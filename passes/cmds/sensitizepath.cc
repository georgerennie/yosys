/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2022 George Rennie <georgerennie@gmail.com>
 *
 *  Permission to use, copy, modify, and/or distribute this software for any
 *  purpose with or without fee is hereby granted, provided that the above
 *  copyright notice and this permission notice appear in all copies.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 *  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 *  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 *  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 *  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 *  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 *  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 *
 */

#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "kernel/yosys.h"
#include <algorithm>
#include <utility>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

/*
 * Options:
 * - x-able inputs
 *   - This allows interface properties to define assumptions about when they
 *       aren't x
 *   - Can't be used with constrain_x
 *   - Should this default to on or off?
 * - constrain away x sources
 *   - how do we choose what x sources to keep? Using selection maybe?
 *   - how are preconditions for the x source decided?
 *     - maybe assumptions can be used to define the times it isnt x
 *
 * Further thoughts:
 * - Therefore the only settings to worry about are whether explicit x signals
 *     should be added and whether x sources should be constrained away, although
 *     there is still the question of how to decide what signals are kept as x.
 *     For now let's go with currently selected cells/wires
 * - Maybe add warning to documentation that in constrain mode x assumptions will
 *     be taken as constraint assumptions so be careful as to what is enabled
 * - Consider using something other than === 'x in constrain mode, as yosys
 *     will optimise xs before they reach sensitizepath and its also not super
 *     clear
 *     - Potential approach - don't - use yosys command to specify secure srcs
 *         and destinations, and a signal for when they are a valid src/dest
 *     - Can have three options, -src wire (en), -checker wire (en),
 *         -block wire (en), where enables are optional, and block is used to
 *         specify a wire to ignore the secure data travelling through
 *
 * x sources:
 * - undriven wires (incl. undriven wires)
 *   - These should be connected
 * - explicit x's
 *   - These should be replaced by a wire that is used by both paths
 * - uninitialised FFs
 *   - These should be assumed the same in the first clock cycle
 */

struct SensitizePathWorker {
	bool opt_constrain_inputs = false;
	bool opt_constrain_all = false;

	SigMap sigmap;
	RTLIL::Design *design;
	RTLIL::Module *src_module;
	RTLIL::Module *miter;

	dict<RTLIL::Wire *, RTLIL::Wire *> wire_map;
	std::vector<RTLIL::SigSig> new_connections;

	static inline RTLIL::IdString label_b(RTLIL::IdString name) { return name.str() + "__b"; }
	static inline RTLIL::IdString label_x(RTLIL::IdString name) { return name.str() + "__is_x"; }

	template <class... Args> inline void connect(Args &&...args) { new_connections.emplace_back(std::forward<Args>(args)...); }

	void write_new_connections() { miter->new_connections(new_connections); }

	// void constrain_explicit_x()
	// {
	//   // Check for xs in cells and connections
	//   // TODO: How do we map from a sigspec to a path b sigspec??
	// }

	// void constrain_ff_init() {}

	RTLIL::SigSpec rewrite_sigspec(const RTLIL::SigSpec &sig)
	{
		// Convert path a wires to path b wires in a sigspec
		RTLIL::SigSpec new_sig;
		for (auto chunk : sig.chunks()) {
			if (chunk.is_wire())
				chunk.wire = wire_map[chunk.wire];
			new_sig.append(chunk);
		}
		return new_sig;
	}

	std::pair<RTLIL::SigSpec, RTLIL::SigSpec> rewrite_sigspec_constrain(const RTLIL::SigSpec &sig)
	{
		// Convert path a wires to path b wires in a sigspec, and constrain any
		// x bits to take the same anyseq value in both paths
		RTLIL::SigSpec sig_a, sig_b;

		for (auto chunk : sig.chunks()) {
			if (chunk.is_wire()) {
				sig_a.append(chunk);
				chunk.wire = wire_map[chunk.wire];
				sig_b.append(chunk);
				continue;
			}

			size_t x_len = 0;
			for (const auto bit : chunk.data) {
				if (bit == State::Sx) {
					x_len++;
					continue;
				}

				if (x_len > 0) {
					auto anyseq = miter->Anyseq(NEW_ID, x_len);
					sig_a.append(anyseq);
					sig_b.append(anyseq);
					x_len = 0;
				}

				sig_a.append(bit);
				sig_b.append(bit);
			}

			if (x_len > 0) {
				auto anyseq = miter->Anyseq(NEW_ID, x_len);
				sig_a.append(anyseq);
				sig_b.append(anyseq);
			}
		}

		log_assert(GetSize(sig_a) == GetSize(sig));
		return std::make_pair(sig_a, sig_b);
	}

	void convert_x_equality(RTLIL::Cell *eq_cell)
	{
		// Insert $eqx/$nex cells to replace ===/!== 'x
		RTLIL::SigSpec sig_a = sigmap(eq_cell->getPort(ID::A));
		RTLIL::SigSpec sig_b = sigmap(eq_cell->getPort(ID::B));

		// TODO: Should this use rewrite_sigspec_constrain
		// what happens if you have (2'b1x === 'x)
		// what happens if you have ('x == 'x) and its constrained?
		if (sig_a.is_fully_undef())
			sig_a = rewrite_sigspec(sig_b);
		else if (sig_b.is_fully_undef())
			sig_b = rewrite_sigspec(sig_a);
		else
			return;

		RTLIL::SigSpec eq_wire;
		if (eq_cell->type == ID($eqx))
			eq_wire = miter->Nex(NEW_ID, sig_a, sig_b);
		else
			eq_wire = miter->Eqx(NEW_ID, sig_a, sig_b);

		RTLIL::SigSpec sig_y = eq_cell->getPort(ID::Y);
		connect(sig_y, eq_wire);
		connect(rewrite_sigspec(sig_y), eq_wire);

		miter->remove(eq_cell);
	}

	void add_x_wire(RTLIL::Wire *wire_a, RTLIL::Wire *wire_b)
	{
		if (!wire_a->name.isPublic())
			return;

		auto wire_x = miter->addWire(label_x(wire_a->name), wire_b);
		wire_x->set_bool_attribute(ID::keep);
		miter->addNex(NEW_ID, wire_a, wire_b, wire_x);
	}

	void run()
	{
		src_module->cloneInto(miter);

		SigPool undriven_signals;
		SigMap miter_map(miter);
		sigmap.swap(miter_map);

		const auto wires = miter->wires().to_vector();
		const auto cells = miter->cells().to_vector();
		const auto connections = miter->connections();

		for (auto wire : wires) {
			// Create copy of each wire
			auto wire_b = miter->addWire(NEW_ID, wire);
			wire_b->port_input = false;
			wire_b->port_output = false;
			wire_map[wire] = wire_b;

			// Add wire to encode if wire and wire_b diverge
			add_x_wire(wire, wire_b);

			// If constraining undriven wires, we need to first consider every non
			// input wire
			if (opt_constrain_all) {
				undriven_signals.add(sigmap(wire));
				continue;
			}

			// If wire_b is an input, create a driver
			if (wire->port_input) {
				if (opt_constrain_inputs)
					connect(wire_b, wire);
				else
					connect(wire_b, miter->Anyseq(NEW_ID, GetSize(wire_b)));
			}
		}

		for (auto cell : cells) {
			if (opt_constrain_all) {
				// Remove any driven signals from undriven_signals
				for (const auto &conn : cell->connections())
					if (!cell->known() || cell->output(conn.first))
						undriven_signals.del(sigmap(conn.second));
			}

			// The logic path is symmetrical so we dont need to copy assertions/covers
			// to the second path as they are equisatisfiable
			if (cell->type.in(ID($assert), ID($live), ID($cover)))
				continue;

			// Explicit sources of non-determinism should not be considered to be X,
			// so must take the same value in both paths
			if (cell->type.in(ID($anyseq), ID($anyconst), ID($allseq), ID($allconst))) {
				auto sig = cell->getPort(ID::Y);
				connect(rewrite_sigspec(sig), sig);
				continue;
			}

			// Insert $eqx/$nex cells between paths to replace ===/!== 'x
			if (!opt_constrain_all && cell->type.in(ID($eqx), ID($nex))) {
				convert_x_equality(cell);
				continue;
			}

			// Copy cell to second path
			auto cell_b = miter->addCell(label_b(cell->name), cell);
			for (const auto &conn : cell_b->connections()) {
				if (opt_constrain_all) {
					const auto new_sigs = rewrite_sigspec_constrain(conn.second);
					cell->setPort(conn.first, new_sigs.first);
					cell_b->setPort(conn.first, new_sigs.second);
				} else
					cell_b->setPort(conn.first, rewrite_sigspec(conn.second));
			}
		}

		for (auto conn : connections) {
			if (opt_constrain_all) {
				const auto new_sigs = rewrite_sigspec_constrain(conn.second);
				connect(conn.first, new_sigs.first);
				connect(rewrite_sigspec(conn.first), new_sigs.second);
			} else {
				connect(conn);
				connect(rewrite_sigspec(conn.first), rewrite_sigspec(conn.second));
			}
		}

		miter->fixup_ports();

		if (opt_constrain_all) {
			// Constrain any undriven wires
			RTLIL::SigSpec undriven_sig = undriven_signals.export_all();
			for (auto &chunk_a : undriven_sig.chunks()) {
				log("chunk: %s\n", log_signal(chunk_a.wire));
				log_assert(chunk_a.is_wire());
				SigChunk chunk_b(wire_map[chunk_a.wire], chunk_a.offset, chunk_a.width);

				if (chunk_a.wire->port_input)
					connect(chunk_b, chunk_a);
				else {
					const auto anyseq = miter->Anyseq(NEW_ID, GetSize(chunk_a));
					connect(chunk_a, anyseq);
					connect(chunk_b, anyseq);
				}
			}
		}

		write_new_connections();
	}
};

struct SensitizePath : public Pass {
	SensitizePath() : Pass("sensitizepath", "create a miter circuit for path sensitization") {}
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    sensitizepath [options] src_module miter_module [selection]\n");
		log("\n");
		log("This creates a miter module for formal with two copies of the input module\n");
		log("and converts comparisons of the form (sig === 'x) and (sig !== 'x) into a\n");
		log("comparison between the values of sig in the two copies. This is used in\n");
		log("formal to prove that a signal is defined, or that the value of one net\n");
		log("cannot influence the value of another net.\n");
		log("\n");
		log("    -constrain_inputs\n");
		log("        Forces the inputs to the module to be defined.\n");
		log("\n");
		log("    -constrain_undef\n");
		log("        Constrain undriven wires, initial register values, x constants\n");
		log("        and module inputs to take the same value in both circuits.\n");
		log("\n");
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		SensitizePathWorker worker;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-constrain_inputs") {
				worker.opt_constrain_inputs = true;
				continue;
			}
			if (args[argidx] == "-constrain_undef") {
				worker.opt_constrain_all = true;
				continue;
			}

			if (args[argidx][0] == '-') {
				cmd_error(args, argidx, "Unknown option.");
			}
			break;
		}

		if (args.size() != argidx + 2) {
			cmd_error(args, argidx, "Invalid number of module arguments.\n");
		}

		// TODO: fix memid weirdness
		// TODO: If we encounter a $mem/$mem_v2 in constrained mode emit warning that we
		// can't constrain the init values, and to consider running memory instead

		worker.design = design;
		worker.src_module = design->module(RTLIL::escape_id(args[argidx]));
		worker.miter = design->module(RTLIL::escape_id(args[argidx + 1]));

		if (worker.src_module == nullptr)
			log_cmd_error("Can't find source module %s.\n", args[argidx].c_str());

		if (worker.miter != nullptr)
			log_cmd_error("Miter module %s already exists.\n", args[argidx + 1].c_str());

		if (worker.src_module->has_memories() || worker.src_module->has_processes())
			log_cmd_error("Source module contains memories or processes. Run 'memory' or 'proc' respectively.\n");

		log_header(design, "Executing PATH_SENSITIZE pass (creating path sensitization miter)\n");

		worker.miter = design->addModule(RTLIL::escape_id(args[argidx + 1]));
		worker.run();
	}
} SensitizePathPass;

PRIVATE_NAMESPACE_END
