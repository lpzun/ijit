/**
 * @brief prev.cc
 *
 * @date   Nov 22, 2015
 * @author Peizun Liu
 */

#include "image.hh"

namespace iotf {

pre_image::pre_image() {

}

pre_image::~pre_image() {

}

/**
 * @brief implement the pure virtual function <step> from base case image
 * @param tau
 * @return cover predecessors
 *         a set of cover predecessors
 */
deque<global_state> pre_image::step(const global_state& tau) {
	const auto& G = this->build_CFG("");
	return this->compute_cov_predecessors(tau, G);
}

void pre_image::parser(const string& filename) {

}

cfg pre_image::build_CFG(const string& filename) {
	cfg G;
	return G;
}

/**
 * @brief compute cover predecessors of configuration tau
 * @param _tau
 * @param G
 * @return the set of cover predecessors
 */
deque<global_state> pre_image::compute_cov_predecessors(
		const global_state& _tau, const cfg& G) {
	auto cov = this->compute_drc_precedessors(_tau, G); /// direct   predecessors
	auto exp = this->compute_exp_predecessors(_tau, G); /// expanded predecessors
	cov.insert(cov.end(), exp.begin(), exp.end()); /// combine them together
	return cov;
}

/**
 * @brief compute direct predecessors
 * @param _tau
 * @param G
 * @return direct predecessors
 *         store in deque<global_state>
 */
deque<global_state> pre_image::compute_drc_precedessors(
		const global_state& _tau, const cfg& G) {
	deque<global_state> drc_predecessors;
	const auto& _sh = _tau.get_s();
	const auto& _Z = _tau.get_locals();
	for (auto il = _Z.begin(); il != _Z.end(); ++il) {
		const auto& _local = il->first;
		const auto& _pc = _local.get_pc();   /// current pc
		const auto& _lo = _local.get_vars(); /// local vars
		for (auto ipc = G.get_A()[_pc].cbegin(); ipc != G.get_A()[_pc].cend();
				++ipc) {
			const auto& e = G.get_E()[*ipc]; /// get the edge by pc
			const auto& pc = e.get_dest();
			switch (e.get_stmt().get_type()) {
			case type_stmt::GOTO: {
				/// goto statement
				///   pc: goto <_pc>;
				///    ...
				///  _pc: ...
				///
				/// SEMANTIC: nondeterministic goto
				local_state local(pc, _lo);
				auto Z = alg::update_counters(local, _local, _Z);
				drc_predecessors.emplace_back(_sh, Z);
			}
				break;
			case type_stmt::ASSG: {
				/// parallel statement
				///   pc: <id>+ := <expr>+ constrain <expr>;
				/// pc+1: ...
				///
				/// SEMANTIC: assignment statement, postcondition of
				/// vars might have to satisfy the constraint
				// TODO
			}
				break;
			case type_stmt::IFEL: {
				/// if ... else ... statement: conditional statement
				///   pc: if (<expr>) then <sseq> else <sseq>; fi;
				/// pc+1: ...
				///
				/// SEMANTIC:
				if (e.get_stmt().get_precondition().eval(_sh.get_vars(), _lo)) {
					//TODO
				} else {
					//TODO
				}
			}
				break;
			case type_stmt::ASSE: {
				/// assert statement
				///   pc: assert ( <expr> );
				/// pc+1: ...
				///
				/// SEMANTIC: assertion statement: encoding bad states

			}
				break;
			case type_stmt::ASSU: {
				/// assume statement: conditional statement
				///   pc: assume ( <expr> );
				/// pc+1: ...
				///
				/// SEMANTIC: advance if expr is evaluated to be true;
				/// block otherwise.
				if (e.get_stmt().get_precondition().eval(_sh.get_vars(), _lo)) {
					local_state local(pc, _lo);
					auto Z = alg::update_counters(local, _local, _Z);
					drc_predecessors.emplace_back(_sh, Z);
				}
			}
				break;
			case type_stmt::NTHR: {
				/// thread creation statement like:
				///   pc: start_thread <label>;
				/// pc+1: ...
				///
				/// SEMANTIC: the start_thread <label> instruction creates a new
				/// thread that starts execution at the program location label.
				/// It gets a copy of the local variables of the current thread,
				/// which continues execution at the proceeding statement.
				///
				/// An example of thread creation:
				///     10: start_thread goto 20;
				///		11: ...
				///          ...
				///		20: ...
				/// CFG: only 1 edge          10 (plocal)
				///           (not in CFG) x/    \
				///                        /      \
				///              (slocal) 11	  20 (_local)
				///
				///      case 1: _local.pc == new_thr_pc // don't need this
				///      case 2: _local.pc == pc + 1

				local_state slocal(pc + 1, _lo); /// succeeding local state
				auto ifind = _Z.find(slocal);
				if (ifind != _Z.end()) {
					auto Z(_Z);
					/// increment the source local state
					local_state plocal(pc, _lo);
					alg::increment(plocal, Z);
					/// decrement the new and succeeding local states
					alg::decrement(_local, Z);
					alg::decrement(slocal, Z);

					drc_predecessors.emplace_back(_sh, Z);
				}
			}
				break;
			case type_stmt::ETHR: {

			}
				break;
			case type_stmt::EATM: {

			}
				break;
			case type_stmt::BCST: {
				/// the broadcast statement
				///   pc: broadcast;
				/// pc+1: ...
				/// SEMANTIC: advance the pc of active thread, and wake up all waiting
				/// thread via advancing their pcs.
				///
				/// An example of broadcast:
				///      10: wait;
				///      11: ...
				///          ...
				///      20: wait;
				///      21: ...
				///          ...
				///      30: broadcast;
				/// 	 31: ...
				///          ...
				///
				///    (11, 21, 31, ...) <-
				///                         (10, 20, 30, ...)
				///                         (11, 20, 30, ...)
				///                         (10, 21, 30, ...)
				///                         (11, 21, 30, ...)
				auto Z(_Z);
				/// update post-broadcast thread
				local_state local(pc, _local.get_vars());
				Z = alg::update_counters(local, _local, Z);
				/// extract all post-wait threads
				for (auto iw = Z.begin(); iw != Z.end(); ++iw) {
					// TODO
				}
			}
				break;
			case type_stmt::WAIT: {

			}
				break;
			default: {
				local_state local(pc, _local.get_vars());
				auto Z = alg::update_counters(local, _local, _Z);
				drc_predecessors.emplace_back(local, Z);
			}
				break;
			}
		}
	}

	return drc_predecessors;
}

/**
 * @brief compute the expanded cover predecessors
 * @param _tau
 * @param G
 * @return expanded cover predecessors
 */
deque<global_state> pre_image::compute_exp_predecessors(
		const global_state& _tau, const cfg& G) {
	deque<global_state> exp_predecessors;

	return exp_predecessors;
}

}

