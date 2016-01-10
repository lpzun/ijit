/**
 * @brief prev.cc:  it serves as a supporting source file
 *        to implement the preimage computation
 *
 * @date   Nov 22, 2015
 * @author Peizun Liu
 */

#include "../iotf.hh"

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
deque<prog_state> pre_image::step(const prog_state& tau) {
    return this->compute_cov_predecessors(tau);
}

/**
 * @brief compute cover predecessors of configuration tau
 * @param _tau
 * @param G
 * @return the set of cover predecessors
 */
deque<prog_state> pre_image::compute_cov_predecessors(const prog_state& _tau) {
    auto cov = this->compute_drc_precedessors(_tau); /// direct   predecessors
    auto exp = this->compute_exp_predecessors(_tau); /// expanded predecessors
    cov.insert(cov.end(), exp.begin(), exp.end());   /// combine them together
    return cov;
}

/**
 * @brief compute direct predecessors
 * @param _tau
 * @return direct predecessors
 *         store in deque<prog_state>
 */
deque<prog_state> pre_image::compute_drc_precedessors(const prog_state& _tau) {
    deque<prog_state> drc_predecessors;
    const auto& _share = _tau.get_s(); /// current shared state
    const auto& _sv = _share.get_vars(); /// the valuation of shared variables
    const auto& _Z = _tau.get_locals(); /// the local part of _tau: counter abs.
    for (auto il = _Z.begin(); il != _Z.end(); ++il) {
        const auto& _local = il->first;
        const auto& _pc = _local.get_pc();   /// current pc
        const auto& _lv = _local.get_vars(); /// local vars
        /// iterate over all preceding statements via <parser::prev_G>
        for (auto ipc = parser::get_prev_G().get_A()[_pc].cbegin();
                ipc != parser::get_prev_G().get_A()[_pc].cend(); ++ipc) {
            const auto& e = parser::get_prev_G().get_E()[*ipc]; /// get the edge by pc
            const auto& pc = e.get_dest();
            switch (e.get_stmt().get_type()) {
            case type_stmt::GOTO: {
                /// goto statement
                ///   pc: goto <_pc>;
                ///    ...
                ///  _pc: ...
                ///
                /// SEMANTIC: nondeterministic goto
                local_state local(pc, _lv);
                auto Z = alg::update_counters(local, _local, _Z);
                drc_predecessors.emplace_back(_share, Z);
            }
                break;
            case type_stmt::ASSG: {
                /// parallel statement
                ///   pc: <id>+ := <expr>+ constrain <expr>;
                ///
                /// SEMANTIC: assignment statement, postcondition of
                /// vars might have to satisfy the constraint
                if (e.get_stmt().get_condition().eval(_sv, _lv)) {
                    /// compute all direct predecessors via weakest
                    /// precondition and SAT solvers
                    auto P = this->compute_image_assg_stmt(_sv, _lv);
                    for (auto ip = P.cbegin(); ip != P.cend(); ++ip) {
                        shared_state share(ip->first);
                        local_state local(pc, ip->second);

                        auto Z = alg::update_counters(local, _local, _Z);
                        drc_predecessors.emplace_back(share, Z);
                    }
                }
            }
                break;
            case type_stmt::IFEL: {
                /// if ... else ... statement: conditional statement
                ///   pc: if (<expr>) then <sseq> else <sseq>; fi;
                /// pc+1: ...
                ///
                /// SEMANTIC:
                if (e.get_stmt().get_condition().eval(_sv, _lv)) {
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
                /// SEMANTIC: assertion statement: encoding bad states:
                /// The idea is that: if there is an assertion but we do NOT
                /// care about it in one specific verification, then we adv-
                /// ance the PC when the assertion is satisfiable.
                if (e.get_stmt().get_condition().eval(_share.get_vars(), _lv)) {
                    local_state local(pc, _lv);
                    auto Z = alg::update_counters(local, _local, _Z);
                    drc_predecessors.emplace_back(_share, Z);
                }
            }
                break;
            case type_stmt::ASSU: {
                /// assume statement: conditional statement
                ///   pc: assume ( <expr> );
                /// pc+1: ...
                ///
                /// SEMANTIC: advance if expr is evaluated to be true;
                /// block otherwise.
                if (e.get_stmt().get_condition().eval(_sv, _lv)) {
                    local_state local(pc, _lv);
                    auto Z = alg::update_counters(local, _local, _Z);
                    drc_predecessors.emplace_back(_share, Z);
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

                local_state slocal(pc + 1, _lv); /// succeeding local state
                auto ifind = _Z.find(slocal);
                if (ifind != _Z.end()) {
                    auto Z(_Z);
                    /// increment the source local state
                    local_state plocal(pc, _lv);
                    alg::increment(plocal, Z);
                    /// decrement the new and succeeding local states
                    alg::decrement(_local, Z);
                    alg::decrement(slocal, Z);

                    drc_predecessors.emplace_back(_share, Z);
                }
            }
                break;
            case type_stmt::ETHR: {
                /// thread termination statement
                ///   pc: end_thread;
                /// pc+1: ...
                ///
                /// SEMANTIC: the end_thread statement terminates the actual thread,
                /// i.e., has no successor state.
                ///
                /// We treat this as a skip statement

            }
                break;
            case type_stmt::EATM: {
                /// the ending statement of atomic section
                ///   pc: atomic_begin;
                ///   ...
                ///  pc': atomic_end;
                /// SEMANTIC: the atomic_end statement prevents the scheduler from
                /// a context switch to an other thread
                /// NOTE    : the atomic_begin statement is not processed here, but
                /// in the subroutine.

                /// ns, i.e., new shared state, is to store the final shared state
                /// after across atomic section
                auto ns = _share;
                auto T_in = this->compute_image_atom_sect(ns, _local);
                auto Z = alg::update_counters(T_in, _local, _Z);
                drc_predecessors.emplace_back(ns, _Z);
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

                }
            }
                break;
            case type_stmt::WAIT: {
                /// the wait statement
                ///   pc: wait;
                /// pc+1: ...
                /// SEMANTIC: blocks the execution of a thread.
                /// There is no pre-image just by itself. It has to be paired
                /// with broadcast.
            }
                break;
            default: {
                /// it mostly says the skip statement
                ///   pc: skip;
                /// pc+1: ...
                /// SEMANTIC: advance the pc to pc + 1

                /// successor local state: l'.pc = l.pc + 1
                local_state local(pc, _local.get_vars());
                auto Z = alg::update_counters(local, _local, _Z);
                drc_predecessors.emplace_back(_share, Z);
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
deque<prog_state> pre_image::compute_exp_predecessors(const prog_state& _tau) {
    deque<prog_state> exp_predecessors;

    return exp_predecessors;
}

/**
 * @brief compute pre images across an atomic section:
 *        Be careful that an atomic section could contain various statements.
 *
 * @param s: shared state at the end of atomic section (atomic_end).
 *           It is also used to return the final shared state before the atomic
 *           section.
 * @param l: local state at the end of atomic section
 * @return preceding local states across atomic section
 */
deque<local_state> pre_image::compute_image_atom_sect(shared_state& s,
        const local_state& l) {
    deque<local_state> locals;

    return locals;
}

/**
 * @brief compute pre images for broadcast statement. It involves all post-wait
 *        threads
 *        TODO: this is not the final version.
 * @param pw
 */
void pre_image::compute_image_bcst_stmt(deque<local_state>& pw) {
    for (auto il = pw.begin(); il != pw.end(); ++il) {
        il->set_pc(il->get_pc() - 1);
    }
}

/**
 * @brief compute the pre images for an assignment statement
 * @param _sv
 * @param _lv
 * @return a list of valuations for shared and local variables
 */
deque<pair<state_v, state_v>> pre_image::compute_image_assg_stmt(
        const state_v& _sv, const state_v& _lv) {
    deque<pair<state_v, state_v>> result;
    return result;
}

/**
 * @brief compute weakest precondition
 * @param _sv
 * @param _lv
 * @return a deque of pair<state_v, state_v>
 */
deque<pair<state_v, state_v>> pre_image::weakest_precondition(
        const state_v& _sv, const state_v& _lv) {
    deque<pair<state_v, state_v>> result;
    return result;
}

}

