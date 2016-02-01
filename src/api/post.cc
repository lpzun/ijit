/**
 * @brief post.cc: it serves as a supporting source file
 *        to implement the postimage computation
 *
 * @date   Nov 16, 2015
 * @author Peizun Liu
 */

#include "../iotf.hh"

namespace iotf {

/**
 * @brief default constructor
 */
post_image::post_image() {

}

/**
 * @brief default  destructor
 */
post_image::~post_image() {

}

/**
 * @brief to compute post images of global state tau: this implementation
 *        iterates over all threads: each thread is used as active thread
 * @param tau
 * @return cover successors
 *         a set of cover successors
 */
deque<prog_state> post_image::step(const prog_state& tau) {
    return this->compute_cov_successors(tau);
}

/**
 * @brief to compute post images of global state tau: all post images are
 *        computed with respect to a particular thread.
 * @param tau
 * @param l
 * @return
 */
deque<prog_state> post_image::step(const prog_state& tau,
        const local_state& l) {

}

/**
 * @brief compute the successors of a configuration (program state) tau
 * @param tau
 * @return the set of postimages: store in a deque<program states>
 */
deque<prog_state> post_image::compute_cov_successors(const prog_state& tau) {
    cout << " I am in the compute_cov_successors...\n";
    deque<prog_state> successors;
    const auto& share = tau.get_s(); /// current shared state
    const auto& sv = share.get_vars(); /// the valuation of shared variables
    const auto& Z = tau.get_locals();  /// the local part of tau: counter abs.
    for (auto il = Z.cbegin(); il != Z.cend(); ++il) {
        const auto& local = il->first;      /// current local
        const auto& pc = local.get_pc();    /// current pc
        const auto& lv = local.get_vars();  /// local vars
        /// iterate over all succeeding statements via <parser::post_G>
        for (auto ipc = parser::get_post_G().get_A()[pc].cbegin();
                ipc != parser::get_post_G().get_A()[pc].cend(); ++ipc) {
            const auto& e = parser::get_post_G().get_E()[*ipc]; /// get the edge point by pc
            const auto& _pc = e.get_dest();
            switch (e.get_stmt().get_type()) {
            case type_stmt::GOTO: {
                /// goto statement
                ///   pc: goto <_pc>;
                ///    ...
                ///  _pc: ...
                ///
                /// SEMANTIC: nondeterministic goto
                local_state _local(_pc, lv);
                auto _Z = alg::update_counters(_local, local, Z);
                successors.emplace_back(share, _Z);
            }
                break;
            case type_stmt::ASSG: {
                /// parallel assignment statement
                ///   pc: <id>+ := <expr>+ constrain <expr>;
                /// pc+1: ...
                ///
                /// SEMANTIC: assignment statement, postcondition of
                /// vars might have to satisfy the constraint
                vector<expr> assgs; //  TODO: need to do sth....

                /// compute shared state
                state_v _sv(sv);
                /// compute local  state
                state_v _lv(lv);
                this->compute_image_assg_stmt(_sv, _lv, sv, lv, pc);

                /// NOTE: the "constrain <expr>" could involve the valuations
                /// for shared and local variables before and after executing
                /// assignment statement ...
                if (e.get_stmt().get_condition().eval(_sv, _lv)) {
                    shared_state _share(_sv);
                    local_state _local(_pc, _lv);
                    auto _Z = alg::update_counters(_local, local, Z);
                    successors.emplace_back(_share, _Z);
                }
            }
                break;
            case type_stmt::IFEL: {
                /// if ... else ... statement: conditional statement
                ///   pc: if (<expr>) then <sseq> else <sseq>; fi;
                /// pc+1: ...
                ///
                /// SEMANTIC:
                if (e.get_stmt().get_condition().eval(sv, lv)) {
                    auto _local = this->compute_image_ifth_stmt(local, _pc);
                    auto _Z = alg::update_counters(_local, local, Z);
                    successors.emplace_back(share, _Z);
                } else {
                    auto _local = this->compute_image_else_stmt(local);
                    auto _Z = alg::update_counters(_local, local, Z);
                    successors.emplace_back(share, _Z);
                }
            }
                break;
            case type_stmt::ASSE: {
                /// assert statement
                ///   pc: assert ( <expr> );
                /// pc+1: ...
                ///
                /// SEMANTIC: assertion statement: encoding bad states
                /// This is a deadend statement
            }
                break;
            case type_stmt::ASSU: {
                /// assume statement: conditional statement
                ///   pc: assume ( <expr> );
                /// pc+1: ...
                ///
                /// SEMANTIC: advance if expr is evaluated to be true;
                /// block otherwise.
                if (e.get_stmt().get_condition().eval(sv, lv)) {
                    /// successor local state: l'.pc = l.pc + 1
                    local_state _local(_pc, lv);
                    auto _Z = alg::update_counters(_local, local, Z);
                    successors.emplace_back(share, _Z);
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

                deque<local_state> T_in;
                /// create a new thread whose l''.pc = label and append it to T_in
                T_in.emplace_back(_pc, lv);
                /// update current thread that l'.pc = l.pc + 1 and append it T_in
                T_in.emplace_back(_pc + 1, lv);
                auto _Z = alg::update_counters(T_in, local, Z);
                successors.emplace_back(share, _Z);
            }
                break;
            case type_stmt::ETHR: {
                /// thread termination statement
                ///   pc: end_thread;
                /// pc+1: ...
                ///
                /// SEMANTIC: the end_thread statement terminates the actual thread,
                /// i.e., has no successor state.
                auto _Z(Z);
                alg::decrement(local, _Z);
                successors.emplace_back(share, _Z);
            }
                break;
            case type_stmt::ATOM: {
                /// the beginning statement of atomic section
                ///   pc: atomic_begin;
                ///   ...
                ///  pc': atomic_end;
                /// SEMANTIC: the atomic_begin statement prevents the scheduler from
                /// a context switch to an other thread
                /// NOTE    : the atomic_end statement is not processed here, but in
                /// the subroutine.

                /// nss, i.e., new shared states, is to store the final shared states
                /// after across atomic section
                deque<shared_state> nss;
                /// lss, i.e., new local  states, is to store the final local  states
                /// after across atomic section
                deque<local_state> nls;

                this->compute_image_atom_sect(share, local, nss, nls);
                for (const auto& _local : nls) { /// first iterate over local states
                    auto _Z = alg::update_counters(_local, local, Z);
                    for (const auto& _share : nss) ///then iterate over shared states
                        successors.emplace_back(_share, _Z);
                }
            }
                break;
            case type_stmt::BCST: {
                /// the broadcast statement
                ///   pc: broadcast;
                /// pc+1: ...
                /// SEMANTIC: advance the pc of active thread, and wake up all
                /// waiting thread via advancing their pcs.
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
                auto _Z(Z);
                /// advance all blocking threads at the wait statements
                for (auto ilo = _Z.begin(); ilo != _Z.end(); ++ilo) {
                    if (parser::get_post_G().get_E()[ilo->first.get_pc()].get_stmt().get_type()
                            == type_stmt::WAIT) {
                        auto l_wait(ilo->first);
                        l_wait.set_pc(ilo->first.get_pc() + 1);
                        auto n_wait(ilo->second);
                        _Z.erase(ilo); /// remove old pair
                        _Z.emplace(l_wait, n_wait);
                    }
                }

                /// advance the broadcast thread
                auto l_bcst(local);
                l_bcst.set_pc(local.get_pc() + 1);
                _Z = alg::update_counters(l_bcst, local, _Z);
                successors.emplace_back(share, _Z);
            }
                break;
            case type_stmt::WAIT: {
                /// the wait statement
                ///   pc: wait;
                /// pc+1: ...
                /// SEMANTIC: blocks the execution of a thread.
                /// There is NO pre-image just by itself. It has to be paired
                /// with broadcast. Thus, it would be handled in broadcast
                /// statement.
            }
                break;
            default: {
                /// it mostly says the skip statement
                ///   pc: skip;
                /// pc+1: ...
                /// SEMANTIC: advance the pc to pc + 1

                /// successor local state: l'.pc = l.pc + 1
                local_state _local(_pc, lv);
                auto _Z = alg::update_counters(_local, local, Z);
                successors.emplace_back(share, _Z);
            }
                break;
            }
        }
    }
    return successors;
}

/**
 * @brief compute post image after an parallel assignment statement
 * @param s
 * @param start
 * @param assgs
 * @param sh
 * @param lo
 */
void post_image::compute_image_assg_stmt(state_v& _s, state_v& _l,
        const state_v& s, const state_v& l, const size_pc& pc) {
    auto ifind = parser::get_post_G().get_assignments().find(pc);
    if (ifind != parser::get_post_G().get_assignments().end()) {
        const auto& sh = ifind->second.sh;
        for (auto i = 0; i < sh.size(); ++i) {
            if (sh[i].is_valid())
                _s[i] = sh[i].eval(s, l);
        }
        const auto& lo = ifind->second.lo;
        for (auto i = 0; i < lo.size(); ++i) {
            if (lo[i].is_valid())
                _l[i] = lo[i].eval(s, l);
        }
    }
}

/**
 * @brief this is the <if...then> branch of IFEL statement
 * @note  the if statements in our benchmarks have the uniformed form:
 *        if <expr> then goto pc; fi;
 *        The expr is very limited into one of the following formats:
 *          (1) 0
 *          (2) *
 *          (3) !(*)
 *          (4) v
 *          (5) !v
 *        At this stage, we could assume that all of <if...else...> statements
 *        follow the above form, and then extend to more general cases in the future.
 *
 * @param l: current local state
 * @return the succeeding local state, whose pc = ... appearing in the goto
 *         statement in then section
 */
local_state post_image::compute_image_ifth_stmt(const local_state& l,
        const size_pc& _pc) {
    return local_state(_pc, l.get_vars());
}

/**
 * @brief this is the <else> branch of IFEL statement
 * @param l: current local state
 * @return the succeeding local state, whose pc = pc + 1
 */
local_state post_image::compute_image_else_stmt(const local_state& l) {
    return local_state(l.get_pc() + 1, l.get_vars());
}

/**
 * @brief compute post images across an atomic section:
 *        Be careful that an atomic section could contain various statements.
 *
 * @note  As in our benchmark, atomic section always follows the form:
 *         1: atomic_begin;
 *         2: assume(<expr>);
 *         3: <id>+ := <expr>+ constrain <expr>; || skip;
 *         4: atomic_end;
 *         Except atomic_begin and atomic_end, the atomic section only involves
 *         three kinds of statements: assume, skip and parallel assignments.
 *
 * @param  s: shared state at the beginning of atomic section
 *           It's also used to return the final shared state after the
 *           atomic section.
 * @param  l: local state at the beginning of atomic section
 * @param _s: the shared states after executing atomic section
 * @param _l: the local  states after executing atomic section
 */
void post_image::compute_image_atom_sect(const shared_state& s,
        const local_state& l, deque<shared_state>& _s, deque<local_state>& _l) {

}

} /* namespace otf */
