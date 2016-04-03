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
 * @brief to compute all pre images of global state tau: this implementation
 *        iterates over all threads: each thread is used as an active thread
 * @param tau: the global state
 * @param p  : the type of preimages
 * @return cover predecessors
 *         a set of cover predecessors
 */
deque<prog_state> pre_image::step(const prog_state& tau, const prev& p) {
    switch (p) {
    case prev::COV:
        return this->compute_cov_pre_images(tau);
    default:
        return this->compute_drc_pre_images(tau);
    }
}

/**
 * @brief the
 * @param tau
 * @param l
 * @return
 */
deque<prog_state> pre_image::step(const prog_state& tau, const local_state& l) {
    deque<prog_state> images;
    this->compute_pre_images(tau, l, images);
    return images;
}

/**
 * @brief compute cover predecessors of configuration tau
 * @param _tau
 * @param G
 * @return the set of cover predecessors
 */
deque<prog_state> pre_image::compute_cov_pre_images(const prog_state& _tau) {
    auto cov = this->compute_drc_pre_images(_tau); /// direct   predecessors
    auto exp = this->compute_exp_pre_images(_tau); /// expanded predecessors
    cov.insert(cov.end(), exp.begin(), exp.end()); /// combine them together
    return cov;
}

/**
 * @brief compute direct predecessors
 * @param _tau
 * @return direct predecessors
 *         store in deque<prog_state>
 */
deque<prog_state> pre_image::compute_drc_pre_images(const prog_state& _tau) {
    deque<prog_state> images;
    for (const auto& _l : _tau.get_locals())
        this->compute_pre_images(_tau, _l.first, images);
    return images;
}

/**
 * @brief compute the expanded cover predecessors
 * @param _tau
 * @param G
 * @return expanded cover predecessors
 */
deque<prog_state> pre_image::compute_exp_pre_images(const prog_state& _tau) {
    deque<prog_state> images;

    return images;
}

/**
 * @brief compute all pre images of a program state tau w.r.t. local state _l
 * @param _tau  : a program state
 * @param _l    : a specific local state
 * @param images: the list of pre images of _tau w.r.t. one thread whose local
 *        state is _l
 */
void pre_image::compute_pre_images(const prog_state& _tau,
        const local_state& _l, deque<prog_state>& images) {
    /// extract all necessary information from program state _tau and
    /// local state _l
    const auto& _s = _tau.get_s();      /// current shared state
    const auto& _sv = _s.get_vars();    /// shared vars: the valuation
    const auto& _Z = _tau.get_locals(); /// the local part of _tau
    const auto& _pc = _l.get_pc();      /// current pc
    const auto& _lv = _l.get_vars();    /// local vars : the valuation

    /// iterate over all preceding statements via <parser::prev_G>
    const auto& predecessors = parser::get_prev_G().get_A()[_pc];
    for (auto ie = predecessors.cbegin(); ie != predecessors.cend(); ++ie) {
        const auto& e = *ie; /// get the edge by pc
        const auto& pc = e.get_dest();
//        cout << e << "\n";
//        cout << _pc << "->" << pc << "\n";
        switch (e.get_stmt().get_type()) {
        case type_stmt::GOTO: {
            /// goto statement
            ///   pc: goto <_pc>;
            ///    ...
            ///  _pc: ...
            ///
            /// SEMANTIC: nondeterministic goto
            local_state l(pc, _lv);
            cout << __func__ << " goto " << l << "\n";
            const auto& Z = alg::update_counters(l, _l, _Z);
            images.emplace_back(_s, Z);
        }
            break;
        case type_stmt::ASSG: {
            /// parallel statement
            ///   pc: <id>+ := <expr>+ constrain <expr>;
            ///
            /// SEMANTIC: assignment statement, postcondition of
            /// vars might have to satisfy the constraint

            /// compute all direct predecessors via weakest
            /// precondition and SAT solvers
            cout << __func__ << " parallel assignment " << pc << "\n";
            const auto& wp = this->compute_image_assg_stmt(pc, _sv, _lv);
            for (auto ip = wp.cbegin(); ip != wp.cend(); ++ip) {
                const auto& cond = e.get_stmt().get_condition();
                if (cond.is_void()
                        || (cond.eval(ip->first, ip->second, _sv, _lv)
                                != sool::F)) {
                    const auto& Z = alg::update_counters(
                            local_state(pc, ip->second), _l, _Z);
                    images.emplace_back(shared_state(ip->first), Z);
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
            const auto& cond = e.get_stmt().get_condition().eval(_sv, _lv);
            if (_pc != pc + 1) {
                if (cond != sool::F) {
                    const auto& l = this->compute_image_ifth_stmt(_l, pc);
                    const auto& Z = alg::update_counters(l, _l, _Z);
                    images.emplace_back(_s, Z);
                }
            } else {
                if (cond != sool::T) {
                    const auto& l = this->compute_image_else_stmt(_l);
                    const auto& Z = alg::update_counters(l, _l, _Z);
                    images.emplace_back(_s, Z);
                }
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
            local_state l(pc, _lv);
            const auto& Z = alg::update_counters(l, _l, _Z);
            images.emplace_back(_s, Z);
        }
            break;
        case type_stmt::ASSU: {
            /// assume statement: conditional statement
            ///   pc: assume ( <expr> );
            /// pc+1: ...
            ///
            /// SEMANTIC: advance if expr is evaluated to be true;
            /// block otherwise.
            cout << __func__ << " assume " << "\n";
            const auto& cond = e.get_stmt().get_condition().eval(_sv, _lv);
            if (cond != sool::F) {
                local_state l(pc, _lv);
                const auto& Z = alg::update_counters(l, _l, _Z);
                images.emplace_back(_s, Z);
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
            /// CFG: only 1 edge          10 (pl)
            ///           (not in CFG) x/    \
			///                        /      \
			///                 (sl) 11	       20 (_l)
            ///
            ///      case 1: _l.pc == new_thr_pc // don't need this
            ///      case 2: _l.pc == pc + 1

            local_state sl(pc + 1, _lv); /// succeeding local state
            auto ifind = _Z.find(sl);
            if (ifind != _Z.end()) {
                auto Z(_Z);
                /// increment the source local state
                local_state pl(pc, _lv);
                alg::increment(pl, Z);
                /// decrement the new and succeeding local states
                alg::decrement(_l, Z);
                alg::decrement(sl, Z);
                images.emplace_back(_s, Z);
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
            local_state l(pc, _lv);
            const auto& Z = alg::update_counters(l, _l, _Z);
            images.emplace_back(_s, Z);
        }
            break;
        case type_stmt::EATM: {
            /// ending statement of atomic section
            ///   pc: atomic_begin;
            ///   ...
            ///  pc': atomic_end;
            /// SEMANTIC: the atomic_end statement prevents the scheduler from
            /// a context switch to an other thread
            /// NOTE    : the atomic_begin statement is not processed here,but
            /// in the subroutine.

            auto _pc(pc); /// the copy of pc
            const auto& wp = this->compute_image_atom_sect(_sv, _lv, _pc);
            for (auto ip = wp.cbegin(); ip != wp.cend(); ++ip) {
                const auto& Z = alg::update_counters(
                        local_state(_pc, ip->second), _l, _Z);
                images.emplace_back(shared_state(ip->first), Z);
            }
        }
            break;
        case type_stmt::BCST: {
            /// broadcast statement
            ///   pc: broadcast;
            /// pc+1: ...
            /// SEMANTIC: advance pc of active thread, and wake up all waiting
            /// threads via advancing their pc's.
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
            local_state l(pc, _lv);
            Z = alg::update_counters(l, _l, Z);
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
            local_state l(pc, _lv);
            const auto& Z = alg::update_counters(l, _l, _Z);
            images.emplace_back(_s, Z);
        }
            break;
        }
    }
}

/**
 * @brief compute the pre images for an assignment statement
 * @param _sv
 * @param _lv
 * @return a list of valuations for shared and local variables
 */
deque<pair<state_v, state_v>> pre_image::compute_image_assg_stmt(
        const size_pc& pc, const state_v& _sv, const state_v& _lv) {
    deque<pair<state_v, state_v>> worklist; /// store the result

    auto ifind = parser::get_prev_G().get_assignments().find(pc);
    if (ifind != parser::get_prev_G().get_assignments().end()) {
        /// step 0: preparations:
        ///         (1) obtain assignments to shared variables
        const auto& sh = ifind->second.sh;
        ///         (2) obtain assignments to local  variables
        const auto& lo = ifind->second.lo;

        /// step 1: conjoin all equalities in format v' = expr of parallel
        ///         assignment together...
        deque<symbol> sexpr;
        for (auto i = 0; i < sh.size(); ++i) {
            if (!sh[i].is_void())
                this->conjoin_equality(_sv[i], sh[i].get_sexpr(), sexpr);
        }
        for (auto i = 0; i < lo.size(); ++i) {
            if (!lo[i].is_void())
                this->conjoin_equality(_lv[i], lo[i].get_sexpr(), sexpr);
        }

        /// step 2: collect all non-free variables, and replace them with
        ///         the past-parallel-assignment values
        ss_vars s_vars(refs::SV_NUM, sool::N);
        sl_vars l_vars(refs::LV_NUM, sool::N);
        for (auto i = 0; i < sh.size(); ++i) {
            if (sh[i].is_void()) {
                s_vars[i] = _sv[i] ? sool::T : sool::F;
                solver::substitute(sexpr, solver::encode(i, true), _sv[i]);
            }
        }
        for (auto i = 0; i < lo.size(); ++i) {
            if (lo[i].is_void()) {
                l_vars[i] = _lv[i] ? sool::T : sool::F;
                solver::substitute(sexpr, solver::encode(i, false), _lv[i]);
            }
        }

        /// step 3: compute weakest preconditions for parallel assignment
        const auto& assgs = solver::all_sat_solve(sexpr, s_vars, l_vars);
        for (const auto& assg : assgs) {
            /// step 3.1: build shared BV via splitting *
            deque<state_v> svs;        /// store shared BV
            svs.emplace_back(state_v(0));
            for (auto i = 0; i < assg.first.size(); ++i) {
                alg::split(assg.first[i], i, svs);
            }

            /// step 3.2: build local  BV via splitting *
            deque<state_v> lvs;        /// store local  BV
            lvs.emplace_back(state_v(0));
            for (auto i = 0; i < assg.second.size(); ++i) {
                alg::split(assg.second[i], i, lvs);
            }

            /// step 3.3: determine if sv and lv are valid
            ///           preimages, and store it if true
            for (const auto& sv : svs)
                for (const auto& lv : lvs)
                    worklist.emplace_back(sv, lv);
        } /// ending of step 3
    }
    return worklist;
}

/**
 * @brief conjoin all equalities that generated in parallel assignments
 *        together, the format is (_v = se)
 * @param _v
 * @param se
 * @param app: the expression to which (_v = se) appends
 */
void pre_image::conjoin_equality(const bool& _v, const deque<symbol>& se,
        deque<symbol>& app) {
    if (app.empty()) {
        app.emplace_back(_v);
        app.insert(app.end(), se.begin(), se.end());
        app.emplace_back(solver::EQ);
        app.emplace_back(solver::PAR);
    } else {
        app.emplace_back(_v);
        app.insert(app.end(), se.begin(), se.end());
        app.emplace_back(solver::EQ);
        app.emplace_back(solver::PAR);
        app.emplace_back(solver::AND);
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
 *        At this stage, we could assume that all of <if...else...>
 *        statements follow the above form, and then extend to more
 *        general cases in the future.
 *
 * @param _l: current local state
 * @return the predecessor local state, whose pc = ...
 */
local_state pre_image::compute_image_ifth_stmt(const local_state& _l,
        const size_pc& pc) {
    return local_state(pc, _l.get_vars());
}

/**
 * @brief this is the <else> branch of IFEL statement
 * @param _l: current local state
 * @return the predecessor local state, whose pc = pc' - 1
 */
local_state pre_image::compute_image_else_stmt(const local_state& _l) {
    return local_state(_l.get_pc() - 1, _l.get_vars());
}

/**
 * @brief compute pre images across an atomic section:
 *        Remark that an atomic section could contain various statements
 *
 * @param s: shared state at the end of atomic section (atomic_end).
 *           It is also used to return the final shared state before atomic
 *           section.
 * @param l: local state at the end of atomic section
 * @return predecessor local states across atomic section
 */
deque<pair<state_v, state_v>> pre_image::compute_image_atom_sect(
        const state_v& _sv, const state_v& _lv, size_pc& _pc) {
    deque<pair<state_v, state_v>> result;

    auto e = parser::get_prev_G().get_A()[_pc].front();
    while (e.get_stmt().get_type() != type_stmt::ATOM) {
        const auto& pc = e.get_dest();
        switch (e.get_stmt().get_type()) {
        case type_stmt::ASSU: {
            for (auto ip = result.cbegin(); ip != result.cend(); ++ip) {
                const auto& cond = e.get_stmt().get_condition();
                if (cond.eval(ip->first, ip->second) == sool::F) /// UNSAT
                    result.erase(ip);
            }
            _pc = pc;
        }
            break;
        case type_stmt::SKIP: {
            _pc = pc;
        }
            break;
        case type_stmt::ASSG: {
            const auto& wp = this->compute_image_assg_stmt(pc, _sv, _lv);
            for (auto ip = wp.cbegin(); ip != wp.cend(); ++ip) {
                const auto& cond = e.get_stmt().get_condition();
                if (cond.is_void()
                        || (cond.eval(ip->first, ip->second, _sv, _lv)
                                != sool::F))
                    result.emplace_back(ip->first, ip->second);
            }
            _pc = pc;
        }
            break;
        default: {
            throw iotf_runtime_error(
                    "atomic section contains unable-to-tackle statements");
        }
            break;
        }

        e = parser::get_prev_G().get_A()[_pc].front();
    }
    return result;
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

} /* namespace iotf */
