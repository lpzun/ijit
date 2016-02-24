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
 * @brief to compute all post images of global state tau: the implementation
 *        iterates over all threads: each thread is used as an active thread
 * @param tau: a program state
 * @return images: the list of post images of tau w.r.t. all threads
 */
deque<prog_state> post_image::step(const prog_state& tau) {
    DBG_LOC()
    deque<prog_state> images;
    for (const auto& p : tau.get_locals()) /// iterate over all local states
        this->compute_post_images(tau, p.first, images);
    return images;
}

/**
 * @brief to compute all post images of global state tau: the post images are
 *        computed with respect to a particular thread.
 * @param tau   : a program state
 * @param l     : a specific local state
 * @return images: the list of post images of tau w.r.t. local state <l>
 */
deque<prog_state> post_image::step(const prog_state& tau,
        const local_state& l) {
    deque<prog_state> images;
    this->compute_post_images(tau, l, images);
    return images;
}

/**
 * @brief compute all post images of a program state tau w.r.t. local state l
 * @param tau   : a program state
 * @param l     : a specific local state
 * @param images: the list of post images of tau w.r.t. one thread whose local
 *        state is l
 */
void post_image::compute_post_images(const prog_state& tau,
        const local_state& l, deque<prog_state>& images) {
    /// extract all necessary information from program state tau and
    /// local state l
    const auto& s = tau.get_s();       /// current shared state
    const auto& sv = s.get_vars();     /// shared vars: the valuation
    const auto& Z = tau.get_locals();  /// the local part of tau
    const auto& pc = l.get_pc();       /// current pc
    const auto& lv = l.get_vars();     /// local vars : the valuation

    /// iterate over all succeeding statements via <parser::post_G>
    const auto& successors = parser::get_post_G().get_A()[pc];
    for (auto ie = successors.cbegin(); ie != successors.cend(); ++ie) {
        /// extract the edge pointed by pc: e = (pc, _pc)
        const auto& e = *ie;
        const auto& _pc = e.get_dest();
        switch (e.get_stmt().get_type()) {
        case type_stmt::GOTO: {
            /// <goto> statement
            ///   pc: goto <_pc>;
            ///    ...
            ///  _pc: ...
            ///
            /// SEMANTIC: nondeterministic goto
            local_state _l(_pc, lv); /// post local state
            const auto& _Z = alg::update_counters(_l, l, Z);
            images.emplace_back(s, _Z);
        }
            break;
        case type_stmt::ASSG: {
            /// <parallel assignment> statement
            ///   pc: <id>+ := <expr>+ constrain <expr>;
            /// pc+1: ...
            ///
            /// SEMANTIC: assignment statement, postcondition of
            /// vars might have to satisfy the constraint
            cout << __func__ << " assign...\n" << sv << "\n" << lv << "\n";
            const auto& p = this->compute_image_assg_stmt(sv, lv, pc);

            /// NOTE: the "constrain <expr>" could involve the valuations
            /// for shared and local variables before and after executing
            /// assignment statement ...
            const auto& cond = e.get_stmt().get_condition();
            for (const auto& _lv : p.second) {
                local_state _l(_pc, _lv);            /// local state
                const auto& _Z = alg::update_counters(_l, l, Z);
                for (const auto& _sv : p.first)
                    if (!cond.is_valid()
                            || (cond.eval(sv, lv, _sv, _lv) != sool::F)) {
                        shared_state _s(_sv);    /// shared state
                        images.emplace_back(_s, _Z);
                    }
            }
        }
            break;
        case type_stmt::IFEL: {
            /// <if ... else ...> statement: conditional statement
            ///   pc: if (<expr>) then <sseq> else <sseq>; fi;
            /// pc+1: ...
            ///
            /// SEMANTIC:
            const auto& cond = e.get_stmt().get_condition().eval(sv, lv);
            if (cond != sool::F) {
                const auto& _l = this->compute_image_ifth_stmt(l, _pc);
                const auto& _Z = alg::update_counters(_l, l, Z);
                images.emplace_back(s, _Z);
            } else {
                const auto& _l = this->compute_image_else_stmt(l);
                const auto& _Z = alg::update_counters(_l, l, Z);
                images.emplace_back(s, _Z);
            }
        }
            break;
        case type_stmt::ASSE: {
            /// <assert> statement
            ///   pc: assert ( <expr> );
            /// pc+1: ...
            ///
            /// SEMANTIC: assertion statement: encoding bad states
            /// This is a deadend statement
            /// NOTE: for now, we treat it as a <skip> statement..
            local_state _l(_pc, lv);
            const auto& _Z = alg::update_counters(_l, l, Z);
            images.emplace_back(s, _Z);
        }
            break;
        case type_stmt::ASSU: {
            /// <assume> statement: conditional statement
            ///   pc: assume ( <expr> );
            /// pc+1: ...
            ///
            /// SEMANTIC: advance if expr is evaluated to be true;
            /// block otherwise.
            cout << __func__ << " assume...\n" << sv << "\n" << lv << "\n";
            const auto& cond = e.get_stmt().get_condition().eval(sv, lv);
            if (cond != sool::F) {
                /// successor local state: l'.pc = l.pc + 1
                local_state _l(_pc, lv);
                const auto& _Z = alg::update_counters(_l, l, Z);
                images.emplace_back(s, _Z);
            }
        }
            break;
        case type_stmt::NTHR: {
            /// <thread creation> statement like:
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
            T_in.emplace_back(pc + 1, lv);
            const auto& _Z = alg::update_counters(T_in, l, Z);
            images.emplace_back(s, _Z);
        }
            break;
        case type_stmt::ETHR: {
            /// <thread termination> statement
            ///   pc: end_thread;
            /// pc+1: ...
            ///
            /// SEMANTIC: the end_thread statement terminates the actual thread,
            /// i.e., has no successor state.
            auto _Z(Z);
            alg::decrement(l, _Z);
            images.emplace_back(s, _Z);
        }
            break;
        case type_stmt::ATOM: {
            /// the beginning statement of <atomic> section
            ///   pc: atomic_begin;
            ///   ...
            ///  pc': atomic_end;
            /// SEMANTIC: the atomic_begin statement prevents the scheduler from
            /// switching a context to another thread
            /// NOTE    : the atomic_end statement is not processed here, but in
            /// the subroutine.

            /// nss, i.e., new shared valuation, is to store the final shared
            /// states after across atomic section
            deque<state_v> nsv;
            /// lss, i.e., new local  valuation, is to store the final local
            /// states after across atomic section
            deque<state_v> nlv;

            auto ppc(_pc);
            this->compute_image_atom_sect(sv, lv, ppc, nsv, nlv);
            cout << nsv.size() << " ======///===== " << nlv.size() << "\n";
            for (const auto& _lv : nlv) { /// first iterate over local states
                const auto& _Z = alg::update_counters(local_state(ppc, _lv), l,
                        Z);
                for (const auto& _sv : nsv) ///then iterate over shared states
                    images.emplace_back(shared_state(_sv), _Z);
            }
        }
            break;
        case type_stmt::BCST: {
            /// <broadcast> statement
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
                const auto& waiting =
                        parser::get_post_G().get_A()[ilo->first.get_pc()];
                if (waiting.front().get_stmt().get_type() == type_stmt::WAIT) {
                    auto l_wait(ilo->first);
                    l_wait.set_pc(ilo->first.get_pc() + 1);
                    auto n_wait(ilo->second);
                    _Z.erase(ilo); /// remove old pair
                    _Z.emplace(l_wait, n_wait);
                }
            }

            /// advance the broadcast thread
            auto l_bcst(l);
            l_bcst.set_pc(l.get_pc() + 1);
            _Z = alg::update_counters(l_bcst, l, _Z);
            images.emplace_back(s, _Z);
        }
            break;
        case type_stmt::WAIT: {
            /// <wait> statement
            ///   pc: wait;
            /// pc+1: ...
            /// SEMANTIC: blocks the execution of a thread. Therefore:
            /// There is NO post-image just by itself. It has to be paired
            /// with broadcast, and thus it will be handled in <broadcast>
            /// statement.
        }
            break;
        default: {
            /// this case mostly says the <skip> statement
            ///   pc: skip;
            /// pc+1: ...
            /// SEMANTIC: advance the pc to pc + 1

            /// successor local state: l'.pc = l.pc + 1
            local_state _l(_pc, lv);
            const auto& _Z = alg::update_counters(_l, l, Z);
            images.emplace_back(s, _Z);
        }
            break;
        }
    }
}

/**
 * @brief compute post image after an parallel assignment statement
 * @param s
 * @param start
 * @param assgs
 * @param sh
 * @param lo
 */
pair<deque<state_v>, deque<state_v>> post_image::compute_image_assg_stmt(
        const state_v& s, const state_v& l, const size_pc& pc) {
    deque<state_v> svs;
    svs.emplace_back(s);
    deque<state_v> lvs;
    lvs.emplace_back(l);
    auto ifind = parser::get_post_G().get_assignments().find(pc);
    if (ifind != parser::get_post_G().get_assignments().end()) {
        const auto& sh = ifind->second.sh;
        for (auto i = 0; i < sh.size(); ++i) {
            if (sh[i].is_valid())
                split(sh[i].eval(s, l), i, svs);
        }
        const auto& lo = ifind->second.lo;
        for (auto i = 0; i < lo.size(); ++i) {
            if (lo[i].is_valid())
                split(lo[i].eval(s, l), i, lvs);
        }
    }

    cout << __func__ << "\n";
    cout << "shared...\n";
    for (const auto& s : svs)
        cout << s << endl;
    cout << "local ...\n";
    for (const auto& l : lvs)
        cout << l << endl;
    return std::make_pair(svs, lvs);
}

/**
 * @brief split nondeterministic value into false and true
 * @param v
 * @param i
 * @param svs
 */
void post_image::split(const sool& v, const size_t& i, deque<state_v>& svs) {
    switch (v) {
    case sool::F:
        for (auto& sv : svs) {
            sv[i] = 0;
        }
        break;
    case sool::T:
        for (auto& sv : svs) {
            sv[i] = 1;
        }
        break;
    default:
        for (auto& sv : svs) {
            sv[i] = 0;
            auto cp(sv); /// build a copy of sv
            cp[i] = 1;
            svs.emplace_back(cp);
        }
        break;
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
 * @param  sv: shared state at the beginning of atomic section
 *           It's also used to return the final shared state after the
 *           atomic section.
 * @param  lv: local state at the beginning of atomic section
 * @param pc: current pc
 * @param svs: the shared valuations after executing atomic section
 * @param lvs: the local  valuations after executing atomic section
 */
void post_image::compute_image_atom_sect(const state_v& sv, const state_v& lv,
        size_pc& pc, deque<state_v>& svs, deque<state_v>& lvs) {
    auto e = parser::get_post_G().get_A()[pc].front();
    auto stmt = e.get_stmt().get_type();

    while (stmt != type_stmt::EATM) {
        auto _pc = e.get_dest();
        cout << _pc << " " << stmt << "===================\n";
        switch (stmt) {
        case type_stmt::ASSU: {
            /// <assume> statement in atomic section:
            /// if expression is evaluated as false, then it blocks here,
            /// i.e., it is locked in atomic section and waits for unlock
            const auto& cond = e.get_stmt().get_condition();
            if (cond.eval(sv, lv) == sool::F) /// unsatisfiable in assume
                return;
            pc = _pc;
        }
            break;
        case type_stmt::SKIP: {
            /// <skip> statement in atomic section:
            /// this does nothing but updates pc
            pc = _pc;
        }
            break;
        case type_stmt::ASSG: {
            /// <parallel assignment> statement:
            /// SEMANTIC: assignment statement, postcondition of
            /// vars might have to satisfy the constraint
            const auto& p = this->compute_image_assg_stmt(sv, lv, pc);
            const auto& cond = e.get_stmt().get_condition();

            cout << svs.size() << " ======/===//===== " << lvs.size() << "\n";
            if (cond.is_valid())
                svs = p.first, lvs = p.second;
            else
                for (const auto& _sv : p.first) { // TODO a bug here: duplicate
                    for (const auto& _lv : p.second)
                        if (cond.eval(sv, lv, _sv, _lv) != sool::F)
                            svs.emplace_back(_sv), lvs.emplace_back(_lv);
                }
            pc = _pc;
        }
            break;
        default: {
            DBG_LOC()
            throw iotf_runtime_error(
                    "atomic section appears unable-to-tackle statements");
        }
            break;
        }

        cout << pc << "\n";
        e = parser::get_post_G().get_A()[pc].front();
        stmt = e.get_stmt().get_type();
    }

    pc += 1; /// advance one more step on <atomic_end>
    /// add sv back if no successor
    if (svs.empty())
        svs.emplace_back(sv);
    /// add lv back if no successor
    if (lvs.empty())
        lvs.emplace_back(lv);
}

} /* namespace otf */
