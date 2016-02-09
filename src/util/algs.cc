/**
 * @brief algs.cc
 *
 * @date   Nov 17, 2015
 * @author Peizun Liu
 */

#include "algs.hh"

namespace iotf {
/**
 * @brief This function is used to increment/decrement the counters for
 * 		  all local states in T_in/T_de.
 * @param t_in
 * @param t_de
 * @param Z
 * @return local states, represented in counter abstraction form
 */
cab_locals alg::update_counters(const local_state& t_in,
        const local_state& t_de, const cab_locals& Z) {
    if (t_in == t_de)
        return Z;

    auto _Z = Z;
    auto ifind = _Z.find(t_de);
    if (ifind != _Z.end()) {
        if (--ifind->second == 0)
            _Z.erase(ifind);
    }

    ifind = _Z.find(t_in);
    if (ifind != _Z.end()) {
        ifind->second += 1;
    } else {
        _Z.emplace(t_in, 1);
    }
    return _Z;
}

/**
 * @brief This function is used to increment/decrement the counters for
 * 		  all local states in T_in/T_de.
 * @param T_in
 * @param t_de
 * @param Z
 * @return
 */
cab_locals alg::update_counters(const deque<local_state>& T_in,
        const local_state& t_de, const cab_locals& Z) {
    auto _Z = Z;

    for (const auto& t_in : T_in)
        merge(t_in, 1, _Z);

    auto ifind = _Z.find(t_de);
    if (ifind != _Z.end()) {
        if (--ifind->second == 0)
            _Z.erase(ifind);
    }

    return _Z;
}

/**
 * @brief This function is used to increment/decrement the counters for
 * 			  all local states in T_in/T_de. It calls function merge.
 * @param T_in: local states whose counter is to be incremented
 * @param T_de: local states whose counter is to to be decremented
 * @param Z: thread counter, represented in counter-abstracted form
 * @return thread counter, represented in counter-abstracted form
 */
cab_locals alg::update_counters(const deque<local_state>& T_in,
        const deque<local_state>& T_de, const cab_locals& Z) {
    auto _Z = Z;

    for (const auto& t_in : T_in) {
        merge(t_in, 1, _Z);
    }

    for (const auto& t_de : T_de) {
        auto ifind = _Z.find(t_de);
        if (ifind != _Z.end()) {
            ifind->second--;
            if (ifind->second == 0)
                _Z.erase(ifind);
        }
    }

    return _Z;
}

/**
 * @brief This function is used to update local's counter:
 * 			  (1) add n to current counter if exists local in Z, or
 * 			  (2) create a item (local, n) if exists no local in Z
 * @param local
 * @param n
 * @param Z
 */
void alg::merge(const local_state& local, const ushort& n, cab_locals& Z) {
    auto ifind = Z.find(local);
    if (ifind != Z.end()) {
        ifind->second += n;
    } else {
        Z.emplace(local, n);
    }
}

/**
 * @brief split all nondeterministic * values
 * @param vs: probably contains some *
 * @return the result after split
 */
deque<vector<sool>> alg::split(const vector<sool>& vs) {
    deque<vector<sool>> result;
    if (vs.size() == 0)
        return result;

    queue<vector<sool>> worklist;
    worklist.push(vs);
    while (!worklist.empty()) {
        auto curr = worklist.front();
        worklist.pop();
        bool is_nondet = false;
        for (auto i = 0; i < curr.size(); ++i) {
            if (curr[i] == sool::N) {
                curr[i] = sool::T;
                worklist.push(curr);
                curr[i] = sool::F;
                worklist.push(curr);
                /// mark there exist a *
                is_nondet = true;
            }
        }
        if (!is_nondet)
            result.emplace_back(curr);
    }
    return result;
}

///////////////////////////////////////////////////////////////////////////////
/// from here: class solver
///
///////////////////////////////////////////////////////////////////////////////

const short solver::CONST_F; /// constant false
const short solver::CONST_T; /// constant true
const short solver::CONST_N; /// constant nondeterminism
const short solver::NEG; /// !, negation
const short solver::AND; /// &, and
const short solver::OR;  /// |, or
const short solver::XOR; /// ^, exclusive or
const short solver::EQ;  /// =, equal
const short solver::NEQ; /// !=, not equal
const short solver::IMP; /// =>, implies
const short solver::PAR; /// parenthesis

solver::solver() {

}
solver::~solver() {

}

/**
 * @brief This is a customized "exhaustive" SAT solver, which can be used to
 *        extract targets from assertions in Boolean program. It's an
 *        exhaustive algorithm. I've no idea if we should use a more efficient
 *        SAT solver. It seems unnecessary due to that each assertion contains
 *        only very few boolean variables.
 * @param expr
 * @param s
 * @param l
 * @return a sat solver
 */
bool solver::solve(const deque<symbol>& sexpr, const state_v& s,
        const state_v& l) {
    stack<bool> worklist;
    bool op1, op2;
    for (const auto& ss : sexpr) {
        switch (ss) {
        case solver::AND:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.push(op1 & op2);
            break;
        case solver::OR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.push(op1 | op2);
            break;
        case solver::XOR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.push(op1 ^ op2);
            break;
        case solver::EQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.push(op1 == op2);
            break;
        case solver::NEQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.push(op1 != op2);
            break;
        case solver::NEG:
            op1 = worklist.top(), worklist.pop();
            worklist.push(!op1);
            break;
        case solver::PAR:
            break;
        case solver::CONST_F:
            worklist.push(false);
            break;
        case solver::CONST_T:
            worklist.push(true);
            break;
        case solver::CONST_N:
            throw iotf_runtime_error("* is not splitted");
            break;
        default: {
            bool is_shared = false;
            const auto& i = solver::decode(ss, is_shared);
            if (is_shared)
                worklist.push(s[i]);
            else
                worklist.push(l[i]);
        }
            break;
        }
    }
    return worklist.top();
}

/**
 * @brief split * into 0 and 1 during expression evaluation
 * @param sexpr:
 * @return a list of expression after splitting
 */
deque<deque<symbol>> solver::split(const deque<symbol>& sexpr) {
    deque<deque<symbol>> worklist;
    worklist.emplace_back(sexpr);
    deque<deque<symbol>> splitted;
    for (auto i = 0; i < sexpr.size(); ++i) {
        if (sexpr[i] == solver::CONST_N) {
            while (!worklist.empty()) {
                auto e1 = worklist.front();
                worklist.pop_front();
                auto e2 = e1;

                e1[i] = solver::CONST_F;
                e2[i] = solver::CONST_T;

                splitted.emplace_back(e1);
                splitted.emplace_back(e2);
            }
            splitted.swap(worklist);
        }
    }
    return worklist;
}

/**
 * @brief decode
 * @param idx
 * @param is_shared
 */
symbol solver::decode(const symbol& idx, bool& is_shared) {
    auto id = idx - 3;
    is_shared = true;
    if (id >= refs::S_VARS_NUM)
        id -= refs::S_VARS_NUM, is_shared = false;
    return id;
}

/**
 * @brief decode
 * @param idx
 * @param is_shared
 * @param is_primed
 */
symbol solver::decode(const symbol& idx, bool& is_shared, bool& is_primed) {
    auto id = idx - 3;
    if (id < refs::S_VARS_NUM + refs::L_VARS_NUM) {
        is_primed = false, is_shared = true;
        if (id >= refs::S_VARS_NUM)
            is_shared = false, id -= refs::S_VARS_NUM;
    } else {
        is_primed = true, is_shared = true;
        if (id >= 2 * refs::S_VARS_NUM + refs::L_VARS_NUM)
            is_shared = false, id -= refs::S_VARS_NUM;
        id -= refs::S_VARS_NUM + refs::L_VARS_NUM;
    }
    return id;
}

} /* namespace otf */
