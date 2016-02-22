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
    DBG_LOC()
    auto _Z = Z;
    DBG_LOC()
    auto ifind = _Z.find(t_de);
    DBG_LOC()
    if (ifind != _Z.end()) {
        DBG_LOC()
        ifind->second -= 1;
        if (ifind->second == 0)
            _Z.erase(ifind);
    }
    DBG_LOC()

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
        ifind->second -= 1;
        if (ifind->second == 0)
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
            ifind->second -= 1;
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
            worklist.emplace(op1 & op2);
            break;
        case solver::OR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 | op2);
            break;
        case solver::XOR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 ^ op2);
            break;
        case solver::EQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 == op2);
            break;
        case solver::NEQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 != op2);
            break;
        case solver::NEG:
            op1 = worklist.top(), worklist.pop();
            worklist.emplace(!op1);
            break;
        case solver::PAR:
            break;
        case solver::CONST_F:
            worklist.emplace(false);
            break;
        case solver::CONST_T:
            worklist.emplace(true);
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
 * @brief This is a customized "exhaustive" SAT solver, which can be used to
 *        extract targets from assertions in Boolean program. It's an
 *        exhaustive algorithm. I've no idea if we should use a more efficient
 *        SAT solver. It seems unnecessary due to that each assertion contains
 *        only very few boolean variables.
 * @param sexpr
 * @param s
 * @param l
 * @param _s
 * @param _l
 * @return
 */
bool solver::solve(const deque<symbol>& sexpr, const state_v& s,
        const state_v& l, const state_v& _s, const state_v& _l) {
    stack<bool> worklist;
    bool op1, op2;
    for (const auto& ss : sexpr) {
        switch (ss) {
        case solver::AND:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 & op2);
            break;
        case solver::OR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 | op2);
            break;
        case solver::XOR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 ^ op2);
            break;
        case solver::EQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 == op2);
            break;
        case solver::NEQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 != op2);
            break;
        case solver::NEG:
            op1 = worklist.top(), worklist.pop();
            worklist.emplace(!op1);
            break;
        case solver::PAR:
            break;
        case solver::CONST_F:
            worklist.emplace(false);
            break;
        case solver::CONST_T:
            worklist.emplace(true);
            break;
        case solver::CONST_N:
            throw iotf_runtime_error("* is not splitted");
            break;
        default: {
            bool is_shared = false, is_primed = false;
            const auto& i = solver::decode(ss, is_shared, is_primed);
            if (!is_primed) { /// normal variables
                if (is_shared)
                    worklist.push(s[i]);
                else
                    worklist.push(l[i]);
            } else { /// primed variables
                if (is_shared)
                    worklist.push(_s[i]);
                else
                    worklist.push(_l[i]);
            }
        }
            break;
        }
    }
    return worklist.top();
}

/**
 * @brief an all sat solver
 * @param sexpr
 * @return
 */
deque<pair<ss_vars, sl_vars>> solver::all_sat_solve(
        const deque<symbol>& sexpr) {
    deque<pair<ss_vars, sl_vars>> result;

    /// step 1: collect the ids of Boolean variables:
    ///         this is a subset of all variables
    map<symbol, ushort> active_id;
    ushort num = 0; /// number of active variables
    for (const auto& s : sexpr) {
        if (s > solver::CONST_N) {
            const auto& p = active_id.emplace(s, num);
            if (p.second)
                ++num;
        }
    }

    /// if the expression does not involve any variable, then
    /// evaluate the expression, and based on the result:
    /// (1) true : all assignments satisfy the expression,
    /// (2) false: no assignment satisfies the expression.
    if (num == 0) {
        if (solver::eval(sexpr)) {
            ss_vars sassg(refs::S_VARS_NUM, sool::N);
            sl_vars lassg(refs::L_VARS_NUM, sool::N);
            result.emplace_back(sassg, lassg);
        }
        return result;
    }

    /// step 2: enumerate over all possible valuations
    ///         of active Boolean variables
    for (auto assg = 0; assg < pow(2, num); ++assg) {
        /// step 3: build an assignment to active variables
        const auto& bv = solver::to_binary(assg, num);

        ss_vars s_tmp(refs::S_VARS_NUM, sool::N);
        sl_vars l_tmp(refs::L_VARS_NUM, sool::N);

        /// step 4: replace Boolean variables by its values
        auto se = sexpr;
        for (auto i = 0; i < se.size(); ++i) {
            if (se[i] > solver::CONST_N) {
                auto ifind = active_id.find(se[i]);
                se[i] = bv[ifind->second];

                bool is_shared = false;
                const auto& idx = solver::decode(se[i], is_shared);
                if (is_shared)
                    s_tmp[idx] = bv[ifind->second] ? sool::T : sool::F;
                else
                    l_tmp[idx] = bv[ifind->second] ? sool::T : sool::F;
            }
        }

        /// step 5: evaluate the expression
        if (solver::eval(se)) {
            result.emplace_back(s_tmp, l_tmp);
        }
    }

    return result;
}

/**
 * @brief split * into 0 and 1 during expression evaluation
 * @param sexpr: a expression with *
 * @return a list of expressions after splitting * into 0 and 1
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
 * @brief split * into 0 and 1 during expression evaluation
 * @param sexpr: a expression with *
 * @return a list of expressions after splitting * into 0 and 1
 */
deque<deque<sool>> solver::split(const deque<sool>& vsool) {
    deque<deque<sool>> worklist;
    worklist.emplace_back(vsool);
    deque<deque<sool>> splitted;
    for (auto i = 0; i < vsool.size(); ++i) {
        if (vsool[i] == sool::N) {
            while (!worklist.empty()) {
                auto v1 = worklist.front();
                worklist.pop_front();
                auto v2 = v1;

                v1[i] = sool::F;
                v2[i] = sool::T;

                splitted.emplace_back(v1);
                splitted.emplace_back(v2);
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

/**
 * @brief convert a unsigned to a binary representation
 * @param n
 * @param bits
 * @return a binary stored in vector<bool>
 */
vector<bool> solver::to_binary(const int& n, const short& shift) {
    auto num = n;
    vector<bool> bv(shift);
    for (auto i = 0; i < shift; ++i) {
        int b = (num >> i) & 1;
        bv[i] = b == 1 ? 1 : 0;
    }
    return bv;
}

/**
 * @brief to computer power(base, exponent)
 * @param base
 * @param bits
 * @return
 */
int solver::power(const int& base, const int& exponent) {
    auto shift = exponent;
    int result = 1;
    while (shift-- > 0) {
        result *= base;
    }
    return result;
}

/**
 * @brief to evaluate a Boolean expression whose variables have
 *        already been replaced by their valuations.
 * @param sexpr: a Boolean expression
 * @return evaluation result: true or false
 */
bool solver::eval(const deque<symbol>& sexpr) {
    stack<bool> worklist;
    bool op1, op2;
    for (const auto& ss : sexpr) {
        switch (ss) {
        case solver::AND:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 & op2);
            break;
        case solver::OR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 | op2);
            break;
        case solver::XOR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 ^ op2);
            break;
        case solver::EQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 == op2);
            break;
        case solver::NEQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 != op2);
            break;
        case solver::NEG:
            op1 = worklist.top(), worklist.pop();
            worklist.emplace(!op1);
            break;
        case solver::PAR:
            break;
        case solver::CONST_F:
            worklist.emplace(false);
            break;
        case solver::CONST_T:
            worklist.emplace(true);
            break;
        case solver::CONST_N:
            throw iotf_runtime_error("* is not splitted");
            break;
        default:
            throw("A variable appears in solver::eval()");
            break;
        }
    }
    cout << "worklist.top(): " << worklist.top() << "\n";
    return worklist.top();

}

} /* namespace otf */
