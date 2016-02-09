/**
 * @brief bopp.cc
 *
 * @date  : Jan 12, 2016
 * @author: lpzun
 */

#include "aide.hh"

namespace iotf {

/**
 * @brief default constructor
 */
paide::paide() :
        is_failed(false), lineno(0), ipc(0), s_vars_num(0), l_vars_num(0), ///
        s_vars_list(), l_vars_list(), s_vars_init(), l_vars_init(), ///
        suc_pc_set(), expr_in_list(), assg_stmt_lhs(), assg_stmt_rhs(), all_pc_set() {
}

/**
 * @brief default destructor
 */
paide::~paide() {
}

/**
 * @brief add variables and initialization
 * @param var
 * @param val
 * @param is_shared
 */
void paide::add_vars(const string& var, const sool& val,
        const bool& is_shared) {
    if (is_shared) {
        const auto& p = s_vars_list.emplace(var, s_vars_num + 1);
        if (p.second)
            s_vars_init.emplace(++s_vars_num, val);
    } else {
        const auto& p = l_vars_list.emplace(var, l_vars_num + 1);
        if (p.second)
            l_vars_init.emplace(++l_vars_num, val);
    }
}
/**
 * @brief recorde the initialization of boolean variables
 * @param var
 * @param val
 */
void paide::init_vars(const string& var, const sool& val) {
    map<string, ushort>::iterator ifind;
    if ((ifind = s_vars_list.find(var)) != s_vars_list.end())
        s_vars_init[ifind->second] = val;
    else if ((ifind = l_vars_list.find(var)) != l_vars_list.end())
        l_vars_init[ifind->second] = val;
    else
        throw iotf_runtime_error("no such a variable " + var);
}

/**
 * @brief to determine if the pc is unique or not
 * @param pc
 */
bool paide::is_pc_unique(const size_pc& pc) {
    const auto& result = all_pc_set.emplace(pc);
    if (!result.second)
        throw iotf_runtime_error(
                "syntax error: pc " + std::to_string(pc) + " is duplicated.");
    return true;
}

/**
 * @brief to create the edge for goto or non-deterministic statements
 * @param from
 * @param sp
 */
void paide::add_edge(const size_pc& src, const type_stmt& type) {
    for (const auto& dest : suc_pc_set)
        cfg_G.add_edge(src, dest, type);
}

/**
 * @brief to add an edge to a control flow graph
 * @param from
 * @param to
 * @param type
 * @param is_condition
 */
void paide::add_edge(const size_pc& src, const size_pc& dest,
        const type_stmt& type, const bool& is_condition) {
    if (!is_condition) {
        cfg_G.add_edge(src, dest, type);
    } else {
        cfg_G.add_edge(src, dest, type, expr(expr_in_list));
    }
    /// build assignment
    if (type == type_stmt::ASSG) {
        cfg_G.add_assignment(src, this->create_assignment());
    }
}

/**
 * @brief build an assignment
 * @return
 */
assignment paide::create_assignment() {
    assignment assg(this->s_vars_num, this->l_vars_num);
    auto il = assg_stmt_lhs.cbegin(), iend = assg_stmt_lhs.cend();
    auto ir = assg_stmt_rhs.cbegin(), eend = assg_stmt_rhs.cend();
    while (il != iend && ir != eend) {
        cout << *il << "::::::::::::::paide::create_assignment\n";
        const auto& p = this->decode(*il);
        if (p.second)
            assg.sh[p.first] = expr(*ir);
        else
            assg.lo[p.first] = expr(*ir);
        ++il, ++ir;
    }
    return assg;
}

/**
 * @brief to add the expression symbols to a list
 * @param symbol
 */
void paide::add_to_expr_in_list(const symbol& s) {
    expr_in_list.emplace_back(s);
}

/**
 * @brief to restore the expression
 * @param symb_list
 * @param is_origi: this para is to generate the comments!!!!!!!
 * @return expression
 */
string paide::recov_expr_from_list(const deque<symbol>& sexpr) {
    stack<string> worklist;
    string op1, op2;
    for (const auto& ss : sexpr) {
        switch (ss) {
        case solver::AND:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 + " & " + op2);
            break;
        case solver::OR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 + " 1 " + op2);
            break;
        case solver::XOR:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 + " ^ " + op2);
            break;
        case solver::EQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 + " = " + op2);
            break;
        case solver::NEQ:
            op1 = worklist.top(), worklist.pop();
            op2 = worklist.top(), worklist.pop();
            worklist.emplace(op1 + " != " + op2);
            break;
        case solver::NEG:
            op1 = worklist.top(), worklist.pop();
            worklist.emplace("!" + op1);
            break;
        case solver::PAR:
            op1 = worklist.top(), worklist.pop();
            worklist.emplace("(" + op1 + ")");
            break;
        case solver::CONST_F:
            worklist.emplace("0");
            break;
        case solver::CONST_T:
            worklist.emplace("1");
            break;
        case solver::CONST_N:
            worklist.emplace("*");
            break;
        default:
            worklist.emplace(std::to_string(ss));
            break;
        }
    }
    return worklist.top();
}

/**
 * @brief look up the index of iden in the map of variables
 * @param iden
 * @return index if find var
 *         throw an exception otherwise
 */
symbol paide::encode(const string& var) {
    symbol idx = 2;
    if (var.front() != '\'') {
        auto ifind = s_vars_list.find(var);
        if (ifind == s_vars_list.end()) {
            ifind = l_vars_list.find(var);
            if (ifind != l_vars_list.end())
                idx += s_vars_num;
            else
                throw iotf_runtime_error(var + "cannot find!");
        }
        idx += ifind->second;
    } else {
        auto ifind = s_vars_list.find(var.substr(1));
        if (ifind == s_vars_list.end()) {
            ifind = l_vars_list.find(var.substr(1));
            if (ifind != l_vars_list.end())
                idx += s_vars_num;
            else
                throw iotf_runtime_error(var + "cannot find!");
        }
        idx += ifind->second + s_vars_num + l_vars_num;
    }
    return idx;
}

/**
 * @brief decode the symbol
 * @param idx
 * @return pair<symbol, bool>
 *         symbol: the symbol of Boolean variables
 *         bool  : true if shared Boolean variable
 *                 false if local Boolean variable
 */
pair<symbol, bool> paide::decode(const symbol& idx) {
    auto id = idx - 3;
    if (id < s_vars_num)
        return std::make_pair(id, true);
    else
        return std::make_pair(id - s_vars_num, false);
}

/**
 * @brief output the control flow graph to the file
 * @param file
 */
void paide::test_output_control_flow_graph() {
    for (const auto& e : cfg_G.get_E()) {
        cout << e << "\n";
    }
    for (const auto& s : cfg_G.get_assignments()) {
        cout << s.first << " " << s.second << "\n";
    }
}

/**
 * @brief a temporary function
 */
void paide::is_failed_assertion() {
    for (const auto& s : expr_in_list) {
        if (s == solver::CONST_N || s == solver::CONST_F) {
            if (!this->is_failed) {
                this->is_failed = true;
                break;
            }
        }
    }
}

/**
 * @brief testing methods
 */
void paide::test_output_parallel_assg_stmt() {
    auto i_iter = assg_stmt_lhs.begin(), i_end = assg_stmt_lhs.end();
    auto e_iter = assg_stmt_rhs.begin(), e_end = assg_stmt_rhs.end();
    while (i_iter != i_end && e_iter != e_end) {
        const auto& iden = *i_iter;
        const auto& expr = *e_iter;
        cout << iden << ":=" << recov_expr_from_list(expr) << endl;
        i_iter++, e_iter++;
    }
}

} /* namespace iotf */
