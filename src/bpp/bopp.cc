/**
 * @brief bopp.cc
 *
 * @date  : Jan 12, 2016
 * @author: lpzun
 */

#include "bopp.hh"

namespace iotf {


/**
 * @brief extract initial states from Boolean programs
 * @param minit
 * @return string
 */
string fw_aide::create_init_state(const map<ushort, char>& minit) {
    string ss = "";
    for (auto is = minit.begin(), end = minit.end(); is != end; is++) {
        ss.push_back(',');
        ss.push_back(is->second);
    }
    if (ss.size() > 1)
        ss = ss.substr(1);
    return ss;
}

/**
 * @brief to add the shared variables to a map
 * @param var
 * @param index
 * @return
 */
bool fw_aide::add_to_shared_vars_list(const string& var, const ushort& index) {
    auto p = s_vars_list.emplace(var, index);
    return p.second;
}

/**
 * @brief to add the shared variables to a map
 * @param var
 * @param index
 * @return
 */
bool fw_aide::add_to_local_vars_list(const string& var, const ushort& index) {
    auto p = l_vars_list.emplace(var, index);
    return p.second;
}

/**
 * @brief to add the expression symbols to a list
 * @param symbol
 */
void fw_aide::add_to_expr_symb_list(const string& symbol) {
    expr_symb_list.emplace_back(symbol);
}

/***************************** Control Flow Graph *****************************/
/**
 * @brief to determine if the pc is unique or not
 * @param pc
 */
bool fw_aide::is_pc_unique(const ushort& pc) {
    auto result = pc_set.emplace(pc);
    if (!result.second) {
        cerr << "syntax error: pc " << pc << " is duplicated." << endl;
        return false;
    }
    return true;
}

/**
 * @brief to create the edge for sequential statement
 * @param from
 * @param to
 * @param wp weakest precondition formula
 */
void fw_aide::create_control_flow_graph(const ushort& from, const string& sp) {
    string edge;
    edge.append(std::to_string(from)).append(" ").append(sp);
    control_flow_graph.emplace_back(edge);
}

/**
 * @brief output the control flow graph to the file
 * @param file
 */
void fw_aide::output_control_flow_graph(FILE *file) {
    for (auto iter = control_flow_graph.begin(), end = control_flow_graph.end();
            iter != end; iter++) {
        fprintf(file, "%s\n", (*iter).c_str());
    }
}

/**
 * @brief goto statement
 * @return
 */
string fw_aide::create_goto_stmt_sp() {
    return fw_aide::STMT_NTHR + " " + goto_targets.substr(1);
}

/**
 * @brief skip statement
 * @return
 */
string fw_aide::create_skip_stmt_sp() {
    return fw_aide::STMT_SKIP;
}

/**
 * @brief assume statement
 * @return
 */
string fw_aide::create_assume_stmt_sp() {
    auto expr = recov_expr_from_symb_list(expr_symb_list);
    return fw_aide::STMT_ATOM + " " + expr;
}

/**
 * @brief assert statement, same as the skip statement
 * @return
 */
string fw_aide::create_assert_stmt_sp() {
    return fw_aide::STMT_SKIP;
}

/**
 * @brief assignment statement
 *    _x = x, where _x is the successor
 * @return string
 */
string fw_aide::create_assign_stmt_sp() {
    auto ii = assign_stmt_lhs.begin(), iend = assign_stmt_lhs.end();
    auto ie = assign_stmt_rhs.begin(), eend = assign_stmt_rhs.end();
    string formula;
    while (ii != iend && ie != eend) {
        const auto& iden = *ii;
        const auto& expr = output_expr_as_str_from_symb_list(*ie);
        formula.append(";").append(look_up_var_index(iden)).append(",").append(
                expr);
        ii++, ie++;
    }
    return fw_aide::STMT_ETHR + " " + formula.substr(1);
}

/**
 * @brief if (expr == true) then statement
 * @param e
 */
void fw_aide::create_if_true_stmt_sp(const string& e) {
    const auto& edge = control_flow_graph.back();
    control_flow_graph.pop_back();
    if (e.find_first_of('*') != std::string::npos)
        control_flow_graph.push_back(edge);
    else
        control_flow_graph.push_back(edge + fw_aide::_AND_ + e);
}

/**
 * @brief if (expr == false); next statement
 * @param e
 * @return string
 */
string fw_aide::create_if_false_stmt_sp(const string& e) {
    if (e.find_first_of('*') != std::string::npos) {
        return "";
    } else if (e.at(0) == '!') {
        return "" + fw_aide::_AND_ + "(" + e.substr(1) + ")";
    }
    return "" + fw_aide::_AND_ + "(!" + e + ")";
}

/**
 * @brief start_thread <pc>
 * @param pc
 * @return string
 */
string fw_aide::create_new_thr_stmt_sp(const string& pc) {
    return fw_aide::STMT_GOTO + " " + pc;
}

/**
 * @brief wait
 * @return string
 */
string fw_aide::create_wait_stmt_sp() {
    return fw_aide::STMT_ASSG;
}

/**
 * @brief broadcast
 * @return string
 */
string fw_aide::create_broadcast_stmt_sp() {
    return fw_aide::STMT_IFEL;
}

/**
 * @brief atomic statement: begin and end
 * @return string
 */
string fw_aide::create_atom_stmt_sp() {
    return fw_aide::STMT_ASSE;
}

/**
 * @brief look up the index of iden in the map of variables
 * @param iden
 * @return index if find var
 *     -1 otherwise
 */
string fw_aide::look_up_var_index(const string& var) {
    map<string, ushort>::iterator ifind;
    if ((ifind = s_vars_list.find(var)) != s_vars_list.end()) {
        return std::to_string(ifind->second);
    } else if ((ifind = l_vars_list.find(var)) != l_vars_list.end()) {
        return std::to_string(ifind->second + l_vars_list.size());
    }
    return "-1";
}

/**
 * @brief to output the name of successor's variable
 * @param var
 * @return string var + SUCC_POSTFIX
 */
string fw_aide::create_succ_vars(const string& var) {
    return fw_aide::SUCC_POSTFIX + var;
}

/**
 * @brief to restore the expression
 * @param symb_list
 * @param is_origi: this para is to generate the comments!!!!!!!
 * @return expression
 */
string fw_aide::output_expr_as_str_from_symb_list(
        const deque<string>& symb_list) {
    string formula;
    for (auto begin = symb_list.begin(), end = symb_list.end(); begin != end;
            begin++) {
        string symbol = *begin;
        /// using regular expression here would be a better choice
        if (!(symbol.compare("&&") == 0 || symbol.compare("||") == 0
                || symbol.compare("!=") == 0 || symbol.compare("==") == 0
                || symbol.compare("^") == 0 || symbol.compare("()") == 0
                || symbol.compare("!") == 0
                || symbol.compare(fw_aide::ZERO) == 0
                || symbol.compare(fw_aide::ONE) == 0
                || symbol.compare(fw_aide::KLEENE_STAR) == 0)) {
            formula.append(",").append(look_up_var_index(symbol));
        } else {
            formula.append(",").append(symbol);
        }
    }
    return formula.substr(1);
}

/**
 * @brief to restore the expression
 * @param symb_list
 * @param is_origi: this para is to generate the comments!!!!!!!
 * @return expression
 */
string fw_aide::recov_expr_from_symb_list(const deque<string>& symb_list,
        const bool& is_origi) {
    stack<string> expr_comp;
    for (auto begin = symb_list.begin(), end = symb_list.end(); begin != end;
            begin++) {
        string symbol = *begin;
        string operand1 = "", operand2 = "";
        if (symbol.compare("&&") == 0) { // and
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " && " + operand1);
        } else if (symbol.compare("||") == 0) { // or
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " || " + operand1);
        } else if (symbol.compare("==") == 0) { // equal
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " == " + operand1);
        } else if (symbol.compare("!=") == 0) { // not equal
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " != " + operand1);
        } else if (symbol.compare("^") == 0) { // exclusive or
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " ^ " + operand1);
        } else if (symbol.compare("()") == 0) { // bracket
            operand1 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push("(" + operand1 + ")");
        } else if (symbol.compare(fw_aide::NEGATION) == 0) { // negation
            operand1 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(fw_aide::NEGATION + operand1);
        } else if (symbol.compare(fw_aide::KLEENE_STAR) == 0) { // non-deterministic
            expr_comp.push(fw_aide::KLEENE_STAR);
        } else if (symbol.compare(fw_aide::ZERO) == 0) { // constant 0
            expr_comp.push(symbol);
        } else if (symbol.compare(fw_aide::ONE) == 0) { // constant 1
            expr_comp.push(symbol);
        } else { // variables
            expr_comp.push(is_origi ? symbol : create_succ_vars(symbol));
        }
    }
    return expr_comp.top();
}

/******************** Extract Thread States From an Assertion ***********************/

/**
 * @brief This is a customized "exhaustive" SAT solver, which can be used to extract targets
 *    from assertions in Boolean program. It's an exhaustive algorithm. I've no idea if
 *        we should use a more efficient SAT solver. It seems unnecessary due to that each
 *        assertion contains only very few boolean variables.
 * @note Here, we assume the assertion doesn't contain any constant, i.e., *, 0, 1.
 * @param symb_list: an expression
 * @param pc
 * @return a set of satisfiable assignments
 */
void fw_aide::exhaustive_sat_solver(const deque<string>& symb_list,
        const ushort& pc) {
    deque<string> s_target_list;
    map<string, ushort> assert_vars; // boolean variables in the assertion
    ushort assert_vars_num = 0; // the number of boolean variables in the assertion
    for (auto begin = symb_list.begin(), end = symb_list.end(); begin != end;
            begin++) {
        string symbol = *begin;
        /// using regular expression here would be a better choice
        if (!(symbol.compare("&&") == 0 || symbol.compare("||") == 0
                || symbol.compare("!=") == 0 || symbol.compare("==") == 0
                || symbol.compare("^") == 0 || symbol.compare("()") == 0
                || symbol.compare("!") == 0
                || symbol.compare(fw_aide::ZERO) == 0
                || symbol.compare(fw_aide::ONE) == 0)) {
            if (symbol.compare(fw_aide::KLEENE_STAR) == 0) {
                vector<ushort> t_shared(s_vars_list.size(), 2);
                vector<ushort> t_locals(l_vars_list.size(), 2);
                string ss;
                if (create_vars_value_as_str(t_shared).size() > 1)
                    ss.append(create_vars_value_as_str(t_shared).substr(1));
                ss.append("|").append(std::to_string(pc)).append(
                        create_vars_value_as_str(t_locals));
                s_target_list.push_back(ss);
                valid_assertion_ts.emplace(pc, s_target_list);
                return;
            } else {
                assert_vars.emplace(symbol, assert_vars_num);
                assert_vars_num++;
            }
        }
    }

    for (ushort i = 0; i < power(2, assert_vars_num); i++) {
        vector<bool> assert_vars_assignments = decimal2binary(i,
                assert_vars_num);
        vector<ushort> t_shared(s_vars_list.size(), 2);
        vector<ushort> t_locals(l_vars_list.size(), 2);

        stack<bool> comp_result_stack;
        for (auto begin = symb_list.begin(), end = symb_list.end();
                begin != end; begin++) {
            string symbol = *begin;
            bool operand1, operand2;
            if (symbol.compare("&&") == 0) { // and
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 && operand1);
            } else if (symbol.compare("||") == 0) { // or
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 || operand1);
            } else if (symbol.compare("==") == 0) { // equal
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 == operand1);
            } else if (symbol.compare("!=") == 0) { // not equal
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 != operand1);
            } else if (symbol.compare("^") == 0) { // exclusive or
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 ^ operand1);
            } else if (symbol.compare("()") == 0) { // bracket
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push((operand1));
            } else if (symbol.compare("!") == 0) { // negation
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(!operand1);
            } else if (symbol.compare(fw_aide::ZERO) == 0) { // constant 0
                comp_result_stack.push(false);
            } else if (symbol.compare(fw_aide::ONE) == 0) { // constant 1
                comp_result_stack.push(true);
            } else { // variables
                map<string, ushort>::iterator ifind;
                if ((ifind = assert_vars.find(symbol)) != assert_vars.end()) {
                    bool b_value = assert_vars_assignments[ifind->second];
                    comp_result_stack.push(b_value);
                    if ((ifind = s_vars_list.find(symbol)) != s_vars_list.end())
                        t_shared[ifind->second - 1] = b_value;
                    else if ((ifind = l_vars_list.find(symbol))
                            != l_vars_list.end())
                        t_locals[ifind->second - 1] = b_value;
                }
            }
        }

        if (!comp_result_stack.top()) {
            string ss;
            if (create_vars_value_as_str(t_shared).size() > 1)
                ss.append(create_vars_value_as_str(t_shared).substr(1));
            ss.append("|").append(std::to_string(pc)).append(
                    create_vars_value_as_str(t_locals));
            s_target_list.push_back(ss);
        }
    }
    fw_aide::valid_assertion_ts.emplace(pc, s_target_list);
}

/**
 * @brief covert a decimal to binary
 * @param n
 * @param size
 * @return vector<bool>: the first element is the least-significant bit
 */
vector<bool> fw_aide::decimal2binary(const int& n, const int& size) {
    vector<bool> bv(size, false);
    ushort dividend = n, i = 0;
    do {
        bool mod = dividend % 2;
        dividend = dividend / 2;
        bv[i++] = mod;
    } while (dividend >= 1);
    return bv;
}

/**
 * @brief power computation
 * @param base
 * @param exp
 * @return
 */
ushort fw_aide::power(const ushort& base, const ushort& exp) {
    ushort result = 1;
    for (ushort i = 0; i < exp; ++i)
        result *= base;
    return result;
}

/**
 * @brief convert the vector<ushort> to a shared/local state
 * @param sv
 */
string fw_aide::create_vars_value_as_str(const vector<ushort>& sv) {
    string target;
    for (auto iter = sv.begin(), end = sv.end(); iter != end; iter++) {
        const ushort val = *iter;
        switch (val) {
        case 0:
            target.append(",0");
            break;
        case 1:
            target.append(",1");
            break;
        case 2:
            target.append(",*");
            break;
        }
    }
    return target;
}

/**
 * @brief to print thread state extracted from assertion
 */
void fw_aide::output_assertion_ts_to_file(const string& filename) {
    FILE* file = fopen(filename.c_str(), "w");
    for (auto iter = valid_assertion_ts.begin(), end = valid_assertion_ts.end();
            iter != end; iter++) {
        const auto& pc = iter->first;
        const auto& tss = iter->second;
        fprintf(file, "#%d\n", pc);
        for (auto l_iter = tss.begin(), l_end = tss.end(); l_iter != l_end;
                l_iter++) {
            const string& assign = *l_iter;
            fprintf(file, "%s\n", assign.c_str());
        }
        fprintf(file, "\n");
    }
    fclose(file);
}

/**
 * @brief testing methods
 */
void fw_aide::test_output_parallel_assign_stmt() {
    auto i_iter = assign_stmt_lhs.begin(), i_end = assign_stmt_lhs.end();
    auto e_iter = assign_stmt_rhs.begin(), e_end = assign_stmt_rhs.end();
    while (i_iter != i_end && e_iter != e_end) {
        const auto& iden = *i_iter;
        const auto& expr = *e_iter;
        cout << iden << ":=" << recov_expr_from_symb_list(expr, true) << endl;
        i_iter++, e_iter++;
    }
}

/**
 * @brief to print thread state extracted from assertion
 */
void fw_aide::test_print_valid_assertion_ts() {
    for (auto iter = valid_assertion_ts.begin(), end = valid_assertion_ts.end();
            iter != end; iter++) {
        const auto& pc = iter->first;
        const auto& tss = iter->second;
        for (auto l_iter = tss.begin(), l_end = tss.end(); l_iter != l_end;
                l_iter++) {
            const auto& assign = *l_iter;
            cout << pc << ":" << assign << endl;
        }
    }
}

} /* namespace iotf */
