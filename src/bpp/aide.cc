/**
 * @brief bopp.cc
 *
 * @date  : Jan 12, 2016
 * @author: lpzun
 */

#include "aide.hh"

namespace iotf {

////////////////////////// Control Flow Graph ///////////////////////////////
/**
 * @brief to determine if the pc is unique or not
 * @param pc
 */
bool paide::is_pc_unique(const size_pc& pc) {
    auto result = pc_set.emplace(pc);
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
    for (auto ie = succ_pc_set.begin(); ie != succ_pc_set.end(); ++ie)
        cfg_G.add_edge(edge(src, *ie, type));
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
        cfg_G.add_edge(edge(src, dest, type));
    } else {
        cfg_G.add_edge(edge(src, dest, type, expr(expr_in_list)));
    }
    /// build assignment
    if (type == type_stmt::ASSG) {
        cfg_G.add_assignment(src, this->create_assignment());
    }
}

/**
 * @brief output the control flow graph to the file
 * @param file
 */
void paide::output_control_flow_graph(FILE *file) {
    for (auto i = cfg_G.get_E().begin(); i != cfg_G.get_E().end(); ++i) {
        cout << i->get_src() << "->" << i->get_dest() << " " << endl;
    }
}

/**
 * @brief extract initial states from Boolean programs
 * @param minit
 * @return string
 */
string paide::create_init_state(const map<ushort, sool>& minit) {
    string ss = "";
    for (auto is = minit.begin(); is != minit.end(); ++is) {
        ss.push_back(',');
        switch (is->second) {
        case sool::N:
            ss.push_back('*');
            break;
        case sool::F:
            ss.push_back('0');
            break;
        default:
            ss.push_back('1');
            break;
        }

    }
    if (ss.size() > 1)
        ss = ss.substr(1);
    return ss;
}

/**
 * @brief build an assignment
 * @return
 */
assignment paide::create_assignment() {
//    for (auto iid = s_vars_list.begin(); iid != s_vars_list.end(); ++iid)//todo testing
//        cout << iid->first << " " << iid->second << endl;
//
//    cout << this->s_vars_num << " " << this->l_vars_num << endl; //todo testing
    assignment assg(this->s_vars_num, this->l_vars_num);
    auto il = assign_stmt_lhs.begin(), iend = assign_stmt_lhs.end();
    auto ir = assign_stmt_rhs.begin(), eend = assign_stmt_rhs.end();
    while (il != iend && ir != eend) {
        const auto& p = look_up_var_index(*il);
//        cout << "==========" << p.second << endl;
        if (p.first)
            assg.sh[p.second] = expr(*ir);
        else
            assg.lo[p.second] = expr(*ir);
        ++il, ++ir;
    }
    return assg;
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
string paide::recov_expr_from_list(const deque<symbol>& symb_list,
        const bool& is_origi) {
    stack<string> expr_comp;
    for (auto is = symb_list.begin(); is != symb_list.end(); ++is) {
        const auto& s = *is;
        cout << s << " " << endl;
        string operand1 = "", operand2 = "";
        if (s.compare("&") == 0) { // and
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " & " + operand1);
        } else if (s.compare("|") == 0) { // or
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " | " + operand1);
        } else if (s.compare("=") == 0) { // equal
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " = " + operand1);
        } else if (s.compare("!=") == 0) { // not equal
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " != " + operand1);
        } else if (s.compare("^") == 0) { // exclusive or
            operand1 = expr_comp.top();
            expr_comp.pop();
            operand2 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(operand2 + " ^ " + operand1);
        } else if (s.compare("()") == 0) { // bracket
            operand1 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push("(" + operand1 + ")");
        } else if (s.compare(refs::NEG) == 0) { // negation
            operand1 = expr_comp.top();
            expr_comp.pop();
            expr_comp.push(refs::NEG + operand1);
        } else if (s.compare(refs::CONST_N) == 0) { // non-deterministic
            expr_comp.push(refs::CONST_N);
        } else if (s.compare(refs::CONST_F) == 0) { // constant 0
            expr_comp.push(s);
        } else if (s.compare(refs::CONST_N) == 0) { // constant 1
            expr_comp.push(s);
        } else { // variables
            expr_comp.push(is_origi ? s : create_succ_vars(s));
        }
    }
    return expr_comp.top();
}

/**
 * @brief This is a customized "exhaustive" SAT solver, which can be used to
 *        extract targets from assertions in Boolean program. It's an
 *        exhaustive algorithm. I've no idea if we should use a more efficient
 *        SAT solver. It seems unnecessary due to that each assertion contains
 *        only very few boolean variables.
 * @note Here, we assume the assertion doesn't contain any constant, i.e., *, 0, 1.
 * @param symb_list: an expression
 * @param pc
 * @return a set of satisfiable assignments
 */
void paide::all_sat_solver(const deque<string>& symb_list, const ushort& pc) {
    deque<string> s_target_list;
    map<string, ushort> assert_vars; /// boolean variables in the assertion
    ushort assert_vars_num = 0; /// the # of boolean variables in the assertion
    for (auto is = symb_list.begin(); is != symb_list.end(); ++is) {
        const auto& s = *is;
        /// using regular expression here would be a better choice
        if (!(s.compare(refs::AND) == 0 || s.compare(refs::OR) == 0
                || s.compare(refs::NEQ) == 0 || s.compare(refs::EQ) == 0
                || s.compare(refs::XOR) == 0 || s.compare(refs::NEG) == 0
                || s.compare(refs::PAREN_L + refs::PAREN_R) == 0
                || s.compare(refs::CONST_F) == 0
                || s.compare(refs::CONST_T) == 0)) {
            if (s.compare(refs::CONST_N) == 0) {
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
                assert_vars.emplace(s, assert_vars_num);
                assert_vars_num++;
            }
        }
    }

    for (auto i = 0; i < static_cast<int>(std::pow(2, assert_vars_num)); i++) {
        vector<bool> assert_vars_assignments = decimal2binary(i,
                assert_vars_num);
        vector<ushort> t_shared(s_vars_list.size(), 2);
        vector<ushort> t_locals(l_vars_list.size(), 2);

        stack<bool> comp_result_stack;
        for (auto is = symb_list.begin(); is != symb_list.end(); ++is) {
            const auto& symbol = *is;
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
            } else if (symbol.compare(refs::CONST_F) == 0) { // constant 0
                comp_result_stack.push(false);
            } else if (symbol.compare(refs::CONST_T) == 0) { // constant 1
                comp_result_stack.push(true);
            } else { // variables
                map<string, ushort>::iterator ifind;
                if ((ifind = assert_vars.find(symbol)) != assert_vars.end()) {
                    const auto& b_value = assert_vars_assignments[ifind->second];
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
    this->valid_assertion_ts.emplace(pc, s_target_list);
}

/**
 * @brief covert a decimal to binary
 * @param n
 * @param size
 * @return vector<bool>: the first element is the least-significant bit
 */
vector<bool> paide::decimal2binary(const int& n, const int& size) {
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
 * @brief to print thread state extracted from assertion
 */
void paide::output_final_state_to_file(const string& filename) {
    FILE* file = fopen(filename.c_str(), "w");
    for (auto iter = valid_assertion_ts.begin();
            iter != valid_assertion_ts.end(); ++iter) {
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
void paide::test_output_parallel_assign_stmt() {
    auto i_iter = assign_stmt_lhs.begin(), i_end = assign_stmt_lhs.end();
    auto e_iter = assign_stmt_rhs.begin(), e_end = assign_stmt_rhs.end();
    while (i_iter != i_end && e_iter != e_end) {
        const auto& iden = *i_iter;
        const auto& expr = *e_iter;
        cout << iden << ":=" << recov_expr_from_list(expr, true) << endl;
        i_iter++, e_iter++;
    }
}

/**
 * @brief to print thread state extracted from assertion
 */
void paide::test_print_valid_assertion_ts() {
    for (auto iter = valid_assertion_ts.begin();
            iter != valid_assertion_ts.end(); iter++) {
        const auto& pc = iter->first;
        const auto& tss = iter->second;
        for (auto l_iter = tss.begin(), l_end = tss.end(); l_iter != l_end;
                l_iter++) {
            const auto& assign = *l_iter;
            cout << pc << ":" << assign << endl;
        }
    }
}

/**
 * @brief look up the index of iden in the map of variables
 * @param iden
 * @return index if find var
 *         throw an exception otherwise
 */
pair<bool, ushort> paide::look_up_var_index(const string& var) {
    map<string, ushort>::iterator ifind;
    if ((ifind = s_vars_list.find(var)) != s_vars_list.end()) {
        return std::make_pair(true, ifind->second - 1);
    } else if ((ifind = l_vars_list.find(var)) != l_vars_list.end()) {
        return std::make_pair(false, ifind->second - 1);
    }
    throw iotf_runtime_error(var + "variable is undefined");
}

/**
 * @brief to output the name of successor's variable
 * @param var
 * @return string var + SUCC_POSTFIX
 */
string paide::create_succ_vars(const string& var) {
    return this->SUCC_POSTFIX + var;
}

/**
 * @brief convert the vector<ushort> to a shared/local state
 * @param sv
 */
string paide::create_vars_value_as_str(const vector<ushort>& sv) {
    string target;
    for (auto iv = sv.begin(); iv != sv.end(); ++iv) {
        const auto& val = *iv;
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

///////////////////////////////////////////////////////////////////////////////
/// from here: the auxiliary functions for forward based parser
///
///////////////////////////////////////////////////////////////////////////////

///////////////////////////////////////////////////////////////////////////////
/// from here: the auxiliary functions for backward based parser
///
///////////////////////////////////////////////////////////////////////////////

/**
 * @brief to add the shared variables to a map
 * @param var
 * @param index
 * @return
 */
bool bw_aide::add_to_l_vars_list(const string& var, const ushort& index) {
    auto p = l_vars_list.emplace(var, index);
    return p.second;
}

/**
 * @brief output the wp in the Dimacs format
 * @param file
 */
void bw_aide::output_control_flow_graph_dimacs(FILE *file) {
    size_pc index = s_vars_list.size() + l_vars_list.size();
    string inv = create_invariant_clause_in_wp();
    replace_vars_with_index(inv, index);
    fprintf(file, "%s = %s\n", INVARIANT.c_str(), inv.c_str());

//    for (auto ie = control_flow_graph.begin(); ie != control_flow_graph.end();
//            ++ie) {
//        auto edge = *ie;
//        replace_vars_with_index(edge, index);
//        fprintf(file, "%s\n", edge.c_str());
//    }
}

/**
 * @brief replace variables with Dimacs index
 * @param src
 * @param index
 */
void bw_aide::replace_vars_with_index(string& src, const ushort& index) {
    replaceAll(src, "--", "");
    for (auto is = s_vars_list.begin(); is != s_vars_list.end(); ++is) {
        replaceAll(src, create_succ_vars(is->first),
                std::to_string(is->second + l_vars_list.size() + index));
        replaceAll(src, is->first, std::to_string(is->second));
    }
    for (auto il = l_vars_list.begin(); il != l_vars_list.end(); il++) {
        replaceAll(src, create_succ_vars(il->first),
                std::to_string(il->second + index));
        replaceAll(src, il->first,
                std::to_string(il->second + s_vars_list.size()));
    }
}

/**
 *@brief replace all appearances of src in str with subst
 * @param str
 * @param src
 * @param subst
 */
void bw_aide::replaceAll(string& str, const string& src, const string& subst) {
    if (src.empty())
        return;
    size_t start_pos = 0;
    while ((start_pos = str.find(src, start_pos)) != string::npos) {
        str.replace(start_pos, src.length(), subst);
        start_pos += subst.length(); /// in case 'to' contains 'from', like replacing 'x' with 'yx'
    }
}

///////////// build Weakest Precondition Formula of Statements ////////////
///
/**
 * @brief to create the part of wp formula, which contains the non-assignment variables
 *           call by create_assign_stmt_wp()
 * @return string the wp formula
 */
string bw_aide::create_unassign_clause_in_wp() {
    string formula;
    for (auto il = l_vars_list.begin(); il != l_vars_list.end(); il++) {
        auto ifind = std::find(assign_stmt_lhs.begin(), assign_stmt_lhs.end(),
                il->first);
        if (ifind == assign_stmt_lhs.end()) {
            formula.append(il->first).append(" ").append("-").append(
                    create_succ_vars(il->first)).append(_AND_);
            formula.append("-").append(il->first).append(" ").append(
                    create_succ_vars(il->first)).append(_AND_);
        }
    }
    formula = formula.substr(0, formula.length() - _AND_.size());
    return formula;
}

/**
 * @brief to create invariant wp formula:
 *          call by goto, skip, assert, and assume statements
 * @return string: the wp formula
 */
string bw_aide::create_invariant_clause_in_wp() {
    string formula;
    for (auto il = l_vars_list.begin(); il != l_vars_list.end(); il++) {
        formula.append(il->first).append(" ").append("-").append(
                create_succ_vars(il->first)).append(_AND_);
        formula.append("-").append(il->first).append(" ").append(
                create_succ_vars(il->first)).append(_AND_);
    }
    formula = formula.substr(0, formula.length() - _AND_.size());
    return formula;
}

/**
 * @brief to output the name of successor's variable
 * @param var
 * @return string var + SUCC_POSTFIX
 */
string bw_aide::create_succ_vars(const string& var) {
    return SUCC_POSTFIX + var;
}

string bw_aide::convert_formula_to_cnf(const deque<string>& symb_list,
        const bool& is_assign) {
    string wp_in_cnf;

    map<string, ushort> expr_vars; // boolean variables in the formula
    ushort expr_vars_num = 0; // the number of boolean variables in the formula
    for (auto is = symb_list.begin(); is != symb_list.end(); is++) {
        const auto& s = *is;
        // using regular expression here would be a better choice
        if (!(s.compare(refs::AND) == 0 || s.compare(refs::OR) == 0
                || s.compare(refs::NEQ) == 0 || s.compare(refs::EQ) == 0
                || s.compare(refs::XOR) == 0
                || s.compare(refs::PAREN_L + refs::PAREN_R) == 0
                || s.compare(refs::NEG) == 0 || s.compare(refs::CONST_F) == 0
                || s.compare(refs::CONST_T) == 0
                || s.compare(refs::CONST_N) == 0)) {
            expr_vars.emplace(s, expr_vars_num);
            ++expr_vars_num;
        }
    }

    if (expr_vars_num == 0)
        return recov_expr_from_list(symb_list, true);

    vector<ushort> var_indices(expr_vars.size());
    for (ushort i = 0; i < std::pow(2, expr_vars_num); i++) {
        auto assert_vars_assignments = decimal2binary(i, expr_vars_num);
        stack<bool> comp_result_stack;
        for (auto is = symb_list.begin(); is != symb_list.end(); ++is) {
            const auto& s = *is;
            bool operand1, operand2;
            if (s.compare(refs::AND) == 0) { // and
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 && operand1);
            } else if (s.compare(refs::OR) == 0) { // or
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 || operand1);
            } else if (s.compare(refs::EQ) == 0) { // equal
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 == operand1);
            } else if (s.compare(refs::NEQ) == 0) { // not equal
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 != operand1);
            } else if (s.compare(refs::OR) == 0) { // exclusive or
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                operand2 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand2 ^ operand1);
            } else if (s.compare(refs::PAREN_L + refs::PAREN_R) == 0) { // bracket
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(operand1);
            } else if (s.compare(refs::NEG) == 0) { // negation
                operand1 = comp_result_stack.top();
                comp_result_stack.pop();
                comp_result_stack.push(!operand1);
            } else { // variables
                map<string, ushort>::iterator ifind;
                if ((ifind = expr_vars.find(s)) != expr_vars.end()) {
                    ushort i = ifind->second;
                    bool b_value = assert_vars_assignments[i];
                    if (is_assign) {
                        if ((ifind = s_vars_list.find(s)) != s_vars_list.end())
                            var_indices[i] = ifind->second;
                        else if ((ifind = l_vars_list.find(s))
                                != l_vars_list.end())
                            var_indices[i] = ifind->second + s_vars_list.size();
                    } else {
                        if ((ifind = s_vars_list.find(s)) != s_vars_list.end())
                            var_indices[i] = ifind->second + s_vars_list.size()
                                    + 2 * l_vars_list.size();
                        else if ((ifind = l_vars_list.find(s))
                                != l_vars_list.end())
                            var_indices[i] = ifind->second + s_vars_list.size()
                                    + l_vars_list.size();
                    }
                    comp_result_stack.push(b_value);
                }
            }
        }

        if (!comp_result_stack.top()) {
            ushort i = 0;
            wp_in_cnf.append("& ");
            for (auto ib = assert_vars_assignments.begin(), end =
                    assert_vars_assignments.end(); ib != end; ib++, i++) {
                wp_in_cnf.append(
                        std::to_string(
                                (*ib ? -var_indices[i] : var_indices[i]))).append(
                        " ");
            }
        }
    }

    return wp_in_cnf.substr(2);
}

///////////////////// Some Testing Methods /////////////////////
void bw_aide::test_output_parallel_assign_stmt() {
    auto i_iter = assign_stmt_lhs.begin(), i_end = assign_stmt_lhs.end();
    auto e_iter = assign_stmt_rhs.begin(), e_end = assign_stmt_rhs.end();
    while (i_iter != i_end && e_iter != e_end) {
        const auto& iden = *i_iter;
        const auto& expr = *e_iter;
        cout << iden << ":=" << recov_expr_from_list(expr, true) << endl;
        i_iter++, e_iter++;
    }
}

/**
 * @brief to print thread state extracted from assertion
 */
void bw_aide::test_print_valid_assertion_ts() {
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
