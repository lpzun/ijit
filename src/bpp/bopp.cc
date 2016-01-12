/**
 * @brief bopp.cc
 *
 * @date  : Jan 12, 2016
 * @author: lpzun
 */

#include "bopp.hh"

namespace iotf {
/**
 * @brief get a command
 * @param begin
 * @param end
 * @param option
 * @return a cmd
 */
char* getCmdOption(char ** begin, char ** end, const std::string & option) {
    char ** itr = std::find(begin, end, option);
    if (itr != end && ++itr != end) {
        return *itr;
    }
    return 0;
}

/**
 * @brief if a specific cmd exists or not
 * @param begin
 * @param end
 * @param option
 * @return true if exists
 *         false otherwise
 */
bool cmdOptionExists(char** begin, char** end, const std::string& option) {
    return std::find(begin, end, option) != end;
}

/*
 int main(int argc, char *argv[]) {
 if (cmdOptionExists(argv, argv + argc, "-h")) {
 printf("Usage: BoPP [-cfg file] [-taf file]\n");
 }

 char* cfg_file_name = getCmdOption(argv, argv + argc, "-cfg");
 if (cfg_file_name == 0) {
 cfg_file_name = comm::DEFAULT_CFG_FILE_NAME;
 }

 char* taf_file_name = getCmdOption(argv, argv + argc, "-taf");
 if (taf_file_name == 0) {
 taf_file_name = comm::DEFAULT_TAF_FILE_NAME;
 }

 char DEFAULT_CFG_FILE_NAME[100] = "bp.cfg";
 char DEFAULT_TAF_FILE_NAME[100] = "bp.taf";
 /// file list
 FILE *cfg_file = fopen(cfg_file_name, "w");

 //move the file point to the begin and print the total line number
 fprintf(cfg_file, "# control flow graph and other information\n");
 fprintf(cfg_file, "shared %d\n", comm::s_vars_num);
 fprintf(cfg_file, "local %d\n", comm::l_vars_num);

 //note the initial pc!!!!!!!!
 fprintf(cfg_file, "init %s|0,%s # initial thread state\n",
 (create_init_state(comm::s_var_init)).c_str(),
 (create_init_state(comm::l_var_init)).c_str());
 fprintf(cfg_file, "%d%s %d\n", comm::line,
 " # the number of lines in BP with cand PC = ", comm::cand_count);
 cout << comm::cand_count << ":" << comm::line << endl;

 output_control_flow_graph(cfg_file);
 fclose(cfg_file);

 //test_print_valid_assertion_ts(); // testing
 output_assertion_ts_to_file(taf_file_name);

 return 0;
 }*/

const string fw_aide::SUCC_POSTFIX = "_";

const string fw_aide::KLEENE_STAR = "*";
const string fw_aide::ZERO = "0";
const string fw_aide::ONE = "1";
const string fw_aide::_AND_ = " & ";
const string fw_aide::NEGATION = "!";
const string fw_aide::RIGHT_PAREN = "(";
const string fw_aide::LEFT_PAREN = ")";

const string fw_aide::NON_CAND_MARK = "-1"; /// non-candidate-pc statement
const string fw_aide::NEW_THRD_MARK = "-2"; /// thread creation mark
const string fw_aide::WAIT_STMT_MARK = "-3"; /// wait statement mark
const string fw_aide::BCST_STMT_MARK = "-4"; /// broadcast statement mark
const string fw_aide::ATOM_STMT_MARK = "-5"; /// atomic section mark
const string fw_aide::END_THRD_MARK = "-6"; /// thread termination statement mark
const string fw_aide::GOTO_STMT_MARK = "-7"; /// goto statement mark
const string fw_aide::ASSGIN_STMT_MARK = "-8"; /// assignment statement mark
const string fw_aide::ASSUM_STMT_MARK = "-9"; /// assume statement mark

ushort fw_aide::line = 0; /// initialize the lineno: a stupid way to do this
ushort fw_aide::ipc = 0; /// the source of cfg edge
ushort fw_aide::s_vars_num = 0; /// the number of shared variables
ushort fw_aide::l_vars_num = 0; /// the number of local variables

set<ushort> fw_aide::pc_set;
map<string, ushort> fw_aide::s_vars_list;
map<string, ushort> fw_aide::l_vars_list;
list<string> fw_aide::control_flow_graph; /// control flow graph
map<ushort, char> fw_aide::s_var_init; /// to record the initial shared state
map<ushort, char> fw_aide::l_var_init; /// to record the initial local state
string fw_aide::goto_targets; /// to output the comments

list<string> fw_aide::expr_symb_list;
list<string> fw_aide::assign_stmt_lhs;
list<list<string> > fw_aide::assign_stmt_rhs;
list<string> fw_aide::assign_identifiers;

/**
 * @brief extract initial states from Boolean programs
 * @param minit
 * @return
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
    auto p = fw_aide::s_vars_list.insert(std::pair<string, ushort>(var, index));
    return p.second;
}

/**
 * @brief to add the shared variables to a map
 * @param var
 * @param index
 * @return
 */
bool fw_aide::add_to_local_vars_list(const string& var, const ushort& index) {
    auto p = fw_aide::l_vars_list.insert(std::pair<string, ushort>(var, index));
    return p.second;
}

/**
 * @brief to add the expression symbols to a list
 * @param symbol
 */
void fw_aide::add_to_expr_symb_list(const string& symbol) {
    fw_aide::expr_symb_list.push_back(symbol);
}

/***************************** Control Flow Graph *****************************/
/**
 * @brief to determine if the pc is unique or not
 * @param pc
 */
bool fw_aide::is_pc_unique(const ushort& pc) {
    auto result = fw_aide::pc_set.insert(pc);
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
    fw_aide::control_flow_graph.push_back(edge);
}

/**
 * @brief output the control flow graph to the file
 * @param file
 */
void fw_aide::output_control_flow_graph(FILE *file) {
    for (auto iter = fw_aide::control_flow_graph.begin(), end =
            fw_aide::control_flow_graph.end(); iter != end; iter++) {
        fprintf(file, "%s\n", (*iter).c_str());
    }
}

/**
 * @brief goto statement
 * @return
 */
string fw_aide::create_goto_stmt_sp() {
    return fw_aide::GOTO_STMT_MARK + " " + fw_aide::goto_targets.substr(1);
}

/**
 * @brief skip statement
 * @return
 */
string fw_aide::create_skip_stmt_sp() {
    return fw_aide::NON_CAND_MARK;
}

/**
 * @brief assume statement
 * @return
 */
string fw_aide::create_assume_stmt_sp() {
    auto expr = recov_expr_from_symb_list(fw_aide::expr_symb_list);
    return fw_aide::ASSUM_STMT_MARK + " " + expr;
}

/**
 * @brief assert statement, same as the skip statement
 * @return
 */
string fw_aide::create_assert_stmt_sp() {
    return fw_aide::NON_CAND_MARK;
}

/**
 * @brief assignment statement
 *    _x = x, where _x is the successor
 * @return string
 */
string fw_aide::create_assign_stmt_sp() {
    auto ii = fw_aide::assign_stmt_lhs.begin(), iend =
            fw_aide::assign_stmt_lhs.end();
    auto ie = fw_aide::assign_stmt_rhs.begin(), eend =
            fw_aide::assign_stmt_rhs.end();
    string formula;
    while (ii != iend && ie != eend) {
        const auto& iden = *ii;
        auto expr = output_expr_as_str_from_symb_list(*ie);
        formula.append(";").append(look_up_var_index(iden)).append(",").append(
                expr);
        ii++, ie++;
    }
    return fw_aide::ASSGIN_STMT_MARK + " " + formula.substr(1);
}

/**
 * @brief if (expr == true) then statement
 * @param e
 */
void fw_aide::create_if_true_stmt_sp(const string& e) {
    const auto& edge = fw_aide::control_flow_graph.back();
    fw_aide::control_flow_graph.pop_back();
    if (e.find_first_of('*') != std::string::npos)
        fw_aide::control_flow_graph.push_back(edge);
    else
        fw_aide::control_flow_graph.push_back(edge + fw_aide::_AND_ + e);
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
    return fw_aide::NEW_THRD_MARK + " " + pc;
}

/**
 * @brief wait
 * @return string
 */
string fw_aide::create_wait_stmt_sp() {
    return fw_aide::WAIT_STMT_MARK;
}

/**
 * @brief broadcast
 * @return string
 */
string fw_aide::create_broadcast_stmt_sp() {
    return fw_aide::BCST_STMT_MARK;
}

/**
 * @brief atomic statement: begin and end
 * @return string
 */
string fw_aide::create_atom_stmt_sp() {
    return fw_aide::ATOM_STMT_MARK;
}

/**
 * @brief look up the index of iden in the map of variables
 * @param iden
 * @return index if find var
 *     -1 otherwise
 */
string fw_aide::look_up_var_index(const string& var) {
    map<string, ushort>::iterator ifind;
    if ((ifind = fw_aide::s_vars_list.find(var))
            != fw_aide::s_vars_list.end()) {
        return std::to_string(ifind->second);
    } else if ((ifind = fw_aide::l_vars_list.find(var))
            != fw_aide::l_vars_list.end()) {
        return std::to_string(ifind->second + fw_aide::l_vars_list.size());
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
        const list<string>& symb_list) {
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
string fw_aide::recov_expr_from_symb_list(const list<string>& symb_list,
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
void fw_aide::exhaustive_sat_solver(const list<string>& symb_list,
        const ushort& pc) {
    list<string> s_target_list;
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
                vector<ushort> t_shared(fw_aide::s_vars_list.size(), 2);
                vector<ushort> t_locals(fw_aide::l_vars_list.size(), 2);
                string ss;
                if (create_vars_value_as_str(t_shared).size() > 1)
                    ss.append(create_vars_value_as_str(t_shared).substr(1));
                ss.append("|").append(std::to_string(pc)).append(
                        create_vars_value_as_str(t_locals));
                s_target_list.push_back(ss);
                fw_aide::valid_assertion_ts.insert(
                        std::pair<ushort, list<string> >(pc, s_target_list));
                return;
            } else {
                assert_vars.insert(
                        std::pair<string, ushort>(symbol, assert_vars_num));
                assert_vars_num++;
            }
        }
    }

    for (ushort i = 0; i < power(2, assert_vars_num); i++) {
        vector<bool> assert_vars_assignments = decimal2binary(i,
                assert_vars_num);
        vector<ushort> t_shared(fw_aide::s_vars_list.size(), 2);
        vector<ushort> t_locals(fw_aide::l_vars_list.size(), 2);

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
                    if ((ifind = fw_aide::s_vars_list.find(symbol))
                            != fw_aide::s_vars_list.end())
                        t_shared[ifind->second - 1] = b_value;
                    else if ((ifind = fw_aide::l_vars_list.find(symbol))
                            != fw_aide::l_vars_list.end())
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
    for (auto iter = fw_aide::valid_assertion_ts.begin(), end =
            fw_aide::valid_assertion_ts.end(); iter != end; iter++) {
        const ushort& pc = iter->first;
        const list<string>& tss = iter->second;
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
    auto i_iter = fw_aide::assign_stmt_lhs.begin(), i_end =
            fw_aide::assign_stmt_lhs.end();
    auto e_iter = fw_aide::assign_stmt_rhs.begin(), e_end =
            fw_aide::assign_stmt_rhs.end();
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
    for (auto iter = fw_aide::valid_assertion_ts.begin(), end =
            fw_aide::valid_assertion_ts.end(); iter != end; iter++) {
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
