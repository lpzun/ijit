/*************************************************************************************
 ** Name:       BoPP: parser
 ** Authors:    Peizun Liu
 ** Version:    0.5
 ** Copyright:  It belongs to Thomas Wahl's group in CAR Lab, CCIS, NEU
 ** Create on:  Feb, 2014
 ** Modified :  Jan, 2016
 ** Decription: BoPP is a Boolean Program Parser written with C++. It aims at parsing
 *              Boolean programs to generate a control folow graph and the correspon-
 *              ding weakest preconditions (strongest postconditions) for each state-
 *              ment when computing a preimage (postimage).
 *
 *              parser:
 *              v0.5: adding the forward-based CFG and so on
 ************************************************************************************/

#ifndef BPP_BOPP_HH_
#define BPP_BOPP_HH_

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cmath>

#include <algorithm>
#include <iostream>
#include <string>
#include <sstream>
#include <map>
#include <set>
#include <deque>
#include <vector>
#include <stack>

using std::string;
using std::cout;
using std::endl;
using std::cin;
using std::cerr;

using std::set;
using std::map;
using std::deque;
using std::vector;
using std::stack;

typedef unsigned short ushort;

namespace iotf {

/**
 * @brief this is auxiliary class for forward based parser
 */
class fw_aide {
public:
    fw_aide() :
            lineno(0), ipc(0), s_vars_num(0), l_vars_num(0) {
    }

    ~fw_aide() {
    }

    const string SUCC_POSTFIX = "_";
    const string KLEENE_STAR = "*";
    const string ZERO = "0";
    const string ONE = "1";
    const string _AND_ = " & ";
    const string NEGATION = "!";
    const string R_PAREN = "(";
    const string L_PAREN = ")";

    const string STMT_SKIP = "-1"; /// all other statement mark
    const string STMT_GOTO = "-2"; /// goto statement mark
    const string STMT_ASSG = "-3"; /// assignment statement mark
    const string STMT_IFEL = "-4"; /// if (<expr>) then <sseq> else <sseq>; fi;
    const string STMT_ASSE = "-5"; /// assertion statement mark
    const string STMT_ASSU = "-6"; /// assume statement mark
    const string STMT_NTHR = "-7"; /// thread creation statement mark
    const string STMT_ETHR = "-8"; /// thread termination statement mark
    const string STMT_ATOM = "-9"; /// atomic beginning statement mark
    const string STMT_EATM = "-10"; /// atomic section ending statement mark
    const string STMT_BCST = "-11"; /// broadcast statement mark
    const string STMT_WAIT = "-12"; /// wait statement mark
    const string STMT_SIGN = "-13"; /// signal statement mark

    ushort lineno; /// initialize the lineno: a stupid way to do this
    ushort ipc; /// the source of cfg edge
    ushort s_vars_num; /// the number of shared variables
    ushort l_vars_num; /// the number of local variables

    set<ushort> pc_set;
    map<string, ushort> s_vars_list; /// store shared variables and indices
    map<string, ushort> l_vars_list; /// store local  variables and indices
    deque<string> control_flow_graph; /// control flow graph
    map<ushort, char> s_var_init; /// to record the initial shared state
    map<ushort, char> l_var_init; /// to record the initial local state

    deque<string> expr_symb_list; /// the expression symbol list

    /// to store parallel assignment statements
    deque<string> assign_stmt_lhs; /// the right-hand side of parallel assignment
    deque<deque<string>> assign_stmt_rhs; /// the left-hand side of of parallel assignment

    deque<string> assign_identifiers;

    map<ushort, deque<string> > valid_assertion_ts;

    /////////////////////////////// function list /////////////////////////////
    bool add_to_shared_vars_list(const string& var, const ushort& index);
    bool add_to_local_vars_list(const string& var, const ushort& index);

    /// control flow graph function list
    bool is_pc_unique(const ushort& pc);
    void add_edge(const ushort& from, const ushort& to, const string& sp);
    void output_control_flow_graph(FILE *file);

    string create_init_state(const map<ushort, char>& minit);
    void add_to_expr_symb_list(const string& symbol);

    /// create the weakest precondition formula of statements
    string create_skip_stmt_sp();
    string create_goto_stmt_sp();
    string create_assg_stmt_sp();
    void create_ifth_stmt_sp(const string& e);
    string create_else_stmt_sp(const string& e);
    string create_asse_stmt_sp();
    string create_assu_stmt_sp();
    string create_nthr_stmt_sp(const string& pc);
    string create_atom_stmt_sp();
    string create_eatm_stmt_sp();
    string create_bcst_stmt_sp();
    string create_wait_stmt_sp();

    /// extract thread state from assertion
    void exhaustive_sat_solver(const deque<string>& symb_list,
            const ushort& pc);
    string create_vars_value_as_str(const vector<ushort>& sv);
    void output_assertion_ts_to_file(const string& filename);
    string recov_expr_from_symb_list(const deque<string>& symb_list,
            const bool& is_origi = false);
    string output_expr_as_str_from_symb_list(const deque<string>& symb_list);

    /// unit test
    void test_print_valid_assertion_ts();
    void test_output_parallel_assign_stmt();

private:
    string look_up_var_index(const string& var);
    string create_succ_vars(const string& var);
    vector<bool> decimal2binary(const int& n, const int& size);
};

class bw_aide {
public:
    bw_aide() :
            lineno(0), ipc(0), s_vars_num(0), l_vars_num(0), is_dimacs(false) {
    }
    ~bw_aide() {
    }

    const string SUCC_POSTFIX = "_";
    const string KLEENE_STAR = "*";
    const string ZERO = "0";
    const string ONE = "1";
    const string _AND_ = " & ";
    const string NEGATION = "!";
    const string R_PAREN = "(";
    const string L_PAREN = ")";

    const string STMT_SKIP = "-1"; /// all other statement mark
    const string STMT_GOTO = "-2"; /// goto statement mark
    const string STMT_ASSG = "-3"; /// assignment statement mark
    const string STMT_IFEL = "-4"; /// if (<expr>) then <sseq> else <sseq>; fi;
    const string STMT_ASSE = "-5"; /// assertion statement mark
    const string STMT_ASSU = "-6"; /// assume statement mark
    const string STMT_NTHR = "-7"; /// thread creation statement mark
    const string STMT_ETHR = "-8"; /// thread termination statement mark
    const string STMT_ATOM = "-9"; /// atomic beginning statement mark
    const string STMT_EATM = "-10"; /// atomic section ending statement mark
    const string STMT_BCST = "-11"; /// broadcast statement mark
    const string STMT_WAIT = "-12"; /// wait statement mark
    const string STMT_SIGN = "-13"; /// signal statement mark

    const string INVARIANT = "inv";

    ushort lineno; /// initialize the lineno: a stupid way to do this
    ushort ipc; /// the source of cfg edge
    ushort s_vars_num; /// the number of shared variables
    ushort l_vars_num; /// the number of local variables
    bool is_dimacs;

    set<ushort> pc_set;
    map<string, ushort> s_vars_list;
    map<string, ushort> l_vars_list;
    deque<string> control_flow_graph; /// control flow graph
    map<ushort, char> s_var_init; /// to record the initial shared state
    map<ushort, char> l_var_init; /// to record the initial local state
    string goto_targets; /// to output the comments
    set<ushort> succ_stmt_label;

    deque<string> expr_symb_list;
    deque<string> assign_stmt_lhs;
    deque<deque<string> > assign_stmt_rhs;
    deque<string> assign_identifiers;
    map<ushort, deque<string> > valid_assertion_ts;

    ushort cand_count = 0;

    /// control flow graph function list
    bool is_pc_unique(const ushort& pc);
    void add_edge(const ushort& from, const string& wp);
    void add_edge(const ushort& from, const ushort& to, const string& wp);
    void output_control_flow_graph(FILE *file);
    void output_control_flow_graph_dimacs(FILE *file);

    string create_init_state(const map<ushort, char>& minit);
    bool add_to_shared_vars_list(const string& var, const ushort& index);
    bool add_to_local_vars_list(const string& var, const ushort& index);
    void add_to_expr_symb_list(const string& symbol);

    /// create weakest precondition formula of statements
    string create_skip_stmt_wp();
    string create_goto_stmt_wp();
    string create_assg_stmt_wp();
    void create_ifth_stmt_wp(const string& e);
    string create_else_stmt_wp(const string& e);
    string create_asse_stmt_wp();
    string create_assu_stmt_wp();
    string create_nthr_stmt_wp(const string& pc);
    string create_atom_stmt_wp();
    string create_eatm_stmt_wp();
    string create_bcst_stmt_wp();
    string create_wait_stmt_wp();

    /// extract thread state from assertion
    string create_vars_value_as_str(const vector<ushort>& sv);
    void output_assertion_ts_to_file(const string& filename);
    string convert_formula_to_cnf(const deque<string>& symb_list,
            const bool& is_assign);
    string recov_expr_from_symb_list(const deque<string>& symb_list,
            const bool& is_origi = false);
    void exhaustive_sat_solver(const deque<string>& symb_list,
            const ushort& pc);

    /// unit test
    void test_print_valid_assertion_ts();
    void test_output_parallel_assign_stmt();

private:
    string create_unassign_clause_in_wp();
    string create_invariant_clause_in_wp();
    string create_succ_vars(const string& var);

    void replace_vars_with_index(string& src, const ushort& index);
    void replaceAll(std::string& str, const std::string& from,
            const std::string& to);
    vector<bool> decimal2binary(const int& n, const int& size);
};

} /* namespace iotf */

#endif /* BPP_BOPP_HH_ */
