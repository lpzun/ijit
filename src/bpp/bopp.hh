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

#include <algorithm>
#include <iostream>
#include <string>
#include <sstream>
#include <map>
#include <set>
#include <list>
#include <vector>
#include <stack>

using std::string;
using std::cout;
using std::endl;
using std::cin;
using std::cerr;

using std::set;
using std::map;
using std::list;
using std::vector;
using std::stack;

typedef unsigned short ushort;

namespace iotf {

/**
 * @brief this is the aide for forward based parser
 */
class fw_aide {
    fw_aide() {
    }
    ~fw_aide() {
    }

    const static string SUCC_POSTFIX;

    const static string KLEENE_STAR;
    const static string ZERO;
    const static string ONE;
    const static string _AND_;
    const static string NEGATION;
    const static string RIGHT_PAREN;
    const static string LEFT_PAREN;

    const static string NON_CAND_MARK; /// non-candidate-pc statement
    const static string NEW_THRD_MARK; /// thread creation mark
    const static string WAIT_STMT_MARK; /// wait statement mark
    const static string BCST_STMT_MARK; /// broadcast statement mark
    const static string ATOM_STMT_MARK; /// atomic section mark
    const static string END_THRD_MARK; /// thread termination statement mark
    const static string GOTO_STMT_MARK; /// goto statement mark
    const static string ASSGIN_STMT_MARK; /// assignment statement mark
    const static string ASSUM_STMT_MARK; /// assume statement mark

    static ushort line; // initialize the lineno: a stupid way to do this
    static ushort ipc; // the source of cfg edge
    static ushort s_vars_num; // the number of shared variables
    static ushort l_vars_num; // the number of local variables

    static set<ushort> pc_set;
    static map<string, ushort> s_vars_list;
    static map<string, ushort> l_vars_list;
    static list<string> control_flow_graph; // control flow graph
    static map<ushort, char> s_var_init; // to record the initial shared state
    static map<ushort, char> l_var_init; // to record the initial local state
    static string goto_targets; // to output the comments

    static list<string> expr_symb_list;
    static list<string> assign_stmt_lhs;
    static list<list<string> > assign_stmt_rhs;
    static list<string> assign_identifiers;

    map<ushort, list<string> > valid_assertion_ts;

    /// control flow graph function list
    bool is_pc_unique(const ushort& pc);
    void create_control_flow_graph(const ushort& from, const string& sp);
    void output_control_flow_graph(FILE *file);

    string create_init_state(const map<ushort, char>& minit);
    bool add_to_shared_vars_list(const string& var, const ushort& index);
    bool add_to_local_vars_list(const string& var, const ushort& index);
    void add_to_expr_symb_list(const string& symbol);

    /// create the weakest precondition formula of statements
    string create_goto_stmt_sp();
    string create_skip_stmt_sp();
    string create_assume_stmt_sp();
    string create_assert_stmt_sp();
    string create_assign_stmt_sp();
    void create_if_true_stmt_sp(const string& e);
    string create_if_false_stmt_sp(const string& e);
    string create_new_thr_stmt_sp(const string& pc);
    string create_wait_stmt_sp();
    string create_broadcast_stmt_sp();
    string create_atom_stmt_sp();

    string look_up_var_index(const string& var);
    string create_succ_vars(const string& var);

    /// extract thread state from assertion
    void exhaustive_sat_solver(const list<string>& symb_list, const ushort& pc);
    vector<bool> decimal2binary(const int& n, const int& size);
    ushort power(const ushort& base, const ushort& exp);
    string create_vars_value_as_str(const vector<ushort>& sv);
    void output_assertion_ts_to_file(const string& filename);
    string recov_expr_from_symb_list(const list<string>& symb_list,
            const bool& is_origi = false);
    string output_expr_as_str_from_symb_list(const list<string>& symb_list);

    /// unit test
    void test_print_valid_assertion_ts();
    void test_output_parallel_assign_stmt();
};

} /* namespace iotf */

#endif /* BPP_BOPP_HH_ */
