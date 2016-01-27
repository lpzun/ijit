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

#ifndef BPP_AIDE_HH_
#define BPP_AIDE_HH_

#include <cstdio>
#include <cstdlib>
#include <cassert>
#include <cmath>

#include <algorithm>
#include <iostream>
#include <string>
#include <sstream>
#include <map>
#include <unordered_map>
#include <set>
#include <deque>
#include <vector>
#include <stack>
#include <memory>

#include "../api/cfg.hh"
#include "../util/excp.hh"

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
using std::pair;

namespace iotf {

/**
 * @brief this is auxiliary class for Boolean program parser
 *        paide: parser aide
 */
class paide {
public:
    paide() :
            lineno(0), ipc(0), s_vars_num(0), l_vars_num(0) {
    }

    virtual ~paide() {
    }

    const string SUCC_POSTFIX = "_";
    const string _AND_ = " & ";

    size_pc lineno; /// initialize the lineno
    size_pc ipc; /// the source of cfg edge
    ushort s_vars_num; /// the number of shared variables
    ushort l_vars_num; /// the number of local variables

    set<size_pc> pc_set;

    map<string, ushort> s_vars_list; /// store shared variables and indices
    map<string, ushort> l_vars_list; /// store local  variables and indices
    map<ushort, sool> s_vars_init; /// to record the initial shared state
    map<ushort, sool> l_vars_init; /// to record the initial local state

    cfg cfg_G;

    set<size_pc> succ_pc_set; /// store the succeeding pcs

    deque<symbol> expr_in_list; /// the expression symbol list

    /// to store parallel assignment statements
    deque<string> assign_stmt_lhs; /// the right-hand side of parallel assignment
    deque<deque<string>> assign_stmt_rhs; /// the left-hand side of of parallel assignment

    map<size_pc, deque<string>> valid_assertion_ts;

    /////////////////////////////// function list /////////////////////////////

    /// control flow graph function list
    bool is_pc_unique(const size_pc& pc);

    void add_edge(const size_pc& src, const type_stmt& type);

    void add_edge(const size_pc& src, const size_pc& dest,
            const type_stmt& type, const bool& is_condition = false);

    void output_control_flow_graph();

    /// initial states
    ///
    void add_vars(const string& var, const sool& val, const bool& is_shared);
    void init_vars(const string& var, const sool& val);
    string create_init_state(const map<ushort, sool>& minit);

    /// extract final state from assertion
    void output_final_state_to_file(const string& filename);
    void all_sat_solver(const deque<string>& symb_list, const ushort& pc);

    /// expression
    void add_to_expr_in_list(const string& symbol);
    string recov_expr_from_list(const deque<string>& symb_list,
            const bool& is_origi = false);
    string output_expr_as_str(const deque<string>& symb_list);

    /// unit test
    void test_print_valid_assertion_ts();
    void test_output_parallel_assign_stmt();

protected:
    pair<bool, ushort> look_up_var_index(const string& var);
    string create_succ_vars(const string& var);
    vector<bool> decimal2binary(const int& n, const int& size);
    string create_vars_value_as_str(const vector<ushort>& sv);

    assignment create_assignment();

private:

}
;

/**
 * @brief this is auxiliary class for forward based parser
 */
class fw_aide: public paide {
public:
    fw_aide() :
            paide() {

    }

    virtual ~fw_aide() {

    }

private:

};

/**
 * @brief this is auxiliary class for backward based parser
 */
class bw_aide: public paide {
public:
    bw_aide() :
            paide(), is_dimacs(false) {
    }
    ~bw_aide() {
    }

    const string INVARIANT = "inv";

    bool is_dimacs;

    ushort cand_count = 0;

    void output_control_flow_graph_dimacs(FILE *file);

    bool add_to_l_vars_list(const string& var, const ushort& index);
    void add_to_expr_symb_list(const string& symbol);

    /// create weakest precondition formula of statements

    /// unit test
    void test_print_valid_assertion_ts();
    void test_output_parallel_assign_stmt();

private:
    string create_unassign_clause_in_wp();
    string create_invariant_clause_in_wp();
    string create_succ_vars(const string& var);

    void replace_vars_with_index(string& src, const ushort& index);
    void replaceAll(string& str, const string& from, const string& to);
};

} /* namespace iotf */

#endif /* BPP_AIDE_HH_ */
