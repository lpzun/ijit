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
            is_failed(false), lineno(0), ipc(0), s_vars_num(0), l_vars_num(0) {
    }

    ~paide() {
    }

    const string SUCC_POSTFIX = "_";
    const string _AND_ = " & ";

    bool is_failed;
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

    /// expression
    void add_to_expr_in_list(const string& symbol);
    string recov_expr_from_list(const deque<string>& symb_list,
            const bool& is_origi = false);
    void all_sat_solver(const deque<string>& symb_list, const ushort& pc);

    /// unit test
    void test_print_valid_assertion_ts();
    void test_output_parallel_assign_stmt();
    void is_failed_assertion();

protected:
    pair<bool, ushort> look_up_var_index(const string& var);
    string create_succ_vars(const string& var);
    vector<bool> decimal2binary(const int& n, const int& size);
    string create_vars_value_as_str(const vector<ushort>& sv);

    assignment create_assignment();
private:
    map<size_pc, deque<string>> valid_assertion_ts;
}
;

} /* namespace otf */
#endif /* BPP_AIDE_HH_ */
