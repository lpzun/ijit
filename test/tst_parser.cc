/**
 * @brief tst_parser.cc
 *
 * @date  : Feb 4, 2016
 * @author: lpzun
 */

#include "../test/tst_parser.hh"

namespace iotf {

tst_parser::tst_parser() {

}

tst_parser::~tst_parser() {

}

/**
 * @brief test parser and image computation
 * @param filename
 */
void tst_parser::test_parser(const string& filename) {
    auto P = parser::parse(filename, mode::POST);
    uint sss = 3;
    converter c;
    auto sv = c.convert_sss_to_sps(sss);
    shared_state s(sv);
    cout << "shared bitset: " << sv << "\n";
    cout << "shared state: " << s << "\n";

    state_v lv(1);
    cout << "local bitset: " << lv << "\n";
    uint pc;
    cin >> pc;
//	auto sls = c.convert_lps_to_lss(pc, lv);
//	cout << sls << "\n";
//    cout  <<"local state: "<< sls << "\n";
    local_state l(pc, lv);
    cout << "local state: " << l << "\n";

    ca_locals locals;
    locals.emplace(l, 2);

    prog_state tau(s, locals);
    cout << tau << "\n";
    post_image image;
    auto _tau = image.step(tau);
    for (const auto& g : _tau)
        cout << g << endl;
}

void tst_solver::test_split() {
    DBG_LOC()
    deque<symbol> se1;
    se1.emplace_back(solver::CONST_N);
    se1.emplace_back(solver::NEG);
    se1.emplace_back(solver::PAR);
    se1.emplace_back(solver::CONST_N);
    for (const auto& s : se1) {
        cout << s << " ";
    }
    cout << "\n";
    auto ret = solver::split(se1);
    cout << "size: " << ret.size() << endl;
    for (const auto& l : ret) {
        for (const auto& s : l)
            cout << s << " ";
        cout << "\n";
    }

    cout << "\n";
}

/**
 * @brief testing
 */
void tst_solver::test_all_sat_solve() {
    refs::S_VARS_NUM = 2;
    refs::L_VARS_NUM = 2;
/// se1: 0
    cout << "expression se1...\n";
    deque<symbol> se1;
    se1.emplace_back(0);
    auto ret1 = solver::all_sat_solve(se1);
    tst_solver::print(ret1);
    cout << "\n";

/// se2: 1
    cout << "expression se2...\n";
    deque<symbol> se2;
    se2.emplace_back(1);
    auto ret2 = solver::all_sat_solve(se2);
    print(ret2);
    cout << "\n";

/// se3: !0
    deque<symbol> se3;
    cout << "expression se3...\n";
    se3.emplace_back(0);
    se3.emplace_back(solver::PAR);
    se3.emplace_back(solver::NEG);
    auto ret3 = solver::all_sat_solve(se3);
    print(ret3);
    cout << "\n";

/// se2: 1
    cout << "expression se4...\n";
    deque<symbol> se4;
    se4.emplace_back(1);
    se4.emplace_back(solver::PAR);
    se4.emplace_back(solver::NEG);
    auto ret4 = solver::all_sat_solve(se4);
    print(ret4);
    cout << "\n";

/// se5: *
    cout << "expression se5...\n";
    deque<symbol> se5;
    se5.emplace_back(solver::CONST_N);
    auto splited = solver::split(se5);
    deque<pair<ss_vars, sl_vars>> ret5;
    for (const auto& ex : splited) {
        auto tmp = solver::all_sat_solve(ex);
        ret5.insert(ret5.end(), tmp.begin(), tmp.end());
    }
    print(ret5);
    cout << "\n";
}

/**
 * @brief print
 * @param assgs
 */
void tst_solver::print(const deque<pair<ss_vars, sl_vars>>& assgs) {
    for (const auto& p : assgs) {
        for (const auto & s : p.first)
            cout << s << ",";
        cout << "|";
        for (const auto & l : p.second)
            cout << "," << l;
        cout << "\n";
    }
}
} /* namespace iotf */
