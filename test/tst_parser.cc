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
 * @brief test parser
 * @param filename
 */
void tst_parser::test_parser(const string& filename) {
    auto P = parser::parse(filename, mode::POST);
    cout << "I'm here.......1....\n";
    converter c;
    cout << __func__ << " initial states: " << "\n";
    for (const auto& its : P.first) {
        cout << its << "\n";
        // cout << c.convert(its) << "\n";
    }

    cout << __func__ << " final states: " << "\n";
    for (const auto& ifs : P.second) {
        cout << ifs << "\n";
        // cout << c.convert(ifs) << "\n";
    }
}

/**
 * @brief test image computation
 * @param filename
 */
void tst_parser::test_post_image(const string& filename) {
    auto P = parser::parse(filename, mode::POST);
    converter c;
    cout << __func__ << " initial states: " << "\n";
    for (const auto& its : P.first) {
        cout << its << "\n";
        //cout << c.convert(its) << "\n";
    }

    cout << __func__ << " final states: " << "\n";
    for (const auto& ifs : P.second) {
        cout << ifs << "\n";
        //cout << c.convert(ifs) << "\n";
    }

    uint sss = 1;
    auto sv = c.convert_sss_to_sps(sss);
    shared_state s(sv);
    cout << "shared bitset: " << sv << "\n";
    cout << "shared state: " << s << "\n";

    state_v lv(0);
    cout << "local bitset: " << lv << "\n";
    uint pc;
    cin >> pc;
//    auto sls = c.convert_lps_to_lss(pc, lv);
//    cout << sls << "\n";
//    cout << "local state: " << sls << "\n";
    local_state l1(pc, lv);
    cout << "local state: " << l1 << "\n";
    local_state l2(2, lv);
    cout << "local state: " << l2 << "\n";

    ca_locals locals;
    locals.emplace(l1, 2);
    locals.emplace(l2, 1);

    prog_state tau(s, locals);
    cout << tau << "\n";
    post_image image;
    auto _tau = image.step(tau);
    for (const auto& g : _tau)
        cout << g << endl;
}

/**
 * @brief test image computation
 * @param filename
 */
void tst_parser::test_pre_image(const string& filename) {
    auto P = parser::parse(filename, mode::PREV);
    /// testing converter
    cout << __func__ << " initial states: " << "\n";
    for (const auto& its : P.first) {
        cout << its << "\n";
        //cout << c.convert(its) << "\n";
    }

    cout << __func__ << " final states: " << "\n";
    for (const auto& ifs : P.second) {
        cout << ifs << "\n";
        //cout << c.convert(ifs) << "\n";
    }

    /// testing preimage computation
    shared_state s(state_v(1));
    cout << "shared state: " << s << "\n";

    state_v lv(0);
    uint pc;
    cin >> pc;
    local_state l1(pc, lv);
    cout << "local state: " << l1 << "\n";
    local_state l2(2, lv);
    cout << "local state: " << l2 << "\n";

    ca_locals locals;
    locals.emplace(l1, 2);
    locals.emplace(l2, 1);

    prog_state tau(s, locals);
    cout << tau << "\n";

    pre_image image;
    auto _tau = image.step(tau);
    for (const auto& g : _tau)
        cout << g << "\n";
    cout << endl;
}

/**
 * @brief test split function
 */
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
    cout << endl;
}

/**
 * @brief testing
 */
void tst_solver::test_all_sat_solve() {
    refs::SV_NUM = 2;
    refs::LV_NUM = 2;
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
