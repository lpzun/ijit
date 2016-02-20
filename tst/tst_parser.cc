/**
 * @brief tst_parser.cc
 *
 * @date  : Feb 4, 2016
 * @author: lpzun
 */

#include "tst_parser.hh"

namespace iotf {

tst_parser::tst_parser() {

}

tst_parser::~tst_parser() {

}

void tst_parser::test_parser(const string& filename) {
    auto P = parser::parse(filename, mode::POST);
}

void tst_solver::tst_split() {
    cout<<__func__<<"I am here\n";
    DBG_LOC();
    deque<symbol> se1;
    se1.emplace_back(solver::CONST_N);
    se1.emplace_back(solver::NEG);
    se1.emplace_back(solver::PAR);
    se1.emplace_back(solver::CONST_N);
    for (const auto& s : se1) {
        cout << s << endl;
    }
    auto ret = solver::split(se1);
    cout << "size: " << ret.size() << endl;
    for (const auto& l : ret) {
        for (const auto& s : l)
            cout << s << endl;
    }
}

} /* namespace iotf */
