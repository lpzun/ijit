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
    cout << "I am here.....\n";
    deque<symbol> sexpr;
    sexpr.emplace_back(solver::CONST_N);
    sexpr.emplace_back(solver::NEG);
    sexpr.emplace_back(solver::PAR);
    sexpr.emplace_back(solver::CONST_N);
    for (const auto& s : sexpr) {
        cout << s << endl;
    }
    auto ret = solver::split(sexpr);
    cout << "size: " << ret.size() << endl;
    for (const auto& l : ret) {
        for (const auto& s : l)
            cout << s << endl;
    }
}

} /* namespace iotf */
