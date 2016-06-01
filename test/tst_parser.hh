/**
 * @brief tst_parser.hh
 *
 * @date  : Feb 4, 2016
 * @author: lpzun
 */

#ifndef TST_PARSER_HH_
#define TST_PARSER_HH_

#include "../src/iotf.hh"

namespace ijit {

class tst_parser {
public:
    tst_parser();
    ~tst_parser();

    static void test_parser(const string& filename);
    static void test_post_image(const string& filename);
    static void test_pre_image(const string& filename);
};

class tst_solver {
public:
    static void test_split();
    static void test_all_sat_solve();

private:
    static void print(const deque<pair<symbval, symbval>>& assgs);
};

} /* namespace iotf */

#endif /* TST_PARSER_HH_ */
