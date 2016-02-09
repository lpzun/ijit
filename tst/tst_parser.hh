/**
 * @brief tst_parser.hh
 *
 * @date  : Feb 4, 2016
 * @author: lpzun
 */

#ifndef TST_PARSER_HH_
#define TST_PARSER_HH_

#include "../src/iotf.hh"

namespace iotf {

class tst_parser {
public:
    tst_parser();
    ~tst_parser();

    void test_parser(const string& filename);
};

class tst_solver {
public:

    static void tst_split();
};

} /* namespace iotf */

#endif /* TST_PARSER_HH_ */
