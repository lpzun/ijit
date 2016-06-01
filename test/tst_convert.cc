/**
 * @brief tst_convert.cc
 *
 * @date  : Feb 4, 2016
 * @author: lpzun
 */

#include "../test/tst_convert.hh"

namespace ijit {

tst_convert::tst_convert() {
    // TODO Auto-generated constructor stub

}

tst_convert::~tst_convert() {
    // TODO Auto-generated destructor stub
}

void tst_convert::test_converter() {
    const uint N = 32;

    bitset<N> mask;
    mask.set();
    cout << mask << "\n";
    bitset<N> foo(4);
    cout << foo << "\n";
    cout << ((foo << 8) & mask) << "\n";

    foo.set(1);
    cout << foo << endl;

    converter c;
//    cout << c.mask << "\n";
//
//    cout << c.convert_sss_to_sps(8) << "\n";
//
//    state_v ps(8);
//    cout << c.convert_sps_to_sss(ps) << "\n";
//
//    const auto& p = c.convert_lss_to_lps(8);
//    cout << "pc: " << p.first << "; lv: " << p.second << "\n";
}

} /* namespace iotf */
