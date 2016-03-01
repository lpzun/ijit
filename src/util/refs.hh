/**
 * @brief refs.hh: this file defines some constant/static variables
 *        used across the API.
 *
 * @date   Nov 13, 2015
 * @author Peizun Liu
 */

#ifndef UTIL_REFS_HH_
#define UTIL_REFS_HH_

#ifndef SIZE_B
#define SIZE_B 16
#else
#endif

#include "head.hh"

namespace iotf {

class refs {
public:
    refs() {
    }
    ~refs() {
    }

    static ushort SV_NUM;
    static ushort LV_NUM;
    static ushort PC_NUM;

    /// constant expression
    static const string CONST_N; /// constant nondeterminism
    static const string CONST_T; /// constant true
    static const string CONST_F; /// constant false

    ///  unary expression
    static const string NEG; /// !, negation

    /// binary expression
    static const string AND; /// &, and
    static const string OR;  /// |, or
    static const string XOR; /// ^, exclusive or
    static const string EQ;  /// =, equal
    static const string NEQ; /// !=, not equal
    static const string IMPLIES; /// =>, implies

    /// parentheses "()"
    static const string PAREN_L;
    static const string PAREN_R;
};

} /* namespace otf */

#endif /* UTIL_REFS_HH_ */
