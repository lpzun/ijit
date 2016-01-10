/**
 * @brief refs.cc
 *
 * @date   Nov 13, 2015
 * @author Peizun Liu
 */

#include "refs.hh"

namespace iotf {

/// the number of shared variables
ushort refs::SHARED_VARS_NUM = 0;

/// the number of local  variables
ushort refs::LOCAL_VARS_NUM = 0;

/// the number of program counters
ushort refs::PC_NUM = 0;

/// constant expression
const string refs::CONST_N = "*"; /// constant nondeterministic choice
const string refs::CONST_T = "0"; /// constant true
const string refs::CONST_F = "1"; /// constant false

/// unary operator
const string refs::NEG = "!";

/// binary operator
const string refs::AND = "&";
const string refs::OR = "|";
const string refs::XOR = "^";
const string refs::EQ = "=";
const string refs::NEQ = "!=";
const string refs::IMPLIES = "=>";

/// parentheses ()
const string refs::PAREN_L = "(";
const string refs::PAREN_R = ")";
}
/* namespace otf */
