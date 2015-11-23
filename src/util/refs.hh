/**
 * @brief refs.hh
 *
 * @date   Nov 13, 2015
 * @author Peizun Liu
 */

#ifndef UTIL_REFS_HH_
#define UTIL_REFS_HH_

#include "head.hh"

namespace iotf {

class refs {
public:
	refs();
	virtual ~refs();

	static ushort SHARED_VARS_NUM;
	static ushort LOCAL_VARS_NUM;
	static ushort PC_NUM;

	/// used in expression
	static const string NON_DET;
	static const string TRUE;
	static const string FALSE;

	static const string AND;
	static const string OR;
	static const string XOR;
	static const string NEG;

	static const string R_PAREN;
	static const string L_PAREN;
};

} /* namespace otf */

#endif /* UTIL_REFS_HH_ */
