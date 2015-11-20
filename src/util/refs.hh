/**
 * @brief refs.hh
 *
 * @date   Nov 13, 2015
 * @author Peizun Liu
 */

#ifndef UTIL_REFS_HH_
#define UTIL_REFS_HH_

#include "head.hh"

namespace otf {

class refs {
public:
	refs();
	virtual ~refs();

	static ushort SHARED_VARS_NUM;
	static ushort LOCAL_VARS_NUM;
	static ushort PC_NUM;

};

} /* namespace otf */

#endif /* UTIL_REFS_HH_ */
