/**
 * @brief refs.cc
 *
 * @date   Nov 13, 2015
 * @author Peizun Liu
 */

#include "refs.hh"

namespace otf {

refs::refs() {
	// TODO Auto-generated constructor stub

}

refs::~refs() {
	// TODO Auto-generated destructor stub
}

/// the number of shared variables
ushort refs::SHARED_VARS_NUM = 0;

/// the number of local  variables
ushort refs::LOCAL_VARS_NUM = 0;

/// the number of program counters
ushort refs::PC_NUM = 0;

} /* namespace otf */
