/**
 * algs.hh
 *
 *  Created on: Nov 16, 2015
 *      Author: lpzun
 */

#ifndef UTIL_ALGS_HH_
#define UTIL_ALGS_HH_

#include "state.hh"

namespace iotf {
class alg {
public:
	static cab_locals update_counters(const local_state& t_in,
			const local_state& t_de, const cab_locals& Z);

	static cab_locals update_counters(const deque<local_state>& T_in,
			const local_state& t_de, const cab_locals& Z);

	static cab_locals update_counters(const deque<local_state>& T_in,
			const deque<local_state>& T_de, const cab_locals& Z);

	static void merge(const local_state& local, const ushort& n, cab_locals& Z);
};
} /* namespace iotf */

#endif /* UTIL_ALGS_HH_ */
