/**
 * @brief cfg.hh
 *
 * @date   Nov 16, 2015
 * @author Peizun Liu
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

	/**
	 * @brief increment the counter of t_in by one
	 * @param t_in
	 * @param Z
	 */
	static void increment(const local_state& t_in, cab_locals& Z) {
		auto ifind = Z.find(t_in);
		if (ifind != Z.end()) {
			ifind->second += 1;
		} else {
			Z.emplace(t_in, 1);
		}
	}

	/**
	 * @brief decrement the counter of t_de by one
	 * @param t_de
	 * @param Z
	 */
	static void decrement(const local_state& t_de, cab_locals& Z) {
		auto ifind = Z.find(t_de);
		if (ifind != Z.end()) {
			if (--ifind->second == 0)
				Z.erase(ifind);
		} else {
			throw;
		}
	}

	static deque<vector<sbool>> split(const vector<sbool>& vs);
};
} /* namespace iotf */

#endif /* UTIL_ALGS_HH_ */
