/**
 * algs.cc
 *
 *  Created on: Nov 16, 2015
 *      Author: lpzun
 */

#include "algs.hh"

namespace iotf {
/**
 * @brief This function is used to increment/decrement the counters for
 * 		  all local states in T_in/T_de.
 * @param t_in
 * @param t_de
 * @param Z
 * @return local states, represented in counter abstraction form
 */
cab_locals alg::update_counters(const local_state& t_in,
		const local_state& t_de, const cab_locals& Z) {
	if (t_in == t_de)
		return Z;

	auto _Z = Z;
	auto ifind = _Z.find(t_de);
	if (ifind != _Z.end()) {
		if (--ifind->second == 0)
			_Z.erase(ifind);
	}

	ifind = _Z.find(t_in);
	if (ifind != _Z.end()) {
		ifind->second += 1;
	} else {
		_Z.emplace(t_in, 1);
	}
	return _Z;
}

/**
 * @brief This function is used to increment/decrement the counters for
 * 		  all local states in T_in/T_de.
 * @param T_in
 * @param t_de
 * @param Z
 * @return
 */
cab_locals alg::update_counters(const deque<local_state>& T_in,
		const local_state& t_de, const cab_locals& Z) {
	auto _Z = Z;

	for (const auto& t_in : T_in)
		merge(t_in, 1, _Z);

	auto ifind = _Z.find(t_de);
	if (ifind != _Z.end()) {
		if (--ifind->second == 0)
			_Z.erase(ifind);
	}

	return _Z;
}

/**
 * @brief This function is used to increment/decrement the counters for
 * 			  all local states in T_in/T_de. It calls function merge.
 * @param T_in: local states whose counter is to be incremented
 * @param T_de: local states whose counter is to to be decremented
 * @param Z: thread counter, represented in counter-abstracted form
 * @return thread counter, represented in counter-abstracted form
 */
cab_locals alg::update_counters(const deque<local_state>& T_in,
		const deque<local_state>& T_de, const cab_locals& Z) {
	auto _Z = Z;

	for (const auto& t_in : T_in) {
		merge(t_in, 1, _Z);
	}

	for (const auto& t_de : T_de) {
		auto ifind = _Z.find(t_de);
		if (ifind != _Z.end()) {
			ifind->second--;
			if (ifind->second == 0)
				_Z.erase(ifind);
		}
	}

	return _Z;
}

/**
 * @brief This function is used to update local's counter:
 * 			  (1) add n to current counter if exists local in Z, or
 * 			  (2) create a item (local, n) if exists no local in Z
 * @param local
 * @param n
 * @param Z
 */
void alg::merge(const local_state& local, const ushort& n, cab_locals& Z) {
	auto ifind = Z.find(local);
	if (ifind != Z.end()) {
		ifind->second += n;
	} else {
		Z.emplace(local, n);
	}
}

} /* namespace otf */
