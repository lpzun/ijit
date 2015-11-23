/**
 * image.cc
 *
 *  Created on: Nov 16, 2015
 *      Author: lpzun
 */

#include "image.hh"

namespace otf {

post_image::post_image() {

}

post_image::~post_image() {

}

/**
 * @brief implement the pure virtual function <step> from base case image
 * @param tau
 * @return cover successors
 *         a set of cover successors
 */
deque<global_state> post_image::step(const global_state& tau) {
	auto G = this->build_CFG("");
	return this->compute_cov_successors(tau, G);
}

/**
 * @brief compute the cover successors of configuration tau
 * @param tau
 * @param G
 * @return
 */
deque<global_state> post_image::compute_cov_successors(const global_state& tau,
		const cfg& G) {
	deque<global_state> cov;
	const auto& sh = tau.get_s(); /// shared state
	for (auto il = tau.get_locals().cbegin(); il != tau.get_locals().cend();
			++il) {
		const auto& pc = il->first.get_pc();    /// current pc
		const auto& lo = il->first.get_vars();  /// local state
		for (auto ipc = G.get_A()[pc].cbegin(); ipc != G.get_A()[pc].cend();
				++ipc) {
			const auto& e = G.get_E()[*ipc]; /// get the edge point by pc
			const auto& _pc = e.get_dest();
			switch (e.get_stmt()) {
			case type_stmt::NTHR:
				break;
			case type_stmt::WAIT:
				break;
			case type_stmt::BCST:
				break;
			case type_stmt::ATOM:
				break;
			case type_stmt::ETHR:
				break;
			case type_stmt::GOTO:
				break;
			case type_stmt::ASSG:
				break;
			case type_stmt::WPIN:
				break;
			default:
				local_state _lo(_pc, lo);
			}
		}
	}
	return cov;
}

void post_image::parser(const string& filename) {

}

cfg post_image::build_CFG(const string& filename) {
	cfg G;
	return G;
}

} /* namespace otf */
