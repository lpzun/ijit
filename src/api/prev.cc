/**
 * prev.cc
 *
 *  Created on: Nov 22, 2015
 *      Author: lpzun
 */

#include "image.hh"

namespace otf {


pre_image::pre_image() {

}

pre_image::~pre_image() {

}

/**
 * @brief implement the pure virtual function <step> from base case image
 * @param tau
 * @return cover predecessors
 *         a set of cover predecessors
 */
deque<global_state> pre_image::step(const global_state& tau) {
	return this->compute_cov_predecessors(tau);
}

/**
 * @brief compute cover predecessors of configuration tau
 * @param _tau
 * @return the set of cover predecessors
 */
deque<global_state> pre_image::compute_cov_predecessors(
		const global_state& _tau) {
	deque < global_state > cov;

	return cov;
}

void pre_image::parser(const string& filename) {

}

cfg pre_image::build_CFG(const string& filename) {
	cfg G;
	return G;
}
}

