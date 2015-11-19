/**
 * image.cc
 *
 *  Created on: Nov 16, 2015
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
	deque<global_state> cov;

	return cov;
}

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
	return this->compute_cov_successors(tau);
}

/**
 * @brief compute the cover successors of configuration tau
 * @param tau
 * @return
 */
deque<global_state> post_image::compute_cov_successors(
		const global_state& tau) {
	deque<global_state> cov;
	return cov;
}

} /* namespace otf */
