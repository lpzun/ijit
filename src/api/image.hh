/**
 * @brief image.hh
 *
 * @date   Nov 16, 2015
 * @author Peizun Liu
 */

#ifndef API_IMAGE_HH_
#define API_IMAGE_HH_

#include "../util/algs.hh"
#include "cfg.hh"

namespace iotf {

/**
 * @brief data structure: image: a derived class of image
 *        to compute pre images of a configuration
 */
class image {
public:
	image() {
	}

	virtual ~image() {
	}

	virtual deque<global_state> step(const global_state& tau) = 0;
private:
	virtual void parser(const string& filename) = 0;
	virtual cfg build_CFG(const string& filename) = 0;
};

/**
 * @brief data structure: pre_image: a derived class of image via
 *        public inheritance.
 *        to compute pre images of a configuration
 */
class pre_image: public image {
public:
	pre_image();
	virtual ~pre_image();
	virtual deque<global_state> step(const global_state& tau) override;

private:
	deque<global_state> compute_cov_predecessors(const global_state& _tau,
			const cfg& G);
	deque<global_state> compute_drc_precedessors(const global_state& _tau,
			const cfg& G);
	deque<global_state> compute_exp_predecessors(const global_state& _tau,
			const cfg& G);

	deque<local_state> compute_image_atom_sect(shared_state& s,
			const local_state& l);
	void compute_image_bcst_stmt(deque<local_state>& pw);

	virtual void parser(const string& filename) override;
	virtual cfg build_CFG(const string& filename) override;
};

/**
 * @brief data structure: post_image: a derived class of image via
 *        public inheritance.
 *        to compute post images of a configuration
 */
class post_image: public image {
public:
	post_image();
	virtual ~post_image();

	virtual deque<global_state> step(const global_state& tau) override;
private:
	deque<global_state> compute_cov_successors(const global_state& tau,
			const cfg& G);
	deque<local_state> compute_image_atom_sect(shared_state& s,
			const local_state& l);

	virtual void parser(const string& filename) override;
	virtual cfg build_CFG(const string& filename) override;
};

} /* namespace otf */

#endif /* API_IMAGE_HH_ */
