/**
 * @brief image.hh
 *
 * @date   Nov 16, 2015
 * @author Peizun Liu
 */

#ifndef API_IOTF_HH_
#define API_IOTF_HH_

#include "../util/algs.hh"
#include "cfg.hh"

namespace iotf {

enum class mode {
	PREV, POST
};

/**
 * @brief a parser: parse a Boolean program, build its control flow graph
 *        and extract its weakest preconditions/strongest postconditions
 */
class parser {
public:
	parser();

	~parser();

	static void parse(const string& filename, const mode& m = mode::PREV);
private:
	static void parse_in_prev_mode(const string& filename);
	static void parse_in_post_mode(const string& filename);
};

/// system state
using syst_state = pair<uint, map<uint, uint>>;
using prog_state = global_state;

/**
 * @brief a converter: convert a program state to a system state, and vice
 *        versa.
 */
class converter {
public:
	converter() {
	}

	virtual ~converter() {
	}

	virtual prog_state convert(const syst_state& ss);
	virtual syst_state convert(const prog_state& ps);

private:
	vector<bool> convert_ss_to_ps(const uint& ss);
	uint convert_ps_to_ss(const vector<bool>& ps);
};

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

	virtual deque<prog_state> step(const prog_state& tau) = 0;
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
	virtual deque<prog_state> step(const prog_state& tau) override;

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

	deque<pair<state_v, state_v>> compute_image_assg_stmt(const state_v& _sv,
			const state_v& _lv);
	deque<pair<state_v, state_v>> weakest_precondition(const state_v& _sv,
			const state_v& _lv);

	deque<state_v> all_sat_solver();
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

	virtual deque<prog_state> step(const prog_state& tau) override;

private:
	deque<global_state> compute_cov_successors(const global_state& tau,
			const cfg& G);
	deque<local_state> compute_image_atom_sect(shared_state& s,
			const local_state& l);

	void compute_image_assg_stmt(state_v& s, const size_t& start,
			const vector<expr>& assgs, const state_v& sh, const state_v& lo);
};

} /* namespace otf */

#endif /* API_IOTF_HH_ */
