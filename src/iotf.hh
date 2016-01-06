/******************************************************************************
 * Synopsis	    [OTF: an On-The-Fly API: from Boolean Program to TTS on demand]
 *
 * Author       [Peizun Liu]
 *
 * (C) 2015 - 2018 Peizun Liu, Northeastern University, United States
 *
 * All rights reserved. Redistribution and use in source and binary forms,
 * with or without modification, are permitted provided that the following
 * conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 *    this list of conditions and the following disclaimer.
 *
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * 3. All advertising materials mentioning features or use of this software
 *    must display the following acknowledgment:
 *
 *    This product includes software developed by Peizun Liu @ Thomas Wahl's
 *    group, Northeastern University, United States and its contributors.
 *
 * 4. Neither the name of the University nor the names of its contributors
 *    may be used to endorse or promote products derived from this software
 *    without specific prior written permission.
 *
 * THIS SOFTWARE IS PROVIDED BY THE REGENTS AND CONTRIBUTORS `AS IS'' AND ANY
 * EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE REGENTS OR CONTRIBUTORS BE LIABLE FOR ANY
 * DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
 * (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
 * ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 *****************************************************************************/

#ifndef IOTF_HH_
#define IOTF_HH_

#include "util/algs.hh"
#include "api/cfg.hh"

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
	deque<prog_state> compute_cov_predecessors(const prog_state& _tau,
			const cfg& G);
	deque<prog_state> compute_drc_precedessors(const prog_state& _tau,
			const cfg& G);
	deque<prog_state> compute_exp_predecessors(const prog_state& _tau,
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
	deque<prog_state> compute_cov_successors(const prog_state& tau,
			const cfg& G);
	deque<local_state> compute_image_atom_sect(shared_state& s,
			const local_state& l);

	void compute_image_assg_stmt(state_v& s, const size_t& start,
			const vector<expr>& assgs, const state_v& sh, const state_v& lo);
};

} /* namespace otf */

#endif /* IOTF_HH_ */
