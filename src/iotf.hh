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
#include "util/excp.hh"
#include "api/cfg.hh"
#include "bpp/bopp.tab.hh"

namespace iotf {

/// system state
using syst_state = pair<uint, map<uint, uint>>;
using prog_state = global_state;

using initl_ps = deque<prog_state>;
using final_ps = deque<prog_state>;

/**
 * @brief the mode of parser: probably compute prev-/post- images of a global state
 */
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

    static pair<initl_ps, final_ps> parse(const string& filename,
            const mode& m = mode::PREV);

    static const cfg& get_post_G() {
        return post_G;
    }

    static const cfg& get_prev_G() {
        return prev_G;
    }

private:
    static pair<initl_ps, final_ps> parse_in_prev_mode(const string& filename);
    static pair<initl_ps, final_ps> parse_in_post_mode(const string& filename);

    static cfg prev_G; /// control flow graph in PREV mode
    static cfg post_G; /// control flow graph in POST mode
};

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

    virtual deque<prog_state> convert(const deque<syst_state>& ss);
    virtual deque<syst_state> convert(const deque<prog_state>& ps);
    virtual prog_state convert(const syst_state& ss);
    virtual syst_state convert(const prog_state& ps);

private:
    vector<bool> convert_ss_to_ps(const uint& ss);
    uint convert_ps_to_ss(const vector<bool>& ps);
};

/**
 * @brief the type of pre_image: direct preimage or covering preimage
 *        DRC: direct   preimages
 *        COV: covering preimages
 */
enum class prev {
    DRC, COV
};

/**
 * @brief interface: the class pre_image is used to compute preimages
 *        of a global state
 */
class pre_image {
public:
    pre_image();
    ~pre_image();
    deque<prog_state> step(const prog_state& tau, const prev& p = prev::DRC);
    deque<prog_state> step(const prog_state& tau, const local_state& l);

private:
    /// compute covering preimages
    deque<prog_state> compute_cov_pre_images(const prog_state& _tau);
    deque<prog_state> compute_exp_pre_images(const prog_state& _tau);

    /// compute direct preimages
    deque<prog_state> compute_drc_pre_images(const prog_state& _tau);

    void compute_pre_images(const prog_state& _tau, const local_state& _l,
            deque<prog_state>& images);

    deque<local_state> compute_image_atom_sect(shared_state& s,
            const local_state& l);
    void compute_image_bcst_stmt(deque<local_state>& pw);

    deque<pair<state_v, state_v>> compute_image_assg_stmt(const state_v& _sv,
            const state_v& _lv);
    deque<pair<state_v, state_v>> weakest_precondition(const state_v& _sv,
            const state_v& _lv);
};

/**
 * @brief interface: the class post_image is used to compute postimages
 *        of a global state
 */
class post_image {
public:
    post_image();
    ~post_image();

    deque<prog_state> step(const prog_state& tau);
    deque<prog_state> step(const prog_state& tau, const local_state& l);

private:
    void compute_post_images(const prog_state& tau, const local_state& l,
            deque<prog_state>& images);

    void compute_image_assg_stmt(state_v& _s, state_v& _l, const state_v& s,
            const state_v& l, const size_pc& pc);

    local_state compute_image_ifth_stmt(const local_state& l,
            const size_pc& _pc);
    local_state compute_image_else_stmt(const local_state& l);

    void compute_image_atom_sect(const shared_state& s, const local_state& l,
            deque<shared_state>& _s, deque<local_state>& _l);
};

} /* namespace otf */

#endif /* IOTF_HH_ */
