/**
 * @brief tst_fws.cc
 *
 * @date  : Mar 8, 2016
 * @author: lpzun
 */

#include "tst_fws.hh"

namespace fws {

FWS::FWS() :
        initl_TS(), final_TS() {
}

FWS::~FWS() {
}

/**
 * @brief the standard finite-state search that operates on transition systems.
 *        Here, we adjust it to an function that directly operates on Boolean
 *        programs using our API.
 * @param n
 * @param filename
 * @return bool
 *        true : if some assertion is violated;
 *        false: otherwise.
 */
bool FWS::standard_FWS(const size_tc& n, const string& filename) {
#ifndef NDEBUG
    cout << __func__ << " " << n << " " << filename << "\n";
#endif
    /// Place 1: call the parser in API to parse Boolean programs.
    ///          It returns a pair of lists that store thread states
    const auto& P = parser::parse(filename, mode::POST);
    this->initl_TS = P.first;  /// the list of initial thread states
    this->final_TS = P.second; /// the list of final   thread states
#ifndef NDEBUG
    cout << __func__ << " initial states: " << "\n";
    for (const auto& its : this->initl_TS) {
        cout << its << "\n";
    }

    cout << __func__ << " final states: " << "\n";
    for (const auto& ifs : this->final_TS) {
        cout << ifs << "\n";
    }
#endif
    antichain worklist;
    antichain explored;

    /// initialize worklist ...
    for (const auto& ips : initl_TS)
        worklist.emplace_back(ips.get_s(), ips.get_l(), n);

    /// Place 2: instantiate <post_image> to compute postimages
    post_image image;
    while (!worklist.empty()) {
        const auto tau = worklist.front();
        worklist.pop_front();
        /// step 1: if upward(tau) is already explored, then
        ///         discard it
        if (!this->is_maximal(tau, explored))
            continue;
        /// step  2: compute all post images; check if final
        ///          state is coverable; maximize <worklist>
        /// Place 3: call the <step> in the instance <image>
        const auto& images = image.step(tau);
        for (const auto& _tau : images) {
            /// return true if _tau covers final state
            if (this->is_reached(_tau))
                return true;
            /// if upward(_tau) already exists, then discard it
            if (!this->is_maximal(_tau, worklist))
                continue;
            /// maximize <worklist> in term of _tau
            this->maximize(_tau, worklist);
            worklist.emplace_back(_tau); /// insert into worklist
        }
        /// maximize <explored> in term of tau
        this->maximize(tau, explored);
        explored.emplace_back(tau); /// insert into explored
    }
    return false;
}

/**
 * @brief check if some already-explored state covers s, and maximize explored
 * @param s
 * @param explored
 * @return
 */
bool FWS::is_maximal(const state& s, const antichain& explored) {
    for (auto itau = explored.begin(); itau != explored.end(); ++itau) {
        if (this->is_covered(s, *itau)) {
            return false;
        }
    }
    return true;
}

/**
 * @brief maximize
 * @param worklist
 */
void FWS::maximize(const state& s, antichain& worklist) {
    for (auto itau = worklist.begin(); itau != worklist.end();) {
        if (this->is_covered(*itau, s)) {
            itau = worklist.erase(itau);
        } else {
            ++itau;
        }
    }
}

/**
 * @brief to determine if s belongs to upward-closure of initial states
 * @param s
 * @return true : if s is in the upward-closure of initial state
 *         false: otherwise
 */
bool FWS::is_reached(const state& s) {
    for (const auto f : this->final_TS) {
        if (s.get_s() == f.get_s()) {
            auto ifind = s.get_locals().find(f.get_l());
            if (ifind != s.get_locals().cend() && ifind->second > 0) {
                cout << "covers: " << s << "\n";
                return true;
            }
        }
    }
    return false;
}

/**
 * @brief to determine whether s1 is covered by s2.
 *        NOTE: this function assumes that the local parts of s1 and s2
 *        are ordered.
 * @param s1
 * @param s2
 * @return true : if s1 <= s2
 *         false: otherwise
 */
bool FWS::is_covered(const state& s1, const state& s2) {
    if (s1.get_s() == s2.get_s()
            && s1.get_locals().size() <= s2.get_locals().size()) {
        auto is1 = s1.get_locals().cbegin();
        auto is2 = s2.get_locals().cbegin();
        while (is1 != s1.get_locals().cend()) {
            /// check if is2 reaches to the end
            if (is2 == s2.get_locals().cend())
                return false;
            /// compare the map's contents
            if (is1->first == is2->first) {
                if (is1->second <= is2->second)
                    ++is1, ++is2;
                else
                    return false;
            } else if (is1->first > is2->first) {
                ++is2;
            } else if (is1->first < is2->first) {
                return false;
            }
        }
        return true;
    }
    return false;
}

} /* namespace fws */
