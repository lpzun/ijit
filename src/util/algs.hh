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

    static deque<vector<sool>> split(const vector<sool>& vs);
};

using symb = short;

class solver {
public:
    const static short CONST_F = 0; /// constant false
    const static short CONST_T = 1; /// constant true
    const static short CONST_N = 2; /// constant nondeterminism
    const static short NEG = -1; /// !, negation
    const static short AND = -2; /// &, and
    const static short OR = -3;  /// |, or
    const static short XOR = -4; /// ^, exclusive or
    const static short EQ = -5;  /// =, equal
    const static short NEQ = -6; /// !=, not equal
    const static short IMP = -7; /// =>, implies
    const static short PAR = -8; /// parenthesis

    solver();
    ~solver();

    static bool solve(const deque<symb>& expr, const state_v& s,
            const state_v& l);
    static short encode(const ushort& idx, const bool& is_shared,
            const bool& is_primed);

    static short decode(const ushort& idx, bool& is_shared);
    static short decode(const ushort& idx, bool& is_shared, bool& is_primed);
};

} /* namespace iotf */

#endif /* UTIL_ALGS_HH_ */
