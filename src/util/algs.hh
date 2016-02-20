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
};

class solver {
public:
    static const short CONST_F = 0; /// constant false
    static const short CONST_T = 1; /// constant true
    static const short CONST_N = 2; /// constant nondeterminism
    static const short NEG = -1; /// !, negation
    static const short AND = -2; /// &, and
    static const short OR = -3;  /// |, or
    static const short XOR = -4; /// ^, exclusive or
    static const short EQ = -5;  /// =, equal
    static const short NEQ = -6; /// !=, not equal
    static const short IMP = -7; /// =>, implies
    static const short PAR = -8; /// parenthesis

    solver();
    ~solver();

    static bool solve(const deque<symbol>& sexpr, const state_v& s,
            const state_v& l);
    static bool solve(const deque<symbol>& sexpr, const state_v& s,
            const state_v& l, const state_v& _s, const state_v& _l);

    static bool all_sat_solve(const deque<symbol>& sexpr);

    static deque<deque<symbol>> split(const deque<symbol>& sexpr);
    static deque<deque<sool>> split(const deque<sool>& vs);

private:
    static symbol decode(const symbol& idx, bool& is_shared);
    static symbol decode(const symbol& idx, bool& is_shared, bool& is_primed);
    static vector<bool> to_binary(const int& n, const short& bits);
};

} /* namespace iotf */

#endif /* UTIL_ALGS_HH_ */
