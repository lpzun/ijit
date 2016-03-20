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
    static ca_locals update_counters(const local_state& t_in,
            const local_state& t_de, const ca_locals& Z);

    static ca_locals update_counters(const deque<local_state>& T_in,
            const local_state& t_de, const ca_locals& Z);

    static ca_locals update_counters(const deque<local_state>& T_in,
            const deque<local_state>& T_de, const ca_locals& Z);

    static void merge(const local_state& local, const ushort& n, ca_locals& Z);

    /**
     * @brief increment the counter of t_in by one
     * @param t_in
     * @param Z
     */
    static inline void increment(const local_state& t_in, ca_locals& Z) {
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
    static inline void decrement(const local_state& t_de, ca_locals& Z) {
        auto ifind = Z.find(t_de);
        if (ifind != Z.end()) {
            ifind->second -= 1;
            if (ifind->second == 0)
                Z.erase(ifind);
        } else {
            throw;
        }
    }

    static void split(const sool& v, const size_t& i, deque<state_v>& svs);
};

/**
 * @brief solver this class contains all function to evaluate all
 *        possible Boolean expressions appearing in Boolean programs.
 */
class solver {
public:
    static const symbol CONST_F = 0; /// constant false
    static const symbol CONST_T = 1; /// constant true
    static const symbol CONST_N = 2; /// constant nondeterminism
    static const symbol NEG = -1; /// !, negation
    static const symbol AND = -2; /// &, and
    static const symbol OR  = -3;  /// |, or
    static const symbol XOR = -4; /// ^, exclusive or
    static const symbol EQ  = -5;  /// =, equal
    static const symbol NEQ = -6; /// !=, not equal
    static const symbol IMP = -7; /// =>, implies
    static const symbol PAR = -8; /// parenthesis

    solver();
    ~solver();

    static bool solve(const deque<symbol>& sexpr, const state_v& s,
            const state_v& l);
    static bool solve(const deque<symbol>& sexpr, const state_v& s,
            const state_v& l, const state_v& _s, const state_v& _l);
    static deque<pair<ss_vars, sl_vars>> all_sat_solve(
            const deque<symbol>& sexpr, const ss_vars& s_vars,
            const sl_vars& l_vars);

    static deque<deque<symbol>> split(const deque<symbol>& sexpr);
    static deque<deque<sool>> split(const deque<sool>& vs);

    static void substitute(deque<symbol>& sexpr, const symbol& var,
            const symbol& ins);

    static symbol encode(const symbol& idx, const bool& is_shared);

private:
    static bool eval(const deque<symbol>& sexpr);

    static symbol decode(const symbol& idx, bool& is_shared);
    static symbol decode(const symbol& idx, bool& is_shared, bool& is_primed);
    static vector<bool> to_binary(const int& n, const short& shift);
    static int power(const int& base, const int& exponent);
};

} /* namespace iotf */

#endif /* UTIL_ALGS_HH_ */
