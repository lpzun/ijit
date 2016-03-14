/**
 * @brief  state.cc
 *
 *
 * @date   Nov 13, 2015
 * @author Peizun Liu
 */

#include "state.hh"

namespace iotf {

/**
 * @brief default constructor
 */
shared_state::shared_state() :
        vars() {
}

/**
 * @brief constructor with state_v
 * @param vars
 */
shared_state::shared_state(const state_v& vars) :
        vars(vars) {
    // cout << __func__ << " constructor: " << vars << "\n";
}

/**
 * @brief default destructor
 */
shared_state::~shared_state() {

}

/**
 * @brief overloading operator <<
 * @param out
 * @param s
 * @return output stream:
 *         print shared state
 */
ostream& operator <<(ostream& out, const shared_state& s) {
    if (s.get_vars().size() > 0) {
        for (auto i = 0; i < refs::SV_NUM; ++i)
            out << s.get_vars()[i];
    }
    return out;
}

/**
 * @brief constructor
 */
local_state::local_state() :
        pc(0), vars() {

}

/**
 * @brief constructor with pc and vars
 * @param pc
 * @param vars
 */
local_state::local_state(const size_pc& pc, const state_v& vars) :
        pc(pc), vars(vars) {
    //cout << __func__ << " constructor : " << vars << "\n";

}

/**
 * @brief default destructor
 */
local_state::~local_state() {

}

/**
 * @brief overloading operator <<
 * @param out
 * @param l
 * @return output stream
 *         print local state
 */
ostream& operator <<(ostream& out, const local_state& l) {
    out << l.get_pc();
    for (auto i = 0; i < refs::LV_NUM; ++i)
        out << l.get_vars()[i];
    return out;
}

/**
 * @brief default constructor
 */
thread_state::thread_state() :
        s(shared_state()), l(local_state()) {

}

/**
 * @brief constructor with shared state s and local state l
 * @param s
 * @param l
 */
thread_state::thread_state(const shared_state& s, const local_state& l) :
        s(s), l(l) {

}

/**
 * @brief constructor with shared state s and local state l
 * @param sv
 * @param pc
 * @param lv
 */
thread_state::thread_state(const state_v& sv, const size_pc& pc,
        const state_v& lv) :
        s(sv), l(pc, lv) {

}

/**
 * @brief copy constructor
 * @param t
 */
thread_state::thread_state(const thread_state& t) :
        s(t.get_s()), l(t.get_l()) {

}

/**
 * @brief default destructor
 */
thread_state::~thread_state() {

}

/**
 * @brief overloading operator <<
 * @param out
 * @param t
 * @return output stream
 *         print thread state
 */
ostream& operator <<(ostream& out, const thread_state& t) {
    out << "(" << t.get_s() << "|" << t.get_l() << ")";
    return out;
}

/**
 * @brief default constructor
 */
global_state::global_state() :
        s(shared_state()), locals() {

}

/**
 * @brief constructor with shared state and local state
 * @param s
 * @param l
 */
global_state::global_state(const shared_state& s, const local_state& l) :
        s(s), locals() {
    locals.emplace(l, 1);
}

/**
 * @brief constructor with shared state and local state
 * @param s
 * @param l
 * @param n
 */
global_state::global_state(const shared_state& s, const local_state& l,
        const size_tc& n) :
        s(s), locals() {
    locals.emplace(l, n);
}

/**
 * @brief constructor with shared state and locals
 * @param s
 * @param locals
 */
global_state::global_state(const shared_state& s, const ca_locals& locals) :
        s(s), locals(locals) {

}

/**
 * @brief copy constructor
 * @param g
 */
global_state::global_state(const global_state& g) :
        s(g.get_s()), locals(g.get_locals()) {

}

/**
 * @brief default destructor
 */
global_state::~global_state() {

}

/**
 * @brief overloading operator <<
 * @param out
 * @param g
 * @return output stream
 *         print global state
 */
ostream& operator <<(ostream& out, const global_state& g) {
    out << "<" << g.get_s() << "|";
    for (auto il = g.get_locals().begin(); il != g.get_locals().end(); ++il)
        out << "(" << il->first << "," << il->second << ")";
    out << ">";
    return out;
}

} /* namespace ucob */

