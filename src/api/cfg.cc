/**
 * @brief cfg.cc: the sou
 *
 * @date   Nov 17, 2015
 * @author Peizun Liu
 */

#include "cfg.hh"

namespace iotf {

/**
 * @brief default constructor
 */
cfg::cfg() :
        A(adj_list(refs::PC_NUM)), E(vector<edge>(refs::PC_NUM)), assignments() {
}

/**
 * @brief constructor with max PC
 * @param max_PC
 */
cfg::cfg(const size_pc& size_A, const size_pc& size_E) :
        A(adj_list(size_A)), E(vector<edge>(size_E)), assignments() {
}

/**
 * @brief constructor with adjacent list A and edge set E
 * @param A
 * @param E
 * @param assigns
 */
cfg::cfg(const adj_list& A, const vector<edge>& E,
        const unordered_map<size_pc, assignment>& assigns) :
        A(A), E(E), assignments(assigns) {

}

/**
 * @brief default destructor
 */
cfg::~cfg() {
}

/**
 * @brief append an edge to E in CFG
 * @param e
 */
void cfg::add_edge(const size_pc& src, const size_pc& dest,
        const type_stmt& type) {
    if (src < this->A.size())
        A[src].emplace_back(dest);
    else
        A.emplace_back(deque<size_pc>(1, dest));
    E.emplace_back(src, dest, type);
}

/**
 * @brief append an edge to E in CFG
 * @param e
 */
void cfg::add_edge(const size_pc& src, const size_pc& dest,
        const type_stmt& type, const expr& condition) {
    if (src < this->A.size())
        A[src].emplace_back(dest);
    else
        A.emplace_back(deque<size_pc>(1, dest));
    E.emplace_back(src, dest, type, condition);
}
/**
 * @brief add an assignment to location pc
 * @param pc: location
 * @param a : assignment
 */
void cfg::add_assignment(const size_pc& pc, const assignment& a) {
    this->assignments.emplace(pc, a);
}

/**
 * @brief output a assignment
 * @param out
 * @param s
 * @return
 */
ostream& operator <<(ostream& out, const assignment& s) {
    for (auto i = 0; i < s.sh.size(); ++i)
        if (s.sh[i].is_valid())
            out << "s" << i << "=" << s.sh[i] << ";";
    for (auto i = 0; i < s.lo.size(); ++i)
        if (s.lo[i].is_valid())
            out << "l" << i << "=" << s.lo[i] << ";";
    return out;
}

/**
 * @brief default constructor
 */
edge::edge() :
        src(0), dest(0), st() {

}

/**
 * @brief constructor with src, dest and stmt
 * @param src
 * @param dest
 * @param stmt
 */
edge::edge(const size_pc& src, const size_pc& dest, const stmt& s) :
        src(src), dest(dest), st(s) {

}

/**
 *
 * @param src
 * @param dest
 * @param type
 */
edge::edge(const size_pc& src, const size_pc& dest, const type_stmt& type) :
        src(src), dest(dest), st(type) {

}

/**
 * @brief constructor with src, dest, type and stmt
 * @param src
 * @param dest
 * @param type
 * @param condition
 */
edge::edge(const size_pc& src, const size_pc& dest, const type_stmt& type,
        const expr& condition) :
        src(src), dest(dest), st(type, condition) {

}

/**
 * @brief copy constructor
 * @param e
 */
edge::edge(const edge& e) :
        src(e.get_src()), dest(e.get_dest()), st(e.get_stmt()) {
}

/**
 * @brief default destructor
 */
edge::~edge() {

}

/**
 * @brief overloading operator <<
 * @param out
 * @param s
 * @return output stream:
 *         print an edge in cfg
 */
ostream& operator <<(ostream& out, const edge& e) {
    out << e.get_src() << "->" << e.get_dest() << " " << e.get_stmt();
    return out;
}

/**
 * @brief default constructor
 */
stmt::stmt() :
        type(), condition() {

}

stmt::stmt(const type_stmt& type) :
        type(type), condition() {

}

/**
 * @brief constructor with type and precondition
 * @param type
 * @param precondition
 */
stmt::stmt(const type_stmt& type, const expr& condition) :
        type(type), condition(condition) {

}

/**
 * @brief copy constructor
 * @param s
 */
stmt::stmt(const stmt& s) :
        type(s.get_type()), condition(s.get_condition()) {

}

/**
 * @brief default destructor
 */
stmt::~stmt() {
}

/**
 * @brief overloading operator <<
 * @param out
 * @param s
 * @return output stream:
 *         print statement
 */
ostream& operator <<(ostream& out, const stmt& s) {
    out << s.get_type() << " " << s.get_condition();
    return out;
}

/**
 * @brief default consructor
 */
expr::expr() :
        sexpr() {

}

/**
 * @brief constructor with string
 * @param se
 */
expr::expr(const deque<symbol>& sexpr) :
        sexpr(sexpr) {

}

/**
 * @brief copy constructor
 * @param e
 */
expr::expr(const expr& e) :
        sexpr(e.get_sexpr()) {

}

/**
 * @brief default destructor
 */
expr::~expr() {

}

/**
 * @brief evaluation function:
 *
 * @param sv
 * @param lv
 * @return value_v
 */
const value_v expr::eval(const state_v& sv, const state_v& lv) const {
    return solver::solve(sexpr, sv, lv);
}

/**
 * @brief evaluation function:
 *        non-const version
 * @param sh
 * @param lo
 * @return a valuation
 */
value_v expr::eval(const state_v& sh, const state_v& lo) {
    return static_cast<value_v>(static_cast<const expr&>(*this).eval(sh, lo));
}

/**
 * @brief overloading operator <<
 * @param out
 * @param e
 * @return
 */
ostream& operator <<(ostream& out, const expr& e) {
    for (auto is = e.get_sexpr().begin(); is != e.get_sexpr().end(); ++is) {
        out << *is << " ";
    }
    return out;
}
}
/* namespace otf */
