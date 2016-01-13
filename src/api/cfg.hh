/**
 * @brief cfg.hh: the header file of some common data structures:
 *        type_stmt: the type of statements
 *        expr     : expression used in Boolean programs
 *        stmt     : it wraps the type and condition (if applicable)
 *                   of a statement.
 *        edge     : the edge of CFG; it wraps the source \pc and
 *                   destination \pc, as well as the statement.
 *
 * @date   Nov 17, 2015
 * @author Peizun Liu
 */

#ifndef API_CFG_HH_
#define API_CFG_HH_

#include "../util/state.hh"

namespace iotf {

/**
 * @breif data structure <type_stmt>: some special statement type
 *         SKIP = -1 : all other statement
 *         GOTO = -2 : goto statement
 *         ASSG = -3 : assignment statement
 *         IFEL = -4 : if (<expr>) then <sseq> else <sseq>; fi;
 *         ASSE = -5 : assertion statement
 *         ASSU = -6 : assume statement
 *         NTHR = -7 : thread creation statement
 *         ETHR = -8 : thread termination statement
 *         ATOM = -9 : atomic section beginning
 *         EATM = -10: atomic section ending
 *         BCST = -11: broadcast statement
 *         WAIT = -12: wait statement
 *         SIGN = -13: signal statement
 */
enum class type_stmt {
    SKIP = -1,
    GOTO = -2,
    ASSG = -3,
    IFEL = -4,
    ASSE = -5,
    ASSU = -6,
    NTHR = -7,
    ETHR = -8,
    ATOM = -9,
    EATM = -10,
    BCST = -11,
    WAIT = -12,
    SIGN = -13
};

/**
 * @brief data structure <expr>: build an expression from a list of strings
 */
class expr {
public:
    expr();
    expr(const deque<string>& sexpr);
    expr(const expr& e);

    ~expr();

    /// getter
    const deque<string>& get_sexpr() const {
        return sexpr;
    }

    const bool is_valid() const {
        return !sexpr.empty();
    }

    const value_v eval(const state_v& sh, const state_v& lo) const;
    value_v eval(const state_v& sh, const state_v& lo);
private:
    deque<string> sexpr;
};

/**
 * @brief data structure <stmt>: store statement information, it wraps
 *        the type and condition (if applicable) of a statement; it is
 *        labeled to a edge in a control flow graph.
 */
class stmt {
public:
    stmt();
    stmt(const type_stmt& type, const expr& condition);
    stmt(const stmt& s);
    ~stmt();

    /**
     * @brief return the precondition if computing the preimage, or
     *        postcondition if computing the postimage.
     * @return precondition or postcondition
     */
    const expr& get_condition() const {
        return condition;
    }

    /**
     * @brief return statement type
     * @return
     */
    type_stmt get_type() const {
        return type;
    }

private:
    type_stmt type; /// statement type
    expr condition; /// precondition or postcondition
};

/**
 * @brief data structure: edge, the base class
 *        src : source pc of CFG edge
 *        dest: destination pc of CFG edge
 *        stmt: statement type attached to edge (src, dest)
 */
class edge {
public:
    edge();
    edge(const size_pc& src, const size_pc& dest, const stmt& st);
    edge(const edge& e);
    ~edge();

    size_pc get_dest() const {
        return dest;
    }

    size_pc get_src() const {
        return src;
    }

    const stmt& get_stmt() const {
        return st;
    }

private:
    size_pc src;
    size_pc dest;
    stmt st;
};

using adj_list = vector<deque<size_pc>>;
using expr_vec = vector<expr>;

/**
 * @brief this data structure defines the expressions in a parallel
 *        assignment statement
 */
struct assignment {
    expr_vec sh;
    expr_vec lo;
    assignment() :
            sh(refs::SHARED_VARS_NUM), lo(refs::LOCAL_VARS_NUM) {

    }
    ~assignment() {
    }
};

/**
 * @brief this data structure defines the Control Flow Graph used in
 *        pre-/post-images. This is the most important data structure.
 *        A CFG is built during parse a Boolean program via our Parser.
 */
class cfg {
public:
    cfg();
    cfg(const size_pc& size_A, const size_pc& size_E);
    cfg(const adj_list& A, const vector<edge>& E,
            const unordered_map<size_pc, assignment>& assigns);
    ~cfg();

    const adj_list& get_A() const {
        return A;
    }

    const vector<edge>& get_E() const {
        return E;
    }

    const unordered_map<size_pc, assignment>& get_assignments() const {
        return assignments;
    }

    void add_edge(const edge& e);
    void add_edge(const size_pc& idx, const edge& e);

private:
    adj_list A;
    vector<edge> E;
    unordered_map<size_pc, assignment> assignments;
};

} /* namespace otf */

#endif /* API_CFG_HH_ */
