/**
 * @brief cfg.hh
 *
 * @date   Nov 17, 2015
 * @author Peizun Liu
 */

#ifndef API_CFG_HH_
#define API_CFG_HH_

#include "../util/state.hh"

namespace iotf {

/**
 * @breif some special statement type
 *         SKIP = -1 : all other statement
 *         GOTO = -2 : goto statement
 *         ASSG = -3 : assignment statement
 *         IFEL = -4 : if (<expr>) then <sseq> else <sseq>; fi;
 *         ASSE = -5 : assertion statement
 *         ASSU = -6 : assume statement
 *         NTHR = -7 : thread creation statement
 *         ETHR = -8 : thread termination statement
 *         ATOM = -9 : atomic beginning
 *         EATM = -10: invariant in weakest precondition
 *         BCST = -11: broadcast statement
 *         WAIT = -12: wait statement
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
	WAIT = -12
};

/**
 * @brief data structure expr
 *        extract an expression from a string
 */
class expr {
public:
	expr();
	expr(const deque<string>& se);
	expr(const expr& e);
	~expr();

	/// getter
	const deque<string>& get_se() const {
		return se;
	}

	const value_v eval(const state_v& sh, const state_v& lo) const;
	value_v eval(const state_v& sh, const state_v& lo);
private:
	deque<string> se;
};

/**
 * @brief data structure stmt
 *        store statement
 */
class stmt {
public:
	stmt();
	stmt(const type_stmt& type, const expr& precondition);
	stmt(const stmt& s);
	~stmt();

	const expr& get_precondition() const {
		return precondition;
	}

	type_stmt get_type() const {
		return type;
	}

private:
	type_stmt type;
	expr precondition;
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

/**
 * @brief define Control Flow Graph
 */
class cfg {
public:
	cfg();
	cfg(const size_pc& size_A, const size_pc& size_E);
	cfg(const adj_list& A, const vector<edge>& E);
	~cfg();

	const adj_list& get_A() const {
		return A;
	}

	const vector<edge>& get_E() const {
		return E;
	}

	void add_edge(const edge& e);
	void add_edge(const size_pc& idx, const edge& e);

private:
	adj_list A;
	vector<edge> E;
};

} /* namespace otf */

#endif /* API_CFG_HH_ */
