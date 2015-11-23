/**
 * cfg.hh
 *
 *  Created on: Nov 17, 2015
 *      Author: lpzun
 */

#ifndef API_CFG_HH_
#define API_CFG_HH_

#include "../util/state.hh"

namespace iotf {

/**
 * @breif some special statement type
 *         NORM = -1: all other statement
 *         NTHR = -2: thread creation statement
 *         WAIT = -3: wait statement
 *         BCST = -4: broadcast statement
 *         ATOM = -5: atomic beginning
 *         ETHR = -6: thread termination statement
 *         GOTO = -7: goto statement
 *         ASSG = -8: assignment statement
 *         WPIN = -9: invariant in weakest precondition
 *         IFEL = -10: if (<expr>) then <sseq> else <sseq> fi;
 */
enum class type_stmt {
	NORM = -1,
	NTHR = -2,
	WAIT = -3,
	BCST = -4,
	ATOM = -5,
	ETHR = -6,
	GOTO = -7,
	ASSG = -8,
	WPIN = -9,
	IFEL = -10
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
