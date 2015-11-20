/**
 * cfg.hh
 *
 *  Created on: Nov 17, 2015
 *      Author: lpzun
 */

#ifndef API_CFG_HH_
#define API_CFG_HH_

#include "../util/state.hh"

namespace otf {

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
 */
enum class STMT {
	NORM = -1,
	NTHR = -2,
	WAIT = -3,
	BCST = -4,
	ATOM = -5,
	ETHR = -6,
	GOTO = -7,
	ASSG = -8,
	WPIN = -9
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
	edge(const size_pc& src, const size_pc& dest, const STMT& stmt);
	edge(const edge& e);
	virtual ~edge();

	size_pc get_dest() const {
		return dest;
	}

	size_pc get_src() const {
		return src;
	}

	STMT get_stmt() const {
		return stmt;
	}

private:
	size_pc src;
	size_pc dest;
	STMT stmt;
};

/**
 * @brief data structure: fws_edge: a derived class of edge via public
 *        inheritance
 *        to define the forward edge
 * @note  post-image computation relies on forward edge
 */
class fws_edge: public edge {
public:
	fws_edge();
	fws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt);
	fws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt,
			const vector<value_v>& sps, const vector<value_v>& spl);
	fws_edge(const fws_edge& fe);
	virtual ~fws_edge();

	const vector<value_v>& get_spl() const {
		return spl;
	}

	const vector<value_v>& get_sps() const {
		return sps;
	}

private:
	vector<value_v> sps; /// strongest postcondition of shared part
	vector<value_v> spl; /// strongest postcondition of local  part
};

/**
 * @brief data structure: bws_edge: a derived class of edge via public
 *        inheritance
 *        to define the backward edge
 * @note  pre-image computation relies on backward edge
 */
class bws_edge: public edge {
public:
	bws_edge();
	bws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt);
	bws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt,
			const vector<value_v>& wp);
	bws_edge(const bws_edge& be);
	virtual ~bws_edge();

	const vector<value_v>& get_wp() const {
		return wp;
	}

private:
	vector<value_v> wp; /// weakest precondition of statement stmt
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
