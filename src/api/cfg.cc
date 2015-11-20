/**
 * cfg.cc
 *
 *  Created on: Nov 17, 2015
 *      Author: lpzun
 */

#include "cfg.hh"

namespace otf {

/**
 * @brief default constructor
 */
cfg::cfg() :
		A(adj_list(refs::PC_NUM)), E(vector<edge>(refs::PC_NUM)) {
}

/**
 * @brief constructor with max PC
 * @param max_PC
 */
cfg::cfg(const size_pc& size_A, const size_pc& size_E) :
		A(adj_list(size_A)), E(vector<edge>(size_E)) {
}

/**
 * @brief constructor with adjacent list A and edge set E
 * @param A
 * @param E
 */
cfg::cfg(const adj_list& A, const vector<edge>& E) :
		A(A), E(E) {

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
void cfg::add_edge(const edge& e) {
	E.emplace_back(e);
}

/**
 * @brief insert edge in location idx if applicable (i.e., idx <= E.size());
 *        throw an exception if idx > E.size();
 * @param idx
 * @param e
 */
void cfg::add_edge(const size_pc& idx, const edge& e) {
	if (idx < E.size())
		E[idx] = e;
	else if (idx == E.size())
		E.emplace_back(e);
	else
		throw;
}

/**
 * @brief default constructor
 */
edge::edge() :
		src(0), dest(0), stmt(STMT::NORM) {

}

/**
 * @brief constructor with src, dest and stmt
 * @param src
 * @param dest
 * @param stmt
 */
edge::edge(const size_pc& src, const size_pc& dest, const STMT& stmt) :
		src(src), dest(dest), stmt(stmt) {

}

/**
 * @brief copy constructor
 * @param e
 */
edge::edge(const edge& e) :
		src(e.get_src()), dest(e.get_dest()), stmt(e.get_stmt()) {

}

/**
 * @brief default destructor
 */
edge::~edge() {

}

/**
 * @brief default constructor
 */
fws_edge::fws_edge() :
		edge(), sps(), spl() {

}

/**
 * @brief constructor with src, dest, and stmt (all three parameters used in
 *        base class)
 * @param src
 * @param dest
 * @param stmt
 */
fws_edge::fws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt) :
		edge(src, dest, stmt), sps(), spl() {

}

/**
 * @brief constructor with src, dest, stmt (used in base class), and sps, spl
 * @param src
 * @param dest
 * @param stmt
 * @param sps
 * @param spl
 */
fws_edge::fws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt,
		const vector<value_v>& sps, const vector<value_v>& spl) :
		edge(src, dest, stmt), sps(sps), spl(spl) {

}

/**
 * @brief copy constructor
 * @param fe
 */
fws_edge::fws_edge(const fws_edge& fe) :
		edge(fe.get_src(), fe.get_dest(), fe.get_stmt()), sps(fe.get_sps()), spl(
				fe.get_spl()) {

}

/**
 * @brief default destructor
 */
fws_edge::~fws_edge() {

}

/**
 * @brief default constructor
 */
bws_edge::bws_edge() :
		edge(), wp() {

}

/**
 * @brief constructor with src, dest, and stmt (all three parameters used in
 *        base class)
 * @param src
 * @param dest
 * @param stmt
 */
bws_edge::bws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt) :
		edge(src, dest, stmt), wp() {

}

/**
 * @brief constructor with src, dest, stmt (used in base class), and wp
 * @param src
 * @param dest
 * @param stmt
 * @param wp
 */
bws_edge::bws_edge(const size_pc& src, const size_pc& dest, const STMT& stmt,
		const vector<value_v>& wp) :
		edge(src, dest, stmt), wp(wp) {

}

/**
 * @brief copy constructor
 * @param be
 */
bws_edge::bws_edge(const bws_edge& be) :
		edge(be.get_src(), be.get_dest(), be.get_stmt()), wp(be.get_wp()) {

}

bws_edge::~bws_edge() {

}

}
/* namespace otf */
