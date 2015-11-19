/**
 * cfg.cc
 *
 *  Created on: Nov 17, 2015
 *      Author: lpzun
 */

#include "cfg.hh"

namespace otf {

cfg::cfg() {
	// TODO Auto-generated constructor stub

}

cfg::~cfg() {
	// TODO Auto-generated destructor stub
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

bws_edge::~bws_edge() {

}

}
/* namespace otf */
