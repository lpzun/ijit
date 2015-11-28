/**
 * @brief cfg.cc
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
 * @brief default constructor
 */
stmt::stmt() :
		type(), precondition() {

}

/**
 * @brief constructor with type and precondition
 * @param type
 * @param precondition
 */
stmt::stmt(const type_stmt& type, const expr& precondition) :
		type(type), precondition(precondition) {

}

/**
 * @brief copy constructor
 * @param s
 */
stmt::stmt(const stmt& s) :
		type(s.get_type()), precondition(s.get_precondition()) {

}

/**
 * @brief default destructor
 */
stmt::~stmt() {
}

/**
 * @brief default consructor
 */
expr::expr() :
		se() {

}

/**
 * @brief constructor with string
 * @param se
 */
expr::expr(const deque<string>& se) :
		se(se) {

}

/**
 * @brief copy constructor
 * @param e
 */
expr::expr(const expr& e) :
		se(e.get_se()) {

}

/**
 * @brief default destructor
 */
expr::~expr() {

}

/**
 * @brief evaluation function:
 *
 * @param sh
 * @param lo
 * @return value_v
 */
const value_v expr::eval(const state_v& sh, const state_v& lo) const {
	stack<value_v> comp_result_stack;
	for (auto ifac = se.cbegin(); ifac != se.cend(); ++ifac) {
		const string& factor = *ifac;
		value_v operand1, operand2;
		if (factor.compare("&&") == 0) { /// and
			operand1 = comp_result_stack.top();
			comp_result_stack.pop();
			operand2 = comp_result_stack.top();
			comp_result_stack.pop();
			comp_result_stack.push(operand2 && operand1);
		} else if (factor.compare("||") == 0) { /// or
			operand1 = comp_result_stack.top();
			comp_result_stack.pop();
			operand2 = comp_result_stack.top();
			comp_result_stack.pop();
			comp_result_stack.push(operand2 || operand1);
		} else if (factor.compare("==") == 0) { /// equal
			operand1 = comp_result_stack.top();
			comp_result_stack.pop();
			operand2 = comp_result_stack.top();
			comp_result_stack.pop();
			comp_result_stack.push(operand2 == operand1);
		} else if (factor.compare("!=") == 0) { /// not equal
			operand1 = comp_result_stack.top();
			comp_result_stack.pop();
			operand2 = comp_result_stack.top();
			comp_result_stack.pop();
			comp_result_stack.push(operand2 != operand1);
		} else if (factor.compare("^") == 0) { /// exclusive OR
			operand1 = comp_result_stack.top();
			comp_result_stack.pop();
			operand2 = comp_result_stack.top();
			comp_result_stack.pop();
			comp_result_stack.push(operand2 ^ operand1);
		} else if (factor.compare("()") == 0) { /// parenthesis
			operand1 = comp_result_stack.top();
			comp_result_stack.pop();
			comp_result_stack.push(operand1);
		} else if (factor.compare("!") == 0) { /// negation
			operand1 = comp_result_stack.top();
			comp_result_stack.pop();
			comp_result_stack.push(!operand1);
		} else if (factor.compare("0") == 0) { /// constant 0
			comp_result_stack.push(false);
		} else if (factor.compare("1") == 0) { /// constant 1
			comp_result_stack.push(true);
		} else if (factor.compare("*")) {
			return true;
		} else { // variables
			short index = std::stoi(factor);
			if (index < refs::SHARED_VARS_NUM)
				comp_result_stack.push(sh[index]);
			else
				comp_result_stack.push(lo[index - refs::SHARED_VARS_NUM]);
		}
	}
	return comp_result_stack.top();
}

/**
 * @brief evaluation function:
 *        non-const version
 * @param sh
 * @param lo
 * @return
 */
value_v expr::eval(const state_v& sh, const state_v& lo) {
	return static_cast<value_v>(static_cast<const expr&>(*this).eval(sh, lo));
}

}
/* namespace otf */
