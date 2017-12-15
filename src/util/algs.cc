/**
 * @brief algs.cc
 *
 * @date   Nov 17, 2015
 * @author Peizun Liu
 */

#include "algs.hh"

namespace ijit {
/**
 * @brief This function is used to increment/decrement the counters for all
 * 		  local states in T_in/T_de.
 * @param t_in
 * @param t_de
 * @param Z
 * @return local states, represented in counter abstraction form
 */
ca_locals alg::update_counters(const local_state& t_in, const local_state& t_de,
		const ca_locals& Z) {
	if (t_in == t_de)
		return Z;

	auto _Z = Z;

	auto ide = _Z.find(t_de);
	if (ide != _Z.end()) {
		ide->second -= 1;
		if (ide->second == 0)
			_Z.erase(ide);
	}

	auto iin = _Z.find(t_in);
	if (iin != _Z.end()) {
		iin->second += 1;
	} else {
		_Z.emplace(t_in, 1);
	}

	return _Z;
}

/**
 * @brief increment the counter of t_in by one
 * @param t_in
 * @param Z
 */
void alg::increment(const local_state& t_in, ca_locals& Z) {
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
void alg::decrement(const local_state& t_de, ca_locals& Z) {
	auto ifind = Z.find(t_de);
	if (ifind != Z.end()) {
		ifind->second -= 1;
		if (ifind->second == 0)
			Z.erase(ifind);
	} else {
		cerr << __func__ << " " << t_de;
		throw ijit_runtime_error(" unfounded!");
	}
}

/**
 * @brief update counters for normal transitions with acceleration
 * @param t_in
 * @param t_de
 * @param Z
 * @param same if the shared states are same
 * @return local state part
 */
ca_locals alg::update_counter(const local_state& t_in, const local_state& t_de,
		const ca_locals& Z, const bool& same) {
	if (t_in == t_de)
		return Z;

	auto _Z = Z;
	/// step 1: update or eliminate the pair for the decremental local state
	///         skip update if its counter is w as w - 1 = w
	auto ide = _Z.find(t_in);
	if (ide != _Z.end() && ide->second != refs::omega) {
		ide->second -= 1;
		if (ide->second == 0) /// remove it if a counter ever becomes zero
			_Z.erase(ide);
	}

	/// step 2: update or add pair for the incremental local state
	auto iin = _Z.find(t_de);
	if (iin != _Z.end()) {
		if (iin->second != refs::omega) {
			if (ide->second == refs::omega && same) {
				/// add with w if transition can be re-taken
				iin->second = refs::omega;
			} else {
				/// otherwise, plus one
				iin->second += 1;
			}
		} /// skip its update if the counter is w as w + 1 = w
	} else if (ide->second == refs::omega && same) {
		/// add with w if transition can be re-taken
		_Z.emplace(t_de, refs::omega);
	} else {
		/// create a new pair if exists no such pair in previous
		_Z.emplace(t_de, 1);
	}

	return _Z;
}

/**
 * @brief increment the counter of t_in by one
 * @param t_in
 * @param Z
 */
void alg::increment(const local_state& t_in, ca_locals& Z, const bool& same) {
	auto ifind = Z.find(t_in);
	if (ifind != Z.end()) {
		if (ifind->second != refs::omega) {
			if (same)
				ifind->second = refs::omega;
			else
				ifind->second += 1;
		}
	} else {
		Z.emplace(t_in, 1);
	}
}

/**
 * @brief decrement the counter of t_de by one
 * @param t_de
 * @param Z
 */
void alg::decrement(const local_state& t_de, ca_locals& Z, const bool& same) {
	auto ifind = Z.find(t_de);
	if (ifind != Z.end()) {
		if (ifind->second != refs::omega) {
			ifind->second -= 1;
			if (ifind->second == 0)
				Z.erase(ifind);
		}
	} else {
		throw ijit_runtime_error(std::string(__func__) + ": t_de unfounded!");
	}
}

/**
 * @brief split nondeterministic value into false and true
 * @param v
 * @param i
 * @param svs
 */
void alg::split(const sool& v, const size_t& i, deque<state_v>& svs) {
	switch (v) {
	case sool::F:
		for (auto& sv : svs) {
			sv[i] = 0;
		}
		break;
	case sool::T:
		for (auto& sv : svs) {
			sv[i] = 1;
		}
		break;
	default:
		for (auto& sv : svs) {
			sv[i] = 0;
			auto cp(sv); /// build a copy of sv
			cp[i] = 1;
			svs.emplace_back(cp);
		}
		break;
	}
}

/**
 * @brief to restore the expression
 * @param symb_list
 * @param is_origi: this para is to generate the comments!!!!!!!
 * @return expression
 */
string solver::recov_expr_from_list(const deque<symbol>& sexpr) {
	stack<string> worklist;
	string op1, op2;
	for (const auto& ss : sexpr) {
		switch (ss) {
		case solver::AND:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 + " & " + op2);
			break;
		case solver::OR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 + " | " + op2);
			break;
		case solver::XOR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 + " ^ " + op2);
			break;
		case solver::EQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 + " = " + op2);
			break;
		case solver::NEQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 + " != " + op2);
			break;
		case solver::NEG:
			op1 = worklist.top(), worklist.pop();
			worklist.emplace("!" + op1);
			break;
		case solver::PAR:
			op1 = worklist.top(), worklist.pop();
			worklist.emplace("(" + op1 + ")");
			break;
		case solver::CONST_F:
			worklist.emplace("0");
			break;
		case solver::CONST_T:
			worklist.emplace("1");
			break;
		case solver::CONST_N:
			worklist.emplace("*");
			break;
		default:
			worklist.emplace(std::to_string(ss));
			break;
		}
	}
	return worklist.top();
}

///////////////////////////////////////////////////////////////////////////////
/// from here: class solver
///
///////////////////////////////////////////////////////////////////////////////

const short solver::CONST_F; /// constant false
const short solver::CONST_T; /// constant true
const short solver::CONST_N; /// constant nondeterminism
const short solver::NEG; /// !, negation
const short solver::AND; /// &, and
const short solver::OR;  /// |, or
const short solver::XOR; /// ^, exclusive or
const short solver::EQ;  /// =, equal
const short solver::NEQ; /// !=, not equal
const short solver::IMP; /// =>, implies
const short solver::PAR; /// parenthesis

solver::solver() {

}
solver::~solver() {

}

/**
 * @brief This is a customized "exhaustive" SAT solver, which can be used to
 *        extract targets from assertions in Boolean program. It's an
 *        exhaustive algorithm. I've no idea if we should use a more efficient
 *        SAT solver. It seems unnecessary due to that each assertion contains
 *        only very few boolean variables.
 * @param expr
 * @param s
 * @param l
 * @return a sat solver
 */
bool solver::solve(const deque<symbol>& sexpr, const state_v& s,
		const state_v& l) {
	stack<bool> worklist;
	bool op1, op2;
	for (const auto& ss : sexpr) {
		switch (ss) {
		case solver::AND:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 & op2);
			break;
		case solver::OR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 | op2);
			break;
		case solver::XOR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 ^ op2);
			break;
		case solver::EQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 == op2);
			break;
		case solver::NEQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 != op2);
			break;
		case solver::NEG:
			op1 = worklist.top(), worklist.pop();
			worklist.emplace(!op1);
			break;
		case solver::PAR:
			break;
		case solver::CONST_F:
			worklist.emplace(false);
			break;
		case solver::CONST_T:
			worklist.emplace(true);
			break;
		case solver::CONST_N:
			throw ijit_runtime_error(string(__func__) + ": * is not splitted");
			break;
		default: {
			bool is_shared = false;
			const auto& i = solver::decode(ss, is_shared);
			if (is_shared)
				worklist.push(s[i]);
			else
				worklist.push(l[i]);
		}
			break;
		}
	}
	return worklist.top();
}

/**
 * @brief This is a customized "exhaustive" SAT solver, which can be used to
 *        extract targets from assertions in Boolean program. It's an
 *        exhaustive algorithm. I've no idea if we should use a more efficient
 *        SAT solver. It seems unnecessary due to that each assertion contains
 *        only very few boolean variables.
 * @param sexpr
 * @param s
 * @param l
 * @param _s
 * @param _l
 * @return
 */
bool solver::solve(const deque<symbol>& sexpr, const state_v& s,
		const state_v& l, const state_v& _s, const state_v& _l) {
	stack<bool> worklist;
	bool op1, op2;
	for (const auto& ss : sexpr) {
		switch (ss) {
		case solver::AND:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 & op2);
			break;
		case solver::OR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 | op2);
			break;
		case solver::XOR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 ^ op2);
			break;
		case solver::EQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 == op2);
			break;
		case solver::NEQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 != op2);
			break;
		case solver::NEG:
			op1 = worklist.top(), worklist.pop();
			worklist.emplace(!op1);
			break;
		case solver::PAR:
			break;
		case solver::CONST_F:
			worklist.emplace(false);
			break;
		case solver::CONST_T:
			worklist.emplace(true);
			break;
		case solver::CONST_N:
			throw ijit_runtime_error(string(__func__) + ": * is not splitted");
			break;
		default: {
			bool is_shared = false, is_primed = false;
			const auto& i = solver::decode(ss, is_shared, is_primed);
			if (!is_primed) { /// normal variables
				if (is_shared)
					worklist.push(s[i]);
				else
					worklist.push(l[i]);
			} else { /// primed variables
				if (is_shared)
					worklist.push(_s[i]);
				else
					worklist.push(_l[i]);
			}
		}
			break;
		}
	}
	return worklist.top();
}

/**
 * @brief This is an all sat solver: it's an exhaustive one, so it's not
 *        very efficient.
 *        TODO: consider to call an off-the-shelf incremental SAT solver
 *
 * @param sexpr
 * @return all of the valuations that satisfy sexpr
 */
deque<pair<symbval, symbval>> solver::all_sat_solve(const deque<symbol>& sexpr,
		const symbval& s_vars, const symbval& l_vars) {

	DBG_STD(cout << __func__ << recov_expr_from_list(sexpr) << "\n";)

	deque<pair<symbval, symbval>> result;
	/// step 1: collect ids of free Boolean variables:
	///         this is a subset of all variables
	map<symbol, ushort> vfree_id;
	ushort vfree = 0; /// the number of free variables
	for (const auto& s : sexpr) {
		if (s > solver::CONST_N && vfree_id.emplace(s, vfree).second)
			++vfree;
	}

	/// CASE 1: if the expression does not involve any variable, then
	///   evaluate the expression, and based on the result:
	///   (1) true : all assignments satisfy the expression,
	///   (2) false: no assignment satisfies the expression.
	if (vfree == 0) {
		/// (3) split nondeterministic symbol * into 0 and 1
		const auto& expressions = solver::split(sexpr);
		for (const auto& expr : expressions)
			if (solver::eval(expr)) {	/// <expr> is true everywhere
				result.emplace_back(s_vars, l_vars);
				break;
			}
		return result;
	}

	DBG_STD(cout << __func__ << " " << vfree << endl;)
	/// CASE 2: otherwise, enumerate over all possible valuations
	///   of free Boolean variables
	for (auto assg = 0; assg < (1 << vfree); ++assg) {
		/// step 1: build an assignment to active variables
		const auto& bv = solver::to_binary(assg, vfree);
		symbval s_tmp(s_vars);
		symbval l_tmp(l_vars);
		auto se = sexpr;
		/// step 4: replace Boolean variables by its values
		for (auto i = 0; i < se.size(); ++i) {
			if (se[i] > solver::CONST_N) {
				auto ifind = vfree_id.find(se[i]);
				/// step 4.1: determine whether se[i] is shared or not
				bool is_shared = false;
				const auto& idx = solver::decode(se[i], is_shared);
				if (is_shared) {
					s_tmp[idx] = (bv[ifind->second] ? sool::T : sool::F);
				} else {
					l_tmp[idx] = (bv[ifind->second] ? sool::T : sool::F);
				}
				/// step 4.2: assign a Boolean value to variable se[i]
				se[i] = bv[ifind->second];
			}
		}

		/// (1) split nondeterministic symbol * into 0 and 1
		const auto& expressions = solver::split(se);
		for (const auto& expr : expressions) {
			/// step 5: evaluate the expression
			if (solver::eval(expr)) {
				result.emplace_back(s_tmp, l_tmp);
				break;
			}
		}
	}
#ifdef DEBUG
	cout<<__func__<<"\n";
	for (const auto& p : result) {
		for (const auto& s : p.first)
		cout << s;
		for (const auto& l : p.second)
		cout << l;
		cout << endl;
	}
#endif /* end debug */
	return result;
}

/**
 * @brief split * into 0 and 1 during expression evaluation
 * @param sexpr: a expression with *
 * @return a list of expressions after splitting * into 0 and 1
 */
deque<deque<symbol>> solver::split(const deque<symbol>& sexpr) {
	deque<deque<symbol>> worklist;
	worklist.emplace_back(sexpr);
	deque<deque<symbol>> splitted;
	for (auto i = 0; i < sexpr.size(); ++i) {
		if (sexpr[i] == solver::CONST_N) {
			while (!worklist.empty()) {
				auto e1 = worklist.front();
				worklist.pop_front();
				auto e2 = e1;

				e1[i] = solver::CONST_F;
				e2[i] = solver::CONST_T;

				splitted.emplace_back(e1);
				splitted.emplace_back(e2);
			}
			splitted.swap(worklist);
		}
	}
	return worklist;
}

/**
 * @brief do substitution:
 * @param sexpr:
 * @param var  :
 * @param ins  :
 */
void solver::substitute(deque<symbol>& sexpr, const symbol& var,
		const symbol& ins) {
	for (auto& s : sexpr) {
		if (s == var)
			s = ins;
	}
}

/**
 * @brief split * into 0 and 1 during expression evaluation
 * @param sexpr: a expression with *
 * @return a list of expressions after splitting * into 0 and 1
 */
deque<deque<sool>> solver::split(const deque<sool>& vsool) {
	deque<deque<sool>> worklist;
	worklist.emplace_back(vsool);
	deque<deque<sool>> splitted;
	for (auto i = 0; i < vsool.size(); ++i) {
		if (vsool[i] == sool::N) {
			while (!worklist.empty()) {
				auto v1 = worklist.front();
				worklist.pop_front();
				auto v2 = v1;

				v1[i] = sool::F;
				v2[i] = sool::T;

				splitted.emplace_back(v1);
				splitted.emplace_back(v2);
			}
			splitted.swap(worklist);
		}
	}
	return worklist;
}

symbol solver::encode(const symbol& idx, const bool& is_shared) {
	if (is_shared)
		return idx + 3;
	else
		return idx + 3 + refs::SV_NUM;
}

/**
 * @brief decode
 * @param idx
 * @param is_shared
 */
symbol solver::decode(const symbol& idx, bool& is_shared) {
	auto id = idx - 3;
	is_shared = true;
	if (id >= refs::SV_NUM)
		is_shared = false, id -= refs::SV_NUM;
	return id;
}

/**
 * @brief decode
 * @param idx
 * @param is_shared
 * @param is_primed
 */
symbol solver::decode(const symbol& idx, bool& is_shared, bool& is_primed) {
	auto id = idx - 3;
	if (id < refs::SV_NUM + refs::LV_NUM) {
		is_primed = false, is_shared = true;
		if (id >= refs::SV_NUM)
			is_shared = false, id -= refs::SV_NUM;
	} else {
		is_primed = true, is_shared = true;
		if (id >= 2 * refs::SV_NUM + refs::LV_NUM)
			is_shared = false, id -= refs::SV_NUM;
		id = id - refs::SV_NUM - refs::LV_NUM;
	}
	return id;
}

/**
 * @brief convert a unsigned to a binary representation
 * @param n
 * @param bits
 * @return a binary stored in vector<bool>
 */
vector<bool> solver::to_binary(const int& n, const short& shift) {
	auto num = n;
	vector<bool> bv(shift);
	for (auto i = 0; i < shift; ++i) {
		int b = (num >> i) & 1;
		bv[i] = b == 1 ? 1 : 0;
	}
	return bv;
}

/**
 * @brief to computer power(base, exponent)
 * @param base
 * @param bits
 * @return
 */
int solver::power(const int& base, const int& exponent) {
	auto shift = exponent;
	int result = 1;
	while (shift-- > 0) {
		result *= base;
	}
	return result;
}

/**
 * @brief to evaluate a Boolean expression whose variables have
 *        already been replaced by their valuations.
 * @param sexpr: a Boolean expression
 * @return evaluation result: true or false
 */
bool solver::eval(const deque<symbol>& sexpr) {
	stack<bool> worklist;
	bool op1, op2;
	for (const auto& ss : sexpr) {
		switch (ss) {
		case solver::AND:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 & op2);
			break;
		case solver::OR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 | op2);
			break;
		case solver::XOR:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 ^ op2);
			break;
		case solver::EQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 == op2);
			break;
		case solver::NEQ:
			op1 = worklist.top(), worklist.pop();
			op2 = worklist.top(), worklist.pop();
			worklist.emplace(op1 != op2);
			break;
		case solver::NEG:
			op1 = worklist.top(), worklist.pop();
			worklist.emplace(!op1);
			break;
		case solver::PAR:
			break;
		case solver::CONST_F:
			worklist.emplace(false);
			break;
		case solver::CONST_T:
			worklist.emplace(true);
			break;
		case solver::CONST_N:
			throw ijit_runtime_error(string(__func__) + ": * is not splitted");
			break;
		default:
			throw("A variable appears in solver::eval()");
			break;
		}
	}
	if (worklist.empty())
		return false;
	return worklist.top();
}

} /* namespace otf */
