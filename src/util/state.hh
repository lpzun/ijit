/**
 * @brief  state.hh: defines the following data structure:
 *         value_v     : the value of  variable in Boolean programs
 *         sbool       : symbolic value of a variable used in Boolean program: {F, T, N}
 *         state_v     : vector<bool>
 *         size_pc     : the domain of pc
 *         size_tc     : the domain of thread counts;
 *         shared_state: shared state, a valuation for shared variables
 *         local_state : local state,  a valuation for local  variables
 *         thread_state: a combination of shared and local states
 *         cab_locals  : map<local_state, size_tc>, represented in counter abstraction
 *         global_state: a global configuration stored in counter abstraction form
 *
 * @date   Nov 13, 2015
 * @author Peizun Liu
 */

#ifndef UTIL_STATE_HH_
#define UTIL_STATE_HH_

#include "head.hh"
#include "refs.hh"

namespace ijit {

template<std::size_t N>
bool operator <(const std::bitset<N>& x, const std::bitset<N>& y) {
	DBG_LOC()
	for (int i = N - 1; i >= 0; i--) {
		if (x[i] ^ y[i])
			return y[i];
	}
	return false;
}

template<std::size_t N>
bool operator ==(const std::bitset<N>& x, const std::bitset<N>& y) {
	DBG_LOC()
	for (int i = N - 1; i >= 0; i--) {
		if (x[i] ^ y[i])
			return false;
	}
	return true;
}

/// define the data structure to store the valuation for
/// shared/local variables in Boolean programs
using state_v = bitset<SIZE_B>;

/// define the data structure to store program counter (pc);
using size_pc = unsigned short;

/// define the data structure to store the thread count
using size_tc = unsigned short;

/// define the symbols of Boolean expression
/// it includes operator and operand
using symbol = short;

/**
 * @brief sool = symbolic boolean variables
 */
enum class sool {
	F = 0, T = 1, N = 2
};

inline sool operator !(const sool& v) {
	if (v == sool::F)
		return sool::T;
	if (v == sool::T)
		return sool::F;
	return sool::N;
}

/**
 * @brief sbool AND operator & The truth table is as follows:
 *			v1:	 F		F		T		N		F		T		T		N		N
 *			v2:	 F		T		F		F		N		T		N		T		N
 *			re:	 F		F		F		F		F		T		N		N		N
 * @param s1
 * @param s2
 * @return see above table
 */
inline sool operator &(const sool& v1, const sool& v2) {
	if (v1 == sool::F || v2 == sool::F)
		return sool::F;
	if (v1 == sool::T && v2 == sool::T)
		return sool::T;
	return sool::N;
}

/**
 * @brief symbol OR operator ||. The truth table is as follows:
 *			v1:	 F		F		T		N		F		T		T		N		N
 *			v2:	 F		T		F		F		N		T		N		T		N
 *			re:	 F		T		T		N		N		T		N		N		N
 * @param s1
 * @param s2
 * @return see above table
 */
inline sool operator |(const sool& s1, const sool& s2) {
	if (s1 == sool::N || s2 == sool::N)
		return sool::N;
	if (s1 == sool::F && s2 == sool::F)
		return sool::F;
	return sool::T;
}

/**
 * @brief overloading operator <<
 * @param out
 * @param s
 * @return output stream:
 *         print an edge in cfg
 */
inline ostream& operator <<(ostream& out, const sool& s) {
	switch (s) {
	case sool::F:
		out << 0;
		break;
	case sool::T:
		out << 1;
		break;
	case sool::N:
		out << 2;
		break;
	default:
		throw ijit_runtime_error("unknown value for Boolean variable");
		break;
	}
	return out;
}
/// define the value of variables in Boolean programs
using value_v = sool;

/// symbolic valuation for shared variables
using symbval = vector<sool>;

/**
 * @brief define data structure shared state
 * 		  vars  to store valuation for shared variables
 */
class shared_state {
public:
	shared_state();
	shared_state(const state_v& vars);
	shared_state(const uint v);
	~shared_state();

	const state_v& get_vars() const {
		return vars;
	}

	void set_vars(const state_v& vars) {
		this->vars = vars;
	}

private:
	state_v vars;

	friend ostream& operator <<(ostream& out, const shared_state& s);
};

/**
 * @brief overloading operator <
 *
 * @note  the comparison over two vector<bool>s are the the corresponding
 *        two numbers encoding from the bits: the most significant is the
 *        left-most bit, e.g.,
 *        	{1,0,0,0} = 8          {0,0,0,1} = 1
 *
 * @param s1
 * @param s2
 * @return bool
 *         true : if s1 < s2
 *         false: otherwise
 */
inline bool operator <(const shared_state& s1, const shared_state& s2) {
	for (int i = refs::SV_NUM - 1; i >= 0; i--)
		if (s1.get_vars()[i] ^ s2.get_vars()[i])
			return s2.get_vars()[i];
	return false;
}

/**
 * @brief overloading operator >
 * @param s1
 * @param s2
 * @return bool
 *         true : if s1 > s2
 *         false: otherwise
 */
inline bool operator >(const shared_state& s1, const shared_state& s2) {
	return s2 < s1;
}

/**
 * @brief overloading operator ==
 * @param s1
 * @param s2
 * @return bool
 *         true : if s1 == s2
 *         false: otherwise
 */
inline bool operator ==(const shared_state& s1, const shared_state& s2) {
	for (int i = refs::SV_NUM - 1; i >= 0; i--)
		if (s1.get_vars()[i] ^ s2.get_vars()[i])
			return false;
	return true;
}

/**
 * @brief overloading operator !=
 * @param s1
 * @param s2
 * @return bool
 *         true : if s1 != s2
 *         false: otherwise
 */
inline bool operator !=(const shared_state& s1, const shared_state& s2) {
	return !(s1 == s2);
}

/**
 * @brief define data structure local state
 *        pc    to store the program counter
 * 		  vats  to store the valuation for local variables
 */
class local_state {
public:
	local_state();
	local_state(const size_pc& pc, const state_v& vars);
	local_state(const size_pc& pc, const uint v);
	~local_state();

	size_pc get_pc() const {
		return pc;
	}

	void set_pc(const size_pc& pc) {
		this->pc = pc;
	}

	const state_v& get_vars() const {
		return vars;
	}

	void set_vars(const state_v& vars) {
		this->vars = vars;
	}

private:
	size_pc pc;
	state_v vars;

	friend ostream& operator <<(ostream& out, const local_state& l);
};

/**
 * @brief overloading operator <
 *
 * @note  the comparison over two vector<bool>s are the the corresponding
 *        two numbers encoding from the bits: the most significant is the
 *        left-most bit, e.g.,
 *        	{1,0,0,0} = 8          {0,0,0,1} = 1
 * @param l1
 * @param l2
 * @return bool
 *         true : if l1 < l2
 *         false: otherwise
 */
inline bool operator <(const local_state& l1, const local_state& l2) {
	if (l1.get_pc() == l2.get_pc()) {
		for (int i = refs::LV_NUM - 1; i >= 0; i--)
			if (l1.get_vars()[i] ^ l2.get_vars()[i])
				return l2.get_vars()[i];
		return false;
	}
	return l1.get_pc() < l2.get_pc();
}

/**
 * @brief overloading operator >
 * @param l1
 * @param l2
 * @return bool
 *         true : if l1 > l2
 *         false: otherwise
 */
inline bool operator >(const local_state& l1, const local_state& l2) {
	return l2 < l1;
}

/**
 * @brief overloading operator ==
 * @param l1
 * @param l2
 * @return bool
 *         true : if l1 == l2
 *         false: otherwise
 */
inline bool operator ==(const local_state& l1, const local_state& l2) {
	if (l1.get_pc() == l2.get_pc()) {
		for (int i = refs::LV_NUM - 1; i >= 0; i--)
			if (l1.get_vars()[i] ^ l2.get_vars()[i])
				return false;
		return true;
	}
	return false;
}

/**
 * @brief overloading operator !=
 * @param l1
 * @param l2
 * @return bool
 *         true : if l1 != l2
 *         false: otherwise
 */
inline bool operator !=(const local_state& l1, const local_state& l2) {
	return !(l1 == l2);
}

/**
 * @brief define data structure thread state
 *        s:  to store the shared state
 * 		  l:  to store the local  state
 */
class thread_state {
public:
	thread_state();
	thread_state(const shared_state& s, const local_state& l);
	thread_state(const state_v& sv, const size_pc& pc, const state_v& lv);
	thread_state(const thread_state& t);
	~thread_state();

	const local_state& get_l() const {
		return l;
	}

	void set_local(const local_state& l) {
		this->l = l;
	}

	const shared_state& get_s() const {
		return s;
	}

	void set_s(const shared_state& s) {
		this->s = s;
	}

private:
	shared_state s;
	local_state l;

	friend ostream& operator <<(ostream& out, const thread_state& t);
};

/**
 * @brief overloading operator <
 * @param t1
 * @param t2
 * @return bool
 *         true : if t1 < t2
 *         false: otherwise
 */
inline bool operator <(const thread_state& t1, const thread_state& t2) {
	if (t1.get_s() == t2.get_s())
		return t1.get_l() < t2.get_l();
	return t1.get_s() < t2.get_s();
}

/**
 * @brief overloading operator >
 * @param t1
 * @param t2
 * @return bool
 *         true : if t1 > t2
 *         false: otherwise
 */
inline bool operator >(const thread_state& t1, const thread_state& t2) {
	return t2 < t1;
}

/**
 * @brief overloading operator ==
 * @param t1
 * @param t2
 * @return bool
 *         true : if t1 == t2
 *         false: otherwise
 */
inline bool operator ==(const thread_state& t1, const thread_state& t2) {
	return t1.get_s() == t2.get_s() && t1.get_l() == t2.get_l();
}

/**
 * @brief overloading operator !=
 * @param t1
 * @param t2
 * @return bool
 *         true : if t1 != t2
 *         false: otherwise
 */
inline bool operator !=(const thread_state& t1, const thread_state& t2) {
	return !(t1 == t2);
}

/**
 * @brief define the date structure to store LOCAL stateS that
 *        are represented in Counter ABstraction.
 * @note  A thing we have to keep in mind is that: when we use
 *        counter abstraction, we always assume that the system
 *        is symmetric: the ordering of thread does not matter.
 *        We might extend this to the a symmetric system in the future.
 */
using ca_locals = map<local_state, size_tc>;

/**
 * @brief define data structure global state
 *        s: to store the shared state
 * 		  locals: to store the local states that in counter abstraction
 * 		  representation
 */
class global_state {
public:
	global_state();
	global_state(const shared_state& s, const local_state& l);
	global_state(const shared_state& s, const local_state& l, const size_tc& n);
	global_state(const shared_state& s, const ca_locals& locals);
	global_state(const global_state& g);
	~global_state();

	const ca_locals& get_locals() const {
		return locals;
	}

	void set_locals(const ca_locals& locals) {
		this->locals = locals;
	}

	const shared_state& get_s() const {
		return s;
	}

	void set_s(const shared_state& s) {
		this->s = s;
	}

private:
	shared_state s;
	ca_locals locals;

	friend ostream& operator <<(ostream& out, const global_state& g);
};

/**
 * @brief overloading operator <
 * @note  TODO: When I overloaded this definition, I used the standard
 *        relational operations for map in c++ STL. This is might not
 *        100 percent fit the situation we faced here: wqo and so on.
 *        I have to rethink this in the future design.
 * @param g1
 * @param g2
 * @return bool
 *         true : if g1 < g2
 *         false: otherwise
 */
inline bool operator <(const global_state& g1, const global_state& g2) {
	if (g1.get_s() == g2.get_s()) {
		if (g1.get_locals().size() == g2.get_locals().size())
			return g1.get_locals() < g2.get_locals();
		return g1.get_locals().size() < g2.get_locals().size();
	}
	return g1.get_s() < g2.get_s();
}

/**
 * @brief overloading operator >
 * @param g1
 * @param g2
 * @return bool
 *         true : if g1 > g2
 *         false: otherwise
 */
inline bool operator >(const global_state& g1, const global_state& g2) {
	return g2 < g1;
}

/**
 * @brief overloading operator ==
 * @note  Please be careful this definition
 * @param g1
 * @param g2
 * @return bool
 *         true : if g1 == g2
 *         false: otherwise
 */
inline bool operator ==(const global_state& g1, const global_state& g2) {
	if (g1.get_s() == g2.get_s()) {
		const auto& locals1 = g1.get_locals();
		const auto& locals2 = g2.get_locals();
		return locals1.size() == locals2.size()
				&& std::equal(locals1.begin(), locals1.end(), locals2.begin());
	}
	return false;
}

/**
 * @brief overloading operator !=
 * @param g1
 * @param g2
 * @return bool
 *         true : if g1 != g2
 *         false: otherwise
 */
inline bool operator !=(const global_state& g1, const global_state& g2) {
	return !(g1 == g2);
}

} /* namespace iotf */
#endif /* UTIL_STATE_HH_ */
