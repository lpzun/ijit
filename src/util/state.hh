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

namespace iotf {

/// define the value of variables in Boolean programs
using value_v = bool;

/// define the data structure to store the valuation for
/// shared/local variables in Boolean programs
using state_v = vector<bool>;

/// define the data structure to store program counter (pc);
using size_pc = unsigned short;

/// define the data structure to store the thread count
using size_tc = unsigned short;

enum class sbool {
	F = 0, T = 1, N = 2
};

inline sbool operator !(const sbool& v) {
	if (v == sbool::F)
		return sbool::T;
	if (v == sbool::T)
		return sbool::F;
	return sbool::N;
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
inline sbool operator &(const sbool& v1, const sbool& v2) {
	if (v1 == sbool::F || v2 == sbool::F)
		return sbool::F;
	if (v1 == sbool::T && v2 == sbool::T)
		return sbool::T;
	return sbool::N;
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
inline sbool operator |(const sbool& s1, const sbool& s2) {
	if (s1 == sbool::N || s2 == sbool::N)
		return sbool::N;
	if (s1 == sbool::F && s2 == sbool::F)
		return sbool::F;
	return sbool::T;
}

/**
 * @brief define data structure shared state
 * 		  vars  to store valuation for shared variables
 */
class shared_state {
public:
	shared_state();
	shared_state(const state_v& vars);
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
	return s1.get_vars() < s2.get_vars();
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
	return s1.get_vars() == s2.get_vars();
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
		return l1.get_vars() < l2.get_vars();
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
	return l1.get_pc() == l2.get_pc() && l1.get_vars() == l2.get_vars();
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
using cab_locals = map<local_state, size_tc>;

/**
 * @brief define data structure global state
 *        s: to store the shared state
 * 		  locals: to store the local states that in counter abstraction
 * 		  representation
 */
class global_state {
public:
	global_state();
	global_state(const shared_state& s, const cab_locals& locals);
	global_state(const global_state& g);
	~global_state();

	const cab_locals& get_locals() const {
		return locals;
	}

	void set_locals(const cab_locals& locals) {
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
	cab_locals locals;

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
