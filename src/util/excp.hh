/**
 * @brief excp.hh
 *
 * @date   Jan 7, 2016
 * @author Peizun Liu
 */

#ifndef UTIL_EXCP_HH_
#define UTIL_EXCP_HH_

#include <exception>
#include <string>

using std::exception;
using std::runtime_error;
using std::string;

namespace ijit {

/**
 * @brief this is the customized exception class for our API
 */
class iotf_exception: public std::exception {
public:
	iotf_exception(const string& msg = "") :
			msg(msg) {
	}
	virtual ~iotf_exception() {
	}
	virtual const char* what() const noexcept {
		return msg.c_str();
	}
private:
	string msg;
};

/**
 * @brief this is the customized runtime_error for our API
 */
class iotf_runtime_error: public runtime_error {
public:
	iotf_runtime_error() :
			runtime_error("iotf runtime error") {
	}
	iotf_runtime_error(const string& msg = "iotf runtime error") :
			runtime_error(msg.c_str()) {
	}
	~iotf_runtime_error() {
	}
};

} /* namespace iotf */

#endif /* UTIL_EXCP_HH_ */
