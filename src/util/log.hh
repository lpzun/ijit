/**
 * @brief log.hh: this file defines debugger, the logger and so on.
 *
 * @date  : Jan 7, 2016
 * @author: Peizun Liu
 */

#ifndef UTIL_LOG_HH_
#define UTIL_LOG_HH_

namespace iotf {

// #define NDEBUG

#ifndef NDEBUG
#  define DBG_LOG(x) std::cerr << x <<"\n";
#  define DBG_STD(x) x;
#  define DBG_LOC() std::cerr \
        <<__func__<<": I am here ..."<<"\n";
#else
#  define DBG_LOG(x)
#  define DBG_STD(x)
#  define DBG_LOC();
#endif

/**
 * @brief define the debugger level
 *
 * LOG_FATAL  : severe errors that require program exit
 * LOG_ERROR  : error messages that can't be recovered from but the program
 *              can continue to run.
 * LOG_WARNING: recoverable problem that you should be notified about.
 * LOG_INFO   : informational messages.
 * LOG_ENTRY  : log entry and exit to all functions.
 * LOG_PARM   : log entry and exit to all functions with parameters passed and
 *              values returned.
 * LOG_DEBUG  : general debugging messages, basically useful information that
 *              can be output on a single line.
 */
enum class log_mode {
	LOG_FATAL, LOG_ERROR, LOG_WARNING, LOG_INFO, LOG_ENTRY, LOG_PARM, LOG_DEBUG
};

class logger {
public:
	inline logger();
	inline ~logger();
	inline void logging(const std::string& msg);
private:
	log_mode level;
};

inline logger::logger() :
		level(log_mode::LOG_INFO) {

}
inline logger::~logger() {

}

/**
 * @brief define a logger that print out the log
 * @param msg
 */
inline void logger::logging(const std::string& msg) {
	switch (this->level) {
	case log_mode::LOG_INFO:
		std::cout << msg << std::endl;
		break;
	default:
		return;
	}
}

} /* namespace iotf */

#endif /* UTIL_LOG_HH_ */
