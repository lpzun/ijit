/**
 * @brief tst_fws.hh
 *
 * @date  : Mar 8, 2016
 * @author: lpzun
 */

#ifndef TST_FWS_HH_
#define TST_FWS_HH_

/// Place 0: include the header and namespace
#include "../src/iotf.hh"
using namespace iotf;

namespace fws {

using state = prog_state;
using thread_state= prog_thread;
using antichain = deque<state>;

class FWS {
public:
    FWS();
    ~FWS();

    bool standard_FWS(const size_tc& n, const string& filename);
    bool onthefly_FWS(const size_tc& n, const string& filename);

private:
    deque<thread_state> initl_TS;
    deque<thread_state> final_TS;
    bool is_maximal(const state& s, const antichain& explored);
    void maximize(const state& s, antichain& worklist);

    bool is_reached(const state& s);
    bool is_covered(const state& s1, const state& s2);

};

} /* namespace fws */

#endif /* TST_FWS_HH_ */
