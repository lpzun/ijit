/**
 * @brief tst_fws.hh
 *
 * @date  : Mar 8, 2016
 * @author: lpzun
 */

#ifndef TST_FWS_HH_
#define TST_FWS_HH_

#include "../src/iotf.hh"

namespace iotf {

using state = prog_state;
using antichain = deque<state>;

class FWS {
public:
    FWS();
    ~FWS();

    bool standard_FWS(const size_tc& n, const string& filename);

private:
    deque<state> initl_TS;
    deque<state> final_TS;
    bool is_maximal(const global_state& s, const antichain& explored);
    void maximize(const global_state& s, antichain& worklist);

    bool is_reached(const global_state& s);
    bool is_covered(const global_state& s1, const global_state& s2);

};

} /* namespace iotf */

#endif /* TST_FWS_HH_ */
