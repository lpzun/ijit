/**
 * @brief prop.cc: it serves as a supporting source file to store all other
 *        class declared in the header image.hh, like
 *        class parser and converter (the default implementations for virtual
 *        functions)
 *        Q: Why I named it as prop.cc?
 *        A: Because I think this file defines the common properties of the
 *        entire API. That's it!
 *
 * @date   Dec 26, 2015
 * @author Peizun Liu
 */

#include "../iotf.hh"

/// declare yyin to let parser read from file
/// NOTE: this is not an elegant way to do this
extern FILE * yyin;

namespace iotf {

/**
 * @brief override operator << for system state
 * @param out
 * @param s
 * @return ostream
 */
ostream& operator <<(ostream& out, const syst_state& s) {
    out << "<" << s.first << "|";
    for (const auto& p : s.second) {
        out << "(" << p.first << "," << p.second << ")";
    }
    return out;
}

/**
 * @brief override operator << for system thread state
 * @param out
 * @param s
 * @return ostream
 */
ostream& operator <<(ostream& out, const syst_thread& s) {
    out << "(" << s.first << "," << s.second << ")";
    return out;

}

cfg parser::prev_G; /// control flow graph in PREV mode
cfg parser::post_G; /// control flow graph in POST mode

/**
 * @brief default constructor
 */
parser::parser() {

}

/**
 * @brief default  destructor
 */
parser::~parser() {

}

/**
 * @brief parse Boolean programs based on the mode (preimage or postimage)
 * @param filename: Boolean program
 * @param m       : mode
 */
pair<deque<prog_thread>, deque<prog_thread>> parser::parse(
        const string& filename, const mode& m) {
    if (m == mode::PREV) {
        return parse_in_prev_mode(filename);
    } else if (m == mode::POST) {
        return parse_in_post_mode(filename);
    } else {
        throw iotf_runtime_error("there is no such mode!");
    }
}

/**
 * @brief parse Boolean programs in  preimage mode
 * @param filename
 */
pair<deque<prog_thread>, deque<prog_thread>> parser::parse_in_prev_mode(
        const string& filename) {
    paide aide;
    const auto& I = create_initl_state(aide.l_vars_init, aide.s_vars_init);
    const auto& Q = create_final_state(aide.asse_pc_set);
    return std::make_pair(I, Q);
}

/**
 * @brief parse Boolean programs in postimage mode
 * @param filename
 */
pair<deque<prog_thread>, deque<prog_thread>> parser::parse_in_post_mode(
        const string& filename) {
    FILE *bfile = fopen(filename.c_str(), "r");
    if (!bfile) {
        throw iotf_runtime_error(filename + " open failed!");
    }

    yyin = bfile;

    cout << "starting to parse Boolean program...\n";
    paide aide;
    yy::bp parser(aide); /// build a parser
    int result = parser.parse(); /// and run it
    if (result != 0) {
        throw iotf_runtime_error(
                "Parser exit with exception: " + std::to_string(result));
    }

    /// move the file point to the begin and print the total line number
    cout << "shared, local, line\n";
    refs::SV_NUM = aide.s_vars_num;
    refs::LV_NUM = aide.l_vars_num;
    refs::PC_NUM = aide.lineno;
    cout << refs::SV_NUM << "," << refs::LV_NUM << "," << aide.lineno << "\n";
#ifndef NDEBUG
    DBG_LOG("for testing: before...\n")
    aide.print_control_flow_graph();
#endif
    post_G = aide.cfg_G;
#ifndef NDEBUG
    DBG_LOG("for testing: after...\n")
    cout << post_G << endl;
#endif
    /// build the initial states
    const auto& I = create_initl_state(aide.s_vars_init, aide.l_vars_init);
    /// build the final   states
    const auto& Q = create_final_state(aide.asse_pc_set);
    return std::make_pair(I, Q);
}

/**
 * @brief compute initial states
 * @param s_vars_init
 * @param l_vars_init
 * @param pc
 * @return initial states
 */
deque<prog_thread> parser::create_initl_state(
        const map<ushort, sool>& s_vars_init,
        const map<ushort, sool>& l_vars_init, const size_pc& pc) {
#ifndef NDEBUG
    cout << "output initial values stored in maps...\n";
    cout << "(";
    for (const auto& p : s_vars_init)
    cout << p.second;
    cout << "|0";
    for (const auto& p : l_vars_init)
    cout << p.second;
    cout << ")\n";
#endif
    /// to store the initial program states
    deque<prog_thread> ips;

    /// step 1: build shared BV via splitting *
    deque<state_v> svs; /// store shared BV
    svs.emplace_back(state_v(0));
    for (const auto& p : s_vars_init) {
        alg::split(p.second, p.first - 1, svs);
    }

    /// step 2: build local  BV via splitting *
    deque<state_v> lvs; /// store local  BV
    lvs.emplace_back(state_v(0));
    for (const auto& p : l_vars_init) {
        alg::split(p.second, p.first - 1, lvs);
    }

    /// step 3: build global states via shared
    ///         BVs and local BVs
    for (const auto& sv : svs) {
        for (const auto& lv : lvs) {
            ips.emplace_back(sv, pc, lv);
        }
    }

#ifndef NDEBUG
    cout << __func__ << "\n";
    for (const auto& g : ips)
    cout << g << endl;
#endif

    return ips;
}

/**
 * @brief generate all final states for all assertions collected
 *        by their PCs
 * @param pcs
 * @return the list of final states
 */
deque<prog_thread> parser::create_final_state(const set<size_pc>& pcs) {
    deque<prog_thread> fps;
    for (const auto& pc : pcs) {
        parser::create_final_state(pc, fps);
    }
#ifndef NDEBUG
    cout << __func__ << "\n";
    for (const auto& g : fps)
    cout << g << endl;
    cout << __func__ << "-----------------\n";
#endif
    return fps;
}

/**
 * @brief generate all final states for all assertions collected
 *        by a particular PC <pc>
 * @param pc  : the particular pc
 * @param fps : the deque to store final program state
 */
void parser::create_final_state(const size_pc& pc, deque<prog_thread>& fps) {
    const auto& predecessors = parser::get_post_G().get_A()[pc];
    const auto& e = predecessors.front();
    if (e.get_stmt().get_type() == type_stmt::ASSE) {
        const auto& expressions = e.get_stmt().get_condition().get_splited();
        for (const auto& exp : expressions) {
            const auto& assgs = solver::all_sat_solve(exp);
            for (const auto& assg : assgs) {
                /// step 1: build shared BV via splitting *
                deque<state_v> svs; /// store shared BV
                svs.emplace_back(state_v(0));
                for (auto i = 0; i < assg.first.size(); ++i) {
                    alg::split(assg.first[i], i, svs);
                }

                /// step 2: build local  BV via splitting *
                deque<state_v> lvs; /// store local  BV
                lvs.emplace_back(state_v(0));
                for (auto i = 0; i < assg.second.size(); ++i) {
                    alg::split(assg.second[i], i, lvs);
                }

                /// step 3: build global states via shared
                ///         BVs and local BVs
                for (const auto& sv : svs) {
                    for (const auto& lv : lvs) {
                        fps.emplace_back(sv, pc, lv);
                    }
                }
                /// complete the final state for a satisfiable assignment
            }
        }
    }
}

///////////////////////////////////////////////////////////////////////////////
/// from here: all member definitions of class converter                    ///
///////////////////////////////////////////////////////////////////////////////

/**
 * @brief convert a list of system states (user-form global state) to a list of
 *        program states (our otf-form global state)
 * @param ss: a list of system states
 * @return    a list of program states
 */
deque<prog_state> converter::convert(const deque<syst_state>& ss) {
    deque<prog_state> ps;
    for (const auto& s : ss)
        ps.emplace_back(this->convert(s));
    return ps;
}

/**
 * @brief convert a list of program states (user-form global state) to a list of
 *        system states (our otf-form global state)
 * @param ss: a list of program states
 * @return    a list of system states
 */
deque<syst_state> converter::convert(const deque<prog_state>& ps) {
    deque<syst_state> ss;
    for (const auto& p : ps)
        ss.emplace_back(this->convert(p));
    return ss;
}

/**
 * @brief convert a system state (user-form global state) to a program state
 *        (our otf-form global state)
 * @param s
 * @param Z
 * @return a program state
 */
prog_state converter::convert(const syst_state& ss) {
    const auto& sps = this->convert_sss_to_sps(ss.first);
    ca_locals Z; /// build local parts
    for (const auto& p : ss.second) {
        const auto& l = this->convert_lss_to_lps(p.first);
        Z.emplace(local_state(l.first, l.second), p.second);
    }
    return global_state(shared_state(sps), Z);
}

/**
 * @brief convert a program state (our otf-form global state) to a system state
 *        (user-form global state)
 * @param gs
 * @return a pair
 */
syst_state converter::convert(const prog_state& ps) {
    const auto& sss = this->convert_sps_to_sss(ps.get_s().get_vars());
    map<uint, uint> Z;
    for (const auto p : ps.get_locals()) {
        const auto& l = p.first;
        const auto& sls = this->convert_lps_to_lss(l.get_pc(), l.get_vars());
        Z.emplace(sls, p.second);
    }
    return std::make_pair(sss, Z);
}

/**
 * @brief This function is to convert program thread state to a system state
 *
 * @param ss: program thread state
 *
 * @return system thread state
 */
syst_thread converter::convert(const prog_thread& pts) {
    const auto& sts = this->convert_sps_to_sss(pts.get_s().get_vars());
    const auto& stl = this->convert_lps_to_lss(pts.get_l().get_pc(),
            pts.get_l().get_vars());
    return std::make_pair(sts, stl);
}

/**
 * @brief This function is to convert a system thread state to a program thread state
 *
 * @param ss: system thread state
 *
 * @return program thread state
 */
prog_thread converter::convert(const syst_thread& sts) {
    const auto& sv = this->convert_sss_to_sps(sts.first);
    const auto& p = this->convert_lss_to_lps(sts.second);
    return thread_state(sv, p.first, p.second);
}

/**
 * @brief convert a shared system state to a shared program state
 * @param ss
 * @return a shared program state
 */
state_v converter::convert_sss_to_sps(const uint& ss) {
    return state_v(ss);
}

/**
 * @brief to convert a shared program state to a shared system state
 * @param ps
 * @return a shared system state
 */
uint converter::convert_sps_to_sss(const state_v& ps) {
    return ps.to_ulong();
}

/**
 * @brief to convert a local system state to local program state
 *      low pc              local             high
 *           ________________ _______________
 *          |________________|_______________|
 *
 * @param ss
 * @return a pair (pc, state_v)
 */
pair<size_pc, state_v> converter::convert_lss_to_lps(const uint& ss) {
    size_pc pc = ss & mask;
    state_v lv(ss >> SIZE_B / 2);
    return std::make_pair(pc, lv);
}

/**
 * @brief to convert a pair (pc, state_v) to a local program state
 * @param pc
 * @param ps
 * @return a local system state
 */
uint converter::convert_lps_to_lss(const size_pc& pc, const state_v& ps) {
    auto lv = (ps << (SIZE_B / 2)).to_ullong();
    return lv ^ pc;
}

} /* namespace otf */
