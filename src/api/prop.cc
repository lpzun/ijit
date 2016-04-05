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
    /// step 0: set an istream point to a Boolean program
    FILE *bfile = fopen(filename.c_str(), "r");
    if (!bfile) {
        throw iotf_runtime_error(filename + " open failed!");
    }
    /// step 1: set the input stream of the parser as bfile
    yyin = bfile;

    cout << "starting to parse Boolean program...\n";
    /// step 2: instantiate a parser aide
    paide aide(m);
    /// step 3: instantiate a parser
    yy::bp parser(aide);
    /// step 4: run the parser to parse the input BP
    int result = parser.parse();
    if (result != 0) {
        throw iotf_runtime_error(
                "Parser exit with exception: " + std::to_string(result));
    }

    /// step 5: output the parsing result...
    cout << "shared, local, line\n";
    refs::SV_NUM = aide.s_vars_num;
    refs::LV_NUM = aide.l_vars_num;
    refs::PC_NUM = aide.lineno;
    cout << refs::SV_NUM << "," << refs::LV_NUM << "," << refs::PC_NUM << "\n";
#ifdef NDEBUG
    DBG_LOG("for testing: before...\n")
    aide.print_control_flow_graph();
#endif

    /// step 6: setup the CFG in term of the parser's mode
    if (m == mode::PREV) {
        prev_G = aide.cfg_G;
    } else if (m == mode::POST) {
        post_G = aide.cfg_G;
    } else {
        throw iotf_runtime_error("there is no such mode!");
    }

#ifdef NDEBUG
    DBG_LOG("for testing: after...\n")
    if (m == mode::PREV)
        cout << prev_G << "\n";
    else if (m == mode::POST)
        cout << post_G << "\n";
#endif

    /// step 7: setup the initial and final states from the parser: this
    ///         step has nothing to do with mode
    /// build the initial states
    const auto& I = create_initl_state(aide.s_vars_init, aide.l_vars_init);

    /// build the final   states
    const auto& Q = create_final_state(m, aide.asse_pc_set);

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
 * @param m  : the forward or backward mode
 * @param pcs: the list of PCs associating with assertions
 * @return the deque of final states
 */
deque<prog_thread> parser::create_final_state(const mode& m,
        const set<size_pc>& pcs) {
    deque<prog_thread> fps;
    if (m == mode::PREV) {
        for (const auto& pc : pcs)
            parser::create_final_state(pc + 1, parser::prev_G, pc, fps);
    } else {
        for (const auto& pc : pcs)
            parser::create_final_state(pc, parser::post_G, pc, fps);
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
 * @param pos : the indexing <pc> that we use to locate the edge
 *        associating with a <pc>
 * @param G   : control flow graph: could be forward or backward
 *        based
 * @param pc  : the real <pc> points to an assertion
 * @param fps : the deque to store final program state
 */
void parser::create_final_state(const size_pc& pos, const cfg& G,
        const size_pc& pc, deque<prog_thread>& fps) {
    for (const auto& e : G.get_A()[pos]) {
        if (e.get_stmt().get_type() == type_stmt::ASSE) {
            const auto& expressions =
                    e.get_stmt().get_condition().get_splited();
            for (const auto& exp : expressions) {
                symbval s_vars(refs::SV_NUM, sool::N);
                symbval l_vars(refs::LV_NUM, sool::N);
                const auto& assgs = solver::all_sat_solve(exp, s_vars, l_vars);
                for (const auto& assg : assgs) {
                    /// step 1: build shared BV via splitting *
                    deque<state_v> svs;        /// store shared BV
                    svs.emplace_back(state_v(0));
                    for (auto i = 0; i < assg.first.size(); ++i) {
                        alg::split(assg.first[i], i, svs);
                    }

                    /// step 2: build local  BV via splitting *
                    deque<state_v> lvs;        /// store local  BV
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
    } /// complete the iteration over all edges
}

///////////////////////////////////////////////////////////////////////////////
/// from here: all member definitions of class converter                    ///
///////////////////////////////////////////////////////////////////////////////

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
 * @brief convert a program state (our otf-form global state) to a system state
 *        (user-form global state)
 * @param gs
 * @return a pair
 */
syst_state converter::convert(const prog_state& ps) {
    const auto& sss = this->convert_sps_to_sss(ps.get_s().get_vars());
    map<uint, ushort> Z;
    for (const auto p : ps.get_locals()) {
        const auto& l = p.first;
        const auto& sls = this->convert_lps_to_lss(l.get_pc(), l.get_vars());
        Z.emplace(sls, p.second);
    }
    return std::make_pair(sss, Z);
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
 * @brief This function is to convert a list of program thread states to
 *        a list of system states
 *
 * @param ss: a list of program thread states
 *
 * @return a list of system thread states
 */
deque<syst_thread> converter::convert(const deque<prog_thread>& pts) {
    deque<syst_thread> stss;
    for (const auto& pt : pts)
        stss.emplace_back(this->convert(pt));
    return stss;
}

/**
 * @brief This function is to convert program thread state to a system state
 *
 * @param ss: program thread state
 *
 * @return system thread state
 */
syst_thread converter::convert(const prog_thread& pt) {
    const auto& sst = this->convert_sps_to_sss(pt.get_s().get_vars());
    const auto& lst = this->convert_lps_to_lss(pt.get_l().get_pc(),
            pt.get_l().get_vars());
    return std::make_pair(sst, lst);
}

/**
 * @brief This function is to convert a system thread state to a program
 *        thread state
 *
 * @param ss: system thread state
 *
 * @return program thread state
 */
prog_thread converter::convert(const syst_thread& st) {
    const auto& sv = this->convert_sss_to_sps(st.first);
    const auto& p = this->convert_lss_to_lps(st.second);
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
