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

cfg parser::prev_G; /// control flow graph in PREV mode
cfg parser::post_G; /// control flow graph in POST mode

/**
 * @brief default constructor
 */
parser::parser() {

}

/**
 * @brief default destructor
 */
parser::~parser() {

}

/**
 * @brief parse Boolean programs based on the mode (preimage or postimage)
 * @param filename: Boolean program
 * @param m       : mode
 */
pair<initl_ps, final_ps> parser::parse(const string& filename, const mode& m) {
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
pair<initl_ps, final_ps> parser::parse_in_prev_mode(const string& filename) {
    initl_ps I;
    final_ps Q;
    // TODO initialize prev_G
    return std::make_pair(I, Q);
}

/**
 * @brief parse Boolean programs in postimage mode
 * @param filename
 */
pair<initl_ps, final_ps> parser::parse_in_post_mode(const string& filename) {
    initl_ps I;
    final_ps Q;

    FILE *bPfile = fopen(filename.c_str(), "r");
    if (!bPfile) {
        throw iotf_runtime_error("I cannot open " + filename);
    }
    yyin = bPfile;
    char DEFAULT_CFG_FILE_NAME[100] = "bp.cfg";
    char DEFAULT_TAF_FILE_NAME[100] = "bp.taf";
    char* cfg_file_name = DEFAULT_CFG_FILE_NAME;
    char* taf_file_name = DEFAULT_TAF_FILE_NAME;
    /// file list
    FILE *cfg_file = fopen(cfg_file_name, "w");
    fw_aide aide;
    yy::bp parser(aide); // make a parser
    int result = parser.parse(); // and run it
    if (result != 0) {
        throw iotf_runtime_error(
                "Parser exit with exception: code " + std::to_string(result));
    }

    /* fw_aide aide; */
    //move the file point to the begin and print the total line number
    fprintf(cfg_file, "# control flow graph and other information\n");
    fprintf(cfg_file, "shared %d\n", aide.s_vars_num);
    fprintf(cfg_file, "local %d\n", aide.l_vars_num);

    //note the initial pc!!!!!!!!
    fprintf(cfg_file, "init %s|0,%s # initial thread state\n",
            (aide.create_init_state(aide.s_vars_init)).c_str(),
            (aide.create_init_state(aide.l_vars_init)).c_str());
    fprintf(cfg_file, "%d%s %d\n", aide.lineno,
            " # the number of lines in BP with cand PC = ", 1);
    cout << 1 << ":" << aide.lineno << endl;

    aide.output_control_flow_graph(cfg_file);
    fclose(cfg_file);

    // test_print_valid_assertion_ts(); // testing
    aide.output_final_state_to_file(taf_file_name);
    // TODO initialize post_G
    return std::make_pair(I, Q);
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
    // TODO
    return global_state();
}

/**
 * @brief convert a program state (our otf-form global state) to a system state
 *        (user-form global state)
 * @param gs
 * @return a pair
 */
syst_state converter::convert(const prog_state& ps) {
    // TODO
    return std::make_pair<uint, map<uint, uint>>(0, map<uint, uint>());
}

/**
 * @brief convert a shared system state to a shared program state
 * @param ss
 * @return a shared program state
 */
vector<bool> converter::convert_ss_to_ps(const uint& ss) {
    vector<bool> sv(refs::SHARED_VARS_NUM, false);
    int pos = 0;
    while (pos < refs::SHARED_VARS_NUM) {
        if ((ss >> pos) & 1)
            sv[pos] = true;
    }
    return sv;
}

/**
 * @brief convert a shared program state to a shared system state
 * @param ps
 * @return a shared system state
 */
uint converter::convert_ps_to_ss(const vector<bool>& ps) {
    uint ss = 0;
    for (int i = 0; i < ps.size(); ++i) {
        if (ps[i])
            ss += 1 >> i;
    }
    return ss;
}

} /* namespace otf */
