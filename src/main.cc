/******************************************************************************
 * @brief The main function of the API
 *        to test our API
 *
 *****************************************************************************/

#include <iostream>

#include "iotf.hh"
#include "bpp/bopp_fw.tab.hh"

using namespace iotf;

/**
 * @brief get a command
 * @param begin
 * @param end
 * @param option
 * @return a cmd
 */
char* getCmdOption(char ** begin, char ** end, const std::string & option) {
    char ** itr = std::find(begin, end, option);
    if (itr != end && ++itr != end) {
        return *itr;
    }
    return 0;
}

/**
 * @brief if a specific cmd exists or not
 * @param begin
 * @param end
 * @param option
 * @return true if exists
 *         false otherwise
 */
bool cmdOptionExists(char** begin, char** end, const std::string& option) {
    return std::find(begin, end, option) != end;
}

/**
 * @brief parser:
 * @param argc
 * @param argv
 * @return return the type of parser
 */
int main(int argc, char *argv[]) {
    char DEFAULT_CFG_FILE_NAME[100] = "bp.cfg";
    char DEFAULT_TAF_FILE_NAME[100] = "bp.taf";
    if (cmdOptionExists(argv, argv + argc, "-h")) {
        printf("Usage: BoPP [-cfg file] [-taf file]\n");
    }

    char* cfg_file_name = getCmdOption(argv, argv + argc, "-cfg");
    if (cfg_file_name == 0) {
        cfg_file_name = DEFAULT_CFG_FILE_NAME;
    }

    char* taf_file_name = getCmdOption(argv, argv + argc, "-taf");
    if (taf_file_name == 0) {
        taf_file_name = DEFAULT_TAF_FILE_NAME;
    }

    /// file list
    FILE *cfg_file = fopen(cfg_file_name, "w");
    fw_aide aide;
    yy::bp parser(aide); // make a parser
    int result = parser.parse(); // and run it

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

    //test_print_valid_assertion_ts(); // testing
    aide.output_final_state_to_file(taf_file_name);
    return result;
}
