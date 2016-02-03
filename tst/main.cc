/******************************************************************************
 * @brief The main function of the API
 *        to test our API
 *
 *****************************************************************************/

#include <iostream>

#include "../src/iotf.hh"

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
    /*if (cmdOptionExists(argv, argv + argc, "-h")) {
     printf("Usage: itof [-f file]\n");
     }

     string filename(getCmdOption(argv, argv + argc, "-f"));
     if (filename.length() == 0) {
     filename = "example/test1.bp";
     }
     auto P = parser::parse(filename, mode::POST);
     */
    const uint N = 32;

    bitset<N> mask;
    mask.set();
    cout << mask << endl;
    bitset<N> foo(4);
    cout << foo << endl;
    cout << ((foo << 8) & mask) << endl;

    foo.set(1);
    cout << foo << endl;
}
