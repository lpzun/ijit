/******************************************************************************
 * @brief The main function of the API
 *        to test our API
 *
 *****************************************************************************/

#include <iostream>

#include "../test/tst_convert.hh"
#include "../test/tst_parser.hh"

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
    try {
        if (cmdOptionExists(argv, argv + argc, "-h")) {
            printf("Usage: itof [-f file]\n");
        }

        const string filename(getCmdOption(argv, argv + argc, "-f"));
        if (filename.length() == 0) {
            throw iotf_runtime_error("Please specify filename!");
        }

        cout << true << " " << false << "\n";

        cout << "testing split...\n";
        tst_solver::test_split();

        cout << "testing all sat solve...\n";
        tst_solver::test_all_sat_solve();

        cout << "testing parser...\n";
        tst_parser::test_parser(filename);

//        cout << "from here...................\n";
//        bitset<16> bs1(1);
//        cout << bs1 << "\n";
//        bitset<16> bs3(3);
//        cout << bs3 << "\n";
//
//        if (bs1 < bs3)
//            cout << "< works on bitset" << endl;

        return 0;
    } catch (const iotf_runtime_error& e) {
        cerr << e.what() << endl;
    } catch (const iotf_exception& e) {
        cerr << e.what() << endl;
    } catch (const std::runtime_error& e) {
        cerr << e.what() << endl;
    } catch (const std::exception& e) {
        cerr << e.what() << endl;
    } catch (...) {
        cerr << "unknown error!" << endl;
    }
}
