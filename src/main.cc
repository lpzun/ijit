/******************************************************************************
 * @brief The main function of the API
 *        to test our API
 *
 *****************************************************************************/

#include <iostream>

#include "iotf.hh"
using namespace iotf;

int main() {
	cout << "I am at the beginning of main\n";
	parser::parse("", iotf::mode::POST);
	post_image post;
	global_state g;
	post.step(g);

	return 0;
}
