/******************************************************************************
 * @brief The main function of the API
 *        to test our API
 *
 *****************************************************************************/

#include <iostream>

#include "iotf.hh"
using namespace iotf;

int main() {
	cout << "!!!Hello World!!!" << endl; // prints !!!Hello World!!!
	vector<bool> vb1;
	vb1.push_back(true);
	vb1.push_back(false);
	vb1.push_back(false);
	vb1.push_back(false);

	vector<bool> vb2;
	vb2.push_back(false);
	vb2.push_back(true);
	vb2.push_back(false);
	vb2.push_back(false);
	if (vb1 < vb2)
		cout << "<: I am here\n";
	else if (vb1 > vb2)
		cout << ">: I am here\n";
	else
		cout << "=: I am here\n";

	std::map<char, int> foo, bar;
	foo['a'] = 100;
	foo['b'] = 200;
	foo['c'] = 20;
	bar['b'] = 10;
	bar['z'] = 1000;

	// foo ({{a,100},{b,200}}) vs bar ({a,10},{z,1000}}):
	if (foo == bar)
		std::cout << "foo and bar are equal\n";
	if (foo != bar)
		std::cout << "foo and bar are not equal\n";
	if (foo < bar)
		std::cout << "foo is less than bar\n";
	if (foo > bar)
		std::cout << "foo is greater than bar\n";
	if (foo <= bar)
		std::cout << "foo is less than or equal to bar\n";
	if (foo >= bar)
		std::cout << "foo is greater than or equal to bar\n";

	cout<<int()<<endl;

	pre_image i;
	global_state g;
	i.step(g);
	return 0;
}
