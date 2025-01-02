#include "ibex.h"
#include <iostream>

using namespace std;
using namespace ibex;

int main() {

    Interval zero(0, 0);
    Interval one(1, 1);
    Variable x, y, z;

    cout << "Trial 1: Basic integral forward" << endl;
    Function i1(x, x * x);
    Function i(z, integral(i1, zero, z));

    cout << i << endl;
    cout << i.cf << endl;

    double _args1[1][2] = {{2, 2}};
    IntervalVector args1(1, _args1);
    Interval r1 = i.eval(args1);

    cout << r1 << endl;

    //return 0;

    cout << "Trial 2: Desired semantics" << endl;
    Function j3(y, x, x - y);
    Function j2(x, z, integral(j3, zero, z, Array<const ExprNode>(x)));
    Function j(z, integral(j2, zero, z, Array<const ExprNode>(z)));

    cout << j << endl;
    cout << j.cf << endl;

    double _args2[1][2] = {{1, 42}};
    IntervalVector args2(1, _args2);
    Interval r2 = j.eval(args2);

    cout << r2 << endl;

    cout << "Trial 3: contracting" << endl;
    Function k2(x, z, z-2);
    Function k(z, integral(k2, zero, one, Array<const ExprNode>(z)));

	IntervalVector args3(1,Interval(-10,10));

	/* we give f directly (means that the constraint is f=0) */
	CtcFwdBwd c(k);
	c.contract(args3);
    std::cout << "After contraction" << std::endl;

	/* display ([0.2929, 0.7072] ; [0.2929, 0.7072]) */
	cout << args3 << endl;
    std::cout << "Re-Evaluation" << std::endl;

    cout << k.eval(args3) << endl;

	return 0;
}