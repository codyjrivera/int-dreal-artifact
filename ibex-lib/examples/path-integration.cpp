#include "ibex.h"
#include <iostream>

using namespace std;
using namespace ibex;

int main() {
    Interval zero(0, 0);
    Interval twenty(20, 20);
    Variable x, y, z;

    cout << "The pathological integral" << endl;
    Function i1(x, exp(-0.5 * pow((x - 10)/ 5, 2)));
    Function i(z, integral(i1, zero, twenty));

    cout << i1 << endl;
    cout << i1.cf << endl;

    cout << i << endl;
    cout << i.cf << endl;

    double _args1[1][2] = {{2, 2}};
    IntervalVector args1(1, _args1);
    Interval r1 = i.eval(args1);

    cout << r1 << endl;

    cout << "A nonpathological example" << endl;
    Function j1(x, exp(-0.5 * ((x - 10)/ 5)));
    Function j(z, integral(j1, zero, twenty));

    cout << j1 << endl;
    cout << j1.cf << endl;

    cout << j << endl;
    cout << j.cf << endl;    

    Interval r2 = j.eval(args1);
    cout << r2 << endl;

    cout << "Yet another buggy example" << endl;

    Interval eps(0.8, 1); // or eps(0.9, 0.9)
    Variable evar;
    Function k1(x, evar, 1 / (evar * evar));
    Function k(z, integral(k1, zero, twenty, Array<const ExprNode>(eps)));

    cout << k1 << endl;
    cout << k1.cf << endl;

    cout << k << endl;
    cout << k.cf << endl;    

    Interval r3 = k.eval(args1);
    cout << r3 << endl;

	return 0;
}