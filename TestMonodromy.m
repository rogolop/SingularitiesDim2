AttachSpec("./IntegralClosureDim2.spec");
Q<x, y> := LocalPolynomialRing(RationalField(), 2, "lglex");

// Example in mondoromyB from Singular's mondromy_lib.
M := Monodromy(x^6 + y^6 + x^2*y^2);
s := Parent(M[1][1]).1; i := 1;
assert(M[i] eq <s - 4/3, 1>); i +:= 1;
assert(M[i] eq <s - 4/3, 1>); i +:= 1;
assert(M[i] eq <s - 7/6, 1>); i +:= 1;
assert(M[i] eq <s - 7/6, 1>); i +:= 1;
assert(M[i] eq <s - 1, 1>); i +:= 1;
assert(M[i] eq <s - 1, 1>); i +:= 1;
assert(M[i] eq <s - 1, 1>); i +:= 1;
assert(M[i] eq <s - 5/6, 1>); i +:= 1;
assert(M[i] eq <s - 5/6, 1>); i +:= 1;
assert(M[i] eq <s - 2/3, 1>); i +:= 1;
assert(M[i] eq <s - 2/3, 1>); i +:= 1;
assert(M[i] eq <s - 1/2, 2>); i +:= 1;

// Example in monodromy from Singular's gmssing_lib.
M := Monodromy(x^5 + y^5 + x^2*y^2);
s := Parent(M[1][1]).1; i := 1;
assert(M[i] eq <s - 13/10, 1>); i +:= 1;
assert(M[i] eq <s - 13/10, 1>); i +:= 1;
assert(M[i] eq <s - 11/10, 1>); i +:= 1;
assert(M[i] eq <s - 11/10, 1>); i +:= 1;
assert(M[i] eq <s - 1, 1>); i +:= 1;
assert(M[i] eq <s - 9/10, 1>); i +:= 1;
assert(M[i] eq <s - 9/10, 1>); i +:= 1;
assert(M[i] eq <s - 7/10, 1>); i +:= 1;
assert(M[i] eq <s - 7/10, 1>); i +:= 1;
assert(M[i] eq <s - 1/2, 2>); i +:= 1;








