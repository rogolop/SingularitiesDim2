AttachSpec("/Users/guillem/IntegralClosureDim2/IntegralClosureDim2.m");
Q<x, y> := LocalPolynomialRing(RationalField(), 2, "lglex");

// Whole ring
I := ideal<Q | 1 + x, y>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 0 and Nrows(P) eq 0);
assert(Ncols(v) eq 0 and Nrows(v) eq 1);
assert(#C eq 0);

// Whole ring
I := ideal<Q | 1 + y, x>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 0 and Nrows(P) eq 0);
assert(Ncols(v) eq 0 and Nrows(v) eq 1);
assert(#C eq 0);

// Maximal ideal
I := ideal<Q | x, y>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 1 and Nrows(P) eq 1);
assert(Ncols(v) eq 1 and Nrows(v) eq 1);
assert(#C eq 1);

// Single free point
I := ideal<Q | y, x^2>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 2 and Nrows(P) eq 2);
assert(Ncols(v) eq 2 and Nrows(v) eq 1);
assert(#C eq 2); assert(C[2] eq 0);

// Single free point
I := ideal<Q | x, y^2>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 2 and Nrows(P) eq 2);
assert(Ncols(v) eq 2 and Nrows(v) eq 1);
assert(#C eq 2); assert(C[2] eq Infinity());

// Cusp ideal
I := ideal<Q | y^2, x^3>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq 0); assert(C[3] eq Infinity());

// Cusp ideal
I := ideal<Q | x^2, y^3>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq Infinity()); assert(C[3] eq Infinity());

// Exemple common branch
I := ideal<Q | x^2, x*y^2, y^5 - x^6>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq Infinity()); assert(C[3] eq Infinity());

// Exemple common branch
I := ideal<Q | y^2, y*x^2, x^5 - y^6>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq 0); assert(C[3] eq 0);

// Casas' Collectanea example
I := ideal<Q | x^5*y - y^3, x^8 + 2*x^5*y>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq 0); assert(C[3] eq 0);
assert(C[4] eq Infinity());

// Casas' Collectanea example
I := ideal<Q | y^5*x - x^3, y^8 + 2*y^5*x>;
B := BasePoints(I: Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4);
assert(C[2] eq Infinity());
assert(C[3] eq Infinity());
assert(C[4] eq Infinity());

// Victor's TFM examples

// A1
f := (y^2 - x^3)*(y^2 + x^3);
B := BasePoints(JacobiIdeal1(f): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq 0);

B := BasePoints(JacobiIdeal2(f): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq 0);

B := BasePoints(JacobiIdeal1(Evaluate(f, <y, x>)): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq Infinity());

B := BasePoints(JacobiIdeal2(Evaluate(f, <y, x>)): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq Infinity());

// A2
f := (y^2 - x^3)*(y^2 - 2*x^3);
B := BasePoints(JacobiIdeal1(f): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq 0);

B := BasePoints(JacobiIdeal2(f): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq 0);

B := BasePoints(JacobiIdeal1(Evaluate(f, <y, x>)): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq Infinity());

B := BasePoints(JacobiIdeal2(Evaluate(f, <y, x>)): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 4 and Nrows(P) eq 4);
assert(Ncols(v) eq 4 and Nrows(v) eq 1);
assert(#C eq 4); assert(C[2] eq Infinity());

// A3
f := (y^2 - x^3)*((y - x)^2 - x^3);
B := BasePoints(JacobiIdeal1(f): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq 1);

B := BasePoints(JacobiIdeal2(f): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq 1);

B := BasePoints(JacobiIdeal1(Evaluate(f, <y, x>)): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq Infinity());

B := BasePoints(JacobiIdeal2(Evaluate(f, <y, x>)): Coefficients := true);
P := B[1]; v := B[2]; g := B[3]; C := B[4];
assert(Ncols(P) eq 3 and Nrows(P) eq 3);
assert(Ncols(v) eq 3 and Nrows(v) eq 1);
assert(#C eq 3); assert(C[2] eq Infinity());
