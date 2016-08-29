import "SemiGroup.m": Euclides, TailExponentMatrix, InversionFormula;

// Given a Puiseux series s, returns its associated Weierstrass equation.
intrinsic WeierstrassEquationCyclotomic(s::RngSerPuisElt, Q::RngMPolLoc) -> RngMPolLocElt
{ Computes the Weierstrass equation associated to a Puiseux series }
require Type(CoefficientRing(Parent(s))) eq FldAC:
  "Argument's coefficient ring must be an algebraically closed field";
  x := Q.1; y := Q.2;
  C, n, m := Coefficients(s); zeta := RootOfUnity(n, BaseRing(Q));

  S := [&+[Q | C[i] * zeta^(j * (m + i - 1)) * x^(m + i - 1) :
    i in [1..#C]] : j in [1..n]];
  return &+[LeadingCoefficient(T) * x^(Exponents(T)[1] div n)
   * y^(Exponents(T)[2]) : T in Terms(&*[y - s : s in S])];
end intrinsic;

// Given a Puiseux series s, returns its associated Weierstrass equation.
intrinsic WeierstrassEquationDeterminant(s::RngSerPuisElt, Q::RngMPolLoc) -> RngMPolLocElt
{ Computes the Weierstrass equation associated to a Puiseux series }
  x := Q.1; y := Q.2; C, m, n := Coefficients(s); G := CyclicGroup(n);
  g := n gt 1 select G.1^(n - 1) else G.0;

  V := [&+[Q | C[i + 1] * x^((m + i - s) div n) : i in [0..#C - 1] |
    (i + m) mod n eq s] : s in [0..n - 1]];
  M := Matrix([V[Eltseq(g^i)] : i in [0..n - 1]]);
  for i in [1..n] do
    InsertBlock(~M, x * Submatrix(M, [i], [1..i - 1]), i, 1);
  end for;
  return Determinant(ScalarMatrix(n, y) - M);
end intrinsic;

// Factorices the weighted cluster (P, v, c) as a unique sum of
// irreducible weighted clusters.
ClusterFactorization := function(P, v, c)
  N := Transpose(P) * P; Ninv := N^-1; exc := v * N;
  n := Ncols(P); ZZ := IntegerRing();

  B := []; // For each point with strictly positive excess.
  for i in [i : i in [1..n] | exc[1][i] gt 0] do
    p := i; I := [p];
    while p ne 1 do // Traverse the cluster back to the origin
      p := [j : j in Reverse([1..n]) | P[p][j] eq -1][1]; I := [p] cat I;
    end while;
    v := ZeroMatrix(ZZ, 1, n); v[1][i] := exc[1][i]; v := v * Ninv; B cat:= [v];
  end for; return B;
end function;

// Returns the curve going sharply through (P, v).
// Prerequisite: The last point of (P, v) must be free.
// && the cluster (P, v, c) must be irreducible.
SharplyCurve := function(P, v, c, Q)
  m := Gcd(Eltseq(v)); v := v div m; G := SemiGroup(P, v);
  M := CharExponents(G) cat [TailExponentMatrix(P, v)];
  // If the curve is the y-axis.
  if #G eq 1 and #c gt 1 and &and[c[i][1] eq 0: i in [2..#c]] then
  return Q.1; end if;

  // If the curve is inverted.
  if c[2][1] eq 0 then M := InversionFormula(M, P, c); end if;
  P<t> := PuiseuxSeriesRing(Parent(c[1][2])); s := P!0; k := 1; n := M[1][2];
  for i in [2..#M] do
    mj := M[i - 1][1]; nj := M[i - 1][2]; mi := M[i][1]; h0 := (mi - mj) div nj;
    s +:= &+[P | c[k + l][2] * t^((mj + l * nj) / n) : l in [0..h0]];
    k +:= &+Euclides(mi - mj, nj)[1];
  end for; return WeierstrassEquationDeterminant(s, Q)^m;
end function;

// Computes the curvettes a weighted cluster.
Curvettes := function(P, v, c, Q)
  P_inv := P^-1; Pt := Transpose(P); Pt_inv := Transpose(P_inv);
  n := Ncols(P); isSat := &+[Pt[i] : i in [1..n]];
  // 'Curvette' points are always free.
  freePoints := [p : p in [1..n] | isSat[p] eq 0]; curvPoints := [];
  for p in freePoints do
    // Points proximate to 'p'.
    prox_p := [i : i in [p + 1..n] | Pt[p][i] eq -1];
    // Points proximate to 'p' that are satellites.
    prox_p_sat := [q : q in prox_p | isSat[q] eq -1];
    // Select 'p' is if it has no proximate points in K (dead end) or
    // all its proximate points in K are satellite (rupture point).
    if #prox_p eq 0 or #prox_p eq #prox_p_sat then
      curvPoints cat:= [p]; end if;
  end for; C := []; // Now, construct equations for each curvette.
  for p in curvPoints do
    i_p := ZeroMatrix(IntegerRing(), 1, n); i_p[1][p] := 1;
    e_p := i_p*P_inv; Ip := [i : i in [1..n] | e_p[1][i] ne 0];
    v_p := e_p*Pt_inv; f_p := SharplyCurve(Submatrix(P, Ip, Ip),
      Submatrix(v_p, [1], Ip), c[Ip], Q);
    C cat:= [<f_p, v_p, e_p>];
  end for;
  // Let's check if we need to add x or y as a curvette. This will always
  // happen in the irreducible case. Otherwise, we might have smooth curvettes
  // playing the role of x and/or y.
  e_O := ZeroMatrix(IntegerRing(), 1, n); e_O[1][1] := 1; v_O := e_O*Pt_inv;
  if #[f : f in C | LeadingTerm(f[1]) eq Q.1] eq 0 then
    C cat:= [<Q.1, v_O, e_O>]; end if;
  if #[f : f in C | LeadingTerm(f[1]) eq Q.2] eq 0 then
    C cat:= [<Q.2, v_O, e_O>]; end if;
  return C;
end function;

// Unloads the weighted cluster represented by (P, v) where
// v are virtual values.
Unloading := function(P, v)
  N := Transpose(P) * P; n := Ncols(P);
  while #[r : r in Eltseq(v * N) | r lt 0] gt 0 do
    p := [i : i in [1..n] | (v * N)[1][i] lt 0][1];
    lp := ZeroMatrix(IntegerRing(), 1, n); lp[1][p] := 1;
    rp := (lp * N * Transpose(lp))[1][1];
    np := Ceiling(-(v * N * Transpose(lp))[1][1] / rp);
    v +:= np * lp;
  end while; return v;
end function;

//forward IntegralClosureImpl;
//
//IntegralClosureImpl := function(P, v, c, Q)
//  // If the cluster has a single point, return a power of the maximal ideal.
//  if Ncols(P) eq 1 then return (ideal<Q | Q.1, Q.2>)^v[1][1]; end if;
//
//  // Compute the curvete going through the current cluster.
//  N := Ncols(P); m := Gcd(Eltseq(v)); v := v div m; ZZ := IntegerRing();
//  isFree := &+[Transpose(P)[i] : i in [1..N]]; // Last free point.
//  p := [i : i in Reverse([1..N]) | isFree[i] eq 0][1]; Ip := [1..p];
//  Pp := Submatrix(P, Ip, Ip); vp := ZeroMatrix(ZZ, 1, #Ip); vp[1][#Ip] := 1;
//  vp := vp * (Transpose(Pp) * Pp)^-1; n := v[1][1] div vp[1][1]; cp := c[Ip];
//  f := SharplyCurve(Pp, vp, cp, Q); // A sharply curve is enough.
//
//  // Add free point at the origin & unload.
//  P := InsertBlock(ScalarMatrix(N + 1, 1), P, 1, 1);
//  v := InsertBlock(ZeroMatrix(ZZ, 1, N + 1), v, 1, 1);
//  P[N + 1][1] := -1; v[1][N + 1] := v[1][1] + 1;
//  v := Unloading(P, v); e := v * Transpose(P); // Unload & get multiplicities.
//  I := [i : i in [1..N] | e[1][i] ne 0]; // Remove empty points.
//  P := Submatrix(P, I, I); v := Submatrix(v, [1], I); c := c[I];
//
//  // Apply Zariski theorem on complete ideals and recurse.
//  II := [ IntegralClosureImpl(K[1], K[2], K[3], Q) :
//    K in ClusterFactorization(P, v, c) ];
//  // Return ((f^n) + \prod_{i=1}^{#II} I_i)^m.
//  return CleanIdeal(ideal<Q | f^n> + [i gt 1 select Self(i-1) * II[i]
//    else II[1] : i in [1..#II]][#II])^m;
//end function;

IntegralClosureIrreducible := function(P, v, c, Cv)
  return 0;
end function;

intrinsic IntegralClosure(I::RngMPolLoc) -> RngMPolLoc
{ Computes the integral closure of a bivariate polynomial ideal }
require Type(Representative(I)) eq RngMPolLocElt:
  "Argument must be a polynomial ideal";
require Rank(Parent(Representative(I))) eq 2:
  "Argument must be a bivariate polynomial ideal";
  // Compute the weighted cluster of base points.
  B := BasePoints(I : Coefficients := true);
  P := B[1]; v := B[2]; f := B[3]; c := B[4];
  if Ncols(P) eq 0 then return ideal<Parent(f) | f>; end if;

  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex");
  Cv := Curvettes(P, v, c, Q);
  print Cv;
  //II := [ IntegralClosureIrreducible(P, v_i, c, Cv) :
  //  v_i in ClusterFactorization(P, v, c) ];
  //// Multiply by the affine part and return the std basis if requested.
  //J := ideal<Q | f> * CleanIdeal([i gt 1 select Self(i - 1) * II[i]
  //  else II[1] : i in [1..#II]][#II]);
  return [];
end intrinsic;
