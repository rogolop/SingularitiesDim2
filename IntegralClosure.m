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
  x := Q.1; y := Q.2; C, m, n := Coefficients(s); g := CyclicGroup(n).1^(n - 1);

  V := [&+[Q | C[i + 1] * x^((m + i - s) div n) : i in [0..#C - 1] |
    (i + m) mod n eq s] : s in [0..n - 1]];
  M := Matrix([V[Eltseq(g^i)] : i in [0..n - 1]]);
  for i in [1..n] do
    InsertBlock(~M, x * Submatrix(M, [i], [1..i - 1]), i, 1);
  end for;
  return Determinant(ScalarMatrix(n, y) - M);
end intrinsic;

// Factorices the weighted cluster (P, v) as a unique sum of
// irreducible weighted clusters.
ClusterFactorization := function(P, v, c)
  N := Transpose(P) * P; Ninv := N^-1; exc := v * N;
  n := Ncols(P); ZZ := IntegerRing();

  B := [];
  // For each point with strictly positive excess.
  for i in [i : i in [1..n] | exc[1][i] gt 0] do
    p := i; I := [p];
    // Traverse the cluster back to the origin
    while p ne 1 do
      p := [j : j in Reverse([1..n]) | P[p][j] eq -1][1]; I := [p] cat I;
    end while;
    v := ZeroMatrix(ZZ, 1, n); v[1][i] := exc[1][i]; v := v * Ninv;
    B cat:= [v];
  end for; return B;
end function;

// Returns the curve going sharply through (P, v).
// Prerequisite: The last point of (P, v) must be free.
SharplyCurve := function(P, v, c, Q)
  m := Gcd(Eltseq(v)); v := v div m; G := SemiGroup(P, v);
  M := CharExponents(G) cat [TailExponentMatrix(P, v)];
  // If the curve is the y-axis.
  if #G eq 1 and #c gt 1 and &and[Type(c[i]) eq Infty: i in [2..#c]] then return Q.1; end if;

  // If the curve is inverted.
  if Type(c[2]) eq Infty then M := InversionFormula(M, P, c); end if;
  P<t> := PuiseuxSeriesRing(Parent(c[1])); s := P!0; k := 1; n := M[1][2];
  for i in [2..#M] do
    mj := M[i - 1][1]; nj := M[i - 1][2]; mi := M[i][1]; h0 := (mi - mj) div nj;
    s +:= &+[P | c[k + l] * t^((mj + l * nj) / n) : l in [0..h0]];
    k +:= &+Euclides(mi - mj, nj)[1];
  end for; return WeierstrassEquationDeterminant(s, Q)^m;
end function;

// Compute the curvettes an irreducible weighted cluster.
// Caveat: Depending on whether P ends with a free or a satellite point
//         this function returns g + 1 or g equations respectively.
Curvettes := function(P, v, c, Q)
  Pt := Transpose(P); e := v * Pt; N := Pt * P; Ninv := N^-1;
  n := Ncols(P); ZZ := IntegerRing();
  // Only look at points with e > 0.
  inCluster := [i : i in [1..n] | e[1][i] ne 0];
  isFreeOrSat := &+[Pt[i] : i in [1..n]]; isFreeOrSat[1] := 0;

  Cv := []; q := #inCluster;
  // While q different from the origin.
  while q ne 0 do
    // Find last free point in the cluster.
    p := [i : i in Reverse([1..q]) | isFreeOrSat[inCluster[i]] eq 0][1];
    // Compute the irreducible cluster K(p) ending at p.
    inCluster := inCluster[1..p]; m := #inCluster;
    v := ZeroMatrix(ZZ, 1, n); v[1][m] := 1; v := v * Ninv;
    // Compute the sharply curve through K(p).
    Cv cat:= [<SharplyCurve(Submatrix(P, inCluster, inCluster),
      Submatrix(v, [1], inCluster), c[inCluster], Q), v>];
    // Either the first sat after p or the origin.
    q := ([0] cat [i : i in Reverse([1..m]) |
      Abs(isFreeOrSat[inCluster[i]]) eq 1])[1];
  end while;
  // Add the missing branch (first curvette).
  if LeadingTerm(Cv[1][1]) eq Q.2 then
    e := ZeroMatrix(ZZ, 1, n); e[1][1] := 1;
    for i in [1..n] do if Type(c[i]) eq Infty then e[1][i] := 1; end if; end for;
    Cv cat:= [<Q.1, e * Pt^-1>];
  else
    e := ZeroMatrix(ZZ, 1, n); e[1][1] := 1;
    Cv cat:= [<Q.2, e * Pt^-1>];
  end if; return Reverse(Cv);
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

//CleanIdeal := function(I)
//  J := Basis(I); for g in J do
//    J := [f : f in J | not IsDivisibleBy(f, g) or f eq g];
//  end for; return ideal<Parent(J[1]) | J>;
//end function;

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

IntegralClosureIrreducible := function(P, v, c, Q)
  print <P, v, c>;
  print Curvettes(P, v, c, Q);
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

  Q<x, y> := LocalPolynomialRing(Parent(c[1]), 2, "lglex");
  II := [ IntegralClosureIrreducible(P, vv, c, Q) :
    vv in ClusterFactorization(P, v, c) ];
  //// Multiply by the affine part and return the std basis if requested.
  //J := ideal<Q | f> * CleanIdeal([i gt 1 select Self(i - 1) * II[i]
  //  else II[1] : i in [1..#II]][#II]);
  return [];
end intrinsic;
