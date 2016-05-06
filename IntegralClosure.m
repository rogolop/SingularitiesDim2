import "SemiGroup.m": Euclides, TailExponentMatrix, InversionFormula;

intrinsic WeierstrassEquation(s::RngSerPuisElt, Q::RngMPolLoc) -> RngMPolLocElt
{ Computes the Weierstrass equation associated to a Puiseux series }
require Type(CoefficientRing(Parent(s))) eq FldAC:
  "Argument's coefficient ring must be an algebraically closed field";
  A := BaseRing(Q); x := Q.1; y := Q.2;
  n := ExponentDenominator(s); ZZ := IntegerRing();
  m := Valuation(s) eq Infinity() select ZZ!0 else ZZ!(n*Valuation(s));
  zeta := RootOfUnity(n, A); C := Coefficients(s); S := [];
  for j in [1..n] do
    Append(~S, &+[Q | C[i]*zeta^(j*(m + i - 1))*x^(m + i - 1) : i in [1..#C]]);
  end for;
  return &+[LeadingCoefficient(T) * x^(Exponents(T)[1] div n)
   * y^(Exponents(T)[2]) : T in Terms(&*[y - s : s in S])];
end intrinsic;

ClusterFactorization := function(P, v, c)
  n := Ncols(P); B := [* *]; ZZ := IntegerRing(); N := Transpose(P)*P;
  // For each point with strictly positive excess.
  for i in [i : i in [1..n] | (v*N)[1][i] gt 0] do
    p := i; I := [p]; // Traverse the cluster back to the origin
    while p ne 1 do
      p := [j : j in Reverse([1..n]) | P[p][j] eq -1][1]; I := [p] cat I;
    end while;
    e := ZeroMatrix(ZZ, 1, #I); e[1][#I] := (v*N)[1][i];
    Q := Submatrix(P, I, I); e := e*(Transpose(Q)*Q)^-1;
    B cat:= [* <Q, e, c[I]> *];
  end for; return B;
end function;

SharplyCurve := function(P, v, c, Q)
  m := Gcd(Eltseq(v)); v := v div m; G := SemiGroup(P, v);
  M := CharExponents(G) cat [TailExponentMatrix(P, v)];
  // If the curve is the y-axis.
  if #G eq 1 and &and[Type(c[i]) eq Infty: i in [2..#c]] then return Q.1; end if;
  // If the curve is inverted.
  if Type(c[2]) eq Infty then M := InversionFormula(M, P, c); end if;

  P<t> := PuiseuxSeriesRing(Parent(c[1])); s := P!0; k := 1; n := M[1][2];
  for i in [2..#M] do
    mj := M[i-1][1]; nj := M[i-1][2]; mi := M[i][1]; h0 := (mi - mj) div nj;
    s +:= &+[P | c[k + l]*t^((mj + l*nj)/n) : l in [0..h0]];
    k +:= &+Euclides(mi - mj, nj)[1];
  end for; return WeierstrassEquation(s, Q);
end function;

Unloading := function(P, v)
  N := Transpose(P)*P; n := Ncols(P); ZZ := IntegerRing();
  while #[r : r in Eltseq(v*N) | r lt 0] gt 0 do
    p := [i : i in [1..n] | (v*N)[1][i] lt 0][1];
    lp := ZeroMatrix(ZZ, 1, n); lp[1][p] := 1;
    rp := (lp*N*Transpose(lp))[1][1];
    np := Ceiling(-(v*N*Transpose(lp))[1][1]/rp); v +:= np*lp;
  end while; return v;
end function;

CleanIdeal := function(I)
  J := Basis(I); for g in J do
    J := [f : f in J | not IsDivisibleBy(f, g) or f eq g];
  end for; return ideal<Parent(J[1]) | J>;
end function;

forward IntegralClosureImpl;

IntegralClosureImpl := function(P, v, c, Q)
  // If the cluster has a single point, return a power of the maximal ideal.
  if Ncols(P) eq 1 then return (ideal<Q | Q.1, Q.2>)^v[1][1]; end if;

  // Compute the curvete going through the current cluster.
  N := Ncols(P); m := Gcd(Eltseq(v)); v := v div m; ZZ := IntegerRing();
  isFree := &+[Transpose(P)[i] : i in [1..N]]; // Last free point.
  p := [i : i in Reverse([1..N]) | isFree[i] eq 0][1]; Ip := [1..p];
  Pp := Submatrix(P, Ip, Ip); vp := ZeroMatrix(ZZ, 1, #Ip); vp[1][#Ip] := 1;
  vp := vp*(Transpose(Pp)*Pp)^-1; n := v[1][1] div vp[1][1]; cp := c[Ip];
  f := SharplyCurve(Pp, vp, cp, Q); // A sharply curve is enough.

  // Add free point at the origin & unload.
  P := InsertBlock(ScalarMatrix(N + 1, 1), P, 1, 1);
  v := InsertBlock(ZeroMatrix(ZZ, 1, N + 1), v, 1, 1);
  P[N + 1][1] := -1; v[1][N + 1] := v[1][1] + 1;
  v := Unloading(P, v); e := v*Transpose(P); // Unload & get multiplicities.
  I := [i : i in [1..N] | e[1][i] ne 0]; // Remove empty points.
  P := Submatrix(P, I, I); v := Submatrix(v, [1], I); c := c[I];

  // Apply Zariski theorem on complete ideals and recurse.
  II := [ IntegralClosureImpl(K[1], K[2], K[3], Q) :
    K in ClusterFactorization(P, v, c) ];
  // Return ((f^n) + \prod_{i=1}^{#II} I_i)^m.
  return CleanIdeal(ideal<Q | f^n> + [i gt 1 select Self(i-1)*II[i]
    else II[1] : i in [1..#II]][#II])^m;
end function;

intrinsic IntegralClosure(I::RngMPolLoc: StdBasis := false) -> RngMPolLoc
{ Computes the integral closure of a bivariate polynomial ideal }
require Type(Representative(I)) eq RngMPolLocElt:
  "Argument must be a polynomial ideal";
require Rank(Parent(Representative(I))) eq 2:
  "Argument must be a bivariate polynomial ideal";
  // Compute the weighted cluster of base points.
  B := BasePoints(I : Coefficients := true);
  P := B[1]; v := B[2]; f := B[3]; c := B[4];
  if Ncols(P) eq 0 then return ideal<Parent(f) | f>; end if;
  // Factorize the cluster of base points and start recursion.
  Q<x, y> := LocalPolynomialRing(Parent(c[1]), 2, "lglex");
  II := [ IntegralClosureImpl(K[1], K[2], K[3], Q) :
    K in ClusterFactorization(P, v, c) ];
  // Multiply by the affine part and return the std basis if requested.
  J := ideal<Q | f>*CleanIdeal([i gt 1 select Self(i - 1)*II[i]
    else II[1] : i in [1..#II]][#II]);
  if StdBasis then return StandardBasis(J); else return J; end if;
end intrinsic;
