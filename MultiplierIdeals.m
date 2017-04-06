import "ProximityMatrix.m": ProximityMatrixImpl;
import "IntegralClosure.m": IntegralClosureIrreducible, Unloading, ProductIdeals,
                            ClusterFactorization, Curvettes;

// Ignore this function for the moment
intrinsic PseudoMultiplierChain(I::RngMPolLoc) -> []
{ Returns the chain of multiplier ideals associated to an irreducible plane curve }
require Rank(I) eq 2: "First argument must be a plane ideal";

  BP := BasePoints(I: Coefficients := true);
  P := BP[1]; v := BP[2]; f := BP[3]; c := BP[4];
  if f ne 1 then error "ideal must be m-primary"; end if;
  Pt := Transpose(P); e := v*Pt; rho := e*P; N := Ncols(P);
  if &+[rho[1][i] : i in [1..N]] ne 1 then error "ideal must be simple"; end if;
  KK := (e*Transpose(e))[1][1]; // Divisor auto-intersection.

  // Compute the curvettes of the curve.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex");
  Cv := Curvettes(P, e[1]*Pt^-1, c, Q);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, N); max[1][1] := 1; max := max*Pt^-1;

  v_i := ZeroMatrix(IntegerRing(), 1, N); m_i := 0; J := [];
  while m_i lt KK do
    // Enlarge the values of the previos cluster.
    v_i[1][N] +:= 1; v_i := Unloading(P, v_i); e_i := v_i*Pt;

    // Compute generators for the complete ideal J_i.
    J_i := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q) :
      v_j in ClusterFactorization(P, v_i)];
    J_i := [g[1] : g in ProductIdeals(J_i) |
      &or[g[2][1][i] lt (v_i + max)[1][i] : i in [1..N]]];

    // Jump the gaps in the filtration.
    KK_i := &+[e[1][i] * e_i[1][i] : i in [1..N]]; // Intersection [K, K_i]
    Append(~J, J_i); m_i := KK_i;
  end while;

  return J;
end intrinsic;

RSet := function(p, q)
  return [a*p + b*q : a in [1..q], b in [1..p] | a*p + b*q lt p*q];
end function;

// Reference: D. Naie - Jumping numbers of a unibranch curve on a smooth surface
intrinsic JumpingNumbers(G::[RngIntElt]) -> []
{ Compute the Jumping Numbers < 1 of an irreducible plane curve from its semigroup }
  require IsPlaneCurveSemiGroup(G): "G is not the semigroup of a plane curve";
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];

  g := #G - 1; JN := [];
  for i in [1..g] do
    p := E[i] / E[i + 1]; q := G[i + 1] / E[i + 1]; R := RSet(p, q);
    Rmj := [k*p*q + alpha : k in [0..E[i+1] - 1], alpha in R];
    JN cat:= [[beta / Lcm(E[i], G[i + 1]) : beta in Rmj]];
  end for; return JN;
end intrinsic;

// Reference: D. Naie - Jumping numbers of a unibranch curve on a smooth surface
intrinsic JumpingNumbers(n::RngIntElt, M::[RngIntElt]) -> []
{ Compute the Jumping Numbers < 1 of an irreducible plane curve from its char. exponents }
  G := SemiGroup(n, M); return JumpingNumbers(G);
end intrinsic;
