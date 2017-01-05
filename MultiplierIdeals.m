import "ProximityMatrix.m": ProximityMatrixImpl;
import "IntegralClosure.m": IntegralClosureIrreducible, Unloading, ProductIdeals,
                            ClusterFactorization, Curvettes;

// TODO: Change irreducible curve by simple ideal?
intrinsic MultiplierChain(f::RngMPolLocElt, n::RngIntElt) -> []
{ Returns the chain of multiplier ideals associated to an irreducible plane curve }
require Rank(Parent(f)) eq 2: "First argument must be a bivariate polynomial";
require n ge 0: "Second argument must be a non-negative integer";

  S := PuiseuxExpansion(f);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  P, e, c := ProximityMatrixImpl([<S[1][1], 1>]);
  Pt := Transpose(P); e := e[1]; c := c[1];
  N := Ncols(P); KK := e*Transpose(e); // Curve auto-intersection.
  if n eq 0 then n := KK[1][1]; end if;

  // Compute the curvettes of the curve.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex");
  Cv := Curvettes(P, e[1]*Pt^-1, c, Q);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, N); max[1][1] := 1; max := max*Pt^-1;

  v_i := ZeroMatrix(IntegerRing(), 1, N); m_i := 0; J := [];
  while m_i lt n do
    // Enlarge the values of the previos cluster.
    v_i[1][N] +:= 1; v_i := Unloading(P, v_i); e_i := v_i*Pt;

    // Compute generators for the complete ideal J_i.
    J_i := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q) :
      v_j in ClusterFactorization(P, v_i)];
    J_i := [g[1] : g in ProductIdeals(J_i) |
      &or[g[2][1][i] lt (v_i + max)[1][i] : i in [1..N]]];

    // Fill the gaps in the filtration.
    KK_i := &+[e[1][i] * e_i[1][i] : i in [1..N]]; // Intersection [K, K_i]
    J cat:= [J_i : i in [1..Min(KK_i, n) - m_i]]; m_i := KK_i;
  end while;

  return J;
end intrinsic;

