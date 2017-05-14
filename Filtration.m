import "ProximityMatrix.m": ProximityMatrixImpl,
                            ProximityMatrixBranch,
                            MultiplicityVectorBranch,
                            CoefficientsVectorBranch;
import "IntegralClosure.m": IntegralClosureIrreducible,
                            Unloading, ProductIdeals,
                            ClusterFactorization, Curvettes;

FiltrationImpl := function(s, f, e, M)
  // Compute an upper bound for the necessary points.
  KK := (e*Transpose(e))[1][1]; N := Max(Ncols(e) + M - KK, Ncols(e));
  // Get the proximity matrix with all the necessary points.
  s := PuiseuxExpansionExpandReduced(s, f: Terms := M - KK - 1)[1];
  P := ProximityMatrixBranch(s, N); Pt := Transpose(P); Pt_inv := Pt^-1;
  e := MultiplicityVectorBranch(s, N); c := CoefficientsVectorBranch(s, N);

  // Compute the curvettes of the curve.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex");
  Cv := Curvettes(P, e*Pt_inv, c, Q);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, N); max[1][1] := 1; max := max*Pt_inv;

  // Construct the i-th cluster.
  e_i := ZeroMatrix(IntegerRing(), 1, N); m_i := 0; H := [];
  while m_i lt M do
    // Enlarge the previous cluster with one point on the curve.
    I := [i : i in [1..N] | e_i[1][i] eq 0][1];
    e_i[1][I] := 1; v_i := e_i*Pt_inv;
    // Unload K_i to get a strictly consistent cluster.
    v_i := Unloading(P, v_i); e_i := v_i*Pt;

    // Compute generators for the complete ideal H_i.
    H_i := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q) :
      v_j in ClusterFactorization(P, v_i)];
    H_i := [g[1] : g in ProductIdeals(H_i) |
      &or[g[2][1][i] lt (v_i + max)[1][i] : i in [1..N]]];

    // Fill the gaps in the filtration.
    KK_i := &+[e[i] * e_i[1][i] : i in [1..N]]; // Intersection [K, K_i]
    H cat:= [H_i]; m_i := KK_i;
  end while; return H;
end function;

// Helper funcition
ConvertToIdeal := func<I, Q | [&*[g[1]^g[2] : g in f] : f in I]>;

intrinsic Filtration(f::RngMPolLocElt, n::RngIntElt : Ideal := true) -> []
{ Returns a filtration by complete ideals of an irreducible
  plane curve up to autointersection n }
require n ge 0: "Second argument must be a non-negative integer";

  Q := Parent(f); S := PuiseuxExpansion(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  s := S[1][1]; f := S[1][3]; _, e, _ := ProximityMatrixImpl([<s, 1>]);
  KK := e[1]*Transpose(e[1]); // Curve auto-intersection.

  F := FiltrationImpl(s, f, e[1], n eq 0 select KK[1][1] else n);
  ConvertToIdeal := func<I, Q | [&*[g[1]^g[2] : g in f] : f in I]>;
  if Ideal eq true then return [ConvertToIdeal(I, Q) : I in F];
  else return F; end if;
end intrinsic;
