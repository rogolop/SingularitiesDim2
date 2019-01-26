import "ProximityMatrix.m": ProximityMatrixImpl,
                            ProximityMatrixBranch,
                            MultiplicityVectorBranch,
                            CoefficientsVectorBranch;
import "IntegralClosure.m": IntegralClosureIrreducible,
                            Unloading, ProductIdeals,
                            ClusterFactorization, Curvettes;
import "BasePoints.m": ExpandWeightedCluster;
import "SemiGroup.m": TailExponentSeries;

// Helper funcition
ConvertToIdeal := func<I, Q | [&*[g[1]^g[2] : g in f] : f in I]>;

FiltrationRuptureImpl := function(P, e, c, i, niBi)
  // Compute the curvettes of the curve.
  Q<x, y> := LocalPolynomialRing(Parent(c[1][2]), 2, "lglex"); ZZ := Integers();
  Pt := Transpose(P); Pt_inv := Pt^-1;
  Cv := Curvettes(P, e*Pt_inv, c, Q); N := Ncols(P);
  // Compute the maximal ideal values.
  max := ZeroMatrix(IntegerRing(), 1, N); max[1][1] := 1; max := max*Pt_inv;

  // Compute the position of the i-th rupture divisor.
  VS := RSpace(ZZ, N); isSat := &+[VS | Pt[i] : i in [1..N]]; R := [];
  for p in [2..N] do // Construct the set of rupture points.
    // Points proximate to 'p' that are free.
    prox_p_free := [i : i in [p + 1..N] | Pt[p][i] eq -1 and isSat[i] ne -1];
    if (isSat[p] eq -1 and (#prox_p_free ge 1 or p eq N)) or
       (isSat[p] ne -1 and #prox_p_free ge 2) then R cat:= [p]; end if;
  end for; Ri := R[i];

  // Construct the i-th cluster.
  vi := ZeroMatrix(IntegerRing(), 1, N); H := [];
  while vi[1][Ri] lt niBi do
    // Unload K_i to get a strictly consistent cluster.
    vi[1][Ri] +:= 1; vi := Unloading(P, vi);

    // Compute generators for the complete ideal H_i.
    Hi := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q) :
      v_j in ClusterFactorization(P, vi)];
    Hi := [g[1] : g in ProductIdeals(Hi) |
      &or[g[2][1][i] lt (vi + max)[1][i] : i in [1..N]]];
    H cat:= [<Hi, vi[1][Ri]>];
  end while; return H;
end function;

intrinsic FiltrationRupture(f::RngMPolLocElt, i::RngIntElt : N := -1, Ideal := true) -> []
{ Returns a filtration by complete ideals of an irreducible
  plane curve associated to the i-th rupture divisor }
require i gt 0: "Second argument must be a positive integer";

  Q := Parent(f); S := PuiseuxExpansion(f: Polynomial := true); ZZ := Integers();
  if #S gt 1 or S[1][2] gt 1 then error "The curve must be irreducible"; end if;
  s := S[1][1]; P, e, c := ProximityMatrixImpl([<s, 1>]); G := SemiGroup(P);
  if i gt #G - 1 then error "Rupture divisor index too large"; end if;
  Ei := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  n := G[1]; Ni := [0] cat [ZZ!(Ei[i] div Ei[i + 1]) : i in [1..#G - 1]];
  if N lt 0 then N := Ni[i + 1] * G[i + 1]; end if;

  F := FiltrationRuptureImpl(P, e[1], c[1], i, N);
  if Ideal eq true then return [<ConvertToIdeal(I[1], Q), I[2]> : I in F];
  else return F; end if;
end intrinsic;

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
  ei := ZeroMatrix(IntegerRing(), 1, N); m_i := 0; H := [];
  while m_i lt M do
    // Get the last points with multiplicity zero.
    I := [i : i in [1..N] | ei[1][i] eq 0][1];
    ei[1][I] := 1; vi := ei*Pt_inv;
    // Unload K_i to get a strictly consistent cluster.
    vi := Unloading(P, vi); ei := vi*Pt;

    // Compute generators for the complete ideal H_i.
    Hi := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q) :
      v_j in ClusterFactorization(P, vi)];
    Hi := [g[1] : g in ProductIdeals(Hi) |
      &or[g[2][1][i] lt (vi + max)[1][i] : i in [1..N]]];

    // Fill the gaps in the filtration.
    KK_i := &+[e[i] * ei[1][i] : i in [1..N]]; // Intersection [K, K_i]
    H cat:= [<Hi, KK_i>]; m_i := KK_i;
  end while; return H;
end function;

intrinsic Filtration(f::RngMPolLocElt : N := -1, Ideal := true) -> []
{ Returns a filtration by complete ideals of an irreducible
  plane curve up to autointersection n }

  Q := Parent(f); S := PuiseuxExpansion(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  s := S[1][1]; f := S[1][3]; _, e, _ := ProximityMatrixImpl([<s, 1>]);
  KK := e[1]*Transpose(e[1]); // Curve auto-intersection.

  F := FiltrationImpl(s, f, e[1], N lt 0 select KK[1][1] else N);
  if Ideal eq true then return [<ConvertToIdeal(I[1], Q), I[2]> : I in F];
  else return F; end if;
end intrinsic;

TjurinaFiltrationImpl := function(S, f)
  // Get the proximity matrix with all the necessary points.
  P, E, C := ProximityMatrixImpl(S); N := NumberOfColumns(P);
  Pt := Transpose(P); Pt_inv := Pt^-1; R := Parent(f);
  // The Tjurina ideal & its standard basis.
  J := JacobianIdeal(f) + ideal<R | f>; J := ideal<R | StandardBasis(J)>;

  // Compute the curvettes of the curve.
  A := Parent(C[1][1][2]); Q := LocalPolynomialRing(A, 2, "lglex");
  vi := E[1]*Pt_inv; Cv := Curvettes(P, vi, C[1], Q); ZZ := IntegerRing();
  // Add the curve itself as a curvette.
  Cvf := <[<Q!f, 1>], vi, E[1]>; Cv cat:= [Cvf];
  // Compute the maximal ideal values.
  max := ZeroMatrix(ZZ, 1, N); max[1][1] := 1; max := max*Pt_inv;

  // Construct the i-th cluster.
  ei := ZeroMatrix(ZZ, 1, N); JJ := []; Hi := ideal<R | 1>; Ji := Hi meet J;
  while Hi ne Ji do
    // Enlarge, if necessary, the cluster with one point on the curve.
    I := [i : i in [1..N] | ei[1][i] eq 0];
    if #I eq 0 then
      ExpandWeightedCluster(~P, ~E, ~C, ~S, -1); N := N + 1; P[N][N - 1] := -1;
      E[1][1][N] := 1; ei := E[1]; Pt := Transpose(P); Pt_inv := Pt^-1;
      // Expand (i.e. blow-up an extra point) the maximal ideal.
      max := ZeroMatrix(ZZ, 1, N); max[1][1] := 1; max := max*Pt_inv;

      newCv := []; // Expand (i.e. blow-up an extra points) the curvettes.
      for i in [1..#Cv] do
        Ei := InsertBlock(ZeroMatrix(ZZ, 1, N), Cv[i][3], 1, 1);
        if i eq #Cv then Ei[1][N] := 1; end if; // The last curvette is f.
        newCv cat:= [<Cv[i][1], Ei*Pt_inv, Ei>];
      end for; Cv := newCv;
    else ei[1][I[1]] := 1; end if;

    // Unload K_i to get a strictly consistent cluster.
    vi := ei*Pt^-1; vi := Unloading(P, vi); ei := vi*Pt;

    // Compute generators for the complete ideal H_i.
    Hi := [IntegralClosureIrreducible(P, P*Transpose(v_j), v_j, Cv, max, Q)
      : v_j in ClusterFactorization(P, vi)];
    Hi := [g[1] : g in ProductIdeals(Hi) | &or[g[2][1][i] lt
      (vi + max)[1][i] : i in [1..N]]];
    Hi := ideal<R | ConvertToIdeal(Hi, R)>; Ji := Hi meet J;
    JJ cat:= [<Ji, vi[1][Ncols(vi)]>];
  end while; return JJ;
end function;

intrinsic TjurinaFiltration(f::RngMPolLocElt) -> []
{ Returns an adapted filtration of the Tjurinna ideal of an irreducible
  plane curve }

  Q := Parent(f); S := PuiseuxExpansion(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  return TjurinaFiltrationImpl(S, f);
end intrinsic;
