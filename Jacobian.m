import "ProximityMatrix.m": ProximityMatrixImpl, ProximityMatrixBranch,
                            MultiplicityVectorBranch, CoefficientsVectorBranch;
import "SemiGroup.m": TailExponentSeries;
import "IntegralClosure.m": IntegralClosureImpl, Unloading, CleanIdeal,
                            ClusterFactorization;

FiltrationImpl := function(s, f, M)
  // Compute the auto-intersection of the cluster of singular points K.
  e := ProximityMatrixImpl([<s, 1>])[2][1];
  KK := &+[ei*ei : ei in Eltseq(e)]; N := Ncols(e) + M - KK;
  // Get the proximity matrix with all the necessary points. (Upper bound)
  s := NewtonPuiseuxAlgorithmExpandReduced(s, f: Terms := M - KK - 1)[1];
  P := ProximityMatrixBranch(s, N); e := MultiplicityVectorBranch(s, N);
  c := CoefficientsVectorBranch(s, N); // N is the number of points needed.
  // The first ideals of the filtrations are the maximal ideal.
  R<x, y> := LocalPolynomialRing(RationalField(), 2, "lglex"); n := e[1];
  H := [ideal<R | x, y> : i in [1..n]]; I := [1]; m_i := n;
  e_i := Matrix(1, 1, [1]); ZZ := IntegerRing();
  // Construct the i-th cluster.
  while m_i lt M do
    // Enlarge the previous cluster with one point on the curve.
    I cat:= [I[#I] + 1]; P_i := Submatrix(P, I, I);
    e_i := InsertBlock(ZeroMatrix(ZZ, 1, #I), e_i, 1, 1);
    e_i[1][#I] := 1; v_i := e_i*Transpose(P_i)^-1;
    // Unload K_i to get a strictly consistent cluster.
    v_i := Unloading(P_i, v_i); e_i := v_i*Transpose(P_i);
    I := [i : i in [1..Ncols(P_i)] | e_i[1][i] ne 0]; P_i := Submatrix(P_i, I, I);
    e_i := Submatrix(e_i, [1], I); v_i := Submatrix(v_i, [1], I); c_i := c[I];
    // Get the intersection [K, K_i] & and the complete ideal H_i.
    KK_i := &+[e_i[1][j]*e[j] : j in [1..#I]];
    HH_i := [ IntegralClosureImpl(K_j[1], K_j[2], K_j[3], Parent(f)) :
      K_j in ClusterFactorization(P_i, v_i, c_i) ];
    H_i := CleanIdeal([j gt 1 select Self(j - 1)*HH_i[j]
      else HH_i[1] : j in [1..#HH_i]][#HH_i]);
    // Fill the gaps in the filtration.
    H cat:= [ideal<R | Basis(H_i)> : i in [1..Min(KK_i, M) - m_i]];
    m_i := KK_i;
  end while; return H;
end function;

intrinsic Filtration(f::RngMPolLocElt, n::RngIntElt: StdBasis := false) -> []
{ Returns a filtration by complete ideals of an irreducible
  plane curve up to multiplicity n. }
require Rank(Parent(f)) eq 2: "First argument must be a bivariate polynomial";
require n ge 0: "Second argument must be a non-negative integer";

  S := NewtonPuiseuxAlgorithm(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  s := S[1][1]; f := S[1][3]; e := ProximityMatrixImpl([<s, 1>])[2][1];
  KK := &+[ei*ei : ei in Eltseq(e)]; // Curve auto-intersection.

  F := FiltrationImpl(s, f, n eq 0 select KK else n);
  if StdBasis then return [ideal<Parent(Basis(F[1])[1]) | StandardBasis(F_i)>
    : F_i in F]; else return F; end if;
end intrinsic;

TjurinaFiltrationImpl := function(s, f, J)
  // Get the proximity matrix with all the necessary points.
  P := ProximityMatrixImpl([<s, 1>] : ExtraPoint := true, Coefficients := true);
  e := P[2][1]; c := P[3][1]; P := P[1]; M := CharExponents(s);
  // Compute the auto-intersection of the cluster of singular points K.
  KK := &+[ei*ei : ei in Eltseq(e)]; N := Ncols(P); K0K0 := KK;
  // The first ideals of the filtrations are the maximal ideal.
  R<x, y> := Parent(Basis(J)[1]); n := e[1][1];
  JJ := [J meet ideal<R | x, y> : i in [1..n]]; I := [1]; m_i := n;
  e_i := Matrix(1, 1, [1]); H_i := ideal<R | x, y>; ZZ := IntegerRing();
  // Construct the i-th cluster.
  while JJ[#JJ] ne H_i do
    // Enlarge the previous cluster with one point on the curve.
    I cat:= [I[#I] + 1]; P_i := Submatrix(P, I, I);
    e_i := InsertBlock(ZeroMatrix(ZZ, 1, #I), e_i, 1, 1);
    e_i[1][#I] := 1; v_i := e_i*Transpose(P_i)^-1;
    // Unload K_i to get a strictly consistent cluster.
    v_i := Unloading(P_i, v_i); e_i := v_i*Transpose(P_i);
    I := [i : i in [1..Ncols(P_i)] | e_i[1][i] ne 0]; P_i := Submatrix(P_i, I, I);
    e_i := Submatrix(e_i, [1], I); v_i := Submatrix(v_i, [1], I); c_i := c[I];
    // Get the intersection [K, K_i] & and the complete ideal H_i.
    KK_i := &+[e_i[1][j]*e[1][j] : j in [1..#I]];
    HH_i := [ IntegralClosureImpl(K_j[1], K_j[2], K_j[3], Parent(f)) :
      K_j in ClusterFactorization(P_i, v_i, c_i) ];
    H_i := ideal<R | Basis(CleanIdeal([j gt 1 select Self(j - 1)*HH_i[j]
      else HH_i[1] : j in [1..#HH_i]][#HH_i]))>;
    // Fill the gaps in the filtration.
    JJ cat:= [J meet H_i : i in [1..KK_i - m_i]]; m_i := KK_i;
    // Enlarge the base cluster K & recompute.
    if KK le KK_i then // Only compute Puiseux terms when strictly necessary
      if Numerator(Degree(s)) - M[#M][1] lt KK - K0K0 then
        s := NewtonPuiseuxAlgorithmExpandReduced(s, f : Polynomial := true);
        f := s[1][2]; s := s[1][1];
      end if;
      P := ProximityMatrixBranch(s, N + 1);
      c := CoefficientsVectorBranch(s, N + 1);
      e := [MultiplicityVectorBranch(s, N + 1)];
      KK := &+[ei*ei : ei in Eltseq(e[1])]; N := Ncols(P);
    end if;
  end while; return JJ;
end function;

intrinsic TjurinaFiltration(f::RngMPolLocElt: StdBasis := false) -> []
{ Computes a filtration adapted to the Tjurina algebra
  of an irreducible plane curve. }
require Rank(Parent(f)) eq 2: "First argument must be a bivariate polynomial";
  R<x, y> := LocalPolynomialRing(RationalField(), 2, "lglex");
  Jf := ideal<R | Derivative(f, 1), Derivative(f, 2), f>;

  S := NewtonPuiseuxAlgorithm(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  s := S[1][1]; f := S[1][3]; e := ProximityMatrixImpl([<s, 1>])[2][1];
  c := &+[ei*(ei - 1) : ei in Eltseq(e)]; G := SemiGroup(s);

  F := TjurinaFiltrationImpl(s, f, Jf); F := F[(c + Min(G[1], G[2]) - 1)..#F];
  if StdBasis then return [ideal<Parent(Basis(F[1])[1]) | StandardBasis(F_i)>
    : F_i in F]; else return F; end if;
end intrinsic;

intrinsic TjurinaGaps(f::RngMPolLocElt) -> []
{ Returns the set of Tjurina gaps of an irreducible plane curve. }
require Rank(Parent(f)) eq 2: "First argument must be a bivariate polynomial";

  F := TjurinaFiltration(f);
  return <[i - 1 : i in [1..#F-1] | F[i] eq F[i + 1]], #F>;
end intrinsic;
