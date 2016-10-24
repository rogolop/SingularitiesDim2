import "ProximityMatrix.m": ProximityMatrixImpl, ProximityMatrixBranch,
                            MultiplicityVectorBranch, CoefficientsVectorBranch;
import "IntegralClosure.m": IntegralClosureIrreducible, Unloading, ProductIdeals,
                            ClusterFactorization, Curvettes;

FiltrationImpl := function(s, f, e, M)
  // Compute an upper bound for the necessary points.
  KK := (e*Transpose(e))[1][1]; N := Ncols(e) + M - KK;
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
    H cat:= [H_i : i in [1..Min(KK_i, M) - m_i]]; m_i := KK_i;
  end while; return H;
end function;

intrinsic Filtration(f::RngMPolLocElt, n::RngIntElt) -> []
{ Returns a filtration by complete ideals of an irreducible
  plane curve up to multiplicity n }
require Rank(Parent(f)) eq 2: "First argument must be a bivariate polynomial";
require n ge 0: "Second argument must be a non-negative integer";

  S := PuiseuxExpansion(f: Polynomial := true);
  if #S gt 1 or S[1][2] gt 1 then error "the curve must be irreducible"; end if;
  s := S[1][1]; f := S[1][3]; _, e, _ := ProximityMatrixImpl([<s, 1>]);
  KK := e[1]*Transpose(e[1]); // Curve auto-intersection.

  return FiltrationImpl(s, f, e[1], n eq 0 select KK[1][1] else n);
end intrinsic;

intrinsic MultiplierIdeals(f::RngMPolLocElt, n::RngIntElt) -> []
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

function ConvertToIdeal(I, Q)
  return ideal<Q | [&*[f_i[1]^f_i[2] : f_i in f] : f in I]>;
end function;

intrinsic Traces(f::RngMPolLocElt, n::RngIntElt, C::MonStgElt, I::MonStgElt) -> []
{ Take traces... }
require Rank(Parent(f)) eq 2: "First argument must be a bivariate polynomial";
require n ge 0: "Second argument must be a non-negative integer";
  Q := Parent(f);

  if C eq "Filtration" then C := Filtration(f, n);
  elif C eq "Multiplier" then C := MultiplierIdeals(f, n);
  else error "Unrecognized chain"; end if;

  if I eq "Jacobian" then I := ideal<Q | f, Derivative(f, 1), Derivative(f, 2)>;
  elif I eq "Gradient" then I := ideal<Q | Derivative(f, 1), Derivative(f, 2)>;
  elif I eq "Maximal" then I := ideal<Q | Q.1, Q.2>;
  else error "Unrecognized ideal"; end if;

  T := [ConvertToIdeal(Ci, Q) meet I : Ci in C];
  return [i : i in [1..#T - 1] | T[i] eq T[i + 1]];
end intrinsic;

//intrinsic ModularPower(f::RngMPolLocElt, n::RngIntElt, I::RngMPolLoc)
//  -> RngMPolLocElt
//{ Returns f^n mod I }
//  p := Characteristic(CoefficientRing(Parent(f)));
//require p gt 0: "Computations only valid over finite fields";
//require n ge 0: "Second argument must be a non-negative integer";
//  g := 1; f := NormalForm(f, I);
//  while n gt 0 do
//    if n mod p ne 0 then g := NormalForm(g * f^(n mod p), I); end if;
//    n div:= p; f := NormalForm(f^p, I);
//  end while; return g;
//end intrinsic;
//
//intrinsic ModularPowerBinary(f::RngMPolLocElt, n::RngIntElt, I::RngMPolLoc)
//  -> RngMPolLocElt
//{ Returns f^n mod I }
//require n ge 0: "Second argument must be a non-negative integer";
//  g := 1; f := NormalForm(f, I);
//  while n gt 0 do
//    if n mod 2 ne 0 then g := NormalForm(g * f, I); end if;
//    n div:= 2; f := NormalForm(f * f, I);
//  end while; return g;
//end intrinsic;
