
intrinsic YanoExponents(n::RngIntElt, M::[RngIntElt]) -> RngSerPuisElt
{ Computes the generating sequence for the generic b-exponents
  of a characteristic sequence }
  G := SemiGroup(n, M);
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  M := [n] cat M;

  Rk := [i gt 1 select (E[i - 1] div E[i]) * (Self(i - 1) + M[i] - M[i - 1])
    else n : i in [1..#G]];
  rk := [(M[i] + n) div E[i] : i in [1..#G]];
  Rk_ := [n] cat [(Rk[i] * E[i]) div E[i - 1] : i in [2..#G]];
  rk_ := [2] cat [(rk[i] * E[i]) div E[i - 1] + 1 : i in [2..#G]];

  P<t> := PuiseuxSeriesRing(RationalField());
  s := &+[t^(rk[i]/Rk[i]) * (1 - t)/(1 - t^(1/Rk[i])) : i in [2..#Rk]] -
        &+[t^(rk_[i]/Rk_[i]) * (1 - t)/(1 - t^(1/Rk_[i])) :
            i in [1..#Rk_]] + t;
  return ChangePrecision(s, Infinity());
end intrinsic;

intrinsic MonomialCurve(G::[RngIntElt]) -> []
{ Computes the monomial curve assocaited to a semigroup of a
  plane curve }
require IsPlaneCurveSemiGroup(G): "G is not the semigroup of a plane curve";
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  N := [E[i - 1] div E[i] : i in [2..#G]];

  R := PolynomialRing(RationalField(), G); I := [R | ];
  AssignNames(~R, ["u" cat IntegerToString(i) : i in [0..#G - 1]]);
  for i in [1..#G - 1] do
    _, L_i := SemiGroupMembership(N[i] * G[i + 1], G[[1..i]]);
    I cat:= [R.(i + 1)^N[i] - &*[R.j^L_i[j] : j in [1..i]]];
  end for; return I;
end intrinsic;

intrinsic MonomialCurve(n::RngIntElt, M::[RngIntElt]) -> []
{ Computes the monomial curve associated to a characteristic sequence }
  G := SemiGroup(n, M);
  return MonomialCurve(G);
end intrinsic;

intrinsic DeformationCurve(G::[RngIntElt]) -> []
{ Computes the deformations of the monomial curve associated to the
  semigroup G }
  I := MonomialCurve(G); g := #I; R := Parent(I[1]);
  M := EModule(R, g); N := ideal<R | I> * M;
  J := Transpose(JacobianMatrix(I));
  T_1 := N + sub<M | [M ! m : m in RowSequence(J)]>;

  Groebner(T_1); LT := [LeadingTerm(m) : m in Basis(T_1)]; D_mu := [];
  for i in [1..g] do
    LT_i := ideal<R | [m[i] : m in LT | m[i] ne 0]>;
    M_i := [M.i * m : m in MonomialBasis(quo<R | LT_i>)];
    D_mu cat:= [m : m in M_i | Degree(m) gt Degree(I[i])];
  end for;

  RR := LocalPolynomialRing(RationalField(), Rank(R) + #D_mu, "lglex");
  AssignNames(~RR, ["v" cat IntegerToString(i) : i in [0..#D_mu - 1]] cat
                   ["u" cat IntegerToString(i) : i in [0..g]]);
  phi := hom<R -> RR | [RR.i : i in [#D_mu + 1..Rank(RR)]]>;
  II := [RR | phi(f) : f in I];
  for i in [1..#D_mu] do
    e_i := Column(D_mu[i]);
    II[e_i] +:= RR.i * phi(D_mu[i][e_i]);
  end for;

  return II;
end intrinsic;
