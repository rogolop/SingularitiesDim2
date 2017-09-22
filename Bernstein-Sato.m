intrinsic YanoExponents(n::RngIntElt, M::[RngIntElt]) -> RngSerPuisElt
{ Computes the generating sequence for the generic b-exponents
  of a characteristic sequence }
  G := SemiGroup(n, M); M := [n] cat M;
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];

  Rk := [i gt 1 select (E[i - 1] div E[i]) * (Self(i - 1) + M[i] - M[i - 1])
    else n : i in [1..#G]];
  rk := [(M[i] + n) div E[i] : i in [1..#G]];
  Rk_ := [n] cat [(Rk[i] * E[i]) div E[i - 1] : i in [2..#G]];
  rk_ := [2] cat [(rk[i] * E[i]) div E[i - 1] + 1 : i in [2..#G]];

  P<t> := PuiseuxSeriesRing(RationalField());
  s := &+[P | t^(rk[i]/Rk[i]) * (1 - t)/(1 - t^(1/Rk[i])) : i in [2..#Rk]] -
        &+[P | t^(rk_[i]/Rk_[i]) * (1 - t)/(1 - t^(1/Rk_[i])) :
          i in [1..#Rk_]] + t;
  return ChangePrecision(s, Infinity());
end intrinsic;

intrinsic YanoExponents(G::[RngIntElt]) -> RngSetPuisElt
{ Computes the generating sequence for the generic b-exponents
  of a semigroup }
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  N := [E[i - 1] div E[i] : i in [2..#G]]; g := #G - 1; n := G[1];
  M := CharExponents(G); M := [n] cat [m[1] : m in M[2..#M]];

  Rk := [n] cat [N[i - 1] * G[i] : i in [2..#G]];
  rk := [(M[i] + n) div E[i] : i in [1..#G]];
  Rk_ := G; rk_ := [2] cat [(rk[i] * E[i]) div E[i - 1] + 1 : i in [2..#G]];

  P<t> := PuiseuxSeriesRing(RationalField());
  s := &+[P | t^(rk[i]/Rk[i]) * (1 - t)/(1 - t^(1/Rk[i])) : i in [2..#Rk]] -
        &+[P | t^(rk_[i]/Rk_[i]) * (1 - t)/(1 - t^(1/Rk_[i])) :
          i in [1..#Rk_]] + t;
  return ChangePrecision(t^(g - 1)*s, Infinity());
end intrinsic;

intrinsic BernsteinSatoGeneric(G::[RngIntElt]) -> []
{ Returns the roots of the generic Bernstein-Sato }
  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  N := [E[i - 1] div E[i] : i in [2..#G]]; g := #G - 1; n := G[1];
  C := CharExponents(G); C := [n] cat [m[1] : m in C[2..#C]];
  ZZ := IntegerRing(); M := [ZZ | C[i]/E[i] : i in [2..#G]];
  Q := [M[1]] cat [M[i] - N[i]*M[i-1] : i in [2..g]];

  BS := [];
  for i in [2..g] do
    NNi := &*[N[j] : j in [1..i]];
    Si := [NNi] cat [ZZ | Q[j] * &*[ZZ | N[k] : k in [j+1..i]] : j in [1..i]];

    BSi := [(M[i] + NNi + nu)/(N[i]*G[i+1]) : nu in [0..N[i]*G[i+1] - 1] |
      Denominator(E[i]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1 and
      Denominator(G[i+1]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1];

    BStop := [(M[i] + NNi + nu)/(N[i]*G[i+1]) : nu in [0..N[i]*G[i+1] - 1] |
      Denominator(E[i]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1 and
      Denominator(G[i+1]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1 and
      SemiGroupMembership(nu, [10,15,36])];
    BSan := SetToSequence(Set(BSi) diff Set(BStop));

    BS cat:= [BStop, BSan];
  end for; return BS;
end intrinsic;

intrinsic BSOneCharExp(a::RngIntElt, b::RngIntElt) -> []
{ Random computations for the B-S polynomial in the one char exponent case }
require a lt b: "a < b please";
require Gcd(a, b) eq 1: "Gcd(a, b) must be equal to 1";
  // Initial ring for the quasi-homogeneous
  Q<x, y> := LocalPolynomialRing(Rationals(), 2);
  f0 := y^a - x^b; P := ProximityMatrix(f0);

  // Jacobian algebra monomial basis
  Jf := JacobianIdeal(f0); QJf := Q/Jf; F := hom<QJf -> Q | Q.1, Q.2>;
  M := [m : m in F(MonomialBasis(QJf)) | Exponents(m)[1]*a +
                                         Exponents(m)[2]*b gt a*b];
  T := [Exponents(m)[1]*a + Exponents(m)[2]*b - a*b : m in Reverse(M)];

  // Deformation ring
  A := PolynomialRing(Rationals(), #M);
  AssignNames(~A, ["a" cat IntegerToString(t) : t in T]);
  R<x, y> := PolynomialRing(A, [4, 9]); G := hom<Q -> R | R.1, R.2>;
  f := y^a - x^b + &+[R | A.i * G(M[#M - i + 1]) : i in [1..#M]];
  print "Equation:";
  print "---------";
  print f;
  print "\n";

  print "Semigroup:";
  print "----------";
  print <a, b>;
  print "\n";

  // Construct blow-up
  //k := Matrix(1, Ncols(P), [1 : i in [1..Ncols(P)]]);
  //k := k * Transpose(P)^-1; // Values for the K_\pi + 1
  //idx := [i : i in [1..Ncols(P)] | P[Ncols(P)][i] ne 0];
  blw2 := <Q.1, Q.1*Q.2>; blw1 := <Q.1*Q.2, Q.2>;
  f1 := <Q!1, f0>; f2 := <Q!1, f0>; blw := <Q.1, Q.2>;
  while Evaluate(f1[2], <0,0>) eq 0 or Evaluate(f2[2], <0,0>) eq 0 do
    if Evaluate(f1[2], <0,0>) ne 0 and Evaluate(f2[2], <0,0>) eq 0 then
      tmp := f1; f1 := f2; f2 := tmp;
    end if;
    n := Multiplicity(f1[2]);
    f2[1] := Evaluate(f1[1], blw2); f2[2] := Evaluate(f1[2], blw2);
    f1[1] := Evaluate(f1[1], blw1); f1[2] := Evaluate(f1[2], blw1);
    f2[1] *:= Q.1^n; f2[2] := ExactQuotient(f2[2], Q.1^n);
    f1[1] *:= Q.2^n; f1[2] := ExactQuotient(f1[2], Q.2^n);
    if Evaluate(f1[2], <0,0>) eq 0 then
      blw[1] := Evaluate(blw[1], blw1);
      blw[2] := Evaluate(blw[2], blw1);
    elif Evaluate(f2[2], <0,0>) eq 0 then
      blw[1] := Evaluate(blw[1], blw2);
      blw[2] := Evaluate(blw[2], blw2);
    else
      print "Blow-up equations:";
      print "------------------";
      print <Evaluate(blw[1], blw2), Evaluate(blw[2], blw2)>;
      print <Evaluate(blw[1], blw1), Evaluate(blw[2], blw1)>;
      print "\n";

      blw[1] := Evaluate(blw[1], blw2);
      blw[2] := Evaluate(blw[2], blw2);
    end if;
  end while;

  // Resolve the semi-quasi-homogeneous.
  E := G(f2[1]); f := ExactQuotient(Evaluate(f, <G(blw[1]), G(blw[2])>), E);
  print "Strict transform & exceptional part:";
  print "------------------------------------";
  print <f, E>;
  print "\n";

  // Topological roots
  TopRoots := [<(a + b + nu)/(a*b), nu> : nu in [0..a*b - 1] |
    SemiGroupMembership(nu, [a, b]) ];
  print "Topological roots:";
  print "------------------";
  print TopRoots;
  print "\n";

  return [];
end intrinsic;
