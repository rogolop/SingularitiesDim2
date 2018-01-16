import "SemiGroup.m": Euclides;

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
  for i in [1..g] do
    NNi := &*[N[j] : j in [1..i]];
    Si := [NNi] cat [ZZ | Q[j] * &*[ZZ | N[k] : k in [j+1..i]] : j in [1..i]];

    BSi := [<(M[i] + NNi + nu)/(N[i]*G[i+1]), nu> : nu in [0..N[i]*G[i+1] - 1] |
      Denominator(E[i]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1 and
      Denominator(G[i+1]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1];

    Gi := [ZZ!(g/E[i + 1]) : g in G[1..i + 1]];
    BStop := [<(M[i] + NNi + nu)/(N[i]*G[i+1]), nu> : nu in [0..N[i]*G[i+1] - 1] |
      Denominator(E[i]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1 and
      Denominator(G[i+1]*(M[i] + NNi + nu)/(N[i]*G[i+1])) ne 1 and
      SemiGroupMembership(nu, Gi)];
    BSan := SetToSequence(Set(BSi) diff Set(BStop));

    BS cat:= [BStop, BSan];
  end for; return BS;
end intrinsic;

function Multiplicity2(f, n)
  R := Parent(f); M := ideal<R | R.n>; N := 0; I := M;
  while NormalForm(f, I) eq 0 do I *:= M; N +:= 1; end while; return N;
end function;

intrinsic BSOneCharExp(a::RngIntElt, b::RngIntElt) -> []
{ TEST Random computations for the B-S polynomial in the one char exponent case TEST}
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
  f := y^a - x^b;// + &+[R | A.i * G(M[#M - i + 1]) : i in [1..#M]];
  print "Equation:";
  print "---------";
  print f;
  print "\n";

  print "Semigroup:";
  print "----------";
  print <a, b>;
  print "\n";

  // Construct blow-up
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
      XY := f2[1];
      Kpi := Determinant(JacobianMatrix([blw[1], blw[2]]));
      a1 := Degree(XY, 1); b1 := Degree(Kpi, 1);
      a2 := Degree(XY, 2); b2 := Degree(Kpi, 2);
      //print [<a1, b1>, <a2, b2>];
      //print blw;
      //print a1*(b2 + 1) - a2*(b1 + 1);
    elif Evaluate(f2[2], <0,0>) eq 0 then
      blw[1] := Evaluate(blw[1], blw2);
      blw[2] := Evaluate(blw[2], blw2);
      XY := f2[1];
      Kpi := Determinant(JacobianMatrix([blw[1], blw[2]]));
      a1 := Degree(XY, 1); b1 := Degree(Kpi, 1);
      a2 := Degree(XY, 2); b2 := Degree(Kpi, 2);
      //print [<a1, b1>, <a2, b2>];
      //print blw;
      //print a1*(b2 + 1) - a2*(b1 + 1);
    else
      Pi1 := <Evaluate(blw[1], blw2), Evaluate(blw[2], blw2)>;
      Pi2 := <Evaluate(blw[1], blw1), Evaluate(blw[2], blw1)>;
    end if;
  end while;

  print "Blow-up equations:";
  print "------------------";
  print Pi1;
  print Pi2;
  print "\n";

  // Resolve the semi-quasi-homogeneous.
  f1 := Evaluate(Q!f, <Pi1[1], Pi1[2]>);
  f2 := Evaluate(Q!f, <Pi2[1], Pi2[2]>);
  a := Multiplicity2(f1, 1); b := Multiplicity2(f1, 2);
  c := Multiplicity2(f2, 1); d := Multiplicity2(f2, 2);
  E1 := R.1^a * R.2^b; E2 := R.1^c * R.2^d;
  f1 := ExactQuotient(Evaluate(f, <G(Pi1[1]), G(Pi1[2])>), E1);
  f2 := ExactQuotient(Evaluate(f, <G(Pi2[1]), G(Pi2[2])>), E2);
  print "Strict transform & exceptional part:";
  print "------------------------------------";
  print <f1, E1>;
  print <f2, E2>;
  print "\n";

  return [];
end intrinsic;

intrinsic StudySingularity(G::[RngIntElt]) -> []
{ TEST Random Computations TEST }
  ZZ := IntegerRing(); RR := RealField(4); g := #G - 1;
  require IsPlaneCurveSemiGroup(G): "Argument must be a plane curve semigroup";
  C := CharExponents(G); n := C[1][2]; M := [C[i][1] : i in [2..#G]];
  P, e := ProximityMatrix(G); Pt := Transpose(P); v := e*Pt^-1; N := Ncols(P);
  k := Matrix(ZZ, [[1 : i in [1..N]]]); k := k*Pt^-1;

  // Numerical data
  Ei := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  n := G[1]; Ni := [0] cat [ZZ!(Ei[i] div Ei[i + 1]) : i in [1..g]];
  Mi := [0] cat [ZZ!(M[i]/Ei[i + 1]) : i in [1..g]];
  MMi := [ZZ!(G[i]/Ei[i]) : i in [1..#G]];
  Qi := [Mi[2]] cat [ZZ!((M[i + 1] - M[i])/Ei[i + 2]) : i in [1..g - 1]];
  nB := [Ni[i+1] * G[i+1] : i in [1..g]];

  print "\n";
  print "SemiGroup: ", G;
  print "Char. Exponents: ", <n, M>;
  print "Ei's: ", Ei, "Ni's: ", Ni;
  print "MMi's: ", MMi, "Mi's: ", Mi;
  print "Qi's: ", Qi, "nB's: ", nB, "\n";

  VS := RSpace(ZZ, N); isSat := &+[VS | Pt[i] : i in [1..N]]; R := [0];
  for p in [2..N] do // Construct the set of rupture points.
    // Points proximate to 'p' that are free.
    prox_p_free := [i : i in [p + 1..N] | Pt[p][i] eq -1 and isSat[i] ne -1];
    if (isSat[p] eq -1 and (#prox_p_free ge 1 or p eq N)) or
       (isSat[p] ne -1 and #prox_p_free ge 2) then R cat:= [p]; end if;
  end for;

  for i in [1..g] do // For each rupture divisor
    // Previous and current rupture points & Semigroup of the monomial curve.
    p0 := R[i] + 1; pi := R[i+1]; Gpi := <Ni[i+1], Qi[i]>;
    // Points that pi is proximate too, i.e., divisors cutting E_p_i.
    pi_prox := [k : k in [1..N] | P[pi][k] eq -1];
    // Resolution data of the two divisors cutting E_p_i.
    r1 := pi_prox[1]; v1 := v[1, r1]; k1 := k[1, r1];
    r2 := pi_prox[2]; v2 := v[1, r2]; k2 := k[1, r2];
    // Semigroups of the curvettes of the divisors cutting E_p_i.
    Pr1 := Submatrix(P, p0, p0, r1 - p0 + 1, r1 - p0 + 1);
    Gr1 := SemiGroup(Pr1 : UseExtraPoints := true);
    Pr2 := Submatrix(P, p0, p0, r2 - p0 + 1, r2 - p0 + 1);
    Gr2 := SemiGroup(Pr2 : UseExtraPoints := true);
    // Finally, data from the toric resolution morphism.
    H := Euclides(Qi[i], Ni[i+1])[1];
    if #H mod 2 eq 1 then
      AB := Gr1; CD := Gr2;
      if Qi[i] lt Ni[i+1] then a := AB[1]; b := AB[2]; d := CD[1]; c := CD[2];
      else a := AB[1]; b := AB[2]; c := CD[1]; d := CD[2]; end if;
    else
      AB := Gr2; CD := Gr1;
      tmp := v1; v1 := v2; v2 := tmp;
      tmp := k1; k1 := k2; k2 := tmp;
      if Qi[i] lt Ni[i+1] then b := AB[1]; a := AB[2]; c := CD[1]; d := CD[2];
      else a := AB[1]; b := AB[2]; c := CD[1]; d := CD[2]; end if;
    end if;


    print "Rupture divisor #", i, ":";
    print "------------------------";
    print "Resolution data: ", "<nb_i, k_p_i + 1> =", <nB[i], k[1, pi] + 1>, ",";
    print "\t\t  <v_1, k_1> =", <v1, k1>, ",", "<v_2, k_2> =", <v2, k2>;
    print "Monomial trans.: ", "<n_i, q_i> =", <Ni[i+1], Qi[i]>, ",";
    print "\t\t  <a, b> =", <a, b>, ",", "<c, d> =", <c, d>;

    print "Pole candidates:";
    for nu in [0..nB[i] - 1] do
      rho_nu := -(k[1, pi] + 1 + nu)/nB[i];
      eps1 := v1*rho_nu + k1; eps2 := v2*rho_nu + k2;
      print "<nu, rho> =", <nu, rho_nu>, ",", "<eps1, eps2, ei·sigma> =",
        <eps1, eps2, Ei[i + 1]*rho_nu>;
      if Denominator(eps2) eq 1 then print "***"; end if;

      assert(eps1 + 1 eq -a/Ni[i + 1]*nu + 1/Ni[i + 1]);
      assert(eps2 + 1 eq -(d + c*Ni[i]*MMi[i])/MMi[i + 1]*nu +
        (Mi[i] - Ni[i]*MMi[i] + &*Ni[2..i])/MMi[i + 1]);
      assert(eps1 + eps2 + Ei[i + 1]*rho_nu + nu + 2 eq 0);

      //if g eq 1 then
      //  C := SemiGroupCoord(nu + n*MMi[2], G);
      //  print <RR!a*nu/Ni[2],
      //            a*C[1][1] + b*C[1][2] - a*MMi[2],
      //        RR!a*nu/Ni[2] + 1 - 1/Ni[2]>;
      //  print <RR!d*nu/MMi[2],
      //            c*C[#C][1] + d*C[#C][2] - d*Ni[2],
      //         RR!d*nu/MMi[2] + 1 - 1/MMi[2]>;
      //end if;
      if g eq 2 and i eq g then
        C := SemiGroupCoord(nu + nB[i], G);
      //for cc in C do
      //  print <a*Ni[2]*cc[1] + a*MMi[2]*cc[2] +
      //    (a*Ni[2]*MMi[2] + b)*cc[3] - a*MMi[3], cc>;
      //  //print <c*Ni[2]*cc[1] + c*MMi[2]*cc[2] +
      //  //  (c*Ni[2]*MMi[2] + d)*cc[3] - (c*Ni[2]*MMi[2] + d)*Ni[3]>;
      //end for;
      end if;
    end for;
    print "\n";
  end for;

  return [];
end intrinsic;
