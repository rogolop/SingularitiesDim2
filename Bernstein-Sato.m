import "SemiGroup.m": Euclides;

intrinsic BExponents(n::RngIntElt, M::[RngIntElt]) -> RngSerPuisElt
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

intrinsic BExponents(G::[RngIntElt]) -> RngSetPuisElt
{ Computes the generating sequence for the generic b-exponents
  of a semigroup }
    C := CharExponents(G); n := C[1][2]; C := [C[i][1] : i in [2..#C]];
    return BExponents(n, C);
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

intrinsic StudySingularity(G::[RngIntElt]) -> []
{ Shows all the invariants associated to a plane curve singularity
  with semigroup G }
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
    end for;
    print "\n";
  end for;

  return [];
end intrinsic;

intrinsic StudySingularity2(G::[RngIntElt]) -> []
{ Shows all the invariants associated to a plane curve singularity
  with semigroup G }
  ZZ := IntegerRing(); RR := RealField(4); g := #G - 1;
  require IsPlaneCurveSemiGroup(G): "Argument must be a plane curve semigroup";
  C := CharExponents(G); n := C[1][2]; M := [C[i][1] : i in [2..#G]];
  P, e := ProximityMatrix(G : ExtraPoint := true);
  Pt := Transpose(P); vF := e*Pt^-1;
  N := Ncols(P); vK := Matrix(ZZ, [[1 : i in [1..N]]]); vK := vK*Pt^-1;
  P_inv := P^-1; Pt_inv := Transpose(P_inv); N := Ncols(P);
  E := -Transpose(P)*P;

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

  // 'Curvette' points are always free.
  freePoints := [p : p in [1..N] | isSat[p] eq 0]; curvPoints := [1];
  for p in freePoints do
    // Points proximate to 'p'.
    prox_p := [i : i in [p + 1..N] | Pt[p][i] eq -1];
    // Points proximate to 'p' that are satellites.
    prox_p_sat := [q : q in prox_p | isSat[q] eq -1];
    // Select 'p' is if it has no proximate points in K (dead end) or
    // all its proximate points in K are satellite (rupture point).
    if #prox_p eq 0 or #prox_p eq #prox_p_sat then
      curvPoints cat:= [p]; end if;
  end for; MaxContact := [];
  for p in curvPoints do
    i_p := ZeroMatrix(IntegerRing(), 1, N); i_p[1][p] := 1;
    e_p := i_p*P_inv; Ip := [i : i in [1..N] | e_p[1][i] ne 0];
    v_p := e_p*Pt_inv; MaxContact cat:= [v_p];
  end for;
  print MaxContact;

  for i in [1..g] do // For each rupture divisor
    // Current rupture points
    pi := R[i+1];
    // Points that pi is proximate too, i.e., divisors cutting E_p_i.
    pi_prox := [k : k in [1..N] | E[pi][k] eq 1];

    print i;
    print "Topological roots candidates:";

    Gi := G[1..i+1]; d := Gcd(Gi); Gi := [ZZ!(gi / d) : gi in Gi];
    GiVals := [nu : nu in [0..2*nB[i] - 1] | SemiGroupMembership(nu, Gi)];
    for nu in GiVals do
      for C in SemiGroupCoord(nu, Gi) do
      print C;
        vNu := &+[MaxContact[j]*C[j] : j in [1..#C]];
        sigmaNu := -(vNu[1, pi] + vK[1, pi] + 1)/vF[1, pi];
        eps1 := vF[1, pi_prox[1]] * sigmaNu + vNu[1, pi_prox[1]] +
          vK[1, pi_prox[1]];
        eps2 := vF[1, pi_prox[2]] * sigmaNu + vNu[1, pi_prox[2]] +
          vK[1, pi_prox[2]];
        eps3 := vF[1, pi_prox[3]] * sigmaNu + vNu[1, pi_prox[3]] +
          vK[1, pi_prox[3]];
        print <nu, sigmaNu>, <eps1, eps2, eps3>, eps1 + eps2 + eps3;
        print <vNu[1, pi_prox[1]], vNu[1, pi_prox[2]], vNu[1, pi_prox[3]]>;
      end for;

      print "\n";
    end for;

    //  rho_nu := -(k[1, pi] + 1 + nu)/nB[i];
    //  eps1 := v1*rho_nu + k1; eps2 := v2*rho_nu + k2;
    //  print "<nu, rho> =", <nu, rho_nu>, ",", "<eps1, eps2, ei·sigma> =",
    //    <eps1, eps2, Ei[i + 1]*rho_nu>;
    //  if Denominator(eps2) eq 1 then print "***"; end if;

    //  assert(eps1 + 1 eq -a/Ni[i + 1]*nu + 1/Ni[i + 1]);
    //  assert(eps2 + 1 eq -(d + c*Ni[i]*MMi[i])/MMi[i + 1]*nu +
    //    (Mi[i] - Ni[i]*MMi[i] + &*Ni[2..i])/MMi[i + 1]);
    //  assert(eps1 + eps2 + Ei[i + 1]*rho_nu + nu + 2 eq 0);
    //end for;
  end for;

  return [];
end intrinsic;

function PartialBellPolynomialImpl(n, k, R)
  if n eq 0 and k eq 0 then return R!1; end if;
  if n eq 0 or k eq 0 then return R!0; end if;
  return &+ [ Binomial(n - 1, i - 1) * R.i *
    PartialBellPolynomialImpl(n - i, k - 1, R) : i in [1..n - k + 1] ];
end function;

intrinsic PartialBellPolynomial(n::RngIntElt, k::RngIntElt) -> RngPolElt
{ Computes the (n, k) partial Bell polynomial }
  R := PolynomialRing(Rationals(), n - k + 1);
  return PartialBellPolynomialImpl(n, k, R);
end intrinsic;

function DerivativeSPower(f, nu, sigma)
  R := Parent(f);
  return [ Evaluate(Derivative(f, i, 1), <0, R.2>) : i in [0..nu] ];
end function;

intrinsic StratificationBSOneCharExp(a::RngIntElt, b::RngIntElt) -> [ ]
{ Computes the stratification for the Bernstein-Sato polynomial of a plane
  curve with one characteristic exponent }
require a lt b: "a < b please";
require Gcd(a, b) eq 1: "Gcd(a, b) must be equal to 1";
  // Initial ring for the quasi-homogeneous
  Q<x, y> := LocalPolynomialRing(Rationals(), 2);
  f0 := y^a - x^b;

  // Jacobian algebra monomial basis
  Jf := JacobianIdeal(f0); QJf := Q/Jf; F := hom<QJf -> Q | Q.1, Q.2>;
  M := [m : m in F(MonomialBasis(QJf)) | Exponents(m)[1]*a +
                                         Exponents(m)[2]*b gt a*b];
  T := [Exponents(m)[1]*a + Exponents(m)[2]*b - a*b : m in Reverse(M)];

  // Deformation ring
  A := PolynomialRing(Rationals(), #M);
  AssignNames(~A, ["t" cat IntegerToString(t) : t in T]);
  R<x, y> := PolynomialRing(A, [a, b]); G := hom<Q -> R | R.1, R.2>;
  f := y^a - x^b + &+[R | A.i * G(M[#M - i + 1]) : i in [1..#M]];

  n := a; q := b;
  // Monomial resolution
  _, a, b := Xgcd(-q, n);
  _, c, d := Xgcd(q, -n);
  if a lt 0 and b lt 0 then a := a + n; b := b + q; end if;
  if c lt 0 and d lt 0 then c := c + n; d := d + q; end if;
  f := ExactQuotient(Evaluate(f, <x^n*y^c, x^q*y^d>), x^(n*q)*y^(n*d));
  print f;

  N := #[ nu : nu in [0..n*q] | not SemiGroupMembership(nu, [n, q]) and
    not Denominator(n*(n + q + nu)/(n*q)) eq 1 and
    not Denominator(q*(n + q + nu)/(n*q)) eq 1 ];
  print N;

  // For each candidate pole
  for nu in [0..n*q] do
    // Check if the candidate is analytic
    sigma := -(n + q + nu)/(n*q);
    if not SemiGroupMembership(nu, [n, q]) and
       not Denominator(n*sigma) eq 1 and
       not Denominator(q*sigma) eq 1 then
      print "---------> ", <nu, sigma>;
      // For each Dirac's delta in the basis
      for K in [<k1, k2> : k1 in [0..N], k2 in [0..N]] do
        k1 := K[1]; k2 := K[2];
        if k1*n + k2*q le nu then
          print "Dirac: ", K;
          print Binomial(nu, k1*n + k2*q)*y^(c*k1 + d*k2);
        end if;
      end for;
    end if;
  end for;

  return [];
end intrinsic;
