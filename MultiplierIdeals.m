import "ProximityMatrix.m": ProximityMatrixImpl;
import "IntegralClosure.m": IntegralClosureIrreducible, Unloading, ProductIdeals,
                            ClusterFactorization, Curvettes, GeneratorsOXD;

// Reference: D. Naie - Jumping numbers of a unibranch curve on a smooth surface
intrinsic JumpingNumbers(G::[RngIntElt]) -> []
{ Compute the Jumping Numbers < 1 of an irreducible plane curve
  from its semigroup }
  require IsPlaneCurveSemiGroup(G): "G must be the semigroup of a plane curve";

  E := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  RSet := func<p, q | [a*p+b*q : a in [1..q], b in [1..p] | a*p+b*q lt p*q]>;

  g := #G - 1; JN := [];
  for i in [1..g] do
    p := E[i] / E[i + 1]; q := G[i + 1] / E[i + 1]; R := RSet(p, q);
    Rmj := [k*p*q + alpha : k in [0..E[i+1] - 1], alpha in R];
    JN cat:= [[beta / Lcm(E[i], G[i + 1]) : beta in Sort(Rmj)]];
  end for; return JN;
end intrinsic;

// Reference: D. Naie - Jumping numbers of a unibranch curve on a smooth surface
intrinsic JumpingNumbers(n::RngIntElt, M::[RngIntElt]) -> []
{ Compute the Jumping Numbers < 1 of an irreducible plane curve from its
  char. exponents }
  G := SemiGroup(n, M); return JumpingNumbers(G);
end intrinsic;

intrinsic MultiplierIdeals(f::RngMPolLocElt) -> []
{ Computes the Multiplier Ideals and its assocaited Jumping number for a plane
  curve using the algorithm of Alberich-Àlvarez-Dachs }

  P, E, C := ProximityMatrix(f: Coefficients := true); QQ := Rationals();
  EQ := ChangeRing(E, QQ); PQ := ChangeRing(P, QQ); PQTinv := Transpose(PQ)^-1;
  N := Ncols(P); F := EQ*PQTinv; K := Matrix([[QQ | 1 : i in [1..N]]]);
  K := K * PQTinv;

  JN := 0; S := [];
  while JN lt 1 do
    D := Unloading(PQ, Matrix([[QQ | Floor(ei) : ei in Eltseq(JN*F - K)]]));
    lastJN := JN;
    JN, i := Min([(K[1][i] + 1 + D[1][i])/F[1][i] : i in [1..N]]);
    D := ChangeRing(D, IntegerRing());
    S cat:= [<lastJN, D, GeneratorsOXD(P, D, C, Parent(f))>];
  end while; return S;
end intrinsic;

intrinsic RuptureJumpingNumbers(G::[RngIntElt]) -> []
{ Compute the rupture jumping numbers of a plane branch }
  P, E := ProximityMatrix(G); QQ := Rationals(); ZZ := Integers();
  N := Ncols(P); P := ChangeRing(P, QQ); Pt := Transpose(P);
  E := ChangeRing(E, QQ); PTinv := Pt^-1; F := E*PTinv;
  K := Matrix([[QQ | 1 : i in [1..N]]]); K := K * PTinv;

  VS := RSpace(ZZ, N); R := []; isSat := &+[VS | Pt[i] : i in [1..N]];
  for p in [2..N] do // Construct the set of rupture points.
    // Points proximate to 'p' that are free.
    prox_p_free := [i : i in [p + 1..N] | Pt[p][i] eq -1 and isSat[i] ne -1];
    if (isSat[p] eq -1 and (#prox_p_free ge 1)) then R cat:= [p]; end if;
  end for; R cat:= [N];

  JN := [];
  Ei := [i gt 1 select Gcd(Self(i - 1), G[i]) else G[1] : i in [1..#G]];
  for i in [1..# G - 1] do
    JNi := 0; Si := []; r := R[i]; lct := (K[1][r] + 1)/F[1][r];
    Fi := Matrix([[QQ | 0 : j in [1..N]]]); Fi[1][r] := F[1][r];
    while JNi lt 1 + lct do
      D := Unloading(P, Matrix([[QQ | Floor(ei) : ei in Eltseq(JNi*Fi - K)]]));
      JNi := (K[1][r] + 1 + D[1][r])/F[1][r];
      if Denominator(Ei[i]*JNi) ne 1 and Denominator(G[i + 1]*JNi) ne 1 then
        Si cat:= [JNi];
      end if;
    end while; JN cat:= [Si[1..#Si - 1]];
  end for; return JN;
end intrinsic;
