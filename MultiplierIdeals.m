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
  curve using the algorithm from Alberich-Àlvarez-Dachs }

  P, E, C := ProximityMatrix(f: Coefficients := true); QQ := Rationals();
  EQ := ChangeRing(E, QQ); PQ := ChangeRing(P, QQ); PQTinv := Transpose(PQ)^-1;  N := Ncols(P); F := EQ*PQTinv; K := Matrix([[QQ | 1 : i in [1..N]]]);
  K := K * PQTinv;

  JN := 0; S := [];
  while JN lt 1 do
    D := Unloading(PQ, Matrix([[QQ | Floor(ei) : ei in Eltseq(JN*F - K)]]));
    lastJN := JN;
    JN := Min([(K[1][i] + 1 + D[1][i])/F[1][i] : i in [1..N]]);
    D := ChangeRing(D, IntegerRing());
    S cat:= [<lastJN, D, GeneratorsOXD(P, D, C, Parent(f))>];
  end while; return S;
end intrinsic;

intrinsic MultiplierIdealsTest(f::RngMPolLocElt) -> []
{ Test }

  P, E := ProximityMatrix(f); QQ := Rationals(); N := Ncols(P);
  P := ChangeRing(P, QQ); E := ChangeRing(E, QQ); PTinv := Transpose(P)^-1;
  F := E*PTinv; K := Matrix([[QQ | 1 : i in [1..N]]]); K := K * PTinv;


  FF := Matrix([[QQ | 0 : i in [1..N]]]);
  KK := Matrix([[QQ | 0 : i in [1..N]]]);
  //N := 3;
  FF[1][N] := F[1][N];
  KK[1][N] := KK[1][N];
  //FF[1][N-1] := F[1][N-1];
  //FF[1][4] := F[1][4];

  //FF := F;

  print FF;

  JN := 0; S := [];
  while JN lt 1 do
    D := Unloading(P, Matrix([[QQ | Floor(ei) : ei in Eltseq(JN*FF - K)]]));
    JN := Min([(K[1][i] + 1 + D[1][i])/FF[1][i] : i in [1..N] | FF[1][i] ne 0]);
    //JN := (K[1][N] + 1 + D[1][N])/FF[1][N];
    S cat:= [JN];
  end while; return S;
end intrinsic;
