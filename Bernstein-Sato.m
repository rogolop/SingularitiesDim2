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
  print f;

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
      blw[1] := Evaluate(blw[1], blw1);
      blw[2] := Evaluate(blw[2], blw1);
    end if;
  end while;

  // Resolve the semi-quasi-homogeneous.
  E := G(f1[1]); f := ExactQuotient(Evaluate(f, <G(blw[1]), G(blw[2])>), E);
  print <f, E>;
  print blw;

  // Topological roots
  TopRoots := [<(a + b + nu)/(a*b), nu> : nu in [0..a*b - 1] |
    SemiGroupMembership(nu, [a, b]) ];
  print TopRoots;

  return [];
end intrinsic;
