//intrinsic FTFiltration(f::RngMPolLocElt) -> []
//{ }
//require CoefficientRing(Parent(f)) eq RationalField():
//  "Argument must be a rational bivariate polynomial";
//  H := Filtration(f, 0); m := 46;
//  P<p> := PolynomialRing(RationalField());
//  for H_i in H do
//    P1 := [p : p in PrimesInInterval(m, m * m) | p mod m eq 1][[1..3]];
//    R := LocalPolynomialRing(FiniteField(P1[1]), 2);
//    ft11 := FThresholdE1(R!f, ConvertToIdeal(H_i, R));
//    R := LocalPolynomialRing(FiniteField(P1[2]), 2);
//    ft12 := FThresholdE1(R!f, ConvertToIdeal(H_i, R));
//    R := LocalPolynomialRing(FiniteField(P1[3]), 2);
//    ft13 := FThresholdE1(R!f, ConvertToIdeal(H_i, R));
//    nu11 := (ft11 - ft12)/(P1[1] - P1[2])*p +
//      (ft11 - (ft11 - ft12)/(P1[1] - P1[2])*P1[1]);
//    nu12 := (ft12 - ft13)/(P1[2] - P1[3])*p +
//      (ft12 - (ft12 - ft13)/(P1[2] - P1[3])*P1[2]);
//    nu13 := (ft13 - ft11)/(P1[3] - P1[1])*p +
//      (ft13 - (ft13 - ft11)/(P1[3] - P1[1])*P1[3]);
//    print H_i;
//    print P1[1]; print P1[2]; print P1[3];
//    print nu11; print nu12; print nu13;
//    //assert(nu11 eq nu12);
//    P2 := [p : p in PrimesInInterval(m, m * m) | p mod m eq m - 1][[1..3]];
//    R := LocalPolynomialRing(FiniteField(P2[1]), 2);
//    ft21 := FThresholdE1(R!f, ConvertToIdeal(H_i, R));
//    R := LocalPolynomialRing(FiniteField(P2[2]), 2);
//    ft22 := FThresholdE1(R!f, ConvertToIdeal(H_i, R));
//    R := LocalPolynomialRing(FiniteField(P2[3]), 2);
//    ft23 := FThresholdE1(R!f, ConvertToIdeal(H_i, R));
//  end for; return [];
//end intrinsic;

// Modular exponentiation of f^n mod I decomposing n mod p with memoization.
ModularExp := procedure(f, n, p, ~I, ~M)
  g := Parent(f)!1; m := 0; i := 1;
  if M[1] eq -1 then M[1] := NormalForm(f, I); end if; f := M[1];
  while n gt 0 do
    if n mod p ne 0 then
      n_p := n mod p; m +:= i * n_p;
      if M[m] eq -1 then M[m] := NormalForm(g * f^n_p, I); end if; g := M[m];
    end if;
    n div:= p; i *:= p;
    if M[i] eq -1 then M[i] := NormalForm(f^p, I); end if; f := M[i];
  end while;
end procedure;

intrinsic Nu(f::RngMPolLocElt, I::RngMPolLoc : e := 1) -> RngIntElt
{ Computes the nu value of f with respect to the ideal I }
  R := Parent(f); p := Characteristic(CoefficientRing(R));
  q := Characteristic(CoefficientRing(I));
require p gt 0 and q gt 0: "Computations only valid over finite fields";
require p eq q: "Arguments defined over different finite fields";
require NormalForm(f, I) eq 0: "First argument must be contained in I";
require Basis(I)[1] ne 1 and Gcd(Basis(I)) eq 1: "Second argument must be an m-primary ideal";
  Ip := ideal<R | [g^(p^e) : g in Basis(I)]>;
  bottom := 0; top := p; mid := p^e div 2;
  M := [R | -1 : i in [1..2^Ceiling(Log(2, p^e))]];
  while top - 1 gt bottom do
    ModularExp(f, mid, 2, ~Ip, ~M); alpha := M[mid];
    if alpha ne 0 then bottom := mid; else top := mid; end if;
    mid := (bottom + top) div 2;
  end while; return mid;
end intrinsic;
