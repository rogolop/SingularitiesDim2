Euclides := function(m, n)
  hs := []; ns := [];
  while n ne 0 do
    Append(~hs, m div n); Append(~ns, n);
    r := m mod n; m := n; n := r;
  end while; return <hs, ns>;
end function;

intrinsic CharExponents(s::RngSerPuisElt) -> []
{ Returns the characteristic exponents of a Puiseux series }
  C, m, n := ElementToSequence(s);
  // Exponents appearing in the series s
  E := [ m + i - 1 : i in [1 .. #C] | C[i] ne 0 ];
  charExps := [<0, n>]; ni := n;
  while ni ne 1 do
    // m_i = min{ j | a_j != 0 and j \not\in (n_{i-1}) }
    mi := [ e : e in E | e mod ni ne 0 ][1];
    // n_i = gcd(n, m_1, ..., m_k)
    ni := Gcd(ni, mi);
    Append(~charExps, <mi, ni>);
  end while; return charExps;
end intrinsic;

intrinsic CharExponents(f::RngMPolLocElt) -> []
{ Returns the characteristic exponents of an irreducible bivariate polynomials }
require Rank(Parent(f)) eq 2: "Argument must be a bivariate polynomial";
  S := PuiseuxExpansionReduced(f);
  if #S ne 1 then error "Argument must be an irreducible series"; end if;
  return CharExponents(S[1]);
end intrinsic;

intrinsic CharExponents(G::[ RngIntElt ]) -> [ ]
{ Computes the characteristic exponents from the generators of the semigroup }
require Gcd(G) eq 1: "Argument must be a numerical semigroup";
  M := [G[1]]; N := [G[1]];
  for i in [2..#G] do
    M cat:= [ &+[j ne i select -(N[j - 1] - N[j]) div N[i - 1] * M[j]
      else G[j] : j in [2..i]] ]; N cat:= [Gcd(M)];
  end for;
  return [<0, N[1]>] cat [<M[i], N[i]> : i in [2..#M]];
end intrinsic;

TailExponentSeries := function(s)
  C, m, n := ElementToSequence(s);
  // Exponents appearing in the series s
  E := [ m + i - 1 : i in [1 .. #C] | C[i] ne 0 ];
  charExps := CharExponents(s); g := #charExps;
  if s eq 0 then return <0, 1>; end if;
  return [<e, 1> : e in Reverse(E) | e ge charExps[g][1]][1];
end function;

TailExponentMatrix := function(P, v)
  E := CharExponents(SemiGroup(P, v)); n := Ncols(P);
  // If last point is satellite there is no tail exponent
  if &+Eltseq(P[n]) eq -1 then error "no free point"; end if;
  Pt := Transpose(P); isSat := &+[Pt[j]: j in [1..n]];
  p := ([i : i in Reverse([1..n]) | isSat[i] eq -1] cat [0])[1] + 1;
  return <E[#E][1] + (n - p), 1>;
end function;

intrinsic SemiGroup(s::RngSerPuisElt) -> []
{ Computes a minimal set of generators for the semigroup of the
  Puiseux series of an irreducible plane curve }
  M := CharExponents(s); // (G)amma starts with <n, m, ...>
  G := [i gt 2 select ( (Self(i-1) - M[i-1][1]) * M[i-2][2] div M[i-1][2] ) +
    M[i][1] + ( (M[i-2][2] - M[i-1][2]) div M[i-1][2] ) * M[i-1][1]
        else [M[1][2], M[2][1]][i] : i in [1 .. #M]];
  return G;
end intrinsic;

intrinsic SemiGroup(f::RngMPolLocElt) -> []
{ Computes a minimal set of generators for the semigroup of
  and irreducible plane curve }
require Rank(Parent(f)) eq 2: "Argument must be a bivariate polynomial";
  S := PuiseuxExpansionReduced(f);
  if #S ne 1 then error "Argument must be an irreducible series"; end if;
  return SemiGroup(S[1]);
end intrinsic;

intrinsic SemiGroup(P::Mtrx, v::Mtrx) -> []
{ Returns the minimal set of generators for the semigroup of and irreducible
  plane curve from its weighted cluster of singular points }
require Ncols(P) eq Nrows(P) and Ncols(v) eq Ncols(P) and Nrows(v) eq 1:
  "Arguments do not have the required dimensions";
require v[1][1] le v[1][Ncols(v)]: "Argument v is not a vector of values";
require #[i: i in [1..Ncols(P)] | (v * P)[1][i] gt 0] eq 1:
  "Weighted cluster not irreducible";
require Gcd(Eltseq(v)) eq 1: "Weighted cluster not irreducible";

  n := Ncols(P); Pt := Transpose(P); isSat := &+[Pt[i] : i in [1..n]];
  G := [v[1][1]]; G cat:= [v[1][i] : i in [1..n - 1] |
    isSat[i] ne -1 and isSat[i + 1] eq -1];
  return G;
end intrinsic;

forward SemiGroupMemberImpl;

SemiGroupMemberImpl := procedure(v, i, ~G, ~B, ~b, ~V)
  if v lt 0 or i gt #G then b := 0; return; end if;
  if B[v + 1, i] ne -1 then b := B[v + 1, i]; return; end if;
  V[i] := V[i] + 1;
  SemiGroupMemberImpl(v - G[i], i, ~G, ~B, ~b, ~V);
  B[v + 1, i] := b; if b eq 1 then return; end if;
  V[i] := V[i] - 1;
  SemiGroupMemberImpl(v, i + 1, ~G, ~B, ~b, ~V);
  B[v + 1, i] := b; if b eq 1 then return; end if;
end procedure;

intrinsic SemiGroupMembership(v::RngIntElt, G::[ RngIntElt ]) -> BoolElt
{ Returns whether or not an integer v belongs to a numerical semigroup G and
  the coordinates v in the semigroup }
require Gcd(G) eq 1: "Argument must be a numerical semigroup";
  Sort(~G); V := [0 : i in [1..#G]];
  B := Matrix(v + 1, #G, [IntegerRing() | -1 : i in [1..(v + 1) * #G]]);
  for i in [1..#G] do B[0 + 1][i] := 1; end for;
  b := 0; SemiGroupMemberImpl(v, 1, ~G, ~B, ~b, ~V);
  return b eq 1, V;
end intrinsic;

InversionFormula := function(M0, P, c)
  // Compute the exp. of the last free pt. depending of the first char. exp.
  N := Ncols(P); Pt := Transpose(P); isSat := &+[Pt[j]: j in [1..N]];
  p := ([i : i in [1..N] | isSat[i] eq -1] cat [N + 1])[1] - 1;
  m := ([i : i in [2..p] | c[i][1] eq 0] cat [0])[1] - 1;
  // Depending on whether 'm' is 0 or not, we have case (a) or case (b).
  M1 := [<0, m eq -1 select M0[2][1] else Lcm(M0[1][2], m)>]; k := #M0 - 1;
  M1 cat:= [<M0[1][2], Gcd(M1[1][2], M0[1][2])>]; i0 := m eq -1 select 2 else 1;
  ni := M1[2][2]; // ni := gcd(n, m_1, ..., m_i)
  for i in [i0..k] do // \bar{mi} = mi + n - \bar{n}
    mi := M0[i + 1][1] + M0[1][2] - M1[1][2];
    ni := Gcd(ni, mi); M1 cat:= [<mi, ni>];
  end for; return M1;
end function;
