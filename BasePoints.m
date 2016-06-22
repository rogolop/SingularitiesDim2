import "ProximityMatrix.m": ProximityMatrixImpl, CoefficientsVectorBranch;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

intrinsic ExactQuotient(f::RngMPolLocElt, g::RngMPolLocElt) -> RngMPolLocElt
{ Return the quotient x div y, assuming y divides x exactly. }
  P := Parent(f); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return P!ExactQuotient(Q!f, Q!g);
end intrinsic;

///////////////////////////////////////////////////////////////////////////////
///////////////////////////////////////////////////////////////////////////////

ExpandWeightedCluster := procedure(~P, ~EE, ~CC, ~S, b)
  // Expand the proximity matrix.
  P := InsertBlock(ScalarMatrix(Ncols(P) + 1, 1), P, 1, 1);
  // Expand branches multiplicities.
  EE := [InsertBlock(ZeroMatrix(IntegerRing(), 1, Ncols(P)), EEi, 1, 1) : EEi in EE];
  if b ne -1 then EE[b][Ncols(P)] := 1; end if;
  // If a free points, expand the Puiseux series.
  if b ne -1 then
    // Number of points of branch b appearing in BP(I)
    m := #[e : e in Eltseq(EE[b]) | e ne 0];
    // If we do not have enough terms of Puiseux already computed...
    if #CC[b] lt m + 1 then
      TEMP := NewtonPuiseuxAlgorithmExpandReduced(S[b][1], S[b][3]:
        Terms := m + 1 - #CC[b])[1];
      S[b][1] := TEMP[1][1]; S[b][3] := TEMP[1][3];
      CC[b] := CoefficientsVectorBranch(CC[b], m + 1);
    end if; // Append the new coefficient to the cluster's coeffs.
  // Otherwise, just add Infinity coefficients.
  end if;
end procedure;

ComputeBasePointsData := procedure(~P, ~EE, ~CC, ~S, N, ~E, ~C, ~V, ~v)
  // Compute the multiplicities of each generator in G.
  E := [ZeroMatrix(IntegerRing(), 1, Ncols(P)) : i in [1..N]];
  // Hold information about the branches in each generator.
  for i in [1..#S] do
    for m in S[i][2] do
      E[m[2]] := E[m[2]] + m[1]*EE[i];
    end for;
  end for;
  // Merge the coefficients of each branch.
  C := [* Infinity() : i in [1..Ncols(P)] *];
  for i in [1..#EE] do
    I := [j : j in [1..Ncols(P)] | EE[i][1][j] ne 0];
    for j in [1..#I] do C[I[j]] := CC[i][j]; end for;
  end for;
  // Values for each generator in G & each (initial) base point.
  V := [e*Transpose(P^-1) : e in E];
  v := ZeroMatrix(IntegerRing(), 1, Ncols(P));
  for i in [1..Ncols(P)] do v[1][i] := Min([vj[1][i] : vj in V]); end for;
end procedure;

intrinsic BasePoints(I::RngMPolLoc : Coefficients := false) -> []
{ Computes the weighted cluster of base points of a bivariate
  polynomial ideal I }
require Type(Representative(I)) eq RngMPolLocElt:
  "Argument must be a polynomial ideal";
require Rank(Parent(Representative(I))) eq 2:
  "Argument must be a bivariate polynomial ideal";
  // Generators in G & fixed part F.
  G := Basis(I); F := Gcd(G); G := [ExactQuotient(g, F) : g in G];

  // ------------ Compute all information --------------
  S := NewtonPuiseuxAlgorithm(G: Polynomial := true); // Puiseux series for each branch.
  TEMP := ProximityMatrixImpl([* <s[1], 1> : s in S *]: ExtraPoint := true, Coefficients := true);
  P := TEMP[1]; // Proximity matrix of the cluster.
  EE := TEMP[2]; // Multiplicities of each branch in the cluster.
  CC := TEMP[3]; // Coefficients of each branch in the cluster.

  E := []; // Multiplicities of each generator.
  C := [* *]; // Coefficients of BP(I).
  V := []; // Vector a values for each generator.
  v := []; // Virtual values of BP(I).
  ComputeBasePointsData(~P, ~EE, ~CC, ~S, #G, ~E, ~C, ~V, ~v);

  //print [* P, EE, E, V, v, CC, C*];

  // ------------ Add new free points ------------------
  lastFree := [i : i in [1..Ncols(P)] | (&+P[1..Ncols(P)])[i] eq 1];
  points2test := #lastFree - 1; idx := 1;
  // For each last free point on a branch...
  while points2test gt 0 do
    // Values for each gen. at p.
    p := lastFree[idx]; Vp := [vi[1][p] : vi in V];
    // Generators achieving the minimum.
    GG := [i : i in [1..#Vp] | Vp[i] eq Min(Vp)];
    // If the multiplicities of all the generators achieving the minimum
    // at p is > 0 add new point.
    if &and[E[g][1][p] ne 0 : g in GG] then
      // The (unique) branch of the generator 'g' where 'p' belongs.
      assert(#[i : i in [1..#EE] | EE[i][1, p] ne 0] eq 1);
      b := [i : i in [1..#EE] | EE[i][1, p] ne 0][1];
      ExpandWeightedCluster(~P, ~EE, ~CC, ~S, b); P[Ncols(P)][p] := -1;
      ComputeBasePointsData(~P, ~EE, ~CC, ~S, #G, ~E, ~B, ~C, ~V, ~v); // Recompute.
      // We may need to add more free points after the points we added.
      lastFree cat:= [Ncols(P)]; points2test := points2test + 1;
    end if;
  points2test := points2test - 1; idx := idx + 1;
  end while;

  // ------------ Add new satellite points ------------------
  points2test := Ncols(P) - 1; p := 2; // Do not start by the origin.
  while points2test gt 0 do
    // Values for the generators at point p.
    Vp := [vi[1][p] - v[1][p] : vi in V];
    // Points p is proximate to && Points proximate to p.
    p_prox := [i : i in [1..Ncols(P)] | P[p][i] eq -1];
    prox_p := [i : i in [1..Ncols(P)] | P[i][p] eq -1];
    Q := [q : q in p_prox | &+Eltseq(Submatrix(P, prox_p, [q])) eq 0];
    for q in Q do
      // Values for the generators at point q.
      Vq := [vi[1][q] - v[1][q] : vi in V];
      if &*[Vp[i] + Vq[i] : i in [1..#Vp]] ne 0 then
        ExpandWeightedCluster(~P, ~EE, ~CC, ~S, -1);
        P[Ncols(P)][p] := -1; P[Ncols(P)][q] := -1;
        ComputeBasePointsData(~P, ~EE, ~CC, ~S, #G, ~E, ~C, ~V, ~v); // Recompute.
        // We may need to add more satellite points after the points we added.
        points2test := points2test + 1;
      end if;
    end for;
  points2test := points2test - 1; p := p + 1;
  end while;

  // ------------ Remove non base points ---------------
  // Multiplicities for the cluster of base points.
  e := v*Transpose(P); I := [i : i in [1..Ncols(P)] | e[1][i] ne 0];
  // Remove points not in the cluster of base points.
  P := Submatrix(P, I, I); v := Submatrix(v, [1], I); C := C[I];

  if Coefficients then return <P, v, F, C>;
  else return <P, v, F>; end if;
end intrinsic;
