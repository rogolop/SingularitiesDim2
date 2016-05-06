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

intrinsic BasePoints(I::RngMPolLoc : Coefficients := false) -> []
{ Computes the weighted cluster of base points of a bivariate
  polynomial ideal I }
require Type(Representative(I)) eq RngMPolLocElt:
  "Argument must be a polynomial ideal";
require Rank(Parent(Representative(I))) eq 2:
  "Argument must be a bivariate polynomial ideal";
  // Generators in G & fixed part F.
  G := Basis(I); F := Gcd(G); G := [ExactQuotient(g, F) : g in G];
  // Compute the Puiseux expansion & the prox. matrix for the product.
  S := NewtonPuiseuxAlgorithm(G: Polynomial := true);
  P := ProximityMatrixImpl([* <s[1], 1> : s in S *]: ExtraPoint := true,
    Coefficients := true);
  CC := P[3]; EE := P[2]; n := Ncols(P[1]); P := P[1]; ZZ := IntegerRing();
  // Merge the coefficients of each branch.
  C := [* 0: i in [1..n] *];
  for i in [1..#EE] do
    I := [j : j in [1..n] | EE[i][1][j] ne 0];
    for j in [1..#I] do C[I[j]] := CC[i][j]; end for;
  end for;
  // Compute the multiplicities of each generator in G.
  E := [ZeroMatrix(ZZ, 1, n) : i in [1..#G]]; B := [[* *] : i in [1..#G]];
  for i in [1..#S] do for m in S[i][2] do
    E[m[2]] := E[m[2]] + m[1]*EE[i];
    B[m[2]] cat:= [* <m[1]*EE[i], S[i][1], S[i][3], CC[i]> *];
  end for; end for;
  print P;
  print E;
  // Values for each generator in G.
  V := [e*Transpose(P^-1) : e in E]; v := ZeroMatrix(ZZ, 1, n);
  // Values for the points in the cluster of base points.
  for i in [1..n] do v[1][i] := Min([vj[1][i] : vj in V]); end for;
  // Multiplicities for the cluster of base points.
  e := v*Transpose(P); I := [i : i in [1..n] | e[1][i] ne 0]; C:= C[I];
  // Remove points not in the cluster of base points.
  P := Submatrix(P, I, I);  v := Submatrix(v, [1], I); n := Ncols(P);
  V := [Submatrix(v, [1], I) : v in V]; E := [Submatrix(e, [1], I) : e in E];
  B := [[* <Submatrix(bi[1], [1], I), bi[2], bi[3], bi[4]>: bi in b *]: b in B];
  // ------------ Add NEW free points ------------------
  e := v*Transpose(P); inCluster := [i : i in [1..n] | e[1][i] ne 0];
  S := &+Submatrix(P, inCluster, inCluster)[1..#inCluster];
  lastFree := [i : i in [1..#inCluster] | S[i] eq 1];
  // For each last free point on a branch...
  for p in lastFree do
    // Values for each gen. at p && index of the gen. achieving the minimum.
    Vp := [vi[1][p] : vi in V]; g := Index(Vp, Min(Vp));
    print Vp;
    print g;
    // If there is a unique gen. achieving the min. and
    // the excess is positive add new points.
    uniqueGen := #[vp : vp in Vp | vp eq v[1][p]] eq 1;
    print [vp : vp in Vp | vp eq v[1][p]];
    print uniqueGen;
    if uniqueGen and E[g][1][p] ne 0 then
      // Minimm of the values for all the generator except g.
      wp := Min(Exclude(Vp, v[1][p]));
      // Number of new free points.
      k := Ceiling((wp - v[1][p])/E[g][1][p]);
      // Expand the proximity matrix.
      P := InsertBlock(ScalarMatrix(n + k, 1), P, 1, 1);
      P[n + 1][p] := -1; n := n + k;
      for i in [1..k - 1] do P[n - i + 1][n - i] := -1; end for;
      // Expand the vector of mult. of each generator & recompute.
      E := [InsertBlock(ZeroMatrix(ZZ, 1, n), e, 1, 1): e in E];
      for i in [1..k] do E[g][1][n - i + 1] := E[g][1][p]; end for;
      V := [e*Transpose(P^-1) : e in E]; v := ZeroMatrix(ZZ, 1, n);
      for i in [1..n] do v[1][i] := Min([vj[1][i] : vj in V]); end for;
      // Expand the vector of coefficients.
      if Coefficients then // 1) Find the right branch in the current gen.
        b := [i: i in [1..#B[g]] | B[g][i][1][1, p] ne 0][1]; Bg := B[g][b];
        // Number of points of branch b appearing in BP(I)
        m := #[e : e in Eltseq(Bg[1]) | e ne 0];
        // If we do not have enough terms of Puiseux already computed...
        if #Bg[4] lt m + k then
          Bg[2] := NewtonPuiseuxAlgorithmExpandReduced(Bg[2], Bg[3]:
            Terms := m + k - #Bg[4])[1];
          Bg[4] := CoefficientsVectorBranch(Bg[2], m + k);
        end if; for i in [1..k] do C cat:= [* Bg[4][m + i] *]; end for;
      end if;
    end if;
  end for; // ------------ Add NEW satellite points ------------------
  e := v*Transpose(P); inCluster := [i : i in [1..n] | e[1][i] ne 0];
  points2test := #inCluster - 1; i := 2;
  while points2test gt 0 do
    // Values for the generators at point p.
    p := inCluster[i]; Vp := [vi[1][p] - v[1][p] : vi in V];
    // Points p is proximate to && Points proximate to p.
    p_prox := [i : i in [1..#inCluster] | P[p][inCluster[i]] eq -1];
    prox_p := [i : i in [1..#inCluster] | P[inCluster[i]][p] eq -1];
    Q := [ q : q in p_prox | &+Eltseq(Submatrix(P, prox_p, [q])) eq 0];
    for q in Q do
      // Values for the generators at point q.
      Vq := [vi[1][q] - v[1][q] : vi in V];
      if &*[Vp[i] + Vq[i] : i in [1..#Vp]] ne 0 then
        // Expand the proximity matrix.
        P := InsertBlock(ScalarMatrix(n + 1, 1), P, 1, 1); n := n + 1;
        P[n][p] := -1; P[n][q] := -1;
        // Expand the vector of mult. of each generator.
        E := [InsertBlock(ZeroMatrix(ZZ, 1, n), e, 1, 1): e in E];
        V := [e*Transpose(P^-1) : e in E]; v := ZeroMatrix(ZZ, 1, n);
        for i in [1..n] do v[1][i] := Min([vj[1][i] : vj in V]); end for;
        e := v*Transpose(P); inCluster := [i : i in [1..n] | e[1][i] ne 0];
        // Expand the vector of coefficients.
        if Coefficients then C cat:= [* Infinity() *]; end if;
        points2test := points2test + 1;
      end if;
    end for; points2test := points2test - 1; i := i + 1;
  end while;
  if Coefficients then return <P, v, F, C>;
  else return <P, v, F>; end if;
end intrinsic;
