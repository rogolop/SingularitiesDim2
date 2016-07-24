// SquarefreePart not available for local polynomial rings.
intrinsic SquarefreePart(f::RngMPolLocElt) -> RngMPolLocElt
{ Return the squarefree part of f, which is the largest (normalized)
  divisor g of f which is squarefree. }
  P := Parent(f); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return P!SquarefreePart(Q!f);
end intrinsic;

// SquarefreeFactorization not available for local polynomial rings.
intrinsic SquarefreeFactorization(f::RngMPolLocElt) -> SeqEnum
{ Factorize into squarefree polynomials the polynomial f. }
  P := Parent(f); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return [<P!g[1], g[2]> : g in SquarefreeFactorization(Q!f)];
end intrinsic;

// ExactQuotient not available for local polynomial rings.
intrinsic ExactQuotient(f::RngMPolLocElt, g::RngMPolLocElt) -> RngMPolLocElt
{ Return the quotient x div y, assuming y divides x exactly. }
  P := Parent(f); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return P!ExactQuotient(Q!f, Q!g);
end intrinsic;

// NewtonPolygon not available for local polynomial rings.
intrinsic NewtonPolygon(f::RngMPolLocElt) -> NwtnPgon
{ The standard Newton polygon of a polynomial f in two variables. This is the
  hull of the Newton points of the polynomial together with the points +∞ on
  each axis. The horizontal and vertical `end' faces are not listed among the
  faces of the polygon; the points at infinity are not listed among the vertices
  of the polygon.

  The parameter Faces can have the value "Inner", "Lower" or "All". This
  determines which faces are returned by the intrinsic Faces. }
  P := Parent(f); Q := PolynomialRing(CoefficientRing(P), Rank(P));
  return NewtonPolygon(Q!f);
end intrinsic;
