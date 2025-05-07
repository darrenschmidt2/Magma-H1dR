# Magma-H1dR
The file h1dRComputation.m computes the matrices of the Frobenius and Cartier Operators on H1 de Rham Cohomology of a Z_p tower of curves over P1 totally ramified at infinity.

First let p be a prime and construct a polynomial ring A<t> := PolynomialRing(GF(p))

Then call computeH1dR(p,r,n,f) for F_{p^r} where p is prime,  n is the level of the tower, and f(t) is a polynomial such that y1^p-y1 = f

This returns an H1dR module M. To get the Frobenius operator, call Action(M).1 and to get the Cartier operator, call Action(M).2.

The file eoType.m computes the Ekedahl-Oort type of M. Call EOType(M) and it returns the Ekedahl-Oort Type.
