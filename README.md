# Magma-H1dR
The file h1dRComputation.m computes the matrices of the Frobenius and Cartier Operators on H1 de Rham Cohomology of a Z_p tower of curves over P1 totally ramified at infinity.

First let p be a prime and construct a polynomial ring A<t> := PolynomialRing(GF(p^r))

Then call computeH1dR(p,r,n,f) for F_{p^r} where p is prime,  n is the level of the tower, and f(t) is a polynomial such that y1^p-y1 = f

This returns an H1dR module M. To get the Frobenius operator, call Action(M).1 and to get the Cartier operator, call Action(M).2.

The file eoType.m computes the Ekedahl-Oort type of M. Call EOType(M) and it returns the Ekedahl-Oort Type.

# Computed Data

The folder computedData contains the EO-types of already computed towers. Inside that folder, the next layer is given by number, representing the field characteristic.

In each file inside, the prime power, the level of the tower, and the polynomial for the base curve are listed. Below that is a list giving the Ekedahl-Oort type of that level in the tower.

Below the EO-type is a 3x3 matrix where the i,j-th entry represents the dimension of Ker $(V^j)$ intersecting Ker $\left(\frac{F^i}{F^{(i-1)}}\right)$ 
