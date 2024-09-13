// Routines to compute the Greenberg transform


// need the auxiliary eta and witt functions
load 'witt.m'; // this one calls eta.m


function bin_tab(n,m)
    // binomial table up to choose n and modulo m
    // using Pascal's triangle
    F:=ResidueClassRing(m);
    res:=[[F!1],[F!1,F!1]];  // res[i][j]=bin(i-1,j-1)
    for i in [2..n] do
        v:=[F!1];
        for j in [1..(i-1)] do
            Append(~v,res[i][j] + res[i][j+1]);
        end for;
        Append(~v,F!1);
        Append(~res,v);
    end for;
    return res;
end function;


//load 'witt_gen.m';



function Not_Zero_Vec(v)
    // checks if a vector is the zero vector
    for i in [1..#v] do
        if v[i] ne 0 then
            return true;
        end if;
    end for;

    return false;

end function;





function Pol_GT_Form(f,p,n)
    // f a polynomial in two variables over Z
    // converts to format to use with GT below
    res:=[];
    for mon in Monomials(f) do
        coef:=IntToWitt(MonomialCoefficient(f,mon),p,n);
        Append(~res,[* coef, Degree(mon,1), Degree(mon,2) *]);
    end for;
    
    return res;

end function;



// /////////////////////////////////////////////////
// GT -- using vetav


function GT_der(f,p,i,r,n,tab,pols)
    // to use to compute the GT
    // compute f^{(i,r-i)} (assuming 0<=i<=r)
    // needs to supply: table with binomials (tab)
    //                  vector to perform sums of Witt vectors (vecP)

    if r eq 0 then
        derf:=f;  // no derivative
    else
        derf:=[]; // derivative
        for t in f do
            // loop over the terms of f

            coef:=t[1];
            degx:=t[2];
            degy:=t[3];

            // print "coef = ", coef;

            if (degx-i ge 0) and (degy-(r-i) ge 0) and Not_Zero_Vec(coef) then
                // make sure derivative of the term is not zero

                // print "degx, degy = ", degx, degy;

                bin1:=tab[degx+1][i+1];
                bin2:=tab[degy+1][r-i+1];

                b12:=Integers()!(bin1*bin2);

                if (b12 mod p^(n-r+1)) eq 1 then
                    // no need to multiply
                    Append(~derf, [* [ coef[i] : i in [1..(n+1-r)] ] , degx-i, degy-(r-i) *]);
                elif (b12 mod p^(n-r+1)) ne 0 then
                    // if the term is not zero...
                    v1:=IntToWitt(b12,p,n-r);

                    // print "v1 = ", v1;
                    // print "[ coef[",i,"]: i in [1..(n+1-r)] ] = ", [ coef[i] : i in [1..(n+1-r)] ];
                    // print "prod = ", newWittProd(v1,[ coef[i] : i in [1..(n+1-r)] ] : pols:=pols);

                    Append(~derf,[* WittProd1(v1,[ coef[i] : i in [1..(n+1-r)] ] : pols:=pols) , degx-i, degy-(r-i) *]);
                end if;
            end if;
        end for;

        // derivative is zero?
        if #derf eq 0 then
            derf:=[ [* [0 : s in [0..n-r]], 0, 0 *] ];
        end if;
    end if;

    return derf;

end function;




function split_Ds(f,p,max,PR)
    // given a polynomial f (likely over Z/p^n) returns
    // [ \xi_0(f) , \xi_1(f), ... , \xi_max(f) ]
    
    res:=[ PR!0 : i in [0..max] ];
    for mon in Monomials(f) do
        coef:=Integers()!(MonomialCoefficient(f,mon));
        vcoef:=IntToWitt(coef,p,max);
        for i in [1..(max+1)] do
            //res[i]+:=PR!(vcoef[i])*PR!mon; // ambigous coercion
            res[i]+:=PR!(vcoef[i])*Monomial(PR, Exponents(mon));
        end for;
    end for;

    return res;

end function;



function GT_Ds(i,r,n,p,PR)
    // assumes r>=1!!!

    PR1:=PolynomialRing(ResidueClassRing(p^(n+1)),2*n+2);

    PR2<t>:=PolynomialRing(PR1);

    tmp:=Min(n,n-r+1);
    
    t1:=&+[ PR2.1^s*PR1.(s+1)^(p^(n-s)) : s in [1..tmp] ];
    t2:=&+[ PR2.1^s*PR1.(n+s+2)^(p^(n-s)) : s in [1..tmp] ];

    t:=t1^i*t2^(r-i);
    delete t1, t2;

    
    t:=[ Coefficient(t,s) : s in [r..n] ];
    // t = [ D_{r,n}^{(i,r-i)}, ... , D_{n,n}^{(i,r-i)} ]

    // now, split each D_{s,n}^{(i,r-i)} into
    // [ D_{s,n,0}^{(i,r-i)}, ..., D_{r,n,n-s}^{(i,r-i)} ]
    return [ split_Ds(f,p,n-r,PR) : f in t ];

end function;



function Pol_Root(f,r)
    // takes "r-th root" of a polyn.
    // in fact, leaves coefficient the same and divide
    // the powers of variables by n

    P:=Parent(f);
    n:=Rank(P);
    res:=0;
    for mon in Monomials(f) do
        nmon:=MonomialCoefficient(f,mon);
        for i in [1..n] do
            nmon*:=(P.i)^(Degree(mon,i) div r);
        end for;
        res+:=nmon;
    end for;
    
    return res;

end function;





function GT1(f : pols:=[], tab:=[], vvars:=[])
    // f must be given by f:=[ ... , [[a0,a1,...,an],i,j] , ... ]
    n:=#(f[1][1])-1; // length of the coefficients - 1
    //P:=Parent(f[1][1][1]);
    P:=Universe(f[1][1]);
    p:=Characteristic(P);

    if #pols eq 0 then
        pols:=etapols(p,n);
    end if;

    PR:=PolynomialRing(P,2*n+2);
    AssignNames(~PR,
                [ "x" cat IntegerToString(i) : i in [0..n] ] cat 
                [ "y" cat IntegerToString(i) : i in [0..n] ] );

    maxdegx:=Max([t[2] : t in f]);
    maxdegy:=Max([t[3] : t in f]);

    maxdeg:=Max(maxdegx,maxdegy); // to find the binomial table size

    if #tab eq 0 then
        tab:=bin_tab(maxdeg,p^(n+1)); // table of binomials to use
    end if;

    res:=[ [] : s in [0..n] ];

    for r in [0..n] do
        for i in [0..r] do
            if (i le maxdegx) and (r-i le maxdegy) then
                // first, compute the derivative
                derf:=GT_der(f,p,i,r,n,tab,pols);

                // print "derf = ", derf;
                
                // now we need the Ds
                Ds:=GT_Ds(i,r,n,p,PR);
                // Ds=[ [D_{r,n,0}^{(i,r-i)} , ... , D_{r,n,n-r}^{(i,r-i)}],
                //      [D_{r+1,n,0}^{(i,r-i)} , ... , D_{r,n,n-r-1}^{(i,r-i)}],
                //      ...,
                //      [D_{n,n,0}^{(i,r-i)}] ]


                // print "Ds = ", Ds;

                for m in [r..n] do
                    for j in [r..m] do
                        for k in [r..j] do

                            // print "r, i, m, j, k = ", r, i, m, j, k;

                            // split the derivative (i.e., the \xi_i's)
                            // also takes care of the Frob and evalutation
                            vt:=&+[ (t[1][m-j+1])^(p^j)*(PR.1)^(t[2]*p^m)*(PR.(n+2))^(t[3]*p^m) : t in derf ];

                            // create a vector to evaluate D_{r,n}
                            // to get D_{r,m}
                            v:=< PR!0 : s in [1..(2*n+2)] >;
                            for s in [2..(m+1)] do
                                v[s]:=PR.s;
                                v[s+n+1]:=PR.(s+n+1);
                            end for;
                            
                            // get D_{r,m} from D_{r,n}
                            tmp:=Evaluate(Ds[k-r+1][j-k+1],v);
                            tmp:=Pol_Root(tmp,p^(n-m));

                            if #vvars ne 0 then 
                                res[m+1]:=res[m+1] cat [ Evaluate(term,vvars) : term in Terms(vt*tmp)];
                            else
                                res[m+1]:=res[m+1] cat Terms(vt*tmp);
                            end if;
                            
                        end for; // k
                        delete tmp, v, vt;
                    end for; // j
                end for; // m
            end if;
        end for; // i
    end for; // r

    // now add the etas...

    // print "pols = ", pols;

    for i in [1..n] do

        // print "res[", i, "] = ", res[i];

        ve:=vetav(p,n-i+1,res[i] : pols:=pols);
        
        // print "ve = ", ve;

        for j in [(i+1)..(n+1)] do
            if ve[j-i] ne 0 then
                Append(~res[j],ve[j-i]);
            end if;
        end for;

        // don't need all pols anymore
        pols:=pols[1..(n-i)];

    end for;

    return [ &+t : t in res ];

end function; 





// ////////////////////////////////////////////////////
// using vetav2


function GT_der2(f,p,i,r,n,tab,bintab)
    // to use to compute the GT
    // compute f^{(i,r-i)} (assuming 0<=i<=r)
    // needs to supply: table with binomials (tab)
    //                  vector to perform sums of Witt vectors (vecP)

    if r eq 0 then
        derf:=f;  // no derivative
    else
        derf:=[]; // derivative
        for t in f do
            // loop over the terms of f

            coef:=t[1];
            degx:=t[2];
            degy:=t[3];

            // print "coef = ", coef;

            if (degx-i ge 0) and (degy-(r-i) ge 0) and Not_Zero_Vec(coef) then
                // make sure derivative of the term is not zero

                // print "degx, degy = ", degx, degy;

                bin1:=tab[degx+1][i+1];
                bin2:=tab[degy+1][r-i+1];

                b12:=Integers()!(bin1*bin2);

                if (b12 mod p^(n-r+1)) eq 1 then
                    // no need to multiply
                    Append(~derf, [* [ coef[i] : i in [1..(n+1-r)] ] , degx-i, degy-(r-i) *]);
                elif (b12 mod p^(n-r+1)) ne 0 then
                    // if the term is not zero...
                    v1:=IntToWitt(b12,p,n-r);

                    // print "v1 = ", v1;
                    // print "[ coef[",i,"]: i in [1..(n+1-r)] ] = ", [ coef[i] : i in [1..(n+1-r)] ];
                    // print "prod = ", newWittProd(v1,[ coef[i] : i in [1..(n+1-r)] ] : pols:=pols);

                    Append(~derf,[* WittProd2(v1,[ coef[i] : i in [1..(n+1-r)] ] : bintab:=bintab) , degx-i, degy-(r-i) *]);
                end if;
            end if;
        end for;

        // derivative is zero?
        if #derf eq 0 then
            derf:=[ [* [0 : s in [0..n-r]], 0, 0 *] ];
        end if;
    end if;

    return derf;

end function;




function split_Ds2(f,p,max,PR)
    // given a polynomial f (likely over Z/p^n) returns
    // [ \xi_0(f) , \xi_1(f), ... , \xi_max(f) ]
    
    res:=[ PR!0 : i in [0..max] ];
    for mon in Monomials(f) do
        coef:=Integers()!(MonomialCoefficient(f,mon));
        vcoef:=IntToWitt(coef,p,max);
        for i in [1..(max+1)] do
            res[i]+:=PR!(vcoef[i])*PR!mon;
        end for;
    end for;

    return res;

end function;



function GT_Ds2(i,r,n,p,PR)
    // assumes r>=1!!!

    PR1:=PolynomialRing(ResidueClassRing(p^(n+1)),2*n+2);

    PR2<t>:=PolynomialRing(PR1);

    tmp:=Min(n,n-r+1);
    
    t1:=&+[ PR2.1^s*PR1.(s+1)^(p^(n-s)) : s in [1..tmp] ];
    t2:=&+[ PR2.1^s*PR1.(n+s+2)^(p^(n-s)) : s in [1..tmp] ];

    t:=t1^i*t2^(r-i);
    delete t1, t2;

    
    t:=[ Coefficient(t,s) : s in [r..n] ];
    // t = [ D_{r,n}^{(i,r-i)}, ... , D_{n,n}^{(i,r-i)} ]

    // now, split each D_{s,n}^{(i,r-i)} into
    // [ D_{s,n,0}^{(i,r-i)}, ..., D_{r,n,n-s}^{(i,r-i)} ]
    return [ split_Ds2(f,p,n-r,PR) : f in t ];

end function;





function GT2(f : bintab:=[], tab:=[], vvars:=[])
    // f must be given by f:=[ ... , [[a0,a1,...,an],i,j] , ... ]
    n:=#(f[1][1])-1; // length of the coefficients - 1
    //P:=Parent(f[1][1][1]);
    P:=Universe(f[1][1]);
    p:=Characteristic(P);

    if #bintab eq 0 then
        bintab:=BinTab(p,n);
    end if;

    PR:=PolynomialRing(P,2*n+2);
    AssignNames(~PR,
                [ "x" cat IntegerToString(i) : i in [0..n] ] cat 
                [ "y" cat IntegerToString(i) : i in [0..n] ] );

    maxdegx:=Max([t[2] : t in f]);
    maxdegy:=Max([t[3] : t in f]);

    maxdeg:=Max(maxdegx,maxdegy); // to find the binomial table size

    if #tab eq 0 then
        tab:=bin_tab(maxdeg,p^(n+1)); // table of binomials to use
    end if;

    res:=[ [] : s in [0..n] ];

    for r in [0..n] do
        for i in [0..r] do
            if (i le maxdegx) and (r-i le maxdegy) then            
                // first, compute the derivative
                derf:=GT_der2(f,p,i,r,n,tab,bintab);

                // print "derf = ", derf;
                
                // now we need the Ds
                Ds:=GT_Ds2(i,r,n,p,PR);
                // Ds=[ [D_{r,n,0}^{(i,r-i)} , ... , D_{r,n,n-r}^{(i,r-i)}],
                //      [D_{r+1,n,0}^{(i,r-i)} , ... , D_{r,n,n-r-1}^{(i,r-i)}],
                //      ...,
                //      [D_{n,n,0}^{(i,r-i)}] ]


                // print "Ds = ", Ds;

                for m in [r..n] do
                    for j in [r..m] do
                        for k in [r..j] do

                            // print "r, i, m, j, k = ", r, i, m, j, k;

                            // split the derivative (i.e., the \xi_i's)
                            // also takes care of the Frob and evalutation
                            vt:=&+[ (t[1][m-j+1])^(p^j)*(PR.1)^(t[2]*p^m)*(PR.(n+2))^(t[3]*p^m) : t in derf ];

                            // create a vector to evaluate D_{r,n}
                            // to get D_{r,m}
                            v:=< PR!0 : s in [1..(2*n+2)] >;
                            for s in [2..(m+1)] do
                                v[s]:=PR.s;
                                v[s+n+1]:=PR.(s+n+1);
                            end for;
                            
                            // get D_{r,m} from D_{r,n}
                            tmp:=Evaluate(Ds[k-r+1][j-k+1],v);
                            tmp:=Pol_Root(tmp,p^(n-m));

                            if #vvars ne 0 then 
                                res[m+1]:=res[m+1] cat [ Evaluate(term,vvars) : term in Terms(vt*tmp)];
                            else
                                res[m+1]:=res[m+1] cat Terms(vt*tmp);
                            end if;
                            
                        end for; // k
                        delete tmp, v, vt;
                    end for; // j
                end for; // m
            end if;
        end for; // i

    end for; // r

    // now add the etas...

    // print "pols = ", pols;

    for i in [1..n] do

        // print "res[", i, "] = ", res[i];

        ve:=vetav2(p,n-i+1,res[i] : bintab:=bintab);
        
        // print "ve = ", ve;

        for j in [(i+1)..(n+1)] do
            if ve[j-i] ne 0 then
                Append(~res[j],ve[j-i]);
            end if;
        end for;

        // don't need all pols anymore
        bintab:=bintab[1..(n-i)];

    end for;

    return [ &+t : t in res ];

end function; 




// ///////////////////////////////////////////////////
// this version tries to store some of the computed
// terms in memory to try to speed the computations,
// but it seems to take the same time and uses a lot
// more memory



function GT_der3(f,p,i,r,n,tab,bintab)
    // to use to compute the GT
    // compute f^{(i,r-i)} (assuming 0<=i<=r)
    // needs to supply: table with binomials (tab)
    //                  vector to perform sums of Witt vectors (vecP)

    if r eq 0 then
        derf:=f;  // no derivative
    else
        derf:=[]; // derivative
        for t in f do
            // loop over the terms of f

            coef:=t[1];
            degx:=t[2];
            degy:=t[3];

            // print "coef = ", coef;

            if (degx-i ge 0) and (degy-(r-i) ge 0) and Not_Zero_Vec(coef) then
                // make sure derivative of the term is not zero

                // print "degx, degy = ", degx, degy;

                bin1:=tab[degx+1][i+1];
                bin2:=tab[degy+1][r-i+1];

                b12:=Integers()!(bin1*bin2);

                if (b12 mod p^(n-r+1)) eq 1 then
                    // no need to multiply
                    Append(~derf, [* [ coef[i] : i in [1..(n+1-r)] ] , degx-i, degy-(r-i) *]);
                elif (b12 mod p^(n-r+1)) ne 0 then
                    // if the term is not zero...
                    v1:=IntToWitt(b12,p,n-r);

                    // print "v1 = ", v1;
                    // print "[ coef[",i,"]: i in [1..(n+1-r)] ] = ", [ coef[i] : i in [1..(n+1-r)] ];
                    // print "prod = ", newWittProd(v1,[ coef[i] : i in [1..(n+1-r)] ] : pols:=pols);

                    Append(~derf,[* WittProd3(v1,[ coef[i] : i in [1..(n+1-r)] ] : bintab:=bintab) , degx-i, degy-(r-i) *]);
                end if;
            end if;
        end for;

        // derivative is zero?
        if #derf eq 0 then
            derf:=[ [* [0 : s in [0..n-r]], 0, 0 *] ];
        end if;
    end if;

    return derf;

end function;




function split_Ds3(f,p,max)
    // given a polynomial f (likely over Z/p^n) returns
    // [ \xi_0(f) , \xi_1(f), ... , \xi_max(f) ]
    
    PR:=Parent(f);
    m:=Rank(PR);
    PR3:=PolynomialRing(GF(p),m); // will return over GF(p)

    res:=[ PR3!0 : i in [0..max] ];

    for mon in Monomials(f) do
        coef:=Integers()!(MonomialCoefficient(f,mon));
        vcoef:=IntToWitt(coef,p,max);
        for i in [1..(max+1)] do
            res[i]+:=PR3!(vcoef[i])*PR3!mon;
        end for;
    end for;

    return res;

end function;



function GT_Ds3(n,r,p,PR)
    // assumes r>=1!!!

    vecDs:=AssociativeArray(); // will have all the D[n,r,i,k,t]

    PR1:=PolynomialRing(ResidueClassRing(p^(n+1-r)),2*n+2); // x's and y's

    PR2<t>:=PolynomialRing(PR1); // t


    tmp:=Min(n,n-r+1); // in case r=0
    t1:=&+[ PR2.1^s*PR1.(s+1)^(p^(n-s)) : s in [1..tmp] ];    

    vx:=[PR2!1,t1]; // contains tthe powers of t1

    // compute other powers
    for i in [2..r] do
        vx[i+1]:=t1*vx[i];
    end for;

    tmpeval:=[ PR1.(n+2+i) : i in [0..n] ] cat [ PR1!0 : i in [0..n] ];
    for i in [0..r] do
        tmp:=&+[ Evaluate(Coefficient(vx[r-i+1],dd),tmpeval)*t^dd : dd in [0..Degree(vx[r-i+1])] ];
        tmp1:=vx[i+1]*tmp;
        for k in [r..n] do
            // print "splid Ds";
            tmp2:=split_Ds3(Coefficient(tmp1,k),p,n-k);
            for t in [0..(n-k)] do
                vecDs[[n,r,i,k,t]]:=PR!tmp2[t+1];
            end for;
        end for;
    end for;

    return vecDs;

end function;






function GT3(f : bintab:=[], tab:=[], vvars:=[])
    // f must be given by f:=[ ... , [[a0,a1,...,an],i,j] , ... ]
    n:=#(f[1][1])-1; // length of the coefficients - 1
    //P:=Parent(f[1][1][1]);
    P:=Universe(f[1][1]);
    p:=Characteristic(P);

    if #bintab eq 0 then
        bintab:=BinTab(p,n);
    end if;

    PR:=PolynomialRing(P,2*n+2);
    AssignNames(~PR,
                [ "x" cat IntegerToString(i) : i in [0..n] ] cat 
                [ "y" cat IntegerToString(i) : i in [0..n] ] );

    maxdegx:=Max([t[2] : t in f]);
    maxdegy:=Max([t[3] : t in f]);

    maxdeg:=Max(maxdegx,maxdegy); // to find the binomial table size

    if #tab eq 0 then
        tab:=bin_tab(maxdeg,p^(n+1)); // table of binomials to use
    end if;

    res:=[ [] : s in [0..n] ];

    for r in [0..n] do
        
        // print "compute Ds: r, n = ", r, n;
        vecDs:=GT_Ds3(n,r,p,PR);

        for i in [0..r] do
            if (i le maxdegx) and (r-i le maxdegy) then
                
                // first, compute the derivative
                // print "compute der.";
                derf:=GT_der3(f,p,i,r,n,tab,bintab);

                // print "derf = ", derf;
                
                for m in [r..n] do
                    for j in [r..m] do
                        for k in [r..j] do

                            // print "r, i, m, j, k = ", r, i, m, j, k;

                            // split the derivative (i.e., the \xi_i's)
                            // also takes care of the Frob and evalutation
                            vt:=&+[ (t[1][m-j+1])^(p^j)*(PR.1)^(t[2]*p^m)*(PR.(n+2))^(t[3]*p^m) : t in derf ];

                            // create a vector to evaluate D_{r,n}
                            // to get D_{r,m}
                            v:=< PR!0 : s in [1..(2*n+2)] >;
                            for s in [2..(m+1)] do
                                v[s]:=PR.s;
                                v[s+n+1]:=PR.(s+n+1);
                            end for;
                            
                            // get D_{r,m} from D_{r,n}
                            // print "evaluate Ds";
                            tmp:=Evaluate(vecDs[[n,r,i,k,j-k]],v);
                            // print "pol root";
                            tmp:=Pol_Root(tmp,p^(n-m));

                            if #vvars ne 0 then
                                // print "evaluate";
                                res[m+1]:=res[m+1] cat [ Evaluate(term,vvars) : term in Terms(vt*tmp)];
                            else
                                res[m+1]:=res[m+1] cat Terms(vt*tmp);
                            end if;
                            
                        end for; // k
                        delete tmp, v, vt;
                    end for; // j
                end for; // m
            end if;
        end for; // i


    end for; // r

    // now add the etas...

    // print "pols = ", pols;

    for i in [1..n] do

        // print "res[", i, "] = ", res[i];

        //print "compute etas";
        ve:=vetav3(p,n-i+1,res[i] : bintab:=bintab);
        
        // print "ve = ", ve;

        for j in [(i+1)..(n+1)] do
            if ve[j-i] ne 0 then 
                Append(~res[j],ve[j-i]);
            end if;
        end for;

        // don't need all pols anymore
        bintab:=bintab[1..(n-i)];
    end for;

    return [ &+t : t in res ];

end function; 


// /////////////////////////////////////////////////
// WRAPPERS
// Use a single function to perform the operations
// /////////////////////////////////////////////////

function GT(f : choice:=1, pols:=[], bintab:=[], tab:=[], vvars:=[])
    if choice eq 2 then
        return GT2(f : bintab:=bintab, tab:=tab, vvars:=vvars);
    elif choice eq 3 then
        return GT3(f : bintab:=bintab, tab:=tab, vvars:=vvars);
    else
        return GT1(f : pols:=pols, tab:=tab, vvars:=vvars);
    end if;
end function;


// ///////////////////////////////////////
// POWERS
// ///////////////////////////////////////


function WittPower1(v,k : pols:=pols)
    //p:=Characteristic(Parent(v[1]));
    p:=Characteristic(Universe(v));
    F:=GF(p);
    l := #v;
    vone := [ F!1 ] cat [ F!0 : i in [2..l]];
    vzero:=[ F!0 : i in [1..l] ];
    return GT1([ [* vone, k, 0 *]]: pols:=pols, vvars:=v cat vzero);
end function;


function WittPower2(v,k : bintab:=bintab)
    //p:=Characteristic(Parent(v[1]));
    p:=Characteristic(Universe(v));
    F:=GF(p);
    l := #v;
    vone := [ F!1 ] cat [ F!0 : i in [2..l]];
    vzero:=[ F!0 : i in [1..l] ];
    return GT2([ [* vone, k, 0 *]]: bintab:=bintab, vvars:=v cat vzero);
end function;

function WittPower3(v,k : bintab:=bintab)
    //p:=Characteristic(Parent(v[1]));
    p:=Characteristic(Universe(v));
    F:=GF(p);
    l := #v;
    vone := [ F!1 ] cat [ F!0 : i in [2..l]];
    vzero:=[ F!0 : i in [1..l] ];
    return GT3([ [* vone, k, 0 *]]: bintab:=bintab, vvars:=v cat vzero);
end function;



function WittPower(v,k : choice:=1, pols:=[], bintab:=[])

    //P := Parent(v[1]);
    P := Universe(v);

    // if over a finite field, perform in Zq
    if IsFinite(P) and IsField(P) then
        p:=Characteristic(P);
        n:=#v-1;
        d:=Degree(P);
        Zp:=pAdicRing(p : Precision:=n+1);
        Zq<aa>:= ext<Zp | d>;
        v1 := WittVToSeries(v : Zq:=Zq);
        tmp := SeriesToWittV(Zq!(v1^k));
        return [ P!x : x in tmp ];
    end if;


    if choice eq 2 then
        return WittPower2(v, k : bintab:=bintab);
    elif choice eq 3 then
        return WittPower2(v, k : bintab:=bintab);
    else
        return WittPower1(v, k : pols:=pols);
    end if;
end function;    

