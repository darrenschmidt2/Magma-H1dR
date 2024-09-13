// Computation of the eta polynomials that help with
// computations of Witt vectors

// /////////////////////////////////////////
// BASIC FUNCTIONS
// ////////////////////////////////////////


// For Witt Vectors over finite fields, operations are
// *MUCH* more efficient if converting to p-adic extensions

// convert a Witt vector over a finite field to p-adic power series
function WittVToSeries(v : Zq:=0)

    //FF:=Parent(v[1]);
    FF:=Universe(v);
    p:=Characteristic(FF);
    n:=#v-1;

    // if ring is not given, create it
    // if Zq cmpeq pAdicRing(2) then
    if Zq cmpeq 0 then
        k:=Degree(FF);
        Zp:=pAdicRing(p : Precision:=n+1);
        Zq<aa>:= ext<Zp | k>;
    end if;

    return &+[ Zq!TeichmuellerLift(Root(v[i],p^(i-1)),quo<Zq | p^(n+2-i)>)*p^(i-1) : i in [1..(n+1)] ];

end function;


// convert p-adic power series to a Witt vector
function SeriesToWittV(s : F:=0)

    Zq:=Parent(s);
    n:=Zq`DefaultPrecision-1;
    k:=Degree(Zq);
    p:=Prime(Zq);

    // if finite field not given, create it
    if F cmpeq 0 then
        F<a>:=GF(p^k);
    end if;

    v:=[];

    a:=s;
    for i in [0..n] do
        t:=F!a;
        Append(~v,t);
        tt:= Zq!TeichmuellerLift(t,quo<Zq | p^(n+1-i)>);
        a:=(a - tt) div p;
    end for;
    return [ v[i+1]^(p^i) : i in [0..n] ];

end function;



function IntToWitt(k,p,n)
    Zp := pAdicRing(p : Precision:=n+1);
    F:=GF(p);
    return SeriesToWittV(Zp!k : F:=F);
end function;




// OBSOLETE: the function above performs better!
/* // compute prim. roots of 1 to help */
/* // change integers to Witt vectors */
/* function GenPrimRoots(p,n) */
/*     if p eq 2 */
/*       then return [0,1]; */
/*     end if; */

/*     res:=[0,1]; */

/*     ZZ:=Integers(); */
/*     PR<x>:=PolynomialRing(ZZ); */
    

/*     R:=ResidueClassRing(p^n); */
    
/*     f:=x^(p-1)-1; */
/*     fp:=(p-1)*x^(p-2); */

/*     for i in [2..(p-2)] do */
/* 	root:=R!i; */
/* 	while (Evaluate(f,root) ne R!0) do  */
/* 	    root-:=Evaluate(f,root)/(Evaluate(fp,root)); */
/* 	end while; */
/* 	Append(~res,ZZ!root); */
/*     end for; */

/*     // Append(~res,-1); */
/*     Append(~res,p^n-1); */

/*     return(res); */

/* end function; */
	    


/* // Convert Integer to Witt Vector */
/* function IntToWitt(n,p,l : primr:=[]) */

/* // n = number to be converted */
/* // p = prime */
/* // l = length */
/* // primr = primitive roots  */

/*     Zp:=GF(p); */
/*     ZZ:=Integers(); */

/*     if primr eq [] */
/* 	then primr:=GenPrimRoots(p,l); */
/*     end if; */

/*     // print primr; */
    
/*     res:=[]; */
/*     numb:=n mod p^l; */
    
/*     for i in [1..l] do */
/* 	entry:=numb mod p; */
/* 	Append(~res,Zp!entry); */
/* 	// print "i = ", i; */
/* 	// print "numb = ", numb; */
/* 	// print "entry = ", entry; */
/* 	// print "primr[entry+1] = ", primr[entry+1]; */
/* 	// print "(numb-primr[entry+1]) div p = ", (numb-primr[entry+1]) div p; */
/* 	// print ""; */
/* 	numb:=((numb-primr[entry+1]) div p); */
/*     end for; */

/*     return res; */

/* end function; */


// ///////////////////////////////////////////////
// MAIN FUNCTIONS
// ///////////////////////////////////////////////


function etapols(p,n)
    // compute eta polyn.
    PP<x,y>:=PolynomialRing(ResidueClassRing(p),2);
    res:=[* *];
    // res[i], at first has p^i*eta_i
    for i in [1..n] do
        P1<x,y>:=PolynomialRing(ResidueClassRing(p^(i+1)),2);
        res[i]:=x^(p^i)+y^(p^i) - (x+y)^(p^i);
    end for;
    // fix eta_1, which is done
    res[1]:=PP!(res[1] div p);
    // now add the power of the terms which we finish
    for i in [2..n] do
        t:=res[i-1];
        // add the powers of the precomputed to all
        for j in [i..n] do
            P1:=Parent(res[j]);
            t:=(P1!t)^p;
            res[j]-:=p^(i-1)*t;
        end for;
        res[i]:=PP!(res[i] div p^i);
       // res[i] is done!
    end for;
    return [x : x in res];
end function;




// remove zeros of a vector to simplify comp. of etas
// if v is all zeros, return [0] to avoid problems with &+[]
function vRemoveZeros(v)

    tmp:=[ x : x in v | x ne 0 ];
    if #tmp ne 0 then
        return tmp;
    else
        if #v eq 0 then
            return [ 0 ];
        else
            return [ Parent(v[1])!0 ];
        end if;
    end if;
end function;


// MOST EFFICIENT (it seems)
// seems to work better than vetav2 and vetav3
function vetav(p,k,v : pols:=[ ])
    // the input v is a vector!
    // the output is a vector of resulting
    //    polynomials eta_i(v) for i=1, ... , k

    // firts, remove zeros!
    v:=vRemoveZeros(v);

    lgt:=#v;
    // print "length = ", lgt;
    if lgt eq 1 then
        P:=Parent(v[1]);
        return [ P!0 : i in [1..k] ];
    end if;
    if pols eq [ ] then
        pols:=etapols(p,k);
    end if;
    if lgt eq 2 then
        // //////////////////////////////////////////////////////////////////////
        // now, the special case of #v=2
        // //////////////////////////////////////////////////////////////////////
        return [ Evaluate(pol,v) : pol in pols ]; // needs to have pols precomputed
    else
        // //////////////////////////////////////////////////////////////////////
        // now if #v>2
        // split v in two
        v1:=[ v[i] : i in [1..(lgt div 2)] ];
        v2:=[ v[i] : i in [((lgt div 2)+1)..lgt] ];
        x1:=$$(p,k,v1 : pols:=pols);
        x2:=$$(p,k,v2 : pols:=pols);
        x3:=$$(p,k,[ &+v1, &+v2 ] : pols:=pols);
        res:=[ ];
        for i in [1..k] do
            // print "i = ", i;
            // print res;
            // print Parent(x1[i]), Parent(x2[i]), Parent(x3[i]);
            // print x1[i], x2[i], x3[i];
            res[i]:=vRemoveZeros([ x1[i],x2[i],x3[i] ]);
        end for;
        delete x1,x2,x3,v1,v2;
        for i in [2..k] do
            // lim1:=#res[i-1]; // should be 2^(i-2)*3-(2^(i-2)-1);
            // // print lim1 eq 2^(i-2)*3-(2^(i-2)-1);
            // for j in [1..(lim1-1)] do
            //     temp:=$$(p,k-i+1,[res[i-1][j],&+( res[i-1][(j+1)..lim1] )] : pols:=pols[1..(k-i+1)]);
            //     for t in [1..(k-i+1)] do
            //         Append(~res[i-1+t],temp[t]);
            //     end for;
            // end for;
            // delete temp;
            pols:=pols[1..(k-i+1)];
            tmp:=$$(p,k-i+1,res[i-1] : pols:=pols);
            for t in [i..k] do
                if tmp[t-i+1] ne 0 then 
                    Append(~res[t],tmp[t-i+1]);
                end if;
            end for;
            delete tmp;
        end for;
        return [ &+x : x in res ];
    end if;
end function;


// below we introduce a procedure to evaluate the
// eta functions without having to store them.
// saves memory, but can be slower


function BinTab(p,k)
    // gives back the bin. coeff need for vetav2

    /* if #primr eq 0 then */
    /*     primr:=GenPrimRoots(p,k+1); // to convert to bin. to Witt vec */
    /* end if; */

    R:=ResidueClassRing(p^(k+1));
    ZZ:=Integers();

    par:=(p mod 2); // partity of p

    res:=[ ];
    for i in [1..k] do
        num:=p^i; 
        tmp:=[ R!1 ];  // 1/p*Biniomial(p,1)
        for j in [2..(num-1)] do
            a:=num-(j-1);
            a:=R!(a div p^(Valuation(j-1,p)));
            b:=R!(j div p^(Valuation(j,p)));
            Append(~tmp,tmp[j-1]*a*b^(-1)); // add next binomial
            delete a, b;
        end for;
        Append(~res,[ IntToWitt(-ZZ!(tmp[j]),p,Valuation(j,p))[Valuation(j,p)+1] : j in [1..#tmp] ]); // conv to Witt vec and take right coord

        delete tmp;

        // now add the symmetric part at the end
        bg:=((num-par) div 2)+1;
        for j in [bg..(num-1)] do
            res[i][j]:=res[i][num-j];
        end for;
    end for;

    return res;
end function;




vetav2 := function(p,k,v : bintab:=[] )
    // the input v is a vector!
    // the output is a vector of resulting
    //    polynomials eta_i(v) for i=1, ... , k

    // firts, remove zeros!
    v:=vRemoveZeros(v);
    
    lgt:=#v;
    // print "length = ", lgt;
    if lgt eq 1 then
        P:=Parent(v[1]);
        return [ P!0 : i in [1..k] ];
    end if;

    if #bintab eq 0 then
        // bintab:=BinTab(p,k);
        bintab:=BinTab(p,k);
    end if;

    //print bintab;

    if lgt eq 2 then

        x:=v[1];
        y:=v[2];


        res:=[];

        for j in [1..k] do
           res[j]:=[ bintab[j][i]*x^i*y^(p^j-i) : i in [1..(p^j-1)]];
        end for;

        for j in [1..(k-1)] do
            v:=$$(p,k-j,res[j] : bintab:=bintab );
            for i in [1..(k-j)] do
                if v[i] ne 0 then 
                    Append(~res[j+i],v[i]);
                end if;
            end for;
        end for;
        
        return [ &+term : term in res];


    else
        // //////////////////////////////////////////////////////////////////////
        // now if #v>2
        // split v in two
        v1:=[ v[i] : i in [1..(lgt div 2)] ];
        v2:=[ v[i] : i in [((lgt div 2)+1)..lgt] ];
        x1:=$$(p,k,v1 : bintab:=bintab );
        x2:=$$(p,k,v2 : bintab:=bintab );
        x3:=$$(p,k,[ &+v1, &+v2 ] : bintab:=bintab );
        res:=[ ];
        for i in [1..k] do
            //print "i = ", i;
            //print res;
            //print Parent(x1[i]), Parent(x2[i]), Parent(x3[i]);
            //print x1[i], x2[i], x3[i];
            //print vRemoveZeros([ x1[i],x2[i],x3[i] ]);
            res[i]:=vRemoveZeros([ x1[i],x2[i],x3[i] ]);
            //Append(~res,vRemoveZeros([ x1[i],x2[i],x3[i] ]));
        end for;
        delete x1,x2,x3,v1,v2;
        for i in [2..k] do
            // lim1:=#res[i-1]; // should be 2^(i-2)*3-(2^(i-2)-1);
            // // print lim1 eq 2^(i-2)*3-(2^(i-2)-1);
            // for j in [1..(lim1-1)] do
            //     temp:=$$(p,k-i+1,[res[i-1][j],&+( res[i-1][(j+1)..lim1] )] : pols:=pols[1..(k-i+1)]);
            //     for t in [1..(k-i+1)] do
            //         Append(~res[i-1+t],temp[t]);
            //     end for;
            // end for;
            // delete temp;
            tmp:=$$(p,k-i+1,res[i-1] : bintab:=bintab );
            for t in [i..k] do
                if tmp[t-i+1] ne 0 then 
                    Append(~res[t],tmp[t-i+1]);
                end if;
            end for;
            delete tmp;
        end for;

        return [ &+x : x in res ];
    end if;
end function;





// in this one we have first a procedure which will store ALL
// precomputed terms in the "associative array" pre
procedure vetav3p(p,k,v,~pre : bintab:=[] )
    // the input v is a vector!
    // the output is a vector of resulting
    //    polynomials eta_i(v) for i=1, ... , k


    if (not IsDefined(pre,<k,v>)) and (not IsDefined(pre,<k,vRemoveZeros(v)>)) then 

        // firts, remove zeros!
        v:=vRemoveZeros(v);

        lgt:=#v;
        // print "length = ", lgt;
        if lgt eq 1 then
            P:=Parent(v[1]);
            for i in [1..k] do
                pre[<i,v>]:= P!0;
            end for;
        else

            if #bintab eq 0 then
                // bintab:=BinTab(p,k);
                bintab:=BinTab(p,k);
            end if;

            //print bintab;

            if lgt eq 2 then

                x:=v[1];
                y:=v[2];

                res:=[];

                for j in [1..k] do
                    res[j]:=vRemoveZeros([ bintab[j][i]*x^i*y^(p^j-i) : i in [1..(p^j-1)]]);
                end for;


                for j in [1..(k-1)] do
                    if #res[j] ne 1 then
                        // print "res[",j,"] =", res[j];
                        if not IsDefined(pre,<k-j,res[j]>) then
                            $$(p,k-j,res[j],~pre : bintab:=bintab );
                        end if;
                        for i in [1..(k-j)] do
                            // print "i = ", i;
                            // if we have <k-j,res[j]>, we have all previous!
                            // print res[j];
                            if pre[<i,res[j]>] ne 0 then 
                                Append(~res[j+i],pre[<i,res[j]>]);
                            end if;
                        end for;
                    end if;
                end for;

                for t in [1..k] do
                    if not IsDefined(pre,<t,v>) then
                        pre[<t,v>]:=&+res[t];
                    end if;
                end for;

            else
                // //////////////////////////////////////////////////////////////////////
                // now if #v>2
                // split v in two
                v1:=[ v[i] : i in [1..(lgt div 2)] ];
                v2:=[ v[i] : i in [((lgt div 2)+1)..lgt] ];
                v3:=vRemoveZeros([ &+v1, &+v2 ]);
                
                if (#v1 ne 1) and (not IsDefined(pre,<k,v1>)) then
                    $$(p,k,v1,~pre : bintab:=bintab);
                end if;
                
                if not IsDefined(pre,<k,v2>) then
                    $$(p,k,v2,~pre : bintab:=bintab);
                end if;

                if (#v3 ne 1) and (not IsDefined(pre,<k,v3>)) then
                    $$(p,k,v3,~pre : bintab:=bintab);
                end if;


                // print "keys = ", Keys(pre);
                // print "v1 = ", v1;
                // print "v2 = ", v2;
                // print "v3 = ", v3;
                // print "k = ", k;
                res:=[ ];
                for i in [1..k] do
                    // print "i = ", i;
                    // print res;
                    // print Parent(x1[i]), Parent(x2[i]), Parent(x3[i]);
                    // print x1[i], x2[i], x3[i];
                    if #v1 ne 1 then
                        if #v3 ne 1 then
                            res[i]:=vRemoveZeros([ pre[<i,v1>],pre[<i,v2>],pre[<i,v3>] ]);
                        else
                            res[i]:=vRemoveZeros([ pre[<i,v1>],pre[<i,v2>] ]);
                        end if;
                    else
                        if #v3 ne 1 then
                            res[i]:=vRemoveZeros([ pre[<i,v2>],pre[<i,v3>] ]);
                        else
                            res[i]:=[ pre[<i,v2>] ];
                        end if;
                    end if;
                end for;
                delete v1,v2,v3;
                for i in [2..k] do
                    // lim1:=#res[i-1]; // should be 2^(i-2)*3-(2^(i-2)-1);
                    // // print lim1 eq 2^(i-2)*3-(2^(i-2)-1);
                    // for j in [1..(lim1-1)] do
                    //     temp:=$$(p,k-i+1,[res[i-1][j],&+( res[i-1][(j+1)..lim1] )] : pols:=pols[1..(k-i+1)]);
                    //     for t in [1..(k-i+1)] do
                    //         Append(~res[i-1+t],temp[t]);
                    //     end for;
                    // end for;
                    // delete temp;
                    if not IsDefined(pre,<k-i+1,vRemoveZeros(res[i-1])>) then
                        $$(p,k-i+1,res[i-1],~pre : bintab:=bintab );
                    end if;
                    for t in [i..k] do
                        if pre[<t-i+1,vRemoveZeros(res[i-1])>] ne 0 then
                            Append(~res[t],pre[<t-i+1,vRemoveZeros(res[i-1])>]);
                        end if;
                    end for;
                end for;

                for t in [1..k] do
                    if not IsDefined(pre,<t,v>) then
                        pre[<t,v>]:=&+res[t];
                    end if;
                end for;

            end if;

        end if;
    end if;
end procedure;


function vetav3(p,k,v : bintab:=[] )

    // firts, remove zeros!
    v:=vRemoveZeros(v);

    pre:=AssociativeArray();
    vetav3p(p,k,v,~pre : bintab:=bintab);
    return [ pre[<i,v>] : i in [1..k] ];
end function;







// raise terms to p^r
pterms := function(f,p,r)
    return &+[ x^(p^r) : x in Terms(f) ];
end function;




