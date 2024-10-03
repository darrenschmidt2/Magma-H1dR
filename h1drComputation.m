/* This program computes H1 in the deRham cohomology of at level n of a Z_p tower of curves over P1 totally ramified over one point.*/

//Witt Vector Computations
load "gt.m";

/*
Find the leading term of f, where leadingterms are expressions for the leading terms of yn, ... y1, x 
in terms of a uniformizer (also denoted x)
n - level of the tower
f polynomial defining cover y^p -y = f
*/
function find_leadingterm(n,f,leadingterms)
	highest := LeadingTerm(Evaluate(f,leadingterms)) ;
    
	if highest eq 0 then
		assert(f eq 0); //something went wrong. leadingterms?
		return 0,0;
	end if;
	//return the coefficient and the exponent on the highest order term in the local expansion
	// using the last variable for a uniformizer
	return Coefficients(highest)[1], Exponents(highest)[n+1];
end function;

/*
Create a monomial of specific order at level
p - characteristic
level - which level to work at
x, ys[1], ... ys[n] : variables defining tower
ds : ramification invariants at at each level
exponent : the order to use
*/
function create_term(p,level,x,ys,ds,exponent)
	term := Parent(ys[level])!1;
	j := level-1;
	remaining := exponent;

	while remaining gt 0 and j gt 0 do
		newexp:= (Integers()!(remaining/p^(level-1-j)) * Modinv(ds[j],p)) mod p ;
		remaining := remaining - newexp * ds[j] * p^(level-1-j);
		term := term * ys[j]^(newexp);
		j := j-1;
	end while;
	
	//if this assertion fails, we haven't been able to produce the required function using this method
	//we can prove it will never fail for basic towers.  Not entirely sure about more general examples
	assert(remaining mod p^(level-1) eq 0);
	
	term := term * x^(Integers()! (remaining/(p^(level-1))));
	
	return term;
end function;

/*
Normalize the level of the ASW Witt tower to be in standard form
assume previous levels already dealt with
returns the standard form for f_level and the leading term in the expansion of y_level above infinity
p : characteristic
n : largest level in tower
ds : ramification invariants at at each level
x, ys[1], ... ys[n] : variables defining tower
f : polynomial for next level
leadingterms: precomputed leading terms for x, ys
level : level working at now
*/
function normalize_ASW_level(p,n,ds,x,ys,f,leadingterms,simplify,level)
	coeff,deg := find_leadingterm(n,f,leadingterms);
	y_mod :=0 ; //keep track of modifications to y_level
	while deg gt ds[level] do
		//the leading term has degree a multiple of p. Kill it off
		new_term := create_term(p,level,x,ys,ds,Integers()!(deg/p));
		
		newcoeff, newdeg := find_leadingterm(n,new_term^p - new_term,leadingterms);
		assert( newdeg eq deg);
		
		new_term := Root(coeff,p) * newcoeff^(-p) * new_term;
		//cancel out the biggest term		
		f:= simplify(f -  (new_term^p - new_term)) ; 
		y_mod := y_mod - new_term;
		old_deg := deg;
		coeff,deg := find_leadingterm(n,f,leadingterms);
		assert ( deg lt old_deg);
	end while;
	
	assert(deg eq ds[level]);
	return f, Root(coeff,p) * x^deg , y_mod;
end function;

/*Normalize the ASW tower to put it in Madden's standard form
p : characteristic
n : largest level in tower
P : multivariable polynomial ring in x, ys
ds : ramification invariants at at each level
x, ys[1], ... ys[n] : variables defining tower
fs : polynomials defining each extension (not in standard form yet)
*/
function normalize_ASW(p,n,P,ds,x,ys,fs)
	standard_f := [];
    yList := [];
	leadingterms := [0 : j in [1..n]] cat [x];
	
	for level in [1..n] do
		A,g:= quo<P | [ ys[j]^p - ys[j] - standard_f[j] : j in [1..level-1]]>;
		lift := Inverse(g); //g isn't invertible, but this picks a nice section
	
		//write things in standard forms using Artin-Schreier relations
		simplify := function(poly)
			return lift(g(poly));
		end function;
		
		//make a change of variable ys'[level] = ys[level] + y_mod
		//such that fs[level] + y_mod^p - y_mod is in standard form
		new_f,new_u,y_mod :=normalize_ASW_level(p,n,ds,x,ys,fs[level],leadingterms,simplify,level);
        
		Append(~standard_f,new_f);
		
		//update leading terms for next level
		for j in [n+2-level..n+1] do
			leadingterms[j] := Evaluate( leadingterms[j], x,x^p);
		end for;
	
		leadingterms[n+1-level] := new_u;
		
		//update later ys's based on change of variables ys[level] = ys'[level] - y_mod
		for j in [ level+1..n] do
			base_fsj := fs[j];
			//The simple thing to do would be to evalute as in the next line
			//fs[j] := simplify(Evaluate(fs[j],ys[level],ys[level] - y_mod));
			//But this involves a huge number of monomials.  Need to rewrite to be more efficient using relations 
			//by working on quotient ring
			coeffs := Coefficients(base_fsj,ys[level]);
			
			power := 0;
			accumulated := A!1;
			fsj_alt := A!0;
			
			while power lt # coeffs do
				fsj_alt := fsj_alt + g(coeffs[power+1]) * accumulated;
				accumulated := accumulated * g(ys[level] - y_mod);
				power +:=1;
			end while;
			
			
			//assert( lift(fsj_alt) eq fs[j]);
			fs[j]  := lift(fsj_alt);
		end for;
	end for;

	return standard_f;	
end function;

/*Decompose a function in x,y1,...,yn into its monomials
f : Function to decompose
p : prime
V : list of variables [x,y1,...,yn]
R : F_q[x]
*/
decompFunc := function(f,p,V,R)
    //List of coefficients of f viewed as a polynomial in the y variables
    L := Flat(f);
    A := [];
    F := [];
    C := [];
    degList := [];
    
    //Keeps track of the exponent for each y variable
    counter := [0 : i in [2 .. #V]];
    counter[1] := -1;
    
    for i in [1 .. #L] do
        //Iterates through y variable exponents
        for j in [1 .. #counter] do
            if counter[j] eq p-1 then
                counter[j] := 0;
            else
                counter[j] := counter[j] + 1;
                break;
            end if;
        end for;
        
        //For each non-zero function in L, grabs the number and stores it in C, and constructs the function without
        //the coefficient and stores it in F.
        if L[i] ne 0 then
            deg := Degree(Denominator(L[i]));
            g := L[i]*V[1]^(deg);
            h := R!g;
            A := Eltseq(h);
            for j in [1 .. #A] do
                if A[j] ne 0 then
                    Append(~C, A[j]);
                    l := V[1]^(j-1)/V[1]^deg;

                    degree := j-1 - deg;
                    for k in [1 .. #counter] do
                        l := l*V[k+1]^counter[k];
                    end for;
                    Append(~F, l);

                    Append(~degList, [degree] cat counter);
                end if;
            end for;
        end if;
    end for;
    
    //Returns functions and coefficients
    return F,C,degList;
end function;

/*Computes a basis of H1 of sheaf cohomology of the structure sheaf
The basis is of the form x^v*y1^{a1}*...*yn^{an}
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
N : Ceiling(2*g/p^n) where g is the genus of the curve
F : List of functions in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeH1R := function(n,L,N,B,p,V,d)
    F := [];
    degList := [];
    while L ne B do

        //Computes order of vanishing of function at infinity
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        //If this is true, function is a basis element. Append it to the list of functions F
        if vanishing gt 0 and vanishing le N*p^(n) then
            func := 1;
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            Append(~F,func);
            Append(~degList, L);
        end if;

        //Loops through all possible exponents up to their bounds
        if L[1] eq B[1] then
            L[1] := -N;

            for i in [2 .. #L] do
                if L[i] eq B[i] then
                    L[i] := 0;
                else
                    L[i] := L[i] + 1;
                    break;
                end if;
            end for;
        else
            L[1] := L[1] + 1;
        end if;
    end while;
    
    //Deals with the case where L = B
    vanishing := p^n*L[1];
    for i in [1 .. #L-1] do
        vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
    end for;


    if vanishing gt 0 and vanishing le N*p^(n) then
        func := 1;
        for i in [1 .. n+1] do
            func := func * V[i]^L[i];
        end for;

        Append(~F,func);
        Append(~degList, L);
        end if;
    
    return F, degList;
end function;

/* Computes functions of the form x^v y1^{a1} ... yn^{an} with order of vanishing at infinity
<= 0
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
N : Ceiling(2*g/p^n) where g is the genus of the curve
F : List of functions in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeP1 := function(n,L,N,B,p,V,d)
    F := [];
    degList := [];
    
    while L ne B do
        //Computes order of vanishing at infinity
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        //If order of vanishing <= 0, add function to function list
        if vanishing le 0 then
            func := 1;
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            Append(~F,func);
            Append(~degList, L);
        end if;

        if L[1] eq B[1] then
            L[1] := -N*p;

            for i in [2 .. #L] do
                if L[i] eq B[i] then
                    L[i] := 0;
                else
                    L[i] := L[i] + 1;
                    break;
                end if;
            end for;
        else
            L[1] := L[1] + 1;
        end if;
    end while;
    
    //Computes order of vanishing at infinity
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        //If order of vanishing <= 0, add function to function list
        if vanishing le 0 then
            func := 1;
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            Append(~F,func);
            Append(~degList, L);
        end if;
    
    return F, degList;

end function;

/* Computes functions of the form x^v y1^{a1} ... yn^{an} with order of vanishing at infinity
<= N*p^(n+1) and >= 0.
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
N : Ceiling(2*g/p^n) where g is the genus of the curve
F : List of functions in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeP2 := function(n,L,N,B,p,V,d)
    F := [];
    degList := [];
    
    while L ne B do
    
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        if vanishing le N*p^(n+1) then
            func := 1;
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            Append(~F,func);
            Append(~degList, L);
        end if;

        if L[1] eq B[1] then
            L[1] := 0;

            for i in [2 .. #L] do
                if L[i] eq B[i] then
                    L[i] := 0;
                else
                    L[i] := L[i] + 1;
                    break;
                end if;
            end for;
        else
            L[1] := L[1] + 1;
        end if;
    end while;
    
    vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        if vanishing le N*p^(n+1) then
            func := 1;
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            Append(~F,func);
            Append(~degList, L);
        end if;
    
    return F, degList;

end function;

/* Computes functions of the form x^v y1^{a1} ... yn^{an} with order of vanishing at infinity
<= p^(n+1)*N. Note that H1R = P12/(P1+P2).
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
N : Ceiling(2*g/p^n) where g is the genus of the curve
F : List of functions in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeP12 := function(n,L,N,B,p,V,d)
    F := [];
    degList := [];
    while L ne B do
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        if vanishing le p^(n+1)*N then
            func := 1;
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~degList, L);
            Append(~F,func);
        end if;

        if L[1] eq B[1] then
            L[1] := -N*p;

            for i in [2 .. #L] do
                if L[i] eq B[i] then
                    L[i] := 0;
                else
                    L[i] := L[i] + 1;
                    break;
                end if;
            end for;
        else
            L[1] := L[1] + 1;
        end if;
        
    end while;
    
    vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        if vanishing le p^(n+1)*N then
            func := 1;
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~degList,L);
            Append(~F,func);
        end if;
    
    return F, degList;

end function;

/* Computes basis of regular differentials of the form x^v y1^{a1} ... yn^{an}*dx using Madden's bounds
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
F : List of differentials in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeO := function(n,L,B,p,V,d)
    F := [];
    degList := [];
    
    while L ne B do
    
        rhs := -p^n-1;
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        /*Madden's paper shows basis elements are x^L[1]*y1^L[2]*...yn^L[n+1]
        with p^n*L[1] <= rhs from above*/
        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;
        L[1] := 0;

        for i in [2 .. #L] do
            if L[i] eq B[i] then
                L[i] := 0;
            else
                L[i] := L[i] + 1;
                break;
            end if;
        end for;
        
    end while;
    
    rhs := -p^n-1;
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        /*Madden's paper shows basis elements are x^L[1]*y1^L[2]*...yn^L[n+1]
        with p^n*L[1] <= rhs from above*/
        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;
    
    return F, degList;

end function;

/* Computes differentials of the form x^v y1^{a1} ... yn^{an}*dx
Basis elements of H1dR are of the form <f,w,t> where w, t are regular differentials and df=w-t.
O1 is where the differentials w are and O2 is where the differentials t are. O12 is a larger space where both are.
We require that v is non-positive.
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
F : List of differentials in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeO1 := function(n,L,N,B,p,V,d)
    F := [];
    degList := [];
    
    while L ne B do
        rhs := -p^n-1;
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;
        L[1] := -N-1;

        for i in [2 .. #L] do
            if L[i] eq B[i] then
                L[i] := 0;
            else
                L[i] := L[i] + 1;
                break;
            end if;
        end for;
    end while;
    
    rhs := -p^n-1;
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;

    return F, degList;

end function;

/* Computes differentials of the form x^v y1^{a1} ... yn^{an}*dx
Basis elements of H1dR are of the form <f,w,t> where w, t are regular differentials and df=w-t.
O1 is where the differentials w are and O2 is where the differentials t are. O12 is a larger space where both are.
We require here that v is non-negative.
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
F : List of differentials in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeO2 := function(n,L,N,B,p,V,d)
    F := [];
    degList := [];
    
    while L ne B do
        rhs := -p^n-1+p^n*(N+1);
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;
        L[1] := 0;

        for i in [2 .. #L] do
            if L[i] eq B[i] then
                L[i] := 0;
            else
                L[i] := L[i] + 1;
                break;
            end if;
        end for;
    end while;
    
    rhs := -p^n-1+p^n*(N+1);
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;

    return F, degList;

end function;

/* Computes differentials of the form x^n y1^{a1} ... yn^{an}*dx
Basis elements of H1dR are of the form <f,w,t> where w, t are regular differentials and df=w-t.
O1 is where the differentials w are and O2 is where the differentials t are. O12 is a larger space where both are.
Here v ranges over -N-1 to N+1
n : Level of the tower
L : list of starting values for exponents of the variables in the order x, y1, ..., yn
F : List of differentials in the basis, initially given as [].
B : List of bounds for the exponents of the variables in the same order as the initial values
p : prime
V : List of variables [x,y1,...,yn]
d : List of ramification invariants for levels 1 to n
*/
computeO12 := function(n,L,N,B,p,V,d)
    F := [];
    degList := [];
    
    while L ne B do
        rhs := -p^n-1+p^n*(N+1);
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;
        L[1] := -N-1;

        for i in [2 .. #L] do
            if L[i] eq B[i] then
                L[i] := 0;
            else
                L[i] := L[i] + 1;
                break;
            end if;
        end for;
    end while;
    
    rhs := -p^n-1+p^n*(N+1);
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            func := Differential(V[1]);
            for i in [1 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~F, func);
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;

    return F, degList;

end function;

computeCartier := function(f,R,p,x,A)
    dx := Differential(x);
    
    F := Flat(f);
        
    for a in F do
        if a ne 0 then
            xTerm := a;
                break;
        end if;
    end for;

    xPower := Exponents(R!xTerm)[1];

    k := Integers()!(Integers(p)!xPower);
    n := Integers()!((xPower - k)/p);
        
    expression := f*x^(k-xPower);
        
    if #A ne 0 then
        if IsDefined(A, expression) then
            return A[expression] * x^n, A;
        end if;
    end if;
    
    cart := Cartier(expression*dx) / dx;
    A[expression] := cart;
    return cart*x^n, A;
        
end function;

binarySearch := function(L,L1,n,p)
    /*coeffList1 := [0 : i in [1 .. n+1]];
    
    funcFlat := Flat(f);
    
    for i in [1 .. #funcFlat] do
        if funcFlat[i] ne 0 then
            coeffList1[1] := Degree(Numerator(funcFlat[i]))-Degree(Denominator(funcFlat[i]));
            break;
        end if;
        //Iterates through y variable exponents
        for j in [2 .. #coeffList1] do
            if coeffList1[j] eq p-1 then
                coeffList1[j] := 0;
            else
                coeffList1[j] := coeffList1[j] + 1;
                break;
            end if;
        end for;
    end for;
    */
    low := 1;
    high := #L;
    while low le high do
        midpoint := Floor((low + high)/2);
        L2 := L[midpoint];
        /*flatList := Flat(g);
        
        coeffList2 := [0 : i in [1 .. n+1]];
        
        for i in [1 .. #flatList] do
            if flatList[i] ne 0 then
                coeffList2[1] := Degree(Numerator(flatList[i]))-Degree(Denominator(flatList[i]));
                break;
            end if;
            //Iterates through y variable exponents
            for j in [2 .. #coeffList2] do
                if coeffList2[j] eq p-1 then
                    coeffList2[j] := 0;
                else
                    coeffList2[j] := coeffList2[j] + 1;
                    break;
                end if;
            end for;
        end for;*/
        
        compare := -1;
        
        for i in [#L1 .. 1 by -1] do
            if L1[i] gt L2[i] then
                 compare := 2;
                 break;
            
            
            elif L1[i] lt L2[i] then
                compare := 1;
                break;
            
            else
                compare := 0;
            end if;
        end for;
        
        if compare eq 0 then
            return midpoint, true;
        
        elif compare eq 1 then
            high := midpoint - 1;
        else
            low := midpoint + 1;
        end if;
            
    end while;
    
    return -1, false;
    
    
end function;

/*Computes H1 of deRham cohomology.
K : Function Field of the curve
d : Ramification invariant of the first level of the tower
n : level of the tower
f : polynomial such that y1^p-y1 = f
*/
computeH1dR := function(p,r,d,n,f)
    k := GF(p^r);
    R<x> := PolynomialRing(k);
    F := PolynomialRing(k,n+1);
    
    //Witt vector computations don't function correctly for n = 1
    if n eq 1 then
		a1 := F.1;
        t := F.2;
        ys := [a1];
        yp := [a1^p];
        AssignNames(~F,[ "a" cat IntegerToString(j) : j in [n..1 by -1]] cat ["t"]);
		ASW:=[a1^p -a1];
	else
        epols:=etapols(p,n-1); //characteristic p, length n
        t := F.(n+1);
        ys := [];
	
        AssignNames(~F,[ "a" cat IntegerToString(j) : j in [n..1 by -1]] cat ["t"]);
	
        for index in [n..1 by -1] do
            Append(~ys,F.index);
        end for;
	
        yp := [ys[i]^p : i in [1..n]];
        ASW:= WittDiff(yp,ys : pols:=epols);
    end if;

    //Break up the terms in the polynomial f.
    xs := Eltseq(f);
    
    //Adds up the witt vectors that are the monomials of f.
    v := [F!0 : j in [1 .. n]];
    
    if n ne 1 then
        v[1] := xs[1];
        for i in [1 .. #xs-1] do
            b := [F!0 : j in [1 .. n]];
            b[1] := xs[i+1]*t^i;
            v := WittSum(v,b : pols := epols);
        end for;
    else
        v[1] := Evaluate(f,t);
    end if;
    
    //Creates functions using Artin-Schreier-Witt theory with yi^p-yi=fs[i]
    fs := [yp[i] - ys[i] - ASW[i] + v[i] : i in [1 .. #ASW]];

    //Computes ramification invariants up to level n of the tower
    dList := [d];
    if n gt 1 then
        for i := 2 to n do
            Append(~dList, d*(p^(2*i-1)+1)/(p+1));
        end for;
    end if;

    //List of variables in the tower in Madden's standard form
    if n ne 1 then
        new_fs := normalize_ASW(p, n, F, dList, t, ys, fs);
    else
        new_fs := fs;
    end if;

    fieldList := [];
    varList := [];
    for i in [1 .. n] do

        if i eq 1 then
            L := FieldOfFractions(R);
        else
            L := fieldList[i-1];   
        end if;
        A := PolynomialRing(L);
        evalList := [0 : j in [1 .. (n+1)-i]] cat Reverse(varList) cat [x];

        g := A.1^p - A.1 - A!(Evaluate(F!new_fs[i], evalList));

        E := ext<L | g>;
        for j in [1 .. #varList] do 
            varList[j] := E!varList[j];
        end for;

        if i ne 1 then
            varList := ChangeUniverse(varList,E);
        end if;
        Append(~fieldList, E);
        Append(~varList, E.1);
    end for;
    
    K := fieldList[n];
    varList := [K!x] cat varList;
    
    x := varList[1];
    dx := Differential(x);
    
    //Computes genus
    g := 0.5*(d/(p+1)*p^(2*n) - p^n - (p+1+d)/(p+1))+1;
    
    N := Ceiling(2*g/p^n);
    
    //Sets initial list and bound lists and computes the bases of Riemann Roch spaces and differential spaces needed

    initList := [0 : i in [1 .. n+1]];
    
    boundList := [p-1 : i in [1 .. n+1]];
    
    
    initList[1] := -N;
    boundList[1] := -1;
   
    H1R, degH := computeH1R(n, initList, N, boundList, p, varList, dList);
    
    initList[1] := -N*p;
    boundList[1] := 0;

    P1, degP1 := computeP1(n, initList, N, boundList, p, varList, dList);
    
    initList[1] := 0;
    boundList[1] := N*p;
    
    P2, degP2 := computeP2(n, initList, N, boundList, p, varList, dList);
    
    initList[1] := -N*p;
    
    P12, degP12 := computeP12(n, initList, N, boundList, p, varList, dList);
    
    initList[1] := 0;
    boundList[1] := 0;
    
    O, degO := computeO(n, initList, boundList, p, varList, dList);
    
    initList[1] := -N-1;
    boundList[1] := -N-1;
    
    O1, degO1 := computeO1(n, initList, N, boundList, p, varList, dList);
    
    initList[1] := 0;
    boundList[1] := 0;
    
    O2, degO2 := computeO2(n, initList, N, boundList, p, varList, dList);
    
    initList[1] := -N-1;
    boundList[1] := -N-1;

    O12, degO12 := computeO12(n, initList, N, boundList, p, varList, dList);

    //Computes Frobenius on H1 of the structure sheaf. Applies the isomorphism and raises basis element to the pth power
    //then computes what the linear combination of elements of H1 of f^p is.
    FHN := [];

    for f in H1R do
        F,C, degF := decompFunc(f^p,p,varList,R);
        L := [0 : j in [1 .. #H1R]];
        for i in [1 .. #F] do
            if degF[i][1] lt 0 then
                _, inList := binarySearch(degP1, degF[i], n,p);
            else
                _, inList := binarySearch(degP2, degF[i], n, p);
            end if;

            if not inList then

                ind,_ := binarySearch(degH, degF[i],n,p);

                L[ind] := C[i];

            end if;
        end for;

        Append(~FHN,L);
    end for;



    //Computes matrix of Cartier operator on the regular differentials
    VHN := [];
    A := AssociativeArray();
    for w in O do
        vw, A := computeCartier(w/dx, R, p, x, A);
        F,C,degF := decompFunc(vw,p,varList,R);
        L := [0 : j in [1 .. #O]];
        for i in [1 .. #F] do
            ind,_ := binarySearch(degO,degF[i],n,p); 

            if ind ne -1 then
                L[ind] := C[i];
            end if;
        end for;
        Append(~VHN,L);
    end for;

    //Basis of quotient of O12 by O2
    O12q := [];
    degO12q := [];
    HyperClasses := [];
    for i in [1 .. #O12] do
        if not O12[i] in O2 then
            Append(~O12q, O12[i]);
            Append(~degO12q, degO12[i]);
        end if;
    end for;
    
    //Matrix of map of O1 into O12/O2.
    O1mat := [];
    
    for i in [1 .. #O1] do
        w := O1[i];
        L := [0 : j in [1 .. #O12q]];
        ind, _ := binarySearch(degO12q, degO1[i], n, p);
        if ind ne -1 then
            L[ind] := 1;
        end if;
        Append(~O1mat,L);
    end for;
   

    O1mat := Matrix(O1mat);
    O1mat := ChangeRing(O1mat, k);    
    V := VectorSpace(k, #O12q);
    
    //Computes basis elements of H1 deRham, which are of the form <f,u,v> with df = u+v, u in O1 and v in O2
    //Other basis elements are <0,w,w> with w a basis element of the regular differentials
    for f in H1R do
        //Computes what df is in O12/O2, then finds u in O1 such that u = df in O12/O2
        //Then v = df-u.
        df := Differential(f) / dx;
        F,C, degF := decompFunc(df, p, varList,R);
        uvec := [0 : j in [1 .. #O12q]];
        for i in [1 .. #F] do
            ind,_ := binarySearch(degO12q, degF[i], n,p);
            if ind ne -1 then
                uvec[ind] := C[i];
            end if;
        end for;
        
        uvec := V ! uvec;
        solu := Solution(O1mat,uvec);
        u := &+[solu[i]*O1[i] : i in [1 .. #O1]];
        v := df*dx - u;
        Append(~HyperClasses,<f,u,v>);
    end for;

    //Basis of P12/P2
    P12q := [];
    degP12q := [];
    for i in [1 .. #P12] do
        if not P12[i] in P2 then
            Append(~P12q, P12[i]);
            Append(~degP12q, degP12[i]);
        end if;
    end for;

    P1mat := [];
    
    //Constructs matrix of map of P1 into P12/P2
    for i in [1 .. #P1] do
        L := [0 : j in [1 .. #P12q]];
        ind, _ := binarySearch(degP12q, degP1[i], n,p);
        if ind ne -1 then
            L[ind] := 1;
        end if;
        Append(~P1mat,L);
    end for;

    V := VectorSpace(k,#P12q);
    P1mat := Matrix(P1mat);
    P1mat := ChangeRing(P1mat, k);
    FON := [];
    
    //Computes action of Frobenius on H1dR
    for i in [1 .. #H1R] do
        f := HyperClasses[i][1];
        
        //F(f_i, u_i, v_i) - Sum_j FHN[i,j]*(f_j , u_j, v_j) projects to 0 in H1 of structure sheaf
        Frobf := f^p - &+[FHN[i,j]*HyperClasses[j][1] : j in [1 .. #H1R]];
        vector := [0 : k in [1 .. #P12q]];
        
        //Computes what Frobf is in P12/P2.
        F,C, degF := decompFunc(Frobf, p, varList,R);
        for j in [1 .. #F] do
            ind := Index(P12q, F[j]);
            ind, _ := binarySearch(degP12q, degF[j], n, p);
            if ind ne -1 then
                vector[ind] := C[j];
            end if;
        end for;
        
        //Finds the u such that u is sent to Frobf in P12/P2
        //This gives that d(Frobf) = du + dv
        //du is in O1, dv is in O2
        vector := V ! vector;
        uvec := Solution(P1mat, vector);
        u := &+[uvec[j]*P1[j] : j in [1 .. #P1]];
        v := Frobf - u;
        
        //eta cancels out the -&+[FHN[i,j]*HyperClasses[j][1] : j in [1 .. #H1R]]
        eta := - &+[FHN[i,j]*HyperClasses[j][2]: j in [1 .. #H1R]];
        differential := eta - Differential(u);
        differential := differential / dx;
        
        //Then computes the linear combination of basis elements of differentials
        F,C, degF := decompFunc(differential, p, varList,R);
        L := [0 : k in [1 .. #O]];
        for j in [1 .. #F] do
            ind, _ := binarySearch(degO, degF[j], n, p);
            if ind ne -1 then
                L[ind] := C[j];
            end if;
        end for;
        
        Append(~FON, L);   
    end for; 
        
    VON := [];
    
    //Computes Cartier Operator on H1 deRham
    for i in [1 .. #H1R] do
        u := HyperClasses[i][2];
        Vu := Cartier(u) / dx;
        
        F,C, degF := decompFunc(Vu, p, varList,R);
        L := [0 : k in [1 .. #O]];
        for j in [1 .. #F] do
            ind := Index(O, F[j]*dx);
            ind, _ := binarySearch(degO, degF[j], n, p);
            if ind ne -1 then
                L[ind] := C[j];
            end if;
        end for;
        Append(~VON, L);
    end for;

    FHN := Matrix(k, FHN);
    FON := Matrix(k, FON);
    VHN := Matrix(k, VHN);
    VON := Matrix(k, VON);

    //Constructs Frobenius and Cartier matrices of size 2g x 2g
    F := VerticalJoin(HorizontalJoin(FHN, FON), ZeroMatrix(k, #H1R, 2*#H1R));

    V := VerticalJoin(HorizontalJoin(ZeroMatrix(k,#H1R,#H1R),VON),HorizontalJoin(ZeroMatrix(k,#H1R,#H1R),VHN));

    M := RModule(MatrixRing<k,2*#H1R | F,V>);
    //K`H1deRham := M;
    B := [*O, HyperClasses*];
    return M;
end function;

