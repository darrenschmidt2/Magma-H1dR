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
computeH1R := function(n,L,N,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    while L ne B do

        //Computes order of vanishing of function at infinity
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        //If this is true, function is a basis element. Append it to the list of functions F
        if vanishing gt 0 and vanishing le N*p^(n) then
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
            end if;
            
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter+1;
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
        if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
        for i in [2 .. n+1] do
            func := func * V[i]^L[i];
        end for;

        dict[lift(func)] := counter;
        Append(~funcList,lift(func));
        Append(~degList, L);
        end if;
    
    return dict, funcList;
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
computeP1 := function(n,L,N,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    
    while L ne B do
        //Computes order of vanishing at infinity
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        //If order of vanishing <= 0, add function to function list
        if vanishing le 0 then
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
            end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter + 1;
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
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            Append(~degList, L);
        end if;
    
    return dict, funcList;

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
computeP2 := function(n,L,N,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    
    while L ne B do
    
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        if vanishing le N*p^(n+1) then
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter+1;
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
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;

            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            Append(~degList, L);
        end if;
    
    return dict, funcList;

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
computeP12 := function(n,L,N,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    while L ne B do
        vanishing := p^n*L[1];
        for i in [1 .. #L-1] do
            vanishing := vanishing + p^(n-i)*d[i]*L[i+1];
        end for;

        if vanishing le p^(n+1)*N then
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~degList, L);
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter+1;
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
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            Append(~degList,L);
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));

        end if;
    
    return dict, funcList;

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
computeO := function(n,L,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    
    while L ne B do
    
        rhs := -p^n-1;
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        /*Madden's paper shows basis elements are x^L[1]*y1^L[2]*...yn^L[n+1]
        with p^n*L[1] <= rhs from above*/
        while p^n*L[1] le rhs do
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter+1;
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
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[2]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;
    
    return dict, funcList;

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
computeO1 := function(n,L,N,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    
    while L ne B do
        rhs := -p^n-1;
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter + 1;
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
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;

    return dict, funcList;

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
computeO2 := function(n,L,N,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    
    while L ne B do
        rhs := -p^n-1+p^n*(N+1);
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter+1;
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
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;

    return dict, funcList;

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
computeO12 := function(n,L,N,B,p,V,d,lift)
    dict := AssociativeArray();
    funcList := [];
    counter := 1;
    degList := [];
    
    while L ne B do
        rhs := -p^n-1+p^n*(N+1);
        for i in [1 .. n] do
            rhs := rhs + (p-1)*p^(n-i)*d[i] - p^(n-i)*d[i]*L[i+1];
        end for;

        while p^n*L[1] le rhs do
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            counter := counter+1;
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
            if L[1] lt 0 then
                func := (1/V[1])^AbsoluteValue(L[1]);
            else
                func := V[1]^L[1];
        end if;
            for i in [2 .. n+1] do
                func := func * V[i]^L[i];
            end for;
            dict[lift(func)] := counter;
            Append(~funcList,lift(func));
            Append(~degList, L);
            L[1] := L[1] + 1;
        end while;

    return dict, funcList;

end function;

//Computes Cartier operator using semi-linearity. Breaks differential into sum of monomials and reduces powers mod p.
//Cartier operator on monomials can then be computed by using the quotient relations and using results from lower down the tower
//funcList: quotient relation functions
//df: differential form
//p: Prime
//varList: [x,y1,y2,...]
//cartierDict: Dictionary starting the result of the Cartier operator on monomial differential forms.
//A: Highest level of the tower
computeCartier := function(funcList,df,p,varList,cartierDict,R,B,A,P)
    x := varList[1];
    df := P!df;

    //Breaks up differential into monomials.
    n := #varList;
    xDegrees := [];
    coefficients := [];
    //monomials := Monomials(df);
    terms := [];
 
    tempTerms := Terms(df);

        for term in tempTerms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));
            
            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);
            

            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                if coeffList[i] ne 0 then
                    dictTerm := P!(monomialList[i]*term/(xTerm* x^xDegree));
                    xCoeff := Coefficients(dictTerm);
                    deg := Degree(Numerator(xCoeff[#xCoeff])) - Degree(Denominator(xCoeff[#xCoeff]));
                    Append(~xDegrees, deg);

                    Append(~terms, dictTerm);
                    Append(~coefficients, coeffList[i]);
                end if;
            end for;
        end for;
    
 
    cartierComp := 0;

    for i in [1 .. #terms] do
        
        //Reduces powers of each variable in monomial mod p
        exponents := [xDegrees[i]] cat Reverse(Exponents(terms[i]));

        modList := [Abs(exponents[j]) mod p : j in [1 .. n]];
        multipleList := [exponents[j] ge 0 select Integers()!((exponents[j]-modList[j])/p) else Integers()!((exponents[j]+modList[j])/p) : j in [1 .. n]];

        expression := &*[exponents[j] ge 0 select varList[j]^modList[j] else 1/varList[j]^modList[j] : j in [1 .. n]];
        
        newExpression := &*[multipleList[j] ge 0 select varList[j]^multipleList[j] else 1/varList[j]^Abs(multipleList[j]) : j in [1 .. n]];
        
        //Refers to dictionary to compute Cartier, or reduces down using function relations with the x's and y_i's

        if IsDefined(cartierDict, expression) then
            
            cartierComp := cartierComp + 
            coefficients[i] * cartierDict[expression] * newExpression;
        else

            for j in [#exponents .. 2 by -1] do
                if modList[j] ne 0 then

                    cartier := &+[varList[j]^l*Binomial(modList[j],l)*$$(funcList, A!(expression/(varList[j]^modList[j])*(-funcList[j-1])^(modList[j]-l)),p,varList,cartierDict,R,B,A,P) : l in [0 .. modList[j]]];
                    cartierDict[expression] := cartier;
                    cartierComp := cartierComp + coefficients[i]*cartier * newExpression;
                    break;
                end if;
            end for;
        end if;
    end for;

    return cartierComp;

        
end function;

//Given a function f computes df.
//f: Input function
//dys: A list giving what dy_i equals in terms of dx
//varList: [x,y1,y2,...]
//n: Level of tower
computeDifferential := function(f,dys,varList,n)

    if f eq 0 then
        return 0;
    end if;
    monomials := Monomials(f);
    coeff := Coefficients(f);
    differential := monomials[#monomials]*Derivative(coeff[#coeff]);
    
    if n ne 1 then
    
        differential := differential + &+[Derivative(f,varList[i])*dys[i] : i in [2 .. #varList]];
    else
        differential := differential + Derivative(f)*dys[2];

    end if;
    
    return differential;

end function;

/*Computes H1 of deRham cohomology.
K : Function Field of the curve
d : Ramification invariant of the first level of the tower
n : level of the tower
f : polynomial such that y1^p-y1 = f
*/
computeH1dR := function(p,r,n,f)
    k := GF(p^r);
    R<x> := FunctionField(k);
    
    //Witt vector computations don't function correctly for n = 1
    if n eq 1 then
		A<a1,b>:= PolynomialRing(k,2);
		as := [a1];
        ap := [a1^p];
		ASW:=[a1^p -a1];
        
	else
	
        A:= PolynomialRing(k,n+1);
        b := A.(n+1);
        as := [];
	
        AssignNames(~A,[ "a" cat IntegerToString(j) : j in [n..1 by -1]] cat ["b"]);
	
        for index in [n..1 by -1] do
            Append(~as,A.index);
        end for;
	
        ap := [as[i]^p : i in [1..n]];
        epols:=etapols(p,n-1); //characteristic p, length n
        ASW:= WittDiff(ap,as : pols:=epols);
    end if;
    
    if n eq 1 then
		P<y1>:= PolynomialRing(R);

        ys := [y1];
	else
	
        P:= PolynomialRing(R,n);
        ys := [];
	
        AssignNames(~P,[ "y" cat IntegerToString(j) : j in [n..1 by -1]]);
        
        for index in [n..1 by -1] do
            Append(~ys,P.index);
        end for;

    end if;
    
    
    //Break up the terms in the polynomial f.
    xs := Eltseq(f);
    
    //Adds up the witt vectors that are the monomials of f.
    v := [A!0 : j in [1 .. n]];
    
    if n ne 1 then
        v[1] := xs[1];
        for i in [1 .. #xs-1] do
            sumTerm := [A!0 : j in [1 .. n]];
            sumTerm[1] := xs[i+1]*b^i;
            v := WittSum(v,sumTerm : pols := epols);
        end for;
    else
        v[1] := Evaluate(f,b);
    end if;

    //Creates functions using Artin-Schreier-Witt theory with yi^p-yi=fs[i]
    fs := [ap[i] - as[i] - ASW[i] + v[i] : i in [1 .. #ASW]];
    
    print("Witt vector calculations done");

    //Computes ramification invariants up to level n of the tower
    d := Degree(f);
    dList := [d];
    if n gt 1 then
        for i := 2 to n do
            Append(~dList, d*(p^(2*i-1)+1)/(p+1));
        end for;
    end if;

    //List of variables in the tower in Madden's standard form
    if n ne 1 then
        new_fs := normalize_ASW(p, n, A, dList, b, as, fs);
    else
        new_fs := fs;
    end if;
    
    x := P!x;
    varList := [x] cat ys;
    
    
    //gs are the functions defining the tower in terms of x,y1,y2,...
    //dys is a list of functions f_i such that dy_i = f_i dx
    gs := [];
    dys := [1,-1*Evaluate(Derivative(new_fs[1],b), Reverse(varList))];

    for i in [1 .. n] do
        newFunc := Evaluate(new_fs[i], Reverse(varList));
        Append(~gs,newFunc);
    end for;
    
    for i in [2 .. n] do
        newFunc := Evaluate(Derivative(-1*new_fs[i],A.(n+1)), Reverse(varList)) + &+[Evaluate(Derivative(-1*new_fs[i], A.j) ,Reverse(varList)) * dys[n-j+2] : j in [n .. n-i+2 by -1]];
        Append(~dys, newFunc);
    end for;

    print("Tower now in standard form");


    A, h := quo<P | [ys[i]^p - ys[i] - gs[i] : i in [1 .. n]]>;
    lift := Inverse(h);

    
    print("Tower constructed");

    
    //Computes genus
    g := 0.5*(d/(p+1)*p^(2*n) - p^n - (p+1+d)/(p+1))+1;
    
    N := Ceiling(2*g/p^n);
    
    //Sets initial list and bound lists and computes the bases of Riemann Roch spaces and differential spaces needed

    initList := [0 : i in [1 .. n+1]];
    
    boundList := [p-1 : i in [1 .. n+1]];
    
    
    initList[1] := -N;
    boundList[1] := -1;
   
    H1RDict, H1R := computeH1R(n, initList, N, boundList, p, varList, dList, lift);

    print("H1R computed");

    initList[1] := -N*p;
    boundList[1] := 0;

    P1Dict, P1 := computeP1(n, initList, N, boundList, p, varList, dList, lift);
    print("P1 computed");
    
    
    initList[1] := 0;
    boundList[1] := N*p;
    
    P2Dict, P2 := computeP2(n, initList, N, boundList, p, varList, dList, lift);
    print("P2 computed");
    initList[1] := -N*p;
    
    P12Dict, P12 := computeP12(n, initList, N, boundList, p, varList, dList, lift);
    print("P12 computed");
    initList[1] := 0;
    boundList[1] := 0;
    
    ODict, O := computeO(n, initList, boundList, p, varList, dList, lift);
    print("O computed");
    initList[1] := -N-1;
    boundList[1] := -N-1;
    
    O1Dict, O1 := computeO1(n, initList, N, boundList, p, varList, dList, lift);
    print("O1 computed");
    initList[1] := 0;
    boundList[1] := 0;
    
    O2Dict, O2 := computeO2(n, initList, N, boundList, p, varList, dList, lift);
    print("O2 computed");
    initList[1] := -N-1;
    boundList[1] := -N-1;

    O12Dict, O12 := computeO12(n, initList, N, boundList, p, varList, dList, lift);
    print("O12 computed");
    
    

    //Computes Frobenius on H1 of the structure sheaf. Applies the isomorphism and raises basis element to the pth power
    //then computes what the linear combination of elements of H1 of f^p is.
    FHN := [];


    B := RingOfIntegers(R);

    for f in H1R do
        terms := Terms(lift(f^p));

        entry := [0 : i in [1..g]];
        for term in terms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));

            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);


            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                dictTerm := monomialList[i]*term/(xTerm* x^xDegree);

                if IsDefined(H1RDict,dictTerm) then
                    index := H1RDict[dictTerm];
                    
                    entry[index] := entry[index]+coeffList[i];

                end if;
                
            end for;
        
        end for;
        Append(~FHN, entry);
    end for;
    
    print("Constructed F on functions");

    //Computes matrix of Cartier operator on the regular differentials
    VHN := [];
    

    cartierDict := AssociativeArray();
    for i in [0 .. p-2] do
        cartierDict[varList[1]^i] := 0;
    end for;
    
    for i in [2 .. p-1] do
        cartierDict[1/varList[1]^i] := 0;
    end for;
    
    cartierDict[varList[1]^(p-1)] := 1;
    cartierDict[1/varList[1]] := 1/varList[1];

    for w in O do
        cartierResult := computeCartier(gs, P!w, p, varList, cartierDict,R,B,A,P);

        terms := Terms(lift(cartierResult));
        entry := [0 : i in [1..g]];
        for term in terms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));

            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);


            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                dictTerm := monomialList[i]*term/(xTerm* x^xDegree);
                if IsDefined(ODict,dictTerm) then
                    index := ODict[dictTerm];

                    entry[index] := entry[index]+coeffList[i];
                end if;
                
            end for;
            
        end for;
        Append(~VHN, entry);
    end for;

    print("Constructed V on differentials");


    
    
    //Basis of quotient of O12 by O2
    O12qDict := AssociativeArray();
    O12q := [];
    counter := 1;
    HyperClasses := [];
    for w in O12 do
        if not IsDefined(O2Dict, w) then
            O12qDict[w] := counter;
            counter := counter + 1;
            Append(~O12q, w);
        end if;
    end for;
    

    //Matrix of map of O1 into O12/O2.
    O1mat := [];
    
    for w in O1 do
        L := [0 : j in [1 .. #O12q]];
        
        if IsDefined(O12qDict, w) then
            L[O12qDict[w]] := 1;
        end if;
        
        Append(~O1mat,L);
    end for;
   
    
    O1mat := Matrix(O1mat);
    O1mat := ChangeRing(O1mat, k);    
    V := VectorSpace(k, #O12q);
     print("Built O quotient matrix"); 

     

    //Computes basis elements of H1 deRham, which are of the form <f,u,v> with df = u+v, u in O1 and v in O2
    //Other basis elements are <0,w,w> with w a basis element of the regular differentials
    for f in H1R do
        //Computes what df is in O12/O2, then finds u in O1 such that u = df in O12/O2
        //Then v = df-u.
        df := computeDifferential(f,dys,varList,n);
        
        terms := Terms(lift(df));
        uvec := [0 : i in [1..#O12q]];
        for term in terms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));

            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);


            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                dictTerm := monomialList[i]*term/(xTerm* x^xDegree);
                if IsDefined(O12qDict,dictTerm) then
                    index := O12qDict[dictTerm];

                    uvec[index] := uvec[index]+coeffList[i];
                end if;
                
            end for;
            
        end for;
        
        uvec := V ! uvec;
        solu := Solution(O1mat,uvec);
        u := &+[solu[i]*O1[i] : i in [1 .. #O1]];

        v := df - u;
        Append(~HyperClasses,<lift(f),lift(u),lift(v)>);
    end for;
    print("Constructed hyperclasses");

    //Basis of P12/P2
    P12q := [];
    counter := 1;
    P12qDict := AssociativeArray();
    for f in P12 do
        if not IsDefined(P2Dict, f) then
            Append(~P12q, f);
            P12qDict[f] := counter;
            counter := counter+1;
        end if;
    end for;

    P1mat := [];
    
    //Constructs matrix of map of P1 into P12/P2
    for f in P1 do
        L := [0 : j in [1 .. #P12q]];

        if IsDefined(P12qDict, f) then
            L[P12qDict[f]] := 1;
        end if;
        Append(~P1mat,L);
    end for;
    
    
    V := VectorSpace(k,#P12q);
    P1mat := Matrix(P1mat);
    P1mat := ChangeRing(P1mat, k);
    
    FON := [];
    
    print("Constructed P quotient matrix");
    
    //Computes action of Frobenius on H1dR
    for i in [1 .. #H1R] do
        f := HyperClasses[i][1];
        
        //F(f_i, u_i, v_i) - Sum_j FHN[i,j]*(f_j , u_j, v_j) projects to 0 in H1 of structure sheaf
        Frobf := f^p - &+[FHN[i,j]*HyperClasses[j][1] : j in [1 .. #H1R]];
        vector := [0 : k in [1 .. #P12q]];
        
        //Computes what Frobf is in P12/P2.
        terms := Terms(lift(Frobf));
        for term in terms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));

            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);


            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                dictTerm := monomialList[i]*term/(xTerm* x^xDegree);
                if IsDefined(P12qDict,dictTerm) then
                    index := P12qDict[dictTerm];

                    vector[index] := vector[index]+coeffList[i];
                end if;
                
            end for;
            
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
        differential := eta - computeDifferential(u,dys,varList,n);
        
        terms := Terms(lift(differential));
        vec := [0 : i in [1..#O]];
        for term in terms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));

            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);


            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                dictTerm := monomialList[i]*term/(xTerm* x^xDegree);
                if IsDefined(ODict,dictTerm) then
                    index := ODict[dictTerm];

                    vec[index] := vec[index]+coeffList[i];
                end if;
                
            end for;
            
        end for;

        Append(~FON, vec);   
    end for; 
    print("Constructed F on hyperclasses");

    
    VON := [];

    //Computes Cartier Operator on H1 deRham
    for i in [1 .. #H1R] do
        u := HyperClasses[i][2];
        w := HyperClasses[i][3];
        if #Terms(u) le #Terms(w) then
            vu := computeCartier(gs, u, p, varList, cartierDict,R,B,A,P);
        else
            vu := computeCartier(gs, -1*w, p, varList, cartierDict,R,B,A,P);
        end if;

        terms := Terms(lift(vu));
        vec := [0 : i in [1..#O]];
        for term in terms do
            coeffList := Coefficients(term);
            xTerm := R!coeffList[#coeffList];

            xDegree := Degree(Denominator(xTerm));

            xPolyTerm := B!(xTerm*x^(xDegree));
            coeffList := Coefficients(xPolyTerm);


            monomialList := Monomials(xPolyTerm);
            for i in [1 .. #monomialList] do
                dictTerm := monomialList[i]*term/(xTerm* x^xDegree);
                if IsDefined(ODict,dictTerm) then
                    index := ODict[dictTerm];

                    vec[index] := vec[index]+coeffList[i];
                end if;
                
            end for;
            
        end for;

        Append(~VON, vec);
    end for;
    print("Constructed V on hyperclasses");
    
    FHN := Matrix(k, FHN);
    FON := Matrix(k, FON);
    VHN := Matrix(k, VHN);
    VON := Matrix(k, VON);

    //Constructs Frobenius and Cartier matrices of size 2g x 2g
    F := VerticalJoin(HorizontalJoin(FHN, FON), ZeroMatrix(k, #H1R, 2*#H1R));

    V := VerticalJoin(HorizontalJoin(ZeroMatrix(k,#H1R,#H1R),VON),HorizontalJoin(ZeroMatrix(k,#H1R,#H1R),VHN));

    M := RModule(MatrixRing<k,2*#H1R | F,V>);

    B := [*O, HyperClasses*];
    return M; 
end function;

