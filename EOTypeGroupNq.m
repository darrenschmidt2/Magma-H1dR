declare attributes FldFun:H1deRham;

pullBack:=function(f, s);
    s:=Image(f) meet s;
    sol, N := Solution(f, Basis(s));
    return sub<Generic(N)|[b : b in Basis(N + RowSpace(Matrix(sol)))]>;
end function;

sim:=function(f,s,e);
	B:=Basis(s);
	A:=Matrix(B);
	BS:=FrobeniusImage(A,e)*f;	
//	BS:=[];
//	for b in B do
//		BS:=BS cat [FrobeniusImage(b,e)*f];
//	end for;
	return sub<Generic(s) | Rows(BS)>;
end function;

ssub:=function(U,W,e)
	B:=Basis(U);
	A:=Matrix(B);
	BS:=Rows(FrobeniusImage(A,e));
	US:=sub<W|BS>;
	return US;
end function;
	
spullBack:=function(f, s,e);
    s:=sim(f,Generic(s),e) meet s;
    sol, N := Solution(f, Basis(s));
    Lsub:=sub<Generic(N)|[b : b in Basis(N + RowSpace(Matrix(sol)))]>;
    return ssub(Lsub,Generic(N),-e);
end function;

	

intrinsic IsValidEO(EO::SeqEnum) ->. 
   {Checks if the length 2g sequence is a valid symmetric BT1 EO-type}
   g:=Integers()!EO[#EO];
   is_dual:=&and [(EO[j] eq EO[j+1]) eq (EO[2*g-j] eq (EO[2*g-j-1]+1)) : j in [1..2*g-2]];
   is_increasing:= &and [EO[i+1] in {EO[i], EO[i]+1} : i in [1..#EO-1]];  
   return is_increasing and is_dual and (EO[#EO] eq (#EO div 2)) and (EO[1] in {0,1});
end intrinsic;


intrinsic IsLeq(EO1::SeqEnum, EO2::SeqEnum) ->. 
   {Checks if the EO-type EO1 is less than or equal to EO2 in the partial ordering on EO types}
   g1:=Integers()!EO1[#EO1];
   g2:=Integers()!EO2[#EO2];
   assert(g1 eq g2);
   g:=g1;
   compare:= &and [EO1[j] le EO2[j]  :j in [1..2*g]];
   return compare;
end intrinsic;



intrinsic ExtendEO(EO::SeqEnum) -> .
	{Given a length g EO type return the length 2g type}
	
    g:=#EO;
    longEO:=EO cat [0 : i in [1..g]];
    for i in [1..g-1] do 
    	longEO[2*g-i] := EO[i]+g-i;	
    end for;
    longEO[2*g] :=g;
    assert IsValidEO(longEO);
    return longEO;
end intrinsic;

FinalFiltration:=procedure(~EO);
  last:=0;
  thisrun:=[];
  inputEO:=EO;
  for i in [1..#EO] do
    if EO[i] eq -1 then
       Append(~thisrun,i);
    else
       for j in [1..#thisrun] do
         if EO[i] eq last then
           EO[i-j]:=last;
         else
           EO[i-j]:=EO[i] - j;
        end if;
       end for;
       last:=EO[i];
       thisrun:=[];
    end if;
  end for;

end procedure;


intrinsic GpMatrix(K::FldFun, s::Map) -> .
 {Return the F,V module M viewed over k[S-1]}
	p:=Characteristic(K);
	M,Fr,Ver,S:=H1dR(K,s);
	J,A,I:=JordanForm(S);
	F:=A*Fr*A^(-1);
	V:=A*Ver*A^(-1);
	
	k1<S>:=PolynomialRing(GF(p),1);
	k<s>:=quo<k1 | S^p>;
	
	Id:=IdentityMatrix(GF(p),#Rows(J));
	
	W:=VectorSpaceWithBasis(Rows(J));
	//W:=VectorSpaceWithBasis(Rows(Id));

	Fmat:=[];
			counterA:=1;
			for i in [1..#I] do
				multA:=I[i][2];
				co:=Coordinates(W,J[counterA]*F);		
				newrow:=[];
				counterB:=1;
				for i in [1..#I] do
					multB:=I[i][2];
					entry:=0;  for a in [counterB.. counterB + multB - 1] do entry:=entry+co[a]*s^(a-counterB); end for; newrow:=newrow cat [entry]; 
					counterB:=counterB+multB;
				end for;		
				Fmat:=Fmat cat [newrow];
				counterA:=counterA+multA;
			end for;

	Vmat:=[];
			counterA:=1;
			for i in [1..#I] do
				multA:=I[i][2];
				co:=Coordinates(W,J[counterA]*V);		
				newrow:=[];
				counterB:=1;
				for i in [1..#I] do
					multB:=I[i][2];
					entry:=0;  for a in [counterB.. counterB + multB - 1] do entry:=entry+co[a]*s^(a-counterB); end for; newrow:=newrow cat [entry]; 
					counterB:=counterB+multB;
				end for;		
				Vmat:=Vmat cat [newrow];
				counterA:=counterA+multA;
			end for;
	


	return Matrix(Fmat),Matrix(Vmat),I;
end intrinsic;

intrinsic FssDM(M::ModRng, S::AlgMatElt[FldFin]) -> AlgMat
 {Return the F,V submodule of M given by the F-semisimple part of M}
	
	k:=CoefficientRing(M);
	F:=Action(M).1;
	d:=Dimension(M);
	Mnew:=RModule(MatrixAlgebra<k,d| F,S>);
	FM:=sub<Mnew | Image(F^d)>;
	return FM;

end intrinsic;


intrinsic GpFMatrix(K::FldFun, s::Map) -> .
 {Return the F-module Mss viewed over k[S-1]}
	p:=Characteristic(K);
	M,F,V,S:=H1dR(K,s);
	MSS:=FssDM(M,S);
	Fss:=Action(MSS).1;
	Sss:=Action(MSS).2;
	
	J,A,I:=JordanForm(Sss);
	F:=A*Fss*A^(-1);
	
	
	k1<S>:=PolynomialRing(GF(p),1);
	k<s>:=quo<k1 | S^p>;
	
	
	
	W:=VectorSpaceWithBasis(Rows(J));
	

	Fmat:=[];
			counterA:=1;
			for i in [1..#I] do
				multA:=I[i][2];
				co:=Coordinates(W,J[counterA]*F);		
				newrow:=[];
				counterB:=1;
				for i in [1..#I] do
					multB:=I[i][2];
					entry:=0;  for a in [counterB.. counterB + multB - 1] do entry:=entry+co[a]*s^(a-counterB); end for; newrow:=newrow cat [entry]; 
					counterB:=counterB+multB;
				end for;		
				Fmat:=Fmat cat [newrow];
				counterA:=counterA+multA;
			end for;

	
	return Matrix(Fmat),I;
end intrinsic;





intrinsic subDM(M::ModRng, S::AlgMatElt[FldFin]) -> AlgMat
 {Return the F,V submodule of M given by kernel S}

SM:=sub<M | Kernel(S)>;
return SM;

end intrinsic;

intrinsic isBT(M::ModRng) -> BoolElt 
 {check if M is a BT-module}

F:=Action(M).1;
V:=Action(M).2;

BFV:= Image(F) eq Kernel(V);
BVF:= Image(V) eq Kernel(F);
tt:=Dimension(M) - Dimension(Kernel(V))-Dimension(Kernel(F));

print "Number of T-type factors is",-tt;
return (BFV and BVF);

end intrinsic;






intrinsic H1dR(K::FldFun, s::Map) -> AlgMat
  {Return the F,V module of dimension 2g}
  
//  if assigned K`H1deRham then
//    return K`H1deRham;
//  end if;
  
  p:=Characteristic(K);
  Fq:=ConstantField(K);
  Fp:=GF(p);
  g:=Genus(K);
  n:=Degree(Fq,Fp);

  t:=K!PolynomialRing(Fq).1;
  dt:=Differential(t);
  gdt:=Differential(s(t));

  P:=[ZeroDivisor(d), PoleDivisor(d)]   where d :=  Divisor(t);
  N:=Ceiling(2*g/Degree(P[1]));

  NP1:= N*(P[1]);
  NP2:= N*(P[2]);
  pNP1:= p*NP1;
  pNP2:= p*NP2;
  
  //
  // ------  Build the Riemann Roch Spaces for H^1(O) and H^0(Omega_1)
  //
  
  O, Om:=DifferentialSpace(DivisorGroup(K)!0);
  O12, O12m:=DifferentialSpace(-(NP1+NP2) -P[1]-P[2]);
  O1, O1m:=DifferentialSpace(-NP1-P[1]);
  O2, O2m:=DifferentialSpace(-NP2-P[2]); 
  

  R12, R12m:=RiemannRochSpace(NP1+NP2);
  R1, R1m:=RiemannRochSpace(NP1);
  R2, R2m:=RiemannRochSpace(NP2);

  H, Hm:=R12/(R1+R2);

  if Dimension(H) ne g or g eq 0 then
  	print "WARNING: Constant field not exact!";
  	return RModule(MatrixRing(Fq,0));
  end if;
  
  
  //
  // ------ Build Riemann Roch Spaces with larger poles and the reduction map back
  //

  P12, P12m:=RiemannRochSpace(pNP1+pNP2);
  P1, P1m:=RiemannRochSpace(pNP1);
  P2, P2m:=RiemannRochSpace(pNP2);

  Hp,Hpm:=P12/(P1+P2);
  Basisdifs:=[Om(b) : b in Basis(O)];
  Basisfns:=[R12m(Inverse(Hm)(b)) : b in Basis(H)];
  RtoP:=Matrix([Hpm(Inverse(P12m)(b)) : b in Basisfns]);
  _, PtoR:=IsInvertible(RtoP);
  //
  // ------ Build Frobenius on H^1(O) -> H^1(O)
  //

FHN:=[];
for f in Basisfns do
	Frobf:=Hpm(Inverse(P12m)(f^p))*PtoR;
	Append(~FHN,Frobf);
end for;

  //
  // ------ Build s-action on H^1(O) -> H^1(O)
  //

SHN:=[];
for f in Basisfns do
	gf:=Hm(Inverse(R12m)(s(f)));
	Append(~SHN,gf);
end for;

 //
  // ------ Build s-action on H^0(Omega) -> H^0(Omega)
  //

SVN:=[];
for w in Basisdifs do
	gw:=Inverse(Om)(s(w/dt)*gdt);
	Append(~SVN, gw);
end for;


  //
  // ------ Build V on H^0(Omega) -> H^0(Omega)
  //

VHN:=[];
for w in Basisdifs do
	Vw:=Inverse(Om)(Cartier(w));
	Append(~VHN,Vw);
end for;


  //
  // ------ Apply section to Basisfns to promote them to a linearly independent set of elements in H^1_dR
  // ------ To do so, we must decompose df = u + v with u in O1 and v in O2.  Such decomposition is accomplished by reducing df mod O2, 
  // ------ writing the result as a linear combination of the reduction mod O2 of a basis for O1, and then lifting back by taking the same linear combination of the basis of O1. 
  //

DQ,DQm:=O12/O2;
O1fns:=[O1m(b) : b in Basis(O1)];
O1mat:=Matrix([DQm(b) : b in Basis(O1)]);

HyperClasses:=[];
for f in Basisfns do
	df:=Differential(f);
	uvec:=DQm(df);
	solu:=Solution(O1mat,uvec);
	u:=&+[solu[i]*O1fns[i] : i in [1..#O1fns]];
	v:=df - u;
	Append(~HyperClasses,<f,u,v>);
end for;


  //
  // ------ Compute Frobenius on HyperClasses: F(f_i , u_i, v_i) = (f_i^p , 0 , 0).  We know that F(f_i, u_i, v_i) - Sum_j FHN[i,j]*(f_j , u_j, v_j) projects to 0 in H^1(O), so must be in the image of H^0(Omega); express that differential in terms of a basis.
  //


QP,QPm:=P12 / P2;
P1fns:=[P1m(b) : b in Basis(P1)];
P1mat:=Matrix([QPm(b) : b in Basis(P1)]);

FON:=[];
for i in [1..g] do
	f:=HyperClasses[i][1];
	Frobf:=f^p - &+[FHN[i,j]*HyperClasses[j][1] : j in [1..g]];
	uvec:=Solution(P1mat, QPm(Frobf));
	u:=&+[uvec[i]*P1fns[i] : i in [1..#P1fns]];
	v:=Frobf - u;
	eta:= - &+[FHN[i,j]*HyperClasses[j][2] : j in [1..g]];
	tau:= - &+[FHN[i,j]*HyperClasses[j][3] : j in [1..g]];
	Append(~FON,Inverse(Om)(eta - Differential(u)));
end for;


  //
  // ------ Compute Cartier on HyperClasses: V(f_i , u_i, v_i) = ( 0 , V(u_i) , V(v_i)).  
  //

VON:=[];
for i in [1..g] do
	u:=HyperClasses[i][2];
	v:=HyperClasses[i][3];
	Vu:=Cartier(u);
	Vv:=Cartier(v);
	Append(~VON,Inverse(Om)(Vu));
end for;


 //
  // ------ Compute s-action on HyperClasses: s(f_i , u_i, v_i) = (sf_i , s*u_i , s*v_i).  We know that s(f_i, u_i, v_i) - Sum_j SHN[i,j]*(f_j , u_j, v_j) projects to 0 in H^1(O), so must be in the image of H^0(Omega); express that differential in terms of a basis.
  //


Q,Qm:=R12 / R2;
R1fns:=[R1m(b) : b in Basis(R1)];
R1mat:=Matrix([Qm(b) : b in Basis(R1)]);

SON:=[];
for i in [1..g] do
	f:=HyperClasses[i][1];
	u:=HyperClasses[i][2];
	v:=HyperClasses[i][3];
	gf:=s(f) - &+[SHN[i,j]*HyperClasses[j][1] : j in [1..g]];
	avec:=Solution(R1mat, Qm(gf));
	a:=&+[avec[i]*R1fns[i] : i in [1..#R1fns]];
	b:=gf - a;
	eta:= s(u/dt)*gdt - &+[SHN[i,j]*HyperClasses[j][2] : j in [1..g]];
	tau:= s(v/dt)*gdt - &+[SHN[i,j]*HyperClasses[j][3] : j in [1..g]];
	Append(~SON,Inverse(Om)(eta-Differential(a)));
end for;




  //
  // ------ Set F and V on H^1_dR
  //
  
  F:=VerticalJoin(HorizontalJoin(Matrix(FHN), Matrix(FON)), ZeroMatrix(Fq,g,2*g));

  	
  
  Z:=ZeroMatrix(Fq, g,g);
  V:=VerticalJoin(HorizontalJoin(Z, Matrix(VON)), HorizontalJoin(Z, Matrix(VHN)));
  
    //
  // ------ Build action of s on H^0(Omega) -> H^0(Omega)
  //


Z:=ZeroMatrix(Fq,g,g);
S:=VerticalJoin(HorizontalJoin(Matrix(SHN), Matrix(SON)), HorizontalJoin(Z,Matrix(SVN)));




  // Set the attribute and return the module. 
  
  B:=[*Basisdifs,HyperClasses*];
  
  M:=RModule(MatrixRing<Fq, 2*g |F,V>);
  K`H1deRham:=M;
  return   B, F, V;
end intrinsic;

intrinsic EOType(D::ModRng) -> .
	{Return the EO type of the FV module}
	
	H1:=VectorSpace(D);
    S:=[*H1*];

  Vit:=function(V,S, Filt);
     VS:=[* *];
     for s in S do
        flag:=true;
        thisS:=s;
        while flag do
           //Vs:=sub<H1|[b*V : b in Basis(thisS)]>;
           Vs:=sim(V,thisS,-1);
           Filt[Dimension(thisS)]:=Dimension(Vs);
           if Dimension(Vs) eq 0 then
              flag:=false;
           else
              if Filt[Dimension(Vs)] eq -1 then
                 Append(~VS, Vs);
                 thisS:=Vs;
              else
                 flag:=false;
              end if;
           end if;
        end while;
     end for;
     return Filt, VS;
  end function;

  Finit:=function(F,S, Filt);
     FS:=[* *];
     dims:={};
     for s in S do
        flag:=true;
        i:=1;
        Fi:=F;
        while flag do
           Fins:=spullBack(Fi, s,i);
           if Filt[Dimension(Fins)] eq -1 and not Dimension(Fins) in dims then
             Append(~FS, Fins);
             Include(~dims, Dimension(Fins));
             i:=i+1;
             Fi:=FrobeniusImage(Fi,1)*F;
           else
             flag:=false;
           end if;
        end while;
     end for;
     return FS;
  end function;

  F:=Action(D).1;
  V:=Action(D).2;
  EO:=[-1: i in [1..Dimension(D)]];
  EO1, VS:= Vit(V, S, EO);
  while EO1 ne EO do
    EO:=EO1;
    FS:=Finit(F,VS, EO);
    EO1,VS:=Vit(V,FS, EO);
  end while;

  FinalFiltration(~EO);
  
  return EO;
end intrinsic;
  

intrinsic EOType(Kn::FldFun) -> []
  {Return the lenght 2g sequence of the Ekedahl-Oort type of Kn}
  M:=H1dR(Kn);
  
  if Dimension(M) eq 0 then
  	return [];
  end if;
  
  EO:=EOType(M);  
  
  Fp:=GF(Characteristic(Kn));
  Fq:=ConstantField(Kn);
  n:=Degree(Fq,Fp);
  g:=Genus(Kn);

  eo_dim:=Integers()!(Dimension(M)/2);
 
  NewEO:=[];
  n:=Integers()!(eo_dim/g);
  for i in [1..Floor(#EO/n)] do
     Append(~NewEO,Integers()!(EO[i*n]/n));
  end for;
  EO:=NewEO;
  
  assert IsValidEO(EO);
  
  return EO;
end intrinsic;

//
// ------------------------- Conversion functions:
//


intrinsic EOToPermutation(EO::SeqEnum)-> .
  {Convert EO type to a permutation}
  
  pi:=[];
  if EO[1] eq 1 then
    pi[1]:=0;
  else
    pi[1]:=EO[#EO];
  end if;

  for i in [1..#EO-1] do;
    if EO[i] eq EO[i+1] then
      pi[i+1]:=EO[#EO]+i-EO[i];
    else
      pi[i+1]:=EO[i];
    end if;
  end for;

  S2g:=SymmetricGroup(#EO);
  cyc:=S2g![p+1: p in pi];
  return cyc;
end intrinsic;

intrinsic PermutationToEO(c::GrpPermElt) -> .
	{Permutation to EO}
    EOC:=[];
    c_elt:=Eltseq(c); 
    if c_elt[1] eq 1 then
    	EOC[1]:= 1;
    	count:=1;
    else 	
    	EOC[1]:=0;
    	count:=0;
    end if;
    
    for i in [2..#c_elt] do
      if c_elt[i] lt i then
        count:=count+1;
      end if;
      if (c_elt[i] eq i) and i le (#c_elt div 2) then 
      	count:=count+1;
      end if;
      EOC[i]:=count;
    end for;
 	return EOC;
end intrinsic;

intrinsic PermutationToEO(c::SeqEnum) -> .
	{Permutation to EO}
	return PermutationToEO(SymmetricGroup(#c)!c);
end intrinsic;


intrinsic DecomposeEO(EO::SeqEnum) -> .
  {Return the EO type of each irreducible submodule}

  cyc:=EOToPermutation(EO);
  C:=CycleDecomposition(cyc);
  g:=EO[#EO];
  
  EODec:=AssociativeArray();
  for c in C do
  	if #c eq 1 then 
  		if c[1] gt g then 
  			EOC:=[0];
  		else
  			EOC:=[1];
  		end if;
  	else 
  		table:=Sort(c);
  		newc:={@ Index(table,i) : i in c @};
    	EOC:=PermutationToEO(Sym(#newc)![newc]);
    end if;
    
    if not IsDefined(EODec, EOC) then
      EODec[EOC]:=1;
    else
      EODec[EOC]+:=1;
    end if;
  end for;

  return {*eo^^EODec[eo] : eo in Keys(EODec) *};
end intrinsic

NormalizeCycle:=function(fvword);
	seq:=Eltseq(fvword);
	P:=Parent(fvword);
	return P!Min({Rotate(seq,i) : i in [1..#seq]});
end function;


CycletoFV:=function(c : P:=FreeGroup(2));
    f:=P.1;
    v:=P.2;
    w:=P!1;
    c:=IndexedSetToSequence(c);
    for i in [2..#c] do
      if c[i] gt c[i-1] then
        w:=w*f;
      else
        w:=w*v;
      end if;
    end for;
    if c[#c] gt c[1] then
    	w:=w*v;
    end if;
 return NormalizeCycle(w);
end function;

intrinsic EOToFVRelations(EO::SeqEnum : P:=FreeGroup(2)) ->.
    {return the fv relations of the components}
    
    if Names(P) eq Names(FreeGroup(2)) then
    	AssignNames(~P, ["F","V"]);
    end if;
    decomp:={* *};
    
    for c in CycleDecomposition(EOToPermutation(EO)) do 
  		if #c eq 1 then 
  			if c[1] gt EO[#EO] then 
  				fv_rel:=P.1;
  			else
  				fv_rel:=P.2;
  			end if;
  		else 
  			fv_rel:=CycletoFV(c: P:=P);
    	end if;
    
   		Include(~decomp, [fv_rel]);
   	end for;
    return decomp;		
end intrinsic;

intrinsic FVRelationToEO(FVelt::GrpFPElt) ->.
    {FV Relations to an EO type}
    
	EO:=[];
	fvseq:= Reverse(Eltseq(NormalizeCycle(FVelt)));
	
	if #fvseq eq 1 then 
		if fvseq[1] eq 1 then
			return [1];
		else 
			return [0];
		end if;
	end if;
	
	
	Mat_Ring:=MatrixRing(GF(2), #fvseq);
	f:=Zero(Mat_Ring);
	v:=Zero(Mat_Ring);
		
	for i in [1..#fvseq-1] do 
		if fvseq[i] eq 2 then 
			v[i,i+1] +:=1;
		else 
			f[i+1,i]+:=1;
		end if;
	end for;
	f[1,#fvseq] +:=1;
	  
	M:=RModule(MatrixRing<GF(2), #fvseq | Transpose(f), Transpose(v)>);
	return EOType(M);
	 	
end intrinsic;


F_iter:=function(EOs, S, Filt);
	FS:=[* *];
	dims:={};
	genera := [e[#e] : e in EOs];
	for s in S do
		flag:=true;
		thiss:=s;
		while flag do 
			F_ins:=[thiss[i] eq 0 select genera[i] else (thiss[i] - EOs[i][thiss[i]]) + genera[i] : i in [1..#genera]];
			if Filt[&+F_ins] eq -1 and not &+F_ins in dims then
				Append(~FS, F_ins);	
				Include(~dims, &+F_ins);
				thiss:=F_ins;
			else
				flag:=false;
			end if;
		end while;
	end for;
	return FS;
end function;

V_iter:=function(EOs, S, Filt);
	VS:=[* *];
	for s in S do 
		flag:=true;
		thiss:=s;
		while flag do 
			Vs:=[thiss[i] eq 0 select 0 else EOs[i][thiss[i]] : i in [1..#s]];
			Filt[&+thiss] := &+Vs;
			if &+Vs eq 0 then 
				flag:=false;
			else 
				if Filt[&+Vs] eq -1 then
					Append(~VS, Vs);
					thiss:=Vs;
				else
					flag:=false;
				end if;
			end if;
		end while;
	end for;
	return Filt, VS;
end function;


intrinsic ComposeEO(EOset::SetMulti) -> .
	{Turns a multiset of EOs into a single EO}
	if Type(EOset) eq SetMulti then 
		EOs:=MultisetToSequence(EOset);
	else 
		EOs:=EOset;
	end if;
	
	//assert &and [IsEven(#e) or (#e eq 1) : e in EOs];
	
	genera := [#e/2 : e in EOs];
	g := Integers()!(&+genera);
	
  	EO:=[-1: i in [1..2*g-1]] cat [g];
  	
  	S:=[[#eo : eo in EOs]];
  	EO1, VS:= V_iter(EOs, S, EO);
  	while EO1 ne EO do
    	EO:=EO1;
    	FS:=F_iter(EOs,VS, EO);
    	EO1,VS:=V_iter(EOs,FS, EO);
  	end while;

	FinalFiltration(~EO);
 	assert IsValidEO(EO);
 	
 	return(EO);
end intrinsic;
 
 
intrinsic FVRelationsToEO(FVelts::SetMulti) ->.
    {From a collection of FV Relations to an EO type}   
    return ComposeEO({*FVRelationToEO(fv[1]) : fv in FVelts*});        	
end intrinsic;


intrinsic FVModule(EO::SeqEnum , p::RngIntElt) -> .
	{Return the canonical FV module (over GF(p)) for a given type}
	
	assert IsPrime(p);
	
	g:=EO[#EO];
	
	Mat_ring:=MatrixRing(GF(p),2*g);
	F:=Zero(Mat_ring);
	V:=Zero(Mat_ring);
	IP:=Zero(Mat_ring);
	
	jump_indices:=[];
	if EO[1] eq 1 then 
		Append(~jump_indices, 1);
	end if;
	for i in [2..2*g] do 
		if EO[i] gt EO[i-1] then
			Append(~jump_indices, i);
		end if;
	end for;
	
	assert #jump_indices eq g;
	
	non_indices:=[2*g+1-j : j in jump_indices];
	
	for i in [1..g] do 
		IP[jump_indices[i],non_indices[i]] :=1;
		IP[non_indices[i], jump_indices[i]] :=-1;
	end for;
	
	for i in [1..g] do 
		F[jump_indices[i], i] :=1;
	end for;
	 
	for i in [1..g] do 
		sign:=1;
		if 2*g+i-1 in jump_indices then
			sign:=-1;
		end if;
		V[2*g-i+1, non_indices[i]] := sign;
	end for;
	
	return RModule(MatrixRing<GF(p), 2*g | Transpose(F), Transpose(V)>),  IP;
end intrinsic;

	
intrinsic _Tester(g::.)
    {testing the compose and decompose functions}
	V:=VectorSpace(GF(2),g);

	eolist:=[];
	for v in V do 
		eo:=[0 : i in [1..g+1]];
		for i in [2..g+1] do 
			eo[i] := eo[i-1]+ Integers()!(v[i-1]);
		end for;
		eo:=eo[2..g+1];
		for i in [g+1..2*g-1] do 
			Append(~eo, eo[2*g-i]-g+i);
		end for;
		Append(~eo, g);
		eolist cat:=[eo];
		
	    //tests
	    
	    //print eo;
	    
	    //Symmetric EO tests
	    try 
			assert eo eq ComposeEO(DecomposeEO(eo));
			assert eo eq PermutationToEO(EOToPermutation(eo));
			assert eo eq EOType(FVModule(eo,3));
			assert eo eq FVRelationsToEO(EOToFVRelations(eo));
			assert DecomposeEO(eo) eq {* EOType(s) : s in DirectSumDecomposition(FVModule(eo,3)) *};
		catch e
			error Sprint(eo), e;
		end try;
	end for;
	assert #{e : e in eolist} eq 2^g;
	//Sort(~eolist);
	//print eolist;
end intrinsic;





intrinsic SH1dR(K::FldFun, s::Map,i::RngIntElt) -> AlgMat
  {Return the F,V module given as hypecohomology of kernel(s^i) on dR complex of K}
  
  p:=Characteristic(K);
  
  assert(i ge 0 and i le p);
  
  Fq:=ConstantField(K);
  Fp:=GF(p);
  g:=Genus(K);
  n:=Degree(Fq,Fp);

  t:=K!BaseField(K).1;
  dt:=Differential(t);
  gdt:=Differential(s(t));

  Ram:=Support(Divisor(dt));
  dlist:=[-ArtinSchreierReduction(K.1,v) : v in Ram];
  gBase:=Integers()!((g-1 -  (p-1)/2*&+[d+1 : d in dlist])/p + 1);
  
  Oquodim:=function(j)
  	degEj:=&+[Ceiling((p-j)*d/p) : d in dlist];
	if degEj eq 0 then
		return gBase;
	else
		return gBase + degEj - 1;
	end if;
  end function;
  
   Hquodim:=function(j)
  	degDj:=&+[Ceiling((j-1)*d/p) : d in dlist];
	if degDj eq 0 then
		return gBase;
	else
		return gBase + degDj - 1;
	end if;
  end function;
  
 
  if i eq 0 then
  	Hidim:=0;
	Oidim:=0;
  else
	Hidim:=&+[Hquodim(j) : j in [1..i]];
	Oidim:=&+[Oquodim(j) : j in [1..i]];
 end if;
  
  
  P:=[ZeroDivisor(d), PoleDivisor(d)]   where d :=  Divisor(t);
  N:=Ceiling(2*g/Degree(P[1]));

  NP1:= N*(P[1]);
  NP2:= N*(P[2]);
  pNP1:= p*NP1;
  pNP2:= p*NP2;
  
  //
  // ------  Build the Riemann Roch Spaces for H^1(O) and H^0(Omega_1)
  //
  
  O, Om:=DifferentialSpace(DivisorGroup(K)!0);
  O12, O12m:=DifferentialSpace(-(NP1+NP2) -P[1]-P[2]);
  O1, O1m:=DifferentialSpace(-NP1-P[1]);
  O2, O2m:=DifferentialSpace(-NP2-P[2]); 
  
  OBasisdiff:=[Om(b) : b in Basis(O)];
  O1Basisdiff:=[O1m(b) : b in Basis(O1)];
  O2Basisdiff:=[O2m(b) : b in Basis(O2)];
  O12Basisdiff:=[O12m(b) : b in Basis(O12)];

  Os:=Matrix([Inverse(Om)(s(b/dt)*gdt) : b in OBasisdiff]);
  O12s:=Matrix([Inverse(O12m)(s(b/dt)*gdt) : b in O12Basisdiff]);
    O1s:=Matrix([Inverse(O1m)(s(b/dt)*gdt) : b in O1Basisdiff]);
      O2s:=Matrix([Inverse(O2m)(s(b/dt)*gdt) : b in O2Basisdiff]);

  Oi,Oim:=sub<O|Kernel((Os-1)^i)>;
  O12i:=sub<O12|Kernel((O12s-1)^i)>;
  O1i:=sub<O1|Kernel((O1s-1)^i)>;
   O2i:=sub<O2|Kernel((O2s-1)^i)>; 

  OiBasisdiff:=[Om(b) : b in Basis(Oi)];

  dimOi:=Dimension(Oi);
  assert(dimOi eq Oidim); //Make sure the dimension is correct
  

  R12, R12m:=RiemannRochSpace(NP1+NP2);
  R1, R1m:=RiemannRochSpace(NP1);
  R2, R2m:=RiemannRochSpace(NP2);
  
  R1Basisfns:=[R1m(b) : b in Basis(R1)];
  R2Basisfns:=[R2m(b) : b in Basis(R2)];
  R12Basisfns:=[R12m(b) : b in Basis(R12)];
 
  R12s:=Matrix([Inverse(R12m)(s(b)) : b in R12Basisfns]);
    R1s:=Matrix([Inverse(R1m)(s(b)) : b in R1Basisfns]);
      R2s:=Matrix([Inverse(R2m)(s(b)) : b in R2Basisfns]);
 
  R12i:=sub<R12|Kernel((R12s-1)^i)>;
  R1i:=sub<R1|Kernel((R1s-1)^i)>;
   R2i:=sub<R2|Kernel((R2s-1)^i)>; 

  Hi, Him:=R12i/(R1i+R2i);
  dimHi:=Dimension(Hi);
  assert(dimHi eq Hidim);  //Make sure the dimension is correct
  
  
    P12, P12m:=RiemannRochSpace(pNP1+pNP2);
  P1, P1m:=RiemannRochSpace(pNP1);
  P2, P2m:=RiemannRochSpace(pNP2);

  P1Basisfns:=[P1m(b) : b in Basis(P1)];
  P2Basisfns:=[P2m(b) : b in Basis(P2)];
  P12Basisfns:=[P12m(b) : b in Basis(P12)];

  P12s:=Matrix([Inverse(P12m)(s(b)) : b in P12Basisfns]);
    P1s:=Matrix([Inverse(P1m)(s(b)) : b in P1Basisfns]);
      P2s:=Matrix([Inverse(P2m)(s(b)) : b in P2Basisfns]);

  P12i:=sub<P12|Kernel((P12s-1)^i)>;
  P1i:=sub<P1|Kernel((P1s-1)^i)>;
   P2i:=sub<P2|Kernel((P2s-1)^i)>;

  Hpi,Hpim:=P12i/(P1i+P2i);

  Basisfns:=[R12m(Inverse(Him)(b)) : b in Basis(Hi)];
  if Dimension(Hi) eq 0 then 
 	RtoP:=1;
	PtoR:=1;
 else
	 RtoP:=Matrix([Hpim(Inverse(P12m)(b)) : b in Basisfns]);
	  _, PtoR:=IsInvertible(RtoP);
 end if;

  //
  // ------ Build Frobenius on H^1(ker s^i O) -> H^1(ker s^i O)
  //

FHN:=[];
for f in Basisfns do
	Frobf:=Hpim(Inverse(P12m)(f^p))*PtoR;
	Append(~FHN,Frobf);
end for;

  //
  // ------ Build V on H^0(ker s^i Omega) -> H^0(ker s^i Omega)
  //

VHN:=[];
for w in OiBasisdiff do
	Vw:=Inverse(Oim)(Cartier(w));
	Append(~VHN,Vw);
end for;

//
//---If H^1(ker s^i  O) = 0, hypercohomology will be H^0(ker s^i Omega)
//

if dimHi eq 0 then
	d:=dimOi;
	if dimOi gt 0 then
		F:=ZeroMatrix(Fp,dimOi);
		V:=Matrix(VHN);
		M:=RModule(MatrixRing<Fp, dimOi |F,V>);
	else
		F:=0;
		V:=0;
		M:=RModule(MatrixRing<Fp, 0 |F,V>);
	end if;
	return M,F,V;
end if;

//
//---If H^0(ker s^i  Omega) = 0, hypercohomology will be H^1(ker s^i O)
//

if dimOi eq 0 then
	if dimHi gt 0 then
		V:=ZeroMatrix(Fp,dimHi);
		F:=Matrix(FHN);
		M:=RModule(MatrixRing<Fp, dimHi |F,V>);
	else
		V:=0;
		F:=0;
		M:=RModule(MatrixRing<Fp, 0 |F,V>);
	end if;
	return M,F,V;
end if;


 //
  // ------ Apply section to Basisfns to promote them to a linearly independent set of elements in H^1_dR
  // ------ To do so, we must decompose df = u + v with u in O1i and v in O2i.  Such decomposition is accomplished by reducing df mod O2i, 
  // ------ writing the result as a linear combination of the reduction mod O2i of a basis for O1i, and then lifting back by taking the same linear combination of the basis of O1i. 
  //

DQi,DQim:=O12i/O2i;
O1ifns:=[O1m(b) : b in Basis(O1i)];
O1imat:=Matrix([DQim(b) : b in Basis(O1i)]);


HyperClasses:=[];
for f in Basisfns do
	df:=Differential(f);
	uvec:=DQim(df);
	solu:=Solution(O1imat,uvec);
	u:=&+[solu[j]*O1ifns[j] : j in [1..#O1ifns]];
	v:=df - u;
	Append(~HyperClasses,<f,u,v>);
end for;


  //
  // ------ Compute Frobenius on HyperClasses: F(f_i , u_i, v_i) = (f_i^p , 0 , 0).  We know that F(f_i, u_i, v_i) - Sum_j FHN[i,j]*(f_j , u_j, v_j) projects to 0 in H^1(ker s^i O), so must be in the image of H^0(ker s^i Omega); express that differential in terms of a basis.
  //


QPi,QPim:=P12i / P2i;
P1ifns:=[P1m(b) : b in Basis(P1i)];
P1imat:=Matrix([QPim(b) : b in Basis(P1i)]);

FON:=[];
for j in [1..dimHi] do
	f:=HyperClasses[j][1];
	Frobf:=f^p - &+[FHN[j,k]*HyperClasses[k][1] : k in [1..dimHi]];
	uvec:=Solution(P1imat, QPim(Frobf));
	u:=&+[uvec[k]*P1ifns[k] : k in [1..#P1ifns]];
	v:=Frobf - u;
	eta:= - &+[FHN[j,k]*HyperClasses[k][2] : k in [1..dimHi]];
	tau:= - &+[FHN[j,k]*HyperClasses[k][3] : k in [1..dimHi]];
	Append(~FON,Inverse(Oim)(eta - Differential(u)));
end for;


  //
  // ------ Compute Cartier on HyperClasses: V(f_i , u_i, v_i) = ( 0 , V(u_i) , V(v_i)).  
  //

VON:=[];
for j in [1..dimHi] do
	u:=HyperClasses[j][2];
	v:=HyperClasses[j][3];
	Vu:=Cartier(u);
	Vv:=Cartier(v);
	Append(~VON,Inverse(Oim)(Vu));
end for;



 //
  // ------ Set F on H^1_dR
  //
  
  F:=VerticalJoin(HorizontalJoin(Matrix(FHN), Matrix(FON)), ZeroMatrix(Fp,dimOi,dimOi+dimHi));

  	
  
  Z1:=ZeroMatrix(Fp, dimHi,dimHi);
  Z2:=ZeroMatrix(Fp, dimOi,dimHi);
  V:=VerticalJoin(HorizontalJoin(Z1, Matrix(VON)), HorizontalJoin(Z2, Matrix(VHN)));
  


  // Set the attribute and return the module. 
  
  M:=RModule(MatrixRing<Fp, dimOi+dimHi |F,V>);
  K`H1deRham:=M;
  return   M,F,V;







end intrinsic;







intrinsic BH1dR(K::FldFun,s::Map,D::DivFunElt,E::DivFunElt) -> AlgMat
  {Return the F,V module given as hypecohomology of D,E-modified dR complex of K}
  
  p:=Characteristic(K);
  degE:=Degree(E);
  degD:=Degree(D);
  degmax:=Max([degE,degD]);
  
//  assert(i ge 0 and i le p);
  
  Fq:=ConstantField(K);
  Fp:=GF(p);
  g:=Genus(K);
  n:=Degree(Fq,Fp);

  t:=K!BaseField(K).1;
  dt:=Differential(t);
  gdt:=Differential(s(t));

//  Ram:=Support(Divisor(dt));
 // dlist:=[-ArtinSchreierReduction(K.1,v) : v in Ram];
  //gBase:=Integers()!((g-1 -  (p-1)/2*&+[d+1 : d in dlist])/p + 1);
  
 // Oquodim:=function(j)
  //	degEj:=&+[Ceiling((p-j)*d/p) : d in dlist];
//	if degEj eq 0 then
//		return gBase;
//	else
//		return gBase + degEj - 1;
//	end if;
 // end function;
  
  // Hquodim:=function(j)
  //	degDj:=&+[Ceiling((j-1)*d/p) : d in dlist];
//	if degDj eq 0 then
//		return gBase;
//	else
//		return gBase + degDj - 1;
//	end if;
 // end function;
  
 
  //if i eq 0 then
  //	Hidim:=0;
//	Oidim:=0;
 // else
//	Hidim:=&+[Hquodim(j) : j in [1..i]];
//	Oidim:=&+[Oquodim(j) : j in [1..i]];
 //end if;
  
  
  P:=[ZeroDivisor(d), PoleDivisor(d)]   where d :=  Divisor(t);
  N:=Ceiling((2*g+degmax)/Degree(P[1]));

  NP1:= N*(P[1]);
  NP2:= N*(P[2]);
  pNP1:= p*NP1;
  pNP2:= p*NP2;
  pE:=p*E;
  
  //
  // ------  Build the Riemann Roch Spaces for H^1(O) and H^0(Omega_1)
  //
  
  Oh, Ohm:=DifferentialSpace(DivisorGroup(K)!0);
  O, Om:=DifferentialSpace(-D);
  O12, O12m:=DifferentialSpace(-D-(NP1+NP2) -P[1]-P[2]);
  O1, O1m:=DifferentialSpace(-D-NP1-P[1]);
  O2, O2m:=DifferentialSpace(-D-NP2-P[2]); 

  OhBasisdiff:=[Ohm(b) : b in Basis(Oh)];  
  OBasisdiff:=[Om(b) : b in Basis(O)];
  O1Basisdiff:=[O1m(b) : b in Basis(O1)];
  O2Basisdiff:=[O2m(b) : b in Basis(O2)];
  O12Basisdiff:=[O12m(b) : b in Basis(O12)];

Holdiff:=[Inverse(Om)(w) : w in OhBasisdiff];

 // Os:=Matrix([Inverse(Om)(s(b/dt)*gdt) : b in OBasisdiff]);
 // O12s:=Matrix([Inverse(O12m)(s(b/dt)*gdt) : b in O12Basisdiff]);
  //  O1s:=Matrix([Inverse(O1m)(s(b/dt)*gdt) : b in O1Basisdiff]);
   //   O2s:=Matrix([Inverse(O2m)(s(b/dt)*gdt) : b in O2Basisdiff]);

  //Oi,Oim:=sub<O|Kernel((Os-1)^i)>;
  //O12i:=sub<O12|Kernel((O12s-1)^i)>;
  //O1i:=sub<O1|Kernel((O1s-1)^i)>;
   //O2i:=sub<O2|Kernel((O2s-1)^i)>; 

  //OiBasisdiff:=[Om(b) : b in Basis(Oi)];

dimO:=Dimension(O);
  //assert(dimOi eq Oidim); //Make sure the dimension is correct
  

  R12, R12m:=RiemannRochSpace(-E+NP1+NP2);
  R1, R1m:=RiemannRochSpace(-E+NP1);
  R2, R2m:=RiemannRochSpace(-E+NP2);
  
  R1Basisfns:=[R1m(b) : b in Basis(R1)];
  R2Basisfns:=[R2m(b) : b in Basis(R2)];
  R12Basisfns:=[R12m(b) : b in Basis(R12)];
 
//  R12s:=Matrix([Inverse(R12m)(s(b)) : b in R12Basisfns]);
 //   R1s:=Matrix([Inverse(R1m)(s(b)) : b in R1Basisfns]);
  //    R2s:=Matrix([Inverse(R2m)(s(b)) : b in R2Basisfns]);
 
 // R12i:=sub<R12|Kernel((R12s-1)^i)>;
  //R1i:=sub<R1|Kernel((R1s-1)^i)>;
   //R2i:=sub<R2|Kernel((R2s-1)^i)>; 

  H, Hm:=R12/(R1+R2);
  dimH:=Dimension(H);
  //assert(dimHi eq Hidim);  //Make sure the dimension is correct
  
  
    P12, P12m:=RiemannRochSpace(pNP1+pNP2-E);
  P1, P1m:=RiemannRochSpace(pNP1-E);
  P2, P2m:=RiemannRochSpace(pNP2-E);

  P1Basisfns:=[P1m(b) : b in Basis(P1)];
  P2Basisfns:=[P2m(b) : b in Basis(P2)];
  P12Basisfns:=[P12m(b) : b in Basis(P12)];

 // P12s:=Matrix([Inverse(P12m)(s(b)) : b in P12Basisfns]);
  //  P1s:=Matrix([Inverse(P1m)(s(b)) : b in P1Basisfns]);
   //   P2s:=Matrix([Inverse(P2m)(s(b)) : b in P2Basisfns]);

//  P12i:=sub<P12|Kernel((P12s-1)^i)>;
 // P1i:=sub<P1|Kernel((P1s-1)^i)>;
  // P2i:=sub<P2|Kernel((P2s-1)^i)>;

  Hp,Hpm:=P12/(P1+P2);

  Basisfns:=[R12m(Inverse(Hm)(b)) : b in Basis(H)];
  if Dimension(H) eq 0 then 
 	RtoP:=1;
	PtoR:=1;
 else
	 RtoP:=Matrix([Hpm(Inverse(P12m)(b)) : b in Basisfns]);
	  _, PtoR:=IsInvertible(RtoP);
 end if;

  //
  // ------ Build Frobenius on H^1(-E) -> H^1(-E)
  //

FHN:=[];
for f in Basisfns do
	Frobf:=Hpm(Inverse(P12m)(f^p))*PtoR;
	Append(~FHN,Frobf);
end for;

  //
  // ------ Build V on H^0(Omega(D)) -> H^0(Omega(D))
  //

VHN:=[];
for w in OBasisdiff do
	Vw:=Inverse(Om)(Cartier(w));
	Append(~VHN,Vw);
end for;

//
//---If H^1(ker s^i  O) = 0, hypercohomology will be H^0(ker s^i Omega)
//

//if dimHi eq 0 then
//	d:=dimOi;
//	if dimOi gt 0 then
//		F:=ZeroMatrix(Fp,dimOi);
//		V:=Matrix(VHN);
//		M:=RModule(MatrixRing<Fp, dimOi |F,V>);
//	else
//		F:=0;
//		V:=0;
//		M:=RModule(MatrixRing<Fp, 0 |F,V>);
//	end if;
//	return M,F,V;
//end if;

//
//---If H^0(ker s^i  Omega) = 0, hypercohomology will be H^1(ker s^i O)
//

//if dimOi eq 0 then
//	if dimHi gt 0 then
//		V:=ZeroMatrix(Fp,dimHi);
//		F:=Matrix(FHN);
//		M:=RModule(MatrixRing<Fp, dimHi |F,V>);
//	else
//		V:=0;
//		F:=0;
//		M:=RModule(MatrixRing<Fp, 0 |F,V>);
//	end if;
//	return M,F,V;
//end if;


 //
  // ------ Apply section to Basisfns to promote them to a linearly independent set of elements in H^1_dR
  // ------ To do so, we must decompose df = u + v with u in O1i and v in O2i.  Such decomposition is accomplished by reducing df mod O2i, 
  // ------ writing the result as a linear combination of the reduction mod O2i of a basis for O1i, and then lifting back by taking the same linear combination of the basis of O1i. 
  //

DQ,DQm:=O12/O2;
O1fns:=[O1m(b) : b in Basis(O1)];
O1mat:=Matrix([DQm(b) : b in Basis(O1)]);


HyperClasses:=[];
for f in Basisfns do
	df:=Differential(f);
	uvec:=DQm(df);
	solu:=Solution(O1mat,uvec);
	u:=&+[solu[j]*O1fns[j] : j in [1..#O1fns]];
	v:=df - u;
	Append(~HyperClasses,<f,u,v>);
end for;


  //
  // ------ Compute Frobenius on HyperClasses: F(f_i , u_i, v_i) = (f_i^p , 0 , 0).  We know that F(f_i, u_i, v_i) - Sum_j FHN[i,j]*(f_j , u_j, v_j) projects to 0 in H^1(-E), so must be in the image of H^0(Omega(D)); express that differential in terms of a basis.
  //


QP,QPm:=P12 / P2;
P1fns:=[P1m(b) : b in Basis(P1)];
P1mat:=Matrix([QPm(b) : b in Basis(P1)]);

FON:=[];
for j in [1..dimH] do
	f:=HyperClasses[j][1];
	Frobf:=f^p - &+[FHN[j,k]*HyperClasses[k][1] : k in [1..dimH]];
	uvec:=Solution(P1mat, QPm(Frobf));
	u:=&+[uvec[k]*P1fns[k] : k in [1..#P1fns]];
	v:=Frobf - u;
	eta:= - &+[FHN[j,k]*HyperClasses[k][2] : k in [1..dimH]];
	tau:= - &+[FHN[j,k]*HyperClasses[k][3] : k in [1..dimH]];
	Append(~FON,Inverse(Om)(eta - Differential(u)));
end for;


  //
  // ------ Compute Cartier on HyperClasses: V(f_i , u_i, v_i) = ( 0 , V(u_i) , V(v_i)).  
  //

VON:=[];
for j in [1..dimH] do
	u:=HyperClasses[j][2];
	v:=HyperClasses[j][3];
	Vu:=Cartier(u);
	Vv:=Cartier(v);
	Append(~VON,Inverse(Om)(Vu));
end for;



 //
  // ------ Set F on H^1_dR
  //
  
  F:=VerticalJoin(HorizontalJoin(Matrix(FHN), Matrix(FON)), ZeroMatrix(Fq,dimO,dimO+dimH));

  	
  
  Z1:=ZeroMatrix(Fq, dimH,dimH);
  Z2:=ZeroMatrix(Fq, dimO,dimH);
  V:=VerticalJoin(HorizontalJoin(Z1, Matrix(VON)), HorizontalJoin(Z2, Matrix(VHN)));
    VO:=Matrix(VHN);


  // Set the attribute and return the module. 
  
  M:=RModule(MatrixRing<Fq, dimO+dimH |F,V>);
  MO:=RModule(MatrixRing<Fq, dimO |VO>);
  BO:=Basis(MO);
  
  gens:=[];
  for h in Holdiff do
  	gens:=gens cat [&+[h[i]*BO[i] : i in [1..dimO]]];
  end for;
  
  
  
  K`H1deRham:=M;
 return   MO,sub<MO|gens>,M;







end intrinsic;



