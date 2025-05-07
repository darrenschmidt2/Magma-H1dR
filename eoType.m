//Given the canonical filtration, fills in the EO type and computes the final filtration
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

//Given H1dR module D, computes the canonical filtration and then the EO type
//Starting with H1dR, repeatedly apply V until you get to 0, then apply F^(-1) until you get a repeated result, go back to V
//and repeat. Constructs a filtration of the subspaces found by keeping track of basis elements. If dim H1dR = n, keep track
//of a basis [b_1, ..., b_n]. Then the subspace with dimension 1 <= m <= n found has basis given by b_1, ... , b_m
canonicalType := function(D)
    H1:=VectorSpace(D);
    basis := Basis(H1);
    dimList := [Dimension(D)];

  Vit:=function(V,dims, dimList, basis, kerV, Filt);
     newDims := [];

     for dim in dims do
         flag := true;
         thisDim := dim;
         while flag do

             subspace := [];


             solBasis := Basis(sub<H1|basis[1 .. thisDim]> meet Image(V));
             subspace := Solution(V, solBasis);
             newVec := sub<H1|subspace> + kerV;
             newDim := Dimension(newVec);

             if newDim in dimList or Filt[newDim] ne -1 then
                 flag := false;

             else
             subDim := 0;
             for i in [#dimList .. 1 by -1] do
                 if dimList[i] lt newDim then
                     subDim := dimList[i];
                     break;
                 end if;
             end for;

             newBasis := [];
             i := 1;

                 newBasis := ExtendBasis(basis[1 .. subDim], newVec);
                 Append(~newDims, newDim);
                 Append(~dimList, newDim);
                 Sort(~dimList);

                 for otherDim in dimList do
                    if otherDim gt newDim then
                        newBasis := ExtendBasis(newBasis, sub<H1 | basis[1 .. otherDim]>);
                        for i in [1 .. #newBasis] do
                            basis[i] := newBasis[i];
                        end for;
                        break;
                    end if;
                end for;
             end if;
             thisDim := newDim;
         end while;
     end for;
     return newDims, dimList, basis;
  end function;

  Finit:=function(F,dims,dimList, basis, Filt);
    newDims := [];

    for dim in dims do
            thisDim := dim;
            flag := true;
        while flag do

            newBasis := [];
            subspace := basis[1 .. thisDim];
            BF := Rows(FrobeniusImage(Matrix(subspace),1)*F);

            subDim := Dimension(sub<H1|BF>);
            newSubDim := 0;
            for i in [#dimList .. 1 by -1] do
                if dimList[i] lt subDim then
                    newSubDim := dimList[i];
                    break;
                end if;
            end for;

            subspace := basis[1 .. newSubDim];

            newDim := subDim;


            newBasis := ExtendBasis(subspace, sub<H1|subspace cat BF>);
            Filt[thisDim] := newDim;
            if newDim eq 0 then
                flag := false;
            elif Filt[newDim] ne -1 then
                flag := false;

            else
                Append(~newDims, newDim);
                Append(~dimList, newDim);
                Sort(~dimList);
                for otherDim in dimList do
                    if otherDim gt newDim then
                        newBasis := ExtendBasis(newBasis, sub<H1 | basis[1 .. otherDim]>);
                        for i in [1 .. #newBasis] do
                            basis[i] := newBasis[i];
                        end for;
                        break;
                    end if;
                end for;
                thisDim := newDim;
            end if;
        end while;
    end for;
    return Filt, newDims, dimList, basis;
  end function;

  F:=Action(D).1;
  V:=Action(D).2;
  EO:=[-1: i in [1..Dimension(D)]];
  kerV := Kernel(V);
  EO1, newDims, dimList, basis := Finit(F, dimList, dimList, basis, EO);
  while EO1 ne EO do
    EO:=EO1;
    newDims, dimList, basis := Vit(V,newDims,dimList,basis, kerV, EO);
    EO1, newDims, dimList, basis :=Finit(F,newDims, dimList, basis, EO);
  end while;

  FinalFiltration(~EO);

  return EO;

end function;
