Attach("EOTypeGroupNq.m");
load "h1drComputation.m";

computeU11 := function(p,r,d,n,f)
    
    uList := [];
    
    for m in [1 .. n] do
    
        M := computeH1dR(p,r,d,m,f);
        
        Eo := EOType(M);
        R := EOToFVRelations(Eo);
        
        lengthList := [];
        relations := [];
        for a in R do
            Append(~lengthList, #a[1]);
            Append(~relations, a);
        end for;
        
        l := LCM(lengthList);
        maximum,_ := Max(lengthList);
        relations := IndexedSet(relations);
        mult := Multiplicities(R);

        G := Parent(relations[1][1]);

        s11 := 0;
        counting := 0;
        for i in [1 .. #relations] do
            if Integers(2)!l eq 0 then
                if relations[i][1] eq G.1 * G.2 then
                    s11 := mult[i];
                end if;
            end if;

            for j in [0 .. Min(maximum,Floor((l-4)/2))] do
                word := G.2^2*(G.1*G.2)^j*G.1^2;
                wordLength := #word;
                if #relations[i][1] ge wordLength then
                    for k in [0 .. #relations[i][1]] do
                        if Subword(RotateWord(relations[i][1],k),#relations[i][1]-wordLength+1,wordLength) eq word then
                            counting := counting + 1;
                            break;
                        end if;
                    end for;
                end if;
            end for;

        end for;
        u11 := s11 + counting;
        Append(~uList, u11);
    end for;
    return uList;

end function;
