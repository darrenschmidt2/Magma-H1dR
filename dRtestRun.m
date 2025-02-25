load "h1drComputation.m";

F<t> := PolynomialRing(GF(3));

M := computeH1dR(3,1,1,t^2);

F := Action(M).1;
V := Action(M).2;

f := Open("frobeniusMatrix.txt", "w");
v := Open("cartierMatrix.txt", "w");

rows := NumberOfRows(F);

for i in [1 .. rows] do
    for j in [1 .. rows] do
        Write(f, Sprint(F[i][j]));
        Write(v, Sprint(V[i][j]));
    end for;
end for;


