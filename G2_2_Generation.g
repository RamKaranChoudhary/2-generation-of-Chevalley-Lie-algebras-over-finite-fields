LoadPackage("liealgdb");
TestG2Pair := function(q)
    local L, b, x, y, S, dimS;
    
    L := SimpleLieAlgebra("G", 2, GF(q));
    b := ChevalleyBasis(L);    
    x := b[1][1] + b[1][2] + b[3][1];
    y := b[2][1] + b[2][2] + b[3][2];
    S := Subalgebra(L, [x, y]);
    dimS := Dimension(S);
    Print("q = ", q, ", dimension = ", dimS, "\n");
    if dimS = 14 then
        Print("  -> SUCCESS: generates G2 over GF(", q, ")\n");
        return true;
    else
        Print("  -> FAIL: dimension is ", dimS, " (expected 14)\n");
        return false;
    fi;
end;

# Run the test for q = 5, 7, 11
for q in [5, 7, 11] do
    TestG2Pair(q);
    Print("\n");
od;
