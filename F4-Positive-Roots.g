CartanF4 := [
    [ 2, -1,  0,  0],
    [-1,  2, -2,  0],
    [ 0, -1,  2, -1],
    [ 0,  0, -1,  2]
];
RootsF4 := IdentityMat(4);
posF4 := 1;

while posF4 <= Length(RootsF4) do
    betaF4 := RootsF4[posF4];
    for iF4 in [1..4] do
        valF4 := Sum([1..4],
            jF4 -> betaF4[jF4] * CartanF4[jF4][iF4]);
        newF4 := ShallowCopy(betaF4);
        newF4[iF4] := newF4[iF4] - valF4;

        if Position(RootsF4, newF4) = fail then
            Add(RootsF4, newF4);
        fi;
    od;
    posF4 := posF4 + 1;
od;

PosRootsF4 := Filtered(RootsF4,
    betaF4 -> ForAll(betaF4, cF4 -> cF4 >= 0));

# Root coefficients to linear-form coefficients: d = c A
RootFormF4 := function(betaF4)
    return List([1..4], iF4 ->
        Sum([1..4],
            jF4 -> betaF4[jF4] * CartanF4[jF4][iF4]));
end;

LinearFormsF4 := List(PosRootsF4, RootFormF4);
Print("Total roots: ", Length(RootsF4), "\n");
Print("Positive roots: ", Length(PosRootsF4), "\n");

if Length(RootsF4) <> 48 or Length(PosRootsF4) <> 24 then
    Error("Expected 48 roots and 24 positive roots. Check CartanF4.");
fi;
Print("\n--- Positive roots and corresponding linear forms ---\n");

for iF4 in [1..Length(PosRootsF4)] do
    Print("Root coefficients: ", PosRootsF4[iF4],
          "   Linear form coefficients: ",
          LinearFormsF4[iF4], "\n");
od;

all_factors := [];
# 1. Linear forms themselves
for r in LinearFormsF4 do
    Add(all_factors, r);
od;
# 2. Differences r_i - r_j, i < j
for i in [1..Length(LinearFormsF4)] do
    for j in [i+1..Length(LinearFormsF4)] do
        Add(all_factors, LinearFormsF4[i] - LinearFormsF4[j]);
    od;
od;
# 3. Sums r_i + r_j, ordered pairs i <> j
for i in [1..Length(LinearFormsF4)] do
    for j in [1..Length(LinearFormsF4)] do
        if i <> j then
            Add(all_factors, LinearFormsF4[i] + LinearFormsF4[j]);
        fi;
    od;
od;
Print("\nTotal factors (with repetitions): ",
      Length(all_factors), "\n");

# Normalize a 4-vector over Q
NormalizeForm := function(v)
    local w, g, denoms, commonDenom, i;

    w := ShallowCopy(v);
    denoms := List(w, x -> DenominatorRat(x));
    commonDenom := Lcm(denoms);
    w := List(w, x -> NumeratorRat(x * commonDenom));
    g := Gcd(List(w, x -> AbsInt(x)));

    if g = 0 then
        return [0,0,0,0];
    fi;
    w := List(w, x -> QuoInt(x, g));
    for i in [1..Length(w)] do
        if w[i] <> 0 then
            if w[i] < 0 then
                w := List(w, x -> -x);
            fi;
            break;
        fi;
    od;
    return w;
end;

# Deduplicate primitive forms and retain their occurrences
distinct_forms := [];
scalars_per_form := [];
for f in all_factors do
    nf := NormalizeForm(f);
    pos := Position(distinct_forms, nf);

    if pos = fail then
        Add(distinct_forms, nf);
        Add(scalars_per_form, [f]);
    else
        Add(scalars_per_form[pos], f);
    fi;
od;
Print("\nNumber of distinct primitive forms: ",
      Length(distinct_forms), "\n");
Print("Sum of multiplicities: ",
      Sum(List(scalars_per_form, Length)), "\n");

# Product of all scalars relating occurrences to normalized forms
prodScalars := 1;
for i in [1..Length(distinct_forms)] do
    nf := distinct_forms[i];
    for f in scalars_per_form[i] do
        for k in [1..4] do
            if nf[k] <> 0 then
                prodScalars := prodScalars * (f[k] / nf[k]);
                break;
            fi;
        od;
    od;
od;
Print("\nProduct of all scalars = ", prodScalars, "\n");

PrimeList := function(n)
    n := AbsInt(n);
    if n <= 1 then
        return [];
    fi;
    return Set(FactorsInt(n));
end;

PrintFactorization := function(label, n)
    local fs;
    n := AbsInt(n);
    Print(label, " = ", n, "\n");
    if n = 1 then
        Print("  (trivial: no prime factors)\n");
        return;
    fi;
    fs := FactorsInt(n);
    Print("  Factorization (with multiplicity): ", fs, "\n");
    Print("  Distinct primes: ", Set(fs), "\n");
end;

# Factorization and prime divisors of prodScalars
Print("\n--- Factorization of prodScalars ---\n");
S := AbsInt(prodScalars);
Print("prodScalars = ", prodScalars, "\n");
Print("Using S = |prodScalars| = ", S, "\n");
PrintFactorization("|prodScalars|", S);
primeDivisorsS := PrimeList(S);
Print("Prime divisors of S: ", primeDivisorsS, "\n");

# Count distinct forms by first nonzero coordinate over Q
Print("\n--- Counting distinct forms by zero patterns (over Q) ---\n");
counts := [0,0,0,0];
for f in distinct_forms do
    for i in [1..4] do
        if f[i] <> 0 then
            counts[i] := counts[i] + 1;
            break;
        fi;
    od;
od;
Print("Total distinct forms: ", Length(distinct_forms), "\n");
for i in [1..4] do
    Print("Forms whose first nonzero coefficient is x",
          i, ": ", counts[i], "\n");
od;
n_zero := Number(distinct_forms,
    f -> ForAll(f, x -> x = 0));
Print("Zero forms: ", n_zero, "\n");

# Product of first nonzero coefficients over Q
ProductFirstNonZero := function(forms)
    local prod, f, i, found;
    prod := 1;
    for f in forms do
        found := false;
        for i in [1..Length(f)] do
            if f[i] <> 0 then
                prod := prod * f[i];
                found := true;
                break;
            fi;
        od;
        if not found then
            Print("Warning: zero form encountered!\n");
        fi;
    od;
    return prod;
end;
P_first_nonzero := ProductFirstNonZero(distinct_forms);
Print("\nProduct of first non-zero coefficients = ",
      P_first_nonzero, "\n");
Print("Factorization of |P_first_nonzero| = ",
      FactorsInt(AbsInt(P_first_nonzero)), "\n");
Print("Distinct primes of |P_first_nonzero| = ",
      PrimeList(P_first_nonzero), "\n");

# Per-prime GF(p) calculations for
# p in PrimeList(P_first_nonzero) \ PrimeList(S)
Print("Per-prime GF(p) calculation (with projective deduplication)\n");

scalar_primes := PrimeList(S);
P_primes := PrimeList(P_first_nonzero);
target_primes := Difference(P_primes, scalar_primes);

Print("Primes dividing S: ", scalar_primes, "\n");
Print("Primes dividing P_first_nonzero: ", P_primes, "\n");
Print("Target primes: ", target_primes, "\n");

ProductFirstNonZeroModP := function(forms, p)
    local F, prod, f, i, found;
    F := GF(p);
    prod := One(F);
    for f in forms do
        found := false;
        for i in [1..Length(f)] do
            if f[i] <> Zero(F) then
                prod := prod * f[i];
                found := true;
                break;
            fi;
        od;
        if not found then
            Print("Warning: zero form encountered mod ", p, "\n");
        fi;
    od;
    return prod;
end;

# Projective normalization in GF(p)
NormalizeModP := function(v, F)
    local i, inv;
    for i in [1..Length(v)] do
        if v[i] <> Zero(F) then
            inv := Inverse(v[i]);
            return List(v, x -> x * inv);
        fi;
    od;
    return ShallowCopy(v);
end;

# Per-prime calculations
for p in target_primes do
    Print("Characteristic p = ", p, "\n");
    Print("-------------------------------------------------\n");

    F := GF(p);

    # 1. Reduce distinct integer forms modulo p
    reduced := List(distinct_forms,
        f -> List(f, x -> Int(x) * One(F)));

    # 2. Projective normalization
    normalized := List(reduced, v -> NormalizeModP(v, F));

    # 3. Group by projective class and record scalar lambda.
    # reduced[i] = lambda * representative; zero has lambda = 0.

    classes := [];
    lambdas := [];
    for i in [1..Length(reduced)] do
        v := reduced[i];
        if ForAll(v, x -> x = Zero(F)) then
            pos := Position(classes, v);
            if pos = fail then
                Add(classes, v);
                pos := Length(classes);
            fi;
            Add(lambdas, Zero(F));
         else
            nv := normalized[i];
            pos := Position(classes, nv);
            if pos = fail then
                Add(classes, nv);
                pos := Length(classes);
            fi;
            for k in [1..4] do
                if v[k] <> Zero(F) then
                    Add(lambdas, v[k] / classes[pos][k]);
                    break;
                fi;
            od;
        fi;
    od;
    distinct_forms_modp := ShallowCopy(classes);

    Print("\n--- Projective deduplication mod ", p, " ---\n");
    Print("Forms before deduplication: ", Length(reduced), "\n");
    Print("Distinct projective classes mod ", p, ": ",
          Length(distinct_forms_modp), "\n");

    n_new := Number(distinct_forms_modp,
        f -> not ForAll(f, x -> x = Zero(F)));
    if n_new = 0 then
        Print("Every form collapses to zero mod ", p, ".\n");
    fi;

    # 4. Product of collapse scalars modulo p
    prodScalarsModP := One(F);
    for lam in lambdas do
        prodScalarsModP := prodScalarsModP * lam;
    od;
    Print("\nProduct of collapse scalars mod ", p, " = ",
          Int(prodScalarsModP), "\n");
    if Int(prodScalarsModP) > 1 then
        Print("Factorization: ",
              FactorsInt(Int(prodScalarsModP)), "\n");
        Print("Distinct primes: ",
              PrimeList(Int(prodScalarsModP)), "\n");
    else
        Print("Product is 0 or 1; no nontrivial prime factorization.\n");
    fi;

    # 5. Zero-pattern counts on the deduplicated set
    Print("\n--- Zero-pattern counts mod ", p, " ---\n");
    counts_p := [0,0,0,0];
    for f in distinct_forms_modp do
        for i in [1..4] do
            if f[i] <> Zero(F) then
                counts_p[i] := counts_p[i] + 1;
                break;
            fi;
        od;
    od;
    Print("Total distinct forms mod ", p, ": ",
          Length(distinct_forms_modp), "\n");

    for i in [1..4] do
        Print("Forms whose first nonzero coefficient is x",
              i, " mod ", p, ": ", counts_p[i], "\n");
    od;

    n_zero := Number(distinct_forms_modp,
        f -> ForAll(f, x -> x = Zero(F)));
    Print("Forms reducing to the zero vector mod ", p, ": ",
          n_zero, "\n");

# 6. Product of first nonzero coefficients modulo p
Print("\n--- Product of first nonzero coefficients mod ", p, " ---\n");
P_p := ProductFirstNonZeroModP(distinct_forms_modp, p);
Print("Product modulo ", p, " = ", P_p, "\n");
od;
Print("Done. Processed target primes: ", target_primes, "\n");
