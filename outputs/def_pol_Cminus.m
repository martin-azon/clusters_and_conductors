//In this file we construct the defining polynomials for the Cminus curve for different values of r and p.

primes := [r : r in [5..100] | IsPrime(r)]; //Initializing the lists
defining_pols := [* *];

p := 7; //set any desired value of p

FFQ<a, c> := FunctionField(Rationals(), 2); // a, c will be treated as elements of a function field 
//Notice that we don't need b anymore
Pols_FF<x> := PolynomialRing(FFQ);

function GenerateMinpolw(r); //generates the minimal polynomial of w, the generator of K = Q(zeta)^+
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function KrausC_ppr(r); //returns the defining polynomial of the curve Cminus(a, b, c)
    h := GenerateMinpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2); 
    //notice that we evaluate h in -x^2 + 2 and not in x^2 - 2. This is because C-K consider the minimal
    //polynomial of -w, so we need to evaluate h at the opposite of what they do. We need to add then the
    //factor (-1)^((r-1)/2) to keep the same sign. 
    g := (c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r);
    return g;
end function;

print " ";
print "We fix p = ", p; 
print " ";
print "The defining polynomials for different values of r are:";
print " ";

for r in primes do
    def_pol := KrausC_ppr(r);
    defining_pols := Append(defining_pols, def_pol);
    print "When r = ", r, " the defining polynomial is:";
    print def_pol, " " ;
end for;

print defining_pols;
