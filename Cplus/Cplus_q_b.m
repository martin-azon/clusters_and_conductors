//We compute the cluster picture and conductor of the curve Cplus at any 
//prime q dividing b, q ne 2, r. We expect Cplus to be semistable at such places.

//Note that, given two integers b, c, then ap := c^r - b^p is an integer, but its p-th power is not.
//That's why, if the curve Cplus is constructed with b, c as input, we focus on prime numbers dividing b, 
//and we forget about those dividing ap. 



Attach("clusters.m");

R<x> := PolynomialRing(Rationals()); 

function Minpolw(r); 
    //generates the defining polynomial of  K=Q(zeta_r + 1/zeta_r)
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function gplus_b(b, c, r, p); 
    //constructs the polynomial in Q[x] defining the curve Cminus associated to b & c
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    return (x + 2*c)*((c)^(r)*Evaluate(f, x/c) -2*(c^r-2*b^p));
end function;

function Cplus_q(r, p, rge, counter);
    tested_pmts := [];
    ctr := 0;
    results := [];
    while ctr lt counter do
        b := Random(-rge, rge);
        c := Random(-rge, rge);
        if not ([b, c] in tested_pmts) then
            ap := c^r - b^p;
            if (Gcd(Gcd(ap, b), c) eq 1) and (ap*b*c ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                ctr := ctr + 1;
                print "Iteration nº", ctr, "\n";
                gpl := gplus_b(b, c, r, p);
                print "r = ", r, ", p = ", p, ", a^p = ", ap, ", b = ", b, ", c = ", c, "\n";
                print "Polynomial gplus =", gpl;
                BadPrimes:=Factorization(Integers()!Discriminant(gpl)); 
                BadPrimes_b := [fact[1] : fact in BadPrimes | ((b mod fact[1]) eq 0) and (fact[1] ne 2) and (fact[1] ne r)];
                print "Bad primes dividing b, not 2,", r, "are:", BadPrimes_b, "\n\n";
                for q in BadPrimes_b do 
                    print "The cluster picture of Cplus at", q, "is:";
                    print ClusterPicture(gpl, q);
                    print "\nExpected depth of the twins:", p*Valuation(b, q)/2, "\n"; //expected (absolute) depth, recall that a, bp are coprime and q divides a
                    cond_exp := Conductor(HyperellipticCurve(gpl), q);
                    print "The conductor of Cplus at", q, "is", cond_exp, "\n\n";
                    results := Append(results, [q, cond_exp]);
                end for;
                print "\n\n\n\n";
            end if;
        end if;
    end while;
    return results;
end function;
        




print "\n\n\n\n##########################################################";
print "We compute the cluster pictures and conductor of the curve";
print "Cplus(r, p, b, c) at q when q divides b, q ne 2, r.";
print "##########################################################\n\n";


print "\n\n########################################";
print "Computing 10 iterations for r = 5, p = 7";
print "########################################\n\n";

res_5_7 := Cplus_q(5, 7, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 5, p = 11";
print "########################################\n\n";

res_5_11 := Cplus_q(5, 11, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 7, p = 5";
print "########################################\n\n";

res_7_5 := Cplus_q(7, 5, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 7, p = 11";
print "########################################\n\n";

res_7_11 := Cplus_q(7, 11, 5000, 10);

print "When r = 5, p = 7, we expect the conductor exponent at primes dividing b to be 2. We find:\n";
print res_5_7;
print "\nWhen r = 5, p = 11, we expect the conductor exponent at primes dividing b to be 2. We find:\n";
print res_5_11;
print "\nWhen r = 7, p = 5, we expect the conductor exponent at primes dividing b to be 3. We find:\n";
print res_7_5;
print "\nWhen r = 7, p = 11, we expect the conductor exponent at primes dividing b to be 3. We find:\n";
print res_7_11;
