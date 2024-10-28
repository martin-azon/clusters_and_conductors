//We compute the cluster picture and conductor of the curve Cminus at any 
//prime q dividing a, q ne 2, r. We expect Cminus to be semistable at such places.

//Note that, given two integers a, c, then bp := c^r - a^p is an integer, but its p-th power is not.
//That's why, if the curve Cminus is constructed with a, c as input, we focus on prime numbers dividing a, 
//and we forget about those dividing bp. 



Attach("clusters.m");

R<x> := PolynomialRing(Rationals()); 

function Minpolw(r); 
    //generates the defining polynomial of  K=Q(zeta_r + 1/zeta_r)
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function grminus_a(a, c, r, p); 
    //constructs the polynomial in Q[x] defining the curve Cminus associated to a & c
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    return (c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r);
end function;

function Cminus_q(r, p, rge, counter);
    tested_pmts := [];
    ctr := 0;
    results := [];
    while ctr lt counter do
        a := Random(-rge, rge);
        c := Random(-rge, rge);
        if not ([a, c] in tested_pmts) then
            bp := c^r - a^p;
            if (Gcd(Gcd(a, bp), c) eq 1) and (a*bp*c ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                ctr := ctr + 1;
                print "Iteration nº", ctr, "\n";
                gm := grminus_a(a, c, r, p);
                print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c, "\n";
                print "Polynomial gminus =", gm;
                BadPrimes:=Factorization(Integers()!Discriminant(gm)); 
                BadPrimes_a := [fact[1] : fact in BadPrimes | ((a mod fact[1]) eq 0) and (fact[1] ne 2) and (fact[1] ne r)];
                print "Bad primes dividing a, not 2,", r, "are:", BadPrimes_a, "\n\n";
                for q in BadPrimes_a do 
                    print "The cluster picture of Cminus at", q, "is:";
                    print ClusterPicture(gm, q);
                    print "\nExpected depth of the twins:", p*Valuation(a, q)/2, "\n"; //expected (absolute) depth, recall that a, bp are coprime and q divides a
                    cond_exp := Conductor(HyperellipticCurve(gm), q);
                    print "The conductor of Cminus at", q, "is", cond_exp, "\n\n";
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
print "Cminus(r, p, a, c) at q when q divides a, q ne 2, r.";
print "##########################################################\n\n";


print "\n\n########################################";
print "Computing 10 iterations for r = 5, p = 7";
print "########################################\n\n";

res_5_7 := Cminus_q(5, 7, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 5, p = 11";
print "########################################\n\n";

res_5_11 := Cminus_q(5, 11, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 7, p = 5";
print "########################################\n\n";

res_7_5 := Cminus_q(7, 5, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 7, p = 11";
print "########################################\n\n";

res_7_11 := Cminus_q(7, 11, 5000, 10);

print "When r = 5, p = 7, we expect the conductor exponent at primes dividing a to be 2. We find:\n";
print res_5_7;
print "\nWhen r = 5, p = 11, we expect the conductor exponent at primes dividing a to be 2. We find:\n";
print res_5_11;
print "\nWhen r = 7, p = 5, we expect the conductor exponent at primes dividing a to be 3. We find:\n";
print res_7_5;
print "\nWhen r = 7, p = 11, we expect the conductor exponent at primes dividing a to be 3. We find:\n";
print res_7_11;
