//We compute the cluster picture and conductor of the curve Crrp at any 
//prime q dividing a^r+b^r, q ne 2, r. We expect Crrp to be semistable at such places.


Attach("clusters.m");

R<x> := PolynomialRing(Rationals()); 

function Minpolw(r); 
    //generates the defining polynomial of  K=Q(zeta_r + 1/zeta_r)
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function frrp(a, b, r); 
    //constructs the polynomial in Q[x] defining the curve Cminus associated to a & c
    h := Minpolw(r);
    return (a*b)^(Numerator((r-1)/2))*x*Evaluate(h, x^2/(a*b) + 2) + b^r - a^r;
end function;

function Crrp_q(r, rge, counter);
    tested_pmts := [];
    ctr := 0;
    results := [];
    while ctr lt counter do
        a := Random(-rge, rge);
        b := Random(-rge, rge);
        if not ([a, b] in tested_pmts) then
            cp := a^r + b^r;
            if (Gcd(Gcd(a, b), cp) eq 1) and (a*b*cp ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                tested_pmts := Append(tested_pmts, [a, b]);
                ctr := ctr + 1;
                print "Iteration nº", ctr, "\n";
                fr := frrp(a, b, r);
                print "r = ", r, ", a = ", a, ", b = ", b, ", c^p = ", cp, "\n";
                print "Polynomial frrp =", fr;
                BadPrimes:=Factorization(Integers()!Discriminant(fr)); 
                BadPrimes_cp := [fact[1] : fact in BadPrimes | ((cp mod fact[1]) eq 0) and (fact[1] ne 2) and (fact[1] ne r)];
                print "Bad primes dividing a^r+b^r, not 2,", r, "are:", BadPrimes_cp, "\n\n";
                for q in BadPrimes_cp do 
                    print "The cluster picture of Crrp at", q, "is:";
                    print ClusterPicture(fr, q);
                    print "\nExpected depth of the twins:", Valuation(cp, q), "\n"; //expected (absolute) depth
                    cond_exp := Conductor(HyperellipticCurve(fr), q);
                    print "The conductor of Crrp at", q, "is", cond_exp, "\n\n";
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
print "Crrp(r, a, b) at q when q divides a^r+b^r, q ne 2, r.";
print "##########################################################\n\n";


print "\n\n########################################";
print "Computing 10 iterations for r = 5";
print "########################################\n\n";

res_5 := Crrp_q(5, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 7";
print "########################################\n\n";

res_7 := Crrp_q(7, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 11";
print "########################################\n\n";

res_11 := Crrp_q(11, 5000, 10);


print "When r = 5, we expect the conductor exponent at primes dividing a^r+b^r to be 2. We find the following (1st entry is the place q, second entry is the conductor exponent at q):\n";
print res_5;
print "\nWhen r = 7, we expect the conductor exponent at primes dividing a^r+b^r to be 3. We find the following (1st entry is the place q, second entry is the conductor exponent at q):\n";
print res_7;
print "\nWhen r = 11, we expect the conductor exponent at primes dividing a^r+b^r to be 5. We find the following (1st entry is the place q, second entry is the conductor exponent at q):\n";
print res_11;
