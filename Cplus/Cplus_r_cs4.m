//We compute the cluster picture and conductor of the curve Cplus at r when r mid a
//We expect the conductor exponent at r to be r-2.


Attach("clusters.m");

R<x> := PolynomialRing(Rationals()); 

function Minpolw(r); 
    //generates the defining polynomial of  K=Q(zeta_r + 1/zeta_r)
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function gplus_b(b, c, r, p); 
    //constructs the polynomial in Q[x] defining the curve Cplus associated to b & c
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    return (x + 2*c)*((c)^(r)*Evaluate(f, x/c) -2*(c^r-2*b^p));
end function;

function Cplus_r_cs3(r, p, rge, counter);
    tested_pmts := [];
    ctr := 0;
    results := [];
    while ctr lt counter do
        b := Random(-rge, rge);
        c := Random(-rge, rge);
        if not ([b, c] in tested_pmts) then
            ap := c^r - b^p;
            if (Gcd(Gcd(ap, b), c) eq 1) and (ap*b*c ne 0) and (b mod r eq 0) then //assuming that the solution to the dioph. eq. is nontrivial
                tested_pmts := Append(tested_pmts, [b, c]);
                gpl := gplus_b(b, c, r, p);
                ctr := ctr + 1;
                print "Iteration nº", ctr, "\n";
                print "r = ", r, ", p = ", p, ", a^p = ", ap, ", b = ", b, ", c = ", c, "\n";
                print "Polynomial gplus =", gpl, " ";
                print "The cluster picture of Cplus at", r, "is:";
                print ClusterPicture(gpl, r);
                depth_m := p*Valuation(b, r)/2 - r/(r-1);
                print "\nExpected depths of the twins:", depth_m + 2/(r-1), ", intermediate depth:", 2/(r-1), "\n";
                cond_exp := Conductor(HyperellipticCurve(gpl), r);
                print "The conductor of Cplus at", r, "is", cond_exp;
                results := Append(results, cond_exp);
                print "\n\n\n\n";
            end if;
        end if;
    end while;
    return results;
end function;



print "\n\n\n\n######################################################";
print "We compute the cluster pictures and conductor of the curve";
print "Cplus(r, p, a, c) at r when r divides b .";
print "##########################################################\n\n";


print "\n\n########################################";
print "Computing 10 iterations for r = 5, p = 7";
print "########################################\n\n";

res_5_7 := Cplus_r_cs3(5, 7, 5000, 10);

print "\n\n#########################################";
print "Computing 10 iterations for r = 5, p = 11";
print "#########################################\n\n";

res_5_11 := Cplus_r_cs3(5, 11, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 7, p = 5";
print "########################################\n\n";

res_7_5 := Cplus_r_cs3(7, 5, 5000, 10);

print "\n\n#########################################";
print "Computing 10 iterations for r = 7, p = 11";
print "#########################################\n\n";

res_7_11 := Cplus_r_cs3(7, 11, 5000, 10);


print "When r = 5, p = 7, we expect the conductor exponent at r to be 4. We find:\n";
print res_5_7;
print "\nWhen r = 5, p = 11, we expect the conductor exponent at r to be 4. We find:\n";
print res_5_11;
print "\nWhen r = 7, p = 5, we expect the conductor exponent at r to be 6. We find:\n";
print res_7_5;
print "\nWhen r = 7, p = 11, we expect the conductor exponent at r to be 6. We find:\n";
print res_7_11;