//We compute the cluster picture and conductor of the curve Crrp at r when r mid a^r+b^r
//We expect Crrp the conductor exponent at r to be r-1.


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

function Crrp_r_cs1(r, rge, counter);
    tested_pmts := [];
    ctr := 0;
    results := [];
    while ctr lt counter do
        a := Random(-rge, rge);
        b := Random(-rge, rge);
        if not ([a, b] in tested_pmts) then
            cp := a^r + b^r;
            if (Gcd(Gcd(a, b), cp) eq 1) and (a*b*cp ne 0) and (cp mod r eq 0) then //assuming that the solution to the dioph. eq. is nontrivial
                ctr := ctr + 1;
                print "Iteration nº", ctr, "\n";
                fr := frrp(a, b, r);
                print "r = ", r, ", a = ", a, ", b = ", b, ", c^p = ", cp, "\n";
                print "Polynomial frrp =", fr;
                print "The cluster picture of Crrp at", r, "is:";
                print ClusterPicture(fr, r);
                print "\nExpected outer depth:", 2/(r-1), "expected depth of the twins:", Valuation(a+b, r) + 1/(r-1),"\n"; //expected (absolute) depth
                cond_exp := Conductor(HyperellipticCurve(fr), r);
                print "The conductor of Crrp at", r, "is", cond_exp;
                results := Append(results, cond_exp);
                print "\n\n\n";
            end if;
        end if;
    end while;
    return results;
end function;
        




print "\n\n\n\n##########################################################";
print "We compute the cluster pictures and conductor of the curve";
print "Crrp(r, a, b) at r when r divides a^r+b^r.";
print "##########################################################\n\n";


print "\n\n########################################";
print "Computing 10 iterations for r = 5";
print "########################################\n\n";

res_5 := Crrp_r_cs1(5, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 7";
print "########################################\n\n";

res_7 := Crrp_r_cs1(7, 5000, 10);

print "\n\n########################################";
print "Computing 10 iterations for r = 11";
print "########################################\n\n";

res_11 := Crrp_r_cs1(11, 5000, 10);

print "When r = 5, we expect the conductor exponent at r be 4. We find:\n";
print res_5;
print "\nWhen r = 7, we expect the conductor exponent at r to be 6. We find:\n";
print res_7;
print "\nWhen r = 11, we expect the conductor exponent at r to be 10. We find:\n";
print res_11;