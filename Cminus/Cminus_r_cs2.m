//We compute the cluster picture and conductor of the curve Cminus at r when r nmid ab
//and the polynomial gminus is irreducible over Qr.
//We expect the conductor exponent at r to be r.


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

function Cminus_r_cs1(r, p, rge, counter);
    Qr := pAdicField(r, 200);
    RQr<X> := PolynomialRing(Qr);
    
    tested_pmts := [];
    ctr := 0;
    results := [];
    while ctr lt counter do
        a := Random(-rge, rge);
        c := Random(-rge, rge);
        if not ([a, c] in tested_pmts) then
            bp := c^r - a^p;
            if (Gcd(Gcd(a, bp), c) eq 1) and (a*bp*c ne 0) and (a*bp mod r ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                gm := grminus_a(a, c, r, p);
                Gm := Evaluate(gm, X);
                if IsIrreducible(Gm) then
                    tested_pmts := Append(tested_pmts, [a, c]);
                    ctr := ctr + 1;
                    print "Iteration nº", ctr, "\n";
                    print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c, "\n";
                    print "Polynomial gminus =", gm, " ";
                    print "The cluster picture of Cminus at", r, "is:";
                    print ClusterPicture(gm, r);
                    print "\nExpected outer depth:", 1/(r-1), "\n";
                    cond_exp := Conductor(HyperellipticCurve(gm), r);
                    print "The conductor of Cminus at", r, "is", cond_exp;
                    results := Append(results, cond_exp);
                    print "\n\n\n\n";
                end if; 
            end if;
        end if;
    end while;
    return results;
end function;



print "\n\n\n\n#############################################################################";
print "We compute the cluster pictures and conductor of the curve";
print "Cminus(r, p, a, c) at r when r does not divide a*b and gminus is irreducible.";
print "#############################################################################\n\n";


print "\n\n########################################";
print "Computing 10 iterations for r = 5, p = 7";
print "########################################\n\n";

res_5_7 := Cminus_r_cs1(5, 7, 5000, 10);

print "\n\n#########################################";
print "Computing 10 iterations for r = 5, p = 11";
print "#########################################\n\n";

res_5_11 := Cminus_r_cs1(5, 11, 5000, 10);




print "When r = 5, p = 7, we expect the conductor exponent at r to be 5. We find:\n";
print res_5_7;
print "\nWhen r = 5, p = 11, we expect the conductor exponent at r to be 5. We find:\n";
print res_5_11;

