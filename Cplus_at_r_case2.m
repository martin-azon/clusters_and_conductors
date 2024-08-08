//We are going to compute the cluster picture and conductor of the curve C^- (a.k.a. Cminus) at r when r divides a.
//We expect Cminus the conductor to be r-1 in that case!

Attach("clusters.m");

R<x> := PolynomialRing(Rationals()); //we begin over the rationals

function Minpolw(r); //generates the minimal polynomial of w, the generator of K=Q(zeta_r)^+
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function frplus(a, c, r, p); //constructs the polynomial defining the curve Cminus
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := ((c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r))*(x+2*c);
    return g;
end function;


procedure Cplus_at_r_case2(r, p, rge_a, rge_c); 
    //prints the cluster picture and the conductor of Cminus at r when r divides a*bp
    for a in [-rge_a..rge_a] do
        for c in [-rge_c..rge_c] do
            bp := c^r - a^p;
            if (Gcd(a, c) eq 1) and (a*bp*c ne 0) and (a mod r eq 0) then //assuming that the solution to the dioph. eq. is nontrivial
                frp := frplus(a, c, r, p);
                print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c;
                //print "Factorisation of b^p = ", Factorization(bp);
                //print " ";
                print "Polynomial frplus = ", frp; 
                print " ";
                C := ClusterPicture(frp, r);
                print "The cluster picture of Cplus at r is :";
                print C;
                print " ";
                print "The conductor of Cplus at r is", Conductor(HyperellipticCurve(frp), r);
                depth_m := p*Valuation(a, r)/2 + Valuation(bp, r)/2 - (r-2)/(r-1); //expected depth according to the overleaf
                //note that Tim's package deals with absolute depths and not relative ones
                //so magma gives the same depths as the ones we have in the overleaf!
                print "Expected depths = ", depth_m, ",", 2/(r-1);
                print " ";
                print " ";
                print " ";
                print " ";
            end if;
        end for;
    end for;
end procedure;


primes_r := [5, 7];
primes_p := [5, 7];


print " ";
print " ";
print " ";
print " ";
print "##########################################################";
print "We compute the cluster picture and conductor of the curve";
print "Cplus(r, p, a, c) at r when r divides a*bp.";
print "##########################################################";
print " ";
print " ";
print " ";
print " ";

/*
for r in primes_r do
    for p in primes_p do
        if p ne r then
            Cplus_at_r_case2(r, p, 3*r, 3);
            print"#############################################";
            print "CHANGING PARAMETER p !!!!";
            print"#############################################";
            print " ";   
        end if;
    end for;
    print"#############################################";
    print "CHANGING PARAMETER r !!!!";
    print"#############################################";
    print " ";
end for;

*/


Cplus_at_r_case2(5, 7, 3*5, 3);
print"#############################################";
print "CHANGING PARAMETER r !!!!";
print"#############################################";
print " ";   
Cplus_at_r_case2(7, 5, 3*7, 3);
print"#############################################";
print "CHANGING PARAMETER r !!!!";
print"#############################################";
print " ";   
Cplus_at_r_case2(7, 11, 3*7, 3);
print"#############################################";
print "CHANGING PARAMETER r !!!!";
print"#############################################";
print " ";   
Cplus_at_r_case2(7, 13, 3*7, 3);