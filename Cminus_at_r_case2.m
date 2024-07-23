//We are going to compute the cluster picture and conductor of the curve C^- (a.k.a. Cminus) at r when r divides a.
//We expect Cminus the conductor to be r-1 in that case!

Attach("clusters.m");

R<x> := PolynomialRing(Rationals()); //we begin over the rationals

function Minpolw(r); //generates the minimal polynomial of w, the generator of K=Q(zeta_r)^+
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function frminus(a, c, r, p); //constructs the polynomial defining the curve Cminus
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := (c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r);
    return g;
end function;


procedure Cminus_at_r_case2(r, p, rge_a, rge_c); 
    //prints the cluster picture and the conductor of Cminus at r when r divides a*bp
    for a in [-rge_a..rge_a] do
        for c in [-rge_c..rge_c] do
            bp := c^r - a^p;
            if (Gcd(a, c) eq 1) and (a*bp*c ne 0) and (a mod r eq 0) then //assuming that the solution to the dioph. eq. is nontrivial
                frm := frminus(a, c, r, p);
                print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c;
                //print "Factorisation of b^p = ", Factorization(bp);
                //print " ";
                print "Polynomial frminus = ", frm; 
                print " ";
                C := ClusterPicture(frm, r);
                print "The cluster picture of Cminus at r is :";
                print C;
                print " ";
                print "The conductor of Cminus at r is", Conductor(HyperellipticCurve(frm), r);
                depth_m := p*Valuation(a, r)/2 + Valuation(bp, r)/2 - r/(r-1); //expected depth according to the overleaf
                //note that Tim's package deals with absolute depths and not relative ones
                //so magma gives the same depths as the ones we have in the overleaf!
                print "Expected depth n = ", depth_m;
                print " ";
                print " ";
                print " ";
                print " ";
            end if;
        end for;
    end for;
end procedure;


primes_r := [5, 7];
primes_p := [7, 11, 13];

print "We compute the cluster pictures and conductor of the curve";
print "Cminus(r, p, a, c) at r when r divides a*bp.";


for r in primes_r do
    print"#############################################";
    print "CHANGING PARAMETER r !!!!";
    print"#############################################";
    print " ";
    for p in primes_p do
        if p ne r then
            print"#############################################";
            print "CHANGING PARAMETER p !!!!";
            print"#############################################";
            print " ";
            Cminus_at_r_case2(r, p, 10, 5);    
        end if;
    end for;
end for;
