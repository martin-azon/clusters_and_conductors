//We compute the cluster picture and conductor of the base change of the curve C^- (a.k.a. Cminus) to 
//K = Q(zeta)^+ at the place qr in K which lies above r, when r divides ab.

Attach("clusters.m");

function Minpolw(r); //generates the minimal polynomial of w, the generator of K=Q(zeta_r)^+
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function extK(r : prec:= 100);
    //returns the extension K of Qr obtained by adjoining zeta_r + 1/zeta_r
    MinPolw := Minpolw(r);

    Qr := pAdicField(r, prec);
    R<t> := PolynomialRing(Qr);
    minpolw := elt<R | Evaluate(MinPolw, t+2)>;
    //print IsEisenstein(minpolw); it is always true!
    K := ext<Qr | minpolw>;
    return K;
end function;


function frminusK(a, c, r, p); //constructs the polynomial over K defining the (base change of the) curve Cminus
    K<w> := extK(r);
    h := Minpolw(r);
    RK<x> := PolynomialRing(K);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := (c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r);
    return g;
end function;



procedure CminusK_at_qr_case2(r, p, rge_a, rge_c);
    //prints the cluster picture and the conductor of Cminus at r when r does not divide a*bp
    K<w> := extK(r);
    for a in [-rge_a..rge_a] do
        for c in [-rge_c..rge_c] do
            bp := c^r - a^p;
            if (Gcd(a, c) eq 1) and (a*bp*c ne 0) and (a mod r eq 0) then //assuming that the solution to the dioph. eq. is nontrivial
                frm := frminusK(a, c, r, p);
                print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c;
                print "Polynomial frminus = ", frm; 
                print " ";
                C := ClusterPicture(frm);
                print "The cluster picture of Cminus at r is :";
                print C;
                print " ";
                depth_m := p*(r-1)*Valuation(a, r)/4 + Valuation(bp, r)/2 + 1 -r/2;
                print "Expected depth is", depth_m;
                print " ";
                print "The conductor of Cminus at q_r is", Valuation(Conductor(HyperellipticCurve(frm)));
                print " ";
                print " ";
                print " ";
                print " ";
            end if;
        end for;
    end for;
end procedure;

primes_r := [5, 7, 11];
primes_p := [7, 11, 13, 17];

print " ";
print " ";
print " ";
print " ";
print "##########################################################";
print "We compute the cluster picture and conductor of the curve";
print "Cminus(r, p, a, c) at r when r divides a*bp.";
print "We call w = zeta + 1/zeta.";
print "##########################################################";
print " ";
print " ";
print " ";
print " ";

for r in primes_r do
    for p in primes_p do
        if p ne r then
            for i in [-3..3] do
                CminusK_at_qr_case2(r, p, i*r, 5);
            end for; 
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

