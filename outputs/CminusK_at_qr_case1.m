//We compute the cluster picture and conductor of the base change of the curve C^- (a.k.a. Cminus) to 
//K = Q(zeta)^+ at the place qr in K which lies above r, when r does not divide ab.
//We expect Cminus to be semistable at such places!

Attach("clusters.m");

function Minpolw(r); //generates the minimal polynomial of w, the generator of K=Q(zeta_r)^+
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function extK(r : prec:= 50);
    //returns the extension K of Qr obtained by adjoining zeta_r + 1/zeta_r
    MinPolw := Minpolw(r);
    Qr := pAdicField(r, prec);
    R<x> := PolynomialRing(Qr);
    minpolw := elt<R | Evaluate(MinPolw, x+2)>;
    //print IsEisenstein(minpolw); it is always true!
    K := ext<Qr | minpolw>;
    return K;
end function;

function frminus(a, c, r, p : prec := 50); //constructs the polynomial defining the curve Cminus
    R<x> := PolynomialRing(pAdicField(r, prec));
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := (c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r);
    return g;
end function;


/*
function frminusK(a, c, r, p); //constructs the polynomial over K defining the (base change of the) curve Cminus
    K<w> := extK(r);
    h := Minpolw(r);
    RK<x> := PolynomialRing(K);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := (c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r);
    return g;
end function;
*/


procedure CminusK_at_qr_case1(r, p, rge_a, rge_c);
    //prints the cluster picture and the conductor of Cminus at r when r does not divide a*bp
    K<w> := extK(r);
    for a in [-rge_a..rge_a] do
        for c in [-rge_c..rge_c] do
            bp := c^r - a^p;
            if (Gcd(a, c) eq 1) and (a*bp*c ne 0) and (a*bp mod r ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                frm := frminus(a, c, r, p);
                print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c;
                print "Polynomial frminus = ", frm; 
                print " ";
                print "Factorisation of frm in Qr is ", Factorization(frm);
                print " ";
                print " ";
                RK<X> := PolynomialRing(K);
                Frm := Evaluate(frm, X);
                C := ClusterPicture(Frm);
                print "The cluster picture of Cminus at r is :";
                print C;
                print " ";
                print "Expected depth is 1/2";
                print " ";
                print "The conductor of Cminus at r is", Valuation(Conductor(HyperellipticCurve(Frm)));
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

print " ";
print "##########################################################";
print "We compute the cluster pictures and conductor of the curve";
print "Cminus(r, p, a, c) at r when r does not divide a*bp.";
print "We call w = zeta + 1/zeta";
print "##########################################################";
print " ";

for r in primes_r do
    for p in primes_p do
        if p ne r then
            CminusK_at_qr_case1(r, p, 10, 5); 
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
