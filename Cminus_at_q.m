//We are going to compute the cluster picture and conductor of the curve C^- (a.k.a. Cminus) at any place q dividng a*b, q ne r.
//We expect Cminus to be semistable at such places!

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


procedure Cminus_at_q(r, p, rge_a, rge_c); //prints the cluster picture of Cminus at q ne r
    for a in [-rge_a..rge_a] do
        for c in [-rge_c..rge_c] do
            bp := c^r - a^p;
            if (Gcd(a, c) eq 1) and (a*bp*c ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                frm := frminus(a, c, r, p);
                print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c;
                print "Factorisation of b^p = ", Factorization(bp);
                print " ";
                print "Polynomial frminus = ", frm; //displaying places of bad reduction
                BadPrimes:=Factorization(Integers()!Discriminant(frm));
                print "Bad primes are: ", BadPrimes;
                print " ";
                print " ";
                for i in [2..#BadPrimes] do //i begins at position 2 because BadPrimes[1] = 2
                    q := BadPrimes[i][1]; //taking only the prime and not the power 
                    if q ne r then
                        C := ClusterPicture(frm, q);
                        print "The cluster picture of Cminus at ", q, "is :";
                        print C;
                        print " ";
                        print "The conductor of Cminus at ", q, "is", Conductor(HyperellipticCurve(frm), q);
                        depths_C := C`d;
                        depth_n := p*Valuation(a, q)/2 + Valuation(bp, q)/2; //expected depth
                        //Recall that bp = b^p so p*v_q(b) = v_q(bp)!!!!!
                        for j in [1..#depths_C - 1] do
                            if depths_C[j] ne depth_n then
                                print"#############################################";
                                print"DEPTHS DON'T MATCH!!!!!! BEWARE!!!!!!!!!!!!!!";
                                print"#############################################";                        
                            end if;
                        end for;
                        print "Expected depth n = ", depth_n;
                        print " ";
                    end if;
                end for;
            print " ";
            print " ";
            print " ";
            print " ";
            end if;
        end for;
    end for;
end procedure;


primes_r := [r : r in [5..15] | IsPrime(r)];
primes_p := [r : r in [5..11] | IsPrime(r)];

print "We compute the cluster pictures and conductor of the curve";
print "Cminus(r, p, a, c) at q when q is a place not dividing 2r.";

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
            Cminus_at_q(r, p, 5, 5);
        end if;
    end for;
end for;
