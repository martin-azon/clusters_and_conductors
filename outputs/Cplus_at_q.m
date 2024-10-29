//We are going to compute the cluster picture and conductor of the curve C^+ (a.k.a. Cplus) at any place q dividing a*b, q ne r.
//We expect Cminus to be semistable at such places!

Attach("clusters.m");

R<x> := PolynomialRing(Rationals()); //we begin over the rationals

function Minpolw(r); //generates the minimal polynomial of w, the generator of K=Q(zeta_r)^+
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;

function frplusa(a, c, r, p); //constructs the polynomial defining the curve Cminus
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := ((c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r))*(x+2*c);
    return g;
end function;

function frplusb(b, c, r, p); //constructs the polynomial defining the curve Cminus
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := ((c)^(r)*Evaluate(f, x/c) -2*(c^r - 2*b^p))*(x+2*c);
    return g;
end function;


procedure Cplus_at_q_a(r, p, rge_ab, rge_c); //prints the cluster picture of Cplus at q ne r
    for a in [-rge_ab..rge_ab] do
        for c in [-rge_c..rge_c] do
            bp := c^r - a^p;
            if (Gcd(a, c) eq 1) and (a*bp*c ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                frp := frplusa(a, c, r, p);
                print "r = ", r, ", p = ", p, ", a = ", a, ", b^p = ", bp, ", c = ", c;
                print "Factorisation of b^p = ", Factorization(bp);
                print " ";
                print "Polynomial frplus =", frp; 
                BadPrimes:=Factorization(Integers()!Discriminant(frp));
                print "Bad primes are: ", BadPrimes; //displaying places of bad reduction
                print " ";
                print " ";
                print " ";
                for i in [2..#BadPrimes] do //i begins at position 2 because BadPrimes[1] = 2
                    q := BadPrimes[i][1]; //taking only the prime and not the power 
                    if (q ne r) and (a mod q eq 0) then
                        C := ClusterPicture(frp, q);
                        depth_n := p*Valuation(a, q)/2 + Valuation(bp, q)/2; //expected (absolute) depth
                        print "The cluster picture of Cplus at ", q, "is :";
                        print C;
                        print "Expected depth n = ", depth_n;
                        depths_C := C`d;
                        //Recall that bp = b^p so p*v_q(b) = v_q(bp)!!!!!
                        for j in [1..#depths_C - 1] do
                            if depths_C[j] ne depth_n then
                                print " ";
                                print " ";
                                print"#############################################";
                                print"DEPTHS DON'T MATCH!!!!!! BEWARE!!!!!!!!!!!!!!";
                                print"#############################################";                        
                                print " ";
                                print " ";
                            end if;
                        end for;
                        print " ";
                        print "The conductor of Cplus at ", q, "is", Conductor(HyperellipticCurve(frp), q);
                        print " ";
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


procedure Cplus_at_q_b(r, p, rge_ab, rge_c); //prints the cluster picture of Cplus at q ne r
    for b in [-rge_ab..rge_ab] do
        for c in [-rge_c..rge_c] do
            ap := c^r - b^p;
            if (Gcd(b, c) eq 1) and (ap*b*c ne 0) then //assuming that the solution to the dioph. eq. is nontrivial
                frp := frplusb(b, c, r, p);
                div_other_2r := false;
                for pr in Factorization(b) do  //we check if b
                    if (pr[1] ne 2) and (pr[1] ne r) then
                    div_other_2r := true;
                    end if;
                end for;
                if div_other_2r then 
                    print "r = ", r, ", p = ", p, ", b = ", b, ", a^p = ", ap, ", c = ", c;
                    print " ";
                    print "Polynomial frplus =", frp; 
                    BadPrimes:=Factorization(Integers()!Discriminant(frp));
                    BadPrimes := [q[1] : q in BadPrimes | (b mod q[1] eq 0) and (q[1] mod 2 eq 1)];
                    print "Odd bad primes dividing b are: ", BadPrimes; //displaying places of bad reduction
                    print " ";
                    print " ";
                    print " ";
                    for q in BadPrimes do //i begins at position 2 because BadPrimes[1] = 2
                        if (q ne r) then
                            C := ClusterPicture(frp, q);
                            depth_n := p*Valuation(b, q)/2 + Valuation(ap, q)/2; //expected (absolute) depth
                            print "The cluster picture of Cplus at ", q, "is :";
                            print C;
                            print "Expected depth n = ", depth_n;
                            depths_C := C`d;
                            //Recall that bp = b^p so p*v_q(b) = v_q(bp)!!!!!
                            for j in [1..#depths_C - 1] do
                                if depths_C[j] ne depth_n then
                                    print " ";
                                    print " ";
                                    print"#############################################";
                                    print"DEPTHS DON'T MATCH!!!!!! BEWARE!!!!!!!!!!!!!!";
                                    print"#############################################";                        
                                    print " ";
                                    print " ";
                                end if;
                            end for;
                            print " ";
                            print "The conductor of Cplus at ", q, "is", Conductor(HyperellipticCurve(frp), q);
                            print " ";
                            print " ";
                        end if;
                    end for;
                end if;
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



print " ";
print " ";
print " ";
print " ";
print "##########################################################";
print "We compute the cluster pictures and conductor of the curve";
print "Cplus(r, p, a, c) at q when q is a place not dividing 2r.";
print "##########################################################";
print " ";
print " ";
print " ";
print " ";

/*

Cplus_at_q_b(5, 7, 3*5, 3);
print"#############################################";
print "CHANGING PARAMETER r !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(5, 11, 3*5, 3);
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(7, 5, 3*7, 3);
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(7, 11, 3*7, 3);
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(7, 13, 3*7, 3);


*/

Cplus_at_q_b(5, 7, 3*5, 3);
print"#############################################";
print "CHANGING PARAMETER r !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(5, 11, 3*5, 3);
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(7, 5, 3*7, 3);
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(7, 11, 3*7, 3);
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";   
Cplus_at_q_b(7, 13, 3*7, 3);







