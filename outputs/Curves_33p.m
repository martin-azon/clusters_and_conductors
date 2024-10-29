function cond_Eminus_a(a, c, p, q); 
    //returns the conductor exponent of the curve associated to the parameters a, b at the prime q
    E := EllipticCurve([-3*c, -2*(2*a^p -c^3)]);
    print E;    
    print "Kodaira Symbol of E at 3 when 3|a: ", KodairaSymbol(E, 3);
    print " ";

    return Valuation(Conductor(E), q);
end function;


/*
function cond_Epl_b(b, c, p, q); 
    //returns the conductor exponent of the curve associated to the parameters A, B, a, b at the prime q
    E := EllipticCurve([-3*c, -2*(c^3 - 2*b^p)]);
    return Valuation(Conductor(E, q);
end function;

*/


function cond_at_3_a(p, rge);
    exp_at3 := [ ];
    for a in [-rge..rge] do
        for c in [-rge..rge] do
            bp := c^3 - a^p;
            if (a*bp*c ne 0) and (Gcd(Gcd(a, bp), c) eq 1) and (a mod 3 eq 0) then 
                print "a = ", a, ", bp = ", bp, ", c =", c;
                print " ";
                cond_exp := cond_Eminus_a(a, c, p, 3);
                print "Conductor exponent at 3 is ", cond_exp;
                if cond_exp eq 1 then
                    print "MULTIPLICATIVE REDUCTION AT 3!!!!!!!!";
                end if;
                exp_at3 := Append(exp_at3, cond_exp);
                print " ";
                print " ";
                print " ";
                print " ";
            end if;
        end for;
    end for;
    return exp_at3;
end function;


print " ";
print " ";
print " ";
print " ";
print "##########################################################";
print "We compute the Kodaira type and conductor of the curve";
print "Cminus(3, p, a, c) at 3 when 3 divides a for p ranging";
print "in {5, 7, 11, 13}.";
print "##########################################################";
print " ";
print " ";
print " ";
print " ";


exp_p5 := cond_at_3_a(5, 20);

print " ";
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";

exp_p7 := cond_at_3_a(7, 20);

print " ";
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";

exp_p11 := cond_at_3_a(11, 20);

print " ";
print"#############################################";
print "CHANGING PARAMETER p !!!!";
print"#############################################";
print " ";

exp_p13 := cond_at_3_a(13, 20);

print " ";
print " ";


print "When p = 5 the conductor exponents are:";
print exp_p5;
print " ";
print "When p = 7 the conductor exponents are:";
print exp_p7;
print " ";
print "When p = 11 the conductor exponents are:";
print exp_p11;
print " ";
print "When p = 13 the conductor exponents are:";
print exp_p13;
print " ";
