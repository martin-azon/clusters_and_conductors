//We are going to compute the cluster picture of the curves C^+ and C^- 
//defined in [Chen-Koutsianas], p.9 of the latest version

R<x> := PolynomialRing(Rationals()); //we begin over the rationals

function Minpolw(r); //generates the minimal polynomial of w, the generator of K=Q(zeta_r)^+
    Cycl<zeta> := CyclotomicField(r);
    K<w> := sub<Cycl | zeta + 1/zeta>;
    return MinimalPolynomial(w);
end function;


function frbminus(b, c, r, p); //constructs the polynomial defining the curve Cminus
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := (c)^(r)*Evaluate(f, x/c) -2*(c^r-2*b^p);
    return g;
end function;


function frbplus(b, c, r, p);
    return (x+2*c)*frbminus(b, c, r, p);
end function;

function framinus(a, c, r, p); //constructs the polynomial defining the curve Cminus
    h := Minpolw(r);
    f := (-1)^(Numerator((r-1)/2))*x*Evaluate(h, -x^2 + 2);
    g := (c)^(r)*Evaluate(f, x/c) -2*(2*a^p - c^r);
    return g;
end function;


function fraplus(a, c, r, p);
    return (x+2*c)*framinus(a, c, r, p);
end function;

