# clusters_and_conductors
<pre>

This is a repository containing numerical verifications for the computations done in the preprint


  
Conductor exponents for families of hyperelliptic curves, 
by Martin Azon, Mar Curcó-Iranzo, Maleeha Khawaja, Céline Maistret and Diana Mocanu.

  
  
All numerical tests were performed using Tim Dokchitser's package "clusters.m". 
The authors acknowledge him for sharing it wiht us and allowing us to use it.

  
Files are stored in three different folders, one for each of the families of curves studied in the article:

Crrp, which corresponds to the family of curves C_r associated to the equation of signature (r, r, p),
Cminus, which corresponds to the family of curves C_r^- associated to the equation of signature (p, p, r),
Cplus, which corresponds to the family of curves C_r^+ associated to the equation of signature (p, p, r).

In each folder one will find different magma files ( .m ), with the corresponding output in text format ( .txt ).

  
In each file appear the computions of the cluster pictures and conductor exponents of the corresponding curve in a specific case. 
The different cases are listed below:

  
Crrp_q ---> Computes clusters and conductors of Crrp at places dividing ab, different from 2, r.
Crrp_r_cs1 ---> Computes clusters and conductors of Crrp at r when r does not divide ab.
Crrp_r_cs2 ---> Computes clusters and conductors of Crrp at r when r divides ab.

Cminus_q ---> Computes clusters and conductors of Cminus at places dividing a, different from 2, r.
Cminus_r_cs1 ---> Computes clusters and conductors of Cminus at r when r does not divide ab and the defining polynomial gminus is reducible.
Cminus_r_cs2 ---> Computes clusters and conductors of Cminus at r when r does not divide ab and the defining polynomial gminus is irreducible.
Cminus_r_cs3 ---> Computes clusters and conductors of Cminus at r when r divides ab.

Cplus_q_a ---> Computes clusters and conductors of Cplus at places dividing a, different from 2, r.
Cplus_q_b ---> Computes clusters and conductors of Cplus at places dividing b, different from 2, r.
Cplus_r_cs1 ---> Computes clusters and conductors of Cplus at r when r does not divide ab and the polynomial gminus is reducible.
Cplus_r_cs2 ---> Computes clusters and conductors of Cplus at r when r does not divide ab and the polynomial gminus is irreducible.
Cplus_r_cs3 ---> Computes clusters and conductors of Cplus at r when r divides a.
Cplus_r_cs4 ---> Computes clusters and conductors of Cplus at r when r divides b.

  
Note that the triple (a, b, c), assumed to be a solution to the diophantine equation, in general does not exists. 
That is why, we consider two integers among a, b, c and work only with the r-th or p-th power of the remaining one. 
For example, for the curve Crrp, we take a, b as input and consider only cp := a^r + b^r, which is an integer, but its p-th root is not.
Similarly, when working with Cminus, we take a, c as input and consider only bp := c^r - a^p. 

</pre>
