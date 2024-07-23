# clusters_and_conductors
Numerical tests to compute the conductor of some hyperelliptic Frey curves using cluster pictures.

I am naming files by the name of the curve, the place we work at and the case we deal with.
By now, different cases appear only when we look at the prime r or the place qr in Q(zeta)^+.
  case1 means r does not divide ab,
  case2 means r divides ab.

Recall that we are manipulating a, a^p, c, c^r, and b^p, but we cannot access directly b (which is not an integer).
Thus, whenever we are in case 2, I assume that r divides a and not bp, because this leads to pathological cases, computations take much longer and this would not occur in our setting. 

All outputs are placed in the outputs folder. They have the same name as the magma file they come from, with .m replaced by .txt, e.g. your_favorite_file.m ----> your_favorite_file.txt .

Tim's package on clusters is called "clusters.m". I'm also putting it as an attached file for you to download it and use it as you want.
Here you have the link to download the redlib package: 

https://people.maths.bris.ac.uk/~matyd/redlib/redlib.html

BEWARE: none of the packages is finished, so we better be cautious while using them!

Feel free to modify, add and manipulate anything you want! Just add comments so that everyone can keep track of the changes we make :D
