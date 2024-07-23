/*******************************************************************

Cluster library for hyperelliptic curves                      

By TD, RootNumber by MB

/*******************************************************************/
  
//freeze;

// TODO: Balance, FrobeniusName
// Igusa invariants

declare type ClPic;            // Cluster picture


declare attributes ClPic:
  B,           // [*[*1,2*],3*]                   Main List
  C,           // [[1],[2],[3],[1,2],[1,2,3]]     All clusters, starts with roots, 
  //                                              ends with top, sorted by size
  // Below this line up to name: defined when C is computed
  //
  N,           // 3                               Total number of points of B
  g,           // 1                               Total genus 
  Co,Ce,Cu,    // [1,2], [...], []                odd,even,ubereven cluster indices
  Cpo,         // [4,5]                           Indices of proper (non-root) clusters
  Cpi,         // [5]                             Indices of principal clusters (new defn)
  Ct,          // [4]                             Indices of twins
  ch,          // [[],[],[],[1,2],[1,2,3]]        Children indices for each cluster
  pa,          // [4,4,5,5,0]                     Parent indices for each cluster
  Cg,          // [0,0,0,0,0]                     Genus for every cluster
  balanced,    // boolean                         IsBalanced
  name,        // U:0:0:1                         [copied until here by ClTreeCopy]
  f,           // (x-1)(x^2-2)                    defining polynomial (if assigned)
  r,           // [1+O(5^20),...]                 p-adic roots (if assigned)
  M,           // Matrix(90,1; 1,90)              valuation difference matrix
  d,           // [0,0,0,1/2,0]                   depth (=d(c,infty)) for proper clusters
  vcf,         // 0                               valuation of the leading coefficient

  G,           // from Galois representation machinery           
  Gr,
  GtoGr, 
  Gact,
  I,
  ramgps,
  Frob,
  Frobr,
  tamecharacter,
  A,
  K,
  F,
  pi,
  cf,
  sqrtfield,    // finite field
  sqrtlist,     // tuples [<a,sqrta>,...] already computed (stored for consistency)
  
  // Below this line: assigned if frob is assigned
  frob,        // (1,2)                           Frobenius permutation on proper clusters
  froblinks,   // [[7,8]]                         links from frobenius orbits
  frobsigns,   // [-1,1,0,0,0]                    frobenius signs for certain (even+...) proper clusters
  froborbit,   // [1,1,2,2,3]                     which frobenius orbit proper cluster belongs to
  frobname,    // U+:0:0:1 
  frobtexname; // U$^+$:0:0:1 

   
declare verbose ClPic,3;     // Verbose printing


forward DefineClusters;


//////////////////////////////////////// mmylib stuff

Z:=Integers();
Q:=Rationals();
PR:=PolynomialRing;
RFF:=RationalFunctionField;
CD:=CremonaDatabase();
R<x>:=PR(Q);
function SortSet(X)           return Sort(SetToSequence(Set(X))); end function;
function sif(cond,s)          
  if Type(cond) in [SeqEnum,SetEnum,List] then cond:=not IsEmpty(cond); end if;
  return cond select s else ""; 
end function;

function DelSymbols(s,delsymb) 
  if Type(s) ne MonStgElt then s:=Sprint(s); end if;
  if Type(delsymb) eq MonStgElt then delsymb:=Eltseq(delsymb); end if;  
  s:=[c: c in Eltseq(s) | not (c in delsymb)];
  return IsEmpty(s) select "" else &cat s;
end function;

function DelSpaces(s)    // delete spaces from a string s
  return DelSymbols(s," \n");
end function;

function Count(S,x)                           // Count elements equal to x in S
  if Type(S) eq MonStgElt then S:=Eltseq(S); end if;
  return #[z: z in S | z eq x];
end function;

procedure GlobalSet(var,value)
  Q:=Rationals();
  if not (var in GetAttributes(FldRat)) then  
    AddAttribute(FldRat,var);
  end if;
  Q``var:=value;
end procedure;

function GlobalGet(var)
  Q:=Rationals();
  return Q``var;
end function;

function PrintSequence(L: sep:=", ", prfun:=Sprint)    
  if IsEmpty(L) then return ""; end if;
  return &cat[prfun(L[i]) * (i eq #L select "" else sep): i in [1..#L]];
end function;

procedure SortBy(~L,f: sign:=1)
  if Type(L) eq SetEnum then
    L:=SetToSequence(L);
  end if;
  Sort(~L,func<a,b|fa lt fb select -sign else (fa eq fb select 0 else sign)
                   where fa is f(a) where fb is f(b)>);
end procedure;                

procedure write(filename,str: con:=true, rewrite:=false, newline:="\n")
  if con then str; end if;
  F:=Open(filename,rewrite select "w" else "a");
  WriteBytes(F,[StringToCode(c): c in Eltseq(Sprint(str)*newline)]);
  Flush(F);
end procedure;

function ReplaceStringFunc(s,fs,ts)
  if Type(s) ne MonStgElt then s:=Sprint(s); end if;
  if Type(fs) eq SeqEnum then
    for i:=1 to #fs do
      s:=ReplaceStringFunc(s,fs[i],ts[i]);
    end for;
    return s;
  end if;
  return SubstituteString(s,fs,ts);
end function;

procedure ReplaceString(~s,fs,ts)
  s:=ReplaceStringFunc(s,fs,ts);
end procedure;

function Last(v)
  if Type(v) in [SeqEnum,List,SetIndx,Tup] then return v[#v]; end if;
  if HasSignature("Eltseq",[Type(v)]) then 
    w:=Eltseq(v); return w[#w]; 
  end if;
  error "Last: unrecognised type";
end function;

function Match(s,m)
  R:=RealField();
  s:=Eltseq(s cat CodeToString(127));
  m:=Eltseq(m cat CodeToString(127));

  // Convert "HEL%%LO %S(%I)" into [* "HEL%LO ","%S","(","%I",")" *]

  M:=[""];
  skip:=false;
  for i:=1 to #m do
    c:=m[i];
    if c ne "%" then
      l:=#(M[#M]);
      cmd:=(l ne 0) and (M[#M][1] eq "%");
      if cmd and (l eq 1) and (StringToCode(c) in [StringToCode("a")..StringToCode("z")]) then
        c:=CodeToString(StringToCode(c)-StringToCode("a")+StringToCode("A"));
      end if;
      M[#M] cat:= c;
      if not cmd then continue; end if;
      if (c in ["O","M"]) and (l eq 1) then continue; end if;
      Append(~M,"");
      continue;
    end if;
    if skip then skip:=false; continue; end if;
    if m[i+1] eq "%" then
      M[#M] cat:= c; skip:=true; continue;
    end if;
    Append(~M,"%");
  end for;
  M:=[s: s in M | #s ne 0];

  buf:=[* *];
  for i:=1 to #M do
    c:=M[i];
    if (#c eq 1) or (c[1] ne "%") then
      if (#s lt #c) or (&cat(s[1..#c]) ne c) then return false,buf; end if;
      for j:=1 to #c do Remove(~s,1); end for;
    elif c in ["%S","%E"] then
      if i eq #M then
        Append(~buf,&cat s); 
        if c eq "%E" then try buf[#buf]:=eval buf[#buf]; catch e return false, buf; end try; end if;
        return true,buf;
      end if;
      stop:=M[i+1];
      l:=0;
      if (#stop eq 3) and (stop[1] eq "%") and (stop[2] in ["M","O"]) then
        stop:=stop[3];
      end if;
      if (#stop eq 1) or (stop[1] ne "%") then
        for j:=1 to #s do
          if &cat(s[j..Min(#s,j+#stop-1)]) eq stop then l:=j; break; end if;
        end for;
      elif stop in ["%W","%I","%R"] then
        for j:=1 to #s do
          if (s[j] in ["0","1","2","3","4","5","6","7","8","9"])
             or ((stop ne "%W") and (s[j] eq "-"))
           then l:=j; break; end if;
        end for;
      else
        l:=1;
      end if;
      if l eq 0 then return false,buf; end if;
      Append(~buf,"");
      for j:=1 to l-1 do
        buf[#buf] cat:= s[1];
        Remove(~s,1);
      end for;
      if c eq "%E" then try buf[#buf]:=eval buf[#buf]; catch e return false, buf; end try; end if;
    elif (c[2] in ["M","O"]) and (#c eq 3) then
      ok:=false;
      while s[1] eq c[3] do Remove(~s,1); ok:=true; end while;
      if (c[2] eq "M") and (not ok) then return false,buf; end if;
    elif c[2] in ["W","I","R"] then
      l:=0;
      W:=s[1];
      if (W eq "-") and (c[2] eq "W") then return false,buf; end if;
      ok:=true;
      repeat
        try
          assert Last(W) ne " ";
          w:=eval W; 
          W cat:= s[l+2];
          error if not IsCoercible(c[2] eq "R" select R else Q,w),"";
          res:=w;
          l+:=1; 
        catch e
          ok:=false;
        end try;
      until not ok;
      if l eq 0 then return false,buf; end if;
      Append(~buf,res);
      for j:=1 to l do Remove(~s,1); end for;
    else
      error "Match: "*c*" is not implemented";
    end if;
  end for;
  return #s eq 0,buf;
end function;

CycleType:=func<g|Sort([#x: x in CycleDecomposition(g)])>;   // increasing order

function CanonicalElementOfCycleType(t)
  l:=[n+1: n in [1..&+t]]; n:=0;
  for c in t do l[n+c]:=n+1; n+:=c; end for;
  return Sym(&+t)!l;
end function;

function Last(v)
  if Type(v) in [SeqEnum,List,SetIndx,Tup] then return v[#v]; end if;
  if HasSignature("Eltseq",[Type(v)]) then 
    w:=Eltseq(v); return w[#w]; 
  end if;
  error "Last: unrecognised type";
end function;


///

sgnsymbol:=func<n|n eq 0 select "" else (n ge 0 select "+" else "-")>;


/////////////////////////////////////////////////////////////
//    Basic type functions                                 //
/////////////////////////////////////////////////////////////


intrinsic IsCoercible(B::ClPic, y::.) -> BoolElt, .
{Coerce a cluster tree.}
  return false, _;
end intrinsic;


intrinsic 'in'(B::ClPic, y::.) -> BoolElt
{"in" function for an cluster tree.}
  return false;
end intrinsic;


intrinsic Print(T::ClPic, level::MonStgElt)
{Print a cluster tree.}
  printf ReplaceStringFunc(T`B,["*"," ","[","]"],["","","(",")"]);
  if (assigned T`frob) and not IsEmpty(T`froblinks) and (level ne "Minimal") then
    printf " F"*DelSpaces(T`froblinks);
  end if;
  if (assigned T`d) and (level ne "Minimal") then
    printf " d="*DelSpaces(T`d);
  end if;
end intrinsic;


/////////////////////////////////////////////////////////////
//    List functions (T`B)                                 //
/////////////////////////////////////////////////////////////


function ListTreeSize(b)
  return Type(b) eq RngIntElt select 1 else &+[ListTreeSize(x): x in b]; 
end function;


function Flatten(b: sort:=true)
  if Type(b) eq RngIntElt 
    then return [b]; 
    else B:=&cat [Flatten(x: sort:=sort): x in b];
         return sort select Sort(B) else B; 
  end if;  
end function;


function ListToClusters(B)
  if Type(B) eq RngIntElt then return [[B]]; 
  elif #B eq 1 then return [[B[1]]]; 
  else return Append(&cat [ListToClusters(x): x in B],Flatten(B));
  end if;
end function;


function ListGreater(x,y,ignorenumbers) 
  case [Type(x),Type(y)]: 
    when [RngIntElt,RngIntElt]: return ignorenumbers select false else (x gt y); 
    when [RngIntElt,List]:      return false; 
    when [List,RngIntElt]:      return true; 
    when [List,List]:           
      xsize:=#Flatten(x);
      ysize:=#Flatten(y);
      if xsize gt ysize then return true; end if;
      if xsize lt ysize then return false; end if;
      for i:=1 to #x do
        if ListGreater(x[i],y[i],true) then return true; end if;
        if ListGreater(y[i],x[i],true) then return false; end if;
      end for;
      for i:=1 to #x do
        if ListGreater(x[i],y[i],ignorenumbers) then return true; end if;
        if ListGreater(y[i],x[i],ignorenumbers) then return false; end if;
      end for;
      return false; 
    else error "ListGreater: unrecognized type"*Sprint([Type(x),Type(y)]);
  end case;
end function;


function SortList(L)
  if Type(L) ne List then return L; end if;
  L:=[* SortList(c): c in L *];
  repeat
    swaps:=false;
    for i:=1 to #L-1 do 
      if ListGreater(L[i],L[i+1],false) then
        T:=L[i]; L[i]:=L[i+1]; L[i+1]:=T; swaps:=true;
      end if;
    end for;
  until not swaps;
  return L;
end function;


/////////////////////////////////////////////////////////////
//    Roots to cluster trees                               //
/////////////////////////////////////////////////////////////


/////////////////////////////////////////////////////////////
//    ClPic creation functions                            //
/////////////////////////////////////////////////////////////


intrinsic ClPicCreate() -> ClPic
{Create a cluster tree (hackobj function).}
  return New(ClPic);
end intrinsic;


procedure DefineClusters(~T)
  if assigned T`C then return; end if;
  g:=T`g;
  N:=T`N;
  C:=ListToClusters(T`B);                                      // All clusters
  SortBy(~C,func<c|<#c,c>>);                                   // sorted by size
  T`C:=C;

  T`Co:=[i: i in [1..#C] | IsOdd(#C[i]) ];                  // Odd
  T`Ce:=[i: i in [1..#C] | IsEven(#C[i]) ];                 // Even
  T`Ct:=[i: i in T`Ce | #C[i] eq 2];                        // Twins
 
  T`Cpo:=[i: i in [1..#C] | #C[i] gt 1];                     // Proper clusters
  //if #C[#C] eq 2*g+2 and #C[#C-1] eq 2*g+1 then 
  //  T`Cpo:=Prune(T`Cpo);                                   // not coroot in old version
  //end if;

  ch:=[ [i: i in [1..j-1] | C[i] subset C[j]]: j in [1..#C]];   // Children
  for i:=#ch to 1 by -1 do
    ci:=ch[i];
    for j in ci, k in ch[j] do 
      Exclude(~ci,k);                 // Exclude children of children
    end for;
    ch[i]:=ci;    
  end for;  
  T`ch:=ch;

  T`Cpi:=[Position(C,s): s in C | (#s gt 2) and             // Principal clusters
      ((#s le 2*g) or not exists{s0: s0 in C | 
      (#s0 ge 2*g) and (s0 ne s) and (s0 subset s)}) and 
      ( (s ne Last(C)) or (#Last(ch) ne 2) or IsOdd(#s) )];
 
  T`Cu:=[i: i in T`Ce | forall{c: c in ch[i] | IsEven(#C[c])}];   // Ubereven

  pa:=[0: c in C];                    // Parents, 0 for top
  for i in [1..#C], c in ch[i] do 
    pa[c]:=i; 
  end for;
  T`pa:=pa;

                                      // genera of components for each cluster
  T`Cg:=[Max(0,(n-1) div 2) where n is #[c: c in ch[i] | IsOdd(#C[c])]: i in [1..#C]];

  T`balanced:= IsEven(N) and (#[c: c in C | #c gt N/2] eq 1) and IsEven(#[c: c in C | #c eq N/2]);  // balanced
                 
end procedure;


procedure SetClPicEntries(~B,L: first:=true)
  if first then GlobalSet("i",1); end if;
  for j:=1 to #B do  
    if Type(B[j]) eq RngIntElt then
      i:=GlobalGet("i"); 
      B[j]:=L[i];
      GlobalSet("i",i+1); 
    else
      SetClPicEntries(~B[j],L: first:=false);
    end if;
  end for;
end procedure;


intrinsic ClusterPicture(B::List) -> ClPic
{Cluster picture for a given list B, e.g. B=[*[*1,2*],3*]}
  error if Type(B) ne List, "B must be a list, e.g. [*[*1,2*],3*]";

  T:=ClPicCreate();
  T`B:=B;
  T`N:=ListTreeSize(T`B);
  T`g:=(T`N-1) div 2;
  return T;
end intrinsic;


intrinsic ClusterPicture(B::List, links::SeqEnum) -> ClPic
{Cluster picture for a given list B, e.g. B=[*[*1,2*],[*3,4*],[*5,6*]*] 
  and Frobenius links, e.g. [[1,2],[3,4]]} 
  T:=ClusterPicture(B);
  error "not fully implemented";
  T`frob:=links;
  return T;
end intrinsic;


intrinsic ClusterPicture(C::SeqEnum[SeqEnum]: sort:=true) -> ClPic
{Cluster picture from a list of clusters}

  SortBy(~C,func<c|<#c,c>>);                                     // Children
  ch:=[ [i: i in [1..j-1] | C[i] subset C[j]]: j in [1..#C]];   
  for i:=#ch to 1 by -1 do
    ci:=ch[i];
    for j in ci, k in ch[j] do 
      Exclude(~ci,k);                 // Exclude children of children
    end for;
    ch[i]:=ci;    
  end for;  

  forward list;                          // convert to list
  list:=func<i|IsEmpty(ch[i]) select i else [* list(c): c in ch[i] *]>;
  return ClusterPicture(list(#C)); 
    
end intrinsic;


function ValuationMatrixToClusters(M)
  if ISA(Type(M),AlgMatElt) then 
    M:=[Eltseq(M[i]): i in [1..NumberOfRows(M)]];
  end if;
  clusters:=[];
  depths:=[];
  for m in Reverse(SortSet(Flat(M))) do
    c:=[];
    for i:=1 to #M do 
      if exists(j){j: j in [1..#c] | M[i,c[j][1]] ge m} 
        then Append(~c[j],i);
        else Append(~c,[i]);
      end if;
    end for;
    for cl in c do
    if cl notin clusters then
      Append(~clusters,cl);
      Append(~depths,m);
    end if;                          
    end for;
  end for;
  return clusters,depths;
end function;


intrinsic ClusterPicture(M::AlgMatElt) -> ClPic
{Cluster picture from a valuation matrix}
  C,d:=ValuationMatrixToClusters(M);
  T:=ClusterPicture(C);
  DefineClusters(~T);
  AssignDepths(~T,[d[Position(C,T`C[c])]: c in T`Cpo]);
  T`M:=M;
  return T;
end intrinsic;


function GaloisToPermutation(F,r: V:=Valuation)
  perm:=[];
  for x in r do
    Fx:=F(x);
    list:=[V(Fx-R): R in r];
    v,m:=Max(list);
    assert (v gt 0) and (#[x: x in list | x eq v] eq 1);   
      // F must permute the roots, just checking
    Append(~perm,m);
  end for;
  return Sym(#r)!perm;
end function;


function LiftSign(x)
  if x eq 1  then return 1; end if;
  if x eq -1 then return -1; end if;
  if x eq 0 then return 0; end if;
  error "LiftSign: x is not +1,-1,0";
end function;


intrinsic ClusterPicture(f::RngUPolElt) -> ClPic
{Cluster picture from a p-adic polynomial}

  K:=FieldOfFractions(BaseRing(f));
  require Type(K) in [FldPad]: "Base field should be p-adic";

  vprint CrvHyp,1: "Spliting the 2-torsion";
  
  F0:=SplittingField(f: Std:=false);             // K  = Base field
  n:=Degree(f);                                  // F0 = Splitting field of f /K
  g:=(n-1) div 2;
  k0<z>:=ResidueClassField(Integers(F0));
  p:=Characteristic(k0);
  
  f2:=PR(Z)!DefiningPolynomial(ext<k0|2>,PrimeField(k0));

  R<X>:=PR(K);
  pi0:=UniformizingElement(F0);
  f3:=R!MinimalPolynomial(pi0,K);
  f3:=Evaluate(f3,X^2);
  
  vprint CrvHyp,2: "Biquadratic extension";               // done correctly now!
 
  A:=GaloisRepresentations(f2*f3*f)[1];                   // F = Biquadratic ext of F0
  
  G<[Ggens]>:=Group(A);                                   // G
  r:=[r[1]: r in Roots(f,A`F)];
  assert #r eq n;
  
  Grgens:=[GaloisToPermutation(A`act(g),r): g in Ggens];
  Gr<[Grgens]>:=sub<Sym(n)|Grgens>;                       // Gr
  GtoGr:=hom<G->Gr|Grgens>;

  assert #Kernel(GtoGr) ge 4;  // 1 -> ker -> G -> Gr -> 1
   
  OK:=Integers(K);
  kK:=ResidueClassField(OK);
  F:=Field(A);
  OF:=Integers(F);
  pi:=UniformizingElement(F);
  k<z>,red:=ResidueClassField(OF);
  q:=#k;
  
  I<[Igens]>:=A`I;
  ramgps:=A`ramgps;
  Frob:=A`Frob;
  Frobr:=GtoGr(Frob);
  Gact:=A`act;
  
  error if IsEven(p), "p must be odd in LocalDataWithSemistableModel";
  
  tamecharacter:=map<G->k|x:->red(Gact(x)(pi)/pi)>;
  
  vprintf CrvHyp,1: "G=%o I=%o order(Frob)=%o G(rts)=%o ramgps=%o\n",
    GroupName(G),GroupName(I),Order(Frob),GroupName(Gr),
    DelSymbols([<GroupName(D[1]),D[2]>: D in ramgps]," \"");       // "

  e:=RamificationDegree(F,K);
  M:=Matrix([[Valuation(a-b)/e: a in r]: b in r]);
  T:=ClusterPicture(M);

  prec:=Precision(A`F); 
  rootprec:=Min([Valuation(Evaluate(f,x)): x in r]);
  maxrootdiff:=Max([e*M[i,j]: i,j in [1..#r] | i lt j]);

  vprintf CrvHyp,1: "Field precision: %o  Root precision: %o  Max(v(r[i]-r[j])): %o\n",
    prec, rootprec, maxrootdiff;

  error if (maxrootdiff gt prec/3) or (rootprec lt 3/4*prec), 
    "Not enough precision to compute the roots";
 
  T`f:=f;
  T`r:=r;
  T`G:=G;
  T`Gr:=Gr;
  T`GtoGr:=GtoGr;
  T`I:=I;
  T`ramgps:=ramgps;
  T`Frob:=Frob;
  T`Frobr:=Frobr;
  T`A:=A;
  T`Gact:=Gact;
  T`tamecharacter:=tamecharacter;
  T`K:=K;
  T`F:=F;
  T`pi:=pi;
  T`cf:=LeadingCoefficient(f);
  T`vcf:=Valuation(K!T`cf);
  T`sqrtfield:=ResidueClassField(Integers(T`F));
  T`sqrtlist:=[];
  
  // Orbits & stabilisers on clusters
  // [GroupName(Stabiliser(T`Gr,c)): c in Clusters(T)];
 
  Po:=ProperClusters(T);
  C:=Clusters(T);
  act:=PermutationAction(T,Po);
  T`frob:=act(Frob); 
  O:=[SortSet(c): c in CycleDecomposition(T`frob)];
  fo:=[[j: j in [1..#O] | i in O[j]][1]: i in [1..#Po]];
  T`froborbit:=fo;
  T`froblinks:=[ [Position(C,Po[i]),Position(C,Po[j])]: i,j in [1..#Po] | (i lt j) and (fo[i] eq fo[j]) and 
    not exists{k: k in [i+1..j-1] | fo[i] eq fo[k]}
  ];

  /*
  froblinked:=[C[c[1]]: c in T`froblinks];
  T`frobsigns:=[Z| EpsilonCharacter(T,i)(Frobenius(T,i)): i in Po];
  for i:=1 to #Po do
    if (T`frobsigns[i] ne 0) and Po[i] in froblinked then T`frobsigns[i]:=1; end if;
  end for;
  */
  
  T`frobsigns:=[LiftSign(Epsilon(T,c)(Frobenius(T))): c in Po];
  
  return T;
end intrinsic;


intrinsic ClusterPicture(f::RngUPolElt, p::RngIntElt: prec:=0) -> ClPic
{Cluster picture from a polynomial over the rationals}
  v:=Valuation(Discriminant(f),p);
  if prec eq 0 
    then P:=Sort(SetToSequence({v+3,2*v+3,10,20,40,100,200,500,1000}));
    else P:=[prec];
  end if;
  for precision in P do
    try
      vprint CrvHyp,1: "Trying precision =",precision;
      Qp:=pAdicField(p,precision);
      T:=ClusterPicture(PolynomialRing(Qp)!f);
      ok:=true;
    catch e 
      s:=e`Object;
      ok:=false;
    end try;
    if ok then break; end if;
  end for;
  error if not ok, "Could not compute the Cluster picture: "*s;
  return T;
end intrinsic;


intrinsic LeadingCoefficient(T:: ClPic) -> RngElt
{}
  require assigned T`cf: "Cluster picture not defined by a specific polynomial";
  return T`cf;
end intrinsic;


intrinsic ResidueField(T:: ClPic) -> FldAlg
{}
  return ResidueClassField(Integers(SplittingField(T)));
end intrinsic;


intrinsic ResidueClassField(T:: ClPic) -> FldAlg
{}
  return ResidueField(T);
end intrinsic;


intrinsic SplittingField(T:: ClPic) -> FldAlg
{}
  require assigned T`F: "Cluster not defined by a specific polynomial";
  return T`F;
end intrinsic;


intrinsic BaseField(T:: ClPic) -> FldAlg
{}
  require assigned T`K: "Cluster not defined by a specific polynomial";
  return T`K;
end intrinsic;


intrinsic RootsInside(T:: ClPic, c::SeqEnum) -> FldAlg
{Roots inside a cluster}
  return [Universe(r)| r[i]: i in c] where r is T`r;
end intrinsic;


intrinsic RootsInside(T:: ClPic, i::RngIntElt) -> FldAlg
{Roots inside a cluster (given by its index)}
  return RootsInside(T,Cluster(T,i));
end intrinsic;


intrinsic Center(T:: ClPic, c::SeqEnum) -> FldAlg
{Center of a cluster}
  /*  Galois-invariant if possible? */
  if assigned T`K and (#c mod ResidueCharacteristic(T) ne 0)
    then return &+[T`r[j]: j in c]/#c;
    else return T`r[c[1]];
  end if;
  /**/
  return T`r[c[1]];
end intrinsic;


intrinsic Center(T:: ClPic, i::RngIntElt) -> FldAlg
{Center of a cluster (given by its index)}
  return Center(T,Cluster(T,i));
end intrinsic;


intrinsic RootsOutside(T:: ClPic, c::SeqEnum) -> FldAlg
{Roots outside a cluster}
  return [Universe(r)| r[i]: i in [1..#r] | i notin c] where r is T`r;
end intrinsic;


intrinsic RootsOutside(T:: ClPic, i::RngIntElt) -> FldAlg
{Roots outside a cluster (given by its index)}
  return RootsOutside(T,Cluster(T,i));
end intrinsic;


intrinsic GaloisGroup(T:: ClPic) -> Grp
{}
  return T`G;
end intrinsic;


intrinsic InertiaGroup(T:: ClPic) -> Grp
{}
  return T`I;
end intrinsic;


intrinsic Frobenius(T:: ClPic) -> GrpElt
{Chosen Frobenius element of the Galois group of T}
  return T`Frob;
end intrinsic;


intrinsic Frobenius(T:: ClPic, c:: SeqEnum) -> GrpElt
{Frobenius element of the stabiliser of c}
  S:=Stabiliser(T,c);
  F:=Frobenius(T);
  return F^Min([i: i in Divisors(Order(F)) | F^i in S]);
end intrinsic;


intrinsic Chi(T:: ClPic, sigma::GrpPermElt) -> FldFinElt
{Tame character Chi associated to a cluster (sigma(pi)/pi mod pi)}
  G:=GaloisGroup(T);
  k,m:=ResidueField(T);
  pi:=T`pi;
  return m(T`Gact(G!sigma)(pi)/pi);
end intrinsic;


intrinsic ResidueFieldAction(T:: ClPic, sigma::GrpPermElt) -> .
{}
  G:=GaloisGroup(T);
  k,m:=ResidueField(T);
  return hom<k->k|[m(T`Gact(G!sigma)(k.1@@m))]>;
end intrinsic;


intrinsic LeadingCoefficient(T:: ClPic, c::SeqEnum) -> RngElt
{Leading coefficient of a cluster}
  pi:=T`pi;
  F:=SplittingField(T);
  K:=BaseField(T);
  eFK:=RamificationDegree(F,K);
  z:=Center(T,c);
  cc:=LeadingCoefficient(T) * &*[F| z-r: r in RootsOutside(T,c)] / 
    pi^(Z!(eFK*(Nu(T,c)-#c*Depth(T,c))));
  k,m:=ResidueField(T);
  return m(cc);
end intrinsic;


intrinsic LeadingCoefficient(T:: ClPic, i::RngIntElt) -> RngElt
{Leading coefficient of a cluster (given by its index)}
  return LeadingCoefficient(T,Cluster(T,i));
end intrinsic;


intrinsic Stabiliser(T:: ClPic, c::SeqEnum) -> GrpFin
{Stabiliser of a cluster in GaloisGroup(G)}
  G:=GaloisGroup(T);
  u:=T`GtoGr;
  H:=Stabiliser(u(G),Set(c));
  return H@@u;
end intrinsic;


intrinsic Stabiliser(T:: ClPic, i::RngIntElt) -> GrpFin
{Stabiliser of a cluster c in GaloisGroup(G) (with c given by its index i)}
  return Stabiliser(T,Cluster(T,i));
end intrinsic;


function LiftMapToCharacter(T,c,H)
  if #H eq 1 then return PrincipalCharacter(H); end if;
 
  _<[gens]>:=H;
  f:=[c(g): g in gens];
  o:=LCM([Order(a): a in f]);
  if o eq 1 then return PrincipalCharacter(H); end if;

  k:=Universe(f);
  a,m:=UnitGroup(k);
  prim:=m(a.1);
  zeta:=CyclotomicField(o: Sparse).1;
  lift:=func<x|zeta^(Z!(Log(prim,x)/(#k div o)))>;
    
  CC:=[c[3]: c in ConjugacyClasses(H)];
 
  return CharacterRing(H)! [lift(c(x)): x in CC]; 
end function;


intrinsic Sqrt(T:: ClPic, c::FldFinElt) -> FldFinElt
{}
  //Sprintf(">> Sqrt(%o)",c);
  if exists(d){d: d in T`sqrtlist | d[1] eq c} then return d[2]; end if;
  k:=T`sqrtfield;
  R<x>:=PR(k);
  r:=Roots(x^2-c);
  if IsEmpty(r) then              // enlarge k
    k:=ext<k|2>;
    T`sqrtfield:=k;
    T`sqrtlist:=[ [k|d[1],d[2]]: d in T`sqrtlist ];
    R<x>:=PR(k);
    r:=Roots(x^2-c);
  end if;
  //s:=r[Random(1,2)][1];                     // store and return
  s:=r[1][1];                                 // store and return
  Append(~T`sqrtlist,[c,s]);
  return s;
end intrinsic;


intrinsic Epsilon(T:: ClPic, c::SeqEnum) -> UserProgram
{Epsilon function of a cluster: sigma -> epsilon_c(sigma) in the residue field}
  require #c gt 1: "Cluster must be proper";

  // 0 for odd clusters
  if not IsEven(#c) then return func<sigma|0>; end if; 

  // for even clusters
  nu:=Nu(T,c);
  d:=Depth(T,c);
  F:=SplittingField(T);
  K:=BaseField(T);
  eFK:=RamificationDegree(F,K);
  cc:=LeadingCoefficient(T,c); 

  //">>",DelSpaces(c),nu,d,eFK,cc,"F_"*Sprint(#Parent(cc)),Order(cc),#ResidueField(T);
  
  function eps(sigma)
    //return ResidueFieldAction(T,sigma)(1);
    return ResidueFieldAction(T,sigma)(Sqrt(T,cc)) / 
      Sqrt(T,LeadingCoefficient(T,Sort(c^T`GtoGr(sigma)))) *
      Chi(T,sigma)^(Z!(eFK*((nu/2)-(#c div 2)*d)));
  end function;
  
  return eps; 
end intrinsic;


intrinsic Epsilon(T:: ClPic, i::RngIntElt) -> UserProgram
{Epsilon function of a cluster: sigma -> epsilon_c(sigma) in the residue field (with the cluster given by its index)}
  return Epsilon(T,Cluster(T,i)); 
end intrinsic;


intrinsic EpsilonCharacter(T:: ClPic, c::SeqEnum) -> AlgChtrElt
{Epsilon character of an even cluster, which is a complex character of its stabiliser}
  require #c gt 1: "Cluster must be proper";
  S:=Stabiliser(T,c);
  if IsOdd(#c) then return CharacterRing(S)!0; end if;
  return LiftMapToCharacter(T,Epsilon(T,c),S);
end intrinsic;


intrinsic ConjugateCluster(T:: ClPic, c::SeqEnum, sigma::GrpPermElt) -> SeqEnum
{Apply sigma in GaloisGroup(T) to a cluster c}
  G:=GaloisGroup(T);
  g:=T`GtoGr(G!sigma);
  csigma:=Sort(c^g);
  assert Position(Clusters(T),csigma) ne 0;
  return csigma;
end intrinsic;


intrinsic PermutationAction(T:: ClPic, C::SeqEnum) -> Map, GrpPerm 
{Galois action on the given Galois invariant set of clusters (even, odd, ubereven, all,...); 
returns h,h(G)}
  G:=GaloisGroup(T);
  if IsEmpty(C) then return CharacterRing(G)!0; end if;
  h:=hom<G->Sym(#C)|g:->[Position(C,ConjugateCluster(T,T`C[c],g)): c in C]>;
  return h,h(G);
end intrinsic;


intrinsic ToricRepresentation(T:: ClPic) -> GalRep, GalRep, GalRep
{Second argument returned is restriction to inertia, third is full Galois group}
  /*
  G:=GaloisGroup(T);
  P:=ProperClusters(T);
  PNU:=[i: i in [1..#P] | IsEven(T,P[i]) and not HasUberevenParent(T,P[i])];
  FO,FN,FS:=FrobeniusOrbitsOnClusters(T,PNU);
  chi:=&+[Induction(EpsilonCharacter(T,P[e]),G): e in FO];
  return (T`A)!!chi;
  */

  E:=[c: c in EvenClusters(T) | not IsUbereven(T,c)];
  G:=GaloisGroup(T);
  I:=InertiaGroup(T);
  if IsEmpty(E) then return (T`A)!!(CharacterRing(G)!0), CharacterRing(I)!0, CharacterRing(G)!0; end if;
  h,hG:=PermutationAction(T,E);
  EO:=E[[c[1]: c in Orbits(hG)]];
  chi:=&+[Induction(EpsilonCharacter(T,e),G): e in EO] -       // ind(epsilon) over G-orbits of 
    Induction(EpsilonCharacter(T,TopCluster(T)),G);            // even non-ubereven clusters,
  chiI:=Restriction(chi,InertiaGroup(T));
  return (T`A)!!chi, chiI, chi;                                           // minus epsilon(top cluster)

end intrinsic;

intrinsic ToricRootNumber(T:: ClPic) -> RngIntElt
{}
  EF:=EulerFactor(T);
  R<X>:=Parent(EF);
  WTor:=(-1)^Valuation(EF,X-1);
  Trep,Tor:=ToricRepresentation(T);
  
  error if ResidueCharacteristic(T) eq 2 or IsAbelian(InertiaGroup(T)) eq false, 
    "Even residue characteristic or nonabelian inertia";
  
  if Degree(ResidueClassField(Integers(BaseField(T)))) mod 2 eq 0 then
	return Integers()!WTor;
  else
	for x in CharacterTable(InertiaGroup(T)) do
	  if Order(x) eq 2 then
	    WTor:=WTor*(LegendreSymbol(-1,ResidueCharacteristic(T))^(InnerProduct(x,Tor)));
	  end if;
    end for;
    return Integers()!WTor;
  end if;
end intrinsic;

intrinsic AbelianRepresentation(T:: ClPic, c::SeqEnum) -> GalRep
{Representation of inertia stabiliser on the abelian part coming from the cluster}
  G:=GaloisGroup(T);
  I:=InertiaGroup(T);

  c0:=OddChildren(T,c);
  S:=Stabiliser(T,c);
  SI:=S meet I;
 
  if #c0 lt 3 then return CharacterRing(SI)!0; end if;
  
  h:=hom<SI->Sym(#c0)|g:->[Position(c0,ConjugateCluster(T,c,g)): c in c0]>;
  CC:=[c[3]: c in ConjugacyClasses(SI)];
  c0m1char:=CharacterRing(SI)![#Fix(h(x))-1: x in CC];

  eps:=Restriction(EpsilonCharacter(T,c),SI);

  lambdatilde:=Nu(T,c)/2 - Depth(T,c)* &+[#x div 2: x in Children(T,c)];
//"lambdatilde=",lambdatilde;
  F:=SplittingField(T);
  K:=BaseField(T);
  eFK:=RamificationDegree(F,K);
//"eFK=",eFK;
  pow:=Z!(eFK*lambdatilde);
//"pow=",pow;
  gamma:=func<sigma|Chi(T,sigma)^pow>;
//"SI=",GroupName(SI);
  gammatilde:=LiftMapToCharacter(T,gamma,SI);
//"gammatilde=",gammatilde;
     
  return gammatilde*c0m1char - eps;
end intrinsic;


intrinsic AbelianRepresentation(T:: ClPic) -> GalRep
{Abelian part, as a representation of inertia}
  G:=GaloisGroup(T);
  I:=InertiaGroup(T);

  C:=Clusters(T);
  A:=[c: c in C | #OddChildren(T,c) ge 3];
  if IsEmpty(A) then return CharacterRing(G)!0; end if;

  h,hG:=PermutationAction(T,A);
  hI:=h(I);
  AO:=A[[c[1]: c in Orbits(hI)]];
  
  chi:=&+[Induction(AbelianRepresentation(T,c),I): c in AO];
  return chi;
end intrinsic;

intrinsic AbelianRootNumber(T:: ClPic) -> RngIntElt
{Computes the root number corresponding to the abelian part}

  p:=ResidueCharacteristic(T);
  
  error if GCD(p,#InertiaGroup(T)) ne 1, 
    "Wild Inertia";
  if Degree(ResidueClassField(Integers(BaseField(T)))) mod 2 eq 0 then
	WAb:=1;
  else
	Ab:=Restriction(AbelianRepresentation(T),InertiaGroup(T));
	E:=[];
	for x in CharacterTable(InertiaGroup(T)) do
	  mx:=InnerProduct(x,Ab);
	  if mx ge 1 then
		for i in [1..mx] do
		  Append(~E,Order(x));
		end for;
	  end if;
	end for;

	EAb:=[];
	for x in E do
	  if [x,Multiplicity(E,x)] notin EAb then
		Append(~EAb,[x,Multiplicity(E,x)]);
	  end if;
	end for;

	WAb:=1;

	for x in EAb do
	  e,m:=Explode(x);
	  if e le 2 then
		redm:=Integers()!(m/2);
	  else
		redm:=Integers()!(m/EulerPhi(e));
	  end if;	
	  if redm mod 2 eq 0 or e eq 1 then
		continue;
	  end if;
	  if IsPrimePower(e) then
		bool,l,k:=IsPrimePower(e);
		if l ne 2 then
		  WAb:=WAb*LegendreSymbol(p,l);
		else
		  if k eq 1 then
			WAb:=WAb*LegendreSymbol(-1,p);
		  elif k eq 2 then
			WAb:=WAb*LegendreSymbol(-2,p);
		  else
			WAb:=WAb*LegendreSymbol(2,p);
		  end if;
		end if;
	  end if;
	
	  if e gt 2 and e mod 2 eq 0 then
		if IsPrimePower(Integers()!(e/2)) then
		  bool,l,k:=IsPrimePower(Integers()!(e/2));
		  if l mod 4 eq 3 then
			WAb:=WAb*LegendreSymbol(-1,p);
		  end if;
		end if;
	  end if;
	end for;
  end if;
	
  return WAb;
end intrinsic;

intrinsic RootNumber(T:: ClPic) -> RngIntElt
{Works in tame inertia}
  return AbelianRootNumber(T)*ToricRootNumber(T);
end intrinsic;

intrinsic ResidueCharacteristic(T:: ClPic) -> RngIntElt
{}
  return Characteristic(ResidueClassField(Integers(BaseField(T))));
end intrinsic;


intrinsic IsOfXType(T:: ClPic: alloweven:=false) -> BoolElt
{Top cluster with two principal children of the same parity}
  ch:=Children(T,TopCluster(T));
  return (#ch eq 2) and (#ch[1] gt 2) and (#ch[2] gt 2) and
    (IsOdd(#ch[1]) and IsOdd(#ch[2]) or
    alloweven and IsEven(#ch[1]) and IsEven(#ch[2]));
end intrinsic;


intrinsic IsSemistable(T:: ClPic) -> BoolElt
{Semistability criterion}
  I:=InertiaGroup(T);
  if GCD(#I,ResidueCharacteristic(T)) ne 1 then return false; end if;
  if IsOfXType(T) and not IsCoercible(Z,Depth(T,TopCluster(T))) then return false; end if;
  return 
    forall{c: c in PrincipalClusters(T) | IsCoercible(Z,Depth(T,c)) and IsEven(Z!Nu(T,c))} and
    #PermutationAction(T,PrincipalClusters(T))(I) eq 1;
end intrinsic;


intrinsic TamagawaNumberCl(T:: ClPic) -> RngIntElt
{}
  E:=EvenClusters(T);
  
  if IsEmpty(E) or ((#E eq 1) and (E[1] eq TopCluster(T))) then return 1; end if; 
  error if not IsSemistable(T), "Tamagawa numbers only implemented in the semistable case";
  error if Genus(T) ne 2, "Tamagawa numbers only implemented in genus 2";

  P:=ProperClusters(T);
  fs:=FrobeniusSigns(T);

  t:=[c: c in E | #c in [2,4]];        // twins and cotwins
  d:=[Z| 2*RelativeDepth(T,c,Parent(T,c)): c in t];  // 2*depth to parent

  // 6=2+4 -> remove 4 and change the depth of 2 to relative depth
  if (#Last(t) eq 4) and exists(i){i: i in [1..#t-1] | Parent(T,t[i]) eq Parent(T,Last(t))} then
    d[i]+:=Last(d);
    t:=t[[1..#t-1]];
    d:=d[[1..#t]];     
  end if;
  
  frobs:=[fs[Position(P,c)]: c in t];                // Frobenius signs
  frobt:=PermutationAction(T,t)(Frobenius(T));       // Frobenius permutation action
  o:=[Z| d[1]: d in CycleDecomposition(frobt)];      // orbit representatives
  twiddle:=func<n|IsOdd(Z!n) select 1 else 2>;
  
  if #t lt 3 then                                                       // non-ubereven 
    vprintf ClPic,2: "non-u o=%o d=%o signs=%o\n",DelSpaces(o),DelSpaces(d),DelSpaces(frobs);
    return &*[frobs[j] eq 1 select d[j] else twiddle(d[j]): j in o];    
  elif Order(frobt) eq 3 then                                           // t-t-t 
    vprintf ClPic,2: "t-t-t signs=%o",DelSpaces(frobs);
    return frobs[1] eq -1 select 1 else 3;
  elif Order(frobt) eq 2 then                                           // t-t t
    assert exists(j){j: j in {1,2,3} | j^frobt eq j}; 
    A:=j eq 1 select d[2] else d[1];
    C:=d[j];
    vprintf ClPic,2: "t-t t A=%o C=%o d=%o signs=%o\n",A,C,DelSpaces(d),DelSpaces(frobs);
    if frobs[j] eq 1 then return A+2*C; else return A; end if;
  else                                                                  // t t t
    A,B,C:=Explode(d);
    N:=A*B+B*C+A*C;
    D:=GCD([Z|A,B,C]);
    vprintf ClPic,2: "t t t A=%o B=%o C=%o N=%o D=%o signs=%o",A,B,C,N,D,DelSpaces(frobs);
    if frobs[1] eq 1 then return N; else return twiddle(N div D)*twiddle(D); end if;
  end if; 

end intrinsic;


intrinsic FormalTamagawaNumber(T:: ClPic) -> RngIntElt
{}
  E:=EvenClusters(T);
  
  if IsEmpty(E) or ((#E eq 1) and (E[1] eq TopCluster(T))) then return 1; end if; 
  error if Genus(T) ne 2, "Tamagawa numbers only implemented in genus 2";

  P:=ProperClusters(T);
  fs:=FrobeniusSigns(T);

  t:=[c: c in E | #c in [2,4]];        // twins and cotwins
  d:=[2*RelativeDepth(T,c,Parent(T,c)): c in t];  // 2*depth to parent

  // 6=2+4 -> remove 4 and change the depth of 2 to relative depth
  if (#Last(t) eq 4) and exists(i){i: i in [1..#t-1] | Parent(T,t[i]) eq Parent(T,Last(t))} then
    d[i]+:=Last(d);
    t:=t[[1..#t-1]];
    d:=d[[1..#t]];     
  end if;
  
  frobs:=[fs[Position(P,c)]: c in t];                // Frobenius signs
  frobt:=Sym(#t)![Position(t, P[Position(P,u)^T`frob] ): u in t];
                                                     // Frobenius permutation action
  o:=[Z| d[1]: d in CycleDecomposition(frobt)];      // orbit representatives
  twiddle:=func<s|"\\widetilde{"*Sprint(s)*"}">;
  
  if #t lt 3 then                                                       // non-ubereven 
    vprintf ClPic,2: "non-u o=%o d=%o signs=%o\n",DelSpaces(o),DelSpaces(d),DelSpaces(frobs);
    return &cat[frobs[j] eq 1 select Sprint(d[j]) else twiddle(d[j]): j in o];    
  elif Order(frobt) eq 3 then                                           // t-t-t 
    vprintf ClPic,2: "t-t-t signs=%o",DelSpaces(frobs);
    return frobs[1] eq -1 select 1 else 3;
  elif Order(frobt) eq 2 then                                           // t-t t
    assert exists(j){j: j in {1,2,3} | j^frobt eq j}; 
    A:=j eq 1 select d[2] else d[1];
    C:=d[j];
    vprintf ClPic,2: "t-t t A=%o C=%o d=%o signs=%o\n",A,C,DelSpaces(d),DelSpaces(frobs);
    if frobs[j] eq 1 then return A+2*C; else return A; end if;
  else                                                                  // t t t
    A,B,C:=Explode(d);
    N:=A*B+B*C+A*C;
    //D:=GCD([Z|A,B,C]);
    vprintf ClPic,2: "t t t A=%o B=%o C=%o N=%o signs=%o",A,B,C,N,DelSpaces(frobs);
    if frobs[1] eq 1 then return "N"; else return 
      twiddle("N/D")*"\\times"*twiddle("D"); end if;
  end if; 

end intrinsic;


///////////////////////////////////////////////////


function ClTreeCopy(T0) 
  T:=ClPicCreate();
  T`B:=T0`B;

  if assigned T0`C then
    T`C:=T0`C;
    T`Co:=T0`Co;
    T`Ce:=T0`Ce;
    T`Cu:=T0`Cu;
    T`g:=T0`g;
    T`N:=T0`N;
    T`Cpi:=T0`Cpi;
    T`Cpo:=T0`Cpo;
    T`Ct:=T0`Ct;
    T`ch:=T0`ch;
    T`Cg:=T0`Cg;
    T`pa:=T0`pa;
    T`g:=T0`g;
    T`balanced:=T0`balanced;
    //T`name:=T0`name;
  end if;

  return T;
end function;


intrinsic Eltseq(T::ClPic) -> List
{}
  return T`B;
end intrinsic;


intrinsic Clusters(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`C;  
end intrinsic;


intrinsic OddClusterIndices(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`Co;  
end intrinsic;


intrinsic EvenClusterIndices(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`Ce;  
end intrinsic;


intrinsic EvenClusters(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`C[T`Ce];  
end intrinsic;


intrinsic UberevenClusterIndices(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`Cu;  
end intrinsic;


intrinsic UberevenClusters(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`C[T`Cu];  
end intrinsic;


intrinsic TwinClusterIndices(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`Ct;  
end intrinsic;


intrinsic TwinClusters(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`C[T`Ct];
end intrinsic;


intrinsic ChildrenIndices(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T);
  return T`ch;  
end intrinsic;


intrinsic ParentIndex(T::ClPic, c::SeqEnum) -> RngIntElt
{}
  DefineClusters(~T);
  return T`pa[ClusterIndex(T,c)];
end intrinsic;


intrinsic Parent(T::ClPic, c::SeqEnum) -> SeqEnum
{}
  DefineClusters(~T);
  return T`C[ParentIndex(T,c)];
end intrinsic;


intrinsic ParentIndex(T::ClPic, i::RngIntElt) -> RngIntElt
{}
  DefineClusters(~T);
  requirerange i,1,#T`C;
  return T`pa[i];
end intrinsic;


intrinsic Parent(T::ClPic, i::RngIntElt) -> SeqEnum
{}
  DefineClusters(~T);
  return T`C[ParentIndex(T,i)];
end intrinsic;


intrinsic HasUberevenParent(T:: ClPic, s::SeqEnum) -> BoolElt
{true if the cluster s has a parent and it is ubereven}
  p:=ParentIndex(T,s);
  return (p ne 0) and IsUbereven(T,p);
end intrinsic;


intrinsic ChildrenIndices(T::ClPic, p::RngIntElt) -> SeqEnum
{}
  DefineClusters(~T); 
  error if (p eq 0) or (p gt #T`C), "Cluster #"*Sprint(p)*" not found in "*Sprint(T);
  return T`ch[p];
end intrinsic;


intrinsic ClusterIndex(T::ClPic, c::SeqEnum: err:=true) -> RngIntElt
{}
  DefineClusters(~T); 
  p:=Position(T`C,c);
  error if err and (p eq 0), "Cluster "*DelSpaces(c)*" not found in "*Sprint(T);
  return p;
end intrinsic;


intrinsic Cluster(T::ClPic, i::RngIntElt) -> SeqEnum
{Cluster by its index}
  DefineClusters(~T); 
  return T`C[i];
end intrinsic;


intrinsic ChildrenIndices(T::ClPic, c::SeqEnum) -> SeqEnum
{}
  DefineClusters(~T); 
  return T`ch[ClusterIndex(T,c)];
end intrinsic;


intrinsic Children(T::ClPic, c::SeqEnum) -> SeqEnum
{}
  DefineClusters(~T); 
  ch:=ChildrenIndices(T,c);
  return T`C[ch];
end intrinsic;


intrinsic Children(T::ClPic, c::RngIntElt) -> SeqEnum
{}
  DefineClusters(~T); 
  ch:=ChildrenIndices(T,c);
  return T`C[ch];
end intrinsic;


intrinsic ProperChildren(T::ClPic, c::SeqEnum) -> SeqEnum
{}
  return [u: u in Children(T,c) | IsProper(T,u)];
end intrinsic;


intrinsic OddChildren(T::ClPic, c::SeqEnum) -> SeqEnum
{}
  return [x: x in Children(T,c) | IsOdd(#x)];
end intrinsic;


intrinsic IsOdd(T:: ClPic, c::SeqEnum) -> BoolElt
{}
  return IsOdd(#c);
end intrinsic;


intrinsic IsEven(T:: ClPic, c::SeqEnum) -> BoolElt
{}
  return IsEven(#c);
end intrinsic;


intrinsic IsPrincipal(T:: ClPic, c::SeqEnum) -> BoolElt
{}
  return Position(T`C,Sort(c)) in T`Cpi;
end intrinsic;


intrinsic IsEven(T:: ClPic, c::SeqEnum) -> BoolElt
{}
  return IsEven(#c);
end intrinsic;


intrinsic IsProper(T:: ClPic, c::SeqEnum) -> BoolElt
{}
  return #c gt 1;
end intrinsic;


intrinsic IsUbereven(T:: ClPic, c::SeqEnum) -> BoolElt
{}
  return Position(T`C,Sort(c)) in T`Cu;
end intrinsic;


intrinsic IsUbereven(T:: ClPic, p::RngIntElt) -> BoolElt
{}
  DefineClusters(~T); 
  return p in T`Cu;
end intrinsic;


intrinsic ProperClusterIndices(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T); 
  return T`Cpo;
end intrinsic;


intrinsic ProperClusters(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T); 
  return T`C[T`Cpo];
end intrinsic;


intrinsic PrincipalClusters(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T); 
  return T`C[T`Cpi];
end intrinsic;


intrinsic '#'(T::ClPic) -> RngIntElt
{}
  return T`N; 
end intrinsic;


intrinsic Genus(T::ClPic) -> RngIntElt
{}
  return T`g;
end intrinsic;


intrinsic Genus(T::ClPic, c::RngIntElt) -> RngIntElt
{}
  DefineClusters(~T); 
  return T`Cg[c];
end intrinsic;


intrinsic Genus(T::ClPic, c::SeqEnum) -> RngIntElt
{}
  DefineClusters(~T); 
  return T`Cg[Position(T`C,c)];
end intrinsic;


intrinsic AbelianDimension(T::ClPic) -> RngIntElt
{}
  DefineClusters(~T); 
  return &+T`Cg;
end intrinsic;


intrinsic ToricDimension(T::ClPic) -> RngIntElt
{}
  return Genus(T)-AbelianDimension(T);
end intrinsic;


intrinsic IsBalanced(T::ClPic) -> BoolElt
{Also looks at depths}
  DefineClusters(~T);
  if assigned T`d then
    c:=[c: c in T`C | #c eq T`N/2];
    if #c eq 2 then
      check:=(Depth(T,TopCluster(T)) eq 0) and (Depth(T,c[1]) eq Depth(T,c[2]));
    else
      check:=(Depth(T,TopCluster(T)) eq 0);
    end if;
    return (T`balanced and check);
  else
    return T`balanced;
  end if;
end intrinsic;


intrinsic TopCluster(T::ClPic) -> SeqEnum
{}
  DefineClusters(~T); 
  return Last(T`C);
end intrinsic;


intrinsic ValuationMatrix(T::ClPic) -> AlgMatElt
{}
  return T`M;
end intrinsic;


intrinsic Roots(T::ClPic) -> SeqEnum
{}
  return T`r;
end intrinsic;


intrinsic Depths(T::ClPic) -> SeqEnum
{}
  return T`d;
end intrinsic;


intrinsic DefiningPolynomial(T::ClPic) -> RngUPolElt
{}
  return T`f; 
end intrinsic;


intrinsic Depth(T::ClPic, c::SeqEnum) -> .
{}
  DefineClusters(~T); 
  p:=Position(ProperClusters(T),c);
  error if (p eq 0) or (not assigned T`d), "Undefined depth for "*Sprint(c);
  return T`d[p];
end intrinsic;


intrinsic Depth(T::ClPic, i::RngIntElt) -> .
{}
  DefineClusters(~T); 
  return Depth(T,T`C[i]);
end intrinsic;


intrinsic Nu(T::ClPic, c::SeqEnum) -> .
{}
  DefineClusters(~T); 
  p:=Position(T`C[T`Cpo],c);
  error if (p eq 0) or (not assigned T`d), "Nu: Depths not assigned";
  d:=T`d[p];
  return T`vcf + d*#c + &+[Universe(T`d)|Distance(T,a,c[1]): a in [1..T`N] | a notin c];
end intrinsic;


intrinsic TopClusterIndex(T::ClPic) -> RngIntElt
{}
  DefineClusters(~T); 
  return #(T`C);
end intrinsic;


intrinsic AssignDepths(~T::ClPic, d::SeqEnum) 
{Assign depths to all proper clusters}
  DefineClusters(~T); 
  error if #T`Cpo ne #d, "Depths should be assigned for all proper (non-root) clusters";
  T`d:=d;
  T`vcf:=0;
end intrinsic;


intrinsic AssignDepths(~T::ClPic, d::SeqEnum, vcf::Any) 
{Assign depths to all proper clusters and the valuation of the leading coefficient of f}
  AssignDepths(~T,d);
  T`vcf:=vcf;
end intrinsic;


intrinsic AssignRelativeDepths(~T::ClPic, rd::SeqEnum) 
{Assign depths to all proper clusters by specifying relative depths to their parents}
  DefineClusters(~T); 
  P:=ProperClusters(T);
  error if #P ne #rd, "Depths should be assigned for all proper (non-root) clusters";
  d:=[Last(rd): i in P];       // for top cluster d=rd
  for i:=#P-1 to 1 by -1 do
    p:=Position(P,Parent(T,P[i]));
    d[i]:=rd[i] + d[p];        // for the others d=rd + d(parent), inductively
  end for;   
  T`d:=d;
  T`vcf:=0;
end intrinsic;


intrinsic LeastCommonAncestorIndex(T::ClPic, c1::SeqEnum, c2::SeqEnum) -> RngIntElt
{}
  DefineClusters(~T); 
  if c1 subset c2 then return Position(T`C,c2); end if;
  if c2 subset c1 then return Position(T`C,c1); end if;
  repeat
    c1:=Parent(T,c1);
  until c2 subset c1;
  return Position(T`C,c1); 
end intrinsic;


intrinsic LeastCommonAncestor(T::ClPic, c1::SeqEnum, c2::SeqEnum) -> SeqEnum
{}
  return T`C[LeastCommonAncestorIndex(T,c1,c2)];
end intrinsic;


intrinsic LeastCommonAncestorIndex(T::ClPic, i1::RngIntElt, i2::RngIntElt) -> RngIntElt
{}
  DefineClusters(~T); 
  return LeastCommonAncestorIndex(T,T`C[i1],T`C[i2]);
end intrinsic;


intrinsic LeastCommonAncestor(T::ClPic, i1::RngIntElt, i2::RngIntElt) -> SeqEnum
{}
  return T`C[LeastCommonAncestorIndex(T,i1,i2)];
end intrinsic;


intrinsic Distance(T::ClPic, i1::RngIntElt, i2::RngIntElt) -> RngElt
{Valuation v(C1-C2) computed with depths (that must be assigned)}
  error if not assigned T`d, "Distance: depths must be assigned";
  C1:=T`C[i1];
  C2:=T`C[i2];
  if (C1 subset C2) or (C2 subset C1) then return Infinity(); end if;
  return Depth(T,LeastCommonAncestor(T,i1,i2));
end intrinsic;


intrinsic Distance(T::ClPic, C1::SeqEnum, C2::SeqEnum) -> RngElt
{Valuation v(C1-C2) computed with depths (that must be assigned)}
  error if not assigned T`d, "Distance: depths must be assigned";
  c1:=ClusterIndex(T,C1); 
  c2:=ClusterIndex(T,C2); 
  if (C1 subset C2) or (C2 subset C1) then return Infinity(); end if;
  return Depth(T,LeastCommonAncestor(T,c1,c2));
end intrinsic;


intrinsic RelativeDepth(T::ClPic, c1::SeqEnum, c2::SeqEnum) -> RngElt
{Relative depth (distance in the BY tree)}
  c:=LeastCommonAncestor(T,c1,c2);
  return (Depth(T,c1)-Depth(T,c))+(Depth(T,c2)-Depth(T,c));
end intrinsic;


intrinsic RelativeDepth(T::ClPic, i1::RngIntElt, i2::RngIntElt) -> RngElt
{Relative depth (distance in the BY tree)}
  c:=LeastCommonAncestor(T,i1,i2);
  return (Depth(T,i1)-Depth(T,c))+(Depth(T,i2)-Depth(T,c));
end intrinsic;


intrinsic RelativeDepth(T::ClPic, c1::SeqEnum, c2::SeqEnum) -> RngElt
{Relative depth (distance in the BY tree)}
  c:=LeastCommonAncestor(T,c1,c2);
  return (Depth(T,c1)-Depth(T,c))+(Depth(T,c2)-Depth(T,c));
end intrinsic;


intrinsic ClusterToList(T::ClPic, c::SeqEnum) -> .
{}
  if #c eq 1 
    then return c[1]; 
    else return [* ClusterToList(T,u): u in Children(T,c) *];
  end if;
end intrinsic;

intrinsic OddtoEven(T::ClPic) -> ClPic
{Even degree cluster picture}
  if IsEven(T`N) then return T; end if;
  
  B:=Append(ClusterToList(T,TopCluster(T)),T`N+1);
  B:=SortList(B);
  S:=ClusterPicture(B);
  DefineClusters(~S);

  if assigned T`d then
    if assigned T`vcf then
      AssignDepths(~S,T`d,T`vcf);
    else AssignDepths(~S,T`d); end if;
  end if;

  return S;
end intrinsic;

intrinsic Cocluster(T::ClPic) -> ClPic
{Replace cluster of size N>2 with cocluster if N even}
  N:=T`N;
  c:=[c: c in Clusters(T) | #c gt N/2];
  if (#c eq 1 or IsOdd(N)) then return T; end if;
  
  c:=c[#c -1];  								// deal with largest first
  B:=[* ClusterToList(T,h) : h in Children(T,c) *];
  A:=[* ClusterToList(T,h) : h in Children(T,TopCluster(T)) | h ne c *];
  if #A eq 1 then A:=A[1]; end if;  
  
  B:=B cat [*A*];
  B:=SortList(B);
  S:=ClusterPicture(B);

  if assigned T`d then
    d:=[];
    m:=RelativeDepth(T,c);

    for s in ProperClusters(S) do
      if s eq TopCluster(S) then
        Append(~d,Depth(T,s));
      elif s in ProperClusters(T) and (s subset c) then
	     Append(~d,Depth(T,s)-m);
	   elif s in ProperClusters(T) then
	     Append(~d,Depth(T,s)+m);
	   else
 	     Append(~d,m);
	   end if;
    end for;
      
    if assigned T`vcf then
      AssignDepths(~S,d,T`vcf);
    else AssignDepths(~S,d); end if;
  end if;

  return S;
end intrinsic;

intrinsic Balance(T::ClPic) -> ClPic
{Transform a cluster tree to the canonical balanced form}
  T:=OddtoEven(T);
  N:=T`N;
  if IsBalanced(T) then return T; end if;
  
  c:=[c: c in Clusters(T) | #c gt N/2];
  while #c ne 1 do  								// if cluster of size > N/2
    T:=Cocluster(T);
    c:=[c: c in Clusters(T) | #c gt N/2];
  end while;
  
  S:=T;    
  c:=[c: c in T`C | #c eq N/2];
  if IsOdd(#c) then									// one of size N/2
    c:=c[1];
    A:=[* ClusterToList(T,h) : h in Children(T,TopCluster(T)) | h ne c *];
    B:=[* ClusterToList(T,c) *] cat [* A *];
    B:=SortList(B);
    S:=ClusterPicture(B);

    if assigned T`d then
      d:=[];
      m:=RelativeDepth(T,c)/2;

      for s in ProperClusters(S) do
        if s eq TopCluster(S) then
          Append(~d,Depth(T,s));
        elif s in ProperClusters(T) and (s subset c) then
	  Append(~d,Depth(T,s)-m);
	elif s in ProperClusters(T)then
	  Append(~d,Depth(T,s)+m);
	else
 	  Append(~d,m);
	end if;
      end for;
      
      if assigned T`vcf then
        AssignDepths(~S,d,T`vcf);
      else AssignDepths(~S,d); end if;
    end if;
  elif #c eq 2 and assigned T`d and (Depth(T,c[1]) ne Depth(T,c[2])) then  		// shift so two depths are equal
    B:=S`B;
    m:=(Depth(T,c[2])-Depth(T,c[1]))/2;
    d:=[];
    for s in ProperClusters(S) do
      if s eq TopCluster(S) then
        Append(~d,Depth(T,s));
      elif s subset c[1] then
        Append(~d,Depth(T,s)+m);
      else
	Append(~d,Depth(T,s)-m);
      end if;
    end for;
    S:=ClusterPicture(B);
    if assigned T`vcf then
      AssignDepths(~S,d,T`vcf);
    else AssignDepths(~S,d); end if;
  end if;
  
  if assigned T`d then 		// shift so top cluster has depth 0
    B:=S`B;
    d:=[];
    for a in S`d do
      Append(~d,a-Depth(S,TopCluster(S)));
    end for;
    S:=ClusterPicture(B);
    AssignDepths(~S,d,T`vcf);
  end if;

  return S;
end intrinsic;

intrinsic OldBalance(T::ClPic) -> ClPic
{Transform a cluster tree to the canonical balanced form}
  if IsBalanced(T) then return T; end if;
  C:=T`C;
  N:=T`N;

  c:=[c: c in C | #c ge N/2][1];                    // new top cluster

  function b(u)
    if u eq TopCluster(T) then 
      ch:=[* ClusterToList(T,h): h in Children(T,u) | not (c subset h) *];
      if IsOdd(N) then Append(~ch,N+1); end if;
      if #ch eq 1 then ch:=ch[1]; end if;
      return ch;
    end if;
    ch:=[* ClusterToList(T,h): h in Children(T,u) | not (c subset h) *];
    Append(~ch,b(Parent(T,u)));
    return ch;
  end function;
  
  if #c eq N/2 
    then B:=[* ClusterToList(T,c),b(Parent(T,c)) *];                // one of size N/2
    else B:=Append(ClusterToList(T,c),b(Parent(T,c)));              // all other cases
  end if;
  
  B:=SortList(B);

  p:=Flatten(B: sort:=false);                  // permutation
  n:=#p;
  p:=(Sym(n)!p)^(-1);
  //"  c>",c;
  //"per>",p;
  //"new>",B;
  
  SetClPicEntries(~B,[1..n]);
  S:=ClusterPicture(B);
  DefineClusters(~S);
                                              // new depths 
  //"old>",T;
  //"srt>",S;
  if assigned T`d then
    d:=[Universe(T`d)| 0: i in ProperClusterIndices(S)];
    dc:=Depth(T,c);
    for u0 in ProperClusters(T) do  
      if (#u0 eq T`N) and (#Children(T,u0)) eq 2 then continue; end if;   // top = c1 union c2
      u:=u0;
      d0:=Depth(T,u0);
      if u eq c then u:=[1..n];               // c -> new top
      elif u subset c then ;                  // u<c proper -> untouched
      elif exists(z){z: z in Children(T,u) | c subset z} then
           u:=[x: x in [1..n] | x notin z];   // u>c proper -> complement to
                                              //   the child containing c
      else ;                                  // untouched   
      end if;                                 
      r:=Sort(u^p);
      j:=Position(ProperClusters(S),r);
      if j eq 0 then continue; end if;
      //error if j eq 0, "Balance: could not find the corresponding cluster in the balanced tree";
      error if d[j] ne 0, Sprintf("Balance: depth already assigned");
      d[j]:=dc+RelativeDepth(T,c,u0);
      //">>",DelSpaces(c),DelSpaces(u0),DelSpaces(dc),DelSpaces(RelativeDepth(T,c,u0)),"->",d[j];
      //Sprintf("%-30o %-30o %o",DelSpaces(u0)*" "*Sprint(d0),DelSpaces(r),j);
    end for;
    S`d:=d;
  end if;
     
  return S;
end intrinsic;


intrinsic FrobeniusOrbitsOnClusters(T::ClPic, ch::SeqEnum) -> SeqEnum, SeqEnum, SeqEnum
{Frobenius orbits on a list of clusters; returns orbit representatives, orbits sizes and orbit signs}
  error if not assigned T`frob, "Frobenius is not assigned";
  //if Order(T`frob) eq 1 then return ch,[1: c in ch]; end if;
  cyc:=CycleDecomposition(T`frob);  
  O:=[SortSet(Set(ch) meet Set(c)): c in cyc];
  O:=[o: o in O | #o ne 0];
  S:=FrobeniusSigns(T);
  return [o[1]: o in O], [#o: o in O], [&*[S[j]: j in o]: o in O];
end intrinsic;


intrinsic FrobeniusSigns(T::ClPic) -> SeqEnum
{}
  error if not assigned T`frob, "FrobeniusSigns: Frobenius not assigned yet";
  P:=T`Cpo;
  s:=T`frobsigns;
  for i:=#s-1 to 1 by -1 do
    c:=T`C[P[i]];
    if (s[i] eq 0) and IsEven(#c) then 
      if HasUberevenParent(T,c) 
        then s[i]:=s[Position(P,T`pa[P[i]])];
        else s[i]:=+1;
      end if;
    end if;
  end for;
  return s;
end intrinsic;


intrinsic EulerFactor(T::ClPic) -> RngUPolElt 
{Euler factor of the toric part of a cluster picture} 
  if ToricRepresentation(T) ne T`A!!(CharacterRing(GaloisGroup(T))!0) then
    return EulerFactor(ToricRepresentation(T));
  else
	R<x>:=PolynomialRing(Rationals());
	return Identity(R);
  end if;
 
  /*    
  // works for semistable ones
  P:=ProperClusters(T);
  PNU:=[i: i in [1..#P] | IsEven(T,P[i]) and not HasUberevenParent(T,P[i])];
  FO,FN,FS:=FrobeniusOrbitsOnClusters(T,PNU);
  R<X>:=PR(Q);
  f:=&*[R|1+FS[i]*X^FN[i]: i in [1..#FO]];
  return f;  
  */

  /*
  // old - obsolete
  s:=FrobeniusSigns(T);
  P:=T`Cpo;
  U:=T`Cu;
  cyc:=CycleDecomposition(T`frob);
  c:=[Position(T`froborbit,i): i in [1..#cyc]];
  R<X>:=PR(Q);

  f:=&*[R|1-s[c[1]]*X^#c: c in cyc | P[c[1]] notin U];
    // contribution from each orbit of even non-ubereven clusters
  top:=(1-s[#P]*X);
  loc:=f div top;          // divided by one from the top cluster 
  error if f ne loc*top,
    "Error in EulerFactor for "*Sprint(T);
  */

  /* 
  for c in cyc do 
    if P[c[1]] notin U then
      ">>*",Sprint(1-(s[c[1]]*X)^#c);
    end if;
  end for;
  ">>/"*Sprint(1-s[#P]*X);
  "-->",Sprint(loc);
  */
  
 // return loc; 
end intrinsic;


childlinksym:=func<u|IsEven(#u) select ":" else ".">;
XSymbol:=func<n|IsEven(n) select "o" else "x">;
brck:=func<s|#s gt 1 select "{"*s*"}" else s>;


intrinsic RelativeDepth(T::ClPic, c::SeqEnum) -> RngElt
{Depth to the parent of a cluster c}
  if c eq TopCluster(T) then return Depth(T,c); end if;
  return Depth(T,c) - Depth(T,Parent(T,c));
end intrinsic;


intrinsic ProperClusterIndex(T::ClPic, c::SeqEnum) -> RngIntElt
{Index of c in ProperClusters(T)}
  i:=Position(ProperClusters(T),c);
  error if i eq 0, DelSpaces(c)*" not found in proper clusters";
  return i;
end intrinsic;


intrinsic IsFirstInOrbit(T::ClPic, c::SeqEnum) -> BoolElt, SeqEnum
{Is first in a Frobenius orbit on proper clusters. Returns true/false and the first j 
    for which ProperClusters(T)[j] is in the orbit of c}
  i:=ProperClusterIndex(T,c);
  j:=Min([j: j in [1..i] | T`froborbit[j] eq T`froborbit[i]]);
  return j eq i, j;
end intrinsic;


intrinsic IsLastInOrbit(T::ClPic, c::SeqEnum) -> BoolElt
{Is last in a Frobenius orbit on proper clusters}
  i:=ProperClusterIndex(T,c);
  return forall{j: j in [i+1..#T`Cpo] | T`froborbit[j] ne T`froborbit[i]};
end intrinsic;


function sgnsymbol(x)
  if   x gt 0 then return "+";
  elif x lt 0 then return "-";
  else return "";    
  end if;
end function;


function NameMain(T,c,top,d,open) 

  twins:=TwinClusters(T);
  twinletters:="nmklrstabcdxyz";
  PC:=ProperClusters(T);

  function depth(u) 
    if d and (u in PC) then return Sprint(2*RelativeDepth(T,u)); end if;
    pt:=Position(twins,u);
    return pt eq 0 select "" else twinletters[pt];
  end function;
   
  function depthsym(u)
    s:=depth(u);
    return sif(#s gt 0,"_"*s);
  end function;

  function childlinksym(u: x:=false)
    return sif(not x,IsEven(#u) select ":" else ".");
  end function;

  genus:=Genus(T,c);
  ch:=Children(T,c);

  chp:=[u: u in ch | #u gt 2];
  cht:=[u: u in ch | #u eq 2];

  xtype:=(c eq Last(T`C)) and IsOfXType(T: alloweven) and not open and (Genus(T) gt 1);
  s:=xtype 
    select XSymbol(#Children(T,c)[1])                           // x/o
    else Sprint(genus);                                         // every other type
  if IsEmpty(chp cat cht) then return s; end if;
  if IsEmpty(chp) and not IsEmpty(cht) and not xtype and (genus eq 0) then s:="I"; end if;

  twinstr:=IsEmpty(cht) select "" else 
    "_"*brck(Prune(&cat[depth(u)*",": u in cht]));

  if xtype then                                                      // x
    s:=childlinksym(chp[1]: x)*NameMain(T,chp[1],true,d,false) 
         * s * 
       childlinksym(chp[2]: x)*NameMain(T,chp[2],true,d,false);
  elif exists{x: x in ch | IsOdd(#x)} then                           // non-ubereven
    s:=s*twinstr*&cat[Parent("")|childlinksym(u)*NameMain(T,u,false,d,false) : u in chp];  
  else                                                               // ubereven
    s:="U"*twinstr* &cat[Parent("")|childlinksym(u)*NameMain(T,u,false,d,false) : u in chp];            
  end if;

  return top or IsEmpty(chp) select s else "("*s*")"; 
end function;


function FrobeniusNameMain(T: open:=false, d:=true)

  twins:=TwinClusters(T);
  twinletters:="nmrstklabcdxyz";
  P:=ProperClusters(T);    // ordered by size
  
  FO,_,FS:=FrobeniusOrbitsOnClusters(T,[1..#P]);
  frobsigns:=[i in FO select sgnsymbol(FS[Position(FO,i)]) else "": i in [1..#P]];
  
  function depth(u) 
    if d and (u in P) then return Sprint(2*RelativeDepth(T,u)); end if;
    pt:=Position(twins,u);
    return pt eq 0 select "" else twinletters[pt];
  end function;
  
  function depthsym(u)
    return sif(#s gt 0,"_"*s) where s is depth(u);
  end function;
  
  plainnames:=[];          // ["I_n",...]
  frobnames:=[];           // ["I_n^+",...]
  
  for i:=1 to #P do
  
    c:=P[i];
    first,j:=IsFirstInOrbit(T,c);
    if not first then 
      frobnames[i]:=plainnames[j]; continue;
    end if;
  
    // Proper and twin children of the cluster c=P[i]
    
    ch:=Children(T,c);
    chp:=[u: u in ch | #u gt 2];  // proper non-twins
    cht:=[u: u in ch | #u eq 2];  // twins
  
    subs:=[];    // subscripts     e.g [0,1] for U_{0,1}^+:I_4     (from twins)
    chs:=[];     // children           [I_4]                       (from proper non-twins)
    sups:=[];    // superscripts       [+]
  
    // s := symbol for the cluster - 1,2,...,I,U,x,o
        
    genus:=Genus(T,c);
    xtype:=(i eq #P) and IsOfXType(T: alloweven) and not open and (Genus(T) gt 1);
    xeventype:=xtype and not IsOfXType(T: alloweven:=false);
    if xtype then
      s:=XSymbol(#Children(T,c)[1]);                           // x/o
    elif IsUbereven(T,c) then
      s:="U";                                                  // U
      if not HasUberevenParent(T,c) then 
        Append(~sups,frobsigns[i]);                            // possibly with +,-
      end if;
    elif IsEmpty(chp) and not IsEmpty(cht) and (genus eq 0) then 
      s:="I";                                                  // I
    else  
      s:=Sprint(genus);                                        // 0,1,2,...
    end if;
    
    for twin in [false,true] do
    C:=twin select cht else chp;
    for ch in C do
      k:=Position(P,ch);
      if not IsFirstInOrbit(T,ch) then continue; end if;
      o:=#{u: u in C | j eq k where _,j is IsFirstInOrbit(T,u)};
      if xtype then xorbit:=o; o:=1; end if;
      link:=sif(not xtype,childlinksym(ch));
      firstname:=twin select depth(ch) else link*frobnames[k];
      nextnames:=twin select depth(ch) else link*plainnames[k];
      orbitname:=firstname;
      for l:=1 to o-1 do orbitname*:="~"*nextnames; end for;
      if twin then Append(~subs,orbitname); else Append(~chs,orbitname); end if;
      if not IsUbereven(T,c) and frobsigns[k] ne "" then 
        Append(~sups,frobsigns[k]);
      end if;
    end for;
    end for;
  
    subs:=brck(PrintSequence(subs: sep:=","));
      subs:=sif(#subs gt 0,"_"*subs);
    sups:=brck(PrintSequence(sups: sep:=","));
      sups:=sif(#sups gt 0,"^"*sups);
   
    if xtype then 
      xevensgn:=sif(xeventype,"^"*frobsigns[i]);
      if xorbit eq 2 
        then frobnames[i]:=chs[1] * "~" * s * xevensgn * plainnames[#P-2];
        else frobnames[i]:=chs[1] * s * xevensgn * chs[2];
      end if;
    else
      br:=not IsEmpty(chp) and (i ne #P);
      obr:=br select "(" else "";
      cbr:=br select ")" else "";
      
      plainnames[i]:=obr* s * subs * PrintSequence(chs: sep:="") *cbr;
      frobnames[i]:=obr* s * subs * sups * PrintSequence(chs: sep:="") *cbr;
    end if;    
    
  end for;
  
  return Last(frobnames);

end function;


intrinsic Name(T:: ClPic: tex:=false, d:=true, open:=false, frob:=false) -> MonStgElt
{}
  DefineClusters(~T);
  d:=d and assigned T`d;
  frob:=frob and assigned T`frob;

  if frob  
    then s:=FrobeniusNameMain(T: d:=d,open:=open);
    else s:=NameMain(T,Last(T`C),true,d,open);
  end if;
  
  //br:=open and Count(s,".")+Count(s,":") ne 0; 
  br:=false; //???
  
  if br then s:="("*s*")"; end if;
  s:=sif(open,childlinksym(T))*s;
  if not tex then 
    return ReplaceStringFunc(s,["~.","~:"],["~","~"]);
  end if;
  return "\\hetype{"*ReplaceStringFunc(s,
    ["~o","~x","~.","~:","~"],
    ["\\FrobO ","\\FrobX ","\\FrobDot ","\\FrobCol ","\\FrobL "])*"}";
end intrinsic;


intrinsic FrobeniusName(T:: ClPic) -> MonStgElt
{}
  if assigned T`frobname then return T`frobname; end if;
  if not assigned T`frob then return Name(T); end if;
  T`frobname:=Name(T: frob);
  return T`frobname;
end intrinsic;


intrinsic FrobeniusTeXName(T:: ClPic) -> MonStgElt
{}
  if assigned T`frobtexname then return T`frobtexname; end if;
  if not assigned T`frob then return Name(T: tex); end if;
  T`frobtexname:=Name(T: frob,tex);
  return T`frobtexname;
end intrinsic;


///////////////////////////////////////////////////


function shift(b,n)
  if Type(b) eq RngIntElt then return b+n; end if;
  return [* shift(x,n): x in b *];
end function;


intrinsic ClusterPicturesOfDegree(N:: RngIntElt: balanced:=false) -> SeqEnum[ClPic] 
{}
// number of series-reduced planted trees; OEIS: A000669

  if N eq 1 then return [ClusterPicture([*1*])]; end if;

  B:=[* [**]: i in [1..N] *];      
  
  function ClTrees(n) 
    if n eq 1 then return [*1*]; end if;
    if #B[n] ne 0 then return B[n]; end if;
    res:=[];
    for P0 in Partitions(n) do
      P:=Reverse(P0);
      m:=#P;
      if m eq 1 then continue; end if;
      L:=[* ClTrees(c): c in P *];
      for i:=1 to m do 
        L[i]:=shift(L[i],&+[Z|P[j]: j in [1..i-1]]);
      end for;
      I:=[[1..#b]: b in L];
      for i in CartesianProduct(I) do
        ok:=true;
        for j:=1 to m-1 do
        if (P[j] eq P[j+1]) and (i[j] gt i[j+1]) then
          ok:=false; break;
        end if;
        end for;
        if not ok then continue; end if;
        X:=[* L[j][i[j]]: j in [1..m] *];
        Append(~res,X);
      end for;
    end for;
    return Reverse(res);
  end function;
  
  for i:=1 to N do
    B[i]:=ClTrees(i);
    vprint ClPic, 1: Sprintf("#B(%o) = %-2o",i,#B[i]);
  end for;
  
  list:=[ClusterPicture(b): b in B[N]];
  if balanced then list:=[b: b in list | IsBalanced(b)]; end if;
  return list;

end intrinsic;


intrinsic ClusterPicture(N:: RngIntElt, s:MonStgElt) -> ClPic
{Cluster picture of a given size with a given name}
  found:=false;
  for T in ClusterPicturesOfDegree(N) do
    if Name(T) eq s then 
      found:=true; F:=ClusterPicture(T`B); break;
    end if;
  end for; 
  error if not found, "Name "*s*" not found in degree "*Sprint(N);
  return F;
end intrinsic;


function ClusterPictureSamplePolynomial(b,p: typ:=3)    // Sample polynomial of a given Bosch type
  assert typ in [1..3];
  if Type(b) eq RngIntElt then return x; end if;
  if (#b eq 2) and (Type(b[1]) eq RngIntElt) and (Type(b[2]) eq RngIntElt) then
    return x^2-1/p; 
  end if;
  if typ eq 1 then
    return &*[p^Degree(f)*Evaluate(f,(x-(i-1))/p) where f is ClusterPictureSamplePolynomial(b[i],p): i in [1..#b]];  
  elif typ eq 2 then
    return &*[p^(2*Degree(f))*Evaluate(f,(x-(i-1))/p^2) where f is ClusterPictureSamplePolynomial(b[i],p): i in [1..#b]];  
  else
    return &*[IsEven(Degree(f)) 
      select p^Degree(f)*Evaluate(f,(x-(i-1))/p)
      else p^(2*Degree(f))*Evaluate(f,(x-(i-1))/p^2) 
      where f is ClusterPictureSamplePolynomial(b[i],p): i in [1..#b]];  
   end if;
end function;


///////////////////////////////////////////////////
// Cluster pictures and graphs                   //
///////////////////////////////////////////////////


procedure ClusterPictureTeXAdd(b,~x,~name,~clcount,~out,~named: links:=[], 
    label:=func<c|"","">,rootname:=func<n|"default">,rootstep:=0.3,clusterstep:=0.1,preclusterstep:=rootstep,firstchild:=true)
  if Type(b) eq RngIntElt then
    name:="r"*Sprint(b);
    s:=rootname(b);
    if s eq "default"     
      then out*:=Sprintf("  \\Root(%o,2)(%o);\n",RealField(3)!x,name);   
      else out*:=Sprintf("  \\RootT(%o,2)(%o){%o};\n",RealField(3)!x,name,s);   
    end if;
    x+:=rootstep;
    named:=false;
  else 
    children:="";
    cllinks:=[];
    if not firstchild then x+:=preclusterstep; end if;
    first:=0;
    firstname:="";
    for i:=1 to #b do
      //D:=b[#b+1-i];
      D:=b[i];
      chnamed:=true;
      addcllink:=false;
      changefirst:=false;
      if not IsEmpty(links) then 
        fd:=Flatten(D);
        ignore:=[];
        if (first cmpne 0) and exists(ignore){l: l in links | (first in l) and (fd in l)} then 
          addcllink:=true; first:=0;
        end if;
        if (first cmpeq 0) and exists{l: l in links | (fd in l) and (l ne ignore)} then 
          first:=fd; 
          changefirst:=true; chnamed:=false; 
        end if;
      end if;
      ClusterPictureTeXAdd(D,~x,~nchild,~clcount,~out,~chnamed: links:=links, label:=label, 
        rootstep:=rootstep, clusterstep:=clusterstep, preclusterstep:=preclusterstep, rootname:=rootname, firstchild:=i eq 1);
      children*:=Sprintf("(%o)",nchild);
      if chnamed then children*:=Sprintf("(%on)",nchild); end if;
      if addcllink then 
        Append(~cllinks,[firstname,nchild]); 
      end if;  
      if changefirst then 
        firstname:=nchild;
      end if;
    end for;
    clcount+:=1;

    name:="c"*Sprint(clcount);
    lab,sgn:=label(b);
    if (lab cmpne "") or (sgn cmpne "") 
      then if Type(lab) ne MonStgElt and Position(Sprint(lab),"/2") ne 0 then 
             lab:=Sprintf("\\frac{%o}{%o}",Sprint(2*lab),2);
           end if;
           out*:=Sprintf("  \\ClusterDS(%o){%o}{%o}{%o};\n",name,children,lab,sgn); named:=true;
      else out*:=Sprintf("  \\Cluster(%o){%o};\n",name,children); named:=false;
    end if;   
   
    for cl in cllinks do 
      l1,l2:=Explode(cl);
      out*:=Sprintf("  \\frob(%o)(%o);\n",l1,l2);          
    end for;

    x+:=clusterstep;
  end if;  
end procedure;


intrinsic ClusterPictureTeX(T::ClPic: header:=true, scale:="0.95",dprint:=func<s|Sprint(s)>,rootname:=func<n|"default">,
  rootstep:=0.25,clusterstep:=0.16,preclusterstep:=rootstep,PrintZeroDepth:=true) -> MonStgElt
{}
  DefineClusters(~T);
  
  clcount:=0;
  x:=10*rootstep;
  out:=header select "\\clusterpicture["*scale*"]\n" else "";
  links:=assigned T`frob select [[T`C[l[1]],T`C[l[2]]]: l in T`froblinks] else [];
  P:=T`C[T`Cpo];

  function label(b)
    f:=Flatten(b);
    p:=Position(P,f);
    d:=(p ne 0) and (assigned T`d) and ((RelativeDepth(T,f) ne 0) or PrintZeroDepth)
      select RelativeDepth(T,f) else "";
    s:=assigned T`frobsigns select sgnsymbol(T`frobsigns[p]) else "";
    return d,s;
  end function;
 
  d:=assigned T`d select [<T`C[T`Cpo[i]],T`d[i]>: i in [1..#T`Cpo] ] else [];
  named:=true;
  ClusterPictureTeXAdd(T`B,~x,~name,~clcount,~out,~named: links:=links, 
    label:=label, rootstep:=rootstep, clusterstep:=clusterstep, rootname:=rootname, preclusterstep:=preclusterstep);
  out*:=header select "\\endclusterpicture" else "";
  return out;
end intrinsic;


procedure ClusterPictureTeXNewAdd(B,b,~name,~namefrob,~clcount,~out,~lastcluster: links:=[], 
    label:=func<c|"","">,rootname:=func<n|"default">,firstchild:=true)
  if Type(b) eq RngIntElt then
    opencount:=0;
    if #B ne 1 then
      c:=Parent(B,b);
      while b-1 notin c do      // Number of clusters that b opens
        opencount+:=1;
        if #c eq #B then break; end if;
        c:=Parent(B,c); 
      end while;    
      if (b ne 1) and (opencount eq 0) and ([b-1] notin Children(B,c)) then
        opencount+:=1;           // +1 if b-1 closes a cluster
      end if;
    end if;
    step:=opencount eq 0 select "" else Sprint(opencount);
    name:="r"*Sprint(b);
    namefrob:=name;
    s:=rootname(b);
    if s eq "default"     
      then out*:=Sprintf("  \\Root {%o} {%o} {%o};\n",step,lastcluster,name);   
      else out*:=Sprintf("  \\RootT {%o} {%o} {%o} {%o};\n",step,lastcluster,name,s);   
    end if;
    lastcluster:=name;
  else 
    children:="";
    cllinks:=[];
    first:=0;
    firstname:="";
    for i:=1 to #b do
      D:=b[i];
      addcllink:=false;
      changefirst:=false;
      if not IsEmpty(links) then 
        fd:=Flatten(D);
        ignore:=[];
        if (first cmpne 0) and exists(ignore){l: l in links | (first in l) and (fd in l)} then 
          addcllink:=true; first:=0;
        end if;
        if (first cmpeq 0) and exists{l: l in links | (fd in l) and (l ne ignore)} then 
          first:=fd; changefirst:=true; 
        end if;
      end if;
      ClusterPictureTeXNewAdd(B,D,~nchild,~nchildfrob,~clcount,~out,~lastcluster: links:=links, label:=label, 
        rootname:=rootname, firstchild:=i eq 1);
      children*:=Sprintf("(%o)",nchild);
      if addcllink then 
        Append(~cllinks,[firstname,nchild]); 
      end if;  
      if changefirst then 
        firstname:=nchildfrob;
      end if;
    end for;
    clcount+:=1;

    name:="c"*Sprint(clcount);
    namefrob:=name;
    lastcluster:=name;
    lab,sgn:=label(b);
    if (lab cmpne "") or (sgn cmpne "") 
      then if Type(lab) ne MonStgElt and Position(Sprint(lab),"/2") ne 0 then 
             lab:=Sprintf("\\frac{%o}{%o}",Sprint(2*lab),2);
           end if;
           out*:=Sprintf("  \\ClusterLD %o[%o][%o] = %o;\n",name,sgn,lab,children); 
           namefrob*:="t";
      else out*:=Sprintf("  \\Cluster %o = %o;\n",name,children); 
    end if;   
   
    for cl in cllinks do 
      l1,l2:=Explode(cl);
      out*:=Sprintf("  \\frob(%o)(%o);\n",l1,l2);          
    end for;

  end if;  
end procedure;


intrinsic ClusterPictureTeXNew(T::ClPic: dprint:=func<s|Sprint(s)>,rootname:=func<n|"default">,
  PrintZeroDepth:=true, header:=true) -> MonStgElt
{}
  DefineClusters(~T);
  
  clcount:=0;
  out:=header select "\\clusterpicture\n" else "";
  links:=assigned T`frob select [[T`C[l[1]],T`C[l[2]]]: l in T`froblinks] else [];
  P:=T`C[T`Cpo];

  function label(b)
    f:=Flatten(b);
    p:=Position(P,f);
    d:=(p ne 0) and (assigned T`d) and ((RelativeDepth(T,f) ne 0) or PrintZeroDepth)
      select RelativeDepth(T,f) else "";
    s:=assigned T`frobsigns select sgnsymbol(T`frobsigns[p]) else "";
    return d,s;
  end function;
 
  d:=assigned T`d select [<T`C[T`Cpo[i]],T`d[i]>: i in [1..#T`Cpo] ] else [];
  lastcluster:="first";
  ClusterPictureTeXNewAdd(T,T`B,~name,~namefrob,~clcount,~out,~lastcluster: links:=links, label:=label, rootname:=rootname);
  out*:=header select "\\endclusterpicture" else "";
  return out;
end intrinsic;


procedure ClusterGraphMain(T,c,~i,~s: top:="n", parent:=0, ofs:=0.4, scale:="0.85", yofs:="0.5")
  if top eq "n" then s:=Sprintf("\\clusterpicture[%o]\n",scale); end if;
  C:=Clusters(T); 
  ch:=Children(T,c);
  ch:=(#T gt 1) select Children(T,c) else C;
  u:=not exists{x: x in ch | IsOdd(#x)};
  sym:=u select "u" else (IsOdd(#c) or (top eq "u") select "o" else "e");
  i+:=1;
  s*:=top eq "n" 
    select Sprintf("  \\t%ocluster(6,0)(c%o){%o}\n",sym,i,yofs)
      else Sprintf("  \\subcluster %o c%o-c%o (%o,%o)\n",sym,parent,i,RealField(2)!ofs,yofs);
  cur:=i;
  ofs:=0.4;
  for x in ch do
    if #x eq 1 then s*:=Sprintf("    \\subroot c%o-r%o {0.4}\n",cur,x[1],RealField(2)!ofs); 
                    ofs:=0.4;
               else ClusterGraphMain(T,x,~i,~s: top:=sym, parent:=cur, ofs:=ofs, scale:=scale, yofs:=yofs);  
                    ofs:=0.75*#{u: u in C | (#u ne 1) and (u subset x)}+0.4*#x;
    end if;
  end for;
  s*:=Sprintf("  \\endcluster c%o {0.45}\n",cur);
  if top eq "n" then s*:="\\endclusterpicture"; end if;
end procedure;


intrinsic ClusterGraph(T::ClPic: ofs:=0.4, scale:="0.85", yofs:="0.5") -> MonStgElt
{}
  i:=0;
  ClusterGraphMain(T,[1..#T],~i,~clg: ofs:=ofs, scale:=scale, yofs:=yofs);
  return clg;
end intrinsic;


intrinsic TeXCluster(filename::MonStgElt, T::ClPic: ofs:=0.4, clustersep:="1.5pt", 
  graphscale:="0.85", picscale:="0.95", header:=true, footer:=true, con:=false)
{}
  if header then 
    write(filename,Sprintf("\\documentclass[11pt]{amsart}\n\\usepackage{texmac}\n"*
    "\\usepackage{semmac}\n\\oddsidemargin 0pt\n\\evensidemargin 0pt\n"*
    "\\advance\\textwidth by 3cm\n\\def\\clustersep{%o}\n\\begin{document}\n",clustersep):
    con:=con, rewrite);
  end if;

  cname:=FrobeniusTeXName(T);
  clg:=ClusterGraph(T: ofs:=ofs, scale:=graphscale);
  pic:=ClusterPictureTeX(T: scale:=picscale);
  cnamestr:=Sprintf("\\hfill\\raise10pt\\hbox{%o}\n",cname);
  write(filename,"\\smallskip\n"*pic*"\\hfill"*clg*cnamestr*"\n\\smallskip\n": con:=con);

  if footer then 
    write(filename,"\\end{document}": con:=con);
  end if;

end intrinsic; 


///////////////////////////////////////////////////
// Frobenius links                               //
///////////////////////////////////////////////////


intrinsic AllFrobeniusLinks(T:: ClPic) -> SeqEnum
{All possible ways to link clusters in T with Frobenius}

  C:=Clusters(T);
  Cu:=UberevenClusterIndices(T);
  N:=2*Genus(T)+2;
  G:=Sym(N);
  pa:=T`pa;                                  // parents

  H:=G;                                      // Stabiliser of the cluster picture
  for m in [2..N-1] do
    Cm:=[c: c in C | #c eq m];
    if IsEmpty(Cm) then continue; end if;
    Sm:=sub<G|[Stabiliser(G,[i: i in [1..N] | i notin c]): c in Cm]>;
    Nm:=Normaliser(G,Sm);
    H:=H meet Nm;
  end for;
  
  P:=ProperClusters(T);            // action on proper clusters
  CS:=[Set(c): c in P]; 
  h:=hom<H->Sym(#CS)|h:->[Position(CS,c^h): c in CS]>;    
  A:=Image(h);
  
  O:=[SortSet(o): o in Orbits(A)];
  AElts:=[a: a in A];
  Adm:=[true: a in A];
  Links:=[[]: a in A];
  
  for ai:=1 to #A do               // admissible Frobenius elements (canonical cycle type)
    a:=AElts[ai];
    orbits:=[SetToSequence(Set(o)): o in CycleDecomposition(a) | #o gt 1];
    for pi:=1 to #P do
      if pi ne pi^a then continue; end if;     // a does not stabilise the cluster
      p:=P[pi];
      ch:=[Position(P,c): c in Children(T,p) | #c gt 1];
      if IsEmpty(ch) then continue; end if;
      for o in O do
        och:=SortSet(Set(o) meet Set(ch));
        if IsEmpty(och) then continue; end if;
        act:=Sym(#och)![Position(och,x^a): x in och];
        can:=CanonicalElementOfCycleType(Reverse(Sort(CycleType(act))));
        if act ne can then Adm[ai]:=false; continue ai; end if;
        Links[ai] cat:= [[x,x+1]: x in och | x^a eq x+1];
      end for;
    end for;
  end for;
  for ai:=1 to #A do   
    a:=AElts[ai];
    D:=Divisors(Order(a));
    Adm[ai]:=forall{d: d in D | Adm[Position(AElts,a^d)]};
    if not Adm[ai] then continue; end if;
    Links[ai]:=SortSet(&cat [Links[Position(AElts,a^d)]: d in D]);
  end for;

  list:=[<AElts[ai],[[Position(C,P[l[1]]),Position(C,P[l[2]])]:   
    l in Links[ai]]>: ai in [1..#A] | Adm[ai]];
    
  for i:=#list to 1 by -1 do
    if exists{j: j in [1..i-1] | list[j][2] eq list[i][2]} then
      Remove(~list,i);
    end if;
  end for;

  nonuberevenparent:=func<i|  (pa[i] ne 0) and (pa[i] notin Cu)
     or (pa[i] eq 0) and (i in Cu)>;

  trees:=[];

  for i:=1 to #list do
    f,l:=Explode(list[i]);
    cyc:=CycleDecomposition(f);
    //">",DelSpaces(f),DelSpaces(l),CycleDecomposition(f);
    o:=[SortSet(c): c in cyc];
    of:=[c: c in o | IsEven(#P[c[1]])   // even, non-top, non-ubereven parent
      and nonuberevenparent(Position(C,P[c[1]]))];
      //and (pa[P[c[1]]] ne 0) and (C[pa[P[c[1]]]] notin CU)];   
    os:=[c[1]: c in of];          // clusters for which the signs can be assigned
    ol:=[#c: c in of];            // and their orbit sizes under Frobenius
    Opos:=[Representative({i: i in [1..#O] | o in O[i]}): o in os];
       // to which H-orbit they belong
    for s in CartesianPower({-1,1},#os) do
      sg:=[x: x in s];
  
      if exists{0: i,j in [1..#os] | (i lt j) and (Opos[i] eq Opos[j]) 
          and (sg[j] gt sg[i]) and (ol[i] eq ol[j])} then continue; end if;     
      // isomorphic choice
       
      //">",DelSpaces(os),DelSpaces(sg),DelSpaces(O),DelSpaces(Opos);
        
      F:=ClTreeCopy(T);
      F`frob:=f;
      F`froblinks:=l;
      F`frobsigns:=[exists(z){z: z in [1..#os], y in o | (os[z] in y) and (j in y)} 
        select 1 else 0: j in [1..#P]]; // 1 was sg[z]
      for j:=1 to #os do
        F`frobsigns[os[j]]:=sg[j];
      end for;

      F`froborbit:=[0: i in [1..#P]];
      for i:=1 to #cyc do
        for j in cyc[i] do
          F`froborbit[j]:=i;    
        end for;
      end for;

      Append(~trees,F);
    end for;
  end for;

  return trees;
    
end intrinsic;


intrinsic HyperellipticGraph(S:: ClPic) -> GrphUnd
{Hyperelliptic graph that corresponds to a cluster tree; with some extra
vertices inserted to make it simple and make AutomorphismGroup work}
 
  g:=Genus(S);
  P:=PrincipalClusters(S);
  
  U:=UberevenClusters(S);
  T:=TwinClusters(S);
  NU:=[s: s in P | s notin U];
  
  function v(s)
    i:=Position(NU,s);
    if i ne 0 then return [i]; end if;
    i:=Position(U,s);
    assert i ne 0;
    return [#NU + 2*i-1, #NU + 2*i];
  end function;
  
  L:=0;                // links from even non-ubereven clusters to non-ubereven parents
  for s in P do 
    if s eq TopCluster(S) then continue; end if;
    p:=Parent(S,s);
    if not IsEven(S,s) or IsUbereven(S,s) or IsUbereven(S,p) then continue; end if;
    L+:=1;
  end for;
    
  genera:=[#OddChildren(S,s): s in NU] cat [0: i in [1..2*#U  +2*#T+2*L]];
  
  G:=Graph<0|>;                                   // principal clusters -> vertices / pairs  
  AddVertices(~G,#NU + 2*#U  +2*#T+2*L,genera);   // and virtual vertices for twins & even links 
                                        
  VG:=Vertices(G);
  
  for i:=1 to #T do              // twins -> loops or anti-invariant edges
    t:=T[i];
    vp:=v(Parent(S,t));
    vt1:=#NU+2*#U+2*i-1;
    vt2:=#NU+2*#U+2*i;
    G+:={VG[vp[1]],VG[vt1]};
    G+:={VG[vt1],VG[vt2]};
    G+:={VG[vp[#vp]],VG[vt2]};
  end for;
  
  j:=#NU+2*#U+2*#T;
  for s in P do
    if s eq TopCluster(S) then continue; end if;
    p:=Parent(S,s);
    if IsOdd(S,s) then
      if p notin P then
        assert exists(p){c: c in Children(S,p) | c ne s};   // x-type, replace p by other child
      end if;
      G+:={VG[v(s)[1]],VG[v(p)[1]]}; continue;
    end if;  
    if IsUbereven(S,p) then
      //if p notin P then
      //  assert exists(p){c: c in Children(S,p) | c ne s};   // x-type, replace p by other child
      //end if;
      G+:={VG[v(s)[1]],VG[v(p)[1]]}; 
      G+:={VG[Last(v(s))],VG[v(p)[2]]}; continue;
    end if;  
    if IsUbereven(S,s) then
      G+:={VG[v(s)[1]],VG[v(p)[1]]}; 
      G+:={VG[v(s)[2]],VG[v(p)[1]]}; continue;
    end if;  
    // s even, not ubereven, and p not ubereven - two links
    j+:=1;
    G+:={VG[v(s)[1]],VG[j]};
    G+:={VG[v(p)[1]],VG[j]};
    j+:=1;
    G+:={VG[v(s)[1]],VG[j]};
    G+:={VG[v(p)[1]],VG[j]};
  end for;

  return G,VG;
   
end intrinsic;


intrinsic BYTree(S:: ClPic) -> GrphUnd
{BY tree that corresponds to a cluster tree}

  blue:=0;
  yellow:=-1;
  g:=Genus(S); 
  t:=TopCluster(S);

  P:=PrincipalClusters(S);
  if IsEmpty(P) then 
    if g eq 0 then P:=[t]; end if;                         // genus 0 - exceptional case
    if g eq 1 then P:=[TwinClusters(S)[1]]; end if;        // genus 1 - exceptional case
  end if;
  
  tc:=Children(S,t);

  if IsEven(#S) and (#tc eq 2) and (#tc[1] ge 3) and (#tc[2] ge 3) then     // two maximal principals, 2g+2
    Exclude(~P,t); 
    xtype:=true; 
  else 
    xtype:=false;                                            // one maximal principal
  end if;

  TW:=[t: t in TwinClusters(S) | ParentIndex(S,t) ne 0 and (Parent(S,t) in P)];  
  U:=UberevenClusters(S);
  CTW:=#Last(P) eq 2*g select [t] else [];
  colors:=[s in U select yellow else blue+Genus(S,s): s in P] cat [blue: s in TW cat CTW];

  T:=Graph<0|>;                          // principal clusters -> vertices / pairs  
  AddVertices(~T,#P+#TW+#CTW,colors);    // and virtual vertices for twins and cotwins
  V:=Vertices(T);

  for i:=1 to #TW do                // edges from twins
    p:=Parent(S,TW[i]);
    pi:=Position(P,p);
    AddEdge(~T,#P+i,pi,yellow); 
  end for;  
  if not IsEmpty(CTW) then          // edges from a cotwin
    AddEdge(~T,#P,#P+#TW+1,yellow); 
  end if;

  for i:=1 to #P do                // edges from principal children
    s:=P[i];
    if s eq TopCluster(S) then continue; end if;
    p:=Parent(S,P[i]);
    pi:=Position(P,p);
    if pi eq 0 then continue; end if;
    AddEdge(~T,i,pi,IsEven(S,s) select yellow else blue);
  end for;  

  if xtype then             // two children of an x-type top cluster
    c1,c2:=Explode(Children(S,TopCluster(S)));
    p1:=Position(P,c1);
    p2:=Position(P,c2);
    AddEdge(~T,p1,p2,IsEven(#c1) select yellow else blue);
  end if;    

  return T,V,Edges(T);
   
end intrinsic;


intrinsic OpenBYTree(S:: ClPic) -> GrphUnd
{Open BY tree that corresponds to a cluster tree}

  blue:=0;
  yellow:=-1;
  inf:=-2;

  P:=[c: c in Clusters(S) | #c gt 2];
  if IsEmpty(P) then P:=[TopCluster(S)]; end if;

  t:=TopCluster(S);
  TW:=[c: c in TwinClusters(S) | c ne t];  
  U:=UberevenClusters(S);
  
  infindex:=#P+#TW+1;
  colors:=[s in U select yellow else blue+Genus(S,s): s in P] cat [blue: s in TW] cat [inf];
 
  T:=Graph<0|>;                       // clusters of size>2 -> vertices, plus infinity 
  AddVertices(~T,#P+#TW+1,colors);    // and non-principal vertices for twins
  V:=Vertices(T);
  EdgeData:=[];
  
  for i:=1 to #TW do                // edges from twins
    p:=Parent(S,TW[i]);
    pi:=Position(P,p);
    AddEdge(~T,#P+i,pi,yellow); 
    Append(~EdgeData,<TW[i],#P+i,pi,yellow>);
  end for;  

  for i:=1 to #P do                // edges from principal children
    s:=P[i];
    if s eq TopCluster(S) 
      then pi:=infindex;
      else pi:=Position(P,Parent(S,P[i]));
    end if;
    color:=IsEven(S,s) select yellow else blue;
    AddEdge(~T,i,pi,color);
    Append(~EdgeData,<s,i,pi,color>);
  end for;  

  return T,V,Edges(T),EdgeData;
   
end intrinsic;


intrinsic BYTreeTeX(T:: GrphUnd: graph:=false, xscale:=1, yscale:=1,
  label:=func<i,c|c eq 0 select "\\relax" else c>, decorations:="",
  edgestyle:=func<v1,v2|"">) -> MonStgElt
{TeX a BY tree or an open BY tree}
  error if not IsConnected(T),"a BY tree must be connected";

  function style(e) 
    v1,v2:=Explode(SetToSequence(EndVertices(e)));    
    return edgestyle(Index(v1),Index(v2)); 
  end function;
  
  V:=VertexSet(T);
  L:=Labels(V);
  E:=EdgeSet(T);
  LE:=Labels(E);
  
  blue:=0;
  yellow:=-1;
  inf:=-2;
  
  infpos:=Position(L,inf);
  if infpos ne 0 then
    inf:=V.infpos;
    infcolor:=Label(Representative(IncidentEdges(inf)));
  end if;
  
  XY:=[[0,0]: i in [1..#V]];
  
  P:=[Paths(v): v in V];
  lp:=[Max([#p: p in U]): U in P];
  _,r:=Max(lp);                                // r rightmost vertex
  _,l:=Max([#U: U in P[r]]);                   // l leftmost vertex
  longest:=P[l][r];                            // longest path
  
  placed:={V.l};
  XY[l]:=[0,0];
  
  for i:=1 to #longest do             // Place vertices in the longest path
    assert exists(v){v: v in EndVertices(longest[i]) | v notin placed};
    Include(~placed,v);
    XY[Index(v)]:=[i,0];
  end for;
  
  while #placed lt #V do
  for v in V do
    if v notin placed then continue; end if;
    N:=Neighbours(v);
    NP:=[w: w in N | w in placed];
    NN:=[w: w in N | w notin placed];
    if IsEmpty(NN) then continue; end if;
    x,y:=Explode(XY[Index(v)]);
    pos:=[[x-1,y],[x+1,y],[x,y+1],[x,y-1],[x+1,y+1],[x-1,y-1],[x+1,y-1],[x-1,y+1]];
    pos:=[p: p in pos | p notin XY]; 
    //v,x,y,#NN,#pos;  
    error if #NN gt #pos, "Not enough directions";
    for i:=1 to #NN do
      XY[Index(NN[i])]:=pos[i];
      Include(~placed,NN[i]);
    end for;
  end for;
  end while;

  XY:=[[xscale*d[1],yscale*d[2]]: d in XY];
  
  n:=func<x|Sprint(RealField(3)!x)>;

  NP:=[V.i: i in [1..#V] | Degree(V.i) eq 1 and L[i] eq 0];   // Non-principal vertices

  if (infpos ne 0) and (#V eq 2) and (LE[1] eq blue) then
    assert exists(v){v : v in V | (infpos eq 0) or (v ne inf)};
    Exclude(~NP,v); 
  end if;  
  //if (infpos eq 0) and (#V eq 2) and (#NP eq 2) and (LE[1] eq yellow) then
  //  NP:=[];
  //end if;

  header:="\\begin{tikzpicture}[scale=\\GraphScale]\n";
  out:=graph select "  \\GraphVertices\n" else "  \\BlueVertices\n";                                

  // Blue principal vertices and empty coordinates for the non-principal ones

  for i in [i: i in [1..#V] | (L[i] ge blue) and ((not graph) or (V.i notin NP))] do
    out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=%o]{%o};\n",n(1.5*XY[i][1]),n(XY[i][2]),
      label(i,L[i]),i);
  end for;

  for i in [i: i in [1..#V] | (L[i] ge blue) and graph and (V.i in NP)] do
    out*:=Sprintf("  \\coordinate (%o) at (%o,%o);\n",
      i,n(1.5*XY[i][1]),n(XY[i][2]));
  end for;

  YellowVertices:=[i: i in [1..#V] | L[i] eq yellow];      // Yellow vertices
  if not graph and not IsEmpty(YellowVertices) then out*:="  \\YellowVertices\n"; end if;
  for i in YellowVertices do
    if graph then
      out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=%o]{%o+}\n",n(1.5*XY[i][1]+0.25),n(XY[i][2]+0.25),"\\relax",i);
      out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=%o]{%o-}\n",n(1.5*XY[i][1]-0.25),n(XY[i][2]-0.25),"\\relax",i);
    else
      out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=%o]{%o}\n",n(1.5*XY[i][1]),n(XY[i][2]),"\\relax",i);
    end if;
  end for;
  
  i:=infpos;                                               // Infinity
  if i ne 0 then
    if graph and (infcolor eq yellow) then
      out*:=Sprintf("  \\InfVertices\n  \\Vertex[x=%o,y=%o,L=\\InfLabel]{%o+}\n",
        n(1.5*XY[i][1]+0.25),n(XY[i][2]+0.25),i);
      out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=\\InfLabel]{%o-}\n",
        n(1.5*XY[i][1]-0.25),n(XY[i][2]-0.25),i);
    else
      out*:=Sprintf("  \\InfVertices\n  \\Vertex[x=%o,y=%o,L=\\InfLabel]{%o}\n",
        n(1.5*XY[i][1]),n(XY[i][2]),i);
    end if;
  end if;
  
  BlueEdges:={e: e in E | Label(e) eq blue};
  YellowEdges:={e: e in E | Label(e) eq yellow};
  
  if graph or not IsEmpty(BlueEdges) then out*:="  \\BlueEdges\n"; end if;     // Blue edges
  for e in BlueEdges do
    v:=SetToSequence(EndVertices(e));
    out*:=Sprintf("  \\Edge%o(%o)(%o)\n",style(e),v[1],v[2]);
  end for;
  
  if not graph and not IsEmpty(YellowEdges) then                      // Yellow edges
    out*:="  \\YellowEdges\n"; 
  end if;     
  for e in YellowEdges do
    v:=SetToSequence(EndVertices(e));
    if graph and ((v[1] in NP) or (v[2] in NP)) then continue; end if;
    l1:=Label(v[1]);
    l2:=Label(v[2]);
    if not graph then
      out*:=Sprintf("  \\Edge%o(%o)(%o)\n",style(e),v[1],v[2]);
    elif (l1 ge blue) and (l2 ge blue) then
      out*:="  \\BendedEdges\n";
      out*:=Sprintf("  \\Edge%o(%o)(%o)\n",style(e),v[1],v[2]);
      out*:=Sprintf("  \\Edge%o(%o)(%o)\n",style(e),v[2],v[1]);
      out*:="  \\BlueEdges\n";
    elif (l1 ge blue) and (l2 lt blue) then
      out*:=Sprintf("  \\Edge%o(%o)(%o+)\n",style(e),v[1],v[2]);
      out*:=Sprintf("  \\Edge%o(%o)(%o-)\n",style(e),v[1],v[2]);
    elif (l2 ge blue) and (l1 lt blue) then
      out*:=Sprintf("  \\Edge%o(%o+)(%o)\n",style(e),v[1],v[2]);
      out*:=Sprintf("  \\Edge%o(%o-)(%o)\n",style(e),v[1],v[2]);
    else 
      out*:=Sprintf("  \\Edge%o(%o+)(%o+)\n",style(e),v[1],v[2]);
      out*:=Sprintf("  \\Edge%o(%o-)(%o-)\n",style(e),v[1],v[2]);
    end if;    
  end for;

  if graph then
  for w in NP do
    v:=Representative(Neighbours(w));
    assert exists(vi){i: i in [1..#V] | V.i eq v};
    assert exists(wi){i: i in [1..#V] | V.i eq w};
    xv,yv:=Explode(XY[vi]);
    xw,yw:=Explode(XY[wi]);
    l:=L[vi];
    s:=l eq yellow select "Edge" else "Loop";
    if xw lt xv then dir:="W"; 
    elif xw gt xv then dir:="E"; 
    elif yw lt yv then dir:="N"; 
    else dir:="S";    
    end if;
    out*:=Sprintf("  \\%o%o(%o)\n",s,dir,v);   
  end for;
  end if;

  // exceptional circle graph (closed)
  if graph and (infpos eq 0) and (#V eq 2) and (#NP eq 2) and (LE[1] eq yellow) then
    out:=Sprintf("  \\GCircle(%o,%o)(%o,%o)\n",
      n(1.5*XY[1][1]),n(XY[1][2]),n(1.5*XY[2][1]),n(XY[2][2]));
    out*:="  \\BlueVertices\n";
    out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=\\relax]{%o}\n",
      n(1.5*XY[1][1]),n(XY[1][2]),1);
    out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=\\relax]{%o}\n",
      n(1.5*XY[2][1]),n(XY[2][2]),2);
  end if;

  // exceptional circle graph (open)
  if graph and (infpos ne 0) and (#V eq 2) and (#NP eq 1) and (LE[1] eq yellow) then
    out*:="  \\BlueVertices\n";
    out*:=Sprintf("  \\Vertex[x=%o,y=%o,L=\\relax]{%o}\n",
      n(1.5*XY[1][1]-0.25),n(XY[1][2]),1);
  end if;
  
  footer:="\\end{tikzpicture}";
  return header*out*decorations*footer;
end intrinsic;


intrinsic ClusterPictureTeXNew(s::MonStgElt) -> MonStgElt
{Produce a TeX cluster picture from a string describing clusters, e.g. s="[1,[2,3]_n^e-[4B,5B]_n^e]_*" }

  int:=func<s|(s[1] ge "0") and (s[1] le "9")>;

  // Split into tokens
  
  tokens:=[];
  repeat
    if int(s) then                      // Integer (root index)
      ok,buf:=Match(s,"%i%s"); 
      s:=buf[2]; 
      Append(~tokens,Sprint(buf[1]));
    elif s[1] eq "{" then               // Opening }
      brcount:=0;
      ok:=false;
      for i:=1 to #s do
        if s[i] eq "{" then brcount+:=1; end if;
        if s[i] eq "}" then brcount-:=1; end if;
        if brcount eq 0 then ok:=true; token:=s[[1..i]]; s:=s[[i+1..#s]]; break; end if;
      end for;
      error if not ok, "Closing brace not found: "*s;
      Append(~tokens,token);
    else                                 // Everything else
      Append(~tokens,s[1]);
      s:=s[[2..#s]];
    end if;
  until #s eq 0;
  
  // Process clusters and depth
  
  error if IsEmpty(tokens), "Empty string";
  error if tokens[1] ne "[", "Opening [ expected at the beginning";
  error if Count(tokens,"[") ne Count(tokens,"]"), "Unmatched []";
  
  CS:=[];    // Cluster stack
  C:=[];     // Discovered clusters 
  subs:=[];  // Subscripts
  sups:=[];  // Superscripts
  i:=1;
  lastt:="";
  froblinks:=[];  // Frobenius links between clusters
  rootstyle:=[];  // Root styles A,B,C,...
  clstyle:=[];    // Cluster styles A,B,C,...
  repeat
    t:=tokens[i];
    i+:=1;
    if t eq "[" then            // Open a new cluster
      Append(~CS,[]);
    elif t eq "]" then          // Close the current cluster
      Append(~C,CS[#CS]);
      Append(~subs,"");
      Append(~sups,"");
      Append(~clstyle,"");
      if #CS ne 1 then 
        CS[#CS-1] cat:= CS[#CS];
      end if;
      CS:=CS[[1..#CS-1]];
    elif int(t) then            // Add a root
      Append(~CS[#CS],eval t);  
      rootstyle[eval t]:="";
    elif t eq "_" then          // subscript
      error if i gt #tokens, "Cannot end with a _";
      error if lastt notin ["]","^"], "_ does not follow a closed cluster";
      subs[#C]:=tokens[i];
      i+:=1;
    elif t eq "^" then          // superscript
      error if i gt #tokens, "Cannot end with a ^";
      error if lastt notin ["]","_"], "^ does not follow a closed cluster";
      sups[#C]:=tokens[i];
      i+:=1;
    elif (#t eq 1) and (t ge "A") and (t le "Z") and int(lastt) then   // Root style
      rootstyle[eval lastt]:=t; continue;
    elif (#t eq 1) and (t ge "A") and (t le "Z") and lastt in ["]","^","_"] then   // Cluster style
      clstyle[#C]:=t; continue;
    else
      error if t notin [",","-"], "Unexpected symbol: "*t;
      if t eq "-" then 
        error if lastt notin ["]","_","^"], "- does not follow a closed cluster";
        Append(~froblinks,#C);
      end if;
    end if;
    lastt:=t;
  until i gt #tokens;
  error if not IsEmpty(CS), "Unmatched clusters";
  
  // Make cluster picture
  
  top:=C[#C];
  for c in C do assert c subset top; end for;
  CP:=ClusterPicture(C cat [[c]: c in top]);
  
  // Generate output without decorations and frobenius links (inserted later)
  
  out:=ClusterPictureTeXNew(CP);
  
  // Subscripts, superscripts, styles
  
  for i:=1 to #C do
    clstr:=Sprintf("\\Cluster c%o = ",i);
    p:=Position(out,clstr);
    error if p eq 0, "Cluster #"*Sprint(i)*" not found in TeX output";
    p2:=Position(out[[p..#out]],";") + p-1;
    assert out[p2] eq ";";
    error if p2 eq 0, "Cluster #"*Sprint(i)*" semicolon not matched in TeX output";
    sup:=sups[i] ne "";
    sub:=subs[i] ne "";
    style:=clstyle[i] ne "" select ",cl"*clstyle[i] else "";
    if not (sup or sub) then dec:=clstr;
    elif not sup        then dec:=Sprintf("\\ClusterD c%o[%o] = ",i,subs[i]);
    elif not sub        then dec:=Sprintf("\\ClusterL c%o[%o] = ",i,sups[i]);
    else                     dec:=Sprintf("\\ClusterLD c%o[%o][%o] = ",i,sups[i],subs[i]);
    end if;     
    out:=out[[1..p-1]]*dec*out[[p+#clstr..p2-1]]*style*out[[p2..#out]];
  end for;
  
  // Root style
  
  S:=Split(out);
  for i:=1 to #S do
    ok,buf:=Match(S[i],"  \\Root {%s} {%s} {r%i};");
    if (not ok) or (rootstyle[buf[3]] eq "") then continue; end if;
    S[i]:=Sprintf("  \\Root[%o] {%o} {%o} {r%o};",rootstyle[buf[3]],buf[1],buf[2],buf[3]);
  end for;
  out:=PrintSequence(S: sep:="\n");
  
  // Frobenius links 
  
  for i in froblinks do
    next:=[c: c in Children(CP,Parent(CP,C[i])) | Max(C[i])+1 in c][1];
    j:=Position(C,next);
    t:=(subs[i] ne "") or (sups[i] ne "") select "t" else "";
    ReplaceString(~out,"\\endclusterpicture",
      Sprintf("  \\frob(c%o%o)(c%o);\n\\endclusterpicture",i,t,j));
  end for;

  return out;

end intrinsic;

Wpe:=function(p,e)
  p:=Integers()!p;
  e:=Integers()!e;  
  if IsPrimePower(e) then
	bool,l,k:=IsPrimePower(e);
	if l ne 2 then
	  return LegendreSymbol(p,l);
	else
	  if k eq 1 then
		return LegendreSymbol(-1,p);
	  elif k eq 2 then
		return LegendreSymbol(-2,p);
	  else
		return LegendreSymbol(2,p);
	  end if;
	end if;
  elif e gt 2 and e mod 4 eq 2 then
	if IsPrimePower(Integers()!(e/2)) then
	  bool,l,k:=IsPrimePower(Integers()!(e/2));
	  if l mod 4 eq 3 then
		return LegendreSymbol(-1,p);
	  else
		return 1;
	  end if;
	else
	  return 1;
	end if;
  else
	return 1 ;
  end if;
end function;

intrinsic IsLocalLawful(T:: ClPic) -> BoolElt
{Checks if an abelian variety is local lawful}

  lawful:=false;
  p:=ResidueCharacteristic(T);
  Ab:=AbelianRepresentation(T);
  CT:=CharacterTable(InertiaGroup(T));
  Orders:=[];
  Mult:=[];
  for chi in CT do
    if InnerProduct(chi,Ab) eq 0 then
	  continue;
    else
      if Order(chi) notin Orders then
	    Append(~Orders,Order(chi));
	    Append(~Mult,[Order(chi),InnerProduct(chi,Ab)]);
	  else
	    for i in [1..#Mult]	do
	      if Mult[i,1] eq Order(chi) then
		    Mult[i,2]:=Mult[i,2]+InnerProduct(chi,Ab);
		  end if;
	    end for;
	  end if;
    end if;
  end for;
  
  redMult:=[];
  for i in [1..#Mult]  do
    if Mult[i,1] le 2 then
      continue;
    end if;
    if (Integers()!Mult[i,1]) mod 2 eq 1 then
	  newmult:=Integers()!(Mult[i,2]/EulerPhi((Integers()!Mult[i,1])));
      Append(~redMult,[Mult[i,1],newmult]);
    elif (Integers()!Mult[i,1]) mod 4 eq 2 or Mult[i,1] eq 4 then
	  newmult:=Integers()!(Mult[i,2]/EulerPhi((Integers()!Mult[i,1])));
      Append(~redMult,[Integers()!(Mult[i,1]/2),newmult]);
    end if;
  end for;
  
  Wg:=1;
  for rm in redMult do
    Wg:=Wg*(Wpe(p,rm[1])^rm[2]);
  end for;
  
  if Degree(ResidueClassField(Integers(BaseField(T)))) mod 2 eq 0 then
    Wg:=1;
  end if;
  
  if Degree(Ab) eq 2*Genus(T) and Wg eq 1 then
    lawful:=true;
  end if;

  Trep,Tor,TorGal:=ToricRepresentation(T);
  CTG:=CharacterTable(GaloisGroup(T));
  assert Restriction(TorGal,InertiaGroup(T)) eq Tor;
  
  QuadChars:=[];
  for chi in CTG do
    if Degree(chi) eq 1 and Order(chi) eq 2 then
      Append(~QuadChars,chi);
    end if;
  end for;
  
  for chi in QuadChars do
    if Restriction(chi,InertiaGroup(T)) eq CT!1 then
      eta:=chi;
      Exclude(~QuadChars,eta);
    end if;
  end for;
  
  n1:=Integers()!(InnerProduct(TorGal,CTG!1));
  n2:=Integers()!(InnerProduct(TorGal,eta));
  if #QuadChars eq 0 then
    n3,n4:=Explode([Integers()!0,Integers()!0]);
  else
    assert #QuadChars eq 2; 
    n3:=Integers()!(InnerProduct(TorGal,QuadChars[1]));
    n4:=Integers()!(InnerProduct(TorGal,QuadChars[2]));
  end if;
  
  if ((n1-n2) mod 2 eq 0) and ((n3-n4) mod 2 eq 0) and (Wg eq (-1)^(n1+n3)) then
    lawful:=true;
  end if;
 
  return lawful;  
end intrinsic;


// Simone's functions


intrinsic IsGaloisInvariant(Sigma::ClPic) -> BoolElt
{Are all proper clusters Galois-invariant}
  _,G:=PermutationAction(Sigma,ProperClusters(Sigma));
  return #G eq 1;
end intrinsic;


intrinsic IsRemovable(Sigma::ClPic, c::SeqEnum[RngIntElt]) -> BoolElt
{Is a removable cluster in the sense of Muselli}
  g:=Genus(Sigma);
  return not IsProper(Sigma,c) 
    or (c eq TopCluster(Sigma)) and exists{t: t in ProperChildren(Sigma,c) | #t eq 2*g+1};
end intrinsic;


intrinsic IsContractible(Sigma::ClPic, c::SeqEnum[RngIntElt]) -> BoolElt
{Is a contractible cluster in the sense of Muselli}
  g:=Genus(Sigma);
  ds:=Depth(Sigma,c);
  intdepth:=IsCoercible(Z,ds);
  return (#c eq 2) and not intdepth
    or (#c eq 2*g+2) and forall{t: t in ProperChildren(Sigma,c) | #t eq 2*g} and not intdepth
    or (#c eq 2*g+2) and (#Children(Sigma,c) eq 2) and IsOdd(#(Children(Sigma,c)[1])) and IsOdd(Z!ds);
end intrinsic;


