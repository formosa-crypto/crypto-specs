require import AllCore List RealExp IntDiv.
require (*  *) Subtype. 
from Jasmin require import JModel.

require import Notation.

op n : { int | 0 <= n } as ge0_n.

op len1 = ceil (8%r * n%r / log2 w%r).
op len2 = floor (log2 (len1 * (w - 1))%r / log2 w%r) + 1.
op len = len1 + len2.

lemma ge0_len : 0 <= len by admit.

clone import Subtype as NBytes with 
   type T = W8.t list,
   op P = fun l => size l = n
   rename "T" as "nbytes"
   proof inhabited by (exists (nseq n W8.zero);smt(size_nseq ge0_n))
   proof *.

type key = nbytes.
type seed = nbytes.

op prf : seed -> adrs -> key.
op f : key -> nbytes -> nbytes.
op nbytexor(a b : nbytes) = 
    map (fun (ab : W8.t*W8.t) => ab.`1 `^` ab.`2) (zip a b).

module Chain = {
  proc chain(_X : nbytes, i s : int, _SEED : seed, _ADRS : adrs) : nbytes = {
    var tmp : nbytes <- _X;
    var _KEY : key;
    var chcount : int <- 0;
    var _BM : nbytes;
    (* case i + s <= w-1 is precondition *)
    while (chcount < s) {
     _ADRS <- setHashAddress _ADRS (i + chcount);
     _ADRS <- setKeyAndMask _ADRS 0;
     _KEY <- prf _SEED  _ADRS;
     _ADRS <- setKeyAndMask _ADRS 1;
     _BM <- prf _SEED _ADRS;

     tmp <- f _KEY (nbytexor tmp _BM);
     chcount <- chcount + 1;       
    }
    return tmp;
  }
}.

op chain_pre(_X : nbytes, i s : int, _SEED : seed, _ADRS : adrs) = 
    0 <= s <= w-1.
    

op chain(_X : nbytes, i s : int, 
         _SEED : seed, _ADRS : adrs) : nbytes.

axiom chain0 _X i s _SEED _ADRS: 
    s = 0 => chain _X i s _SEED _ADRS = _X.

axiom chainS _x i s _SEED _ADRS: 
    0 < s => chain _x i s _SEED _ADRS =
      let tmp = chain _x i (s - 1) _SEED _ADRS in 
      let _ADRS = setHashAddress _ADRS (i + s - 1) in
      let _ADRS = setKeyAndMask _ADRS 0 in
      let _KEY = prf _SEED  _ADRS in
      let _ADRS = setKeyAndMask _ADRS 1 in
      let _BM = prf _SEED _ADRS in
      let tmp = f _KEY (nbytexor tmp _BM) in
          tmp.

lemma chain_ll : islossless Chain.chain
  by proc;while(true) (s - chcount); by auto => /#.

lemma chain_imp_fun __X _i _s  __SEED __ADRS:
  chain_pre __X _i _s  __SEED __ADRS =>
  hoare [ Chain.chain : 
          arg = (__X,_i,_s,__SEED,__ADRS) ==>
             res = chain __X _i _s  __SEED __ADRS].
proof. 
move => cpre.
proc => /=.  
while(__X = _X /\ _i = i /\ _s = s /\
      __SEED = _SEED /\ 
      (forall k, 0 <= k < 6 => _ADRS.[k] = __ADRS.[k]) /\ 
      tmp = chain __X _i chcount __SEED __ADRS /\
      0<=chcount<=_s); last by auto;smt(chain0).
auto => /> &hr *.
do split; move => *; 1,3,4: by smt(Array8.set_eqiE Array8.set_neqiE).
by rewrite (chainS _ _ (chcount{hr} + 1) _ _) 1:/# /=;
   congr;congr => /=; [ | congr];
   apply tP => i  ib;
   case (i <> 7);smt(Array8.set_eqiE Array8.set_neqiE).
qed.
