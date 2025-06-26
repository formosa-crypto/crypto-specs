require import AllCore IntDiv List Ring.

from Jasmin require import JWord.

from JazzEC require import Array25 Array32 Array34 Array64 Array128 Array168 Array256 Array384.
from JazzEC require import Array1024 Array1408 Array1024 Array1088 Array1184 Array1536.

require import GFq Rq Serialization Correctness1024.
require import BitEncoding.
import BitChunking BS2Int.
(*---*) import IntID.
import Serialization1024.

(* FixMe: Move *)
lemma iteriS_rw ['a] (n : int) (opr : int -> 'a -> 'a) (x : 'a) :
  0 < n => iteri n opr x = opr (n - 1) (iteri (n - 1) opr x).
proof. smt(iteriS). qed.

lemma mkseqSr_rw ['a] (f : int -> 'a) (n : int) :
  0 < n => mkseq f n = f 0 :: mkseq (fun i => f (i+1)) (n-1).
proof. move => *. have H : exists i, n = i+1 by smt().
elim H => i H0 /=; rewrite H0 /(\o) /=.
have := mkseqSr f i _; 1: by smt().
rewrite /(\o) => /= => - /#. 
qed.

lemma nth_nth_chunk ['a]  (r i j : int) (l : 'a list) x0 x1 x2 :
   0 <= r =>
   0 <= i < size l %/ r =>
   0 <= j < r => nth x0 (nth x1 (chunk r l) i) j = nth x2 l (r*i+j).
proof. 
move => *.
rewrite /chunk /= nth_mkseq 1:/# /= nth_take 1,2:/# /= nth_drop 1,2:/#. 
rewrite (nth_change_dfl x0 x2) //.
split; smt(JUtils.divz_cmp size_ge0).
qed.

lemma size_BytesToBits l : size (BytesToBits l) = 8 * size l by
     rewrite size_flatten /= StdBigop.Bigint.sumzE /= -map_comp /(\o) /=;
     rewrite !StdBigop.Bigint.BIA.big_mapT /= /(\o) /=;
     rewrite !StdBigop.Bigint.big_constz /=;
     rewrite !count_predT /= /= /#. 

lemma size_chunksBytesToBits l k n : 
   0 < k => 0 <= n < 8 * size l %/ k =>
   size ((nth witness (chunk k (BytesToBits l))) n) = k.
move => kb nb.
+ have  /= [_ ->] := (all_nthP (fun l => size l = k) (chunk k (flatten (map W8.w2bits l))) witness); 1,3: by smt(List.allP in_chunk_size).
   by  rewrite !size_chunk /=; [ by smt() | ];
     rewrite size_flatten /= StdBigop.Bigint.sumzE /= -map_comp /(\o) /=;
     rewrite !StdBigop.Bigint.BIA.big_mapT /= /(\o) /=;
     rewrite !StdBigop.Bigint.big_constz /=;
     rewrite !count_predT /= /#. 
qed.

lemma size_take_le  ['a] (n : int) (s : 'a list):
   0 <= n => size (take n s) = if n <= size s then n else size s
  by smt(size_take).

lemma size_drop_le ['a] (n : int) (s : 'a list): 
    0 <= n => 0 <= size s - n => size (drop n s) = if 0 <= size s - n then size s - n else 0
by smt(size_drop).

lemma pow2_8 : 2^8 = 256 by [].

lemma subarray384K0 (a b c d : W8.t Array384.t):
   subarray384
        (fromarray384 a b c d) 0 = a.
proof.
rewrite /subarray384 /fromarray384 tP => k kb.
by rewrite initiE 1:/# /= initiE 1:/# /= /= kb /=.
qed.

lemma subarray384K1 (a b c d : W8.t Array384.t):
   subarray384
        (fromarray384 a b c d) 1 = b.
proof.
rewrite /subarray384 /fromarray384 tP => k kb.
by rewrite initiE 1:/# /= initiE 1:/# /= /= ifF /#. 
qed.

lemma subarray384K2 (a b c d : W8.t Array384.t):
   subarray384
        (fromarray384 a b c d) 2 = c.
proof.
rewrite /subarray384 /fromarray384 tP => k kb.
by rewrite initiE 1:/# /= initiE 1:/# /= /= ifF /#. 
qed.

lemma subarray384K3 (a b c d : W8.t Array384.t):
   subarray384
        (fromarray384 a b c d) 3 = d.
proof.
rewrite /subarray384 /fromarray384 tP => k kb.
by rewrite initiE 1:/# /= initiE 1:/# /= /= ifF /#. 
qed.

lemma fromarray256K ['a] (x : 'a Array1024.t) :
     fromarray256 (subarray256 x 0) 
                  (subarray256 x 1)
                  (subarray256 x 2)
                  (subarray256 x 3) = x.
 rewrite /fromarray256 /subarray256; rewrite tP => k kb; rewrite initiE 1:/# /=.
 case(0<=k<256); 1: by move => *; rewrite initiE /#.
 case(256<=k<512); 1: by move => *; rewrite initiE /#.
 case(512<=k<768); by move => *; rewrite initiE /#.
qed.


lemma sem_decode1K  : cancel decode1  encode1.
admitted.

lemma sem_decode5K  : cancel decode5  encode5.
admitted.

lemma sem_decode12K  : cancel decode12  encode12.
admitted.   

lemma subarray256K ['a] (a b c d : 'a Array256.t) :
     subarray256 (fromarray256 a b c d) 0 = a /\
     subarray256 (fromarray256 a b c d) 1 = b /\
     subarray256 (fromarray256 a b c d) 2 = c /\
     subarray256 (fromarray256 a b c d) 3 = d.
admitted. (* 
by rewrite /subarray256 /fromarray256; do split; rewrite tP => k kb; rewrite initiE 1:/# /= initiE 1:/# /=; [ rewrite ifT 1:/# /=| rewrite ifF 1:/# /= ifT 1:/# /= | rewrite ifF 1:/#  /= ifF 1: /# /= | rewrite ifF 1:/#  /= ifF 1: /# /=].
*)

lemma fromarray384K ['a] (x : 'a Array1536.t) :
     fromarray384 (subarray384 x 0) 
                  (subarray384 x 1)
                  (subarray384 x 2)
                  (subarray384 x 3) = x.
admitted. (* 
 rewrite /fromarray384 /subarray384; rewrite tP => k kb; rewrite initiE 1:/# /=.
 case(0<=k<384); 1: by move => *; rewrite initiE /#.
 case(384<=k<768); by move => *; rewrite initiE /#.
 case(768<=k<1024); by move => *; rewrite initiE /#.
qed. *)


lemma sem_decode12_vecK  : cancel decode12_vec  encode12_vec.
admitted.

lemma sem_decode11_vecK  : cancel decode11_vec  encode11_vec.
admitted.

lemma sem_encode1K (x : ipoly) : 
   (forall i, 0 <= i < 256 => 0 <= x.[i] < 2) =>
     x = (decode1 (encode1 x)).
admitted.

lemma sem_encode5K (x : ipoly) : 
   (forall i, 0 <= i < 256 => 0 <= x.[i] < 32) =>
     x =  decode5 (encode5 x).
admitted.

lemma sem_encode11_vecK (x : ipolyvec) : 
   (forall i, 0 <= i < 1408 => 0 <= x.[i] < 1408) =>
     x =  decode11_vec (encode11_vec x).
admitted.


lemma sem_encode12_vecK (x : ipolyvec) : 
   (forall i, 0 <= i < 1024 => 0 <= x.[i] < 4096) =>
     x =  decode12_vec (encode12_vec x).
admitted.

require import BitEncoding.  
import BS2Int BitChunking.
lemma sem_decode1_bnd a k : 0<=k<256 => 0<= (decode1 a).[k] < 2.
admitted.
(* 
proof.
move => kb; rewrite /sem_decode1 get_of_list //. 
pose ll := decode _ _.
have Hs : size ll = 256 by
  rewrite /ll /decode size_map size_chunk //= size_take_le //=; 
  smt(Array32.size_to_list size_BytesToBits).
have /= := (all_nthP (fun (b : int) => 0<= b < 2) ll 0) .
have ->  /= : all (fun (b : int) => 0 <= b && b < 2) ll; last by smt().
rewrite allP /ll /decode => /= i.
rewrite mapP => Hm; elim Hm => v [Hv ->].
have Hsv := (in_chunk_size _ _ _ _ Hv); 1: smt().
have := bs2int_range v; rewrite Hsv /=.
by smt(mem_range).
qed.


*)
