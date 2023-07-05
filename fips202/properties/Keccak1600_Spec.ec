(******************************************************************************
   Keccak1600_Spec.ec:

   Properties of the Keccak1600 specification.

    - function byte-based specification
    - correctness wrt imperative spec [FIPS202_SHA3.ec]

******************************************************************************)
require import AllCore List Int IntDiv.

require StdOrder.
import StdOrder.IntOrder.

require BitEncoding.
import BitEncoding.BitChunking.

require export FIPS202_SHA3.

require import Keccakf1600_Spec.

import EclibExtra.

(*

type bit = bool.
type bits = bool list.
*)
type byte = W8.t.
type bytes = W8.t list.

op bytes2state (bs: bytes): state =
 Array25.of_list W64.zero (w64L_from_bytes bs).

op state2bytes (st: state): bytes =
 w64L_to_bytes (to_list st).

op state_set_u8 (st: state, pos: int, x: byte): state =
 st.[pos %/ 8 <- w64_set_u8 st.[pos %/ 8] (pos %% 8) x].

op state_xor_u8 (st: state, pos: int, x: byte): state =
 st.[pos %/ 8 <- w64_xor_u8 st.[pos %/ 8] (pos %% 8) x].




(** [state_absorb] adds [m] to the state *)
op state_absorb (st: state, m: bytes): state =
 addstate st (bytes2state m).

(** [state_squeeze] extracts [len] bytes from [st] *)
op state_squeeze (st: state, len: int): bytes =
 take len (state2bytes st).

(*

(** [chunkremnant] returns the leftovers not handled by [chunk] *)
op chunkremnant ['a] (n: int) (bs: 'a list) =
 drop (size bs %/ n * n) bs.
*)

abbrev KECCAK_F1600 = keccak_f1600_op.

(** absorb intermediate blocks *)
op state_absorb_iblocks (ml: bytes list): state =
 foldl (fun st m => KECCAK_F1600 (state_absorb st m)) st0 ml.

(** [addratebit] flips the "rate bit" *)
op addratebit (r64: int, st: state): state =
 st.[r64-1 <- w64_xor_u8 st.[r64-1] 7 (W8.of_int 128)].
(* alternative definition... 
op addratebit (r64: int, st: state): state =
 let w = st.[r64-1] in
 let rb = w.[63] in
 st.[r64-1 <- w.[63 <- !rb]].
*)

op keccak1600_absorb_op (r64: int, suffix: byte, m: bytes): state =
 addratebit
  r64
  (state_absorb (state_absorb_iblocks (chunk (8*r64) m))
                (rcons (chunkremains (8*r64) m) suffix)).


(** squeezes [len] bytes from [KECCAK_F1600^i(st)] *)
op state_squeeze_i (st: state, len: int, i: int): bytes =
  state_squeeze (iter i KECCAK_F1600 st) len.


op keccak1600_squeeze_op (r64: int, st: state, len: int) =
 (* intermediate blocks *)
 flatten (map (state_squeeze_i st (8*r64)) (iota_ 1 (len %/ (8*r64))))
 (* last block *)
 ++ state_squeeze_i st (len %% (8*r64)) (len %/ (8*r64) + 1).




op keccak1600_op (r64: int, suffix: byte, m: bytes, len8: int): bytes =
 keccak1600_squeeze_op r64 (keccak1600_absorb_op r64 suffix m) len8.


op SHA3_224 (m: bytes): bytes =
 keccak1600_op 18 (W8.of_int 06) m 28.
op SHA3_256 (m: bytes): bytes =
 keccak1600_op 17 (W8.of_int 06) m 32.
op SHA3_384 (m: bytes): bytes =
 keccak1600_op 13 (W8.of_int 06) m 48.
op SHA3_512 (m: bytes): bytes =
 keccak1600_op 9 (W8.of_int 06) m 64.
op SHAKE128 (m: bytes, len8: int): bytes =
 keccak1600_op 21 (W8.of_int 31) m len8.
op SHAKE256 (m:bytes, len8: int): bytes =
 keccak1600_op 17 (W8.of_int 31) m len8.

(** Using XOFs without explicit output len argument.

    Citation from [FIPS-202, A-2 (pag. 24)]:

    "By design, the output length for an XOF does not affect the bits
    that it produces, which means that the output length is not a
    necessary input to the function. Conceptually, the output can be
    an infinite string, and the application/protocol/system that
    invokes the function simply computes the desired number of initial
    bits of that string. Consequently, when two different output
    lengths are chosen for a common message, the two outputs are
    closely related: the longer output is an extension of the shorter
    output. For example, given any positive integers "d" and "e", and any
    message "M", "Trunc_d(SHAKE128(M, d+e))" is identical to "SHAKE128(M,
    d)". The same property holds for SHAKE256."

    To support such a use, we provide functions returning the "ith" (i \in
    [1..]) block of SHAKE128/256 for a given input.                                   *)

op SHAKE128_i (m: bytes, i: int): bytes =
 drop (8*21*(i-1)) (SHAKE128 m (8*21*i)).

op SHAKE256_i (m: bytes, i: int): bytes =
 drop (8*17*(i-1)) (SHAKE256 m (8*17*i)).






(*******************************************************************************
                               Correctness proof
*******************************************************************************)


lemma Array25_of_listK' ['a] (d:'a) l:
 to_list (Array25.of_list d l)
 = take 25 (l ++ nseq 25 d).
proof.
apply (eq_from_nth d).
 by rewrite size_to_list size_take; smt(size_cat size_ge0 size_nseq).
rewrite size_to_list => i Hi.
rewrite /Array25.to_list nth_mkseq //=.
rewrite get_of_list // take_cat.
case: (25 < size l) => C.
 by rewrite nth_take /#.
rewrite nth_cat.
case: (i < size l) => C2 //.
by rewrite take_nseq nth_nseq; smt(nth_out size_ge0).
qed.

print chunkfill.
(* este faz sentido (em vez de ter de lidar com os nseqs... *)
op chunkfill' ['a] (d:'a) n l =
 take n (l ++ nseq n d).


lemma state2bitsK:
 cancel state2bits bits2state.
admitted.

lemma bits2stateK bs:
 state2bits (bits2state bs)
 = chunkfill' false 1600 bs.
 admitted.

lemma addstateA (s1 s2 s3: state):
 addstate s1 (addstate s2 s3) = addstate (addstate s1 s2) s3.
proof.
rewrite /addstate; apply ext_eq => i Hi.
by rewrite !map2iE // W64.WRing.AddMonoid.addmA. 
qed.

op xorbits (xs ys: bool list) = map2 Logic.(^) xs ys.

lemma addstate_xorbits bs1 bs2:
 size bs1 = size bs2 =>
 addstate (bits2state bs1) (bits2state bs2)
 = bits2state (xorbits bs1 bs2).
proof.
move=> Hsz .
rewrite /bits2state /addstate; apply Array25.ext_eq => i Hi.
rewrite map2iE // !get_of_list //.
rewrite !nth_w64L_from_bits /xorbits 1..3:/#  drop_map2 take_map2.
apply W64.ext_eq => k Hk.
rewrite !get_bits2w //.
case: (k < size (take 64 (drop (i * 64) bs1))) => C.
 rewrite (nth_map2 false false).
  rewrite size_take // size_drop 1:/#.
  smt(size_take size_drop size_ge0).
 smt(W64.get_bits2w).
rewrite nth_out; first by rewrite size_map2 1:/#.
by rewrite xorwE !get_bits2w // !nth_take 1..4:/# !nth_drop 1..4:/# !nth_out; smt(size_take size_drop).
qed.

lemma W64_bits2w_nseq0 n:
 W64.bits2w (nseq n false)
 = W64.zero.
proof.
apply W64.ext_eq => i Hi.
by rewrite /bits2w initiE //= nth_nseq_if /#.
qed.

lemma addratebit_addstate r64 st:
 0 < r64 <= 25 =>
 addratebit r64 st
 = addstate st (bits2state (rcons (nseq (64*r64-1) false) true)).
proof.
move=> Hr64; rewrite /addratebit /addstate /=.
apply ext_eq => i Hi.
rewrite map2iE //.
case: (i = r64-1) => C; last first.
 rewrite get_setE 1:/# C /= /bits2state get_of_list //.
 rewrite nth_w64L_from_bits 1:/# -cats1.
 case (i < r64-1) => C2.
  rewrite drop_cat size_nseq ifT 1:/# drop_nseq 1:/#.
  rewrite take_cat ifT ?size_nseq 1:/# take_nseq. 
  by rewrite W64_bits2w_nseq0 /#.
 rewrite drop_cat ifF ?size_nseq 1:/# drop_oversize 1:/#.
 by rewrite /= W64_bits2w_nil.
rewrite /bits2state get_of_list // nth_w64L_from_bits 1:/# -cats1.
rewrite get_setE 1:/# ifT 1:/#.
apply W64.ext_eq => k Hk.
rewrite xorwE /=.
case: (k = 63) => C2.
 rewrite /w64_xor_u8 /= pack8wE // get_setE // C2 /=.
 rewrite nth_take // nth_drop // 1:/# nth_cat ifF.
  by rewrite size_nseq /#.
 rewrite size_nseq C /= lez_maxr 1:/# of_intE /int2bs /mkseq -iotaredE /=.
 pose X:= (_ = 0).
 by have ->{X}/=: X=true by smt().
rewrite /w64_xor_u8 /= pack8wE // get_setE // eq_sym.
rewrite C drop_cat ifT ?size_nseq 1:/# drop_nseq 1:/#.
rewrite take_cat ?size_nseq ifF 1:/#.
pose X:= 64 - _.
have ->{X}: X=(size [true]) by smt().
rewrite take_size get_bits2w 1:// nth_cat ifT ?size_nseq 1:/# nth_nseq 1:/# /=.
case: (k %/ 8 = 7) => E.
 rewrite W8u8.get_bits8 // E xorwE.
 have Emod: k %% 8 <> 7 by smt().
 have ->: (W8.of_int 128).[k %% 8] = false.
  by rewrite of_intE /int2bs /mkseq -iotaredE /= /bits2w initiE 1:/# /= /#.
 smt().
by rewrite get_unpack8 1:/# W8u8.get_bits8.
qed.

lemma size_pad10star1 r len:
 0 < r =>
 0 <= len %% r <= r-2 =>
 size (pad10star1 r len)
 = r - (len %% r).
proof.
move=> Hr Hlen.
rewrite /pad10star1 /= size_rcons size_nseq lez_maxr 1:/#.
rewrite -modzDml -modzNm -modzDl /#.
qed.

(*
lemma size_pad10star1 r len:
 0 < r =>
 0 <= len <= r-2 =>
 size (pad10star1 r len)
 = r - (len %% r).
proof.
move=> Hr Hlen.
by rewrite /pad10star1 /= size_rcons size_nseq lez_maxr /#.
qed.
*)

lemma nosmt pad10star1_modr r64 len8 mbits_size:
 0 < r64 =>
 pad10star1 (64*r64) (8*len8 + mbits_size)
 = pad10star1 (64*r64) (8 * (len8 %% (8*r64)) + mbits_size).
proof.
move=> Hr; rewrite /pad10star1; congr; congr; congr.
have ->: -(8 * len8 + mbits_size) - 2 = - (8 * len8 + (mbits_size + 2)) by ring.
rewrite -modzNm -modzDml {1}(:64*r64=8*(8*r64)) 1:/# -mulz_modr // modzNm /#.
qed.

lemma nosmt chunk_padded r64 bs mbits:
 0 < r64 =>
 size mbits <= 6 =>
 chunk (64*r64) (bytes_to_bits bs ++ mbits ++ pad10star1 (64*r64) (8*size bs + size mbits))
 = chunk (64*r64) (bytes_to_bits bs)
   ++ [chunkremains (64*r64) (bytes_to_bits bs) ++ mbits ++ pad10star1 (64*r64) (8*(size bs%%(8*r64)) + size mbits)].
proof.
move => Hr64 Hmbits; rewrite -catA chunk_cat' 1:/#; congr.
rewrite chunk1 1:/#.
 rewrite !size_cat size_chunkremains size_bytes_to_bits size_pad10star1 1:/#; first smt(size_ge0).
 rewrite (:64*r64=8*r64*8) 1:/#.
 have [_ B]:= divmod_mul (8*r64) 8 (size bs) (size mbits) _ _; smt(size_ge0).
by rewrite !catA; congr; congr; apply pad10star1_modr.
qed.

(*
search chunkremains.
lemma chunkify_cat' ['a]:
   forall (n : int) (l1 l2 : 'a list),
     0 < n =>
     chunkify n (l1 ++ l2) = chunk n l1 ++ chunkify n (chunkremains n l1 ++ l2).
*)
(*
lemma chunk_padded' r64 bs mbits:
 0 < r64 =>
 size mbits <= 6 =>
 chunk (64*r64) (bytes_to_bits bs ++ mbits ++ pad10star1 (64*r64) (8*size bs + size mbits))
 = chunk (64*r64) (bytes_to_bits bs)
   ++ [chunkremains (64*r64) (bytes_to_bits bs) ++ mbits ++ pad10star1 (64*r64) (8*size bs + size mbits)].
proof.
move => Hr64 Hmbits; rewrite -catA chunk_cat' 1:/#; congr.
rewrite chunk1 1:/#.
 rewrite !size_cat size_chunkremains size_bytes_to_bits size_pad10star1 1:/#; first smt(size_ge0).
 rewrite (:64*r64=8*r64*8) 1:/#.
 have [_ B]:= divmod_mul (8*r64) 8 (size bs) (size mbits) _ _; smt(size_ge0).
smt(catA).
qed.
*)

lemma pad10star1_split r l n:
 0 < r =>
 size l <= r-2 =>
 n = size  l =>
 l ++ pad10star1 r n
 = xorbits (rcons l true ++ nseq (r - size l - 1) false)
           (rcons (nseq (r-1) false) true).
proof.
have Hsz_ge0 := size_ge0 <:bool>.
move => Hr Hsz ->; apply (eq_from_nth false).
 by rewrite size_map2 !size_cat !size_rcons !size_nseq size_pad10star1 /#.
move=> i.
pose S:= size _; have ->{S}: S = r. 
 rewrite /S size_cat size_pad10star1 // 2:/#.
 by rewrite modz_small /#.
move=> Hi.
rewrite /xorbits (nth_map2 false false).
 smt(size_rcons size_nseq size_cat).
rewrite nth_cat.
case: (i < size l) => C1.
 rewrite -cats1 -!catA nth_cat C1 /= nth_rcons ifT.
  by rewrite size_nseq /#.
 by rewrite nth_nseq /#.
rewrite -cats1 -catA nth_cat C1.
rewrite /pad10star1 /=.
case: (i-size l<>0) => C2 /=.
 rewrite nth_nseq 1:/# addFb nth_rcons.
 have ->: ((- size l)-2) %% r = r-size l-2.
  by rewrite -modzDl /#.
 rewrite size_nseq lez_maxr 1:/#.
 case: (i - size l - 1 < r - size l - 2) => C3;
  smt(nth_nseq nth_rcons size_nseq).
rewrite nth_rcons nth_nseq; smt(size_nseq size_ge0).
qed.

(*
op keccak1600_absorb_op (r64: int, suffix: byte, m: bytes): state =
 addratebit
  r64
  (state_absorb (state_absorb_iblocks r64 m)
                (rcons (chunkremains (8*r64) m) suffix)).
*)
lemma bits2state_cat_nseq0 n bs:
 bits2state (bs ++ nseq n false) = bits2state bs.
proof.
rewrite /bits2state.
admit.
qed.

lemma bits2bytes2state bs:
 bits2state bs = bytes2state (bytes_from_bits bs).
admitted.

lemma addstate_last (st:state) r64 mbits bs suffix:
 0 < r64 <= 25 =>
 size mbits <= 6 =>
 suffix = W8.bits2w (rcons mbits true) =>
 addstate st (bits2state (chunkremains (64*r64) (bytes_to_bits bs) ++ mbits ++ pad10star1 (64*r64) (8*(size bs %% (8*r64)) + size mbits)))
 = addratebit r64 (addstate st (bytes2state (rcons (chunkremains (8*r64) bs) suffix))).
proof.
move=> Hr64 Hmbits Hsuffix.
rewrite pad10star1_split 1:/#.
  by rewrite size_cat size_chunkremains size_bytes_to_bits /#.
 by rewrite size_cat size_chunkremains size_bytes_to_bits /#.
rewrite -addstate_xorbits. 
 rewrite size_cat !size_rcons !size_cat !size_nseq size_chunkremains size_bytes_to_bits; smt(size_ge0).
rewrite addstateA -addratebit_addstate //; congr; congr.
rewrite bits2state_cat_nseq0 -(bits2state_cat_nseq0 (7-size mbits)) bits2bytes2state.
pose L := _ ++ _.
have ->: L = bytes_to_bits (rcons (chunkremains (8 * r64) bs) suffix).
 rewrite /L -!cats1 bytes_to_bits_cat /chunkremains bytes_to_bits_drop -!catA; congr.
  by congr; rewrite size_bytes_to_bits /#.
 rewrite !catA bytes_to_bits_cons bytes_to_bits_nil cats0.
 rewrite Hsuffix W8_bits2wK' ?size_rcons 1:/# cats1; congr; smt().
by rewrite bytes_to_bitsK.
qed.


lemma nth_chunk ['a] k (l: 'a list) i:
 0 < k =>
 k %| size l =>
 nth [] (chunk k l) i =
 take k (drop (k*i) l).
proof.
admitted.


print Keccak1600.
(*
  proc sponge1600_pad10star1(r : int, m : bool list, d : int) : bool list = {
*)


lemma sponge_correct _r64 _m _suffix _mbits _len8:
 0 < _len8 => (* this can be removed by an extra case... *)
 size _mbits <= 6 =>
 W8.w2bits _suffix = rcons _mbits true =>
 hoare [ Keccak1600.sponge1600_pad10star1:
         r = 64*_r64 /\ m = bytes_to_bits _m ++ _mbits /\ d = 8*_len8
         ==> res = bytes_to_bits (keccak1600_op _r64 _suffix _m _len8 )].
proof.
move=> Hlen8 Hmbits Hsuffix; proc; simplify.
seq 6: (#pre /\ s = keccak1600_absorb_op _r64 _suffix _m).
print keccak1600_absorb_op.
 while (#pre /\ n = size m %/ 8 + 1 /\ 0 <= i <= n /\
        pl = chunk r (bytes_to_bits _m ++ _mbits ++ pad10star1 r (8 * (size _m) + size _mbits)) /\
        s <- state_absorb_iblocks r64 
 admit.
exlim (keccak1600_absorb_op _r64 _suffix _m) => st.
splitwhile 2: (size z + d < d).
seq 2: (#[:-2]pre /\ s = (iter (d %/ r) KECCAK_F1600 st) /\ size z = r * (d %/ r)) => //.
 admit.
admit.
qed.



