(******************************************************************************
   Keccak1600_Spec.ec:

   Properties of the Keccak1600 specification.

    - functionol byte-based specification
    - correctness wrt imperative spec [FIPS202_SHA3.ec]

******************************************************************************)
require import AllCore List Int IntDiv.

require StdOrder.
import StdOrder.IntOrder.

require import Keccakf1600_Spec.
require import FIPS202_SHA3_Spec.

require BitEncoding.
import BitEncoding.BitChunking.

import EclibExtra.


op bytes2state (bs: bytes): state =
 Array25.of_list W64.zero (w64L_from_bytes bs).

op state2bytes (st: state): bytes =
 w64L_to_bytes (to_list st).

lemma size_state2bytes s:
 size (state2bytes s) = 200.
proof.
by rewrite size_w64L_to_bytes Array25.size_to_list.
qed.

lemma bits2bytes2state l:
 bits2state l = bytes2state (bytes_from_bits l).
proof.
by rewrite /bytes2state w64L_from_bytes_from_bits /#.
qed.

lemma state2bytes2bits s:
 bytes_to_bits (state2bytes s) = state2bits s.
proof.
by rewrite /state2bytes /state2bits w64L_to_bytes_to_bits.
qed.

lemma bytes2bits2state l:
 bits2state (bytes_to_bits l) = bytes2state l.
proof.
rewrite /bits2state /bytes2state tP => i Hi.
by rewrite w64L_from_bits_from_bytes.
qed.

(* sometimes is convenient to have a byte-view of the state... *)
(*from JExtr*) require import WArray200.

abbrev stbytes (st: state) : WArray200.t =
 WArray200.init64 ("_.[_]" st).
abbrev stwords (st200: WArray200.t) : state =
 Array25.init (WArray200.get64 st200).

lemma stbytesK st:
 stwords (stbytes st) = st.
proof.
rewrite tP => i Hi.
rewrite initiE //= get64E /=.
apply W8u8.wordP => k Hk.
rewrite pack8bE //= bits8E initiE 1:/# /= initiE 1:/# /= bits8E.
by apply W8.init_ext => x Hx /#.
qed.

lemma stwordsK st:
 stbytes (stwords st) = st.
proof.
rewrite tP => i Hi.
rewrite initiE //= initiE 1:/# /= get64E pack8bE 1:/#.
by rewrite initiE 1:/# /= /#.
qed.

lemma stbytes_inj s1 s2:
 stbytes s1 = stbytes s2 => s1 = s2.
proof.
by move=> E; rewrite -(stbytesK s1) E stbytesK.
qed.

abbrev bytes2stbytes l = WArray200.of_list l.

lemma bytes2stbytesP l:
 stwords (bytes2stbytes l) = bytes2state l.
proof.
apply stbytes_inj.
rewrite stwordsK tP => i Hi.
rewrite get_of_list // initiE //=.
rewrite initiE 1:/# /= nth_w64L_from_bytes 1:/#.
rewrite pack8bE 1:/# get_of_list 1:/#.
by rewrite nth_take // 1:/# nth_drop 1..2:/# /#.
qed.

op addstbytes = WArray200.map2 W8.(`^`).

lemma stbytes_addstate st1 st2:
 stbytes (addstate st1 st2)
 = addstbytes (stbytes st1) (stbytes st2).
proof.
rewrite tP => i Hi.
by rewrite map2iE // initiE //= map2iE 1:/# !initiE /#.
qed.


(**************************************************************
     Functional Byte-oriented specification of KECCAK1600
***************************************************************)

(* the padding [pad10star1] is decomposed on a start-byte (which
 includes domain-separation bits) and a trailing bit  *)

op addratebit8 r8 (st: WArray200.t) =
 st.[r8-1 <- st.[r8-1] `^` W8.of_int 128].

op addratebit r8 (st: state) =
 stwords (addratebit8 r8 (stbytes st)).

lemma addratebitE (r8 : int) (st : state):
 0 < r8 && r8 <= 200 =>
 addratebit r8 st
 = addstate st (bytes2state (rcons (nseq (r8 - 1) W8.zero) (W8.of_int 128))).
proof.
move=> Hr.
apply stbytes_inj; rewrite /addratebit stwordsK tP => i Hi.
pose st2:= bytes2state _.
rewrite -{-1}(stbytesK st) -(stbytesK st2) stbytes_addstate.
rewrite get_setE 1:/# map2iE // /st2 -bytes2stbytesP !stwordsK.
case: (i=r8-1) => E.
 rewrite E; congr.
 by rewrite get_of_list 1:/#
 nth_rcons size_nseq ifF 1:/# ifT 1:/#.
rewrite !get_of_list 1:/# nth_rcons size_nseq ler_maxr 1:/#.
case: (i < r8-1) => C.
 by rewrite nth_nseq /#.
by rewrite ifF /#.
qed.

(* Absorbs a byte-list [m] into the state *)
op stateabsorb st m = addstate st (bytes2state m).

(* Absorbs all the intermediate (rate-sized) blocks *)
op stateabsorb_iblocks (ml: bytes list) st: state =
 foldl (fun st m => keccak_f1600_op (stateabsorb st m)) st ml.

(* Absorbs the last block (where [size m < r8]) *)
op stateabsorb_last (r8: int, m: bytes, trail: byte) st: state =
 addratebit r8 (stateabsorb st (rcons m trail)).

(* Full absorb function *)
op ABSORB1600 (r8: int, m: bytes, trail: byte): state =
 stateabsorb_last r8 (chunkremains r8 m) trail (stateabsorb_iblocks (chunk r8 m) st0).

(* Squeezes [len] bytes from [st] *)
op statesqueeze (st: state) (len: int) =
 take len (state2bytes st).

op statesqueeze_i r8 st i =
 statesqueeze (st_i st i) r8.

(* Full squeeze of [outlen8] bytes *)
op SQUEEZE1600 (r8: int, st: state, outlen8: int): bytes =
 (* intermediate blocks *)
 flatten (map (statesqueeze_i r8 st) (iota_ 1 ((outlen8-1) %/ r8)))
 (* last block *)
 ++ statesqueeze (st_i st ((outlen8-1) %/ r8 + 1))
                  (outlen8 - max 0 ((outlen8-1) %/ r8 * r8)).

(* The Sponge construction *)
op KECCAK1600 (r8: int, m: bytes, trail: byte, outlen8: int): bytes =
 SQUEEZE1600 r8 (ABSORB1600 r8 m trail) outlen8.

(** DOMAIN-SEPARATION bits *)
(* Remark: DS_BYTE includes first bit of [pad10star1] *)
op SHA_DS_BYTE = W8.of_int 06.
op SHAKE_DS_BYTE = W8.of_int 31.
op RAWSHAKE_DS_BYTE = W8.of_int 07.

(* Byte-level functional specification of SHA/SHAKE family *)
op SHA3_224 (m: bytes): bytes =
 KECCAK1600 144 m SHA_DS_BYTE 28.
op SHA3_256 (m: bytes): bytes =
 KECCAK1600 136 m SHA_DS_BYTE 32.
op SHA3_384 (m: bytes): bytes =
 KECCAK1600 104 m SHA_DS_BYTE 48.
op SHA3_512 (m: bytes): bytes =
 KECCAK1600 72 m SHA_DS_BYTE 64.
op SHAKE128 (m: bytes, outlen8:int): bytes =
 KECCAK1600 168 m SHAKE_DS_BYTE outlen8.
op SHAKE256 (m: bytes, outlen8:int): bytes =
 KECCAK1600 136 m SHAKE_DS_BYTE outlen8.
op RAWSHAKE128 (m: bytes, outlen8:int): bytes =
 KECCAK1600 168 m RAWSHAKE_DS_BYTE outlen8.
op RAWSHAKE256 (m: bytes, outlen8:int): bytes =
 KECCAK1600 136 m RAWSHAKE_DS_BYTE outlen8.

(* For XOFs, it is also convenient to have access to absorb/squeeze *)
op SHAKE128_ABSORB m = ABSORB1600 168 m SHAKE_DS_BYTE.
op SHAKE128_SQUEEZE_BLOCK st = 
 let st' = keccak_f1600_op st in (st', statesqueeze st' 168).

op SHAKE256_ABSORB m = ABSORB1600 136 m SHAKE_DS_BYTE.
op SHAKE256_SQUEEZE_BLOCK st = 
 let st' = keccak_f1600_op st in (st', statesqueeze st' 138).

op RAWSHAKE128_ABSORB m = ABSORB1600 168 m RAWSHAKE_DS_BYTE.
op RAWSHAKE128_SQUEEZE_BLOCK st = 
 let st' = keccak_f1600_op st in (st', statesqueeze st' 168).

op RAWSHAKE256_ABSORB m = ABSORB1600 136 m RAWSHAKE_DS_BYTE.
op RAWSHAKE256_SQUEEZE_BLOCK st = 
 let st' = keccak_f1600_op st in (st', statesqueeze st' 138).

(* TODO: relate SHAKE128 with SHAKE128_ABSORB and SHAKE128_SQUEZZE_BLOCK, etc. *)

(**************************************************************
     Correctness wrt bit-oriented functional specification
***************************************************************)

op DS_BYTE_ok ds_bits ds_byte =
 size ds_bits <= 6 /\ ds_byte = W8.bits2w (rcons ds_bits true).

lemma SHA_DS_BYTE_ok:
 DS_BYTE_ok SHA_DS_BITS SHA_DS_BYTE.
proof.
rewrite /DS_BYTE_ok /SHA_DS_BYTE /SHA_DS_BITS //=.
apply (W8.all_eq_eq).
by rewrite /W8.of_int /int2bs /mkseq -iotaredE /all_eq /=.
qed.

lemma SHAKE_DS_BYTE_ok:
 DS_BYTE_ok SHAKE_DS_BITS SHAKE_DS_BYTE.
proof.
rewrite /DS_BYTE_ok /SHAKE_DS_BYTE /SHAKE_DS_BITS //=.
apply (W8.all_eq_eq).
by rewrite /W8.of_int /int2bs /mkseq -iotaredE /all_eq /=.
qed.

lemma RAWSHAKE_DS_BYTE_ok:
 DS_BYTE_ok RAWSHAKE_DS_BITS RAWSHAKE_DS_BYTE.
proof.
rewrite /DS_BYTE_ok /RAWSHAKE_DS_BYTE /RAWSHAKE_DS_BITS //=.
apply (W8.all_eq_eq).
by rewrite /W8.of_int /int2bs /mkseq -iotaredE /all_eq /=.
qed.

lemma split_padded_rcons r8 m ds_bits:
 0 < r8 =>
 size ds_bits <= 6 =>
 split_padded (8*r8) (bytes_to_bits m ++ ds_bits)
 = rcons (chunk (8*r8) (bytes_to_bits m))
    (chunkremains (8*r8) (bytes_to_bits m) ++ ds_bits
     ++ pad10star1 (8*r8) (size (bytes_to_bits m ++ ds_bits))).
proof.
move=> Hr Hsz.
rewrite -!catA chunk_cat' 1:/# -cats1 !catA; congr.
by rewrite chunk_size 1:/# !size_cat // size_chunkremains size_pad10star1
  1:/# size_bytes_to_bits; smt(size_ge0).
qed.

lemma absorb_iblocks r r8 m:
 0 < r =>
 r = 8 * r8 =>
 foldl (fun s b => keccak_f1600_op (addstate s b))
       st0
       (map bits2state (chunk r (bytes_to_bits m))) 
 = stateabsorb_iblocks (chunk r8 m) st0.
proof.
move=> Hr Er.
rewrite /state_absorbiblocks Er.
rewrite chunk_bytes_to_bits.
rewrite -map_comp foldl_map.
apply eq_foldl => //.
move=> s l /=; congr.
rewrite /stateabsorb; congr.
by rewrite /(\o) /= bytes2bits2state.
qed.

lemma keccak1600_absorb_opE r r8 m ds_bits ds_byte:
 0 < r <= 1600 =>
 r = 8*r8 =>
 DS_BYTE_ok ds_bits ds_byte =>
 keccak1600_absorb_op r (bytes_to_bits m ++ ds_bits)
 = keccak_f1600_op (ABSORB1600 r8 m ds_byte).
proof.
move=> Hr Hr8 [Hdsbits Hdsbyte].
rewrite /keccak1600_absorb_op /ABSORB1600.
(* intermediate blocks *)
rewrite Hr8 split_padded_rcons 1..2:/# map_rcons.
rewrite foldl_rcons /= /stateabsorb_last; congr.
rewrite (absorb_iblocks _ r8) 1..2:/#.
(* lastblock *)
pose ST:= stateabsorb_iblocks _ _.
have E8: 8*size m %/ (8*r8) * (8*r8)
        = 8*(size m %/ r8 * r8) by smt().
rewrite /chunkremains !size_bytes_to_bits E8.
rewrite -bytes_to_bits_drop -cats1 /stateabsorb -bytes2bits2state.
rewrite bytes_to_bits_cat /pad10star1 -cat1s !catA -cats1 bits2state_cat addstateA !catA cat_nseq;
 1..2:smt(size_ge0).
rewrite !size_cat !size_bytes_to_bits !size_drop;
 1: smt(size_ge0).
rewrite ler_maxr /=; 1:smt(size_ge0).
have ->: size m - size m %/ r8 * r8
         = size m %% r8 by smt().
have ->: (- (8 * size m + size ds_bits)) - 2
         = - (8*size m + size ds_bits + 2) by smt().
rewrite modNz //=; 1..2:smt(size_ge0).
have ->: (8 * size m + size ds_bits + 1) %% (8 * r8)
         = (size m * 8 + (size ds_bits + 1))%%(r8*8)
 by smt().
have [_ ->]:= divmod_mul r8 8 (size m) (size ds_bits+1) _ _; 1..2:smt(size_ge0).
have ->: 8 * (size m %% r8) + size ds_bits + 1 + (8 * r8 - 1 - (size m %% r8 * 8 + (size ds_bits + 1)))
         = 8*r8 - 1 by smt().
rewrite addratebitE 1:/#; congr.
 congr. 
 rewrite bits2bytes2state -catA bytes_from_bits_cat.
  by rewrite size_bytes_to_bits /#.
 rewrite bytes_to_bitsK -bytes_to_bits_cat bits2bytes2state bytes_to_bitsK; congr; congr.
 rewrite bytes_from_bits_cons.
  rewrite size_cat; smt(size_ge0).
 by rewrite take_oversize 1:size_cat // 1:/# drop_oversize 1:size_cat 1:/# bytes_from_bits_nil cats1 /#.
rewrite bits2bytes2state; congr.
rewrite (:8*r8-1=8*(r8-1)+7) 1:/#.
rewrite -cat_nseq // 1:/# -catA -cats1.
rewrite bytes_from_bits_cat.
 by rewrite size_nseq ler_maxr /#.
congr.
 by rewrite bytes_from_bits_nseq0 /#.
rewrite -mkseq_nseq /mkseq -iotaredE /= /bytes_from_bits chunkify_chunk // chunk_size //=. 
apply W8.all_eq_eq; rewrite /all_eq /=.
by rewrite of_intE /int2bs /mkseq -iotaredE /=.
qed.

lemma keccak1600_squeeze_opE r r8 st outlen outlen8:
 0 < r <= 1600 =>
 r = 8*r8 =>
 outlen = 8*outlen8 =>
 keccak1600_squeeze_op r (keccak_f1600_op st) outlen
 = bytes_to_bits (SQUEEZE1600 r8 st outlen8).
proof.
move=> Hr Hr8 Ho8.
case: (outlen <= 0) => Hout.
 rewrite /keccak1600_squeeze_op take_le0 1:/# //.
 rewrite /SQUEEZE1600 iota0 1:/#  flatten_nil /=.
 by rewrite /statesqueeze take_le0 /#.
rewrite /keccak1600_squeeze_op /SQUEEZE1600.
rewrite bytes_to_bits_cat iotaSr 1:/#.
rewrite map_rcons flatten_rcons take_cat.
pose ll:= flatten _.
have size_ll: size ll = (outlen - 1) %/ r * r.
 rewrite (size_flatten' r).
  move=> x /mapP [y [Hy]].
  rewrite /(\o) /= => ->.
  by rewrite size_take' 1:/# ifT ?size_state2bits 1:/#.
 by rewrite size_map /(\o) /= size_iota ler_maxr /#.
rewrite ifF ?size_ll 1:/#.
have E: (outlen - 1) %/ r = (outlen8-1) %/ r8.
 by rewrite Ho8 mulrC Hr8 divzMr // 1:/# divzMDl //=.
congr.
 rewrite (:iota_ 1 = iota_ (1+0)) 1:/# iota_addl -map_comp.
 rewrite /ll E bytes_to_bits_flatten; congr.
 rewrite -map_comp.
 apply eq_in_map => x /@mem_iota /> *.
 rewrite /(\o) /= /statesqueeze_i addrC /state_squeeze bytes_to_bits_take; congr.
 rewrite state2bytes2bits; congr.
 by rewrite /st_i iterSr //.
pose L:=outlen - _.
rewrite /statesqueeze bytes_to_bits_take.
rewrite /(\o) /= state2bytes2bits.
rewrite take_take'; congr.
 rewrite /L ler_maxr 1:/#.
 by rewrite ler_minl /#.
congr.
rewrite /st_i.
have ->: (outlen - 1) %/ r = (outlen8-1) %/ r8.
 by rewrite Ho8 mulrC Hr8 divzMr // 1:/# divzMDl //=.
by rewrite iterSr /#.
qed.

lemma keccak1600_opE c r8 m ds_bits ds_byte outlen outlen8:
 0 <= c < 1600 =>
 1600 - c = 8*r8 =>
 outlen = 8*outlen8 =>
 DS_BYTE_ok ds_bits ds_byte =>
 keccak1600_op c (bytes_to_bits m ++ ds_bits) outlen
 = bytes_to_bits (KECCAK1600 r8 m ds_byte outlen8).
proof.
move=> *; rewrite /KECCAK1600 /keccak1600_op /keccak1600_sponge_op.
rewrite (keccak1600_absorb_opE _ r8 _ _ ds_byte) // 1:/#.
by apply keccak1600_squeeze_opE => // /#.
qed.

lemma sha3_224_opE m:
 sha3_224_op (bytes_to_bits m)
 = bytes_to_bits (SHA3_224 m).
proof.
apply keccak1600_opE => //.
exact SHA_DS_BYTE_ok.
qed.

lemma sha3_256_opE m:
 sha3_256_op (bytes_to_bits m)
 = bytes_to_bits (SHA3_256 m).
proof.
apply keccak1600_opE => //.
exact SHA_DS_BYTE_ok.
qed.

lemma sha3_384_opE m:
 sha3_384_op (bytes_to_bits m)
 = bytes_to_bits (SHA3_384 m).
proof.
apply keccak1600_opE => //.
exact SHA_DS_BYTE_ok.
qed.

lemma sha3_512_opE m:
 sha3_512_op (bytes_to_bits m)
 = bytes_to_bits (SHA3_512 m).
proof.
apply keccak1600_opE => //.
exact SHA_DS_BYTE_ok.
qed.

lemma shake128_opE m outlen outlen8:
 outlen = 8*outlen8 =>
 shake128_op (bytes_to_bits m) outlen
 = bytes_to_bits (SHAKE128 m outlen8).
proof.
move=> H; apply keccak1600_opE => //.
exact SHAKE_DS_BYTE_ok.
qed.

lemma shake256_opE m outlen outlen8:
 outlen = 8*outlen8 =>
 shake256_op (bytes_to_bits m) outlen
 = bytes_to_bits (SHAKE256 m outlen8).
proof.
move=> H; apply keccak1600_opE => //.
exact SHAKE_DS_BYTE_ok.
qed.

lemma rawshake128_opE m outlen outlen8:
 outlen = 8*outlen8 =>
 rawshake128_op (bytes_to_bits m) outlen
 = bytes_to_bits (RAWSHAKE128 m outlen8).
proof.
move=> H; apply keccak1600_opE => //.
exact RAWSHAKE_DS_BYTE_ok.
qed.

lemma rawshake256_opE m outlen outlen8:
 outlen = 8*outlen8 =>
 rawshake256_op (bytes_to_bits m) outlen
 = bytes_to_bits (RAWSHAKE256 m outlen8).
proof.
move=> H; apply keccak1600_opE => //.
exact RAWSHAKE_DS_BYTE_ok.
qed.


(**************************************************************
     Correctness of (bit-level) FIPS202 standard
   wrt byte-level functional spec.
***************************************************************)

hoare fips202_KECCAK1600_h _ds_bits _r8 _ds_byte _m _outlen8:
 Keccak1600.keccak1600
 : c = 1600 - 8*_r8 /\
   0 < _r8 <= 200 /\
   m = bytes_to_bits _m ++ _ds_bits /\
   DS_BYTE_ok _ds_bits _ds_byte /\
   outlen = 8*_outlen8
   ==> res = bytes_to_bits (KECCAK1600 _r8 _m _ds_byte _outlen8).
proof.
conseq (keccak1600_h (1600-8*_r8) (bytes_to_bits _m++_ds_bits) (8*_outlen8)).
 by move=> &m H => /> /#.
smt(keccak1600_opE).
qed.

phoare fips202_KECCAK1600_ph _ds_bits _r8 _ds_byte _m _outlen8:
 [ Keccak1600.keccak1600
 : c = 1600 - 8*_r8 /\
   0 < _r8 <= 200 /\
   m = bytes_to_bits _m ++ _ds_bits /\
   DS_BYTE_ok _ds_bits _ds_byte /\
   outlen = 8*_outlen8
   ==> res = bytes_to_bits (KECCAK1600 _r8 _m _ds_byte _outlen8)
 ] = 1%r.
proof.
by conseq keccak1600_ll (fips202_KECCAK1600_h _ds_bits _r8 _ds_byte _m _outlen8) => /#.
qed.

hoare fips202_SHA3_224_h _m:
 Keccak1600.sha3_224
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_224 _m).
proof.
conseq (sha3_224_h (bytes_to_bits _m)).
smt(sha3_224_opE).
qed.

phoare fips202_SHA3_224_ph _m:
 [ Keccak1600.sha3_224
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_224 _m)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_224 by proc; call keccak1600_ll.
by conseq Hll (fips202_SHA3_224_h _m).
qed.

hoare fips202_SHA3_256_h _m:
 Keccak1600.sha3_256
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_256 _m).
proof.
conseq (sha3_256_h (bytes_to_bits _m)).
smt(sha3_256_opE).
qed.

phoare fips202_SHA3_256_ph _m:
 [ Keccak1600.sha3_256
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_256 _m)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_256 by proc; call keccak1600_ll.
by conseq Hll (fips202_SHA3_256_h _m).
qed.

hoare fips202_SHA3_384_h _m:
 Keccak1600.sha3_384
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_384 _m).
proof.
conseq (sha3_384_h (bytes_to_bits _m)).
smt(sha3_384_opE).
qed.

phoare fips202_SHA3_384_ph _m:
 [ Keccak1600.sha3_384
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_384 _m)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_384 by proc; call keccak1600_ll.
by conseq Hll (fips202_SHA3_384_h _m).
qed.

hoare fips202_SHA3_512_bh _m:
 Keccak1600.sha3_512
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_512 _m).
proof.
conseq (sha3_512_h (bytes_to_bits _m)).
smt(sha3_512_opE).
qed.

phoare fips202_SHA3_512_ph _m:
 [ Keccak1600.sha3_512
 : m = bytes_to_bits _m ==> res = bytes_to_bits (SHA3_512 _m)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.sha3_512 by proc; call keccak1600_ll.
by conseq Hll (fips202_SHA3_512_bh _m).
qed.

hoare fips202_SHAKE128_h _m _len8:
 Keccak1600.shake128
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (SHAKE128 _m _len8).
proof.
conseq (shake128_h (bytes_to_bits _m) (8*_len8)).
smt(shake128_opE).
qed.

phoare fips202_SHAKE128_ph _m _len8:
 [ Keccak1600.shake128
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (SHAKE128 _m _len8)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.shake128 by proc; call keccak1600_ll.
by conseq Hll (fips202_SHAKE128_h _m _len8).
qed.

hoare fips202_SHAKE256_h _m _len8:
 Keccak1600.shake256
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (SHAKE256 _m _len8).
proof.
conseq (shake256_h (bytes_to_bits _m) (8*_len8)).
smt(shake256_opE).
qed.

phoare fips202_SHAKE256_ph _m _len8:
 [ Keccak1600.shake256
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (SHAKE256 _m _len8)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.shake256 by proc; call keccak1600_ll.
by conseq Hll (fips202_SHAKE256_h _m _len8).
qed.

hoare fips202_RAWSHAKE128_h _m _len8:
 Keccak1600.rawSHAKE128
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (RAWSHAKE128 _m _len8).
proof.
conseq (rawshake128_h (bytes_to_bits _m) (8*_len8)).
smt(rawshake128_opE).
qed.

phoare fips202_RAWSHAKE128_ph _m _len8:
 [ Keccak1600.rawSHAKE128
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (RAWSHAKE128 _m _len8)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.rawSHAKE128 by proc; call keccak1600_ll.
by conseq Hll (fips202_RAWSHAKE128_h _m _len8).
qed.

hoare fips202_RAWSHAKE256_h _m _len8:
 Keccak1600.rawSHAKE256
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (RAWSHAKE256 _m _len8).
proof.
conseq (rawshake256_h (bytes_to_bits _m) (8*_len8)).
smt(rawshake256_opE).
qed.

phoare fips202_RAWSHAKE256_ph _m _len8:
 [ Keccak1600.rawSHAKE256
 : m = bytes_to_bits _m /\ d = 8*_len8 
   ==> res = bytes_to_bits (RAWSHAKE256 _m _len8)
 ] = 1%r.
proof.
have Hll: islossless Keccak1600.rawSHAKE256 by proc; call keccak1600_ll.
by conseq Hll (fips202_RAWSHAKE256_h _m _len8).
qed.

(**************************************************************
     Imperative byte-oriented SPONGE construction
  (a convenient target for implementation correctness proofs)
***************************************************************)

module Keccak1600Bytes = {
 proc absorb(r8: int, inp: bytes, trail: byte): state = {
    var l, lastb, st, i;
    l <- chunk r8 inp;
    st <- st0;
    i <- 0;
    while (i < size l) {
      st <- stateabsorb st (nth [] l i);
      st <- keccak_f1600_op st;
      i <- i + 1;
    }
    lastb <- chunkremains r8 inp;
    st <- stateabsorb st (rcons lastb trail);
    st <- addratebit r8 st;
  return st;
 }
 proc squeeze(r8: int, st: state, outlen: int): bytes = {
   var out_bytes, i;
   out_bytes <- [];
   i <- 1;
   st <- keccak_f1600_op st;
   while (r8*i < outlen) {
     out_bytes <- out_bytes ++ statesqueeze st r8;  
     st <- keccak_f1600_op st;
     i <- i + 1;
   }
   out_bytes <- out_bytes ++ statesqueeze st (outlen - r8*(i-1));
   return out_bytes;
 }
 proc sponge(r8:int, m: bytes, trail: byte, len8: int): bytes = {
   var s, r;
   s <@ absorb(r8, m, trail);
   r <@ squeeze(r8, s, len8);
  return r;
 }
 proc sha3_224(m: bytes): bytes = {
   var r;
   r <@ sponge(144, m, SHA_DS_BYTE, 28);
   return r;
 }
 proc sha3_256(m: bytes): bytes = {
   var r;
   r <@ sponge(136, m, SHA_DS_BYTE, 32);
   return r;
 }
 proc sha3_384(m: bytes): bytes = {
   var r;
   r <@ sponge(104, m, SHA_DS_BYTE, 48);
   return r;
 }
 proc sha3_512(m: bytes): bytes = {
   var r;
   r <@ sponge(72, m, SHA_DS_BYTE, 64);
   return r;
 }
 proc shake128(m: bytes, outlen8: int): bytes = {
   var r;
   r <@ sponge(168, m, SHAKE_DS_BYTE, outlen8);
   return r;
 }
 proc shake256(m: bytes, outlen8: int): bytes = {
   var r;
   r <@ sponge(136, m, SHAKE_DS_BYTE, outlen8);
   return r;
 }
 proc rawshake128(m: bytes, outlen8: int): bytes = {
   var r;
   r <@ sponge(168, m, RAWSHAKE_DS_BYTE, outlen8);
   return r;
 }
 proc rawshake256(m: bytes, outlen8: int): bytes = {
   var r;
   r <@ sponge(136, m, RAWSHAKE_DS_BYTE, outlen8);
   return r;
 }
}.

hoare ABSORB1600_h _r8 _trail _m:
 Keccak1600Bytes.absorb: r8=_r8 /\ trail=_trail /\ inp=_m /\ 0 < _r8 ==> res = ABSORB1600 _r8 _m _trail.
proof.
proc; simplify.
sp 1; seq 3: (#pre /\ st = stateabsorb_iblocks l st0).
 while (#pre /\ 0 <= i <= size l /\
        stateabsorb_iblocks l st0
        = stateabsorb_iblocks (drop i l) st).
  auto => /> &m Hr Hi0 Hi1 IH.
  rewrite size_chunk // => H; split; first smt().
  rewrite IH dropS 1:/#.
  rewrite -(head_behead (drop i{m} _) []) /=. 
   by rewrite -size_eq0 size_drop // size_chunk // /#.
  rewrite /stateabsorb_iblocks /=.
  apply eq_foldl => //.
  rewrite /C nth_chunk // 1:/#. 
  congr; congr.
  rewrite drop_chunk // -nth0_head nth_chunk //=.
   by rewrite size_drop 1:/# ler_maxr /#.
  by rewrite drop0.
 auto => /> *; split.
  by rewrite size_chunk // drop0; smt(size_ge0).
 move=> i st Hi1 _ Hi2.
 have ->: i=size (chunk _r8 _m) by smt().
 by rewrite drop_oversize // /#.
by auto.
qed.

lemma ABSORB1600_ll:
 phoare [ Keccak1600Bytes.absorb: 0 < r8 ==> true ] = 1%r.
proof.
proc; sp 1; simplify.
wp; while (#pre /\ i <= size l) (size l - i).
 by move=> z; auto => /> &m Hr /#.
by auto => /> &m Hr; smt(size_ge0).
qed.

phoare ABSORB1600_ph _r8 _trail _m:
 [ Keccak1600Bytes.absorb
 : r8=_r8 /\ trail=_trail /\ inp=_m /\ 0 < _r8 
 ==> res = ABSORB1600 _r8 _m _trail
 ] = 1%r.
proof. by conseq ABSORB1600_ll (ABSORB1600_h _r8 _trail _m). qed.

hoare SQUEEZE1600_h _r8 _st _len:
 Keccak1600Bytes.squeeze
 : r8=_r8 /\ st=_st /\ outlen=_len 
   /\ 0 < _r8 <= 200
   ==> res = SQUEEZE1600 _r8 _st _len.
proof.
proc; case: (0 < outlen); simplify.
 seq 4: (#[/1,3:]pre /\ 
         out_bytes = flatten (map (statesqueeze_i _r8 _st) (iota_ 1 ((_len-1) %/ _r8))) /\
         st = st_i _st ((_len-1) %/ _r8+1) /\
         i = (_len-1) %/ _r8 + 1).
  while (0 < i <= (_len-1) %/ _r8 + 1 /\
         #[/1,3:]pre /\
         out_bytes = flatten (map (statesqueeze_i _r8 _st) (iota_ 1 (i-1))) /\
         st = st_i _st i).
   auto => /> &m Hi_1 Hi_2 Hr8_1 Hr8_2 *; split; 1:smt().
   split.
    rewrite {3}(:i{m}=i{m}-1+1) 1:/# iotaSr 1:/# /=.
    rewrite map_rcons flatten_rcons; congr.
    by rewrite /statesqueeze_i; congr; smt().
   by rewrite /st_i !iterS /#.
  auto => /> *; split. 
   by rewrite iota0 //= flatten_nil /st_i iter1 /#.
  move => /> i???.
  by have ->//: i=(_len-1)%/_r8+1 by smt().
 auto => /> Hr64_1 Hr64_2 ?.
 rewrite /SQUEEZE1600 ler_maxr 1:/#; congr; congr.
 by rewrite mulzC {1}(divz_eq (_len-1) _r8) /#.
rcondf 4; first by auto => /> /#.
auto => /> *.
rewrite /SQUEEZE1600 iota0 1:/# flatten_nil /=.
by rewrite /statesqueeze !take_le0 /#.
qed.

lemma SQUEEZE1600_ll:
 phoare [ Keccak1600Bytes.squeeze: 0 < r8 ==> true ] = 1%r.
proof.
proc; wp; simplify. 
case: (outlen<0).
 by rcondf 4; auto => /> /#. 
while (0 < r8 /\ 0 < r8*i<=outlen+r8) (outlen - i).
 move=> z; auto => /> &m Hr /#.
by auto => /> &m Hr ? /#.
qed.

phoare SQUEEZE1600_ph _r8 _st _len:
 [ Keccak1600Bytes.squeeze
 : r8=_r8 /\ st=_st /\ outlen=_len /\ 0<_r8 <= 200
   ==> res = SQUEEZE1600 _r8 _st _len
 ] = 1%r.
proof.
by conseq SQUEEZE1600_ll (SQUEEZE1600_h _r8 _st _len).
qed.

hoare KECCAK1600_h _r8 _trail _m _len8:
 Keccak1600Bytes.sponge
 : r8=_r8 /\ trail=_trail /\ m=_m /\ len8=_len8 
   /\ 0 < _r8 <= 200
   ==> res = KECCAK1600 _r8 _m _trail _len8.
proof.
proc.
ecall (SQUEEZE1600_h r8 s len8).
ecall (ABSORB1600_h r8 trail m).
by auto => />.
qed.

phoare KECCAK1600_ll:
 [ Keccak1600Bytes.sponge: 0 < r8 ==> true ] = 1%r.
proof.
proc.
call SQUEEZE1600_ll.
call ABSORB1600_ll.
by auto => />.
qed.

phoare KECCAK1600_ph _r8 _trail _m _len8:
 [ Keccak1600Bytes.sponge
   : r8=_r8 /\ trail=_trail /\ m=_m /\ len8=_len8 
     /\ 0 < _r8 <= 200
     ==> res = KECCAK1600 _r8 _m _trail _len8
 ] = 1%r.
proof. by conseq KECCAK1600_ll (KECCAK1600_h _r8 _trail _m _len8). qed.

hoare SHA3_224_h _m:
 Keccak1600Bytes.sha3_224
 : m = _m
   ==> res = SHA3_224 _m.
proof. by proc; ecall (KECCAK1600_h 144 SHA_DS_BYTE m 28). qed.

lemma SHA3_224_ll: islossless Keccak1600Bytes.sha3_224.
proof. by proc; call KECCAK1600_ll. qed.

phoare SHA3_224_ph _m:
 [ Keccak1600Bytes.sha3_224
   : m = _m
     ==> res = SHA3_224 _m
 ] = 1%r.
proof. by conseq SHA3_224_ll (SHA3_224_h _m). qed.

hoare SHA3_256_h _m:
 Keccak1600Bytes.sha3_256
 : m = _m
   ==> res = SHA3_256 _m.
proof. by proc; ecall (KECCAK1600_h 136 SHA_DS_BYTE m 32). qed.

lemma SHA3_256_ll: islossless Keccak1600Bytes.sha3_256.
proof. by proc; call KECCAK1600_ll. qed.

phoare SHA3_256_ph _m:
 [ Keccak1600Bytes.sha3_256
   : m = _m
     ==> res = SHA3_256 _m
 ] = 1%r.
proof. by conseq SHA3_256_ll (SHA3_256_h _m). qed.

hoare SHA3_384_h _m:
 Keccak1600Bytes.sha3_384
 : m = _m
   ==> res = SHA3_384 _m.
proof. by proc; ecall (KECCAK1600_h 104 SHA_DS_BYTE m 48). qed.

lemma SHA3_384_ll: islossless Keccak1600Bytes.sha3_384.
proof. by proc; call KECCAK1600_ll. qed.

phoare SHA3_384_ph _m:
 [ Keccak1600Bytes.sha3_384
   : m = _m
     ==> res = SHA3_384 _m
 ] = 1%r.
proof. by conseq SHA3_384_ll (SHA3_384_h _m). qed.

hoare SHA3_512_h _m:
 Keccak1600Bytes.sha3_512
 : m = _m
   ==> res = SHA3_512 _m.
proof. by proc; ecall (KECCAK1600_h 72 SHA_DS_BYTE m 64). qed.

lemma SHA3_512_ll: islossless Keccak1600Bytes.sha3_512.
proof. by proc; call KECCAK1600_ll. qed.

phoare SHA3_512_ph _m:
 [ Keccak1600Bytes.sha3_512
   : m = _m
     ==> res = SHA3_512 _m
 ] = 1%r.
proof. by conseq SHA3_512_ll (SHA3_512_h _m). qed.

hoare SHAKE128_h _m _outlen8:
 Keccak1600Bytes.shake128
 : m = _m /\ outlen8=_outlen8
   ==> res = SHAKE128 _m _outlen8.
proof. by proc; ecall (KECCAK1600_h 168 SHAKE_DS_BYTE m outlen8). qed.

lemma SHAKE128_ll: islossless Keccak1600Bytes.shake128.
proof. by proc; call KECCAK1600_ll. qed.

phoare SHAKE128_ph _m _outlen8:
 [ Keccak1600Bytes.shake128
   : m = _m /\ outlen8 = _outlen8
     ==> res = SHAKE128 _m _outlen8
 ] = 1%r.
proof. by conseq SHAKE128_ll (SHAKE128_h _m _outlen8). qed.

hoare SHAKE256_h _m _outlen8:
 Keccak1600Bytes.shake256
 : m = _m /\ outlen8=_outlen8
   ==> res = SHAKE256 _m _outlen8.
proof. by proc; ecall (KECCAK1600_h 136 SHAKE_DS_BYTE m outlen8). qed.

lemma SHAKE256_ll: islossless Keccak1600Bytes.shake256.
proof. by proc; call KECCAK1600_ll. qed.

phoare SHAKE256_ph _m _outlen8:
 [ Keccak1600Bytes.shake256
   : m = _m /\ outlen8 = _outlen8
     ==> res = SHAKE256 _m _outlen8
 ] = 1%r.
proof. by conseq SHAKE256_ll (SHAKE256_h _m _outlen8). qed.

hoare RAWSHAKE128_h _m _outlen8:
 Keccak1600Bytes.rawshake128
 : m = _m /\ outlen8=_outlen8
   ==> res = RAWSHAKE128 _m _outlen8.
proof. by proc; ecall (KECCAK1600_h 168 RAWSHAKE_DS_BYTE m outlen8). qed.

lemma RAWSHAKE128_ll: islossless Keccak1600Bytes.rawshake128.
proof. by proc; call KECCAK1600_ll. qed.

phoare RAWSHAKE128_ph _m _outlen8:
 [ Keccak1600Bytes.rawshake128
   : m = _m /\ outlen8 = _outlen8
     ==> res = RAWSHAKE128 _m _outlen8
 ] = 1%r.
proof. by conseq RAWSHAKE128_ll (RAWSHAKE128_h _m _outlen8). qed.

hoare RAWSHAKE256_h _m _outlen8:
 Keccak1600Bytes.rawshake256
 : m = _m /\ outlen8=_outlen8
   ==> res = RAWSHAKE256 _m _outlen8.
proof. by proc; ecall (KECCAK1600_h 136 RAWSHAKE_DS_BYTE m outlen8). qed.

lemma RAWSHAKE256_ll: islossless Keccak1600Bytes.rawshake256.
proof. by proc; call KECCAK1600_ll. qed.

phoare RAWSHAKE256_ph _m _outlen8:
 [ Keccak1600Bytes.rawshake256
   : m = _m /\ outlen8 = _outlen8
     ==> res = RAWSHAKE256 _m _outlen8
 ] = 1%r.
proof. by conseq RAWSHAKE256_ll (RAWSHAKE256_h _m _outlen8). qed.



