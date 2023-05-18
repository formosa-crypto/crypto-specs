(******************************************************************************
   Keccak1600_Spec.ec:

   Properties of the Keccak1600 specification.

******************************************************************************)
require import AllCore List Int IntDiv.
require StdOrder.
import StdOrder.IntOrder.

require export FIPS202_SHA3.

require import Keccakf1600_Spec.

import EclibExtra.

require BitEncoding.
import BitEncoding.BitChunking.

type byte = W8.t.
type bytes = W8.t list.
type w64 = W64.t.
type w64s = W64.t list.

(** sets a specific byte of a 64-bit word *)
op w64_set_u8 (w: w64, pos: int, x: byte): w64 =
 pack8_t (unpack8 w).[pos <- x].

op w64_xor_u8 (w: w64, pos: int, x: byte): w64 =
 let w8u8 = unpack8 w in pack8_t w8u8.[pos <- w8u8.[pos] `^` x].

op bytes2state (bs: bytes): state =
 Array25.of_list W64.zero (w8L2w64L bs).

op state2bytes (st: state): bytes =
 w64L2w8L (to_list st).

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



(** [chunkremnant] returns the leftovers not handled by [chunk] *)
op chunkremnant ['a] (n: int) (bs: 'a list) =
 drop (size bs %/ n * n) bs.


abbrev KECCAK_F1600 = keccak_f1600_op.

(** absorb intermediate blocks *)
op state_absorb_iblocks (r64: int, m: bytes): state =
 foldl (fun st m => KECCAK_F1600 (state_absorb st m)) st0 (chunk (8*r64) m).

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
  (state_absorb (state_absorb_iblocks r64 m)
                (rcons (chunkremnant (8*r64) m) suffix)).


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




(** [SHAKE128_i(m,i)] returns the last 168 bytes of [SHAKE128(m,i*168)] (ith block) *)
op SHAKE128_i (m: bytes) (i: int): bytes =
 drop (168*(i-1)) (SHAKE128 m (i*168)).

