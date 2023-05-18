(* General EC imports *)
require import AllCore List.
from Jasmin require import JModel.
require import Array25 Array32 Array64 Array128 Array168 Array256 Array960 Array1152.


require import Keccak1600_Spec.


(* XXX: Link to specs of Keccak functions *)
op SHA3_256_32_32 (m: W8.t Array32.t): W8.t Array32.t =
 Array32.of_list W8.zero (SHA3_256 (to_list m)).

(* XXX: Writing input type as "product" is probably terrible for domain separation checking *)
op SHA3_256_1088_32 (m: W8.t Array960.t * W8.t Array128.t): W8.t Array32.t =
 Array32.of_list W8.zero (SHA3_256 (to_list m.`1 ++ to_list m.`2)).
(* XXX: same here *)
op SHA3_256_1184_32 (m: W8.t Array1152.t * W8.t Array32.t): W8.t Array32.t =
 Array32.of_list W8.zero (SHA3_256 (to_list m.`1 ++ to_list m.`2)).

op SHA3_512_32_64 (m: W8.t Array32.t): W8.t Array32.t * W8.t Array32.t =
 let bs = SHA3_512 (to_list m)
 in (Array32.of_list W8.zero (take 32 bs), Array32.of_list W8.zero (drop 32 bs)).
(* XXX: same here *)
op SHA3_512_64_64 (m1 m2: W8.t Array32.t): W8.t Array32.t * W8.t Array32.t =
 let bs = SHA3_512 (to_list m1 ++ to_list m2)
 in (Array32.of_list W8.zero (take 32 bs), Array32.of_list W8.zero (drop 32 bs)).


(* Option I: expose state... *)
op SHAKE128_ABSORB_34 (m: W8.t Array32.t, mi mj: W8.t): W64.t Array25.t =
 keccak1600_absorb_op 21 (W8.of_int 31) (to_list m ++ [mi;mj]).
op SHAKE128_SQUEEZE_168 (st: W64.t Array25.t): W64.t Array25.t *  W8.t Array168.t = 
 let st' = KECCAK_F1600 st
 in (st', Array168.of_list W8.zero (state_squeeze st' 168)).

(* Option II: exploit relation between outputs of different lengths *)
(** [SHAKE128_i(m,i)] returns the last 168 bytes of [SHAKE128(m,i*168)] (that is, the ith block) *)
op SHAKE128_i (m: W8.t Array32.t, mi mj: W8.t, cnt: int): W8.t Array168.t =
 Array168.of_list W8.zero (drop (168*(cnt-1)) (SHAKE128 (to_list m ++ [mi;mj]) (168*cnt))).


(* XXX: same here *)
op SHAKE256_64_32 (m1 m2: W8.t Array32.t): W8.t Array32.t =
 Array32.of_list W8.zero (SHAKE256 (to_list m1 ++ to_list m2) 32).
op SHAKE256_33_128 (m: W8.t Array32.t, mj: W8.t): W8.t Array128.t =
 Array128.of_list W8.zero (SHAKE256 (to_list m ++ [mj]) 128).



op G_coins = SHA3_512_32_64.
op G_mhpk  = SHA3_512_64_64.

op H_msg = SHA3_256_32_32.
op H_pk  = SHA3_256_1184_32.
op H_ct  = SHA3_256_1088_32.

op KDF = SHAKE256_64_32.

op PRF = SHAKE256_33_128.


module type XOF_t = {
  proc init(rho : W8.t Array32.t, i j : int) : unit
  proc next_bytes() : W8.t Array168.t
}.

(* Option I *)
module XOF_I : XOF_t = {
  var state : W64.t Array25.t
  proc init(rho : W8.t Array32.t, i j : int) : unit = {
    state <- SHAKE128_ABSORB_34 rho (W8.of_int i) (W8.of_int j);
  }

  proc next_bytes() : W8.t Array168.t = { 
    var buf;
    (state,buf) <- SHAKE128_SQUEEZE_168 state;
    return buf; 
  }
}.

(* Option II *)
module XOF_II : XOF_t = {
  var cnt : int
  var msg: W8.t list
  proc init(rho : W8.t Array32.t, i j : int) : unit = {
    cnt <- 0;
    msg <- (to_list rho) ++ [W8.of_int i; W8.of_int j];
  }
  proc next_bytes() : W8.t Array168.t = { 
    var buf;
    cnt <- cnt + 1;
    buf <- SHAKE128_i msg cnt;
    return Array168.of_list W8.zero buf; 
  }
}.
