(* General EC imports *)
require import AllCore.
from Jasmin require import JModel.
require import Array25 Array32 Array64 Array128 Array168 Array256 Array960 Array1152.

(* XXX: Link to specs of Keccak functions *)
op SHA3_256_32_32 : W8.t Array32.t -> W8.t Array32.t.
(* XXX: Writing input type as "product" is probably terrible for domain separation checking *)
op SHA3_256_1088_32 : W8.t Array960.t * W8.t Array128.t -> W8.t Array32.t.
(* XXX: same here *)
op SHA3_256_1184_32 : W8.t Array1152.t * W8.t Array32.t -> W8.t Array32.t.

op SHA3_512_32_64 : W8.t Array32.t -> W8.t Array32.t * W8.t Array32.t.
(* XXX: same here *)
op SHA3_512_64_64 : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t * W8.t Array32.t.

op SHAKE128_ABSORB_34 : W8.t Array32.t -> W8.t -> W8.t ->  W64.t Array25.t.
op SHAKE128_SQUEEZE_168 : W64.t Array25.t -> W64.t Array25.t *  W8.t Array168.t.

(* XXX: same here *)
op SHAKE256_64_32 : W8.t Array32.t -> W8.t Array32.t -> W8.t Array32.t.
op SHAKE256_33_128 : W8.t Array32.t -> W8.t ->  W8.t Array128.t.

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

module XOF : XOF_t = {
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
