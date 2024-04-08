(* General EC imports *)
require import AllCore List.
from Jasmin require import JModel.

require import Array25 Array32 Array34 Array64 Array66 Array168 Array136 Array320.

require import Keccak1600_Spec.

op SHAKE128_ABSORB_34 (x: W8.t Array34.t) : W64.t Array25.t =
 SHAKE128_ABSORB (to_list x).
op SHAKE128_SQUEEZE_168 (st: W64.t Array25.t): W64.t Array25.t *  W8.t Array168.t =
 let (st', l) = SHAKE128_SQUEEZE_BLOCK st in (st', Array168.of_list W8.zero l).

op SHAKE256_ABSORB_32 (x: W8.t Array32.t) : W64.t Array25.t =
 SHAKE256_ABSORB (to_list x).
op SHAKE256_ABSORB_66 (x: W8.t Array66.t) : W64.t Array25.t =
 SHAKE256_ABSORB (to_list x).
op SHAKE256_SQUEEZE_136 (st: W64.t Array25.t): W64.t Array25.t *  W8.t Array136.t =
 let (st', l) = SHAKE256_SQUEEZE_BLOCK st in (st', Array136.of_list W8.zero l).

op SHAKE256_66_320 (rho : W8.t Array64.t, r : W16.t): W8.t Array320.t =
 Array320.of_list W8.zero (SHAKE256 (to_list rho ++ W2u8.Pack.to_list (W2u8.unpack8 r)) 320).

module type H_t = {
  proc init32(rho : W8.t Array32.t) : unit
  proc init66(rho : W8.t Array64.t, r : W16.t) : unit
  proc next_bytes() : W8.t Array136.t
}.

module H : H_t = {
  var state : W64.t Array25.t
  proc init32(rho : W8.t Array32.t) : unit = {
    state <- SHAKE256_ABSORB_32 rho;
  }

  proc init66(rho : W8.t Array64.t, r : W16.t) : unit = {
    var seed;
    seed <- Array66.init (fun ii => if 0 <= ii < 64 then rho.[ii] 
                          else (W2u8.unpack8 r).[ii-64]);
    state <- SHAKE256_ABSORB_66 seed;
  }

  proc next_bytes() : W8.t Array136.t = { 
    var buf;
    (state,buf) <- SHAKE256_SQUEEZE_136 state;
    return buf; 
  }
}.

module type H128_t = {
  proc init(rho : W8.t Array32.t, i j : W8.t) : unit
  proc next_bytes() : W8.t Array168.t
}.

module H128 : H128_t = {
  var state : W64.t Array25.t
  proc init(rho : W8.t Array32.t, i j : W8.t) : unit = {
    var seed;
    seed <- Array34.init (fun ii => if 0 <= ii < 32 then rho.[ii] 
                          else if ii = 32 then i else j);
    state <- SHAKE128_ABSORB_34 seed;
  }

  proc next_bytes() : W8.t Array168.t = { 
    var buf;
    (state,buf) <- SHAKE128_SQUEEZE_168 state;
    return buf; 
  }
}.

op Hhint = SHAKE256_66_320.
