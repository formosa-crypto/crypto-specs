require import AllCore List.
from Jasmin require import JModel.

require import Array16 Array25 Array32 Array34 Array64 Array66 Array96 Array168 Array136 Array320 Array1952.

require import Keccak1600_Spec.

op SHAKE256_66_320 (rho : W8.t Array64.t, r : W16.t): W8.t Array320.t =
 Array320.of_list W8.zero (SHAKE256 (to_list rho ++ W2u8.Pack.to_list (W2u8.unpack8 r)) 320).

op SHAKE256_32_128 (rho : W8.t Array32.t): W8.t Array32.t * W8.t Array64.t * W8.t Array32.t =
 let bytes = (SHAKE256 (to_list rho) 128) in
 (Array32.of_list W8.zero (take 32 bytes),
  Array64.of_list W8.zero (take 64 (drop 32 bytes)),
  Array32.of_list W8.zero (drop 96 bytes)).

op SHAKE256_1952_64 (pk : W8.t Array1952.t): W8.t Array64.t =
 Array64.of_list W8.zero (SHAKE256 (to_list pk) 64).

op SHAKE256_160_48 (mu : W8.t Array64.t, w1enc : W8.t Array96.t): W8.t Array32.t * W8.t Array16.t =
 let bytes = (SHAKE256 ((to_list mu) ++ (to_list w1enc)) 48) in
 (Array32.of_list W8.zero (take 32 bytes),
  Array16.of_list W8.zero (drop 32 bytes)).

op SHAKE256_96_64 (_K coins : W8.t Array32.t, mu : W8.t Array64.t): W8.t Array64.t =
 Array64.of_list W8.zero (SHAKE256 (to_list _K ++ to_list coins ++ to_list mu) 64).

op SHAKE256_ABSORB_32 (x: W8.t Array32.t) : W64.t Array25.t =
 SHAKE256_ABSORB (to_list x).
op SHAKE256_ABSORB_66 (x: W8.t Array66.t) : W64.t Array25.t =
 SHAKE256_ABSORB (to_list x).
op SHAKE256_SQUEEZE_136 (st: W64.t Array25.t): W64.t Array25.t *  W8.t Array136.t =
 let (st', l) = SHAKE256_SQUEEZE_BLOCK st in (st', Array136.of_list W8.zero l).

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

op SHAKE128_ABSORB_34 (x: W8.t Array34.t) : W64.t Array25.t =
 SHAKE128_ABSORB (to_list x).
op SHAKE128_SQUEEZE_168 (st: W64.t Array25.t): W64.t Array25.t *  W8.t Array168.t =
 let (st', l) = SHAKE128_SQUEEZE_BLOCK st in (st', Array168.of_list W8.zero l).

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
op Hseed = SHAKE256_32_128.
op Hpk = SHAKE256_1952_64.
op Hm(tr : W8.t Array64.t, m : W8.t list) : W8.t Array64.t  =  Array64.of_list witness (SHAKE256 (to_list tr ++ m) 64).
op Hcomm = SHAKE256_160_48.
op Hprivsd = SHAKE256_96_64.
