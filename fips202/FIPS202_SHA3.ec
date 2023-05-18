(******************************************************************************
   Keccak_f1600_Spec.ec:

   Specification of the Keccak-f1600 permutation.

   Normative reference: FIPS PUB 202
   https://nvlpubs.nist.gov/nistpubs/fips/nist.fips.202.pdf
******************************************************************************)
require import AllCore List Int IntDiv.
require BitEncoding.
import BitEncoding.BitChunking.

require export FIPS202_Keccakf1600.


(** Initial state *)
op st0 : state = Array25.create W64.zero.

(** State addition (xor) *)
op addstate = Array25.map2 W64.(`^`) .


(** Section 5.1 -- Specification of [pad10*1]
    Algorithm 9 *)
op pad10star1 (x: int) (m: int): bool list =
 true :: rcons (nseq ((-m-2)%%x) false) true.


(** Imperative specification for [Keccak-f1600]. *)
module Keccak1600 = {
  (** Section 4 - SPONGE CONSTRUCTION
      Algorithm 8 *)
  proc sponge1600_pad10star1(r: int, m: bool list, d: int): bool list = {
    var p, pl, n, s, i, z;
    p <- m ++ pad10star1 r (size m);
    pl <- chunk r p;
    n <- (size p) %/ r;
    s <- st0;
    i <- 0;
    while (i < n) { (* absorb *)
      s <- addstate s (bits2state (nth [] pl i));
      s <@ Keccakf1600.keccak_f1600(s);
      i <- i + 1;
    }
    (* squeeze *)
    z <- take r (state2bits s);
    while (size z < d) {
      s <@ Keccakf1600.keccak_f1600(s);
      z <- z ++ take r (state2bits s);
    }
    return take d z;
  }
  (** Section 5.2 - Specification of KECCAK[c] *)
  proc keccak1600(c: int, m: bool list, outlen: int): bool list = {
    var z;
    z <@ sponge1600_pad10star1(keccak_b - c, m, outlen);
    return z;
  }
  (** Section 6.1 - SHA-3 Hash Functions *)
  proc sha3_224(m: bool list): bool list = {
    var z;
    z <@ keccak1600(448, m++[false; true], 224);
    return z;
  }
  proc sha3_256(m: bool list): bool list = {
    var z;
    z <@ keccak1600(512, m++[false; true], 256);
    return z;
  }
  proc sha3_384(m: bool list): bool list = {
    var z;
    z <@ keccak1600(768, m++[false; true], 384);
    return z;
  }
  proc sha3_512(m: bool list): bool list = {
    var z;
    z <@ keccak1600(1024, m++[false; true], 512);
    return z;
  }
  (** Section 6.2 - SHA-3 Extendable-Output Functions *)
  proc shake128(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(256, m++[true; true; true; true], d);
    return z;
  }
  proc shake256(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(512, m++[true; true; true; true], d);
    return z;
  }
  (** Section 6.3 - AlternateDefinitionsof SHA-3 Extendable-Output Functions *)
  proc rawSHAKE128(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(256, m++[true; true], d);
    return z;
  }
  proc rawSHAKE256(m: bool list, d: int): bool list = {
    var z;
    z <@ keccak1600(512, m++[true; true], d);
    return z;
  }


}.


