require import AllCore IntDiv FloorCeil StdOrder RealExp List.
require import ZModP Ring.
require import Distr DList DistrExtra DMap DInterval.
from Jasmin require import JWord JUtils.
require PKE_Ext.
require import Array25 Array32 Array34 Array64 Array128 Array168 Array256 Array384.
require import Array768 Array960 Array1024 Array1088 Array1184 Array1152.
require  PRF.

require import KyberLib.
import BitEncoding BitChunking BS2Int.

(*---*) import RField RealOrder IntOrder IntID.

require import GFq.
import Zq.

require import KPoly.
import PolyR.
import KMatrix.

require import Serialization.

(****************************)
(****************************)
(* SCHEME SPECIFICATION     *)
(****************************)
(****************************)

theory KyberSpec.

  (* For the CPA component will model the three usages of SHA3 family 
  components as different cryptographic primitives. 

  This will be an entropy smoothing hash function/prg.

  G = fn _sha3512_32(reg ptr u8[64] out, reg const ptr u8[32] in) -> stack u8[64]

  This will be a XOF construction based on a random oracle that
  takes the input to absorb plus an integer to identify the
  output block.

  XOF =
  fn _shake128_absorb34(reg ptr u64[25] state, reg const ptr u8[34] in) -> reg ptr u64[25]
  fn _shake128_squeezeblock(reg ptr u64[25] state, reg ptr u8[SHAKE128_RATE] out) -> 
  reg ptr u64[25], reg ptr u8[SHAKE128_RATE] => RATE is 168

  This will be a PRF.

  PRF = fn _shake256_128_33(reg ptr u8[128] out, reg const ptr u8[33] in) -> stack u8[128]

  We do not clone the ROM in fully specified form because
  we want to analyse the Spec in different ROM settings.

  Note that the following operators are used only for one purpose in the
  external algorithms, and they are all implicitly domain-separated
  due to either the use of different algorithms or different input lengths.
  ************************************************)

op SHA3_256_32_32 : W8.t Array32.t -> unit -> W8.t Array32.t.
op SHA3_256_64_64   : W8.t Array64.t -> W8.t Array64.t.
op SHA3_256_1088_32 : W8.t Array1088.t -> W8.t Array32.t.
op SHA3_256_1184_32 : W8.t Array1184.t -> W8.t Array32.t.

op SHA3_512_32_64 : W8.t Array32.t -> unit -> W8.t Array64.t.

op SHAKE128_ABSORB_34 : W8.t Array34.t ->  W64.t Array25.t.
op SHAKE128_SQUEEZE_168 : W64.t Array25.t -> W64.t Array25.t *  W8.t Array168.t.

op SHAKE256_64_32 : W8.t Array64.t -> W8.t Array32.t.
op SHAKE256_33_128 : W8.t Array32.t -> W8.t ->  W8.t Array128.t.

clone import PKE_Ext as KyberPKE with
type pkey = W8.t Array1152.t * W8.t Array32.t,
type skey = W8.t Array1152.t,
type plaintext = W8.t Array32.t,
type ciphertext = W8.t Array960.t * W8.t Array128.t.

  (* PRF keys in encryption come directly from srand *)
abbrev srand = darray32 W8.dword.

  (* G needs only to be entropy smoothing, which is
  exactly a PRF without any input *)
clone PRF as HS_DEFS with
type D <- unit,
type R <- W8.t Array64.t.

clone import HS_DEFS.PseudoRF as HSF with
type K <- W8.t Array32.t, 
op dK <- srand,
op F <- SHA3_512_32_64.

module KHS = HSF.PseudoRF.

module G(HS: HSF.PseudoRF) = {
  proc sample(s : W8.t Array32.t) : W8.t Array32.t * W8.t Array32.t = {
  var rhosig,rho,sig;
  rhosig <@ HS.f(s,());
  rho <- Array32.init (fun i => rhosig.[i]);
  sig <- Array32.init (fun i => rhosig.[i + 32]);
  return (rho,sig);
  }
}.

    (* We take some liberty to specify parse using a XOF that
    returns 168 bytes at a time, which is what the Kyber
    implementation does. *)
module type XOF_t(O : RO.POracle) = {
  proc init(rho :  W8.t Array32.t, i j : W8.t) : unit
  proc next_bytes() : W8.t Array168.t
}.

    (* This is a concrete XOF that does not use the random oracle,
    and that matches the Kyber spec and the implementation *)

module (XOF : XOF_t) (O : KyberPKE.RO.POracle) = {
  var state : W64.t Array25.t
  proc init(rho : W8.t Array32.t, i j : W8.t) : unit = {
  var extseed : W8.t Array34.t;
  extseed <- Array34.init
    (fun k => if k < 32 then rho.[k] else if k=32 then i else j);
      state <- SHAKE128_ABSORB_34 extseed;
  }
      proc next_bytes() : W8.t Array168.t = { 
      var buf;
    (state,buf) <- SHAKE128_SQUEEZE_168 state;
      return buf; 
  }
}.


module Parse(XOF : XOF_t, O : RO.POracle) = {
  proc sample() : poly = {
  var j, b168, bi, bi1, bi2, d1, d2,k;
  var aa : poly;
  aa <- witness;
  j <- 0;
  while (j < 256) {
  b168 <@ XOF(O).next_bytes();
  k <- 0;
  while ((j < 256) && (k < 168)) {
  bi  <- b168.[k];
  bi1 <- b168.[k+1];
  bi2 <- b168.[k+2];
  k <- k + 3;
  d1 <- to_uint bi        + 256 * (to_uint bi1 %% 16);
  d2 <- to_uint bi1 %/ 16 + 16  * to_uint bi2;
  if (d1 < q)                { aa.[j] <- inFq d1; j <- j + 1; }
  if ((d2 < q) && (j < 256)) { aa.[j] <- inFq d2; j <- j + 1; }
      }
    }
        return aa;
  }
}.


clone PRF as PRF_DEFS with
type D <- W8.t,
type R <- W8.t Array128.t.


clone import PRF_DEFS.PseudoRF as PRF_ with
type K <- W8.t Array32.t, 
op dK <- srand,
op F <- SHAKE256_33_128.

module KPRF = PRF_.PseudoRF.

module CBD2(PRF : PseudoRF) = {
  proc sample_spec(sig : W8.t Array32.t, _N : int) : poly = {
  var i,a,b,bytes,bits;
  var rr : poly;
  rr <- witness;
  bytes <@ PRF.f(sig, W8.of_int _N);
  bits <- BytesToBits (to_list bytes);
  i <- 0;
  while (i < 256) { 
  a <- b2i (nth false bits (4*i)) + b2i (nth false bits (4*i+1));
  b <- b2i (nth false bits (4*i+2)) + b2i (nth false bits (4*i+3));
  rr.[i] <- inFq  (a - b);
  i <- i + 1;
    }
        return rr;

  }
      proc sample(sig : W8.t Array32.t, _N : int) : poly = {
      var i,j,a,b,bytes;
      var rr : poly;
      rr <- witness;
      bytes <@ PRF.f(sig, W8.of_int _N);
      i <- 0; j <- 0;
      while (i < 128) { (* unroll loop body once to match code *)
      a <- b2i bytes.[i].[j %% 2 * 4 + 0] + b2i bytes.[i].[j %% 2 * 4 + 1];
      b <- b2i bytes.[i].[j %% 2 * 4 + 2] + b2i bytes.[i].[j %% 2 * 4 + 3];
      rr.[j] <- inFq  (a - b);
      j <- j + 1;
      a <- b2i bytes.[i].[j %% 2 * 4 + 0] + b2i bytes.[i].[j %% 2 * 4 + 1];
      b <- b2i bytes.[i].[j %% 2 * 4 + 2] + b2i bytes.[i].[j %% 2 * 4 + 3];
      rr.[j] <- inFq  (a - b);
      j <- j + 1;
      i <- i + 1;
    }
        return rr;
  }
}.

module KyberCPAPKE(HS : HSF.PseudoRF, XOF : XOF_t, PRF : PseudoRF, O : RO.POracle) : Scheme = {

  (* Spec gives a derandomized enc that matches this code *)
  proc kg_derand(seed: W8.t Array32.t) : pkey * skey = {
  var rho, sig, i, j, _N,c,t;
  var tv,sv : W8.t Array1152.t;
  var a : matrix;
  var s,e : vector;
  a <- witness;
  e <- witness;
  s <- witness;
  sv <- witness;
  tv <- witness;
    (rho,sig) <@ G(HS).sample(seed);
      _N <- 0; 
      i <- 0;
      while (i < kvec) {
      j <- 0;
      while (j < kvec) {
      XOF(O).init(rho,W8.of_int j,W8.of_int i);
      c <@ Parse(XOF,O).sample();
      a.[(i,j)] <- c;
      j <- j + 1;
      }
          i <- i + 1;
    }      
        i <- 0;
        while (i < kvec) {
        c <@ CBD2(PRF).sample(sig,_N);
        s <- set s i c;
        _N <- _N + 1;
        i <- i + 1;
    }         
        i <- 0;
        while (i < kvec) {
        c <@ CBD2(PRF).sample(sig,_N);
        e <- set e i c;
        _N <- _N + 1;
        i <- i + 1;
    }      
        s <- nttv s;
        e <- nttv e; 
        t <- ntt_mmul a s + e;
        tv <@ EncDec.encode12_vec(toipolyvec t); (* minimum residues *)
        sv <@ EncDec.encode12_vec(toipolyvec s); (* minimum residues *)
        return ((tv,rho),sv);
  }

      proc kg() : pkey * skey = {
      var s,kp;
      s <$ srand;
      kp <@ kg_derand(s);
      return kp;
  }

      (* Spec gives a derandomized enc that matches this code *)
      proc enc_derand(pk : pkey, m : plaintext, r : W8.t Array32.t) : ciphertext = {
      var _N,i,j,c,tv,rho,rv,e1,e2,rhat,u,v,mp,c2,thati;
      var that : vector;
      var aT : matrix;
      var c1 : W8.t Array960.t;
      aT <- witness;
      c1 <- witness;
      e1 <- witness;
      rv <- witness;
      that <- witness;
    (tv,rho) <- pk;
      _N <- 0;
      thati <@ EncDec.decode12_vec(tv); 
      that <- ofipolyvec thati;
      i <- 0;
      while (i < kvec) {
      j <- 0;
      while (j < kvec) {
      XOF(O).init(rho,W8.of_int i, W8.of_int j);
      c <@ Parse(XOF,O).sample();
      aT.[(i,j)] <- c; (* this is the transposed matrix *)
      j <- j + 1;
      }
          i <- i + 1;
    } 
        i <- 0;
        while (i < kvec) {
        c <@ CBD2(PRF).sample(r,_N);
        rv <- set rv i c;
        _N <- _N + 1;
        i <- i + 1;
    }         
        i <- 0;
        while (i < kvec) {
        c <@ CBD2(PRF).sample(r,_N);
        e1 <- set e1 i c;
        _N <- _N + 1;
        i <- i + 1;
    }      
        e2 <@ CBD2(PRF).sample(r,_N);
        rhat <- nttv rv;
        u <- invnttv (ntt_mmul aT rhat) + e1;
        mp <@ EncDec.decode1(m);
        v <- invntt (ntt_dotp that rhat) &+ e2 &+ decompress_poly 1 mp; 
        c1 <@ EncDec.encode10_vec(compress_polyvec 10 u); 
        c2 <@ EncDec.encode4(compress_poly 4 v);
        return (c1,c2);
  }

      proc enc(pk : pkey, m : plaintext) : ciphertext = {
      var r,c;
      r <$ srand;
      c <@ enc_derand(pk,m,r);
      return c;
  }

      proc dec(sk : skey, cph : ciphertext) : plaintext option = {
      var m,mp,ui,v,vi,si, c1, c2;
      var u,s : vector;
      u <- witness;
      s <- witness;
    (c1,c2) <- cph;
      ui <@ EncDec.decode10_vec(c1);
      u <- decompress_polyvec 10 ui;
      vi <@ EncDec.decode4(c2);
      v <- decompress_poly 4 vi;
      si <@ EncDec.decode12_vec(sk);
      s <- ofipolyvec si;
      mp <- v &+ ((&-) (invntt (ntt_dotp s (nttv u))));
      m <@ EncDec.encode1(compress_poly 1 mp);
      return Some m;
  }

}.

    (*********************************)
    (*********************************)
    (*********************************)
    (* IND CCA Component             *)
    (*********************************)
    (*********************************)

clone PRF as HS_KEM_DEFS with
type D <- unit,
type R <- W8.t Array32.t.


clone import HS_KEM_DEFS.PseudoRF as HSF_KEM with
type K <- W8.t Array32.t, 
op dK <- srand,
op F <- SHA3_256_32_32.

module KHS_KEM = HSF_KEM.PseudoRF.

module KemG(KemHS: HSF_KEM.PseudoRF) = {
  proc sample(s : W8.t Array32.t) : W8.t Array32.t = {
  var m;
  m <@ KemHS.f(s,());
  return m;
  }
}.

module type KEMHashes(O : RO.POracle) = {
  proc pkH(pk : W8.t Array1152.t * W8.t Array32.t) : W8.t Array32.t
  proc cH(c : W8.t Array960.t * W8.t Array128.t) : W8.t Array32.t
  proc g(m : W8.t Array32.t, pkh : W8.t Array32.t) : W8.t Array32.t * W8.t Array32.t 
  proc kdf(kt : W8.t Array32.t, ch : W8.t Array32.t) : W8.t Array32.t
}.

module (KemH : KEMHashes) (RO : RO.POracle) = {
  proc pkH(pk : W8.t Array1152.t * W8.t Array32.t) : W8.t Array32.t = {
  return SHA3_256_1184_32 (Array1184.init (fun k => if (k < 1152) then pk.`1.[k] else pk.`2.[k-1152]));
  }
      proc cH(c : W8.t Array960.t * W8.t Array128.t) : W8.t Array32.t = {
      return SHA3_256_1088_32 (Array1088.init (fun k => if (k < 960) then c.`1.[k] else c.`2.[k-960]));

  }
      proc g(m : W8.t Array32.t, pkh : W8.t Array32.t) : W8.t Array32.t * W8.t Array32.t  = {
      var ktr;
      ktr <- SHA3_256_64_64 (Array64.init (fun k => if (k < 32) then m.[k] else pkh.[k-32]));
      return (Array32.init (fun i=> ktr.[i]), Array32.init (fun i => ktr.[i + 32]));
  }
      proc kdf(kt : W8.t Array32.t, ch : W8.t Array32.t) : W8.t Array32.t = {
      return SHAKE256_64_32 (Array64.init (fun k => if (k < 32) then kt.[k] else ch.[k-32]));
  }

}.


import PRF_.
module KyberKEM(HS : HSF.PseudoRF, XOF : XOF_t, PRF : PseudoRF, 
  KemHS : HSF_KEM.PseudoRF, KemH : KEMHashes, O : RO.POracle)  = {

  proc kg_derand(seed : W8.t Array32.t * W8.t Array32.t) : 
  pkey * (skey * pkey * W8.t Array32.t * W8.t Array32.t) = {
  var kgs,z,pk,sk,hpk;
  kgs <- seed.`1;
  z <- seed.`2;
    (pk,sk) <@ KyberCPAPKE(HS,XOF,PRF,O).kg_derand(kgs);
      hpk <@ KemH(O).pkH(pk);
      return (pk, (sk,pk,hpk,z));
    
  }

      proc enc_derand(pk : pkey, prem : W8.t Array32.t) : ciphertext * W8.t Array32.t = {
      var m,hpk,_Kt,r,c,hc,_K;
      m <@ KemG(KemHS).sample(prem); 
      hpk <@ KemH(O).pkH(pk); 
    (_Kt,r) <@ KemH(O).g(m,hpk);
      c <@ KyberCPAPKE(HS,XOF,PRF,O).enc_derand(pk,m,r);
      hc <@ KemH(O).cH(c);
      _K <@ KemH(O).kdf(_Kt,hc);
      return (c,_K);
  }

      proc dec(cph : ciphertext, sk : skey * pkey * W8.t Array32.t * W8.t Array32.t) : W8.t Array32.t = {
      var m,_Kt,r,skp,pk,hpk,z,c,hc,_K;
    (skp,pk,hpk,z) <- sk;
      m <@ KyberCPAPKE(HS,XOF,PRF,O).dec(skp,cph);
    (_Kt,r) <@ KemH(O).g(oget m,hpk);
      c <@ KyberCPAPKE(HS,XOF,PRF,O).enc_derand(pk,oget m,r);
      hc <@ KemH(O).cH(cph);
    if (c = cph) {
      _K <@ KemH(O).kdf(_Kt,hc);
    }
        else {
        _K <@ KemH(O).kdf(z,hc);
    }
        return _K;
  }
}.


end KyberSpec.
