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

require import Symmetric.

require import GFq.
import Zq.

require import Rq.

require import Sampling.

require import VecMat.
import KMatrix.

require import Serialization.

require import InnerPKE.



(* clone PRF as HS_KEM_DEFS with
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
  *)
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
