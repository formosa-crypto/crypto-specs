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
require import Rq.
require import Symmetric.
require import Sampling.
require import VecMat.
import KMatrix.
require import Serialization.
require import InnerPKE.


module Kyber = {

  proc kg_derand(coins: W8.t Array32.t * W8.t Array32.t) : pkey * (skey * pkey * W8.t Array32.t * W8.t Array32.t) = {
      var kgs,z,pk,sk,hpk;
      kgs     <- coins.`1;
      z       <- coins.`2;
      (pk,sk) <@ InnerPKE.kg_derand(kgs);
      hpk     <- H_pk pk;
      return (pk, (sk,pk,hpk,z));
    }

  proc enc_derand(pk : pkey, prem : W8.t Array32.t) : ciphertext * W8.t Array32.t = {
    var m,hpk,_Kt,r,c,hc,_K;
    m       <- H_msg prem; 
    hpk     <- H_pk pk;
    (_Kt,r) <- G_mhpk m hpk;
    c       <@ InnerPKE.enc_derand(pk,m,r);
    hc      <- H_ct c;
    _K      <- KDF _Kt hc;
    return (c,_K);
  }

  proc dec(cph : ciphertext, sk : skey * pkey * W8.t Array32.t * W8.t Array32.t) : W8.t Array32.t = {
    var m,_Kt,r,skp,pk,hpk,z,c,hc,_K;
    (skp,pk,hpk,z) <- sk;
    m              <@ InnerPKE.dec(skp,cph);
    (_Kt,r)        <- G_mhpk m hpk;
    c              <@ InnerPKE.enc_derand(pk,m,r);
    hc             <- H_ct c;
    if (c = cph) {
      _K <- KDF _Kt hc;
    }
    else {
      _K <- KDF z hc;
    }
    return _K;
  }
}.
