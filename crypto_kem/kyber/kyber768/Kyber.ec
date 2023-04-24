(* General EC imports *)
from Jasmin require import JWord.
require import Array32.

(* Imports of "lower-level" Kyber spec parts *)
require import GFq.
import Zq.
require import Rq.
require import Symmetric.
require import Sampling.
require import VecMat.
import PolyMat.
require import Serialization.
require InnerPKE.
(*clone InnerPKE.*)

type publickey = InnerPKE.pkey.
type secretkey = InnerPKE.skey * InnerPKE.pkey * W8.t Array32.t * W8.t Array32.t.
type ciphertext = InnerPKE.ciphertext.
type sharedsecret = W8.t Array32.t.

module Kyber = {

  proc kg_derand(coins: W8.t Array32.t * W8.t Array32.t) : publickey * secretkey = {
    var kgs,z,pk,sk,hpk;
    kgs     <- coins.`1;
    z       <- coins.`2;
    (pk,sk) <@ InnerPKE.InnerPKE.kg_derand(kgs);
    hpk     <- H_pk pk;
    return (pk, (sk,pk,hpk,z));
  }

  proc enc_derand(pk : publickey, coins: W8.t Array32.t) : ciphertext * sharedsecret = {
    var m,hpk,_Kt,r,c,hc,_K;
    m       <- H_msg coins; 
    hpk     <- H_pk pk;
    (_Kt,r) <- G_mhpk m hpk;
    c       <@ InnerPKE.InnerPKE.enc_derand(pk,m,r);
    hc      <- H_ct c;
    _K      <- KDF _Kt hc;
    return (c,_K);
  }

  proc dec(cph : ciphertext, sk : secretkey) : sharedsecret = {
    var m,_Kt,r,skp,pk,hpk,z,c,hc,_K;
    (skp,pk,hpk,z) <- sk;
    m              <@ InnerPKE.InnerPKE.dec(skp,cph);
    (_Kt,r)        <- G_mhpk m hpk;
    c              <@ InnerPKE.InnerPKE.enc_derand(pk,m,r);
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
