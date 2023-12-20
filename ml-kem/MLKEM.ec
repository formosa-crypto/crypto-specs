(* General EC imports *)
from Jasmin require import JWord.
require import Array32.

(* Imports of "lower-level" MLKEM spec parts *)
require import GFq.
import Zq.
require import Rq.
require import Symmetric.
require import Sampling.
require import VecMat.
import PolyMat.
require import Serialization.
require import InnerPKE.

type publickey = InnerPKE.pkey.
type secretkey = InnerPKE.skey* InnerPKE.pkey * W8.t Array32.t * W8.t Array32.t.
type ciphertext = InnerPKE.ciphertext.
type sharedsecret = W8.t Array32.t.

import InnerPKE.
module MLKEM = {

  proc kg_derand(coins: W8.t Array32.t * W8.t Array32.t) : publickey * secretkey = {
    var kgs,z,pk,sk,hpk;
    kgs     <- coins.`1;
    z       <- coins.`2;
    (pk,sk) <@ InnerPKE.kg_derand(kgs);
    hpk     <- H_pk pk;
    return (pk, (sk,pk,hpk,z));
  }

  proc enc_derand(pk : publickey, coins: W8.t Array32.t) : ciphertext * sharedsecret = {
    var m,hpk,r,c,_K;
    m       <- coins;
    hpk     <- H_pk pk;
    (_K,r) <- G_mhpk m hpk;
    c       <@ InnerPKE.enc_derand(pk,m,r);
    return (c,_K);
  }

  proc dec(cph : ciphertext, sk : secretkey) : sharedsecret = {
    var m,_K',r,skp,pk,hpk,z,c,_K;
    (skp,pk,hpk,z) <- sk;
    m             <@ InnerPKE.dec(skp,cph);
    (_K,r)        <- G_mhpk m hpk;
    _K'           <- J z cph;
    c             <@ InnerPKE.enc_derand(pk,m,r);
    if (c <> cph) {
      _K <- _K';
    }
    return _K;
  }
}.
