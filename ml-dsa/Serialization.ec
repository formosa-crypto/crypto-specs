require import AllCore BitEncoding List RealExp IntDiv.
from Jasmin require import JModel.

require import Array16 Array32 Array64 Array96 Array256 Array1952 Array3309 Array4032.

require import Parameters GFq Rq VecMat Conversion Symmetric.
import PolyLVec PolyKVec PolyMat.

module PkEncDec = {
  proc pkEncode(rho : W8.t Array32.t, t1 : polykvec) : W8.t Array1952.t = {
    var i, pki, pkbytes, pk;
    pkbytes <- [];
    i <- 0;
    while (i < kvec) {
      pki <- SimpleBitPack t1.[i] 10;
      pkbytes <- pkbytes ++ pki; 
    }
    pk <- Array1952.init (fun ii => if 0<= ii < 32 then rho.[ii] else nth witness pkbytes (ii - 32));
    return pk;
  }

  proc pkDecode(pk :  W8.t Array1952.t) :  W8.t Array32.t * polykvec = {
    var i, rho, pki;
    var t1 : polykvec;
    t1 <- witness;
    rho <- Array32.init (fun ii  => pk.[ii]);
    i <- 0;
    while (i < kvec) {
      pki <- SimpleBitUnpack (mkseq (fun ii => pk.[32+320*i + ii]) 256) 10;
      t1 <- t1.[i <- pki];
    }
    return (rho,t1);
  }

}.

module SkEncDec = {
  proc skEncode(rho k : W8.t Array32.t, tr : W8.t Array64.t, s1 : polylvec, s2 t0 : polykvec)
    : W8.t Array4032.t = {
    var i, skbytes, ski,sk; 
    skbytes <- [];
    i <- 0;
    while (i < lvec) {
      ski <- BitPack s1.[i] Eta Eta;
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitPack s2.[i] Eta Eta;
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitPack t0.[i] (2^(d-1)) (2^(d-1));
      skbytes <- skbytes ++ ski;
      i <- i + 1;
    }
    sk <- Array4032.init(fun ii => if 0 <= ii < 32 then rho.[ii]
                                   else if 32 <= ii < 64 then k.[ii]
                                   else if 64 <= ii < 128 then tr.[ii]
                                   else nth witness skbytes (ii - 128));
    return sk;
  }

  proc skDecode(sk : W8.t Array4032.t) : W8.t Array32.t * W8.t Array32.t * W8.t Array64.t * polylvec * polykvec * polykvec = {
    var rho, k, tr,ski, i;
    var s1 : polylvec;
    var  s2,t0 : polykvec;  
    s1 <- witness;
    s2 <- witness;
    t0 <- witness;
    rho <- Array32.init(fun ii => sk.[ii]);
    k <- Array32.init(fun ii => sk.[ii+32]);
    tr <- Array64.init(fun ii => sk.[ii+64]);
    i <- 0;
    while (i < lvec) {
      ski <- BitUnpack (mkseq (fun ii => sk.[128 + 96*i + ii]) 256) Eta Eta;
      s1 <- s1.[i <- ski];
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitUnpack (mkseq (fun ii => sk.[128 + 96*lvec + 96*i + ii]) 256) Eta Eta;
      s2 <- s2.[i <- ski];
      i <- i + 1;
    }
    i <- 0;
    while (i < kvec) {
      ski <- BitUnpack (mkseq (fun ii => sk.[128 + 96*lvec + 96*kvec + 416*i + ii]) 256) (2^(d-1)) (2^(d-1));
      t0 <- t0.[i <- ski];
      i <- i + 1;
    }
    return (rho,k,tr,s1,s2,t0);  
  }
}.

module SigEncDec = {
  proc sigEncode(ct1 : W8.t Array32.t, ct2 : W8.t Array16.t, z : polylvec, h : polykvec) : W8.t Array3309.t = {
    var sigma, sigbytes, sigi, i;
    sigbytes <- [];
    i <- 0;
    while (i < lvec) {
       sigi <- BitPack z.[i] (gamma1 - 1) (gamma1);
       sigbytes <- sigbytes ++ sigi;
       i <- i + 1;
    }
    sigi <@ HintPackUnpack.hintBitPack(h);
    sigbytes <- sigbytes ++ sigi;
    sigma <- Array3309.init (fun ii =>
      if 0 <= ii < 32 then ct1.[ii]
      else if 32 <= ii < 96 then ct2.[ii]
      else nth witness sigbytes (ii - 96));
    return sigma;
  }

  proc sigDecode(sigma : W8.t Array3309.t) : 
    W8.t Array32.t * W8.t Array16.t * polylvec * polykvec option = {
     var ct1,ct2,sigi,h,i;
     var z : polylvec;
     z <- witness;
     ct1 <- Array32.init(fun ii => sigma.[ii]);
     ct2 <- Array16.init(fun ii => sigma.[ii-32]);
     i <- 0;
     while (i < lvec) {
       sigi <- BitUnpack (mkseq (fun ii => sigma.[48 + 96*i + ii]) 256) (gamma1 - 1) gamma1;
       z <- z.[i <- sigi];
       i <- i + 1;
    }
    h <@ HintPackUnpack.hintBitUnpack(mkseq (fun ii => sigma.[96 + 96*lvec + ii]) (kvec + w_hint));

    return (ct1,ct2,z,h);
  }
}.

op w1Encode(w1 : polykvec) : W8.t Array96.t = 
  Array96.of_list witness (flatten (map
    (fun wi => SimpleBitPack wi ((q-1)%/(2*gamma2) - 1)) (mkseq (fun ii => w1.[ii]) kvec))).
