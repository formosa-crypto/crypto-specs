require import AllCore List.
from Jasmin require import JModel.

require import Parameters GFq Rq VecMat Conversion Serialization Symmetric Sampling.
import PolyKVec PolyLVec PolyMat.
import Zq.

require import Array32 Array64 Array96 Array256 Array1952 Array3309 Array4032.

module MLDSA = {
   proc keygen_derand(eps : W8.t Array32.t) : W8.t Array4032.t * W8.t Array1952.t= {
     var sk,rho,rhop,_K,_A,s1,s2,t,t1,t0,pk,tr;
     (rho,rhop,_K) <- Hseed eps;
     _A <@ ExpandA.sample(rho);
     (s1,s2) <@ ExpandS.sample(rhop);
     t <- invnttv (ntt_mmul _A (nttv s1)) + s2;
     (t1,t0) <- polykvec_Power2Round t;
     pk <@ PkEncDec.pkEncode(rho,t1);
     tr <- Hpk pk;
     sk <@ SkEncDec.skEncode(rho,_K,tr,s1,s2,t0);
     return (sk,pk);
  }

  proc sign_derand(sk : W8.t Array4032.t, m : W8.t list, coins : W8.t Array32.t) : W8.t Array3309.t = {
     var rho,_K,tr,s1,s2,t0,s1h,s2h,t0h,_A,mu,rhop,kappa,ct1,ct2,sigma,y,w,w1,c,ch,cs1,cs2,z,r0,ct0,h;
     var zh : (polylvec * polykvec) option;
     ct1 <- witness; ct2 <- witness;
     (rho,_K,tr,s1,s2,t0) <@ SkEncDec.skDecode(sk);
     s1h <- nttv s1;
     s2h <- nttv s2;
     t0h <- nttv t0;
     _A <@ ExpandA.sample(rho);
     mu <- Hm tr m;
     rhop <- Hprivsd _K coins mu;
     kappa <- 0;
     zh <- None;
     while (zh = None) {
       y <@ ExpandMask.sample(rhop,kappa);
       w <- invnttv (ntt_mmul _A (nttv y));
       w1 <- polykvec_HighBits w;
       (ct1,ct2) <- Hcomm mu (w1Encode w1);
       c <@ SampleInBall.sample(ct1);
       ch <- ntt c;
       cs1 <- invnttv (polylvec_ntt_smul ch s1);
       cs2 <- invnttv (polykvec_ntt_smul ch s2);
       z <- y + cs1;
       r0 <- polykvec_LowBits (w - cs2);
       if (polylvec_infnorm z (gamma1 - Beta) && polykvec_infnorm r0 (gamma2 - Beta)) {
          ct0 <- invnttv (polykvec_ntt_smul ch t0);
          h <- polykvec_MakeHint (PolyKVec.zerov-ct0) w - cs2 + ct0;
          if (polykvec_infnorm ct0 gamma2 && polykvec_hammw h w_hint) {
             zh <- Some (z,h);
          }
       }
       kappa <- kappa + lvec;
     }
     sigma <@ SigEncDec.sigEncode(ct1,ct2,polylvec_mods (oget zh).`1 q,(oget zh).`2);
     return sigma;
  }

  proc verify(pk : W8.t Array1952.t, sigma : W8.t Array3309.t, m : W8.t list) : bool = {
    var rho,t1,ct1,ct2,z,h,rb,_A,tr,mu,c,wapprox,w1,ctp;
    rb <- false;
    (rho,t1) <@ PkEncDec.pkDecode(pk);
    (ct1,ct2,z,h) <@ SigEncDec.sigDecode(sigma);
    if (h <> None) {
      _A <@ ExpandA.sample(rho);
      tr <- Hpk pk;
      mu <- Hm tr m;
      c <@ SampleInBall.sample(ct1);
      wapprox <- invnttv (ntt_mmul _A (nttv z) - (polykvec_ntt_smul (ntt c) (nttv (smul t1 (incoeff (2^d))))));
      w1 <- polykvec_UseHint (oget h) wapprox;
      ctp <- Hcomm mu (w1Encode w1);
      rb <- polylvec_infnorm z (gamma1 - Beta);
      rb <- rb && (ct1,ct2) = ctp && polykvec_hammw (oget h) w_hint;
    }
    return rb;
  }
}.
