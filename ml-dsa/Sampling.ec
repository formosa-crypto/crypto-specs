require import AllCore IntDiv.
from Jasmin require import JModel.

require import Array2 Array32 Array64 Array136 Array168 Array256 Array320.
require import GFq.
require import Rq.
import Zq.

require import Symmetric Conversion VecMat.
import PolyMat.
import PolyKVec.
import PolyLVec.

op tau = 33.

module SampleInBall = {
   proc sample(rho : W8.t Array32.t) : poly = {
      var b136 : W8.t Array136.t;
      var signbytes : W64.t;
      var k,i,j;
      var c : poly;
      c <- witness;
      H.init32(rho);
      b136 <@ H.next_bytes();
      signbytes <- W8u8.pack8_t (W8u8.Pack.init (fun ii => b136.[ii]));
      k <- 8;
      i <- 256 - tau;
      while (i < 256) {
          while (k < 136 && i < 256) {
             if (to_uint b136.[k] <= i) {
                j <- to_uint b136.[k];
                c.[i] <- c.[j];
                c.[j] <- if signbytes.[i + tau - 256] then incoeff (-1) else incoeff (1);
                i <- i + 1;
             }
             k <- k + 1;
          }
          if ( i < 256) { b136 <@ H.next_bytes(); k <- 0; }
      }
      return c;
   }
}.

module RejNTTPoly = {
  proc sample(rho : W8.t Array32.t, r s : W8.t) : poly = {
    var j, b168, bi, bi1, bi2, k,co;
    var c : poly;
    c <- witness;
    H128.init(rho,r,s);
    j <- 0;
    while (j < 256) {
      b168 <@ H128.next_bytes();
      k <- 0;
      while ((j < 256) && (k < 168)) {
        bi  <- b168.[k];
        bi1 <- b168.[k+1];
        bi2 <- b168.[k+2];
        k <- k + 3;
        co <- CoeffFromThreeBytes bi bi1 bi2;
        if (co <> None) {
           c.[j] <- incoeff (oget co);
           j <- j + 1;
        }
      }
    }
    return c;
  }
}.

module RejBoundedPoly = {
  proc sample(rho : W8.t Array64.t,r : W16.t) : poly = {
    var j,b136,k,z,z0,z1;
    var a : poly;
    a <- witness;
    H.init66(rho,r);
    j <- 0;
    while (j < 256) {
      b136 <@ H.next_bytes();
      k <- 0;
      while ((j < 256) && (k < 136)) {
        z  <- b136.[k];
        k <- k + 1;
        z0 <- CoeffFromHalfByte (to_uint z %% 16);
        z1 <- CoeffFromHalfByte (to_uint z %/ 16);
        if (z0 <> None) { a.[j] <- incoeff (oget z0); j <- j + 1; }
        if ((z1 <> None) && (j < 256)) { a.[j] <- incoeff (oget z1); j <- j + 1; }
      }
    }
    return a;
  }
}.

module ExpandA = {
   proc sample(rho : W8.t Array32.t) : polymat = {
      var r,s,ars;
      var aa : polymat;
      aa <- witness;
      r <- 0;
      while (r < kvec) {
          s <- 0;
          while (s < lvec) {
            ars <@ RejNTTPoly.sample(rho,W8.of_int r, W8.of_int s);
            aa <- aa.[(r,s) <- ars];
            s <- s + 1;
          }
          r <- r + 1;
      }
      return aa;
   }
}.

module ExpandS = {
   proc sample(rho : W8.t Array64.t) : polylvec * polykvec = {
      var si,r;
      var s1 : polylvec;
      var s2 : polykvec;
      s1 <- witness;
      s2 <- witness;
      r <- 0;
      while (r < lvec) {
         si <@ RejBoundedPoly.sample(rho,W16.of_int r);
         s1 <- s1.[r <- si];
            r <- r + 1;
      }
      while (r < kvec) {
         si <@ RejBoundedPoly.sample(rho,W16.of_int (r + lvec));
         s2 <- s2.[r <- si];
         r <- r + 1;
      }
      return (s1,s2);
   }
}.

module ExpandMask = {
   proc sample(rho : W8.t Array64.t, u : int) : polylvec = {
     var r, b320,si;
     var s : polylvec;
     s <- witness;
     r <- 0;
     while (r < lvec) {
        b320 <- Hhint rho (W16.of_int (r + u));
        si <- BitUnpack (to_list b320) (gamma1-1) (gamma1);
        s <- s.[r <- si];
        r <- r + 1;
     }
     return s;
   }
}.
