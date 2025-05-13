(* General EC imports *)
require import AllCore IntDiv List.

from Jasmin require import JWord.

from JazzEC require import Array32 Array128 Array160 Array256 Array384 Array768 Array960 Array1024 Array1152 Array1408 Array1536.

import BitEncoding BS2Int.

(* Imports of "lower-level" MLKEM spec parts *)
require import GFq.
import Zq.
require import Rq.

require import VecMat.

type ipoly = int Array256.t.
op toipoly(p : poly) : ipoly = map asint p.
op ofipoly(p : ipoly)  : poly = map incoeff p.

theory Serialization768.

import VecMat768 PolyVec PolyMat.

type ipolyvec = int Array768.t.

op [a] subarray256(x : 'a Array768.t, i : int) =
Array256.init (fun k => x.[256*i + k]).

op [a] fromarray256(a0 a1 a2 : 'a Array256.t) : 'a Array768.t = 
  Array768.init (fun k => if 0 <= k < 256
                        then a0.[k]
                        else if 256 <= k < 512
                             then a1.[k-256] 
                             else a2.[k-512]).   

op [a] subarray384(x : 'a Array1152.t, i : int) =
      Array384.init (fun k => x.[384*i + k]).

op [a] fromarray384(a0 a1 a2 : 'a Array384.t) : 'a Array1152.t = 
Array1152.init (fun k => if 0 <= k < 384
                         then a0.[k]
                         else if 384 <= k < 768
                         then a1.[k-384] 
                         else a2.[k-768]).   

op toipolyvec(p : polyvec) : ipolyvec = map asint (fromarray256 p.[0] p.[1] p.[2]).

op ofipolyvec(p : ipolyvec) : polyvec =  
    zerov.[0 <- map incoeff (subarray256 p 0)]
         .[1 <- map incoeff (subarray256 p 1)]
         .[2 <- map incoeff (subarray256 p 2)].

op compress_polyvec(d : int, p : polyvec) : ipolyvec =  
     map (compress d) (fromarray256 p.[0] p.[1] p.[2]).

op decompress_polyvec(d : int, p : ipolyvec) =  
    zerov.[0 <- map (decompress d) (subarray256 p 0)]
         .[1 <- map (decompress d) (subarray256 p 1)]
         .[2 <- map (decompress d) (subarray256 p 2)].

(* To avoid loop matching pain with the implementation
 we adopt the same control structure and specify EncDec
 in a more palatable way. *)

module EncDec = {

  proc decode12(a : W8.t Array384.t) : ipoly = {
    var i;
    var r : ipoly;
    r <- witness;
    i <- 0;
    while (i < 128) {
      r.[i*2+0]  <- to_uint a.[3*i] + to_uint a.[3*i+1] %% 2^4 * 2^8;
      r.[i*2+1]  <- to_uint a.[3*i+2] * 2^4 + to_uint a.[3*i+1] %/ 2^4;
      i <- i + 1;
    }
    return r;
  }

  proc decode4(a : W8.t Array128.t) : ipoly = {
    var i;
    var r : ipoly;
    r <- witness;
    i <- 0;
    while (i < 128) {
      r.[i*2+0]  <- to_uint a.[i] %% 16;
      r.[i*2+1]  <- to_uint a.[i] %/ 16;
      i <- i + 1;
    }
    return r;
  }

  proc decode1(a : W8.t Array32.t) : ipoly = {
    var i;
    var r : ipoly;
    r <- witness;
    i <- 0;
    while (i < 32) {
      r.[i*8+0] <- b2i a.[i].[0];
      r.[i*8+1] <- b2i a.[i].[1];
      r.[i*8+2] <- b2i a.[i].[2];
      r.[i*8+3] <- b2i a.[i].[3];
      r.[i*8+4] <- b2i a.[i].[4];
      r.[i*8+5] <- b2i a.[i].[5];
      r.[i*8+6] <- b2i a.[i].[6];
      r.[i*8+7] <- b2i a.[i].[7];
      i<-i+1;
    }
    return r;
  }

  proc encode12(a : ipoly) : W8.t Array384.t = {
    var fi1,fi2,i,j;
    var r : W8.t Array384.t;
    r <- witness;
    j <- 0; i <- 0; 
    while (i < 256) {
      fi1 <- a.[i];
      fi2 <- a.[i+1];
      r.[j] <- W8.of_int fi1;                               j <- j + 1;
      r.[j] <- W8.of_int ((fi2 %% 2^4) * 2^4 + fi1 %/ 2^8); j <- j + 1;
      r.[j] <- W8.of_int (fi2 %/ 2^4);                      j <- j + 1;
      i <- i + 2;
    }
    return r;
  }

  proc encode4(p : ipoly) : W8.t Array128.t = {
    var fi,fi1,i,j;
    var r : W8.t Array128.t;
    r <- witness;
    j <- 0; i <- 0; 
    while (i < 128) {
      fi <- p.[j]; j <- j + 1;
      fi1 <- p.[j]; j <- j + 1; 
      r.[i] <- W8.of_int (fi + fi1 * 2^4); i <- i + 1;
    }
    return r;
  }

  proc encode1(a : ipoly) : W8.t Array32.t = {
    var i,j,r;
    var ra : W8.t Array32.t;
    ra <- witness;
    i <- 0;
    while (i < 32) {
      r <- W8.zero;
      j <- 0;
      while (j < 8) {
        r <- W8.of_int (to_uint r + a.[8*i+j] * 2^j);
        j <- j + 1;
      }
      ra.[i] <- r;
      i <- i + 1;
    }
    return ra;      
  }

  (* Extension to polyvecs *)

  proc encode10_vec(u : ipolyvec) : W8.t Array960.t = {
    var c : W8.t Array960.t;
    var i,j,t0,t1,t2,t3;
    c <- witness;
    j <- 0; i <- 0; 
    while (i < 768) {
      t0 <- u.[i];
      t1 <- u.[i + 1];
      t2 <- u.[i + 2];
      t3 <- u.[i + 3];
      c.[j] <- W8.of_int t0; j <- j + 1;
      c.[j] <-  W8.of_int (t0 %/ 2^8 + t1 * 2^2); j <- j + 1;
      c.[j] <-  W8.of_int (t1 %/ 2^6 + t2 * 2^4); j <- j + 1;
      c.[j] <-  W8.of_int (t2 %/ 2^4 + t3 * 2^6); j <- j + 1;
      c.[j] <-  W8.of_int (t3 %/ 2^2); j <- j + 1;
      i <- i + 4;
    }
    return c;
  }

  proc encode12_vec(a : ipolyvec) : W8.t Array1152.t = {
    var a1, a2, a3;
    a1 <@ encode12(subarray256 a 0);
    a2 <@ encode12(subarray256 a 1);
    a3 <@ encode12(subarray256 a 2);
    return fromarray384 a1 a2 a3;
  }

  proc decode10_vec(u : W8.t Array960.t) : ipolyvec = {
    var c : ipolyvec;
    var i,j,t0,t1,t2,t3,t4;
    c <- witness;
    j <- 0; i <- 0; 
    while (i < 768) {
      t0 <- u.[j]; t1 <- u.[j + 1]; t2 <- u.[j + 2]; t3 <- u.[j + 3]; t4 <- u.[j + 4];
      c.[i] <- to_uint t0 + (to_uint t1 %% 2^2) * 2^8;
      c.[i + 1] <-  to_uint t1 %/ 2^2 + (to_uint t2 %% 2^4) * 2^6;
      c.[i + 2] <-  to_uint t2 %/ 2^4 + (to_uint t3 %% 2^6) * 2^4;
      c.[i + 3] <-  to_uint t3 %/ 2^6 + (to_uint t4) * 2^2;
      j <- j + 5;
      i <- i + 4;
    }
    return c;
  }


  proc decode12_vec(a : W8.t Array1152.t) : ipolyvec = {
    var a1, a2, a3;
    a1 <@ decode12(subarray384 a 0);
    a2 <@ decode12(subarray384 a 1);
    a3 <@ decode12(subarray384 a 2);
    return fromarray256 a1 a2 a3;
  }

}.

(* Fixme: Move to properties file. Needs EC feature. *)
proc op encode4 = EncDec.encode4.
proc op encode1 = EncDec.encode1.
proc op encode10_vec = EncDec.encode10_vec.
proc op encode12 = EncDec.encode12.
proc op encode12_vec = EncDec.encode12_vec.

proc op decode4 = EncDec.decode4.
proc op decode1 = EncDec.decode1.
proc op decode10_vec = EncDec.decode10_vec.
proc op decode12 = EncDec.decode12.
proc op decode12_vec = EncDec.decode12_vec.

end Serialization768.

theory Serialization1024.

import VecMat1024 PolyVec PolyMat.

type ipolyvec = int Array1024.t.

op [a] subarray256(x : 'a Array1024.t, i : int) =
Array256.init (fun k => x.[256*i + k]).

op [a] fromarray256(a0 a1 a2 a3 : 'a Array256.t) : 'a Array1024.t = 
  Array1024.init (fun k => if 0 <= k < 256
                        then a0.[k]
                        else if 256 <= k < 512
                             then a1.[k - 256]
                             else if 512 <= k < 768
                                  then a2.[k-512] 
                                  else a3.[k-768]).   

op [a] subarray384(x : 'a Array1536.t, i : int) =
      Array384.init (fun k => x.[384*i + k]).

op [a] fromarray384(a0 a1 a2 a3 : 'a Array384.t) : 'a Array1536.t = 
Array1536.init (fun k => if 0 <= k < 384
                         then a0.[k]
                         else if 384 <= k < 768
                              then a1.[k-384] 
                              else if 768 <= k < 1152
                                   then a2.[k-768] 
                                   else a3.[k-1152]).   

op toipolyvec(p : polyvec) : ipolyvec = map asint (fromarray256 p.[0] p.[1] p.[2] p.[3]).

op ofipolyvec(p : ipolyvec) : polyvec =  
    zerov.[0 <- map incoeff (subarray256 p 0)]
         .[1 <- map incoeff (subarray256 p 1)]
         .[2 <- map incoeff (subarray256 p 2)]
         .[3 <- map incoeff (subarray256 p 3)].

op compress_polyvec(d : int, p : polyvec) : ipolyvec =  
     map (compress d) (fromarray256 p.[0] p.[1] p.[2] p.[3]).

op decompress_polyvec(d : int, p : ipolyvec) =  
    zerov.[0 <- map (decompress d) (subarray256 p 0)]
         .[1 <- map (decompress d) (subarray256 p 1)]
         .[2 <- map (decompress d) (subarray256 p 2)]
         .[3 <- map (decompress d) (subarray256 p 3)].

(* To avoid loop matching pain with the implementation
 we adopt the same control structure and specify EncDec
 in a more palatable way. *)

module EncDec = {

  proc decode12(a : W8.t Array384.t) : ipoly = {
    var i;
    var r : ipoly;
    r <- witness;
    i <- 0;
    while (i < 128) {
      r.[i*2+0]  <- to_uint a.[3*i] + to_uint a.[3*i+1] %% 2^4 * 2^8;
      r.[i*2+1]  <- to_uint a.[3*i+2] * 2^4 + to_uint a.[3*i+1] %/ 2^4;
      i <- i + 1;
    }
    return r;
  }

  proc decode5(a : W8.t Array160.t) : ipoly = {
    var i,j,b1,b2,b3,b4,b5;
    var r : ipoly;
    r <- witness;
    j <- 0; i <- 0; 
    while (i < 160) {
      b1 <- a.[i];
      b2 <- a.[i+1];
      b3 <- a.[i+2];
      b4 <- a.[i+3];
      b5 <- a.[i+4];
      r.[j]  <- to_uint b1 %% 2^5; j <- j + 1;
      r.[j]  <- to_uint b1 %/ 2^5 + (to_uint b2 %% 2^2) * 2^3; j <- j + 1;
      r.[j]  <- (to_uint b2 %/ 2^2) %% 2^5; j <- j + 1;
      r.[j]  <- to_uint b2 %/ 2^7 + (to_uint b3 %% 2^4) * 2^1; j <- j + 1;
      r.[j]  <- to_uint b3 %/ 2^4 + (to_uint b4 %% 2^1) * 2^4; j <- j + 1;
      r.[j]  <- (to_uint b4 %/ 2^1) %% 2^5; j <- j + 1;
      r.[j]  <- to_uint b4 %/ 2^6 + (to_uint b5 %% 2^3) * 2^2; j <- j + 1;
      r.[j] <- (to_uint b5) %/ 2^3; j <- j + 1;
      i <- i + 5;
    }
    return r;
  }

  proc decode1(a : W8.t Array32.t) : ipoly = {
    var i;
    var r : ipoly;
    r <- witness;
    i <- 0;
    while (i < 32) {
      r.[i*8+0] <- b2i a.[i].[0];
      r.[i*8+1] <- b2i a.[i].[1];
      r.[i*8+2] <- b2i a.[i].[2];
      r.[i*8+3] <- b2i a.[i].[3];
      r.[i*8+4] <- b2i a.[i].[4];
      r.[i*8+5] <- b2i a.[i].[5];
      r.[i*8+6] <- b2i a.[i].[6];
      r.[i*8+7] <- b2i a.[i].[7];
      i<-i+1;
    }
    return r;
  }

  proc encode12(a : ipoly) : W8.t Array384.t = {
    var fi1,fi2,i,j;
    var r : W8.t Array384.t;
    r <- witness;
    j <- 0; i <- 0; 
    while (i < 256) {
      fi1 <- a.[i];
      fi2 <- a.[i+1];
      r.[j] <- W8.of_int fi1;                               j <- j + 1;
      r.[j] <- W8.of_int ((fi2 %% 2^4) * 2^4 + fi1 %/ 2^8); j <- j + 1;
      r.[j] <- W8.of_int (fi2 %/ 2^4);                      j <- j + 1;
      i <- i + 2;
    }
    return r;
  }

  proc encode5(p : ipoly) : W8.t Array160.t = {
    var fi,fi1,fi2,fi3,fi4,fi5,fi6,fi7,i,j;
    var r : W8.t Array160.t;
    r <- witness;
    j <- 0; i <- 0; 
    while (i < 160) {
      fi  <- p.[j]; j <- j + 1;
      fi1 <- p.[j]; j <- j + 1; 
      fi2 <- p.[j]; j <- j + 1;
      fi3 <- p.[j]; j <- j + 1; 
      fi4 <- p.[j]; j <- j + 1;
      fi5 <- p.[j]; j <- j + 1; 
      fi6 <- p.[j]; j <- j + 1;
      fi7 <- p.[j]; j <- j + 1; 
      r.[i] <- W8.of_int (fi + fi1 * 2^5);
      r.[i+1] <- W8.of_int (fi1 %/ 2^3 + fi2 * 2^2 + fi3*2^7);
      r.[i+2] <- W8.of_int (fi3 %/ 2^1 + fi4 * 2^4);
      r.[i+3] <- W8.of_int (fi4 %/ 2^4 + fi5 * 2^1 + fi5 * 2^6);
      r.[i+4] <- W8.of_int (fi6 %/ 2^2 + fi7 * 2^3);
      i <- i + 5;
    }
    return r;
  }

  proc encode1(a : ipoly) : W8.t Array32.t = {
    var i,j,r;
    var ra : W8.t Array32.t;
    ra <- witness;
    i <- 0;
    while (i < 32) {
      r <- W8.zero;
      j <- 0;
      while (j < 8) {
        r <- W8.of_int (to_uint r + a.[8*i+j] * 2^j);
        j <- j + 1;
      }
      ra.[i] <- r;
      i <- i + 1;
    }
    return ra;      
  }

  (* Extension to polyvecs *)

  proc encode11_vec(u : ipolyvec) : W8.t Array1408.t = {
    var c : W8.t Array1408.t;
    var i,j;
    c <- witness;
    j <- 0; i <- 0; 
    (* 
    while (i < 1024) {
      t0 <- u.[i];
      t1 <- u.[i + 1];
      t2 <- u.[i + 2];
      t3 <- u.[i + 3];
      c.[j] <- W8.of_int t0; j <- j + 1;
      c.[j] <-  W8.of_int (t0 %/ 2^8 + t1 * 2^2); j <- j + 1;
      c.[j] <-  W8.of_int (t1 %/ 2^6 + t2 * 2^4); j <- j + 1;
      c.[j] <-  W8.of_int (t2 %/ 2^4 + t3 * 2^6); j <- j + 1;
      c.[j] <-  W8.of_int (t3 %/ 2^2); j <- j + 1;
      i <- i + 4;
    } 
    *)
    return c;
  }

  proc encode12_vec(a : ipolyvec) : W8.t Array1536.t = {
    var a1, a2, a3, a4;
    a1 <@ encode12(subarray256 a 0);
    a2 <@ encode12(subarray256 a 1);
    a3 <@ encode12(subarray256 a 2);
    a4 <@ encode12(subarray256 a 3);
    return fromarray384 a1 a2 a3 a4;
  }

  proc decode11_vec(u : W8.t Array1408.t) : ipolyvec = {
    var c : ipolyvec;
    var i,j;
    c <- witness;
    j <- 0; i <- 0; 
    (* 
    while (i < 1024) {
      t0 <- u.[j]; t1 <- u.[j + 1]; t2 <- u.[j + 2]; t3 <- u.[j + 3]; t4 <- u.[j + 4];
      c.[i] <- to_uint t0 + (to_uint t1 %% 2^2) * 2^8;
      c.[i + 1] <-  to_uint t1 %/ 2^2 + (to_uint t2 %% 2^4) * 2^6;
      c.[i + 2] <-  to_uint t2 %/ 2^4 + (to_uint t3 %% 2^6) * 2^4;
      c.[i + 3] <-  to_uint t3 %/ 2^6 + (to_uint t4) * 2^2;
      j <- j + 5;
      i <- i + 4;
    }
    *)
    return c;
  }


  proc decode12_vec(a : W8.t Array1536.t) : ipolyvec = {
    var a1, a2, a3, a4;
    a1 <@ decode12(subarray384 a 0);
    a2 <@ decode12(subarray384 a 1);
    a3 <@ decode12(subarray384 a 2);
    a4 <@ decode12(subarray384 a 3);
    return fromarray256 a1 a2 a3 a4;
  }

}.

(* Fixme: Move to properties file. Needs EC feature. *)
proc op encode5 = EncDec.encode5.
proc op encode1 = EncDec.encode1.
proc op encode11_vec = EncDec.encode11_vec.
proc op encode12 = EncDec.encode12.
proc op encode12_vec = EncDec.encode12_vec.

proc op decode5 = EncDec.decode5.
proc op decode1 = EncDec.decode1.
proc op decode11_vec = EncDec.decode11_vec.
proc op decode12 = EncDec.decode12.
proc op decode12_vec = EncDec.decode12_vec.

end Serialization1024.

