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
import Vector.

(****************************************************************************)
  (****************************************************************************)
  (*  Encoding polys and vectors to and from byte arrays                      *)
  (****************************************************************************)
  (****************************************************************************)

type ipoly = int Array256.t.
op toipoly(p : poly) : ipoly = map asint p.
op ofipoly(p : ipoly)  : poly = map inFq p.

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

op toipolyvec(p : vector) : ipolyvec = map asint (fromarray256 p.[0] p.[1] p.[2]).

op ofipolyvec(p : ipolyvec) =  offunv (fun k => map inFq (subarray256 p k)).

op compress_polyvec(d : int, p : vector) : ipolyvec =  
  map (compress d) (fromarray256 p.[0] p.[1] p.[2]).

op decompress_polyvec(d : int, p : ipolyvec) =  
offunv (fun k => map (decompress d) (subarray256 p k)).



require import BitEncoding.
import BitChunking.

op BytesToBits(bytes : W8.t list) : bool list = flatten (map W8.w2bits bytes).
op decode(l : int, bits : bool list) = map bs2int (chunk l (take (256*l) bits)).
op decode_vec(l : int, bits : bool list) = map bs2int (chunk l (take (768*l) bits)).


  (* Decode Operators as Defined in the Kyber Spec *)
op sem_decode12(a : W8.t Array384.t) : ipoly =
  Array256.of_list 0 (decode 12 (BytesToBits (to_list a))).
op sem_decode4(a : W8.t Array128.t) : ipoly = 
  Array256.of_list 0 (decode 4 (BytesToBits (to_list a))).
op sem_decode1(a : W8.t Array32.t) : ipoly = 
  Array256.of_list 0 (decode 1 (BytesToBits (to_list a))).
op sem_decode10_vec(a : W8.t Array960.t) : ipolyvec = 
  Array768.of_list 0 (decode_vec 10 (BytesToBits (to_list a))).
op sem_decode12_vec(a : W8.t Array1152.t) : ipolyvec = 
  Array768.of_list 0 (decode_vec 12 (BytesToBits (to_list a))).

  (* To avoid loop matching pain with the implementation
  we adopt the same control structure and specify EncDec
  in a more palattable way. *)
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

      (* Extension to vectors *)

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
