require import AllCore BitEncoding List RealExp IntDiv.
from Jasmin require import JModel.

require import Array256.

require import GFq.
require import Rq.
require import VecMat.
import PolyVec.
import PolyMat.

op Eta : int = 2.

op IntegerToBits(x alpha : int) : bool list = BS2Int.int2bs alpha x. 
op BitsToInteger(y : bool list) : int = BS2Int.bs2int y.

op BitsToBytes(y : bool list) : W8.t list = map W8.bits2w (BitChunking.chunk 8 y).
op BytesToBits(x : W8.t list) : bool list = flatten (map W8.w2bits x).

op CoeffFromThreeBytes(b0 b1 b2 : W8.t) : int option = 
   let b2 = if 127 < to_uint b2 then b2 - W8.of_int 128 else b2 in
   let z = 2^16*to_uint b2 + 2^8 * to_uint b1 + to_uint b0 in
   if z < q then Some z else None.

op CoeffFromHalfByte(b : int) : int option =
   if Eta = 2 && b < 15 
   then Some (2 - (b %% 5))
   else if Eta = 4 && b < 9 
        then Some (4 - b)
        else None.

op SimpleBitPack(w : poly, b : int) : W8.t list = 
   let blen_b = ilog 2 b + 1 in
     BitsToBytes (flatten (map (fun wi => IntegerToBits (Zq.asint wi) blen_b) (Array256.to_list w))).

op BitPack(w : poly, a b : int) : W8.t list = 
   let blen_ab = ilog 2 (a + b) + 1 in
     BitsToBytes (flatten (map (fun wi => IntegerToBits (b - as_sint wi) blen_ab) (Array256.to_list w))).

op SimpleBitUnpack(v : W8.t list, b : int) : poly =
   let c = ilog 2 b + 1 in
   let z = BytesToBits(v) in
     Array256.init (fun i => nth witness (map (fun co => Zq.incoeff (BitsToInteger co)) (BitChunking.chunk c z)) i).

op BitUnpack(v : W8.t list, a b : int) : poly =
   let c = ilog 2 (a + b) + 1 in
   let z = BytesToBits(v) in
     Array256.init (fun i => nth witness (map (fun co => Zq.incoeff (b - BitsToInteger co)) (BitChunking.chunk c z)) i).

op w_hint = 55.

module HintPackUnpack = {
   proc hintBitPack(h : polyvec) : W8.t list = {
     var index : int;
     var y : W8.t list;
     var i,j;
     y <- mkseq (fun _ => W8.zero) (kvec + w_hint);
     index <- 0;
     i <- 0;
     while (i < kvec) {
        j <- 0;
        while (j < 256) {
           if (h.[i].[j] = Zq.one) {
              y <- put y j (W8.of_int index);
              index <- index + 1;
           }
           j <- j + 1;
        }
        y <- put y (w_hint + i) (W8.of_int index);
        i <- i + 1;
     }
     return y;
   }

   proc hintBitUnpack(y : W8.t list) : polyvec option = {
     var h : polyvec;
     var index : int;
     var error : bool;
     var i;
     h <- witness;
     index <- 0;
     error <- false;
     i <- 0;
     while (i < kvec) {
       if (to_uint (nth witness y (w_hint+i)) < index || 
                   w_hint < to_uint (nth witness y (w_hint+i))) {
           error <- true; 
       }
       while (index < to_uint (nth witness y (w_hint+i))) {
          h.[i] <- h.[i].[to_uint (nth witness y index) <- Zq.one];
          index <- index + 1;
       }
       
       i <- i + 1;
     }
     while (index < w_hint) {
       if (to_uint (nth witness y index) <> 0) {
         error <- true;
       }
       index <- index + 1;
     }
     return if error then None else Some h;
   }
}.

