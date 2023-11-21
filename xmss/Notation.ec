require import AllCore List RealExp IntDiv Array32 Array8.
from Jasmin require import JModel.

type byte = W8.t.

(* prefix of big endian byte representation of a 32-bit word *)
op toByte(x : W32.t, k : int) : byte list =  
     take k (rev (to_list (W4u8.unpack8 x))).

(* the range of indices into a wots chain *)
op w : { int | w = 4 \/ w = 16} as w_vals.

module BaseW = {
  proc base_w(_X : byte list, out_len : int) : int list = {
       var _in : int <- 0;
       var out : int <- 0;
       var total : W8.t <- W8.of_int 0;
       var bits : int <- 0;
       var consumed : int <- 0;
       var basew : int list;

       basew <- nseq out_len 0;

       while (consumed < out_len) {
           if (bits = 0) {
               total <- nth witness _X _in;
               _in <- _in + 1;
               bits <- bits + 8;
           }
           bits <- bits - floor (log2 w%r);
           basew <- put basew out 
             (W8.to_uint
               ((total `>>` W8.of_int bits) 
                          `&` W8.of_int (w - 1)));
           out <- out + 1;
           consumed <- consumed + 1;
       }
       return basew;  }
}.

pred base_w_pre(_X : W8.t list, out_len :int) = 
   out_len <= 8 * size _X %/ floor (log2 w%r).

pred base_w_post(_X : W8.t list, out_len :int, 
                 base_w : W8.t list) =
    size base_w = out_len /\
    all (fun x => 0 <= W8.to_uint x <= w-1) base_w.

(*
 +-------------------------+
 | layer address  (32 bits)| 0 
 +-------------------------+
 | tree address   (64 bits)| 1,2
 +-------------------------+
 | type = 0       (32 bits)| 3
 +-------------------------+
 | OTS address    (32 bits)| 4
 +-------------------------+
 | chain address  (32 bits)| 5
 +-------------------------+
 | hash address   (32 bits)| 6
 +-------------------------+
 | keyAndMask     (32 bits)| 7
 +-------------------------+
*)

type adrs = W32.t Array8.t.

op setChainAddress(_ADRS : adrs, chainadrs : int) =
   _ADRS.[5 <- W32.of_int chainadrs].

op setHashAddress(_ADRS : adrs, hashadrs : int) =
   _ADRS.[6 <- W32.of_int hashadrs].

op setKeyAndMask(_ADRS : adrs, keyandmask : int) =
   _ADRS.[7 <- W32.of_int keyandmask].

