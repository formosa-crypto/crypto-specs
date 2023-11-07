require import AllCore List Distr RealExp IntDiv.
require (*  *) Subtype.
from Jasmin require import JModel.
require import Notation Primitives.

import DList.
import NBytes.


clone import Subtype as SKEY with 
   type T = nbytes list,
   op P = fun l => size l = len
   rename "T" as "skey"
   proof inhabited by (exists (nseq len (nseq n W8.zero));smt(size_nseq ge0_len))
   proof *.

type message = nbytes.
type pkey = skey.
type signature = skey.

module WOTS = {
   proc genSK() : skey = {
      var sk <- (nseq len (nseq n W8.zero));
      var i <- 0;
      var ski;

      while (i < len) {
        ski <$ DList.dlist W8.dword n; 
        sk <- put sk i ski;
        i <- i + 1;
      }
      return sk;
   }

   proc genPK(sk : skey, _SEED : seed, _ADRS : adrs) : pkey = {
      var pk <- (nseq len (nseq n W8.zero));
      var i <- 0;
      var pki,ski;

      while (i < len) {
        ski <- nth witness sk i;
        pki <- chain ski 0 (w-1) _SEED _ADRS; 
        pk <- put pk i pki;
        i <- i + 1;
      }
      return sk;
   }

   proc kg(_SEED : seed, _ADRS : adrs) : skey * pkey = {
      var sk,pk;
      sk <@ genSK();
      pk <@ genPK(sk, _SEED, _ADRS);
      return (sk,pk);
   }

   proc sign(_M : message, sk : skey, _SEED : seed, _ADRS : adrs) : signature = {
      var csum : W32.t;
      var msg,i,mi,sig,len_2_bytes,csumw,ski,msgi,sigi;

      (* Convert message to base w *)
      msg<@BaseW.base_w(_M,len1);

      (* Compute checksum *)
      csum <- W32.zero;
      i <- 0;
      while (i < len1) {
         mi <- nth witness msg i;
         csum <- csum + W32.of_int (w - 1 - mi);
         i <- i + 1;
      } 
      csum <- csum `<<` W8.of_int ( 8 - ( ( len2 * floor (log2 w%r) ) %% 8 ));
      len_2_bytes <- ceil( ( len2%r * (log2 w%r) ) / 8%r );
      csumw <@ BaseW.base_w(toByte csum len_2_bytes, len2);
      msg <- msg ++ csumw;
      sig <- nseq len (nseq n W8.zero);
      i <- 0;
      while(i < len) {
         _ADRS <- setChainAddress _ADRS i;
         ski <- nth witness sk i;
         msgi <- nth witness msg i;
         sigi <@ Chain.chain(ski, 0, msgi, _SEED, _ADRS);
         sig <- put sig i sigi;
         i <- i + 1;
      }

      return sig;
   }

   proc pkFromSig(_M : message, sig : signature,  _SEED : seed, _ADRS : adrs) : pkey = {
      var csum : W32.t;
      var msg,i,mi,len_2_bytes,csumw,msgi,sigi,tmp_pk,pki;

      if (size _M = n) {
         (* Convert message to base w *)
         msg<@BaseW.base_w(_M,len1);

         (* Compute checksum *)
         csum <- W32.zero;
         i <- 0;
         while (i < len1) {
            mi <- nth witness msg i;
            csum <- csum + W32.of_int (w - 1 - mi);
            i <- i + 1;
         } 

         csum <- csum `<<` W8.of_int ( 8 - ( ( len2 * floor (log2 w%r) ) %% 8 ));
         len_2_bytes <- ceil( ( len2%r * (log2 w%r) ) / 8%r );
         csumw <@ BaseW.base_w(toByte csum len_2_bytes, len2);
         msg <- msg ++ csumw;
         sig <- nseq len (nseq n W8.zero);
         i <- 0;
         while(i < len) {
            _ADRS <- setChainAddress _ADRS i;
            msgi <- nth witness msg i;
            sigi <- nth witness sig i;
            pki <@ Chain.chain(sigi, msgi, w - 1 - msgi, _SEED, _ADRS); 
            tmp_pk <- put tmp_pk i pki; 
            i <- i + 1;
         }
      }
      return tmp_pk;

   }

   proc verify(pk : pkey, _M : message, sig : signature,  _SEED : seed, _ADRS : adrs) : bool = {
      var tmp_pk;
      tmp_pk <@ pkFromSig(_M,sig,_SEED,_ADRS);
      return pk = tmp_pk;
   }

}.
