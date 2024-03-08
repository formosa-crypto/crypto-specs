require import AllCore.
require import IntDiv.
require import List.
require import Ring.
require import Array256.

require import GFq.
import Zq.

(******************************************************)
(* Representations of polynomials in Zq[X]/(X^256+1)  *)
(* We use an array representation for both Rq and ntt *)
(* domain.                                            *)
(******************************************************)

type poly = coeff Array256.t.

op zero : poly = Array256.create Zq.zero.
op one : poly = zero.[0<-Zq.one].

(* Ring multiplication: schoolbook multiplication in this
ring is essentially generating a square matrix of coefficient
multiplications and summing over the columns. *)
op (&*) (pa pb : poly) : poly =
  Array256.init (fun (i : int) => foldr (fun (k : int) (ci : coeff) =>
  if (0 <= i - k) 
  then ci + pa.[k] * pb.[i - k] 
  else ci - pa.[k] * pb.[256 + (i - k)]) 
  Zq.zero (iota_ 0 256)).

op (&+) (pa pb : poly) : poly = 
  map2 (fun a b : coeff  => Zq.(+) a b) pa pb.

op (&-) (p : poly) : poly =  map Zq.([-]) p.

(*
(* Compression/decompression of polys *)

op compress_poly(d : int, p : poly) : int Array256.t =  map (compress d) p.

op decompress_poly(d : int, p : int Array256.t) : poly =  map (decompress d) p.
*)

(**************************************************)
(**************************************************)

(* The NTT operation over ring elements 

*)

require (****) Bigalg.
clone import Bigalg.BigComRing as BigDom with
type  CR.t     <- coeff,
op  CR.zeror <- Zq.zero,
op  CR.oner  <- Zq.one,
op  CR.(+)   <- Zq.(+),
op  CR.([-]) <- Zq.([-]),
op  CR.( * ) <- Zq.( * ),
op  CR.invr  <- Zq.inv,
op  CR.ofint <- ZqRing.ofint,
pred  CR.unit  <- Zq.unit
proof *.

realize CR.addrA     by apply ZqRing.addrA.
realize CR.addrC     by apply ZqRing.addrC.
realize CR.add0r     by apply ZqRing.add0r.
realize CR.addNr     by apply ZqRing.addNr.
realize CR.oner_neq0 by apply ZqRing.oner_neq0.
realize CR.mulrA     by apply ZqRing.mulrA.
realize CR.mulrC     by apply ZqRing.mulrC.
realize CR.mul1r     by apply ZqRing.mul1r.
realize CR.mulrDl    by apply ZqRing.mulrDl.
realize CR.mulVr     by apply ZqRing.mulVr.
realize CR.unitP     by apply ZqRing.unitP.
realize CR.unitout   by apply ZqRing.unitout.

op zroot = incoeff 1753.

op br = BitEncoding.BitReverse.bsrev 8.
op ntt(p : poly) : poly = Array256.init (fun i => 
  if i %% 2  = 0
  then let ii = i %/ 2 in BAdd.bigi predT (fun j => p.[j] * ZqRing.exp zroot ((br (ii + 128)) * j)) 0 256
  else let ii = i %/ 2 in BAdd.bigi predT (fun j => p.[j] * ZqRing.exp (-zroot) ((br (ii + 128)) * j)) 0 256) axiomatized by nttE.

op invntt(p : poly) : poly.
(* = Array256.init (fun i => 
  if i %% 2  = 0 
  then let ii = i %/ 2 in BAdd.bigi predT (fun j => inv (incoeff 128) * p.[2*j]   * ZqRing.exp zroot (-((2 * br j + 1) * ii))) 0 128
  else let ii = i %/ 2 in BAdd.bigi predT (fun j => inv (incoeff 128) * p.[2*j+1] * ZqRing.exp zroot (-((2 * br j + 1) * ii))) 0 128) axiomatized by invnttE. *)

(* The base multiplication in the NTT domain pointwise. *)

op basemul(a b : poly) :  poly = Array256.init (fun i => a.[i] * b.[i]).

