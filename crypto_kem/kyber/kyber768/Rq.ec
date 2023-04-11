require import AllCore.
require import IntDiv.
require import List.
require import Ring.
require import Array256.

require import GFq.
import Zq.

(*****************************************************)
(* Representations of polynomials in Zq[X]/(X^256+1) *)
(*****************************************************)

type poly = Fq Array256.t.

op zero : poly = Array256.create Zq.zero.
op one : poly = zero.[0<-Zq.one].

(* Ring multiplication: schoolbook multiplication in this
ring is essentially generating a square matrix of coefficient
multiplications and summing over the columns. *)
op (&*) (pa pb : poly) : poly =
  Array256.init (fun (i : int) => foldr (fun (k : int) (ci : Fq) =>
  if (0 <= i - k) 
  then ci + pa.[k] * pb.[i - k] 
  else ci - pa.[k] * pb.[256 + (i - k)]) 
  Zq.zero (iota_ 0 256)).

op (&+) (pa pb : poly) : poly = 
  map2 (fun a b : Fq  => Zq.(+) a b) pa pb.

op (&-) (p : poly) : poly =  map Zq.([-]) p.

(* Compression/decompression of polys *)

op compress_poly(d : int, p : poly) : int Array256.t =  map (compress d) p.

op decompress_poly(d : int, p : int Array256.t) : poly =  map (decompress d) p.


(**************************************************)
(**************************************************)

(* The NTT operation over ring elements 

We give here the mathematical specification of the NTT in
a way that roughly matches what is described in the spec.

Then we will have an NTT.ec file where we prove that 1) the imperative
specs are equivalent to these operators and 2) that these operators have
the properties we require to show that Kyber is correct up to some
decryption failure bound.

*)

require (****) Bigalg.
clone import Bigalg.BigComRing as BigDom with
type  CR.t     <- Fq,
op  CR.zeror <- Zq.zero,
op  CR.oner  <- Zq.one,
op  CR.(+)   <- Zq.(+),
op  CR.([-]) <- Zq.([-]),
op  CR.( * ) <- Zq.( * ),
op  CR.invr  <- Zq.inv,
op  CR.ofint <- ZqRing.ofint,
pred  CR.unit  <- Zq.unit
proof CR.*.

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


op zroot = inFq 17.

op br = BitEncoding.BitReverse.bsrev 7.

op ntt(p : poly) = Array256.init (fun i => 
  if i %% 2  = 0
  then let ii = i %/ 2 in BAdd.bigi predT (fun j => p.[2*j]   * ZqRing.exp zroot ((2 * br ii + 1) * j)) 0 128
  else let ii = i %/ 2 in BAdd.bigi predT (fun j => p.[2*j+1] * ZqRing.exp zroot ((2 * br ii + 1) * j)) 0 128) axiomatized by nttE.


op invntt(p : poly) = Array256.init (fun i => 
  if i %% 2  = 0 
  then let ii = i %/ 2 in BAdd.bigi predT (fun j => inv (inFq 128) * p.[2*j]   * ZqRing.exp zroot (-((2 * br j + 1) * ii))) 0 128
  else let ii = i %/ 2 in BAdd.bigi predT (fun j => inv (inFq 128) * p.[2*j+1] * ZqRing.exp zroot (-((2 * br j + 1) * ii))) 0 128) axiomatized by invnttE.

  (* This is multiplication of two degree-1 polynomials in Fq
  modulo X^2 - zroot.
  
  (a1 + a2 X) * (b1 + b2 X) mod (X^2 - zroot) = 

  (a2b2zroot + a1b1) + (a1b2 + a2b1)X 


  And its extension to two products, one over   
  (X^2 - zroot) and another one over (X^2 + zroot)
  *)
op cmplx_mul (a :Fq * Fq, b : Fq * Fq, zzeta : Fq) : Fq * Fq =
(a.`2 * b.`2 * zzeta + a.`1*b.`1, a.`1 * b.`2 + a.`2 * b.`1).

  (* The base multiplication in the NTT domain is defined in the
  spec as follows. *)

op basemul(a b : poly) :  poly = Array256.init (fun i =>
  if i %% 2  = 0 
  then let ii = i %/ 2     in 
  (cmplx_mul (a.[2*ii],a.[2*ii+1]) (b.[2*ii],b.[2*ii+1]) (ZqRing.exp zroot ((2 * br ii + 1)))).`1
  else let ii = i %/ 2 in 
  (cmplx_mul (a.[2*ii],a.[2*ii+1]) (b.[2*ii],b.[2*ii+1]) (ZqRing.exp zroot ((2 * br ii + 1)))).`2).


    (* END: NTT *)

    (* We can now set-up the EC algebraic libraries *)

    (* Note that I have no way to pass the ring operations
    to this theory because it takes the representation
    to be that of the base ring of polynomials, which 
    I never work with. *)

(* XXX: Is this really needed in the spec? *)

(*
require import PolyReduce.
clone import PolyReduce as PolyR with
op n <- 256,
type BasePoly.coeff <- Fq,
op BasePoly.Coeff.(+) <- Zq.(+),
op BasePoly.Coeff.( *)(* <- Zq.( *)(*,
op BasePoly.Coeff.zeror <- Zq.zero,
op BasePoly.Coeff.oner <- Zq.one,
op BasePoly.Coeff.([-]) <- Zq.([-]),
op BasePoly.Coeff.invr <- Zq.inv,
pred BasePoly.Coeff.unit <- Zq.unit
rename "polyXnD1" as "AlgR"
rename "poly" as "basepoly"
proof BasePoly.Coeff.addrA by apply ZqRing.addrA
proof BasePoly.Coeff.addrC by apply ZqRing.addrC
proof BasePoly.Coeff.add0r by apply ZqRing.add0r 
proof BasePoly.Coeff.addNr by apply ZqRing.addNr 
proof BasePoly.Coeff.oner_neq0 by apply ZqRing.oner_neq0
proof BasePoly.Coeff.mulrA by apply ZqRing.mulrA
proof BasePoly.Coeff.mulrC by apply ZqRing.mulrC 
proof BasePoly.Coeff.mul1r by apply ZqRing.mul1r 
proof BasePoly.Coeff.mulrDl by apply ZqRing.mulrDl 
proof BasePoly.Coeff.mulVr by apply ZqRing.mulVr
proof BasePoly.Coeff.unitP by apply ZqRing.unitP 
proof BasePoly.Coeff.unitout by apply ZqRing.unitout
proof gt0_n by auto. 

op poly2polyr(p : poly) : AlgR = pi (oget (BasePoly.to_basepoly 
    (fun i => if 0<=i<256 then p.[i] else Zq.zero))).
op polyr2poly(p : AlgR) : poly = Array256.init (fun i => p.[i]).
    *)


