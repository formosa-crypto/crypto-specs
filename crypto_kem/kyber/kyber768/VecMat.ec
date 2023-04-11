require import Rq.

op kvec : int = 3. 

require Matrix.
clone import Matrix as KMatrix with
op size <- kvec,
type ZR.t = poly,
op ZR.zeror <- Rq.zero,
op ZR.oner <- Rq.one,
op ZR.(+) <- Rq.(&+),
op ZR.([-]) <- Rq.(&-),
op ZR.( * ) <- Rq.(&*).

instance ring with R
op rzero = Rq.zero
op rone  = Rq.one
op add   = Rq.(&+)
op opp   = Rq.(&-)
op mul   = Rq.(&*)
op expr  = ZR.exp
op ofint = ZR.ofint

proof oner_neq0 by apply ZR.oner_neq0
proof addrA     by apply ZR.addrA
proof addrC     by apply ZR.addrC
proof addr0     by apply ZR.addr0
proof addrN     by apply ZR.addrN
proof mulr1     by apply ZR.mulr1
proof mulrA     by apply ZR.mulrA
proof mulrC     by apply ZR.mulrC
proof mulrDl    by apply ZR.mulrDl
proof expr0     by apply ZR.expr0
proof ofint0    by apply ZR.ofint0
proof ofint1    by apply ZR.ofint1
proof exprS     by apply ZR.exprS
proof ofintS    by apply ZR.ofintS
proof ofintN    by apply ZR.ofintN.


import Vector.

(* This should be added to matrix *)
op "_.[_<-_]" (m : matrix) (ij : int * int) (c : poly) : matrix = 
offunm (fun i j => if (i,j) = ij then c else (tofunm m) i j).

op set (v : vector) (i : int) (c : poly) : vector = 
offunv (fun i' => if i = i' then c else (tofunv v) i').

op mapm(f : poly -> poly, m : matrix) = offunm (fun i j => f (tofunm m i j)).
op mapv(f : poly -> poly, v : vector) = offunv (fun i => f (tofunv v i)).
(***********)

op nttv v = mapv ntt v.
op nttm m = mapm ntt m.
op invnttv v = mapv invntt v.
op invnttm m = mapm invntt m.

op ntt_mmul(m : matrix, v : vector) : vector = 
  offunv (fun (i : int) => (Big.BAdd.bigi predT (fun (j : int) => basemul m.[i, j] v.[j]) 0 kvec)).

op ntt_dotp(v1 v2 : vector) : poly = 
  Big.BAdd.bigi predT (fun (i : int) => basemul v1.[i] v2.[i]) 0 kvec.

