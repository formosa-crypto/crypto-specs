require import Rq.

op kvec : int = 3. 

require Matrix.
clone import Matrix as PolyMat with
  op size <- kvec,
  theory ZR <- Rq
  rename "Vector" as "PolyVec"
  rename "vector" as "polyvec"
  rename "matrix" as "polymat".

  import PolyVec.


(* This should be added to Matrix *)
op "_.[_<-_]" (m : polymat) (ij : int * int) (c : poly) : polymat = 
offunm (fun i j => if (i,j) = ij then c else (tofunm m) i j).

op set (v : polyvec) (i : int) (c : poly) : polyvec = 
offunv (fun i' => if i = i' then c else (tofunv v) i').

op mapm(f : poly -> poly, m : polymat) = offunm (fun i j => f (tofunm m i j)).
op mapv(f : poly -> poly, v : polyvec) = offunv (fun i => f (tofunv v i)).
(***********)

op nttv v = mapv ntt v.
op nttm m = mapm ntt m.
op invnttv v = mapv invntt v.
op invnttm m = mapm invntt m.

op ntt_mmul(m : polymat, v : polyvec) : polyvec = 
offunv (fun (i : int) => (Big.BAdd.bigi predT (fun (j : int) => basemul m.[i, j] v.[j]) 0 kvec)).

op ntt_dotp(v1 v2 : polyvec) : poly = 
Big.BAdd.bigi predT (fun (i : int) => basemul v1.[i] v2.[i]) 0 kvec.

