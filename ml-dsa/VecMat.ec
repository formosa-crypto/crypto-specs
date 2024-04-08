require import Rq.

(* We have k x l matrices *)
op kvec : int = 6. 
op lvec : int = 5.

theory PolyLVec.
type polylvec.
op "_.[_]" (v : polylvec) (i : int) : poly.
op "_.[_<-_]" (v : polylvec) (i : int) (c : poly) : polylvec.
op mapv(f : poly -> poly, v : polylvec) : polylvec.
op nttv v = mapv ntt v.
op invnttv v = mapv invntt v.
op zerov : polylvec.
op (+) : polylvec -> polylvec -> polylvec.
end PolyLVec.

theory PolyKVec.
type polykvec.
op "_.[_]" (v : polykvec) (i : int) : poly.
op "_.[_<-_]" (v : polykvec) (i : int) (c : poly) : polykvec.
op mapv(f : poly -> poly, v : polykvec) : polykvec.
op nttv v = mapv ntt v.
op invnttv v = mapv invntt v.
op zerov : polykvec.
op (+) : polykvec -> polykvec -> polykvec.
end PolyKVec.

theory PolyMat.
type polymat.
op "_.[_]" (m : polymat) (ij : int * int) : poly.
op "_.[_<-_]" (m : polymat) (ij : int * int) (c : poly) : polymat.
op mapm(f : poly -> poly, m : polymat) : polymat.
op nttm m = mapm ntt m.
op invnttm m = mapm invntt m.
op zerom : polymat. 
end PolyMat.

import PolyLVec PolyKVec PolyMat.

(*
op ntt_mmul(m : polymat, v : polyvec) : polyvec = 
   zerov.[0 <- basemul m.[0, 0] v.[0] &+ basemul m.[0, 1] v.[1] &+ basemul m.[0, 2] v.[2]]
        .[1 <- basemul m.[1, 0] v.[0] &+ basemul m.[1, 1] v.[1] &+ basemul m.[1, 2] v.[2]]
        .[2 <- basemul m.[2, 0] v.[0] &+ basemul m.[2, 1] v.[1] &+ basemul m.[2, 2] v.[2]].

op ntt_dotp(v1 v2 : polyvec) : poly = 
   basemul v1.[0] v2.[0] &+ basemul v1.[1] v2.[1] &+ basemul v1.[2] v2.[2].
*)
