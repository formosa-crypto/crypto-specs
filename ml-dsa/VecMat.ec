require import AllCore List.
require import Parameters GFq Rq.
import Zq.

require import Array256.

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
op (-) : polykvec -> polykvec -> polykvec.
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

op polykvec_ntt_smul(p : poly, v : polykvec) : polykvec = 
   PolyKVec.zerov.[0 <- basemul v.[0] p]
                 .[1 <- basemul v.[1] p]
                 .[2 <- basemul v.[2] p]
                 .[3 <- basemul v.[3] p]
                 .[4 <- basemul v.[4] p]
                 .[5 <- basemul v.[5] p].

op polylvec_ntt_smul(p : poly, v : polylvec) : polylvec = 
   PolyLVec.zerov.[0 <- basemul v.[0] p]
                 .[1 <- basemul v.[1] p]
                 .[2 <- basemul v.[2] p]
                 .[3 <- basemul v.[3] p]
                 .[4 <- basemul v.[4] p].

op smul(v : polykvec, c : coeff) : polykvec = 
   mapv (fun (vi : poly) => map (fun ci => ci*c) vi) v.

op ntt_mmul(m : polymat, v : polylvec) : polykvec = 
   PolyKVec.zerov.[0 <- basemul m.[0, 0] v.[0] &+ basemul m.[0, 1] v.[1] &+ basemul m.[0, 2] v.[2] &+ basemul m.[0, 3] v.[3] &+ basemul m.[0, 4] v.[4]]
        .[1 <- basemul m.[1, 0] v.[0] &+ basemul m.[1, 1] v.[1] &+ basemul m.[1, 2] v.[2] &+ basemul m.[1, 3] v.[3] &+ basemul m.[1, 4] v.[4]]
        .[2 <- basemul m.[2, 0] v.[0] &+ basemul m.[2, 1] v.[1] &+ basemul m.[2, 2] v.[2] &+ basemul m.[2, 3] v.[3] &+ basemul m.[2, 4] v.[4]]
        .[3 <- basemul m.[3, 0] v.[0] &+ basemul m.[3, 1] v.[1] &+ basemul m.[3, 2] v.[2] &+ basemul m.[3, 3] v.[3] &+ basemul m.[3, 4] v.[4]]
        .[4 <- basemul m.[4, 0] v.[0] &+ basemul m.[4, 1] v.[1] &+ basemul m.[4, 2] v.[2] &+ basemul m.[4, 3] v.[3] &+ basemul m.[4, 4] v.[4]]
        .[5 <- basemul m.[5, 0] v.[0] &+ basemul m.[5, 1] v.[1] &+ basemul m.[5, 2] v.[2] &+ basemul m.[5, 3] v.[3] &+ basemul m.[5, 4] v.[4]].

(*
op ntt_dotp(v1 v2 : polyvec) : poly = 
   basemul v1.[0] v2.[0] &+ basemul v1.[1] v2.[1] &+ basemul v1.[2] v2.[2].
*)

op polykvec_Power2Round(t : polykvec) : polykvec * polykvec =
   (PolyKVec.zerov.[0 <- (poly_Power2Round t.[0]).`1]
                  .[1 <- (poly_Power2Round t.[1]).`1]
                  .[2 <- (poly_Power2Round t.[2]).`1]
                  .[3 <- (poly_Power2Round t.[3]).`1]
                  .[4 <- (poly_Power2Round t.[4]).`1]
                  .[5 <- (poly_Power2Round t.[5]).`1],
    PolyKVec.zerov.[0 <- (poly_Power2Round t.[0]).`2]
                  .[1 <- (poly_Power2Round t.[1]).`2]
                  .[2 <- (poly_Power2Round t.[2]).`2]
                  .[3 <- (poly_Power2Round t.[3]).`2]
                  .[4 <- (poly_Power2Round t.[4]).`2]
                  .[5 <- (poly_Power2Round t.[5]).`2]).


op polykvec_UseHint(h : polykvec, r : polykvec) : polykvec = 
   PolyKVec.zerov.[0 <- (poly_UseHint h.[0] r.[0])]
                 .[1 <- (poly_UseHint h.[1] r.[1])]
                 .[2 <- (poly_UseHint h.[2] r.[2])]
                 .[3 <- (poly_UseHint h.[3] r.[3])]
                 .[4 <- (poly_UseHint h.[4] r.[4])]
                 .[5 <- (poly_UseHint h.[5] r.[5])].

op polykvec_MakeHint(v1 : polykvec, v2 : polykvec) : polykvec = 
   PolyKVec.zerov.[0 <- (poly_MakeHint v1.[0] v2.[0])]
                 .[1 <- (poly_MakeHint v1.[1] v2.[1])]
                 .[2 <- (poly_MakeHint v1.[2] v2.[2])]
                 .[3 <- (poly_MakeHint v1.[3] v2.[3])]
                 .[4 <- (poly_MakeHint v1.[4] v2.[4])]
                 .[5 <- (poly_MakeHint v1.[5] v2.[5])].
   
op polylvec_infnorm(v : polylvec, bound : int) : bool = 
  all (fun ii => Array256.all (fun c => absZq c < bound) v.[ii]) (iota_ 0 5).

op polykvec_infnorm(v : polykvec, bound : int) : bool = 
  all (fun ii => Array256.all (fun c => absZq c < bound) v.[ii]) (iota_ 0 6).

op polykvec_hammw(v : polykvec, bound : int) : bool = 
  all (fun ii => count (fun c => c <> Zq.zero) (to_list (v.[ii])) <= bound) (iota_ 0 5).

op polylvec_mods(v : polylvec, md : int) : polylvec = 
  mapv (fun (p : poly) => map (fun c => incoeff (smod (asint c) md)) p) v.

op polykvec_HighBits(v : polykvec) : polykvec = 
  mapv (fun (p : poly) => map (fun c => incoeff (HighBits c)) p) v.


op polykvec_LowBits(v : polykvec) : polykvec = 
  mapv (fun (p : poly) => map (fun c => incoeff (LowBits c)) p) v.

