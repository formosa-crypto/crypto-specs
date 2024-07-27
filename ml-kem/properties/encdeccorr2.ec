(* -------------------------------------------------------------------- *)
(* ----- *) require import AllCore IntDiv List Ring StdOrder.
from Jasmin require import JUtils JWord.

require import Array32 Array768 Array960.
require import BitEncoding.
(* - *) import BitChunking BS2Int IntOrder.

require import JWordList Serialization Correctness.

(* -------------------------------------------------------------------- *)
abstract theory ArrayExtra.
  op size : int.

  clone import JArray.PolyArray as A with op size <- size.

  lemma fill0 ['a] (f : int -> 'a) (w : 'a A.t) (i : int) :
    fill f i 0 w = w.
  proof. by apply/tP=> j rgj; rewrite fillE initE rgj /= iffalse //#. qed.

  lemma fillS ['a] (f : int -> 'a) (w : 'a A.t) (i l : int) :
    0 <= i => i+l <= size => 0 < l => fill f i l w = fill f (i+1) (l-1) w.[i <- f i].
  proof.
  move=> ge0_i le_iDl_sz gt0_l; apply/tP=> j rgj.
  by rewrite !fillE !initE rgj /= get_set_if /#.
  qed.
  
  lemma fill_get ['a] (f : int -> 'a) (w : 'a A.t) (i l m : int) :
    0 <= i => i+l <= size => 0 <= m < l => (fill f i l w).[i + m] = f (i + m).
  proof. by move=> ge0_i le_iDl_sz [ge0_m lt_ml]; rewrite fillE initE //#. qed.
end ArrayExtra.

(* -------------------------------------------------------------------- *)
abstract theory W8ArrayExtra.
  op size : int.

  clone import JArray.PolyArray as A with op size <- size.

  op bits (a : W8.t A.t) =
    flatten (map W8.w2bits (A.to_list a)).

  lemma get_bit (x0 : bool) (a : W8.t A.t) (i j : int) :
    0 <= i < size => 0 <= j < 8 => a.[i].[j] = nth x0 (bits a) (i*8+j).
  proof.
  move=> rgi rgj @/bits; rewrite (nth_flatten x0 8).
  - by apply/List.allP=> bs /mapP[w] [_ ->].
  rewrite divzMDl // modzMDl pdiv_small //= pmod_small //.
  rewrite (nth_map witness) ?size_to_list // get_to_list.
  by rewrite (nth_change_dfl false).
  qed.

  lemma get_bits (a : W8.t A.t) (i : int) :
    0 <= i < size => W8.w2bits a.[i] = take 8 (drop (8 * i) (bits a)).
  proof.
  move=> rgi @/bits; rewrite drop_flatten_ctt.
  - by move=> bs /mapP[w] [_ ->].
  rewrite -map_drop (take_flatten_ctt 8 1).
  - by move=> bs /mapP[w] [_ ->].
  rewrite -map_take (drop_take1_nth witness) ?size_to_list //=.
  by rewrite flatten_seq1.
  qed.

  lemma size_bits (a : W8.t A.t) : size (bits a) = size * 8.
  proof.
  rewrite (size_flatten_ctt 8); first by move=> bs /mapP[w] [_ ->].
  by rewrite size_map size_to_list [8*_]mulrC.
  qed.

  lemma inj_bits : injective bits.
  proof.
  move=> a1 a2 eq_bits; apply/tP => i rgi; apply/W8.wordP => j rgj.
  by rewrite !(get_bit false) // eq_bits.
  qed.

  lemma bits_init (f : int -> W8.t) : bits (A.init f) =
    flatten (mkseq (fun i => w2bits (f i)) size).
  proof.
  rewrite &(eq_from_nth false) -1:size_bits => [|i rgi].
  - rewrite size_bits (size_flatten_ctt 8).
    - by move=> bs /mapP[w] [_ ->].
    - by rewrite size_mkseq; smt(A.ge0_size).
  have dvdi8: 0 <= i %/ 8 < size by smt().
  have modi8: 0 <= i %% 8 < 8 by smt().
  rewrite {1}[i](divz_eq _ 8) -get_bit // initE.
  rewrite dvdi8 (nth_flatten _ 8) -1:nth_mkseq //.
  by apply/List.allP=> bs /mapP[/= j] [_ ->].
  qed.

  lemma bits_fill (f : int -> W8.t) (w : W8.t A.t) (i l : int) :
    0 <= i => 0 <= l => i+l <= size => bits (fill f i l w) =
         take (8 * i) (bits w)
      ++ flatten (mkseq (fun k => w2bits (f (i+k))) l)
      ++ drop (8 * (i+l)) (bits w).
  proof.
  move=> ge0_i ge0_l le_iDl_asz; rewrite fillE.
  pose s := flatten _; have szs: size s = 8 * l.
  - rewrite /s (size_flatten_ctt 8).
    - by move=> bs /mapP[?] [_ ->].
    - by rewrite size_mkseq /#.
  have sztk: size (take (8 * i) (bits w)) = 8 * i.
  - by rewrite size_take ~-1:/# size_bits /#.
  have skdp: size (drop (8 * (i + l)) (bits w)) = 8 * (size - (i + l)).
  - by rewrite size_drop ~-1:/# size_bits /#.
  rewrite &(eq_from_nth false) -1:size_bits => [|j rgj].
  - by rewrite size_bits !size_cat /#.
  rewrite {1}[j](divz_eq _ 8) -(get_bit false) ~-1:/#.
  rewrite initE iftrue 1:/# /= -catA !nth_cat sztk.
  rewrite lez_divRL // ltz_divLR // [j<8*i]ltzNge if_neg.
  rewrite szs ltr_subl_addr -mulrDr [l+i]addrC ![_*8]mulrC.
  rewrite -[j-_-_]addrA -opprD -mulrDr; case: (8*i <= j) => /=.
  - move=> ?; case: (j < 8*(i+l)) => ?.
    - rewrite &(eq_sym) (nth_flatten false 8).
      - by apply/List.allP=> bs /= /mapP[/= ?] [_ ->].
      - by rewrite nth_mkseq; smt().
    - by rewrite nth_drop ~-1:/# (get_bit false) /#.
  - by move=> ?; rewrite nth_take ~-1:/# (get_bit false) /#.
  qed.
end W8ArrayExtra.

(* -------------------------------------------------------------------- *)
abbrev "_.[_]" ['a] (x : 'a list) (i : int) = nth witness x i.

(* -------------------------------------------------------------------- *)
clone import ArrayExtra as ArrayExtra768
  with op size <- 768, theory A <- Array768.

clone import ArrayExtra as ArrayExtra960
  with op size <- 960, theory A <- Array960.

(* -------------------------------------------------------------------- *)
clone import W8ArrayExtra as W8ArrayExtra32
  with op size <- 32, theory A <- Array32.

clone import W8ArrayExtra as W8ArrayExtra768
  with op size <- 768, theory A <- Array768.

clone import W8ArrayExtra as W8ArrayExtra960
  with op size <- 960, theory A <- Array960.

(* -------------------------------------------------------------------- *)
lemma bs2int_take (v : W8.t) (n : int) :
  0 <= n => bs2int (take n (w2bits v)) = W8.to_uint v %% 2^n.
proof. by move=> ge0_n; rewrite -bs2int_mod // -to_uintE. qed.

lemma bs2int_drop (v : W8.t) (n : int) :
  0 <= n => bs2int (drop n (w2bits v)) = W8.to_uint v %/ 2^n.
proof. by move=> ge0_n; rewrite -bs2int_div // -to_uintE. qed.

(* -------------------------------------------------------------------- *)
theory EncDecOp.
  op benc, asize, csize : int.

  axiom gt0_benc : 0 < benc.

  clone import JArray.PolyArray as A with op size <- asize.
  clone import JArray.PolyArray as C with op size <- csize.

  clone ArrayExtra   as AE with op size <- asize, theory A <- A.
  clone W8ArrayExtra as CE with op size <- csize, theory A <- C.

  axiom sizes_compatible : 8 * csize = benc * asize.

  type ivec = int  A.t.
  type cvec = W8.t C.t.

  op encodeXX (u : ivec) : cvec =
    let bits = chunk 8 (flatten (map (fun i => int2bs benc i) (to_list u))) in
    C.init (fun i => W8.bits2w bits.[i]).

  op decodeXX (u : cvec) : ivec =
    let bits = chunk benc (CE.bits u) in A.init (fun i => bs2int bits.[i]).

  lemma encodeXXP (u : ivec) :
    (forall k, 0 <= k < asize => 0 <= u.[k] < 2^benc) =>
      forall i, 0 <= i < asize =>
        bs2int (take benc (drop (benc*i) (CE.bits (encodeXX u)))) = u.[i].
  proof.
  have ? := gt0_benc; have ? := sizes_compatible. (* FIXME: smt hint *)
  move=> rgu i rgi @/encodeXX /=; rewrite CE.bits_init /=.
  pose F k := (chunk 8 (flatten (map (int2bs benc) (to_list u)))).[k].
  rewrite -(eq_in_mkseq F) /F /= => {F} [k rgk|] /=-; first rewrite bits2wK //.
  - apply: size_nth_chunk => //; rewrite (size_flatten_ctt benc).
    - by move=> x /mapP[m] [_ ->]; rewrite size_int2bs /#.
    - by rewrite size_map size_to_list /#.
  pose s := chunk 8 _; have: size s = csize.
  - rewrite /s size_chunk // (size_flatten_ctt benc).
    - by move=> t /mapP[m] [_ ->]; rewrite size_int2bs /#.
    - by rewrite size_map size_to_list /#.
  move=> <-; rewrite (mkseq_nth witness s) chunkK //.
  - rewrite (size_flatten_ctt benc) ?size_map ?size_iota //. 
    - by move=> t /mapP[m] [_ ->]; rewrite size_int2bs /#.
    - smt().
  rewrite drop_flatten_ctt.
  - by move=> t /mapP[m] [_ ->]; rewrite size_int2bs /#.
  rewrite (take_flatten_ctt benc 1).
  - by move=> t /mem_drop /mapP[m] [_ ->]; rewrite size_int2bs /#.
  rewrite (drop_take1_nth witness) ?size_map ?size_iota ~-1://# /=.
  by rewrite (nth_map witness) ?size_to_list //= flatten1 int2bsK //#.
  qed.

  lemma encodeXX_uniq (u : ivec) (bs : cvec) :
       (forall k, 0 <= k < asize => 0 <= u.[k] < 2^benc)
    => (forall i, 0 <= i < asize =>
         bs2int (take benc (drop (benc*i) (CE.bits bs))) = u.[i])
    => bs = encodeXX u.
  proof.
  have ? := gt0_benc; have ? := sizes_compatible.
  have ?: 0 < benc by smt().
  have ?: benc %| csize * 8 by rewrite [_*8]mulrC sizes_compatible /#.
  move=> rgu bsP; rewrite &(CE.inj_bits) &(inj_chunk benc) ?CE.size_bits //.
  rewrite &(eq_from_nth []) !size_chunk ?CE.size_bits //=.
  move=> i rgi; have ?: 0 <= i < asize by smt().
  rewrite !JWordList.nth_chunk ?CE.size_bits ~-1://#.
  apply: inj_bs2int_eqsize.
  - by rewrite !size_takel // ?size_drop ?CE.size_bits /#.
  - by rewrite bsP 1:/# encodeXXP //#.
  qed.

  lemma encodeXXK (u : ivec):
       (forall k, 0 <= k < asize => 0 <= u.[k] < 2^benc)
    => decodeXX (encodeXX u) = u.
  proof.
  have ? := gt0_benc; have ? := sizes_compatible.
  move=> rgu; have rP := encodeXXP _ rgu.
  apply/A.tP => i rgi; rewrite -rP // /decodeXX /=.
  rewrite initE rgi /= (nth_change_dfl [<:bool>]).
  - by rewrite size_chunk // ?CE.size_bits //#.
  - by rewrite JWordList.nth_chunk ?CE.size_bits //#.
  qed.

  lemma range_decodeXX (u : cvec) :
    forall i, 0 <= i < asize => 0 <= (decodeXX u).[i] < 2^benc.
  proof.
  have ? := gt0_benc; have ? := sizes_compatible.
  move=> i rgi @/decodeXX /=; rewrite initE iftrue //=.
  rewrite bs2int_ge0 /= &(ltr_le_trans  _ _ _ (bs2int_le2Xs _)) &(lerr_eq).
  by congr; rewrite &(size_nth_chunk) 1:/#  CE.size_bits /#.
  qed.

  lemma decodeXXK (u : cvec) : encodeXX (decodeXX u) = u.
  proof.
  have ? := gt0_benc; have ? := sizes_compatible.
  apply/eq_sym/encodeXX_uniq; first by apply/range_decodeXX.
  move=> i rgi @/decodeXX /=; rewrite initE rgi /=.
  rewrite -nth_chunk ?CE.size_bits ~-1://#.
  rewrite (nth_change_dfl witness) // size_chunk //.
  by rewrite CE.size_bits /#.
  qed.
end EncDecOp.

(* -------------------------------------------------------------------- *)
clone import EncDecOp as EncDecOp10
  with
    op     benc  <- 10,
    op     asize <- 768,
    op     csize <- 960,
    theory A     <- Array768,
    theory C     <- Array960,
    theory AE    <- ArrayExtra768,
    theory CE    <- W8ArrayExtra960,
    type   ivec  <- ipolyvec

    proof * by done

    rename [op, lemma] "XX" as "10".

(* -------------------------------------------------------------------- *)
lemma proc_decode10P (u0 : bool list) :
  hoare[EncDec.decode10_vec : bits u = u0 ==>
    forall k, 0 <= k < 768 => res.[k] = bs2int (take 10 (drop (10 * k) u0))
  ].
proof.
proc; sp; while (
     0 <= i < 768+4
  /\ 4 %| i
  /\ j = 5 * (i %/ 4)
  /\ bits u = u0
  /\ forall k, 0 <= k < i => c.[k] = bs2int (take 10 (drop (10 * k) u0))
); last by auto=> /> /#.
auto=> /> &hr ge0_i _ dvd4_i ih lt768_i; do! split; ~-1:smt().
pose j := 5 * (i{hr} %/ 4).
move=> k ge0_k ltk; case: (k < i{hr}); first by rewrite !get_set_if /#.
move/StdOrder.IntOrder.lerNgt => le_ik.
have [d [rgd ->>]]: exists d, 0 <= d < 4 /\ k = i{hr} + d by smt().
pose v0 := to_uint u{hr}.[j] + to_uint u{hr}.[j + 1] %% 4 * 256.
pose v1 := to_uint u{hr}.[j + 1] %/ 4 + to_uint u{hr}.[j + 2] %% 16 * 64.
pose v2 := to_uint u{hr}.[j + 2] %/ 16 + to_uint u{hr}.[j + 3] %% 64 * 16.
pose v3 := to_uint u{hr}.[j + 3] %/ 64 + to_uint u{hr}.[j + 4] * 4.
have := (eq_refl (fill (fun m => [v0; v1; v2; v3].[m - i{hr}]) i{hr} 4 c{hr})).
rewrite 4?{1}fillS ~-1://# /= fill0; do! rewrite addrAC /= => ->.
rewrite fill_get ~-1://# /= addrAC /=; have: (d \in iota_ 0 4).
- by rewrite 4?JUtils.iotaS_minus //= iota0 //#.
rewrite 4?JUtils.iotaS_minus //= iota0 //= => [#|] ->> /=.
- rewrite /v0 !to_uintE !get_bits ~-1://#.
  rewrite (bs2int_mod _ 2) // take_take /= [_*256]mulrC (bs2intD _ _ 8).
  - by rewrite size_take // size_drop 1:/# size_bits /#.
  by rewrite (takeD _ 8 2) ~-1:// drop_drop //#.
- rewrite /v1 !to_uintE !get_bits ~-1://#.
  rewrite (bs2int_mod _ 4) // take_take (bs2int_div 2) ~-1:// /=.
  rewrite [_*64]mulrC (bs2intD _ _ 6).
  - by smt(size_drop size_take size_bits).
  rewrite drop_take //= drop_drop ~-1://# (takeD _ 6 4) ~-1://.
  by rewrite drop_drop //#.
- rewrite /v2 !to_uintE !get_bits ~-1://#.
  rewrite (bs2int_div 4) ~-1:// (bs2int_mod _ 6) ~-1://.
  rewrite drop_take //= drop_drop ~-1://# take_take /=.
  rewrite [_*16]mulrC (bs2intD _ _ 4).
  - by smt(size_drop size_take size_bits).
  by rewrite (takeD _ 4 6) ~-1:// drop_drop //#.
- rewrite /v3 !to_uintE !get_bits ~-1://#.
  rewrite (bs2int_div 6) ~-1://# [_*4]mulrC (bs2intD _ _ 2).
  - by smt(size_drop size_take size_bits).
  rewrite drop_take //= drop_drop ~-1://# (takeD _ 2 8) ~-1://.
  by rewrite drop_drop //#.
qed.

hint simplify flatten_nil, flatten_cons.

lemma proc_encode10P (u0 : ipolyvec) :
  (forall k, 0 <= k < 768 => 0 <= u0.[k] < 1024) =>

  hoare[EncDec.encode10_vec : u = u0 ==>
    forall i, 0 <= i < 768 =>
      bs2int (take 10 (drop (10*i) (bits res))) = u0.[i]
  ].
proof.
move=> rgu; proc; sp; while (
     0 <= i < 768+4
  /\ 4 %| i
  /\ j = 5 * (i %/ 4)
  /\ u = u0
  /\ forall k, 0 <= k < i =>
       bs2int (take 10 (drop (10*k) (bits c))) = u0.[k]
); last by auto=> /> /#.
auto=> /> &hr ge0_i _ dvd4_i ih lt768_i; do! split; ~-1:smt().
move=> k ge0_k ltk; case/dvdzP: dvd4_i => i4 ->>; rewrite mulzK ~-1://.
pose v0 := W8.of_int u0.[i4 * 4].
pose v1 := W8.of_int (u0.[i4 * 4] %/ 256 + u0.[i4 * 4 + 1] * 4).
pose v2 := W8.of_int (u0.[i4 * 4 + 1] %/ 64 + u0.[i4 * 4 + 2] * 16).
pose v3 := W8.of_int (u0.[i4 * 4 + 2] %/ 16 + u0.[i4 * 4 + 3] * 64).
pose v4 := W8.of_int (u0.[i4 * 4 + 3] %/ 4).
have := (eq_refl (fill (fun m => [v0; v1; v2; v3; v4].[m - 5 * i4]) (5 * i4) 5 c{hr})).
rewrite 5?{1}fillS ~-1://# /= fill0; do! rewrite addrAC /= => ->.
pose F m := [v0; v1; v2; v3; v4].[m - 5 * i4]; rewrite bits_fill ~-1://#.
case: (k < i4 * 4) => [lt_k_4i4|gtk].
- rewrite -catA; move: (flatten _ ++ _) => s.
  rewrite drop_catl 1:#smt:(size_cat size_take size_bits size_ge0).
  rewrite take_catl 1:#smt:(size_take size_drop size_bits).
  by rewrite drop_take ~-1:/# take_take iftrue ~-1://# &(ih).
pose s := flatten _; have sz_s: size s = 40.
- rewrite size_flatten map_mkseq /(\o) -(eq_mkseq (fun _ => 8)) //=.
  rewrite StdBigop.Bigint.sumzE StdBigop.Bigint.BIA.big_mapT /(\o) /=.
  by rewrite -/(range 0 5) StdBigop.Bigint.bigi_constz //#.
pose vs := [v0; v1; v2; v3; v4].
have sE: s = flatten (map W8.w2bits vs).
- move=> @/s; congr; rewrite -map_mkseq.
  rewrite -(eq_in_mkseq (fun i => vs.[i])) 1:/# /=.
  by rewrite 5?mkseqSr_minus /(\o) //= mkseq0.
have dm: forall m, 0 <= m => drop (8 * m) s = flatten (map W8.w2bits (drop m vs)).
- move=> m rgm; rewrite sE drop_flatten_ctt -1:map_drop //.
  by move=> x /mapP[w] [_ ->]; rewrite size_w2bits.
have tm: forall m, 0 <= m => take (8 * m) s = flatten (map W8.w2bits (take m vs)).
- move=> m rgm; rewrite sE take_flatten_ctt -1:map_take //.
  by move=> x /mapP[w] [_ ->]; rewrite size_w2bits.
rewrite -catA drop_catr 1:#smt:(size_cat size_take size_bits size_ge0).
rewrite size_take 1://# size_bits iftrue 1://# drop_catl 1://#.
rewrite take_catl; first by rewrite size_drop /#.
have [d [rgd ->>]]: exists d, (0 <= d < 4) /\ k = i4 * 4 + d by smt().
rewrite (_ : (10 * _ - _)%Int = 10 * d) 1:#ring.
have: d \in iota_ 0 4 by rewrite 4?JUtils.iotaS_minus //= iota0 //#.
rewrite 4?JUtils.iotaS_minus ~-1://= iota0 ~-1:// /= => [#|] ->> /=.
- rewrite drop0 (takeD _ 8 2) ~-1:// bs2int_cat size_take -1:iftrue ~-1://#.
  rewrite (tm 1) //= (dm 1) //= take_cons drop_cons /= cats0.
  rewrite take_catl ?size_w2bits // bs2int_take 1:// /v1 of_uintK /=.
  rewrite (modz_dvd_pow 2 8 _ 2) //= modzMDr pmod_small 1:/#.
  by rewrite -to_uintE /= addrC of_uintK /= [256*_]mulrC -divz_eq.
- rewrite -(drop_drop _ 2 8) // (dm 1) // drop_cons /=.
  rewrite drop_catl ?size_w2bits // take_catr size_drop //=.
  rewrite (_ : 10 - _ = 4) // take_catl ?size_w2bits //.
  rewrite bs2int_cat bs2int_drop 1:// /v1 /= (modz_pow2_div 8 2) //=.
  rewrite divzMDr ~-1:// -divzMr ~-1://= pdiv_small ~-1://# /=.
  rewrite size_drop 1:// size_w2bits (_ : max _ _ = 6) 1:// /=.
  rewrite bs2int_take 1:// /v2 of_uintK /= (modz_dvd_pow 4 8 _ 2) //=.
  by rewrite modzMDr addrC pmod_small 1:/# [64*_]mulrC -divz_eq.
- rewrite -(drop_drop _ 4 16) // (dm 2) // 2!drop_cons /=.
  rewrite drop_catl ?size_w2bits // take_catr.
  - by rewrite size_drop // size_w2bits.
  rewrite size_drop // size_w2bits (_ : 10 - _ = 6) //.
  rewrite take_catl ?size_wbits // bs2int_cat bs2int_drop 1://.
  rewrite size_drop 1:// size_w2bits (_ : max _ _ = 4) 1:// /=.
  rewrite bs2int_take 1:// /= /v2 of_uintK /= (modz_pow2_div 8 4) 1:// /=.
  rewrite divzMDr 1:// -divzMr ~-1:// /= pdiv_small 1:/# /=.
  rewrite of_uintK /= (modz_dvd_pow 6 8 _ 2) 1:// /=.
  by rewrite modzMDr addrC pmod_small 1:/# [16*_]mulrC -divz_eq.
- rewrite -(drop_drop _ 6 24) // (dm 3) // 3!drop_cons /=.
  rewrite drop_catl ?size_w2bits // take_catr.
  - by rewrite size_drop // size_w2bits.
  rewrite size_drop // size_w2bits (_ : 10 - _ = 8) //.
  rewrite cats0 take_oversize ?size_w2bits //.
  rewrite bs2int_cat ?size_drop // size_w2bits.
  rewrite (_ : max _ _ = 2) //= bs2int_drop 1:// /v3 /=.
  rewrite (modz_pow2_div 8 6) //= divzMDr //.
  rewrite -divzMr //= pdiv_small 1:/# /= /v4 -to_uintE /=.
  by rewrite addrC pmod_small 1:/# [4*_]mulrC -divz_eq.
qed.

lemma proc_encode10E (u0 : ipolyvec) :
  (forall k, 0 <= k < 768 => 0 <= u0.[k] < 1024) =>

  hoare[EncDec.encode10_vec: u = u0 ==> res = encode10 u0].
proof.
move=> rgu; proc*; call(proc_encode10P u0 rgu); auto=> />.
by move=> r rP; apply: encode10_uniq.
qed.

lemma proc_decode10E (u0 : W8.t Array960.t) :
  hoare[EncDec.decode10_vec: u = u0 ==> res = decode10 u0].
proof.
proc*; call(proc_decode10P (bits u0)); auto=> />.
move=> r rP; apply/Array768.tP => i rgi.
rewrite rP // /decode10 /= initE iftrue //=.
rewrite (nth_change_dfl [<:bool>]).
- by rewrite size_chunk // ?size_bits.
- by rewrite JWordList.nth_chunk ?size_bits ~-1://#.
qed.

module EncDecExp = {
  proc exp10(u : ipolyvec) = {
    var ub;

    ub <@ EncDec.encode10_vec(u);
    u  <@ EncDec.decode10_vec(ub);

    return u;
  }
}.

lemma exp10P (u0 : ipolyvec) :
  (forall k, 0 <= k < 768 => 0 <= u0.[k] < 1024) =>

  hoare[EncDecExp.exp10: u = u0 ==> res = u0].
proof.
move=> rgu; proc;
  call (proc_decode10E (encode10 u0));
  call (proc_encode10P u0);
  auto=> />.
by move=> r rP; split; [apply/encode10_uniq | rewrite encode10K].
qed.
