require import AllCore List IntDiv QFABV.
from Jasmin require import JModel_x86.
require import Array4 Array5 Array6 Array7 Array8 Array9 Array24 Array25 Array32.
require import Array48 Array50 Array256 Array768 Array960.

require import WArray32 WArray512 WArray960 WArray1536.

import BitEncoding BS2Int BitChunking.

require import JWord_extra.


(* TO BE MOVED! *)

(*[size_flatten] (for uniform inner lists) *)
lemma size_flatten' ['a] sz (ss: 'a list list):
 (forall x, x\in ss => size x = sz) =>
 size (flatten ss) = sz*size ss.
proof.
move=> H; rewrite size_flatten.
rewrite StdBigop.Bigint.sumzE.
rewrite StdBigop.Bigint.BIA.big_map.
rewrite -(StdBigop.Bigint.BIA.eq_big_seq (fun _ => sz)) /=.
 by move=> x Hx; rewrite /(\o) /= H.
by rewrite StdBigop.Bigint.big_constz count_predT.
qed.


(* END MOVED *)



(* ----------- BEGIN BOOL BINDINGS ---------- *)
op bool2bits (b : bool) : bool list = [b].
op bits2bool (b: bool list) : bool = List.nth false b 0.

op i2b (i : int) = (i %% 2 <> 0).
op b2si (b: bool) = 0.

bind bitstring bool2bits bits2bool b2i b2si i2b bool 1.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by rewrite /bool2bits /bits2bool;smt(size_eq1).
realize ofintP by rewrite /bits2bool /int2bs => i; rewrite (nth_mkseq false) //. 
realize touintP by rewrite /bool2bits /= => bv; rewrite bs2int_cons bs2int_nil /=. 
realize tosintP by move => bv => //. 

bind op bool (/\) "and".
realize bvandP by move=> bv1 bv2; rewrite /bool2bits /#.

(* ----------- BEGIN W8 BINDINGS ---------- *)
bind bitstring W8.w2bits W8.bits2w W8.to_uint W8.to_sint W8.of_int W8.t 8.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by smt(W8.bits2wK). 
realize ofintP by move => *;rewrite /of_int int2bs_mod.
realize tosintP. move => bv /=;rewrite /to_sint /smod /BVA_Top_JWord_W8_t.msb.
have -> /=: nth false (w2bits bv) (8 - 1) = 2 ^ (8 - 1) <= to_uint bv; last by smt().
rewrite /to_uint. 
rewrite -{2}(cat_take_drop 7 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W8.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
by smt(bs2int_range mem_range W8.size_w2bits pow2_8).
qed.
realize touintP by smt().


(* -------------------------------------------------------------------- *)
bind op [W8.t & bool] W8."_.[_]" "get".

realize bvgetP by done.

(* -------------------------------------------------------------------- *)
bind op W8.t W8.andw "and".

realize bvandP.
proof.
move=> w1 w2; apply/(eq_from_nth witness).
- by rewrite size_map size_zip !size_w2bits.
rewrite size_w2bits => i rg_i; rewrite (nth_map witness) /=.
- by rewrite size_zip !size_w2bits.
rewrite nth_zip_cond /= size_zip !size_w2bits lez_minl 1:// /=.
rewrite 2?iftrue ~-1:/# /=.
rewrite [nth _ (w2bits w1) _](nth_change_dfl false) ?size_w2bits 1:/#.
rewrite [nth _ (w2bits w2) _](nth_change_dfl false) ?size_w2bits 1:/#.
by rewrite !get_w2bits w2bitsE nth_mkseq //#.
qed.

(* ----------- BEGIN W10 BINDINGS -----------*)

theory W10.
abbrev [-printing] size = 10.
clone include BitWordSH with op size <- size
rename "_XX" as "_10"
proof gt0_size by done,
size_le_256 by done.

end W10. export W10 W10.ALU W10.SHIFT.

bind bitstring W10.w2bits W10.bits2w W10.to_uint W10.to_sint W10.of_int W10.t 10.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by smt(W10.bits2wK). 
realize ofintP by move => *;rewrite /of_int int2bs_mod.
realize tosintP. move => bv /=;rewrite /to_sint /smod /BVA_Top_W10_t.msb.
have -> /=: nth false (w2bits bv) (10 - 1) = 2 ^ (10 - 1) <= to_uint bv; last by smt().
rewrite /to_uint. 
rewrite -{2}(cat_take_drop 9 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W10.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
have ? : 2^10 = 1024 by rewrite /=.
by smt(bs2int_range mem_range W10.size_w2bits).
qed.
realize touintP by smt().

(* ----------- BEGIN W12 BINDINGS -----------*)

theory W12.
  abbrev [-printing] size = 12.
  clone include BitWordSH with op size <- size
  rename "_XX" as "_12"
  proof gt0_size by done, size_le_256 by done.
end W12.

import W12.

(* -------------------------------------------------------------------- *)
bind bitstring W12.w2bits W12.bits2w W12.to_uint W12.to_sint W12.of_int W12.t 12.
realize size_tolist by auto.
realize tolistP     by auto.
realize oflistP     by smt(W12.bits2wK).
realize ofintP      by move=> *; rewrite /of_int int2bs_mod.
realize touintP     by smt().

realize tosintP.
proof.
move=> bv /= @/to_sint @/smod @/msb.
rewrite (_ : nth _ _ _ = 2 ^ (12 - 1) <= to_uint bv) -1:/#.
rewrite /to_uint -{2}(cat_take_drop 11 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W12.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
have ?: W12.modulus = 4096 by done.
by smt(bs2int_range mem_range W12.size_w2bits).
qed.

(* ----------- BEGIN W16 BINDINGS ---------- *)

bind bitstring W16.w2bits W16.bits2w W16.to_uint W16.to_sint W16.of_int W16.t 16.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by smt(W16.bits2wK). 
realize ofintP by move => *;rewrite /of_int int2bs_mod.
realize tosintP. move => bv /=;rewrite /to_sint /smod /BVA_Top_JWord_W16_t.msb.
have -> /=: nth false (w2bits bv) (16 - 1) = 2 ^ (16 - 1) <= to_uint bv; last by smt().
rewrite /to_uint. 
rewrite -{2}(cat_take_drop 15 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W16.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
by smt(bs2int_range mem_range W16.size_w2bits pow2_16).
qed.
realize touintP by smt().

bind op W16.t W16.( + ) "add".
realize bvaddP by exact W16.to_uintD.

bind op [bool & W16.t] W16.\ult "ult".
realize bvultP by move=> bv1 bv2; rewrite W16.ultE /#.

bind op [bool & W16.t] W16.\slt "slt".
realize bvsltP by move=> w1 w2; rewrite W16.sltE /#.

bind op W16.t W16.andw "and".
realize bvandP. 
rewrite /andw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W16.size_w2bits).
qed.


bind op W16.t W16.orw "or".
realize bvorP. 
rewrite /orw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W16.size_w2bits).
qed.

op W16_sub (a : W16.t, b: W16.t) : W16.t = 
  a - b.

bind op W16.t W16_sub "sub".
realize bvsubP by  rewrite /W16_sub => bv1 bv2; rewrite W16.to_uintD to_uintN /= /#.

op sll_16 (w1 w2 : W16.t) : W16.t =
  if (16 <= to_uint w2) then  W16.zero else  w1 `<<` (truncateu8 w2).

bind op [W16.t] sll_16 "shl".
realize bvshlP.
rewrite /sll_16 => bv1 bv2.
case : (16 <= to_uint bv2); last first.
+ rewrite /(`<<`) W16.to_uint_shl; 1: by smt(W8.to_uint_cmp).
  rewrite /truncateu8  => bv2bnd />.
  rewrite (pmod_small (to_uint bv2) _).
   smt(W16.to_uint_cmp).
  rewrite (pmod_small (to_uint bv2) _).
  smt(W16.to_uint_cmp).
  done.
move => *. 
have -> : to_uint bv2 = (to_uint bv2 - 16) + 16 by ring. 
by rewrite exprD_nneg 1,2:/# /= /#.
qed.


op sra_16 (w1 w2 : W16.t) : W16.t =
W16.sar w1 (to_uint w2).
(*
if (16 <= to_uint w2) then  W16.zero else w1 `|>>` (truncateu8 w2).
*)

bind op [W16.t] sra_16 "ashr".
realize bvashrP.
move=> bv1 bv2; rewrite W16_sar_div; smt(W16.to_uint_cmp).
qed.

op srl_16 (w1 w2 : W16.t) : W16.t =
  if 16 <= (to_uint w2) then W16.zero else
  w1 `>>` (truncateu8 w2).

bind op [W16.t] srl_16 "shr".
realize bvshrP.
rewrite /srl_16 => bv1 bv2.
case : (16 <= to_uint bv2); last first.
+ rewrite /(`>>`) W16.to_uint_shr; 1: by smt(W8.to_uint_cmp).
  rewrite /truncateu8  => bv2bnd />.
  rewrite (pmod_small (to_uint bv2) _); smt(W16.to_uint_cmp).
move => *. 
have -> : to_uint bv2 = (to_uint bv2 - 16) + 16 by ring. 
rewrite exprD_nneg 1,2:/# /=. 
smt(StdOrder.IntOrder.expr_gt0 W16.to_uint_cmp pow2_16).
qed.


bind op [W16.t & W8.t] W2u8.truncateu8 "truncate".
realize bvtruncateP.
move => mv; rewrite /truncateu8 /W16.w2bits take_mkseq 1:// /= /w2bits.
apply (eq_from_nth witness);1: by smt(size_mkseq).
move => i; rewrite size_mkseq /= /max /= => ib.
rewrite !nth_mkseq 1..2:// /of_int /to_uint /= get_bits2w 1:// 
        nth_mkseq 1:// /= get_to_uint 1:// /= /to_uint /=.
have -> /=: (0 <= i && i < 16) by smt().
pose a := bs2int (w2bits mv). 
rewrite {1}(divz_eq a (2^(8-i)*2^i)) !mulrA divzMDl;
   1: by smt(StdOrder.IntOrder.expr_gt0).
rewrite dvdz_modzDl; 1: by
 have ->  : 2^(8-i) = 2^((8-i-1)+1); [ by smt() |
    rewrite exprS 1:/#; smt(dvdz_mull dvdz_mulr)].  
by have -> : (2 ^ (8 - i) * 2 ^ i) = 256; 
  [ rewrite -StdBigop.Bigint.Num.Domain.exprD_nneg 
     1,2:/# /= -!addrA /= | done ].
qed.



(* ----------- BEGIN W32 BINDINGS ---------- *)

bind bitstring W32.w2bits W32.bits2w W32.to_uint W32.to_sint W32.of_int W32.t 32.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by smt(W32.bits2wK). 
realize ofintP by move => *;rewrite /of_int int2bs_mod.
realize tosintP. move => bv /=;rewrite /to_sint /smod /BVA_Top_JWord_W32_t.msb.
have -> /=: nth false (w2bits bv) (32 - 1) = 2 ^ (32 - 1) <= to_uint bv; last by smt().
rewrite /to_uint. 
rewrite -{2}(cat_take_drop 31 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W32.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
by smt(bs2int_range mem_range W32.size_w2bits pow2_32).
qed.
realize touintP by smt().

bind op [bool & W32.t] W32.init "init".
realize bvinitP.
move=> f; apply (eq_from_nth false).
 rewrite (size_flatten' 1).
  move=> x /mkseqP [y [Hy ->]] /=.
  exact BVA_Top_Pervasive_bool.size_tolist.
 by rewrite size_w2bits size_mkseq /#.
rewrite size_w2bits => i Hi.
rewrite get_w2bits (BitEncoding.BitChunking.nth_flatten false 1 _).
 apply/List.allP => x /mkseqP [y [Hy ->]] /=.
 exact BVA_Top_Pervasive_bool.size_tolist.
by rewrite (:i %% 1 = 0) 1:/# nth_mkseq 1:/# /bool2bits initiE /=.
qed.

bind op [W32.t & bool] W32."_.[_]" "get".
realize bvgetP by rewrite /bool2bits.

bind op W32.t W32.( + ) "add".
realize bvaddP by exact W32.to_uintD.


bind op W32.t W32.( * ) "mul".
realize bvmulP by exact W32.to_uintM. 

op W32_sub (a : W32.t, b: W32.t) : W32.t = 
  a - b.

bind op W32.t W32_sub "sub".
realize bvsubP by  rewrite /W32_sub => bv1 bv2; rewrite W32.to_uintD to_uintN /= /#.

bind op W32.t W32.andw "and".
realize bvandP. 
rewrite /andw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W32.size_w2bits).
qed.

bind op W32.t W32.orw "or".
realize bvorP. 
rewrite /orw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W32.size_w2bits).
qed.

bind op W32.t W32.(+^) "xor".
realize bvxorP. 
rewrite /W32.(+^) /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W32.size_w2bits).
qed.

bind op [W32.t] W32.invw "not".
realize bvnotP.
move=> bv1.
apply (eq_from_nth false); 1: rewrite !size_map size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
by rewrite (nth_map false) 1:// /= /#.
qed.

op rol_32 (w1 w2 : W32.t): W32.t =
  w1 `|<<<|` to_uint w2. 

op (`|<<|`) (w1: W32.t, w2: W8.t): W32.t =
 rol_32 w1 (zeroextu32 (w2 `&` (W8.of_int 31))).

abbrev (\rol) (w1: W32.t, w2: W8.t): W32.t = w1 `|<<|`w2.

bind op [W32.t] rol_32 "rol".
realize bvrolP.
rewrite /rol_32=> bv1 bv2 i Hi.
by rewrite !get_w2bits rolE initiE.
qed.

op ror_32 (w1 w2 : W32.t): W32.t =
  w1 `|>>>|` to_uint w2. 

print W32.(`|>>>|`).
op (`|>>|`) (w1: W32.t, w2: W8.t): W32.t =
 ror_32 w1 (zeroextu32 w2).

abbrev (\ror) (w1: W32.t, w2: W8.t): W32.t = w1 `|>>|`w2.

bind op [W32.t] ror_32 "ror".
realize bvrorP.
rewrite /ror_32=> bv1 bv2 i Hi.
by rewrite !get_w2bits rorE initiE.
qed.

op sll_32 (w1 w2 : W32.t) : W32.t =
 w1 `<<<` to_uint w2.

op (`<<`) (w1: W32.t, w2: W8.t): W32.t =
 sll_32 w1 (zeroextu32 (w2 `&` (W8.of_int 31))).

bind op [W32.t] sll_32 "shl".
realize bvshlP.
rewrite /shl_32 => bv1 bv2.
by rewrite W32.to_uint_shl; 1:smt(W32.to_uint_cmp).
qed.

op srl_32 (w1 w2 : W32.t) : W32.t =
  w1 `>>>` W32.to_uint w2.

op (`>>`) (w1: W32.t, w2: W8.t): W32.t =
 srl_32 w1 (zeroextu32 (w2 `&` (W8.of_int 31))).

bind op [W32.t] srl_32 "shr".
realize bvshrP.
rewrite /shr_32 => bv1 bv2.
by rewrite W32.to_uint_shr; 1:smt(W32.to_uint_cmp).
qed.

op sra_32 (w1 w2 : W32.t) : W32.t =
 W32.sar w1 (to_uint w2).

bind op [W32.t] sra_32 "ashr".
realize bvashrP.
move => bv1 bv2; rewrite W32_sar_div; smt(W32.to_uint_cmp).
qed.

bind op [W8.t & W32.t] W4u8.zeroextu32 "zextend".
realize bvzextendP.
move => bv; rewrite /zeroextu32 /= of_uintK /= modz_small 2://.
apply bound_abs; smt(W8.to_uint_cmp pow2_8).
qed.

bind op [W16.t & W32.t] W2u16.zeroextu32 "zextend".
realize bvzextendP by move => bv; rewrite /zeroextu64 /= of_uintK /=; smt(W16.to_uint_cmp pow2_16).

bind op [W16.t & W32.t] sigextu32 "sextend".
realize bvsextendP.
move => bv;rewrite  /sigextu32 /to_sint /smod /= !of_uintK /=.
case (32768 <= to_uint bv); 2: smt(W16.to_uint_cmp).
move =>?;rewrite -{2}(oppzK (to_uint bv - 65536)) modNz /=; smt(W16.to_uint_cmp pow2_16). 
qed.

bind op [W32.t & W8.t] W4u8.truncateu8 "truncate".
realize bvtruncateP.
move => mv; rewrite /truncateu8 /W32.w2bits take_mkseq 1:// /= /w2bits.
apply (eq_from_nth witness);1: by smt(size_mkseq).
move => i; rewrite size_mkseq /= /max /= => ib.
rewrite !nth_mkseq 1..2:// /of_int /to_uint /= get_bits2w 1:// 
        nth_mkseq 1:// /= get_to_uint /= /to_uint /=.
have -> /=: (0 <= i && i < 32) by smt().
pose a := bs2int (w2bits mv). 
rewrite {1}(divz_eq a (2^(8-i)*2^i)) !mulrA divzMDl;
   1: by smt(StdOrder.IntOrder.expr_gt0).
rewrite dvdz_modzDl; 1: by
 have ->  : 2^(8-i) = 2^((8-i-1)+1); [ by smt() |
    rewrite exprS 1:/#; smt(dvdz_mull dvdz_mulr)].  
by have -> : (2 ^ (8 - i) * 2 ^ i) = 256; 
  [ rewrite -StdBigop.Bigint.Num.Domain.exprD_nneg 
     1,2:/# /= -!addrA /= | done ].
qed.

bind op [W32.t & W16.t] W2u16.truncateu16 "truncate".
realize bvtruncateP.
move => mv; rewrite /truncateu16 /W32.w2bits take_mkseq 1:// /= /w2bits.
apply (eq_from_nth witness);1: by smt(size_mkseq).
move => i; rewrite size_mkseq /= /max /= => ib.
rewrite !nth_mkseq 1..2:// /of_int /to_uint /= get_bits2w 1://
        nth_mkseq 1:// /= get_to_uint /= /to_uint /=.
have -> /=: (0 <= i && i < 32) by smt().
pose a := bs2int (w2bits mv). 
rewrite {1}(divz_eq a (2^(16-i)*2^i)) !mulrA divzMDl;
   1: by smt(StdOrder.IntOrder.expr_gt0).
rewrite dvdz_modzDl; 1: by
 have ->  : 2^(16-i) = 2^((16-i-1)+1); [ by smt() |
    rewrite exprS 1:/#; smt(dvdz_mull dvdz_mulr)].  
by have -> : (2 ^ (16 - i) * 2 ^ i) = 65536; 
  [ rewrite -StdBigop.Bigint.Num.Domain.exprD_nneg 
     1,2:/# /= -!addrA /= | done ].
qed.

op BIC (x y : W32.t) : W32.t =
  x `&` invw y.

abbrev (\BIC) (x y : W32.t) : W32.t = BIC x y.

op BFC (x : W32.t) (lsb width : W8.t) : W32.t =
 let mask = ((W32.of_int (-1)) `<<` width) `|<<|` lsb
 in (x `&` mask).

abbrev (\BFC) x lsb width = BFC x lsb width.

op BFI (x y : W32.t) (lsb width : W8.t) : W32.t =
 let mask = ((W32.of_int (-1)) `<<` width) `|<<|` lsb
 in (x `&` mask) `|` (BIC x y).

abbrev (\BFI) x y lsb width = BFI x y lsb width.


(* ----------- BEGIN W64 BINDINGS ---------- *)

bind bitstring W64.w2bits W64.bits2w W64.to_uint W64.to_sint W64.of_int W64.t 64.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by smt(W64.bits2wK). 
realize ofintP by move => *;rewrite /of_int int2bs_mod.
realize tosintP. move => bv /=;rewrite /to_sint /smod /BVA_Top_JWord_W64_t.msb.
have -> /=: nth false (w2bits bv) (64 - 1) = 2 ^ (64 - 1) <= to_uint bv; last by smt().
rewrite /to_uint. 
rewrite -{2}(cat_take_drop 63 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W64.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
by smt(bs2int_range mem_range W64.size_w2bits pow2_64).
qed.
realize touintP by smt().

bind op [bool & W64.t] W64.init "init".
realize bvinitP.
move=> f; apply (eq_from_nth false).
 rewrite (size_flatten' 1).
  move=> x /mkseqP [y [Hy ->]] /=.
  exact BVA_Top_Pervasive_bool.size_tolist.
 by rewrite size_w2bits size_mkseq /#.
rewrite size_w2bits => i Hi.
rewrite get_w2bits (BitEncoding.BitChunking.nth_flatten false 1 _).
 apply/List.allP => x /mkseqP [y [Hy ->]] /=.
 exact BVA_Top_Pervasive_bool.size_tolist.
by rewrite (:i %% 1 = 0) 1:/# nth_mkseq 1:/# /bool2bits initiE /=.
qed.

bind op [W64.t & bool] W64."_.[_]" "get".
realize bvgetP by rewrite /bool2bits.

bind op W64.t W64.( + ) "add".
realize bvaddP by exact W64.to_uintD.

bind op W64.t W64.( * ) "mul".
realize bvmulP by exact W64.to_uintM.

bind op W64.t W64.andw "and".
realize bvandP. 
rewrite /andw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W64.size_w2bits).
qed.

bind op W64.t W64.orw "or".
realize bvorP. 
rewrite /orw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W64.size_w2bits).
qed.

bind op [W64.t] W64.(+^) "xor".
realize bvxorP.
move => bv1 bv2.
apply (eq_from_nth false); 1: rewrite !size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite (nth_map (false,false)) /=; 1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=; 1:smt(W64.size_w2bits).
qed.

bind op [W64.t] W64.invw "not".
realize bvnotP.
move=> bv1.
apply (eq_from_nth false); 1: rewrite !size_map size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
by rewrite (nth_map false) 1:// /= /#.
qed.


op srl_64 (w1 w2 : W64.t) : W64.t =
  if (64 <= to_uint w2) then  W64.zero else  w1 `>>` (truncateu8 w2).

bind op [W64.t] srl_64 "shr".
realize bvshrP.
rewrite /srl_64 => bv1 bv2.
case : (64 <= to_uint bv2); last first.
+ rewrite /(`>>`) W64.to_uint_shr; 1: by smt(W8.to_uint_cmp).
  rewrite /truncateu8  => bv2bnd />.
  rewrite (pmod_small (to_uint bv2) _); smt(W64.to_uint_cmp).
move => *. 
have -> : to_uint bv2 = (to_uint bv2 - 64) + 64 by ring. 
rewrite exprD_nneg 1,2:/# /=. 
smt(StdOrder.IntOrder.expr_gt0 W64.to_uint_cmp pow2_64).
qed.


op sll_64 (w1 w2 : W64.t) : W64.t =
  if (64 <= to_uint w2) then W64.zero else w1 `<<` (truncateu8 w2).

bind op [W64.t] sll_64 "shl".
realize bvshlP. 
proof.
rewrite /sll_64 => bv1 bv2.
case : (64 <= to_uint bv2); last first.
+ rewrite /(`<<`) W64.to_uint_shl; 1: by smt(W8.to_uint_cmp).
  rewrite /truncateu8  => bv2bnd />.
  rewrite (pmod_small (to_uint bv2) _);smt(W64.to_uint_cmp).
move => *. 
have -> : to_uint bv2 = (to_uint bv2 - 64) + 64 by ring. 
by rewrite exprD_nneg 1,2:/# /= /#.
qed.

op rol_64 (w1 w2 : W64.t): W64.t =
  w1 `|<<<|` to_uint w2. 

bind op [W64.t] rol_64 "rol".
realize bvrolP.
rewrite /rol_64=> bv1 bv2 i Hi.
by rewrite !get_w2bits rolE initiE.
qed.


bind op [W16.t & W64.t] W4u16.zeroextu64 "zextend".
realize bvzextendP
 by move => bv; rewrite /zeroextu64 /= of_uintK /=; smt(W16.to_uint_cmp pow2_16).

bind op [W64.t & W16.t] W4u16.truncateu16 "truncate".
realize bvtruncateP.
move => mv; rewrite /truncateu16 /W64.w2bits take_mkseq 1:// /= /w2bits.
apply (eq_from_nth witness);1: by smt(size_mkseq).
move => i; rewrite size_mkseq /= /max /= => ib.
rewrite !nth_mkseq 1:// /of_int /to_uint 1:// /= get_bits2w 1:// 
        nth_mkseq 1:// /= get_to_uint /= /to_uint /=.
have -> /=: (0 <= i && i < 64) by smt().
pose a := bs2int (w2bits mv). 
rewrite {1}(divz_eq a (2^(16-i)*2^i)) !mulrA divzMDl;
   1: by smt(StdOrder.IntOrder.expr_gt0).
rewrite dvdz_modzDl; 1: by
 have ->  : 2^(16-i) = 2^((16-i-1)+1); [ by smt() |
    rewrite exprS 1:/#; smt(dvdz_mull dvdz_mulr)].  
by have -> : (2 ^ (16 - i) * 2 ^ i) = 65536; 
  [ rewrite -StdBigop.Bigint.Num.Domain.exprD_nneg 
     1,2:/# /= -!addrA /= | done ].
qed.

op truncate64_10 (bw: W64.t) : W10.t = W10.bits2w (W64.w2bits bw).

bind op [W64.t & W10.t] truncate64_10 "truncate".
realize bvtruncateP. 
move => mv. rewrite /truncate64_10 /W64.w2bits take_mkseq 1:// /= /w2bits.
apply (eq_from_nth witness);1: by smt(size_mkseq).
move => i; rewrite size_mkseq /= /max /= => ib.
by rewrite !nth_mkseq 1..2:// /bits2w initiE 1:// /= nth_mkseq /#.  
qed.

bind op [W64.t & W8.t] W8u8.truncateu8 "truncate".
realize bvtruncateP.  (* generalize *)
move => mv; rewrite /truncateu8 /W64.w2bits take_mkseq 1:// /= /w2bits.
apply (eq_from_nth witness);1: by smt(size_mkseq).
move => i; rewrite size_mkseq /= /max /= => ib.
rewrite !nth_mkseq 1..2:// /of_int /to_uint /= get_bits2w 1:// 
        nth_mkseq 1:// /= get_to_uint /= /to_uint /=.
have -> /=: (0 <= i && i < 64) by smt().
pose a := bs2int (w2bits mv). 
rewrite {1}(divz_eq a (2^(8-i)*2^i)) !mulrA divzMDl;
   1: by smt(StdOrder.IntOrder.expr_gt0).
rewrite dvdz_modzDl; 1: by
 have ->  : 2^(8-i) = 2^((8-i-1)+1); [ by smt() |
    rewrite exprS 1:/#; smt(dvdz_mull dvdz_mulr)].  
by have -> : (2 ^ (8 - i) * 2 ^ i) = 256; 
  [ rewrite -StdBigop.Bigint.Num.Domain.exprD_nneg 
     1,2:/# /= -!addrA /= | done ].
qed.



(* ----------- BEGIN W128 BINDINGS ---------- *)

bind bitstring W128.w2bits W128.bits2w W128.to_uint W128.to_sint W128.of_int W128.t 128.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by smt(W128.bits2wK). 
realize ofintP by move => *;rewrite /of_int int2bs_mod.
realize tosintP. move => bv /=;rewrite /to_sint /smod /BVA_Top_JWord_W128_t.msb.
have -> /=: nth false (w2bits bv) (128 - 1) = 2 ^ (128 - 1) <= to_uint bv; last by smt().
rewrite /to_uint. 
rewrite -{2}(cat_take_drop 127 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W128.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
by smt(bs2int_range mem_range W128.size_w2bits pow2_128).
qed.
realize touintP by smt().

(* ----------- BEGIN W256 BINDINGS ---------- *)

bind bitstring W256.w2bits W256.bits2w W256.to_uint W256.to_sint W256.of_int W256.t 256.
realize size_tolist by auto.
realize tolistP by auto.
realize oflistP by smt(W256.bits2wK). 
realize ofintP by move => *;rewrite /of_int int2bs_mod.
realize tosintP. move => bv /=;rewrite /to_sint /smod /BVA_Top_JWord_W256_t.msb.
have -> /=: nth false (w2bits bv) (256 - 1) = 2 ^ (256 - 1) <= to_uint bv; last by smt().
rewrite /to_uint. 
rewrite -{2}(cat_take_drop 255 (w2bits bv)).
rewrite bs2int_cat size_take 1:// W256.size_w2bits /=.
rewrite -bs2int_div 1:// /= get_to_uint /=.
rewrite -bs2int_mod 1:// /= /to_uint.
by smt(bs2int_range mem_range W256.size_w2bits pow2_256).
qed.
realize touintP by smt().

bind op [bool & W256.t] W256.init "init".
realize bvinitP.
move=> f; apply (eq_from_nth false).
 rewrite (size_flatten' 1).
  move=> x /mkseqP [y [Hy ->]] /=.
  exact BVA_Top_Pervasive_bool.size_tolist.
 by rewrite size_w2bits size_mkseq /#.
rewrite size_w2bits => i Hi.
rewrite get_w2bits (BitEncoding.BitChunking.nth_flatten false 1 _).
 apply/List.allP => x /mkseqP [y [Hy ->]] /=.
 exact BVA_Top_Pervasive_bool.size_tolist.
by rewrite (:i %% 1 = 0) 1:/# nth_mkseq 1:/# /bool2bits initiE /=.
qed.

bind op [W256.t & bool] W256."_.[_]" "get".
realize bvgetP by rewrite /bool2bits.

bind op W256.t W256.andw "and".
realize bvandP. 
rewrite /andw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W64.size_w2bits).
qed.

bind op W256.t W256.orw "or".
realize bvorP. 
rewrite /orw /map2 => bv1 bv2.
apply (eq_from_nth false);1: rewrite size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite initiE 1:/# (nth_map (false,false)) /=;1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=;1:smt(W64.size_w2bits).
qed.

bind op [W256.t] W256.(+^) "xor".
realize bvxorP.
move => bv1 bv2.
apply (eq_from_nth false); 1: rewrite !size_map size_zip !size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
rewrite (nth_map (false,false)) /=; 1: rewrite size_zip !size_w2bits /#. 
by rewrite !nth_zip /=; 1:smt(W64.size_w2bits).
qed.

bind op [W256.t] W256.invw "not".
realize bvnotP.
move=> bv1.
apply (eq_from_nth false); 1: rewrite !size_map size_w2bits /#. 
move => i; rewrite size_w2bits /= => ib.
by rewrite (nth_map false) 1:// /= /#.
qed.


bind op [W256.t & W128.t] truncateu128 "truncate".
realize bvtruncateP.
move => mv; rewrite /truncateu128 /W256.w2bits take_mkseq 1:// /= /w2bits.
apply (eq_from_nth witness);1: by smt(size_mkseq).
move => i; rewrite size_mkseq /= /max /= => ib.
rewrite !nth_mkseq 1..2:// /of_int /to_uint /= get_bits2w 1:// 
        nth_mkseq 1:// /= get_to_uint /= /to_uint /=.
have -> /=: (0 <= i && i < 256) by smt().
pose a := bs2int (w2bits mv). 
rewrite {1}(divz_eq a (2^(128-i)*2^i)) !mulrA divzMDl;
   1: by smt(StdOrder.IntOrder.expr_gt0).
rewrite dvdz_modzDl; 1: by
 have ->  : 2^(128-i) = 2^((128-i-1)+1); [ by smt() |
    rewrite exprS 1:/#; smt(dvdz_mull dvdz_mulr)].  
by have -> : (2 ^ (128 - i) * 2 ^ i) = 340282366920938463463374607431768211456; 
  [ rewrite -StdBigop.Bigint.Num.Domain.exprD_nneg 
     1,2:/# /= -!addrA /= | done ].
qed.

(*
(* ----------- BEGIN W512 BINDINGS ---------- *)

theory W512.
  abbrev [-printing] size = 512.
  clone include BitWord with op size <- size
  rename "_XX" as "_256"
  proof gt0_size by done.
end W512.

import W512.

bind bitstring W512.w2bits W512.bits2w W512.to_uint W512.to_sint W512.of_int W512.t 512.
realize size_tolist by auto.
realize tolistP     by auto.
realize oflistP     by smt(W512.bits2wK).
realize ofintP      by move=> *; rewrite /of_int int2bs_mod.
realize touintP     by smt().

realize tosintP.
proof.
move=> bv /= @/to_sint @/smod @/msb.
rewrite (_ : nth _ _ _ = 2 ^ (512 - 1) <= to_uint bv) -1:/#.
rewrite /to_uint -{2}(cat_take_drop 511 (w2bits bv)).
rewrite bs2int_cat size_take ~-1:// W512.size_w2bits /=.
rewrite -bs2int_div ~-1:// /= get_to_uint ~-1:// /=.
rewrite -bs2int_mod ~-1:// /= /to_uint.
have ?: W512.modulus = 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096 by done.
by smt(bs2int_range mem_range W512.size_w2bits).
qed.
*)

(* ----------- BEGIN ARRAY BINDINGS ---------- *)

bind array Array256."_.[_]" Array256."_.[_<-_]" Array256.to_list Array256.of_list Array256.t 256.
realize tolistP by done.
realize get_setP by smt(Array256.get_setE). 
realize eqP by smt(Array256.tP).
realize get_out by smt(Array256.get_out).


bind array Array768."_.[_]" Array768."_.[_<-_]" Array768.to_list Array768.of_list Array768.t 768.
realize tolistP by done.
realize get_setP by smt(Array768.get_setE). 
realize eqP by smt(Array768.tP).
realize get_out by smt(Array768.get_out).

bind array Array32."_.[_]" Array32."_.[_<-_]" Array32.to_list Array32.of_list Array32.t 32.
realize tolistP by done.
realize get_setP by smt(Array32.get_setE). 
realize eqP by smt(Array32.tP).
realize get_out by smt(Array32.get_out).

bind array Array960."_.[_]" Array960."_.[_<-_]" Array960.to_list Array960.of_list Array960.t 960.
realize tolistP by done.
realize get_setP by smt(Array960.get_setE). 
realize eqP by smt(Array960.tP).
realize get_out by smt(Array960.get_out).

bind array Array4."_.[_]" Array4."_.[_<-_]" Array4.to_list Array4.of_list Array4.t 4.
realize tolistP by done.
realize get_setP by smt(Array4.get_setE). 
realize eqP by smt(Array4.tP).
realize get_out by smt(Array4.get_out).

bind array Array5."_.[_]" Array5."_.[_<-_]" Array5.to_list Array5.of_list Array5.t 5.
realize tolistP by done.
realize get_setP by smt(Array5.get_setE). 
realize eqP by smt(Array5.tP).
realize get_out by smt(Array5.get_out).

bind array Array6."_.[_]" Array6."_.[_<-_]" Array6.to_list Array6.of_list Array6.t 6.
realize tolistP by done.
realize get_setP by smt(Array6.get_setE). 
realize eqP by smt(Array6.tP).
realize get_out by smt(Array6.get_out).

bind array Array7."_.[_]" Array7."_.[_<-_]" Array7.to_list Array7.of_list Array7.t 7.
realize tolistP by done.
realize get_setP by smt(Array7.get_setE). 
realize eqP by smt(Array7.tP).
realize get_out by smt(Array7.get_out).

bind array Array24."_.[_]" Array24."_.[_<-_]" Array24.to_list Array24.of_list Array24.t 24.
realize tolistP by done.
realize get_setP by smt(Array24.get_setE). 
realize eqP by smt(Array24.tP).
realize get_out by smt(Array24.get_out).

bind array Array25."_.[_]" Array25."_.[_<-_]" Array25.to_list Array25.of_list Array25.t 25.
realize tolistP by done.
realize get_setP by smt(Array25.get_setE). 
realize eqP by smt(Array25.tP).
realize get_out by smt(Array25.get_out).

bind array Array8."_.[_]" Array8."_.[_<-_]" Array8.to_list Array8.of_list Array8.t 8.
realize tolistP by done.
realize get_setP by smt(Array8.get_setE). 
realize eqP by smt(Array8.tP).
realize get_out by smt(Array8.get_out).

bind array Array50."_.[_]" Array50."_.[_<-_]" Array50.to_list Array50.of_list Array50.t 50.
realize tolistP by done.
realize get_setP by smt(Array50.get_setE). 
realize eqP by smt(Array50.tP).
realize get_out by smt(Array50.get_out).

bind array Array48."_.[_]" Array48."_.[_<-_]" Array48.to_list Array48.of_list Array48.t 48.
realize tolistP by done.
realize get_setP by smt(Array48.get_setE). 
realize eqP by smt(Array48.tP).
realize get_out by smt(Array48.get_out).

op init_8_32 f: W32.t Array8.t = Array8.init f.
bind op [W32.t & Array8.t] init_8_32 "ainit".
realize bvainitP.
proof.
rewrite /init_8_32 => f.
rewrite BVA_Top_Array8_Array8_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array8.initE).
qed.

op init_50_32 f: W32.t Array50.t = Array50.init f.
bind op [W32.t & Array50.t] init_50_32 "ainit".
realize bvainitP.
proof.
rewrite /init_50_32 => f.
rewrite BVA_Top_Array50_Array50_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array50.initE).
qed.

op init_48_32 f: W32.t Array48.t = Array48.init f.
bind op [W32.t & Array48.t] init_48_32 "ainit".
realize bvainitP.
proof.
rewrite /init_48_32 => f.
rewrite BVA_Top_Array48_Array48_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array48.initE).
qed.



op init_256_16 (f: int -> W16.t) : W16.t Array256.t = Array256.init f.

bind op [W16.t & Array256.t] init_256_16 "ainit".
realize bvainitP.
proof.
rewrite /init_256_16 => f.
rewrite BVA_Top_Array256_Array256_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array256.initE).
qed.

op init_768_16 (f: int -> W16.t) : W16.t Array768.t = Array768.init f.

bind op [W16.t & Array768.t] init_768_16 "ainit".
realize bvainitP.
rewrite /init_768_16 => f.
rewrite BVA_Top_Array768_Array768_t.tolistP.
apply eq_in_mkseq => i i_bnd; smt(Array768.initE).
qed.

op init_4_64 (f: int -> W64.t) : W64.t Array4.t = Array4.init f.

bind op [W64.t & Array4.t] init_4_64 "ainit".
realize bvainitP.
proof.
rewrite /init_4_64 => f.
rewrite BVA_Top_Array4_Array4_t.tolistP.
apply eq_in_mkseq => i i_bnd; smt(Array4.initE).
qed.

op init_5_64 (f: int -> W64.t) = Array5.init f.

bind op [W64.t & Array5.t] init_5_64 "ainit".
realize bvainitP.
proof.
rewrite /init_5_64 => f.
rewrite BVA_Top_Array5_Array5_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array5.initE).
qed.

op init_5_32 f: W32.t Array5.t = Array5.init f.
bind op [W32.t & Array5.t] init_5_32 "ainit".
realize bvainitP.
proof.
rewrite /init_5_32 => f.
rewrite BVA_Top_Array5_Array5_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array5.initE).
qed.


op init_6_256 (f: int -> W256.t) = Array6.init f.

bind op [W256.t & Array6.t] init_6_256 "ainit".
realize bvainitP.
proof.
rewrite /init_6_256 => f.
rewrite BVA_Top_Array6_Array6_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array6.initE).
qed.

op init_7_256 (f: int -> W256.t) = Array7.init f.

bind op [W256.t & Array7.t] init_7_256 "ainit".
realize bvainitP.
proof.
rewrite /init_7_256 => f.
rewrite BVA_Top_Array7_Array7_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array7.initE).
qed.

op init_25_64 (f: int -> W64.t) = Array25.init f.

bind op [W64.t & Array25.t] init_25_64 "ainit".
realize bvainitP.
proof.
rewrite /init_25_64 => f.
rewrite BVA_Top_Array25_Array25_t.tolistP.
by apply eq_in_mkseq => i i_bnd; smt(Array25.initE).
qed.

op init_960_8 (f: int -> W8.t) : W8.t Array960.t = Array960.init f.

bind op [W8.t & Array960.t] init_960_8 "ainit".
realize bvainitP.
proof.
rewrite /init_960_8 => f.
rewrite BVA_Top_Array960_Array960_t.tolistP.
apply eq_in_mkseq => i i_bnd; smt(Array960.initE).
qed.

op sliceget256_16_256 (arr: W16.t Array256.t) (offset: int) : W256.t = 
   if 8 %| offset then 
    get256_direct ((init16 (fun (i_0 : int) => arr.[i_0])))%WArray512 (offset %/ 8)
   else W256.bits2w (take 256 (drop offset (flatten (map W16.w2bits (to_list arr))))).

bind op [W16.t & W256.t & Array256.t] sliceget256_16_256 "asliceget".
realize bvaslicegetP.
move => /= arr offset; rewrite /sliceget256_16_256 /= => H k kb. 
case (8%| offset) => /= *; last by smt(W256.get_bits2w).
rewrite /get256_direct pack32E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= bits8E initiE 1:/# /=.
rewrite nth_take 1,2:/# nth_drop 1,2:/#.
rewrite (BitEncoding.BitChunking.nth_flatten false 16 _). 
+ rewrite allP => x /=; rewrite mapP => He; elim He;smt(W16.size_w2bits).
rewrite (nth_map W16.zero []); 1: smt(Array256.size_to_list).
by rewrite nth_mkseq /#.
qed.


op sliceset256_16_256 (arr: W16.t Array256.t) (offset: int) (bv: W256.t) : W16.t Array256.t =
  if 8 %| offset
  then (init (fun (i3 : int) => get16 (set256_direct ((init16 (fun (i_0 : int) => arr.[i_0])))%WArray512 (offset %/ 8) bv) i3))%Array256
  else  Array256.of_list witness (map W16.bits2w (chunk 16 (take offset (flatten (map W16.w2bits (to_list arr))) ++ w2bits bv ++
  drop (offset + 256) (flatten (map W16.w2bits (to_list arr)))))).

lemma size_flatten_W16_w2bits (a : W16.t list) :
  (size (flatten (map W16.w2bits (a))))  =  16 * size a.
proof.
  rewrite size_flatten -map_comp /(\o) /=.
  rewrite StdBigop.Bigint.sumzE /= StdBigop.Bigint.BIA.big_mapT /(\o) /=. 
  rewrite StdBigop.Bigint.big_constz count_predT /#.
qed.

bind op [W16.t & W256.t & Array256.t] sliceset256_16_256 "asliceset".
realize bvaslicesetP. 
move => arr offset bv H /= k kb; rewrite /sliceset256_16_256 /=. 
case (8 %| offset) => /= *; last first.
+ rewrite of_listK; 1: by rewrite size_map size_chunk 1:// !size_cat size_take;
      by smt(size_take size_drop  W16.size_w2bits size_cat Array256.size_to_list size_flatten_W16_w2bits size_ge0). 
  rewrite -(map_comp W16.w2bits W16.bits2w) /(\o). 
  have := eq_in_map ((fun (x : bool list) => w2bits ((bits2w x))%W16)) idfun (chunk 16
        (take offset (flatten (map W16.w2bits (to_list arr))) ++ w2bits bv ++
         drop (offset + 256) (flatten (map W16.w2bits (to_list arr))))).
  rewrite iffE => [#] -> * /=; 1: by smt(in_chunk_size W16.bits2wK).
  rewrite map_id /= chunkK 1://;1: by rewrite !size_cat size_take;
    by smt(size_take size_drop  W16.size_w2bits size_cat Array256.size_to_list size_flatten_W16_w2bits size_ge0). 
  by rewrite !nth_cat !size_cat /=;
     smt(nth_take nth_drop size_take size_drop  W16.size_w2bits size_cat Array256.size_to_list size_flatten_W16_w2bits size_ge0). 
rewrite (nth_flatten _ 16); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W16.size_w2bits).
rewrite (nth_map W16.zero []); 1: smt(Array256.size_to_list).
rewrite nth_mkseq 1:/# /= initiE 1:/# /= get16E pack2E initiE 1:/# /= initiE 1:/# /= /set256_direct.
rewrite initiE 1:/# /=.
case (offset <= k && k < offset + 256) => *; 1: by 
  rewrite ifT 1:/#  get_bits8 /= 1,2:/# initiE // initiE //.
rewrite ifF 1:/# initiE 1:/# /=.
rewrite (nth_flatten _ 16); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W16.size_w2bits).
rewrite (nth_map W16.zero []); 1: smt(Array256.size_to_list).
rewrite nth_mkseq 1:/# /= bits8E /= initiE /# /=.
qed.

op sliceget32_8_256 (arr: W8.t Array32.t) (offset: int) : W256.t = 
if 8 %| offset then 
    get256_direct (WArray32.init8 (fun (i_0 : int) => arr.[i_0])) (offset %/ 8)
   else W256.bits2w (take 256 (drop offset (flatten (map W8.w2bits (to_list arr))))).

bind op [W8.t & W256.t & Array32.t] sliceget32_8_256 "asliceget".
realize bvaslicegetP.
move => /= arr offset; rewrite /sliceget32_8_256 /= => H k kb. 
case (8%| offset) => /= *; last by smt(W256.get_bits2w).
rewrite /get256_direct pack32E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /=. 
rewrite nth_take 1,2:/# nth_drop 1,2:/#.
rewrite (BitEncoding.BitChunking.nth_flatten false 8 _). 
+ rewrite allP => x /=; rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map W8.zero []); 1: smt(Array32.size_to_list).
by rewrite nth_mkseq /#.
qed.

op sliceget768_16_256 (arr: W16.t Array768.t) (offset: int) : W256.t =
if 8 %| offset then 
    get256_direct (WArray1536.init16 (fun (i_0 : int) => arr.[i_0])) (offset %/ 8)
   else W256.bits2w (take 256 (drop offset (flatten (map W16.w2bits (to_list arr))))).


bind op [W16.t & W256.t & Array768.t] sliceget768_16_256 "asliceget".
realize bvaslicegetP.
move => /= arr offset; rewrite /sliceget768_16_256 /= => H k kb. 
case (8%| offset) => /= *; last by smt(W256.get_bits2w).
rewrite /get256_direct pack32E initiE 1:/# /= initiE 1:/# /= initiE 1:/# /= bits8E initiE 1:/# /=.
rewrite nth_take 1,2:/# nth_drop 1,2:/#.
rewrite (BitEncoding.BitChunking.nth_flatten false 16 _). 
+ rewrite allP => x /=; rewrite mapP => He; elim He;smt(W16.size_w2bits).
rewrite (nth_map W16.zero []); 1: smt(Array768.size_to_list).
by rewrite nth_mkseq /#.
qed.

op sliceset960_8_128 (arr: W8.t Array960.t) (offset: int) (bv: W128.t) : W8.t Array960.t = 
  if 8 %| offset
  then Array960.init (fun (i3 : int) => get8 (set128_direct ((init8 (fun (i_0 : int) => arr.[i_0])))%WArray960 (offset %/ 8) bv) i3)
  else  Array960.of_list witness (map W8.bits2w (chunk 8 (take offset (flatten (map W8.w2bits (to_list arr))) ++ w2bits bv ++
  drop (offset + 128) (flatten (map W8.w2bits (to_list arr)))))).

lemma size_flatten_W8_w2bits (a : W8.t list) :
  (size (flatten (map W8.w2bits (a))))  =  8 * size a.
proof.
  rewrite size_flatten -map_comp /(\o) /=.
  rewrite StdBigop.Bigint.sumzE /= StdBigop.Bigint.BIA.big_mapT /(\o) /=. 
  rewrite StdBigop.Bigint.big_constz count_predT /#.
qed.

bind op [W8.t & W128.t & Array960.t] sliceset960_8_128 "asliceset".
realize bvaslicesetP.
move => arr offset bv H /= k kb; rewrite /sliceset960_8_128 /=. 
case (8 %| offset) => /= *; last first.
+ rewrite of_listK; 1: by  rewrite size_map size_chunk 1:// !size_cat size_take; 
      by smt(size_take size_drop  W8.size_w2bits size_cat Array960.size_to_list size_flatten_W8_w2bits size_ge0). 
  rewrite -(map_comp W8.w2bits W8.bits2w) /(\o). 
  have := eq_in_map ((fun (x : bool list) => w2bits ((bits2w x))%W8)) idfun (chunk 8
        (take offset (flatten (map W8.w2bits (to_list arr))) ++ w2bits bv ++
         drop (offset + 128) (flatten (map W8.w2bits (to_list arr))))).
  rewrite iffE => [#] -> * /=; 1: by smt(in_chunk_size W8.bits2wK).
  rewrite map_id /= chunkK 1://;1: by rewrite !size_cat size_take;
    by smt(size_take size_drop  W8.size_w2bits size_cat Array960.size_to_list size_flatten_W8_w2bits size_ge0). 
  by rewrite !nth_cat !size_cat /=;
     smt(nth_take nth_drop size_take size_drop  W8.size_w2bits size_cat Array960.size_to_list size_flatten_W8_w2bits size_ge0). 
rewrite (nth_flatten _ 8); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map W8.zero []); 1: smt(Array960.size_to_list).
rewrite nth_mkseq 1:/# /= initiE 1:/# /= /get8 /set128_direct.
rewrite initiE 1:/# /=.
case (offset <= k && k < offset + 128) => *; 1: by 
  rewrite ifT 1:/#  get_bits8 /= 1,2:/# initiE // initiE //.
rewrite ifF 1:/# initiE 1:/# /=.
rewrite (nth_flatten _ 8); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map W8.zero []); 1: smt(Array960.size_to_list).
rewrite nth_mkseq /#.
qed.


op sliceset960_8_32 (arr: W8.t Array960.t) (offset: int) (bv: W32.t) : W8.t Array960.t = 
  if 8 %| offset
  then Array960.init
     (WArray960.get8
        (set32_direct (WArray960.init8 (fun (i_0 : int) => arr.[i_0])) (
           offset %/ 8) bv))
  else  Array960.of_list witness (map W8.bits2w (chunk 8 (take offset (flatten (map W8.w2bits (to_list arr))) ++ w2bits bv ++
  drop (offset + 32) (flatten (map W8.w2bits (to_list arr)))))).


bind op [W8.t & W32.t & Array960.t] sliceset960_8_32 "asliceset".
realize bvaslicesetP.
move => arr offset bv H /= k kb; rewrite /sliceset960_8_32 /=. 
case (8 %| offset) => /= *; last first.
+ rewrite of_listK; 1: by  rewrite size_map size_chunk 1:// !size_cat size_take; 
      by smt(size_take size_drop  W8.size_w2bits size_cat Array960.size_to_list size_flatten_W8_w2bits size_ge0). 
  rewrite -(map_comp W8.w2bits W8.bits2w) /(\o). 
  have := eq_in_map ((fun (x : bool list) => w2bits ((bits2w x))%W8)) idfun (chunk 8
        (take offset (flatten (map W8.w2bits (to_list arr))) ++ w2bits bv ++
         drop (offset + 32) (flatten (map W8.w2bits (to_list arr))))).
  rewrite iffE => [#] -> * /=; 1: by smt(in_chunk_size W8.bits2wK).
  rewrite map_id /= chunkK 1://;1: by rewrite !size_cat size_take;
    by smt(size_take size_drop  W8.size_w2bits size_cat Array960.size_to_list size_flatten_W8_w2bits size_ge0). 
  by rewrite !nth_cat !size_cat /=;
     smt(nth_take nth_drop size_take size_drop  W8.size_w2bits size_cat Array960.size_to_list size_flatten_W8_w2bits size_ge0). 
rewrite (nth_flatten _ 8); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map W8.zero []); 1: smt(Array960.size_to_list).
rewrite nth_mkseq 1:/# /= initiE 1:/# /= /get8 /set32_direct.
rewrite initiE 1:/# /=.
case (offset <= k && k < offset + 32) => *; 1: by 
  rewrite ifT 1:/#  get_bits8 /= 1,2:/# initiE // initiE //.
rewrite ifF 1:/# initiE 1:/# /=.
rewrite (nth_flatten _ 8); 1: by rewrite allP => i;rewrite mapP => He; elim He;smt(W8.size_w2bits).
rewrite (nth_map W8.zero []); 1: smt(Array960.size_to_list).
rewrite nth_mkseq /#.
qed.

op init_4_32 (f: int -> W32.t) : W32.t Array4.t = Array4.init f.

bind op [W32.t & Array4.t] init_4_32 "ainit".
realize bvainitP. 
rewrite /init_4_32 => f.
rewrite BVA_Top_Array4_Array4_t.tolistP.
apply eq_in_mkseq => i i_bnd;
smt(Array4.initE).
qed.


(* BEGIN BIND CIRCUITS *)

bind circuit VPBROADCAST_16u16 "VPBROADCAST_16u16".
bind circuit VPBROADCAST_8u32 "VPBROADCAST_8u32".
bind circuit VPBROADCAST_4u64 "VPBROADCAST_4u64".
bind circuit VPMADDWD_256 "VPMADDWD_16u16".
bind circuit VPSLLV_8u32 "VPSLLV_8u32".
bind circuit VPSRL_4u64 "VPSRL_4u64".
bind circuit VPSHUFB_256 "VPSHUFB_256".
bind circuit VEXTRACTI128 "VEXTRACTI128".
bind circuit VPBLENDW_128 "VPBLEND_8u16".
bind circuit VPEXTR_32 "VEXTRACTI32_256".
bind circuit W4u32.VPEXTR_32 "VEXTRACTI32_128".
bind circuit VPMULH_16u16 "VPMULH_16u16".
bind circuit VPMULHRS_16u16 "VPMULHRS_16u16".
bind circuit VPMULL_16u16 "VPMULL_16u16".
bind circuit VPSUB_16u16 "VPSUB_16u16".
bind circuit VPADD_16u16 "VPADD_16u16".
bind circuit W32.mulhi "UMULHI_32".

bind circuit VPSHUFD_256 "VPSHUFD_256".
bind circuit VPERMQ "VPERMQ".
bind circuit VPSRL_4u64 "VPSRL_4u64".
bind circuit VPADD_4u64 "VPADD_4u64".
bind circuit VPBLENDD_256 "VPBLEND_8u32".
bind circuit VPSLLV_4u64 "VPSLLV_4u64".
bind circuit VPSRLV_4u64 "VPSRLV_4u64".
bind circuit VPSRLDQ_256 "VPSRLDQ_256".
