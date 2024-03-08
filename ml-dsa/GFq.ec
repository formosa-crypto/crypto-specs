require import AllCore.
require import IntDiv.
require import ZModP Ring.

op q : int = 8380417 axiomatized by qE.
axiom prime_q : prime q.

clone import ZModField as Zq with 
  op p <- q 
  rename "zmod" as "coeff"
  rename "ZModp" as "Zq"
  proof  prime_p by apply prime_q
  proof *.

(* Signed representation *)
op as_sint(x : coeff) = if (q-1) %/ 2 < asint x then asint x - q else asint x.

abbrev absZq (x: coeff): int = `| as_sint x |.

op d : int = 13.
op gamma1 : int = 2^19.
op gamma2 : int = (q - 1) %/ 32.

op smod(n d : int) : int = if (d %/2 < n %% d) then n %% d - d else n %%d.

op Power2Round(x : coeff) : int * int = 
    let rplus = asint x in
    let rzero = smod rplus 2^d
    in ((rplus - rzero) %/ 2^d,rzero).

op Decompose(r : coeff) : int * int = 
   let rplus = asint r in
   let rzero = smod rplus (2*gamma2) in
   if (rplus - rzero = q-1) 
   then (0,rzero - 1)
   else ((rplus - rzero) %/ (2*gamma2),rzero).

op HighBits(r : coeff) = (Decompose r).`1.

op LowBits(r : coeff) = (Decompose r).`2.

op MakeHint(z r : coeff) : bool = 
   let r1 = HighBits(r) in
   let v1 = HighBits(r+z) in
      r1 <> v1.

op UseHint(h : bool, r : coeff) : int = 
    let m = (q-1) %/ (2*gamma2) in
    let (r1,r0) = Decompose r in
    if h && 0 < r0
    then (r1 + 1) %% m
    else if (h && r0 <= 0)
         then (r1 - 1) %% m
         else r1.

