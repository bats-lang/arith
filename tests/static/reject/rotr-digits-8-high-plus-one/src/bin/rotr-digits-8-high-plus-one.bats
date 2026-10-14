#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn rotr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.ROTR(n, h, l, h2, l2)): $AR.ROTR(n, c, d, c2, d2) = p

prfn claim {a,b,r,t:nat | a < 256; b < 256; r < 256; t < 256} ()
  : $AR.ROTR(8, 256*a + r, 256*b + t, a + 256*t + 1, b + 256*r) = let
  prval first = $AR.rotr_digits_4{16*a + r/16, 16*b + t/16, r - 16*(r/16), t - 16*(t/16)}()
  prval second = $AR.rotr_digits_4{a + 256*(t - 16*(t/16)), b + 256*(r - 16*(r/16)), r/16, t/16}()
in rotr_cast($AR.rotr_add(first, second)) end

implement main0 () = ()
