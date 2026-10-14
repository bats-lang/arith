#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn rotr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.ROTR(n, h, l, h2, l2)): $AR.ROTR(n, c, d, c2, d2) = p

prfn claim {a,b,r,t:nat | a < 4096; b < 4096; r < 16; t < 16} ()
  : $AR.ROTR(4, 16*a + r, 16*b + t, a + 4096*r, b + 4096*t) = let
  prval first = $AR.rotr_digits_2{4*a + r/4, 4*b + t/4, r - 4*(r/4), t - 4*(t/4)}()
  prval second = $AR.rotr_digits_2{a + 4096*(t - 4*(t/4)), b + 4096*(r - 4*(r/4)), r/4, t/4}()
in rotr_cast($AR.rotr_add(first, second)) end

implement main0 () = ()
