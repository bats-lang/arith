#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn rotr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.ROTR(n, h, l, h2, l2)): $AR.ROTR(n, c, d, c2, d2) = p

prfn claim {a,b,r,t:nat | a < 16384; b < 16384; r < 4; t < 4} ()
  : $AR.ROTR(2, 4*a + r, 4*b + t, a + 16384*t, b + 16384*r + 1) = let
  prval first = $AR.rotr_digits_1{2*a + r/2, 2*b + t/2, r - 2*(r/2), t - 2*(t/2)}()
  prval second = $AR.rotr_digits_1{a + 16384*(t - 2*(t/2)), b + 16384*(r - 2*(r/2)), r/2, t/2}()
in rotr_cast($AR.rotr_add(first, second)) end

implement main0 () = ()
