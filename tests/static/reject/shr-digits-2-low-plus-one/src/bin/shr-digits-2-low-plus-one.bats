#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn shr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.SHR(n, h, l, h2, l2)): $AR.SHR(n, c, d, c2, d2) = p

prfn claim {a,b,r,t:nat | a < 16384; b < 16384; r < 4; t < 4} ()
  : $AR.SHR(2, 4*a + r, 4*b + t, a, b + 16384*r + 1) = let
  prval first = $AR.shr_digits_1{2*a + r/2, 2*b + t/2, r - 2*(r/2), t - 2*(t/2)}()
  prval second = $AR.shr_digits_1{a, b + 16384*(r - 2*(r/2)), r/2, t/2}()
in shr_cast($AR.shr_add(first, second)) end

implement main0 () = ()
