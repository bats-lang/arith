#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn shr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.SHR(n, h, l, h2, l2)): $AR.SHR(n, c, d, c2, d2) = p

prfn claim {a,b,r,t:nat | a < 4096; b < 4096; r < 16; t < 16} ()
  : $AR.SHR(4, 16*a + r, 16*b + t, a, b + 256*r) = let
  prval first = $AR.shr_digits_2{4*a + r/4, 4*b + t/4, r - 4*(r/4), t - 4*(t/4)}()
  prval second = $AR.shr_digits_2{a, b + 4096*(r - 4*(r/4)), r/4, t/4}()
in shr_cast($AR.shr_add(first, second)) end

implement main0 () = ()
