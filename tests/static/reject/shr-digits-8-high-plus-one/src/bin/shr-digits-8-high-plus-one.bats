#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn shr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.SHR(n, h, l, h2, l2)): $AR.SHR(n, c, d, c2, d2) = p

prfn claim {a,b,r,t:nat | a < 256; b < 256; r < 256; t < 256} ()
  : $AR.SHR(8, 256*a + r, 256*b + t, a + 1, b + 256*r) = let
  prval first = $AR.shr_digits_4{16*a + r/16, 16*b + t/16, r - 16*(r/16), t - 16*(t/16)}()
  prval second = $AR.shr_digits_4{a, b + 256*(r - 16*(r/16)), r/16, t/16}()
in shr_cast($AR.shr_add(first, second)) end

implement main0 () = ()
