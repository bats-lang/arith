#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn shr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.SHR(n, h, l, h2, l2)): $AR.SHR(n, c, d, c2, d2) = p

prfn claim {h,l:nat | h < 65536; l < 65536} ()
  : $AR.SHR(16, h, l, 0, l) = let
  prval first = $AR.shr_digits_8{h/256, l/256, h - 256*(h/256), l - 256*(l/256)}()
  prval second = $AR.shr_digits_8{0, h - 256*(h/256), h/256, l/256}()
in shr_cast($AR.shr_add(first, second)) end

implement main0 () = ()
