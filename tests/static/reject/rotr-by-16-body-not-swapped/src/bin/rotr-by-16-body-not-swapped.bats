#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn rotr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.ROTR(n, h, l, h2, l2)): $AR.ROTR(n, c, d, c2, d2) = p

prfn claim {h,l:nat | h < 65536; l < 65536} ()
  : $AR.ROTR(16, h, l, h, l) = let
  prval first = $AR.rotr_digits_8{h/256, l/256, h - 256*(h/256), l - 256*(l/256)}()
  prval second = $AR.rotr_digits_8{l - 256*(l/256), h - 256*(h/256), h/256, l/256}()
in rotr_cast($AR.rotr_add(first, second)) end

implement main0 () = ()
