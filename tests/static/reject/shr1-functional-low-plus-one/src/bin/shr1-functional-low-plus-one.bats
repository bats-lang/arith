#include "share/atspre_staload.hats"
#use arith as AR

(* the statement claims l2 == l3 + 1; the call of shr1_functional gives l2 == l3 *)
prfn claim {h,l,h2,l2,h3,l3:nat} (p: $AR.SHR1(h, l, h2, l2), q: $AR.SHR1(h, l, h3, l3)): [h2 == h3; l2 == l3 + 1] void =
  $AR.shr1_functional(p, q)

implement main0 () = ()
