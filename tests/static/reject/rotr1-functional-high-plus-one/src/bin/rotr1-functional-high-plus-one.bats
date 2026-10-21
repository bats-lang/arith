#include "share/atspre_staload.hats"
#use arith as AR

(* the statement claims h2 == h3 + 1; the call of rotr1_functional gives h2 == h3 *)
prfn claim {h,l,h2,l2,h3,l3:nat} (p: $AR.ROTR1(h, l, h2, l2), q: $AR.ROTR1(h, l, h3, l3)): [h2 == h3 + 1; l2 == l3] void =
  $AR.rotr1_functional(p, q)

implement main0 () = ()
