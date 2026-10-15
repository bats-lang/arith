#include "share/atspre_staload.hats"
#use arith as AR

(* a rotation by 3 and then by 4 is a rotation by 7, not by 8 *)
prfn claim {h,l,h1,l1,h2,l2:nat} (p: $AR.ROTR(3, h, l, h1, l1), q: $AR.ROTR(4, h1, l1, h2, l2)): $AR.ROTR(8, h, l, h2, l2) =
  $AR.rotr_add(p, q)

implement main0 () = ()
