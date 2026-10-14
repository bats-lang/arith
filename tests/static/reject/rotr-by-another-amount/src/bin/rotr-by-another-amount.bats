#include "share/atspre_staload.hats"
#use arith as AR

(* a rotation by 3 is not a proof of a rotation by 4 *)
prfn claim {h,l,h2,l2:nat} (pf: $AR.ROTR(3, h, l, h2, l2)): $AR.ROTR(4, h, l, h2, l2) = pf

implement main0 () = ()
