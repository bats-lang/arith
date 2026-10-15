#include "share/atspre_staload.hats"
#use arith as AR

(* a shift by 3 and then by 4 is a shift by 7, not by 8 *)
prfn claim {h,l,h1,l1,h2,l2:nat} (p: $AR.SHR(3, h, l, h1, l1), q: $AR.SHR(4, h1, l1, h2, l2)): $AR.SHR(8, h, l, h2, l2) =
  $AR.shr_add(p, q)

implement main0 () = ()
