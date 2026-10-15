#include "share/atspre_staload.hats"
#use arith as AR

(* 2 to the 16 needs sixteen steps; fifteen make 2 to the 15 *)
prfn claim (): $AR.POW2(16, 65536) =
  $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ(
  $AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ($AR.POW2_succ(
  $AR.POW2_zero())))))))))))))))

implement main0 () = ()
