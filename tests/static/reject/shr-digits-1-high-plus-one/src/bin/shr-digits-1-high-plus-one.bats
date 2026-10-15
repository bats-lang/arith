#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn claim {a,b,r,t:nat | a < 32768; b < 32768; r < 2; t < 2} ()
  : $AR.SHR(1, 2*a + r, 2*b + t, a + 1, b + 32768*r) =
  $AR.SHR_succ($AR.SHR1_mk{a,b}{r,t}(), $AR.SHR_zero())

implement main0 () = ()
