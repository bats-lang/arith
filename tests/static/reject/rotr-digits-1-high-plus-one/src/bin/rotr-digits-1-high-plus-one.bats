#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn claim {a,b,r,t:nat | a < 32768; b < 32768; r < 2; t < 2} ()
  : $AR.ROTR(1, 2*a + r, 2*b + t, a + 32768*t + 1, b + 32768*r) = $AR.ROTR_succ($AR.ROTR1_mk{a,b}{r,t}(), $AR.ROTR_zero())

implement main0 () = ()
