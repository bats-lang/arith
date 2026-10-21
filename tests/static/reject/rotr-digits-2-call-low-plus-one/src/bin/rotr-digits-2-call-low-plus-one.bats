#include "share/atspre_staload.hats"
#use arith as AR

(* the statement claims l2 one more than the lemma gives *)
prfn claim {a,b,r,t:nat | a < 16384; b < 16384; r < 4; t < 4} ()
  : $AR.ROTR(2, 4*a + r, 4*b + t, a + 16384*t, b + 16384*r + 1) = $AR.rotr_digits_2{a,b,r,t}()

implement main0 () = ()
