#include "share/atspre_staload.hats"
#use arith as AR

(* the statement claims h2 one more than the lemma gives *)
prfn claim {a,b,r,t:nat | a < 32768; b < 32768; r < 2; t < 2} ()
  : $AR.ROTR(1, 2*a + r, 2*b + t, a + 32768*t + 1, b + 32768*r) = $AR.rotr_digits_1{a,b,r,t}()

implement main0 () = ()
