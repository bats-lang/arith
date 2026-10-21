#include "share/atspre_staload.hats"
#use arith as AR

(* the statement claims h2 one more than the lemma gives *)
prfn claim {a,b,r,t:nat | a < 256; b < 256; r < 256; t < 256} ()
  : $AR.ROTR(8, 256*a + r, 256*b + t, a + 256*t + 1, b + 256*r) = $AR.rotr_digits_8{a,b,r,t}()

implement main0 () = ()
