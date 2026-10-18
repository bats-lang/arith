#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
(* a byte of a word is one number: the two are not one apart *)
prfn claim {a,b,r,s:nat | a < 256; b < 256; r < 256; s < 256; 256*a + r == 256*b + s} (): [a == b + 1] void = ()

implement main0 () = ()
