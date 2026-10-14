#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
(* a number is its half and its lowest bit in one way only: the halves are not one apart *)
prfn claim {a,s,a2,s2:nat | s < 2; s2 < 2; 2*a + s == 2*a2 + s2} (): [a == a2 + 1; s == s2] void = ()

implement main0 () = ()
