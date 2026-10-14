#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
(* the low halves: one sum in two ways has one carry and one result *)
prfn claim {l1,l2,l3,l4,c,c2:nat | l1 < 65536; l2 < 65536; l3 < 65536; l4 < 65536; c < 2; c2 < 2;
  l1 + l2 == l3 + 65536*c; l1 + l2 == l4 + 65536*c2} (): [c == c2; l3 == l4 + 1] void = ()

implement main0 () = ()
