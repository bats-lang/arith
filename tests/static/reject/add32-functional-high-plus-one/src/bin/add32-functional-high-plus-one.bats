#include "share/atspre_staload.hats"
#use arith as AR

(* the statement claims h3 == h4 + 1; the lemma gives h3 == h4 *)
prfn claim {h1,l1,h2,l2,h3,l3,h4,l4:nat}
  (p: $AR.ADD32(h1, l1, h2, l2, h3, l3), q: $AR.ADD32(h1, l1, h2, l2, h4, l4)): [h3 == h4 + 1; l3 == l4] void =
  $AR.add32_functional(p, q)

implement main0 () = ()
