#include "share/atspre_staload.hats"
#use arith as AR

(* the halves are under 2 to the 16 = 65536; a proof of 2 to the 15 bounds them by 32768 only *)
prfn claim {h1,h2,h3:nat | h1 < 65536; h2 < 65536} (w: $AR.POW2(15, 32768), x: $AR.OR(h1, h2, h3)): [h3 < 65536] void =
  $AR.or_bound(w, x)

implement main0 () = ()
