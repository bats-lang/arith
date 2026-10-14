#include "share/atspre_staload.hats"
#use arith as AR

(* a false variant of the lemma, with its proof: the solver must reject it *)
prfn _low {l1,l2,l3,l4,c,c2:nat | l1 < 65536; l2 < 65536; l3 < 65536; l4 < 65536; c < 2; c2 < 2;
  l1 + l2 == l3 + 65536*c; l1 + l2 == l4 + 65536*c2} (): [c == c2; l3 == l4] void = ()
prfn _high {h1,h2,h3,h4,c,d,d2:nat | h1 < 65536; h2 < 65536; h3 < 65536; h4 < 65536; c < 2; d < 2; d2 < 2;
  h1 + h2 + c == h3 + 65536*d; h1 + h2 + c == h4 + 65536*d2} (): [h3 == h4 + 1] void = ()
prfn claim {h1,l1,h2,l2,h3,l3,h4,l4:nat}
  (p: $AR.ADD32(h1, l1, h2, l2, h3, l3), q: $AR.ADD32(h1, l1, h2, l2, h4, l4)): [h3 == h4 + 1; l3 == l4] void =
  case+ p of $AR.ADD32_mk{..}{c,d}() => (case+ q of $AR.ADD32_mk{..}{c2,d2}() => let
    prval () = _low{l1,l2,l3,l4,c,c2}()
    prval () = _high{h1,h2,h3,h4,c,d,d2}()
  in end)

implement main0 () = ()
