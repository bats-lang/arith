#include "share/atspre_staload.hats"
#use arith as AR

(* the low half of an and is not the first operand: 1 and 2 is 0 *)
fn claim {h1,l1,h2,l2:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536}
  (h1: int h1, l1: int l1, h2: int h2, l2: int l2)
  : [h3,l3:nat | h3 < 65536; l3 < 65536; l3 == l1] ($AR.AND(h1, h2, h3), $AR.AND(l1, l2, l3) | @(int h3, int l3)) =
  $AR.and32(h1, l1, h2, l2)

implement main0 () = ()
