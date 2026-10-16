#include "share/atspre_staload.hats"
#use arith as AR

(* the high half of an exclusive or is not the sum of the high halves: 1 xor 1 is 0 *)
fn claim {h1,l1,h2,l2:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536}
  (h1: int h1, l1: int l1, h2: int h2, l2: int l2)
  : [h3,l3:nat | h3 < 65536; l3 < 65536; h3 == h1 + h2] ($AR.XOR(h1, h2, h3), $AR.XOR(l1, l2, l3) | @(int h3, int l3)) =
  $AR.xor32(h1, l1, h2, l2)

implement main0 () = ()
