#include "share/atspre_staload.hats"
#use arith as AR

(* without the bounds of both halves the result is not a half *)
fn claim {h1,l1,h2,l2:nat | h1 < 65536; l1 < 65536; h2 < 65536; l2 < 65536}
  (h1: int h1, l1: int l1, h2: int h2, l2: int l2)
  : [h3,l3:nat | h3 < 65536; l3 < 65536] ($AR.AND(h1, h2, h3), $AR.AND(l1, l2, l3) | @(int h3, int l3)) = let
  val (high | h3) = $AR.and_proved(h1, h2)
  val (low | l3) = $AR.and_proved(l1, l2)
  prval () = $AR.and_bound($AR.pow2_half(), high)
in (high, low | @(h3, l3)) end

implement main0 () = ()
