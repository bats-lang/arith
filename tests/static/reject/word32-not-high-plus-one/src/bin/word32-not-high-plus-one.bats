#include "share/atspre_staload.hats"
#use arith as AR

(* a proof that the high half of the complement is one more than it is *)
fn complement_plus_one {h,l:nat} (pf: $AR.NOT32(h, l, 65535 - h + 1, 65535 - l) | x: $AR.word32(65535 - h + 1, 65535 - l)): int = 0

fn claim {h,l:nat | h < 65536; l < 65536} (x: $AR.word32(h, l)): int = let
  val (pf | y) = $AR.word32_not(x)
in complement_plus_one(pf | y) end

implement main0 () = println! (claim($AR.word32_of_half(1)))
