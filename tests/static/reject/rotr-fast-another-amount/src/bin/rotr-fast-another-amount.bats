#include "share/atspre_staload.hats"
#use arith as AR

(* a proof of a rotation by n + 1 *)
fn rotated_by_next {n,h,l,h2,l2:nat} (n: int n, pf: $AR.ROTR(n + 1, h, l, h2, l2) | h2: int h2, l2: int l2): int = h2

(* the fast rotation by n is a proof of a rotation by n, not by n + 1 *)
fn claim {n,h,l:nat | n < 31; h < 65536; l < 65536} (n: int n, h: int h, l: int l): int = let
  val (pf | @(h2, l2)) = $AR.rotr_fast(n, h, l)
in rotated_by_next(n, pf | h2, l2) end

implement main0 () = println! (claim(3, 1, 2))
