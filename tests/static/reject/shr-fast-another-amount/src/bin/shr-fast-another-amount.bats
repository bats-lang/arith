#include "share/atspre_staload.hats"
#use arith as AR

(* a proof of a shift by n + 1 *)
fn shifted_by_next {n,h,l,h2,l2:nat} (n: int n, pf: $AR.SHR(n + 1, h, l, h2, l2) | h2: int h2, l2: int l2): int = h2

(* the fast shift by n is a proof of a shift by n, not by n + 1 *)
fn claim {n,h,l:nat | n < 31; h < 65536; l < 65536} (n: int n, h: int h, l: int l): int = let
  val (pf | @(h2, l2)) = $AR.shr_fast(n, h, l)
in shifted_by_next(n, pf | h2, l2) end

implement main0 () = println! (claim(3, 1, 2))
