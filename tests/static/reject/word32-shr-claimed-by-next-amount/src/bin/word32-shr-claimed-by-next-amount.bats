#include "share/atspre_staload.hats"
#use arith as AR

(* a proof of a shift by n + 1 *)
fn shifted_by_next {n,h,l,h2,l2:nat} (n: int n, pf: $AR.SHR(n + 1, h, l, h2, l2) | x: $AR.word32(h2, l2)): int = n

(* the shift of a word by n is a proof of a shift by n, not by n + 1 *)
fn claim {n,h,l:nat | n < 31; h < 65536; l < 65536} (n: int n, x: $AR.word32(h, l)): int = let
  val (pf | s) = $AR.word32_shr(x, n)
in shifted_by_next(n, pf | s) end

implement main0 () = println! (claim(3, $AR.word32_of_half(1)))
