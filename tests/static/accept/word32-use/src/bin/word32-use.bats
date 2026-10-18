#include "share/atspre_staload.hats"
#use arith as AR

(* A word's shift and exclusive or run on one machine word, and their proofs
   are the ones the halves-based specification gives: the shift by 3 of the
   word is the shift by 3 of its halves (SHR is a function), and the
   exclusive or is one of each half *)
fn small {h,l:nat | h < 65536; l < 65536} (x: $AR.word32(h, l), h: int h, l: int l): int = let
  val (fast | s) = $AR.word32_shr(x, 3)
  val (spec | @(sh, sl)) = $AR.shr(3, h, l)
  prval () = $AR.shr_functional(fast, spec)
  val (high, low | t) = $AR.word32_xor(s, x)
  val (hi2, lo2 | @(xh, xl)) = $AR.xor32(sh, sl, h, l)
  prval () = $AR.xor_functional(high, hi2)
  prval () = $AR.xor_functional(low, lo2)
in $AR.add_int_int(xh, xl) end

implement main0 () = println! (small($AR.word32_of_half(5), 0, 5))
