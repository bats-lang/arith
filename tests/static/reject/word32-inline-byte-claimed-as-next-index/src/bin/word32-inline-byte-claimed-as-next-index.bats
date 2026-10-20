#include "share/atspre_staload.hats"
#use arith as AR

(* a proof of the byte after the one asked for *)
fn byte_after {i,h,l,b:nat} (i: int i, pf: $AR.WORD_BYTE(i + 1, h, l, b) | b: int b): int = b

(* byte i of a word is a proof about byte i, not about byte i + 1 *)
fn claim {i,h,l:nat | i < 3; h < 65536; l < 65536} (i: int i, x: $AR.word32(h, l)): int = let
  val (pf | b) = $AR.word32_byte_inline(x, i)
in byte_after(i, pf | b) end

implement main0 () = println! (claim(1, $AR.word32_of_half(1)))
