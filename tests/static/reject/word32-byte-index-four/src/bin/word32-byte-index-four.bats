#include "share/atspre_staload.hats"
#use arith as AR

(* a word has bytes 0 to 3 *)
fn claim (x: $AR.word32(0, 1)): int = let
  val (_ | b) = $AR.word32_byte(x, 4)
in b end

implement main0 () = println! (claim($AR.word32_of_half(1)))
