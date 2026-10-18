#include "share/atspre_staload.hats"
#use arith as AR

(* the proofs for the high halves and the low halves, in that order *)
fn halves {a,b,c,d,e,f:nat} (high: $AR.XOR(a, c, e), low: $AR.XOR(b, d, f) | x: $AR.word32(e, f)): int = 0

(* the exclusive or's proof for the high halves is not the low halves' *)
fn claim {a,b,c,d:nat | a < 65536; b < 65536; c < 65536; d < 65536} (x: $AR.word32(a, b), y: $AR.word32(c, d)): int = let
  val (high, low | z) = $AR.word32_xor(x, y)
in halves(low, high | z) end

implement main0 () = println! (claim($AR.word32_of_half(1), $AR.word32_of_half(2)))
