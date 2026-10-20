#include "share/atspre_staload.hats"
#use arith as AR

(* the high half is the first two bytes, not the last two *)
fn halves_swapped {a,b,c,d:nat | a < 256; b < 256; c < 256; d < 256} (a: int a, b: int b, c: int c, d: int d): $AR.word32(256*c + d, 256*a + b) =
  $AR.word32_pack_inline(a, b, c, d)

implement main0 () = let val _ = halves_swapped(1, 2, 3, 4) in () end
