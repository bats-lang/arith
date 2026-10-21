#include "share/atspre_staload.hats"
#use arith as AR

(* the step by 1 returns its low half as the proof says: one more is false *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.ROTR(1, h, l, h2, l2 + 1) | @(int h2, int l2)) =
  $AR.rotr_step_1(h, l)

implement main0 () = ()
