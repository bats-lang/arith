#include "share/atspre_staload.hats"
#use arith as AR

(* the step by 16 swaps the halves: its values are the halves swapped, so
   the claim that they are not is false *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : ($AR.ROTR(16, h, l, l, h) | @(int h, int l)) =
  $AR.rotr_step_16(h, l)

implement main0 () = ()
