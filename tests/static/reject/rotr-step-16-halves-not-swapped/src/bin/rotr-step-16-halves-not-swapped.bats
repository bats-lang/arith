#include "share/atspre_staload.hats"
#use arith as AR

(* the step by 16 swaps the halves *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : ($AR.ROTR(16, h, l, l, h) | @(int l, int h)) = ($AR.rotr_by_16{h,l}() | @(h, l))

implement main0 () = ()
