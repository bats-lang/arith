#include "share/atspre_staload.hats"
#use arith as AR

(* the step by 16 leaves zero in the high half *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : ($AR.SHR(16, h, l, 0, h) | @(int 0, int h)) = ($AR.shr_by_16{h,l}() | @(h, h))

implement main0 () = ()
