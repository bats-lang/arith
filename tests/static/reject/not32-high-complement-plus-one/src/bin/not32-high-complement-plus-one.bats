#include "share/atspre_staload.hats"
#use arith as AR

(* the complement of the high half is 65535 - h, not 65536 - h *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : ($AR.NOT32(h, l, 65536 - h, 65535 - l) | @(int(65536 - h), int(65535 - l))) =
  $AR.not32(h, l)

implement main0 () = ()
