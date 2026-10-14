#include "share/atspre_staload.hats"
#use arith as AR

(* a rotation by 16 swaps the halves: it does not leave them *)
prfn claim {h,l:nat | h < 65536; l < 65536} (): $AR.ROTR(16, h, l, h, l) = $AR.rotr_by_16{h,l}()

implement main0 () = ()
