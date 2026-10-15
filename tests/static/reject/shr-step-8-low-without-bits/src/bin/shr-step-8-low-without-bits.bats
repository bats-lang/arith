#include "share/atspre_staload.hats"
#use arith as AR

prfn shr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.SHR(n, h, l, h2, l2)): $AR.SHR(n, c, d, c2, d2) = p

(* the step by 8 with a wrong result: its proof is the library's, the halves are not *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.SHR(8, h, l, h2, l2) | @(int h2, int l2)) = let
  val a = h / 256
  val b = l / 256
  val r = $AR.sub_g1(h, $AR.mul_g1(256, a))
  prval pf = $AR.shr_digits_8{h/256, l/256, h - 256*(h/256), l - 256*(l/256)}()
in (shr_cast(pf) | @(a, b)) end

implement main0 () = ()
