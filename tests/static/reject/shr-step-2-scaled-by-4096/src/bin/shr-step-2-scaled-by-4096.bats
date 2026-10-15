#include "share/atspre_staload.hats"
#use arith as AR

prfn shr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.SHR(n, h, l, h2, l2)): $AR.SHR(n, c, d, c2, d2) = p

(* the step by 2 with a wrong result: its proof is the library's, the halves are not *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.SHR(2, h, l, h2, l2) | @(int h2, int l2)) = let
  val a = h / 4
  val b = l / 4
  val r = $AR.sub_g1(h, $AR.mul_g1(4, a))
  prval pf = $AR.shr_digits_2{h/4, l/4, h - 4*(h/4), l - 4*(l/4)}()
in (shr_cast(pf) | @(a, $AR.add_g1(b, $AR.mul_g1(4096, r)))) end

implement main0 () = ()
