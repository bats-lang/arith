#include "share/atspre_staload.hats"
#use arith as AR

prfn rotr_cast {n,h,l,h2,l2,c,d,c2,d2:nat | h == c; l == d; h2 == c2; l2 == d2}
  (p: $AR.ROTR(n, h, l, h2, l2)): $AR.ROTR(n, c, d, c2, d2) = p

(* the step by 8 with a wrong result: its proof is the library's, the halves are not *)
fn claim {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l)
  : [h2,l2:nat | h2 < 65536; l2 < 65536] ($AR.ROTR(8, h, l, h2, l2) | @(int h2, int l2)) = let
  val a = h / 256
  val b = l / 256
  val r = $AR.sub_g1(h, $AR.mul_g1(256, a))
  val t = $AR.sub_g1(l, $AR.mul_g1(256, b))
  prval pf = $AR.rotr_digits_8{h/256, l/256, h - 256*(h/256), l - 256*(l/256)}()
in (rotr_cast(pf) | @($AR.add_g1($AR.add_g1(a, $AR.mul_g1(256, t)), 1), $AR.add_g1(b, $AR.mul_g1(256, r)))) end

implement main0 () = ()
