#include "share/atspre_staload.hats"
#use arith as AR

(* The word operations are proved against ROTR, SHR and ADD32 (bit by bit
   and carry by carry); here they are compared with the standard's own
   formulas on C's 32-bit unsigned int (FIPS 180-4, sections 3.2 and 2.2.2:
   ROTR^n(x) = (x >> n) or (x << (32 - n)), SHR^n(x) = x >> n, and the sum
   modulo 2 to the 32) for edge words and a fixed pseudo-random sequence,
   every amount of 1 to 31. This ties the specification to the formulas it
   stands for. Exits 1 on any mismatch. *)
fn whole (h: int, l: int): uint =
  (g0int2uint_int_uint(h) << 16) lor g0int2uint_int_uint(l)

fn bad(ok: bool): int = if ok then 0 else 1

fn plus(a: int, b: int): int = $AR.add_int_int(a, b)

fn same {h2,l2:nat | h2 < 65536; l2 < 65536} (h2: int h2, l2: int l2, want: uint): bool =
  whole(h2, l2) = want

fn agrees {h,l,h0,l0:nat | h < 65536; l < 65536; h0 < 65536; l0 < 65536} (h: int h, l: int l, h0: int h0, l0: int l0): int = let
  val x = whole(h, l)
  fun amounts {n:nat | n <= 32} .<32 - n>. (n: int n, failed: int): int =
    if n >= 32 then failed
    else if n = 0 then amounts(n + 1, failed)
    else let
      val (_ | @(rh, rl)) = $AR.rotr(n, h, l)
      val (_ | @(sh, sl)) = $AR.shr(n, h, l)
      val rot_ok = same(rh, rl, (x >> n) lor (x << (32 - n)))
      val shr_ok = same(sh, sl, x >> n)
    in amounts(n + 1, plus(failed, plus(bad(rot_ok), bad(shr_ok)))) end
  val (_ | @(zh, zl)) = $AR.rotr(0, h, l)
  val (_ | @(nh, nl)) = $AR.not32(h, l)
  val (_ | @(ah, al)) = $AR.add32(h, l, h0, l0)
  val (_, _ | @(xh, xl)) = $AR.xor32(h, l, h0, l0)
  val (_, _ | @(dh, dl)) = $AR.and32(h, l, h0, l0)
  val (_, _ | @(oh, ol)) = $AR.or32(h, l, h0, l0)
  val y = whole(h0, l0)
  val extra = plus(plus(plus(bad(same(zh, zl, x)), bad(same(nh, nl, lnot x))),
    plus(bad(same(ah, al, x + y)), bad(same(xh, xl, x lxor y)))),
    plus(bad(same(dh, dl, x land y)), bad(same(oh, ol, x lor y))))
in amounts(0, extra) end

(* the next of a fixed pseudo-random sequence of halves *)
fn next (seed: int): [v:nat | v < 65536] int v =
  $AR.add_g1($AR.mul_g1($AR.low_byte($AR.div_int_int(seed, 7)), 256), $AR.low_byte($AR.div_int_int(seed, 3)))

fun walk {i:nat | i <= 3000} .<3000 - i>. (i: int i, failed: int): int =
  if i >= 3000 then failed
  else let
    val h = next(plus($AR.mul_int_int(i, 40503), 17))
    val l = next(plus($AR.mul_int_int(i, 9973), 5))
    val h0 = next(plus($AR.mul_int_int(i, 7919), 101))
    val l0 = next(plus($AR.mul_int_int(i, 31337), 7))
  in walk(i + 1, plus(failed, agrees(h, l, h0, l0))) end

implement main0 () = let
  val edges = plus(plus(plus(agrees(0, 0, 0, 0), agrees(65535, 65535, 65535, 65535)), plus(agrees(65535, 65535, 0, 1), agrees(32768, 0, 0, 1))),
    plus(plus(agrees(0, 1, 32768, 0), agrees(1, 0, 0, 65535)), agrees(43690, 21845, 21845, 43690)))
  val failed = plus(edges, walk(0, 0))
in
  if failed = 0 then println! ("word: all cases pass")
  else let val () = println! ("FAIL word: ", failed, " cases differ") in exit_void(1) end
end
