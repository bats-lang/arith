#include "share/atspre_staload.hats"
#use arith as AR

(* The fast shift (shr_fast: at most five constant-time steps on the
   halves) is compared with the standard's own operator on C's 32-bit
   unsigned int (FIPS 180-4, section 3.2: SHR^n(x) = x >> n), and with the
   specification's loop of single bits (shr), for every amount 0 to 31 on
   edge words and a fixed pseudo-random sequence; and each step alone (by
   1, 2, 4, 8 and 16 bits) the same. Exits 1 on any mismatch. *)
fn whole (h: int, l: int): uint =
  (g0int2uint_int_uint(h) << 16) lor g0int2uint_int_uint(l)

fn bad(ok: bool): int = if ok then 0 else 1

fn plus(a: int, b: int): int = $AR.add_int_int(a, b)

fn same {h2,l2:nat | h2 < 65536; l2 < 65536} (h2: int h2, l2: int l2, want: uint): bool =
  whole(h2, l2) = want

fn shifted {n:nat | n < 32} (x: uint, n: int n): uint = x >> n

fn steps_agree {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int = let
  val x = whole(h, l)
  val (_ | @(h1, l1)) = $AR.shr_step_1(h, l)
  val (_ | @(h2, l2)) = $AR.shr_step_2(h, l)
  val (_ | @(h4, l4)) = $AR.shr_step_4(h, l)
  val (_ | @(h8, l8)) = $AR.shr_step_8(h, l)
  val (_ | @(h16, l16)) = $AR.shr_step_16(h, l)
in plus(plus(plus(bad(same(h1, l1, shifted(x, 1))), bad(same(h2, l2, shifted(x, 2)))),
  plus(bad(same(h4, l4, shifted(x, 4))), bad(same(h8, l8, shifted(x, 8))))),
  bad(same(h16, l16, shifted(x, 16)))) end

fn agrees {h,l:nat | h < 65536; l < 65536} (h: int h, l: int l): int = let
  val x = whole(h, l)
  fun amounts {n:nat | n <= 32} .<32 - n>. (n: int n, failed: int): int =
    if n >= 32 then failed
    else let
      val (_ | @(fh, fl)) = $AR.shr_fast(n, h, l)
      val (_ | @(sh, sl)) = $AR.shr(n, h, l)
      val fast_ok = same(fh, fl, shifted(x, n))
      val slow_ok = (fh = sh) && (fl = sl)
    in amounts(n + 1, plus(failed, plus(bad(fast_ok), bad(slow_ok)))) end
in amounts(0, steps_agree(h, l)) end

(* the next of a fixed pseudo-random sequence of halves *)
fn next (seed: int): [v:nat | v < 65536] int v =
  $AR.add_g1($AR.mul_g1($AR.low_byte($AR.div_int_int(seed, 7)), 256), $AR.low_byte($AR.div_int_int(seed, 3)))

fun walk {i:nat | i <= 20000} .<20000 - i>. (i: int i, failed: int): int =
  if i >= 20000 then failed
  else let
    val h = next(plus($AR.mul_int_int(i, 40503), 17))
    val l = next(plus($AR.mul_int_int(i, 9973), 5))
  in walk(i + 1, plus(failed, agrees(h, l))) end

implement main0 () = let
  val edges = plus(plus(plus(agrees(0, 0), agrees(65535, 65535)), plus(agrees(0, 1), agrees(32768, 0))),
    plus(plus(agrees(1, 0), agrees(0, 32768)), plus(agrees(255, 65280), agrees(43690, 21845))))
  val failed = plus(edges, walk(0, 0))
in
  if failed = 0 then println! ("fast_shr: all cases pass")
  else let val () = println! ("FAIL fast_shr: ", failed, " cases differ") in exit_void(1) end
end
