#include "share/atspre_staload.hats"
#use arith as AR

(* xor_g1 is the C operator under the specification XOR (bit by bit,
   from the least significant); here the specification is run as a loop
   and compared, for every pair of numbers under 4096, for pairs spread
   over all 16 bits, and for the edges. Exits 1 on any mismatch. *)
fun reference {w:nat} .<w>. (a: int, b: int, w: int w, weight: int): int =
  if w <= 0 then 0
  else let
    val bit_a = $AR.mod_int_int(a, 2)
    val bit_b = $AR.mod_int_int(b, 2)
    val here = (if bit_a = bit_b then 0 else weight)
  in $AR.add_int_int(here, reference($AR.div_int_int(a, 2), $AR.div_int_int(b, 2), w - 1, $AR.mul_int_int(weight, 2))) end

fn agrees {a,b:nat | a < 65536; b < 65536} (a: int a, b: int b): bool = let
  val (_ | got) = $AR.xor_g1(a, b)
in got = reference(a, b, 16, 1) end

fun grid {a,b:nat | a <= 4096; b <= 4096} .<4096 - a, 4096 - b>. (a: int a, b: int b, failed: int): int =
  if a >= 4096 then failed
  else if b >= 4096 then grid(a + 1, 0, failed)
  else grid(a, b + 1, (if agrees(a, b) then failed else $AR.add_int_int(failed, 1)))

fun spread {i,j:nat | i <= 262; j <= 262} .<262 - i, 262 - j>. (i: int i, j: int j, failed: int): int =
  if i >= 262 then failed
  else if j >= 262 then spread(i + 1, 0, failed)
  else spread(i, j + 1, (if agrees(251 * i, 251 * j) then failed else $AR.add_int_int(failed, 1)))

implement main0 () = let
  val edges = (if agrees(65535, 65535) then 0 else 1) + (if agrees(65535, 0) then 0 else 1)
  val more = (if agrees(32768, 32767) then 0 else 1) + (if agrees(43690, 21845) then 0 else 1)
  val failed = $AR.add_int_int($AR.add_int_int(grid(0, 0, 0), spread(0, 0, 0)), $AR.add_int_int(edges, more))
in
  if $AR.eq_int_int(failed, 0) then println! ("xor: all cases pass")
  else let val () = println! ("FAIL xor: ", failed, " pairs differ") in exit_void(1) end
end
