#include "share/atspre_staload.hats"
#use arith as AR

(* low_byte(x) must equal x land 255 for every byte value and for
   values outside [0, 256). Exits 1 on any mismatch. *)
fun all_bytes {i:nat | i <= 256} .<256 - i>. (i: int i): bool =
  if i >= 256 then true
  else if $AR.low_byte(i) != i then let
    val () = println! ("FAIL low_byte(", i, ") = ", $AR.low_byte(i))
  in false end
  else all_bytes(i + 1)

fn check (name: string, got: int, want: int): bool = let
  val ok = (got = want)
  val () = (if ok then () else println! ("FAIL ", name, ": got ", got, ", want ", want))
in ok end

implement main0 () = let
  val r1 = all_bytes(0)
  val r2 = check("256", $AR.low_byte(256), 0)
  val r3 = check("-1", $AR.low_byte(~1), 255)
  val r4 = check("0x1234", $AR.low_byte(4660), 52)
  val r5 = check("byte_of_char A", $AR.byte_of_char('A'), 65)
  val r6 = check("byte_of_char \\377", $AR.byte_of_char('\377'), 255)
in
  if r1 && r2 && r3 && r4 && r5 && r6 then println! ("low_byte: all cases pass")
  else exit_void(1)
end
