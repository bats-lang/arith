# arith

Integer arithmetic primitives for the [Bats](https://github.com/bats-lang) programming language.

## Features

- Basic arithmetic: `add_int_int`, `sub_int_int`, `mul_int_int`, `div_int_int`, `mod_int_int`
- Comparison: `eq_int_int`, `neq_int_int`, `lt_int_int`, `gt_int_int`, `gte_int_int`, `lt1_int_int`
- Bytes: `low_byte`, `byte_of_char` (proven in [0, 256), without a cast)
- Conversion: `g0_of_g1`

## Usage

```bats
#use arith as AR

val sum = $AR.add_int_int(1, 2)
val is_eq = $AR.eq_int_int(x, 0)
```

## API

See [docs/lib.md](docs/lib.md) for the full API reference.

## Safety

Safe library — no `$UNSAFE`, no `$extfcall`. Uses `mac#` bindings to ATS2 prelude functions.
