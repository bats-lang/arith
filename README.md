# arith

Integer arithmetic primitives for the [Bats](https://github.com/bats-lang) programming language.

## API

See [docs/lib.md](docs/lib.md) for the full API reference.

## Safety

`unsafe = true` for exactly one `$UNSAFE` block of three trusted primitives on `word32` (`word32_rotr`, `word32_pack`, `word32_byte`); see CLAUDE.md. Everything else uses `mac#` bindings to ATS2 prelude functions and proofs, no `$extfcall`.
