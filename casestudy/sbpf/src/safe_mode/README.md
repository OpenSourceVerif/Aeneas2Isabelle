# sBPF JIT safe-mode case study

This directory is a verification-oriented copy of the JIT's safety-relevant
core. The production files `src/jit.rs` and `src/x86.rs` are intentionally
unchanged.

- `x86.rs` mirrors the production instruction constructors, but `encode`
  returns a `Vec<u8>` instead of writing into executable memory through a raw
  pointer.
- `jit.rs` models the text section, anchors, program-counter table, and jump
  relocations with owned vectors and integer offsets.
- Executable-memory allocation, memory-permission changes, conversion of bytes
  to function pointers, and invocation of generated code remain outside this
  directory. Those operations form the trusted `unsafe` boundary.

The focused Charon/Aeneas entry points avoid translating unrelated derived and
standard-library functions:

```sh
# Safe x86 encoder
charon cargo --preset aeneas \
  --start-from 'crate::safe_mode::x86::_::encode' \
  --dest-file /tmp/sbpf-safe-encode.llbc -- --lib
aeneas -backend isabelle \
  -dest /tmp/sbpf-safe-encode-isabelle \
  /tmp/sbpf-safe-encode.llbc

# Offset-based JIT model
charon cargo --preset aeneas \
  --start-from 'crate::safe_mode::jit::_::relative_to_anchor' \
  --dest-file /tmp/sbpf-safe-jit-model.llbc -- --lib
aeneas -backend isabelle \
  -dest /tmp/sbpf-safe-jit-model-isabelle \
  /tmp/sbpf-safe-jit-model.llbc
```

Run `cargo test safe_mode` to execute the encoding and relocation regression
tests.
