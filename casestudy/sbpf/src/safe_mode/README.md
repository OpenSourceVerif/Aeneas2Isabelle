# sBPF JIT safe-mode case study

This directory is a verification-oriented copy of the JIT's safety-relevant
core. The production files `src/jit.rs` and `src/x86.rs` are intentionally
unchanged.

- `x86.rs` mirrors the production instruction constructors, but `encode`
  returns a `Vec<u8>` instead of writing into executable memory through a raw
  pointer.
- `jit.rs` accepts the production `ebpf::Insn` representation and translates a
  safe instruction subset into x86 bytes. It covers register mapping, moves,
  arithmetic and bitwise operations, immediate and register shifts,
  conditional and unconditional branches, the text section, anchors, the
  program-counter table, and jump relocation. All addresses are represented by
  vector indices and integer offsets.
- Executable-memory allocation, memory-permission changes, conversion of bytes
  to function pointers, and invocation of generated code remain outside this
  directory. Runtime memory translation, calls, instruction metering,
  randomized constant sanitization, and multiplication or division subroutines
  are also not modeled. Those operations either depend on the trusted `unsafe`
  boundary or require additional semantic support.

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
  --start-from 'crate::safe_mode::jit::_::compile_sbpf' \
  --dest-file /tmp/sbpf-safe-jit-model.llbc -- --lib
aeneas -backend isabelle \
  -dest /tmp/sbpf-safe-jit-model-isabelle \
  /tmp/sbpf-safe-jit-model.llbc
```

Run `cargo test safe_mode` to execute the encoding and relocation regression
tests.
