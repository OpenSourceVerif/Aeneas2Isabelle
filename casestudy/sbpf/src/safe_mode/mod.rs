//! Safe, executable models of the parts of the JIT that are suitable for
//! translation with Charon and Aeneas.
//!
//! This module intentionally does not allocate executable memory or call
//! generated machine code.  The production JIT remains the trusted boundary
//! for those operations.

pub mod jit;
pub mod x86;

pub use jit::{JitCompilerModel, JitModelError, OperandSize};
