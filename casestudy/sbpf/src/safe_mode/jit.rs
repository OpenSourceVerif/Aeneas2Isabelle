//! Safe model of the byte-buffer and relocation part of `crate::jit`.

#![allow(clippy::arithmetic_side_effects)]

use super::x86::X86Instruction;
use std::convert::TryFrom;

/// Bit width of an instruction operand.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum OperandSize {
    /// No operand.
    S0 = 0,
    /// 8-bit operand.
    S8 = 8,
    /// 16-bit operand.
    S16 = 16,
    /// 32-bit operand.
    S32 = 32,
    /// 64-bit operand.
    S64 = 64,
}

/// A pending relative jump represented only with indices.
#[derive(Clone, Debug, PartialEq, Eq)]
struct JumpModel {
    /// Offset of the four-byte relative displacement.
    location: usize,
    /// VM program counter to which the jump points.
    target_pc: usize,
}

/// Errors detected by the safe JIT model.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JitModelError {
    /// An anchor index was outside the configured anchor table.
    InvalidAnchor,
    /// A program-counter index was outside the configured PC table.
    InvalidProgramCounter,
    /// A requested anchor has not been set yet.
    AnchorNotSet,
    /// A requested program-counter offset has not been set yet.
    ProgramCounterNotSet,
    /// A relative displacement does not fit in an x86 `i32`.
    RelativeOffsetOutOfRange,
    /// A relocation does not point to four bytes in the text section.
    InvalidRelocation,
}

/// Safe model of the state used while constructing JIT machine code.
///
/// The model owns a growable byte vector and represents every address as a
/// byte offset.  It deliberately has no API for changing memory permissions
/// or invoking the resulting bytes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JitCompilerModel {
    text_section: Vec<u8>,
    pc_section: Vec<Option<usize>>,
    text_section_jumps: Vec<JumpModel>,
    anchors: Vec<Option<usize>>,
}

impl JitCompilerModel {
    /// Creates an empty model with fixed-size PC and anchor tables.
    pub fn new(program_counter_count: usize, anchor_count: usize) -> Self {
        Self {
            text_section: Vec::new(),
            pc_section: vec![None; program_counter_count],
            text_section_jumps: Vec::new(),
            anchors: vec![None; anchor_count],
        }
    }

    /// Returns the generated machine-code bytes.
    pub fn text_section(&self) -> &[u8] {
        &self.text_section
    }

    /// Returns the current byte offset in the text section.
    pub fn offset_in_text_section(&self) -> usize {
        self.text_section.len()
    }

    /// Appends one byte to the text section.
    pub fn emit_byte(&mut self, byte: u8) {
        self.text_section.push(byte);
    }

    /// Appends a sequence of bytes to the text section.
    pub fn emit_bytes(&mut self, bytes: &[u8]) {
        self.text_section.extend_from_slice(bytes);
    }

    /// Emits the least-significant bytes of `data` in little-endian order.
    pub fn emit_variable_length(&mut self, size: OperandSize, data: u64) {
        let bytes = data.to_le_bytes();
        match size {
            OperandSize::S0 => {}
            OperandSize::S8 => self.emit_bytes(&bytes[..1]),
            OperandSize::S16 => self.emit_bytes(&bytes[..2]),
            OperandSize::S32 => self.emit_bytes(&bytes[..4]),
            OperandSize::S64 => self.emit_bytes(&bytes),
        }
    }

    /// Encodes and appends an x86 instruction.
    pub fn emit_ins(&mut self, instruction: &X86Instruction) {
        self.emit_bytes(&instruction.encode());
    }

    /// Records the current byte offset for a VM program counter.
    pub fn set_program_counter(&mut self, pc: usize) -> Result<(), JitModelError> {
        let slot = self
            .pc_section
            .get_mut(pc)
            .ok_or(JitModelError::InvalidProgramCounter)?;
        *slot = Some(self.text_section.len());
        Ok(())
    }

    /// Records the current byte offset for an internal JIT anchor.
    pub fn set_anchor(&mut self, anchor: usize) -> Result<(), JitModelError> {
        let slot = self
            .anchors
            .get_mut(anchor)
            .ok_or(JitModelError::InvalidAnchor)?;
        *slot = Some(self.text_section.len());
        Ok(())
    }

    /// Computes an x86 relative displacement from the next instruction.
    pub fn relative_to_anchor(
        &self,
        anchor: usize,
        instruction_length: usize,
    ) -> Result<i32, JitModelError> {
        let destination = self
            .anchors
            .get(anchor)
            .ok_or(JitModelError::InvalidAnchor)?
            .ok_or(JitModelError::AnchorNotSet)?;
        let instruction_end = self
            .text_section
            .len()
            .checked_add(instruction_length)
            .ok_or(JitModelError::RelativeOffsetOutOfRange)?;
        relative_offset(destination, instruction_end)
    }

    /// Computes a relative displacement or records a forward relocation.
    ///
    /// `instruction_length` must include the trailing four-byte displacement,
    /// as it does in the production JIT.
    pub fn relative_to_target_pc(
        &mut self,
        target_pc: usize,
        instruction_length: usize,
    ) -> Result<i32, JitModelError> {
        let destination = *self
            .pc_section
            .get(target_pc)
            .ok_or(JitModelError::InvalidProgramCounter)?;
        let instruction_end = self
            .text_section
            .len()
            .checked_add(instruction_length)
            .ok_or(JitModelError::RelativeOffsetOutOfRange)?;
        match destination {
            Some(destination) => relative_offset(destination, instruction_end),
            None => {
                let location = instruction_end
                    .checked_sub(4)
                    .ok_or(JitModelError::InvalidRelocation)?;
                self.text_section_jumps.push(JumpModel {
                    location,
                    target_pc,
                });
                Ok(0)
            }
        }
    }

    /// Applies every recorded forward-jump relocation.
    pub fn resolve_jumps(&mut self) -> Result<(), JitModelError> {
        for jump in &self.text_section_jumps {
            let destination = self
                .pc_section
                .get(jump.target_pc)
                .ok_or(JitModelError::InvalidProgramCounter)?
                .ok_or(JitModelError::ProgramCounterNotSet)?;
            let instruction_end = jump
                .location
                .checked_add(4)
                .ok_or(JitModelError::InvalidRelocation)?;
            let displacement = relative_offset(destination, instruction_end)?;
            let relocation = self
                .text_section
                .get_mut(jump.location..instruction_end)
                .ok_or(JitModelError::InvalidRelocation)?;
            relocation.copy_from_slice(&displacement.to_le_bytes());
        }
        self.text_section_jumps.clear();
        Ok(())
    }
}

/// Converts the mathematical difference of two offsets to an x86 displacement.
fn relative_offset(destination: usize, instruction_end: usize) -> Result<i32, JitModelError> {
    let difference = (destination as i128) - (instruction_end as i128);
    i32::try_from(difference).map_err(|_| JitModelError::RelativeOffsetOutOfRange)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::safe_mode::x86::X86Instruction;

    #[test]
    fn resolves_forward_jump_using_offsets() {
        let mut jit = JitCompilerModel::new(2, 0);
        jit.set_program_counter(0).unwrap();

        let displacement = jit.relative_to_target_pc(1, 5).unwrap();
        jit.emit_ins(&X86Instruction::jump_immediate(displacement));
        jit.emit_byte(0x90);
        jit.set_program_counter(1).unwrap();
        jit.resolve_jumps().unwrap();

        assert_eq!(jit.text_section(), &[0xe9, 1, 0, 0, 0, 0x90]);
    }

    #[test]
    fn computes_backward_anchor_displacement() {
        let mut jit = JitCompilerModel::new(0, 1);
        jit.set_anchor(0).unwrap();
        jit.emit_byte(0x90);

        assert_eq!(jit.relative_to_anchor(0, 5), Ok(-6));
    }
}
