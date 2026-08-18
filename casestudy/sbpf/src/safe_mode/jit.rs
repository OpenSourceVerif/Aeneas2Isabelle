//! Safe model of the instruction-selection, byte-buffer, and relocation parts
//! of `crate::jit`.

#![allow(clippy::arithmetic_side_effects, missing_docs)]

use super::x86::{X86Instruction, X86Register};
use crate::ebpf;
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

/// Host registers used for the eleven general-purpose sBPF registers.
///
/// This is the same register assignment used by the production JIT.  The safe
/// model records only the code-generation choice and does not access the host
/// register file itself.
const REGISTER_MAP: [X86Register; 11] = [
    X86Register::RAX,
    X86Register::RSI,
    X86Register::RDX,
    X86Register::RCX,
    X86Register::R8,
    X86Register::R9,
    X86Register::RBX,
    X86Register::R12,
    X86Register::R13,
    X86Register::R14,
    X86Register::R15,
];

/// Scratch register used when an immediate does not fit in an x86 immediate
/// operand.
const REGISTER_SCRATCH: X86Register = X86Register::R11;

/// Arithmetic and bitwise operations emitted directly by the safe JIT model.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum AluOperation {
    Add,
    Subtract,
    Or,
    And,
    Xor,
}

/// Immediate shift operations emitted directly by the safe JIT model.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum ShiftOperation {
    Left,
    Right,
    ArithmeticRight,
}

/// Conditions supported by the safe branch encoder.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum JumpCondition {
    Equal,
    NotEqual,
    Greater,
    GreaterOrEqual,
    Less,
    LessOrEqual,
    SignedGreater,
    SignedGreaterOrEqual,
    SignedLess,
    SignedLessOrEqual,
}

/// A safe, verification-oriented subset of the instructions handled by the
/// production JIT.
///
/// Registers are sBPF register indices.  Jump destinations are instruction
/// indices rather than pointers into executable memory.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum JitInstruction {
    LoadImmediate {
        size: OperandSize,
        destination: usize,
        value: i64,
    },
    MoveRegister {
        size: OperandSize,
        source: usize,
        destination: usize,
    },
    AluImmediate {
        size: OperandSize,
        operation: AluOperation,
        destination: usize,
        value: i64,
    },
    AluRegister {
        size: OperandSize,
        operation: AluOperation,
        source: usize,
        destination: usize,
    },
    ShiftImmediate {
        size: OperandSize,
        operation: ShiftOperation,
        destination: usize,
        amount: u8,
    },
    ShiftRegister {
        size: OperandSize,
        operation: ShiftOperation,
        source: usize,
        destination: usize,
    },
    Jump {
        target_pc: usize,
    },
    JumpImmediate {
        size: OperandSize,
        condition: JumpCondition,
        destination: usize,
        value: i64,
        target_pc: usize,
    },
    JumpRegister {
        size: OperandSize,
        condition: JumpCondition,
        source: usize,
        destination: usize,
        target_pc: usize,
    },
    JumpTestImmediate {
        size: OperandSize,
        destination: usize,
        value: i64,
        target_pc: usize,
    },
    JumpTestRegister {
        size: OperandSize,
        source: usize,
        destination: usize,
        target_pc: usize,
    },
    Return,
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
    /// An sBPF register index was outside the supported register map.
    InvalidRegister,
    /// A branch target could not be represented as an instruction index.
    InvalidJumpTarget,
    /// The instruction uses an operand size not handled by the safe model.
    InvalidOperandSize,
    /// The instruction is outside the safe compiler subset.
    UnsupportedInstruction,
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

    /// Emits one instruction from the safe sBPF subset.
    pub fn emit_jit_instruction(
        &mut self,
        instruction: JitInstruction,
    ) -> Result<(), JitModelError> {
        match instruction {
            JitInstruction::LoadImmediate {
                size,
                destination,
                value,
            } => {
                let destination = mapped_register(destination)?;
                let value = match size {
                    OperandSize::S32 => (value as u32) as i64,
                    OperandSize::S64 => value,
                    _ => return Err(JitModelError::InvalidOperandSize),
                };
                self.emit_ins(&X86Instruction::load_immediate(destination, value));
            }
            JitInstruction::MoveRegister {
                size,
                source,
                destination,
            } => {
                let source = mapped_register(source)?;
                let destination = mapped_register(destination)?;
                self.emit_ins(&X86Instruction::mov(size, source, destination));
            }
            JitInstruction::AluImmediate {
                size,
                operation,
                destination,
                value,
            } => {
                let destination = mapped_register(destination)?;
                let (opcode, opcode_extension) = alu_encoding(operation);
                if value >= i32::MIN as i64 && value <= i32::MAX as i64 {
                    self.emit_ins(&X86Instruction::alu_immediate(
                        size,
                        0x81,
                        opcode_extension,
                        destination,
                        value,
                        None,
                    ));
                } else {
                    self.emit_ins(&X86Instruction::load_immediate(REGISTER_SCRATCH, value));
                    self.emit_ins(&X86Instruction::alu(
                        size,
                        opcode,
                        REGISTER_SCRATCH,
                        destination,
                        None,
                    ));
                }
            }
            JitInstruction::AluRegister {
                size,
                operation,
                source,
                destination,
            } => {
                let source = mapped_register(source)?;
                let destination = mapped_register(destination)?;
                let (opcode, _) = alu_encoding(operation);
                self.emit_ins(&X86Instruction::alu(
                    size,
                    opcode,
                    source,
                    destination,
                    None,
                ));
            }
            JitInstruction::ShiftImmediate {
                size,
                operation,
                destination,
                amount,
            } => {
                let destination = mapped_register(destination)?;
                self.emit_ins(&X86Instruction::alu_immediate(
                    size,
                    0xc1,
                    shift_opcode_extension(operation),
                    destination,
                    amount as i64,
                    None,
                ));
            }
            JitInstruction::ShiftRegister {
                size,
                operation,
                source,
                destination,
            } => {
                let source = mapped_register(source)?;
                let destination = mapped_register(destination)?;
                self.emit_register_shift(size, operation, source, destination);
            }
            JitInstruction::Jump { target_pc } => {
                let displacement = self.relative_to_target_pc(target_pc, 5)?;
                self.emit_ins(&X86Instruction::jump_immediate(displacement));
            }
            JitInstruction::JumpImmediate {
                size,
                condition,
                destination,
                value,
                target_pc,
            } => {
                let destination = mapped_register(destination)?;
                self.emit_ins(&X86Instruction::cmp_immediate(
                    size,
                    destination,
                    value,
                    None,
                ));
                let displacement = self.relative_to_target_pc(target_pc, 6)?;
                self.emit_ins(&X86Instruction::conditional_jump_immediate(
                    jump_opcode(condition),
                    displacement,
                ));
            }
            JitInstruction::JumpRegister {
                size,
                condition,
                source,
                destination,
                target_pc,
            } => {
                let source = mapped_register(source)?;
                let destination = mapped_register(destination)?;
                self.emit_ins(&X86Instruction::cmp(size, source, destination, None));
                let displacement = self.relative_to_target_pc(target_pc, 6)?;
                self.emit_ins(&X86Instruction::conditional_jump_immediate(
                    jump_opcode(condition),
                    displacement,
                ));
            }
            JitInstruction::JumpTestImmediate {
                size,
                destination,
                value,
                target_pc,
            } => {
                let destination = mapped_register(destination)?;
                self.emit_ins(&X86Instruction::test_immediate(
                    size,
                    destination,
                    value,
                    None,
                ));
                let displacement = self.relative_to_target_pc(target_pc, 6)?;
                self.emit_ins(&X86Instruction::conditional_jump_immediate(
                    jump_opcode(JumpCondition::NotEqual),
                    displacement,
                ));
            }
            JitInstruction::JumpTestRegister {
                size,
                source,
                destination,
                target_pc,
            } => {
                let source = mapped_register(source)?;
                let destination = mapped_register(destination)?;
                self.emit_ins(&X86Instruction::test(size, source, destination, None));
                let displacement = self.relative_to_target_pc(target_pc, 6)?;
                self.emit_ins(&X86Instruction::conditional_jump_immediate(
                    jump_opcode(JumpCondition::NotEqual),
                    displacement,
                ));
            }
            JitInstruction::Return => {
                self.emit_ins(&X86Instruction::return_near());
            }
        }
        Ok(())
    }

    fn emit_register_shift(
        &mut self,
        size: OperandSize,
        operation: ShiftOperation,
        source: X86Register,
        destination: X86Register,
    ) {
        let opcode_extension = shift_opcode_extension(operation);
        if matches!(size, OperandSize::S32) {
            self.emit_ins(&X86Instruction::mov(size, destination, destination));
        }
        if source == X86Register::RCX {
            self.emit_ins(&X86Instruction::alu_immediate(
                size,
                0xd3,
                opcode_extension,
                destination,
                0,
                None,
            ));
        } else if destination == X86Register::RCX {
            self.emit_ins(&X86Instruction::push(source, None));
            self.emit_ins(&X86Instruction::xchg(
                OperandSize::S64,
                source,
                X86Register::RCX,
                None,
            ));
            self.emit_ins(&X86Instruction::alu_immediate(
                size,
                0xd3,
                opcode_extension,
                source,
                0,
                None,
            ));
            self.emit_ins(&X86Instruction::mov(
                OperandSize::S64,
                source,
                X86Register::RCX,
            ));
            self.emit_ins(&X86Instruction::pop(source));
        } else {
            self.emit_ins(&X86Instruction::push(X86Register::RCX, None));
            self.emit_ins(&X86Instruction::mov(
                OperandSize::S64,
                source,
                X86Register::RCX,
            ));
            self.emit_ins(&X86Instruction::alu_immediate(
                size,
                0xd3,
                opcode_extension,
                destination,
                0,
                None,
            ));
            self.emit_ins(&X86Instruction::pop(X86Register::RCX));
        }
    }

    /// Compiles a sequence from the safe instruction subset into owned x86
    /// bytes and resolves all forward branches.
    pub fn compile(program: &[JitInstruction]) -> Result<Vec<u8>, JitModelError> {
        let mut compiler = Self::new(program.len(), 0);
        let mut pc = 0;
        while pc < program.len() {
            compiler.set_program_counter(pc)?;
            let instruction = *program
                .get(pc)
                .ok_or(JitModelError::InvalidProgramCounter)?;
            compiler.emit_jit_instruction(instruction)?;
            pc += 1;
        }
        compiler.resolve_jumps()?;
        Ok(compiler.text_section)
    }

    /// Compiles decoded instructions from sBPF's production instruction
    /// representation when they belong to the safe subset.
    pub fn compile_sbpf(program: &[ebpf::Insn]) -> Result<Vec<u8>, JitModelError> {
        let mut compiler = Self::new(program.len(), 0);
        let mut pc = 0;
        while pc < program.len() {
            compiler.set_program_counter(pc)?;
            let instruction = program
                .get(pc)
                .ok_or(JitModelError::InvalidProgramCounter)?;
            let instruction = lower_sbpf_instruction(pc, instruction)?;
            compiler.emit_jit_instruction(instruction)?;
            pc += 1;
        }
        compiler.resolve_jumps()?;
        Ok(compiler.text_section)
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

fn lower_sbpf_instruction(
    pc: usize,
    instruction: &ebpf::Insn,
) -> Result<JitInstruction, JitModelError> {
    let class = instruction.opc & ebpf::BPF_CLS_MASK;
    match class {
        ebpf::BPF_ALU32_LOAD => lower_alu_instruction(OperandSize::S32, instruction),
        ebpf::BPF_ALU64_STORE => lower_alu_instruction(OperandSize::S64, instruction),
        ebpf::BPF_JMP32 => lower_jump_instruction(OperandSize::S32, pc, instruction),
        ebpf::BPF_JMP64 => lower_jump_instruction(OperandSize::S64, pc, instruction),
        _ => Err(JitModelError::UnsupportedInstruction),
    }
}

fn lower_alu_instruction(
    size: OperandSize,
    instruction: &ebpf::Insn,
) -> Result<JitInstruction, JitModelError> {
    let operation = instruction.opc & ebpf::BPF_ALU_OP_MASK;
    let register_source = instruction.opc & ebpf::BPF_X != 0;
    let source = instruction.src as usize;
    let destination = instruction.dst as usize;

    match operation {
        ebpf::BPF_MOV => {
            if register_source {
                Ok(JitInstruction::MoveRegister {
                    size,
                    source,
                    destination,
                })
            } else {
                Ok(JitInstruction::LoadImmediate {
                    size,
                    destination,
                    value: instruction.imm,
                })
            }
        }
        ebpf::BPF_ADD | ebpf::BPF_SUB | ebpf::BPF_OR | ebpf::BPF_AND | ebpf::BPF_XOR => {
            let operation = match operation {
                ebpf::BPF_ADD => AluOperation::Add,
                ebpf::BPF_SUB => AluOperation::Subtract,
                ebpf::BPF_OR => AluOperation::Or,
                ebpf::BPF_AND => AluOperation::And,
                ebpf::BPF_XOR => AluOperation::Xor,
                _ => return Err(JitModelError::UnsupportedInstruction),
            };
            if register_source {
                Ok(JitInstruction::AluRegister {
                    size,
                    operation,
                    source,
                    destination,
                })
            } else {
                Ok(JitInstruction::AluImmediate {
                    size,
                    operation,
                    destination,
                    value: instruction.imm,
                })
            }
        }
        ebpf::BPF_LSH | ebpf::BPF_RSH | ebpf::BPF_ARSH => {
            let operation = match operation {
                ebpf::BPF_LSH => ShiftOperation::Left,
                ebpf::BPF_RSH => ShiftOperation::Right,
                ebpf::BPF_ARSH => ShiftOperation::ArithmeticRight,
                _ => return Err(JitModelError::UnsupportedInstruction),
            };
            if register_source {
                Ok(JitInstruction::ShiftRegister {
                    size,
                    operation,
                    source,
                    destination,
                })
            } else {
                Ok(JitInstruction::ShiftImmediate {
                    size,
                    operation,
                    destination,
                    amount: instruction.imm as u8,
                })
            }
        }
        _ => Err(JitModelError::UnsupportedInstruction),
    }
}

fn lower_jump_instruction(
    size: OperandSize,
    pc: usize,
    instruction: &ebpf::Insn,
) -> Result<JitInstruction, JitModelError> {
    let operation = instruction.opc & ebpf::BPF_ALU_OP_MASK;
    if matches!(size, OperandSize::S64) && operation == ebpf::BPF_EXIT {
        return Ok(JitInstruction::Return);
    }

    let target_pc = branch_target(pc, instruction.off)?;
    if matches!(size, OperandSize::S64) && operation == ebpf::BPF_JA {
        return Ok(JitInstruction::Jump { target_pc });
    }

    let register_source = instruction.opc & ebpf::BPF_X != 0;
    let source = instruction.src as usize;
    let destination = instruction.dst as usize;
    if operation == ebpf::BPF_JSET {
        if register_source {
            return Ok(JitInstruction::JumpTestRegister {
                size,
                source,
                destination,
                target_pc,
            });
        }
        return Ok(JitInstruction::JumpTestImmediate {
            size,
            destination,
            value: instruction.imm,
            target_pc,
        });
    }

    let condition = jump_condition_from_operation(operation)?;
    if register_source {
        Ok(JitInstruction::JumpRegister {
            size,
            condition,
            source,
            destination,
            target_pc,
        })
    } else {
        Ok(JitInstruction::JumpImmediate {
            size,
            condition,
            destination,
            value: instruction.imm,
            target_pc,
        })
    }
}

fn branch_target(pc: usize, offset: i16) -> Result<usize, JitModelError> {
    let target = (pc as i128) + (offset as i128) + 1;
    if target < 0 || target > usize::MAX as i128 {
        Err(JitModelError::InvalidJumpTarget)
    } else {
        Ok(target as usize)
    }
}

fn jump_condition_from_operation(operation: u8) -> Result<JumpCondition, JitModelError> {
    match operation {
        ebpf::BPF_JEQ => Ok(JumpCondition::Equal),
        ebpf::BPF_JNE => Ok(JumpCondition::NotEqual),
        ebpf::BPF_JGT => Ok(JumpCondition::Greater),
        ebpf::BPF_JGE => Ok(JumpCondition::GreaterOrEqual),
        ebpf::BPF_JLT => Ok(JumpCondition::Less),
        ebpf::BPF_JLE => Ok(JumpCondition::LessOrEqual),
        ebpf::BPF_JSGT => Ok(JumpCondition::SignedGreater),
        ebpf::BPF_JSGE => Ok(JumpCondition::SignedGreaterOrEqual),
        ebpf::BPF_JSLT => Ok(JumpCondition::SignedLess),
        ebpf::BPF_JSLE => Ok(JumpCondition::SignedLessOrEqual),
        _ => Err(JitModelError::UnsupportedInstruction),
    }
}

fn mapped_register(index: usize) -> Result<X86Register, JitModelError> {
    match REGISTER_MAP.get(index) {
        Some(register) => Ok(*register),
        None => Err(JitModelError::InvalidRegister),
    }
}

fn alu_encoding(operation: AluOperation) -> (u8, u8) {
    match operation {
        AluOperation::Add => (0x01, 0),
        AluOperation::Or => (0x09, 1),
        AluOperation::And => (0x21, 4),
        AluOperation::Subtract => (0x29, 5),
        AluOperation::Xor => (0x31, 6),
    }
}

fn shift_opcode_extension(operation: ShiftOperation) -> u8 {
    match operation {
        ShiftOperation::Left => 4,
        ShiftOperation::Right => 5,
        ShiftOperation::ArithmeticRight => 7,
    }
}

fn jump_opcode(condition: JumpCondition) -> u8 {
    match condition {
        JumpCondition::Equal => 0x84,
        JumpCondition::NotEqual => 0x85,
        JumpCondition::Greater => 0x87,
        JumpCondition::GreaterOrEqual => 0x83,
        JumpCondition::Less => 0x82,
        JumpCondition::LessOrEqual => 0x86,
        JumpCondition::SignedGreater => 0x8f,
        JumpCondition::SignedGreaterOrEqual => 0x8d,
        JumpCondition::SignedLess => 0x8c,
        JumpCondition::SignedLessOrEqual => 0x8e,
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

    #[test]
    fn compiles_arithmetic_and_return() {
        let code = JitCompilerModel::compile(&[
            JitInstruction::LoadImmediate {
                size: OperandSize::S64,
                destination: 0,
                value: 1,
            },
            JitInstruction::AluImmediate {
                size: OperandSize::S64,
                operation: AluOperation::Add,
                destination: 0,
                value: 2,
            },
            JitInstruction::Return,
        ])
        .unwrap();

        assert_eq!(
            code,
            [
                0xb8, 1, 0, 0, 0, // mov eax, 1
                0x48, 0x81, 0xc0, 2, 0, 0, 0,    // add rax, 2
                0xc3, // ret
            ]
        );
    }

    #[test]
    fn resolves_forward_branch_in_compiled_program() {
        let code = JitCompilerModel::compile(&[
            JitInstruction::Jump { target_pc: 2 },
            JitInstruction::LoadImmediate {
                size: OperandSize::S64,
                destination: 0,
                value: 7,
            },
            JitInstruction::Return,
        ])
        .unwrap();

        assert_eq!(
            code,
            [
                0xe9, 5, 0, 0, 0, // jump over the five-byte load
                0xb8, 7, 0, 0, 0, 0xc3,
            ]
        );
    }

    #[test]
    fn rejects_invalid_register() {
        let result = JitCompilerModel::compile(&[JitInstruction::LoadImmediate {
            size: OperandSize::S64,
            destination: 11,
            value: 0,
        }]);

        assert_eq!(result, Err(JitModelError::InvalidRegister));
    }

    #[test]
    fn compiles_decoded_sbpf_instructions() {
        let program = [
            ebpf::Insn {
                opc: ebpf::MOV64_IMM,
                dst: 0,
                imm: 1,
                ..ebpf::Insn::default()
            },
            ebpf::Insn {
                opc: ebpf::ADD64_IMM,
                dst: 0,
                imm: 2,
                ..ebpf::Insn::default()
            },
            ebpf::Insn {
                opc: ebpf::EXIT,
                ..ebpf::Insn::default()
            },
        ];

        assert_eq!(
            JitCompilerModel::compile_sbpf(&program),
            JitCompilerModel::compile(&[
                JitInstruction::LoadImmediate {
                    size: OperandSize::S64,
                    destination: 0,
                    value: 1,
                },
                JitInstruction::AluImmediate {
                    size: OperandSize::S64,
                    operation: AluOperation::Add,
                    destination: 0,
                    value: 2,
                },
                JitInstruction::Return,
            ])
        );
    }

    #[test]
    fn rejects_unsupported_memory_instruction() {
        let program = [ebpf::Insn {
            opc: ebpf::LD_DW_REG,
            ..ebpf::Insn::default()
        }];

        assert_eq!(
            JitCompilerModel::compile_sbpf(&program),
            Err(JitModelError::UnsupportedInstruction)
        );
    }

    #[test]
    fn compiles_decoded_forward_jump() {
        let program = [
            ebpf::Insn {
                opc: ebpf::JA,
                off: 1,
                ..ebpf::Insn::default()
            },
            ebpf::Insn {
                opc: ebpf::MOV64_IMM,
                dst: 0,
                imm: 7,
                ..ebpf::Insn::default()
            },
            ebpf::Insn {
                opc: ebpf::EXIT,
                ..ebpf::Insn::default()
            },
        ];

        assert_eq!(
            JitCompilerModel::compile_sbpf(&program).unwrap(),
            [
                0xe9, 5, 0, 0, 0, // jump over the five-byte load
                0xb8, 7, 0, 0, 0, 0xc3,
            ]
        );
    }
}
