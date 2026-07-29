//! Safe x86-64 byte encoder extracted from `crate::x86`.
//!
//! The instruction constructors mirror the production encoder, while
//! [`X86Instruction::encode`] returns owned bytes instead of writing through a
//! raw pointer in executable memory.

#![allow(clippy::arithmetic_side_effects, missing_docs)]

use super::jit::OperandSize;

macro_rules! exclude_operand_sizes {
    ($size:expr, $($to_exclude:path)|+ $(,)?) => {
        debug_assert!(match $size {
            $($to_exclude)|+ => false,
            _ => true,
        });
    }
}

#[allow(dead_code, clippy::upper_case_acronyms)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
#[repr(u8)]
pub enum X86Register {
    RAX = 0,
    RCX = 1,
    RDX = 2,
    RBX = 3,
    RSP = 4,
    RBP = 5,
    RSI = 6,
    RDI = 7,
    R8 = 8,
    R9 = 9,
    R10 = 10,
    R11 = 11,
    R12 = 12,
    R13 = 13,
    R14 = 14,
    R15 = 15,
    MM0 = 16,
    MM1 = 17,
    MM2 = 18,
    MM3 = 19,
    MM4 = 20,
    MM5 = 21,
    MM6 = 22,
    MM7 = 23,
}
use X86Register::*;

pub const ARGUMENT_REGISTERS: [X86Register; 6] = [RDI, RSI, RDX, RCX, R8, R9];
pub const CALLER_SAVED_REGISTERS: [X86Register; 9] = [RAX, RCX, RDX, RSI, RDI, R8, R9, R10, R11];
pub const CALLEE_SAVED_REGISTERS: [X86Register; 6] = [RBP, RBX, R12, R13, R14, R15];

struct X86Rex {
    w: bool,
    r: bool,
    x: bool,
    b: bool,
}

struct X86ModRm {
    mode: u8,
    r: u8,
    m: u8,
}

struct X86Sib {
    scale: u8,
    index: u8,
    base: u8,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum X86IndirectAccess {
    /// `[second_operand + offset]`.
    Offset(i32),
    /// `[second_operand + offset + index << shift]`.
    OffsetIndexShift(i32, X86Register, u8),
}

#[allow(dead_code)]
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum FenceType {
    Load = 5,
    All = 6,
    Store = 7,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub struct X86Instruction {
    size: OperandSize,
    opcode_escape_sequence: u8,
    opcode: u8,
    modrm: bool,
    indirect: Option<X86IndirectAccess>,
    first_operand: u8,
    second_operand: u8,
    immediate_size: OperandSize,
    immediate: i64,
}

impl X86Instruction {
    pub const DEFAULT: Self = Self {
        size: OperandSize::S0,
        opcode_escape_sequence: 0,
        opcode: 0,
        modrm: true,
        indirect: None,
        first_operand: 0,
        second_operand: 0,
        immediate_size: OperandSize::S0,
        immediate: 0,
    };

    /// Encodes the instruction without writing through a raw pointer.
    pub fn encode(&self) -> Vec<u8> {
        debug_assert!(!matches!(self.size, OperandSize::S0));
        let mut output = Vec::new();
        let mut rex = X86Rex {
            w: matches!(self.size, OperandSize::S64),
            r: self.first_operand & 0b1000 != 0,
            x: false,
            b: self.second_operand & 0b1000 != 0,
        };
        let mut modrm = X86ModRm {
            mode: 0,
            r: self.first_operand & 0b111,
            m: self.second_operand & 0b111,
        };
        let mut sib = X86Sib {
            scale: 0,
            index: 0,
            base: 0,
        };
        let mut displacement_size = OperandSize::S0;
        let mut displacement = 0_i32;

        if self.modrm {
            match self.indirect {
                Some(X86IndirectAccess::Offset(offset)) => {
                    displacement = offset;
                    debug_assert_ne!(self.second_operand & 0b111, 4);
                    if (-128..=127).contains(&displacement)
                        || (displacement == 0 && self.second_operand & 0b111 == 5)
                    {
                        displacement_size = OperandSize::S8;
                        modrm.mode = 1;
                    } else {
                        displacement_size = OperandSize::S32;
                        modrm.mode = 2;
                    }
                }
                Some(X86IndirectAccess::OffsetIndexShift(offset, index, shift)) => {
                    displacement = offset;
                    if (-128..=127).contains(&displacement) {
                        displacement_size = OperandSize::S8;
                        modrm.mode = 1;
                    } else {
                        displacement_size = OperandSize::S32;
                        modrm.mode = 2;
                    }
                    modrm.m = 4;
                    rex.x = (index as u8) & 0b1000 != 0;
                    sib.scale = shift & 0b11;
                    sib.index = (index as u8) & 0b111;
                    sib.base = self.second_operand & 0b111;
                }
                None => modrm.mode = 3,
            }
        }

        if matches!(self.size, OperandSize::S16) {
            output.push(0x66);
        }
        let rex_byte =
            ((rex.w as u8) << 3) | ((rex.r as u8) << 2) | ((rex.x as u8) << 1) | (rex.b as u8);
        if rex_byte != 0 {
            output.push(0x40 | rex_byte);
        }
        match self.opcode_escape_sequence {
            1 => output.push(0x0f),
            2 => output.extend_from_slice(&0x0f38_u16.to_le_bytes()),
            3 => output.extend_from_slice(&0x0f3a_u16.to_le_bytes()),
            _ => {}
        }
        output.push(self.opcode);
        if self.modrm {
            output.push((modrm.mode << 6) | (modrm.r << 3) | modrm.m);
            let sib_byte = (sib.scale << 6) | (sib.index << 3) | sib.base;
            if sib_byte != 0 {
                output.push(sib_byte);
            }
            emit_variable_length(&mut output, displacement_size, displacement as u64);
        }
        emit_variable_length(&mut output, self.immediate_size, self.immediate as u64);
        output
    }

    pub const fn alu_escaped(
        size: OperandSize,
        opcode_escape_sequence: u8,
        opcode: u8,
        source: X86Register,
        destination: X86Register,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S8 | OperandSize::S16);
        Self {
            size,
            opcode_escape_sequence,
            opcode,
            first_operand: source as u8,
            second_operand: destination as u8,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn alu_immediate_escaped(
        size: OperandSize,
        opcode_escape_sequence: u8,
        opcode: u8,
        opcode_extension: u8,
        destination: X86Register,
        immediate: i64,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S8 | OperandSize::S16);
        Self {
            size,
            opcode_escape_sequence,
            opcode,
            first_operand: opcode_extension,
            second_operand: destination as u8,
            immediate_size: match opcode {
                0xc1 => OperandSize::S8,
                0x81 => OperandSize::S32,
                0xf7 if opcode_extension == 0 => OperandSize::S32,
                _ => OperandSize::S0,
            },
            immediate,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn alu(
        size: OperandSize,
        opcode: u8,
        source: X86Register,
        destination: X86Register,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        Self::alu_escaped(size, 0, opcode, source, destination, indirect)
    }

    pub const fn alu_immediate(
        size: OperandSize,
        opcode: u8,
        opcode_extension: u8,
        destination: X86Register,
        immediate: i64,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        Self::alu_immediate_escaped(
            size,
            0,
            opcode,
            opcode_extension,
            destination,
            immediate,
            indirect,
        )
    }

    pub const fn mov(size: OperandSize, source: X86Register, destination: X86Register) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S8 | OperandSize::S16);
        Self {
            size,
            opcode: 0x89,
            first_operand: source as u8,
            second_operand: destination as u8,
            ..Self::DEFAULT
        }
    }

    pub const fn mov_with_sign_extension(
        size: OperandSize,
        source: X86Register,
        destination: X86Register,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S8 | OperandSize::S16);
        Self {
            size,
            opcode: 0x63,
            first_operand: destination as u8,
            second_operand: source as u8,
            ..Self::DEFAULT
        }
    }

    pub const fn mov_mmx(size: OperandSize, source: X86Register, destination: X86Register) -> Self {
        exclude_operand_sizes!(
            size,
            OperandSize::S0 | OperandSize::S8 | OperandSize::S16 | OperandSize::S32
        );
        if (destination as u8) & 16 != 0 {
            Self {
                size,
                opcode_escape_sequence: 1,
                opcode: if (source as u8) & 16 != 0 { 0x6f } else { 0x6e },
                first_operand: (destination as u8) & 0xf,
                second_operand: (source as u8) & 0xf,
                ..Self::DEFAULT
            }
        } else {
            Self {
                size,
                opcode_escape_sequence: 1,
                opcode: 0x7e,
                first_operand: (source as u8) & 0xf,
                second_operand: (destination as u8) & 0xf,
                ..Self::DEFAULT
            }
        }
    }

    pub const fn cmov(
        size: OperandSize,
        condition: u8,
        source: X86Register,
        destination: X86Register,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S8 | OperandSize::S16);
        Self {
            size,
            opcode_escape_sequence: 1,
            opcode: condition,
            first_operand: destination as u8,
            second_operand: source as u8,
            ..Self::DEFAULT
        }
    }

    pub const fn xchg(
        size: OperandSize,
        source: X86Register,
        destination: X86Register,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(
            size,
            OperandSize::S0 | OperandSize::S8 | OperandSize::S16 | OperandSize::S32
        );
        Self {
            size,
            opcode: 0x87,
            first_operand: source as u8,
            second_operand: destination as u8,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn bswap(size: OperandSize, destination: X86Register) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S8);
        match size {
            OperandSize::S16 => Self {
                size,
                opcode: 0xc1,
                second_operand: destination as u8,
                immediate_size: OperandSize::S8,
                immediate: 8,
                ..Self::DEFAULT
            },
            OperandSize::S32 | OperandSize::S64 => Self {
                size,
                opcode_escape_sequence: 1,
                opcode: 0xc8 | ((destination as u8) & 0b111),
                modrm: false,
                second_operand: destination as u8,
                ..Self::DEFAULT
            },
            _ => panic!("invalid operand size"),
        }
    }

    pub const fn test(
        size: OperandSize,
        source: X86Register,
        destination: X86Register,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0);
        Self {
            size,
            opcode: if matches!(size, OperandSize::S8) {
                0x84
            } else {
                0x85
            },
            first_operand: source as u8,
            second_operand: destination as u8,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn test_immediate(
        size: OperandSize,
        destination: X86Register,
        immediate: i64,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0);
        Self {
            size,
            opcode: if matches!(size, OperandSize::S8) {
                0xf6
            } else {
                0xf7
            },
            first_operand: 0,
            second_operand: destination as u8,
            immediate_size: if matches!(size, OperandSize::S64) {
                OperandSize::S32
            } else {
                size
            },
            immediate,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn cmp(
        size: OperandSize,
        source: X86Register,
        destination: X86Register,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0);
        Self {
            size,
            opcode: if matches!(size, OperandSize::S8) {
                0x38
            } else {
                0x39
            },
            first_operand: source as u8,
            second_operand: destination as u8,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn cmp_immediate(
        size: OperandSize,
        destination: X86Register,
        immediate: i64,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0);
        Self {
            size,
            opcode: if matches!(size, OperandSize::S8) {
                0x80
            } else {
                0x81
            },
            first_operand: 7,
            second_operand: destination as u8,
            immediate_size: if matches!(size, OperandSize::S64) {
                OperandSize::S32
            } else {
                size
            },
            immediate,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn lea(
        size: OperandSize,
        source: X86Register,
        destination: X86Register,
        indirect: Option<X86IndirectAccess>,
    ) -> Self {
        exclude_operand_sizes!(
            size,
            OperandSize::S0 | OperandSize::S8 | OperandSize::S16 | OperandSize::S32
        );
        Self {
            size,
            opcode: 0x8d,
            first_operand: destination as u8,
            second_operand: source as u8,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn sign_extend_rax_rdx(size: OperandSize) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S8 | OperandSize::S16);
        Self {
            size,
            opcode: 0x99,
            modrm: false,
            ..Self::DEFAULT
        }
    }

    pub const fn load(
        size: OperandSize,
        source: X86Register,
        destination: X86Register,
        indirect: X86IndirectAccess,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0);
        Self {
            size: if matches!(size, OperandSize::S64) {
                OperandSize::S64
            } else {
                OperandSize::S32
            },
            opcode_escape_sequence: match size {
                OperandSize::S8 | OperandSize::S16 => 1,
                _ => 0,
            },
            opcode: match size {
                OperandSize::S8 => 0xb6,
                OperandSize::S16 => 0xb7,
                _ => 0x8b,
            },
            first_operand: destination as u8,
            second_operand: source as u8,
            indirect: Some(indirect),
            ..Self::DEFAULT
        }
    }

    pub const fn store(
        size: OperandSize,
        source: X86Register,
        destination: X86Register,
        indirect: X86IndirectAccess,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0);
        Self {
            size,
            opcode: if matches!(size, OperandSize::S8) {
                0x88
            } else {
                0x89
            },
            first_operand: source as u8,
            second_operand: destination as u8,
            indirect: Some(indirect),
            ..Self::DEFAULT
        }
    }

    pub const fn load_immediate(destination: X86Register, immediate: i64) -> Self {
        let mut size = OperandSize::S64;
        if immediate >= 0 {
            if immediate <= u32::MAX as i64 {
                size = OperandSize::S32;
            }
        } else if immediate >= i32::MIN as i64 {
            return Self {
                size: OperandSize::S64,
                opcode: 0xc7,
                second_operand: destination as u8,
                immediate_size: OperandSize::S32,
                immediate,
                ..Self::DEFAULT
            };
        }
        Self {
            size,
            opcode: 0xb8 | ((destination as u8) & 0b111),
            modrm: false,
            second_operand: destination as u8,
            immediate_size: size,
            immediate,
            ..Self::DEFAULT
        }
    }

    pub const fn store_immediate(
        size: OperandSize,
        destination: X86Register,
        indirect: X86IndirectAccess,
        immediate: i64,
    ) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0);
        Self {
            size,
            opcode: if matches!(size, OperandSize::S8) {
                0xc6
            } else {
                0xc7
            },
            second_operand: destination as u8,
            indirect: Some(indirect),
            immediate_size: if matches!(size, OperandSize::S64) {
                OperandSize::S32
            } else {
                size
            },
            immediate,
            ..Self::DEFAULT
        }
    }

    pub const fn push_immediate(size: OperandSize, immediate: i32) -> Self {
        exclude_operand_sizes!(size, OperandSize::S0 | OperandSize::S16);
        Self {
            size,
            opcode: if matches!(size, OperandSize::S8) {
                0x6a
            } else {
                0x68
            },
            modrm: false,
            immediate_size: if matches!(size, OperandSize::S64) {
                OperandSize::S32
            } else {
                size
            },
            immediate: immediate as i64,
            ..Self::DEFAULT
        }
    }

    pub const fn push(source: X86Register, indirect: Option<X86IndirectAccess>) -> Self {
        if indirect.is_none() {
            Self {
                size: OperandSize::S32,
                opcode: 0x50 | ((source as u8) & 0b111),
                modrm: false,
                second_operand: source as u8,
                ..Self::DEFAULT
            }
        } else {
            Self {
                size: OperandSize::S64,
                opcode: 0xff,
                first_operand: 6,
                second_operand: source as u8,
                indirect,
                ..Self::DEFAULT
            }
        }
    }

    pub const fn pop(destination: X86Register) -> Self {
        Self {
            size: OperandSize::S32,
            opcode: 0x58 | ((destination as u8) & 0b111),
            modrm: false,
            second_operand: destination as u8,
            ..Self::DEFAULT
        }
    }

    pub const fn conditional_jump_immediate(opcode: u8, relative_destination: i32) -> Self {
        Self {
            size: OperandSize::S32,
            opcode_escape_sequence: 1,
            opcode,
            modrm: false,
            immediate_size: OperandSize::S32,
            immediate: relative_destination as i64,
            ..Self::DEFAULT
        }
    }

    pub const fn jump_immediate(relative_destination: i32) -> Self {
        Self {
            size: OperandSize::S32,
            opcode: 0xe9,
            modrm: false,
            immediate_size: OperandSize::S32,
            immediate: relative_destination as i64,
            ..Self::DEFAULT
        }
    }

    pub const fn jump_reg(destination: X86Register, indirect: Option<X86IndirectAccess>) -> Self {
        Self {
            size: OperandSize::S64,
            opcode: 0xff,
            first_operand: 4,
            second_operand: destination as u8,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn call_immediate(relative_destination: i32) -> Self {
        Self {
            size: OperandSize::S32,
            opcode: 0xe8,
            modrm: false,
            immediate_size: OperandSize::S32,
            immediate: relative_destination as i64,
            ..Self::DEFAULT
        }
    }

    pub const fn call_reg(destination: X86Register, indirect: Option<X86IndirectAccess>) -> Self {
        Self {
            size: OperandSize::S64,
            opcode: 0xff,
            first_operand: 2,
            second_operand: destination as u8,
            indirect,
            ..Self::DEFAULT
        }
    }

    pub const fn return_near() -> Self {
        Self {
            size: OperandSize::S32,
            opcode: 0xc3,
            modrm: false,
            ..Self::DEFAULT
        }
    }

    pub const fn noop() -> Self {
        Self {
            size: OperandSize::S32,
            opcode: 0x90,
            modrm: false,
            ..Self::DEFAULT
        }
    }

    pub const fn interrupt(immediate: u8) -> Self {
        if immediate == 3 {
            Self {
                size: OperandSize::S32,
                opcode: 0xcc,
                modrm: false,
                ..Self::DEFAULT
            }
        } else {
            Self {
                size: OperandSize::S32,
                opcode: 0xcd,
                modrm: false,
                immediate_size: OperandSize::S8,
                immediate: immediate as i64,
                ..Self::DEFAULT
            }
        }
    }

    pub const fn cycle_count() -> Self {
        Self {
            size: OperandSize::S32,
            opcode_escape_sequence: 1,
            opcode: 0x31,
            modrm: false,
            ..Self::DEFAULT
        }
    }

    pub const fn fence(fence_type: FenceType) -> Self {
        Self {
            size: OperandSize::S32,
            opcode_escape_sequence: 1,
            opcode: 0xae,
            first_operand: fence_type as u8,
            ..Self::DEFAULT
        }
    }
}

fn emit_variable_length(output: &mut Vec<u8>, size: OperandSize, data: u64) {
    let bytes = data.to_le_bytes();
    match size {
        OperandSize::S0 => {}
        OperandSize::S8 => output.extend_from_slice(&bytes[..1]),
        OperandSize::S16 => output.extend_from_slice(&bytes[..2]),
        OperandSize::S32 => output.extend_from_slice(&bytes[..4]),
        OperandSize::S64 => output.extend_from_slice(&bytes),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn encodes_register_move() {
        let instruction = X86Instruction::mov(OperandSize::S64, RAX, RBX);
        assert_eq!(instruction.encode(), vec![0x48, 0x89, 0xc3]);
    }

    #[test]
    fn encodes_positive_immediate_with_shorter_form() {
        let instruction = X86Instruction::load_immediate(RAX, 1);
        assert_eq!(instruction.encode(), vec![0xb8, 1, 0, 0, 0]);
    }

    #[test]
    fn encodes_indirect_load_with_displacement() {
        let instruction =
            X86Instruction::load(OperandSize::S64, RBP, R9, X86IndirectAccess::Offset(-8));
        assert_eq!(instruction.encode(), vec![0x4c, 0x8b, 0x4d, 0xf8]);
    }
}
