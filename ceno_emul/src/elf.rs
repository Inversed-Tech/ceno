// Based on: https://github.com/risc0/risc0/blob/6b6daeafa1545984aa28581fca56d9ef13dcbae6/risc0/binfmt/src/elf.rs
//
// Copyright 2024 RISC Zero, Inc.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

extern crate alloc;

use std::iter::successors;

use alloc::collections::BTreeMap;
use itertools::Itertools;

use crate::{CENO_PLATFORM, addr::WORD_SIZE, disassemble::transpile, rv32im::Instruction};
use anyhow::{Context, Result, anyhow, bail};
use elf::{
    ElfBytes,
    abi::{PF_R, PF_W, PF_X},
    endian::LittleEndian,
    file::Class,
};

/// A RISC Zero program
#[derive(Clone, Debug)]
pub struct Program {
    /// The entrypoint of the program
    pub entry: u32,
    /// This is the lowest address of the program's executable code
    pub base_address: u32,
    /// This is the heap start address, match with _sheap retrieve from elf
    pub sheap: u32,
    /// The instructions of the program
    pub instructions: Vec<Instruction>,
    /// The initial memory image
    pub image: BTreeMap<u32, u32>,
}

impl From<&[Instruction]> for Program {
    fn from(insn_codes: &[Instruction]) -> Program {
        Self {
            entry: CENO_PLATFORM.pc_base(),
            base_address: CENO_PLATFORM.pc_base(),
            sheap: CENO_PLATFORM.heap.start,
            instructions: insn_codes.to_vec(),
            image: Default::default(),
        }
    }
}

impl Program {
    /// Create program
    pub fn new(
        entry: u32,
        base_address: u32,
        sheap: u32,
        instructions: Vec<Instruction>,
        image: BTreeMap<u32, u32>,
    ) -> Program {
        Self {
            entry,
            base_address,
            sheap,
            instructions,
            image,
        }
    }

    /// Initialize a RISC Zero Program from an appropriate ELF file
    pub fn load_elf(input: &[u8], max_mem: u32) -> Result<Program> {
        let mut instructions: Vec<u32> = Vec::new();
        let mut image: BTreeMap<u32, u32> = BTreeMap::new();
        let mut base_address = None;

        let elf = ElfBytes::<LittleEndian>::minimal_parse(input)
            .map_err(|err| anyhow!("Elf parse error: {err}"))?;
        if elf.ehdr.class != Class::ELF32 {
            bail!("Not a 32-bit ELF");
        }
        if elf.ehdr.e_machine != elf::abi::EM_RISCV {
            bail!("Invalid machine type, must be RISC-V");
        }
        if elf.ehdr.e_type != elf::abi::ET_EXEC {
            bail!("Invalid ELF type, must be executable");
        }
        let entry: u32 = elf
            .ehdr
            .e_entry
            .try_into()
            .map_err(|err| anyhow!("e_entry was larger than 32 bits. {err}"))?;
        if entry >= max_mem || entry % WORD_SIZE as u32 != 0 {
            bail!("Invalid entrypoint");
        }
        let segments = elf.segments().ok_or(anyhow!("Missing segment table"))?;
        if segments.len() > 256 {
            bail!("Too many program headers");
        }
        for (idx, segment) in segments
            .iter()
            .filter(|x| x.p_type == elf::abi::PT_LOAD)
            .enumerate()
        {
            let file_size: u32 = segment
                .p_filesz
                .try_into()
                .map_err(|err| anyhow!("filesize was larger than 32 bits. {err}"))?;
            if file_size >= max_mem {
                bail!("Invalid segment file_size");
            }
            let mem_size: u32 = segment
                .p_memsz
                .try_into()
                .map_err(|err| anyhow!("mem_size was larger than 32 bits {err}"))?;
            if mem_size >= max_mem {
                bail!("Invalid segment mem_size");
            }
            let vaddr: u32 = segment
                .p_vaddr
                .try_into()
                .map_err(|err| anyhow!("vaddr is larger than 32 bits. {err}"))?;
            let p_flags = segment.p_flags;
            if (p_flags & PF_X) != 0 {
                if base_address.is_none() {
                    base_address = Some(vaddr);
                } else {
                    return Err(anyhow!("only support one executable segment"));
                }
            }
            if vaddr % WORD_SIZE as u32 != 0 {
                bail!("vaddr {vaddr:08x} is unaligned");
            }
            tracing::debug!(
                "ELF segment {idx}: {}{}{} vaddr=0x{vaddr:08x} file_size={file_size} mem_size={mem_size}",
                if p_flags & PF_R != 0 { "R" } else { "-" },
                if p_flags & PF_W != 0 { "W" } else { "-" },
                if p_flags & PF_X != 0 { "X" } else { "-" },
            );
            let offset: u32 = segment
                .p_offset
                .try_into()
                .map_err(|err| anyhow!("offset is larger than 32 bits. {err}"))?;
            for i in (0..mem_size).step_by(WORD_SIZE) {
                let addr = vaddr.checked_add(i).context("Invalid segment vaddr")?;
                if addr >= max_mem {
                    bail!(
                        "Address [0x{addr:08x}] exceeds maximum address for guest programs [0x{max_mem:08x}]"
                    );
                }
                if i >= file_size {
                    // Past the file size and skip.
                } else {
                    let mut word = 0;
                    // Don't read past the end of the file.
                    let len = core::cmp::min(file_size - i, WORD_SIZE as u32);
                    for j in 0..len {
                        let offset = (offset + i + j) as usize;
                        let byte = input.get(offset).context("Invalid segment offset")?;
                        word |= (*byte as u32) << (j * 8);
                    }
                    image.insert(addr, word);
                    if (segment.p_flags & PF_X) != 0 {
                        instructions.push(word);
                    }
                }
            }
        }

        if base_address.is_none() {
            return Err(anyhow!("does not have executable segment"));
        }
        let base_address = base_address.unwrap();
        assert!(entry >= base_address);
        assert!((entry - base_address) as usize <= instructions.len() * WORD_SIZE);

        let instructions = transpile(base_address, &instructions);

        // program data include text/rodata/data/bss
        // truncate padding 0 section after bss
        let mut program_data = image
            .into_iter()
            .sorted_by_key(|(addr, _)| *addr)
            .collect_vec();

        // record current max address of bss
        // as later when we do static program data padding, it must cover max bss section and assure it's well constrained
        let bss_max_addr = program_data.last().cloned();

        // padding program_data to next power of 2 from last addr
        let padding_size = program_data.len().next_power_of_two() - program_data.len();
        if padding_size > 0 {
            program_data.extend(
                successors(
                    program_data.last().map(|d| (d.0 + WORD_SIZE as u32, 0)),
                    |(prev_addr, _)| Some((prev_addr + WORD_SIZE as u32, 0)),
                )
                .take(padding_size)
                .collect_vec(),
            );
        }

        let Some(((padded_max_static_addr, _), (bss_max_addr, _))) =
            program_data.last().zip(bss_max_addr)
        else {
            return Err(anyhow!("invalid size of data"));
        };

        if *padded_max_static_addr < bss_max_addr {
            return Err(anyhow!(
                "padded_max_static_addr should larger than bss_max_addr"
            ));
        }

        // retrieve sheap from elf
        let sheap = elf
            .symbol_table()?
            .and_then(|(symtab, strtab)| {
                symtab.iter().find_map(|symbol| {
                    strtab
                        .get(symbol.st_name as usize)
                        .ok()
                        .filter(|&name| name == "_sheap")
                        .map(|_| symbol.st_value)
                })
            })
            .ok_or_else(|| anyhow!("unable to find _sheap symbol"))? as u32;

        // there should be no
        if *padded_max_static_addr >= sheap {
            return Err(anyhow!(
                "padded_max_static_addr overlap with _sheap heap start address"
            ));
        }

        Ok(Program {
            entry,
            base_address,
            sheap,
            image: program_data.into_iter().collect::<BTreeMap<u32, u32>>(),
            instructions,
        })
    }
}
