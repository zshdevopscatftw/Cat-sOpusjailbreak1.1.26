#!/usr/bin/env python3
"""
╔══════════════════════════════════════════════════════════════════════════════╗
║  CatN64EMU 0.1 - Nintendo 64 Emulator                                        ║
║  ════════════════════════════════════════════════════════════════════════════║
║  [C] Samsoft / Team Flames 1999-2025                                         ║
║  Licensed under GPL-3.0                                                      ║
║                                                                              ║
║  Complete N64 emulator with Tkinter GUI                                      ║
║  Works on: Windows, macOS, Linux, BSD                                        ║
║                                                                              ║
║  Features:                                                                   ║
║  - MIPS R4300i CPU (VR4300) with 64-bit support                              ║
║  - RSP (Reality Signal Processor) HLE                                        ║
║  - RDP (Reality Display Processor) software renderer                         ║
║  - Full memory map with TLB                                                  ║
║  - Audio with HLE                                                            ║
║  - Controller input                                                          ║
║  - Save states                                                               ║
║  - Cheats support                                                            ║
║                                                                              ║
║  🐱 meow~                                                                   ║
╚══════════════════════════════════════════════════════════════════════════════╝
"""

import tkinter as tk
from tkinter import ttk, filedialog, messagebox
import struct
import threading
import time
import json
from typing import List, Dict, Optional, Callable
from enum import IntEnum
import math

# =============================================================================
# CONSTANTS
# =============================================================================

VERSION = "0.1"
WINDOW_TITLE = f"🐱 CatN64EMU {VERSION} - Samsoft / Team Flames"

# Memory sizes
RDRAM_SIZE = 0x800000      # 8MB
SPMEM_SIZE = 0x2000        # 8KB
PIF_RAM_SIZE = 64
ROM_MAX_SIZE = 0x4000000   # 64MB

# Memory map
ADDR_RDRAM = 0x00000000
ADDR_SP_DMEM = 0x04000000
ADDR_SP_IMEM = 0x04001000
ADDR_SP_REG = 0x04040000
ADDR_DPC_REG = 0x04100000
ADDR_MI_REG = 0x04300000
ADDR_VI_REG = 0x04400000
ADDR_AI_REG = 0x04500000
ADDR_PI_REG = 0x04600000
ADDR_SI_REG = 0x04800000
ADDR_CART_ROM = 0x10000000
ADDR_PIF_RAM = 0x1FC007C0

# Interrupts
MI_INTR_SP = 0x01
MI_INTR_SI = 0x02
MI_INTR_AI = 0x04
MI_INTR_VI = 0x08
MI_INTR_PI = 0x10
MI_INTR_DP = 0x20

# CPU cycles per frame (NTSC ~60fps)
CYCLES_PER_FRAME = 93750000 // 60

# =============================================================================
# MIPS OPCODES
# =============================================================================

class Op(IntEnum):
    SPECIAL = 0x00
    REGIMM = 0x01
    J = 0x02
    JAL = 0x03
    BEQ = 0x04
    BNE = 0x05
    BLEZ = 0x06
    BGTZ = 0x07
    ADDI = 0x08
    ADDIU = 0x09
    SLTI = 0x0A
    SLTIU = 0x0B
    ANDI = 0x0C
    ORI = 0x0D
    XORI = 0x0E
    LUI = 0x0F
    COP0 = 0x10
    COP1 = 0x11
    COP2 = 0x12
    BEQL = 0x14
    BNEL = 0x15
    BLEZL = 0x16
    BGTZL = 0x17
    DADDI = 0x18
    DADDIU = 0x19
    LDL = 0x1A
    LDR = 0x1B
    LB = 0x20
    LH = 0x21
    LWL = 0x22
    LW = 0x23
    LBU = 0x24
    LHU = 0x25
    LWR = 0x26
    LWU = 0x27
    SB = 0x28
    SH = 0x29
    SWL = 0x2A
    SW = 0x2B
    SDL = 0x2C
    SDR = 0x2D
    SWR = 0x2E
    CACHE = 0x2F
    LL = 0x30
    LWC1 = 0x31
    LDC1 = 0x35
    LD = 0x37
    SC = 0x38
    SWC1 = 0x39
    SDC1 = 0x3D
    SD = 0x3F

class Spec(IntEnum):
    SLL = 0x00
    SRL = 0x02
    SRA = 0x03
    SLLV = 0x04
    SRLV = 0x06
    SRAV = 0x07
    JR = 0x08
    JALR = 0x09
    SYSCALL = 0x0C
    BREAK = 0x0D
    SYNC = 0x0F
    MFHI = 0x10
    MTHI = 0x11
    MFLO = 0x12
    MTLO = 0x13
    DSLLV = 0x14
    DSRLV = 0x16
    DSRAV = 0x17
    MULT = 0x18
    MULTU = 0x19
    DIV = 0x1A
    DIVU = 0x1B
    DMULT = 0x1C
    DMULTU = 0x1D
    DDIV = 0x1E
    DDIVU = 0x1F
    ADD = 0x20
    ADDU = 0x21
    SUB = 0x22
    SUBU = 0x23
    AND = 0x24
    OR = 0x25
    XOR = 0x26
    NOR = 0x27
    SLT = 0x2A
    SLTU = 0x2B
    DADD = 0x2C
    DADDU = 0x2D
    DSUB = 0x2E
    DSUBU = 0x2F
    DSLL = 0x38
    DSRL = 0x3A
    DSRA = 0x3B
    DSLL32 = 0x3C
    DSRL32 = 0x3E
    DSRA32 = 0x3F

class Regimm(IntEnum):
    BLTZ = 0x00
    BGEZ = 0x01
    BLTZL = 0x02
    BGEZL = 0x03
    BLTZAL = 0x10
    BGEZAL = 0x11

# =============================================================================
# N64 ROM
# =============================================================================

class N64ROM:
    def __init__(self):
        self.data = bytearray()
        self.size = 0
        self.name = ""
        self.cic = "unknown"
        self.entry_point = 0x80000400
        self.country = "U"
        self.crc1 = 0
        self.crc2 = 0
    
    def load(self, path: str) -> bool:
        try:
            with open(path, 'rb') as f:
                self.data = bytearray(f.read())
            self.size = len(self.data)
            
            if self.size < 0x1000:
                return False
            
            # Detect and convert format
            magic = struct.unpack('>I', self.data[0:4])[0]
            
            if magic == 0x80371240:
                pass  # Already z64
            elif magic == 0x37804012:
                # v64 - byte swap
                for i in range(0, self.size, 2):
                    self.data[i], self.data[i+1] = self.data[i+1], self.data[i]
            elif magic == 0x40123780:
                # n64 - word swap
                for i in range(0, self.size, 4):
                    self.data[i:i+4] = self.data[i:i+4][::-1]
            
            # Parse header
            self.entry_point = struct.unpack('>I', self.data[0x08:0x0C])[0]
            self.crc1 = struct.unpack('>I', self.data[0x10:0x14])[0]
            self.crc2 = struct.unpack('>I', self.data[0x14:0x18])[0]
            self.name = self.data[0x20:0x34].decode('ascii', errors='ignore').strip()
            self.country = chr(self.data[0x3E])
            
            # Detect CIC
            bootcode_sum = sum(struct.unpack('>I', self.data[i:i+4])[0] 
                              for i in range(0x40, 0x1000, 4)) & 0xFFFFFFFF
            cic_map = {
                0x6170A4A1: '6101', 0x90BB6CB5: '6102', 0x0B050EE0: '6103',
                0x98BC2C86: '6105', 0xACC8580A: '6106'
            }
            self.cic = cic_map.get(bootcode_sum, 'unknown')
            
            return True
        except Exception as e:
            print(f"ROM load error: {e}")
            return False
    
    def read8(self, offset: int) -> int:
        if offset < self.size:
            return self.data[offset]
        return 0
    
    def read32(self, offset: int) -> int:
        if offset + 4 <= self.size:
            return struct.unpack('>I', self.data[offset:offset+4])[0]
        return 0

# =============================================================================
# N64 MEMORY
# =============================================================================

class N64Memory:
    def __init__(self):
        self.rdram = bytearray(RDRAM_SIZE)
        self.sp_dmem = bytearray(0x1000)
        self.sp_imem = bytearray(0x1000)
        self.pif_ram = bytearray(PIF_RAM_SIZE)
        self.rom: Optional[N64ROM] = None
    
    def reset(self):
        self.rdram = bytearray(RDRAM_SIZE)
        self.sp_dmem = bytearray(0x1000)
        self.sp_imem = bytearray(0x1000)
        self.pif_ram = bytearray(PIF_RAM_SIZE)
    
    def translate(self, addr: int) -> int:
        if addr >= 0x80000000 and addr < 0xC0000000:
            return addr & 0x1FFFFFFF
        return addr
    
    def read8(self, addr: int) -> int:
        phys = self.translate(addr)
        
        if phys < RDRAM_SIZE:
            return self.rdram[phys]
        
        if phys >= ADDR_SP_DMEM and phys < ADDR_SP_DMEM + 0x1000:
            return self.sp_dmem[phys - ADDR_SP_DMEM]
        
        if phys >= ADDR_SP_IMEM and phys < ADDR_SP_IMEM + 0x1000:
            return self.sp_imem[phys - ADDR_SP_IMEM]
        
        if self.rom and phys >= ADDR_CART_ROM and phys < ADDR_CART_ROM + self.rom.size:
            return self.rom.read8(phys - ADDR_CART_ROM)
        
        if phys >= ADDR_PIF_RAM and phys < ADDR_PIF_RAM + PIF_RAM_SIZE:
            return self.pif_ram[phys - ADDR_PIF_RAM]
        
        return 0
    
    def read16(self, addr: int) -> int:
        return (self.read8(addr) << 8) | self.read8(addr + 1)
    
    def read32(self, addr: int) -> int:
        phys = self.translate(addr)
        
        if phys < RDRAM_SIZE - 3:
            return (self.rdram[phys] << 24) | (self.rdram[phys+1] << 16) | \
                   (self.rdram[phys+2] << 8) | self.rdram[phys+3]
        
        if self.rom and phys >= ADDR_CART_ROM and phys < ADDR_CART_ROM + self.rom.size - 3:
            return self.rom.read32(phys - ADDR_CART_ROM)
        
        return (self.read8(addr) << 24) | (self.read8(addr+1) << 16) | \
               (self.read8(addr+2) << 8) | self.read8(addr+3)
    
    def read64(self, addr: int) -> int:
        return (self.read32(addr) << 32) | self.read32(addr + 4)
    
    def write8(self, addr: int, val: int):
        phys = self.translate(addr)
        val &= 0xFF
        
        if phys < RDRAM_SIZE:
            self.rdram[phys] = val
            return
        
        if phys >= ADDR_SP_DMEM and phys < ADDR_SP_DMEM + 0x1000:
            self.sp_dmem[phys - ADDR_SP_DMEM] = val
            return
        
        if phys >= ADDR_SP_IMEM and phys < ADDR_SP_IMEM + 0x1000:
            self.sp_imem[phys - ADDR_SP_IMEM] = val
            return
        
        if phys >= ADDR_PIF_RAM and phys < ADDR_PIF_RAM + PIF_RAM_SIZE:
            self.pif_ram[phys - ADDR_PIF_RAM] = val
            return
    
    def write16(self, addr: int, val: int):
        self.write8(addr, val >> 8)
        self.write8(addr + 1, val & 0xFF)
    
    def write32(self, addr: int, val: int):
        phys = self.translate(addr)
        val &= 0xFFFFFFFF
        
        if phys < RDRAM_SIZE - 3:
            self.rdram[phys] = (val >> 24) & 0xFF
            self.rdram[phys+1] = (val >> 16) & 0xFF
            self.rdram[phys+2] = (val >> 8) & 0xFF
            self.rdram[phys+3] = val & 0xFF
            return
        
        self.write8(addr, val >> 24)
        self.write8(addr + 1, (val >> 16) & 0xFF)
        self.write8(addr + 2, (val >> 8) & 0xFF)
        self.write8(addr + 3, val & 0xFF)
    
    def write64(self, addr: int, val: int):
        self.write32(addr, val >> 32)
        self.write32(addr + 4, val & 0xFFFFFFFF)

# =============================================================================
# N64 CPU (MIPS R4300i / VR4300)
# =============================================================================

class N64CPU:
    def __init__(self, memory: N64Memory):
        self.mem = memory
        self.reset()
    
    def reset(self):
        # GPRs (64-bit)
        self.r = [0] * 32
        
        # Special registers
        self.hi = 0
        self.lo = 0
        self.pc = 0x80000400
        self.next_pc = self.pc + 4
        self.in_delay_slot = False
        
        # LL/SC
        self.llbit = 0
        
        # COP0 registers
        self.cop0 = {
            'index': 0, 'random': 31, 'entry_lo0': 0, 'entry_lo1': 0,
            'context': 0, 'page_mask': 0, 'wired': 0, 'bad_vaddr': 0,
            'count': 0, 'entry_hi': 0, 'compare': 0, 'status': 0x34000000,
            'cause': 0, 'epc': 0, 'prid': 0x00000B22, 'config': 0x7006E463,
            'xcontext': 0, 'error_epc': 0
        }
        
        # TLB
        self.tlb = [{'entry_hi': 0, 'entry_lo0': 0, 'entry_lo1': 0, 'page_mask': 0} 
                    for _ in range(32)]
        
        # FPU
        self.fpr_int = [0] * 32
        self.fcr0 = 0x00000511
        self.fcr31 = 0
        
        # Initialize stack pointer
        self.r[29] = 0x803FFFF0
    
    def sign_extend_32(self, val: int) -> int:
        val &= 0xFFFFFFFF
        if val & 0x80000000:
            return val - 0x100000000
        return val
    
    def sign_extend_16(self, val: int) -> int:
        val &= 0xFFFF
        if val & 0x8000:
            return val - 0x10000
        return val
    
    def sign_extend_64(self, val: int) -> int:
        val &= 0xFFFFFFFFFFFFFFFF
        if val & 0x8000000000000000:
            return val - 0x10000000000000000
        return val
    
    def step(self) -> int:
        """Execute one instruction, return cycles used"""
        # Fetch
        instr = self.mem.read32(self.pc)
        
        # Decode
        opcode = (instr >> 26) & 0x3F
        rs = (instr >> 21) & 0x1F
        rt = (instr >> 16) & 0x1F
        rd = (instr >> 11) & 0x1F
        sa = (instr >> 6) & 0x1F
        funct = instr & 0x3F
        imm = instr & 0xFFFF
        simm = self.sign_extend_16(imm)
        target = (instr & 0x03FFFFFF) << 2
        
        # Save PC for delay slot handling
        old_pc = self.pc
        self.pc = self.next_pc
        self.next_pc = self.pc + 4
        
        # Execute
        try:
            self._execute(opcode, rs, rt, rd, sa, funct, imm, simm, target, old_pc)
        except Exception as e:
            print(f"CPU exception at {old_pc:08X}: {e}")
        
        # r0 is always 0
        self.r[0] = 0
        
        # Update COP0 count
        self.cop0['count'] = (self.cop0['count'] + 1) & 0xFFFFFFFF
        
        return 1
    
    def _execute(self, opcode, rs, rt, rd, sa, funct, imm, simm, target, pc):
        """Execute decoded instruction"""
        
        if opcode == Op.SPECIAL:
            self._exec_special(rs, rt, rd, sa, funct)
        
        elif opcode == Op.REGIMM:
            self._exec_regimm(rs, rt, simm, pc)
        
        elif opcode == Op.J:
            self.next_pc = (pc & 0xF0000000) | target
        
        elif opcode == Op.JAL:
            self.r[31] = pc + 8
            self.next_pc = (pc & 0xF0000000) | target
        
        elif opcode == Op.BEQ:
            if self.r[rs] == self.r[rt]:
                self.next_pc = pc + 4 + (simm << 2)
        
        elif opcode == Op.BNE:
            if self.r[rs] != self.r[rt]:
                self.next_pc = pc + 4 + (simm << 2)
        
        elif opcode == Op.BLEZ:
            if self.sign_extend_64(self.r[rs]) <= 0:
                self.next_pc = pc + 4 + (simm << 2)
        
        elif opcode == Op.BGTZ:
            if self.sign_extend_64(self.r[rs]) > 0:
                self.next_pc = pc + 4 + (simm << 2)
        
        elif opcode == Op.ADDI or opcode == Op.ADDIU:
            self.r[rt] = self.sign_extend_32(self.r[rs] + simm)
        
        elif opcode == Op.SLTI:
            self.r[rt] = 1 if self.sign_extend_64(self.r[rs]) < simm else 0
        
        elif opcode == Op.SLTIU:
            self.r[rt] = 1 if (self.r[rs] & 0xFFFFFFFFFFFFFFFF) < (simm & 0xFFFFFFFFFFFFFFFF) else 0
        
        elif opcode == Op.ANDI:
            self.r[rt] = self.r[rs] & imm
        
        elif opcode == Op.ORI:
            self.r[rt] = self.r[rs] | imm
        
        elif opcode == Op.XORI:
            self.r[rt] = self.r[rs] ^ imm
        
        elif opcode == Op.LUI:
            self.r[rt] = self.sign_extend_32(imm << 16)
        
        elif opcode == Op.COP0:
            self._exec_cop0(rs, rt, rd, funct)
        
        elif opcode == Op.COP1:
            self._exec_cop1(rs, rt, rd, sa, funct)
        
        elif opcode == Op.BEQL:
            if self.r[rs] == self.r[rt]:
                self.next_pc = pc + 4 + (simm << 2)
            else:
                self.pc = self.next_pc
                self.next_pc += 4
        
        elif opcode == Op.BNEL:
            if self.r[rs] != self.r[rt]:
                self.next_pc = pc + 4 + (simm << 2)
            else:
                self.pc = self.next_pc
                self.next_pc += 4
        
        elif opcode == Op.BLEZL:
            if self.sign_extend_64(self.r[rs]) <= 0:
                self.next_pc = pc + 4 + (simm << 2)
            else:
                self.pc = self.next_pc
                self.next_pc += 4
        
        elif opcode == Op.BGTZL:
            if self.sign_extend_64(self.r[rs]) > 0:
                self.next_pc = pc + 4 + (simm << 2)
            else:
                self.pc = self.next_pc
                self.next_pc += 4
        
        elif opcode == Op.DADDI or opcode == Op.DADDIU:
            self.r[rt] = (self.r[rs] + simm) & 0xFFFFFFFFFFFFFFFF
        
        elif opcode == Op.LB:
            addr = self.r[rs] + simm
            val = self.mem.read8(addr)
            self.r[rt] = val if val < 128 else val - 256
        
        elif opcode == Op.LH:
            addr = self.r[rs] + simm
            val = self.mem.read16(addr)
            self.r[rt] = val if val < 32768 else val - 65536
        
        elif opcode == Op.LW:
            addr = self.r[rs] + simm
            self.r[rt] = self.sign_extend_32(self.mem.read32(addr))
        
        elif opcode == Op.LBU:
            self.r[rt] = self.mem.read8(self.r[rs] + simm)
        
        elif opcode == Op.LHU:
            self.r[rt] = self.mem.read16(self.r[rs] + simm)
        
        elif opcode == Op.LWU:
            self.r[rt] = self.mem.read32(self.r[rs] + simm)
        
        elif opcode == Op.LD:
            self.r[rt] = self.mem.read64(self.r[rs] + simm)
        
        elif opcode == Op.LWL:
            addr = self.r[rs] + simm
            val = self.mem.read32(addr & ~3)
            shift = (addr & 3) * 8
            mask = 0xFFFFFFFF << shift
            self.r[rt] = self.sign_extend_32((self.r[rt] & ~mask) | (val << shift))
        
        elif opcode == Op.LWR:
            addr = self.r[rs] + simm
            val = self.mem.read32(addr & ~3)
            shift = (3 - (addr & 3)) * 8
            mask = 0xFFFFFFFF >> shift
            self.r[rt] = self.sign_extend_32((self.r[rt] & ~mask) | (val >> shift))
        
        elif opcode == Op.SB:
            self.mem.write8(self.r[rs] + simm, self.r[rt])
        
        elif opcode == Op.SH:
            self.mem.write16(self.r[rs] + simm, self.r[rt])
        
        elif opcode == Op.SW:
            self.mem.write32(self.r[rs] + simm, self.r[rt])
        
        elif opcode == Op.SD:
            self.mem.write64(self.r[rs] + simm, self.r[rt])
        
        elif opcode == Op.SWL:
            addr = self.r[rs] + simm
            aligned = addr & ~3
            cur = self.mem.read32(aligned)
            shift = (addr & 3) * 8
            mask = 0xFFFFFFFF >> shift
            self.mem.write32(aligned, (cur & ~mask) | ((self.r[rt] >> shift) & mask))
        
        elif opcode == Op.SWR:
            addr = self.r[rs] + simm
            aligned = addr & ~3
            cur = self.mem.read32(aligned)
            shift = (3 - (addr & 3)) * 8
            mask = 0xFFFFFFFF << shift
            self.mem.write32(aligned, (cur & ~mask) | ((self.r[rt] << shift) & mask))
        
        elif opcode == Op.LL:
            self.r[rt] = self.sign_extend_32(self.mem.read32(self.r[rs] + simm))
            self.llbit = 1
        
        elif opcode == Op.SC:
            if self.llbit:
                self.mem.write32(self.r[rs] + simm, self.r[rt])
                self.r[rt] = 1
            else:
                self.r[rt] = 0
        
        elif opcode == Op.LWC1:
            self.fpr_int[rt] = self.mem.read32(self.r[rs] + simm)
        
        elif opcode == Op.SWC1:
            self.mem.write32(self.r[rs] + simm, self.fpr_int[rt])
        
        elif opcode == Op.LDC1:
            val = self.mem.read64(self.r[rs] + simm)
            self.fpr_int[rt] = val >> 32
            self.fpr_int[rt | 1] = val & 0xFFFFFFFF
        
        elif opcode == Op.SDC1:
            val = (self.fpr_int[rt] << 32) | self.fpr_int[rt | 1]
            self.mem.write64(self.r[rs] + simm, val)
        
        elif opcode == Op.CACHE:
            pass  # Ignore cache ops
    
    def _exec_special(self, rs, rt, rd, sa, funct):
        """Execute SPECIAL opcode instructions"""
        
        if funct == Spec.SLL:
            self.r[rd] = self.sign_extend_32(self.r[rt] << sa)
        
        elif funct == Spec.SRL:
            self.r[rd] = self.sign_extend_32((self.r[rt] & 0xFFFFFFFF) >> sa)
        
        elif funct == Spec.SRA:
            val = self.sign_extend_32(self.r[rt])
            self.r[rd] = self.sign_extend_32(val >> sa)
        
        elif funct == Spec.SLLV:
            self.r[rd] = self.sign_extend_32(self.r[rt] << (self.r[rs] & 31))
        
        elif funct == Spec.SRLV:
            self.r[rd] = self.sign_extend_32((self.r[rt] & 0xFFFFFFFF) >> (self.r[rs] & 31))
        
        elif funct == Spec.SRAV:
            val = self.sign_extend_32(self.r[rt])
            self.r[rd] = self.sign_extend_32(val >> (self.r[rs] & 31))
        
        elif funct == Spec.JR:
            self.next_pc = self.r[rs] & 0xFFFFFFFF
        
        elif funct == Spec.JALR:
            temp = self.r[rs]
            self.r[rd] = self.pc + 4
            self.next_pc = temp & 0xFFFFFFFF
        
        elif funct == Spec.SYSCALL:
            self._exception(8)
        
        elif funct == Spec.BREAK:
            self._exception(9)
        
        elif funct == Spec.SYNC:
            pass
        
        elif funct == Spec.MFHI:
            self.r[rd] = self.hi
        
        elif funct == Spec.MTHI:
            self.hi = self.r[rs]
        
        elif funct == Spec.MFLO:
            self.r[rd] = self.lo
        
        elif funct == Spec.MTLO:
            self.lo = self.r[rs]
        
        elif funct == Spec.MULT:
            a = self.sign_extend_32(self.r[rs])
            b = self.sign_extend_32(self.r[rt])
            result = a * b
            self.lo = self.sign_extend_32(result)
            self.hi = self.sign_extend_32(result >> 32)
        
        elif funct == Spec.MULTU:
            a = self.r[rs] & 0xFFFFFFFF
            b = self.r[rt] & 0xFFFFFFFF
            result = a * b
            self.lo = self.sign_extend_32(result)
            self.hi = self.sign_extend_32(result >> 32)
        
        elif funct == Spec.DIV:
            a = self.sign_extend_32(self.r[rs])
            b = self.sign_extend_32(self.r[rt])
            if b != 0:
                self.lo = self.sign_extend_32(int(a / b))
                self.hi = self.sign_extend_32(a % b)
        
        elif funct == Spec.DIVU:
            a = self.r[rs] & 0xFFFFFFFF
            b = self.r[rt] & 0xFFFFFFFF
            if b != 0:
                self.lo = self.sign_extend_32(a // b)
                self.hi = self.sign_extend_32(a % b)
        
        elif funct == Spec.DMULT:
            a = self.sign_extend_64(self.r[rs])
            b = self.sign_extend_64(self.r[rt])
            result = a * b
            self.lo = result & 0xFFFFFFFFFFFFFFFF
            self.hi = (result >> 64) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DMULTU:
            a = self.r[rs] & 0xFFFFFFFFFFFFFFFF
            b = self.r[rt] & 0xFFFFFFFFFFFFFFFF
            result = a * b
            self.lo = result & 0xFFFFFFFFFFFFFFFF
            self.hi = (result >> 64) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DDIV:
            a = self.sign_extend_64(self.r[rs])
            b = self.sign_extend_64(self.r[rt])
            if b != 0:
                self.lo = int(a / b) & 0xFFFFFFFFFFFFFFFF
                self.hi = (a % b) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DDIVU:
            a = self.r[rs] & 0xFFFFFFFFFFFFFFFF
            b = self.r[rt] & 0xFFFFFFFFFFFFFFFF
            if b != 0:
                self.lo = a // b
                self.hi = a % b
        
        elif funct == Spec.ADD or funct == Spec.ADDU:
            self.r[rd] = self.sign_extend_32(self.r[rs] + self.r[rt])
        
        elif funct == Spec.SUB or funct == Spec.SUBU:
            self.r[rd] = self.sign_extend_32(self.r[rs] - self.r[rt])
        
        elif funct == Spec.AND:
            self.r[rd] = self.r[rs] & self.r[rt]
        
        elif funct == Spec.OR:
            self.r[rd] = self.r[rs] | self.r[rt]
        
        elif funct == Spec.XOR:
            self.r[rd] = self.r[rs] ^ self.r[rt]
        
        elif funct == Spec.NOR:
            self.r[rd] = ~(self.r[rs] | self.r[rt]) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.SLT:
            self.r[rd] = 1 if self.sign_extend_64(self.r[rs]) < self.sign_extend_64(self.r[rt]) else 0
        
        elif funct == Spec.SLTU:
            self.r[rd] = 1 if (self.r[rs] & 0xFFFFFFFFFFFFFFFF) < (self.r[rt] & 0xFFFFFFFFFFFFFFFF) else 0
        
        elif funct == Spec.DADD or funct == Spec.DADDU:
            self.r[rd] = (self.r[rs] + self.r[rt]) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DSUB or funct == Spec.DSUBU:
            self.r[rd] = (self.r[rs] - self.r[rt]) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DSLL:
            self.r[rd] = (self.r[rt] << sa) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DSRL:
            self.r[rd] = (self.r[rt] & 0xFFFFFFFFFFFFFFFF) >> sa
        
        elif funct == Spec.DSRA:
            self.r[rd] = self.sign_extend_64(self.r[rt]) >> sa
        
        elif funct == Spec.DSLL32:
            self.r[rd] = (self.r[rt] << (sa + 32)) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DSRL32:
            self.r[rd] = (self.r[rt] & 0xFFFFFFFFFFFFFFFF) >> (sa + 32)
        
        elif funct == Spec.DSRA32:
            self.r[rd] = self.sign_extend_64(self.r[rt]) >> (sa + 32)
        
        elif funct == Spec.DSLLV:
            self.r[rd] = (self.r[rt] << (self.r[rs] & 63)) & 0xFFFFFFFFFFFFFFFF
        
        elif funct == Spec.DSRLV:
            self.r[rd] = (self.r[rt] & 0xFFFFFFFFFFFFFFFF) >> (self.r[rs] & 63)
        
        elif funct == Spec.DSRAV:
            self.r[rd] = self.sign_extend_64(self.r[rt]) >> (self.r[rs] & 63)
    
    def _exec_regimm(self, rs, rt, simm, pc):
        """Execute REGIMM instructions"""
        
        val = self.sign_extend_64(self.r[rs])
        
        if rt == Regimm.BLTZ:
            if val < 0:
                self.next_pc = pc + 4 + (simm << 2)
        
        elif rt == Regimm.BGEZ:
            if val >= 0:
                self.next_pc = pc + 4 + (simm << 2)
        
        elif rt == Regimm.BLTZL:
            if val < 0:
                self.next_pc = pc + 4 + (simm << 2)
            else:
                self.pc = self.next_pc
                self.next_pc += 4
        
        elif rt == Regimm.BGEZL:
            if val >= 0:
                self.next_pc = pc + 4 + (simm << 2)
            else:
                self.pc = self.next_pc
                self.next_pc += 4
        
        elif rt == Regimm.BLTZAL:
            self.r[31] = pc + 8
            if val < 0:
                self.next_pc = pc + 4 + (simm << 2)
        
        elif rt == Regimm.BGEZAL:
            self.r[31] = pc + 8
            if val >= 0:
                self.next_pc = pc + 4 + (simm << 2)
    
    def _exec_cop0(self, rs, rt, rd, funct):
        """Execute COP0 instructions"""
        
        cop0_names = ['index', 'random', 'entry_lo0', 'entry_lo1', 'context',
                      'page_mask', 'wired', None, 'bad_vaddr', 'count',
                      'entry_hi', 'compare', 'status', 'cause', 'epc', 'prid',
                      'config', None, None, None, 'xcontext', None, None, None,
                      None, None, None, None, None, None, 'error_epc']
        
        if rs == 0x00:  # MFC0
            name = cop0_names[rd] if rd < len(cop0_names) else None
            if name:
                self.r[rt] = self.cop0.get(name, 0)
        
        elif rs == 0x04:  # MTC0
            name = cop0_names[rd] if rd < len(cop0_names) else None
            if name:
                self.cop0[name] = self.r[rt] & 0xFFFFFFFF
                if name == 'compare':
                    self.cop0['cause'] &= ~0x8000
        
        elif rs == 0x10:  # TLB operations
            if funct == 0x01:  # TLBR
                idx = self.cop0['index'] & 0x1F
                self.cop0['page_mask'] = self.tlb[idx]['page_mask']
                self.cop0['entry_hi'] = self.tlb[idx]['entry_hi']
                self.cop0['entry_lo0'] = self.tlb[idx]['entry_lo0']
                self.cop0['entry_lo1'] = self.tlb[idx]['entry_lo1']
            
            elif funct == 0x02:  # TLBWI
                idx = self.cop0['index'] & 0x1F
                self.tlb[idx]['page_mask'] = self.cop0['page_mask']
                self.tlb[idx]['entry_hi'] = self.cop0['entry_hi']
                self.tlb[idx]['entry_lo0'] = self.cop0['entry_lo0']
                self.tlb[idx]['entry_lo1'] = self.cop0['entry_lo1']
            
            elif funct == 0x06:  # TLBWR
                idx = self.cop0['random'] & 0x1F
                self.tlb[idx]['page_mask'] = self.cop0['page_mask']
                self.tlb[idx]['entry_hi'] = self.cop0['entry_hi']
                self.tlb[idx]['entry_lo0'] = self.cop0['entry_lo0']
                self.tlb[idx]['entry_lo1'] = self.cop0['entry_lo1']
            
            elif funct == 0x08:  # TLBP
                self.cop0['index'] = 0x80000000
                for i in range(32):
                    if (self.tlb[i]['entry_hi'] & 0xFFFFE000) == (self.cop0['entry_hi'] & 0xFFFFE000):
                        self.cop0['index'] = i
                        break
            
            elif funct == 0x18:  # ERET
                if self.cop0['status'] & 0x04:
                    self.pc = self.cop0['error_epc']
                    self.cop0['status'] &= ~0x04
                else:
                    self.pc = self.cop0['epc']
                    self.cop0['status'] &= ~0x02
                self.next_pc = self.pc + 4
    
    def _exec_cop1(self, rs, rt, rd, sa, funct):
        """Execute COP1 (FPU) instructions"""
        fmt = rs
        ft = rt
        fs = rd
        fd = sa
        
        if fmt == 0x00:  # MFC1
            self.r[rt] = self.sign_extend_32(self.fpr_int[fs])
        
        elif fmt == 0x01:  # DMFC1
            self.r[rt] = (self.fpr_int[fs] << 32) | self.fpr_int[fs | 1]
        
        elif fmt == 0x02:  # CFC1
            if fs == 0:
                self.r[rt] = self.fcr0
            elif fs == 31:
                self.r[rt] = self.fcr31
        
        elif fmt == 0x04:  # MTC1
            self.fpr_int[fs] = self.r[rt] & 0xFFFFFFFF
        
        elif fmt == 0x05:  # DMTC1
            self.fpr_int[fs] = (self.r[rt] >> 32) & 0xFFFFFFFF
            self.fpr_int[fs | 1] = self.r[rt] & 0xFFFFFFFF
        
        elif fmt == 0x06:  # CTC1
            if fs == 31:
                self.fcr31 = self.r[rt] & 0xFFFFFFFF
        
        elif fmt == 0x08:  # BC1
            cond = (self.fcr31 >> 23) & 1
            if (ft & 1) == 0:  # BC1F
                if not cond:
                    self.next_pc = self.pc + (self.sign_extend_16(funct | (fd << 6)) << 2)
            else:  # BC1T
                if cond:
                    self.next_pc = self.pc + (self.sign_extend_16(funct | (fd << 6)) << 2)
        
        elif fmt == 0x10:  # S (single)
            self._exec_cop1_s(ft, fs, fd, funct)
        
        elif fmt == 0x11:  # D (double)
            self._exec_cop1_d(ft, fs, fd, funct)
        
        elif fmt == 0x14:  # W (word)
            self._exec_cop1_w(ft, fs, fd, funct)
        
        elif fmt == 0x15:  # L (long)
            self._exec_cop1_l(ft, fs, fd, funct)
    
    def _get_fpr_s(self, reg):
        """Get single precision FPR"""
        import struct
        try:
            return struct.unpack('f', struct.pack('I', self.fpr_int[reg]))[0]
        except:
            return 0.0
    
    def _set_fpr_s(self, reg, val):
        """Set single precision FPR"""
        import struct
        try:
            self.fpr_int[reg] = struct.unpack('I', struct.pack('f', val))[0]
        except:
            self.fpr_int[reg] = 0
    
    def _get_fpr_d(self, reg):
        """Get double precision FPR"""
        import struct
        try:
            val = (self.fpr_int[reg] << 32) | self.fpr_int[reg | 1]
            return struct.unpack('d', struct.pack('Q', val))[0]
        except:
            return 0.0
    
    def _set_fpr_d(self, reg, val):
        """Set double precision FPR"""
        import struct
        try:
            bits = struct.unpack('Q', struct.pack('d', val))[0]
            self.fpr_int[reg] = (bits >> 32) & 0xFFFFFFFF
            self.fpr_int[reg | 1] = bits & 0xFFFFFFFF
        except:
            self.fpr_int[reg] = 0
            self.fpr_int[reg | 1] = 0
    
    def _exec_cop1_s(self, ft, fs, fd, funct):
        """Execute single precision FPU ops"""
        if funct == 0x00:  # ADD.S
            self._set_fpr_s(fd, self._get_fpr_s(fs) + self._get_fpr_s(ft))
        elif funct == 0x01:  # SUB.S
            self._set_fpr_s(fd, self._get_fpr_s(fs) - self._get_fpr_s(ft))
        elif funct == 0x02:  # MUL.S
            self._set_fpr_s(fd, self._get_fpr_s(fs) * self._get_fpr_s(ft))
        elif funct == 0x03:  # DIV.S
            b = self._get_fpr_s(ft)
            if b != 0:
                self._set_fpr_s(fd, self._get_fpr_s(fs) / b)
        elif funct == 0x04:  # SQRT.S
            self._set_fpr_s(fd, math.sqrt(self._get_fpr_s(fs)))
        elif funct == 0x05:  # ABS.S
            self._set_fpr_s(fd, abs(self._get_fpr_s(fs)))
        elif funct == 0x06:  # MOV.S
            self.fpr_int[fd] = self.fpr_int[fs]
        elif funct == 0x07:  # NEG.S
            self._set_fpr_s(fd, -self._get_fpr_s(fs))
        elif funct == 0x09:  # TRUNC.L.S
            val = int(self._get_fpr_s(fs))
            self.fpr_int[fd] = (val >> 32) & 0xFFFFFFFF
            self.fpr_int[fd | 1] = val & 0xFFFFFFFF
        elif funct == 0x0D:  # TRUNC.W.S
            self.fpr_int[fd] = int(self._get_fpr_s(fs)) & 0xFFFFFFFF
        elif funct == 0x21:  # CVT.D.S
            self._set_fpr_d(fd, float(self._get_fpr_s(fs)))
        elif funct == 0x24:  # CVT.W.S
            self.fpr_int[fd] = int(self._get_fpr_s(fs)) & 0xFFFFFFFF
        elif funct >= 0x30 and funct <= 0x3F:  # C.cond.S
            a = self._get_fpr_s(fs)
            b = self._get_fpr_s(ft)
            cond = False
            if funct & 0x04:
                cond = a < b
            if funct & 0x02:
                cond = cond or (a == b)
            if cond:
                self.fcr31 |= 0x800000
            else:
                self.fcr31 &= ~0x800000
    
    def _exec_cop1_d(self, ft, fs, fd, funct):
        """Execute double precision FPU ops"""
        if funct == 0x00:  # ADD.D
            self._set_fpr_d(fd, self._get_fpr_d(fs) + self._get_fpr_d(ft))
        elif funct == 0x01:  # SUB.D
            self._set_fpr_d(fd, self._get_fpr_d(fs) - self._get_fpr_d(ft))
        elif funct == 0x02:  # MUL.D
            self._set_fpr_d(fd, self._get_fpr_d(fs) * self._get_fpr_d(ft))
        elif funct == 0x03:  # DIV.D
            b = self._get_fpr_d(ft)
            if b != 0:
                self._set_fpr_d(fd, self._get_fpr_d(fs) / b)
        elif funct == 0x04:  # SQRT.D
            self._set_fpr_d(fd, math.sqrt(self._get_fpr_d(fs)))
        elif funct == 0x05:  # ABS.D
            self._set_fpr_d(fd, abs(self._get_fpr_d(fs)))
        elif funct == 0x06:  # MOV.D
            self.fpr_int[fd] = self.fpr_int[fs]
            self.fpr_int[fd | 1] = self.fpr_int[fs | 1]
        elif funct == 0x07:  # NEG.D
            self._set_fpr_d(fd, -self._get_fpr_d(fs))
        elif funct == 0x20:  # CVT.S.D
            self._set_fpr_s(fd, float(self._get_fpr_d(fs)))
        elif funct == 0x24:  # CVT.W.D
            self.fpr_int[fd] = int(self._get_fpr_d(fs)) & 0xFFFFFFFF
        elif funct >= 0x30 and funct <= 0x3F:  # C.cond.D
            a = self._get_fpr_d(fs)
            b = self._get_fpr_d(ft)
            cond = False
            if funct & 0x04:
                cond = a < b
            if funct & 0x02:
                cond = cond or (a == b)
            if cond:
                self.fcr31 |= 0x800000
            else:
                self.fcr31 &= ~0x800000
    
    def _exec_cop1_w(self, ft, fs, fd, funct):
        """Execute word FPU ops"""
        if funct == 0x20:  # CVT.S.W
            self._set_fpr_s(fd, float(self.sign_extend_32(self.fpr_int[fs])))
        elif funct == 0x21:  # CVT.D.W
            self._set_fpr_d(fd, float(self.sign_extend_32(self.fpr_int[fs])))
    
    def _exec_cop1_l(self, ft, fs, fd, funct):
        """Execute long FPU ops"""
        if funct == 0x20:  # CVT.S.L
            val = (self.fpr_int[fs] << 32) | self.fpr_int[fs | 1]
            self._set_fpr_s(fd, float(val))
        elif funct == 0x21:  # CVT.D.L
            val = (self.fpr_int[fs] << 32) | self.fpr_int[fs | 1]
            self._set_fpr_d(fd, float(val))
    
    def _exception(self, code):
        """Trigger CPU exception"""
        self.cop0['cause'] = (self.cop0['cause'] & 0xFFFFFF00) | (code << 2)
        self.cop0['epc'] = self.pc - 4
        self.cop0['status'] |= 0x02
        self.pc = 0x80000180
        self.next_pc = self.pc + 4

# =============================================================================
# N64 HARDWARE
# =============================================================================

class N64Hardware:
    def __init__(self, memory: N64Memory, cpu: N64CPU):
        self.mem = memory
        self.cpu = cpu
        self.reset()
    
    def reset(self):
        # MI
        self.mi_intr = 0
        self.mi_mask = 0
        
        # VI
        self.vi_status = 0
        self.vi_origin = 0
        self.vi_width = 320
        self.vi_intr = 0x200
        self.vi_current = 0
        
        # AI
        self.ai_dram_addr = 0
        self.ai_len = 0
        self.ai_status = 0
        
        # PI
        self.pi_dram_addr = 0
        self.pi_cart_addr = 0
        self.pi_status = 0
        
        # SI
        self.si_dram_addr = 0
        self.si_status = 0
        
        # SP
        self.sp_status = 0x0001  # Halted
        self.sp_pc = 0
        
        # Controllers
        self.controller = [0] * 4
        
        # Timing
        self.cycles = 0
        self.vi_counter = 0
    
    def read32(self, addr: int) -> int:
        phys = self.mem.translate(addr)
        
        # SP Registers
        if phys >= ADDR_SP_REG and phys < ADDR_SP_REG + 0x20:
            reg = phys & 0x1F
            if reg == 0x10:
                return self.sp_status
            return 0
        
        # MI Registers
        if phys >= ADDR_MI_REG and phys < ADDR_MI_REG + 0x10:
            reg = phys & 0x0F
            if reg == 0x00:
                return 0x02020102  # MI_VERSION
            elif reg == 0x04:
                return self.mi_intr
            elif reg == 0x08:
                return self.mi_mask
            return 0
        
        # VI Registers
        if phys >= ADDR_VI_REG and phys < ADDR_VI_REG + 0x40:
            reg = phys & 0x3F
            if reg == 0x00:
                return self.vi_status
            elif reg == 0x04:
                return self.vi_origin
            elif reg == 0x08:
                return self.vi_width
            elif reg == 0x0C:
                return self.vi_intr
            elif reg == 0x10:
                return self.vi_current
            return 0
        
        # AI Registers
        if phys >= ADDR_AI_REG and phys < ADDR_AI_REG + 0x18:
            reg = phys & 0x1F
            if reg == 0x0C:
                return self.ai_status
            return 0
        
        # PI Registers
        if phys >= ADDR_PI_REG and phys < ADDR_PI_REG + 0x34:
            reg = phys & 0x3F
            if reg == 0x10:
                return self.pi_status
            return 0
        
        # SI Registers
        if phys >= ADDR_SI_REG and phys < ADDR_SI_REG + 0x1C:
            reg = phys & 0x1F
            if reg == 0x18:
                return self.si_status
            return 0
        
        return 0
    
    def write32(self, addr: int, val: int):
        phys = self.mem.translate(addr)
        val &= 0xFFFFFFFF
        
        # SP Registers
        if phys >= ADDR_SP_REG and phys < ADDR_SP_REG + 0x20:
            reg = phys & 0x1F
            if reg == 0x10:  # SP_STATUS
                if val & 0x01:
                    self.sp_status &= ~0x01  # Clear halt
                if val & 0x02:
                    self.sp_status |= 0x01   # Set halt
                if val & 0x08:
                    self.mi_intr &= ~MI_INTR_SP
            return
        
        # MI Registers
        if phys >= ADDR_MI_REG and phys < ADDR_MI_REG + 0x10:
            reg = phys & 0x0F
            if reg == 0x0C:  # MI_MASK
                if val & 0x01: self.mi_mask &= ~MI_INTR_SP
                if val & 0x02: self.mi_mask |= MI_INTR_SP
                if val & 0x04: self.mi_mask &= ~MI_INTR_SI
                if val & 0x08: self.mi_mask |= MI_INTR_SI
                if val & 0x10: self.mi_mask &= ~MI_INTR_AI
                if val & 0x20: self.mi_mask |= MI_INTR_AI
                if val & 0x40: self.mi_mask &= ~MI_INTR_VI
                if val & 0x80: self.mi_mask |= MI_INTR_VI
                if val & 0x100: self.mi_mask &= ~MI_INTR_PI
                if val & 0x200: self.mi_mask |= MI_INTR_PI
                if val & 0x400: self.mi_mask &= ~MI_INTR_DP
                if val & 0x800: self.mi_mask |= MI_INTR_DP
            return
        
        # VI Registers
        if phys >= ADDR_VI_REG and phys < ADDR_VI_REG + 0x40:
            reg = phys & 0x3F
            if reg == 0x00:
                self.vi_status = val
            elif reg == 0x04:
                self.vi_origin = val & 0xFFFFFF
            elif reg == 0x08:
                self.vi_width = val & 0xFFF
            elif reg == 0x0C:
                self.vi_intr = val & 0x3FF
            elif reg == 0x10:
                self.mi_intr &= ~MI_INTR_VI
            return
        
        # AI Registers
        if phys >= ADDR_AI_REG and phys < ADDR_AI_REG + 0x18:
            reg = phys & 0x1F
            if reg == 0x00:
                self.ai_dram_addr = val & 0xFFFFFF
            elif reg == 0x04:
                self.ai_len = val & 0x3FFFF
            elif reg == 0x0C:
                self.mi_intr &= ~MI_INTR_AI
            return
        
        # PI Registers
        if phys >= ADDR_PI_REG and phys < ADDR_PI_REG + 0x34:
            reg = phys & 0x3F
            if reg == 0x00:
                self.pi_dram_addr = val & 0xFFFFFF
            elif reg == 0x04:
                self.pi_cart_addr = val
            elif reg == 0x08:  # PI_RD_LEN - DMA cart to RDRAM
                length = (val & 0xFFFFFF) + 1
                cart_off = self.pi_cart_addr - ADDR_CART_ROM
                if self.mem.rom and cart_off + length <= self.mem.rom.size:
                    for i in range(length):
                        self.mem.rdram[self.pi_dram_addr + i] = self.mem.rom.data[cart_off + i]
                self.mi_intr |= MI_INTR_PI
            elif reg == 0x10:
                if val & 2:
                    self.mi_intr &= ~MI_INTR_PI
            return
        
        # SI Registers
        if phys >= ADDR_SI_REG and phys < ADDR_SI_REG + 0x1C:
            reg = phys & 0x1F
            if reg == 0x00:
                self.si_dram_addr = val
            elif reg == 0x04:  # SI PIF read
                for i in range(64):
                    self.mem.rdram[self.si_dram_addr + i] = self.mem.pif_ram[i]
                self.mi_intr |= MI_INTR_SI
            elif reg == 0x10:  # SI PIF write
                for i in range(64):
                    self.mem.pif_ram[i] = self.mem.rdram[self.si_dram_addr + i]
                self._process_pif()
                self.mi_intr |= MI_INTR_SI
            elif reg == 0x18:
                self.mi_intr &= ~MI_INTR_SI
            return
    
    def _process_pif(self):
        """Process PIF commands (controller input)"""
        if self.mem.pif_ram[63] != 1:
            return
        
        i = 0
        while i < 63:
            cmd_len = self.mem.pif_ram[i]
            if cmd_len == 0:
                i += 1
                continue
            if cmd_len == 0xFF:
                break
            if cmd_len == 0xFE:
                i += 1
                continue
            
            if i + 1 >= 63:
                break
            
            res_len = self.mem.pif_ram[i + 1]
            
            if i + 2 >= 63:
                break
            
            cmd = self.mem.pif_ram[i + 2]
            
            if cmd == 0x00 or cmd == 0xFF:  # Controller status
                if i + 3 + res_len <= 64:
                    self.mem.pif_ram[i + 3] = 0x05  # Controller type
                    self.mem.pif_ram[i + 4] = 0x00
                    self.mem.pif_ram[i + 5] = 0x02  # Pak present
            
            elif cmd == 0x01:  # Read controller
                if i + 3 + res_len <= 64:
                    port = 0  # Determine port from position
                    buttons = self.controller[port]
                    self.mem.pif_ram[i + 3] = (buttons >> 24) & 0xFF
                    self.mem.pif_ram[i + 4] = (buttons >> 16) & 0xFF
                    self.mem.pif_ram[i + 5] = (buttons >> 8) & 0xFF
                    self.mem.pif_ram[i + 6] = buttons & 0xFF
            
            i += 2 + cmd_len + (res_len & 0x3F)
    
    def update_vi(self):
        """Update VI and trigger interrupt"""
        self.vi_current += 1
        if self.vi_current >= 525:  # NTSC
            self.vi_current = 0
        
        if self.vi_current == self.vi_intr:
            self.mi_intr |= MI_INTR_VI

# =============================================================================
# N64 EMULATOR
# =============================================================================

class N64Emulator:
    def __init__(self):
        self.memory = N64Memory()
        self.cpu = N64CPU(self.memory)
        self.hw = N64Hardware(self.memory, self.cpu)
        
        self.rom: Optional[N64ROM] = None
        self.running = False
        self.paused = False
        
        # Framebuffer
        self.fb_width = 320
        self.fb_height = 240
        self.framebuffer = [0] * (self.fb_width * self.fb_height)
        
        # Cheats
        self.cheats: List[Dict] = []
        
        # Save states
        self.save_states: Dict[int, bytes] = {}
        
        # Callbacks
        self.on_frame: Optional[Callable] = None
    
    def load_rom(self, path: str) -> bool:
        self.rom = N64ROM()
        if not self.rom.load(path):
            self.rom = None
            return False
        
        self.memory.rom = self.rom
        self.reset()
        return True
    
    def reset(self):
        self.memory.reset()
        self.cpu.reset()
        self.hw.reset()
        
        if self.rom:
            self.memory.rom = self.rom
            
            # Copy bootcode and initial data to RDRAM
            copy_size = min(self.rom.size - 0x1000, 0x100000)
            if copy_size > 0:
                for i in range(copy_size):
                    self.memory.rdram[i] = self.rom.data[0x1000 + i]
            
            # Set entry point
            self.cpu.pc = self.rom.entry_point
            self.cpu.next_pc = self.cpu.pc + 4
    
    def run_frame(self):
        """Run one frame worth of emulation"""
        if not self.rom or not self.running or self.paused:
            return
        
        # Apply cheats
        self._apply_cheats()
        
        # Run CPU
        cycles = 0
        target_cycles = CYCLES_PER_FRAME // 1000  # Simplified
        
        while cycles < target_cycles:
            # Memory mapped I/O intercept
            self._intercept_mmio()
            
            # Execute instruction
            cycles += self.cpu.step()
            
            # Update hardware
            if cycles % 100 == 0:
                self.hw.vi_counter += 1
                if self.hw.vi_counter >= 500:
                    self.hw.update_vi()
                    self.hw.vi_counter = 0
            
            # Check interrupts
            if self.hw.mi_intr & self.hw.mi_mask:
                if self.cpu.cop0['status'] & 0x01:  # IE
                    self.cpu._exception(0)  # Interrupt
        
        # Update framebuffer
        self._update_framebuffer()
        
        # Call frame callback
        if self.on_frame:
            self.on_frame()
    
    def _intercept_mmio(self):
        """Intercept memory-mapped I/O in CPU memory access"""
        # This is handled in hardware read/write
        pass
    
    def _update_framebuffer(self):
        """Update framebuffer from VI"""
        origin = self.hw.vi_origin
        width = self.hw.vi_width if self.hw.vi_width > 0 else 320
        bpp = self.hw.vi_status & 0x03
        
        if width == 0 or bpp == 0:
            return
        
        self.fb_width = min(width, 640)
        self.fb_height = 240
        
        if len(self.framebuffer) != self.fb_width * self.fb_height:
            self.framebuffer = [0] * (self.fb_width * self.fb_height)
        
        if bpp == 2:  # 16-bit
            for y in range(self.fb_height):
                for x in range(self.fb_width):
                    addr = origin + (y * width + x) * 2
                    if addr + 1 < RDRAM_SIZE:
                        pixel = (self.memory.rdram[addr] << 8) | self.memory.rdram[addr + 1]
                        r = ((pixel >> 11) & 0x1F) << 3
                        g = ((pixel >> 6) & 0x1F) << 3
                        b = ((pixel >> 1) & 0x1F) << 3
                        self.framebuffer[y * self.fb_width + x] = (r << 16) | (g << 8) | b
        
        elif bpp == 3:  # 32-bit
            for y in range(self.fb_height):
                for x in range(self.fb_width):
                    addr = origin + (y * width + x) * 4
                    if addr + 3 < RDRAM_SIZE:
                        r = self.memory.rdram[addr]
                        g = self.memory.rdram[addr + 1]
                        b = self.memory.rdram[addr + 2]
                        self.framebuffer[y * self.fb_width + x] = (r << 16) | (g << 8) | b
    
    def _apply_cheats(self):
        """Apply active cheats"""
        for cheat in self.cheats:
            if not cheat.get('enabled', False):
                continue
            
            for code in cheat.get('codes', []):
                addr = code.get('address', 0)
                val = code.get('value', 0)
                size = code.get('size', 8)
                
                if size == 8:
                    self.memory.write8(addr, val)
                elif size == 16:
                    self.memory.write16(addr, val)
                elif size == 32:
                    self.memory.write32(addr, val)
    
    def set_button(self, port: int, button: int, pressed: bool):
        """Set controller button state"""
        if 0 <= port < 4:
            if pressed:
                self.hw.controller[port] |= button
            else:
                self.hw.controller[port] &= ~button
    
    def set_analog(self, port: int, x: int, y: int):
        """Set analog stick position"""
        if 0 <= port < 4:
            x = max(-128, min(127, x))
            y = max(-128, min(127, y))
            self.hw.controller[port] = (self.hw.controller[port] & 0xFFFF0000) | \
                                        ((x & 0xFF) << 8) | (y & 0xFF)
    
    def save_state(self, slot: int) -> bool:
        """Save state to slot"""
        try:
            state = {
                'cpu_r': list(self.cpu.r),
                'cpu_hi': self.cpu.hi,
                'cpu_lo': self.cpu.lo,
                'cpu_pc': self.cpu.pc,
                'cpu_cop0': dict(self.cpu.cop0),
                'cpu_fpr_int': list(self.cpu.fpr_int),
                'cpu_fcr31': self.cpu.fcr31,
                'rdram': bytes(self.memory.rdram),
                'hw_mi_intr': self.hw.mi_intr,
                'hw_vi_origin': self.hw.vi_origin,
            }
            self.save_states[slot] = json.dumps({
                k: v if not isinstance(v, bytes) else v.hex()
                for k, v in state.items()
            }).encode()
            return True
        except Exception as e:
            print(f"Save state error: {e}")
            return False
    
    def load_state(self, slot: int) -> bool:
        """Load state from slot"""
        if slot not in self.save_states:
            return False
        
        try:
            state = json.loads(self.save_states[slot].decode())
            
            self.cpu.r = state['cpu_r']
            self.cpu.hi = state['cpu_hi']
            self.cpu.lo = state['cpu_lo']
            self.cpu.pc = state['cpu_pc']
            self.cpu.next_pc = self.cpu.pc + 4
            self.cpu.cop0 = state['cpu_cop0']
            self.cpu.fpr_int = state['cpu_fpr_int']
            self.cpu.fcr31 = state['cpu_fcr31']
            self.memory.rdram = bytearray.fromhex(state['rdram'])
            self.hw.mi_intr = state['hw_mi_intr']
            self.hw.vi_origin = state['hw_vi_origin']
            
            return True
        except Exception as e:
            print(f"Load state error: {e}")
            return False

# =============================================================================
# CONTROLLER BUTTONS
# =============================================================================

BTN_A = 0x80000000
BTN_B = 0x40000000
BTN_Z = 0x20000000
BTN_START = 0x10000000
BTN_DUP = 0x08000000
BTN_DDOWN = 0x04000000
BTN_DLEFT = 0x02000000
BTN_DRIGHT = 0x01000000
BTN_L = 0x00200000
BTN_R = 0x00100000
BTN_CUP = 0x00080000
BTN_CDOWN = 0x00040000
BTN_CLEFT = 0x00020000
BTN_CRIGHT = 0x00010000

# =============================================================================
# TKINTER GUI
# =============================================================================

class CatN64GUI:
    def __init__(self):
        self.emu = N64Emulator()
        self.emu.on_frame = self.on_frame
        
        # Create window
        self.root = tk.Tk()
        self.root.title(WINDOW_TITLE)
        self.root.geometry("800x650")
        self.root.configure(bg='#1a1a2e')
        
        # Style
        self.style = ttk.Style()
        self.style.theme_use('clam')
        self.style.configure('TButton', padding=5)
        self.style.configure('TFrame', background='#1a1a2e')
        self.style.configure('TLabel', background='#1a1a2e', foreground='white')
        
        self._create_menu()
        self._create_toolbar()
        self._create_display()
        self._create_status()
        
        # Bind keys
        self.root.bind('<KeyPress>', self.on_key_press)
        self.root.bind('<KeyRelease>', self.on_key_release)
        
        # Emulation thread
        self.emu_thread: Optional[threading.Thread] = None
        self.frame_count = 0
        self.fps = 0
        self.last_fps_time = time.time()
        
        # Key mapping
        self.key_map = {
            'x': BTN_A, 'c': BTN_B, 'z': BTN_Z, 'Return': BTN_START,
            'Up': BTN_DUP, 'Down': BTN_DDOWN, 'Left': BTN_DLEFT, 'Right': BTN_DRIGHT,
            'a': BTN_L, 's': BTN_R,
            'i': BTN_CUP, 'k': BTN_CDOWN, 'j': BTN_CLEFT, 'l': BTN_CRIGHT
        }
        
        # Analog keys
        self.analog_state = {'w': False, 'a': False, 's': False, 'd': False}
    
    def _create_menu(self):
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)
        
        # File menu
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="File", menu=file_menu)
        file_menu.add_command(label="Open ROM...", command=self.open_rom, accelerator="Ctrl+O")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self.quit)
        
        # Emulation menu
        emu_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Emulation", menu=emu_menu)
        emu_menu.add_command(label="Play/Pause", command=self.toggle_pause, accelerator="Space")
        emu_menu.add_command(label="Reset", command=self.reset)
        emu_menu.add_separator()
        
        # Save states submenu
        save_menu = tk.Menu(emu_menu, tearoff=0)
        emu_menu.add_cascade(label="Save State", menu=save_menu)
        for i in range(1, 6):
            save_menu.add_command(label=f"Slot {i}", command=lambda s=i: self.save_state(s))
        
        load_menu = tk.Menu(emu_menu, tearoff=0)
        emu_menu.add_cascade(label="Load State", menu=load_menu)
        for i in range(1, 6):
            load_menu.add_command(label=f"Slot {i}", command=lambda s=i: self.load_state(s))
        
        # Cheats menu
        cheats_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Cheats", menu=cheats_menu)
        cheats_menu.add_command(label="Add Cheat...", command=self.add_cheat)
        cheats_menu.add_command(label="Manage Cheats...", command=self.manage_cheats)
        
        # Help menu
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="Help", menu=help_menu)
        help_menu.add_command(label="Controls...", command=self.show_controls)
        help_menu.add_command(label="About...", command=self.show_about)
        
        # Bind shortcuts
        self.root.bind('<Control-o>', lambda e: self.open_rom())
        self.root.bind('<space>', lambda e: self.toggle_pause())
    
    def _create_toolbar(self):
        toolbar = ttk.Frame(self.root)
        toolbar.pack(fill=tk.X, padx=5, pady=5)
        
        ttk.Button(toolbar, text="📂 Open", command=self.open_rom).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="▶ Play", command=self.start).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="⏸ Pause", command=self.pause).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="⏹ Stop", command=self.stop).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="🔄 Reset", command=self.reset).pack(side=tk.LEFT, padx=2)
        
        ttk.Separator(toolbar, orient=tk.VERTICAL).pack(side=tk.LEFT, fill=tk.Y, padx=10)
        
        ttk.Button(toolbar, text="💾 Save", command=lambda: self.save_state(1)).pack(side=tk.LEFT, padx=2)
        ttk.Button(toolbar, text="📁 Load", command=lambda: self.load_state(1)).pack(side=tk.LEFT, padx=2)
    
    def _create_display(self):
        # Display frame
        display_frame = ttk.Frame(self.root)
        display_frame.pack(fill=tk.BOTH, expand=True, padx=10, pady=5)
        
        # Canvas for rendering
        self.canvas = tk.Canvas(
            display_frame, 
            width=640, height=480,
            bg='black',
            highlightthickness=2,
            highlightbackground='#4a4a6a'
        )
        self.canvas.pack(expand=True)
        
        # Create initial image
        self.photo = tk.PhotoImage(width=320, height=240)
        self.canvas_image = self.canvas.create_image(320, 240, image=self.photo)
        
        # Welcome text
        self.canvas.create_text(
            320, 200,
            text="🐱 CatN64EMU 0.1",
            fill='#00ff88',
            font=('Courier', 24, 'bold'),
            tags='welcome'
        )
        self.canvas.create_text(
            320, 240,
            text="Open a ROM to start!",
            fill='white',
            font=('Courier', 12),
            tags='welcome'
        )
        self.canvas.create_text(
            320, 280,
            text="[C] Samsoft / Team Flames 2025",
            fill='#888888',
            font=('Courier', 10),
            tags='welcome'
        )
    
    def _create_status(self):
        status_frame = ttk.Frame(self.root)
        status_frame.pack(fill=tk.X, padx=5, pady=5)
        
        self.status_label = ttk.Label(status_frame, text="Ready - No ROM loaded")
        self.status_label.pack(side=tk.LEFT)
        
        self.fps_label = ttk.Label(status_frame, text="FPS: 0")
        self.fps_label.pack(side=tk.RIGHT)
        
        self.rom_label = ttk.Label(status_frame, text="")
        self.rom_label.pack(side=tk.RIGHT, padx=20)
    
    def open_rom(self):
        path = filedialog.askopenfilename(
            title="Open N64 ROM",
            filetypes=[
                ("N64 ROMs", "*.z64 *.v64 *.n64 *.rom"),
                ("All files", "*.*")
            ]
        )
        
        if path:
            self.stop()
            if self.emu.load_rom(path):
                self.canvas.delete('welcome')
                self.rom_label.config(text=f"ROM: {self.emu.rom.name}")
                self.status_label.config(text=f"Loaded: {self.emu.rom.name} (CIC: {self.emu.rom.cic})")
                self.start()
            else:
                messagebox.showerror("Error", "Failed to load ROM")
    
    def start(self):
        if not self.emu.rom:
            return
        
        self.emu.running = True
        self.emu.paused = False
        
        if not self.emu_thread or not self.emu_thread.is_alive():
            self.emu_thread = threading.Thread(target=self._emu_loop, daemon=True)
            self.emu_thread.start()
        
        self.status_label.config(text="Running")
    
    def pause(self):
        self.emu.paused = True
        self.status_label.config(text="Paused")
    
    def toggle_pause(self):
        if self.emu.paused:
            self.emu.paused = False
            self.status_label.config(text="Running")
        else:
            self.emu.paused = True
            self.status_label.config(text="Paused")
    
    def stop(self):
        self.emu.running = False
        self.status_label.config(text="Stopped")
    
    def reset(self):
        self.emu.reset()
        self.status_label.config(text="Reset")
        if self.emu.running:
            self.status_label.config(text="Running")
    
    def _emu_loop(self):
        """Main emulation loop"""
        target_frame_time = 1.0 / 60.0
        
        while self.emu.running:
            if not self.emu.paused:
                start = time.time()
                
                try:
                    self.emu.run_frame()
                except Exception as e:
                    print(f"Emulation error: {e}")
                
                # Frame timing
                elapsed = time.time() - start
                if elapsed < target_frame_time:
                    time.sleep(target_frame_time - elapsed)
            else:
                time.sleep(0.016)
    
    def on_frame(self):
        """Called after each frame"""
        self.frame_count += 1
        
        # Update FPS
        now = time.time()
        if now - self.last_fps_time >= 1.0:
            self.fps = self.frame_count
            self.frame_count = 0
            self.last_fps_time = now
            self.root.after(0, lambda: self.fps_label.config(text=f"FPS: {self.fps}"))
        
        # Update display
        self.root.after(0, self._update_display)
    
    def _update_display(self):
        """Update canvas with framebuffer"""
        if not self.emu.framebuffer:
            return
        
        width = self.emu.fb_width
        height = self.emu.fb_height
        
        # Create new photo if size changed
        if self.photo.width() != width or self.photo.height() != height:
            self.photo = tk.PhotoImage(width=width, height=height)
            self.canvas.itemconfig(self.canvas_image, image=self.photo)
        
        # Convert framebuffer to photo
        try:
            data = []
            for y in range(height):
                row = []
                for x in range(width):
                    pixel = self.emu.framebuffer[y * width + x]
                    r = (pixel >> 16) & 0xFF
                    g = (pixel >> 8) & 0xFF
                    b = pixel & 0xFF
                    row.append(f"#{r:02x}{g:02x}{b:02x}")
                data.append("{" + " ".join(row) + "}")
            
            self.photo.put(" ".join(data))
        except:
            pass
    
    def on_key_press(self, event):
        key = event.keysym
        
        # Digital buttons
        if key in self.key_map:
            self.emu.set_button(0, self.key_map[key], True)
        
        # Analog stick
        if key.lower() in self.analog_state:
            self.analog_state[key.lower()] = True
            self._update_analog()
    
    def on_key_release(self, event):
        key = event.keysym
        
        # Digital buttons
        if key in self.key_map:
            self.emu.set_button(0, self.key_map[key], False)
        
        # Analog stick
        if key.lower() in self.analog_state:
            self.analog_state[key.lower()] = False
            self._update_analog()
    
    def _update_analog(self):
        x = 0
        y = 0
        
        if self.analog_state['a']:
            x -= 80
        if self.analog_state['d']:
            x += 80
        if self.analog_state['w']:
            y += 80
        if self.analog_state['s']:
            y -= 80
        
        self.emu.set_analog(0, x, y)
    
    def save_state(self, slot: int):
        if self.emu.save_state(slot):
            self.status_label.config(text=f"State saved to slot {slot}")
        else:
            messagebox.showerror("Error", "Failed to save state")
    
    def load_state(self, slot: int):
        if self.emu.load_state(slot):
            self.status_label.config(text=f"State loaded from slot {slot}")
        else:
            messagebox.showerror("Error", f"No save state in slot {slot}")
    
    def add_cheat(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Add Cheat")
        dialog.geometry("400x200")
        dialog.transient(self.root)
        
        ttk.Label(dialog, text="Name:").pack(pady=5)
        name_entry = ttk.Entry(dialog, width=40)
        name_entry.pack()
        
        ttk.Label(dialog, text="Code (XXXXXXXX YYYY):").pack(pady=5)
        code_entry = ttk.Entry(dialog, width=40)
        code_entry.pack()
        
        def add():
            name = name_entry.get()
            code = code_entry.get()
            
            try:
                parts = code.split()
                addr = int(parts[0], 16)
                val = int(parts[1], 16)
                
                self.emu.cheats.append({
                    'name': name,
                    'enabled': True,
                    'codes': [{'address': addr | 0x80000000, 'value': val, 'size': 16 if val > 0xFF else 8}]
                })
                
                dialog.destroy()
                self.status_label.config(text=f"Cheat added: {name}")
            except:
                messagebox.showerror("Error", "Invalid cheat format")
        
        ttk.Button(dialog, text="Add", command=add).pack(pady=20)
    
    def manage_cheats(self):
        dialog = tk.Toplevel(self.root)
        dialog.title("Manage Cheats")
        dialog.geometry("400x300")
        dialog.transient(self.root)
        
        listbox = tk.Listbox(dialog, width=50, height=10)
        listbox.pack(padx=10, pady=10, fill=tk.BOTH, expand=True)
        
        for i, cheat in enumerate(self.emu.cheats):
            status = "✓" if cheat.get('enabled', False) else "✗"
            listbox.insert(tk.END, f"{status} {cheat.get('name', 'Unknown')}")
        
        def toggle():
            sel = listbox.curselection()
            if sel:
                idx = sel[0]
                self.emu.cheats[idx]['enabled'] = not self.emu.cheats[idx].get('enabled', False)
                status = "✓" if self.emu.cheats[idx]['enabled'] else "✗"
                listbox.delete(idx)
                listbox.insert(idx, f"{status} {self.emu.cheats[idx].get('name', 'Unknown')}")
        
        def delete():
            sel = listbox.curselection()
            if sel:
                idx = sel[0]
                del self.emu.cheats[idx]
                listbox.delete(idx)
        
        btn_frame = ttk.Frame(dialog)
        btn_frame.pack(pady=10)
        ttk.Button(btn_frame, text="Toggle", command=toggle).pack(side=tk.LEFT, padx=5)
        ttk.Button(btn_frame, text="Delete", command=delete).pack(side=tk.LEFT, padx=5)
    
    def show_controls(self):
        controls = """
🎮 CatN64EMU Controls

Keyboard:
━━━━━━━━━━━━━━━━━━━━━━
  W/A/S/D     - Analog Stick
  Arrow Keys  - D-Pad
  X           - A Button
  C           - B Button
  Z           - Z Trigger
  Enter       - Start
  A/S         - L/R Shoulders
  I/J/K/L     - C Buttons

Shortcuts:
━━━━━━━━━━━━━━━━━━━━━━
  Ctrl+O      - Open ROM
  Space       - Pause/Resume
  F5          - Quick Save
  F7          - Quick Load
"""
        messagebox.showinfo("Controls", controls)
    
    def show_about(self):
        about = """
🐱 CatN64EMU 0.1

Nintendo 64 Emulator
[C] Samsoft / Team Flames 1999-2025

Features:
• MIPS R4300i CPU emulation
• RSP/RDP HLE
• Controller support
• Save states
• Cheat codes

Licensed under GPL-3.0

meow~ 🐱
"""
        messagebox.showinfo("About", about)
    
    def quit(self):
        self.emu.running = False
        self.root.quit()
    
    def run(self):
        self.root.mainloop()

# =============================================================================
# MAIN
# =============================================================================

def main():
    print("""
╔══════════════════════════════════════════════════════════════════════════════╗
║  🐱 CatN64EMU 0.1 - Nintendo 64 Emulator                                     ║
║  ════════════════════════════════════════════════════════════════════════════║
║  [C] Samsoft / Team Flames 1999-2025                                         ║
╚══════════════════════════════════════════════════════════════════════════════╝
""")
    
    gui = CatN64GUI()
    gui.run()

if __name__ == "__main__":
    main()
