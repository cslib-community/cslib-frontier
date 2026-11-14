/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SDitH.PRG

/-! Checked functional clients for SDitH v3 Algorithm 6. -/

public section

namespace SDitHPRGTests

open Cslib Cslib.Crypto Cslib.Crypto.SDitH

/-- A toy 32-to-16-bit cipher shape. It combines each low input bit with the corresponding bit
16 positions above it, so both the low block counter and the shifted PRG tweak are observable. -/
def toyEnc (key input : BitString 32) : BitString 16 := fun i =>
  key ⟨i.val, by omega⟩ ^^ input ⟨i.val, by omega⟩ ^^ input ⟨i.val + 16, by omega⟩

/-- Parse the toy cipher output into two little-endian bytes. -/
def toyParse (block : BitString 16) : FixedBytes 2 := fun i =>
  BitString.equivFin 8 fun j => block ⟨8 * i.val + j.val, by omega⟩

def toySeed : BitString 32 := fun i => decide (i.val = 0 ∨ i.val = 9)

def zeroSalt : BitString 32 := fun _ => false

-- The unsalted stream uses the low little-endian counter bits and truncates the third block.
example : prg toyEnc toyParse toySeed .hashBased none 5 = [1, 2, 0, 2, 3] := by
  decide +kernel

-- Shifting tweak one by 16 toggles the first output bit in the salted stream.
example : prg toyEnc toyParse toySeed .hashBased (some (zeroSalt, (1 : Fin 256))) 3 =
    [0, 2, 1] := by
  decide +kernel

-- The functional output is prefix-consistent and has the requested length.
example : (prg toyEnc toyParse toySeed .hashBased none 5).take 3 =
    prg toyEnc toyParse toySeed .hashBased none 3 := by
  exact take_prg toyEnc toyParse toySeed .hashBased none (by norm_num) (by norm_num)

example : (prg toyEnc toyParse toySeed .hashBased none 5).length = 5 := by
  exact length_prg toyEnc toyParse toySeed .hashBased none (by norm_num) 5

example : prg toyEnc toyParse toySeed .hashBased none 0 = [] := by
  exact prg_zero_output toyEnc toyParse toySeed .hashBased none

/- The reference implementation resolves Algorithm 6's width discrepancy with 16-byte blocks in
Category I and full 32-byte Rijndael-256 blocks in Categories III and V. These shapes record that
choice without claiming an AES or Rijndael implementation. -/

def categoryIEncShape : BitString 128 → BitString 128 → BitString 128 := fun _ _ _ => false

def categoryIParseShape : BitString 128 → FixedBytes 16 := fun _ _ => 0

def categoryIIIEncShape : BitString 192 → BitString 192 → BitString 256 := fun _ _ _ => false

def categoryIIIParseShape : BitString 256 → FixedBytes 32 := fun _ _ => 0

example :
    (prgBlocks categoryIEncShape categoryIParseShape (fun _ => false) .hashBased none
      (33 ⌈/⌉ 16)).length = 3 := by
  decide +kernel

example :
    (prgBlocks categoryIIIEncShape categoryIIIParseShape (fun _ => false) .hashBased none
      (33 ⌈/⌉ 32)).length = 2 := by
  decide +kernel

end SDitHPRGTests
