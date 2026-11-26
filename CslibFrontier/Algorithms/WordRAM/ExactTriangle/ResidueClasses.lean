/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.Classes
public import CslibFrontier.Algorithms.WordRAM.ThreeSum.ChanHe.Residues
public import CslibFrontier.Computability.WordRAM.Compile
public import Mathlib.Data.List.GetD
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Initialized signed weights to native residue classes

The flat input is an unsigned `(n,p)` header followed by the signed encodings of the three
`n×n` weight matrices. Native arithmetic allocates a residue array, class counts and disjoint
query blocks. The existing signed residue kernel processes every weight before the class scanner
reads the A–B residues. Neither residues nor class/layout tables are input certificates.

## Main definitions

* `ResidueClasses.input`: the mixed unsigned-header/signed-weight encoding.
* `ResidueClasses.programAt`: the same preparation at a fixed caller header offset.
* `ResidueClasses.program`: fixed thirty-two-register native preparation.
* `ResidueClasses.addressBound`: explicit arithmetic and allocation bound.

## Main results

* `ResidueClasses.exec_at`: callable execution from a fixed caller header.
* `ResidueClasses.exec_input`: initialized execution, residues, class counts, queries and frame.
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.ResidueClasses

open Cslib.WordRAM

open Cslib.Algorithms.WordRAM.ThreeSum.ChanHe

/-- Header cursor and class-scanner source register. -/
abbrev temp : Fin 32 := 0
/-- Class-scanner side register. -/
abbrev scanSize : Fin 32 := 2
/-- Signed-residue source register. -/
abbrev weightSrc : Fin 32 := 9
/-- Signed-residue destination register. -/
abbrev weightDst : Fin 32 := 10
/-- Signed-residue length register. -/
abbrev weightLen : Fin 32 := 11
/-- Signed modulus and subsequent class-count pointer register. -/
abbrev encodedMod : Fin 32 := 12
/-- Class-scanner query pointer register. -/
abbrev scanQueries : Fin 32 := 13
/-- Class-scanner modulus register. -/
abbrev scanModulus : Fin 32 := 14

/-- Unsigned side length. -/
abbrev size : Fin 32 := 24
/-- Unsigned positive modulus. -/
abbrev modulus : Fin 32 := 25
/-- Start of the signed weights. -/
abbrev weights : Fin 32 := 26
/-- Start of all three unsigned residue matrices. -/
abbrev residues : Fin 32 := 27
/-- Start of the computed class-count array. -/
abbrev counts : Fin 32 := 28
/-- Start of the class query blocks. -/
abbrev queries : Fin 32 := 29
/-- Area of one weight matrix. -/
abbrev area : Fin 32 := 30
/-- Constant one, preserved by both callees. -/
abbrev one : Fin 32 := 31

/-- Header followed by the three signed weight matrices in A–B, B–C, A–C order. -/
def input (n p : ℕ) (values : List ℤ) : List ℕ := [n, p] ++ values.map Signed.encode

/-- A fitting value covering every allocation endpoint and temporary for a caller header.
The adjacent header cells contain `n,p`, followed by the three signed matrices. -/
def addressBoundAt (header n p : ℕ) : ℕ :=
  header + 2 + 6 * (n * n) + p + 2 * (n * n) * p + 4

/-- The standard input places its `n,p` header immediately after the machine's length cell. -/
def addressBound (n p : ℕ) : ℕ := addressBoundAt 1 n p

private abbrev bank (r : ℕ) (hr : r ≤ 24) : Fin r → Fin 32 := Fin.castLE (by omega)

private theorem bank_injective (r : ℕ) (hr : r ≤ 24) : (bank r hr).Injective :=
  fun _ _ h => Fin.ext (congrArg (fun k : Fin 32 => k.val) h)

/-- The existing signed residue conversion, including unsigned decoding of each remainder. -/
def reduce : Code .standard 32 := Residues.program.rename (Fin.castLE (by decide))

/-- Reuse the complete native class scanner. -/
def classify : Code .standard 32 := Classes.program.rename (Fin.castLE (by decide))

/-- Read a fixed caller header and compute all array bases, lengths and the encoded modulus.
The offset is a code parameter; the complete ET caller uses one fixed input format. -/
def setupAt (header : ℕ) : Code .standard 32 := ram[
  one ← #1; temp ← #header; size ← *temp; temp ← temp + one; modulus ← *temp;
  weights ← #(header + 2); area ← size * size; weightLen ← area + area;
  weightLen ← weightLen + area;
  weightSrc ← weights; weightDst ← weights + weightLen; residues ← weightDst;
  counts ← residues + weightLen; queries ← counts + modulus; encodedMod ← modulus + modulus ]

/-- Read the standard initialized input header. -/
def setup : Code .standard 32 := setupAt 1

/-- Deliver the five actual scanner arguments after residue conversion. -/
def deliver : Code .standard 32 := ram[
  temp ← residues; scanSize ← size; encodedMod ← counts;
  scanQueries ← queries; scanModulus ← modulus ]

/-- Native setup, reduction and enumeration for a fixed caller header. -/
def programAt (header : ℕ) : Code .standard 32 :=
  .seq (setupAt header) (.seq reduce (.seq deliver classify))

/-- All setup, reduction and enumeration is native code. -/
def program : Code .standard 32 := programAt 1

/-- Changing the fixed header offset changes constants but not the instruction graph. -/
theorem programAt_fixed (header : ℕ) :
    (programAt header).size ≤ 160 ∧ ¬(programAt header).ReadsWidth := by
  change (programAt 0).size ≤ 160 ∧ ¬(programAt 0).ReadsWidth
  decide

/-- Fixed instruction graph, independent of dimensions and physical width. -/
theorem program_fixed : program.size ≤ 160 ∧ ¬program.ReadsWidth := by decide

private theorem input_weight (n p : ℕ) (values : List ℤ) (q : ℕ) :
    (Data.init (input n p values) : Data 32).mem (3 + q) = Signed.encode (values.getD q 0) := by
  rw [show 3 + q = (q + 2) + 1 by omega, Data.init_mem_succ]
  simp only [input, List.getD_eq_getElem?_getD, List.getElem?_cons_succ,
    List.cons_append, List.nil_append, List.getElem?_map]
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_map,
    Signed.encode, Int.natAbs_zero, lt_self_iff_false,
    ↓reduceIte, Nat.mul_zero, Nat.add_zero] using (List.getD_map values (n := q) Signed.encode
      (d := (0 : ℤ)))

/-- Callable residue/class preparation from a concrete caller header and signed matrix words.
The fixed offset selects the adjacent `n,p` cells; no initialized-memory shape is assumed outside
that payload. The cost and output frame include every setup, signed reduction and class scan. -/
theorem exec_at {w : ℕ} (header n p : ℕ) (values : ℕ → ℤ) (initial : Data 32)
    (hnHeader : initial.mem header = n) (hpHeader : initial.mem (header + 1) = p)
    (hinput : ∀ q < 3 * (n * n),
      initial.mem (header + 2 + q) = Signed.encode (values q))
    (hp : 0 < p) (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (haddress : Fits (w + 2) (addressBoundAt header n p)) :
    let base := header + 2
    ∃ y, ExecWithin (w + 2) (programAt header) initial y
        (69 * (n * n) + p * (14 * (n * n) + 14) + 30) ∧
      y.regs residues = base + 3 * (n * n) ∧ y.regs counts = base + 6 * (n * n) ∧
      y.regs queries = base + 6 * (n * n) + p ∧
      (∀ q < 3 * (n * n), y.mem (base + 3 * (n * n) + q) =
        (values q % (p : ℤ)).toNat) ∧
      (∀ j < p, y.mem (base + 6 * (n * n) + j) =
        Nat.count (fun q => (values q % (p : ℤ)).toNat = j) (n * n)) ∧
      (∀ j < p, ∀ q < n * n, (values q % (p : ℤ)).toNat = j →
        y.mem (base + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values k % (p : ℤ)).toNat = j) q) = q / n ∧
        y.mem (base + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values k % (p : ℤ)).toNat = j) q + 1) = q % n) ∧
      (∀ a, a < base + 3 * (n * n) ∨
        base + 6 * (n * n) + p + 2 * (n * n) * p ≤ a →
          y.mem a = initial.mem a) := by
  let N := n * n
  let base := header + 2
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  change Fits (w + 2) (base + 6 * N + p + 2 * N * p + 4) at haddress
  have h1 : Fits (w + 2) 1 := haddress.of_le (by omega)
  have hmodfit : Fits (w + 2) (p + p) := by
    have h := (Signed.encode_fits hmod).mono (show w + 1 ≤ w + 2 by omega)
    simpa [Signed.encode, two_mul, show ¬(p : ℤ) < 0 by omega] using h
  have hsizeFit : Fits (w + 2) n := haddress.of_le (by have : n ≤ N := Nat.le_mul_self n; omega)
  refine WP.exists_execWithin ?_
  unfold programAt setupAt reduce deliver classify
  wram_exec [hnHeader, hpHeader]
  wram_call (Residues.exec _ (fun q => values q) hp hmod
    (by wram_simp [Signed.encode, two_mul, show ¬(p : ℤ) < 0 by omega]; omega)
    (fun q hq => hvalues q (by wram_simp at hq; omega))
    (by wram_simp; exact haddress.of_le (by omega))
    (by wram_simp; exact haddress.of_le (by omega))
    (by wram_simp; omega)
    (fun q hq => by wram_simp at hq ⊢; exact hinput q (by omega)))
    canonical (bank_injective 16 (by decide)) with v ⟨hvm, -⟩
  wram_simp at hvm
  have hresmem (q : ℕ) (hq : q < 3 * N) : v.mem (base + 3 * N + q) = R q := by
    rw [hvm, Residues.memory, ite_eq_left (by omega),
      show base + 3 * N + q - (base + (N + N + N)) = q by omega]
  wram_exec
  wram_call (Classes.exec _ R h1
    (fun q hq => by
      wram_simp at hq ⊢
      rw [show base + (N + N + N) + q = base + 3 * N + q by omega]
      exact hresmem q (by omega))
    (by wram_simp; omega)
    (by wram_simp; omega)
    (by wram_simp; exact haddress.of_le (by dsimp [N] at *; omega))
    (by wram_simp; exact haddress.of_le (by dsimp [N] at *; omega))
    (by wram_simp; exact haddress.of_le (by dsimp [N] at *; omega)))
    canonical (bank_injective 20 (by decide)) with z ⟨-, hzcounts, hzpairs, hzframe⟩
  wram_simp at hzcounts hzpairs hzframe
  have hbase6 : base + (N + N + N) + (N + N + N) = base + 6 * N := by omega
  rw [hbase6] at hzcounts hzpairs hzframe
  refine ⟨by wram_simp; omega, by wram_simp; omega, by wram_simp; omega, by wram_simp; omega,
    fun q hq => ?_, hzcounts, hzpairs, fun a ha => ?_⟩
  · wram_simp; rw [hzframe _ (by omega) (by omega)]; exact hresmem q hq
  · wram_simp
    rw [hzframe a (by omega) (by omega), hvm, Residues.memory]
    exact ite_eq_right (by omega)

/-- Read the input header, compute all three residue matrices and enumerate the A–B queries.
The signed width is `w`, and execution uses the existing signed compiler's `w+2` unsigned width.
The cost includes every header, reduction, argument-delivery and class-scan instruction; the
final halt is excluded. This subroutine does not choose a prime or solve an instance. -/
theorem exec_input {w : ℕ} (n p : ℕ) (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < values.length, GenericRAM.Signed.Fits w (values.getD q 0))
    (haddress : Fits (w + 2) (addressBound n p)) :
    ∃ y, ExecWithin (w + 2) program (.init (input n p values)) y
        (69 * (n * n) + p * (14 * (n * n) + 14) + 30) ∧
      y.regs residues = 3 + 3 * (n * n) ∧ y.regs counts = 3 + 6 * (n * n) ∧
      y.regs queries = 3 + 6 * (n * n) + p ∧
      (∀ q < 3 * (n * n), y.mem (3 + 3 * (n * n) + q) =
        (values.getD q 0 % (p : ℤ)).toNat) ∧
      (∀ j < p, y.mem (3 + 6 * (n * n) + j) =
        Nat.count (fun q => (values.getD q 0 % (p : ℤ)).toNat = j) (n * n)) ∧
      (∀ j < p, ∀ q < n * n, (values.getD q 0 % (p : ℤ)).toNat = j →
        y.mem (3 + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values.getD k 0 % (p : ℤ)).toNat = j) q) = q / n ∧
        y.mem (3 + 6 * (n * n) + p + 2 * (n * n) * j +
          2 * Nat.count (fun k => (values.getD k 0 % (p : ℤ)).toNat = j) q + 1) = q % n) ∧
      (∀ a, a < 3 + 3 * (n * n) ∨
        3 + 6 * (n * n) + p + 2 * (n * n) * p ≤ a →
          y.mem a = (Data.init (input n p values) : Data 32).mem a) := by
  have h := exec_at (w := w) 1 n p (fun q => values.getD q 0) (.init (input n p values))
    (by simp [input, Data.init]) (by simp [input, Data.init])
    (fun q _ => input_weight n p values q) hp hmod
    (fun q hq => hvalues q (by simpa only [hlen] using hq)) haddress
  simpa only [program, Nat.reduceAdd] using h

end Cslib.Algorithms.WordRAM.ExactTriangle.ResidueClasses
