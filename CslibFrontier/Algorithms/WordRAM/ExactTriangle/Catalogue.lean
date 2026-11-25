/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.Call
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ChunkCatalogue
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.Parameters
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.ResidueClasses
import CslibFrontier.Computability.WordRAM.SymbolicExec.CanonicalCall
import CslibFrontier.Computability.WordRAM.SymbolicExec.Havoc
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame

/-!
# Computing an ExactTriangle instance catalogue

The fixed input format is `(D,g,n,p)` followed by the three signed weight matrices. The program
computes residues and query classes, computes the splitting parameters from `D,g,n`, and
concatenates the actual query-chunk descriptors. The caller supplies neither the parameters nor
a class, prefix or descriptor table. Subsequent matrix preparation consumes this catalogue.

This is native composition of the existing Theorem 17 residue, parameter, class and chunk
kernels. The modulus remains a supplied positive argument; prime selection belongs to the outer
ExactTriangle host.

## Main definitions

* `Catalogue.program`: fixed thirty-two-register native catalogue computation.
* `Catalogue.budget`: input-derived numeric bound for arithmetic and allocated addresses.
* `Catalogue.cost`: charged cost before the final halt.
* `Catalogue.Output`: computed parameters, residues, queries, descriptors and memory frame.

## Main results

* `Catalogue.exec_at`: actual execution from the fixed input header, exact parameters, residue
  and query readback, concatenated descriptors and a combined memory frame.

## References

The class/query layout follows the pinned
[Theorem 17 construction](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Programs/Sec3/Theorem17/Instances/Classes.lean).
The native composition and instruction bounds are original.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.Catalogue

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle

/-- Computed maximum vertices per piece, preserved by descriptor enumeration. -/
abbrev pieceLength : Fin 32 := 28
/-- Computed number of pieces, preserved by descriptor enumeration. -/
abbrev pieces : Fin 32 := 29

/-- Existing parameter computation in the lower register bank. -/
@[expose]
def parameters : Code .standard 32 := Parameters.program.rename (Fin.castLE (by decide))

/-- Internal argument delivery from the fixed `D,g,n,p` header. -/
@[expose]
def deliverParameters : Code .standard 32 :=
  let header : Fin 32 := 0
  let one : Fin 32 := 31
  let n : Fin 32 := 6
  let D : Fin 32 := 7
  let g : Fin 32 := 8
  ram[ one ← #1; header ← #1; D ← *header; header ← header + one;
    g ← *header; header ← header + one; n ← *header ]

/-- Internal argument delivery and allocation after the computed query blocks. Copying the
count/query pointers precedes overwriting their old registers with the computed piece data. -/
@[expose]
def deliverChunks : Code .standard 32 :=
  let n : Fin 32 := 6
  let cap : Fin 32 := 10
  let len : Fin 32 := 11
  let num : Fin 32 := 12
  let oldCounts : Fin 32 := 28
  let oldQueries : Fin 32 := 29
  let counts := ChunkCatalogue.counts
  let queries := ChunkCatalogue.queries
  let size := ChunkCatalogue.size
  let capacity := ChunkCatalogue.capacity
  let modulus := ChunkCatalogue.modulus
  let dst := ChunkCatalogue.dst
  let header := ChunkCatalogue.addr
  ram[ counts ← oldCounts; queries ← oldQueries; size ← n; capacity ← cap;
    pieceLength ← len; pieces ← num; header ← #4; modulus ← *header;
    dst ← size * size; dst ← dst + dst; dst ← dst * modulus; dst ← dst + queries ]

/-- All class, parameter and chunk work is performed by actual native instructions. -/
@[expose]
def program : Code .standard 32 :=
  .seq (ResidueClasses.programAt 3) (.seq deliverParameters
    (.seq parameters (.seq deliverChunks ChunkCatalogue.program)))

/-- One finite instruction graph, independent of runtime sizes and physical width. -/
theorem program_fixed : program.size ≤ 320 ∧ ¬program.ReadsWidth := by decide

/-- A single explicit bound covering the fourth-power square-root input, all ceiling
temporaries and the worst-case descriptor reservation. Signed payloads have a separate bound. -/
@[expose]
def budget (n D g p : ℕ) : ℕ :=
  4 * ((n * n) * (n * n)) + 20 * p * (n * n) + 30 * (n * n) +
    8 * D + 8 * g + 8 * n + 8 * p + 64

/-- Every setup, parameter, signed residue, class scan and descriptor instruction is charged;
the final halt is added by the flat caller. -/
@[expose]
def cost (n D p : ℕ) : ℕ :=
  69 * (n * n) + p * (31 * (n * n) + 34) +
    5 * sOf D + 5 * queryCap n D + 85

private abbrev bank : Fin 15 → Fin 32 := Fin.castLE (by decide)

private theorem bank_injective : Function.Injective bank := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 32 => k.val) h)

/-- Exact computed parameters, residue/query arrays, concatenated descriptors and memory
frame. This is the readback established by the actual native catalogue execution. -/
@[expose]
def Output (n D g p : ℕ) (values : ℕ → ℤ) (initial y : Data 32) : Prop :=
    let N := n * n
    let R := fun q => (values q % (p : ℤ)).toNat
    let C := fun rho => Nat.count (fun q => R q = rho) N
    let out := 5 + 6 * N + p + 2 * N * p
    y.regs ChunkCatalogue.size = n ∧ y.regs ChunkCatalogue.modulus = p ∧
    y.regs ChunkCatalogue.counts = 5 + 6 * N ∧
    y.regs ChunkCatalogue.queries = 5 + 6 * N + p ∧
    y.regs ChunkCatalogue.dst = out ∧
    y.regs ChunkCatalogue.capacity = queryCap n D ∧
    y.regs pieceLength = pieceSize D g ∧ y.regs pieces = numPieces n D g ∧
    y.regs ChunkCatalogue.written = ChunkCatalogue.before C (queryCap n D) p ∧
    y.regs ChunkCatalogue.heap = out + 3 * y.regs ChunkCatalogue.written ∧
    (∀ q < 3 * N, y.mem (5 + 3 * N + q) = R q) ∧
    (∀ rho < p, y.mem (5 + 6 * N + rho) = C rho) ∧
    (∀ rho < p, ∀ q < N, R q = rho →
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q) = q / n ∧
      y.mem (5 + 6 * N + p + 2 * N * rho +
        2 * Nat.count (fun k => R k = rho) q + 1) = q % n) ∧
    (∀ rho < p, ∀ k < C rho ⌈/⌉ queryCap n D,
      y.mem (out + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k)) = rho ∧
      y.mem (out + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 1) =
        5 + 6 * N + p + 2 * rho * N + 2 * (k * queryCap n D) ∧
      y.mem (out + 3 * (ChunkCatalogue.before C (queryCap n D) rho + k) + 2) =
        min (queryCap n D) (C rho - k * queryCap n D)) ∧
    (∀ a, a < 5 + 3 * N ∨ out + 3 * y.regs ChunkCatalogue.written ≤ a →
      y.mem a = initial.mem a)

/-- Prepare the actual catalogue at the fixed header, computing both splitting parameters and
every class/chunk. The result contains no supplied layout or execution certificates. The two
input-dependent fit premises cover ordinary signed values and the explicit numeric budget. -/
theorem exec_at {w : ℕ} (n D g p : ℕ) (values : ℕ → ℤ) (initial : Data 32)
    (hDHeader : initial.mem 1 = D) (hgHeader : initial.mem 2 = g)
    (hnHeader : initial.mem 3 = n) (hpHeader : initial.mem 4 = p)
    (hinput : ∀ q < 3 * (n * n), initial.mem (5 + q) = Signed.encode (values q))
    (hD : 1 ≤ D) (hDn : D ≤ n) (hg : 1 ≤ g) (hp : 0 < p)
    (hmod : GenericRAM.Signed.Fits w (p : ℤ))
    (hvalues : ∀ q < 3 * (n * n), GenericRAM.Signed.Fits w (values q))
    (hbudget : Fits (w + 2) (budget n D g p)) :
    ∃ y, ExecWithin (w + 2) program initial y (cost n D p) ∧
      Output n D g p values initial y := by
  let N := n * n
  let R (q : ℕ) := (values q % (p : ℤ)).toNat
  let C (rho : ℕ) := Nat.count (fun q => R q = rho) N
  let countBase := 5 + 6 * N
  let queryBase := countBase + p
  let out := queryBase + 2 * N * p
  change Fits (w + 2)
    (4 * (N * N) + 20 * p * N + 30 * N + 8 * D + 8 * g + 8 * n + 8 * p + 64) at hbudget
  have hs : sOf D ≤ D := Nat.sqrt_le_self D
  have hpiece : pieceSize D g ≤ D := (pieceSize_le_sOf hg).trans hs
  have hC : ∀ rho < p, C rho ≤ N := fun _ _ => Nat.count_le _
  refine WP.exists_execWithin ?_
  unfold program deliverParameters parameters deliverChunks
  refine WP.seq ?_
  wram_call (ResidueClasses.exec_at (w := w) 3 n p values initial hnHeader hpHeader hinput hp hmod
    hvalues (hbudget.of_le (by dsimp [ResidueClasses.addressBoundAt, N]; nlinarith only [])))
    with a ⟨har, hac, haq, hares, hacounts, hapairs, haframe⟩
  change a.regs ResidueClasses.counts = countBase at hac
  change a.regs ResidueClasses.queries = queryBase at haq
  have ha1 : a.mem 1 = D := (haframe 1 (Or.inl (by omega))).trans hDHeader
  have ha2 : a.mem 2 = g := (haframe 2 (Or.inl (by omega))).trans hgHeader
  have ha3 : a.mem 3 = n := (haframe 3 (Or.inl (by omega))).trans hnHeader
  have ha4 : a.mem 4 = p := (haframe 4 (Or.inl (by omega))).trans hpHeader
  wram_exec [ha1, ha2, ha3]
  wram_call (Parameters.exec ..) canonical bank_injective [hbudget.of_le, N]
    with c ⟨hvs, hvq, hvB, hvH, hvn, _, _, hvm⟩
  wram_simp at hvq hvB hvH hvn hvm
  have hc4 : c.mem 4 = p := (congrFun hvm 4).trans ha4
  have h2Np : Fits (w + 2) ((n * n + n * n) * p) := hbudget.of_le (by dsimp [N]; nlinarith only [])
  have hOut : Fits (w + 2) ((n * n + n * n) * p + queryBase) :=
    hbudget.of_le (by dsimp [N, queryBase, countBase]; nlinarith only [])
  wram_exec [hac, haq, hvn, hvq, hvB, hvH, hc4]
  have hout_eq : (n * n + n * n) * p + queryBase = out := by dsimp [out, N]; nlinarith only []
  have hq := one_le_queryCap hD hDn
  wram_call (ChunkCatalogue.exec _ C _ _ _ (by wram_simp; dsimp [queryBase]; omega)
    (by wram_simp; nlinarith only [])
    (by wram_simp; exact hbudget.of_le (by dsimp [queryBase, countBase, N]; nlinarith only [])))
    framed [hvm] with vy my ⟨hycount, hyheap, -, hycells, hyframe⟩
  rw [hout_eq] at hyheap hycells hyframe
  have hyold (a' : ℕ) (ha' : a' < out) : my a' = a.mem a' := hyframe a' (by omega)
  refine ⟨by wram_simp [cost, N]; ring_nf; omega,
    by wram_simp, by wram_simp, by wram_simp; rfl, by wram_simp; rfl,
    by wram_simp [hout_eq]; rfl, by wram_simp,
    by wram_simp, by wram_simp, by wram_simp [hycount]; rfl,
    by wram_simp [hyheap, hycount]; rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro q hq
    wram_simp
    exact (hyold _ (by dsimp [out, queryBase, countBase, N] at *; omega)).trans (hares q hq)
  · intro rho hrho
    wram_simp
    exact (hyold _ (by dsimp [out, queryBase, countBase, N] at *; omega)).trans (hacounts rho hrho)
  · intro rho hrho q hq hRq
    wram_simp
    have hcount : Nat.count (fun k => R k = rho) q ≤ q := Nat.count_le _
    have hbound := Nat.mul_le_mul_left (2 * N) (Nat.succ_le_of_lt hrho)
    rw [Nat.mul_succ] at hbound
    rw [hyold _ (by dsimp [out, queryBase, countBase, N, R] at *; omega),
        hyold _ (by dsimp [out, queryBase, countBase, N, R] at *; omega)]
    exact hapairs rho hrho q hq hRq
  · wram_simp; exact hycells
  · intro a' ha'
    wram_simp at ha' ⊢
    change a' < 5 + 3 * N ∨ out + 3 * vy ChunkCatalogue.written ≤ a' at ha'
    have hlt : 5 + 3 * N ≤ out := by dsimp only [out, queryBase, countBase]; omega
    rw [hyframe a' (by omega)]
    exact haframe a' (ha'.imp_right fun _ => by change out ≤ a'; omega)

end Cslib.Algorithms.WordRAM.ExactTriangle.Catalogue
