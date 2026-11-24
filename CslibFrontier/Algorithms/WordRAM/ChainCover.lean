/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.ChainCover
public import CslibFrontier.Algorithms.WordRAM.HopcroftKarp
import CslibFrontier.Computability.WordRAM.Allocation
import CslibFrontier.Computability.WordRAM.CountingLoop
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.SymbolicExec
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Tactic.Linarith

/-!
# Dilworth minimum chain cover and maximum antichain on the word RAM

This file implements and proves `O(n^{5/2})` machine-level running-time bounds on the
standard-basis word RAM (`Basis.standard`) for Fulkerson's reduction of Dilworth's minimum chain
cover and maximum antichain to Hopcroft–Karp maximum bipartite matching:

* Given an `n × n` strict poset comparability matrix (`PosetInstance`, specialized to finite
  partial orders via `PosetInstance.ofEnum`), `chainLabelsProgram` and `maxAntichainProgram`
  build exact CSR neighbour lists in `O(n²)` instructions (`matrixSetupCode true`), run
  Hopcroft–Karp in `O(n^{5/2})` instructions (`coreCode` / `core_exec`), and then either merge
  chain labels in `O(n²)` instructions (`chainLabels_eq_foldl_rowMate`) or scan the König
  uncovered antichain in `O(n)` instructions (`foldl_uncoveredStep`), matching `minChainCover`.

## Main definitions

* `Cslib.Algorithms.WordRAM.ChainCover.PosetInstance`,
  `Cslib.Algorithms.WordRAM.ChainCover.PosetInstance.ofEnum`,
  `Cslib.Algorithms.WordRAM.ChainCover.PosetInstance.encode`,
  `Cslib.Algorithms.WordRAM.ChainCover.PosetInstance.chainLabelsList`,
  `Cslib.Algorithms.WordRAM.ChainCover.PosetInstance.antichainList`,
  `Cslib.Algorithms.WordRAM.ChainCover.PosetInstance.wordBound`: poset comparability problem
  instance, row-major encoding, outputs, and word-width envelope.
* `Cslib.Algorithms.WordRAM.ChainCover.chainLabelsProgram`,
  `Cslib.Algorithms.WordRAM.ChainCover.maxAntichainProgram`: `O(n^{5/2})` word-RAM programs.
* `Cslib.Algorithms.WordRAM.ChainCover.chainCoverTime`: instruction bound.

## Main results

* `Cslib.Algorithms.WordRAM.ChainCover.executesList_chainLabels`,
  `Cslib.Algorithms.WordRAM.ChainCover.computesListInTime_chainLabels`,
  `Cslib.Algorithms.WordRAM.ChainCover.executesList_maxAntichain`,
  `Cslib.Algorithms.WordRAM.ChainCover.computesListInTime_maxAntichain`: `O(n^{5/2})` minimum
  chain cover and maximum antichain endpoints.

## References

* [D. R. Fulkerson, *Note on Dilworth's decomposition theorem for partially ordered
  sets*][Fulkerson1956]
* [J. E. Hopcroft and R. M. Karp, *An n^{5/2} Algorithm for Maximum Matchings in Bipartite
  Graphs*][HopcroftKarp1973]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 7.3
-/

public section

namespace Cslib.Algorithms.WordRAM.ChainCover

open Cslib.WordRAM
open Cslib.Algorithms.Lean
open Cslib.Algorithms.Lean.MaxFlow
open Cslib.Algorithms.WordRAM.HopcroftKarp
open Cslib.Algorithms.WordRAM.HopcroftKarp.Reg

/-! ## Poset instances and encodings -/

/-- An `n`-element strict comparability relation `lt : Fin n × Fin n → Bool` for computing a
Dilworth minimum chain cover and maximum antichain on the word RAM. -/
structure PosetInstance where
  /-- Number of elements of the poset. -/
  n : ℕ
  /-- Strict comparability indicator `lt (i, j) = true` when element `i` is strictly below `j`. -/
  lt : Fin n × Fin n → Bool

namespace PosetInstance

/-- Construct a `PosetInstance` from an enumerated poset `e : Fin n ≃ α`. -/
@[expose] def ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    PosetInstance where
  n := n
  lt := enumLtGraph e

/-- Underlying `n × n` dense bipartite instance on `inst.lt`. -/
@[expose] def toDense (inst : PosetInstance) : DenseInstance where
  m := inst.n
  r := inst.n
  graph := inst.lt

/-- Row-major word encoding `n :: matrixWords` (`1 + n * n` words). -/
@[expose] def encode (inst : PosetInstance) : List ℕ :=
  inst.n :: (List.finRange inst.n).flatMap fun u =>
    (List.finRange inst.n).map fun v => if inst.lt (u, v) then 1 else 0

/-- Chain label list `[c₀, …, c_{n - 1}]` computed by Fulkerson's reduction on `inst.lt`. -/
@[expose] def chainLabelsList (inst : PosetInstance) : List ℕ :=
  let hk := hopcroftKarpDense inst.lt
  let lab := chainLabels hk.matching (List.finRange inst.n ×ˢ List.finRange inst.n)
    (Vector.ofFn id)
  (List.finRange inst.n).map fun i => (vget lab i).val

/-- Sorted index list of the König uncovered antichain of `inst.lt`. -/
@[expose] def antichainList (inst : PosetInstance) : List ℕ :=
  let hk := hopcroftKarpDense inst.lt
  ((List.finRange inst.n).filter fun i => decide (i ∈ hk.cover.uncovered)).map Fin.val

/-- Sufficient word-value envelope for `O(n^{5/2})` chain cover and antichain computation. -/
@[expose] def wordBound (inst : PosetInstance) : ℕ :=
  2 * inst.n * inst.n + 16 * inst.n + 16

theorem chainLabelsList_ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (ofEnum e).chainLabelsList =
      (List.finRange n).map fun i => (vget (minChainCover e).labels i).val := rfl

theorem antichainList_ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (ofEnum e).antichainList =
      ((List.finRange n).filter fun i => decide (i ∈ (minChainCover e).antichain)).map Fin.val := by
  have heq : (ofEnum e).lt = enumLtGraph e := rfl
  have hanti : (minChainCover e).antichain =
      (hopcroftKarpDense (enumLtGraph e)).cover.uncovered := by
    simp [minChainCover, foldl_uncoveredStep]
  dsimp only [antichainList]
  rw [heq]
  congr 1
  refine List.filter_congr fun i _ => ?_
  exact decide_eq_decide.mpr (by rw [hanti]; rfl)

theorem length_antichainList_ofEnum {α : Type*} {n : ℕ} [LT α] [DecidableLT α] (e : Fin n ≃ α) :
    (ofEnum e).antichainList.length = (minChainCover e).antichain.card := by
  rw [antichainList_ofEnum, List.length_map]
  have hnd : ((List.finRange n).filter fun i => decide (i ∈ (minChainCover e).antichain)).Nodup :=
    (List.nodup_finRange n).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp

theorem encode_length (inst : PosetInstance) :
    inst.encode.length = 1 + inst.n * inst.n := by
  simp only [encode, List.length_cons, List.length_flatMap, List.length_map, List.length_finRange,
    List.map_const', List.sum_replicate, smul_eq_mul]
  omega

private theorem init_mem_n {reg : ℕ} (inst : PosetInstance) :
    (Data.init inst.encode : Data reg).mem 1 = inst.n := rfl

private theorem init_mem_entry {reg : ℕ} (inst : PosetInstance) (u v : Fin inst.n) :
    (Data.init inst.encode : Data reg).mem (2 + (u.val * inst.n + v.val)) =
      if inst.lt (u, v) then 1 else 0 := by
  change (Data.init ([inst.n] ++ (List.finRange inst.n).flatMap fun u' =>
    (List.finRange inst.n).map fun v' => if inst.lt (u', v') then 1 else 0) : Data reg).mem
      ([inst.n].length + 1 + (u.val * inst.n + v.val)) = _
  exact Data.init_mem_flatMap_finRange [inst.n] (fun u' v' => if inst.lt (u', v') then 1 else 0)
    u v

theorem inputFits_encode {w : ℕ} (inst : PosetInstance) (hw : Fits w inst.wordBound) :
    InputFits w inst.encode := by
  rw [PosetInstance.encode, ← List.singleton_append]
  exact InputFits.flatMap_finRange [inst.n] (fun u v => if inst.lt (u, v) then 1 else 0)
    (hw.of_le (by simp only [List.length_singleton]; unfold wordBound; nlinarith))
    (fun x hx => by
      simp only [List.mem_singleton] at hx; subst hx
      exact hw.of_le (by unfold wordBound; nlinarith))
    (fun _ _ => by
      split_ifs
      · exact hw.of_le (by unfold wordBound; nlinarith)
      · exact fits_zero w)

end PosetInstance

/-! ## Scratch register aliases and Fulkerson core -/

private abbrev qHead : Fin 34 := ⟨22, by decide⟩
private abbrev qTail : Fin 34 := ⟨23, by decide⟩
private abbrev idx : Fin 34 := ⟨28, by decide⟩
private abbrev addr : Fin 34 := ⟨30, by decide⟩
private abbrev val : Fin 34 := ⟨31, by decide⟩
private abbrev val2 : Fin 34 := ⟨32, by decide⟩
private abbrev tmp : Fin 34 := ⟨33, by decide⟩

private def encodeOptFin {m : ℕ} : Option (Fin m) → ℕ
  | some u => u.val
  | none => m

private def posetCoreCode : Code .standard 34 :=
  .seq (matrixSetupCode true) coreCode

private def scatterRowMateBody : Code .standard 34 := ram[
  addr ← bColMateReg + idx; val ← *addr;
  if val < rm then [ addr ← bMLReg + val; *addr ← idx ] else [ tmp ← zero ];
  idx ← idx + one ]

private def scatterRowMateCode : Code .standard 34 :=
  .seq (Cslib.WordRAM.fillConst bMLReg rm rm one idx addr)
    (.seq (ram[ idx ← #0 ]) (.loop (.lt idx rm) scatterRowMateBody))

private def initLabelsBody : Code .standard 34 := ram[
  addr ← outBase + one; addr ← addr + idx; *addr ← idx;
  idx ← idx + one ]

private def initLabelsCode : Code .standard 34 :=
  .seq (ram[ addr ← outBase; *addr ← rm; idx ← #0 ])
    (.loop (.lt idx rm) initLabelsBody)

private def mergeInnerBody : Code .standard 34 := ram[
  addr ← outBase + one; addr ← addr + idx; tmp ← *addr;
  if tmp = val2 then [ *addr ← val ] else [ tmp ← zero ];
  idx ← idx + one ]

private def mergeBranchTrue : Code .standard 34 :=
  .seq (ram[ addr ← outBase + one; addr ← addr + qHead; val ← *addr;
             addr ← outBase + one; addr ← addr + qTail; val2 ← *addr;
             idx ← #0 ])
    (.loop (.lt idx rm) mergeInnerBody)

private def mergeOuterBody : Code .standard 34 :=
  .seq (ram[ addr ← bMLReg + qHead; qTail ← *addr ])
    (.seq (.branch (.lt qTail rm) mergeBranchTrue (ram[ tmp ← zero ]))
      (ram[ qHead ← qHead + one ]))

private def mergeLabelsCode : Code .standard 34 :=
  .seq (ram[ qHead ← #0 ]) (.loop (.lt qHead rm) mergeOuterBody)

private def chainLabelsTail : Code .standard 34 :=
  .seq scatterRowMateCode (.seq initLabelsCode mergeLabelsCode)

private def maxAntichainBody : Code .standard 34 := ram[
  addr ← bDistReg + idx; val ← *addr;
  if zero < val then [
    addr ← bColMateReg + idx; val2 ← *addr;
    if val2 < rm then [
      addr ← bDistReg + val2; tmp ← *addr
    ] else [
      tmp ← zero
    ];
    if tmp = zero then [
      addr ← outBase + one; addr ← addr + acc; *addr ← idx;
      acc ← acc + one
    ] else [ tmp ← zero ]
  ] else [ tmp ← zero ];
  idx ← idx + one ]

private def maxAntichainTail : Code .standard 34 :=
  .seq (ram[ acc ← #0; idx ← #0 ])
    (.seq (.loop (.lt idx rm) maxAntichainBody)
      (ram[ addr ← outBase; *addr ← acc ]))

/-- Standard-basis word-RAM program computing `inst.chainLabelsList` (`ExecutesList`) in
`O(n^{5/2})` instructions via Fulkerson's bipartite matching reduction. -/
def chainLabelsProgram : Program .standard 34 :=
  (posetCoreCode.seq chainLabelsTail).program outBase

/-- Standard-basis word-RAM program computing the König uncovered maximum antichain
`inst.antichainList` (`ExecutesList`) in `O(n^{5/2})` instructions. -/
def maxAntichainProgram : Program .standard 34 :=
  (posetCoreCode.seq maxAntichainTail).program outBase

/-- Instruction bound `O(n^{5/2})` for `chainLabelsProgram` and `maxAntichainProgram`. -/
@[expose] def chainCoverTime (n : ℕ) : ℕ :=
  (2 * Nat.sqrt n + 1) * (112 * n * n + 147 * n + 48) +
    19 * n * n + 48 * n + 62

private def rowMateOf {n : ℕ} (mate : Vector (Option (Fin n)) n) (i : Fin n) : Option (Fin n) :=
  (List.finRange n).find? fun j => decide (vget mate j = some i)

private theorem rowMateOf_eq_some_iff {n : ℕ} {G : Fin n × Fin n → Bool}
    {mate : Vector (Option (Fin n)) n} (hM : IsMatching G (mateMatching mate))
    (i j : Fin n) : rowMateOf mate i = some j ↔ (i, j) ∈ mateMatching mate := by
  let p : Fin n → Bool := fun j' => decide (vget mate j' = some i)
  change (List.finRange n).find? p = some j ↔ (i, j) ∈ mateMatching mate
  constructor
  · intro hf
    have hp : p j = true := List.find?_some hf
    exact mem_mateMatching.mpr (of_decide_eq_true hp)
  · intro hm
    have hvj : vget mate j = some i := mem_mateMatching.mp hm
    cases hf : (List.finRange n).find? p with
    | none =>
      have hfalse := (List.find?_eq_none.mp hf) j (List.mem_finRange j)
      simp [p, hvj] at hfalse
    | some j₁ =>
      have hp₁ : p j₁ = true := List.find?_some hf
      have hvj₁ : vget mate j₁ = some i := of_decide_eq_true hp₁
      exact congrArg some (hM.2.1 i j₁ j (mem_mateMatching.mpr hvj₁) hm)

private abbrev posetSparse (inst : PosetInstance) : SparseInstance :=
  { m := inst.n, r := inst.n, adj := exactBipAdj inst.lt }

private abbrev posetLoopRes (inst : PosetInstance) :=
  hkLoop (posetSparse inst).graph (posetSparse inst).adj (inst.n + 1) 0
    (Vector.replicate inst.n none)


private theorem exec_posetCoreCode {w : ℕ} (inst : PosetInstance) (hw : Fits w inst.wordBound) :
    ∃ y, ExecWithin w posetCoreCode (Data.init inst.encode) y
        ((2 * Nat.sqrt inst.n + 1) * (112 * inst.n * inst.n + 147 * inst.n + 48) +
          9 * inst.n * inst.n + 13 * inst.n + 39) ∧
      BaseRegs (posetSparse inst) (2 + inst.n * inst.n) y ∧
      (∀ v : Fin inst.n,
        y.mem ((2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges + v.val) =
          match vget (posetLoopRes inst).mate v with | some u => u.val | none => inst.n) ∧
      (∀ u : Fin inst.n,
        y.mem ((2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges +
            inst.n + inst.n + u.val) =
          match vget (posetLoopRes inst).dist u with | none => 0 | some j => j + 1) := by
  have hfit_all : Fits w ((2 + inst.n * inst.n) + 7 * inst.n + 6 * inst.n +
      inst.n * inst.n + 8) := hw.of_le (by unfold PosetInstance.wordBound; nlinarith)
  obtain ⟨y₁, he_setup, hb₁, hcsr₁⟩ :=
    exec_matrixSetupCode (m := inst.n) (r := inst.n) true (fun _ => rfl) inst.lt inst.encode
      inst.init_mem_n (fun h => by cases h)
      (fun u v => inst.init_mem_entry u v) (hfit_all.of_le (by simp; omega))
  have hE_le : (posetSparse inst).numEdges ≤ inst.n * inst.n := inst.toDense.numEdges_toSparse_le
  have hnu_le : (posetSparse inst).maxMatchingCard ≤ inst.n := by
    have := (posetSparse inst).maxMatchingCard_le_min
    change (posetSparse inst).maxMatchingCard ≤ min inst.n inst.n at this
    simpa using this
  have hsqrt_le : Nat.sqrt (posetSparse inst).maxMatchingCard ≤ Nat.sqrt inst.n :=
    Nat.sqrt_le_sqrt hnu_le
  have hfit_core : Fits w ((2 + inst.n * inst.n) + 7 * (posetSparse inst).m +
      5 * (posetSparse inst).r + (posetSparse inst).numEdges + 8) := by
    change Fits w ((2 + inst.n * inst.n) + 7 * inst.n + 5 * inst.n +
      (posetSparse inst).numEdges + 8)
    exact hfit_all.of_le (by omega)
  obtain ⟨y, he_core, hby, _, hmate_y, hdist_y, _⟩ :=
    core_exec (posetSparse inst) y₁ hb₁ hcsr₁ hfit_core
  have hcore_le : coreTime inst.n inst.n (posetSparse inst).numEdges
      (posetSparse inst).maxMatchingCard ≤
      (2 * Nat.sqrt inst.n + 1) *
        (112 * inst.n * inst.n + 147 * inst.n + 48) + 5 * inst.n + 6 := by
    unfold coreTime
    refine Nat.add_le_add_right (Nat.add_le_add_right ?_ _) _
    calc (2 * Nat.sqrt (posetSparse inst).maxMatchingCard + 1) *
          (100 * inst.n + 47 * inst.n + 112 * (posetSparse inst).numEdges + 48)
        ≤ (2 * Nat.sqrt inst.n + 1) *
            (100 * inst.n + 47 * inst.n + 112 * (posetSparse inst).numEdges + 48) :=
          Nat.mul_le_mul_right _ (by omega)
      _ ≤ (2 * Nat.sqrt inst.n + 1) *
            (112 * inst.n * inst.n + 147 * inst.n + 48) :=
          Nat.mul_le_mul_left _ (by nlinarith)
  refine ⟨y, (he_setup.seq he_core).mono ?_, hby,
    fun v => by
      have hv := hmate_y v
      cases h : vget (posetLoopRes inst).mate v <;> simpa [h] using hv,
    fun u => by
      have hu := hdist_y u
      cases h : vget (posetLoopRes inst).dist u <;> simpa [h] using hu⟩
  change 9 * inst.n * inst.n + 8 * inst.n + 33 +
      coreTime inst.n inst.n (posetSparse inst).numEdges
        (posetSparse inst).maxMatchingCard ≤ _
  omega

private theorem exec_scatterRowMateCode {w bOff : ℕ} (inst : PosetInstance)
    (mate : Vector (Option (Fin inst.n)) inst.n)
    (hM : IsMatching (posetSparse inst).graph (mateMatching mate))
    (x : Data 34) (hb : BaseRegs (posetSparse inst) bOff x)
    (hmate : ∀ v : Fin inst.n,
      x.mem (bOff + inst.n + 1 + (posetSparse inst).numEdges + v.val) =
        encodeOptFin (vget mate v))
    (hfit : Fits w (bOff + 7 * inst.n + 6 * inst.n + (posetSparse inst).numEdges + 8)) :
    ∃ y, ExecWithin w scatterRowMateCode x y (13 * inst.n + 9) ∧
      BaseRegs (posetSparse inst) bOff y ∧
      (∀ i : Fin inst.n,
        y.mem (bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n + i.val) =
          encodeOptFin (rowMateOf mate i)) ∧
      (∀ a, ¬(bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n ≤ a ∧
          a < bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n + inst.n) →
        y.mem a = x.mem a) := by
  have hrm_eq : x.regs rm = inst.n := hb.hrm
  have hbML_eq : x.regs bMLReg = bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n :=
    hb.hbML
  obtain ⟨y₁, he₁_raw, hr₁_raw, _, hmem₁⟩ := Cslib.WordRAM.fillConst_exec (w := w)
    (base := bMLReg) (len := rm) (val := rm) (one := one) (idx := idx) (addr := addr)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) hb.hone
    (by rw [hbML_eq, hrm_eq]; exact hfit.of_le (by omega))
    (by rw [hrm_eq]; exact hfit.of_le (by omega))
  have he₁ : ExecWithin w (Cslib.WordRAM.fillConst bMLReg rm rm one idx addr) x y₁
      (5 * inst.n + 3) := by rw [hrm_eq] at he₁_raw; exact he₁_raw.within
  have hr₁ : ∀ i : Fin 34, i.val < 28 → y₁.regs i = x.regs i := fun i hi =>
    hr₁_raw i (fun h => by subst h; simp at hi) (fun h => by subst h; simp at hi)
  have hfill₁ : ∀ k < inst.n,
      y₁.mem (bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n + k) = inst.n := by
    intro k hk
    rw [hmem₁, hbML_eq, hrm_eq]
    exact fill_of_owns ⟨Nat.le_add_right _ _, Nat.add_lt_add_left hk _⟩
  have hf₁ : ∀ a, ¬(bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n ≤ a ∧
      a < bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n + inst.n) →
      y₁.mem a = x.mem a := by
    intro a ha
    rw [hmem₁, hbML_eq, hrm_eq]
    exact fill_of_not_owns ha
  have hb₁ : BaseRegs (posetSparse inst) bOff y₁ := hb.of_eq fun i hi => hr₁ i (by omega)
  have hs₀ : ∃ s₀, ExecWithin w (ram[ idx ← #0 ] : Code .standard 34) y₁ s₀ 1 ∧
      s₀ = y₁.set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let P (t : ℕ) (y : Data 34) : Prop :=
    t ≤ inst.n ∧
      (∀ i : Fin 34, i.val < 19 → y.regs i = x.regs i) ∧
      (∀ (j i : Fin inst.n), j.val < t → vget mate j = some i →
        y.mem (bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n + i.val) = j.val) ∧
      (∀ i : Fin inst.n, (∀ j : Fin inst.n, j.val < t → vget mate j ≠ some i) →
        y.mem (bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n + i.val) = inst.n) ∧
      (∀ a, ¬(bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n ≤ a ∧
          a < bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n + inst.n) →
        y.mem a = x.mem a)
  have hP₀ : P 0 (y₁.set idx 0) :=
    ⟨Nat.zero_le _, fun i hi => by wram_simp [hr₁ i (by omega)],
      fun _ _ hj => absurd hj (Nat.not_lt_zero _),
      fun i _ => hfill₁ i.val i.isLt,
      fun a ha => hf₁ a ha⟩
  have hbody (y : Data 34) (hy : P (y.regs idx) y) (hlt : y.regs idx < inst.n) :
      ∃ z, ExecWithin w scatterRowMateBody y z 6 ∧ P (y.regs idx + 1) z ∧
        z.regs idx = y.regs idx + 1 := by
    obtain ⟨_, hr, hsome, hnone, hf⟩ := hy
    have hby : BaseRegs (posetSparse inst) bOff y := hb.of_eq hr
    let j₀ : Fin inst.n := ⟨y.regs idx, hlt⟩
    have hj₀_lt := j₀.isLt
    have hcm_j : y.mem (bOff + inst.n + 1 + (posetSparse inst).numEdges + y.regs idx) =
        encodeOptFin (vget mate j₀) := by
      rw [hf _ (by omega)]
      exact hmate j₀
    have hf_cm : Fits w (bOff + inst.n + 1 + (posetSparse inst).numEdges + y.regs idx) :=
      hfit.of_le (by omega)
    have hf_idx1 : Fits w (y.regs idx + 1) := hfit.of_le (by omega)
    have hby_cm : y.regs bColMateReg = bOff + inst.n + 1 + (posetSparse inst).numEdges :=
      hby.hbColMate
    have hby_rm : y.regs rm = inst.n := hby.hrm
    have hby_ml : y.regs bMLReg =
        bOff + inst.n + 1 + (posetSparse inst).numEdges + inst.n := hby.hbML
    refine WP.exists_execWithin ?_
    unfold scatterRowMateBody
    cases hmj : vget mate j₀ with
    | none =>
      have henc : encodeOptFin (vget mate j₀) = inst.n := by simp [hmj, encodeOptFin]
      wram_exec [hby_cm, hby_rm, hby.hzero, hby.hone, hcm_j, henc, hf_cm, hf_idx1]
      refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], fun j i hj hm => ?_,
        fun i hall => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · by_cases hjj : j = j₀
        · subst j; rw [hmj] at hm; cases hm
        · have : j.val ≠ y.regs idx := fun h => hjj (Fin.ext h)
          wram_simp
          exact hsome j i (by omega) hm
      · wram_simp
        exact hnone i fun j hj => hall j (by omega)
      · wram_simp; exact hf a ha
    | some i₀ =>
      have hi₀_lt := i₀.isLt
      have henc : encodeOptFin (vget mate j₀) = i₀.val := by simp [hmj, encodeOptFin]
      have hf_ml : Fits w (bOff + inst.n + 1 + (posetSparse inst).numEdges +
          inst.n + i₀.val) := hfit.of_le (by omega)
      wram_exec [hby_cm, hby_rm, hby_ml, hby.hone, hcm_j, henc, hi₀_lt,
        hf_cm, hf_ml, hf_idx1]
      refine ⟨⟨by omega, fun i hi => by wram_simp [hr i hi], fun j i hj hm => ?_,
        fun i hall => ?_, fun a ha => ?_⟩, by wram_simp⟩
      · by_cases hjj : j = j₀
        · subst j
          rw [hmj] at hm
          obtain ⟨rfl⟩ := hm
          dsimp only [j₀]
          wram_simp
        · have hj_lt : j.val < y.regs idx := by
            have : j.val ≠ y.regs idx := fun h => hjj (Fin.ext h)
            omega
          have hii : i ≠ i₀ := fun h => by
            subst i
            exact hjj (hM.2.1 i₀ j j₀ (mem_mateMatching.mpr hm) (mem_mateMatching.mpr hmj))
          have hne_val : i.val ≠ i₀.val := fun h => hii (Fin.ext h)
          wram_simp
          exact hsome j i hj_lt hm
      · have hii : i ≠ i₀ := fun h => by subst i; exact hall j₀ (Nat.lt_succ_self _) hmj
        have hne_val : i.val ≠ i₀.val := fun h => hii (Fin.ext h)
        wram_simp
        exact hnone i fun j hj => hall j (by omega)
      · wram_simp
        exact hf a ha
  obtain ⟨y, hl, hPn, _⟩ := ExecWithin.loop_count P
    (fun y hy => (hy.2.1 rm (by decide)).trans hrm_eq) hbody
    (x := y₁.set idx 0) (by simp) (by simpa using hP₀)
  obtain ⟨_, hr, hsome, hnone, hf⟩ := hPn
  refine ⟨y, (he₁.seq (he₀.seq hl)).mono (by simp; omega), hb.of_eq hr, fun i => ?_, hf⟩
  cases hrm_i : rowMateOf mate i with
  | some j =>
    have hm : vget mate j = some i :=
      mem_mateMatching.mp ((rowMateOf_eq_some_iff hM i j).mp hrm_i)
    simpa [encodeOptFin] using hsome j i j.isLt hm
  | none =>
    have hall : ∀ j : Fin inst.n, j.val < inst.n → vget mate j ≠ some i := fun j _ hm => by
      have := (rowMateOf_eq_some_iff hM i j).mpr (mem_mateMatching.mpr hm)
      rw [hrm_i] at this
      cases this
    simpa [encodeOptFin] using hnone i hall

private theorem exec_chainLabelsTail {w : ℕ} (inst : PosetInstance)
    (hw : Fits w inst.wordBound) (y : Data 34)
    (hby : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) y)
    (hmate_y : ∀ v : Fin inst.n,
      y.mem ((2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges + v.val) =
        match vget (posetLoopRes inst).mate v with
        | some u => u.val
        | none => inst.n) :
    ∃ z, ExecWithin w chainLabelsTail y z (9 * inst.n * inst.n + 35 * inst.n + 17) ∧
      outputList z.mem (z.regs outBase) = inst.chainLabelsList ∧
      Fits w (z.regs outBase + inst.chainLabelsList.length) := by
  have hE_le : (posetSparse inst).numEdges ≤ inst.n * inst.n := inst.toDense.numEdges_toSparse_le
  have hfit_all : Fits w ((2 + inst.n * inst.n) + 7 * inst.n + 6 * inst.n +
      (posetSparse inst).numEdges + 8) :=
    hw.of_le (by unfold PosetInstance.wordBound; nlinarith)
  have hM : IsMatching (posetSparse inst).graph (mateMatching (posetLoopRes inst).mate) := by
    have hc := (hopcroftKarp_correct (posetSparse inst).bipAdjValid_graph).1.1
    rwa [hopcroftKarp_matching_eq_mateMatching] at hc
  have hmate_enc : ∀ v : Fin inst.n,
      y.mem ((2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges + v.val) =
        encodeOptFin (vget (posetLoopRes inst).mate v) := fun v => by
    have hv := hmate_y v
    cases h : vget (posetLoopRes inst).mate v <;> simpa [encodeOptFin, h] using hv
  obtain ⟨y₁, he_scat, hb₁, hrm_mem, _⟩ :=
    exec_scatterRowMateCode inst (posetLoopRes inst).mate hM y hby hmate_enc hfit_all
  -- Step B: initLabelsCode
  let bOut := (2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges +
    4 * inst.n + 6 * inst.n + 6
  let bML := (2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges + inst.n
  have hml_lt_out : bML + inst.n ≤ bOut := by dsimp only [bML, bOut]; omega
  have hf_ob : Fits w bOut := hfit_all.of_le (by dsimp only [bOut]; omega)
  have hb₁_ob : y₁.regs outBase = bOut := hb₁.houtBase
  have hb₁_rm : y₁.regs rm = inst.n := hb₁.hrm
  have hs_il₀ : ∃ s_il, ExecWithin w
      (ram[ addr ← outBase; *addr ← rm; idx ← #0 ] : Code .standard 34) y₁ s_il 3 ∧
      s_il = ((y₁.set addr bOut).write bOut inst.n).set idx 0 := by
    refine WP.exists_execWithin ?_
    wram_exec [hb₁_ob, hb₁_rm, hf_ob]
    rfl
  obtain ⟨s_il, he_il₀, rfl⟩ := hs_il₀
  let s_il := ((y₁.set addr bOut).write bOut inst.n).set idx 0
  let PI (t : ℕ) (w_st : Data 34) : Prop :=
    t ≤ inst.n ∧
      (∀ i : Fin 34, i.val < 19 → w_st.regs i = y₁.regs i) ∧
      w_st.mem bOut = inst.n ∧
      (∀ k : ℕ, k < t → w_st.mem (bOut + 1 + k) = k) ∧
      (∀ a, ¬(bOut ≤ a ∧ a < bOut + 1 + t) → w_st.mem a = y₁.mem a)
  have hPI₀ : PI 0 s_il :=
    ⟨Nat.zero_le _, fun i hi => by dsimp only [s_il]; wram_simp,
      by dsimp only [s_il]; wram_simp,
      fun _ hk => absurd hk (Nat.not_lt_zero _),
      fun a ha => by dsimp only [s_il]; wram_simp⟩
  have hilBody (w_st : Data 34) (hw_st : PI (w_st.regs idx) w_st)
      (hlt : w_st.regs idx < inst.n) :
      ∃ w', ExecWithin w initLabelsBody w_st w' 4 ∧ PI (w_st.regs idx + 1) w' ∧
        w'.regs idx = w_st.regs idx + 1 := by
    obtain ⟨_, hr_i, hob_i, hlab_i, hf_i⟩ := hw_st
    have hbw : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) w_st := hb₁.of_eq hr_i
    have hbw_ob : w_st.regs outBase = bOut := hbw.houtBase
    have hf_o1 : Fits w (bOut + 1) := hfit_all.of_le (by dsimp only [bOut]; omega)
    have hf_ok : Fits w ((bOut + 1) + w_st.regs idx) :=
      hfit_all.of_le (by dsimp only [bOut]; omega)
    have hf_idx1 : Fits w (w_st.regs idx + 1) := hfit_all.of_le (by omega)
    refine WP.exists_execWithin ?_
    unfold initLabelsBody
    wram_exec [hbw_ob, hbw.hone, hf_o1, hf_ok, hf_idx1]
    refine ⟨⟨by omega, fun i hi => by wram_simp [hr_i i hi],
      by wram_simp [hob_i],
      fun k hk => ?_, fun a ha => ?_⟩, by wram_simp⟩
    · by_cases heq : k = w_st.regs idx
      · subst heq; wram_simp
      · wram_simp; exact hlab_i k (by omega)
    · wram_simp; exact hf_i a (by omega)
  have hsil_idx : s_il.regs idx = 0 := by dsimp only [s_il]; wram_simp
  obtain ⟨y₂, hl_il, hPIn, _⟩ := ExecWithin.loop_count PI
    (fun w_st hw_st => (hw_st.2.1 rm (by decide)).trans hb₁_rm) hilBody
    (x := s_il) (by rw [hsil_idx]; exact Nat.zero_le _) (by rw [hsil_idx]; exact hPI₀)
  rw [hsil_idx, Nat.sub_zero] at hl_il
  obtain ⟨_, hr₂, hob₂, hlab₂, hf₂⟩ := hPIn
  have hb₂ : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) y₂ := hb₁.of_eq hr₂
  have hb₂_rm : y₂.regs rm = inst.n := hb₂.hrm
  -- Step C: mergeLabelsCode
  let stepFn (lab : Vector (Fin inst.n) inst.n) (i : Fin inst.n) : Vector (Fin inst.n) inst.n :=
    match rowMateOf (posetLoopRes inst).mate i with
    | some j => mergeChains lab (i, j)
    | none => lab
  let labAt (k : ℕ) : Vector (Fin inst.n) inst.n :=
    ((List.finRange inst.n).take k).foldl stepFn (Vector.ofFn id)
  have hs_mg₀ : ∃ s_mg, ExecWithin w (ram[ qHead ← #0 ] : Code .standard 34) y₂ s_mg 1 ∧
      s_mg = y₂.set qHead 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨s_mg, he_mg₀, rfl⟩ := hs_mg₀
  let PM (k : ℕ) (w_st : Data 34) : Prop :=
    k ≤ inst.n ∧
      (∀ i : Fin 34, i.val < 19 → w_st.regs i = y₂.regs i) ∧
      w_st.mem bOut = inst.n ∧
      (∀ t : Fin inst.n, w_st.mem (bOut + 1 + t.val) = (vget (labAt k) t).val) ∧
      (∀ a, ¬(bOut + 1 ≤ a ∧ a < bOut + 1 + inst.n) → w_st.mem a = y₂.mem a)
  have hPM₀ : PM 0 (y₂.set qHead 0) :=
    ⟨Nat.zero_le _, fun i hi => by wram_simp, hob₂,
      fun t => by
        simp only [Data.set, labAt, List.take_zero, List.foldl_nil, vget, Vector.getElem_ofFn, id]
        exact hlab₂ t.val t.isLt,
      fun _ _ => rfl⟩
  have hmgOuter (w_st : Data 34) (hw_st : PM (w_st.regs qHead) w_st)
      (hk_lt : w_st.regs qHead < inst.n) :
      ∃ z_st, ExecWithin w mergeOuterBody w_st z_st (9 * inst.n + 14) ∧
        PM (w_st.regs qHead + 1) z_st ∧ z_st.regs qHead = w_st.regs qHead + 1 := by
    obtain ⟨_, hr_m, hob_m, hlab_m, hf_m⟩ := hw_st
    have hbw : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) w_st := hb₂.of_eq hr_m
    have hbw_ml : w_st.regs bMLReg = bML := hbw.hbML
    have hbw_rm : w_st.regs rm = inst.n := hbw.hrm
    have hbw_ob : w_st.regs outBase = bOut := hbw.houtBase
    let i₀ : Fin inst.n := ⟨w_st.regs qHead, hk_lt⟩
    have hrm_i₀ : w_st.mem (bML + w_st.regs qHead) =
        encodeOptFin (rowMateOf (posetLoopRes inst).mate i₀) := by
      rw [hf_m _ (by omega), hf₂ _ (by omega)]
      exact hrm_mem i₀
    have hf_ml_i : Fits w (bML + w_st.regs qHead) :=
      hfit_all.of_le (by dsimp only [bML]; omega)
    have hf_qh1 : Fits w (w_st.regs qHead + 1) := hfit_all.of_le (by omega)
    have hchk : ∃ w_chk, ExecWithin w
        (ram[ addr ← bMLReg + qHead; qTail ← *addr ] : Code .standard 34) w_st w_chk 2 ∧
        w_chk = (w_st.set addr (bML + w_st.regs qHead)).set qTail
          (encodeOptFin (rowMateOf (posetLoopRes inst).mate i₀)) := by
      refine WP.exists_execWithin ?_
      wram_exec [hbw_ml, hrm_i₀, hf_ml_i]
      rfl
    obtain ⟨w_chk, he_chk, rfl⟩ := hchk
    let w_chk := (w_st.set addr (bML + w_st.regs qHead)).set qTail
      (encodeOptFin (rowMateOf (posetLoopRes inst).mate i₀))
    have hlab_succ : labAt (w_st.regs qHead + 1) = stepFn (labAt (w_st.regs qHead)) i₀ := by
      dsimp only [labAt]
      rw [List.take_succ_finRange hk_lt, List.foldl_append, List.foldl_cons, List.foldl_nil]
    cases hrmi : rowMateOf (posetLoopRes inst).mate i₀ with
    | none =>
      have hc_neg : ¬(Cond.lt qTail rm).Holds w_chk := by
        simp [Cond.holds_lt, w_chk, hrmi, encodeOptFin, hbw_rm]
      have hnop : ExecWithin w (ram[ tmp ← zero ] : Code .standard 34)
          w_chk (w_chk.set tmp 0) 1 := by
        refine WP.execWithin ?_
        have hz_chk : w_chk.regs zero = 0 := by dsimp only [w_chk]; wram_simp [hbw.hzero]
        wram_exec [hz_chk]; rfl
      have hinc : ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34)
          (w_chk.set tmp 0) ((w_chk.set tmp 0).set qHead (w_st.regs qHead + 1)) 1 := by
        refine WP.execWithin ?_
        have hqh_chk : w_chk.regs qHead = w_st.regs qHead := by dsimp only [w_chk]; wram_simp
        have hone_chk : w_chk.regs one = 1 := by dsimp only [w_chk]; wram_simp [hbw.hone]
        wram_exec [hqh_chk, hone_chk, hf_qh1]; rfl
      have he_br := hnop.branch_neg (pos := mergeBranchTrue) hc_neg
      refine ⟨(w_chk.set tmp 0).set qHead (w_st.regs qHead + 1),
        (he_chk.seq (he_br.seq hinc)).mono (by omega),
        ⟨by omega, fun i hi => by dsimp only [w_chk]; wram_simp [hr_m i hi],
          hob_m, fun t => by rw [hlab_succ]; dsimp only [stepFn]; rw [hrmi]; exact hlab_m t,
          fun a ha => hf_m a ha⟩, by wram_simp⟩
    | some j₀ =>
      have hj₀_lt : j₀.val < inst.n := j₀.isLt
      have hc_pos : (Cond.lt qTail rm).Holds w_chk := by
        simp [Cond.holds_lt, w_chk, hrmi, encodeOptFin, hbw_rm]
      let newV := (vget (labAt (w_st.regs qHead)) i₀).val
      let oldV := (vget (labAt (w_st.regs qHead)) j₀).val
      have hf_o1 : Fits w (bOut + 1) := hfit_all.of_le (by dsimp only [bOut]; omega)
      have hf_oi : Fits w ((bOut + 1) + w_st.regs qHead) :=
        hfit_all.of_le (by dsimp only [bOut]; omega)
      have hf_oj : Fits w ((bOut + 1) + j₀.val) :=
        hfit_all.of_le (by dsimp only [bOut]; omega)
      have hmem_i : w_chk.mem ((bOut + 1) + w_st.regs qHead) = newV := by
        simpa [w_chk, Nat.add_assoc] using hlab_m i₀
      have hmem_j : w_chk.mem ((bOut + 1) + j₀.val) = oldV := by
        simpa [w_chk, Nat.add_assoc] using hlab_m j₀
      have hpre_br : ∃ w_in, ExecWithin w
          (ram[ addr ← outBase + one; addr ← addr + qHead; val ← *addr;
                addr ← outBase + one; addr ← addr + qTail; val2 ← *addr;
                idx ← #0 ] : Code .standard 34) w_chk w_in 7 ∧
          (∀ i : Fin 34, i.val < 23 → w_in.regs i = w_st.regs i) ∧
          w_in.regs idx = 0 ∧ w_in.regs val = newV ∧ w_in.regs val2 = oldV ∧
          w_in.mem = w_st.mem := by
        refine WP.exists_execWithin ?_
        have hob_chk : w_chk.regs outBase = bOut := by
          dsimp only [w_chk]; wram_simp [hbw_ob]
        have hone_chk : w_chk.regs one = 1 := by dsimp only [w_chk]; wram_simp [hbw.hone]
        have hqh_chk : w_chk.regs qHead = w_st.regs qHead := by dsimp only [w_chk]; wram_simp
        have hqt_chk : w_chk.regs qTail = j₀.val := by
          dsimp only [w_chk]; wram_simp [hrmi, encodeOptFin]
        wram_exec [hob_chk, hone_chk, hqh_chk, hqt_chk, hmem_i, hmem_j, hf_o1, hf_oi, hf_oj]
        exact ⟨fun i hi => by dsimp only [w_chk]; wram_simp, by wram_simp,
          by wram_simp, by wram_simp, rfl⟩
      obtain ⟨w_in, he_pre_br, hr_in, hidx_in, hval_in, hval2_in, hmem_in⟩ := hpre_br
      let PN (s : ℕ) (u_st : Data 34) : Prop :=
        s ≤ inst.n ∧
          (∀ i : Fin 34, i.val < 23 → u_st.regs i = w_st.regs i) ∧
          u_st.regs val = newV ∧ u_st.regs val2 = oldV ∧
          (∀ t : Fin inst.n, t.val < s →
            u_st.mem (bOut + 1 + t.val) =
              (vget (mergeChains (labAt (w_st.regs qHead)) (i₀, j₀)) t).val) ∧
          (∀ t : Fin inst.n, s ≤ t.val →
            u_st.mem (bOut + 1 + t.val) = (vget (labAt (w_st.regs qHead)) t).val) ∧
          (∀ a, ¬(bOut + 1 ≤ a ∧ a < bOut + 1 + inst.n) → u_st.mem a = w_st.mem a)
      have hPN₀ : PN 0 w_in :=
        ⟨Nat.zero_le _, hr_in, hval_in, hval2_in,
          fun _ ht => absurd ht (Nat.not_lt_zero _),
          fun t _ => by rw [hmem_in]; exact hlab_m t,
          fun _ _ => by rw [hmem_in]⟩
      have hinnerBody (u_st : Data 34) (hu_st : PN (u_st.regs idx) u_st)
          (hs_lt : u_st.regs idx < inst.n) :
          ∃ u', ExecWithin w mergeInnerBody u_st u' 7 ∧ PN (u_st.regs idx + 1) u' ∧
            u'.regs idx = u_st.regs idx + 1 := by
        obtain ⟨_, hr_u, hv_u, hv2_u, hpre_u, hsuf_u, hf_u⟩ := hu_st
        have hbu : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) u_st :=
          hb₂.of_eq fun i hi => (hr_u i (by omega)).trans (hr_m i hi)
        have hbu_ob : u_st.regs outBase = bOut := hbu.houtBase
        let t₀ : Fin inst.n := ⟨u_st.regs idx, hs_lt⟩
        have ht₀_lt := t₀.isLt
        have hmem_t₀ : u_st.mem ((bOut + 1) + u_st.regs idx) =
            (vget (labAt (w_st.regs qHead)) t₀).val := by
          simpa [Nat.add_assoc] using hsuf_u t₀ (le_refl _)
        have hf_ot : Fits w ((bOut + 1) + u_st.regs idx) :=
          hfit_all.of_le (by dsimp only [bOut]; omega)
        have hf_s1 : Fits w (u_st.regs idx + 1) := hfit_all.of_le (by omega)
        refine WP.exists_execWithin ?_
        unfold mergeInnerBody
        by_cases heq_v : (vget (labAt (w_st.regs qHead)) t₀).val = oldV
        · have heq_fin : vget (labAt (w_st.regs qHead)) t₀ =
              vget (labAt (w_st.regs qHead)) j₀ := Fin.ext heq_v
          have hm_eq : vget (mergeChains (labAt (w_st.regs qHead)) (i₀, j₀)) t₀ =
              vget (labAt (w_st.regs qHead)) i₀ :=
            (Vector.getElem_ofFn t₀.isLt).trans (ite_eq_left heq_fin)
          wram_exec [hbu_ob, hbu.hone, hv_u, hv2_u, hmem_t₀, heq_v, hf_o1, hf_ot, hf_s1]
          refine ⟨⟨by omega, fun i hi => by wram_simp [hr_u i hi],
            by wram_simp [hv_u], by wram_simp [hv2_u], fun t ht => ?_, fun t ht => ?_,
            fun a ha => ?_⟩, by wram_simp⟩
          · by_cases htt : t = t₀
            · subst t
              wram_simp
              exact (congrArg Fin.val hm_eq).symm
            · have : t.val ≠ u_st.regs idx := fun h => htt (Fin.ext h)
              wram_simp
              exact hpre_u t (by omega)
          · wram_simp
            exact hsuf_u t (by omega)
          · wram_simp; exact hf_u a ha
        · have hne_fin : vget (labAt (w_st.regs qHead)) t₀ ≠
              vget (labAt (w_st.regs qHead)) j₀ := fun h => heq_v (congrArg Fin.val h)
          have hm_eq : vget (mergeChains (labAt (w_st.regs qHead)) (i₀, j₀)) t₀ =
              vget (labAt (w_st.regs qHead)) t₀ :=
            (Vector.getElem_ofFn t₀.isLt).trans (ite_eq_right hne_fin)
          wram_exec [hbu_ob, hbu.hone, hbu.hzero, hv2_u, hmem_t₀, heq_v,
            hf_o1, hf_ot, hf_s1]
          refine ⟨⟨by omega, fun i hi => by wram_simp [hr_u i hi],
            by wram_simp [hv_u], by wram_simp [hv2_u], fun t ht => ?_, fun t ht => ?_,
            fun a ha => ?_⟩, by wram_simp⟩
          · by_cases htt : t = t₀
            · subst t
              wram_simp
              rw [hsuf_u t₀ (le_refl _), hm_eq]
            · have : t.val ≠ u_st.regs idx := fun h => htt (Fin.ext h)
              wram_simp
              exact hpre_u t (by omega)
          · wram_simp; exact hsuf_u t (by omega)
          · wram_simp; exact hf_u a ha
      obtain ⟨w_out, hl_in, hPNn, _⟩ := ExecWithin.loop_count PN
        (fun u_st hu_st =>
          (hu_st.2.1 rm (by decide)).trans ((hr_m rm (by decide)).trans hb₂_rm))
        hinnerBody (x := w_in) (by rw [hidx_in]; exact Nat.zero_le _)
        (by rw [hidx_in]; exact hPN₀)
      rw [hidx_in, Nat.sub_zero] at hl_in
      obtain ⟨_, hr_out, _, _, hpre_out, _, hf_out⟩ := hPNn
      have he_br :=
        (he_pre_br.seq hl_in).branch_pos (neg := (ram[ tmp ← zero ] : Code .standard 34)) hc_pos
      have hqh_out : w_out.regs qHead = w_st.regs qHead := hr_out qHead (by decide)
      have hone_out : w_out.regs one = 1 :=
        (hr_out one (by decide)).trans ((hr_m one (by decide)).trans hb₂.hone)
      have hinc : ExecWithin w (ram[ qHead ← qHead + one ] : Code .standard 34)
          w_out (w_out.set qHead (w_st.regs qHead + 1)) 1 := by
        refine WP.execWithin ?_
        wram_exec [hqh_out, hone_out, hf_qh1]; rfl
      refine ⟨w_out.set qHead (w_st.regs qHead + 1),
        (he_chk.seq (he_br.seq hinc)).mono (by omega),
        ⟨by omega, fun i hi => by wram_simp [(hr_out i (by omega)).trans (hr_m i hi)],
          by dsimp only [Data.set]; rw [hf_out _ (by omega)]; exact hob_m,
          fun t => by
            dsimp only [Data.set]
            rw [hlab_succ]
            dsimp only [stepFn]
            rw [hrmi]
            exact hpre_out t t.isLt,
          fun a ha => (hf_out a ha).trans (hf_m a ha)⟩, by wram_simp⟩
  obtain ⟨z, hl_mg, hPMn, _⟩ := ExecWithin.loop_count PM
    (fun w_st hw_st => (hw_st.2.1 rm (by decide)).trans hb₂_rm) hmgOuter
    (x := y₂.set qHead 0) (by simp) (by simpa using hPM₀)
  obtain ⟨_, hrz, hobz, hlabz, _⟩ := hPMn
  have hbz : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) z := hb₂.of_eq hrz
  have hbz_ob : z.regs outBase = bOut := hbz.houtBase
  have hs_graph : (posetSparse inst).graph = inst.lt := inst.toDense.toSparse_graph
  have hmatch_eq : (hopcroftKarpDense inst.lt).matching =
      mateMatching (posetLoopRes inst).mate := by
    rw [← hopcroftKarp_exactBipAdj inst.lt]
    change (hopcroftKarp inst.lt (posetSparse inst).adj).matching = _
    rw [← hs_graph]
    exact hopcroftKarp_matching_eq_mateMatching
  have hlab_full : labAt inst.n =
      chainLabels (hopcroftKarpDense inst.lt).matching
        (List.finRange inst.n ×ˢ List.finRange inst.n) (Vector.ofFn id) := by
    dsimp only [labAt, stepFn]
    rw [List.take_of_length_le (by simp), hmatch_eq,
      chainLabels_eq_foldl_rowMate (rowMateOf (posetLoopRes inst).mate) (rowMateOf_eq_some_iff hM)]
    congr 1
    funext lab i
    cases rowMateOf (posetLoopRes inst).mate i <;> rfl
  have hcl_len : inst.chainLabelsList.length = inst.n := by
    simp [PosetInstance.chainLabelsList]
  have hout_z : outputList z.mem (z.regs outBase) = inst.chainLabelsList := by
    rw [hbz_ob, outputList_eq_iff, hcl_len]
    refine ⟨hobz, fun i => ?_⟩
    have hi_val : i.val < inst.chainLabelsList.length := i.isLt
    have hi_lt : i.val < inst.n := hi_val.trans_eq hcl_len
    change z.mem (bOut + 1 + i.val) = inst.chainLabelsList[i.val]'hi_val
    rw [hlabz ⟨i.val, hi_lt⟩, hlab_full]
    simp [PosetInstance.chainLabelsList]
  have hfit_out : Fits w (z.regs outBase + inst.chainLabelsList.length) := by
    rw [hbz_ob, hcl_len]
    exact hfit_all.of_le (by dsimp only [bOut]; omega)
  have hqh0 : (y₂.set qHead 0).regs qHead = 0 := by simp
  rw [hqh0, Nat.sub_zero] at hl_mg
  exact ⟨z, (he_scat.seq ((he_il₀.seq hl_il).seq (he_mg₀.seq hl_mg))).mono (by nlinarith),
    hout_z, hfit_out⟩

private theorem exec_maxAntichainTail {w : ℕ} (inst : PosetInstance)
    (hw : Fits w inst.wordBound) (y : Data 34)
    (hby : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) y)
    (hmate_y : ∀ v : Fin inst.n,
      y.mem ((2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges + v.val) =
        match vget (posetLoopRes inst).mate v with
        | some u => u.val
        | none => inst.n)
    (hdist_y : ∀ u : Fin inst.n,
      y.mem ((2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges +
          inst.n + inst.n + u.val) =
        match vget (posetLoopRes inst).dist u with
        | none => 0
        | some j => j + 1) :
    ∃ z, ExecWithin w maxAntichainTail y z (16 * inst.n + 6) ∧
      outputList z.mem (z.regs outBase) = inst.antichainList ∧
      Fits w (z.regs outBase + inst.antichainList.length) := by
  have hE_le : (posetSparse inst).numEdges ≤ inst.n * inst.n := inst.toDense.numEdges_toSparse_le
  have hfit_all : Fits w ((2 + inst.n * inst.n) + 7 * inst.n + 6 * inst.n +
      (posetSparse inst).numEdges + 8) :=
    hw.of_le (by unfold PosetInstance.wordBound; nlinarith)
  let hk := hopcroftKarpDense inst.lt
  have hs_graph : (posetSparse inst).graph = inst.lt := inst.toDense.toSparse_graph
  have hhk_eq : hk = hopcroftKarp (posetSparse inst).graph (posetSparse inst).adj := by
    change hopcroftKarpDense inst.lt = hopcroftKarp (posetSparse inst).graph (exactBipAdj inst.lt)
    rw [← hopcroftKarp_exactBipAdj inst.lt, hs_graph]
  have huncov_iff : ∀ i : Fin inst.n,
      i ∈ hk.cover.uncovered ↔
        vget (posetLoopRes inst).dist i ≠ none ∧
          ∀ w₀ : Fin inst.n, vget (posetLoopRes inst).mate i = some w₀ →
            vget (posetLoopRes inst).dist w₀ = none := by
    intro i
    rw [mem_uncovered, hhk_eq]
    unfold hopcroftKarp posetLoopRes
    simp only [mem_foldl_hkCoverLeftStep, mem_foldl_hkCoverRightStep, Finset.notMem_empty,
      List.mem_finRange, true_and, false_or, not_exists, not_and, Classical.not_not]
  let ac (t : ℕ) : List ℕ :=
    (((List.finRange inst.n).take t).filter fun i => decide (i ∈ hk.cover.uncovered)).map Fin.val
  have hac_len : ∀ t : ℕ, (ac t).length ≤ t := fun t => by
    calc (ac t).length
      _ = (((List.finRange inst.n).take t).filter _).length := List.length_map _
      _ ≤ ((List.finRange inst.n).take t).length := List.length_filter_le _ _
      _ ≤ t := List.length_take_le _ _
  let bCol := (2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges
  let bDist := (2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges + inst.n + inst.n
  let bOut := (2 + inst.n * inst.n) + inst.n + 1 + (posetSparse inst).numEdges +
    4 * inst.n + 6 * inst.n + 6
  have hcol_lt_out : bCol + inst.n ≤ bOut := by dsimp only [bCol, bOut]; omega
  have hdist_lt_out : bDist + inst.n ≤ bOut := by dsimp only [bDist, bOut]; omega
  have hby_rm : y.regs rm = inst.n := hby.hrm
  have hs₀ : ∃ s₀, ExecWithin w (ram[ acc ← #0; idx ← #0 ] : Code .standard 34) y s₀ 2 ∧
      s₀ = (y.set acc 0).set idx 0 := by
    refine WP.exists_execWithin ?_; wram_exec; rfl
  obtain ⟨s₀, he₀, rfl⟩ := hs₀
  let PA (t : ℕ) (w_st : Data 34) : Prop :=
    t ≤ inst.n ∧
      (∀ i : Fin 34, i.val < 19 → w_st.regs i = y.regs i) ∧
      w_st.regs acc = (ac t).length ∧
      (∀ k : ℕ, (hk_len : k < (ac t).length) → w_st.mem (bOut + 1 + k) = (ac t)[k]'hk_len) ∧
      (∀ a, ¬(bOut + 1 ≤ a ∧ a < bOut + 1 + t) → w_st.mem a = y.mem a)
  have hPA₀ : PA 0 ((y.set acc 0).set idx 0) :=
    ⟨Nat.zero_le _, fun i hi => by wram_simp, by wram_simp; simp [ac],
      fun _ hk_len => absurd hk_len (by simp [ac]), fun _ _ => rfl⟩
  have hacBody (w_st : Data 34) (hw_st : PA (w_st.regs idx) w_st)
      (hlt : w_st.regs idx < inst.n) :
      ∃ w', ExecWithin w maxAntichainBody w_st w' 14 ∧ PA (w_st.regs idx + 1) w' ∧
        w'.regs idx = w_st.regs idx + 1 := by
    obtain ⟨_, hr_a, hacc_a, hblk_a, hf_a⟩ := hw_st
    have hbw : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) w_st := hby.of_eq hr_a
    have hbw_dist : w_st.regs bDistReg = bDist := hbw.hbDist
    have hbw_col : w_st.regs bColMateReg = bCol := hbw.hbColMate
    have hbw_ob : w_st.regs outBase = bOut := hbw.houtBase
    have hbw_rm : w_st.regs rm = inst.n := hbw.hrm
    let i₀ : Fin inst.n := ⟨w_st.regs idx, hlt⟩
    have hac_le : (ac (w_st.regs idx)).length ≤ w_st.regs idx := hac_len (w_st.regs idx)
    have hdi₀ : w_st.mem (bDist + w_st.regs idx) =
        match vget (posetLoopRes inst).dist i₀ with | none => 0 | some j => j + 1 := by
      rw [hf_a _ (by omega)]
      exact hdist_y i₀
    have hmi₀ : w_st.mem (bCol + w_st.regs idx) =
        match vget (posetLoopRes inst).mate i₀ with | some u => u.val | none => inst.n := by
      rw [hf_a _ (by omega)]
      exact hmate_y i₀
    have hf_di : Fits w (bDist + w_st.regs idx) :=
      hfit_all.of_le (by dsimp only [bDist]; omega)
    have hf_mi : Fits w (bCol + w_st.regs idx) :=
      hfit_all.of_le (by dsimp only [bCol]; omega)
    have hf_o1 : Fits w (bOut + 1) := hfit_all.of_le (by dsimp only [bOut]; omega)
    have hf_oa : Fits w ((bOut + 1) + (ac (w_st.regs idx)).length) :=
      hfit_all.of_le (by dsimp only [bOut]; omega)
    have hf_a1 : Fits w ((ac (w_st.regs idx)).length + 1) := hfit_all.of_le (by omega)
    have hf_idx1 : Fits w (w_st.regs idx + 1) := hfit_all.of_le (by omega)
    have hac_succ : ac (w_st.regs idx + 1) =
        if i₀ ∈ hk.cover.uncovered then ac (w_st.regs idx) ++ [i₀.val]
        else ac (w_st.regs idx) := by
      dsimp only [ac]
      rw [List.take_succ_finRange hlt, List.filter_append, List.map_append]
      by_cases h : i₀ ∈ hk.cover.uncovered <;> simp [i₀, h]
    have emit_proof (hunc : i₀ ∈ hk.cover.uncovered) :
        ∀ (w' : Data 34),
          (∀ i : Fin 34, i.val < 19 → w'.regs i = w_st.regs i) →
          w'.regs acc = (ac (w_st.regs idx)).length + 1 →
          w'.regs idx = w_st.regs idx + 1 →
          w'.mem = Function.update w_st.mem
            ((bOut + 1) + (ac (w_st.regs idx)).length) (w_st.regs idx) →
          PA (w_st.regs idx + 1) w' ∧ w'.regs idx = w_st.regs idx + 1 := by
      intro w' hr' hacc' hidx' hmem'
      have hac_s : ac (w_st.regs idx + 1) = ac (w_st.regs idx) ++ [i₀.val] := by
        rw [hac_succ, ite_eq_left hunc]
      refine ⟨⟨by omega, fun i hi => (hr' i hi).trans (hr_a i hi),
        by rw [hacc', hac_s, List.length_append, List.length_singleton],
        fun k hk_len => ?_, fun a ha => ?_⟩, hidx'⟩
      · have hk_lt1 : k < (ac (w_st.regs idx)).length + 1 := by
          have hk' := hk_len
          rwa [hac_s, List.length_append, List.length_singleton] at hk'
        simp only [hac_s]
        by_cases hk_old : k < (ac (w_st.regs idx)).length
        · rw [List.getElem_append_left hk_old, hmem', Function.update_of_ne (by omega)]
          exact hblk_a k hk_old
        · have hk_eq : k = (ac (w_st.regs idx)).length := by omega
          subst hk_eq
          rw [List.getElem_append_right (le_refl _), hmem', Function.update_self]
          simp [i₀]
      · rw [hmem', Function.update_of_ne (by omega)]
        exact hf_a a (by omega)
    have skip_proof (hnunc : i₀ ∉ hk.cover.uncovered) :
        ∀ (w' : Data 34),
          (∀ i : Fin 34, i.val < 19 → w'.regs i = w_st.regs i) →
          w'.regs acc = (ac (w_st.regs idx)).length →
          w'.regs idx = w_st.regs idx + 1 →
          w'.mem = w_st.mem →
          PA (w_st.regs idx + 1) w' ∧ w'.regs idx = w_st.regs idx + 1 := by
      intro w' hr' hacc' hidx' hmem'
      have hac_s : ac (w_st.regs idx + 1) = ac (w_st.regs idx) := by
        rw [hac_succ, ite_eq_right hnunc]
      refine ⟨⟨by omega, fun i hi => (hr' i hi).trans (hr_a i hi),
        by rw [hacc', hac_s], fun k hk_len => ?_,
        fun a ha => by rw [hmem']; exact hf_a a (by omega)⟩, hidx'⟩
      have hk' : k < (ac (w_st.regs idx)).length := by rwa [← hac_s]
      rw [hmem']
      simpa [hac_s] using hblk_a k hk'
    refine WP.exists_execWithin ?_
    unfold maxAntichainBody
    cases hd_i : vget (posetLoopRes inst).dist i₀ with
    | none =>
      rw [hd_i] at hdi₀
      have hnunc : i₀ ∉ hk.cover.uncovered := fun h => ((huncov_iff i₀).mp h).1 hd_i
      wram_exec [hbw_dist, hbw.hzero, hbw.hone, hdi₀, hf_di, hf_idx1]
      exact skip_proof hnunc _ (fun _ _ => by wram_simp) (by wram_simp [hacc_a])
        (by wram_simp) rfl
    | some j =>
      rw [hd_i] at hdi₀
      have hpos : 0 < j + 1 := Nat.succ_pos j
      cases hm_i : vget (posetLoopRes inst).mate i₀ with
      | none =>
        rw [hm_i] at hmi₀
        have hnl : ¬inst.n < inst.n := Nat.lt_irrefl _
        have hunc : i₀ ∈ hk.cover.uncovered := (huncov_iff i₀).mpr ⟨by simp [hd_i],
          fun _ hw₀ => by rw [hm_i] at hw₀; cases hw₀⟩
        wram_exec [hbw_dist, hbw_col, hbw_ob, hbw_rm, hbw.hzero, hbw.hone,
          hacc_a, hdi₀, hpos, hmi₀, hnl, hf_di, hf_mi, hf_o1, hf_oa, hf_a1, hf_idx1]
        exact emit_proof hunc _ (fun _ _ => by wram_simp) (by wram_simp) (by wram_simp) rfl
      | some w₀ =>
        have hw₀_lt : w₀.val < inst.n := w₀.isLt
        rw [hm_i] at hmi₀
        have hdw₀ : w_st.mem (bDist + w₀.val) =
            match vget (posetLoopRes inst).dist w₀ with | none => 0 | some j' => j' + 1 := by
          rw [hf_a _ (by omega)]
          exact hdist_y w₀
        have hf_dw : Fits w (bDist + w₀.val) :=
          hfit_all.of_le (by dsimp only [bDist]; omega)
        cases hd_w : vget (posetLoopRes inst).dist w₀ with
        | none =>
          rw [hd_w] at hdw₀
          have hunc : i₀ ∈ hk.cover.uncovered := (huncov_iff i₀).mpr ⟨by simp [hd_i],
            fun w' hw' => by rw [hm_i] at hw'; obtain ⟨rfl⟩ := hw'; exact hd_w⟩
          wram_exec [hbw_dist, hbw_col, hbw_ob, hbw_rm, hbw.hzero, hbw.hone,
            hacc_a, hdi₀, hpos, hmi₀, hw₀_lt, hdw₀,
            hf_di, hf_mi, hf_dw, hf_o1, hf_oa, hf_a1, hf_idx1]
          exact emit_proof hunc _ (fun _ _ => by wram_simp) (by wram_simp) (by wram_simp) rfl
        | some j' =>
          rw [hd_w] at hdw₀
          have hne0 : j' + 1 ≠ 0 := Nat.succ_ne_zero j'
          have hnunc : i₀ ∉ hk.cover.uncovered := fun h => by
            have := ((huncov_iff i₀).mp h).2 w₀ hm_i
            rw [hd_w] at this
            cases this
          wram_exec [hbw_dist, hbw_col, hbw_rm, hbw.hzero, hbw.hone,
            hdi₀, hpos, hmi₀, hw₀_lt, hdw₀, hne0, hf_di, hf_mi, hf_dw, hf_idx1]
          exact skip_proof hnunc _ (fun _ _ => by wram_simp) (by wram_simp [hacc_a])
            (by wram_simp) rfl
  obtain ⟨y₁, hl_ac, hPAn, _⟩ := ExecWithin.loop_count PA
    (fun w_st hw_st => (hw_st.2.1 rm (by decide)).trans hby_rm) hacBody
    (x := (y.set acc 0).set idx 0) (by simp) (by simpa using hPA₀)
  obtain ⟨_, hr₁, hacc₁, hblk₁, _⟩ := hPAn
  have hb₁ : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) y₁ := hby.of_eq hr₁
  have hb₁_ob : y₁.regs outBase = bOut := hb₁.houtBase
  have hac_full : ac inst.n = inst.antichainList := by
    dsimp only [ac, PosetInstance.antichainList, hk]
    rw [List.take_of_length_le (by simp)]
  have hf_ob : Fits w bOut := hfit_all.of_le (by dsimp only [bOut]; omega)
  have htail : ∃ z, ExecWithin w
      (ram[ addr ← outBase; *addr ← acc ] : Code .standard 34) y₁ z 2 ∧
      z = (y₁.set addr bOut).write bOut inst.antichainList.length := by
    refine WP.exists_execWithin ?_
    rw [hac_full] at hacc₁
    wram_exec [hb₁_ob, hacc₁, hf_ob]
    rfl
  obtain ⟨z, he_tail, rfl⟩ := htail
  let z := (y₁.set addr bOut).write bOut inst.antichainList.length
  have hbz : BaseRegs (posetSparse inst) (2 + inst.n * inst.n) z :=
    hb₁.of_eq fun i hi => by dsimp only [z]; wram_simp
  have hbz_ob : z.regs outBase = bOut := hbz.houtBase
  have hout_z : outputList z.mem (z.regs outBase) = inst.antichainList := by
    rw [hbz_ob, outputList_eq_iff]
    refine ⟨by dsimp only [z]; wram_simp, fun i => ?_⟩
    have hi_val : i.val < inst.antichainList.length := i.isLt
    have hi_ac : i.val < (ac inst.n).length := by rwa [hac_full]
    change z.mem (bOut + 1 + i.val) = inst.antichainList[i.val]'hi_val
    have hmem_i : z.mem (bOut + 1 + i.val) = y₁.mem (bOut + 1 + i.val) := by
      dsimp only [z]; wram_simp
    rw [hmem_i]
    simpa [hac_full] using hblk₁ i.val hi_ac
  have hac_le_n : inst.antichainList.length ≤ inst.n := by
    rw [← hac_full]; exact hac_len inst.n
  have hfit_out : Fits w (z.regs outBase + inst.antichainList.length) := by
    rw [hbz_ob]
    exact hfit_all.of_le (by dsimp only [bOut]; omega)
  exact ⟨z, (he₀.seq (hl_ac.seq he_tail)).mono (by simp; omega), hout_z, hfit_out⟩

/-- **`O(n^{5/2})` Word-RAM minimum chain cover labels (`ExecutesList`).** -/
theorem executesList_chainLabels {w : ℕ} (inst : PosetInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w chainLabelsProgram (.init inst.encode) inst.chainLabelsList steps ∧
      steps ≤ chainCoverTime inst.n := by
  obtain ⟨y, he_core, hby, hmate_y, _⟩ := exec_posetCoreCode inst hw
  obtain ⟨z, he_tail, hout, hfit⟩ := exec_chainLabelsTail inst hw y hby hmate_y
  obtain ⟨t, ht, hex⟩ := he_core.seq he_tail
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]), ?_⟩
  unfold chainCoverTime at *
  nlinarith

/-- **`Program.ComputesListInTime` form of `executesList_chainLabels`.** -/
theorem computesListInTime_chainLabels :
    chainLabelsProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => chainCoverTime inst.n) (fun inst w => Fits w inst.wordBound)
      PosetInstance.chainLabelsList :=
  fun inst _ hw _ => executesList_chainLabels inst hw

/-- **`O(n^{5/2})` Word-RAM maximum antichain (`ExecutesList`).** -/
theorem executesList_maxAntichain {w : ℕ} (inst : PosetInstance) (hw : Fits w inst.wordBound) :
    ∃ steps, ExecutesList w maxAntichainProgram (.init inst.encode) inst.antichainList steps ∧
      steps ≤ chainCoverTime inst.n := by
  obtain ⟨y, he_core, hby, hmate_y, hdist_y⟩ := exec_posetCoreCode inst hw
  obtain ⟨z, he_tail, hout, hfit⟩ := exec_maxAntichainTail inst hw y hby hmate_y hdist_y
  obtain ⟨t, ht, hex⟩ := he_core.seq he_tail
  refine ⟨t + 1, hout ▸ hex.executesList outBase (by rwa [hout]), ?_⟩
  unfold chainCoverTime at *
  nlinarith

/-- **`Program.ComputesListInTime` form of `executesList_maxAntichain`.** -/
theorem computesListInTime_maxAntichain :
    maxAntichainProgram.ComputesListInTime (fun _ inst => inst.encode)
      (fun inst _ => chainCoverTime inst.n) (fun inst w => Fits w inst.wordBound)
      PosetInstance.antichainList :=
  fun inst _ hw _ => executesList_maxAntichain inst hw


end Cslib.Algorithms.WordRAM.ChainCover
