/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.Computability.WordRAM.RegisterFrame
import CslibFrontier.Foundations.Data.Nat.Div
public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Karger.Contraction
public import CslibFrontier.Computability.WordRAM.Heap
public import CslibFrontier.Computability.WordRAM.Notation
public import CslibFrontier.Computability.WordRAM.Randomized.Law
import CslibFrontier.Computability.WordRAM.SymbolicExec.Frame
import CslibFrontier.Computability.WordRAM.SymbolicExec.StructFrame

/-!
# Workspace-relocatable randomized contraction on the word RAM

Implements Karger's edge-weight-proportional contraction loop (`contractDownTo`) and its companion
row-degree initializer (`computeDegreesAndTotal`) as structured `Cslib.WordRAM` programs over
`Basis.standard` with `16` registers.

All memory accesses are parameterized dynamically by register-held workspace pointers
(`wBase`, `dBase`, `stride`, `activeK`, `targetT`, `totS`), with zero hardcoded memory addresses and
a `Modifies` frame confined to
`Finset.Ico wBase (wBase + stride * k) ∪ Finset.Ico dBase (dBase + k)`.
This allows both repeated-trial amplification (`KargerMinCut`) and recursive stack-allocated calls
in Karger–Stein (`FastCut`) to invoke `contractDownTo` directly at arbitrary memory offsets.

Each contraction from `m + 1` down to `m` active supervertices runs in `O(m)` worst-case
instructions and issues at most `1` `rand` call (`0` calls when total active weight `totS = 0`),
yielding `36 * (k ^ 2 - t ^ 2) + 4` worst-case instructions and at most `k - t` `rand` calls from
`k` down to `t`, with survival probability at least `(t * (t - 1)) / (k * (k - 1))` for any fixed
minimum cut of a connected multigraph.

The probability is not proved on machine states. `contractDownTo` simulates Karger's algorithm as
a client of the contraction structure `Cslib.Algorithms.Lean.Karger.spec`: the graph the machine
holds (`heldGraph`) has the law of `Cslib.Algorithms.Lean.Karger.contractTimes`
(`contractDownTo_law`). Each step's `rand` call draws the offset uniformly below the total weight,
as the client's coin does, and `postRandStep_exec` contracts the pair sampled there. The survival
bound and the contraction invariant are the specification's
(`Cslib.Algorithms.Lean.Karger.survives_contractTimes`,
`Cslib.Algorithms.Lean.Karger.isContractionOf_of_mem_support_contractTimes`), carried through that
law.

## Source statements and notation mapping

* **Matrix contraction and survival bound (paraphrase):**
  - `[KargerStein1996]`, Section 2, Lemma 2.1, Theorem 2.2, and Corollary 2.3, and Section 2.1,
    Corollary 2.4 (paraphrase): contracting an `n`-vertex weighted multigraph from `k` down to `t`
    supervertices via edge-weight-proportional selection preserves any fixed minimum cut with
    probability at least `C(t, 2) / C(k, 2) = t * (t - 1) / (k * (k - 1))` (`[Karger1993]`,
    Section 2, Theorem 2.1 and `[MitzenmacherUpfal2017]`, Section 1.5, Theorem 1.8 give the `t = 2`
    case `2 / (n * (n - 1))`).
  - `[KargerStein1996]`, Section 3 ("Implementing the Contraction Algorithm"), Section 3.1,
    Lemma 3.1 and Section 3.2, Corollary 3.2 (paraphrase): maintaining an `n × n` weighted
    adjacency matrix `W` and row-degree array `D[u] = ∑ v, W[u, v]` selects each edge `(u, v)` with
    probability `2 * W[u, v] / ∑ w, D[w]` and executes the Contraction Algorithm in `O(n ^ 2)`
    total time (`O(n)` per contraction step in `[KargerStein1996]`, Section 3.2).
* **Notation mapping and implementation variants:**
  - `C(t, 2) / C(k, 2)` ↔ `((t * (t - 1) : ℕ) : ℝ≥0∞) / (k * (k - 1))` in `contractDownTo_spec`
    and `contractDownToAt_spec`;
  - whereas `[KargerStein1996]`, Section 3.1 draws twice (`u` proportional to `D[u]` then `v`
    proportional to `W[u, v]` via two `Random-Select` calls), our `contractDownTo` uses an
    equivalent single-draw variant: one unit-cost word-RAM `rand` instruction drawing uniformly from
    `{0, …, totS - 1}` (`totS = totalDoubledWeight W`), resolved through linear prefix-sum scans
    `uScan` over `D[0..k)` and `vScan` over `W[u, 0..k)` to select each unordered pair `{u, v}` with
    the same probability `2 * W[u, v] / totS` of Lemma 3.1;
  - whereas `[KargerStein1996]`, Section 3.2 updates rows and columns in `O(n)` per contraction by
    zeroing the removed vertex in place, our `contractDownTo` swap-compacts active slot `k - 1` into
    `v` so each contraction step on `k` active supervertices runs in `O(k)` instructions.

## Main definitions

* `Cslib.Algorithms.WordRAM.Karger.flattenMatrix`: the row-major `n ^ 2`-word input layout of a
  weight matrix.
* `Cslib.Algorithms.WordRAM.Karger.HoldsMatrix`,
  `Cslib.Algorithms.WordRAM.Karger.HoldsWorkspace`,
  `Cslib.Algorithms.WordRAM.Karger.workspaceFootprint`,
  `Cslib.Algorithms.WordRAM.Karger.ContractState`: relocatable memory layout and word-bound
  invariants for an active `k × k` supervertex adjacency matrix with row stride `stride` and row
  degree array at `dBase`.
* `Cslib.Algorithms.WordRAM.Karger.heldGraph`: the graph a machine state holds, as a state of
  `Cslib.Algorithms.Lean.Karger.spec`.
* `Cslib.Algorithms.WordRAM.Karger.computeDegreesAndTotal`,
  `Cslib.Algorithms.WordRAM.Karger.computeDegreesAndTotalAt`: deterministic `O(k ^ 2)` initializer
  populating `D[0..k)` and `totS`.
* `Cslib.Algorithms.WordRAM.Karger.contractDownTo`,
  `Cslib.Algorithms.WordRAM.Karger.contractDownToAt`: randomized contraction loop from `activeK`
  down to `targetT`.

## Main results

* `Cslib.Algorithms.WordRAM.Karger.computeDegreesAndTotal_exec`: `computeDegreesAndTotal` populates
  `HoldsWorkspace` and `totS = totalDoubledWeight W` within `6 * k ^ 2 + 12 * k + 6` instructions,
  modifying only `Finset.Ico dBase (dBase + k)`.
* `Cslib.Algorithms.WordRAM.Karger.contractDownTo_law`: `contractDownTo` simulates `k - t`
  contractions of the specification: `ExecRandLaw` with `IsQueryBounded (k - t)`, worst-case step
  bound `36 * (k ^ 2 - t ^ 2) + 4`, `Modifies` frame, and the law of `heldGraph`.
* `Cslib.Algorithms.WordRAM.Karger.contractDownToAt_law`: the same on any `r ≥ 16` registers,
  preserving the caller's registers.
* `Cslib.Algorithms.WordRAM.Karger.ContractState.mem_add_one`: on two supervertices, the weight
  between them is half the total weight of the held graph.
* `Cslib.Algorithms.WordRAM.Karger.contractDownTo_spec`: joint certificate of `ExecRand`,
  `IsQueryBounded (k - t)`, worst-case step bound `36 * (k ^ 2 - t ^ 2) + 4`, `Modifies` frame,
  contraction invariant `IsContractionOf`, and cut-survival probability lower bound
  `((t * (t - 1) : ℕ) : ℝ≥0∞) / (k * (k - 1))`, the last two from the specification.

## References

* [D. R. Karger, *Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut
  Algorithm*][Karger1993]
* [D. R. Karger and C. Stein, *A New Approach to the Minimum Cut Problem*][KargerStein1996]
-/

@[expose] public section

namespace Cslib.Algorithms.WordRAM.Karger

open scoped ENNReal
open Cslib.WeightedCut
open Cslib.Probability.PMF
open Cslib.WordRAM
open Cslib.Algorithms.Karger

/-! ### Register layout (`r = 16`) -/

namespace Reg

/-- Constant `0`. -/
abbrev zero : Fin 16 := 0
/-- Constant `1`. -/
abbrev one : Fin 16 := 1
/-- Base address of active adjacency matrix `W`. -/
abbrev wBase : Fin 16 := 2
/-- Base address of active row-degree array `D`. -/
abbrev dBase : Fin 16 := 3
/-- Row stride (`≥ activeK`) of the matrix buffer at `wBase`. -/
abbrev stride : Fin 16 := 4
/-- Current number `k` of active supervertices. -/
abbrev activeK : Fin 16 := 5
/-- Target number `t` of active supervertices (`2 ≤ t ≤ k`). -/
abbrev targetT : Fin 16 := 6
/-- Current doubled total weight `S = totalDoubledWeight W`. -/
abbrev totS : Fin 16 := 7
/-- Sampled / outer row index `u`. -/
abbrev uReg : Fin 16 := 8
/-- Sampled / inner column index `v`. -/
abbrev vReg : Fin 16 := 9
/-- Loop index for merge and compaction sweeps. -/
abbrev idx : Fin 16 := 10
/-- Sample remainder / scratch address register. -/
abbrev rem : Fin 16 := 11
/-- Scratch pointer 1. -/
abbrev addr1 : Fin 16 := 12
/-- Scratch pointer 2. -/
abbrev addr2 : Fin 16 := 13
/-- Scratch value 1. -/
abbrev val1 : Fin 16 := 14
/-- Scratch value 2. -/
abbrev val2 : Fin 16 := 15

end Reg

/-! ### Row-major input layout of the matrix -/

/-- Row-major `n * n`-element list encoding of `W : Fin n → Fin n → ℕ`. -/
def flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) : List ℕ :=
  List.ofFn fun idx : Fin (n * n) =>
    W ⟨idx.val / n, Nat.div_lt_of_lt_mul idx.isLt⟩
      ⟨idx.val % n, Nat.mod_lt _
        (Nat.pos_of_ne_zero fun h0 => Nat.not_lt_zero idx.val (by simpa [h0] using idx.isLt))⟩

@[simp]
theorem length_flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) :
    (flattenMatrix W).length = n * n := by
  simp [flattenMatrix]

theorem getElem_flattenMatrix {n : ℕ} (W : Fin n → Fin n → ℕ) (u v : Fin n) :
    (flattenMatrix W)[u.val * n + v.val]'(by
      rw [length_flattenMatrix]
      nlinarith [u.isLt, v.isLt]) = W u v := by
  simp only [flattenMatrix, List.getElem_ofFn]
  congr 1 <;> exact Fin.ext (by
    first | exact Nat.mul_add_div_of_lt _ v.isLt | exact Nat.mul_add_mod_of_lt v.isLt)

theorem mem_flattenMatrix_le_totalDoubledWeight {n : ℕ} (W : Fin n → Fin n → ℕ)
    {x : ℕ} (hx : x ∈ flattenMatrix W) :
    x ≤ totalDoubledWeight W := by
  rcases List.mem_ofFn.mp hx with ⟨_, rfl⟩
  exact entry_le_totalDoubledWeight W _ _

/-! ### Relocatable workspace representation and address geometry -/

/-- Memory `mem` stores `W : Fin k → Fin k → ℕ` at base address `wb` with row stride `str`. -/
def HoldsMatrix (mem : ℕ → ℕ) (wb str : ℕ) {k : ℕ} (W : Fin k → Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, mem (wb + i.val * str + j.val) = W i j

/-- In `Data.init (pfx ++ flattenMatrix W)`, the flattened matrix occupies memory starting at
`1 + pfx.length` with stride `n`. -/
theorem holdsMatrix_init_append {r n : ℕ} (pfx : List ℕ) (W : Fin n → Fin n → ℕ) :
    HoldsMatrix (Data.init (r := r) (pfx ++ flattenMatrix W)).mem (1 + pfx.length) n W := by
  intro i j
  have hlt : i.val * n + j.val < (flattenMatrix W).length := by
    rw [length_flattenMatrix]
    have h1 := Nat.mul_le_mul_right n i.isLt
    rw [Nat.succ_mul] at h1; omega
  rw [show (1 + pfx.length) + i.val * n + j.val = (pfx.length + (i.val * n + j.val)) + 1 by omega,
    Data.init_mem_succ, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (Nat.le_add_right pfx.length _)]
  simpa only [Nat.add_sub_cancel_left, List.getElem?_eq_getElem hlt, Option.getD_some] using
    getElem_flattenMatrix W i j

/-- In `Data.init (n :: flattenMatrix W)`, memory holds `W` at base `2` with stride `n`. -/
theorem holdsMatrix_init_single {r n : ℕ} (W : Fin n → Fin n → ℕ) :
    HoldsMatrix (Data.init (r := r) (n :: flattenMatrix W)).mem 2 n W :=
  holdsMatrix_init_append [n] W

/-- The input `a :: flattenMatrix W` fits word size `w` when one fitting bound `B` covers both
the input length `1 + n * n` and the leading word `a`, and the matrix total fits. -/
theorem inputFits_cons_flattenMatrix {w a n B : ℕ} {W : Fin n → Fin n → ℕ} (hB : Fits w B)
    (hlen : 1 + n * n ≤ B) (ha : a ≤ B) (htot : Fits w (totalDoubledWeight W)) :
    InputFits w (a :: flattenMatrix W) :=
  ⟨by simpa only [List.length_cons, length_flattenMatrix] using hB.of_le (by omega),
    List.forall_mem_cons.mpr ⟨hB.of_le ha, fun _ hmem =>
      htot.of_le (mem_flattenMatrix_le_totalDoubledWeight W hmem)⟩⟩

/-- Memory `mem` stores `W : Fin k → Fin k → ℕ` at `(wb, str)` and its row degrees `rowDeg W` at
`db`. -/
def HoldsWorkspace (mem : ℕ → ℕ) (wb db str : ℕ) {k : ℕ} (W : Fin k → Fin k → ℕ) : Prop :=
  HoldsMatrix mem wb str W ∧ ∀ i : Fin k, mem (db + i.val) = rowDeg W i

/-- Permitted memory write footprint of an active `k`-supervertex workspace at `(wb, db, str)`. -/
def workspaceFootprint (wb db str k : ℕ) : Finset ℕ :=
  Finset.Ico wb (wb + str * k) ∪ Finset.Ico db (db + k)

/-- Machine-state precondition for `contractDownTo` on `k` active supervertices targeting `t`. -/
structure ContractState (w wb db str k t : ℕ) (W : Fin k → Fin k → ℕ) (x : Data 16) : Prop where
  regs_wBase : x.regs Reg.wBase = wb
  regs_dBase : x.regs Reg.dBase = db
  regs_stride : x.regs Reg.stride = str
  regs_activeK : x.regs Reg.activeK = k
  regs_targetT : x.regs Reg.targetT = t
  regs_totS : x.regs Reg.totS = totalDoubledWeight W
  le_stride : k ≤ str
  disjoint_blocks : wb + str * k ≤ db ∨ db + k ≤ wb
  fits_wEnd : Fits w (wb + str * k)
  fits_dEnd : Fits w (db + k)
  fits_totS : Fits w (totalDoubledWeight W)
  workspace : HoldsWorkspace x.mem wb db str W

/-- The graph that a machine state holds in the workspace at `wb` with row stride `str`: `activeK`
supervertices, with the weight matrix read from memory. It abstracts a `ContractState` to a state
of the contraction structure `Lean.Karger.spec`. -/
def heldGraph (wb str : ℕ) (x : Data 16) : Lean.Karger.Graph :=
  ⟨x.regs Reg.activeK, fun i j => x.mem (wb + i.val * str + j.val)⟩

/-- A state holding `W` on `k` supervertices holds the graph `⟨k, W⟩`. -/
theorem ContractState.heldGraph_eq {w wb db str k t : ℕ} {W : Fin k → Fin k → ℕ} {x : Data 16}
    (hst : ContractState w wb db str k t W x) : heldGraph wb str x = ⟨k, W⟩ := by
  unfold heldGraph
  rw [hst.regs_activeK]
  exact congrArg _ (funext₂ hst.workspace.1)

/-- On two supervertices, the weight between them, at `wb + 1`, is half the total weight of the
held graph. -/
theorem ContractState.mem_add_one {w wb db str t : ℕ} {W : Fin 2 → Fin 2 → ℕ} {x : Data 16}
    (hst : ContractState w wb db str 2 t W x) (hW : IsMultigraph W) :
    x.mem (wb + 1) = totalDoubledWeight (heldGraph wb str x).weight / 2 := by
  rw [hst.heldGraph_eq]
  change _ = totalDoubledWeight W / 2
  rw [totalDoubledWeight_fin_two hW, show x.mem (wb + 1) = W 0 1 by simpa using hst.workspace.1 0 1]
  omega

/-- The weight matrix of a state is the weight of the graph it holds. -/
private theorem ContractState.eq_of_heldGraph_eq {w wb db str k t : ℕ} {W W' : Fin k → Fin k → ℕ}
    {x : Data 16} (hst : ContractState w wb db str k t W x) (h : heldGraph wb str x = ⟨k, W'⟩) :
    W = W' := by
  simpa only [Lean.Karger.Graph.mk.injEq, heq_eq_eq, true_and] using hst.heldGraph_eq.symm.trans h

theorem matAddr_lt_end {wb str k : ℕ} (hstr : k ≤ str) (i j : Fin k) :
    wb + i.val * str + j.val < wb + str * k := by
  have hj : j.val < str := lt_of_lt_of_le j.isLt hstr
  have hmul : (i.val + 1) * str ≤ k * str := Nat.mul_le_mul_right str i.isLt
  rw [Nat.succ_mul, Nat.mul_comm k str] at hmul
  omega

theorem matAddr_mem_Ico {wb str k : ℕ} (hstr : k ≤ str) (i j : Fin k) :
    wb + i.val * str + j.val ∈ Finset.Ico wb (wb + str * k) :=
  Finset.mem_Ico.mpr ⟨by omega, matAddr_lt_end hstr i j⟩

theorem degAddr_mem_Ico {db k : ℕ} (i : Fin k) :
    db + i.val ∈ Finset.Ico db (db + k) :=
  Finset.mem_Ico.mpr ⟨by omega, by omega⟩

theorem matAddr_inj {wb str k : ℕ} (hstr : k ≤ str) {i₁ j₁ i₂ j₂ : Fin k}
    (h : wb + i₁.val * str + j₁.val = wb + i₂.val * str + j₂.val) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hj₁ : j₁.val < str := lt_of_lt_of_le j₁.isLt hstr
  have hj₂ : j₂.val < str := lt_of_lt_of_le j₂.isLt hstr
  have hi_eq : i₁.val = i₂.val := by
    rcases lt_trichotomy i₁.val i₂.val with hlt | heq | hgt
    · have := Nat.mul_le_mul_right str hlt; rw [Nat.succ_mul] at this; omega
    · exact heq
    · have := Nat.mul_le_mul_right str hgt; rw [Nat.succ_mul] at this; omega
  exact ⟨Fin.ext hi_eq, Fin.ext (by rw [hi_eq] at h; omega)⟩

theorem matAddr_ne_degAddr {wb db str k : ℕ} (hstr : k ≤ str)
    (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb) (i j l : Fin k) :
    wb + i.val * str + j.val ≠ db + l.val := by
  have hm := matAddr_lt_end (wb := wb) hstr i j
  have hl := l.isLt
  omega

theorem workspaceFootprint_mono {wb db str k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) :
    workspaceFootprint wb db str k₁ ⊆ workspaceFootprint wb db str k₂ := by
  intro a ha
  simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico] at ha ⊢
  have hmul : str * k₁ ≤ str * k₂ := Nat.mul_le_mul_left str hle
  omega

/-- A square workspace `workspaceFootprint wb db k k` lies in `[a, b)` whenever `a ≤ wb`,
`wb + k * k ≤ db` and `db + k ≤ b`. -/
theorem workspaceFootprint_subset_Ico {a b wb db k : ℕ}
    (haw : a ≤ wb) (hwd : wb + k * k ≤ db) (hdb : db + k ≤ b) :
    workspaceFootprint wb db k k ⊆ Finset.Ico a b := by
  intro x hx
  simp only [workspaceFootprint, Finset.mem_union, Finset.mem_Ico] at hx ⊢
  omega

theorem modifies_trans_subset {F F₁ F₂ : Finset ℕ} {m₀ m₁ m₂ : ℕ → ℕ}
    (h₁ : Modifies F₁ m₀ m₁) (h₂ : Modifies F₂ m₁ m₂) (hs₁ : F₁ ⊆ F) (hs₂ : F₂ ⊆ F) :
    Modifies F m₀ m₂ := fun a ha =>
  (h₂ a fun h => ha (hs₂ h)).trans (h₁ a fun h => ha (hs₁ h))

theorem modifies_update_of_mem {F : Finset ℕ} {a : ℕ} (ha : a ∈ F) (m : ℕ → ℕ) (v : ℕ) :
    Modifies F m (Function.update m a v) :=
  fun b hb => Function.update_of_ne (fun h : b = a => hb (h ▸ ha)) v m

private theorem modifies_step_update {F : Finset ℕ} {m₁ m₂ : ℕ → ℕ} {a : ℕ}
    (h : Modifies F m₁ m₂) (ha : a ∈ F) (v : ℕ) :
    Modifies F m₁ (Function.update m₂ a v) :=
  modifies_trans_subset h (modifies_update_of_mem ha m₂ v) Finset.Subset.rfl Finset.Subset.rfl

private theorem update_matAddr_eq {wb str k : ℕ} (hstr : k ≤ str) (m : ℕ → ℕ)
    (a b i j : Fin k) (v : ℕ) :
    Function.update m (wb + a.val * str + b.val) v (wb + i.val * str + j.val) =
      if i = a ∧ j = b then v else m (wb + i.val * str + j.val) := by
  by_cases h : i = a ∧ j = b
  · rcases h with ⟨rfl, rfl⟩; simp
  · simp [h, Function.update_of_ne (fun heq => h (matAddr_inj hstr heq))]

private theorem update_degAddr_of_matAddr {wb db str k : ℕ} (hstr : k ≤ str)
    (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb) (m : ℕ → ℕ) (a b l : Fin k) (v : ℕ) :
    Function.update m (wb + a.val * str + b.val) v (db + l.val) = m (db + l.val) :=
  Function.update_of_ne (matAddr_ne_degAddr hstr hdisj a b l).symm v m

private theorem update_matAddr_of_degAddr {wb db str k : ℕ} (hstr : k ≤ str)
    (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb) (m : ℕ → ℕ) (l i j : Fin k) (v : ℕ) :
    Function.update m (db + l.val) v (wb + i.val * str + j.val) =
      m (wb + i.val * str + j.val) :=
  Function.update_of_ne (matAddr_ne_degAddr hstr hdisj i j l) v m

private theorem rowDeg_mergePair_u_le_contract {m : ℕ} {W : Fin (m + 1) → Fin (m + 1) → ℕ}
    {u v : Fin (m + 1)} (huv : u ≠ v) :
    rowDeg (mergePair W u v) u ≤ totalDoubledWeight (contractMatrix W u v) := by
  have hidx : rowDeg (mergePair W u v) u =
      rowDeg (contractMatrix W u v) (compactIdx v u huv) := by
    rw [rowDeg_contractMatrix, embedCompact_compactIdx]
  exact hidx ▸ rowDeg_le_totalDoubledWeight _ _

/-! ### Prefix sums and workspace register frame -/

/-- Sum of `f b` over active indices `b : Fin k` with `b.val < j`. -/
private def prefixSum {k : ℕ} (f : Fin k → ℕ) (j : ℕ) : ℕ :=
  ∑ b ∈ Finset.univ.filter (fun b : Fin k => b.val < j), f b

/-- `prefixSum` at `0` is `0`. -/
private theorem prefixSum_zero {k : ℕ} (f : Fin k → ℕ) : prefixSum f 0 = 0 := by
  simp [prefixSum]

/-- `prefixSum` splits off its `j`-th term when `j < k`. -/
private theorem prefixSum_succ {k j : ℕ} (hj : j < k) (f : Fin k → ℕ) :
    prefixSum f (j + 1) = prefixSum f j + f ⟨j, hj⟩ := by
  have hlt : Finset.univ.filter (fun b : Fin k => b.val < j) = Finset.Iio ⟨j, hj⟩ := by
    simpa [Fin.lt_def] using Finset.filter_gt_eq_Iio (a := (⟨j, hj⟩ : Fin k))
  have hle : Finset.univ.filter (fun b : Fin k => b.val ≤ j) = Finset.Iic ⟨j, hj⟩ := by
    simpa [Fin.le_def] using Finset.filter_ge_eq_Iic (a := (⟨j, hj⟩ : Fin k))
  simp_rw [prefixSum, Nat.lt_succ_iff, hle, hlt, ← Finset.sum_Iio_add_eq_sum_Iic]

/-- `prefixSum` up to `k` is the full `Finset.univ` sum. -/
private theorem prefixSum_full {k : ℕ} (f : Fin k → ℕ) :
    prefixSum f k = ∑ b : Fin k, f b := by
  simp [prefixSum]

/-- `prefixSum` is monotone in its cutoff `j`. -/
private theorem prefixSum_mono {k : ℕ} (f : Fin k → ℕ) {i j : ℕ} (hle : i ≤ j) :
    prefixSum f i ≤ prefixSum f j :=
  Finset.sum_le_sum_of_subset fun b hb => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    omega

/-- Any `prefixSum` is bounded by the full sum over `Fin k`. -/
private theorem prefixSum_le_sum {k : ℕ} (f : Fin k → ℕ) (j : ℕ) :
    prefixSum f j ≤ ∑ b : Fin k, f b :=
  Finset.sum_le_univ_sum_of_nonneg fun _ => Nat.zero_le _

/-- `degBefore W a` as a `prefixSum` of `rowDeg W`. -/
private theorem degBefore_eq_prefixSum {k : ℕ} (W : Fin k → Fin k → ℕ) (a : Fin k) :
    degBefore W a = prefixSum (rowDeg W) a.val := by
  simp only [degBefore, prefixSum, Fin.lt_def]

/-- `weightBefore W u b` as a `prefixSum` of row `W u`. -/
private theorem weightBefore_eq_prefixSum {k : ℕ} (W : Fin k → Fin k → ℕ) (u b : Fin k) :
    weightBefore W u b = prefixSum (W u) b.val := by
  simp only [weightBefore, prefixSum, Fin.lt_def]

/-- Row offset `idx * str` and row pointer `wb + idx * str` both fit word size `w` whenever
`idx ≤ k` and `wb + str * k` fits. -/
private theorem rowBase_fits {w wb str k idx : ℕ} (hwEnd : Fits w (wb + str * k))
    (hle : idx ≤ k) : Fits w (idx * str) ∧ Fits w (wb + idx * str) := by
  have hmul : idx * str ≤ str * k :=
    Nat.mul_comm k str ▸ Nat.mul_le_mul_right str hle
  exact ⟨hwEnd.of_le (by omega), hwEnd.of_le (by omega)⟩

/-- Shared read-only register frame (`zero`, `one`, `wBase`, `dBase`, `stride`, `activeK`,
`targetT`) preserved across workspace helper phases. -/
private structure KargerFrame (wb db str k t : ℕ) (y : Data 16) : Prop where
  zero_eq : y.regs Reg.zero = 0
  one_eq : y.regs Reg.one = 1
  wBase_eq : y.regs Reg.wBase = wb
  dBase_eq : y.regs Reg.dBase = db
  stride_eq : y.regs Reg.stride = str
  activeK_eq : y.regs Reg.activeK = k
  targetT_eq : y.regs Reg.targetT = t

/-! ### Part 1: Deterministic `O(k ^ 2)` row-degree and total-weight initializer -/

section ComputeDegrees

open Reg

/-- Inner loop body accumulating `W[u, v]` into `val1`. -/
def degInnerBody : Code .standard 16 := ram[
  addr2 ← addr1 + vReg;
  val2 ← *addr2;
  val1 ← val1 + val2;
  vReg ← vReg + one
]

/-- Outer loop body computing `D[u] = rowDeg W u` and adding it to `totS`. -/
def degOuterBody : Code .standard 16 := ram[
  val2 ← uReg * stride;
  addr1 ← wBase + val2;
  val1 ← #0;
  vReg ← #0;
  while vReg < activeK do [ ⟪degInnerBody⟫ ];
  addr2 ← dBase + uReg;
  *addr2 ← val1;
  totS ← totS + val1;
  uReg ← uReg + one
]

/-- Compute all row degrees `D[0..k)` at `dBase` and `totS = totalDoubledWeight W` from `W` at
`(wBase, stride)` in `6 * k ^ 2 + 12 * k + 6` instructions. -/
def computeDegreesAndTotal : Code .standard 16 := ram[
  zero ← #0;
  one ← #1;
  totS ← #0;
  uReg ← #0;
  while uReg < activeK do [ ⟪degOuterBody⟫ ]
]

/-- Inner `degInnerBody` loop computing `rowDeg W u` in `val1` in `6 * k + 2` instructions. -/
private theorem degInnerLoop_exec {w wb db str k t : ℕ} {W : Fin k → Fin k → ℕ}
    (u : Fin k) {x : Data 16} (hstr : k ≤ str)
    (hwEnd : Fits w (wb + str * k)) (hdEnd : Fits w (db + k))
    (htot : Fits w (totalDoubledWeight W)) (hmat : HoldsMatrix x.mem wb str W)
    (hf : KargerFrame wb db str k t x) (hu : x.regs uReg = u.val)
    (ha1 : x.regs addr1 = wb + u.val * str) (hv : x.regs vReg = 0) (hv1 : x.regs val1 = 0) :
    ∃ q, ExecWithin w ram[while vReg < activeK do [ ⟪degInnerBody⟫ ]] x q (6 * k + 2) ∧
      KargerFrame wb db str k t q ∧ q.regs uReg = u.val ∧ q.regs totS = x.regs totS ∧
      q.regs val1 = rowDeg W u ∧ q.mem = x.mem := by
  let Inv (q : Data 16) : Prop :=
    KargerFrame wb db str k t q ∧ q.regs uReg = u.val ∧ q.regs totS = x.regs totS ∧
    q.regs addr1 = wb + u.val * str ∧ q.regs vReg ≤ k ∧
    q.regs val1 = prefixSum (W u) (q.regs vReg) ∧ q.mem = x.mem
  have hbody : ∀ q, Inv q → (Cond.lt vReg activeK).Holds q →
      ∃ q', ExecWithin w degInnerBody q q' 4 ∧ Inv q' ∧ k - q'.regs vReg < k - q.regs vReg := by
    rintro q ⟨hqf, hqu, hqtot, hqa1, hqv_le, hqval1, hqmem⟩ hvc
    obtain ⟨v_val, hv_eq⟩ : ∃ v_val, q.regs vReg = v_val := ⟨_, rfl⟩
    have hv_lt : v_val < k := by simpa [Cond.holds_lt, hv_eq, hqf.activeK_eq] using hvc
    let v : Fin k := ⟨v_val, hv_lt⟩
    have hcell_fit : Fits w (wb + u.val * str + v_val) :=
      hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr u v))
    have hsum_fit : Fits w (prefixSum (W u) v_val + W u v) :=
      prefixSum_succ hv_lt (W u) ▸ htot.of_le ((prefixSum_le_sum (W u) (v_val + 1)).trans
        (rowDeg_le_totalDoubledWeight W u))
    have hv_fit : Fits w (v_val + 1) := hdEnd.of_le (by omega)
    have hread : q.mem (wb + u.val * str + v_val) = W u v := hqmem ▸ hmat u v
    rw [hv_eq] at hqval1
    unfold degInnerBody
    wram_exec [hqf.one_eq, hqa1, hv_eq, hread, hqval1, hcell_fit, hsum_fit, hv_fit]
    refine ⟨⟨by struct_frame hqf, by wram_simp [hqu], by wram_simp [hqtot],
      by wram_simp [hqa1], by wram_simp; omega, ?_, hqmem⟩, by wram_simp [hv_eq]; omega⟩
    wram_simp [prefixSum_succ hv_lt (W u)]; rfl
  obtain ⟨q, hloop, ⟨hqf, hqu, hqtot, _, hqv_le, hqval1, hqmem⟩, hvc⟩ :=
    ExecWithin.loop_invariant Inv (fun q => k - q.regs vReg) hbody
      ⟨hf, hu, rfl, ha1, by omega, by rw [hv, hv1, prefixSum_zero], rfl⟩
  have hv_end : q.regs vReg = k := by simp only [Cond.holds_lt, hqf.activeK_eq] at hvc; omega
  exact ⟨q, hloop.mono (by rw [hv]; omega), hqf, hqu, hqtot,
    by rw [hqval1, hv_end, prefixSum_full]; rfl, hqmem⟩

/-- `computeDegreesAndTotal` initializes `D[0..k)` and `totS` in `6 * k ^ 2 + 12 * k + 6`
instructions while modifying only `Finset.Ico db (db + k)`. -/
theorem computeDegreesAndTotal_exec {w wb db str k : ℕ} {W : Fin k → Fin k → ℕ} {x : Data 16}
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = k)
    (hstr : k ≤ str) (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb)
    (h1 : Fits w 1) (hwEnd : Fits w (wb + str * k)) (hdEnd : Fits w (db + k))
    (htot : Fits w (totalDoubledWeight W)) (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y, ExecWithin w computeDegreesAndTotal x y (6 * k ^ 2 + 12 * k + 6) ∧
      HoldsWorkspace y.mem wb db str W ∧
      Modifies (Finset.Ico db (db + k)) x.mem y.mem ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = k ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight W := by
  let OuterInv (y : Data 16) : Prop :=
    KargerFrame wb db str k (x.regs targetT) y ∧
    y.regs uReg ≤ k ∧
    y.regs totS = prefixSum (rowDeg W) (y.regs uReg) ∧
    HoldsMatrix y.mem wb str W ∧
    Modifies (Finset.Ico db (db + k)) x.mem y.mem ∧
    ∀ a : Fin k, a.val < y.regs uReg → y.mem (db + a.val) = rowDeg W a
  have houter_body : ∀ y, OuterInv y → (Cond.lt uReg activeK).Holds y →
      ∃ z, ExecWithin w degOuterBody y z (6 * k + 10) ∧ OuterInv z ∧
        k - z.regs uReg < k - y.regs uReg := by
    rintro y ⟨hyf, hyu_le, hytot, hymat, hymod, hydeg⟩ hc
    obtain ⟨u_val, hu_eq⟩ : ∃ u_val, y.regs uReg = u_val := ⟨_, rfl⟩
    have hu_lt : u_val < k := by simpa [Cond.holds_lt, hu_eq, hyf.activeK_eq] using hc
    let u : Fin k := ⟨u_val, hu_lt⟩
    obtain ⟨hmul_fit, hrow_fit⟩ := rowBase_fits hwEnd (Nat.le_of_lt hu_lt)
    unfold degOuterBody
    wram_exec [hyf.stride_eq, hyf.wBase_eq, hu_eq, hmul_fit, hrow_fit]
    wram_call (degInnerLoop_exec u hstr hwEnd hdEnd htot hymat (by struct_frame hyf)
      (by wram_simp [hu_eq]; rfl) (by wram_simp; rfl) (by wram_simp) (by wram_simp))
      with q ⟨hqf, hqu, hqtot, hval1, hqmem⟩
    have hqm : q.mem = y.mem := by mem_frame
    have hqt : q.regs totS = y.regs totS := by regs_frame
    have htot_fit : Fits w (prefixSum (rowDeg W) u_val + rowDeg W u) :=
      prefixSum_succ hu_lt (rowDeg W) ▸ htot.of_le (prefixSum_le_sum (rowDeg W) (u_val + 1))
    have hdu_fit : Fits w (db + u_val) := hdEnd.of_le (by omega)
    have hu1_fit : Fits w (u_val + 1) := hdEnd.of_le (by omega)
    rw [hu_eq] at hytot
    wram_exec [hqf.dBase_eq, hqf.one_eq, (show q.regs uReg = u_val from hqu), hval1, hqt,
      hytot, hdu_fit, htot_fit, hu1_fit]
    refine ⟨⟨by struct_frame hqf, by wram_simp; omega,
      by wram_simp [prefixSum_succ hu_lt (rowDeg W)]; rfl,
      fun i j => by
        simp only [Data.set_mem, Data.write_mem, hqm]
        exact (update_matAddr_of_degAddr hstr hdisj y.mem u i j _).trans (hymat i j),
      by simpa only [Data.set_mem, Data.write_mem, hqm] using
        modifies_step_update hymod (degAddr_mem_Ico (db := db) u) (rowDeg W u),
      fun a ha => ?_⟩, by wram_simp [hu_eq]; omega⟩
    wram_simp at ha; simp only [Data.set_mem, Data.write_mem]
    obtain rfl | hne := eq_or_ne a u
    · exact Function.update_self _ _ _
    · have hau : a.val ≠ u_val := Fin.val_ne_of_ne hne
      rw [Function.update_of_ne (by omega : db + a.val ≠ db + u_val), hqm]
      exact hydeg a (by rw [hu_eq]; omega)
  unfold computeDegreesAndTotal
  wram_exec [h1]
  refine WP.name fun x₀ hx₀_eq => ?_
  have hx₀ : OuterInv x₀ := by
    subst hx₀_eq
    exact ⟨⟨by wram_simp, by wram_simp, by wram_simp [hwBase], by wram_simp [hdBase],
      by wram_simp [hstride], by wram_simp [hactiveK], by wram_simp⟩,
      by wram_simp; omega, by wram_simp [prefixSum_zero], hmat, Modifies.refl _ _,
      fun _ ha => by wram_simp at ha⟩
  have hx₀_u : x₀.regs uReg = 0 := by subst hx₀_eq; wram_simp
  obtain ⟨y_end, hloop, ⟨hyf, _, hytot, hymat, hymod, hydeg⟩, huc⟩ :=
    ExecWithin.loop_invariant OuterInv (fun y => k - y.regs uReg) houter_body hx₀
  have hu_end : y_end.regs uReg = k := by simp only [Cond.holds_lt, hyf.activeK_eq] at huc; omega
  have hmul : (k - x₀.regs uReg) * (6 * k + 10 + 2) = 6 * k ^ 2 + 12 * k := by
    rw [hx₀_u, Nat.sub_zero]; ring
  exact WP.of_execWithin hloop ⟨by omega,
    ⟨hymat, fun a => hydeg a (hu_end ▸ a.isLt)⟩, hymod,
    hyf.zero_eq, hyf.one_eq, hyf.wBase_eq, hyf.dBase_eq, hyf.stride_eq,
    hyf.activeK_eq, hyf.targetT_eq, by rw [hytot, hu_end, prefixSum_full]; rfl⟩

end ComputeDegrees

/-! ### Part 2: Single contraction step and `contractDownTo` -/

section Contract

open Reg

/-- Loop body for scanning row degrees `D[u]` until `rem ≤ D[u]`. -/
def uScanBody : Code .standard 16 := ram[
  rem ← rem - val1;
  uReg ← uReg + one;
  addr1 ← dBase + uReg;
  val1 ← *addr1
]

/-- Scan `u = 0, 1, …` from `rem = r + 1` to locate the sampled row `u` and row offset. -/
def uScan : Code .standard 16 := ram[
  rem ← rem + one;
  uReg ← #0;
  addr1 ← dBase + uReg;
  val1 ← *addr1;
  while val1 < rem do [ ⟪uScanBody⟫ ]
]

/-- Loop body for scanning row `W[u, v]` until `rem ≤ W[u, v]`. -/
def vScanBody : Code .standard 16 := ram[
  rem ← rem - val1;
  vReg ← vReg + one;
  addr2 ← addr1 + vReg;
  val1 ← *addr2
]

/-- Scan `v = 0, 1, …` along row `u` to locate the sampled column `v` (`u ≠ v`) with
`val1 = W u v`. -/
def vScan : Code .standard 16 := ram[
  val2 ← uReg * stride;
  addr1 ← wBase + val2;
  vReg ← #0;
  addr2 ← addr1 + vReg;
  val1 ← *addr2;
  while val1 < rem do [ ⟪vScanBody⟫ ]
]

/-- Update `totS`, zero `W[u, v]`, and update `D[u]` and `D[v]` for merging `v` into `u`. -/
def phaseADegrees : Code .standard 16 := ram[
  totS ← totS - val1;
  totS ← totS - val1;
  *addr2 ← zero;
  addr2 ← dBase + uReg;
  val2 ← *addr2;
  val2 ← val2 - val1;
  addr1 ← dBase + vReg;
  rem ← *addr1;
  rem ← rem - val1;
  val2 ← val2 + rem;
  *addr2 ← val2;
  *addr1 ← zero
]

/-- Set `addr1 = wBase + u * stride`, `addr2 = wBase + v * stride`, zero `W[v, u]`, and set
`idx = 0`. -/
def phaseAPtrs : Code .standard 16 := ram[
  val2 ← uReg * stride;
  addr1 ← wBase + val2;
  val2 ← vReg * stride;
  addr2 ← wBase + val2;
  rem ← addr2 + uReg;
  *rem ← zero;
  idx ← #0
]

/-- Redirect edges between `v` and `idx` (`idx ∉ {u, v}`) into `u` and zero `v`'s entries. -/
def mergeUpdate : Code .standard 16 := ram[
  rem ← addr2 + idx;
  val1 ← *rem;
  *rem ← zero;
  rem ← addr1 + idx;
  val2 ← *rem;
  val2 ← val2 + val1;
  *rem ← val2;
  val1 ← idx * stride;
  val1 ← wBase + val1;
  rem ← val1 + vReg;
  *rem ← zero;
  rem ← val1 + uReg;
  *rem ← val2
]

/-- Single iteration of the Phase A merge sweep over `idx < activeK`. -/
def mergeBody : Code .standard 16 := ram[
  if idx = uReg then [
    idx ← idx + one
  ] else [
    if idx = vReg then [
      idx ← idx + one
    ] else [
      ⟪mergeUpdate⟫;
      idx ← idx + one
    ]
  ]
]

/-- Copy `(activeK, idx)` and `(idx, activeK)` into `(vReg, idx)` and `(idx, vReg)` for
`idx ≠ v`. -/
def compactUpdate : Code .standard 16 := ram[
  rem ← addr1 + idx;
  val1 ← *rem;
  rem ← addr2 + idx;
  *rem ← val1;
  val2 ← idx * stride;
  val2 ← wBase + val2;
  rem ← val2 + vReg;
  *rem ← val1
]

/-- Single iteration of the Phase B swap-compaction sweep over `idx < m`. -/
def compactBody : Code .standard 16 := ram[
  if idx = vReg then [
    idx ← idx + one
  ] else [
    ⟪compactUpdate⟫;
    idx ← idx + one
  ]
]

/-- Setup for Phase B when `v < m`: copy `D[m]` to `D[v]` and compute row pointers for `m` and
`v`. -/
def compactSetup : Code .standard 16 := ram[
  addr1 ← dBase + activeK;
  val1 ← *addr1;
  addr2 ← dBase + vReg;
  *addr2 ← val1;
  val1 ← activeK * stride;
  addr1 ← wBase + val1;
  val1 ← vReg * stride;
  addr2 ← wBase + val1;
  idx ← #0
]

/-- Deterministic continuation of a positive-weight contraction step once `rem` holds `r < totS`. -/
def postRandStep : Code .standard 16 := ram[
  ⟪uScan⟫;
  ⟪vScan⟫;
  ⟪phaseADegrees⟫;
  ⟪phaseAPtrs⟫;
  while idx < activeK do [ ⟪mergeBody⟫ ];
  activeK ← activeK - one;
  if vReg < activeK then [
    ⟪compactSetup⟫;
    while idx < activeK do [ ⟪compactBody⟫ ]
  ] else [
    idx ← #0
  ]
]

/-- One supervertex contraction step: deterministic merge when `totS = 0`, and edge-proportional
random contraction otherwise. -/
def contractStep : Code .standard 16 := ram[
  if totS = zero then [
    activeK ← activeK - one
  ] else [
    val1 ← totS - one;
    rem ← rand val1;
    ⟪postRandStep⟫
  ]
]

/-- Workspace-relocatable randomized contraction loop from `activeK` down to `targetT`. -/
def contractDownTo : Code .standard 16 := ram[
  zero ← #0;
  one ← #1;
  while targetT < activeK do [ ⟪contractStep⟫ ]
]

/-! #### Intermediate matrix invariants for `mergeLoop` and `compactLoop` -/

private def mergeStepMatrix {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k) (idx : ℕ)
    (i j : Fin k) : ℕ :=
  if ((i = u ∨ i = v) ∧ j ≠ u ∧ j ≠ v ∧ idx ≤ j.val) ∨
     ((j = u ∨ j = v) ∧ i ≠ u ∧ i ≠ v ∧ idx ≤ i.val) then
    W i j
  else
    mergePair W u v i j

private theorem mergeStepMatrix_zero {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {u v : Fin k} (i j : Fin k) :
    mergeStepMatrix W u v 0 i j =
      if (i = u ∧ j = v) ∨ (i = v ∧ j = u) then 0 else W i j := by
  unfold mergeStepMatrix
  simp only [Nat.zero_le, and_true]
  by_cases hiu : i = u <;> by_cases hiv : i = v <;>
    by_cases hju : j = u <;> by_cases hjv : j = v
  all_goals simp_all [mergePair, hW.2]

private theorem mergeStepMatrix_full {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k)
    (i j : Fin k) :
    mergeStepMatrix W u v k i j = mergePair W u v i j := by
  simp [mergeStepMatrix, Nat.not_le_of_lt i.isLt, Nat.not_le_of_lt j.isLt]

private theorem mergeStepMatrix_step_eq_of_mem {k : ℕ} (W : Fin k → Fin k → ℕ) (u v : Fin k)
    {c : ℕ} (hc : c = u.val ∨ c = v.val) (i j : Fin k) :
    mergeStepMatrix W u v (c + 1) i j = mergeStepMatrix W u v c i j := by
  have aux {a b : Fin k} :
      ((a = u ∨ a = v) ∧ b ≠ u ∧ b ≠ v ∧ c + 1 ≤ b.val) ↔
        ((a = u ∨ a = v) ∧ b ≠ u ∧ b ≠ v ∧ c ≤ b.val) :=
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by omega⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by
      rcases hc with rfl | rfl
      · have := Fin.val_ne_of_ne h2; omega
      · have := Fin.val_ne_of_ne h3; omega⟩⟩
  simp only [mergeStepMatrix, aux]

private theorem mergeStepMatrix_succ {k : ℕ} {W : Fin k → Fin k → ℕ} (hW : IsMultigraph W)
    {u v c : Fin k} (huv : u ≠ v) (hcu : c ≠ u) (hcv : c ≠ v) (i j : Fin k) :
    (if i = c ∧ j = u then W u c + W v c
      else if i = c ∧ j = v then 0
      else if i = u ∧ j = c then W u c + W v c
      else if i = v ∧ j = c then 0
      else mergeStepMatrix W u v c.val i j) =
      mergeStepMatrix W u v (c.val + 1) i j := by
  have hstep {a b : Fin k} (hab : ¬ (a = u ∧ b = c) ∧ ¬ (a = v ∧ b = c)) :
      ((a = u ∨ a = v) ∧ b ≠ u ∧ b ≠ v ∧ c.val ≤ b.val) ↔
        ((a = u ∨ a = v) ∧ b ≠ u ∧ b ≠ v ∧ c.val + 1 ≤ b.val) :=
    ⟨fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by
      have hbc : b ≠ c := fun h => h1.elim (fun ha => hab.1 ⟨ha, h⟩) (fun ha => hab.2 ⟨ha, h⟩)
      have := Fin.val_ne_of_ne hbc; omega⟩, fun ⟨h1, h2, h3, h4⟩ => ⟨h1, h2, h3, by omega⟩⟩
  have hnc : ¬ (c.val + 1 ≤ c.val) := by omega
  split_ifs with h_cu h_cv h_uc h_vc
  · rw [h_cu.1, h_cu.2]
    simp [mergeStepMatrix, mergePair, hcu, hcv, huv, hnc, hW.1 c u, hW.1 c v]
  · rw [h_cv.1, h_cv.2]
    simp [mergeStepMatrix, mergePair, hcu, hcv, hnc]
  · rw [h_uc.1, h_uc.2]
    simp [mergeStepMatrix, mergePair, hcu, hcu.symm, hcv, huv, hnc]
  · rw [h_vc.1, h_vc.2]
    simp [mergeStepMatrix, mergePair, hcu, hcv, hnc]
  · simp only [mergeStepMatrix, hstep ⟨h_uc, h_vc⟩,
      hstep ⟨fun ⟨hj, hi⟩ => h_cu ⟨hi, hj⟩, fun ⟨hj, hi⟩ => h_cv ⟨hi, hj⟩⟩]

private def compactStepMatrix {m : ℕ} (W₁ : Fin (m + 1) → Fin (m + 1) → ℕ)
    (v : Fin (m + 1)) (idx : ℕ) (i j : Fin m) : ℕ :=
  if (i.val = v.val ∧ j.val ≠ v.val ∧ idx ≤ j.val) ∨
     (j.val = v.val ∧ i.val ≠ v.val ∧ idx ≤ i.val) then
    W₁ i.castSucc j.castSucc
  else
    W₁ (embedCompact v i) (embedCompact v j)

private theorem compactStepMatrix_zero {m : ℕ} {W₁ : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hW₁ : IsMultigraph W₁) {v : Fin (m + 1)} (i j : Fin m) :
    compactStepMatrix W₁ v 0 i j = W₁ i.castSucc j.castSucc := by
  unfold compactStepMatrix embedCompact
  simp only [Nat.zero_le, and_true]
  by_cases hi : i.val = v.val <;> by_cases hj : j.val = v.val
  · obtain rfl : i = j := Fin.ext (hi.trans hj.symm); simp [hi, hW₁.2]
  all_goals simp [hi, hj]

private theorem compactStepMatrix_full {m : ℕ} (W : Fin (m + 1) → Fin (m + 1) → ℕ)
    (u v : Fin (m + 1)) (i j : Fin m) :
    compactStepMatrix (mergePair W u v) v m i j = contractMatrix W u v i j := by
  simp [compactStepMatrix, contractMatrix, Nat.not_le_of_lt i.isLt, Nat.not_le_of_lt j.isLt]

private theorem compactStepMatrix_step_eq_of_eq {m : ℕ} (W₁ : Fin (m + 1) → Fin (m + 1) → ℕ)
    (v : Fin (m + 1)) {c : ℕ} (hc : c = v.val) (i j : Fin m) :
    compactStepMatrix W₁ v (c + 1) i j = compactStepMatrix W₁ v c i j := by
  subst hc
  have aux {a b : Fin m} :
      (a.val = v.val ∧ b.val ≠ v.val ∧ v.val + 1 ≤ b.val) ↔
        (a.val = v.val ∧ b.val ≠ v.val ∧ v.val ≤ b.val) := by omega
  simp only [compactStepMatrix, aux]

private theorem compactStepMatrix_succ {m : ℕ} {W₁ : Fin (m + 1) → Fin (m + 1) → ℕ}
    (hW₁ : IsMultigraph W₁) {v : Fin (m + 1)} (hv : v.val < m) {c : Fin m}
    (hcv : c.val ≠ v.val) (i j : Fin m) :
    (if i = c ∧ j = ⟨v.val, hv⟩ then W₁ (Fin.last m) c.castSucc
      else if i = ⟨v.val, hv⟩ ∧ j = c then W₁ (Fin.last m) c.castSucc
      else compactStepMatrix W₁ v c.val i j) =
      compactStepMatrix W₁ v (c.val + 1) i j := by
  have hstep {a b : Fin m} (hab : ¬ (a = ⟨v.val, hv⟩ ∧ b = c)) :
      (a.val = v.val ∧ b.val ≠ v.val ∧ c.val ≤ b.val) ↔
        (a.val = v.val ∧ b.val ≠ v.val ∧ c.val + 1 ≤ b.val) :=
    ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by
      have := Fin.val_ne_of_ne (fun h : b = c => hab ⟨Fin.ext h1, h⟩); omega⟩,
      fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩⟩
  have hnc : ¬ (c.val + 1 ≤ c.val) := by omega
  split_ifs with h_cv h_vc
  · rw [h_cv.1, h_cv.2]
    simp [compactStepMatrix, embedCompact, hcv, hnc, hW₁.1 c.castSucc (Fin.last m)]
  · rw [h_vc.1, h_vc.2]
    simp [compactStepMatrix, embedCompact, hcv, hnc]
  · simp only [compactStepMatrix, hstep h_vc, hstep (fun ⟨hj, hi⟩ => h_cv ⟨hi, hj⟩)]

/-! #### Deterministic execution of `uScan`, `vScan`, and `postRandStep` -/

/-- Shared execution contract for the prefix-sum threshold scan loop used by both `uScan` and
`vScan`: starting at index `y.regs idxReg` with remainder `R + 1 - prefixSum f (y.regs idxReg)` and
loaded entry `f ⟨y.regs idxReg, _⟩` in `val1`, the loop advances `d` steps to `tgt`, leaving memory
and all registers outside `{rem, idxReg, ptrReg, val1}` unchanged. -/
private theorem scanThresholdLoop_exec {w k R : ℕ} (base : ℕ)
    {idxReg ptrReg baseReg : Fin 16}
    (h_ne : idxReg ≠ rem ∧ idxReg ≠ val1 ∧ idxReg ≠ one ∧ idxReg ≠ ptrReg ∧
      ptrReg ≠ rem ∧ ptrReg ≠ val1 ∧ ptrReg ≠ one ∧
      baseReg ≠ rem ∧ baseReg ≠ val1 ∧ baseReg ≠ idxReg ∧ baseReg ≠ ptrReg)
    {f : Fin k → ℕ} {tgt : Fin k}
    (hlo : prefixSum f tgt.val ≤ R) (hhi : R < prefixSum f tgt.val + f tgt)
    (hfit_R1 : Fits w (R + 1)) (hfit_idx : Fits w tgt.val) (hfit_ptr : Fits w (base + tgt.val)) :
    ∀ (d : ℕ) (y : Data 16),
      y.regs one = 1 →
      y.regs baseReg = base →
      y.regs idxReg + d = tgt.val →
      y.regs rem = R + 1 - prefixSum f (y.regs idxReg) →
      y.regs ptrReg = base + y.regs idxReg →
      (∀ hi : y.regs idxReg < k, y.regs val1 = f ⟨y.regs idxReg, hi⟩) →
      (∀ a : Fin k, y.mem (base + a.val) = f a) →
      ∃ z, ExecWithin w
          (.loop (.lt val1 rem) ram[
            rem ← rem - val1; idxReg ← idxReg + one;
            ptrReg ← baseReg + idxReg; val1 ← *ptrReg ])
          y z (6 * d + 2) ∧
        z.mem = y.mem ∧
        z.regs idxReg = tgt.val ∧
        z.regs ptrReg = base + tgt.val ∧
        z.regs val1 = f tgt ∧
        z.regs rem = R + 1 - prefixSum f tgt.val ∧
        ∀ r : Fin 16, r ≠ rem → r ≠ idxReg → r ≠ ptrReg → r ≠ val1 → z.regs r = y.regs r
  | 0, y, _, _, hd, hrem, hptr, hval1, _ => by
    have hidx_eq : y.regs idxReg = tgt.val := by omega
    have hval1_tgt : y.regs val1 = f tgt := by
      simpa [Fin.ext_iff, hidx_eq] using hval1 (hidx_eq ▸ tgt.isLt)
    have hc : ¬ (Cond.lt val1 rem).Holds y := by
      simp only [Cond.holds_lt, hval1_tgt, hrem, hidx_eq]; omega
    exact ⟨y, (ExecWithin.loop_exit hc).mono (by omega), rfl, hidx_eq, hidx_eq ▸ hptr,
      hval1_tgt, hidx_eq ▸ hrem, fun _ _ _ _ _ => rfl⟩
  | d + 1, y, hone, hbase, hd, hrem, hptr, hval1, hmem => by
    obtain ⟨i, hi_eq⟩ : ∃ i, y.regs idxReg = i := ⟨_, rfl⟩
    rw [hi_eq] at hd hrem hptr
    have hi_lt_tgt : i < tgt.val := by omega
    have hi_lt_k : i < k := lt_trans hi_lt_tgt tgt.isLt
    have hi1_lt_k : i + 1 < k := lt_of_le_of_lt hi_lt_tgt tgt.isLt
    have hval1_i : y.regs val1 = f ⟨i, hi_lt_k⟩ := by
      simpa [Fin.ext_iff, hi_eq] using hval1 (hi_eq ▸ hi_lt_k)
    have hpref_succ := prefixSum_succ hi_lt_k f
    have hpref_le : prefixSum f (i + 1) ≤ prefixSum f tgt.val := prefixSum_mono f hi_lt_tgt
    have hc : (Cond.lt val1 rem).Holds y := by simp only [Cond.holds_lt, hval1_i, hrem]; omega
    have ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h_ne
    have hsub_fit : Fits w ((R + 1 - prefixSum f i) - f ⟨i, hi_lt_k⟩) := hfit_R1.of_le (by omega)
    have hidx1_fit : Fits w (i + 1) := hfit_idx.of_le (by omega)
    have hptr1_fit : Fits w (base + (i + 1)) := hfit_ptr.of_le (by omega)
    refine WP.exists_execWithin (WP.loop_iter hc ?_)
    wram_exec [hone, hbase, hi_eq, hrem, hval1_i, hmem ⟨i + 1, hi1_lt_k⟩,
      hsub_fit, hidx1_fit, hptr1_fit]
    wram_call (scanThresholdLoop_exec base h_ne hlo hhi hfit_R1 hfit_idx hfit_ptr d _
      (by wram_simp [hone]) (by wram_simp [hbase]) (by wram_simp; omega) (by wram_simp; omega)
      (by wram_simp) (fun _ => by wram_simp) (fun a => by wram_simp [hmem a]))
      with z ⟨hzm, hz_idx, hz_ptr, hz_val1, hz_rem, hz_other⟩
    exact ⟨by omega, hzm, hz_idx, hz_ptr, hz_val1, hz_rem,
      fun r hr1 hr2 hr3 hr4 => (hz_other r hr1 hr2 hr3 hr4).trans (by wram_simp)⟩

/-- Deterministic execution of `uScan` locating row `u` for a sampled offset `r_val`. -/
theorem uScan_exec {w wb db str k r_val : ℕ} {W : Fin k → Fin k → ℕ}
    {u v : Fin k} {x : Data 16}
    (hsamp : IsSampledPair W r_val u v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = k)
    (htotS : x.regs totS = totalDoubledWeight W) (hrem : x.regs rem = r_val)
    (hdEnd : Fits w (db + k)) (htot : Fits w (totalDoubledWeight W))
    (hdeg : ∀ i : Fin k, x.mem (db + i.val) = rowDeg W i) :
    ∃ y, ExecWithin w uScan x y (6 * k) ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = k ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight W ∧
      y.regs uReg = u.val ∧
      y.regs rem = r_val + 1 - degBefore W u := by
  have hk_pos : 0 < k := Nat.zero_lt_of_lt u.isLt
  rcases hsamp with ⟨hoff_le, hoff_lt⟩
  unfold edgeOffset at hoff_le hoff_lt
  have hwb_le := weightBefore_add_le_rowDeg W u v
  have hdb_le := degBefore_add_le_totalDoubledWeight W u
  have hr1_fit : Fits w (r_val + 1) := htot.of_le (by omega)
  have hdb0_fit : Fits w db := hdEnd.of_le (by omega)
  have hmem0 : x.mem db = rowDeg W ⟨0, hk_pos⟩ := by simpa using hdeg ⟨0, hk_pos⟩
  have hlo : prefixSum (rowDeg W) u.val ≤ r_val := by rw [← degBefore_eq_prefixSum]; omega
  have hhi : r_val < prefixSum (rowDeg W) u.val + rowDeg W u := by
    rw [← degBefore_eq_prefixSum]; omega
  unfold uScan
  wram_exec [hrem, h1, hdBase, hmem0, hr1_fit, hdb0_fit]
  wram_call (scanThresholdLoop_exec db (tgt := u) (by decide) hlo hhi hr1_fit
    (hdEnd.of_le (by have := u.isLt; omega)) (hdEnd.of_le (by have := u.isLt; omega))
    u.val _ (by wram_simp [h1]) (by wram_simp [hdBase]) (by wram_simp)
    (by wram_simp [prefixSum_zero]) (by wram_simp) (fun _ => by wram_simp)
    (fun a => by wram_simp [hdeg a]))
    with y ⟨hym, hy_u, _, _, hy_rem, hy_other⟩
  have hu_lt : u.val < k := u.isLt
  exact ⟨by omega, hym,
    by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, hy_u, degBefore_eq_prefixSum W u ▸ hy_rem⟩

/-- Deterministic execution of `vScan` locating column `v` along row `u`. -/
theorem vScan_exec {w wb db str k r_val : ℕ} {W : Fin k → Fin k → ℕ}
    {u v : Fin k} {x : Data 16}
    (hsamp : IsSampledPair W r_val u v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = k)
    (htotS : x.regs totS = totalDoubledWeight W)
    (huReg : x.regs uReg = u.val) (hrem : x.regs rem = r_val + 1 - degBefore W u)
    (hstr : k ≤ str) (hwEnd : Fits w (wb + str * k)) (hdEnd : Fits w (db + k))
    (htot : Fits w (totalDoubledWeight W))
    (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y, ExecWithin w vScan x y (6 * k + 1) ∧
      y.mem = x.mem ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = k ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight W ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val ∧
      y.regs addr2 = wb + u.val * str + v.val ∧
      y.regs val1 = W u v := by
  have hk_pos : 0 < k := Nat.zero_lt_of_lt v.isLt
  rcases hsamp with ⟨hoff_le, hoff_lt⟩
  unfold edgeOffset at hoff_le hoff_lt
  let rem_u := r_val - degBefore W u
  have hrem_eq : r_val + 1 - degBefore W u = rem_u + 1 := by omega
  have hrem1_fit : Fits w (rem_u + 1) := by
    have := weightBefore_add_le_rowDeg W u v; have := degBefore_add_le_totalDoubledWeight W u
    exact htot.of_le (by omega)
  obtain ⟨hmul_fit, hrow_fit⟩ := rowBase_fits hwEnd (Nat.le_of_lt u.isLt)
  have hm0 : x.mem (wb + u.val * str) = W u ⟨0, hk_pos⟩ := by simpa using hmat u ⟨0, hk_pos⟩
  have hlo : prefixSum (W u) v.val ≤ rem_u := by rw [← weightBefore_eq_prefixSum]; omega
  have hhi : rem_u < prefixSum (W u) v.val + W u v := by rw [← weightBefore_eq_prefixSum]; omega
  unfold vScan
  wram_exec [huReg, hstride, hwBase, hm0, hmul_fit, hrow_fit]
  wram_call (scanThresholdLoop_exec (wb + u.val * str) (tgt := v) (by decide) hlo hhi
    hrem1_fit (hdEnd.of_le (by have := v.isLt; omega))
    (hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr u v)))
    v.val _ (by wram_simp [h1]) (by wram_simp) (by wram_simp)
    (by wram_simp [hrem, hrem_eq, prefixSum_zero]) (by wram_simp) (fun _ => by wram_simp)
    (fun b => by wram_simp [hmat u b]))
    with y ⟨hym, hy_v, hy_a2, hy_v1, _, hy_other⟩
  have hv_lt : v.val < k := v.isLt
  exact ⟨by omega, hym,
    by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame, by regs_frame,
    by regs_frame, by regs_frame, by regs_frame, hy_v, hy_a2, hy_v1⟩

/-! #### Execution of `phaseADegrees`, `phaseAPtrs`, and `mergeLoop` -/

/-- Deterministic execution of `phaseADegrees` updating `totS`, `W[u, v]`, `D[u]`, and `D[v]`. -/
theorem phaseADegrees_exec {w wb db str m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (huv : u ≠ v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m + 1)
    (htotS : x.regs totS = totalDoubledWeight W)
    (huReg : x.regs uReg = u.val) (hvReg : x.regs vReg = v.val)
    (ha2 : x.regs addr2 = wb + u.val * str + v.val) (hv1 : x.regs val1 = W u v)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hdEnd : Fits w (db + (m + 1))) (htot : Fits w (totalDoubledWeight W))
    (hws : HoldsWorkspace x.mem wb db str W) :
    ∃ y, ExecWithin w phaseADegrees x y 12 ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      (∀ i : Fin (m + 1), y.mem (db + i.val) = rowDeg (mergePair W u v) i) ∧
      (∀ i j : Fin (m + 1),
        y.mem (wb + i.val * str + j.val) = if i = u ∧ j = v then 0 else W i j) ∧
      y.regs zero = 0 ∧ y.regs one = 1 ∧
      y.regs wBase = wb ∧ y.regs dBase = db ∧ y.regs stride = str ∧
      y.regs activeK = m + 1 ∧ y.regs targetT = x.regs targetT ∧
      y.regs totS = totalDoubledWeight (contractMatrix W u v) ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val := by
  have htot_contract := totalDoubledWeight_contractMatrix hW huv
  have hS2_eq : (totalDoubledWeight W - W u v) - W u v =
      totalDoubledWeight (contractMatrix W u v) := by omega
  have hS2_fit : Fits w (totalDoubledWeight (contractMatrix W u v)) := htot.of_le (by omega)
  have hdu_new_eq : (rowDeg W u - W u v) + (rowDeg W v - W u v) = rowDeg (mergePair W u v) u := by
    rw [rowDeg_mergePair_u hW huv, hW.1 v u]
  have hdu_addr_fit : Fits w (db + u.val) := hdEnd.of_le (by have := u.isLt; omega)
  have hdv_addr_fit : Fits w (db + v.val) := hdEnd.of_le (by have := v.isLt; omega)
  have hS1_fit : Fits w (totalDoubledWeight W - W u v) := htot.of_le (by omega)
  have hdu_sub_fit : Fits w (rowDeg W u - W u v) :=
    htot.of_le ((Nat.sub_le _ _).trans (rowDeg_le_totalDoubledWeight W u))
  have hdv_sub_fit : Fits w (rowDeg W v - W u v) :=
    htot.of_le ((Nat.sub_le _ _).trans (rowDeg_le_totalDoubledWeight W v))
  have hdu_new_fit : Fits w (rowDeg (mergePair W u v) u) :=
    hS2_fit.of_le (rowDeg_mergePair_u_le_contract huv)
  have hdu_ne : db + u.val ≠ wb + u.val * str + v.val :=
    (matAddr_ne_degAddr hstr hdisj u v u).symm
  have hdv_ne : db + v.val ≠ wb + u.val * str + v.val :=
    (matAddr_ne_degAddr hstr hdisj u v v).symm
  have hdu_mem : x.mem (db + u.val) = rowDeg W u := hws.2 u
  have hdv_mem : x.mem (db + v.val) = rowDeg W v := hws.2 v
  unfold phaseADegrees
  wram_exec [h0, htotS, hv1, ha2, hdBase, huReg, hvReg, hdu_ne, hdv_ne, hdu_mem, hdv_mem,
    hS1_fit, hS2_eq, hS2_fit, hdu_addr_fit, hdv_addr_fit, hdu_sub_fit, hdv_sub_fit,
    hdu_new_eq, hdu_new_fit]
  refine ⟨?_, ?_, ?_,
    by wram_simp [h0], by wram_simp [h1], by wram_simp [hwBase], by wram_simp [hdBase],
    by wram_simp [hstride], by wram_simp [hactiveK], by wram_simp, by wram_simp,
    by wram_simp [huReg], by wram_simp [hvReg]⟩
  · simp only [Data.set_mem, Data.write_mem]
    exact modifies_step_update (modifies_step_update
      (modifies_update_of_mem (Finset.mem_union_left _ (matAddr_mem_Ico hstr u v)) x.mem 0)
      (Finset.mem_union_right _ (degAddr_mem_Ico u)) _)
      (Finset.mem_union_right _ (degAddr_mem_Ico v)) 0
  · intro i
    simp only [Data.set_mem, Data.write_mem]
    obtain rfl | hiv := eq_or_ne i v
    · simp [rowDeg_mergePair_v]
    · rw [Function.update_of_ne (fun h => hiv (Fin.ext (by omega)))]
      obtain rfl | hiu := eq_or_ne i u
      · simp
      · rw [Function.update_of_ne (fun h => hiu (Fin.ext (by omega))),
          update_degAddr_of_matAddr hstr hdisj, hws.2 i, rowDeg_mergePair_other hW huv hiu hiv]
  · intro i j
    simp only [Data.set_mem, Data.write_mem,
      update_matAddr_of_degAddr hstr hdisj, update_matAddr_eq hstr, hws.1 i j]

/-- Deterministic execution of `phaseAPtrs`: compute row pointers for `u` and `v`, zero `W[v, u]`,
and initialize `idx = 0`. -/
private theorem phaseAPtrs_exec {w wb db str m t : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (hf : KargerFrame wb db str (m + 1) t x)
    (huReg : x.regs uReg = u.val) (hvReg : x.regs vReg = v.val)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1)))
    (hdeg : ∀ i : Fin (m + 1), x.mem (db + i.val) = rowDeg (mergePair W u v) i)
    (hmat : ∀ i j : Fin (m + 1),
      x.mem (wb + i.val * str + j.val) = if i = u ∧ j = v then 0 else W i j) :
    ∃ y, ExecWithin w phaseAPtrs x y 7 ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      (∀ i : Fin (m + 1), y.mem (db + i.val) = rowDeg (mergePair W u v) i) ∧
      HoldsMatrix y.mem wb str (mergeStepMatrix W u v 0) ∧
      KargerFrame wb db str (m + 1) t y ∧
      y.regs totS = x.regs totS ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val ∧
      y.regs addr1 = wb + u.val * str ∧
      y.regs addr2 = wb + v.val * str ∧
      y.regs idx = 0 := by
  obtain ⟨hmul_u_fit, hrow_u_fit⟩ := rowBase_fits hwEnd (Nat.le_of_lt u.isLt)
  obtain ⟨hmul_v_fit, hrow_v_fit⟩ := rowBase_fits hwEnd (Nat.le_of_lt v.isLt)
  unfold phaseAPtrs
  wram_exec [hf.zero_eq, hf.wBase_eq, hf.stride_eq, huReg, hvReg, hmul_u_fit, hrow_u_fit,
    hmul_v_fit, hrow_v_fit, hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr v u))]
  refine ⟨?_, fun i => ?_, fun i j => ?_, by struct_frame hf, by wram_simp,
    by wram_simp [huReg], by wram_simp [hvReg], by wram_simp, by wram_simp, by wram_simp⟩
  · simp only [Data.set_mem, Data.write_mem]
    exact modifies_update_of_mem (Finset.mem_union_left _ (matAddr_mem_Ico hstr v u)) x.mem 0
  · simpa only [Data.set_mem, Data.write_mem, update_degAddr_of_matAddr hstr hdisj] using hdeg i
  · simp only [Data.set_mem, Data.write_mem, update_matAddr_eq hstr, mergeStepMatrix_zero hW,
      hmat i j]
    by_cases h1 : i = v ∧ j = u <;> by_cases h2 : i = u ∧ j = v <;> simp [h1, h2]

/-- Deterministic execution of `mergeLoop` sweeping `idx` from `0` to `m + 1` to form
`mergePair W u v` in place. -/
private theorem mergeLoop_exec {w wb db str m t : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (huv : u ≠ v)
    (hf : KargerFrame wb db str (m + 1) t x)
    (huReg : x.regs uReg = u.val) (hvReg : x.regs vReg = v.val)
    (ha1 : x.regs addr1 = wb + u.val * str) (ha2 : x.regs addr2 = wb + v.val * str)
    (hidx0 : x.regs idx = 0)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (htot : Fits w (totalDoubledWeight W))
    (hdeg : ∀ i : Fin (m + 1), x.mem (db + i.val) = rowDeg (mergePair W u v) i)
    (hmat0 : HoldsMatrix x.mem wb str (mergeStepMatrix W u v 0)) :
    ∃ y, ExecWithin w ram[while idx < activeK do [ ⟪mergeBody⟫ ]] x y (20 * (m + 1) + 2) ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      HoldsWorkspace y.mem wb db str (mergePair W u v) ∧
      KargerFrame wb db str (m + 1) t y ∧
      y.regs totS = x.regs totS ∧
      y.regs uReg = u.val ∧ y.regs vReg = v.val := by
  let Inv (y : Data 16) : Prop :=
    KargerFrame wb db str (m + 1) t y ∧ y.regs totS = x.regs totS ∧
    y.regs uReg = u.val ∧ y.regs vReg = v.val ∧
    y.regs addr1 = wb + u.val * str ∧ y.regs addr2 = wb + v.val * str ∧
    y.regs idx ≤ m + 1 ∧
    Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
    (∀ i : Fin (m + 1), y.mem (db + i.val) = rowDeg (mergePair W u v) i) ∧
    HoldsMatrix y.mem wb str (mergeStepMatrix W u v (y.regs idx))
  have hbody : ∀ y, Inv y → (Cond.lt idx activeK).Holds y →
      ∃ z, ExecWithin w mergeBody y z 18 ∧ Inv z ∧
        (m + 1) - z.regs idx < (m + 1) - y.regs idx := by
    rintro y ⟨hyf, hytot, hyu, hyv, hya1, hya2, hyidx_le, hymod, hydeg, hymat⟩ hc
    obtain ⟨c_val, hidx_eq⟩ : ∃ c_val, y.regs idx = c_val := ⟨_, rfl⟩
    have hc_lt : c_val < m + 1 := by simpa [Cond.holds_lt, hidx_eq, hyf.activeK_eq] using hc
    let c : Fin (m + 1) := ⟨c_val, hc_lt⟩
    have hc1_fit : Fits w (c_val + 1) := hdEnd.of_le (by omega)
    have hskip (hmem : c_val = u.val ∨ c_val = v.val) :
        Inv (y.set idx (c_val + 1)) ∧
          (m + 1) - (y.set idx (c_val + 1)).regs idx < (m + 1) - y.regs idx :=
      ⟨⟨by struct_frame hyf, by wram_simp [hytot], by wram_simp [hyu], by wram_simp [hyv],
        by wram_simp [hya1], by wram_simp [hya2], by wram_simp; omega, hymod, hydeg,
        fun i j => by
          wram_simp; rw [mergeStepMatrix_step_eq_of_mem W u v hmem, ← hidx_eq]; exact hymat i j⟩,
        by wram_simp [hidx_eq]; omega⟩
    unfold mergeBody
    by_cases hcu : c_val = u.val
    · wram_exec [hyf.one_eq, hyu, hidx_eq, hcu, hc1_fit]; rw [← hcu]; exact hskip (Or.inl hcu)
    · by_cases hcv : c_val = v.val
      · wram_exec [hyf.one_eq, hyu, hyv, hidx_eq, hcu, hcv, hc1_fit]
        rw [← hcv]; exact hskip (Or.inr hcv)
      · have hc_ne_u : c ≠ u := fun h => hcu (congrArg Fin.val h)
        have hc_ne_v : c ≠ v := fun h => hcv (congrArg Fin.val h)
        obtain ⟨hcmul_fit, hcrow_fit⟩ := rowBase_fits hwEnd (Nat.le_of_lt c.isLt)
        have hvc_fit : Fits w (wb + v.val * str + c_val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr v c))
        have huc_fit : Fits w (wb + u.val * str + c_val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr u c))
        have hcv_fit : Fits w (wb + c_val * str + v.val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr c v))
        have hcu_fit : Fits w (wb + c_val * str + u.val) :=
          hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr c u))
        have hsum_fit : Fits w (W u c + W v c) := by
          have hmp : mergePair W u v u c = W u c + W v c := by
            simp [mergePair, hc_ne_u.symm, huv, hc_ne_v]
          have := entry_le_rowDeg (mergePair W u v) u c
          have := rowDeg_mergePair_u_le_contract (W := W) huv
          have := totalDoubledWeight_contractMatrix hW huv
          exact htot.of_le (by omega)
        have hread_vc : y.mem (wb + v.val * str + c_val) = W v c := by
          simpa [mergeStepMatrix, c, hidx_eq, hc_ne_u, hc_ne_v] using hymat v c
        have hread_uc : y.mem (wb + u.val * str + c_val) = W u c := by
          simpa [mergeStepMatrix, c, hidx_eq, hc_ne_u, hc_ne_v] using hymat u c
        have hne_uc_vc : wb + u.val * str + c_val ≠ wb + v.val * str + c_val :=
          fun h => huv (matAddr_inj hstr (i₁ := u) (j₁ := c) (i₂ := v) (j₂ := c) h).1
        unfold mergeUpdate
        wram_exec [hyf.zero_eq, hyf.one_eq, hyf.wBase_eq, hyf.stride_eq,
          hyu, hyv, hya1, hya2, hidx_eq, hcu, hcv, hne_uc_vc, hread_vc, hread_uc,
          hvc_fit, huc_fit, hsum_fit, hcmul_fit, hcrow_fit, hcv_fit, hcu_fit, hc1_fit]
        refine ⟨⟨by struct_frame hyf, by wram_simp [hytot], by wram_simp [hyu],
          by wram_simp [hyv], by wram_simp [hya1], by wram_simp [hya2], by wram_simp; omega,
          ?_, fun i => ?_, fun i j => ?_⟩, by wram_simp [hidx_eq]; omega⟩
        · simp only [Data.set_mem, Data.write_mem]
          exact modifies_step_update (modifies_step_update (modifies_step_update
            (modifies_step_update hymod (Finset.mem_union_left _ (matAddr_mem_Ico hstr v c)) 0)
            (Finset.mem_union_left _ (matAddr_mem_Ico hstr u c)) _)
            (Finset.mem_union_left _ (matAddr_mem_Ico hstr c v)) 0)
            (Finset.mem_union_left _ (matAddr_mem_Ico hstr c u)) _
        · simpa only [Data.set_mem, Data.write_mem, show c_val = c.val from rfl,
            update_degAddr_of_matAddr hstr hdisj] using hydeg i
        · wram_simp
          simp only [Data.set_mem, Data.write_mem, show c_val = c.val from rfl,
            update_matAddr_eq hstr, hymat i j, hidx_eq]
          exact mergeStepMatrix_succ hW huv hc_ne_u hc_ne_v i j
  obtain ⟨y_end, hloop, ⟨hyf, hytot, hyu, hyv, _, _, _, hymod, hydeg, hymat⟩, hnc⟩ :=
    ExecWithin.loop_invariant Inv (fun y => (m + 1) - y.regs idx) hbody
      ⟨hf, rfl, huReg, hvReg, ha1, ha2, by omega, Modifies.refl _ _, hdeg, hidx0 ▸ hmat0⟩
  have hidx_end : y_end.regs idx = m + 1 := by
    simp only [Cond.holds_lt, hyf.activeK_eq] at hnc; omega
  exact ⟨y_end, hloop.mono (by rw [hidx0]; omega), hymod,
    ⟨fun i j => by simpa [hidx_end, mergeStepMatrix_full] using hymat i j, hydeg⟩,
    hyf, hytot, hyu, hyv⟩

/-! #### Execution of Phase B (`compactSetup` + `compactLoop`) and `postRandStep` -/

/-- Deterministic execution of the Phase B `compactBody` loop compacting row/column `Fin.last m`
into slot `v` (`v.val < m`). -/
private theorem compactLoop_exec {w wb db str m t : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (hv_lt : v.val < m) (hf : KargerFrame wb db str m t x)
    (hvReg : x.regs vReg = v.val) (ha1 : x.regs addr1 = wb + m * str)
    (ha2 : x.regs addr2 = wb + v.val * str) (hidx0 : x.regs idx = 0)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (hdeg : ∀ i : Fin m, x.mem (db + i.val) = rowDeg (contractMatrix W u v) i)
    (hrowm : ∀ c : Fin m, x.mem (wb + m * str + c.val) = mergePair W u v (Fin.last m) c.castSucc)
    (hmat0 : HoldsMatrix x.mem wb str (compactStepMatrix (mergePair W u v) v 0)) :
    ∃ y, ExecWithin w ram[while idx < activeK do [ ⟪compactBody⟫ ]] x y (13 * m + 2) ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      HoldsWorkspace y.mem wb db str (contractMatrix W u v) ∧
      KargerFrame wb db str m t y ∧ y.regs totS = x.regs totS := by
  let W₁ := mergePair W u v
  have hW₁ : IsMultigraph W₁ := isMultigraph_mergePair hW u v
  let Inv (y : Data 16) : Prop :=
    KargerFrame wb db str m t y ∧ y.regs totS = x.regs totS ∧ y.regs vReg = v.val ∧
    y.regs addr1 = wb + m * str ∧ y.regs addr2 = wb + v.val * str ∧ y.regs idx ≤ m ∧
    Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
    (∀ i : Fin m, y.mem (db + i.val) = rowDeg (contractMatrix W u v) i) ∧
    (∀ c : Fin m, y.mem (wb + m * str + c.val) = W₁ (Fin.last m) c.castSucc) ∧
    HoldsMatrix y.mem wb str (compactStepMatrix W₁ v (y.regs idx))
  have hbody : ∀ y, Inv y → (Cond.lt idx activeK).Holds y →
      ∃ z, ExecWithin w compactBody y z 11 ∧ Inv z ∧ m - z.regs idx < m - y.regs idx := by
    rintro y ⟨hyf, hytot, hyv, hya1, hya2, hyidx_le, hymod, hydeg, hyrowm, hymat⟩ hc
    obtain ⟨c_val, hidx_eq⟩ : ∃ c_val, y.regs idx = c_val := ⟨_, rfl⟩
    have hc_lt : c_val < m := by simpa [Cond.holds_lt, hidx_eq, hyf.activeK_eq] using hc
    let c : Fin m := ⟨c_val, hc_lt⟩
    have hc1_fit : Fits w (c_val + 1) := hdEnd.of_le (by omega)
    unfold compactBody
    by_cases hcv : c_val = v.val
    · wram_exec [hyf.one_eq, hyv, hidx_eq, hcv, hc1_fit]
      exact ⟨⟨by struct_frame hyf, by wram_simp [hytot], by wram_simp [hyv],
        by wram_simp [hya1], by wram_simp [hya2], by wram_simp; omega, hymod, hydeg, hyrowm,
        fun i j => by
          wram_simp; rw [← hcv, compactStepMatrix_step_eq_of_eq W₁ v hcv, ← hidx_eq]
          exact hymat i j⟩, by wram_simp [hidx_eq]; omega⟩
    · obtain ⟨hcmul_fit, hcrow_fit⟩ := rowBase_fits hwEnd (Nat.le_of_lt c.castSucc.isLt)
      have hmc_fit : Fits w (wb + m * str + c_val) :=
        hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr (Fin.last m) c.castSucc))
      have hvc_fit : Fits w (wb + v.val * str + c_val) :=
        hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr v c.castSucc))
      have hcv_fit : Fits w (wb + c_val * str + v.val) :=
        hwEnd.of_le (Nat.le_of_lt (matAddr_lt_end hstr c.castSucc v))
      have hread_mc : y.mem (wb + m * str + c_val) = W₁ (Fin.last m) c.castSucc := hyrowm c
      unfold compactUpdate
      wram_exec [hyf.one_eq, hyf.wBase_eq, hyf.stride_eq, hyv, hya1, hya2, hidx_eq, hcv,
        hread_mc, hmc_fit, hvc_fit, hcmul_fit, hcrow_fit, hcv_fit, hc1_fit]
      refine ⟨⟨by struct_frame hyf, by wram_simp [hytot], by wram_simp [hyv],
        by wram_simp [hya1], by wram_simp [hya2], by wram_simp; omega,
        ?_, fun i => ?_, fun c' => ?_, fun i j => ?_⟩, by wram_simp [hidx_eq]; omega⟩
      · simp only [Data.set_mem, Data.write_mem]
        exact modifies_step_update (modifies_step_update hymod
          (Finset.mem_union_left _ (matAddr_mem_Ico hstr v c.castSucc)) _)
          (Finset.mem_union_left _ (matAddr_mem_Ico hstr c.castSucc v)) _
      · simpa only [Data.set_mem, Data.write_mem,
          show c_val = c.castSucc.val from rfl, show i.val = i.castSucc.val from rfl,
          update_degAddr_of_matAddr hstr hdisj] using hydeg i
      · have hne (a b : Fin (m + 1)) (ha : a.val < m) :
            wb + m * str + c'.val ≠ wb + a.val * str + b.val := fun h =>
          absurd (congrArg Fin.val (matAddr_inj hstr (i₁ := Fin.last m) (j₁ := c'.castSucc) h).1)
            (by simp; omega)
        simp only [Data.set_mem, Data.write_mem]
        rw [show c_val = c.castSucc.val from rfl,
          Function.update_of_ne (hne c.castSucc v hc_lt),
          Function.update_of_ne (hne v c.castSucc hv_lt)]
        exact hyrowm c'
      · wram_simp; simp only [Data.set_mem, Data.write_mem]
        change Function.update (Function.update y.mem
            (wb + (⟨v.val, hv_lt⟩ : Fin m).val * str + c.val) (W₁ (Fin.last m) c.castSucc))
            (wb + c.val * str + (⟨v.val, hv_lt⟩ : Fin m).val) (W₁ (Fin.last m) c.castSucc)
            (wb + i.val * str + j.val) = _
        rw [update_matAddr_eq (by omega : m ≤ str), update_matAddr_eq (by omega : m ≤ str),
          hymat i j, hidx_eq]
        exact compactStepMatrix_succ hW₁ hv_lt (c := c) hcv i j
  obtain ⟨y_end, hloop, ⟨hyf, hytot, _, _, _, _, hymod, hydeg, _, hymat⟩, hnc⟩ :=
    ExecWithin.loop_invariant Inv (fun y => m - y.regs idx) hbody
      ⟨hf, rfl, hvReg, ha1, ha2, by omega, Modifies.refl _ _, hdeg, hrowm, hidx0 ▸ hmat0⟩
  have hidx_end : y_end.regs idx = m := by simp only [Cond.holds_lt, hyf.activeK_eq] at hnc; omega
  exact ⟨y_end, hloop.mono (by rw [hidx0]; omega), hymod,
    ⟨fun i j => by simpa [hidx_end, W₁, compactStepMatrix_full] using hymat i j, hydeg⟩,
    hyf, hytot⟩

/-- Deterministic execution of Phase B (`compactSetup` followed by `compactLoop`) when `v < m`,
compacting vertex `Fin.last m` into slot `v` to form `contractMatrix W u v`. -/
private theorem compactPhase_exec {w wb db str m t : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hW : IsMultigraph W) (hv_lt : v.val < m)
    (hf : KargerFrame wb db str m t x)
    (hvReg : x.regs vReg = v.val)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (hws1 : HoldsWorkspace x.mem wb db str (mergePair W u v)) :
    ∃ y, ExecWithin w ram[⟪compactSetup⟫; while idx < activeK do [ ⟪compactBody⟫ ]]
        x y (13 * m + 11) ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      HoldsWorkspace y.mem wb db str (contractMatrix W u v) ∧
      KargerFrame wb db str m t y ∧
      y.regs totS = x.regs totS := by
  let W₁ := mergePair W u v
  have hW₁ : IsMultigraph W₁ := isMultigraph_mergePair hW u v
  obtain ⟨hmmul_fit, hmrow_fit⟩ := rowBase_fits hwEnd (Nat.le_succ m)
  obtain ⟨hvmul_fit, hvrow_fit⟩ := rowBase_fits hwEnd (Nat.le_of_lt v.isLt)
  have hdm_fit : Fits w (db + m) := hdEnd.of_le (by omega)
  have hdv_fit : Fits w (db + v.val) := hdEnd.of_le (by omega)
  have hread_dm : x.mem (db + m) = rowDeg W₁ (Fin.last m) := hws1.2 (Fin.last m)
  unfold compactSetup
  wram_exec [hf.wBase_eq, hf.dBase_eq, hf.stride_eq, hf.activeK_eq, hvReg,
    hread_dm, hdm_fit, hdv_fit, hmmul_fit, hmrow_fit, hvmul_fit, hvrow_fit]
  refine WP.name fun x₁ hx₁_eq => ?_
  have hx₁_mem : x₁.mem = Function.update x.mem (db + v.val) (rowDeg W₁ (Fin.last m)) := by
    subst hx₁_eq; simp only [Data.set_mem, Data.write_mem]
  have hdeg : ∀ i : Fin m, x₁.mem (db + i.val) = rowDeg (contractMatrix W u v) i := fun i => by
    rw [hx₁_mem, rowDeg_contractMatrix]; unfold embedCompact
    by_cases hiv : i.val = v.val
    · rw [hiv]; simp [W₁]
    · rw [Function.update_of_ne (by omega : db + i.val ≠ db + v.val)]
      simp only [hiv, ↓reduceIte]; exact hws1.2 i.castSucc
  have hrowm : ∀ c : Fin m, x₁.mem (wb + m * str + c.val) = W₁ (Fin.last m) c.castSucc := fun c =>
    by simpa only [hx₁_mem, Fin.val_last, Fin.val_castSucc] using
      (update_matAddr_of_degAddr hstr hdisj x.mem v (Fin.last m) c.castSucc _).trans
        (hws1.1 (Fin.last m) c.castSucc)
  have hmat0 : HoldsMatrix x₁.mem wb str (compactStepMatrix W₁ v 0) := fun i j => by
    rw [hx₁_mem, compactStepMatrix_zero hW₁]
    exact (update_matAddr_of_degAddr hstr hdisj x.mem v i.castSucc j.castSucc _).trans
      (hws1.1 i.castSucc j.castSucc)
  obtain ⟨y, hloop, hmod, hws, hyf, hytot⟩ :=
    compactLoop_exec (x := x₁) hW hv_lt (by struct_frame hf) (by regs_frame)
      (by subst hx₁_eq; wram_simp) (by subst hx₁_eq; wram_simp) (by subst hx₁_eq; wram_simp)
      hstr hdisj hwEnd hdEnd hdeg hrowm hmat0
  have hx₁_mod : Modifies (workspaceFootprint wb db str (m + 1)) x.mem x₁.mem :=
    hx₁_mem ▸ modifies_update_of_mem (Finset.mem_union_right _ (degAddr_mem_Ico v)) x.mem _
  exact WP.of_execWithin hloop ⟨by omega,
    modifies_trans_subset hx₁_mod hmod Finset.Subset.rfl Finset.Subset.rfl, hws, hyf,
    by regs_frame⟩

/-- Deterministic post-sampling execution: given `x.regs rem = r_val` with
`IsSampledPair W r_val u v`, `postRandStep` contracts `(u, v)` and swap-compacts `Fin.last m` into
slot `v` within `45 * (m + 1) + 22` instructions. -/
theorem postRandStep_exec {w wb db str m t r_val : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {u v : Fin (m + 1)} {x : Data 16}
    (hm : 2 ≤ m) (hW : IsMultigraph W) (hsamp : IsSampledPair W r_val u v)
    (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hwBase : x.regs wBase = wb) (hdBase : x.regs dBase = db)
    (hstride : x.regs stride = str) (hactiveK : x.regs activeK = m + 1)
    (htargetT : x.regs targetT = t) (htotS : x.regs totS = totalDoubledWeight W)
    (hrem : x.regs rem = r_val)
    (hstr : m + 1 ≤ str) (hdisj : wb + str * (m + 1) ≤ db ∨ db + (m + 1) ≤ wb)
    (hwEnd : Fits w (wb + str * (m + 1))) (hdEnd : Fits w (db + (m + 1)))
    (htot : Fits w (totalDoubledWeight W)) (hws : HoldsWorkspace x.mem wb db str W) :
    ∃ y, ExecWithin w postRandStep x y (45 * (m + 1) + 22) ∧
      Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
      ContractState w wb db str m t (contractMatrix W u v) y ∧
      y.regs zero = 0 ∧ y.regs one = 1 := by
  have huv : u ≠ v := isSampledPair_ne hW hsamp
  have hmul_le : str * m ≤ str * (m + 1) := Nat.mul_le_mul_left str (Nat.le_succ m)
  have htot_c_fit : Fits w (totalDoubledWeight (contractMatrix W u v)) :=
    htot.of_le (by have := totalDoubledWeight_contractMatrix hW huv; omega)
  have hdisj_m : wb + str * m ≤ db ∨ db + m ≤ wb := by omega
  have hwEnd_m : Fits w (wb + str * m) := hwEnd.of_le (by omega)
  have hdEnd_m : Fits w (db + m) := hdEnd.of_le (by omega)
  unfold postRandStep
  wram_exec
  wram_call (uScan_exec hsamp h0 h1 hwBase hdBase hstride hactiveK htotS hrem hdEnd htot hws.2)
    with y1 ⟨hm1, h1_0, h1_1, h1_wb, h1_db, h1_str, h1_k, h1_t, h1_tot, h1_u, h1_rem⟩
  wram_call (vScan_exec hsamp h1_0 h1_1 h1_wb h1_db h1_str h1_k h1_tot h1_u h1_rem
    hstr hwEnd hdEnd htot (hm1 ▸ hws.1))
    with y2 ⟨hm2, h2_0, h2_1, h2_wb, h2_db, h2_str, h2_k, h2_t, h2_tot, h2_u, h2_v, h2_a2, h2_v1⟩
  wram_call (phaseADegrees_exec hW huv h2_0 h2_1 h2_wb h2_db h2_str h2_k h2_tot h2_u h2_v
    h2_a2 h2_v1 hstr hdisj hdEnd htot (hm2.trans hm1 ▸ hws))
    with y3 ⟨hmod3, h3_deg, h3_mat, h3_0, h3_1, h3_wb, h3_db, h3_str, h3_k, h3_t, h3_tot,
      h3_u, h3_v⟩
  wram_call (phaseAPtrs_exec hW ⟨h3_0, h3_1, h3_wb, h3_db, h3_str, h3_k, by regs_frame⟩
      h3_u h3_v hstr hdisj hwEnd h3_deg h3_mat)
    with y4 ⟨hmod4, h4_deg, h4_mat0, hf4, h4_tot, h4_u, h4_v, h4_a1, h4_a2, h4_idx⟩
  wram_call (mergeLoop_exec hW huv hf4 h4_u h4_v h4_a1 h4_a2 h4_idx
    hstr hdisj hwEnd hdEnd htot h4_deg h4_mat0)
    with y5 ⟨hmod5, h5_ws, hf5, h5_tot, _, h5_v⟩
  have hmod15 := modifies_trans_subset
    (modifies_trans_subset (show Modifies (workspaceFootprint wb db str (m + 1)) x.mem y3.mem by
      simpa only [hm2, hm1] using hmod3) hmod4 Finset.Subset.rfl Finset.Subset.rfl)
    hmod5 Finset.Subset.rfl Finset.Subset.rfl
  refine WP.seq (WP.bin hf5.activeK_eq hf5.one_eq (Nat.add_sub_cancel m 1) (hdEnd.of_le (by omega))
    (WP.branch (fun hc => ?_) (fun hc => ?_)))
  · have hv_lt : v.val < m := by wram_simp [Cond.holds_lt, h5_v] at hc; exact hc
    wram_call (compactPhase_exec (u := u) (t := t) hW hv_lt (by regs_frame)
      (by regs_frame) hstr hdisj hwEnd hdEnd h5_ws)
      with y7 ⟨hmod7, h7_ws, hf7, h7_tot⟩
    exact ⟨by omega, modifies_trans_subset hmod15 hmod7 Finset.Subset.rfl Finset.Subset.rfl,
      ⟨hf7.wBase_eq, hf7.dBase_eq, hf7.stride_eq, hf7.activeK_eq, hf7.targetT_eq,
        by regs_frame, by omega, hdisj_m, hwEnd_m, hdEnd_m,
        htot_c_fit, h7_ws⟩, hf7.zero_eq, hf7.one_eq⟩
  · have hv_lt : ¬ v.val < m := by wram_simp [Cond.holds_lt, h5_v] at hc; exact hc
    wram_exec
    have hembed (i : Fin m) : embedCompact v i = i.castSucc := by
      simp [embedCompact, show i.val ≠ v.val by have := i.isLt; have := v.isLt; omega]
    exact ⟨hmod15,
      ⟨by regs_frame, by regs_frame, by regs_frame, by wram_simp, by regs_frame,
        by regs_frame, by omega, hdisj_m, hwEnd_m, hdEnd_m, htot_c_fit,
        ⟨fun i j => by simpa [contractMatrix, hembed] using h5_ws.1 i.castSucc j.castSucc,
         fun i => by simpa [rowDeg_contractMatrix, hembed] using h5_ws.2 i.castSucc⟩⟩,
      by regs_frame, by regs_frame⟩

/-! #### Simulation of the contraction structure and `contractDownTo_spec` -/

private theorem step_budget_succ {t m n_post z₂ : ℕ} (ht : 2 ≤ t) (hm : t ≤ m)
    (hn : n_post ≤ 45 * (m + 1) + 22) (hz : z₂ ≤ 36 * (m ^ 2 - t ^ 2) + 2) :
    (1 + (1 + n_post) + 2) + z₂ + 2 ≤ 36 * ((m + 1) ^ 2 - t ^ 2) + 2 := by
  have hsq : (m ^ 2 - t ^ 2) + (2 * m + 1) = (m + 1) ^ 2 - t ^ 2 := by
    zify [Nat.pow_le_pow_left hm 2, Nat.pow_le_pow_left (by omega : t ≤ m + 1) 2]; ring
  have : 36 * (m ^ 2 - t ^ 2) + 36 * (2 * m + 1) = 36 * ((m + 1) ^ 2 - t ^ 2) := by
    rw [← Nat.mul_add, hsq]
  omega

/-- Target survival predicate on final `Data 16`: memory holds a contracted `t`-supervertex
multigraph `W'` along `part'` where some active cut `B'` pulls back to `C_star`. -/
def SurvivalPost {n : ℕ} (W₀ : Fin n → Fin n → ℕ) (wb db str t : ℕ)
    (C_star : Finset (Fin n)) (y : Data 16) : Prop :=
  ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t) (B' : Finset (Fin t)),
    IsContractionOf W₀ part' W' ∧
    HoldsWorkspace y.mem wb db str W' ∧
    y.regs totS = totalDoubledWeight W' ∧
    pullbackCut part' B' = C_star

/-- Zero-weight branch of `contractStep`: drops supervertex `Fin.last m` deterministically with
zero `rand` calls. -/
private theorem contractStep_law_zero {w wb db str t m : ℕ}
    {W : Fin (m + 1) → Fin (m + 1) → ℕ} {x : Data 16} (hW : IsMultigraph W)
    (hS0 : totalDoubledWeight W = 0) (h0 : x.regs zero = 0) (h1 : x.regs one = 1)
    (hst : ContractState w wb db str (m + 1) t W x) :
    ExecRandLaw w contractStep x
      (fun y => Modifies (workspaceFootprint wb db str (m + 1)) x.mem y.mem ∧
        y.regs zero = 0 ∧ y.regs one = 1 ∧ ∃ W' : Fin m → Fin m → ℕ,
          IsMultigraph W' ∧ ContractState w wb db str m t W' y)
      2 0 (heldGraph wb str) (PMF.pure ⟨m, contractMatrix W 0 (Fin.last m)⟩) := by
  have hW_zero (a b : Fin (m + 1)) : W a b = 0 := by
    have := entry_le_totalDoubledWeight W a b; omega
  have hcm_zero (i j : Fin m) : contractMatrix W 0 (Fin.last m) i j = 0 := by
    simp [contractMatrix, mergePair, hW_zero]
  have hdeg_zero (i : Fin m) : rowDeg (contractMatrix W 0 (Fin.last m)) i = 0 := by
    simp [rowDeg, hcm_zero]
  have htot_zero : totalDoubledWeight (contractMatrix W 0 (Fin.last m)) = 0 := by
    simp [totalDoubledWeight, hdeg_zero]
  have hmul : str * m ≤ str * (m + 1) := Nat.mul_le_mul_left str (Nat.le_succ m)
  let x_next := x.set activeK m
  have hop : (Op.bin .sub activeK activeK one).eval w x = some x_next := by
    simp only [Op.eval_bin, BinOp.eval, hst.regs_activeK, h1, Nat.add_sub_cancel]
    exact Data.put_of_fits (hst.fits_dEnd.of_le (by omega))
  have hws_next : HoldsWorkspace x_next.mem wb db str (contractMatrix W 0 (Fin.last m)) :=
    ⟨fun i j => (hst.workspace.1 i.castSucc j.castSucc).trans (by rw [hW_zero, hcm_zero]),
     fun i => (hst.workspace.2 i.castSucc).trans (by simp [rowDeg, hW_zero, hcm_zero])⟩
  have hst_next : ContractState w wb db str m t (contractMatrix W 0 (Fin.last m)) x_next :=
    ⟨by wram_simp [x_next, hst.regs_wBase], by wram_simp [x_next, hst.regs_dBase],
      by wram_simp [x_next, hst.regs_stride], by wram_simp [x_next],
      by wram_simp [x_next, hst.regs_targetT],
      by wram_simp [x_next, hst.regs_totS, hS0, htot_zero],
      by have := hst.le_stride; omega, by have := hst.disjoint_blocks; omega,
      hst.fits_wEnd.of_le (by omega), hst.fits_dEnd.of_le (by omega),
      by rw [htot_zero]; exact fits_zero w, hws_next⟩
  rw [← hst_next.heldGraph_eq]
  exact ExecRandLaw.branch_pos (by simp [hst.regs_totS, hS0, h0])
    (ExecRandLaw.of_execWithin (ExecWithin.op hop)
      ⟨Modifies.refl _ _, by wram_simp [x_next, h0], by wram_simp [x_next, h1],
        _, isMultigraph_contractMatrix hW _ _, hst_next⟩)

/-- **The contraction loop refines the contraction structure.** From a state holding a multigraph
`W` on `t + s` supervertices, the loop runs within `36 ((t + s)² - t²) + 2` instructions and `s`
`rand` calls, writes only the workspace and ends holding a multigraph on `t` supervertices. The
graph it holds has the law of `s` contractions of `⟨t + s, W⟩` in `Lean.Karger.spec`: each
positive-weight step draws the offset uniformly below the total weight, as the client
`Lean.Karger.contractStep` does, and `postRandStep` contracts the pair sampled there. -/
private theorem contractLoop_law {w wb db str t s : ℕ} {W : Fin (t + s) → Fin (t + s) → ℕ}
    {x : Data 16} (ht : 2 ≤ t) (hW : IsMultigraph W) (h0 : x.regs zero = 0)
    (h1 : x.regs one = 1) (hst : ContractState w wb db str (t + s) t W x) :
    ExecRandLaw w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] x
      (fun y => Modifies (workspaceFootprint wb db str (t + s)) x.mem y.mem ∧
        ∃ W' : Fin t → Fin t → ℕ, IsMultigraph W' ∧ ContractState w wb db str t t W' y)
      (36 * ((t + s) ^ 2 - t ^ 2) + 2) s (heldGraph wb str)
      ((Lean.Karger.spec.toRandomized.withCoins.run (Lean.Karger.contractTimes s)
        ⟨t + s, W⟩).map Prod.snd) := by
  induction s generalizing x with
  | zero =>
    have hnc : ¬ (Cond.lt targetT activeK).Holds x := by simp [hst.regs_targetT, hst.regs_activeK]
    refine ((ExecRandLaw.loop_exit hnc ⟨Modifies.refl _ _, W, hW, hst⟩).congr_law ?_).mono
      (fun _ h => h) (Nat.le_add_left _ _) le_rfl
    rw [hst.heldGraph_eq]
    exact (PMF.pure_map Prod.snd ((), (⟨t + 0, W⟩ : Lean.Karger.Graph))).symm
  | succ s ih =>
    let κ (G : Lean.Karger.Graph) : PMF Lean.Karger.Graph :=
      (Lean.Karger.spec.toRandomized.withCoins.run (Lean.Karger.contractTimes s) G).map Prod.snd
    have hc_loop : (Cond.lt targetT activeK).Holds x := by
      simp only [Cond.holds_lt, hst.regs_targetT, hst.regs_activeK]; omega
    let P (y : Data 16) : Prop :=
      Modifies (workspaceFootprint wb db str (t + s + 1)) x.mem y.mem ∧ y.regs zero = 0 ∧
        y.regs one = 1 ∧ ∃ W' : Fin (t + s) → Fin (t + s) → ℕ,
          IsMultigraph W' ∧ ContractState w wb db str (t + s) t W' y
    have hrest : ∀ y, P y → ExecRandLaw w ram[while targetT < activeK do [ ⟪contractStep⟫ ]] y
        (fun z => Modifies (workspaceFootprint wb db str (t + (s + 1))) x.mem z.mem ∧
          ∃ W' : Fin t → Fin t → ℕ, IsMultigraph W' ∧ ContractState w wb db str t t W' z)
        (36 * ((t + s) ^ 2 - t ^ 2) + 2) s (heldGraph wb str) (κ (heldGraph wb str y)) := by
      rintro y ⟨hmod, hy0, hy1, W', hW', hst'⟩
      rw [hst'.heldGraph_eq]
      exact (ih hW' hy0 hy1 hst').mono (fun z ⟨hmz, hz⟩ => ⟨modifies_trans_subset hmod hmz
        Finset.Subset.rfl (workspaceFootprint_mono (Nat.le_succ _)), hz⟩) le_rfl le_rfl
    have hbudget := step_budget_succ (n_post := 45 * (t + s + 1) + 22) ht (Nat.le_add_right t s)
      le_rfl le_rfl
    by_cases hS0 : totalDoubledWeight W = 0
    · refine ((ExecRandLaw.loop_iter hc_loop
        (contractStep_law_zero hW hS0 h0 h1 hst) hrest).congr_law ?_).mono
        (fun _ h => h) (le_trans (by omega) hbudget) (by omega)
      rw [PMF.pure_bind]
      exact (congrArg (PMF.map Prod.snd) (Lean.Karger.run_contractStep_bind_of_eq_zero (m := t + s)
        (Lean.Karger.contractTimes s) W hS0)).symm
    · have hSm1_fit : Fits w (totalDoubledWeight W - 1) := hst.fits_totS.of_le (by omega)
      let x_sub := x.set val1 (totalDoubledWeight W - 1)
      have hop_sub : (Op.bin .sub val1 totS one).eval w x = some x_sub := by
        simp only [Op.eval_bin, BinOp.eval, hst.regs_totS, h1]; exact Data.put_of_fits hSm1_fit
      have hN : x_sub.regs val1 = totalDoubledWeight W - 1 := by wram_simp [x_sub]
      have hpost : ∀ k : Fin (x_sub.regs val1 + 1), ∃ y,
          ExecWithin w postRandStep (x_sub.set rem k.val) y (45 * (t + s + 1) + 22) ∧ P y ∧
            heldGraph wb str y = Lean.Karger.contractGraph ⟨t + s + 1, W⟩
              (Lean.Karger.sampledPair W k).1 (Lean.Karger.sampledPair W k).2 := by
        intro k
        obtain ⟨u, v, hsamp⟩ := exists_isSampledPair W (show k.val < totalDoubledWeight W by
          have := k.isLt; omega)
        obtain ⟨y, hy, hmod, hst', hy0, hy1⟩ :=
          postRandStep_exec (x := x_sub.set rem k.val) (m := t + s) (t := t) (by omega) hW hsamp
            (by wram_simp [x_sub, h0]) (by wram_simp [x_sub, h1])
            (by wram_simp [x_sub, hst.regs_wBase]) (by wram_simp [x_sub, hst.regs_dBase])
            (by wram_simp [x_sub, hst.regs_stride])
            (by wram_simp [x_sub, hst.regs_activeK]; omega)
            (by wram_simp [x_sub, hst.regs_targetT]) (by wram_simp [x_sub, hst.regs_totS])
            (by wram_simp) hst.le_stride hst.disjoint_blocks hst.fits_wEnd hst.fits_dEnd
            hst.fits_totS hst.workspace
        exact ⟨y, hy, ⟨hmod, hy0, hy1, _, isMultigraph_contractMatrix hW u v, hst'⟩, by
          rw [hst'.heldGraph_eq, Lean.Karger.sampledPair_eq hsamp, Lean.Karger.contractGraph_fin]⟩
      choose y hy using hpost
      have hb : ExecRandLaw w contractStep x P (1 + (1 + (45 * (t + s + 1) + 22)) + 2) 1
          (heldGraph wb str) ((Probability.PMF.uniformOfFintype (Fin (x_sub.regs val1 + 1))).map
            fun k => heldGraph wb str (y k)) :=
        ExecRandLaw.branch_neg (by simp [hst.regs_totS, h0, hS0])
          (ExecRandLaw.seq_det (ExecWithin.op hop_sub)
            (ExecRandLaw.rand_seq (hN ▸ hSm1_fit) (fun k => (hy k).1) fun k => (hy k).2.1))
      refine ((ExecRandLaw.loop_iter hc_loop hb hrest).congr_law ?_).mono
        (fun _ h => h) hbudget (by omega)
      rw [PMF.bind_map, Function.comp_def, funext (fun k => congrArg κ (hy k).2.2), hN]
      exact (PMF.map_bind _ _ _).symm.trans (congrArg (PMF.map Prod.snd)
        (Lean.Karger.run_contractStep_bind (m := t + s) (Lean.Karger.contractTimes s) W hS0).symm)

/-- **`contractDownTo` refines the contraction structure.** From a state holding a multigraph `W`
on `k ≥ t ≥ 2` supervertices, `contractDownTo` runs within `36 (k² - t²) + 4` instructions and
`k - t` `rand` calls, writes only the workspace and ends holding a multigraph on `t` supervertices.
The graph it holds (`heldGraph`) has the law of `k - t` contractions of `⟨k, W⟩` by the client
`Lean.Karger.contractTimes` of `Lean.Karger.spec`. -/
theorem contractDownTo_law {w wb db str k t : ℕ} {W : Fin k → Fin k → ℕ} {x : Data 16}
    (ht : 2 ≤ t) (htk : t ≤ k) (hW : IsMultigraph W) (hst : ContractState w wb db str k t W x) :
    ExecRandLaw w contractDownTo x
      (fun y => Modifies (workspaceFootprint wb db str k) x.mem y.mem ∧
        ∃ W' : Fin t → Fin t → ℕ, IsMultigraph W' ∧ ContractState w wb db str t t W' y)
      (36 * (k ^ 2 - t ^ 2) + 4) (k - t) (heldGraph wb str)
      ((Lean.Karger.spec.toRandomized.withCoins.run (Lean.Karger.contractTimes (k - t))
        ⟨k, W⟩).map Prod.snd) := by
  obtain ⟨s, rfl⟩ : ∃ s, k = t + s := ⟨k - t, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1_fit : Fits w 1 := hst.fits_dEnd.of_le (by omega)
  let x₁ := (x.set zero 0).set one 1
  have hst₁ : ContractState w wb db str (t + s) t W x₁ := by struct_frame hst
  have hloop := contractLoop_law ht hW (by wram_simp [x₁]) (by wram_simp [x₁]) hst₁
  unfold contractDownTo
  exact (ExecRandLaw.seq_det (ExecWithin.const (fits_zero w))
    (ExecRandLaw.seq_det (ExecWithin.const h1_fit) hloop)).mono (fun _ h => h) (by omega) le_rfl

/-- **Master specification for `contractDownTo` (`Code .standard 16`).**
Starting from any `ContractState w wb db str k t W x` (`2 ≤ t ≤ k`) where `W` is a contraction of
`W₀` along `part`, `contractDownTo`:
1. terminates fault-free on every path (`ExecRand`),
2. issues at most `k - t` `rand` calls (`IsQueryBounded (k - t)`),
3. executes at most `36 * (k ^ 2 - t ^ 2) + 4` instructions on every path, modifying only
   `workspaceFootprint wb db str k` and leaving a valid `t`-supervertex `ContractState` that is a
   contraction of `W₀`, and
4. preserves any fixed minimum cut `pullbackCut part B` of a connected multigraph (`0 < minCut W₀`)
   with probability at least `(t * (t - 1)) / (k * (k - 1))`.

The first three parts and the law of the held graph are `contractDownTo_law`. The contraction in
part 3 and the bound in part 4 are the specification's
(`Lean.Karger.isContractionOf_of_mem_support_contractTimes`, `Lean.Karger.survives_contractTimes`),
carried through that law. -/
theorem contractDownTo_spec {n w wb db str k t : ℕ} {W₀ : Fin n → Fin n → ℕ}
    {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data 16}
    (ht : 2 ≤ t) (htk : t ≤ k) (hC : IsContractionOf W₀ part W)
    (hst : ContractState w wb db str k t W x) :
    ∃ m : ProbComp (Data 16 × ℕ),
      ExecRand w contractDownTo x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 36 * (k ^ 2 - t ^ 2) + 4 ∧
        Modifies (workspaceFootprint wb db str k) x.mem z.1.mem ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          ContractState w wb db str t t W' z.1) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞)) ≤
          m.eval.toOuterMeasure {z | SurvivalPost W₀ wb db str t (pullbackCut part B) z.1}) := by
  obtain ⟨m, hm, hq, hsup, hlaw⟩ := contractDownTo_law ht htk hC.multigraph hst
  obtain ⟨s, rfl⟩ : ∃ s, k = t + s := ⟨k - t, by omega⟩
  rw [Nat.add_sub_cancel_left, ProbComp.eval_map] at hlaw
  refine ⟨m, hm, hq, fun z hz => ?_, fun B hmin hB hBmin => ?_⟩
  · obtain ⟨⟨hmod, W', -, hst'⟩, hT⟩ := hsup z hz
    have hz' : heldGraph wb str z.1 ∈ ((Lean.Karger.spec.toRandomized.withCoins.run
        (Lean.Karger.contractTimes s) ⟨t + s, W⟩).map Prod.snd).support := by
      rw [← hlaw, PMF.mem_support_map_iff]
      exact ⟨z, by rwa [ProbComp.support_eval], rfl⟩
    obtain ⟨y, hy, hyz⟩ := (PMF.mem_support_map_iff _ _ _).mp hz'
    obtain ⟨W'', part', hy', hC'⟩ :=
      Lean.Karger.isContractionOf_of_mem_support_contractTimes (by omega) s hC hy
    obtain rfl := hst'.eq_of_heldGraph_eq (hyz.symm.trans hy')
    exact ⟨hT, hmod, W', part', hC', hst'⟩
  · calc _ ≤ _ := Lean.Karger.survives_contractTimes ht hmin s hC hB hBmin
      _ = (m.eval.map fun z => heldGraph wb str z.1).toOuterMeasure
          {G | Lean.Karger.Survives W₀ (pullbackCut part B) t G} := by
        rw [hlaw, PMF.toOuterMeasure_map_apply]
        rfl
      _ ≤ _ := by
        rw [PMF.toOuterMeasure_map_apply]
        refine PMF.toOuterMeasure_mono _ fun z ⟨⟨W'', part', B', hG, hC', hpb⟩, hz⟩ => ?_
        rw [ProbComp.support_eval] at hz
        obtain ⟨⟨-, W', -, hst'⟩, -⟩ := hsup z hz
        obtain rfl := hst'.eq_of_heldGraph_eq hG
        exact ⟨W', part', B', hC', hst'.workspace, hst'.regs_totS, hpb⟩

/-- At `t = 2`, any state satisfying `SurvivalPost W₀ wb db str 2 C_star y` where `C_star` is a
non-trivial cut attaining `minCut W₀` stores `minCut W₀` in `y.mem (wb + 1)`. -/
theorem survivalPost_two_mem_eq {n : ℕ} {W₀ : Fin n → Fin n → ℕ} {wb db str : ℕ}
    {C_star : Finset (Fin n)} {y : Data 16}
    (hnt : IsNonTrivialCut C_star) (hmin : cutWeight W₀ C_star = minCut W₀)
    (hsurv : SurvivalPost W₀ wb db str 2 C_star y) :
    y.mem (wb + 1) = minCut W₀ := by
  obtain ⟨W', part', B', hC', hws', -, hpb'⟩ := hsurv
  have hB' : IsNonTrivialCut B' := isNonTrivialCut_of_pullbackCut part' (hpb' ▸ hnt)
  rw [show y.mem (wb + 1) = W' 0 1 by simpa using hws'.1 0 1,
    ← cutWeight_fin_two hC'.multigraph hB', ← cutWeight_pullbackCut hC', hpb', hmin]

/-! ### Register-embedding (`Code.rename`) wrappers for callers with `r ≥ 16` -/

/-- `computeDegreesAndTotal` embedded on registers `0..15` of any `r`-register file (`16 ≤ r`). -/
def computeDegreesAndTotalAt {r : ℕ} (hr : 16 ≤ r) : Code .standard r :=
  computeDegreesAndTotal.rename (Fin.castLE hr)

/-- `contractDownTo` embedded on registers `0..15` of any `r`-register file (`16 ≤ r`). -/
def contractDownToAt {r : ℕ} (hr : 16 ≤ r) : Code .standard r :=
  contractDownTo.rename (Fin.castLE hr)

/-- Specification of `computeDegreesAndTotalAt hr` on any `r`-register file (`16 ≤ r`), preserving
all caller registers with index `≥ 16`. -/
theorem computeDegreesAndTotalAt_exec {r w wb db str k : ℕ} (hr : 16 ≤ r)
    {W : Fin k → Fin k → ℕ} {x : Data r}
    (hwBase : x.regs (Fin.castLE hr wBase) = wb)
    (hdBase : x.regs (Fin.castLE hr dBase) = db)
    (hstride : x.regs (Fin.castLE hr stride) = str)
    (hactiveK : x.regs (Fin.castLE hr activeK) = k)
    (hstr : k ≤ str) (hdisj : wb + str * k ≤ db ∨ db + k ≤ wb)
    (h1 : Fits w 1) (hwEnd : Fits w (wb + str * k)) (hdEnd : Fits w (db + k))
    (htot : Fits w (totalDoubledWeight W)) (hmat : HoldsMatrix x.mem wb str W) :
    ∃ y : Data r, ExecWithin w (computeDegreesAndTotalAt hr) x y (6 * k ^ 2 + 12 * k + 6) ∧
      HoldsWorkspace y.mem wb db str W ∧
      Modifies (Finset.Ico db (db + k)) x.mem y.mem ∧
      y.regs (Fin.castLE hr wBase) = wb ∧
      y.regs (Fin.castLE hr dBase) = db ∧
      y.regs (Fin.castLE hr stride) = str ∧
      y.regs (Fin.castLE hr activeK) = k ∧
      y.regs (Fin.castLE hr targetT) = x.regs (Fin.castLE hr targetT) ∧
      y.regs (Fin.castLE hr totS) = totalDoubledWeight W ∧
      ∀ j : Fin r, 16 ≤ j.val → y.regs j = x.regs j := by
  obtain ⟨y, hy, ⟨hws, hmod, _, _, hwb, hdb, hstr, hk, ht, htot⟩, hframe⟩ :=
    ExecWithin.rename_post (Fin.castLE_injective hr)
      (computeDegreesAndTotal_exec (x := x.comap (Fin.castLE hr))
        hwBase hdBase hstride hactiveK hstr hdisj h1 hwEnd hdEnd htot hmat)
  refine ⟨y, hy, hws, hmod, hwb, hdb, hstr, hk, ht, htot, fun j hj => hframe j fun i hi => ?_⟩
  have := congrArg Fin.val hi; change i.val = j.val at this; omega

/-- `contractDownToAt hr` simulates `k - t` contractions of `Lean.Karger.spec` on any `r`-register
file (`16 ≤ r`), as `contractDownTo_law` does, and preserves all caller registers with index
`≥ 16`. -/
theorem contractDownToAt_law {r w wb db str k t : ℕ} (hr : 16 ≤ r) {W : Fin k → Fin k → ℕ}
    {x : Data r} (ht : 2 ≤ t) (htk : t ≤ k) (hW : IsMultigraph W)
    (hst : ContractState w wb db str k t W (x.comap (Fin.castLE hr))) :
    ExecRandLaw w (contractDownToAt hr) x
      (fun y => Modifies (workspaceFootprint wb db str k) x.mem y.mem ∧
        (∀ j : Fin r, 16 ≤ j.val → y.regs j = x.regs j) ∧
        ∃ W' : Fin t → Fin t → ℕ, IsMultigraph W' ∧
          ContractState w wb db str t t W' (y.comap (Fin.castLE hr)))
      (36 * (k ^ 2 - t ^ 2) + 4) (k - t) (fun y => heldGraph wb str (y.comap (Fin.castLE hr)))
      ((Lean.Karger.spec.toRandomized.withCoins.run (Lean.Karger.contractTimes (k - t))
        ⟨k, W⟩).map Prod.snd) :=
  (ExecRandLaw.rename (Fin.castLE_injective hr) (contractDownTo_law ht htk hW hst)).mono
    (fun _ ⟨y, ⟨hmod, hy⟩, he⟩ => he ▸ ⟨hmod,
      fun j hj => Data.extend_castLE_regs_of_le (hrs := hr) y x j hj,
      by rwa [Data.comap_extend (Fin.castLE_injective hr)]⟩) le_rfl le_rfl

/-- Specification of `contractDownToAt hr` on any `r`-register file (`16 ≤ r`), preserving all
caller registers with index `≥ 16`. -/
theorem contractDownToAt_spec {r n w wb db str k t : ℕ} (hr : 16 ≤ r)
    {W₀ : Fin n → Fin n → ℕ} {W : Fin k → Fin k → ℕ} {part : Fin n → Fin k} {x : Data r}
    (ht : 2 ≤ t) (htk : t ≤ k) (hC : IsContractionOf W₀ part W)
    (hst : ContractState w wb db str k t W (x.comap (Fin.castLE hr))) :
    ∃ m : ProbComp (Data r × ℕ),
      ExecRand w (contractDownToAt hr) x m ∧
      m.IsQueryBounded (k - t) ∧
      (∀ z ∈ m.support,
        z.2 ≤ 36 * (k ^ 2 - t ^ 2) + 4 ∧
        Modifies (workspaceFootprint wb db str k) x.mem z.1.mem ∧
        (∀ j : Fin r, 16 ≤ j.val → z.1.regs j = x.regs j) ∧
        ∃ (W' : Fin t → Fin t → ℕ) (part' : Fin n → Fin t),
          IsContractionOf W₀ part' W' ∧
          ContractState w wb db str t t W' (z.1.comap (Fin.castLE hr))) ∧
      (∀ B : Finset (Fin k),
        0 < minCut W₀ → IsNonTrivialCut B →
        cutWeight W₀ (pullbackCut part B) = minCut W₀ →
        (((t * (t - 1) : ℕ) : ℝ≥0∞) / ((k * (k - 1) : ℕ) : ℝ≥0∞)) ≤
          m.eval.toOuterMeasure
            {z | SurvivalPost W₀ wb db str t (pullbackCut part B)
              (z.1.comap (Fin.castLE hr))}) := by
  obtain ⟨m₀, hm₀, hq₀, hsup₀, hsurv₀⟩ := contractDownTo_spec ht htk hC hst
  let f := Fin.castLE hr
  have hf : f.Injective := Fin.castLE_injective hr
  refine ⟨(fun z : Data 16 × ℕ => (z.1.extend f x, z.2)) <$> m₀, hm₀.rename hf,
    by simpa only [OracleComp.IsQueryBounded, OracleComp.isCostBounded_map_iff] using hq₀,
    fun z hz => ?_, fun B hmin hBnt hBmin => ?_⟩
  · obtain ⟨z₀, hz₀, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hz
    rcases hsup₀ z₀ hz₀ with ⟨ht0, hmod0, W', part', hC', hst'⟩
    exact ⟨ht0, hmod0, fun j hj => Data.extend_castLE_regs_of_le (hrs := hr) z₀.1 x j hj,
      W', part', hC', by rwa [Data.comap_extend hf]⟩
  · simp only [ProbComp.eval_map, PMF.toOuterMeasure_map_apply, Set.preimage, Set.mem_ofPred_eq, f,
      Data.comap_extend hf]
    exact hsurv₀ B hmin hBnt hBmin

end Contract

end Cslib.Algorithms.WordRAM.Karger
