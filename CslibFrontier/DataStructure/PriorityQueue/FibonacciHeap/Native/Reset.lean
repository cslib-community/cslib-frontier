/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Realization.Structure
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Memory
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Decrease
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Extract
public import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Read
import CslibFrontier.Computability.WordRAM.Realization.LoopCongr
import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
import CslibFrontier.DataStructure.PriorityQueue.FibonacciHeap.Native.Domain
import CslibFrontier.Tactic.Realize

/-!
# Native `Memory.Prog` wrapper layer and sparse `O(touchedLen + 1)` Fibonacci heap reset

This module packages the existing linked `FibonacciHeap` operations as composable `Memory.Prog`
wrappers with uniform `Realizes .exact` (`work = 0`) native compilation certificates and
footprint-preserving operational/amortized specs, together with a sparse `O(touchedLen + 1)`
reset routine:

* `allocProg`: zero-cleared allocation of `9 * n + 5` words at `s.frontier` returning `base`.
* `isEmptyProg`, `getKeyProg`, `insertProg`, `decreaseKeyProg`, `extractRawProg`: composable
  `Memory.Prog` wrappers around the linked `FibonacciHeap` operations.
* `op_spec`: general framed operation spec preserving `s.frontier`, `Memory.WellFormed`, and
  every address outside `footprint n base`.
* `ResetArgs`, `resetArgsWords`, `ResetSafe`, `resetProg`: sparse `O(touchedLen + 1)` reset
  clearing `inHeap` on a caller-supplied list of `touchedLen` vertices and zeroing the four header
  scalars (`minRoot`, `numRoots`, `numMarked`, `sz`), restoring an empty framed Fibonacci heap with
  zero potential while preserving everything outside `footprint args.capacity args.heapBase`.

## Main results

* `realizes_allocProg`, `realizes_isEmptyProg`, `realizes_getKeyProg`, `realizes_insertProg`,
  `realizes_decreaseKeyProg`, `realizes_extractRawProg`, `realizes_resetProg`: uniform
  `Realizes .exact` (`work := fun _ _ => 0`) certificates.
* `allocProg_spec`, `op_spec`, `isEmptyProg_spec`, `getKeyProg_spec`, `insertProg_spec`,
  `decreaseKeyProg_spec`, `extractRawProg_spec`, `resetProg_spec`: correctness, framing
  (`Modifies`), well-formedness, and amortized/worst-case `memoryCost` certificates.
-/

public section

namespace Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native

open Cslib.WordRAM Cslib.WordRAM.Realization Cslib.DataStructure
open Cslib.DataStructure.PriorityQueue Cslib.DataStructure.PriorityQueue.WordRAM.FibonacciHeap

/-! ## Helpers -/

private theorem potential_eq_zero_of_zero {n : ℕ} {g : Cell → ℕ}
    (hr : g .numRoots = 0) (hm : g .numMarked = 0) :
    potential n g = 0 := by
  simp only [potential, view, hr, hm, Nat.mul_zero, Nat.add_zero]

private theorem layout_abs_eq_zero_of_clear {n : ℕ} {m : ℕ → ℕ} {base : ℕ} {c : Cell}
    (hc : Cell.ok n c) :
    (layout n base).abs ⟨clear m base (9 * n + 5), base + (9 * n + 5)⟩ c = 0 := by
  have hmem := addr_mem_footprint (base := base) hc
  simp only [footprint, Finset.mem_Ico] at hmem
  simp only [Record.Layout.abs, hc, ite_true]
  exact clear_of_owns (show Block.Owns ⟨base, 9 * n + 5⟩ _ from ⟨hmem.1, by dsimp only; omega⟩)

/-! ## Allocation -/

/-- Allocates a `9 * n + 5`-word zero-cleared Fibonacci heap block at `s.frontier`, returning its
base address. -/
@[expose] def allocProg (n : ℕ) : Memory.Prog ℕ :=
  Memory.alloc (9 * n + 5)

/-- Uniform exact-basis realization of `allocProg` with zero extra local work. -/
theorem realizes_allocProg : Realizes .exact
    allocProg (WordEncoding.encode (α := ℕ)) (WordEncoding.encode (α := ℕ))
    (fun w n s => Fits w (s.frontier + (9 * n + 5))) (fun _ _ => 0) := by
  have nine (n : ℕ) : n + n + n + n + n + n + n + n + n = 9 * n := by omega
  realize rewriting [allocProg, ← nine]
  exact h.of_le (by omega)

/-- `allocProg_spec`: allocates an empty framed Fibonacci heap at `s.frontier` with zero
potential, preserving all existing cells and well-formedness. -/
theorem allocProg_spec {w n K : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hfit : Fits w (s.frontier + (9 * n + 5))) :
    let prog := allocProg n
    let base := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    base = s.frontier ∧
    s'.frontier = s.frontier + (9 * n + 5) ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint n base) s.mem s'.mem ∧
    (framed hn hK base).inv s' ∧
    (framed hn hK base).abs s' = IndexedMinPQ.empty n ∧
    potential n ((layout n base).abs s') = 0 ∧
    memoryCost prog s ≤ 9 * n + 6 := by
  have hv : (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (allocProg n)) :=
    validHistory_alloc hfit
  have hbase : (Memory.spec 0).clientResult s (allocProg n) = s.frontier := rfl
  have hs' : (Memory.spec 0).clientState s (allocProg n) =
      ⟨clear s.mem s.frontier (9 * n + 5), s.frontier + (9 * n + 5)⟩ := rfl
  obtain ⟨hinv, habs⟩ := framed_alloc hn hK s
  refine ⟨hv, hbase, rfl, wellFormed_clientState hwf hv, fun a ha => ?_, ?_, ?_, ?_, ?_⟩
  · simp only [hbase, footprint, Finset.mem_Ico] at ha
    rw [hs']
    exact clear_of_not_owns (by simp only [Block.Owns]; omega)
  · simpa only [hbase, hs'] using hinv
  · simpa only [hbase, hs'] using habs
  · rw [hbase, hs']
    exact potential_eq_zero_of_zero
      (layout_abs_eq_zero_of_clear (n := n) (base := s.frontier) (c := .numRoots) trivial)
      (layout_abs_eq_zero_of_clear (n := n) (base := s.frontier) (c := .numMarked) trivial)
  · simp only [allocProg, memoryCost_alloc]; omega

/-! ## Composable `Memory.Prog` Wrappers -/

/-- Native `Memory.Prog` wrapper for `FibonacciHeap.isEmpty`. -/
@[expose] def isEmptyProg (n base : ℕ) : Memory.Prog Bool :=
  DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) isEmpty

/-- Native `Memory.Prog` wrapper for `FibonacciHeap.getKey`. -/
@[expose] def getKeyProg (n base v : ℕ) : Memory.Prog (Option ℕ) :=
  DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (getKey v)

/-- Native `Memory.Prog` wrapper for `FibonacciHeap.insert`. -/
@[expose] def insertProg (n base v k : ℕ) : Memory.Prog Unit :=
  DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (insert v k)

/-- Native `Memory.Prog` wrapper for `FibonacciHeap.decreaseKey`. -/
@[expose] def decreaseKeyProg (n base v k : ℕ) : Memory.Prog Unit :=
  DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (decreaseKey n v k)

/-- Native `Memory.Prog` wrapper for `FibonacciHeap.Native.extractRaw`. -/
@[expose] def extractRawProg (n base : ℕ) : Memory.Prog (Option (ℕ × ℕ)) :=
  DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0) (extractRaw n)

/-- Uniform exact-basis realization of `isEmptyProg` with zero extra local work. -/
theorem realizes_isEmptyProg : Realizes .exact
    (fun d : Fin 2 → ℕ => isEmptyProg (d 0) (d 1))
    (.refl _) boolWords (fun w d _ => Fits w (d 1 + (9 * d 0 + 5))) (fun _ _ => 0) :=
  (realizes_isEmpty.reindex (fun d : Fin 2 → ℕ => (d 0, d 1)) (.refl _) ![0, 1]
    (by intro d i; fin_cases i <;> rfl)).consequence
    (fun _ _ _ _ _ h => h) (fun _ _ => le_rfl)

/-- Uniform exact-basis realization of `getKeyProg` with zero extra local work. -/
theorem realizes_getKeyProg : Realizes .exact
    (fun d : Fin 3 → ℕ => getKeyProg (d 0) (d 1) (d 2))
    (.refl _) optionWords
    (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) :=
  realizes_getKey

/-- Uniform exact-basis realization of `insertProg` with zero extra local work. -/
theorem realizes_insertProg : Realizes .exact
    (fun d : Fin 4 → ℕ => insertProg (d 0) (d 1) (d 2) (d 3))
    (.refl _) (WordEncoding.encode (α := Unit))
    (fun w d _ => Fits w (d 1 + (9 * d 0 + 5)) ∧ d 2 < d 0) (fun _ _ => 0) :=
  realizes_insert

/-- Uniform exact-basis realization of `decreaseKeyProg` with zero extra local work. -/
theorem realizes_decreaseKeyProg : Realizes .exact
    (fun d : Fin 4 → ℕ => decreaseKeyProg (d 0) (d 1) (d 2) (d 3))
    (.refl _) (WordEncoding.encode (α := Unit)) decreaseValid (fun _ _ => 0) :=
  realizes_decreaseKey

/-- Uniform exact-basis realization of `extractRawProg` with zero extra local work. -/
theorem realizes_extractRawProg : Realizes .exact
    (fun d : Fin 2 → ℕ => extractRawProg (d 0) (d 1))
    (.refl _) (WordEncoding.encode (α := Option (ℕ × ℕ))) extractValid (fun _ _ => 0) :=
  realizes_extractRaw

/-! ## Operational and Amortized Specifications -/

private theorem methods_eq_link_zero {w n K base : ℕ} (hn : Fits w n) (hK : Fits w K)
    (o : IndexedMinPQ.Op n) :
    (framed hn hK base).methods o =
      DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
        (FibonacciHeap.methods n 0 K o) := by
  have h1 : (framed hn hK base).methods o =
      DataStructure.link (E := Memory.spec w) ((layout n base).methods w)
        (FibonacciHeap.methods n w K o) := rfl
  rw [h1, link_width]
  cases o <;> rfl

/-- General specification for any linked `IndexedMinPQ.Op n` on a framed Fibonacci heap:
admissibility, invariant preservation, frontier preservation, `Memory.WellFormed` preservation,
footprint-bounded `Modifies`, exact `IndexedMinPQ.step` simulation, and amortized `memoryCost`. -/
theorem op_spec {w n K base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) (o : IndexedMinPQ.Op n)
    (hv_op : IndexedMinPQ.valid K ((framed hn hK base).abs s) o) :
    let prog := DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
      (FibonacciHeap.methods n 0 K o)
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK base).inv s' ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint n base) s.mem s'.mem ∧
    IndexedMinPQ.step ((framed hn hK base).abs s) o = ((framed hn hK base).abs s', res) ∧
    memoryCost prog s + potential n ((layout n base).abs s') ≤
      charge n ((framed hn hK base).abs s) o + potential n ((layout n base).abs s) := by
  have hmethods := methods_eq_link_zero (base := base) hn hK o
  have hv_w : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s ((framed hn hK base).methods o)) :=
    ((Memory.spec w).demonicValid_iff_validHistory_runClient _ _).mp
      ((framed hn hK base).valid o hinv hv_op)
  have hv_0 : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (FibonacciHeap.methods n 0 K o))) := by
    rwa [← hmethods]
  have hrun : (Memory.spec w).ClientRun s ((framed hn hK base).methods o)
      ((Memory.spec w).clientResult s ((framed hn hK base).methods o))
      ((Memory.spec w).clientState s ((framed hn hK base).methods o))
      ((Memory.spec w).canonicalTranscript s
        ((Memory.spec w).clientHistory s ((framed hn hK base).methods o))) :=
    StateTransitionSpec.clientRun_canonical (D := Memory.spec w) s
      ((framed hn hK base).methods o) hv_w
  obtain ⟨hstep, hinv'⟩ := (framed hn hK base).correct o hinv hv_op hrun
  obtain ⟨hmod, _, hfr⟩ := (framed hn hK base).modifies o hinv hv_op hrun
  have hcost := (framed_amortized hn hK base).step o hinv hv_op hrun
  rw [StateTransitionSpec.totalCostTranscript_canonicalTranscript] at hcost
  have hres_eq : (Memory.spec w).clientResult s ((framed hn hK base).methods o) =
      (Memory.spec 0).clientResult s (DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (FibonacciHeap.methods n 0 K o)) := by
    rw [hmethods, clientResult_width]
  have hs'_eq : (Memory.spec w).clientState s ((framed hn hK base).methods o) =
      (Memory.spec 0).clientState s (DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (FibonacciHeap.methods n 0 K o)) := by
    rw [hmethods, clientState_width]
  rw [hres_eq] at hstep
  rw [hs'_eq] at hstep hinv' hmod hfr
  have hfr' : ((Memory.spec 0).clientState s (DataStructure.link (E := Memory.spec 0)
      ((layout n base).methods 0) (FibonacciHeap.methods n 0 K o))).frontier = s.frontier :=
    le_antisymm (by simpa [framed_room] using hfr) (Memory.frontier_le_clientState _ _)
  have hmod_all : Modifies (footprint n base) s.mem ((Memory.spec 0).clientState s
      (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
        (FibonacciHeap.methods n 0 K o))).mem := by
    intro a ha
    by_cases hlt : a < s.frontier
    · exact hmod a hlt (by simpa [framed_footprint] using ha)
    · have ha_fr : ((Memory.spec w).clientState s (DataStructure.link (E := Memory.spec 0)
          ((layout n base).methods 0) (FibonacciHeap.methods n 0 K o))).frontier ≤ a := by
        rw [clientState_width w, hfr']
        exact Nat.le_of_not_lt hlt
      have hm := Memory.mem_clientState_of_frontier_le s _ hv_0 ha_fr
      rwa [clientState_width w] at hm
  refine ⟨hv_0, hinv', hfr', wellFormed_clientState hwf hv_0, hmod_all,
    (((indexedMinPQSpec n K).step_iff_stepFn _ _ _ _).mp hstep).symm, ?_⟩
  rw [hmethods, ← memoryCost_eq_totalCost w, clientState_width w] at hcost
  change memoryCost _ s + (potential n ((layout n base).abs _) + 0) ≤ _ at hcost
  simpa only [Nat.add_zero] using hcost

private theorem op_update_spec {w n K base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) (o : IndexedMinPQ.Op n)
    (hv_op : IndexedMinPQ.valid K ((framed hn hK base).abs s) o)
    {s_next : IndexedMinPQ.State n} {r : o.Result}
    (hstep_def : IndexedMinPQ.step ((framed hn hK base).abs s) o = (s_next, r))
    {C : ℕ} (hcharge : charge n ((framed hn hK base).abs s) o ≤ C) :
    let prog := DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
      (FibonacciHeap.methods n 0 K o)
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK base).inv s' ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint n base) s.mem s'.mem ∧
    (framed hn hK base).abs s' = s_next ∧
    memoryCost prog s + potential n ((layout n base).abs s') ≤
      C + potential n ((layout n base).abs s) := by
  obtain ⟨hv_h, hinv', hfr', hwf', hmod, hstep, hcost⟩ := op_spec hwf hn hK hinv o hv_op
  rw [hstep_def] at hstep
  obtain ⟨habs, _⟩ := Prod.mk.inj hstep
  refine ⟨hv_h, hinv', hfr', hwf', hmod, habs.symm, ?_⟩
  omega

/-- Specification of `isEmptyProg`. -/
theorem isEmptyProg_spec {w n K base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) :
    let prog := isEmptyProg n base
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK base).inv s' ∧
    s' = s ∧
    res = decide (IndexedMinPQ.dom ((framed hn hK base).abs s) = ∅) ∧
    memoryCost prog s ≤ 1 := by
  obtain ⟨hv_h, hinv', _, _, _, hstep, hcost⟩ := op_spec hwf hn hK hinv .isEmpty trivial
  have hst : (Memory.spec 0).clientState s (isEmptyProg n base) = s := rfl
  simp only [IndexedMinPQ.step] at hstep
  obtain ⟨_, hres⟩ := Prod.mk.inj hstep
  refine ⟨hv_h, hinv', hst, hres.symm, ?_⟩
  dsimp only [FibonacciHeap.methods, isEmptyProg, charge] at hcost hst ⊢
  rw [hst] at hcost
  omega

/-- Specification of `getKeyProg`. -/
theorem getKeyProg_spec {w n K base v : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) (hv : v < n) :
    let prog := getKeyProg n base v
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK base).inv s' ∧
    s' = s ∧
    res = (framed hn hK base).abs s ⟨v, hv⟩ ∧
    memoryCost prog s ≤ 2 := by
  obtain ⟨hv_h, hinv', _, _, _, hstep, hcost⟩ :=
    op_spec hwf hn hK hinv (.getKey ⟨v, hv⟩) trivial
  have hprog : getKeyProg n base v = (do
      let b ← Memory.read (base + 7 * n + v)
      if b = 0 then pure none else do
        let k ← Memory.read (base + v)
        pure (some k)) := by
    dsimp only [getKeyProg]
    simp only [DataStructure.link, getKey, PFunctor.FreeM.liftM_bind, rd, Record.read, layout]
    congr 1 with b : 1
    split_ifs <;> rfl
  have hst : (Memory.spec 0).clientState s (getKeyProg n base v) = s := by
    rw [hprog, StateTransitionSpec.clientState_bind, clientState_read]
    split_ifs
    · rfl
    · rw [StateTransitionSpec.clientState_bind, clientState_read]; rfl
  simp only [IndexedMinPQ.step] at hstep
  obtain ⟨_, hres⟩ := Prod.mk.inj hstep
  refine ⟨hv_h, hinv', hst, hres.symm, ?_⟩
  dsimp only [FibonacciHeap.methods, getKeyProg, charge] at hcost hst ⊢
  rw [hst] at hcost
  omega

/-- Specification of `insertProg`. -/
theorem insertProg_spec {w n K base v k : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) (hv : v < n) (hk : k ≤ K)
    (habsent : (framed hn hK base).abs s ⟨v, hv⟩ = none) :
    let prog := insertProg n base v k
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK base).inv s' ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint n base) s.mem s'.mem ∧
    (framed hn hK base).abs s' =
      Function.update ((framed hn hK base).abs s) ⟨v, hv⟩ (some k) ∧
    memoryCost prog s + potential n ((layout n base).abs s') ≤
      43 + potential n ((layout n base).abs s) :=
  op_update_spec hwf hn hK hinv (.insert ⟨v, hv⟩ k) ⟨habsent, hk⟩ rfl
    (by simp only [charge, credit]; omega)

/-- Specification of `decreaseKeyProg`. -/
theorem decreaseKeyProg_spec {w n K base v k k₀ : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) (hv : v < n)
    (hold : (framed hn hK base).abs s ⟨v, hv⟩ = some k₀) (hle : k ≤ k₀) (hk : k ≤ K) :
    let prog := decreaseKeyProg n base v k
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK base).inv s' ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint n base) s.mem s'.mem ∧
    (framed hn hK base).abs s' =
      Function.update ((framed hn hK base).abs s) ⟨v, hv⟩ (some k) ∧
    memoryCost prog s + potential n ((layout n base).abs s') ≤
      104 + potential n ((layout n base).abs s) :=
  op_update_spec hwf hn hK hinv (.decreaseKey ⟨v, hv⟩ k) ⟨⟨k₀, hold, hle⟩, hk⟩ rfl
    (by simp only [charge]; omega)

/-- Specification of `extractRawProg`. -/
theorem extractRawProg_spec {w n K base : ℕ} {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w n) (hK : Fits w K)
    (hinv : (framed hn hK base).inv s) :
    let prog := extractRawProg n base
    let res := (Memory.spec 0).clientResult s prog
    let s' := (Memory.spec 0).clientState s prog
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    (framed hn hK base).inv s' ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint n base) s.mem s'.mem ∧
    (IndexedMinPQ.dom ((framed hn hK base).abs s)).card = s.mem (base + 9 * n + 4) ∧
    (res = none →
      (framed hn hK base).abs s = IndexedMinPQ.empty n ∧
      (framed hn hK base).abs s' = IndexedMinPQ.empty n) ∧
    (∀ y k, res = some (y, k) →
      ∃ hy : y < n, (framed hn hK base).abs s ⟨y, hy⟩ = some k ∧
        (∀ z : Fin n, ∀ kz, (framed hn hK base).abs s z = some kz →
          k < kz ∨ (k = kz ∧ y ≤ z.val)) ∧
        (framed hn hK base).abs s' =
          Function.update ((framed hn hK base).abs s) ⟨y, hy⟩ none) ∧
    memoryCost prog s + potential n ((layout n base).abs s') ≤
      92 * (Nat.log 2 (s.mem (base + 9 * n + 4)) + 1) + potential n ((layout n base).abs s) := by
  obtain ⟨hv_h, hinv', hfr', hwf', hmod, hstep, hcost⟩ :=
    op_spec hwf hn hK hinv .extractMin trivial
  have hrc0 := runClient_extractRaw (layout n base) 0 0 s
  have hrcw := runClient_extractRaw (layout n base) 0 w s
  have hres_eq : (Memory.spec 0).clientResult s (extractRawProg n base) =
      Option.map (fun a : Fin n × ℕ => (a.1.val, a.2))
        ((Memory.spec 0).clientResult s (DataStructure.link (E := Memory.spec 0)
          ((layout n base).methods 0) (extractMin n))) :=
    congrArg Prod.fst hrc0
  have hs'_eq : (Memory.spec 0).clientState s (extractRawProg n base) =
      (Memory.spec 0).clientState s (DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (extractMin n)) :=
    congrArg (fun p => p.2.1) hrc0
  have hhist_eq : (Memory.spec w).clientHistory s (extractRawProg n base) =
      (Memory.spec w).clientHistory s (DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (extractMin n)) :=
    congrArg (fun p => p.2.2) hrcw
  have hhist0 : (Memory.spec 0).clientHistory s (extractRawProg n base) =
      (Memory.spec 0).clientHistory s (DataStructure.link (E := Memory.spec 0)
        ((layout n base).methods 0) (extractMin n)) :=
    congrArg (fun p => p.2.2) hrc0
  have hsz_eq : (IndexedMinPQ.dom ((framed hn hK base).abs s)).card =
      s.mem (base + 9 * n + 4) := by
    obtain ⟨_, _, _, _, _, _, hsz, _⟩ := hinv.2
    have hmem : (view n ((layout n base).abs s)).sz = s.mem (base + 9 * n + 4) := by
      simp only [view, Record.Layout.abs, Cell.ok, ite_true, layout]
    exact hsz.symm.trans hmem
  simp only [IndexedMinPQ.step] at hstep
  obtain ⟨habs, hres_ex⟩ := Prod.mk.inj hstep
  dsimp only [FibonacciHeap.methods] at habs hres_ex hcost
  refine ⟨by rwa [hhist_eq], by rwa [hs'_eq], by rwa [hs'_eq], by rwa [hs'_eq],
    by rw [hs'_eq]; exact hmod, hsz_eq, ?_, ?_, ?_⟩
  · intro hnone
    rw [hres_eq, ← hres_ex] at hnone
    cases hfm : IndexedMinPQ.findMin ((framed hn hK base).abs s) with
    | none =>
      have hemp : (framed hn hK base).abs s = IndexedMinPQ.empty n := funext fun v =>
        IndexedMinPQ.notMem_dom_iff.mp
          (IndexedMinPQ.findMin_eq_none_iff.mp hfm ▸ Finset.notMem_empty v)
      exact ⟨hemp, by rw [hs'_eq, ← habs, hfm, hemp]⟩
    | some uk => simp [hfm] at hnone
  · intro y k hsome
    rw [hres_eq, ← hres_ex] at hsome
    cases hfm : IndexedMinPQ.findMin ((framed hn hK base).abs s) with
    | none => simp [hfm] at hsome
    | some uk =>
      rcases uk with ⟨m, km⟩
      simp only [hfm, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hsome
      rcases hsome with ⟨rfl, rfl⟩
      exact ⟨m.isLt, IndexedMinPQ.findMin_eq_some_state hfm,
        fun z kz hz => IndexedMinPQ.findMin_le hfm z kz hz, by rw [hs'_eq, ← habs, hfm]⟩
  · rw [hs'_eq]
    have hmc : memoryCost (extractRawProg n base) s =
        memoryCost (DataStructure.link (E := Memory.spec 0) ((layout n base).methods 0)
          (extractMin n)) s := by
      simp only [memoryCost, hhist0]
    rw [hmc, ← hsz_eq]
    simpa only [FibonacciHeap.charge, extractCharge] using hcost

/-! ## Sparse `O(touchedLen + 1)` Heap Reset -/

/-- Runtime arguments for resetting a capacity-`capacity` Fibonacci heap at `heapBase` using
an array of `touchedLen` touched vertex indices stored at `touchedBase`. -/
structure ResetArgs where
  /-- Vertex capacity `n` of the Fibonacci heap. -/
  capacity : ℕ
  /-- Base address of the `9 * capacity + 5`-word Fibonacci heap layout. -/
  heapBase : ℕ
  /-- Base address of the array holding touched vertex indices. -/
  touchedBase : ℕ
  /-- Number of touched vertex entries to clear. -/
  touchedLen : ℕ

/-- Faithful four-word encoding of `ResetArgs`. -/
word_enc_structure resetArgsWords : ResetArgs where
  capacity : wordWords,
  heapBase : wordWords,
  touchedBase : wordWords,
  touchedLen : wordWords

private structure ResetEnv where
  capacity : ℕ
  heapBase : ℕ
  touchedBase : ℕ

private word_enc_structure resetEnvWords : ResetEnv where
  capacity : wordWords,
  heapBase : wordWords,
  touchedBase : wordWords

private def resetStep (x : ResetEnv × ℕ) : Memory.Prog ℕ := do
  let env := Prod.fst x
  let i := Prod.snd x
  let v ← Memory.read (env.touchedBase + i)
  Memory.write (env.heapBase + 7 * env.capacity + v) 0
  pure (i + 1)

private def resetStepSafe (w : ℕ) (x : ResetEnv × ℕ) (s : Memory.State) : Prop :=
  let env := Prod.fst x
  let i := Prod.snd x
  Fits w (env.heapBase + (9 * env.capacity + 5)) ∧ Fits w (i + 1) ∧
    env.touchedBase + i < s.frontier ∧ s.mem (env.touchedBase + i) < env.capacity

private theorem realizes_resetStep : Realizes .exact
    resetStep (appendWords resetEnvWords wordWords) wordWords resetStepSafe (fun _ _ => 0) := by
  have seven (n : ℕ) : n + n + n + n + n + n + n = 7 * n := by omega
  realize rewriting [resetStep, ← seven]
  all_goals
    simp only [seven] at *
    rcases h with ⟨hfh, hi, hfr, hval⟩
    have hfront := hmem.frontier_fits
    fits

/-- Native safety domain for `resetProg`: word-fit bounds on the heap layout and counter,
allocation bounds on both arrays, index bounds on touched entries, and disjointness of the
touched array from the `inHeap` slice. -/
structure ResetSafe (w : ℕ) (args : ResetArgs) (s : Memory.State) : Prop where
  /-- The entire `9 * capacity + 5`-word heap layout fits in `w`-bit words. -/
  heapFit : Fits w (args.heapBase + (9 * args.capacity + 5))
  /-- The loop bound increment `touchedLen + 1` fits in `w`-bit words. -/
  touchedFit : Fits w (args.touchedLen + 1)
  /-- The touched array lies below the frontier. -/
  touchedAllocated : args.touchedBase + args.touchedLen ≤ s.frontier
  /-- The heap layout lies below the frontier. -/
  heapAllocated : args.heapBase + 9 * args.capacity + 5 ≤ s.frontier
  /-- Every touched entry is a valid vertex handle `< capacity`. -/
  touchedLt : ∀ i < args.touchedLen, s.mem (args.touchedBase + i) < args.capacity
  /-- The touched array is disjoint from the heap's `inHeap` array. -/
  touchedDisjointInHeap : ∀ i < args.touchedLen,
    args.touchedBase + i < args.heapBase + 7 * args.capacity ∨
    args.heapBase + 8 * args.capacity ≤ args.touchedBase + i

/-- Resets a Fibonacci heap in `O(touchedLen + 1)` memory operations by clearing `inHeap` on
`touched` entries and zeroing the four scalar counters `minRoot`, `numRoots`, `numMarked`, `sz`. -/
def resetProg (args : ResetArgs) : Memory.Prog Unit := do
  let _ ← iterate resetStep ⟨args.capacity, args.heapBase, args.touchedBase⟩ args.touchedLen 0
  Memory.write (args.heapBase + 9 * args.capacity + 1) 0
  Memory.write (args.heapBase + 9 * args.capacity + 2) 0
  Memory.write (args.heapBase + 9 * args.capacity + 3) 0
  Memory.write (args.heapBase + 9 * args.capacity + 4) 0

private theorem reset_iter_safe {w : ℕ} {args : ResetArgs} {s : Memory.State}
    (h : ResetSafe w args s) :
    iterationSafe resetStep resetStepSafe w
      ⟨args.capacity, args.heapBase, args.touchedBase⟩ args.touchedLen 0 s := by
  let env : ResetEnv := ⟨args.capacity, args.heapBase, args.touchedBase⟩
  let inv (j i : ℕ) (t : Memory.State) : Prop :=
    i + j = args.touchedLen ∧
    t.frontier = s.frontier ∧
    (∀ idx, i ≤ idx → idx < args.touchedLen →
      t.mem (args.touchedBase + idx) = s.mem (args.touchedBase + idx))
  refine iterationSafe_of_stepInv resetStep resetStepSafe w env inv ?_
    ⟨Nat.zero_add _, rfl, fun _ _ _ => rfl⟩
  intro j i t ⟨hj, htfr, hmem_t⟩
  have hlt : i < args.touchedLen := by omega
  have hval_eq : t.mem (args.touchedBase + i) = s.mem (args.touchedBase + i) :=
    hmem_t i le_rfl hlt
  refine ⟨?_, ?_⟩
  · refine ⟨h.heapFit, h.touchedFit.of_le (by omega), ?_, hval_eq ▸ h.touchedLt i hlt⟩
    rw [htfr]
    exact lt_of_lt_of_le (Nat.add_lt_add_left hlt args.touchedBase) h.touchedAllocated
  · have hstep_res : (Memory.spec 0).clientResult t (resetStep (env, i)) = i + 1 := rfl
    have hstep_st : (Memory.spec 0).clientState t (resetStep (env, i)) =
        ⟨Function.update t.mem
          (args.heapBase + 7 * args.capacity + t.mem (args.touchedBase + i)) 0,
          t.frontier⟩ := rfl
    refine ⟨by rw [hstep_res]; omega, by rw [hstep_st]; exact htfr, fun idx hi1 hi2 => ?_⟩
    rw [hstep_st]
    dsimp only
    have hne : args.touchedBase + idx ≠
        args.heapBase + 7 * args.capacity + t.mem (args.touchedBase + i) := by
      have hlt_v : t.mem (args.touchedBase + i) < args.capacity := hval_eq ▸ h.touchedLt i hlt
      rcases h.touchedDisjointInHeap idx hi2 with hd | hd <;> omega
    rw [Function.update_of_ne hne]
    exact hmem_t idx (by rw [hstep_res] at hi1; omega) hi2

/-- Uniform exact-basis realization of `resetProg` with zero extra local work. -/
theorem realizes_resetProg : Realizes .exact
    resetProg resetArgsWords (WordEncoding.encode (α := Unit)) ResetSafe (fun _ _ => 0) := by
  have nine (n : ℕ) : n + n + n + n + n + n + n + n + n = 9 * n := by omega
  realize [realizes_resetStep] rewriting [resetProg, ← nine]
  all_goals
    simp only [nine] at *
    have hfront := hmem.frontier_fits
    have hfr_it := Memory.frontier_le_clientState (w := 0) s
      (iterate resetStep ⟨d.capacity, d.heapBase, d.touchedBase⟩ d.touchedLen 0)
    first
    | exact iterationSafe_imp (reset_iter_safe h) (fun _ => rfl) (fun _ _ hs => hs)
    | exact h.heapFit.of_le (by omega)

/-- Specification of `resetProg`: clears all touched `inHeap` entries and zeroes the four
header scalars, restoring an empty framed Fibonacci heap with zero potential in `O(touchedLen + 1)`
memory operations while preserving the frontier and every cell outside `footprint`. -/
theorem resetProg_spec {w K : ℕ} (args : ResetArgs) {s : Memory.State}
    (hwf : Memory.WellFormed w s) (hn : Fits w args.capacity) (hK : Fits w K)
    (hfit_tl : Fits w (args.touchedLen + 1))
    (hinv : (framed hn hK args.heapBase).inv s)
    (ht_fr : args.touchedBase + args.touchedLen ≤ s.frontier)
    (hvals : ∀ i < args.touchedLen, s.mem (args.touchedBase + i) < args.capacity)
    (hdisj : ∀ i < args.touchedLen,
      args.touchedBase + i < args.heapBase + 7 * args.capacity ∨
      args.heapBase + 8 * args.capacity ≤ args.touchedBase + i)
    (hcov : ∀ v : Fin args.capacity, ((framed hn hK args.heapBase).abs s v).isSome →
      ∃ i < args.touchedLen, s.mem (args.touchedBase + i) = v.val) :
    let prog := resetProg args
    let s' := (Memory.spec 0).clientState s prog
    ResetSafe w args s ∧
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s prog) ∧
    s'.frontier = s.frontier ∧
    Memory.WellFormed w s' ∧
    Modifies (footprint args.capacity args.heapBase) s.mem s'.mem ∧
    (framed hn hK args.heapBase).inv s' ∧
    (framed hn hK args.heapBase).abs s' = IndexedMinPQ.empty args.capacity ∧
    potential args.capacity ((layout args.capacity args.heapBase).abs s') = 0 ∧
    memoryCost prog s ≤ 2 * args.touchedLen + 4 := by
  have hfh_fr : args.heapBase + 9 * args.capacity + 5 ≤ s.frontier := by
    have hlt := hinv.1 .sz trivial
    simp only [layout] at hlt
    omega
  have hfh_fit : Fits w (args.heapBase + (9 * args.capacity + 5)) :=
    hwf.frontier_fits.of_le (by omega)
  have hsafe : ResetSafe w args s :=
    ⟨hfh_fit, hfit_tl, ht_fr, hfh_fr, hvals, hdisj⟩
  let env : ResetEnv := ⟨args.capacity, args.heapBase, args.touchedBase⟩
  let mod (x : ℕ) : Prop :=
    args.heapBase + 7 * args.capacity ≤ x ∧ x < args.heapBase + 8 * args.capacity
  let inv (k idx : ℕ) (t : Memory.State) : Prop :=
    idx = k ∧ t.frontier = s.frontier ∧
    (∀ x, ¬mod x → t.mem x = s.mem x) ∧
    (∀ i < k, t.mem (args.heapBase + 7 * args.capacity + s.mem (args.touchedBase + i)) = 0) ∧
    (∀ v : Fin args.capacity, (framed hn hK args.heapBase).abs s v = none →
      t.mem (args.heapBase + 7 * args.capacity + v.val) = 0)
  have hnone0 : ∀ v : Fin args.capacity, (framed hn hK args.heapBase).abs s v = none →
      s.mem (args.heapBase + 7 * args.capacity + v.val) = 0 := by
    intro v hv
    obtain ⟨_, _, _, _, hin_h, _⟩ := hinv.2
    by_contra hne
    have hne' :
        (view args.capacity ((layout args.capacity args.heapBase).abs s)).inHeap v ≠ 0 := by
      simpa only [view, Record.Layout.abs, Cell.ok, v.isLt, ite_true, layout] using hne
    have his : (abs args.capacity ((layout args.capacity args.heapBase).abs s) v).isSome :=
      (hin_h v).1.mp hne'
    change ((framed hn hK args.heapBase).abs s v).isSome at his
    simp [hv] at his
  have hiter := iterate_spec resetStep resetStepSafe w env 2 args.touchedLen inv mod
    (fun k hk idx t ⟨hk_eq, htfr, htmem, htclr, htnone⟩ => by
      subst hk_eq
      have htb_not_mod : ¬mod (args.touchedBase + idx) := by
        rcases hdisj idx hk with h1 | h2 <;> simp only [mod] <;> omega
      have hval_eq : t.mem (args.touchedBase + idx) = s.mem (args.touchedBase + idx) :=
        htmem _ htb_not_mod
      have hlt_v : s.mem (args.touchedBase + idx) < args.capacity := hvals idx hk
      have hhs : resetStepSafe w (env, idx) t := by
        dsimp only [resetStepSafe, env]
        exact ⟨hfh_fit, hfit_tl.of_le (by omega), by rw [htfr]; omega, hval_eq ▸ hlt_v⟩
      have hv_step : (Memory.spec w).ValidHistory t
          ((Memory.spec w).clientHistory t (resetStep (env, idx))) := by
        dsimp only [resetStep, env]
        exact validHistory_read_bind (by rw [htfr]; omega)
          (validHistory_write_bind (by rw [htfr, hval_eq]; omega) (fits_zero w)
            (validHistory_pure w _ _))
      have hcost_step : memoryCost (resetStep (env, idx)) t ≤ 2 := by
        simp only [resetStep, memoryCost_bind', memoryCost_read, memoryCost_write,
          memoryCost_pure]
        omega
      have hst : (Memory.spec 0).clientState t (resetStep (env, idx)) =
          ⟨Function.update t.mem (args.heapBase + 7 * args.capacity +
            t.mem (args.touchedBase + idx)) 0, t.frontier⟩ := rfl
      have hne_upd : ∀ {x}, ¬mod x →
          x ≠ args.heapBase + 7 * args.capacity + t.mem (args.touchedBase + idx) :=
        fun hx h => hx (by simp only [mod, hval_eq] at h ⊢; omega)
      refine ⟨hhs, hv_step, hcost_step, by rw [hst], fun x hx => ?_,
        rfl, by rw [hst]; exact htfr, fun x hx => ?_, fun i hi => ?_, fun v hv => ?_⟩
      · simp only [hst, Function.update_of_ne (hne_upd hx)]
      · simpa only [hst, Function.update_of_ne (hne_upd hx)] using htmem x hx
      · rw [hst]
        dsimp only
        rw [hval_eq]
        by_cases hik : i = idx
        · subst hik; rw [Function.update_self]
        · by_cases hsame : s.mem (args.touchedBase + i) = s.mem (args.touchedBase + idx)
          · rw [hsame, Function.update_self]
          · rw [Function.update_of_ne (by omega)]
            exact htclr i (by omega)
      · rw [hst]
        dsimp only
        by_cases hsame : v.val = t.mem (args.touchedBase + idx)
        · rw [hsame, Function.update_self]
        · rw [Function.update_of_ne (by omega)]
          exact htnone v hv)
    0 s ⟨rfl, rfl, fun _ _ => rfl, fun _ hi => by omega, hnone0⟩
  rcases hiter with ⟨_, hv_iter, hc_iter, hfr_iter, hmod_iter, _, _, _, hclr_iter, hnone_iter⟩
  set s₁ := (Memory.spec 0).clientState s (iterate resetStep env args.touchedLen 0)
  have hcons_s₁ : ∀ d ≤ args.capacity, s₁.mem (args.heapBase + 8 * args.capacity + d) = 0 := by
    intro d hd
    have hnot : ¬mod (args.heapBase + 8 * args.capacity + d) := by simp only [mod]; omega
    rw [hmod_iter _ hnot]
    obtain ⟨_, _, _, _, _, _, _, _, _, hcons, _⟩ := hinv.2
    have hcons' : (view args.capacity ((layout args.capacity args.heapBase).abs s)).cons d = 0 :=
      hcons d hd
    simpa only [view, Record.Layout.abs, Cell.ok, hd, ite_true, layout] using hcons'
  have hin_s₁ : ∀ v : Fin args.capacity,
      s₁.mem (args.heapBase + 7 * args.capacity + v.val) = 0 := by
    intro v
    cases habs_v : (framed hn hK args.heapBase).abs s v with
    | none => exact hnone_iter v habs_v
    | some _ =>
      obtain ⟨i, hi, hvi⟩ := hcov v (by simp [habs_v])
      simpa only [hvi] using hclr_iter i hi
  have hv_all : (Memory.spec w).ValidHistory s
      ((Memory.spec w).clientHistory s (resetProg args)) := by
    dsimp only [resetProg]
    refine validHistory_bind_step hv_iter ?_
    change (Memory.spec w).ValidHistory s₁ _
    exact validHistory_write_bind (by rw [hfr_iter]; omega) (fits_zero w)
      (validHistory_write_bind (by rw [hfr_iter]; omega) (fits_zero w)
        (validHistory_write_bind (by rw [hfr_iter]; omega) (fits_zero w)
          (validHistory_write (by rw [hfr_iter]; omega) (fits_zero w))))
  have hs'_eq : (Memory.spec 0).clientState s (resetProg args) =
      ⟨Function.update (Function.update (Function.update (Function.update s₁.mem
        (args.heapBase + 9 * args.capacity + 1) 0) (args.heapBase + 9 * args.capacity + 2) 0)
        (args.heapBase + 9 * args.capacity + 3) 0) (args.heapBase + 9 * args.capacity + 4) 0,
        s₁.frontier⟩ := by
    dsimp only [resetProg]
    rw [StateTransitionSpec.clientState_bind]
    rfl
  have hfr' : ((Memory.spec 0).clientState s (resetProg args)).frontier = s.frontier :=
    (congrArg Memory.State.frontier hs'_eq).trans hfr_iter
  have hmod' : Modifies (footprint args.capacity args.heapBase) s.mem
      ((Memory.spec 0).clientState s (resetProg args)).mem := by
    intro a hfp
    simp only [footprint, Finset.mem_Ico] at hfp
    rw [hs'_eq]
    dsimp only
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hmod_iter a (fun ⟨h1, h2⟩ => hfp ⟨by omega, by omega⟩)
  have hfib_raw : FibRawInv args.capacity K (IndexedMinPQ.empty args.capacity)
      (view args.capacity ((layout args.capacity args.heapBase).abs
        ((Memory.spec 0).clientState s (resetProg args)))) := by
    refine FibRawInv.empty ?_ ?_ ?_ ?_ ?_ ?_
    · intro v
      rw [hs'_eq]
      simp only [view, Record.Layout.abs, Cell.ok, v.isLt, ite_true, layout]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hin_s₁ v
    · intro d hd
      rw [hs'_eq]
      simp only [view, Record.Layout.abs, Cell.ok, hd, ite_true, layout]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact hcons_s₁ d hd
    · rw [hs'_eq]
      simp only [view, Record.Layout.abs, Cell.ok, ite_true, layout]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [hs'_eq]
      simp only [view, Record.Layout.abs, Cell.ok, ite_true, layout]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [hs'_eq]
      simp only [view, Record.Layout.abs, Cell.ok, ite_true, layout]
      rw [Function.update_of_ne (by omega), Function.update_self]
    · rw [hs'_eq]
      simp only [view, Record.Layout.abs, Cell.ok, ite_true, layout]
      rw [Function.update_self]
  obtain ⟨hinv_rec, habs_rec⟩ := inv_of_fibRawInv hfib_raw
  have hinv_lay : (layout args.capacity args.heapBase).Inv
      ((Memory.spec 0).clientState s (resetProg args)) :=
    fun i hi => hfr' ▸ hinv.1 i hi
  have hpot' : potential args.capacity ((layout args.capacity args.heapBase).abs
      ((Memory.spec 0).clientState s (resetProg args))) = 0 := by
    refine potential_eq_zero_of_zero ?_ ?_
    · rw [hs'_eq]
      simp only [Record.Layout.abs, Cell.ok, ite_true, layout]
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega), Function.update_self]
    · rw [hs'_eq]
      simp only [Record.Layout.abs, Cell.ok, ite_true, layout]
      rw [Function.update_of_ne (by omega), Function.update_self]
  have hcost' : memoryCost (resetProg args) s ≤ 2 * args.touchedLen + 4 := by
    dsimp only [resetProg]
    rw [memoryCost_bind']
    change memoryCost (iterate resetStep env args.touchedLen 0) s + memoryCost _ s₁ ≤ _
    have h4 : memoryCost (do
        Memory.write (args.heapBase + 9 * args.capacity + 1) 0
        Memory.write (args.heapBase + 9 * args.capacity + 2) 0
        Memory.write (args.heapBase + 9 * args.capacity + 3) 0
        Memory.write (args.heapBase + 9 * args.capacity + 4) 0) s₁ ≤ 4 := by
      simp only [memoryCost_bind', memoryCost_write]
      omega
    omega
  exact ⟨hsafe, hv_all, hfr', wellFormed_clientState hwf hv_all, hmod', ⟨hinv_lay, hinv_rec⟩,
    habs_rec, hpot', hcost'⟩

end Cslib.DataStructure.PriorityQueue.FibonacciHeap.Native
