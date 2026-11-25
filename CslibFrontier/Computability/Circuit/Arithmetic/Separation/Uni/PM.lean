/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.TakeDrop
import Mathlib.Tactic.FinCases

/-!
# Pointer machines

Every step loads one record from the heap and allocates one fresh record at the next address.
Each step operates on nine integer variables: the five registers (`0..4`), the three loaded record
fields (`5..7`), and the freshly allocated address (`8`).

The key lemma `Mach.gv_iff` shows that checking step-by-step causality (`Mach.Seq`) is equivalent
to the global check `Mach.GV` (where loads may refer to the full final heap) whenever the initial
heap is closed (`Mach.Closed`).

## Relation to `Cslib.PointerMachine`

This model is intentionally distinct from `CslibFrontier/Computability/PointerMachine/Defs.lean`
(`Cslib.PointerMachine`, Tarjan's deterministic PC-indexed instruction model with arbitrary `Layout`
and total operations). Here `Uni.Mach A M K` is a `CommRing`-weighted nondeterministic rule
relation over modes `M` and record kinds `K`, with fixed 5-register / 3-field bit-sliced records,
finite accepting-run weight sums (`Mach.SumTo`), and the global-heap relaxation `Mach.GV` needed by
the universal weighted-automaton reduction in `[AnthropicVPVNP2026]`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.PM`.

## Main definitions

* `Uni.Mach`: a weighted pointer machine with modes `M`, record kinds `K`, and weights in `A`.
* `Uni.rv`: embeds register index `Fin 5` into variable index `Fin 9`.
* `Uni.Rec`: a heap record `(kind, ![address, field0, field1, field2])`.
* `Uni.Mach.Step`, `Uni.Mach.ld`, `Uni.Mach.al`, `Uni.Mach.wts`.
* `Uni.Mach.State`, `Uni.Mach.Fire`, `Uni.Mach.nxt`, `Uni.Mach.Seq`.
* `Uni.Mach.GV`: globally checked trace condition.
* `Uni.Mach.Closed`: heap address-closure invariant.
* `Uni.Mach.SumTo`: finite accepting-run weight sum and length bound.

## Main results

* `Uni.Mach.gv_iff`: equivalence between global verification `GV` and step-by-step `Seq`.
* `Uni.Mach.Seq.le`: every variable value in an accepting run is bounded by `σ.n + tr.length`.
* `Uni.Mach.SumTo.mono`, `Uni.Mach.SumTo.halt`, `Uni.Mach.SumTo.fin`, `Uni.Mach.SumTo.none`,
  `Uni.Mach.SumTo.one`, `Uni.Mach.SumTo.two`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset

/-- A pointer machine with modes `M`, record kinds `K`, and weights in `A`. The nine variables of
a step are: the five registers (`0..4`), the three fields of the loaded record (`5..7`), and the
new address (`8`). -/
structure Mach (A M K : Type*) where
  /-- transition rules -/
  Rl : Type
  [fR : Fintype Rl]
  [dR : DecidableEq Rl]
  /-- mode before the step -/
  src : Rl → M
  /-- mode after the step -/
  dst : Rl → M
  /-- optional bit read from the input -/
  rd : Rl → Option Bool
  /-- kind of the record loaded in this step -/
  lk : Rl → K
  /-- register holding the address of the loaded record -/
  la : Rl → Fin 5
  /-- kind of the record allocated in this step -/
  ak : Rl → K
  /-- three variable indices supplying the new record's fields -/
  af : Rl → Fin 3 → Fin 9
  /-- variable indices supplying the five updated registers -/
  dr : Rl → Fin 5 → Fin 9
  /-- transition weight -/
  wt : Rl → A
  /-- initial mode -/
  m0 : M
  /-- halting mode -/
  mh : M
  /-- kind of the initial record at address `0` -/
  kN : K

attribute [instance] Mach.fR Mach.dR

/-- Embed a register index (`Fin 5`) as a step variable index (`Fin 9`). -/
@[expose] def rv (i : Fin 5) : Fin 9 := ⟨i.1, by omega⟩

/-- Heap records: record kind together with `[address, field0, field1, field2]`. -/
abbrev Rec (K : Type*) := K × (Fin 4 → ℕ)

namespace Mach

variable {A M K : Type*}

/-- A step: a transition rule together with an assignment to the nine variables. -/
abbrev Step (P : Mach A M K) := P.Rl × (Fin 9 → ℕ)

/-- The record loaded by step `st`. -/
@[expose] def ld {P : Mach A M K} (st : P.Step) : Rec K :=
  (P.lk st.1, ![st.2 (rv (P.la st.1)), st.2 5, st.2 6, st.2 7])

/-- The record allocated by step `st`. -/
@[expose] def al {P : Mach A M K} (st : P.Step) : Rec K :=
  (P.ak st.1, ![st.2 8, st.2 (P.af st.1 0), st.2 (P.af st.1 1), st.2 (P.af st.1 2)])

/-- The product of rule weights along a trace of steps. -/
@[expose] def wts [CommMonoid A] {P : Mach A M K} (tr : List P.Step) : A :=
  (tr.map fun st => P.wt st.1).prod

/-- A pointer-machine configuration. -/
structure State (M K : Type*) where
  /-- current control mode -/
  mode : M
  /-- current values of the five registers -/
  regs : Fin 5 → ℕ
  /-- allocated records -/
  heap : List (Rec K)
  /-- last allocated address -/
  n : ℕ
  /-- remaining input bits -/
  inp : List Bool

/-- Local validity of firing step `st` from configuration `σ`. -/
structure Fire {P : Mach A M K} (σ : State M K) (st : P.Step) : Prop where
  /-- rule source matches current mode -/
  src : P.src st.1 = σ.mode
  /-- first five variables match current registers -/
  regs : ∀ i, st.2 (rv i) = σ.regs i
  /-- fresh address equals `σ.n + 1` -/
  fresh : st.2 8 = σ.n + 1
  /-- loaded record already exists in the heap -/
  load : ld st ∈ σ.heap
  /-- rule consumes a prefix of the remaining input -/
  read : (P.rd st.1).toList <+: σ.inp

/-- The configuration resulting from executing step `st` in configuration `σ`. -/
@[expose] def nxt {P : Mach A M K} (σ : State M K) (st : P.Step) : State M K where
  mode := P.dst st.1
  regs i := st.2 (P.dr st.1 i)
  heap := σ.heap ++ [al st]
  n := σ.n + 1
  inp := σ.inp.drop (P.rd st.1).toList.length

/-- Step-by-step accepting runs of `P` starting from `σ`. -/
@[expose] def Seq (P : Mach A M K) : State M K → List P.Step → Prop
  | σ, [] => σ.mode = P.mh ∧ σ.inp = []
  | σ, st :: tr => Fire σ st ∧ Seq P (nxt σ st) tr

/-- Runs checked globally: loads may refer to any record in the final heap `σ.heap ++ tr.map al`. -/
structure GV {P : Mach A M K} (σ : State M K) (tr : List P.Step) : Prop where
  /-- mode chain runs from `σ.mode` to `P.mh` -/
  modes : σ.mode :: tr.map (fun st => P.dst st.1) = tr.map (fun st => P.src st.1) ++ [P.mh]
  /-- each register is threaded across all steps -/
  regs : ∀ i, ∃ fin, σ.regs i :: tr.map (fun st => st.2 (P.dr st.1 i)) =
    tr.map (fun st => st.2 (rv i)) ++ [fin]
  /-- fresh addresses equal `σ.n + 1, σ.n + 2, …, σ.n + tr.length` -/
  fresh : tr.map (fun st => st.2 8) = (List.range tr.length).map fun j => σ.n + 1 + j
  /-- concatenated input bits read equal `σ.inp` -/
  read : (tr.flatMap fun st => (P.rd st.1).toList) = σ.inp
  /-- every loaded record appears in the combined initial + allocated heap -/
  load : ∀ st ∈ tr, ld st ∈ σ.heap ++ tr.map al

/-- A configuration whose heap and registers use only addresses `≤ σ.n` and covers `0..σ.n`. -/
structure Closed (σ : State M K) : Prop where
  /-- every record's entries are at most `σ.n` -/
  le : ∀ c ∈ σ.heap, ∀ i, c.2 i ≤ σ.n
  /-- every address `≤ σ.n` occurs on some heap record -/
  ex : ∀ j ≤ σ.n, ∃ c ∈ σ.heap, c.2 0 = j
  /-- every register is at most `σ.n` -/
  reg : ∀ i, σ.regs i ≤ σ.n

private theorem env_cases (p : Fin 9 → Prop) (h : ∀ i : Fin 5, p (rv i))
    (h5 : p 5) (h6 : p 6) (h7 : p 7) (h8 : p 8) : ∀ i, p i := by
  intro i
  fin_cases i
  · exact h 0
  · exact h 1
  · exact h 2
  · exact h 3
  · exact h 4
  · exact h5
  · exact h6
  · exact h7
  · exact h8

theorem Closed.env {P : Mach A M K} {σ : State M K} (hσ : Closed σ) {st : P.Step}
    (hf : Fire σ st) : ∀ i, st.2 i ≤ σ.n + 1 := by
  have hl := hσ.le _ hf.load
  refine env_cases _ (fun i => ?_) ?_ ?_ ?_ ?_
  · rw [hf.regs]
    exact (hσ.reg i).trans (Nat.le_succ _)
  · exact (hl 1).trans (Nat.le_succ _)
  · exact (hl 2).trans (Nat.le_succ _)
  · exact (hl 3).trans (Nat.le_succ _)
  · exact hf.fresh.le

theorem Closed.nxt {P : Mach A M K} {σ : State M K} (hσ : Closed σ) {st : P.Step}
    (hf : Fire σ st) : Closed (Mach.nxt σ st) := by
  have he := hσ.env hf
  constructor
  · intro c hc i
    simp only [Mach.nxt, List.mem_append, List.mem_singleton] at hc ⊢
    rcases hc with hc | rfl
    · exact (hσ.le c hc i).trans (Nat.le_succ _)
    · have h4 : ∀ i : Fin 4, (al st).2 i ≤ σ.n + 1 := by
        intro i
        fin_cases i <;> exact he _
      exact h4 i
  · intro j hj
    simp only [Mach.nxt] at hj ⊢
    rcases Nat.lt_or_ge σ.n j with h | h
    · refine ⟨al st, by simp, ?_⟩
      have : (al st).2 0 = st.2 8 := rfl
      rw [this, hf.fresh]
      omega
    · obtain ⟨c, hc, h0⟩ := hσ.ex j h
      exact ⟨c, by simp [hc], h0⟩
  · intro i
    exact he _

/-- For a closed initial configuration, global verification `GV` is equivalent to sequential
acceptance `Seq`. -/
theorem gv_iff {P : Mach A M K} {σ : State M K} (hσ : Closed σ) (tr : List P.Step) :
    GV σ tr ↔ Seq P σ tr := by
  induction tr generalizing σ with
  | nil =>
    constructor
    · rintro ⟨h1, -, -, h4, -⟩
      exact ⟨by simpa using h1, by simpa using h4.symm⟩
    · rintro ⟨h1, h2⟩
      refine ⟨by simp [h1], fun i => ⟨σ.regs i, rfl⟩, rfl, by simp [h2], by simp⟩
  | cons st tr ih =>
    constructor
    · intro h
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h1
      have hr : ∀ i, σ.regs i = st.2 (rv i) ∧
          ∃ fin, st.2 (P.dr st.1 i) :: tr.map (fun st => st.2 (P.dr st.1 i)) =
            tr.map (fun st => st.2 (rv i)) ++ [fin] := by
        intro i
        obtain ⟨fin, hfin⟩ := h2 i
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at hfin
        exact ⟨hfin.1, fin, hfin.2⟩
      rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons,
        List.cons.injEq, List.map_map] at h3
      have hfr : ∀ st' ∈ tr, σ.n + 1 < st'.2 8 := by
        intro st' hst
        have hm : st'.2 8 ∈ tr.map fun st => st.2 8 := List.mem_map.2 ⟨st', hst, rfl⟩
        rw [h3.2, List.mem_map] at hm
        obtain ⟨j, -, hj⟩ := hm
        simp only [Function.comp] at hj
        omega
      have hload : ld st ∈ σ.heap := by
        have hm := h5 st (by simp)
        rw [List.mem_append] at hm
        rcases hm with hm | hm
        · exact hm
        · exfalso
          have ha : (ld st).2 0 ≤ σ.n := by
            have : (ld st).2 0 = st.2 (rv (P.la st.1)) := rfl
            rw [this, ← (hr _).1]
            exact hσ.reg _
          rw [List.map_cons, List.mem_cons, List.mem_map] at hm
          rcases hm with e | ⟨st', hst, e⟩
          · have h0 : (ld st).2 0 = (al st).2 0 := by rw [e]
            have h8 : (al st).2 0 = st.2 8 := rfl
            have := h3.1
            omega
          · have h0 : (ld st).2 0 = (al st').2 0 := by rw [e]
            have h8 : (al st').2 0 = st'.2 8 := rfl
            have := hfr st' hst
            omega
      have hf : Fire σ st := by
        refine ⟨h1.1.symm, fun i => (hr i).1.symm, by simpa using h3.1, hload, ?_⟩
        rw [← h4, List.flatMap_cons]
        exact List.prefix_append _ _
      refine ⟨hf, (ih (hσ.nxt hf)).1 ⟨h1.2, fun i => (hr i).2, ?_, ?_, ?_⟩⟩
      · rw [h3.2]
        refine List.map_congr_left fun j _ => ?_
        simp only [Function.comp, Mach.nxt]
        omega
      · simp only [Mach.nxt]
        rw [← h4, List.flatMap_cons, List.drop_left]
      · intro st' hst
        have hm := h5 st' (by simp [hst])
        simp only [Mach.nxt]
        rw [List.map_cons] at hm
        simpa using hm
    · rintro ⟨hf, h⟩
      obtain ⟨h1, h2, h3, h4, h5⟩ := (ih (hσ.nxt hf)).2 h
      refine ⟨?_, fun i => ?_, ?_, ?_, ?_⟩
      · simp only [List.map_cons, List.cons_append, List.cons.injEq]
        exact ⟨hf.src.symm, h1⟩
      · obtain ⟨fin, hfin⟩ := h2 i
        refine ⟨fin, ?_⟩
        simp only [List.map_cons, List.cons_append, List.cons.injEq]
        exact ⟨(hf.regs i).symm, hfin⟩
      · rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_cons,
          List.cons.injEq, List.map_map]
        refine ⟨hf.fresh, ?_⟩
        rw [h3]
        refine List.map_congr_left fun j _ => ?_
        simp only [Function.comp, Mach.nxt]
        omega
      · rw [List.flatMap_cons, h4]
        simp only [Mach.nxt]
        obtain ⟨rest, hrest⟩ := hf.read
        rw [← hrest, List.drop_left]
      · intro st' hst
        rw [List.mem_cons] at hst
        rw [List.map_cons]
        rcases hst with rfl | hst
        · exact List.mem_append_left _ hf.load
        · have := h5 st' hst
          simp only [Mach.nxt] at this
          simpa using this

/-- Every variable value occurring along a sequential accepting run is at most `σ.n + tr.length`. -/
theorem Seq.le {P : Mach A M K} {σ : State M K} (hσ : Closed σ) {tr : List P.Step}
    (h : Seq P σ tr) : ∀ st ∈ tr, ∀ i, st.2 i ≤ σ.n + tr.length := by
  induction tr generalizing σ with
  | nil => simp
  | cons st tr ih =>
    obtain ⟨hf, h⟩ := h
    intro st' hst i
    rw [List.mem_cons] at hst
    rw [List.length_cons]
    rcases hst with rfl | hst
    · have := hσ.env hf i
      omega
    · have := ih (hσ.nxt hf) h st' hst i
      simp only [Mach.nxt] at this
      omega

section SumTo

variable [CommRing A]

/-- The accepting runs from `σ` form a finite set whose weights sum to `S` and whose lengths are
all at most `B`. -/
@[expose] def SumTo (P : Mach A M K) (σ : State M K) (S : A) (B : ℤ) : Prop :=
  ∃ R : Finset (List P.Step),
    (∀ tr, tr ∈ R ↔ Seq P σ tr) ∧ ∑ tr ∈ R, wts tr = S ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ B

theorem SumTo.mono {P : Mach A M K} {σ : State M K} {S : A} {B B' : ℤ}
    (h : SumTo P σ S B) (hB : B ≤ B') : SumTo P σ S B' := by
  obtain ⟨R, h1, h2, h3⟩ := h
  exact ⟨R, h1, h2, fun tr htr => (h3 tr htr).trans hB⟩

/-- Halting case: when no rule starts from `P.mh`, the unique accepting run is `[]`. -/
theorem SumTo.halt {P : Mach A M K} {σ : State M K} (hm : σ.mode = P.mh) (hi : σ.inp = [])
    (hP : ∀ r, P.src r ≠ P.mh) : SumTo P σ 1 0 := by
  refine ⟨{[]}, fun tr => ?_, by simp [wts], by simp⟩
  rw [Finset.mem_singleton]
  constructor
  · rintro rfl
    exact ⟨hm, hi⟩
  · intro h
    rcases tr with _ | ⟨st, tr⟩
    · rfl
    · exact absurd (h.1.src.trans hm) (hP _)

/-- Branching step: finitely many fireable transitions with inductive `SumTo` bounds. -/
theorem SumTo.fin {P : Mach A M K} {σ : State M K} (hm : σ.mode ≠ P.mh) (F : Finset P.Step)
    (hF : ∀ st, st ∈ F ↔ Fire σ st) (S : P.Step → A) (B : ℤ)
    (h : ∀ st ∈ F, SumTo P (nxt σ st) (S st) B) :
    SumTo P σ (∑ st ∈ F, P.wt st.1 * S st) (B + 1) := by
  classical
  have h' : ∀ st, ∃ R : Finset (List P.Step),
      st ∈ F → (∀ tr, tr ∈ R ↔ Seq P (nxt σ st) tr) ∧
        ∑ tr ∈ R, wts tr = S st ∧ ∀ tr ∈ R, (tr.length : ℤ) ≤ B := by
    intro st
    by_cases hst : st ∈ F
    · obtain ⟨R, hR⟩ := h st hst
      exact ⟨R, fun _ => hR⟩
    · exact ⟨∅, fun h => absurd h hst⟩
  choose R hR using h'
  refine ⟨F.biUnion fun st => (R st).image fun tr => st :: tr, fun tr => ?_, ?_, ?_⟩
  · simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨st, hst, tr, htr, rfl⟩
      exact ⟨(hF st).1 hst, ((hR st hst).1 tr).1 htr⟩
    · intro htr
      rcases tr with _ | ⟨st, tr⟩
      · exact absurd htr.1 hm
      · have hst := (hF st).2 htr.1
        exact ⟨st, hst, tr, ((hR st hst).1 tr).2 htr.2, rfl⟩
  · rw [Finset.sum_biUnion]
    · refine Finset.sum_congr rfl fun st hst => ?_
      rw [Finset.sum_image (by intro x _ y _ e; simpa using e),
        ← (hR st hst).2.1, Finset.mul_sum]
      exact Finset.sum_congr rfl fun tr _ => by simp [wts]
    · intro st _ st' _ hne
      rw [Function.onFun, Finset.disjoint_left]
      intro tr h1 h2
      rw [Finset.mem_image] at h1 h2
      obtain ⟨t1, -, rfl⟩ := h1
      obtain ⟨t2, -, e⟩ := h2
      exact hne (List.cons.inj e).1.symm
  · intro tr htr
    simp only [Finset.mem_biUnion, Finset.mem_image] at htr
    obtain ⟨st, hst, tr, htr, rfl⟩ := htr
    have := (hR st hst).2.2 tr htr
    rw [List.length_cons]
    push_cast
    omega

/-- Stuck case: no transition can fire from a non-halting mode. -/
theorem SumTo.none {P : Mach A M K} {σ : State M K} (hm : σ.mode ≠ P.mh)
    (h : ∀ st : P.Step, ¬ Fire σ st) (B : ℤ) : SumTo P σ 0 B := by
  refine ⟨∅, fun tr => ?_, by simp, by simp⟩
  simp only [Finset.notMem_empty, false_iff]
  intro htr
  rcases tr with _ | ⟨st, tr⟩
  · exact hm htr.1
  · exact h st htr.1

/-- Deterministic step: a unique transition fires from `σ`. -/
theorem SumTo.one {P : Mach A M K} {σ : State M K} (hm : σ.mode ≠ P.mh) (st : P.Step)
    (hst : ∀ st', Fire σ st' ↔ st' = st) {S : A} {B : ℤ}
    (h : SumTo P (nxt σ st) S B) : SumTo P σ (P.wt st.1 * S) (B + 1) := by
  have h1 := SumTo.fin hm {st} (fun st' => by rw [Finset.mem_singleton, hst])
    (fun _ => S) B (by
      intro st' hst'
      rw [Finset.mem_singleton] at hst'
      subst hst'
      exact h)
  simpa using h1

/-- Two-way branch: two distinct transitions fire from `σ`. -/
theorem SumTo.two {P : Mach A M K} {σ : State M K} (hm : σ.mode ≠ P.mh) (st st₁ : P.Step)
    (hne : st ≠ st₁) (hst : ∀ st', Fire σ st' ↔ st' = st ∨ st' = st₁) {S S₁ : A} {B : ℤ}
    (h : SumTo P (nxt σ st) S B) (h₁ : SumTo P (nxt σ st₁) S₁ B) :
    SumTo P σ (P.wt st.1 * S + P.wt st₁.1 * S₁) (B + 1) := by
  classical
  have h1 := SumTo.fin hm {st, st₁}
    (fun st' => by rw [Finset.mem_insert, Finset.mem_singleton, hst])
    (fun st' => if st' = st then S else S₁) B (by
      intro st' hst'
      rw [Finset.mem_insert, Finset.mem_singleton] at hst'
      rcases hst' with rfl | rfl
      · simpa using h
      · simpa [hne.symm] using h₁)
  rw [Finset.sum_pair hne] at h1
  simpa [hne.symm] using h1

end SumTo

end Mach

end Cslib.Circuits.Arithmetic.Separation.Uni
