/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Reduction.TruthTable
public import CslibFrontier.Computability.Complexity.Reduction.TruthTable.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup

/-!
# Bounded, disjunctive, conjunctive and positive truth-table reductions

Restrictions of polynomial-time truth-table reductions
(`Cslib.Complexity.PolyTimeTruthTableReducible`) [Ladner, Lynch and Selman][LadnerLynchSelman1975]:

* a **`k`-truth-table** reduction makes at most `k` queries, and a **bounded truth-table**
  reduction makes at most `k` queries for some fixed `k`;
* a **disjunctive** (**conjunctive**) truth-table reduction accepts exactly when some (every)
  query is in the target set, so it needs no combiner;
* a **positive** truth-table reduction has a combiner that is monotone in the answers. Positivity
  is taken semantically, as a monotone polynomial-time combiner; it is not the syntactic notion
  of a Boolean formula built from `∧` and `∨`.

Each definition instantiates a resource-free kernel of
`CslibFrontier.Computability.Reduction.TruthTable` (`Cslib.Complexity.TruthTableReducibleBy`,
`Cslib.Complexity.PTTReducibleBy`, `Cslib.Complexity.DTTReducibleBy` or
`Cslib.Complexity.CTTReducibleBy`), whose lemmas prove the inclusions, complementation, duality and
composition laws below.

## Main definitions

* `Cslib.Complexity.PolyTimeKTruthTableReducible`, `Cslib.Complexity.PolyTimeBTTReducible`.
* `Cslib.Complexity.PolyTimeDTTReducible`, `Cslib.Complexity.PolyTimeCTTReducible`.
* `Cslib.Complexity.PolyTimePTTReducible`.

## Main results

* The hierarchy `≤ₘ ⇒ ≤₁-tt ⇒ ≤ₖ-tt ⇒ ≤btt ⇒ ≤tt` and `≤ₘ ⇒ ≤dtt, ≤ctt ⇒ ≤ptt ⇒ ≤tt`:
  `Cslib.Complexity.PolyTimeReducible.polyTimeKTruthTableReducible_one`,
  `Cslib.Complexity.PolyTimeKTruthTableReducible.mono`,
  `Cslib.Complexity.PolyTimeKTruthTableReducible.polyTimeBTTReducible`,
  `Cslib.Complexity.PolyTimeBTTReducible.polyTimeTruthTableReducible`,
  `Cslib.Complexity.PolyTimeReducible.polyTimeDTTReducible`,
  `Cslib.Complexity.PolyTimeReducible.polyTimeCTTReducible`,
  `Cslib.Complexity.PolyTimeReducible.polyTimePTTReducible`,
  `Cslib.Complexity.PolyTimeDTTReducible.polyTimePTTReducible`,
  `Cslib.Complexity.PolyTimeCTTReducible.polyTimePTTReducible`,
  `Cslib.Complexity.PolyTimePTTReducible.polyTimeTruthTableReducible`.
* Complementation and duality: `compl_left`, `compl_right` and `compl` for
  `PolyTimeKTruthTableReducible` and `PolyTimeBTTReducible`, and
  `Cslib.Complexity.polyTimeDTTReducible_iff_polyTimeCTTReducible_compl`.
* Transitivity: `Cslib.Complexity.PolyTimeTruthTableReducible.trans` (re-exported from
  `CslibFrontier.Computability.Complexity.Reduction.TruthTable.Composition`),
  `Cslib.Complexity.PolyTimeKTruthTableReducible.trans` (`k`- and `k'`-query reductions compose to a
  `k * k'`-query reduction), `Cslib.Complexity.PolyTimeBTTReducible.trans`,
  `Cslib.Complexity.PolyTimeDTTReducible.trans`, `Cslib.Complexity.PolyTimeCTTReducible.trans`,
  `Cslib.Complexity.PolyTimePTTReducible.trans`.
* Reflexivity of bounded, disjunctive, conjunctive and positive truth-table reducibility:
  `Cslib.Complexity.PolyTimeBTTReducible.refl`, `Cslib.Complexity.PolyTimeDTTReducible.refl`,
  `Cslib.Complexity.PolyTimeCTTReducible.refl`, `Cslib.Complexity.PolyTimePTTReducible.refl`.
* Closure of `P` under bounded, disjunctive, conjunctive and positive truth-table reductions:
  `Cslib.Complexity.PolyTimeBTTReducible.mem_P`, `Cslib.Complexity.PolyTimeDTTReducible.mem_P`,
  `Cslib.Complexity.PolyTimeCTTReducible.mem_P`, `Cslib.Complexity.PolyTimePTTReducible.mem_P`.

## References

* [R. E. Ladner, N. A. Lynch, A. L. Selman, *A comparison of polynomial time
  reducibilities*][LadnerLynchSelman1975]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
  {L : Set α} {B : Set β} {C : Set γ}

/-! ### Bounded truth-table reductions -/

/-- A truth-table reduction making at most `k` queries on every input. -/
def PolyTimeKTruthTableReducible (k : ℕ) (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (L : Set α) (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    (ComputableInPolyTime r encA encUnary ∧
      ComputableInPolyTime q (encPair encA encUnary) encB ∧
      ComputableInPolyTime d (encPair encA encBits) encBool ∧
      ∀ a, r a ≤ k) ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

/-- A truth-table reduction making a bounded number of queries. -/
def PolyTimeBTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ k, PolyTimeKTruthTableReducible k encA encB L B

/-- A many-one reduction is a `1`-truth-table reduction. -/
theorem PolyTimeReducible.polyTimeKTruthTableReducible_one (h : PolyTimeReducible encA encB L B) :
    PolyTimeKTruthTableReducible 1 encA encB L B :=
  ManyOneReducibleBy.truthTableReducibleBy
    (fun _ hf => ⟨by fun_prop, by fun_prop, by fun_prop, fun _ => le_rfl⟩) h

/-- Allowing more queries. -/
theorem PolyTimeKTruthTableReducible.mono {k k' : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) (hk : k ≤ k') :
    PolyTimeKTruthTableReducible k' encA encB L B :=
  TruthTableReducibleBy.mono
    (fun _ _ _ ⟨hr, hq, hd, hrk⟩ => ⟨hr, hq, hd, fun a => (hrk a).trans hk⟩) h

/-- A `k`-truth-table reduction is a bounded truth-table reduction. -/
theorem PolyTimeKTruthTableReducible.polyTimeBTTReducible {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) : PolyTimeBTTReducible encA encB L B :=
  ⟨k, h⟩

/-- A bounded truth-table reduction is a truth-table reduction. -/
theorem PolyTimeBTTReducible.polyTimeTruthTableReducible (h : PolyTimeBTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  let ⟨_, h⟩ := h
  TruthTableReducibleBy.mono (fun _ _ _ ⟨hr, hq, hd, _⟩ => ⟨hr, hq, hd⟩) h

/-- A many-one reduction is a bounded truth-table reduction. -/
theorem PolyTimeReducible.polyTimeBTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeBTTReducible encA encB L B :=
  h.polyTimeKTruthTableReducible_one.polyTimeBTTReducible

/-- Bounded truth-table reducibility is reflexive. -/
@[refl]
theorem PolyTimeBTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeBTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeBTTReducible

/-- Negating the combiner keeps the queries, so a `k`-truth-table reduction from `L` to `B` gives
one from `Lᶜ` to `B`. -/
theorem PolyTimeKTruthTableReducible.compl_left {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) :
    PolyTimeKTruthTableReducible k encA encB Lᶜ B :=
  TruthTableReducibleBy.compl_left (fun _ _ _ ⟨hr, hq, hd, hrk⟩ => ⟨hr, hq, by fun_prop, hrk⟩) h

/-- Negating each answer bit before evaluation turns a `k`-truth-table reduction from `L` to `B`
into one from `L` to `Bᶜ`. -/
theorem PolyTimeKTruthTableReducible.compl_right {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) :
    PolyTimeKTruthTableReducible k encA encB L Bᶜ :=
  TruthTableReducibleBy.compl_right (fun _ _ _ ⟨hr, hq, hd, hrk⟩ => ⟨hr, hq, by fun_prop, hrk⟩) h

/-- A `k`-truth-table reduction from `L` to `B` gives one from `Lᶜ` to `Bᶜ`. -/
theorem PolyTimeKTruthTableReducible.compl {k : ℕ}
    (h : PolyTimeKTruthTableReducible k encA encB L B) :
    PolyTimeKTruthTableReducible k encA encB Lᶜ Bᶜ :=
  TruthTableReducibleBy.compl (fun _ _ _ ⟨hr, hq, hd, hrk⟩ => ⟨hr, hq, by fun_prop, hrk⟩) h

/-- Negating the combiner turns a bounded truth-table reduction from `L` to `B` into one from `Lᶜ`
to `B`. -/
theorem PolyTimeBTTReducible.compl_left (h : PolyTimeBTTReducible encA encB L B) :
    PolyTimeBTTReducible encA encB Lᶜ B :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.compl_left⟩

/-- Negating the answer bits turns a bounded truth-table reduction from `L` to `B` into one from
`L` to `Bᶜ`. -/
theorem PolyTimeBTTReducible.compl_right (h : PolyTimeBTTReducible encA encB L B) :
    PolyTimeBTTReducible encA encB L Bᶜ :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.compl_right⟩

/-- A bounded truth-table reduction from `L` to `B` gives one from `Lᶜ` to `Bᶜ`. -/
theorem PolyTimeBTTReducible.compl (h : PolyTimeBTTReducible encA encB L B) :
    PolyTimeBTTReducible encA encB Lᶜ Bᶜ :=
  let ⟨k, hk⟩ := h
  ⟨k, hk.compl⟩

/-- `P` is closed under bounded truth-table reductions. -/
theorem PolyTimeBTTReducible.mem_P (h : PolyTimeBTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- Composing a `k`-truth-table and a `k'`-truth-table reduction gives a `k * k'`-truth-table
reduction, via quotient/remainder block indexing (`TruthTableReducibleBy.trans_bounded`). -/
@[trans]
theorem PolyTimeKTruthTableReducible.trans {k k' : ℕ}
    (hLB : PolyTimeKTruthTableReducible k encA encB L B)
    (hBC : PolyTimeKTruthTableReducible k' encB encC B C) :
    PolyTimeKTruthTableReducible (k * k') encA encC L C :=
  TruthTableReducibleBy.trans_bounded (fun _ _ _ h => h.2.2.2) (fun _ _ _ h => h.2.2.2)
    (fun _ _ _ _ _ _ ⟨hr, hq, hd, _⟩ ⟨hr', hq', hd', _⟩ hmul =>
      ⟨by fun_prop, computableInPolyTime_truthTableCompQuery hq hq' (.const k'),
        computableInPolyTime_truthTableCompCombiner hr hq hd hr' hd' (.const k'), hmul⟩)
    hLB hBC

/-- **Bounded truth-table reductions compose.** -/
@[trans]
theorem PolyTimeBTTReducible.trans (hLB : PolyTimeBTTReducible encA encB L B)
    (hBC : PolyTimeBTTReducible encB encC B C) : PolyTimeBTTReducible encA encC L C :=
  let ⟨_, h₁⟩ := hLB
  let ⟨_, h₂⟩ := hBC
  ⟨_, h₁.trans h₂⟩

/-! ### Disjunctive and conjunctive truth-table reductions -/

/-- `a ∈ L` exactly when some of the `r a` queries `q (a, i)` is in `B`. -/
def PolyTimeDTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    (ComputableInPolyTime r encA encUnary ∧ ComputableInPolyTime q (encPair encA encUnary) encB) ∧
    ∀ a, a ∈ L ↔ ∃ i < r a, q (a, i) ∈ B

/-- `a ∈ L` exactly when every one of the `r a` queries `q (a, i)` is in `B`. -/
def PolyTimeCTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β),
    (ComputableInPolyTime r encA encUnary ∧ ComputableInPolyTime q (encPair encA encUnary) encB) ∧
    ∀ a, a ∈ L ↔ ∀ i < r a, q (a, i) ∈ B

/-- Disjunctive reductions of `L` to `B` are the conjunctive reductions of `Lᶜ` to `Bᶜ`, with the
same queries. -/
theorem polyTimeDTTReducible_iff_polyTimeCTTReducible_compl :
    PolyTimeDTTReducible encA encB L B ↔ PolyTimeCTTReducible encA encB Lᶜ Bᶜ :=
  dttReducibleBy_iff_cttReducibleBy_compl

/-- A many-one reduction is a disjunctive reduction with one query. -/
theorem PolyTimeReducible.polyTimeDTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeDTTReducible encA encB L B :=
  ManyOneReducibleBy.dttReducibleBy (fun _ hf => ⟨by fun_prop, by fun_prop⟩) h

/-- A many-one reduction is a conjunctive reduction with one query. -/
theorem PolyTimeReducible.polyTimeCTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimeCTTReducible encA encB L B :=
  ManyOneReducibleBy.cttReducibleBy (fun _ hf => ⟨by fun_prop, by fun_prop⟩) h

/-- Disjunctive truth-table reducibility is reflexive. -/
@[refl]
theorem PolyTimeDTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeDTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeDTTReducible

/-- Conjunctive truth-table reducibility is reflexive. -/
@[refl]
theorem PolyTimeCTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimeCTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimeCTTReducible

private theorem computableInPolyTime_dttComp {r : α → ℕ} {q : α × ℕ → β}
    {r' : β → ℕ} {q' : β × ℕ → γ}
    (hr : ComputableInPolyTime r encA encUnary)
    (hq : ComputableInPolyTime q (encPair encA encUnary) encB)
    (hr' : ComputableInPolyTime r' encB encUnary)
    (hq' : ComputableInPolyTime q' (encPair encB encUnary) encC) :
    ComputableInPolyTime (fun a => (truthTableCompPairs r q r' a).length) encA encUnary ∧
      ComputableInPolyTime (dttCompQuery r q r' q') (encPair encA encUnary) encC := by
  have hpairs : ComputableInPolyTime (truthTableCompPairs r q r') encA
      (encList (encPair encUnary encUnary)) := by
    unfold truthTableCompPairs
    fun_prop
  have hij : ComputableInPolyTime
      (fun x : α × ℕ => (truthTableCompPairs r q r' x.1)[x.2]?.getD (0, 0))
      (encPair encA encUnary) (encPair encUnary encUnary) := by
    fun_prop
  exact ⟨by fun_prop, by unfold dttCompQuery; fun_prop⟩

/-- Composing disjunctive reductions via `DTTReducibleBy.trans`. -/
@[trans]
theorem PolyTimeDTTReducible.trans
    (hLB : PolyTimeDTTReducible encA encB L B) (hBC : PolyTimeDTTReducible encB encC B C) :
    PolyTimeDTTReducible encA encC L C :=
  DTTReducibleBy.trans
    (fun _ _ _ _ ⟨hr, hq⟩ ⟨hr', hq'⟩ => computableInPolyTime_dttComp hr hq hr' hq') hLB hBC

/-- Composing conjunctive reductions via `CTTReducibleBy.trans`. -/
@[trans]
theorem PolyTimeCTTReducible.trans
    (hLB : PolyTimeCTTReducible encA encB L B) (hBC : PolyTimeCTTReducible encB encC B C) :
    PolyTimeCTTReducible encA encC L C :=
  CTTReducibleBy.trans
    (fun _ _ _ _ ⟨hr, hq⟩ ⟨hr', hq'⟩ => computableInPolyTime_dttComp hr hq hr' hq') hLB hBC

/-! ### Positive truth-table reductions -/

/-- A truth-table reduction whose combiner is monotone in the answers: turning answers from
`false` to `true` never turns acceptance into rejection. -/
def PolyTimePTTReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool) (L : Set α)
    (B : Set β) : Prop :=
  ∃ (r : α → ℕ) (q : α × ℕ → β) (d : α × List Bool → Bool),
    (ComputableInPolyTime r encA encUnary ∧
      ComputableInPolyTime q (encPair encA encUnary) encB ∧
      ComputableInPolyTime d (encPair encA encBits) encBool ∧
      ∀ a u v, List.Forall₂ (· ≤ ·) u v → d (a, u) ≤ d (a, v)) ∧
    ∀ a, a ∈ L ↔ d (a, truthTableAnswers (q ⁻¹' B) r a) = true

private theorem polyTimePTTReducible_iff_pttReducibleBy :
    PolyTimePTTReducible encA encB L B ↔
      PTTReducibleBy (fun r q d => ComputableInPolyTime r encA encUnary ∧
        ComputableInPolyTime q (encPair encA encUnary) encB ∧
        ComputableInPolyTime d (encPair encA encBits) encBool) L B :=
  exists₃_congr fun _ _ _ => and_congr_left fun _ =>
    ⟨fun ⟨hr, hq, hd, hm⟩ => ⟨⟨hr, hq, hd⟩, hm⟩, fun ⟨⟨hr, hq, hd⟩, hm⟩ => ⟨hr, hq, hd, hm⟩⟩

/-- A positive truth-table reduction is a truth-table reduction. -/
theorem PolyTimePTTReducible.polyTimeTruthTableReducible (h : PolyTimePTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  (polyTimePTTReducible_iff_pttReducibleBy.mp h).toTruthTableReducibleBy

/-- A many-one reduction is a positive truth-table reduction with one query. -/
theorem PolyTimeReducible.polyTimePTTReducible (h : PolyTimeReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B :=
  polyTimePTTReducible_iff_pttReducibleBy.mpr <|
    ManyOneReducibleBy.pttReducibleBy (fun _ hf => ⟨by fun_prop, by fun_prop, by fun_prop⟩) h

/-- Positive truth-table reducibility is reflexive. -/
@[refl]
theorem PolyTimePTTReducible.refl (encA : α ↪ List Bool) (L : Set α) :
    PolyTimePTTReducible encA encA L L :=
  (PolyTimeReducible.refl encA L).polyTimePTTReducible

/-- A disjunctive reduction is positive, with the disjunction of the answers as combiner. -/
theorem PolyTimeDTTReducible.polyTimePTTReducible (h : PolyTimeDTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B :=
  polyTimePTTReducible_iff_pttReducibleBy.mpr <|
    DTTReducibleBy.pttReducibleBy (fun _ _ ⟨hr, hq⟩ => ⟨hr, hq, by fun_prop⟩) h

/-- A conjunctive reduction is positive, with the conjunction of the answers as combiner. -/
theorem PolyTimeCTTReducible.polyTimePTTReducible (h : PolyTimeCTTReducible encA encB L B) :
    PolyTimePTTReducible encA encB L B :=
  polyTimePTTReducible_iff_pttReducibleBy.mpr <|
    CTTReducibleBy.pttReducibleBy (fun _ _ ⟨hr, hq⟩ => ⟨hr, hq, by fun_prop⟩) h

/-- A disjunctive truth-table reduction is a truth-table reduction. -/
theorem PolyTimeDTTReducible.polyTimeTruthTableReducible (h : PolyTimeDTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  h.polyTimePTTReducible.polyTimeTruthTableReducible

/-- A conjunctive truth-table reduction is a truth-table reduction. -/
theorem PolyTimeCTTReducible.polyTimeTruthTableReducible (h : PolyTimeCTTReducible encA encB L B) :
    PolyTimeTruthTableReducible encA encB L B :=
  h.polyTimePTTReducible.polyTimeTruthTableReducible

/-- `P` is closed under disjunctive truth-table reductions. -/
theorem PolyTimeDTTReducible.mem_P (h : PolyTimeDTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- `P` is closed under conjunctive truth-table reductions. -/
theorem PolyTimeCTTReducible.mem_P (h : PolyTimeCTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- `P` is closed under positive truth-table reductions. -/
theorem PolyTimePTTReducible.mem_P (h : PolyTimePTTReducible encA encB L B) (hB : B ∈ P encB) :
    L ∈ P encA :=
  h.polyTimeTruthTableReducible.mem_P hB

/-- **Positive truth-table reductions compose.** -/
@[trans]
theorem PolyTimePTTReducible.trans (hLB : PolyTimePTTReducible encA encB L B)
    (hBC : PolyTimePTTReducible encB encC B C) : PolyTimePTTReducible encA encC L C :=
  polyTimePTTReducible_iff_pttReducibleBy.mpr <|
    PTTReducibleBy.trans (fun _ _ _ _ _ _ ⟨hr, hq, hd⟩ ⟨hr', hq', hd'⟩ =>
      let ⟨M, hcM, hM⟩ := exists_polyTime_truthTableComp_bound hr hq hr'
      ⟨M, hcM, by fun_prop, computableInPolyTime_truthTableCompQuery hq hq' hM,
        computableInPolyTime_truthTableCompCombiner hr hq hd hr' hd' hM⟩)
      (polyTimePTTReducible_iff_pttReducibleBy.mp hLB)
      (polyTimePTTReducible_iff_pttReducibleBy.mp hBC)

end Cslib.Complexity
