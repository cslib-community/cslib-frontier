/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Tactic.FailureNote
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public meta import Lean.Elab.Tactic

/-!
# Presburger cardinality, quorum-intersection, and pigeonhole solver for `Finset`

Distributed consensus, quorum-system, and combinatorial proofs repeatedly combine `Finset`
cardinalities with Boolean set algebra (`∅`, `Finset.univ`, `∪`, `∩`, `\`, `ᶜ`), point operations
(`{x}`, `insert`, `erase`), set relations (`⊆`, `=`, `≠`, `Disjoint`, `Finset.Nonempty`),
membership (`∈`, `∉`), `Finset.filter` subset and disjoint-fiber partitions, embedding/image size
bounds (`Finset.map`, `Finset.image`), and pigeonhole witness goals (`∃ x ∈ S, x ∉ F`,
`S.Nonempty`).

`finset_card` decides this quantifier-free Boolean Algebra with Presburger Arithmetic (BAPA)
fragment over each carrier type `α` present in the goal and hypotheses:

1. Optional bracket arguments `finset_card [d₁, h₁, …]` unfold named definitions `d₁` in the goal
   and relevant hypotheses, rewrite with quantified `=`/`↔` lemmas, and add proof hints `h₁`.
2. Existential nonemptiness and pigeonhole targets (`S.Nonempty`, `∃ x ∈ S, x ∉ T`,
   `∃ x, x ∈ S`, and `∃ x, x ∉ T` under `[Fintype α]`) reduce to strict positivity of the
   corresponding `Finset.card`.
3. Pre-pass size bridges record `(S.map emb).card = S.card`, `(S.image f).card ≤ S.card`, and
   `Fintype.card (Fin n) = n`, connecting multiple carrier types when an embedding maps between
   them.
4. For each carrier type `α`, atomic finsets are collected up to a hard cap (`maxAtoms = 5`, at
   most `32` Venn cells; points involved only in `∈`/`∉` without `≠` or `{·}`/`insert`/`erase`
   contribute zero-atom nonemptiness bounds instead of Venn atoms). Every compound Boolean
   expression and set relation reduces over a verified Venn-partition tree (`vennSum`, working both
   with `[Fintype α]` via `Finset.univ` and without `[Fintype α]` via `unionAll`) into nonnegative
   `ℕ` cell counts, harvested `Finset.filter` constraints (`filter_subset`, distinct-value fiber
   disjointness, and `Bool`/negation partitions) add zero new atoms, and `omega` closes the
   resulting linear system.

## Main definitions

* `finset_card`: close a quantifier-free `Finset` cardinality, quorum-intersection, set-relation,
  or pigeonhole goal via Venn decomposition and `omega`.
-/

public section

namespace Cslib.Tactic.FinsetCard

universe u v

/-- Syntax of compound Boolean `Finset` expressions over indexed atomic finsets and a bounding
ambient finset `top`. -/
protected inductive SetExpr : Type
  | empty : FinsetCard.SetExpr
  | top : FinsetCard.SetExpr
  | atom (idx : ℕ) : FinsetCard.SetExpr
  | union (a b : FinsetCard.SetExpr) : FinsetCard.SetExpr
  | inter (a b : FinsetCard.SetExpr) : FinsetCard.SetExpr
  | sdiff (a b : FinsetCard.SetExpr) : FinsetCard.SetExpr

/-- Truth value of `SetExpr` under an atomic membership bit-vector `bs`. -/
@[expose] protected def SetExpr.evalBool : FinsetCard.SetExpr → List Bool → Bool
  | .empty, _ => false
  | .top, _ => true
  | .atom i, bs => bs.getD i false
  | .union a b, bs => a.evalBool bs || b.evalBool bs
  | .inter a b, bs => a.evalBool bs && b.evalBool bs
  | .sdiff a b, bs => a.evalBool bs && !b.evalBool bs

/-- Concrete `Finset α` denoted by a `SetExpr` inside ambient finset `U` over atoms `as`. -/
@[expose] protected def SetExpr.denote {α : Type u} [DecidableEq α]
    (U : Finset α) (as : List (Finset α)) : FinsetCard.SetExpr → Finset α
  | .empty => ∅
  | .top => U
  | .atom i => as.getD i ∅
  | .union a b => a.denote U as ∪ b.denote U as
  | .inter a b => a.denote U as ∩ b.denote U as
  | .sdiff a b => a.denote U as \ b.denote U as

/-- Sum of Venn-cell cardinalities selected by Boolean valuation `f` under ambient finset `U` and
atomic finsets `as`. Uses `cond` so concrete `SetExpr` valuations iota-reduce cleanly. -/
@[expose] protected def vennSum {α : Type u} [DecidableEq α]
    (f : List Bool → Bool) (U : Finset α) : List (Finset α) → ℕ
  | [] => cond (f []) U.card 0
  | A :: rest =>
    FinsetCard.vennSum (fun bs => f (false :: bs)) (U \ A) rest +
    FinsetCard.vennSum (fun bs => f (true :: bs)) (U ∩ A) rest

private def regionSet {α : Type u} [DecidableEq α]
    (f : List Bool → Bool) (U : Finset α) : List (Finset α) → Finset α
  | [] => if f [] = true then U else ∅
  | A :: rest =>
    regionSet (fun bs => f (false :: bs)) (U \ A) rest ∪
    regionSet (fun bs => f (true :: bs)) (U ∩ A) rest

private theorem mem_regionSet {α : Type u} [DecidableEq α]
    (f : List Bool → Bool) (U : Finset α) (as : List (Finset α)) (x : α) :
    x ∈ regionSet f U as ↔ x ∈ U ∧ f (as.map fun A => decide (x ∈ A)) = true := by
  induction as generalizing f U with
  | nil =>
    simp only [regionSet, List.map_nil]
    cases f [] <;> simp
  | cons A rest ih =>
    simp only [regionSet, Finset.mem_union, ih, Finset.mem_sdiff, Finset.mem_inter, List.map_cons]
    by_cases hxA : x ∈ A
    · simp only [hxA, not_true_eq_false, and_false, false_and, false_or, and_true, decide_true]
    · simp only [hxA, not_false_eq_true, and_true, and_false, false_and, or_false, decide_false]

private theorem card_regionSet {α : Type u} [DecidableEq α]
    (f : List Bool → Bool) (U : Finset α) (as : List (Finset α)) :
    (regionSet f U as).card = FinsetCard.vennSum f U as := by
  induction as generalizing f U with
  | nil =>
    simp only [regionSet, FinsetCard.vennSum]
    cases f [] <;> simp
  | cons A rest ih =>
    simp only [regionSet, FinsetCard.vennSum]
    have hdisj : Disjoint
        (regionSet (fun bs => f (false :: bs)) (U \ A) rest)
        (regionSet (fun bs => f (true :: bs)) (U ∩ A) rest) := by
      rw [Finset.disjoint_left]
      intro x hx₁ hx₂
      rw [mem_regionSet, Finset.mem_sdiff] at hx₁
      rw [mem_regionSet, Finset.mem_inter] at hx₂
      exact hx₁.1.2 hx₂.1.2
    rw [Finset.card_union_of_disjoint hdisj, ih, ih]

/-- Predicate asserting every atom in `as` is a subset of ambient finset `U`. -/
protected inductive AllSubset {α : Type u} (U : Finset α) : List (Finset α) → Prop
  | nil : FinsetCard.AllSubset U []
  | cons {A : Finset α} {rest : List (Finset α)} :
      A ⊆ U → FinsetCard.AllSubset U rest → FinsetCard.AllSubset U (A :: rest)

/-- Finite bounding union of a list of finsets (used when `[Fintype α]` is unavailable). -/
@[expose] protected def unionAll {α : Type u} [DecidableEq α] : List (Finset α) → Finset α
  | [] => ∅
  | [A] => A
  | A :: B :: rest => A ∪ FinsetCard.unionAll (B :: rest)

private theorem allSubset_mono {α : Type u} {U V : Finset α} {as : List (Finset α)}
    (hUV : U ⊆ V) (h : FinsetCard.AllSubset U as) : FinsetCard.AllSubset V as := by
  induction h with
  | nil => exact .nil
  | cons hA _ ih => exact .cons (hA.trans hUV) ih

/-- Every list of finsets is contained in `Finset.univ`. -/
protected theorem allSubset_univ {α : Type u} [Fintype α] (as : List (Finset α)) :
    FinsetCard.AllSubset Finset.univ as := by
  induction as with
  | nil => exact .nil
  | cons A rest ih => exact .cons (Finset.subset_univ A) ih

/-- Every list of finsets is contained in `unionAll as`. -/
protected theorem allSubset_unionAll {α : Type u} [DecidableEq α] (as : List (Finset α)) :
    FinsetCard.AllSubset (FinsetCard.unionAll as) as := by
  induction as with
  | nil => exact .nil
  | cons A rest ih =>
    cases rest with
    | nil => exact .cons Finset.Subset.rfl .nil
    | cons B tail =>
      exact .cons Finset.subset_union_left (allSubset_mono Finset.subset_union_right ih)

private theorem mem_getD_iff {α : Type u} [DecidableEq α] {U : Finset α} {as : List (Finset α)}
    (hU : FinsetCard.AllSubset U as) (i : ℕ) (x : α) :
    x ∈ as.getD i ∅ ↔ x ∈ U ∧ (as.map fun A => decide (x ∈ A)).getD i false = true := by
  induction hU generalizing i with
  | nil =>
    simp only [List.getD_nil, Finset.notMem_empty, List.map_nil, Bool.false_eq_true, and_false]
  | @cons A rest hAU _ ih =>
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, List.map_cons, decide_eq_true_eq]
      exact ⟨fun hx => ⟨hAU hx, hx⟩, fun h => h.2⟩
    | succ j =>
      simpa only [List.getD_cons_succ, List.map_cons] using ih j

private theorem denote_eq_regionSet {α : Type u} [DecidableEq α] {U : Finset α}
    {as : List (Finset α)} (hU : FinsetCard.AllSubset U as) (e : FinsetCard.SetExpr) :
    e.denote U as = regionSet e.evalBool U as := by
  ext x
  rw [mem_regionSet]
  induction e with
  | empty =>
    simp only [SetExpr.denote, Finset.notMem_empty, SetExpr.evalBool, Bool.false_eq_true, and_false]
  | top =>
    simp only [SetExpr.denote, SetExpr.evalBool, and_true]
  | atom i =>
    exact mem_getD_iff hU i x
  | union a b iha ihb =>
    simp only [SetExpr.denote, Finset.mem_union, iha, ihb, SetExpr.evalBool, Bool.or_eq_true]
    exact ⟨fun h => h.elim (fun h₁ => ⟨h₁.1, Or.inl h₁.2⟩) (fun h₂ => ⟨h₂.1, Or.inr h₂.2⟩),
      fun ⟨hx, h⟩ => h.elim (fun h₁ => Or.inl ⟨hx, h₁⟩) (fun h₂ => Or.inr ⟨hx, h₂⟩)⟩
  | inter a b iha ihb =>
    simp only [SetExpr.denote, Finset.mem_inter, iha, ihb, SetExpr.evalBool, Bool.and_eq_true]
    exact ⟨fun ⟨⟨hx, ha⟩, _, hb⟩ => ⟨hx, ha, hb⟩, fun ⟨hx, ha, hb⟩ => ⟨⟨hx, ha⟩, hx, hb⟩⟩
  | sdiff a b iha ihb =>
    simp only [SetExpr.denote, Finset.mem_sdiff, iha, ihb, SetExpr.evalBool, Bool.and_eq_true,
      Bool.not_eq_true']
    refine ⟨fun ⟨⟨hx, ha⟩, hnb⟩ => ⟨hx, ha, ?_⟩, fun ⟨hx, ha, hb⟩ =>
      ⟨⟨hx, ha⟩, fun ⟨_, hb'⟩ => Bool.false_ne_true (hb ▸ hb')⟩⟩
    cases hb : b.evalBool (List.map (fun A => decide (x ∈ A)) as)
    · rfl
    · exact False.elim (hnb ⟨hx, hb⟩)

/-- Reflection equation expressing `(e.denote U as).card` as a Venn-cell sum. -/
protected theorem card_denote_eq {α : Type u} [DecidableEq α] {U : Finset α}
    {as : List (Finset α)} (hU : FinsetCard.AllSubset U as) (e : FinsetCard.SetExpr) :
    (e.denote U as).card = FinsetCard.vennSum e.evalBool U as := by
  rw [denote_eq_regionSet hU e, card_regionSet]

/-- Reflection equation expressing `Fintype.card α` as the sum of Venn cells of `Finset.univ`. -/
protected theorem card_univ_eq_vennSum {α : Type u} (ft₁ ft₂ : Fintype α)
    [DecidableEq α] (as : List (Finset α)) :
    @Fintype.card α ft₁ =
      FinsetCard.vennSum (fun _ => true) (@Finset.univ α ft₂) as := by
  cases Subsingleton.elim ft₁ ft₂
  rw [← @Finset.card_univ α ft₁]
  exact FinsetCard.card_denote_eq (@FinsetCard.allSubset_univ α ft₁ as) .top

private theorem regionSet_eq_empty_iff {α : Type u} [DecidableEq α]
    (f : List Bool → Bool) (U : Finset α) (as : List (Finset α)) :
    regionSet f U as = ∅ ↔ FinsetCard.vennSum f U as = 0 := by
  rw [← Finset.card_eq_zero, card_regionSet]

/-- Translate `s ⊆ t` into `vennSum (s \ t) = 0`. -/
protected theorem subset_denote_mp {α : Type u} [DecidableEq α] {U : Finset α}
    {as : List (Finset α)} (hU : FinsetCard.AllSubset U as) {e₁ e₂ : FinsetCard.SetExpr}
    {s t : Finset α} (hs : s = e₁.denote U as) (ht : t = e₂.denote U as) (h : s ⊆ t) :
    FinsetCard.vennSum (fun bs => e₁.evalBool bs && !e₂.evalBool bs) U as = 0 := by
  subst hs ht
  have hemp : (e₁.sdiff e₂).denote U as = ∅ := Finset.sdiff_eq_empty_iff_subset.2 h
  rw [denote_eq_regionSet hU] at hemp
  exact (regionSet_eq_empty_iff _ U as).1 hemp

/-- Translate `Disjoint s t` into `vennSum (s ∩ t) = 0`. -/
protected theorem disjoint_denote_mp {α : Type u} [DecidableEq α] {U : Finset α}
    {as : List (Finset α)} (hU : FinsetCard.AllSubset U as) {e₁ e₂ : FinsetCard.SetExpr}
    {s t : Finset α} (hs : s = e₁.denote U as) (ht : t = e₂.denote U as) (h : Disjoint s t) :
    FinsetCard.vennSum (fun bs => e₁.evalBool bs && e₂.evalBool bs) U as = 0 := by
  subst hs ht
  have hemp : (e₁.inter e₂).denote U as = ∅ := Finset.disjoint_iff_inter_eq_empty.1 h
  rw [denote_eq_regionSet hU] at hemp
  exact (regionSet_eq_empty_iff _ U as).1 hemp

/-- Translate `¬ Disjoint s t` into `0 < vennSum (s ∩ t)`. -/
protected theorem not_disjoint_denote_mp {α : Type u} [DecidableEq α] {U : Finset α}
    {as : List (Finset α)} (hU : FinsetCard.AllSubset U as) {e₁ e₂ : FinsetCard.SetExpr}
    {s t : Finset α} (hs : s = e₁.denote U as) (ht : t = e₂.denote U as) (h : ¬ Disjoint s t) :
    0 < FinsetCard.vennSum (fun bs => e₁.evalBool bs && e₂.evalBool bs) U as := by
  subst hs ht
  refine Nat.pos_of_ne_zero fun h0 => h ?_
  have hemp : (e₁.inter e₂).denote U as = ∅ := by
    rw [denote_eq_regionSet hU]
    exact (regionSet_eq_empty_iff _ U as).2 h0
  exact Finset.disjoint_iff_inter_eq_empty.2 hemp

/-- Translate `s = t` into `vennSum (s ∆ t) = 0`. -/
protected theorem eq_denote_mp {α : Type u} [DecidableEq α] {U : Finset α}
    {as : List (Finset α)} (hU : FinsetCard.AllSubset U as) {e₁ e₂ : FinsetCard.SetExpr}
    {s t : Finset α} (hs : s = e₁.denote U as) (ht : t = e₂.denote U as) (h : s = t) :
    FinsetCard.vennSum (fun bs => e₁.evalBool bs != e₂.evalBool bs) U as = 0 := by
  subst hs ht
  rw [← regionSet_eq_empty_iff]
  ext x
  simp only [mem_regionSet, Finset.notMem_empty, iff_false, not_and]
  intro hx hne
  have heq : x ∈ e₁.denote U as ↔ x ∈ e₂.denote U as := by rw [h]
  rw [denote_eq_regionSet hU, denote_eq_regionSet hU, mem_regionSet, mem_regionSet] at heq
  cases hb₁ : e₁.evalBool (List.map (fun A => decide (x ∈ A)) as) <;>
    cases hb₂ : e₂.evalBool (List.map (fun A => decide (x ∈ A)) as)
  · rw [hb₁, hb₂] at hne; exact Bool.false_ne_true hne
  · exact Bool.false_ne_true (hb₁ ▸ (heq.2 ⟨hx, hb₂⟩).2)
  · exact Bool.false_ne_true (hb₂ ▸ (heq.1 ⟨hx, hb₁⟩).2)
  · rw [hb₁, hb₂] at hne; exact Bool.false_ne_true hne

/-- Translate `s ≠ t` into `0 < vennSum (s ∆ t)`. -/
protected theorem ne_denote_mp {α : Type u} [DecidableEq α] {U : Finset α}
    {as : List (Finset α)} (hU : FinsetCard.AllSubset U as) {e₁ e₂ : FinsetCard.SetExpr}
    {s t : Finset α} (hs : s = e₁.denote U as) (ht : t = e₂.denote U as) (h : s ≠ t) :
    0 < FinsetCard.vennSum (fun bs => e₁.evalBool bs != e₂.evalBool bs) U as := by
  subst hs ht
  refine Nat.pos_of_ne_zero fun h0 => h ?_
  have hemp := (regionSet_eq_empty_iff (fun bs => e₁.evalBool bs != e₂.evalBool bs) U as).2 h0
  rw [denote_eq_regionSet hU, denote_eq_regionSet hU]
  ext x
  simp only [mem_regionSet]
  refine and_congr_right fun hx => ?_
  have hx0 : x ∉ regionSet (fun bs => e₁.evalBool bs != e₂.evalBool bs) U as :=
    hemp ▸ Finset.notMem_empty x
  simp only [mem_regionSet, hx, true_and, bne_eq_false_iff_eq, Bool.not_eq_true] at hx0
  rw [hx0]

/-! ### Instance-insensitive `SetExpr` normalization bridges -/

/-- Coherence of `Finset.univ` across any two `Fintype α` instances. -/
protected theorem univ_eq {α : Type u} (ft₁ ft₂ : Fintype α) :
    @Finset.univ α ft₁ = @Finset.univ α ft₂ := by
  cases Subsingleton.elim ft₁ ft₂; rfl

/-- Coherence of `∪` (`Max.max`) across any two `DecidableEq α` instances. -/
protected theorem union_eq_of_eq {α : Type u} (d₁ d₂ : DecidableEq α)
    {s₁ s₂ t₁ t₂ : Finset α} (hs : s₁ = t₁) (ht : s₂ = t₂) :
    @Max.max (Finset α) (@Finset.instMax α d₁) s₁ s₂ =
      @Max.max (Finset α) (@Finset.instMax α d₂) t₁ t₂ := by
  cases Subsingleton.elim d₁ d₂; subst hs ht; rfl

/-- Coherence of `∩` (`Min.min`) across any two `DecidableEq α` instances. -/
protected theorem inter_eq_of_eq {α : Type u} (d₁ d₂ : DecidableEq α)
    {s₁ s₂ t₁ t₂ : Finset α} (hs : s₁ = t₁) (ht : s₂ = t₂) :
    @Min.min (Finset α) (@Finset.instMin α d₁) s₁ s₂ =
      @Min.min (Finset α) (@Finset.instMin α d₂) t₁ t₂ := by
  cases Subsingleton.elim d₁ d₂; subst hs ht; rfl

/-- Coherence of `\` (`SDiff.sdiff`) across any two `DecidableEq α` instances. -/
protected theorem sdiff_eq_of_eq {α : Type u} (d₁ d₂ : DecidableEq α)
    {s₁ s₂ t₁ t₂ : Finset α} (hs : s₁ = t₁) (ht : s₂ = t₂) :
    @SDiff.sdiff (Finset α) (@Finset.instSDiff α d₁) s₁ s₂ =
      @SDiff.sdiff (Finset α) (@Finset.instSDiff α d₂) t₁ t₂ := by
  cases Subsingleton.elim d₁ d₂; subst hs ht; rfl

/-- Rewrite `sᶜ` to `Finset.univ \ t` across any `Fintype` and `DecidableEq` instances. -/
protected theorem compl_eq_sdiff_univ_of_eq {α : Type u} (ft₁ ft₂ : Fintype α)
    (d₁ d₂ : DecidableEq α) {s t : Finset α} (hs : s = t) :
    @Compl.compl (Finset α) (@BooleanAlgebra.toCompl (Finset α) (@Finset.booleanAlgebra α ft₁ d₁))
        s =
      @SDiff.sdiff (Finset α) (@Finset.instSDiff α d₂) (@Finset.univ α ft₂) t := by
  cases Subsingleton.elim ft₁ ft₂
  cases Subsingleton.elim d₁ d₂
  subst hs
  exact @Finset.compl_eq_univ_sdiff α ft₁ d₁ s

/-- Rewrite `insert x s` to `{x} ∪ t` across any two `DecidableEq α` instances. -/
protected theorem insert_eq_union_of_eq {α : Type u} (d₁ d₂ : DecidableEq α)
    (x : α) {s t : Finset α} (hs : s = t) :
    @Insert.insert α (Finset α) (@Finset.instInsert α d₁) x s =
      @Max.max (Finset α) (@Finset.instMax α d₂) ({x} : Finset α) t := by
  cases Subsingleton.elim d₁ d₂; subst hs; exact @Finset.insert_eq α d₁ x s

/-- Rewrite `s.erase x` to `t \ {x}` across any two `DecidableEq α` instances. -/
protected theorem erase_eq_sdiff_of_eq {α : Type u} (d₁ d₂ : DecidableEq α)
    {s t : Finset α} (x : α) (hs : s = t) :
    @Finset.erase α d₁ s x =
      @SDiff.sdiff (Finset α) (@Finset.instSDiff α d₂) t ({x} : Finset α) := by
  cases Subsingleton.elim d₁ d₂; subst hs; exact @Finset.erase_eq α d₁ s x

/-! ### Pigeonhole and `Finset.filter` structural lemmas -/

/-- Witness `∃ x ∈ s, x ∉ t` from `0 < (s \ t).card`. -/
protected theorem exists_mem_notMem_of_card_sdiff_pos {α : Type u} [DecidableEq α]
    {s t : Finset α} (h : 0 < (s \ t).card) : ∃ x ∈ s, x ∉ t := by
  obtain ⟨x, hx⟩ := Finset.card_pos.1 h
  exact ⟨x, (Finset.mem_sdiff.1 hx).1, (Finset.mem_sdiff.1 hx).2⟩

/-- Witness `∃ x, x ∉ t` from `0 < (Finset.univ \ t).card`. -/
protected theorem exists_notMem_of_card_sdiff_univ_pos {α : Type u} [Fintype α] [DecidableEq α]
    {t : Finset α} (h : 0 < (Finset.univ \ t).card) : ∃ x, x ∉ t := by
  obtain ⟨x, _, hxt⟩ := FinsetCard.exists_mem_notMem_of_card_sdiff_pos h
  exact ⟨x, hxt⟩

/-- Distinct fibers `s₁.filter (f · = v₁)` and `s₂.filter (f · = v₂)` are disjoint
when `v₁ ≠ v₂`. -/
protected theorem disjoint_filter_eq_of_ne {α : Type u} {β : Type v}
    {s₁ s₂ : Finset α} (f : α → β) {v₁ v₂ : β}
    [d₁ : DecidablePred fun x => f x = v₁] [d₂ : DecidablePred fun x => f x = v₂]
    (hne : v₁ ≠ v₂) :
    Disjoint (@Finset.filter α (fun x => f x = v₁) d₁ s₁)
      (@Finset.filter α (fun x => f x = v₂) d₂ s₂) :=
  Finset.disjoint_iff_ne.2 fun _ hx _ hy hxy =>
    hne (((Finset.mem_filter.1 hx).2).symm.trans (hxy ▸ (Finset.mem_filter.1 hy).2))

/-- Boolean fibers `f x = true` and `f x = false` partition `s`. -/
protected theorem filter_eq_true_union_filter_eq_false {α : Type u} [DecidableEq α]
    (s : Finset α) (f : α → Bool)
    [d₁ : DecidablePred fun x => f x = true] [d₂ : DecidablePred fun x => f x = false] :
    @Finset.filter α (fun x => f x = true) d₁ s ∪
      @Finset.filter α (fun x => f x = false) d₂ s = s := by
  ext x
  simp only [Finset.mem_union, Finset.mem_filter]
  cases f x <;> simp

end Cslib.Tactic.FinsetCard

end

public meta section

namespace Cslib.Tactic.FinsetCard

open Lean Meta Elab Tactic

/-- Hard upper bound on atomic finsets per carrier type (`2 ^ 5 = 32` Venn cells). -/
private def maxAtoms : ℕ := 5

/-- Meta-phase evaluator mirroring `FinsetCard.SetExpr.evalBool`. -/
private def evalBoolMeta : FinsetCard.SetExpr → List Bool → Bool
  | .empty, _ => false
  | .top, _ => true
  | .atom i, bs => bs.getD i false
  | .union a b, bs => evalBoolMeta a bs || evalBoolMeta b bs
  | .inter a b, bs => evalBoolMeta a bs && evalBoolMeta b bs
  | .sdiff a b, bs => evalBoolMeta a bs && !evalBoolMeta b bs

/-- Extract `α` when `ty` is syntactically `Finset α`. -/
private def finsetCarrier? (ty : Expr) : Option (Expr × Level) :=
  let ty := ty.cleanupAnnotations
  if ty.isAppOfArity ``Finset 1 then
    match ty.getAppFn with
    | .const _ [u] => some (ty.appArg!, u)
    | _ => none
  else none

/-- Check whether `e` is a compound Boolean or structural `Finset` constructor worth peeking
through a local `let`/`set` binding. -/
private def isStructuredFinsetVal (e : Expr) : Bool :=
  let e := e.cleanupAnnotations
  match e.getAppFn.constName? with
  | some n =>
    n == ``EmptyCollection.emptyCollection || n == ``Bot.bot ||
    n == ``Finset.univ || n == ``Top.top ||
    n == ``Max.max || n == ``Union.union ||
    n == ``Min.min || n == ``Inter.inter ||
    n == ``SDiff.sdiff || n == ``Compl.compl ||
    n == ``Insert.insert || n == ``Finset.erase || n == ``Singleton.singleton ||
    n == ``Finset.filter || n == ``Finset.map || n == ``Finset.image
  | none => false

/-- Peel structure projections and local `let`/`set` bindings (including applied `let`-bound
functions) whose value is a compound or structural `Finset` expression defeq to `e`. -/
private partial def peekFinsetLet (e : Expr) (fuel : ℕ := 8) : MetaM Expr := do
  if fuel == 0 then return e
  let e' := e.cleanupAnnotations
  if e'.isProj then
    let red ← whnfCore e'
    if red != e' then
      return ← peekFinsetLet red (fuel - 1)
  if let .fvar id := e'.getAppFn then
    if let some val ← id.getValue? then
      let val := (← instantiateMVars val).beta e'.getAppArgs
      if isStructuredFinsetVal val then
        return ← peekFinsetLet val (fuel - 1)
  return e

/-- Relational fact over `Finset α` harvested from the local context. -/
private inductive SetRelFact
  | subset (s t pf : Expr)
  | disjoint (s t pf : Expr)
  | notDisjoint (s t pf : Expr)
  | eq (s t pf : Expr)
  | ne (s t pf : Expr)

/-- Membership or point-disequality fact over `α` harvested from the local context. -/
private inductive PointFact
  | mem (x s pf : Expr)
  | notMem (x s pf : Expr)
  | ne (x y pf : Expr)

/-- Collected BAPA problem data for one carrier type `α`. -/
private structure CarrierData where
  α : Expr
  u : Level
  cardTerms : Array Expr := #[]
  fintypeCards : Array (Expr × Expr) := #[]
  setRels : Array SetRelFact := #[]
  pointFacts : Array PointFact := #[]

private instance : Inhabited CarrierData :=
  ⟨⟨default, .zero, #[], #[], #[], #[]⟩⟩

private def findOrInsertCarrier (carriers : Array CarrierData) (α : Expr) (u : Level) :
    MetaM (Array CarrierData × ℕ) := do
  for i in [:carriers.size] do
    if ← withReducible (isDefEq carriers[i]!.α α) then
      return (carriers, i)
  return (carriers.push { α, u }, carriers.size)

private def pushUniqueExpr (arr : Array Expr) (e : Expr) : Array Expr :=
  if arr.any (· == e) then arr else arr.push e

/-- Construct `{x} : Finset α`. -/
private def mkSingletonFinset (α : Expr) (u : Level) (x : Expr) : Expr :=
  mkApp4 (mkConst ``Singleton.singleton [u, u]) α (mkApp (mkConst ``Finset [u]) α)
    (mkApp (mkConst ``Finset.instSingleton [u]) α) x

/-- Look up an exact proof of `prop` (or symmetric `=`, `≠`) in the local context. -/
private def findExactLocal? (prop : Expr) : MetaM (Option Expr) := do
  let prop ← instantiateMVars prop
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    if ← withReducible (isDefEq t prop) then return some d.toExpr
  if prop.isAppOfArity ``Ne 3 then
    let args := prop.getAppArgs
    let sym := mkApp3 prop.getAppFn args[0]! args[2]! args[1]!
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if ← withReducible (isDefEq (← instantiateMVars d.type) sym) then
        return some (← mkAppM ``Ne.symm #[d.toExpr])
    let notEq1 := mkApp (mkConst ``Not) (mkApp3 (mkConst ``Eq prop.getAppFn.constLevels!)
      args[0]! args[1]! args[2]!)
    let notEq2 := mkApp (mkConst ``Not) (mkApp3 (mkConst ``Eq prop.getAppFn.constLevels!)
      args[0]! args[2]! args[1]!)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← instantiateMVars d.type
      if ← withReducible (isDefEq t notEq1) then return some d.toExpr
      if ← withReducible (isDefEq t notEq2) then return some (← mkAppM ``Ne.symm #[d.toExpr])
  return none

/-- Prove `v₁ ≠ v₂` cheaply via local hypothesis lookup, `decide` on ground terms, or a bounded
`omega` probe on `Nat`/`Int`/`Fin`. -/
private def proveNeFast? (β v₁ v₂ : Expr) : MetaM (Option Expr) := do
  if v₁ == v₂ then return none
  let neProp ← mkAppOptM ``Ne #[some β, some v₁, some v₂]
  if let some h ← findExactLocal? neProp then return some h
  if !neProp.hasFVar && !neProp.hasMVar then
    let saved ← saveState
    try return some (← mkDecideProof neProp) catch _ => saved.restore
  let βc := β.cleanupAnnotations
  if βc.isConstOf ``Nat || βc.isConstOf ``Int || βc.isAppOfArity ``Fin 1 then
    let hyps ← (← getLCtx).foldlM (init := #[]) fun acc d => do
      if d.isImplementationDetail then return acc
      if ← isProp d.type then return acc.push d.toExpr else return acc
    let saved ← saveState
    let attempt : MetaM (Option Expr) :=
      withCurrHeartbeats <|
        withTheReader Core.Context (fun c => { c with maxHeartbeats := 50000 }) do
          let g ← mkFreshExprSyntheticOpaqueMVar neProp
          let some g' ← g.mvarId!.falseOrByContra | return none
          let ok ← g'.withContext do
            let some neg := (← getLCtx).lastDecl | return false
            Lean.Elab.Tactic.Omega.omega (neg.toExpr :: hyps.toList) g'
            return true
          if ok then return some (← instantiateMVars g) else return none
    return ← tryCatchRuntimeEx attempt fun _ => do saved.restore; return none
  return none

/-- Build the exact `Nat` expression to which `FinsetCard.vennSum f U atoms` iota-reduces. -/
private def mkVennSumExpr (α : Expr) (u : Level) (decEq : Expr)
    (evalFn : List Bool → Bool) (U : Expr) : List Expr → Expr
  | [] =>
    if evalFn [] then mkApp2 (mkConst ``Finset.card [u]) α U
    else mkNatLit 0
  | A :: rest =>
    let finsetTy := mkApp (mkConst ``Finset [u]) α
    let sdiffUA := mkApp4 (mkConst ``SDiff.sdiff [u]) finsetTy
      (mkApp2 (mkConst ``Finset.instSDiff [u]) α decEq) U A
    let interUA := mkApp4 (mkConst ``Min.min [u]) finsetTy
      (mkApp2 (mkConst ``Finset.instMin [u]) α decEq) U A
    mkNatAdd
      (mkVennSumExpr α u decEq (fun bs => evalFn (false :: bs)) sdiffUA rest)
      (mkVennSumExpr α u decEq (fun bs => evalFn (true :: bs)) interUA rest)

/-- Build a Lean `Expr` representing a `FinsetCard.SetExpr` value. -/
private def reflectSetExpr : FinsetCard.SetExpr → Expr
  | .empty => mkConst ``FinsetCard.SetExpr.empty
  | .top => mkConst ``FinsetCard.SetExpr.top
  | .atom i => mkApp (mkConst ``FinsetCard.SetExpr.atom) (mkNatLit i)
  | .union a b => mkApp2 (mkConst ``FinsetCard.SetExpr.union) (reflectSetExpr a) (reflectSetExpr b)
  | .inter a b => mkApp2 (mkConst ``FinsetCard.SetExpr.inter) (reflectSetExpr a) (reflectSetExpr b)
  | .sdiff a b => mkApp2 (mkConst ``FinsetCard.SetExpr.sdiff) (reflectSetExpr a) (reflectSetExpr b)

/-- Build a Lean `List (Finset α)` expression from `atoms`. -/
private def mkFinsetListExpr (α : Expr) (u : Level) (atoms : List Expr) : Expr :=
  let elemTy := mkApp (mkConst ``Finset [u]) α
  atoms.foldr (fun a acc => mkApp3 (mkConst ``List.cons [u]) elemTy a acc)
    (mkApp (mkConst ``List.nil [u]) elemTy)

/-- Parse a `Finset α` expression into `(se : SetExpr, eqProof? : Option Expr)` where `eqProof?`
proves `rawS = se.denote U atoms` (`none` means definitionally equal). When `allowNewAtoms` is
`false`, refuses to allocate new atoms. -/
private partial def parseSetExpr (α : Expr) (u : Level) (decEq : Expr) (fintype? : Option Expr)
    (allowNewAtoms : Bool) (atomsRef : IO.Ref (Array Expr)) (s : Expr) :
    MetaM (Option (FinsetCard.SetExpr × Option Expr)) := do
  let sPeel ← peekFinsetLet s
  let sClean := sPeel.cleanupAnnotations
  let fn := sClean.getAppFn
  let args := sClean.getAppArgs
  if (fn.isConstOf ``EmptyCollection.emptyCollection || fn.isConstOf ``Bot.bot) &&
      args.size == 2 then
    return some (.empty, none)
  if fn.isConstOf ``Finset.univ && args.size == 2 then
    if let some ft := fintype? then
      let rawFt := args[1]!
      let pf? ← if ← isDefEq rawFt ft then pure none else
        some <$> mkAppOptM ``FinsetCard.univ_eq #[some α, some rawFt, some ft]
      return some (.top, pf?)
  let parseBinOp (ctor : FinsetCard.SetExpr → FinsetCard.SetExpr → FinsetCard.SetExpr)
      (instName thmName : Name) : MetaM (Option (FinsetCard.SetExpr × Option Expr)) := do
    let rawInst := args[1]!; let s₁ := args[2]!; let s₂ := args[3]!
    let some (e₁, p₁?) ← parseSetExpr α u decEq fintype? allowNewAtoms atomsRef s₁ | return none
    let some (e₂, p₂?) ← parseSetExpr α u decEq fintype? allowNewAtoms atomsRef s₂ | return none
    if p₁?.isNone && p₂?.isNone &&
        (← isDefEq rawInst (mkApp2 (mkConst instName [u]) α decEq)) then
      return some (ctor e₁ e₂, none)
    let d₁ := if rawInst.getAppNumArgs ≥ 2 then rawInst.appArg! else decEq
    let p₁ ← match p₁? with | some p => pure p | none => mkEqRefl s₁
    let p₂ ← match p₂? with | some p => pure p | none => mkEqRefl s₂
    let pf ← mkAppOptM thmName
      #[some α, some d₁, some decEq, some s₁, some s₂, none, none, some p₁, some p₂]
    return some (ctor e₁ e₂, some pf)
  if (fn.isConstOf ``Max.max || fn.isConstOf ``Union.union) && args.size == 4 then
    return ← parseBinOp .union ``Finset.instMax ``FinsetCard.union_eq_of_eq
  if (fn.isConstOf ``Min.min || fn.isConstOf ``Inter.inter) && args.size == 4 then
    return ← parseBinOp .inter ``Finset.instMin ``FinsetCard.inter_eq_of_eq
  if fn.isConstOf ``SDiff.sdiff && args.size == 4 then
    return ← parseBinOp .sdiff ``Finset.instSDiff ``FinsetCard.sdiff_eq_of_eq
  if fn.isConstOf ``Compl.compl && args.size == 3 then
    if let some ft := fintype? then
      let s₁ := args[2]!
      let some (e₁, p₁?) ← parseSetExpr α u decEq fintype? allowNewAtoms atomsRef s₁ | return none
      let baArgs := args[1]!.appArg!.getAppArgs
      if baArgs.size == 3 then
        let p₁ ← match p₁? with | some p => pure p | none => mkEqRefl s₁
        let pf ← mkAppOptM ``FinsetCard.compl_eq_sdiff_univ_of_eq
          #[some α, some baArgs[1]!, some ft, some baArgs[2]!, some decEq, some s₁, none, some p₁]
        return some (.sdiff .top e₁, some pf)
  if fn.isConstOf ``Insert.insert && args.size == 5 then
    let rawInsInst := args[2]!; let x := args[3]!; let s₁ := args[4]!
    let sing := mkSingletonFinset α u x
    let some (eSing, _) ← parseSetExpr α u decEq fintype? allowNewAtoms atomsRef sing | return none
    let some (e₁, p₁?) ← parseSetExpr α u decEq fintype? allowNewAtoms atomsRef s₁ | return none
    let d₁ := if rawInsInst.getAppNumArgs ≥ 2 then rawInsInst.appArg! else decEq
    let p₁ ← match p₁? with | some p => pure p | none => mkEqRefl s₁
    let pf ← mkAppOptM ``FinsetCard.insert_eq_union_of_eq
      #[some α, some d₁, some decEq, some x, some s₁, none, some p₁]
    return some (.union eSing e₁, some pf)
  if fn.isConstOf ``Finset.erase && args.size == 4 then
    let d₁ := args[1]!; let s₁ := args[2]!; let x := args[3]!
    let sing := mkSingletonFinset α u x
    let some (eSing, _) ← parseSetExpr α u decEq fintype? allowNewAtoms atomsRef sing | return none
    let some (e₁, p₁?) ← parseSetExpr α u decEq fintype? allowNewAtoms atomsRef s₁ | return none
    let p₁ ← match p₁? with | some p => pure p | none => mkEqRefl s₁
    let pf ← mkAppOptM ``FinsetCard.erase_eq_sdiff_of_eq
      #[some α, some d₁, some decEq, some s₁, none, some x, some p₁]
    return some (.sdiff e₁ eSing, some pf)
  let atoms ← atomsRef.get
  for i in [:atoms.size] do
    if atoms[i]! == sPeel || (← withReducible (isDefEq atoms[i]! sPeel)) then
      return some (.atom i, none)
  if !allowNewAtoms then return none
  atomsRef.set (atoms.push sPeel)
  return some (.atom atoms.size, none)

/-- Recursively scan a `Finset` expression `s` for `Finset.map` and `Finset.image` leaves, linking
their cardinalities across carriers. -/
private partial def scanSetExprForMapImg (s : Expr)
    (ref : IO.Ref (Array CarrierData)) (mapImgRef : IO.Ref (Array (Expr × Expr))) :
    MetaM Unit := do
  let sPeel ← peekFinsetLet s
  let sc := sPeel.cleanupAnnotations
  let sFn := sc.getAppFn
  let sArgs := sc.getAppArgs
  if (sFn.isConstOf ``Max.max || sFn.isConstOf ``Union.union ||
      sFn.isConstOf ``Min.min || sFn.isConstOf ``Inter.inter ||
      sFn.isConstOf ``SDiff.sdiff) && sArgs.size == 4 then
    scanSetExprForMapImg sArgs[2]! ref mapImgRef
    scanSetExprForMapImg sArgs[3]! ref mapImgRef
  else if sFn.isConstOf ``Compl.compl && sArgs.size == 3 then
    scanSetExprForMapImg sArgs[2]! ref mapImgRef
  else if sFn.isConstOf ``Insert.insert && sArgs.size == 5 then
    scanSetExprForMapImg sArgs[4]! ref mapImgRef
  else if sFn.isConstOf ``Finset.erase && sArgs.size == 4 then
    scanSetExprForMapImg sArgs[2]! ref mapImgRef
  else if sFn.isConstOf ``Finset.map && sArgs.size == 4 then
    let αSrc := sArgs[0]!; let αDst := sArgs[1]!
    let uSrc := sFn.constLevels![0]!; let uDst := sFn.constLevels![1]!
    let src := sArgs[3]!
    let pf := mkApp4 (mkConst ``Finset.card_map sFn.constLevels!) αSrc αDst src sArgs[2]!
    let cur ← mapImgRef.get
    unless cur.any (fun (x, _) => x == sPeel) do
      mapImgRef.set (cur.push (sPeel, pf))
    let (cs₁, i₁) ← findOrInsertCarrier (← ref.get) αDst uDst
    ref.set (cs₁.set! i₁ { cs₁[i₁]! with cardTerms := pushUniqueExpr cs₁[i₁]!.cardTerms sPeel })
    let (cs₂, i₂) ← findOrInsertCarrier (← ref.get) αSrc uSrc
    ref.set (cs₂.set! i₂ { cs₂[i₂]! with cardTerms := pushUniqueExpr cs₂[i₂]!.cardTerms src })
    scanSetExprForMapImg src ref mapImgRef
  else if sFn.isConstOf ``Finset.image && sArgs.size == 5 then
    let αSrc := sArgs[0]!; let αDst := sArgs[1]!
    let uSrc := sFn.constLevels![0]!; let uDst := sFn.constLevels![1]!
    let src := sArgs[4]!
    let pf := mkApp5 (mkConst ``Finset.card_image_le sFn.constLevels!)
      αSrc αDst src sArgs[3]! sArgs[2]!
    let cur ← mapImgRef.get
    unless cur.any (fun (x, _) => x == sPeel) do
      mapImgRef.set (cur.push (sPeel, pf))
    let (cs₁, i₁) ← findOrInsertCarrier (← ref.get) αDst uDst
    ref.set (cs₁.set! i₁ { cs₁[i₁]! with cardTerms := pushUniqueExpr cs₁[i₁]!.cardTerms sPeel })
    let (cs₂, i₂) ← findOrInsertCarrier (← ref.get) αSrc uSrc
    ref.set (cs₂.set! i₂ { cs₂[i₂]! with cardTerms := pushUniqueExpr cs₂[i₂]!.cardTerms src })
    scanSetExprForMapImg src ref mapImgRef

/-- Collect all closed `Finset.card s` and `Fintype.card α` subterms appearing inside `e`
without opening universal quantifiers or lambdas. -/
private partial def collectCardSubterms (e : Expr)
    (ref : IO.Ref (Array CarrierData)) (mapImgRef : IO.Ref (Array (Expr × Expr))) :
    MetaM Unit := do
  let rec visit (sub : Expr) : MetaM Unit := do
    if sub.hasLooseBVars then return
    let fn := sub.getAppFn
    let args := sub.getAppArgs
    if fn.isConstOf ``Finset.card && args.size == 2 then
      let α := args[0]!; let u := fn.constLevels![0]!; let s := args[1]!
      let (cs, idx) ← findOrInsertCarrier (← ref.get) α u
      let cd := cs[idx]!
      ref.set (cs.set! idx { cd with cardTerms := pushUniqueExpr cd.cardTerms s })
      scanSetExprForMapImg s ref mapImgRef
    else if fn.isConstOf ``Fintype.card && args.size == 2 then
      let α := args[0]!; let u := fn.constLevels![0]!; let ft := args[1]!
      let (cs, idx) ← findOrInsertCarrier (← ref.get) α u
      let cd := cs[idx]!
      let cd' := if cd.fintypeCards.any (fun (x, _) => x == sub) then cd
        else { cd with fintypeCards := cd.fintypeCards.push (sub, ft) }
      ref.set (cs.set! idx cd')
    match sub with
    | .app f a => visit f; visit a
    | .letE _ t v b _ => visit t; visit v; if !b.hasLooseBVars then visit b
    | .forallE _ d b _ => visit d; if !b.hasLooseBVars then visit b
    | .mdata _ inner => visit inner
    | .proj _ _ inner => visit inner
    | _ => pure ()
  visit e

/-- Harvest relational `Finset` and point facts from a hypothesis `(ty, pf)`. -/
private partial def harvestHyp (ty pf : Expr)
    (ref : IO.Ref (Array CarrierData)) (mapImgRef : IO.Ref (Array (Expr × Expr)))
    (depth : ℕ := 8) : MetaM Unit := do
  let ty ← instantiateMVars ty
  collectCardSubterms ty ref mapImgRef
  let t := ty.cleanupAnnotations
  if depth > 0 && t.isAppOfArity ``And 2 then
    let args := t.getAppArgs
    harvestHyp args[0]! (← mkAppM ``And.left #[pf]) ref mapImgRef (depth - 1)
    harvestHyp args[1]! (← mkAppM ``And.right #[pf]) ref mapImgRef (depth - 1)
    return
  let addRel (α : Expr) (u : Level) (r : SetRelFact) : MetaM Unit := do
    let (cs, idx) ← findOrInsertCarrier (← ref.get) α u
    let cd := cs[idx]!
    ref.set (cs.set! idx { cd with setRels := cd.setRels.push r })
    let (s, dst) := match r with
      | .subset a b _ | .disjoint a b _ | .notDisjoint a b _ | .eq a b _ | .ne a b _ => (a, b)
    scanSetExprForMapImg s ref mapImgRef
    scanSetExprForMapImg dst ref mapImgRef
  let addPt (α : Expr) (u : Level) (p : PointFact) : MetaM Unit := do
    let (cs, idx) ← findOrInsertCarrier (← ref.get) α u
    let cd := cs[idx]!
    ref.set (cs.set! idx { cd with pointFacts := cd.pointFacts.push p })
  if t.isAppOfArity ``Not 1 then
    let inner := t.appArg!.cleanupAnnotations
    let fn := inner.getAppFn
    let args := inner.getAppArgs
    if fn.isConstOf ``Disjoint && args.size == 5 then
      if let some (α, u) := finsetCarrier? args[0]! then
        addRel α u (.notDisjoint args[3]! args[4]! pf); return
    if fn.isConstOf ``Eq && args.size == 3 then
      if let some (α, u) := finsetCarrier? args[0]! then
        addRel α u (.ne args[1]! args[2]! pf); return
      if let .sort (.succ u) ← whnf (← inferType args[0]!) then
        if !(← isProp args[0]!) && !args[0]!.cleanupAnnotations.isConstOf ``Nat &&
            !args[0]!.cleanupAnnotations.isConstOf ``Int then
          addPt args[0]! u (.ne args[1]! args[2]! pf); return
    if fn.isConstOf ``Membership.mem && args.size == 5 then
      if let some (α, u) := finsetCarrier? args[1]! then
        addPt α u (.notMem args[4]! args[3]! pf); return
    return
  let fn := t.getAppFn
  let args := t.getAppArgs
  if (fn.isConstOf ``LE.le || fn.isConstOf ``HasSubset.Subset) && args.size == 4 then
    if let some (α, u) := finsetCarrier? args[0]! then
      addRel α u (.subset args[2]! args[3]! pf); return
  if fn.isConstOf ``Disjoint && args.size == 5 then
    if let some (α, u) := finsetCarrier? args[0]! then
      addRel α u (.disjoint args[3]! args[4]! pf); return
  if fn.isConstOf ``Finset.Nonempty && args.size == 2 && depth > 0 then
    let α := args[0]!; let u := fn.constLevels![0]!; let s := args[1]!
    let neEmpPf ← mkAppOptM ``Iff.mpr
      #[none, none, some (mkApp2 (mkConst ``Finset.ne_empty_iff_nonempty [u]) α s), some pf]
    harvestHyp (← inferType neEmpPf) neEmpPf ref mapImgRef (depth - 1); return
  if fn.isConstOf ``Membership.mem && args.size == 5 then
    if let some (α, u) := finsetCarrier? args[1]! then
      addPt α u (.mem args[4]! args[3]! pf); return
  if fn.isConstOf ``Eq && args.size == 3 then
    if let some (α, u) := finsetCarrier? args[0]! then
      addRel α u (.eq args[1]! args[2]! pf); return
  if fn.isConstOf ``Ne && args.size == 3 then
    if let some (α, u) := finsetCarrier? args[0]! then
      addRel α u (.ne args[1]! args[2]! pf); return
    if let .sort (.succ u) ← whnf (← inferType args[0]!) then
      if !(← isProp args[0]!) && !args[0]!.cleanupAnnotations.isConstOf ``Nat &&
          !args[0]!.cleanupAnnotations.isConstOf ``Int then
        addPt args[0]! u (.ne args[1]! args[2]! pf); return

/-- Check whether `s` contains `{x}`, `insert x _`, or `_.erase x` for element `x`. -/
private partial def collectExplicitSingletonPts (α : Expr) (s : Expr)
    (pts : IO.Ref (Array Expr)) : MetaM Unit := do
  let sPeel ← peekFinsetLet s
  let sc := sPeel.cleanupAnnotations
  let fn := sc.getAppFn
  let args := sc.getAppArgs
  if (fn.isConstOf ``Max.max || fn.isConstOf ``Union.union ||
      fn.isConstOf ``Min.min || fn.isConstOf ``Inter.inter ||
      fn.isConstOf ``SDiff.sdiff) && args.size == 4 then
    collectExplicitSingletonPts α args[2]! pts
    collectExplicitSingletonPts α args[3]! pts
  else if fn.isConstOf ``Compl.compl && args.size == 3 then
    collectExplicitSingletonPts α args[2]! pts
  else if fn.isConstOf ``Insert.insert && args.size == 5 then
    pts.modify (pushUniqueExpr · args[3]!)
    collectExplicitSingletonPts α args[4]! pts
  else if fn.isConstOf ``Finset.erase && args.size == 4 then
    pts.modify (pushUniqueExpr · args[3]!)
    collectExplicitSingletonPts α args[2]! pts
  else if fn.isConstOf ``Singleton.singleton && args.size == 4 then
    if ← withReducible (isDefEq args[0]! α) then
      pts.modify (pushUniqueExpr · args[3]!)

/-- Extract `(β, f, v)` when `p` has the shape `fun x => f x = v` (`v` independent of `x`). -/
private def matchFiberPred? (α p : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  withLocalDeclD `x α fun x => do
    let body := (p.beta #[x]).cleanupAnnotations
    if body.isAppOfArity ``Eq 3 then
      let args := body.getAppArgs
      if !args[2]!.containsFVar x.fvarId! then
        return some (args[0]!, ← mkLambdaFVars #[x] args[1]!, args[2]!)
    return none

/-- Reduce subset (`s ⊆ t` → `s \ t = ∅`), nonemptiness, or pigeonhole targets before
`falseOrByContra`. -/
private def tryReduceTarget (g : MVarId) : MetaM MVarId := g.withContext do
  let target := (← instantiateMVars (← g.getType)).cleanupAnnotations
  let fn := target.getAppFn
  let args := target.getAppArgs
  if (fn.isConstOf ``LE.le || fn.isConstOf ``HasSubset.Subset) && args.size == 4 then
    if let some (α, u) := finsetCarrier? args[0]! then
      let s := args[2]!; let t := args[3]!
      let decEq := (← synthInstance? (mkApp (mkConst ``DecidableEq [u.succ]) α)).getD
        (mkApp (mkConst ``Classical.typeDecidableEq [u.succ]) α)
      let finsetTy := mkApp (mkConst ``Finset [u]) α
      let sd := mkApp4 (mkConst ``SDiff.sdiff [u]) finsetTy
        (mkApp2 (mkConst ``Finset.instSDiff [u]) α decEq) s t
      let emp ← mkAppOptM ``EmptyCollection.emptyCollection #[some finsetTy, none]
      let newTy ← mkEq sd emp
      let m ← mkFreshExprSyntheticOpaqueMVar newTy
      let pf ← mkAppOptM ``Iff.mp
        #[none, none,
          some (mkApp4 (mkConst ``Finset.sdiff_eq_empty_iff_subset [u]) α decEq s t),
          some m]
      if ← isDefEq (← inferType pf) target then
        g.assign (← mkExpectedTypeHint pf target)
        return m.mvarId!
  if fn.isConstOf ``Finset.Nonempty && args.size == 2 then
    let α := args[0]!; let u := fn.constLevels![0]!; let s := args[1]!
    let newTy ← mkAppM ``LT.lt #[mkNatLit 0, mkApp2 (mkConst ``Finset.card [u]) α s]
    let m ← mkFreshExprSyntheticOpaqueMVar newTy
    let pf ← mkAppOptM ``Iff.mp
      #[none, none, some (mkApp2 (mkConst ``Finset.card_pos [u]) α s), some m]
    g.assign pf
    return m.mvarId!
  if fn.isConstOf ``Exists && args.size == 2 then
    let α := args[0]!
    let .sort (.succ u) ← whnf (← inferType α) | return g
    let pred := args[1]!
    let decEq := (← synthInstance? (mkApp (mkConst ``DecidableEq [u.succ]) α)).getD
      (mkApp (mkConst ``Classical.typeDecidableEq [u.succ]) α)
    let action? ← withLocalDeclD `x α fun x => do
      let body := (pred.beta #[x]).cleanupAnnotations
      if body.isAppOfArity ``Membership.mem 5 then
        let bArgs := body.getAppArgs
        if (finsetCarrier? bArgs[1]!).isSome && bArgs[4]! == x &&
            !bArgs[3]!.containsFVar x.fvarId! then
          return some (0, bArgs[3]!, bArgs[3]!)
      if body.isAppOfArity ``And 2 then
        let a := body.getAppArgs[0]!.cleanupAnnotations
        let b := body.getAppArgs[1]!.cleanupAnnotations
        if a.isAppOfArity ``Membership.mem 5 && b.isAppOfArity ``Not 1 then
          let bm := b.appArg!.cleanupAnnotations
          if bm.isAppOfArity ``Membership.mem 5 then
            let aArgs := a.getAppArgs; let bArgs := bm.getAppArgs
            if (finsetCarrier? aArgs[1]!).isSome && (finsetCarrier? bArgs[1]!).isSome &&
                aArgs[4]! == x && bArgs[4]! == x &&
                !aArgs[3]!.containsFVar x.fvarId! && !bArgs[3]!.containsFVar x.fvarId! then
              return some (1, aArgs[3]!, bArgs[3]!)
      if body.isAppOfArity ``Not 1 then
        let bm := body.appArg!.cleanupAnnotations
        if bm.isAppOfArity ``Membership.mem 5 then
          let bArgs := bm.getAppArgs
          if (finsetCarrier? bArgs[1]!).isSome && bArgs[4]! == x &&
              !bArgs[3]!.containsFVar x.fvarId! then
            return some (2, bArgs[3]!, bArgs[3]!)
      return none
    if let some (kind, s, t) := action? then
      let finsetTy := mkApp (mkConst ``Finset [u]) α
      let sdiffInst := mkApp2 (mkConst ``Finset.instSDiff [u]) α decEq
      if kind == 0 then
        let newTy ← mkAppM ``LT.lt #[mkNatLit 0, mkApp2 (mkConst ``Finset.card [u]) α s]
        let m ← mkFreshExprSyntheticOpaqueMVar newTy
        let pf ← mkAppOptM ``Iff.mp
          #[none, none, some (mkApp2 (mkConst ``Finset.card_pos [u]) α s), some m]
        if ← isDefEq (← inferType pf) target then
          g.assign (← mkExpectedTypeHint pf target); return m.mvarId!
      else if kind == 1 then
        let sd := mkApp4 (mkConst ``SDiff.sdiff [u]) finsetTy sdiffInst s t
        let newTy ← mkAppM ``LT.lt #[mkNatLit 0, mkApp2 (mkConst ``Finset.card [u]) α sd]
        let m ← mkFreshExprSyntheticOpaqueMVar newTy
        let pf ← mkAppOptM ``FinsetCard.exists_mem_notMem_of_card_sdiff_pos
          #[some α, some decEq, some s, some t, some m]
        if ← isDefEq (← inferType pf) target then
          g.assign pf; return m.mvarId!
      else if kind == 2 then
        if let some ft ← synthInstance? (mkApp (mkConst ``Fintype [u]) α) then
          let univ := mkApp2 (mkConst ``Finset.univ [u]) α ft
          let sd := mkApp4 (mkConst ``SDiff.sdiff [u]) finsetTy sdiffInst univ t
          let newTy ← mkAppM ``LT.lt #[mkNatLit 0, mkApp2 (mkConst ``Finset.card [u]) α sd]
          let m ← mkFreshExprSyntheticOpaqueMVar newTy
          let pf ← mkAppOptM ``FinsetCard.exists_notMem_of_card_sdiff_univ_pos
            #[some α, some ft, some decEq, some t, some m]
          if ← isDefEq (← inferType pf) target then
            g.assign pf; return m.mvarId!
  return g

private structure ParsedRel where
  kind : ℕ
  e₁ : FinsetCard.SetExpr
  e₂ : FinsetCard.SetExpr
  pf : Expr
  p₁? : Option Expr
  p₂? : Option Expr
  s : Expr
  t : Expr

/-- Extract `Finset α` expressions appearing directly in `goalTy` (before `falseOrByContra`). -/
private partial def collectGoalFinsets (α goalTy : Expr) : MetaM (Array Expr) := do
  let accRef ← IO.mkRef (#[] : Array Expr)
  let addIfCarrier (candα s : Expr) : MetaM Unit := do
    if ← withReducible (isDefEq candα α) then
      accRef.modify (pushUniqueExpr · s)
  let rec go (e : Expr) : MetaM Unit := do
    if e.hasLooseBVars then return
    let ec := e.cleanupAnnotations
    let fn := ec.getAppFn
    let args := ec.getAppArgs
    if fn.isConstOf ``Finset.card && args.size == 2 then
      addIfCarrier args[0]! args[1]!
    else if (fn.isConstOf ``LE.le || fn.isConstOf ``HasSubset.Subset) && args.size == 4 then
      if let some (cα, _) := finsetCarrier? args[0]! then
        addIfCarrier cα args[2]!; addIfCarrier cα args[3]!
    else if fn.isConstOf ``Disjoint && args.size == 5 then
      if let some (cα, _) := finsetCarrier? args[0]! then
        addIfCarrier cα args[3]!; addIfCarrier cα args[4]!
    else if (fn.isConstOf ``Eq || fn.isConstOf ``Ne) && args.size == 3 then
      if let some (cα, _) := finsetCarrier? args[0]! then
        addIfCarrier cα args[1]!; addIfCarrier cα args[2]!
    else if fn.isConstOf ``Finset.Nonempty && args.size == 2 then
      addIfCarrier args[0]! args[1]!
    match ec with
    | .app f a => go f; go a
    | .forallE _ d b _ => go d; if !b.hasLooseBVars then go b
    | .letE _ t v b _ => go t; go v; if !b.hasLooseBVars then go b
    | .mdata _ inner => go inner
    | _ => pure ()
  go goalTy
  accRef.get

/-- Check whether carrier `α` appears directly in `goalTy` (as `Finset α`, `Fintype.card α`, or
point equality/membership on `α`). -/
private partial def carrierInGoal (α goalTy : Expr) : MetaM Bool := do
  let foundRef ← IO.mkRef false
  let checkCand (cand : Expr) : MetaM Unit := do
    if !(← foundRef.get) then
      if ← withReducible (isDefEq cand α) then
        foundRef.set true
  let rec go (e : Expr) : MetaM Unit := do
    if (← foundRef.get) || e.hasLooseBVars then return
    let ec := e.cleanupAnnotations
    let fn := ec.getAppFn
    let args := ec.getAppArgs
    if fn.isConstOf ``Finset && args.size == 1 then
      checkCand args[0]!
    else if fn.isConstOf ``Fintype.card && args.size == 2 then
      checkCand args[0]!
    else if (fn.isConstOf ``Eq || fn.isConstOf ``Ne) && args.size == 3 then
      checkCand args[0]!
    else if fn.isConstOf ``Membership.mem && args.size == 5 then
      checkCand args[0]!
    match ec with
    | .app f a => go f; go a
    | .forallE _ d b _ => go d; if !b.hasLooseBVars then go b
    | .letE _ t v b _ => go t; go v; if !b.hasLooseBVars then go b
    | .mdata _ inner => go inner
    | _ => pure ()
  go goalTy
  foundRef.get

/-- Process one `CarrierData` and return all derived arithmetic `Hypothesis` facts for `omega`
(plus `atoms.size` for diagnostics). -/
private def buildCarrierFacts (cd : CarrierData) (goalBeforeContra : Expr) :
    MetaM (Array Hypothesis × ℕ) := do
  let α := cd.α
  let u := cd.u
  let fintype? ← synthInstance? (mkApp (mkConst ``Fintype [u]) α)
  let decEq := (← synthInstance? (mkApp (mkConst ``DecidableEq [u.succ]) α)).getD
    (mkApp (mkConst ``Classical.typeDecidableEq [u.succ]) α)
  let finsetTy := mkApp (mkConst ``Finset [u]) α
  let sdiffInst := mkApp2 (mkConst ``Finset.instSDiff [u]) α decEq

  let atomPtsRef ← IO.mkRef (#[] : Array Expr)
  for s in cd.cardTerms do collectExplicitSingletonPts α s atomPtsRef
  for r in cd.setRels do
    let (s, t) := match r with
      | .subset a b _ | .disjoint a b _ | .notDisjoint a b _ | .eq a b _ | .ne a b _ => (a, b)
    collectExplicitSingletonPts α s atomPtsRef
    collectExplicitSingletonPts α t atomPtsRef
  let hasMemFact := cd.pointFacts.any fun
    | .mem .. | .notMem .. => true
    | .ne .. => false
  let hasFinsetOrUniv := !cd.cardTerms.isEmpty || !cd.setRels.isEmpty ||
    !cd.fintypeCards.isEmpty || hasMemFact
  if hasFinsetOrUniv then
    for pf in cd.pointFacts do
      if let .ne x y _ := pf then
        atomPtsRef.modify (fun a => pushUniqueExpr (pushUniqueExpr a x) y)
  let atomPts ← atomPtsRef.get

  let mut cardTerms := cd.cardTerms
  let mut setRels := cd.setRels
  let mut outFacts : Array Hypothesis := #[]
  let mut nonAtomMems : Array (Expr × Expr × Expr) := #[]
  let mut nonAtomNotMems : Array (Expr × Expr × Expr) := #[]

  for pt in atomPts do
    let sing := mkSingletonFinset α u pt
    cardTerms := pushUniqueExpr cardTerms sing
    let cardOnePf := mkApp2 (mkConst ``Finset.card_singleton [u]) α pt
    outFacts := outFacts.push
      { userName := `h_sing, type := ← inferType cardOnePf, value := cardOnePf }

  let mkCardPosOfMem (x s memPf : Expr) : MetaM Hypothesis := do
    let neZero := mkApp4 (mkConst ``Finset.card_ne_zero_of_mem [u]) α s x memPf
    let posPf := mkApp2 (mkConst ``Nat.pos_of_ne_zero)
      (mkApp2 (mkConst ``Finset.card [u]) α s) neZero
    return { userName := `h_mem_pos, type := ← inferType posPf, value := posPf }

  for pfact in cd.pointFacts do
    match pfact with
    | .mem x s pf =>
      if atomPts.any (· == x) then
        let sing := mkSingletonFinset α u x
        let subPf ← mkAppOptM ``Iff.mpr
          #[none, none, some (mkApp3 (mkConst ``Finset.singleton_subset_iff [u]) α s x), some pf]
        setRels := setRels.push (.subset sing s subPf)
      else
        nonAtomMems := nonAtomMems.push (x, s, pf)
        cardTerms := pushUniqueExpr cardTerms s
        outFacts := outFacts.push (← mkCardPosOfMem x s pf)
    | .notMem x t pf =>
      if atomPts.any (· == x) then
        let sing := mkSingletonFinset α u x
        let disjPf ← mkAppOptM ``Iff.mpr
          #[none, none, some (mkApp3 (mkConst ``Finset.disjoint_singleton_left [u]) α t x), some pf]
        setRels := setRels.push (.disjoint sing t disjPf)
      else
        nonAtomNotMems := nonAtomNotMems.push (x, t, pf)
        if let some ft := fintype? then
          let univ := mkApp2 (mkConst ``Finset.univ [u]) α ft
          let sd := mkApp4 (mkConst ``SDiff.sdiff [u]) finsetTy sdiffInst univ t
          cardTerms := pushUniqueExpr cardTerms sd
          let memUniv := mkApp3 (mkConst ``Finset.mem_univ [u]) α ft x
          let memSd ← mkAppOptM ``Iff.mpr
            #[none, none, some (mkApp5 (mkConst ``Finset.mem_sdiff [u]) α decEq univ t x),
              some (← mkAppM ``And.intro #[memUniv, pf])]
          outFacts := outFacts.push (← mkCardPosOfMem x sd memSd)
    | .ne x y pf =>
      if atomPts.any (· == x) && atomPts.any (· == y) then
        let singX := mkSingletonFinset α u x
        let singY := mkSingletonFinset α u y
        let disjPf ← mkAppOptM ``Iff.mpr
          #[none, none, some (mkApp3 (mkConst ``Finset.disjoint_singleton [u]) α x y), some pf]
        setRels := setRels.push (.disjoint singX singY disjPf)

  for (x, s, pfs) in nonAtomMems do
    for (x', t, pft) in nonAtomNotMems do
      if x == x' || (← withReducible (isDefEq x x')) then
        let sd := mkApp4 (mkConst ``SDiff.sdiff [u]) finsetTy sdiffInst s t
        cardTerms := pushUniqueExpr cardTerms sd
        let memProp ← mkAppOptM ``Membership.mem #[some α, some finsetTy, none, some t, some x]
        let pft' ← mkExpectedTypeHint pft (mkApp (mkConst ``Not) memProp)
        let memSd ← mkAppOptM ``Iff.mpr
          #[none, none, some (mkApp5 (mkConst ``Finset.mem_sdiff [u]) α decEq s t x),
            some (← mkAppM ``And.intro #[pfs, pft'])]
        outFacts := outFacts.push (← mkCardPosOfMem x sd memSd)

  if cardTerms.isEmpty && setRels.isEmpty && cd.fintypeCards.isEmpty then
    return (outFacts, 0)

  let parseAll (allowNew : Bool) (ref : IO.Ref (Array Expr)) :
      MetaM (Array (Expr × FinsetCard.SetExpr × Option Expr) × Array ParsedRel) := do
    let mut pCards : Array (Expr × FinsetCard.SetExpr × Option Expr) := #[]
    for s in cardTerms do
      if let some (se, eqPf?) ← parseSetExpr α u decEq fintype? allowNew ref s then
        pCards := pCards.push (s, se, eqPf?)
    let mut pRels : Array ParsedRel := #[]
    let parseBin (k : ℕ) (s t pf : Expr) (acc : Array ParsedRel) : MetaM (Array ParsedRel) := do
      if let (some (e₁, p₁?), some (e₂, p₂?)) ← (return (
          ← parseSetExpr α u decEq fintype? allowNew ref s,
          ← parseSetExpr α u decEq fintype? allowNew ref t)) then
        return acc.push ⟨k, e₁, e₂, pf, p₁?, p₂?, s, t⟩
      return acc
    for r in setRels do
      match r with
      | .subset s t pf => pRels ← parseBin 0 s t pf pRels
      | .disjoint s t pf => pRels ← parseBin 1 s t pf pRels
      | .notDisjoint s t pf => pRels ← parseBin 2 s t pf pRels
      | .eq s t pf => pRels ← parseBin 3 s t pf pRels
      | .ne s t pf => pRels ← parseBin 4 s t pf pRels
    return (pCards, pRels)

  let atomsRef ← IO.mkRef (#[] : Array Expr)
  let (pc0, pr0) ← parseAll true atomsRef
  let mut parsedCards := pc0
  let mut parsedRels := pr0

  -- When unrelated outer hypotheses push `atoms` past `maxAtoms`, focus on the goal's connected
  -- component of ≤ `maxAtoms` atomic finsets, or skip carriers absent from the goal.
  if (← atomsRef.get).size > maxAtoms then
    let goalSets ← collectGoalFinsets α goalBeforeContra
    let focusRef ← IO.mkRef (#[] : Array Expr)
    for gs in goalSets do
      let _ ← parseSetExpr α u decEq fintype? true focusRef gs
    let seedSize := (← focusRef.get).size
    if 0 < seedSize && seedSize ≤ maxAtoms then
      for _ in [:2] do
        for r in setRels do
          let (s, t) := match r with
            | .subset a b _ | .disjoint a b _ | .notDisjoint a b _ | .eq a b _ | .ne a b _ => (a, b)
          let cur ← focusRef.get
          let rRef ← IO.mkRef (#[] : Array Expr)
          let _ ← parseSetExpr α u decEq fintype? true rRef s
          let _ ← parseSetExpr α u decEq fintype? true rRef t
          let rAtoms ← rRef.get
          let overlaps ← rAtoms.anyM fun ra =>
            cur.anyM fun ca => pure (ca == ra) <||> withReducible (isDefEq ca ra)
          if overlaps then
            let tmpRef ← IO.mkRef cur
            for ra in rAtoms do
              let _ ← parseSetExpr α u decEq fintype? true tmpRef ra
            if (← tmpRef.get).size ≤ maxAtoms then
              focusRef.set (← tmpRef.get)
      atomsRef.set (← focusRef.get)
      let (pc, pr) ← parseAll false atomsRef
      parsedCards := pc
      parsedRels := pr
    else if seedSize == 0 && !(← carrierInGoal α goalBeforeContra) then
      return (outFacts, 0)

  let atoms ← atomsRef.get
  if atoms.size > maxAtoms then
    throwError "finset_card: carrier '{α}' has {atoms.size} atomic finsets (limit: {maxAtoms}): \
      {atoms.toList}. Bound or combine intermediate sets before calling `finset_card`."

  -- Harvest zero-new-atom `Finset.filter` constraints among `atoms`
  for i in [:atoms.size] do
    let ai := atoms[i]!.cleanupAnnotations
    if ai.isAppOfArity ``Finset.filter 4 then
      let fArgs := ai.getAppArgs
      let p₁ := fArgs[1]!; let d₁ := fArgs[2]!; let base₁ := fArgs[3]!
      if !base₁.cleanupAnnotations.isAppOfArity ``Finset.univ 2 then
        if let some (eBase, pBase?) ← parseSetExpr α u decEq fintype? false atomsRef base₁ then
          let subPf := mkApp4 (mkConst ``Finset.filter_subset [u]) α p₁ d₁ base₁
          parsedRels := parsedRels.push ⟨0, .atom i, eBase, subPf, none, pBase?, atoms[i]!, base₁⟩
      let fib₁? ← matchFiberPred? α p₁
      for j in [i + 1 : atoms.size] do
        let aj := atoms[j]!.cleanupAnnotations
        if aj.isAppOfArity ``Finset.filter 4 then
          let gArgs := aj.getAppArgs
          let p₂ := gArgs[1]!; let d₂ := gArgs[2]!; let base₂ := gArgs[3]!
          let isNeg₁₂ ← withLocalDeclD `x α (fun x =>
            withReducible do isDefEq (p₂.beta #[x]) (mkApp (mkConst ``Not) (p₁.beta #[x])))
          let isNeg₂₁ ← if isNeg₁₂ then pure false else withLocalDeclD `x α (fun x =>
            withReducible do isDefEq (p₁.beta #[x]) (mkApp (mkConst ``Not) (p₂.beta #[x])))
          if isNeg₁₂ || isNeg₂₁ then
            let (idxA, idxB, sA, sB, predP, decP, decNotP) :=
              if isNeg₁₂ then (i, j, base₁, base₂, p₁, d₁, d₂)
              else (j, i, base₂, base₁, p₂, d₂, d₁)
            let disjPf ← mkAppOptM ``Finset.disjoint_filter_filter_not
              #[some α, some sA, some sB, some predP, some decP, some decNotP]
            parsedRels := parsedRels.push
              ⟨1, .atom idxA, .atom idxB, disjPf, none, none, atoms[idxA]!, atoms[idxB]!⟩
            if sA == sB then
              if let some (eBase, pBase?) ← parseSetExpr α u decEq fintype? false atomsRef sA then
                let partPf ← mkAppOptM ``Finset.filter_union_filter_not_eq
                  #[some α, some predP, some decP, some decEq, some decNotP, some sA]
                let lhs := mkApp4 (mkConst ``Max.max [u]) finsetTy
                  (mkApp2 (mkConst ``Finset.instMax [u]) α decEq) atoms[idxA]! atoms[idxB]!
                parsedRels := parsedRels.push
                  ⟨3, .union (.atom idxA) (.atom idxB), eBase, partPf, none, pBase?, lhs, sA⟩
          else if let some (β₁, fn₁, v₁) := fib₁? then
            if let some (β₂, fn₂, v₂) ← matchFiberPred? α p₂ then
              if (← withReducible (isDefEq β₁ β₂)) && (← withReducible (isDefEq fn₁ fn₂)) then
                if let some hne ← proveNeFast? β₁ v₁ v₂ then
                  let disjPf ← mkAppOptM ``FinsetCard.disjoint_filter_eq_of_ne
                    #[some α, some β₁, some base₁, some base₂, some fn₁, some v₁, some v₂,
                      some d₁, some d₂, some hne]
                  parsedRels := parsedRels.push
                    ⟨1, .atom i, .atom j, disjPf, none, none, atoms[i]!, atoms[j]!⟩
                  if base₁ == base₂ && β₁.cleanupAnnotations.isConstOf ``Bool then
                    let v₁c := v₁.cleanupAnnotations; let v₂c := v₂.cleanupAnnotations
                    let isTF := v₁c.isConstOf ``Bool.true && v₂c.isConstOf ``Bool.false
                    let isFT := v₁c.isConstOf ``Bool.false && v₂c.isConstOf ``Bool.true
                    if isTF || isFT then
                      if let some (eB, pB?) ←
                          parseSetExpr α u decEq fintype? false atomsRef base₁ then
                        let (idxT, idxF, dT, dF) :=
                          if isTF then (i, j, d₁, d₂) else (j, i, d₂, d₁)
                        let partPf ← mkAppOptM ``FinsetCard.filter_eq_true_union_filter_eq_false
                          #[some α, some decEq, some base₁, some fn₁, some dT, some dF]
                        let lhs := mkApp4 (mkConst ``Max.max [u]) finsetTy
                          (mkApp2 (mkConst ``Finset.instMax [u]) α decEq) atoms[idxT]! atoms[idxF]!
                        parsedRels := parsedRels.push
                          ⟨3, .union (.atom idxT) (.atom idxF), eB, partPf, none, pB?, lhs, base₁⟩

  let atomsList := atoms.toList
  let asExpr := mkFinsetListExpr α u atomsList
  let (U, hU) := match fintype? with
    | some ft =>
      (mkApp2 (mkConst ``Finset.univ [u]) α ft,
       mkApp3 (mkConst ``FinsetCard.allSubset_univ [u]) α ft asExpr)
    | none =>
      (mkApp3 (mkConst ``FinsetCard.unionAll [u]) α decEq asExpr,
       mkApp3 (mkConst ``FinsetCard.allSubset_unionAll [u]) α decEq asExpr)

  let denoteOf (se : FinsetCard.SetExpr) : Expr :=
    mkApp5 (mkConst ``FinsetCard.SetExpr.denote [u]) α decEq U asExpr (reflectSetExpr se)

  if let some ft := fintype? then
    let rhs := mkVennSumExpr α u decEq (fun _ => true) U atomsList
    for (fcExpr, ft₁) in cd.fintypeCards do
      let eqTy ← mkEq fcExpr rhs
      let rawPf := mkApp5 (mkConst ``FinsetCard.card_univ_eq_vennSum [u]) α ft₁ ft decEq asExpr
      let pf ← mkExpectedTypeHint rawPf eqTy
      outFacts := outFacts.push { userName := `h_univ_card, type := eqTy, value := pf }

  for (s, se, eqPf?) in parsedCards do
    let lhs := mkApp2 (mkConst ``Finset.card [u]) α s
    let rhs := mkVennSumExpr α u decEq (evalBoolMeta se) U atomsList
    let eqTy ← mkEq lhs rhs
    let basePf := mkApp6 (mkConst ``FinsetCard.card_denote_eq [u])
      α decEq U asExpr hU (reflectSetExpr se)
    let rawPf ← match eqPf? with
      | none => pure basePf
      | some eqPf =>
        let cardCongr ← mkCongrArg (mkApp (mkConst ``Finset.card [u]) α) eqPf
        mkEqTrans cardCongr basePf
    let pf ← mkExpectedTypeHint rawPf eqTy
    outFacts := outFacts.push { userName := `h_card, type := eqTy, value := pf }

  let zero := mkNatLit 0
  for r in parsedRels do
    let e₁ := r.e₁; let e₂ := r.e₂
    let p₁ ← match r.p₁? with | some p => pure p | none => mkEqRefl (denoteOf e₁)
    let p₂ ← match r.p₂? with | some p => pure p | none => mkEqRefl (denoteOf e₂)
    let re₁ := reflectSetExpr e₁; let re₂ := reflectSetExpr e₂
    let mkBinHyp (nm thm : Name) (comb : Bool → Bool → Bool) (isPos : Bool) :
        MetaM Hypothesis := do
      let v := mkVennSumExpr α u decEq (fun bs => comb (evalBoolMeta e₁ bs) (evalBoolMeta e₂ bs))
        U atomsList
      let ty ← if isPos then mkAppM ``LT.lt #[zero, v] else mkEq v zero
      let raw ← mkAppOptM thm #[some α, some decEq, some U, some asExpr, some hU, some re₁,
        some re₂, some r.s, some r.t, some p₁, some p₂, some r.pf]
      return { userName := nm, type := ty, value := ← mkExpectedTypeHint raw ty }
    if r.kind == 0 then
      outFacts := outFacts.push (← mkBinHyp `h_sub ``FinsetCard.subset_denote_mp (· && !·) false)
    else if r.kind == 1 then
      outFacts := outFacts.push (← mkBinHyp `h_disj ``FinsetCard.disjoint_denote_mp (· && ·) false)
    else if r.kind == 2 then
      outFacts := outFacts.push
        (← mkBinHyp `h_ndisj ``FinsetCard.not_disjoint_denote_mp (· && ·) true)
    else if r.kind == 3 then
      outFacts := outFacts.push (← mkBinHyp `h_eq ``FinsetCard.eq_denote_mp (· != ·) false)
    else if r.kind == 4 then
      outFacts := outFacts.push (← mkBinHyp `h_ne ``FinsetCard.ne_denote_mp (· != ·) true)

  return (outFacts, atoms.size)

/-- Parse optional `finset_card [x₁, x₂, …]` bracket arguments into:
1. global `def`/`abbrev` names to delta-expand,
2. rewrite `simpLemma` syntax items (for quantified `=`/`↔` lemmas), and
3. concrete proof terms to assert as local hypotheses. -/
private def classifyArgs (rawArgs : Array Term) :
    TacticM (NameSet × Array (TSyntax `Lean.Parser.Tactic.simpLemma) × Array Hypothesis) :=
  withMainContext do
  let mut defs : NameSet := {}
  let mut rwLemmas : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  let mut extraHyps : Array Hypothesis := #[]
  for stx in rawArgs do
    if stx.raw.isIdent then
      let name? ← try some <$> realizeGlobalConstNoOverload stx catch _ => pure none
      if let some name := name? then
        if let some info := (← getEnv).find? name then
          if info.isDef then
            defs := defs.insert name
            continue
          if info.type.isForall then
            let body ← forallTelescope info.type fun _ b => pure b.cleanupAnnotations
            if body.isAppOfArity ``Eq 3 || body.isAppOfArity ``Iff 2 then
              let sl ← `(Lean.Parser.Tactic.simpLemma| $stx:term)
              rwLemmas := rwLemmas.push sl
              continue
    let e ← elabTerm stx none
    let ty ← instantiateMVars (← inferType e)
    if ← isProp ty then
      let tyWhnf ← whnfD ty
      if tyWhnf.isForall then
        let body ← forallTelescope ty fun _ b => pure b.cleanupAnnotations
        if body.isAppOfArity ``Eq 3 || body.isAppOfArity ``Iff 2 then
          let sl ← `(Lean.Parser.Tactic.simpLemma| $stx:term)
          rwLemmas := rwLemmas.push sl
          continue
      extraHyps := extraHyps.push { userName := `h_hint, type := ty, value := e }
    else
      throwError "finset_card: expected a definition to unfold or a proof term, got '{stx}' of \
        type{indentExpr ty}"
  return (defs, rwLemmas, extraHyps)

/-- Prove a quantifier-free `Finset` cardinality, quorum-intersection, set-relation (`⊆`, `=`,
`≠`, `Disjoint`, `Finset.Nonempty`), membership (`∈`, `∉`), or pigeonhole (`∃ x ∈ S, x ∉ F`) goal
by Venn-region decomposition (up to 5 atomic finsets per carrier type) followed by `omega`.

* `finset_card` inspects the goal and all local hypotheses across every carrier type `α`.
* `finset_card [d₁, h₁, …]` additionally unfolds named definitions `d₁`, rewrites with quantified
  `=`/`↔` lemmas, and supplies extra proof terms `h₁` (such as product bounds or list-nodup
  cardinalities). -/
syntax (name := finsetCard) "finset_card" (" [" term,* "]")? : tactic

@[inherit_doc finsetCard]
elab_rules : tactic
  | `(tactic| finset_card $[[$args,*]]?) => focus do
    recordExtraModUse (isMeta := false) `Init.Omega
    recordExtraModUse (isMeta := false) `CslibFrontier.Tactic.FinsetCard
    let rawArgs := (args.map (·.getElems)).getD #[]
    let (unfoldDefs, rwLemmas, extraHyps) ← classifyArgs rawArgs

    if !extraHyps.isEmpty then
      let g ← getMainGoal
      let (_, g) ← g.assertHypotheses extraHyps
      replaceMainGoal [g]

    if !rwLemmas.isEmpty then
      let g ← getMainGoal
      let free ← g.getNondepPropHyps
      let copies ← g.withContext do
        (← getLCtx).foldlM (init := #[]) fun acc d => do
          if d.isImplementationDetail || free.contains d.fvarId || !(← isProp d.type) then
            return acc
          return acc.push { userName := d.userName, type := d.type, value := d.toExpr }
      let (_, g) ← g.assertHypotheses copies
      replaceMainGoal [g]
      withoutRecover <| evalTactic
        (← `(tactic| simp -failIfUnchanged only [$rwLemmas,*] at *))
      if (← getUnsolvedGoals).isEmpty then return

    if !unfoldDefs.isEmpty then
      let g ← getMainGoal
      let g ← g.withContext do
        let mentionsDef (e : Expr) : Bool :=
          (e.find? fun t => match t.constName? with
            | some n => unfoldDefs.contains n | none => false).isSome
        let expand (e : Expr) : CoreM Expr := deltaExpand e (unfoldDefs.contains ·)
        let target ← instantiateMVars (← g.getType)
        let g ← if mentionsDef target then g.replaceTargetDefEq (← expand target) else pure g
        let unfoldedHyps ← (← getLCtx).foldlM (init := #[]) fun acc d => do
          if d.isImplementationDetail then return acc
          let ty ← instantiateMVars d.type
          unless mentionsDef ty && (← isProp ty) do return acc
          return acc.push { userName := d.userName, type := ← expand ty, value := d.toExpr }
        let (_, g) ← g.assertHypotheses unfoldedHyps
        return g
      replaceMainGoal [g]

    let origGoal ← getMainGoal
    let g ← tryReduceTarget origGoal
    replaceMainGoal [g]

    let g ← getMainGoal
    let goalBeforeContra ← instantiateMVars (← g.getType)
    let some g ← g.falseOrByContra | replaceMainGoal []; return

    let (g, totalCarriers) ← g.withContext do
      let carriersRef ← IO.mkRef (#[] : Array CarrierData)
      let mapImgRef ← IO.mkRef (#[] : Array (Expr × Expr))
      for d in ← getLCtx do
        if d.isImplementationDetail then continue
        if ← isProp d.type then
          harvestHyp d.type d.toExpr carriersRef mapImgRef

      let mut derivedFacts : Array Hypothesis := #[]

      for (_, pf) in ← mapImgRef.get do
        derivedFacts := derivedFacts.push
          { userName := `h_map_img_card, type := ← inferType pf, value := pf }

      let carriers ← carriersRef.get
      let mut activeCarriers := 0
      for cd in carriers do
        let αc := cd.α.cleanupAnnotations
        if αc.isAppOfArity ``Fin 1 then
          let n := αc.appArg!
          let pf := mkApp (mkConst ``Fintype.card_fin) n
          derivedFacts := derivedFacts.push
            { userName := `h_card_fin, type := ← inferType pf, value := pf }
          let hasFinsetAct := !cd.cardTerms.isEmpty || !cd.setRels.isEmpty ||
            cd.pointFacts.any fun | .mem .. | .notMem .. => true | .ne .. => false
          if hasFinsetAct || !cd.fintypeCards.isEmpty ||
              (!cd.pointFacts.isEmpty && (← carrierInGoal cd.α goalBeforeContra)) then
            let fc := (← inferType pf).getAppArgs[1]!
            let ft := fc.appArg!
            let cd' := if cd.fintypeCards.any (fun (x, _) => x == fc) then cd
              else { cd with fintypeCards := cd.fintypeCards.push (fc, ft) }
            let (facts, _) ← buildCarrierFacts cd' goalBeforeContra
            derivedFacts := derivedFacts ++ facts
            activeCarriers := activeCarriers + 1
          else
            activeCarriers := activeCarriers + 1
        else
          if !cd.cardTerms.isEmpty || !cd.setRels.isEmpty || !cd.fintypeCards.isEmpty ||
              !cd.pointFacts.isEmpty then
            let (facts, _) ← buildCarrierFacts cd goalBeforeContra
            if !facts.isEmpty then
              derivedFacts := derivedFacts ++ facts
              activeCarriers := activeCarriers + 1

      if activeCarriers == 0 && derivedFacts.isEmpty then
        throwError "finset_card: no `Finset` or `Fintype.card` terms found; use `omega` for plain \
          arithmetic.{indentD origGoal}"

      let (_, g') ← g.assertHypotheses derivedFacts
      return (g', activeCarriers)

    replaceMainGoal [g]
    Cslib.Tactic.withFailureNote
      m!"finset_card reduced {totalCarriers} finite-set carrier(s) to Venn-region cardinalities, \
        and `omega` could not close the resulting Presburger goal:{indentD origGoal}\n\
        Supply opaque definitions or nonlinear bounds with `finset_card [def_or_hint]`." do
      evalTactic (← `(tactic| omega))

end Cslib.Tactic.FinsetCard

end
