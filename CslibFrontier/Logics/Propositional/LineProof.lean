/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.List.Basic
public import Mathlib.Data.Set.Defs

/-!
# Line-based DAG derivations

Propositional proof systems such as resolution, cutting planes and Frege present derivations as
sequences of lines in which each line is a hypothesis, an axiom, or inferred from earlier lines by
a sound rule. Recording a derivation in reverse chronological order (from its last line to its
first) lets a derivation grow by consing a new line in front while referencing any earlier line in
the tail, so shared intermediate lines are reused as a directed acyclic graph rather than
re-derived as a tree.

This module factors the common DAG proof-list combinators once over an arbitrary line type `L`:

* `Cslib.Logic.PL.LineRule` and `Cslib.Logic.PL.LineProof`: rules `premises ⊢ concl` (axioms have
  `premises = []`) and reverse-chronological derivations from a rule set `R` and hypothesis set `Γ`.
* `Cslib.Logic.PL.LineProof.comp`: DAG cut / replay of a derivation from `Δ` on top of a derivation
  `ls` from `Γ` when `Δ ⊆ Γ ∪ {x | x ∈ ls}`, keeping only a duplicate-free sublist of new lines
  not already present in `ls`.
* `Cslib.Logic.PL.LineProof.Grows` and `Cslib.Logic.PL.LineProof.simulate`: bounded-overhead
  extension of an existing prefix and line-by-line simulation between rule systems.

The bridge from sound derivations of arity at most two to semantic derivations
(`Cslib.Logic.PL.IsSemanticDerivation`) lives in
`CslibFrontier.Logics.Propositional.LineProof.SemanticDerivation`.

## Main definitions

* `Cslib.Logic.PL.LineRule`: an inference rule `premises ⊢ concl` over lines of type `L`.
* `Cslib.Logic.PL.LineProof`: reverse-chronological DAG derivations from rules `R` and
  hypotheses `Γ`.
* `Cslib.Logic.PL.LineProof.Grows`: extending an existing derivation by at most `n` prepended
  lines.

## Main results

* `Cslib.Logic.PL.LineProof.holds`: inductive soundness with respect to any semantic predicate
  preserved by `R`.
* `Cslib.Logic.PL.LineProof.comp`, `Cslib.Logic.PL.LineProof.Grows.comp`: DAG replay of a
  derivation onto an existing prefix without re-deriving lines already present.
* `Cslib.Logic.PL.LineProof.Grows.simulate`, `Cslib.Logic.PL.LineProof.simulate`: stepwise rule
  simulation with linear line-count overhead.

## References

* [S. A. Cook, R. A. Reckhow, *The relative efficiency of propositional proof
  systems*][CookReckhow1979]
-/

public section

namespace Cslib.Logic.PL

/-- An inference rule on lines of type `L`: from `premises` infer `concl`. An axiom is a rule with
`premises = []`. -/
@[ext]
structure LineRule (L : Type*) where
  /-- The earlier lines required by the rule. -/
  premises : List L
  /-- The line inferred by the rule. -/
  concl : L

/-- A **line-based DAG derivation** using rules `R` from hypotheses `Γ`, listed from its last line
to its first: every line is either in `Γ` or the conclusion of a rule in `R` whose premises already
appear below it in the derivation. -/
inductive LineProof {L : Type*} (R : Set (LineRule L)) (Γ : Set L) : List L → Prop
  /-- The empty derivation. -/
  | nil : LineProof R Γ []
  /-- A hypothesis from `Γ` added as a new line. -/
  | hyp {ls : List L} {x : L} (h : LineProof R Γ ls) (hx : x ∈ Γ) : LineProof R Γ (x :: ls)
  /-- The conclusion of a rule in `R` whose premises already appear in `ls`. -/
  | step {ls : List L} {r : LineRule L} (h : LineProof R Γ ls) (hr : r ∈ R)
      (hp : ∀ p ∈ r.premises, p ∈ ls) : LineProof R Γ (r.concl :: ls)

namespace LineProof

variable {L : Type*} {R R' : Set (LineRule L)} {Γ Δ : Set L} {ls ls' : List L}

/-- Enlarging the hypothesis set preserves derivations. -/
theorem mono_hyp (h : LineProof R Γ ls) (hΓ : Γ ⊆ Δ) : LineProof R Δ ls := by
  induction h with
  | nil => exact .nil
  | hyp _ hx ih => exact ih.hyp (hΓ hx)
  | step _ hr hp ih => exact ih.step hr hp

/-- Enlarging the rule set preserves derivations. -/
theorem mono_rules (h : LineProof R Γ ls) (hR : R ⊆ R') : LineProof R' Γ ls := by
  induction h with
  | nil => exact .nil
  | hyp _ hx ih => exact ih.hyp hx
  | step _ hr hp ih => exact ih.step (hR hr) hp

/-- A derivation uses only the hypotheses that appear among its lines. -/
theorem restrict (h : LineProof R Γ ls) : LineProof R (Γ ∩ {x | x ∈ ls}) ls := by
  suffices ∀ ls', ls ⊆ ls' → LineProof R (Γ ∩ {x | x ∈ ls'}) ls from this ls (List.Subset.refl _)
  intro ls' hsub
  induction h with
  | nil => exact .nil
  | hyp _ hx ih => exact (ih (List.cons_subset.1 hsub).2).hyp ⟨hx, (List.cons_subset.1 hsub).1⟩
  | step _ hr hp ih => exact (ih (List.cons_subset.1 hsub).2).step hr hp

/-- Placing a derivation `ls` on top of a derivation `ls'` from the same rules and hypotheses gives
a derivation `ls ++ ls'`. -/
theorem append (h : LineProof R Γ ls) (h' : LineProof R Γ ls') : LineProof R Γ (ls ++ ls') := by
  induction h with
  | nil => exact h'
  | hyp _ hx ih => exact ih.hyp hx
  | step _ hr hp ih => exact ih.step hr fun p hp' => List.mem_append_left _ (hp p hp')

/-- **Soundness**: if every hypothesis in `Γ` satisfies `Sem` and every rule in `R` preserves `Sem`
from its premises to its conclusion, then every line of `ls` satisfies `Sem`. -/
theorem holds {Sem : L → Prop} (h : LineProof R Γ ls) (hΓ : ∀ x ∈ Γ, Sem x)
    (hR : ∀ r ∈ R, (∀ p ∈ r.premises, Sem p) → Sem r.concl) : ∀ x ∈ ls, Sem x := by
  induction h with
  | nil => simp
  | hyp _ hx ih => exact List.forall_mem_cons.2 ⟨hΓ _ hx, ih⟩
  | step _ hr hp ih => exact List.forall_mem_cons.2 ⟨hR _ hr fun p hp' => ih p (hp p hp'), ih⟩

/-! ### DAG replay and cut -/

/-- One replay step of `LineProof.comp`: skip `x` if it is already available in `ls'' ++ ls`, and
prepend it otherwise. -/
private theorem comp_step {ls'' : List L} {x : L} (h'' : LineProof R Γ (ls'' ++ ls))
    (hadd : x ∉ ls'' ++ ls → LineProof R Γ (x :: (ls'' ++ ls)))
    (hup : ∀ y ∈ ls', y ∈ ls'' ++ ls) (hsub : ls''.Sublist ls') (hnodup : ls''.Nodup)
    (hdisj : ∀ y ∈ ls'', y ∉ ls) :
    ∃ ls₀, LineProof R Γ (ls₀ ++ ls) ∧ (∀ y ∈ x :: ls', y ∈ ls₀ ++ ls) ∧
      ls₀.Sublist (x :: ls') ∧ ls₀.Nodup ∧ ∀ y ∈ ls₀, y ∉ ls := by
  classical
  by_cases hx : x ∈ ls'' ++ ls
  · exact ⟨ls'', h'', List.forall_mem_cons.2 ⟨hx, hup⟩, hsub.cons x, hnodup, hdisj⟩
  · exact ⟨x :: ls'', hadd hx,
      List.forall_mem_cons.2 ⟨List.mem_cons_self, fun y hy => List.mem_cons_of_mem _ (hup y hy)⟩,
      hsub.cons_cons x, List.nodup_cons.2 ⟨fun hx'' => hx (List.mem_append_left _ hx''), hnodup⟩,
      List.forall_mem_cons.2 ⟨fun hxls => hx (List.mem_append_right _ hxls), hdisj⟩⟩

/-- **DAG replay / cut**: a derivation `ls'` from `Δ` replays on top of a derivation `ls` from `Γ`
when every line of `Δ` is in `Γ` or already in `ls`. Lines already present in `ls` (or derived
earlier during the replay) are reused rather than emitted again, so the prepended suffix `ls''` is a
duplicate-free sublist of `ls'` disjoint from `ls`. -/
theorem comp (hΔ : LineProof R Δ ls') (h : LineProof R Γ ls)
    (hΔΓ : ∀ x ∈ Δ, x ∈ Γ ∨ x ∈ ls) :
    ∃ ls'', LineProof R Γ (ls'' ++ ls) ∧ (∀ x ∈ ls', x ∈ ls'' ++ ls) ∧
      ls''.Sublist ls' ∧ ls''.Nodup ∧ ∀ x ∈ ls'', x ∉ ls := by
  induction hΔ with
  | nil => exact ⟨[], h, by simp, .slnil, List.nodup_nil, by simp⟩
  | @hyp ls₀ x _ hx ih =>
    obtain ⟨ls'', h'', hup, hsub, hnodup, hdisj⟩ := ih
    exact comp_step h'' (fun hnot => h''.hyp ((hΔΓ x hx).resolve_right
      fun hxls => hnot (List.mem_append_right _ hxls))) hup hsub hnodup hdisj
  | @step ls₀ r _ hr hp ih =>
    obtain ⟨ls'', h'', hup, hsub, hnodup, hdisj⟩ := ih
    exact comp_step h'' (fun _ => h''.step hr fun p hp' => hup p (hp p hp'))
      hup hsub hnodup hdisj

/-! ### Bounded-overhead prefix growth and simulation -/

/-- `ls'` extends the derivation `ls` by prepending at most `n` lines. -/
def Grows (R : Set (LineRule L)) (Γ : Set L) (ls ls' : List L) (n : ℕ) : Prop :=
  ∃ m, ls' = m ++ ls ∧ LineProof R Γ ls' ∧ m.length ≤ n

namespace Grows

variable {ls₁ ls₂ ls₃ : List L} {m n : ℕ}

/-- Zero prepended lines. -/
theorem refl (h : LineProof R Γ ls₁) : Grows R Γ ls₁ ls₁ 0 :=
  ⟨[], rfl, h, le_rfl⟩

/-- Growth composes, adding the line bounds. -/
theorem trans (h₁ : Grows R Γ ls₁ ls₂ m) (h₂ : Grows R Γ ls₂ ls₃ n) :
    Grows R Γ ls₁ ls₃ (m + n) :=
  let ⟨m₁, e₁, _, hm₁⟩ := h₁
  let ⟨m₂, e₂, hp, hm₂⟩ := h₂
  ⟨m₂ ++ m₁, by simp [e₁, e₂], hp, by simp; omega⟩

/-- The extended list is a valid derivation. -/
theorem lineProof (h : Grows R Γ ls₁ ls₂ n) : LineProof R Γ ls₂ :=
  let ⟨_, _, hp, _⟩ := h
  hp

/-- Growth preserves all earlier lines. -/
theorem subset (h : Grows R Γ ls₁ ls₂ n) : ls₁ ⊆ ls₂ :=
  let ⟨_, e, _, _⟩ := h
  e ▸ List.subset_append_right _ _

/-- Growth within `m` lines is growth within any `n ≥ m` lines. -/
theorem mono (h : Grows R Γ ls₁ ls₂ m) (hmn : m ≤ n) : Grows R Γ ls₁ ls₂ n :=
  let ⟨m₁, e, hp, hm₁⟩ := h
  ⟨m₁, e, hp, hm₁.trans hmn⟩

/-- Growing the empty derivation by at most `n` lines yields at most `n` lines. -/
theorem length_of_nil (h : Grows R Γ [] ls₁ n) : ls₁.length ≤ n :=
  let ⟨_, e, _, hm₁⟩ := h
  by simpa [e] using hm₁

/-- Prepending a list `m₁` of at most `n` lines when `m₁ ++ ls₁` is a derivation. -/
theorem of_append {m₁ : List L} (h : LineProof R Γ (m₁ ++ ls₁)) (hlen : m₁.length ≤ n) :
    Grows R Γ ls₁ (m₁ ++ ls₁) n :=
  ⟨m₁, rfl, h, hlen⟩

/-- Adding one hypothesis line. -/
theorem hyp (h : LineProof R Γ ls₁) {x : L} (hx : x ∈ Γ) : Grows R Γ ls₁ (x :: ls₁) 1 :=
  ⟨[x], rfl, h.hyp hx, le_rfl⟩

/-- Adding one rule step. -/
theorem step (h : LineProof R Γ ls₁) {r : LineRule L} (hr : r ∈ R)
    (hp : ∀ p ∈ r.premises, p ∈ ls₁) : Grows R Γ ls₁ (r.concl :: ls₁) 1 :=
  ⟨[r.concl], rfl, h.step hr hp, le_rfl⟩

/-- Replaying a derivation `ls'` from `Δ` onto `ls₁` via `LineProof.comp` grows `ls₁` by at most
`ls'.length` lines. -/
theorem comp (hΔ : LineProof R Δ ls') (h : LineProof R Γ ls₁)
    (hΔΓ : ∀ x ∈ Δ, x ∈ Γ ∨ x ∈ ls₁) :
    ∃ ls₂, Grows R Γ ls₁ ls₂ ls'.length ∧ ∀ x ∈ ls', x ∈ ls₂ := by
  obtain ⟨m₁, hm₁, hmem, hsub, -, -⟩ := hΔ.comp h hΔΓ
  exact ⟨m₁ ++ ls₁, ⟨m₁, rfl, hm₁, hsub.length_le⟩, hmem⟩

/-- Making every element of `xs` that lies in `Γ` or `ls₁` available on the derivation list costs at
most `xs.length` new lines. -/
theorem collect (h : LineProof R Γ ls₁) {xs : List L} (hxs : ∀ x ∈ xs, x ∈ Γ ∨ x ∈ ls₁) :
    ∃ ls₂, Grows R Γ ls₁ ls₂ xs.length ∧ ∀ x ∈ xs, x ∈ ls₂ := by
  have hp : ∀ ys : List L, LineProof R {x | x ∈ ys} ys := fun ys => by
    induction ys with
    | nil => exact .nil
    | cons x ys ih => exact (ih.mono_hyp fun _ => List.mem_cons_of_mem x).hyp List.mem_cons_self
  exact comp (hp xs) h hxs

/-- **Stepwise simulation over an existing prefix**: if each hypothesis and rule step of `ls` can
extend any target derivation already containing the translated premises by at most `k` lines to
include the translated conclusion, then `ls` extends `ls₀` by at most `k * ls.length` lines. -/
theorem simulate {L₁ L₂ : Type*} {R₁ : Set (LineRule L₁)} {Γ₁ : Set L₁}
    {R₂ : Set (LineRule L₂)} {Γ₂ : Set L₂} (tr : L₁ → L₂) (k : ℕ)
    {ls : List L₁} (h : LineProof R₁ Γ₁ ls) {ls₀ : List L₂} (h₀ : LineProof R₂ Γ₂ ls₀)
    (hhyp : ∀ {ls'}, LineProof R₂ Γ₂ ls' → ∀ x ∈ Γ₁, x ∈ ls →
      ∃ ls'', Grows R₂ Γ₂ ls' ls'' k ∧ tr x ∈ ls'')
    (hstep : ∀ {ls'}, LineProof R₂ Γ₂ ls' → ∀ r ∈ R₁, r.concl ∈ ls →
      (∀ p ∈ r.premises, p ∈ ls ∧ tr p ∈ ls') →
      ∃ ls'', Grows R₂ Γ₂ ls' ls'' k ∧ tr r.concl ∈ ls'') :
    ∃ ls', Grows R₂ Γ₂ ls₀ ls' (k * ls.length) ∧ ∀ x ∈ ls, tr x ∈ ls' := by
  induction h with
  | nil => exact ⟨ls₀, (refl h₀).mono (Nat.zero_le _), by simp⟩
  | @hyp _ x _ hx ih =>
    obtain ⟨ls₁, g₁, h₁⟩ := ih (fun h' y hy hyl => hhyp h' y hy (List.mem_cons_of_mem _ hyl))
      (fun h' r hr hc hp => hstep h' r hr (List.mem_cons_of_mem _ hc)
        fun p hp' => ⟨List.mem_cons_of_mem _ (hp p hp').1, (hp p hp').2⟩)
    obtain ⟨ls₂, g₂, h₂⟩ := hhyp g₁.lineProof x hx List.mem_cons_self
    exact ⟨ls₂, (g₁.trans g₂).mono (le_of_eq (by rw [List.length_cons, Nat.mul_succ])),
      List.forall_mem_cons.2 ⟨h₂, fun y hy => g₂.subset (h₁ y hy)⟩⟩
  | @step _ r _ hr hp ih =>
    obtain ⟨ls₁, g₁, h₁⟩ := ih (fun h' y hy hyl => hhyp h' y hy (List.mem_cons_of_mem _ hyl))
      (fun h' r' hr' hc hp' => hstep h' r' hr' (List.mem_cons_of_mem _ hc)
        fun p hp'' => ⟨List.mem_cons_of_mem _ (hp' p hp'').1, (hp' p hp'').2⟩)
    obtain ⟨ls₂, g₂, h₂⟩ := hstep g₁.lineProof r hr List.mem_cons_self
      fun p hp' => ⟨List.mem_cons_of_mem _ (hp p hp'), h₁ p (hp p hp')⟩
    exact ⟨ls₂, (g₁.trans g₂).mono (le_of_eq (by rw [List.length_cons, Nat.mul_succ])),
      List.forall_mem_cons.2 ⟨h₂, fun y hy => g₂.subset (h₁ y hy)⟩⟩

end Grows

/-- **Stepwise rule simulation**: suppose every hypothesis of `Γ₁` appearing in `ls` has a
derivation in `(R₂, Γ₂)` of at most `k` lines, and every rule `r ∈ R₁` applied in `ls` derives
`tr r.concl` in `(R₂, Γ₂ ∪ {y | y ∈ r.premises.map tr})` in at most `k` lines. Replaying each
step via `LineProof.comp` translates `ls` into a derivation `ls'` in `(R₂, Γ₂)` containing `tr x`
for every `x ∈ ls`, with at most `k * ls.length` lines. -/
theorem simulate {L₁ L₂ : Type*} {R₁ : Set (LineRule L₁)} {Γ₁ : Set L₁}
    {R₂ : Set (LineRule L₂)} {Γ₂ : Set L₂} (tr : L₁ → L₂) (k : ℕ)
    {ls : List L₁} (h : LineProof R₁ Γ₁ ls)
    (hhyp : ∀ x ∈ Γ₁, x ∈ ls → ∃ m, LineProof R₂ Γ₂ m ∧ tr x ∈ m ∧ m.length ≤ k)
    (hstep : ∀ r ∈ R₁, r.concl ∈ ls → (∀ p ∈ r.premises, p ∈ ls) →
      ∃ m, LineProof R₂ (Γ₂ ∪ {y | y ∈ r.premises.map tr}) m ∧
        tr r.concl ∈ m ∧ m.length ≤ k) :
    ∃ ls', LineProof R₂ Γ₂ ls' ∧ (∀ x ∈ ls, tr x ∈ ls') ∧ ls'.length ≤ k * ls.length := by
  obtain ⟨ls', g, hmem⟩ := Grows.simulate tr k h .nil
    (fun h' x hx hxls => let ⟨m, hm, hxm, hlen⟩ := hhyp x hx hxls
      let ⟨ls'', g'', hmem⟩ := Grows.comp hm h' fun _ => .inl
      ⟨ls'', g''.mono hlen, hmem _ hxm⟩)
    (fun h' r hr hc hp => let ⟨m, hm, hcm, hlen⟩ := hstep r hr hc fun p hp' => (hp p hp').1
      let ⟨ls'', g'', hmem⟩ := Grows.comp hm h' fun _ hy =>
        hy.imp id fun hy => let ⟨p, hp', e⟩ := List.mem_map.1 hy; e ▸ (hp p hp').2
      ⟨ls'', g''.mono hlen, hmem _ hcm⟩)
  exact ⟨ls', g.lineProof, hmem, g.length_of_nil⟩

end LineProof

end Cslib.Logic.PL
