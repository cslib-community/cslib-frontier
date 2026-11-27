/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/TuringDegree.lean`)

public import CslibFrontier.Foundations.Computability.RecursiveInCode
public import Mathlib.Algebra.Notation.Indicator
import CslibFrontier.Foundations.Data.List.Primrec

/-!
# The Kleene–Post theorem: incomparable Turing degrees

Kleene and Post showed that the Turing degrees are not linearly ordered: there are sets `A` and
`B` of natural numbers with `A ≰ᵀ B` and `B ≰ᵀ A`. This file proves it by the finite extension
method. Two finite binary strings `σ` and `τ` are built in stages. At stage `2e + 1` the string
`σ` is extended by one bit so that the oracle code `e` relative to any extension of `τ` cannot
compute the characteristic function of `A` at the position of the new bit. Either some extension
of `τ` makes the computation converge, in which case `τ` is extended to it and the bit is chosen
to disagree with the output, or no extension does, in which case the computation diverges for
every oracle extending `τ`. Stage `2e + 2` is symmetric. The stage-bounded evaluator
`Nat.RecursiveIn.Code.evaln` turns the first alternative into a statement about finite strings,
and its soundness and completeness (the use principle) carry the conclusion to the limit sets.

This proves the incomparability statement of Kleene–Post. The construction is noncomputable here:
it decides by classical choice whether some extension forces convergence. The bound
`A, B ≤ᵀ ∅′` from the source, which holds because this question is `Σ₁` and hence decided by
`∅′`, is proved in `CslibFrontier.Foundations.Computability.KleenePostJump`
(`kleene_post_below_jump`).

## Main results

* `Nat.RecursiveIn.kleene_post`: there are sets `A B : Set ℕ` whose characteristic functions are
  Turing incomparable.
* `TuringDegree.exists_incomparable`: the Turing degrees are not linearly ordered.

## References

* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

open Encodable Denumerable
open scoped Computability

namespace Nat.RecursiveIn

namespace KleenePost

open Code

/-- A finite binary string, read as a finite oracle prefix with values in `{0, 1}`. -/
@[expose]
def bits (σ : List Bool) : List ℕ := σ.map Bool.toNat

/-- Converting a finite binary string to its `{0, 1}`-valued prefix is primitive recursive. -/
theorem primrec_bits : _root_.Primrec bits :=
  _root_.Primrec.list_map _root_.Primrec.id
    ((_root_.Primrec.dom_bool Bool.toNat).comp _root_.Primrec.snd).to₂

/-- Converting the first `M` bits of a Boolean sequence via `bits` agrees with `prefixOf`. -/
theorem prefixOf_bool_eq_bits (g : ℕ → Bool) (M : ℕ) :
    bits ((List.range M).map g) = prefixOf (fun n => (g n).toNat) M := by
  simp [bits, prefixOf, Function.comp_def]

/-- Stage bound `p.2.1` in a halting witness `(σ, k, y)`. -/
abbrev witnessStage (p : List Bool × ℕ × ℕ) : ℕ := p.2.1

/-- Output value `p.2.2` in a halting witness `(σ, k, y)`. -/
abbrev witnessOutput (p : List Bool × ℕ × ℕ) : ℕ := p.2.2

/-- Some extension of the finite string `τ` makes the code `c` converge on `x` at some stage.
The witness packs the extension, the stage and the output. -/
@[expose]
def Halts (c : Code) (τ : List Bool) (x : ℕ) : Prop :=
  ∃ p : List Bool × ℕ × ℕ,
    τ <+: p.1 ∧ witnessOutput p ∈ evaln (bits p.1) (witnessStage p) c x

/-- Predicate stating that `e` decodes to a halting witness `(σ, k, y)` for `c` on `x` extending
`τ`. -/
@[expose]
def haltsPred (c : Code) (τ : List Bool) (x : ℕ) (e : ℕ) : Prop :=
  ∃ p : List Bool × ℕ × ℕ,
    Encodable.decode e = some p ∧
      τ <+: p.1 ∧ witnessOutput p ∈ evaln (bits p.1) (witnessStage p) c x

instance (c : Code) (τ : List Bool) (x : ℕ) (e : ℕ) : Decidable (haltsPred c τ x e) :=
  match h : Encodable.decode (α := List Bool × ℕ × ℕ) e with
  | none => isFalse fun ⟨_, hp, _⟩ => by simp [h] at hp
  | some p =>
    decidable_of_iff (τ <+: p.1 ∧ p.2.2 ∈ evaln (bits p.1) p.2.1 c x)
      ⟨fun hp => ⟨p, h, hp⟩, fun ⟨_, hp', hp⟩ => Option.some.inj (h.symm.trans hp') ▸ hp⟩

lemma Halts_iff_exists_haltsPred (c : Code) (τ : List Bool) (x : ℕ) :
    Halts c τ x ↔ ∃ e, haltsPred c τ x e :=
  ⟨fun ⟨p, hp⟩ => ⟨Encodable.encode p, p, Encodable.encodek _, hp⟩, fun ⟨_, p, _, hp⟩ => ⟨p, hp⟩⟩

open Classical in
/-- One finite-extension step against the code `c`: extend `σ` by one bit at position
`σ.length`, and extend `τ` to force convergence of `c` at that position when possible. -/
@[expose]
noncomputable def step (c : Code) (σ τ : List Bool) : List Bool × List Bool :=
  if h : Halts c τ σ.length then
    let e := Nat.find (p := haltsPred c τ σ.length) ((Halts_iff_exists_haltsPred c τ σ.length).mp h)
    match Encodable.decode (α := List Bool × ℕ × ℕ) e with
    | some p => (σ ++ [decide (witnessOutput p = 0)], p.1)
    | none => (σ ++ [false], τ)
  else
    (σ ++ [false], τ)

theorem step_fst (c : Code) (σ τ : List Bool) : ∃ b, (step c σ τ).1 = σ ++ [b] := by
  unfold step
  dsimp only
  split_ifs
  · cases Encodable.decode (α := List Bool × ℕ × ℕ) (Nat.find (p := haltsPred c τ σ.length) _) <;>
      exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

open Classical in
private theorem exists_step_of_halts {c : Code} {σ τ : List Bool} (h : Halts c τ σ.length) :
    ∃ p : List Bool × ℕ × ℕ,
      step c σ τ = (σ ++ [decide (p.2.2 = 0)], p.1) ∧
        τ <+: p.1 ∧ p.2.2 ∈ evaln (bits p.1) p.2.1 c σ.length := by
  obtain ⟨p, hp, hτ, heval⟩ :=
    Nat.find_spec (p := haltsPred c τ σ.length) ((Halts_iff_exists_haltsPred c τ σ.length).mp h)
  exact ⟨p, by simp [step, h, hp], hτ, heval⟩

theorem step_snd (c : Code) (σ τ : List Bool) : τ <+: (step c σ τ).2 := by
  by_cases h : Halts c τ σ.length
  · obtain ⟨_, hstep, hτ, -⟩ := exists_step_of_halts h
    exact hstep ▸ hτ
  · simp [step, h]

/-- The finite string `σ` is an initial segment of the `Bool` sequence `a`. -/
@[expose]
def Agrees (σ : List Bool) (a : ℕ → Bool) : Prop := ∀ i (h : i < σ.length), σ[i] = a i

/-- The diagonalization step: if `a` extends the first output of `step c σ τ` and `b` extends the
second, then `c` relative to `b` does not compute `a`. -/
theorem step_spec {c : Code} {σ τ : List Bool} {a b : ℕ → Bool}
    (hσ : Agrees (step c σ τ).1 a) (hτ : Agrees (step c σ τ).2 b) :
    eval (fun n => (b n).toNat : ℕ → ℕ) c ≠ (fun n => (a n).toNat : ℕ → ℕ) := by
  intro heq
  have hx : (a σ.length).toNat ∈ eval (fun n => (b n).toNat : ℕ → ℕ) c σ.length := by
    rw [heq, PFun.coe_val]; exact Part.mem_some _
  by_cases h : Halts c τ σ.length
  · obtain ⟨p, hstep, -, heval⟩ := exists_step_of_halts h
    rw [hstep] at hσ hτ
    have hv : p.2.2 ∈ eval (fun n => (b n).toNat : ℕ → ℕ) c σ.length :=
      evaln_sound (fun i hi => by
        simp only [bits, List.getElem_map, hτ i (by simpa [bits] using hi), PFun.coe_val]
        exact Part.mem_some _) heval
    have hax : a σ.length = decide (p.2.2 = 0) := by simpa using (hσ σ.length (by simp)).symm
    have hv' : p.2.2 = (a σ.length).toNat := Part.mem_unique hv hx
    cases ha : a σ.length <;> simp only [ha, Bool.toNat_true, Bool.toNat_false] at hv' <;>
      simp [ha, hv'] at hax
  · rw [show step c σ τ = (σ ++ [false], τ) by simp [step, h]] at hσ hτ
    obtain ⟨N, k, hk⟩ := evaln_complete.1 hx
    let M := max N τ.length
    refine h ⟨((List.range M).map b, k, (a σ.length).toNat), ?_, ?_⟩
    · rw [List.prefix_iff_eq_take]
      exact List.ext_getElem (by simp; omega)
        fun i h₁ _ => by simp [hτ i h₁]
    · rw [prefixOf_bool_eq_bits]
      exact evaln_mono (prefixOf_prefix _ (le_max_left _ _)) le_rfl hk

/-- The finite-extension construction. Stage `2e + 1` extends the first string against code `e`,
and stage `2e + 2` extends the second string against code `e`. -/
@[expose]
noncomputable def stage : ℕ → List Bool × List Bool
  | 0 => ([], [])
  | s + 1 =>
    if s % 2 = 0 then step (ofNat Code (s / 2)) (stage s).1 (stage s).2
    else (step (ofNat Code (s / 2)) (stage s).2 (stage s).1).swap

theorem stage_succ_prefix (s : ℕ) :
    (stage s).1 <+: (stage (s + 1)).1 ∧ (stage s).2 <+: (stage (s + 1)).2 := by
  simp only [stage]
  split_ifs
  · obtain ⟨_, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).1 (stage s).2
    exact ⟨hb ▸ List.prefix_append _ _, step_snd _ _ _⟩
  · obtain ⟨_, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).2 (stage s).1
    refine ⟨step_snd _ _ _, ?_⟩
    rw [Prod.snd_swap, hb]
    exact List.prefix_append _ _

theorem stage_prefix {s t : ℕ} (h : s ≤ t) :
    (stage s).1 <+: (stage t).1 ∧ (stage s).2 <+: (stage t).2 := by
  induction h with
  | refl => exact ⟨List.prefix_refl _, List.prefix_refl _⟩
  | step _ ih =>
    exact ⟨ih.1.trans (stage_succ_prefix _).1, ih.2.trans (stage_succ_prefix _).2⟩

theorem length_stage (s : ℕ) :
    (s + 1) / 2 ≤ (stage s).1.length ∧ s / 2 ≤ (stage s).2.length := by
  fun_induction stage s with
  | case1 => simp
  | case2 s h ih =>
    obtain ⟨_, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).1 (stage s).2
    have := (step_snd (ofNat Code (s / 2)) (stage s).1 (stage s).2).length_le
    rw [hb, List.length_append, List.length_singleton]; omega
  | case3 s h ih =>
    obtain ⟨_, hb⟩ := step_fst (ofNat Code (s / 2)) (stage s).2 (stage s).1
    have := (step_snd (ofNat Code (s / 2)) (stage s).2 (stage s).1).length_le
    rw [Prod.fst_swap, Prod.snd_swap, hb, List.length_append, List.length_singleton]; omega

/-- The first limit sequence: its value at `n` is fixed by stage `2 * n + 2`. -/
@[expose]
noncomputable def limA (n : ℕ) : Bool := (stage (2 * n + 2)).1.getD n false

/-- The second limit sequence: its value at `n` is fixed by stage `2 * n + 2`. -/
@[expose]
noncomputable def limB (n : ℕ) : Bool := (stage (2 * n + 2)).2.getD n false

/-- Every stage of a prefix-monotone chain of binary strings agrees with the limit sequence
extracted at indices `idx i` whenever `i < (f (idx i)).length`. -/
theorem agrees_of_prefix {f : ℕ → List Bool} {idx : ℕ → ℕ}
    (hpref : ∀ {s t}, s ≤ t → f s <+: f t) (hlen : ∀ i, i < (f (idx i)).length) (s : ℕ) :
    Agrees (f s) (fun n => (f (idx n)).getD n false) := fun i hi => by
  dsimp only
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hlen i), Option.getD_some,
    (hpref (le_max_left s (idx i))).getElem hi,
    (hpref (le_max_right s (idx i))).getElem (hlen i)]

theorem agrees_limA (s : ℕ) : Agrees (stage s).1 limA :=
  agrees_of_prefix (idx := fun n => 2 * n + 2) (fun h => (stage_prefix h).1)
    (fun i => by have := (length_stage (2 * i + 2)).1; omega) s

theorem agrees_limB (s : ℕ) : Agrees (stage s).2 limB :=
  agrees_of_prefix (idx := fun n => 2 * n + 2) (fun h => (stage_prefix h).2)
    (fun i => by have := (length_stage (2 * i + 2)).2; omega) s

theorem not_limA_le_limB :
    ¬(fun n => (limA n).toNat : ℕ → ℕ) ≤ᵀ (fun n => (limB n).toNat : ℕ → ℕ) := fun h => by
  obtain ⟨c, hc⟩ := turingReducible_iff_exists_code.1 h
  have hs : stage (2 * encode c + 1) =
      step c (stage (2 * encode c)).1 (stage (2 * encode c)).2 := by simp [stage]
  exact step_spec (hs ▸ agrees_limA _) (hs ▸ agrees_limB _) hc

theorem not_limB_le_limA :
    ¬(fun n => (limB n).toNat : ℕ → ℕ) ≤ᵀ (fun n => (limA n).toNat : ℕ → ℕ) := fun h => by
  obtain ⟨c, hc⟩ := turingReducible_iff_exists_code.1 h
  have hs : stage (2 * encode c + 2) =
      (step c (stage (2 * encode c + 1)).2 (stage (2 * encode c + 1)).1).swap := by
    rw [stage]
    simp only [show ¬((2 * encode c + 1) % 2 = 0) by omega, ↓reduceIte,
      show (2 * encode c + 1) / 2 = encode c by omega, ofNat_encode]
  exact step_spec (by simpa [hs] using agrees_limB (2 * encode c + 2))
    (by simpa [hs] using agrees_limA (2 * encode c + 2)) hc

theorem indicator_eq (a : ℕ → Bool) :
    ({n | a n = true} : Set ℕ).indicator 1 = fun n => (a n).toNat :=
  funext fun n => by cases h : a n <;> simp [Set.indicator, h]

end KleenePost

open KleenePost in
/-- **Kleene–Post theorem** (incomparability part): there are sets `A` and `B` of natural numbers
whose characteristic functions are Turing incomparable, `A ≰ᵀ B` and `B ≰ᵀ A`. The sets are built
by finite extension; the bound `A, B ≤ᵀ ∅′` of the source is not part of this statement. -/
theorem kleene_post :
    ∃ A B : Set ℕ, ¬(A.indicator 1 : ℕ → ℕ) ≤ᵀ (B.indicator 1 : ℕ → ℕ) ∧
      ¬(B.indicator 1 : ℕ → ℕ) ≤ᵀ (A.indicator 1 : ℕ → ℕ) :=
  ⟨{n | limA n = true}, {n | limB n = true}, by
    rw [indicator_eq, indicator_eq]; exact ⟨not_limA_le_limB, not_limB_le_limA⟩⟩

end Nat.RecursiveIn

/-- The Turing degrees are not linearly ordered: some two degrees are incomparable. -/
theorem TuringDegree.exists_incomparable : ∃ d₁ d₂ : TuringDegree, ¬d₁ ≤ d₂ ∧ ¬d₂ ≤ d₁ :=
  let ⟨A, B, h₁, h₂⟩ := Nat.RecursiveIn.kleene_post
  ⟨toAntisymmetrization _ (A.indicator 1 : ℕ → ℕ),
    toAntisymmetrization _ (B.indicator 1 : ℕ → ℕ), h₁, h₂⟩
