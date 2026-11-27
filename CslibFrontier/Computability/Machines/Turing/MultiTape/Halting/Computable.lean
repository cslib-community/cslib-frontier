/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable.Defs
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.TotalComputability

/-!
# Computable functions and decidable sets

A function is computable (`Turing.MultiTapeTM.IsComputable`) when it is computable within some
bounds in the sense of cslib's `Turing.MultiTapeTM.ComputableInTimeAndSpace`: some machine with a
binary alphabet and finitely many states halts on every encoded input with the encoded value. The
bounds are arbitrary, so this is computability by a total machine
(`Turing.MultiTapeTM.isComputable_iff`). A set is decidable (`Turing.MultiTapeTM.IsDecidable`) when
it is decidable within some bounds in the sense of `Turing.MultiTapeTM.DecidableInTimeAndSpace`,
that is, when its Boolean indicator is computable.

Computable functions compose (`Turing.MultiTapeTM.IsComputable.comp`). The realizing machines
are normalized internally before composition; callers supply plain certificates and need no
normal-form contract. Plain polynomial-time and degree certificates imply computability through
`Turing.MultiTapeTM.ComputableInPolyTime.isComputable` and
`Turing.MultiTapeTM.ComputableInDegree.isComputable`. Decidable sets are closed under complement,
intersection and union.

These are the decidable sets of [Sipser, Definition 3.6][Sipser2013], for the library's native
multi-tape machines. Mathlib's `ComputablePred` is the analogous notion for its partial recursive
functions; `Turing.MultiTapeTM.IsComputable.computable` and
`Turing.MultiTapeTM.IsDecidable.computablePred` in `MultiTape.Halting.Partrec` connect the two
models.

## Main definitions

* `Turing.MultiTapeTM.IsComputable`: computability by a total machine.
* `Turing.MultiTapeTM.IsDecidable`: decidability by a total machine.

## Main results

* `Turing.MultiTapeTM.isComputable_iff`: computability is the existence of a machine computing the
  function without bounds.
* `Turing.MultiTapeTM.IsComputable.comp`, `.prod`, `.ite`,
  `Turing.MultiTapeTM.isComputable_id`, `Turing.MultiTapeTM.IsComputable.of_finite`: closure
  properties.
* `Turing.MultiTapeTM.indicator_eq_true_iff`, `Turing.MultiTapeTM.indicator_eq_false_iff`: the
  indicator of a set.
* `Turing.MultiTapeTM.isDecidable_iff`: decidability through any computable Boolean function.
* `Turing.MultiTapeTM.IsDecidable.compl`, `.inter`, `.union`: decidable sets are closed under
  complement, intersection and union.

## References

* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Turing.MultiTapeTM

universe u

variable {α β γ : Type*} {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
  {encOut : γ ↪ List Bool}

/-! ### Computable functions -/

/-- Functions computable in polynomial time are computable (`IsComputable`). -/
theorem ComputableInPolyTime.isComputable {α β : Type*} {f : α → β}
    {encIn : α ↪ List Bool} {encMid : β ↪ List Bool}
    (h : ComputableInPolyTime f encIn encMid) : IsComputable f encIn encMid :=
  let ⟨_, _, _, h⟩ := h
  h.2.isComputable

/-- A plain degree certificate implies computability, forgetting all numerical bounds. -/
theorem ComputableInDegree.isComputable {f : α → β} {d e : ℕ}
    (h : ComputableInDegree f encIn encMid d e) : IsComputable f encIn encMid :=
  h.computableInPolyTime.isComputable

/-- **Computable functions compose.** -/
theorem IsComputable.comp {f : β → γ} {g : α → β} (hf : IsComputable f encMid encOut)
    (hg : IsComputable g encIn encMid) : IsComputable (f ∘ g) encIn encOut := by
  obtain ⟨_, _, _, _, _, tm₁, h₁⟩ := Internal.TotalComputability.normalizedMachine hg
  obtain ⟨_, _, _, _, _, tm₂, h₂⟩ := Internal.TotalComputability.normalizedMachine hf
  exact ⟨_, _, _, _, inferInstance, tm₂.comp tm₁ true,
    fun a => ((h₁ a).comp (h₂ (g a)) true).computesInTimeAndSpace⟩

/-- The identity is computable. -/
theorem isComputable_id (enc : α ↪ List Bool) : IsComputable id enc enc :=
  (ComputableInPolyTime.of_eq fun _ => rfl).isComputable

/-- Functions on finite types are computable. -/
theorem IsComputable.of_finite [Finite α] (f : α → β) : IsComputable f encIn encMid :=
  (ComputableInPolyTime.of_finite f).isComputable

/-- Pairs of computable functions are computable. -/
theorem IsComputable.prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool} {enc₁ : β₁ ↪ List Bool}
    {enc₂ : β₂ ↪ List Bool} {enc : β₁ × β₂ ↪ List Bool} [PairEncoding enc₁ enc₂ enc]
    {f : α → β₁} {g : α → β₂} (hf : IsComputable f encIn enc₁) (hg : IsComputable g encIn enc₂) :
    IsComputable (fun a => (f a, g a)) encIn enc :=
  let ⟨_, _, hf⟩ := hf
  let ⟨_, _, hg⟩ := hg
  let ⟨_, h⟩ := PairEncoding.pair_mono hf hg
  h.isComputable

/-- Conditional selection between computable Boolean functions is computable. The carrier lives in
`Type`, as `Turing.MultiTapeTM.IsComputable.prod` pairs into `Bool × Bool`. -/
theorem IsComputable.ite {α : Type} {encIn : α ↪ List Bool} {c t e : α → Bool}
    (hc : IsComputable c encIn encBool) (ht : IsComputable t encIn encBool)
    (he : IsComputable e encIn encBool) :
    IsComputable (fun a => if c a then t a else e a) encIn encBool :=
  let hte := ht.prod (enc := encPair encBool encBool) he
  let hcte := hc.prod (enc := encPair encBool (encPair encBool encBool)) hte
  (IsComputable.of_finite (encIn := encPair encBool (encPair encBool encBool))
    (encMid := encBool) fun q : Bool × Bool × Bool => if q.1 then q.2.1 else q.2.2).comp hcte

/-! ### Decidable sets -/

/-- `L` is decidable with respect to the encoding `enc`: its Boolean indicator is computable, by a
machine with a binary alphabet and finitely many states within some time and space bounds. -/
def IsDecidable (L : Set α) (enc : α ↪ List Bool) : Prop :=
  ∃ t s : α → ℕ, DecidableInTimeAndSpace L enc t s

variable {L : Set α} {enc : α ↪ List Bool}

/-- The indicator of `L` is `true` exactly on `L`. -/
theorem indicator_eq_true_iff {a : α} : indicator L a = true ↔ a ∈ L := by
  classical
  by_cases ha : a ∈ L <;> simp [indicator, ha]

/-- The indicator of `L` is `false` exactly off `L`. -/
theorem indicator_eq_false_iff {a : α} : indicator L a = false ↔ a ∉ L := by
  rw [← Bool.not_eq_true, indicator_eq_true_iff]

/-- A set is decidable exactly when its Boolean indicator is computable. -/
theorem isDecidable_iff_isComputable_indicator :
    IsDecidable L enc ↔ IsComputable (indicator L) enc encBool :=
  Iff.rfl

/-- **A set is decidable exactly when some computable Boolean function decides membership.** -/
theorem isDecidable_iff :
    IsDecidable L enc ↔ ∃ f : α → Bool, IsComputable f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true := by
  classical
  rw [isDecidable_iff_isComputable_indicator]
  refine ⟨fun h => ⟨_, h, fun a => by simp [indicator]⟩, fun ⟨f, hf, hL⟩ => ?_⟩
  convert hf using 1
  funext a
  by_cases ha : a ∈ L <;> simp only [indicator, ha, ↓reduceIte]
  · exact ((hL a).mp ha).symm
  · exact (Bool.not_eq_true _).mp (mt (hL a).mpr ha) |>.symm

/-- Membership in a decidable set is decided by a computable Boolean function. -/
theorem IsDecidable.exists_isComputable (h : IsDecidable L enc) :
    ∃ f : α → Bool, IsComputable f enc encBool ∧ ∀ a, a ∈ L ↔ f a = true :=
  isDecidable_iff.mp h

/-- **Decidable sets are closed under complement.** -/
theorem IsDecidable.compl (h : IsDecidable L enc) : IsDecidable Lᶜ enc :=
  let ⟨f, hf, hL⟩ := h.exists_isComputable
  isDecidable_iff.mpr ⟨fun a => !f a, (IsComputable.of_finite (fun b : Bool => !b)).comp hf,
    fun a => by simp [hL a]⟩

@[simp]
theorem isDecidable_compl_iff : IsDecidable Lᶜ enc ↔ IsDecidable L enc :=
  ⟨fun h => compl_compl L ▸ h.compl, IsDecidable.compl⟩

/-- **Decidable sets are closed under intersection**: run both deciders and take the conjunction.
The carrier lives in `Type`, as `Turing.MultiTapeTM.IsComputable.prod` pairs into `Bool × Bool`. -/
theorem IsDecidable.inter {α : Type} {L L' : Set α} {enc : α ↪ List Bool} (h : IsDecidable L enc)
    (h' : IsDecidable L' enc) : IsDecidable (L ∩ L') enc :=
  let ⟨f, hf, hL⟩ := h.exists_isComputable
  let ⟨g, hg, hL'⟩ := h'.exists_isComputable
  isDecidable_iff.mpr ⟨fun a => f a && g a,
    (IsComputable.of_finite (encIn := encPair encBool encBool) (encMid := encBool)
      fun p : Bool × Bool => p.1 && p.2).comp (hf.prod hg), fun a => by simp [hL a, hL' a]⟩

/-- **Decidable sets are closed under union.** -/
theorem IsDecidable.union {α : Type} {L L' : Set α} {enc : α ↪ List Bool} (h : IsDecidable L enc)
    (h' : IsDecidable L' enc) : IsDecidable (L ∪ L') enc := by
  simpa only [Set.compl_inter, compl_compl] using (h.compl.inter h'.compl).compl

end Turing.MultiTapeTM
