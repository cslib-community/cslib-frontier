/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Bool
public import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds

/-! # Computational capabilities of pair, option and list encodings

The classes contain proofs of plain computational capabilities, not selected machines or clocks.
Pairing retains independent time and workspace bounds and explicitly charges the output pair.
-/

namespace Turing.MultiTapeTM

universe u v

/-! ### Encodings of pairs, options and lists -/

section Classes

variable {α : Type u} {β : Type v}

/-- `enc` encodes pairs compatibly with `enc₁` and `enc₂`. -/
public class PairEncoding (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool)
    (enc : α × β ↪ List Bool) : Prop where
  /-- Pairing is a combinator: functions `f` and `g` computable from a common input within
  common bounds combine into `fun x => (f x, g x)`, within a constant factor of those bounds, plus
  space for the encoded pair. Different bounds are covered by
  `Turing.MultiTapeTM.PairEncoding.pair_mono`. -/
  pair {γ : Type (max u v)} {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t s : γ → ℕ} :
    ComputableInTimeAndSpace f encIn enc₁ t s →
    ComputableInTimeAndSpace g encIn enc₂ t s →
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t x + 1)) (fun x => c * (s x + (enc (f x, g x)).length + 1))
  /-- The first projection is computable in linear time and space. -/
  fst : ComputableInDegree Prod.fst enc enc₁ 1 1
  /-- The second projection is computable in linear time and space. -/
  snd : ComputableInDegree Prod.snd enc enc₂ 1 1

/-- Construction and default elimination for an explicitly supplied option encoding.
The payload encoding may be inferred from the supplied option encoding; this does not choose
an option encoding from a payload type or encoding. -/
public class OptionEncoding (enc₁ : semiOutParam (α ↪ List Bool)) (enc : Option α ↪ List
  Bool) : Prop where
  /-- Constructor classification has linear resource degree and constant output degree. -/
  isSome : ComputableInDegree Option.isSome enc encBool 1 0
  /-- `some` is computable in linear time and space. -/
  some : ComputableInDegree some enc₁ enc 1 1
  /-- `Option.getD` is computable in linear time and space. -/
  getD (d : α) : ComputableInDegree (fun o => o.getD d) enc enc₁ 1 1

/-- Option capabilities for the empty-word halt protocol of the iteration kernel.
Canonical tagged options do not satisfy this protocol. -/
public class HaltOptionEncoding (enc₁ : α ↪ List Bool) (enc : Option α ↪ List Bool)
    : Prop extends OptionEncoding enc₁ enc where
  /-- The kernel stops on the empty word. -/
  none_eq : enc none = []

/-- `enc` encodes lists compatibly with `enc₁`. -/
public class ListEncoding (enc₁ : α ↪ List Bool) (enc : List α ↪ List Bool) : Prop where
  /-- `List.headD` is computable in linear time and space. -/
  headD (d : α) : ComputableInDegree (fun l => l.headD d) enc enc₁ 1 1
  /-- `List.tail` is computable in linear time and space. -/
  tail : ComputableInDegree List.tail enc enc 1 1
  /-- Testing a list for emptiness is computable in linear time and space. -/
  isEmpty : ComputableInDegree List.isEmpty enc encBool 1 1

/-- Pairing functions computable within different bounds. -/
public theorem PairEncoding.pair_mono {enc₁ : α ↪ List Bool} {enc₂ : β ↪ List Bool}
    {enc : α × β ↪ List Bool} [h : PairEncoding enc₁ enc₂ enc]
    {γ : Type (max u v)}
    {encIn : γ ↪ List Bool} {f : γ → α} {g : γ → β} {t₁ s₁ t₂ s₂ : γ → ℕ}
    (hf : ComputableInTimeAndSpace f encIn enc₁ t₁ s₁)
    (hg : ComputableInTimeAndSpace g encIn enc₂ t₂ s₂) :
    ∃ c, ComputableInTimeAndSpace (fun x => (f x, g x)) encIn enc
      (fun x => c * (t₁ x + t₂ x + 1))
      (fun x => c * (s₁ x + s₂ x + (enc (f x, g x)).length + 1)) :=
  h.pair (γ := γ) (encIn := encIn) (f := f) (g := g)
    (t := fun x => t₁ x + t₂ x) (s := fun x => s₁ x + s₂ x)
    (hf.mono (fun _ => Nat.le_add_right _ _) (fun _ => Nat.le_add_right _ _))
    (hg.mono (fun _ => Nat.le_add_left _ _) (fun _ => Nat.le_add_left _ _))

end Classes

end Turing.MultiTapeTM
