/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FunProp
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredBind
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength

/-!
# Stored registers next to a read-only input, within a fixed workspace budget

A body of `Turing.MultiTapeTM.ComputableInSpace.loopWith` or
`Turing.MultiTapeTM.ComputableInSpace.recWith` is a function of a pair `(r, a)` of stored
registers and the input, encoded by `encPair encR encA`, within a budget that charges the
registers and not the input. The rules of this module are the leaves of such a certificate, in
the budget-preserving form of `Turing.MultiTapeTM.ComputableInSpace.budget_prod`, so that `space`
composes the rest: the registers, a function of the input alone, a certified function of other
registers, the length of the input, and the bit of the input at a computed position.

Every rule asks that the budget cover the registers and the logarithm of the length of the
input, as the hypothesis
`(fun p => (encR p.1).length + Nat.log2 (encA p.2).length) ≼ Bs`. For a budget that is a sum
with these two summands, `space` proves it.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.budget_registers`: the stored registers.
* `Turing.MultiTapeTM.ComputableInSpace.budget_ofInput`: a function of the input alone.
* `Turing.MultiTapeTM.ComputableInSpace.budget_subst`: a certified function of other registers
  and the input, on registers computed from the stored ones by a logspace map.
* `Turing.MultiTapeTM.ComputableInSpace.assoc_context`: registers next to the registers of an
  enclosing rule.
* `Turing.MultiTapeTM.ComputableInSpace.inputLength`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_inputLength`,
  `Turing.MultiTapeTM.ComputableInSpace.budget_inputBit`: the length of the input, and its bit at
  a computed position.
-/

public section

namespace Turing.MultiTapeTM.ComputableInSpace

variable {α ρ σ β γ : Type} {encA : α ↪ List Bool} {encR : ρ ↪ List Bool}
  {encS : σ ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {Bs : ρ × α → ℕ}

/-- The budget `Bs` covers the registers and the logarithm of the length of the input. -/
abbrev CoversContext (encR : ρ ↪ List Bool) (encA : α ↪ List Bool) (Bs : ρ × α → ℕ) : Prop :=
  (fun p : ρ × α => (encR p.1).length + Nat.log2 (encA p.2).length) ≼ Bs

/-- The stored registers, within a budget that covers them. -/
@[fun_prop]
theorem budget_registers (h : CoversContext encR encA Bs) :
    ComputableInSpace (fun p : ρ × α => p.1) (encPair encR encA) encR Bs :=
  ((ComputableInLogSpace.fst encR encA).inSpace_context
    (.of_le fun _ => Nat.le_add_right _ _)).weaken h

/-- A function of the input alone next to stored registers: within a budget that covers the
registers and the budget of the function. -/
theorem budget_ofInput {f : α → β} {S : α → ℕ} (hf : ComputableInSpace f encA encB S)
    (h : CoversContext encR encA Bs) (hS : (fun p : ρ × α => S p.2) ≼ Bs) :
    ComputableInSpace (fun p : ρ × α => f p.2) (encPair encR encA) encB Bs :=
  (hf.comp_logSpace (ComputableInLogSpace.snd encR encA)).weaken (.add hS
    (BigOLe.trans ⟨3, fun p => by
      have := log2_length_encPair_le encR encA p
      dsimp only
      omega⟩ h))

/-- A certified function of registers and the input, on registers that a logspace map computes
from the stored ones: within a budget that covers the stored registers and the budget of the
function on the new ones. The new registers are recomputed, not stored. -/
theorem budget_subst {g : σ × α → γ} {T : σ × α → ℕ} {f : ρ × α → σ}
    (hg : ComputableInSpace g (encPair encS encA) encC T)
    (hf : ComputableInLogSpace f (encPair encR encA) encS)
    (h : CoversContext encR encA Bs) (hT : (fun p : ρ × α => T (f p, p.2)) ≼ Bs) :
    ComputableInSpace (fun p : ρ × α => g (f p, p.2)) (encPair encR encA) encC Bs :=
  (hg.comp_logSpace (f := fun p : ρ × α => (f p, p.2))
    (.pair hf (.snd encR encA))).weaken (.add hT
    (BigOLe.trans ⟨3, fun p => by
      have := log2_length_encPair_le encR encA p
      dsimp only
      omega⟩ h))

/-- **Registers next to the registers of an enclosing rule.** A function of registers `(s, r)` and
the input is also a function of the registers `s` and the context `(r, a)`, in which the outer
registers `r` and the input are read-only. This is the form in which a rule such as
`Turing.MultiTapeTM.ComputableInSpace.recWith` asks for a part when the rule is itself applied to
stored registers and an input. -/
theorem assoc_context {g : (σ × ρ) × α → γ} {T : (σ × ρ) × α → ℕ}
    (hg : ComputableInSpace g (encPair (encPair encS encR) encA) encC T) :
    ComputableInSpace (fun q : σ × ρ × α => g ((q.1, q.2.1), q.2.2))
      (encPair encS (encPair encR encA)) encC fun q =>
        T ((q.1, q.2.1), q.2.2) + (encS q.1).length + (encR q.2.1).length +
          Nat.log2 (encA q.2.2).length :=
  (hg.comp_logSpace (f := fun q : σ × ρ × α => ((q.1, q.2.1), q.2.2))
    (.pair (.pair (.fst encS _) ((ComputableInLogSpace.fst encR encA).comp' (.snd encS _)))
      ((ComputableInLogSpace.snd encR encA).comp' (.snd encS _)))).weaken ⟨5, fun q => by
        have h₁ := log2_length_encPair_le encS (encPair encR encA) q
        have h₂ := log2_length_encPair_le encR encA q.2
        dsimp only
        omega⟩

/-- The length of the input, in binary, within the logarithm of that length. -/
theorem inputLength (encA : α ↪ List Bool) :
    ComputableInSpace (fun a => (encA a).length) encA encNat fun a => Nat.log2 (encA a).length :=
  (computableInLogSpace_bitsLength.comp' (.of_eq (encMid := encBits) (f := fun a : α => encA a)
    fun _ => rfl)).inSpace_of_length_log ⟨1, fun a => by
      simpa only [one_mul] using length_encNat_le_log2 (le_refl (encA a).length)⟩

/-- The length of the input next to stored registers, within a budget that covers them. -/
theorem budget_inputLength (h : CoversContext encR encA Bs) :
    ComputableInSpace (fun p : ρ × α => (encA p.2).length) (encPair encR encA) encNat Bs :=
  budget_ofInput (inputLength encA) h
    (BigOLe.trans (.of_le fun _ => Nat.le_add_left _ _) h)

/-- **The bit of the input at a computed position**, `none` past its end: the position is any
function of the registers and the input within the budget; it is stored, and the input is read
there (`Turing.MultiTapeTM.ComputableInSpace.bindWith`,
`Turing.MultiTapeTM.ComputableInSpace.inputBit`). -/
theorem budget_inputBit {i : ρ × α → ℕ} (hi : ComputableInSpace i (encPair encR encA) encNat Bs)
    (h : CoversContext encR encA Bs) :
    ComputableInSpace (fun p : ρ × α => (encA p.2)[i p]?) (encPair encR encA)
      (encOption encBool) Bs := by
  have hread := (inputBit encA).comp_logSpace_context (encR := encNat)
    (encA := encPair encR encA) (f := fun q : ℕ × ρ × α => (q.1, q.2.2))
    (S := fun p => 2 * (encR p.1).length + Nat.log2 (encA p.2).length + 2)
    (.pair (.fst encNat _) ((ComputableInLogSpace.snd encR encA).comp' (.snd encNat _)))
    (.of_le fun q => by dsimp only; omega) (log2_length_encPair_le encR encA)
  obtain ⟨c, hc⟩ := h
  refine (bindWith (g := fun q : ℕ × ρ × α => (encA q.2.2)[q.1]?)
    (Sg := fun p => 2 * (encR p.1).length + Nat.log2 (encA p.2).length + 2) hi hread).weaken
    ⟨4 * c + 5, fun p => ?_⟩
  have h₁ := log2_length_encPair_le encR encA p
  have h₂ := hc p
  have h₃ : (4 * c + 5) * (Bs p + 1) = 4 * (c * (Bs p + 1)) + 5 * (Bs p + 1) := by ring
  dsimp only at h₂ ⊢
  omega

end Turing.MultiTapeTM.ComputableInSpace
