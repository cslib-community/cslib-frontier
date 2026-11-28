/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Composition.Recompute
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words

/-!
# Storing an intermediate value

`Turing.MultiTapeTM.ComputableInSpace.bindWith` computes `fun a => g (h a, a)` by storing the value
`h a` and running `g` on it and the input, where `g` is in the context form of
`Turing.MultiTapeTM.ComputableInSpace.loopWith`. The budgets add: the space of `h`, the space of
`g` beyond its stored argument, and the logarithm of the length of the input. Composition by
recomputation (`Turing.MultiTapeTM.ComputableInSpace.comp_space`) instead multiplies the bound by
a constant of both machines, and needs a budget of `g` on the value of `h` alone.

The rule is a loop of two rounds: the registers are the stored value and the optional result,
the first round fills in the result and the second stops.

## Main results

* `Turing.MultiTapeTM.ComputableInSpace.bindWith`: a function of the input and a stored
  intermediate value, within the sum of the budgets.
-/

public section

namespace Turing.MultiTapeTM

open ComputableInSpace

/-- The body of the two-round loop: compute the result unless it is already there. -/
private def bindStep {α β γ : Type} (g : β × α → γ) (p : (β × Option γ) × α) :
    Option (β × Option γ) :=
  if p.1.2.isSome then none else some (p.1.1, some (g (p.1.1, p.2)))

/-- **Storing an intermediate value.** If `h` is computable within `Sh`, and `g` takes the stored
value of `h` and the input within the length of that value plus `Sg`, then `fun a => g (h a, a)`
is computable within `Sh + Sg + log₂ n` on inputs of length `n`. The value `h a` is stored, not
recomputed, so the constant does not depend on how `g` reads it. -/
theorem ComputableInSpace.bindWith {α β γ : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {encC : γ ↪ List Bool} {h : α → β} {g : β × α → γ} {Sh Sg : α → ℕ}
    (hh : ComputableInSpace h encA encB Sh)
    (hg : ComputableInSpace g (encPair encB encA) encC fun p => (encB p.1).length + Sg p.2) :
    ComputableInSpace (fun a => g (h a, a)) encA encC
      fun a => Sh a + Sg a + Nat.log2 (encA a).length := by
  obtain ⟨-, ch, -, hhout⟩ := id hh
  obtain ⟨-, cg, -, hgout⟩ := id hg
  -- the registers in context form, and the parts of the body
  have hreg : ComputableInSpace (fun p : (β × Option γ) × α => p.1)
      (encPair (encPair encB (encOption encC)) encA) (encPair encB (encOption encC))
      fun p => (encPair encB (encOption encC) p.1).length +
        (Sh p.2 + Sg p.2 + Nat.log2 (encA p.2).length) :=
    ((ComputableInLogSpace.fst _ encA).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _)).mono_le fun _ => by omega
  have hgp : ComputableInSpace (fun p : (β × Option γ) × α => g (p.1.1, p.2))
      (encPair (encPair encB (encOption encC)) encA) encC
      fun p => (encPair encB (encOption encC) p.1).length +
        (Sh p.2 + Sg p.2 + Nat.log2 (encA p.2).length) :=
    hg.comp_logSpace_context (f := fun p : (β × Option γ) × α => (p.1.1, p.2))
      (S := fun a => Sh a + Sg a + Nat.log2 (encA a).length)
      (ComputableInLogSpace.pair
        ((ComputableInLogSpace.fst encB (encOption encC)).comp'
          (ComputableInLogSpace.fst _ encA))
        (ComputableInLogSpace.snd _ encA))
      (.of_le fun p => by simp only [length_encPair]; omega) fun _ => by omega
  have hstep : ComputableInSpace (bindStep g) (encPair (encPair encB (encOption encC)) encA)
      (encOption (encPair encB (encOption encC)))
      fun p => (encPair encB (encOption encC) p.1).length +
        (Sh p.2 + Sg p.2 + Nat.log2 (encA p.2).length) :=
    (budget_ite (budget_optionIsSome hreg.snd')
      (ComputableInSpace.budget_const none)
      (budget_optionSome (budget_prod hreg.fst' (budget_optionSome hgp)))).of_enc_eq
      fun _ => rfl
  have hinit : ComputableInSpace (fun a => (h a, (none : Option γ))) encA
      (encPair encB (encOption encC)) fun a => Sh a + Sg a + Nat.log2 (encA a).length :=
    budget_prod (hh.mono_le fun _ => by omega)
      (ComputableInSpace.budget_const _)
  -- the loop of two rounds
  have hloop := ComputableInSpace.loopWith (step := bindStep g)
    (B := fun a => (encPair encB (encOption encC) (h a, some (g (h a, a)))).length +
      (Sh a + Sg a + Nat.log2 (encA a).length))
    (fun a j => if j = 0 then (h a, none) else (h a, some (g (h a, a)))) (fun _ => 1)
    hinit hstep (fun _ => rfl)
    (fun a j hj => by
      obtain rfl : j = 0 := by omega
      simp [bindStep])
    (fun a => by simp [bindStep])
    (fun a j hj => by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
      · simp
      · simp)
  refine (budget_comp_linear
    (of_inO (.of_linear (ListEncoding.tail encBool)) :
      ComputableInSpace List.tail encBits encBits fun w => (encBits w).length)
    (hloop.snd'.of_enc_eq (encC := encBits) (g := fun a => encOption encC (some (g (h a, a))))
      fun a => by simp)).of_enc_eq (encC := encC) (fun a => by simp) |>.weaken
    ⟨4 + 2 * ch + cg * (ch + 1), fun a => ?_⟩
  -- the stored value and the result are within the budgets of `h` and `g`
  have h₁ := hhout a
  have h₂ := hgout (h a, a)
  simp only [length_encPair, encOption_some, List.length_cons] at h₂ ⊢
  generalize (encB (h a)).length = X at *
  generalize (encC (g (h a, a))).length = Y at *
  generalize hL : Sh a + Sg a + Nat.log2 (encA a).length + 1 = L
  have hX : ch * (Sh a + 1) ≤ ch * L := Nat.mul_le_mul_left ch (by omega)
  have hY : cg * (X + Sg a + 1) ≤ cg * (ch * L + L) :=
    Nat.mul_le_mul_left cg (by omega)
  have : (4 + 2 * ch + cg * (ch + 1)) * L = 4 * L + 2 * (ch * L) + cg * (ch * L + L) := by ring
  omega

end Turing.MultiTapeTM
