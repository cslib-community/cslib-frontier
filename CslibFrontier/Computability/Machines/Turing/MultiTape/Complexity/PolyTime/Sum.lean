/-
Copyright (c) 2026 Samuel Schlesinger, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Sum
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds

/-!
# Polynomial-time sum constructors and case analysis

The two injections retain the supplied payload encoding and add its tag bit. Their certificates
reuse the linear time and space certificates of `ComputableInO.inl` and `.inr`, forgetting
only their explicit bounds. Case analysis retains captured inputs and reuses
`ComputableInO.sumElimSnd`, with a common polynomial bound on both branches. No default value or
finite-domain assumption is needed for either summand or for the output.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.sumInl`, `.sumInr`: tagged sum construction.
* `Turing.MultiTapeTM.ComputableInPolyTime.sumElimSnd`, `.sumElimWithInput`: native case analysis
  retaining captured inputs.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β : Type}

/-- Tag an encoded value as belonging to the left summand. -/
@[fun_prop]
theorem sumInl (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inl (α := α) (β := β)) left (encSum left right) :=
  (ComputableInO.inl left right).computableInPolyTime .self .self

/-- Tag an encoded value as belonging to the right summand. -/
@[fun_prop]
theorem sumInr (left : α ↪ List Bool) (right : β ↪ List Bool) :
    ComputableInPolyTime (Sum.inr (α := α) (β := β)) right (encSum left right) :=
  (ComputableInO.inr left right).computableInPolyTime .self .self

/-- Native tagged-sum case analysis retaining the original captured input. -/
theorem sumElimSnd {α β γ δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool}
    {left : γ → α → δ} {right : γ → β → δ}
    (hl : ComputableInPolyTime (fun p : γ × α => left p.1 p.2) (encPair eg ea) ed)
    (hr : ComputableInPolyTime (fun p : γ × β => right p.1 p.2) (encPair eg eb) ed) :
    ComputableInPolyTime
      (fun p : γ × (α ⊕ β) => p.2.elim (left p.1) (right p.1))
      (encPair eg (encSum ea eb)) ed := by
  obtain ⟨dl, _, hl⟩ := hl.exists_degree
  obtain ⟨dr, _, hr⟩ := hr.exists_degree
  let enc := encPair eg (encSum ea eb)
  have hcost : PolyBounded (fun p : γ × (α ⊕ β) => (enc p).length)
      (fun p => p.2.elim
        (fun a => ((encPair eg ea (p.1, a)).length + 1) ^ dl)
        (fun b => ((encPair eg eb (p.1, b)).length + 1) ^ dr)) := by
    refine ((PolyBounded.self.add (.const 1)).pow (max dl dr)).mono ?_
    rintro ⟨x, a | b⟩
    · apply (Nat.pow_le_pow_left (show (encPair eg ea (x, a)).length + 1 ≤
        (enc (x, .inl a)).length + 1 by simp [enc]) dl).trans
      exact Nat.pow_le_pow_right (by omega) (Nat.le_max_left dl dr)
    · apply (Nat.pow_le_pow_left (show (encPair eg eb (x, b)).length + 1 ≤
        (enc (x, .inr b)).length + 1 by simp [enc]) dr).trans
      exact Nat.pow_le_pow_right (by omega) (Nat.le_max_right dl dr)
  exact (hl.inO.sumElimSnd hr.inO).computableInPolyTime
    (PolyBounded.self.add hcost) (PolyBounded.self.add hcost)

/-- Native case analysis on a computed sum, retaining captured original inputs. -/
theorem sumElimWithInput {α β γ δ : Type} {ea : α ↪ List Bool} {eb : β ↪ List Bool}
    {eg : γ ↪ List Bool} {ed : δ ↪ List Bool}
    {value : γ → α ⊕ β} {left : γ → α → δ} {right : γ → β → δ}
    (hv : ComputableInPolyTime value eg (encSum ea eb))
    (hl : ComputableInPolyTime (fun p : γ × α => left p.1 p.2) (encPair eg ea) ed)
    (hr : ComputableInPolyTime (fun p : γ × β => right p.1 p.2) (encPair eg eb) ed) :
    ComputableInPolyTime (fun p => (value p).elim (left p) (right p)) eg ed := by
  simpa only [Function.comp_def] using (sumElimSnd hl hr).comp
    ((ComputableInPolyTime.id' (encIn := eg)).prod hv)

end Turing.MultiTapeTM.ComputableInPolyTime
