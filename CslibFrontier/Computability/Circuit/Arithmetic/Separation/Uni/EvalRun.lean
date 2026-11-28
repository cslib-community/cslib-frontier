/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.EvalCompound
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith

/-!
# The universal machine evaluates all formulas

The remaining constructs are `run`, which evaluates two subformulas and then the value of the
first as a program at the value of the second, and `theta`, which reads the value of its
subformula as a name and multiplies by the constant with this name. The induction on the
evaluation (`Interpreter.Ev`) then shows that the machine evaluates every code correctly
(`Uni.EvalsTo.of_ev`); the case of each construct is found from the code by unfolding
`Interpreter.Fm.ofTree` and splitting on the opcode.

## Main results

* `Uni.EvalsTo.run`, `Uni.EvalsTo.theta`.
* `Uni.EvalsTo.of_ev`: the machine evaluates all formulas.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix I (the proof of Proposition I.1, "The pointer machine"), module `Nc.Uni.EvThm3`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Interpreter (Tree Fm Run Ev)

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)} {o a x : Tree}

theorem EvalsTo.run (ho : o.len = 6) {la lb : List (Run A)} {L : Run A → Run A → List (Run A)}
    (iha : EvalsTo θ supp a.hd x la) (ihb : EvalsTo θ supp a.tl x lb)
    (ihc : ∀ r ∈ la, ∀ s ∈ lb, EvalsTo θ supp r.out s.out (L r s)) :
    EvalsTo θ supp (.cons o a) x (la.flatMap fun r => lb.flatMap fun s =>
      (L r s).map fun t => ((r.seq s).seq t).tick t.out) := by
  intro σ H k inp hσ m B h
  rw [plainValue_seq₃]
  simp only [List.forall_mem_flatMap, List.forall_mem_map] at h
  have hC := codeCost_ge (supp := supp)
  refine .mono (hσ.sumTo_decode (B := B - 12) 6 ho rfl fun σ₁ ha hx hk h₂ => ?_) (by omega)
  obtain ⟨p, q, s, hrec, hp, hq⟩ := ha.step.load h₂.wf
  generalize decide (a ≠ .nil) = c at hrec
  cases c
  all_goals
    refine h₂.sumTo_step hrec rfl fun h₃ => ?_
    refine iha _ _ _ _ ⟨h₃.self, hp.step, hx.step.step, rfl⟩ _ _ fun r hr hb σ₄ h₄ hk₄ hv => ?_
    refine h₄.sumTo_step (h₄.frame_mem hk₄) rfl fun h₅ => ?_
    refine ihb _ _ _ _ ⟨h₅.self, (hq.step.mono h₄.heap).step,
      (hx.step.step.mono h₄.heap).step, rfl⟩ _ _ fun s' hs hb' σ₆ h₆ hk₆ hv' => ?_
    refine h₆.sumTo_step (h₆.frame_mem hk₆) rfl fun h₇ => ?_
    exact ihc r hr s' hs _ _ _ _ ⟨(h₇.mono h₅.heap).mono h₃.heap,
      (hv.step.mono h₆.heap).step, hv'.step, hk⟩ _ _ fun t ht hbt σ' hσ' hk' hv'' =>
        .mono (h r hr s' hs t ht (List.append_eq_nil_iff.2
          ⟨List.append_eq_nil_iff.2 ⟨hb, hb'⟩, hbt⟩) σ' hσ' hk' hv'')
          (by push_cast [Run.tick, Run.seq]; linarith)

theorem EvalsTo.theta (hθ : ∀ q, q ∉ supp → θ q = 0) (ho : o.len = 9) {l : List (Run A)}
    (ih : EvalsTo θ supp a x l) : EvalsTo θ supp (.cons o a) x
      (l.map fun r => ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩) := by
  intro σ H k inp hσ m B h
  rw [show plainValue m (l.map fun r => (⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩ : Run A))
      = plainValue (fun r => θ r.out.path * m ⟨r.cost + 1, r.th * θ r.out.path, r.bill, .nil⟩) l
    by simp [plainValue, plainWeight, Function.comp_def, mul_assoc]]
  simp only [List.forall_mem_map] at h
  refine .mono (hσ.sumTo_decode (B := B - 12) 9 ho rfl fun σ₁ ha hx hk h₂ => ?_) (by omega)
  refine ih _ _ _ _ ⟨h₂.self, ha.step, hx.step, rfl⟩ _ _ fun r hr hb σ₃ h₃ hk₃ hv => ?_
  have hfr := h₃.frame_mem hk₃
  by_cases hp : ([] : List Bool) ∈ prefixes supp
  · refine h₃.sumTo_step hfr (dite_eq_left hp) fun h₄ => ?_
    exact .mono (sumTo_readName hθ r.out ⟨[], hp⟩ _ (h₄.mono h₂.heap) hv.step hk (h r hr hb)) (by
      simp only [codeCost, List.length_nil, Nat.sub_zero, Nat.cast_add, Nat.cast_one]
      linarith)
  · rw [hθ _ fun hq => hp (mem_prefixes.2 ⟨_, hq, List.nil_prefix⟩), zero_mul]
    exact h₃.sumTo_zero hfr (dite_eq_right hp) _

/-- **The machine evaluates all formulas.** -/
theorem EvalsTo.of_ev (hθ : ∀ q, q ∉ supp → θ q = 0) {F : Fm} {x : Tree} {l : List (Run A)}
    (h : Ev θ F x l) : ∀ c, Fm.ofTree c = F → EvalsTo θ supp c x l := by
  induction h with
    (rintro (_ | ⟨o, c⟩) hF <;> rw [Fm.ofTree] at hF <;> [skip; split at hF] <;> cases hF)
  | quote => first | exact .nil | exact .quote ‹_›
  | id => exact .id ‹_›
  | hd _ ih => exact .hd_tl true rfl ‹_› (ih _ rfl)
  | tl _ ih => exact .hd_tl false rfl ‹_› (ih _ rfl)
  | cons _ _ iha ihb => exact .cons ‹_› (iha _ rfl) (ihb _ rfl)
  | ite _ _ _ iha ihb ihc =>
    exact .ite ‹_› (iha _ rfl) (fun r hr hn => ihb r hr hn _ rfl) fun r hr hn => ihc r hr hn _ rfl
  | run _ _ _ iha ihb ihc =>
    exact .run ‹_› (iha _ rfl) (ihb _ rfl) fun r hr s hs => ihc r hr s hs _ rfl
  | guess => exact .guess ‹_›
  | fail => exact .fail (by grind)
  | theta _ ih => exact .theta hθ ‹_› (ih _ rfl)
  | mul => exact .mul ‹_› _

end Cslib.Circuits.Arithmetic.Separation.Uni
