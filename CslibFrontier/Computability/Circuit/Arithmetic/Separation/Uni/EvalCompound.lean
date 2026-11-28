/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.EvalCore
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith

/-!
# The universal machine evaluates formulas: `hd`, `tl`, `cons`, `ite`

For a construct with subformulas the machine pushes a frame, evaluates the first subformula, and
on the return to the frame goes on: it takes a subtree of the value (`hd`, `tl`), evaluates the
second subformula and builds a record (`cons`), or chooses the subformula to evaluate
(`ite`). Each case is a chain of forced steps (`Uni.InMode.sumTo_step`) between the uses of the
induction hypotheses.

## Main results

* `Uni.EvalsTo.hd_tl` (both `hd` and `tl`), `Uni.EvalsTo.cons`, `Uni.EvalsTo.ite`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Appendix I (the proof of Proposition I.1, "The pointer machine"), module `Nc.Uni.EvThm2`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Interpreter (Tree Fm Run)

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)} {o a x : Tree}

/-- `hd` (for `b = true`, opcode `2`) and `tl` (for `b = false`, opcode `3`). -/
theorem EvalsTo.hd_tl (b : Bool) {j : Fin 11} (hj : j = bif b then 2 else 3) (ho : o.len = j)
    {l : List (Run A)} (ih : EvalsTo θ supp a x l) :
    EvalsTo θ supp (.cons o a) x (l.map fun r => r.tick (bif b then r.out.hd else r.out.tl)) := by
  intro σ H k inp hσ m B h
  rw [plainValue_map_tick]
  simp only [List.forall_mem_map] at h
  have hC := codeCost_ge (supp := supp)
  subst hj
  cases b
  all_goals
    refine .mono (hσ.sumTo_decode (B := B - 12) _ ho rfl fun σ₁ ha hx hk h₂ => ?_) (by omega)
    refine ih _ _ _ _ ⟨h₂.self, ha.step, hx.step, rfl⟩ _ _ fun r hr hb σ₃ h₃ hk₃ hv => ?_
    refine h₃.sumTo_step (h₃.frame_mem hk₃) rfl fun h₄ => ?_
    obtain ⟨p, q, s, hrec, hp, hq⟩ := hv.step.load h₄.wf
    generalize decide (r.out ≠ .nil) = c at hrec
    cases c <;> refine h₄.sumTo_step hrec rfl fun h₅ => ?_ <;>
      exact .mono (h r hr hb _ (h₅.mono h₂.heap) hk (by first | exact hp.step | exact hq.step))
        (by push_cast [Run.tick]; linarith)

theorem EvalsTo.cons (ho : o.len = 4) {la lb : List (Run A)} (iha : EvalsTo θ supp a.hd x la)
    (ihb : EvalsTo θ supp a.tl x lb) : EvalsTo θ supp (.cons o a) x
      (la.flatMap fun r => lb.map fun s => (r.seq s).tick (.cons r.out s.out)) := by
  intro σ H k inp hσ m B h
  rw [plainValue_seq m la (fun _ => lb) fun r s => .cons r.out s.out]
  simp only [List.forall_mem_flatMap, List.forall_mem_map] at h
  have hC := codeCost_ge (supp := supp)
  refine .mono (hσ.sumTo_decode (B := B - 12) 4 ho rfl fun σ₁ ha hx hk h₂ => ?_) (by omega)
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
    exact .mono (h r hr s' hs (List.append_eq_nil_iff.2 ⟨hb, hb'⟩) _
      ((h₇.mono h₅.heap).mono h₃.heap) hk
      ⟨_, _, _, mem_heap_step σ₆ _ _ _ _, (hv.step.mono h₆.heap).step, hv'.step⟩)
      (by push_cast [Run.tick, Run.seq]; linarith)

theorem EvalsTo.ite (ho : o.len = 5) {la : List (Run A)} {L : Run A → List (Run A)}
    (iha : EvalsTo θ supp a.hd x la)
    (ihb : ∀ r ∈ la, r.out ≠ .nil → EvalsTo θ supp a.tl.hd x (L r))
    (ihc : ∀ r ∈ la, r.out = .nil → EvalsTo θ supp a.tl.tl x (L r)) :
    EvalsTo θ supp (.cons o a) x
      (la.flatMap fun r => (L r).map fun s => (r.seq s).tick s.out) := by
  intro σ H k inp hσ m B h
  rw [plainValue_seq m la L fun _ s => s.out]
  simp only [List.forall_mem_flatMap, List.forall_mem_map] at h
  have hC := codeCost_ge (supp := supp)
  refine .mono (hσ.sumTo_decode (B := B - 12) 5 ho rfl fun σ₁ ha hx hk h₂ => ?_) (by omega)
  obtain ⟨p, q, s, hrec, hp, hq⟩ := ha.step.load h₂.wf
  generalize decide (a ≠ .nil) = c at hrec
  cases c
  all_goals
    refine h₂.sumTo_step hrec rfl fun h₃ => ?_
    refine iha _ _ _ _ ⟨h₃.self, hp.step, hx.step.step, rfl⟩ _ _ fun r hr hb σ₄ h₄ hk₄ hv => ?_
    refine h₄.sumTo_step (h₄.frame_mem hk₄) rfl fun h₅ => ?_
    have ih : EvalsTo θ supp (bif decide (r.out ≠ .nil) then a.tl.hd else a.tl.tl) x (L r) := by
      by_cases hn : r.out = .nil
      · simpa [hn] using ihc r hr hn
      · simpa [hn] using ihb r hr hn
    obtain ⟨y₁, y₂, y₃, hy, -, -⟩ := hv.step.load h₅.wf
    generalize decide (r.out ≠ .nil) = d at hy ih
    cases d
    all_goals
      refine h₅.sumTo_step hy rfl fun h₆ => ?_
      obtain ⟨z₁, z₂, z₃, hz, hz₁, hz₂⟩ := ((hq.step.mono h₄.heap).step.step).load h₆.wf
      generalize decide (a.tl ≠ .nil) = e at hz
      cases e <;> refine h₆.sumTo_step hz rfl fun h₇ => ?_ <;>
        exact ih _ _ _ _ ⟨h₇.mono h₃.heap, by first | exact hz₁.step | exact hz₂.step,
          (hx.step.step.mono h₄.heap).step.step.step, hk⟩ _ _ fun s' hs hb' σ' hσ' hk' hv' =>
            .mono (h r hr s' hs (List.append_eq_nil_iff.2 ⟨hb, hb'⟩) σ' hσ' hk' hv')
              (by push_cast [Run.tick, Run.seq]; linarith)

end Cslib.Circuits.Arithmetic.Separation.Uni
