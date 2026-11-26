/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Step
import CslibFrontier.Foundations.Data.List.Forall2
import Mathlib.Tactic.Ring

/-!
# The diagonal, over a finite ring

`Interpreter.diagF D g` guesses a bit. On `1` it accepts with weight `1`; on `0` it applies `D` to
the plain instances of its own argument, for the budgets that `g` guesses. Its value is therefore
`1` plus a weighted sum of the values of `D` (`Interpreter.diagF_ev`). Over a finite ring this is
the diagonal argument against accelerators at a large scale.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `NS1.Diag`.

## Main definitions

* `Interpreter.diagF`.

## Main results

* `Interpreter.diagF_ev`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Interpreter

open Cslib.Circuits.Arithmetic.Separation.Interpreter.Tree

variable {A : Type} [CommRing A] {θ : List Bool → A} {R : Type} [CommRing R] [Algebra A R]

/-- 1 + the value of the argument applied to itself. -/
@[expose] def diagF (D : Tree) (g : Fm) : Fm := .ite .guess (.quote .nil) (app D (ZE .id g))

theorem diagF_ev {κ : List Bool → R} {D z : Tree} {g : Fm} {cg tD : ℕ} {P : List Bool → Prop}
    {lg : List (Run A)}
    {Q : List (Bt × R)} (hg : Ev θ g z lg) (rg : List.Forall₂ (RelG κ P cg) lg Q)
    (hD : ∀ q ∈ Q, Hl θ (Fm.ofTree D) (zq z z q.1) ∧ ∀ r ∈ evl θ (Fm.ofTree D) (zq z z q.1),
        r.cost ≤ tD ∧
      ∀ n ∈ r.bill, P n) :
    ∃ l, Ev θ (diagF D g) z l ∧ (∀ r ∈ l, r.cost ≤ cg + tD + 30 ∧ ∀ n ∈ r.bill, P n) ∧
      val κ l = 1 + (Q.map fun q => q.2 * val κ (evl θ (Fm.ofTree D) (zq z z q.1))).sum := by
  obtain ⟨lZ, rZ, eD⟩ := ZE_app_ev (κ := κ) (D := D) (Dt.id z) hg rg fun q hq => (hD q hq).1
  have hZ := fun s (hs : s ∈ lZ) => rZ.exists_mem_of_mem hs
  set lD :=
      lZ.flatMap fun s => (evl θ (Fm.ofTree D) s.out).map fun t =>
          ((Run.det 1 D).seq s).seq t |>.tick t.out
    with hlD
  have e := Ev.ite (b := .quote .nil) (c := app D (ZE .id g))
      (L := fun r => if r.out = .nil then lD else [.det 1 .nil])
    (Ev.guess (θ := θ) z) (fun r _ h => by rw [ite_eq_right h]; exact .quote .nil z)
        (fun r _ h => by rw [ite_eq_left h]; exact eD)
  have hl : ([.det 1 .nil, .det 1 Tree.one] : List (Run A)).flatMap (fun r =>
      (if r.out = .nil then lD else [.det 1 .nil]).map fun s => (r.seq s).tick s.out) =
      (lD.map fun s => ((Run.det 1 .nil).seq s).tick s.out) ++
          [((Run.det 1 Tree.one).seq (.det 1 .nil)).tick .nil] := by
    simp [Run.det, Tree.one]
  rw [hl] at e
  refine ⟨_, e, ?_, ?_⟩
  · intro r hr
    rw [List.mem_append] at hr
    rcases hr with hr | hr
    · rw [List.mem_map] at hr
      obtain ⟨u, hu, rfl⟩ := hr
      obtain ⟨s, hs, t, ht, h1, h2, -, -⟩ := mem_app hu
      obtain ⟨q, hq, -, h4, h5, h6⟩ := hZ s hs
      rw [h4] at ht
      obtain ⟨c1, p1⟩ := (hD q hq).2 t ht
      refine ⟨?_, ?_⟩
      · simp only [Run.seq, Run.tick, Run.det] at h1 ⊢
        omega
      · intro n hn
        simp only [Run.seq, Run.tick, Run.det, List.nil_append] at hn
        rw [h2, List.mem_append] at hn
        rcases hn with hn | hn
        · exact h5 n hn
        · exact p1 n hn
    · simp only [List.mem_singleton] at hr
      subst hr
      refine ⟨?_, ?_⟩
      · simp only [Run.seq, Run.tick, Run.det]
        omega
      · simp [Run.seq, Run.tick, Run.det]
  · have s1 : val κ (lD.map fun s => ((Run.det 1 .nil).seq s).tick s.out) = val κ lD := by
      simp [val, Function.comp_def, wt_tick, wt_seq, wt_det]
    have s2 : val κ lD = (Q.map fun q => q.2 * val κ (evl θ (Fm.ofTree D) (zq z z q.1))).sum := by
      rw [val_eq_sumF, hlD, sumF_app]
      simp only [val_eq_sumF]
      exact sum_rel (c := fun q : Bt × R => q.2) (o := fun q : Bt × R => zq z z q.1)
        (rZ.imp fun r q hr => ⟨hr.1, hr.2.1⟩)
    rw [← s2, ← s1]
    simp only
        [val, List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
            List.sum_nil,
      wt_tick, wt_seq, wt_det, mul_one, add_zero]
    ring

end Cslib.Circuits.Arithmetic.Separation.Interpreter
