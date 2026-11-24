/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Cslib.Computability.Circuit.Boolean.Basic
import CslibFrontier.Computability.Circuit.Frontier.Closure

/-! Checked clients for `SimpleGraph.IndepCount` and `Frontier/Closure.lean`. -/

open Set Filter Cslib.Circuits Cslib.Circuits.Frontier

namespace CslibFrontierTests.FrontierClosure

/-! ### Exact independent-set counts and 2-SAT polarity compression -/

example : (SimpleGraph.pathGraph 0).indepSetCount = 1 :=
  SimpleGraph.indepSetCount_pathGraph 0

/-- Every finite graph has at least one independent set (`∅`), even when complete. -/
example (n : ℕ) : 1 ≤ (⊤ : SimpleGraph (Fin n)).indepSetCount :=
  (⊤ : SimpleGraph (Fin n)).indepSetCount_pos

example : (SimpleGraph.pathGraph 4).indepSetCount = 8 :=
  SimpleGraph.indepSetCount_pathGraph 4

example : (SimpleGraph.pathGraph 5).indepSetCount = 13 :=
  SimpleGraph.indepSetCount_pathGraph 5

/-- The 4-vertex star `K_{1, 3}` with hub `0 : Fin 4`. -/
private def star3 : SimpleGraph (Fin 4) where
  Adj u w := (u = 0 ∧ w ≠ 0) ∨ (w = 0 ∧ u ≠ 0)
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun _ h => by rcases h with ⟨rfl, hne⟩ | ⟨rfl, hne⟩ <;> exact hne rfl⟩

example : star3.indepSetCount = 9 := by
  have h := SimpleGraph.indepSetCount_star star3 0
    (fun _ _ hadj => by rcases hadj with ⟨h1, _⟩ | ⟨h2, _⟩ <;> [exact Or.inl h1; exact Or.inr h2])
    (fun w hw => Or.inl ⟨rfl, hw⟩)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h
  exact h

/-- Any mixed-polarity 2-SAT family on `P_4` has at most `F_6 = 8` solutions. -/
example (S : Set (Fin 4 → Bool))
    (h01 : ∀ x ∈ S, ¬(x 0 = false ∧ x 1 = true))
    (h12 : ∀ x ∈ S, ¬(x 1 = true ∧ x 2 = true))
    (h23 : ∀ x ∈ S, ¬(x 2 = true ∧ x 3 = false)) :
    S.ncard ≤ 8 := by
  change S.ncard ≤ Nat.fib (4 + 2)
  rw [← SimpleGraph.indepSetCount_pathGraph 4]
  refine SimpleGraph.ncard_le_indepSetCount_of_forall_adj (SimpleGraph.pathGraph 4) ?_
  intro u w hadj
  have hu := u.isLt
  have hw := w.isLt
  rcases SimpleGraph.pathGraph_adj.mp hadj with h | h
  · have hcases : (u = 0 ∧ w = 1) ∨ (u = 1 ∧ w = 2) ∨ (u = 2 ∧ w = 3) := by
      simp only [Fin.ext_iff]
      omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨false, true, h01⟩
    · exact ⟨true, true, h12⟩
    · exact ⟨true, false, h23⟩
  · have hcases : (w = 0 ∧ u = 1) ∨ (w = 1 ∧ u = 2) ∨ (w = 2 ∧ u = 3) := by
      simp only [Fin.ext_iff]
      omega
    rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨true, false, fun x hx ⟨h1, h0⟩ => h01 x hx ⟨h0, h1⟩⟩
    · exact ⟨true, true, fun x hx ⟨h2, h1⟩ => h12 x hx ⟨h1, h2⟩⟩
    · exact ⟨false, true, fun x hx ⟨h3, h2⟩ => h23 x hx ⟨h2, h3⟩⟩

/-! ### Forward DAG closure (`D₀(W) ⊊ D*(W)`) on a concrete two-gate Boolean cascade -/

/-- Gate `0` computes `x₀ ∧ x₁`; gate `1` computes `g₀ ∨ x₁`. -/
private def cascadeProg : Program Boolean.signature 2 2 :=
  ((Program.empty : Program Boolean.signature 2 0).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.or, ![Wire.gate 0, Wire.input 1]⟩

/-- Cut wire set `W = {x₀, x₁, g₁}` omits the intermediate wire `g₀`, so `g₁ ∉ D₀(W)` while
`g₁ ∈ D*(W)`. -/
private def cascadeCut : Set (Wire 2 2) :=
  {Wire.input 0, Wire.input 1, Wire.gate 1}

private theorem cascadeProg_lines_one :
    cascadeProg.lines (Fin.last 1) =
      ⟨Boolean.Op.or, Wire.Renaming.castSucc.apply ∘ ![Wire.gate 0, Wire.input 1]⟩ := by
  unfold cascadeProg
  rw [Program.lines_gate_last]
  rfl

private theorem cascadeProg_lines_zero :
    cascadeProg.lines (Fin.last 0).castSucc =
      ⟨Boolean.Op.and, Wire.Renaming.castSucc.apply ∘ Wire.Renaming.castSucc.apply ∘
        ![Wire.input 0, Wire.input 1]⟩ := by
  unfold cascadeProg
  rw [Program.lines_gate_castSucc, Program.lines_gate_last]
  rfl

example : (.gate 1 : Wire 2 2) ∉ cascadeProg.depthOneDetermined cascadeCut := by
  rintro ⟨_, g, heq, hargs⟩
  have hg : g = Fin.last 1 := (Wire.gate.inj heq).symm
  subst hg
  rw [cascadeProg_lines_one] at hargs
  have h0 := hargs (0 : Fin 2)
  simp [cascadeCut, Wire.Renaming.castSucc] at h0

private theorem gate1_mem_forwardDetermined :
    (.gate 1 : Wire 2 2) ∈ cascadeProg.forwardDetermined cascadeCut := by
  refine ⟨by simp [cascadeCut], Fin.last 1, rfl, ?_⟩
  rw [cascadeProg_lines_one]
  intro a
  fin_cases a
  · dsimp only [Function.comp_apply, Matrix.cons_val_zero]
    rw [Wire.Renaming.castSucc_apply]
    change cascadeProg.DagSpan cascadeCut (.gate (Fin.last 0).castSucc)
    refine .gate ?_
    rw [cascadeProg_lines_zero]
    intro b
    fin_cases b <;> exact .base (by simp [cascadeCut])
  · exact .base (by simp [cascadeCut])

example : (.gate 1 : Wire 2 2) ∈ cascadeProg.forwardDetermined cascadeCut :=
  gate1_mem_forwardDetermined

example (x y : Fin 2 → Bool)
    (h0 : x 0 = y 0) (h1 : x 1 = y 1) :
    EqOn (cascadeProg.trace Boolean.interpretation x)
      (cascadeProg.trace Boolean.interpretation y) cascadeCut := by
  refine cascadeProg.eqOn_of_eqOn_sdiff_forwardDetermined
    (D := {(.gate 1 : Wire 2 2)})
    (fun w hw => mem_singleton_iff.mp hw ▸ gate1_mem_forwardDetermined) ?_
  rintro w ⟨hwC, hwD⟩
  rcases hwC with rfl | rfl | hgate
  · exact h0
  · exact h1
  · exact absurd hgate hwD

/-! ### Unary `NOT` gates cost zero in `arityExcess`, and fan-out-`≥ 5` wires slice cleanly -/

/-- Five binary `AND` gates reading `.input 0` (alongside `.input 1`), plus a unary `NOT` gate:
6 gates total, `arityExcess = 5` (the `NOT` gate is free). -/
private def highFanoutProg : Program Boolean.signature 2 6 :=
  (((((((Program.empty : Program Boolean.signature 2 0).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
    ⟨Boolean.Op.not, ![Wire.gate 4]⟩)

private def highFanoutCircuit : Circuit Boolean.signature 2 1 where
  program := highFanoutProg
  outputs _ := .gate 5

example : highFanoutProg.arityExcess = 5 :=
  rfl

example : ∃ (t g' : ℕ) (q : Program (allOpsSignature Bool) 2 g')
    (Acc' : Fin (2 + g') → Set Bool) (S' : Set (Fin 2 → Bool)),
      q.FanInAtMost 2 ∧
      (∀ w : Wire 2 g', q.gateConsumers w ≤ 4) ∧
      g' + 5 * t ≤ 5 ∧
      S'.Nonempty ∧
      (Compiler.network (allWiresCircuit q) (allOpsInterpretation Bool) Acc').accepted = S' := by
  have hfan : highFanoutCircuit.FanInAtMost 2 := highFanoutCircuit.fanInAtMost_two
  have hne : {x : Fin 2 → Bool | ∀ o, highFanoutCircuit.eval Boolean.interpretation x o ∈
      ({true} : Set Bool)}.Nonempty := by
    refine ⟨fun _ => false, fun o => ?_⟩
    have ho : o = 0 := Subsingleton.elim o 0
    subst ho
    exact rfl
  obtain ⟨t, g', q, Acc', S', hqfan, -, -, hle4, hex, -, hS'ne, hacc, -⟩ :=
    exists_sliced_fanout_le_four highFanoutCircuit Boolean.interpretation (fun _ => {true})
      hfan hne
  have hex5 : highFanoutCircuit.program.arityExcess = 5 := rfl
  exact ⟨t, g', q, Acc', S', hqfan, hle4, hex5 ▸ hex, hS'ne, hacc⟩

example {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        ∃ (t g' : ℕ) (q : Program (allOpsSignature Bool) n g'),
          q.FanInAtMost 2 ∧
          (∀ w : Wire n g', q.gateConsumers w ≤ 4) ∧
          q.arityExcess + 5 * t ≤ c.program.arityExcess ∧
          c.program.arityExcess ≤ c.innerSize ∧
          (1 + 2 * Real.pi / (3 * Real.arccos (5 / 6)) - 1 / 100) * n +
              (5 - (1 + 2 * Real.pi / (3 * Real.arccos (5 / 6)))) * t <
            c.program.arityExcess :=
  eventually_switched_slicing_surplus.{0, 0} hSK (by norm_num)

end CslibFrontierTests.FrontierClosure
