/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating.StoppingProduct
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.WorkTapePredicate
import
CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.FastContraction.StoppingQuery.RouteTime

/-!
A complete native terminal interprets every entry as zero, while retaining the circuit's actual
Boolean constants. One fixed compiled machine is exercised at zero, one, two and three vertices,
including the empty product and a padded product of positive height. Every coefficient, precision
bit and claim is covered, with arbitrary host input and arbitrarily long protected assignment.
-/

namespace CslibFrontierTests.StoppingProduct

open Turing Turing.MultiTapeTM Turing.MultiTapeATM Cslib GaloisRingArith
open Cslib.Circuits.Boolean Cslib.Circuits.Frontier.FastContraction
open StoppingQuery.ProductRouting

private def response (p : Position) : Bool := decide (terminalValue (fun _ => false) p = p.claim)

private theorem response_polyTime : ComputableInPolyTime response encPosition encBool := by
  have hconst : ComputableInPolyTime
      (fun op : Op => match op with | .const b => b | _ => false)
      encOp encBool := ComputableInPolyTime.of_finite _
  have hv : ComputableInPolyTime (terminalValue (fun _ => false)) encPosition encBool := by
    unfold terminalValue
    exact ComputableInPolyTime.ite_decide
      (ComputableInPolyTime.decide_eq'
        (StoppingQuery.Product.encNodeData_kind_polyTime
          (encPosition_data_polyTime ComputableInPolyTime.id'))
        (ComputableInPolyTime.const 4))
      (ComputableInPolyTime.const false) (hconst.comp operation_polyTime)
  exact ComputableInPolyTime.decide_eq' hv (by fun_prop)

private theorem view_terminal {k : ℕ} {S : Type} (runner : MultiTapeATM (k + 2) Bool S)
    (host word data : List Bool) :
    viewCfg Fin.castSuccEmb
      ((TwoWordInput.ready (Fin.last (k + 2)) (Fin.natAdd k 0).castSucc host word data).withState
        (some runner.toPTM.initial)) =
      (WorkTapePredicate.config host data).withState (some runner.toPTM.initial) := by
  apply Cfg.ext <;> try rfl
  funext i z
  change tapeOfList (if i.castSucc = Fin.last (k + 2) then word else
    if i.castSucc = (Fin.natAdd k (0 : Fin 2)).castSucc then data else []) z =
      tapeOfList (Function.update (fun _ => []) (Fin.natAdd k 0) data i) (z - 0)
  simp only [Fin.castSucc_ne_last, ↓reduceIte, Fin.castSucc_inj, sub_zero]
  by_cases hi : i = Fin.natAdd k 0 <;> simp [hi]

private theorem expected_value (vertices : Fin 4) (coefficient : Fin (modulus 0).length)
    (bit : Fin 3) :
    ((representative 0 3 (∏ _ ∈ Finset.range vertices.val,
      (0 : Ring 3 (modulus 0)))).coeff coefficient.val).val.testBit bit.val =
        decide (vertices.val = 0 ∧ coefficient.val = 0 ∧ bit.val = 0) := by
  fin_cases vertices
  · simpa [InterpolationGrid.factorBit, InterpolationGrid.factor] using
      (InterpolationGrid.factorBit_eq 0 3 0 0 0 coefficient bit).symm
  all_goals simp [representative]

-- No terminal-machine hypothesis remains: the polynomial predicate runner is constructed here.
example : ∃ (U : ℕ) (assignmentSource querySource : Fin U) (Q : Type) (_ : Finite Q)
    (atm : MultiTapeATM U Bool Q) (C D cL dL : ℕ),
    ∀ (host word : List Bool) (vertices : Fin 4) (coefficient : Fin (modulus 0).length)
      (bit : Fin 3) (claim : Bool),
      let parameters : StoppingQuery.Product.Parameters := ⟨0, 3, vertices.val⟩
      let position := root parameters coefficient.val bit.val claim
      let bound := metadataBound parameters (2 ^ Nat.clog 2 vertices.val)
        (Nat.clog 2 vertices.val)
      let start := (TwoWordInput.ready assignmentSource querySource host word
        (encPosition position)).withState (some atm.toPTM.initial)
      let time := StoppingProduct.clock C D parameters (cL * (bound + 1) ^ dL)
      atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
        decide (vertices.val = 0 ∧ coefficient.val = 0 ∧ bit.val = 0) = claim) := by
  obtain ⟨k, S, hS, runner, cL, dL, hr⟩ :=
    WorkTapePredicate.exists_alternating_of_polyTime response_polyTime
  let assignment := Fin.last (k + 2)
  let query := (Fin.natAdd k (0 : Fin 2)).castSucc
  let terminal := runner.extendTapes Fin.castSuccEmb
  obtain ⟨U, ass, src, Q, hQ, atm, C, D, _, h⟩ := StoppingProduct.exists_evaluator
    assignment query (Fin.castSucc_ne_last _).symm terminal
  refine ⟨U, ass, src, Q, hQ, atm, C, D, cL, dL, ?_⟩
  intro host word vertices coefficient bit claim parameters position bound start time
  have ht : ∀ p, Valid parameters (2 ^ Nat.clog 2 vertices.val)
        (Nat.clog 2 vertices.val) p → player p = none →
      let cfg := (TwoWordInput.ready assignment query host word (encPosition p)).withState
        (some terminal.toPTM.initial)
      terminal.HaltsWithin (cL * (bound + 1) ^ dL) cfg ∧
        (terminal.AcceptsWithin (cL * (bound + 1) ^ dL) cfg ↔
          StoppingQuery.value 0 3 0 vertices.val (fun _ _ => 0) (address p) = p.claim) := by
    intro p hp hplayer cfg
    obtain ⟨ha, hh⟩ := hr p host
    have hbudget := Nat.mul_le_mul_left cL (Nat.pow_le_pow_left
      (Nat.add_le_add_right hp.length_encPosition_le 1) dL)
    have hv := view_terminal runner host word (encPosition p)
    have hhalt := (runner.haltsWithin_extendTapes_iff Fin.castSuccEmb _ cfg).mpr
      (hv ▸ hh.mono hbudget)
    have haccept : runner.AcceptsWithin (cL * (bound + 1) ^ dL)
        ((WorkTapePredicate.config host (encPosition p)).withState
          (some runner.toPTM.initial)) ↔ response p = true :=
      ⟨fun h => ha.mp (h.of_halted_stepCoins hh), fun h => (ha.mpr h).mono hbudget⟩
    have hvalue := terminal_value p (fun _ _ => 0) hplayer
    rw [hp.parameters] at hvalue
    have he : StoppingQuery.entryBit 0 3 (fun _ _ => 0) = (fun _ => false) := by
      funext e
      simp [StoppingQuery.entryBit, representative]
    change StoppingQuery.value 0 3 0 vertices.val (fun _ _ => 0) (address p) =
      terminalValue (StoppingQuery.entryBit 0 3 (fun _ _ => 0)) p at hvalue
    rw [he] at hvalue
    refine ⟨hhalt, ?_⟩
    refine ((runner.acceptsWithin_extendTapes_iff Fin.castSuccEmb _ cfg).trans
      (hv ▸ Iff.rfl)).trans (haccept.trans ?_)
    simp [response, hvalue]
  have hs := h host word parameters (fun _ _ => 0) (cL * (bound + 1) ^ dL)
    ht coefficient bit claim
  refine ⟨hs.1, hs.2.trans ?_⟩
  change ((representative 0 3 (∏ _ ∈ Finset.range vertices.val,
    (0 : Ring 3 (modulus 0)))).coeff coefficient.val).val.testBit bit.val = claim ↔ _
  rw [expected_value]

end CslibFrontierTests.StoppingProduct
