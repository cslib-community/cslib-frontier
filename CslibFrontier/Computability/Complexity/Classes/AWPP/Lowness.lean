/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.AWPP
public import CslibFrontier.Computability.Complexity.Classes.PP.Oracle
import CslibFrontier.Computability.Complexity.Classes.AWPP.OracleWeights
import CslibFrontier.Computability.Complexity.Classes.Oracle.Deterministic
import CslibFrontier.Computability.Complexity.Classes.PP.Characterization
import CslibFrontier.Computability.Complexity.Classes.SharpP.Aggregation
import CslibFrontier.Computability.Complexity.Classes.SharpP.WeightedReplay
import CslibFrontier.Computability.Complexity.Classes.SharpP.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary
import Mathlib.Tactic.Linarith

/-!
# AWPP is low for PP

An AWPP oracle adds no power to the strict-majority verifier class `PPWithOracle`
[Fenner2003]. The simulation weights guessed adaptive oracle replies by amplified GapP
numerators. Amplification depends on the original input, and all queries use a common dyadic
denominator. Polynomial-time native replay and uniform GapP products and sums certify the
resulting ordinary GapP function.

PP-lowness was established by Li (1993); see [Fenner, Fortnow, Kurtz and Li][FennerEtAl2003],
Section 6.1. The constant-error AWPP characterization and amplification used here follow
[Fenner][Fenner2003].

## Main definitions

The verifier classes `AWPP`, `PP`, and `PPWithOracle` are imported from their defining modules.

## Main results

* `PPWithOracle_eq_PP_of_mem_AWPP`: every AWPP language is low for PP.

The result uses the existing strict polynomial-time adaptive word-oracle verifier model; it does
not add a separate characterization by probabilistic oracle machines. Exact majority ties
reject in both classes.

## References

* [S. Fenner, L. Fortnow, S. Kurtz, L. Li, *An Oracle Builder's Toolkit*][FennerEtAl2003],
  Section 6.1.
* [S. Fenner, *PP-Lowness and a Simple Definition of AWPP*][Fenner2003]
-/

public section

namespace Cslib.Complexity

open _root_.Turing (MultiTapePTM)
open _root_.Turing.MultiTapeTM
  (ComputableInPolyTime encBits encBits_apply encBool_apply encPair encUnary length_encPair)
open _root_.Turing.MultiTapeMachine (FiniteConfig)
open _root_.Turing.MultiTapePTM (replyStep)
open Probability.AdaptiveWeights Finset

variable {α : Type} {enc : α ↪ List Bool} {A : Set (List Bool)}

private theorem answerStep_take_iterate {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit) (g : List Bool → Bool)
    (input : List Bool) (T n : ℕ) (hn : n ≤ T) :
    (machine.answerStep (fun q => [g (q.2.take T)]))^[n]
        (FiniteConfig.init machine.initial input) =
      (machine.answerStep (fun q => [g q.2]))^[n]
        (FiniteConfig.init machine.initial input) := by
  have hspace (i : ℕ) : FiniteConfig.SpaceBound input.length i 1
      ((machine.answerStep (fun q => [g q.2]))^[i]
        (FiniteConfig.init machine.initial input)) := by
    induction i with
    | zero => exact FiniteConfig.spaceBound_init _ _ _
    | succ i ih => rw [Function.iterate_succ_apply']; exact machine.spaceBound_answerStep g ih
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega),
      machine.answerStep_bit (fun w => g (w.take T)), machine.answerStep_bit g,
      List.take_of_length_le ((machine.length_pendingRequest_le (hspace n)).trans (by omega))]

private theorem weightedReplay_error {k : ℕ} {Control : Type}
    (machine : MultiTapePTM k Bool Control Unit)
    (input : α → List Bool) (T R : α → ℕ) (H : α × List Bool → ℤ)
    (a : α) (e : ℕ)
    (hw : ∀ w,
      let D := (2 : ℤ) ^ R a
      (0 ≤ H (a, w) ∧ H (a, w) ≤ D) ∧
        (w.take (T a) ∈ A → (2 : ℤ) ^ e * (D - H (a, w)) ≤ D) ∧
        (w.take (T a) ∉ A → (2 : ℤ) ^ e * H (a, w) ≤ D)) :
    (2 : ℤ) ^ e * |weightedReplay machine input T (fun x => 2 ^ R x) H a -
      (2 : ℤ) ^ (R a * T a) * (if (OracleComp.interpret (m := Id) (languageOracle A)
        (machine.run (pure false) (fun op word => OracleComp.query (op, word))
          (T a) (input a))).headD false then 1 else 0)| ≤
      (T a : ℤ) * (2 : ℤ) ^ (R a * T a) := by
  classical
  let g : List Bool → Bool := fun w => decide (w ∈ A)
  let D : ℤ := 2 ^ R a
  let p := fun cfg =>
    if (machine.pendingQuery cfg).isSome then H (a, machine.pendingRequest cfg) else 0
  let answer := fun cfg => if (machine.pendingQuery cfg).isSome then
    g ((machine.pendingRequest cfg).take (T a)) else false
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hstep : (fun cfg => machine.replyStep cfg (answer cfg)) =
      machine.answerStep (fun q => [g (q.2.take (T a))]) := funext fun cfg => by
    rw [machine.answerStep_bit (fun w => g (w.take (T a))) cfg]
    by_cases hq : (machine.pendingQuery cfg).isSome <;> simp [replyStep, answer, hq]
  have h := acceptWeight_error machine.replyStep (fun cfg => cfg.tapes.output.headD false) answer
    (p := p) hD (show 0 ≤ (2 : ℤ) ^ e by positivity)
    (fun cfg => by dsimp only [p]; split; exacts [(hw _).1, ⟨le_rfl, hD⟩])
    (fun cfg => by
      by_cases hq : (machine.pendingQuery cfg).isSome
      · by_cases ha : (machine.pendingRequest cfg).take (T a) ∈ A
        · simpa [branchWeight, p, answer, g, hq, ha] using (hw _).2.1 ha
        · simpa [branchWeight, p, answer, g, hq, ha] using (hw _).2.2 ha
      · simpa [branchWeight, p, answer, hq] using hD)
    (T a) (FiniteConfig.init machine.initial (input a))
  rw [hstep, answerStep_take_iterate machine g (input a) (T a) (T a) le_rfl] at h
  have hout : OracleComp.interpret (m := Id) (languageOracle A)
      (machine.run (pure false) (fun op word => OracleComp.query (op, word)) (T a) (input a)) =
      ((machine.answerStep (fun q => [g q.2]))^[T a]
        (FiniteConfig.init machine.initial (input a))).tapes.output :=
    machine.interpret_run_pure_false (languageOracle A) (T a) (input a)
  simpa only [weightedReplay, p, D, ← pow_mul, hout] using h

private theorem positive_gap_iff {S C B E : ℤ} (hE : 0 < E)
    (herr : 16 * |S - C * E| ≤ E) :
    0 < 4 * S - (2 * B + 1) * E ↔ B < 2 * C := by
  have h1 := le_abs_self (S - C * E)
  have h2 := neg_le_abs (S - C * E)
  refine ⟨fun hpos => by_contra fun hn => ?_, fun hgt => ?_⟩
  · have := mul_le_mul_of_nonneg_right (show 2 * C ≤ B by omega) hE.le
    nlinarith
  · have := mul_le_mul_of_nonneg_right (show B + 1 ≤ 2 * C by omega) hE.le
    nlinarith

/-- Every AWPP language is low for strict-majority polynomial-time oracle verifiers. -/
theorem PPWithOracle_eq_PP_of_mem_AWPP (hA : A ∈ AWPP encBits) (enc : α ↪ List Bool) :
    PPWithOracle A enc = PP enc := by
  classical
  refine Set.Subset.antisymm ?_ (PP_subset_PPWithOracle A enc)
  rintro L ⟨p, V, ⟨program, hprogram, hV⟩, hL⟩
  obtain ⟨k, m, machine, c, d, hrun⟩ := Probability.IsOraclePPTOn.exists_fin_run_pure_false hprogram
  let r : α → ℕ := fun a => p.eval (enc a).length
  let T : α → ℕ := fun a => c * (2 * (enc a).length + 1 + r a + 1) ^ d
  have hr : ComputableInPolyTime r enc encUnary := by dsimp [r]; fun_prop
  have hT : ComputableInPolyTime T enc encUnary := by dsimp [T]; fun_prop
  let e : α → ℕ := fun a => r a + T a + 4
  have he : ComputableInPolyTime e enc encUnary := by dsimp [e]; fun_prop
  obtain ⟨H, hH, R, hR, hweights⟩ := exists_AWPP_queryWeights hA hT he
  let input : α × List Bool → List Bool := encPair enc encBits
  let F := weightedReplay machine input (fun x => T x.1) (fun x => 2 ^ R x.1)
    (fun x => H (x.1.1, x.2))
  have hF : F ∈ GapP (encPair enc encBits) := GapP.weightedReplay_mem machine
    (by dsimp [input]; fun_prop) (by fun_prop) (mem_GapP_of_polyTime (by fun_prop))
    (GapP.comp_mem hH (by fun_prop))
  let S : α → ℤ := fun a => ∑ w : Fin (r a) → Bool, F (a, List.ofFn w)
  let E : α → ℤ := fun a => 2 ^ (R a * T a)
  refine mem_PP_iff_exists_GapP.mpr ⟨fun a => 4 * S a - (2 * (2 : ℤ) ^ r a + 1) * E a,
    GapP.sub_mem' (GapP.mul_mem (mem_GapP_of_polyTime (by fun_prop)) (GapP.sum_bits_mem hF hr))
      (GapP.mul_mem (mem_GapP_of_polyTime (by fun_prop))
        (mem_GapP_of_polyTime (by dsimp [E]; fun_prop))),
    fun a => ?_⟩
  have herror (w : Fin (r a) → Bool) : (2 : ℤ) ^ (r a + T a + 4) *
      |F (a, List.ofFn w) - E a * (if V (a, List.ofFn w) then 1 else 0)| ≤ (T a : ℤ) * E a := by
    have hw := weightedReplay_error machine input (fun x => T x.1) (fun x => R x.1)
      (fun x => H (x.1.1, x.2)) (a, List.ofFn w) (e a) (hweights a)
    have hclock : T a = c * ((encPair enc encBits (a, List.ofFn w)).length + 1) ^ d := by
      simp only [T, length_encPair, encBits_apply, List.length_ofFn]
    have hout := hrun (a, List.ofFn w) (languageOracle A)
    rw [hV] at hout
    simpa only [input, F, E, e, hclock, hout, encBool_apply, List.headD_cons] using hw
  have hbatch := sum_error (show 0 ≤ E a by dsimp [E]; positivity)
    (fun w : Fin (r a) → Bool => F (a, List.ofFn w)) (fun w => V (a, List.ofFn w)) herror
  rw [show (∑ w : Fin (r a) → Bool, if V (a, List.ofFn w) then (1 : ℤ) else 0) =
      acceptCount V a (r a) by
    simp only [acceptCount, card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero],
    mul_comm (E a)] at hbatch
  rw [hL a]
  exact_mod_cast (positive_gap_iff (B := (2 : ℤ) ^ r a)
    (show 0 < E a by dsimp [E]; positivity) hbatch).symm

end Cslib.Complexity
