/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module

import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.LayerTally
import CslibFrontier.Computability.Circuit.Boolean.SemiUnbounded.MinIsolation

/-!
# Tests for min-isolation of proof trees in layered semi-unbounded circuits

Checked witnesses exercising:
1. A concrete two-AND-level normal-form circuit with multiple distinct proof trees per true gate,
   a false gate with no proof trees, an explicit isolating seed, and the Justesen-family
   existence and weight bounds.
2. A fan-in-two AND gate with duplicate inputs (`binary c c`), verifying that min-isolation
   still isolates the gate when `c` is isolated.
3. The `x₁ ∨ x₂` counterexample showing that dropping the AND-first-layer normal-form condition
   leaves two distinct weight-0 proof trees under every code and every seed, whereas inserting an
   AND layer above the leaves restores min-isolation.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.SemiUnboundedMinIsolation

open Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit

/-! ## 1. A two-AND-level normal-form circuit with multiple proof trees and a false gate

Gates on `Fin 9`:
* Layer 0 (leaves): `0 = true`, `1 = true`, `2 = false`.
* Layer 1 (AND-level 0):
  - `3 = AND(0, 1)` (true)
  - `4 = AND(0)` (true, unary)
  - `5 = AND(0, 2)` (false)
* Layer 2 (OR-level 0):
  - `6 = OR(3, 4, 5)` (true, two distinct proof trees via `3` and `4`)
* Layer 3 (AND-level 1):
  - `7 = AND(6, 6)` (true, duplicate-child binary AND gate: 4 distinct proof trees!)
* Layer 4 (OR-level 1):
  - `8 = OR(7)` (true, 4 distinct proof trees)
-/

private def exLayer : Fin 9 → ℕ
  | ⟨0, _⟩ | ⟨1, _⟩ | ⟨2, _⟩ => 0
  | ⟨3, _⟩ | ⟨4, _⟩ | ⟨5, _⟩ => 1
  | ⟨6, _⟩ => 2
  | ⟨7, _⟩ => 3
  | ⟨8, _⟩ => 4

private def exKind : Fin 9 → GateKind (Fin 9)
  | ⟨0, _⟩ => .leaf true
  | ⟨1, _⟩ => .leaf true
  | ⟨2, _⟩ => .leaf false
  | ⟨3, _⟩ => .and (.binary 0 1)
  | ⟨4, _⟩ => .and (.unary 0)
  | ⟨5, _⟩ => .and (.binary 0 2)
  | ⟨6, _⟩ => .or
  | ⟨7, _⟩ => .and (.binary 6 6)
  | ⟨8, _⟩ => .or

private def exOrChild : Fin 9 → Fin 9 → Prop
  | ⟨6, _⟩, c => c = 3 ∨ c = 4 ∨ c = 5
  | ⟨8, _⟩, c => c = 7
  | _, _ => False

private def exCircuit : LayeredSemiUnboundedCircuit (Fin 9) where
  layer := exLayer
  kind := exKind
  orChild := exOrChild
  layer_andUnary := by
    intro g c h
    fin_cases g <;> cases h
    decide
  layer_andBinary := by
    intro g l r h
    fin_cases g <;> cases h <;> decide
  layer_orChild := by
    intro g c hg hc
    fin_cases g <;> cases hg
    · rcases hc with rfl | rfl | rfl <;> decide
    · cases hc; decide

private theorem exCircuit_inNormalForm : exCircuit.InNormalForm where
  leaf_of_layer_zero := by
    intro g h
    fin_cases g <;>
      first
      | exact ⟨_, rfl⟩
      | (simp [exCircuit, exLayer] at h)
  and_of_odd := by
    intro g h
    fin_cases g <;>
      first
      | exact ⟨_, rfl⟩
      | (exfalso; rcases h with ⟨k, hk⟩; simp only [exCircuit, exLayer] at hk; omega)
  or_of_pos_even := by
    intro g hpos heven
    fin_cases g <;>
      first
      | rfl
      | (exfalso; rcases heven with ⟨k, hk⟩; simp only [exCircuit, exLayer] at hpos hk; omega)

-- Two distinct proof trees for OR gate 6 (via AND gates 3 and 4).
private def pt3 : exCircuit.ProofTree 3 :=
  .andBinary rfl (.leaf rfl) (.leaf rfl)

private def pt4 : exCircuit.ProofTree 4 :=
  .andUnary rfl (.leaf rfl)

private def pt6Via3 : exCircuit.ProofTree 6 :=
  .orChoice rfl (Or.inl rfl) pt3

private def pt6Via4 : exCircuit.ProofTree 6 :=
  .orChoice rfl (Or.inr (Or.inl rfl)) pt4

-- Two distinct proof trees for duplicate-input AND gate 7 (different subtrees on each side).
private def pt7Left : exCircuit.ProofTree 7 :=
  .andBinary rfl pt6Via3 pt6Via3

private def pt7Mixed : exCircuit.ProofTree 7 :=
  .andBinary rfl pt6Via3 pt6Via4

example : pt6Via3 ≠ pt6Via4 := by
  intro h
  cases h

example : pt7Left ≠ pt7Mixed := by
  intro h
  cases h

-- Gate 8 evaluates to `true`, while gate 5 evaluates to `false` and has no proof trees.
example : exCircuit.Eval 8 :=
  (exCircuit.eval_iff_nonempty_proofTree 8).mpr ⟨.orChoice rfl rfl pt7Left⟩

example : ¬exCircuit.Eval 5 ∧ IsEmpty (exCircuit.ProofTree 5) := by
  have h5 : ¬exCircuit.Eval 5 := by
    rw [exCircuit.eval_andBinary (rfl : exCircuit.kind 5 = .and (.binary 0 2))]
    rintro ⟨_, h2⟩
    rw [exCircuit.eval_leaf (rfl : exCircuit.kind 2 = .leaf false)] at h2
    cases h2
  refine ⟨h5, ⟨fun t => h5 ((exCircuit.eval_iff_nonempty_proofTree 5).mpr ⟨t⟩)⟩⟩

-- A concrete 1-bit code and seed isolate `exCircuit`, separating `pt6Via3` (weight 0) from
-- `pt6Via4` (weight 1) and giving `pt7Left` strictly smaller weight than `pt7Mixed`.
private def exCode : Fin 9 → Fin 1 → Bool
  | ⟨4, _⟩, _ => true
  | _, _ => false

private def exSeed : Fin 1 → Bool := fun _ => true

example :
    pt6Via3.weight (exCircuit.seededGateWeight exCode exSeed) = 0 ∧
    pt6Via4.weight (exCircuit.seededGateWeight exCode exSeed) = 1 ∧
    pt7Left.weight (exCircuit.seededGateWeight exCode exSeed) = 0 ∧
    pt7Mixed.weight (exCircuit.seededGateWeight exCode exSeed) = 1 := by
  decide

private theorem exCircuit_isMinIsolating :
    exCircuit.IsMinIsolating (exCircuit.seededGateWeight exCode exSeed) := by
  apply exCircuit.isMinIsolating_of_separated
  intro g hgor u v hcu hcv hne tu tv _ _
  fin_cases g <;> cases hgor
  · have hno5 : ∀ t : exCircuit.ProofTree 5, False := fun t => by
      have h5 : exCircuit.Eval 5 := (exCircuit.eval_iff_nonempty_proofTree 5).mpr ⟨t⟩
      rw [exCircuit.eval_andBinary (rfl : exCircuit.kind 5 = .and (.binary 0 2))] at h5
      rw [exCircuit.eval_leaf (rfl : exCircuit.kind 2 = .leaf false)] at h5
      exact Bool.false_ne_true h5.2
    have huniq3 (t : exCircuit.ProofTree 3) : t = pt3 := by
      cases t with
      | leaf h => cases h
      | andUnary h _ => cases h
      | orChoice h _ _ => cases h
      | andBinary h tl tr =>
        cases h
        cases tl with
        | leaf _ =>
          cases tr with
          | leaf _ => rfl
          | andUnary h _ => cases h
          | andBinary h _ _ => cases h
          | orChoice h _ _ => cases h
        | andUnary h _ => cases h
        | andBinary h _ _ => cases h
        | orChoice h _ _ => cases h
    have huniq4 (t : exCircuit.ProofTree 4) : t = pt4 := by
      cases t with
      | leaf h => cases h
      | andBinary h _ _ => cases h
      | orChoice h _ _ => cases h
      | andUnary h ts =>
        cases h
        cases ts with
        | leaf _ => rfl
        | andUnary h _ => cases h
        | andBinary h _ _ => cases h
        | orChoice h _ _ => cases h
    rcases hcu with rfl | rfl | rfl <;> rcases hcv with rfl | rfl | rfl
    · exact (hne rfl).elim
    · rw [huniq3 tu, huniq4 tv]; decide
    · exact (hno5 tv).elim
    · rw [huniq4 tu, huniq3 tv]; decide
    · exact (hne rfl).elim
    · exact (hno5 tv).elim
    · exact (hno5 tu).elim
    · exact (hno5 tu).elim
    · exact (hno5 tu).elim
  · rcases hcu with rfl; rcases hcv with rfl
    exact (hne rfl).elim

-- Layer 2 contains the OR gate with alternative proof trees. The isolating weight makes the
-- exact tally select a single transcript even though the gate admits multiple valid trees.
open Classical in
example :
    let w := exCircuit.seededGateWeight exCode exSeed
    let trueGates := Finset.univ.filter
      (fun g : {g // exCircuit.layer g = 2} => exCircuit.Eval g.val)
    ∃! t : LayerTranscript exCircuit 2, t.selected.card = trueGates.card ∧
      (∑ g ∈ t.selected, t.weightAt w g) =
        ∑ g ∈ trueGates, (LayerTranscript.minimum exCircuit 2 w).weightAt w g := by
  simpa only [LayerTranscript.selected_minimum] using
    exCircuit.existsUnique_layerTranscript_of_min_isolation 2 _
      (fun g => exCircuit_isMinIsolating g.val)

example :
    let w := exCircuit.seededGateWeight exCode exSeed
    (LayerTranscript.minimum exCircuit 2 w).weightAt w ⟨6, rfl⟩ = 0 := by
  intro w
  have htrue := (exCircuit.eval_iff_nonempty_proofTree 6).mpr ⟨pt6Via3⟩
  obtain ⟨p, hp, heq⟩ := LayerTranscript.weightAt_minimum (k := 2) (w := w) ⟨6, rfl⟩ htrue
  rw [heq]
  exact Nat.eq_zero_of_le_zero (isMinOn_univ_iff.mp hp pt6Via3)

-- The Justesen family isolates `exCircuit` with explicit seed-length and magnitude bounds.
example :
    ∃ seed : Fin (Cslib.Code.JustesenFamily.codeLength 9 0) → Bool,
      exCircuit.IsMinIsolating (exCircuit.generatedGateWeight seed) ∧
      ∀ g : Fin 9,
        exCircuit.generatedGateWeight seed g <
          6 ^ (1 + Cslib.Code.JustesenFamily.codeLength 9 0) := by
  obtain ⟨seed, hseed⟩ := exCircuit.exists_generatedGateWeight_isMinIsolating exCircuit_inNormalForm
  refine ⟨seed, hseed, fun g => ?_⟩
  have h1 : exCircuit.andLevel g ≤ 1 ∨ g = 8 := by fin_cases g <;> decide
  rcases h1 with hle1 | rfl
  · exact (exCircuit.generatedGateWeight_lt_pow seed g).trans_le
      (Nat.pow_le_pow_right (by decide) (by omega))
  · change 0 < _
    positivity

-- The collision bound on the two satisfied AND-level-0 children `3` and `4` of OR gate `6`.
example :
    have h3 : exCircuit.Eval 3 := (exCircuit.eval_iff_nonempty_proofTree 3).mpr ⟨pt3⟩
    have h4 : exCircuit.Eval 4 := (exCircuit.eval_iff_nonempty_proofTree 4).mpr ⟨pt4⟩
    (Finset.univ.filter fun seed =>
      exCircuit.minProofTreeWeight exCode seed h3 =
        exCircuit.minProofTreeWeight exCode seed h4).card ≤ 1 := by
  intro h3 h4
  have h := exCircuit.card_tyingSeeds_le exCircuit_inNormalForm exCode
    (u := 3) (v := 4) rfl rfl rfl h3 h4
  simpa [show hammingDist (exCode 3) (exCode 4) = 1 by decide] using h

-- Uniform polynomial magnitude bound for logarithmic AND-depth circuits (checked at `c = 1`).
example :
    ∃ D : ℕ, ∀ (seed : Fin (Cslib.Code.JustesenFamily.codeLength 9 0) → Bool) (g : Fin 9),
      exCircuit.generatedGateWeight seed g < (2 * (9 + 1)) ^ D := by
  obtain ⟨D, hD⟩ := generatedGateWeight_polynomial_of_log_depth 1
  refine ⟨D, fun seed g => hD 9 exCircuit seed g ?_⟩
  fin_cases g <;> decide

/-! ## 2. Negative test of normal form: `x₁ ∨ x₂` without an AND first layer

Gates on `Fin 3`:
* Layer 0 (leaves): `0 = true` (`x₁`), `1 = true` (`x₂`).
* Layer 1 (OR gate directly above leaves): `2 = OR(0, 1)`.

This violates `InNormalForm` (layer 1 is odd, yet gate `2` is `.or`). Both proof trees of gate `2`
contain no AND gates and therefore have weight `0` under every code and every seed, so no seed
min-isolates `x₁ ∨ x₂`.
-/

private def x1OrX2 : LayeredSemiUnboundedCircuit (Fin 3) where
  layer
    | ⟨0, _⟩ | ⟨1, _⟩ => 0
    | ⟨2, _⟩ => 1
  kind
    | ⟨0, _⟩ => .leaf true
    | ⟨1, _⟩ => .leaf true
    | ⟨2, _⟩ => .or
  orChild
    | ⟨2, _⟩, c => c = 0 ∨ c = 1
    | _, _ => False
  layer_andUnary := by
    intro g c h
    fin_cases g <;> cases h
  layer_andBinary := by
    intro g l r h
    fin_cases g <;> cases h
  layer_orChild := by
    intro g c hg hc
    fin_cases g <;> cases hg
    rcases hc with rfl | rfl <;> decide

example : ¬x1OrX2.InNormalForm := by
  intro h
  obtain ⟨inp, hinp⟩ := h.and_of_odd (g := 2) (by decide : Odd (x1OrX2.layer 2))
  cases hinp

example : x1OrX2.Eval 2 :=
  (x1OrX2.eval_or rfl).mpr ⟨0, Or.inl rfl, (x1OrX2.eval_leaf rfl).mpr rfl⟩

example (ℓ : ℕ) (code : Fin 3 → Fin ℓ → Bool) (seed : Fin ℓ → Bool) :
    ¬x1OrX2.IsMinIsolating (x1OrX2.seededGateWeight code seed) := by
  intro hiso
  have heval : x1OrX2.Eval 2 :=
    (x1OrX2.eval_or rfl).mpr ⟨0, Or.inl rfl, (x1OrX2.eval_leaf rfl).mpr rfl⟩
  let t₀ : x1OrX2.ProofTree 2 := .orChoice rfl (Or.inl rfl) (.leaf rfl)
  let t₁ : x1OrX2.ProofTree 2 := .orChoice rfl (Or.inr rfl) (.leaf rfl)
  have hne : t₀ ≠ t₁ := by
    intro h
    have hchild :
        (match t₀ with | .orChoice (c := c) _ _ _ => c | _ => 2) =
        (match t₁ with | .orChoice (c := c) _ _ _ => c | _ => 2) :=
      congrArg (fun t => match t with | .orChoice (c := c) _ _ _ => c | _ => 2) h
    exact (by decide : (0 : Fin 3) ≠ 1) hchild
  have hmin₀ : IsMinOn (ProofTree.weight (x1OrX2.seededGateWeight code seed)) Set.univ t₀ :=
    isMinOn_univ_iff.mpr fun _ => Nat.zero_le _
  have hmin₁ : IsMinOn (ProofTree.weight (x1OrX2.seededGateWeight code seed)) Set.univ t₁ :=
    isMinOn_univ_iff.mpr fun _ => Nat.zero_le _
  obtain ⟨t, _, huniq⟩ := hiso 2 heval
  exact hne ((huniq t₀ hmin₀).trans (huniq t₁ hmin₁).symm)

-- Inserting a layer of unary AND gates above `x₁, x₂` restores normal form and min-isolation.
private def x1OrX2NormalForm : LayeredSemiUnboundedCircuit (Fin 5) where
  layer
    | ⟨0, _⟩ | ⟨1, _⟩ => 0
    | ⟨2, _⟩ | ⟨3, _⟩ => 1
    | ⟨4, _⟩ => 2
  kind
    | ⟨0, _⟩ => .leaf true
    | ⟨1, _⟩ => .leaf true
    | ⟨2, _⟩ => .and (.unary 0)
    | ⟨3, _⟩ => .and (.unary 1)
    | ⟨4, _⟩ => .or
  orChild
    | ⟨4, _⟩, c => c = 2 ∨ c = 3
    | _, _ => False
  layer_andUnary := by
    intro g c h
    fin_cases g <;> cases h <;> decide
  layer_andBinary := by
    intro g l r h
    fin_cases g <;> cases h
  layer_orChild := by
    intro g c hg hc
    fin_cases g <;> cases hg
    rcases hc with rfl | rfl <;> decide

private theorem x1OrX2NormalForm_inNormalForm : x1OrX2NormalForm.InNormalForm where
  leaf_of_layer_zero := by
    intro g h
    fin_cases g <;>
      first
      | exact ⟨_, rfl⟩
      | (simp [x1OrX2NormalForm] at h)
  and_of_odd := by
    intro g h
    fin_cases g <;>
      first
      | exact ⟨_, rfl⟩
      | (exfalso; rcases h with ⟨k, hk⟩; simp only [x1OrX2NormalForm] at hk; omega)
  or_of_pos_even := by
    intro g hp he
    fin_cases g <;>
      first
      | rfl
      | (exfalso; rcases he with ⟨k, hk⟩; simp only [x1OrX2NormalForm] at hp hk; omega)

example :
    ∃ seed, x1OrX2NormalForm.IsMinIsolating (x1OrX2NormalForm.generatedGateWeight seed) :=
  x1OrX2NormalForm.exists_generatedGateWeight_isMinIsolating x1OrX2NormalForm_inNormalForm

end CslibFrontierTests.SemiUnboundedMinIsolation
