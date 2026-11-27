/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Frontier.Ledger.Unconditional

/-! Checked clients for the tightened `|U| ^ k · |M|` ledger sweep and threshold/LTF monoids. -/

open Cslib.Circuits Cslib.Circuits.Frontier Filter Asymptotics

namespace CslibFrontierTests.FrontierLedgerThreshold

/-! ### Truncated addition monoid and threshold / LTF aggregation -/

example : Nat.card (TruncAdd 7) = 8 :=
  TruncAdd.card 7

example (n t : ℕ) : Aggregates (Cslib.threshold n t) (TruncAdd t) :=
  aggregates_threshold n t

example (n t : ℕ) : Aggregates (fun x : Fin n → Bool => decide (Cslib.BitString.weight x = t))
    (TruncAdd (t + 1)) :=
  aggregates_exactWeight n t

example (n : ℕ) : Aggregates (Cslib.majority n) (TruncAdd ((n + 1) / 2)) :=
  aggregates_majority n

example (n : ℕ) : Aggregates (Cslib.strictMajority n) (TruncAdd (n / 2 + 1)) :=
  aggregates_strictMajority n

example (n : ℕ) (f : Cslib.BooleanFunction n) (hf : f.IsSymmetric) :
    Aggregates f (TruncAdd n) :=
  aggregates_isSymmetric hf

example (op : Boolean.Threshold.Op) (j : ℕ)
    (hj : match op with | .not => 1 ≤ j | .threshold _ c => c ≤ j) :
    Aggregates (Boolean.Threshold.interpretation op) (TruncAdd j) :=
  aggregates_thresholdOp op hj

example (n : ℕ) (w : Fin n → ℤ) (P : ℤ → Bool) :
    Aggregates (fun x : Fin n → Bool => P (∑ i, if x i then w i else 0))
      (TruncAdd (∑ i, (w i).natAbs)) :=
  aggregates_weightedSum w le_rfl P

example (n : ℕ) (w : Fin n → ℤ) (θ : ℤ) :
    Aggregates (fun x : Fin n → Bool => decide (θ ≤ ∑ i, if x i then w i else 0))
      (TruncAdd (∑ i, (w i).natAbs)) :=
  aggregates_ltf w θ le_rfl

/-! ### Tightened extra-message cardinality (`|U| ^ k * |M| < |M| ^ 2` for `TruncAdd 10`) -/

example {σ : Signature} {n s : ℕ} (p : Program σ n s) (special : Fin s → Prop)
    [DecidablePred special] (I : Interpretation σ Bool)
    (L : Ledger special p I (TruncAdd 10)) (o : Wire n s) (Acc : Set Bool)
    (π : Layout (Compiler.Vertex (liveCircuit p special))) (t : ℕ)
    (hk : Nat.card {g // special g} = 1) :
    (L.extra π t '' {x | p.trace I x o ∈ Acc}).ncard ≤ 22 := by
  have h := L.ncard_extra_le (o := o) (Acc := Acc) π t
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hk, pow_one, TruncAdd.card] at h
  omega

/-! ### Non-vacuous switched (`4.57597 n`) client instantiations for threshold and LTF gates -/

example {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) :
    ∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.Threshold.signature n 1)
      (special : Fin c.size → Prop) [DecidablePred special] (t : ℕ),
        1 ≤ t →
        (∀ g, ¬special g → (c.program.lines g).op.arity ≤ 2) →
        (∀ g, special g → match (c.program.lines g).op with
          | .not => True
          | .threshold _ j => j ≤ t) →
        Nat.card {g // special g} * (Real.log 2 + Real.log (t + 1)) ≤ β n →
        c.Decides Boolean.Threshold.interpretation Acc (S n) →
          (1 + 2 * Real.pi / (3 * Real.arccos (5 / 6)) - 1 / 100) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have h := eventually_lt_mul_card_of_threshold (le_refl 2)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hSK hβ
    (ε := 1 / 100) (by norm_num)
  rw [Switched.one_add_inv_two_mul_switchedCoefficient] at h
  filter_upwards [h] with n hn Acc c special _ t ht1 hfan hcut hk hdec
  have hres := hn Acc c special t ht1 hfan hcut hk hdec
  push_cast at hres
  linarith

example {S : ∀ n, Set (Fin n → Bool)} {K : ℕ → ℕ} (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{0}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (W : ℕ),
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ 2) →
        (∀ g, special g → ∃ (w : Fin (σ.Arity (c.program.lines g).op) → ℤ) (P : ℤ → Bool),
          (∑ i, (w i).natAbs) ≤ W ∧
          I (c.program.lines g).op = fun x => P (∑ i, if x i then w i else 0)) →
        Nat.card {g // special g} * (Real.log 2 + Real.log (W + 1)) ≤ β n →
        c.Decides I Acc (S n) →
          (1 + 2 * Real.pi / (3 * Real.arccos (5 / 6)) - 1 / 100) * n <
            (c.program.innerGates.filter fun g => ¬special g).card := by
  have h := eventually_lt_mul_card_of_ltf.{0} (le_refl 2)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hSK hβ
    (ε := 1 / 100) (by norm_num)
  rw [Switched.one_add_inv_two_mul_switchedCoefficient] at h
  filter_upwards [h] with n hn σ I Acc c special _ W hfan hltf hk hdec
  have hres := hn σ I Acc c special W hfan hltf hk hdec
  push_cast at hres
  linarith

end CslibFrontierTests.FrontierLedgerThreshold
