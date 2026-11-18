/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Game.Statistical

/-! # Adaptive signing budgets and concrete hedge losses -/

set_option linter.privateModule false

open Cslib Cslib.Probability Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204 Cslib.Quantum
open scoped Cslib.Probability.PMF

-- Ask for the same signature twice, with a coherent query and a measurement in between.
-- An independent fair coin makes early termination and a second request both possible.
private def repeatedRequest (q : SigningQuery) : QuantumSigningForger where
  addressBits := 2
  responseBytes := 1
  workQubits := 0
  program _ := do
    let sig ← OracleComp.query (.inr (.inr q))
    let _ ← OracleComp.query (.inr (.inl .query))
    let bits ← OracleComp.query (.inr (.inl (.measure 0)))
    let coin ← OracleComp.query (.inl 1)
    let out := fun (r : Option (List Byte)) => Forgery.mk q.context q.message (r.getD [])
    if (bits == [true]) ^^ (coin == 1) then
      let sig' ← OracleComp.query (.inr (.inr q))
      return out sig'
    else return out sig

private theorem repeatedRequest_budget (q : SigningQuery) :
    (repeatedRequest q).SigningCallsLe 2 := by
  intro pk
  refine .liftBind _ _ 1 fun _ => ?_
  refine .liftBind _ _ 1 fun _ => ?_
  refine .liftBind _ _ 1 fun bits => ?_
  refine .liftBind _ _ 1 fun coin => ?_
  split
  · exact .liftBind _ _ 0 fun _ => .pure _ 0
  · exact .pure _ 1

-- The genuine two-call program needs only the two presampled hedges even with its device calls.
example (q : SigningQuery) (H : Xofs) (s : Level) (keys : KeyPair) :
    (PMF.uniformOfFintype (Fin 2 → FixedBytes 32)).bind (fun t =>
      (repeatedRequest q).transcriptWithHedges H H s keys (List.ofFn t)) =
      (repeatedRequest q).transcript H s keys :=
  (repeatedRequest q).uniform_transcriptWithHedges H s keys (repeatedRequest_budget q)

-- Substitute the 2⁶⁴-signing-query budget into the fresh-digest term of the existing reduction.
set_option exponentiation.threshold 257 in
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b : ℕ}
    (ha : 272 ≤ a) (hb : 894 ≤ b) (hn : C.SigningCallsLe (2 ^ 64)) :
    dist (((base.uniformPrefixes a b).bind (C.matrixTrial s)).map
      (·.any SignedMatrixTrial.newDigestWin))
      (C.distinctHedgeGame s base a b hn (by decide) SignedMatrixTrial.newDigestWin) <
      1 / 2 ^ 129 := by
  refine (C.dist_matrixTrial_distinctHedges s base ha hb hn (by decide) _).trans_lt ?_
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  exact_mod_cast (by decide : (2 ^ 64 * (2 ^ 64 - 1) : ℕ) * 2 ^ 129 < 2 ^ 257)

-- Compose the new fresh-digest term with the actual strong-forgery split.
example (C : QuantumSigningForger) (s : Level) (base : Xofs) {a b n : ℕ}
    (ha : 272 ≤ a) (hb : 894 ≤ b) (hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 256) :
    let R := base.uniformPrefixes a b
    let trial := R.bind (C.matrixTrial s)
    (Game.succProbability (C.randomPrefixGame s base a b) : ℝ) ≤
      Game.succProbability
        (C.distinctHedgeGame s base a b hn hsize SignedMatrixTrial.newDigestWin) +
        ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 +
        (Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
          Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
            ((R.bind fun H => C.matrixSolver s H A).map fun v => decide (ModuleSIS.IsSolution
              (ModuleSIS.hermiteMatrix A) (max (2 * (s.params.γ₁ - s.params.β))
                (4 * s.params.γ₂ + 2)) v)))) := by
  intro R trial
  have split := NNReal.coe_le_coe.mpr (C.randomPrefixGame_forgery_le s base ha hb)
  rw [NNReal.coe_add] at split
  refine split.trans (add_le_add_left ?_ _)
  apply Game.coe_succProbability_le_add_of_advantage_le
  rw [Game.advantage_eq_nndist, coe_nndist]
  exact C.dist_matrixTrial_distinctHedges s base ha hb hn hsize _
