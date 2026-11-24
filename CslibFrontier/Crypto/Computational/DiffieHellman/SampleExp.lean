/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Probability.IID
import CslibFrontier.Probability.StatisticalDistance.Product

/-!
# Approximate exponent sampling bounds for one and several draws

`Cslib.Crypto.PrimeOrderGroupFamily.sampleExp` samples an exponent modulo `F.order d` within
statistical distance `1 / 2 ^ n` of exact uniform on `ZMod (F.order d)`. By `CloseTo.piFin`,
replacing `m` independent `sampleExp n d` draws by as many independent exact uniform draws
changes `Game.advantage` by at most `m / 2 ^ n`. The two- and three-draw forms state this for
nested binds, the shape their clients use.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_uniform_sampleExp`,
  `Cslib.Crypto.PrimeOrderGroupFamily.closeTo_map_uniform_sampleExp`: `sampleExp n d` modulo `q` is
  within statistical distance `1 / 2 ^ n` of uniform on `ZMod q`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_pair_le`: replacing two independent
  `sampleExp n d` draws by two independent uniform draws on `ZMod (F.order d)` changes
  `Game.advantage` by at most `2 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_sampleExp_triple_le`: the same for three
  draws, with loss at most `3 / 2 ^ n`.
* `Cslib.Crypto.PrimeOrderGroupFamily.advantage_bind_iid_sampleExp_le`: the same for `m` draws,
  as a tuple `PMF.iid`, with loss at most `m / 2 ^ n`.
-/

public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)

open Classical in
/-- An exponent sampled by `sampleExp n d` is within statistical distance `1 / 2 ^ n` of uniform on
`ZMod q`. -/
theorem closeTo_uniform_sampleExp (n : ℕ) (d : F.Desc) :
    CloseTo (PMF.uniformOfFintype (ZMod (F.order d)))
      ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))
      (1 / 2 ^ n : ℝ≥0) := by
  refine Game.closeTo_of_advantage_decide_le fun E => ?_
  rw [Game.advantage_comm]
  have h := F.advantage_bind_sampleExp_le n d fun a => PMF.pure (decide (a ∈ E))
  rw [PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact h

open Classical in
/-- Post-processing the modular cast of `sampleExp n d` by `f` is within `ℝ≥0∞`-distance
`1 / 2 ^ n` of `f` applied to a uniform scalar in `ZMod q`. -/
theorem closeTo_map_uniform_sampleExp {α : Type} (n : ℕ) (d : F.Desc)
    (f : ZMod (F.order d) → α) :
    CloseTo ((PMF.uniformOfFintype (ZMod (F.order d))).map f)
      (ProbComp.eval (f <$> ((Nat.cast : ℕ → ZMod (F.order d)) <$> F.sampleExp n d)))
      (1 / 2 ^ n : ℝ≥0∞) := by
  have hδ : (((1 / 2 ^ n : ℝ≥0)) : ℝ≥0∞) = 1 / 2 ^ n := by
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
      ENNReal.coe_ofNat]
  rw [ProbComp.eval_map, ProbComp.eval_map, ← hδ]
  exact (F.closeTo_uniform_sampleExp n d).map f

/-- Replacing two independent `sampleExp n d` draws by two independent exact uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `2 / 2 ^ n`. -/
theorem advantage_bind_sampleExp_pair_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a =>
        (ProbComp.eval (F.sampleExp n d)).bind fun b =>
          k (a : ZMod (F.order d)) (b : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β => k α β) ≤
      2 / 2 ^ n := by
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.sampleExp n d)).bind fun b =>
        k α (b : ZMod (F.order d))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d (fun α =>
    (ProbComp.eval (F.sampleExp n d)).bind fun b => k α (b : ZMod (F.order d)))
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun α => F.advantage_bind_sampleExp_le n d (k α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 1 / 2 ^ n := add_le_add h1 h2
    _ = 2 / 2 ^ n := by rw [← add_div, one_add_one_eq_two]

/-- Replacing three independent `sampleExp n d` draws by three independent exact uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `3 / 2 ^ n`. -/
theorem advantage_bind_sampleExp_triple_le (n : ℕ) (d : F.Desc)
    (k : ZMod (F.order d) → ZMod (F.order d) → ZMod (F.order d) → Game) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a =>
        (ProbComp.eval (F.sampleExp n d)).bind fun b =>
          (ProbComp.eval (F.sampleExp n d)).bind fun c =>
            k (a : ZMod (F.order d)) (b : ZMod (F.order d)) (c : ZMod (F.order d)))
      ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
        (PMF.uniformOfFintype (ZMod (F.order d))).bind fun β =>
          (PMF.uniformOfFintype (ZMod (F.order d))).bind fun γ => k α β γ) ≤
      3 / 2 ^ n := by
  refine (Game.advantage_triangle _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind fun α =>
      (ProbComp.eval (F.sampleExp n d)).bind fun b =>
        (ProbComp.eval (F.sampleExp n d)).bind fun c =>
          k α (b : ZMod (F.order d)) (c : ZMod (F.order d))) _).trans ?_
  have h1 := F.advantage_bind_sampleExp_le n d (fun α =>
    (ProbComp.eval (F.sampleExp n d)).bind fun b =>
      (ProbComp.eval (F.sampleExp n d)).bind fun c =>
        k α (b : ZMod (F.order d)) (c : ZMod (F.order d)))
  have h2 := Game.advantage_bind_le_nnreal (PMF.uniformOfFintype (ZMod (F.order d))) _ _
    (fun α => F.advantage_bind_sampleExp_pair_le n d (k α))
  calc _ ≤ (1 : ℝ≥0) / 2 ^ n + 2 / 2 ^ n := add_le_add h1 h2
    _ = 3 / 2 ^ n := by rw [← add_div]; norm_num

/-- Replacing `m` independent `sampleExp n d` draws by `m` independent exact uniform draws on
`ZMod (F.order d)` changes `Game.advantage` by at most `m / 2 ^ n`. -/
theorem advantage_bind_iid_sampleExp_le (n : ℕ) (d : F.Desc) (m : ℕ)
    (k : (Fin m → ZMod (F.order d)) → Game) :
    Game.advantage
      ((PMF.iid (ProbComp.eval (F.sampleExp n d)) m).bind fun a =>
        k fun i => (a i : ZMod (F.order d)))
      ((PMF.iid (PMF.uniformOfFintype (ZMod (F.order d))) m).bind k) ≤
      m / 2 ^ n := by
  have hone : CloseTo ((ProbComp.eval (F.sampleExp n d)).map (Nat.cast : ℕ → ZMod (F.order d)))
      (PMF.uniformOfFintype (ZMod (F.order d))) (1 / 2 ^ n : ℝ≥0) :=
    Game.closeTo_iff_forall_advantage_bind_le.2 fun test => by
      rw [PMF.bind_map]
      exact F.advantage_bind_sampleExp_le n d test
  have h := Game.coe_advantage_bind_le_of_closeTo (CloseTo.piFin (k := m) fun _ => hone) k
  rw [PMF.piFin_const, PMF.piFin_const, PMF.iid_map, PMF.bind_map, ← ENNReal.coe_natCast,
    ← ENNReal.coe_mul, mul_one_div] at h
  exact ENNReal.coe_le_coe.1 h

end Cslib.Crypto.PrimeOrderGroupFamily
