/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.RepeatedInversion.SlotBound
public import CslibFrontier.Crypto.Game.Inversion
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount

import CslibFrontier.Probability.PMF.Bind

/-!
# Tests for `RepeatedInversion`

* **T1**: the printed winning condition of [BonehShoup2023], Exercise 14.15 (p. 612) is met with
  probability one by a single reveal query (`eval_printed_game`, `printedAttack_isQueryBounded`).
* **T2**: even with the index corrected, one reveal query wins the `chainUnrevealed` game on a
  function with a side chain with probability one (`eval_unrevealed_game_sideChain`,
  `sideChainAttack_isQueryBounded`), while `chainConsistent` succeeds only when the seed has tag `1`
  (`succProbability_consistent_game_sideChain`) and inverting `sideChain g` reduces to inverting
  `g` up to `1 / (m + 3)` (`sideChain_preimage`, `succProbability_inversion_sideChain_le`).
* **T3**: at `d = 0`, returning the first public seed wins `repeatedIterateExperiment` with
  probability one (`eval_game_zero`), and `0 < d` is necessary in
  `succProbability_repeatedIterateUnrevealedExperiment_of_injective` (`zeroAttack`,
  `zeroAttack_isQueryBounded`).
-/

public section

namespace CslibFrontierTests.RepeatedInversion

open Cslib Cslib.Crypto Cslib.Probability
open scoped ENNReal NNReal

/-! ### T1: the winning condition as printed is met with probability one -/

/-- Exercise 14.15 as printed (p. 612): no reveal `(a, b')` with `b' ≤ b`, where the claim is
for `f^(b)(x) = y_a`, that is, for position `d - b`. -/
def chainPrinted {X : Type} (d : ℕ) (k : ℕ) (_ : X) (log : List (ℕ × X)) : Bool :=
  log.all fun r => r.1 / d != k / d || decide (d - k % d < r.1 % d)

/-- Reveal position `d - 1` of chain `0` and return it as the claim for `b = 1`. -/
def printedAttack {X : Type} (d : ℕ) (_ : List X) : ProbOracleComp (fun _ : ℕ => X) (ℕ × X) := do
  let v ← ProbOracleComp.query (spec := fun _ : ℕ => X) (d - 1)
  return (d - 1, v)

/-- For every `f`, every input law, `n ≥ 1` chains and `d ≥ 3`, `printedAttack` wins the game as
printed with probability one. -/
theorem eval_printed_game {X : Type} [Inhabited X] [DecidableEq X] (sample : ProbComp X)
    (f : X → X) {n d : ℕ} (hn : 0 < n) (hd : 3 ≤ d) :
    ProbComp.eval (forgeExperiment (chainKeyGen sample f n d) (chainSigner id f d)
      (fun ys _ k => chainVerify f d ys k) (chainPrinted d) (printedAttack d)) =
      PMF.pure true := by
  simp only [forgeExperiment, chainKeyGen, ProbOracleComp.runLogWith, printedAttack,
    ProbOracleComp.runState_bind, ProbOracleComp.runState_query, ProbOracleComp.runState_pure,
    bind_assoc, pure_bind, StateT.run_bind, ProbOracleComp.logOracle_run, chainSigner,
    Signer.ofSign_apply, map_pure, StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [Probability.PMF.bind_congr_on_support (ProbComp.eval (OracleComp.replicate n sample)) _
    (fun _ => PMF.pure true)]
  · simp
  · intro xs hxs
    have hlen : 0 < xs.length := ((ProbComp.mem_support_replicate_iff _ _ _).mp hxs).1.symm ▸ hn
    have h0 : (xs.map f^[d])[0]? = some (f^[d] (xs.getD 0 default)) := by
      cases xs with
      | nil => simp at hlen
      | cons x _ => simp
    have hdiv : (d - 1) / d = 0 := Nat.div_eq_of_lt (by omega)
    have hmod : (d - 1) % d = d - 1 := Nat.mod_eq_of_lt (by omega)
    have hiter : f^[d - (d - 1)] (chainSlot f d xs (d - 1)) = f^[d] (xs.getD 0 default) := by
      rw [chainSlot, hdiv, hmod, show d - (d - 1) = 1 by omega, Function.iterate_one,
        ← Function.iterate_succ_apply' f (d - 1), Nat.succ_eq_add_one,
        Nat.sub_add_cancel (by omega)]
    have hver : chainVerify f d (xs.map f^[d]) (d - 1) (chainSlot f d xs (d - 1)) = true := by
      simp [chainVerify, hdiv, h0, hiter]
    have hpr : chainPrinted d (d - 1) (chainSlot f d xs (d - 1))
        [(d - 1, chainSlot f d xs (d - 1))] = true := by
      simp [chainPrinted, hmod, show d - (d - 1) < d - 1 by omega]
    simp [hver, hpr]

/-- The attack makes one reveal query: its efficiency certificate. -/
theorem printedAttack_isQueryBounded {X : Type} (d : ℕ) (ys : List X) :
    (printedAttack (X := X) d ys).IsQueryBounded 1 := by
  simpa [printedAttack, ProbOracleComp.IsQueryBounded, ProbOracleComp.query] using
    (OracleComp.IsCostBounded.query (Sum.inr (d - 1))
      (cost := Sum.elim (fun _ => 0) (fun _ => 1))).bind
        fun v => .pure (d - 1, v) 0

/-! ### T2: with the index corrected, a function with a side chain still loses -/

variable {G : Type} {m : ℕ}

/-- `f (a, τ) = (g a, 0)` for `τ ≠ 1` and `f (a, 1) = (a, 2)`: tag `1` opens a side chain that
rejoins the main chain one step later. -/
def sideChain (g : G → G) (x : G × Fin (m + 3)) : G × Fin (m + 3) :=
  if x.2 = 1 then (x.1, 2) else (g x.1, 0)

/-- `n = 1`, `d = 2`: reveal position `1`, read off its first coordinate `u`, and claim `(u, 1)`
for position `0`. -/
def sideChainAttack (_ : List (G × Fin (m + 3))) :
    ProbOracleComp (fun _ : ℕ => G × Fin (m + 3)) (ℕ × (G × Fin (m + 3))) := do
  let u ← ProbOracleComp.query (spec := fun _ : ℕ => G × Fin (m + 3)) 1
  return (0, (u.1, 1))

/-- The attack wins the index-corrected `chainUnrevealed` game of Exercise 14.15 with probability
one, for every `g` and every input law. -/
theorem eval_unrevealed_game_sideChain [DecidableEq G] [Inhabited G]
    (sample : ProbComp (G × Fin (m + 3))) (g : G → G) :
    ProbComp.eval
        (repeatedIterateUnrevealedExperiment id sample (sideChain g) 1 2 sideChainAttack) =
      PMF.pure true := by
  simp only [repeatedIterateUnrevealedExperiment, forgeExperiment, chainKeyGen,
    ProbOracleComp.runLogWith, sideChainAttack, ProbOracleComp.runState_bind,
    ProbOracleComp.runState_query, ProbOracleComp.runState_pure, bind_assoc, pure_bind,
    StateT.run_bind, ProbOracleComp.logOracle_run, chainSigner, Signer.ofSign_apply, map_pure,
    StateT.run_pure, ProbComp.eval_bind, ProbComp.eval_pure]
  rw [Probability.PMF.bind_congr_on_support (ProbComp.eval (OracleComp.replicate 1 sample)) _
    (fun _ => PMF.pure true)]
  · simp
  · intro xs hxs
    have hlen : xs.length = 1 := ((ProbComp.mem_support_replicate_iff _ _ _).mp hxs).1
    cases xs with
    | nil => simp at hlen
    | cons x xs' =>
      simp only [List.length_cons, Nat.add_eq_right, List.length_eq_zero_iff] at hlen
      subst hlen
      have hu : chainSlot (sideChain g) 2 [x] 1 = sideChain g x := by
        simp [chainSlot]
      have htop : (sideChain g)^[2] ((chainSlot (sideChain g) 2 [x] 1).1, (1 : Fin (m + 3))) =
          (sideChain g)^[2] x := by
        rw [hu, Function.iterate_succ_apply', Function.iterate_one,
          Function.iterate_succ_apply', Function.iterate_one]
        have h21 : (2 : Fin (m + 3)) ≠ 1 := by
          simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < m + 3),
            Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
        have h01 : (0 : Fin (m + 3)) ≠ 1 := by simp
        by_cases hx : x.2 = 1
        · simp [sideChain, hx, h21]
        · simp [sideChain, hx, h21, h01]
      simp [chainVerify, chainUnrevealed, htop]

/-- The attack makes one reveal query: its efficiency certificate. -/
theorem sideChainAttack_isQueryBounded (ys : List (G × Fin (m + 3))) :
    (sideChainAttack (G := G) (m := m) ys).IsQueryBounded 1 := by
  simpa [sideChainAttack, ProbOracleComp.IsQueryBounded, ProbOracleComp.query] using
    (OracleComp.IsCostBounded.query (Sum.inr 1)
      (cost := Sum.elim (fun _ => 0) (fun _ => 1))).bind
        fun u => .pure (0, (u.1, 1)) 0

/-- Concrete `m = 0`, `G = Fin 2`, `g = (· + 1)` instance of `eval_unrevealed_game_sideChain`. -/
example (sample : ProbComp (Fin 2 × Fin 3)) :
    ProbComp.eval (repeatedIterateUnrevealedExperiment id sample
      (sideChain (m := 0) fun a : Fin 2 => a + 1) 1 2 sideChainAttack) = PMF.pure true :=
  eval_unrevealed_game_sideChain sample _

/-- Its claim is chain-consistent only when the seed has tag `1`. -/
theorem succProbability_consistent_game_sideChain [DecidableEq G] [Inhabited G] [Fintype G]
    (sample : ProbComp (G × Fin (m + 3))) (g : G → G)
    (hsample : ProbComp.eval sample = PMF.uniformOfFintype (G × Fin (m + 3))) :
    Experiment.succProbability
      (repeatedIterateExperiment id sample (sideChain g) 1 2 sideChainAttack) = 1 / (m + 3) := by
  have hexp : ProbComp.eval
      (repeatedIterateExperiment id sample (sideChain g) 1 2 sideChainAttack) =
      (PMF.uniformOfFintype (G × Fin (m + 3))).map (fun x => decide (x.2 = 1)) := by
    ext b
    simp only [repeatedIterateExperiment, forgeExperiment, chainKeyGen,
      ProbOracleComp.runLogWith, sideChainAttack, ProbOracleComp.runState_bind,
      ProbOracleComp.runState_query, ProbOracleComp.runState_pure, bind_assoc, pure_bind,
      StateT.run_bind, ProbOracleComp.logOracle_run, chainSigner, Signer.ofSign_apply, map_pure,
      StateT.run_pure, OracleComp.replicate_succ, OracleComp.replicate_zero, ProbComp.eval_bind,
      ProbComp.eval_pure, hsample, PMF.bind_apply, PMF.map_apply]
    simp only [PMF.pure_apply, mul_ite, mul_one, mul_zero]
    rw [tsum_fintype, tsum_fintype]
    refine Finset.sum_congr rfl fun x _ => ?_
    have hu : chainSlot (sideChain g) 2 [x] 1 = sideChain g x := by
      simp [chainSlot]
    have hside : sideChain (m := m) g (x.1, 1) = (x.1, 2) := by simp [sideChain]
    by_cases hx : x.2 = 1
    · have h1 : sideChain g x = (x.1, 2) := by simp [sideChain, hx]
      simp [hu, h1, hside, chainVerify, chainConsistent, Function.iterate_succ_apply', hx]
    · have hne21 : (2 : Fin (m + 3)) ≠ 1 := by
        simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < m + 3),
          Nat.mod_eq_of_lt (by omega : 1 < m + 3)]
      have hne20 : (2 : Fin (m + 3)) ≠ 0 := by
        simp [Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 2 < m + 3)]
      have hfalse : ((g x.1, (2 : Fin (m + 3))) == (g x.1, 0)) = false := by
        simp [Bool.eq_false_iff, beq_iff_eq, hne20]
      simp [hu, chainVerify, chainConsistent, sideChain, hx, hne21, hfalse]
  rw [← ENNReal.coe_inj]
  have h1 : (((1 / (m + 3)) : ℝ≥0) : ℝ≥0∞) = 1 / (m + 3 : ℝ≥0∞) := by simp
  rw [h1, Experiment.succProbability, Game.succProbability,
    ENNReal.coe_toNNReal (PMF.apply_ne_top _ _), hexp, PMF.map_apply, tsum_fintype]
  calc
    _ = ∑ _a : G, (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        simp
    _ = (Fintype.card G : ℝ≥0∞) * ((Fintype.card G : ℝ≥0∞) * (m + 3 : ℝ≥0∞))⁻¹ := by
        simp [Fintype.card_prod]
    _ = 1 / (m + 3 : ℝ≥0∞) := by
        have hG0 : (Fintype.card G : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
        have hm0 : (m + 3 : ℝ≥0∞) ≠ 0 := by positivity
        rw [ENNReal.mul_inv (Or.inl hG0) (Or.inr hm0), ← mul_assoc,
          ENNReal.mul_inv_cancel hG0 (by simp), one_mul, one_div]

private theorem sideChain_iterate_of_ne_one (g : G → G) {a : G} {τ : Fin (m + 3)} (hτ : τ ≠ 1)
    {j : ℕ} (hj : 0 < j) : (sideChain g)^[j] (a, τ) = (g^[j] a, 0) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj.ne'
  induction k generalizing a τ with
  | zero =>
    simp [sideChain, hτ]
  | succ k ih =>
    have hstep : sideChain g (a, τ) = (g a, 0) := by simp [sideChain, hτ]
    rw [Function.iterate_succ_apply, hstep, Function.iterate_succ_apply g]
    exact ih (a := g a) (τ := 0) (by simp) (Nat.succ_pos k)

/-- Away from tag `1`, every `sideChain g`-preimage of an iterate is a `g`-preimage: inverting
`sideChain g` on an iterate is inverting `g`. -/
theorem sideChain_preimage (g : G → G) {a : G} {τ : Fin (m + 3)} (hτ : τ ≠ 1) {j : ℕ}
    (hj : 0 < j) {x' : G × Fin (m + 3)} (h : sideChain g x' = (sideChain g)^[j] (a, τ)) :
    g x'.1 = g^[j] a ∧ x'.2 ≠ 1 := by
  rw [sideChain_iterate_of_ne_one g hτ hj] at h
  by_cases hx' : x'.2 = 1
  · simp only [sideChain, hx', ↓reduceIte, Prod.mk.injEq, Fin.ext_iff, Fin.val_two,
      Fin.val_zero] at h
    omega
  · simp only [sideChain, hx', ↓reduceIte, Prod.mk.injEq] at h
    exact ⟨h.1, hx'⟩

/-- So `sideChain g` is as hard to invert at every level (the challenge is the iterate `k + 1` of
a uniform point) as `g` is to invert, up to the probability `1 / (m + 3)` of tag `1`. -/
theorem succProbability_inversion_sideChain_le [DecidableEq G] [Inhabited G] [Fintype G] {g : G → G}
    (hg : Function.Bijective g) (sampleG : ProbComp G)
    (hG : ProbComp.eval sampleG = PMF.uniformOfFintype G)
    (sample : ProbComp (G × Fin (m + 3)))
    (hsample : ProbComp.eval sample = PMF.uniformOfFintype (G × Fin (m + 3)))
    (k : ℕ) (A : G × Fin (m + 3) → ProbComp (G × Fin (m + 3))) :
    Experiment.succProbability
        (inversionExperiment ((sideChain g)^[k] <$> sample) (sideChain g) A) ≤
      1 / (m + 3) + Experiment.succProbability
        (inversionExperiment sampleG g fun z => Prod.fst <$> A (z, 0)) := by
  have hgk : Function.Bijective (g^[k]) := hg.iterate k
  have hmapG : (PMF.uniformOfFintype G).map (g^[k]) = PMF.uniformOfFintype G :=
    PMF.uniformOfFintype_map_equiv (Equiv.ofBijective _ hgk)
  have h1 : (((1 / (m + 3)) : ℝ≥0) : ℝ≥0∞) = 1 / (m + 3 : ℝ≥0∞) := by simp
  rw [← ENNReal.coe_le_coe, ENNReal.coe_add, h1]
  simp only [Experiment.succProbability, Game.succProbability,
    ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)]
  have hleft : ProbComp.eval
      (inversionExperiment ((sideChain g)^[k] <$> sample) (sideChain g) A) true =
      ∑ x : G × Fin (m + 3), (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ *
        ∑' x' : G × Fin (m + 3),
          ProbComp.eval (A ((sideChain g)^[k + 1] x)) x' *
            (if sideChain g x' = (sideChain g)^[k + 1] x then (1 : ℝ≥0∞) else 0) := by
    have hevalL : ProbComp.eval
        (inversionExperiment ((sideChain g)^[k] <$> sample) (sideChain g) A) =
        (PMF.uniformOfFintype (G × Fin (m + 3))).bind fun x =>
          (ProbComp.eval (A ((sideChain g)^[k + 1] x))).map fun x' =>
            decide (sideChain g x' = (sideChain g)^[k + 1] x) := by
      simp only [inversionExperiment, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
        hsample, PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      simp_rw [← Function.iterate_succ_apply' (sideChain g) k, Nat.succ_eq_add_one]
      refine congr_arg _ (funext fun x => congr_arg _ (funext fun x' => congr_arg PMF.pure ?_))
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    simp only [hevalL, PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply]
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun x _ => ?_
    refine congr_arg ((Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ * ·) ?_
    refine tsum_congr fun x' => ?_
    by_cases h : sideChain g x' = (sideChain g)^[k + 1] x <;>
      (simp only [Function.iterate_succ_apply] at h ⊢; simp [h])
  have hright : ProbComp.eval
      (inversionExperiment sampleG g fun z => Prod.fst <$> A (z, 0)) true =
      ∑ a : G, (Fintype.card G : ℝ≥0∞)⁻¹ *
        ∑' x' : G × Fin (m + 3),
          ProbComp.eval (A (g^[k + 1] a, 0)) x' *
            (if g x'.1 = g^[k + 1] a then (1 : ℝ≥0∞) else 0) := by
    have heval : ProbComp.eval (inversionExperiment sampleG g fun z => Prod.fst <$> A (z, 0)) =
        (PMF.uniformOfFintype G).bind fun a =>
          (ProbComp.eval (A (g^[k + 1] a, 0))).map fun x' => decide (g x'.1 = g^[k + 1] a) := by
      simp only [inversionExperiment, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
        hG]
      conv_lhs => rw [← hmapG]
      simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]
      simp_rw [← Function.iterate_succ_apply' g k, Nat.succ_eq_add_one]
      refine congr_arg _ (funext fun a => congr_arg _ (funext fun x' => congr_arg PMF.pure ?_))
      rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_eq]
    simp only [heval, PMF.bind_apply, PMF.map_apply, PMF.uniformOfFintype_apply]
    rw [tsum_fintype]
    refine Finset.sum_congr rfl fun a _ => ?_
    refine congr_arg ((Fintype.card G : ℝ≥0∞)⁻¹ * ·) ?_
    refine tsum_congr fun x' => ?_
    by_cases h : g x'.1 = g^[k + 1] a <;>
      (simp only [Function.iterate_succ_apply] at h ⊢; simp [h])
  rw [hleft, hright, Fintype.sum_prod_type, Finset.sum_comm]
  have hsplit : ∀ τ : Fin (m + 3),
      (∑ a : G, (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ *
        ∑' x' : G × Fin (m + 3),
          ProbComp.eval (A ((sideChain g)^[k + 1] (a, τ))) x' *
            (if sideChain g x' = (sideChain g)^[k + 1] (a, τ) then (1 : ℝ≥0∞) else 0)) ≤
      if τ = 1 then (Fintype.card G : ℝ≥0∞) * (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹
      else ((m + 3 : ℝ≥0∞)⁻¹ *
        ∑ a : G, (Fintype.card G : ℝ≥0∞)⁻¹ *
          ∑' x' : G × Fin (m + 3),
            ProbComp.eval (A (g^[k + 1] a, 0)) x' *
              (if g x'.1 = g^[k + 1] a then (1 : ℝ≥0∞) else 0)) := by
    intro τ
    by_cases hτ : τ = 1
    · subst hτ
      simp only [↓reduceIte]
      calc
        ∑ a : G, (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ *
            ∑' x' : G × Fin (m + 3),
              ProbComp.eval (A ((sideChain g)^[k + 1] (a, 1))) x' *
                (if sideChain g x' = (sideChain g)^[k + 1] (a, 1) then (1 : ℝ≥0∞) else 0)
          ≤ ∑ _a : G, (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ * 1 := by
            refine Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left ?_ (by simp)
            calc
              ∑' x' : G × Fin (m + 3),
                  ProbComp.eval (A ((sideChain g)^[k + 1] (a, 1))) x' *
                    (if sideChain g x' = (sideChain g)^[k + 1] (a, 1) then (1 : ℝ≥0∞) else 0)
                ≤ ∑' x' : G × Fin (m + 3),
                    ProbComp.eval (A ((sideChain g)^[k + 1] (a, 1))) x' := by
                  refine tsum_le_tsum fun x' => ?_
                  split_ifs <;> simp
              _ = 1 := PMF.tsum_coe _
        _ = (Fintype.card G : ℝ≥0∞) * (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ := by
            simp
    · simp only [hτ, ↓reduceIte, Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      have hG0 : (Fintype.card G : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
      have hm0 : (m + 3 : ℝ≥0∞) ≠ 0 := by positivity
      have hinv : (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ =
          (m + 3 : ℝ≥0∞)⁻¹ * (Fintype.card G : ℝ≥0∞)⁻¹ := by
        simp [Fintype.card_prod, ENNReal.mul_inv (Or.inl hG0) (Or.inr hm0), mul_comm]
      rw [hinv, mul_assoc, sideChain_iterate_of_ne_one g hτ (Nat.succ_pos k)]
      refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by simp)) (by simp)
      refine tsum_le_tsum fun x' => ?_
      split_ifs with h1 h2
      · rfl
      · exfalso
        exact h2 ((sideChain_preimage g hτ (Nat.succ_pos k) (by
          simpa [sideChain_iterate_of_ne_one g hτ (Nat.succ_pos k)] using h1)).1)
      · simp
      · simp
  calc
    ∑ τ : Fin (m + 3), ∑ a : G, (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ *
        ∑' x' : G × Fin (m + 3),
          ProbComp.eval (A ((sideChain g)^[k + 1] (a, τ))) x' *
            (if sideChain g x' = (sideChain g)^[k + 1] (a, τ) then (1 : ℝ≥0∞) else 0)
      ≤ ∑ τ : Fin (m + 3),
          if τ = 1 then (Fintype.card G : ℝ≥0∞) * (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹
          else ((m + 3 : ℝ≥0∞)⁻¹ *
            ∑ a : G, (Fintype.card G : ℝ≥0∞)⁻¹ *
              ∑' x' : G × Fin (m + 3),
                ProbComp.eval (A (g^[k + 1] a, 0)) x' *
                  (if g x'.1 = g^[k + 1] a then (1 : ℝ≥0∞) else 0)) :=
        Finset.sum_le_sum fun τ _ => hsplit τ
    _ ≤ (Fintype.card G : ℝ≥0∞) * (Fintype.card (G × Fin (m + 3)) : ℝ≥0∞)⁻¹ +
          (m + 3 : ℝ≥0∞) * ((m + 3 : ℝ≥0∞)⁻¹ *
            ∑ a : G, (Fintype.card G : ℝ≥0∞)⁻¹ *
              ∑' x' : G × Fin (m + 3),
                ProbComp.eval (A (g^[k + 1] a, 0)) x' *
                  (if g x'.1 = g^[k + 1] a then (1 : ℝ≥0∞) else 0)) := by
        rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const]
        have h1card : (Finset.filter (fun τ : Fin (m + 3) => τ = 1) Finset.univ).card = 1 := by
          rw [Finset.card_eq_one]
          exact ⟨1, by ext τ; simp⟩
        have h2card : (Finset.filter (fun τ : Fin (m + 3) => ¬τ = 1) Finset.univ).card ≤ m + 3 := by
          simpa using (Finset.card_le_univ
            (Finset.filter (fun τ : Fin (m + 3) => ¬τ = 1) Finset.univ))
        rw [h1card, one_nsmul, nsmul_eq_mul]
        have h2coe : ((Finset.filter (fun τ : Fin (m + 3) => ¬τ = 1) Finset.univ).card : ℝ≥0∞) ≤
            m + 3 := by
          simpa using (Nat.cast_le (α := ℝ≥0∞)).2 h2card
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_right h2coe (by simp))
    _ = 1 / (m + 3 : ℝ≥0∞) +
          ∑ a : G, (Fintype.card G : ℝ≥0∞)⁻¹ *
            ∑' x' : G × Fin (m + 3),
              ProbComp.eval (A (g^[k + 1] a, 0)) x' *
                (if g x'.1 = g^[k + 1] a then (1 : ℝ≥0∞) else 0) := by
        have hG0 : (Fintype.card G : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
        have hm0 : (m + 3 : ℝ≥0∞) ≠ 0 := by positivity
        have hmtop : (m + 3 : ℝ≥0∞) ≠ ⊤ := by simp
        congr 1
        · rw [Fintype.card_prod, Fintype.card_fin]
          push_cast
          rw [ENNReal.mul_inv (Or.inl hG0) (Or.inr hm0), ← mul_assoc,
            ENNReal.mul_inv_cancel hG0 (by simp), one_mul, one_div]
        · rw [← mul_assoc, ENNReal.mul_inv_cancel hm0 hmtop, one_mul]

/-- Evaluating `sideChain` on `(0, 1)` when `m = 0`, `G = Fin 2`, and `g = (· + 1)`. -/
example : sideChain (m := 0) (fun a : Fin 2 => a + 1) (0, 1) = (0, 2) := by decide

/-! ### T3: behavior at `d = 0` and necessity of `0 < d` -/

/-- At `d = 0` the public value of a chain is its seed, and returning it without reveal queries
wins `repeatedIterateExperiment` with probability one. -/
theorem eval_game_zero {X : Type} [Inhabited X] [DecidableEq X] (sample : ProbComp X)
    (f : X → X) {n : ℕ} (hn : 0 < n) :
    ProbComp.eval (repeatedIterateExperiment (Q := ℕ) id sample f n 0
      fun ys => pure (0, ys.headI)) = PMF.pure true := by
  simp only [repeatedIterateExperiment, forgeExperiment, chainKeyGen, ProbOracleComp.runLogWith,
    ProbOracleComp.runState_pure, bind_assoc, pure_bind, StateT.run_pure, ProbComp.eval_bind,
    ProbComp.eval_pure]
  rw [Probability.PMF.bind_congr_on_support (ProbComp.eval (OracleComp.replicate n sample)) _
    (fun _ => PMF.pure true)]
  · simp
  · intro xs hxs
    have hlen : 0 < xs.length := ((ProbComp.mem_support_replicate_iff _ _ _).mp hxs).1.symm ▸ hn
    cases xs with
    | nil => simp at hlen
    | cons x xs' =>
      simp [chainVerify, chainConsistent]

/-- At `d = 0` with the injective `f = not`: reveal slot `2`, then claim the public value for
slot `1`. -/
def zeroAttack (ys : List Bool) : ProbOracleComp (fun _ : ℕ => Bool) (ℕ × Bool) := do
  let _ ← ProbOracleComp.query (spec := fun _ : ℕ => Bool) 2
  return (1, ys.headI)

/-- `zeroAttack` makes one reveal query: its efficiency certificate. -/
theorem zeroAttack_isQueryBounded (ys : List Bool) :
    (zeroAttack ys).IsQueryBounded 1 := by
  simpa [zeroAttack, ProbOracleComp.IsQueryBounded, ProbOracleComp.query] using
    (OracleComp.IsCostBounded.query (Sum.inr 2)
      (cost := Sum.elim (fun _ => 0) (fun _ => 1))).bind
        fun _ => .pure (1, ys.headI) 0

/-- Probe of `0 < d` in `succProbability_repeatedIterateUnrevealedExperiment_of_injective`:
at `d = 0`, `zeroAttack` wins `repeatedIterateUnrevealedExperiment` with probability one. -/
example : ProbComp.eval (repeatedIterateUnrevealedExperiment id (pure true) not 1 0 zeroAttack) =
    PMF.pure true := by
  simp [repeatedIterateUnrevealedExperiment, forgeExperiment, chainKeyGen, chainSigner, chainSlot,
    chainVerify, chainUnrevealed, zeroAttack, ProbOracleComp.runLogWith,
    ProbOracleComp.runState_query, ProbOracleComp.logOracle_run, OracleComp.replicate_succ,
    OracleComp.replicate_zero]

/-- Probe of `0 < d` in `succProbability_repeatedIterateUnrevealedExperiment_of_injective`:
at `d = 0`, `zeroAttack` loses `repeatedIterateExperiment` with probability one. -/
example : ProbComp.eval (repeatedIterateExperiment id (pure true) not 1 0 zeroAttack) =
    PMF.pure false := by
  simp [repeatedIterateExperiment, forgeExperiment, chainKeyGen, chainSigner, chainSlot,
    chainVerify, chainConsistent, zeroAttack, ProbOracleComp.runLogWith,
    ProbOracleComp.runState_query, ProbOracleComp.logOracle_run, OracleComp.replicate_succ,
    OracleComp.replicate_zero]

/-! ### Guessing step (`SlotBound`) checks and boundary probes -/

/-- Probe of `0 < d` in `succProbability_repeatedIterateExperiment_le_sum`: at `d = 0`, the slot
sum over `Finset.range (n * 0)` is zero while `eval_game_zero` gives success probability `1`. -/
example :
    (∑ g ∈ Finset.range (1 * 0), Experiment.succProbability
      (inversionExperiment (Bool.not^[g % 0] <$> (pure true : ProbComp Bool)) Bool.not
        (slotInverter (Q := ℕ) id (pure true) Bool.not 1 0 g (fun ys => pure (0, ys.headI))))) <
    Experiment.succProbability
      (repeatedIterateExperiment (Q := ℕ) id (pure true) Bool.not 1 0
        fun ys => pure (0, ys.headI)) := by
  rw [Finset.range_zero, Finset.sum_empty]
  simp [Experiment.succProbability, Game.succProbability, eval_game_zero]

private def secondSlotAttack : List Bool → ProbOracleComp (fun _ : ℕ => Bool) (ℕ × Bool)
  | ys => pure (1, ys.getD 1 false)

/-- Concrete two-slot check of `slotInverter` and `plantInverter`: targeting slot `1` on
`id` with seed `true`, a planted challenge at `g = 1` succeeds with probability `1` while
`g = 0` returns `default = false` and fails (`0`), so `plantInverter` succeeds with `1 / 2`
while `repeatedInversionExperiment` succeeds with `1` (tight for the factor `2` bound). -/
example :
    Experiment.succProbability (inversionExperiment (pure true) id
      (slotInverter (Q := ℕ) id (pure true) id 2 1 1 secondSlotAttack)) = 1 := by
  simp [Experiment.succProbability, Game.succProbability, inversionExperiment, slotInverter,
    secondSlotAttack, OracleComp.replicate_succ, OracleComp.replicate_zero]

example :
    Experiment.succProbability (inversionExperiment (pure true) id
      (plantInverter (Q := ℕ) id (pure true) id 2 secondSlotAttack)) = 1 / 2 := by
  have h0 :
      ProbComp.eval (inversionExperiment (pure true) id
        (slotInverter (Q := ℕ) id (pure true) id 2 1 0 secondSlotAttack)) = PMF.pure false := by
    simp [inversionExperiment, slotInverter, secondSlotAttack, OracleComp.replicate_succ,
      OracleComp.replicate_zero]
  have h1 :
      ProbComp.eval (inversionExperiment (pure true) id
        (slotInverter (Q := ℕ) id (pure true) id 2 1 1 secondSlotAttack)) = PMF.pure true := by
    simp [inversionExperiment, slotInverter, secondSlotAttack, OracleComp.replicate_succ,
      OracleComp.replicate_zero]
  have h :
      ProbComp.eval (inversionExperiment (pure true) id
        (plantInverter (Q := ℕ) id (pure true) id 2 secondSlotAttack)) =
      (PMF.uniformOfFintype (Fin 2)).bind fun ω =>
        ProbComp.eval (inversionExperiment (pure true) id
          (slotInverter (Q := ℕ) id (pure true) id 2 1 ω secondSlotAttack)) := by
    simp only [inversionExperiment, plantInverter, ProbComp.eval_bind, ProbComp.eval_pure,
      ProbComp.eval_unifFin, PMF.pure_bind, PMF.bind_bind]
  rw [Experiment.succProbability, h]
  simp only [Game.succProbability, PMF.bind_apply, PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [tsum_fintype, Fin.sum_univ_two]
  simp only [Fin.val_zero, Fin.val_one, h0, h1, PMF.pure_apply]
  norm_num [ENNReal.toNNReal_ofNat]

example :
    Experiment.succProbability (repeatedInversionExperiment (Q := ℕ) id (pure true) id 2
      secondSlotAttack) = 1 := by
  simp [Experiment.succProbability, Game.succProbability, repeatedInversionExperiment,
    forgeExperiment, secondSlotAttack, ProbOracleComp.runLogWith, ProbOracleComp.runState_pure,
    StateT.run_pure, OracleComp.replicate_succ, OracleComp.replicate_zero]

end CslibFrontierTests.RepeatedInversion
