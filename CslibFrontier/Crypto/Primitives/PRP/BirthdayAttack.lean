/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Primitives.PRP.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.Vector
public import Mathlib.Data.Nat.Factorial.Basic
import CslibFrontier.Probability.IID
import CslibFrontier.Probability.IID.Birthday
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Event

/-!
# Birthday distinguisher against a block cipher as a PRF

This module formalizes the non-adaptive collision-testing distinguisher of Boneh–Shoup (§4.4.3,
printed p. 134) that separates any block cipher `E : Key → Equiv.Perm D` from a uniform random
function `D → D` in the finite-type PRF experiment (`Cslib.Crypto.PRF.advantage`):

* `Cslib.Crypto.PRP.birthdayDistinguisher x` queries a tuple `x : Fin Q → D` and outputs `true` iff
  the oracle's answers fail to be injective. It makes `Q` queries
  (`isQueryBounded_birthdayDistinguisher`). When `x` is injective, the real block-cipher
  experiment always outputs `false` (`eval_realExperiment_birthdayDistinguisher`), so the PRF
  advantage equals the collision probability of `Q` independent uniform samples from `D`:
  `1 - (Fintype.card D).descFactorial Q / (Fintype.card D : ℝ) ^ Q`
  (`coe_advantage_birthdayDistinguisher`), which is at least
  `min (Q * (Q - 1) / (4 * Fintype.card D)) 0.63` (`min_le_advantage_birthdayDistinguisher`).
  When `x` enumerates `D` (`Function.Bijective x`) and `2 ≤ Fintype.card D`, the advantage is at
  least `1 / 2` (`half_le_advantage_birthdayDistinguisher_of_bijective`).

## Differences from [BonehShoup2023]

* The book's adversary makes `Q` distinct queries. Here they are a tuple `x : Fin Q → D` with
  `Function.Injective x`, which forces `Q ≤ Fintype.card D`.
* The distinguisher outputs `decide (¬ Function.Injective y)` rather than searching explicitly for
  a pair `i ≠ j` with `y i = y j`, which is logically equivalent.
* For the full-domain distinguisher (`N` queries), the book implicitly assumes `N ≥ 2` when claiming
  `1 - N! / N^N ≥ 1 / 2` (at `N = 1`, `1 - 1! / 1^1 = 0`). Here `2 ≤ Fintype.card D` is explicit in
  `half_le_advantage_birthdayDistinguisher_of_bijective`.
* Statements are finite-type with oracle query bounds (`ProbOracleComp.IsQueryBounded`); no running
  time in a machine model is tracked, and the counter-mode attack of §4.4.4.1 is not included.

## Main definitions

* `Cslib.Crypto.PRP.birthdayDistinguisher`: non-adaptive `Q`-query collision distinguisher.

## Main results

* `Cslib.Crypto.PRP.isQueryBounded_birthdayDistinguisher`: `birthdayDistinguisher x` makes at most
  `Q` queries.
* `Cslib.Crypto.PRP.eval_realExperiment_birthdayDistinguisher`: zero collision probability against
  any permutation cipher when `x` is injective.
* `Cslib.Crypto.PRP.succProbability_idealExperiment_birthdayDistinguisher`: exact collision
  probability in `PRF.idealExperiment`.
* `Cslib.Crypto.PRP.coe_advantage_birthdayDistinguisher`: exact PRF advantage `1 - (|D|)_Q / |D|^Q`.
* `Cslib.Crypto.PRP.min_le_advantage_birthdayDistinguisher`: lower bound
  `min (Q * (Q - 1) / (4 * |D|)) 0.63 ≤ PRF.advantage`.
* `Cslib.Crypto.PRP.half_le_advantage_birthdayDistinguisher_of_bijective`: `1 / 2` lower bound
  whenever `Function.Bijective x` and `2 ≤ |D|`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], §4.4.3 (printed p. 134).
-/

public section

namespace Cslib.Crypto.PRP

open Cslib.Probability.PMF
open scoped Nat NNReal

/-- Birthday distinguisher of Boneh–Shoup (§4.4.3, printed p. 134): given `Q` inputs
`x : Fin Q → D`, it queries the PRF oracle at `x 0, …, x (Q - 1)` and returns `true` iff two
responses collide. -/
def birthdayDistinguisher {D : Type} [DecidableEq D] {Q : ℕ} (x : Fin Q → D) :
    ProbOracleComp (fun _ : D => D) Bool := do
  let y ← OracleComp.pi fun i => ProbOracleComp.query (spec := fun _ : D => D) (x i)
  return decide (¬ Function.Injective y)

/-- `birthdayDistinguisher x` makes at most `Q` oracle queries on every execution path. -/
theorem isQueryBounded_birthdayDistinguisher {D : Type} [DecidableEq D] {Q : ℕ}
    (x : Fin Q → D) :
    (birthdayDistinguisher x).IsQueryBounded Q :=
  (OracleComp.IsCostBounded.bind
    (ProbOracleComp.isQueryBounded_pi_query (spec := fun _ : D => D) x)
    fun y => OracleComp.IsCostBounded.pure (decide (¬ Function.Injective y)) 0).mono
    (Nat.add_zero Q).le

/-- Against any deterministic oracle `f : D → D`, `birthdayDistinguisher x` returns `true` iff
`f ∘ x` fails to be injective. -/
theorem run_birthdayDistinguisher {D : Type} [DecidableEq D] {Q : ℕ} (x : Fin Q → D)
    (f : D → D) :
    (birthdayDistinguisher x).run (fun d => pure (f d)) =
      pure (decide (¬ Function.Injective (f ∘ x))) := by
  simp [birthdayDistinguisher, ProbOracleComp.run_pi_query, Function.comp_def]

/-- In Experiment 0 (`PRP.realExperiment`), any block cipher `E : Key → Equiv.Perm D` preserves
injectivity of `x`, so `birthdayDistinguisher x` outputs `false` with probability `1`. -/
theorem eval_realExperiment_birthdayDistinguisher {Key D : Type} [Fintype Key] [Nonempty Key]
    [DecidableEq D] (E : Key → Equiv.Perm D) {Q : ℕ} {x : Fin Q → D}
    (hx : Function.Injective x) :
    ProbComp.eval (PRP.realExperiment E (birthdayDistinguisher x)) = PMF.pure false := by
  simp only [PRP.realExperiment, PRF.realExperiment, ProbComp.eval_bind,
    run_birthdayDistinguisher, ProbComp.eval_pure]
  simp [hx, PMF.bind_const]

private theorem succProbability_idealExperiment_birthdayDistinguisher_eq_iid
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    {Q : ℕ} {x : Fin Q → D} (hx : Function.Injective x) :
    (Game.succProbability (ProbComp.eval (PRF.idealExperiment (birthdayDistinguisher x))) : ℝ) =
      ((iid (uniformOfFintype D) Q).toOuterMeasure {y | ¬ Function.Injective y}).toReal := by
  have heval : ProbComp.eval (PRF.idealExperiment (birthdayDistinguisher x)) =
      (iid (uniformOfFintype D) Q).map (fun y => decide (¬ Function.Injective y)) := by
    simp only [PRF.idealExperiment, ProbComp.eval_bind, run_birthdayDistinguisher,
      ProbComp.eval_pure, ProbComp.eval_uniform]
    change (uniformOfFintype (D → D)).bind
        (PMF.pure ∘ ((fun y : Fin Q → D => decide (¬ Function.Injective y)) ∘
          fun f : D → D => f ∘ x)) = _
    have hcomp : (fun f : D → D => f ∘ x) = fun f i => f ((⟨x, hx⟩ : Fin Q ↪ D) i) := rfl
    rw [PMF.bind_pure_comp, ← PMF.map_comp, hcomp,
      uniformOfFintype_pi_map_comp_embedding, ← iid_uniformOfFintype Q]
  have hpre : (fun y : Fin Q → D => decide (¬ Function.Injective y)) ⁻¹' {true} =
      {y | ¬ Function.Injective y} := by
    ext y
    simp
  rw [Game.coe_succProbability, heval, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply, hpre]

/-- In Experiment 1 (`PRF.idealExperiment`), for injective `x : Fin Q → D`,
`birthdayDistinguisher x` outputs `true` with probability `1 - (|D|)_Q / |D|^Q`. -/
theorem succProbability_idealExperiment_birthdayDistinguisher
    {D : Type} [Fintype D] [DecidableEq D] [Nonempty D]
    {Q : ℕ} {x : Fin Q → D} (hx : Function.Injective x) :
    (Game.succProbability (ProbComp.eval (PRF.idealExperiment (birthdayDistinguisher x))) : ℝ) =
      1 - ((Fintype.card D).descFactorial Q : ℝ) / (Fintype.card D : ℝ) ^ Q := by
  rw [succProbability_idealExperiment_birthdayDistinguisher_eq_iid hx]
  have hsum := toOuterMeasure_toReal_add_compl (iid (uniformOfFintype D) Q)
    {y : Fin Q → D | Function.Injective y}
  have hinj := iid_uniformOfFintype_injective (α := D) Q
  change ((iid (uniformOfFintype D) Q).toOuterMeasure
    {y : Fin Q → D | Function.Injective y}ᶜ).toReal = _
  linarith

private theorem coe_advantage_birthdayDistinguisher_eq_succProbability
    {Key D : Type} [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D] [Nonempty D]
    (E : Key → Equiv.Perm D) {Q : ℕ} {x : Fin Q → D} (hx : Function.Injective x) :
    (PRF.advantage (fun key => ⇑(E key)) (birthdayDistinguisher x) : ℝ) =
      Game.succProbability (ProbComp.eval (PRF.idealExperiment (birthdayDistinguisher x))) := by
  have hreal : ProbComp.eval (PRF.realExperiment (fun key => ⇑(E key)) (birthdayDistinguisher x)) =
      PMF.pure false := eval_realExperiment_birthdayDistinguisher E hx
  rw [PRF.advantage, hreal, Game.advantage_pure_false_left]

/-- Exact PRF distinguishing advantage of `birthdayDistinguisher x` against any block cipher
`E : Key → Equiv.Perm D` when `x` is injective (§4.4.3, printed p. 134): `1 - (|D|)_Q / |D|^Q`. -/
theorem coe_advantage_birthdayDistinguisher
    {Key D : Type} [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D] [Nonempty D]
    (E : Key → Equiv.Perm D) {Q : ℕ} {x : Fin Q → D} (hx : Function.Injective x) :
    (PRF.advantage (fun key => ⇑(E key)) (birthdayDistinguisher x) : ℝ) =
      1 - ((Fintype.card D).descFactorial Q : ℝ) / (Fintype.card D : ℝ) ^ Q := by
  rw [coe_advantage_birthdayDistinguisher_eq_succProbability E hx,
    succProbability_idealExperiment_birthdayDistinguisher hx]

/-- Birthday lower bound on the PRF advantage of `birthdayDistinguisher x` against any block cipher
`E : Key → Equiv.Perm D` (§4.4.3, printed p. 134): `min (Q * (Q - 1) / (4 * |D|)) 0.63`. -/
theorem min_le_advantage_birthdayDistinguisher
    {Key D : Type} [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D] [Nonempty D]
    (E : Key → Equiv.Perm D) {Q : ℕ} {x : Fin Q → D} (hx : Function.Injective x) :
    min ((Q : ℝ) * (Q - 1) / (4 * Fintype.card D)) 0.63 ≤
      (PRF.advantage (fun key => ⇑(E key)) (birthdayDistinguisher x) : ℝ) := by
  rw [coe_advantage_birthdayDistinguisher_eq_succProbability E hx,
    succProbability_idealExperiment_birthdayDistinguisher_eq_iid hx]
  exact min_le_iid_not_injective (uniformOfFintype D) Q

private theorem two_mul_factorial_le_pow {n : ℕ} (hn : 2 ≤ n) : 2 * n ! ≤ n ^ n := by
  induction n, hn using Nat.le_induction with
  | base => decide
  | succ m hm ih =>
    calc
      2 * (m + 1)! = (m + 1) * (2 * m !) := by rw [Nat.factorial_succ]; ring
      _ ≤ (m + 1) * m ^ m := Nat.mul_le_mul_left _ ih
      _ ≤ (m + 1) * (m + 1) ^ m := by gcongr; omega
      _ = (m + 1) ^ (m + 1) := by rw [Nat.pow_succ, mul_comm]

/-- A tuple `x` that enumerates a domain of at least two points gives PRF advantage at least `1 / 2`
against any block cipher `E : Key → Equiv.Perm D` (§4.4.3, printed p. 134): the advantage is
`1 - |D|! / |D|^|D|`. -/
theorem half_le_advantage_birthdayDistinguisher_of_bijective
    {Key D : Type} [Fintype Key] [Nonempty Key] [Fintype D] [DecidableEq D] [Nonempty D]
    (E : Key → Equiv.Perm D) {Q : ℕ} {x : Fin Q → D} (hx : Function.Bijective x)
    (hD : 2 ≤ Fintype.card D) :
    (1 / 2 : ℝ) ≤ PRF.advantage (fun key => ⇑(E key)) (birthdayDistinguisher x) := by
  obtain rfl : Q = Fintype.card D := by
    simpa using Fintype.card_of_bijective hx
  rw [coe_advantage_birthdayDistinguisher E hx.injective, Nat.descFactorial_self]
  have hpos : (0 : ℝ) < (Fintype.card D : ℝ) ^ Fintype.card D := by positivity
  have hfac : (2 : ℝ) * (Fintype.card D)! ≤ (Fintype.card D : ℝ) ^ Fintype.card D := by
    exact_mod_cast two_mul_factorial_le_pow hD
  rw [le_sub_comm, div_le_iff₀ hpos]
  linarith

end Cslib.Crypto.PRP
