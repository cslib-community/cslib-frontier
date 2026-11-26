/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Engineering.Electrical.LinearCircuit
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Tests for linear circuits, modified nodal equations and certified stability

Every certificate below was produced by an untrusted exact generator (index-one decoupling by row
reduction and a Schur complement, the equilibrium, and an exact Lyapunov solution with `LDLᵀ`
witnesses) and is checked by the kernel (`decide +kernel`).

* **RC** (`rc`): a 1 V source with an input port, `R = 1 Ω`, `C = 1 F`. The end-to-end theorem
  gives exponential stability of every trajectory about the operating point `φ = (1, 1)`,
  `i = 0`, and the checked realization from the source input to the capacitor voltage and the
  source node voltage is `A = -1`, `B = 1`, `C = (1, 0)ᵀ`, `D = (0, 1)ᵀ` (direct feedthrough).
* **Damped series RLC** (`rlc`): `R = 3 Ω`, `L = 1 H`, `C = 1/2 F`, end to end.
* **Ideal LC** (`lc`): an accepted decoupling with `A = !![0, -1; 1, 0]`, but explicit
  oscillating trajectories show that the equilibrium is not attractive, so no Lyapunov
  certificate is accepted.
* **Unstable controlled source** (`neg`): `C = 1 F`, `R = 1 Ω` and a VCCS of `g = -2 S` act as a
  net negative conductance; an explicit growing trajectory exists and no Lyapunov certificate is
  accepted.
* **Rejections**: an inconsistent circuit (two parallel voltage sources of 1 V and 2 V) has no
  accepted decoupling and no accepted equilibrium; an index-two circuit (a voltage source in
  parallel with a capacitor) has no accepted decoupling; a corrupted decoupling and a malformed
  netlist are rejected.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CircuitMNA

open Set Filter Topology Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra Cslib.Electrical

/-! ### RC: end-to-end stability and a checked realization -/

/-- A 1 V source (input port 0) at node 1, `R = 1 Ω` from node 1 to node 2, `C = 1 F` from
node 2 to ground. -/
abbrev rc : Netlist where
  nodes := 2
  inputs := 1
  branches := [⟨1, 0, .voltageSource 1 (some 0)⟩, ⟨1, 2, .resistor 1⟩, ⟨2, 0, .capacitor 1⟩]

/-- The decoupling of `rc`. -/
def rcDec : DecouplingCert where
  k := 1
  r := 4
  P₁ := [[0, 1, 1, 1, 1]]
  P₂ := [[0, 0, -1, 0, 0], [-1, 0, 1, 1, 0], [0, 0, -1, -1, 0], [0, -1, -1, -1, 0]]
  P₁' := [[0], [0], [0], [0], [1]]
  P₂' := [[0, -1, -1, 0], [0, 0, 1, -1], [-1, 0, 0, 0], [1, 0, -1, 0], [0, 0, 0, 1]]
  Q₁ := [[0], [1], [1], [-1], [-1]]
  Q₂ := [[1, 0, 0, 0], [0, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]
  Q₁' := [[0, 1, 0, 0, 0]]
  Q₂' := [[1, 0, 0, 0, 0], [0, -1, 1, 0, 0], [0, 1, 0, 1, 0], [0, 1, 0, 0, 1]]
  A := [[-1]]

/-- The operating point of `rc`. -/
def rcEq : List ℚ := [1, 1, 0, 0, 0]

/-- The Lyapunov matrix for the reduced matrix of `rc`. -/
def rcP : List (List ℚ) := [[(1/2 : ℚ)]]

/-- The `LDLᵀ` witnesses for `rcP` and its residual. -/
def rcLyap : LyapunovCert := ⟨⟨[[1]], [(1/2 : ℚ)]⟩,
  ⟨[[1]], [1]⟩⟩

theorem rc_check : rc.check = true := by decide +kernel
theorem rcDec_check : rcDec.check rc.size rc.eRows rc.fRows = true := by decide +kernel
theorem rcEq_check : isEquilibriumRows rc.size rc.fRows rc.bList rcEq = true := by decide +kernel
theorem rcLyap_check : rcLyap.check rcDec.k rcDec.A rcP = true := by
  decide +kernel

/-- Every RC trajectory with the source at 1 V converges exponentially to the operating point,
which is itself a trajectory, and every capacitor state starts one. -/
example := rc.isExponentiallyStable_of_check rc_check rcDec_check rcEq_check
  (LyapunovCert.isExponentiallyStable_of_check rcLyap_check)

/-- The probes: the capacitor voltage and the source node voltage. -/
def rcProbes : List Probe := [.voltage 2 0, .voltage 1 0]

theorem rc_realization :
    rcDec.reducedB rc.size rc.inputs rc.gRows = [[1]] ∧
    rcDec.outputC rc.size rcProbes.length (rc.probeRows rcProbes) = [[1], [0]] ∧
    rcDec.feedthroughD rc.size rcProbes.length rc.inputs (rc.probeRows rcProbes) rc.gRows =
      [[0], [1]] := by
  decide +kernel

/-- The input/output behaviour of the RC circuit, for every input signal and every trajectory:
the state `x = Q₁' (z - z₀)` (the capacitor voltage deviation) solves `ẋ = -x + u`, and the
outputs satisfy `y - y₀ = C x + D u` with the direct feedthrough `D = (0, 1)ᵀ`. -/
example {u : ℝ → Fin rc.inputs → ℝ} {φ : ℝ → Fin rc.nodes → ℝ}
    {i : ℝ → Fin rc.branches.length → ℝ} (h : rc.IsTrajectoryOn u φ i (Ici 0)) :
    (rc.realization rcDec rcProbes).IsSolutionOn u
      (fun t => realOfRows rcDec.k rc.size rcDec.Q₁' *ᵥ
        (Fin.append (φ t) (i t) - realOfList rc.size rcEq)) (Ici 0) :=
  ((rc.isTrajectoryOn_iff_realization rc_check rcDec_check rcEq_check rcProbes
    (uniqueDiffOn_Ici 0)).1 h).2

/-! ### Damped series RLC -/

/-- A 1 V source at node 1, then `R = 3 Ω`, `L = 1 H` and `C = 1/2 F` in series to ground. -/
abbrev rlc : Netlist where
  nodes := 3
  inputs := 0
  branches := [⟨1, 0, .voltageSource 1 none⟩, ⟨1, 2, .resistor 3⟩, ⟨2, 3, .inductor 1⟩,
    ⟨3, 0, .capacitor (1/2)⟩]

/-- The decoupling of `rlc`. -/
def rlcDec : DecouplingCert where
  k := 2
  r := 5
  P₁ := [[0, 0, 2, 0, 0, 0, 2], [0, 3, 0, 1, 1, 1, 0]]
  P₂ := [[0, 0, 0, -1, 0, 0, 0],
    [0, -3, 0, -1, -1, 0, 0],
    [-1, -1, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 0, 0],
    [0, 0, -1, 0, 0, 0, 0]]
  P₁' := [[0, 0], [0, 0], [0, 0], [0, 0], [0, 0], [0, 1], [(1/2 : ℚ), 0]]
  P₂' := [[0, 0, -1, -1, 0],
    [0, 0, 0, 1, 0],
    [0, 0, 0, 0, -1],
    [-1, 0, 0, 0, 0],
    [1, -1, 0, -3, 0],
    [0, 1, 0, 0, 0],
    [0, 0, 0, 0, 1]]
  Q₁ := [[0, 0], [0, -3], [1, 0], [0, -1], [0, 1], [0, 1], [0, 1]]
  Q₂ := [[1, 0, 0, 0, 0],
    [0, 1, 0, 0, 0],
    [0, 0, 0, 0, 0],
    [0, 0, 1, 0, 0],
    [0, 0, 0, 1, 0],
    [0, 0, 0, 0, 0],
    [0, 0, 0, 0, 1]]
  Q₁' := [[0, 0, 1, 0, 0, 0, 0], [0, 0, 0, 0, 0, 1, 0]]
  Q₂' := [[1, 0, 0, 0, 0, 0, 0],
    [0, 1, 0, 0, 0, 3, 0],
    [0, 0, 0, 1, 0, 1, 0],
    [0, 0, 0, 0, 1, -1, 0],
    [0, 0, 0, 0, 0, -1, 1]]
  A := [[0, 2], [-1, -3]]

/-- The operating point of `rlc`. -/
def rlcEq : List ℚ := [1, 1, 1, 0, 0, 0, 0]

/-- The Lyapunov matrix for the reduced matrix of `rlc`. -/
def rlcP : List (List ℚ) := [[1, (1/2 : ℚ)], [(1/2 : ℚ), (1/2 : ℚ)]]

/-- The `LDLᵀ` witnesses for `rlcP` and its residual. -/
def rlcLyap : LyapunovCert := ⟨⟨[[1], [(1/2 : ℚ), 1]], [1, (1/4 : ℚ)]⟩,
  ⟨[[1], [0, 1]], [1, 1]⟩⟩

theorem rlc_check : rlc.check = true := by decide +kernel
theorem rlcDec_check : rlcDec.check rlc.size rlc.eRows rlc.fRows = true := by decide +kernel
theorem rlcEq_check : isEquilibriumRows rlc.size rlc.fRows rlc.bList rlcEq = true := by
  decide +kernel
theorem rlcLyap_check :
    rlcLyap.check rlcDec.k rlcDec.A rlcP = true := by
  decide +kernel

/-- Exponential stability of every damped RLC trajectory about the operating point. -/
example := rlc.isExponentiallyStable_of_check rlc_check rlcDec_check rlcEq_check
  (LyapunovCert.isExponentiallyStable_of_check rlcLyap_check)

/-! ### Ideal LC: an accepted decoupling, but no asymptotic stability -/

/-- `L = 1 H` and `C = 1 F` in parallel between node 1 and ground. -/
abbrev lc : Netlist where
  nodes := 1
  inputs := 0
  branches := [⟨1, 0, .inductor 1⟩, ⟨1, 0, .capacitor 1⟩]

/-- The decoupling of `lc`. -/
def lcDec : DecouplingCert where
  k := 2
  r := 1
  P₁ := [[1, 0, 1], [0, 1, 0]]
  P₂ := [[-1, 0, 0]]
  P₁' := [[0, 0], [0, 1], [1, 0]]
  P₂' := [[-1], [0], [1]]
  Q₁ := [[1, 0], [0, 1], [0, -1]]
  Q₂ := [[0], [0], [1]]
  Q₁' := [[1, 0, 0], [0, 1, 0]]
  Q₂' := [[0, 1, 1]]
  A := [[0, -1], [1, 0]]

/-- The operating point of `lc`. -/
def lcEq : List ℚ := [0, 0, 0]

theorem lc_check : lc.check = true := by decide +kernel
theorem lcDec_check : lcDec.check lc.size lc.eRows lc.fRows = true := by decide +kernel
theorem lcEq_check : isEquilibriumRows lc.size lc.fRows lc.bList lcEq = true := by decide +kernel

/-- The oscillation `φ = ε cos t`, `i_L = ε sin t`, `i_C = -ε sin t` is an LC trajectory. -/
theorem lc_osc (ε : ℝ) :
    lc.IsTrajectoryOn 0 (fun t _ => ε * Real.cos t) (fun t => ![ε * Real.sin t, -(ε * Real.sin t)])
      (Ici 0) := by
  constructor
  · intro t _ k
    fin_cases k
    erw [Fin.sum_univ_two]
    simp [Branch.incidence]
  · intro t _ b
    fin_cases b
    · simp only [lc, Element.Law, potential]
      simpa using ((Real.hasDerivAt_sin t).const_mul ε).hasDerivWithinAt
    · simp only [lc, Element.Law, potential]
      simpa using ((Real.hasDerivAt_cos t).const_mul ε).hasDerivWithinAt

/-- The potential of the oscillation does not tend to the equilibrium value `0`. -/
theorem lc_not_tendsto {ε : ℝ} (hε : ε ≠ 0) :
    ¬ Tendsto (fun t : ℝ => ε * Real.cos t) atTop (𝓝 0) := by
  intro h
  have h2 := h.comp ((tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
    (by positivity : (0 : ℝ) < 2 * Real.pi))
  have : (fun n : ℕ => ε * Real.cos (2 * Real.pi * n)) = fun _ => ε := by
    funext n
    rw [mul_comm (2 * Real.pi), Real.cos_nat_mul_two_pi, mul_one]
  simp only [Function.comp_def, this] at h2
  exact hε (tendsto_nhds_unique tendsto_const_nhds h2)

/-- **The ideal LC circuit is not asymptotically stable:** arbitrarily close to the equilibrium
there are trajectories that do not converge to it. -/
example : ∀ δ > 0, ∃ φ i, lc.IsTrajectoryOn 0 φ i (Ici 0) ∧ |φ 0 0| < δ ∧
    ¬ Tendsto (fun t => φ t 0) atTop (𝓝 0) := fun δ hδ =>
  ⟨_, _, lc_osc (δ / 2),
    by simp only [Real.cos_zero, mul_one]; rw [abs_of_pos (half_pos hδ)]; linarith,
    lc_not_tendsto (by positivity)⟩

private theorem norm_le_of_apply {n : ℕ} (z : Fin n → ℝ) (j : Fin n) :
    |z j| ≤ ‖WithLp.toLp 2 z‖ := by
  simpa using PiLp.norm_apply_le (WithLp.toLp 2 z) j

/-- Hence no Lyapunov certificate is accepted for its reduced matrix. -/
theorem lc_no_lyapunov (l : LyapunovCert) (P : List (List ℚ)) :
    l.check lcDec.k lcDec.A P = false := by
  by_contra hl
  obtain ⟨-, -, M, α, hα, hM⟩ := lc.isExponentiallyStable_of_check lc_check lcDec_check
    lcEq_check (LyapunovCert.isExponentiallyStable_of_check (Bool.eq_true_of_not_eq_false hl))
  have hq : ofList lc.size lcEq = 0 := by funext j; fin_cases j <;> decide
  have hz : realOfList lc.size lcEq = 0 := by
    funext j; simp only [realOfList, hq, Pi.zero_apply, Rat.cast_zero]
  set K := ‖WithLp.toLp 2 (Fin.append ((fun t _ => (1 : ℝ) * Real.cos t) 0)
    ((fun t => ![(1 : ℝ) * Real.sin t, -((1 : ℝ) * Real.sin t)]) 0) - realOfList lc.size lcEq)‖
  apply lc_not_tendsto (ε := 1) one_ne_zero
  have hb : ∀ t ≥ 0, |1 * Real.cos t| ≤ M * Real.exp (-(α * t)) * K := fun t ht => by
    have := hM _ _ (lc_osc 1) t ht
    refine (le_trans (le_of_eq ?_) (norm_le_of_apply _ (Fin.castAdd _ 0))).trans this
    rw [Pi.sub_apply, Fin.append_left, hz, Pi.zero_apply, sub_zero]
  have hlim : Tendsto (fun t => M * Real.exp (-(α * t)) * K) atTop (𝓝 0) := by
    simpa using ((Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hα))).const_mul M).mul_const K
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 0] with t ht using by simpa using hb t ht

/-! ### An unstable controlled-source circuit -/

/-- `C = 1 F`, `R = 1 Ω` and a VCCS `i = -2 φ₁` from node 1 to ground: `φ₁' = φ₁`. -/
abbrev neg : Netlist where
  nodes := 1
  inputs := 0
  branches := [⟨1, 0, .capacitor 1⟩, ⟨1, 0, .resistor 1⟩, ⟨1, 0, .vccs (-2) 1 0⟩]

/-- The decoupling of `neg`. -/
def negDec : DecouplingCert where
  k := 1
  r := 3
  P₁ := [[1, 1, -1, -1]]
  P₂ := [[-1, 0, 1, 1], [0, 0, -1, 0], [0, 0, 0, -1]]
  P₁' := [[0], [1], [0], [0]]
  P₂' := [[-1, -1, -1], [1, 0, 0], [0, -1, 0], [0, 0, -1]]
  Q₁ := [[1], [1], [1], [-2]]
  Q₂ := [[0, 0, 0], [1, 0, 0], [0, 1, 0], [0, 0, 1]]
  Q₁' := [[1, 0, 0, 0]]
  Q₂' := [[-1, 1, 0, 0], [-1, 0, 1, 0], [2, 0, 0, 1]]
  A := [[1]]

/-- The operating point of `neg`. -/
def negEq : List ℚ := [0, 0, 0, 0]

theorem neg_check : neg.check = true := by decide +kernel
theorem negDec_check : negDec.check neg.size neg.eRows neg.fRows = true := by decide +kernel
theorem negEq_check : isEquilibriumRows neg.size neg.fRows neg.bList negEq = true := by
  decide +kernel

/-- The growing trajectory `φ₁ = ε eᵗ`. -/
theorem neg_grow (ε : ℝ) :
    neg.IsTrajectoryOn 0 (fun t _ => ε * Real.exp t)
      (fun t => ![ε * Real.exp t, ε * Real.exp t, -2 * (ε * Real.exp t)]) (Ici 0) := by
  constructor
  · intro t _ k
    fin_cases k
    erw [Fin.sum_univ_three]
    simp [Branch.incidence]
    ring
  · intro t _ b
    fin_cases b
    · simp only [neg, Element.Law, potential]
      simpa using ((Real.hasDerivAt_exp t).const_mul ε).hasDerivWithinAt
    · simp [neg, Element.Law, potential]
    · simp [neg, Element.Law, potential]

/-- **The circuit is unstable:** arbitrarily close to the equilibrium `0` there are trajectories
whose potential is unbounded. -/
example : ∀ δ > 0, ∃ φ i, neg.IsTrajectoryOn 0 φ i (Ici 0) ∧ |φ 0 0| < δ ∧
    ∀ B : ℝ, ∃ t ≥ 0, B < φ t 0 := fun δ hδ => by
  refine ⟨_, _, neg_grow (δ / 2),
    by simp only [Real.exp_zero, mul_one]; rw [abs_of_pos (half_pos hδ)]; linarith, fun B => ?_⟩
  have hB : 0 ≤ 2 * |B| / δ := by positivity
  refine ⟨Real.log (2 * |B| / δ + 1), Real.log_nonneg (by linarith), ?_⟩
  rw [Real.exp_log (by positivity)]
  have h2 : δ / 2 * (2 * |B| / δ + 1) = |B| + δ / 2 := by field_simp
  linarith [le_abs_self B]

/-- Hence no Lyapunov certificate is accepted for its reduced matrix. -/
theorem neg_no_lyapunov (l : LyapunovCert) (P : List (List ℚ)) :
    l.check negDec.k negDec.A P = false := by
  by_contra hl
  obtain ⟨-, -, M, α, hα, hM⟩ := neg.isExponentiallyStable_of_check neg_check negDec_check
    negEq_check (LyapunovCert.isExponentiallyStable_of_check (Bool.eq_true_of_not_eq_false hl))
  have hq : ofList neg.size negEq = 0 := by funext j; fin_cases j <;> decide
  have hz : realOfList neg.size negEq = 0 := by
    funext j; simp only [realOfList, hq, Pi.zero_apply, Rat.cast_zero]
  set K := ‖WithLp.toLp 2 (Fin.append ((fun t _ => (1 : ℝ) * Real.exp t) 0)
    ((fun t => ![(1 : ℝ) * Real.exp t, 1 * Real.exp t, -2 * (1 * Real.exp t)]) 0) -
      realOfList neg.size negEq)‖
  have hb : ∀ t ≥ 0, Real.exp t ≤ |M| * K := fun t ht => by
    have h1 := hM _ _ (neg_grow 1) t ht
    have h2 : Real.exp t ≤ M * Real.exp (-(α * t)) * K := by
      refine (le_trans (le_of_eq ?_) (norm_le_of_apply _ (Fin.castAdd _ 0))).trans h1
      rw [Pi.sub_apply, Fin.append_left, hz, Pi.zero_apply, sub_zero, one_mul,
        abs_of_pos (Real.exp_pos t)]
    have hK : 0 ≤ K := norm_nonneg _
    have he : Real.exp (-(α * t)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
    have : M * Real.exp (-(α * t)) ≤ |M| :=
      (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.exp_pos _).le).trans
        (mul_le_of_le_one_right (abs_nonneg M) he)
    nlinarith [mul_le_mul_of_nonneg_right this hK]
  have hMK : 0 ≤ |M| * K := by positivity
  have := hb (Real.log (|M| * K + 1)) (Real.log_nonneg (by linarith))
  rw [Real.exp_log (by positivity)] at this
  linarith

/-! ### Rejections -/

/-- Two voltage sources of 1 V and 2 V in parallel: no trajectory exists. -/
abbrev clash : Netlist where
  nodes := 1
  inputs := 0
  branches := [⟨1, 0, .voltageSource 1 none⟩, ⟨1, 0, .voltageSource 2 none⟩]

theorem clash_check : clash.check = true := by decide +kernel

theorem clash_no_trajectory {φ : ℝ → Fin clash.nodes → ℝ} {i : ℝ → Fin clash.branches.length → ℝ}
    (h : clash.IsTrajectoryOn 0 φ i (Ici 0)) : False := by
  have h0 := h.law 0 self_mem_Ici ⟨0, by decide⟩
  have h1 := h.law 0 self_mem_Ici ⟨1, by decide⟩
  simp only [clash, Element.Law, inputValue, List.get_eq_getElem] at h0 h1
  norm_num at h0 h1
  linarith

/-- **The inconsistent circuit has no accepted decoupling**: acceptance would give a
trajectory. -/
theorem clash_no_decoupling (d : DecouplingCert) :
    d.check clash.size clash.eRows clash.fRows = false := by
  by_contra hd
  set D := DecouplingCert.toDecoupling (m := clash.inputs) (G := clash.gRows) (b := clash.bList)
    (Bool.eq_true_of_not_eq_false hd)
  obtain ⟨z, hz, -⟩ := (D.exists_isSolutionOn_Ici_iff (u := 0) continuousOn_const
      (D.reconstruct 0 0)).2
    (by rw [DescriptorSystem.IndexOneDecoupling.Q₁'_mulVec_reconstruct]; rfl)
  have hz' : clash.mna.IsSolutionOn 0 z (Ici 0) := hz
  refine clash_no_trajectory (φ := fun t j => z t (Fin.castAdd _ j))
    (i := fun t b => z t (Fin.natAdd _ b)) ?_
  rw [Netlist.isTrajectoryOn_iff clash_check (uniqueDiffOn_Ici 0)]
  convert hz' using 1
  funext t
  exact Fin.append_castAdd_natAdd

/-- **Nor an accepted equilibrium.** -/
theorem clash_no_equilibrium (z₀ : List ℚ) :
    isEquilibriumRows clash.size clash.fRows clash.bList z₀ = false := by
  by_contra hz
  have h := (isEquilibrium_of_isEquilibriumRows (m := clash.inputs) (E := clash.eRows)
    (G := clash.gRows) (Bool.eq_true_of_not_eq_false hz)).isSolutionOn (Ici 0)
  refine clash_no_trajectory (φ := fun _ j => realOfList clash.size z₀ (Fin.castAdd _ j))
    (i := fun _ b => realOfList clash.size z₀ (Fin.natAdd _ b)) ?_
  have h' : clash.mna.IsSolutionOn 0 (fun _ => realOfList clash.size z₀) (Ici 0) := h
  rw [Netlist.isTrajectoryOn_iff clash_check (uniqueDiffOn_Ici 0)]
  convert h' using 1
  funext t
  exact Fin.append_castAdd_natAdd

/-- A 1 V source in parallel with `C = 1 F`: a capacitor–source loop (index two). Its only
trajectory is constant. -/
abbrev vc : Netlist where
  nodes := 1
  inputs := 0
  branches := [⟨1, 0, .voltageSource 1 none⟩, ⟨1, 0, .capacitor 1⟩]

theorem vc_check : vc.check = true := by decide +kernel

/-- Every trajectory of `vc` starts at `φ = 1`, `i = 0`. -/
theorem vc_initial {φ : ℝ → Fin vc.nodes → ℝ} {i : ℝ → Fin vc.branches.length → ℝ}
    (h : vc.IsTrajectoryOn 0 φ i (Ici 0)) : Fin.append (φ 0) (i 0) = ![1, 0, 0] := by
  have hv : ∀ t ∈ Ici (0 : ℝ), φ t 0 = 1 := fun t ht => by
    have := h.law t ht ⟨0, by decide⟩
    simpa [vc, Element.Law, inputValue, potential] using this
  have hC := h.law 0 self_mem_Ici ⟨1, by decide⟩
  simp only [vc, Element.Law, potential, List.get_eq_getElem] at hC
  norm_num at hC
  have hC' : HasDerivWithinAt (fun _ => (1 : ℝ)) (i 0 1) (Ici (0 : ℝ)) 0 :=
    hC.congr (fun t ht => (hv t ht).symm) (hv 0 self_mem_Ici).symm
  have hi1 : i 0 1 = 0 :=
    (uniqueDiffOn_Ici 0 0 self_mem_Ici).eq_deriv _ hC' (hasDerivWithinAt_const _ _ _)
  have hk : i 0 0 = 0 := by
    have := h.kcl 0 self_mem_Ici 0
    erw [Fin.sum_univ_two] at this
    simpa [Branch.incidence, hi1] using this
  funext j
  fin_cases j
  · exact (Fin.append_left (φ 0) (i 0) 0).trans (hv 0 self_mem_Ici)
  · exact (Fin.append_right (φ 0) (i 0) 0).trans hk
  · exact (Fin.append_right (φ 0) (i 0) 1).trans hi1

/-- **The index-two circuit has no accepted decoupling.** With `k ≥ 1` differential coordinates,
acceptance would give trajectories through two different differential states, but all
trajectories start at the same point; with `k = 0`, `E = E Q₁ Q₁'` would vanish, but `E` holds
the capacitance. -/
theorem vc_no_decoupling (d : DecouplingCert) : d.check vc.size vc.eRows vc.fRows = false := by
  by_contra hd
  set D := DecouplingCert.toDecoupling (m := vc.inputs) (G := vc.gRows) (b := vc.bList)
    (Bool.eq_true_of_not_eq_false hd)
  have traj : ∀ x₀ : Fin d.k → ℝ, realOfRows d.k vc.size d.Q₁' *ᵥ ![1, 0, 0] = x₀ := fun x₀ => by
    obtain ⟨z, hz, h0⟩ := (D.exists_isSolutionOn_Ici_iff (u := 0) continuousOn_const
        (D.reconstruct x₀ 0)).2
      (by rw [DescriptorSystem.IndexOneDecoupling.Q₁'_mulVec_reconstruct]; rfl)
    have hz' : vc.mna.IsSolutionOn 0 z (Ici 0) := hz
    have ht : vc.IsTrajectoryOn 0 (fun t j => z t (Fin.castAdd _ j))
        (fun t b => z t (Fin.natAdd _ b)) (Ici 0) := by
      rw [Netlist.isTrajectoryOn_iff vc_check (uniqueDiffOn_Ici 0)]
      convert hz' using 1
      funext t
      exact Fin.append_castAdd_natAdd
    rw [← vc_initial ht, Fin.append_castAdd_natAdd, h0]
    exact DescriptorSystem.IndexOneDecoupling.Q₁'_mulVec_reconstruct (D := D) x₀ 0
  rcases Nat.eq_zero_or_pos d.k with hk | hk
  · have hE := congrFun (congrFun D.E_eq_mul_Q₁_mul_Q₁' ⟨2, by decide⟩) ⟨0, by decide⟩
    have : IsEmpty (Fin d.k) := by rw [hk]; infer_instance
    simp only [Matrix.mul_apply, Finset.univ_eq_empty, Finset.sum_empty] at hE
    have hq : ofLists vc.size vc.size vc.eRows ⟨2, by decide⟩ ⟨0, by decide⟩ = 1 := by
      decide +kernel
    have : ((ofLists vc.size vc.size vc.eRows ⟨2, by decide⟩ ⟨0, by decide⟩ : ℚ) : ℝ) = 0 := hE
    rw [hq] at this
    norm_num at this
  · have h0 := traj 0
    have h1 := traj (Pi.single ⟨0, hk⟩ 1)
    have := congrFun (h0.symm.trans h1) ⟨0, hk⟩
    simp at this

/-- A corrupted decoupling of the RC circuit is rejected. -/
example : ({ rcDec with Q₁' := [[0, 1, 0, 0, 1]] } : DecouplingCert).check rc.size rc.eRows
    rc.fRows = false := by
  decide +kernel

/-- A netlist with a nonpositive resistance or an undefined node is rejected. -/
example : ({ rc with branches := [⟨1, 0, .resistor 0⟩] } : Netlist).check = false := by
  decide +kernel

example : ({ rc with branches := [⟨1, 3, .resistor 1⟩] } : Netlist).check = false := by
  decide +kernel

end CslibFrontierTests.CircuitMNA
