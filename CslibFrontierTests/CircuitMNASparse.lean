/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: local-only (tests)

import CslibFrontier.Languages.Electrical.SparseDecoupling
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Tests for structured (Schur-form) decouplings of circuits

Every certificate below was produced by an untrusted exact generator (a row permutation, a column
permutation with the eliminations for floating capacitors, sparse `LU` factors, `K` and `A`) and
is checked by the kernel (`decide +kernel`) against the sparse stamps of the netlist
(`Cslib.Electrical.Netlist.eSparse`, `fSparse`).

* **RC** and **damped series RLC**: end-to-end exponential stability through the structured
  decoupling and a dense Lyapunov certificate.
* **Fourth-order Sallen–Key filter** (`sk4`, 29 unknowns, 7 states): the structured decoupling
  is accepted in under a second of kernel time (the dense `DecouplingCert` takes about 12 s).
* **Sparse equilibria and realizations**: the operating points pass the sparse equilibrium
  check (a wrong one is rejected); for `rc`, the input data of the realization are accepted (a
  corrupted `W` is rejected), the checked realization from the source input to the capacitor
  voltage and the source node voltage is `A = -1`, `B = 1`, `C = (1, 0)ᵀ`, `D = (0, 1)ᵀ`, its
  response kernel is `h t = (e^{-t}, 0)ᵀ`, and every trajectory from the operating-point
  capacitor voltage has the zero-state response `D u t + ∫₀ᵗ h (t - s) u s ds`.
* **Rejections**: a corrupted `K` and a singular triangular factor are rejected.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.CircuitMNASparse

open Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra Cslib.Electrical

/-! ### RC -/

/-- A 1 V source (input port 0) at node 1, `R = 1 Ω` from node 1 to node 2, `C = 1 F` from
node 2 to ground. -/
abbrev rc : Netlist where
  nodes := 2
  inputs := 1
  branches := [⟨1, 0, .voltageSource 1 (some 0)⟩, ⟨1, 2, .resistor 1⟩, ⟨2, 0, .capacitor 1⟩]

/-- The structured decoupling of `rc`. -/
def rcSDec : SparseDecouplingCert where
  k := 1
  r := 4
  T := [[(4, 1)], [(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)]]
  Tᵢ := [[(1, 1)], [(2, 1)], [(3, 1)], [(4, 1)], [(0, 1)]]
  U := [[(3, 1)], [(0, 1)], [(1, 1)], [(4, 1)], [(2, 1)]]
  Uᵢ := [[(1, 1)], [(2, 1)], [(4, 1)], [(0, 1)], [(3, 1)]]
  LE := [[(0, 1)]]
  UE := [[(0, 1)]]
  LF := [[(0, 1)], [(1, 1)], [(2, 1)], [(2, (-1)), (3, 1)]]
  UF := [[(0, (-1)), (3, (-1))], [(1, (-1)), (3, 1)], [(2, (-1))], [(3, (-1))]]
  K := [[(0, (-1))], [(0, 1)], [], [(0, 1)]]
  A := [[-1]]

/-- The Lyapunov matrix for the reduced matrix of `rcSDec`. -/
def rcSP : List (List ℚ) := [[(1/2 : ℚ)]]

/-- The `LDLᵀ` witnesses for `rcSP` and its residual. -/
def rcSLyap : LyapunovCert := ⟨⟨[[1]], [(1/2 : ℚ)]⟩,
  ⟨[[1]], [1]⟩⟩

/-- The operating point `φ = (1, 1)`, `i = 0` of `rc`. -/
def rcEq : List ℚ := [1, 1, 0, 0, 0]

theorem rc_check : rc.check = true := by decide +kernel
theorem rcSDec_check : rcSDec.check rc.size rc.eSparse rc.fSparse = true := by decide +kernel
theorem rcEq_check : isEquilibriumRows rc.size rc.fRows rc.bList rcEq = true := by
  decide +kernel
theorem rcSLyap_check : rcSLyap.check rcSDec.k rcSDec.A rcSP = true := by decide +kernel

/-- Exponential stability of every RC trajectory about the operating point. -/
example := rc.isExponentiallyStable_of_sparseCheck rc_check rcSDec_check rcEq_check
  (LyapunovCert.isExponentiallyStable_of_check rcSLyap_check)

/-- A corrupted `K` is rejected. -/
example : ({ rcSDec with K := [[(0, 1)], [(0, 1)], [], [(0, 1)]] } : SparseDecouplingCert).check
    rc.size rc.eSparse rc.fSparse = false := by
  decide +kernel

/-- A singular upper triangular factor of the algebraic block is rejected. -/
example : ({ rcSDec with UF := [[(0, -1), (3, -1)], [(1, -1), (3, 1)], [(2, -1)], []] } :
    SparseDecouplingCert).check rc.size rc.eSparse rc.fSparse = false := by
  decide +kernel

/-! ### Damped series RLC -/

/-- A 1 V source at node 1, `R = 3 Ω` from node 1 to node 2, `L = 1 H` from node 2 to node 3 and
`C = 1/2 F` from node 3 to ground. -/
abbrev rlc : Netlist where
  nodes := 3
  inputs := 0
  branches := [⟨1, 0, .voltageSource 1 none⟩, ⟨1, 2, .resistor 3⟩, ⟨2, 3, .inductor 1⟩,
    ⟨3, 0, .capacitor (1/2)⟩]

/-- The structured decoupling of `rlc`. -/
def rlcSDec : SparseDecouplingCert where
  k := 2
  r := 5
  T := [[(5, 1)], [(6, 1)], [(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(4, 1)]]
  Tᵢ := [[(2, 1)], [(3, 1)], [(4, 1)], [(5, 1)], [(6, 1)], [(0, 1)], [(1, 1)]]
  U := [[(5, 1)], [(6, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(0, 1)], [(4, 1)]]
  Uᵢ := [[(5, 1)], [(2, 1)], [(3, 1)], [(4, 1)], [(6, 1)], [(0, 1)], [(1, 1)]]
  LE := [[(0, 1)], [(1, 1)]]
  UE := [[(0, 1)], [(1, (1/2 : ℚ))]]
  LF := [[(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(1, (-3)), (3, (-1)), (4, 1)]]
  UF := [[(0, (-1)), (1, (-1))], [(1, 1)], [(2, (-1))], [(3, (-1))], [(4, (-1))]]
  K := [[(0, 1)], [(0, (-1))], [(0, (-1))], [], [(0, 3)]]
  A := [[-3, -1], [2, 0]]

/-- The Lyapunov matrix for the reduced matrix of `rlcSDec`. -/
def rlcSP : List (List ℚ) := [[(1/2 : ℚ), (1/2 : ℚ)], [(1/2 : ℚ), 1]]

/-- The `LDLᵀ` witnesses for `rlcSP` and its residual. -/
def rlcSLyap : LyapunovCert := ⟨⟨[[1], [1, 1]], [(1/2 : ℚ), (1/2 : ℚ)]⟩,
  ⟨[[1], [0, 1]], [1, 1]⟩⟩

/-- The operating point of `rlc`. -/
def rlcEq : List ℚ := [1, 1, 1, 0, 0, 0, 0]

theorem rlc_check : rlc.check = true := by decide +kernel
theorem rlcSDec_check : rlcSDec.check rlc.size rlc.eSparse rlc.fSparse = true := by
  decide +kernel
theorem rlcEq_check : isEquilibriumRows rlc.size rlc.fRows rlc.bList rlcEq = true := by
  decide +kernel
theorem rlcSLyap_check : rlcSLyap.check rlcSDec.k rlcSDec.A rlcSP = true := by decide +kernel

/-- Exponential stability of every damped RLC trajectory about the operating point. -/
example := rlc.isExponentiallyStable_of_sparseCheck rlc_check rlcSDec_check rlcEq_check
  (LyapunovCert.isExponentiallyStable_of_check rlcSLyap_check)

/-! ### Fourth-order Sallen–Key low-pass filter -/

/-- Two cascaded unity-gain Sallen–Key low-pass stages (4th order), op-amps as one-pole
macromodels (gm = 10 mS, 10 MΩ, 22 pF, A0 = 1e5) with unity VCVS output buffers, a 10 µH input
inductor and a 10 kΩ load. -/
abbrev sk4 : Netlist where
  nodes := 10
  inputs := 1
  branches := [⟨1, 0, .voltageSource 0 (some 0)⟩, ⟨1, 2, .inductor (1/100000)⟩,
    ⟨2, 3, .resistor 10000⟩, ⟨3, 4, .resistor 10000⟩, ⟨3, 6, .capacitor (1/10000000)⟩,
    ⟨4, 0, .capacitor (47/1000000000)⟩, ⟨0, 5, .vccs (1/100) 4 6⟩, ⟨5, 0, .resistor 10000000⟩,
    ⟨5, 0, .capacitor (22/1000000000000)⟩, ⟨6, 0, .vcvs 1 5 0⟩,
    ⟨6, 7, .resistor 4700⟩, ⟨7, 8, .resistor 4700⟩, ⟨7, 10, .capacitor (1/10000000)⟩,
    ⟨8, 0, .capacitor (22/1000000000)⟩, ⟨0, 9, .vccs (1/100) 8 10⟩, ⟨9, 0, .resistor 10000000⟩,
    ⟨9, 0, .capacitor (22/1000000000000)⟩, ⟨10, 0, .vcvs 1 9 0⟩, ⟨10, 0, .resistor 10000⟩]

/-- The structured decoupling of `sk4`. -/
def sk4SDec : SparseDecouplingCert where
  k := 7
  r := 22
  T := [[(15, 1)], [(18, 1)], [(23, 1)], [(26, 1)], [(11, 1)], [(14, 1)], [(22, 1)], [(17, 1)],
    [(25, 1)], [(0, 1)], [(1, 1)], [(3, 1)], [(4, 1)], [(5, 1)], [(2, 1)], [(13, 1)], [(7, 1)],
    [(8, 1)], [(9, 1)], [(28, 1)], [(6, 1)], [(20, 1)], [(21, 1)], [(10, 1)], [(12, 1)], [(16,
    1)], [(19, 1)], [(24, 1)], [(27, 1)]]
  Tᵢ := [[(9, 1)], [(10, 1)], [(14, 1)], [(11, 1)], [(12, 1)], [(13, 1)], [(20, 1)], [(16, 1)],
    [(17, 1)], [(18, 1)], [(23, 1)], [(4, 1)], [(24, 1)], [(15, 1)], [(5, 1)], [(0, 1)], [(25,
    1)], [(7, 1)], [(1, 1)], [(26, 1)], [(21, 1)], [(22, 1)], [(6, 1)], [(2, 1)], [(27, 1)], [(8,
    1)], [(3, 1)], [(28, 1)], [(19, 1)]]
  U := [[(23, 1)], [(24, 1)], [(5, 1), (26, 1)], [(0, 1)], [(1, 1)], [(26, 1)], [(6, 1), (28,
    1)], [(2, 1)], [(3, 1)], [(28, 1)], [(9, 1)], [(4, 1)], [(10, 1)], [(15, 1)], [(14, 1)],
    [(11, 1)], [(25, 1)], [(7, 1)], [(12, 1)], [(13, 1)], [(21, 1)], [(22, 1)], [(20, 1)], [(16,
    1)], [(27, 1)], [(8, 1)], [(17, 1)], [(18, 1)], [(19, 1)]]
  Uᵢ := [[(3, 1)], [(4, 1)], [(7, 1)], [(8, 1)], [(11, 1)], [(2, 1), (5, (-1))], [(6, 1), (9,
    (-1))], [(17, 1)], [(25, 1)], [(10, 1)], [(12, 1)], [(15, 1)], [(18, 1)], [(19, 1)], [(14,
    1)], [(13, 1)], [(23, 1)], [(26, 1)], [(27, 1)], [(28, 1)], [(22, 1)], [(20, 1)], [(21, 1)],
    [(0, 1)], [(1, 1)], [(16, 1)], [(5, 1)], [(24, 1)], [(9, 1)]]
  LE := [[(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(4, 1)], [(5, 1)], [(6, 1)]]
  UE := [[(0, (47/1000000000 : ℚ))], [(1, (11/500000000000 : ℚ))], [(2, (11/500000000 : ℚ))],
    [(3, (11/500000000000 : ℚ))], [(4, (1/100000 : ℚ))], [(5, (1/10000000 : ℚ))], [(6,
    (1/10000000 : ℚ))]]
  LF := [[(0, 1)], [(1, 1)], [(2, 1)], [(3, 1)], [(4, 1)], [(0, (1/10000000 : ℚ)), (5, 1)], [(6,
    1)], [(3, (-1)), (7, 1)], [(8, 1)], [(9, 1)], [(1, (1/10000000 : ℚ)), (10, 1)], [(11, 1)],
    [(12, 1)], [(13, 1)], [(14, 1)], [(15, 1)], [(16, 1)], [(3, 10000), (17, 1)], [(18, 1)],
    [(19, 1)], [(20, 1)], [(21, 1)]]
  UF := [[(0, (-10000000))], [(1, (-10000000))], [(2, (-1))], [(3, (-1))], [(4, (-1)), (8, 1)],
    [(5, (-1)), (18, 1)], [(6, (-1)), (7, 1), (14, (-1))], [(7, (-1)), (8, (-1))], [(8,
    (-10000)), (19, 1)], [(9, (-1)), (15, 1)], [(10, (-1)), (20, 1)], [(11, (-1)), (12, (-1)),
    (13, 1)], [(12, (-10000)), (21, 1)], [(13, (-1)), (14, 1), (15, (-1))], [(14, (-4700)), (19,
    1), (21, (-1))], [(15, (-4700)), (21, 1)], [(16, (-1))], [(17, 1), (19, (-1))], [(18, (-1)),
    (19, (-1/100 : ℚ))], [(19, (-1))], [(20, (-1)), (21, (-1/100 : ℚ))], [(21, (-1))]]
  K := [[(1, (-1/10000000 : ℚ))], [(3, (-1/10000000 : ℚ))], [(4, 1)], [(4, (-1))], [(0,
    (1/10000 : ℚ)), (1, (-1/10000 : ℚ)), (5, (-1/10000 : ℚ))], [(0, (-1/100 : ℚ)), (1,
    (100001/10000000 : ℚ))], [(0, (-1/10000 : ℚ)), (1, (147/470000 : ℚ)), (3, (-1/4700 : ℚ)), (4,
    (-1)), (5, (1/10000 : ℚ)), (6, (-1/4700 : ℚ))], [(0, (-1/10000 : ℚ)), (1, (1/10000 : ℚ)), (4,
    (-1)), (5, (1/10000 : ℚ))], [(0, (1/10000 : ℚ)), (1, (-1/10000 : ℚ)), (5, (-1/10000 : ℚ))],
    [(2, (1/4700 : ℚ)), (3, (-1/4700 : ℚ)), (6, (-1/4700 : ℚ))], [(2, (-1/100 : ℚ)), (3,
    (100001/10000000 : ℚ))], [(1, (-1/4700 : ℚ)), (2, (-1/4700 : ℚ)), (3, (247/470000 : ℚ)), (6,
    (1/2350 : ℚ))], [(3, (-1/10000 : ℚ))], [(1, (-1/4700 : ℚ)), (2, (-1/4700 : ℚ)), (3,
    (1/2350 : ℚ)), (6, (1/2350 : ℚ))], [(1, (-1/4700 : ℚ)), (3, (1/4700 : ℚ)), (6,
    (1/4700 : ℚ))], [(2, (1/4700 : ℚ)), (3, (-1/4700 : ℚ)), (6, (-1/4700 : ℚ))], [], [(1, (-1)),
    (4, (-10000)), (5, (-1))], [(0, (-1/100 : ℚ)), (1, (1/100 : ℚ))], [(1, (-1))], [(2,
    (-1/100 : ℚ)), (3, (1/100 : ℚ))], [(3, (-1))]]
  A := [[(-100000/47 : ℚ), (100000/47 : ℚ), 0, 0, 0, (100000/47 : ℚ), 0], [(5000000000/11 : ℚ),
    -454550000, 0, 0, 0, 0, 0], [0, 0, (-5000000/517 : ℚ), (5000000/517 : ℚ), 0, 0,
    (5000000/517 : ℚ)], [0, 0, (5000000000/11 : ℚ), -454550000, 0, 0, 0], [0, -100000, 0, 0,
    -1000000000, -100000, 0], [1000, -1000, 0, 0, 10000000, -1000, 0], [0, (100000/47 : ℚ),
    (100000/47 : ℚ), (-200000/47 : ℚ), 0, 0, (-200000/47 : ℚ)]]

/-- The structured decoupling of the 29-unknown filter is accepted. -/
example : sk4SDec.check sk4.size sk4.eSparse sk4.fSparse = true := by decide +kernel

/-! ### Sparse equilibria and realizations -/

/-- The operating points of `rc` and `rlc` pass the sparse equilibrium check. -/
theorem rcEq_sparse : isEquilibriumSparse rc.size rc.fSparse rc.bList rcEq = true := by
  decide +kernel
theorem rlcEq_sparse : isEquilibriumSparse rlc.size rlc.fSparse rlc.bList rlcEq = true := by
  decide +kernel

/-- The stability theorem with the sparse equilibrium check. -/
example := rlc.isExponentiallyStable_of_sparseChecks rlc_check rlcSDec_check rlcEq_sparse
  (LyapunovCert.isExponentiallyStable_of_check rlcSLyap_check)

/-- A wrong operating point is rejected. -/
example : isEquilibriumSparse rc.size rc.fSparse rc.bList [1, 0, 0, 0, 0] = false := by
  decide +kernel

/-- The input data of the realization of `rc` through `rcSDec`. -/
def rcSReal : SparseRealizationCert where
  W := [[(0, 1)], [(0, (-1))], [(0, (-1))], [(0, (-1))]]
  B := [[(0, 1)]]

theorem rcSReal_check :
    rcSReal.check rcSDec rc.size rc.eSparse rc.fSparse rc.gSparse = true := by
  decide +kernel

/-- A corrupted `W` is rejected. -/
example : ({ rcSReal with W := [[(0, 1)], [(0, 1)], [(0, (-1))], [(0, (-1))]] } :
    SparseRealizationCert).check rcSDec rc.size rc.eSparse rc.fSparse rc.gSparse = false := by
  decide +kernel

/-- The probes: the capacitor voltage and the source node voltage. -/
abbrev rcProbes : List Probe := [.voltage 2 0, .voltage 1 0]

/-- The computed output rows of the realization of `rc`: `C = (1, 0)ᵀ` and `D = (0, 1)ᵀ`. -/
theorem rc_outputRows :
    eqSparse (SparseRealizationCert.outputRows rcSDec (rc.probeSparse rcProbes))
        [[(0, 1)], []] = true ∧
      eqSparse (rcSReal.feedthroughRows rcSDec (rc.probeSparse rcProbes)) [[], [(0, 1)]] =
        true := by
  decide +kernel

/-- **The checked realization of the RC circuit** through the structured certificate:
`A = -1`, `B = 1`, `C = (1, 0)ᵀ` and the direct feedthrough `D = (0, 1)ᵀ` of the source node. -/
theorem rc_sparseRealization :
    rc.sparseRealization rcSDec rcSReal rcProbes =
      ⟨of fun _ _ => -1, of fun _ _ => 1, of fun o _ => if o.val = 0 then 1 else 0,
        of fun o _ => if o.val = 0 then 0 else 1⟩ := by
  have hk : rcSDec.k = 1 := rfl
  have h0 : ∀ j : Fin rcSDec.k, j.val = 0 := fun j => by have := j.is_lt; omega
  simp only [Netlist.sparseRealization, realOfSparse_eq_of_eqSparse rc_outputRows.1,
    realOfSparse_eq_of_eqSparse rc_outputRows.2]
  congr 1 <;> ext i j
  · simp only [realOfRows, map_apply, of_apply, ofLists_apply, ofList_apply, h0]
    norm_num [rcSDec]
  · simp [realOfSparse, ofSparse_apply, rcSReal, sparseGet_cons, h0]
  · fin_cases i <;> simp [ofSparse_apply, sparseGet_cons, h0]
  · fin_cases i <;> fin_cases j <;> simp [ofSparse_apply, sparseGet_cons]

/-- **The impulse response of the RC circuit**: the response kernel of the checked realization
is `h t = (e^{-t}, 0)ᵀ` for `t ≥ 0`. -/
theorem rc_responseKernel {t : ℝ} (ht : 0 ≤ t) :
    (rc.sparseRealization rcSDec rcSReal rcProbes).responseKernel t =
      of fun o _ => if o.val = 0 then Real.exp (-t) else 0 := by
  have hk : Fintype.card (Fin rcSDec.k) = 1 := rfl
  rw [rc_sparseRealization, LTISystem.responseKernel_eq_of_hasDerivWithinAt
    (X := fun τ => of fun _ _ => Real.exp (-τ)) _ _ ht]
  · ext o j
    simp [Matrix.mul_apply, hk]
  · intro j τ _
    refine (hasDerivAt_pi.2 fun l => ?_).hasDerivWithinAt
    simpa [Matrix.mulVec, dotProduct, hk] using (hasDerivAt_neg τ).exp
  · ext i j
    simp

/-- **The zero-state response of the RC circuit**, from the structured certificates: for every
input `u` continuous on `[0, ∞)` and every circuit trajectory whose capacitor starts at its
operating-point voltage `1`, the probed outputs differ from their operating-point values by
`D u t + ∫₀ᵗ h (t - s) u s ds`, with `h t = (e^{-t}, 0)ᵀ` and `D = (0, 1)ᵀ`. -/
theorem rc_zeroState {u : ℝ → Fin rc.inputs → ℝ} (hu : ContinuousOn u (Set.Ici 0))
    {φ : ℝ → Fin rc.nodes → ℝ} {i : ℝ → Fin rc.branches.length → ℝ}
    (h : rc.IsTrajectoryOn u φ i (Set.Ici 0)) (h₀ : φ 0 1 = 1) {t : ℝ} (ht : 0 ≤ t) :
    (fun o => (rcProbes.get o).eval (φ t) (i t)) -
        (fun o => (rcProbes.get o).eval (fun j => realOfList rc.size rcEq (Fin.castAdd _ j))
          (fun b => realOfList rc.size rcEq (Fin.natAdd _ b))) =
      (of fun o _ => if o.val = 0 then 0 else 1 : Matrix (Fin 2) (Fin 1) ℝ) *ᵥ u t +
        ∫ s in 0..t, (of fun o _ => if o.val = 0 then Real.exp (-(t - s)) else 0 :
          Matrix (Fin 2) (Fin 1) ℝ) *ᵥ u s := by
  have hx : realOfSparse rcSDec.k rc.size rcSDec.Uᵢ *ᵥ
      (Fin.append (φ 0) (i 0) - realOfList rc.size rcEq) = 0 := by
    funext l
    have hl : l.val = 0 := by have := l.is_lt; change _ < 1 at this; omega
    simp only [mulVec, dotProduct, realOfSparse, map_apply, ofSparse_apply, Pi.zero_apply]
    rw [Finset.sum_eq_single (⟨1, by decide⟩ : Fin rc.size)]
    · simp [rcSDec, hl, sparseGet_cons, Fin.append, Fin.addCases, h₀, rcEq, realOfList,
        ofList_apply, Netlist.size]
    · intro j _ hj
      have hj' : j.val ≠ 1 := fun h => hj (Fin.ext h)
      simp [rcSDec, hl, sparseGet_cons, Ne.symm hj']
    · simp
  rw [h.probe_sub_eq_integral_sparse rc_check rcSDec_check rcSReal_check rcEq_sparse rcProbes
    hu hx ht, rc_sparseRealization]
  congr 1
  refine intervalIntegral.integral_congr fun s hs => ?_
  rw [Set.uIcc_of_le ht] at hs
  rw [← rc_sparseRealization, rc_responseKernel (sub_nonneg.2 hs.2)]
  rfl

end CslibFrontierTests.CircuitMNASparse
