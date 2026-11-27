/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.SparseDescriptorRealization
public import CslibFrontier.Languages.Electrical.LinearCircuit
import Mathlib.Data.List.GetD

/-!
# Certified stability of circuits through structured decouplings

The circuit-level stability theorem of `CslibFrontier.Languages.Electrical.LinearCircuit`,
for any index-one decoupling of the modified nodal equations
(`Cslib.Electrical.Netlist.isExponentiallyStable_of_decoupling`), and its instance for an
accepted structured certificate (`Cslib.LinearAlgebra.SparseDecouplingCert`), whose check is
sparse and much faster than that of a dense `Cslib.LinearAlgebra.DecouplingCert` on circuits of
more than a few nodes.

With the input data of a `Cslib.LinearAlgebra.SparseRealizationCert` and the sparse
equilibrium check `Cslib.LinearAlgebra.isEquilibriumSparse`, nothing dense is checked: the
checked proper realization `ẋ = A x + B u`, `y - y₀ = C x + D u` for selected probes and the
input ports (`Cslib.Electrical.Netlist.sparseRealization`) is the same statement as the dense
`Cslib.Electrical.Netlist.isTrajectoryOn_iff_realization`, and its response kernel gives the
zero-state response of the circuit (`IsTrajectoryOn.probe_sub_eq_integral_sparse`).

## Main definitions

* `Cslib.Electrical.Netlist.eSparse`, `fSparse`, `gSparse`, `probeSparse`: sparse rows of the
  modified nodal equations and of the probes.
* `Cslib.Electrical.Netlist.sparseRealization`: the checked realization.

## Main results

* `Cslib.Electrical.Netlist.isExponentiallyStable_of_decoupling`
* `Cslib.Electrical.Netlist.isExponentiallyStable_of_sparseCheck`,
  `Cslib.Electrical.Netlist.isExponentiallyStable_of_sparseChecks`
* `Cslib.Electrical.Netlist.isTrajectoryOn_iff_sparseRealization`,
  `Cslib.Electrical.Netlist.IsTrajectoryOn.probe_sub_eq_sparse`,
  `Cslib.Electrical.Netlist.IsTrajectoryOn.probe_sub_eq_integral_sparse`
-/

public section

open Set Matrix Mathlib.Tactic.Matrix Cslib.LinearAlgebra

namespace Cslib.Electrical

/-! ### Sparse rows of the modified nodal equations -/

/-- The sparse row of the voltage `φ_p - φ_q`, with `n` potential columns (`vrow`). -/
@[expose] def vSparse (n p q : ℕ) : List (ℕ × ℚ) :=
  (if p ≠ 0 ∧ p ≤ n then [(p - 1, 1)] else []) ++ (if q ≠ 0 ∧ q ≤ n then [(q - 1, -1)] else [])

theorem sparseGet_vSparse (n p q j : ℕ) : sparseGet (vSparse n p q) j = vrow n p q j := by
  simp only [vSparse, vrow, sparseGet_append]
  split_ifs <;> simp only [sparseGet_cons, sparseGet_nil] <;> (try split_ifs) <;>
    first | (exfalso; omega) | norm_num

/-- The stamp row of branch `b` in `E`. -/
@[expose] def branchERow (n b : ℕ) (br : Branch) : List (ℕ × ℚ) :=
  sparseScale br.elem.stamp.eV (vSparse n br.pos br.neg) ++ [(n + b, br.elem.stamp.eI)]

/-- The stamp row of branch `b` in `F`. -/
@[expose] def branchFRow (n b : ℕ) (br : Branch) : List (ℕ × ℚ) :=
  sparseScale br.elem.stamp.fV (vSparse n br.pos br.neg) ++ [(n + b, br.elem.stamp.fI)] ++
    sparseScale br.elem.stamp.fC (vSparse n br.elem.stamp.cp br.elem.stamp.cn)

/-- A voltage term and a current term of a stamp row. -/
private theorem sparseGet_stamp (n b p q j : ℕ) (a x : ℚ) :
    sparseGet (sparseScale a (vSparse n p q) ++ [(n + b, x)]) j =
      a * vrow n p q j + x * crow n b j := by
  simp only [sparseGet_append, sparseGet_sparseScale, sparseGet_vSparse, sparseGet_cons,
    sparseGet_nil, crow, add_zero]
  by_cases h : j = n + b
  · rw [ite_eq_left h.symm, ite_eq_left h, mul_one]
  · rw [ite_eq_right (Ne.symm h), ite_eq_right h, mul_zero]

/-- The KCL row of node `k`: `-incidence` at the current column of each branch, from branch
`b` on. -/
@[expose] def kclRow (n k : ℕ) : ℕ → List Branch → List (ℕ × ℚ)
  | _, [] => []
  | b, br :: brs => (n + b, -br.incidence k) :: kclRow n k (b + 1) brs

/-- The rows `f b br` of the branches from index `b` on, without random access. -/
@[expose] def mapBranches (f : ℕ → Branch → List (ℕ × ℚ)) :
    ℕ → List Branch → List (List (ℕ × ℚ))
  | _, [] => []
  | b, br :: brs => f b br :: mapBranches f (b + 1) brs

private theorem getD_mapBranches (f : ℕ → Branch → List (ℕ × ℚ)) :
    ∀ (b : ℕ) (l : List Branch) (i : ℕ),
      (mapBranches f b l).getD i [] = if i < l.length then f (b + i) (l.getD i default) else []
  | _, [], _ => by simp [mapBranches]
  | b, br :: brs, 0 => by simp [mapBranches]
  | b, br :: brs, i + 1 => by
    simp only [mapBranches, List.getD_cons_succ, getD_mapBranches f (b + 1) brs i,
      List.length_cons, Nat.add_lt_add_iff_right, show b + 1 + i = b + (i + 1) by omega]

private theorem sparseGet_kclRow (n k : ℕ) :
    ∀ (b : ℕ) (l : List Branch) (j : ℕ), sparseGet (kclRow n k b l) j =
      if n + b ≤ j ∧ j - (n + b) < l.length then -(l.getD (j - (n + b)) default).incidence k
      else 0
  | _, [], _ => by simp [kclRow]
  | b, br :: brs, j => by
    rw [kclRow, sparseGet_cons, sparseGet_kclRow n k (b + 1) brs j]
    rcases Nat.lt_trichotomy j (n + b) with h | h | h
    · rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]
    · subst h
      rw [ite_eq_left rfl, ite_eq_right (by omega), ite_eq_left (by simp), Nat.sub_self]
      simp
    · rw [ite_eq_right (by omega)]
      obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_lt h
      simp only [show n + b + t + 1 - (n + (b + 1)) = t by omega,
        show n + b + t + 1 - (n + b) = t + 1 by omega, List.length_cons, List.getD_cons_succ]
      by_cases ht : t < brs.length
      · rw [ite_eq_left ⟨by omega, ht⟩, ite_eq_left ⟨by omega, by omega⟩]
      · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

namespace Netlist

variable (c : Netlist)

/-- The sparse rows of `E`, built from the stamps in one pass over the branches. -/
@[expose] def eSparse : List (List (ℕ × ℚ)) :=
  List.replicate c.nodes [] ++
    mapBranches (fun b br => (branchERow c.nodes b br).filter fun e => e.2 != 0) 0 c.branches

/-- The sparse rows of `F`, built from the stamps in one pass over the branches per row. -/
@[expose] def fSparse : List (List (ℕ × ℚ)) :=
  (List.range c.nodes).map (fun r => (kclRow c.nodes (r + 1) 0 c.branches).filter
      fun e => e.2 != 0) ++
    mapBranches (fun b br => (branchFRow c.nodes b br).filter fun e => e.2 != 0) 0 c.branches

variable {c}

private theorem realOfSparse_eq_rowsOf {R : List (List (ℕ × ℚ))} {g : ℕ → ℕ → ℚ}
    (h : ∀ r j, r < c.size → j < c.size → sparseGet (R.getD r []) j = g r j) :
    realOfSparse c.size c.size R = realOfRows c.size c.size (rowsOf c.size c.size g) := by
  ext i j
  rw [realOfSparse, map_apply, ofSparse_apply, h i j i.is_lt j.is_lt, realOfRows, map_apply,
    ofLists_apply, ofList_apply]
  simp [rowsOf, List.getD_eq_getElem?_getD]

private theorem getD_branchRows {f : ℕ → Branch → List (ℕ × ℚ)} {A : List (List (ℕ × ℚ))}
    (hA : A.length = c.nodes) {r : ℕ} (hr : c.nodes ≤ r) (hr' : r < c.size) :
    (A ++ mapBranches f 0 c.branches).getD r [] = f (r - c.nodes) (c.branch (r - c.nodes)) := by
  simp only [size] at hr'
  rw [List.getD_append_right _ _ _ _ (by omega), getD_mapBranches, hA, ite_eq_left (by omega),
    zero_add, branch]

theorem mna_E_eq : c.mna.E = realOfSparse c.size c.size c.eSparse := by
  refine (realOfSparse_eq_rowsOf fun r j hr _ => ?_).symm
  rw [eEntry]
  by_cases hrn : r < c.nodes
  · rw [ite_eq_left hrn, eSparse, List.getD_append _ _ _ _ (by simpa using hrn)]
    simp [List.getD_eq_getElem?_getD, hrn]
  · rw [ite_eq_right hrn, eSparse, getD_branchRows (by simp) (by omega) hr,
      sparseGet_filter_ne_zero, branchERow, sparseGet_stamp]

theorem mna_F_eq : c.mna.F = realOfSparse c.size c.size c.fSparse := by
  refine (realOfSparse_eq_rowsOf fun r j hr hj => ?_).symm
  rw [fEntry]
  by_cases hrn : r < c.nodes
  · rw [ite_eq_left hrn, fSparse, List.getD_append _ _ _ _ (by simpa using hrn),
      show ((List.range c.nodes).map fun r => (kclRow c.nodes (r + 1) 0 c.branches).filter
        fun e => e.2 != 0).getD r [] = (kclRow c.nodes (r + 1) 0 c.branches).filter
        fun e => e.2 != 0 by simp [List.getD_eq_getElem?_getD, hrn],
      sparseGet_filter_ne_zero, sparseGet_kclRow, add_zero]
    simp only [size] at hj
    by_cases hjn : c.nodes ≤ j
    · rw [ite_eq_left ⟨hjn, by omega⟩, ite_eq_left hjn, branch]
    · rw [ite_eq_right fun h => hjn h.1, ite_eq_right hjn]
  · rw [ite_eq_right hrn, fSparse, getD_branchRows (by simp) (by omega) hr,
      sparseGet_filter_ne_zero, branchFRow, sparseGet_append, sparseGet_stamp,
      sparseGet_sparseScale, sparseGet_vSparse]

variable {c : Netlist}

/-- **Exponential stability of a circuit from a decoupling.** Let the netlist be well formed, `D`
an index-one decoupling of its modified nodal equations, `z₀` an equilibrium, and `ẋ = A x`
exponentially stable for the state matrix of `D`. Then, with zero input, `z₀` is a circuit
trajectory, every differential state `x₀` (read through `D.Q₁'`) starts a circuit trajectory on
`[0, ∞)`, and every circuit trajectory on `[0, ∞)` converges to `z₀` exponentially in the
Euclidean norm of all potentials and branch currents. -/
theorem isExponentiallyStable_of_decoupling {κ ρ : Type*} [Fintype κ] [Fintype ρ]
    [DecidableEq κ] [DecidableEq ρ] (hc : c.check = true) (D : c.mna.IndexOneDecoupling κ ρ)
    {z₀ : Fin c.size → ℝ} (heq : c.mna.IsEquilibrium z₀)
    (hA : (toEuclideanCLM (𝕜 := ℝ) D.A).IsExponentiallyStable) :
    c.IsTrajectoryOn 0 (fun _ j => z₀ (Fin.castAdd _ j)) (fun _ b => z₀ (Fin.natAdd _ b))
        (Ici 0) ∧
      (∀ x₀ : κ → ℝ, ∃ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) ∧
        D.Q₁' *ᵥ Fin.append (φ 0) (i 0) = x₀) ∧
      ∃ M α : ℝ, 0 < α ∧ ∀ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) → ∀ t ≥ 0,
        ‖WithLp.toLp 2 (Fin.append (φ t) (i t) - z₀)‖ ≤
          M * Real.exp (-(α * t)) * ‖WithLp.toLp 2 (Fin.append (φ 0) (i 0) - z₀)‖ := by
  have hs := uniqueDiffOn_Ici (0 : ℝ)
  refine ⟨?_, fun x₀ => ?_, ?_⟩
  · rw [isTrajectoryOn_iff hc hs]
    simpa only [Fin.append_castAdd_natAdd] using heq.isSolutionOn (Ici 0)
  · obtain ⟨z, hz, h0⟩ := (D.exists_isSolutionOn_Ici_iff (u := 0) continuousOn_const
      (D.reconstruct x₀ 0)).2
      (by rw [DescriptorSystem.IndexOneDecoupling.Q₁'_mulVec_reconstruct]; rfl)
    refine ⟨fun t j => z t (Fin.castAdd _ j), fun t b => z t (Fin.natAdd _ b), ?_, ?_⟩
    · rw [isTrajectoryOn_iff hc hs]
      simpa only [Fin.append_castAdd_natAdd] using hz
    · rw [Fin.append_castAdd_natAdd, h0]
      exact DescriptorSystem.IndexOneDecoupling.Q₁'_mulVec_reconstruct (D := D) x₀ 0
  · obtain ⟨M, α, hα, hM⟩ := D.isExponentiallyStableAt heq hA
    exact ⟨M, α, hα, fun φ i h t ht => hM _ ((isTrajectoryOn_iff hc hs).1 h) t ht⟩

/-- **Certified exponential stability of a circuit, structured certificate.** The conclusions
of `isExponentiallyStable_of_decoupling` for an accepted structured decoupling `d`, an exactly
checked equilibrium `z₀` and the checked reduced matrix `d.A`; the differential coordinates
are the first `d.k` rows of `d.Uᵢ`. -/
theorem isExponentiallyStable_of_sparseCheck {d : SparseDecouplingCert} {z₀ : List ℚ}
    (hc : c.check = true) (hd : d.check c.size c.eSparse c.fSparse = true)
    (hz : isEquilibriumRows c.size c.fRows c.bList z₀ = true)
    (hA : (toEuclideanCLM (𝕜 := ℝ) (realOfRows d.k d.k d.A)).IsExponentiallyStable) :
    c.IsTrajectoryOn 0 (fun _ j => realOfList c.size z₀ (Fin.castAdd _ j))
        (fun _ b => realOfList c.size z₀ (Fin.natAdd _ b)) (Ici 0) ∧
      (∀ x₀ : Fin d.k → ℝ, ∃ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) ∧
        realOfSparse d.k c.size d.Uᵢ *ᵥ Fin.append (φ 0) (i 0) = x₀) ∧
      ∃ M α : ℝ, 0 < α ∧ ∀ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) → ∀ t ≥ 0,
        ‖WithLp.toLp 2 (Fin.append (φ t) (i t) - realOfList c.size z₀)‖ ≤
          M * Real.exp (-(α * t)) *
            ‖WithLp.toLp 2 (Fin.append (φ 0) (i 0) - realOfList c.size z₀)‖ := by
  have := isExponentiallyStable_of_decoupling hc
    (SparseDecouplingCert.toDecoupling mna_E_eq mna_F_eq hd)
    (isEquilibrium_of_isEquilibriumRows hz)
    (SparseDecouplingCert.A_toDecoupling mna_E_eq mna_F_eq hd ▸ hA)
  rwa [SparseDecouplingCert.Q₁'_toDecoupling] at this

/-- **Certified exponential stability of a circuit, fully sparse.** The conclusions of
`isExponentiallyStable_of_sparseCheck`, with the equilibrium checked against the sparse rows
of `F` (`isEquilibriumSparse`) instead of the dense rows. -/
theorem isExponentiallyStable_of_sparseChecks {d : SparseDecouplingCert} {z₀ : List ℚ}
    (hc : c.check = true) (hd : d.check c.size c.eSparse c.fSparse = true)
    (hz : isEquilibriumSparse c.size c.fSparse c.bList z₀ = true)
    (hA : (toEuclideanCLM (𝕜 := ℝ) (realOfRows d.k d.k d.A)).IsExponentiallyStable) :
    c.IsTrajectoryOn 0 (fun _ j => realOfList c.size z₀ (Fin.castAdd _ j))
        (fun _ b => realOfList c.size z₀ (Fin.natAdd _ b)) (Ici 0) ∧
      (∀ x₀ : Fin d.k → ℝ, ∃ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) ∧
        realOfSparse d.k c.size d.Uᵢ *ᵥ Fin.append (φ 0) (i 0) = x₀) ∧
      ∃ M α : ℝ, 0 < α ∧ ∀ φ i, c.IsTrajectoryOn 0 φ i (Ici 0) → ∀ t ≥ 0,
        ‖WithLp.toLp 2 (Fin.append (φ t) (i t) - realOfList c.size z₀)‖ ≤
          M * Real.exp (-(α * t)) *
            ‖WithLp.toLp 2 (Fin.append (φ 0) (i 0) - realOfList c.size z₀)‖ := by
  have := isExponentiallyStable_of_decoupling hc
    (SparseDecouplingCert.toDecoupling mna_E_eq mna_F_eq hd)
    (isEquilibrium_of_isEquilibriumSparse mna_F_eq rfl hz)
    (SparseDecouplingCert.A_toDecoupling mna_E_eq mna_F_eq hd ▸ hA)
  rwa [SparseDecouplingCert.Q₁'_toDecoupling] at this

/-! ### Checked realizations through structured decouplings -/

variable (c) in
/-- The sparse rows of the input matrix `G`. -/
@[expose] def gSparse : List (List (ℕ × ℚ)) := sparseOfRows c.gRows

variable (c) in
/-- The sparse rows of the output map of a list of probes. -/
@[expose] def probeSparse (probes : List Probe) : List (List (ℕ × ℚ)) :=
  sparseOfRows (c.probeRows probes)

/-- The input matrix of the modified nodal equations from its sparse rows. -/
theorem mna_G_eq : c.mna.G = realOfSparse c.size c.inputs c.gSparse :=
  (realOfSparse_sparseOfRows _ _ _).symm

variable (c) in
/-- The checked realization of a circuit through a structured decoupling `d` with input data
`e`, for the probes `probes` and the input ports of the circuit:
`ẋ = A x + B u`, `y = C x + D u` with `A = d.A`, `B = e.B`, `C = H Q₁` and `D = -H Q₂ P₂ G`
computed from sparse rows (`SparseRealizationCert.outputRows`, `feedthroughRows`). -/
@[expose] noncomputable def sparseRealization (d : SparseDecouplingCert)
    (e : SparseRealizationCert) (probes : List Probe) :
    LTISystem (Fin d.k) (Fin c.inputs) (Fin probes.length) where
  A := realOfRows d.k d.k d.A
  B := realOfSparse d.k c.inputs e.B
  C := realOfSparse probes.length d.k (SparseRealizationCert.outputRows d (c.probeSparse probes))
  D := realOfSparse probes.length c.inputs (e.feedthroughRows d (c.probeSparse probes))

/-- **Checked proper realization, structured certificate.** Let the netlist be well formed, `d`
an accepted structured decoupling, `e` accepted input data for it and `z₀` a checked
equilibrium. On a time set with unique derivatives and for every input signal `u`, `(φ, i)` is
a circuit trajectory exactly when

1. `z = (φ, i)` is reconstructed from the state `x = Uᵢ₁ (z - z₀)` (the first `d.k` rows of
   `d.Uᵢ`) and the input: `z = z₀ + Q₁ x - (Q₂ P₂ G) u`, with the sparse rows
   `d.stateRows` of `Q₁` and `e.inputRows d` of `Q₂ P₂ G`, and
2. `x` solves `ẋ = A x + B u` of `c.sparseRealization d e probes`.

The probed outputs then satisfy `y - y₀ = C x + D u` (`IsTrajectoryOn.probe_sub_eq_sparse`). -/
theorem isTrajectoryOn_iff_sparseRealization {d : SparseDecouplingCert}
    {e : SparseRealizationCert} {z₀ : List ℚ} (hc : c.check = true)
    (hd : d.check c.size c.eSparse c.fSparse = true)
    (he : e.check d c.size c.eSparse c.fSparse c.gSparse = true)
    (hz : isEquilibriumSparse c.size c.fSparse c.bList z₀ = true) (probes : List Probe)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {u : ℝ → Fin c.inputs → ℝ} {φ : ℝ → Fin c.nodes → ℝ}
    {i : ℝ → Fin c.branches.length → ℝ} :
    c.IsTrajectoryOn u φ i s ↔
      (∀ t ∈ s, Fin.append (φ t) (i t) = realOfList c.size z₀ +
          realOfSparse c.size d.k d.stateRows *ᵥ (realOfSparse d.k c.size d.Uᵢ *ᵥ
            (Fin.append (φ t) (i t) - realOfList c.size z₀)) -
          realOfSparse c.size c.inputs (e.inputRows d) *ᵥ u t) ∧
      (c.sparseRealization d e probes).IsSolutionOn u
        (fun t => realOfSparse d.k c.size d.Uᵢ *ᵥ
          (Fin.append (φ t) (i t) - realOfList c.size z₀)) s := by
  set D := SparseDecouplingCert.toDecoupling mna_E_eq mna_F_eq hd
  have hQ₂ := (SparseRealizationCert.Q₂_P₂_G_toDecoupling mna_E_eq mna_F_eq mna_G_eq hd he).1
  rw [isTrajectoryOn_iff hc hs, (D.isSolutionOn_iff_realization
    (realOfSparse probes.length c.size (c.probeSparse probes))
    (isEquilibrium_of_isEquilibriumSparse mna_F_eq rfl hz) hs),
    SparseRealizationCert.realization_toDecoupling mna_E_eq mna_F_eq mna_G_eq hd he,
    SparseDecouplingCert.Q₁'_toDecoupling, SparseDecouplingCert.Q₁_toDecoupling, ← hQ₂]
  simp only [mulVec_mulVec, Matrix.mul_assoc]
  rfl

/-- **Output equation, structured certificate.** Along a circuit trajectory, the probed outputs
differ from their values at the operating point by `C x + D u`, where `x = Uᵢ₁ (z - z₀)` is the
state of `c.sparseRealization d e probes`. -/
theorem IsTrajectoryOn.probe_sub_eq_sparse {d : SparseDecouplingCert}
    {e : SparseRealizationCert} {z₀ : List ℚ} (hc : c.check = true)
    (hd : d.check c.size c.eSparse c.fSparse = true)
    (he : e.check d c.size c.eSparse c.fSparse c.gSparse = true)
    (hz : isEquilibriumSparse c.size c.fSparse c.bList z₀ = true) (probes : List Probe)
    {s : Set ℝ} (hs : UniqueDiffOn ℝ s) {u : ℝ → Fin c.inputs → ℝ} {φ : ℝ → Fin c.nodes → ℝ}
    {i : ℝ → Fin c.branches.length → ℝ} (h : c.IsTrajectoryOn u φ i s) {t : ℝ} (ht : t ∈ s) :
    (fun o => (probes.get o).eval (φ t) (i t)) -
        (fun o => (probes.get o).eval (fun j => realOfList c.size z₀ (Fin.castAdd _ j))
          (fun b => realOfList c.size z₀ (Fin.natAdd _ b))) =
      (c.sparseRealization d e probes).C *ᵥ
          (realOfSparse d.k c.size d.Uᵢ *ᵥ (Fin.append (φ t) (i t) - realOfList c.size z₀)) +
        (c.sparseRealization d e probes).D *ᵥ u t := by
  set D := SparseDecouplingCert.toDecoupling mna_E_eq mna_F_eq hd
  have hQ₂ := (SparseRealizationCert.Q₂_P₂_G_toDecoupling mna_E_eq mna_F_eq mna_G_eq hd he).1
  have hrec := ((isTrajectoryOn_iff_sparseRealization hc hd he hz probes hs).1 h).1 t ht
  rw [← SparseDecouplingCert.Q₁_toDecoupling mna_E_eq mna_F_eq hd,
    ← SparseDecouplingCert.Q₁'_toDecoupling mna_E_eq mna_F_eq hd, ← hQ₂, ← mulVec_mulVec,
    ← mulVec_mulVec] at hrec
  have := D.output_eq (realOfSparse probes.length c.size (c.probeSparse probes)) hrec
  rw [SparseRealizationCert.realization_toDecoupling mna_E_eq mna_F_eq mna_G_eq hd he,
    SparseDecouplingCert.Q₁'_toDecoupling] at this
  have hH : realOfSparse probes.length c.size (c.probeSparse probes) =
      realOfRows probes.length c.size (c.probeRows probes) := realOfSparse_sparseOfRows _ _ _
  rw [hH] at this
  rw [← probeRows_mulVec, ← probeRows_mulVec, Fin.append_castAdd_natAdd]
  exact this

/-- **Zero-state response of a circuit, structured certificate.** For an input `u` continuous on
`[0, ∞)` and a circuit trajectory on `[0, ∞)` that starts at the operating point state
(`x 0 = Uᵢ₁ (z 0 - z₀) = 0`), the probed outputs are, for `t ≥ 0`,

  `y t - y₀ = D u t + ∫ s in 0..t, h (t - s) u s`,

with the response kernel `h t = C exp (t A) B` (`LTISystem.responseKernel`) and the direct
feedthrough `D` of `c.sparseRealization d e probes`. -/
theorem IsTrajectoryOn.probe_sub_eq_integral_sparse {d : SparseDecouplingCert}
    {e : SparseRealizationCert} {z₀ : List ℚ} (hc : c.check = true)
    (hd : d.check c.size c.eSparse c.fSparse = true)
    (he : e.check d c.size c.eSparse c.fSparse c.gSparse = true)
    (hz : isEquilibriumSparse c.size c.fSparse c.bList z₀ = true) (probes : List Probe)
    {u : ℝ → Fin c.inputs → ℝ} (hu : ContinuousOn u (Ici 0)) {φ : ℝ → Fin c.nodes → ℝ}
    {i : ℝ → Fin c.branches.length → ℝ} (h : c.IsTrajectoryOn u φ i (Ici 0))
    (h₀ : realOfSparse d.k c.size d.Uᵢ *ᵥ (Fin.append (φ 0) (i 0) - realOfList c.size z₀) = 0)
    {t : ℝ} (ht : 0 ≤ t) :
    (fun o => (probes.get o).eval (φ t) (i t)) -
        (fun o => (probes.get o).eval (fun j => realOfList c.size z₀ (Fin.castAdd _ j))
          (fun b => realOfList c.size z₀ (Fin.natAdd _ b))) =
      (c.sparseRealization d e probes).D *ᵥ u t +
        ∫ s in 0..t, (c.sparseRealization d e probes).responseKernel (t - s) *ᵥ u s := by
  have hx := ((isTrajectoryOn_iff_sparseRealization hc hd he hz probes
    (uniqueDiffOn_Ici 0)).1 h).2
  rw [h.probe_sub_eq_sparse hc hd he hz probes (uniqueDiffOn_Ici 0) ht,
    hx.output_eq_Ici hu ht, h₀, mulVec_zero, mulVec_zero, zero_add]

end Netlist

end Cslib.Electrical
