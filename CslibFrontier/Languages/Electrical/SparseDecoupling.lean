/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.SparseDescriptorCertificate
public import CslibFrontier.Languages.Electrical.LinearCircuit
import Mathlib.Data.List.GetD

/-!
# Certified stability of circuits through structured decouplings

The modified nodal equations of a netlist as sparse rows, built in one pass over the branches
(`Cslib.Electrical.Netlist.eSparse`, `fSparse`), and the circuit-level stability theorem of
`CslibFrontier.Languages.Electrical.LinearCircuit`
(`Cslib.Electrical.Netlist.isExponentiallyStable_of_decoupling`) for an accepted structured
certificate (`Cslib.LinearAlgebra.SparseDecouplingCert`), whose check is sparse and much faster
than that of a dense `Cslib.LinearAlgebra.DecouplingCert` on circuits of more than a few nodes.

## Main definitions

* `Cslib.Electrical.Netlist.eSparse`, `Cslib.Electrical.Netlist.fSparse`: the sparse rows of
  `E` and `F`.

## Main results

* `Cslib.Electrical.Netlist.mna_E_eq`, `Cslib.Electrical.Netlist.mna_F_eq`: they are the rows of
  the modified nodal equations.
* `Cslib.Electrical.Netlist.isExponentiallyStable_of_sparseCheck`
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

end Netlist

end Cslib.Electrical
