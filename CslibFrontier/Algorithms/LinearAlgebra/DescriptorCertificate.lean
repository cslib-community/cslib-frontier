/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.LinearAlgebra.LyapunovCertificate
public import CslibFrontier.Foundations.Analysis.ODE.Descriptor
import Mathlib.LinearAlgebra.Matrix.Integer

/-!
# Kernel-checked index-one decouplings of rational descriptor systems

A rational descriptor system `E ż = F z + G u + b` with `N` unknowns is given by the rows of `E`,
`F` and `G` and the list `b`, read with `Mathlib.Tactic.Matrix.ofLists` and cast to `ℝ`
(`Cslib.LinearAlgebra.descriptorOfRows`). An untrusted tool proposes an index-one decoupling
(`Cslib.LinearAlgebra.DecouplingCert`): the blocks `P₁`, `P₂` of a row transformation with a
left inverse `[P₁' P₂']`, and the blocks `Q₁`, `Q₂` of a change of unknowns with inverse
`[Q₁'; Q₂']`. The checker `DecouplingCert.check` recomputes, exactly over `ℚ`, the products

  `P E Q = [[1, 0], [0, 0]]`,  `P₁ F Q₂ = 0`,  `P₂ F Q₁ = 0`,  `P₂ F Q₂ = 1`,
  `P₁' P₁ + P₂' P₂ = 1`,  `Q₁ Q₁' + Q₂ Q₂' = 1`,  `Q₁' Q₁ = 1`,  `Q₁' Q₂ = 0`,

and acceptance yields a `DescriptorSystem.IndexOneDecoupling` of the real system
(`DecouplingCert.toDecoupling`), whose reduced ODE `ẋ = A x + B u + c` has the state matrix
`A = P₁ F Q₁`, supplied as `DecouplingCert.A` and checked. Nothing is assumed about `E`, and
no algebraic equation is dropped: the decoupling theorems of
`CslibFrontier.Foundations.Analysis.ODE.Descriptor` reconstruct every unknown.

A system of higher index, or one whose algebraic equations are singular (inconsistent or
underdetermined), has no accepted certificate, because acceptance implies the existence and
uniqueness theorems of the decoupling. Rejection of a particular certificate, however, says
nothing about the system.

An equilibrium `F z₀ + b = 0` is checked exactly (`Cslib.LinearAlgebra.isEquilibriumRows`), and
`DecouplingCert.isExponentiallyStableAt_of_check` composes the decoupling with the Lyapunov
checker `Cslib.LinearAlgebra.LyapunovCert.check` applied to `DecouplingCert.A`: acceptance proves that
every solution with zero input converges exponentially to `z₀`.

## Main definitions

* `Cslib.LinearAlgebra.descriptorOfRows`: the real descriptor system of rational rows.
* `Cslib.LinearAlgebra.DecouplingCert`, `DecouplingCert.check`.
* `Cslib.LinearAlgebra.isEquilibriumRows`: the exact equilibrium check.

## Main results

* `Cslib.LinearAlgebra.DecouplingCert.toDecoupling`: an accepted certificate is an index-one
  decoupling of the real system, with `DecouplingCert.A` as its state matrix
  (`DecouplingCert.A_toDecoupling`).
* `Cslib.LinearAlgebra.isEquilibrium_of_isEquilibriumRows`: soundness of the equilibrium check.
* `Cslib.LinearAlgebra.DecouplingCert.isExponentiallyStableAt_of_check`: decoupling, equilibrium
  and Lyapunov certificates prove exponential stability of the descriptor equilibrium.
-/

public section

open Matrix Mathlib.Tactic.Matrix

namespace Cslib.LinearAlgebra

/-- The real `m × n` matrix of rational rows. -/
abbrev realOfRows (m n : ℕ) (rows : List (List ℚ)) : Matrix (Fin m) (Fin n) ℝ :=
  (ofLists m n rows).map ((↑) : ℚ → ℝ)

/-- The real vector of a list of rationals, read with `ofList`. -/
abbrev realOfList (n : ℕ) (l : List ℚ) : Fin n → ℝ := fun i => ((ofList n l i : ℚ) : ℝ)

/-- The real descriptor system `E ż = F z + G u + b` with `N` unknowns and `m` inputs, from the
rational rows of `E`, `F`, `G` and the entries of `b`. -/
@[expose] noncomputable def descriptorOfRows (N m : ℕ) (E F G : List (List ℚ)) (b : List ℚ) :
    DescriptorSystem (Fin N) (Fin m) where
  E := realOfRows N N E
  F := realOfRows N N F
  G := realOfRows N m G
  b := realOfList N b

/-! ### Exact checks on rows -/

/-- Whether `rows`, read as an `m × n` matrix, is zero. -/
@[expose] def isZeroRows (m n : ℕ) (rows : List (List ℚ)) : Bool :=
  (List.range m).all fun i => (List.range n).all fun j => (rows.getD i []).getD j 0 == 0

/-- Whether `rows`, read as an `n × n` matrix, is the identity. -/
@[expose] def isOneRows (n : ℕ) (rows : List (List ℚ)) : Bool :=
  (List.range n).all fun i => (List.range n).all fun j =>
    (rows.getD i []).getD j 0 == if i = j then 1 else 0

theorem ofLists_eq_zero_of_isZeroRows {m n : ℕ} {rows : List (List ℚ)}
    (h : isZeroRows m n rows = true) : ofLists m n rows = 0 := by
  ext i j
  simp only [isZeroRows, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  simpa [ofLists_apply, ofList_apply] using h i i.is_lt j j.is_lt

theorem ofLists_eq_one_of_isOneRows {n : ℕ} {rows : List (List ℚ)}
    (h : isOneRows n rows = true) : ofLists n n rows = 1 := by
  ext i j
  simp only [isOneRows, List.all_eq_true, List.mem_range, beq_iff_eq] at h
  have := h i i.is_lt j j.is_lt
  rw [Matrix.one_apply]
  simpa [ofLists_apply, ofList_apply, Fin.val_inj] using this

/-- The rows of `A *ᵥ v` for `A` read as `m × n` and `v` read as a length-`n` vector. -/
@[expose] def rowsMulVec (m n : ℕ) (A : List (List ℚ)) (v : List ℚ) : List ℚ :=
  List.ofFn fun i : Fin m => rowDot ((A.getD i []).take n) v

theorem ofList_rowsMulVec (m n : ℕ) (A : List (List ℚ)) (v : List ℚ) :
    ofList m (rowsMulVec m n A v) = ofLists m n A *ᵥ ofList n v := by
  ext i
  rw [ofList_apply, rowsMulVec]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.is_lt,
    dite_true, Option.getD_some]
  rw [rowDot_eq_sum _ (List.length_take_le _ _)]
  simp only [mulVec, dotProduct, ofLists_apply, ofList_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [List.getD_eq_getElem?_getD, k.is_lt]

/-- Whether the first `n` entries of `v + w`, padded with zeros, vanish. -/
@[expose] def sumIsZero : ℕ → List ℚ → List ℚ → Bool
  | 0, _, _ => true
  | n + 1, v, w => v.headD 0 + w.headD 0 == 0 && sumIsZero n v.tail w.tail

theorem getD_add_getD_eq_zero_of_sumIsZero :
    ∀ {n : ℕ} {v w : List ℚ}, sumIsZero n v w = true → ∀ i < n, v.getD i 0 + w.getD i 0 = 0
  | 0, _, _, _, i, hi => absurd hi (Nat.not_lt_zero i)
  | n + 1, v, w, h, i, hi => by
    simp only [sumIsZero, Bool.and_eq_true, beq_iff_eq] at h
    rcases i with _ | i
    · cases v <;> cases w <;> simp_all
    · have := getD_add_getD_eq_zero_of_sumIsZero h.2 i (by omega)
      cases v <;> cases w <;> simp_all

/-- Whether `z₀` is an equilibrium, `F z₀ + b = 0`, of the system with `N` unknowns. -/
@[expose] def isEquilibriumRows (N : ℕ) (F : List (List ℚ)) (b z₀ : List ℚ) : Bool :=
  sumIsZero N (rowsMulVec N N F z₀) b

private theorem realOfRows_mul (a b c : ℕ) (X Y : List (List ℚ)) :
    realOfRows a b X * realOfRows b c Y = realOfRows a c (rowsMul a b c X Y) := by
  rw [realOfRows, realOfRows, realOfRows, ofLists_rowsMul, map_mul_ratCast]

private theorem realOfRows_add (a b : ℕ) (X Y : List (List ℚ)) :
    realOfRows a b X + realOfRows a b Y = realOfRows a b (rowsMap₂ (· + ·) a b X Y) := by
  rw [realOfRows, realOfRows, realOfRows, ofLists_rowsMap₂]
  ext i j
  simp

private theorem realOfRows_sub (a b : ℕ) (X Y : List (List ℚ)) :
    realOfRows a b X - realOfRows a b Y = realOfRows a b (rowsMap₂ (· - ·) a b X Y) := by
  rw [realOfRows, realOfRows, realOfRows, ofLists_rowsMap₂]
  ext i j
  simp

private theorem realOfRows_eq_one {n : ℕ} {rows : List (List ℚ)}
    (h : isOneRows n rows = true) : realOfRows n n rows = 1 := by
  rw [realOfRows, ofLists_eq_one_of_isOneRows h, Matrix.map_one _ Rat.cast_zero Rat.cast_one]

private theorem realOfRows_eq_zero {m n : ℕ} {rows : List (List ℚ)}
    (h : isZeroRows m n rows = true) : realOfRows m n rows = 0 := by
  rw [realOfRows, ofLists_eq_zero_of_isZeroRows h, Matrix.map_zero _ Rat.cast_zero]

/-- **Soundness of the equilibrium check.** -/
theorem isEquilibrium_of_isEquilibriumRows {N m : ℕ} {E F G : List (List ℚ)} {b z₀ : List ℚ}
    (h : isEquilibriumRows N F b z₀ = true) :
    (descriptorOfRows N m E F G b).IsEquilibrium (realOfList N z₀) := by
  have hq : ofLists N N F *ᵥ ofList N z₀ + ofList N b = 0 := by
    ext i
    have := getD_add_getD_eq_zero_of_sumIsZero h i i.is_lt
    rw [← ofList_apply, ← ofList_apply, ofList_rowsMulVec] at this
    simpa using this
  funext i
  have hi := congrArg (fun v => ((v i : ℚ) : ℝ)) hq
  simp only [Pi.add_apply, Pi.zero_apply, Rat.cast_add, Rat.cast_zero, mulVec, dotProduct,
    Rat.cast_sum, Rat.cast_mul] at hi
  change (realOfRows N N F *ᵥ realOfList N z₀) i + realOfList N b i = 0
  simpa only [mulVec, dotProduct, realOfRows, map_apply] using hi

/-! ### Decoupling certificates -/

/-- A proposed index-one decoupling of a descriptor system with `N` unknowns into `k`
differential and `r` algebraic coordinates; see the module documentation for the identities the
checker verifies. All blocks are lists of rational rows. -/
structure DecouplingCert where
  /-- The number of differential coordinates. -/
  k : ℕ
  /-- The number of algebraic coordinates. -/
  r : ℕ
  /-- `k × N`: rows producing the differential equations. -/
  P₁ : List (List ℚ)
  /-- `r × N`: rows producing the algebraic equations. -/
  P₂ : List (List ℚ)
  /-- `N × k`: left inverse of `P`, first block. -/
  P₁' : List (List ℚ)
  /-- `N × r`: left inverse of `P`, second block. -/
  P₂' : List (List ℚ)
  /-- `N × k`: unknowns from the differential coordinates. -/
  Q₁ : List (List ℚ)
  /-- `N × r`: unknowns from the algebraic coordinates. -/
  Q₂ : List (List ℚ)
  /-- `k × N`: differential coordinates of the unknowns. -/
  Q₁' : List (List ℚ)
  /-- `r × N`: algebraic coordinates of the unknowns. -/
  Q₂' : List (List ℚ)
  /-- `k × k`: the reduced state matrix `P₁ F Q₁`, checked. -/
  A : List (List ℚ)

namespace DecouplingCert

variable (c : DecouplingCert) (N : ℕ)

/-- The rows of the reduced input matrix `B = P₁ G`, for `m` inputs. -/
@[expose] def reducedB (m : ℕ) (G : List (List ℚ)) : List (List ℚ) := rowsMul c.k N m c.P₁ G

/-- The rows of the output matrix `C = H Q₁` of the output map `H` with `p` rows. -/
@[expose] def outputC (p : ℕ) (H : List (List ℚ)) : List (List ℚ) := rowsMul p N c.k H c.Q₁

/-- The rows of the feedthrough matrix `D = -(H Q₂ P₂ G)`. -/
@[expose] def feedthroughD (p m : ℕ) (H G : List (List ℚ)) : List (List ℚ) :=
  rowsMap₂ (fun x _ => -x) p m
    (rowsMul p N m (rowsMul p c.r N (rowsMul p N c.r H c.Q₂) c.P₂) G) ([] : List (List ℚ))

/-- Whether `c` is an index-one decoupling of the pencil `(E, F)` with `N` unknowns. All
products are recomputed exactly over `ℚ`. -/
@[expose] def check (E F : List (List ℚ)) : Bool :=
  let PE₁ := rowsMul c.k N N c.P₁ E
  let PE₂ := rowsMul c.r N N c.P₂ E
  let PF₁ := rowsMul c.k N N c.P₁ F
  let PF₂ := rowsMul c.r N N c.P₂ F
  isOneRows c.k (rowsMul c.k N c.k PE₁ c.Q₁) &&
  isZeroRows c.k c.r (rowsMul c.k N c.r PE₁ c.Q₂) &&
  isZeroRows c.r c.k (rowsMul c.r N c.k PE₂ c.Q₁) &&
  isZeroRows c.r c.r (rowsMul c.r N c.r PE₂ c.Q₂) &&
  isZeroRows c.k c.r (rowsMul c.k N c.r PF₁ c.Q₂) &&
  isZeroRows c.r c.k (rowsMul c.r N c.k PF₂ c.Q₁) &&
  isOneRows c.r (rowsMul c.r N c.r PF₂ c.Q₂) &&
  isOneRows N (rowsMap₂ (· + ·) N N (rowsMul N c.k N c.P₁' c.P₁) (rowsMul N c.r N c.P₂' c.P₂)) &&
  isOneRows N (rowsMap₂ (· + ·) N N (rowsMul N c.k N c.Q₁ c.Q₁') (rowsMul N c.r N c.Q₂ c.Q₂')) &&
  isOneRows c.k (rowsMul c.k N c.k c.Q₁' c.Q₁) &&
  isZeroRows c.k c.r (rowsMul c.k N c.r c.Q₁' c.Q₂) &&
  isZeroRows c.k c.k (rowsMap₂ (· - ·) c.k c.k (rowsMul c.k N c.k PF₁ c.Q₁) c.A)

variable {c N} {m : ℕ} {E F G : List (List ℚ)} {b : List ℚ}

/-- **Soundness.** An accepted certificate is an index-one decoupling of the real descriptor
system. -/
@[expose] noncomputable def toDecoupling (h : c.check N E F = true) :
    (descriptorOfRows N m E F G b).IndexOneDecoupling (Fin c.k) (Fin c.r) where
  P₁ := realOfRows c.k N c.P₁
  P₂ := realOfRows c.r N c.P₂
  P₁' := realOfRows N c.k c.P₁'
  P₂' := realOfRows N c.r c.P₂'
  Q₁ := realOfRows N c.k c.Q₁
  Q₂ := realOfRows N c.r c.Q₂
  Q₁' := realOfRows c.k N c.Q₁'
  Q₂' := realOfRows c.r N c.Q₂'
  E₁₁ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [descriptorOfRows, realOfRows_mul]
    exact realOfRows_eq_one (h.1.1.1.1.1.1.1.1.1.1.1)
  E₁₂ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [descriptorOfRows, realOfRows_mul]
    exact realOfRows_eq_zero (h.1.1.1.1.1.1.1.1.1.1.2)
  E₂₁ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [descriptorOfRows, realOfRows_mul]
    exact realOfRows_eq_zero (h.1.1.1.1.1.1.1.1.1.2)
  E₂₂ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [descriptorOfRows, realOfRows_mul]
    exact realOfRows_eq_zero (h.1.1.1.1.1.1.1.1.2)
  F₁₂ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [descriptorOfRows, realOfRows_mul]
    exact realOfRows_eq_zero (h.1.1.1.1.1.1.1.2)
  F₂₁ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [descriptorOfRows, realOfRows_mul]
    exact realOfRows_eq_zero (h.1.1.1.1.1.1.2)
  F₂₂ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [descriptorOfRows, realOfRows_mul]
    exact realOfRows_eq_one (h.1.1.1.1.1.2)
  P_inv := by
    simp only [check, Bool.and_eq_true] at h
    simp only [realOfRows_mul, realOfRows_add]
    exact realOfRows_eq_one (h.1.1.1.1.2)
  Q_inv := by
    simp only [check, Bool.and_eq_true] at h
    simp only [realOfRows_mul, realOfRows_add]
    exact realOfRows_eq_one (h.1.1.1.2)
  Q₁'_Q₁ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [realOfRows_mul]
    exact realOfRows_eq_one (h.1.1.2)
  Q₁'_Q₂ := by
    simp only [check, Bool.and_eq_true] at h
    simp only [realOfRows_mul]
    exact realOfRows_eq_zero (h.1.2)

/-- The state matrix of the decoupling is the matrix of the checked `DecouplingCert.A`. -/
theorem A_toDecoupling (h : c.check N E F = true) :
    (toDecoupling (m := m) (G := G) (b := b) h).A = realOfRows c.k c.k c.A := by
  simp only [check, Bool.and_eq_true] at h
  have h0 := realOfRows_eq_zero h.2
  rw [← realOfRows_sub, sub_eq_zero] at h0
  simp only [toDecoupling, DescriptorSystem.IndexOneDecoupling.A, descriptorOfRows]
  rw [← h0, realOfRows_mul, realOfRows_mul]

/-- **The checked realization.** The proper realization of an accepted decoupling with output
map `H` has the rational matrices `A`, `reducedB`, `outputC` and `feedthroughD`. -/
theorem realization_toDecoupling (h : c.check N E F = true) (p : ℕ) (H : List (List ℚ)) :
    (toDecoupling (m := m) (G := G) (b := b) h).realization (realOfRows p N H) =
      { A := realOfRows c.k c.k (c.A), B := realOfRows c.k m (c.reducedB N m G),
        C := realOfRows p c.k (c.outputC N p H),
        D := realOfRows p m (c.feedthroughD N p m H G) } := by
  simp only [DescriptorSystem.IndexOneDecoupling.realization, A_toDecoupling]
  congr 1
  · simp [toDecoupling, DescriptorSystem.IndexOneDecoupling.B, descriptorOfRows, reducedB,
      realOfRows_mul]
  · simp [toDecoupling, outputC, realOfRows_mul]
  · have hD : realOfRows p N H * realOfRows N c.r c.Q₂ * realOfRows c.r N c.P₂ *
        realOfRows N m G = realOfRows p m
          (rowsMul p N m (rowsMul p c.r N (rowsMul p N c.r H c.Q₂) c.P₂) G) := by
      simp only [realOfRows_mul]
    have := congrArg Neg.neg hD
    simp only [toDecoupling, descriptorOfRows]
    rw [this, feedthroughD, realOfRows, realOfRows, ofLists_rowsMap₂]
    ext i j
    simp

/-- **End-to-end descriptor stability certificate.** If `c` is an accepted decoupling of
`(E, F)`, `z₀` passes the exact equilibrium check, and the Lyapunov certificate `l` is accepted
for the reduced matrix `A` and a rational `P`, then every solution with zero input of the
real descriptor system converges to `z₀` exponentially, in the Euclidean norm. -/
theorem isExponentiallyStableAt_of_check {z₀ : List ℚ} {l : LyapunovCert} {P : List (List ℚ)}
    (hc : c.check N E F = true) (hz : isEquilibriumRows N F b z₀ = true)
    (hl : l.check c.k (c.A) P = true) :
    (descriptorOfRows N m E F G b).IsExponentiallyStableAt (realOfList N z₀) := by
  refine (toDecoupling hc).isExponentiallyStableAt (isEquilibrium_of_isEquilibriumRows hz) ?_
  rw [A_toDecoupling]
  exact LyapunovCert.isExponentiallyStable_of_check hl

end DecouplingCert

end Cslib.LinearAlgebra
