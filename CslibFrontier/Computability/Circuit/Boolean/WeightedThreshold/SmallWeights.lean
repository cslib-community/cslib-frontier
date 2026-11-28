/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Nat.Factorial.Basic
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Cramer
import CslibFrontier.Foundations.LinearAlgebra.Matrix.Vertex
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Basic.Real.Basic

/-!
# Small integer weights for threshold functions

A natural-weight threshold on Boolean inputs has an equivalent strict integer threshold with all
weights and its bias bounded by `(N + 1) · (N + 1)!`. This is the small-weight step needed to
simulate a majority gate that reads repeated wires.

A full-rank set of tight inequalities determines a separating vertex. Cramer's rule clears its
denominator, and the Leibniz determinant bound controls every coefficient. For the classical
weight-bound problem see [Muroga, §9.3.2][Muroga1971]. [Håstad, §3, Theorem 3.2][Hastad1994]
treats signed inputs and proves the sharper bound `2^(-N) (N + 1)^((N + 1)/2)`.
-/

public section

namespace Cslib.SmallWeights

open Finset Module Matrix

variable {ι : Type*} [Finite ι] {m : ℕ}

/-- The rows of `r` tight at `v`: those with `r j ⬝ᵥ v = 1`. -/
private noncomputable def tight (r : ι → Fin m → ℝ) (v : Fin m → ℝ) : Set (Fin m → ℝ) :=
  r '' {j | r j ⬝ᵥ v = 1}

/-- The rank of the rows tight at `v`. -/
private noncomputable def tightRank (r : ι → Fin m → ℝ) (v : Fin m → ℝ) : ℕ :=
  finrank ℝ (Submodule.span ℝ (tight r v))

omit [Finite ι] in
private theorem tightRank_le (r : ι → Fin m → ℝ) (v : Fin m → ℝ) : tightRank r v ≤ m :=
  (Submodule.finrank_le _).trans_eq (by simp)

/-- A linear functional on `Fin m → ℝ` is the dot product with its values on the basis vectors. -/
private theorem dual_apply_eq_dotProduct (f : Module.Dual ℝ (Fin m → ℝ)) (x : Fin m → ℝ) :
    f x = x ⬝ᵥ fun i => f (Pi.single i 1) := by
  rw [LinearMap.pi_apply_eq_sum_univ f x, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_eq_mul]
  congr 2
  funext j
  simp [Pi.single_apply, eq_comm]

/-- **One step towards a vertex**: if the rows tight at a feasible point do not span, moving along
a direction orthogonal to them makes a further row tight, so the tight rank grows. -/
private theorem exists_tightRank_lt (r : ι → Fin m → ℝ) (hspan : Submodule.span ℝ (Set.range r) = ⊤)
    {v : Fin m → ℝ} (hv : ∀ j, 1 ≤ r j ⬝ᵥ v) (hlt : Submodule.span ℝ (tight r v) ≠ ⊤) :
    ∃ v' : Fin m → ℝ, (∀ j, 1 ≤ r j ⬝ᵥ v') ∧ tightRank r v < tightRank r v' := by
  have : Fintype ι := Fintype.ofFinite ι
  obtain ⟨f₀, hf₀, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hlt)
  -- some row is not annihilated
  have hrow : ∃ j, f₀ (r j) ≠ 0 := by
    by_contra h
    push Not at h
    apply hf₀
    have : Submodule.span ℝ (Set.range r) ≤ LinearMap.ker f₀ :=
      Submodule.span_le.mpr (Set.range_subset_iff.mpr fun j => h j)
    rw [hspan, top_le_iff] at this
    exact LinearMap.ker_eq_top.mp this
  obtain ⟨j₀, hj₀⟩ := hrow
  -- orient the functional so that `j₀` decreases
  let f : Module.Dual ℝ (Fin m → ℝ) := if f₀ (r j₀) < 0 then f₀ else -f₀
  have hfj₀ : f (r j₀) < 0 := by
    simp only [f]
    split_ifs with h
    · exact h
    · simp only [LinearMap.neg_apply, neg_neg_iff_pos]
      exact lt_of_le_of_ne (not_lt.mp h) (Ne.symm hj₀)
  have hfker : Submodule.span ℝ (tight r v) ≤ LinearMap.ker f := by
    intro x hx
    have := hker hx
    simp only [LinearMap.mem_ker] at this ⊢
    simp only [f]
    split_ifs <;> simp [this]
  set d : Fin m → ℝ := fun i => f (Pi.single i 1)
  have hfd (x : Fin m → ℝ) : f x = x ⬝ᵥ d := dual_apply_eq_dotProduct f x
  let A : Matrix ι (Fin m) ℝ := -(Matrix.of r)
  have hA (z : Fin m → ℝ) (j : ι) : (A *ᵥ z) j = -(r j ⬝ᵥ z) := by
    exact congrFun (Matrix.neg_mulVec z (Matrix.of r)) j
  have hle : A *ᵥ v ≤ fun _ => (-1 : ℝ) := fun j => by
    rw [hA]
    exact neg_le_neg (hv j)
  have hdir : 0 < (A *ᵥ d) j₀ := by simpa only [hA, neg_pos, ← hfd] using hfj₀
  obtain ⟨t, j₁, hj₁, hfeas, htight⟩ := Matrix.exists_tight_add_smul hle hdir
  let v' := v + t • d
  have hj₁d : r j₁ ⬝ᵥ d < 0 := by simpa only [hA, neg_pos] using hj₁
  have hdot (j : ι) : r j ⬝ᵥ v' = r j ⬝ᵥ v + t * (r j ⬝ᵥ d) := by
    simp [v', dotProduct_add, dotProduct_smul]
  refine ⟨v', fun j => ?_, ?_⟩
  · simpa only [hA, neg_le_neg_iff] using hfeas j
  · -- Old tight rows stay tight, and a row outside their span becomes tight.
    have hsub : tight r v ⊆ tight r v' := by
      rintro _ ⟨j, hj, rfl⟩
      refine ⟨j, ?_, rfl⟩
      have hj' : r j ⬝ᵥ v = 1 := hj
      have h0 : f (r j) = 0 := hfker (Submodule.subset_span ⟨j, hj, rfl⟩)
      change r j ⬝ᵥ v' = 1
      rw [hdot, ← hfd, h0, mul_zero, add_zero, hj']
    have hj₁t : r j₁ ∈ tight r v' := by
      refine ⟨j₁, ?_, rfl⟩
      change r j₁ ⬝ᵥ (v + t • d) = 1
      simpa only [hA, neg_inj] using htight
    have hnot : r j₁ ∉ Submodule.span ℝ (tight r v) := by
      intro hmem
      have h0 : f (r j₁) = 0 := hfker hmem
      rw [hfd] at h0
      linarith
    have hlt' : Submodule.span ℝ (tight r v) < Submodule.span ℝ (tight r v') := by
      refine lt_of_le_of_ne (Submodule.span_mono hsub) fun heq => hnot ?_
      rw [heq]
      exact Submodule.subset_span hj₁t
    exact Submodule.finrank_lt_finrank_of_lt hlt'

/-- **A vertex of a feasible polyhedron whose rows span**: some feasible point has tight rows
spanning the whole space. -/
private theorem exists_span_tight_eq_top (r : ι → Fin m → ℝ)
    (hspan : Submodule.span ℝ (Set.range r) = ⊤)
    (hfeas : ∃ v : Fin m → ℝ, ∀ j, 1 ≤ r j ⬝ᵥ v) :
    ∃ v : Fin m → ℝ, (∀ j, 1 ≤ r j ⬝ᵥ v) ∧ Submodule.span ℝ (tight r v) = ⊤ := by
  classical
  let P : ℕ → Prop := fun k => ∃ v : Fin m → ℝ, (∀ j, 1 ≤ r j ⬝ᵥ v) ∧ k ≤ tightRank r v
  have hP0 : P 0 := by
    obtain ⟨v, hv⟩ := hfeas
    exact ⟨v, hv, Nat.zero_le _⟩
  obtain ⟨v, hv, hK⟩ := Nat.findGreatest_spec (Nat.zero_le m) hP0
  refine ⟨v, hv, ?_⟩
  by_contra hne
  obtain ⟨v', hv', hlt⟩ := exists_tightRank_lt r hspan hv hne
  have hPv' : P (tightRank r v') := ⟨v', hv', le_rfl⟩
  have := Nat.le_findGreatest (tightRank_le r v') hPv'
  omega

/-- **Tight linearly independent rows at a vertex**: there are a feasible point and `m` linearly
independent rows that are tight at it. -/
private theorem exists_tight_basis (r : ι → Fin m → ℝ) (hspan : Submodule.span ℝ (Set.range r) = ⊤)
    (hfeas : ∃ v : Fin m → ℝ, ∀ j, 1 ≤ r j ⬝ᵥ v) :
    ∃ (σ : Fin m → ι) (v : Fin m → ℝ), (∀ j, 1 ≤ r j ⬝ᵥ v) ∧ (∀ k, r (σ k) ⬝ᵥ v = 1) ∧
      LinearIndependent ℝ (fun k => r (σ k)) := by
  classical
  obtain ⟨v, hv, htop⟩ := exists_span_tight_eq_top r hspan hfeas
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent ℝ (tight r v)
  have hbfin : b.Finite := hbli.setFinite
  have : Fintype b := hbfin.fintype
  let B : Basis b ℝ (Fin m → ℝ) := Basis.mk hbli (by rw [Subtype.range_coe, hbspan, htop])
  have hcard : Fintype.card b = m := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  let e : Fin m ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hmem (k : Fin m) : ∃ j, r j ⬝ᵥ v = 1 ∧ r j = (e k : Fin m → ℝ) := by
    obtain ⟨j, hj, hjr⟩ := hbsub (e k).2
    exact ⟨j, hj, hjr⟩
  choose σ hσ hσr using hmem
  refine ⟨σ, v, hv, hσ, ?_⟩
  have : (fun k => r (σ k)) = (fun x : b => (x : Fin m → ℝ)) ∘ e := funext fun k => hσr k
  rw [this]
  exact hbli.comp e e.injective

/-- The real vector of an integer vector. -/
private abbrev toReal (x : Fin m → ℤ) : Fin m → ℝ := fun i => (x i : ℝ)

private theorem toReal_dotProduct (x y : Fin m → ℤ) :
    toReal x ⬝ᵥ toReal y = ((x ⬝ᵥ y : ℤ) : ℝ) := by
  simp [dotProduct]

omit [Finite ι] in
/-- **Integer weights from a vertex, by Cramer's rule**: if the integer rows `R` with entries in
`[-1, 1]` have a feasible point at which `m` linearly independent rows `R ∘ σ` are tight, there is
an integer point with every row at least `1` and every coordinate at most `m · m!` in absolute
value. -/
private theorem exists_int_point (R : ι → Fin m → ℤ) (hR : ∀ j i, |R j i| ≤ 1) (σ : Fin m → ι)
    (v : Fin m → ℝ) (hv : ∀ j, 1 ≤ toReal (R j) ⬝ᵥ v) (htight : ∀ k, toReal (R (σ k)) ⬝ᵥ v = 1)
    (hli : LinearIndependent ℝ (fun k => toReal (R (σ k)))) :
    ∃ u : Fin m → ℤ, (∀ j, 1 ≤ R j ⬝ᵥ u) ∧ ∀ i, |u i| ≤ m * m.factorial := by
  classical
  let A : Matrix (Fin m) (Fin m) ℤ := Matrix.of fun k i => R (σ k) i
  let AR : Matrix (Fin m) (Fin m) ℝ := (Int.castRingHom ℝ).mapMatrix A
  have hAR : AR.row = fun k => toReal (R (σ k)) := rfl
  have hdetR : AR.det ≠ 0 := by
    have := (Matrix.linearIndependent_row_iff_isUnit (A := AR)).mp (hAR ▸ hli)
    exact (Matrix.isUnit_iff_isUnit_det AR).mp this |>.ne_zero
  have hdet : A.det ≠ 0 := by
    intro h
    apply hdetR
    rw [show AR.det = ((Int.castRingHom ℝ) A.det) from (RingHom.map_det _ _).symm, h, map_zero]
  let w : Fin m → ℤ := A.adjugate *ᵥ fun _ => 1
  have hw : toReal w = (A.det : ℝ) • v := by
    have hcast : A.map (Int.cast : ℤ → ℝ) *ᵥ v = fun _ => (1 : ℝ) := funext fun k => htight k
    have hcramer := Matrix.intCast_cramer_eq_det_smul (c := fun _ => (1 : ℤ))
      (by simpa only [Int.cast_one] using hcast)
    simpa only [Matrix.cramer_eq_adjugate_mulVec, toReal, w] using hcramer
  refine ⟨A.det.sign • w, fun j => ?_, fun i => ?_⟩
  · have hreal : ((R j ⬝ᵥ (A.det.sign • w) : ℤ) : ℝ) =
        ((|A.det| : ℤ) : ℝ) * (toReal (R j) ⬝ᵥ v) := by
      rw [dotProduct_smul, smul_eq_mul, Int.cast_mul, ← toReal_dotProduct, hw, dotProduct_smul,
        smul_eq_mul, ← Int.sign_mul_self_eq_abs]
      push_cast
      ring
    have hpos : (1 : ℝ) ≤ ((|A.det| : ℤ) : ℝ) := by exact_mod_cast Int.one_le_abs hdet
    have : (1 : ℝ) ≤ ((R j ⬝ᵥ (A.det.sign • w) : ℤ) : ℝ) := by
      rw [hreal]
      nlinarith [hv j]
    exact_mod_cast this
  · -- each adjugate entry is a determinant of a matrix with entries in `[-1, 1]`
    have hentry (k : Fin m) : |A.adjugate i k| ≤ m.factorial := by
      rw [Matrix.adjugate_apply]
      have := Matrix.det_le (abv := AbsoluteValue.abs) (x := (1 : ℤ))
        (A := A.updateRow k (Pi.single i 1)) fun a b => by
          by_cases hak : a = k
          · subst hak
            simp only [Matrix.updateRow_self, Pi.single_apply]
            split_ifs <;> simp
          · rw [Matrix.updateRow_ne hak]
            exact hR _ _
      simpa [Fintype.card_fin] using this
    have hsign : |A.det.sign| ≤ 1 := by
      rcases Int.sign_trichotomy A.det with h | h | h <;> simp [h]
    calc |(A.det.sign • w) i| = |A.det.sign| * |w i| := by simp [abs_mul]
      _ ≤ 1 * |w i| := mul_le_mul_of_nonneg_right hsign (abs_nonneg _)
      _ = |∑ k, A.adjugate i k| := by simp [w, Matrix.mulVec, dotProduct]
      _ ≤ ∑ k, |A.adjugate i k| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin m, (m.factorial : ℤ) := Finset.sum_le_sum fun k _ => hentry k
      _ = m * m.factorial := by simp

/-- The dot product with an appended last coordinate. -/
private theorem snoc_dotProduct_snoc {R : Type*} [CommSemiring R] {N : ℕ} (x y : Fin N → R)
    (a b : R) :
    (Fin.snoc x a : Fin (N + 1) → R) ⬝ᵥ Fin.snoc y b = x ⬝ᵥ y + a * b := by
  simp [dotProduct, Fin.sum_univ_castSucc]

/-- The weight bound `(N + 1) · (N + 1)!` of `N`-input threshold functions. -/
@[expose] def weightBound (N : ℕ) : ℕ := (N + 1) * (N + 1).factorial

/-- Small-weight step for a majority gate with repeated wires. A threshold
function with nonnegative integer weights `c` and threshold `t` on `N` inputs is also a strict
threshold function with integer weights and threshold of absolute value at most
`(N + 1) · (N + 1)!`. The non-strict natural cutoff includes ties, while the signed realization
uses a strict cutoff. Håstad’s signed-input Theorem 3.2 [Hastad1994] gives a sharper bound. -/
theorem exists_small_threshold {N : ℕ} (c : Fin N → ℕ) (t : ℕ) :
    ∃ (u : Fin N → ℤ) (θ : ℤ), (∀ i, |u i| ≤ weightBound N) ∧ |θ| ≤ weightBound N ∧
      ∀ x : Fin N → Bool, (t ≤ ∑ i, c i * (x i).toNat ↔ θ < ∑ i, u i * (x i).toNat) := by
  classical
  let val : (Fin N → Bool) → Fin N → ℤ := fun x i => ((x i).toNat : ℤ)
  let sgn : (Fin N → Bool) → ℤ := fun x => if t ≤ ∑ i, c i * (x i).toNat then 1 else -1
  let R : (Fin N → Bool) → Fin (N + 1) → ℤ := fun x => sgn x • Fin.snoc (val x) (-1)
  have hsgn (x : Fin N → Bool) : |sgn x| = 1 := by simp only [sgn]; split_ifs <;> simp
  have hR : ∀ x k, |R x k| ≤ 1 := by
    intro x k
    simp only [R, Pi.smul_apply, smul_eq_mul, abs_mul, hsgn, one_mul]
    induction k using Fin.lastCases with
    | last => simp
    | cast i => simp only [Fin.snoc_castSucc, val]; cases x i <;> simp
  -- the rows span
  have hspan : Submodule.span ℝ (Set.range fun x => toReal (R x)) = ⊤ := by
    set S := Submodule.span ℝ (Set.range fun x => toReal (R x))
    have hmem (x : Fin N → Bool) : toReal (Fin.snoc (val x) (-1)) ∈ S := by
      have hsq : (sgn x : ℝ) * sgn x = 1 := by simp only [sgn]; split_ifs <;> norm_num
      have : toReal (Fin.snoc (val x) (-1)) = (sgn x : ℝ) • toReal (R x) := by
        funext k
        simp only [toReal, R, Pi.smul_apply, smul_eq_mul, Int.cast_mul]
        rw [← mul_assoc, hsq, one_mul]
      rw [this]
      exact S.smul_mem _ (Submodule.subset_span ⟨x, rfl⟩)
    have hlast : (Pi.single (Fin.last N) 1 : Fin (N + 1) → ℝ) ∈ S := by
      have h := S.neg_mem (hmem fun _ => false)
      convert h using 1
      funext k
      induction k using Fin.lastCases with
      | last => simp [toReal]
      | cast i => simp [toReal, val, Fin.castSucc_ne_last]
    have hcast (i : Fin N) : (Pi.single i.castSucc 1 : Fin (N + 1) → ℝ) ∈ S := by
      have h := S.add_mem (hmem fun j => decide (j = i)) hlast
      convert h using 1
      funext k
      induction k using Fin.lastCases with
      | last => simp [toReal, Fin.castSucc_ne_last]
      | cast j =>
        by_cases hij : j = i
        · subst hij; simp [toReal, val, Fin.castSucc_ne_last]
        · simp [toReal, val, hij, Fin.castSucc_ne_last,
            Fin.castSucc_injective N |>.ne hij]
    rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin (N + 1))).span_eq, Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    induction k using Fin.lastCases with
    | last => simpa using hlast
    | cast i => simpa using hcast i
  -- a feasible point
  have hfeas : ∃ v : Fin (N + 1) → ℝ, ∀ x, 1 ≤ toReal (R x) ⬝ᵥ v := by
    refine ⟨Fin.snoc (fun i => 2 * (c i : ℝ)) (2 * t - 1), fun x => ?_⟩
    have hdot : toReal (R x) ⬝ᵥ (Fin.snoc (fun i => 2 * (c i : ℝ)) (2 * t - 1)) =
        (sgn x : ℝ) * (2 * ((∑ i, c i * (x i).toNat : ℕ) : ℝ) - (2 * t - 1)) := by
      have : toReal (R x) = Fin.snoc (fun i => (sgn x : ℝ) * (val x i : ℝ)) (-(sgn x : ℝ)) := by
        funext k
        induction k using Fin.lastCases with
        | last => simp [toReal, R]
        | cast i => simp [toReal, R]
      rw [this, snoc_dotProduct_snoc]
      simp only [dotProduct, val, Int.cast_natCast]
      push_cast
      have hsum : ∑ i, (sgn x : ℝ) * ((x i).toNat : ℝ) * (2 * (c i : ℝ)) =
          (sgn x : ℝ) * (2 * ∑ i, (c i : ℝ) * ((x i).toNat : ℝ)) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
      rw [hsum]
      ring
    rw [hdot]
    simp only [sgn]
    split_ifs with h
    · have : (t : ℝ) ≤ ((∑ i, c i * (x i).toNat : ℕ) : ℝ) := by exact_mod_cast h
      push_cast at this ⊢
      linarith
    · have : ((∑ i, c i * (x i).toNat : ℕ) : ℝ) + 1 ≤ t := by
        exact_mod_cast Nat.lt_of_not_le h
      push_cast at this ⊢
      linarith
  obtain ⟨σ, v, hv, htight, hli⟩ := exists_tight_basis _ hspan hfeas
  obtain ⟨u, hu, hub⟩ := exists_int_point R hR σ v hv htight hli
  refine ⟨fun i => u i.castSucc, u (Fin.last N), fun i => by simpa [weightBound] using hub _,
    by simpa [weightBound] using hub _, fun x => ?_⟩
  have hrow : R x ⬝ᵥ u = sgn x * (∑ i, u i.castSucc * (x i).toNat - u (Fin.last N)) := by
    have : u = Fin.snoc (fun i => u i.castSucc) (u (Fin.last N)) := by
      funext k
      induction k using Fin.lastCases <;> simp
    rw [this, show R x = sgn x • Fin.snoc (val x) (-1) from rfl, smul_dotProduct,
      snoc_dotProduct_snoc]
    simp only [dotProduct, val, smul_eq_mul, Fin.snoc_castSucc, Fin.snoc_last]
    rw [Finset.sum_congr rfl fun i _ => mul_comm ((x i).toNat : ℤ) (u i.castSucc)]
    ring
  have h1 := hu x
  rw [hrow] at h1
  simp only [sgn] at h1
  split_ifs at h1 with h
  · exact ⟨fun _ => by linarith, fun _ => h⟩
  · exact ⟨fun h' => absurd h' h, fun h' => by linarith⟩

end Cslib.SmallWeights
