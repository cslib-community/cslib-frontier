/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.LowIndividualDegree

/-!
# Polynomial-valued axis-line answers

A line answer with the requested domain and degree bound determines a univariate polynomial
function in any affine parameterization. The answer decoder agrees at every accepted point.
-/

public section

namespace Cslib.PCP.LowIndividualDegree

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- There is one axis-parallel line in one coordinate. -/
theorem linePoints_single_eq_univ (u : Point F 1) (i : Fin 1) :
    linePoints u (Pi.single i (1 : F)) = univ := by
  apply eq_univ_of_forall
  intro x
  have h : u + (x i - u i) • Pi.single i (1 : F) = x := by
    funext j
    rw [Subsingleton.elim j i]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
    abel
  rw [← h]
  exact mem_linePoints u (Pi.single i 1) (x i - u i)

/-- A polynomial answer on the full line, represented as a function on its points. -/
abbrev PolynomialFunction (F : Type*) [Field F] [Fintype F] [DecidableEq F] (d : ℕ) :=
  {f : ↥(univ : Finset (Point F 1)) → F // LineHasDegree f d}

noncomputable instance (d : ℕ) : Fintype (PolynomialFunction F d) := by
  unfold PolynomialFunction
  exact Fintype.ofFinite _

/-- Evaluate the polynomial function at an ambient point. -/
def PolynomialFunction.eval {d : ℕ} (f : PolynomialFunction F d) (u : Point F 1) : F :=
  f.val ⟨u, mem_univ u⟩

omit [Fintype F] [DecidableEq F] in
private theorem zero_add_smul_single (u : Point F 1) :
    (0 : Point F 1) + u 0 • Pi.single 0 (1 : F) = u := by
  funext j
  rw [Subsingleton.elim j 0]
  simp [Pi.smul_apply, smul_eq_mul]

private theorem polynomial_of_affine_answer {m d : ℕ} (u v : Point F m)
    (L : Finset (Point F m)) (f : L → F) (hL : linePoints u v = L) (hf : LineHasDegree f d) :
    ∃ p : Polynomial F, p.natDegree ≤ d ∧
      ∀ t : F, f ⟨u + t • v, hL ▸ mem_linePoints u v t⟩ = p.eval t := by
  subst L
  exact hf.exists_polynomial

/-- A legal answer on the whole line is represented by a univariate polynomial in the sole
coordinate, with the advertised degree bound. -/
theorem PolynomialFunction.exists_polynomial {d : ℕ} (f : PolynomialFunction F d) :
    ∃ p : Polynomial F, p.natDegree ≤ d ∧
      ∀ x : Point F 1, f.eval x = p.eval (x 0) := by
  obtain ⟨p, hp, he⟩ := polynomial_of_affine_answer 0 (Pi.single 0 1) univ f.val
    (linePoints_single_eq_univ 0 0) f.property
  refine ⟨p, hp, fun x => ?_⟩
  simpa only [PolynomialFunction.eval, zero_add_smul_single x] using he (x 0)

/-- Evaluate a univariate polynomial function at a field element. -/
def PolynomialFunction.value {d : ℕ} (p : PolynomialFunction F d) (t : F) : F :=
  p.eval (fun _ => t)

theorem PolynomialFunction.value_eq_eval {d : ℕ} (p : PolynomialFunction F d) (t : F) :
    p.value t = p.eval (fun _ => t) := by
  unfold value
  rfl

/-- The values at field elements determine a polynomial function. -/
theorem PolynomialFunction.value_injective {d : ℕ} :
    Function.Injective (PolynomialFunction.value : PolynomialFunction F d → F → F) := by
  intro f g h
  refine Subtype.ext (funext fun x => ?_)
  have hx : (fun _ : Fin 1 => x.val 0) = x.val :=
    funext fun j => congrArg x.val (Subsingleton.elim 0 j)
  simpa only [PolynomialFunction.value_eq_eval, PolynomialFunction.eval, hx] using
    congrFun h (x.val 0)

theorem PolynomialFunction.exists_polynomial_value {d : ℕ} (p : PolynomialFunction F d) :
    ∃ f : Polynomial F, f.natDegree ≤ d ∧ ∀ t, f.eval t = p.value t := by
  obtain ⟨f, hf, he⟩ := p.exists_polynomial
  exact ⟨f, hf, fun t => (he (fun _ => t)).symm⟩

/-- A degree-zero function takes the same value at every field element. -/
theorem PolynomialFunction.value_eq_of_degree_zero (f : PolynomialFunction F 0) (s t : F) :
    f.value s = f.value t := by
  obtain ⟨p, hp, he⟩ := f.exists_polynomial_value
  rw [← he s, ← he t, Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hp),
    Polynomial.eval_C, Polynomial.eval_C]

/-- Represent the evaluations of a degree-bounded univariate polynomial. -/
noncomputable def PolynomialFunction.ofPolynomial {d : ℕ} (p : Polynomial F)
    (hp : p.natDegree ≤ d) : PolynomialFunction F d :=
  ⟨fun u => p.eval (u.val 0), 0, Pi.single 0 1, linePoints_single_eq_univ 0 0, p, hp,
    fun t => by simp [Pi.smul_apply, smul_eq_mul]⟩

@[simp] theorem PolynomialFunction.eval_ofPolynomial {d : ℕ} (p : Polynomial F)
    (hp : p.natDegree ≤ d) (u : Point F 1) : (ofPolynomial p hp).eval u = p.eval (u 0) := by
  unfold eval ofPolynomial
  rfl

/-- Read the values of a line answer in the supplied affine parameterization.
Malformed answers are decoded to the zero polynomial. -/
noncomputable def decodeAffinePolynomial {m : ℕ} (d : ℕ) (u v : Point F m)
    (a : Answer F m) : PolynomialFunction F d := by
  classical
  let z : PolynomialFunction F d := .ofPolynomial 0 (by simp)
  cases a with
  | inl _ => exact z
  | inr a =>
    obtain ⟨L, f⟩ := a
    exact if hL : linePoints u v = L then
      if hf : LineHasDegree f d then
        let h := polynomial_of_affine_answer u v L f hL hf
        .ofPolynomial (Classical.choose h) (Classical.choose_spec h).1
      else z
    else z

/-- Read the point answer, using zero for a line answer sent to a point question. -/
def decodePoint {m : ℕ} : Answer F m → F
  | .inl z => z
  | .inr _ => 0

omit [Fintype F] [DecidableEq F] in
@[simp] theorem decodePoint_inl {m : ℕ} (a : F) :
    decodePoint (m := m) (Sum.inl a) = a := by
  unfold decodePoint
  rfl

omit [Fintype F] [DecidableEq F] in
@[simp] theorem decodePoint_inr {m : ℕ} (a : Σ L : Finset (Point F m), L → F) :
    decodePoint (Sum.inr a) = 0 := by
  unfold decodePoint
  rfl

/-- The affine decoder agrees with any accepted point answer on the queried line. -/
theorem decodeAffinePolynomial_agrees {m d : ℕ} (u v : Point F m) (t : F) (z : Point F 1)
    {a b : Answer F m} (h : accepts d (.axis (linePoints u v)) (.point (u + t • v)) a b)
    (hz : z 0 = t) :
    (decodeAffinePolynomial d u v a).eval z =
      decodePoint b := by
  classical
  obtain ⟨⟨L, f⟩, c, rfl, rfl, hL, hf, ⟨_, he⟩⟩ :=
    exists_legal_of_accepts_axis_point d _ _ a b h
  change L = linePoints u v at hL
  subst L
  unfold decodeAffinePolynomial
  simp only [dite_true, dite_eq_left hf, PolynomialFunction.eval_ofPolynomial, hz, decodePoint]
  exact ((Classical.choose_spec (polynomial_of_affine_answer u v _ f rfl hf)).2 t).symm.trans he

/-- Read a legal full-line answer in the sole coordinate. -/
noncomputable def decodePolynomial (d : ℕ) (a : Answer F 1) : PolynomialFunction F d :=
  decodeAffinePolynomial d 0 (Pi.single 0 1) a

theorem decodePolynomial_agrees {d : ℕ} {u : Point F 1} {a b : Answer F 1}
    (h : accepts d (.axis univ) (.point u) a b) :
    (decodePolynomial d a).eval u = decodePoint b := by
  apply decodeAffinePolynomial_agrees 0 (Pi.single 0 1) (u 0) u _ rfl
  simpa only [linePoints_single_eq_univ, zero_add_smul_single] using h

end Cslib.PCP.LowIndividualDegree
