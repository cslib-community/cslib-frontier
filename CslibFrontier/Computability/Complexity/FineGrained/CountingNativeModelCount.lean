/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingNativeEndpoint
public import CslibFrontier.Computability.Complexity.Problems.SAT.Declared
import CslibFrontier.Computability.Complexity.FineGrained.CountingScaleBounds
import CslibFrontier.Foundations.Data.Nat.Power
import CslibFrontier.Logics.Propositional.CNF.ModelCount.DenseRelabel
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.OCombinators

/-!
# Subexponential model counting for bounded-width CNF formulas

For every fixed clause width `k`, one native machine computes the number of satisfying
assignments `CNF.modelCount φ` of every formula `φ` with clauses of at most `k` literals. It
runs in time `2 ^ (A * interpolationScale n)` times a polynomial in the encoding length, where
`n = φ.numVars`, and in space polynomial in the encoding length.

This restates `CountingNativeEndpoint.exists_declaredCounter` on the plain formula: the machine
relabels the variables densely, declares their number, and runs the declared counter. The
resource bounds are folded into `ComputableInO`.

More generally:
* `CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared` composes
  `CountingNativeEndpoint.exists_declaredCounter` with any polynomial-time reduction
  `g : α → ℕ × CNF ℕ` and polynomial-time validity guard `valid : α → Bool`.
* `CountingNativeEndpoint.exists_shiftedCounter_of_polyTime_toCNF` composes
  `CountingNativeEndpoint.exists_modelCounter` with any polynomial-time CNF compilation
  `φ : α → CNF ℕ`, unary binary-power shift `shift : α → ℕ`, validity guard `valid : α → Bool`,
  and linear variable-count bound `(φ x).numVars ≤ C * μ x + D`, multiplying `(φ x).modelCount`
  by `2 ^ shift x` in binary while rescaling the subexponential rate to `μ x`.

## Main results

* `CountingNativeEndpoint.exists_counter_of_polyTime_toDeclared`: compose the declared `k`-CNF
  counter with any polynomial-time reduction and validity guard.
* `CountingNativeEndpoint.exists_modelCounter`: the bounded-width model counter.
* `CountingNativeEndpoint.exists_shiftedCounter_of_polyTime_toCNF`: compose the bounded-width
  model counter with a `2 ^ shift` factor and a linear `numVars ≤ C * μ + D` rescaling.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Proposition 6.4.
-/

namespace Cslib.Complexity.CountingNativeEndpoint

open Cslib.Logic.PL Turing.MultiTapeTM SubexponentialSAT

/-- General composition of `CountingNativeEndpoint.exists_declaredCounter` with any polynomial-time
reduction `g : α → ℕ × CNF ℕ` and polynomial-time validity guard `valid : α → Bool`. -/
public theorem exists_counter_of_polyTime_toDeclared {α : Type} {encA : α ↪ List Bool} (k : ℕ)
    {g : α → DeclaredCNF} (hg : ComputableInPolyTime g encA encDeclaredCNF)
    {valid : α → Bool} (hvalid : ComputableInPolyTime valid encA encBool)
    (hvalid_imp : ∀ x, valid x = true →
      CNF.validDeclaredInput k (g x).numVars (g x).formula = true) :
    ∃ (count : α → ℕ) (T S : α → ℕ) (A c e a b : ℕ),
      ComputableInO count encA encNat T S ∧
      (∀ x, count x =
        if valid x then (g x).formula.modelCountOn (Finset.range (g x).numVars) else 0) ∧
      (∀ x, (T x : ℝ) ≤ c * ((2 : ℝ) ^ ((A : ℝ) * interpolationScale (g x).numVars) *
        (((encA x).length : ℝ) + 1) ^ e) + c) ∧
      (∀ x, S x ≤ a * ((encA x).length + 1) ^ b) := by
  let g' (x : α) : ℕ × CNF ℕ := ((g x).numVars, (g x).formula)
  have hg' : ComputableInPolyTime g' encA (encPair encUnary encCNF) :=
    (encDeclaredCNF_numVars_polyTime hg).prod (encDeclaredCNF_formula_polyTime hg)
  obtain ⟨count₀, T₀, S₀, A, c₀, e₀, a₀, b₀, hcount₀, hspec₀, hT₀, hS₀⟩ :=
    exists_declaredCounter k
  obtain ⟨dg, _, hdg⟩ := hg'.exists_degree
  obtain ⟨dv, _, hdv⟩ := hvalid.exists_degree
  obtain ⟨p, q, hp⟩ := hg'.polyBounded_length.exists_le
  have hcomp := hcount₀.comp hdg.inO
  have hite := hdv.inO.ite hcomp (ComputableInO.const (encIn := encA) 0)
  let P (x : α) := ((encA x).length + 1) ^ dv + ((encA x).length + 1) ^ dg + (encA x).length
  let T (x : α) := P x + T₀ (g' x)
  let S (x : α) := P x + S₀ (g' x)
  -- Shared by the time and space bounds: the reduced instance has polynomial length, and the
  -- guard and reduction overhead `P x` is below `3 (|x| + 1) ^ E` for every `E > dv + dg`.
  have hpow : ∀ x k, ((encPair encUnary encCNF (g' x)).length + 1) ^ k ≤
      (p + 1) ^ k * ((encA x).length + 1) ^ (q * k) := fun x =>
    Nat.add_one_pow_le_of_le_mul_pow (Nat.succ_pos _) (hp x)
  have hP_le : ∀ x E, dv + dg + 1 ≤ E → P x ≤ 3 * ((encA x).length + 1) ^ E := by
    intro x E hE
    have hY1 : 1 ≤ (encA x).length + 1 := Nat.le_add_left 1 _
    have h1 := Nat.pow_le_pow_right hY1 (show dv ≤ E by omega)
    have h2 := Nat.pow_le_pow_right hY1 (show dg ≤ E by omega)
    have h3 := (Nat.le_succ (encA x).length).trans
      (Nat.le_self_pow (by omega : E ≠ 0) ((encA x).length + 1))
    dsimp only [P]
    omega
  refine ⟨fun x => if valid x then count₀ (g' x) else 0, T, S, A,
    3 + c₀ * (p + 1) ^ e₀, dv + dg + 1 + q * e₀,
    3 + a₀ * (p + 1) ^ b₀, dv + dg + 1 + q * b₀,
    (hite.mono 1 (fun x => ?_) (fun x => ?_)).of_enc_eq (fun _ => rfl),
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · dsimp only [T, P]
    split_ifs <;> omega
  · dsimp only [S, P]
    split_ifs <;> omega
  · by_cases hx : valid x = true
    · simp [hx, hspec₀ (g' x), hvalid_imp x hx, g']
    · simp [hx]
  · have hY1 : 1 ≤ (encA x).length + 1 := Nat.le_add_left 1 _
    have hX1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((A : ℝ) * interpolationScale (g x).numVars) :=
      Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg A) (interpolationScale_nonneg _))
    have hW : (((encPair encUnary encCNF (g' x)).length : ℝ) + 1) ^ e₀ ≤
        ((p : ℝ) + 1) ^ e₀ * (((encA x).length : ℝ) + 1) ^ (dv + dg + 1 + q * e₀) := by
      exact_mod_cast (hpow x e₀).trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (Nat.le_add_left _ _)))
    have hPR : (P x : ℝ) ≤ 3 * (((encA x).length : ℝ) + 1) ^ (dv + dg + 1 + q * e₀) := by
      exact_mod_cast hP_le x _ (Nat.le_add_right _ _)
    have hQ : (1 : ℝ) ≤ ((p : ℝ) + 1) ^ e₀ := one_le_pow₀ (by linarith [p.cast_nonneg (α := ℝ)])
    have hZ : (0 : ℝ) ≤ (((encA x).length : ℝ) + 1) ^ (dv + dg + 1 + q * e₀) := by positivity
    have hc₀ : (0 : ℝ) ≤ c₀ := Nat.cast_nonneg c₀
    have hT₀x := hT₀ (g' x)
    change ((P x + T₀ (g' x) : ℕ) : ℝ) ≤ _
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left hW (mul_nonneg hc₀ (zero_le_one.trans hX1)),
      mul_le_mul_of_nonneg_right hX1 hZ, mul_le_mul_of_nonneg_left hQ hc₀]
  · have hY1 : 1 ≤ (encA x).length + 1 := Nat.le_add_left 1 _
    have hS₀x := (hS₀ (g' x)).trans (Nat.mul_le_mul_left a₀ ((hpow x b₀).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (Nat.le_add_left _ (dv + dg + 1))))))
    have hP_B := hP_le x (dv + dg + 1 + q * b₀) (Nat.le_add_right _ _)
    change P x + S₀ (g' x) ≤
      (3 + a₀ * (p + 1) ^ b₀) * ((encA x).length + 1) ^ (dv + dg + 1 + q * b₀)
    rw [Nat.add_mul, Nat.mul_assoc]
    omega

/-- Dense relabeling followed by declaring the number of variables. -/
private theorem computableInPolyTime_declareDense :
    ComputableInPolyTime (fun φ : CNF ℕ => (φ.denseRelabel.numVars, φ.denseRelabel)) encCNF
      (encPair encUnary encCNF) := by
  exact (by fun_prop : ComputableInPolyTime (fun ψ : CNF ℕ => (ψ.numVars, ψ)) encCNF
    (encPair encUnary encCNF)).comp SAT.computableInPolyTime_denseRelabel

/-- **Subexponential bounded-width model counting.** For each width `k`, one machine computes
`φ.modelCount` on every formula `φ` whose clauses have at most `k` literals, in time
`2 ^ (A * interpolationScale φ.numVars)` times a polynomial in the encoding length, and in
polynomial space. -/
public theorem exists_modelCounter (k : ℕ) :
    ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
      (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
      ComputableInO count encCNF encNat
        (fun φ => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ *
          ((encCNF φ).length + 1) ^ e)
        (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨count, T, S, A, c, e, a, b, hcount, hspec, hT, hS⟩ := exists_declaredCounter k
  set g : CNF ℕ → ℕ × CNF ℕ := fun φ => (φ.denseRelabel.numVars, φ.denseRelabel)
  obtain ⟨d, _, hd⟩ := computableInPolyTime_declareDense.exists_degree
  obtain ⟨p, q, hp⟩ := computableInPolyTime_declareDense.polyBounded_length.exists_le
  refine ⟨fun φ => count (g φ), A, q * e + d, q * b + d, fun φ hφ => ?_,
    (hcount.comp hd.inO).mono
      (c * (p + 1) ^ e + 1 + c + a * (p + 1) ^ b + 1) (fun φ => ?_) (fun φ => ?_)⟩
  · have hw : ∀ cl ∈ φ.denseRelabel, cl.length ≤ k :=
      (CNF.all_length_le_denseRelabel φ).mpr hφ
    have hv : CNF.validDeclaredInput k φ.denseRelabel.numVars φ.denseRelabel = true :=
      CNF.validDeclaredInput_eq_true_iff.mpr
        ⟨hw, by rw [CNF.vars_denseRelabel_toFinset, CNF.numVars_denseRelabel]⟩
    dsimp only [g]
    rw [hspec, ite_eq_left hv, CNF.numVars_denseRelabel, CNF.modelCountOn_denseRelabel]
  all_goals
    set Y := (encCNF φ).length + 1 with hY
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hpow := Nat.add_one_pow_le_of_le_mul_pow hY1 (hp φ)
  · -- time
    set X : ℝ := (2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars) with hX
    set N := ⌈X⌉₊
    have hXN : X ≤ N := Nat.le_ceil X
    have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hTg : T (g φ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c := by
      have h : (T (g φ) : ℝ) ≤
          c * (X * (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e) + c := by
        simpa only [g, CNF.numVars_denseRelabel, X] using hT (g φ)
      have hpowR : (((encPair encUnary encCNF (g φ)).length : ℝ) + 1) ^ e ≤
          (p + 1) ^ e * Y ^ (q * e) := by exact_mod_cast hpow e
      have hmul := mul_le_mul_of_nonneg_left
        (mul_le_mul hXN hpowR (by positivity) (by positivity)) (Nat.cast_nonneg c)
      exact_mod_cast (by linarith : (T (g φ) : ℝ) ≤ c * (p + 1) ^ e * (N * Y ^ (q * e)) + c)
    have hqe : Y ^ (q * e) ≤ Y ^ (q * e + d) := Nat.pow_le_pow_right hY1 (by omega)
    have hd' : Y ^ d ≤ N * Y ^ (q * e + d) :=
      (Nat.pow_le_pow_right hY1 (by omega)).trans (Nat.le_mul_of_pos_left _ hN1)
    have hmul := Nat.mul_le_mul_left (c * (p + 1) ^ e) (Nat.mul_le_mul_left N hqe)
    change Y ^ d + T (g φ) ≤ _ * (N * Y ^ (q * e + d) + 1)
    generalize N * Y ^ (q * e + d) = Z at hd' hmul ⊢
    generalize c * (p + 1) ^ e = u at hTg hmul ⊢
    generalize a * (p + 1) ^ b = v
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]
  · -- space
    have hSg : S (g φ) ≤ a * (p + 1) ^ b * Y ^ (q * b + d) :=
      (hS (g φ)).trans (by
        rw [mul_assoc]
        exact Nat.mul_le_mul_left a ((hpow b).trans (Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right hY1 (by omega)))))
    have hd' : Y ^ d ≤ Y ^ (q * b + d) := Nat.pow_le_pow_right hY1 (by omega)
    change Y ^ d + S (g φ) ≤ _ * (Y ^ (q * b + d) + 1)
    generalize Y ^ (q * b + d) = Z at hSg hd' ⊢
    generalize a * (p + 1) ^ b = v at hSg ⊢
    generalize c * (p + 1) ^ e = u
    nlinarith [Nat.zero_le (c * Z), Nat.zero_le (v * Z), Nat.zero_le (u * Z)]

/-- Compose `CountingNativeEndpoint.exists_modelCounter` with a polynomial-time CNF compilation
`φ : α → CNF ℕ`, a polynomial-time unary binary-exponent shift `shift : α → ℕ`, a polynomial-time
validity guard `valid : α → Bool`, and a linear variable-count bound `(φ x).numVars ≤ C * μ x + D`
under `valid x = true`, multiplying `(φ x).modelCount` in binary by `2 ^ shift x` while rescaling
the `interpolationScale` exponent to `μ x`. -/
public theorem exists_shiftedCounter_of_polyTime_toCNF {α : Type} {encA : α ↪ List Bool} (k : ℕ)
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ encA encCNF)
    {shift : α → ℕ} (hshift : ComputableInPolyTime shift encA encUnary)
    {valid : α → Bool} (hvalid : ComputableInPolyTime valid encA encBool)
    (μ : α → ℕ) (C D : ℕ)
    (hvalid_imp : ∀ x, valid x = true →
      (∀ cl ∈ φ x, cl.length ≤ k) ∧ (φ x).numVars ≤ C * μ x + D) :
    ∃ (count : α → ℕ) (A e b : ℕ),
      (∀ x, count x = if valid x then 2 ^ shift x * (φ x).modelCount else 0) ∧
      ComputableInO count encA encNat
        (fun x => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale (μ x))⌉₊ *
          ((encA x).length + 1) ^ e)
        (fun x => ((encA x).length + 1) ^ b) := by
  open ComputableInPolyTime in
  set fCNF : α → CNF ℕ := fun x => if valid x then φ x else []
  have hfCNF_poly : ComputableInPolyTime fCNF encA encCNF :=
    hvalid.ite hφ (const [])
  set fPow : α → ℕ := fun x => if valid x then 2 ^ shift x else 0
  have hfPow_poly : ComputableInPolyTime fPow encA encNat :=
    hvalid.ite (binary_two_pow.comp hshift) (const 0)
  obtain ⟨d₁, _, hfCNF_deg⟩ := hfCNF_poly.exists_degree
  obtain ⟨p, q, hfCNF_len⟩ := hfCNF_poly.polyBounded_length.exists_le
  obtain ⟨d₂, _, hfPow_deg⟩ := hfPow_poly.exists_degree
  obtain ⟨d₃, _, hmul_deg⟩ := (binary_mul' (fst encNat encNat) (snd encNat encNat)).exists_degree
  obtain ⟨countCNF, A₀, e₀, b₀, hcountCNF_spec, hcountCNF_inO⟩ := exists_modelCounter k
  have hsub := hcountCNF_inO.comp hfCNF_deg.inO
  have hpair := hfPow_deg.inO.prod hsub
  obtain ⟨c_pair, hpair_len⟩ := hpair.length_le
  have htot := hmul_deg.inO.comp hpair
  obtain ⟨K, _, hK_bound⟩ := ceil_two_pow_interpolationScale_le_of_linear A₀ C D
  let A : ℕ := A₀ * 8 ^ (2 * C)
  let B₁ : ℕ := d₁ + d₂ + q * b₀
  let M : ℕ := c_pair * (3 + (p + 1) ^ b₀) + 1
  let e : ℕ := B₁ + q * e₀ + B₁ * d₃
  let b : ℕ := B₁ + B₁ * d₃
  let C_bound : ℕ := 2 + K * (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1
  refine ⟨fun x => fPow x * countCNF (fCNF x), A, e, b, fun x => ?_,
    htot.mono C_bound (fun x => ?_) (fun x => ?_)⟩
  · by_cases hvx : valid x = true
    · simp [fPow, fCNF, hvx, hcountCNF_spec (φ x) (hvalid_imp x hvx).1]
    · simp [fPow, fCNF, hvx]
  all_goals
    set Y : ℕ := (encA x).length + 1
    have hY1 : 1 ≤ Y := Nat.le_add_left 1 _
    have hφ_pow := Nat.add_one_pow_le_of_le_mul_pow hY1 (hfCNF_len x)
    have hSpair_le : Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) ≤
        (2 + (p + 1) ^ b₀) * Y ^ B₁ := by
      have hd₂ : Y ^ d₂ ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by dsimp only [B₁]; omega)
      have hd₁ : Y ^ d₁ ≤ Y ^ B₁ := Nat.pow_le_pow_right hY1 (by dsimp only [B₁]; omega)
      have h3 := (hφ_pow b₀).trans (Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right hY1 (show q * b₀ ≤ B₁ by dsimp only [B₁]; omega)))
      nlinarith
    have hpair_d₃ : ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃ ≤
        M ^ d₃ * Y ^ (B₁ * d₃) := by
      have h1 := (hpair_len x).trans
        (Nat.mul_le_mul_left c_pair (Nat.add_le_add hSpair_le (Nat.one_le_pow B₁ Y hY1)))
      dsimp only [Function.comp_apply] at h1
      refine Nat.pow_le_pow_mul_pow_of_le_mul_pow ?_ d₃
      dsimp only [M]
      nlinarith [Nat.one_le_pow B₁ Y hY1]
  · set N : ℕ := ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale (μ x))⌉₊
    have hN1 : 1 ≤ N := Nat.one_le_ceil_iff.mpr (Real.rpow_pos_of_pos (by norm_num) _)
    have hnum_le : (fCNF x).numVars ≤ C * μ x + D := by
      by_cases hvx : valid x = true
      · simpa only [fCNF, hvx, ↓reduceIte] using (hvalid_imp x hvx).2
      · simp [fCNF, hvx, CNF.numVars, CNF.vars]
    have hle (k : ℕ) (hk : k ≤ e) : Y ^ k ≤ N * Y ^ e :=
      (Nat.pow_le_pow_right hY1 hk).trans (Nat.le_mul_of_pos_left _ hN1)
    have hsub_T := Nat.mul_le_mul (hK_bound hnum_le) ((hφ_pow e₀).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (show q * e₀ ≤ e by dsimp only [e]; omega))))
    have hd₃ := hpair_d₃.trans (Nat.mul_le_mul_left _ (hle _ (by dsimp only [e]; omega)))
    change Y ^ d₂ + (Y ^ d₁ + ⌈(2 : ℝ) ^ ((A₀ : ℝ) * interpolationScale (fCNF x).numVars)⌉₊ *
      ((encCNF (fCNF x)).length + 1) ^ e₀) +
      ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃ ≤
      C_bound * (N * Y ^ e + 1)
    dsimp only [C_bound]
    calc _ ≤ N * Y ^ e + (N * Y ^ e + K * N * ((p + 1) ^ e₀ * Y ^ e)) + M ^ d₃ * (N * Y ^ e) :=
          Nat.add_le_add (Nat.add_le_add (hle d₂ (by dsimp only [e, B₁]; omega))
            (Nat.add_le_add (hle d₁ (by dsimp only [e, B₁]; omega)) hsub_T)) hd₃
      _ = (2 + K * (p + 1) ^ e₀ + M ^ d₃) * (N * Y ^ e) := by ring
      _ ≤ _ := Nat.mul_le_mul (by omega) (Nat.le_succ _)
  · have hB₁_b : Y ^ B₁ ≤ Y ^ b := Nat.pow_le_pow_right hY1 (by dsimp only [b]; omega)
    have hBd₃_b : Y ^ (B₁ * d₃) ≤ Y ^ b := Nat.pow_le_pow_right hY1 (by dsimp only [b]; omega)
    have hs1 := hSpair_le.trans (Nat.mul_le_mul_left _ hB₁_b)
    have hs2 := hpair_d₃.trans (Nat.mul_le_mul_left _ hBd₃_b)
    change Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) +
      ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃ ≤
      C_bound * (Y ^ b + 1)
    dsimp only [C_bound]
    calc Y ^ d₂ + (Y ^ d₁ + ((encCNF (fCNF x)).length + 1) ^ b₀) +
          ((encPair encNat encNat (fPow x, countCNF (fCNF x))).length + 1) ^ d₃
        ≤ (2 + (p + 1) ^ b₀) * Y ^ b + M ^ d₃ * Y ^ b := Nat.add_le_add hs1 hs2
      _ = (2 + (p + 1) ^ b₀ + M ^ d₃) * Y ^ b := by ring
      _ ≤ (2 + K * (p + 1) ^ e₀ + (p + 1) ^ b₀ + M ^ d₃ + 1) * (Y ^ b + 1) :=
          Nat.mul_le_mul (by omega) (Nat.le_succ _)

end Cslib.Complexity.CountingNativeEndpoint
