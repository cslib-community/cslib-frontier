/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Basic
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Curvature
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Flag.Exchange
import CslibFrontier.Foundations.Geometry.CAT0.Toolkit
import CslibFrontier.Foundations.Data.Finset.DisjointCard

/-!
# Outside the contracting case, the square root of the rank is a price

Steps 1 to 7 of the proof of Theorem D.2 of [AnthropicVPVNP2026]. Every price on `Mat_μ(F₂)` is
pulled back from a CAT(0) space (Proposition C.3), so the squared diagonals of every quadrangle
`a, a + W, a + W + W', a + W'` add up to at most its squared sides (Lemma C.4(b)); averaged over
transversal pairs `(W, W')` this gives `D(i + j)² ≤ D(i)² + D(j)²` (Step 1). If the contracting
hypothesis fails, a compactness argument gives a price with `D(r)² = r` for all `r ≤ μ`
(Step 2), for which all these quadrangles have equality (Step 3). For `μ ≥ 3` the scalar products
`B_a` then vanish on transversal pairs (Steps 4–6), and the squared distances are the ranks of the
differences (Step 7, `TwoCases.exists_sq_eq_rank`).

## Main results

* `TwoCases.exists_sq_eq_rank`: outside the contracting case, for `μ ≥ 3` some price `w` on
  `Mat_μ(F₂)` has `w a a' ^ 2 = rk (a - a')`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Theorem D.2, Steps 1 to 7 of its proof, pp. 30–31; module `Paper.Alternative`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.TwoCases

open Finset Filter Topology Matrix Cslib.PartyTensor Cslib.CAT0
open Cslib.Circuits.Arithmetic.Separation.Flag

variable {K : Type} [Field K] {μ : ℕ} {w : Mt μ → Mt μ → ℝ}

/-! ### Step 1: subadditivity -/

/-- Lemma C.4(b) in a price, which is pulled back from a CAT(0) space by Proposition C.3. -/
private theorem quadrangle (hw : IsPrice K w) (x v y u : Mt μ) :
    w x v ^ 2 + w y u ^ 2 ≤ w x y ^ 2 + w y v ^ 2 + w v u ^ 2 + w x u ^ 2 ∧
      (w x v ^ 2 + w y u ^ 2 = w x y ^ 2 + w y v ^ 2 + w v u ^ 2 + w x u ^ 2 →
        w x y = w v u ∧ w y v = w x u) := by
  obtain ⟨Y, _, _, f, -, hf⟩ := Curvature.exists_completeCAT0Space_of_isPrice hw
  simp only [← hf]
  exact ⟨dist_sq_add_dist_sq_le_sides _ _ _ _, sides_eq_of_dist_sq_add_dist_sq_eq⟩

private theorem defect_nonneg (hw : IsPrice K w) (a W W' : Mt μ) : 0 ≤ defect w a W W' := by
  have := (quadrangle hw a (a + W + W') (a + W) (a + W')).1
  unfold defect
  linarith

/-- The number of the triples `(p, q, a)`. -/
private noncomputable abbrev frames (μ : ℕ) : ℝ :=
  (Fintype.card (GLM (Fin μ)) : ℝ) ^ 2 * Fintype.card (Mt μ)

private theorem frames_pos : 0 < frames μ := by
  unfold frames
  have : (0 : ℝ) < Fintype.card (GLM (Fin μ)) := by exact_mod_cast Fintype.card_pos
  positivity

/-- The squared sides minus the squared diagonals of the quadrangles with sides `p · dg S · q`
and `p · dg T · q`, added over all `p`, `q` and `a`, are `2 (D(|S|)² + D(|T|)² − D(|S| + |T|)²)`
times their number. -/
private theorem sum_defect_eq (hw : IsPrice K w) {S T : Finset (Fin μ)} (h : Disjoint S T) :
    ∑ p : GLM (Fin μ), ∑ q : GLM (Fin μ), ∑ a, defect w a (X p q S) (X p q T) =
      2 * frames μ * (meanSq w S.card + meanSq w T.card - meanSq w (S.card + T.card)) := by
  have hMD : ∀ S : Finset (Fin μ), MD w (dg S) = frames μ * meanSq w S.card := fun S => by
    have : (Fintype.card (Mt μ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [MD, DM_dg_eq, ← mul_sum, meanSq, frames]
    field_simp
  rw [sum_all_defect hw.symm h, hMD, hMD, hMD, card_union_of_disjoint h]
  ring

private theorem meanSq_add_le (hw : IsPrice K w) {i j : ℕ} (hij : i + j ≤ μ) :
    meanSq w (i + j) ≤ meanSq w i + meanSq w j := by
  obtain ⟨S, -, T, -, hST, rfl, rfl⟩ :=
    exists_disjoint_card_eq (s := (univ : Finset (Fin μ))) (by simpa using hij)
  have h := sum_defect_eq hw hST
  have h0 : 0 ≤ 2 * frames μ * (meanSq w S.card + meanSq w T.card -
      meanSq w (S.card + T.card)) :=
    h ▸ sum_nonneg fun _ _ => sum_nonneg fun _ _ => sum_nonneg fun _ _ => defect_nonneg hw _ _ _
  have := frames_pos (μ := μ)
  nlinarith

private theorem meanSq_zero (hw : IsPrice K w) : meanSq w 0 = 0 := by
  rw [meanSq, sum_eq_zero fun a _ => ?_, zero_div]
  rw [rankMean, sum_eq_zero fun W hW => ?_, zero_div]
  obtain ⟨p, q, S, rfl⟩ := exists_X W
  rw [mem_filter, rank_X, card_eq_zero] at hW
  simp [hW.2, X_empty, hw.self]

/-- `D(r)² ≤ r D(1)²`. -/
private theorem meanSq_le (hw : IsPrice K w) {r : ℕ} (hr : r ≤ μ) :
    meanSq w r ≤ r * meanSq w 1 := by
  induction r with
  | zero => simp [meanSq_zero hw]
  | succ r ih =>
    have := meanSq_add_le hw (i := r) (j := 1) hr
    push_cast
    linarith [ih (by omega)]

/-- Each squared distance is at most `|Mat_μ(F₂)|²` times the mean over its rank. -/
private theorem sq_le_meanSq (w : Mt μ → Mt μ → ℝ) (a W : Mt μ) :
    w a (a + W) ^ 2 ≤ (Fintype.card (Mt μ) : ℝ) ^ 2 * meanSq w W.rank := by
  have hc : (0 : ℝ) < Fintype.card (Mt μ) := by exact_mod_cast Fintype.card_pos
  have hn : (0 : ℝ) < #{V : Mt μ | V.rank = W.rank} := by exact_mod_cast card_pos.2 ⟨W, by simp⟩
  have h1 : w a (a + W) ^ 2 ≤ #{V : Mt μ | V.rank = W.rank} *
      rankMean (fun V => w a (a + V)) W.rank := by
    rw [rankMean, mul_div_cancel₀ _ hn.ne']
    exact single_le_sum (f := fun V => w a (a + V) ^ 2) (fun _ _ => sq_nonneg _) (by simp)
  have h2 : rankMean (fun V => w a (a + V)) W.rank ≤ Fintype.card (Mt μ) * meanSq w W.rank := by
    rw [meanSq, mul_div_cancel₀ _ hc.ne']
    exact single_le_sum (f := fun a => rankMean (fun V => w a (a + V)) W.rank)
      (fun _ _ => rankMean_nonneg _ _) (mem_univ a)
  have h3 : (#{V : Mt μ | V.rank = W.rank} : ℝ) ≤ Fintype.card (Mt μ) := by
    exact_mod_cast card_le_univ _
  exact h1.trans ((by gcongr; exact rankMean_nonneg _ _ : _ ≤
    (Fintype.card (Mt μ) : ℝ) * (Fintype.card (Mt μ) * meanSq w W.rank)).trans_eq (by ring))

/-! ### Step 2: a price with equality -/

private theorem meanSq_smul (w : Mt μ → Mt μ → ℝ) (c : ℝ) (r : ℕ) :
    meanSq (fun a b => c * w a b) r = c ^ 2 * meanSq w r := by
  simp only [meanSq, rankMean, mul_pow, ← mul_sum, mul_div_assoc]

private theorem continuous_meanSq (r : ℕ) : Continuous fun w : Mt μ → Mt μ → ℝ => meanSq w r := by
  unfold meanSq rankMean; fun_prop

/-- "As the contracting hypothesis fails, … by compactness, pass to a limit": a price with
`D(r)² = r` for all `r ≤ μ`. The prices with `D(1) = 1` are bounded (`sq_le_meanSq`), so they
form a compact set; if `D(μ)²` stayed below `μ` on it, `s = (max 1 (sup D(μ)²))^(1/2)` would
witness the contracting hypothesis. -/
private theorem exists_meanSq_eq (hK : ¬ ContractingCase K) (hμ : 2 ≤ μ) :
    ∃ w : Mt μ → Mt μ → ℝ, IsPrice K w ∧ ∀ r ≤ μ, meanSq w r = r := by
  by_contra hK'
  set C := √((Fintype.card (Mt μ) : ℝ) ^ 2 * μ)
  set S := {w : Mt μ → Mt μ → ℝ | IsPrice K w ∧ ∀ a b, w a b ≤ C} ∩ {w | meanSq w 1 = 1}
  have hS : IsCompact S := (isCompact_setOf_isPrice_le K fun _ _ => C).inter_right
    (isClosed_eq (continuous_meanSq 1) continuous_const)
  have scale (w : Mt μ → Mt μ → ℝ) (hw : IsPrice K w) (h1 : 0 < meanSq w 1) :
      (fun a b => (√(meanSq w 1))⁻¹ * w a b) ∈ S := by
    set w' := fun a b => (√(meanSq w 1))⁻¹ * w a b
    have hc : meanSq w' 1 = 1 := by
      rw [meanSq_smul, inv_pow, Real.sq_sqrt h1.le, inv_mul_cancel₀ h1.ne']
    have hw' : IsPrice K w' := hw.smul (inv_nonneg.2 (Real.sqrt_nonneg (meanSq w 1)))
    refine ⟨⟨hw', fun a b => Real.le_sqrt_of_sq_le ?_⟩, hc⟩
    have hr := (rank_le_card_width (a + b)).trans (Fintype.card_fin μ).le
    refine (add_cancel_left a b ▸ sq_le_meanSq w' a (a + b)).trans ?_
    gcongr; exact (meanSq_le hw' hr).trans (by rw [hc, mul_one]; exact_mod_cast hr)
  obtain ⟨M, hMμ, hM⟩ : ∃ M : ℝ, M < μ ∧ ∀ w ∈ S, meanSq w μ ≤ M := by
    rcases S.eq_empty_or_nonempty with h0 | hne
    · exact ⟨0, by positivity, by simp [h0]⟩
    obtain ⟨w, ⟨⟨hw, -⟩, hw1⟩, hmax⟩ := hS.exists_isMaxOn hne (continuous_meanSq μ).continuousOn
    refine ⟨meanSq w μ, lt_of_le_of_ne ((meanSq_le hw le_rfl).trans_eq (by rw [hw1, mul_one]))
      fun e => hK' ⟨w, hw, fun r hr => ?_⟩, hmax⟩
    have h1 := meanSq_le hw hr
    have h2 := meanSq_le hw (Nat.sub_le μ r)
    have h3 := meanSq_add_le hw (i := r) (j := μ - r) (by omega)
    rw [hw1, mul_one] at h1 h2
    rw [Nat.add_sub_cancel' hr, e] at h3
    push_cast [hr] at h2
    linarith
  refine hK ⟨μ, √(max 1 M), hμ, Real.one_le_sqrt.2 (le_max_left _ _), ?_, fun w hw => ?_⟩
  · rw [Real.sq_sqrt (le_max_of_le_left zero_le_one)]; exact max_lt (by exact_mod_cast hμ) hMμ
  rw [distAtRank, distAtRank, ← Real.sqrt_mul (le_max_of_le_left zero_le_one)]
  refine Real.sqrt_le_sqrt ?_
  rcases (meanSq_nonneg w 1).eq_or_lt with h0 | h1
  · have := meanSq_le hw le_rfl
    rw [← h0] at this ⊢
    linarith [meanSq_nonneg w μ]
  · have h := hM _ (scale w hw h1)
    rw [meanSq_smul, inv_pow, Real.sq_sqrt h1.le, inv_mul_le_iff₀ h1] at h
    exact h.trans ((mul_comm _ _).le.trans (mul_le_mul_of_nonneg_right (le_max_right 1 M) h1.le))

/-! ### Step 3: equality for all quadrangles -/

/-- A price with `D(r)² = r` for all `r ≤ μ`. -/
private structure Extremal (K : Type) [Field K] (w : Mt μ → Mt μ → ℝ) : Prop where
  price : IsPrice K w
  meanSq_eq : ∀ r ≤ μ, meanSq w r = r

private theorem transversal_X₂ {p q : GLM (Fin μ)} {S T : Finset (Fin μ)} (h : Disjoint S T) :
    Transversal ![X p q S, X p q T] :=
  (transversal_iff _).2 ⟨p, q, ![S, T], by simp [Fin.forall_fin_two, h, h.symm],
    Fin.forall_fin_two.2 ⟨rfl, rfl⟩⟩

private theorem transversal_symm {W W' : Mt μ} (h : Transversal ![W, W']) :
    Transversal ![W', W] :=
  transversal_two.2 ⟨(transversal_two.1 h).1.symm, (transversal_two.1 h).2.symm⟩

/-- "In this price the inequality of Step 1 … is an equality": opposite sides of the quadrangle
of a transversal pair are equal. -/
private theorem Extremal.sides (hx : Extremal K w) {W W' : Mt μ} (h : Transversal ![W, W'])
    (a : Mt μ) :
    w a (a + W) = w (a + W + W') (a + W') ∧ w (a + W) (a + W + W') = w a (a + W') ∧
      defect w a W W' = 0 := by
  obtain ⟨p, q, S, hd, hW⟩ := (transversal_iff _).1 h
  obtain rfl : W = X p q (S 0) := hW 0
  obtain rfl : W' = X p q (S 1) := hW 1
  have hST := hd 0 1 (by decide)
  have hc : (S 0).card + (S 1).card ≤ μ := by
    rw [← card_union_of_disjoint hST]; exact card_le_univ _ |>.trans (Fintype.card_fin μ).le
  have h1 := sum_defect_eq hx.price hST
  rw [hx.meanSq_eq _ hc, hx.meanSq_eq _ (by omega), hx.meanSq_eq _ (by omega)] at h1
  simp only [Nat.cast_add, sub_self, mul_zero, ← Fintype.sum_prod_type'] at h1
  have h0 := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg fun _ => defect_nonneg hx.price _ _ _).1
    h1) (p, q, a)
  refine ⟨(quadrangle hx.price _ _ _ _).2 ?_ |>.1, (quadrangle hx.price _ _ _ _).2 ?_ |>.2, h0⟩ <;>
  · simp only [defect, Pi.zero_apply] at h0
    linarith

/-- (D.1): `n_{a + W'}(W) = n_a(W)` for transversal `W`, `W'`. -/
private theorem Extremal.opposite (hx : Extremal K w) {W W' : Mt μ} (h : Transversal ![W, W'])
    (a : Mt μ) : nn w (a + W') W = nn w a W := by
  rw [nn, nn, (hx.sides h a).1, add_right_comm, hx.price.symm]

/-- (D.2): `|a + W, a + W'|² = 2 n_a(W) + 2 n_a(W') − n_a(W + W')` for transversal `W`, `W'`. -/
private theorem Extremal.diagonal (hx : Extremal K w) {W W' : Mt μ} (h : Transversal ![W, W'])
    (a : Mt μ) : w (a + W) (a + W') ^ 2 = 2 * nn w a W + 2 * nn w a W' - nn w a (W + W') := by
  obtain ⟨h1, h2, h3⟩ := hx.sides h a
  simp only [defect, nn, ← add_assoc] at h3 ⊢
  rw [← h1, h2] at h3
  linarith

/-! ### Step 4: additivity -/

/-- (D.3): `B_a(W₁, W₂ + W₃) = B_a(W₁, W₂) + B_a(W₁, W₃)` for transversal `W₁`, `W₂`, `W₃`, by
(D.2) at `a + W₂` for the pair `(W₁, W₂ + W₃)`. -/
private theorem Extremal.additive (hx : Extremal K w) {W₁ W₂ W₃ : Mt μ}
    (h : Transversal ![W₁, W₂, W₃]) (a : Mt μ) :
    BB w a W₁ (W₂ + W₃) = BB w a W₁ W₂ + BB w a W₁ W₃ := by
  obtain ⟨p, q, S, hd, hW⟩ := (transversal_iff _).1 h
  obtain rfl : W₁ = X p q (S 0) := hW 0
  obtain rfl : W₂ = X p q (S 1) := hW 1
  obtain rfl : W₃ = X p q (S 2) := hW 2
  have e1 := hx.diagonal (transversal_X₂ (p := p) (q := q)
    (disjoint_union_right.2 ⟨hd 0 1 (by decide), hd 0 2 (by decide)⟩)) (a + X p q (S 1))
  have e2 := hx.diagonal (transversal_X₂ (p := p) (q := q)
    (disjoint_union_right.2 ⟨(hd 0 1 (by decide)).symm, hd 1 2 (by decide)⟩)) a
  have e3 := hx.diagonal (transversal_X₂ (p := p) (q := q)
    (disjoint_union_left.2 ⟨hd 0 2 (by decide), hd 1 2 (by decide)⟩)) a
  have e4 := hx.diagonal (transversal_X₂ (p := p) (q := q) (hd 1 2 (by decide))) a
  have e5 := hx.opposite (transversal_X₂ (p := p) (q := q) (hd 0 1 (by decide))) a
  rw [X_union p q (hd 1 2 (by decide))] at e1
  rw [X_union p q (hd 0 2 (by decide))] at e2
  rw [X_union p q (hd 0 1 (by decide))] at e3
  set A := X p q (S 0)
  set B := X p q (S 1)
  set C := X p q (S 2)
  rw [show a + B + A = a + (A + B) by abel,
    show nn w (a + B) (B + C) = w (a + B) (a + C) ^ 2 by rw [nn, add_assoc, add_cancel_left],
    show a + B + (B + C) = a + C by rw [add_assoc, add_cancel_left],
    show nn w (a + B) (A + (B + C)) = w (a + B) (a + (A + C)) ^ 2 by
      rw [nn, add_left_comm A, add_assoc, add_cancel_left],
    e2, e4, e5, e3] at e1
  unfold BB
  rw [show A + B + C = A + (B + C) by abel, show B + (A + C) = A + (B + C) by abel] at *
  linarith

/-! ### Step 5: `B_a` is constant on pairs of rank one -/

section Exchange

/-! The exchange is used for `Φ = B_a(W, ·)`, additive by Step 4, and for `W = 0` and
`Φ = n_a`; the paper's `χ(u, x)` is `Φ(u xᵀ)`. -/

variable {W : Mt μ} {Φ : Mt μ → ℝ}

/-- "`χ(u₁, x₁) − χ(u₁, x₁ + x₂) = χ(u₁ + u₂, x₂) − χ(u₂, x₂)`. The right-hand side does not
depend on `x₁`, and the left-hand side changes sign when `x₁` becomes `x₁ + x₂`, which leaves the
three matrices transversal, so both sides vanish." -/
private theorem exchange (hΦ : ∀ V₁ V₂, Transversal ![W, V₁, V₂] → Φ (V₁ + V₂) = Φ V₁ + Φ V₂)
    {u₁ u₂ x₁ x₂ : Fin μ → F2} (hu : Indep2 (colSpace W) u₁ u₂)
    (hx : Indep2 (rowSpace W) x₁ x₂) :
    Φ (vecMulVec u₁ (x₁ + x₂)) = Φ (vecMulVec u₁ x₁) ∧
      Φ (vecMulVec (u₁ + u₂) x₂) = Φ (vecMulVec u₂ x₂) := by
  have key : ∀ {x₁ : Fin μ → F2}, Indep2 (rowSpace W) x₁ x₂ →
      Φ (vecMulVec u₁ x₁) + Φ (vecMulVec u₂ x₂) =
        Φ (vecMulVec u₁ (x₁ + x₂)) + Φ (vecMulVec (u₁ + u₂) x₂) := fun hx => by
    rw [← hΦ _ _ (transversal_of_indep2 hu hx),
      ← hΦ _ _ (transversal_of_indep2 hu.add_right hx.add_left), vecMulVec_add, add_vecMulVec,
      add_assoc, ← add_assoc (vecMulVec u₁ x₂), madd_self, zero_add]
  have k2 := key hx.add_left
  rw [add_assoc, vadd_self, add_zero] at k2
  have k1 := key hx
  constructor <;> linarith

/-- "Thus `x` may be changed by any vector outside its span with the row space of `W`, and
likewise `u`", and "such moves connect all vectors outside" these spaces: `Φ` has one value on
the matrices of rank one transversal to `W`, if `rk W + 2 ≤ μ`. -/
private theorem connect_rank_one
    (hΦ : ∀ V₁ V₂, Transversal ![W, V₁, V₂] → Φ (V₁ + V₂) = Φ V₁ + Φ V₂)
    (hW : W.rank + 2 ≤ μ) {u x u' x' : Fin μ → F2} (hu : u ∉ colSpace W) (hx : x ∉ rowSpace W)
    (hu' : u' ∉ colSpace W) (hx' : x' ∉ rowSpace W) :
    Φ (vecMulVec u x) = Φ (vecMulVec u' x') := by
  rw [← finrank_colSpace] at hW
  have hW' : Module.finrank F2 (rowSpace W) + 2 ≤ μ := by rwa [finrank_rowSpace, ← finrank_colSpace]
  refine (connect hW' (g := fun x => Φ (vecMulVec u x))
      (fun x y h => (exchange hΦ (exists_indep2 hW hu).choose_spec h).1) hx hx').trans
    (connect hW (g := fun u => Φ (vecMulVec u x')) (fun u v h => ?_) hu hu')
  rw [add_comm]
  exact (exchange hΦ h.symm (exists_indep2 hW' hx').choose_spec.symm).2

end Exchange

/-- A matrix of rank one is `u xᵀ` with `u, x ≠ 0`. -/
private theorem exists_vec {V : Mt μ} (h : V.rank = 1) :
    ∃ u x : Fin μ → F2, u ≠ 0 ∧ x ≠ 0 ∧ V = vecMulVec u x := by
  obtain ⟨p, q, S, rfl⟩ := exists_X V
  obtain ⟨i, rfl⟩ := card_eq_one.1 ((rank_X p q S).symm.trans h)
  exact ⟨_, _, col_ne_zero p i, row_ne_zero q i, X_singleton p q i⟩

/-- `Φ` has one value on the matrices of rank one that are transversal to `W`. -/
private theorem connect_rank_one'
    {W : Mt μ} {Φ : Mt μ → ℝ} (hΦ : ∀ V₁ V₂, Transversal ![W, V₁, V₂] → Φ (V₁ + V₂) = Φ V₁ + Φ V₂)
    (hW : W.rank + 2 ≤ μ) {V V' : Mt μ} (hV : Transversal ![W, V]) (hV' : Transversal ![W, V'])
    (h1 : V.rank = 1) (h2 : V'.rank = 1) : Φ V = Φ V' := by
  obtain ⟨u, x, hu, hx, rfl⟩ := exists_vec h1
  obtain ⟨u', x', hu', hx', rfl⟩ := exists_vec h2
  exact connect_rank_one hΦ hW ((transversal_vec hu hx).1 hV).1 ((transversal_vec hu hx).1 hV).2
    ((transversal_vec hu' hx').1 hV').1 ((transversal_vec hu' hx').1 hV').2

/-- "… any two matrices of rank one are both transversal to a third", as `μ ≥ 3`. -/
private theorem exists_transversal (hμ : 3 ≤ μ) {V W : Mt μ} (hV : V.rank = 1)
    (hW : W.rank = 1) : ∃ Z : Mt μ, Z.rank = 1 ∧ Transversal ![V, Z] ∧ Transversal ![W, Z] := by
  have hc := Submodule.finrank_add_le_finrank_add_finrank (colSpace V) (colSpace W)
  have hr := Submodule.finrank_add_le_finrank_add_finrank (rowSpace V) (rowSpace W)
  rw [finrank_colSpace, finrank_colSpace] at hc; rw [finrank_rowSpace, finrank_rowSpace] at hr
  obtain ⟨u, hu⟩ := exists_notMem (A := colSpace V ⊔ colSpace W) (by omega)
  obtain ⟨x, hx⟩ := exists_notMem (A := rowSpace V ⊔ rowSpace W) (by omega)
  have hu0 : u ≠ 0 := fun e => hu (e ▸ zero_mem _)
  have hx0 : x ≠ 0 := fun e => hx (e ▸ zero_mem _)
  exact ⟨vecMulVec u x, rank_vec hu0 hx0,
    (transversal_vec hu0 hx0).2 ⟨mt Submodule.mem_sup_left hu, mt Submodule.mem_sup_left hx⟩,
    (transversal_vec hu0 hx0).2 ⟨mt Submodule.mem_sup_right hu, mt Submodule.mem_sup_right hx⟩⟩

/-- "As `B_a` is symmetric, it takes one value `λ(a)` on all transversal pairs of matrices of
rank one." -/
private theorem Extremal.lambda (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {V V' W W' : Mt μ}
    (hV : Transversal ![V, V']) (hW : Transversal ![W, W']) (h1 : V.rank = 1) (h2 : V'.rank = 1)
    (h3 : W.rank = 1) (h4 : W'.rank = 1) : BB w a V V' = BB w a W W' := by
  have con {Z U U' : Mt μ} (hZ : Z.rank = 1) (hU : U.rank = 1) (hU' : U'.rank = 1)
      (t : Transversal ![Z, U]) (t' : Transversal ![Z, U']) : BB w a Z U = BB w a Z U' :=
    connect_rank_one' (Φ := BB w a _) (fun _ _ h => hx.additive h a) (by omega) t t' hU hU'
  obtain ⟨Z, hZ, t1, t2⟩ := exists_transversal hμ h1 h3
  rw [con h1 h2 hZ hV t1, BB_comm, con hZ h1 h3 (transversal_symm t1) (transversal_symm t2),
    BB_comm, con h3 hZ h4 t2 hW]

/-! ### Step 6: `λ = 0` -/

/-- "`B_{a+V}(V, W') = −B_a(V, W')`" for transversal `V`, `W'`. -/
private theorem Extremal.reflect (hx : Extremal K w) {V W' : Mt μ} (h : Transversal ![V, W'])
    (a : Mt μ) : BB w (a + V) V W' = - BB w a V W' := by
  unfold BB
  rw [show nn w (a + V) (V + W') = w (a + V) (a + W') ^ 2 by rw [nn, add_assoc, add_cancel_left],
    show nn w (a + V) V = nn w a V by rw [nn, nn, add_assoc, madd_self, add_zero, hx.price.symm],
    hx.diagonal h a, hx.opposite (transversal_symm h) a]
  ring

/-- "Hence `λ = 0`": `B_a` vanishes on transversal pairs of rank one. -/
private theorem Extremal.BB_eq_zero (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {W W' : Mt μ}
    (h : Transversal ![W, W']) (h1 : W.rank = 1) (h2 : W'.rank = 1) : BB w a W W' = 0 := by
  let e (l : Fin μ) : Mt μ := X 1 1 {l}
  have r1 (l : Fin μ) : (e l).rank = 1 := by simp [e, rank_X]
  have tr {l l' : Fin μ} (h : l ≠ l') : Transversal ![e l, e l'] :=
    transversal_X₂ (disjoint_singleton.2 h)
  set i : Fin μ := ⟨0, by omega⟩
  set j : Fin μ := ⟨1, by omega⟩
  set k : Fin μ := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
  have hik : i ≠ k := by simp [i, k, Fin.ext_iff]
  have hjk : j ≠ k := by simp [j, k, Fin.ext_iff]
  have lam (b : Mt μ) {l l' : Fin μ} (h : l ≠ l') : BB w b (e l) (e l') = BB w b (e i) (e j) :=
    hx.lambda hμ b (tr h) (tr hij) (r1 _) (r1 _) (r1 _) (r1 _)
  have two (b : Mt μ) : BB w b (e i + e j) (e k) = 2 * BB w b (e i) (e j) := by
    rw [BB_comm, hx.additive ((transversal_iff _).2 ⟨1, 1, ![{k}, {i}, {j}], by
      simp [Fin.forall_fin_succ, hik.symm, hjk.symm, hij, hik, hjk, Ne.symm],
      by simp [Fin.forall_fin_succ, e]⟩), lam b hik.symm, lam b hjk.symm]; ring
  have s3 := hx.reflect (V := e i + e j) (W' := e k)
    (by rw [← X_union _ _ (disjoint_singleton.2 hij)]
        exact transversal_X₂ (by simp [hik.symm, hjk.symm])) a
  rw [two, two, ← add_assoc, ← lam _ hij.symm, hx.reflect (tr hij.symm), lam _ hij.symm,
    hx.reflect (tr hij)] at s3
  rw [hx.lambda hμ a h (tr hij) h1 h2 (r1 _) (r1 _)]; linarith

/-! ### Step 7: the squared distance is the rank -/

/-- By Step 6 and (D.3), `n_a` is additive on `p · dg S · q = ∑_{i ∈ S} p · dg{i} · q`. -/
private theorem Extremal.nn_X (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) (p q : GLM (Fin μ))
    (S : Finset (Fin μ)) : nn w a (X p q S) = ∑ i ∈ S, nn w a (X p q {i}) := by
  induction S using Finset.induction_on with
  | empty => simp [nn, X_empty, hx.price.self]
  | insert i S hi ih =>
    have hB (T : Finset (Fin μ)) : i ∉ T → BB w a (X p q {i}) (X p q T) = 0 := by
      induction T using Finset.induction_on with
      | empty => simp [BB, nn, X_empty, hx.price.self]
      | insert j T hj ihT =>
        intro hiT; rw [mem_insert, not_or] at hiT
        rw [insert_eq, X_union p q (disjoint_singleton_left.2 hj),
          hx.additive ((transversal_iff _).2 ⟨p, q, ![{i}, {j}, T], by
            simp [Fin.forall_fin_succ, hiT.1, Ne.symm hiT.1, hiT.2, hj],
            by simp [Fin.forall_fin_succ]⟩), ihT hiT.2,
          hx.BB_eq_zero hμ a (transversal_X₂ (disjoint_singleton.2 hiT.1)) (by simp [rank_X])
            (by simp [rank_X]), add_zero]
    have h1 := hB S hi; unfold BB at h1
    rw [sum_insert hi, insert_eq, X_union p q (disjoint_singleton_left.2 hi), ← ih]; linarith

/-- "`n_a` has one value on all matrices of rank one", by the exchange with `W = 0`. -/
private theorem Extremal.nn_eq (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {V V' : Mt μ}
    (h1 : V.rank = 1) (h2 : V'.rank = 1) : nn w a V = nn w a V' := by
  refine connect_rank_one' (W := 0) (fun V₁ V₂ h => ?_) (by rw [rank_zero]; omega)
    (transversal_zero V) (transversal_zero V') h1 h2
  obtain ⟨p, q, S, hd, hW⟩ := (transversal_iff _).1 h.tail
  obtain rfl : V₁ = X p q (S 0) := hW 0
  obtain rfl : V₂ = X p q (S 1) := hW 1
  rw [← X_union p q (hd 0 1 (by decide)), hx.nn_X hμ, hx.nn_X hμ, hx.nn_X hμ,
    sum_union (hd 0 1 (by decide))]

/-- "By (D.1) this value does not depend on `a`, so it equals `D(1)² = 1`." -/
private theorem Extremal.nn_eq_one (hx : Extremal K w) (hμ : 3 ≤ μ) (a : Mt μ) {V : Mt μ}
    (hV : V.rank = 1) : nn w a V = 1 := by
  have shift (b Z : Mt μ) (hZ : Z.rank = 1) : nn w (b + Z) V = nn w b V := by
    obtain ⟨Z', hZ', t, -⟩ := exists_transversal hμ hZ hZ
    rw [hx.nn_eq hμ _ hV hZ', hx.nn_eq hμ _ hV hZ', hx.opposite (transversal_symm t)]
  have all (b : Mt μ) : nn w b V = nn w a V := by
    obtain ⟨p, q, S, hS⟩ := exists_X (a + b)
    rw [← add_cancel_left a b, hS]; clear hS
    induction S using Finset.induction_on with
    | empty => rw [X_empty, add_zero]
    | insert j S hj ih =>
      rw [insert_eq, union_comm, X_union p q (disjoint_singleton_right.2 hj), ← add_assoc,
        shift _ _ (by simp [rank_X]), ih]
  have h1 := hx.meanSq_eq 1 (by omega)
  have hc : (Fintype.card (Mt μ) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hn : (#{W : Mt μ | W.rank = 1} : ℝ) ≠ 0 :=
    by exact_mod_cast (card_pos.2 ⟨V, by simp [hV]⟩).ne'
  have h2 (b : Mt μ) : rankMean (fun W => w b (b + W)) 1 = nn w a V := by
    rw [rankMean, div_eq_iff hn, sum_congr rfl fun W hW =>
      show w b (b + W) ^ 2 = _ from (hx.nn_eq hμ b (mem_filter.1 hW).2 hV).trans (all b),
      sum_const, nsmul_eq_mul, mul_comm]
  simpa only [meanSq, h2, sum_const, card_univ, nsmul_eq_mul, mul_div_cancel_left₀ _ hc,
    Nat.cast_one] using h1

/-- **Steps 1 to 7 of the proof of Theorem D.2** (pp. 30–31): if the contracting hypothesis fails,
then for `μ ≥ 3` some price on `Mat_μ(F₂)` is the square root of the rank of the difference. -/
theorem exists_sq_eq_rank (hK : ¬ ContractingCase K) (hμ : 3 ≤ μ) :
    ∃ w : Mt μ → Mt μ → ℝ, IsPrice K w ∧ ∀ a a', w a a' ^ 2 = (a - a').rank := by
  obtain ⟨w, hw, hr⟩ := exists_meanSq_eq hK (by omega : 2 ≤ μ)
  have hx : Extremal K w := ⟨hw, hr⟩
  refine ⟨w, hw, fun a a' => ?_⟩
  obtain ⟨p, q, S, hS⟩ := exists_X (a + a')
  rw [show a - a' = a + a' by ext; exact CharTwo.sub_eq_add _ _, hS, rank_X,
    ← add_cancel_left a a', hS, ← nn, hx.nn_X hμ,
    sum_congr rfl fun i _ => hx.nn_eq_one hμ a (by simp [rank_X])]
  simp

end Cslib.Circuits.Arithmetic.Separation.TwoCases
