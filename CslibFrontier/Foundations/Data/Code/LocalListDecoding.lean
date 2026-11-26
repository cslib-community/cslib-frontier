/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.HintDecoding
public import CslibFrontier.Foundations.Data.Code.LocalDecoding
import CslibFrontier.Foundations.Data.Finset.Markov
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Local list decoding of Reed–Muller codes along lines with advice

Let `p` be a polynomial of total degree at most `d` in `m` variables over a field `F` with `q`
elements, and let `g` agree with `p` on a set `A` of `a` points, a small fraction of the
`Q = q ^ m` points. Local list decoding [SudanTrevisanVadhan2001] recovers `p(x)` at most points
`x` by decoding `g` along the line through `x` and a fixed point `z`, using the advice `p(z)` to
single out `p` among the polynomials that agree with `g` on the line.

The decoder `Cslib.Code.lineListDecode g d D z a x` parametrizes the line by
`t ↦ x + t • v`, where `v` is `z - x` scaled so that its first nonzero entry is `1`
(`Cslib.LinearAlgebra.firstNonzero`); then `z = x + c • v` for `c` the first nonzero entry of
`z - x`. It runs Sudan decoding with the hint `a` at `c` on the restriction of `g` to the line
(`Cslib.Code.hintDecode`). The direction `v` and the received word depend only on `x` and the line,
not on the position of `z` on it, so the hint position `c` is uniformly distributed over `F ∖ {0}`
given the line.

Two things can go wrong for a pair `(x, z)`: the line can have at most `D` agreements, or the hint
position can be one of the at most `D - d` bad positions of `Cslib.Code.card_hintDecode_ne_le`.
Points of a random line are pairwise independent and uniform, so the number `N` of agreements on
the line through a random point in a random direction has mean `μ = q * a / Q` and variance at most
`μ`, and Chebyshev's inequality bounds the first event
(`Cslib.Code.card_filter_lineAgree_le_mul_sq_le`). The second has probability at most
`(D - d) / (q - 1)` given the line. Averaging over `z`
(`Cslib.Code.exists_card_lineListDecode_ne_le`), some advice point `z` makes the decoder, with the
advice `p(z)`, correct at all but
`1 + (q * a * (Q - 1) / (μ - D) ^ 2 + Q * (Q - 1) * (D - d) / (q - 1)) / Q` points.

## Main definitions

* `Cslib.Code.lineAgree`: the number of points of a line in a set.
* `Cslib.Code.lineListDecode`: the local list decoder with advice.

## Main results

* `Cslib.Code.card_filter_lineAgree_le_mul_sq_le`: random lines sample a set well.
* `Cslib.Code.lineListDecode_eq`: the decoder is correct on good lines and hint positions.
* `Cslib.Code.exists_card_lineListDecode_ne_le`: **local list decoding of Reed–Muller codes**.

## References

* [M. Sudan, L. Trevisan, S. Vadhan, *Pseudorandom generators without the XOR lemma*]
  [SudanTrevisanVadhan2001]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09], Chapter 19
-/

@[expose] public section

namespace Cslib.Code

open Finset Polynomial Cslib.LinearAlgebra

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m : ℕ}

/-! ### Random lines sample well -/

/-- The number of points of the line `t ↦ x + t • u` in `A`. -/
def lineAgree (A : Finset (Fin m → F)) (x u : Fin m → F) : ℕ := #{t : F | x + t • u ∈ A}

/-- The nonzero directions with a base point. -/
private def seeds (m : ℕ) (F : Type*) [Fintype F] [DecidableEq F] [Zero F] :
    Finset ((Fin m → F) × (Fin m → F)) := univ.filter fun xu => xu.2 ≠ 0

private theorem card_seeds : #(seeds m F) = Fintype.card F ^ m * (Fintype.card F ^ m - 1) := by
  rw [seeds, show (univ.filter fun xu : (Fin m → F) × (Fin m → F) => xu.2 ≠ 0) =
    univ ×ˢ (univ.filter fun u : Fin m → F => u ≠ 0) by ext; simp, card_product, card_univ,
    Fintype.card_fun, Fintype.card_fin, filter_ne', card_erase_of_mem (mem_univ _), card_univ,
    Fintype.card_fun, Fintype.card_fin]

/-- Each point of a random line is uniformly distributed. -/
private theorem card_seeds_mem (A : Finset (Fin m → F)) (t : F) :
    #{xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A} = #A * (Fintype.card F ^ m - 1) := by
  rw [show #A * (Fintype.card F ^ m - 1) = #(A ×ˢ (univ : Finset (Fin m → F)).erase 0) by
    rw [card_product, card_erase_of_mem (mem_univ _), card_univ, Fintype.card_fun,
      Fintype.card_fin]]
  refine card_nbij' (fun xu => (xu.1 + t • xu.2, xu.2)) (fun yu => (yu.1 - t • yu.2, yu.2))
    ?_ ?_ ?_ ?_ <;> intro xu hxu <;> simp_all [seeds]

omit [Fintype F] [DecidableEq F] in
/-- The base point and direction of the line through `y` at `t` and `y'` at `t'`. -/
private theorem line_through {t t' : F} (hsub : t - t' ≠ 0) (y y' : Fin m → F) :
    y - t • (t - t')⁻¹ • (y - y') + t • (t - t')⁻¹ • (y - y') = y ∧
      y - t • (t - t')⁻¹ • (y - y') + t' • (t - t')⁻¹ • (y - y') = y' := by
  have h1 : (t - t') • (t - t')⁻¹ • (y - y') = y - y' := by
    rw [smul_smul, mul_inv_cancel₀ hsub, one_smul]
  exact ⟨sub_add_cancel _ _, by linear_combination (norm := module) -h1⟩

/-- Two distinct points of a random line are a uniformly random pair of distinct points. -/
private theorem card_seeds_mem_mem (A : Finset (Fin m → F)) {t t' : F} (htt : t ≠ t') :
    #{xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A ∧ xu.1 + t' • xu.2 ∈ A} = #A * #A - #A := by
  rw [← offDiag_card]
  have hsub : t - t' ≠ 0 := sub_ne_zero.2 htt
  have hdir : ∀ x u : Fin m → F, (t - t')⁻¹ • (x + t • u - (x + t' • u)) = u := fun x u => by
    rw [show x + t • u - (x + t' • u) = (t - t') • u by rw [sub_smul]; abel, smul_smul,
      inv_mul_cancel₀ hsub, one_smul]
  refine card_nbij' (fun xu => (xu.1 + t • xu.2, xu.1 + t' • xu.2))
    (fun yy => (yy.1 - t • (t - t')⁻¹ • (yy.1 - yy.2), (t - t')⁻¹ • (yy.1 - yy.2)))
    (fun xu hxu => ?_) (fun yy hyy => ?_) (fun xu _ => ?_) (fun yy _ => ?_)
  · obtain ⟨x, u⟩ := xu
    simp only [mem_coe, seeds, filter_filter, mem_filter, mem_offDiag] at hxu ⊢
    exact ⟨hxu.2.2.1, hxu.2.2.2, fun heq => hxu.2.1 (by rw [← hdir x u, heq, sub_self, smul_zero])⟩
  · obtain ⟨y, y'⟩ := yy
    rw [mem_coe, mem_offDiag] at hyy
    rw [mem_coe, seeds, filter_filter, mem_filter]
    obtain ⟨h₁, h₂⟩ := line_through hsub y y'
    exact ⟨mem_univ _, fun h0 => hyy.2.2 (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left
      (inv_ne_zero hsub))), by simpa only [h₁] using hyy.1, by simpa only [h₂] using hyy.2.1⟩
  · obtain ⟨x, u⟩ := xu
    simp only [hdir, Prod.mk.injEq, and_true]
    abel
  · obtain ⟨y, y'⟩ := yy
    obtain ⟨h₁, h₂⟩ := line_through hsub y y'
    exact Prod.ext h₁ h₂

/-- `lineAgree` as a sum of indicators. -/
private theorem lineAgree_cast_eq_sum (A : Finset (Fin m → F)) (x u : Fin m → F) :
    (lineAgree A x u : ℝ) = ∑ t : F, if x + t • u ∈ A then (1 : ℝ) else 0 := by
  simp [lineAgree, sum_boole]

/-- The first moment of `lineAgree A` over `seeds m F`. -/
private theorem sum_lineAgree_seeds (A : Finset (Fin m → F)) :
    ∑ xu ∈ seeds m F, (lineAgree A xu.1 xu.2 : ℝ) =
      Fintype.card F * (#A * ((Fintype.card F : ℝ) ^ m - 1)) := by
  simp only [lineAgree_cast_eq_sum]
  rw [sum_comm]
  simp only [sum_boole, card_seeds_mem, sum_const, card_univ, nsmul_eq_mul, Nat.cast_mul,
    Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos), Nat.cast_pow, Nat.cast_one]

/-- The second moment of `lineAgree A` over `seeds m F`. -/
private theorem sum_lineAgree_sq_seeds (A : Finset (Fin m → F)) :
    ∑ xu ∈ seeds m F, (lineAgree A xu.1 xu.2 : ℝ) ^ 2 =
      Fintype.card F * (#A * ((Fintype.card F : ℝ) ^ m - 1)) +
        Fintype.card F * (Fintype.card F - 1) * (#A * #A - #A) := by
  have hsq (xu : (Fin m → F) × (Fin m → F)) :
      (lineAgree A xu.1 xu.2 : ℝ) ^ 2 = ∑ t : F, ∑ t' : F,
        if xu.1 + t • xu.2 ∈ A ∧ xu.1 + t' • xu.2 ∈ A then (1 : ℝ) else 0 := by
    rw [lineAgree_cast_eq_sum, sq, sum_mul_sum]
    simp only [ite_zero_mul_ite_zero, mul_one]
  have hrow (t : F) : ∑ t' : F,
      ((#{xu ∈ seeds m F | xu.1 + t • xu.2 ∈ A ∧ xu.1 + t' • xu.2 ∈ A} : ℕ) : ℝ) =
        #A * ((Fintype.card F : ℝ) ^ m - 1) + (Fintype.card F - 1) * (#A * #A - #A) := by
    rw [← add_sum_erase _ _ (mem_univ t), sum_congr rfl fun t' ht' => by
      rw [card_seeds_mem_mem A (Ne.symm (ne_of_mem_erase ht'))]]
    simp only [and_self, card_seeds_mem A t, sum_const, card_erase_of_mem (mem_univ _),
      card_univ, nsmul_eq_mul, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos),
      Nat.cast_sub (Fintype.card_pos (α := F)), Nat.cast_sub (Nat.le_mul_self #A), Nat.cast_pow,
      Nat.cast_one]
  simp only [hsq]
  rw [sum_comm]
  refine (sum_congr rfl fun _ _ => sum_comm).trans ?_
  simp only [sum_boole, hrow, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- The centered second moment of `lineAgree A` over `seeds m F`. -/
private theorem sum_lineAgree_sub_sq_le (A : Finset (Fin m → F)) :
    ∑ xu ∈ seeds m F,
        ((lineAgree A xu.1 xu.2 : ℝ) - Fintype.card F * #A / Fintype.card F ^ m) ^ 2 ≤
      Fintype.card F * #A * (Fintype.card F ^ m - 1) := by
  have haQ : (#A : ℝ) ≤ Fintype.card F ^ m := by
    exact_mod_cast (card_le_univ A).trans_eq (by simp)
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hQ1 : (1 : ℝ) ≤ Fintype.card F ^ m := one_le_pow₀ hq1
  have ha0 : (0 : ℝ) ≤ #A := by positivity
  have hcardS : (#(seeds m F) : ℝ) = Fintype.card F ^ m * (Fintype.card F ^ m - 1) := by
    rw [card_seeds, Nat.cast_mul, Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos)]; simp
  simp only [sub_sq, sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, ← sum_mul,
    ← mul_sum, sum_lineAgree_seeds, sum_lineAgree_sq_seeds, hcardS]
  generalize (Fintype.card F : ℝ) ^ m = Q at *
  generalize (Fintype.card F : ℝ) = q at *
  generalize (#A : ℝ) = a at *
  have hQ0 : Q ≠ 0 := by linarith
  have key : 0 ≤ q * a * ((q - 1) * (Q - a) + a * (Q - 1)) / Q := by
    have := mul_nonneg (sub_nonneg.2 hq1) (sub_nonneg.2 haQ)
    have := mul_nonneg ha0 (sub_nonneg.2 hQ1)
    exact div_nonneg (by positivity) (by linarith)
  rw [← sub_nonneg]
  convert key using 1
  field_simp
  ring

/-- **Random lines sample a set well.** Over all points `x` and nonzero directions `u`, the
number of pairs for which the line `t ↦ x + t • u` has at most `D` points in `A` is at most
`q * a * (Q - 1) / (μ - D) ^ 2`, where `a = #A`, `Q = q ^ m` and `μ = q * a / Q > D` is the mean
number of points of a line in `A`. -/
theorem card_filter_lineAgree_le_mul_sq_le (A : Finset (Fin m → F)) {D : ℝ}
    (hD : D < Fintype.card F * #A / Fintype.card F ^ m) :
    (#{xu : (Fin m → F) × (Fin m → F) | xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ D} : ℝ) *
        (Fintype.card F * #A / Fintype.card F ^ m - D) ^ 2 ≤
      Fintype.card F * #A * (Fintype.card F ^ m - 1) := by
  have hfilter : ({xu : (Fin m → F) × (Fin m → F) |
      xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ D} : Finset _) =
      {xu ∈ seeds m F | (lineAgree A xu.1 xu.2 : ℝ) ≤ D} := by rw [seeds, filter_filter]
  rw [hfilter]
  refine (card_filter_mul_le_sum _ _ _ (fun _ _ => sq_nonneg _) fun xu _ hxu => ?_).trans
    (sum_lineAgree_sub_sq_le A)
  nlinarith [sq_nonneg ((lineAgree A xu.1 xu.2 : ℝ) - Fintype.card F * #A / Fintype.card F ^ m)]

/-! ### The decoder -/

/-- **The local list decoder with advice.** To decode at `x` with advice `a` at `z`: parametrize
the line through `x` and `z` as `t ↦ x + t • v`, with `v` the normalization of `z - x`, and run
Sudan decoding with the hint `a` at the position `c = firstNonzero (z - x)` of `z` on the
restriction of `g` to the line. -/
noncomputable def lineListDecode (g : (Fin m → F) → F) (d D : ℕ) (z : Fin m → F) (a : F)
    (x : Fin m → F) : F :=
  hintDecode id (fun t : F => g (x + t • (firstNonzero (z - x))⁻¹ • (z - x))) d D
    (firstNonzero (z - x)) a

/-- Scaling the direction by a nonzero constant does not change the number of points of a line in
a set. -/
theorem lineAgree_smul (A : Finset (Fin m → F)) (x u : Fin m → F) {c : F} (hc : c ≠ 0) :
    lineAgree A x (c • u) = lineAgree A x u := by
  refine card_nbij' (fun t => t * c) (fun t => t * c⁻¹) (fun t ht => ?_) (fun t ht => ?_)
    (fun t _ => by simp [hc]) (fun t _ => by simp [hc])
  · simpa [mul_smul] using ht
  · simpa [smul_smul, hc] using ht

/-- **The decoder at a pair of points.** With `c = firstNonzero (z - x)` and
`v = c⁻¹ • (z - x)`, the decoder with advice `p z` is Sudan decoding with the hint `p (x + c • v)`
at `c` on the line `t ↦ x + t • v`. -/
theorem lineListDecode_eq (g p : (Fin m → F) → F) (d D : ℕ) {x z : Fin m → F} :
    lineListDecode g d D z (p z) x =
      hintDecode id (fun t : F => g (x + t • (firstNonzero (z - x))⁻¹ • (z - x))) d D
        (firstNonzero (z - x))
        (p (x + firstNonzero (z - x) • (firstNonzero (z - x))⁻¹ • (z - x))) := by
  rw [firstNonzero_smul_inv_smul, add_sub_cancel]
  rfl

/-- **Few bad hint positions on a good line.** If the line `t ↦ x + t • v` has more than `D`
points where `g` agrees with the Reed–Muller codeword `p`, then Sudan decoding with the hint
`p (x + τ • v)` at `τ` returns `p x` for all but at most `D - d` positions `τ`. -/
private theorem card_hintDecode_line_ne_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F) (x v : Fin m → F)
    (hagree : D < lineAgree {y | g y = p y} x v) :
    #{τ | hintDecode id (fun t : F => g (x + t • v)) d D τ (p (x + τ • v)) ≠ p x} ≤ D - d := by
  obtain ⟨P, hP, hPeval⟩ := exists_natDegree_le_eval_eq_of_mem_reedMuller hp x v
  have hx : p x = P.eval 0 := by rw [hPeval, zero_smul, add_zero]
  have hag : #{t : F | P.eval (id t) = g (x + t • v)} = lineAgree {y | g y = p y} x v := by
    simp only [lineAgree]
    congr 1
    ext t
    simp [hPeval, eq_comm]
  simpa only [← hPeval, hx] using card_hintDecode_ne_le (α := id)
    (w := fun t : F => g (x + t • v)) Function.injective_id hd hn hDq hP (by rwa [hag])

/-- The normalized directions: those whose first nonzero entry is `1`. -/
private def normDirs (m : ℕ) (F : Type*) [Field F] [Fintype F] [DecidableEq F] :
    Finset (Fin m → F) := univ.filter fun v => firstNonzero v = 1

/-- There are at most `(Q - 1) / (q - 1)` normalized directions. -/
private theorem card_normDirs_mul_le :
    #(normDirs m F) * (Fintype.card F - 1) ≤ Fintype.card F ^ m - 1 := by
  have h := card_le_card_of_injOn (s := normDirs m F ×ˢ (univ.erase (0 : F)))
    (t := (univ : Finset (Fin m → F)).erase 0) (fun vc => vc.2 • vc.1) (fun vc hvc => by
      simp only [coe_product, Set.mem_prod, mem_coe, normDirs, mem_filter, mem_univ, true_and,
        mem_erase, ne_eq, and_true] at hvc ⊢
      exact fun h0 => (smul_eq_zero.1 h0).elim hvc.2 fun h0 =>
        one_ne_zero (hvc.1.symm.trans (firstNonzero_eq_zero_iff.2 h0)))
      (fun vc hvc vc' hvc' heq => by
      simp only [coe_product, Set.mem_prod, mem_coe, normDirs, mem_filter, mem_univ, true_and,
        mem_erase, ne_eq, and_true] at hvc hvc' heq
      have hc : vc.2 = vc'.2 := by
        simpa only [firstNonzero_smul, hvc.1, hvc'.1, mul_one] using congrArg firstNonzero heq
      rw [hc] at heq
      exact Prod.ext (smul_right_injective _ hvc'.2 heq) hc)
  rwa [card_product, card_erase_of_mem (mem_univ _), card_erase_of_mem (mem_univ _), card_univ,
    card_univ, Fintype.card_fun, Fintype.card_fin] at h

/-- For a fixed `x`, at most `#(normDirs m F) * (D - d)` points `z ≠ x` lie on a line through `x`
with more than `D` agreements yet make `lineListDecode` fail at `x`. -/
private theorem card_filter_lineListDecode_ne_of_lt_lineAgree_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F) (x : Fin m → F) :
    #{z | z ≠ x ∧ D < lineAgree {y | g y = p y} x (z - x) ∧
      lineListDecode g d D z (p z) x ≠ p x} ≤ #(normDirs m F) * (D - d) := by
  set A : Finset (Fin m → F) := {y | g y = p y}
  let bad (v : Fin m → F) : Finset F :=
    {τ | hintDecode id (fun t : F => g (x + t • v)) d D τ (p (x + τ • v)) ≠ p x}
  calc #{z | z ≠ x ∧ D < lineAgree A x (z - x) ∧ lineListDecode g d D z (p z) x ≠ p x}
      ≤ #(((normDirs m F).filter (fun v => D < lineAgree A x v)).sigma bad) := by
        refine card_le_card_of_injOn
          (fun z => ⟨(firstNonzero (z - x))⁻¹ • (z - x), firstNonzero (z - x)⟩)
          (fun z hz => ?_) (fun z hz z' hz' heq => ?_)
        · simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hz
          obtain ⟨hne, hD, hdec⟩ := hz
          have hl : firstNonzero (z - x) ≠ 0 := firstNonzero_eq_zero_iff.not.2 (sub_ne_zero.2 hne)
          simp only [coe_sigma, Set.mem_sigma_iff, mem_coe, mem_filter, normDirs, mem_univ,
            true_and, bad]
          rw [lineListDecode_eq g p d D] at hdec
          exact ⟨⟨by rw [firstNonzero_smul, inv_mul_cancel₀ hl],
            by rwa [lineAgree_smul A _ _ (inv_ne_zero hl)]⟩, hdec⟩
        · simp only [Sigma.mk.inj_iff, heq_eq_eq] at heq
          rw [← sub_left_inj (a := x), ← firstNonzero_smul_inv_smul (u := z - x), heq.1, heq.2,
            firstNonzero_smul_inv_smul]
    _ = ∑ v ∈ (normDirs m F).filter (fun v => D < lineAgree A x v), #(bad v) := card_sigma _ _
    _ ≤ ∑ v ∈ (normDirs m F).filter (fun v => D < lineAgree A x v), (D - d) :=
        sum_le_sum fun v hv => card_hintDecode_line_ne_le hd hn hDq hp g x v (mem_filter.1 hv).2
    _ ≤ #(normDirs m F) * (D - d) := by
        rw [sum_const, smul_eq_mul]; exact Nat.mul_le_mul_right _ (card_filter_le _ _)

/-- Over all pairs `(x, z)`, the number of pairs where `lineListDecode` fails is at most the
diagonal (`q ^ m`), plus the pairs on lines with at most `D` agreements, plus at most
`q ^ m * #(normDirs m F) * (D - d)` pairs on good lines with a bad hint position. -/
private theorem sum_card_filter_lineListDecode_ne_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F) :
    ∑ z : Fin m → F, #{x | lineListDecode g d D z (p z) x ≠ p x} ≤
      Fintype.card F ^ m +
        #{xu : (Fin m → F) × (Fin m → F) |
          xu.2 ≠ 0 ∧ (lineAgree {y | g y = p y} xu.1 xu.2 : ℝ) ≤ (D : ℝ)} +
        Fintype.card F ^ m * (#(normDirs m F) * (D - d)) := by
  set A : Finset (Fin m → F) := {y | g y = p y}
  have hswap : (∑ z : Fin m → F, #{x | lineListDecode g d D z (p z) x ≠ p x}) =
      ∑ x : Fin m → F, #{z | lineListDecode g d D z (p z) x ≠ p x} := by
    simp only [card_eq_sum_ones, sum_filter]; exact sum_comm
  have hpt (x : Fin m → F) : #{z | lineListDecode g d D z (p z) x ≠ p x} ≤
      1 + #{u : Fin m → F | u ≠ 0 ∧ (lineAgree A x u : ℝ) ≤ (D : ℝ)} +
        #(normDirs m F) * (D - d) := by
    have hsub : ({z | lineListDecode g d D z (p z) x ≠ p x} : Finset _) ⊆
        ({x} : Finset _) ∪ ({z | z ≠ x ∧ lineAgree A x (z - x) ≤ D} : Finset _) ∪
          ({z | z ≠ x ∧ D < lineAgree A x (z - x) ∧
            lineListDecode g d D z (p z) x ≠ p x} : Finset _) := by
      intro z hz
      simp only [mem_filter, mem_univ, true_and, mem_union, mem_singleton, ← not_le] at hz ⊢
      tauto
    have hshift : #{z | z ≠ x ∧ lineAgree A x (z - x) ≤ D} =
        #{u : Fin m → F | u ≠ 0 ∧ (lineAgree A x u : ℝ) ≤ (D : ℝ)} := by
      simp only [card_eq_sum_ones, sum_filter]
      exact Fintype.sum_equiv (Equiv.subRight x) _ _ fun z => by
        simp [Equiv.subRight_apply, sub_ne_zero]
    refine (card_le_card hsub).trans ((card_union_le _ _).trans (add_le_add
      ((card_union_le _ _).trans_eq (by rw [card_singleton, hshift]))
      (card_filter_lineListDecode_ne_of_lt_lineAgree_le hd hn hDq hp g x)))
  have hS₂ : (∑ x : Fin m → F, #{u : Fin m → F | u ≠ 0 ∧ (lineAgree A x u : ℝ) ≤ (D : ℝ)}) =
      #{xu : (Fin m → F) × (Fin m → F) | xu.2 ≠ 0 ∧ (lineAgree A xu.1 xu.2 : ℝ) ≤ (D : ℝ)} := by
    simp only [card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  rw [hswap]; refine (sum_le_sum fun x _ => hpt x).trans ?_
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fun, Fintype.card_fin, smul_eq_mul,
    mul_one, hS₂, le_rfl]

/-- In `ℝ`, the number of normalized directions is at most `(q ^ m - 1) / (q - 1)`. -/
private theorem card_normDirs_le_real :
    (#(normDirs m F) : ℝ) ≤ ((Fintype.card F : ℝ) ^ m - 1) / (Fintype.card F - 1) := by
  rw [le_div_iff₀ (sub_pos.2 (by exact_mod_cast Fintype.one_lt_card))]
  have h := Nat.cast_le (α := ℝ).2 (card_normDirs_mul_le (m := m) (F := F))
  rwa [Nat.cast_mul, Nat.cast_sub Fintype.card_pos,
    Nat.cast_sub (Nat.one_le_pow _ _ Fintype.card_pos), Nat.cast_pow, Nat.cast_one] at h

/-- **Local list decoding of Reed–Muller codes**, a variant of [SudanTrevisanVadhan2001]. Let
`p` be a codeword of the Reed–Muller code of degree `d ≥ 1` in `m` variables over a field with `q`
elements, `Q = q ^ m`, and let `g` agree with `p` on `a` points. Let `D < q` be such that there
are more than `q` monomials of `(1, d)`-weighted degree at most `D`, and suppose
`D < μ = q * a / Q`. Then for some advice point `z`, the decoder `lineListDecode g d D z (p z)`
computes `p` at all but
`1 + (q * a * (Q - 1) / (μ - D) ^ 2 + Q * (Q - 1) * (D - d) / (q - 1)) / Q` points. -/
theorem exists_card_lineListDecode_ne_le {d D : ℕ} (hd : 1 ≤ d)
    (hn : Fintype.card F < #(Sudan.monomials d D)) (hDq : D < Fintype.card F)
    {p : (Fin m → F) → F} (hp : p ∈ reedMuller F m d) (g : (Fin m → F) → F)
    (hμ : (D : ℝ) < Fintype.card F * #{y | g y = p y} / Fintype.card F ^ m) :
    ∃ z, (#{x | lineListDecode g d D z (p z) x ≠ p x} : ℝ) ≤
      1 + (Fintype.card F * #{y | g y = p y} * (Fintype.card F ^ m - 1) /
          (Fintype.card F * #{y | g y = p y} / Fintype.card F ^ m - D) ^ 2 +
        Fintype.card F ^ m * (Fintype.card F ^ m - 1) * (D - d : ℕ) / (Fintype.card F - 1)) /
          Fintype.card F ^ m := by
  have hlow := (le_div_iff₀ (pow_pos (sub_pos.2 hμ) 2)).2
    (card_filter_lineAgree_le_mul_sq_le _ hμ)
  have hbad : (Fintype.card F ^ m : ℝ) * (#(normDirs m F) * (D - d : ℕ)) ≤
      Fintype.card F ^ m * (Fintype.card F ^ m - 1) * (D - d : ℕ) / (Fintype.card F - 1) := by
    rw [mul_assoc, mul_div_assoc, mul_div_right_comm]
    gcongr
    exact card_normDirs_le_real
  have htot := Nat.cast_le (α := ℝ).2 (sum_card_filter_lineListDecode_ne_le hd hn hDq hp g)
  simp only [Nat.cast_sum, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at htot
  refine (exists_le_of_sum_le univ_nonempty ?_).imp fun _ => And.right
  rw [sum_const, card_univ, nsmul_eq_mul, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
    mul_add, mul_one, mul_div_cancel₀ _ (by positivity)]
  linarith

end Cslib.Code
