/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The Sapozhenko–Lovász–Stein greedy covering bound

If every element `w ∈ W` of a nonempty finite ground set is hit by at least a `p`-fraction (`p > 0`)
of the tests in a nonempty finite family `S`, the greedy set-cover algorithm — repeatedly choosing
a test hitting as many remaining elements as possible — shrinks the uncovered set by at least a
factor `1 - p < exp (-p)` per step and covers `W` using at most `(1 + ln |W|) / p` tests
(`Cslib.exists_cover_card_le_of_mul_le_card_hit`) [Jukna2011, §1.2 and §2.6].

When every element of `W` is hit the same number of times (`hconst`), double counting equates the
per-element hit fraction with the average covered weight per test divided by `|W|`, yielding a
cover of size at most `(1 + ln |W|) |W| |S| / M` for any positive lower bound `M` on the total
number of incidences (`Cslib.exists_cover_card_le_of_const_hit`). Specializing to a uniform set
family `F ⊆ 2 ^ X` gives Lemma 2 of [Sergeev2026UniqueDisjointness, §3, p. 4]
(`Cslib.exists_subset_cover_card_le_of_uniform`): `F` contains a cover of `X` of size at most
`(1 + ln |X|) |X| / s`, where `s` is the average cardinality of a set in `F`.

## Main results

* `Cslib.exists_cover_card_le_of_mul_le_card_hit`: greedy covering from a fractional hit bound `p`.
* `Cslib.exists_cover_card_le_of_const_hit`: greedy covering from uniform degree and total
  incidences.
* `Cslib.exists_subset_cover_card_le_of_uniform`: Lemma 2 of [Sergeev2026UniqueDisjointness]
  (Sapozhenko–Lovász–Stein uniform set-covering bound).

## References

* [S. Jukna, *Extremal Combinatorics: With Applications in Computer Science*, 2nd ed.][Jukna2011],
  §1.2 and §2.6
* [I. S. Sergeev, *Upper Bounds for the Monotone Rank of the Unique Disjointness Matrix*]
  [Sergeev2026UniqueDisjointness], §3, Lemma 2, p. 4
-/

public section

namespace Cslib

open Finset

/-- Double counting of incidences between `U` and the tests in `S`. -/
private theorem sum_card_filter_hit_comm {S β : Type*} [Fintype S] (U : Finset β)
    (hit : S → β → Prop) [DecidableRel hit] :
    ∑ w ∈ U, ((univ.filter (hit · w)).card : ℝ) = ∑ s : S, ((U.filter (hit s ·)).card : ℝ) := by
  simp only [← sum_boole]
  exact sum_comm

/-- **Greedy covering from fractional density**: if every `w ∈ W` (`W` nonempty) is hit by at least
`p * |S|` elements of `S` (`p > 0`), some subset `G ⊆ S` covers `W` with
`|G| ≤ (1 + ln |W|) / p` [Jukna2011, §1.2]. -/
theorem exists_cover_card_le_of_mul_le_card_hit {S β : Type*} [Fintype S] [Nonempty S]
    {W : Finset β} (hW : W.Nonempty) (hit : S → β → Prop) [DecidableRel hit] {p : ℝ}
    (hp : 0 < p) (hdeg : ∀ w ∈ W, p * Fintype.card S ≤ ((univ.filter (hit · w)).card : ℝ)) :
    ∃ G : Finset S, (∀ w ∈ W, ∃ s ∈ G, hit s w) ∧
      (G.card : ℝ) ≤ (1 + Real.log W.card) / p := by
  classical
  have hScard : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos (α := S)
  have hp1 : p ≤ 1 := by
    obtain ⟨w₀, hw₀⟩ := hW
    have hle : ((univ.filter (hit · w₀)).card : ℝ) ≤ Fintype.card S := by
      exact_mod_cast (card_filter_le (univ : Finset S) (hit · w₀)).trans_eq card_univ
    nlinarith [hdeg w₀ hw₀]
  let pick (U : Finset β) : S :=
    (exists_max_image (univ : Finset S) (fun s => (U.filter (hit s ·)).card) univ_nonempty).choose
  have hpick (U : Finset β) (s : S) :
      (U.filter (hit s ·)).card ≤ (U.filter (hit (pick U) ·)).card :=
    (exists_max_image (univ : Finset S) (fun s => (U.filter (hit s ·)).card)
      univ_nonempty).choose_spec.2 s (mem_univ s)
  let U : ℕ → Finset β :=
    fun k => Nat.rec W (fun _ Ui => Ui.filter fun w => ¬ hit (pick Ui) w) k
  have hU_sub : ∀ i, U i ⊆ W := by
    intro i
    induction i with
    | zero => exact Subset.rfl
    | succ i ih => exact (filter_subset _ (U i)).trans ih
  have hU_cov : ∀ k, ∀ w ∈ W, w ∈ U k ∨ ∃ i < k, hit (pick (U i)) w := by
    intro k
    induction k with
    | zero => intro w hw; exact Or.inl hw
    | succ k ih =>
      intro w hw
      rcases ih w hw with hwUk | ⟨i, hi, hhit⟩
      · by_cases hh : hit (pick (U k)) w
        · exact Or.inr ⟨k, Nat.lt_succ_self k, hh⟩
        · exact Or.inl (mem_filter.2 ⟨hwUk, hh⟩)
      · exact Or.inr ⟨i, Nat.lt_succ_of_lt hi, hhit⟩
  have hU_step : ∀ i, ((U (i + 1)).card : ℝ) ≤ (U i).card * (1 - p) := by
    intro i
    have hsum : (U i).card * (p * Fintype.card S) ≤
        (Fintype.card S : ℝ) * ((U i).filter (hit (pick (U i)) ·)).card := by
      calc (U i).card * (p * Fintype.card S)
          = ∑ _w ∈ U i, p * Fintype.card S := by rw [sum_const, nsmul_eq_mul]
        _ ≤ ∑ w ∈ U i, ((univ.filter (hit · w)).card : ℝ) :=
              sum_le_sum fun w hw => hdeg w (hU_sub i hw)
        _ = ∑ s : S, (((U i).filter (hit s ·)).card : ℝ) := sum_card_filter_hit_comm _ _
        _ ≤ ∑ _s : S, (((U i).filter (hit (pick (U i)) ·)).card : ℝ) :=
              sum_le_sum fun s _ => by exact_mod_cast hpick (U i) s
        _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]
    have hpart :
        (((U i).filter (hit (pick (U i)) ·)).card : ℝ) + (U (i + 1)).card = (U i).card := by
      exact_mod_cast card_filter_add_card_filter_not (p := fun w => hit (pick (U i)) w) (s := U i)
    have hhit_ge : (U i).card * p ≤ ((U i).filter (hit (pick (U i)) ·)).card := by
      nlinarith
    linarith
  have hU_pow : ∀ k, ((U k).card : ℝ) ≤ W.card * (1 - p) ^ k := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, mul_one]
      exact le_rfl
    | succ k ih =>
      rw [pow_succ, ← mul_assoc]
      exact (hU_step k).trans (mul_le_mul_of_nonneg_right ih (by linarith))
  have hempty (k : ℕ) (h : ((U k).card : ℝ) < 1) : U k = ∅ :=
    card_eq_zero.1 (Nat.lt_one_iff.1 (by exact_mod_cast h))
  have hWreal : (1 : ℝ) ≤ W.card := by exact_mod_cast hW.card_pos
  have hlog_nonneg : 0 ≤ Real.log W.card := Real.log_nonneg hWreal
  obtain ⟨k, hUk, hk⟩ : ∃ k : ℕ, U k = ∅ ∧ (k : ℝ) ≤ (1 + Real.log W.card) / p := by
    by_cases hsmall : W.card = 1 ∨ p = 1
    · refine ⟨1, hempty 1 ?_, ?_⟩
      · have h1 := hU_pow 1
        rw [pow_one] at h1
        rcases hsmall with hW1 | rfl
        · rw [hW1, Nat.cast_one] at h1
          linarith
        · linarith
      · rw [Nat.cast_one, le_div_iff₀ hp]
        linarith
    push Not at hsmall
    have hWgt1 : (1 : ℝ) < W.card := by
      exact_mod_cast (show 1 < W.card by have := hW.card_pos; omega)
    have hlog_pos : 0 < Real.log W.card := Real.log_pos hWgt1
    let k : ℕ := Nat.ceil (Real.log W.card / p)
    refine ⟨k, hempty k ?_, ?_⟩
    · have hpow_lt : (1 - p) ^ k < Real.exp (-p) ^ k :=
        pow_lt_pow_left₀ (by linarith [Real.add_one_lt_exp (neg_ne_zero.2 hp.ne')])
          (by linarith [lt_of_le_of_ne hp1 hsmall.2])
          (Nat.ceil_pos.2 (div_pos hlog_pos hp)).ne'
      have hkp : Real.log W.card ≤ (k : ℝ) * p := (div_le_iff₀ hp).1 (Nat.le_ceil _)
      have hexp_le : Real.exp (-p) ^ k ≤ (W.card : ℝ)⁻¹ := by
        rw [← Real.exp_natCast_mul, ← Real.exp_log (by positivity : (0 : ℝ) < W.card),
          ← Real.exp_neg]
        exact Real.exp_le_exp.2 (by linarith)
      calc ((U k).card : ℝ)
          ≤ W.card * (1 - p) ^ k := hU_pow k
        _ < W.card * (W.card : ℝ)⁻¹ :=
              mul_lt_mul_of_pos_left (hpow_lt.trans_le hexp_le) (by positivity)
        _ = 1 := mul_inv_cancel₀ (by positivity)
    · have hk_lt : (k : ℝ) < Real.log W.card / p + 1 := Nat.ceil_lt_add_one (by positivity)
      have hone_le : 1 ≤ 1 / p := (one_le_div hp).2 hp1
      calc (k : ℝ) ≤ Real.log W.card / p + 1 / p := by linarith
        _ = (1 + Real.log W.card) / p := by ring
  refine ⟨(range k).image fun i => pick (U i), fun w hw => ?_, ?_⟩
  · rcases hU_cov k w hw with hwk | ⟨i, hi, hhit⟩
    · simp [hUk] at hwk
    · exact ⟨pick (U i), mem_image.2 ⟨i, mem_range.2 hi, rfl⟩, hhit⟩
  · exact (show _ ≤ (k : ℝ) by exact_mod_cast card_image_le.trans_eq (card_range k)).trans hk

/-- **Greedy covering from constant hit count and total incidences**: if every element of `W` (`W`
nonempty) is hit by the same number of tests in `S` and the total number of incidences is at least
`M > 0`, some subset `G ⊆ S` covers `W` with `|G| ≤ (1 + ln |W|) |W| |S| / M`. -/
theorem exists_cover_card_le_of_const_hit {S β : Type*} [Fintype S] [Nonempty S]
    {W : Finset β} (hW : W.Nonempty) (hit : S → β → Prop) [DecidableRel hit]
    (hconst : ∀ w₁ ∈ W, ∀ w₂ ∈ W,
      (univ.filter (hit · w₁)).card = (univ.filter (hit · w₂)).card)
    {M : ℝ} (hM0 : 0 < M) (hM : M ≤ ∑ s : S, ((W.filter (hit s ·)).card : ℝ)) :
    ∃ G : Finset S, (∀ w ∈ W, ∃ s ∈ G, hit s w) ∧
      (G.card : ℝ) ≤ (1 + Real.log W.card) * W.card * Fintype.card S / M := by
  obtain ⟨w₀, hw₀⟩ := id hW
  let d : ℕ := (univ.filter (hit · w₀)).card
  have hd (w : β) (hw : w ∈ W) : ((univ.filter (hit · w)).card : ℝ) = d := by
    exact_mod_cast hconst w hw w₀ hw₀
  have hWpos : (0 : ℝ) < W.card := by exact_mod_cast hW.card_pos
  have hSpos : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos (α := S)
  have hdouble : M ≤ W.card * (d : ℝ) := by
    refine (hM.trans_eq (sum_card_filter_hit_comm W hit).symm).trans_eq ?_
    rw [← nsmul_eq_mul, ← sum_const]
    exact sum_congr rfl hd
  let p : ℝ := M / (W.card * Fintype.card S)
  have hp : 0 < p := by positivity
  have hdeg : ∀ w ∈ W, p * Fintype.card S ≤ ((univ.filter (hit · w)).card : ℝ) := by
    intro w hw
    have hpS : p * Fintype.card S = M / W.card := by
      simp only [p]
      field_simp
    rw [hd w hw, hpS, div_le_iff₀ hWpos]
    linarith
  obtain ⟨G, hGcov, hGcard⟩ := exists_cover_card_le_of_mul_le_card_hit hW hit hp hdeg
  refine ⟨G, hGcov, hGcard.trans_eq ?_⟩
  simp only [p]
  field_simp

/-- **Sapozhenko–Lovász–Stein uniform set-covering bound**
([Sergeev2026UniqueDisjointness, §3, Lemma 2, p. 4]; [Jukna2011, §2.6]): if `F ⊆ 2 ^ X` uniformly
covers a nonempty finite set `X` (`∀ x ∈ X, #{A ∈ F | x ∈ A} = d` with `d ≥ 1`), then `F` contains
a covering `G ⊆ F` of `X` of size `|G| ≤ (1 + ln |X|) |X| / s`, where
`s = (∑ A ∈ F, |A|) / |F|` is the average cardinality of a set in `F`. -/
theorem exists_subset_cover_card_le_of_uniform {α : Type*} [DecidableEq α]
    {X : Finset α} (hX : X.Nonempty) {F : Finset (Finset α)} (hF : F ⊆ X.powerset)
    {d : ℕ} (hd : 1 ≤ d) (hunif : ∀ x ∈ X, (F.filter (x ∈ ·)).card = d) :
    ∃ G ⊆ F, X ⊆ G.biUnion id ∧
      (G.card : ℝ) ≤ (1 + Real.log X.card) * X.card / ((∑ A ∈ F, (A.card : ℝ)) / F.card) := by
  obtain ⟨x₀, hx₀⟩ := id hX
  have hpos₀ : 0 < (F.filter (x₀ ∈ ·)).card := by
    rw [hunif x₀ hx₀]
    omega
  have hFne : F.Nonempty := by
    obtain ⟨A, hA⟩ := card_pos.1 hpos₀
    exact ⟨A, (mem_filter.1 hA).1⟩
  let _ : Nonempty F := hFne.coe_sort
  let hit : F → α → Prop := fun A x => x ∈ A.val
  have hcard_hit : ∀ x, (univ.filter (hit · x)).card = (F.filter (x ∈ ·)).card := by
    intro x
    refine card_bij (fun A _ => A.val) (fun A hA => ?_) (fun A₁ _ A₂ _ h => Subtype.ext h)
      (fun B hB => ?_)
    · rw [mem_filter] at hA
      exact mem_filter.2 ⟨A.property, hA.2⟩
    · rw [mem_filter] at hB
      exact ⟨⟨B, hB.1⟩, mem_filter.2 ⟨mem_univ _, hB.2⟩, rfl⟩
  have hconst : ∀ x₁ ∈ X, ∀ x₂ ∈ X,
      (univ.filter (hit · x₁)).card = (univ.filter (hit · x₂)).card := by
    intro x₁ hx₁ x₂ hx₂
    rw [hcard_hit, hcard_hit, hunif x₁ hx₁, hunif x₂ hx₂]
  let M : ℝ := ∑ A ∈ F, (A.card : ℝ)
  have hsum_eq : ∑ A : F, ((X.filter (hit A ·)).card : ℝ) = M := by
    rw [univ_eq_attach]
    refine (sum_congr rfl fun A _ => ?_).trans (sum_attach F fun A => (A.card : ℝ))
    change ((X.filter (· ∈ A.val)).card : ℝ) = _
    rw [filter_mem_eq_inter, inter_eq_right.2 (mem_powerset.1 (hF A.property))]
  have hM0 : 0 < M := by
    obtain ⟨A₀, hA₀⟩ := card_pos.1 hpos₀
    rw [mem_filter] at hA₀
    exact sum_pos' (fun _ _ => by positivity) ⟨A₀, hA₀.1, by exact_mod_cast card_pos.2 ⟨x₀, hA₀.2⟩⟩
  obtain ⟨G', hG'cov, hG'card⟩ :=
    exists_cover_card_le_of_const_hit hX hit hconst hM0 (le_of_eq hsum_eq.symm)
  let G : Finset (Finset α) := G'.image Subtype.val
  refine ⟨G, ?_, ?_, ?_⟩
  · intro A hA
    obtain ⟨A', _, rfl⟩ := mem_image.1 hA
    exact A'.property
  · intro x hx
    obtain ⟨A', hA'G, hxA'⟩ := hG'cov x hx
    exact mem_biUnion.2 ⟨A'.val, mem_image.2 ⟨A', hA'G, rfl⟩, hxA'⟩
  · have hG_le : (G.card : ℝ) ≤ G'.card := by exact_mod_cast card_image_le
    have hFcard : (Fintype.card F : ℝ) = F.card := by exact_mod_cast Fintype.card_coe F
    have hFpos : (0 : ℝ) < F.card := by exact_mod_cast hFne.card_pos
    refine (hG_le.trans hG'card).trans_eq ?_
    rw [hFcard]
    change (1 + Real.log X.card) * X.card * F.card / M =
      (1 + Real.log X.card) * X.card / (M / F.card)
    field_simp

end Cslib
