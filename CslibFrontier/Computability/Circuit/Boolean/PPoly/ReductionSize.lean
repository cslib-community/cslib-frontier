/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.PPoly
import CslibFrontier.Computability.Circuit.Boolean.Combinators

/-!
# Circuit sizes under length-bounded reductions

A fixed-width reduction pays for its own circuit and one target slice. A variable-width
reduction outputs a padded word and one flag per possible output length. Its postprocessing
pays for all possible target slices, the guards and their disjunction.

## Main definitions

* `readPaddedPrefix` selects the data bits for a particular length.
* `CircuitReductionDegrees` records circuit size and output-width envelopes.

## Main results

* `fixedWidth_size_of_reduction` gives the additive gate bound.
* `variableWidth_size_of_reduction` accounts for the guarded target circuits explicitly.
* `size_of_fixedWidth_degrees` and `size_of_reductionDegrees` give polynomial-degree bounds.
* `readPaddedPrefix_append` identifies the data prefix when flags are appended.
* `reduction_degree_tradeoff` transfers a fixed-degree source exclusion.
* `outside_PPoly_of_common_circuitReductionDegrees` transfers a family of source exclusions.
-/

public section

namespace Cslib.Circuits.Boolean

open Cslib Cslib.Circuits

/-- If the reduction supplies one fixed output width at each input width, circuit composition
adds the reduction gates and one target circuit at that width. Wires have zero gate cost. -/
theorem fixedWidth_size_of_reduction {A B : Language Bool} (m r s : ℕ → ℕ)
    (F : ∀ n, (Fin n → Bool) → Fin (m n) → Bool)
    (hF : ∀ n, complexity interpretation (F n) ≤ r n)
    (hcorrect : ∀ n (x : Fin n → Bool), List.ofFn x ∈ A ↔ List.ofFn (F n x) ∈ B)
    (hB : B ∈ SIZE s) : A ∈ SIZE (fun n => r n + s (m n)) := by
  intro n
  have hs : single (A.slice n) = fun x => single (B.slice (m n)) (F n x) := by
    funext x i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    change A.slice n x = B.slice (m n) (F n x)
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, Language.slice_eq_true_iff]
    exact hcorrect n x
  change complexity interpretation (single (A.slice n)) ≤ _
  rw [hs]
  exact (complexity_comp_le (F n) (single (B.slice (m n)))).trans
    (Nat.add_le_add (hF n) (hB (m n)))

/-- Read the indicated prefix of a padded word whose trailing outputs are length flags. -/
@[expose] def readPaddedPrefix {m : ℕ} (i : Fin (m + 1)) (z : Fin (m + (m + 1)) → Bool)
    (j : Fin i.val) : Bool := z (Fin.castAdd (m + 1) ⟨j.val, by omega⟩)

/-- Appending length flags leaves each bit of the selected data prefix unchanged. -/
@[simp] theorem readPaddedPrefix_append {m : ℕ} (i : Fin (m + 1))
    (u : Fin m → Bool) (v : Fin (m + 1) → Bool) (j : Fin i.val) :
    readPaddedPrefix i (Fin.append u v) j = u ⟨j.val, by omega⟩ :=
  Fin.append_left _ _ _

private noncomputable def selectedTest (B : Language Bool) {m : ℕ} (i : Fin (m + 1))
    (z : Fin (m + (m + 1)) → Bool) : Bool :=
  z (Fin.natAdd m i) && B.slice i.val (readPaddedPrefix i z)

private noncomputable def selectedSlice (B : Language Bool) (m : ℕ)
    (z : Fin (m + (m + 1)) → Bool) : Bool :=
  open Classical in decide (∃ i : Fin (m + 1), i ∈ Finset.univ ∧ selectedTest B i z = true)

private theorem complexity_selectedSlice {B : Language Bool} {s : ℕ → ℕ} (hB : B ∈ SIZE s)
    (m c : ℕ) (hc : ∀ i ≤ m, s i ≤ c) :
    complexity interpretation (single (selectedSlice B m)) ≤ (m + 1) * (c + 2) + 1 := by
  classical
  have h := complexity_decide_exists_mem_le (Finset.univ : Finset (Fin (m + 1)))
    (selectedTest B) (c := c + 1) (fun i _ => ?_)
  · change complexity interpretation (single (fun z => decide _)) ≤ _
    simpa only [Finset.card_univ, Fintype.card_fin, Nat.add_assoc] using h
  · let select (j : Fin i.val) : Fin (m + (m + 1)) := Fin.castAdd (m + 1) ⟨j.val, by omega⟩
    have wire := complexity_comp_le (I := interpretation)
      (fun z : Fin (m + (m + 1)) → Bool => z ∘ select) (single (B.slice i.val))
    rw [complexity_wiring, zero_add] at wire
    have hs :
        complexity interpretation (single fun z => B.slice i.val (readPaddedPrefix i z)) ≤ c :=
      wire.trans ((hB i.val).trans (hc i.val (Nat.le_of_lt_succ i.isLt)))
    have hand := complexity_and_le (fun z : Fin (m + (m + 1)) → Bool => z (Fin.natAdd m i))
      (fun z => B.slice i.val (readPaddedPrefix i z))
    rw [complexity_single_proj, zero_add] at hand
    exact hand.trans (Nat.add_le_add_right hs 1)

/-- A variable-width reduction circuit may output a padded word and one flag per possible
length. The cost of producing both is charged to `r`. The selector adds one guarded target
slice per length and a disjunction. -/
theorem variableWidth_size_of_reduction {A B : Language Bool} (m r s c : ℕ → ℕ)
    (F : ∀ n, (Fin n → Bool) → Fin (m n + (m n + 1)) → Bool)
    (hF : ∀ n, complexity interpretation (F n) ≤ r n)
    (hc : ∀ n i, i ≤ m n → s i ≤ c n)
    (hcorrect : ∀ n (x : Fin n → Bool), ∃ i : Fin (m n + 1),
      (∀ j, F n x (Fin.natAdd (m n) j) = true ↔ j = i) ∧
      (List.ofFn x ∈ A ↔ List.ofFn (readPaddedPrefix i (F n x)) ∈ B))
    (hB : B ∈ SIZE s) : A ∈ SIZE (fun n => r n + ((m n + 1) * (c n + 2) + 1)) := by
  intro n
  have hs : single (A.slice n) = fun x => single (selectedSlice B (m n)) (F n x) := by
    funext x j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    obtain ⟨i, flags, correct⟩ := hcorrect n x
    change A.slice n x = selectedSlice B (m n) (F n x)
    rw [Bool.eq_iff_iff, Language.slice_eq_true_iff, correct]
    change List.ofFn (readPaddedPrefix i (F n x)) ∈ B ↔
      decide (∃ k : Fin (m n + 1), k ∈ Finset.univ ∧ selectedTest B k (F n x) = true) = true
    rw [decide_eq_true_eq]
    dsimp only [selectedTest]
    simp only [Finset.mem_univ, true_and, Bool.and_eq_true, flags,
      Language.slice_eq_true_iff]
    exact ⟨fun h => ⟨i, rfl, h⟩, fun ⟨_, e, h⟩ => e ▸ h⟩
  change complexity interpretation (single (A.slice n)) ≤ _
  rw [hs]
  exact (complexity_comp_le (F n) (single (selectedSlice B (m n)))).trans
    (Nat.add_le_add (hF n) (complexity_selectedSlice hB _ _ (hc n)))

/-- Size and output-width degrees for the circuit representation used by
`variableWidth_size_of_reduction`. The two coefficients may depend on the source language.
The reduction circuit produces both the padded word and its one-hot length flags. -/
@[expose] def CircuitReductionDegrees (A B : Language Bool) (a b : ℕ) : Prop :=
  ∃ (R M : ℕ) (width : ℕ → ℕ)
    (F : ∀ n, (Fin n → Bool) → Fin (width n + (width n + 1)) → Bool),
    (∀ n, complexity interpretation (F n) ≤ R * (n + 1) ^ a) ∧
    (∀ n, width n + 1 ≤ M * (n + 1) ^ b) ∧
    (∀ n (x : Fin n → Bool), ∃ i : Fin (width n + 1),
      (∀ j, F n x (Fin.natAdd (width n) j) = true ↔ j = i) ∧
      (List.ofFn x ∈ A ↔ List.ofFn (readPaddedPrefix i (F n x)) ∈ B))

/-- Charge all possible output slices, giving degree `max a (b * (d + 1))`. -/
theorem size_of_reductionDegrees {A B : Language Bool} {a b d C : ℕ}
    (h : CircuitReductionDegrees A B a b) (hB : B ∈ SIZE (fun n => C * (n + 1) ^ d)) :
    ∃ K, A ∈ SIZE (fun n => K * (n + 1) ^ max a (b * (d + 1))) := by
  obtain ⟨R, M, width, F, hF, hw, hcorrect⟩ := h
  have hs := variableWidth_size_of_reduction width (fun n => R * (n + 1) ^ a)
    (fun n => C * (n + 1) ^ d) (fun n => C * (width n + 1) ^ d) F hF
    (fun n i hi => Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hi) _))
    hcorrect hB
  refine ⟨R + (C + 2) * M ^ (d + 1) + 1, SIZE_mono (fun n => ?_) hs⟩
  let x := n + 1
  let w := width n + 1
  let e := max a (b * (d + 1))
  have hx : 0 < x := Nat.succ_pos _
  have hwpos : 0 < w := Nat.succ_pos _
  have h₁ : x ^ a ≤ x ^ e := Nat.pow_le_pow_right hx (le_max_left _ _)
  have h₂ : x ^ (b * (d + 1)) ≤ x ^ e := Nat.pow_le_pow_right hx (le_max_right _ _)
  have h₃ : 1 ≤ x ^ e := Nat.succ_le_of_lt (Nat.pow_pos hx)
  have h₄ : 1 ≤ w ^ d := Nat.succ_le_of_lt (Nat.pow_pos hwpos)
  change R * x ^ a + (w * (C * w ^ d + 2) + 1) ≤ (R + (C + 2) * M ^ (d + 1) + 1) * x ^ e
  have hsel : w * (C * w ^ d + 2) ≤ (C + 2) * w ^ (d + 1) := by
    calc
      w * (C * w ^ d + 2) ≤ w * (C * w ^ d + 2 * w ^ d) :=
        Nat.mul_le_mul_left _ (Nat.add_le_add_left (by simpa using Nat.mul_le_mul_left 2 h₄) _)
      _ = (C + 2) * w ^ (d + 1) := by rw [pow_succ]; ring
  have hpow : w ^ (d + 1) ≤ M ^ (d + 1) * x ^ (b * (d + 1)) := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (hw n) _
  calc
    _ ≤ R * x ^ e + ((C + 2) * M ^ (d + 1) * x ^ e + x ^ e) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ h₁) (Nat.add_le_add
        (hsel.trans ((Nat.mul_le_mul_left _ (hpow.trans (Nat.mul_le_mul_left _ h₂))).trans_eq
          (by ring))) h₃)
    _ = _ := by ring

/-- An excluded source circuit degree is strictly below the degree obtained by composition. -/
theorem reduction_degree_tradeoff {L B : Language Bool} {a b d k C : ℕ}
    (hard : ∀ c, L ∉ SIZE (fun n => c * (n + 1) ^ k))
    (reduction : CircuitReductionDegrees L B a b)
    (target : B ∈ SIZE (fun n => C * (n + 1) ^ d)) :
    k < max a (b * (d + 1)) := by
  by_contra! h
  obtain ⟨c, hc⟩ := size_of_reductionDegrees reduction target
  exact hard c (SIZE_mono
    (fun n => Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos _) h)) hc)

/-- Fixed-width composition avoids the extra output-length factor in the exponent. -/
theorem size_of_fixedWidth_degrees {A B : Language Bool} {a b d C R M : ℕ}
    (width : ℕ → ℕ) (F : ∀ n, (Fin n → Bool) → Fin (width n) → Bool)
    (hF : ∀ n, complexity interpretation (F n) ≤ R * (n + 1) ^ a)
    (hw : ∀ n, width n + 1 ≤ M * (n + 1) ^ b)
    (hcorrect : ∀ n (x : Fin n → Bool), List.ofFn x ∈ A ↔ List.ofFn (F n x) ∈ B)
    (hB : B ∈ SIZE (fun n => C * (n + 1) ^ d)) :
    A ∈ SIZE (fun n => (R + C * M ^ d) * (n + 1) ^ max a (b * d)) := by
  refine SIZE_mono (fun n => ?_) (fixedWidth_size_of_reduction width _ _ F hF hcorrect hB)
  let x := n + 1
  let e := max a (b * d)
  have hx : 0 < x := Nat.succ_pos n
  have hpow : (width n + 1) ^ d ≤ M ^ d * x ^ (b * d) := by
    rw [pow_mul, ← mul_pow]
    exact Nat.pow_le_pow_left (hw n) _
  change R * x ^ a + C * (width n + 1) ^ d ≤ (R + C * M ^ d) * x ^ e
  calc
    _ ≤ R * x ^ e + C * (M ^ d * x ^ e) := Nat.add_le_add
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (le_max_left _ _)))
      (Nat.mul_le_mul_left _ (hpow.trans
        (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hx (le_max_right _ _)))))
    _ = _ := by ring

/-- Common circuit reduction degrees transfer a family of source circuit exclusions. -/
theorem outside_PPoly_of_common_circuitReductionDegrees {B : Language Bool} {a b : ℕ}
    (family : ∀ k, ∃ L : Language Bool,
      (∀ c, L ∉ SIZE (fun n => c * (n + 1) ^ k)) ∧ CircuitReductionDegrees L B a b) :
    B ∉ PPoly := by
  intro bounded
  obtain ⟨d, hC⟩ := mem_PPoly_iff_exists_mem_SIZE.mp bounded
  obtain ⟨L, hard, reduction⟩ := family (max a (b * (d + 1)))
  exact (Nat.lt_irrefl _) (reduction_degree_tradeoff hard reduction hC)

end Cslib.Circuits.Boolean
