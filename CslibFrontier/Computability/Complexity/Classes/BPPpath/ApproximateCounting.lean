/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPPpath
public import CslibFrontier.Computability.Complexity.Classes.Operators
public import CslibFrontier.Computability.Complexity.Classes.Oracle
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.SharpP.ApproximateCounting
import CslibFrontier.Foundations.Data.Finset.Density
import CslibFrontier.Foundations.Probability.ProductDensity
import CslibFrontier.Tactic.PolyTime

/-!
# Deciding BPPpath with a SAT oracle

Theorem 3.11(2) of the preprint by [Han, Hemaspaandra and Thierauf][HanHemaspaandraThierauf1997]
puts bounded-error path-count computation in bounded-error polynomial time with an NP oracle.
We use the native verifier-count definition of `BPPpath` and the encoded SAT oracle. Applying
the bounded-error operator to `PWithOracle` supplies a polynomial-length string of fair bits
to the oracle decider.

The proof uses the approximate-counting approach mentioned before Definition 3.8 of the authors'
preprint. Two independent Stockmeyer runs estimate the accepting and rejecting path counts. A
relative error of at most one quarter preserves their strict order under the factor-three gap,
including when the smaller count is zero.
-/

public section

namespace Cslib.Complexity

open Finset Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

private theorem exists_quarter_estimate {f : α → ℕ} (hf : f ∈ SharpP enc) :
    ∃ (p : Polynomial ℕ) (E : α × List Bool → ℕ),
      ComputableInPolyTimeWithOracle (encCNF '' SAT) E (encPair enc encBits) encNat ∧
      ∀ a, 7 / 8 ≤ dens {r : BitString (p.eval (enc a).length) |
        |(E (a, List.ofFn r) : ℚ) - f a| ≤ f a / 4} := by
  classical
  -- The framed one-bit prefix makes the failure bound at most 1/8 even at length zero.
  have hpad := SharpP.comp_mem hf (ComputableInPolyTime.snd encBits enc)
  obtain ⟨p, E, hE, hbad⟩ := SharpP.exists_approxCount_SAT hpad 4 (by simp)
  let pad (a : α) : List Bool × α := ([true], a)
  have hlen (a : α) : (encPair encBits enc (pad a)).length = 3 + (enc a).length := by
    simp [pad]
    omega
  let L : Polynomial ℕ := p.comp (3 + Polynomial.X)
  have hL (a : α) : L.eval (enc a).length = p.eval (encPair encBits enc (pad a)).length := by
    rw [hlen]
    simp [L, Polynomial.eval_comp]
  refine ⟨L, fun z => E (pad z.1, z.2), hE.preprocess ?_, fun a => ?_⟩
  · exact (((ComputableInPolyTime.const ([true] : List Bool)).prod
      (ComputableInPolyTime.fst enc encBits)).prod (.snd enc encBits))
  · rw [hL]
    have hb := hbad (pad a)
    simp only [Function.comp_apply, pad, Polynomial.eval_ofNat, Nat.cast_ofNat] at hb
    have hpow : (8 : ℚ≥0) ≤ 2 ^ (encPair encBits enc (pad a)).length := by
      calc
        8 = (2 : ℚ≥0) ^ 3 := by decide
        _ ≤ _ := pow_le_pow_right₀ (by decide) (by rw [hlen]; omega)
    have hfailure := hb.trans (inv_anti₀ (by norm_num : (0 : ℚ≥0) < 8) hpow)
    have hsum := dens_filter_add_dens_filter_not_eq_dens
      (s := (univ : Finset (BitString (p.eval (encPair encBits enc (pad a)).length))))
      (fun r => |(E (pad a, List.ofFn r) : ℚ) - f a| ≤ f a / 4)
    simp only [not_le, dens_univ] at hsum
    apply le_of_add_le_add_right
    calc
      7 / 8 + (8 : ℚ≥0)⁻¹ = 1 := by norm_num
      _ ≤ _ := hsum.symm.le.trans (add_le_add_right hfailure _)

/-- **BPPpath is contained in BPP with a SAT oracle**
(Theorem 3.11(2) of the preprint by [Han, Hemaspaandra and Thierauf][HanHemaspaandraThierauf1997]).
The encoded SAT language is NP-complete. On every encoded input the comparison of two
SAT-oracle estimates agrees with membership with probability at least two thirds. -/
theorem BPPpath_subset_BPOp_PWithOracle_SAT :
    BPPpath enc ⊆ BPOp enc (PWithOracle (encCNF '' SAT) (encPair enc encBits)) := by
  classical
  rintro A ⟨acc, hacc, rej, hrej, hgap⟩
  obtain ⟨p, E, hE, hp⟩ := exists_quarter_estimate hacc
  obtain ⟨q, F, hF, hq⟩ := exists_quarter_estimate hrej
  let k (a : α) := p.eval (enc a).length
  let accept (z : α × List Bool) :=
    decide (F (z.1, z.2.drop (k z.1)) < E (z.1, z.2.take (k z.1)))
  have hk : ComputableInPolyTime (fun z : α × List Bool => k z.1) (encPair enc encBits)
      encUnary := by dsimp [k]; fun_prop
  have hV : ComputableInPolyTimeWithOracle (encCNF '' SAT) accept (encPair enc encBits)
      encBool := by
    have hleft := hF.preprocess ((ComputableInPolyTime.fst enc encBits).prod
      (ComputableInPolyTime.bitsDropWithInput (.snd enc encBits) hk))
    have hright := hE.preprocess ((ComputableInPolyTime.fst enc encBits).prod
      (ComputableInPolyTime.bitsTakeWithInput (.snd enc encBits) hk))
    exact (hleft.prod hright).map ComputableInPolyTime.binary_lt
  refine ⟨p + q, {z | accept z = true}, ⟨accept, hV, fun _ => Iff.rfl⟩, fun a => ?_⟩
  let n := (enc a).length
  let good (g : ℕ) (e : ℕ) := |(e : ℚ) - g| ≤ g / 4
  let correct (r : List Bool) := accept (a, r) = decide (a ∈ A)
  have hgood : (2 / 3 : ℚ≥0) ≤ dens {r : BitString (p.eval n + q.eval n) |
      correct (List.ofFn r)} := by
    rw [← Fintype.dens_filter_comp_equiv (Fin.appendEquiv (p.eval n) (q.eval n))
      (fun r => correct (List.ofFn r))]
    calc
      _ ≤ (7 / 8 : ℚ≥0) * (7 / 8) := by
        exact_mod_cast (by norm_num : (2 / 3 : ℚ) ≤ 7 / 8 * (7 / 8))
      _ ≤ dens {r : BitString (p.eval n) | good (acc a) (E (a, List.ofFn r))} *
          dens {r : BitString (q.eval n) | good (rej a) (F (a, List.ofFn r))} :=
        mul_le_mul' (hp a) (hq a)
      _ ≤ _ := by
        rw [← Probability.dens_filter_fst_and_snd]
        apply dens_le_dens
        rintro ⟨u, v⟩ huv
        simp only [mem_filter, mem_univ, true_and] at huv ⊢
        obtain ⟨hu, hv⟩ := huv
        simp only [good, abs_le] at hu hv
        obtain ⟨hpos, hy, hn⟩ := hgap a
        have happ : List.ofFn (Fin.appendEquiv _ _ (u, v)) = List.ofFn u ++ List.ofFn v :=
          List.ofFn_fin_append u v
        simp only [correct, accept, happ]
        have hku : k a = (List.ofFn u).length := by simp [k, n]
        rw [hku, List.drop_left, List.take_left]
        by_cases ha : a ∈ A
        · simp only [ha, decide_true, decide_eq_true_eq]
          have h₁ : (0 : ℚ) < acc a + rej a := by exact_mod_cast hpos
          have h₂ : (3 : ℚ) * rej a ≤ acc a := by exact_mod_cast hy ha
          exact_mod_cast (show (F (a, List.ofFn v) : ℚ) < E (a, List.ofFn u) by linarith)
        · simp only [ha, decide_false, decide_eq_false_iff_not, not_lt]
          have h₂ : (3 : ℚ) * acc a ≤ rej a := by exact_mod_cast hn ha
          exact_mod_cast (show (E (a, List.ofFn u) : ℚ) ≤ F (a, List.ofFn v) by linarith)
  have hcard : 2 * 2 ^ ((p + q).eval n) ≤
      3 * #{r : BitString ((p + q).eval n) | correct (List.ofFn r)} := by
    let count (m : ℕ) := #{r : BitString m | correct (List.ofFn r)}
    change 2 * 2 ^ ((p + q).eval n) ≤ 3 * count ((p + q).eval n)
    rw [Polynomial.eval_add]
    rw [dens_eq_card_div_card, BitString.card, div_le_div_iff₀ (by norm_num)
      (by positivity)] at hgood
    rw [Nat.mul_comm 3]
    exact_mod_cast hgood
  constructor <;> intro ha
  · change a ∈ A at ha
    simpa [BoundedErrorAt, correct, ha, n] using hcard
  · change a ∉ A at ha
    simpa [BoundedErrorAt, correct, ha, n] using hcard

end Cslib.Complexity
