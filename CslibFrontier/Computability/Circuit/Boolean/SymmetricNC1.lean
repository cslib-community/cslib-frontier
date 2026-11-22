/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CarrySave
import CslibFrontier.Foundations.Data.Nat.PowClog

/-!
# Symmetric functions in logarithmic depth

A Boolean function of `k` bits is *symmetric* when it depends only on the number of true bits,
that is, it is `x ↦ g (weight x)` for some `g : ℕ → Bool`. Such a function has a De Morgan circuit
of fan-in two with `O(k²)` gates and depth `O(log k)` (`symmetricDeMorganCircuit`): the carry-save
circuit `weightCircuit k` writes the weight in binary with `w = ⌈log₂ (k + 1)⌉` bits in depth
`O(log k)`, and the disjunction of the minterms of the accepted weights `j ≤ k` reads it, in depth
`1 + ⌈log₂ w⌉ + ⌈log₂ (k + 1)⌉` [Vollmer, Chapter 4][Vollmer1999].

`MOD_q` gates are symmetric, so this simulates them in logarithmic depth
(`Cslib.Circuits.Boolean.Unbounded.modMultDeMorganCircuit`), the step from `ACC⁰` to `NC¹`.

## Main definitions

* `Cslib.Circuits.Boolean.symmetricDeMorganCircuit`: a De Morgan circuit for `x ↦ g (weight x)`.

## Main results

* `Cslib.Circuits.Boolean.computes_symmetricDeMorganCircuit`: it computes `x ↦ g (weight x)`.
* `Cslib.Circuits.Boolean.size_symmetricDeMorganCircuit_le`: at most `70 (k + 1)²` gates.
* `Cslib.Circuits.Boolean.depth_symmetricDeMorganCircuit_le`: depth at most
  `2 + 21 ⌈log₂ (k + 1)⌉`.

## References

* [H. Vollmer, *Introduction to Circuit Complexity*][Vollmer1999]
-/

public section

namespace Cslib.Circuits.Boolean

/-- The disjunction of the minterms, over `⌈log₂ (k + 1)⌉` bits, of the weights `j ≤ k` with
`g j`. On the binary weight of a string of `k` bits it computes `g` of the weight. -/
private def weightFormula (k : ℕ) (g : ℕ → Bool) : Formula signature (Nat.clog 2 (k + 1)) :=
  Formula.orList (((List.finRange (k + 1)).filter fun j : Fin (k + 1) => g j).map fun j =>
    Formula.minterm ((BitString.equivFin (Nat.clog 2 (k + 1))).symm
      (Fin.castLE (Nat.le_pow_clog one_lt_two (k + 1)) j)))

private theorem depth_weightFormula_le (k : ℕ) (g : ℕ → Bool) :
    (weightFormula k g).depth ≤ 1 + 2 * Nat.clog 2 (k + 1) := by
  have h := Formula.depthWith_orList_le (cost := 1) (d := 1 + Nat.clog 2 (Nat.clog 2 (k + 1)))
    (l := ((List.finRange (k + 1)).filter fun j : Fin (k + 1) => g j).map fun j =>
      Formula.minterm ((BitString.equivFin (Nat.clog 2 (k + 1))).symm
        (Fin.castLE (Nat.le_pow_clog one_lt_two (k + 1)) j)))
    (by
      simp only [List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂,
        Formula.depthWith_one]
      exact fun _ _ => Formula.depth_minterm_le _)
    (fun _ => by simp)
  simp only [Formula.depthWith_one, Pi.one_apply, one_mul, List.length_map] at h
  have hlen : Nat.clog 2 ((List.finRange (k + 1)).filter fun j : Fin (k + 1) => g j).length ≤
      Nat.clog 2 (k + 1) :=
    Nat.clog_mono_right 2 ((List.length_filter_le _ _).trans (List.length_finRange).le)
  have hc : Nat.clog 2 (Nat.clog 2 (k + 1)) ≤ Nat.clog 2 (k + 1) :=
    (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self.le
  rw [weightFormula]
  omega

/-- **Symmetric functions in logarithmic depth**: a De Morgan circuit of fan-in two computing
`x ↦ g (weight x)` on `k` bits. It writes the weight in binary (`weightCircuit k`) and tests it
against the accepted weights `j ≤ k` by a balanced disjunction of minterms. -/
def symmetricDeMorganCircuit (k : ℕ) (g : ℕ → Bool) : Circuit signature k 1 :=
  (weightFormula k g).toCircuit.comp (weightCircuit k)

/-- `symmetricDeMorganCircuit k g` computes `g` of the number of true bits. -/
theorem computes_symmetricDeMorganCircuit (k : ℕ) (g : ℕ → Bool) :
    (symmetricDeMorganCircuit k g).Computes interpretation
      (single fun x => g (BitString.weight x)) := by
  intro x
  funext o
  have hb := val_eval_weightCircuit x
  rw [symmetricDeMorganCircuit, Circuit.eval_comp, Formula.eval_toCircuit, weightFormula,
    Formula.eval_orList, single_apply, Bool.eq_iff_iff, List.any_eq_true]
  simp only [List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    exists_exists_and_eq_and, Formula.eval_minterm, decide_eq_true_eq]
  constructor
  · rintro ⟨j, hj, hbj⟩
    rw [hbj, Equiv.apply_symm_apply, Fin.val_castLE] at hb
    rw [← hb]
    exact hj
  · intro hg
    refine ⟨⟨BitString.weight x, Nat.lt_succ_of_le (BitString.weight_le_length x)⟩, hg, ?_⟩
    rw [Equiv.eq_symm_apply]
    exact Fin.ext hb

/-- `symmetricDeMorganCircuit k g` has at most `70 (k + 1)²` gates. -/
theorem size_symmetricDeMorganCircuit_le (k : ℕ) (g : ℕ → Bool) :
    (symmetricDeMorganCircuit k g).size ≤ 70 * (k + 1) ^ 2 := by
  have hck : Nat.clog 2 (k + 1) ≤ k := (Nat.clog_le_iff_le_pow one_lt_two).2 Nat.lt_two_pow_self
  have hw := size_weightCircuit_le k
  have hF : (weightFormula k g).size < 2 ^ (1 + 2 * Nat.clog 2 (k + 1)) :=
    (Formula.size_lt_pow_depth (Formula.fanInAtMost_of_arity_le arity_le_two _) le_rfl).trans_le
      (Nat.pow_le_pow_right two_pos (depth_weightFormula_le k g))
  have hpow : 2 ^ Nat.clog 2 (k + 1) ≤ 2 * k + 1 := by
    have := Nat.pow_clog_lt_mul one_lt_two (n := k + 1) (by omega)
    omega
  have hF' : 2 ^ (1 + 2 * Nat.clog 2 (k + 1)) ≤ 2 * (2 * k + 1) ^ 2 := by
    rw [pow_add, pow_mul', pow_one]
    gcongr
  have hmax : max 1 k ≤ k + 1 := max_le (by omega) (by omega)
  rw [symmetricDeMorganCircuit, Circuit.size_comp, Formula.size_toCircuit]
  have h1 : k * (40 * Nat.clog 2 (k + 1)) ≤ 40 * k * k := by nlinarith
  have h2 : Nat.clog 2 (k + 1) * (20 * Nat.clog 2 (k + 1) + 1) ≤ k * (20 * k + 1) := by gcongr
  nlinarith

/-- `symmetricDeMorganCircuit k g` has depth at most `2 + 21 ⌈log₂ (k + 1)⌉`. -/
theorem depth_symmetricDeMorganCircuit_le (k : ℕ) (g : ℕ → Bool) :
    (symmetricDeMorganCircuit k g).depth ≤ 2 + 21 * Nat.clog 2 (k + 1) := by
  refine (Circuit.depth_comp_le _ _).trans ?_
  have h1 := (Formula.depth_toCircuit_le (weightFormula k g)).trans (depth_weightFormula_le k g)
  have h2 := depth_weightCircuit_le k
  omega

end Cslib.Circuits.Boolean
