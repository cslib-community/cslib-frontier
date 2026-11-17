/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Parsing
public import CslibFrontier.Computability.Complexity.Problems.SAT
import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Hardness
import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Membership
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Classes.PH.Closure

/-!
# Quantified SAT is complete at every positive level of the polynomial hierarchy

`SigmaSAT i` and `PiSAT i` are total languages on the existing `QBF ℕ` syntax, with the
existing binary-variable prefix-token encoding `encQBF`. Polynomial-time prefix extraction
reduces membership to the grouped formula verifier. For hardness, every native alternating
verifier is compiled to a tableau with its auxiliary variables merged into the final block.
Negating the matrix and swapping every quantifier gives the dual result.

## Main results

* `SigmaSAT_sigmaPComplete`: `ΣᵢSAT` is `Σᵢᵖ`-complete, for every `i ≥ 1`.
* `PiSAT_piPComplete`: `ΠᵢSAT` is `Πᵢᵖ`-complete, for every `i ≥ 1`.
* `SAT_karp_equivalent_SigmaSAT_one`: SAT and 1QBF reduce to each other.

These are [Arora–Barak, draft Example 5.9, display (1), printed pp. 94–95,
and Exercise 5 §1, printed p. 100][AroraBarak07] and [Goldreich, Exercises 3.7 and 3.10(1),
printed pp. 133 and 135][Goldreich2007DraftR2], in the native binary multitape model.
Hardness ranges over every source type and every explicit source encoding.
The matrix is an arbitrary quantifier-free Boolean formula. No CNF/DNF restriction is imposed.
-/

public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM QuantifiedSAT

/-- Existential-first bounded quantified SAT is in its native hierarchy level, including zero. -/
theorem SigmaSAT_mem_SigmaP (i : ℕ) : SigmaSAT i ∈ SigmaP i encQBF := by
  apply inter_mem_SigmaP
  · exact SigmaP_mono (Nat.zero_le i) (P_subset_SigmaP_zero
      ⟨PrenexQBF.startsCorrectly true, PrenexQBF.startsCorrectly_polyTime true,
        fun _ => Iff.rfl⟩)
  · exact PolyTimeReducible.mem_SigmaP
      ⟨PrenexQBF.parse true i, PrenexQBF.parse_polyTime true i, fun _ => Iff.rfl⟩
      (PrenexQBF.mem_SigmaP i)

/-- Universal-first bounded quantified SAT is in its native hierarchy level, including zero. -/
theorem PiSAT_mem_PiP (i : ℕ) : PiSAT i ∈ PiP i encQBF := by
  apply inter_mem_PiP
  · apply PiP_mono (Nat.zero_le i)
    change {φ | PrenexQBF.startsCorrectly false φ = true} ∈ PiP 0 encQBF
    rw [PiP_zero]
    exact ⟨PrenexQBF.startsCorrectly false, PrenexQBF.startsCorrectly_polyTime false,
      fun _ => Iff.rfl⟩
  · exact PolyTimeReducible.mem_PiP
      ⟨PrenexQBF.parse false i, PrenexQBF.parse_polyTime false i, fun _ => Iff.rfl⟩
      (PrenexQBF.mem_PiP i)

/-- Every `Σᵢᵖ` problem, with any instance encoding, reduces to `ΣᵢSAT` for `i ≥ 1`. -/
theorem SigmaSAT_sigmaPHard {i : ℕ} (hi : 1 ≤ i) : SigmaPHard i encQBF (SigmaSAT i) := by
  intro α enc A hA
  obtain ⟨f, hf, hspec⟩ := exists_tableauReduction hi hA
  refine ⟨fun a => (f a).formula true,
    PrenexQBF.formula_polyTime hf true i (fun a => (hspec a).1.1), fun a => ?_⟩
  have hne : (f a).blocks ≠ [] := by
    intro heq
    have := (hspec a).1.1
    simp only [heq, List.length_nil] at this
    omega
  change a ∈ A ↔ PrenexQBF.startsCorrectly true ((f a).formula true) = true ∧
    PrenexQBF.parse true i ((f a).formula true) ∈ PrenexQBF.SigmaSAT i
  rw [and_iff_right (PrenexQBF.startsCorrectly_formula (f a) true hne (hspec a).2.1)]
  have hp := PrenexQBF.parse_formula true (f a) (hspec a).1.2.1 (hspec a).2.1
  rw [(hspec a).1.1] at hp
  rw [hp]
  exact (hspec a).2.2.trans (and_iff_right (hspec a).1).symm

/-- Every `Πᵢᵖ` problem, with any instance encoding, reduces to `ΠᵢSAT` for `i ≥ 1`. -/
theorem PiSAT_piPHard {i : ℕ} (hi : 1 ≤ i) : PiPHard i encQBF (PiSAT i) := by
  intro α enc A hA
  obtain ⟨f, hf, hspec⟩ := exists_tableauReduction hi (compl_mem_SigmaP_of_mem_PiP hA)
  let g (a : α) : PrenexQBF := ⟨(f a).blocks, (f a).matrix.not⟩
  have hg : ComputableInPolyTime g enc encPrenexQBF := by
    unfold g
    have hn := TQBF.computableInPolyTime_not (encPrenexQBF_matrix_polyTime hf)
    fun_prop
  have hwell (a : α) : (g a).WellFormed i :=
    ⟨(hspec a).1.1, QBF.quantifierFree_not.mpr (hspec a).1.2.1, (hspec a).1.2.2⟩
  refine ⟨fun a => (g a).formula false,
    PrenexQBF.formula_polyTime hg false i (fun a => (hwell a).1), fun a => ?_⟩
  have hne : (g a).blocks ≠ [] := by
    intro heq
    have := (hwell a).1
    simp only [heq, List.length_nil] at this
    omega
  change a ∈ A ↔ PrenexQBF.startsCorrectly false ((g a).formula false) = true ∧
    PrenexQBF.parse false i ((g a).formula false) ∈ PrenexQBF.PiSAT i
  rw [and_iff_right (PrenexQBF.startsCorrectly_formula (g a) false hne (hspec a).2.1)]
  have hp := PrenexQBF.parse_formula false (g a) (hwell a).2.1 (hspec a).2.1
  rw [(hwell a).1] at hp
  rw [hp]
  change a ∈ A ↔ (g a).WellFormed i ∧ ((g a).formula false).eval (fun _ => false) = true
  rw [and_iff_right (hwell a)]
  have hd := QBF.eval_blocks_dual true (f a).blocks (f a).matrix (fun _ => false)
  change ((g a).formula false).eval (fun _ => false) =
    !((f a).formula true).eval (fun _ => false) at hd
  rw [hd]
  have heq := (hspec a).2.2
  simpa only [Set.mem_compl_iff, Bool.not_eq_true', ← Bool.not_eq_true, not_not] using
    not_congr heq

/-- **`ΣᵢSAT` is `Σᵢᵖ`-complete for every positive level**, under polynomial-time many-one
reductions, with the existing `QBF ℕ` syntax and `encQBF` encoding.
[Arora–Barak, Exercise 5 §1][AroraBarak07]; [Goldreich, Exercise 3.7][Goldreich2007DraftR2]. -/
theorem SigmaSAT_sigmaPComplete {i : ℕ} (hi : 1 ≤ i) :
    SigmaPComplete i encQBF (SigmaSAT i) :=
  ⟨SigmaSAT_mem_SigmaP i, SigmaSAT_sigmaPHard hi⟩

/-- **`ΠᵢSAT` is `Πᵢᵖ`-complete for every positive level**, with the same explicit encoding
and unrestricted quantifier-free matrix as `SigmaSAT_sigmaPComplete`.
[Arora–Barak, Example 5.9 and Exercise 5 §1][AroraBarak07]. -/
theorem PiSAT_piPComplete {i : ℕ} (hi : 1 ≤ i) : PiPComplete i encQBF (PiSAT i) :=
  ⟨PiSAT_mem_PiP i, PiSAT_piPHard hi⟩

/-- **SAT and 1QBF are Karp-equivalent**, [Goldreich, Exercise 3.10(1)][Goldreich2007DraftR2].
SAT uses its existing CNF encoding and 1QBF the existing QBF encoding. -/
theorem SAT_karp_equivalent_SigmaSAT_one :
    PolyTimeReducible encCNF encQBF SAT (SigmaSAT 1) ∧
      PolyTimeReducible encQBF encCNF (SigmaSAT 1) SAT :=
  ⟨SigmaSAT_sigmaPHard (by omega) encCNF SAT
      (by simpa only [SigmaP_one] using CookLevin.SAT_npComplete.1),
    CookLevin.SAT_npHard encQBF (SigmaSAT 1)
      (by simpa only [SigmaP_one] using SigmaSAT_mem_SigmaP 1)⟩

end Cslib.Complexity
