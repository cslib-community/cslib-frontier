/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.BPP.RandomizedReduction
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Operators
public import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Games
public import CslibFrontier.Computability.Complexity.Problems.ThreeSAT
public import CslibFrontier.Computability.Complexity.Classes.PH
import CslibFrontier.Computability.Complexity.Classes.ArthurMerlin.Collapse

/-!
# BP·NP as the languages randomly reducible to 3SAT

[Arora and Barak, Definition 7.20][AroraBarak07] (printed p. 129 / PDF p. 145) defines
`BP·NP = {L : L ≤_r 3SAT}`, by analogy with `NP = {L : L ≤_p 3SAT}`. With the randomized
reductions of Definition 7.19 (`BPReducible`) and the library's `ThreeSAT` on `encCNF`, this set
is the bounded-error operator applied to `NP` (`setOf_bpReducible_ThreeSAT`): a randomized
reduction to 3SAT is a polynomial-time map of the instance and the random string, and the
preimage of 3SAT under such a map is an NP language; conversely, an NP language of pairs reduces
to 3SAT by the Cook–Levin theorem. This connects the source definition with the native operator
results `BPOp_NP` (`BP·NP = AM`) and the collapse `PH_eq_SigmaP_two_of_coNP_subset_AM`.

## Main results

* `Cslib.Complexity.setOf_bpReducible_ThreeSAT`: `{L | L ≤_r 3SAT} = BPOp (NP …)`.
* `Cslib.Complexity.AMk_two_eq_setOf_bpReducible_ThreeSAT`: **Arora–Barak, Exercise 8.5**,
  `AM[2] = BP·NP` with Definition 7.20.
* `Cslib.Complexity.coNP_subset_AM_of_bpReducible_compl_ThreeSAT`,
  `Cslib.Complexity.PH_eq_SigmaP_three_of_bpReducible_compl_ThreeSAT`: **Arora–Barak,
  Exercise 7.6**, if the complement of 3SAT is in `BP·NP` then `PH = Σ₃`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak07], Definition
  7.20 and Exercises 7.6 and 8.5.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **Definition 7.20 of [Arora and Barak][AroraBarak07] is the bounded-error operator on `NP`**:
the languages that reduce to `ThreeSAT` under randomized polynomial-time reductions are exactly
`BPOp enc (NP (encPair enc encBits))`. -/
theorem setOf_bpReducible_ThreeSAT :
    {L : Set α | BPReducible enc encCNF L ThreeSAT} = BPOp enc (NP (encPair enc encBits)) := by
  classical
  ext L
  simp only [Set.mem_ofPred_eq, bpReducible_iff, mem_BPOp]
  constructor
  · rintro ⟨p, f, hf, hdec⟩
    exact ⟨p, {x | f x ∈ ThreeSAT},
      PolyTimeReducible.mem_NP ⟨f, hf, fun _ => Iff.rfl⟩ ThreeSAT_npComplete.1, hdec⟩
  · rintro ⟨p, L', hL', hdec⟩
    obtain ⟨g, hg, hgL⟩ := ThreeSAT_npHard _ _ hL'
    refine ⟨p, g, hg, ?_⟩
    have hV : (fun x => decide (g x ∈ ThreeSAT)) = fun x => decide (x ∈ L') :=
      funext fun x => decide_eq_decide.2 (hgL x).symm
    rw [hV]
    exact hdec

/-- **Arora–Barak, Exercise 8.5** [AroraBarak07]: `AM[2] = BP·NP`, with `BP·NP` as in
Definition 7.20, the languages that reduce to `ThreeSAT` under randomized polynomial-time
reductions. -/
theorem AMk_two_eq_setOf_bpReducible_ThreeSAT :
    AMk enc 2 = {L : Set α | BPReducible enc encCNF L ThreeSAT} := by
  rw [AMk_two, setOf_bpReducible_ThreeSAT, BPOp_NP]

/-- If the complement of `ThreeSAT` reduces to `ThreeSAT` under randomized polynomial-time
reductions, then `coNP ⊆ AM` for every encoding. -/
theorem coNP_subset_AM_of_bpReducible_compl_ThreeSAT
    (h : BPReducible encCNF encCNF ThreeSATᶜ ThreeSAT) {β : Type} (encB : β ↪ List Bool) :
    coNP encB ⊆ AM encB := by
  have hAM : ThreeSATᶜ ∈ AM encCNF := by
    rw [← AMk_two, AMk_two_eq_setOf_bpReducible_ThreeSAT]
    exact h
  exact fun L hL => (NPHard.compl ThreeSAT_npHard encB L hL).mem_AM hAM

/-- **Arora–Barak, Exercise 7.6** [AroraBarak07]: if the complement of 3SAT is in `BP·NP`
(Definition 7.20), then the polynomial hierarchy collapses to `Σ₃`. The proof gives the stronger
collapse to `Σ₂` (`PH_eq_SigmaP_two_of_coNP_subset_AM`). -/
theorem PH_eq_SigmaP_three_of_bpReducible_compl_ThreeSAT
    (h : BPReducible encCNF encCNF ThreeSATᶜ ThreeSAT) : PH enc = SigmaP 3 enc := by
  have h2 := PH_eq_SigmaP_two_of_coNP_subset_AM (enc := enc)
    (coNP_subset_AM_of_bpReducible_compl_ThreeSAT h)
  exact (SigmaP_subset_PH 3).antisymm' (h2 ▸ SigmaP_subset_SigmaP_succ 2)

end Cslib.Complexity
