/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.QUADEQ
public import CslibFrontier.Computability.Complexity.Classes.Promise.Reduction
public import CslibFrontier.Computability.PolyTime.BitString.SmallBias
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# The gap problem of quadratic equations is NP-hard

Goldreich's Exercise 10.6 [Goldreich2007DraftR5] shows that a natural gap problem is NP-hard
without the PCP theorem: given a system of quadratic equations over `𝔽₂`, tell satisfiable systems
apart from systems in which every assignment violates at least a third of the equations, or more
generally at least a `1/2 - ε` fraction of them. `GapQUADEQ δ` is this promise problem with
violation threshold `δ`, over the instances and encoding of `QUADEQ`.

The proof is the amplifying self-reduction of the guideline. A system `F` of `m` equations is
mapped to the system `QUADEQ.amplify k F` with one equation for each mask `r` of the uniform
`1/k`-biased family `Cslib.BitString.poweringMasks m k`: the linear combination of the equations
of `F` that `r` selects. An assignment satisfying `F` satisfies every combination. An assignment
violating some equation of `F` has a nonzero violation vector `v ∈ 𝔽₂^m`, and violates the
combination of `r` exactly when `⟨r, v⟩ = 1`; by the bias bound this happens for at least a
`(1 - 1/k)/2` fraction of the masks (`Cslib.BitString.IsSmallBias.le_card_filter_parityOn`).
For a constant `k ≥ 1/(1 - 2δ)` the map is a polynomial-time reduction from `QUADEQ`, which is
NP-hard (`Cslib.Complexity.QUADEQ_npHard`), to `GapQUADEQ δ`.

## Source mapping

[Goldreich2007DraftR5], Exercise 10.6, printed pp. 496–497 (PDF pp. 114–115). Yes-instances are
the satisfiable systems, as in the source. No-instances are the systems in which every assignment
violates at least a `δ` fraction of the equations, counted with multiplicity. The source's
thresholds are `δ = 1/3` and `δ = 1/2 - ε`; `GapQUADEQ_npHard` proves every `0 < δ < 1/2`. The
empty system and thresholds `δ ≤ 0` give no no-instances, as in
`Cslib.Complexity.PromiseProblem.gapMin`, so that the two sets are disjoint. Goldreich's bias
(§8.5.2, equations (8.18)–(8.19)) is the absolute character expectation, as in
`Cslib.BitString.IsSmallBias`. Character bias `ε` gives the stronger violation fraction
`(1 - ε) / 2`, hence also the source's `1/2 - ε`; the guideline's bias `1/6` is a sufficient,
conservative choice for violation fraction `1/3`.
Hardness is under polynomial-time Karp reductions of promise problems
(`Cslib.Complexity.PromiseProblem.NPHard`), and membership is in promise-NP, which together are
the source's NP-completeness.

## Main definitions

* `Cslib.Complexity.GapQUADEQ`: the gap problem with violation threshold `δ`.
* `Cslib.Complexity.QUADEQ.amplify`: the amplifying self-reduction.

## Main results

* `Cslib.Complexity.QUADEQ.holds_amplify`, `Cslib.Complexity.QUADEQ.le_countViolated_amplify`:
  completeness and the violation gap of the amplified system.
* `Cslib.Complexity.QUADEQ.computableInPolyTime_amplify`: the reduction runs in polynomial time,
  including the construction of the small-bias family.
* `Cslib.Complexity.polyTimeReducible_QUADEQ_GapQUADEQ`: the Karp reduction.
* `Cslib.Complexity.GapQUADEQ_npHard`, `Cslib.Complexity.GapQUADEQ_mem_PromiseNP`: the gap
  problem is NP-hard and in promise-NP, for every `0 < δ < 1/2`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft][Goldreich2007DraftR5]
-/

@[expose] public section

namespace Cslib.Complexity

open Cslib.Logic.PL Turing.MultiTapeTM PromiseProblem
open scoped Finset

/-- **The gap problem of quadratic equations over `𝔽₂`** with violation threshold `δ`
[Goldreich2007DraftR5, Exercise 10.6]: yes-instances are the satisfiable systems (`QUADEQ`),
no-instances the systems in which every assignment violates at least a `δ` fraction of the
equations. For `δ ≤ 0` there are no no-instances, and the empty system is never one. -/
def GapQUADEQ (δ : ℝ) : PromiseProblem (QuadSystem ℕ) where
  yes := QUADEQ
  no := {F | 0 < δ ∧ ∀ a : ℕ → Bool, δ ≤ (F.countViolated a : ℝ) / F.length}
  disjoint := Set.disjoint_left.2 fun F ⟨a, ha⟩ ⟨hδ, h⟩ => by
    have h0 : F.countViolated a = 0 :=
      List.countP_eq_zero.2 fun e he => by simpa using ha e he
    have := h a
    rw [h0, Nat.cast_zero, zero_div] at this
    linarith

namespace QUADEQ

/-- **The amplifying self-reduction**: one equation for each mask of the uniform `1/k`-biased
family `Cslib.BitString.poweringMasks` of width the number of equations, namely the linear
combination of the equations the mask selects. -/
def amplify (k : ℕ) (F : QuadSystem ℕ) : QuadSystem ℕ :=
  (BitString.poweringMasks F.length k).map F.linearCombination

/-- An assignment satisfying a system satisfies its amplification. -/
theorem holds_amplify {k : ℕ} {F : QuadSystem ℕ} {a : ℕ → Bool} (h : F.Holds a) :
    (amplify k F).Holds a := by
  simp only [amplify, QuadSystem.Holds, List.mem_map]
  rintro _ ⟨r, -, rfl⟩
  rw [QuadSystem.holds_linearCombination_iff, Finset.card_eq_zero.2
    (Finset.filter_eq_empty_iff.2 fun i _ hi => hi.1 (h _ (List.getElem_mem _)))]
  exact ⟨0, rfl⟩

/-- **The violation gap**: an assignment violating some equation of `F` violates at least a
`(1 - 1/k) / 2` fraction of the equations of `amplify k F`. -/
theorem le_countViolated_amplify {k : ℕ} (hk : 0 < k) {F : QuadSystem ℕ} {a : ℕ → Bool}
    (h : ¬F.Holds a) :
    (1 - 1 / (k : ℝ)) / 2 ≤
      ((amplify k F).countViolated a : ℝ) / (amplify k F).length := by
  let S : Finset (Fin F.length) := {i | ¬F[i].Holds a}
  have hS : S.Nonempty := by
    obtain ⟨e, he, hea⟩ : ∃ e ∈ F, ¬e.Holds a := by simpa [QuadSystem.Holds] using h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact ⟨⟨i, hi⟩, by simpa [S] using hea⟩
  have hviol (r : List Bool) :
      (¬(F.linearCombination r).Holds a) ↔ parityOn S (BitString.ofList _ r) = true := by
    rw [QuadSystem.holds_linearCombination_iff, parityOn, Finset.filter_filter,
      Nat.not_even_iff, decide_eq_true_iff]
    rfl
  have hcount : (amplify k F).countViolated a =
      #{j : Fin (BitString.poweringMasks F.length k).length |
        parityOn S (BitString.ofList _ ((BitString.poweringMasks F.length k).getD j [])) =
          true} := by
    rw [amplify, QuadSystem.countViolated, List.countP_map, List.countP_eq_card_filter_getElem]
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
      decide_eq_true_iff, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem j.isLt,
      Option.getD_some]
    exact hviol _
  rw [hcount, amplify, List.length_map,
    le_div_iff₀ (mod_cast Nat.pos_of_ne_zero (NeZero.ne _) :
      (0 : ℝ) < (BitString.poweringMasks F.length k).length)]
  exact (BitString.isSmallBias_poweringMasks F.length hk).le_card_filter_parityOn hS

/-- The linear combination of the equations a mask selects is computable in polynomial time. -/
theorem computableInPolyTime_linearCombination :
    ComputableInPolyTime (fun p : QuadSystem ℕ × List Bool => p.1.linearCombination p.2)
      (encPair encoding encBits) (encQuadEquation encNat) := by
  have hG : ComputableInPolyTime (fun p : QuadSystem ℕ × List Bool =>
      ((p.2.zip p.1).filter (·.1)).map (·.2)) (encPair encoding encBits) encoding := by
    have hz := (ComputableInPolyTime.zip encBool (encQuadEquation encNat)).comp
      (((bits_encList_polyTime encBool).1.comp (ComputableInPolyTime.snd encoding encBits)).prod
        (ComputableInPolyTime.fst encoding encBits))
    exact (ComputableInPolyTime.map (ComputableInPolyTime.snd _ _)).comp
      ((ComputableInPolyTime.filter (ComputableInPolyTime.fst _ _)).comp hz)
  have hsum : ComputableInPolyTime (fun G : QuadSystem ℕ =>
      (⟨G.flatMap (·.terms), (G.map (·.rhs)).sum⟩ : QuadEquation ℕ)) encoding
        (encQuadEquation encNat) := by
    have hxor (l : List Bool) : l.sum = l.foldl xor false := by rw [List.sum_eq_foldl]; rfl
    simp only [hxor]
    unfold encoding
    fun_prop
  exact hsum.comp hG

/-- **The amplifying self-reduction runs in polynomial time**, for every fixed `k`. The
certificate includes the construction of the small-bias family on the unary width
`F.length`. -/
theorem computableInPolyTime_amplify (k : ℕ) :
    ComputableInPolyTime (amplify k) encoding encoding := by
  have hmasks : ComputableInPolyTime (fun F : QuadSystem ℕ => BitString.poweringMasks F.length k)
      encoding (encList encBits) := by
    simpa only [Function.comp_def] using BitString.poweringMasks_polyTime.comp (encIn := encoding)
      (ComputableInPolyTime.prod (encIn := encoding)
        (ComputableInPolyTime.length_list (encQuadEquation encNat))
        (ComputableInPolyTime.const (encIn := encoding) (encOut := encUnary) k))
  exact ComputableInPolyTime.mapWithInput (encB := encQuadEquation encNat)
    (f := QuadSystem.linearCombination) hmasks computableInPolyTime_linearCombination

end QUADEQ

/-- **QUADEQ reduces to its gap problem** [Goldreich2007DraftR5, Exercise 10.6]: for
`0 < δ < 1/2`, the amplifying self-reduction with a constant `k ≥ 1/(1 - 2δ)` maps satisfiable
systems to satisfiable systems and unsatisfiable systems to systems in which every assignment
violates at least a `δ` fraction of the equations. -/
theorem polyTimeReducible_QUADEQ_GapQUADEQ {δ : ℝ} (hδ₀ : 0 < δ) (hδ : δ < 1 / 2) :
    PromiseProblem.PolyTimeReducible QUADEQ.encoding QUADEQ.encoding (ofSet QUADEQ)
      (GapQUADEQ δ) := by
  set k := ⌈(1 - 2 * δ)⁻¹⌉₊
  have hpos : 0 < 1 - 2 * δ := by linarith
  have hk : 0 < k := Nat.ceil_pos.2 (inv_pos.2 hpos)
  have hkδ : δ ≤ (1 - 1 / (k : ℝ)) / 2 := by
    have : 1 / (k : ℝ) ≤ 1 - 2 * δ := one_div (k : ℝ) ▸ inv_le_of_inv_le₀ hpos (Nat.le_ceil _)
    linarith
  exact ⟨QUADEQ.amplify k, QUADEQ.computableInPolyTime_amplify k,
    fun _ ⟨a, ha⟩ => ⟨a, QUADEQ.holds_amplify ha⟩, fun F hF =>
      ⟨hδ₀, fun a => hkδ.trans (QUADEQ.le_countViolated_amplify hk fun ha => hF ⟨a, ha⟩)⟩⟩

/-- **The gap problem of quadratic equations is NP-hard**, without the PCP theorem
[Goldreich2007DraftR5, Exercise 10.6]: for every `0 < δ < 1/2`, in particular for the source's
`δ = 1/3` and `δ = 1/2 - ε`, it is NP-hard to tell satisfiable systems of quadratic equations over
`𝔽₂` apart from systems in which every assignment violates at least a `δ` fraction of the
equations. -/
theorem GapQUADEQ_npHard {δ : ℝ} (hδ₀ : 0 < δ) (hδ : δ < 1 / 2) :
    PromiseProblem.NPHard QUADEQ.encoding (GapQUADEQ δ) :=
  (npHard_ofSet_iff.2 QUADEQ_npHard).trans (polyTimeReducible_QUADEQ_GapQUADEQ hδ₀ hδ)

/-- The gap problem is in promise-NP: its yes-instances form `QUADEQ`, which is in `NP`.
Together with `GapQUADEQ_npHard` this is the NP-completeness of [Goldreich2007DraftR5,
Exercise 10.6]. -/
theorem GapQUADEQ_mem_PromiseNP (δ : ℝ) : GapQUADEQ δ ∈ PromiseNP QUADEQ.encoding :=
  ⟨QUADEQ, QUADEQ.mem_NP, subset_rfl, (GapQUADEQ δ).disjoint⟩

end Cslib.Complexity
