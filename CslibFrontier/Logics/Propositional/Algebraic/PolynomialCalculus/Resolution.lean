/-
Copyright (c) 2026 Vincent Palma, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Palma, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Algebraic.CNF.PCR
public import CslibFrontier.Logics.Propositional.Algebraic.PolynomialCalculus.Composition
import CslibFrontier.Foundations.Data.MvPolynomial.CoefficientDegree
import CslibFrontier.Foundations.Data.MvPolynomial.Support
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.Ring

/-!
# Resolution simulated by polynomial calculus resolution

Every list-calculus resolution proof with `s` lines of distinct-literal width at most `w`
has a polynomial calculus proof of its squarefree twin-variable clause polynomials, from
`CNF.toPCRPolys`, with monomial-count size at most `(5 * w + 13) * s` and degree at most
`w + 1` (`CNF.IsProof.exists_pcr`). All translated lines are retained, so the same theorem
translates refutations and derivations with several conclusions.

The polynomial calculus model and twin-variable encoding are those of
[AlekhnovichBenSassonRazborovWigderson2002, §4.1]. The explicit constants here are an
accounting bound for this construction, not a claim that the source states these constants.
Size counts supported monomials on proof lines, not coefficient bit length or the runtime of
proof translation. The old list-based `Clause.toPoly` is unchanged.

For a resolution step with squarefree resolvent monomial `M`, multiply the parent monomials
to obtain `X (v, false) * M` and `X (v, true) * M`, then subtract
`M * (X (v, true) + X (v, false) - 1)` from their sum. If a pivot polarity survives in the
resolvent because a parent is tautological, one parent is already a subclause of the resolvent:
multiplication alone suffices. Thus neither absence of tautologies nor absence of repeated
literals is assumed. Proof composition shares previously translated lines.

## Main results

* `Cslib.Logic.PL.PC.IsProof.exists_toPCRPoly_resolvent`: one bounded resolution step.
* `Cslib.Logic.PL.CNF.IsProof.exists_pcr`: translate all lines of a bounded-width proof.
* `Cslib.Logic.PL.CNF.IsProof.exists_pcr_refutation`: simultaneous size and degree bounds for
  refutations.
* `Cslib.Logic.PL.CNF.RefutableInWidth.pcr_refutableInDegree`: width gives PCR degree.
* `Cslib.Logic.PL.CNF.RefutableInSize.pcr_refutableInSize`: a size bound using the number of
  occurring variables.

## References

* [M. Alekhnovich, E. Ben-Sasson, A. A. Razborov, A. Wigderson,
  *Space Complexity in Propositional Calculus*, §4.1][AlekhnovichBenSassonRazborovWigderson2002]
-/

public section

namespace Cslib.Logic.PL

open MvPolynomial

variable {V R : Type*} [DecidableEq V] [CommRing R]

private theorem extend_clause {F ls : List (MvPolynomial (Literal V) R)} {c : Clause V}
    (h : PC.IsProof F ls) (hc : c.toPCRPoly R ∈ ls) (S : Finset (Literal V))
    (hS : c.toFinset ⊆ S) :
    ∃ ms, PC.IsProof F ms ∧ ls ⊆ ms ∧ (∏ l ∈ S, X l.negate) ∈ ms ∧
      PC.size ms ≤ PC.size ls + S.card + 1 ∧
      PC.degree ms ≤ max (PC.degree ls) S.card := by
  classical
  obtain ⟨ms, hms, hsub, hp, hs, hd⟩ :=
    h.exists_prod_mul hc (S \ c.toFinset) Std.Sat.Literal.negate
  have hcard : (S \ c.toFinset).card + c.width = S.card :=
    Finset.card_sdiff_add_card_eq_card hS
  rw [Clause.toPCRPoly_eq_prod, Finset.prod_sdiff hS] at hp
  refine ⟨ms, hms, hsub, hp, ?_, ?_⟩
  · have := Nat.mul_le_mul_left ((S \ c.toFinset).card + 1) (c.card_support_toPCRPoly_le (R := R))
    omega
  · have := c.totalDegree_toPCRPoly_le (R := R)
    omega

/-- A resolution inference can extend a polynomial calculus proof by at most
`5 * resolvent.width + 13` monomials, with degree at most the larger of its old degree and
`resolvent.width + 1`. Both translated parents and the pivot's complementarity axiom suffice.
Repeated literals and tautological parents are permitted. -/
theorem PC.IsProof.exists_toPCRPoly_resolvent
    {F ls : List (MvPolynomial (Literal V) R)} {c₁ c₂ : Clause V}
    (h : PC.IsProof F ls) (v : V)
    (h₁ : c₁.toPCRPoly R ∈ ls) (h₂ : c₂.toPCRPoly R ∈ ls)
    (hcomp : PCR.complementAxiom v ∈ F) :
    ∃ ms, PC.IsProof F ms ∧ ls ⊆ ms ∧ (c₁.resolvent c₂ v).toPCRPoly R ∈ ms ∧
      PC.size ms ≤ PC.size ls + 5 * (c₁.resolvent c₂ v).width + 13 ∧
      PC.degree ms ≤ max (PC.degree ls) ((c₁.resolvent c₂ v).width + 1) := by
  classical
  let d := c₁.resolvent c₂ v
  change ∃ ms, PC.IsProof F ms ∧ ls ⊆ ms ∧ d.toPCRPoly R ∈ ms ∧
    PC.size ms ≤ PC.size ls + 5 * d.width + 13 ∧
    PC.degree ms ≤ max (PC.degree ls) (d.width + 1)
  let S := d.toFinset
  have hS : S.card = d.width := rfl
  have hleft : c₁.toFinset ⊆ insert (v, true) S := Finset.subset_insert_iff.2 fun l hl =>
    List.mem_toFinset.2 (Clause.mem_resolvent.2
      (.inl ⟨List.mem_toFinset.1 (Finset.mem_of_mem_erase hl), Finset.ne_of_mem_erase hl⟩))
  have hright : c₂.toFinset ⊆ insert (v, false) S := Finset.subset_insert_iff.2 fun l hl =>
    List.mem_toFinset.2 (Clause.mem_resolvent.2
      (.inr ⟨List.mem_toFinset.1 (Finset.mem_of_mem_erase hl), Finset.ne_of_mem_erase hl⟩))
  by_cases hone : ∃ c : Clause V, c.toPCRPoly R ∈ ls ∧ c.toFinset ⊆ S
  · obtain ⟨c, hc, hsub⟩ := hone
    obtain ⟨ms, hms, hls, hp, hs, hd⟩ := extend_clause h hc S hsub
    exact ⟨ms, hms, hls, hp, by omega, by omega⟩
  have hposS : (v, true) ∉ S := fun hp =>
    hone ⟨c₁, h₁, by rwa [Finset.insert_eq_of_mem hp] at hleft⟩
  have hnegS : (v, false) ∉ S := fun hn =>
    hone ⟨c₂, h₂, by rwa [Finset.insert_eq_of_mem hn] at hright⟩
  let M : MvPolynomial (Literal V) R := d.toPCRPoly R
  let a : MvPolynomial (Literal V) R := X (v, false) * M
  let b : MvPolynomial (Literal V) R := X (v, true) * M
  let q : MvPolynomial (Literal V) R := M * PCR.complementAxiom v
  obtain ⟨ms₁, hm₁, hls₁, ha, hs₁, hd₁⟩ := extend_clause h h₁ _ hleft
  have ha' : a ∈ ms₁ := by
    simpa [Finset.prod_insert hposS, Std.Sat.Literal.negate, a, M, Clause.toPCRPoly, S] using ha
  obtain ⟨ms₂, hm₂, hls₂, hb, hs₂, hd₂⟩ := extend_clause hm₁ (hls₁ h₂) _ hright
  have hb' : b ∈ ms₂ := by
    simpa [Finset.prod_insert hnegS, Std.Sat.Literal.negate, b, M, Clause.toPCRPoly, S] using hb
  let base := PCR.complementAxiom v :: ms₂
  have hbase : PC.IsProof F base := hm₂.mem hcomp
  obtain ⟨ms₃, hm₃, hls₃, hq, hs₃, hd₃⟩ :=
    hbase.exists_prod_mul (p := PCR.complementAxiom v) List.mem_cons_self S Std.Sat.Literal.negate
  have ha₃ : a ∈ ms₃ := hls₃ (List.mem_cons_of_mem _ (hls₂ ha'))
  have hb₃ : b ∈ ms₃ := hls₃ (List.mem_cons_of_mem _ hb')
  have hsum : PC.IsProof F ((a + b) :: ms₃) := by
    simpa using hm₃.linear 1 1 ha₃ hb₃
  have heq : C (1 : R) * (a + b) + C (-1 : R) * q = M := by
    simp only [map_one, map_neg, one_mul, neg_one_mul, a, b, q, PCR.complementAxiom]; ring
  have hfinal : PC.IsProof F (M :: (a + b) :: ms₃) :=
    heq ▸ hsum.linear 1 (-1) List.mem_cons_self (List.mem_cons_of_mem _ hq)
  have hMsize : M.support.card ≤ 1 := d.card_support_toPCRPoly_le
  have hMdeg : M.totalDegree ≤ d.width := d.totalDegree_toPCRPoly_le
  have hbounds (sign : Bool) :
      (X (v, sign) * M).support.card ≤ 1 ∧ (X (v, sign) * M).totalDegree ≤ d.width + 1 := by
    refine ⟨by simpa only [support_X_mul, Finset.card_map] using hMsize,
      (totalDegree_mul _ _).trans ?_⟩
    rw [Nat.add_comm (X (v, sign) : MvPolynomial (Literal V) R).totalDegree]
    exact Nat.add_le_add hMdeg (totalDegree_X_le _)
  obtain ⟨hasize, hadeg⟩ := hbounds false
  obtain ⟨hbsize, hbdeg⟩ := hbounds true
  have hsumsize : (a + b).support.card ≤ 2 :=
    (Finset.card_le_card support_add).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add hasize hbsize))
  have hsumdeg : (a + b).totalDegree ≤ d.width + 1 :=
    (totalDegree_add _ _).trans (max_le hadeg hbdeg)
  have hcsize := PCR.card_support_complementAxiom_le (R := R) v
  have hcdeg := PCR.totalDegree_complementAxiom_le (R := R) v
  simp only [Finset.card_insert_of_notMem hposS, Finset.card_insert_of_notMem hnegS, hS]
    at hs₁ hs₂ hd₁ hd₂
  refine ⟨M :: (a + b) :: ms₃, hfinal, fun p hp => ?_, List.mem_cons_self, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      (hls₃ (List.mem_cons_of_mem _ (hls₂ (hls₁ hp)))))
  · have hmul := Nat.mul_le_mul_left (S.card + 1) hcsize
    simp only [base, PC.size_cons, hS] at hs₃ hmul ⊢; omega
  · simp only [base, PC.degree_cons, hS] at hd₃ ⊢; omega

variable [Fintype V]

/-- Translate every line of a resolution proof of width at most `w` to the complete squarefree
PCR encoding. The resulting proof has size at most `(5 * w + 13) * ls.length` and degree at
most `w + 1`. The size measure counts monomial occurrences, and resolution size counts lines. -/
theorem CNF.IsProof.exists_pcr {φ : CNF V} {ls : List (Clause V)} (h : φ.IsProof ls)
    {w : ℕ} (hw : ∀ c ∈ ls, c.width ≤ w) :
    ∃ ms, PC.IsProof (φ.toPCRPolys R) ms ∧ (∀ c ∈ ls, c.toPCRPoly R ∈ ms) ∧
      PC.size ms ≤ (5 * w + 13) * ls.length ∧ PC.degree ms ≤ w + 1 := by
  induction h with
  | nil => exact ⟨[], .nil, by simp, by simp, by simp⟩
  | @mem ls c h hc ih =>
    obtain ⟨ms, hm, hlines, hs, hd⟩ := ih (fun d hd => hw d (List.mem_cons_of_mem _ hd))
    refine ⟨c.toPCRPoly R :: ms, hm.mem (CNF.toPCRPoly_mem_toPCRPolys hc),
      List.forall_mem_cons.2 ⟨List.mem_cons_self, fun d hd => List.mem_cons_of_mem _ (hlines d hd)⟩,
      ?_, ?_⟩
    · rw [PC.size_cons, List.length_cons, Nat.mul_add]
      have := c.card_support_toPCRPoly_le (R := R)
      omega
    · rw [PC.degree_cons]
      have := c.totalDegree_toPCRPoly_le (R := R)
      have := hw c List.mem_cons_self
      omega
  | @resolvent ls c₁ c₂ v h h₁ h₂ hv₁ hv₂ ih =>
    obtain ⟨ms, hm, hlines, hs, hd⟩ := ih (fun d hd => hw d (List.mem_cons_of_mem _ hd))
    obtain ⟨ns, hn, hsub, hp, hsize, hdeg⟩ := hm.exists_toPCRPoly_resolvent v
      (hlines c₁ h₁) (hlines c₂ h₂)
      (φ.axioms_subset_toPCRPolys (PCR.complementAxiom_mem_axioms v))
    have hwres := hw (c₁.resolvent c₂ v) List.mem_cons_self
    refine ⟨ns, hn, List.forall_mem_cons.2 ⟨hp, fun c hc => hsub (hlines c hc)⟩, ?_, by omega⟩
    rw [List.length_cons, Nat.mul_add]; omega

/-- A width-`w` resolution refutation with `s` lines has one PCR refutation simultaneously
bounded by `(5 * w + 13) * s` monomials and degree `w + 1`. -/
theorem CNF.IsProof.exists_pcr_refutation {φ : CNF V} {ls : List (Clause V)}
    (h : φ.IsProof ls) (hnil : [] ∈ ls) {w : ℕ} (hw : ∀ c ∈ ls, c.width ≤ w) :
    ∃ ms, PC.IsProof (φ.toPCRPolys R) ms ∧ 1 ∈ ms ∧
      PC.size ms ≤ (5 * w + 13) * ls.length ∧ PC.degree ms ≤ w + 1 := by
  obtain ⟨ms, hm, hlines, hs, hd⟩ := h.exists_pcr (R := R) hw
  exact ⟨ms, hm, by simpa using hlines [] hnil, hs, hd⟩

/-- A width-`w` resolution refutation gives a PCR refutation of degree at most `w + 1`. -/
theorem CNF.RefutableInWidth.pcr_refutableInDegree {φ : CNF V} {w : ℕ}
    (h : φ.RefutableInWidth w) : PC.RefutableInDegree (φ.toPCRPolys R) (w + 1) := by
  obtain ⟨ls, hls, hnil, hw⟩ := h
  exact (hls.exists_pcr_refutation (R := R) hnil hw).imp fun _ ⟨hm, h1, _, hd⟩ => ⟨hm, h1, hd⟩

/-- An `s`-line resolution refutation has a PCR refutation of size at most
`(10 * n + 13) * s`, where `n` is the number of distinct variables occurring in the CNF.
The count excludes unused variables of the ambient finite type. -/
theorem CNF.RefutableInSize.pcr_refutableInSize {φ : CNF V} {s : ℕ}
    (h : φ.RefutableInSize s) :
    PC.RefutableInSize (φ.toPCRPolys R) ((10 * φ.vars.toFinset.card + 13) * s) := by
  obtain ⟨ls, hls, hnil, hlen⟩ := h
  obtain ⟨ms, hm, h1, hs, _⟩ := hls.exists_pcr_refutation (R := R) hnil
    (w := 2 * φ.vars.toFinset.card) (fun c hc => hls.width_le hc)
  exact ⟨ms, hm, h1, hs.trans (Nat.mul_le_mul (by omega) hlen)⟩

end Cslib.Logic.PL
