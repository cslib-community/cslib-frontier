/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.ProofSystem
import CslibFrontier.Computability.Complexity.CookLevin.Completeness
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.BitString.Enumeration

/-!
# Exhaustive proof systems for `coNP` sets

Every nonempty set in `coNP` whose encoding has a decoder has a proof system, usually not a
polynomially bounded one (`Cslib.Complexity.ProofSystem.exhaustive`). A proof is an encoded
instance followed by padding. For the certificate length `m` that a verifier for the complement
prescribes, the proof is checked when `m ≤ ⌊log₂ |π|⌋`. For a nonempty proof `π` this says that
`π` has at least `2 ^ m` bits. The empty proof passes only with `m = 0`, with its single empty
certificate. When it passes, checking that the complement's verifier rejects every certificate of
length `m` takes time polynomial in the length of the proof.

The dichotomy of [Cook and Reckhow][CookReckhow1979] then holds for one fixed proof system, as in
[Goldreich, Theorem B.13][Goldreich2007DraftR6]. Some proof system for the unsatisfiable formulas in
conjunctive normal form is polynomially bounded exactly when `NP = coNP`
(`Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_NP_eq_coNP`). The source derives it
from the coNP-completeness of its tautologies. The proof here chooses the system by cases on
`NP = coNP`. If they are equal, it is a polynomially bounded system. If not, it is the exhaustive
system, and no system for that set is polynomially bounded.

## Main definitions

* `Cslib.Complexity.ProofSystem.exhaustive`: the exhaustive proof system of a verifier for the
  complement of a set.

## Main results

* `Cslib.Complexity.ProofSystem.exhaustive_frame_append_replicate`,
  `Cslib.Complexity.ProofSystem.exhaustive_eq_of_notMem`: a padded framed member proves itself, and
  a word whose decoded instance is not in the set proves the default member.
* `Cslib.Complexity.ProofSystem.nonempty_of_mem_coNP`: every nonempty `coNP` set with a decodable
  encoding has a proof system.
* `Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_coNP_subset_NP`: for a nonempty
  decodable `coNP`-complete set, one proof system is polynomially bounded exactly when
  `coNP ⊆ NP`.
* `Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_NP_eq_coNP`: Goldreich's
  Theorem B.13, for refutations of formulas in conjunctive normal form.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, May 2007 draft `r6.pdf`,
  Appendix B.4][Goldreich2007DraftR6], Definition B.12 and Theorem B.13 (printed p. 527,
  PDF p. 19)
* [S. A. Cook, R. A. Reckhow, *The relative efficiency of propositional proof
  systems*][CookReckhow1979]
-/

public section

namespace Cslib.Complexity.ProofSystem

open Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool} {L : Set α} {p : Polynomial ℕ}
  {V : α × List Bool → Bool}

/-- The certificate length that the verifier prescribes for the instance a word presents. -/
private def certLength (D : Decoder enc) (p : Polynomial ℕ) (π : List Bool) : ℕ :=
  p.eval (enc (verifierInstance D π)).length

/-- Whether the prescribed certificate length `m` of a word `π` satisfies `m ≤ ⌊log₂ |π|⌋` and the
verifier rejects every certificate of length `m`. The enumeration is cut at `⌊log₂ |π|⌋` bits, so
it stays polynomial in the length of the word even when the first test fails. -/
private def exhaustiveAccepts (D : Decoder enc) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (π : List Bool) : Bool :=
  decide (certLength D p π ≤ Nat.log 2 π.length) &&
    (BitString.enumList (min (certLength D p π) (Nat.log 2 π.length))).all
      fun w => !V (verifierInstance D π, w)

private theorem computableInPolyTime_exhaustiveAccepts (D : Decoder enc)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (exhaustiveAccepts D p V) encBits encBool := by
  have hi : ComputableInPolyTime (verifierInstance D) encBits enc :=
    D.computableInPolyTime.comp unframe
  have hlen : ComputableInPolyTime (certLength D p) encBits encUnary :=
    (unary_eval p).comp ((encoding_length enc).comp hi)
  have hlog : ComputableInPolyTime (fun π : List Bool => Nat.log 2 π.length) encBits encUnary :=
    ComputableInPolyTime.unary_log_two.comp length_bits
  have henum : ComputableInPolyTime
      (fun π => BitString.enumList (min (certLength D p π) (Nat.log 2 π.length)))
      encBits (encList encBits) :=
    bitsEnumList_of_le_mul_log (c := 1) (unary_min' hlen hlog) fun π => by
      simp only [encBits_apply, one_mul]
      exact (min_le_right _ _).trans (Nat.le_succ _)
  have htest : ComputableInPolyTime
      (fun q : List Bool × List Bool => !V (verifierInstance D q.1, q.2))
      (encPair encBits encBits) encBool :=
    bool_not.comp (hV.comp ((hi.comp (fst _ _)).prod (snd _ _)))
  exact bool_and' (ComputableInPolyTime.unary_le' hlen hlog)
    (allWithInput henum htest)

/-- Soundness of the check: an accepted word presents a member of `L`. -/
private theorem mem_of_exhaustiveAccepts (D : Decoder enc) (hVL : IsVerifier enc p V Lᶜ)
    {π : List Bool} (h : exhaustiveAccepts D p V π = true) : verifierInstance D π ∈ L := by
  simp only [exhaustiveAccepts, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨hle, hall⟩ := h
  by_contra hnot
  obtain ⟨w, hw, hVw⟩ := (hVL _).1 hnot
  rw [min_eq_left hle] at hall
  have := hall w (BitString.mem_enumList.2 (by rw [hw]; rfl))
  simp [hVw] at this

/-- A framed member followed by `2 ^ m` padding bits passes the check. -/
private theorem exhaustiveAccepts_frame_append_replicate (D : Decoder enc)
    (hVL : IsVerifier enc p V Lᶜ) {a : α} (ha : a ∈ L) :
    exhaustiveAccepts D p V
      (frame (enc a) ++ List.replicate (2 ^ p.eval (enc a).length) false) = true := by
  set m := p.eval (enc a).length
  have hi : verifierInstance D (frame (enc a) ++ List.replicate (2 ^ m) false) = a := by
    rw [verifierInstance, unframe_frame_append, D.decode_enc]
  have hm : m ≤ Nat.log 2 (frame (enc a) ++ List.replicate (2 ^ m) false).length :=
    Nat.le_log_of_pow_le (by decide) (by simp)
  simp only [exhaustiveAccepts, certLength, hi, Bool.and_eq_true, decide_eq_true_eq,
    List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
  refine ⟨hm, fun w hw => ?_⟩
  rw [min_eq_left hm, BitString.mem_enumList] at hw
  by_contra hVw
  exact (hVL a).2 ⟨w, hw, by simpa using hVw⟩ ha

/-- The **exhaustive proof system** of a verifier `V` for the complement of `L`, with a default
member `a₀`. A word `π` proves the instance its first frame decodes to when the certificate length
`m` that `V` prescribes for it satisfies `m ≤ ⌊log₂ |π|⌋` and `V` rejects every certificate of
length `m`; otherwise it proves `a₀`. A member `a` of `L` is proved by its framed encoding
followed by `2 ^ m` padding bits (`exhaustive_frame_append_replicate`), so proofs may be
exponentially long. -/
def exhaustive (D : Decoder enc) (hV : ComputableInPolyTime V (encPair enc encBits) encBool)
    (hVL : IsVerifier enc p V Lᶜ) {a₀ : α} (ha₀ : a₀ ∈ L) : ProofSystem enc L where
  toFun π := if exhaustiveAccepts D p V π then verifierInstance D π else a₀
  computable := (computableInPolyTime_exhaustiveAccepts D hV).ite'
    (D.computableInPolyTime.comp unframe) (const a₀)
  range_eq := by
    refine Set.Subset.antisymm ?_ fun a ha => ?_
    · rintro _ ⟨π, rfl⟩
      dsimp only
      split_ifs with h
      · exact mem_of_exhaustiveAccepts D hVL h
      · exact ha₀
    · refine ⟨frame (enc a) ++ List.replicate (2 ^ p.eval (enc a).length) false, ?_⟩
      simp only [exhaustiveAccepts_frame_append_replicate D hVL ha, ↓reduceIte,
        verifierInstance, unframe_frame_append, D.decode_enc]

/-- A member `a` of `L` is proved by its framed encoding followed by `2 ^ m` padding bits, for the
certificate length `m = p (|enc a|)` of the verifier. -/
theorem exhaustive_frame_append_replicate (D : Decoder enc)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (hVL : IsVerifier enc p V Lᶜ)
    {a₀ : α} (ha₀ : a₀ ∈ L) {a : α} (ha : a ∈ L) :
    exhaustive D hV hVL ha₀
      (frame (enc a) ++ List.replicate (2 ^ p.eval (enc a).length) false) = a := by
  change (if _ then _ else _) = a
  simp only [exhaustiveAccepts_frame_append_replicate D hVL ha, ↓reduceIte, verifierInstance,
    unframe_frame_append, D.decode_enc]

/-- A word whose first frame decodes to an instance outside `L` proves the default member. -/
theorem exhaustive_eq_of_notMem (D : Decoder enc)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) (hVL : IsVerifier enc p V Lᶜ)
    {a₀ : α} (ha₀ : a₀ ∈ L) {π : List Bool} (h : verifierInstance D π ∉ L) :
    exhaustive D hV hVL ha₀ π = a₀ := by
  change (if _ then _ else _) = a₀
  split_ifs with hacc
  · exact absurd (mem_of_exhaustiveAccepts D hVL hacc) h
  · rfl

/-- **Every nonempty `coNP` set with a decodable encoding has a proof system**: the exhaustive
proof system of a verifier for its complement. -/
theorem nonempty_of_mem_coNP (D : Decoder enc) (hL : L ∈ coNP enc) (hne : L.Nonempty) :
    Nonempty (ProofSystem enc L) := by
  obtain ⟨p, V, hV, hVL⟩ := hL
  exact ⟨exhaustive D hV hVL hne.some_mem⟩

/-- **One proof system decides `coNP ⊆ NP`**: a nonempty `coNP`-complete set with a decodable
encoding has a proof system that is polynomially bounded exactly when `coNP ⊆ NP`, for problems
with every encoding of their instances. The system is chosen by cases: a polynomially bounded one
when `coNP ⊆ NP`, and any one otherwise (`nonempty_of_mem_coNP`), which then is not polynomially
bounded by `coNP_subset_NP_iff_exists_polynomiallyBounded`. -/
theorem exists_polynomiallyBounded_iff_coNP_subset_NP {β : Type} {encB : β ↪ List Bool}
    {B : Set β} (hB : coNPComplete encB B) (D : Decoder encB) (hne : B.Nonempty) :
    ∃ M : ProofSystem encB B,
      (M.PolynomiallyBounded ↔ ∀ {γ : Type} (encC : γ ↪ List Bool), coNP encC ⊆ NP encC) := by
  have hCR := coNP_subset_NP_iff_exists_polynomiallyBounded hB D hne
  by_cases h : ∀ {γ : Type} (encC : γ ↪ List Bool), coNP encC ⊆ NP encC
  · obtain ⟨M, hM⟩ := hCR.1 h
    exact ⟨M, iff_of_true hM h⟩
  · obtain ⟨M⟩ := nonempty_of_mem_coNP D hB.1 hne
    exact ⟨M, iff_of_false (fun hM => h (hCR.2 ⟨M, hM⟩)) h⟩

/-- **A fixed proof system is polynomially bounded exactly when `NP = coNP`**
([Goldreich, Theorem B.13][Goldreich2007DraftR6], after [CookReckhow1979]): there is a proof
system `M` for the unsatisfiable formulas in conjunctive normal form such that `M` is polynomially
bounded if and only if `NP = coNP`, for problems with every encoding of their instances.

Deviations from the source, which states the theorem for propositional tautologies and proof
systems given as verifiers (Definition B.12):
* Proofs here refute unsatisfiable CNF formulas, the refutation view the source adopts in the rest
  of Appendix B.4.
* A proof system is a Cook–Reckhow function onto the set (`ProofSystem`), computable in
  polynomial time in the length of the proof. A verifier `M(π, T)` running in time polynomial in
  `|π| + |T|` gives such a function by encoding both the formula and its certificate in the proof
  word (prove `T` when `M` accepts, a fixed member otherwise). Conversely, a function `f` gives the
  verifier that evaluates `f π` and compares it with `T`. Polynomial boundedness transfers in both
  directions, but the proofs and their exact lengths need not agree.
* "`L_M` is upper-bounded by a polynomial" is `PolynomiallyBounded`, a polynomial bound on a
  shortest proof of each member, which is the per-instance form of the bound on the maximum.

The source derives the theorem from the coNP-completeness of the tautologies. The proof here
chooses `M` by cases on `NP = coNP`, a polynomially bounded system if they are equal and the
exhaustive system otherwise, so `M` is not explicit. -/
theorem exists_polynomiallyBounded_iff_NP_eq_coNP :
    ∃ M : ProofSystem encCNF UNSAT,
      (M.PolynomiallyBounded ↔ ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) := by
  obtain ⟨M, hM⟩ := exists_polynomiallyBounded_iff_coNP_subset_NP CookLevin.UNSAT_coNPComplete
    cnfDecoder ⟨[[]], fun ⟨_, h⟩ => by simp at h⟩
  exact ⟨M, hM.trans NP_eq_coNP_iff_coNP_subset_NP.symm⟩

end Cslib.Complexity.ProofSystem
