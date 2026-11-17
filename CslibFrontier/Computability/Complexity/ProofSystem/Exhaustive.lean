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
instance followed by padding at least as long as the number `2 ^ m` of certificates of the
prescribed length `m` for its complement. With that much padding, checking that the complement's
verifier rejects every certificate takes time polynomial in the length of the proof.

So the dichotomy of [Cook and Reckhow][CookReckhow1979] can be stated with one fixed proof system,
as in [Goldreich, Theorem B.13][Goldreich2007DraftR6]: some proof system for the unsatisfiable
formulas in conjunctive normal form is polynomially bounded exactly when `NP = coNP`
(`Cslib.Complexity.ProofSystem.exists_polynomiallyBounded_iff_NP_eq_coNP`). The system is chosen by
cases on `NP = coNP`. If they are equal, it is a polynomially bounded system. If not, it is the
exhaustive system, and no system for that set is polynomially bounded.

## Main definitions

* `Cslib.Complexity.ProofSystem.exhaustive`: the exhaustive proof system of a verifier for the
  complement of a set.

## Main results

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

/-- Whether a word pads its instance to at least `2 ^ m` bits, for the prescribed certificate
length `m`, and the verifier rejects every certificate of length `m`. The enumeration is cut at
`Nat.log 2 π.length` bits, so it stays polynomial in the length of the word. -/
private def exhaustiveAccepts (D : Decoder enc) (p : Polynomial ℕ) (V : α × List Bool → Bool)
    (π : List Bool) : Bool :=
  decide (certLength D p π ≤ Nat.log 2 π.length) &&
    (BitString.enumList (min (certLength D p π) (Nat.log 2 π.length))).all
      fun w => !V (verifierInstance D π, w)

private theorem two_pow_min_mul_le (m n : ℕ) :
    2 ^ min m (Nat.log 2 n) * (2 * min m (Nat.log 2 n) + 1) ≤ (n + 1) * (2 * n + 1) := by
  have hlog : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hpow : 2 ^ min m (Nat.log 2 n) ≤ n + 1 := by
    refine (Nat.pow_le_pow_right (by decide) (min_le_right _ _)).trans ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
  have hmin : min m (Nat.log 2 n) ≤ n := (min_le_right _ _).trans hlog
  exact Nat.mul_le_mul hpow (by omega)

private theorem computableInPolyTime_exhaustiveAccepts (D : Decoder enc)
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (exhaustiveAccepts D p V) encBits encBool := by
  have hi : ComputableInPolyTime (verifierInstance D) encBits enc :=
    D.computableInPolyTime.comp unframe
  have hlen : ComputableInPolyTime (certLength D p) encBits encUnary :=
    (unary_eval p).comp ((encoding_length enc).comp hi)
  have hlog : ComputableInPolyTime (fun π : List Bool => Nat.log 2 π.length) encBits encUnary :=
    (ComputableInPolyTime.of_tidy ComputableTidilyInPolyTime.unary_log_two).comp length_bits
  have henum : ComputableInPolyTime
      (fun π => BitString.enumList (min (certLength D p π) (Nat.log 2 π.length)))
      encBits (encList encBits) :=
    bitsEnumList (unary_min' hlen hlog) (size := fun n => (n + 1) * (2 * n + 1))
      (by fun_prop) fun π => two_pow_min_mul_le _ _
  have htest : ComputableInPolyTime
      (fun q : List Bool × List Bool => !V (verifierInstance D q.1, q.2))
      (encPair encBits encBits) encBool :=
    bool_not.comp (hV.comp ((hi.comp (fst _ _)).prod (snd _ _)))
  exact bool_and' (.of_tidy (ComputableTidilyInPolyTime.unary_le' hlen.tidy hlog.tidy))
    (allWithInput henum htest)

/-- The **exhaustive proof system** of a verifier `V` for the complement of `L`, with a default
member `a₀`. A word proves the instance its first frame decodes to when it is at least `2 ^ m`
bits long, for the certificate length `m` that `V` prescribes, and `V` rejects every certificate
of length `m`; otherwise it proves `a₀`. A member `a` of `L` is proved by its framed encoding
followed by `2 ^ m` padding bits, so proofs may be exponentially long. -/
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
      · simp only [exhaustiveAccepts, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
          Bool.not_eq_eq_eq_not, Bool.not_true] at h
        obtain ⟨hle, hall⟩ := h
        by_contra hnot
        obtain ⟨w, hw, hVw⟩ := (hVL _).1 hnot
        rw [min_eq_left hle] at hall
        have := hall w (BitString.mem_enumList.2 (by rw [hw]; rfl))
        simp [hVw] at this
      · exact ha₀
    · set m := p.eval (enc a).length
      refine ⟨frame (enc a) ++ List.replicate (2 ^ m) false, ?_⟩
      have hi : verifierInstance D (frame (enc a) ++ List.replicate (2 ^ m) false) = a := by
        rw [verifierInstance, unframe_frame_append, D.decode_enc]
      have hm : m ≤ Nat.log 2 (frame (enc a) ++ List.replicate (2 ^ m) false).length :=
        Nat.le_log_of_pow_le (by decide) (by simp)
      have hacc : exhaustiveAccepts D p V (frame (enc a) ++ List.replicate (2 ^ m) false) := by
        simp only [exhaustiveAccepts, certLength, hi, Bool.and_eq_true, decide_eq_true_eq,
          List.all_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true]
        refine ⟨hm, fun w hw => ?_⟩
        rw [min_eq_left hm, BitString.mem_enumList] at hw
        by_contra hVw
        exact (hVL a).2 ⟨w, hw, by simpa using hVw⟩ ha
      simp only [hacc, ↓reduceIte, hi]

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
systems given as verifiers: proofs here refute unsatisfiable CNF formulas (the refutation view the
source adopts in the rest of Appendix B.4), and a proof system is a Cook–Reckhow function onto
the set (`ProofSystem`), computable in polynomial time in the length of the proof. A verifier
`M(π, T)` running in time polynomial in `|π| + |T|` gives such a function (prove `T` when `M`
accepts, a fixed member otherwise), and such a function `f` gives the verifier `f π = T`, with
the same proofs. "`L_M` is upper-bounded by a polynomial" is `PolynomiallyBounded`. As in the
source, `M` is not explicit: it is chosen by cases on `NP = coNP`. -/
theorem exists_polynomiallyBounded_iff_NP_eq_coNP :
    ∃ M : ProofSystem encCNF UNSAT,
      (M.PolynomiallyBounded ↔ ∀ {γ : Type} (encC : γ ↪ List Bool), NP encC = coNP encC) := by
  obtain ⟨M, hM⟩ := exists_polynomiallyBounded_iff_coNP_subset_NP CookLevin.UNSAT_coNPComplete
    cnfDecoder ⟨[[]], fun ⟨_, h⟩ => by simp at h⟩
  exact ⟨M, hM.trans NP_eq_coNP_iff_coNP_subset_NP.symm⟩

end Cslib.Complexity.ProofSystem
