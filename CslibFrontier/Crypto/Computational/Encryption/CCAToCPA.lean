/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.Authenticated
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.PPT

/-!
# Chosen-ciphertext security implies chosen-plaintext security

In a chosen-ciphertext attack, "the adversary has all the power of an attacker in a chosen
plaintext attack, but in addition, the adversary may obtain decryptions of ciphertexts of its
choosing" ([BonehShoup2023], Section 9.2.2, printed p. 362). This module proves the resulting
implication `INDCCA → INDCPA` for symmetric ciphers: a CPA adversary becomes a `CCAAdversary`
that sends each of its queries to the encryption channel of `ccaOracle` and makes no decryption
query. It gives the CPA half of the AE security claimed in Exercise 9.15(b) (printed p. 395).

## Main definitions

* `SymmetricCipher.cpaToCCAAdversary`: forwards each CPA query to the encryption channel of the
  CCA oracle, truncating replies to a polynomial ciphertext-length bound.

## Main results

* `SymmetricCipher.isOraclePPT_cpaToCCAAdversary`: the reduction is `IsOraclePPT`.
* `SymmetricCipher.eval_ccaGame_cpaToCCAAdversary`: under a ciphertext-length bound, the CCA game
  of the reduction has the same output distribution as the CPA game of the original adversary.
* `SymmetricCipher.INDCCA.indcpa`: `INDCCA` implies `INDCPA`.

## References

* [D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023]
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace SymmetricCipher

/-- Forward a CPA encryption request `((), req)` to the encryption channel `(false, req)` of the
CCA oracle, truncating the reply to `ctBound` bits. -/
private def cpaToCCAHandler (ctBound : ℕ) (request : Unit × List Bool) :
    WordOracleComp Bool (List Bool) :=
  List.take ctBound <$> ProbOracleComp.query (false, request.2)

/-- The CCA adversary that runs a CPA adversary, answering its encryption queries through the
encryption channel of the CCA oracle (replies truncated to `ctBound n` bits) and making no
decryption query. -/
noncomputable def cpaToCCAAdversary (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) : CCAAdversary :=
  fun n _ =>
    OracleComp.interpret
      (OracleComp.sumHandler (fun m => ProbOracleComp.sample (ProbComp.unifFin m))
        (cpaToCCAHandler (ctBound n)))
      (adversary n [])

/-- `cpaToCCAAdversary` is oracle PPT when the CPA adversary is and the bound `ctBound` is
polynomial-time computable. -/
theorem isOraclePPT_cpaToCCAAdversary {ctBound : ℕ → ℕ}
    (hctBound : ComputableInPolyTime ctBound encUnary encUnary)
    {adversary : OracleDistinguisher} (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (cpaToCCAAdversary ctBound adversary) := by
  let EIn := encPair (encPair encUnary encBits) (encPair (encFinEnum Unit) encBits)
  have hhandler : IsOraclePPTOn EIn encBits
      (fun p : (ℕ × List Bool) × (Unit × List Bool) =>
        cpaToCCAHandler (ctBound p.1.1) p.2) := by
    dsimp only [EIn]
    ppt [cpaToCCAHandler]
  have hres : ComputableInPolyTime
      (fun pair : (ℕ × List Bool) × List Bool => ctBound pair.1.1)
      (encPair (encPair encUnary encBits) encBits) encUnary :=
    hctBound.comp (ComputableInPolyTime.fst _ _ |>.comp (ComputableInPolyTime.fst _ _))
  refine hadversary.interpret_preprocess_open'
    (prepare := fun p : ℕ × List Bool => (p.1, ([] : List Bool)))
    (resources := fun p _ => ctBound p.1)
    (by fun_prop) hhandler hres fun p req reply hreply => ?_
  unfold cpaToCCAHandler at hreply
  obtain ⟨raw, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
  exact List.length_take_le _ _

private theorem map_runWith_cpaToCCAHandler (E : SymmetricCipher) (ctBound : ℕ → ℕ) (bit : Bool)
    (n : ℕ) (k : List Bool)
    (hctBound : ∀ msg, msg.length = n →
      ∀ ct ∈ (ProbComp.eval (E.encrypt n k msg)).support, ct.length ≤ ctBound n)
    (request : Unit × List Bool) (queried : List (List Bool)) :
    (ProbOracleComp.runWith (fun q s => ProbComp.eval (E.ccaOracle n k bit q s))
        (cpaToCCAHandler (ctBound n) request) queried).map (fun x => (x.1, ())) =
      ProbComp.eval (E.cpaEncryptionOracle n k bit request ()) := by
  simp only [cpaToCCAHandler, cpaEncryptionOracle, ProbOracleComp.runWith_map,
    ProbOracleComp.runWith_query, ccaOracle, Bool.false_eq_true, ↓reduceIte]
  by_cases hlen : ((unframe request.2).length == n && (dropFrame request.2).length == n) = true
  · simp only [hlen, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure, PMF.map_bind,
      PMF.pure_map, Prod.map_apply]
    apply PMF.bind_congr_on_support
    intro ct hct
    have hmb : (if bit then dropFrame request.2 else unframe request.2).length = n := by
      simp only [Bool.and_eq_true, beq_iff_eq] at hlen
      cases bit <;> simp [hlen]
    rw [List.take_of_length_le (hctBound _ hmb ct hct)]
  · simp only [hlen, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_map,
      Prod.map_apply, List.take_nil]

/-- If `ctBound n` bounds the length of every ciphertext of an `n`-bit message, the CCA game of
`cpaToCCAAdversary ctBound adversary` has the same output distribution as the CPA game of
`adversary`, for either challenge bit. -/
theorem eval_ccaGame_cpaToCCAAdversary (E : SymmetricCipher) (ctBound : ℕ → ℕ)
    (adversary : OracleDistinguisher) (bit : Bool) (n : ℕ)
    (hctBound : E.CiphertextLengthLE n (ctBound n)) :
    ProbComp.eval (E.ccaGame (cpaToCCAAdversary ctBound adversary) bit n) =
      ProbComp.eval (E.cpaGame adversary bit n) := by
  simp only [ccaGame, cpaGame, cpaToCCAAdversary, runWith_norm, pmf_norm]
  peel_binds k
  have hsim := ProbOracleComp.runWith_map_state
    (oracle := fun q s =>
      ProbOracleComp.runWith (fun q' s' => ProbComp.eval (E.ccaOracle n k bit q' s'))
      (cpaToCCAHandler (ctBound n) q) s)
    (oracle' := fun q s => ProbComp.eval (E.cpaEncryptionOracle n k bit q s))
    (represent := fun _ => ())
    (step := map_runWith_cpaToCCAHandler E ctBound bit n k (hctBound k k_mem))
    (adversary n []) []
  have hsim' := congrArg (PMF.map Prod.fst) hsim
  simp only [pmf_norm] at hsim'
  exact hsim'

/-- Adaptive chosen-ciphertext security implies adaptive chosen-plaintext security. -/
theorem INDCCA.indcpa {E : SymmetricCipher} (h : E.INDCCA) : E.INDCPA := by
  intro adversary hadversary
  obtain ⟨ctBound, hctBoundPoly, hctBound⟩ := E.exists_ciphertext_length_bound_of_length_eq
  have hcca := h (cpaToCCAAdversary ctBound adversary)
    (isOraclePPT_cpaToCCAAdversary hctBoundPoly hadversary)
  dsimp only at hcca ⊢
  simpa only [eval_ccaGame_cpaToCCAAdversary E ctBound adversary false _ (hctBound _),
    eval_ccaGame_cpaToCCAAdversary E ctBound adversary true _ (hctBound _)] using hcca

end SymmetricCipher

end Cslib.Crypto
