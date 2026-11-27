/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.IP.GraphNonIsomorphism
import CslibFrontier.Computability.Complexity.Classes.IP.Shamir
import CslibFrontier.Computability.Complexity.Classes.MIP
import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Computability.Complexity.Classes.MIP.Correction

/-! Multiprover interactive proofs (`MIP₂` and `MIP`), non-communicating provers, deterministic
prover optimality, transcript consistency, the upper bound `MIP ⊆ NEXP`,
and consistency checks
for proof-oracle verifiers. -/

namespace CslibFrontierTests.MIP

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

-- The degree-one reply for t ↦ t is read low coefficient first; the second node detects a lie.
example : Cslib.Complexity.MIP.checkLineReply 5 1 (QBFProtocol.encodeReply 5 [0, 1]) [1, 2] := by
  decide

example : Cslib.Complexity.MIP.checkLineReply 5 1 (QBFProtocol.encodeReply 5 [0, 1]) [1, 0] =
    false := by decide

/-! ### Non-communicating provers and transcript consistency -/

-- Querying channel `0` leaves channel `1`'s state untouched.
example (P : Fin 2 → Prover Unit) (word : List Bool) (s s' : ∀ i : Fin 2, (P i).State)
    (reply : List Bool)
    (hout : (reply, s') ∈ (((Prover.independent P).respond ((0 : Fin 2), word)).run s).support) :
    s' 1 = s 1 :=
  Prover.independent_state_eq_of_ne P ((0 : Fin 2), word) s s' reply (by decide : (1 : Fin 2) ≠ 0)
    hout

-- `projHistory` filters and extracts the `(query, reply)` pairs of a single prover channel, and
-- `consistentHist` checks whether two histories give identical replies on their common queries.
example :
    MIP.projHistory 0
      [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
      [([true], [false]), ([true, false], [true])] ∧
    MIP.projHistory 1
      [(0, ([true], [false])), (1, ([false], [true])), (0, ([true, false], [true]))] =
      [([false], [true])] ∧
    MIP.consistentHist
      [([true], [false]), ([false], [true])]
      [([true], [false]), ([true], [false])] = true ∧
    MIP.consistentHist
      [([true], [false])]
      [([true], [true])] = false :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ### Non-vacuity: concrete `IsMultiproverProof` instance -/

-- Every single-prover interactive proof embeds into a two-prover interactive proof via channel 0,
-- giving `GraphNonIsomorphism` completeness `1`, soundness `(17 / 32) ^ 2`, and membership in
-- `MIP₂`, `MIP`, and `NEXP` alongside `TQBF`.
example (x : GraphIsomorphismInstance) :
    (x ∈ GraphNonIsomorphism →
      ∃ P : Fin 2 → Prover Unit,
        1 ≤ acceptProb
          (WordOracleComp.singleOracle (0 : Fin 2) (GraphNonIsomorphism.verifier x))
          (Prover.independent P)) ∧
    (x ∉ GraphNonIsomorphism →
      ∀ P : Fin 2 → Prover Unit,
        acceptProb
          (WordOracleComp.singleOracle (0 : Fin 2) (GraphNonIsomorphism.verifier x))
          (Prover.independent P) ≤ (17 / 32) ^ 2) :=
  ⟨(GraphNonIsomorphism.isInteractiveProof_verifier.isMultiproverProof_singleOracle
      (0 : Fin 2)).complete x,
    (GraphNonIsomorphism.isInteractiveProof_verifier.isMultiproverProof_singleOracle
      (0 : Fin 2)).sound x⟩

example :
    GraphNonIsomorphism ∈ MIP₂ encGraphIsomorphism ∧
    GraphNonIsomorphism ∈ MIP encGraphIsomorphism ∧
    GraphNonIsomorphism ∈ NEXP encGraphIsomorphism ∧
    TQBF ∈ MIP₂ encQBF ∧
    TQBF ∈ NEXP encQBF :=
  ⟨IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP,
    MIP₂_subset_MIP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP),
    MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ GraphNonIsomorphism.mem_IP),
    IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1),
    MIP₂_subset_NEXP _ (IP_subset_MIP₂ _ (PSPACE_subset_IP _ TQBF_pspaceComplete.1))⟩

/-! ### Static proof oracles and consistency checks -/

example (st : Oracularize.CheckState) :
    Oracularize.encCheckState st = encPair encNat encBool (st.count, st.disagreed) := rfl

example : {b : Bool | b = true} ∈ PCPPoly encBool := by
  refine ⟨fun b => pure b, ComputableInPolyTime.isOraclePPTOn (by fun_prop), ?_, ?_⟩
  · rintro b rfl
    exact ⟨fun _ => false, by simp [acceptProb, Prover.run_pure, PMF.pure_apply]⟩
  · intro b hb π
    cases b <;> simp_all [acceptProb, Prover.run_pure, PMF.pure_apply]

-- A verifier accepting with probability three quarters falls below one half in four repetitions.
example (π : List Bool → Bool) :
    acceptProb (sequentialRepeat 4 (ProbOracleComp.sample (ProbComp.sampleDyadicCoin 3 3)))
      (Prover.ofProof (Operation := Unit) π) = 81 / 256 := by
  rw [acceptProb_sequentialRepeat_ofProof, acceptProb, Prover.run_sample, PMF.map_comp]
  change ((ProbComp.eval (ProbComp.sampleDyadicCoin 3 3)).map id true) ^ 4 = _
  rw [PMF.map_id, ProbComp.eval_sampleDyadicCoin_true, show dyadicSize 3 = 4 from by decide]
  norm_num [ENNReal.div_pow]

-- The unique index selected by zero coin flips never encounters a query.
example (P : Fin 2 → Prover Unit) :
    acceptProb (Oracularize.roundBits (pure true) 0) (Prover.independent P) = 1 := by
  rw [Oracularize.acceptProb_roundBits, Oracularize.round, acceptProb_sample_bind]
  simp [Oracularize.checked, acceptProb, Prover.run_pure, OracleComp.interpret_pure, PMF.pure_apply]

private noncomputable def repeatQuery : WordOracleComp Unit Bool := do
  let first ← ProbOracleComp.query ((), [])
  let second ← ProbOracleComp.query ((), [])
  pure (first.headD false != second.headD false)

example (π : List Bool → Bool) : acceptProb repeatQuery (Prover.ofProof π) = 0 := by
  unfold repeatQuery acceptProb
  simp only [Prover.run_bind, Prover.run_query, Prover.ofProof, StateT.run, PMF.pure_bind,
    Prover.run_pure, List.headD_cons, bne_self_eq_false, PMF.pure_map]
  simp [PMF.pure_apply]

-- Channel zero alternates between false and true. Channel one always answers false.
private noncomputable def cheater (i : Fin 2) : Prover Unit where
  State := Bool
  init := false
  respond _ st := PMF.pure ([decide (i = 0) && st], !st)

private theorem checked_cheater (j : ℕ) :
    acceptProb (do let r ← Oracularize.checked repeatQuery j; pure (r.1 && !r.2.disagreed))
      (Prover.independent cheater) = (if j = 1 then 0 else 1) := by
  let outcome : Bool × (Oracularize.logged (cheater 0)).State :=
    (true, ⟨false, [([], true), ([], false)]⟩)
  have run : (Oracularize.logged (cheater 0)).run repeatQuery ⟨(cheater 0).init, []⟩ =
      PMF.pure outcome := by
    simp only [repeatQuery, Prover.run_bind, Prover.run_query, Oracularize.logged, cheater,
      StateT.run, StateT.mk, PMF.pure_bind, PMF.pure_map, Prover.run_pure]
    rfl
  rw [Oracularize.acceptProb_checked, run,
    tsum_eq_single outcome (fun x hx => by rw [PMF.pure_apply_of_ne _ _ hx, zero_mul])]
  rw [PMF.pure_apply_self, one_mul]
  dsimp only [outcome]
  rcases j with _ | _ | j <;> simp [Oracularize.weight, Oracularize.answerProb, StateT.run,
    cheater, PMF.pure_apply]

example : acceptProb (Oracularize.round repeatQuery 2) (Prover.independent cheater) = 2 / 3 := by
  rw [Oracularize.round, acceptProb_sample_bind]
  simp only [checked_cheater, ProbComp.eval_unifFin, PMF.uniformOfFintype_apply, Fintype.card_fin,
    tsum_fintype, Fin.sum_univ_succ]
  norm_num [div_eq_mul_inv, two_mul, Fin.sum_univ_succ]

example :
    acceptProb (Oracularize.roundBits repeatQuery 2) (Prover.independent cheater) = 3 / 4 := by
  rw [Oracularize.acceptProb_roundBits]
  change acceptProb (Oracularize.round repeatQuery 3) _ = _
  rw [Oracularize.round, acceptProb_sample_bind]
  simp only [checked_cheater, ProbComp.eval_unifFin, PMF.uniformOfFintype_apply, Fintype.card_fin,
    tsum_fintype, Fin.sum_univ_succ]
  norm_num [div_eq_mul_inv, two_mul, Fin.sum_univ_succ]
  ring

section

open Cslib.Complexity.MIP

private def correctionProof (q : List Bool) : Bool :=
  decide (q ∈ [encPair encBits encNat (correctionKey [0] [0], 2),
    encPair encBits encNat (pointTableKey [0], 1),
    encPair encBits encNat (pointTableKey [0], 2)])

-- At direction zero both point queries use the same address. Its binary value six
-- represents one over F₅, so the constant-one polynomial is accepted.
example : (Prover.ofProof correctionProof).run (correctAt 5 1 [0] [0]) () = PMF.pure (some 1, ()) := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let z : Fin 1 → ZMod 5 := fun _ => 0
  have h := run_correctAt correctionProof z z
  have ha : correctionAnswer correctionProof z z = some 1 := by decide
  simpa only [ha, show (List.ofFn fun j => (z j).val) = [0] by decide] using h

end

end CslibFrontierTests.MIP
