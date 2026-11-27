/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Complexity.Classes.IP.GraphNonIsomorphism
import CslibFrontier.Computability.Complexity.Classes.IP.Shamir
import CslibFrontier.Computability.Complexity.Classes.MIP

/-! Multiprover interactive proofs (`MIP₂` and `MIP`), non-communicating provers, deterministic
prover optimality, transcript consistency, the upper bound `MIP ⊆ NEXP`, and consistency checks for proof-oracle verifiers. -/

namespace CslibFrontierTests.MIP

open Cslib Cslib.Complexity Cslib.Probability Turing.MultiTapeTM

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

example : acceptProb (Oracularize.roundBits repeatQuery 2) (Prover.independent cheater) = 3 / 4 := by
  rw [Oracularize.acceptProb_roundBits]
  change acceptProb (Oracularize.round repeatQuery 3) _ = _
  rw [Oracularize.round, acceptProb_sample_bind]
  simp only [checked_cheater, ProbComp.eval_unifFin, PMF.uniformOfFintype_apply, Fintype.card_fin,
    tsum_fintype, Fin.sum_univ_succ]
  norm_num [div_eq_mul_inv, two_mul, Fin.sum_univ_succ]
  ring

end CslibFrontierTests.MIP
