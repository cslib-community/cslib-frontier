/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.QuantifiedSAT.Oracle
import CslibFrontier.Computability.Complexity.Classes.PH.OracleNP
import CslibFrontier.Computability.Complexity.Classes.PH.OracleCollapse
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Collapse
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-! Clients of the oracle characterization: complement queries, arbitrary encodings and
polynomially many conditions. No choice of machine, reduction or transcript is supplied. -/

set_option linter.privateModule false

open Cslib.Complexity Turing.MultiTapeTM

-- A universal-level problem uses the same complete existential oracle and negates its answer.
example {α : Type} (enc : α ↪ List Bool) {k : ℕ} (hk : 1 ≤ k) {L : Set α}
    (hL : L ∈ PiP k enc) : L ∈ PWithOracle (encQBF '' SigmaSAT k) enc :=
  (image_SigmaSAT_sigmaPComplete hk).SigmaP_union_PiP_subset_PWithOracle enc (Or.inr hL)

-- Compose the two halves: deterministic Σ₂-oracle access is in Π₃, on any encoding.
example {α : Type} (enc : α ↪ List Bool) {L : Set α}
    (hL : L ∈ PWithOracle (encQBF '' SigmaSAT 2) enc) : L ∈ PiP 3 enc := by
  exact (iUnion_PWithOracle_subset_SigmaP_succ_inter_PiP_succ 2 enc
    (Set.mem_iUnion₂.mpr ⟨_, (image_SigmaSAT_sigmaPComplete (by omega)).1, hL⟩)).2

-- The zero-length conjunction accepts every input, including the empty word.
example (B : Set (List Bool × ℕ)) (hB : B ∈ SigmaP 2 (encPair encBits encUnary)) :
    (Set.univ : Set (List Bool)) ∈ SigmaP 2 encBits := by
  simpa only [Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, Set.ofPred_true] using
    mem_SigmaP_of_forall_lt (N := fun _ => 0) (.const 0) hB

-- A polynomial family of Σ₂ conditions still needs only two blocks.
example {α : Type} (enc : α ↪ List Bool) {B : Set (α × ℕ)}
    (hB : B ∈ SigmaP 2 (encPair enc encUnary)) :
    {a | ∀ i < (enc a).length ^ 2, (a, i) ∈ B} ∈ SigmaP 2 enc :=
  mem_SigmaP_of_forall_lt (by fun_prop) hB

-- The CNF SAT equality transports an arbitrary second-level problem to an oracle verifier.
example {α : Type} (enc : α ↪ List Bool) {L : Set α} (hL : L ∈ SigmaP 2 enc) :
    ∃ p V, ComputableInPolyTimeWithOracle (encCNF '' SAT) V (encPair enc encBits) encBool ∧
      IsVerifier enc p V L :=
  mem_NPWithOracle.mp (by rwa [← SigmaP_two_eq_NPWithOracle_SAT enc])

-- A false reply to a live query is invalid for the universal oracle.
example {t : ℕ} {Control Operation : Type} [DecidableEq Operation]
    (machine : Turing.MultiTapePTM t Bool Control Operation) (a : List Bool)
    (hq : (machine.pendingQuery (machine.replayPrefix (encBits a) [false] 0)).isSome) :
    (a, [false]) ∉ oracleTranscriptNo machine encBits Set.univ := by
  intro h
  exact mem_oracleTranscriptNo.mp h 0 (by simp) rfl hq (Set.mem_univ _)

-- The TQBF oracle collapses two-block problems on an encoded type.
example {L : Set Bool} (hL : L ∈ SigmaPWithOracle (encQBF '' TQBF) 2 encBool) :
    L ∈ PWithOracle (encQBF '' TQBF) encBool := by
  apply PHWithOracle_subset_PWithOracle_of_eq_NPWithOracle
    (PWithOracle_image_TQBF_eq_NPWithOracle encBits)
  exact Set.mem_iUnion.mpr ⟨2, hL⟩
