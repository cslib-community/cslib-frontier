/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.MIP.SumcheckProof
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Tactic.EncLen

/-!
# The scalar sumcheck verifier with a static bit proof

The verifier receives its independent challenges on a binary tape. Each coefficient row is
addressed by the external challenges and the preceding entries of the tape.

## Main definitions

* `Cslib.Complexity.MIP.SumcheckProof.verifyRounds` queries the proof on a supplied challenge tape.
* `Cslib.Complexity.MIP.SumcheckProof.transcript` computes that state from an explicit bit table.

## Main results

* `Cslib.Complexity.MIP.SumcheckProof.isOraclePPTOn_verifyRounds` certifies the strict running time.
* `Cslib.Complexity.MIP.SumcheckProof.run_verifyRounds` computes the transcript for any bit table.
-/

public section

namespace Cslib.Complexity.MIP.SumcheckProof

open Turing.MultiTapeTM Probability Interactive.Sumcheck

/-- Verify the coefficient rows of a sumcheck claiming a zero Boolean-cube sum. Return the full
challenge prefix, the final claim and the conjunction of the consistency checks. -/
def verifyRounds (p : ℕ) (external : List ℕ) (d width : ℕ) (rs : List ℕ) :
    WordOracleComp Unit WordState :=
  OracleComp.iterate rs.length
    (fun s => advance p external d width (rs.getD s.challenges.length 0) s) ⟨[], 0, true⟩

private theorem length_getD_le (rs : List ℕ) (i : ℕ) :
    (encNat (rs.getD i 0)).length ≤ (encList encNat rs).length := by
  by_cases hi : i < rs.length
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
    exact SizedListEncoding.length_elem_le rs _ (List.getElem_mem hi)
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi),
      Option.getD_none]
    exact Nat.zero_le _

/-- The transcript verifier is strict oracle polynomial time, including against arbitrary
stateful oracles. Its parameters and complete challenge tape may depend on the original input. -/
theorem isOraclePPTOn_verifyRounds {α : Type} {e : α ↪ List Bool} {p d width : α → ℕ}
    {external rs : α → List ℕ} (hp : ComputableInPolyTime p e encNat)
    (he : ComputableInPolyTime external e (encList encNat))
    (hd : ComputableInPolyTime d e encUnary) (hw : ComputableInPolyTime width e encUnary)
    (hr : ComputableInPolyTime rs e (encList encNat)) :
    IsOraclePPTOn e encWordState
      (fun a => verifyRounds (p a) (external a) (d a) (width a) (rs a)) := by
  unfold verifyRounds
  apply IsOraclePPTOn.iterateWith_of_bounded_growth
    ((ComputableInPolyTime.length_list encNat).comp hr) (ComputableInPolyTime.const _)
  · apply isOraclePPTOn_advance (hp.comp (.fst _ _)) (he.comp (.fst _ _))
      (hd.comp (.fst _ _)) (hw.comp (.fst _ _)) _ (.snd _ _)
    exact ComputableInPolyTime.listGetDWithInput (hr.comp (.fst _ _))
      ((ComputableInPolyTime.length_list encNat).comp (encWordState_challenges_polyTime (.snd _ _)))
      0
  · exact (PolyBounded.const 8).mul
      ((hr.polyBounded_length.add hp.polyBounded_length).add (.const 2))
  · intro a s next hnext
    obtain ⟨cs, _, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
    let r := (rs a).getD s.challenges.length 0
    have hlen := length_getD_le (rs a) s.challenges.length
    have hval := Polynomial.evalCoeffListMod_lt (p a) r cs
    have hclaim := length_encNat_mono (show Polynomial.evalCoeffListMod (p a) r cs ≤ p a by omega)
    have hlist : (encList encNat (s.challenges ++ [r])).length =
        (encList encNat s.challenges).length + 2 * (encNat r).length + 1 := by
      simp [length_encList, Nat.add_assoc]
    change (encWordState (s.advance (p a) cs r)).length ≤ _
    dsimp only [WordState.advance]
    change (encNat r).length ≤ _ at hlen
    enc_len [encWordState_apply, encWordStateFields]

/-- The transcript obtained by interpreting a static table at the actual public prefixes. -/
@[expose] def transcript (π : List Bool → Bool) (p : ℕ) (external : List ℕ) (d width : ℕ)
    (rs : List ℕ) : WordState :=
  rs.foldl (fun s r => s.advance p (row π external s.challenges d width) r) ⟨[], 0, true⟩

/-- The empty transcript starts at claim zero and has passed every check so far. -/
@[simp] theorem transcript_nil (π : List Bool → Bool) (p : ℕ) (ext : List ℕ) (d w : ℕ) :
    transcript π p ext d w [] = ⟨[], 0, true⟩ := rfl

/-- Appending one challenge advances the state from its prefix. -/
theorem transcript_snoc (π : List Bool → Bool) (p : ℕ) (ext : List ℕ) (d w r : ℕ)
    (rs : List ℕ) :
    transcript π p ext d w (rs ++ [r]) = (transcript π p ext d w rs).advance p
      (row π ext (transcript π p ext d w rs).challenges d w) r := by
  simp [transcript, List.foldl_append]

/-- Each round reveals its single new challenge after fixing its coefficient row. -/
@[simp] theorem transcript_challenges (π : List Bool → Bool) (p : ℕ) (ext : List ℕ) (d w : ℕ)
    (rs : List ℕ) : (transcript π p ext d w rs).challenges = rs := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih => simp [transcript_snoc, WordState.advance, ih]

/-- Every claim returned by a nonzero-modulus transcript is a canonical residue. -/
theorem transcript_claim_lt (π : List Bool → Bool) {p : ℕ} (hp : 0 < p) (ext : List ℕ)
    (d w : ℕ) (rs : List ℕ) : (transcript π p ext d w rs).claim < p := by
  induction rs using List.reverseRecOn with
  | nil => exact hp
  | append_singleton rs r _ =>
    rw [transcript_snoc]
    exact (Polynomial.evalCoeffListMod_lt p r _).trans_le (max_le le_rfl hp)

/-- Under a static proof, the word verifier computes precisely the prefix-dependent transcript. -/
theorem run_verifyRounds (π : List Bool → Bool) (p : ℕ) (ext : List ℕ) (d w : ℕ)
    (rs : List ℕ) :
    (Prover.ofProof π).run (verifyRounds p ext d w rs) () =
      PMF.pure (transcript π p ext d w rs, ()) := by
  let step (s : WordState) := advance p ext d w (rs.getD s.challenges.length 0) s
  have hprefix (i : ℕ) (hi : i ≤ rs.length) :
      (Prover.ofProof π).run (OracleComp.iterate i step ⟨[], 0, true⟩) () =
        PMF.pure (transcript π p ext d w (rs.take i), ()) := by
    induction i with
    | zero => rfl
    | succ i ih =>
      have hi' : i < rs.length := hi
      rw [OracleComp.iterate_succ, Prover.run, ProbOracleComp.runWith_bind]
      change ((Prover.ofProof π).run _ ()).bind _ = _
      rw [ih hi'.le, PMF.pure_bind]
      change (Prover.ofProof π).run (advance _ _ _ _ _ _) () = _
      rw [run_advance, List.take_succ_eq_append_getElem hi', transcript_snoc,
        transcript_challenges, List.length_take, Nat.min_eq_left hi'.le]
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  simpa only [verifyRounds, List.take_length] using hprefix rs.length le_rfl

end Cslib.Complexity.MIP.SumcheckProof
