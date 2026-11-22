/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.PH.OracleTranscript
public import CslibFrontier.Computability.Complexity.Classes.PH.BoundedConjunction
public import CslibFrontier.Computability.Complexity.Classes.Oracle.Monotone
import CslibFrontier.Computability.Complexity.Classes.Oracle.CanonicalReplay
import CslibFrontier.Computability.Complexity.Classes.Oracle.Lowness
import CslibFrontier.Computability.Complexity.Classes.Oracle.Complement
import CslibFrontier.Computability.Complexity.Classes.PH.Closure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Oracle characterization of the polynomial hierarchy

For every positive `k`, `Σₖ₊₁ = NP^{Σₖ}`. The oracle computation is the native strict
polynomial-time word-query program; NP uses an oracle verifier with an exact polynomial
certificate length. Guess the verifier's instruction-indexed query transcript, including both
positive and negative replies. Positive replies are checked in `Σₖ`, negative replies in `Πₖ`;
local instructions carry a `false` transcript bit. Polynomially bounded conjunction and
existential projection then place the computation in `Σₖ₊₁`.

The reverse inclusion peels the first existential block and queries the complement of the
remaining `Πₖ` predicate. The union over oracles can be replaced by any Karp-complete raw-word
`Σₖ` language.

This is [Arora–Barak, web draft 2007-01-08, Theorem 5.15, printed p. 98, Exercise 5 §7,
printed p. 100][AroraBarak07], and [Goldreich, January 2007 draft, Proposition 3.11,
printed pp. 126–128, Exercises 3.9 and 3.10(2), printed pp. 134–135][Goldreich2007DraftR2].
## Main results

* `SigmaP_succ_eq_iUnion_NPWithOracle`: the union-over-oracles characterization.
* `SigmaPComplete.SigmaP_succ_eq_NPWithOracle`: the complete-oracle characterization.
* `SigmaP_union_PiP_subset_iUnion_PWithOracle`,
  `iUnion_PWithOracle_subset_SigmaP_succ_inter_PiP_succ`: deterministic oracle bounds.

All theorems quantify over arbitrary instance encodings; oracles are total bit-string languages,
with malformed encodings outside encoded problem languages.
-/

public section
namespace Cslib.Complexity
open Turing.MultiTapeTM
open _root_.Turing _root_.Turing.MultiTapePTM
variable {α β : Type} {output : β ↪ List Bool} {enc : α ↪ List Bool} {k : ℕ} {A : Set (List Bool)}

/-- The positive replies of an oracle transcript are certified in the oracle's existential
level, without adding an alternation. -/
theorem oracleTranscriptYes_mem_SigmaP {t : ℕ} {Control Operation : Type}
    [DecidableEq Operation] [Finite Control] [Finite Operation]
    {machine : MultiTapePTM t Bool Control Operation} (hA : A ∈ SigmaP k encBits) :
    oracleTranscriptYes machine enc A ∈ SigmaP k (encPair enc encBits) := by
  have hreplay : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ => ((enc y.1.1, y.1.2), y.2))
      (encPair (encPair enc encBits) encUnary) (encPair (encPair encBits encBits) encUnary) := by
    fun_prop
  have hquery := machine.replayPrefix_isQuery_pt.comp hreplay
  have hreq := machine.replayPrefix_pendingRequest_pt.comp hreplay
  let G : Set ((α × List Bool) × ℕ) := {y | y.1.2.getD y.2 false = false}
  let Q : Set ((α × List Bool) × ℕ) :=
    {y | (machine.pendingQuery (machine.replayPrefix (enc y.1.1) y.1.2 y.2)).isSome = true}
  have hG : G ∈ P (encPair (encPair enc encBits) encUnary) :=
    ⟨fun y => !y.1.2.getD y.2 false, by fun_prop, by simp [G]⟩
  have hQ : Q ∈ P (encPair (encPair enc encBits) encUnary) :=
    ⟨_, hquery, fun _ => Iff.rfl⟩
  have hR := (show PolyTimeReducible _ encBits
    {y : (α × List Bool) × ℕ |
      machine.pendingRequest (machine.replayPrefix (enc y.1.1) y.1.2 y.2) ∈ A} A from
    ⟨_, hreq, fun _ => Iff.rfl⟩).mem_SigmaP hA
  have hall := mem_SigmaP_of_forall_lt (by fun_prop : ComputableInPolyTime
    (fun x : α × List Bool => x.2.length) (encPair enc encBits) encUnary)
    (union_mem_SigmaP (SigmaP_mono (Nat.zero_le k) (SigmaP_zero ▸ hG))
      (inter_mem_SigmaP (SigmaP_mono (Nat.zero_le k) (SigmaP_zero ▸ hQ)) hR))
  convert hall using 1
  ext x
  simp only [mem_oracleTranscriptYes, Set.mem_ofPred_eq, Set.mem_union, Set.mem_inter_iff,
    G, Q]
  refine forall₂_congr fun i _ => ?_
  cases x.2.getD i false <;> simp

/-- Negative replies are certified in the dual universal level. They cannot be checked using
only positive certificates for the oracle. -/
theorem oracleTranscriptNo_mem_PiP {t : ℕ} {Control Operation : Type}
    [DecidableEq Operation] [Finite Control] [Finite Operation]
    {machine : MultiTapePTM t Bool Control Operation} (hA : A ∈ SigmaP k encBits) :
    oracleTranscriptNo machine enc A ∈ PiP k (encPair enc encBits) := by
  have hreplay : ComputableInPolyTime
      (fun y : (α × List Bool) × ℕ => ((enc y.1.1, y.1.2), y.2))
      (encPair (encPair enc encBits) encUnary) (encPair (encPair encBits encBits) encUnary) := by
    fun_prop
  have hquery := machine.replayPrefix_isQuery_pt.comp hreplay
  have hreq := machine.replayPrefix_pendingRequest_pt.comp hreplay
  let G : Set ((α × List Bool) × ℕ) := {y | y.1.2.getD y.2 false = true ∨
    (machine.pendingQuery (machine.replayPrefix (enc y.1.1) y.1.2 y.2)).isSome = false}
  have hbit := ComputableInPolyTime.bitsGetDWithInput
    (ComputableInPolyTime.fst (encPair enc encBits) encUnary).snd'
    (ComputableInPolyTime.snd (encPair enc encBits) encUnary) false
  have hG : G ∈ P (encPair (encPair enc encBits) encUnary) :=
    ⟨fun y => y.1.2.getD y.2 false ||
      !(machine.pendingQuery (machine.replayPrefix (enc y.1.1) y.1.2 y.2)).isSome,
      ComputableInPolyTime.bool_or' hbit (ComputableInPolyTime.bool_not.comp hquery),
      by simp [G]⟩
  have hR := (show PolyTimeReducible _ encBits
    {y : (α × List Bool) × ℕ |
      machine.pendingRequest (machine.replayPrefix (enc y.1.1) y.1.2 y.2) ∈ Aᶜ} Aᶜ from
    ⟨_, hreq, fun _ => Iff.rfl⟩).mem_PiP (compl_mem_PiP_of_mem_SigmaP hA)
  have hall := mem_PiP_of_forall_lt (by fun_prop : ComputableInPolyTime
    (fun x : α × List Bool => x.2.length) (encPair enc encBits) encUnary)
    (union_mem_PiP (PiP_mono (Nat.zero_le k) (PiP_zero ▸ hG)) hR)
  convert hall using 1
  ext x
  simp only [mem_oracleTranscriptNo, Set.mem_ofPred_eq, Set.mem_union, G, Set.mem_compl_iff]
  refine forall₂_congr fun i _ => ?_
  cases x.2.getD i false <;>
    cases (machine.pendingQuery (machine.replayPrefix (enc x.1) x.2 i)).isSome <;> simp

open Classical in
/-- Polynomial-time predicates of encoded oracle outputs lie one level above the oracle.
Both positive and negative replies are certified by the guessed transcript. -/
theorem ComputableInPolyTimeWithOracle.encoded_mem_SigmaP_succ {f : α → β}
    {P : α × List Bool → Bool} (hA : A ∈ SigmaP k encBits)
    (hf : ComputableInPolyTimeWithOracle A f enc output)
    (hP : ComputableInPolyTime P (encPair enc encBits) encBool) :
    {a | P (a, output (f a)) = true} ∈ SigmaP (k + 1) enc := by
  obtain ⟨t, m, machine, T, hout⟩ := hf.exists_replayOutput
  -- the replayed output of a transcript satisfies `P`
  let good : Set (α × List Bool) :=
    {x | P (x.1, machine.replayOutput (enc x.1) x.2) = true}
  have hgood : good ∈ SigmaP (k + 1) (encPair enc encBits) := by
    have hgoodP : good ∈ Complexity.P (encPair enc encBits) :=
      ⟨fun x => P (x.1, machine.replayOutput (enc x.1) x.2), hP.comp
        ((ComputableInPolyTime.fst _ _).prod
          (machine.computableInPolyTime_replayOutput.comp
            (g := fun x : α × List Bool => (enc x.1, x.2)) (by fun_prop))), fun _ => Iff.rfl⟩
    rw [← SigmaP_zero] at hgoodP
    exact SigmaP_mono (Nat.zero_le _) hgoodP
  have hYes : oracleTranscriptYes machine enc A ∈ SigmaP (k + 1) (encPair enc encBits) :=
    SigmaP_subset_SigmaP_succ k (oracleTranscriptYes_mem_SigmaP hA)
  have hNo : oracleTranscriptNo machine enc A ∈ SigmaP (k + 1) (encPair enc encBits) :=
    PiP_subset_SigmaP_succ k (oracleTranscriptNo_mem_PiP hA)
  have hB := inter_mem_SigmaP hgood (inter_mem_SigmaP hYes hNo)
  convert mem_SigmaP_of_exists (by omega) hB T using 1
  ext a
  simp only [Set.mem_ofPred_eq]
  let g : List Bool → Bool := fun q => decide (q ∈ A)
  constructor
  · intro h
    refine ⟨machine.oracleReplies g (T.eval (enc a).length) (enc a),
      machine.length_oracleReplies _ _ _, ?_,
      mem_oracleTranscriptYes_inter_oracleTranscriptNo.mpr ?_⟩
    · change P (a, _) = true
      rwa [hout]
    · rw [machine.length_oracleReplies]
  · rintro ⟨t, ht, hP', hYN⟩
    have heq : t = machine.oracleReplies g t.length (enc a) :=
      mem_oracleTranscriptYes_inter_oracleTranscriptNo.mp hYN
    change P (a, machine.replayOutput (enc a) t) = true at hP'
    rwa [heq, ht, hout] at hP'

/-- Polynomial time with a `Σₖ` oracle lies in `Σₖ₊₁`. -/
theorem PWithOracle_subset_SigmaP_succ (hA : A ∈ SigmaP k encBits) :
    PWithOracle A enc ⊆ SigmaP (k + 1) enc := by
  rintro L ⟨f, hf, hL⟩
  have hP : ComputableInPolyTime (fun x : α × List Bool => decide (x.2 = [true]))
      (encPair enc encBits) encBool := by fun_prop
  convert hf.encoded_mem_SigmaP_succ hA hP using 1
  ext a
  simp [hL a, encBool_apply]

/-- An oracle NP verifier uses an existential certificate, which merges with the first block
of the transcript simulation. Thus `NP^A ⊆ Σₖ₊₁` for `A ∈ Σₖ`. -/
theorem NPWithOracle_subset_SigmaP_succ (hA : A ∈ SigmaP k encBits) :
    NPWithOracle A enc ⊆ SigmaP (k + 1) enc := by
  rintro L ⟨p, V, hV, hL⟩
  have hB : {x | V x = true} ∈ PWithOracle A (encPair enc encBits) :=
    ⟨V, hV, fun _ => Iff.rfl⟩
  convert mem_SigmaP_of_exists (by omega) (PWithOracle_subset_SigmaP_succ hA hB) p using 1
  exact Set.ext hL

/-- Every `Σₖ` or `Πₖ` problem is decidable with some raw-word `Σₖ` oracle. -/
theorem SigmaP_union_PiP_subset_iUnion_PWithOracle (k : ℕ) (enc : α ↪ List Bool) :
    SigmaP k enc ∪ PiP k enc ⊆ ⋃ O ∈ SigmaP k encBits, PWithOracle O enc := by
  have hs : ∀ {B : Set α}, B ∈ SigmaP k enc →
      B ∈ ⋃ O ∈ SigmaP k encBits, PWithOracle O enc := by
    intro B hB
    obtain ⟨O, hO, rfl⟩ := exists_mem_SigmaP_encBits_preimage hB
    exact Set.mem_iUnion₂.mpr ⟨O, hO,
      (show PolyTimeReducible enc encBits (enc ⁻¹' O) O from
        ⟨enc, by fun_prop, fun _ => Iff.rfl⟩).mem_PWithOracle (mem_PWithOracle_self O)⟩
  rintro B (hB | hB)
  · exact hs hB
  · obtain ⟨O, hO, hBO⟩ := Set.mem_iUnion₂.mp (hs (compl_mem_SigmaP_of_mem_PiP hB))
    exact Set.mem_iUnion₂.mpr ⟨O, hO, by
      simpa only [compl_compl] using compl_mem_PWithOracle hBO⟩

/-- **Goldreich Proposition 3.11:** for `k ≥ 1`, the next existential level is oracle NP
with an oracle from the current existential level. -/
theorem SigmaP_succ_eq_iUnion_NPWithOracle (k : ℕ) (enc : α ↪ List Bool) :
    SigmaP (k + 1) enc = ⋃ O ∈ SigmaP k encBits, NPWithOracle O enc := by
  apply Set.Subset.antisymm
  · intro L hL
    obtain ⟨p, B, hB, rfl⟩ := mem_SigmaP_succ_iff.mp hL
    obtain ⟨O, hO, V, hV, hBV⟩ := Set.mem_iUnion₂.mp
      (SigmaP_union_PiP_subset_iUnion_PWithOracle k (encPair enc encBits) (Or.inr hB))
    exact Set.mem_iUnion₂.mpr ⟨O, hO, p, V, hV, fun a => by
      simp only [Set.mem_ofPred_eq, hBV]⟩
  · exact Set.iUnion₂_subset fun O hO => NPWithOracle_subset_SigmaP_succ hO

/-- **Goldreich Exercise 3.9:** deterministic access to a `Σₖ` oracle contains `Σₖ ∪ Πₖ`
and lies inside `Σₖ₊₁ ∩ Πₖ₊₁`. -/
theorem iUnion_PWithOracle_subset_SigmaP_succ_inter_PiP_succ (k : ℕ)
    (enc : α ↪ List Bool) :
    (⋃ O ∈ SigmaP k encBits, PWithOracle O enc) ⊆ SigmaP (k + 1) enc ∩ PiP (k + 1) enc := by
  refine Set.iUnion₂_subset fun O hO L hL => ⟨PWithOracle_subset_SigmaP_succ hO hL, ?_⟩
  simpa only [compl_compl] using compl_mem_PiP_of_mem_SigmaP
    (PWithOracle_subset_SigmaP_succ hO (compl_mem_PWithOracle hL))

/-- **Goldreich Exercise 3.9(2), oracle duality:** `P^{Πₖ} = P^{Σₖ}`. Negating each
oracle reply does not require either oracle class to be closed under complement. -/
theorem iUnion_PWithOracle_PiP_eq (k : ℕ) (enc : α ↪ List Bool) :
    (⋃ O ∈ PiP k encBits, PWithOracle O enc) =
      ⋃ O ∈ SigmaP k encBits, PWithOracle O enc := by
  apply Set.Subset.antisymm
  · refine Set.iUnion₂_subset fun O hO => ?_
    rw [← PWithOracle_compl_eq O enc]
    exact Set.subset_iUnion₂_of_subset Oᶜ (compl_mem_SigmaP_of_mem_PiP hO) le_rfl
  · refine Set.iUnion₂_subset fun O hO => ?_
    rw [← PWithOracle_compl_eq O enc]
    exact Set.subset_iUnion₂_of_subset Oᶜ (compl_mem_PiP_of_mem_SigmaP hO) le_rfl

/-- A Karp-complete raw-word `Σₖ` oracle decides every `Σₖ` and `Πₖ` problem in polynomial
time: reduce to the oracle, and complement the output for the universal level. -/
theorem SigmaPComplete.SigmaP_union_PiP_subset_PWithOracle (hA : SigmaPComplete k encBits A)
    (enc : α ↪ List Bool) : SigmaP k enc ∪ PiP k enc ⊆ PWithOracle A enc := by
  intro B hB
  rcases hB with hB | hB
  · exact (hA.2 enc B hB).mem_PWithOracle (mem_PWithOracle_self A)
  · simpa only [compl_compl] using compl_mem_PWithOracle
      ((hA.2 enc Bᶜ (compl_mem_SigmaP_of_mem_PiP hB)).mem_PWithOracle
        (mem_PWithOracle_self A))

/-- **Goldreich Exercise 3.10(2), general complete-oracle principle:** the union `P^{Σₖ}`
is polynomial time with any Karp-complete raw-word `Σₖ` oracle. -/
theorem SigmaPComplete.iUnion_PWithOracle_eq (hA : SigmaPComplete k encBits A)
    (enc : α ↪ List Bool) :
    (⋃ O ∈ SigmaP k encBits, PWithOracle O enc) = PWithOracle A enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun O hO => (hA.2 encBits O hO).PWithOracle_subset enc
  · exact Set.subset_iUnion₂_of_subset A hA.1 le_rfl

/-- A complete `Σₖ` oracle also replaces the union of oracle NP classes. -/
theorem SigmaPComplete.iUnion_NPWithOracle_eq (hA : SigmaPComplete k encBits A)
    (enc : α ↪ List Bool) :
    (⋃ O ∈ SigmaP k encBits, NPWithOracle O enc) = NPWithOracle A enc := by
  apply Set.Subset.antisymm
  · exact Set.iUnion₂_subset fun O hO => (hA.2 encBits O hO).NPWithOracle_subset enc
  · exact Set.subset_iUnion₂_of_subset A hA.1 le_rfl

/-- **Arora–Barak Theorem 5.15 / Goldreich Proposition 3.11, complete-oracle form:**
`Σₖ₊₁ = NP^A` for any Karp-complete raw-word `Σₖ` oracle, `k ≥ 1`. -/
theorem SigmaPComplete.SigmaP_succ_eq_NPWithOracle
    (hA : SigmaPComplete k encBits A) (enc : α ↪ List Bool) :
    SigmaP (k + 1) enc = NPWithOracle A enc := by
  rw [SigmaP_succ_eq_iUnion_NPWithOracle, hA.iUnion_NPWithOracle_eq]

end Cslib.Complexity
