/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.IP.OptimalProver
public import CslibFrontier.Computability.Complexity.Classes.IP.PSPACE
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryOrder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatPower
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.List.Append
import CslibFrontier.Tactic.EncLen

/-!
# A best reply that is computable

The optimal prover of `Cslib.Complexity.Interaction.optimalProver` answers with a best reply chosen
non-constructively. Here the best reply is the first one, in the enumeration of the short words by
their codes (`Cslib.Complexity.Interaction.decodeWord`, `Cslib.Complexity.Interaction.firstCode`),
that maximizes the value of the extended history, so that it can be computed by a loop over the
codes. The loop evaluates the value of each extended history by the explicit-stack evaluator of
`CslibFrontier.Computability.Complexity.Classes.IP.PSPACE`
(`Cslib.Complexity.Interaction.evaluateWith`), with the leaf values after the history
(`Cslib.Complexity.Interaction.evalFrom`).

## Main definitions

* `Cslib.Complexity.Interaction.firstArgmax`: the first maximizer of a function on an initial
  segment of the naturals, with its maximum.
* `Cslib.Complexity.Interaction.firstBestReply`: the first best reply.

## Main results

* `Cslib.Complexity.Interaction.value_firstBestReply`: the first best reply attains the best value.
* `Cslib.Complexity.Interaction.computableInPolySpace_firstBestReply`: the first best reply within
  polynomial space, computed by a loop over the codes.
* `Cslib.Complexity.Interaction.acceptProb_le_firstBestReply`: the first best reply is an optimal
  prover.
* `Cslib.Complexity.exists_bestReply_of_isInteractiveProof`: a polynomial-space best-reply prover.
-/

@[expose] public section

namespace Cslib.Complexity.Interaction

open Cslib.BitString (increment)

/-! ### The first maximizer -/

/-- The first maximizer of `f` among `0, …, N - 1`, with its value; `(0, 0)` when `N = 0`. -/
def firstArgmax (f : ℕ → ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | i + 1 => if (firstArgmax f i).2 < f i then (i, f i) else firstArgmax f i

/-- The second component of `firstArgmax` is the maximum. -/
theorem firstArgmax_snd (f : ℕ → ℕ) (N : ℕ) :
    (firstArgmax f N).2 = (Finset.range N).sup f := by
  induction N with
  | zero => simp [firstArgmax]
  | succ N ih =>
    rw [Finset.range_add_one, Finset.sup_insert, firstArgmax]
    split_ifs with h
    · rw [ih] at h
      exact (sup_eq_left.mpr h.le).symm
    · rw [ih] at h ⊢
      exact (sup_eq_right.mpr (not_lt.mp h)).symm

/-- A maximizer below `N` attains the maximum, when `N` is positive. -/
theorem firstArgmax_spec (f : ℕ → ℕ) {N : ℕ} (hN : 0 < N) :
    (firstArgmax f N).1 < N ∧ f (firstArgmax f N).1 = (firstArgmax f N).2 := by
  induction N, hN using Nat.le_induction with
  | base =>
    simp only [firstArgmax]
    by_cases h0 : 0 < f 0
    · simp [h0]
    · have : f 0 = 0 := by lia
      simp [this]
  | succ N hN ih =>
    rw [firstArgmax]
    split_ifs with h
    · exact ⟨Nat.lt_succ_self _, rfl⟩
    · exact ⟨ih.1.trans (Nat.lt_succ_self _), ih.2⟩

/-! ### The first best reply -/

section BestReply

variable {R : Type} [Fintype R] (F : R → WordQueryComp Unit Bool) (L : ℕ)

/-- The word coded by the `j`-th code of length `L + 1`. -/
def codeWord (j : ℕ) : List Bool := decodeWord (increment^[j] (firstCode L))

/-- **The first best reply**: the first word, in the order of the codes, that maximizes the value
of the extended history with `n` rounds to go. -/
noncomputable def firstBestReply (n : ℕ) (h : History) (m : List Bool) : List Bool :=
  codeWord L (firstArgmax (fun j => value F L n (h ++ [(m, codeWord L j)])) (codeCount L)).1

/-- The first best reply has length at most `L`. -/
theorem firstBestReply_mem (n : ℕ) (h : History) (m : List Bool) :
    firstBestReply F L n h m ∈ BitString.shortWords L := by
  rw [← image_decodeWord_iterate_firstCode]
  exact Finset.mem_image.mpr ⟨_, Finset.mem_range.mpr
    (firstArgmax_spec _ (codeCount_pos L)).1, rfl⟩

/-- **The first best reply attains the best value.** -/
theorem value_firstBestReply (n : ℕ) (h : History) (m : List Bool) :
    value F L n (h ++ [(m, firstBestReply F L n h m)]) =
      (BitString.shortWords L).sup fun y => value F L n (h ++ [(m, y)]) := by
  set f : ℕ → ℕ := fun j => value F L n (h ++ [(m, codeWord L j)]) with hf
  have hsup : (BitString.shortWords L).sup (fun y => value F L n (h ++ [(m, y)])) =
      (Finset.range (codeCount L)).sup f := by
    rw [← image_decodeWord_iterate_firstCode, Finset.sup_image]
    rfl
  rw [hsup, ← firstArgmax_snd, ← (firstArgmax_spec f (codeCount_pos L)).2]
  rfl

end BestReply

/-! ### Stability of the value in the number of rounds -/

section Stability

variable {R : Type} [Fintype R] {F : R → WordQueryComp Unit Bool} {L D : ℕ}

/-- The first best reply, computed with `D` rounds to go, attains the best value with the rounds
that remain. -/
theorem value_firstBestReply_of_lt (hF : IsBounded F D L) (h : History) (m : List Bool) :
    value F L (D - h.length - 1) (h ++ [(m, firstBestReply F L D h m)]) =
      (BitString.shortWords L).sup fun y => value F L (D - h.length - 1) (h ++ [(m, y)]) := by
  have hv (y : List Bool) : value F L (D - h.length - 1) (h ++ [(m, y)]) =
      value F L D (h ++ [(m, y)]) := by
    rw [value_eq_of_le hF _ _ (by simp only [List.length_append, List.length_singleton]; lia),
      value_eq_of_le hF D _ (by simp only [List.length_append, List.length_singleton]; lia)]
  simp only [hv]
  exact value_firstBestReply F L D h m

end Stability

/-! ### The first best reply within polynomial space -/

section Loop

open _root_.Turing _root_.Turing.MultiTapeTM ComputableInPolyTime

attribute [local fun_prop] binary_max' binary_min' computableInPolyTime_firstCode

variable {α : Type}

/-- The state of the loop over the codes: the input, the current code, the code of the best reply
so far and its value. -/
private abbrev BestState (α : Type) := (α × History × List Bool) × List Bool × List Bool × ℕ

/-- The input of the best-reply computation, in the state of the loop. -/
private abbrev BestState.query (s : BestState α) : α × History × List Bool := s.1

/-- The current code of the state of the loop. -/
private abbrev BestState.code (s : BestState α) : List Bool := s.2.1

/-- The code of the best reply so far, in the state of the loop. -/
private abbrev BestState.bestCode (s : BestState α) : List Bool := s.2.2.1

/-- The value of the best reply so far, in the state of the loop. -/
private abbrev BestState.bestValue (s : BestState α) : ℕ := s.2.2.2

/-- States of the loop, encoded by their fields. -/
private abbrev encBestState (enc : α ↪ List Bool) : BestState α ↪ List Bool :=
  encPair (encReplyInput enc) (encPair encBits (encPair encBits encNat))

variable (enc : α ↪ List Bool) {k : ℕ} {Control : Type}
  (M : MultiTapePTM k Bool Control Unit) (fuel : α → ℕ)

/-- One step of the loop over the codes: evaluate the value of the reply of the current code,
keep the best code so far unless the new value is larger, and move to the next code. -/
private def bestStep (s : BestState α) : BestState α :=
  if decide (s.bestValue < evalFrom enc M fuel
      (s.query.1, s.query.2.1 ++ [(s.query.2.2, decodeWord s.code)])) then
    (s.query, BitString.increment s.code, s.code,
      evalFrom enc M fuel
        (s.query.1, s.query.2.1 ++ [(s.query.2.2, decodeWord s.code)]))
  else (s.query, BitString.increment s.code, s.bestCode, s.bestValue)

/-- The start of the loop: the first code, which is the best so far, with value `0`. -/
private def bestInit (p : α × History × List Bool) : BestState α :=
  (p, firstCode (fuel p.1), firstCode (fuel p.1), 0)

/-- The result of the loop: the word of the best code after all the codes. -/
private def bestReplyEval (p : α × History × List Bool) : List Bool :=
  decodeWord ((bestStep enc M fuel)^[codeCount (fuel p.1)] (bestInit fuel p)).bestCode

/-- The value of the reply of the `j`-th code. -/
private noncomputable def bestF (p : α × History × List Bool) (j : ℕ) : ℕ :=
  value (coinFamily M (fuel p.1) (enc p.1)) (fuel p.1) (fuel p.1)
    (p.2.1 ++ [(p.2.2, codeWord (fuel p.1) j)])

/-- After `j` steps the loop holds the `j`-th code, and the first best code and value among the
earlier ones. -/
private theorem iterate_bestStep (p : α × History × List Bool) (j : ℕ) :
    (bestStep enc M fuel)^[j] (bestInit fuel p) =
      (p, BitString.increment^[j] (firstCode (fuel p.1)),
        BitString.increment^[(firstArgmax (bestF enc M fuel p) j).1] (firstCode (fuel p.1)),
        (firstArgmax (bestF enc M fuel p) j).2) := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have hval : evalFrom enc M fuel (p.1, p.2.1 ++ [(p.2.2, decodeWord
        (BitString.increment^[j] (firstCode (fuel p.1))))]) = bestF enc M fuel p j :=
      evalFrom_eq enc M fuel _
    rw [Function.iterate_succ_apply', ih]
    by_cases h : (firstArgmax (bestF enc M fuel p) j).2 < bestF enc M fuel p j
    · simp [bestStep, hval, firstArgmax, h, Function.iterate_succ_apply']
    · simp [bestStep, hval, firstArgmax, h, Function.iterate_succ_apply']

/-- **The loop computes the first best reply.** -/
private theorem bestReplyEval_eq (p : α × History × List Bool) :
    bestReplyEval enc M fuel p =
      firstBestReply (coinFamily M (fuel p.1) (enc p.1)) (fuel p.1) (fuel p.1) p.2.1 p.2.2 := by
  rw [bestReplyEval, iterate_bestStep]
  rfl

variable {enc fuel}

/-- **The first best reply within polynomial space**, as a function of the instance, the history and
the message. -/
private theorem computableInPolySpace_bestReplyEval [Finite Control] [Inhabited α]
    (hfuel : ComputableInPolyTime fuel enc encUnary) :
    ComputableInPolySpace (bestReplyEval enc M fuel) (encReplyInput enc) encBits := by
  have hfuelP : ComputableInPolyTime (fun p : α × History × List Bool => fuel p.1)
      (encReplyInput enc) encUnary := hfuel.comp (fst _ _)
  have hdec := computableInPolyTime_decodeWord
  have hval : ComputableInPolySpace (fun s : BestState α =>
      evalFrom enc M fuel (s.1.1, s.1.2.1 ++ [(s.1.2.2, decodeWord s.2.1)]))
      (encBestState enc) encNat := by
    refine (computableInPolySpace_evalFrom M hfuel).comp (ComputableInPolySpace.of_polyTime ?_)
    fun_prop
  have hv : ComputableInPolyTime (fun s : BestState α => s.2.2.2) (encBestState enc) encNat := by
    fun_prop
  have hcond := (ComputableInPolySpace.of_polyTime binary_lt).comp
    ((ComputableInPolySpace.of_polyTime hv).prod hval)
  have hs1 : ComputableInPolyTime (fun s : BestState α => s.1) (encBestState enc)
      (encReplyInput enc) := by fun_prop
  have hu : ComputableInPolyTime (fun s : BestState α => s.2.1) (encBestState enc) encBits := by
    fun_prop
  have hinc : ComputableInPolyTime (fun s : BestState α => BitString.increment s.2.1)
      (encBestState enc) encBits := ComputableInPolyTime.increment.comp hu
  have hB : ComputableInPolyTime (fun s : BestState α =>
      (s.1, BitString.increment s.2.1, s.2.2.1, s.2.2.2)) (encBestState enc)
      (encBestState enc) := by
    fun_prop
  have hstep : ComputableInPolySpace (bestStep enc M fuel) (encBestState enc)
      (encBestState enc) :=
    (ComputableInPolySpace.ite hcond
      ((ComputableInPolySpace.of_polyTime hs1).prod ((ComputableInPolySpace.of_polyTime hinc).prod
        ((ComputableInPolySpace.of_polyTime hu).prod hval)))
      (ComputableInPolySpace.of_polyTime hB)).congr fun s => rfl
  have hn : ComputableInPolyTime (fun p : α × History × List Bool => codeCount (fuel p.1))
      (encReplyInput enc) encNat := by
    simp only [codeCount]
    exact binary_sub' (binary_two_pow.comp (unary_succ.comp hfuelP)) (const (encOut := encNat) 1)
  have hinit : ComputableInPolyTime (bestInit fuel) (encReplyInput enc) (encBestState enc) := by
    unfold bestInit
    fun_prop
  have hL (q : α × History × List Bool) (a b : List Bool) (v : ℕ) :
      (encBestState enc (q, a, b, v)).length = 2 * (encReplyInput enc q).length + 1 +
        (2 * a.length + 1 + (2 * b.length + 1 + (encNat v).length)) := by
    simp only [length_encPair, encBits_apply]
  have hit := ComputableInPolySpace.iterate hn (ComputableInPolySpace.of_polyTime hinit) hstep
    (B := fun p => 2 * (encReplyInput enc p).length + 5 * fuel p.1 + 8)
    (by growth_poly) (fun p j _ => by
      rw [iterate_bestStep, hL]
      have hlen (i : ℕ) : (BitString.increment^[i] (firstCode (fuel p.1))).length =
          fuel p.1 + 1 := by
        induction i with
        | zero => simp [firstCode]
        | succ i ih => rw [Function.iterate_succ_apply']; simpa using ih
      have hvle : (firstArgmax (bestF enc M fuel p) j).2 ≤ 2 ^ fuel p.1 := by
        rw [firstArgmax_snd]
        refine Finset.sup_le fun i _ => ?_
        unfold bestF
        exact (value_le_card _ _).trans ((Finset.card_le_univ _).trans (by simp))
      have hv' := length_encNat_le_of_le_two_pow hvle
      rw [hlen, hlen]
      lia)
  have hproj : ComputableInPolyTime (fun s : BestState α => s.2.2.1) (encBestState enc)
      encBits := by fun_prop
  exact ((ComputableInPolySpace.of_polyTime hdec).comp
    ((ComputableInPolySpace.of_polyTime hproj).comp hit)).congr fun p => rfl

end Loop

section Optimal

open Cslib.Probability _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {Control : Type}

/-- **The first best reply is an optimal prover.** If the verifier `V` is realized, against every
stateful prover, by the run of the oracle machine `M` under the clock `fuel a`, then the
deterministic prover answering every message with the first best reply (`firstBestReply`, with
`fuel a` rounds to go) is accepted with probability at least that of every prover. -/
theorem acceptProb_le_firstBestReply {V : α → WordOracleComp Unit Bool}
    {M : MultiTapePTM k Bool Control Unit} {fuel : α → ℕ}
    (hV : ∀ a (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (encBool <$> V a) s =
      ProbOracleComp.runWith oracle (M.runOracle (fuel a) (enc a)) s)
    (a : α) (P : Prover Unit) :
    acceptProb (V a) P ≤ acceptProb (V a) (Prover.ofHistoryFun fun h q =>
      firstBestReply (coinFamily M (fuel a) (enc a)) (fuel a) (fuel a) h q) := by
  set t := fuel a
  have hbounded := isBounded_coinFamily M t (enc a)
  have hacc (P : Prover Unit) : acceptProb (V a) P =
      (2 ^ t : ENNReal)⁻¹ * ∑ r, acceptFrom P P.init (some (coinFamily M t (enc a) r)) :=
    acceptProb_eq_sum M (by
      simpa only [ProbOracleComp.runWith_eq_run_interpret] using hV a) P
  rw [hacc P, hacc, sum_acceptFrom_ofHistoryFun hbounded _ fun h m _ =>
    value_firstBestReply_of_lt hbounded h m]
  exact mul_le_mul_right (sum_acceptFrom_le_value hbounded P) _

/-- **The first best reply within polynomial space**: the function sending an instance, a history
and a message to the first best reply (`firstBestReply` with `fuel a` rounds to go) is computable
within polynomial space, when the number of coins `fuel a` is computable in polynomial time. -/
theorem computableInPolySpace_firstBestReply [Finite Control] [Inhabited α]
    (M : MultiTapePTM k Bool Control Unit) {fuel : α → ℕ}
    (hfuel : ComputableInPolyTime fuel enc encUnary) :
    ComputableInPolySpace (fun p : α × (History × List Bool) =>
      firstBestReply (coinFamily M (fuel p.1) (enc p.1)) (fuel p.1) (fuel p.1) p.2.1 p.2.2)
      (encReplyInput enc) encBits :=
  (computableInPolySpace_bestReplyEval M hfuel).congr fun p => bestReplyEval_eq enc M fuel p

end Optimal

end Cslib.Complexity.Interaction

namespace Cslib.Complexity

open Cslib.Probability Interaction _root_.Turing _root_.Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {k : ℕ} {Control : Type}

/-- **A best-reply prover computable in polynomial space.** For a problem with an interactive proof
whose verifier is strict oracle PPT, there is a function `bestR` of the instance, the history and
the message, computable within polynomial space, with polynomially long replies, such that for every
member `a` the deterministic prover answering the message `q` after the history `h` with
`bestR (a, (h, q))` is accepted with probability at least `2 / 3`. It is the first best reply of the
proof of `IP ⊆ PSPACE` (`Cslib.Complexity.Interaction.firstBestReply`): by
`Cslib.Complexity.Interaction.acceptProb_le_firstBestReply` it is accepted at least as often as
every prover, in particular as the honest one. -/
theorem exists_bestReply_of_isInteractiveProof {A : Set α}
    {verifier : α → WordOracleComp Unit Bool} (hppt : IsOraclePPTOn enc encBool verifier)
    (hA : IsInteractiveProof verifier A (2 / 3) (1 / 3)) :
    ∃ (bestR : α × (History × List Bool) → List Bool) (c d : ℕ),
      ComputableInPolySpace bestR (encReplyInput enc) encBits ∧
      (∀ p, (bestR p).length ≤ c * ((enc p.1).length + 1) ^ d) ∧
      ∀ a ∈ A, 2 / 3 ≤ acceptProb (verifier a)
        (Prover.ofHistoryFun fun h q => bestR (a, (h, q))) := by
  rcases isEmpty_or_nonempty α with hα | hα
  · exact ⟨fun _ => [], 0, 0, ComputableInPolySpace.of_polyTime (ComputableInPolyTime.const []),
      fun p => isEmptyElim p.1, fun a => isEmptyElim a⟩
  let _ : Inhabited α := Classical.inhabited_of_nonempty hα
  obtain ⟨_, k, Control, _, M, c, d, hreal⟩ := hppt
  set fuel : α → ℕ := fun a => c * ((enc a).length + 1) ^ d
  have hfuel : ComputableInPolyTime fuel enc encUnary := by
    have hlen : ComputableInPolyTime (fun a => (enc a).length) enc encUnary := by fun_prop
    exact ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
      hlen).of_enc_eq fun a => by simp [fuel]
  refine ⟨_, c, d, computableInPolySpace_firstBestReply M hfuel, fun p => ?_, fun a ha => ?_⟩
  · exact BitString.mem_shortWords.mp (Interaction.firstBestReply_mem _ _ _ _ _)
  · obtain ⟨P, hP⟩ := hA.complete a ha
    exact hP.trans (acceptProb_le_firstBestReply (fun a S oracle s => hreal a S oracle s) a P)

end Cslib.Complexity
