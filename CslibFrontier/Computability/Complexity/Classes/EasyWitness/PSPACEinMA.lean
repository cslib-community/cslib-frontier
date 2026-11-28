/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EasyWitness.AdviceEval
public import CslibFrontier.Computability.Complexity.Classes.IP.AdviceProver
public import CslibFrontier.Computability.Complexity.Classes.IP.BestReply
public import CslibFrontier.Computability.Complexity.Classes.IP.Shamir
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# `PSPACE ⊆ MA` if `PSPACE ⊆ P/poly`

If `PSPACE ⊆ P/poly`, then `PSPACE ⊆ MA`. This is the step of [ImpagliazzoKabanetsWigderson2002]
that follows [BabaiFortnowNisanWigderson1993]: by `PSPACE = IP`
(`Cslib.Complexity.PSPACE_subset_IP`) a problem in `PSPACE` has an interactive proof, the best reply
of its optimal prover is a function computable in polynomial space
(`Cslib.Complexity.exists_bestReply_of_isInteractiveProof`), and under the hypothesis one
polynomial-time evaluator computes every such function from polynomial-size advice
(`Cslib.Complexity.EasyWitness.exists_adviceEval_of_PSPACE_subset_PPoly`). Merlin sends the
instance, framed, followed by the advice for the best-reply function, so that Arthur can run the
verifier against the prover that answers by the evaluator
(`Cslib.Complexity.mem_MA_of_adviceProver`).

The advice is correct only for inputs up to a length bound, so the best reply is evaluated only on
the histories that can occur: along a run of the verifier against a prover with replies of
polynomial length, the history has at most as many entries as the verifier has rounds, with
messages and replies of bounded length, and two reply functions that agree on these histories are
accepted with the same probability (`Cslib.Complexity.Interaction.acceptProb_ofHistoryFun_congr`).

## Main results

* `Cslib.Complexity.Interaction.acceptProb_ofHistoryFun_congr`: the acceptance probability against
  a history-dependent prover depends only on its replies to the histories that can occur.
* `Cslib.Complexity.EasyWitness.PSPACE_subset_MA_of_PSPACE_subset_PPoly`: if `PSPACE ⊆ P/poly`,
  then `PSPACE ⊆ MA`.

## References

* [R. Impagliazzo, V. Kabanets, A. Wigderson, *In search of an easy witness: exponential time vs.
  probabilistic polynomial time*][ImpagliazzoKabanetsWigderson2002]
* [L. Babai, L. Fortnow, N. Nisan, A. Wigderson, *BPP has subexponential time simulations unless
  EXPTIME has publishable proofs*][BabaiFortnowNisanWigderson1993]
-/

public section

namespace Cslib.Complexity.Interaction

open Cslib.Probability _root_.Turing.MultiTapeTM

section Congr

variable {R : Type} {F : R → WordQueryComp Unit Bool} {D L : ℕ}

/-- Two history-dependent provers that give the same replies on the histories that can occur
(at most `D` entries, messages of length at most `L`, replies of length at most `ρ`) make a bounded
program accept with the same probability, when the first replies with at most `ρ` bits. -/
private theorem acceptFrom_ofHistoryFun_congr (hF : IsBounded F D L) (ρ : ℕ)
    (g g' : History → List Bool → List Bool) (hρ : ∀ h m, (g h m).length ≤ ρ)
    (hgg : ∀ h m, h.length < D → (∀ e ∈ h, e.1.length ≤ L ∧ e.2.length ≤ ρ) → m.length ≤ L →
      g h m = g' h m)
    (r : R) (n : ℕ) (h : History) (hn : h.length + n = D)
    (hh : ∀ e ∈ h, e.1.length ≤ L ∧ e.2.length ≤ ρ) :
    acceptFrom (Prover.ofHistoryFun g) h (after (F r) h) =
      acceptFrom (Prover.ofHistoryFun g') h (after (F r) h) := by
  induction n generalizing h with
  | zero =>
    rw [acceptFrom_after_of_le hF (Prover.ofHistoryFun g) h r (h := h) (by lia),
      acceptFrom_after_of_le hF (Prover.ofHistoryFun g') h r (h := h) (by lia)]
  | succ n ih =>
    rw [acceptFrom_after_eq (Prover.ofHistoryFun g) h (F r) h
        (fun m hm => hF.message r h m hm),
      acceptFrom_after_eq (Prover.ofHistoryFun g') h (F r) h
        (fun m hm => hF.message r h m hm)]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := BitString.mem_shortWords.mp hm
    have hgm := hgg h m (by lia) hh hm'
    simp only [StateT.run, PMF.pure_apply, ite_mul, one_mul, zero_mul]
    rw [tsum_ite_eq, tsum_ite_eq, ← hgm]
    exact ih (h ++ [(m, g h m)]) (by simp only [List.length_append, List.length_singleton]; lia)
      (fun e he => by
        rcases List.mem_append.mp he with he | he
        · exact hh e he
        · rw [List.mem_singleton] at he
          subst he
          exact ⟨hm', hρ h m⟩)

variable {k : ℕ} {Control : Type}

/-- **Acceptance depends only on the replies to the histories that can occur.** If the verifier
`V` is realized by the run of `M` under the clock `t`, and two history-dependent provers, the first
with replies of at most `ρ` bits, agree on every history with fewer than `t` entries, messages of
at most `t` bits and replies of at most `ρ` bits, then `V` is accepted with the same probability
against both. -/
theorem acceptProb_ofHistoryFun_congr (M : _root_.Turing.MultiTapePTM k Bool Control Unit)
    {V : WordOracleComp Unit Bool} {t : ℕ} {x : List Bool}
    (hV : ∀ (S : Type) (oracle : Unit × List Bool → StateT S PMF (List Bool)) s,
      ProbOracleComp.runWith oracle (encBool <$> V) s =
      ProbOracleComp.runWith oracle (M.runOracle t x) s)
    (ρ : ℕ) (g g' : History → List Bool → List Bool) (hρ : ∀ h m, (g h m).length ≤ ρ)
    (hgg : ∀ h m, h.length < t → (∀ e ∈ h, e.1.length ≤ t ∧ e.2.length ≤ ρ) → m.length ≤ t →
      g h m = g' h m) :
    acceptProb V (Prover.ofHistoryFun g) = acceptProb V (Prover.ofHistoryFun g') := by
  have hacc (P : Prover Unit) : acceptProb V P =
      (2 ^ t : ENNReal)⁻¹ * ∑ r, acceptFrom P P.init (some (coinFamily M t x r)) :=
    acceptProb_eq_sum M (by simpa only [ProbOracleComp.runWith_eq_run_interpret] using hV) P
  rw [hacc, hacc]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  simpa only [after_nil] using acceptFrom_ofHistoryFun_congr (isBounded_coinFamily M t x) ρ g g'
    hρ hgg r t [] (by simp) (by simp)

end Congr

end Cslib.Complexity.Interaction

namespace Cslib.Complexity.EasyWitness

open Cslib.Probability Interaction _root_.Turing.MultiTapeTM

/-- The length of the encoded input of a best-reply computation on a history with at most `t`
entries, messages of at most `t` bits and replies of at most `ρ` bits, and a message of at most
`t` bits. -/
private theorem length_encReplyInput_le {t ρ : ℕ} (a : List Bool) (h : History) (q : List Bool)
    (hh : h.length ≤ t) (hent : ∀ e ∈ h, e.1.length ≤ t ∧ e.2.length ≤ ρ) (hq : q.length ≤ t) :
    (encReplyInput encBits (a, (h, q))).length ≤
      2 * a.length + 1 + (2 * (t * (2 * (2 * t + 1 + ρ) + 1)) + 1 + t) := by
  have h1 : (encHistory h).length ≤ h.length * (2 * (2 * t + 1 + ρ) + 1) :=
    length_encList_le (encPair encBits encBits) h (b := 2 * t + 1 + ρ) fun e he => by
      simp only [length_encPair, encBits_apply]
      have := hent e he
      lia
  have h2 : h.length * (2 * (2 * t + 1 + ρ) + 1) ≤ t * (2 * (2 * t + 1 + ρ) + 1) :=
    Nat.mul_le_mul_right _ hh
  simp only [encReplyInput, length_encPair, encBits_apply]
  lia

/-- **`PSPACE ⊆ MA` if `PSPACE ⊆ P/poly`** [ImpagliazzoKabanetsWigderson2002]. Every problem in
`PSPACE` has an interactive proof (`PSPACE ⊆ IP`) whose best reply is computable in polynomial
space; under `PSPACE ⊆ P/poly` a single polynomial-time evaluator computes it from short advice, and
Merlin, sending the instance and the advice, replaces the prover. -/
theorem PSPACE_subset_MA_of_PSPACE_subset_PPoly
    (hS : ∀ L : Language Bool, (L : Set (List Bool)) ∈ PSPACE encBits →
      L ∈ Cslib.Circuits.Boolean.PPoly) :
    PSPACE encBits ⊆ MA encBits := by
  intro A hA
  obtain ⟨verifier, hppt, hproof⟩ := mem_IP.mp (PSPACE_subset_IP encBits hA)
  obtain ⟨bestR, c, d, hbestS, hbestlen, hbestacc⟩ :=
    exists_bestReply_of_isInteractiveProof hppt hproof
  obtain ⟨G, hG, hGev⟩ := exists_adviceEval_of_PSPACE_subset_PPoly hS
  -- the best reply as a function of a word
  let Dec : Decoder (encReplyInput encBits) :=
    Decoder.pair Decoder.bits (Decoder.pair (Decoder.list (Decoder.pair Decoder.bits Decoder.bits))
      Decoder.bits)
  have hf : ComputableInPolySpace (fun x => bestR (Dec.decode x)) encBits encBits :=
    hbestS.comp (ComputableInPolySpace.of_polyTime Dec.computableInPolyTime)
  obtain ⟨ℓ₀, hℓ₀⟩ := hGev _ hf
  -- the coin clock of the verifier
  have hppt' := hppt
  obtain ⟨_, k, Control, hfin, M, c₁, d₁, hreal⟩ := hppt'
  have := hfin
  -- the polynomials: bound on the inputs of the best reply, advice and reply lengths
  obtain ⟨Np, hNp⟩ : ∃ Np : Polynomial ℕ, ∀ n, Np.eval n =
      2 * n + 1 + (2 * ((c₁ * (n + 1) ^ d₁) * (2 * (2 * (c₁ * (n + 1) ^ d₁) + 1 +
        c * (n + 1) ^ d) + 1)) + 1 + c₁ * (n + 1) ^ d₁) :=
    ⟨2 * Polynomial.X + 1 + (2 * ((Polynomial.C c₁ * (Polynomial.X + 1) ^ d₁) *
      (2 * (2 * (Polynomial.C c₁ * (Polynomial.X + 1) ^ d₁) + 1 +
        Polynomial.C c * (Polynomial.X + 1) ^ d) + 1)) + 1 +
        Polynomial.C c₁ * (Polynomial.X + 1) ^ d₁), fun n => by simp⟩
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Polynomial ℕ, ∀ n, ℓ.eval n = 2 * n + 1 + ℓ₀.eval (Np.eval n) :=
    ⟨2 * Polynomial.X + 1 + ℓ₀.comp Np, fun n => by simp [Polynomial.eval_comp]⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Polynomial ℕ, ∀ n, ρ.eval n = c * (n + 1) ^ d :=
    ⟨Polynomial.C c * (Polynomial.X + 1) ^ d, fun n => by simp⟩
  -- the prover computed from the advice
  obtain ⟨G', hG'def⟩ : ∃ G' : List Bool × (History × List Bool) → List Bool, G' = fun z =>
      (G (dropFrame z.1, encReplyInput encBits (unframe z.1, z.2))).take
        (c * ((unframe z.1).length + 1) ^ d) := ⟨_, rfl⟩
  have hG'eval (w : List Bool) (h : History) (q : List Bool) : G' (w, (h, q)) =
      (G (dropFrame w, encReplyInput encBits (unframe w, (h, q)))).take
        (c * ((unframe w).length + 1) ^ d) := by rw [hG'def]
  have hG' : ComputableInPolyTime G' (encPair encBits (encPair encHistory encBits)) encBits := by
    have hu : ComputableInPolyTime (fun z : List Bool × (History × List Bool) => unframe z.1)
        (encPair encBits (encPair encHistory encBits)) encBits :=
      ComputableInPolyTime.unframe.comp (ComputableInPolyTime.fst _ _)
    have hd : ComputableInPolyTime (fun z : List Bool × (History × List Bool) => dropFrame z.1)
        (encPair encBits (encPair encHistory encBits)) encBits :=
      ComputableInPolyTime.dropFrame.comp (ComputableInPolyTime.fst _ _)
    have hr : ComputableInPolyTime (fun z : List Bool × (History × List Bool) => z.2)
        (encPair encBits (encPair encHistory encBits)) (encPair encHistory encBits) :=
      ComputableInPolyTime.snd _ _
    have henc : ComputableInPolyTime
        (fun z : List Bool × (History × List Bool) =>
          encReplyInput encBits (unframe z.1, z.2))
        (encPair encBits (encPair encHistory encBits)) encBits :=
      (ComputableInPolyTime.of_eq (f := encReplyInput encBits) (encOut := encBits)
        fun _ => rfl).comp (hu.prod hr)
    have hcount : ComputableInPolyTime
        (fun z : List Bool × (History × List Bool) => c * ((unframe z.1).length + 1) ^ d)
        (encPair encBits (encPair encHistory encBits)) encUnary :=
      ((ComputableInPolyTime.unary_eval (Polynomial.C c * (Polynomial.X + 1) ^ d)).comp
        (ComputableInPolyTime.length_bits_comp hu)).of_enc_eq fun z => by simp
    rw [hG'def]
    exact ComputableInPolyTime.bitsTakeWithInput (hG.comp (hd.prod henc)) hcount
  refine mem_MA_of_adviceProver hppt (fun a ha P => hproof.sound a ha P) hG' ℓ ρ fun a ha => ?_
  -- the advice of a member
  obtain ⟨w₀, hw₀, hw₀G⟩ := hℓ₀ (Np.eval (encBits a).length)
  have hw : ∀ h q, G' (frame a ++ w₀, (h, q)) =
      (G (w₀, encReplyInput encBits (a, (h, q)))).take (c * ((encBits a).length + 1) ^ d) := by
    intro h q
    rw [hG'eval, unframe_frame_append, dropFrame_frame_append]
    rfl
  have hρw (h : History) (q : List Bool) : (G' (frame a ++ w₀, (h, q))).length ≤
      c * ((encBits a).length + 1) ^ d := by
    rw [hw]
    exact List.length_take_le _ _
  -- on the histories that can occur the prover answers by the best reply
  have hgg : ∀ (h : History) (m : List Bool), h.length < c₁ * ((encBits a).length + 1) ^ d₁ →
      (∀ e ∈ h, e.1.length ≤ c₁ * ((encBits a).length + 1) ^ d₁ ∧
        e.2.length ≤ c * ((encBits a).length + 1) ^ d) →
      m.length ≤ c₁ * ((encBits a).length + 1) ^ d₁ →
      G' (frame a ++ w₀, (h, m)) = bestR (a, (h, m)) := by
    intro h m hlen hent hm
    have hN := length_encReplyInput_le a h m hlen.le hent hm
    have hG0 := hw₀G (encReplyInput encBits (a, (h, m))) (hN.trans (le_of_eq (hNp _).symm))
    rw [hw, hG0, Dec.decode_enc]
    exact List.take_of_length_le (hbestlen (a, (h, m)))
  refine ⟨frame a ++ w₀, ?_, fun h q => (hρw h q).trans_eq (hρ _).symm, ?_⟩
  · rw [hℓ]
    simp only [List.length_append, length_frame, encBits_apply] at hw₀ ⊢
    lia
  · rw [acceptProb_ofHistoryFun_congr M (fun S oracle s => hreal a S oracle s)
      (c * ((encBits a).length + 1) ^ d) (fun h q => G' (frame a ++ w₀, (h, q)))
      (fun h q => bestR (a, (h, q))) (fun h q => hρw h q) hgg]
    exact hbestacc a ha

end Cslib.Complexity.EasyWitness
