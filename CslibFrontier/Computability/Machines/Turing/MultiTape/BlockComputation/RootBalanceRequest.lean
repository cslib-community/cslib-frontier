/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootPredecessorContext
public import CslibFrontier.Computability.PolyTime.SeededRankRequest
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.PolyTime

/-!
# Preparing the external count request after the root balance moves

The verifier retains one prefix containing the schedule, seed and edge count, then appends
the chosen edge, rank and bit-index digits. Only the extracted short fields enter arithmetic.
Another linear pass installs the chosen edge in the shared schedule context. The resulting
pair of words is the complete input to the native count machine.
-/

public section

namespace Turing.MultiTapeTM.RootBalanceRequest

open Cslib Circuits.Boolean.CarryLookahead.Query

/-- Shared root schedule and seed, followed by the binary size of the edge universe. -/
abbrev Public := RootPredecessorQuery.Input × ℕ

/-- Shared prefix encoding before framing it on the physical choice tape. -/
abbrev encPublic := encPair RootPredecessorQuery.encInput encNat

/-- The shared public data and the raw bits chosen in the quantifier prefix. -/
abbrev Input := Public × List Bool

/-- The retained schedule and seed used to evaluate the selected root edge. -/
abbrev rootQuery (a : Input) : RootPredecessorQuery.Input := a.1.1

/-- The number of root edges available to the challenge. -/
abbrev edgeCount (a : Input) : ℕ := a.1.2

/-- The choice word directly follows the framed shared prefix. -/
abbrev encInput := encPair encPublic encBits

/-- Predicate context and count parameters, in the external rank machine's input format. -/
abbrev encOutput := encPair encBits CountingInput.encInput

/-- Arithmetic budget for external assembly. -/
@[expose] def shortSize (a : Input) :=
  RootPredecessorQuery.shortSize (rootQuery a) + (edgeCount a).size + a.2.length + 1

/-- Select the three fields needed to decode the quantified moves. -/
@[expose] def challenge (a : Input) : SeededRankChallenge.Input :=
  ⟨edgeCount a, (rootQuery a).context.labelLength, a.2⟩

/-- Install an edge in the retained graph and seed, beginning the count with candidate zero. -/
@[expose] def withEdge (a : RootPredecessorQuery.Input) (e : ℕ) : RootPredecessorQuery.Input :=
  {a with context := {a.context with edge := e, candidate := 0}}

/-- Root schedule and seed with the edge selected by the challenge dispatcher. -/
@[expose] def selected (a : Input) : RootPredecessorQuery.Input :=
  withEdge (rootQuery a) (SeededRankRequest.run (challenge a)).1

/-- The complete serialized count request. -/
@[expose] def prepare (a : Input) : List Bool × CountingInput.Input :=
  (RootPredecessorContext.word (selected a), (SeededRankRequest.run (challenge a)).2)

private theorem challenge_deg : ComputableInDegree challenge encInput SeededRankChallenge.encInput
    1 1 := by
  have hpub := ComputableInDegree.fst encPublic encBits
  have harg := (ComputableInDegree.fst RootPredecessorQuery.encInput encNat).comp hpub
  have hn := (ComputableInDegree.snd RootPredecessorQuery.encInput encNat).comp hpub
  have ha := SeededPredecessor.encContext_labelLength_deg.comp
    (RootPredecessorQuery.encInput_context_deg.comp harg)
  exact SeededRankChallenge.encInput_mk_deg.comp
    (hn.prod (ha.prod (ComputableInDegree.snd encPublic encBits)))

private theorem update_deg : ComputableInDegree (fun p : Public => withEdge p.1 p.2)
    encPublic RootPredecessorQuery.encInput 1 1 := by
  have harg := ComputableInDegree.fst RootPredecessorQuery.encInput encNat
  have hc := RootPredecessorQuery.encInput_context_deg.comp harg
  open SeededPredecessor in
  have hctx := (encContext_universeSize_deg.comp hc).prod ((encContext_labelLength_deg.comp hc).prod
    ((encContext_c0_deg.comp hc).prod ((encContext_c1_deg.comp hc).prod ((encContext_c2_deg.comp hc
      ).prod ((encContext_c3_deg.comp hc).prod
        ((ComputableInDegree.snd RootPredecessorQuery.encInput encNat).prod
          (ComputableInDegree.const (encMid := encNat) 0)))))))
  exact ((RootPredecessorQuery.encInput_raw_deg.comp harg).prod
    ((RootPredecessorQuery.encInput_copies_deg.comp harg).prod hctx)).of_enc_eq fun _ => rfl

private def install (p : RootPredecessorQuery.Input × (ℕ × CountingInput.Input)) :
    List Bool × CountingInput.Input := (RootPredecessorContext.word (withEdge p.1 p.2.1), p.2.2)

private theorem install_deg : ComputableInDegree install
    (encPair RootPredecessorQuery.encInput SeededRankRequest.encOutput) encOutput 1 1 := by
  have hl := ComputableInDegree.fst RootPredecessorQuery.encInput SeededRankRequest.encOutput
  have hr := ComputableInDegree.snd RootPredecessorQuery.encInput SeededRankRequest.encOutput
  have he := (ComputableInDegree.fst encNat CountingInput.encInput).comp hr
  have hp := (ComputableInDegree.snd encNat CountingInput.encInput).comp hr
  exact (RootPredecessorContext.word_deg.comp (update_deg.comp (hl.prod he))).prod hp

private theorem challenge_size : PolyBounded shortSize (fun a =>
    (SeededRankChallenge.encInput (challenge a)).length) := by
  apply PolyBounded.of_forall_le 2 1
  intro a
  rw [SeededRankChallenge.length_encInput, pow_one]
  unfold challenge shortSize RootPredecessorQuery.shortSize
  simp [SeededPredecessor.encContext_apply, SeededPredecessor.encContextFields,
    encNat_apply]
  omega

/-- Installing the selected edge adds only its binary length and removes the old candidate. -/
theorem shortSize_selected_le (a : Input) : RootPredecessorQuery.shortSize (selected a) ≤
    RootPredecessorQuery.shortSize (rootQuery a) + 2 * (edgeCount a).size := by
  have he := Nat.size_le_size (SeededRankRequest.edge_le (challenge a))
  change (SeededRankRequest.run (challenge a)).1.size ≤ (edgeCount a).size at he
  simp [selected, withEdge, RootPredecessorQuery.shortSize, SeededPredecessor.encContext_apply,
    SeededPredecessor.encContextFields, encNat_apply, Nat.size_eq_bits_len]
  omega

/-- The long schedule is shared with the chosen rank query. -/
@[simp] theorem selected_raw (a : Input) : (selected a).raw = (rootQuery a).raw := rfl

/-- Both numeric count parameters retain short binary encodings after dispatch. -/
theorem parameter_sizes (a : Input) : (prepare a).2.count.size ≤ (edgeCount a).size ∧
    (prepare a).2.query.width.size ≤ (edgeCount a).size + 1 :=
  SeededRankRequest.parameter_sizes (challenge a)

/-- The complete challenge input consists of a fixed number of frames plus the chosen bits. -/
theorem length_encInput_le (a : Input) : (encInput a).length ≤
    8 * (rootQuery a).raw.length + 8 * (shortSize a + 2) := by
  simp only [encInput, encPublic, length_encPair, RootPredecessorQuery.length_encInput,
    encNat_apply, Nat.size_eq_bits_len, encBits_apply, shortSize, RootPredecessorQuery.shortSize,
    rootQuery, edgeCount]
  omega

/-- The full encoded output is linear in the schedule and short input, on every choice word. -/
theorem length_prepare_le (a : Input) : (encOutput (prepare a)).length ≤
    4 * (rootQuery a).raw.length + 12 * shortSize a + 12 := by
  have hw := RootPredecessorContext.length_word_le (selected a)
  rw [RootPredecessorQuery.length_encInput] at hw
  have hs := shortSize_selected_le a
  have h := SeededRankRequest.parameter_sizes (challenge a)
  have hp := CountingInput.length_encInput_le _ (SeededRankRequest.valid_bit (challenge a))
  rw [encOutput, length_encPair]
  change 2 * (RootPredecessorContext.word (selected a)).length + 1 +
    (CountingInput.encInput (SeededRankRequest.run (challenge a)).2).length ≤ _
  change (SeededRankRequest.run (challenge a)).2.count.size ≤ (edgeCount a).size ∧
    (SeededRankRequest.run (challenge a)).2.query.width.size ≤ (edgeCount a).size + 1 at h
  have hraw : (selected a).raw = (rootQuery a).raw := rfl
  unfold shortSize RootPredecessorQuery.shortSize at *
  have hcopies : (selected a).copies = (rootQuery a).copies := rfl
  rw [hraw, hcopies] at hw hs
  omega

/-- A fixed native machine reads the whole challenge tape and writes the external count input
in linear raw length plus a polynomial in the short fields. -/
theorem exists_computableInO : ∃ d, ComputableInO prepare encInput encOutput
    (fun a => (rootQuery a).raw.length + shortSize a ^ d)
    (fun a => (rootQuery a).raw.length + shortSize a ^ d) := by
  have harg := ((ComputableInDegree.fst RootPredecessorQuery.encInput encNat).comp
    (ComputableInDegree.fst encPublic encBits)).inO_one
  obtain ⟨t, s, ht, hs, h⟩ := SeededRankRequest.computableInPolyTime_run.exists_computableInO
  have hall := install_deg.inO_one.comp_linear (harg.prod (h.comp challenge_deg.inO_one))
  let extra (a : Input) := 16 * (shortSize a + 2) + t (challenge a) + s (challenge a)
  have hex : PolyBounded shortSize extra :=
    (((PolyBounded.const 16).mul (PolyBounded.self.add (PolyBounded.const 2))).add
      (ht.comp challenge_size)).add (hs.comp challenge_size)
  obtain ⟨c, d, hd⟩ := hex.exists_le_linear_add_pow (fun a => (rootQuery a).raw.length) 16
    (fun a => by simp [shortSize])
  refine ⟨d, hall.mono c (fun a => ?_) (fun a => ?_)⟩ <;> refine le_trans ?_ (hd a) <;>
    have hh := length_encInput_le a <;> dsimp only [extra] <;>
      simp only [encInput] at hh ⊢ <;> omega

end Turing.MultiTapeTM.RootBalanceRequest
