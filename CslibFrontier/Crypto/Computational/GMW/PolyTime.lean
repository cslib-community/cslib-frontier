/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.OracleSimulation
public import CslibFrontier.Crypto.Computational.GMW.Protocol
public import CslibFrontier.Crypto.Encoding
public import CslibFrontier.Crypto.Game.Retry
public import CslibFrontier.Logics.Propositional.CNF.Encoding
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Tactic.PPT

/-!
# Polynomial-time and PPT certificates for the 3-copy GMW protocol

This module registers `@[fun_prop]` polynomial-time and strict-(oracle-)PPT certificates for the
3-copy masked-3SAT GMW protocol gadgets defined in
`CslibFrontier.Crypto.Computational.GMW.Protocol`,
proves that `runTwoRound` preserves strict PPT when driven by polynomial-time round functions and a
strict oracle PPT verifier (`isPPTOn_runTwoRound`), defines the zero-knowledge simulator
`gmwSimulator` (via `gmwSampleSimCoins`, `gmwSimWithPads`, `gmwSimAttempt` and `firstSuccess`), and
certifies:

* `isOraclePPTOn_gmwVerifier`: the honest verifier `gmwVerifier` is uniform strict oracle PPT;
* `isPPTOn_gmwInteract`: running any uniform strict oracle PPT verifier against the honest prover is
  uniform strict PPT;
* `isPPTOn_gmwSimulator`: the GMW zero-knowledge simulator `gmwSimulator` is uniform strict PPT.

## Main definitions

* `Cslib.Crypto.GMW.encTwoRoundState`, `Cslib.Crypto.GMW.encProverCoins`: the encodings of the
  state of `runTwoRound` and of the prover's coins.
* `Cslib.Crypto.GMW.gmwSampleSimCoins`, `Cslib.Crypto.GMW.gmwSimWithPads`,
  `Cslib.Crypto.GMW.gmwSimAttempt`: single-attempt GMW simulator components. An attempt returns
  `some` view when its guess hits the verifier's challenge and `none` otherwise (`acceptGuess`).
* `Cslib.Crypto.GMW.gmwSimulator`: the GMW zero-knowledge simulator repeating `gmwSimAttempt`
  `n + 1` times.

## Main results

* `Cslib.Crypto.GMW.isOraclePPTOn_gmwVerifier`: `gmwVerifier` is `IsOraclePPTOn`.
* `Cslib.Crypto.GMW.isPPTOn_gmwInteract`: `gmwInteract` is `IsPPTOn`.
* `Cslib.Crypto.GMW.isPPTOn_gmwSimulator`: `gmwSimulator` is `IsPPTOn`.

## References

* [O. Goldreich, S. Micali, A. Wigderson, *Proofs that Yield Nothing But Their Validity, or All
  Languages in NP Have Zero-Knowledge Proof Systems*][GoldreichMicaliWigderson1991]
* [M. Naor, *Bit Commitment Using Pseudorandomness*][Naor1991]
-/

@[expose] public section

namespace Cslib.Crypto.GMW

open Probability Complexity Logic.PL Turing.MultiTapeTM

/-! ### Polynomial-time certificates for protocol gadgets -/

private theorem computableInPolyTime_clauseLitVar (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => ((c a).getD i (0, false)).1) input encNat :=
  (hc.listGetDWithInput (.const i) (0, false)).fst'

private theorem computableInPolyTime_clauseLitPol (i : ℕ) {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => ((c a).getD i (0, false)).2) input encBool :=
  (hc.listGetDWithInput (.const i) (0, false)).snd'

@[fun_prop]
theorem computableInPolyTime_gmwBit0Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => gmwBit0Of8 (t a)) input encBool := by
  polytime [gmwBit0Of8]

@[fun_prop]
theorem computableInPolyTime_gmwBit1Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => gmwBit1Of8 (t a)) input encBool := by
  polytime [gmwBit1Of8]

@[fun_prop]
theorem computableInPolyTime_gmwBit2Of8 {α : Type} {input : α ↪ List Bool} {t : α → ℕ}
    (ht : ComputableInPolyTime t input encUnary) :
    ComputableInPolyTime (fun a => gmwBit2Of8 (t a)) input encBool := by
  polytime [gmwBit2Of8]

@[fun_prop]
theorem computableInPolyTime_gmwActiveIdx {α : Type} {input : α ↪ List Bool}
    {b₀ b₁ b₂ : α → Bool} (hb₀ : ComputableInPolyTime b₀ input encBool)
    (hb₁ : ComputableInPolyTime b₁ input encBool) (hb₂ : ComputableInPolyTime b₂ input encBool) :
    ComputableInPolyTime (fun a => gmwActiveIdx (b₀ a) (b₁ a) (b₂ a)) input encUnary := by
  polytime [gmwActiveIdx]

@[fun_prop]
theorem computableInPolyTime_clauseEvalBits {α : Type} {input : α ↪ List Bool}
    {c : α → Clause ℕ} {b₀ b₁ b₂ : α → Bool}
    (hc : ComputableInPolyTime c input (encClause encNat))
    (hb₀ : ComputableInPolyTime b₀ input encBool) (hb₁ : ComputableInPolyTime b₁ input encBool)
    (hb₂ : ComputableInPolyTime b₂ input encBool) :
    ComputableInPolyTime (fun a => clauseEvalBits (c a) (b₀ a) (b₁ a) (b₂ a)) input encBool := by
  have hp0 := computableInPolyTime_clauseLitPol 0 hc
  have hp1 := computableInPolyTime_clauseLitPol 1 hc
  have hp2 := computableInPolyTime_clauseLitPol 2 hc
  polytime [clauseEvalBits]

@[fun_prop]
theorem computableInPolyTime_varBit {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {vec : α → List Bool} {v : α → ℕ}
    (hφ : ComputableInPolyTime φ input encCNF) (hvec : ComputableInPolyTime vec input encBits)
    (hv : ComputableInPolyTime v input encNat) :
    ComputableInPolyTime (fun a => varBit (φ a) (vec a) (v a)) input encBool := by
  polytime [varBit]

@[fun_prop]
theorem computableInPolyTime_clauseTableRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableInPolyTime φ input encCNF) (hm : ComputableInPolyTime m input encBits)
    (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => clauseTableRow (φ a) (m a) (c a)) input encBits := by
  have hf := hφ.comp (.fst input encUnary)
  have hm1 := hm.comp (.fst input encUnary)
  have hc1 := hc.comp (.fst input encUnary)
  have hv0 := computableInPolyTime_varBit hf hm1 (computableInPolyTime_clauseLitVar 0 hc1)
  have hv1 := computableInPolyTime_varBit hf hm1 (computableInPolyTime_clauseLitVar 1 hc1)
  have hv2 := computableInPolyTime_varBit hf hm1 (computableInPolyTime_clauseLitVar 2 hc1)
  dsimp only [Function.comp_def] at hv0 hv1 hv2
  dsimp only [clauseTableRow]
  apply (ComputableInPolyTime.const (List.range 8)).mapToBitsWithInput (enc := encUnary)
  polytime

@[fun_prop]
theorem computableInPolyTime_clauseActiveRow {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool} {c : α → Clause ℕ}
    (hφ : ComputableInPolyTime φ input encCNF) (hv : ComputableInPolyTime v input encBits)
    (hc : ComputableInPolyTime c input (encClause encNat)) :
    ComputableInPolyTime (fun a => clauseActiveRow (φ a) (v a) (c a)) input encBits := by
  have hf := hφ.comp (.fst input encUnary)
  have hv1' := hv.comp (.fst input encUnary)
  have hc1 := hc.comp (.fst input encUnary)
  have hidx := computableInPolyTime_gmwActiveIdx
    (computableInPolyTime_varBit hf hv1' (computableInPolyTime_clauseLitVar 0 hc1))
    (computableInPolyTime_varBit hf hv1' (computableInPolyTime_clauseLitVar 1 hc1))
    (computableInPolyTime_varBit hf hv1' (computableInPolyTime_clauseLitVar 2 hc1))
  dsimp only [Function.comp_def] at hidx
  dsimp only [clauseActiveRow]
  apply (ComputableInPolyTime.const (List.range 8)).mapToBitsWithInput (enc := encUnary)
  polytime

@[fun_prop]
theorem computableInPolyTime_tableBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {m : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hm : ComputableInPolyTime m input encBits) :
    ComputableInPolyTime (fun a => tableBits (φ a) (m a)) input encBits := by
  polytime [tableBits]

@[fun_prop]
theorem computableInPolyTime_activeTableFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {v : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hv : ComputableInPolyTime v input encBits) :
    ComputableInPolyTime (fun a => activeTableFlags (φ a) (v a)) input encBits := by
  polytime [activeTableFlags]

@[fun_prop]
theorem computableInPolyTime_copyLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ input encCNF) :
    ComputableInPolyTime (fun a => copyLen (φ a)) input encUnary := by
  polytime [copyLen]

@[fun_prop]
theorem computableInPolyTime_totalLen {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} (hφ : ComputableInPolyTime φ input encCNF) :
    ComputableInPolyTime (fun a => totalLen (φ a)) input encUnary := by
  polytime [totalLen]

@[fun_prop]
theorem computableInPolyTime_mPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => mPart (φ a) (copy a)) input encBits := by
  polytime [mPart]

@[fun_prop]
theorem computableInPolyTime_vPart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => vPart (φ a) (copy a)) input encBits := by
  polytime [vPart]

@[fun_prop]
theorem computableInPolyTime_tablePart {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => tablePart (φ a) (copy a)) input encBits := by
  polytime [tablePart]

@[fun_prop]
theorem computableInPolyTime_realCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m : α → List Bool} (hφ : ComputableInPolyTime φ input encCNF)
    (hw : ComputableInPolyTime w input encBits) (hm : ComputableInPolyTime m input encBits) :
    ComputableInPolyTime (fun a => realCopyBits (φ a) (w a) (m a)) input encBits := by
  polytime [realCopyBits]

@[fun_prop]
theorem computableInPolyTime_simCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {rand : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hb : ComputableInPolyTime b input encBool)
    (hrand : ComputableInPolyTime rand input encBits) :
    ComputableInPolyTime (fun a => simCopyBits (φ a) (b a) (rand a)) input encBits := by
  polytime [simCopyBits]

@[fun_prop]
theorem computableInPolyTime_copyOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hb : ComputableInPolyTime b input encBool)
    (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => copyOpenFlags (φ a) (b a) (copy a)) input encBits := by
  polytime [copyOpenFlags]

@[fun_prop]
theorem computableInPolyTime_verifyCopyBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {b : α → Bool} {copy : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hb : ComputableInPolyTime b input encBool)
    (hcopy : ComputableInPolyTime copy input encBits) :
    ComputableInPolyTime (fun a => verifyCopyBits (φ a) (b a) (copy a)) input encBool := by
  polytime [verifyCopyBits]

@[fun_prop]
theorem computableInPolyTime_gmwCopy0 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => gmwCopy0 (φ a) (bits a)) input encBits := by
  polytime [gmwCopy0]

@[fun_prop]
theorem computableInPolyTime_gmwCopy1 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => gmwCopy1 (φ a) (bits a)) input encBits := by
  polytime [gmwCopy1]

@[fun_prop]
theorem computableInPolyTime_gmwCopy2 {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {bits : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => gmwCopy2 (φ a) (bits a)) input encBits := by
  polytime [gmwCopy2]

@[fun_prop]
theorem computableInPolyTime_realBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {w m₀ m₁ m₂ : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hw : ComputableInPolyTime w input encBits)
    (hm₀ : ComputableInPolyTime m₀ input encBits) (hm₁ : ComputableInPolyTime m₁ input encBits)
    (hm₂ : ComputableInPolyTime m₂ input encBits) :
    ComputableInPolyTime (fun a => realBits (φ a) (w a) (m₀ a) (m₁ a) (m₂ a)) input encBits := by
  polytime [realBits]

@[fun_prop]
theorem computableInPolyTime_simBits {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch r₀ r₁ r₂ : α → List Bool}
    (hφ : ComputableInPolyTime φ input encCNF) (hch : ComputableInPolyTime ch input encBits)
    (hr₀ : ComputableInPolyTime r₀ input encBits) (hr₁ : ComputableInPolyTime r₁ input encBits)
    (hr₂ : ComputableInPolyTime r₂ input encBits) :
    ComputableInPolyTime (fun a => simBits (φ a) (ch a) (r₀ a) (r₁ a) (r₂ a)) input encBits := by
  polytime [simBits]

@[fun_prop]
theorem computableInPolyTime_allOpenFlags {α : Type} {input : α ↪ List Bool}
    {φ : α → CNF ℕ} {ch bits : α → List Bool} (hφ : ComputableInPolyTime φ input encCNF)
    (hch : ComputableInPolyTime ch input encBits)
    (hbits : ComputableInPolyTime bits input encBits) :
    ComputableInPolyTime (fun a => allOpenFlags (φ a) (ch a) (bits a)) input encBits := by
  polytime [allOpenFlags]

@[fun_prop]
theorem computableInPolyTime_proverReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ}
    {r openFlags bits : α → List Bool} {seeds pads : α → List (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hm : ComputableInPolyTime m input encUnary) (hr : ComputableInPolyTime r input encBits)
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits))
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    ComputableInPolyTime
      (fun a => proverReply1 generator (m a) (r a) (openFlags a) (bits a) (seeds a) (pads a))
      input encBits := by
  polytime [proverReply1]

@[fun_prop]
theorem computableInPolyTime_proverReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch bits : α → List Bool} {seeds : α → List (List Bool)}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hch : ComputableInPolyTime ch input encBits) (hbits : ComputableInPolyTime bits input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits)) :
    ComputableInPolyTime (fun a => proverReply2 (s a) (φ a) (ch a) (bits a) (seeds a))
      input encBits := by
  polytime [proverReply2]

@[fun_prop]
theorem computableInPolyTime_verifyCommitments {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r flags commitReply openedBits openSeedsFlat : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hs : ComputableInPolyTime s input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hφ : ComputableInPolyTime φ input encCNF) (hr : ComputableInPolyTime r input encBits)
    (hflags : ComputableInPolyTime flags input encBits)
    (hcommit : ComputableInPolyTime commitReply input encBits)
    (hopened : ComputableInPolyTime openedBits input encBits)
    (hseeds : ComputableInPolyTime openSeedsFlat input encBits) :
    ComputableInPolyTime
      (fun a => verifyCommitments generator (s a) (m a) (φ a) (r a) (flags a)
        (commitReply a) (openedBits a) (openSeedsFlat a))
      input encBool := by
  polytime [verifyCommitments]

@[fun_prop]
theorem computableInPolyTime_verifyTranscript {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {s m : α → ℕ} {φ : α → CNF ℕ}
    {r commitReply ch openReply : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hs : ComputableInPolyTime s input encUnary) (hm : ComputableInPolyTime m input encUnary)
    (hφ : ComputableInPolyTime φ input encCNF) (hr : ComputableInPolyTime r input encBits)
    (hcommit : ComputableInPolyTime commitReply input encBits)
    (hch : ComputableInPolyTime ch input encBits)
    (hopen : ComputableInPolyTime openReply input encBits) :
    ComputableInPolyTime
      (fun a => verifyTranscript generator (s a) (m a) (φ a) (r a)
        (commitReply a) (ch a) (openReply a))
      input encBool := by
  polytime [verifyTranscript]

@[fun_prop]
theorem isOraclePPTOn_gmwVerifier {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length)
    (hf : ComputableInPolyTime f enc encCNF) :
    IsOraclePPTOn (encPair encUnary enc) encBool
      (fun p : ℕ × α => gmwVerifier generator length f p.1 p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  ppt [gmwVerifier]

/-! ### PPT certificates for `runTwoRound` and honest interaction -/

/-- The state of `runTwoRound`: the round counter in unary, then the recorded challenge as a bit
word. The round counter is framed. -/
enc_structure encTwoRoundState : TwoRoundState where
  round : encUnary, challenge : encBits

/-- The prover's coins, as sampled for the honest prover by `sampleHonestCoins` or for the simulator
by `gmwSampleSimCoins`: the committed bits as a bit word, then the list of commitment seeds, each a
bit word. The bits are framed, and so is each seed. -/
enc_structure encProverCoins : ProverCoins where
  bits : encBits, seeds : (encList encBits)

theorem isPPTOn_runTwoRound {α β Caller : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    {prepare : Caller → ℕ × α × List Bool} {reply1 reply2 : Caller × List Bool → List Bool}
    {bound : Caller → ℕ}
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z))
    (hprep : ComputableInPolyTime prepare input (encInstanceAuxInput enc))
    (hr1 : ComputableInPolyTime reply1 (encPair input encBits) encBits)
    (hr2 : ComputableInPolyTime reply2 (encPair input encBits) encBits)
    (hbound : ComputableInPolyTime bound input encUnary)
    (hle1 : ∀ c q, (reply1 (c, q)).length ≤ bound c)
    (hle2 : ∀ c q, (reply2 (c, q)).length ≤ bound c) :
    IsPPTOn input (encPair encB encTwoRoundState)
      (fun c => runTwoRound (fun q => reply1 (c, q)) (fun q => reply2 (c, q))
        (Vstar (prepare c).1 (prepare c).2.1 (prepare c).2.2) .init) := by
  have hlen_state : ∀ s : TwoRoundState, s.round ≤ 2 → s.challenge.length = 3 →
      (encTwoRoundState s).length ≤ 9 := by
    intro s hs1 hs2
    simp only [encTwoRoundState_apply, encTwoRoundStateFields, length_encPair, encUnary_apply,
      List.length_replicate, encBits_apply, hs2]; omega
  refine hV.run_interpret_preprocess (operationEncoding := encFinEnum Unit)
    (stateEncoding := encTwoRoundState)
    (handler := fun c q s =>
      pure (twoRoundStep (fun x => reply1 (c, x)) (fun x => reply2 (c, x)) q.2 s))
    (prepare := prepare) (initial := fun _ => .init)
    (resources := fun c _ => bound c + 9) hprep
    (by polytime [twoRoundStep] : ComputableInPolyTime _ _ _).isPPTOn
    (ComputableInPolyTime.const TwoRoundState.init)
    (fun _ s => s.round ≤ 2 ∧ s.challenge.length = 3) (fun _ => ⟨Nat.zero_le _, rfl⟩)
    (by polytime)
    (fun c request state hstate result hresult => ?_)
  simp only [ProbComp.eval_pure, PMF.support_pure, Set.mem_singleton_iff] at hresult
  subst hresult; dsimp only [twoRoundStep]
  split_ifs with h0 h1
  · dsimp only; exact ⟨⟨by omega, hstate.2⟩, (hle1 c request.2).trans (by omega),
      (hlen_state ⟨1, state.challenge⟩ (Nat.le_succ 1) hstate.2).trans (by omega)⟩
  · dsimp only; exact ⟨⟨by omega, BitString.length_listRow 3 0 request.2⟩,
      (hle2 c _).trans (by omega), (hlen_state ⟨2, BitString.listRow 3 0 request.2⟩ le_rfl
        (BitString.length_listRow 3 0 request.2)).trans (by omega)⟩
  · dsimp only; exact ⟨hstate, by simp, (hlen_state state hstate.1 hstate.2).trans (by omega)⟩

@[fun_prop]
theorem isPPTOn_runTwoRound_prover {α β Caller : Type} {enc : α ↪ List Bool}
    {encB : β ↪ List Bool} {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    {generator : List Bool → List Bool} {n s m : Caller → ℕ} {a : Caller → α}
    {z : Caller → List Bool} {φ : Caller → CNF ℕ}
    {openFlags bits ch_guess : Caller → List Bool} {seeds pads : Caller → List (List Bool)}
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z))
    (hg : ComputableInPolyTime generator encBits encBits)
    (hn : ComputableInPolyTime n input encUnary) (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (ha : ComputableInPolyTime a input enc)
    (hz : ComputableInPolyTime z input encBits) (hφ : ComputableInPolyTime φ input encCNF)
    (hopen : ComputableInPolyTime openFlags input encBits)
    (hbits : ComputableInPolyTime bits input encBits)
    (hch : ComputableInPolyTime ch_guess input encBits)
    (hseeds : ComputableInPolyTime seeds input (encList encBits))
    (hpads : ComputableInPolyTime pads input (encList encBits)) :
    IsPPTOn input (encPair encB encTwoRoundState)
      (fun c => runTwoRound
        (fun r => proverReply1 generator (m c) r (openFlags c) (bits c) (seeds c) (pads c))
        (fun _ => proverReply2 (s c) (φ c) (ch_guess c) (bits c) (seeds c))
        (Vstar (n c) (a c) (z c)) .init) :=
  isPPTOn_runTwoRound hV (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => proverReply1 generator (m p.1) p.2 (openFlags p.1)
      (bits p.1) (seeds p.1) (pads p.1))
    (reply2 := fun p => proverReply2 (s p.1) (φ p.1) (ch_guess p.1) (bits p.1) (seeds p.1))
    (bound := fun c => (bits c).length * m c + (bits c).length * (s c + 1))
    (by polytime) (by polytime) (by polytime) (by polytime)
    (fun c q => by dsimp only; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only; rw [length_proverReply2_any]; omega)

/-! ### GMW zero-knowledge simulator and its PPT certificate -/

@[fun_prop]
theorem computableInPolyTime_firstSuccess {α β : Type} {input : α ↪ List Bool}
    {enc : β ↪ List Bool} {d : α → β} {attempts : α → List (Option β)}
    (hd : ComputableInPolyTime d input enc)
    (ha : ComputableInPolyTime attempts input (encList (encOption enc))) :
    ComputableInPolyTime (fun a => firstSuccess (d a) (attempts a)) input enc :=
  let hfilt := (ComputableInPolyTime.headD (encA := encOption enc) none).comp'
    (ha.filterWithInput
      (ComputableInPolyTime.snd input (encOption enc)).optionIsSome)
  (hfilt.optionGetDWithInput hd)

@[fun_prop]
theorem computableInPolyTime_acceptGuess {α β : Type} {input : α ↪ List Bool}
    {encB : β ↪ List Bool} {ch_guess : α → List Bool} {result : α → β × TwoRoundState}
    (hch : ComputableInPolyTime ch_guess input encBits)
    (hres : ComputableInPolyTime result input (encPair encB encTwoRoundState)) :
    ComputableInPolyTime (fun a => acceptGuess (ch_guess a) (result a)) input (encOption encB) := by
  polytime [acceptGuess]

/-- Sample the GMW simulator's random strings and commitment seeds for a guessed challenge
`ch_guess`; the committed bits are `simBits φ ch_guess r₀ r₁ r₂`. -/
noncomputable def gmwSampleSimCoins (s : ℕ) (φ : CNF ℕ) (ch_guess : List Bool) :
    ProbComp ProverCoins := do
  let r₀ ← BitString.sampleList φ.vars.length
  let r₁ ← BitString.sampleList φ.vars.length
  let r₂ ← BitString.sampleList φ.vars.length
  let seeds ← OracleComp.replicate (totalLen φ) (BitString.sampleList s)
  return ⟨simBits φ ch_guess r₀ r₁ r₂, seeds⟩

@[fun_prop]
theorem isPPTOn_gmwSampleSimCoins {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {ch_guess : α → List Bool}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hch : ComputableInPolyTime ch_guess input encBits) :
    IsPPTOn input encProverCoins (fun a => gmwSampleSimCoins (s a) (φ a) (ch_guess a)) := by
  ppt [gmwSampleSimCoins]

/-- Run one simulated GMW attempt on `prog` with pre-sampled unopened pads `pads`, without any
witness: guess the challenge, commit to `simBits` for that guess, and return the verifier's output
when its challenge equals the guess. -/
noncomputable def gmwSimWithPads {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (prog : WordOracleComp Unit β) (pads : List (List Bool)) :
    ProbComp (Option β) := do
  let ch_guess ← BitString.sampleList 3
  let coins ← gmwSampleSimCoins s φ ch_guess
  acceptGuess ch_guess <$> runTwoRound
    (fun r => proverReply1 generator m r (allOpenFlags φ ch_guess coins.bits) coins.bits
      coins.seeds pads)
    (fun _ => proverReply2 s φ ch_guess coins.bits coins.seeds)
    prog .init

/-- One attempt of the GMW zero-knowledge simulator on `prog`, without any witness. -/
noncomputable def gmwSimAttempt {β : Type} (generator : List Bool → List Bool) (s m : ℕ)
    (φ : CNF ℕ) (prog : WordOracleComp Unit β) : ProbComp (Option β) := do
  let pads ← OracleComp.replicate (totalLen φ) (BitString.sampleList m)
  gmwSimWithPads generator s m φ prog pads

/-- The GMW zero-knowledge simulator: run `gmwSimAttempt` `n + 1` times and return the first
successful view, or `[]` when every attempt failed. -/
noncomputable def gmwSimulator {α : Type} (generator : List Bool → List Bool) (length : ℕ → ℕ)
    (f : α → CNF ℕ) (Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool))
    (n : ℕ) (a : α) (z : List Bool) : ProbComp (List Bool) :=
  firstSuccess [] <$> OracleComp.replicate (n + 1)
    (gmwSimAttempt generator (n + 7) (length (n + 7)) (f a) (Vstar n a z))

theorem isPPTOn_gmwSimWithPads {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encPair (encInstanceAuxInput enc) (encList encBits)) (encOption encB)
      (fun p : (ℕ × α × List Bool) × List (List Bool) =>
        gmwSimWithPads generator (p.1.1 + 7) (length (p.1.1 + 7))
          (f p.1.2.1) (Vstar p.1.1 p.1.2.1 p.1.2.2) p.2) := by
  have hlength := PRG.polyTime_length hg hlen
  ppt [gmwSimWithPads]

theorem isPPTOn_gmwSimAttempt {α β : Type} {enc : α ↪ List Bool} {encB : β ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit β}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encB (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encInstanceAuxInput enc) (encOption encB)
      (fun p : ℕ × α × List Bool =>
        gmwSimAttempt generator (p.1 + 7) (length (p.1 + 7))
          (f p.2.1) (Vstar p.1 p.2.1 p.2.2)) := by
  have hlength := PRG.polyTime_length hg hlen
  have hPads := isPPTOn_gmwSimWithPads hg hlen hf hV
  ppt [gmwSimAttempt]

theorem isPPTOn_gmwSimulator {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encInstanceAuxInput enc) encBits
      (fun (n, a, z) => gmwSimulator generator length f Vstar n a z) := by
  change IsPPTOn (encInstanceAuxInput enc) encBits
    (fun p => gmwSimulator generator length f Vstar p.1 p.2.1 p.2.2)
  have hAtt := isPPTOn_gmwSimAttempt hg hlen hf hV
  ppt [gmwSimulator]

@[fun_prop]
theorem computableInPolyTime_honestReply1 {α : Type} {input : α ↪ List Bool}
    {generator : List Bool → List Bool} {m : α → ℕ} {φ : α → CNF ℕ}
    {coins : α → ProverCoins} {r : α → List Bool}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hm : ComputableInPolyTime m input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hcoins : ComputableInPolyTime coins input encProverCoins)
    (hr : ComputableInPolyTime r input encBits) :
    ComputableInPolyTime (fun a => honestReply1 generator (m a) (φ a) (coins a) (r a))
      input encBits := by
  polytime [honestReply1]

@[fun_prop]
theorem computableInPolyTime_honestReply2 {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {coins : α → ProverCoins} {ch : α → List Bool}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hcoins : ComputableInPolyTime coins input encProverCoins)
    (hch : ComputableInPolyTime ch input encBits) :
    ComputableInPolyTime (fun a => honestReply2 (s a) (φ a) (coins a) (ch a)) input encBits := by
  polytime [honestReply2]

@[fun_prop]
theorem isPPTOn_runTwoRound_honest {α Caller : Type} {enc : α ↪ List Bool}
    {input : Caller ↪ List Bool}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    {generator : List Bool → List Bool} {n s m : Caller → ℕ} {a : Caller → α}
    {z : Caller → List Bool} {φ : Caller → CNF ℕ} {coins : Caller → ProverCoins}
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z))
    (hg : ComputableInPolyTime generator encBits encBits)
    (hn : ComputableInPolyTime n input encUnary) (hs : ComputableInPolyTime s input encUnary)
    (hm : ComputableInPolyTime m input encUnary) (ha : ComputableInPolyTime a input enc)
    (hz : ComputableInPolyTime z input encBits) (hφ : ComputableInPolyTime φ input encCNF)
    (hcoins : ComputableInPolyTime coins input encProverCoins) :
    IsPPTOn input (encPair encBits encTwoRoundState)
      (fun c => runTwoRound (honestReply1 generator (m c) (φ c) (coins c))
        (honestReply2 (s c) (φ c) (coins c)) (Vstar (n c) (a c) (z c)) .init) :=
  isPPTOn_runTwoRound hV (prepare := fun c => (n c, a c, z c))
    (reply1 := fun p => honestReply1 generator (m p.1) (φ p.1) (coins p.1) p.2)
    (reply2 := fun p => honestReply2 (s p.1) (φ p.1) (coins p.1) p.2)
    (bound := fun c => (coins c).bits.length * m c + (coins c).bits.length * (s c + 1))
    (by polytime) (by polytime) (by polytime) (by polytime)
    (fun c q => by dsimp only [honestReply1]; exact (List.length_take_le _ _).trans (by omega))
    (fun c q => by dsimp only [honestReply2]; rw [length_proverReply2_any]; omega)

@[fun_prop]
theorem isPPTOn_sampleHonestCoins {α : Type} {input : α ↪ List Bool}
    {s : α → ℕ} {φ : α → CNF ℕ} {w : α → List Bool}
    (hs : ComputableInPolyTime s input encUnary) (hφ : ComputableInPolyTime φ input encCNF)
    (hw : ComputableInPolyTime w input encBits) :
    IsPPTOn input encProverCoins (fun a => sampleHonestCoins (s a) (φ a) (w a)) := by
  ppt [sampleHonestCoins]

theorem isPPTOn_gmwInteract {α : Type} {enc : α ↪ List Bool}
    {generator : List Bool → List Bool} {length : ℕ → ℕ} {f : α → CNF ℕ}
    {Vstar : ℕ → α → List Bool → WordOracleComp Unit (List Bool)}
    (hg : ComputableInPolyTime generator encBits encBits)
    (hlen : ∀ s, (generator s).length = length s.length) (hf : ComputableInPolyTime f enc encCNF)
    (hV : IsOraclePPTOn (encInstanceAuxInput enc) encBits (fun (n, a, z) => Vstar n a z)) :
    IsPPTOn (encInstanceWitnessAuxInput enc) encBits
      (fun (n, a, w, z) =>
        gmwInteract generator (n + 7) (length (n + 7)) (f a) w (Vstar n a z)) := by
  change IsPPTOn (encInstanceWitnessAuxInput enc) encBits
    (fun p => gmwInteract generator (p.1 + 7) (length (p.1 + 7)) (f p.2.1) p.2.2.1
      (Vstar p.1 p.2.1 p.2.2.2))
  have hlength := PRG.polyTime_length hg hlen
  ppt [gmwInteract]

end Cslib.Crypto.GMW
