/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.CCA
public import CslibFrontier.Probability.UniformNat
import Mathlib.Data.List.GetD
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.Encryption.DecryptionBound
import CslibFrontier.Crypto.Game.Hybrid
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation.Handler
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindCompare
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.SuppCases
import CslibFrontier.Tactic.Negligible

/-!
# Hybrid reduction from single-challenge 1CCA to batch multi-challenge CCA

This module proves the hybrid equivalence between single-challenge chosen-ciphertext security
(`INDCCA2On`, Definition 12.2) and the two-phase batch-challenge multi-challenge chosen-ciphertext
experiment (`INDCCA2MultiOn`, in which all challenge pairs are submitted in a single list between
Phase 1 and Phase 2 decryption queries), a batch-challenge step toward [Boneh and Shoup, Section
12.1, Theorem 12.1, printed p. 468][BonehShoup2023]. It also provides the stateless Phase 2
challenge-rejection filter handler `multiPhase2FilterHandler` shared with the fully adaptive
interleaved-query reduction in `CslibFrontier.Crypto.Computational.Encryption.CCA.Interleaved`.

Splitting this hybrid reduction out of `CslibFrontier.Crypto.Computational.Encryption.CCA` keeps the
core 1CCA and batch multi-challenge definitions free of hybrid-game, dyadic-sampling, and decryption
length-bound dependencies for 1CCA-only clients.

## Main definitions

* `Cslib.Crypto.Encryption.multiPhase2FilterHandler`: stateless Phase 2 oracle handler rejecting
  decryption queries in a forbidden challenge-ciphertext list `cts` with `[]` and forwarding other
  queries with a bounded reply-length prefix.
* `Cslib.Crypto.Encryption.cca2MultiHybridGameOn`: `split`-hybrid batch multi-challenge CCA
  experiment encrypting the first `split` pairs with the right message and the remaining pairs with
  the left message.
* `Cslib.Crypto.Encryption.cca2MultiToSingleAt`, `Cslib.Crypto.Encryption.cca2MultiToSingle`:
  single-challenge `CCA2AdversaryOf Msg` reductions at a fixed hybrid index `split` and at a
  uniformly sampled dyadic index `Fin (dyadicSize (Q n))`.

## Main results

* `Cslib.Crypto.Encryption.isQueryBounded_multiPhase2FilterHandler`,
  `Cslib.Crypto.Encryption.isOraclePPTOn_run_multiPhase2FilterHandler`,
  `Cslib.Crypto.Encryption.eval_run_multiPhase2FilterHandler`,
  `Cslib.Crypto.Encryption.eval_run_multiPhase2FilterHandler_phase1`: query bound, uniform strict
  oracle PPT certificate, and Phase 2 / Phase 1 distributional simulation identities for
  `multiPhase2FilterHandler`.
* `Cslib.Crypto.Encryption.isPPT_cca2MultiToSingleAt`,
  `Cslib.Crypto.Encryption.isPPT_cca2MultiToSingle`,
  `Cslib.Crypto.Encryption.isQueryBounded_cca2MultiToSingleAt`,
  `Cslib.Crypto.Encryption.isQueryBounded_cca2MultiToSingle`: strict oracle PPT and query-bound
  preservation for the batch multi-to-single reductions.
* `Cslib.Crypto.Encryption.cca2MultiHybridGameOn_step_gap`,
  `Cslib.Crypto.Encryption.cca2MultiGameOn_gap`,
  `Cslib.Crypto.Encryption.advantage_cca2MultiGameOn`: exact single-step and `dyadicSize (Q n)`
  hybrid advantage identities.

## Steps toward Theorem 12.1

[BonehShoup2023], Theorem 12.1 (printed p. 468) concerns Attack Game 12.1 (p. 467), in which
encryption and decryption queries are adaptively interleaved. It is
`Cslib.Crypto.Encryption.INDCCA2On.indcca2InterleavedOn` and
`Cslib.Crypto.Encryption.indcca2InterleavedOn_iff_indcca2On` in
`CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean`. The theorems below are its
restriction to adversaries that submit all challenge pairs in one batch between the two phases of
decryption queries; `Interleaved.lean` uses them to relate the two notions
(`indcca2InterleavedOn_iff_indcca2MultiOn`).

* `Cslib.Crypto.Encryption.INDCCA2On.indcca2MultiOn`,
  `Cslib.Crypto.Encryption.indcca2MultiOn_iff_indcca2On`,
  `Cslib.Crypto.Encryption.INDCCA2Of.indcca2MultiOf`,
  `Cslib.Crypto.Encryption.indcca2MultiOf_iff_indcca2Of`,
  `Cslib.Crypto.Encryption.INDCCA2.indcca2Multi`,
  `Cslib.Crypto.Encryption.indcca2Multi_iff_indcca2`,
  `Cslib.Crypto.Encryption.WordINDCCA2.wordINDCCA2Multi`,
  `Cslib.Crypto.Encryption.wordINDCCA2Multi_iff_wordINDCCA2`: single-challenge 1CCA implies
  batch-challenge multi-challenge CCA, and the two are equivalent.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 12.1 (Attack Game 12.1, Definitions 12.1–12.2, and
  Theorem 12.1, printed pp. 467–469).
-/

public section

namespace Cslib.Crypto.Encryption

open Probability Turing.MultiTapeTM
open scoped NNReal

/-- Saved state passed from Phase 1 (`choose`) to Phase 2 (`guess`) of `cca2MultiToSingleAt`. -/
private structure MultiCCA2State where
  /-- Whether Phase 1 accepted the challenge list and embedded the external challenge. -/
  active : Bool
  /-- State word saved by the multi-challenge adversary's `choose`. -/
  stateA : List Bool
  /-- Challenge ciphertexts before the embedded one, encrypting the right messages. -/
  ctsFront : List (List Bool)
  /-- Challenge ciphertexts after the embedded one, encrypting the left messages. -/
  ctsBack : List (List Bool)

/-- Encoding of `MultiCCA2State` as the framed tuple `(active, stateA, ctsFront, ctsBack)`. -/
private enc_structure encMultiCCA2State : MultiCCA2State where
  active : encBool, stateA : encBits, ctsFront : (encList encBits), ctsBack : (encList encBits)

private example (s : MultiCCA2State) :
    encMultiCCA2State s = encPair encBool (encPair encBits (encPair (encList encBits)
      (encList encBits))) (s.active, s.stateA, s.ctsFront, s.ctsBack) := rfl

/-- Total polynomial-time decoder for `encMultiCCA2State`. -/
private def multiCCA2StateDecoder : Decoder encMultiCCA2State :=
  (Decoder.bool.pair (Decoder.bits.pair ((Decoder.list Decoder.bits).pair
    (Decoder.list Decoder.bits)))).map
    (fun (active, stateA, ctsFront, ctsBack) => ⟨active, stateA, ctsFront, ctsBack⟩)
    (fun s => (s.active, s.stateA, s.ctsFront, s.ctsBack)) (fun _ => rfl) (fun _ => rfl)

/-- Encoded inactive state returned when `split ≥ choice.1.length` or any chosen challenge pair
fails `valid`. -/
private def rejectMultiCCA2State : List Bool :=
  encMultiCCA2State ⟨false, [], [], []⟩

@[simp] private theorem decode_rejectMultiCCA2State :
    multiCCA2StateDecoder.decode rejectMultiCCA2State = ⟨false, [], [], []⟩ :=
  multiCCA2StateDecoder.decode_enc ⟨false, [], [], []⟩

/-! ### Shared Phase 2 challenge-rejection filter handler -/

/-- Stateless Phase 2 filter handler for multi-to-single CCA reductions: reject any decryption
query `request.2 ∈ cts` with `[]`, and forward all other queries `request.2 ∉ cts` to the external
single-challenge decryption oracle (truncating the reply to `decBound request.2` bits for strict
oracle PPT certification). -/
def multiPhase2FilterHandler (decBound : List Bool → ℕ) (cts : List (List Bool))
    (request : Unit × List Bool) :
    StateT Unit (WordOracleComp Unit) (List Bool) := fun s =>
  if decide (request.2 ∈ cts) then
    pure ([], s)
  else
    (fun reply => (reply, s)) <$>
      (List.take (decBound request.2) <$> ProbOracleComp.query ((), request.2))

/-- Each call to `multiPhase2FilterHandler` makes at most `1` external decryption query. -/
theorem isQueryBounded_multiPhase2FilterHandler (decBound : List Bool → ℕ)
    (cts : List (List Bool)) (request : Unit × List Bool) (s : Unit) :
    (multiPhase2FilterHandler decBound cts request s).IsQueryBounded 1 := by
  unfold multiPhase2FilterHandler
  split_ifs
  · exact OracleComp.IsCostBounded.pure ([], s) 1
  · simpa only [Functor.map_map, OracleComp.isCostBounded_map_iff] using
      ProbOracleComp.IsQueryBounded.query ((), request.2)

/-- Running a strict oracle PPT program through `multiPhase2FilterHandler` is uniformly strict
oracle PPT whenever the reply-length cap and forbidden ciphertext list are computable in polynomial
time from the caller's input. -/
theorem isOraclePPTOn_run_multiPhase2FilterHandler {Caller β : Type}
    {ECaller : Caller ↪ List Bool} {EOut : β ↪ List Bool}
    {cap : Caller → List Bool → ℕ} {cts : Caller → List (List Bool)}
    {prog : Caller → WordOracleComp Unit β}
    (hcap : ComputableInPolyTime (fun p : Caller × List Bool => cap p.1 p.2)
      (encPair ECaller encBits) encUnary)
    (hcts : ComputableInPolyTime cts ECaller (encList encBits))
    (hprog : IsOraclePPTOn (Operation := Unit) ECaller EOut prog) :
    IsOraclePPTOn (Operation := Unit) ECaller (encPair EOut (encFinEnum Unit))
      (fun a =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (multiPhase2FilterHandler (cap a) (cts a)))
          (prog a)).run ()) := by
  refine hprog.run_interpret_preprocess_open (operationEncoding := encFinEnum Unit)
    (stateEncoding := encFinEnum Unit)
    (prepare := id) (initial := fun _ => ()) (resources := cap)
    ComputableInPolyTime.id'
    (by
      have hlim : ComputableInPolyTime
          (fun ⟨caller, (_, req), _⟩ => cap caller req)
          (encHandlerCall ECaller (encFinEnum Unit) (encFinEnum Unit)) encUnary :=
        hcap.comp (show ComputableInPolyTime (fun ⟨caller, (_, req), _⟩ => (caller, req))
          (encHandlerCall ECaller (encFinEnum Unit) (encFinEnum Unit)) _ by fun_prop)
      dsimp only [multiPhase2FilterHandler]
      exact IsOraclePPTOn.cond (by fun_prop) (by fun_prop)
        ((IsOraclePPTOn.query_take (Operation := Unit) () (by fun_prop) hlim).map_with
          (by fun_prop)))
    (by fun_prop) (fun _ _ => True) (fun _ => trivial) hcap
    fun _ _ _ _ _ hresult => ?_
  dsimp only [multiPhase2FilterHandler] at hresult
  split_ifs at hresult
  · supp_cases hresult; exact ⟨trivial, Nat.zero_le _, Nat.le_add_right _ _⟩
  · supp_cases hresult; exact ⟨trivial, List.length_take_le _ _, Nat.le_add_right _ _⟩

/-- Shared simulation lemma for `multiPhase2FilterHandler`: any base oracle agreeing with
`decrypt` on every `req ∉ cts` induces `cca2MultiPhase2Oracle` under `multiPhase2FilterHandler`. -/
private theorem eval_run_multiPhase2FilterHandler_of_eq {Out α : Type}
    (encOut : Out ↪ List Bool) (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : List Bool → ℕ) (n : ℕ) (sk : List Bool) (cts : List (List Bool))
    (baseOracle : Unit × List Bool → StateT Unit ProbComp (List Bool))
    (hbase : ∀ req ∉ cts,
      baseOracle ((), req) () = pure (encOption encOut (decrypt n sk req), ()))
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound req)
    (prog : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) baseOracle)
      (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler decBound cts))
        prog).run ())).run ()) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n sk cts))
      prog).run ()) := by
  rw [OracleComp.interpret_map, StateT.run_map, ProbComp.eval_map,
    ProbOracleComp.eval_run_interpret_eq_runWith, ProbOracleComp.eval_run_interpret_eq_runWith,
    ProbOracleComp.runWith_run_interpret_map (multiPhase2FilterHandler decBound cts)
      (fun q s => ProbComp.eval (baseOracle q s))
      (fun q s => ProbComp.eval (cca2MultiPhase2Oracle encOut decrypt n sk cts q s))
      (fun _ => ()) (fun _ => ()) (by
      intro ⟨⟨⟩, req⟩ ⟨⟩
      dsimp only [StateT.run]
      by_cases hmem : req ∈ cts
      · simp [cca2MultiPhase2Oracle, multiPhase2FilterHandler, hmem, ProbComp.eval_pure]
      · unfold cca2MultiPhase2Oracle multiPhase2FilterHandler
        simp only [hmem, decide_false, Bool.false_eq_true, ↓reduceIte, hbase req hmem,
          List.take_of_length_le (hdecBound req), runWith_norm, pmf_norm])
      prog (), PMF.map_comp]
  exact (congrArg (PMF.map · _) (funext fun _ => rfl : _ = id)).trans (PMF.map_id _)

/-- Interpreting `multiPhase2FilterHandler` against `cca2Phase2Oracle` on `ct ∈ cts` has the exact
same output distribution as running directly against `cca2MultiPhase2Oracle` on `cts`, whenever
`decBound` upper-bounds every encoded decryption output length. -/
theorem eval_run_multiPhase2FilterHandler {Out α : Type}
    (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : List Bool → ℕ)
    (n : ℕ) (sk ct : List Bool) (cts : List (List Bool))
    (hct : ct ∈ cts)
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound req)
    (prog : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase2Oracle encOut decrypt n sk ct))
      (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler decBound cts))
        prog).run ())).run ()) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n sk cts))
      prog).run ()) :=
  eval_run_multiPhase2FilterHandler_of_eq encOut decrypt decBound n sk cts
    (cca2Phase2Oracle encOut decrypt n sk ct)
    (fun req hmem => by
      have hne : (req == ct) = false := beq_eq_false_iff_ne.mpr fun heq => hmem (heq ▸ hct)
      simp [cca2Phase2Oracle, hne])
    hdecBound prog

/-- Interpreting `multiPhase2FilterHandler` against `cca2Phase1Oracle` has the exact same output
distribution as running directly against `cca2MultiPhase2Oracle` on `cts`, whenever `decBound`
upper-bounds every encoded decryption output length. -/
theorem eval_run_multiPhase2FilterHandler_phase1 {Out α : Type}
    (encOut : Out ↪ List Bool)
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : List Bool → ℕ)
    (n : ℕ) (sk : List Bool) (cts : List (List Bool))
    (hdecBound : ∀ req, (encOption encOut (decrypt n sk req)).length ≤ decBound req)
    (prog : WordOracleComp Unit α) :
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2Phase1Oracle encOut decrypt n sk))
      (Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler decBound cts))
        prog).run ())).run ()) =
    ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (cca2MultiPhase2Oracle encOut decrypt n sk cts))
      prog).run ()) :=
  eval_run_multiPhase2FilterHandler_of_eq encOut decrypt decBound n sk cts
    (cca2Phase1Oracle encOut decrypt n sk) (fun _ _ => rfl) hdecBound prog

/-! ### Single-challenge 1CCA implies batch-challenge CCA (step toward Theorem 12.1) -/

/-- Continuation of the multi-challenge hybrid experiment at index `split : ℕ` after
`(keys, choice)` have been sampled. -/
private noncomputable def cca2MultiHybridCont {Msg Out : Type}
    (encOut : Out ↪ List Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ)
    (keys : List Bool × List Bool)
    (choice : List (Msg × Msg) × List Bool) (split : ℕ) : ProbComp Bool := do
  let ctsFront ← (choice.1.take split).mapM (fun p => encrypt n keys.1 p.2)
  let ctsBack ← (choice.1.drop split).mapM (fun p => encrypt n keys.1 p.1)
  let cts := ctsFront ++ ctsBack
  let guessOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2MultiPhase2Oracle encOut decrypt n keys.2 cts))
    (adversary.guess n choice.2 cts)).run ()
  return guessOut.1

/-- Hybrid multi-challenge CCA experiment at index `split : ℕ` ([BonehShoup2023], Section 12.1,
Theorem 12.1, printed p. 468): encrypt the first `split` challenge pairs (`choice.1.take split`)
using the right (`true`) message `p.2` and the remaining challenge pairs (`choice.1.drop split`)
using the left (`false`) message `p.1`. -/
noncomputable def cca2MultiHybridGameOn {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (split n : ℕ) : ProbComp Bool := do
  let keys ← keyGen n
  let choiceOut ← (OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (cca2Phase1Oracle encOut decrypt n keys.2))
    (adversary.choose n keys.1)).run ()
  let choice := choiceOut.1
  if choice.1.all (fun p => valid n keys.1 p.1 p.2) then
    cca2MultiHybridCont encOut encrypt decrypt adversary n keys choice split
  else
    return false

/-- At `split = 0`, `cca2MultiHybridGameOn` coincides with `cca2MultiGameOn ... false`. -/
@[simp] theorem eval_cca2MultiHybridGameOn_zero {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ) :
    ProbComp.eval (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary 0 n) =
      ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary false n) := by
  simp [cca2MultiHybridGameOn, cca2MultiHybridCont, cca2MultiGameOn]

/-- Whenever every supported Phase 1 run chooses at most `split` challenge pairs,
`cca2MultiHybridGameOn` at `split` has the same output distribution as
`cca2MultiGameOn ... true`. -/
theorem eval_cca2MultiHybridGameOn_of_le {Msg Out : Type}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (adversary : MultiCCA2AdversaryOf Msg) (split n : ℕ)
    (hbound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ challenges stateA, ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support →
        challenges.length ≤ split) :
    ProbComp.eval (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary split n) =
      ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary true n) := by
  simp only [cca2MultiHybridGameOn, cca2MultiHybridCont, cca2MultiGameOn, ProbComp.eval_bind]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys =>
    PMF.bind_congr_on_support _ _ _ fun ⟨⟨challenges, stateA⟩, ⟨⟩⟩ hchoice => ?_
  have hle := hbound keys hkeys challenges stateA hchoice
  simp [List.take_of_length_le hle, List.drop_eq_nil_of_le hle]

/-- Single-challenge `CCA2AdversaryOf Msg` reduction at fixed hybrid index `split : ℕ`
(batch-challenge specialization of [BonehShoup2023], Section 12.1, Theorem 12.1, printed
p. 468). -/
noncomputable def cca2MultiToSingleAt {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (split : ℕ) : CCA2AdversaryOf Msg where
  choose n pk := do
    let choice ← adversary.choose n pk
    if decide (split < choice.1.length) && choice.1.all (fun p => valid n pk p.1 p.2) then
      let target := choice.1.getD split (default, default)
      let ctsFront ←
        ProbOracleComp.sample ((choice.1.take split).mapM (fun p => encrypt n pk p.2))
      let ctsBack ←
        ProbOracleComp.sample ((choice.1.drop (split + 1)).mapM (fun p => encrypt n pk p.1))
      return (target, encMultiCCA2State ⟨true, choice.2, ctsFront, ctsBack⟩)
    else
      return ((default, default), rejectMultiCCA2State)
  guess n state ct :=
    let decoded := multiCCA2StateDecoder.decode state
    if decoded.active then
      let cts := decoded.ctsFront ++ ct :: decoded.ctsBack
      Prod.fst <$> (OracleComp.interpret
        (OracleComp.sumHandler
          (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
          (multiPhase2FilterHandler (decBound n) cts))
        (adversary.guess n decoded.stateA cts)).run ()
    else
      pure false

/-- Single-challenge `CCA2AdversaryOf Msg` reduction that samples a uniform dyadic hybrid index
`split ← ProbOracleComp.sample (sampleDyadicIndex (Q n))` in Phase 1 and runs
`cca2MultiToSingleAt valid encrypt decBound adversary split` (batch-challenge specialization of
[BonehShoup2023], Section 12.1, Theorem 12.1, printed p. 468). -/
noncomputable def cca2MultiToSingle {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) : CCA2AdversaryOf Msg where
  choose n pk := do
    let split ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q n))
    (cca2MultiToSingleAt valid encrypt decBound adversary split).choose n pk
  guess n state ct :=
    (cca2MultiToSingleAt valid encrypt decBound adversary 0).guess n state ct

/-- Phase 1 (`choose`) of `cca2MultiToSingleAt` is uniformly strict oracle PPT in
`((n, pk), split)`. -/
private theorem isOraclePPTOn_cca2MultiToSingleAt_choose {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hA : adversary.IsPPT encMsg) :
    IsOraclePPTOn (Operation := Unit)
      (encPair (encPair encUnary encBits) encUnary)
      (encChoiceOut encMsg)
      (fun ⟨(n, pk), split⟩ =>
        (cca2MultiToSingleAt valid encrypt decBound adversary split).choose n pk) := by
  dsimp only [cca2MultiToSingleAt]
  refine (hA.choose.on.preprocess (by fun_prop)).bind_with
    (IsOraclePPTOn.cond (by fun_prop) ?_ (by fun_prop))
  exact (IsPPTOn.mapMWith (element := encPair encMsg encMsg) (by fun_prop)
    (by fun_prop)).isOraclePPTOn.bind_with
    ((IsPPTOn.mapMWith (element := encPair encMsg encMsg) (by fun_prop)
      (by fun_prop)).isOraclePPTOn.bind_with (by fun_prop))

/-- Phase 2 (`guess`) of `cca2MultiToSingleAt` is uniformly strict oracle PPT in
`(n, state, ct)`. -/
private theorem isOraclePPTOn_cca2MultiToSingleAt_guess {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    {decBound : ℕ → List Bool → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hdecBound : ComputableInPolyTime
      (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (split : ℕ) :
    IsOraclePPTOn (Operation := Unit)
      encGuessInput encBool
      (fun ⟨n, state, ct⟩ =>
        (cca2MultiToSingleAt valid encrypt decBound adversary split).guess n state ct) := by
  have hrun := isOraclePPTOn_run_multiPhase2FilterHandler
    (ECaller := encGuessInput) (EOut := encBool)
    (cap := fun ⟨n, _, _⟩ req => decBound n req)
    (cts := fun ⟨_, state, ct⟩ => (multiCCA2StateDecoder.decode state).ctsFront ++
      ct :: (multiCCA2StateDecoder.decode state).ctsBack)
    (hdecBound.comp (show ComputableInPolyTime (fun ⟨⟨n, _⟩, req⟩ => (n, req))
      (encPair encGuessInput encBits) _ by fun_prop))
    (by fun_prop)
    (hA.guess.preprocess
      (prepare := fun ⟨n, state, ct⟩ =>
        (n, (multiCCA2StateDecoder.decode state).stateA,
          (multiCCA2StateDecoder.decode state).ctsFront ++
            ct :: (multiCCA2StateDecoder.decode state).ctsBack))
      (by fun_prop))
  dsimp only [cca2MultiToSingleAt]; fun_prop

/-- `cca2MultiToSingleAt` preserves strict oracle PPT admissibility (`CCA2AdversaryOf.IsPPT`). -/
theorem isPPT_cca2MultiToSingleAt {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime
      (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hA : adversary.IsPPT encMsg) (split : ℕ) :
    (cca2MultiToSingleAt valid encrypt decBound adversary split).IsPPT encMsg where
  choose := ((isOraclePPTOn_cca2MultiToSingleAt_choose (decBound := decBound)
    hvalid hencrypt hA).preprocess (ComputableInPolyTime.id'.prod (.const split))).isOraclePPT
  guess := isOraclePPTOn_cca2MultiToSingleAt_guess valid encrypt hdecBound hA split

/-- `cca2MultiToSingle` preserves strict oracle PPT admissibility (`CCA2AdversaryOf.IsPPT`). -/
theorem isPPT_cca2MultiToSingle {Msg : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool}
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decBound : ℕ → List Bool → ℕ} {Q : ℕ → ℕ}
    {adversary : MultiCCA2AdversaryOf Msg}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecBound : ComputableInPolyTime
      (fun p : ℕ × List Bool => decBound p.1 p.2)
      (encPair encUnary encBits) encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary)
    (hA : adversary.IsPPT encMsg) :
    (cca2MultiToSingle valid encrypt decBound Q adversary).IsPPT encMsg where
  choose := ((by fun_prop : IsOraclePPTOn (Operation := Unit) (encPair encUnary encBits) encUnary
    fun caller : ℕ × List Bool =>
      ProbOracleComp.sample (ProbComp.sampleDyadicIndex (Q caller.1))).bind_with
    (isOraclePPTOn_cca2MultiToSingleAt_choose hvalid hencrypt hA)).isOraclePPT
  guess := isOraclePPTOn_cca2MultiToSingleAt_guess valid encrypt hdecBound hA 0

/-- `cca2MultiToSingleAt` preserves both Phase 1 (`Q₁ n`) and Phase 2 (`Q₂ n`) decryption query
bounds ([BonehShoup2023], Theorem 12.1, printed p. 468). -/
theorem isQueryBounded_cca2MultiToSingleAt {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ)
    {adversary : MultiCCA2AdversaryOf Msg} {Q₁ Q₂ : ℕ → ℕ}
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (split : ℕ) :
    (cca2MultiToSingleAt valid encrypt decBound adversary split).IsQueryBounded Q₁ Q₂ := by
  refine ⟨fun n pk => ?_, fun n state ct => ?_⟩
  · dsimp only [cca2MultiToSingleAt]
    exact (hQ.1 n pk).bind (m := 0) fun _ => by
      split_ifs
      · exact (ProbOracleComp.IsQueryBounded.sample _).bind (m := 0) fun _ =>
          (ProbOracleComp.IsQueryBounded.sample _).bind (m := 0) fun _ =>
            OracleComp.IsCostBounded.pure _ 0
      · exact OracleComp.IsCostBounded.pure _ 0
  · dsimp only [cca2MultiToSingleAt]
    split_ifs
    · refine (OracleComp.isCostBounded_map_iff _ _ _).mpr <|
        OracleComp.IsCostBounded.run_interpret (fun q s => ?_)
          (hQ.2 n (multiCCA2StateDecoder.decode state).stateA _) ()
      rcases q with m | req
      · simpa [OracleComp.sumHandler, StateT.lift, OracleComp.isCostBounded_map_iff] using
          ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m)
      · exact isQueryBounded_multiPhase2FilterHandler (decBound n) _ req s
    · exact OracleComp.IsCostBounded.pure false (Q₂ n)

/-- `cca2MultiToSingle` preserves both Phase 1 (`Q₁ n`) and Phase 2 (`Q₂ n`) decryption query
bounds ([BonehShoup2023], Theorem 12.1, printed p. 468). -/
theorem isQueryBounded_cca2MultiToSingle {Msg : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    {adversary : MultiCCA2AdversaryOf Msg} {Q₁ Q₂ : ℕ → ℕ}
    (hQ : adversary.IsQueryBounded Q₁ Q₂) :
    (cca2MultiToSingle valid encrypt decBound Q adversary).IsQueryBounded Q₁ Q₂ := by
  have hat := isQueryBounded_cca2MultiToSingleAt valid encrypt decBound hQ
  refine ⟨fun n pk => ?_, fun n state ct => (hat 0).2 n state ct⟩
  simpa only [cca2MultiToSingle, Nat.zero_add] using
    (ProbOracleComp.IsQueryBounded.sample (ProbComp.sampleDyadicIndex (Q n))).bind
      fun split => (hat split).1 n pk

/-- Running `cca2MultiToSingle` in `cca2GameOn` averages `cca2MultiToSingleAt` uniformly over
`Fin (dyadicSize (Q n))`. -/
theorem eval_cca2GameOn_cca2MultiToSingle {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (bit : Bool) (n : ℕ) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt
        (cca2MultiToSingle valid encrypt decBound Q adversary) bit n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (Q n)))).bind
        (fun i =>
          ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingleAt valid encrypt decBound adversary i.val) bit n)) := by
  simp only [cca2GameOn, cca2MultiToSingle, ProbComp.eval_sampleDyadicIndex,
    runWith_norm, pmf_norm]
  exact PMF.bind_comm _ _ _

private theorem eval_cca2GameOn_cca2MultiToSingleAt {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (split : ℕ) (bit : Bool) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req) :
    ProbComp.eval
      (cca2GameOn valid encOut keyGen encrypt decrypt
        (cca2MultiToSingleAt valid encrypt decBound adversary split) bit n) =
    (ProbComp.eval (keyGen n)).bind fun keys =>
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).bind fun ⟨(challenges, stateA), _⟩ =>
          if decide (split < challenges.length) &&
              challenges.all (fun p => valid n keys.1 p.1 p.2) then
            ProbComp.eval (cca2MultiHybridCont encOut encrypt decrypt adversary n keys
              (challenges, stateA) (if bit then split + 1 else split))
          else
            PMF.pure false := by
  simp only [cca2GameOn, cca2MultiToSingleAt, OracleComp.interpret_bind, StateT.run_bind,
    ProbComp.eval_bind, PMF.bind_bind]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys =>
    PMF.bind_congr_on_support _ _ _ fun ⟨⟨challenges, stateA⟩, ⟨⟩⟩ _ => ?_
  by_cases hcond :
      (decide (split < challenges.length) &&
        challenges.all (fun p => valid n keys.1 p.1 p.2)) = true
  · obtain ⟨hlt, hall⟩ := by simpa only [Bool.and_eq_true, decide_eq_true_eq] using hcond
    have hvalid_target : valid n keys.1 challenges[split].1 challenges[split].2 = true :=
      List.all_eq_true.mp hall _ (List.getElem_mem hlt)
    simp only [hcond, ↓reduceIte, ChoiceOut.msg₀, ChoiceOut.msg₁, ChoiceOut.state,
      ChoiceOut.msgs, List.getD_eq_getElem _ _ hlt, ProbOracleComp.eval_run_interpret_eq_runWith,
      ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample, ProbOracleComp.runWith_pure,
      PMF.bind_map, Function.comp_def, PMF.bind_bind, PMF.pure_bind, hvalid_target,
      ProbComp.eval_bind, multiCCA2StateDecoder.decode_enc]
    have hguess (ctsFront ctsBack : List (List Bool)) (ct : List Bool) :=
      (ProbOracleComp.eval_run_interpret_eq_runWith
        (cca2Phase2Oracle encOut decrypt n keys.2 ct) _ ()).symm.trans
        (eval_run_multiPhase2FilterHandler encOut decrypt (decBound n) n keys.2 ct
          (ctsFront ++ ct :: ctsBack) (List.mem_append_right _ (List.mem_cons_self ..))
          (hdecBound keys hkeys) (adversary.guess n stateA (ctsFront ++ ct :: ctsBack)))
    simp only [hguess]
    cases bit
    · simp only [Bool.false_eq_true, ↓reduceIte, cca2MultiHybridCont, ProbComp.eval_bind,
        List.drop_eq_getElem_cons hlt, List.mapM_cons, ProbComp.eval_pure, PMF.bind_bind,
        PMF.pure_bind]
      exact congrArg _ (funext fun _ => PMF.bind_comm _ _ _)
    · simp only [↓reduceIte, cca2MultiHybridCont, ProbComp.eval_bind, List.take_add_one,
        List.getElem?_eq_getElem hlt, Option.toList_some, List.mapM_append, List.mapM_cons,
        List.mapM_nil, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind, List.append_assoc,
        List.singleton_append]
      exact congrArg _ (funext fun _ => PMF.bind_comm _ _ _)
  · simp only [hcond, Bool.false_eq_true, ↓reduceIte, ChoiceOut.msg₀, ChoiceOut.msg₁,
      ChoiceOut.state, ChoiceOut.msgs, OracleComp.interpret_pure, StateT.run_pure,
      ProbComp.eval_pure, PMF.pure_bind, decode_rejectMultiCCA2State]
    by_cases hv : valid n keys.1 default default = true <;>
      simp only [hv, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.pure_bind, PMF.bind_const]

/-- **Single-step hybrid identity for multi-challenge CCA** ([BonehShoup2023], Theorem 12.1,
printed p. 468): at any hybrid index `split : ℕ`, the signed success-probability gap between
`cca2MultiHybridGameOn ... split` and `cca2MultiHybridGameOn ... (split + 1)` equals the signed
1CCA gap of `cca2MultiToSingleAt ... split`. -/
theorem cca2MultiHybridGameOn_step_gap {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (split n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req) :
    (Game.succProbability
        (ProbComp.eval
          (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary split n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary (split + 1) n)) =
      (Game.succProbability
        (ProbComp.eval
          (cca2GameOn valid encOut keyGen encrypt decrypt
            (cca2MultiToSingleAt valid encrypt decBound adversary split) false n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (cca2GameOn valid encOut keyGen encrypt decrypt
            (cca2MultiToSingleAt valid encrypt decBound adversary split) true n)) := by
  have hadd :
      ProbComp.eval
        (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary split n) true +
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (cca2MultiToSingleAt valid encrypt decBound adversary split) true n) true =
      ProbComp.eval
        (cca2MultiHybridGameOn valid encOut keyGen encrypt decrypt adversary (split + 1) n) true +
      ProbComp.eval
        (cca2GameOn valid encOut keyGen encrypt decrypt
          (cca2MultiToSingleAt valid encrypt decBound adversary split) false n) true := by
    rw [eval_cca2GameOn_cca2MultiToSingleAt valid encOut keyGen encrypt decrypt decBound adversary
        split false n hdecBound,
      eval_cca2GameOn_cca2MultiToSingleAt valid encOut keyGen encrypt decrypt decBound adversary
        split true n hdecBound]
    simp only [cca2MultiHybridGameOn, ProbComp.eval_bind]
    refine PMF.bind_apply_add_eq_on_support fun keys _ =>
      PMF.bind_apply_add_eq_on_support fun ⟨⟨challenges, stateA⟩, ⟨⟩⟩ _ => ?_
    by_cases hall : challenges.all (fun p => valid n keys.1 p.1 p.2) = true
    · by_cases hlt : split < challenges.length
      · simp [hall, decide_eq_true hlt, add_comm]
      · have hle : challenges.length ≤ split := Nat.le_of_not_lt hlt
        simp [hall, decide_eq_false hlt, cca2MultiHybridCont, List.take_of_length_le hle,
          List.take_of_length_le (Nat.le_add_right_of_le hle), List.drop_eq_nil_of_le hle,
          List.drop_eq_nil_of_le (Nat.le_add_right_of_le hle)]
    · simp [hall, ProbComp.eval_pure]
  have hreal := congrArg ENNReal.toReal hadd
  simp only [ENNReal.toReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _),
    Game.succProbability, ENNReal.coe_toNNReal_eq_toReal] at hreal ⊢
  linarith

/-- Signed hybrid gap for batch-challenge multi-challenge CCA, a step toward [BonehShoup2023],
Theorem 12.1 (printed p. 468) for batch challenges only: when every supported Phase 1 challenge
list has length at most `Q n`, the batch-challenge multi-challenge signed success-probability gap
equals `dyadicSize (Q n)` times the single-challenge 1CCA gap of `cca2MultiToSingle`. -/
theorem cca2MultiGameOn_gap {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req)
    (hQ : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ challenges stateA, ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support →
        challenges.length ≤ Q n) :
    (Game.succProbability
        (ProbComp.eval
          (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary false n)) : ℝ) -
      Game.succProbability
        (ProbComp.eval
          (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary true n)) =
      (dyadicSize (Q n) : ℝ) *
        ((Game.succProbability
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) false n)) : ℝ) -
        Game.succProbability
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) true n))) := by
  have : NeZero (dyadicSize (Q n)) := ⟨(dyadicSize_pos (Q n)).ne'⟩
  have htop := eval_cca2MultiHybridGameOn_of_le valid encOut keyGen encrypt decrypt adversary
    (dyadicSize (Q n)) n fun keys hkeys challenges stateA hchoice =>
      (hQ keys hkeys challenges stateA hchoice).trans (Nat.le_of_lt (lt_dyadicSize (Q n)))
  have hred := Game.succProbability_hybrid_reduction _ _ _
    (dyadicSize (Q n)) (dyadicSize (Q n)) le_rfl 1 fun split _ =>
      (cca2MultiHybridGameOn_step_gap valid encOut keyGen encrypt decrypt decBound adversary
        split n hdecBound).trans (one_mul _).symm
  rw [← eval_cca2MultiHybridGameOn_zero valid encOut keyGen encrypt decrypt adversary n, ← htop,
    hred, mul_one, eval_cca2GameOn_cca2MultiToSingle, eval_cca2GameOn_cca2MultiToSingle]
  simp only [Fin.is_lt, ↓reduceIte]

/-- Hybrid advantage identity for batch-challenge multi-challenge CCA, a step toward
[BonehShoup2023], Theorem 12.1 (printed p. 468) for batch challenges only: when every supported
Phase 1 challenge list has length at most `Q n`, the batch-challenge multi-challenge CCA advantage
equals `dyadicSize (Q n)` times the single-challenge 1CCA advantage of `cca2MultiToSingle`. -/
theorem advantage_cca2MultiGameOn {Msg Out : Type} [Inhabited Msg]
    (valid : ℕ → List Bool → Msg → Msg → Bool)
    (encOut : Out ↪ List Bool)
    (keyGen : ℕ → ProbComp (List Bool × List Bool))
    (encrypt : ℕ → List Bool → Msg → ProbComp (List Bool))
    (decrypt : ℕ → List Bool → List Bool → Option Out)
    (decBound : ℕ → List Bool → ℕ) (Q : ℕ → ℕ)
    (adversary : MultiCCA2AdversaryOf Msg) (n : ℕ)
    (hdecBound : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ req, (encOption encOut (decrypt n keys.2 req)).length ≤ decBound n req)
    (hQ : ∀ keys ∈ (ProbComp.eval (keyGen n)).support,
      ∀ challenges stateA, ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support →
        challenges.length ≤ Q n) :
    Game.advantage
      (ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary false n))
      (ProbComp.eval (cca2MultiGameOn valid encOut keyGen encrypt decrypt adversary true n)) =
      dyadicSize (Q n) *
        Game.advantage
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) false n))
          (ProbComp.eval
            (cca2GameOn valid encOut keyGen encrypt decrypt
              (cca2MultiToSingle valid encrypt decBound Q adversary) true n)) := by
  exact NNReal.eq (by
    rw [NNReal.coe_mul, Game.coe_advantage, Game.coe_advantage, NNReal.coe_natCast,
      cca2MultiGameOn_gap valid encOut keyGen encrypt decrypt decBound Q adversary n hdecBound hQ,
      abs_mul, Nat.abs_cast])

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 (printed p. 468), not the cited
result: single-challenge 1CCA security implies batch-challenge multi-challenge CCA security, in
which all encryption queries come in one batch between Phase 1 and Phase 2 decryption queries,
whenever `valid`, `keyGen`, `encrypt`, and `decrypt` are polynomial-time / strict PPT. Attack
Game 12.1 (p. 467) lets the adversary interleave encryption and decryption queries adaptively;
Theorem 12.1 for that game is `INDCCA2On.indcca2InterleavedOn`
(`CslibFrontier/Crypto/Computational/Encryption/CCA/Interleaved.lean`). -/
theorem INDCCA2On.indcca2MultiOn {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2On valid encMsg encOut keyGen encrypt decrypt) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt := by
  intro adversary hA
  obtain ⟨ck, dk, hlenKey⟩ := hkeyGen.length_le
  obtain ⟨decBound, hdecBoundPoly, hdecBound⟩ := exists_decryption_length_bound hkeyGen hdecrypt
  obtain ⟨_, _, _, _, cq, dq, _, _, hlenCh⟩ := hA.query_bounds
  let Q : ℕ → ℕ := fun n => cq * (n + ck * (n + 1) ^ dk + 2) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by fun_prop
  have hQ (n : ℕ) (keys : List Bool × List Bool)
      (hkeys : keys ∈ (ProbComp.eval (keyGen n)).support)
      (challenges : List (Msg × Msg)) (stateA : List Bool)
      (hchoice : ((challenges, stateA), ()) ∈ (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (cca2Phase1Oracle encOut decrypt n keys.2))
        (adversary.choose n keys.1)).run ())).support) :
      challenges.length ≤ Q n := by
    have hk := hlenKey n keys hkeys
    simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply] at hk
    rw [ProbOracleComp.eval_run_interpret_eq_runWith] at hchoice
    rw [ProbOracleComp.runWith_eq_run_interpret] at hchoice
    have hch := (hlenCh n keys.1 Unit _ () () (challenges, stateA) hchoice).1
    exact hch.trans (Nat.mul_le_mul_left cq (Nat.pow_le_pow_left (by omega) dq))
  have hsingleNeg := h (cca2MultiToSingle valid encrypt decBound Q adversary)
    (isPPT_cca2MultiToSingle hvalid hencrypt hdecBoundPoly hQPoly hA)
  negligible using fun n => (advantage_cca2MultiGameOn valid encOut keyGen encrypt decrypt
    decBound Q adversary n (hdecBound n) (hQ n)).le

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2 (printed
p. 468), not the cited result: single-challenge 1CCA security and batch-challenge multi-challenge
CCA security are equivalent under any polynomial-time challenge-pair admissibility predicate
`valid`. Batch challenges restrict the adaptively interleaved queries of Attack Game 12.1
(p. 467); the equivalence for that game is `indcca2InterleavedOn_iff_indcca2On`. -/
theorem indcca2MultiOn_iff_indcca2On {Msg Out : Type} [Inhabited Msg]
    {valid : ℕ → List Bool → Msg → Msg → Bool}
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hvalid : ComputableInPolyTime
      (fun ⟨n, pk, m₀, m₁⟩ => valid n pk m₀ m₁)
      (encChallengePairInput encMsg) encBool)
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2MultiOn valid encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2On valid encMsg encOut keyGen encrypt decrypt :=
  ⟨INDCCA2MultiOn.indcca2On,
    INDCCA2On.indcca2MultiOn hvalid hkeyGen hencrypt hdecrypt⟩

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1, not the cited result:
unrestricted single-challenge 1CCA security implies unrestricted batch-challenge multi-challenge
CCA security. Theorem 12.1 for interleaved queries is `INDCCA2Of.indcca2InterleavedOf`. -/
theorem INDCCA2Of.indcca2MultiOf {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut))
    (h : INDCCA2Of encMsg encOut keyGen encrypt decrypt) :
    INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt :=
  INDCCA2On.indcca2MultiOn (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt h

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2, not the
cited result: unrestricted 1CCA and batch-challenge multi-challenge CCA security are
equivalent. -/
theorem indcca2MultiOf_iff_indcca2Of {Msg Out : Type} [Inhabited Msg]
    {encMsg : Msg ↪ List Bool} {encOut : Out ↪ List Bool}
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Msg → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Out}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encMsg) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encOut)) :
    INDCCA2MultiOf encMsg encOut keyGen encrypt decrypt ↔
      INDCCA2Of encMsg encOut keyGen encrypt decrypt :=
  indcca2MultiOn_iff_indcca2On (ComputableInPolyTime.const true)
    hkeyGen hencrypt hdecrypt

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1, not the cited result: bit
single-challenge 1CCA security implies bit batch-challenge multi-challenge CCA security. Theorem
12.1 for interleaved queries is `INDCCA2.indcca2Interleaved`. -/
theorem INDCCA2.indcca2Multi
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encBool))
    (h : INDCCA2 keyGen encrypt decrypt) :
    INDCCA2Multi keyGen encrypt decrypt :=
  INDCCA2Of.indcca2MultiOf hkeyGen hencrypt hdecrypt h

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2, not the
cited result: bit 1CCA and bit batch-challenge multi-challenge CCA security are equivalent. -/
theorem indcca2Multi_iff_indcca2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option Bool}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBool) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encBool)) :
    INDCCA2Multi keyGen encrypt decrypt ↔ INDCCA2 keyGen encrypt decrypt :=
  indcca2MultiOf_iff_indcca2Of hkeyGen hencrypt hdecrypt

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1, not the cited result: word
single-challenge 1CCA security implies word batch-challenge multi-challenge CCA security. Theorem
12.1 for interleaved queries is `WordINDCCA2.wordINDCCA2Interleaved`. -/
theorem WordINDCCA2.wordINDCCA2Multi
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encBits))
    (h : WordINDCCA2 keyGen encrypt decrypt) :
    WordINDCCA2Multi keyGen encrypt decrypt :=
  INDCCA2On.indcca2MultiOn (by fun_prop) hkeyGen hencrypt hdecrypt h

/-- Batch-challenge step toward [BonehShoup2023], Theorem 12.1 with Definition 12.2, not the
cited result: word 1CCA and word batch-challenge multi-challenge CCA security are equivalent. -/
theorem wordINDCCA2Multi_iff_wordINDCCA2
    {keyGen : ℕ → ProbComp (List Bool × List Bool)}
    {encrypt : ℕ → List Bool → List Bool → ProbComp (List Bool)}
    {decrypt : ℕ → List Bool → List Bool → Option (List Bool)}
    (hkeyGen : IsPPTOn encUnary (encPair encBits encBits) keyGen)
    (hencrypt : IsPPTOn (encKeyedInput encBits) encBits
      (fun ⟨n, pk, m⟩ => encrypt n pk m))
    (hdecrypt : ComputableInPolyTime
      (fun ⟨n, sk, ct⟩ => decrypt n sk ct)
      (encKeyedInput encBits) (encOption encBits)) :
    WordINDCCA2Multi keyGen encrypt decrypt ↔ WordINDCCA2 keyGen encrypt decrypt :=
  indcca2MultiOn_iff_indcca2On (by fun_prop) hkeyGen hencrypt hdecrypt

end Cslib.Crypto.Encryption
