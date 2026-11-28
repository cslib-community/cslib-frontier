/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Probabilistic.Oracle.Codec
import CslibFrontier.Crypto.Computational.Encryption.Authenticated
import CslibFrontier.Crypto.Computational.Encryption.EncryptThenMAC
import CslibFrontier.Languages.Probabilistic.Oracle.Lens
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.UntilBad.PlantedQuery
import CslibFrontier.Probability.StatisticalDistance.CouplingBind
import CslibFrontier.Tactic.PolyTime
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.SuppCases

/-!
# Checked Examples for `CouplingBind`, `StateLens`, `PlantedQuery`, and `OracleCodec`

Exercises the combinators on concrete, non-vacuous instances:
1. `PMF.CoupledWithin.closeTo`, `CoupledWithin.bind`, `bind_left`, and `bind_right`.
2. `StateLens.zoom` (including `memoize` zooming), `StateLens.latch`,
   `probIdenticalUntilBad_latch`, and `toOuterMeasure_latch_le` on a named 3-field record.
3. `ProbOracleComp.plantedHandler`, `toOuterMeasure_bad_le_sum_planted`, and
   `toOuterMeasure_bad_le_sum_planted_of_cost` on adaptive multi-query programs, plus `rfl`
   verification that `SymmetricCipher.encCCAToCIState` preserves exact encoded bit-words.
4. `OracleCodec.bitStrings`, `queryWord`, `toWord`, `adapt_toWord`, `runWith_wordOracle_toWord`,
   `run_wordOracle_toWord`, `isQueryBounded_toWord`, `IsOraclePPTOn.queryWord`, and
   `IsOraclePPTOn.run_wordOracle_open`.
-/

namespace CslibFrontierTests.Crypto.OracleCodecLens

open Cslib Cslib.Crypto Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

/-! ### 1. `CoupledWithin.bind` and `CoupledWithin.closeTo` -/

private theorem coupledWithin_uniformBool_pure :
    PMF.CoupledWithin (PMF.uniformOfFintype Bool) (PMF.pure false) (1 / 2) := by
  refine ⟨(PMF.uniformOfFintype Bool).map (·, false), ?_, ?_, ?_⟩
  · exact (PMF.map_comp _ _ _).trans (PMF.map_id _)
  · exact (PMF.map_comp _ _ _).trans (PMF.map_const _ false)
  · rw [PMF.toOuterMeasure_map_apply]
    have hset : (fun b : Bool => (b, false)) ⁻¹' {p : Bool × Bool | p.1 ≠ p.2} =
        ({true} : Set Bool) := by
      ext b; cases b <;> simp
    rw [hset, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
    simp

-- Sequencing coupled distributions via `CoupledWithin.bind` (exploiting support restriction on `ν`
-- AND a nonzero continuation error `1 / 2`) and projecting to `CloseTo`.
example : CloseTo
    ((PMF.uniformOfFintype Bool).bind fun b =>
      if b then PMF.pure true else PMF.uniformOfFintype Bool)
    ((PMF.pure false).bind fun _ => PMF.pure false)
    (1 / 2 + 1 / 2) := by
  refine (coupledWithin_uniformBool_pure.bind fun b hb => ?_).closeTo
  rw [PMF.mem_support_pure_iff] at hb
  subst hb
  exact coupledWithin_uniformBool_pure

example : PMF.CoupledWithin
    ((PMF.uniformOfFintype Bool).bind fun b => PMF.pure (!b))
    ((PMF.pure false).bind fun b => PMF.pure (!b))
    (1 / 2) :=
  coupledWithin_uniformBool_pure.bind_left fun b => PMF.pure (!b)

example : PMF.CoupledWithin
    ((PMF.pure false).bind fun _ => PMF.uniformOfFintype Bool)
    ((PMF.pure false).bind fun _ => PMF.pure false)
    (1 / 2) :=
  PMF.CoupledWithin.bind_right (PMF.pure false) fun _ _ => coupledWithin_uniformBool_pure

/-! ### 2. `StateLens.zoom` and `StateLens.latch` on a Named Record -/

private structure ToyState where
  cache : List (Bool × Bool)
  calls : ℕ
  bad : Bool
  deriving DecidableEq

private def ToyState.cacheLens : StateLens ToyState (List (Bool × Bool)) where
  get s := s.cache
  set s c := { s with cache := c }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

private def ToyState.callsLens : StateLens ToyState ℕ where
  get s := s.calls
  set s n := { s with calls := n }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

private def ToyState.badLens : StateLens ToyState Bool where
  get s := s.bad
  set s b := { s with bad := b }
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

private noncomputable def bumpCalls (_ : Unit) : StateT ℕ PMF ℕ :=
  fun n => PMF.pure (n, n + 1)

private def twoCalls : ProbOracleComp (fun _ : Unit => ℕ) (ℕ × ℕ) := do
  let a ← ProbOracleComp.query ()
  let b ← ProbOracleComp.query ()
  return (a, b)

-- `StateLens.runWith_zoom` advances `calls` while preserving `cache` and `bad` intact.
example (s : ToyState) :
    ProbOracleComp.runWith (fun q => ToyState.callsLens.zoom (bumpCalls q)) twoCalls s =
      PMF.pure ((s.calls, s.calls + 1), { s with calls := s.calls + 2 }) := by
  rw [ToyState.callsLens.runWith_zoom]
  simp [ToyState.callsLens, twoCalls, bumpCalls, runWith_norm, pmf_norm, Nat.add_assoc]

-- `StateLens.zoom_memoize_of_none` and `zoom_memoize_of_some` update only `cache`.
example :
    ToyState.cacheLens.zoom (memoize (fun b => PMF.pure (!b)) true) ⟨[], 7, false⟩ =
      PMF.pure (false, ⟨[(true, false)], 7, false⟩) := by
  rw [ToyState.cacheLens.zoom_memoize_of_none _ true _ rfl]
  simp [ToyState.cacheLens]

-- `StateLens.latch`, `probIdenticalUntilBad_latch`, and `toOuterMeasure_latch_le`.
private noncomputable def faithfulToyStep (b : Bool) (st : ToyState) : PMF (Bool × ToyState) :=
  if (st.cache.lookup b).isSome then
    PMF.pure (false, { st with bad := true })
  else
    PMF.pure (true, ⟨(b, true) :: st.cache, st.calls + 1, false⟩)

private noncomputable def forgetfulToyStep (b : Bool) (st : ToyState) : PMF (Bool × ToyState) :=
  if (st.cache.lookup b).isSome then
    PMF.pure (true, { st with bad := true })
  else
    PMF.pure (true, ⟨(b, true) :: st.cache, st.calls + 1, false⟩)

example : ProbOracleComp.IdenticalUntilBad
    (ToyState.badLens.latch faithfulToyStep)
    (ToyState.badLens.latch forgetfulToyStep)
    ToyState.badLens.Bad := by
  refine ToyState.badLens.probIdenticalUntilBad_latch _ _ fun b st _ ans st' hst' => ?_
  unfold faithfulToyStep forgetfulToyStep
  split_ifs
  · simp only [PMF.pure_apply, Prod.mk.injEq]
    have hne : st' ≠ { st with bad := true } := fun h => by
      rw [h] at hst'
      exact Bool.false_ne_true (by simpa [ToyState.badLens] using hst'.symm)
    simp [hne]
  · rfl

/-! ### 3. `PlantedQuery` Union Bound & `encCCAToCIState` Word-Layout Check -/

-- Exact `rfl` check that migrating `ccaToCIHandler` to `PlantedState` + `enc_structure`
-- preserves every encoded bit-word identically.
example (j : ℕ) (b : Bool) (ct : List Bool) :
    (SymmetricCipher.encCCAToCIState ⟨j, b, ct⟩ : List Bool) =
      encPair encUnary (encPair encBool encBits) (j, (b, ct)) :=
  rfl

-- Adaptive 2-query planted-index union bound (`toOuterMeasure_bad_le_sum_planted`):
-- the second query depends on the first query's reply, and `Q = 2` bounds the latching probability.
private noncomputable def secretHitStep (secret : Bool) (q : Bool) (_ : Unit) :
    PMF (Bool × (Unit × Bool)) :=
  PMF.pure (false, ((), q == secret))

private def adaptiveTwoGuesses : ProbOracleComp (fun _ : Bool => Bool) Unit := do
  let r ← ProbOracleComp.query false
  let _ ← ProbOracleComp.query (!r)
  return ()

private theorem isQueryBounded_adaptiveTwoGuesses : adaptiveTwoGuesses.IsQueryBounded 2 := by
  simpa [adaptiveTwoGuesses] using
    (ProbOracleComp.IsQueryBounded.query (spec := fun _ : Bool => Bool) false).bind fun r =>
      (ProbOracleComp.IsQueryBounded.query (spec := fun _ : Bool => Bool) (!r)).bind fun _ =>
        OracleComp.IsCostBounded.pure () 0

example (secret : Bool) :
    (ProbOracleComp.runWith (OracleComp.withBadFlag (secretHitStep secret))
      adaptiveTwoGuesses ((), false)).toOuterMeasure {x | OracleComp.FlagBad x.2} ≤
      ∑ j ∈ Finset.range 2,
        (ProbOracleComp.runWith
            (ProbOracleComp.plantedHandler (fun _ s => PMF.pure (false, s))
              (fun _ => true) _root_.id false (fun _ => false))
            adaptiveTwoGuesses (ProbOracleComp.PlantedOracleState.init j false ())).bind
          (fun x => PMF.pure
            (x.2.planted.hasCaptured && (x.2.planted.candidate == secret)))
          true := by
  refine ProbOracleComp.toOuterMeasure_bad_le_sum_planted
    (embed := fun s : Unit => (s, false))
    (hembed := fun _ => Bool.false_ne_true)
    (sim := fun _ s => PMF.pure (false, s))
    (isBad := fun q _ => q == secret)
    (extract := _root_.id) (defaultCand := false) (dummyReply := fun _ => false)
    (win := fun c _ => c == secret)
    (fun q ⟨⟩ hgood => by
      simp [OracleComp.withBadFlag, secretHitStep, hgood])
    (fun q ⟨⟩ hb => hb)
    isQueryBounded_adaptiveTwoGuesses ()

/-! ### 4. `OracleCodec` Typed-to-Word Lifting & `IsOraclePPTOn` Composition -/

private def typedEchoProg : ProbOracleComp (fun _ : BitString 2 => BitString 3) (BitString 3) := do
  let y ← ProbOracleComp.query (BitString.ofList 2 [true, false])
  return y

private def wordEchoProg : WordOracleComp Unit (BitString 3) :=
  (OracleCodec.bitStrings 2 3).toWord (fun _ => 3) (fun _ w => BitString.ofList 3 w) typedEchoProg

-- `adapt_toWord` recovers the original typed program when replies decode cleanly.
example :
    (OracleCodec.bitStrings 2 3).adapt wordEchoProg = typedEchoProg := by
  refine (OracleCodec.bitStrings 2 3).adapt_toWord
    (fun _ r => by simp [OracleCodec.bitStrings])
    (fun _ r => BitString.ofList_ofFn r) typedEchoProg

-- `run_wordOracle_toWord` equates stateless `ProbComp` evaluation of the word and typed runs.
example (oracle : BitString 2 → ProbComp (BitString 3)) :
    ProbComp.eval (wordEchoProg.run ((OracleCodec.bitStrings 2 3).wordOracle oracle)) =
      ProbComp.eval (typedEchoProg.run oracle) :=
  (OracleCodec.bitStrings 2 3).run_wordOracle_toWord oracle
    (fun _ _ _ => by simp [OracleCodec.bitStrings])
    (fun _ r => BitString.ofList_ofFn r) typedEchoProg

-- `isQueryBounded_toWord` preserves external query budgets.
example : wordEchoProg.IsQueryBounded 1 := by
  refine (OracleCodec.bitStrings 2 3).isQueryBounded_toWord _ _ ?_
  simpa [typedEchoProg] using ProbOracleComp.IsQueryBounded.query (BitString.ofList 2 [true, false])

private def fin2Codec : OracleCodec Unit Bool fun _ => Bool where
  encodeQuery b := ((), [b])
  decodeQuery req := match req.2 with
    | [b] => some b
    | _ => none
  decodeQuery_eq_some_iff := by
    rintro ⟨⟨⟩, w⟩ b
    cases w with
    | nil => simp
    | cons h t =>
      cases t with
      | nil => simp [eq_comm]
      | cons _ _ => simp
  encodeReply _ := ⟨fun b => [b], fun a b h => by simpa using h⟩

private theorem decode_fin2Codec_eq (req : Unit × List Bool) :
    fin2Codec.decodeQuery req =
      if req.2.length == 1 then some (req.2.headD false) else none := by
  rcases req with ⟨⟨⟩, _ | ⟨b, _ | ⟨_, _⟩⟩⟩ <;> rfl

-- `IsOraclePPTOn.queryWord` and `IsOraclePPTOn.run_wordOracle_open` compose cleanly on `fin2Codec`.
private theorem isOraclePPTOn_fin2Query :
    IsOraclePPTOn encBits encBool
      (fun w : List Bool =>
        fin2Codec.queryWord (fun _ => 1) (fun _ r => r.headD false) (w.headD false)) := by
  refine IsOraclePPTOn.queryWord fin2Codec
    (opEncoding := encFinEnum Unit)
    (henc := ?_) (hcap := ComputableInPolyTime.const 1) (hdec := ?_)
  · dsimp only [fin2Codec]
    exact (ComputableInPolyTime.const ()).prod (by polytime)
  · polytime

example :
    IsOraclePPTOn encBits (encPair encBool encUnary)
      (fun w : List Bool =>
        (OracleComp.interpret
          (OracleComp.sumHandler
            (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
            (fin2Codec.wordOracle (fun (q : Bool) (st : ℕ) =>
              (pure (!q, st + 1) : WordOracleComp Empty (Bool × ℕ)))))
          (fin2Codec.queryWord (fun _ => 1) (fun _ r => r.headD false)
            (w.headD false))).run 0) := by
  have hdec : ComputableInPolyTime fin2Codec.decodeQuery
      (encPair (encFinEnum Unit) encBits) (encOption encBool) := by
    rw [funext decode_fin2Codec_eq]
    polytime
  have hencReply : ComputableInPolyTime (fun p : Bool × Bool => fin2Codec.encodeReply p.1 p.2)
      (encPair encBool encBool) encBits := by
    dsimp only [fin2Codec]
    polytime
  have htyped :
      IsOraclePPTOn (encPair encBits (encPair encBool encUnary)) (encPair encBool encUnary)
        (fun ⟨_, q, st⟩ =>
          (pure (!q, st + 1) : WordOracleComp Empty (Bool × ℕ))) := by
    ppt
  refine isOraclePPTOn_fin2Query.run_wordOracle_open fin2Codec false
    (source := encBits) (input := encBits) (output := encBool)
    (opEncoding := encFinEnum Unit) (queryEncoding := encBool) (replyEncoding := encBool)
    (stateEncoding := encUnary)
    (prepare := _root_.id) (initial := fun _ => 0) (resources := fun _ _ => 2)
    (by fun_prop) hdec hencReply htyped (ComputableInPolyTime.const 0)
    (fun _ _ => True) (fun _ => trivial) (by polytime) ?_
  intro _ q st _ res hres
  supp_cases hres with ⟨rfl, rfl⟩
  refine ⟨trivial, ?_, ?_⟩
  · change [!q].length ≤ 2
    simp
  · change (List.replicate (st + 1) true).length ≤ (List.replicate st true).length + 2
    simp only [List.length_replicate]
    exact Nat.add_le_add_left (by decide) st

end CslibFrontierTests.Crypto.OracleCodecLens
