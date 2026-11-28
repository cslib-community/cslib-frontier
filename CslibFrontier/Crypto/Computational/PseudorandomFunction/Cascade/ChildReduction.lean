/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Cascade.ChildRouting
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Languages.Probabilistic.Memoize
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution
import CslibFrontier.Languages.Probabilistic.Oracle.Support

/-!
# Single-key challenge program for cascade child channels

A client uses natural-number channels in order of first visit. The program draws a challenge
index using fair bits and rejects indices outside the channel budget. It memoizes random replies
on earlier channels, forwards the selected channel to a single external word oracle, and uses
independent private keys for later channels. Inputs are read as fixed-width blocks and replies
are capped at the state width.

## Main definitions

* `Cslib.Crypto.CascadeChildChallengeState`: first-use cursor and lazy answer cache.
* `Cslib.Crypto.cascadeChildChallengeHandler`: one simulated child query.
* `Cslib.Crypto.cascadeChildChallengeAtProgram`: simulate the client at a fixed index and key word.
* `Cslib.Crypto.cascadeChildChallengeProgram`: sample the challenge index and private keys,
  then simulate the client.

## Main results

* `Cslib.Crypto.isQueryBounded_cascadeChildChallengeProgram`: the simulation preserves
  the client's external query bound.
* `Cslib.Crypto.isOraclePPTOn_cascadeChildChallengeProgram`: strict oracle PPT for the
  sampled simulation given a strict certificate for its encoded client.

## References

* [BonehShoup2023], v0.6, Section 4.6.1 (printed pp. 152–154) and Section 6.4.2
  (printed pp. 229–230), for the adjacent-hybrid step.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

/-- State of the single-key simulation. The cursor counts channels already assigned, and
only channels before the challenge need an answer cache. -/
structure CascadeChildChallengeState where
  /-- Number of child channels assigned in first-use order. -/
  assigned : ℕ
  /-- Sampled ideal answers, keyed by channel number and normalized block. -/
  idealAnswers : List ((ℕ × List Bool) × List Bool)

/-- Answer a request for an already assigned channel or the next unused channel, below
`count`. Earlier channels have independent lazy random functions, `selected` calls the
external oracle, and later channels use separate `n`-bit rows of `keys`. -/
@[expose]
noncomputable def cascadeChildChallengeHandler
    (family : List Bool → List Bool → List Bool) (width n count selected : ℕ)
    (keys : List Bool) (request : ℕ × List Bool) (state : CascadeChildChallengeState) :
    WordOracleComp Unit (List Bool × CascadeChildChallengeState) :=
  if request.1 < count ∧ request.1 ≤ state.assigned then
    let block := BitString.listRow width 0 request.2
    let next := { state with assigned := max state.assigned (request.1 + 1) }
    if request.1 < selected then do
      let (reply, cache) ← ProbOracleComp.sample
        (memoize (fun _ => BitString.sampleList n) (request.1, block) state.idealAnswers)
      return (reply, { next with idealAnswers := cache })
    else if request.1 = selected then do
      let reply ← ProbOracleComp.query ((), block)
      return (reply.take n, next)
    else pure ((family (BitString.listRow n request.1 keys) block).take n, next)
  else pure ([], state)

/-- Framed unary cursor followed by the memoization cache. -/
private enc_structure encChallengeState : CascadeChildChallengeState where
  assigned : (encUnary), idealAnswers : (encMemoCache encCascadeChildRequest encBits)

private structure ChallengeParameters where
  width : ℕ
  security : ℕ
  count : ℕ
  selected : ℕ
  keys : List Bool

/-- Framed unary block width, security parameter and channel count, then a framed binary
challenge index and the private key word. -/
private enc_structure encChallengeParameters : ChallengeParameters where
  width : (encUnary), security : (encUnary), count : (encUnary), selected : (encNat),
  keys : (encBits)

private abbrev ChallengeCall := ChallengeParameters × (ℕ × List Bool) × CascadeChildChallengeState

/-- The parameters, framed child request and current state. -/
private abbrev encChallengeCall : ChallengeCall ↪ List Bool :=
  encPair encChallengeParameters (encPair encCascadeChildRequest encChallengeState)

private theorem isOraclePPTOn_challengeHandler {family : List Bool → List Bool → List Bool}
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) :
    IsOraclePPTOn encChallengeCall (encPair encBits encChallengeState)
      (fun x : ChallengeCall => cascadeChildChallengeHandler family x.1.width x.1.security
        x.1.count x.1.selected x.1.keys x.2.1 x.2.2) := by
  let hparams := ComputableInPolyTime.fst encChallengeParameters
    (encPair encCascadeChildRequest encChallengeState)
  let hrequestState := ComputableInPolyTime.snd encChallengeParameters
    (encPair encCascadeChildRequest encChallengeState)
  let hchannel := hrequestState.fst'.fst'
  let hchannelBin := ComputableInPolyTime.unary_to_binary.comp hchannel
  let hstate := hrequestState.snd'
  let hcache := encChallengeState_idealAnswers_polyTime hstate
  let hcursor := encChallengeState_assigned_polyTime hstate
  let hn := encChallengeParameters_security_polyTime hparams
  let hcount := encChallengeParameters_count_polyTime hparams
  let hselected := encChallengeParameters_selected_polyTime hparams
  let hwidth := encChallengeParameters_width_polyTime hparams
  let hkeys := encChallengeParameters_keys_polyTime hparams
  let hblock := ComputableInPolyTime.bitsRowWithInput hwidth (.const 0) hrequestState.fst'.snd'
  let hnext := hcursor.unary_max' (hchannel.unary_add' (.const 1))
  let hnextState := encChallengeState_mk_polyTime hnext hcache
  have hguard : ComputableInPolyTime (fun x : ChallengeCall =>
      decide (x.2.1.1 < x.1.count ∧ x.2.1.1 ≤ x.2.2.assigned)) encChallengeCall encBool :=
    ComputableInPolyTime.decide_and (hchannel.unary_lt' hcount) (hchannel.unary_le' hcursor)
  simp only [cascadeChildChallengeHandler]
  refine IsOraclePPTOn.ite hguard ?_
    (((ComputableInPolyTime.const ([] : List Bool)).prod hstate).isPPTOn.isOraclePPTOn)
  refine IsOraclePPTOn.ite (hchannelBin.binary_lt' hselected) ?_ ?_
  · have hsample := IsPPTOn.memoize (compute := fun (x : ChallengeCall) (_ : ℕ × List Bool) =>
        BitString.sampleList x.1.security) hn.sampleList (hchannel.prod hblock) hcache
    let hin := ComputableInPolyTime.fst encChallengeCall
      (encPair encBits (encMemoCache encCascadeChildRequest encBits))
    let hout := ComputableInPolyTime.snd encChallengeCall
      (encPair encBits (encMemoCache encCascadeChildRequest encBits))
    simpa only [ProbOracleComp.sample_map, bind_pure_comp] using
      (hsample.isOraclePPTOn (Operation := Unit)).map_with
        (f := fun x out =>
          (out.1, CascadeChildChallengeState.mk (max x.2.2.assigned (x.2.1.1 + 1)) out.2))
        (hout.fst'.prod (encChallengeState_mk_polyTime (hnext.comp hin) hout.snd'))
  · refine IsOraclePPTOn.ite (hchannelBin.decide_eq' hselected) ?_ ?_
    · let hin := ComputableInPolyTime.fst encChallengeCall encBits
      let hout := ComputableInPolyTime.snd encChallengeCall encBits
      simpa only [bind_pure_comp, Functor.map_map, Function.comp_def] using
        (IsOraclePPTOn.query_take () hblock hn).map_with
          (f := fun x reply => (reply, { x.2.2 with assigned := max x.2.2.assigned (x.2.1.1 + 1) }))
          (hout.prod (hnextState.comp hin))
    · let hkey := ComputableInPolyTime.bitsRowWithInput hn hchannel hkeys
      exact (((hEval.comp (hkey.prod hblock)).bitsTakeWithInput hn).prod hnextState)
        |>.isPPTOn.isOraclePPTOn

private theorem challengeHandler_bounds (family : List Bool → List Bool → List Bool)
    (width n count selected : ℕ) (keys : List Bool) (request : ℕ × List Bool)
    (state : CascadeChildChallengeState) (result : List Bool × CascadeChildChallengeState)
    (hwidth : ∀ entry ∈ state.idealAnswers, entry.2.length ≤ n)
    (hresult : result ∈ OracleComp.support
      (cascadeChildChallengeHandler family width n count selected keys request state)) :
    (∀ entry ∈ result.2.idealAnswers, entry.2.length ≤ n) ∧ result.1.length ≤ n ∧
      (encChallengeState result.2).length ≤ (encChallengeState state).length +
        (4 * (2 * count + 1 + width) + 2 * n + 5) := by
  unfold cascadeChildChallengeHandler at hresult
  split at hresult
  · rename_i hallowed
    have hcursor : max state.assigned (request.1 + 1) ≤ state.assigned + 1 := by
      have := hallowed.2
      omega
    have hchannel := hallowed.1
    split at hresult
    · obtain ⟨⟨reply, cache⟩, hcache, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
      obtain rfl := OracleComp.eq_of_mem_supportWith_pure hreply
      change (reply, cache) ∈ OracleComp.support (ProbOracleComp.sample (spec :=
        fun _ : Unit × List Bool => List Bool)
          (memoize (fun _ => BitString.sampleList n)
            (request.1, BitString.listRow width 0 request.2) state.idealAnswers)) at hcache
      rw [ProbOracleComp.support_sample, ProbComp.eval_memoize] at hcache
      simp only [BitString.eval_sampleList] at hcache
      obtain ⟨hreply, hwidth', hgrowth⟩ := memoize_call_size_le encCascadeChildRequest encBits
        (fun _ => BitString.uniformList n) (request.1, BitString.listRow width 0 request.2)
        state.idealAnswers n (by simpa only [encBits_apply] using hwidth)
        (fun word hw => by simpa only [encBits_apply] using
          (BitString.length_of_mem_support_uniformList hw).le) (reply, cache) hcache
      refine ⟨hwidth', hreply, ?_⟩
      simp only [encChallengeState_apply, length_encPair, encUnary_apply, List.length_replicate,
        encCascadeChildRequest, encBits_apply, BitString.length_listRow] at hgrowth ⊢
      omega
    · split at hresult
      · obtain ⟨reply, _, hreply⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
        obtain rfl := OracleComp.eq_of_mem_supportWith_pure hreply
        refine ⟨hwidth, List.length_take_le _ _, ?_⟩
        simp only [encChallengeState_apply, length_encPair, encUnary_apply, List.length_replicate]
        omega
      · obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
        refine ⟨hwidth, List.length_take_le _ _, ?_⟩
        simp only [encChallengeState_apply, length_encPair, encUnary_apply, List.length_replicate]
        omega
  · obtain rfl := OracleComp.eq_of_mem_supportWith_pure hresult
    exact ⟨hwidth, Nat.zero_le _, Nat.le_add_right _ _⟩

/-- Run the simulated child oracle from an empty state with a fixed challenge channel and
key word. The sampled wrapper rejects out-of-range channels before calling this program. -/
@[expose]
noncomputable def cascadeChildChallengeAtProgram
    (family : List Bool → List Bool → List Bool) (width n count selected : ℕ)
    (keys : List Bool) (program : WordOracleComp ℕ Bool) : WordOracleComp Unit Bool :=
  Prod.fst <$> (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k)))
      (cascadeChildChallengeHandler family width n count selected keys))
    program).run ⟨0, []⟩

private def decodeChildRequest (word : List Bool) : ℕ × List Bool :=
  ((unframe word).length, dropFrame word)

private theorem decodeChildRequest_encode (request : ℕ × List Bool) :
    decodeChildRequest (encCascadeChildRequest request) = request := by
  rcases request with ⟨channel, block⟩
  simp only [decodeChildRequest, encCascadeChildRequest, unframe_encPair,
    dropFrame_encPair_encBits, encUnary_apply, List.length_replicate]

private def forwardChildRequest (request : ℕ × List Bool) : WordOracleComp Unit (List Bool) :=
  ProbOracleComp.query ((), encCascadeChildRequest request)

private theorem isOraclePPTOn_challengeAt {α : Type} {input : α ↪ List Bool}
    {program : α → WordOracleComp ℕ Bool} {family : List Bool → List Bool → List Bool}
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hprogram : IsOraclePPTOn input encBool
      (fun a => ProbOracleComp.simulate forwardChildRequest (program a))) :
    IsOraclePPTOn (encPair input encChallengeParameters) encBool (fun x : α × ChallengeParameters =>
      cascadeChildChallengeAtProgram family x.2.width x.2.security x.2.count
        x.2.selected x.2.keys (program x.1)) := by
  let encCaller := encPair input encChallengeParameters
  let encCall := encHandlerCall encCaller (encFinEnum Unit) encChallengeState
  let params := ComputableInPolyTime.snd input encChallengeParameters
  let hparams := params.comp (ComputableInPolyTime.fst encCaller
    (encPair (encPair (encFinEnum Unit) encBits) encChallengeState))
  let hrequestState := ComputableInPolyTime.snd encCaller
    (encPair (encPair (encFinEnum Unit) encBits) encChallengeState)
  let hword := hrequestState.fst'.snd'
  let hdecode := ((ComputableInPolyTime.unframe.comp hword).length_bits_comp).prod
    (ComputableInPolyTime.dropFrame.comp hword)
  let handler (x : α × ChallengeParameters) (request : Unit × List Bool) state :=
    cascadeChildChallengeHandler family x.2.width x.2.security x.2.count x.2.selected
      x.2.keys (decodeChildRequest request.2) state
  have hhandler : IsOraclePPTOn encCall (encPair encBits encChallengeState)
      (fun x => handler x.1 x.2.1 x.2.2) :=
    (isOraclePPTOn_challengeHandler hEval).preprocess (hparams.prod
      (hdecode.prod hrequestState.snd'))
  let hresourceParams := params.comp (ComputableInPolyTime.fst encCaller encBits)
  let hcount := encChallengeParameters_count_polyTime hresourceParams
  let hwidth := encChallengeParameters_width_polyTime hresourceParams
  let hn := encChallengeParameters_security_polyTime hresourceParams
  let fourCountWidth := (ComputableInPolyTime.const 4).unary_mul'
    (((ComputableInPolyTime.const 2).unary_mul' hcount).unary_add' (.const 1) |>.unary_add' hwidth)
  let hresources := (fourCountWidth.unary_add'
    ((ComputableInPolyTime.const 2).unary_mul' hn)).unary_add' (.const 5)
  have hrun := hprogram.run_interpret_preprocess_open
    (operationEncoding := encFinEnum Unit) (stateEncoding := encChallengeState)
    (handler := handler) (prepare := Prod.fst) (initial := fun _ => ⟨0, []⟩)
    (resources := fun x _ => 4 * (2 * x.2.count + 1 + x.2.width) + 2 * x.2.security + 5)
    (ComputableInPolyTime.fst input encChallengeParameters) hhandler (.const _)
    (fun x state => ∀ entry ∈ state.idealAnswers, entry.2.length ≤ x.2.security)
    (fun _ => by simp) hresources (fun x request state hcache result hresult => by
      obtain ⟨hcache', hreply, hgrowth⟩ := challengeHandler_bounds family x.2.width x.2.security
        x.2.count x.2.selected x.2.keys (decodeChildRequest request.2) state result hcache hresult
      exact ⟨hcache', by omega, hgrowth⟩)
  refine (hrun.map (ComputableInPolyTime.fst _ _)).congr ?_
  intro x State oracle state
  unfold cascadeChildChallengeAtProgram
  rw [ProbOracleComp.interpret_simulate]
  simp only [forwardChildRequest, ProbOracleComp.interpret_query, decodeChildRequest_encode,
    handler]

/-- Sample a challenge index from `indexBits` fair bits. If it is in range, draw one private
`n`-bit key per channel and run the client with the simulated child oracle. An out-of-range
index returns `false` before the client runs. -/
@[expose]
noncomputable def cascadeChildChallengeProgram
    (family : List Bool → List Bool → List Bool) (width n count indexBits : ℕ)
    (program : WordOracleComp ℕ Bool) : WordOracleComp Unit Bool := do
  let selected ← ProbOracleComp.sample (ProbComp.sampleBinaryNat indexBits)
  if selected < count then
    let keys ← ProbOracleComp.sample (BitString.sampleList (count * n))
    cascadeChildChallengeAtProgram family width n count selected keys program
  else pure false

/-- The sampled challenge simulation is strict oracle PPT for a client certified on the single
word port. The channel budget, block width and number of fair bits are unary computations, while
the sampled index stays binary even on the rejection branch. -/
theorem isOraclePPTOn_cascadeChildChallengeProgram {α : Type} {input : α ↪ List Bool}
    {program : α → WordOracleComp ℕ Bool} {family : List Bool → List Bool → List Bool}
    {width n count indexBits : α → ℕ}
    (hEval : ComputableInPolyTime (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (hprogram : IsOraclePPTOn input encBool (fun a => ProbOracleComp.simulate
      (fun request => ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
        ((), encCascadeChildRequest request)) (program a)))
    (hwidth : ComputableInPolyTime width input encUnary)
    (hn : ComputableInPolyTime n input encUnary)
    (hcount : ComputableInPolyTime count input encUnary)
    (hbits : ComputableInPolyTime indexBits input encUnary) :
    IsOraclePPTOn input encBool (fun a =>
      cascadeChildChallengeProgram family (width a) (n a) (count a) (indexBits a) (program a)) := by
  let hin := ComputableInPolyTime.fst input encNat
  let hselected := ComputableInPolyTime.snd input encNat
  let hcountBin := ComputableInPolyTime.unary_to_binary.comp (hcount.comp hin)
  let hsampleKeys := ((hcount.unary_mul' hn).comp hin).sampleList
  let hcaller := ComputableInPolyTime.fst (encPair input encNat) encBits
  let hkeys := ComputableInPolyTime.snd (encPair input encNat) encBits
  let hparams := encChallengeParameters_mk_polyTime (hwidth.comp (hin.comp hcaller))
    (hn.comp (hin.comp hcaller)) (hcount.comp (hin.comp hcaller))
    (hselected.comp hcaller) hkeys
  have hrun := (isOraclePPTOn_challengeAt hEval hprogram).preprocess
    ((hin.comp hcaller).prod hparams)
  unfold cascadeChildChallengeProgram
  exact ((hbits.sampleBinaryNat).isOraclePPTOn (Operation := Unit)).bind_with
    (IsOraclePPTOn.ite (hselected.binary_lt' hcountBin)
      ((hsampleKeys.isOraclePPTOn (Operation := Unit)).bind_with hrun)
      ((ComputableInPolyTime.const false).isPPTOn.isOraclePPTOn))

private theorem isQueryBounded_cascadeChildChallengeHandler
    (family : List Bool → List Bool → List Bool) (width n count selected : ℕ)
    (keys : List Bool) (request : ℕ × List Bool) (state : CascadeChildChallengeState) :
    ProbOracleComp.IsQueryBounded
      (cascadeChildChallengeHandler family width n count selected keys request state) 1 := by
  unfold cascadeChildChallengeHandler
  split
  · dsimp only
    split
    · exact ((ProbOracleComp.IsQueryBounded.sample _).bind fun _ => .pure _ 0).mono (by decide)
    · split
      · exact (ProbOracleComp.IsQueryBounded.query _).bind fun _ => .pure _ 0
      · exact .pure _ 1
  · exact .pure _ 1

/-- Local key and answer sampling consumes no external queries. The challenge channel forwards
at most one external query per client query. -/
theorem isQueryBounded_cascadeChildChallengeProgram
    (family : List Bool → List Bool → List Bool) (width n count indexBits : ℕ)
    {program : WordOracleComp ℕ Bool} {budget : ℕ}
    (hbudget : program.IsQueryBounded budget) :
    ProbOracleComp.IsQueryBounded
      (cascadeChildChallengeProgram family width n count indexBits program) budget := by
  unfold cascadeChildChallengeProgram
  refine ((ProbOracleComp.IsQueryBounded.sample _).bind (m := budget) fun selected => ?_).mono
    (by simp)
  split
  · refine ((ProbOracleComp.IsQueryBounded.sample _).bind (m := budget) fun keys => ?_).mono
      (by simp)
    unfold cascadeChildChallengeAtProgram
    apply (OracleComp.isCostBounded_map_iff _ _ _).mpr
    refine OracleComp.IsCostBounded.run_interpret (fun query state => ?_) hbudget _
    cases query with
    | inl k =>
      change ((StateT.lift (ProbOracleComp.sample (ProbComp.unifFin k))).run state).IsQueryBounded 0
      rw [StateT.run_lift, bind_pure_comp]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
        (ProbOracleComp.IsQueryBounded.sample _)
    | inr request =>
      exact isQueryBounded_cascadeChildChallengeHandler family width n count selected keys
        request state
  · exact .pure _ budget

end Cslib.Crypto
