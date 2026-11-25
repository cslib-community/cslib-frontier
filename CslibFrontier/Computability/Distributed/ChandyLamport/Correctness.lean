/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ChandyLamport.Snapshot
public import Cslib.Foundations.Semantics.LTS.OmegaExecution
public import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.List.Perm.Basic

/-!
# Chandy–Lamport consistent-cut permutation, stable-property detection, and liveness

This module proves the main correctness and liveness theorems of the Chandy–Lamport global snapshot
algorithm ([ChandyLamport1985], §3.3, §4 Theorem 1, and §5, pp. 70–75):

1. **FIFO cut invariant (`project_chan_eq_preInFlight_append_postInFlight`,
   `preRecv_pops_preInFlight`, `postRecv_records_iff_preInFlight`):** At every reachable augmented
   state, each channel `(u, v)` splits into `preInFlight` (application messages sent before `u`
   recorded) followed by `postInFlight` (application messages sent after `u` recorded), separated by
   `.marker` while `.marker` is in transit. Pre-snapshot receives consume exclusively from
   `preInFlight` (no post-snapshot message is ever received pre-snapshot), and post-snapshot
   receives append `msg` to `chanRec` if and only if `msg` came from `preInFlight`.
2. **Causal permutation & consistent-cut reachability (`chandyLamport_perm_mTr`,
   `chandyLamport_consistent_cut`):** For any finite execution `S_init →*[xl] S_final` starting from
   a pre-snapshot state `S_init` and ending at a snapshot-complete state `S_final`, splitting the
   underlying application events of `xl` into pre-snapshot events (`tracePreEvents S_init xl`)
   followed by post-snapshot events (`tracePostEvents S_init xl`) yields a valid permutation of
   `eraseTrace xl` in `sys.lts` whose intermediate state between all pre-snapshot events and all
   post-snapshot events is literally `extractSnapshot S_final`. In particular:
   `sys.lts.CanReach (project S_init) (extractSnapshot S_final) ∧`
   `sys.lts.CanReach (extractSnapshot S_final) (project S_final)`.
3. **Stable-property detection (`stablePred_transfer`):** For every `IsStablePred sys Φ`,
   `(Φ (extractSnapshot S_final) → Φ (project S_final))` and
   `(¬ Φ (extractSnapshot S_final) → ¬ Φ (project S_init))`.
4. **Snapshot completion liveness (`snapshot_liveness`, `snapshot_liveness_complete`,
   `System.InputEnabled.exists_fair_snapOmegaExecution`):** Under weak FIFO channel fairness on any
   finite strongly connected communication graph (and in particular on the complete network `⊤`)
   with at least one process recording a snapshot, every process eventually records its state and
   every incoming channel recorder eventually reaches `.done` (and remains complete thereafter).
   Every input-enabled system admits fair infinite executions from any well-formed state.

## Main definitions

* `Cslib.Distributed.ChandyLamport.preInFlight`, `Cslib.Distributed.ChandyLamport.postInFlight`:
  in-flight pre-snapshot and post-snapshot application message queues on channel `(u, v)`.
* `Cslib.Distributed.ChandyLamport.System.tracePreEvents`,
  `Cslib.Distributed.ChandyLamport.System.tracePostEvents`: exact subsequences of pre-snapshot and
  post-snapshot application events along an augmented trace.
* `Cslib.Distributed.ChandyLamport.SnapEvent.deliversOn`,
  `Cslib.Distributed.ChandyLamport.FairChannels`: weak FIFO channel delivery fairness on infinite
  executions.
* `Cslib.Distributed.ChandyLamport.StronglyConnected`: strong connectivity of a `Digraph P`.
* `Cslib.Distributed.ChandyLamport.System.InputEnabled`: non-blocking receive assumption ensuring
  fair executions exist.

## Main results

* `Cslib.Distributed.ChandyLamport.project_chan_eq_preInFlight_append_postInFlight`: exact FIFO
  partition of every channel into `preInFlight ++ postInFlight`.
* `Cslib.Distributed.ChandyLamport.System.preRecv_pops_preInFlight`: zero post-snapshot sends are
  ever received pre-snapshot.
* `Cslib.Distributed.ChandyLamport.System.postRecv_records_iff_preInFlight`: `chanRec` records the
  exact pre-snapshot messages received post-snapshot.
* `Cslib.Distributed.ChandyLamport.System.chandyLamport_perm_mTr`: explicit causal permutation of
  `eraseTrace xl` into `tracePreEvents ++ tracePostEvents` passing through
  `extractSnapshot S_final`.
* `Cslib.Distributed.ChandyLamport.System.chandyLamport_consistent_cut`: `extractSnapshot S_final`
  is reachable from `project S_init` and can reach `project S_final` in `sys.lts`.
* `Cslib.Distributed.ChandyLamport.System.stablePred_transfer`: forward/backward transfer of any
  stable global predicate `Φ` via `extractSnapshot S_final`.
* `Cslib.Distributed.ChandyLamport.System.snapshot_liveness`,
  `Cslib.Distributed.ChandyLamport.System.snapshot_liveness_complete`: eventual snapshot completion
  under fair FIFO channel delivery on strongly connected (and complete) networks.
* `Cslib.Distributed.ChandyLamport.System.InputEnabled.exists_fair_snapOmegaExecution`: every
  well-formed state of an input-enabled system extends to a fair infinite execution.

## References

* [K. M. Chandy, L. Lamport, *Distributed Snapshots: Determining Global States of Distributed
  Systems*][ChandyLamport1985]
-/

public section

namespace Cslib.Distributed.ChandyLamport

open Cslib Cslib.ωSequence

/-! ### Part 1: FIFO channel cut partition (`preInFlight` and `postInFlight`) -/

private lemma any_isMarker_eq_true_iff {M : Type*} {ws : List (WireMsg M)} :
    ws.any WireMsg.isMarker = true ↔ .marker ∈ ws := by
  simp [List.any_eq_true]

private lemma any_isMarker_eq_false_iff {M : Type*} {ws : List (WireMsg M)} :
    ws.any WireMsg.isMarker = false ↔ .marker ∉ ws := by
  rw [Bool.eq_false_iff, Ne, any_isMarker_eq_true_iff]

/-- In-flight application messages on channel `(u, v)` sent *before* `u` recorded its snapshot. -/
@[expose] def preInFlight {P S M : Type*} (S_aug : SnapGlobalState P S M) (u v : P) : List M :=
  if (S_aug.chan u v).any WireMsg.isMarker then
    takeBeforeMarker (S_aug.chan u v)
  else if (S_aug.proc u).snapState.isNone then
    unmarker (S_aug.chan u v)
  else
    []

/-- In-flight application messages on channel `(u, v)` sent *after* `u` recorded its snapshot. -/
@[expose] def postInFlight {P S M : Type*} (S_aug : SnapGlobalState P S M) (u v : P) : List M :=
  if (S_aug.chan u v).any WireMsg.isMarker then
    dropAfterMarker (S_aug.chan u v)
  else if (S_aug.proc u).snapState.isNone then
    []
  else
    unmarker (S_aug.chan u v)

private lemma preInFlight_congr {P S M : Type*} {S₁ S₂ : SnapGlobalState P S M} {u v : P}
    (hproc : (S₁.proc u).snapState = (S₂.proc u).snapState)
    (hchan : S₁.chan u v = S₂.chan u v) :
    preInFlight S₁ u v = preInFlight S₂ u v := by
  simp only [preInFlight, hproc, hchan]

private lemma postInFlight_congr {P S M : Type*} {S₁ S₂ : SnapGlobalState P S M} {u v : P}
    (hproc : (S₁.proc u).snapState = (S₂.proc u).snapState)
    (hchan : S₁.chan u v = S₂.chan u v) :
    postInFlight S₁ u v = postInFlight S₂ u v := by
  simp only [postInFlight, hproc, hchan]

/-- Every channel's underlying queue `(project S_aug).chan u v` decomposes into `preInFlight`
followed by `postInFlight`. -/
theorem project_chan_eq_preInFlight_append_postInFlight {P S M : Type*}
    (S_aug : SnapGlobalState P S M) (u v : P) :
    (project S_aug).chan u v = preInFlight S_aug u v ++ postInFlight S_aug u v := by
  simp only [project, preInFlight, postInFlight]
  cases hmk : (S_aug.chan u v).any WireMsg.isMarker
  · cases (S_aug.proc u).snapState.isNone <;> simp
  · simp only [↓reduceIte]
    exact unmarker_eq_takeBeforeMarker_append_dropAfterMarker (S_aug.chan u v)

private theorem preInFlight_eq_unmarker_of_unrecorded {P S M : Type*}
    {S_aug : SnapGlobalState P S M} {u v : P}
    (hunrec : (S_aug.proc u).snapState = none) (hnotm : .marker ∉ S_aug.chan u v) :
    preInFlight S_aug u v = unmarker (S_aug.chan u v) := by
  simp [preInFlight, any_isMarker_eq_false_iff.mpr hnotm, hunrec]

private theorem preInFlight_eq_nil_of_recorded_of_notMem {P S M : Type*}
    {S_aug : SnapGlobalState P S M} {u v : P}
    (hrec : (S_aug.proc u).snapState.isSome = true) (hnotm : .marker ∉ S_aug.chan u v) :
    preInFlight S_aug u v = [] := by
  cases h : (S_aug.proc u).snapState <;>
    simp_all [preInFlight, any_isMarker_eq_false_iff.mpr hnotm]

private theorem postInFlight_eq_nil_of_unrecorded {P S M : Type*}
    {S_aug : SnapGlobalState P S M} {u v : P}
    (hunrec : (S_aug.proc u).snapState = none) (hnotm : .marker ∉ S_aug.chan u v) :
    postInFlight S_aug u v = [] := by
  simp [postInFlight, any_isMarker_eq_false_iff.mpr hnotm, hunrec]

private lemma preInFlight_of_recorded {P S M : Type*}
    {S_aug : SnapGlobalState P S M} {u v : P}
    (hrec : (S_aug.proc u).snapState.isSome = true) :
    preInFlight S_aug u v =
      if (S_aug.chan u v).any WireMsg.isMarker then takeBeforeMarker (S_aug.chan u v) else [] := by
  cases h : (S_aug.proc u).snapState <;> simp_all [preInFlight]

private lemma postInFlight_of_recorded {P S M : Type*}
    {S_aug : SnapGlobalState P S M} {u v : P}
    (hrec : (S_aug.proc u).snapState.isSome = true) :
    postInFlight S_aug u v =
      if (S_aug.chan u v).any WireMsg.isMarker then dropAfterMarker (S_aug.chan u v)
      else unmarker (S_aug.chan u v) := by
  cases h : (S_aug.proc u).snapState <;> simp_all [postInFlight]

/-! ### Private ghost cut structures for the permutation proof -/

@[ext]
private structure CutState (P S M : Type*) where
  s : GlobalState P S M
  snapProc : P → Option S
  preChan : P → P → List M
  postChan : P → P → List M
  recBuf : P → P → List M

private def CutState.Valid {P S M : Type*} (C : CutState P S M) : Prop :=
  (∀ u v, C.s.chan u v = C.preChan u v ++ C.postChan u v) ∧
  (∀ u v, C.snapProc u = none → C.postChan u v = [])

private def ofSnap {P S M : Type*} (S_aug : SnapGlobalState P S M) : CutState P S M where
  s := project S_aug
  snapProc p := (S_aug.proc p).snapState
  preChan := preInFlight S_aug
  postChan := postInFlight S_aug
  recBuf u v := if (S_aug.proc v).snapState.isSome then ((S_aug.proc v).chanRec u).msgs else []

private inductive CutStep (P S M : Type*) where
  | pre (e : Event P S M)
  | cross (p : P)
  | post (e : Event P S M)

private def CutTr {P S M : Type*} [DecidableEq P] (sys : System P S M)
    (C₁ : CutState P S M) (st : CutStep P S M) (C₂ : CutState P S M) : Prop :=
  match st with
  | .pre e =>
    sys.lts.Tr C₁.s e C₂.s ∧
    C₁.snapProc e.actor = none ∧
    C₂.snapProc = C₁.snapProc ∧
    C₂.postChan = C₁.postChan ∧
    C₂.recBuf = C₁.recBuf ∧
    ∀ u v, (e.popsFrom u v → C₁.preChan u v ≠ []) ∧
      C₂.preChan u v =
        (if e.popsFrom u v then (C₁.preChan u v).tail else C₁.preChan u v) ++
          if u = e.actor then outgoingTo e.sent v else []
  | .cross p =>
    C₁.snapProc p = none ∧
    C₂.s = C₁.s ∧
    C₂.snapProc = (fun r => if r = p then some (C₁.s.proc p) else C₁.snapProc r) ∧
    C₂.preChan = C₁.preChan ∧
    C₂.postChan = C₁.postChan ∧
    C₂.recBuf = C₁.recBuf
  | .post e =>
    sys.lts.Tr C₁.s e C₂.s ∧
    (C₁.snapProc e.actor).isSome = true ∧
    C₂.snapProc = C₁.snapProc ∧
    (∀ u v, C₂.preChan u v =
      if e.popsFrom u v then (C₁.preChan u v).tail else C₁.preChan u v) ∧
    (∀ u v, C₂.postChan u v =
      (if e.popsFrom u v ∧ C₁.preChan u v = [] then (C₁.postChan u v).tail
       else C₁.postChan u v) ++
        if u = e.actor then outgoingTo e.sent v else []) ∧
    (∀ u v, C₂.recBuf u v =
      if e.popsFrom u v then
        match C₁.preChan u v with
        | [] => C₁.recBuf u v
        | msg :: _ => C₁.recBuf u v ++ [msg]
      else C₁.recBuf u v)

private inductive CutMTr {P S M : Type*} [DecidableEq P] (sys : System P S M) :
    CutState P S M → List (CutStep P S M) → CutState P S M → Prop where
  | refl {C} : CutMTr sys C [] C
  | stepL {C₁ st C₂ sts C₃} : CutTr sys C₁ st C₂ → CutMTr sys C₂ sts C₃ →
      CutMTr sys C₁ (st :: sts) C₃

namespace System

variable {P S M : Type*} (sys : System P S M)

/-- **Zero post-snapshot sends received pre-snapshot:** when an unrecorded process `dest`
(`snapState = none`) receives `msg` from `src`, `msg` comes from the head of
`preInFlight S₁ src dest` (which is non-empty). -/
theorem preRecv_pops_preInFlight [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {src dest : P} {msg : M} {st' : S} {sent : List (P × M)}
    (hinv : sys.SnapInv S₁)
    (htr : sys.snapLts.Tr S₁ (.app (.recv src dest msg st' sent)) S₂)
    (hpre_dest : (S₁.proc dest).snapState = none) :
    ∃ tail, preInFlight S₁ src dest = msg :: tail := by
  obtain ⟨⟨hadj, hhead, _, _⟩, _⟩ := htr
  obtain ⟨ws, hch⟩ := List.head?_eq_some_iff.mp hhead
  rw [preInFlight]
  cases hmk : (S₁.chan src dest).any WireMsg.isMarker
  · have hnotm : .marker ∉ S₁.chan src dest := any_isMarker_eq_false_iff.mp hmk
    cases hsrc : (S₁.proc src).snapState with
    | none =>
      exact ⟨unmarker ws, by simp [hch]⟩
    | some _ =>
      rcases hinv.recordedSrc src dest (by simp [hsrc]) hadj with ⟨hm, _⟩ | ⟨_, hv_some, _⟩
      · exact absurd hm hnotm
      · simp [hpre_dest] at hv_some
  · exact ⟨takeBeforeMarker ws, by simp [hch, takeBeforeMarker]⟩

/-- **`chanRec` captures the exact pre-snapshot sends received post-snapshot:** when an
already-recorded process `dest` (`snapState.isSome`) receives `msg` from `src`:
* if `preInFlight S₁ src dest` is non-empty, `msg` is its head and `chanRec src` appends `msg`;
* if `preInFlight S₁ src dest = []`, `msg` is the head of `postInFlight S₁ src dest` and
  `chanRec src` is already `.done` and unchanged. -/
theorem postRecv_records_iff_preInFlight [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {src dest : P} {msg : M} {st' : S} {sent : List (P × M)}
    (hinv : sys.SnapInv S₁)
    (htr : sys.snapLts.Tr S₁ (.app (.recv src dest msg st' sent)) S₂)
    (hpost_dest : (S₁.proc dest).snapState.isSome = true) :
    (preInFlight S₁ src dest ≠ [] ∧
      (preInFlight S₁ src dest).head? = some msg ∧
      ((S₂.proc dest).chanRec src).msgs = ((S₁.proc dest).chanRec src).msgs ++ [msg]) ∨
    (preInFlight S₁ src dest = [] ∧
      (postInFlight S₁ src dest).head? = some msg ∧
      ((S₂.proc dest).chanRec src).msgs = ((S₁.proc dest).chanRec src).msgs) := by
  obtain ⟨⟨hadj, hhead, _, _⟩, rfl⟩ := htr
  obtain ⟨ws, hch⟩ := List.head?_eq_some_iff.mp hhead
  cases hsrc : (S₁.proc src).snapState with
  | none =>
    obtain ⟨hnotm, hrec⟩ := hinv.unrecordedSrc src dest hsrc
    obtain ⟨buf, hbuf⟩ := hrec hpost_dest hadj
    have hpre_eq : preInFlight S₁ src dest = msg :: unmarker ws := by
      rw [preInFlight_eq_unmarker_of_unrecorded hsrc hnotm, hch, unmarker_cons_app]
    left
    refine ⟨by simp [hpre_eq], by simp [hpre_eq], ?_⟩
    simp [stepSnap, SnapGlobalState.applyApp, hpost_dest, hbuf, ChannelRec.recordApp,
      ChannelRec.msgs]
  | some _ =>
    have hsrc_some : (S₁.proc src).snapState.isSome = true := by simp [hsrc]
    rcases hinv.recordedSrc src dest hsrc_some hadj with ⟨hmem, hrec⟩ | ⟨hnotm, _, ⟨sv, hsv⟩⟩
    · obtain ⟨buf, hbuf⟩ := hrec hpost_dest
      have hpre_eq : preInFlight S₁ src dest = msg :: takeBeforeMarker ws := by
        rw [preInFlight_of_recorded hsrc_some, any_isMarker_eq_true_iff.mpr hmem, hch]
        rfl
      left
      refine ⟨by simp [hpre_eq], by simp [hpre_eq], ?_⟩
      simp [stepSnap, SnapGlobalState.applyApp, hpost_dest, hbuf, ChannelRec.recordApp,
        ChannelRec.msgs]
    · have hpost_eq : postInFlight S₁ src dest = msg :: unmarker ws := by
        rw [postInFlight_of_recorded hsrc_some, any_isMarker_eq_false_iff.mpr hnotm]
        simp [hch]
      right
      refine ⟨preInFlight_eq_nil_of_recorded_of_notMem hsrc_some hnotm, by simp [hpost_eq], ?_⟩
      simp [stepSnap, SnapGlobalState.applyApp, hpost_dest, hsv, ChannelRec.recordApp,
        ChannelRec.msgs]

/-! ### Part 2: Ghost cut executions & causal permutation (`chandyLamport_consistent_cut`) -/

/-- Subsequence of `Pre`-snapshot application events along augmented trace `xl` from `S_aug`
(events whose actor had `snapState = none` when the event fired). -/
@[expose] def tracePreEvents [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) : List (SnapEvent P S M) → List (Event P S M)
  | [] => []
  | a :: xl =>
    let rest := tracePreEvents (sys.stepSnap S_aug a) xl
    match a with
    | .app e => if (S_aug.proc e.actor).snapState.isNone then e :: rest else rest
    | _ => rest

/-- Subsequence of `Post`-snapshot application events along augmented trace `xl` from `S_aug`
(events whose actor had `snapState.isSome` when the event fired). -/
@[expose] def tracePostEvents [DecidableEq P] [DecidableRel sys.graph.Adj]
    (S_aug : SnapGlobalState P S M) : List (SnapEvent P S M) → List (Event P S M)
  | [] => []
  | a :: xl =>
    let rest := tracePostEvents (sys.stepSnap S_aug a) xl
    match a with
    | .app e => if (S_aug.proc e.actor).snapState.isSome then e :: rest else rest
    | _ => rest

private lemma valid_ofSnap {S_aug : SnapGlobalState P S M} (hinv : sys.SnapInv S_aug) :
    (ofSnap S_aug).Valid :=
  ⟨project_chan_eq_preInFlight_append_postInFlight S_aug,
   fun u v hun => postInFlight_eq_nil_of_unrecorded hun (hinv.unrecordedSrc u v hun).1⟩

private lemma cutTr_preserves_valid [DecidableEq P] {C₁ C₂ : CutState P S M}
    {st : CutStep P S M} (hv : C₁.Valid) (htr : CutTr sys C₁ st C₂) : C₂.Valid := by
  rcases hv with ⟨hchan₁, hunrec₁⟩
  cases st with
  | pre e =>
    rcases htr with ⟨⟨_, hstep⟩, hact_none, hsnap, hpost, _, hpre⟩
    refine ⟨fun u v => ?_, fun u v hu => hpost ▸ hunrec₁ u v (hsnap ▸ hu)⟩
    rw [hstep, GlobalState.applyEvent_chan, hchan₁ u v, (hpre u v).2, hpost]
    by_cases hp : e.popsFrom u v <;> rcases eq_or_ne u e.actor with rfl | hu <;>
      simp [List.tail_append_of_ne_nil, fun u => (hpre u v).1, hunrec₁ _ v hact_none, *]
  | cross p =>
    rcases htr with ⟨_, hC₂s, hsnap, hpre, hpost, _⟩
    refine ⟨fun u v => by rw [hC₂s, hpre, hpost, hchan₁], fun u v hu => ?_⟩
    rw [hpost]
    rcases eq_or_ne u p with rfl | hup <;> simp_all
  | post e =>
    rcases htr with ⟨⟨_, hstep⟩, hact_some, hsnap, hpre, hpost, _⟩
    refine ⟨fun u v => ?_, fun u v hu => ?_⟩
    · rw [hstep, GlobalState.applyEvent_chan, hchan₁ u v, hpre u v, hpost u v]
      cases C₁.preChan u v <;> by_cases hp : e.popsFrom u v <;> simp [hp, List.append_assoc]
    · rw [hsnap] at hu
      have hue : u ≠ e.actor := by rintro rfl; simp [hu] at hact_some
      simp [hpost u v, hunrec₁ u v hu, hue]

/-! #### Mapping `sys.snapLts` transitions into `CutMTr` -/

private lemma pre_post_emit_marker [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {u v : P}
    (hinv : sys.SnapInv S₁)
    (hunrec : (S₁.proc u).snapState = none)
    (hrec₂ : (S₂.proc u).snapState.isSome = true)
    (hch : S₂.chan u v = if sys.graph.Adj u v then S₁.chan u v ++ [.marker] else S₁.chan u v) :
    preInFlight S₂ u v = preInFlight S₁ u v ∧
    postInFlight S₂ u v = postInFlight S₁ u v := by
  have hnotm := (hinv.unrecordedSrc u v hunrec).1
  rw [preInFlight_eq_unmarker_of_unrecorded hunrec hnotm, preInFlight_of_recorded hrec₂,
    postInFlight_eq_nil_of_unrecorded hunrec hnotm, postInFlight_of_recorded hrec₂]
  by_cases hadj : sys.graph.Adj u v
  · have hch₂ : S₂.chan u v = S₁.chan u v ++ [.marker] := by simpa [hadj] using hch
    have hany₂ : (S₂.chan u v).any WireMsg.isMarker = true := by
      rw [hch₂]; exact any_isMarker_eq_true_iff.mpr (by simp)
    rw [hany₂, hch₂]
    exact ⟨by simp [takeBeforeMarker_append_marker_of_notMem hnotm],
      by simp [dropAfterMarker_append_marker_of_notMem hnotm]⟩
  · have hch₁ := (hinv.nonEdge u v hadj).1
    have hch₂ : S₂.chan u v = [] := by simpa [hadj, hch₁] using hch
    simp [hch₁, hch₂]

private lemma pre_post_pop_marker {P S M : Type*}
    {S₁ S₂ : SnapGlobalState P S M} {u v : P} {t_sd : List (WireMsg M)}
    (hu₁ : (S₁.proc u).snapState.isSome = true)
    (hu₂ : (S₂.proc u).snapState.isSome = true)
    (ht_sd : S₁.chan u v = .marker :: t_sd)
    (hch₂ : S₂.chan u v = t_sd)
    (hnotm_tail : .marker ∉ t_sd) :
    preInFlight S₂ u v = preInFlight S₁ u v ∧
    postInFlight S₂ u v = postInFlight S₁ u v := by
  exact ⟨by simp [preInFlight_eq_nil_of_recorded_of_notMem hu₂ (hch₂ ▸ hnotm_tail),
      preInFlight_of_recorded hu₁, ht_sd, takeBeforeMarker],
    by simp [postInFlight_of_recorded hu₂, postInFlight_of_recorded hu₁, hch₂, ht_sd,
      any_isMarker_eq_false_iff.mpr hnotm_tail, dropAfterMarker]⟩

private lemma pre_post_congr {P S M : Type*} {S₁ S₂ : SnapGlobalState P S M} {u v : P}
    (hproc : (S₂.proc u).snapState = (S₁.proc u).snapState)
    (hchan : S₂.chan u v = S₁.chan u v) :
    preInFlight S₂ u v = preInFlight S₁ u v ∧ postInFlight S₂ u v = postInFlight S₁ u v :=
  ⟨preInFlight_congr hproc hchan, postInFlight_congr hproc hchan⟩

private lemma ofSnap_step_initiate [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ : SnapGlobalState P S M} {p : P} (hinv : sys.SnapInv S₁)
    (hen : sys.EnabledSnap S₁ (.initiateSnapshot p)) :
    CutTr sys (ofSnap S₁) (.cross p) (ofSnap (sys.stepSnap S₁ (.initiateSnapshot p))) := by
  have hen' : (S₁.proc p).snapState = none := hen
  let S₂ := sys.stepSnap S₁ (.initiateSnapshot p)
  have hproj := sys.snapTr_project (S₁ := S₁) (a := .initiateSnapshot p) ⟨hen, rfl⟩
  simp only [SnapEvent.toAppEvent] at hproj
  have hboth : ∀ u v, preInFlight S₂ u v = preInFlight S₁ u v ∧
      postInFlight S₂ u v = postInFlight S₁ u v := by
    intro u v
    rcases eq_or_ne u p with rfl | hu
    · exact sys.pre_post_emit_marker hinv hen' (by simp [S₂, stepSnap, applyInitiate])
        (by simp [S₂, stepSnap, applyInitiate])
    · exact pre_post_congr (by simp [S₂, stepSnap, applyInitiate, hu])
        (by simp [S₂, stepSnap, applyInitiate, hu])
  refine ⟨hen', hproj, ?_, funext fun u => funext fun v => (hboth u v).1,
    funext fun u => funext fun v => (hboth u v).2, ?_⟩
  · funext r
    simp only [ofSnap, stepSnap, applyInitiate]
    rcases eq_or_ne r p with rfl | hr <;> simp_all [project]
  · funext u v
    simp only [ofSnap, stepSnap, applyInitiate]
    rcases eq_or_ne v p with rfl | hv
    · rw [hen']
      by_cases hadj : sys.graph.Adj u v <;> simp [hadj, ChannelRec.msgs]
    · simp [hv]

private lemma ofSnap_step_recvMarker_none [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ : SnapGlobalState P S M} {src dest : P} (hinv : sys.SnapInv S₁)
    (hen : sys.EnabledSnap S₁ (.recvMarker src dest))
    (hdest : (S₁.proc dest).snapState = none) :
    CutTr sys (ofSnap S₁) (.cross dest)
      (ofSnap (sys.stepSnap S₁ (.recvMarker src dest))) := by
  obtain ⟨_, hsrc_some, t_sd, ht_sd, hnotm_tail⟩ := sys.enabledSnap_recvMarker_spec hinv hen
  have hsrc_ne_dest : src ≠ dest := by
    intro h; subst h; rw [hdest] at hsrc_some; simp at hsrc_some
  let S₂ := sys.stepSnap S₁ (.recvMarker src dest)
  have hproj := sys.snapTr_project (S₁ := S₁) (a := .recvMarker src dest) ⟨hen, rfl⟩
  simp only [SnapEvent.toAppEvent] at hproj
  have hboth : ∀ u v, preInFlight S₂ u v = preInFlight S₁ u v ∧
      postInFlight S₂ u v = postInFlight S₁ u v := by
    intro u v
    rcases eq_or_ne u dest with rfl | hud
    · have hnp : ¬ (u = src ∧ v = u) := fun hp => hsrc_ne_dest hp.1.symm
      exact sys.pre_post_emit_marker hinv hdest
        (by simp [S₂, stepSnap, applyRecvMarker, hdest])
        (by simp [S₂, stepSnap, applyRecvMarker, hdest, hnp])
    · by_cases hsd : u = src ∧ v = dest
      · rcases hsd with ⟨rfl, rfl⟩
        exact pre_post_pop_marker hsrc_some
          (by simpa [S₂, stepSnap, applyRecvMarker, hdest, hud] using hsrc_some)
          ht_sd (by simp [S₂, stepSnap, applyRecvMarker, hdest, hud, ht_sd]) hnotm_tail
      · exact pre_post_congr (by simp [S₂, stepSnap, applyRecvMarker, hdest, hud])
          (by simp [S₂, stepSnap, applyRecvMarker, hdest, hud, hsd])
  refine ⟨hdest, hproj, ?_, funext fun u => funext fun v => (hboth u v).1,
    funext fun u => funext fun v => (hboth u v).2, ?_⟩
  · funext r
    simp only [ofSnap, stepSnap, applyRecvMarker, hdest]
    rcases eq_or_ne r dest with rfl | hr <;> simp_all [project]
  · funext u v
    simp only [ofSnap, stepSnap, applyRecvMarker, hdest]
    rcases eq_or_ne v dest with rfl | hv
    · rw [hdest]
      by_cases h : u = src ∨ ¬ sys.graph.Adj u v <;> simp [h, ChannelRec.msgs]
    · simp [hv]

private lemma ofSnap_step_recvMarker_some [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ : SnapGlobalState P S M} {src dest : P} {s_d : S} (hinv : sys.SnapInv S₁)
    (hen : sys.EnabledSnap S₁ (.recvMarker src dest))
    (hdest : (S₁.proc dest).snapState = some s_d) :
    ofSnap (sys.stepSnap S₁ (.recvMarker src dest)) = ofSnap S₁ := by
  obtain ⟨_, hsrc_some, t_sd, ht_sd, hnotm_tail⟩ := sys.enabledSnap_recvMarker_spec hinv hen
  let S₂ := sys.stepSnap S₁ (.recvMarker src dest)
  have hsnap_unch : ∀ x, (S₂.proc x).snapState = (S₁.proc x).snapState := fun x => by
    by_cases hx : x = dest <;> simp_all [S₂, stepSnap, applyRecvMarker]
  have hproj := sys.snapTr_project (S₁ := S₁) (a := .recvMarker src dest) ⟨hen, rfl⟩
  simp only [SnapEvent.toAppEvent] at hproj
  have hboth : ∀ u v, preInFlight S₂ u v = preInFlight S₁ u v ∧
      postInFlight S₂ u v = postInFlight S₁ u v := by
    intro u v
    by_cases hsd : u = src ∧ v = dest
    · rcases hsd with ⟨rfl, rfl⟩
      exact pre_post_pop_marker hsrc_some (by rw [hsnap_unch]; exact hsrc_some)
        ht_sd (by simp [S₂, stepSnap, applyRecvMarker, hdest, ht_sd]) hnotm_tail
    · exact pre_post_congr (hsnap_unch u)
        (by simp [S₂, stepSnap, applyRecvMarker, hdest, hsd])
  apply CutState.ext hproj (funext hsnap_unch)
    (funext fun u => funext fun v => (hboth u v).1)
    (funext fun u => funext fun v => (hboth u v).2)
  funext u v
  simp only [ofSnap, stepSnap, applyRecvMarker, hdest]
  rcases eq_or_ne v dest with rfl | hv
  · rcases eq_or_ne u src with rfl | husrc <;> simp_all [ChannelRec.msgs]
  · simp [hv]

/-! #### Channel evolution helpers for `.app e` transitions -/

private lemma preInFlight_pop_app {P S M : Type*} {S₁ S₂ : SnapGlobalState P S M}
    {u v : P} {msg : M} {ws : List (WireMsg M)}
    (hproc : (S₂.proc u).snapState = (S₁.proc u).snapState)
    (hch₁ : S₁.chan u v = .app msg :: ws) (hch₂ : S₂.chan u v = ws) :
    preInFlight S₂ u v = (preInFlight S₁ u v).tail := by
  simp only [preInFlight, hproc, hch₁, hch₂, List.any_cons, WireMsg.isMarker, Bool.false_or]
  cases ws.any WireMsg.isMarker
  · cases (S₁.proc u).snapState.isNone <;> simp
  · simp [takeBeforeMarker]

private lemma postInFlight_pop_app {P S M : Type*} {S₁ S₂ : SnapGlobalState P S M}
    {u v : P} {msg : M} {ws : List (WireMsg M)}
    (hproc : (S₂.proc u).snapState = (S₁.proc u).snapState)
    (hch₁ : S₁.chan u v = .app msg :: ws) (hch₂ : S₂.chan u v = ws) :
    postInFlight S₂ u v =
      if preInFlight S₁ u v = [] then (postInFlight S₁ u v).tail else postInFlight S₁ u v := by
  simp only [preInFlight, postInFlight, hproc, hch₁, hch₂, List.any_cons, WireMsg.isMarker,
    Bool.false_or]
  cases ws.any WireMsg.isMarker
  · cases (S₁.proc u).snapState.isNone <;> simp
  · simp [takeBeforeMarker, dropAfterMarker]

private lemma applyApp_snapState {P S M : Type*} [DecidableEq P]
    (S₁ : SnapGlobalState P S M) (e : Event P S M) (r : P) :
    ((S₁.applyApp e).proc r).snapState = (S₁.proc r).snapState := by
  cases e with
  | internal p _ _ | recv _ p _ _ _ =>
    by_cases hr : r = p <;> simp only [SnapGlobalState.applyApp, hr, ↓reduceIte]

private lemma applyApp_chan {P S M : Type*} [DecidableEq P]
    (S₁ : SnapGlobalState P S M) (e : Event P S M) (u v : P) :
    (S₁.applyApp e).chan u v =
      (if e.popsFrom u v then (S₁.chan u v).tail else S₁.chan u v) ++
        if u = e.actor then (outgoingTo e.sent v).map WireMsg.app else [] := by
  cases e with
  | internal p _ sent =>
    simp only [SnapGlobalState.applyApp, Event.popsFrom, ↓reduceIte, Event.actor, Event.sent]
    by_cases hu : u = p <;> simp [hu]
  | recv src dest _ _ sent =>
    simp only [SnapGlobalState.applyApp, Event.popsFrom, Event.actor, Event.sent]
    by_cases hp : u = src ∧ v = dest <;> simp only [hp, ↓reduceIte] <;>
      by_cases hu : u = dest <;> simp_all

private lemma applyApp_proj_snap [DecidableEq P]
    {S₁ : SnapGlobalState P S M} {e : Event P S M} (hen : sys.EnabledSnap S₁ (.app e)) :
    sys.lts.Tr (project S₁) e (project (S₁.applyApp e)) ∧
    (ofSnap (S₁.applyApp e)).snapProc = (ofSnap S₁).snapProc := by
  classical
  have htr_proj := sys.snapTr_project (S₁ := S₁) (a := .app e) ⟨hen, rfl⟩
  simp only [SnapEvent.toAppEvent] at htr_proj
  exact ⟨htr_proj, funext fun r => applyApp_snapState S₁ e r⟩

private lemma ofSnap_step_app_pre [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ : SnapGlobalState P S M} {e : Event P S M} (hinv : sys.SnapInv S₁)
    (hen : sys.EnabledSnap S₁ (.app e))
    (hact : (S₁.proc e.actor).snapState = none) :
    CutTr sys (ofSnap S₁) (.pre e) (ofSnap (sys.stepSnap S₁ (.app e))) := by
  obtain ⟨htr_proj, hsnap_eq⟩ := sys.applyApp_proj_snap hen
  change CutTr sys (ofSnap S₁) (.pre e) (ofSnap (S₁.applyApp e))
  have hrec_eq : (ofSnap (S₁.applyApp e)).recBuf = (ofSnap S₁).recBuf := by
    funext u v; simp only [ofSnap, applyApp_snapState]
    cases e with
    | internal p _ _ => by_cases hv : v = p <;> simp [SnapGlobalState.applyApp, hv]
    | recv _ dest _ _ _ =>
      simp only [Event.actor] at hact
      by_cases hv : v = dest <;> simp [SnapGlobalState.applyApp, hv, hact]
  have hpop_info : ∀ u v, e.popsFrom u v →
      ∃ msg ws, S₁.chan u v = .app msg :: ws ∧
        ∃ t_pre, preInFlight S₁ u v = msg :: t_pre := by
    intro u v hp
    cases e with
    | internal _ _ _ => exact False.elim hp
    | recv src dest msg st' sent =>
      rcases hp with ⟨rfl, rfl⟩
      obtain ⟨ws, hws⟩ := List.head?_eq_some_iff.mp hen.2.1
      exact ⟨msg, ws, hws, sys.preRecv_pops_preInFlight hinv ⟨hen, rfl⟩ hact⟩
  have hboth : ∀ u v,
      postInFlight (S₁.applyApp e) u v = postInFlight S₁ u v ∧
      preInFlight (S₁.applyApp e) u v =
        (if e.popsFrom u v then (preInFlight S₁ u v).tail else preInFlight S₁ u v) ++
          if u = e.actor then outgoingTo e.sent v else [] := by
    intro u v
    have hu_snap := applyApp_snapState S₁ e u
    have hch₂ := applyApp_chan S₁ e u v
    by_cases hu : u = e.actor
    · subst hu
      have hch_act : (S₁.applyApp e).chan e.actor v =
          (if e.popsFrom e.actor v then (S₁.chan e.actor v).tail else S₁.chan e.actor v) ++
            (outgoingTo e.sent v).map WireMsg.app := by simpa using hch₂
      have hnotm₁ := (hinv.unrecordedSrc _ v hact).1
      have hnotm₂ : .marker ∉ (S₁.applyApp e).chan e.actor v := by
        rw [hch_act]
        split_ifs <;> simp [marker_notMem_map_app, hnotm₁, mt List.mem_of_mem_tail hnotm₁]
      rw [postInFlight_eq_nil_of_unrecorded (hu_snap.trans hact) hnotm₂,
        postInFlight_eq_nil_of_unrecorded hact hnotm₁,
        preInFlight_eq_unmarker_of_unrecorded (hu_snap.trans hact) hnotm₂,
        preInFlight_eq_unmarker_of_unrecorded hact hnotm₁, hch_act]
      by_cases hp : e.popsFrom e.actor v
      · obtain ⟨msg, ws, hws, _⟩ := hpop_info _ v hp
        simp [hp, hws]
      · simp [hp]
    · simp only [hu, ↓reduceIte, List.append_nil]
      by_cases hp : e.popsFrom u v
      · obtain ⟨msg, ws, hws, t_pre, ht_pre⟩ := hpop_info u v hp
        have hch₂' : (S₁.applyApp e).chan u v = ws := by simp [hch₂, hp, hu, hws]
        simp only [hp, ↓reduceIte]
        exact ⟨by rw [postInFlight_pop_app hu_snap hws hch₂']; simp [ht_pre],
          preInFlight_pop_app hu_snap hws hch₂'⟩
      · simp only [hp, ↓reduceIte]
        exact ⟨postInFlight_congr hu_snap (by simp [hch₂, hp, hu]),
          preInFlight_congr hu_snap (by simp [hch₂, hp, hu])⟩
  refine ⟨htr_proj, hact, hsnap_eq, funext fun u => funext fun v => (hboth u v).1, hrec_eq, ?_⟩
  intro u v
  refine ⟨fun hp => ?_, (hboth u v).2⟩
  obtain ⟨_, _, _, _, ht_pre⟩ := hpop_info u v hp
  simp [ofSnap, ht_pre]

private lemma ofSnap_step_app_post [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ : SnapGlobalState P S M} {e : Event P S M} (hinv : sys.SnapInv S₁)
    (hen : sys.EnabledSnap S₁ (.app e))
    (hact : (S₁.proc e.actor).snapState.isSome = true) :
    CutTr sys (ofSnap S₁) (.post e) (ofSnap (sys.stepSnap S₁ (.app e))) := by
  obtain ⟨htr_proj, hsnap_eq⟩ := sys.applyApp_proj_snap hen
  change CutTr sys (ofSnap S₁) (.post e) (ofSnap (S₁.applyApp e))
  have hpop_ws : ∀ u v, e.popsFrom u v → ∃ msg ws, S₁.chan u v = .app msg :: ws := by
    intro u v hp
    cases e with
    | internal _ _ _ => exact False.elim hp
    | recv src dest msg _ _ =>
      rcases hp with ⟨rfl, rfl⟩
      obtain ⟨ws, hws⟩ := List.head?_eq_some_iff.mp hen.2.1
      exact ⟨msg, ws, hws⟩
  have hboth : ∀ u v,
      preInFlight (S₁.applyApp e) u v =
        (if e.popsFrom u v then (preInFlight S₁ u v).tail else preInFlight S₁ u v) ∧
      postInFlight (S₁.applyApp e) u v =
        (if e.popsFrom u v ∧ preInFlight S₁ u v = [] then (postInFlight S₁ u v).tail
         else postInFlight S₁ u v) ++
          if u = e.actor then outgoingTo e.sent v else [] := by
    intro u v
    have hu_snap := applyApp_snapState S₁ e u
    have hch₂ := applyApp_chan S₁ e u v
    let base := if e.popsFrom u v then (S₁.chan u v).tail else S₁.chan u v
    have hany_base : base.any WireMsg.isMarker = (S₁.chan u v).any WireMsg.isMarker := by
      by_cases hp : e.popsFrom u v
      · obtain ⟨msg, ws, hws⟩ := hpop_ws u v hp
        simp [base, hp, hws, WireMsg.isMarker]
      · simp [base, hp]
    by_cases hu : u = e.actor
    · have hact_u : (S₁.proc u).snapState.isSome = true := hu ▸ hact
      have hu_some₂ : ((S₁.applyApp e).proc u).snapState.isSome = true := hu_snap ▸ hact_u
      have hch_eq : (S₁.applyApp e).chan u v = base ++ (outgoingTo e.sent v).map WireMsg.app := by
        rw [hch₂, ite_eq_left hu]
      have hany₂ : ((S₁.applyApp e).chan u v).any WireMsg.isMarker = base.any WireMsg.isMarker := by
        rw [hch_eq, Bool.eq_iff_iff, any_isMarker_eq_true_iff, any_isMarker_eq_true_iff]
        simp [marker_notMem_map_app]
      simp only [preInFlight_of_recorded hu_some₂, preInFlight_of_recorded hact_u,
        postInFlight_of_recorded hu_some₂, postInFlight_of_recorded hact_u,
        hany₂, hany_base, ite_eq_left hu]
      cases hmk : (S₁.chan u v).any WireMsg.isMarker
      · simp only [Bool.false_eq_true, ↓reduceIte, and_true, hch_eq, unmarker_append,
          unmarker_map_app]
        refine ⟨by simp, ?_⟩
        by_cases hp : e.popsFrom u v
        · obtain ⟨msg, ws, hws⟩ := hpop_ws u v hp
          simp [base, hp, hws]
        · simp [base, hp]
      · have hmem_base : .marker ∈ base :=
          any_isMarker_eq_true_iff.mp (hany_base.trans hmk)
        simp only [↓reduceIte, hch_eq, takeBeforeMarker_append_app_of_mem hmem_base,
          dropAfterMarker_append_app_of_mem hmem_base]
        by_cases hp : e.popsFrom u v
        · obtain ⟨msg, ws, hws⟩ := hpop_ws u v hp
          simp [base, hp, hws, takeBeforeMarker, dropAfterMarker]
        · simp [base, hp]
    · simp only [hu, ↓reduceIte, List.append_nil]
      by_cases hp : e.popsFrom u v
      · obtain ⟨msg, ws, hws⟩ := hpop_ws u v hp
        have hch_eq : (S₁.applyApp e).chan u v = ws := by simp [hch₂, hu, hp, hws]
        simp only [hp, ↓reduceIte, true_and]
        exact ⟨preInFlight_pop_app hu_snap hws hch_eq, postInFlight_pop_app hu_snap hws hch_eq⟩
      · simp only [hp, ↓reduceIte, false_and]
        exact ⟨preInFlight_congr hu_snap (by simp [hch₂, hu, hp]),
          postInFlight_congr hu_snap (by simp [hch₂, hu, hp])⟩
  refine ⟨htr_proj, hact, hsnap_eq, fun u v => (hboth u v).1, fun u v => (hboth u v).2, ?_⟩
  · -- `recBuf` update
    intro u v
    cases e with
    | internal p st' sent =>
      by_cases hv : v = p <;> simp [ofSnap, Event.popsFrom, SnapGlobalState.applyApp, hv]
    | recv src dest msg st' sent =>
      simp only [Event.actor] at hact
      have hpost_rec := sys.postRecv_records_iff_preInFlight hinv ⟨hen, rfl⟩ hact
      simp only [ofSnap, Event.popsFrom]
      by_cases hsd : u = src ∧ v = dest
      · rcases hsd with ⟨rfl, rfl⟩
        have hv_some :
            (((S₁.applyApp (.recv u v msg st' sent)).proc v).snapState).isSome = true := by
          simp [SnapGlobalState.applyApp, hact]
        simp only [and_self, ↓reduceIte, hv_some, hact]
        rcases hpost_rec with ⟨_, hhead_pre, hmsgs⟩ | ⟨heq_nil, _, hmsgs⟩
        · obtain ⟨t_p, ht_p⟩ := List.head?_eq_some_iff.mp hhead_pre
          dsimp only [stepSnap] at hmsgs
          simp [ht_p, hmsgs]
        · dsimp only [stepSnap] at hmsgs
          simp [heq_nil, hmsgs]
      · simp only [hsd, ↓reduceIte]
        rcases eq_or_ne v dest with rfl | hv
        · have hu : u ≠ src := fun h => hsd ⟨h, rfl⟩
          simp only [SnapGlobalState.applyApp, hact, hu, ↓reduceIte]
        · simp only [SnapGlobalState.applyApp, hv, ↓reduceIte]

/-! #### Adjacent inversion swaps in `CutMTr` -/

private lemma swap_cross_pre [DecidableEq P] {C₀ C₁ C₂ : CutState P S M}
    {p : P} {e : Event P S M}
    (htr₁ : CutTr sys C₀ (.cross p) C₁) (htr₂ : CutTr sys C₁ (.pre e) C₂) :
    ∃ C₁', CutTr sys C₀ (.pre e) C₁' ∧ CutTr sys C₁' (.cross p) C₂ := by
  rcases htr₁ with ⟨hp_none, hC₁s, hC₁snap, hC₁pre, hC₁post, hC₁rec⟩
  rcases htr₂ with ⟨htr_e, he_none, hC₂snap, hC₂post, hC₂rec, hC₂pre⟩
  rw [hC₁snap] at he_none
  have hep : e.actor ≠ p := by rintro h; simp [h] at he_none
  have hC₀_e_none : C₀.snapProc e.actor = none := by simpa [hep] using he_none
  have hproc_p : C₂.s.proc p = C₀.s.proc p := by
    simp [htr_e.2, hC₁s, GlobalState.applyEvent_proc, hep.symm]
  let C₁' : CutState P S M :=
    { s := C₂.s
      snapProc := C₀.snapProc
      preChan := C₂.preChan
      postChan := C₀.postChan
      recBuf := C₀.recBuf }
  refine ⟨C₁', ?_, ?_⟩
  · refine ⟨hC₁s ▸ htr_e, hC₀_e_none, rfl, rfl, rfl, ?_⟩
    simpa [C₁', hC₁pre] using hC₂pre
  · refine ⟨hp_none, rfl, ?_, rfl, hC₂post.trans hC₁post, hC₂rec.trans hC₁rec⟩
    rw [hC₂snap, hC₁snap]
    funext r
    by_cases hr : r = p <;> simp [C₁', hr, hproc_p]

private lemma swap_post_cross [DecidableEq P] {C₀ C₁ C₂ : CutState P S M}
    {e : Event P S M} {q : P}
    (htr₁ : CutTr sys C₀ (.post e) C₁) (htr₂ : CutTr sys C₁ (.cross q) C₂) :
    ∃ C₁', CutTr sys C₀ (.cross q) C₁' ∧ CutTr sys C₁' (.post e) C₂ := by
  rcases htr₁ with ⟨htr_e, he_some, hC₁snap, hC₁pre, hC₁post, hC₁rec⟩
  rcases htr₂ with ⟨hq_none, hC₂s, hC₂snap, hC₂pre, hC₂post, hC₂rec⟩
  have hC₀_q_none : C₀.snapProc q = none := hC₁snap ▸ hq_none
  have heq : e.actor ≠ q := by rintro rfl; simp [hC₀_q_none] at he_some
  have hproc_q : C₁.s.proc q = C₀.s.proc q := by
    simp [htr_e.2, GlobalState.applyEvent_proc, heq.symm]
  let C₁' : CutState P S M :=
    { s := C₀.s
      snapProc := C₂.snapProc
      preChan := C₀.preChan
      postChan := C₀.postChan
      recBuf := C₀.recBuf }
  refine ⟨C₁', ?_, ?_⟩
  · refine ⟨hC₀_q_none, rfl, ?_, rfl, rfl, rfl⟩
    rw [hC₂snap, hC₁snap]
    funext r
    by_cases hr : r = q <;> simp [hr, hproc_q]
  · refine ⟨hC₂s ▸ htr_e, ?_, rfl, hC₂pre ▸ hC₁pre, hC₂post ▸ hC₁post, hC₂rec ▸ hC₁rec⟩
    simp [C₁', hC₂snap, hC₁snap, heq, he_some]

private lemma swap_post_pre [DecidableEq P] {C₀ C₁ C₂ : CutState P S M}
    {e₁ e₂ : Event P S M} (hv₀ : C₀.Valid)
    (htr₁ : CutTr sys C₀ (.post e₁) C₁) (htr₂ : CutTr sys C₁ (.pre e₂) C₂) :
    ∃ C₁', CutTr sys C₀ (.pre e₂) C₁' ∧ CutTr sys C₁' (.post e₁) C₂ := by
  rcases htr₁ with ⟨htr_e₁, he₁_some, hC₁snap, hC₁pre, hC₁post, hC₁rec⟩
  rcases htr₂ with ⟨htr_e₂, he₂_none, hC₂snap, hC₂post, hC₂rec, hC₂pre⟩
  have hC₀_e₂_none : C₀.snapProc e₂.actor = none := hC₁snap ▸ he₂_none
  have hne : e₁.actor ≠ e₂.actor := by rintro h; simp [h, hC₀_e₂_none] at he₁_some
  have hnot_both_pop : ∀ u v, ¬ (e₁.popsFrom u v ∧ e₂.popsFrom u v) := fun u v ⟨hp₁, hp₂⟩ =>
    hne ((e₁.popsFrom_dest hp₁).symm.trans (e₂.popsFrom_dest hp₂))
  have hpre_pop₂ : ∀ u v, e₂.popsFrom u v → C₀.preChan u v ≠ [] := fun u v hp₂ => by
    have hp₁ : ¬ e₁.popsFrom u v := fun hp₁ => hnot_both_pop u v ⟨hp₁, hp₂⟩
    simpa [hC₁pre u v, hp₁] using (hC₂pre u v).1 hp₂
  have hs_pop₂ : e₂.popsFrom e₁.actor e₂.actor → C₀.s.chan e₁.actor e₂.actor ≠ [] := fun hp₂ => by
    rw [hv₀.1]; exact List.append_ne_nil_of_left_ne_nil (hpre_pop₂ _ _ hp₂) _
  obtain ⟨s₁', htr_e₂', htr_e₁'⟩ := sys.tr_comm_of_ne htr_e₁ htr_e₂ hne hs_pop₂
  have hpre_pop₁_from_q : ∀ v, e₁.popsFrom e₂.actor v → C₀.preChan e₂.actor v ≠ [] := by
    intro v hp₁
    have hs_ne : C₀.s.chan e₂.actor v ≠ [] := by
      cases e₁ with
      | internal _ _ _ => exact False.elim hp₁
      | recv src₁ dest₁ msg₁ _ _ =>
        rcases hp₁ with ⟨rfl, rfl⟩
        obtain ⟨_, ht⟩ := List.head?_eq_some_iff.mp htr_e₁.1.2.1
        simp [ht]
    simpa [hv₀.1, hv₀.2 e₂.actor v hC₀_e₂_none] using hs_ne
  let C₁' : CutState P S M :=
    { s := s₁'
      snapProc := C₀.snapProc
      preChan u v :=
        (if e₂.popsFrom u v then (C₀.preChan u v).tail else C₀.preChan u v) ++
          if u = e₂.actor then outgoingTo e₂.sent v else []
      postChan := C₀.postChan
      recBuf := C₀.recBuf }
  refine ⟨C₁', ?_, ?_⟩
  · exact ⟨htr_e₂', hC₀_e₂_none, rfl, rfl, rfl, fun u v => ⟨hpre_pop₂ u v, rfl⟩⟩
  · have hmatch : ∀ (xs ys buf : List M), xs.head? = ys.head? →
        (match xs with | [] => buf | msg :: _ => buf ++ [msg]) =
          (match ys with | [] => buf | msg :: _ => buf ++ [msg]) := by
      rintro (_ | _) (_ | _) _ h <;> simp_all
    have hpre_shape : ∀ u v, e₁.popsFrom u v →
        ¬ e₂.popsFrom u v ∧
        (C₁'.preChan u v).tail =
          (C₀.preChan u v).tail ++ (if u = e₂.actor then outgoingTo e₂.sent v else []) ∧
        (C₁'.preChan u v = [] ↔ C₀.preChan u v = []) ∧
        (C₁'.preChan u v).head? = (C₀.preChan u v).head? := by
      intro u v hp₁
      have hp₂ : ¬ e₂.popsFrom u v := fun hp₂ => hnot_both_pop u v ⟨hp₁, hp₂⟩
      rcases eq_or_ne u e₂.actor with rfl | hu₂
      · obtain ⟨h, t, hht⟩ := List.exists_cons_of_ne_nil (hpre_pop₁_from_q v hp₁)
        simp [C₁', hp₂, hht]
      · simp [C₁', hp₂, hu₂]
    refine ⟨htr_e₁', he₁_some, hC₂snap.trans hC₁snap, ?_, ?_, ?_⟩
    · intro u v; rw [(hC₂pre u v).2, hC₁pre u v]
      by_cases hp₁ : e₁.popsFrom u v
      · obtain ⟨hp₂, htail, _, _⟩ := hpre_shape u v hp₁; simp [hp₁, hp₂, htail]
      · simp [C₁', hp₁]
    · intro u v; rw [hC₂post, hC₁post u v]
      by_cases hp₁ : e₁.popsFrom u v
      · simp [C₁', hp₁, (hpre_shape u v hp₁).2.2.1]
      · simp [C₁', hp₁]
    · intro u v; rw [hC₂rec, hC₁rec u v]
      by_cases hp₁ : e₁.popsFrom u v
      · simp only [hp₁, ↓reduceIte]; exact hmatch _ _ _ (hpre_shape u v hp₁).2.2.2.symm
      · simp [C₁', hp₁]

/-! #### Pushing `cross` and `post` steps past `pre` and `cross` blocks -/

private lemma push_cross_past_pre [DecidableEq P] {C₀ C₁ C₂ : CutState P S M}
    {p : P} {es : List (Event P S M)}
    (htr : CutTr sys C₀ (.cross p) C₁) (hmtr : CutMTr sys C₁ (es.map CutStep.pre) C₂) :
    ∃ C₁', CutMTr sys C₀ (es.map CutStep.pre) C₁' ∧ CutTr sys C₁' (.cross p) C₂ := by
  induction es generalizing C₀ C₁ with
  | nil =>
    cases hmtr
    exact ⟨C₀, .refl, htr⟩
  | cons e es ih =>
    cases hmtr with
    | stepL hpre hrest =>
      obtain ⟨Cm, hpre', hcross'⟩ := sys.swap_cross_pre htr hpre
      obtain ⟨C₁', hmtr', hcross_end⟩ := ih hcross' hrest
      exact ⟨C₁', .stepL hpre' hmtr', hcross_end⟩

private lemma push_post_past_pre [DecidableEq P] {C₀ C₁ C₂ : CutState P S M}
    {e : Event P S M} {es : List (Event P S M)} (hv₀ : C₀.Valid)
    (htr : CutTr sys C₀ (.post e) C₁) (hmtr : CutMTr sys C₁ (es.map CutStep.pre) C₂) :
    ∃ C₁', CutMTr sys C₀ (es.map CutStep.pre) C₁' ∧ CutTr sys C₁' (.post e) C₂ := by
  induction es generalizing C₀ C₁ with
  | nil =>
    cases hmtr
    exact ⟨C₀, .refl, htr⟩
  | cons e₂ es ih =>
    cases hmtr with
    | stepL hpre hrest =>
      obtain ⟨Cm, hpre', hpost'⟩ := sys.swap_post_pre hv₀ htr hpre
      have hvm : Cm.Valid := sys.cutTr_preserves_valid hv₀ hpre'
      obtain ⟨C₁', hmtr', hpost_end⟩ := ih hvm hpost' hrest
      exact ⟨C₁', .stepL hpre' hmtr', hpost_end⟩

private lemma push_post_past_cross [DecidableEq P] {C₀ C₁ C₂ : CutState P S M}
    {e : Event P S M} {ps : List P}
    (htr : CutTr sys C₀ (.post e) C₁) (hmtr : CutMTr sys C₁ (ps.map CutStep.cross) C₂) :
    ∃ C₁', CutMTr sys C₀ (ps.map CutStep.cross) C₁' ∧ CutTr sys C₁' (.post e) C₂ := by
  induction ps generalizing C₀ C₁ with
  | nil =>
    cases hmtr
    exact ⟨C₀, .refl, htr⟩
  | cons q ps ih =>
    cases hmtr with
    | stepL hcross hrest =>
      obtain ⟨Cm, hcross', hpost'⟩ := sys.swap_post_cross htr hcross
      obtain ⟨C₁', hmtr', hpost_end⟩ := ih hpost' hrest
      exact ⟨C₁', .stepL hcross' hmtr', hpost_end⟩

private lemma snapMTr_ordered_cutMTr [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S_init S_end : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hinv : sys.SnapInv S_init) (hmtr : sys.snapLts.MTr S_init xl S_end) :
    ∃ (crossProcs : List P) (C₁ C₂ : CutState P S M),
      CutMTr sys (ofSnap S_init) ((sys.tracePreEvents S_init xl).map CutStep.pre) C₁ ∧
      CutMTr sys C₁ (crossProcs.map CutStep.cross) C₂ ∧
      CutMTr sys C₂ ((sys.tracePostEvents S_init xl).map CutStep.post) (ofSnap S_end) ∧
      (sys.tracePreEvents S_init xl ++ sys.tracePostEvents S_init xl).Perm (eraseTrace xl) := by
  induction hmtr with
  | refl =>
    exact ⟨[], _, _, .refl, .refl, .refl, List.Perm.refl []⟩
  | @stepL S₀ a S₁ rest S_end htr hrest ih =>
    have hinv₁ : sys.SnapInv S₁ := sys.snapInv_tr S₀ a S₁ htr hinv
    obtain ⟨hen, rfl⟩ := htr
    obtain ⟨ps, C₁, C₂, hpre_m, hcross_m, hpost_m, hperm⟩ := ih hinv₁
    cases a with
    | stutter =>
      exact ⟨ps, C₁, C₂, hpre_m, hcross_m, hpost_m, hperm⟩
    | initiateSnapshot p =>
      have hstep := sys.ofSnap_step_initiate hinv hen
      obtain ⟨C₁', hpre_m', hcross_step⟩ := sys.push_cross_past_pre hstep hpre_m
      exact ⟨p :: ps, C₁', C₂, hpre_m', .stepL hcross_step hcross_m, hpost_m, hperm⟩
    | recvMarker src dest =>
      cases hdest : (S₀.proc dest).snapState with
      | none =>
        have hstep := sys.ofSnap_step_recvMarker_none hinv hen hdest
        obtain ⟨C₁', hpre_m', hcross_step⟩ := sys.push_cross_past_pre hstep hpre_m
        exact ⟨dest :: ps, C₁', C₂, hpre_m', .stepL hcross_step hcross_m, hpost_m, hperm⟩
      | some s_d =>
        have heq := sys.ofSnap_step_recvMarker_some hinv hen hdest
        exact ⟨ps, C₁, C₂, heq ▸ hpre_m, hcross_m, hpost_m, hperm⟩
    | app e =>
      cases hact : (S₀.proc e.actor).snapState with
      | none =>
        have hstep := sys.ofSnap_step_app_pre hinv hen hact
        simp only [tracePreEvents, tracePostEvents, hact, Option.isNone_none, ↓reduceIte,
          Option.isSome_none, Bool.false_eq_true, eraseTrace, List.filterMap_cons,
          SnapEvent.toAppEvent]
        exact ⟨ps, C₁, C₂, .stepL hstep hpre_m, hcross_m, hpost_m, hperm.cons e⟩
      | some s_p =>
        have hact_some : (S₀.proc e.actor).snapState.isSome = true := by simp [hact]
        have hact_none : (S₀.proc e.actor).snapState.isNone = false := by simp [hact]
        have hstep := sys.ofSnap_step_app_post hinv hen hact_some
        obtain ⟨C₁', hpre_m', hpost₁⟩ :=
          sys.push_post_past_pre (sys.valid_ofSnap hinv) hstep hpre_m
        obtain ⟨C₂', hcross_m', hpost₂⟩ := sys.push_post_past_cross hpost₁ hcross_m
        simp only [tracePreEvents, tracePostEvents, hact_none, Bool.false_eq_true, ↓reduceIte,
          hact_some, eraseTrace, List.filterMap_cons, SnapEvent.toAppEvent]
        exact ⟨ps, C₁', C₂', hpre_m', hcross_m', .stepL hpost₂ hpost_m,
          List.perm_middle.trans (hperm.cons e)⟩

/-! #### Identifying the boundary state `C₁.s = extractSnapshot S_final` -/

private lemma cutMTr_pre_props [DecidableEq P] {C₀ C₁ : CutState P S M}
    {es : List (Event P S M)} (hmtr : CutMTr sys C₀ (es.map CutStep.pre) C₁) :
    sys.lts.MTr C₀.s es C₁.s ∧
    C₁.snapProc = C₀.snapProc ∧
    C₁.postChan = C₀.postChan ∧
    C₁.recBuf = C₀.recBuf := by
  induction es generalizing C₀ with
  | nil =>
    cases hmtr
    exact ⟨.refl, rfl, rfl, rfl⟩
  | cons e es ih =>
    cases hmtr with
    | stepL htr hrest =>
      obtain ⟨hmtr', hsnap, hpost, hrec⟩ := ih hrest
      exact ⟨.stepL htr.1 hmtr', hsnap.trans htr.2.2.1, hpost.trans htr.2.2.2.1,
        hrec.trans htr.2.2.2.2.1⟩

private lemma cutMTr_cross_props [DecidableEq P] {C₁ C₂ : CutState P S M}
    {ps : List P} (hmtr : CutMTr sys C₁ (ps.map CutStep.cross) C₂) :
    C₂.s = C₁.s ∧
    C₂.preChan = C₁.preChan ∧
    C₂.postChan = C₁.postChan ∧
    C₂.recBuf = C₁.recBuf ∧
    ∀ p, C₁.snapProc p = none → ∀ s_p, C₂.snapProc p = some s_p → C₁.s.proc p = s_p := by
  induction ps generalizing C₁ with
  | nil =>
    cases hmtr
    exact ⟨rfl, rfl, rfl, rfl, fun p hnone s_p hsome => by simp [hnone] at hsome⟩
  | cons q ps ih =>
    cases hmtr with
    | @stepL _ _ Cm _ _ htr hrest =>
      rcases htr with ⟨_, hCms, hCmsnap, hCmpre, hCmpost, hCmrec⟩
      obtain ⟨hs, hpre, hpost, hrec, hproc⟩ := ih hrest
      refine ⟨hs.trans hCms, hpre.trans hCmpre, hpost.trans hCmpost, hrec.trans hCmrec, ?_⟩
      intro p hp_none s_p hp_some
      rcases eq_or_ne p q with rfl | hpq
      · have hconst : ∀ {Ca Cb : CutState P S M} {qs : List P},
            CutMTr sys Ca (qs.map CutStep.cross) Cb →
            ∀ v, Ca.snapProc p = some v → Cb.snapProc p = some v := by
          intro Ca Cb qs hm v hv
          induction qs generalizing Ca with
          | nil =>
            cases hm
            exact hv
          | cons r qs ihq =>
            cases hm with
            | stepL ht hr =>
              have hpr : p ≠ r := fun h => by simp [h, ht.1] at hv
              exact ihq hr (by simpa [ht.2.2.1, hpr] using hv)
        have heq_some : C₂.snapProc p = some (C₁.s.proc p) :=
          hconst hrest (C₁.s.proc p) (by simp [hCmsnap])
        exact Option.some.inj (heq_some.symm.trans hp_some)
      · rw [← hCms]
        exact hproc p (by simpa [hCmsnap, hpq] using hp_none) s_p hp_some

private lemma cutMTr_post_props [DecidableEq P] {C₂ C₃ : CutState P S M}
    {es : List (Event P S M)} (hmtr : CutMTr sys C₂ (es.map CutStep.post) C₃) :
    sys.lts.MTr C₂.s es C₃.s ∧
    C₃.snapProc = C₂.snapProc ∧
    ∀ u v, C₃.recBuf u v ++ C₃.preChan u v = C₂.recBuf u v ++ C₂.preChan u v := by
  induction es generalizing C₂ with
  | nil =>
    cases hmtr
    exact ⟨.refl, rfl, fun _ _ => rfl⟩
  | cons e es ih =>
    cases hmtr with
    | @stepL _ _ Cm _ _ htr hrest =>
      rcases htr with ⟨htr_e, _, hsnap₁, hpre₁, _, hrec₁⟩
      obtain ⟨hmtr', hsnap₂, hbuf₂⟩ := ih hrest
      refine ⟨.stepL htr_e hmtr', hsnap₂.trans hsnap₁, fun u v => ?_⟩
      rw [hbuf₂ u v, hrec₁ u v, hpre₁ u v]
      by_cases hp : e.popsFrom u v
      · cases C₂.preChan u v <;> simp [hp, List.append_assoc]
      · simp [hp]

private lemma cutMTr_preserves_valid [DecidableEq P] {C₁ C₂ : CutState P S M}
    {sts : List (CutStep P S M)} (hv : C₁.Valid) (hmtr : CutMTr sys C₁ sts C₂) : C₂.Valid := by
  induction hmtr with
  | refl => exact hv
  | stepL htr _ ih => exact ih (sys.cutTr_preserves_valid hv htr)

/-- **Chandy–Lamport explicit causal permutation theorem ([ChandyLamport1985], §4, Theorem 1,
pp. 72–73):** for any finite execution `S_init →*[xl] S_final` from a pre-snapshot state `S_init` to
a snapshot-complete state `S_final`, executing all pre-snapshot events (`tracePreEvents S_init xl`)
from `project S_init` reaches `extractSnapshot S_final` in `sys.lts`, executing all post-snapshot
events (`tracePostEvents S_init xl`) from `extractSnapshot S_final` reaches `project S_final` in
`sys.lts`, and `tracePreEvents S_init xl ++ tracePostEvents S_init xl` is a permutation of
`eraseTrace xl` (any prefix before `S_init` and suffix after `S_final` compose unchanged via
`LTS.MTr.comp`). -/
theorem chandyLamport_perm_mTr [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S_init S_final : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hpre : sys.IsPreSnapshot S_init)
    (hmtr : sys.snapLts.MTr S_init xl S_final)
    (hcomp : IsSnapshotComplete S_final) :
    sys.lts.MTr (project S_init) (sys.tracePreEvents S_init xl) (extractSnapshot S_final) ∧
    sys.lts.MTr (extractSnapshot S_final) (sys.tracePostEvents S_init xl) (project S_final) ∧
    (sys.tracePreEvents S_init xl ++ sys.tracePostEvents S_init xl).Perm (eraseTrace xl) := by
  have hinv₀ : sys.SnapInv S_init := sys.snapInv_of_isPreSnapshot hpre
  have hinv_f : sys.SnapInv S_final := sys.snapInv_mTr hpre hmtr
  obtain ⟨ps, C₁, C₂, hpre_m, hcross_m, hpost_m, hperm⟩ := sys.snapMTr_ordered_cutMTr hinv₀ hmtr
  have hv₁ : C₁.Valid := sys.cutMTr_preserves_valid (sys.valid_ofSnap hinv₀) hpre_m
  obtain ⟨hmtr_pre, hC₁_snap, hC₁_post, hC₁_rec⟩ := sys.cutMTr_pre_props hpre_m
  obtain ⟨hC₂_s, hC₂_pre, _, hC₂_rec, hC₁_proc_eq⟩ := sys.cutMTr_cross_props hcross_m
  obtain ⟨hmtr_post, hCf_snap, hbuf_inv⟩ := sys.cutMTr_post_props hpost_m
  have hC₁_eq : C₁.s = extractSnapshot S_final := by
    apply GlobalState.ext
    · funext p
      obtain ⟨s_p, hs_p⟩ := Option.isSome_iff_exists.mp (hcomp.1 p)
      rw [hC₁_proc_eq p (hC₁_snap ▸ hpre.1 p) s_p (hCf_snap ▸ hs_p)]
      simp [extractSnapshot, hs_p]
    · funext u v
      have hC₁_chan : C₁.s.chan u v = C₁.preChan u v := by
        simp [hv₁.1 u v, hC₁_post, ofSnap,
          postInFlight_eq_nil_of_unrecorded (hpre.1 u) (hpre.2.1 u v)]
      have hCf_pre : preInFlight S_final u v = [] :=
        preInFlight_eq_nil_of_recorded_of_notMem (hcomp.1 u)
          (sys.isSnapshotComplete_no_markers hinv_f hcomp u v)
      simpa [extractSnapshot, ofSnap, hCf_pre, hcomp.1 v, hC₂_rec, hC₁_rec, hpre.1 v, hC₂_pre,
        ← hC₁_chan] using (hbuf_inv u v).symm
  rw [← hC₁_eq]
  exact ⟨hmtr_pre, hC₂_s ▸ hmtr_post, hperm⟩

/-- **Chandy–Lamport consistent-cut reachability theorem ([ChandyLamport1985], §4, Theorem 1,
p. 72):** if a finite augmented execution starts before any snapshot action (`IsPreSnapshot S_init`)
and ends at a state where the global snapshot is complete (`IsSnapshotComplete S_final`), then in
the underlying FIFO system `sys.lts`, the assembled snapshot `S* = extractSnapshot S_final` is
reachable from `project S_init` and `project S_final` is reachable from `S*`. -/
theorem chandyLamport_consistent_cut [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S_init S_final : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hpre : sys.IsPreSnapshot S_init)
    (hmtr : sys.snapLts.MTr S_init xl S_final)
    (hcomp : IsSnapshotComplete S_final) :
    sys.lts.CanReach (project S_init) (extractSnapshot S_final) ∧
    sys.lts.CanReach (extractSnapshot S_final) (project S_final) := by
  obtain ⟨h₁, h₂, _⟩ := sys.chandyLamport_perm_mTr hpre hmtr hcomp
  exact ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩

/-! ### Part 3: Stable-property detection corollary -/

/-- **Stable-property detection (`stablePred_transfer`, [ChandyLamport1985], §5, pp. 74–75):** for
every stable global predicate `Φ` of `sys`, if `Φ` holds in the recorded snapshot
`extractSnapshot S_final`, then `Φ` holds in the actual physical state `project S_final` once the
snapshot finishes; contrapositively (matching `y(S_ι) → definite` on p. 74), if `Φ` fails in
`extractSnapshot S_final`, then `Φ` had not yet become true at `project S_init`. -/
theorem stablePred_transfer [DecidableEq P] [DecidableRel sys.graph.Adj]
    {Φ : GlobalState P S M → Prop} (hΦ : IsStablePred sys Φ)
    {S_init S_final : SnapGlobalState P S M} {xl : List (SnapEvent P S M)}
    (hpre : sys.IsPreSnapshot S_init)
    (hmtr : sys.snapLts.MTr S_init xl S_final)
    (hcomp : IsSnapshotComplete S_final) :
    (Φ (extractSnapshot S_final) → Φ (project S_final)) ∧
    (¬ Φ (extractSnapshot S_final) → ¬ Φ (project S_init)) := by
  obtain ⟨hr₁, hr₂⟩ := sys.chandyLamport_consistent_cut hpre hmtr hcomp
  exact ⟨hΦ.canReach hr₂, hΦ.not_of_canReach hr₁⟩

end System

/-! ### Part 4: Fair FIFO channel delivery & snapshot completion liveness -/

/-- Whether augmented event `a` delivers the head message (application payload or `.marker`) on
channel `(src, dest)`. -/
@[expose] def SnapEvent.deliversOn {P S M : Type*} (a : SnapEvent P S M) (src dest : P) : Prop :=
  match a with
  | .app (.recv u v _ _ _) => u = src ∧ v = dest
  | .recvMarker u v => u = src ∧ v = dest
  | _ => False

/-- Weak FIFO channel delivery fairness: whenever channel `(src, dest)` is non-empty at step `k`,
some step `j ≥ k` delivers from the head of `(src, dest)`. -/
@[expose] def FairChannels {P S M : Type*}
    (ss : ωSequence (SnapGlobalState P S M)) (xs : ωSequence (SnapEvent P S M)) : Prop :=
  ∀ src dest k, (ss k).chan src dest ≠ [] → ∃ j, k ≤ j ∧ (xs j).deliversOn src dest

/-- A directed communication graph `G` is strongly connected if every vertex `v` is reachable from
every vertex `u` by a directed path (`Relation.ReflTransGen G.Adj u v`). -/
@[expose] def StronglyConnected {P : Type*} (G : Digraph P) : Prop :=
  ∀ u v : P, Relation.ReflTransGen G.Adj u v

/-- The complete directed graph `⊤` is strongly connected. -/
theorem stronglyConnected_top (P : Type*) : StronglyConnected (⊤ : Digraph P) :=
  fun _ _ => Relation.ReflTransGen.single trivial

namespace System

variable {P S M : Type*} (sys : System P S M)

/-! #### Monotonicity of recorded process states and completed channel recorders -/

/-- Once process `p` records `snapState = some s_p`, every subsequent transition of `sys.snapLts`
preserves `snapState = some s_p` (write-once local snapshot). -/
theorem snapState_stable_tr [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {a : SnapEvent P S M} {p : P} {s_p : S}
    (htr : sys.snapLts.Tr S₁ a S₂) (hs : (S₁.proc p).snapState = some s_p) :
    (S₂.proc p).snapState = some s_p := by
  obtain ⟨hen, rfl⟩ := htr
  cases a with
  | stutter => exact hs
  | app e => exact (applyApp_snapState S₁ e p).trans hs
  | initiateSnapshot q =>
    have hpq : p ≠ q := by rintro rfl; rw [hen] at hs; cases hs
    simp [stepSnap, applyInitiate, hpq, hs]
  | recvMarker src dest =>
    simp only [stepSnap, applyRecvMarker]
    rcases eq_or_ne p dest with rfl | hpd
    · simp [hs]
    · split <;> simp [hpd, hs]

private theorem snapState_isSome_omega [DecidableEq P] [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hexec : sys.snapLts.OmegaExecution ss xs) {p : P} {k j : ℕ} (hkj : k ≤ j)
    (hs : ((ss k).proc p).snapState.isSome = true) :
    ((ss j).proc p).snapState.isSome = true := by
  obtain ⟨s_p, hs_p⟩ := Option.isSome_iff_exists.mp hs
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  suffices ((ss (k + d)).proc p).snapState = some s_p by simp [this]
  induction d with
  | zero => simpa using hs_p
  | succ d ih =>
    exact sys.snapState_stable_tr (hexec (k + d)) (ih (Nat.le_add_right k d))

/-- Once process `p` has recorded (`snapState.isSome`) and finalized incoming recorder
`chanRec q = .done saved`, every subsequent transition of `sys.snapLts` preserves `.done saved`. -/
theorem chanRec_done_stable_tr [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {a : SnapEvent P S M} {q p : P} {saved : List M}
    (htr : sys.snapLts.Tr S₁ a S₂)
    (hs : ((S₁.proc p).snapState).isSome = true)
    (hd : (S₁.proc p).chanRec q = .done saved) :
    (S₂.proc p).chanRec q = .done saved := by
  obtain ⟨hen, rfl⟩ := htr
  cases a with
  | stutter => exact hd
  | app e =>
    simp only [stepSnap]
    cases e with
    | internal r st' sent =>
      rcases eq_or_ne p r with rfl | hpr <;> simp_all [SnapGlobalState.applyApp]
    | recv src dest msg st' sent =>
      rcases eq_or_ne p dest with rfl | hpd <;> rcases eq_or_ne q src with rfl | hqs <;>
        simp_all [SnapGlobalState.applyApp, ChannelRec.recordApp]
  | initiateSnapshot r =>
    have hpr : p ≠ r := by rintro rfl; rw [hen] at hs; simp at hs
    simp [stepSnap, applyInitiate, hpr, hd]
  | recvMarker src dest =>
    simp only [stepSnap, applyRecvMarker]
    rcases eq_or_ne p dest with rfl | hpd
    · obtain ⟨s_p, hs_p⟩ := Option.isSome_iff_exists.mp hs
      rcases eq_or_ne q src with rfl | hqs <;> simp_all [ChannelRec.msgs]
    · split <;> simp [hpd, hd]

private theorem chanRec_isDone_omega [DecidableEq P] [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hexec : sys.snapLts.OmegaExecution ss xs) {q p : P} {k j : ℕ} (hkj : k ≤ j)
    (hs : ((ss k).proc p).snapState.isSome = true)
    (hd : (((ss k).proc p).chanRec q).isDone = true) :
    (((ss j).proc p).chanRec q).isDone = true := by
  obtain ⟨saved, hsaved⟩ : ∃ saved, ((ss k).proc p).chanRec q = .done saved := by
    cases h : ((ss k).proc p).chanRec q with
    | recording _ => rw [h] at hd; simp [ChannelRec.isDone] at hd
    | done sv => exact ⟨sv, rfl⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hkj
  suffices ((ss (k + d)).proc p).chanRec q = .done saved by simp [this, ChannelRec.isDone]
  induction d with
  | zero => simpa using hsaved
  | succ d ih =>
    have hs_d := sys.snapState_isSome_omega hexec (Nat.le_add_right k d) hs
    exact sys.chanRec_done_stable_tr (hexec (k + d)) hs_d (ih (Nat.le_add_right k d))

/-! #### FIFO progress of `.marker` along a single edge -/

private lemma chan_append_of_not_deliversOn [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {a : SnapEvent P S M} {q p : P}
    (htr : sys.snapLts.Tr S₁ a S₂) (hnd : ¬ a.deliversOn q p) :
    ∃ extra, S₂.chan q p = S₁.chan q p ++ extra := by
  obtain ⟨_, rfl⟩ := htr
  cases a with
  | stutter => exact ⟨[], by simp [stepSnap]⟩
  | initiateSnapshot r =>
    refine ⟨if q = r ∧ sys.graph.Adj r p then [.marker] else [], ?_⟩
    by_cases h : q = r ∧ sys.graph.Adj r p <;> simp [stepSnap, applyInitiate, h]
  | recvMarker src dest =>
    have hne_sd : ¬ (q = src ∧ p = dest) := fun ⟨h₁, h₂⟩ => hnd ⟨h₁.symm, h₂.symm⟩
    simp only [stepSnap, applyRecvMarker]
    cases (S₁.proc dest).snapState
    · simp only [hne_sd, ↓reduceIte]
      refine ⟨if q = dest ∧ sys.graph.Adj dest p then [.marker] else [], ?_⟩
      by_cases h : q = dest ∧ sys.graph.Adj dest p <;> simp [h]
    · exact ⟨[], by simp [hne_sd]⟩
  | app e =>
    cases e with
    | internal r st' sent =>
      refine ⟨if q = r then (outgoingTo sent p).map WireMsg.app else [], ?_⟩
      by_cases h : q = r <;> simp [stepSnap, SnapGlobalState.applyApp, h]
    | recv src dest msg st' sent =>
      have hne_sd : ¬ (q = src ∧ p = dest) := fun ⟨h₁, h₂⟩ => hnd ⟨h₁.symm, h₂.symm⟩
      refine ⟨if q = dest then (outgoingTo sent p).map WireMsg.app else [], ?_⟩
      by_cases h : q = dest <;> simp_all [stepSnap, SnapGlobalState.applyApp]

private lemma chan_append_of_deliversOn [DecidableEq P] [DecidableRel sys.graph.Adj]
    {S₁ S₂ : SnapGlobalState P S M} {a : SnapEvent P S M} {q p : P}
    (htr : sys.snapLts.Tr S₁ a S₂) (hd : a.deliversOn q p) :
    ∃ extra, S₂.chan q p = (S₁.chan q p).tail ++ extra := by
  obtain ⟨_, rfl⟩ := htr
  cases a with
  | stutter | initiateSnapshot _ => exact False.elim hd
  | recvMarker u v =>
    rcases hd with ⟨rfl, rfl⟩
    dsimp only [stepSnap, applyRecvMarker]
    cases (S₁.proc v).snapState
    · refine ⟨if u = v ∧ sys.graph.Adj v v then [.marker] else [], ?_⟩
      by_cases h : u = v ∧ sys.graph.Adj v v <;> simp [h]
    · exact ⟨[], by simp⟩
  | app e =>
    cases e with
    | internal _ _ _ => exact False.elim hd
    | recv u v msg st' sent =>
      rcases hd with ⟨rfl, rfl⟩
      refine ⟨if u = v then (outgoingTo sent u).map WireMsg.app else [], ?_⟩
      by_cases h : u = v <;> simp [stepSnap, SnapGlobalState.applyApp, h]

private lemma chan_prefix_until_delivery [DecidableEq P] [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hexec : sys.snapLts.OmegaExecution ss xs) {q p : P} {k d : ℕ}
    (hnone : ∀ i < d, ¬ (xs (k + i)).deliversOn q p) :
    ∃ extra, (ss (k + d)).chan q p = (ss k).chan q p ++ extra := by
  induction d with
  | zero => exact ⟨[], by simp⟩
  | succ d ih =>
    obtain ⟨ex₁, hex₁⟩ := ih fun i hi => hnone i (Nat.lt_succ_of_lt hi)
    obtain ⟨ex₂, hex₂⟩ := sys.chan_append_of_not_deliversOn (hexec (k + d))
      (hnone d (Nat.lt_succ_self d))
    exact ⟨ex₁ ++ ex₂, by rw [Nat.add_succ, hex₂, hex₁, List.append_assoc]⟩

/-- Under channel fairness, a non-empty channel is eventually delivered from, and until then it
only grows at the back. -/
private lemma exists_delivery_prefix [DecidableEq P] [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hexec : sys.snapLts.OmegaExecution ss xs) (hfair : FairChannels ss xs)
    {q p : P} {k : ℕ} (hne : (ss k).chan q p ≠ []) :
    ∃ d extra, (xs (k + d)).deliversOn q p ∧ (ss (k + d)).chan q p = (ss k).chan q p ++ extra := by
  classical
  have hex_del : ∃ d, (xs (k + d)).deliversOn q p := by
    obtain ⟨j, hkj, hj⟩ := hfair q p k hne
    exact ⟨j - k, by rwa [Nat.add_sub_cancel' hkj]⟩
  obtain ⟨extra, hextra⟩ :=
    sys.chan_prefix_until_delivery hexec fun i hi => Nat.find_min hex_del hi
  exact ⟨_, extra, Nat.find_spec hex_del, hextra⟩

private lemma marker_eventually_delivered [DecidableEq P] [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hexec : sys.snapLts.OmegaExecution ss xs) (hfair : FairChannels ss xs)
    {q p : P} :
    ∀ n k (pre suf : List (WireMsg M)),
      pre.length = n →
      (ss k).chan q p = pre ++ .marker :: suf →
      ∃ j, k ≤ j ∧ ((ss j).proc p).snapState.isSome = true ∧
        (((ss j).proc p).chanRec q).isDone = true := by
  intro n
  induction n with
  | zero =>
    intro k pre suf hlen hch
    obtain rfl := List.eq_nil_of_length_eq_zero hlen
    obtain ⟨d, extra, hd_spec, hextra⟩ :=
      sys.exists_delivery_prefix hexec hfair (q := q) (p := p) (k := k) (by simp [hch])
    rw [hch, List.nil_append, List.cons_append] at hextra
    obtain ⟨hen, hstep⟩ := hexec (k + d)
    cases hxd : xs (k + d) with
    | stutter | initiateSnapshot _ => rw [hxd] at hd_spec; exact False.elim hd_spec
    | app e =>
      rw [hxd] at hd_spec hen
      cases e with
      | internal _ _ _ => exact False.elim hd_spec
      | recv u v msg _ _ =>
        rcases hd_spec with ⟨rfl, rfl⟩
        simpa [hextra] using hen.2.1
    | recvMarker u v =>
      rw [hxd] at hd_spec hstep
      rcases hd_spec with ⟨rfl, rfl⟩
      refine ⟨k + d + 1, by omega, ?_⟩
      rw [hstep]
      dsimp only [stepSnap, applyRecvMarker]
      cases ((ss (k + d)).proc v).snapState <;> simp [ChannelRec.isDone]
  | succ n ih =>
    intro k pre suf hlen hch
    obtain _ | ⟨w, pre'⟩ := pre
    · simp at hlen
    obtain ⟨d, ex₁, hd_spec, hex₁⟩ :=
      sys.exists_delivery_prefix hexec hfair (q := q) (p := p) (k := k) (by simp [hch])
    obtain ⟨ex₂, hex₂⟩ := sys.chan_append_of_deliversOn (hexec (k + d)) hd_spec
    obtain ⟨j, hkj, hjs, hjd⟩ := ih (k + d + 1) pre' (suf ++ ex₁ ++ ex₂) (by simpa using hlen)
      (by rw [hex₂, hex₁, hch]; simp)
    exact ⟨j, by omega, hjs, hjd⟩

private lemma edge_propagation [DecidableEq P] [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hpre₀ : sys.IsPreSnapshot (ss 0))
    (hexec : sys.snapLts.OmegaExecution ss xs) (hfair : FairChannels ss xs)
    {q p : P} (hadj : sys.graph.Adj q p) {k : ℕ}
    (hq : ((ss k).proc q).snapState.isSome = true) :
    ∃ j, k ≤ j ∧ ((ss j).proc p).snapState.isSome = true ∧
      (((ss j).proc p).chanRec q).isDone = true := by
  have hinv_k : sys.SnapInv (ss k) :=
    sys.snapInv_mTr hpre₀ (hexec.extract_mTr (Nat.zero_le k))
  rcases hinv_k.recordedSrc q p hq hadj with ⟨hmem, _⟩ | ⟨_, hp_some, ⟨sv, hsv⟩⟩
  · obtain ⟨pre, suf, hsplit⟩ := List.append_of_mem hmem
    exact sys.marker_eventually_delivered hexec hfair pre.length k pre suf rfl hsplit
  · exact ⟨k, le_rfl, hp_some, by simp [hsv, ChannelRec.isDone]⟩

private lemma path_propagation [DecidableEq P] [DecidableRel sys.graph.Adj]
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hpre₀ : sys.IsPreSnapshot (ss 0))
    (hexec : sys.snapLts.OmegaExecution ss xs) (hfair : FairChannels ss xs)
    {p₀ p : P} (hpath : Relation.ReflTransGen sys.graph.Adj p₀ p) {k₀ : ℕ}
    (hp₀ : ((ss k₀).proc p₀).snapState.isSome = true) :
    ∃ k, k₀ ≤ k ∧ ((ss k).proc p).snapState.isSome = true := by
  induction hpath with
  | refl => exact ⟨k₀, le_rfl, hp₀⟩
  | @tail u v _ hadj ih =>
    obtain ⟨k₁, hk₀₁, hu⟩ := ih
    obtain ⟨k₂, hk₁₂, hv, _⟩ := sys.edge_propagation hpre₀ hexec hfair hadj hu
    exact ⟨k₂, hk₀₁.trans hk₁₂, hv⟩

/-- **Chandy–Lamport snapshot completion liveness ([ChandyLamport1985], §3.3, p. 71):** on any
finite strongly connected communication graph, in any infinite execution starting from a
pre-snapshot state that satisfies weak FIFO channel delivery fairness (`FairChannels`, realizing
`(L1)` while atomic marker handling discharges `(L2)`) and in which at least one process records a
snapshot (`((ss k₀).proc p₀).snapState.isSome`), there exists a step `K` from which
`IsSnapshotComplete (ss k)` holds permanently (`∀ k ≥ K`). -/
theorem snapshot_liveness [Finite P] [DecidableEq P] [DecidableRel sys.graph.Adj]
    (hsc : StronglyConnected sys.graph)
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hpre₀ : sys.IsPreSnapshot (ss 0))
    (hexec : sys.snapLts.OmegaExecution ss xs)
    (hfair : FairChannels ss xs)
    {p₀ : P} {k₀ : ℕ} (hinit : ((ss k₀).proc p₀).snapState.isSome = true) :
    ∃ K, k₀ ≤ K ∧ ∀ k, K ≤ k → IsSnapshotComplete (ss k) := by
  cases nonempty_fintype P
  have hproc_ev : ∀ p : P, ∃ k, k₀ ≤ k ∧ ((ss k).proc p).snapState.isSome = true :=
    fun p => sys.path_propagation hpre₀ hexec hfair (hsc p₀ p) hinit
  choose f_proc hf_proc using hproc_ev
  let K₁ := max k₀ (Finset.univ.sup f_proc)
  have hk₀_K₁ : k₀ ≤ K₁ := le_max_left _ _
  have hK₁_all : ∀ p : P, ((ss K₁).proc p).snapState.isSome = true := by
    intro p
    have hle : f_proc p ≤ K₁ :=
      (Finset.le_sup (f := f_proc) (Finset.mem_univ p)).trans (le_max_right _ _)
    exact sys.snapState_isSome_omega hexec hle (hf_proc p).2
  have hinv_K₁ : sys.SnapInv (ss K₁) :=
    sys.snapInv_mTr hpre₀ (hexec.extract_mTr (Nat.zero_le K₁))
  have hedge_ev : ∀ qp : P × P,
      ∃ j, K₁ ≤ j ∧ (((ss j).proc qp.2).chanRec qp.1).isDone = true := by
    rintro ⟨q, p⟩
    by_cases hadj : sys.graph.Adj q p
    · obtain ⟨j, hKj, _, hdone⟩ := sys.edge_propagation hpre₀ hexec hfair hadj (hK₁_all q)
      exact ⟨j, hKj, hdone⟩
    · have hdone := (hinv_K₁.nonEdge q p hadj).2 (hK₁_all p)
      exact ⟨K₁, le_rfl, by simp [hdone, ChannelRec.isDone]⟩
  choose f_edge hf_edge using hedge_ev
  let K := max K₁ ((Finset.univ : Finset (P × P)).sup f_edge)
  have hK₁_K : K₁ ≤ K := le_max_left _ _
  refine ⟨K, hk₀_K₁.trans hK₁_K, fun k hKk => ⟨?_, ?_⟩⟩
  · intro p
    exact sys.snapState_isSome_omega hexec (hK₁_K.trans hKk) (hK₁_all p)
  · intro q p
    have hfj_le : f_edge (q, p) ≤ K :=
      (Finset.le_sup (f := f_edge) (Finset.mem_univ (q, p))).trans (le_max_right _ _)
    have hs_fj : ((ss (f_edge (q, p))).proc p).snapState.isSome = true :=
      sys.snapState_isSome_omega hexec (hf_edge (q, p)).1 (hK₁_all p)
    exact sys.chanRec_isDone_omega hexec (hfj_le.trans hKk) hs_fj (hf_edge (q, p)).2

/-- Specialization of `snapshot_liveness` to the complete directed network `sys.graph = ⊤`. -/
theorem snapshot_liveness_complete [Finite P] [DecidableEq P] [DecidableRel sys.graph.Adj]
    (htop : sys.graph = ⊤)
    {ss : ωSequence (SnapGlobalState P S M)} {xs : ωSequence (SnapEvent P S M)}
    (hpre₀ : sys.IsPreSnapshot (ss 0))
    (hexec : sys.snapLts.OmegaExecution ss xs)
    (hfair : FairChannels ss xs)
    {p₀ : P} {k₀ : ℕ} (hinit : ((ss k₀).proc p₀).snapState.isSome = true) :
    ∃ K, k₀ ≤ K ∧ ∀ k, K ≤ k → IsSnapshotComplete (ss k) :=
  sys.snapshot_liveness (htop ▸ stronglyConnected_top P) hpre₀ hexec hfair hinit

/-! #### Non-vacuity: fair FIFO scheduler for input-enabled systems -/

/-- A `System` is *input-enabled* if receiving a message at the head of an incident channel is
never locally blocked: for every edge `(src, dest)`, local state `st`, and incoming message `msg`,
there exist `st'` and `sent` satisfying `sys.recv` and respecting `sys.graph`. -/
@[expose] def InputEnabled : Prop :=
  ∀ src dest, sys.graph.Adj src dest → ∀ st msg,
    ∃ st' sent, sys.recv src dest st msg st' sent ∧ ∀ rm ∈ sent, sys.graph.Adj dest rm.1

end System

/-! #### Round-robin channel-draining scheduler -/

private noncomputable def deliverHeadStep {P S M : Type*} [DecidableEq P]
    (sys : System P S M) [DecidableRel sys.graph.Adj]
    (hinp : sys.InputEnabled) (S_aug : SnapGlobalState P S M)
    (src dest : P) (hadj : sys.graph.Adj src dest) :
    Option (SnapEvent P S M × SnapGlobalState P S M) :=
  match S_aug.chan src dest with
  | [] => none
  | .marker :: _ =>
    some (.recvMarker src dest, sys.stepSnap S_aug (.recvMarker src dest))
  | .app msg :: _ =>
    let h := hinp src dest hadj (S_aug.proc dest).appState msg
    let st' := h.choose
    let sent := h.choose_spec.choose
    let a := SnapEvent.app (.recv src dest msg st' sent)
    some (a, sys.stepSnap S_aug a)

private lemma deliverHeadStep_spec {P S M : Type*} [DecidableEq P]
    (sys : System P S M) [DecidableRel sys.graph.Adj]
    (hinp : sys.InputEnabled) {S_aug : SnapGlobalState P S M}
    {src dest : P} (hadj : sys.graph.Adj src dest) (hne : S_aug.chan src dest ≠ []) :
    ∃ a S_aug',
      deliverHeadStep sys hinp S_aug src dest hadj = some (a, S_aug') ∧
      sys.snapLts.Tr S_aug a S_aug' ∧
      a.deliversOn src dest := by
  unfold deliverHeadStep
  cases hch : S_aug.chan src dest with
  | nil => exact absurd hch hne
  | cons w ws =>
    cases w with
    | marker =>
      exact ⟨.recvMarker src dest, _, rfl, ⟨⟨hadj, by simp [hch]⟩, rfl⟩, ⟨rfl, rfl⟩⟩
    | app msg =>
      let h := hinp src dest hadj (S_aug.proc dest).appState msg
      have hspec := h.choose_spec.choose_spec
      refine ⟨_, _, rfl, ⟨⟨hadj, by simp [hch], hspec.1, hspec.2⟩, rfl⟩, ⟨rfl, rfl⟩⟩

private noncomputable def drainEdges {P S M : Type*} [DecidableEq P]
    (sys : System P S M) [DecidableRel sys.graph.Adj]
    (hinp : sys.InputEnabled) (S_aug : SnapGlobalState P S M) :
    List (P × P) → List (SnapEvent P S M) × SnapGlobalState P S M
  | [] => ([], S_aug)
  | (src, dest) :: es =>
    if hadj : sys.graph.Adj src dest then
      match deliverHeadStep sys hinp S_aug src dest hadj with
      | none => drainEdges sys hinp S_aug es
      | some (a, S₁) =>
        let r := drainEdges sys hinp S₁ es
        (a :: r.1, r.2)
    else
      drainEdges sys hinp S_aug es

private lemma drainEdges_spec {P S M : Type*} [DecidableEq P]
    (sys : System P S M) [DecidableRel sys.graph.Adj]
    (hinp : sys.InputEnabled) (S_aug : SnapGlobalState P S M) (es : List (P × P))
    (hwf : sys.WellFormedSnapChan S_aug) :
    let r := drainEdges sys hinp S_aug es
    sys.snapLts.MTr S_aug r.1 r.2 ∧
    sys.WellFormedSnapChan r.2 ∧
    ∀ src dest, (src, dest) ∈ es → S_aug.chan src dest ≠ [] →
      ∃ a ∈ r.1, a.deliversOn src dest := by
  induction es generalizing S_aug with
  | nil =>
    exact ⟨.refl, hwf, fun _ _ hm => False.elim (List.not_mem_nil hm)⟩
  | cons hd es ih =>
    rcases hd with ⟨u, v⟩
    dsimp only [drainEdges]
    by_cases hadj : sys.graph.Adj u v
    · simp only [hadj, ↓reduceDIte]
      cases hdel : deliverHeadStep sys hinp S_aug u v hadj with
      | none =>
        have hempty : S_aug.chan u v = [] := by
          by_contra hne
          obtain ⟨_, _, hsome, -⟩ := deliverHeadStep_spec sys hinp hadj hne
          simp [hdel] at hsome
        obtain ⟨hmtr, hwf', hmem⟩ := ih S_aug hwf
        refine ⟨hmtr, hwf', fun src dest hin hne => ?_⟩
        rcases List.mem_cons.mp hin with heq | hin'
        · cases heq; exact absurd hempty hne
        · exact hmem src dest hin' hne
      | some aS =>
        rcases aS with ⟨a₀, S₁⟩
        obtain ⟨a', S₁', hsome, htr₀, hdel₀⟩ := deliverHeadStep_spec sys hinp (S_aug := S_aug) hadj
          fun he => by simp [deliverHeadStep, he] at hdel
        simp only [hdel, Option.some.injEq, Prod.mk.injEq] at hsome
        obtain ⟨rfl, rfl⟩ := hsome
        have hwf₁ : sys.WellFormedSnapChan S₁ :=
          sys.wellFormedSnapChan_mTr (LTS.MTr.single sys.snapLts htr₀) hwf
        obtain ⟨hmtr, hwf₂, hmem⟩ := ih S₁ hwf₁
        refine ⟨.stepL htr₀ hmtr, hwf₂, fun src dest hin hne => ?_⟩
        rcases List.mem_cons.mp hin with heq | hin'
        · cases heq; exact ⟨a₀, List.mem_cons_self, hdel₀⟩
        by_cases hd : a₀.deliversOn src dest
        · exact ⟨a₀, List.mem_cons_self, hd⟩
        obtain ⟨extra, hex⟩ := sys.chan_append_of_not_deliversOn htr₀ hd
        obtain ⟨a₂, ha₂, hdel₂⟩ :=
          hmem src dest hin' (hex ▸ List.append_ne_nil_of_left_ne_nil hne extra)
        exact ⟨a₂, List.mem_cons_of_mem a₀ ha₂, hdel₂⟩
    · simp only [hadj, ↓reduceDIte]
      obtain ⟨hmtr, hwf', hmem⟩ := ih S_aug hwf
      refine ⟨hmtr, hwf', fun src dest hin hne => ?_⟩
      rcases List.mem_cons.mp hin with heq | hin'
      · rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
        exact absurd (hwf src dest hadj) hne
      · exact hmem src dest hin' hne

private noncomputable def fairPhase {P S M : Type*} [Fintype P] [DecidableEq P]
    (sys : System P S M) [DecidableRel sys.graph.Adj]
    (hinp : sys.InputEnabled) (S_aug : SnapGlobalState P S M) :
    List (SnapEvent P S M) × SnapGlobalState P S M :=
  let r := drainEdges sys hinp S_aug (Finset.univ : Finset (P × P)).toList
  if r.1.isEmpty then ([.stutter], r.2) else r

private lemma fairPhase_spec {P S M : Type*} [Fintype P] [DecidableEq P]
    (sys : System P S M) [DecidableRel sys.graph.Adj]
    (hinp : sys.InputEnabled) (S_aug : SnapGlobalState P S M)
    (hwf : sys.WellFormedSnapChan S_aug) :
    let r := fairPhase sys hinp S_aug
    sys.snapLts.MTr S_aug r.1 r.2 ∧
    0 < r.1.length ∧
    sys.WellFormedSnapChan r.2 ∧
    ∀ src dest, S_aug.chan src dest ≠ [] → ∃ a ∈ r.1, a.deliversOn src dest := by
  dsimp only [fairPhase]
  obtain ⟨hmtr, hwf', hmem⟩ :=
    drainEdges_spec sys hinp S_aug (Finset.univ : Finset (P × P)).toList hwf
  set r := drainEdges sys hinp S_aug (Finset.univ : Finset (P × P)).toList
  cases hemp : r.1.isEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact ⟨hmtr, List.length_pos_iff_ne_nil.mpr (List.isEmpty_eq_false_iff.mp hemp), hwf',
      fun src dest => hmem src dest (Finset.mem_toList.mpr (Finset.mem_univ (src, dest)))⟩
  · simp only [↓reduceIte, List.length_singleton, Nat.zero_lt_one, true_and]
    have hnil : r.1 = [] := List.isEmpty_iff.mp hemp
    rw [hnil] at hmtr hmem
    rw [← LTS.MTr.nil_eq sys.snapLts hmtr]
    refine ⟨LTS.MTr.single sys.snapLts ⟨trivial, rfl⟩, hwf, fun src dest hne => ?_⟩
    obtain ⟨_, ha, _⟩ := hmem src dest (Finset.mem_toList.mpr (Finset.mem_univ (src, dest))) hne
    cases ha

private noncomputable def fairSeq {P S M : Type*} [Fintype P] [DecidableEq P]
    (sys : System P S M) [DecidableRel sys.graph.Adj]
    (hinp : sys.InputEnabled) (S₀ : SnapGlobalState P S M) :
    ℕ → List (SnapEvent P S M) × SnapGlobalState P S M
  | 0 => ([], S₀)
  | k + 1 => fairPhase sys hinp (fairSeq sys hinp S₀ k).2

/-- **Existence of fair infinite executions (non-vacuity of `FairChannels`):** if `sys` is
input-enabled, every augmented state `S₀` with well-formed channels extends to an infinite execution
`(ss, xs)` of `sys.snapLts` starting at `S₀` that satisfies `FairChannels ss xs`. -/
theorem System.InputEnabled.exists_fair_snapOmegaExecution
    {P S M : Type*} [Finite P] [DecidableEq P]
    {sys : System P S M} [DecidableRel sys.graph.Adj] (hinp : sys.InputEnabled)
    {S₀ : SnapGlobalState P S M} (hwf₀ : sys.WellFormedSnapChan S₀) :
    ∃ ss xs, ss 0 = S₀ ∧ sys.snapLts.OmegaExecution ss xs ∧ FairChannels ss xs := by
  cases nonempty_fintype P
  have hwf_seq : ∀ k, sys.WellFormedSnapChan (fairSeq sys hinp S₀ k).2 := by
    intro k
    induction k with
    | zero => exact hwf₀
    | succ k ih => exact (fairPhase_spec sys hinp _ ih).2.2.1
  let ts : ωSequence (SnapGlobalState P S M) :=
    ωSequence.mk fun k => (fairSeq sys hinp S₀ k).2
  let xls : ωSequence (List (SnapEvent P S M)) :=
    (ωSequence.mk fun k => (fairSeq sys hinp S₀ k).1).tail
  have hseg : ∀ k, sys.snapLts.MTr (ts k) (xls k) (ts (k + 1)) ∧ 0 < (xls k).length ∧
      sys.WellFormedSnapChan (ts (k + 1)) ∧
      ∀ src dest, (ts k).chan src dest ≠ [] → ∃ a ∈ xls k, a.deliversOn src dest := fun k => by
    simpa [ts, xls, fairSeq] using fairPhase_spec sys hinp (fairSeq sys hinp S₀ k).2 (hwf_seq k)
  have hpos : ∀ k, 0 < (xls k).length := fun k => (hseg k).2.1
  have : Inhabited (SnapEvent P S M) := ⟨.stutter⟩
  obtain ⟨ss, hexec, hts⟩ := LTS.OmegaExecution.flatten_mTr (fun k => (hseg k).1) hpos
  refine ⟨ss, xls.flatten, ?_, hexec, ?_⟩
  · simpa [cumLen_zero, ts, fairSeq] using hts 0
  · intro src dest k hne
    by_contra! hnot
    have hk_le : k ≤ xls.cumLen k := (cumLen_strictMono hpos).id_le k
    obtain ⟨d, hd_eq⟩ := Nat.exists_eq_add_of_le hk_le
    obtain ⟨extra, hextra⟩ := sys.chan_prefix_until_delivery hexec (q := src) (p := dest)
      (k := k) (d := d) fun i _ => hnot (k + i) (Nat.le_add_right k i)
    have hne_cum : (ts k).chan src dest ≠ [] := by
      rw [← hts k, hd_eq, hextra]
      exact List.append_ne_nil_of_left_ne_nil hne extra
    obtain ⟨a, ha_mem, ha_del⟩ := (hseg k).2.2.2 src dest hne_cum
    obtain ⟨i, hi, heq⟩ := List.getElem_of_mem ha_mem
    have hget : xls.flatten (xls.cumLen k + i) = a := by
      rw [flatten_get_add xls hi hpos, heq]
    exact hnot (xls.cumLen k + i) (hk_le.trans (Nat.le_add_right _ _)) (hget ▸ ha_del)

end Cslib.Distributed.ChandyLamport
