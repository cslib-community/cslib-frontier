/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Computational.AuthenticatedKeyExchange.Experiment
import CslibFrontier.Tactic.PPT

/-!
# Authenticated key exchange: model rule table and structural properties

Checks for `CslibFrontier/Crypto/Computational/AuthenticatedKeyExchange/Experiment.lean`:

* **Rule table of `effectiveKey`** ([BonehShoup2023], §21.9, p. 888): covers `vulnerable` (corrupt,
  honest, exposed), `fresh` (honest, corrupt, unregistered), and `connected` (valid connection,
  `error`-forwarding, second connection, same role, wrong partner, non-fresh peer, running peer,
  self-connection, and out-of-range peer).
* **Non-default `Idealization.exposed` test** (Coordinator ruling 8): verifies through
  `challenger_deliver_of_running` that overriding `Idealization.exposed` changes a `.vulnerable`
  finishing reply from `none` (`error`) to `some key`.
* **Ruling 13 (`hasKeyedConnection_eq`)**: `Challenger.hasConnection` agrees with requiring an
  actual session key whenever no `.connected peer` instance holds `error` (`none`), and differs
  when one does.
* **Ruling 14 (`challenger_of_refused`, `view_of_mem_support`)**: disallowed queries return `[]`
  without modifying state, refusal depends only on `(honestIds, corruptIds, phases)`, and the
  updated visible view is determined by the prior view, query, and reply in both experiments.
* **State bounds (`ttpStep_ne_doubling`)**: no `Protocol` has a TTP that doubles its state on every
  call, although each call of that TTP is polynomial time.
-/

set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.AuthenticatedKeyExchangeModel

open Cslib Cslib.Probability Cslib.Crypto.AKE Turing.MultiTapeTM

/-! ### Fixtures for rule-table checks -/

private def alice : List Bool := [false]
private def bob : List Bool := [true]
private def eve : List Bool := [true, true]

/-- Minimal 2-bit-key protocol whose `step` outputs `bob` as partner and `[true, false]` as
session key. -/
private def sampleProtocol : Protocol where
  keyLength := fun _ => 2
  ttpInit := fun _ => pure []
  registerHonest := fun input => pure ⟨input.ttp, []⟩
  registerCorrupt := fun input => pure ⟨input.ttp, []⟩
  ttpStep := fun input => pure ⟨input.ttp, []⟩
  step := fun _ => pure ⟨[], [], .finished, bob, [true, false]⟩
  keyLength_polyTime := by ppt
  ttpInit_ppt := by ppt
  registerHonest_ppt := by ppt
  registerCorrupt_ppt := by ppt
  ttpStep_ppt := by ppt
  step_ppt := by ppt
  key_length := fun _ _ hout _ => by
    simp only [ProbComp.eval_pure, PMF.mem_support_pure_iff] at hout
    subst hout
    rfl
  stateBound := fun _ => 0
  stateBound_polyTime := by ppt
  registerHonest_ttp_length := fun _ _ hout => by simp_all
  registerCorrupt_ttp_length := fun _ _ hout => by simp_all
  ttpStep_ttp_length := fun _ _ hout => by simp_all
  step_state_length := fun _ _ hout => by simp_all

private def mkInst (u p : List Bool) (r : Role) (ph : Phase) (k : List Bool)
    (cls : Option Classification) (esk : Option (List Bool)) : Instance :=
  ⟨u, [], r, [], ph, p, k, cls, esk⟩

private def mkState (hs cs : List (List Bool)) (is : List Instance) : Challenger :=
  ⟨[], hs.map (⟨·, []⟩), cs, is, []⟩

private def aliceInst : Instance :=
  mkInst alice bob .left .finished [true, false] none none

private def bobFresh : Instance :=
  mkInst bob alice .right .finished [false, true] (some .fresh) (some [true, true])

/-! ### Rule table of `effectiveKey` -/

example :
    ProbComp.eval
        (effectiveKey sampleProtocol 0 .vulnerable false aliceInst (mkState [alice] [bob] [])) =
      PMF.pure (some [true, false]) := by
  simp [effectiveKey, mkState, aliceInst, mkInst, Challenger.isCorrupt, alice, bob]

example :
    ProbComp.eval
        (effectiveKey sampleProtocol 0 .vulnerable false aliceInst (mkState [alice, bob] [] [])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, mkInst, Challenger.isCorrupt]

example :
    ProbComp.eval
        (effectiveKey sampleProtocol 0 .vulnerable true aliceInst (mkState [alice, bob] [] [])) =
      PMF.pure (some [true, false]) := by
  simp [effectiveKey, mkState, aliceInst, mkInst]

example :
    ProbComp.eval
        (effectiveKey sampleProtocol 0 .fresh false aliceInst (mkState [alice, bob] [] [])) =
      (BitString.uniformList 2).map some := by
  simp [effectiveKey, mkState, aliceInst, mkInst, Challenger.isRegistered, Challenger.isHonest,
    Challenger.findHonest, Challenger.isCorrupt, alice, bob, sampleProtocol]

example :
    ProbComp.eval
        (effectiveKey sampleProtocol 0 .fresh false aliceInst (mkState [alice] [bob] [])) =
      (BitString.uniformList 2).map some := by
  simp [effectiveKey, mkState, aliceInst, mkInst, Challenger.isRegistered, Challenger.isHonest,
    Challenger.findHonest, Challenger.isCorrupt, alice, bob, sampleProtocol]

example :
    ProbComp.eval
        (effectiveKey sampleProtocol 0 .fresh false aliceInst (mkState [alice] [] [])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, mkInst, Challenger.isRegistered, Challenger.isHonest,
    Challenger.findHonest, Challenger.isCorrupt, alice, bob]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob] [] [bobFresh])) =
      PMF.pure (some [true, true]) := by
  simp [effectiveKey, mkState, aliceInst, bobFresh, Instance.compatible, Challenger.hasConnection,
    mkInst, alice, bob]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob] []
          [mkInst bob alice .right .finished [false, true] (some .fresh) none])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, Instance.compatible, Challenger.hasConnection, mkInst,
    alice, bob]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob] [] [bobFresh,
          mkInst alice bob .left .finished [] (some (.connected 0)) (some [true, true])])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, bobFresh, Instance.compatible, Challenger.hasConnection,
    mkInst]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob] []
          [mkInst bob alice .left .finished [false, true] (some .fresh) (some [true, true])])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, Instance.compatible, mkInst]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob, eve] []
          [mkInst bob eve .right .finished [false, true] (some .fresh) (some [true, true])])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, Instance.compatible, mkInst, alice, eve]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob] []
          [mkInst bob alice .right .finished [false, true] (some .vulnerable)
            (some [true, true])])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, mkInst]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob] []
          [mkInst bob alice .right .running [false, true] (some .fresh) (some [true, true])])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, Instance.compatible, mkInst]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 0) false aliceInst
        (mkState [alice, bob] [] [aliceInst])) =
      PMF.pure none := by
  simp [effectiveKey, mkState, aliceInst, Instance.compatible, mkInst]

example :
    ProbComp.eval (effectiveKey sampleProtocol 0 (.connected 1) false aliceInst
        (mkState [alice, bob] [] [bobFresh])) =
      PMF.pure none := by
  simp [effectiveKey, mkState]

/-! ### Coordinator ruling 8: `Idealization.exposed` changes the reply -/

private def sRunning : Challenger :=
  mkState [alice, bob] [] [mkInst alice bob .left .running [] none none]

private def idlDefault : Idealization where
  partner := fun _ => .vulnerable

private def idlExposed : Idealization where
  partner := fun _ => .vulnerable
  exposed := fun _ i => i == 0

/-- Under default `exposed` (`fun _ _ => false`), `.deliver` on a `.vulnerable` instance with an
honest partner returns the `error` (`none`) reply. -/
theorem eval_deliver_exposed_false :
    (ProbComp.eval (challenger sampleProtocol 0 (some idlDefault)
        (.deliver, encPair encBits encBits ([], [])) sRunning)).map Prod.fst =
      PMF.pure (encDeliverReply ⟨[], .finished, bob, none⟩) := by
  rw [challenger_deliver_of_running _ _ _ _ _ (mkInst alice bob .left .running [] none none)
    (by rw [unframe_encPair_encBits]; rfl) rfl]
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
  simp [sRunning, mkState, mkInst, sampleProtocol, idlDefault, effectiveKey, Challenger.isCorrupt]

/-- Setting `Idealization.exposed` to a non-default predicate changes the returned `DeliverReply`
from `none` (`error`) to `some [true, false]`. -/
theorem eval_deliver_exposed_true :
    (ProbComp.eval (challenger sampleProtocol 0 (some idlExposed)
        (.deliver, encPair encBits encBits ([], [])) sRunning)).map Prod.fst =
      PMF.pure (encDeliverReply ⟨[], .finished, bob, some [true, false]⟩) := by
  rw [challenger_deliver_of_running _ _ _ _ _ (mkInst alice bob .left .running [] none none)
    (by rw [unframe_encPair_encBits]; rfl) rfl]
  rw [unframe_encPair_encBits, dropFrame_encPair_encBits]
  simp [sRunning, mkState, mkInst, sampleProtocol, idlExposed, effectiveKey]

example :
    (ProbComp.eval (challenger sampleProtocol 0 (some idlExposed)
        (.deliver, encPair encBits encBits ([], [])) sRunning)).map Prod.fst ≠
      (ProbComp.eval (challenger sampleProtocol 0 (some idlDefault)
        (.deliver, encPair encBits encBits ([], [])) sRunning)).map Prod.fst := by
  rw [eval_deliver_exposed_true, eval_deliver_exposed_false]
  intro h
  have hmem : encDeliverReply ⟨[], .finished, bob, some [true, false]⟩ ∈
      (PMF.pure (encDeliverReply ⟨[], .finished, bob, none⟩)).support := by
    rw [← h]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl
  rw [PMF.mem_support_pure_iff] at hmem
  injection encDeliverReply.injective hmem with _ _ _ hopt
  cases hopt

/-! ### Ruling 13: keyed-connection vs classification-only reading -/

/-- Alternative reading of "previously connected to `peer`": counts only `.connected peer`
instances whose recorded `effectiveKey` is not `none` (`error`). -/
def hasKeyedConnection (s : Challenger) (peer : ℕ) : Bool :=
  s.instances.any fun inst =>
    inst.classification == some (.connected peer) && inst.effectiveKey.isSome

/-- `hasKeyedConnection` and `Challenger.hasConnection` agree in every state where no
`.connected peer` instance holds `error` (`effectiveKey = none`). -/
theorem hasKeyedConnection_eq (s : Challenger) (peer : ℕ)
    (h : ∀ inst ∈ s.instances,
      inst.classification = some (.connected peer) → inst.effectiveKey.isSome) :
    hasKeyedConnection s peer = s.hasConnection peer := by
  simp only [hasKeyedConnection, Challenger.hasConnection]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨inst, hmem, hcls, _⟩
    exact ⟨inst, hmem, hcls⟩
  · rintro ⟨inst, hmem, hcls⟩
    exact ⟨inst, hmem, hcls, h inst hmem hcls⟩

example :
    let s := mkState [alice] []
      [mkInst alice bob .left .finished [] (some (.connected 0)) none]
    hasKeyedConnection s 0 = false ∧ s.hasConnection 0 = true := by
  simp [mkState, mkInst, hasKeyedConnection, Challenger.hasConnection]

/-! ### Ruling 14: refusal and visible state view -/

/-- The portion of `Challenger` state observable through query refusal and query responses: the
registered honest and corrupt identities (in order) and each instance's phase. -/
structure VisibleView where
  /-- Registered honest user identities. -/
  honestIds : List (List Bool)
  /-- Registered corrupt user identities. -/
  corruptIds : List (List Bool)
  /-- Phase of each created instance. -/
  phases : List Phase
  deriving DecidableEq

/-- Project the challenger state to its visible view. -/
def view (s : Challenger) : VisibleView :=
  ⟨s.honest.map (·.id), s.corrupt, s.instances.map (·.phase)⟩

/-- Query refusal predicate depending only on `VisibleView` and the query. -/
def refused (v : VisibleView) (q : Op × List Bool) : Bool :=
  match q.1 with
  | .registerHonest => v.honestIds.contains q.2 || v.corruptIds.contains q.2
  | .registerCorrupt => v.honestIds.contains (unframe q.2)
  | .init _ => !v.honestIds.contains q.2
  | .deliver =>
    match v.phases[(unframe q.2).length]? with
    | none => true
    | some p => p != .running
  | .deliverTTP => false

private theorem isHonest_iff_mem_view (s : Challenger) (u : List Bool) :
    s.isHonest u = (view s).honestIds.contains u := by
  simp only [Challenger.isHonest, Challenger.findHonest, view]
  suffices ∀ hs : List HonestUser,
      (hs.find? (fun x => x.id == u)).isSome = (hs.map (·.id)).contains u from
    this s.honest
  intro hs
  induction hs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x.id = u
    · simp [hx]
    · have h1 : (x.id == u) = false := beq_false_of_ne hx
      have h2 : (u == x.id) = false := beq_false_of_ne (Ne.symm hx)
      simp only [List.find?_cons, List.map_cons, List.contains_cons, h1, h2, Bool.false_or, ih]

/-- Extract the resulting instance phase from an encoded `DeliverReply` (returning `.running` on
non-reply words). -/
noncomputable def replyPhase (reply : List Bool) : Phase :=
  by classical exact
    if h : ∃ r : DeliverReply, encDeliverReply r = reply then h.choose.phase else .running

@[simp]
private theorem replyPhase_encDeliverReply (r : DeliverReply) :
    replyPhase (encDeliverReply r) = r.phase := by
  classical
  dsimp only [replyPhase]
  split_ifs with h
  · exact congrArg DeliverReply.phase (encDeliverReply.injective h.choose_spec)
  · exact False.elim (h ⟨r, rfl⟩)

/-- Updated `VisibleView` as a pure function of the prior view, the query, and the reply. -/
noncomputable def nextView (v : VisibleView) (q : Op × List Bool) (reply : List Bool) :
    VisibleView :=
  if refused v q then v
  else match q.1 with
  | .registerHonest => ⟨v.honestIds ++ [q.2], v.corruptIds, v.phases⟩
  | .registerCorrupt => ⟨v.honestIds, v.corruptIds ++ [unframe q.2], v.phases⟩
  | .init _ => ⟨v.honestIds, v.corruptIds, v.phases ++ [.running]⟩
  | .deliver => ⟨v.honestIds, v.corruptIds, v.phases.set (unframe q.2).length (replyPhase reply)⟩
  | .deliverTTP => v

/-- Every refused query returns `[]` and leaves the challenger state unchanged in both
experiments. -/
theorem challenger_of_refused (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (q : Op × List Bool) (s : Challenger) (href : refused (view s) q = true) :
    challenger P n ideal q s = pure ([], s) := by
  obtain ⟨op, req⟩ := q
  cases op with
  | registerHonest =>
    rw [challenger_registerHonest]
    have hreg : s.isRegistered req = true := by
      simpa [Challenger.isRegistered, Challenger.isCorrupt, view, refused,
        isHonest_iff_mem_view] using href
    simp [hreg]
  | registerCorrupt =>
    rw [challenger_registerCorrupt]
    have hhon : s.isHonest (unframe req) = true := by
      simpa [refused, isHonest_iff_mem_view] using href
    simp [hhon]
  | init role =>
    rw [challenger_init]
    have hnone : s.findHonest req = none := by
      have hnot : s.isHonest req = false := by
        simpa [refused, isHonest_iff_mem_view] using href
      simpa [Challenger.isHonest, Option.isSome_eq_false_iff] using hnot
    simp [hnone]
  | deliverTTP => simp [refused] at href
  | deliver =>
    simp only [refused, view, List.getElem?_map] at href
    cases hget : s.instances[(unframe req).length]? with
    | none => exact challenger_deliver_of_getElem?_eq_none P n ideal req s hget
    | some inst =>
      rw [hget, Option.map_some] at href
      have hphase : inst.phase ≠ .running := by simpa using href
      exact challenger_deliver_of_not_running P n ideal req s inst hget hphase

/-- The visible view after any supported transition is determined by `view s`, `q`, and the reply
in both experiments. -/
theorem view_of_mem_support (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (q : Op × List Bool) (s : Challenger) {res : List Bool × Challenger}
    (hres : res ∈ (ProbComp.eval (challenger P n ideal q s)).support) :
    view res.2 = nextView (view s) q res.1 := by
  by_cases href : refused (view s) q = true
  · rw [challenger_of_refused P n ideal q s href, ProbComp.eval_pure, PMF.mem_support_pure_iff]
      at hres
    subst hres
    simp [nextView, href]
  · have href' : refused (view s) q = false := Bool.eq_false_iff.mpr href
    obtain ⟨op, req⟩ := q
    simp only [nextView, href', Bool.false_eq_true, ↓reduceIte]
    cases op with
    | registerHonest =>
      rw [challenger_registerHonest] at hres
      have hreg : s.isRegistered req = false := by
        have hfalse := href'
        simp only [refused, view, Bool.or_eq_false_iff] at hfalse
        rw [Challenger.isRegistered, Challenger.isCorrupt, isHonest_iff_mem_view]
        exact Bool.or_eq_false_iff.mpr ⟨hfalse.1, hfalse.2⟩
      simp only [hreg, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hres
      obtain ⟨out, _, rfl⟩ := hres
      simp [view]
    | registerCorrupt =>
      rw [challenger_registerCorrupt] at hres
      have hhon : s.isHonest (unframe req) = false := by
        simpa [refused, isHonest_iff_mem_view] using href'
      simp only [hhon, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
        PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hres
      obtain ⟨out, _, rfl⟩ := hres
      simp [view]
    | init role =>
      rw [challenger_init] at hres
      have hhon : s.isHonest req = true := by
        simpa [refused, isHonest_iff_mem_view] using href'
      cases hfind : s.findHonest req with
      | none => simp [Challenger.isHonest, hfind] at hhon
      | some u =>
        simp only [hfind, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hres
        subst hres
        simp [view]
    | deliverTTP =>
      rw [challenger_deliverTTP] at hres
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff] at hres
      obtain ⟨out, _, rfl⟩ := hres
      simp [view]
    | deliver =>
      simp only [refused, view, List.getElem?_map] at href'
      cases hget : s.instances[(unframe req).length]? with
      | none => simp [hget] at href'
      | some inst =>
        rw [hget, Option.map_some] at href'
        have hrun : inst.phase = .running := by simpa using href'
        rw [challenger_deliver_of_running P n ideal req s inst hget hrun] at hres
        simp only [ProbComp.eval_bind, PMF.mem_support_bind_iff] at hres
        obtain ⟨out, _, hout⟩ := hres
        by_cases hfin : out.phase = .finished
        · cases ideal with
          | none =>
            simp only [hfin, ↓reduceIte, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hout
            subst hout
            simp only [view, List.map_set, replyPhase_encDeliverReply]
          | some idl =>
            simp only [hfin, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure,
              PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hout
            obtain ⟨esk, _, rfl⟩ := hout
            simp only [view, List.map_set, replyPhase_encDeliverReply, List.set_set]
        · simp only [hfin, ↓reduceIte, ProbComp.eval_pure, PMF.mem_support_pure_iff] at hout
          subst hout
          simp only [view, List.map_set, replyPhase_encDeliverReply]

/-! ### The state bounds exclude a state-doubling TTP -/

/-- No `Protocol` has the online TTP step that doubles its state on every call (`s ↦ true :: (s ++
s)`, replying with `s`), although each such call is polynomial time in its input: on a state longer
than `stateBound 0`, it grows by more than the bound allows. -/
theorem ttpStep_ne_doubling (P : Protocol) :
    P.ttpStep ≠ fun input => pure ⟨true :: (input.ttp ++ input.ttp), input.ttp⟩ := by
  intro h
  let s := List.replicate (P.stateBound 0 + 1) true
  have hgrow := P.ttpStep_ttp_length ⟨0, s, [], []⟩ ⟨true :: (s ++ s), s⟩
    (by rw [h]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  simp only [List.length_cons, List.length_append, s, List.length_replicate] at hgrow
  omega

end CslibFrontierTests.Crypto.AuthenticatedKeyExchangeModel
