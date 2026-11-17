/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.AuthenticatedKeyExchange.Protocol
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Inductive
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair.Projections
public import CslibFrontier.Languages.Probabilistic.BitString

/-!
# Authenticated key exchange: challenger and attack experiments

Communication log, partner functions, challenger state, effective session keys, and the unified
query handler `challenger` for Experiments 0 and 1 ([BonehShoup2023], §21.9, pp. 886–888).

## Model conventions and differences from [BonehShoup2023]

* **(a)** Strict PPT word algorithms (`IsPPTOn`/`IsOraclePPT`/`ComputableInPolyTime`), with
  the size bound of `Protocol` standing in for the book's efficient TTP interface and
  poly-bounded instance configurations (compared in the module defining `Protocol`).
* **(b)** Joint honest registration (`registerHonest` runs in one step, unlogged).
* **(c)** Stepwise corrupt registration (one TTP step and `.corruptUser` log entry per query).
* **(d)** Refused disallowed queries return `[]` with unchanged state. Besides the book's
  disallowed queries, the challenger refuses a query that would hand a protocol algorithm a user
  identity or message longer than `P.sizeBound n` (`Protocol.TooLong`). Refusal and visible view
  depend only on `(honestIds, corruptIds, phases)` and the lengths of the request's words
  (`challenger_of_refused`, `view_of_mem_support`; game-level equivalence is unproved).
* **(e)** Index-named instances (`(unframe req).length`); `.init` omits `user`.
* **(f)** `PartnerFunction` receives security parameter `n`.
* **(g)** Log-then-classify order: `.deliver` logs before `idl.partner` runs.
* **(h)** Explicit `error` outcome (`none : Option (List Bool)`, distinct from every key).
* **(i)** Word-oracle adversaries (`IsOraclePPT`) and `ℝ≥0` advantage (`Game.advantage`).
* **(j)** No correctness clause (`abortProtocol` is statically secure).
* **(k)** Fresh finishing replies match Experiment 0 (checked for one query in
  `eval_challenger_deliver_fresh_reply`; whole-game fresh test unproved).
* **(l)** Non-degenerate key length in negative test (`1 ≤ n`; at `n = 0`, `𝒦` is a singleton).

`Challenger.hasConnection` counts any `.connected peer` classification; `hasKeyedConnection_eq`
shows agreement with requiring a key except after `error` (game equivalence unproved).
`Idealization.exposed` hooks PFS and HSM extensions without changing `challenger`.

## Main definitions and results

* `LogEntry`, `encLog`, `Classification`, `PartnerFunction`, `Challenger`, `Instance.compatible`,
  `Idealization`, `DeliverReply`, `Op`, `effectiveKey`, `challenger`.
* `encDeliverReply_some` and `challenger_*` query equations.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], §21.9,
  pp. 886–888.
-/

public section

namespace Cslib.Crypto.AKE

open Probability Turing.MultiTapeTM

/-- Entry recorded in the AKE communication log ([BonehShoup2023], §21.9, p. 887). -/
inductive LogEntry where
  /-- Corrupt user identity registered with the TTP. -/
  | corruptUser (user : List Bool)
  /-- Initialization of instance `inst` with `role`. Omits `user` (`I.user.id`), matching the
  literal `(init, I, I.role)` entry ([BonehShoup2023], p. 887) so partner functions receive minimal
  information; any partner function here lifts to one given user IDs. -/
  | init (inst : ℕ) (role : Role)
  /-- Accepted `.deliver` step on instance `inst`; omits partner ID and session key. -/
  | deliver (inst : ℕ) (msgIn msgOut : List Bool) (phase : Phase)
  /-- Accepted `.deliverTTP` message pair. -/
  | deliverTTP (msgIn msgOut : List Bool)
  deriving DecidableEq, Repr

/-- Framing encoding of `LogEntry` via `enc_inductive`. -/
enc_inductive encLogEntry : LogEntry where
  | corruptUser : encBits
  | init : encUnary, (encFinEnum Role)
  | deliver : encUnary, encBits, encBits, (encFinEnum Phase)
  | deliverTTP : encBits, encBits

attribute [nolint defsWithUnderscore] encLogEntry_toSum encLogEntry_elim

/-- Encoding of a communication log as a list of `LogEntry` values. -/
abbrev encLog : List LogEntry ↪ List Bool := encList encLogEntry

/-- Classification returned by a partner function ([BonehShoup2023], §21.9, pp. 887–888). -/
inductive Classification where
  /-- Return `I.sk` when `I.pid` is corrupt (or exposed), else `error` (`none`). -/
  | vulnerable
  /-- Draw a uniform key from `𝒦` when `I.pid` is registered, else `error`. -/
  | fresh
  /-- Copy `J.effectiveKey` when `peer` (`J`) is compatible, fresh, and unconnected. -/
  | connected (peer : ℕ)
  deriving DecidableEq, Repr

/-- Framing encoding of `Classification` via `enc_inductive`. -/
enc_inductive encClassification : Classification where
  | vulnerable
  | fresh
  | connected : encUnary

attribute [nolint defsWithUnderscore] encClassification_toSum encClassification_elim

/-- Partner function taking security parameter `n` and communication log. -/
abbrev PartnerFunction : Type := ℕ → List LogEntry → Classification

/-- Honest user registered with the TTP (`U.id`, `U.ltk`). -/
structure HonestUser where
  /-- Bit-string identity chosen at honest registration. -/
  id : List Bool
  /-- Long-term secret key produced by `Protocol.registerHonest`. -/
  longTermKey : List Bool
  deriving DecidableEq, Repr

/-- Execution state of an honest user session instance ([BonehShoup2023], §21.9, p. 886). -/
structure Instance where
  /-- Identity of the honest user owning the instance. -/
  user : List Bool
  /-- Long-term secret key of the owning user. -/
  longTermKey : List Bool
  /-- Role assigned at initialization. -/
  role : Role
  /-- Current local state word. -/
  state : List Bool
  /-- Current execution status (`running`, `aborted`, or `finished`). -/
  phase : Phase
  /-- Partner identity, read when `phase = .finished`. -/
  partner : List Bool
  /-- Session key, read when `phase = .finished`. -/
  key : List Bool
  /-- Partner-function classification recorded in Experiment 1 (`none` until finished). -/
  classification : Option Classification := none
  /-- Effective session key assigned when finishing in Experiment 1 (`none` if `error`/unset). -/
  effectiveKey : Option (List Bool) := none
  deriving DecidableEq, Repr

/-- Finished instances `I`, `J` are compatible when each names the other as partner and they
have opposite roles ([BonehShoup2023], §21.9, p. 888). -/
@[expose]
def Instance.compatible (I J : Instance) : Prop :=
  I.phase = .finished ∧ J.phase = .finished ∧ I.partner = J.user ∧ J.partner = I.user ∧
    I.role ≠ J.role

instance (I J : Instance) : Decidable (I.compatible J) :=
  inferInstanceAs (Decidable
    (I.phase = .finished ∧ J.phase = .finished ∧ I.partner = J.user ∧ J.partner = I.user ∧
      I.role ≠ J.role))

/-- Mutable state of the AKE challenger ([BonehShoup2023], §21.9, pp. 886–888). -/
structure Challenger where
  /-- Internal state word of the TTP. -/
  ttp : List Bool
  /-- Registered honest users. -/
  honest : List HonestUser := []
  /-- Corrupt user identities (repeats allowed from repeated queries). -/
  corrupt : List (List Bool) := []
  /-- Honest user instances in creation order (`0, 1, …`). -/
  instances : List Instance := []
  /-- Communication log passed to the partner function in Experiment 1. -/
  log : List LogEntry := []
  deriving DecidableEq, Repr

/-- Look up an honest user record by identity. -/
@[expose] def Challenger.findHonest (s : Challenger) (user : List Bool) : Option HonestUser :=
  s.honest.find? (·.id == user)

/-- Whether `user` is registered as an honest user. -/
@[expose] def Challenger.isHonest (s : Challenger) (user : List Bool) : Bool :=
  (s.findHonest user).isSome

/-- Whether `user` has been registered as a corrupt user. -/
@[expose] def Challenger.isCorrupt (s : Challenger) (user : List Bool) : Bool :=
  s.corrupt.contains user

/-- Whether `user` has been registered either honestly or corruptly. -/
@[expose] def Challenger.isRegistered (s : Challenger) (user : List Bool) : Bool :=
  s.isHonest user || s.isCorrupt user

/-- Whether any instance in `s` has already been classified as `.connected peer`.
Implements the first reading of "no other user instance previously connected to it"
([BonehShoup2023], p. 888): any `.connected peer` classification counts, even when that
instance received `error` (`effectiveKey = none`). See `hasKeyedConnection_eq`. -/
@[expose] def Challenger.hasConnection (s : Challenger) (peer : ℕ) : Bool :=
  s.instances.any (·.classification == some (.connected peer))

/-- Idealization hook for Experiment 1 ([BonehShoup2023], §21.9, pp. 887–893). Static security
(`Protocol.StaticallySecure`) leaves `exposed` at its default (`fun _ _ => false`); PFS and HSM
security (Definitions 21.2 and 21.3) supply nontrivial `exposed` predicates for `.vulnerable`
instances without changing `challenger`. -/
structure Idealization where
  /-- Partner function classifying each finishing instance from the communication log. -/
  partner : List LogEntry → Classification
  /-- Extra exposure condition making a `.vulnerable` instance `i` in state `s` reveal `I.key`
  rather than `error` (`none`). Defaults to `false`. -/
  exposed : Challenger → ℕ → Bool := fun _ _ => false

/-- Reply returned by an accepted `.deliver` query on a running instance. -/
structure DeliverReply where
  /-- Outgoing protocol message `m_out`. -/
  message : List Bool
  /-- Resulting instance phase. -/
  phase : Phase
  /-- Partner identity (`[]` unless `phase = .finished`). -/
  partner : List Bool
  /-- Session key or effective session key (`none` denotes `error` or non-finished phase). -/
  key : Option (List Bool)
  deriving DecidableEq, Repr

/-- Delivery reply wire format: framed message, phase and partner, followed by the
silent optional key (`none` emits no suffix; `some key` emits `true :: key`). This preserves
the protocol's pre-adoption words: an error reply is the prefix of a successful reply, as used
by the adversary's reply-prefix tests. Canonical tagged options are not used at this boundary.
`enc_structure` generates the constructor and projection certificates for this same format. -/
enc_structure encDeliverReply : DeliverReply where
  message : encBits, phase : (encFinEnum Phase), partner : encBits, key : (encSilentOption encBits)

/-- Oracle query tags exposed to an active AKE adversary ([BonehShoup2023], §21.9, pp. 886–887). -/
inductive Op where
  /-- Register an honest user (`req = user`). -/ | registerHonest
  /-- Register a corrupt user (`req = encPair encBits encBits (user, msg)`). -/ | registerCorrupt
  /-- Initialize an honest instance with `role` (`req = user`). -/ | init (role : Role)
  /-- Deliver a protocol message (`req = encPair encBits encBits (idx, msg)`). -/ | deliver
  /-- Deliver an online message to the TTP (`req = msg`). -/ | deliverTTP
  deriving DecidableEq, Repr

instance : FinEnum Op :=
  FinEnum.ofList [.registerHonest, .registerCorrupt, .init .left, .init .right,
    .deliver, .deliverTTP] (by rintro (_ | _ | (_ | _) | _ | _) <;> decide)

/-- Effective session key distribution for a finishing instance `I` under classification `c` and
exposure flag `exposed` in state `s` ([BonehShoup2023], §21.9, p. 888). Returns `none` for
`error`. -/
@[expose]
noncomputable def effectiveKey (P : Protocol) (n : ℕ) (c : Classification) (exposed : Bool)
    (I : Instance) (s : Challenger) : ProbComp (Option (List Bool)) :=
  match c with
  | .vulnerable => if s.isCorrupt I.partner || exposed then pure (some I.key) else pure none
  | .fresh =>
    if s.isRegistered I.partner then some <$> BitString.sampleList (P.keyLength n) else pure none
  | .connected peer =>
    match s.instances[peer]? with
    | some J =>
      if I.compatible J ∧ J.classification = some .fresh ∧ s.hasConnection peer = false then
        pure J.effectiveKey
      else pure none
    | none => pure none

/-- Query handler for Experiment 0 (`ideal = none`) and Experiment 1 (`ideal = some idl`)
([BonehShoup2023], §21.9, pp. 886–888). Disallowed queries, and queries that would hand a protocol
algorithm a word longer than `P.sizeBound n` (`Protocol.TooLong`), return `[]` with unchanged
state; refusal depends only on `(honestIds, corruptIds, instancePhases)` and the lengths of the
request's words (`challenger_of_refused`, `view_of_mem_support`). Clients should rewrite with
`challenger_*` equations. -/
noncomputable def challenger (P : Protocol) (n : ℕ) (ideal : Option Idealization) :
    Op × List Bool → StateT Challenger ProbComp (List Bool) :=
  fun (op, req) s =>
    match op with
    | .registerHonest =>
      if s.isRegistered req ∨ P.TooLong n req then pure ([], s)
      else do
        let out ← P.registerHonest ⟨n, s.ttp, req, []⟩
        pure ([], { s with ttp := out.ttp, honest := s.honest ++ [⟨req, out.output⟩] })
    | .registerCorrupt =>
      let user := unframe req
      if s.isHonest user ∨ P.TooLong n user ∨ P.TooLong n (dropFrame req) then pure ([], s)
      else do
        let out ← P.registerCorrupt ⟨n, s.ttp, user, dropFrame req⟩
        pure (out.output,
          ⟨out.ttp, s.honest, s.corrupt ++ [user], s.instances, s.log ++ [.corruptUser user]⟩)
    | .init role =>
      match s.findHonest req with
      | none => pure ([], s)
      | some u =>
        let inst : Instance := ⟨u.id, u.longTermKey, role, [], .running, [], [], none, none⟩
        pure ([], ⟨s.ttp, s.honest, s.corrupt, s.instances ++ [inst],
          s.log ++ [.init s.instances.length role]⟩)
    | .deliverTTP =>
      if P.TooLong n req then pure ([], s)
      else do
        let out ← P.ttpStep ⟨n, s.ttp, [], req⟩
        pure (out.output, { s with ttp := out.ttp, log := s.log ++ [.deliverTTP req out.output] })
    | .deliver =>
      let i := (unframe req).length
      let msg := dropFrame req
      match s.instances[i]? with
      | none => pure ([], s)
      | some inst =>
        if inst.phase ≠ .running ∨ P.TooLong n msg then pure ([], s)
        else do
          let out ← P.step ⟨n, inst.user, inst.longTermKey, inst.role, inst.state, msg⟩
          let stepInst : Instance := ⟨inst.user, inst.longTermKey, inst.role, out.state,
            out.phase, out.partner, out.key, inst.classification, inst.effectiveKey⟩
          let s' : Challenger := ⟨s.ttp, s.honest, s.corrupt, s.instances.set i stepInst,
            s.log ++ [.deliver i msg out.message out.phase]⟩
          if out.phase = .finished then
            match ideal with
            | none => pure (encDeliverReply ⟨out.message, .finished, out.partner, some out.key⟩, s')
            | some idl =>
              let c := idl.partner s'.log
              let esk ← effectiveKey P n c (idl.exposed s' i) stepInst s'
              let finInst : Instance := ⟨inst.user, inst.longTermKey, inst.role, out.state,
                out.phase, out.partner, out.key, some c, esk⟩
              pure (encDeliverReply ⟨out.message, .finished, out.partner, esk⟩,
                { s' with instances := s'.instances.set i finInst })
          else
            pure (encDeliverReply ⟨out.message, out.phase, [], none⟩, s')

/-- Encoded `some key` reply equals `none` (`error`) reply followed by `true :: key`. -/
theorem encDeliverReply_some (message : List Bool) (phase : Phase) (partner key : List Bool) :
    encDeliverReply ⟨message, phase, partner, some key⟩ =
      encDeliverReply ⟨message, phase, partner, none⟩ ++ true :: key := by
  simp [encDeliverReply_apply]

/-- Query equation for `.registerHonest`. -/
theorem challenger_registerHonest (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (user : List Bool) (s : Challenger) :
    challenger P n ideal (.registerHonest, user) s =
      (if s.isRegistered user ∨ P.TooLong n user then pure ([], s)
      else do
        let out ← P.registerHonest ⟨n, s.ttp, user, []⟩
        pure ([], { s with ttp := out.ttp, honest := s.honest ++ [⟨user, out.output⟩] })) := by
  rfl

/-- Query equation for `.registerCorrupt`. -/
theorem challenger_registerCorrupt (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (req : List Bool) (s : Challenger) :
    challenger P n ideal (.registerCorrupt, req) s =
      (if s.isHonest (unframe req) ∨ P.TooLong n (unframe req) ∨ P.TooLong n (dropFrame req) then
        pure ([], s)
      else do
        let out ← P.registerCorrupt ⟨n, s.ttp, unframe req, dropFrame req⟩
        pure (out.output, ⟨out.ttp, s.honest, s.corrupt ++ [unframe req], s.instances,
          s.log ++ [.corruptUser (unframe req)]⟩)) := by
  rfl

/-- Query equation for `.init`. -/
theorem challenger_init (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (role : Role) (user : List Bool) (s : Challenger) :
    challenger P n ideal (.init role, user) s = (match s.findHonest user with
      | none => pure ([], s)
      | some u =>
        let inst : Instance := ⟨u.id, u.longTermKey, role, [], .running, [], [], none, none⟩
        pure ([], ⟨s.ttp, s.honest, s.corrupt, s.instances ++ [inst],
          s.log ++ [.init s.instances.length role]⟩)) := by
  rfl

/-- Query equation for `.deliverTTP`. -/
theorem challenger_deliverTTP (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (msg : List Bool) (s : Challenger) :
    challenger P n ideal (.deliverTTP, msg) s = (if P.TooLong n msg then pure ([], s)
      else do
        let out ← P.ttpStep ⟨n, s.ttp, [], msg⟩
        pure (out.output,
          { s with ttp := out.ttp, log := s.log ++ [.deliverTTP msg out.output] })) := by
  rfl

/-- Query equation for `.deliver` targeting a non-existent instance index. -/
theorem challenger_deliver_of_getElem?_eq_none (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (req : List Bool) (s : Challenger) (h : s.instances[(unframe req).length]? = none) :
    challenger P n ideal (.deliver, req) s = pure ([], s) := by
  simp only [challenger, h]

/-- Query equation for `.deliver` targeting a non-running instance. -/
theorem challenger_deliver_of_not_running (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (req : List Bool) (s : Challenger) (inst : Instance)
    (h : s.instances[(unframe req).length]? = some inst) (hphase : inst.phase ≠ .running) :
    challenger P n ideal (.deliver, req) s = pure ([], s) := by
  simp only [challenger, h, ne_eq, hphase, not_false_eq_true, true_or, ↓reduceIte]

/-- Query equation for `.deliver` with a message longer than `P.sizeBound n`. -/
theorem challenger_deliver_of_tooLong (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (req : List Bool) (s : Challenger) (hlong : P.TooLong n (dropFrame req)) :
    challenger P n ideal (.deliver, req) s = pure ([], s) := by
  cases h : s.instances[(unframe req).length]? <;> simp [challenger, h, hlong]

/-- Query equation for `.deliver` of a message of at most `P.sizeBound n` bits to a running
instance. -/
theorem challenger_deliver_of_running (P : Protocol) (n : ℕ) (ideal : Option Idealization)
    (req : List Bool) (s : Challenger) (inst : Instance)
    (h : s.instances[(unframe req).length]? = some inst) (hphase : inst.phase = .running)
    (hlen : ¬ P.TooLong n (dropFrame req)) :
    challenger P n ideal (.deliver, req) s = (do
      let i := (unframe req).length
      let msg := dropFrame req
      let out ← P.step ⟨n, inst.user, inst.longTermKey, inst.role, inst.state, msg⟩
      let stepInst : Instance := ⟨inst.user, inst.longTermKey, inst.role, out.state,
        out.phase, out.partner, out.key, inst.classification, inst.effectiveKey⟩
      let s' : Challenger := ⟨s.ttp, s.honest, s.corrupt, s.instances.set i stepInst,
        s.log ++ [.deliver i msg out.message out.phase]⟩
      if out.phase = .finished then
        match ideal with
        | none => pure (encDeliverReply ⟨out.message, .finished, out.partner, some out.key⟩, s')
        | some idl =>
          let c := idl.partner s'.log
          let esk ← effectiveKey P n c (idl.exposed s' i) stepInst s'
          let finInst : Instance := ⟨inst.user, inst.longTermKey, inst.role, out.state,
            out.phase, out.partner, out.key, some c, esk⟩
          pure (encDeliverReply ⟨out.message, .finished, out.partner, esk⟩,
            { s' with instances := s'.instances.set i finInst })
      else
        pure (encDeliverReply ⟨out.message, out.phase, [], none⟩, s')) := by
  simp only [challenger, h, ne_eq, hphase, not_true_eq_false, hlen, or_self, ↓reduceIte]; rfl

end Cslib.Crypto.AKE
