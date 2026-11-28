/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate


public import CslibFrontier.Crypto.Protocols.UC.Execution

/-!
# Ideal UC Bit Commitment Functionality and Plain-Model Schemes

In `fcom` ([CanettiFischlin2001], Figure 2), committer `0 : Fin 2` submits `.commit b` and later
`.openCom` and receives no party-port output (`none`), while receiver `1 : Fin 2` polls `.query`
and receives `some .receipt` and later `some (.opened b)` once those outputs are released by the
simulator through the backdoor (`CommitmentBackdoor.deliverCommit`,
`CommitmentBackdoor.deliverOpen`). The simulator can also poll `CommitmentBackdoor.query` to read
the current status of `fcom` (`none` when idle, `some .receipt` when committed, and
`some (.opened b)` when opened).

In the plain model (`PlainCommitmentScheme`), committer `0 : Fin 2` and receiver `1 : Fin 2` share
no trusted setup (such as a common reference string with a simulator trapdoor). Honest committer `0`
samples a commit message and opening message `(c, o) ← scheme.commit κ b`, and honest receiver `1`
verifies a delivered pair `(c, o)` using `scheme.verify κ c o`. When committer `0` is statically
corrupted (`C = {0}`), the adversary may inject arbitrary commit and opening messages `(c, o)` to
honest receiver `1`; when receiver `1` is statically corrupted (`C = {1}`), the adversary reads the
commit and opening messages sent by honest committer `0`.


## Main definitions

* `Cslib.Crypto.Protocols.UC.CommitmentInput`,
  `Cslib.Crypto.Protocols.UC.CommitmentOutput`,
  `Cslib.Crypto.Protocols.UC.CommitmentBackdoor`,
  `Cslib.Crypto.Protocols.UC.CommitmentPhase`,
  `Cslib.Crypto.Protocols.UC.CommitmentState`: inputs, outputs, backdoor queries, and states of the
  ideal two-party commitment functionality.
* `Cslib.Crypto.Protocols.UC.fcom`: the two-party ideal bit-commitment functionality
  $\mathcal{F}_{\mathrm{com}}$ with simulator-controlled output delivery.
* `Cslib.Crypto.Protocols.UC.FcomAdversary`: adversaries and simulators facing `fcom`.
* `Cslib.Crypto.Protocols.UC.PlainNetQ`, `Cslib.Crypto.Protocols.UC.PlainNetR`,
  `Cslib.Crypto.Protocols.UC.CommitterState`, `Cslib.Crypto.Protocols.UC.ReceiverState`,
  `Cslib.Crypto.Protocols.UC.PlainCommitmentScheme`,
  `Cslib.Crypto.Protocols.UC.PlainCommitmentSim`: plain-model two-party commitment schemes, their
  compilation `PlainCommitmentScheme.toProtocol` into a UC `Protocol`, and their dummy-adversary
  simulators against `fcom`.

## Main results

* `Cslib.Crypto.Protocols.UC.fcom_isBounded`, `Cslib.Crypto.Protocols.UC.fcom_polyBounded`,
  `Cslib.Crypto.Protocols.UC.corruptRouter_fcom_isBounded`,
  `Cslib.Crypto.Protocols.UC.PlainCommitmentScheme.toProtocol_polyBounded`: call-budget bounds.

## References

* [R. Canetti, M. Fischlin, *Universally Composable Commitments*][CanettiFischlin2001]: Figure 2
  ($\mathcal{F}_{\mathrm{com}}$), numbered as in the full version (Cryptology ePrint Archive,
  Report 2001/055).
* [R. Canetti, *Universally Composable Security*][Canetti2020]: UC execution and emulation.
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.UC

open Polynomial
open scoped NNReal

/-! ### Ideal two-party commitment functionality `fcom` -/

/-- Inputs to the two-party commitment functionality: committer `0` submits `commit b` and
`openCom`, and receiver `1` submits `query` to read its output. -/
inductive CommitmentInput : Type
  | commit (b : Bool)
  | openCom
  | query
  deriving DecidableEq, Repr

/-- Outputs of the two-party commitment functionality: `receipt` acknowledges that a commitment has
been recorded without revealing the bit, and `opened b` reveals the committed bit `b`. -/
inductive CommitmentOutput : Type
  | receipt
  | opened (b : Bool)
  deriving DecidableEq, Repr

/-- Backdoor queries of `fcom`: the simulator can `query` the commitment status (`none` when idle,
`some .receipt` when committed, `some (.opened b)` when opened), `deliverCommit` to release the
receipt to receiver `1`, and `deliverOpen` to release the opened bit to receiver `1`. -/
inductive CommitmentBackdoor : Type
  | query
  | deliverCommit
  | deliverOpen
  deriving DecidableEq, Repr

/-- Post-commit phase of `fcom`: tracks whether committer `0` has opened (`opened`), whether the
simulator has delivered the receipt to receiver `1` (`recDelivered`), and whether the simulator has
delivered the opened bit to receiver `1` (`openDelivered`). -/
structure CommitmentPhase : Type where
  /-- Whether committer `0` has submitted `openCom`. -/
  opened : Bool := false
  /-- Whether the simulator has delivered the commitment receipt to receiver `1`. -/
  recDelivered : Bool := false
  /-- Whether the simulator has delivered the opening to receiver `1`. -/
  openDelivered : Bool := false
  deriving DecidableEq, Repr

/-- Internal state of `fcom`: initially `idle`, and `active b phase` once committer `0` has
committed to `b`. -/
inductive CommitmentState : Type
  | idle
  | active (b : Bool) (phase : CommitmentPhase)
  deriving DecidableEq, Repr

/-- State of `fcom` when bit `b` has been committed (`opened = false, openDelivered = false`) and
the receipt-delivery flag is `recDelivered`. -/
def CommitmentState.committed (b : Bool) (recDelivered : Bool) :
    CommitmentState :=
  .active b { opened := false, recDelivered := recDelivered, openDelivered := false }

/-- State of `fcom` when bit `b` has been opened by committer `0` (`opened = true,
openDelivered = false`) and the receipt-delivery flag is `recDelivered`. -/
def CommitmentState.opened (b : Bool) (recDelivered : Bool) :
    CommitmentState :=
  .active b { opened := true, recDelivered := recDelivered, openDelivered := false }

/-- The ideal two-party bit-commitment functionality $\mathcal{F}_{\mathrm{com}}$
([CanettiFischlin2001], Figure 2) for committer `0 : Fin 2` and receiver `1 : Fin 2` with
simulator-controlled output delivery:
- Committer `0` receives no party-port output (`none`). Sending `commit b` in `idle` records `b` in
  state `CommitmentState.committed b false` (subsequent `commit` inputs are ignored), and sending
  `openCom` in `active b phase` sets `phase.opened := true`.
- Receiver `1` polling `query` receives `none` until the simulator sends `deliverCommit` on the
  backdoor (after `0` has committed), then receives `some .receipt` until the simulator sends
  `deliverOpen` on the backdoor (after `0` has opened and `deliverCommit` has been sent), and then
  receives `some (.opened b)`.
- On backdoor `query`, the simulator receives `none` in `idle`, `some .receipt` when `b` is
  committed and not yet opened (hiding `b`), and `some (.opened b)` once `0` has opened.

Figure 2 halts on an `Open` with no recorded bit; here `openCom` in `idle` is ignored instead, as
it is by the honest committer of `PlainCommitmentScheme.toProtocol`. -/
def fcom :
    IdealFunctionality 2 CommitmentInput CommitmentOutput
      CommitmentBackdoor (Option CommitmentOutput) where
  State := CommitmentState
  init _ _ := pure .idle
  onInput i x s :=
    if i = 0 then
      match x, s with
      | .commit b, .idle => pure (none, .committed b false)
      | .openCom, .active b phase =>
        pure (none, .active b { phase with opened := true })
      | _, _ => pure (none, s)
    else
      match x, s with
      | .query, .active b phase =>
        if phase.openDelivered then
          pure (some (.opened b), s)
        else if phase.recDelivered then
          pure (some .receipt, s)
        else
          pure (none, s)
      | _, _ => pure (none, s)
  onBackdoor q s :=
    match q, s with
    | .query, .idle => pure (none, .idle)
    | .query, .active b phase =>
      if phase.opened then
        pure (some (.opened b), s)
      else
        pure (some .receipt, s)
    | .deliverCommit, .active b phase =>
      pure (none, .active b { phase with recDelivered := true })
    | .deliverOpen, .active b phase =>
      if phase.opened && phase.recDelivered then
        pure (none, .active b { phase with openDelivered := true })
      else
        pure (none, s)
    | _, .idle => pure (none, .idle)

/-- `fcom` is purely deterministic and makes zero oracle calls per activation. -/
theorem fcom_isBounded (κ : ℕ) (C : Finset (Fin 2)) : (fcom.toProtocol κ C).IsBounded 0 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | q <;> [fin_cases i <;> cases x; cases q] <;>
    rcases s with _ | ⟨b, ⟨_ | _, _ | _, _ | _⟩⟩ <;> exact OracleComp.IsCostBounded.pure _ 0

/-- `fcom` has polynomial call budget `0`. -/
theorem fcom_polyBounded : fcom.toProtocol.PolyBounded 0 := fun κ C => by
  rw [Polynomial.eval_zero]
  exact fcom_isBounded κ C

/-- Routing corruptions around `fcom` still makes zero oracle calls per activation. -/
theorem corruptRouter_fcom_isBounded (κ : ℕ) (C : Finset (Fin 2)) :
    (corruptRouter C (fcom.toProtocol κ C)).IsBounded 0 := by
  refine ⟨OracleComp.IsCostBounded.pure _ 0, fun q s => ?_⟩
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | q⟩
  · by_cases hi : i ∈ C
    · simp only [corruptRouter_handle_inl_of_mem C _ hi, StateT.run_pure]
      exact OracleComp.IsCostBounded.pure _ 0
    · simp only [corruptRouter_handle_inl_of_notMem C _ hi]
      exact (fcom_isBounded κ C).2 (.inl (i, x)) s
  · by_cases hi : i ∈ C
    · simp only [corruptRouter_handle_inr_inl_of_mem C _ hi]
      erw [StateT.run_map]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr ((fcom_isBounded κ C).2 (.inl (i, x)) s)
    · simp only [corruptRouter_handle_inr_inl_of_notMem C _ hi, StateT.run_pure]
      exact OracleComp.IsCostBounded.pure _ 0
  · simp only [corruptRouter_handle_inr_inr]
    erw [StateT.run_map]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr ((fcom_isBounded κ C).2 (.inr q) s)

/-- Adversaries (and simulators) facing `fcom`: environment queries `AdvQ` with replies `AdvR`,
and access to the party ports and backdoor of `fcom` on the network side. -/
abbrev FcomAdversary (AdvQ AdvR : Type) : Type 1 :=
  ExecAdversary 2 CommitmentInput CommitmentOutput CommitmentBackdoor (Option CommitmentOutput)
    AdvQ AdvR

/-! ### Plain-model two-party commitment schemes and UC protocol compilation -/

/-- Network queries for a two-party plain-model commitment protocol: the adversary can read the
commit and opening messages posted by honest committer `0` (`readCommit`, `readOpen`) and deliver
commit and opening messages to receiver `1` (`deliverCommit`, `deliverOpen`). -/
inductive PlainNetQ (CommitMsg OpenMsg : Type) : Type
  | readCommit
  | readOpen
  | deliverCommit (c : CommitMsg)
  | deliverOpen (o : OpenMsg)
  deriving DecidableEq, Repr

/-- Network responses for a two-party plain-model commitment protocol. -/
inductive PlainNetR (CommitMsg OpenMsg : Type) : Type
  | commitMsg (c : Option CommitMsg)
  | openMsg (o : Option OpenMsg)
  | ack
  deriving DecidableEq, Repr

/-- Local state of honest committer `0` in a plain-model commitment protocol. -/
inductive CommitterState (CommitMsg OpenMsg : Type) : Type
  | idle
  | committed (c : CommitMsg) (o : OpenMsg)
  | opened (c : CommitMsg) (o : OpenMsg)
  deriving DecidableEq, Repr

/-- Local state of honest receiver `1` in a plain-model commitment protocol. -/
inductive ReceiverState (CommitMsg : Type) : Type
  | waiting
  | committed (c : CommitMsg)
  | finished (res : Option Bool)
  deriving DecidableEq, Repr

/-- A simulator for the dummy adversary of a two-party plain-model commitment scheme with messages
`CommitMsg` and `OpenMsg` against the ideal commitment functionality `fcom`. -/
abbrev PlainCommitmentSim (CommitMsg OpenMsg : Type) : Type 1 :=
  FcomAdversary (RoutedNetQ 2 CommitmentInput (PlainNetQ CommitMsg OpenMsg))
    (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg))

/-- A two-party plain-model bit-commitment scheme with commit message type `CommitMsg` and opening
message type `OpenMsg`:
- `commit κ b` samples the commit message `c` and opening message `o` for bit `b` at security
  parameter `κ`.
- `verify κ c o` verifies a commit message `c` and opening message `o`, returning `some b` if the
  opening is accepted for bit `b` and `none` otherwise. -/
structure PlainCommitmentScheme (CommitMsg OpenMsg : Type) : Type where
  /-- Committer's commit and opening sampler. -/
  commit : ℕ → Bool → ProbComp (CommitMsg × OpenMsg)
  /-- Receiver's verification algorithm. -/
  verify : ℕ → CommitMsg → OpenMsg → ProbComp (Option Bool)

namespace PlainCommitmentScheme

variable {CommitMsg OpenMsg : Type} [DecidableEq CommitMsg] [DecidableEq OpenMsg]

/-- Polynomial call budgets `pC` and `pV` for `scheme.commit` and `scheme.verify`. -/
structure IsPolyBounded (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (pC pV : Polynomial ℕ) : Prop where
  /-- Every commitment to `b` at security parameter `κ` makes at most `pC.eval κ` calls. -/
  commit : ∀ κ b, (scheme.commit κ b).IsQueryBounded (pC.eval κ)
  /-- Every verification at security parameter `κ` makes at most `pV.eval κ` calls. -/
  verify : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ)

/-- The standalone completeness experiment for bit `b` at security parameter `κ`: sample
`(c, o) ← scheme.commit κ b`, run `res ← scheme.verify κ c o`, and check `res = some b`. -/
noncomputable def acceptGame (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (b : Bool) : Game :=
  ProbComp.eval do
    let (c, o) ← scheme.commit κ b
    let res ← scheme.verify κ c o
    return decide (res = some b)

/-- Probability that an honest commitment to `b` followed by an honest opening is accepted by the
receiver at security parameter `κ`. -/
noncomputable def acceptProb (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (b : Bool) : ℝ≥0 :=
  Game.succProbability (scheme.acceptGame κ b)

/-- Perfect completeness: honest commitments to both `false` and `true` are accepted with
probability `1` at every security parameter. -/
def PerfectlyComplete (scheme : PlainCommitmentScheme CommitMsg OpenMsg) : Prop :=
  ∀ κ b, scheme.acceptProb κ b = 1

/-- Compile a `PlainCommitmentScheme` into a two-party UC `Protocol` in the plain model:
- Committer `0` and receiver `1` maintain independent local states `CommitterState` and
  `ReceiverState` with no shared secret state. Committer `0` produces no party-port output (`none`).
- When `0 ∉ C` (honest committer), `deliverCommit c` and `deliverOpen o` deliver `c` and `o` to
  receiver `1` when they match the messages posted by `0`; when `0 ∈ C` (corrupted committer), the
  adversary may inject any `c` and `o` to honest receiver `1`. -/
def toProtocol (scheme : PlainCommitmentScheme CommitMsg OpenMsg) :
    Protocol 2 CommitmentInput CommitmentOutput
      (PlainNetQ CommitMsg OpenMsg) (PlainNetR CommitMsg OpenMsg) := fun κ C => {
  State := CommitterState CommitMsg OpenMsg × ReceiverState CommitMsg
  init := pure (.idle, .waiting)
  handle q s :=
    match q with
    | .inl (i, x) =>
      if i = 0 then
        if (0 : Fin 2) ∈ C then
          pure (none, s)
        else
          match x, s.1 with
          | .commit b, .idle => do
            let co ← ProbOracleComp.sample (scheme.commit κ b)
            return (none, (.committed co.1 co.2, s.2))
          | .openCom, .committed c o =>
            pure (none, (.opened c o, s.2))
          | _, _ => pure (none, s)
      else
        if (1 : Fin 2) ∈ C then
          pure (none, s)
        else
          match x, s.2 with
          | .query, .waiting => pure (none, s)
          | .query, .committed _ => pure (some .receipt, s)
          | .query, .finished (some b) => pure (some (.opened b), s)
          | .query, .finished none => pure (none, s)
          | _, _ => pure (none, s)
    | .inr netQ =>
      match netQ with
      | .readCommit =>
        match s.1 with
        | .idle => pure (.commitMsg none, s)
        | .committed c _ => pure (.commitMsg (some c), s)
        | .opened c _ => pure (.commitMsg (some c), s)
      | .readOpen =>
        match s.1 with
        | .opened _ o => pure (.openMsg (some o), s)
        | _ => pure (.openMsg none, s)
      | .deliverCommit c =>
        match s.2 with
        | .waiting =>
          if (0 : Fin 2) ∈ C then
            pure (.ack, (s.1, .committed c))
          else
            match s.1 with
            | .committed c' _ =>
              if c = c' then pure (.ack, (s.1, .committed c)) else pure (.ack, s)
            | .opened c' _ =>
              if c = c' then pure (.ack, (s.1, .committed c)) else pure (.ack, s)
            | .idle => pure (.ack, s)
        | _ => pure (.ack, s)
      | .deliverOpen o =>
        match s.2 with
        | .committed c =>
          if (0 : Fin 2) ∈ C then do
            let res ← ProbOracleComp.sample (scheme.verify κ c o)
            return (.ack, (s.1, .finished res))
          else
            match s.1 with
            | .opened _ o' =>
              if o = o' then do
                let res ← ProbOracleComp.sample (scheme.verify κ c o)
                return (.ack, (s.1, .finished res))
              else
                pure (.ack, s)
            | _ => pure (.ack, s)
        | _ => pure (.ack, s) }

/-- If `scheme` has polynomial call budgets `pC` and `pV`, then `scheme.toProtocol` has polynomial
call budget `pC + pV`. -/
theorem toProtocol_polyBounded {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pC pV : Polynomial ℕ} (h : scheme.IsPolyBounded pC pV) :
    scheme.toProtocol.PolyBounded (pC + pV) := fun κ C => by
  rw [Polynomial.eval_add]
  refine ⟨OracleComp.IsCostBounded.pure _ _, fun q ⟨s₁, s₂⟩ => ?_⟩
  have h10 : (⟨1, by decide⟩ : Fin 2) ≠ 0 := by decide
  have hverify (c : CommitMsg) (o : OpenMsg) :
      (ProbOracleComp.sample (spec := OracleSpec.empty) (scheme.verify κ c o) >>= fun res =>
        pure (PlainNetR.ack (CommitMsg := CommitMsg) (OpenMsg := OpenMsg),
          (s₁, ReceiverState.finished (CommitMsg := CommitMsg) res))).IsQueryBounded
        (pC.eval κ + pV.eval κ) :=
    ((Machine.isQueryBounded_sample (I := OracleSpec.empty) (h.verify κ c o)).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  rcases q with ⟨i, x⟩ | netQ
  · fin_cases i
    · by_cases h0 : (0 : Fin 2) ∈ C <;> [skip; cases x <;> cases s₁] <;>
        simp only [toProtocol, StateT.run, h0, ↓reduceIte] <;>
        first
        | exact ((Machine.isQueryBounded_sample (I := OracleSpec.empty) (h.commit κ _)).bind
            fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)
        | exact OracleComp.IsCostBounded.pure _ _
    · by_cases h1 : (1 : Fin 2) ∈ C <;> [skip; rcases s₂ with _ | c | (_ | b) <;> cases x] <;>
        simp only [toProtocol, StateT.run, h10, h1, ↓reduceIte] <;>
        exact OracleComp.IsCostBounded.pure _ _
  · cases netQ with
    | readCommit | readOpen => cases s₁ <;> exact OracleComp.IsCostBounded.pure _ _
    | deliverCommit c =>
      cases s₂ <;> cases s₁ <;> simp only [toProtocol, StateT.run] <;>
        (try split_ifs) <;> exact OracleComp.IsCostBounded.pure _ _
    | deliverOpen o =>
      cases s₂ <;> cases s₁ <;> simp only [toProtocol, StateT.run] <;>
        (try split_ifs) <;> (first | exact hverify _ _ | exact OracleComp.IsCostBounded.pure _ _)

end PlainCommitmentScheme

end Cslib.Crypto.Protocols.UC

end
