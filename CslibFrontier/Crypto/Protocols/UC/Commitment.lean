/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.DummyAdversary
import CslibFrontier.Languages.Probabilistic.Simulation
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind

/-!
# Ideal UC Bit Commitment and a Statistical Call-Bounded Impossibility Theorem

This module defines the two-party ideal bit-commitment functionality `fcom` in the Universally
Composable (UC) framework with static corruptions
(`CslibFrontier/Crypto/Protocols/UC/Execution.lean`) and proves a statistical, call-bounded,
one-message adaptation of the Canetti–Fischlin impossibility theorem ([CanettiFischlin2001],
Theorem 6; computational polynomial-time UC execution is open in #6043): no plain-model two-party
commitment scheme with one commitment message and one opening message, and with nontrivial
completeness, realizes `fcom` in this library's novel call-bounded port model (`Realizes`).

Scope relative to the source (#6043). Theorem 6 of [CanettiFischlin2001] covers every bilateral,
terminating polynomial-time protocol with non-negligible termination, even against simulators that
may depend on the environment. The result here is narrower and in a different model:
- `PlainCommitmentScheme` sends one commitment message and one opening message;
- the asymptotic statement `not_realizes_fcom` assumes that the honest acceptance probabilities on
  `false` and `true` eventually sum to at least `1 + c` for a constant `c > 0`;
- `Realizes` supplies one simulator before the environment is chosen (the concrete trade-off
  `acceptProb_add_le_one_add_advantage` allows independent simulators for `C = {0}` and `C = {1}`);
- `PolyBounded` counts oracle calls and allows arbitrary pure computation between them (#6043), so
  the budgets of `corruptReceiverEnv_polyBounded` and `corruptCommitterEnv_polyBounded` are call
  counts, not polynomial-time machine realizations.
Impossibility for this statistical, call-bounded notion does not establish impossibility of
computational UC commitment; general bilateral protocols and the computational setting remain open
(#6043).

In `fcom` ([CanettiFischlin2001], Figure 2), committer `0 : Fin 2` submits `.commit b` and later
`.openCom` and receives no party-port output (`none`), while receiver `1 : Fin 2` polls `.query`
and receives `some .receipt` and later `some (.opened b)` once those outputs are released by the
simulator through the backdoor (`CommitmentBackdoor.deliverCommit`,
`CommitmentBackdoor.deliverOpen`). The simulator can also poll `CommitmentBackdoor.query` to read
the current status of `fcom` (`none` when idle, `some .receipt` when committed, and
`some (.opened b)` when opened).

In the plain model (`PlainCommitmentScheme`), committer `0 : Fin 2` and receiver `1 : Fin 2` share
no trusted setup. Honest committer `0` samples `(c, o) ← scheme.commit κ b`, and honest receiver
`1` verifies a delivered pair `(c, o)` using `scheme.verify κ c o`. When committer `0` is
statically corrupted (`C = {0}`), the adversary may inject arbitrary commit and opening messages
`(c, o)` to honest receiver `1`; when receiver `1` is statically corrupted (`C = {1}`), the
adversary reads the commit and opening messages sent by honest committer `0`.

The Canetti–Fischlin impossibility argument combines two environments against `dummyAdversary`:
1. **Corrupted-receiver experiment (`C = {1}`, `corruptReceiverEnv`):** Honest committer `0`
   commits to `b`, the environment reads `c`, honest committer `0` opens, the environment reads `o`,
   and the environment runs `scheme.verify κ c o` to check `res = some b`. In the real execution
   this succeeds with probability `scheme.acceptProb κ b` (`eval_exec_real_corruptReceiverEnv`). In
   the ideal execution with any simulator `S₁`, while `fcom` is in state `.committed b recDel`
   before opening, `fcom`'s responses on `C = {1}` depend only on `recDel`
   (`runFrom_fcom_committed`), so `S₁`'s pre-open commit phase cannot depend on `b`.
2. **Corrupted-committer equivocation experiment (`C = {0}`, `corruptCommitterEnv`):** Using `S₁`,
   the environment runs `S₁`'s pre-open commit simulation and delivers the resulting `c` to honest
   receiver `1`, checks `some .receipt`, runs `S₁`'s opening simulation for bit `b`, delivers `o`,
   and checks `some (.opened b)`.
   - In the **real** world (`C = {0}`), honest receiver `1` depends only on the delivered `(c, o)`,
     so the real execution equals the ideal execution of `corruptReceiverEnv` with `S₁`
     (`exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv`).
   - In the **ideal** world (`C = {0}`), once honest receiver `1` observes `some .receipt`, `fcom`
     is locked to `.active b* phase` for a single bit `b*` before `b` is used
     (`runFrom_execMachine_fcom_locked`), so the ideal success probabilities on `false` and `true`
     sum to at most `1` (`succProbability_exec_fcom_corruptCommitterEnv_add_le_one`).

Combining both experiments via the triangle inequality yields `acceptProb_add_le_one_add_advantage`
and the concrete and asymptotic impossibility theorems `not_emulatesDummyWithin_fcom`,
`not_realizesWithin_fcom`, `not_realizes_fcom`, and `not_realizes_fcom_of_perfectlyComplete`.

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
* `Cslib.Crypto.Protocols.UC.fcomCommittedView`,
  `Cslib.Crypto.Protocols.UC.fcomLocked`: state-abstraction machines capturing pre-open hiding
  (`C = {1}`) and post-commit binding (`C = {0}`) of `fcom`.
* `Cslib.Crypto.Protocols.UC.PlainNetQ`, `Cslib.Crypto.Protocols.UC.PlainNetR`,
  `Cslib.Crypto.Protocols.UC.CommitterState`, `Cslib.Crypto.Protocols.UC.ReceiverState`,
  `Cslib.Crypto.Protocols.UC.PlainCommitmentScheme`,
  `Cslib.Crypto.Protocols.UC.PlainCommitmentSim`: plain-model two-party commitment schemes, their
  compilation `PlainCommitmentScheme.toProtocol` into a UC `Protocol`, and their dummy-adversary
  simulators against `fcom`.
* `Cslib.Crypto.Protocols.UC.honestCommitEnv`,
  `Cslib.Crypto.Protocols.UC.corruptReceiverEnv`,
  `Cslib.Crypto.Protocols.UC.corruptCommitterEnv`: honest-completeness, corrupted-receiver, and
  corrupted-committer equivocation environments.

## Main results

* `Cslib.Crypto.Protocols.UC.fcom_polyBounded`,
  `Cslib.Crypto.Protocols.UC.runFrom_fcom_committed`,
  `Cslib.Crypto.Protocols.UC.runFrom_execMachine_fcom_locked`: budget, pre-open hiding, and
  post-commit binding of `fcom`.
* `Cslib.Crypto.Protocols.UC.eval_exec_honestCommitEnv`,
  `Cslib.Crypto.Protocols.UC.eval_exec_real_corruptReceiverEnv`,
  `Cslib.Crypto.Protocols.UC.exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv`:
  exact execution laws for honest completeness, corrupted-receiver extraction, and plain-model
  man-in-the-middle equivocation.
* `Cslib.Crypto.Protocols.UC.succProbability_exec_fcom_corruptCommitterEnv_add_le_one`:
  ideal-world binding bounds the sum of equivocation success probabilities on `false` and `true`
  by `1`.
* `Cslib.Crypto.Protocols.UC.acceptProb_add_le_one_add_advantage`: quantitative Canetti–Fischlin
  lower bound relating completeness to $C = \{1\}$ and $C = \{0\}$ distinguishing advantages.
* `Cslib.Crypto.Protocols.UC.not_emulatesDummyWithin_fcom`,
  `Cslib.Crypto.Protocols.UC.not_realizesWithin_fcom`,
  `Cslib.Crypto.Protocols.UC.not_realizes_fcom`,
  `Cslib.Crypto.Protocols.UC.not_realizes_fcom_of_perfectlyComplete`: concrete and asymptotic
  impossibility of one-message plain-model bit commitment in the statistical, call-bounded UC model
  (#6043).

## References

* [R. Canetti, M. Fischlin, *Universally Composable Commitments*][CanettiFischlin2001]: Figure 2
  ($\mathcal{F}_{\mathrm{com}}$) and Theorem 6 (impossibility in the plain model), numbered as in
  the full version (Cryptology ePrint Archive, Report 2001/055).
* [R. Canetti, *Universally Composable Security*][Canetti2020]: UC execution and emulation.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open Polynomial
open OracleComp (sumHandler)
open scoped NNReal ENNReal

/-! ### Closed-machine stepping helpers -/

private def closeRunFrom {ιE α : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (prog : ProbOracleComp E α) (s : M.State) : ProbComp α :=
  Prod.fst <$> Machine.closeProgram (M.runFrom prog s)

private theorem run_eq_bind_closeRunFrom {ιE α : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (prog : ProbOracleComp E α) :
    M.run prog = M.init >>= closeRunFrom M prog := by
  rw [Machine.run, Machine.link, Machine.closeProgram_bind, Machine.closeProgram_sample]
  exact bind_congr fun _ => Machine.closeProgram_map _ _

private theorem run_eq_closeRunFrom_of_init_pure {ιE α : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (prog : ProbOracleComp E α) (s₀ : M.State)
    (hinit : M.init = pure s₀ := by rfl) :
    M.run prog = closeRunFrom M prog s₀ := by
  rw [run_eq_bind_closeRunFrom, hinit, pure_bind]

@[simp] private theorem closeRunFrom_pure {ιE α : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (a : α) (s : M.State) :
    closeRunFrom M (pure a) s = pure a := rfl

private theorem closeRunFrom_sample {ιE α β : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (d : ProbComp α) (cont : α → ProbOracleComp E β)
    (s : M.State) :
    closeRunFrom M (ProbOracleComp.sample d >>= cont) s =
      d >>= fun a => closeRunFrom M (cont a) s := by
  simp only [closeRunFrom, Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left,
    Machine.closeProgram_bind, Machine.closeProgram_sample, map_bind]

private theorem closeRunFrom_query_pure {ιE α : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (q : ιE) (cont : E q → ProbOracleComp E α)
    (s : M.State) (r : E q) (s' : M.State)
    (h : (M.handle q).run s = pure (r, s') := by rfl) :
    closeRunFrom M (ProbOracleComp.query q >>= cont) s = closeRunFrom M (cont r) s' := by
  rw [closeRunFrom, Machine.runFrom_bind, Machine.runFrom_query, h, pure_bind]; rfl

private theorem closeRunFrom_query_sample {ιE α β : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (q : ιE) (cont : E q → ProbOracleComp E β)
    (s : M.State) (d : ProbComp α) (f : α → E q) (g : α → M.State)
    (h : (M.handle q).run s = (fun a => (f a, g a)) <$> ProbOracleComp.sample d) :
    closeRunFrom M (ProbOracleComp.query q >>= cont) s =
      d >>= fun a => closeRunFrom M (cont (f a)) (g a) := by
  rw [closeRunFrom, Machine.runFrom_bind, Machine.runFrom_query, h, bind_map_left,
    Machine.closeProgram_bind, Machine.closeProgram_sample, map_bind]
  rfl

private theorem closeRunFrom_query_bind {ιE α : Type} {E : ιE → Type}
    (M : Machine OracleSpec.empty E) (q : ιE) (cont : E q → ProbOracleComp E α)
    (s : M.State) :
    closeRunFrom M (ProbOracleComp.query q >>= cont) s =
      Machine.closeProgram ((M.handle q).run s) >>= fun x => closeRunFrom M (cont x.1) x.2 := by
  simp only [closeRunFrom, Machine.runFrom_bind, Machine.runFrom_query,
    Machine.closeProgram_bind, map_bind]

private theorem runFrom_liftRightProgram_map_state {ιL ιR α : Type}
    (L : ιL → Type) {R : ιR → Type}
    (M : Machine OracleSpec.empty (L ⊕ₒ R)) (V : Machine OracleSpec.empty R)
    (f : V.State → M.State)
    (h : ∀ q s, (M.handle (.inr q)).run (f s) = Prod.map _root_.id f <$> (V.handle q).run s)
    (program : ProbOracleComp R α) (s : V.State) :
    M.runFrom (Machine.liftRightProgram L program) (f s) =
      Prod.map _root_.id f <$> V.runFrom program s := by
  let M_R : Machine OracleSpec.empty R :=
    { State := M.State, init := M.init, handle := fun q => M.handle (.inr q) }
  have hlift : ∀ (p : ProbOracleComp R α) (st : M.State),
      M.runFrom (Machine.liftRightProgram L p) st = M_R.runFrom p st := by
    intro p
    induction p using OracleComp.induction with
    | pure _ => intro _; rfl
    | query_bind q _ ih =>
      intro st
      rw [PFunctor.FreeM.bind_eq_bind, Machine.liftRightProgram_bind, Machine.runFrom_bind,
        Machine.runFrom_bind]
      cases q with
      | inl k =>
        change (M.runFrom (Machine.liftRightProgram L
            (ProbOracleComp.sample (ProbComp.unifFin k))) st >>= _) =
          (M_R.runFrom (ProbOracleComp.sample (ProbComp.unifFin k)) st >>= _)
        rw [Machine.liftRightProgram_sample, Machine.runFrom_sample, Machine.runFrom_sample,
          bind_map_left, bind_map_left]
        exact bind_congr fun a => ih a st
      | inr q =>
        change (M.runFrom (Machine.liftRightProgram L (ProbOracleComp.query q)) st >>= _) =
          (M_R.runFrom (ProbOracleComp.query q) st >>= _)
        rw [Machine.liftRightProgram_query, Machine.runFrom_query, Machine.runFrom_query]
        exact bind_congr fun x => ih x.1 x.2
  rw [hlift]
  exact Machine.runFrom_map_state M_R V f h program s

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
@[expose] def CommitmentState.committed (b : Bool) (recDelivered : Bool) :
    CommitmentState :=
  .active b { opened := false, recDelivered := recDelivered, openDelivered := false }

/-- State of `fcom` when bit `b` has been opened by committer `0` (`opened = true,
openDelivered = false`) and the receipt-delivery flag is `recDelivered`. -/
@[expose] def CommitmentState.opened (b : Bool) (recDelivered : Bool) :
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
@[expose] def fcom :
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
  rcases q with ⟨i, x⟩ | q
  · fin_cases i <;> cases x <;> rcases s with _ | ⟨b, ⟨_ | _, _ | _, _ | _⟩⟩ <;>
      exact OracleComp.IsCostBounded.pure _ 0
  · cases q <;> rcases s with _ | ⟨b, ⟨_ | _, _ | _, _ | _⟩⟩ <;>
      exact OracleComp.IsCostBounded.pure _ 0

/-- `fcom` has polynomial call budget `0`. -/
theorem fcom_polyBounded : fcom.toProtocol.PolyBounded 0 := fun κ C => by
  rw [Polynomial.eval_zero]
  exact fcom_isBounded κ C

private theorem isBounded_corruptRouter {n t : ℕ} {In Out NetQ NetR : Type} (C : Finset (Fin n))
    {P : Machine OracleSpec.empty (protocolSpec n In Out NetQ NetR)} (hP : P.IsBounded t) :
    (corruptRouter C P).IsBounded t := by
  refine ⟨hP.1, fun q s => ?_⟩
  let sP : P.State := s
  rcases q with ⟨i, x⟩ | ⟨⟨i, x⟩ | q⟩
  · dsimp only [corruptRouter]
    split_ifs
    · exact OracleComp.IsCostBounded.pure _ t
    · exact hP.2 (.inl (i, x)) sP
  · dsimp only [corruptRouter]
    split_ifs
    · change OracleComp.IsQueryBounded ((Sum.inl <$> P.handle (.inl (i, x))).run sP) t
      rw [StateT.run_map]
      exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (hP.2 (.inl (i, x)) sP)
    · exact OracleComp.IsCostBounded.pure _ t
  · change OracleComp.IsQueryBounded ((Sum.inr <$> P.handle (.inr q)).run sP) t
    rw [StateT.run_map]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (hP.2 (.inr q) sP)

/-- Adversaries (and simulators) facing `fcom`: environment queries `AdvQ` with replies `AdvR`,
and access to the party ports and backdoor of `fcom` on the network side. -/
abbrev FcomAdversary (AdvQ AdvR : Type) : Type 1 :=
  ExecAdversary 2 CommitmentInput CommitmentOutput CommitmentBackdoor (Option CommitmentOutput)
    AdvQ AdvR

/-- Bit-independent machine capturing the adversary's view of
`corruptRouter {1} (fcom.toProtocol κ {1})` while `fcom` is in state
`CommitmentState.committed b recDel`: committer `0` is honest (`0 ∉ {1}`), so `0`'s port returns
`none`, while receiver `1`'s `.query` port and the backdoor depend only on the receipt-delivery flag
`recDel : Bool` and not on `b`. -/
@[expose] def fcomCommittedView :
    Machine OracleSpec.empty
      (netSpec (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
        (RoutedNetR CommitmentOutput (Option CommitmentOutput))) where
  State := Bool
  init := pure false
  handle q recDel := pure <|
    match q with
    | .inl (i, x) =>
      if i = 0 then (.inl none, recDel)
      else match x with
        | .query => (.inl (if recDel then some .receipt else none), recDel)
        | _ => (.inl none, recDel)
    | .inr .query => (.inr (some .receipt), recDel)
    | .inr .deliverCommit => (.inr none, true)
    | .inr .deliverOpen => (.inr none, recDel)

private theorem fcomCommittedView_isBounded : fcomCommittedView.IsBounded 0 :=
  ⟨OracleComp.IsCostBounded.pure _ 0, fun _ _ => OracleComp.IsCostBounded.pure _ 0⟩

private theorem handle_corruptRouter_fcom_committed (κ : ℕ) (b : Bool)
    (q : RoutedNetQ 2 CommitmentInput CommitmentBackdoor) (recDel : Bool) :
    ((corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).handle (.inr q)).run
      (.committed b recDel) =
      Prod.map _root_.id (.committed b) <$> (fcomCommittedView.handle q).run recDel := by
  rcases q with ⟨i, x⟩ | q
  · fin_cases i <;> cases x <;> cases recDel <;> rfl
  · cases q <;> cases recDel <;> rfl

/-- Pre-open hiding of `fcom` for `C = {1}`: when only receiver `1` is corrupted, running any
network program against `corruptRouter {1} (fcom.toProtocol κ {1})` from
`CommitmentState.committed b recDel` factors through the bit-independent machine
`fcomCommittedView`. -/
theorem runFrom_fcom_committed (κ : ℕ) (b : Bool) {α : Type}
    (program : ProbOracleComp
      (netSpec (RoutedNetQ 2 CommitmentInput CommitmentBackdoor)
        (RoutedNetR CommitmentOutput (Option CommitmentOutput))) α)
    (recDel : Bool) :
    (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
      (liftNet program) (.committed b recDel) =
      Prod.map _root_.id (.committed b) <$> fcomCommittedView.runFrom program recDel :=
  runFrom_liftRightProgram_map_state (partySpec 2 CommitmentInput CommitmentOutput)
    (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})) fcomCommittedView
    (.committed b) (handle_corruptRouter_fcom_committed κ b) program recDel

/-- State-restricted version of `fcom.toProtocol` once bit `bStar` has been committed: the state is
`phase : CommitmentPhase`, and the committed bit `bStar` can never be altered. -/
@[expose] def fcomLocked (bStar : Bool) :
    Machine OracleSpec.empty
      (protocolSpec 2 CommitmentInput CommitmentOutput
        CommitmentBackdoor (Option CommitmentOutput)) where
  State := CommitmentPhase
  init := pure {}
  handle q phase :=
    match q with
    | .inl (i, x) =>
      if i = 0 then
        match x with
        | .openCom => pure (none, { phase with opened := true })
        | _ => pure (none, phase)
      else
        match x with
        | .query =>
          if phase.openDelivered then
            pure (some (.opened bStar), phase)
          else if phase.recDelivered then
            pure (some .receipt, phase)
          else
            pure (none, phase)
        | _ => pure (none, phase)
    | .inr .query =>
      if phase.opened then
        pure (some (.opened bStar), phase)
      else
        pure (some .receipt, phase)
    | .inr .deliverCommit =>
      pure (none, { phase with recDelivered := true })
    | .inr .deliverOpen =>
      if phase.opened && phase.recDelivered then
        pure (none, { phase with openDelivered := true })
      else
        pure (none, phase)

private theorem handle_fcom_locked (κ : ℕ) (C : Finset (Fin 2)) (bStar : Bool)
    (q : RoutedNetQ 2 CommitmentInput CommitmentBackdoor) (phase : CommitmentPhase) :
    ((fcom.toProtocol κ C).handle q).run (.active bStar phase) =
      Prod.map _root_.id (.active bStar) <$> ((fcomLocked bStar).handle q).run phase := by
  rcases q with ⟨i, x⟩ | q
  · fin_cases i <;> cases x <;> rcases phase with ⟨_ | _, _ | _, _ | _⟩ <;> rfl
  · cases q <;> rcases phase with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

/-- Post-commit binding of `fcom`: running an adversary `S₀` against `fcom` from state
`CommitmentState.active bStar phase` factors through `fcomLocked bStar`. -/
theorem runFrom_execMachine_fcom_locked {AdvQ AdvR : Type}
    (S₀ : FcomAdversary AdvQ AdvR)
    (κ : ℕ) (C : Finset (Fin 2)) (bStar : Bool) {α : Type}
    (program : ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR) α)
    (stS : (S₀ κ C).State) (phase : CommitmentPhase) :
    (execMachine fcom.toProtocol S₀ κ C).runFrom
      program (stS, .active bStar phase) =
      Prod.map _root_.id (Prod.map _root_.id (.active bStar)) <$>
        ((liftAdversary (S₀ κ C)).comp (corruptRouter C (fcomLocked bStar))).runFrom
          program (stS, phase) :=
  Machine.runFrom_map_state
    (execMachine fcom.toProtocol S₀ κ C)
    ((liftAdversary (S₀ κ C)).comp (corruptRouter C (fcomLocked bStar)))
    (Prod.map _root_.id (.active bStar))
    (Machine.comp_handle_map_state (liftAdversary (S₀ κ C))
      (corruptRouter C (fcom.toProtocol κ C)) (corruptRouter C (fcomLocked bStar))
      (.active bStar)
      (handle_corruptRouter_map_state C (fcom.toProtocol κ C) (fcomLocked bStar)
        (.active bStar) (handle_fcom_locked κ C bStar)))
    program (stS, phase)

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
@[expose] noncomputable def acceptGame (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (b : Bool) : Game :=
  ProbComp.eval do
    let (c, o) ← scheme.commit κ b
    let res ← scheme.verify κ c o
    return decide (res = some b)

/-- Probability that an honest commitment to `b` followed by an honest opening is accepted by the
receiver at security parameter `κ`. -/
@[expose] noncomputable def acceptProb (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ)
    (b : Bool) : ℝ≥0 :=
  Game.succProbability (scheme.acceptGame κ b)

/-- Perfect completeness: honest commitments to both `false` and `true` are accepted with
probability `1` at every security parameter. -/
@[expose] def PerfectlyComplete (scheme : PlainCommitmentScheme CommitMsg OpenMsg) : Prop :=
  ∀ κ b, scheme.acceptProb κ b = 1

/-- Compile a `PlainCommitmentScheme` into a two-party UC `Protocol` in the plain model:
- Committer `0` and receiver `1` maintain independent local states `CommitterState` and
  `ReceiverState` with no shared secret state. Committer `0` produces no party-port output (`none`).
- When `0 ∉ C` (honest committer), `deliverCommit c` and `deliverOpen o` deliver `c` and `o` to
  receiver `1` when they match the messages posted by `0`; when `0 ∈ C` (corrupted committer), the
  adversary may inject any `c` and `o` to honest receiver `1`. -/
@[expose] def toProtocol (scheme : PlainCommitmentScheme CommitMsg OpenMsg) :
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
          | .commit b, .idle =>
            ProbOracleComp.sample (scheme.commit κ b) >>= fun co =>
              pure (none, (.committed co.1 co.2, s.2))
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
          if (0 : Fin 2) ∈ C then
            ProbOracleComp.sample (scheme.verify κ c o) >>= fun res =>
              pure (.ack, (s.1, .finished res))
          else
            match s.1 with
            | .opened _ o' =>
              if o = o' then
                ProbOracleComp.sample (scheme.verify κ c o) >>= fun res =>
                  pure (.ack, (s.1, .finished res))
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
  have hcommit (b : Bool) :
      (ProbOracleComp.sample (spec := OracleSpec.empty) (scheme.commit κ b) >>= fun co =>
        pure ((none : Option CommitmentOutput),
          (CommitterState.committed co.1 co.2, s₂))).IsQueryBounded
        (pC.eval κ + pV.eval κ) :=
    ((Machine.isQueryBounded_sample (I := OracleSpec.empty) (h.commit κ b)).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  have hverify (c : CommitMsg) (o : OpenMsg) :
      (ProbOracleComp.sample (spec := OracleSpec.empty) (scheme.verify κ c o) >>= fun res =>
        pure (PlainNetR.ack (CommitMsg := CommitMsg) (OpenMsg := OpenMsg),
          (s₁, ReceiverState.finished (CommitMsg := CommitMsg) res))).IsQueryBounded
        (pC.eval κ + pV.eval κ) :=
    ((Machine.isQueryBounded_sample (I := OracleSpec.empty) (h.verify κ c o)).bind
      fun _ => OracleComp.IsCostBounded.pure _ 0).mono (by omega)
  dsimp only [toProtocol, StateT.run]
  rcases q with ⟨i, x⟩ | netQ
  · fin_cases i
    · by_cases h0 : (0 : Fin 2) ∈ C <;> cases x <;> cases s₁ <;>
        simp only [h0, ↓reduceIte] <;>
        first | exact hcommit _ | exact OracleComp.IsCostBounded.pure _ _
    · have h10 : (⟨1, by decide⟩ : Fin 2) ≠ 0 := by decide
      by_cases h1 : (1 : Fin 2) ∈ C <;> rcases s₂ with _ | c | (_ | b) <;> cases x <;>
        simp only [h10, h1, ↓reduceIte] <;>
        exact OracleComp.IsCostBounded.pure _ _
  · cases netQ with
    | readCommit | readOpen =>
      cases s₁ <;> exact OracleComp.IsCostBounded.pure _ _
    | deliverCommit c =>
      cases s₂ with
      | waiting =>
        by_cases h0 : (0 : Fin 2) ∈ C
        · simp only [h0, ↓reduceIte]; exact OracleComp.IsCostBounded.pure _ _
        · cases s₁ <;> simp only [h0, ↓reduceIte]
          · exact OracleComp.IsCostBounded.pure _ _
          · split_ifs <;> exact OracleComp.IsCostBounded.pure _ _
          · split_ifs <;> exact OracleComp.IsCostBounded.pure _ _
      | _ => exact OracleComp.IsCostBounded.pure _ _
    | deliverOpen o =>
      cases s₂ with
      | committed c =>
        by_cases h0 : (0 : Fin 2) ∈ C
        · simp only [h0, ↓reduceIte]; exact hverify c o
        · cases s₁ <;> simp only [h0, ↓reduceIte]
          · exact OracleComp.IsCostBounded.pure _ _
          · exact OracleComp.IsCostBounded.pure _ _
          · split_ifs
            · exact hverify c o
            · exact OracleComp.IsCostBounded.pure _ _
      | _ => exact OracleComp.IsCostBounded.pure _ _

end PlainCommitmentScheme

/-! ### Honest completeness and Canetti–Fischlin attack environments -/

section Environments

variable {CommitMsg OpenMsg : Type}

/-- Honest-execution environment (`C = ∅`) that instructs committer `0` to commit to `b`, forwards
the commit message `c` to receiver `1`, instructs committer `0` to open, forwards the opening
message `o` to receiver `1`, and checks whether receiver `1` outputs `some (.opened b)`. -/
@[expose] def honestCommitEnv (b : Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      (RoutedNetQ 2 CommitmentInput (PlainNetQ CommitMsg OpenMsg))
      (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg)) := fun _ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .commit b))
  let r₁ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readCommit))
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverCommit c)))
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .openCom))
    let r₂ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readOpen))
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let _ ← ProbOracleComp.query
        (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverOpen o)))
      let out ← ProbOracleComp.query
        (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
      return decide (out = some (.opened b))
    | _ => return false
  | _ => return false

private def plainRouterState [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) (C : Finset (Fin 2))
    (s₁ : CommitterState CommitMsg OpenMsg) (s₂ : ReceiverState CommitMsg) :
    (corruptRouter C (scheme.toProtocol κ C)).State := (s₁, s₂)

private theorem handle_plainRouter_commit [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) {C : Finset (Fin 2)}
    (h0 : (0 : Fin 2) ∉ C) (b : Bool) (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inl (0, .commit b))).run
      (plainRouterState scheme κ C .idle s₂) =
      (fun co => (none, plainRouterState scheme κ C (.committed co.1 co.2) s₂)) <$>
        ProbOracleComp.sample (scheme.commit κ b) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run]
  simp only [h0, ↓reduceIte, bind_pure_comp]

private theorem handle_plainRouter_openCom [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) {C : Finset (Fin 2)}
    (h0 : (0 : Fin 2) ∉ C) (c : CommitMsg) (o : OpenMsg) (s₂ : ReceiverState CommitMsg) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inl (0, .openCom))).run
      (plainRouterState scheme κ C (.committed c o) s₂) =
      pure (none, plainRouterState scheme κ C (.opened c o) s₂) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run]
  simp only [h0, ↓reduceIte]

private theorem handle_plainRouter_deliverCommit_of_notMem
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) {C : Finset (Fin 2)}
    (h0 : (0 : Fin 2) ∉ C) (c : CommitMsg) (o : OpenMsg) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inr (.inr (.deliverCommit c)))).run
      (plainRouterState scheme κ C (.committed c o) .waiting) =
      pure (Sum.inr .ack, plainRouterState scheme κ C (.committed c o) (.committed c)) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run,
    Functor.map, StateT.map]
  simp [h0]

private theorem handle_plainRouter_deliverOpen_of_notMem
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) {C : Finset (Fin 2)}
    (h0 : (0 : Fin 2) ∉ C) (c : CommitMsg) (o : OpenMsg) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inr (.inr (.deliverOpen o)))).run
      (plainRouterState scheme κ C (.opened c o) (.committed c)) =
      (fun res => (Sum.inr .ack, plainRouterState scheme κ C (.opened c o) (.finished res))) <$>
        ProbOracleComp.sample (scheme.verify κ c o) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run,
    Functor.map, StateT.map]
  simp [h0, bind_pure_comp]

private theorem handle_plainRouter_deliverOpen_of_mem
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) {C : Finset (Fin 2)}
    (h0 : (0 : Fin 2) ∈ C) (s₁ : CommitterState CommitMsg OpenMsg) (c : CommitMsg) (o : OpenMsg) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inr (.inr (.deliverOpen o)))).run
      (plainRouterState scheme κ C s₁ (.committed c)) =
      (fun res => (Sum.inr .ack, plainRouterState scheme κ C s₁ (.finished res))) <$>
        ProbOracleComp.sample (scheme.verify κ c o) := by
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run,
    Functor.map, StateT.map]
  simp [h0, bind_pure_comp]

private theorem handle_plainRouter_query_finished [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) {C : Finset (Fin 2)}
    (h1 : (1 : Fin 2) ∉ C) (s₁ : CommitterState CommitMsg OpenMsg) (res : Option Bool) :
    ((corruptRouter C (scheme.toProtocol κ C)).handle (Sum.inl (1, .query))).run
      (plainRouterState scheme κ C s₁ (.finished res)) =
      pure (res.map CommitmentOutput.opened, plainRouterState scheme κ C s₁ (.finished res)) := by
  have h10 : (1 : Fin 2) ≠ 0 := by decide
  dsimp only [corruptRouter, PlainCommitmentScheme.toProtocol, plainRouterState, StateT.run]
  cases res <;> simp only [h1, h10, ↓reduceIte, Option.map]

/-- Shared honest-committer `.commit b` followed by `.readCommit` step for `0 ∉ C`. -/
private theorem closeRunFrom_plainRouter_commit_readCommit
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (κ : ℕ) {C : Finset (Fin 2)}
    (h0 : (0 : Fin 2) ∉ C) (b : Bool)
    (cont : RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg) →
      ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
        (RoutedNetQ 2 CommitmentInput (PlainNetQ CommitMsg OpenMsg))
        (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg))) Bool) :
    closeRunFrom (corruptRouter C (scheme.toProtocol κ C))
      (ProbOracleComp.query (Sum.inl (0, .commit b)) >>= fun _ =>
        ProbOracleComp.query (Sum.inr (.inr .readCommit)) >>= cont)
      (plainRouterState scheme κ C .idle .waiting) =
      scheme.commit κ b >>= fun co =>
        closeRunFrom (corruptRouter C (scheme.toProtocol κ C))
          (cont (Sum.inr (.commitMsg (some co.1))))
          (plainRouterState scheme κ C (.committed co.1 co.2) .waiting) := by
  let M := corruptRouter C (scheme.toProtocol κ C)
  rw [closeRunFrom_query_sample M _ _ _ _ _ _ (handle_plainRouter_commit scheme κ h0 b .waiting)]
  refine bind_congr fun co => ?_
  exact closeRunFrom_query_pure M (Sum.inr (Sum.inr PlainNetQ.readCommit)) cont
    (plainRouterState scheme κ C (.committed co.1 co.2) .waiting)
    (Sum.inr (PlainNetR.commitMsg (some co.1)))
    (plainRouterState scheme κ C (.committed co.1 co.2) .waiting)

/-- With no corruptions (`C = ∅`) and `dummyAdversary`, running `honestCommitEnv b` on
`scheme.toProtocol` has the exact distribution `scheme.acceptGame κ b`. -/
theorem eval_exec_honestCommitEnv [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec scheme.toProtocol (dummyAdversary 2 _ _) ∅ (honestCommitEnv b) κ z).eval =
      scheme.acceptGame κ b := by
  have h0 : (0 : Fin 2) ∉ (∅ : Finset (Fin 2)) := by decide
  have h1 : (1 : Fin 2) ∉ (∅ : Finset (Fin 2)) := by decide
  let M := corruptRouter (∅ : Finset (Fin 2)) (scheme.toProtocol κ ∅)
  rw [exec_dummyAdversary,
    run_eq_closeRunFrom_of_init_pure M _ (plainRouterState scheme κ ∅ .idle .waiting)]
  dsimp only [honestCommitEnv, PlainCommitmentScheme.acceptGame]
  rw [closeRunFrom_plainRouter_commit_readCommit scheme κ h0 b]
  congr 1; refine bind_congr fun ⟨c, o⟩ => ?_
  dsimp only
  rw [closeRunFrom_query_pure M _ _ _ _ _
      (handle_plainRouter_deliverCommit_of_notMem scheme κ h0 c o),
    closeRunFrom_query_pure M _ _ _ _ _ (handle_plainRouter_openCom scheme κ h0 c o _),
    closeRunFrom_query_pure M _ _ _ (Sum.inr (.openMsg (some o)))
      (plainRouterState scheme κ ∅ (.opened c o) (.committed c)) rfl,
    closeRunFrom_query_sample M _ _ _ _ _ _
      (handle_plainRouter_deliverOpen_of_notMem scheme κ h0 c o)]
  refine bind_congr fun res => ?_
  rw [closeRunFrom_query_pure M _ _ _ _ _ (handle_plainRouter_query_finished scheme κ h1 _ res),
    closeRunFrom_pure]
  rcases res with _ | (_ | _) <;> cases b <;> rfl

/-- Canetti–Fischlin corrupted-receiver environment (`C = {1}`): honest committer `0` commits to
`b`, the environment reads the commit message `c` from the network, honest committer `0` opens, the
environment reads the opening message `o` from the network, and the environment runs honest receiver
verification `scheme.verify κ c o` internally to test whether `res = some b`. -/
def corruptReceiverEnv (scheme : PlainCommitmentScheme CommitMsg OpenMsg) (b : Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      (RoutedNetQ 2 CommitmentInput (PlainNetQ CommitMsg OpenMsg))
      (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg)) := fun κ _ => do
  let _ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .commit b))
  let r₁ ← ProbOracleComp.query
    (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readCommit))
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (0, .openCom))
    let r₂ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr .readOpen))
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let res ← ProbOracleComp.sample (scheme.verify κ c o)
      return decide (res = some b)
    | _ => return false
  | _ => return false

/-- If `scheme.verify` has polynomial call budget `pV`, then `corruptReceiverEnv scheme b` has
polynomial call budget `pV + 4`. -/
theorem corruptReceiverEnv_polyBounded {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (b : Bool) : (corruptReceiverEnv scheme b).PolyBounded (pV + 4) := fun κ z => by
  simp only [Polynomial.eval_add, Polynomial.eval_ofNat]
  have hinner : (corruptReceiverEnv scheme b κ z).IsQueryBounded
      (1 + (1 + (1 + (1 + pV.eval κ)))) := by
    dsimp only [corruptReceiverEnv]
    refine (OracleComp.IsCostBounded.query _).bind fun _ =>
      (OracleComp.IsCostBounded.query _).bind fun r₁ => ?_
    rcases r₁ with _ | ⟨⟨_ | c⟩ | _ | _⟩ <;>
      try exact OracleComp.IsCostBounded.pure _ (1 + (1 + pV.eval κ))
    refine (OracleComp.IsCostBounded.query _).bind fun _ =>
      (OracleComp.IsCostBounded.query _).bind fun r₂ => ?_
    rcases r₂ with _ | ⟨_ | ⟨_ | o⟩ | _⟩ <;> try exact OracleComp.IsCostBounded.pure _ (pV.eval κ)
    simpa only [bind_pure_comp, OracleComp.isCostBounded_map_iff] using
      Machine.isQueryBounded_sample (hV κ c o)
  exact hinner.mono (by omega)

/-- In the real execution with `C = {1}` and `dummyAdversary`, `corruptReceiverEnv scheme b`
evaluates to `scheme.acceptGame κ b`. -/
theorem eval_exec_real_corruptReceiverEnv [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z : List Bool) :
    (exec scheme.toProtocol (dummyAdversary 2 _ _) {1} (corruptReceiverEnv scheme b) κ z).eval =
      scheme.acceptGame κ b := by
  have h01 : (0 : Fin 2) ∉ ({1} : Finset (Fin 2)) := by decide
  let M := corruptRouter ({1} : Finset (Fin 2)) (scheme.toProtocol κ {1})
  rw [exec_dummyAdversary,
    run_eq_closeRunFrom_of_init_pure M _ (plainRouterState scheme κ {1} .idle .waiting)]
  dsimp only [corruptReceiverEnv, PlainCommitmentScheme.acceptGame]
  rw [closeRunFrom_plainRouter_commit_readCommit scheme κ h01 b]
  congr 1; refine bind_congr fun ⟨c, o⟩ => ?_
  dsimp only
  rw [closeRunFrom_query_pure M _ _ _ _ _ (handle_plainRouter_openCom scheme κ h01 c o .waiting),
    closeRunFrom_query_pure M _ _ _ (Sum.inr (.openMsg (some o)))
      (plainRouterState scheme κ {1} (.opened c o) .waiting) rfl,
    closeRunFrom_sample]
  rfl

/-- Pre-open commit simulation of a simulator `S₁` for `C = {1}` against `fcomCommittedView`. -/
private def simCommit (S₁ : PlainCommitmentSim CommitMsg OpenMsg) (κ : ℕ) :
    ProbComp ((RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg) × (S₁ κ {1}).State) ×
      fcomCommittedView.State) := do
  let st₀ ← (S₁ κ {1}).init
  Machine.closeProgram
    (fcomCommittedView.runFrom (((S₁ κ {1}).handle (.inr .readCommit)).run st₀)
      (show fcomCommittedView.State from false))

/-- Post-open opening simulation of `S₁` for `C = {1}` from post-commit state `(st₁, recDel₁)` when
`fcom` has opened bit `b`. -/
private def simOpen (S₁ : PlainCommitmentSim CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (st₁ : (S₁ κ {1}).State) (recDel₁ : Bool) :
    ProbComp (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg)) :=
  (Prod.fst ∘ Prod.fst) <$> Machine.closeProgram
    ((corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
      (liftNet (((S₁ κ {1}).handle (.inr .readOpen)).run st₁))
      (show (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).State from
        .opened b recDel₁))

private theorem isQueryBounded_simCommit {S₁ : PlainCommitmentSim CommitMsg OpenMsg} {κ t : ℕ}
    (hS : (S₁ κ {1}).IsBounded t) : (simCommit S₁ κ).IsQueryBounded (2 * t) := by
  have hinner : (simCommit S₁ κ).IsQueryBounded (t + t) := by
    refine hS.1.bind fun st₀ => ?_
    have hrun := Machine.isQueryBounded_runFrom fcomCommittedView_isBounded
      (hS.2 (.inr .readCommit) st₀) (show fcomCommittedView.State from false)
    rw [Nat.mul_one] at hrun
    exact Machine.isQueryBounded_closeProgram hrun
  exact hinner.mono (by omega)

private theorem isQueryBounded_simOpen {S₁ : PlainCommitmentSim CommitMsg OpenMsg} {κ t : ℕ}
    (hS : (S₁ κ {1}).IsBounded t) (b : Bool) (st₁ : (S₁ κ {1}).State) (recDel₁ : Bool) :
    (simOpen S₁ b κ st₁ recDel₁).IsQueryBounded t := by
  refine (OracleComp.isCostBounded_map_iff _ _ _).mpr ?_
  have hrun := Machine.isQueryBounded_runFrom (isBounded_corruptRouter {1} (fcom_isBounded κ {1}))
    (Machine.isQueryBounded_liftRightProgram _ (hS.2 (.inr .readOpen) st₁))
    (.opened b recDel₁)
  rw [Nat.mul_one] at hrun
  exact Machine.isQueryBounded_closeProgram hrun

private def corruptCommitterPrefix (S₁ : PlainCommitmentSim CommitMsg OpenMsg) (κ : ℕ) :
    ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
      (RoutedNetQ 2 CommitmentInput (PlainNetQ CommitMsg OpenMsg))
      (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg)))
      (Option ((S₁ κ {1}).State × Bool)) := do
  let ((r₁, st₁), recDel₁) ← ProbOracleComp.sample (simCommit S₁ κ)
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let _ ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inr (.inr (.deliverCommit c)))
    return some (st₁, recDel₁)
  | _ => return none

private def corruptCommitterSuffix (S₁ : PlainCommitmentSim CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) :
    Option ((S₁ κ {1}).State × Bool) →
    ProbOracleComp (execSpec 2 CommitmentInput CommitmentOutput
      (RoutedNetQ 2 CommitmentInput (PlainNetQ CommitMsg OpenMsg))
      (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg))) Bool
  | some (st₁, recDel₁) => do
    let recOut ← ProbOracleComp.query
      (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
    if recOut = some .receipt then
      let r₂ ← ProbOracleComp.sample (simOpen S₁ b κ st₁ recDel₁)
      match r₂ with
      | .inr (.openMsg (some o)) =>
        let _ ← ProbOracleComp.query
          (spec := execSpec 2 CommitmentInput CommitmentOutput _ _)
          (Sum.inr (.inr (.deliverOpen o)))
        let openOut ← ProbOracleComp.query
          (spec := execSpec 2 CommitmentInput CommitmentOutput _ _) (Sum.inl (1, .query))
        return decide (openOut = some (.opened b))
      | _ => return false
    else
      return false
  | none => return false

/-- Canetti–Fischlin corrupted-committer equivocation environment (`C = {0}`): runs `S₁`'s
bit-independent commit simulation, delivers the resulting commit message to honest receiver `1`,
checks that `1` outputs `some .receipt`, runs `S₁`'s opening simulation for bit `b`, delivers the
opening message, and checks whether `1` outputs `some (.opened b)`. -/
def corruptCommitterEnv (S₁ : PlainCommitmentSim CommitMsg OpenMsg) (b : Bool) :
    Environment 2 CommitmentInput CommitmentOutput
      (RoutedNetQ 2 CommitmentInput (PlainNetQ CommitMsg OpenMsg))
      (RoutedNetR CommitmentOutput (PlainNetR CommitMsg OpenMsg)) := fun κ _ => do
  let pre ← corruptCommitterPrefix S₁ κ
  corruptCommitterSuffix S₁ b κ pre

/-- If `S₁` at `C = {1}` has polynomial call budget `pS`, then `corruptCommitterEnv S₁ b` has
polynomial call budget `3 * pS + 4`. -/
theorem corruptCommitterEnv_polyBounded {S₁ : PlainCommitmentSim CommitMsg OpenMsg}
    {pS : Polynomial ℕ} (hS : ∀ κ, (S₁ κ {1}).IsBounded (pS.eval κ)) (b : Bool) :
    (corruptCommitterEnv S₁ b).PolyBounded (3 * pS + 4) := fun κ _ => by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, corruptCommitterEnv]
  have hpre : (corruptCommitterPrefix S₁ κ).IsQueryBounded (2 * pS.eval κ + 1) := by
    refine (Machine.isQueryBounded_sample (isQueryBounded_simCommit (hS κ))).bind ?_
    rintro ⟨⟨r₁, st₁⟩, recDel₁⟩
    rcases r₁ with _ | ⟨⟨_ | c⟩ | _ | _⟩ <;> try exact OracleComp.IsCostBounded.pure _ 1
    simp only [bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
  have hsuf (pre : Option ((S₁ κ {1}).State × Bool)) :
      (corruptCommitterSuffix S₁ b κ pre).IsQueryBounded (pS.eval κ + 3) := by
    rcases pre with _ | ⟨st₁, recDel₁⟩
    · exact OracleComp.IsCostBounded.pure false (pS.eval κ + 3)
    · have hinner : (corruptCommitterSuffix S₁ b κ (some (st₁, recDel₁))).IsQueryBounded
          (1 + (pS.eval κ + (1 + 1))) := by
        refine (OracleComp.IsCostBounded.query _).bind fun recOut => ?_
        change OracleComp.IsQueryBounded
          (if recOut = some CommitmentOutput.receipt then _ else _) (pS.eval κ + (1 + 1))
        split_ifs
        · refine (Machine.isQueryBounded_sample (isQueryBounded_simOpen (hS κ) b st₁ recDel₁)).bind
            fun r₂ => ?_
          rcases r₂ with _ | ⟨_ | ⟨_ | o⟩ | _⟩ <;> try exact OracleComp.IsCostBounded.pure _ (1 + 1)
          refine (OracleComp.IsCostBounded.query _).bind fun _ => ?_
          simp only [bind_pure_comp]
          exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
        · exact OracleComp.IsCostBounded.pure _ (pS.eval κ + (1 + 1))
      exact hinner.mono (by omega)
  exact (hpre.bind hsuf).mono (by omega)

private def simulatedTranscriptGame (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : PlainCommitmentSim CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) : ProbComp Bool := do
  let ((r₁, st₁), recDel₁) ← simCommit S₁ κ
  match r₁ with
  | .inr (.commitMsg (some c)) =>
    let r₂ ← simOpen S₁ b κ st₁ recDel₁
    match r₂ with
    | .inr (.openMsg (some o)) =>
      let res ← scheme.verify κ c o
      return decide (res = some b)
    | _ => return false
  | _ => return false

private def fcomExecState {AdvQ AdvR : Type}
    (S : FcomAdversary AdvQ AdvR) (κ : ℕ) (C : Finset (Fin 2))
    (st : (S κ C).State) (s : CommitmentState) :
    (execMachine fcom.toProtocol S κ C).State := (st, s)

private theorem init_execMachine_fcom {AdvQ AdvR : Type}
    (S : FcomAdversary AdvQ AdvR) (κ : ℕ) (C : Finset (Fin 2)) :
    (execMachine fcom.toProtocol S κ C).init =
      (fun sA => fcomExecState S κ C sA .idle) <$> (S κ C).init := by
  simp only [execMachine, Machine.comp, liftAdversary, Machine.liftRight, corruptRouter, fcom,
    IdealFunctionality.toProtocol, fcomExecState, pure_bind, bind_pure_comp]

private theorem handle_execMachine_fcom_committed_inr {AdvQ AdvR : Type}
    (S₁ : FcomAdversary AdvQ AdvR)
    (b : Bool) (κ : ℕ) (q : AdvQ) (st₀ : (S₁ κ {1}).State) (recDel : Bool) :
    ((execMachine fcom.toProtocol S₁ κ {1}).handle (Sum.inr q)).run
      (fcomExecState S₁ κ {1} st₀ (.committed b recDel)) =
      (fun x : (AdvR × (S₁ κ {1}).State) × fcomCommittedView.State =>
        ((x.1.1 : execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR (Sum.inr q)),
          fcomExecState S₁ κ {1} x.1.2 (.committed b x.2))) <$>
        fcomCommittedView.runFrom (((S₁ κ {1}).handle q).run st₀)
          (show fcomCommittedView.State from recDel) := by
  change Equiv.prodAssoc _ _ _ <$>
    (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
      (liftNet (((S₁ κ {1}).handle q).run st₀)) (.committed b recDel) = _
  rw [runFrom_fcom_committed κ b, Functor.map_map]
  rfl

private theorem handle_execMachine_fcom_opened_inr {AdvQ AdvR : Type}
    (S₁ : FcomAdversary AdvQ AdvR)
    (b : Bool) (κ : ℕ) (q : AdvQ) (st₁ : (S₁ κ {1}).State) (recDel₁ : Bool) :
    ((execMachine fcom.toProtocol S₁ κ {1}).handle (Sum.inr q)).run
      (fcomExecState S₁ κ {1} st₁ (.opened b recDel₁)) =
      (fun x : (AdvR × (S₁ κ {1}).State) ×
          (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).State =>
        ((x.1.1 : execSpec 2 CommitmentInput CommitmentOutput AdvQ AdvR (Sum.inr q)),
          fcomExecState S₁ κ {1} x.1.2 x.2)) <$>
        (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).runFrom
          (liftNet (((S₁ κ {1}).handle q).run st₁))
          (show (corruptRouter ({1} : Finset (Fin 2)) (fcom.toProtocol κ {1})).State from
            .opened b recDel₁) := rfl

private theorem exec_fcom_corruptReceiverEnv_eq (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : PlainCommitmentSim CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z : List Bool) :
    exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z =
      simulatedTranscriptGame scheme S₁ b κ := by
  let M := execMachine fcom.toProtocol S₁ κ {1}
  rw [exec, run_eq_bind_closeRunFrom, init_execMachine_fcom, bind_map_left]
  simp only [simulatedTranscriptGame, simCommit, simOpen, bind_assoc]
  refine bind_congr fun st₀ => ?_
  dsimp only [corruptReceiverEnv]
  rw [closeRunFrom_query_pure M _ _ (fcomExecState S₁ κ {1} st₀ .idle) none
      (fcomExecState S₁ κ {1} st₀ (.committed b false)) rfl,
    closeRunFrom_query_bind M, handle_execMachine_fcom_committed_inr,
    Machine.closeProgram_map, bind_map_left]
  refine bind_congr fun ⟨⟨r₁, st₁⟩, (recDel₁ : Bool)⟩ => ?_
  rcases r₁ with _ | ⟨⟨_ | c⟩ | _ | _⟩ <;> try rfl
  dsimp only
  rw [closeRunFrom_query_pure M _ _ (fcomExecState S₁ κ {1} st₁ (.committed b recDel₁)) none
      (fcomExecState S₁ κ {1} st₁ (.opened b recDel₁)) rfl,
    closeRunFrom_query_bind M, handle_execMachine_fcom_opened_inr,
    Machine.closeProgram_map, bind_map_left, bind_map_left]
  refine bind_congr fun ⟨⟨r₂, _⟩, _⟩ => ?_
  rcases r₂ with _ | ⟨_ | ⟨_ | o⟩ | _⟩ <;> try rfl
  dsimp only [Function.comp_def]
  rw [closeRunFrom_sample]
  rfl

private theorem exec_real_corruptCommitterEnv_eq [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : PlainCommitmentSim CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z : List Bool) :
    exec scheme.toProtocol (dummyAdversary 2 _ _) {0} (corruptCommitterEnv S₁ b) κ z =
      simulatedTranscriptGame scheme S₁ b κ := by
  have h0 : (0 : Fin 2) ∈ ({0} : Finset (Fin 2)) := by decide
  have h1 : (1 : Fin 2) ∉ ({0} : Finset (Fin 2)) := by decide
  let M := corruptRouter ({0} : Finset (Fin 2)) (scheme.toProtocol κ {0})
  rw [exec_dummyAdversary,
    run_eq_closeRunFrom_of_init_pure M _ (plainRouterState scheme κ {0} .idle .waiting)]
  simp only [corruptCommitterEnv, corruptCommitterPrefix, simulatedTranscriptGame, bind_assoc]
  rw [closeRunFrom_sample]
  refine bind_congr fun ⟨⟨r₁, st₁⟩, recDel₁⟩ => ?_
  rcases r₁ with _ | ⟨⟨_ | c⟩ | _ | _⟩ <;> try rfl
  simp only [pure_bind, bind_assoc]
  rw [closeRunFrom_query_pure M _ _ (plainRouterState scheme κ {0} .idle .waiting) (Sum.inr .ack)
      (plainRouterState scheme κ {0} .idle (.committed c)) rfl]
  simp only [corruptCommitterSuffix]
  rw [closeRunFrom_query_pure M _ _ (plainRouterState scheme κ {0} .idle (.committed c))
      (some .receipt) (plainRouterState scheme κ {0} .idle (.committed c)) rfl]
  simp only [↓reduceIte]
  rw [closeRunFrom_sample]
  refine bind_congr fun r₂ => ?_
  rcases r₂ with _ | ⟨_ | ⟨_ | o⟩ | _⟩ <;> try rfl
  dsimp only
  rw [closeRunFrom_query_sample M _ _ _ _ _ _
      (handle_plainRouter_deliverOpen_of_mem scheme κ h0 .idle c o)]
  refine bind_congr fun res => ?_
  rw [closeRunFrom_query_pure M _ _ _ _ _ (handle_plainRouter_query_finished scheme κ h1 .idle res),
    closeRunFrom_pure]
  rcases res with _ | (_ | _) <;> cases b <;> rfl

/-- Plain-model man-in-the-middle equivocation identity: the real execution of
`corruptCommitterEnv S₁ b` (`C = {0}`) with `dummyAdversary` equals the ideal execution of
`corruptReceiverEnv scheme b` (`C = {1}`) with simulator `S₁`. -/
theorem exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv
    [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ : PlainCommitmentSim CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z₁ z₂ : List Bool) :
    exec scheme.toProtocol (dummyAdversary 2 _ _) {0} (corruptCommitterEnv S₁ b) κ z₁ =
      exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z₂ := by
  rw [exec_real_corruptCommitterEnv_eq, exec_fcom_corruptReceiverEnv_eq]

/-! ### Ideal-world binding bound for `corruptCommitterEnv` -/

private def fcomLockedReply (bStar : Bool) (phase : CommitmentPhase) :
    Option CommitmentOutput :=
  if phase.openDelivered then
    some (.opened bStar)
  else if phase.recDelivered then
    some .receipt
  else
    none

private def fcomLockedState {AdvQ AdvR : Type}
    (S₀ : FcomAdversary AdvQ AdvR) (bStar : Bool) (κ : ℕ)
    (st : (S₀ κ {0}).State) (phase : CommitmentPhase) :
    ((liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))).State :=
  (st, phase)

private theorem handle_fcomLocked_query_one {AdvQ AdvR : Type}
    (S₀ : FcomAdversary AdvQ AdvR)
    (bStar : Bool) (κ : ℕ) (st : (S₀ κ {0}).State) (phase : CommitmentPhase) :
    (((liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))).handle
      (Sum.inl (1, .query))).run (fcomLockedState S₀ bStar κ st phase) =
      pure (fcomLockedReply bStar phase, fcomLockedState S₀ bStar κ st phase) := by
  rcases phase with ⟨_ | _, _ | _, _ | _⟩ <;> rfl

private theorem eval_corruptCommitterSuffix_locked_not
    (S₁ S₀ : PlainCommitmentSim CommitMsg OpenMsg)
    (bStar : Bool) (κ : ℕ) (st₁ : (S₁ κ {1}).State) (recDel₁ : Bool)
    (stS₀ : (S₀ κ {0}).State) (phase : CommitmentPhase) :
    (closeRunFrom (execMachine fcom.toProtocol S₀ κ {0})
      (corruptCommitterSuffix S₁ (!bStar) κ (some (st₁, recDel₁)))
      (fcomExecState S₀ κ {0} stS₀ (.active bStar phase))).eval = PMF.pure false := by
  let L := (liftAdversary (S₀ κ {0})).comp (corruptRouter {0} (fcomLocked bStar))
  have hlock : closeRunFrom (execMachine fcom.toProtocol S₀ κ {0})
      (corruptCommitterSuffix S₁ (!bStar) κ (some (st₁, recDel₁)))
      (fcomExecState S₀ κ {0} stS₀ (.active bStar phase)) =
      closeRunFrom L (corruptCommitterSuffix S₁ (!bStar) κ (some (st₁, recDel₁)))
        (fcomLockedState S₀ bStar κ stS₀ phase) := by
    dsimp only [closeRunFrom, fcomExecState]
    rw [runFrom_execMachine_fcom_locked S₀ κ {0} bStar _ stS₀ phase]
    erw [Machine.closeProgram_map, Functor.map_map]
    rfl
  rw [hlock]
  dsimp only [corruptCommitterSuffix]
  rw [closeRunFrom_query_pure L _ _ _ _ _ (handle_fcomLocked_query_one S₀ bStar κ stS₀ phase)]
  split_ifs with hrec
  · rw [closeRunFrom_sample, ProbComp.eval_bind]
    refine (bind_congr (g := fun _ => PMF.pure false) fun r₂ => ?_).trans (PMF.bind_const _ _)
    rcases r₂ with _ | ⟨_ | ⟨_ | o⟩ | _⟩ <;> try rfl
    dsimp only
    rw [closeRunFrom_query_bind L, ProbComp.eval_bind]
    refine (bind_congr (g := fun _ => PMF.pure false) fun ⟨_, stL⟩ => ?_).trans
      (PMF.bind_const _ _)
    let stS₀' : (S₀ κ {0}).State := stL.1
    let phase' : CommitmentPhase := stL.2
    change (closeRunFrom L _ (fcomLockedState S₀ bStar κ stS₀' phase')).eval = PMF.pure false
    rw [closeRunFrom_query_pure L _ _ _ _ _ (handle_fcomLocked_query_one S₀ bStar κ stS₀' phase'),
      closeRunFrom_pure]
    rcases phase' with ⟨_ | _, _ | _, _ | _⟩ <;> cases bStar <;> rfl
  · rfl

private theorem succProbability_corruptCommitterSuffix_add_le_one
    (S₁ S₀ : PlainCommitmentSim CommitMsg OpenMsg) (κ : ℕ)
    (x : Option ((S₁ κ {1}).State × Bool) × (execMachine fcom.toProtocol S₀ κ {0}).State) :
    Game.succProbability
      (closeRunFrom (execMachine fcom.toProtocol S₀ κ {0})
        (corruptCommitterSuffix S₁ false κ x.1) x.2).eval +
    Game.succProbability
      (closeRunFrom (execMachine fcom.toProtocol S₀ κ {0})
        (corruptCommitterSuffix S₁ true κ x.1) x.2).eval ≤ 1 := by
  let M₀ := execMachine fcom.toProtocol S₀ κ {0}
  rcases x with ⟨pre, st⟩
  let stS₀ : (S₀ κ {0}).State := st.1
  let sP : CommitmentState := st.2
  change Game.succProbability
      (closeRunFrom M₀ (corruptCommitterSuffix S₁ false κ pre)
        (fcomExecState S₀ κ {0} stS₀ sP)).eval +
    Game.succProbability
      (closeRunFrom M₀ (corruptCommitterSuffix S₁ true κ pre)
        (fcomExecState S₀ κ {0} stS₀ sP)).eval ≤ 1
  clear_value stS₀ sP; clear st
  rcases pre with _ | ⟨st₁, recDel₁⟩
  · simp [corruptCommitterSuffix, closeRunFrom, Game.succProbability, PMF.pure_apply]
  · rcases sP with _ | ⟨bStar, phase⟩
    · dsimp only [corruptCommitterSuffix]
      rw [closeRunFrom_query_pure M₀ _ _ (fcomExecState S₀ κ {0} stS₀ .idle) none
          (fcomExecState S₀ κ {0} stS₀ .idle) rfl,
        closeRunFrom_query_pure M₀ _ _ (fcomExecState S₀ κ {0} stS₀ .idle) none
          (fcomExecState S₀ κ {0} stS₀ .idle) rfl]
      simp [Game.succProbability, PMF.pure_apply]
    · cases bStar
      · have htrue := eval_corruptCommitterSuffix_locked_not S₁ S₀ false κ st₁ recDel₁ stS₀ phase
        simp only [Bool.not_false] at htrue
        rw [htrue]
        simpa [Game.succProbability, PMF.pure_apply] using Game.succProbability_le_one _
      · have hfalse := eval_corruptCommitterSuffix_locked_not S₁ S₀ true κ st₁ recDel₁ stS₀ phase
        simp only [Bool.not_true] at hfalse
        rw [hfalse]
        simpa [Game.succProbability, PMF.pure_apply] using Game.succProbability_le_one _

private theorem succProbability_bind_add_le_one {α : Type} (μ : PMF α) (g₁ g₂ : α → Game)
    (h : ∀ x, Game.succProbability (g₁ x) + Game.succProbability (g₂ x) ≤ 1) :
    Game.succProbability (μ.bind g₁) + Game.succProbability (μ.bind g₂) ≤ 1 := by
  have hpt (x : α) : g₁ x true + g₂ x true ≤ 1 := by
    rw [← ENNReal.coe_toNNReal (PMF.apply_ne_top (g₁ x) true),
      ← ENNReal.coe_toNNReal (PMF.apply_ne_top (g₂ x) true), ← ENNReal.coe_add]
    exact ENNReal.coe_le_one_iff.mpr (h x)
  have hsum : (μ.bind g₁) true + (μ.bind g₂) true ≤ 1 := by
    rw [PMF.bind_apply, PMF.bind_apply, ← tsum_add]
    simpa only [← mul_add] using Cslib.Probability.PMF.tsum_mul_le_of_forall_le μ hpt
  dsimp only [Game.succProbability]
  rw [← ENNReal.toNNReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simpa only [ENNReal.toNNReal_one] using ENNReal.toNNReal_mono ENNReal.one_ne_top hsum

/-- Ideal-world binding inequality for `corruptCommitterEnv`: for every simulator `S₀` (`C = {0}`)
and every simulator `S₁` (`C = {1}`), the ideal success probabilities of
`corruptCommitterEnv S₁ false` and `corruptCommitterEnv S₁ true` against `fcom` sum to at most
`1`. -/
theorem succProbability_exec_fcom_corruptCommitterEnv_add_le_one
    (S₁ S₀ : PlainCommitmentSim CommitMsg OpenMsg)
    (κ : ℕ) (z₁ z₂ : List Bool) :
    Game.succProbability (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ false) κ z₁).eval +
      Game.succProbability (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ true) κ z₂).eval ≤
      1 := by
  let M₀ := execMachine fcom.toProtocol S₀ κ {0}
  let preDist : PMF (Option ((S₁ κ {1}).State × Bool) × M₀.State) :=
    (M₀.init >>= fun s₀ => Machine.closeProgram (M₀.runFrom (corruptCommitterPrefix S₁ κ) s₀)).eval
  let sufDist (b : Bool) (x : Option ((S₁ κ {1}).State × Bool) × M₀.State) : Game :=
    (closeRunFrom M₀ (corruptCommitterSuffix S₁ b κ x.1) x.2).eval
  have hexec (b : Bool) (z : List Bool) :
      (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ b) κ z).eval =
        preDist.bind (sufDist b) := by
    simp only [exec, run_eq_bind_closeRunFrom, closeRunFrom, corruptCommitterEnv, preDist, sufDist,
      M₀, Machine.runFrom_bind, Machine.closeProgram_bind, map_bind, ProbComp.eval_bind,
      PMF.bind_bind]
  rw [hexec false z₁, hexec true z₂]
  exact succProbability_bind_add_le_one preDist (sufDist false) (sufDist true)
    (succProbability_corruptCommitterSuffix_add_le_one S₁ S₀ κ)

/-! ### Canetti–Fischlin quantitative trade-off and impossibility theorems -/

private theorem acceptProb_le_ideal_add_advantage [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ S₀ : PlainCommitmentSim CommitMsg OpenMsg)
    (b : Bool) (κ : ℕ) (z₁ z₀ : List Bool) :
    scheme.acceptProb κ b ≤
      Game.succProbability (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ b) κ z₀).eval +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme b) κ z₁ +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ b) κ z₀ := by
  let gR₁ : Game :=
    (exec scheme.toProtocol (dummyAdversary 2 _ _) {1} (corruptReceiverEnv scheme b) κ z₁).eval
  let gI₁ : Game := (exec fcom.toProtocol S₁ {1} (corruptReceiverEnv scheme b) κ z₁).eval
  let gI₀ : Game := (exec fcom.toProtocol S₀ {0} (corruptCommitterEnv S₁ b) κ z₀).eval
  have h1 : Game.succProbability gR₁ ≤ Game.advantage gR₁ gI₁ + Game.succProbability gI₁ := by
    simpa only [Game.advantage_pure_false] using
      Game.advantage_triangle gR₁ gI₁ (PMF.pure false)
  have h2 : Game.succProbability gI₁ ≤ Game.advantage gI₁ gI₀ + Game.succProbability gI₀ := by
    simpa only [Game.advantage_pure_false] using
      Game.advantage_triangle gI₁ gI₀ (PMF.pure false)
  have heq : Game.advantage gI₁ gI₀ =
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ b) κ z₀ := by
    dsimp only [advantage, gI₁, gI₀]
    rw [exec_real_corruptCommitterEnv_eq_exec_fcom_corruptReceiverEnv scheme S₁ b κ z₀ z₁]
  have hR₁ : Game.succProbability gR₁ = scheme.acceptProb κ b := by
    dsimp only [PlainCommitmentScheme.acceptProb, gR₁]
    rw [eval_exec_real_corruptReceiverEnv]
  rw [← hR₁]
  calc Game.succProbability gR₁
      ≤ Game.advantage gR₁ gI₁ + (Game.advantage gI₁ gI₀ + Game.succProbability gI₀) :=
        h1.trans (add_le_add_right h2 _)
    _ = Game.succProbability gI₀ +
        advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
          (corruptReceiverEnv scheme b) κ z₁ +
        advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
          (corruptCommitterEnv S₁ b) κ z₀ := by
        rw [heq]; dsimp only [advantage, gR₁, gI₁]; ac_rfl

/-- Quantitative one-message plain-model trade-off in the statistical UC port model (after Theorem 6
of [CanettiFischlin2001]; #6043): for every `PlainCommitmentScheme`, every corrupted-receiver
simulator `S₁` (`C = {1}`), and every corrupted-committer simulator `S₀` (`C = {0}`), the sum of
the honest acceptance probabilities on `false` and `true` is bounded by `1` plus the four
dummy-adversary distinguishing advantages on `corruptReceiverEnv` and `corruptCommitterEnv`.
Allowing `S₁` and `S₀` to vary independently shows that the bound holds even when the simulator
depends on the static corruption set; setting `S₁ = S₀ = S_D` specializes to one UC simulator. -/
theorem acceptProb_add_le_one_add_advantage [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    (scheme : PlainCommitmentScheme CommitMsg OpenMsg)
    (S₁ S₀ : PlainCommitmentSim CommitMsg OpenMsg)
    (κ : ℕ) (z : List Bool) :
    scheme.acceptProb κ false + scheme.acceptProb κ true ≤
      1 +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₁ {1}
        (corruptReceiverEnv scheme true) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ false) κ z +
      advantage scheme.toProtocol fcom.toProtocol (dummyAdversary 2 _ _) S₀ {0}
        (corruptCommitterEnv S₁ true) κ z := by
  have hfalse := acceptProb_le_ideal_add_advantage scheme S₁ S₀ false κ z z
  have htrue := acceptProb_le_ideal_add_advantage scheme S₁ S₀ true κ z z
  have hideal := succProbability_exec_fcom_corruptCommitterEnv_add_le_one S₁ S₀ κ z z
  rw [← NNReal.coe_le_coe] at hfalse htrue hideal ⊢
  push_cast at hfalse htrue hideal ⊢
  linarith

/-- Concrete impossibility for `EmulatesDummyWithin`, this library's novel call-bounded
dummy-adversary emulation notion (#6043): if `scheme.verify` has polynomial call budget `pV` and at
security parameter `κ` the error bound `ε` satisfies
`1 + 2 * ε (pV + 4) κ + 2 * ε (3 * pD + 4) κ <
  scheme.acceptProb κ false + scheme.acceptProb κ true`,
then `scheme.toProtocol` does not emulate `fcom.toProtocol` against the dummy adversary within
`(pD, ε)`. -/
theorem not_emulatesDummyWithin_fcom [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0) (κ : ℕ)
    (hgap : 1 + 2 * ε (pV + 4) κ + 2 * ε (3 * pD + 4) κ <
      scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ EmulatesDummyWithin scheme.toProtocol fcom.toProtocol pD ε := by
  rintro ⟨S, hS_poly, hadv⟩
  have hS1 : ∀ κ', (S κ' {1}).IsBounded (pD.eval κ') := fun κ' => hS_poly κ' {1}
  have h1_false := hadv {1} (corruptReceiverEnv scheme false) (pV + 4)
    (corruptReceiverEnv_polyBounded hV false) κ []
  have h1_true := hadv {1} (corruptReceiverEnv scheme true) (pV + 4)
    (corruptReceiverEnv_polyBounded hV true) κ []
  have h0_false := hadv {0} (corruptCommitterEnv S false) (3 * pD + 4)
    (corruptCommitterEnv_polyBounded hS1 false) κ []
  have h0_true := hadv {0} (corruptCommitterEnv S true) (3 * pD + 4)
    (corruptCommitterEnv_polyBounded hS1 true) κ []
  have hbound := acceptProb_add_le_one_add_advantage scheme S S κ []
  have hle : scheme.acceptProb κ false + scheme.acceptProb κ true ≤
      1 + 2 * ε (pV + 4) κ + 2 * ε (3 * pD + 4) κ := by
    rw [← NNReal.coe_le_coe] at h1_false h1_true h0_false h0_true hbound ⊢
    push_cast at h1_false h1_true h0_false h0_true hbound ⊢
    linarith
  exact not_lt_of_ge hle hgap

/-- Concrete impossibility for `RealizesWithin`, this library's novel call-bounded realization
notion (#6043): if `scheme.verify` has polynomial call budget `pV` and at security parameter `κ`,
for every dummy-adversary simulator budget `pD` with `SimPolyBound g 1 pD`, the error bound `ε`
satisfies
`1 + 2 * ε 1 (pV + 4) κ + 2 * ε 1 (3 * pD + 4) κ <
  scheme.acceptProb κ false + scheme.acceptProb κ true`,
then `scheme.toProtocol` does not realize `fcom` within `(g, ε)`. -/
theorem not_realizesWithin_fcom [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) (κ : ℕ)
    (hgap : ∀ pD, SimPolyBound g 1 pD →
      1 + 2 * ε 1 (pV + 4) κ + 2 * ε 1 (3 * pD + 4) κ <
        scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ RealizesWithin scheme.toProtocol fcom g ε := by
  intro hreal
  obtain ⟨pD, hg, hdummy⟩ := hreal.emulatesDummyWithin
  exact not_emulatesDummyWithin_fcom hV pD (ε 1) κ (hgap pD hg) hdummy

/-- Statistical, call-bounded one-message plain-model commitment impossibility for `Realizes`, this
library's novel call-bounded static-corruption port-model notion (a special-case adaptation after
Theorem 6 of [CanettiFischlin2001], not that computational bilateral-protocol theorem; #6043): no
`PlainCommitmentScheme` whose verification is polynomial-call bounded and whose honest acceptance
probabilities on `false` and `true` eventually sum to at least `1 + c` (for a constant `c > 0`)
satisfies `Realizes scheme.toProtocol fcom`. See the module docstring for the scope relative to the
source theorem. -/
theorem not_realizes_fcom [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    {c : ℝ≥0} (hc : 0 < c)
    (hcomplete : ∀ᶠ κ in Filter.atTop,
      1 + c ≤ scheme.acceptProb κ false + scheme.acceptProb κ true) :
    ¬ Realizes scheme.toProtocol fcom := by
  intro hreal
  obtain ⟨S, pD, hS_poly, hsim⟩ := (emulates_iff_emulatesDummy _ _).mp hreal
  have hS1 : ∀ κ, (S κ {1}).IsBounded (pD.eval κ) := fun κ => hS_poly κ {1}
  obtain ⟨ε₁, hε₁_neg, hε₁⟩ := hsim (pV + 4)
  obtain ⟨ε₀, hε₀_neg, hε₀⟩ := hsim (3 * pD + 4)
  have hneg : Negligible (fun κ => 2 * ε₁ κ + 2 * ε₀ κ) :=
    (hε₁_neg.const_mul 2).add (hε₀_neg.const_mul 2)
  have ht : Filter.Tendsto (fun κ => 2 * ε₁ κ + 2 * ε₀ κ) Filter.atTop (nhds 0) := by
    simpa using hneg 0
  obtain ⟨κ, hκ_complete, hκ_lt⟩ := (hcomplete.and (ht.eventually_lt_const hc)).exists
  have h1_false := hε₁ {1} (corruptReceiverEnv scheme false)
    (corruptReceiverEnv_polyBounded hV false) κ []
  have h1_true := hε₁ {1} (corruptReceiverEnv scheme true)
    (corruptReceiverEnv_polyBounded hV true) κ []
  have h0_false := hε₀ {0} (corruptCommitterEnv S false)
    (corruptCommitterEnv_polyBounded hS1 false) κ []
  have h0_true := hε₀ {0} (corruptCommitterEnv S true)
    (corruptCommitterEnv_polyBounded hS1 true) κ []
  have hbound := acceptProb_add_le_one_add_advantage scheme S S κ []
  rw [← NNReal.coe_le_coe] at hκ_complete h1_false h1_true h0_false h0_true hbound
  rw [← NNReal.coe_lt_coe] at hκ_lt
  push_cast at hκ_complete hκ_lt h1_false h1_true h0_false h0_true hbound
  linarith

/-- Perfectly complete specialization of `not_realizes_fcom` for `Realizes`, this library's novel
call-bounded static-corruption port-model notion (after Theorem 6 of [CanettiFischlin2001]; #6043):
no perfectly complete `PlainCommitmentScheme` with polynomial-call bounded verification satisfies
`Realizes scheme.toProtocol fcom`. -/
theorem not_realizes_fcom_of_perfectlyComplete [DecidableEq CommitMsg] [DecidableEq OpenMsg]
    {scheme : PlainCommitmentScheme CommitMsg OpenMsg}
    {pV : Polynomial ℕ} (hV : ∀ κ c o, (scheme.verify κ c o).IsQueryBounded (pV.eval κ))
    (hcomplete : scheme.PerfectlyComplete) :
    ¬ Realizes scheme.toProtocol fcom := by
  refine not_realizes_fcom hV (c := 1) zero_lt_one (Filter.Eventually.of_forall fun κ => ?_)
  rw [hcomplete κ false, hcomplete κ true]

end Environments

end Cslib.Crypto.Protocols.UC

end
