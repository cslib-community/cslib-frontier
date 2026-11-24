/-
Copyright (c) 2026 Samuel Schlesinger, Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Adaptive

/-!
# Write-once non-erasing storage and coin exposure for adaptive UC

This module wraps an `AdaptiveProtocol` in an explicit append-only per-party log and
honest-coin exposure layer (`AdaptiveProtocol.withWriteOnce`), motivated by the non-erasing
party model of [Canetti2020], Section 7.1.1 (p. 28:71, as cited in
`CslibFrontier.Crypto.Protocols.UC.Adaptive`).

In the base snapshot model of `UC.Adaptive`, `AdaptiveProtocol.view` is an arbitrary
caller-supplied projection that may hide stored secrets (`View := Unit`) or omit coins drawn and
discarded within a single activation, while `recordSnapshot` appends snapshots for every party
after every activation (including `.net` calls and other parties' activations).

`AdaptiveProtocol.withWriteOnce P mem` augments `P`'s state to `WriteOnceState` by recording:
* `initCoins`: all `ProbComp.unifFin` draws consumed by `(P.machine κ).init`, and
* `tapes i`: an append-only oldest-first list of `PartyActivationRecord`s containing the input,
  output, every intra-activation `ProbComp.unifFin` draw (`coins : OracleComp.Transcript unifSpec`),
  and post-activation `P.view` snapshot for every `.inl (i, x)` activation of party `i`.

## Scope

This module extends the library's snapshot, call-bounded, fixed-`n`-party port model (`UC.Adaptive`;
#6043) and is **not** a formalization of full PPT interactive Turing machines with write-once
worktapes from [Canetti2020] §7.1.1:
* Budgets remain oracle-call counts (`PolyBounded`), not running times.
* `init : ProbComp State` is a single shared machine initializer (unlike per-party initializers), so
  its draws are stored in `WriteOnceState.initCoins` rather than attributed to individual party
  tapes `tapes i`.
* Both honest party calls (`.inl (.party i x)`) and adversary-driven calls on already-corrupted
  parties (`.inr (.party i x)`) invoke `(P.machine κ).handle (.inl (i, x))` behind `adaptiveRouter`,
  so both append to `tapes i`; up to corruption time, `tapes i` holds party `i`'s honest-phase
  inputs, outputs, coins, and views without leaking activation counts of parties `j ≠ i`.

## Main definitions

* `Cslib.Crypto.Protocols.UC.recordProbCoins`, `recordCoins`: non-intrusive `ProbComp.unifFin`
  tape instrumentation preserving execution distributions and query budgets.
* `Cslib.Crypto.Protocols.UC.PartyActivationRecord`, `WriteOnceState`, `WriteOnceView`,
  `AdaptiveProtocol.withWriteOnce`: write-once per-party tape and coin-exposure protocol wrapper.
* `Cslib.Crypto.Protocols.UC.WriteOnceState.TapePrefix`: per-party prefix ordering on tapes.
* `Cslib.Crypto.Protocols.UC.mapNetRAdversary`, `projectWriteOnceReport`,
  `dropWriteOnceTapeReport`: adversary wrappers projecting or dropping write-once tape entries.

## Main results

* `Cslib.Crypto.Protocols.UC.withWriteOnce_handle_inl_tapePrefix`,
  `withWriteOnce_handle_inr_tapes_eq`, `withWriteOnce_onCorrupt_tapes_eq`,
  `mem_support_closeEval_adaptiveRouter_withWriteOnce_tapePrefix`: prefix monotonicity of
  per-party write-once tapes across party calls, network calls, corruptions, and router runs.
* `Cslib.Crypto.Protocols.UC.AdaptiveProtocol.PolyBounded.withWriteOnce`,
  `runFrom_adaptiveRouter_withWriteOnce_noCorrupt`, `adaptiveExec_withWriteOnce_project`,
  `adaptiveExec_withWriteOnce_erasing`: call-budget preservation and exact execution equivalence
  under honest/uncorrupted runs and report projection/erasure.
* `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.of_writeOnce`,
  `AdaptiveEmulates.of_writeOnce`, `AdaptiveEmulatesWithin.erasing_of_writeOnce`,
  `AdaptiveEmulates.erasing_of_writeOnce`: emulation in the `.nonErasing` coin-exposing
  write-once model implies emulation in the projected / `.erasing` model.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Art. 28, 2020
  (ePrint 2000/067 of Feb 11, 2020): Section 7.1.1 (p. 28:71), non-erasing vs. erasing parties.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open Machine (closeEval closeEval_pure closeEval_bind closeEval_map closeEval_sample
  mem_support_closeEval_pure mem_support_closeEval_bind mem_support_closeEval_map)
open scoped NNReal

variable {n : ℕ} {In Out NetQ NetR View View₁ View₂ AdvQ AdvR : Type}
  {NetQ₂ NetR₂ : Type}

/-! ### Non-intrusive coin-tape instrumentation -/

section CoinTape

/-- Execute a closed probabilistic program starting from an initial coin `tape`, appending every
`ProbComp.unifFin k` draw `⟨k, r⟩` in oldest-first order. -/
@[expose] def recordProbCoinsFrom {α : Type} (tape : OracleComp.Transcript unifSpec)
    (program : ProbComp α) : ProbComp (α × OracleComp.Transcript unifSpec) :=
  (OracleComp.interpret (m := StateT (OracleComp.Transcript unifSpec) ProbComp)
    (fun (k : ℕ) (t : OracleComp.Transcript unifSpec) => do
      let r ← ProbComp.unifFin k
      pure (r, t ++ [Sigma.mk k r]))
    program).run tape

/-- Execute a closed probabilistic program while logging every `ProbComp.unifFin` draw in
oldest-first order. -/
@[expose] def recordProbCoins {α : Type} (program : ProbComp α) :
    ProbComp (α × OracleComp.Transcript unifSpec) :=
  recordProbCoinsFrom [] program

/-- Execute an `OracleSpec.empty`-imported private-coin program starting from an initial coin
`tape`, appending every `ProbComp.unifFin k` draw `⟨k, r⟩` in oldest-first order. -/
@[expose] def recordCoinsFrom {α : Type} (tape : OracleComp.Transcript unifSpec)
    (program : ProbOracleComp OracleSpec.empty α) :
    ProbOracleComp OracleSpec.empty (α × OracleComp.Transcript unifSpec) :=
  (OracleComp.interpret
    (m := StateT (OracleComp.Transcript unifSpec) (ProbOracleComp OracleSpec.empty))
    (sumHandler
      (fun (k : ℕ) (t : OracleComp.Transcript unifSpec) => do
        let r ← ProbOracleComp.sample (ProbComp.unifFin k)
        pure (r, t ++ [Sigma.mk k r]))
      fun (q : Empty) => q.elim)
    program).run tape

/-- Execute an `OracleSpec.empty`-imported private-coin program while logging every
`ProbComp.unifFin` draw in oldest-first order. -/
@[expose] def recordCoins {α : Type} (program : ProbOracleComp OracleSpec.empty α) :
    ProbOracleComp OracleSpec.empty (α × OracleComp.Transcript unifSpec) :=
  recordCoinsFrom [] program

@[simp] theorem recordProbCoinsFrom_pure {α : Type} (tape : OracleComp.Transcript unifSpec)
    (a : α) : recordProbCoinsFrom tape (pure a) = pure (a, tape) := rfl

theorem recordProbCoinsFrom_bind {α β : Type} (tape : OracleComp.Transcript unifSpec)
    (program : ProbComp α) (next : α → ProbComp β) :
    recordProbCoinsFrom tape (program >>= next) =
      recordProbCoinsFrom tape program >>= fun p => recordProbCoinsFrom p.2 (next p.1) := by
  dsimp only [recordProbCoinsFrom]
  rw [OracleComp.interpret_bind, StateT.run_bind]

@[simp] theorem recordProbCoinsFrom_unifFin (tape : OracleComp.Transcript unifSpec) (k : ℕ) :
    recordProbCoinsFrom tape (ProbComp.unifFin k) =
      (fun r => (r, tape ++ [⟨k, r⟩])) <$> ProbComp.unifFin k := by
  dsimp only [recordProbCoinsFrom]
  rw [ProbComp.unifFin, OracleComp.interpret_query]
  exact bind_pure_comp _ _

@[simp] theorem recordCoinsFrom_pure {α : Type} (tape : OracleComp.Transcript unifSpec)
    (a : α) : recordCoinsFrom tape (pure a) = pure (a, tape) := rfl

theorem recordCoinsFrom_bind {α β : Type} (tape : OracleComp.Transcript unifSpec)
    (program : ProbOracleComp OracleSpec.empty α)
    (next : α → ProbOracleComp OracleSpec.empty β) :
    recordCoinsFrom tape (program >>= next) =
      recordCoinsFrom tape program >>= fun p => recordCoinsFrom p.2 (next p.1) := by
  dsimp only [recordCoinsFrom]
  rw [OracleComp.interpret_bind, StateT.run_bind]

@[simp] theorem recordCoinsFrom_sample_unifFin (tape : OracleComp.Transcript unifSpec) (k : ℕ) :
    recordCoinsFrom tape (ProbOracleComp.sample (ProbComp.unifFin k)) =
      (fun r => (r, tape ++ [⟨k, r⟩])) <$> ProbOracleComp.sample (ProbComp.unifFin k) := by
  dsimp only [recordCoinsFrom, ProbOracleComp.sample]
  rw [ProbComp.unifFin, OracleComp.substitute_query, OracleComp.interpret_query]
  exact bind_pure_comp _ _

private theorem fst_map_recordProbCoinsFrom {α : Type} (tape : OracleComp.Transcript unifSpec)
    (program : ProbComp α) :
    Prod.fst <$> recordProbCoinsFrom tape program = program := by
  induction program using OracleComp.induction generalizing tape with
  | pure a => simp only [recordProbCoinsFrom_pure, map_pure]
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind, recordProbCoinsFrom_bind]
    have hq : recordProbCoinsFrom tape (OracleComp.query q) =
        (fun r => (r, tape ++ [⟨q, r⟩])) <$> ProbComp.unifFin q :=
      recordProbCoinsFrom_unifFin tape q
    rw [hq, bind_map_left, map_bind]
    exact bind_congr fun r => ih r (tape ++ [⟨q, r⟩])

/-- Forgetting the recorded coin tape from `recordProbCoins` recovers the original closed program
identically. -/
theorem fst_map_recordProbCoins {α : Type} (program : ProbComp α) :
    Prod.fst <$> recordProbCoins program = program :=
  fst_map_recordProbCoinsFrom [] program

private theorem fst_map_recordCoinsFrom {α : Type} (tape : OracleComp.Transcript unifSpec)
    (program : ProbOracleComp OracleSpec.empty α) :
    Prod.fst <$> recordCoinsFrom tape program = program := by
  induction program using OracleComp.induction generalizing tape with
  | pure a => simp only [recordCoinsFrom_pure, map_pure]
  | query_bind q cont ih =>
    rw [PFunctor.FreeM.bind_eq_bind, recordCoinsFrom_bind]
    rcases q with k | q
    · have hq : recordCoinsFrom tape (OracleComp.query (Sum.inl k)) =
          (fun r => (r, tape ++ [⟨k, r⟩])) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
        recordCoinsFrom_sample_unifFin tape k
      rw [hq, bind_map_left, map_bind]
      exact bind_congr fun r => ih r (tape ++ [⟨k, r⟩])
    · exact q.elim

/-- Forgetting the recorded coin tape from `recordCoins` recovers the original program
identically. -/
theorem fst_map_recordCoins {α : Type} (program : ProbOracleComp OracleSpec.empty α) :
    Prod.fst <$> recordCoins program = program :=
  fst_map_recordCoinsFrom [] program

private theorem isQueryBounded_recordProbCoinsFrom {α : Type}
    (tape : OracleComp.Transcript unifSpec) {program : ProbComp α} {m : ℕ}
    (h : program.IsQueryBounded m) : (recordProbCoinsFrom tape program).IsQueryBounded m := by
  induction program using OracleComp.induction generalizing tape m with
  | pure a => simp only [recordProbCoinsFrom_pure]; exact OracleComp.IsCostBounded.pure _ m
  | query_bind q cont ih =>
    obtain ⟨hm, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h
    rw [PFunctor.FreeM.bind_eq_bind, recordProbCoinsFrom_bind]
    have hq : recordProbCoinsFrom tape (OracleComp.query q) =
        (fun r => (r, tape ++ [⟨q, r⟩])) <$> ProbComp.unifFin q :=
      recordProbCoinsFrom_unifFin tape q
    rw [hq, bind_map_left]
    have hstep : (ProbComp.unifFin q >>= fun r =>
          recordProbCoinsFrom (tape ++ [⟨q, r⟩]) (cont r)).IsQueryBounded ((m - 1) + 1) :=
      OracleComp.IsCostBounded.liftBind q
        (fun r => recordProbCoinsFrom (tape ++ [⟨q, r⟩]) (cont r)) (m - 1)
        (fun r => ih r (tape ++ [⟨q, r⟩]) (hcont r))
    simpa only [Nat.sub_add_cancel hm] using hstep

/-- `recordProbCoins` preserves query budgets with zero overhead. -/
theorem isQueryBounded_recordProbCoins {α : Type} {program : ProbComp α} {m : ℕ}
    (h : program.IsQueryBounded m) : (recordProbCoins program).IsQueryBounded m :=
  isQueryBounded_recordProbCoinsFrom [] h

private theorem isQueryBounded_recordCoinsFrom {α : Type}
    (tape : OracleComp.Transcript unifSpec)
    {program : ProbOracleComp OracleSpec.empty α} {m : ℕ}
    (h : program.IsQueryBounded m) : (recordCoinsFrom tape program).IsQueryBounded m := by
  induction program using OracleComp.induction generalizing tape m with
  | pure a => simp only [recordCoinsFrom_pure]; exact OracleComp.IsCostBounded.pure _ m
  | query_bind q cont ih =>
    obtain ⟨hm, hcont⟩ := OracleComp.IsCostBounded.liftBind_iff.mp h
    rw [PFunctor.FreeM.bind_eq_bind, recordCoinsFrom_bind]
    rcases q with k | q
    · have hq : recordCoinsFrom tape (OracleComp.query (Sum.inl k)) =
          (fun r => (r, tape ++ [⟨k, r⟩])) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
        recordCoinsFrom_sample_unifFin tape k
      rw [hq, bind_map_left]
      have hstep : (ProbOracleComp.sample (ProbComp.unifFin k) >>= fun r =>
            recordCoinsFrom (tape ++ [⟨k, r⟩]) (cont r)).IsQueryBounded ((m - 1) + 1) :=
        OracleComp.IsCostBounded.liftBind (Sum.inl k)
          (fun r => recordCoinsFrom (tape ++ [⟨k, r⟩]) (cont r)) (m - 1)
          (fun r => ih r (tape ++ [⟨k, r⟩]) (hcont r))
      simpa only [Nat.sub_add_cancel hm] using hstep
    · exact q.elim

/-- `recordCoins` preserves query budgets with zero overhead. -/
theorem isQueryBounded_recordCoins {α : Type} {program : ProbOracleComp OracleSpec.empty α}
    {m : ℕ} (h : program.IsQueryBounded m) : (recordCoins program).IsQueryBounded m :=
  isQueryBounded_recordCoinsFrom [] h

end CoinTape

/-! ### Write-once storage wrapper and monotonicity invariants -/

section WriteOnce

/-- Single party activation record appended to party `i`'s write-once tape: input, optional
output, all `ProbComp.unifFin` draws sampled during that activation (`coins`), and party `i`'s
post-activation `P.view` snapshot (`postView`). -/
structure PartyActivationRecord (In Out View : Type) : Type where
  /-- Input passed to party `i` for this activation. -/
  input : In
  /-- Output returned by party `i` for this activation, if any. -/
  output : Option Out
  /-- Oldest-first list of `ProbComp.unifFin` draws consumed during this activation. -/
  coins : OracleComp.Transcript unifSpec
  /-- Inner protocol's `view` of party `i` immediately after this activation. -/
  postView : View
  deriving DecidableEq, Repr

/-- Write-once, append-only state wrapper for `P.machine κ`. -/
structure WriteOnceState (S In Out View : Type) (n : ℕ) : Type where
  /-- Underlying inner protocol machine state. -/
  inner : S
  /-- Oldest-first list of `ProbComp.unifFin` draws consumed by `(P.machine κ).init`. -/
  initCoins : OracleComp.Transcript unifSpec
  /-- Per-party append-only oldest-first log of `PartyActivationRecord`s. -/
  tapes : Fin n → List (PartyActivationRecord In Out View)

/-- View exposed upon corrupting party `i` under `AdaptiveProtocol.withWriteOnce`: combines
the inner protocol's current `view` with party `i`'s complete write-once activation and coin
`tape` (`some` when `.nonErasing`, `none` when `.erasing`). -/
structure WriteOnceView (In Out View : Type) : Type where
  /-- Current inner-protocol view at corruption time. -/
  current : View
  /-- Complete append-only activation and coin tape (`some` iff `.nonErasing`). -/
  tape : Option (List (PartyActivationRecord In Out View))
  deriving DecidableEq, Repr

/-- Per-party prefix monotonicity relation on `WriteOnceState`: every party's tape in `s₁` is a
prefix of its tape in `s₂`. -/
@[expose] def WriteOnceState.TapePrefix {S : Type}
    (s₁ s₂ : WriteOnceState S In Out View n) : Prop :=
  ∀ j : Fin n, s₁.tapes j <+: s₂.tapes j

theorem WriteOnceState.TapePrefix.refl {S : Type} (s : WriteOnceState S In Out View n) :
    s.TapePrefix s :=
  fun j => List.prefix_refl (s.tapes j)

theorem WriteOnceState.TapePrefix.trans {S : Type}
    {s₁ s₂ s₃ : WriteOnceState S In Out View n}
    (h₁₂ : s₁.TapePrefix s₂) (h₂₃ : s₂.TapePrefix s₃) : s₁.TapePrefix s₃ :=
  fun j => (h₁₂ j).trans (h₂₃ j)

/-- Wrap an `AdaptiveProtocol` in explicit Canetti §7.1.1-inspired write-once per-party execution
and coin-exposure storage. Each `.inl (i, x)` party activation logs `{ input, output, coins,
postView }` to `tapes i` without modifying `tapes j` (`j ≠ i`); `.inr q` network/backdoor calls
leave all `tapes` unchanged; `onCorrupt` forwards to `P.onCorrupt` on `inner` while preserving all
`tapes`. -/
@[expose] def AdaptiveProtocol.withWriteOnce
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) :
    AdaptiveProtocol n In Out NetQ NetR (WriteOnceView In Out View) where
  machine κ := {
    State := WriteOnceState (P.machine κ).State In Out View n
    init := do
      let (s₀, coins) ← recordProbCoins (P.machine κ).init
      pure { inner := s₀, initCoins := coins, tapes := fun _ => [] }
    handle
      | .inl (i, x) => fun s => do
          let (res, coins) ← recordCoins (((P.machine κ).handle (.inl (i, x))).run s.inner)
          let rec_ : PartyActivationRecord In Out View :=
            { input := x, output := res.1, coins := coins, postView := P.view κ i res.2 }
          pure (res.1, { s with
            inner := res.2
            tapes := fun j => if j = i then s.tapes i ++ [rec_] else s.tapes j })
      | .inr q => fun s => do
          let res ← ((P.machine κ).handle (.inr q)).run s.inner
          pure (res.1, { s with inner := res.2 }) }
  view κ i s :=
    { current := P.view κ i s.inner
      tape := if mem = .nonErasing then some (s.tapes i) else none }
  onCorrupt κ i s := { s with inner := P.onCorrupt κ i s.inner }
  memory := mem

/-- Every reachable post-state of an `.inl (i, x)` activation of `P.withWriteOnce mem` extends
only party `i`'s tape by appending one `PartyActivationRecord`, preserves all other parties'
tapes, and satisfies `TapePrefix`. -/
theorem withWriteOnce_handle_inl_tapePrefix
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (i : Fin n) (x : In) (s : WriteOnceState (P.machine κ).State In Out View n)
    {out : Option Out} {s' : WriteOnceState (P.machine κ).State In Out View n}
    (hs : (out, s') ∈
      (closeEval ((((P.withWriteOnce mem).machine κ).handle (.inl (i, x))).run s)).support) :
    s.TapePrefix s' ∧ (∃ r, s'.tapes i = s.tapes i ++ [r]) ∧
      ∀ j, j ≠ i → s'.tapes j = s.tapes j := by
  dsimp only [AdaptiveProtocol.withWriteOnce, StateT.run] at hs
  erw [mem_support_closeEval_bind] at hs
  obtain ⟨⟨⟨out₀, s₀⟩, coins⟩, _, hs'⟩ := hs
  erw [mem_support_closeEval_pure] at hs'
  rcases hs' with ⟨rfl, rfl⟩
  refine ⟨fun j => ?_, ⟨{ input := x, output := out₀, coins := coins, postView := P.view κ i s₀ },
    by simp⟩, fun j hj => by simp [hj]⟩
  by_cases hj : j = i
  · subst hj; simp [List.prefix_append]
  · simp [hj]

/-- Every `.inr q` (backdoor / network) activation of `P.withWriteOnce mem` leaves all per-party
write-once tapes unchanged. -/
theorem withWriteOnce_handle_inr_tapes_eq
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (q : NetQ) (s : WriteOnceState (P.machine κ).State In Out View n)
    {r : NetR} {s' : WriteOnceState (P.machine κ).State In Out View n}
    (hs : (r, s') ∈
      (closeEval ((((P.withWriteOnce mem).machine κ).handle (.inr q)).run s)).support) :
    s'.tapes = s.tapes := by
  dsimp only [AdaptiveProtocol.withWriteOnce, StateT.run] at hs
  erw [mem_support_closeEval_bind] at hs
  obtain ⟨⟨_, _⟩, _, hs'⟩ := hs
  erw [mem_support_closeEval_pure] at hs'
  rcases hs' with ⟨rfl, rfl⟩
  rfl

/-- Corrupting party `i` via `(P.withWriteOnce mem).onCorrupt` leaves all per-party write-once
tapes unchanged. -/
@[simp] theorem withWriteOnce_onCorrupt_tapes_eq
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (i : Fin n) (s : WriteOnceState (P.machine κ).State In Out View n) :
    ((P.withWriteOnce mem).onCorrupt κ i s).tapes = s.tapes := rfl

private theorem foldl_applyInitialCorruptions_withWriteOnce
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (C₀ : Finset (Fin n)) (is : List (Fin n))
    (s : WriteOnceState (P.machine κ).State In Out View n) :
    is.foldl (fun acc i => if i ∈ C₀ then (P.withWriteOnce mem).onCorrupt κ i acc else acc) s =
      { s with
        inner := is.foldl (fun acc i => if i ∈ C₀ then P.onCorrupt κ i acc else acc) s.inner } := by
  induction is generalizing s with
  | nil => rfl
  | cons i rest ih =>
    dsimp only [List.foldl]
    by_cases hi : i ∈ C₀
    · simp only [hi, ↓reduceIte]
      exact ih { s with inner := P.onCorrupt κ i s.inner }
    · simp only [hi, ↓reduceIte]
      exact ih s

/-- Applying initial corruptions `C₀` to `P.withWriteOnce mem` modifies only `inner` and keeps
all per-party write-once tapes unchanged. -/
theorem withWriteOnce_applyInitialCorruptions_eq
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (C₀ : Finset (Fin n)) (s : WriteOnceState (P.machine κ).State In Out View n) :
    (P.withWriteOnce mem).applyInitialCorruptions κ C₀ s =
      { s with inner := P.applyInitialCorruptions κ C₀ s.inner } :=
  foldl_applyInitialCorruptions_withWriteOnce P mem κ C₀ (List.finRange n) s

/-- Across any execution of `adaptiveRouter mode (P.withWriteOnce mem) κ C₀`, both the per-party
write-once tapes (`TapePrefix`) and the corrupted party set (`⊆`) evolve monotonically: old
tape records and corruptions can never be erased or overwritten. -/
theorem mem_support_closeEval_adaptiveRouter_withWriteOnce_tapePrefix
    (mode : CorruptionMode) (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory)
    (κ : ℕ) (C₀ : Finset (Fin n)) {α : Type}
    (program : ProbOracleComp
      (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View)) α)
    (rs : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    {x : α × AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n}
    (hx : x ∈ (closeEval ((adaptiveRouter mode (P.withWriteOnce mem) κ C₀).runFrom
      program rs)).support) :
    rs.inner.TapePrefix x.2.inner ∧ rs.corrupted ⊆ x.2.corrupted := by
  refine Machine.mem_support_closeEval_runFrom_invariant
    (adaptiveRouter mode (P.withWriteOnce mem) κ C₀)
    (fun _ => True)
    (fun rs₁ rs₂ => rs₁.inner.TapePrefix rs₂.inner ∧ rs₁.corrupted ⊆ rs₂.corrupted)
    (fun rs₀ => ⟨WriteOnceState.TapePrefix.refl rs₀.inner, Finset.Subset.refl _⟩)
    (fun h₁₂ h₂₃ => ⟨h₁₂.1.trans h₂₃.1, h₁₂.2.trans h₂₃.2⟩)
    program (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _) rs hx
    fun q rs' {y} _ hy => ?_
  rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | nq)
  · dsimp only [adaptiveRouter, StateT.run] at hy
    by_cases hi : i ∈ rs'.corrupted
    · rw [ite_eq_left_iff.mpr (fun h => absurd hi h)] at hy
      erw [mem_support_closeEval_pure] at hy
      rcases hy with ⟨rfl, rfl⟩
      exact ⟨WriteOnceState.TapePrefix.refl _, Finset.Subset.refl _⟩
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hi)] at hy
      erw [mem_support_closeEval_bind] at hy
      obtain ⟨⟨_, s'⟩, hs', hy'⟩ := hy
      erw [mem_support_closeEval_pure] at hy'
      rcases hy' with ⟨rfl, rfl⟩
      exact ⟨(withWriteOnce_handle_inl_tapePrefix P mem κ i x rs'.inner hs').1,
        Finset.Subset.refl _⟩
  · dsimp only [adaptiveRouter, StateT.run] at hy
    erw [mem_support_closeEval_pure] at hy
    rcases hy with ⟨rfl, rfl⟩
    exact ⟨WriteOnceState.TapePrefix.refl _, Finset.Subset.refl _⟩
  · dsimp only [adaptiveRouter, StateT.run] at hy
    by_cases hi : i ∈ rs'.corrupted
    · rw [ite_eq_left_iff.mpr (fun h => absurd hi h)] at hy
      erw [mem_support_closeEval_bind] at hy
      obtain ⟨⟨_, s'⟩, hs', hy'⟩ := hy
      erw [mem_support_closeEval_pure] at hy'
      rcases hy' with ⟨rfl, rfl⟩
      exact ⟨(withWriteOnce_handle_inl_tapePrefix P mem κ i x rs'.inner hs').1,
        Finset.Subset.refl _⟩
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hi)] at hy
      erw [mem_support_closeEval_pure] at hy
      rcases hy with ⟨rfl, rfl⟩
      exact ⟨WriteOnceState.TapePrefix.refl _, Finset.Subset.refl _⟩
  · dsimp only [adaptiveRouter, StateT.run] at hy
    cases mode
    · by_cases hi : i ∈ rs'.corrupted
      · rw [ite_eq_left_iff.mpr (fun h => absurd hi h)] at hy
        erw [mem_support_closeEval_pure] at hy
        rcases hy with ⟨rfl, rfl⟩
        exact ⟨WriteOnceState.TapePrefix.refl _, Finset.Subset.refl _⟩
      · rw [ite_eq_right_iff.mpr (fun h => absurd h hi)] at hy
        erw [mem_support_closeEval_pure] at hy
        rcases hy with ⟨rfl, rfl⟩
        exact ⟨WriteOnceState.TapePrefix.refl _, Finset.Subset.refl _⟩
    · erw [mem_support_closeEval_pure] at hy
      rcases hy with ⟨rfl, rfl⟩
      by_cases hi : i ∈ rs'.corrupted
      · simp only [hi, ↓reduceIte]
        exact ⟨WriteOnceState.TapePrefix.refl _, Finset.Subset.refl _⟩
      · simp only [hi, ↓reduceIte]
        exact ⟨WriteOnceState.TapePrefix.refl _, Finset.subset_insert _ _⟩
  · dsimp only [adaptiveRouter, StateT.run] at hy
    erw [mem_support_closeEval_bind] at hy
    obtain ⟨⟨_, s'⟩, hs', hy'⟩ := hy
    erw [mem_support_closeEval_pure] at hy'
    rcases hy' with ⟨rfl, rfl⟩
    refine ⟨fun j => ?_, Finset.Subset.refl _⟩
    dsimp only [AdaptiveProtocol.recordSnapshot]
    rw [withWriteOnce_handle_inr_tapes_eq P mem κ nq rs'.inner hs']

/-- Wrapping an `AdaptiveProtocol` in `withWriteOnce` preserves its per-activation call budget
with zero overhead. -/
theorem AdaptiveProtocol.PolyBounded.withWriteOnce
    {P : AdaptiveProtocol n In Out NetQ NetR View} {p : Polynomial ℕ} (mem : PartyMemory)
    (hP : P.PolyBounded p) : (P.withWriteOnce mem).PolyBounded p := fun κ => by
  refine ⟨?_, fun q s => ?_⟩
  · dsimp only [AdaptiveProtocol.withWriteOnce]
    exact OracleComp.IsCostBounded.bind (isQueryBounded_recordProbCoins (hP κ).1)
      fun _ => OracleComp.IsCostBounded.pure _ 0
  · rcases q with ⟨i, x⟩ | nq
    · dsimp only [AdaptiveProtocol.withWriteOnce, StateT.run]
      exact OracleComp.IsCostBounded.bind
        (isQueryBounded_recordCoins ((hP κ).2 (.inl (i, x)) s.inner))
        fun _ => OracleComp.IsCostBounded.pure _ 0
    · dsimp only [AdaptiveProtocol.withWriteOnce, StateT.run]
      exact OracleComp.IsCostBounded.bind ((hP κ).2 (.inr nq) s.inner)
        fun _ => OracleComp.IsCostBounded.pure _ 0

end WriteOnce

/-! ### Projection equivalence and emulation implication -/

section Projection

/-- Adapt an adversary talking to `View₂` to talk to `View₁` by transforming network replies
with `f : AdaptiveNetR Out NetR View₁ → AdaptiveNetR Out NetR View₂`. -/
@[expose] def mapNetRAdversary
    (f : AdaptiveNetR Out NetR View₁ → AdaptiveNetR Out NetR View₂)
    (A : AdaptiveAdversary n In Out NetQ NetR View₂ AdvQ AdvR) :
    AdaptiveAdversary n In Out NetQ NetR View₁ AdvQ AdvR where
  initial := A.initial
  machine κ := {
    State := (A.machine κ).State
    init := (A.machine κ).init
    handle q s :=
      OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query (spec := probOracleSpec
            (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View₁))) (.inl k))
          fun nq => f <$> ProbOracleComp.query
            (spec := netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View₁)) nq)
        (((A.machine κ).handle q).run s) }

/-- Transforming network replies in an adversary preserves its call budget identically. -/
theorem AdaptiveAdversary.PolyBounded.mapNetR
    (f : AdaptiveNetR Out NetR View₁ → AdaptiveNetR Out NetR View₂)
    {A : AdaptiveAdversary n In Out NetQ NetR View₂ AdvQ AdvR} {pA : Polynomial ℕ}
    (hA : A.PolyBounded pA) : (mapNetRAdversary f A).PolyBounded pA := fun κ => by
  refine ⟨(hA κ).1, fun q s => ?_⟩
  refine OracleComp.IsCostBounded.interpret (fun x => ?_) ((hA κ).2 q s)
  rcases x with k | nq
  · exact OracleComp.IsCostBounded.query _
  · exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- Project a `CorruptionReport (WriteOnceView In Out View)` down to a `CorruptionReport View`
matching target memory mode `mem` by discarding the write-once tape and either keeping projected
snapshot views (`mem = .nonErasing`) or dropping history (`mem = .erasing`). -/
@[expose] def projectWriteOnceReport (mem : PartyMemory)
    (r : CorruptionReport (WriteOnceView In Out View)) : CorruptionReport View :=
  { current := r.current.current
    history := if mem = .nonErasing then r.history.map (List.map (·.current)) else none }

/-- Project `AdaptiveNetR` answers from `WriteOnceView In Out View` down to `View` under target
memory mode `mem`. -/
@[expose] def projectWriteOnceNetR (mem : PartyMemory) :
    AdaptiveNetR Out NetR (WriteOnceView In Out View) → AdaptiveNetR Out NetR View
  | .party out => .party out
  | .corrupt rep => .corrupt (rep.map (projectWriteOnceReport mem))
  | .net r => .net r

/-- Drop `.tape` and router `.history` from a `CorruptionReport (WriteOnceView In Out View)` to
recover the `.erasing` report of `P.withWriteOnce .erasing`. -/
@[expose] def dropWriteOnceTapeReport
    (r : CorruptionReport (WriteOnceView In Out View)) :
    CorruptionReport (WriteOnceView In Out View) :=
  { current := { current := r.current.current, tape := none }
    history := none }

/-- Drop `.tape` and `.history` from `AdaptiveNetR` answers under `WriteOnceView`. -/
@[expose] def dropWriteOnceTapeNetR :
    AdaptiveNetR Out NetR (WriteOnceView In Out View) →
      AdaptiveNetR Out NetR (WriteOnceView In Out View)
  | .party out => .party out
  | .corrupt rep => .corrupt (rep.map dropWriteOnceTapeReport)
  | .net r => .net r

private def WriteOnceRouterRel (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ)
    (rs₁ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (rs₂ : AdaptiveRouterState (P.machine κ).State View n) : Prop :=
  rs₁.inner.inner = rs₂.inner ∧
  rs₁.corrupted = rs₂.corrupted ∧
  (∀ j, (rs₁.trace j).map (·.current) = rs₂.trace j)

private theorem writeOnce_handle_inl_intertwine {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (i : Fin n) (x : In)
    (rs₁ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (rs₂ : AdaptiveRouterState (P.machine κ).State View n)
    (hR : WriteOnceRouterRel P κ rs₁ rs₂)
    (k₁ : Option Out × AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n →
      ProbOracleComp OracleSpec.empty α)
    (k₂ : Option Out × AdaptiveRouterState (P.machine κ).State View n →
      ProbOracleComp OracleSpec.empty α)
    (hcont : ∀ out rs₁' rs₂', WriteOnceRouterRel P κ rs₁' rs₂' → k₁ (out, rs₁') = k₂ (out, rs₂')) :
    ((((P.withWriteOnce mem).machine κ).handle (.inl (i, x)) rs₁.inner >>= fun p =>
        k₁ (p.1, (P.withWriteOnce mem).recordSnapshot κ p.2 rs₁.corrupted rs₁.trace)) =
      (((P.machine κ).handle (.inl (i, x)) rs₂.inner >>= fun p =>
        k₂ (p.1, P.recordSnapshot κ p.2 rs₂.corrupted rs₂.trace)))) := by
  dsimp only [AdaptiveProtocol.withWriteOnce, StateT.run]
  rw [hR.1, bind_assoc]
  have hrec : (P.machine κ).handle (.inl (i, x)) rs₂.inner =
      Prod.fst <$> recordCoins ((P.machine κ).handle (.inl (i, x)) rs₂.inner) :=
    (fst_map_recordCoins _).symm
  conv_rhs => rw [hrec, bind_map_left]
  refine bind_congr fun ⟨⟨out, s'⟩, coins⟩ => ?_
  refine hcont out _ _ ⟨rfl, hR.2.1, fun j => ?_⟩
  simp only [AdaptiveProtocol.recordSnapshot, List.map_append, List.map_cons, List.map_nil]
  rw [hR.2.2 j]

private theorem writeOnce_handle_inr_intertwine {α : Type}
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (nq : NetQ)
    (rs₁ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (rs₂ : AdaptiveRouterState (P.machine κ).State View n)
    (hR : WriteOnceRouterRel P κ rs₁ rs₂)
    (k₁ : AdaptiveNetR Out NetR (WriteOnceView In Out View) × AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n →
      ProbOracleComp OracleSpec.empty α)
    (k₂ : AdaptiveNetR Out NetR View × AdaptiveRouterState (P.machine κ).State View n →
      ProbOracleComp OracleSpec.empty α)
    (hcont : ∀ r rs₁' rs₂', WriteOnceRouterRel P κ rs₁' rs₂' →
      k₁ (.net r, rs₁') = k₂ (.net r, rs₂')) :
    (((((P.withWriteOnce mem).machine κ).handle (.inr nq)).run rs₁.inner >>= fun p =>
        pure (AdaptiveNetR.net p.1,
          (P.withWriteOnce mem).recordSnapshot κ p.2 rs₁.corrupted rs₁.trace)) >>= k₁) =
      ((((P.machine κ).handle (.inr nq)).run rs₂.inner >>= fun p =>
        pure (AdaptiveNetR.net p.1, P.recordSnapshot κ p.2 rs₂.corrupted rs₂.trace)) >>= k₂) := by
  dsimp only [AdaptiveProtocol.withWriteOnce, StateT.run]
  rw [hR.1]
  simp only [bind_assoc, pure_bind]
  refine bind_congr fun ⟨r, s'⟩ => ?_
  refine hcont r _ _ ⟨rfl, hR.2.1, fun j => ?_⟩
  simp only [AdaptiveProtocol.recordSnapshot, List.map_append, List.map_cons, List.map_nil]
  rw [hR.2.2 j]

private theorem runFrom_adaptiveRouter_projectWriteOnce {α β : Type} (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory)
    (hmem : P.memory = .nonErasing → mem = .nonErasing) (κ : ℕ)
    (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) α)
    (rs₁ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (rs₂ : AdaptiveRouterState (P.machine κ).State View n)
    (hR : WriteOnceRouterRel P κ rs₁ rs₂)
    (f : α × AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n →
      ProbOracleComp OracleSpec.empty β)
    (g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs₁' rs₂', WriteOnceRouterRel P κ rs₁' rs₂' → f (a, rs₁') = g (a, rs₂')) :
    ((adaptiveRouter mode (P.withWriteOnce mem) κ C₀).runFrom
        (liftAdaptiveNet (OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query (spec := probOracleSpec
              (netSpec (AdaptiveNetQ n In NetQ)
                (AdaptiveNetR Out NetR (WriteOnceView In Out View)))) (.inl k))
            fun nq => projectWriteOnceNetR P.memory <$>
              ProbOracleComp.query (spec := netSpec (AdaptiveNetQ n In NetQ)
                (AdaptiveNetR Out NetR (WriteOnceView In Out View))) nq)
          netProg)) rs₁ >>= f) =
      ((adaptiveRouter mode P κ C₀).runFrom (liftAdaptiveNet netProg) rs₂ >>= g) := by
  dsimp only [liftAdaptiveNet, Machine.liftRightProgram]
  rw [OracleComp.interpret_interpret, OracleComp.interpret_sumHandler]
  let q₁ : (q : AdaptiveNetQ n In NetQ) →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))
        (AdaptiveNetR Out NetR View) := fun q =>
    projectWriteOnceNetR P.memory <$> ProbOracleComp.query (Sum.inr q)
  let q₂ : (q : AdaptiveNetQ n In NetQ) →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View)
        (AdaptiveNetR Out NetR View) := fun q =>
    ProbOracleComp.query (Sum.inr q)
  have hleft :
      (fun k : ℕ => OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query (spec := probOracleSpec
            (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))) (Sum.inl k))
          fun q => ProbOracleComp.query
            (spec := adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))
            (Sum.inr q))
        (OracleComp.query (spec := probOracleSpec
          (netSpec (AdaptiveNetQ n In NetQ)
            (AdaptiveNetR Out NetR (WriteOnceView In Out View)))) (Sum.inl k))) =
      fun k => OracleComp.query (Sum.inl k) :=
    funext fun k => (OracleComp.interpret_query _ (Sum.inl k)).trans rfl
  have hcomp :
      (fun q : AdaptiveNetQ n In NetQ => OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query (spec := probOracleSpec
            (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))) (Sum.inl k))
          fun q => ProbOracleComp.query
            (spec := adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))
            (Sum.inr q))
        (projectWriteOnceNetR P.memory <$> ProbOracleComp.query q)) = q₁ :=
    funext fun q =>
      (OracleComp.interpret_map _ _ _).trans (congrArg _ (OracleComp.interpret_query _ _))
  erw [hleft, hcomp]
  refine Machine.runFrom_interpret_intertwine
    (adaptiveRouter mode (P.withWriteOnce mem) κ C₀) (adaptiveRouter mode P κ C₀)
    q₁ q₂ (fun _ => True) (WriteOnceRouterRel P κ) netProg
    (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _) rs₁ rs₂ hR f g hfg
    fun q rs₁' rs₂' k₁ k₂ _ hR' hcont => ?_
  dsimp only [q₁, q₂]
  erw [Machine.runFrom_map, Machine.runFrom_query, Machine.runFrom_query, bind_map_left]
  dsimp only [adaptiveRouter, StateT.run]
  cases q with
  | party i x =>
    by_cases hi : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      conv_lhs => erw [bind_assoc]
      conv_rhs => erw [bind_assoc]
      exact writeOnce_handle_inl_intertwine P mem κ i x rs₁' rs₂' hR'
        (fun p => pure (AdaptiveNetR.party p.1, p.2) >>=
          fun a => k₁ (Prod.map (projectWriteOnceNetR P.memory) id a))
        (fun p => pure (AdaptiveNetR.party p.1, p.2) >>= k₂)
        fun out rs₁'' rs₂'' hR'' => by
          erw [pure_bind, pure_bind]
          exact hcont (AdaptiveNetR.party out) rs₁'' rs₂'' hR''
    · have hi₂ : i ∉ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte, pure_bind]
      exact hcont (AdaptiveNetR.party none) rs₁' rs₂' hR'
  | corrupt i =>
    cases mode
    · by_cases hi : i ∈ rs₁'.corrupted
      · have hi₂ : i ∈ rs₂'.corrupted := hR'.2.1 ▸ hi
        simp only [hi, hi₂, ↓reduceIte, pure_bind]
        have hrep : projectWriteOnceNetR P.memory
            (AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce mem).corruptionReport κ i rs₁'))) =
            AdaptiveNetR.corrupt (NetR := NetR) (some (P.corruptionReport κ i rs₂')) := by
          simp only [projectWriteOnceNetR, projectWriteOnceReport, Option.map_some,
            AdaptiveProtocol.corruptionReport, AdaptiveProtocol.withWriteOnce]
          congr 3
          · exact congrArg (P.view κ i) hR'.1
          · cases hP : P.memory
            · simp
            · simp [hmem hP, hR'.2.2 i]
        dsimp only [Prod.map, id_eq]
        erw [hrep, pure_bind]
        exact hcont _ rs₁' rs₂' hR'
      · have hi₂ : i ∉ rs₂'.corrupted := hR'.2.1 ▸ hi
        simp only [hi, hi₂, ↓reduceIte, pure_bind]
        exact hcont _ rs₁' rs₂' hR'
    · simp only [pure_bind]
      by_cases hi : i ∈ rs₁'.corrupted
      · have hi₂ : i ∈ rs₂'.corrupted := hR'.2.1 ▸ hi
        simp only [hi, hi₂, ↓reduceIte]
        have hrep : projectWriteOnceNetR P.memory
            (AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce mem).corruptionReport κ i rs₁'))) =
            AdaptiveNetR.corrupt (NetR := NetR) (some (P.corruptionReport κ i rs₂')) := by
          simp only [projectWriteOnceNetR, projectWriteOnceReport, Option.map_some,
            AdaptiveProtocol.corruptionReport, AdaptiveProtocol.withWriteOnce]
          congr 3
          · exact congrArg (P.view κ i) hR'.1
          · cases hP : P.memory
            · simp
            · simp [hmem hP, hR'.2.2 i]
        dsimp only [Prod.map, id_eq]
        erw [hrep, pure_bind]
        exact hcont _ rs₁' rs₂' hR'
      · have hi₂ : i ∉ rs₂'.corrupted := hR'.2.1 ▸ hi
        simp only [hi, hi₂, ↓reduceIte]
        have hR'' : WriteOnceRouterRel P κ
            { inner := (P.withWriteOnce mem).onCorrupt κ i rs₁'.inner
              corrupted := insert i rs₁'.corrupted
              trace := rs₁'.trace }
            { inner := P.onCorrupt κ i rs₂'.inner
              corrupted := insert i rs₂'.corrupted
              trace := rs₂'.trace } :=
          ⟨congrArg (P.onCorrupt κ i) hR'.1, congrArg (insert i) hR'.2.1, hR'.2.2⟩
        have hrep : projectWriteOnceNetR P.memory
            (AdaptiveNetR.corrupt (NetR := NetR) (some ((P.withWriteOnce mem).corruptionReport κ i
              { inner := (P.withWriteOnce mem).onCorrupt κ i rs₁'.inner
                corrupted := insert i rs₁'.corrupted
                trace := rs₁'.trace }))) =
            AdaptiveNetR.corrupt (NetR := NetR) (some (P.corruptionReport κ i
              { inner := P.onCorrupt κ i rs₂'.inner
                corrupted := insert i rs₂'.corrupted
                trace := rs₂'.trace })) := by
          simp only [projectWriteOnceNetR, projectWriteOnceReport, Option.map_some,
            AdaptiveProtocol.corruptionReport, AdaptiveProtocol.withWriteOnce]
          congr 3
          · exact congrArg (P.view κ i) hR''.1
          · cases hP : P.memory
            · simp
            · simp [hmem hP, hR''.2.2 i]
        dsimp only [Prod.map, id_eq]
        erw [hrep, pure_bind]
        exact hcont _ _ _ hR''
  | net nq =>
    exact writeOnce_handle_inr_intertwine P mem κ nq rs₁' rs₂' hR'
      (fun p => k₁ (projectWriteOnceNetR P.memory p.1, p.2))
      (fun p => k₂ (p.1, p.2))
      fun r rs₁'' rs₂'' hR'' => hcont (.net r) rs₁'' rs₂'' hR''

/-- Honest-phase / uncorrupted execution transparency: for any program over `adaptiveProtocolSpec`
containing no `.corrupt` queries (in particular, all honest-party `.inl` and `.net` queries),
running against `adaptiveRouter mode (P.withWriteOnce mem) κ C₀` from related states produces the
identical `ProbOracleComp` result and related state as running directly against
`adaptiveRouter mode P κ C₀`. -/
theorem runFrom_adaptiveRouter_withWriteOnce_noCorrupt {α β : Type} (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory) (κ : ℕ)
    (C₀ : Finset (Fin n))
    (program : ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View) α)
    (hno : OracleComp.QueriesSatisfy
      (Sum.elim (fun _ => True) fun q => match q with
        | .inl _ => True
        | .inr (.corrupt _) => False
        | .inr _ => True) program)
    (rs₁ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (rs₂ : AdaptiveRouterState (P.machine κ).State View n)
    (hR : rs₁.inner.inner = rs₂.inner ∧ rs₁.corrupted = rs₂.corrupted ∧
      ∀ j, (rs₁.trace j).map (·.current) = rs₂.trace j)
    (f : α × AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n →
      ProbOracleComp OracleSpec.empty β)
    (g : α × AdaptiveRouterState (P.machine κ).State View n → ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs₁' rs₂',
      (rs₁'.inner.inner = rs₂'.inner ∧ rs₁'.corrupted = rs₂'.corrupted ∧
        ∀ j, (rs₁'.trace j).map (·.current) = rs₂'.trace j) →
      f (a, rs₁') = g (a, rs₂')) :
    ((adaptiveRouter mode (P.withWriteOnce mem) κ C₀).runFrom
        (OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query (spec := probOracleSpec
              (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))) (Sum.inl k))
            fun q => match q with
              | .inl p => ProbOracleComp.query (Sum.inl p)
              | .inr (.party i x) =>
                  projectWriteOnceNetR P.memory <$>
                    ProbOracleComp.query (Sum.inr (.party i x))
              | .inr (.corrupt _) => ProbOracleComp.sample (ProbComp.unifFin 0) >>=
                  fun _ => pure (.corrupt none)
              | .inr (.net nq) =>
                  projectWriteOnceNetR P.memory <$> ProbOracleComp.query (Sum.inr (.net nq)))
          program) rs₁ >>= f) =
      ((adaptiveRouter mode P κ C₀).runFrom program rs₂ >>= g) := by
  let Inv : AdaptivePartyQ n In ⊕ AdaptiveNetQ n In NetQ → Prop := fun q => match q with
    | .inl _ => True
    | .inr (.corrupt _) => False
    | .inr _ => True
  let q₁ : (q : AdaptivePartyQ n In ⊕ AdaptiveNetQ n In NetQ) →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))
        (adaptiveProtocolSpec n In Out NetQ NetR View q) := fun q => match q with
    | .inl p => ProbOracleComp.query (Sum.inl p)
    | .inr (.party i x) =>
        projectWriteOnceNetR P.memory <$> ProbOracleComp.query (Sum.inr (.party i x))
    | .inr (.corrupt _) => ProbOracleComp.sample (ProbComp.unifFin 0) >>=
        fun _ => pure (.corrupt none)
    | .inr (.net nq) =>
        projectWriteOnceNetR P.memory <$> ProbOracleComp.query (Sum.inr (.net nq))
  let q₂ : (q : AdaptivePartyQ n In ⊕ AdaptiveNetQ n In NetQ) →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR View)
        (adaptiveProtocolSpec n In Out NetQ NetR View q) :=
    fun q => ProbOracleComp.query q
  have hself :
      OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (.inl k)) q₂) program = program := by
    have hs : sumHandler (fun k => OracleComp.query (spec := probOracleSpec
        (adaptiveProtocolSpec n In Out NetQ NetR View)) (.inl k)) q₂ = OracleComp.query :=
      funext fun q => by cases q <;> rfl
    rw [hs, OracleComp.interpret_query_eq_self]
  conv_rhs => rw [← hself]
  refine Machine.runFrom_interpret_intertwine
    (adaptiveRouter mode (P.withWriteOnce mem) κ C₀) (adaptiveRouter mode P κ C₀)
    q₁ q₂ Inv (WriteOnceRouterRel P κ) program hno rs₁ rs₂ hR f g hfg
    fun q rs₁' rs₂' k₁ k₂ hq hR' hcont => ?_
  rcases q with (⟨i, x⟩ | _) | (⟨i, x⟩ | i | nq)
  · erw [Machine.runFrom_query, Machine.runFrom_query]
    dsimp only [adaptiveRouter, StateT.run]
    by_cases hi : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      erw [pure_bind, pure_bind]
      exact hcont none rs₁' rs₂' hR'
    · have hi₂ : i ∉ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      conv_lhs => erw [bind_assoc]
      conv_rhs => erw [bind_assoc]
      exact writeOnce_handle_inl_intertwine P mem κ i x rs₁' rs₂' hR'
        (fun p => pure (p.1, p.2) >>= k₁) (fun p => pure (p.1, p.2) >>= k₂)
        fun out rs₁'' rs₂'' hR'' => by
          erw [pure_bind, pure_bind]
          exact hcont out rs₁'' rs₂'' hR''
  · erw [Machine.runFrom_query, Machine.runFrom_query]
    dsimp only [adaptiveRouter, StateT.run]
    rw [hR'.2.1]
    exact hcont rs₂'.corrupted rs₁' rs₂' hR'
  · dsimp only [q₁, q₂]
    erw [Machine.runFrom_map, Machine.runFrom_query, Machine.runFrom_query, bind_map_left]
    dsimp only [adaptiveRouter, StateT.run]
    by_cases hi : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      conv_lhs => erw [bind_assoc]
      conv_rhs => erw [bind_assoc]
      exact writeOnce_handle_inl_intertwine P mem κ i x rs₁' rs₂' hR'
        (fun p => pure (AdaptiveNetR.party p.1, p.2) >>=
          fun a => k₁ (Prod.map (projectWriteOnceNetR P.memory) id a))
        (fun p => pure (AdaptiveNetR.party p.1, p.2) >>= k₂)
        fun out rs₁'' rs₂'' hR'' => by
          erw [pure_bind, pure_bind]
          exact hcont (AdaptiveNetR.party out) rs₁'' rs₂'' hR''
    · have hi₂ : i ∉ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte, pure_bind]
      exact hcont (AdaptiveNetR.party none) rs₁' rs₂' hR'
  · exact False.elim hq
  · dsimp only [q₁, q₂]
    erw [Machine.runFrom_map, Machine.runFrom_query, Machine.runFrom_query, bind_map_left]
    dsimp only [adaptiveRouter, StateT.run]
    exact writeOnce_handle_inr_intertwine P mem κ nq rs₁' rs₂' hR'
      (fun p => k₁ (projectWriteOnceNetR P.memory p.1, p.2))
      (fun p => k₂ (p.1, p.2))
      fun r rs₁'' rs₂'' hR'' => hcont (AdaptiveNetR.net r) rs₁'' rs₂'' hR''

private theorem runFrom_adaptiveRouter_dropWriteOnce {α β : Type} (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (κ : ℕ) (C₀ : Finset (Fin n))
    (netProg : ProbOracleComp
      (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR (WriteOnceView In Out View))) α)
    (rs₁ rs₂ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (hinner : rs₁.inner = rs₂.inner) (hcor : rs₁.corrupted = rs₂.corrupted)
    (f g : α × AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n →
      ProbOracleComp OracleSpec.empty β)
    (hfg : ∀ a rs₁' rs₂', rs₁'.inner = rs₂'.inner → rs₁'.corrupted = rs₂'.corrupted →
      f (a, rs₁') = g (a, rs₂')) :
    ((adaptiveRouter mode (P.withWriteOnce .nonErasing) κ C₀).runFrom
        (liftAdaptiveNet (OracleComp.interpret
          (sumHandler
            (fun k => OracleComp.query (spec := probOracleSpec
              (netSpec (AdaptiveNetQ n In NetQ)
                (AdaptiveNetR Out NetR (WriteOnceView In Out View)))) (.inl k))
            fun nq => dropWriteOnceTapeNetR <$>
              ProbOracleComp.query (spec := netSpec (AdaptiveNetQ n In NetQ)
                (AdaptiveNetR Out NetR (WriteOnceView In Out View))) nq)
          netProg)) rs₁ >>= f) =
      ((adaptiveRouter mode (P.withWriteOnce .erasing) κ C₀).runFrom
        (liftAdaptiveNet netProg) rs₂ >>= g) := by
  dsimp only [liftAdaptiveNet, Machine.liftRightProgram]
  rw [OracleComp.interpret_interpret, OracleComp.interpret_sumHandler]
  let q₁ : (q : AdaptiveNetQ n In NetQ) →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))
        (AdaptiveNetR Out NetR (WriteOnceView In Out View)) := fun q =>
    dropWriteOnceTapeNetR <$> ProbOracleComp.query (Sum.inr q)
  let q₂ : (q : AdaptiveNetQ n In NetQ) →
      ProbOracleComp (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))
        (AdaptiveNetR Out NetR (WriteOnceView In Out View)) := fun q =>
    ProbOracleComp.query (Sum.inr q)
  have hleft :
      (fun k : ℕ => OracleComp.interpret
        (sumHandler
          (fun k => OracleComp.query (spec := probOracleSpec
            (adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))) (Sum.inl k))
          fun q => ProbOracleComp.query
            (spec := adaptiveProtocolSpec n In Out NetQ NetR (WriteOnceView In Out View))
            (Sum.inr q))
        (OracleComp.query (spec := probOracleSpec
          (netSpec (AdaptiveNetQ n In NetQ)
            (AdaptiveNetR Out NetR (WriteOnceView In Out View)))) (Sum.inl k))) =
      fun k => OracleComp.query (Sum.inl k) :=
    funext fun k => (OracleComp.interpret_query _ (Sum.inl k)).trans rfl
  have hcomp :
      (fun q : AdaptiveNetQ n In NetQ => OracleComp.interpret
        (sumHandler (fun k => OracleComp.query (.inl k)) fun q => ProbOracleComp.query (.inr q))
        (dropWriteOnceTapeNetR <$> ProbOracleComp.query q)) = q₁ :=
    funext fun q =>
      (OracleComp.interpret_map _ _ _).trans (congrArg _ (OracleComp.interpret_query _ _))
  erw [hleft, hcomp]
  refine Machine.runFrom_interpret_intertwine
    (adaptiveRouter mode (P.withWriteOnce .nonErasing) κ C₀)
    (adaptiveRouter mode (P.withWriteOnce .erasing) κ C₀)
    q₁ q₂ (fun _ => True)
    (fun s₁ s₂ => s₁.inner = s₂.inner ∧ s₁.corrupted = s₂.corrupted)
    netProg (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    rs₁ rs₂ ⟨hinner, hcor⟩ f g (fun a s₁ s₂ hR => hfg a s₁ s₂ hR.1 hR.2)
    fun q rs₁' rs₂' k₁ k₂ _ ⟨hi_eq, hc_eq⟩ hcont => ?_
  dsimp only [q₁, q₂]
  erw [Machine.runFrom_map, Machine.runFrom_query, Machine.runFrom_query, bind_map_left]
  dsimp only [adaptiveRouter, StateT.run]
  cases q with
  | party i x =>
    by_cases hi : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hc_eq ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      rw [hi_eq]
      conv_lhs => erw [bind_assoc]
      conv_rhs => erw [bind_assoc]
      refine bind_congr fun ⟨out, s'⟩ => ?_
      erw [pure_bind, pure_bind]
      exact hcont (.party out) _ _ ⟨rfl, hc_eq⟩
    · have hi₂ : i ∉ rs₂'.corrupted := hc_eq ▸ hi
      simp only [hi, hi₂, ↓reduceIte, pure_bind]
      exact hcont (.party none) rs₁' rs₂' ⟨hi_eq, hc_eq⟩
  | corrupt i =>
    cases mode
    · by_cases hi : i ∈ rs₁'.corrupted
      · have hi₂ : i ∈ rs₂'.corrupted := hc_eq ▸ hi
        simp only [hi, hi₂, ↓reduceIte, pure_bind]
        have hrep : dropWriteOnceTapeNetR
            (AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce .nonErasing).corruptionReport κ i rs₁'))) =
            AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce .erasing).corruptionReport κ i rs₂')) := by
          simp [dropWriteOnceTapeNetR, dropWriteOnceTapeReport, AdaptiveProtocol.corruptionReport,
            AdaptiveProtocol.withWriteOnce, hi_eq]
        dsimp only [Prod.map, id_eq]
        erw [hrep, pure_bind]
        exact hcont _ rs₁' rs₂' ⟨hi_eq, hc_eq⟩
      · have hi₂ : i ∉ rs₂'.corrupted := hc_eq ▸ hi
        simp only [hi, hi₂, ↓reduceIte, pure_bind]
        exact hcont _ rs₁' rs₂' ⟨hi_eq, hc_eq⟩
    · simp only [pure_bind]
      by_cases hi : i ∈ rs₁'.corrupted
      · have hi₂ : i ∈ rs₂'.corrupted := hc_eq ▸ hi
        simp only [hi, hi₂, ↓reduceIte]
        have hrep : dropWriteOnceTapeNetR
            (AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce .nonErasing).corruptionReport κ i rs₁'))) =
            AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce .erasing).corruptionReport κ i rs₂')) := by
          simp [dropWriteOnceTapeNetR, dropWriteOnceTapeReport, AdaptiveProtocol.corruptionReport,
            AdaptiveProtocol.withWriteOnce, hi_eq]
        dsimp only [Prod.map, id_eq]
        erw [hrep, pure_bind]
        exact hcont _ rs₁' rs₂' ⟨hi_eq, hc_eq⟩
      · have hi₂ : i ∉ rs₂'.corrupted := hc_eq ▸ hi
        simp only [hi, hi₂, ↓reduceIte]
        have hi_eq' : (P.withWriteOnce .nonErasing).onCorrupt κ i rs₁'.inner =
            (P.withWriteOnce .erasing).onCorrupt κ i rs₂'.inner :=
          by simp [AdaptiveProtocol.withWriteOnce, hi_eq]
        have hrep : dropWriteOnceTapeNetR
            (AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce .nonErasing).corruptionReport κ i
                { inner := (P.withWriteOnce .nonErasing).onCorrupt κ i rs₁'.inner
                  corrupted := insert i rs₁'.corrupted
                  trace := rs₁'.trace }))) =
            AdaptiveNetR.corrupt (NetR := NetR)
              (some ((P.withWriteOnce .erasing).corruptionReport κ i
                { inner := (P.withWriteOnce .erasing).onCorrupt κ i rs₂'.inner
                  corrupted := insert i rs₂'.corrupted
                  trace := rs₂'.trace })) := by
          simp [dropWriteOnceTapeNetR, dropWriteOnceTapeReport, AdaptiveProtocol.corruptionReport,
            AdaptiveProtocol.withWriteOnce, hi_eq]
        dsimp only [Prod.map, id_eq]
        erw [hrep, pure_bind]
        exact hcont _ _ _ ⟨hi_eq', congrArg (insert i) hc_eq⟩
  | net nq =>
    dsimp only
    rw [hi_eq]
    conv_lhs => erw [bind_assoc]
    conv_rhs => erw [bind_assoc]
    refine bind_congr fun ⟨r, s'⟩ => ?_
    erw [pure_bind, pure_bind]
    exact hcont (.net r) _ _ ⟨rfl, hc_eq⟩

private theorem runFrom_adaptiveExecMachine_withWriteOnce_project {α : Type}
    (mode : CorruptionMode) (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory)
    (hmem : P.memory = .nonErasing → mem = .nonErasing)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State)
    (rs₁ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (rs₂ : AdaptiveRouterState (P.machine κ).State View n)
    (hR : WriteOnceRouterRel P κ rs₁ rs₂) :
    Prod.fst <$> (adaptiveExecMachine mode (P.withWriteOnce mem)
        (mapNetRAdversary (projectWriteOnceNetR P.memory) A) κ).runFrom program (sA, rs₁) =
      Prod.fst <$> (adaptiveExecMachine mode P A κ).runFrom program (sA, rs₂) := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  refine Machine.runFrom_intertwine
    (adaptiveExecMachine mode (P.withWriteOnce mem)
      (mapNetRAdversary (projectWriteOnceNetR P.memory) A) κ)
    (adaptiveExecMachine mode P A κ) (fun _ => True)
    (fun x₁ x₂ => x₁.1 = x₂.1 ∧ WriteOnceRouterRel P κ x₁.2 x₂.2)
    program (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    (sA, rs₁) (sA, rs₂) ⟨rfl, hR⟩ (fun x => pure x.1) (fun x => pure x.1)
    (fun _ _ _ _ => rfl) fun q ⟨sA₁, rs₁'⟩ ⟨sA₂, rs₂'⟩ k₁ k₂ _ ⟨hsA, hR'⟩ hcont => ?_
  dsimp only [adaptiveExecMachine, Machine.comp, liftAdaptiveAdversary, Machine.liftRight]
    at sA₁ rs₁' sA₂ rs₂' hsA
  subst hsA
  rcases q with (⟨i, x⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party, adaptiveExecMachine_handle_inl_party]
    by_cases hi : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      erw [pure_bind, pure_bind]
      exact hcont none _ _ ⟨rfl, hR'⟩
    · have hi₂ : i ∉ rs₂'.corrupted := hR'.2.1 ▸ hi
      simp only [hi, hi₂, ↓reduceIte]
      conv_lhs => erw [bind_assoc]
      conv_rhs => erw [bind_assoc]
      exact writeOnce_handle_inl_intertwine P mem κ i x rs₁' rs₂' hR'
        (fun p => pure (p.1, sA₁, p.2) >>= k₁) (fun p => pure (p.1, sA₁, p.2) >>= k₂)
        fun out rs₁'' rs₂'' hR'' => by
          erw [pure_bind, pure_bind]
          exact hcont out (sA₁, rs₁'') (sA₁, rs₂'') ⟨rfl, hR''⟩
  · erw [adaptiveExecMachine_handle_inl_status, adaptiveExecMachine_handle_inl_status,
      pure_bind, pure_bind]
    rw [hR'.2.1]
    exact hcont rs₂'.corrupted _ _ ⟨rfl, hR'⟩
  · change (Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode (P.withWriteOnce mem) κ
        (A.initial κ)).runFrom (liftAdaptiveNet (((mapNetRAdversary (projectWriteOnceNetR P.memory)
          A).machine κ).handle a |>.run sA₁)) rs₁' >>= k₁) =
      Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode P κ (A.initial κ)).runFrom
        (liftAdaptiveNet (((A.machine κ).handle a).run sA₁)) rs₂' >>= k₂
    erw [bind_map_left, bind_map_left]
    exact runFrom_adaptiveRouter_projectWriteOnce mode P mem hmem κ (A.initial κ)
      (((A.machine κ).handle a).run sA₁) rs₁' rs₂' hR' _ _
      fun ⟨r, sA'⟩ rs₁'' rs₂'' hR'' => hcont r (sA', rs₁'') (sA', rs₂'') ⟨rfl, hR''⟩

/-- Projecting `.corrupt` reports from `P.withWriteOnce mem` back to `P` preserves the exact
`ProbComp Bool` execution distribution for every environment, adversary, and corruption mode,
provided `mem` retains router history whenever `P.memory = .nonErasing`. -/
theorem adaptiveExec_withWriteOnce_project (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (mem : PartyMemory)
    (hmem : P.memory = .nonErasing → mem = .nonErasing)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec mode (P.withWriteOnce mem)
        (mapNetRAdversary (projectWriteOnceNetR P.memory) A) Z κ z =
      adaptiveExec mode P A Z κ z := by
  simp only [adaptiveExec, Machine.run, Machine.link]
  refine congrArg Machine.closeProgram ?_
  erw [Machine.sample_comp_init, Machine.sample_comp_init]
  have hPinit : ProbOracleComp.sample (spec := OracleSpec.empty)
      ((adaptiveRouter mode (P.withWriteOnce mem) κ (A.initial κ)).init) =
      ProbOracleComp.sample (recordProbCoins (P.machine κ).init) >>= fun p =>
        let s₀ : WriteOnceState (P.machine κ).State In Out View n :=
          { inner := p.1, initCoins := p.2, tapes := fun _ => [] }
        let s₁ := (P.withWriteOnce mem).applyInitialCorruptions κ (A.initial κ) s₀
        pure (
          { inner := s₁
            corrupted := A.initial κ
            trace := fun i => [(P.withWriteOnce mem).view κ i s₁] } :
          AdaptiveRouterState _ _ n) := by
    dsimp only [adaptiveRouter, AdaptiveProtocol.withWriteOnce]
    erw [ProbOracleComp.sample_bind, ProbOracleComp.sample_bind, bind_assoc]
    simp only [ProbOracleComp.sample_pure, pure_bind]
  have hPinit₂ : ProbOracleComp.sample (spec := OracleSpec.empty)
      ((adaptiveRouter mode P κ (A.initial κ)).init) =
      ProbOracleComp.sample (recordProbCoins (P.machine κ).init) >>= fun p =>
        let s₁ := P.applyInitialCorruptions κ (A.initial κ) p.1
        pure (
          { inner := s₁
            corrupted := A.initial κ
            trace := fun i => [P.view κ i s₁] } :
          AdaptiveRouterState _ _ n) := by
    dsimp only [adaptiveRouter]
    conv_lhs => rw [← fst_map_recordProbCoins (P.machine κ).init]
    rw [ProbOracleComp.sample_bind, ProbOracleComp.sample_map, bind_map_left]
    refine bind_congr fun p => ?_
    rw [ProbOracleComp.sample_pure]
  dsimp only [mapNetRAdversary] at hPinit ⊢
  erw [hPinit, hPinit₂, bind_assoc, bind_assoc, bind_assoc, bind_assoc]
  refine bind_congr fun p => ?_
  erw [pure_bind, pure_bind, bind_assoc, bind_assoc]
  refine bind_congr fun sA => ?_
  erw [pure_bind, pure_bind]
  refine runFrom_adaptiveExecMachine_withWriteOnce_project mode P mem hmem A κ (Z κ z) sA _ _ ?_
  refine ⟨?_, rfl, fun j => ?_⟩
  · exact congrArg WriteOnceState.inner
      (withWriteOnce_applyInitialCorruptions_eq P mem κ (A.initial κ) _)
  · simp only [List.map_cons, List.map_nil]
    exact congrArg (fun x => [P.view κ j x])
      (congrArg WriteOnceState.inner
        (withWriteOnce_applyInitialCorruptions_eq P mem κ (A.initial κ) _))

private theorem runFrom_adaptiveExecMachine_withWriteOnce_erasing {α : Type}
    (mode : CorruptionMode) (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR (WriteOnceView In Out View) AdvQ AdvR) (κ : ℕ)
    (program : ProbOracleComp (adaptiveExecSpec n In Out AdvQ AdvR) α)
    (sA : (A.machine κ).State)
    (rs₁ rs₂ : AdaptiveRouterState
      (WriteOnceState (P.machine κ).State In Out View n) (WriteOnceView In Out View) n)
    (hinner : rs₁.inner = rs₂.inner) (hcor : rs₁.corrupted = rs₂.corrupted) :
    Prod.fst <$> (adaptiveExecMachine mode (P.withWriteOnce .nonErasing)
        (mapNetRAdversary dropWriteOnceTapeNetR A) κ).runFrom program (sA, rs₁) =
      Prod.fst <$> (adaptiveExecMachine mode (P.withWriteOnce .erasing) A κ).runFrom
        program (sA, rs₂) := by
  rw [map_eq_pure_bind, map_eq_pure_bind]
  refine Machine.runFrom_intertwine
    (adaptiveExecMachine mode (P.withWriteOnce .nonErasing)
      (mapNetRAdversary dropWriteOnceTapeNetR A) κ)
    (adaptiveExecMachine mode (P.withWriteOnce .erasing) A κ) (fun _ => True)
    (fun x₁ x₂ => x₁.1 = x₂.1 ∧ x₁.2.inner = x₂.2.inner ∧ x₁.2.corrupted = x₂.2.corrupted)
    program (OracleComp.QueriesSatisfy.of_forall (fun q => by cases q <;> trivial) _)
    (sA, rs₁) (sA, rs₂) ⟨rfl, hinner, hcor⟩ (fun x => pure x.1) (fun x => pure x.1)
    (fun _ _ _ _ => rfl) fun q ⟨sA₁, rs₁'⟩ ⟨sA₂, rs₂'⟩ k₁ k₂ _ ⟨hsA, hi, hc⟩ hcont => ?_
  dsimp only [adaptiveExecMachine, Machine.comp, liftAdaptiveAdversary, Machine.liftRight]
    at sA₁ rs₁' sA₂ rs₂' hsA
  subst hsA
  rcases q with (⟨i, x⟩ | _) | a
  · erw [adaptiveExecMachine_handle_inl_party, adaptiveExecMachine_handle_inl_party]
    by_cases hi_mem : i ∈ rs₁'.corrupted
    · have hi₂ : i ∈ rs₂'.corrupted := hc ▸ hi_mem
      simp only [hi_mem, hi₂, ↓reduceIte]
      erw [pure_bind, pure_bind]
      exact hcont none _ _ ⟨rfl, hi, hc⟩
    · have hi₂ : i ∉ rs₂'.corrupted := hc ▸ hi_mem
      simp only [hi_mem, hi₂, ↓reduceIte]
      dsimp only [AdaptiveProtocol.withWriteOnce, StateT.run]
      rw [hi]
      conv_lhs => erw [bind_assoc, bind_assoc]
      conv_rhs => erw [bind_assoc, bind_assoc]
      refine bind_congr fun ⟨⟨out, s'⟩, coins⟩ => ?_
      erw [pure_bind, pure_bind, pure_bind, pure_bind]
      exact hcont out _ _ ⟨rfl, rfl, hc⟩
  · erw [adaptiveExecMachine_handle_inl_status, adaptiveExecMachine_handle_inl_status,
      pure_bind, pure_bind]
    rw [hc]
    exact hcont rs₂'.corrupted _ _ ⟨rfl, hi, hc⟩
  · change (Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode (P.withWriteOnce .nonErasing) κ
        (A.initial κ)).runFrom (liftAdaptiveNet (((mapNetRAdversary dropWriteOnceTapeNetR
          A).machine κ).handle a |>.run sA₁)) rs₁' >>= k₁) =
      Equiv.prodAssoc _ _ _ <$> (adaptiveRouter mode (P.withWriteOnce .erasing) κ
        (A.initial κ)).runFrom (liftAdaptiveNet (((A.machine κ).handle a).run sA₁)) rs₂' >>= k₂
    erw [bind_map_left, bind_map_left]
    exact runFrom_adaptiveRouter_dropWriteOnce mode P κ (A.initial κ)
      (((A.machine κ).handle a).run sA₁) rs₁' rs₂' hi hc _ _
      fun ⟨r, sA'⟩ rs₁'' rs₂'' hi' hc' => hcont r (sA', rs₁'') (sA', rs₂'') ⟨rfl, hi', hc'⟩

/-- Dropping `.tape` and `.history` in `.nonErasing` `withWriteOnce` execution yields the exact
`ProbComp Bool` execution of `P.withWriteOnce .erasing`. -/
theorem adaptiveExec_withWriteOnce_erasing (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR (WriteOnceView In Out View) AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec mode (P.withWriteOnce .nonErasing)
        (mapNetRAdversary dropWriteOnceTapeNetR A) Z κ z =
      adaptiveExec mode (P.withWriteOnce .erasing) A Z κ z := by
  simp only [adaptiveExec, Machine.run, Machine.link]
  refine congrArg Machine.closeProgram ?_
  erw [Machine.sample_comp_init, Machine.sample_comp_init]
  have hPinit (mem : PartyMemory) : ProbOracleComp.sample (spec := OracleSpec.empty)
      ((adaptiveRouter mode (P.withWriteOnce mem) κ (A.initial κ)).init) =
      ProbOracleComp.sample (recordProbCoins (P.machine κ).init) >>= fun p =>
        let s₀ : WriteOnceState (P.machine κ).State In Out View n :=
          { inner := p.1, initCoins := p.2, tapes := fun _ => [] }
        let s₁ := (P.withWriteOnce mem).applyInitialCorruptions κ (A.initial κ) s₀
        pure (
          { inner := s₁
            corrupted := A.initial κ
            trace := fun i => [(P.withWriteOnce mem).view κ i s₁] } :
          AdaptiveRouterState _ _ n) := by
    dsimp only [adaptiveRouter, AdaptiveProtocol.withWriteOnce]
    erw [ProbOracleComp.sample_bind, ProbOracleComp.sample_bind, bind_assoc]
    simp only [ProbOracleComp.sample_pure, pure_bind]
  dsimp only [mapNetRAdversary] at hPinit ⊢
  erw [hPinit .nonErasing, hPinit .erasing, bind_assoc, bind_assoc, bind_assoc, bind_assoc]
  refine bind_congr fun p => ?_
  erw [pure_bind, pure_bind, bind_assoc, bind_assoc]
  refine bind_congr fun sA => ?_
  erw [pure_bind, pure_bind]
  refine runFrom_adaptiveExecMachine_withWriteOnce_erasing mode P A κ (Z κ z) sA _ _ ?_ rfl
  simp [withWriteOnce_applyInitialCorruptions_eq]

/-- Concrete adaptive emulation in the coin-exposing `.nonErasing` write-once wrapper implies
concrete adaptive emulation of the underlying protocol `P` (including when `P.memory = .erasing`)
with identical simulator budget and error. -/
theorem AdaptiveEmulatesWithin.of_writeOnce {mode : CorruptionMode}
    {P : AdaptiveProtocol n In Out NetQ NetR View}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin mode (P.withWriteOnce .nonErasing) Q g ε) :
    AdaptiveEmulatesWithin mode P Q g ε := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hSg, hadv⟩ := h AdvQ AdvR
    (mapNetRAdversary (projectWriteOnceNetR P.memory) A) pA (hA.mapNetR _)
  refine ⟨S, pS, hS, hSg, fun Z pZ hZ κ z => ?_⟩
  have heq : adaptiveAdvantage mode P Q A S Z κ z =
      adaptiveAdvantage mode (P.withWriteOnce .nonErasing) Q
        (mapNetRAdversary (projectWriteOnceNetR P.memory) A) S Z κ z := by
    rw [adaptiveAdvantage,
      ← adaptiveExec_withWriteOnce_project mode P .nonErasing (fun _ => rfl) A Z κ z,
      adaptiveAdvantage]
  rw [heq]
  exact hadv Z pZ hZ κ z

/-- Asymptotic adaptive emulation in the coin-exposing `.nonErasing` write-once wrapper implies
asymptotic adaptive emulation of `P` (valid in particular when `P.memory = .erasing`). -/
theorem AdaptiveEmulates.of_writeOnce {mode : CorruptionMode}
    {P : AdaptiveProtocol n In Out NetQ NetR View}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    (h : AdaptiveEmulates mode (P.withWriteOnce .nonErasing) Q) :
    AdaptiveEmulates mode P Q := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hadv⟩ := h AdvQ AdvR
    (mapNetRAdversary (projectWriteOnceNetR P.memory) A) pA (hA.mapNetR _)
  refine ⟨S, pS, hS, fun pZ => ?_⟩
  obtain ⟨ν, hν, hbound⟩ := hadv pZ
  refine ⟨ν, hν, fun Z hZ κ z => ?_⟩
  have heq : adaptiveAdvantage mode P Q A S Z κ z =
      adaptiveAdvantage mode (P.withWriteOnce .nonErasing) Q
        (mapNetRAdversary (projectWriteOnceNetR P.memory) A) S Z κ z := by
    rw [adaptiveAdvantage,
      ← adaptiveExec_withWriteOnce_project mode P .nonErasing (fun _ => rfl) A Z κ z,
      adaptiveAdvantage]
  rw [heq]
  exact hbound Z hZ κ z

/-- Concrete adaptive emulation for `P.withWriteOnce .nonErasing` implies concrete adaptive
emulation for `P.withWriteOnce .erasing` with identical simulator budget and error. -/
theorem AdaptiveEmulatesWithin.erasing_of_writeOnce {mode : CorruptionMode}
    {P : AdaptiveProtocol n In Out NetQ NetR View}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin mode (P.withWriteOnce .nonErasing) Q g ε) :
    AdaptiveEmulatesWithin mode (P.withWriteOnce .erasing) Q g ε := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hSg, hadv⟩ := h AdvQ AdvR
    (mapNetRAdversary dropWriteOnceTapeNetR A) pA (hA.mapNetR _)
  refine ⟨S, pS, hS, hSg, fun Z pZ hZ κ z => ?_⟩
  have heq : adaptiveAdvantage mode (P.withWriteOnce .erasing) Q A S Z κ z =
      adaptiveAdvantage mode (P.withWriteOnce .nonErasing) Q
        (mapNetRAdversary dropWriteOnceTapeNetR A) S Z κ z := by
    rw [adaptiveAdvantage, ← adaptiveExec_withWriteOnce_erasing mode P A Z κ z, adaptiveAdvantage]
  rw [heq]
  exact hadv Z pZ hZ κ z

/-- Asymptotic adaptive emulation for `P.withWriteOnce .nonErasing` implies asymptotic adaptive
emulation for `P.withWriteOnce .erasing`. -/
theorem AdaptiveEmulates.erasing_of_writeOnce {mode : CorruptionMode}
    {P : AdaptiveProtocol n In Out NetQ NetR View}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    (h : AdaptiveEmulates mode (P.withWriteOnce .nonErasing) Q) :
    AdaptiveEmulates mode (P.withWriteOnce .erasing) Q := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hadv⟩ := h AdvQ AdvR
    (mapNetRAdversary dropWriteOnceTapeNetR A) pA (hA.mapNetR _)
  refine ⟨S, pS, hS, fun pZ => ?_⟩
  obtain ⟨ν, hν, hbound⟩ := hadv pZ
  refine ⟨ν, hν, fun Z hZ κ z => ?_⟩
  have heq : adaptiveAdvantage mode (P.withWriteOnce .erasing) Q A S Z κ z =
      adaptiveAdvantage mode (P.withWriteOnce .nonErasing) Q
        (mapNetRAdversary dropWriteOnceTapeNetR A) S Z κ z := by
    rw [adaptiveAdvantage, ← adaptiveExec_withWriteOnce_erasing mode P A Z κ z, adaptiveAdvantage]
  rw [heq]
  exact hbound Z hZ κ z

end Projection

end Cslib.Crypto.Protocols.UC
