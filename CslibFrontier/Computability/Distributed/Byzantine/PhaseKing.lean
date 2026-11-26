/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Byzantine.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Computability.Distributed.Byzantine.NodeBound
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Data.Fintype.EquivFin

/-!
# Two-round rotating-king protocol and multivalued-to-binary reduction steps

The recursive oral messages protocol
(`CslibFrontier.Computability.Distributed.Byzantine.RecursiveOralMessages`) solves synchronous
Byzantine agreement for `n > 3t` in `t + 1` rounds by relaying full trees of depth `t + 1`, so its
message size grows exponentially in `t`. This module lands two polynomial-communication synchronous
protocol steps toward `#7210` (`#3261`) in `Cslib.Distributed.Byzantine`:

1. **Two-round rotating-king protocol step (`phaseKing`, after
   [Berman and Garay][BermanGaray1989]):** a `2 * (t + 1)`-round deterministic protocol over any
   `[DecidableEq V]` for `4 * t < Fintype.card P` in which **every point-to-point message is a
   single value of `V`** (`Msg = V`) and each process stores three fields (`PhaseKingState V`).
   Primary-source locator verification against the paywalled `[BermanGaray1989]` proceedings text,
   inventory registration, and the 3-round-per-phase `3 * t < n` extension of
   [Berman, Garay and Perry][BermanGarayPerry1989] remain open under `#7210`. Given an injective
   schedule `kings : Fin (t + 1) ↪ P` of `t + 1` phase kings:
   * In round `2 * k` (universal broadcast), every process broadcasts its current estimate `est`.
     Because `4 * t < n` implies `n < 2 * (n - 2 * t)`, at most one value `x : V` appears at least
     `n - 2 * t` times (and a fortiori at most one appears at least `n - t` times). Each process
     records `kingProposal` (`x` if some `x` has multiplicity `≥ n - 2 * t`, else `est`) and
     `overwhelming` (`some x` if some `x` has multiplicity `≥ n - t`, else `none`).
   * In round `2 * k + 1` (king tie-break), `kings k` broadcasts its `kingProposal`, and every
     process updates `est` to `x` when `overwhelming = some x` and to the value received from
     `kings k` otherwise.

   Unanimity among correct processes persists across every phase whenever `2 * t < n`
   (`phaseKing_persists`), even if `kings k` is faulty and equivocates. By the pigeonhole
   principle at least one of the `t + 1` distinct kings is correct, and in its phase all correct
   processes converge to that king's proposal whenever `4 * t < n`
   (`phaseKing_converges_of_notMem`): if any correct process had `overwhelming = some x`
   (`multiplicity ≥ n - t`), at least `n - 2 * t` correct processes broadcast `x`, so the correct
   king also saw `multiplicity ≥ n - 2 * t` and proposed `x`. The threshold `4 * t < n` is sharp
   for this 2-round phase structure: on `Fin 4` with `t = 1`, `phaseKing` fails for every king
   schedule and round bound (`phaseKing_fails_four_one`), because a single traitor can create a
   `2`-versus-`2` tie at `n - 2 * t = 2` for an honest king while giving another honest process
   multiplicity `n - t = 3`.

2. **Multivalued-to-binary reduction step (`turpinCoan`, after
   [Turpin and Coan, §§2–3, pp. 74–75][TurpinCoan1984]):** given any `R₀`-round binary protocol
   `πBool : Protocol P SBool MBool` solving `SolvesByzantineAgreement t R₀`,
   `turpinCoan t default πBool` solves multivalued Byzantine agreement over any `[DecidableEq V]`
   in `R₀ + 2` rounds for **all** `3 * t < Fintype.card P` (`turpinCoan_solvesByzantineAgreement`),
   sending `V`-values in **round 1 only** (`turpinCoan_valueMessagesSent_eq`). Verified against the
   published IPL text (`§§1–4, pp. 73–75` in `manual/sources.md`); inventory registration remains
   open under `#7210` pending an outside-fleet source check:
   * In round 1 (`r = 0`), every process broadcasts its initial value `input : V` and marks itself
     `perplexed` if `2 * #{j | heard j = input} ≤ n + t` (the exact integer-multiplied form of
     `#{j | heard j ≠ input} ≥ (n - t) / 2` in `[TurpinCoan1984]`, §2, p. 74).
   * In round 2 (`r = 1`), every process broadcasts its 1-bit `perplexed : Bool` flag, sets
     `alert := decide (n - 2 * t ≤ #{j | perp j = true})`, records as `candidate` the unique value
     vouched for by more than `t` non-perplexed senders (`uniqueAboveOn ... (t + 1)`), and
     initializes `πBool` on `alert`.
   * Rounds `3` through `R₀ + 2` run `πBool`; processes decide `default` when `πBool` outputs
     `true` and `candidate` when `πBool` outputs `false`.

### Model and threshold notes

* **Value-domain wrapper (`MultivaluedProtocol`):** `Cslib.Distributed.Byzantine.Protocol` fixes
  input and output values to `Bool`. `MultivaluedProtocol P State Msg Val` generalizes only the
  input/output type to `Val` with identical synchronous execution semantics, bridges losslessly to
  `Protocol` at `Val = Bool` (`MultivaluedProtocol.toProtocol`), and inherits the `2 ≤ n ≤ 3t`
  impossibility bound (`MultivaluedProtocol.not_solvesByzantineAgreement`) for `[Nontrivial Val]`.
* **Exact threshold and self-message conventions:** `phaseKing` uses `n - 2 * t` for the king's
  proposal threshold and `n - t` for the overwhelming-majority lock (`uniqueAboveOn` returns `none`
  if multiple values tie above threshold, which cannot occur when `4 * t < n`). In `turpinCoan`,
  `2 * count(input) ≤ n + t` expresses `[TurpinCoan1984]` §2's rational threshold
  `count(other) ≥ (n - t) / 2` without division, self-messages in `MultivaluedProtocol` fill local
  `v(j)` and `p(j)` slots for correct processes (so `turpinCoan_valueMessagesSent_eq` counts all
  `(n - |F|) * n` round-1 transmissions), and `candidate` is evaluated uniformly via
  `uniqueAboveOn {j | perp j = false} (t + 1) heard` on both content and perplexed processes
  (matching §2–§3's majority vote when `alert = false`; §4's optional 1-round `2T + 5` variant for
  biased binary protocols is not formalized).

## Main definitions

* `Cslib.Distributed.Byzantine.MultivaluedProtocol`: synchronous deterministic protocol over an
  arbitrary value domain `Val`.
* `Cslib.Distributed.Byzantine.MultivaluedProtocol.state`,
  `Cslib.Distributed.Byzantine.MultivaluedProtocol.decision`: execution and decision against a
  faulty set `F`.
* `Cslib.Distributed.Byzantine.MultivaluedProtocol.SolvesByzantineAgreement`: agreement and
  validity over `Val` against at most `t` faults after `R` rounds.
* `Cslib.Distributed.Byzantine.MultivaluedProtocol.toProtocol`: conversion of a `Bool`-valued
  `MultivaluedProtocol` to `Cslib.Distributed.Byzantine.Protocol`.
* `Cslib.Distributed.Byzantine.uniqueAboveOn`: unique value on a finite domain meeting a
  multiplicity threshold `k`.
* `Cslib.Distributed.Byzantine.PhaseKingState`: three-field local state of `phaseKing`.
* `Cslib.Distributed.Byzantine.phaseKing`: 2-round-per-phase rotating-king protocol step toward
  `#7210` (`Msg = V`, `4 * t < Fintype.card P`).
* `Cslib.Distributed.Byzantine.TurpinCoanMsg`, `Cslib.Distributed.Byzantine.TurpinCoanState`:
  message sum and local state of `turpinCoan`.
* `Cslib.Distributed.Byzantine.turpinCoan`: `(R₀ + 2)`-round multivalued-to-binary reduction step
  toward `#7210` (after `[TurpinCoan1984]`, §§2–3).
* `Cslib.Distributed.Byzantine.turpinCoanValueMessagesSent`: count of value-bearing messages
  emitted by correct processes over `R` rounds of `turpinCoan`.

## Main results

* `Cslib.Distributed.Byzantine.MultivaluedProtocol.not_solvesByzantineAgreement`: no protocol over
  a nontrivial value domain tolerates `t` faults when `2 ≤ Fintype.card P ≤ 3 * t`.
* `Cslib.Distributed.Byzantine.uniqueAboveOn_eq_some_iff`,
  `Cslib.Distributed.Byzantine.uniqueAboveOn_eq_some_iff_of_lt_two_mul`: uniqueness and strict
  majority characterizations of `uniqueAboveOn`.
* `Cslib.Distributed.Byzantine.phaseKing_persists`: unanimity among correct processes persists
  across every 2-round phase whenever `2 * t < Fintype.card P`.
* `Cslib.Distributed.Byzantine.phaseKing_converges_of_notMem`: a phase with a correct king brings
  all correct processes to the same estimate whenever `4 * t < Fintype.card P`.
* `Cslib.Distributed.Byzantine.phaseKing_solvesByzantineAgreement`: protocol-correctness step
  toward `#7210` showing `phaseKing` solves multivalued Byzantine agreement in `R ≥ 2 * (t + 1)`
  rounds whenever `4 * t < Fintype.card P`.
* `Cslib.Distributed.Byzantine.exists_polyMsg_solvesByzantineAgreement`: single-value-message
  protocol existence step toward `#7210` for `4 * t < Fintype.card P` in `R ≥ 2 * (t + 1)` rounds.
* `Cslib.Distributed.Byzantine.phaseKing_fails_four_one`: 2-round `phaseKing` fails on `Fin 4`
  against `1` fault for every king schedule and round bound `R`.
* `Cslib.Distributed.Byzantine.turpinCoan_solvesByzantineAgreement`: reduction step toward `#7210`
  showing `turpinCoan` solves multivalued Byzantine agreement in `R₀ + 2` rounds for all
  `3 * t < Fintype.card P`.
* `Cslib.Distributed.Byzantine.turpinCoan_valueMessagesSent_eq`: across `R + 1` rounds of
  `turpinCoan`, correct processes transmit `(Fintype.card P - F.card) * Fintype.card P`
  value-bearing messages (round 1 only).

## References

* [P. Berman, J. A. Garay, *Asymptotically optimal distributed consensus (extended
  abstract)*][BermanGaray1989]
* [P. Berman, J. A. Garay, K. J. Perry, *Towards optimal distributed
  consensus*][BermanGarayPerry1989]
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
* [R. Turpin, B. A. Coan, *Extending binary Byzantine agreement to multivalued Byzantine
  agreement*][TurpinCoan1984]
-/

public section

namespace Cslib.Distributed.Byzantine

open Finset

/-! ### Multivalued synchronous protocols -/

/-- A deterministic synchronous message-passing protocol on the complete graph of processes `P`
with input and decision values in `Val`.

This is the value-parameterized counterpart of `Cslib.Distributed.Byzantine.Protocol` (which fixes
`Val = Bool`), sharing the same synchronous round execution against static Byzantine faults. -/
structure MultivaluedProtocol (P State Msg Val : Type*) where
  /-- The initial state of a process with a given input value. -/
  init : P → Val → State
  /-- `send r i s j`: the message process `i` in state `s` sends to `j` in round `r + 1`. -/
  send : ℕ → P → State → P → Msg
  /-- `update r i s m`: the state of `i` after round `r + 1`, where `m j` came from `j`. -/
  update : ℕ → P → State → (P → Msg) → State
  /-- The decision of a process in a given state. -/
  output : P → State → Val

namespace MultivaluedProtocol

variable {P S M V : Type*} [DecidableEq P] (π : MultivaluedProtocol P S M V)

/-- The state of process `i` after `r` rounds on inputs `x` when the processes in `F` are faulty
and a faulty `j` sends `adv r j i` to `i` in round `r + 1`. -/
@[expose] def state (F : Finset P) (adv : ℕ → P → P → M) (x : P → V) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (state F adv x r i)
      (fun j => if j ∈ F then adv r j i else π.send r j (state F adv x r j) i)

/-- The decision of process `i` after `R` rounds. -/
@[expose] def decision (F : Finset P) (adv : ℕ → P → P → M) (x : P → V) (R : ℕ) (i : P) : V :=
  π.output i (π.state F adv x R i)

/-- `π` solves multivalued Byzantine agreement over `V` against at most `t` faults in `R` rounds:
whenever at most `t` processes are faulty, all correct processes decide the same value after `R`
rounds, and they decide `v` whenever all correct processes have input `v`. -/
structure SolvesByzantineAgreement (t R : ℕ) : Prop where
  /-- Agreement: all correct processes decide the same value. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (x : P → V),
    ∀ i ∉ F, ∀ j ∉ F, π.decision F adv x R i = π.decision F adv x R j
  /-- Validity: if all correct processes have input `v`, they decide `v`. -/
  validity : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (x : P → V) (v : V),
    (∀ i ∉ F, x i = v) → ∀ i ∉ F, π.decision F adv x R i = v

/-- Tolerating `t` faults implies tolerating at most `t' ≤ t` faults. -/
theorem SolvesByzantineAgreement.mono {π : MultivaluedProtocol P S M V} {t t' R : ℕ}
    (h : π.SolvesByzantineAgreement t R) (ht : t' ≤ t) : π.SolvesByzantineAgreement t' R where
  agreement F hF := h.agreement F (hF.trans ht)
  validity F hF := h.validity F (hF.trans ht)

/-- Reinterpret a `Bool`-valued `MultivaluedProtocol` as a
`Cslib.Distributed.Byzantine.Protocol`. -/
@[expose] def toProtocol (π : MultivaluedProtocol P S M Bool) : Protocol P S M where
  init := π.init
  send := π.send
  update := π.update
  output := π.output

/-- Execution states of `π.toProtocol` coincide with those of `π`. -/
@[simp] theorem toProtocol_state (π : MultivaluedProtocol P S M Bool) (F : Finset P)
    (adv : ℕ → P → P → M) (x : P → Bool) :
    ∀ r, π.toProtocol.state F adv x r = π.state F adv x r
  | 0 => rfl
  | r + 1 => funext fun i => by
    simp only [Protocol.state, state, toProtocol_state π F adv x r]
    rfl

/-- Decisions of `π.toProtocol` coincide with those of `π`. -/
@[simp] theorem toProtocol_decision (π : MultivaluedProtocol P S M Bool) (F : Finset P)
    (adv : ℕ → P → P → M) (x : P → Bool) (R : ℕ) (i : P) :
    π.toProtocol.decision F adv x R i = π.decision F adv x R i := by
  rw [Protocol.decision, decision, toProtocol_state]
  rfl

/-- `π.toProtocol` solves binary `Protocol.SolvesByzantineAgreement` if and only if `π` solves
`MultivaluedProtocol.SolvesByzantineAgreement`. -/
@[simp] theorem toProtocol_solvesByzantineAgreement_iff (π : MultivaluedProtocol P S M Bool)
    (t R : ℕ) :
    π.toProtocol.SolvesByzantineAgreement t R ↔ π.SolvesByzantineAgreement t R := by
  constructor <;> intro h <;> exact
    { agreement := fun F hF adv x i hi j hj => by
        simpa only [toProtocol_decision] using h.agreement F hF adv x i hi j hj
      validity := fun F hF adv x v hv i hi => by
        simpa only [toProtocol_decision] using h.validity F hF adv x v hv i hi }

/-- Over any nontrivial value domain `V`, no deterministic synchronous protocol on
`2 ≤ Fintype.card P ≤ 3 * t` processes solves multivalued Byzantine agreement against `t` faults:
embedding two distinct values of `V` as `Bool` reduces to `Protocol.not_solvesByzantineAgreement`
(after [Fischer, Lynch and Merritt, Theorem 1 and §3.1][FischerLynchMerritt1985]). -/
theorem not_solvesByzantineAgreement [Fintype P] [Nontrivial V] {t R : ℕ}
    (h2 : 2 ≤ Fintype.card P) (h3 : Fintype.card P ≤ 3 * t) :
    ¬ π.SolvesByzantineAgreement t R := by
  classical
  intro h
  obtain ⟨v₀, v₁, hne⟩ := exists_pair_ne V
  let πB : Protocol P S M := {
    init := fun i b => π.init i (if b then v₁ else v₀)
    send := π.send
    update := π.update
    output := fun i s => decide (π.output i s = v₁)
  }
  have hstate (F) (adv) (x : P → Bool) (r : ℕ) :
      πB.state F adv x r = π.state F adv (fun i => if x i then v₁ else v₀) r := by
    induction r with
    | zero => rfl
    | succ r ih =>
      funext i
      simp only [Protocol.state, state]
      rw [ih]
  refine πB.not_solvesByzantineAgreement (R := R) h2 h3 ⟨?_, ?_⟩
  · intro F hF adv x i hi j hj
    simp only [Protocol.decision, πB, hstate]
    exact congrArg (fun v => decide (v = v₁)) (h.agreement F hF adv _ i hi j hj)
  · intro F hF adv x b hb i hi
    have hval := h.validity F hF adv (fun j => if x j then v₁ else v₀) (if b then v₁ else v₀)
      (fun j hj => by rw [hb j hj]) i hi
    simp only [Protocol.decision, πB, hstate, MultivaluedProtocol.decision] at hval ⊢
    rw [hval]
    cases b <;> simp [hne]

end MultivaluedProtocol

/-! ### Unique threshold extraction -/

/-- Return `some v` when `v` is the unique value in `dom.image f` whose multiplicity on `dom` is
at least `k`, and `none` otherwise. -/
@[expose] def uniqueAboveOn {P V : Type*} [DecidableEq V] (dom : Finset P) (k : ℕ) (f : P → V) :
    Option V :=
  let s := (dom.image f).filter fun v => k ≤ (dom.filter fun p => f p = v).card
  if h : s.card = 1 then
    some (s.choose (fun _ => True) (by
      obtain ⟨x, hx⟩ := Finset.card_eq_one.1 h
      exact ⟨x, ⟨by rw [hx]; exact Finset.mem_singleton_self x, trivial⟩,
        fun y hy => by rw [hx, Finset.mem_singleton] at hy; exact hy.1⟩))
  else none

/-- For `1 ≤ k`, `uniqueAboveOn dom k f = some v` if and only if `v` appears at least `k` times on
`dom` and every value appearing at least `k` times on `dom` equals `v`. -/
theorem uniqueAboveOn_eq_some_iff {P V : Type*} [DecidableEq V] {dom : Finset P} {k : ℕ}
    (hk : 1 ≤ k) {f : P → V} {v : V} :
    uniqueAboveOn dom k f = some v ↔
      k ≤ (dom.filter fun p => f p = v).card ∧
        ∀ w, k ≤ (dom.filter fun p => f p = w).card → w = v := by
  have hmem : ∀ w,
      w ∈ (dom.image f).filter (fun w => k ≤ (dom.filter fun p => f p = w).card) ↔
        k ≤ (dom.filter fun p => f p = w).card := by
    intro w
    simp only [Finset.mem_filter, Finset.mem_image, and_iff_right_iff_imp]
    intro hw
    obtain ⟨p, hp⟩ := Finset.card_pos.1 (lt_of_lt_of_le hk hw)
    exact ⟨p, (Finset.mem_filter.1 hp).1, (Finset.mem_filter.1 hp).2⟩
  unfold uniqueAboveOn
  dsimp only
  split_ifs with hcard
  · simp only [Option.some.injEq]
    obtain ⟨x, hx⟩ := Finset.card_eq_one.1 hcard
    generalize_proofs hp
    have hchoose : Finset.choose (fun _ => True) _ hp = x :=
      Finset.mem_singleton.1 (hx ▸ (Finset.choose_spec (fun _ => True) _ hp).1)
    rw [hchoose]
    have hx_mem : k ≤ (dom.filter fun p => f p = x).card :=
      (hmem x).1 (by rw [hx]; exact Finset.mem_singleton_self x)
    exact ⟨fun h => h ▸ ⟨hx_mem, fun w hw => Finset.mem_singleton.1 (hx ▸ (hmem w).2 hw)⟩,
      fun ⟨_, huniq⟩ => huniq x hx_mem⟩
  · simp only [false_iff, not_and]
    exact fun hv huniq => hcard (Finset.card_eq_one.2 ⟨v, Finset.ext fun w => by
      rw [Finset.mem_singleton, hmem]
      exact ⟨huniq w, fun h => h ▸ hv⟩⟩)

/-- When `dom.card < 2 * k`, at most one value can appear `k` times on `dom`, so
`uniqueAboveOn dom k f = some v` holds precisely when `v` has multiplicity at least `k`. -/
theorem uniqueAboveOn_eq_some_iff_of_lt_two_mul {P V : Type*} [DecidableEq V] {dom : Finset P}
    {k : ℕ} (hdom : dom.card < 2 * k) {f : P → V} {v : V} :
    uniqueAboveOn dom k f = some v ↔ k ≤ (dom.filter fun p => f p = v).card := by
  classical
  rw [uniqueAboveOn_eq_some_iff (by omega)]
  exact ⟨And.left, fun hv => ⟨hv, fun w hw => by finset_card⟩⟩

private theorem card_filter_le_of_eqOn_sdiff {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] {F : Finset P} {m g : P → V} (h : ∀ j ∉ F, m j = g j) (v : V) :
    ((univ \ F).filter fun j => g j = v).card ≤ (univ.filter fun j => m j = v).card :=
  Finset.card_le_card fun j hj => by
    simp only [Finset.mem_filter, Finset.mem_sdiff] at hj ⊢
    exact ⟨hj.1.1, (h j hj.1.2).trans hj.2⟩

private theorem card_filter_le_sdiff_add {P V : Type*} [Fintype P] [DecidableEq P]
    [DecidableEq V] {F : Finset P} {m g : P → V} (h : ∀ j ∉ F, m j = g j) (v : V) :
    (univ.filter fun j => m j = v).card ≤
      ((univ \ F).filter fun j => g j = v).card + F.card := by
  refine (Finset.card_le_card fun j hj => ?_).trans (Finset.card_union_le _ _)
  rw [Finset.mem_filter] at hj
  by_cases hjF : j ∈ F
  · exact Finset.mem_union_right _ hjF
  · exact Finset.mem_union_left _
      (Finset.mem_filter.2 ⟨Finset.mem_sdiff.2 ⟨hj.1, hjF⟩, (h j hjF).symm.trans hj.2⟩)

/-! ### Two-round rotating-king protocol step (`4 * t < n`) -/

/-- Local state of a process in the 2-round-per-phase `phaseKing` protocol: its current estimate
`est`, the tie-break value `kingProposal` it would broadcast as phase king in the second round of
the current phase, and the `overwhelming` value (if any) seen with multiplicity at least `n - t` in
the first round of the current phase. -/
structure PhaseKingState (V : Type*) where
  /-- Current decision estimate. -/
  est : V
  /-- Value proposed as phase king in round `2 * k + 1` (`multiplicity ≥ n - 2 * t`, else `est`). -/
  kingProposal : V
  /-- Unique value received at least `n - t` times in round `2 * k`, if any. -/
  overwhelming : Option V
  deriving @[expose] DecidableEq

section PhaseKing

variable {P V : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- Two-round-per-phase rotating-king protocol step toward `#7210` (after
[Berman and Garay][BermanGaray1989]; primary-source locator verification and the 3-round-per-phase
`3 * t < n` extension of [Berman, Garay and Perry][BermanGarayPerry1989] remain open under `#7210`).

Runs `t + 1` two-round phases indexed by `kings : Fin (t + 1) ↪ P`, with every point-to-point
message a single element of `V`:
* **Round `2 * k` (`r % 2 = 0`, `r / 2 = k < t + 1`):** every process broadcasts `s.est`, sets
  `kingProposal` to the unique value of multiplicity `≥ n - 2 * t` (defaulting to `s.est`), and
  sets `overwhelming` to the unique value of multiplicity `≥ n - t` (if any).
* **Round `2 * k + 1` (`r % 2 = 1`, `r / 2 = k < t + 1`):** `kings ⟨k, hk⟩` broadcasts
  `s.kingProposal` (other processes send `s.est`), and every process sets `est` to
  `s.overwhelming.getD (m (kings ⟨k, hk⟩))`.
* **Rounds `≥ 2 * (t + 1)`:** local states freeze. -/
@[expose] def phaseKing (t : ℕ) (kings : Fin (t + 1) ↪ P) :
    MultivaluedProtocol P (PhaseKingState V) V V where
  init _ v := ⟨v, v, none⟩
  send r i s _ :=
    if hk : r / 2 < t + 1 then
      if r % 2 = 0 then s.est
      else if i = kings ⟨r / 2, hk⟩ then s.kingProposal else s.est
    else s.est
  update r _ s m :=
    if hk : r / 2 < t + 1 then
      if r % 2 = 0 then
        { est := s.est
          kingProposal := (uniqueAboveOn univ (Fintype.card P - 2 * t) m).getD s.est
          overwhelming := uniqueAboveOn univ (Fintype.card P - t) m }
      else
        { s with est := s.overwhelming.getD (m (kings ⟨r / 2, hk⟩)) }
    else s
  output _ s := s.est

private theorem phaseKing_step_even {t : ℕ} (kings : Fin (t + 1) ↪ P) (F : Finset P)
    (adv : ℕ → P → P → V) (x : P → V) {k : ℕ} (hk : k < t + 1) (i : P) :
    (phaseKing t kings).state F adv x (2 * k + 1) i =
      let s := (phaseKing t kings).state F adv x (2 * k) i
      let m : P → V := fun j =>
        if j ∈ F then adv (2 * k) j i else ((phaseKing t kings).state F adv x (2 * k) j).est
      { est := s.est
        kingProposal := (uniqueAboveOn univ (Fintype.card P - 2 * t) m).getD s.est
        overwhelming := uniqueAboveOn univ (Fintype.card P - t) m } := by
  simp only [MultivaluedProtocol.state, phaseKing, Nat.mul_div_right _ Nat.zero_lt_two, hk,
    ↓reduceDIte, Nat.mul_mod_right, ↓reduceIte]

private theorem phaseKing_step_odd {t : ℕ} (kings : Fin (t + 1) ↪ P) (F : Finset P)
    (adv : ℕ → P → P → V) (x : P → V) {k : ℕ} (hk : k < t + 1) (i : P) :
    ((phaseKing t kings).state F adv x (2 * (k + 1)) i).est =
      let s := (phaseKing t kings).state F adv x (2 * k + 1) i
      let king := kings ⟨k, hk⟩
      s.overwhelming.getD (if king ∈ F then adv (2 * k + 1) king i
        else ((phaseKing t kings).state F adv x (2 * k + 1) king).kingProposal) := by
  rw [show 2 * (k + 1) = (2 * k + 1) + 1 by omega]
  simp only [MultivaluedProtocol.state, phaseKing, show (2 * k + 1) / 2 = k by omega, hk,
    ↓reduceDIte, show (2 * k + 1) % 2 ≠ 0 by omega, ↓reduceIte]

/-- Unanimity persistence for `phaseKing`: across any phase `k < t + 1` (even when
`kings ⟨k, hk⟩ ∈ F` equivocates arbitrarily), if `F.card ≤ t`, `2 * t < Fintype.card P`, and all
correct processes enter phase `k` with `est = v`, then all correct processes finish phase `k` with
`est = v`. -/
theorem phaseKing_persists {t : ℕ} (kings : Fin (t + 1) ↪ P) {F : Finset P} (hF : F.card ≤ t)
    (hn : 2 * t < Fintype.card P) (adv : ℕ → P → P → V) (x : P → V) {k : ℕ} (hk : k < t + 1)
    {v : V} (huniv : ∀ p ∉ F, ((phaseKing t kings).state F adv x (2 * k) p).est = v) :
    ∀ i ∉ F, ((phaseKing t kings).state F adv x (2 * (k + 1)) i).est = v := by
  intro i _
  rw [phaseKing_step_odd kings F adv x hk i, phaseKing_step_even kings F adv x hk i]
  dsimp only
  set m : P → V := fun j =>
    if j ∈ F then adv (2 * k) j i else ((phaseKing t kings).state F adv x (2 * k) j).est
  have hover : uniqueAboveOn univ (Fintype.card P - t) m = some v := by
    rw [uniqueAboveOn_eq_some_iff_of_lt_two_mul (by finset_card)]
    have hsub : univ \ F ⊆ univ.filter (fun j => m j = v) := fun j hj => by
      obtain ⟨hu, hjF⟩ := Finset.mem_sdiff.1 hj
      exact Finset.mem_filter.2 ⟨hu, by simp only [m, hjF, ↓reduceIte, huniv j hjF]⟩
    finset_card
  rw [hover, Option.getD_some]

/-- Honest-king convergence for `phaseKing`: if `F.card ≤ t`, `4 * t < Fintype.card P`, and the
king `kings k` of phase `k` is correct (`kings k ∉ F`), then all correct processes end phase `k`
with the same estimate (namely `kings k`'s `kingProposal` from round `2 * k`). -/
theorem phaseKing_converges_of_notMem {t : ℕ} (kings : Fin (t + 1) ↪ P) {F : Finset P}
    (hF : F.card ≤ t) (hn : 4 * t < Fintype.card P) (adv : ℕ → P → P → V) (x : P → V)
    (k : Fin (t + 1)) (hking : kings k ∉ F) :
    ∀ i ∉ F, ((phaseKing t kings).state F adv x (2 * (k.val + 1)) i).est =
      ((phaseKing t kings).state F adv x (2 * k.val + 1) (kings k)).kingProposal := by
  intro i _
  rw [phaseKing_step_odd kings F adv x k.isLt i, phaseKing_step_even kings F adv x k.isLt i]
  simp only [Fin.eta, hking, ↓reduceIte]
  set mi : P → V := fun j =>
    if j ∈ F then adv (2 * k.val) j i
    else ((phaseKing t kings).state F adv x (2 * k.val) j).est
  cases hover : uniqueAboveOn univ (Fintype.card P - t) mi with
  | none => rfl
  | some v =>
    rw [uniqueAboveOn_eq_some_iff_of_lt_two_mul (by finset_card)] at hover
    -- At least `n - 2 * t` correct processes broadcast `v`, so the correct king sees `≥ n - 2 * t`.
    rw [Option.getD_some, phaseKing_step_even kings F adv x k.isLt (kings k)]
    dsimp only
    set mk : P → V := fun j =>
      if j ∈ F then adv (2 * k.val) j (kings k)
      else ((phaseKing t kings).state F adv x (2 * k.val) j).est
    have hmi := card_filter_le_sdiff_add (F := F) (m := mi)
      (g := fun j => ((phaseKing t kings).state F adv x (2 * k.val) j).est)
      (fun j hj => by simp only [mi, hj, ↓reduceIte]) v
    have hmk := card_filter_le_of_eqOn_sdiff (F := F) (m := mk)
      (g := fun j => ((phaseKing t kings).state F adv x (2 * k.val) j).est)
      (fun j hj => by simp only [mk, hj, ↓reduceIte]) v
    have hk_over : uniqueAboveOn univ (Fintype.card P - 2 * t) mk = some v := by
      rw [uniqueAboveOn_eq_some_iff_of_lt_two_mul (by finset_card)]
      omega
    rw [hk_over, Option.getD_some]

private theorem phaseKing_persists_from {t : ℕ} (kings : Fin (t + 1) ↪ P) {F : Finset P}
    (hF : F.card ≤ t) (hn : 2 * t < Fintype.card P) (adv : ℕ → P → P → V) (x : P → V) {v : V}
    {k m : ℕ} (hkm : k ≤ m) (hm : m ≤ t + 1)
    (huniv : ∀ p ∉ F, ((phaseKing t kings).state F adv x (2 * k) p).est = v) :
    ∀ i ∉ F, ((phaseKing t kings).state F adv x (2 * m) i).est = v := by
  induction m, hkm using Nat.le_induction with
  | base => exact huniv
  | succ m _ ih => exact phaseKing_persists kings hF hn adv x (by omega) (ih (by omega))

/-- `phaseKing` freezes local states once all `t + 1` two-round phases have completed
(`2 * (t + 1) ≤ R`). -/
theorem phaseKing_state_eq_of_le {t : ℕ} (kings : Fin (t + 1) ↪ P) (F : Finset P)
    (adv : ℕ → P → P → V) (x : P → V) {R : ℕ} (hR : 2 * (t + 1) ≤ R) :
    (phaseKing t kings).state F adv x R = (phaseKing t kings).state F adv x (2 * (t + 1)) := by
  induction R, hR using Nat.le_induction with
  | base => rfl
  | succ r hr ih =>
    funext i
    simpa only [MultivaluedProtocol.state, phaseKing, show ¬r / 2 < t + 1 by omega,
      ↓reduceDIte] using congrFun ih i

/-- Protocol-correctness step toward `#7210` (after [Berman and Garay][BermanGaray1989];
primary-source check, inventory registration, and the 3-round-per-phase `3 * t < n` extension of
[Berman, Garay and Perry][BermanGarayPerry1989] remain open under `#7210`): whenever
`4 * t < Fintype.card P` and `2 * (t + 1) ≤ R`, `phaseKing t kings` solves multivalued Byzantine
agreement against at most `t` faults in `R` rounds with single-value messages (`Msg = V`). -/
theorem phaseKing_solvesByzantineAgreement {t : ℕ} (kings : Fin (t + 1) ↪ P)
    (hn : 4 * t < Fintype.card P) {R : ℕ} (hR : 2 * (t + 1) ≤ R) :
    (phaseKing t kings (V := V)).SolvesByzantineAgreement t R where
  agreement F hF adv x i hi j hj := by
    rw [MultivaluedProtocol.decision, MultivaluedProtocol.decision,
      phaseKing_state_eq_of_le kings F adv x hR]
    change ((phaseKing t kings).state F adv x (2 * (t + 1)) i).est =
      ((phaseKing t kings).state F adv x (2 * (t + 1)) j).est
    -- Among `t + 1` distinct kings, at least one lies outside `F` (`F.card ≤ t`).
    obtain ⟨k, hk⟩ : ∃ k : Fin (t + 1), kings k ∉ F := by
      by_contra! hall
      have hsub : univ.map kings ⊆ F := fun p hp => by
        obtain ⟨k, _, rfl⟩ := Finset.mem_map.1 hp; exact hall k
      finset_card
    have hconv := phaseKing_converges_of_notMem kings hF hn adv x k hk
    have hpers := phaseKing_persists_from kings hF (by omega) adv x
      (Nat.succ_le_of_lt k.isLt) le_rfl hconv
    exact (hpers i hi).trans (hpers j hj).symm
  validity F hF adv x v hv i hi := by
    rw [MultivaluedProtocol.decision, phaseKing_state_eq_of_le kings F adv x hR]
    change ((phaseKing t kings).state F adv x (2 * (t + 1)) i).est = v
    exact phaseKing_persists_from kings hF (by omega) adv x (Nat.zero_le (t + 1)) le_rfl
      (fun p hp => hv p hp) i hi

end PhaseKing

/-- Single-value-message existence step toward `#7210` (after [Berman and Garay][BermanGaray1989];
primary-source check and the 3-round-per-phase `3 * t < n` extension of
[Berman, Garay and Perry][BermanGarayPerry1989] remain open under `#7210`): whenever
`4 * t < Fintype.card P` and `2 * (t + 1) ≤ R`, there exists a synchronous protocol over `V` with
constant-field local state `PhaseKingState V` and message alphabet `V` itself
(`2 * (t + 1) * (|P| - |F|) * |P|` honest point-to-point transmissions across the `2 * (t + 1)`
active rounds) solving `t`-resilient Byzantine agreement in `R` rounds. -/
theorem exists_polyMsg_solvesByzantineAgreement {P : Type*} [Fintype P] [DecidableEq P]
    (V : Type*) {t R : ℕ} (hn : 4 * t < Fintype.card P) (hR : 2 * (t + 1) ≤ R) :
    ∃ π : MultivaluedProtocol P (PhaseKingState V) V V, π.SolvesByzantineAgreement t R := by
  classical
  let kings : Fin (t + 1) ↪ P :=
    (Fin.castLEEmb (by omega)).trans (Fintype.equivFin P).symm.toEmbedding
  exact ⟨phaseKing t kings, phaseKing_solvesByzantineAgreement kings hn hR⟩

/-! ### Sharpness of `4 * t < n` for 2-round Phase-King (`Fin 4, t = 1`) -/

private def mkTwoKings (k₀ k₁ : Fin 4) (h : k₀ ≠ k₁) : Fin 2 ↪ Fin 4 where
  toFun i := if i = 0 then k₀ else k₁
  inj' := by
    revert k₀ k₁ h
    decide

private def thirdHonest (k₀ k₁ : Fin 4) : Fin 4 :=
  if k₀ ≠ 0 ∧ k₁ ≠ 0 then 0
  else if k₀ ≠ 1 ∧ k₁ ≠ 1 then 1
  else 2

/-- Sharpness of `4 * t < n` for two-round `phaseKing`: on `Fin 4` with `t = 1` (`4 * t = n`,
contrasting with `om1` and `om`, which succeed on `Fin 4` using 2-round relay vectors/trees),
`phaseKing 1 kings` fails to solve 1-fault Byzantine agreement for **every** king schedule
`kings : Fin 2 ↪ Fin 4` and **every** round bound `R`.

In phase 0, faulty `kings 1` creates a `2`-versus-`2` tie (`multiplicity = n - 2 * t = 2`) at the
honest king `kings 0` while giving another honest process `p` multiplicity `n - t = 3` for the
opposite bit; in phase 1, `kings 1` is the phase king and equivocates to split `kings 0` and `p`. -/
theorem phaseKing_fails_four_one (kings : Fin 2 ↪ Fin 4) (R : ℕ) :
    ¬ (phaseKing 1 kings (V := Bool)).SolvesByzantineAgreement 1 R := by
  intro hsolves
  have hne : kings 0 ≠ kings 1 := kings.injective.ne (by decide)
  have hkings : kings = mkTwoKings (kings 0) (kings 1) hne := by
    ext ⟨_ | _ | _, h⟩
    exacts [rfl, rfl, absurd h (by omega)]
  let p := thirdHonest (kings 0) (kings 1)
  let F : Finset (Fin 4) := {kings 1}
  let x : Fin 4 → Bool := fun i => decide (i ≠ kings 0)
  let adv : ℕ → Fin 4 → Fin 4 → Bool := fun r _ i => if r = 2 then true else decide (i = p)
  have hmin : ∀ i, (phaseKing 1 kings).decision F adv x R i =
      (phaseKing 1 kings).decision F adv x (min R 4) i := by
    intro i
    by_cases hR : 4 ≤ R
    · rw [Nat.min_eq_right hR]
      simp only [MultivaluedProtocol.decision, phaseKing_state_eq_of_le kings F adv x hR,
        phaseKing_state_eq_of_le kings F adv x le_rfl]
    · rw [Nat.min_eq_left (by omega)]
  let r' : Fin 5 := ⟨min R 4, by omega⟩
  have hsuff : ∀ (k₀ k₁ : Fin 4) (h : k₀ ≠ k₁) (r : Fin 5),
      ({k₁} : Finset (Fin 4)).card ≤ 1 ∧ k₀ ∉ ({k₁} : Finset (Fin 4)) ∧
      thirdHonest k₀ k₁ ∉ ({k₁} : Finset (Fin 4)) ∧
      (phaseKing 1 (mkTwoKings k₀ k₁ h)).decision {k₁}
        (fun rd _ i => if rd = 2 then true else decide (i = thirdHonest k₀ k₁))
        (fun i => decide (i ≠ k₀)) r.val k₀ ≠
      (phaseKing 1 (mkTwoKings k₀ k₁ h)).decision {k₁}
        (fun rd _ i => if rd = 2 then true else decide (i = thirdHonest k₀ k₁))
        (fun i => decide (i ≠ k₀)) r.val (thirdHonest k₀ k₁) := by
    decide
  obtain ⟨hF, hk₀, hp, hdis⟩ := hsuff (kings 0) (kings 1) hne r'
  rw [← hkings] at hdis
  have hag := hsolves.agreement F hF adv x (kings 0) hk₀ p hp
  rw [hmin (kings 0), hmin p] at hag
  exact hdis hag

/-! ### Multivalued-to-binary reduction step (`3 * t < n`) -/

/-- Messages sent by `turpinCoan`: an initial domain value `val` in round 1, a 1-bit `perplexed`
flag in round 2, and messages `bin` of the underlying binary protocol in rounds `3` onward. -/
inductive TurpinCoanMsg (V MBool : Type*) where
  /-- Round 1: broadcast of the process's initial value in `V`. -/
  | val (v : V)
  /-- Round 2: 1-bit flag indicating whether the sender was perplexed after round 1. -/
  | perplexed (b : Bool)
  /-- Rounds `≥ 3`: message of the underlying binary Byzantine agreement protocol. -/
  | bin (m : MBool)
  deriving @[expose] DecidableEq

/-- Whether a `TurpinCoanMsg` carries an element of the value domain `V`. -/
@[expose] def TurpinCoanMsg.isVal {V MBool : Type*} : TurpinCoanMsg V MBool → Bool
  | .val _ => true
  | _ => false

/-- Local state of a process in `turpinCoan`. -/
structure TurpinCoanState (P V SBool : Type*) where
  /-- The process's initial input value. -/
  input : V
  /-- `heard j`: the value received from `j` in round 1. -/
  heard : P → V
  /-- Whether this process was perplexed after round 1 (`2 * count(input) ≤ n + t`). -/
  perplexed : Bool
  /-- Candidate value endorsed by more than `t` non-perplexed senders after round 2. -/
  candidate : V
  /-- Local state of the underlying binary protocol from round 3 onward. -/
  binState : SBool

section TurpinCoan

variable {P V SBool MBool : Type*} [Fintype P] [DecidableEq P] [DecidableEq V]

/-- Two-round multivalued-to-binary preprocessing step toward `#7210` (after
[Turpin and Coan, §2, p. 74][TurpinCoan1984]; inventory registration remains open under `#7210`
pending an outside-fleet source check).

Transforms any binary Byzantine agreement protocol `πBool : Protocol P SBool MBool` into a
multivalued protocol over `V` with fallback `default : V` in two preprocessing rounds:
* **Round 1 (`r = 0`):** broadcast `s.input`; become `perplexed` iff
  `2 * #{j | heard j = s.input} ≤ Fintype.card P + t`.
* **Round 2 (`r = 1`):** broadcast `s.perplexed`; set `alert := decide (n - 2 * t ≤ #{j | perp j})`,
  compute `candidate` as the unique value seen in round 1 from at least `t + 1` senders reporting
  `perp j = false` (defaulting to `default`), and initialize `πBool` with `alert`.
* **Rounds `r + 2` (`r ≥ 0`):** run round `r + 1` of `πBool`; decide `default` if `πBool` decides
  `true` (`alert`) and `s.candidate` otherwise. -/
@[expose] def turpinCoan (t : ℕ) (default : V) (πBool : Protocol P SBool MBool) :
    MultivaluedProtocol P (TurpinCoanState P V SBool) (TurpinCoanMsg V MBool) V where
  init i v :=
    { input := v
      heard := fun _ => v
      perplexed := false
      candidate := v
      binState := πBool.init i false }
  send r i s j := match r with
    | 0 => .val s.input
    | 1 => .perplexed s.perplexed
    | r' + 2 => .bin (πBool.send r' i s.binState j)
  update r i s m := match r with
    | 0 =>
      let heard : P → V := fun j => match m j with | .val v => v | _ => s.input
      { s with
        heard := heard
        perplexed := decide
          (2 * (univ.filter fun j => heard j = s.input).card ≤ Fintype.card P + t) }
    | 1 =>
      let perp : P → Bool := fun j => match m j with | .perplexed b => b | _ => false
      let alert := decide (Fintype.card P - 2 * t ≤ (univ.filter fun j => perp j = true).card)
      let cand := (uniqueAboveOn (univ.filter fun j => perp j = false) (t + 1) s.heard).getD default
      { s with candidate := cand, binState := πBool.init i alert }
    | r' + 2 =>
      let mb : P → MBool := fun j =>
        match m j with | .bin b => b | _ => πBool.send r' i s.binState j
      { s with binState := πBool.update r' i s.binState mb }
  output i s := if πBool.output i s.binState then default else s.candidate

/-- Total number of `V`-carrying (`TurpinCoanMsg.isVal`) point-to-point messages sent by correct
processes (`univ \ F`) across the first `R` rounds of `turpinCoan`. -/
@[expose] def turpinCoanValueMessagesSent (t : ℕ) (default : V) (πBool : Protocol P SBool MBool)
    (F : Finset P) (adv : ℕ → P → P → TurpinCoanMsg V MBool) (x : P → V) (R : ℕ) : ℕ :=
  ∑ r ∈ range R, ∑ i ∈ univ \ F, ∑ j ∈ univ,
    if ((turpinCoan t default πBool).send r i
      ((turpinCoan t default πBool).state F adv x r i) j).isVal then 1 else 0

/-- Across `R + 1` rounds of `turpinCoan`, correct processes transmit `V`-values in round 1 only,
for an exact total of `(Fintype.card P - F.card) * Fintype.card P` value-bearing messages
(independent of `R`, `t`, and the adversary `adv`). -/
theorem turpinCoan_valueMessagesSent_eq (t : ℕ) (default : V) (πBool : Protocol P SBool MBool)
    (F : Finset P) (adv : ℕ → P → P → TurpinCoanMsg V MBool) (x : P → V) (R : ℕ) :
    turpinCoanValueMessagesSent t default πBool F adv x (R + 1) =
      (Fintype.card P - F.card) * Fintype.card P := by
  unfold turpinCoanValueMessagesSent
  rw [Finset.sum_range_succ', Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun _ _ =>
    Finset.sum_eq_zero fun _ _ => by cases k <;> rfl, Nat.zero_add]
  simp only [turpinCoan, TurpinCoanMsg.isVal, ↓reduceIte, Finset.sum_const, Nat.nsmul_eq_mul,
    Nat.mul_one, Finset.card_univ]
  rw [show (univ \ F).card = Fintype.card P - F.card by finset_card]

private theorem turpinCoan_heard_of_notMem (t : ℕ) (default : V) (πBool : Protocol P SBool MBool)
    (F : Finset P) (adv : ℕ → P → P → TurpinCoanMsg V MBool) (x : P → V) (i : P) {j : P}
    (hj : j ∉ F) :
    ((turpinCoan t default πBool).state F adv x 1 i).heard j = x j := by
  simp only [MultivaluedProtocol.state, turpinCoan, hj, ↓reduceIte]

private theorem turpinCoan_perplexed_eq_false_iff {t : ℕ} {default : V}
    {πBool : Protocol P SBool MBool} {F : Finset P} {adv : ℕ → P → P → TurpinCoanMsg V MBool}
    {x : P → V} (i : P) :
    ((turpinCoan t default πBool).state F adv x 1 i).perplexed = false ↔
      Fintype.card P + t <
        2 * (univ.filter fun j =>
          ((turpinCoan t default πBool).state F adv x 1 i).heard j = x i).card := by
  simp only [MultivaluedProtocol.state, turpinCoan, decide_eq_false_iff_not, not_le]

/-- Two correct processes that are both non-perplexed after round 1 must share the same initial
input (`2 * count > n + t` on each leaves room for at most one value outside `F`). -/
private theorem turpinCoan_content_eq {t : ℕ} {default : V} {πBool : Protocol P SBool MBool}
    {F : Finset P} (hF : F.card ≤ t) {adv : ℕ → P → P → TurpinCoanMsg V MBool} {x : P → V}
    {i₀ i₁ : P}
    (hc₀ : ((turpinCoan t default πBool).state F adv x 1 i₀).perplexed = false)
    (hc₁ : ((turpinCoan t default πBool).state F adv x 1 i₁).perplexed = false) :
    x i₀ = x i₁ := by
  rw [turpinCoan_perplexed_eq_false_iff] at hc₀ hc₁
  have hb₀ := card_filter_le_sdiff_add
    (fun _ => turpinCoan_heard_of_notMem t default πBool F adv x i₀) (x i₀)
  have hb₁ := card_filter_le_sdiff_add
    (fun _ => turpinCoan_heard_of_notMem t default πBool F adv x i₁) (x i₁)
  finset_card

/-- Whenever at least `t + 1` correct processes are non-perplexed after round 1, every process `i`
computes their shared initial input as `candidate` at the end of round 2. -/
private theorem turpinCoan_candidate_eq {t : ℕ} {default : V} {πBool : Protocol P SBool MBool}
    {F : Finset P} (hF : F.card ≤ t) {adv : ℕ → P → P → TurpinCoanMsg V MBool} {x : P → V}
    (hC : t + 1 ≤ ((univ \ F).filter fun j =>
      ((turpinCoan t default πBool).state F adv x 1 j).perplexed = false).card)
    {c₀ : P} (_hc₀F : c₀ ∉ F)
    (hc₀ : ((turpinCoan t default πBool).state F adv x 1 c₀).perplexed = false) (i : P) :
    ((turpinCoan t default πBool).state F adv x 2 i).candidate = x c₀ := by
  let s₁ := (turpinCoan t default πBool).state F adv x 1
  let raw : P → TurpinCoanMsg V MBool := fun j =>
    if j ∈ F then adv 1 j i else .perplexed (s₁ j).perplexed
  let perp : P → Bool := fun j => match raw j with | .perplexed b => b | _ => false
  change (uniqueAboveOn (univ.filter fun j => perp j = false) (t + 1) (s₁ i).heard).getD default =
    x c₀
  have hperp : ∀ j ∉ F, perp j = (s₁ j).perplexed := fun j hj => by
    simp only [perp, raw, hj, ↓reduceIte]
  have huniq : uniqueAboveOn (univ.filter fun j => perp j = false) (t + 1) (s₁ i).heard =
      some (x c₀) := by
    rw [uniqueAboveOn_eq_some_iff (by omega)]
    refine ⟨?_, fun w hw => ?_⟩
    · refine hC.trans (Finset.card_le_card fun j hj => ?_)
      obtain ⟨⟨hu, hjF⟩, hj0⟩ := (Finset.mem_filter.1 hj).imp_left Finset.mem_sdiff.1
      exact Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hu, (hperp j hjF).trans hj0⟩,
        (turpinCoan_heard_of_notMem t default πBool F adv x i hjF).trans
          (turpinCoan_content_eq hF hj0 hc₀)⟩
    · by_contra hne
      have hsub : (univ.filter fun j => perp j = false).filter
          (fun j => (s₁ i).heard j = w) ⊆ F := fun j hj => by
        rw [Finset.mem_filter, Finset.mem_filter] at hj
        by_contra hjF
        have hjc : (s₁ j).perplexed = false := (hperp j hjF).symm.trans hj.1.2
        have hval : (s₁ i).heard j = x c₀ :=
          (turpinCoan_heard_of_notMem t default πBool F adv x i hjF).trans
            (turpinCoan_content_eq hF hjc hc₀)
        exact hne (hj.2.symm.trans hval)
      finset_card
  rw [huniq, Option.getD_some]

private def turpinCoanAlert (t : ℕ) (default : V) (πBool : Protocol P SBool MBool)
    (F : Finset P) (adv : ℕ → P → P → TurpinCoanMsg V MBool) (x : P → V) (i : P) : Bool :=
  let s₁ := (turpinCoan t default πBool).state F adv x 1
  let perp : P → Bool := fun j =>
    match (if j ∈ F then adv 1 j i else .perplexed (s₁ j).perplexed) with
    | .perplexed b => b
    | _ => false
  decide (Fintype.card P - 2 * t ≤ (univ.filter fun j => perp j = true).card)

private def turpinCoanAdvBool (t : ℕ) (default : V) (πBool : Protocol P SBool MBool)
    (F : Finset P) (adv : ℕ → P → P → TurpinCoanMsg V MBool) (x : P → V) :
    ℕ → P → P → MBool := fun r j i =>
  match adv (r + 2) j i with
  | .bin b => b
  | _ => πBool.send r i (((turpinCoan t default πBool).state F adv x (r + 2) i).binState) j

private theorem turpinCoan_state_add_two (t : ℕ) (default : V) (πBool : Protocol P SBool MBool)
    (F : Finset P) (adv : ℕ → P → P → TurpinCoanMsg V MBool) (x : P → V) :
    ∀ k i, ((turpinCoan t default πBool).state F adv x (k + 2) i).candidate =
        ((turpinCoan t default πBool).state F adv x 2 i).candidate ∧
      ((turpinCoan t default πBool).state F adv x (k + 2) i).binState =
        πBool.state F (turpinCoanAdvBool t default πBool F adv x)
          (turpinCoanAlert t default πBool F adv x) k i
  | 0, i => ⟨rfl, rfl⟩
  | k + 1, i => by
    have ih := turpinCoan_state_add_two t default πBool F adv x k
    refine ⟨(ih i).1, ?_⟩
    rw [MultivaluedProtocol.state, Protocol.state, ← (ih i).2]
    change πBool.update k i _ _ = πBool.update k i _ _
    congr 1
    funext j
    by_cases hj : j ∈ F
    · simp only [hj, ↓reduceIte, turpinCoanAdvBool]; cases adv (k + 2) j i <;> rfl
    · simp only [hj, ↓reduceIte, ← (ih j).2]; rfl

private theorem turpinCoan_decision_add_two (t : ℕ) (default : V) (πBool : Protocol P SBool MBool)
    (F : Finset P) (adv : ℕ → P → P → TurpinCoanMsg V MBool) (x : P → V) (R₀ : ℕ) (i : P) :
    (turpinCoan t default πBool).decision F adv x (R₀ + 2) i =
      if πBool.decision F (turpinCoanAdvBool t default πBool F adv x)
          (turpinCoanAlert t default πBool F adv x) R₀ i
      then default else ((turpinCoan t default πBool).state F adv x 2 i).candidate := by
  obtain ⟨hc, hb⟩ := turpinCoan_state_add_two t default πBool F adv x R₀ i
  change (if πBool.output i _ then default else _) = _
  rw [hc, hb]
  rfl

/-- Multivalued-to-binary reduction step toward `#7210` (after
[Turpin and Coan, §§2–3, pp. 74–75][TurpinCoan1984]; inventory registration remains open under
`#7210` pending an outside-fleet source check): if `3 * t < Fintype.card P` and
`πBool : Protocol P SBool MBool` solves binary Byzantine agreement against `t` faults in `R₀`
rounds, then `turpinCoan t default πBool` solves multivalued Byzantine agreement over `V` against
`t` faults in `R₀ + 2` rounds. -/
theorem turpinCoan_solvesByzantineAgreement {t R₀ : ℕ} (default : V)
    {πBool : Protocol P SBool MBool} (hn : 3 * t < Fintype.card P)
    (hBool : πBool.SolvesByzantineAgreement t R₀) :
    (turpinCoan t default πBool).SolvesByzantineAgreement t (R₀ + 2) where
  agreement F hF adv x i hi j hj := by
    rw [turpinCoan_decision_add_two, turpinCoan_decision_add_two]
    have hdec := hBool.agreement F hF (turpinCoanAdvBool t default πBool F adv x)
      (turpinCoanAlert t default πBool F adv x) i hi j hj
    rw [← hdec]
    cases hbit : πBool.decision F (turpinCoanAdvBool t default πBool F adv x)
      (turpinCoanAlert t default πBool F adv x) R₀ i with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      -- Not all correct processes had `alert = true`, else `πBool.validity` would force `true`.
      obtain ⟨p₀, -, halert⟩ : ∃ p₀ ∉ F, turpinCoanAlert t default πBool F adv x p₀ = false := by
        by_contra! hall
        exact Bool.false_ne_true (hbit.symm.trans (hBool.validity F hF _ _ true
          (fun p hp => Bool.eq_true_of_ne_false (hall p hp)) i hi))
      simp only [turpinCoanAlert, decide_eq_false_iff_not, not_le] at halert
      -- Every perplexed correct process sent `true` to `p₀`, so `< n - 2 * t` correct processes
      -- are perplexed, leaving `≥ t + 1` non-perplexed correct processes.
      have hperp_lt : ((univ \ F).filter fun q =>
          ((turpinCoan t default πBool).state F adv x 1 q).perplexed = true).card <
          Fintype.card P - 2 * t :=
        lt_of_le_of_lt (card_filter_le_of_eqOn_sdiff (F := F)
          (fun q hq => by simp only [hq, ↓reduceIte]) true) halert
      have hC : t + 1 ≤ ((univ \ F).filter fun q =>
          ((turpinCoan t default πBool).state F adv x 1 q).perplexed = false).card := by
        finset_card
      obtain ⟨c₀, hc₀mem⟩ : ∃ c₀, c₀ ∈ (univ \ F).filter fun q =>
          ((turpinCoan t default πBool).state F adv x 1 q).perplexed = false := by finset_card
      rw [Finset.mem_filter, Finset.mem_sdiff] at hc₀mem
      rw [turpinCoan_candidate_eq hF hC hc₀mem.1.2 hc₀mem.2 i,
        turpinCoan_candidate_eq hF hC hc₀mem.1.2 hc₀mem.2 j]
  validity F hF adv x v hv i hi := by
    rw [turpinCoan_decision_add_two]
    -- Every correct process receives `v` from all `n - |F| ≥ n - t` correct processes in round 1,
    -- so none is perplexed (`2 * (n - t) > n + t` since `3 * t < n`).
    have hcontent : ∀ q ∉ F,
        ((turpinCoan t default πBool).state F adv x 1 q).perplexed = false := by
      intro q hq
      rw [turpinCoan_perplexed_eq_false_iff, hv q hq]
      have hsub : univ \ F ⊆ univ.filter (fun j =>
          ((turpinCoan t default πBool).state F adv x 1 q).heard j = v) := fun j hj => by
        obtain ⟨hu, hjF⟩ := Finset.mem_sdiff.1 hj
        exact Finset.mem_filter.2
          ⟨hu, (turpinCoan_heard_of_notMem t default πBool F adv x q hjF).trans (hv j hjF)⟩
      finset_card
    -- Consequently, every correct process sees `≤ |F| ≤ t < n - 2 * t` perplexed reports and sets
    -- `alert = false`.
    have halert_false : ∀ q ∉ F, turpinCoanAlert t default πBool F adv x q = false := fun q _ => by
      simp only [turpinCoanAlert, decide_eq_false_iff_not, not_le]
      have hsub : (univ.filter fun j =>
          (match (if j ∈ F then adv 1 j q
            else .perplexed ((turpinCoan t default πBool).state F adv x 1 j).perplexed) with
            | .perplexed b => b | _ => false) = true) ⊆ F := fun j hj => by
        by_contra hjF
        simp [hjF, hcontent j hjF] at hj
      finset_card
    simp only [hBool.validity F hF _ _ false halert_false i hi, Bool.false_eq_true, ↓reduceIte]
    have hC : t + 1 ≤ ((univ \ F).filter fun q =>
        ((turpinCoan t default πBool).state F adv x 1 q).perplexed = false).card := by
      rw [Finset.filter_true_of_mem fun q hq => hcontent q (Finset.mem_sdiff.1 hq).2]
      finset_card
    exact (turpinCoan_candidate_eq hF hC hi (hcontent i hi) i).trans (hv i hi)

end TurpinCoan

end Cslib.Distributed.Byzantine
