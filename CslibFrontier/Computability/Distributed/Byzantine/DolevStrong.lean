/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Nodup
import CslibFrontier.Tactic.FinsetCard
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Dolev–Strong authenticated synchronous broadcast

In the unauthenticated synchronous model (`Cslib.Distributed.Byzantine.Protocol`), Byzantine
agreement requires `n > 3t` processes (`NodeBound`). With unforgeable digital signatures, the
`(t + 1)`-round protocol of [Dolev and Strong][DolevStrong1983] (§4, Theorem 3, pp. 662–663) solves
single-sender Byzantine broadcast against up to `t` Byzantine faults for **every** finite process
set `P` and **every** `t`—even when `t ≥ n - 1`—while each correct process sends at most two signed
chains along each outgoing edge across the entire execution.

### Model and protocol-variant choices

* **Provenance-based signature abstraction vs. nested signatures (`AuthProtocol.WellSigned`,
  `AuthProtocol.Unforgeable`):** [Dolev and Strong][DolevStrong1983] (§4, pp. 661–662) represent
  authenticated messages syntactically as nested labels `(((v)p₁)p₂⋯)pᵢ` in which each outer
  signature binds the entire inner label. Here signatures are modeled information-theoretically via
  value-level execution-trace provenance: a faulty process `j ∈ F` may attach any signer list whose
  *correct* members `k ∉ F` each genuinely emitted a signed chain for `c.value` in an earlier step
  `< r`. This gives faulty coalitions strictly more freedom (including reordering or splicing
  signatures on a value already signed by those honest processes) without cryptographic primitives.
* **Dealer-rooted exact-phase-length chains and forwarding outside `c.signers`:** matching
  [Dolev and Strong][DolevStrong1983] (§4, Theorem 3, pp. 662–663), `dolevStrongEligible` requires
  every accepted chain at step `r` (phase `r + 1`) to be rooted at `dealer`
  (`c.signers.getLast? = some dealer`), have exact phase length `c.signers.length = r + 1` with
  `Nodup` signers excluding the receiver, and carry a value not yet in `extracted`; `dolevStrong`
  forwards cosigned chains only to recipients `dst ∉ c.signers`. Every honestly emitted chain
  therefore satisfies `c.signers.length = r + 1 ≤ t + 1` (`dolevStrong_send_chain_props`), and no
  process sends to itself.
* **Built-in two-value relay cap and deterministic sender tie-breaking:** `dolevStrong` directly
  incorporates Theorem 3's two-value cap (`extracted.length ≤ 2`, relaying at most two distinct
  values per process) over an arbitrary `[DecidableEq V]` domain without requiring `[LinearOrder V]`
  or `n ≥ 3`: `[LinearOrder P]` (`Finset.min'`) selects the minimum eligible sender in place of
  Theorem 3's lexicographic message order.
* **Point-to-point chain accounting (`AuthProtocol.correctMessagesSent`):** communication complexity
  counts point-to-point `SignedChain` transmissions sent by correct processes (`≤ 2` per directed
  edge `(j, dst)` with `j ≠ dst`, hence `≤ 2 * (n - F.card) * (n - 1)` total).

## Authenticated synchronous model

A `SignedChain P V` pairs a candidate value `value : V` with a list `signers : List P` of process
identities (ordered outermost-first, with `dealer` at the root `getLast?` in `dolevStrong`). An
`AuthProtocol P V State dealer` gives `dealer` an initial state from its input `input : V`, gives
every other process an input-independent initial state, and in each round `r + 1` delivers lists of
signed chains via the shared faulty-versus-honest selector `AuthProtocol.selectMsg` before updating
local states.

`AuthProtocol.Unforgeable.exists_send_of_mem_signers` combines `WellSigned` and `Unforgeable`: in
any well-signed protocol against an unforgeable adversary, any received chain carrying a correct
process `k`'s signature witnesses that `k` itself emitted a signature for that value at or before
the current round (and strictly before it whenever the sender is not `k`).

## The Dolev–Strong protocol

Each process maintains `DolevStrongState P V`, storing `extracted : List V` (capped at length `≤ 2`)
and `toRelay : List (SignedChain P V)` queued for the next round:

* **Initialization:** `dealer` starts with `extracted = [input]` and
  `toRelay = [⟨input, [dealer]⟩]`; every `i ≠ dealer` starts with `extracted = []` and
  `toRelay = []`.
* **Rounds `1` through `t + 1` (`0 ≤ r ≤ t`):** each process sends `c ∈ toRelay` to every recipient
  `dst ∉ c.signers`. Upon receiving incoming chains, process `i` runs two extraction passes
  (`dolevStrongStepOnce`), accepting new values satisfying `dolevStrongEligible`
  (`c.signers.getLast? = some dealer`, `i ∉ c.signers`, `c.signers.Nodup`,
  `c.signers.length = r + 1`, `c.value ∉ extracted`, `extracted.length < 2`). If `r < t`, each newly
  extracted value is queued in `toRelay` as `⟨c.value, i :: c.signers⟩`. Rounds beyond `t + 1` leave
  states unchanged and send nothing.
* **Decision (`decideExtracted`):** if `extracted = [v]`, output `v`; otherwise (`[]` or two
  conflicting values) output the fallback default `v₀`.

### Correctness and communication complexity

* **Validity (`dealer ∉ F`):** every accepted chain has `getLast? = some dealer`, so unforgeability
  rules out any `w ≠ input`, while `⟨input, [dealer]⟩` reaches every `i ≠ dealer` in round `1`; all
  correct processes end with `extracted = [input]` and decide `input`.
* **Agreement (`F.card ≤ t`):** if a correct process `p` queues a chain `c` in round `r ≤ t`, every
  correct `q` either already lies in `c.signers` (hence already extracted `c.value` by provenance)
  or lies outside `c.signers` and receives `c` directly from `p`, forcing `q` either to extract
  `c.value` or to fill `extracted` to length `2`. If `p` extracts `v` in the final round `t + 1`,
  the accepted chain has `t + 1 > F.card` distinct signers, so some correct signer `k ∉ F` already
  queued a chain for `v` at a round `≤ t`, again forcing `q` to hold `v` or have
  `extracted.length = 2`. Thus `decideExtracted` agrees across all correct processes.
* **Polynomial communication (`dolevStrong_sum_send_length_le_two`,
  `dolevStrong_correctMessagesSent_le`):** each process queues at most `2` chains across the entire
  execution (`dolevStrong_sum_toRelay_length_eq`), never sends to itself, and sends at most `2`
  chains to each other process, giving at most `2 * (n - F.card) * (n - 1)` point-to-point chains in
  total.

## Main definitions

* `Cslib.Distributed.Byzantine.SignedChain`: value paired with a signer list.
* `Cslib.Distributed.Byzantine.AuthProtocol`: synchronous signed-message broadcast protocol.
* `Cslib.Distributed.Byzantine.AuthProtocol.selectMsg`,
  `Cslib.Distributed.Byzantine.AuthProtocol.WellSigned`,
  `Cslib.Distributed.Byzantine.AuthProtocol.Unforgeable`: delivery selector and signature
  discipline.
* `Cslib.Distributed.Byzantine.AuthProtocol.SolvesAuthenticatedBroadcast`: validity, agreement, and
  well-signedness against at most `t` faults after `R` rounds.
* `Cslib.Distributed.Byzantine.AuthProtocol.correctMessagesSent`: total point-to-point signed chains
  emitted by correct processes over `R` rounds.
* `Cslib.Distributed.Byzantine.DolevStrongState`, `Cslib.Distributed.Byzantine.decideExtracted`,
  `Cslib.Distributed.Byzantine.dolevStrongEligible`,
  `Cslib.Distributed.Byzantine.dolevStrongStepOnce`, `Cslib.Distributed.Byzantine.dolevStrongRound`,
  `Cslib.Distributed.Byzantine.dolevStrong`: the `(t + 1)`-round Dolev–Strong broadcast protocol.

## Main results

* `Cslib.Distributed.Byzantine.AuthProtocol.Unforgeable.exists_send_of_mem_signers`: any received
  chain carrying a correct process's signature traces back to an authentic emission by that process.
* `Cslib.Distributed.Byzantine.dolevStrong_send_chain_props`: every chain emitted by `dolevStrong`
  at step `r` is rooted at `dealer`, has `Nodup` signers excluding the recipient, and has exact
  length `r + 1 ≤ t + 1`.
* `Cslib.Distributed.Byzantine.dolevStrong_solvesAuthenticatedBroadcast`: `dolevStrong` solves
  authenticated broadcast against `t` faults in any `R ≥ t + 1` rounds for arbitrary `P`.
* `Cslib.Distributed.Byzantine.dolevStrong_sum_toRelay_length_eq`: across `t + 1` rounds, each
  process queues `((state t i).extracted).length` chains in total.
* `Cslib.Distributed.Byzantine.dolevStrong_sum_send_length_le_two`: every process emits at most `2`
  signed chains per recipient across any number of rounds.
* `Cslib.Distributed.Byzantine.dolevStrong_correctMessagesSent_le`: correct processes emit at most
  `2 * (Fintype.card P - F.card) * (Fintype.card P - 1)` point-to-point signed chains in total.

## References

* [D. Dolev, H. R. Strong, *Authenticated algorithms for Byzantine agreement*][DolevStrong1983]
-/

public section

namespace Cslib.Distributed.Byzantine

/-- A signed broadcast message carrying a root `value` and a list `signers` of processes whose
signatures are attached to it. -/
@[ext]
structure SignedChain (P V : Type*) where
  /-- Broadcast value at the root of the signature chain. -/
  value : V
  /-- Processes whose signatures are attached to this chain (outermost-first in `dolevStrong`). -/
  signers : List P
  deriving @[expose] DecidableEq

/-- A deterministic synchronous signed-message broadcast protocol on `P` over value domain `V` with
distinguished broadcaster `dealer`.

Only `dealer` receives the broadcast input (`initDealer`); all other processes start in
`initOther i`, independent of the input. In round `r + 1` (step `r`), process `j` in state `s` sends
`send r j s i` to `i`, and `i` moves to `update r i s m`, where `m j` is the list of chains received
from `j`. Process `i`'s decision in state `s` is `output i s`. -/
structure AuthProtocol (P V State : Type*) (dealer : P) where
  /-- Initial state of `dealer` given its input value. -/
  initDealer : V → State
  /-- Initial state of a non-dealer process `i`. -/
  initOther : P → State
  /-- `send r j s i`: signed chains sent by `j` in state `s` to `i` in round `r + 1`. -/
  send : ℕ → P → State → P → List (SignedChain P V)
  /-- `update r i s m`: state of `i` after round `r + 1` upon receiving `m j` from each `j`. -/
  update : ℕ → P → State → (P → List (SignedChain P V)) → State
  /-- Decision value read from process `i`'s local state. -/
  output : P → State → V

namespace AuthProtocol

section Model

variable {P V S : Type*} {dealer : P} [DecidableEq P] (π : AuthProtocol P V S dealer)

/-- Faulty-versus-honest message selector at step `r` under global state `σ`: faulty processes in
`F` inject `adv r src i`, while correct processes send `π.send r src (σ src) i`. -/
@[expose] def selectMsg (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V))
    (r : ℕ) (σ : P → S) (src i : P) : List (SignedChain P V) :=
  if src ∈ F then adv r src i else π.send r src (σ src) i

/-- Local state of process `i` after `r` rounds on `dealer` input `input` when processes in `F` are
faulty and send `adv r j i` in round `r + 1`. -/
@[expose] def state (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V)) (input : V) :
    ℕ → P → S
  | 0, i => if i = dealer then π.initDealer input else π.initOther i
  | r + 1, i => π.update r i (state F adv input r i)
      (fun src => π.selectMsg F adv r (state F adv input r) src i)

/-- Chains delivered from `src` to `i` in round `r + 1` (step `r`). -/
@[expose] def receivedAt (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V)) (input : V)
    (r : ℕ) (src i : P) : List (SignedChain P V) :=
  π.selectMsg F adv r (π.state F adv input r) src i

/-- Decision of process `i` after `R` rounds. -/
@[expose] def decision (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V)) (input : V)
    (R : ℕ) (i : P) : V :=
  π.output i (π.state F adv input R i)

/-- Honest signature discipline: whenever `π.send` for process `j` at step `r` emits a chain `c`,
every signer `k ∈ c.signers` with `k ≠ j` appeared on a chain for `c.value` that `j` received in
some earlier step `r' < r`. -/
@[expose] def WellSigned : Prop :=
  ∀ (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (r : ℕ) (j dst : P)
    (c : SignedChain P V), c ∈ π.send r j (π.state F adv input r j) dst →
    ∀ k ∈ c.signers, k ≠ j →
      ∃ r' < r, ∃ src : P, ∃ c₀ ∈ π.receivedAt F adv input r' src j,
        c₀.value = c.value ∧ k ∈ c₀.signers

/-- Adversarial unforgeability: in round `r + 1` (step `r`), a faulty process `j ∈ F` can only
include a correct process `k ∉ F` in `c.signers` if `k` genuinely emitted a chain for `c.value`
carrying `k`'s signature in some earlier step `r' < r`. -/
@[expose] def Unforgeable (F : Finset P) (input : V) (adv : ℕ → P → P → List (SignedChain P V)) :
    Prop :=
  ∀ (r : ℕ), ∀ j ∈ F, ∀ (i : P), ∀ c ∈ adv r j i, ∀ k ∈ c.signers, k ∉ F →
    ∃ r' < r, ∃ dst : P, ∃ c' ∈ π.send r' k (π.state F adv input r' k) dst,
      c'.value = c.value ∧ k ∈ c'.signers

/-- **Signature provenance.** In a well-signed protocol against an unforgeable adversary, whenever
process `i` receives a chain `c` from `src` at step `r` containing a correct signer `k ∉ F`,
process `k` genuinely emitted a chain for `c.value` carrying `k`'s signature either at an earlier
step `r' < r`, or at step `r` itself with `src = k`. -/
theorem Unforgeable.exists_send_of_mem_signers {π : AuthProtocol P V S dealer}
    (hws : π.WellSigned) {F : Finset P} {input : V} {adv : ℕ → P → P → List (SignedChain P V)}
    (hunf : π.Unforgeable F input adv) :
    ∀ (r : ℕ) (src i : P) (c : SignedChain P V),
      c ∈ π.receivedAt F adv input r src i → ∀ k ∈ c.signers, k ∉ F →
        ∃ r', (r' < r ∨ (r' = r ∧ src = k)) ∧
          ∃ dst : P, ∃ c' ∈ π.send r' k (π.state F adv input r' k) dst,
            c'.value = c.value ∧ k ∈ c'.signers := by
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro src i c hrec k hkC hkF
    unfold receivedAt selectMsg at hrec
    by_cases hsrc : src ∈ F
    · simp only [hsrc, ↓reduceIte] at hrec
      obtain ⟨r', hr', dst, c', hc', hval, hk'⟩ := hunf r src hsrc i c hrec k hkC hkF
      exact ⟨r', Or.inl hr', dst, c', hc', hval, hk'⟩
    · simp only [hsrc, ↓reduceIte] at hrec
      by_cases hksrc : k = src
      · subst hksrc
        exact ⟨r, Or.inr ⟨rfl, rfl⟩, i, c, hrec, rfl, hkC⟩
      · obtain ⟨r₁, hr₁, src₁, c₀, hc₀, hval₀, hk₀⟩ := hws F adv input r src i c hrec k hkC hksrc
        obtain ⟨r', hr', dst, c', hc', hval', hk'⟩ := ih r₁ hr₁ src₁ src c₀ hc₀ k hk₀ hkF
        exact ⟨r', Or.inl (by omega), dst, c', hc', hval'.trans hval₀, hk'⟩

/-- `π` solves synchronous authenticated broadcast against up to `t` Byzantine faults in `R`
rounds: `π` is well-signed, all correct processes agree after `R` rounds against any unforgeable
adversary of size at most `t`, and when `dealer` is correct they decide `dealer`'s `input`. -/
structure SolvesAuthenticatedBroadcast (t R : ℕ) : Prop where
  /-- Honest transitions never forge signatures of other processes. -/
  wellSigned : π.WellSigned
  /-- Agreement: all correct processes decide the same value after `R` rounds. -/
  agreement : ∀ F : Finset P, F.card ≤ t →
    ∀ (adv : ℕ → P → P → List (SignedChain P V)) (input : V),
      π.Unforgeable F input adv → ∀ i ∉ F, ∀ j ∉ F,
        π.decision F adv input R i = π.decision F adv input R j
  /-- Validity: if `dealer` is correct, all correct processes decide `input` after `R` rounds. -/
  validity : ∀ F : Finset P, F.card ≤ t → dealer ∉ F →
    ∀ (adv : ℕ → P → P → List (SignedChain P V)) (input : V),
      π.Unforgeable F input adv → ∀ i ∉ F, π.decision F adv input R i = input

/-- Tolerating `t` faults implies tolerating `t' ≤ t` faults. -/
theorem SolvesAuthenticatedBroadcast.mono {π : AuthProtocol P V S dealer} {t t' R : ℕ}
    (h : π.SolvesAuthenticatedBroadcast t R) (ht : t' ≤ t) :
    π.SolvesAuthenticatedBroadcast t' R where
  wellSigned := h.wellSigned
  agreement F hF := h.agreement F (hF.trans ht)
  validity F hF := h.validity F (hF.trans ht)

/-- Total point-to-point signed chains emitted by correct processes (`∉ F`) across all recipients
over the first `R` rounds. -/
@[expose] def correctMessagesSent [Fintype P] (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (R : ℕ) : ℕ :=
  ∑ r ∈ Finset.range R, ∑ j ∈ Finset.univ \ F, ∑ i ∈ Finset.univ,
    (π.send r j (π.state F adv input r j) i).length

end Model

end AuthProtocol

/-! ### The Dolev–Strong protocol -/

/-- Local process state in the Dolev–Strong protocol: at most two extracted candidate values and the
newly cosigned chains queued to forward in the next round. -/
@[ext]
structure DolevStrongState (P V : Type*) where
  /-- Distinct values extracted from valid chains so far (capped at length `≤ 2`). -/
  extracted : List V
  /-- Chains cosigned in the most recent round to be forwarded in the next round. -/
  toRelay : List (SignedChain P V)
  deriving @[expose] DecidableEq

/-- Decision rule for `dolevStrong`: output `v` when `extracted` is the unique singleton `[v]`, and
fall back to `v₀` when zero or at least two values were extracted. -/
@[expose] def decideExtracted {V : Type*} : List V → V → V
  | [v], _ => v
  | _, v₀ => v₀

/-- Step-eligibility predicate for `dolevStrong` ([Dolev and Strong][DolevStrong1983], §4,
Theorem 3, pp. 662–663): at step `r` (phase `r + 1`), process `i` in state `s` accepts an incoming
chain `c` iff `c` is rooted at `dealer` (`c.signers.getLast? = some dealer`), has exact phase length
`c.signers.length = r + 1` with `Nodup` signers excluding `i`, carries a fresh value
`c.value ∉ s.extracted`, and `s.extracted` has not yet reached its two-value cap. -/
abbrev dolevStrongEligible {P V : Type*}
    (dealer i : P) (r : ℕ) (s : DolevStrongState P V) (c : SignedChain P V) : Prop :=
  c.signers.getLast? = some dealer ∧ i ∉ c.signers ∧ c.signers.Nodup ∧
    c.signers.length = r + 1 ∧ c.value ∉ s.extracted ∧ s.extracted.length < 2

/-- Extract at most one new eligible value (from the minimum sender `j` offering one) and prepend
its cosigned chain to `s.toRelay`. Running this twice per round suffices because `s.extracted` is
capped at length `2`. -/
@[expose] def dolevStrongStepOnce {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (dealer i : P) (r : ℕ) (m : P → List (SignedChain P V))
    (s : DolevStrongState P V) : DolevStrongState P V :=
  let elig (c : SignedChain P V) : Bool := decide (dolevStrongEligible dealer i r s c)
  let senders := (Finset.univ : Finset P).filter fun j => (m j).any elig
  if h : senders.Nonempty then
    let j₀ := senders.min' h
    match (m j₀).find? elig with
    | some c => ⟨c.value :: s.extracted, ⟨c.value, i :: c.signers⟩ :: s.toRelay⟩
    | none => s
  else
    s

/-- One round of local state update for `dolevStrong` at step `r ≤ t`. -/
@[expose] def dolevStrongRound {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
    (dealer : P) (t : ℕ) (i : P) (r : ℕ) (s : DolevStrongState P V)
    (m : P → List (SignedChain P V)) : DolevStrongState P V :=
  let step1 := dolevStrongStepOnce dealer i r m ⟨s.extracted, []⟩
  let step2 := dolevStrongStepOnce dealer i r m step1
  ⟨step2.extracted, if r < t then step2.toRelay else []⟩

/-- **The Dolev–Strong `(t + 1)`-round authenticated broadcast protocol**
([Dolev and Strong][DolevStrong1983], §4, Theorem 3, pp. 662–663), with broadcaster `dealer`,
default fallback value `v₀`, and fault bound `t`.

This formalization enforces dealer-rooted exact-phase-length chains (`dolevStrongEligible`:
`c.signers.getLast? = some dealer`, `c.signers.length = r + 1`, `c.signers.Nodup`, `i ∉ c.signers`),
forwards queued chains only to recipients `dst ∉ c.signers` (so every emitted chain has
`c.signers.length = r + 1 ≤ t + 1`), incorporates Theorem 3's two-value relay cap
(`extracted.length ≤ 2`) over arbitrary `[DecidableEq V]` with deterministic sender tie-breaking via
`[LinearOrder P]`, and models signatures via trace provenance (`AuthProtocol.WellSigned` and
`AuthProtocol.Unforgeable`) rather than nested cryptographic primitives. -/
@[expose] def dolevStrong (P V : Type*) [Fintype P] [LinearOrder P] [DecidableEq V]
    (dealer : P) (v₀ : V) (t : ℕ) : AuthProtocol P V (DolevStrongState P V) dealer where
  initDealer v := ⟨[v], [⟨v, [dealer]⟩]⟩
  initOther _ := ⟨[], []⟩
  send r _ s dst := if r ≤ t then s.toRelay.filter (fun c => decide (dst ∉ c.signers)) else []
  update r i s m := if r ≤ t then dolevStrongRound dealer t i r s m else s
  output _ s := decideExtracted s.extracted v₀

section DolevStrongProofs

variable {P V : Type*} [Fintype P] [LinearOrder P] [DecidableEq V]
  (dealer : P) (v₀ : V) (t : ℕ)

/-! ### Step invariants for `dolevStrongStepOnce` and `dolevStrongRound` -/

/-- Characterization of a single extraction pass: either nothing changes (and no sender had an
eligible chain), or one eligible chain `c` from some sender `j₀` is accepted. -/
private theorem stepOnce_spec (i : P) (r : ℕ) (m : P → List (SignedChain P V))
    (s : DolevStrongState P V) :
    (dolevStrongStepOnce dealer i r m s = s ∧
      ∀ j : P, ∀ c ∈ m j, ¬ dolevStrongEligible dealer i r s c) ∨
    ∃ (j₀ : P) (c : SignedChain P V), c ∈ m j₀ ∧
      dolevStrongEligible dealer i r s c ∧
      dolevStrongStepOnce dealer i r m s =
        ⟨c.value :: s.extracted, ⟨c.value, i :: c.signers⟩ :: s.toRelay⟩ := by
  unfold dolevStrongStepOnce
  dsimp only
  set elig : SignedChain P V → Bool := fun c => decide (dolevStrongEligible dealer i r s c)
  split_ifs with h
  · have hj₀ : ((Finset.univ : Finset P).filter fun j => (m j).any elig).min' h ∈
        (Finset.univ : Finset P).filter fun j => (m j).any elig := Finset.min'_mem _ h
    have hj₀_any := (Finset.mem_filter.1 hj₀).2
    obtain ⟨c_wit, hc_wit, helig_wit⟩ := List.any_eq_true.1 hj₀_any
    have hfind_some := List.find?_isSome.2 ⟨c_wit, hc_wit, helig_wit⟩
    obtain ⟨c, hc_eq⟩ := Option.isSome_iff_exists.1 hfind_some
    have helig : elig c = true := List.find?_some hc_eq
    refine Or.inr ⟨_, c, List.mem_of_find?_eq_some hc_eq, of_decide_eq_true helig, ?_⟩
    rw [hc_eq]
  · refine Or.inl ⟨rfl, fun j c hcm hcond => ?_⟩
    apply h
    exact ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j,
      List.any_eq_true.2 ⟨c, hcm, decide_eq_true hcond⟩⟩⟩

/-- Each extraction pass preserves existing extracted values, the two-value length cap, `Nodup`,
and exact `+1` conservation between newly queued relays and newly extracted values. -/
private theorem dolevStrongStepOnce_preserve (i : P) (r : ℕ) (m : P → List (SignedChain P V))
    (s : DolevStrongState P V) (hlen : s.extracted.length ≤ 2) (hnodup : s.extracted.Nodup) :
    (∀ v ∈ s.extracted, v ∈ (dolevStrongStepOnce dealer i r m s).extracted) ∧
      (dolevStrongStepOnce dealer i r m s).extracted.length ≤ 2 ∧
      (dolevStrongStepOnce dealer i r m s).extracted.Nodup ∧
      (dolevStrongStepOnce dealer i r m s).toRelay.length + s.extracted.length =
        s.toRelay.length + (dolevStrongStepOnce dealer i r m s).extracted.length := by
  rcases stepOnce_spec dealer i r m s with ⟨heq, -⟩ | ⟨_, c, _, helig, heq⟩
  · rw [heq]
    exact ⟨fun _ hv => hv, hlen, hnodup, rfl⟩
  · obtain ⟨-, -, -, -, hnotmem, hlt2⟩ := helig
    rw [heq]
    refine ⟨fun v hv => List.mem_cons_of_mem _ hv, ?_, List.nodup_cons.2 ⟨hnotmem, hnodup⟩, ?_⟩ <;>
      · simp only [List.length_cons]; omega

private theorem round_extracted_subset (i : P) (r : ℕ) (s : DolevStrongState P V)
    (m : P → List (SignedChain P V))
    (hlen : s.extracted.length ≤ 2) (hnodup : s.extracted.Nodup) :
    (∀ v ∈ s.extracted, v ∈ (dolevStrongRound dealer t i r s m).extracted) ∧
      (dolevStrongRound dealer t i r s m).extracted.length ≤ 2 ∧
      (dolevStrongRound dealer t i r s m).extracted.Nodup ∧
      (r < t → (dolevStrongRound dealer t i r s m).toRelay.length + s.extracted.length =
        (dolevStrongRound dealer t i r s m).extracted.length) := by
  have h1 := dolevStrongStepOnce_preserve dealer i r m ⟨s.extracted, []⟩ hlen hnodup
  have h2 := dolevStrongStepOnce_preserve dealer i r m
    (dolevStrongStepOnce dealer i r m ⟨s.extracted, []⟩) h1.2.1 h1.2.2.1
  dsimp only [dolevStrongRound]
  refine ⟨fun v hv => h2.1 v (h1.1 v hv), h2.2.1, h2.2.2.1, fun hrt => ?_⟩
  simp only [hrt, ↓reduceIte]
  have e1 := h1.2.2.2
  have e2 := h2.2.2.2
  simp only [List.length_nil, zero_add] at e1
  omega

private theorem mem_stepOnce_toRelay {i : P} {r : ℕ} {m : P → List (SignedChain P V)}
    {s : DolevStrongState P V} {c' : SignedChain P V}
    (hc' : c' ∈ (dolevStrongStepOnce dealer i r m s).toRelay) :
    c' ∈ s.toRelay ∨ (c'.value ∈ (dolevStrongStepOnce dealer i r m s).extracted ∧
      ∃ (src : P) (c₀ : SignedChain P V), c₀ ∈ m src ∧
        c₀.signers.getLast? = some dealer ∧ i ∉ c₀.signers ∧ c₀.signers.Nodup ∧
        c₀.signers.length = r + 1 ∧ c' = ⟨c₀.value, i :: c₀.signers⟩) := by
  rcases stepOnce_spec dealer i r m s with ⟨heq, -⟩ | ⟨src, c₀, hcm, helig, heq⟩
  · rw [heq] at hc'
    exact Or.inl hc'
  · rw [heq] at hc' ⊢
    rcases List.mem_cons.1 hc' with rfl | hrel
    · obtain ⟨hd, hi, hnd, hlen, -, -⟩ := helig
      exact Or.inr ⟨List.mem_cons_self, src, c₀, hcm, hd, hi, hnd, hlen, rfl⟩
    · exact Or.inl hrel

private theorem mem_stepOnce_extracted {i : P} {r : ℕ} {m : P → List (SignedChain P V)}
    {s : DolevStrongState P V} {v : V}
    (hv : v ∈ (dolevStrongStepOnce dealer i r m s).extracted) :
    v ∈ s.extracted ∨ ∃ (src : P) (c₀ : SignedChain P V), c₀ ∈ m src ∧ c₀.value = v ∧
      c₀.signers.getLast? = some dealer ∧ i ∉ c₀.signers ∧ c₀.signers.Nodup ∧
      c₀.signers.length = r + 1 ∧
      ⟨v, i :: c₀.signers⟩ ∈ (dolevStrongStepOnce dealer i r m s).toRelay := by
  rcases stepOnce_spec dealer i r m s with ⟨heq, -⟩ | ⟨src, c₀, hcm, helig, heq⟩
  · rw [heq] at hv
    exact Or.inl hv
  · rw [heq] at hv ⊢
    rcases List.mem_cons.1 hv with rfl | hext
    · obtain ⟨hd, hi, hnd, hlen, -, -⟩ := helig
      exact Or.inr ⟨src, c₀, hcm, rfl, hd, hi, hnd, hlen, List.mem_cons_self⟩
    · exact Or.inl hext

/-- Every chain queued in `toRelay` by `dolevStrongRound` comes from cosigning an incoming eligible
chain, and its value lies in the updated `extracted` list. -/
private theorem mem_round_toRelay {i : P} {r : ℕ} {s : DolevStrongState P V}
    {m : P → List (SignedChain P V)} {c' : SignedChain P V}
    (hc' : c' ∈ (dolevStrongRound dealer t i r s m).toRelay) :
    r < t ∧ c'.value ∈ (dolevStrongRound dealer t i r s m).extracted ∧
      ∃ (src : P) (c₀ : SignedChain P V), c₀ ∈ m src ∧
        c₀.signers.getLast? = some dealer ∧ i ∉ c₀.signers ∧ c₀.signers.Nodup ∧
        c₀.signers.length = r + 1 ∧ c' = ⟨c₀.value, i :: c₀.signers⟩ := by
  dsimp only [dolevStrongRound] at hc' ⊢
  by_cases hrt : r < t
  · simp only [hrt, ↓reduceIte] at hc'
    refine ⟨hrt, ?_⟩
    set s1 := dolevStrongStepOnce dealer i r m ⟨s.extracted, []⟩
    rcases mem_stepOnce_toRelay dealer hc' with hc1 | h2
    · rcases mem_stepOnce_toRelay dealer hc1 with hc0 | ⟨hv1, h1⟩
      · cases hc0
      · have hsub : ∀ v ∈ s1.extracted,
            v ∈ (dolevStrongStepOnce dealer i r m s1).extracted := by
          rcases stepOnce_spec dealer i r m s1 with ⟨heq, -⟩ | ⟨_, _, _, _, heq⟩ <;>
            · rw [heq]; intro v hv; simp [hv]
        exact ⟨hsub _ hv1, h1⟩
    · exact h2
  · simp [hrt] at hc'

/-- Every newly extracted value in `dolevStrongRound` comes from an incoming eligible chain `c₀`,
and when `r < t` a corresponding cosigned chain is queued in `toRelay`. -/
private theorem mem_round_extracted {i : P} {r : ℕ} {s : DolevStrongState P V}
    {m : P → List (SignedChain P V)} {v : V}
    (hv : v ∈ (dolevStrongRound dealer t i r s m).extracted) (hnew : v ∉ s.extracted) :
    ∃ (src : P) (c₀ : SignedChain P V), c₀ ∈ m src ∧ c₀.value = v ∧
      c₀.signers.getLast? = some dealer ∧ i ∉ c₀.signers ∧ c₀.signers.Nodup ∧
      c₀.signers.length = r + 1 ∧
      (r < t → ⟨v, i :: c₀.signers⟩ ∈ (dolevStrongRound dealer t i r s m).toRelay) := by
  dsimp only [dolevStrongRound] at hv ⊢
  set s1 := dolevStrongStepOnce dealer i r m ⟨s.extracted, []⟩
  rcases mem_stepOnce_extracted dealer hv with hv1 | ⟨src, c₀, hcm, rfl, hd, hi, hnd, hlen, hrel2⟩
  · rcases mem_stepOnce_extracted dealer hv1 with hv0 |
      ⟨src, c₀, hcm, rfl, hd, hi, hnd, hlen, hrel1⟩
    · exact absurd hv0 hnew
    · have hsub_rel : ∀ c ∈ s1.toRelay, c ∈ (dolevStrongStepOnce dealer i r m s1).toRelay := by
        rcases stepOnce_spec dealer i r m s1 with ⟨heq, -⟩ | ⟨_, _, _, _, heq⟩ <;>
          · rw [heq]; intro c hc; simp [hc]
      exact ⟨src, c₀, hcm, rfl, hd, hi, hnd, hlen, fun hrt => by simp [hrt, hsub_rel _ hrel1]⟩
  · exact ⟨src, c₀, hcm, rfl, hd, hi, hnd, hlen, fun hrt => by simp [hrt, hrel2]⟩

/-- Reception progress: if some sender `src` delivers a chain `c` with
`c.signers.getLast? = some dealer`, `i ∉ c.signers`, `c.signers.Nodup`, and
`c.signers.length = r + 1`, then after `dolevStrongRound` either `c.value` is in `extracted` or
`extracted` has reached its cap of `2` values. -/
private theorem dolevStrongRound_accept_or_full {i : P} {r : ℕ} {s : DolevStrongState P V}
    {m : P → List (SignedChain P V)} (hlen : s.extracted.length ≤ 2) (hnodup : s.extracted.Nodup)
    {src : P} {c : SignedChain P V} (hc : c ∈ m src) (hd : c.signers.getLast? = some dealer)
    (hi : i ∉ c.signers) (hnd : c.signers.Nodup) (hcard : c.signers.length = r + 1) :
    c.value ∈ (dolevStrongRound dealer t i r s m).extracted ∨
      (dolevStrongRound dealer t i r s m).extracted.length = 2 := by
  -- A pass that ends below the cap without `c.value` found `c` eligible, so it grew by one.
  have grow : ∀ st, c.value ∉ (dolevStrongStepOnce dealer i r m st).extracted →
      (dolevStrongStepOnce dealer i r m st).extracted.length < 2 → c.value ∉ st.extracted ∧
        (dolevStrongStepOnce dealer i r m st).extracted.length = st.extracted.length + 1 := by
    intro st hnot hlt
    rcases stepOnce_spec dealer i r m st with ⟨heq, hnone⟩ | ⟨_, _, _, _, heq⟩
    · rw [heq] at hnot hlt
      exact absurd ⟨hd, hi, hnd, hcard, hnot, hlt⟩ (hnone src c hc)
    · rw [heq] at hnot ⊢
      exact ⟨fun h => hnot (List.mem_cons_of_mem _ h), rfl⟩
  have hle := (round_extracted_subset dealer t i r s m hlen hnodup).2.1
  dsimp only [dolevStrongRound] at hle ⊢
  by_contra hcontra
  rcases not_or.1 hcontra with ⟨hnot2, hne2⟩
  obtain ⟨hnot1, h2⟩ := grow _ hnot2 (by omega)
  obtain ⟨-, h1⟩ := grow _ hnot1 (by omega)
  dsimp only at h1
  omega

/-! ### Global state invariants of `dolevStrong` -/

private theorem dolevStrong_state_zero (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (i : P) :
    (dolevStrong P V dealer v₀ t).state F adv input 0 i =
      if i = dealer then ⟨[input], [⟨input, [dealer]⟩]⟩ else ⟨[], []⟩ :=
  rfl

private theorem dolevStrong_state_succ (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (r : ℕ) (i : P) :
    (dolevStrong P V dealer v₀ t).state F adv input (r + 1) i =
      if r ≤ t then
        dolevStrongRound dealer t i r
          ((dolevStrong P V dealer v₀ t).state F adv input r i)
          (fun src => (dolevStrong P V dealer v₀ t).receivedAt F adv input r src i)
      else
        (dolevStrong P V dealer v₀ t).state F adv input r i :=
  rfl

private theorem dolevStrong_state_succ_of_le (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) {r : ℕ} (hr : r ≤ t) (i : P) :
    (dolevStrong P V dealer v₀ t).state F adv input (r + 1) i =
      dolevStrongRound dealer t i r
        ((dolevStrong P V dealer v₀ t).state F adv input r i)
        (fun src => (dolevStrong P V dealer v₀ t).receivedAt F adv input r src i) := by
  rw [dolevStrong_state_succ]
  simp only [hr, ↓reduceIte]

private theorem dolevStrong_send (r : ℕ) (j : P) (s : DolevStrongState P V) (dst : P) :
    (dolevStrong P V dealer v₀ t).send r j s dst =
      if r ≤ t then s.toRelay.filter (fun c => decide (dst ∉ c.signers)) else [] :=
  rfl

private theorem state_extracted_props (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) :
    ∀ (r : ℕ) (i : P),
      ((dolevStrong P V dealer v₀ t).state F adv input r i).extracted.length ≤ 2 ∧
        ((dolevStrong P V dealer v₀ t).state F adv input r i).extracted.Nodup ∧
        ∀ v ∈ ((dolevStrong P V dealer v₀ t).state F adv input r i).extracted,
          v ∈ ((dolevStrong P V dealer v₀ t).state F adv input (r + 1) i).extracted
  | 0, i => by
    have hinit :
        ((dolevStrong P V dealer v₀ t).state F adv input 0 i).extracted.length ≤ 2 ∧
          ((dolevStrong P V dealer v₀ t).state F adv input 0 i).extracted.Nodup := by
      rw [dolevStrong_state_zero]
      split_ifs <;> simp
    refine ⟨hinit.1, hinit.2, fun v hv => ?_⟩
    rw [dolevStrong_state_succ]
    simp only [Nat.zero_le, ↓reduceIte]
    exact (round_extracted_subset dealer t i 0 _ _ hinit.1 hinit.2).1 v hv
  | r + 1, i => by
    obtain ⟨hlen0, hnd0, -⟩ := state_extracted_props F adv input r i
    have hcur :
        ((dolevStrong P V dealer v₀ t).state F adv input (r + 1) i).extracted.length ≤ 2 ∧
          ((dolevStrong P V dealer v₀ t).state F adv input (r + 1) i).extracted.Nodup := by
      rw [dolevStrong_state_succ]
      split_ifs with hr
      · have h := round_extracted_subset dealer t i r
          ((dolevStrong P V dealer v₀ t).state F adv input r i)
          (fun src => (dolevStrong P V dealer v₀ t).receivedAt F adv input r src i) hlen0 hnd0
        exact ⟨h.2.1, h.2.2.1⟩
      · exact ⟨hlen0, hnd0⟩
    refine ⟨hcur.1, hcur.2, fun v hv => ?_⟩
    rw [dolevStrong_state_succ]
    split_ifs with hr1
    · exact (round_extracted_subset dealer t i (r + 1) _ _ hcur.1 hcur.2).1 v hv
    · exact hv

private theorem extracted_mono (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V))
    (input : V) (i : P) {r₁ r₂ : ℕ} (hle : r₁ ≤ r₂) {v : V}
    (hv : v ∈ ((dolevStrong P V dealer v₀ t).state F adv input r₁ i).extracted) :
    v ∈ ((dolevStrong P V dealer v₀ t).state F adv input r₂ i).extracted := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  clear hle
  induction d with
  | zero => simpa using hv
  | succ d ih =>
    rw [← Nat.add_assoc]
    exact (state_extracted_props dealer v₀ t F adv input (r₁ + d) i).2.2 v ih

private theorem state_freeze_after_succ (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (i : P) {R : ℕ} (hR : t + 1 ≤ R) :
    (dolevStrong P V dealer v₀ t).state F adv input R i =
      (dolevStrong P V dealer v₀ t).state F adv input (t + 1) i := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hR
  clear hR
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [← Nat.add_assoc, dolevStrong_state_succ]
    have hgt : ¬(t + 1 + d ≤ t) := by omega
    simp only [hgt, ↓reduceIte, ih]

private theorem state_dealer_extracted (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) :
    ∀ r : ℕ, ((dolevStrong P V dealer v₀ t).state F adv input r dealer).extracted = [input] ∧
      (0 < r → ((dolevStrong P V dealer v₀ t).state F adv input r dealer).toRelay = [])
  | 0 => ⟨by rw [dolevStrong_state_zero]; simp, fun h => absurd h (Nat.lt_irrefl 0)⟩
  | r + 1 => by
    obtain ⟨hext, hrel⟩ := state_dealer_extracted F adv input r
    have hround : ∀ m, dolevStrongRound dealer t dealer r
        ((dolevStrong P V dealer v₀ t).state F adv input r dealer) m = ⟨[input], []⟩ := by
      intro m
      have hno : ∀ st, dolevStrongStepOnce dealer dealer r m st = st := by
        intro st
        rcases stepOnce_spec dealer dealer r m st with ⟨heq, -⟩ | ⟨_, c, _, helig, _⟩
        · exact heq
        · obtain ⟨hd, hnd, -⟩ := helig
          exact absurd (List.mem_of_getLast? hd) hnd
      simp only [dolevStrongRound, hno, hext, ite_self]
    rw [dolevStrong_state_succ]
    by_cases hr : r ≤ t
    · simp only [hr, ↓reduceIte, hround]
      exact ⟨trivial, fun _ => trivial⟩
    · have hpos : 0 < r := by omega
      simp only [hr, ↓reduceIte]
      exact ⟨hext, fun _ => hrel hpos⟩

/-- Unified invariant on every chain queued in `toRelay` at step `r ≤ t`: `c` is rooted at
`dealer`, includes `j`, has `Nodup` signers of exact length `r + 1`, carries a value already in
`j`'s `extracted` list, and every signer `k ≠ j` appeared on a chain received by `j` at `< r`. -/
private theorem toRelay_props (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V))
    (input : V) {r : ℕ} (hr : r ≤ t) {j : P} {c : SignedChain P V}
    (hc : c ∈ ((dolevStrong P V dealer v₀ t).state F adv input r j).toRelay) :
    c.signers.getLast? = some dealer ∧ j ∈ c.signers ∧ c.signers.Nodup ∧
      c.signers.length = r + 1 ∧
      c.value ∈ ((dolevStrong P V dealer v₀ t).state F adv input r j).extracted ∧
      ∀ k ∈ c.signers, k ≠ j →
        ∃ r' < r, ∃ src : P,
          ∃ c₀ ∈ (dolevStrong P V dealer v₀ t).receivedAt F adv input r' src j,
            c₀.value = c.value ∧ k ∈ c₀.signers := by
  cases r with
  | zero =>
    rw [dolevStrong_state_zero] at hc ⊢
    split_ifs at hc with hjd
    · subst hjd
      obtain rfl := List.mem_singleton.1 hc
      simp
    · simp at hc
  | succ m =>
    have hm : m ≤ t := by omega
    rw [dolevStrong_state_succ] at hc ⊢
    simp only [hm, ↓reduceIte] at hc ⊢
    obtain ⟨_, hv, src, c₀, hc₀, hd, hj0, hnd, hlen, rfl⟩ := mem_round_toRelay dealer t hc
    have hlast : (j :: c₀.signers).getLast? = some dealer := by
      cases hcs : c₀.signers with
      | nil => simp [hcs] at hd
      | cons a rest => rw [List.getLast?_cons_cons, ← hcs, hd]
    refine ⟨hlast, List.mem_cons_self, List.nodup_cons.2 ⟨hj0, hnd⟩, ?_, hv, ?_⟩
    · simp only [List.length_cons, hlen]
    · intro k hk hkne
      rcases List.mem_cons.1 hk with rfl | hk0
      · exact absurd rfl hkne
      · exact ⟨m, Nat.lt_succ_self m, src, c₀, hc₀, rfl, hk0⟩

private theorem mem_toRelay_of_send {F : Finset P} {adv : ℕ → P → P → List (SignedChain P V)}
    {input : V} {r : ℕ} {j dst : P} {c : SignedChain P V}
    (hc : c ∈ (dolevStrong P V dealer v₀ t).send r j
      ((dolevStrong P V dealer v₀ t).state F adv input r j) dst) :
    r ≤ t ∧ c ∈ ((dolevStrong P V dealer v₀ t).state F adv input r j).toRelay ∧
      dst ∉ c.signers := by
  rw [dolevStrong_send] at hc
  split_ifs at hc with hr
  · obtain ⟨hc_rel, hdst⟩ := List.mem_filter.1 hc
    exact ⟨hr, hc_rel, of_decide_eq_true hdst⟩
  · simp at hc

/-- **Emitted chain structure** ([Dolev and Strong][DolevStrong1983], §4, Theorem 3, pp. 662–663):
every chain `c` emitted by `dolevStrong` from `j` to `dst` at step `r` is rooted at `dealer`,
contains `j`, excludes `dst`, has `Nodup` signers, and has exact phase length `r + 1 ≤ t + 1`. -/
theorem dolevStrong_send_chain_props (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V))
    (input : V) {r : ℕ} {j dst : P} {c : SignedChain P V}
    (hc : c ∈ (dolevStrong P V dealer v₀ t).send r j
      ((dolevStrong P V dealer v₀ t).state F adv input r j) dst) :
    c.signers.getLast? = some dealer ∧ j ∈ c.signers ∧ dst ∉ c.signers ∧ c.signers.Nodup ∧
      c.signers.length = r + 1 ∧ c.signers.length ≤ t + 1 := by
  obtain ⟨hr, hc_rel, hdst⟩ := mem_toRelay_of_send dealer v₀ t hc
  obtain ⟨hd, hj, hnd, hlen, -, -⟩ := toRelay_props dealer v₀ t F adv input hr hc_rel
  exact ⟨hd, hj, hdst, hnd, hlen, by omega⟩

private theorem wellSigned_dolevStrong : (dolevStrong P V dealer v₀ t).WellSigned := by
  intro F adv input r j dst c hc k hk hk_ne
  obtain ⟨hr, hc_rel, -⟩ := mem_toRelay_of_send dealer v₀ t hc
  exact (toRelay_props dealer v₀ t F adv input hr hc_rel).2.2.2.2.2 k hk hk_ne

/-- Relay lemma: whenever a correct process `j ∉ F` queues a chain `c` in `toRelay` at step
`r ≤ t`, every correct process `q ∉ F` ends round `t + 1` either having extracted `c.value` or with
`extracted` at its cap of length `2`. -/
private theorem toRelay_reaches_all {F : Finset P} {adv : ℕ → P → P → List (SignedChain P V)}
    {input : V} (hunf : (dolevStrong P V dealer v₀ t).Unforgeable F input adv)
    {r : ℕ} (hr : r ≤ t) {j : P} (hj : j ∉ F) {c : SignedChain P V}
    (hc : c ∈ ((dolevStrong P V dealer v₀ t).state F adv input r j).toRelay)
    {q : P} (hq : q ∉ F) :
    c.value ∈ ((dolevStrong P V dealer v₀ t).state F adv input (t + 1) q).extracted ∨
      ((dolevStrong P V dealer v₀ t).state F adv input (t + 1) q).extracted.length = 2 := by
  obtain ⟨hd, -, hnd, hlen, hv_j, hprev⟩ := toRelay_props dealer v₀ t F adv input hr hc
  by_cases hqc : q ∈ c.signers
  · by_cases hqj : q = j
    · subst hqj
      exact Or.inl (extracted_mono dealer v₀ t F adv input q (by omega) hv_j)
    · obtain ⟨r₁, hr₁, src, c₀, hc₀, hval₀, hq₀⟩ := hprev q hqc hqj
      obtain ⟨r', -, dst', c', hc', hval', -⟩ :=
        hunf.exists_send_of_mem_signers (wellSigned_dolevStrong dealer v₀ t) r₁ src j c₀ hc₀
          q hq₀ hq
      obtain ⟨hr't, hc'_rel, -⟩ := mem_toRelay_of_send dealer v₀ t hc'
      have hv' := (toRelay_props dealer v₀ t F adv input hr't hc'_rel).2.2.2.2.1
      rw [← hval₀, ← hval']
      exact Or.inl (extracted_mono dealer v₀ t F adv input q (by omega) hv')
  · have hcq : c ∈ (dolevStrong P V dealer v₀ t).receivedAt F adv input r j q := by
      simp only [AuthProtocol.receivedAt, AuthProtocol.selectMsg, hj, ↓reduceIte, dolevStrong_send,
        hr, List.mem_filter]
      exact ⟨hc, decide_eq_true hqc⟩
    obtain ⟨hlen_r, hnd_r, -⟩ := state_extracted_props dealer v₀ t F adv input r q
    have hstep := dolevStrongRound_accept_or_full dealer t
      (m := fun src => (dolevStrong P V dealer v₀ t).receivedAt F adv input r src q)
      hlen_r hnd_r (src := j) hcq hd hqc hnd hlen
    rw [← dolevStrong_state_succ_of_le dealer v₀ t F adv input hr q] at hstep
    rcases hstep with hv | hfull
    · exact Or.inl (extracted_mono dealer v₀ t F adv input q (by omega) hv)
    · refine Or.inr (le_antisymm (state_extracted_props dealer v₀ t F adv input (t + 1) q).1 ?_)
      have hle := (state_extracted_props dealer v₀ t F adv input (r + 1) q).2.1.length_le_of_subset
        (fun x hx => extracted_mono dealer v₀ t F adv input q
          (r₁ := r + 1) (r₂ := t + 1) (by omega) hx)
      omega

/-- Any value extracted by a non-dealer process `p` by round `k` entered `extracted` for the first
time at some step `r < k`. -/
private theorem exists_first_extracted (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) {p : P} (hp : p ≠ dealer) :
    ∀ {k : ℕ} {v : V}, v ∈ ((dolevStrong P V dealer v₀ t).state F adv input k p).extracted →
      ∃ r < k, v ∉ ((dolevStrong P V dealer v₀ t).state F adv input r p).extracted ∧
        v ∈ ((dolevStrong P V dealer v₀ t).state F adv input (r + 1) p).extracted
  | 0, _, hv => by
    rw [dolevStrong_state_zero] at hv
    simp [hp] at hv
  | k + 1, v, hv => by
    by_cases hvk : v ∈ ((dolevStrong P V dealer v₀ t).state F adv input k p).extracted
    · obtain ⟨r, hrk, hnot, hin⟩ := exists_first_extracted F adv input hp hvk
      exact ⟨r, by omega, hnot, hin⟩
    · exact ⟨k, Nat.lt_succ_self k, hvk, hv⟩

/-- Mutual propagation: when `F.card ≤ t` and `p ≠ dealer` is correct, any value extracted by `p`
after round `t + 1` either is also extracted by every correct `q` or `q` has `extracted` of length
`2`. -/
private theorem extracted_propagates {F : Finset P} (hF : F.card ≤ t)
    {adv : ℕ → P → P → List (SignedChain P V)} {input : V}
    (hunf : (dolevStrong P V dealer v₀ t).Unforgeable F input adv)
    {p : P} (hpF : p ∉ F) (hpd : p ≠ dealer) {v : V}
    (hv : v ∈ ((dolevStrong P V dealer v₀ t).state F adv input (t + 1) p).extracted)
    {q : P} (hqF : q ∉ F) :
    v ∈ ((dolevStrong P V dealer v₀ t).state F adv input (t + 1) q).extracted ∨
      ((dolevStrong P V dealer v₀ t).state F adv input (t + 1) q).extracted.length = 2 := by
  obtain ⟨r, hrt1, hnot_r, hin_r1⟩ := exists_first_extracted dealer v₀ t F adv input hpd hv
  have hr : r ≤ t := by omega
  rw [dolevStrong_state_succ] at hin_r1
  simp only [hr, ↓reduceIte] at hin_r1
  obtain ⟨src, c₀, hc₀, rfl, hd, hp0, hnd, hlen, hrel⟩ :=
    mem_round_extracted dealer t hin_r1 hnot_r
  by_cases hlt : r < t
  · -- Extracted before the final round: `p` itself cosigns and queues `c₀.value` at `r + 1`.
    have hr1 : r + 1 ≤ t := by omega
    have hc'_rel : ⟨c₀.value, p :: c₀.signers⟩ ∈
        ((dolevStrong P V dealer v₀ t).state F adv input (r + 1) p).toRelay := by
      rw [dolevStrong_state_succ]
      simp only [hr, ↓reduceIte]
      exact hrel hlt
    exact toRelay_reaches_all dealer v₀ t hunf hr1 hpF hc'_rel hqF
  · -- Extracted in the final round `r = t`: `c₀` has `t + 1 > F.card` distinct signers.
    have hrt_eq : r = t := by omega
    subst r
    obtain ⟨k, hk_mem, hkF⟩ : ∃ k ∈ c₀.signers.toFinset, k ∉ F := by
      finset_card [List.toFinset_card_of_nodup hnd]
    obtain ⟨r', -, dst', c', hc', hval, -⟩ :=
      hunf.exists_send_of_mem_signers (wellSigned_dolevStrong dealer v₀ t) t src p c₀ hc₀ k
        (List.mem_toFinset.1 hk_mem) hkF
    obtain ⟨hr't, hc'_rel, -⟩ := mem_toRelay_of_send dealer v₀ t hc'
    rw [← hval]
    exact toRelay_reaches_all dealer v₀ t hunf hr't hkF hc'_rel hqF

omit [Fintype P] [LinearOrder P] [DecidableEq V] in
private theorem not_two_mem_singleton {v a b : V} {rest : List V}
    (hlen : (a :: b :: rest).length ≤ 2) (hnd : (a :: b :: rest).Nodup)
    (h : ∀ x ∈ a :: b :: rest, x ∈ [v] ∨ [v].length = 2) : False := by
  cases rest with
  | cons => simp only [List.length_cons] at hlen; omega
  | nil =>
    have ha := h a (by simp)
    have hb := h b (by simp)
    simp_all

omit [Fintype P] [LinearOrder P] [DecidableEq V] in
/-- **Two-value decision agreement.** If two `Nodup` lists of length at most `2` satisfy mutual
propagation (`x ∈ l₁ → x ∈ l₂ ∨ l₂.length = 2` and symmetrically), then `decideExtracted` yields
the same output on both lists—even if they hold different pairs of values when both have length
`2`. -/
private theorem decideExtracted_eq_of_mutual {l₁ l₂ : List V}
    (hlen₁ : l₁.length ≤ 2) (hlen₂ : l₂.length ≤ 2) (hnd₁ : l₁.Nodup) (hnd₂ : l₂.Nodup)
    (h₁₂ : ∀ x ∈ l₁, x ∈ l₂ ∨ l₂.length = 2) (h₂₁ : ∀ x ∈ l₂, x ∈ l₁ ∨ l₁.length = 2) :
    decideExtracted l₁ v₀ = decideExtracted l₂ v₀ := by
  match l₁, l₂ with
  | [], [] | [], _ :: _ :: _ | _ :: _ :: _, [] | _ :: _ :: _, _ :: _ :: _ => rfl
  | [], [w] =>
    rcases h₂₁ w List.mem_cons_self with hw | hlen
    · cases hw
    · simp at hlen
  | [v], [] =>
    rcases h₁₂ v List.mem_cons_self with hv | hlen
    · cases hv
    · simp at hlen
  | [v], [w] =>
    rcases h₁₂ v List.mem_cons_self with hv | hlen
    · simp only [List.mem_singleton] at hv
      subst hv
      rfl
    · simp at hlen
  | [v], w₁ :: w₂ :: rest => exact False.elim (not_two_mem_singleton hlen₂ hnd₂ h₂₁)
  | v₁ :: v₂ :: rest, [w] => exact False.elim (not_two_mem_singleton hlen₁ hnd₁ h₁₂)

private theorem validity_dolevStrong_at_succ {F : Finset P} (hd : dealer ∉ F)
    {adv : ℕ → P → P → List (SignedChain P V)} {input : V}
    (hunf : (dolevStrong P V dealer v₀ t).Unforgeable F input adv) {i : P} (hi : i ∉ F) :
    (dolevStrong P V dealer v₀ t).decision F adv input (t + 1) i = input := by
  -- Every value extracted by `i` equals `input`, because every accepted chain is rooted at
  -- `dealer`.
  have hall_input :
      ∀ v ∈ ((dolevStrong P V dealer v₀ t).state F adv input (t + 1) i).extracted,
        v = input := by
    intro v hv
    by_cases hid : i = dealer
    · subst i
      rwa [(state_dealer_extracted dealer v₀ t F adv input (t + 1)).1, List.mem_singleton] at hv
    obtain ⟨r, hrt1, hnot_r, hin_r1⟩ := exists_first_extracted dealer v₀ t F adv input hid hv
    have hr : r ≤ t := by omega
    rw [dolevStrong_state_succ] at hin_r1
    simp only [hr, ↓reduceIte] at hin_r1
    obtain ⟨src, c₀, hc₀, rfl, hd_last, -, -, -, -⟩ :=
      mem_round_extracted dealer t hin_r1 hnot_r
    obtain ⟨r', -, dst', c', hc', hval, -⟩ :=
      hunf.exists_send_of_mem_signers (wellSigned_dolevStrong dealer v₀ t) r src i c₀ hc₀
        dealer (List.mem_of_getLast? hd_last) hd
    obtain ⟨hr't, hc'_rel, -⟩ := mem_toRelay_of_send dealer v₀ t hc'
    have hv' := (toRelay_props dealer v₀ t F adv input hr't hc'_rel).2.2.2.2.1
    rw [(state_dealer_extracted dealer v₀ t F adv input r').1, List.mem_singleton] at hv'
    exact hval.symm.trans hv'
  -- And `dealer` queues `⟨input, [dealer]⟩` in round `1` (`r = 0`), so `i` extracts `input`.
  have hrel0 : ⟨input, [dealer]⟩ ∈
      ((dolevStrong P V dealer v₀ t).state F adv input 0 dealer).toRelay := by
    rw [dolevStrong_state_zero]
    simp
  have hreach := toRelay_reaches_all dealer v₀ t hunf (Nat.zero_le t) hd hrel0 hi
  obtain ⟨hlen, hnd, -⟩ := state_extracted_props dealer v₀ t F adv input (t + 1) i
  exact decideExtracted_eq_of_mutual (l₂ := [input]) v₀ hlen (by simp) hnd
    (List.nodup_singleton _) (fun v hv => Or.inl (List.mem_singleton.2 (hall_input v hv)))
    (by simpa using hreach)

/-- **Dolev–Strong authenticated synchronous broadcast** ([Dolev and Strong][DolevStrong1983],
§4, Theorem 3, pp. 662–663): `dolevStrong P V dealer v₀ t` solves synchronous authenticated
broadcast against up to `t` Byzantine faults in any `R ≥ t + 1` rounds, for arbitrary finite `P`
without any `n > 3t` bound. -/
theorem dolevStrong_solvesAuthenticatedBroadcast {R : ℕ} (hR : t + 1 ≤ R) :
    (dolevStrong P V dealer v₀ t).SolvesAuthenticatedBroadcast t R where
  wellSigned := wellSigned_dolevStrong dealer v₀ t
  agreement F hF adv input hunf i hi j hj := by
    have hdec : ∀ q, (dolevStrong P V dealer v₀ t).decision F adv input R q =
        (dolevStrong P V dealer v₀ t).decision F adv input (t + 1) q := fun q => by
      simp only [AuthProtocol.decision, state_freeze_after_succ dealer v₀ t F adv input q hR]
    rw [hdec i, hdec j]
    by_cases hd : dealer ∈ F
    · have hid : i ≠ dealer := fun heq => hi (heq ▸ hd)
      have hjd : j ≠ dealer := fun heq => hj (heq ▸ hd)
      obtain ⟨hlen_i, hnd_i, -⟩ := state_extracted_props dealer v₀ t F adv input (t + 1) i
      obtain ⟨hlen_j, hnd_j, -⟩ := state_extracted_props dealer v₀ t F adv input (t + 1) j
      exact decideExtracted_eq_of_mutual v₀ hlen_i hlen_j hnd_i hnd_j
        (fun v hv => extracted_propagates dealer v₀ t hF hunf hi hid hv hj)
        (fun v hv => extracted_propagates dealer v₀ t hF hunf hj hjd hv hi)
    · rw [validity_dolevStrong_at_succ dealer v₀ t hd hunf hi,
        validity_dolevStrong_at_succ dealer v₀ t hd hunf hj]
  validity F _ hd adv input hunf i hi := by
    simp only [AuthProtocol.decision, state_freeze_after_succ dealer v₀ t F adv input i hR]
    exact validity_dolevStrong_at_succ dealer v₀ t hd hunf hi

/-! ### Polynomial communication complexity -/

private theorem sum_toRelay_length_prefix (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (i : P) :
    ∀ m ≤ t,
      ∑ r ∈ Finset.range (m + 1),
        ((dolevStrong P V dealer v₀ t).state F adv input r i).toRelay.length =
        ((dolevStrong P V dealer v₀ t).state F adv input m i).extracted.length
  | 0, _ => by
    rw [Finset.sum_range_one, dolevStrong_state_zero]
    split_ifs <;> rfl
  | m + 1, hm1 => by
    have hm_lt : m < t := by omega
    have hm_le : m ≤ t := by omega
    rw [Finset.sum_range_succ, sum_toRelay_length_prefix F adv input i m hm_le]
    obtain ⟨hlen_m, hnd_m, -⟩ := state_extracted_props dealer v₀ t F adv input m i
    have htele := (round_extracted_subset dealer t i m
      ((dolevStrong P V dealer v₀ t).state F adv input m i)
      (fun src => (dolevStrong P V dealer v₀ t).receivedAt F adv input m src i)
      hlen_m hnd_m).2.2.2 hm_lt
    rw [dolevStrong_state_succ_of_le dealer v₀ t F adv input hm_le i]
    omega

/-- **Exact relay-queue identity:** across all `t + 1` protocol rounds, each process `i` queues
exactly `((state t i).extracted).length` signed chains in `toRelay`. -/
theorem dolevStrong_sum_toRelay_length_eq (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (i : P) :
    ∑ r ∈ Finset.range (t + 1),
      ((dolevStrong P V dealer v₀ t).state F adv input r i).toRelay.length =
      ((dolevStrong P V dealer v₀ t).state F adv input t i).extracted.length :=
  sum_toRelay_length_prefix dealer v₀ t F adv input i t le_rfl

private theorem send_self_eq_nil (F : Finset P) (adv : ℕ → P → P → List (SignedChain P V))
    (input : V) (r : ℕ) (i : P) :
    (dolevStrong P V dealer v₀ t).send r i
      ((dolevStrong P V dealer v₀ t).state F adv input r i) i = [] := by
  rw [dolevStrong_send]
  split_ifs with hr
  · rw [List.filter_eq_nil_iff]
    intro c hc
    have hi := (toRelay_props dealer v₀ t F adv input hr hc).2.1
    simp [hi]
  · rfl

/-- **Per-edge relay bound** ([Dolev and Strong][DolevStrong1983], §4, Theorem 3, p. 663): across
any number of rounds `R`, each process `i` sends at most `2` signed chains to each recipient
`dst`. -/
theorem dolevStrong_sum_send_length_le_two (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (R : ℕ) (i dst : P) :
    ∑ r ∈ Finset.range R,
      ((dolevStrong P V dealer v₀ t).send r i
        ((dolevStrong P V dealer v₀ t).state F adv input r i) dst).length ≤ 2 := by
  -- Rounds after `t` send nothing; earlier ones send a filter of `toRelay`.
  calc _ ≤ ∑ r ∈ Finset.range (t + 1),
        ((dolevStrong P V dealer v₀ t).send r i
          ((dolevStrong P V dealer v₀ t).state F adv input r i) dst).length :=
        Finset.sum_le_sum_of_ne_zero fun r _ hne => Finset.mem_range.2 <| by
          by_contra h
          simp [dolevStrong_send, show ¬r ≤ t by omega] at hne
    _ ≤ ∑ r ∈ Finset.range (t + 1),
        ((dolevStrong P V dealer v₀ t).state F adv input r i).toRelay.length :=
        Finset.sum_le_sum fun r hr => by
          simp only [dolevStrong_send, Nat.lt_succ_iff.1 (Finset.mem_range.1 hr), ↓reduceIte]
          exact List.length_filter_le _ _
    _ ≤ 2 := (sum_toRelay_length_prefix dealer v₀ t F adv input i t le_rfl).trans_le
        (state_extracted_props dealer v₀ t F adv input t i).1

/-- **Polynomial communication complexity** ([Dolev and Strong][DolevStrong1983], §4, Theorem 3,
pp. 662–663): across any `R` rounds, all correct processes together emit at most
`2 * (Fintype.card P - F.card) * (Fintype.card P - 1)` point-to-point signed chains—at most two per
directed edge leaving a correct process. -/
theorem dolevStrong_correctMessagesSent_le (F : Finset P)
    (adv : ℕ → P → P → List (SignedChain P V)) (input : V) (R : ℕ) :
    (dolevStrong P V dealer v₀ t).correctMessagesSent F adv input R ≤
      2 * (Fintype.card P - F.card) * (Fintype.card P - 1) := by
  unfold AuthProtocol.correctMessagesSent
  rw [Finset.sum_comm]
  -- Each correct `j` sends nothing to itself and at most `2` chains to each other process.
  refine (Finset.sum_le_card_nsmul _ _ (2 * (Fintype.card P - 1)) fun j _ => ?_).trans_eq ?_
  · rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    simp only [send_self_eq_nil, List.length_nil, Finset.sum_const_zero, zero_add]
    refine (Finset.sum_le_card_nsmul _ _ 2 fun i _ =>
      dolevStrong_sum_send_length_le_two dealer v₀ t F adv input R j i).trans_eq ?_
    rw [Nat.nsmul_eq_mul, mul_comm]; finset_card
  · rw [Nat.nsmul_eq_mul, show (Finset.univ \ F).card = Fintype.card P - F.card by finset_card,
      ← Nat.mul_assoc, Nat.mul_comm _ 2]

end DolevStrongProofs

end Cslib.Distributed.Byzantine
