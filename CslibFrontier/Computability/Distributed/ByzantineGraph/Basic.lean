/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.Byzantine.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Computability.Distributed.Byzantine.NodeBound

/-!
# Synchronous Boolean consensus on general communication graphs

Deterministic synchronous message passing over an undirected communication graph
`G : SimpleGraph P` in the presence of static Byzantine faults, for the Boolean consensus problem
of [Pease, Shostak and Lamport][PeaseShostakLamport1980] and
[Fischer, Lynch and Merritt][FischerLynchMerritt1985] (§3, p. 61: every process holds a Boolean
input, all correct processes agree, and unanimous correct inputs force that decision; this differs
from the single-sender broadcast problem `Agreement B` of [Dolev][Dolev1982], §1, pp. 15–16).

In `GraphProtocol G State Msg`, processes communicate only along edges of `G`: in round `r + 1`,
process `i` sends `send r i s j hij` to each adjacent process `j` (`hij : G.Adj i j`) and updates
its local state via `update r i s m`, where `m j hji` is the message received along edge
`hji : G.Adj j i`. A process needs no self-loop on `G` because `update` already receives its own
current state `s`. When the processes in `F : Finset P` are faulty, a faulty neighbour `j ∈ F`
injects `adv r j i hji` along each incident edge `hji : G.Adj j i`. Because `adv` is indexed only
by actual edges of `G`, `SolvesByzantineAgreement` has no vacuity on sparse or edgeless graphs even
when `Msg` is empty. As in `Cslib.Distributed.Byzantine.Protocol`, termination is at a fixed
uniform round `R`: protocols whose decision round varies with the execution are not modelled
directly (for finite `P` and `Msg`, König's lemma yields a uniform round bound).

Three simulation and covering tools connect `GraphProtocol` to the complete-graph theory of
`CslibFrontier.Computability.Distributed.Byzantine.Basic` and
`CslibFrontier.Computability.Distributed.Byzantine.NodeBound`:

* **Supergraph simulation (`GraphProtocol.toSupergraph`):** when `G ≤ H`, any protocol on `G`
  runs on `H` with `Option Msg` payloads by sending `none` along edges of `H` absent from `G` and
  replacing spurious `none` payloads from faulty `G`-neighbours by a locally computed default.
  This preserves `SolvesByzantineAgreement` in both directions.
* **Complete-graph equivalence (`GraphProtocol.toProtocol`, `GraphProtocol.ofProtocol`):** on
  `G = ⊤`, graph protocols and `Cslib.Distributed.Byzantine.Protocol` have equivalent round
  complexity `R` and fault tolerance `t`. Composing `toSupergraph le_top` with `toProtocol`
  transfers the `2 ≤ n ≤ 3t` impossibility bound (`GraphProtocol.not_solvesByzantineAgreement`) to
  every graph `G : SimpleGraph P`.
* **Graph covering networks (`GraphProtocol.coverState`, `GraphProtocol.state_eq_coverState`):**
  a Byzantine execution agrees on all correct processes with a covering network whenever the
  embedding preserves mutual `G`-edges between correct processes and faulty neighbours replay the
  covering network's messages.

## Main definitions

* `Cslib.Distributed.ByzantineGraph.GraphProtocol`: synchronous deterministic protocols on
  `G : SimpleGraph P`.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.state`, `GraphProtocol.decision`: executions with
  Byzantine faults along edges of `G`.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.adaptiveState`: executions against a rushing
  adversary.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.SolvesByzantineAgreement`: agreement and validity
  against at most `t` Byzantine faults after `R` rounds.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.ownInput`: decide the own input without
  communication.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.toSupergraph`: simulate a `G`-protocol on a
  supergraph `H` (`G ≤ H`).
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.toProtocol`,
  `Cslib.Distributed.ByzantineGraph.GraphProtocol.ofProtocol`: translations between
  `GraphProtocol ⊤` and `Cslib.Distributed.Byzantine.Protocol`.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.coverState`: executions on covering networks.

## Main results

* `Cslib.Distributed.ByzantineGraph.GraphProtocol.adaptiveState_eq_state`,
  `Cslib.Distributed.ByzantineGraph.GraphProtocol.SolvesByzantineAgreement.adaptive`: rushing
  adversaries are no stronger than fixed edge-message tables.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.solvesByzantineAgreement_ownInput`: at most one
  process solves Byzantine agreement on any graph against any number of faults.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.solvesByzantineAgreement_toSupergraph_iff`:
  supergraph simulation preserves Byzantine agreement in both directions.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.solvesByzantineAgreement_toProtocol_iff`,
  `Cslib.Distributed.ByzantineGraph.GraphProtocol.solvesByzantineAgreement_ofProtocol_iff`,
  `Cslib.Distributed.ByzantineGraph.exists_solvesByzantineAgreement_top_iff`: equivalence with
  complete-graph `Cslib.Distributed.Byzantine.Protocol` on `G = ⊤`.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.not_solvesByzantineAgreement`: no protocol on any
  graph `G` over `n` processes solves Byzantine agreement against `t` faults when `2 ≤ n ≤ 3t`.
* `Cslib.Distributed.ByzantineGraph.GraphProtocol.state_eq_coverState`: the graph covering lemma.

## References

* [D. Dolev, *The Byzantine generals strike again*][Dolev1982]
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
* [M. Pease, R. Shostak, L. Lamport, *Reaching agreement in the presence of
  faults*][PeaseShostakLamport1980]
-/

public section

namespace Cslib.Distributed.ByzantineGraph

/-- A deterministic synchronous message-passing protocol on the communication graph
`G : SimpleGraph P`.

Process `i` with input bit `b` starts in state `init i b`. In round `r + 1` it sends
`send r i s j hij` to each neighbour `j` (`hij : G.Adj i j`) and moves to `update r i s m`, where
`s` is its current state and `m j hji` is the message received along edge `hji : G.Adj j i`. Its
decision in state `s` is `output i s`. -/
structure GraphProtocol {P : Type*} (G : SimpleGraph P) (State Msg : Type*) where
  /-- The initial state of a process with a given input bit. -/
  init : P → Bool → State
  /-- `send r i s j hij`: the message process `i` in state `s` sends to neighbour `j` in round
  `r + 1`. -/
  send : ℕ → ∀ i : P, State → ∀ j : P, G.Adj i j → Msg
  /-- `update r i s m`: the state of `i` after round `r + 1`, where `m j hji` came from neighbour
  `j`. -/
  update : ℕ → ∀ i : P, State → (∀ j : P, G.Adj j i → Msg) → State
  /-- The decision of a process in a given state. -/
  output : P → State → Bool

namespace GraphProtocol

variable {P S M : Type*} [DecidableEq P] {G : SimpleGraph P} (π : GraphProtocol G S M)

/-- The state of process `i` after `r` rounds on inputs `x` when the processes in `F` are faulty
and a faulty neighbour `j ∈ F` sends `adv r j i hji` along edge `hji : G.Adj j i` in round
`r + 1`. -/
@[expose] def state (F : Finset P) (adv : ℕ → ∀ j i : P, G.Adj j i → M) (x : P → Bool) :
    ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (state F adv x r i)
      (fun j hji => if j ∈ F then adv r j i hji else π.send r j (state F adv x r j) i hji)

/-- The decision of process `i` after `R` rounds. -/
@[expose] def decision (F : Finset P) (adv : ℕ → ∀ j i : P, G.Adj j i → M) (x : P → Bool)
    (R : ℕ) (i : P) : Bool :=
  π.output i (π.state F adv x R i)

/-- `π` solves synchronous Boolean Byzantine agreement on `G` against at most `t` faults in `R`
rounds: whenever at most `t` processes are faulty, whatever messages they send along incident edges
of `G`, the correct processes agree after `R` rounds and decide `v` when all correct processes have
input `v` ([Fischer, Lynch and Merritt][FischerLynchMerritt1985], §3, p. 61). -/
structure SolvesByzantineAgreement (t R : ℕ) : Prop where
  /-- Agreement: all correct processes decide the same value. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → ∀ j i : P, G.Adj j i → M) (x : P → Bool),
    ∀ i ∉ F, ∀ j ∉ F, π.decision F adv x R i = π.decision F adv x R j
  /-- Validity: if all correct processes have input `v`, they decide `v`. -/
  validity : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → ∀ j i : P, G.Adj j i → M) (x : P → Bool)
    (v : Bool), (∀ i ∉ F, x i = v) → ∀ i ∉ F, π.decision F adv x R i = v

/-- Tolerating `t` faults implies tolerating at most `t' ≤ t` faults. -/
theorem SolvesByzantineAgreement.mono {π : GraphProtocol G S M} {t t' R : ℕ}
    (h : π.SolvesByzantineAgreement t R) (ht : t' ≤ t) : π.SolvesByzantineAgreement t' R where
  agreement F hF := h.agreement F (hF.trans ht)
  validity F hF := h.validity F (hF.trans ht)

/-- The state of process `i` after `r` rounds against a *rushing* adversary: in round `r + 1` a
faulty neighbour `j` chooses `strat r σ j i hji` as a function of the global state `σ` after `r`
rounds. -/
@[expose] def adaptiveState (F : Finset P)
    (strat : ℕ → (P → S) → ∀ j i : P, G.Adj j i → M) (x : P → Bool) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (adaptiveState F strat x r i)
      (fun j hji => if j ∈ F then strat r (adaptiveState F strat x r) j i hji
        else π.send r j (adaptiveState F strat x r j) i hji)

/-- A rushing adversary is no stronger than a fixed edge-message table: the execution against
`strat` coincides with the execution against the table of messages `strat` sends along that run. -/
theorem adaptiveState_eq_state (F : Finset P)
    (strat : ℕ → (P → S) → ∀ j i : P, G.Adj j i → M) (x : P → Bool) :
    ∀ r, π.adaptiveState F strat x r =
      π.state F (fun r j i hji => strat r (π.adaptiveState F strat x r) j i hji) x r
  | 0 => rfl
  | r + 1 => by
    funext i
    simp only [adaptiveState, state]
    rw [← adaptiveState_eq_state F strat x r]

/-- Agreement and validity hold against rushing adversaries as well. -/
theorem SolvesByzantineAgreement.adaptive {π : GraphProtocol G S M} {t R : ℕ}
    (h : π.SolvesByzantineAgreement t R) {F : Finset P} (hF : F.card ≤ t)
    (strat : ℕ → (P → S) → ∀ j i : P, G.Adj j i → M) (x : P → Bool) :
    (∀ i ∉ F, ∀ j ∉ F, π.output i (π.adaptiveState F strat x R i) =
      π.output j (π.adaptiveState F strat x R j)) ∧
    ∀ v, (∀ i ∉ F, x i = v) → ∀ i ∉ F, π.output i (π.adaptiveState F strat x R i) = v := by
  rw [π.adaptiveState_eq_state F strat x R]
  exact ⟨h.agreement F hF _ x, h.validity F hF _ x⟩

/-- The protocol on `G` in which every process decides its own input without communicating. -/
@[expose] def ownInput (G : SimpleGraph P) : GraphProtocol G Bool Unit where
  init _ b := b
  send _ _ _ _ _ := ()
  update _ _ s _ := s
  output _ s := s

omit [DecidableEq P] in
/-- On at most one process, deciding the own input solves Byzantine agreement on any graph `G`
against any number of faults and for any decision round `R`. -/
theorem solvesByzantineAgreement_ownInput [DecidableEq P] [Subsingleton P] (G : SimpleGraph P)
    (t R : ℕ) : (ownInput G).SolvesByzantineAgreement t R := by
  have hstate (F adv x r i) : (ownInput G).state F adv x r i = x i := by
    induction r <;> [rfl; assumption]
  exact ⟨fun _ _ _ _ i _ j _ => by rw [Subsingleton.elim i j],
    fun F _ adv x v hv i hi => (hstate F adv x R i).trans (hv i hi)⟩

/-! ### Supergraph simulation and complete-graph equivalence -/

/-- Simulate a protocol on `G` over any supergraph `H` (`G ≤ H`) using `Option M` messages:
processes send `some` along edges of `G` and `none` along edges in `H \ G`, and replace a spurious
`none` received from a faulty `G`-neighbour `j` (`hji : G.Adj j i`) by the locally well-typed
fallback `π.send r i s j hji.symm`. -/
@[expose] def toSupergraph [DecidableRel G.Adj] {H : SimpleGraph P} (hle : G ≤ H)
    (π : GraphProtocol G S M) : GraphProtocol H S (Option M) where
  init := π.init
  send r i s j _ := if hij : G.Adj i j then some (π.send r i s j hij) else none
  update r i s m :=
    π.update r i s fun j hji => (m j (hle hji)).getD (π.send r i s j hji.symm)
  output := π.output

private theorem toSupergraph_state_eq_state [DecidableRel G.Adj] {H : SimpleGraph P}
    (hle : G ≤ H) (F : Finset P) (advH : ℕ → ∀ j i : P, H.Adj j i → Option M) (x : P → Bool) :
    ∀ r, (π.toSupergraph hle).state F advH x r =
      π.state F (fun r j i hji =>
        (advH r j i (hle hji)).getD
          (π.send r i ((π.toSupergraph hle).state F advH x r i) j hji.symm)) x r
  | 0 => rfl
  | r + 1 => by
    have ih := toSupergraph_state_eq_state hle F advH x r
    funext i; dsimp only [state]
    refine congrArg₂ (π.update r i) (congrFun ih i) (funext fun j => funext fun hji => ?_)
    by_cases hj : j ∈ F
    · simp only [hj, ↓reduceIte]
    · simp only [hj, ↓reduceIte, congrFun ih j]
      dsimp only [toSupergraph]
      simp [dite_eq_left_of_eq_true (eq_true hji)]

private theorem state_eq_toSupergraph_state [DecidableRel G.Adj] {H : SimpleGraph P}
    (hle : G ≤ H) (F : Finset P) (advG : ℕ → ∀ j i : P, G.Adj j i → M) (x : P → Bool) :
    ∀ r, π.state F advG x r =
      (π.toSupergraph hle).state F
        (fun r j i _ => if hji : G.Adj j i then some (advG r j i hji) else none) x r
  | 0 => rfl
  | r + 1 => by
    have ih := state_eq_toSupergraph_state hle F advG x r
    funext i; dsimp only [state]
    refine congrArg₂ (π.update r i) (congrFun ih i) (funext fun j => funext fun hji => ?_)
    by_cases hj : j ∈ F
    · simp [hj, dite_eq_left_of_eq_true (eq_true hji)]
    · simp only [hj, ↓reduceIte, congrFun ih j]
      dsimp only [toSupergraph]
      simp [dite_eq_left_of_eq_true (eq_true hji)]

/-- Supergraph simulation preserves `SolvesByzantineAgreement` in both directions. -/
theorem solvesByzantineAgreement_toSupergraph_iff [DecidableRel G.Adj] {H : SimpleGraph P}
    (hle : G ≤ H) (t R : ℕ) :
    (π.toSupergraph hle).SolvesByzantineAgreement t R ↔ π.SolvesByzantineAgreement t R :=
  ⟨fun h =>
    ⟨fun F hF advG x i hi j hj => by
      simp only [decision, π.state_eq_toSupergraph_state hle F advG x R]
      exact h.agreement F hF _ x i hi j hj,
     fun F hF advG x v hv i hi => by
      simp only [decision, π.state_eq_toSupergraph_state hle F advG x R]
      exact h.validity F hF _ x v hv i hi⟩,
   fun h =>
    ⟨fun F hF advH x i hi j hj => by
      simp only [decision, π.toSupergraph_state_eq_state hle F advH x R]
      exact h.agreement F hF _ x i hi j hj,
     fun F hF advH x v hv i hi => by
      simp only [decision, π.toSupergraph_state_eq_state hle F advH x R]
      exact h.validity F hF _ x v hv i hi⟩⟩

/-- View a `GraphProtocol` on the complete simple graph `⊤` as a complete-network
`Cslib.Distributed.Byzantine.Protocol` with `Option M` payloads (`none` on self-loops). -/
@[expose] def toProtocol (π : GraphProtocol (⊤ : SimpleGraph P) S M) :
    Byzantine.Protocol P S (Option M) where
  init := π.init
  send r i s j := if hij : i ≠ j then some (π.send r i s j hij) else none
  update r i s m := π.update r i s fun j hji => (m j).getD (π.send r i s j hji.symm)
  output := π.output

private theorem toProtocol_state_eq_state (π : GraphProtocol (⊤ : SimpleGraph P) S M)
    (F : Finset P) (adv : ℕ → P → P → Option M) (x : P → Bool) :
    ∀ r, π.toProtocol.state F adv x r =
      π.state F (fun r j i hji =>
        (adv r j i).getD (π.send r i (π.toProtocol.state F adv x r i) j hji.symm)) x r
  | 0 => rfl
  | r + 1 => by
    have ih := toProtocol_state_eq_state π F adv x r
    funext i; dsimp only [Byzantine.Protocol.state, state]
    refine congrArg₂ (π.update r i) (congrFun ih i) (funext fun j => funext fun hji => ?_)
    have hne : j ≠ i := hji
    by_cases hj : j ∈ F
    · simp only [hj, ↓reduceIte]
    · simp only [hj, ↓reduceIte, congrFun ih j]
      dsimp only [toProtocol]
      simp [dite_eq_left_of_eq_true (eq_true hne)]

private theorem state_eq_toProtocol_state (π : GraphProtocol (⊤ : SimpleGraph P) S M)
    (F : Finset P) (advG : ℕ → ∀ j i : P, (⊤ : SimpleGraph P).Adj j i → M) (x : P → Bool) :
    ∀ r, π.state F advG x r =
      π.toProtocol.state F
        (fun r j i => if hji : j ≠ i then some (advG r j i hji) else none) x r
  | 0 => rfl
  | r + 1 => by
    have ih := state_eq_toProtocol_state π F advG x r
    funext i; dsimp only [Byzantine.Protocol.state, state]
    refine congrArg₂ (π.update r i) (congrFun ih i) (funext fun j => funext fun hji => ?_)
    have hne : j ≠ i := hji
    by_cases hj : j ∈ F
    · simp [hj, dite_eq_left_of_eq_true (eq_true hne)]
    · simp only [hj, ↓reduceIte, congrFun ih j]
      dsimp only [toProtocol]
      simp [dite_eq_left_of_eq_true (eq_true hne)]

/-- A protocol on the complete simple graph `⊤` solves Byzantine agreement iff its
`Byzantine.Protocol` translation does. -/
theorem solvesByzantineAgreement_toProtocol_iff (π : GraphProtocol (⊤ : SimpleGraph P) S M)
    (t R : ℕ) :
    π.toProtocol.SolvesByzantineAgreement t R ↔ π.SolvesByzantineAgreement t R :=
  ⟨fun h =>
    ⟨fun F hF advG x i hi j hj => by
      simp only [decision, state_eq_toProtocol_state π F advG x R]
      exact h.agreement F hF _ x i hi j hj,
     fun F hF advG x v hv i hi => by
      simp only [decision, state_eq_toProtocol_state π F advG x R]
      exact h.validity F hF _ x v hv i hi⟩,
   fun h =>
    ⟨fun F hF adv x i hi j hj => by
      simp only [Byzantine.Protocol.decision, toProtocol_state_eq_state π F adv x R]
      exact h.agreement F hF _ x i hi j hj,
     fun F hF adv x v hv i hi => by
      simp only [Byzantine.Protocol.decision, toProtocol_state_eq_state π F adv x R]
      exact h.validity F hF _ x v hv i hi⟩⟩

/-- Restrict a complete-network `Cslib.Distributed.Byzantine.Protocol` to `GraphProtocol ⊤`,
computing self-messages locally from the process's own current state. -/
@[expose] def ofProtocol (π : Byzantine.Protocol P S M) :
    GraphProtocol (⊤ : SimpleGraph P) S M where
  init := π.init
  send r i s j _ := π.send r i s j
  update r i s m :=
    π.update r i s fun j => if hji : j = i then π.send r i s i else m j hji
  output := π.output

private theorem ofProtocol_state_eq_state (π : Byzantine.Protocol P S M) (F : Finset P)
    (adv : ℕ → P → P → M) (x : P → Bool) :
    ∀ r, ∀ i ∉ F,
      (ofProtocol π).state F (fun r j i _ => adv r j i) x r i = π.state F adv x r i
  | 0, _, _ => rfl
  | r + 1, i, hi => by
    dsimp only [state, Byzantine.Protocol.state]
    refine congrArg₂ (π.update r i) (ofProtocol_state_eq_state π F adv x r i hi)
      (funext fun j => ?_)
    by_cases hji : j = i
    · subst hji
      simp only [↓reduceDIte, hi, ↓reduceIte, ofProtocol_state_eq_state π F adv x r j hi]
    · simp only [hji, ↓reduceDIte]
      by_cases hj : j ∈ F
      · simp only [hj, ↓reduceIte]
      · simp only [hj, ↓reduceIte, ← ofProtocol_state_eq_state π F adv x r j hj]
        rfl

private theorem state_eq_ofProtocol_state (π : Byzantine.Protocol P S M) (F : Finset P)
    (advG : ℕ → ∀ j i : P, (⊤ : SimpleGraph P).Adj j i → M) (x : P → Bool) (r : ℕ) (i : P)
    (hi : i ∉ F) :
    (ofProtocol π).state F advG x r i =
      π.state F (fun r j i =>
        if hji : j = i then π.send r j (π.init j false) i
        else advG r j i hji) x r i := by
  let adv : ℕ → P → P → M := fun r j i =>
    if hji : j = i then π.send r j (π.init j false) i else advG r j i hji
  have hadv : advG = fun r j i _ => adv r j i :=
    funext fun r => funext fun j => funext fun i => funext fun (hji : j ≠ i) =>
      (dite_eq_right hji).symm
  exact (congrArg (fun a => (ofProtocol π).state F a x r i) hadv).trans
    (ofProtocol_state_eq_state π F adv x r i hi)

/-- Restricting a `Byzantine.Protocol` to `GraphProtocol ⊤` preserves `SolvesByzantineAgreement` in
both directions, keeping the state and message types unchanged. -/
theorem solvesByzantineAgreement_ofProtocol_iff (π : Byzantine.Protocol P S M) (t R : ℕ) :
    (ofProtocol π).SolvesByzantineAgreement t R ↔ π.SolvesByzantineAgreement t R :=
  ⟨fun h =>
    ⟨fun F hF adv x i hi j hj => by
      simp only [Byzantine.Protocol.decision, ← ofProtocol_state_eq_state π F adv x R i hi,
        ← ofProtocol_state_eq_state π F adv x R j hj]
      exact h.agreement F hF _ x i hi j hj,
     fun F hF adv x v hv i hi => by
      simp only [Byzantine.Protocol.decision, ← ofProtocol_state_eq_state π F adv x R i hi]
      exact h.validity F hF _ x v hv i hi⟩,
   fun h =>
    ⟨fun F hF advG x i hi j hj => by
      simp only [decision, state_eq_ofProtocol_state π F advG x R i hi,
        state_eq_ofProtocol_state π F advG x R j hj]
      exact h.agreement F hF _ x i hi j hj,
     fun F hF advG x v hv i hi => by
      simp only [decision, state_eq_ofProtocol_state π F advG x R i hi]
      exact h.validity F hF _ x v hv i hi⟩⟩

/-- **No synchronous Boolean consensus with `n ≤ 3t` processes on any graph**
([PeaseShostakLamport1980]; [FischerLynchMerritt1985], Theorem 1, §3.1, pp. 61–62): on any
communication graph `G` over `n` processes with `2 ≤ n ≤ 3t`, no protocol solves synchronous
fixed-round Boolean Byzantine agreement against `t` faults in any round count `R`. Obtained
immediately by simulating `π` on `⊤` (`toSupergraph le_top`) and applying the complete-graph node
bound `Cslib.Distributed.Byzantine.Protocol.not_solvesByzantineAgreement`. -/
theorem not_solvesByzantineAgreement [Fintype P] {t R : ℕ} (h2 : 2 ≤ Fintype.card P)
    (h3 : Fintype.card P ≤ 3 * t) : ¬ π.SolvesByzantineAgreement t R := by
  classical
  intro h
  exact ((π.toSupergraph (le_top : G ≤ ⊤)).toProtocol).not_solvesByzantineAgreement h2 h3
    ((solvesByzantineAgreement_toProtocol_iff _ t R).mpr
      ((π.solvesByzantineAgreement_toSupergraph_iff le_top t R).mpr h))

/-! ### Covering networks on a communication graph -/

omit [DecidableEq P] in
/-- The state of node `a` of a covering network over `G` after `r` rounds. Node `a` runs the code
of process `label a` on input `input a`, and receives the message along each incident `G`-edge
`hji : G.Adj j (label a)` from node `nbr a j`, which sends it as `j` would. -/
@[expose] def coverState {N : Type*} (label : N → P) (input : N → Bool) (nbr : N → P → N) :
    ℕ → N → S
  | 0, a => π.init (label a) (input a)
  | r + 1, a => π.update r (label a) (coverState label input nbr r a)
      (fun j hji => π.send r j (coverState label input nbr r (nbr a j)) (label a) hji)

omit [DecidableEq P] in
private theorem update_congr_label {r : ℕ} {i l : P} (hl : i = l) {s₁ s₂ : S} (hs : s₁ = s₂)
    {m₁ : ∀ j : P, G.Adj j i → M} {m₂ : ∀ j : P, G.Adj j l → M}
    (hm : ∀ j (hji : G.Adj j i), m₁ j hji = m₂ j (hl ▸ hji)) :
    π.update r i s₁ m₁ = π.update r l s₂ m₂ := by
  subst hl hs
  exact congrArg _ (funext fun j => funext (hm j))

omit [DecidableEq P] in
private theorem send_congr_target {r : ℕ} {j : P} {s₁ s₂ : S} (hs : s₁ = s₂) {i l : P}
    (hl : i = l) (hji : G.Adj j i) :
    π.send r j s₁ i hji = π.send r j s₂ l (hl ▸ hji) := by
  subst hl hs; rfl

/-- **The graph covering lemma** (after [Fischer, Lynch and Merritt][FischerLynchMerritt1985], §2,
pp. 60–61). Suppose the correct processes embed into a covering network by `e`, preserving their
labels, inputs, and mutual `G`-edges (`G.Adj j i → nbr (e i) j = e j`), and that along every
`G`-edge from a faulty process `j ∈ F` to a correct process `i ∉ F`, `j` sends what `nbr (e i) j`
sends in the covering network. Then every correct process `i` has the same state as `e i` after
every round. -/
theorem state_eq_coverState {N : Type*} (label : N → P) (input : N → Bool) (nbr : N → P → N)
    (F : Finset P) (adv : ℕ → ∀ j i : P, G.Adj j i → M) (x : P → Bool) (e : P → N)
    (hlabel : ∀ i ∉ F, label (e i) = i) (hinput : ∀ i ∉ F, input (e i) = x i)
    (hnbr : ∀ i ∉ F, ∀ j ∉ F, G.Adj j i → nbr (e i) j = e j)
    (hadv : ∀ r, ∀ i ∉ F, ∀ j ∈ F, ∀ hji : G.Adj j i,
      adv r j i hji = π.send r j (π.coverState label input nbr r (nbr (e i) j)) i hji) :
    ∀ r, ∀ i ∉ F, π.state F adv x r i = π.coverState label input nbr r (e i)
  | 0, i, hi => by simp only [state, coverState, hlabel i hi, hinput i hi]
  | r + 1, i, hi => by
    simp only [state, coverState]
    refine π.update_congr_label (hlabel i hi).symm
      (state_eq_coverState label input nbr F adv x e hlabel hinput hnbr hadv r i hi)
      fun j hji => ?_
    by_cases hj : j ∈ F
    · simp only [hj, ↓reduceIte, hadv r i hi j hj hji]
      exact π.send_congr_target rfl (hlabel i hi).symm hji
    · simp only [hj, ↓reduceIte]
      have ihj := state_eq_coverState label input nbr F adv x e hlabel hinput hnbr hadv r j hj
      exact π.send_congr_target (ihj.trans (by rw [hnbr i hi j hj hji])) (hlabel i hi).symm hji

end GraphProtocol

/-- On the complete simple graph `⊤`, `GraphProtocol ⊤` and `Cslib.Distributed.Byzantine.Protocol`
admit solutions for the exact same fault thresholds `t` and round bounds `R`. -/
theorem exists_solvesByzantineAgreement_top_iff.{u, v, w} {P : Type u} [DecidableEq P]
    (t R : ℕ) :
    (∃ (S : Type v) (M : Type w) (π : GraphProtocol (⊤ : SimpleGraph P) S M),
        π.SolvesByzantineAgreement t R) ↔
      ∃ (S : Type v) (M : Type w) (π : Byzantine.Protocol P S M),
        π.SolvesByzantineAgreement t R := by
  constructor
  · rintro ⟨S, M, π, h⟩
    exact ⟨S, Option M, π.toProtocol, (π.solvesByzantineAgreement_toProtocol_iff t R).mpr h⟩
  · rintro ⟨S, M, π, h⟩
    exact ⟨S, M, GraphProtocol.ofProtocol π,
      (GraphProtocol.solvesByzantineAgreement_ofProtocol_iff π t R).mpr h⟩

end Cslib.Distributed.ByzantineGraph
