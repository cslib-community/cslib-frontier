/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Median
public import CslibFrontier.Computability.Circuit.Frontier.Network
public import CslibFrontier.Computability.Circuit.InnerSize
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum

/-!
# Post-layout Steiner hypergraph compiler for bounded-fan-in circuits

In `CslibFrontier/Computability/Circuit/Frontier/Compiler/Network.lean`, each signal `w` of fan-out
`f_w` is expanded *before* choosing a vertex layout `π` into a fixed junction chain
`w --- j_0 --- j_1 --- ...` of `f_w` degree-`3` vertices. If `π` visits the consumers of `w` out of
chain order, the chain crosses a cut multiple times and pays multiple frontier bits for the single
value of `w`.

This module compiles a single-output circuit `c : Circuit σ n 1` directly to its **live multiary
signal hypergraph** and, *after* a layout `π : Layout (HyperNode c)` is chosen, routes each live
signal `w` along a `π`-monotone Steiner path (`hyperNetwork c I Acc π`) that crosses every frontier
at most once:

1. **Multiary root collapse (`rootSignal`, `evalFromRoots`).** Chains of nullary and unary gates
   cost zero vertices and zero frontier bits: every wire `w` evaluates as a pure function of at most
   one input or multiary gate (`arity ≥ 2`).
2. **Signal hypergraph (`HyperNode`, `LiveSignal`, `hyperEdge`, `hyperCut`, `hyperWidth`).** The
   vertices `HyperNode c = LiveGate c ⊕ Unit` are the live multiary gates (`≤ c.multiarySize`) plus
   one output vertex. Each live signal `w : LiveInput c ⊕ LiveGate c` spans the hyperedge
   `hyperEdge c w` of nodes producing or reading `w`. For fan-in at most `r`, every node belongs to
   at most `r + 1` hyperedges, every gate hyperedge has cardinality at least `2`, and
   `∑ w, |hyperEdge c w| ≤ (r + 1) |LiveGate c| + 1`.
3. **Post-layout Steiner network (`hyperNetwork`).** Given *any* layout `π : Layout (HyperNode c)`,
   sorting each `hyperEdge c w` in increasing `π`-order and linking consecutive vertices gives a
   constraint network of maximum degree at most `2 (r + 1)`, reading at most `max r 1` inputs per
   vertex, with **exact** frontier width `(hyperNetwork c I Acc π).width π = hyperWidth c π`,
   exact acceptance `{x | c.eval I x 0 ∈ Acc}`, and unique satisfying assignments.

## Main definitions

* `Cslib.Circuits.Frontier.Hypergraph.rootSignal`,
  `Cslib.Circuits.Frontier.Hypergraph.evalFromRoots`: tracing wires through unary/nullary chains to
  inputs and multiary gates.
* `Cslib.Circuits.Frontier.Hypergraph.LiveInput`, `Cslib.Circuits.Frontier.Hypergraph.LiveGate`,
  `Cslib.Circuits.Frontier.Hypergraph.LiveSignal`, `Cslib.Circuits.Frontier.Hypergraph.HyperNode`:
  live signals and hypergraph vertices of a circuit.
* `Cslib.Circuits.Frontier.Hypergraph.hyperEdge`, `Cslib.Circuits.Frontier.Hypergraph.hyperCut`,
  `Cslib.Circuits.Frontier.Hypergraph.hyperWidth`: signal hyperedges, hyperedge cuts, and hypergraph
  layout width.
* `Cslib.Circuits.Frontier.Hypergraph.SteinerEdge`,
  `Cslib.Circuits.Frontier.Hypergraph.hyperNetwork`: post-layout `π`-monotone Steiner constraint
  network.

## Main results

* `Cslib.Circuits.Frontier.Hypergraph.card_liveGate_le_multiarySize`,
  `Cslib.Circuits.Frontier.Hypergraph.card_hyperNode_le`: `|LiveGate c| ≤ c.multiarySize` and
  `|HyperNode c| ≤ c.multiarySize + 1`.
* `Cslib.Circuits.Frontier.Hypergraph.two_le_card_hyperEdge_gate`,
  `Cslib.Circuits.Frontier.Hypergraph.sum_card_hyperEdge_le`: structural hypergraph invariants under
  `c.FanInAtMost r`.
* `Cslib.Circuits.Frontier.Hypergraph.width_hyperNetwork`,
  `Cslib.Circuits.Frontier.Hypergraph.maxDegreeLE_hyperNetwork`,
  `Cslib.Circuits.Frontier.Hypergraph.ncard_readAt_hyperNetwork_le`,
  `Cslib.Circuits.Frontier.Hypergraph.accepted_hyperNetwork`,
  `Cslib.Circuits.Frontier.Hypergraph.satisfies_unique`: exactness, degree/read bounds, and exact
  width preservation of `hyperNetwork`.
-/

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open Set Cslib.Circuits

variable {σ : Signature} {n : ℕ}

/-! ### Multiary root reduction through unary and nullary gates -/

/-- Topological rank of a wire: `0` on inputs and `k + 1` on gate `k`. -/
def wireRank {g : ℕ} : Wire n g → ℕ
  | .input _ => 0
  | .gate k => (k : ℕ) + 1

/-- Every wire read by gate `k` has strictly smaller `wireRank` than `.gate k`. -/
theorem wireRank_arg_lt {g : ℕ} (p : Program σ n g) (k : Fin g)
    (a : Fin (σ.Arity (p.lines k).op)) :
    wireRank ((p.lines k).wires a) < wireRank (.gate k : Wire n g) := by
  cases hw : (p.lines k).wires a with
  | input _ => simp [wireRank]
  | gate j =>
    simp only [wireRank]
    exact Nat.add_lt_add_right (p.lt_of_lines_wires_eq_gate k a j hw) 1

/-- Follow unary chains back from any wire `w` to the unique input `.inl i` or multiary gate
`.inr k` (`arity ≥ 2`) on which `w` depends, or `none` if `w` reduces to a nullary constant. -/
def rootSignal (c : Circuit σ n 1) : Wire n c.size → Option (Fin n ⊕ Fin c.size)
  | .input i => some (.inl i)
  | .gate k =>
    if 2 ≤ σ.Arity (c.program.lines k).op then
      some (.inr k)
    else if h0 : 0 < σ.Arity (c.program.lines k).op then
      have := wireRank_arg_lt c.program k ⟨0, h0⟩
      rootSignal c ((c.program.lines k).wires ⟨0, h0⟩)
    else
      none
termination_by w => wireRank w

/-- Every gate returned by `rootSignal` is a multiary gate (`arity ≥ 2`). -/
theorem rootSignal_mem_multiaryGates (c : Circuit σ n 1) :
    ∀ (w : Wire n c.size) {k : Fin c.size},
      rootSignal c w = some (.inr k) → k ∈ c.program.multiaryGates := by
  refine c.program.wire_induction
    (fun i _ h => by unfold rootSignal at h; simp at h) (fun g ih k h => ?_)
  unfold rootSignal at h
  by_cases h2 : 2 ≤ σ.Arity (c.program.lines g).op
  · simp only [h2, ↓reduceIte, Option.some.injEq, Sum.inr.injEq] at h
    subst h
    exact Program.mem_multiaryGates.mpr h2
  · simp only [h2, ↓reduceIte] at h
    by_cases h0 : 0 < σ.Arity (c.program.lines g).op
    · simp only [h0, ↓reduceDIte] at h
      exact ih ⟨0, h0⟩ h
    · simp [h0] at h

/-- If `rootSignal c w = some (.inr k)`, then `k + 1 ≤ wireRank w`. -/
theorem rootSignal_gate_rank_le (c : Circuit σ n 1) :
    ∀ (w : Wire n c.size) {k : Fin c.size},
      rootSignal c w = some (.inr k) → (k : ℕ) + 1 ≤ wireRank w := by
  refine c.program.wire_induction
    (fun i _ h => by unfold rootSignal at h; simp at h) (fun g ih k h => ?_)
  unfold rootSignal at h
  by_cases h2 : 2 ≤ σ.Arity (c.program.lines g).op
  · simp only [h2, ↓reduceIte, Option.some.injEq, Sum.inr.injEq] at h
    subst h
    exact le_rfl
  · simp only [h2, ↓reduceIte] at h
    by_cases h0 : 0 < σ.Arity (c.program.lines g).op
    · simp only [h0, ↓reduceDIte] at h
      exact (ih ⟨0, h0⟩ h).trans (wireRank_arg_lt c.program g ⟨0, h0⟩).le
    · simp [h0] at h

/-- Evaluate any wire `w` from a valuation `ρ` of inputs and multiary gates by evaluating only
the nullary and unary gates along the chain to `rootSignal c w`. -/
def evalFromRoots {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (ρ : Fin n ⊕ Fin c.size → U) : Wire n c.size → U
  | .input i => ρ (.inl i)
  | .gate k =>
    if 2 ≤ σ.Arity (c.program.lines k).op then
      ρ (.inr k)
    else
      I (c.program.lines k).op fun a =>
        have := wireRank_arg_lt c.program k a
        evalFromRoots c I ρ ((c.program.lines k).wires a)
termination_by w => wireRank w

/-- `evalFromRoots c I ρ w` depends on `ρ` only at the single root `rootSignal c w` (if any). -/
theorem evalFromRoots_congr {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    {ρ₁ ρ₂ : Fin n ⊕ Fin c.size → U} :
    ∀ (w : Wire n c.size),
      (∀ r, rootSignal c w = some r → ρ₁ r = ρ₂ r) →
        evalFromRoots c I ρ₁ w = evalFromRoots c I ρ₂ w := by
  refine c.program.wire_induction
    (fun i h => by
      unfold evalFromRoots
      exact h (.inl i) (by unfold rootSignal; rfl))
    (fun k ih h => ?_)
  conv_lhs => unfold evalFromRoots
  conv_rhs => unfold evalFromRoots
  split_ifs with h2
  · exact h (.inr k) (by unfold rootSignal; simp [h2])
  · congr 1
    funext a
    have h0 : 0 < σ.Arity (c.program.lines k).op := lt_of_le_of_lt (Nat.zero_le _) a.isLt
    have ha0 : a = ⟨0, h0⟩ := Fin.ext (by omega)
    rw [ha0]
    refine ih ⟨0, h0⟩ fun r hr => h r ?_
    unfold rootSignal
    simp [h2, h0, hr]

/-- Canonical root valuation induced by an input vector `x : Fin n → U`. -/
def trueRootVal {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U) (x : Fin n → U) :
    Fin n ⊕ Fin c.size → U
  | .inl i => x i
  | .inr k => c.program.trace I x (.gate k)

/-- Evaluating any wire from `trueRootVal c I x` recovers `c.program.trace I x`. -/
theorem evalFromRoots_trueRootVal {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (x : Fin n → U) :
    ∀ w : Wire n c.size, evalFromRoots c I (trueRootVal c I x) w = c.program.trace I x w := by
  refine c.program.wire_induction
    (fun i => by unfold evalFromRoots; rfl) (fun k ih => ?_)
  unfold evalFromRoots
  split_ifs with h2
  · rfl
  · rw [c.program.trace_gate]
    congr 1
    funext a
    exact ih a

/-! ### Live multiary gates, live signals, and signal hyperedges -/

/-- Reachability in the multiary root DAG from the designated output wire `c.outputs 0`. -/
inductive LiveRoot (c : Circuit σ n 1) : Fin n ⊕ Fin c.size → Prop
  /-- The root signal (if any) of the output wire is live. -/
  | output {r} : rootSignal c (c.outputs 0) = some r → LiveRoot c r
  /-- Every root signal read by an argument of a live gate is live. -/
  | arg {k : Fin c.size} : LiveRoot c (.inr k) →
      (a : Fin (σ.Arity (c.program.lines k).op)) →
      ∀ {r}, rootSignal c ((c.program.lines k).wires a) = some r → LiveRoot c r

theorem LiveRoot.mem_multiaryGates {c : Circuit σ n 1} {k : Fin c.size}
    (hk : LiveRoot c (.inr k)) : k ∈ c.program.multiaryGates := by
  cases hk with
  | output hr => exact rootSignal_mem_multiaryGates c (c.outputs 0) hr
  | arg _ a hr => exact rootSignal_mem_multiaryGates c ((c.program.lines _).wires a) hr

open Classical in
/-- Finset of input indices reachable in the multiary root DAG. -/
noncomputable def liveInputs (c : Circuit σ n 1) : Finset (Fin n) :=
  Finset.univ.filter fun i => LiveRoot c (.inl i)

open Classical in
/-- Finset of multiary gate indices reachable in the multiary root DAG. -/
noncomputable def liveGates (c : Circuit σ n 1) : Finset (Fin c.size) :=
  c.program.multiaryGates.filter fun k => LiveRoot c (.inr k)

/-- Type of live inputs of `c`. -/
abbrev LiveInput (c : Circuit σ n 1) : Type := ↥(liveInputs c)

/-- Type of live multiary gates of `c`. -/
abbrev LiveGate (c : Circuit σ n 1) : Type := ↥(liveGates c)

/-- Type of live signals of `c`: live inputs and live multiary gates. -/
abbrev LiveSignal (c : Circuit σ n 1) : Type := LiveInput c ⊕ LiveGate c

/-- Hypergraph vertices of `c`: one vertex per live multiary gate plus one output vertex. -/
abbrev HyperNode (c : Circuit σ n 1) : Type := LiveGate c ⊕ Unit

theorem mem_liveInputs_iff {c : Circuit σ n 1} {i : Fin n} :
    i ∈ liveInputs c ↔ LiveRoot c (.inl i) := by
  classical
  simp [liveInputs]

theorem mem_liveGates_iff {c : Circuit σ n 1} {k : Fin c.size} :
    k ∈ liveGates c ↔ LiveRoot c (.inr k) := by
  classical
  simp only [liveGates, Finset.mem_filter, and_iff_right_iff_imp]
  exact LiveRoot.mem_multiaryGates

/-- A circuit has at most `n` live inputs. -/
theorem card_liveInput_le (c : Circuit σ n 1) : Fintype.card (LiveInput c) ≤ n := by
  rw [Fintype.card_coe]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)

/-- A circuit has at most `c.multiarySize` live multiary gates. -/
theorem card_liveGate_le_multiarySize (c : Circuit σ n 1) :
    Fintype.card (LiveGate c) ≤ c.multiarySize := by
  classical
  rw [Fintype.card_coe, Circuit.multiarySize]
  exact Finset.card_filter_le _ _

/-- The number of hypergraph vertices is `|LiveGate c| + 1`. -/
theorem card_hyperNode_eq (c : Circuit σ n 1) :
    Fintype.card (HyperNode c) = Fintype.card (LiveGate c) + 1 := by
  rw [Fintype.card_sum, Fintype.card_unique (α := Unit)]

/-- The hypergraph has at most `c.multiarySize + 1` vertices. -/
theorem card_hyperNode_le (c : Circuit σ n 1) :
    Nat.card (HyperNode c) ≤ c.multiarySize + 1 := by
  rw [Nat.card_eq_fintype_card, card_hyperNode_eq]
  exact Nat.add_le_add_right (card_liveGate_le_multiarySize c) 1

/-- Underlying root index in `Fin n ⊕ Fin c.size` of a live signal. -/
def signalRoot {c : Circuit σ n 1} : LiveSignal c → Fin n ⊕ Fin c.size
  | .inl i => .inl i.1
  | .inr g => .inr g.1

theorem signalRoot_injective {c : Circuit σ n 1} :
    Function.Injective (signalRoot (c := c)) := by
  rintro (i₁ | g₁) (i₂ | g₂) h <;> simp only [signalRoot] at h
  · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj h))
  · nomatch h
  · nomatch h
  · exact congrArg Sum.inr (Subtype.ext (Sum.inr.inj h))

theorem signalRoot_live {c : Circuit σ n 1} (w : LiveSignal c) : LiveRoot c (signalRoot w) := by
  rcases w with i | g
  · exact (mem_liveInputs_iff.mp i.2)
  · exact (mem_liveGates_iff.mp g.2)

/-- Lift a root `r` known to satisfy `LiveRoot c r` into `LiveSignal c`. -/
noncomputable def liftLiveSignal {c : Circuit σ n 1} (r : Fin n ⊕ Fin c.size)
    (hr : LiveRoot c r) : LiveSignal c :=
  match r with
  | .inl i => .inl ⟨i, mem_liveInputs_iff.mpr hr⟩
  | .inr k => .inr ⟨k, mem_liveGates_iff.mpr hr⟩

@[simp] theorem signalRoot_liftLiveSignal {c : Circuit σ n 1} (r : Fin n ⊕ Fin c.size)
    (hr : LiveRoot c r) : signalRoot (liftLiveSignal r hr) = r := by
  cases r <;> rfl

/-- Incidence predicate between a live signal `w` and a hypergraph vertex `u`: `u` belongs to `w`'s
hyperedge when `u` produces `w` (`w = .inr g` at `u = .inl g`) or reads `w`. -/
def NodeInEdge (c : Circuit σ n 1) (w : LiveSignal c) : HyperNode c → Prop
  | .inl g =>
    w = .inr g ∨
      ∃ a : Fin (σ.Arity (c.program.lines g.1).op),
        rootSignal c ((c.program.lines g.1).wires a) = some (signalRoot w)
  | .inr () =>
    rootSignal c (c.outputs 0) = some (signalRoot w)

open Classical in
/-- Hyperedge of a live signal `w`: all hypergraph nodes producing or consuming `w`. -/
noncomputable def hyperEdge (c : Circuit σ n 1) (w : LiveSignal c) : Finset (HyperNode c) :=
  Finset.univ.filter (NodeInEdge c w)

theorem mem_hyperEdge_iff {c : Circuit σ n 1} {w : LiveSignal c} {u : HyperNode c} :
    u ∈ hyperEdge c w ↔ NodeInEdge c w u := by
  classical
  simp [hyperEdge]

theorem self_mem_hyperEdge {c : Circuit σ n 1} (g : LiveGate c) :
    (.inl g : HyperNode c) ∈ hyperEdge c (.inr g) :=
  mem_hyperEdge_iff.mpr (Or.inl rfl)

/-- Every live signal belongs to at least one consumer node, so its hyperedge is nonempty. -/
theorem hyperEdge_nonempty (c : Circuit σ n 1) (w : LiveSignal c) :
    (hyperEdge c w).Nonempty := by
  rcases hlive : signalRoot w with i | k
  · have hr : LiveRoot c (.inl i) := hlive ▸ signalRoot_live w
    cases hr with
    | output hout =>
      exact ⟨.inr (), mem_hyperEdge_iff.mpr (by simp [NodeInEdge, hlive, hout])⟩
    | @arg k' hk' a _ harg =>
      exact ⟨.inl ⟨k', mem_liveGates_iff.mpr hk'⟩,
        mem_hyperEdge_iff.mpr (Or.inr ⟨a, by rw [hlive]; exact harg⟩)⟩
  · have hw : w = .inr ⟨k, mem_liveGates_iff.mpr (hlive ▸ signalRoot_live w)⟩ :=
      signalRoot_injective (by simpa [signalRoot] using hlive)
    rw [hw]
    exact ⟨.inl _, self_mem_hyperEdge _⟩

theorem card_hyperEdge_pos (c : Circuit σ n 1) (w : LiveSignal c) :
    1 ≤ (hyperEdge c w).card :=
  Finset.card_pos.mpr (hyperEdge_nonempty c w)

/-- Every live multiary gate has hyperedge cardinality at least `2`: its own vertex `.inl g` plus
at least one consumer vertex strictly later in topological order (or the output vertex). -/
theorem two_le_card_hyperEdge_gate (c : Circuit σ n 1) (g : LiveGate c) :
    2 ≤ (hyperEdge c (.inr g)).card := by
  refine Finset.one_lt_card_iff.mpr ?_
  have hg : LiveRoot c (.inr g.1) := mem_liveGates_iff.mp g.2
  cases hg with
  | output hout =>
    exact ⟨.inl g, .inr (), self_mem_hyperEdge g, mem_hyperEdge_iff.mpr hout, by simp⟩
  | @arg k hk a _ harg =>
    let g' : LiveGate c := ⟨k, mem_liveGates_iff.mpr hk⟩
    have hmem' : (.inl g' : HyperNode c) ∈ hyperEdge c (.inr g) :=
      mem_hyperEdge_iff.mpr (Or.inr ⟨a, harg⟩)
    have hlt : (g.1 : ℕ) + 1 < (k : ℕ) + 1 :=
      (rootSignal_gate_rank_le c _ harg).trans_lt (wireRank_arg_lt c.program k a)
    have hne : (.inl g : HyperNode c) ≠ .inl g' := by
      intro h
      have heq : (g.1 : ℕ) = (k : ℕ) := congrArg (fun x : LiveGate c => (x.1 : ℕ)) (Sum.inl.inj h)
      omega
    exact ⟨.inl g, .inl g', self_mem_hyperEdge g, hmem', hne⟩

/-- At the output node `.inr ()`, at most `1` live signal is incident. -/
theorem card_signals_at_output_le (c : Circuit σ n 1) :
    (Finset.univ.filter fun w : LiveSignal c => (.inr () : HyperNode c) ∈ hyperEdge c w).card ≤
      1 := by
  refine Finset.card_le_one.mpr fun w₁ hw₁ w₂ hw₂ => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_hyperEdge_iff, NodeInEdge] at hw₁ hw₂
  exact signalRoot_injective (Option.some.inj (hw₁.symm.trans hw₂))

/-- At a live gate `.inl g` in a circuit with `c.FanInAtMost r`, at most `r` argument signals
(other than `.inr g` itself) and at most `r + 1` total live signals are incident. -/
theorem card_arg_signals_at_gate_le {c : Circuit σ n 1} {r : ℕ} (hfan : c.FanInAtMost r)
    (g : LiveGate c) :
    (Finset.univ.filter fun w : LiveSignal c =>
      ∃ a : Fin (σ.Arity (c.program.lines g.1).op),
        rootSignal c ((c.program.lines g.1).wires a) = some (signalRoot w)).card ≤ r := by
  classical
  let m := σ.Arity (c.program.lines g.1).op
  have hm : m ≤ r := Program.fanInAtMost_iff.mp hfan g.1
  let fiber : Fin m → Finset (LiveSignal c) := fun a =>
    Finset.univ.filter fun w =>
      rootSignal c ((c.program.lines g.1).wires a) = some (signalRoot w)
  have hfiber_le (a : Fin m) : (fiber a).card ≤ 1 := by
    refine Finset.card_le_one.mpr fun w₁ hw₁ w₂ hw₂ => ?_
    simp only [fiber, Finset.mem_filter, Finset.mem_univ, true_and] at hw₁ hw₂
    exact signalRoot_injective (Option.some.inj (hw₁.symm.trans hw₂))
  calc _ ≤ (Finset.univ.biUnion fiber).card :=
        Finset.card_le_card fun w hw => by simpa [fiber] using hw
    _ ≤ ∑ a : Fin m, (fiber a).card := Finset.card_biUnion_le
    _ ≤ ∑ _a : Fin m, 1 := Finset.sum_le_sum fun a _ => hfiber_le a
    _ = m := by simp [m]
    _ ≤ r := hm

theorem card_signals_at_gate_le {c : Circuit σ n 1} {r : ℕ} (hfan : c.FanInAtMost r)
    (g : LiveGate c) :
    (Finset.univ.filter fun w : LiveSignal c => (.inl g : HyperNode c) ∈ hyperEdge c w).card ≤
      r + 1 := by
  classical
  let S : Finset (LiveSignal c) := Finset.univ.filter fun w : LiveSignal c =>
    ∃ a : Fin (σ.Arity (c.program.lines g.1).op),
      rootSignal c ((c.program.lines g.1).wires a) = some (signalRoot w)
  have hsub : (Finset.univ.filter fun w : LiveSignal c =>
      (.inl g : HyperNode c) ∈ hyperEdge c w) ⊆ insert (.inr g) S := by
    intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_hyperEdge_iff, NodeInEdge] at hw
    rcases hw with rfl | ha
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ w, ha⟩)
  calc (Finset.univ.filter fun w : LiveSignal c => (.inl g : HyperNode c) ∈ hyperEdge c w).card
      ≤ (insert (.inr g) S).card := Finset.card_le_card hsub
    _ ≤ S.card + 1 := Finset.card_insert_le _ _
    _ ≤ r + 1 := Nat.add_le_add_right (card_arg_signals_at_gate_le hfan g) 1

theorem card_signals_at_node_le {c : Circuit σ n 1} {r : ℕ} (hfan : c.FanInAtMost r)
    (u : HyperNode c) :
    (Finset.univ.filter fun w : LiveSignal c => u ∈ hyperEdge c w).card ≤ r + 1 := by
  rcases u with g | ⟨⟩
  · exact card_signals_at_gate_le hfan g
  · exact (card_signals_at_output_le c).trans (Nat.le_add_left 1 r)

/-- Total pin count (sum of hyperedge sizes) across all live signals is at most
`(r + 1) |LiveGate c| + 1`. -/
theorem sum_card_hyperEdge_le {c : Circuit σ n 1} {r : ℕ} (hfan : c.FanInAtMost r) :
    ∑ w : LiveSignal c, (hyperEdge c w).card ≤ (r + 1) * Fintype.card (LiveGate c) + 1 := by
  classical
  have hswap : ∑ w : LiveSignal c, (hyperEdge c w).card =
      ∑ u : HyperNode c, (Finset.univ.filter fun w : LiveSignal c => u ∈ hyperEdge c w).card := by
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    have hlhs : ∀ w : LiveSignal c,
        (∑ _u ∈ hyperEdge c w, 1) = ∑ u : HyperNode c, if u ∈ hyperEdge c w then 1 else 0 :=
      fun w => by rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    simp_rw [hlhs]
    exact Finset.sum_comm
  rw [hswap, Fintype.sum_sum_type, Finset.univ_unique (α := Unit), PUnit.default_eq_unit,
    Finset.sum_singleton]
  refine Nat.add_le_add ?_ (card_signals_at_output_le c)
  calc _ ≤ ∑ _g : LiveGate c, (r + 1) := Finset.sum_le_sum fun g _ => card_signals_at_gate_le hfan g
    _ = (r + 1) * Fintype.card (LiveGate c) := by simp [Nat.mul_comm]

/-! ### Signal cuts and hypergraph layout width -/

/-- A hyperedge `e : Finset V` straddles `L : Set V` when it meets both `L` and `Lᶜ`. -/
@[expose] def HyperedgeStraddles {V : Type*} (e : Finset V) (L : Set V) : Prop :=
  (∃ u ∈ e, u ∈ L) ∧ (∃ v ∈ e, v ∉ L)

/-- Along a real vertex-score threshold `{u | f u < t}`, `HyperedgeStraddles e {u | f u < t}` is
definitionally equivalent to `StraddlesOn f t ↑e`. -/
theorem hyperedgeStraddles_threshold_iff {V : Type*} (e : Finset V) (f : V → ℝ) (t : ℝ) :
    HyperedgeStraddles e {u | f u < t} ↔ StraddlesOn f t (e : Set V) := by
  simp [HyperedgeStraddles, StraddlesOn]

open Classical in
/-- Signal frontier of `L`: the live signals whose hyperedge straddles `L`. -/
noncomputable def hyperCut (c : Circuit σ n 1) (L : Set (HyperNode c)) : Finset (LiveSignal c) :=
  Finset.univ.filter fun w => HyperedgeStraddles (hyperEdge c w) L

@[simp] theorem mem_hyperCut_iff {c : Circuit σ n 1} {L : Set (HyperNode c)} {w : LiveSignal c} :
    w ∈ hyperCut c L ↔ HyperedgeStraddles (hyperEdge c w) L := by
  classical
  simp [hyperCut]

/-- Hypergraph cutwidth of layout `π : Layout (HyperNode c)`: maximum size of `hyperCut` across all
prefixes `π.initial t`. -/
@[expose] noncomputable def hyperWidth (c : Circuit σ n 1) (π : Layout (HyperNode c)) : ℕ :=
  (Finset.range (Nat.card (HyperNode c))).sup fun t => (hyperCut c (π.initial t)).card

/-! ### Post-layout `π`-monotone Steiner constraint network -/

/-- Edges of the post-layout Steiner chain network: `|hyperEdge c w| - 1` chain edges for each live
signal `w : LiveSignal c`. -/
abbrev SteinerEdge (c : Circuit σ n 1) : Type :=
  Σ w : LiveSignal c, Fin ((hyperEdge c w).card - 1)

/-- Canonical `π`-increasing enumeration of `hyperEdge c w`. -/
noncomputable def steinerNode {c : Circuit σ n 1} (π : Layout (HyperNode c)) (w : LiveSignal c) :
    Fin (hyperEdge c w).card → HyperNode c :=
  let sFin : Finset (Fin (Nat.card (HyperNode c))) := (hyperEdge c w).map π.toEmbedding
  have hcard : sFin.card = (hyperEdge c w).card := Finset.card_map _
  fun j => π.symm (sFin.orderEmbOfFin hcard j)

private theorem pi_steinerNode_strictMono {c : Circuit σ n 1} (π : Layout (HyperNode c))
    (w : LiveSignal c) :
    StrictMono fun j : Fin (hyperEdge c w).card => π (steinerNode π w j) := by
  intro j₁ j₂ hj
  simp only [steinerNode, Equiv.apply_symm_apply]
  exact ((hyperEdge c w).map π.toEmbedding |>.orderEmbOfFin (Finset.card_map _)).strictMono hj

private theorem steinerNode_injective {c : Circuit σ n 1} (π : Layout (HyperNode c))
    (w : LiveSignal c) : Function.Injective (steinerNode π w) :=
  fun _ _ h => (pi_steinerNode_strictMono π w).injective (congrArg π h)

private theorem steinerNode_mem {c : Circuit σ n 1} (π : Layout (HyperNode c)) (w : LiveSignal c)
    (j : Fin (hyperEdge c w).card) : steinerNode π w j ∈ hyperEdge c w := by
  have hmem := Finset.orderEmbOfFin_mem ((hyperEdge c w).map π.toEmbedding)
    (Finset.card_map _) j
  rcases Finset.mem_map.mp hmem with ⟨u, hu, heq⟩
  have hsymm : π.symm (((hyperEdge c w).map π.toEmbedding).orderEmbOfFin
      (Finset.card_map _) j) = u := by
    rw [← heq]; exact π.symm_apply_apply u
  simpa only [steinerNode, hsymm] using hu

private theorem exists_steinerNode_eq {c : Circuit σ n 1} (π : Layout (HyperNode c))
    {w : LiveSignal c} {u : HyperNode c} (hu : u ∈ hyperEdge c w) :
    ∃ j : Fin (hyperEdge c w).card, steinerNode π w j = u := by
  have hmem : π u ∈ ((hyperEdge c w).map π.toEmbedding : Set (Fin (Nat.card (HyperNode c)))) :=
    Finset.mem_coe.mpr (Finset.mem_map_of_mem _ hu)
  rw [← Finset.range_orderEmbOfFin ((hyperEdge c w).map π.toEmbedding) (Finset.card_map _),
    Set.mem_range] at hmem
  obtain ⟨j, hj⟩ := hmem
  exact ⟨j, by simp [steinerNode, hj]⟩

/-- Underlying multigraph of `π`-monotone Steiner chains on `HyperNode c`. -/
noncomputable def steinerGraph (c : Circuit σ n 1) (π : Layout (HyperNode c)) :
    Multigraph (HyperNode c) (SteinerEdge c) where
  src e := steinerNode π e.1 ⟨e.2.val, by omega⟩
  tgt e := steinerNode π e.1 ⟨e.2.val + 1, by omega⟩

private theorem steinerGraph_src_mem {c : Circuit σ n 1} (π : Layout (HyperNode c))
    (e : SteinerEdge c) : (steinerGraph c π).src e ∈ hyperEdge c e.1 :=
  steinerNode_mem π e.1 _

private theorem steinerGraph_tgt_mem {c : Circuit σ n 1} (π : Layout (HyperNode c))
    (e : SteinerEdge c) : (steinerGraph c π).tgt e ∈ hyperEdge c e.1 :=
  steinerNode_mem π e.1 _

private theorem steinerGraph_end_mem {c : Circuit σ n 1} {π : Layout (HyperNode c)}
    {e : SteinerEdge c} {u : HyperNode c}
    (hu : (steinerGraph c π).src e = u ∨ (steinerGraph c π).tgt e = u) :
    u ∈ hyperEdge c e.1 := by
  rcases hu with rfl | rfl
  · exact steinerGraph_src_mem π e
  · exact steinerGraph_tgt_mem π e

theorem loopless_steinerGraph (c : Circuit σ n 1) (π : Layout (HyperNode c)) :
    (steinerGraph c π).Loopless := by
  intro e h
  have hlt : π ((steinerGraph c π).src e) < π ((steinerGraph c π).tgt e) :=
    pi_steinerNode_strictMono π e.1 (by simp [Fin.lt_def])
  exact hlt.ne (congrArg π h)

/-- Canonical consumer vertex at which live input `i` is read in `hyperNetwork`. -/
noncomputable def inputAnchor (c : Circuit σ n 1) (i : LiveInput c) : HyperNode c :=
  (hyperEdge_nonempty c (.inl i)).choose

theorem inputAnchor_mem (c : Circuit σ n 1) (i : LiveInput c) :
    inputAnchor c i ∈ hyperEdge c (.inl i) :=
  (hyperEdge_nonempty c (.inl i)).choose_spec

theorem inputAnchor_ne_self_signal {c : Circuit σ n 1} (i : LiveInput c) (g : LiveGate c)
    (h : inputAnchor c i = .inl g) :
    ∃ a : Fin (σ.Arity (c.program.lines g.1).op),
      rootSignal c ((c.program.lines g.1).wires a) = some (.inl i.1) := by
  have hmem := h ▸ inputAnchor_mem c i
  rcases mem_hyperEdge_iff.mp hmem with h_eq | ha
  · nomatch h_eq
  · exact ha

open Classical in
/-- Extend a local signal valuation at `u` to all of `Fin n ⊕ Fin c.size` using fallback `u₀`. -/
noncomputable def extendLocalVal {U : Type*} {c : Circuit σ n 1} (u : HyperNode c) (u₀ : U)
    (val : {w : LiveSignal c // u ∈ hyperEdge c w} → U) : Fin n ⊕ Fin c.size → U
  | .inl i =>
    if hi : i ∈ liveInputs c then
      if hu : u ∈ hyperEdge c (.inl ⟨i, hi⟩) then val ⟨.inl ⟨i, hi⟩, hu⟩ else u₀
    else u₀
  | .inr k =>
    if hk : k ∈ liveGates c then
      if hu : u ∈ hyperEdge c (.inr ⟨k, hk⟩) then val ⟨.inr ⟨k, hk⟩, hu⟩ else u₀
    else u₀

private theorem extendLocalVal_eq {U : Type*} {c : Circuit σ n 1} (u : HyperNode c) (u₀ : U)
    (val : {w : LiveSignal c // u ∈ hyperEdge c w} → U) (w : LiveSignal c)
    (hu : u ∈ hyperEdge c w) :
    extendLocalVal u u₀ val (signalRoot w) = val ⟨w, hu⟩ := by
  rcases w with ⟨i, hi⟩ | ⟨g, hg⟩
  · simp [signalRoot, extendLocalVal, hi, hu]
  · simp [signalRoot, extendLocalVal, hg, hu]

/-- Every root read by an argument of a live gate `g` is the root of a live signal whose hyperedge
contains `.inl g`. -/
private theorem exists_signal_of_arg {c : Circuit σ n 1} (g : LiveGate c)
    {a : Fin (σ.Arity (c.program.lines g.1).op)} {r : Fin n ⊕ Fin c.size}
    (hr : rootSignal c ((c.program.lines g.1).wires a) = some r) :
    ∃ w : LiveSignal c, (.inl g : HyperNode c) ∈ hyperEdge c w ∧ signalRoot w = r :=
  ⟨liftLiveSignal r (.arg (mem_liveGates_iff.mp g.2) a hr),
    mem_hyperEdge_iff.mpr (Or.inr ⟨a, by rw [signalRoot_liftLiveSignal]; exact hr⟩),
    signalRoot_liftLiveSignal _ _⟩

/-- The root of the output wire is the root of a live signal whose hyperedge contains the output
vertex. -/
private theorem exists_signal_of_output {c : Circuit σ n 1} {r : Fin n ⊕ Fin c.size}
    (hr : rootSignal c (c.outputs 0) = some r) :
    ∃ w : LiveSignal c, (.inr () : HyperNode c) ∈ hyperEdge c w ∧ signalRoot w = r :=
  ⟨liftLiveSignal r (.output hr), mem_hyperEdge_iff.mpr (by simp [NodeInEdge, hr]),
    signalRoot_liftLiveSignal _ _⟩

open Classical in
/-- Post-layout Steiner constraint network for `c : Circuit σ n 1` along layout `π`. -/
noncomputable def hyperNetwork {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (π : Layout (HyperNode c)) :
    Network U (Fin n) (HyperNode c) (SteinerEdge c) where
  toMultigraph := steinerGraph c π
  site i := if hi : i ∈ liveInputs c then some (inputAnchor c ⟨i, hi⟩) else none
  Constraint u x α :=
    ∃ val : {w : LiveSignal c // u ∈ hyperEdge c w} → U,
      (∀ (e : SteinerEdge c) (he : (steinerGraph c π).src e = u ∨ (steinerGraph c π).tgt e = u),
        α e = val ⟨e.1, steinerGraph_end_mem he⟩) ∧
      (∀ (i : LiveInput c) (ha : inputAnchor c i = u),
        val ⟨.inl i, ha ▸ inputAnchor_mem c i⟩ = x i.1) ∧
      match u with
      | .inl g =>
        val ⟨.inr g, self_mem_hyperEdge g⟩ =
          I (c.program.lines g.1).op fun a =>
            evalFromRoots c I (extendLocalVal (.inl g) (c.eval I x 0) val)
              ((c.program.lines g.1).wires a)
      | .inr () =>
        evalFromRoots c I (extendLocalVal (.inr ()) (c.eval I x 0) val) (c.outputs 0) ∈ Acc
  constraint_congr u x x' α α' hx hα := by
    rintro ⟨val, hedge, hinp, hsem⟩
    refine ⟨val, fun e he => (hα e he).symm.trans (hedge e he), fun i ha => ?_, ?_⟩
    · rw [hinp i ha]
      exact hx i.1 (by simp [i.2, ha])
    · rcases u with g | ⟨⟩
      · dsimp only at hsem ⊢
        rw [hsem]
        congr 1
        funext a
        refine evalFromRoots_congr c I ((c.program.lines g.1).wires a) fun r hr => ?_
        obtain ⟨w, hw, rfl⟩ := exists_signal_of_arg g hr
        simp only [extendLocalVal_eq _ _ _ w hw]
      · dsimp only at hsem ⊢
        have heq : evalFromRoots c I (extendLocalVal (.inr ()) (c.eval I x 0) val) (c.outputs 0) =
            evalFromRoots c I (extendLocalVal (.inr ()) (c.eval I x' 0) val) (c.outputs 0) := by
          refine evalFromRoots_congr c I (c.outputs 0) fun r hr => ?_
          obtain ⟨w, hw, rfl⟩ := exists_signal_of_output hr
          simp only [extendLocalVal_eq _ _ _ w hw]
        rwa [← heq]

/-! ### Exact width, degree, read-count, and semantic exactness of `hyperNetwork` -/

/-- Along layout `π`, a signal `w`'s Steiner chain crosses `π.initial t` at most once, and crosses
if and only if `hyperEdge c w` straddles `π.initial t`. -/
theorem ncard_frontier_hyperNetwork {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (π : Layout (HyperNode c)) (t : ℕ) :
    ((hyperNetwork c I Acc π).frontier π t).ncard = (hyperCut c (π.initial t)).card := by
  classical
  set F := (hyperNetwork c I Acc π).frontier π t
  have hmem_F (e : SteinerEdge c) :
      e ∈ F ↔ (π (steinerNode π e.1 ⟨e.2.1, by omega⟩) : ℕ) < t ∧
        t ≤ (π (steinerNode π e.1 ⟨e.2.1 + 1, by omega⟩) : ℕ) := by
    have hlt : (π (steinerNode π e.1 ⟨e.2.1, by omega⟩) : ℕ) <
        (π (steinerNode π e.1 ⟨e.2.1 + 1, by omega⟩) : ℕ) :=
      pi_steinerNode_strictMono π e.1 (by simp [Fin.lt_def])
    simp only [F, Multigraph.mem_frontier, hyperNetwork, steinerGraph]
    omega
  have hinj : InjOn (fun e : SteinerEdge c => e.1) F := by
    rintro ⟨w₁, j₁⟩ h₁ ⟨w₂, j₂⟩ h₂ (rfl : w₁ = w₂)
    rw [hmem_F] at h₁ h₂
    dsimp only at h₁ h₂
    suffices hjeq : (j₁ : ℕ) = (j₂ : ℕ) from congrArg (Sigma.mk w₁) (Fin.ext hjeq)
    -- The chain positions increase, so two edges of one chain cannot both cross `t`.
    have hmono {a b : Fin ((hyperEdge c w₁).card - 1)} (hab : a.1 < b.1) :
        (π (steinerNode π w₁ ⟨a.1 + 1, by omega⟩) : ℕ) ≤ π (steinerNode π w₁ ⟨b.1, by omega⟩) :=
      Fin.le_iff_val_le_val.mp <|
        (pi_steinerNode_strictMono π w₁).monotone (by simp [Fin.le_def]; omega)
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt <;> have := hmono hlt <;> omega
  have himg : (fun e : SteinerEdge c => e.1) '' F =
      (hyperCut c (π.initial t) : Set (LiveSignal c)) := by
    ext w
    simp only [Set.mem_image, Finset.mem_coe, hyperCut, Finset.mem_filter, Finset.mem_univ,
      true_and, HyperedgeStraddles, Layout.mem_initial, not_lt]
    constructor
    · rintro ⟨⟨w', j⟩, heF, rfl⟩
      rw [hmem_F] at heF
      dsimp only at heF
      exact ⟨⟨_, steinerNode_mem π w' ⟨j.1, by omega⟩, heF.1⟩,
        ⟨_, steinerNode_mem π w' ⟨j.1 + 1, by omega⟩, heF.2⟩⟩
    · rintro ⟨⟨u, hu, hpu⟩, ⟨v, hv, hpv⟩⟩
      obtain ⟨ju, rfl⟩ := exists_steinerNode_eq π hu
      obtain ⟨jv, rfl⟩ := exists_steinerNode_eq π hv
      have hk := card_hyperEdge_pos c w
      have h0_lt : (π (steinerNode π w ⟨0, hk⟩) : ℕ) < t :=
        lt_of_le_of_lt (Fin.le_iff_val_le_val.mp
          ((pi_steinerNode_strictMono π w).monotone (by simp [Fin.le_def]))) hpu
      have hlast_ge : t ≤ (π (steinerNode π w ⟨(hyperEdge c w).card - 1, by omega⟩) : ℕ) :=
        hpv.trans (Fin.le_iff_val_le_val.mp
          ((pi_steinerNode_strictMono π w).monotone (by simp [Fin.le_def]; omega)))
      have hex : ∃ m : ℕ, ∃ hm : m < (hyperEdge c w).card - 1,
          (π (steinerNode π w ⟨m, by omega⟩) : ℕ) < t ∧
          t ≤ (π (steinerNode π w ⟨m + 1, by omega⟩) : ℕ) := by
        by_contra hnone
        simp only [not_exists, not_and, not_le] at hnone
        have hall : ∀ m (hm : m < (hyperEdge c w).card),
            (π (steinerNode π w ⟨m, hm⟩) : ℕ) < t := by
          intro m
          induction m with
          | zero => intro _; exact h0_lt
          | succ m ih =>
            intro hm
            have hm' : m < (hyperEdge c w).card - 1 := by omega
            exact hnone m hm' (ih (by omega))
        exact not_lt_of_ge hlast_ge (hall ((hyperEdge c w).card - 1) (by omega))
      obtain ⟨m, hm, h1, h2⟩ := hex
      exact ⟨⟨w, ⟨m, hm⟩⟩, (hmem_F ⟨w, ⟨m, hm⟩⟩).mpr ⟨h1, h2⟩, rfl⟩
  rw [← hinj.ncard_image, himg, ncard_coe_finset]

/-- **Exact width preservation:** the Steiner network width along `π` equals `hyperWidth c π`. -/
theorem width_hyperNetwork {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (π : Layout (HyperNode c)) :
    (hyperNetwork c I Acc π).width π = hyperWidth c π := by
  simp only [Multigraph.width, hyperWidth]
  exact Finset.sup_congr rfl fun t _ => ncard_frontier_hyperNetwork c I Acc π t

/-- In a circuit of fan-in at most `r`, `hyperNetwork c I Acc π` has maximum degree at most
`2 * (r + 1)` (at most `2` chain edges at `u` for each of the `≤ r + 1` signals containing `u`). -/
theorem maxDegreeLE_hyperNetwork {U : Type*} {c : Circuit σ n 1} {r : ℕ} (hfan : c.FanInAtMost r)
    (I : Interpretation σ U) (Acc : Set U) (π : Layout (HyperNode c)) :
    (hyperNetwork c I Acc π).MaxDegreeLE (2 * (r + 1)) := by
  classical
  intro u
  let S : Finset (LiveSignal c) := Finset.univ.filter fun w => u ∈ hyperEdge c w
  let tag : {e : SteinerEdge c // e ∈ (hyperNetwork c I Acc π).incidenceSet u} → S × Bool :=
    fun ⟨e, he⟩ =>
      ⟨⟨e.1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, steinerGraph_end_mem he⟩⟩,
        decide ((steinerGraph c π).src e = u)⟩
  have htag_inj : Function.Injective tag := by
    rintro ⟨⟨w₁, j₁⟩, he₁⟩ ⟨⟨w₂, j₂⟩, he₂⟩ h
    obtain ⟨hw, hb⟩ := Prod.mk.inj h
    have hw' : w₁ = w₂ := congrArg Subtype.val hw
    subst hw'
    by_cases hs₁ : (steinerGraph c π).src ⟨w₁, j₁⟩ = u
    · have hs₂ : (steinerGraph c π).src ⟨w₁, j₂⟩ = u := by simpa [tag, hs₁] using hb
      dsimp only [steinerGraph] at hs₁ hs₂
      exact Subtype.ext (congrArg (Sigma.mk w₁)
        (Fin.ext (Fin.mk.inj_iff.mp (steinerNode_injective π w₁ (hs₁.trans hs₂.symm)))))
    · have hs₂ : ¬(steinerGraph c π).src ⟨w₁, j₂⟩ = u := by simpa [tag, hs₁] using hb
      have ht₁ : (steinerGraph c π).tgt ⟨w₁, j₁⟩ = u := he₁.resolve_left hs₁
      have ht₂ : (steinerGraph c π).tgt ⟨w₁, j₂⟩ = u := he₂.resolve_left hs₂
      dsimp only [steinerGraph] at ht₁ ht₂
      exact Subtype.ext (congrArg (Sigma.mk w₁) (Fin.ext
        (Nat.succ_injective (Fin.mk.inj_iff.mp (steinerNode_injective π w₁ (ht₁.trans ht₂.symm))))))
  rw [← Nat.card_coe_set_eq]
  calc Nat.card ↥((hyperNetwork c I Acc π).incidenceSet u)
      ≤ Nat.card (S × Bool) := Nat.card_le_card_of_injective tag htag_inj
    _ = 2 * S.card := by
        rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_coe,
          Nat.card_eq_fintype_card, Fintype.card_bool, Nat.mul_comm]
    _ ≤ 2 * (r + 1) := Nat.mul_le_mul_left 2 (card_signals_at_node_le hfan u)

/-- Every vertex of `hyperNetwork c I Acc π` reads at most `max r 1` inputs. -/
theorem ncard_readAt_hyperNetwork_le {U : Type*} {c : Circuit σ n 1} {r : ℕ}
    (hfan : c.FanInAtMost r) (I : Interpretation σ U) (Acc : Set U) (π : Layout (HyperNode c))
    (u : HyperNode c) :
    ((hyperNetwork c I Acc π).readAt u).ncard ≤ max r 1 := by
  classical
  rcases u with g | ⟨⟩
  · have hmem_read (i : Fin n) (hi : i ∈ (hyperNetwork c I Acc π).readAt (.inl g)) :
        ∃ hmem : i ∈ liveInputs c, inputAnchor c ⟨i, hmem⟩ = .inl g := by
      simp only [Network.readAt, hyperNetwork, mem_ofPred_eq] at hi
      split_ifs at hi with hmem
      exact ⟨hmem, Option.some.inj hi⟩
    let f : {i : Fin n // i ∈ (hyperNetwork c I Acc π).readAt (.inl g)} →
        {w : LiveSignal c // ∃ a : Fin (σ.Arity (c.program.lines g.1).op),
          rootSignal c ((c.program.lines g.1).wires a) = some (signalRoot w)} :=
      fun ⟨i, hi⟩ =>
        ⟨.inl ⟨i, (hmem_read i hi).1⟩,
          inputAnchor_ne_self_signal ⟨i, (hmem_read i hi).1⟩ g (hmem_read i hi).2⟩
    have hf_inj : Function.Injective f := by
      rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ h
      have hval : (.inl ⟨i₁, (hmem_read i₁ h₁).1⟩ : LiveSignal c) =
          .inl ⟨i₂, (hmem_read i₂ h₂).1⟩ := congrArg Subtype.val h
      exact Subtype.ext (congrArg (Subtype.val : LiveInput c → Fin n) (Sum.inl.inj hval))
    rw [← Nat.card_coe_set_eq]
    calc Nat.card ↥((hyperNetwork c I Acc π).readAt (.inl g))
        ≤ Nat.card {w : LiveSignal c // ∃ a : Fin (σ.Arity (c.program.lines g.1).op),
            rootSignal c ((c.program.lines g.1).wires a) = some (signalRoot w)} :=
          Nat.card_le_card_of_injective f hf_inj
      _ ≤ r := by
          rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
          exact card_arg_signals_at_gate_le hfan g
      _ ≤ max r 1 := le_max_left r 1
  · rw [← Nat.card_coe_set_eq]
    have hunit_inj : Function.Injective
        (fun _ : {i : Fin n // i ∈ (hyperNetwork c I Acc π).readAt (.inr ())} => ()) := by
      rintro ⟨i₁, h₁⟩ ⟨i₂, h₂⟩ _
      refine Subtype.ext ?_
      simp only [Network.readAt, hyperNetwork, mem_ofPred_eq] at h₁ h₂
      split_ifs at h₁ with hm₁
      split_ifs at h₂ with hm₂
      simp only [Option.some.injEq] at h₁ h₂
      have he₁ := mem_hyperEdge_iff.mp (h₁ ▸ inputAnchor_mem c ⟨i₁, hm₁⟩)
      have he₂ := mem_hyperEdge_iff.mp (h₂ ▸ inputAnchor_mem c ⟨i₂, hm₂⟩)
      simp only [NodeInEdge, signalRoot] at he₁ he₂
      exact Sum.inl.inj (Option.some.inj (he₁.symm.trans he₂))
    calc Nat.card ↥((hyperNetwork c I Acc π).readAt (.inr ()))
        ≤ Nat.card Unit := Nat.card_le_card_of_injective _ hunit_inj
      _ = 1 := Nat.card_unique
      _ ≤ max r 1 := le_max_right r 1

/-- The inputs read by `hyperNetwork c I Acc π` are precisely `liveInputs c`. -/
theorem read_hyperNetwork {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (π : Layout (HyperNode c)) :
    (hyperNetwork c I Acc π).read = (liveInputs c : Set (Fin n)) := by
  ext i
  simp only [Network.read, Network.readIn, mem_univ, true_and, hyperNetwork, mem_ofPred_eq,
    Finset.mem_coe]
  by_cases hi : i ∈ liveInputs c <;> simp [hi]

/-- Canonical edge valuation carrying the true trace value of every live signal. -/
def traceSteinerVal {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U) (x : Fin n → U)
    (e : SteinerEdge c) : U :=
  trueRootVal c I x (signalRoot e.1)

/-- `traceSteinerVal c I x` satisfies `hyperNetwork c I Acc π` iff `c.eval I x 0 ∈ Acc`, and is the
*unique* satisfying edge valuation for `x`. -/
theorem satisfies_iff_eq_traceSteinerVal {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (π : Layout (HyperNode c)) (x : Fin n → U) (α : SteinerEdge c → U) :
    (hyperNetwork c I Acc π).Satisfies x α ↔
      α = traceSteinerVal c I x ∧ c.eval I x 0 ∈ Acc := by
  -- An output valuation carrying the true root values evaluates the output wire correctly.
  have hout (v : {w : LiveSignal c // (.inr () : HyperNode c) ∈ hyperEdge c w} → U)
      (hv : ∀ w hw, v ⟨w, hw⟩ = trueRootVal c I x (signalRoot w)) :
      evalFromRoots c I (extendLocalVal (.inr ()) (c.eval I x 0) v) (c.outputs 0) =
        c.eval I x 0 := by
    rw [show c.eval I x 0 = c.program.trace I x (c.outputs 0) from rfl,
      ← evalFromRoots_trueRootVal c I x (c.outputs 0)]
    refine evalFromRoots_congr c I (c.outputs 0) fun r hr => ?_
    obtain ⟨w, hw, rfl⟩ := exists_signal_of_output hr
    rw [extendLocalVal_eq (.inr ()) _ v w hw, hv]
  constructor
  · intro hsat
    choose val hedge hinp hsem using hsat
    have hconst (w : LiveSignal c) :
        ∀ (m : ℕ) (hm : m < (hyperEdge c w).card),
          val (steinerNode π w ⟨m, hm⟩) ⟨w, steinerNode_mem π w ⟨m, hm⟩⟩ =
            val (steinerNode π w ⟨0, card_hyperEdge_pos c w⟩)
              ⟨w, steinerNode_mem π w ⟨0, card_hyperEdge_pos c w⟩⟩ := by
      intro m
      induction m with
      | zero => intro _; rfl
      | succ m ih =>
        intro hm
        let e : SteinerEdge c := ⟨w, ⟨m, by omega⟩⟩
        have hsrc := hedge (steinerNode π w ⟨m, by omega⟩) e (Or.inl rfl)
        have htgt := hedge (steinerNode π w ⟨m + 1, hm⟩) e (Or.inr rfl)
        exact (htgt.symm.trans hsrc).trans (ih (by omega))
    have hall_eq (w : LiveSignal c) (u v : HyperNode c) (hu : u ∈ hyperEdge c w)
        (hv : v ∈ hyperEdge c w) : val u ⟨w, hu⟩ = val v ⟨w, hv⟩ := by
      obtain ⟨ju, rfl⟩ := exists_steinerNode_eq π hu
      obtain ⟨jv, rfl⟩ := exists_steinerNode_eq π hv
      exact (hconst w ju.1 ju.2).trans (hconst w jv.1 jv.2).symm
    have hval_inp (i : LiveInput c) (u : HyperNode c) (hu : u ∈ hyperEdge c (.inl i)) :
        val u ⟨.inl i, hu⟩ = x i.1 :=
      (hall_eq (.inl i) u (inputAnchor c i) hu (inputAnchor_mem c i)).trans
        (hinp (inputAnchor c i) i rfl)
    have hval_gate : ∀ (m : ℕ) (g : LiveGate c), (g.1 : ℕ) = m →
        ∀ (u : HyperNode c) (hu : u ∈ hyperEdge c (.inr g)),
          val u ⟨.inr g, hu⟩ = c.program.trace I x (.gate g.1) := by
      intro m
      induction m using Nat.strong_induction_on with
      | _ m ih =>
        intro g hgm u hu
        rw [hall_eq (.inr g) u (.inl g) hu (self_mem_hyperEdge g), hsem (.inl g),
          c.program.trace_gate]
        congr 1
        funext a
        rw [← evalFromRoots_trueRootVal c I x ((c.program.lines g.1).wires a)]
        refine evalFromRoots_congr c I ((c.program.lines g.1).wires a) fun r hr => ?_
        obtain ⟨w, hw, rfl⟩ := exists_signal_of_arg g hr
        rw [extendLocalVal_eq (.inl g) _ (val (.inl g)) w hw]
        rcases w with i | k
        · exact hval_inp i (.inl g) hw
        · have hlt : (k.1 : ℕ) < m := by
            have := (rootSignal_gate_rank_le c _ hr).trans_lt (wireRank_arg_lt c.program g.1 a)
            simp only [wireRank] at this
            omega
          exact ih k.1 hlt k rfl (.inl g) hw
    have hval_true (w : LiveSignal c) (u : HyperNode c) (hu : u ∈ hyperEdge c w) :
        val u ⟨w, hu⟩ = trueRootVal c I x (signalRoot w) := by
      rcases w with i | g
      · exact hval_inp i u hu
      · exact hval_gate g.1 g rfl u hu
    have hα : α = traceSteinerVal c I x := by
      funext e
      rw [hedge ((steinerGraph c π).src e) e (Or.inl rfl),
        hval_true e.1 _ (steinerGraph_src_mem π e)]
      rfl
    exact ⟨hα, hout (val (.inr ())) (fun w => hval_true w _) ▸ hsem (.inr ())⟩
  · rintro ⟨rfl, hacc⟩
    intro u
    let val : {w : LiveSignal c // u ∈ hyperEdge c w} → U :=
      fun w => trueRootVal c I x (signalRoot w.1)
    refine ⟨val, fun _ _ => rfl, fun _ _ => rfl, ?_⟩
    rcases u with g | ⟨⟩
    · dsimp only
      change c.program.trace I x (.gate g.1) = _
      rw [c.program.trace_gate]
      congr 1
      funext a
      rw [← evalFromRoots_trueRootVal c I x ((c.program.lines g.1).wires a)]
      refine evalFromRoots_congr c I ((c.program.lines g.1).wires a) fun r hr => ?_
      obtain ⟨w, hw, rfl⟩ := exists_signal_of_arg g hr
      rw [extendLocalVal_eq (.inl g) _ val w hw]
    · dsimp only
      rwa [hout val fun _ _ => rfl]

/-- Satisfying assignments of `hyperNetwork c I Acc π` are unique on every input `x`. -/
theorem satisfies_unique {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (π : Layout (HyperNode c)) {x : Fin n → U} {α β : SteinerEdge c → U}
    (hα : (hyperNetwork c I Acc π).Satisfies x α)
    (hβ : (hyperNetwork c I Acc π).Satisfies x β) : α = β :=
  ((satisfies_iff_eq_traceSteinerVal c I Acc π x α).mp hα).1.trans
    ((satisfies_iff_eq_traceSteinerVal c I Acc π x β).mp hβ).1.symm

/-- Along every layout `π`, `hyperNetwork c I Acc π` accepts `{x | c.eval I x 0 ∈ Acc}`. -/
@[simp] theorem accepted_hyperNetwork {U : Type*} (c : Circuit σ n 1) (I : Interpretation σ U)
    (Acc : Set U) (π : Layout (HyperNode c)) :
    (hyperNetwork c I Acc π).accepted = {x | c.eval I x 0 ∈ Acc} := by
  ext x
  simp only [Network.accepted, mem_ofPred_eq, satisfies_iff_eq_traceSteinerVal]
  exact ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨traceSteinerVal c I x, rfl, h⟩⟩

end Cslib.Circuits.Frontier.Hypergraph
