/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Formula
public import CslibFrontier.Computability.Circuit.Frontier.Compiler
public import CslibFrontier.Computability.Circuit.Frontier.Layouts.Basic
import CslibFrontier.Computability.Circuit.CompositionLines
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Data.Nat.Card
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Sort

/-!
# Junction-free signal frontiers and post-layout Steiner networks

`Cslib.Circuits.Frontier.Compiler.network` fixes a linear chain of degree-three fan-out junctions
for each signal before choosing a layout. Along a layout that visits consumers in another order,
several edges of one signal may cross the same cut even though all of them carry the same wire
value.

This file compiles a circuit `c` directly on its computation nodes `Node c` — its reachable inner
gates and output vertices, without fan-out junctions — and routes each non-constant signal along
its *post-layout* Steiner path for a given layout `π : Layout (Node c)`:

* **Signal supports and frontiers.** Each active signal `w : ActiveSignal c` (a reachable input or
  reachable inner gate; constant gates are omitted because their trace value is independent of the
  input) has a nonempty support `support c w ⊆ Node c` consisting of its consumers and, for a gate,
  the gate itself (`support_nonempty`). The hyperedge cut of a node set `P` is `signalFrontier c P`:
  the active signals meeting both `P` and `Pᶜ`.
* **Incidence bounds.** For fan-in at most `r`, each inner-gate node belongs to at most `r + 1`
  supports and each output node to at most one (`ncard_activeSignal_mem_support_le`), so the
  support sizes sum to at most `(r + 1) s + m` (`sum_ncard_support_le`). Every reachable inner gate
  has support size at least two (`two_le_ncard_support_gate`), and forms a two-node directed edge to
  its unique consumer node when its fan-out is one (`exists_support_eq_pair_of_isUnitGateSignal`),
  leaving at most `s + 2 g_{≥2} + m` incidences on the remaining signals at fan-in two
  (`sum_ncard_support_nonUnit_le`).
* **Post-layout Steiner network** (`steinerNetwork c I Acc π`). Sorting each signal's support in
  `π`-order links consecutive nodes by `SteinerEdge c`. Exactly one edge of `w` crosses
  `π.initial t` when `w ∈ signalFrontier c (π.initial t)` and none otherwise, so every frontier of
  the network has size `(signalFrontier c (π.initial t)).ncard`
  (`ncard_frontier_steinerGraph_eq`). Exactness and uniqueness of satisfying assignments
  (`satisfies_steinerNetwork_iff`, `accepted_steinerNetwork`) make `Network.ncard_accepted_le`,
  `Network.abs_signedCount_accepted_le`, and `Network.hide` apply directly.

## Main definitions

* `Cslib.Circuits.Frontier.Compiler.Node`, `Cslib.Circuits.Frontier.Compiler.ActiveSignal`:
  computation nodes and non-constant reachable signals.
* `Cslib.Circuits.Frontier.Compiler.support`, `Cslib.Circuits.Frontier.Compiler.signalFrontier`,
  `Cslib.Circuits.Frontier.Compiler.signalWidth`: hyperedge supports, frontiers, and layout width.
* `Cslib.Circuits.Frontier.Compiler.multiFanoutGates`,
  `Cslib.Circuits.Frontier.Compiler.multiFanoutSize`: reachable inner gates of fan-out at least two.
* `Cslib.Circuits.Circuit.gateFanout`: syntactic consumer count of gate `g` across program lines
  and outputs.
* `Cslib.Circuits.Frontier.Compiler.SteinerEdge`, `Cslib.Circuits.Frontier.Compiler.steinerGraph`,
  `Cslib.Circuits.Frontier.Compiler.steinerNetwork`: the post-layout Steiner multigraph and
  constraint network.

## Main results

* `Cslib.Circuits.Frontier.Compiler.multiFanoutSize_le_innerSize`,
  `Cslib.Circuits.Frontier.Compiler.multiFanoutSize_le_card_gateFanout`,
  `Cslib.Circuits.Frontier.Compiler.multiFanoutSize_eq_zero_of_gateFanout_le_one`,
  `Cslib.Circuits.Frontier.Compiler.multiFanoutSize_toCircuit`: upper bounds and zero criteria for
  `multiFanoutSize`, including `multiFanoutSize F.toCircuit = 0` for every formula `F`.
* `Cslib.Circuits.Frontier.Compiler.eval_splice_signalFrontier`: splicing outputs across any node
  cut along `signalFrontier`.
* `Cslib.Circuits.Frontier.Compiler.ncard_frontier_steinerGraph_eq`,
  `Cslib.Circuits.Frontier.Compiler.width_steinerGraph_eq`: network frontiers equal signal
  frontiers.
* `Cslib.Circuits.Frontier.Compiler.satisfies_steinerNetwork_iff`,
  `Cslib.Circuits.Frontier.Compiler.accepted_steinerNetwork`,
  `Cslib.Circuits.Frontier.Compiler.accepted_steinerNetwork_single`: exactness and uniqueness.
-/

public section

namespace Cslib.Circuits.Frontier.Compiler

open Set

/-! ### Nodes, active signals, and hyperedge supports -/

section Supports

variable {σ : Signature} {n m : ℕ}

/-- A computation node of a circuit: a reachable inner gate or an output vertex. Constant gates
(arity zero) and fan-out junctions have no node. -/
inductive Node (c : Circuit σ n m) : Type
  /-- The node of a reachable inner gate. -/
  | gate (g : InnerGate c)
  /-- The node of an output. -/
  | output (o : Fin m)
  deriving DecidableEq

/-- Computation nodes are reachable inner gates and outputs. -/
@[expose] def Node.equiv (c : Circuit σ n m) : Node c ≃ InnerGate c ⊕ Fin m where
  toFun
    | .gate g => .inl g
    | .output o => .inr o
  invFun
    | .inl g => .gate g
    | .inr o => .output o
  left_inv u := by cases u <;> rfl
  right_inv s := by rcases s with g | o <;> rfl

instance (c : Circuit σ n m) : Finite (Node c) :=
  .of_equiv _ (Node.equiv c).symm

/-- Topological rank of a computation node: gate line index for inner gates, and `c.size + o` for
outputs. -/
@[expose] def Node.rank {c : Circuit σ n m} : Node c → ℕ
  | .gate g => g.val.val
  | .output o => c.size + o.val

/-- A circuit has at most `c.innerSize + m` computation nodes. -/
theorem card_node_le (c : Circuit σ n m) : Nat.card (Node c) ≤ c.innerSize + m := by
  rw [Nat.card_congr (Node.equiv c), Nat.card_sum, Nat.card_eq_fintype_card (α := Fin m),
    Fintype.card_fin]
  exact Nat.add_le_add_right (card_innerGate_le (c := c)) m

/-- A non-constant reachable signal of a circuit: a reachable input or a reachable inner gate. -/
inductive ActiveSignal (c : Circuit σ n m) : Type
  /-- A reachable input wire. -/
  | input (i : Fin n) (hi : Reach c (.input i))
  /-- A reachable inner gate. -/
  | gate (g : InnerGate c)
  deriving DecidableEq

variable {c : Circuit σ n m}

/-- The underlying wire of an active signal. -/
@[expose] def ActiveSignal.wire : ActiveSignal c → Wire n c.size
  | .input i _ => .input i
  | .gate ⟨g, _, _⟩ => .gate g

/-- Every active signal is reachable. -/
theorem ActiveSignal.reach : (w : ActiveSignal c) → Reach c w.wire
  | .input _ hi => hi
  | .gate ⟨_, hg, _⟩ => hg

/-- View an active signal as a `Signal`. -/
@[expose] def ActiveSignal.toSignal (w : ActiveSignal c) : Signal c :=
  ⟨w.wire, w.reach⟩

theorem ActiveSignal.toSignal_injective : Function.Injective (ActiveSignal.toSignal (c := c)) := by
  intro w₁ w₂ h
  have hw : w₁.wire = w₂.wire := congrArg Subtype.val h
  cases w₁ with
  | input i₁ hi₁ =>
    cases w₂ with
    | input i₂ hi₂ =>
      cases Wire.input.inj hw
      rfl
    | gate g₂ => cases hw
  | gate g₁ =>
    cases w₂ with
    | input i₂ hi₂ => cases hw
    | gate g₂ =>
      obtain ⟨idx₁, r₁, a₁⟩ := g₁
      obtain ⟨idx₂, r₂, a₂⟩ := g₂
      cases Wire.gate.inj hw
      rfl

/-- Active signals correspond to reachable inputs and reachable inner gates. -/
@[expose] def ActiveSignal.equiv (c : Circuit σ n m) :
    ActiveSignal c ≃ {i : Fin n // Reach c (.input i)} ⊕ InnerGate c where
  toFun
    | .input i hi => .inl ⟨i, hi⟩
    | .gate g => .inr g
  invFun
    | .inl ⟨i, hi⟩ => .input i hi
    | .inr g => .gate g
  left_inv w := by cases w <;> rfl
  right_inv s := by rcases s with ⟨i, hi⟩ | g <;> rfl

instance (c : Circuit σ n m) : Finite (ActiveSignal c) :=
  .of_equiv _ (ActiveSignal.equiv c).symm

/-- Every argument slot belongs to a gate of positive arity, hence an `InnerGate`. -/
@[expose] def Slot.innerGate : Slot c → InnerGate c
  | ⟨⟨g, a⟩, hg⟩ => ⟨g, hg, (Fin.pos a).ne'⟩

/-- The computation node that owns a consumer: the gate of an argument slot, or the output node. -/
@[expose] def ownerNode : Consumer c → Node c
  | .inl a => .gate a.innerGate
  | .inr o => .output o

/-- The computation nodes that consume a signal. -/
@[expose] def consumerNodes (c : Circuit σ n m) (w : Signal c) : Set (Node c) :=
  ownerNode '' {t : Consumer c | consumed t = w}

variable (c) in
/-- **The hyperedge support** of an active signal on `Node c`: its consumer nodes, together with
its own gate node when it is an inner gate. -/
@[expose] def support : ActiveSignal c → Set (Node c)
  | .input i hi => consumerNodes c ⟨.input i, hi⟩
  | .gate g => insert (.gate g) (consumerNodes c (.gate g : ActiveSignal c).toSignal)

/-- Every signal has at least one consumer node. -/
theorem consumerNodes_nonempty (w : Signal c) : (consumerNodes c w).Nonempty := by
  have hpos := fanout_pos (c := c) w
  obtain ⟨⟨t, ht⟩⟩ := Nat.card_pos_iff.mp hpos
  exact ⟨ownerNode t, t, ht, rfl⟩

/-- Every reachable inner gate belongs to its own support. -/
theorem gate_mem_support (g : InnerGate c) : Node.gate g ∈ support c (.gate g) :=
  mem_insert _ _

/-- Every active signal has nonempty support. -/
theorem support_nonempty (w : ActiveSignal c) : (support c w).Nonempty := by
  cases w with
  | input i hi => exact consumerNodes_nonempty ⟨.input i, hi⟩
  | gate g => exact insert_nonempty _ _

/-- Every consumer of an inner gate has strictly larger `Node.rank` than that gate, by DAG
acyclicity. -/
private theorem rank_gate_lt_ownerNode {g : InnerGate c} {t : Consumer c}
    (ht : consumed t = (.gate g : ActiveSignal c).toSignal) :
    (Node.gate g).rank < (ownerNode t).rank := by
  rcases t with ⟨⟨h, a⟩, hh⟩ | o
  · have hw : (c.program.lines h).wires a = .gate g.val := congrArg Subtype.val ht
    exact Fin.lt_def.mp (c.program.lt_of_lines_wires_eq_gate h a g.val hw)
  · exact lt_of_lt_of_le g.val.isLt (Nat.le_add_right c.size o.val)

/-- No consumer of a gate wire is owned by that gate itself. -/
private theorem ownerNode_ne_gate {g : InnerGate c} {t : Consumer c}
    (ht : consumed t = (.gate g : ActiveSignal c).toSignal) : ownerNode t ≠ .gate g := by
  intro heq
  have hlt := rank_gate_lt_ownerNode ht
  rw [heq] at hlt
  exact lt_irrefl _ hlt

/-- Every reachable inner gate has at least two nodes in its support: itself and a consumer. -/
theorem two_le_ncard_support_gate (g : InnerGate c) :
    2 ≤ (support c (.gate g)).ncard := by
  obtain ⟨u, t, ht, rfl⟩ := consumerNodes_nonempty ((.gate g : ActiveSignal c).toSignal)
  have hne : (.gate g : Node c) ≠ ownerNode t := (ownerNode_ne_gate ht).symm
  have hsub : ({Node.gate g, ownerNode t} : Set (Node c)) ⊆ support c (.gate g) :=
    pair_subset_iff.mpr ⟨mem_insert _ _, mem_insert_of_mem _ ⟨t, ht, rfl⟩⟩
  calc 2 = ({Node.gate g, ownerNode t} : Set (Node c)).ncard := (ncard_pair hne).symm
    _ ≤ (support c (.gate g)).ncard := ncard_le_ncard hsub (toFinite _)

/-- A signal has at most `fanout c w` consumer nodes. -/
theorem ncard_consumerNodes_le (w : Signal c) : (consumerNodes c w).ncard ≤ fanout c w := by
  calc (consumerNodes c w).ncard
      ≤ {t : Consumer c | consumed t = w}.ncard := ncard_image_le (toFinite _)
    _ = fanout c w := Nat.card_coe_set_eq _

/-- If an inner gate has fan-out one, its support has size exactly two. -/
theorem ncard_support_gate_eq_two {g : InnerGate c}
    (h1 : fanout c ((.gate g : ActiveSignal c).toSignal) = 1) :
    (support c (.gate g)).ncard = 2 := by
  have hlo := two_le_ncard_support_gate g
  have hcons := ncard_consumerNodes_le ((.gate g : ActiveSignal c).toSignal)
  have hhi : (support c (.gate g)).ncard ≤ 2 :=
    (ncard_insert_le _ _).trans (by omega)
  omega

/-- Each output node belongs to the support of at most one active signal. -/
theorem ncard_activeSignal_mem_support_output_le (o : Fin m) :
    {w : ActiveSignal c | Node.output o ∈ support c w}.ncard ≤ 1 := by
  refine (ncard_le_one (toFinite _)).mpr fun w₁ hw₁ w₂ hw₂ => ?_
  have hmem : ∀ {w : ActiveSignal c}, Node.output o ∈ support c w →
      w.toSignal = consumed (.inr o) := by
    intro w hw
    cases w with
    | input i hi =>
      obtain ⟨t, ht, ho⟩ := hw
      rcases t with a | o'
      · cases ho
      · cases Node.output.inj ho
        exact ht.symm
    | gate g =>
      rcases mem_insert_iff.mp hw with h | ⟨t, ht, ho⟩
      · cases h
      · rcases t with a | o'
        · cases ho
        · cases Node.output.inj ho
          exact ht.symm
  exact ActiveSignal.toSignal_injective ((hmem hw₁).trans (hmem hw₂).symm)

/-- When gates have fan-in at most `r`, each inner-gate node belongs to at most `r + 1` supports. -/
theorem ncard_activeSignal_mem_support_gate_le {r : ℕ} (hfan : c.FanInAtMost r)
    (g : InnerGate c) :
    {w : ActiveSignal c | Node.gate g ∈ support c w}.ncard ≤ r + 1 := by
  classical
  let slotSignal : Fin (σ.Arity (c.program.lines g.val).op) → Signal c :=
    fun a => consumed (.inl ⟨⟨g.val, a⟩, g.property.1⟩)
  have hsub : ActiveSignal.toSignal '' {w : ActiveSignal c | Node.gate g ∈ support c w} ⊆
      insert ((.gate g : ActiveSignal c).toSignal) (range slotSignal) := by
    rintro _ ⟨w, hw, rfl⟩
    cases w with
    | input i hi =>
      obtain ⟨t, ht, ho⟩ := hw
      rcases t with ⟨⟨h, a⟩, hh⟩ | o
      · have hgh : h = g.val := congrArg Subtype.val (Node.gate.inj ho)
        subst hgh
        exact Or.inr ⟨a, ht⟩
      · cases ho
    | gate g' =>
      rcases mem_insert_iff.mp hw with h | ⟨t, ht, ho⟩
      · cases Node.gate.inj h
        exact Or.inl rfl
      · rcases t with ⟨⟨h, a⟩, hh⟩ | o
        · have hgh : h = g.val := congrArg Subtype.val (Node.gate.inj ho)
          subst hgh
          exact Or.inr ⟨a, ht⟩
        · cases ho
  calc {w : ActiveSignal c | Node.gate g ∈ support c w}.ncard
      = (ActiveSignal.toSignal '' {w : ActiveSignal c | Node.gate g ∈ support c w}).ncard :=
        (ncard_image_of_injective _ ActiveSignal.toSignal_injective).symm
    _ ≤ (insert ((.gate g : ActiveSignal c).toSignal) (range slotSignal)).ncard :=
        ncard_le_ncard hsub (toFinite _)
    _ ≤ (range slotSignal).ncard + 1 := ncard_insert_le _ _
    _ ≤ σ.Arity (c.program.lines g.val).op + 1 := by
        have hcard : (range slotSignal).ncard ≤
            Nat.card (Fin (σ.Arity (c.program.lines g.val).op)) := by
          rw [← image_univ]
          exact (ncard_image_le (toFinite _)).trans_eq (ncard_univ _)
        rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
        exact Nat.add_le_add_right hcard 1
    _ ≤ r + 1 := Nat.add_le_add_right (Program.fanInAtMost_iff.mp hfan g.val) 1

/-- Every node belongs to the supports of at most `r + 1` active signals. -/
theorem ncard_activeSignal_mem_support_le {r : ℕ} (hfan : c.FanInAtMost r) (u : Node c) :
    {w : ActiveSignal c | u ∈ support c w}.ncard ≤ r + 1 := by
  cases u with
  | gate g => exact ncard_activeSignal_mem_support_gate_le hfan g
  | output o => exact (ncard_activeSignal_mem_support_output_le o).trans (Nat.le_add_left 1 r)

/-- At most `max r 1` *other* inner-gate nodes contain `u` in their support. -/
theorem ncard_gate_mem_support_ne_le {r : ℕ} (hfan : c.FanInAtMost r) (u : Node c) :
    {g : InnerGate c | u ∈ support c (.gate g) ∧ Node.gate g ≠ u}.ncard ≤ max r 1 := by
  cases u with
  | output o =>
    calc {g : InnerGate c | Node.output o ∈ support c (.gate g) ∧ Node.gate g ≠ .output o}.ncard
        = (ActiveSignal.gate '' {g : InnerGate c |
            Node.output o ∈ support c (.gate g) ∧ Node.gate g ≠ .output o}).ncard :=
          (ncard_image_of_injective _ fun _ _ h => ActiveSignal.gate.inj h).symm
      _ ≤ {w : ActiveSignal c | Node.output o ∈ support c w}.ncard :=
          ncard_le_ncard (by rintro _ ⟨g, hg, rfl⟩; exact hg.1) (toFinite _)
      _ ≤ max r 1 := (ncard_activeSignal_mem_support_output_le o).trans (le_max_right r 1)
  | gate h =>
    have hmem : ActiveSignal.gate h ∈ {w : ActiveSignal c | Node.gate h ∈ support c w} :=
      mem_insert _ _
    have hdiff := ncard_sdiff_singleton_of_mem hmem
    have htot := ncard_activeSignal_mem_support_gate_le hfan h
    have hsub : ActiveSignal.gate '' {g : InnerGate c |
        Node.gate h ∈ support c (.gate g) ∧ Node.gate g ≠ .gate h} ⊆
        {w : ActiveSignal c | Node.gate h ∈ support c w} \ {.gate h} := by
      rintro _ ⟨g, ⟨hg, hne⟩, rfl⟩
      exact ⟨hg, fun heq => hne (congrArg Node.gate (ActiveSignal.gate.inj heq))⟩
    calc {g : InnerGate c | Node.gate h ∈ support c (.gate g) ∧ Node.gate g ≠ .gate h}.ncard
        = (ActiveSignal.gate '' {g : InnerGate c |
            Node.gate h ∈ support c (.gate g) ∧ Node.gate g ≠ .gate h}).ncard :=
          (ncard_image_of_injective _ fun _ _ h' => ActiveSignal.gate.inj h').symm
      _ ≤ ({w : ActiveSignal c | Node.gate h ∈ support c w} \ {.gate h}).ncard :=
          ncard_le_ncard hsub (toFinite _)
      _ ≤ max r 1 := by omega

/-- **Total support incidences.** By double counting across `Node c`, the support sizes of all
active signals sum to at most `(r + 1) · |InnerGate c| + m`. -/
theorem sum_ncard_support_le_card_innerGate [Fintype (ActiveSignal c)] {r : ℕ}
    (hfan : c.FanInAtMost r) :
    ∑ w : ActiveSignal c, (support c w).ncard ≤
      (r + 1) * Nat.card (InnerGate c) + m := by
  classical
  have := Fintype.ofFinite (Node c)
  have := Fintype.ofFinite (InnerGate c)
  have hdouble : ∑ w : ActiveSignal c, (support c w).ncard =
      ∑ u : Node c, {w : ActiveSignal c | u ∈ support c w}.ncard := by
    have hL (w : ActiveSignal c) : (support c w).ncard =
        ∑ u : Node c, if u ∈ support c w then 1 else 0 := by
      rw [Finset.sum_boole, ← ncard_coe_finset]
      congr 1
      ext u
      simp
    have hR (u : Node c) : {w : ActiveSignal c | u ∈ support c w}.ncard =
        ∑ w : ActiveSignal c, if u ∈ support c w then 1 else 0 := by
      rw [Finset.sum_boole, ← ncard_coe_finset]
      congr 1
      ext w
      simp
    simp_rw [hL, hR]
    exact Finset.sum_comm
  rw [hdouble, ← (Node.equiv c).symm.sum_comp (fun u => {w | u ∈ support c w}.ncard),
    Fintype.sum_sum_type]
  have hG : ∑ g : InnerGate c, {w : ActiveSignal c | Node.gate g ∈ support c w}.ncard ≤
      (r + 1) * Nat.card (InnerGate c) := by
    calc ∑ g : InnerGate c, {w : ActiveSignal c | Node.gate g ∈ support c w}.ncard
        ≤ ∑ _g : InnerGate c, (r + 1) :=
          Finset.sum_le_sum fun g _ => ncard_activeSignal_mem_support_gate_le hfan g
      _ = (r + 1) * Nat.card (InnerGate c) := by
          rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_comm, Nat.card_eq_fintype_card]
  have hO : ∑ o : Fin m, {w : ActiveSignal c | Node.output o ∈ support c w}.ncard ≤ m := by
    calc ∑ o : Fin m, {w : ActiveSignal c | Node.output o ∈ support c w}.ncard
        ≤ ∑ _o : Fin m, 1 :=
          Finset.sum_le_sum fun o _ => ncard_activeSignal_mem_support_output_le o
      _ = m := by simp
  exact Nat.add_le_add hG hO

/-- The support sizes of all active signals sum to at most `(r + 1) · c.innerSize + m`. -/
theorem sum_ncard_support_le [Fintype (ActiveSignal c)] {r : ℕ} (hfan : c.FanInAtMost r) :
    ∑ w : ActiveSignal c, (support c w).ncard ≤ (r + 1) * c.innerSize + m :=
  (sum_ncard_support_le_card_innerGate hfan).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_left (r + 1) (card_innerGate_le (c := c))) m)

variable (c) in
/-- Reachable inner gates whose wire has fan-out at least two. -/
@[expose] def multiFanoutGates : Set (InnerGate c) :=
  {g : InnerGate c | 2 ≤ fanout c ((.gate g : ActiveSignal c).toSignal)}

variable (c) in
/-- The number of reachable inner gates of fan-out at least two (`g_{≥2}`). -/
@[expose] noncomputable def multiFanoutSize : ℕ :=
  (multiFanoutGates c).ncard

/-- At most `c.innerSize` reachable inner gates have fan-out at least two. -/
theorem multiFanoutSize_le_innerSize (c : Circuit σ n m) :
    multiFanoutSize c ≤ c.innerSize :=
  (ncard_le_card (multiFanoutGates c)).trans card_innerGate_le

/-- Syntactic consumer count of gate `g` in `c`: the number of argument slots across all program
lines reading `.gate g`, plus the number of circuit outputs equal to `.gate g`. -/
@[expose] def _root_.Cslib.Circuits.Circuit.gateFanout {σ : Signature} {n m : ℕ}
    (c : Circuit σ n m) (g : Fin c.size) : ℕ :=
  (∑ h : Fin c.size,
      (Finset.univ.filter fun a => (c.program.lines h).wires a = .gate g).card) +
    (Finset.univ.filter fun o : Fin m => c.outputs o = .gate g).card

private def consumerToSyntactic (g : InnerGate c) :
    {t : Consumer c // consumed t = (.gate g : ActiveSignal c).toSignal} →
      (Σ h : Fin c.size, {a : Fin (σ.Arity (c.program.lines h).op) //
        (c.program.lines h).wires a = .gate g.val}) ⊕
      {o : Fin m // c.outputs o = .gate g.val}
  | ⟨.inl ⟨⟨h, a⟩, _⟩, ht⟩ => .inl ⟨h, ⟨a, congrArg Subtype.val ht⟩⟩
  | ⟨.inr o, ht⟩ => .inr ⟨o, congrArg Subtype.val ht⟩

private theorem consumerToSyntactic_injective (g : InnerGate c) :
    Function.Injective (consumerToSyntactic (c := c) g) := by
  rintro ⟨⟨⟨h₁, a₁⟩, _⟩ | o₁, ht₁⟩ ⟨⟨⟨h₂, a₂⟩, _⟩ | o₂, ht₂⟩ heq
  · obtain ⟨rfl, ha⟩ := Sigma.mk.inj (Sum.inl.inj heq)
    obtain rfl := Subtype.mk.inj (eq_of_heq ha)
    rfl
  · cases heq
  · cases heq
  · obtain rfl := Subtype.mk.inj (Sum.inr.inj heq)
    rfl

/-- Semantic consumer fan-out of an inner gate is bounded by its syntactic `gateFanout`. -/
theorem fanout_gate_le_gateFanout (g : InnerGate c) :
    fanout c ((.gate g : ActiveSignal c).toSignal) ≤ c.gateFanout g.val := by
  calc fanout c ((.gate g : ActiveSignal c).toSignal)
      ≤ Nat.card ((Σ h : Fin c.size, {a : Fin (σ.Arity (c.program.lines h).op) //
          (c.program.lines h).wires a = .gate g.val}) ⊕
          {o : Fin m // c.outputs o = .gate g.val}) :=
        Nat.card_le_card_of_injective _ (consumerToSyntactic_injective g)
    _ = c.gateFanout g.val := by
        rw [Nat.card_eq_fintype_card, Fintype.card_sum, Fintype.card_sigma]
        simp only [Fintype.card_subtype, Circuit.gateFanout]

/-- `multiFanoutSize c` is at most the number of gates with `2 ≤ c.gateFanout g`. -/
theorem multiFanoutSize_le_card_gateFanout (c : Circuit σ n m) :
    multiFanoutSize c ≤ (Finset.univ.filter fun g : Fin c.size => 2 ≤ c.gateFanout g).card := by
  rw [multiFanoutSize, ← Nat.card_coe_set_eq, ← Fintype.card_coe, ← Nat.card_eq_fintype_card]
  exact Nat.card_le_card_of_injective
    (fun g => ⟨g.val.val, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, g.property.trans (fanout_gate_le_gateFanout g.val)⟩⟩)
    fun g₁ g₂ h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :))

/-- If every gate of `c` has syntactic `gateFanout` at most one, `multiFanoutSize c = 0`. -/
theorem multiFanoutSize_eq_zero_of_gateFanout_le_one {c : Circuit σ n m}
    (h : ∀ g : Fin c.size, c.gateFanout g ≤ 1) : multiFanoutSize c = 0 := by
  refine Nat.eq_zero_of_le_zero ((multiFanoutSize_le_card_gateFanout c).trans ?_)
  rw [Nat.le_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  exact fun g _ => not_le_of_gt (lt_of_le_of_lt (h g) one_lt_two)

private theorem card_filter_eq_of_iff {α : Type*} [Fintype α] {p q : α → Prop}
    [DecidablePred p] [DecidablePred q] (h : ∀ a, p a ↔ q a) :
    (Finset.univ.filter p).card = (Finset.univ.filter q).card := by
  congr 1
  ext a
  exact ⟨fun ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, (h a).mp (Finset.mem_filter.mp ha).2⟩,
    fun ha => Finset.mem_filter.mpr ⟨Finset.mem_univ a, (h a).mpr (Finset.mem_filter.mp ha).2⟩⟩

private theorem card_filter_wire_emb_eq {s' : ℕ} (c : Circuit σ n m)
    (f : Wire n c.size → Wire n s') {g' : Fin s'} (g : Fin c.size)
    (hf : ∀ w, f w = .gate g' ↔ w = .gate g) :
    (∑ h : Fin c.size,
        (Finset.univ.filter fun a => f ((c.program.lines h).wires a) = .gate g').card) +
      (Finset.univ.filter fun o : Fin m => f (c.outputs o) = .gate g').card =
    c.gateFanout g := by
  simp only [Circuit.gateFanout,
    fun h => card_filter_eq_of_iff fun a => hf ((c.program.lines h).wires a),
    card_filter_eq_of_iff fun o => hf (c.outputs o)]

private theorem card_filter_wire_emb_eq_zero {s' : ℕ} (c : Circuit σ n m)
    (f : Wire n c.size → Wire n s') {g' : Fin s'} (hf : ∀ w, f w ≠ .gate g') :
    (∑ h : Fin c.size,
        (Finset.univ.filter fun a => f ((c.program.lines h).wires a) = .gate g').card) +
      (Finset.univ.filter fun o : Fin m => f (c.outputs o) = .gate g').card = 0 := by
  have hl (h : Fin c.size) :
      (Finset.univ.filter fun a => f ((c.program.lines h).wires a) = .gate g').card = 0 :=
    Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun a _ => hf _)
  have ho : (Finset.univ.filter fun o : Fin m => f (c.outputs o) = .gate g').card = 0 :=
    Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun o _ => hf _)
  simp only [hl, ho, Finset.sum_const_zero, add_zero]

private theorem gateFanout_append_split {m₁ m₂ : ℕ} (c₁ : Circuit σ n m₁)
    (c₂ : Circuit σ n m₂) (g' : Fin (c₁.size + c₂.size)) :
    (c₁.append c₂).gateFanout g' =
      ((∑ h : Fin c₁.size,
          (Finset.univ.filter fun a =>
            ((c₁.program.lines h).wires a).castAdd c₂.size = .gate g').card) +
        (Finset.univ.filter fun o : Fin m₁ =>
          (c₁.outputs o).castAdd c₂.size = .gate g').card) +
      ((∑ h : Fin c₂.size,
          (Finset.univ.filter fun a =>
            Program.appendedWire (Wire.input : Fin n → Wire n c₁.size)
              ((c₂.program.lines h).wires a) = .gate g').card) +
        (Finset.univ.filter fun o : Fin m₂ =>
          Program.appendedWire (Wire.input : Fin n → Wire n c₁.size)
            (c₂.outputs o) = .gate g').card) := by
  let d : Circuit σ n (m₁ + m₂) :=
    ⟨c₁.program.append Wire.input c₂.program,
      Fin.append (Wire.castAdd c₂.size ∘ c₁.outputs)
        (Program.appendedWire Wire.input ∘ c₂.outputs)⟩
  change d.gateFanout g' = _
  have hlines :
      (∑ h : Fin (c₁.size + c₂.size),
          (Finset.univ.filter fun a => (d.program.lines h).wires a = .gate g').card) =
        (∑ h : Fin c₁.size,
          (Finset.univ.filter fun a =>
            ((c₁.program.lines h).wires a).castAdd c₂.size = .gate g').card) +
        (∑ h : Fin c₂.size,
          (Finset.univ.filter fun a =>
            Program.appendedWire (Wire.input : Fin n → Wire n c₁.size)
              ((c₂.program.lines h).wires a) = .gate g').card) := by
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    congr 1
    · refine Fintype.sum_congr _ _ fun h => ?_
      change (Finset.univ.filter fun a =>
        ((c₁.program.append Wire.input c₂.program).lines (Fin.castAdd c₂.size h)).wires a =
          .gate g').card = _
      rw [Program.lines_append_castAdd]
      rfl
    · refine Fintype.sum_congr _ _ fun h => ?_
      change (Finset.univ.filter fun a =>
        ((c₁.program.append Wire.input c₂.program).lines (Fin.natAdd c₁.size h)).wires a =
          .gate g').card = _
      rw [Program.lines_append_natAdd]
      rfl
  have houts :
      (Finset.univ.filter fun o : Fin (m₁ + m₂) => d.outputs o = .gate g').card =
        (Finset.univ.filter fun o : Fin m₁ =>
          (c₁.outputs o).castAdd c₂.size = .gate g').card +
        (Finset.univ.filter fun o : Fin m₂ =>
          Program.appendedWire (Wire.input : Fin n → Wire n c₁.size)
            (c₂.outputs o) = .gate g').card := by
    simp only [Finset.card_filter]
    rw [← Equiv.sum_comp finSumFinEquiv, Fintype.sum_sum_type]
    congr 1
    · refine Fintype.sum_congr _ _ fun o => ?_
      rw [show d.outputs (finSumFinEquiv (.inl o)) = (c₁.outputs o).castAdd c₂.size from
        Fin.append_left _ _ o]
    · refine Fintype.sum_congr _ _ fun o => ?_
      rw [show d.outputs (finSumFinEquiv (.inr o)) =
        Program.appendedWire Wire.input (c₂.outputs o) from Fin.append_right _ _ o]
  dsimp only [Circuit.gateFanout]
  rw [hlines, houts]
  omega

private theorem gateFanout_append_castAdd {m₁ m₂ : ℕ} (c₁ : Circuit σ n m₁)
    (c₂ : Circuit σ n m₂) (g : Fin c₁.size) :
    (c₁.append c₂).gateFanout (Fin.castAdd c₂.size g) = c₁.gateFanout g := by
  rw [gateFanout_append_split,
    card_filter_wire_emb_eq c₁ (Wire.castAdd c₂.size) g
      (fun w => by cases w <;> simp [Fin.ext_iff]),
    card_filter_wire_emb_eq_zero c₂ (Program.appendedWire Wire.input) (fun w h => by
      cases w with
      | input _ => cases h
      | gate _ =>
        have := congrArg Fin.val (Wire.gate.inj h)
        dsimp at this
        omega),
    add_zero]

private theorem gateFanout_append_natAdd {m₁ m₂ : ℕ} (c₁ : Circuit σ n m₁)
    (c₂ : Circuit σ n m₂) (g : Fin c₂.size) :
    (c₁.append c₂).gateFanout (Fin.natAdd c₁.size g) = c₂.gateFanout g := by
  rw [gateFanout_append_split,
    card_filter_wire_emb_eq_zero c₁ (Wire.castAdd c₂.size) (fun w h => by
      cases w with
      | input _ => cases h
      | gate _ =>
        have := congrArg Fin.val (Wire.gate.inj h)
        dsimp at this
        omega),
    card_filter_wire_emb_eq c₂ (Program.appendedWire Wire.input) g
      (fun w => by cases w <;> simp [Fin.ext_iff]),
    zero_add]

private theorem gateFanout_append_le_one {m₁ m₂ : ℕ} {c₁ : Circuit σ n m₁}
    {c₂ : Circuit σ n m₂} (hc₁ : ∀ g, c₁.gateFanout g ≤ 1) (hc₂ : ∀ g, c₂.gateFanout g ≤ 1) :
    ∀ g : Fin (c₁.append c₂).size, (c₁.append c₂).gateFanout g ≤ 1 :=
  Fin.addCases (m := c₁.size) (n := c₂.size)
    (fun g => (gateFanout_append_castAdd c₁ c₂ g).trans_le (hc₁ g))
    (fun g => (gateFanout_append_natAdd c₁ c₂ g).trans_le (hc₂ g))

private theorem gateFanout_pi_le_one {m : ℕ} (cs : Fin m → Circuit σ n 1)
    (hcs : ∀ j g, (cs j).gateFanout g ≤ 1) (g : Fin (Circuit.pi cs).size) :
    (Circuit.pi cs).gateFanout g ≤ 1 := by
  induction m with
  | zero => exact g.elim0
  | succ m ih =>
    exact gateFanout_append_le_one (ih (fun i => cs i.castSucc) fun i g => hcs i.castSucc g)
      (hcs (Fin.last m)) g

private theorem gateFanout_oneGate_comp_le_one (op : σ.Op) (c : Circuit σ n (σ.Arity op))
    (hc : ∀ g, c.gateFanout g ≤ 1) (g : Fin ((Circuit.oneGate op id).comp c).size) :
    ((Circuit.oneGate op id).comp c).gateFanout g ≤ 1 := by
  let line : Line σ n c.size :=
    Line.mapWires ⟨op, Wire.input⟩ (Program.appendedWire (g₂ := 0) c.outputs)
  let d : Circuit σ n 1 :=
    ⟨c.program.gate line, Program.appendedWire c.outputs ∘ fun _ => Wire.gate 0⟩
  have hout_eq (o : Fin 1) : d.outputs o = .gate (Fin.last c.size) := by
    change Program.appendedWire c.outputs (Wire.gate 0) = .gate (Fin.last c.size)
    apply congrArg Wire.gate
    ext
    exact Nat.add_zero c.size
  have hd : (Circuit.oneGate op id).comp c = d := rfl
  revert g
  rw [hd]
  intro (g : Fin (c.size + 1))
  induction g using Fin.lastCases with
  | last =>
    have hlines :
        (∑ h : Fin (c.size + 1),
            (Finset.univ.filter fun a =>
              (d.program.lines h).wires a = .gate (Fin.last c.size)).card) = 0 := by
      exact Finset.sum_eq_zero fun h _ => Finset.card_eq_zero.2 <| Finset.filter_eq_empty_iff.2
        fun a _ heq => (Fin.le_last h).not_gt (d.program.lt_of_lines_wires_eq_gate h a _ heq)
    dsimp only [Circuit.gateFanout]
    rw [hlines, zero_add]
    exact (Finset.card_filter_le _ _).trans_eq (by simp)
  | cast g =>
    have hcast_iff (w : Wire n c.size) :
        Wire.Renaming.castSucc w = .gate g.castSucc ↔ w = .gate g := by
      cases w with
      | input i => simp [Wire.Renaming.castSucc]
      | gate j => simp [Wire.Renaming.castSucc, Fin.castSucc_inj]
    have hlines :
        (∑ h : Fin (c.size + 1),
            (Finset.univ.filter fun a =>
              (d.program.lines h).wires a = .gate g.castSucc).card) = c.gateFanout g := by
      change (∑ h : Fin (c.size + 1),
          (Finset.univ.filter fun a =>
            ((c.program.gate line).lines h).wires a = .gate g.castSucc).card) = _
      rw [Fin.sum_univ_castSucc]
      have hprev (h : Fin c.size) :
          (Finset.univ.filter fun a =>
              ((c.program.gate line).lines h.castSucc).wires a = .gate g.castSucc).card =
            (Finset.univ.filter fun a =>
              Wire.Renaming.castSucc ((c.program.lines h).wires a) = .gate g.castSucc).card := by
        rw [Program.lines_gate_castSucc]
        rfl
      have hlast :
          (Finset.univ.filter fun a =>
              ((c.program.gate line).lines (Fin.last c.size)).wires a = .gate g.castSucc).card =
            (Finset.univ.filter fun a =>
              Wire.Renaming.castSucc (c.outputs a) = .gate g.castSucc).card := by
        rw [Program.lines_gate_last]
        refine card_filter_eq_of_iff fun a => ?_
        change Wire.Renaming.castSucc ((c.outputs a).castAdd 0) = _ ↔ _
        cases c.outputs a <;> rfl
      simp only [hprev, hlast]
      exact card_filter_wire_emb_eq c Wire.Renaming.castSucc g hcast_iff
    have hout :
        (Finset.univ.filter fun o : Fin 1 => d.outputs o = .gate g.castSucc).card = 0 :=
      Finset.card_eq_zero.2 <| Finset.filter_eq_empty_iff.2 fun o _ heq =>
        Fin.castSucc_ne_last g (Wire.gate.inj ((hout_eq o).symm.trans heq)).symm
    dsimp only [Circuit.gateFanout]
    rw [hlines, hout, add_zero]
    exact hc g

/-- Every gate in `F.toCircuit` has syntactic consumer fan-out at most one. -/
theorem _root_.Cslib.Circuits.Formula.gateFanout_toCircuit_le_one (F : Formula σ n)
    (g : Fin F.toCircuit.size) : F.toCircuit.gateFanout g ≤ 1 := by
  induction F with
  | input i => exact g.elim0
  | gate op args ih =>
    exact gateFanout_oneGate_comp_le_one op (Circuit.pi fun a => (args a).toCircuit)
      (gateFanout_pi_le_one _ ih) g

/-- Compiling a formula to a circuit produces zero multi-fanout inner gates (`g_{≥2} = 0`). -/
@[simp] theorem multiFanoutSize_toCircuit (F : Formula σ n) :
    multiFanoutSize F.toCircuit = 0 :=
  multiFanoutSize_eq_zero_of_gateFanout_le_one F.gateFanout_toCircuit_le_one

/-- An active signal is *unit-fanout* when it is an inner gate of fan-out one. -/
@[expose] def IsUnitGateSignal (c : Circuit σ n m) : ActiveSignal c → Prop
  | .input _ _ => False
  | .gate g => fanout c ((.gate g : ActiveSignal c).toSignal) = 1

/-- Every unit-fanout inner gate has a two-element support `{.gate g, u}` with
`(.gate g).rank < u.rank`. -/
theorem exists_support_eq_pair_of_isUnitGateSignal {g : InnerGate c}
    (hg : IsUnitGateSignal c (.gate g)) :
    ∃ u : Node c, (Node.gate g).rank < u.rank ∧ support c (.gate g) = {Node.gate g, u} := by
  obtain ⟨u, t, ht, rfl⟩ := consumerNodes_nonempty ((.gate g : ActiveSignal c).toSignal)
  have hlt := rank_gate_lt_ownerNode ht
  have hne : (Node.gate g : Node c) ≠ ownerNode t := fun h => lt_irrefl _ (h ▸ hlt)
  refine ⟨ownerNode t, hlt, ?_⟩
  have hsub : ({Node.gate g, ownerNode t} : Set (Node c)) ⊆ support c (.gate g) :=
    pair_subset_iff.mpr ⟨mem_insert _ _, mem_insert_of_mem _ ⟨t, ht, rfl⟩⟩
  exact (eq_of_subset_of_ncard_le hsub
    ((ncard_support_gate_eq_two hg).trans_le (ncard_pair hne).symm.le) (toFinite _)).symm

/-- **Low-reuse incidence bound at fan-in two.** Subtracting the `2 |G₁|` incidences of fan-out-one
inner gates from `3 |InnerGate c| + m` bounds the remaining support sizes by
`|InnerGate c| + 2 · multiFanoutSize c + m`. -/
theorem sum_ncard_support_nonUnit_le [Fintype (ActiveSignal c)] [DecidablePred (IsUnitGateSignal c)]
    (hfan : c.FanInAtMost 2) :
    ∑ w : ActiveSignal c with ¬IsUnitGateSignal c w, (support c w).ncard ≤
      Nat.card (InnerGate c) + 2 * multiFanoutSize c + m := by
  classical
  have := Fintype.ofFinite (InnerGate c)
  have htot := sum_ncard_support_le_card_innerGate (r := 2) hfan
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (IsUnitGateSignal c)] at htot
  let S₁ : Finset (InnerGate c) :=
    Finset.univ.filter fun g => fanout c ((.gate g : ActiveSignal c).toSignal) = 1
  have hpart : Nat.card (InnerGate c) = S₁.card + multiFanoutSize c := by
    have hge1 (g : InnerGate c) :
        fanout c ((.gate g : ActiveSignal c).toSignal) = 1 ↔ g ∉ multiFanoutGates c := by
      have hp := fanout_pos ((.gate g : ActiveSignal c).toSignal)
      simp only [multiFanoutGates, mem_ofPred_eq]
      omega
    have hmul : multiFanoutSize c =
        (Finset.univ.filter fun g : InnerGate c => g ∈ multiFanoutGates c).card := by
      rw [multiFanoutSize, ← ncard_coe_finset]
      congr 1
      ext g
      simp
    rw [hmul, Nat.card_eq_fintype_card, ← Finset.card_univ,
      ← Finset.card_filter_add_card_filter_not (s := Finset.univ) (· ∈ multiFanoutGates c),
      add_comm]
    congr 2
    ext g
    simp [S₁, hge1]
  have hunit : 2 * S₁.card ≤
      ∑ w : ActiveSignal c with IsUnitGateSignal c w, (support c w).ncard := by
    let emb : InnerGate c ↪ ActiveSignal c :=
      ⟨ActiveSignal.gate, fun _ _ h => ActiveSignal.gate.inj h⟩
    have hsub : S₁.map emb ⊆ Finset.univ.filter (IsUnitGateSignal c) := by
      intro w hw
      obtain ⟨g, hg, rfl⟩ := Finset.mem_map.mp hw
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hg).2⟩
    calc 2 * S₁.card = ∑ _g ∈ S₁, 2 := by
            rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ g ∈ S₁, (support c (emb g)).ncard := Finset.sum_le_sum fun g hg =>
            (ncard_support_gate_eq_two (Finset.mem_filter.mp hg).2).ge
      _ = ∑ w ∈ S₁.map emb, (support c w).ncard :=
            (Finset.sum_map S₁ emb fun w => (support c w).ncard).symm
      _ ≤ ∑ w : ActiveSignal c with IsUnitGateSignal c w, (support c w).ncard :=
            Finset.sum_le_sum_of_subset hsub
  omega

/-! ### Signal frontiers and splicing across any node cut -/

variable (c) in
/-- **The signal frontier** of a node set `P`: the active signals whose support meets both `P` and
its complement. -/
@[expose] def signalFrontier (P : Set (Node c)) : Set (ActiveSignal c) :=
  {w : ActiveSignal c | (support c w ∩ P).Nonempty ∧ (support c w ∩ Pᶜ).Nonempty}

variable (c) in
/-- The inputs read by the nodes in `P`: reachable inputs whose support meets `P`. -/
@[expose] def nodeReadIn (P : Set (Node c)) : Set (Fin n) :=
  {i : Fin n | ∃ hi : Reach c (.input i), (support c (.input i hi) ∩ P).Nonempty}

variable (c) in
/-- The hyperedge cutwidth of a node layout `π`: the maximum size of `signalFrontier` along the
prefixes of `π`. -/
@[expose] noncomputable def signalWidth (π : Layout (Node c)) : ℕ :=
  (Finset.range (Nat.card (Node c) + 1)).sup fun t => (signalFrontier c (π.initial t)).ncard

@[simp] theorem signalFrontier_empty : signalFrontier c ∅ = ∅ := by
  ext w
  simp [signalFrontier]

@[simp] theorem signalFrontier_univ : signalFrontier c univ = ∅ := by
  ext w
  simp [signalFrontier]

@[simp] theorem nodeReadIn_empty : nodeReadIn c ∅ = ∅ := by
  ext i
  simp [nodeReadIn]

theorem nodeReadIn_univ : nodeReadIn c univ = {i : Fin n | Reach c (.input i)} := by
  ext i
  simp only [nodeReadIn, inter_univ, mem_ofPred_eq]
  exact ⟨fun ⟨hi, _⟩ => hi, fun hi => ⟨hi, support_nonempty (.input i hi)⟩⟩

private theorem trace_splice_of_mem_support {U : Type*} {I : Interpretation σ U}
    {P : Set (Node c)} {x y z : Fin n → U}
    (hcut : ∀ w ∈ signalFrontier c P, c.program.trace I x w.wire = c.program.trace I y w.wire)
    {w : ActiveSignal c} {u v : Node c} (hu : u ∈ support c w) (hv : v ∈ support c w)
    (hstep : (u ∈ P → c.program.trace I z w.wire = c.program.trace I x w.wire) ∧
      (u ∉ P → c.program.trace I z w.wire = c.program.trace I y w.wire)) :
    (v ∈ P → c.program.trace I z w.wire = c.program.trace I x w.wire) ∧
    (v ∉ P → c.program.trace I z w.wire = c.program.trace I y w.wire) := by
  refine ⟨fun hvP => ?_, fun hvPc => ?_⟩
  · by_cases huP : u ∈ P
    · exact hstep.1 huP
    · exact (hstep.2 huP).trans (hcut w ⟨⟨v, hv, hvP⟩, ⟨u, hu, huP⟩⟩).symm
  · by_cases huP : u ∈ P
    · exact (hstep.1 huP).trans (hcut w ⟨⟨u, hu, huP⟩, ⟨v, hv, hvPc⟩⟩)
    · exact hstep.2 huP

private theorem trace_consumer_splice_signalFrontier {U : Type*} (I : Interpretation σ U)
    {P : Set (Node c)} {x y z : Fin n → U}
    (hcut : ∀ w ∈ signalFrontier c P, c.program.trace I x w.wire = c.program.trace I y w.wire)
    (hzx : EqOn z x (nodeReadIn c P)) (hzy : EqOn z y (nodeReadIn c P)ᶜ) :
    ∀ (w : Wire n c.size) (hw : Reach c w),
      ∀ t : Consumer c, consumed t = ⟨w, hw⟩ →
        (ownerNode t ∈ P → c.program.trace I z w = c.program.trace I x w) ∧
        (ownerNode t ∉ P → c.program.trace I z w = c.program.trace I y w) := by
  classical
  refine c.program.wire_induction (fun i hi t ht => ?_) (fun g ih hg t ht => ?_)
  · have hmem : ownerNode t ∈ support c (.input i hi) := ⟨t, ht, rfl⟩
    refine ⟨fun hin => hzx ⟨hi, ownerNode t, hmem, hin⟩, fun hout => ?_⟩
    by_cases hhit : (support c (.input i hi) ∩ P).Nonempty
    · have hfront : ActiveSignal.input i hi ∈ signalFrontier c P :=
        ⟨hhit, ⟨ownerNode t, hmem, hout⟩⟩
      exact (hzx ⟨hi, hhit⟩).trans (hcut _ hfront)
    · exact hzy fun ⟨_, u, hu, huP⟩ => hhit ⟨u, hu, huP⟩
  · by_cases ha0 : σ.Arity (c.program.lines g).op = 0
    · have hconst (v₁ v₂ : Fin n → U) :
          c.program.trace I v₁ (.gate g) = c.program.trace I v₂ (.gate g) := by
        rw [Program.trace_gate, Program.trace_gate]
        exact congrArg _ (funext fun a => absurd a.isLt (by omega))
      exact ⟨fun _ => hconst z x, fun _ => hconst z y⟩
    · let ig : InnerGate c := ⟨g, hg, ha0⟩
      have hig : (Node.gate ig ∈ P →
            c.program.trace I z (.gate g) = c.program.trace I x (.gate g)) ∧
          (Node.gate ig ∉ P →
            c.program.trace I z (.gate g) = c.program.trace I y (.gate g)) :=
        ⟨fun hin => by
          rw [Program.trace_gate, Program.trace_gate]
          exact congrArg _ (funext fun a => (ih a (.arg a hg) (.inl ⟨⟨g, a⟩, hg⟩) rfl).1 hin),
         fun hout => by
          rw [Program.trace_gate, Program.trace_gate]
          exact congrArg _ (funext fun a => (ih a (.arg a hg) (.inl ⟨⟨g, a⟩, hg⟩) rfl).2 hout)⟩
      exact trace_splice_of_mem_support (w := .gate ig) hcut (mem_insert _ _)
        (mem_insert_of_mem _ ⟨t, ht, rfl⟩) hig

/-- **Splicing outputs across a node cut.** If the runs of `c` on `x` and `y` agree on every wire
in `signalFrontier c P`, and `z` agrees with `x` on `nodeReadIn c P` and with `y` elsewhere, then
`c.eval I z o` equals `c.eval I x o` when `.output o ∈ P` and `c.eval I y o` when
`.output o ∉ P`. -/
theorem eval_splice_signalFrontier {U : Type*} (I : Interpretation σ U) {P : Set (Node c)}
    {x y z : Fin n → U}
    (hcut : ∀ w ∈ signalFrontier c P, c.program.trace I x w.wire = c.program.trace I y w.wire)
    (hzx : EqOn z x (nodeReadIn c P)) (hzy : EqOn z y (nodeReadIn c P)ᶜ) :
    ∀ o : Fin m, (Node.output o ∈ P → c.eval I z o = c.eval I x o) ∧
      (Node.output o ∉ P → c.eval I z o = c.eval I y o) := fun o =>
  trace_consumer_splice_signalFrontier I hcut hzx hzy (c.outputs o) (.output o) (.inr o) rfl

/-- **Splicing inner-gate wires across a node cut.** Under the same splicing hypotheses, every
reachable inner gate `g` evaluates on `z` to its value on `x` when `.gate g ∈ P` and to its value on
`y` when `.gate g ∉ P`. -/
theorem trace_gate_splice_signalFrontier {U : Type*} (I : Interpretation σ U) {P : Set (Node c)}
    {x y z : Fin n → U}
    (hcut : ∀ w ∈ signalFrontier c P, c.program.trace I x w.wire = c.program.trace I y w.wire)
    (hzx : EqOn z x (nodeReadIn c P)) (hzy : EqOn z y (nodeReadIn c P)ᶜ) (g : InnerGate c) :
    (Node.gate g ∈ P → c.program.trace I z (ActiveSignal.gate g).wire =
      c.program.trace I x (ActiveSignal.gate g).wire) ∧
    (Node.gate g ∉ P → c.program.trace I z (ActiveSignal.gate g).wire =
      c.program.trace I y (ActiveSignal.gate g).wire) := by
  obtain ⟨_, t, ht, rfl⟩ := consumerNodes_nonempty ((.gate g : ActiveSignal c).toSignal)
  exact trace_splice_of_mem_support (w := .gate g) hcut (mem_insert_of_mem _ ⟨t, ht, rfl⟩)
    (mem_insert _ _)
    (trace_consumer_splice_signalFrontier I hcut hzx hzy _ (ActiveSignal.gate g).reach t ht)

end Supports

/-! ### Post-layout Steiner multigraph and constraint network -/

section Steiner

variable {σ : Signature} {n m : ℕ}

open Classical in
private noncomputable def supportPositions (c : Circuit σ n m) (π : Layout (Node c))
    (w : ActiveSignal c) : Finset (Fin (Nat.card (Node c))) :=
  (toFinite (π '' support c w)).toFinset

private theorem card_supportPositions (c : Circuit σ n m) (π : Layout (Node c))
    (w : ActiveSignal c) : (supportPositions c π w).card = (support c w).ncard := by
  rw [supportPositions, ← ncard_eq_toFinset_card _ (toFinite _),
    ncard_image_of_injective _ π.injective]

private noncomputable def supportEmb (c : Circuit σ n m) (π : Layout (Node c))
    (w : ActiveSignal c) : Fin (support c w).ncard ↪o Fin (Nat.card (Node c)) :=
  (supportPositions c π w).orderEmbOfFin (card_supportPositions c π w)

/-- The `k`-th node of `support c w` in increasing `π`-order. -/
noncomputable def supportNode (c : Circuit σ n m) (π : Layout (Node c)) (w : ActiveSignal c)
    (k : Fin (support c w).ncard) : Node c :=
  π.symm (supportEmb c π w k)

private theorem pi_supportNode (c : Circuit σ n m) (π : Layout (Node c)) (w : ActiveSignal c)
    (k : Fin (support c w).ncard) : π (supportNode c π w k) = supportEmb c π w k :=
  π.apply_symm_apply _

theorem supportNode_mem (c : Circuit σ n m) (π : Layout (Node c)) (w : ActiveSignal c)
    (k : Fin (support c w).ncard) : supportNode c π w k ∈ support c w := by
  have hmem : supportEmb c π w k ∈ supportPositions c π w :=
    Finset.orderEmbOfFin_mem (supportPositions c π w) (card_supportPositions c π w) k
  rw [supportPositions, Finite.mem_toFinset] at hmem
  obtain ⟨u, hu, hpi⟩ := hmem
  rw [supportNode, ← hpi, π.symm_apply_apply]
  exact hu

theorem pi_supportNode_lt_iff {c : Circuit σ n m} {π : Layout (Node c)} {w : ActiveSignal c}
    {j k : Fin (support c w).ncard} :
    π (supportNode c π w j) < π (supportNode c π w k) ↔ j < k := by
  rw [pi_supportNode, pi_supportNode]
  exact (supportEmb c π w).lt_iff_lt

theorem pi_supportNode_le_iff {c : Circuit σ n m} {π : Layout (Node c)} {w : ActiveSignal c}
    {j k : Fin (support c w).ncard} :
    π (supportNode c π w j) ≤ π (supportNode c π w k) ↔ j ≤ k := by
  rw [pi_supportNode, pi_supportNode]
  exact (supportEmb c π w).le_iff_le

private theorem mem_range_supportEmb {c : Circuit σ n m} (π : Layout (Node c))
    {w : ActiveSignal c} {u : Node c} (hu : u ∈ support c w) :
    π u ∈ range (supportEmb c π w) := by
  rw [supportEmb, Finset.range_orderEmbOfFin, supportPositions, Finite.coe_toFinset]
  exact ⟨u, hu, rfl⟩

/-- Index of `u ∈ support c w` in increasing `π`-order. -/
private noncomputable def supportIndex {c : Circuit σ n m} (π : Layout (Node c))
    {w : ActiveSignal c} {u : Node c} (hu : u ∈ support c w) : Fin (support c w).ncard :=
  (mem_range_supportEmb π hu).choose

private theorem supportNode_supportIndex {c : Circuit σ n m} (π : Layout (Node c))
    {w : ActiveSignal c} {u : Node c} (hu : u ∈ support c w) :
    supportNode c π w (supportIndex π hu) = u := by
  apply π.injective
  rw [pi_supportNode]
  exact (mem_range_supportEmb π hu).choose_spec

private theorem supportIndex_supportNode {c : Circuit σ n m} (π : Layout (Node c))
    (w : ActiveSignal c) (k : Fin (support c w).ncard) :
    supportIndex π (supportNode_mem c π w k) = k := by
  have heq := supportNode_supportIndex π (supportNode_mem c π w k)
  have hpi := congrArg π heq
  rw [pi_supportNode, pi_supportNode] at hpi
  exact (supportEmb c π w).injective hpi

/-- An edge of the post-layout Steiner path of `w`: joins consecutive elements `j` and `j + 1` of
`support c w` in `π`-order. -/
abbrev SteinerEdge (c : Circuit σ n m) : Type :=
  Σ w : ActiveSignal c, Fin ((support c w).ncard - 1)

instance (c : Circuit σ n m) : Finite (SteinerEdge c) := inferInstance

/-- Source of a Steiner edge: `j`-th support node of its signal. -/
private noncomputable def steinerSrc (c : Circuit σ n m) (π : Layout (Node c)) :
    SteinerEdge c → Node c
  | ⟨w, ⟨j, hj⟩⟩ => supportNode c π w ⟨j, by omega⟩

/-- Target of a Steiner edge: `(j + 1)`-st support node of its signal. -/
private noncomputable def steinerTgt (c : Circuit σ n m) (π : Layout (Node c)) :
    SteinerEdge c → Node c
  | ⟨w, ⟨j, hj⟩⟩ => supportNode c π w ⟨j + 1, by omega⟩

/-- **The post-layout Steiner multigraph** on `Node c`. -/
noncomputable def steinerGraph (c : Circuit σ n m) (π : Layout (Node c)) :
    Multigraph (Node c) (SteinerEdge c) where
  src := steinerSrc c π
  tgt := steinerTgt c π

section GraphProps

variable {c : Circuit σ n m} {π : Layout (Node c)}

private theorem pi_steinerSrc_lt_tgt (e : SteinerEdge c) :
    π (steinerSrc c π e) < π (steinerTgt c π e) := by
  rcases e with ⟨w, ⟨j, hj⟩⟩
  rw [steinerSrc, steinerTgt, pi_supportNode_lt_iff]
  exact Fin.mk_lt_mk.mpr (Nat.lt_succ_self j)

theorem steinerGraph_loopless : (steinerGraph c π).Loopless := by
  intro e h
  exact (ne_of_lt (pi_steinerSrc_lt_tgt e)) (congrArg π h)

private theorem steinerSrc_mem_support (e : SteinerEdge c) :
    steinerSrc c π e ∈ support c e.1 := by
  rcases e with ⟨w, ⟨j, hj⟩⟩
  exact supportNode_mem c π w _

private theorem steinerTgt_mem_support (e : SteinerEdge c) :
    steinerTgt c π e ∈ support c e.1 := by
  rcases e with ⟨w, ⟨j, hj⟩⟩
  exact supportNode_mem c π w _

/-- A Steiner edge crosses `π.initial t` iff `t` separates its two consecutive `π`-positions. -/
private theorem mem_frontier_steinerGraph_iff {t : ℕ} {e : SteinerEdge c} :
    e ∈ (steinerGraph c π).frontier π t ↔
      (π (steinerSrc c π e) : ℕ) < t ∧ t ≤ (π (steinerTgt c π e) : ℕ) := by
  have hlt : (π (steinerSrc c π e) : ℕ) < (π (steinerTgt c π e) : ℕ) :=
    Fin.lt_def.mp (pi_steinerSrc_lt_tgt e)
  simp only [Multigraph.frontier, Multigraph.mem_edgeCut, Layout.mem_initial, steinerGraph]
  omega

/-- At most one Steiner edge of any given signal crosses `π.initial t`. -/
private theorem steinerEdge_eq_of_mem_frontier {t : ℕ} {e₁ e₂ : SteinerEdge c}
    (h₁ : e₁ ∈ (steinerGraph c π).frontier π t) (h₂ : e₂ ∈ (steinerGraph c π).frontier π t)
    (hw : e₁.1 = e₂.1) : e₁ = e₂ := by
  obtain ⟨w, j₁⟩ := e₁
  obtain ⟨w', j₂⟩ := e₂
  dsimp only at hw
  subst hw
  rw [mem_frontier_steinerGraph_iff] at h₁ h₂
  suffices j₁.val = j₂.val from Sigma.ext rfl (heq_of_eq (Fin.ext this))
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle : (π (supportNode c π w ⟨j₁.val + 1, by omega⟩) : ℕ) ≤
        (π (supportNode c π w ⟨j₂.val, by omega⟩) : ℕ) :=
      Fin.le_iff_val_le_val.mp ((pi_supportNode_le_iff (c := c) (π := π)).mpr
        (Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hlt)))
    change _ ∧ t ≤ (π (supportNode c π w ⟨j₁.val + 1, _⟩) : ℕ) at h₁
    change (π (supportNode c π w ⟨j₂.val, _⟩) : ℕ) < t ∧ _ at h₂
    omega
  · have hle : (π (supportNode c π w ⟨j₂.val + 1, by omega⟩) : ℕ) ≤
        (π (supportNode c π w ⟨j₁.val, by omega⟩) : ℕ) :=
      Fin.le_iff_val_le_val.mp ((pi_supportNode_le_iff (c := c) (π := π)).mpr
        (Fin.mk_le_mk.mpr (Nat.succ_le_of_lt hgt)))
    change (π (supportNode c π w ⟨j₁.val, _⟩) : ℕ) < t ∧ _ at h₁
    change _ ∧ t ≤ (π (supportNode c π w ⟨j₂.val + 1, _⟩) : ℕ) at h₂
    omega

/-- **Exact frontier equivalence.** The edges of `steinerGraph c π` crossing `π.initial t`
correspond bijectively to `signalFrontier c (π.initial t)`. -/
theorem ncard_frontier_steinerGraph_eq (t : ℕ) :
    ((steinerGraph c π).frontier π t).ncard = (signalFrontier c (π.initial t)).ncard := by
  let fstEdge : SteinerEdge c → ActiveSignal c := fun e => e.1
  have himg : fstEdge '' (steinerGraph c π).frontier π t = signalFrontier c (π.initial t) := by
    ext w
    constructor
    · rintro ⟨e, he, rfl⟩
      obtain ⟨h₁, h₂⟩ := mem_frontier_steinerGraph_iff.mp he
      exact ⟨⟨steinerSrc c π e, steinerSrc_mem_support e, h₁⟩,
        ⟨steinerTgt c π e, steinerTgt_mem_support e, not_lt.mpr h₂⟩⟩
    · rintro ⟨⟨u, hu, huP⟩, ⟨v, hv, hvPc⟩⟩
      rw [Layout.mem_initial] at huP
      have hvP : t ≤ (π v : ℕ) := not_lt.mp fun h => hvPc h
      let iu := supportIndex π hu
      let iv := supportIndex π hv
      have huv : iu < iv := by
        rw [← pi_supportNode_lt_iff (c := c) (π := π), supportNode_supportIndex π hu,
          supportNode_supportIndex π hv, Fin.lt_def]
        omega
      let S : Finset (Fin (support c w).ncard) :=
        Finset.univ.filter fun j => (π (supportNode c π w j) : ℕ) < t
      have hSne : S.Nonempty := ⟨iu, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by
        rwa [supportNode_supportIndex π hu]⟩⟩
      set j := S.max' hSne
      have hj_lt : (π (supportNode c π w j) : ℕ) < t := (Finset.mem_filter.mp (S.max'_mem hSne)).2
      have hjv : j < iv := by
        by_contra! hge
        have hle := Fin.le_iff_val_le_val.mp ((pi_supportNode_le_iff (c := c) (π := π)).mpr hge)
        rw [supportNode_supportIndex π hv] at hle
        omega
      have hj1 : j.val + 1 < (support c w).ncard := by
        have := Fin.lt_def.mp hjv
        have := iv.isLt
        omega
      have hj1_ge : t ≤ (π (supportNode c π w ⟨j.val + 1, hj1⟩) : ℕ) := by
        by_contra! hlt'
        exact (Fin.le_iff_val_le_val.mp (S.le_max' ⟨j.val + 1, hj1⟩
          (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt'⟩))).not_gt (Nat.lt_succ_self j.val)
      exact ⟨⟨w, ⟨j.val, by omega⟩⟩, mem_frontier_steinerGraph_iff.mpr ⟨hj_lt, hj1_ge⟩, rfl⟩
  rw [← himg]
  exact (InjOn.ncard_image fun e₁ h₁ e₂ h₂ hw => steinerEdge_eq_of_mem_frontier h₁ h₂ hw).symm

/-- The layout width of `steinerGraph c π` along `π` equals `signalWidth c π`. -/
theorem width_steinerGraph_eq : (steinerGraph c π).width π = signalWidth c π := by
  apply le_antisymm
  · refine ((steinerGraph c π).width_le_iff π).mpr fun t => ?_
    rcases le_or_gt t (Nat.card (Node c)) with ht | ht
    · rw [ncard_frontier_steinerGraph_eq]
      exact Finset.le_sup (f := fun s => (signalFrontier c (π.initial s)).ncard)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ht))
    · rw [(steinerGraph c π).frontier_of_card_le π ht.le, ncard_empty]
      exact Nat.zero_le _
  · refine Finset.sup_le fun t _ => ?_
    rw [← ncard_frontier_steinerGraph_eq]
    exact (steinerGraph c π).ncard_frontier_le_width π t

/-- Each node has degree at most `2 (r + 1)` in `steinerGraph c π`. -/
theorem maxDegreeLE_steinerGraph {r : ℕ} (hfan : c.FanInAtMost r) :
    (steinerGraph c π).MaxDegreeLE (2 * (r + 1)) := by
  intro u
  classical
  let φ : {e : SteinerEdge c // e ∈ (steinerGraph c π).incidenceSet u} →
      {w : ActiveSignal c // u ∈ support c w} × Bool :=
    fun ⟨e, he⟩ =>
      if hs : steinerSrc c π e = u then (⟨e.1, hs ▸ steinerSrc_mem_support e⟩, false)
      else (⟨e.1, he.resolve_left hs ▸ steinerTgt_mem_support e⟩, true)
  have hinj : Function.Injective φ := by
    rintro ⟨⟨w₁, j₁⟩, he₁⟩ ⟨⟨w₂, j₂⟩, he₂⟩ h
    dsimp only [φ] at h
    split_ifs at h with hs₁ hs₂ hs₂
    · cases Subtype.mk.inj (Prod.mk.inj h).1
      have hpi : π (supportNode c π w₁ ⟨j₁.val, _⟩) = π (supportNode c π w₁ ⟨j₂.val, _⟩) :=
        congrArg π (hs₁.trans hs₂.symm)
      rw [pi_supportNode, pi_supportNode] at hpi
      exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Fin.ext
        (Fin.mk.inj ((supportEmb c π w₁).injective hpi)))))
    · cases (Prod.mk.inj h).2
    · cases (Prod.mk.inj h).2
    · cases Subtype.mk.inj (Prod.mk.inj h).1
      have hpi : π (supportNode c π w₁ ⟨j₁.val + 1, _⟩) = π (supportNode c π w₁ ⟨j₂.val + 1, _⟩) :=
        congrArg π ((he₁.resolve_left hs₁).trans (he₂.resolve_left hs₂).symm)
      rw [pi_supportNode, pi_supportNode] at hpi
      exact Subtype.ext (Sigma.ext rfl (heq_of_eq (Fin.ext
        (Nat.succ.inj (Fin.mk.inj ((supportEmb c π w₁).injective hpi))))))
  rw [← Nat.card_coe_set_eq]
  calc Nat.card {e : SteinerEdge c // e ∈ (steinerGraph c π).incidenceSet u}
      ≤ Nat.card ({w : ActiveSignal c // u ∈ support c w} × Bool) :=
        Nat.card_le_card_of_injective φ hinj
    _ = {w : ActiveSignal c | u ∈ support c w}.ncard * 2 := by
        have hcoe : Nat.card {w : ActiveSignal c // u ∈ support c w} =
            {w : ActiveSignal c | u ∈ support c w}.ncard :=
          Nat.card_coe_set_eq {w : ActiveSignal c | u ∈ support c w}
        rw [Nat.card_prod, hcoe, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]
    _ ≤ 2 * (r + 1) := by have := ncard_activeSignal_mem_support_le hfan u; omega

end GraphProps

/-! ### The Steiner constraint network -/

section Network

variable {U : Type*}

open Classical in
/-- Each reachable input `i` is read at the first node of its support in `π`-order. -/
private noncomputable def steinerSite (c : Circuit σ n m) (π : Layout (Node c)) (i : Fin n) :
    Option (Node c) :=
  if hi : Reach c (.input i) then
    some (supportNode c π (.input i hi) ⟨0, (ncard_pos (toFinite _)).mpr
      (support_nonempty (.input i hi))⟩)
  else none

/-- Canonical incident Steiner edge of `w` at `u ∈ support c w` when `2 ≤ |support c w|`. -/
private noncomputable def canonicalEdge {c : Circuit σ n m} (π : Layout (Node c))
    {w : ActiveSignal c} {u : Node c} (hu : u ∈ support c w)
    (h2 : 2 ≤ (support c w).ncard) : SteinerEdge c :=
  let idx := supportIndex π hu
  if idx.val = 0 then ⟨w, ⟨0, by omega⟩⟩ else ⟨w, ⟨idx.val - 1, by have := idx.isLt; omega⟩⟩

private theorem canonicalEdge_fst {c : Circuit σ n m} (π : Layout (Node c))
    {w : ActiveSignal c} {u : Node c} (hu : u ∈ support c w)
    (h2 : 2 ≤ (support c w).ncard) : (canonicalEdge π hu h2).1 = w := by
  unfold canonicalEdge
  dsimp only
  split_ifs <;> rfl

private theorem canonicalEdge_incident {c : Circuit σ n m} (π : Layout (Node c))
    {w : ActiveSignal c} {u : Node c} (hu : u ∈ support c w)
    (h2 : 2 ≤ (support c w).ncard) :
    (steinerGraph c π).src (canonicalEdge π hu h2) = u ∨
      (steinerGraph c π).tgt (canonicalEdge π hu h2) = u := by
  unfold canonicalEdge
  dsimp only
  set idx := supportIndex π hu
  split_ifs with h0
  · left
    change supportNode c π w ⟨0, by omega⟩ = u
    have hidx : (⟨0, by omega⟩ : Fin (support c w).ncard) = idx := Fin.ext h0.symm
    rw [hidx]
    exact supportNode_supportIndex π hu
  · right
    have hlt : idx.val - 1 + 1 < (support c w).ncard := by have := idx.isLt; omega
    change supportNode c π w ⟨idx.val - 1 + 1, hlt⟩ = u
    have hidx : (⟨idx.val - 1 + 1, hlt⟩ : Fin (support c w).ncard) = idx :=
      Fin.ext (by dsimp only; omega)
    rw [hidx]
    exact supportNode_supportIndex π hu

open Classical in
/-- Value read for a reachable wire `w` at node `u` when `u` consumes `w` (or is `w`). -/
private noncomputable def wireValAt (c : Circuit σ n m) (I : Interpretation σ U)
    (π : Layout (Node c)) (u : Node c) (x : Fin n → U) (α : SteinerEdge c → U)
    (w : Wire n c.size) (hw : Reach c w) (hu : ∀ aw : ActiveSignal c, aw.wire = w →
      u ∈ support c aw) : U :=
  match w with
  | .input i =>
    let aw : ActiveSignal c := .input i hw
    if h2 : 2 ≤ (support c aw).ncard then α (canonicalEdge π (hu aw rfl) h2) else x i
  | .gate g =>
    if ha0 : σ.Arity (c.program.lines g).op = 0 then
      I (c.program.lines g).op fun a => absurd a.isLt (by omega)
    else
      let aw : ActiveSignal c := .gate ⟨g, hw, ha0⟩
      α (canonicalEdge π (hu aw rfl) (two_le_ncard_support_gate ⟨g, hw, ha0⟩))

/-- Local constraint at node `u` of `steinerNetwork`:
1. All Steiner edges of the same signal incident to `u` agree with `canonicalEdge`.
2. Any input read at `u` (`steinerSite c π i = some u`) matches `x i` on its outgoing edge.
3. Gate nodes evaluate their operation; output nodes check membership in `Acc o`. -/
private def SteinerConstraint (c : Circuit σ n m) (I : Interpretation σ U) (Acc : Fin m → Set U)
    (π : Layout (Node c)) (u : Node c) (x : Fin n → U) (α : SteinerEdge c → U) : Prop :=
  (∀ e : SteinerEdge c, (steinerSrc c π e = u ∨ steinerTgt c π e = u) →
    ∀ (hu : u ∈ support c e.1) (h2 : 2 ≤ (support c e.1).ncard),
      α e = α (canonicalEdge π hu h2)) ∧
  (∀ (i : Fin n) (hi : Reach c (.input i)),
    steinerSite c π i = some u →
    ∀ (hu : u ∈ support c (.input i hi)) (h2 : 2 ≤ (support c (.input i hi)).ncard),
      α (canonicalEdge π hu h2) = x i) ∧
  match u with
  | .gate (⟨gIdx, hgReach, hgArity⟩) =>
    let g : InnerGate c := ⟨gIdx, hgReach, hgArity⟩
    α (canonicalEdge π (gate_mem_support g) (two_le_ncard_support_gate g)) =
      I (c.program.lines gIdx).op fun a =>
        wireValAt c I π (.gate g) x α ((c.program.lines gIdx).wires a) (.arg a hgReach)
          fun aw haw => by
            let sl : Consumer c := .inl ⟨⟨gIdx, a⟩, hgReach⟩
            have hcons : consumed sl = aw.toSignal := Subtype.ext haw.symm
            cases aw with
            | input i hi => exact ⟨sl, hcons, rfl⟩
            | gate g' => exact mem_insert_of_mem _ ⟨sl, hcons, rfl⟩
  | .output o =>
    wireValAt c I π (.output o) x α (c.outputs o) (.output o) (fun aw haw => by
      have hcons : consumed (.inr o : Consumer c) = aw.toSignal := Subtype.ext haw.symm
      cases aw with
      | input i hi => exact ⟨.inr o, hcons, rfl⟩
      | gate g' => exact mem_insert_of_mem _ ⟨.inr o, hcons, rfl⟩) ∈ Acc o

private theorem wireValAt_congr {c : Circuit σ n m} {I : Interpretation σ U}
    {π : Layout (Node c)} {u : Node c} {x x' : Fin n → U} {α α' : SteinerEdge c → U}
    (hx : ∀ i, steinerSite c π i = some u → x i = x' i)
    (hα : ∀ e, (steinerGraph c π).src e = u ∨ (steinerGraph c π).tgt e = u → α e = α' e)
    (w : Wire n c.size) (hw : Reach c w)
    (hu : ∀ aw : ActiveSignal c, aw.wire = w → u ∈ support c aw) :
    wireValAt c I π u x α w hw hu = wireValAt c I π u x' α' w hw hu := by
  cases w with
  | input i =>
    dsimp only [wireValAt]
    split_ifs with h2
    · exact hα _ (canonicalEdge_incident π _ _)
    · have hcard1 : (support c (.input i hw)).ncard = 1 := by
        have hp := (ncard_pos (toFinite _)).mpr (support_nonempty (.input i hw))
        omega
      have hsite : steinerSite c π i = some u := by
        simp only [steinerSite, hw, ↓reduceDIte, Option.some.injEq]
        have : Subsingleton (Fin (support c (.input i hw)).ncard) :=
          Fin.subsingleton_iff_le_one.mpr (by omega)
        have hidx : (⟨0, by omega⟩ : Fin (support c (.input i hw)).ncard) =
            supportIndex π (hu (.input i hw) rfl) :=
          Subsingleton.elim _ _
        rw [hidx]
        exact supportNode_supportIndex π (hu (.input i hw) rfl)
      exact hx i hsite
  | gate g =>
    dsimp only [wireValAt]
    split_ifs with ha0
    · rfl
    · exact hα _ (canonicalEdge_incident π _ _)

/-- **The post-layout Steiner constraint network** of `c` along `π : Layout (Node c)`. -/
noncomputable def steinerNetwork (c : Circuit σ n m) (I : Interpretation σ U)
    (Acc : Fin m → Set U) (π : Layout (Node c)) : Network U (Fin n) (Node c) (SteinerEdge c) where
  toMultigraph := steinerGraph c π
  site := steinerSite c π
  Constraint := SteinerConstraint c I Acc π
  constraint_congr u x x' α α' hx hα h := by
    obtain ⟨h1, h2, h3⟩ := h
    refine ⟨fun e he hu h2' => ?_, fun i hi hs hu h2' => ?_, ?_⟩
    · rw [← hα e he, ← hα _ (canonicalEdge_incident π hu h2')]
      exact h1 e he hu h2'
    · rw [← hα _ (canonicalEdge_incident π hu h2'), ← hx i hs]
      exact h2 i hi hs hu h2'
    · cases u with
      | gate g =>
        dsimp only at h3 ⊢
        rw [← hα _ (canonicalEdge_incident π _ _), h3]
        exact congrArg _ (funext fun a => wireValAt_congr hx hα _ _ _)
      | output o =>
        dsimp only at h3 ⊢
        rwa [← wireValAt_congr hx hα _ _ _]

variable {c : Circuit σ n m} {I : Interpretation σ U} {Acc : Fin m → Set U} {π : Layout (Node c)}

@[simp] theorem steinerNetwork_toMultigraph :
    (steinerNetwork c I Acc π).toMultigraph = steinerGraph c π := by
  unfold steinerNetwork
  rfl

private theorem steinerSite_eq_some {i : Fin n} {u : Node c} (h : steinerSite c π i = some u) :
    ∃ hi : Reach c (.input i), u ∈ support c (.input i hi) := by
  unfold steinerSite at h
  split_ifs at h with hi
  obtain rfl := Option.some.inj h
  exact ⟨hi, supportNode_mem c π (.input i hi) _⟩

/-- The inputs read by `steinerNetwork` are the reachable inputs. -/
theorem read_steinerNetwork :
    (steinerNetwork c I Acc π).read = {i : Fin n | Reach c (.input i)} := by
  ext i
  change (∃ u : Node c, u ∈ univ ∧ steinerSite c π i = some u) ↔ Reach c (.input i)
  refine ⟨fun ⟨_, _, hu⟩ => (steinerSite_eq_some hu).1, fun hi => ?_⟩
  have h0 : 0 < (support c (.input i hi)).ncard :=
    (ncard_pos (toFinite _)).mpr (support_nonempty (.input i hi))
  exact ⟨supportNode c π (.input i hi) ⟨0, h0⟩, mem_univ _, by simp [steinerSite, hi]⟩

/-- The inputs read in `π.initial t` by `steinerNetwork` equal `nodeReadIn c (π.initial t)`. -/
theorem readIn_steinerNetwork_initial (t : ℕ) :
    (steinerNetwork c I Acc π).readIn (π.initial t) = nodeReadIn c (π.initial t) := by
  ext i
  change (∃ u : Node c, (π u : ℕ) < t ∧ steinerSite c π i = some u) ↔
    ∃ hi : Reach c (.input i), (support c (.input i hi) ∩ π.initial t).Nonempty
  constructor
  · rintro ⟨u, hut, hs⟩
    unfold steinerSite at hs
    split_ifs at hs with hi
    obtain rfl := Option.some.inj hs
    exact ⟨hi, _, supportNode_mem c π (.input i hi) _, hut⟩
  · rintro ⟨hi, u, hu, hut⟩
    rw [Layout.mem_initial] at hut
    have h0 : 0 < (support c (.input i hi)).ncard :=
      (ncard_pos (toFinite _)).mpr (support_nonempty (.input i hi))
    let u0 := supportNode c π (.input i hi) ⟨0, h0⟩
    refine ⟨u0, ?_, by simp [steinerSite, hi, u0]⟩
    have hle : (π u0 : ℕ) ≤ (π u : ℕ) := by
      have h := (pi_supportNode_le_iff (c := c) (π := π) (w := .input i hi)
        (j := ⟨0, h0⟩) (k := supportIndex π hu)).mpr (Fin.mk_le_mk.mpr (Nat.zero_le _))
      rw [supportNode_supportIndex π hu] at h
      exact Fin.le_iff_val_le_val.mp h
    omega

/-- Each node reads at most `max r 1` inputs in `steinerNetwork` when `c.FanInAtMost r`. -/
theorem ncard_readAt_steinerNetwork_le {r : ℕ} (hfan : c.FanInAtMost r) (u : Node c) :
    ((steinerNetwork c I Acc π).readAt u).ncard ≤ max r 1 := by
  classical
  cases u with
  | output o =>
    have h1 : ((steinerNetwork c I Acc π).readAt (.output o)).ncard ≤ 1 := by
      refine (ncard_le_one (toFinite _)).mpr fun i₁ h₁ i₂ h₂ => ?_
      obtain ⟨r₁, m₁⟩ := steinerSite_eq_some h₁
      obtain ⟨r₂, m₂⟩ := steinerSite_eq_some h₂
      have heq : ActiveSignal.input i₁ r₁ = ActiveSignal.input i₂ r₂ :=
        (ncard_le_one (toFinite _)).mp (ncard_activeSignal_mem_support_output_le o)
          (.input i₁ r₁) m₁ (.input i₂ r₂) m₂
      cases heq
      rfl
    exact h1.trans (le_max_right r 1)
  | gate g =>
    let slotWire : Fin (σ.Arity (c.program.lines g.val).op) → Option (Fin n) := fun a =>
      match (c.program.lines g.val).wires a with
      | .input i => some i
      | .gate _ => none
    have hslot : ∀ i ∈ (steinerNetwork c I Acc π).readAt (.gate g),
        ∃ a, slotWire a = some i := by
      intro i hi
      obtain ⟨_, hmem⟩ := steinerSite_eq_some hi
      obtain ⟨t, ht, ho⟩ := hmem
      rcases t with ⟨⟨h, a⟩, hh⟩ | o
      · have hgh : h = g.val := congrArg Subtype.val (Node.gate.inj ho)
        subst hgh
        refine ⟨a, ?_⟩
        have hw : (c.program.lines g.val).wires a = .input i := congrArg Subtype.val ht
        simp [slotWire, hw]
      · cases ho
    calc ((steinerNetwork c I Acc π).readAt (.gate g)).ncard
        ≤ Nat.card (Fin (σ.Arity (c.program.lines g.val).op)) := by
          choose f hf using hslot
          refine (ncard_le_ncard_of_injOn
            (fun i => if h : i ∈ (steinerNetwork c I Acc π).readAt (.gate g) then f i h
              else ⟨0, Nat.pos_of_ne_zero g.property.2⟩)
            (fun _ _ => mem_univ _) (fun i₁ h₁ i₂ h₂ heq => ?_) (toFinite _)).trans_eq
            (ncard_univ _)
          simp only [h₁, h₂, ↓reduceDIte] at heq
          have e1 := hf i₁ h₁
          have e2 := hf i₂ h₂
          rw [heq] at e1
          exact Option.some.inj (e1.symm.trans e2)
      _ ≤ max r 1 := by
          rw [Nat.card_eq_fintype_card, Fintype.card_fin]
          exact (Program.fanInAtMost_iff.mp hfan g.val).trans (le_max_left r 1)

/-- In a satisfying assignment of `steinerNetwork`, all Steiner edges of `w` carry the value at
node `0` of `support c w`. -/
private theorem steiner_edge_eq_zero {x : Fin n → U} {α : SteinerEdge c → U}
    (hα : (steinerNetwork c I Acc π).Satisfies x α) (w : ActiveSignal c)
    (h2 : 2 ≤ (support c w).ncard) :
    ∀ (j : ℕ) (hj : j + 1 < (support c w).ncard),
      α ⟨w, ⟨j, by omega⟩⟩ = α ⟨w, ⟨0, by omega⟩⟩
  | 0, _ => rfl
  | j + 1, hj => by
    let u := supportNode c π w ⟨j + 1, by omega⟩
    have hu : u ∈ support c w := supportNode_mem c π w ⟨j + 1, by omega⟩
    obtain ⟨h1, -, -⟩ := hα u
    have he_out : α ⟨w, ⟨j + 1, by omega⟩⟩ = α (canonicalEdge π hu h2) :=
      h1 ⟨w, ⟨j + 1, by omega⟩⟩ (Or.inl rfl) hu h2
    have he_in : α ⟨w, ⟨j, by omega⟩⟩ = α (canonicalEdge π hu h2) :=
      h1 ⟨w, ⟨j, by omega⟩⟩ (Or.inr rfl) hu h2
    exact (he_out.trans he_in.symm).trans (steiner_edge_eq_zero hα w h2 j (by omega))

/-- Every edge of `w` in a satisfying assignment carries `c.program.trace I x w.wire`. -/
private theorem steiner_eq_trace {x : Fin n → U} {α : SteinerEdge c → U}
    (hα : (steinerNetwork c I Acc π).Satisfies x α) :
    ∀ e : SteinerEdge c, α e = c.program.trace I x e.1.wire := by
  have hval : ∀ (w : Wire n c.size) (hw : Reach c w),
      (∀ u (hu : ∀ aw : ActiveSignal c, aw.wire = w → u ∈ support c aw),
        wireValAt c I π u x α w hw hu = c.program.trace I x w) ∧
      (∀ (aw : ActiveSignal c) (haw : aw.wire = w) (j : Fin ((support c aw).ncard - 1)),
        α ⟨aw, j⟩ = c.program.trace I x w) := by
    refine c.program.wire_induction (fun i hi => ?_) (fun g ih hg => ?_)
    · have hed : ∀ (aw : ActiveSignal c) (haw : aw.wire = .input i)
          (j : Fin ((support c aw).ncard - 1)), α ⟨aw, j⟩ = x i := by
        intro aw haw j
        cases aw with
        | gate _ => cases haw
        | input i' hi' =>
          cases Wire.input.inj haw
          have h2 : 2 ≤ (support c (.input i hi')).ncard := by have := j.isLt; omega
          rw [steiner_edge_eq_zero hα (.input i hi') h2 j.val (by have := j.isLt; omega)]
          let u0 := supportNode c π (.input i hi') ⟨0, by omega⟩
          have hu0 : u0 ∈ support c (.input i hi') := supportNode_mem c π _ _
          have hsite : steinerSite c π i = some u0 := by simp [steinerSite, hi', u0]
          obtain ⟨-, h2_in, -⟩ := hα u0
          have hc0 : canonicalEdge π hu0 h2 = ⟨.input i hi', ⟨0, by omega⟩⟩ := by
            unfold canonicalEdge
            dsimp only
            have hidx : (supportIndex π hu0).val = 0 :=
              congrArg Fin.val (supportIndex_supportNode π (.input i hi') ⟨0, by omega⟩)
            simp [hidx]
          rw [← hc0]
          exact h2_in i hi' hsite hu0 h2
      refine ⟨fun u hu => ?_, hed⟩
      dsimp only [wireValAt]
      split_ifs with h2
      · exact hed _ (congrArg ActiveSignal.wire (canonicalEdge_fst π (hu (.input i hi) rfl) h2)) _
      · rfl
    · by_cases ha0 : σ.Arity (c.program.lines g).op = 0
      · refine ⟨fun u _ => ?_, fun aw haw _ => ?_⟩
        · simp only [wireValAt, ha0, ↓reduceDIte]
          rw [Program.trace_gate]
          exact congrArg _ (funext fun a => absurd a.isLt (by omega))
        · cases aw with
          | input _ _ => cases haw
          | gate g' =>
            cases Wire.gate.inj haw
            exact absurd ha0 g'.property.2
      · let ig : InnerGate c := ⟨g, hg, ha0⟩
        have h2 := two_le_ncard_support_gate ig
        obtain ⟨-, -, h3⟩ := hα (.gate ig)
        dsimp only at h3
        have htrace_g : α (canonicalEdge π (gate_mem_support ig) h2) =
            c.program.trace I x (.gate g) := by
          rw [h3, Program.trace_gate]
          exact congrArg _ (funext fun a => (ih a (.arg a hg)).1 _ _)
        have hed : ∀ (aw : ActiveSignal c) (haw : aw.wire = .gate g)
            (j : Fin ((support c aw).ncard - 1)), α ⟨aw, j⟩ = c.program.trace I x (.gate g) := by
          intro aw haw j
          cases aw with
          | input _ _ => cases haw
          | gate g' =>
            obtain ⟨idx', r', a'⟩ := g'
            cases Wire.gate.inj haw
            have hjlt : j.val + 1 < (support c (.gate ig)).ncard := by
              have hlt : j.val < (support c (.gate ig)).ncard - 1 := j.isLt
              omega
            change α ⟨.gate ig, ⟨j.val, by omega⟩⟩ = c.program.trace I x (.gate g)
            rcases he_can : canonicalEdge π (gate_mem_support ig) h2 with ⟨w_c, j_c⟩
            obtain rfl : w_c = .gate ig :=
              (congrArg Sigma.fst he_can).symm.trans (canonicalEdge_fst π _ h2)
            rw [he_can] at htrace_g
            rw [steiner_edge_eq_zero hα (.gate ig) h2 j.val hjlt,
              ← steiner_edge_eq_zero hα (.gate ig) h2 j_c.val (by have := j_c.isLt; omega)]
            exact htrace_g
        refine ⟨fun u hu => ?_, hed⟩
        simp only [wireValAt, ha0, ↓reduceDIte]
        exact hed _ (congrArg ActiveSignal.wire (canonicalEdge_fst π (hu (.gate ig) rfl) h2)) _
  intro e
  exact (hval e.1.wire e.1.reach).2 e.1 rfl e.2

private theorem wireValAt_trace (u : Node c) (x : Fin n → U) (w : Wire n c.size)
    (hw : Reach c w) (hu : ∀ aw : ActiveSignal c, aw.wire = w → u ∈ support c aw) :
    wireValAt c I π u x (fun e => c.program.trace I x e.1.wire) w hw hu =
      c.program.trace I x w := by
  cases w with
  | input i =>
    dsimp only [wireValAt]
    split_ifs with h2
    · rw [canonicalEdge_fst]
      rfl
    · rfl
  | gate g =>
    dsimp only [wireValAt]
    split_ifs with ha0
    · rw [Program.trace_gate]
      exact congrArg _ (funext fun a => absurd a.isLt (by omega))
    · rw [canonicalEdge_fst]
      rfl

/-- The circuit trace values satisfy `steinerNetwork` when every output lies in `Acc o`. -/
theorem satisfies_steinerNetwork_trace {x : Fin n → U} (hx : ∀ o, c.eval I x o ∈ Acc o) :
    (steinerNetwork c I Acc π).Satisfies x fun e => c.program.trace I x e.1.wire := by
  intro u
  refine ⟨fun e _ hu h2 => by dsimp only; rw [canonicalEdge_fst],
    fun _ _ _ hu h2 => by dsimp only; rw [canonicalEdge_fst]; rfl, ?_⟩
  cases u with
  | gate g =>
    dsimp only
    rw [canonicalEdge_fst, show (ActiveSignal.gate g).wire = .gate g.val from rfl,
      Program.trace_gate]
    exact congrArg _ (funext fun a => (wireValAt_trace _ _ _ _ _).symm)
  | output o =>
    dsimp only
    rw [wireValAt_trace]
    exact hx o

/-- **Exactness of `steinerNetwork`.** -/
theorem satisfies_steinerNetwork_iff {x : Fin n → U} {α : SteinerEdge c → U} :
    (steinerNetwork c I Acc π).Satisfies x α ↔
      (∀ o, c.eval I x o ∈ Acc o) ∧ α = fun e => c.program.trace I x e.1.wire := by
  refine ⟨fun hα => ?_, fun ⟨hx, htr⟩ => htr ▸ satisfies_steinerNetwork_trace (π := π) hx⟩
  have htr : α = fun e => c.program.trace I x e.1.wire := funext (steiner_eq_trace hα)
  refine ⟨fun o => ?_, htr⟩
  obtain ⟨-, -, ho⟩ := hα (.output o)
  dsimp only at ho
  subst htr
  rwa [wireValAt_trace] at ho

/-- `steinerNetwork` accepts an input iff every circuit output lies in `Acc o`. -/
theorem accepted_steinerNetwork :
    (steinerNetwork c I Acc π).accepted = {x | ∀ o, c.eval I x o ∈ Acc o} := by
  ext x
  exact ⟨fun ⟨_, hα⟩ => (satisfies_steinerNetwork_iff.mp hα).1,
    fun hx => ⟨_, satisfies_steinerNetwork_trace (π := π) hx⟩⟩

/-- Single-output specialization of `accepted_steinerNetwork`. -/
theorem accepted_steinerNetwork_single {c : Circuit σ n 1} {Acc : Set U}
    {π : Layout (Node c)} :
    (steinerNetwork c I (fun _ => Acc) π).accepted = {x | c.eval I x 0 ∈ Acc} := by
  rw [accepted_steinerNetwork]
  ext x
  exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩

/-- Every input has at most one satisfying assignment in `steinerNetwork`. -/
theorem satisfies_steinerNetwork_unique {x : Fin n → U} {α β : SteinerEdge c → U}
    (hα : (steinerNetwork c I Acc π).Satisfies x α)
    (hβ : (steinerNetwork c I Acc π).Satisfies x β) : α = β :=
  (satisfies_steinerNetwork_iff.mp hα).2.trans (satisfies_steinerNetwork_iff.mp hβ).2.symm

end Network

end Steiner

end Cslib.Circuits.Frontier.Compiler
