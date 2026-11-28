/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.FanInTwo
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.IndepCount
import CslibFrontier.Computability.Circuit.FanIn
import CslibFrontier.Computability.Circuit.Frontier.Layouts.Components
import CslibFrontier.Foundations.Data.Set.Card
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Ring

/-!
# Forward DAG closure, 2-SAT frontier states, and fan-out slicing

This module develops three structural refinements of the frontier compiler:

1. **Forward DAG closure (`Program.DagSpan`, `Program.depthOneDetermined`,
   `Program.forwardDetermined`).** Along any cut `P` of `Compiler.graph c`, a gate wire on the cut
   whose arguments are already functionally determined by `cutWires c P` carries zero independent
   information across the cut. Removing any subset `D ⊆ c.program.forwardDetermined (cutWires c P)`
   (in particular `D = c.program.depthOneDetermined (cutWires c P)`) preserves exact trace
   agreement on `cutWires c P` (`Program.eqOn_of_eqOn_sdiff_forwardDetermined`) and full output
   splicing (`eval_splice_of_eqOn_cutWires_sdiff`).
2. **2-SAT independent-set frontier bound (`ForbidsOutputPair`, `u2ClauseGraph`,
   `ncard_frontierValues_le_indepSetCount`).** In a Boolean circuit, every gate argument `a` whose
   operation forbids at least one `(arg, out)` value pair (`ForbidsOutputPair`, satisfied on both
   inputs of every `AND`-type `U₂` gate `(u ⊕ c₁) ∧ (v ⊕ c₂) ⊕ c₃`) induces a 2-SAT clause across
   every wire subset `R`. By `SimpleGraph.ncard_le_indepSetCount_of_forall_adj`, the number of
   distinct frontier states at step `t` is bounded by `(u2ClauseGraph c.program I R).indepSetCount`
   on the reduced cut `R = cutWires c (π.initial t) \ D` (`F_{k + 2}` on paths, `2 ^ d + 1` on
   stars).
3. **Unary elimination and universal fan-out slicing (`Program.arityExcess`,
   `Program.gateConsumers`, `exists_sliced_fanout_lt`, `eventually_slicing_surplus`).** Eliminating
   nullary and unary gates and deduplicating repeated arguments inside each gate reduces any
   fan-in-`r` circuit to one whose gates all have arity in `[2, r]` and injective argument wires,
   with gate count bounded by `c.program.arityExcess` (so unary `NOT` gates are free). Repeatedly
   fixing by pigeonhole any wire (input or gate) read by `≥ k` binary gates yields a multi-output
   residual circuit in which every wire feeds `< k` gates (`≤ 4` at `k = 5`) and proves the
   fan-out surplus lower bound `(1 + 1/A - ε) n + (k - (1 + 1/A)) t < c.program.arityExcess`.

## Main definitions

* `Cslib.Circuits.Program.DagSpan`, `Cslib.Circuits.Program.depthOneDetermined`,
  `Cslib.Circuits.Program.forwardDetermined`: forward DAG span and determined cut wires (`D₀`,
  `D*`).
* `Cslib.Circuits.Frontier.cutWires`: the wires carried by edges crossing a vertex cut.
* `Cslib.Circuits.Frontier.ForbidsOutputPair`, `Cslib.Circuits.Frontier.u2ClauseGraph`: forbidden
  input-output pairs and the induced 2-SAT clause graph on a wire set.
* `Cslib.Circuits.allOpsSignature`, `Cslib.Circuits.allOpsInterpretation`: universal graded
  signature over `U`.
* `Cslib.Circuits.Program.arityExcess`, `Cslib.Circuits.Program.gateConsumers`: total arity excess
  `∑ g, (arity(g) - 1)` and number of gates reading a wire.

## Main results

* `Cslib.Circuits.Program.eqOn_of_eqOn_sdiff_forwardDetermined`: trace agreement on `W \ D` implies
  trace agreement on `W` whenever `D ⊆ p.forwardDetermined W`.
* `Cslib.Circuits.Frontier.eval_splice_of_eqOn_cutWires_sdiff`: splicing outputs from agreement on
  `cutWires c P \ D`.
* `Cslib.Circuits.Frontier.ncard_frontierValues_le_indepSetCount`: Boolean frontier states at step
  `t` number at most `(u2ClauseGraph c.program I (cutWires c (π.initial t) \ D)).indepSetCount`.
* `Cslib.Circuits.Frontier.exists_sliced_fanout_lt`: structural fan-out slicing (`gateConsumers < k`
  on every wire, `arityExcess + k * t ≤ c.program.arityExcess`, `|U| ^ t * |S'| ≥ |S|`).
* `Cslib.Circuits.Frontier.eventually_slicing_surplus`,
  `Cslib.Circuits.Frontier.eventually_switched_slicing_surplus`: asymptotic fan-out surplus bounds.
-/

public section

namespace Cslib.Circuits

open Set Filter Asymptotics

universe u v

/-! ### Forward DAG closure (`D₀` and `D*`) -/

section DagClosure

variable {σ : Signature.{v}} {n s : ℕ} {U : Type u}

/-- Wires functionally determined by a base set `B` along the forward gate equations of `p`. -/
inductive Program.DagSpan (p : Program σ n s) (B : Set (Wire n s)) : Wire n s → Prop
  /-- Every wire in `B` lies in the span. -/
  | base {w : Wire n s} : w ∈ B → p.DagSpan B w
  /-- A gate lies in the span whenever all of its argument wires do. -/
  | gate {g : Fin s} : (∀ a, p.DagSpan B ((p.lines g).wires a)) → p.DagSpan B (.gate g)

/-- Depth-one determined wires `D₀(W)`: gate wires in `W` all of whose arguments also lie in `W`. -/
@[expose] def Program.depthOneDetermined (p : Program σ n s) (W : Set (Wire n s)) :
    Set (Wire n s) :=
  {w ∈ W | ∃ g, w = .gate g ∧ ∀ a, (p.lines g).wires a ∈ W}

/-- Full forward-determined wires `D*(W)`: gate wires in `W` all of whose arguments lie in
`p.DagSpan W`. -/
@[expose] def Program.forwardDetermined (p : Program σ n s) (W : Set (Wire n s)) :
    Set (Wire n s) :=
  {w ∈ W | ∃ g, w = .gate g ∧ ∀ a, p.DagSpan W ((p.lines g).wires a)}

/-- `p.forwardDetermined W` is a subset of `W`. -/
theorem Program.forwardDetermined_subset (p : Program σ n s) (W : Set (Wire n s)) :
    p.forwardDetermined W ⊆ W :=
  fun _ h => h.1

/-- `D₀(W) ⊆ D*(W)`: depth-one determined wires are forward-determined. -/
theorem Program.depthOneDetermined_subset_forwardDetermined (p : Program σ n s)
    (W : Set (Wire n s)) : p.depthOneDetermined W ⊆ p.forwardDetermined W := by
  rintro w ⟨hw, g, rfl, hargs⟩
  exact ⟨hw, g, rfl, fun a => .base (hargs a)⟩

/-- Monotonicity of `Program.DagSpan` in the base set. -/
theorem Program.DagSpan.mono {p : Program σ n s} {A B : Set (Wire n s)} (hAB : A ⊆ B)
    {w : Wire n s} (h : p.DagSpan A w) : p.DagSpan B w := by
  induction h with
  | base hw => exact .base (hAB hw)
  | gate _ ih => exact .gate ih

/-- **Acyclic basis reduction (`DagSpan W = DagSpan (W \ D*(W))`).** Because `p` is topologically
ordered, removing all forward-determined wires from `W` leaves the forward DAG span unchanged. -/
theorem Program.dagSpan_sdiff_forwardDetermined (p : Program σ n s) (W : Set (Wire n s)) :
    ∀ {w : Wire n s}, p.DagSpan W w → p.DagSpan (W \ p.forwardDetermined W) w := by
  intro w
  refine p.wire_induction (P := fun w => p.DagSpan W w → p.DagSpan (W \ p.forwardDetermined W) w)
    (fun i hi => ?_) (fun g ih hg => ?_) w
  · cases hi with
    | base hiW =>
      refine .base ⟨hiW, ?_⟩
      rintro ⟨_, g, h, _⟩
      cases h
  · cases hg with
    | gate hargs => exact .gate fun a => ih a (hargs a)
    | base hgW =>
      by_cases hall : ∀ a, p.DagSpan W ((p.lines g).wires a)
      · exact .gate fun a => ih a (hall a)
      · refine .base ⟨hgW, ?_⟩
        rintro ⟨_, g', heq, hargs⟩
        cases Wire.gate.inj heq
        exact hall hargs

/-- Two inputs agreeing on `B` agree on every wire in `p.DagSpan B`. -/
theorem Program.trace_eq_of_dagSpan {p : Program σ n s} {I : Interpretation σ U}
    {x y : Fin n → U} {B : Set (Wire n s)} (hB : EqOn (p.trace I x) (p.trace I y) B)
    {w : Wire n s} (hw : p.DagSpan B w) : p.trace I x w = p.trace I y w := by
  induction hw with
  | base hb => exact hB hb
  | gate _ ih =>
    rw [p.trace_gate, p.trace_gate]
    exact congrArg _ (funext ih)

/-- **Forward closure soundness (`D*`).** If `D ⊆ p.forwardDetermined W`, trace agreement on
`W \ D` forces trace agreement on all of `W`. -/
theorem Program.eqOn_of_eqOn_sdiff_forwardDetermined {p : Program σ n s} {I : Interpretation σ U}
    {W D : Set (Wire n s)} (hD : D ⊆ p.forwardDetermined W) {x y : Fin n → U}
    (heq : EqOn (p.trace I x) (p.trace I y) (W \ D)) : EqOn (p.trace I x) (p.trace I y) W := by
  intro w hw
  have hsub : W \ p.forwardDetermined W ⊆ W \ D :=
    fun _ hu => ⟨hu.1, fun hd => hu.2 (hD hd)⟩
  exact p.trace_eq_of_dagSpan heq ((p.dagSpan_sdiff_forwardDetermined W (.base hw)).mono hsub)

/-- **Depth-one closure soundness (`D₀`).** Trace agreement on `W \ p.depthOneDetermined W` forces
trace agreement on all of `W`. -/
theorem Program.eqOn_of_eqOn_sdiff_depthOneDetermined {p : Program σ n s} {I : Interpretation σ U}
    {W : Set (Wire n s)} {x y : Fin n → U}
    (heq : EqOn (p.trace I x) (p.trace I y) (W \ p.depthOneDetermined W)) :
    EqOn (p.trace I x) (p.trace I y) W :=
  p.eqOn_of_eqOn_sdiff_forwardDetermined (p.depthOneDetermined_subset_forwardDetermined W) heq

/-- Removing `D ⊆ p.forwardDetermined W` reduces the wire count by `D.ncard`. -/
theorem Program.ncard_sdiff_add_ncard_of_subset_forwardDetermined {p : Program σ n s}
    {W D : Set (Wire n s)} (hD : D ⊆ p.forwardDetermined W) :
    (W \ D).ncard + D.ncard = W.ncard :=
  ncard_sdiff_add_ncard_of_subset (hD.trans (p.forwardDetermined_subset W)) (toFinite W)

end DagClosure

namespace Frontier

/-! ### Splicing and 2-SAT independent-set bounds across reduced cuts -/

section CutClosure

variable {σ : Signature.{v}} {n m : ℕ} {U : Type u}

/-- The set of circuit wires carried by the edges crossing a vertex cut `P`. -/
@[expose] noncomputable def cutWires (c : Circuit σ n m) (P : Set (Compiler.Vertex c)) :
    Set (Wire n c.size) :=
  (fun e : Compiler.Edge c => e.signal.val) '' (Compiler.graph c).edgeCut P

/-- **Splicing across a forward-reduced cut.** If `D ⊆ c.program.forwardDetermined (cutWires c P)`
and `x` and `y` agree on `cutWires c P \ D`, then splicing `x` inside `P` with `y` outside `P`
produces outputs matching `x` inside `P` and `y` outside `P`. -/
theorem eval_splice_of_eqOn_cutWires_sdiff {c : Circuit σ n m} {I : Interpretation σ U}
    {P : Set (Compiler.Vertex c)} {D : Set (Wire n c.size)}
    (hD : D ⊆ c.program.forwardDetermined (cutWires c P)) {x y z : Fin n → U}
    (hcut : EqOn (c.program.trace I x) (c.program.trace I y) (cutWires c P \ D))
    (hzx : EqOn z x ((Compiler.network c I fun _ => univ).readIn P))
    (hzy : EqOn z y ((Compiler.network c I fun _ => univ).readIn P)ᶜ) (o : Fin m) :
    (Compiler.Vertex.output o ∈ P → c.eval I z o = c.eval I x o) ∧
      (Compiler.Vertex.output o ∉ P → c.eval I z o = c.eval I y o) := by
  have hall := c.program.eqOn_of_eqOn_sdiff_forwardDetermined hD hcut
  exact Compiler.eval_splice (fun e he => hall ⟨e, he, rfl⟩) hzx hzy o

/-- Frontier edge values at layout step `t` are uniquely determined by the trace restricted to
`cutWires c (π.initial t) \ D` for any `D ⊆ c.program.forwardDetermined (cutWires c (π.initial t))`.
-/
theorem frontierValues_eq_of_eqOn_cutWires_sdiff {c : Circuit σ n m} {I : Interpretation σ U}
    {Acc : Fin m → Set U} (π : Layout (Compiler.Vertex c)) {t : ℕ}
    {D : Set (Wire n c.size)}
    (hD : D ⊆ c.program.forwardDetermined (cutWires c (π.initial t))) {x y : Fin n → U}
    (heq : EqOn (c.program.trace I x) (c.program.trace I y) (cutWires c (π.initial t) \ D)) :
    (Compiler.network c I Acc).frontierValues π t (fun e => c.program.trace I x e.signal.val) =
      (Compiler.network c I Acc).frontierValues π t
          (fun e => c.program.trace I y e.signal.val) := by
  have hall := c.program.eqOn_of_eqOn_sdiff_forwardDetermined hD heq
  exact ((Compiler.network c I Acc).frontierValues_eq_iff π).mpr fun e he => hall ⟨e, he, rfl⟩

/-- A Boolean operation `f : (Fin k → Bool) → Bool` *forbids an output pair* on argument `a` when
some pair `(ba, bz) ∈ Bool × Bool` never occurs as `(v a, f v)`. Every `AND`-type binary gate
`(v 0 ⊕ c₁) && (v 1 ⊕ c₂) ⊕ c₃` satisfies this on both arguments, whereas `XOR` and `XNOR` do
not. -/
@[expose] def ForbidsOutputPair {k : ℕ} (f : (Fin k → Bool) → Bool) (a : Fin k) : Prop :=
  ∃ ba bz : Bool, ∀ v : Fin k → Bool, ¬(v a = ba ∧ f v = bz)

/-- Every `AND`-type `U₂` operation `(v 0 ⊕ c₁) && (v 1 ⊕ c₂) ⊕ c₃` forbids a pair on each of its
two arguments (`(c₁, !c₃)` on argument `0`, `(c₂, !c₃)` on argument `1`). -/
theorem forbidsOutputPair_u2 (c₁ c₂ c₃ : Bool) (a : Fin 2) :
    ForbidsOutputPair (fun v : Fin 2 → Bool => xor (((xor (v 0) c₁) && (xor (v 1) c₂))) c₃) a := by
  have ha : a = 0 ∨ a = 1 := by
    have := a.isLt
    omega
  rcases ha with rfl | rfl
  · refine ⟨c₁, !c₃, fun v ⟨h0, hz⟩ => ?_⟩
    dsimp only at hz
    rw [h0] at hz
    cases c₁ <;> cases c₃ <;> simp at hz
  · refine ⟨c₂, !c₃, fun v ⟨h1, hz⟩ => ?_⟩
    dsimp only at hz
    rw [h1] at hz
    cases c₂ <;> cases c₃ <;> simp at hz

/-- Conjunction (`&&`) forbids `(false, true)` on both arguments. -/
theorem forbidsOutputPair_and (a : Fin 2) :
    ForbidsOutputPair (fun v : Fin 2 → Bool => v 0 && v 1) a := by
  simpa using forbidsOutputPair_u2 false false false a

/-- Disjunction (`||`) forbids `(true, false)` on both arguments (`!( !u && !w )`). -/
theorem forbidsOutputPair_or (a : Fin 2) :
    ForbidsOutputPair (fun v : Fin 2 → Bool => v 0 || v 1) a := by
  have h := forbidsOutputPair_u2 true true true a
  convert h using 1
  funext v
  cases v 0 <;> cases v 1 <;> rfl

/-- Directed forbidden-pair edge between wires `u` and `w` in `p`: `w = .gate g` reads `u` in some
slot `a` whose gate operation forbids an output pair on `a`. -/
@[expose] def ClauseEdge {s : ℕ} (p : Program σ n s) (I : Interpretation σ Bool)
    (u w : Wire n s) : Prop :=
  ∃ (g : Fin s) (a : Fin (σ.Arity (p.lines g).op)),
    w = .gate g ∧ (p.lines g).wires a = u ∧ ForbidsOutputPair (I (p.lines g).op) a

/-- No wire has a `ClauseEdge` to itself, by topological acyclicity of `p`. -/
private theorem clauseEdge_irrefl {s : ℕ} (p : Program σ n s) (I : Interpretation σ Bool)
    (u : Wire n s) : ¬ClauseEdge p I u u := by
  rintro ⟨g, a, rfl, hwire, _⟩
  exact (p.lt_of_lines_wires_eq_gate g a g hwire).ne rfl

/-- **The 2-SAT clause graph on a wire set `R`.** Two wires in `R` are adjacent when one is a gate
reading the other through an argument slot satisfying `ForbidsOutputPair`. -/
def u2ClauseGraph {s : ℕ} (p : Program σ n s) (I : Interpretation σ Bool)
    (R : Set (Wire n s)) : SimpleGraph R where
  Adj u w := ClauseEdge p I u.val w.val ∨ ClauseEdge p I w.val u.val
  symm := ⟨fun _ _ h => Or.symm h⟩
  loopless := ⟨fun u h => h.elim (clauseEdge_irrefl p I u.val) (clauseEdge_irrefl p I u.val)⟩

@[simp] theorem u2ClauseGraph_adj {s : ℕ} (p : Program σ n s) (I : Interpretation σ Bool)
    (R : Set (Wire n s)) (u w : R) :
    (u2ClauseGraph p I R).Adj u w ↔ ClauseEdge p I u.val w.val ∨ ClauseEdge p I w.val u.val :=
  Iff.rfl

/-- **Trace projections on `R` are bounded by `i(u2ClauseGraph p I R)`.** Every edge of
`u2ClauseGraph p I R` forbids at least one pair of Boolean values across all program traces, so at
most `(u2ClauseGraph p I R).indepSetCount` distinct restrictions occur on `R`. -/
theorem ncard_trace_domRestrict_le_indepSetCount {s : ℕ} (p : Program σ n s)
    (I : Interpretation σ Bool) (R : Set (Wire n s)) (X : Set (Fin n → Bool)) :
    ((fun x => R.domRestrict (p.trace I x)) '' X).ncard ≤
      (u2ClauseGraph p I R).indepSetCount := by
  refine SimpleGraph.ncard_le_indepSetCount_of_forall_adj (u2ClauseGraph p I R) ?_
  rintro u w (⟨g, a, hw, hu, ba, bz, hforb⟩ | ⟨g, a, hu, hw, ba, bz, hforb⟩)
  · refine ⟨ba, bz, ?_⟩
    rintro _ ⟨x, -, rfl⟩ ⟨hxu, hxw⟩
    simp only [Set.domRestrict_apply] at hxu hxw
    rw [hw, p.trace_gate] at hxw
    exact hforb (fun b => p.trace I x ((p.lines g).wires b)) ⟨hu ▸ hxu, hxw⟩
  · refine ⟨bz, ba, ?_⟩
    rintro _ ⟨x, -, rfl⟩ ⟨hxu, hxw⟩
    simp only [Set.domRestrict_apply] at hxu hxw
    rw [hu, p.trace_gate] at hxu
    exact hforb (fun b => p.trace I x ((p.lines g).wires b)) ⟨hw ▸ hxw, hxu⟩

/-- **Combined `D*(∂)` + `2-SAT` `i(H)` frontier state bound.** Along any layout `π` of a Boolean
circuit `c`, after dropping any forward-determined wire subset
`D ⊆ c.program.forwardDetermined (cutWires c (π.initial t))` (including `D₀`), the number of
distinct frontier states at step `t` across `X` is at most
`(u2ClauseGraph c.program I (cutWires c (π.initial t) \ D)).indepSetCount`. -/
theorem ncard_frontierValues_le_indepSetCount (c : Circuit σ n m) (I : Interpretation σ Bool)
    (Acc : Fin m → Set Bool) (π : Layout (Compiler.Vertex c)) (t : ℕ)
    {D : Set (Wire n c.size)}
    (hD : D ⊆ c.program.forwardDetermined (cutWires c (π.initial t)))
    (X : Set (Fin n → Bool)) :
    ((fun x => (Compiler.network c I Acc).frontierValues π t
        (fun e => c.program.trace I x e.signal.val)) '' X).ncard ≤
      (u2ClauseGraph c.program I (cutWires c (π.initial t) \ D)).indepSetCount := by
  set R := cutWires c (π.initial t) \ D
  refine (ncard_image_le_ncard_image_of_factorsThrough (g := fun x => R.domRestrict
    (c.program.trace I x)) (toFinite X) fun x _ y _ hxy => ?_).trans
      (ncard_trace_domRestrict_le_indepSetCount c.program I R X)
  exact frontierValues_eq_of_eqOn_cutWires_sdiff π hD (domRestrict_eq_domRestrict_iff.mp hxy)

end CutClosure

end Frontier

/-! ### Universal graded signature, arity excess, and fan-out slicing -/

/-- The universal graded signature on `U`, with an `a`-ary operation symbol for every `a : ℕ` and
every function `(Fin a → U) → U`. -/
abbrev allOpsSignature (U : Type u) : Signature.{u} where
  Op := Σ a : ℕ, (Fin a → U) → U
  Arity op := op.1

/-- Canonical evaluation of `allOpsSignature U`. -/
@[expose] def allOpsInterpretation (U : Type u) : Interpretation (allOpsSignature U) U :=
  fun op args => op.2 args

section ArityExcess

variable {σ : Signature.{v}} {n s : ℕ} {U : Type u}

/-- Total arity excess `∑ g, (arity(g) - 1)` of a program. Nullary constants and unary operations
(such as `NOT`) contribute `0`; binary gates contribute `1`; `r`-ary gates contribute `r - 1`. -/
@[expose] def Program.arityExcess (p : Program σ n s) : ℕ :=
  ∑ g : Fin s, (σ.Arity (p.lines g).op - 1)

@[simp] theorem Program.arityExcess_empty : (Program.empty : Program σ n 0).arityExcess = 0 :=
  rfl

@[simp] theorem Program.arityExcess_gate (p : Program σ n s) (line : Line σ n s) :
    (p.gate line).arityExcess = p.arityExcess + (σ.Arity line.op - 1) := by
  simp [Program.arityExcess, Fin.sum_univ_castSucc]

/-- For fan-in at most `r`, `p.arityExcess ≤ (r - 1) * p.innerGates.card`. -/
theorem Program.arityExcess_le_mul_innerGates {p : Program σ n s} {r : ℕ}
    (hfan : p.FanInAtMost r) : p.arityExcess ≤ (r - 1) * p.innerGates.card := by
  rw [Program.arityExcess, ← Finset.sum_subset (Finset.subset_univ p.innerGates)]
  · calc ∑ g ∈ p.innerGates, (σ.Arity (p.lines g).op - 1)
        ≤ ∑ _g ∈ p.innerGates, (r - 1) := by
          refine Finset.sum_le_sum fun g _ => ?_
          have := Program.fanInAtMost_iff.mp hfan g
          omega
      _ = (r - 1) * p.innerGates.card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
  · intro g _ hg
    have h0 : σ.Arity (p.lines g).op = 0 := not_not.mp (mt Program.mem_innerGates.mpr hg)
    simp [h0]

/-- The number of gates in `p` that read wire `w` in at least one argument slot. -/
@[expose] def Program.gateConsumers (p : Program σ n s) (w : Wire n s) : ℕ :=
  (Finset.univ.filter fun g : Fin s => ∃ a, (p.lines g).wires a = w).card

/-- Excess drop when `w` is fixed across `p`: each gate `g` drops by
`min #{a | wires g a = w} (arity(g) - 1)`. -/
@[expose] def Program.excessConsumers (p : Program σ n s) (w : Wire n s) : ℕ :=
  ∑ g : Fin s, min (Finset.univ.filter fun a => (p.lines g).wires a = w).card
    (σ.Arity (p.lines g).op - 1)

/-- When every gate of `p` has arity at least `2`, every gate reading `w` contributes at least `1`
to `p.excessConsumers w`. -/
theorem Program.gateConsumers_le_excessConsumers {p : Program σ n s}
    (h2 : ∀ g : Fin s, 2 ≤ σ.Arity (p.lines g).op) (w : Wire n s) :
    p.gateConsumers w ≤ p.excessConsumers w := by
  rw [Program.gateConsumers, Finset.card_eq_sum_ones, Program.excessConsumers,
    ← Finset.sum_subset (Finset.subset_univ _)]
  · refine Finset.sum_le_sum fun g hg => ?_
    obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hg).2
    have hcard : 1 ≤ (Finset.univ.filter fun b => (p.lines g).wires b = w).card :=
      Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨Finset.mem_univ a, ha⟩⟩
    have har := h2 g
    omega
  · intro g _ hg
    have hcard : (Finset.univ.filter fun b => (p.lines g).wires b = w).card = 0 := by
      rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      intro a ha
      exact hg (Finset.mem_filter.mpr ⟨Finset.mem_univ g, a, (Finset.mem_filter.mp ha).2⟩)
    simp [hcard]

/-! #### Eliminating nullary/unary gates and deduplicating parallel gate inputs -/

@[simp] private theorem wire_lastCases_last {g : ℕ} {motive : Wire n (g + 1) → Sort*}
    (last : motive (.gate (Fin.last g))) (castSucc : ∀ w : Wire n g, motive w.castSucc) :
    Wire.lastCases last castSucc (.gate (Fin.last g)) = last := by
  unfold Wire.lastCases
  exact Fin.lastCases_last

@[simp] private theorem wire_lastCases_castSucc {g : ℕ} {motive : Wire n (g + 1) → Sort*}
    (last : motive (.gate (Fin.last g))) (castSucc : ∀ w : Wire n g, motive w.castSucc)
    (w : Wire n g) : Wire.lastCases last castSucc w.castSucc = castSucc w := by
  cases w with
  | input _ => rfl
  | gate j =>
    unfold Wire.lastCases
    exact Fin.lastCases_castSucc j

/-- Representation of an old wire as either a constant or a unary function of a reduced wire. -/
private abbrev WireRep (U : Type u) (n g' : ℕ) :=
  U ⊕ (Wire n g' × (U → U))

private def WireRep.eval {g' : ℕ} (q : Program (allOpsSignature U) n g') (x : Fin n → U) :
    WireRep U n g' → U
  | .inl u => u
  | .inr (w', f) => f (q.trace (allOpsInterpretation U) x w')

private def WireRep.castSucc {g' : ℕ} : WireRep U n g' → WireRep U n (g' + 1)
  | .inl u => .inl u
  | .inr (w', f) => .inr (w'.castSucc, f)

private def WireRep.getConst {g' : ℕ} :
    (r : WireRep U n g') → (∀ w' f, r ≠ .inr (w', f)) → U
  | .inl u, _ => u
  | .inr (w', f), h => False.elim (h w' f rfl)

private theorem WireRep.getConst_eq_eval {g' : ℕ} (q : Program (allOpsSignature U) n g')
    (x : Fin n → U) : ∀ (r : WireRep U n g') (h : ∀ w' f, r ≠ .inr (w', f)),
      r.getConst h = WireRep.eval q x r
  | .inl _, _ => rfl
  | .inr (w', f), h => False.elim (h w' f rfl)

private def WireRep.evalAtTargets {g' : ℕ} {targets : Finset (Wire n g')}
    (emb : Fin targets.card ≃ targets) (v : Fin targets.card → U) :
    (r : WireRep U n g') → (∀ w' f, r = .inr (w', f) → w' ∈ targets) → U
  | .inl u, _ => u
  | .inr (w', f), hw => f (v (emb.symm ⟨w', hw w' f rfl⟩))

private theorem WireRep.evalAtTargets_eq_eval {g' : ℕ} (q : Program (allOpsSignature U) n g')
    {targets : Finset (Wire n g')} (emb : Fin targets.card ≃ targets) (x : Fin n → U) :
    ∀ (r : WireRep U n g') (hw : ∀ w' f, r = .inr (w', f) → w' ∈ targets),
      WireRep.evalAtTargets emb (fun i => q.trace (allOpsInterpretation U) x (emb i).val) r hw =
        WireRep.eval q x r
  | .inl _, _ => rfl
  | .inr (_, _), _ => by simp [WireRep.evalAtTargets, WireRep.eval]

private theorem WireRep.eval_castSucc {g' : ℕ} (q : Program (allOpsSignature U) n g')
    (l' : Line (allOpsSignature U) n g') (x : Fin n → U) (r : WireRep U n g') :
    WireRep.eval (q.gate l') x r.castSucc = WireRep.eval q x r := by
  cases r with
  | inl _ => rfl
  | inr wf =>
    simp [WireRep.eval, WireRep.castSucc, Program.trace_gate_castSucc]

private structure ReducedProgram (p : Program σ n s) (I : Interpretation σ U) where
  size : ℕ
  program : Program (allOpsSignature U) n size
  rep : Wire n s → WireRep U n size
  eval_rep : ∀ x w, WireRep.eval program x (rep w) = p.trace I x w
  two_le_arity : ∀ k : Fin size, 2 ≤ (allOpsSignature U).Arity (program.lines k).op
  arity_le : ∀ k : Fin size, ∃ k₀ : Fin s,
    (allOpsSignature U).Arity (program.lines k).op ≤ σ.Arity (p.lines k₀).op
  wires_injective : ∀ k : Fin size, Function.Injective (program.lines k).wires
  arityExcess_le : program.arityExcess ≤ p.arityExcess

private noncomputable def elimUnaryAux (I : Interpretation σ U) :
    ∀ {s : ℕ} (p : Program σ n s), ReducedProgram p I
  | _, .empty =>
    { size := 0
      program := .empty
      rep := fun w => match w with
        | .input i => .inr (.input i, id)
        | .gate k => k.elim0
      eval_rep := fun _ w => by cases w with | input => rfl | gate k => exact k.elim0
      two_le_arity := fun k => k.elim0
      arity_le := fun k => k.elim0
      wires_injective := fun k => k.elim0
      arityExcess_le := le_rfl }
  | _, @Program.gate _ _ s₀ p₀ line =>
    let ih := elimUnaryAux I p₀
    let targets : Finset (Wire n ih.size) :=
      Finset.univ.biUnion fun a : Fin (σ.Arity line.op) =>
        match ih.rep (line.wires a) with
        | .inl _ => ∅
        | .inr (w', _) => {w'}
    have hcard_le : targets.card ≤ σ.Arity line.op := by
      calc targets.card
          ≤ ∑ a : Fin (σ.Arity line.op),
              (match ih.rep (line.wires a) with
                | .inl _ => (∅ : Finset (Wire n ih.size))
                | .inr (w', _) => {w'}).card := Finset.card_biUnion_le
        _ ≤ ∑ _a : Fin (σ.Arity line.op), 1 := by
            refine Finset.sum_le_sum fun a _ => ?_
            cases ih.rep (line.wires a) <;> simp
        _ = σ.Arity line.op := by simp
    if hd0 : targets.card = 0 then
      have hconst (a : Fin (σ.Arity line.op)) : ∀ w' f, ih.rep (line.wires a) ≠ .inr (w', f) := by
        intro w' f hrep
        have hw' : w' ∈ targets :=
          Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, by simp [hrep]⟩
        exact absurd hw' (Finset.card_eq_zero.mp hd0 ▸ Finset.notMem_empty w')
      let u_new : U := I line.op fun a => WireRep.getConst (ih.rep (line.wires a)) (hconst a)
      { size := ih.size
        program := ih.program
        rep := fun w => Wire.lastCases (.inl u_new) (fun v => ih.rep v) w
        eval_rep := fun x w => by
          refine Wire.lastCases ?_ (fun v => ?_) w
          · rw [wire_lastCases_last, Program.trace_gate_last]
            change u_new = _
            refine congrArg (I line.op) (funext fun a => ?_)
            rw [← ih.eval_rep x (line.wires a)]
            exact WireRep.getConst_eq_eval ih.program x (ih.rep (line.wires a)) (hconst a)
          · rw [wire_lastCases_castSucc, Program.trace_gate_castSucc]
            exact ih.eval_rep x v
        two_le_arity := ih.two_le_arity
        arity_le := fun k => by
          obtain ⟨k₀, hk₀⟩ := ih.arity_le k
          exact ⟨k₀.castSucc, by simpa using hk₀⟩
        wires_injective := ih.wires_injective
        arityExcess_le := by
          rw [Program.arityExcess_gate]
          exact ih.arityExcess_le.trans (Nat.le_add_right _ _) }
    else if hd1 : targets.card = 1 then
      let emb : Fin targets.card ≃ targets := targets.equivFin.symm
      let w'₀ : Wire n ih.size := (emb ⟨0, by omega⟩).val
      let F : U → U := fun val => I line.op fun a =>
        match ih.rep (line.wires a) with
        | .inl u => u
        | .inr (_, f) => f val
      { size := ih.size
        program := ih.program
        rep := fun w => Wire.lastCases (.inr (w'₀, F)) (fun v => ih.rep v) w
        eval_rep := fun x w => by
          refine Wire.lastCases ?_ (fun v => ?_) w
          · rw [wire_lastCases_last, Program.trace_gate_last]
            change F (ih.program.trace (allOpsInterpretation U) x w'₀) = _
            refine congrArg (I line.op) (funext fun a => ?_)
            rw [← ih.eval_rep x (line.wires a)]
            cases h : ih.rep (line.wires a) with
            | inl u => rfl
            | inr wf =>
              obtain ⟨w', f⟩ := wf
              have hw' : w' ∈ targets :=
                Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, by simp [h]⟩
              have : Subsingleton (Fin targets.card) :=
                Fintype.card_le_one_iff_subsingleton.mp (by simp [hd1])
              have : Subsingleton targets := emb.symm.injective.subsingleton
              have heq : (⟨w', hw'⟩ : targets) = emb ⟨0, by omega⟩ := Subsingleton.elim _ _
              exact congrArg (fun z => f (ih.program.trace (allOpsInterpretation U) x z))
                (congrArg Subtype.val heq).symm
          · rw [wire_lastCases_castSucc, Program.trace_gate_castSucc]
            exact ih.eval_rep x v
        two_le_arity := ih.two_le_arity
        arity_le := fun k => by
          obtain ⟨k₀, hk₀⟩ := ih.arity_le k
          exact ⟨k₀.castSucc, by simpa using hk₀⟩
        wires_injective := ih.wires_injective
        arityExcess_le := by
          rw [Program.arityExcess_gate]
          exact ih.arityExcess_le.trans (Nat.le_add_right _ _) }
    else
      have hd2 : 2 ≤ targets.card := by omega
      let emb : Fin targets.card ≃ targets := targets.equivFin.symm
      have hmem_t (a : Fin (σ.Arity line.op)) :
          ∀ w' f, ih.rep (line.wires a) = .inr (w', f) → w' ∈ targets :=
        fun w' _ h => Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, by simp [h]⟩
      let l' : Line (allOpsSignature U) n ih.size :=
        { op := ⟨targets.card, fun v => I line.op fun a =>
            WireRep.evalAtTargets emb v (ih.rep (line.wires a)) (hmem_t a)⟩
          wires := fun i => (emb i).val }
      { size := ih.size + 1
        program := ih.program.gate l'
        rep := fun w => Wire.lastCases (.inr (.gate (Fin.last ih.size), id))
          (fun v => (ih.rep v).castSucc) w
        eval_rep := fun x w => by
          refine Wire.lastCases ?_ (fun v => ?_) w
          · rw [wire_lastCases_last, Program.trace_gate_last]
            change (ih.program.gate l').trace (allOpsInterpretation U) x
              (.gate (Fin.last ih.size)) = _
            rw [Program.trace_gate_last]
            refine congrArg (I line.op) (funext fun a => ?_)
            rw [← ih.eval_rep x (line.wires a)]
            exact WireRep.evalAtTargets_eq_eval ih.program emb x (ih.rep (line.wires a)) (hmem_t a)
          · rw [wire_lastCases_castSucc, Program.trace_gate_castSucc]
            exact (WireRep.eval_castSucc ih.program l' x (ih.rep v)).trans (ih.eval_rep x v)
        two_le_arity := fun k => by
          refine Fin.lastCases ?_ (fun k => ?_) k
          · simpa [l'] using hd2
          · simpa using ih.two_le_arity k
        arity_le := fun k => by
          refine Fin.lastCases ?_ (fun k => ?_) k
          · exact ⟨Fin.last s₀, by simpa [l'] using hcard_le⟩
          · obtain ⟨k₀, hk₀⟩ := ih.arity_le k
            exact ⟨k₀.castSucc, by simpa using hk₀⟩
        wires_injective := fun k => by
          refine Fin.lastCases ?_ (fun k => ?_) k
          · rw [Program.lines_gate_last]
            intro i j hij
            have h1 := Wire.castSucc_injective hij
            exact emb.injective (Subtype.ext h1)
          · rw [Program.lines_gate_castSucc]
            exact Wire.castSucc_injective.comp (ih.wires_injective k)
        arityExcess_le := by
          rw [Program.arityExcess_gate, Program.arityExcess_gate]
          have h1 : (allOpsSignature U).Arity l'.op - 1 ≤ σ.Arity line.op - 1 := by
            change targets.card - 1 ≤ σ.Arity line.op - 1
            omega
          exact Nat.add_le_add ih.arityExcess_le h1 }

/-! #### Currying a fixed wire across a program -/

private noncomputable def curryLine {g : ℕ} (u₀ : U) (w₀ : Wire n g)
    (l : Line (allOpsSignature U) n g) : Line (allOpsSignature U) n g :=
  let kept := {a : Fin l.op.1 // l.wires a ≠ w₀}
  let emb : Fin (Fintype.card kept) ≃ kept := (Fintype.equivFin kept).symm
  { op := ⟨Fintype.card kept, fun v => l.op.2 fun a =>
      if h : l.wires a = w₀ then u₀ else v (emb.symm ⟨a, h⟩)⟩
    wires := fun i => l.wires (emb i).val }

private theorem curryLine_eval {g : ℕ} (u₀ : U) (w₀ : Wire n g)
    (l : Line (allOpsSignature U) n g) (x : Fin n → U) (gates : Fin g → U)
    (hw₀ : Wire.elim x gates w₀ = u₀) :
    (curryLine u₀ w₀ l).eval (allOpsInterpretation U) x gates =
      l.eval (allOpsInterpretation U) x gates := by
  simp only [Line.eval, curryLine, allOpsInterpretation, Function.comp_def]
  refine congrArg l.op.2 (funext fun a => ?_)
  by_cases h : l.wires a = w₀
  · simp [h, ← hw₀]
  · simp [h]

private theorem curryLine_arity_le {g : ℕ} (u₀ : U) (w₀ : Wire n g)
    (l : Line (allOpsSignature U) n g) :
    (curryLine u₀ w₀ l).op.1 ≤ l.op.1 := by
  simp [curryLine]

private theorem curryLine_arity_sub_one_add {g : ℕ} (u₀ : U) (w₀ : Wire n g)
    (l : Line (allOpsSignature U) n g) :
    ((curryLine u₀ w₀ l).op.1 - 1) +
      min (Finset.univ.filter fun a => l.wires a = w₀).card (l.op.1 - 1) = l.op.1 - 1 := by
  set c := (Finset.univ.filter fun a : Fin l.op.1 => l.wires a = w₀).card
  set b := Fintype.card {a : Fin l.op.1 // l.wires a ≠ w₀}
  set a := l.op.1
  have hsum : c + b = a := by
    simp only [c, b, a, Fintype.card_subtype]
    simpa using Finset.card_filter_add_card_filter_not (s := Finset.univ)
      (p := fun x : Fin l.op.1 => l.wires x = w₀)
  change (b - 1) + min c (a - 1) = a - 1
  omega

private noncomputable def curryProgram (u₀ : U) :
    ∀ {s : ℕ}, Program (allOpsSignature U) n s → Wire n s → Program (allOpsSignature U) n s
  | _, .empty, _ => .empty
  | _, @Program.gate _ _ g q line, w₀ =>
    Wire.lastCases (q.gate line)
      (fun w₀' => (curryProgram u₀ q w₀').gate (curryLine u₀ w₀' line)) w₀

private theorem curryProgram_eval {s : ℕ} (u₀ : U) (p : Program (allOpsSignature U) n s)
    (w₀ : Wire n s) (x : Fin n → U)
    (hw₀ : p.trace (allOpsInterpretation U) x w₀ = u₀) :
    (curryProgram u₀ p w₀).eval (allOpsInterpretation U) x =
      p.eval (allOpsInterpretation U) x := by
  induction p with
  | empty => exact Subsingleton.elim _ _
  | @gate g q line ih =>
    revert hw₀
    refine Wire.lastCases ?_ (fun w₀' => ?_) w₀
    · intro _
      simp [curryProgram]
    · intro hw₀
      simp only [curryProgram, wire_lastCases_castSucc]
      have hw₀' : q.trace (allOpsInterpretation U) x w₀' = u₀ := by
        rwa [Program.trace_gate_castSucc] at hw₀
      have hih := ih w₀' hw₀'
      funext k
      refine Fin.lastCases ?_ (fun k => ?_) k
      · rw [Program.eval_gate_last, Program.eval_gate_last, hih]
        exact curryLine_eval u₀ w₀' line x (q.eval (allOpsInterpretation U) x) hw₀'
      · rw [Program.eval_gate_castSucc, Program.eval_gate_castSucc, hih]

private theorem curryProgram_trace {s : ℕ} (u₀ : U) (p : Program (allOpsSignature U) n s)
    (w₀ : Wire n s) (x : Fin n → U)
    (hw₀ : p.trace (allOpsInterpretation U) x w₀ = u₀) :
    (curryProgram u₀ p w₀).trace (allOpsInterpretation U) x =
      p.trace (allOpsInterpretation U) x := by
  funext w
  cases w with
  | input _ => rfl
  | gate k =>
    exact congrFun (curryProgram_eval u₀ p w₀ x hw₀) k

private theorem curryProgram_trace_self {s : ℕ} (u₀ : U) (p : Program (allOpsSignature U) n s)
    (w₀ : Wire n s) (x : Fin n → U) :
    (curryProgram u₀ p w₀).trace (allOpsInterpretation U) x w₀ =
      p.trace (allOpsInterpretation U) x w₀ := by
  induction p with
  | empty => rfl
  | gate q line ih =>
    refine Wire.lastCases ?_ (fun w₀' => ?_) w₀
    · simp [curryProgram]
    · simp only [curryProgram, wire_lastCases_castSucc, Program.trace_gate_castSucc]
      exact ih w₀'

private theorem curryProgram_fanInAtMost {s r : ℕ} (u₀ : U) (p : Program (allOpsSignature U) n s)
    (w₀ : Wire n s) (hfan : p.FanInAtMost r) :
    (curryProgram u₀ p w₀).FanInAtMost r := by
  induction p with
  | empty => trivial
  | gate q line ih =>
    refine Wire.lastCases ?_ (fun w₀' => ?_) w₀
    · simpa [curryProgram] using hfan
    · simp only [curryProgram, wire_lastCases_castSucc]
      exact ⟨ih w₀' hfan.1, (curryLine_arity_le u₀ w₀' line).trans hfan.2⟩

private theorem mapWires_castSucc_filter_card {σ : Signature.{v}} {g : ℕ}
    (l : Line σ n g) (w₀' : Wire n g) :
    (Finset.univ.filter fun a =>
      (l.mapWires Wire.Renaming.castSucc.apply).wires a = w₀'.castSucc).card =
      (Finset.univ.filter fun a => l.wires a = w₀').card := by
  rcases l with ⟨op, wires⟩
  have hmap : ({ op := op, wires := wires } : Line σ n g).mapWires Wire.Renaming.castSucc.apply =
      { op := op, wires := Wire.Renaming.castSucc.apply ∘ wires } := rfl
  rw [hmap]
  congr 1
  ext a
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply,
    Wire.Renaming.castSucc_apply, Wire.castSucc_injective.eq_iff]

private theorem curryProgram_arityExcess_add {s : ℕ} (u₀ : U)
    (p : Program (allOpsSignature U) n s) (w₀ : Wire n s) :
    (curryProgram u₀ p w₀).arityExcess + p.excessConsumers w₀ = p.arityExcess := by
  induction p with
  | empty => rfl
  | @gate g q line ih =>
    refine Wire.lastCases ?_ (fun w₀' => ?_) w₀
    · have hzero : (q.gate line).excessConsumers (.gate (Fin.last g)) = 0 := by
        rw [Program.excessConsumers]
        refine Finset.sum_eq_zero fun k _ => ?_
        have hcard : (Finset.univ.filter fun a =>
            ((q.gate line).lines k).wires a = .gate (Fin.last g)).card = 0 := by
          rw [Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
          intro a ha
          have hlt := (q.gate line).lt_of_lines_wires_eq_gate k a (Fin.last g)
            (Finset.mem_filter.mp ha).2
          exact absurd hlt (not_lt_of_ge (Fin.le_last k))
        simp [hcard]
      simp [curryProgram, hzero]
    · simp only [curryProgram, wire_lastCases_castSucc, Program.arityExcess_gate]
      have hex : (q.gate line).excessConsumers w₀'.castSucc =
          q.excessConsumers w₀' +
            min (Finset.univ.filter fun a => line.wires a = w₀').card (line.op.1 - 1) := by
        rw [Program.excessConsumers, Fin.sum_univ_castSucc, Program.lines_gate_last]
        congr 1
        · rw [Program.excessConsumers]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Program.lines_gate_castSucc, mapWires_castSucc_filter_card]
          rfl
        · rw [mapWires_castSucc_filter_card]
          rfl
      have hline := curryLine_arity_sub_one_add u₀ w₀' line
      have hih := ih w₀'
      omega

end ArityExcess

namespace Frontier

/-! ### Universal fan-out slicing and multi-output surplus bounds -/

section Slicing

variable {σ : Signature.{v}} {U : Type u}

private theorem exists_fiber_ncard_ge {α : Type*} [Finite α] [Finite U] [Nonempty U]
    (S : Set α) (f : α → U) :
    ∃ u₀ : U, S.ncard ≤ Nat.card U * {x ∈ S | f x = u₀}.ncard := by
  classical
  cases nonempty_fintype α
  cases nonempty_fintype U
  let sS : Finset α := S.toFinset
  obtain ⟨u₀, hu₀⟩ := Finite.exists_max (fun u => (sS.filter fun x => f x = u).card)
  refine ⟨u₀, ?_⟩
  have hsum : sS.card = ∑ u : U, (sS.filter fun x => f x = u).card := by
    rw [← Finset.card_biUnion]
    · congr 1
      ext x
      simp
    · intro u₁ _ u₂ _ hne
      exact Finset.disjoint_left.mpr fun x hx1 hx2 =>
        hne ((Finset.mem_filter.mp hx1).2.symm.trans (Finset.mem_filter.mp hx2).2)
  have hle : sS.card ≤ Fintype.card U * (sS.filter fun x => f x = u₀).card := by
    rw [hsum]
    simpa [Finset.card_univ] using Finset.sum_le_card_nsmul Finset.univ
      (fun u => (sS.filter fun x => f x = u).card) _ fun u _ => hu₀ u
  have h1 : sS.card = S.ncard := by rw [← Set.ncard_coe_finset, Set.coe_toFinset]
  have h2 : (sS.filter fun x => f x = u₀).card = {x ∈ S | f x = u₀}.ncard := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [sS]
  rwa [h1, h2, ← Nat.card_eq_fintype_card] at hle

/-- Transfer wire acceptance predicates across `elimUnaryAux` whenever the accepted set is
nonempty. -/
private theorem transfer_acc_elimUnary {n s : ℕ} (p : Program σ n s) (I : Interpretation σ U)
    (Acc : Wire n s → Set U) {S : Set (Fin n → U)} (hS : S.Nonempty)
    (hSdef : S = {x | ∀ w, p.trace I x w ∈ Acc w}) :
    let red := elimUnaryAux I p
    ∃ Acc' : Wire n red.size → Set U,
      S = {x | ∀ w', red.program.trace (allOpsInterpretation U) x w' ∈ Acc' w'} := by
  intro red
  obtain ⟨x₀, hx₀⟩ := hS
  rw [hSdef] at hx₀
  refine ⟨fun w' => {u | ∀ w f, red.rep w = .inr (w', f) → f u ∈ Acc w}, ?_⟩
  rw [hSdef]
  ext x
  simp only [mem_ofPred_eq]
  constructor
  · intro hx w' w f hrep
    have hev := red.eval_rep x w
    rw [hrep] at hev
    change f (red.program.trace (allOpsInterpretation U) x w') = p.trace I x w at hev
    rw [hev]
    exact hx w
  · intro hx w
    have hev := red.eval_rep x w
    cases hrep : red.rep w with
    | inl u =>
      have hev₀ := red.eval_rep x₀ w
      rw [hrep] at hev hev₀
      change u = p.trace I x w at hev
      change u = p.trace I x₀ w at hev₀
      rw [← hev, hev₀]
      exact hx₀ w
    | inr wf =>
      rw [hrep] at hev
      change wf.2 (red.program.trace (allOpsInterpretation U) x wf.1) = p.trace I x w at hev
      rw [← hev]
      exact hx wf.1 w wf.2 hrep

private theorem ReducedProgram.fanInAtMost {n s : ℕ} {p : Program σ n s}
    {I : Interpretation σ U}
    (red : ReducedProgram p I) {r : ℕ} (h : p.FanInAtMost r) : red.program.FanInAtMost r :=
  Program.fanInAtMost_iff.mpr fun j =>
    let ⟨k₀, hk₀⟩ := red.arity_le j
    hk₀.trans (Program.fanInAtMost_iff.mp h k₀)

/-- Build a circuit exposing every wire of `p : Program τ n g` as one of its `n + g` outputs. -/
@[expose] def allWiresCircuit {τ : Signature} {n g : ℕ} (p : Program τ n g) :
    Circuit τ n (n + g) where
  program := p
  outputs := (Wire.equiv n g).symm ∘ finSumFinEquiv.symm

@[simp] theorem size_allWiresCircuit {τ : Signature} {n g : ℕ} (p : Program τ n g) :
    (allWiresCircuit p).size = g :=
  rfl

@[simp] theorem program_allWiresCircuit {τ : Signature} {n g : ℕ} (p : Program τ n g) :
    (allWiresCircuit p).program = p :=
  rfl

private theorem outputs_allWiresCircuit_surjective {τ : Signature} {n g : ℕ}
    (p : Program τ n g) : Function.Surjective (allWiresCircuit p).outputs :=
  (Wire.equiv n g).symm.surjective.comp finSumFinEquiv.symm.surjective

private theorem read_allWiresCircuit {τ : Signature} {n g : ℕ} (p : Program τ n g)
    (J : Interpretation τ U) (Acc : Fin (n + g) → Set U) :
    (Compiler.network (allWiresCircuit p) J Acc).read = univ := by
  rw [Compiler.read_network]
  refine eq_univ_of_forall fun i => ?_
  obtain ⟨o, ho⟩ := outputs_allWiresCircuit_surjective p (.input i)
  change Compiler.Reach (allWiresCircuit p) (.input i)
  rw [← ho]
  exact Compiler.Reach.output o

/-- **Universal fan-out slicing (`gateConsumers < k`).** Given any circuit `c : Circuit σ n m` of
fan-in at most `r` over a finite nonempty alphabet `U`, if the accepted set `S` is nonempty and
`1 ≤ k`, repeatedly slicing wires with `gateConsumers ≥ k` at their most popular value yields `t`
steps, a subset `S' ⊆ S`, and a program `q : Program (allOpsSignature U) n g'` with wire
constraints `Acc'` such that:

* every gate of `q` has arity in `[2, r]` and injective argument wires (`c_q.innerSize = g'`),
* **every wire `w : Wire n g'` (both input and internal gate) satisfies `q.gateConsumers w < k`**,
* `q.arityExcess + k * t ≤ c.program.arityExcess` (with `g' ≤ q.arityExcess`, and
  `g' = q.arityExcess` when `r = 2`),
* `S' = (Compiler.network (allWiresCircuit q) (allOpsInterpretation U) ...).accepted` and
  `S.ncard ≤ Nat.card U ^ t * S'.ncard`. -/
theorem exists_sliced_fanout_lt [Finite U] [Nonempty U] {n m r k : ℕ} (hk : 1 ≤ k)
    (c : Circuit σ n m) (I : Interpretation σ U) (Acc : Fin m → Set U)
    (hfan : c.FanInAtMost r)
    (hS : {x : Fin n → U | ∀ o, c.eval I x o ∈ Acc o}.Nonempty) :
    ∃ (t g' : ℕ) (q : Program (allOpsSignature U) n g')
      (Acc' : Fin (n + g') → Set U) (S' : Set (Fin n → U)),
        q.FanInAtMost r ∧
        (∀ j : Fin g', 2 ≤ (allOpsSignature U).Arity (q.lines j).op) ∧
        (∀ j : Fin g', Function.Injective (q.lines j).wires) ∧
        (∀ w : Wire n g', q.gateConsumers w < k) ∧
        g' ≤ q.arityExcess ∧
        (r = 2 → g' = q.arityExcess) ∧
        q.arityExcess + k * t ≤ c.program.arityExcess ∧
        S' ⊆ {x | ∀ o, c.eval I x o ∈ Acc o} ∧
        S'.Nonempty ∧
        (Compiler.network (allWiresCircuit q) (allOpsInterpretation U) Acc').accepted = S' ∧
        {x | ∀ o, c.eval I x o ∈ Acc o}.ncard ≤ Nat.card U ^ t * S'.ncard := by
  classical
  set S₀ : Set (Fin n → U) := {x | ∀ o, c.eval I x o ∈ Acc o}
  let AccW₀ : Wire n c.size → Set U := fun w => {u | ∀ o, c.outputs o = w → u ∈ Acc o}
  have hS₀def : S₀ = {x | ∀ w, c.program.trace I x w ∈ AccW₀ w} := by
    ext x
    simp only [S₀, AccW₀, Circuit.eval, Function.comp_apply, mem_ofPred_eq]
    exact ⟨fun hx w o ho => ho ▸ hx o, fun hx o => hx (c.outputs o) o rfl⟩
  let red₀ := elimUnaryAux I c.program
  obtain ⟨Acc_red₀, hAcc_red₀⟩ := transfer_acc_elimUnary c.program I AccW₀ hS hS₀def
  -- Strong induction on `q.arityExcess`.
  suffices ∀ E : ℕ, ∀ (g : ℕ) (q : Program (allOpsSignature U) n g)
      (AccW : Wire n g → Set U) (S : Set (Fin n → U)),
        q.arityExcess = E →
        q.FanInAtMost r →
        (∀ j : Fin g, 2 ≤ (allOpsSignature U).Arity (q.lines j).op) →
        (∀ j : Fin g, Function.Injective (q.lines j).wires) →
        S.Nonempty →
        S = {x | ∀ w, q.trace (allOpsInterpretation U) x w ∈ AccW w} →
        ∃ (t g' : ℕ) (q' : Program (allOpsSignature U) n g')
          (Acc' : Fin (n + g') → Set U) (S' : Set (Fin n → U)),
            q'.FanInAtMost r ∧
            (∀ j : Fin g', 2 ≤ (allOpsSignature U).Arity (q'.lines j).op) ∧
            (∀ j : Fin g', Function.Injective (q'.lines j).wires) ∧
            (∀ w : Wire n g', q'.gateConsumers w < k) ∧
            g' ≤ q'.arityExcess ∧
            (r = 2 → g' = q'.arityExcess) ∧
            q'.arityExcess + k * t ≤ q.arityExcess ∧
            S' ⊆ S ∧
            S'.Nonempty ∧
            (Compiler.network (allWiresCircuit q') (allOpsInterpretation U) Acc').accepted = S' ∧
            S.ncard ≤ Nat.card U ^ t * S'.ncard by
    obtain ⟨t, g', q', Acc', S', h1, h2, h3, h4, h5, h6, hex, hsub, hne, hacc, hcard⟩ :=
      this red₀.program.arityExcess red₀.size red₀.program Acc_red₀ S₀ rfl
        (ReducedProgram.fanInAtMost red₀ hfan) red₀.two_le_arity red₀.wires_injective hS hAcc_red₀
    exact ⟨t, g', q', Acc', S', h1, h2, h3, h4, h5, h6, hex.trans red₀.arityExcess_le,
      hsub, hne, hacc, hcard⟩
  intro E
  induction E using Nat.strong_induction_on with
  | _ E ih =>
    intro g q AccW S hE hqfan hq2 hqinj hSne hSdef
    by_cases hbad : ∃ w₀ : Wire n g, k ≤ q.gateConsumers w₀
    · obtain ⟨w₀, hw₀⟩ := hbad
      obtain ⟨u₀, hu₀⟩ := exists_fiber_ncard_ge S (fun x => q.trace (allOpsInterpretation U) x w₀)
      set S₁ := {x ∈ S | q.trace (allOpsInterpretation U) x w₀ = u₀}
      have hSpos : 0 < S.ncard := (ncard_pos (toFinite S)).mpr hSne
      have hS₁ne : S₁.Nonempty := (ncard_pos (toFinite S₁)).mp <| Nat.pos_of_ne_zero fun h0 => by
        rw [h0, mul_zero] at hu₀; omega
      set qc := curryProgram u₀ q w₀
      let AccW₁ : Wire n g → Set U := fun w => if w = w₀ then AccW w ∩ {u₀} else AccW w
      have hS₁def : S₁ = {x | ∀ w, qc.trace (allOpsInterpretation U) x w ∈ AccW₁ w} := by
        ext x
        simp only [S₁, mem_ofPred_eq]
        constructor
        · rintro ⟨hxS, hxw₀⟩ w
          rw [curryProgram_trace u₀ q w₀ x hxw₀]
          rw [hSdef] at hxS
          rcases eq_or_ne w w₀ with rfl | hw
          · simp only [AccW₁, ↓reduceIte]; exact ⟨hxS _, hxw₀⟩
          · simp [AccW₁, hw, hxS w]
        · intro hx
          have h0 := hx w₀
          simp only [AccW₁, ↓reduceIte, mem_inter_iff, mem_singleton_iff] at h0
          have hw₀_orig : q.trace (allOpsInterpretation U) x w₀ = u₀ :=
            (curryProgram_trace_self u₀ q w₀ x).symm.trans h0.2
          refine ⟨?_, hw₀_orig⟩
          rw [hSdef]
          intro w
          have hxw := hx w
          rw [curryProgram_trace u₀ q w₀ x hw₀_orig] at hxw
          rcases eq_or_ne w w₀ with rfl | hw
          · simp only [AccW₁, ↓reduceIte, mem_inter_iff] at hxw
            exact hxw.1
          · simpa [AccW₁, hw] using hxw
      let red₁ := elimUnaryAux (allOpsInterpretation U) qc
      obtain ⟨AccW₂, hAccW₂⟩ :=
        transfer_acc_elimUnary qc (allOpsInterpretation U) AccW₁ hS₁ne hS₁def
      have hdrop : red₁.program.arityExcess + k ≤ q.arityExcess := by
        have h1 : red₁.program.arityExcess ≤ (curryProgram u₀ q w₀).arityExcess :=
          red₁.arityExcess_le
        have h2 := curryProgram_arityExcess_add u₀ q w₀
        have h3 := q.gateConsumers_le_excessConsumers hq2 w₀
        omega
      have hlt : red₁.program.arityExcess < E := by omega
      obtain ⟨t', g', q', Acc', S', hr1, hr2, hr3, hr4, hr5, hr6, hrex, hrsub, hrne, hracc,
        hrcard⟩ := ih red₁.program.arityExcess hlt red₁.size red₁.program AccW₂ S₁ rfl
          (ReducedProgram.fanInAtMost red₁ (curryProgram_fanInAtMost u₀ q w₀ hqfan))
          red₁.two_le_arity red₁.wires_injective hS₁ne hAccW₂
      refine ⟨t' + 1, g', q', Acc', S', hr1, hr2, hr3, hr4, hr5, hr6, ?_,
        hrsub.trans (fun _ hx => hx.1), hrne, hracc, ?_⟩
      · calc q'.arityExcess + k * (t' + 1)
            = (q'.arityExcess + k * t') + k := by ring
          _ ≤ red₁.program.arityExcess + k := Nat.add_le_add_right hrex k
          _ ≤ q.arityExcess := hdrop
      · calc S.ncard ≤ Nat.card U * S₁.ncard := hu₀
          _ ≤ Nat.card U * (Nat.card U ^ t' * S'.ncard) := Nat.mul_le_mul_left _ hrcard
          _ = Nat.card U ^ (t' + 1) * S'.ncard := by rw [pow_succ', mul_assoc]
    · push Not at hbad
      let Acc' : Fin (n + g) → Set U := fun o => AccW ((allWiresCircuit q).outputs o)
      have hacc : (Compiler.network (allWiresCircuit q) (allOpsInterpretation U) Acc').accepted =
          S := by
        rw [Compiler.accepted_network, hSdef]
        ext x
        simp only [Acc', Circuit.eval, Function.comp_apply, mem_ofPred_eq]
        refine ⟨fun hx w => ?_, fun hx o => hx _⟩
        obtain ⟨o, ho⟩ := outputs_allWiresCircuit_surjective q w
        exact ho ▸ hx o
      have hg_le : g ≤ q.arityExcess :=
        calc g = ∑ _j : Fin g, 1 := by simp
          _ ≤ q.arityExcess := Finset.sum_le_sum fun j _ => Nat.le_sub_one_of_lt (hq2 j)
      have hg_eq (hr2 : r = 2) : g = q.arityExcess := by
        subst hr2
        have hle := q.arityExcess_le_mul_innerGates hqfan
        have hcard : q.innerGates.card ≤ g := (Finset.card_le_univ _).trans_eq (Fintype.card_fin g)
        omega
      exact ⟨0, g, q, Acc', S, hqfan, hq2, hqinj, hbad, hg_le, hg_eq, by simp, Subset.rfl,
        hSne, hacc, by simp⟩

/-- **Fan-in-two slicing to gate fan-out `≤ 4`.** Specializing `exists_sliced_fanout_lt` to `r = 2`
and `k = 5`, every nonempty fan-in-two accepted set `S` admits `t` wire slices to a residual
strictly-binary program `q` of size `g'` where **every wire (input or gate) feeds `≤ 4` gates**,
`g' + 5 * t ≤ c.program.arityExcess ≤ c.innerSize`, and `S.ncard ≤ |U| ^ t * S'.ncard`. -/
theorem exists_sliced_fanout_le_four [Finite U] [Nonempty U] {n m : ℕ}
    (c : Circuit σ n m) (I : Interpretation σ U) (Acc : Fin m → Set U)
    (hfan : c.FanInAtMost 2)
    (hS : {x : Fin n → U | ∀ o, c.eval I x o ∈ Acc o}.Nonempty) :
    ∃ (t g' : ℕ) (q : Program (allOpsSignature U) n g')
      (Acc' : Fin (n + g') → Set U) (S' : Set (Fin n → U)),
        q.FanInAtMost 2 ∧
        (∀ j : Fin g', (allOpsSignature U).Arity (q.lines j).op = 2) ∧
        (∀ j : Fin g', Function.Injective (q.lines j).wires) ∧
        (∀ w : Wire n g', q.gateConsumers w ≤ 4) ∧
        g' + 5 * t ≤ c.program.arityExcess ∧
        S' ⊆ {x | ∀ o, c.eval I x o ∈ Acc o} ∧
        S'.Nonempty ∧
        (Compiler.network (allWiresCircuit q) (allOpsInterpretation U) Acc').accepted = S' ∧
        {x | ∀ o, c.eval I x o ∈ Acc o}.ncard ≤ Nat.card U ^ t * S'.ncard := by
  obtain ⟨t, g', q, Acc', S', hqfan, hq2, hqinj, hlt5, -, hg_eq, hex, hsub, hne, hacc, hcard⟩ :=
    exists_sliced_fanout_lt (by omega : 1 ≤ 5) c I Acc hfan hS
  refine ⟨t, g', q, Acc', S', hqfan, fun j => ?_, hqinj, fun w => Nat.lt_succ_iff.mp (hlt5 w),
    (hg_eq rfl).symm ▸ hex, hsub, hne, hacc, hcard⟩
  have h1 := hq2 j
  have h2 := Program.fanInAtMost_iff.mp hqfan j
  omega

/-! #### Componentwise frontier counting on `allWiresCircuit` -/

private theorem trace_eq_of_eqOn_readIn {τ : Signature} {n m : ℕ} (c : Circuit τ n m)
    (J : Interpretation τ U) (Acc : Fin m → Set U) {W : Set (Compiler.Vertex c)}
    (hW : (Compiler.graph c).edgeCut W = ∅) {x y : Fin n → U}
    (hxy : EqOn x y ((Compiler.network c J Acc).readIn W))
    {e : Compiler.Edge c} (he : e ∈ (Compiler.graph c).touching W) :
    c.program.trace J x e.signal.val = c.program.trace J y e.signal.val := by
  have hx : (Compiler.network c J fun _ => univ).Satisfies x
      fun e => c.program.trace J x e.signal.val := Compiler.satisfies_trace fun _ => mem_univ _
  have hy : (Compiler.network c J fun _ => univ).Satisfies y
      fun e => c.program.trace J y e.signal.val := Compiler.satisfies_trace fun _ => mem_univ _
  have hxy' : EqOn y x ((Compiler.network c J fun _ => univ).readIn W) := hxy.symm
  obtain ⟨γ, hγ, hγx, -⟩ := hx.splice hy
    (by rw [show (Compiler.network c J fun _ => univ).edgeCut W = ∅ from hW]; exact eqOn_empty _ _)
    hxy' (eqOn_refl _ _)
  exact (hγx he).symm.trans (Compiler.eq_trace hγ e)

private theorem exists_step_ncard_le_of_read_univ [Finite U] {τ : Signature}
    {n m K : ℕ} (c : Circuit τ n m) (J : Interpretation τ U) (Acc : Fin m → Set U)
    (hVpos : 0 < Nat.card (Compiler.Vertex c))
    (hread : (Compiler.network c J Acc).read = univ)
    (π : Layout (Compiler.Vertex c))
    (hfree : RectangleFree (Compiler.network c J Acc).accepted K)
    (hKS : K ≤ (Compiler.network c J Acc).accepted.ncard)
    (hsub : ∀ t (ht : t < Nat.card (Compiler.Vertex c)),
      (Compiler.graph c).frontier π t ∪ (Compiler.graph c).frontier π (t + 1) ⊆
        (Compiler.graph c).touching ((Compiler.graph c).component (π.symm ⟨t, ht⟩))) :
    ∃ (t : ℕ) (ht : t < Nat.card (Compiler.Vertex c)),
      (Compiler.network c J Acc).accepted.ncard ≤
        (K - 1) ^ 2 * (Nat.card (Compiler.Vertex c) + 1) *
          Nat.card U ^ min
            (((Compiler.graph c).frontier π t ∪ (Compiler.graph c).frontier π (t + 1)).ncard +
              ((Compiler.network c J Acc).readAt (π.symm ⟨t, ht⟩)).ncard)
            (((Compiler.network c J Acc).readIn
              ((Compiler.graph c).component (π.symm ⟨t, ht⟩))).ncard) := by
  set N := Compiler.network c J Acc
  set V := Nat.card (Compiler.Vertex c)
  let sw := N.frontierSweep (S := N.accepted) π (fun x e => c.program.trace J x e.signal.val)
    (fun _ _ => ()) (fun _ _ _ _ => rfl)
    fun t _ x hx y hy _ hval z hzx hzy => by
      rw [Compiler.accepted_network] at hx hy ⊢
      intro o
      have hsp := Compiler.eval_splice hval hzx hzy o
      by_cases ho : Compiler.Vertex.output o ∈ π.initial t
      · exact hsp.1 ho ▸ hx o
      · exact hsp.2 ho ▸ hy o
  have hextra_le : ((fun _ : Fin n → U => ((), ())) '' N.accepted).ncard ≤ 1 :=
    (ncard_le_card _).trans_eq (by simp)
  have hstep (t : ℕ) (ht : t < V) :
      (sw.transition t '' N.accepted).ncard ≤
        Nat.card U ^ min
          ((N.frontier π t ∪ N.frontier π (t + 1)).ncard + (N.readAt (π.symm ⟨t, ht⟩)).ncard)
          ((N.readIn (N.component (π.symm ⟨t, ht⟩))).ncard) := by
    have hb1 : (sw.transition t '' N.accepted).ncard ≤
        Nat.card U ^ ((N.frontier π t ∪ N.frontier π (t + 1)).ncard +
          (N.readAt (π.symm ⟨t, ht⟩)).ncard) := by
      have hw : (sw.transition t '' N.accepted).ncard ≤
          ((fun _ : Fin n → U => ((), ())) '' N.accepted).ncard *
            Nat.card U ^ ((N.frontier π t ∪ N.frontier π (t + 1)).ncard +
              (N.readAt (π.symm ⟨t, ht⟩)).ncard) := N.ncard_transition_le ht
      exact hw.trans ((Nat.mul_le_mul_right _ hextra_le).trans_eq (one_mul _))
    have hb2 : (sw.transition t '' N.accepted).ncard ≤
        Nat.card U ^ (N.readIn (N.component (π.symm ⟨t, ht⟩))).ncard := by
      set W := N.component (π.symm ⟨t, ht⟩)
      have hW : (Compiler.graph c).edgeCut W = ∅ := N.edgeCut_component _
      have hvW : π.symm ⟨t, ht⟩ ∈ W := N.mem_component_self _
      have hr := sw.ncard_transition_le_of_factorsThrough (t := t)
        (D := ↥(N.readIn W) → U) (fun _ => ()) (fun x => (N.readIn W).domRestrict x)
        fun x _ y _ _ hg => by
          rw [domRestrict_eq_domRestrict_iff] at hg
          have htouch : EqOn (fun e : Compiler.Edge c => c.program.trace J x e.signal.val)
              (fun e : Compiler.Edge c => c.program.trace J y e.signal.val)
              ((Compiler.graph c).touching W) :=
            fun e he => trace_eq_of_eqOn_readIn c J Acc hW hg he
          have hsub_t := hsub t ht
          simp only [Sweep.transition, sw, Network.frontierSweep, Prod.mk.injEq, true_and,
            Network.frontierValues_eq_iff, domRestrict_eq_domRestrict_iff]
          exact ⟨htouch.mono (subset_union_left.trans hsub_t),
            htouch.mono (subset_union_right.trans hsub_t),
            fun i hi => hg ⟨_, hvW, N.revealedBy_succ_diff_subset π ht hi⟩⟩
      have h1 : ((fun _ : Fin n → U => ()) '' N.accepted).ncard ≤ 1 :=
        (ncard_le_card _).trans_eq (by simp)
      rw [Nat.card_fun, Nat.card_coe_set_eq] at hr
      exact hr.trans ((Nat.mul_le_mul_right _ h1).trans_eq (one_mul _))
    rw [min_def]; split_ifs; exacts [hb1, hb2]
  have hlast : (sw.transition V '' N.accepted).ncard ≤ 1 := by
    have hl : (sw.transition V '' N.accepted).ncard ≤
        ((fun _ : Fin n → U => ((), ())) '' N.accepted).ncard *
          Nat.card U ^ N.readᶜ.ncard := N.ncard_transition_last_le
    rw [hread, compl_univ, ncard_empty, pow_zero, mul_one] at hl
    exact hl.trans hextra_le
  obtain ⟨t, ht, hmax⟩ := Finset.exists_max_image (Finset.range V)
    (fun t => (sw.transition t '' N.accepted).ncard) (Finset.nonempty_range_iff.mpr hVpos.ne')
  have ht' : t < V := Finset.mem_range.mp ht
  refine ⟨t, ht', ?_⟩
  have hsum : sw.transitionCount ≤ (V + 1) * (sw.transition t '' N.accepted).ncard := by
    have hpos_m : 1 ≤ (sw.transition t '' N.accepted).ncard := by
      obtain ⟨x₀, hx₀⟩ := (ncard_pos (toFinite N.accepted)).mp
        (lt_of_lt_of_le hfree.pos hKS)
      exact (ncard_pos (toFinite _)).mpr ⟨_, x₀, hx₀, rfl⟩
    rw [Sweep.transitionCount, show sw.length = V + 1 from rfl, Finset.sum_range_succ]
    calc (∑ s ∈ Finset.range V, (sw.transition s '' N.accepted).ncard) +
            (sw.transition V '' N.accepted).ncard
        ≤ V * (sw.transition t '' N.accepted).ncard + 1 := by
          refine Nat.add_le_add ?_ hlast
          simpa using Finset.sum_le_card_nsmul (Finset.range V)
            (fun s => (sw.transition s '' N.accepted).ncard) _ fun s hs => hmax s hs
      _ ≤ (V + 1) * (sw.transition t '' N.accepted).ncard := by
          rw [add_one_mul]
          exact Nat.add_le_add_left hpos_m _
  have hbound : N.accepted.ncard ≤
      (K - 1) ^ 2 * (V + 1) * (sw.transition t '' N.accepted).ncard := by
    calc N.accepted.ncard ≤ (K - 1) ^ 2 * sw.transitionCount := sw.ncard_le hfree hKS
      _ ≤ (K - 1) ^ 2 * ((V + 1) * (sw.transition t '' N.accepted).ncard) := by gcongr
      _ = (K - 1) ^ 2 * (V + 1) * (sw.transition t '' N.accepted).ncard :=
          (mul_assoc _ _ _).symm
  exact hbound.trans (Nat.mul_le_mul_left _ (hstep t ht'))

/-- **Asymptotic fan-out slicing surplus lower bound.** Fix `r ≥ 2`, `LayoutBound (r + 1) A` with
`A > 0`, a dense `K_n`-rectangle-free family `S_n ⊆ U^n`, and a slicing threshold `k ≥ 1`. For
every `ε > 0` and all large `n`, every circuit `c` of fan-in at most `r` deciding `S_n` admits a
slicing count `t : ℕ` (witnessing `t` wires of `gateConsumers ≥ k` sliced down to a residual
circuit where every wire has `gateConsumers < k` and `g' + k * t ≤ c.program.arityExcess`) such
that:

`(1 + 1 / A - ε) * n + ((r - 1) * k - (1 + 1 / A)) * t < (r - 1) * c.program.arityExcess`.

At `r = 2` (`(r - 1) = 1`), this reads `(1 + 1 / A - ε) * n + (k - (1 + 1 / A)) * t <
c.program.arityExcess ≤ c.innerSize`, simultaneously making unary (`NOT`) gates free (at `t = 0` or
`k` large) and charging `+ (k - (1 + 1 / A))` gates of surplus per high-fan-out slice when
`k > 1 + 1 / A`. -/
theorem eventually_slicing_surplus {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}
    [Finite U] [Nontrivial U] (hSK : DenseRectangleFree S K) {k : ℕ} (hk : 1 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost r → c.Decides I Acc (S n) →
        ∃ (t g' : ℕ) (q : Program (allOpsSignature U) n g'),
          q.FanInAtMost r ∧
          (∀ w : Wire n g', q.gateConsumers w < k) ∧
          g' ≤ q.arityExcess ∧
          q.arityExcess + k * t ≤ c.program.arityExcess ∧
          (1 + 1 / A - ε) * n + (((r - 1 : ℕ) : ℝ) * k - (1 + 1 / A)) * t <
            ((r - 1 : ℕ) : ℝ) * c.program.arityExcess := by
  set qU := Nat.card U
  have hqU : (1 : ℝ) < qU := by exact_mod_cast Finite.one_lt_card
  have hLqU : 0 < Real.log qU := Real.log_pos hqU
  set L : ℝ := 1 + 1 / A
  have hLpos : 0 < L := by positivity
  obtain ⟨η, hη, H⟩ := eventually_lt_of_frontier hA (r + 2) hSK.isLittleO_log
    hSK.isLittleO_deficit (β := fun _ => 0) (by simp) hε
  obtain ⟨C, hC⟩ := hlayout.exists_layout_componentwise hη
  -- Bound `(n - log_q |S_n|) + log_q K_n < (ε / L) * n` for the fully-depleted case `|S'| < K_n`.
  have herr : (fun n : ℕ => ((n : ℝ) - Real.logb qU (S n).ncard) + Real.logb qU (K n)) =o[atTop]
      fun n => (n : ℝ) := by
    have h1 : (fun n : ℕ => Real.logb qU (K n)) =o[atTop] fun n => (n : ℝ) :=
      (hSK.isLittleO_log.const_mul_left (1 / Real.log qU)).congr_left fun n => by
        simp only [Real.logb]
        ring
    have h2 : (fun n : ℕ => (n : ℝ) - Real.logb qU (S n).ncard) =o[atTop] fun n => (n : ℝ) :=
      (hSK.isLittleO_deficit.const_mul_left (1 / Real.log qU)).congr_left fun n => by
        simp only [Real.logb]
        field_simp
        ring
    exact h2.add h1
  filter_upwards [H C, herr.bound (div_pos hε (mul_pos two_pos hLpos)),
    hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    eventually_ge_atTop 1] with n hn herrn hfreen hbign hn1
  intro σ I Acc c hfan hdec
  have hS_eq : {x : Fin n → U | ∀ o : Fin 1, c.eval I x o ∈ (fun _ => Acc) o} = S n := by
    ext x
    rw [mem_ofPred_eq, hdec x]
    exact ⟨fun h => h 0, fun h o => Subsingleton.elim o 0 ▸ h⟩
  have hSpos_nat : 0 < (S n).ncard :=
    lt_of_lt_of_le (Nat.mul_pos Nat.card_pos (pow_pos hfreen.pos 2)) hbign
  have hSne : {x : Fin n → U | ∀ o : Fin 1, c.eval I x o ∈ (fun _ => Acc) o}.Nonempty := by
    rw [hS_eq]
    exact (ncard_pos (toFinite (S n))).mp hSpos_nat
  obtain ⟨t, g', q, Acc', S', hqfan, _, _, hlt_k, hg_le, _, hex, hsub, hS'ne, hacc, hcard⟩ :=
    exists_sliced_fanout_lt hk c I (fun _ => Acc) hfan hSne
  rw [hS_eq] at hsub hcard
  refine ⟨t, g', q, hqfan, hlt_k, hg_le, hex, ?_⟩
  have hr1_pos : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
  have hS'pos_nat : 0 < S'.ncard := (ncard_pos (toFinite S')).mpr hS'ne
  have hS'pos_real : (0 : ℝ) < S'.ncard := by exact_mod_cast hS'pos_nat
  have hlog_pigeon : Real.logb qU (S n).ncard ≤ t + Real.logb qU S'.ncard := by
    have h1 : ((S n).ncard : ℝ) ≤ (qU : ℝ) ^ t * S'.ncard := by exact_mod_cast hcard
    calc Real.logb qU (S n).ncard
        ≤ Real.logb qU ((qU : ℝ) ^ t * S'.ncard) :=
          Real.logb_le_logb_of_le hqU (by exact_mod_cast hSpos_nat) h1
      _ = t + Real.logb qU S'.ncard := by
          rw [Real.logb_mul (by positivity) hS'pos_real.ne', Real.logb_pow,
            Real.logb_self_eq_one hqU, mul_one]
  have hex_real : ((r - 1 : ℕ) : ℝ) * g' + ((r - 1 : ℕ) : ℝ) * k * t ≤
      ((r - 1 : ℕ) : ℝ) * c.program.arityExcess := by
    have := Nat.mul_le_mul_left (r - 1) ((Nat.add_le_add_right hg_le (k * t)).trans hex)
    rw [Nat.mul_add, ← Nat.mul_assoc] at this
    exact_mod_cast this
  by_cases hsmall : S'.ncard < K n
  · -- Depleted branch: `S'.ncard < K_n` implies `t ≥ n - o(n)`.
    have hlogS'_le : Real.logb qU S'.ncard ≤ Real.logb qU (K n) :=
      Real.logb_le_logb_of_le hqU (by exact_mod_cast hS'pos_nat) (by exact_mod_cast hsmall.le)
    have hn_pos : (0 : ℝ) < n := by exact_mod_cast hn1
    simp only [Real.norm_eq_abs, abs_of_nonneg hn_pos.le] at herrn
    have herr_bnd := (le_abs_self _).trans herrn
    have hnt : (n : ℝ) - t ≤ ε / (2 * L) * n := by linarith
    have hLnt : L * ((n : ℝ) - t) < ε * n := by
      have heq : L * (ε / (2 * L) * n) = (ε / 2) * n := by field_simp [hLpos.ne']
      linarith [mul_le_mul_of_nonneg_left hnt hLpos.le, mul_pos hε hn_pos]
    have hkt_le : ((r - 1 : ℕ) : ℝ) * k * t ≥ (k : ℝ) * t := by
      nlinarith [show (0 : ℝ) ≤ (k : ℝ) * t by positivity]
    have hk_ge1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hrg_nonneg : (0 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) * g' := by positivity
    -- `(L - ε) n + ((r-1) k - L) t = (r-1) k t + L (n - t) - ε n < (r-1) k t`.
    linarith
  · -- Frontier branch: `K_n ≤ S'.ncard`, apply `exists_step_ncard_le_allWires` + supply/demand.
    have hKS' : K n ≤ S'.ncard := not_lt.mp hsmall
    have hfree' : RectangleFree S' (K n) := fun X A B hrect => hfreen X A B (hrect.trans hsub)
    set cq := allWiresCircuit q
    set N := Compiler.network cq (allOpsInterpretation U) Acc'
    set V := Nat.card (Compiler.Vertex cq)
    have hVpos : 0 < V := by
      obtain ⟨o, ho⟩ := outputs_allWiresCircuit_surjective q (.input ⟨0, hn1⟩)
      have hr_in : Compiler.Reach cq (.input ⟨0, hn1⟩) := by
        rw [← ho]
        exact Compiler.Reach.output o
      have : Nonempty (Compiler.Vertex cq) := ⟨.signal ⟨.input ⟨0, hn1⟩, hr_in⟩⟩
      exact Nat.card_pos
    have hfan_cq : cq.FanInAtMost r := hqfan
    obtain ⟨π, hπ⟩ := hC _ _ (Compiler.graph cq) Compiler.loopless
      (Compiler.maxDegreeLE hr hfan_cq)
    rw [← hacc] at hfree' hKS'
    obtain ⟨t_step, ht_step, hcount⟩ := exists_step_ncard_le_of_read_univ cq
      (allOpsInterpretation U) Acc' hVpos (read_allWiresCircuit q (allOpsInterpretation U) Acc')
      π hfree' hKS' fun s hs =>
        union_subset (hπ s hs s le_rfl (by omega)).1 (hπ s hs (s + 1) (by omega) le_rfl).1
    rw [hacc] at hcount
    set W := N.component (π.symm ⟨t_step, ht_step⟩)
    set a := (N.frontier π t_step ∪ N.frontier π (t_step + 1)).ncard +
      (N.readAt (π.symm ⟨t_step, ht_step⟩)).ncard
    set nW := (N.readIn W).ncard
    set s' : ℝ := ((r - 1 : ℕ) : ℝ) * g'
    have hinner_le : cq.innerSize ≤ g' := cq.innerSize_le_size
    have ha : (a : ℝ) ≤ (N.frontier π t_step).ncard + (r + 2) := by
      have hU : (N.frontier π t_step ∪ N.frontier π (t_step + 1)).ncard ≤
          (N.frontier π t_step).ncard + (r + 1) :=
        (ncard_le_ncard (union_subset subset_union_left (N.frontier_succ_subset π ht_step))
          (toFinite _)).trans ((ncard_union_le _ _).trans
            (Nat.add_le_add_left (Compiler.maxDegreeLE hr hfan_cq _) _))
      have hR : (N.readAt (π.symm ⟨t_step, ht_step⟩)).ncard ≤ 1 :=
        Compiler.ncard_readAt_le (allOpsInterpretation U) Acc' _
      have : a ≤ (N.frontier π t_step).ncard + (r + 2) := by simp only [a]; omega
      exact_mod_cast this
    have hρ : (N.cycleRankOn W : ℝ) + nW ≤ s' + 1 := by
      have h1 := Compiler.cycleRankOn_add_ncard_readIn_le (allOpsInterpretation U) Acc' hfan_cq
        (N.edgeCut_component (π.symm ⟨t_step, ht_step⟩))
        (N.ncard_component_le_ncard_touching_add_one (π.symm ⟨t_step, ht_step⟩))
      have h : N.cycleRankOn W + nW ≤ (r - 1) * g' + 1 :=
        h1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left (r - 1) hinner_le) 1)
      have hreal : ((N.cycleRankOn W + nW : ℕ) : ℝ) ≤ (((r - 1) * g' : ℕ) : ℝ) + 1 := by
        exact_mod_cast h
      push_cast at hreal
      linarith
    have hV : (V : ℝ) ≤ 7 * s' + 3 * n + 3 := by
      have hv1 := (Compiler.card_vertex_le hfan_cq).trans
        (Nat.add_le_add_right (Nat.mul_le_mul_left (2 * r) hinner_le) (3 * (n + g')))
      have h7 : 2 * r + 3 ≤ 7 * (r - 1) := by omega
      have hv2 : V ≤ 7 * ((r - 1) * g') + 3 * n := by
        have := Nat.mul_le_mul_right g' h7
        simp only [V]
        nlinarith
      have hv3 : (V : ℝ) ≤ 7 * (((r - 1) * g' : ℕ) : ℝ) + 3 * n := by exact_mod_cast hv2
      push_cast at hv3
      linarith
    have hK1 := hfreen.pos
    have hlogS' : Real.logb qU S'.ncard ≤
        2 * Real.logb qU (K n) + Real.logb qU (V + 1) + min a nW := by
      have hK2 : (K n - 1) ^ 2 ≤ K n ^ 2 := Nat.pow_le_pow_left (Nat.sub_le _ _) 2
      have hcount' : S'.ncard ≤ (K n - 1) ^ 2 * (V + 1) * qU ^ (min a nW) := hcount
      have hc2 : (S'.ncard : ℝ) ≤ (K n : ℝ) ^ 2 * (V + 1) * (qU : ℝ) ^ (min a nW) := by
        exact_mod_cast hcount'.trans
          (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hK2))
      have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK1
      calc Real.logb qU S'.ncard
          ≤ Real.logb qU ((K n : ℝ) ^ 2 * (V + 1) * (qU : ℝ) ^ (min a nW)) :=
            Real.logb_le_logb_of_le hqU hS'pos_real hc2
        _ = 2 * Real.logb qU (K n) + Real.logb qU (V + 1) + min a nW := by
            rw [Real.logb_mul (by positivity) (by positivity),
              Real.logb_mul (by positivity) (by positivity), Real.logb_pow, Real.logb_pow,
              Real.logb_self_eq_one hqU]
            push_cast
            ring
    -- Shift `(s', ρ, w)` by `t` slices into `eventually_lt_of_frontier`.
    have hAη : 0 < A + η := by linarith
    set s_eff : ℝ := s' + (1 + 1 / (A + η)) * t
    set ρ_eff : ℝ := N.cycleRankOn W + (t : ℝ) / (A + η)
    set w_eff : ℝ := (N.frontier π t_step).ncard + t
    have hs'_nonneg : 0 ≤ s' := by positivity
    have hs_eff_ge : s' ≤ s_eff := le_add_of_nonneg_right (by positivity)
    have hlogK_nonneg : 0 ≤ Real.logb qU (K n) := Real.logb_nonneg hqU (by exact_mod_cast hK1)
    have hmin1 : ((min a nW : ℕ) : ℝ) ≤ a := by exact_mod_cast min_le_left a nW
    have hmin2 : ((min a nW : ℕ) : ℝ) ≤ nW := by exact_mod_cast min_le_right a nW
    have hseff_id : s_eff - t = s' + (t : ℝ) / (A + η) := by
      simp only [s_eff]
      ring
    have hsupply_id : (A + η) * ρ_eff = (A + η) * N.cycleRankOn W + t := by
      simp only [ρ_eff, mul_add]
      rw [mul_div_cancel₀ _ hAη.ne']
    have hsupply_step : ((N.frontier π t_step).ncard : ℝ) ≤
        (A + η) * N.cycleRankOn W + η * V + C :=
      (hπ t_step ht_step t_step le_rfl (by omega)).2
    have hfront := hn s_eff V ρ_eff w_eff (by positivity) (Nat.cast_nonneg _)
      (by linarith) (by linarith) (by linarith) (by linarith)
    have hinv_le : 1 / (A + η) ≤ 1 / A := one_div_le_one_div_of_le hA (by linarith)
    have hmul_le : (1 + 1 / (A + η)) * (t : ℝ) ≤ L * t :=
      mul_le_mul_of_nonneg_right (by simp only [L]; linarith) (Nat.cast_nonneg (α := ℝ) t)
    have hseff_le : s_eff ≤ s' + L * t := by
      simp only [s_eff]
      linarith
    linarith

/-- **Unconditional median-switched fan-out-`≤ 4` surplus bound (`L₃ ≈ 4.575972`).** For every
dense `K_n`-rectangle-free family `S_n ⊆ U^n` and every `ε > 0`, eventually every fan-in-two
circuit `c` deciding `S_n` slices (`t` times, killing `≥ 5` binary consumers per slice) to a
residual program `q` with `gateConsumers ≤ 4` on every wire and

`(L₃ - ε) * n + (5 - L₃) * t < c.program.arityExcess ≤ c.innerSize`,

where `L₃ = 1 + 2π / (3 arccos (5 / 6)) ≈ 4.575972` and `5 - L₃ > 0.424`. -/
theorem eventually_switched_slicing_surplus {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}
    [Finite U] [Nontrivial U] (hSK : DenseRectangleFree S K) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1), c.FanInAtMost 2 → c.Decides I Acc (S n) →
        ∃ (t g' : ℕ) (q : Program (allOpsSignature U) n g'),
          q.FanInAtMost 2 ∧
          (∀ w : Wire n g', q.gateConsumers w ≤ 4) ∧
          q.arityExcess + 5 * t ≤ c.program.arityExcess ∧
          c.program.arityExcess ≤ c.innerSize ∧
          (1 + 2 * Real.pi / (3 * Real.arccos (5 / 6)) - ε) * n +
              (5 - (1 + 2 * Real.pi / (3 * Real.arccos (5 / 6)))) * t <
            c.program.arityExcess := by
  have h := eventually_slicing_surplus.{u, v} (le_refl 2)
    (mul_pos two_pos Switched.switchedCoefficient_pos) layoutBound_switched hSK
    (by omega : 1 ≤ 5) hε
  rw [Switched.one_add_inv_two_mul_switchedCoefficient] at h
  filter_upwards [h] with n hn σ I Acc c hfan hdec
  obtain ⟨t, g', q, hqfan, hlt5, _, hex, hlt⟩ := hn σ I Acc c hfan hdec
  have hle_inner : c.program.arityExcess ≤ c.innerSize := by
    simpa [Circuit.innerSize] using c.program.arityExcess_le_mul_innerGates hfan
  refine ⟨t, g', q, hqfan, fun w => Nat.lt_succ_iff.mp (hlt5 w), hex, hle_inner, ?_⟩
  push_cast at hlt
  linarith

end Slicing

end Frontier

end Cslib.Circuits

