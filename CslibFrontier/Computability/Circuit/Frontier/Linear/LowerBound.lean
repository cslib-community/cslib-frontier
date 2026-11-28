/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler
public import CslibFrontier.Computability.Circuit.Frontier.Demand
public import CslibFrontier.Computability.Circuit.Linearize
public import CslibFrontier.Foundations.Data.Matrix.TotallyRegular
import CslibFrontier.Computability.Circuit.Program
import CslibFrontier.Foundations.Data.Nat.IntermediateValue
import CslibFrontier.Tactic.LinarithCast

/-!
# The frontier lower bound for linear maps

The frontier method applies to circuits with many outputs. For a circuit computing a linear map,
the demand comes from linear algebra instead of from counting rectangles.

Let a circuit over a field `F` compute `x ↦ M x` for an `N × N` matrix `M`, and cut its graph
(`Cslib.Circuits.Frontier.Compiler.graph`) along a set `P` of vertices: `P` reads the inputs `X`
and holds the outputs `Y`. If the runs on two inputs agree on the cut, splicing them
(`Cslib.Circuits.Frontier.Compiler.eval_splice`) shows that the outputs in `Y` do not see the
inputs outside `X`, and the outputs outside `Y` do not see the inputs in `X`. When `M` is totally
regular and `|X| + |Y| = N`, both blocks `M[Y, Xᶜ]` and `M[Yᶜ, X]` are square and nonsingular,
so the values on the cut determine the input. Every layout passes through such a `P`, since
`|X| + |Y|` grows by at most one per vertex, from `0` to `2 N`
(`Cslib.Circuits.Frontier.Compiler.exists_injective_frontier`), by a discrete intermediate value
theorem (`Nat.exists_eq_of_forall_le_add_one`).

How many values can a cut of `k` edges carry? A circuit has *linear capacity*
(`Cslib.Circuits.Circuit.LinearCapacity`) when the values of `k` wires never determine more than
`k` coordinates of the input. This holds

* over a finite alphabet, for every basis: `k` wires take at most `|F| ^ k` values
  (`Cslib.Circuits.Circuit.linearCapacity_of_finite`);
* over any field, for the affine basis: the values of `k` wires are an affine function of the
  input (`Cslib.Circuits.Circuit.linearCapacity_affine`);
* over an infinite field, for polynomial operations, after linearizing the circuit
  (`Cslib.Circuits.Circuit.Computes.exists_affine`).

It fails over infinite fields for arbitrary operations: an injection `F × F → F` lets one wire
carry two coordinates.

So every layout of the graph of the circuit has a frontier of at least `N` edges: the demand is
exactly `N`. For `s` inner gates of fan-in at most `r` the graph has cycle rank at most
`(r - 1) s + 1 - N`, and the comparison of demand and supply (`eventually_lt_of_demand`) gives
the coefficient of the frontier lower bound for decision problems.

**Main theorem** (`eventually_lt_mul_innerSize_of_isTotallyRegular`). Under `LayoutBound (r + 1) A`,
for every `ε > 0` and all large `N`, every circuit of fan-in at most `r` with linear capacity
computing a totally regular map `F^N → F^N` has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`, uniformly in the field. Constants are free.

## Main definitions

* `Cslib.Circuits.Circuit.LinearCapacity`: wires carry at most one coordinate each.
* `Cslib.Circuits.Frontier.Multigraph.inCut`, `Cslib.Circuits.Frontier.Multigraph.outCut`:
  the entering and leaving directed edge cuts of a vertex set.

## Main results

* `Cslib.Circuits.Frontier.Compiler.exists_injective_frontier`: some frontier of every layout
  determines the input.
* `Cslib.Circuits.Frontier.Compiler.eval_eq_of_eqOn_inCut`: outputs inside `P` depend only on
  inputs read in `P` and wires carried by edges entering `P`.
* `Cslib.Circuits.Frontier.Compiler.min_le_ncard_inCut`,
  `Cslib.Circuits.Frontier.Compiler.min_le_ncard_outCut`,
  `Cslib.Circuits.Frontier.Compiler.min_le_ncard_edgeCut`: one-way and unbalanced cut demands for
  totally regular linear maps.
* `Cslib.Circuits.Frontier.exists_graph_of_isTotallyRegular`: the reduction theorem for linear
  maps.
* `Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_isTotallyRegular`: the lower bound, for
  circuits with linear capacity; `..._finite`, `..._affine` and `..._isPolynomial` specialize it
  to finite fields with any basis, to any field with the affine basis, and to infinite fields with
  polynomial operations.

## References

* [L. G. Valiant, *Graph-theoretic arguments in low-level complexity*][Valiant1977]
* [P. Bürgisser, M. Clausen, M. A. Shokrollahi, *Algebraic Complexity
  Theory*][BurgisserClausenShokrollahi1997], Chapter 13
-/

@[expose] public section

open Set Filter Asymptotics Matrix

universe u v

namespace Cslib.Circuits

/-! ### Linear capacity -/

section Capacity

variable {σ : Signature} {U : Type*} {n m : ℕ}

/-- A circuit has *linear capacity* under an interpretation when its wires carry at most one
symbol each: whenever the values of a set `W` of wires determine the input, `n ≤ |W|`. -/
def Circuit.LinearCapacity (c : Circuit σ n m) (I : Interpretation σ U) : Prop :=
  ∀ W : Set (Wire n c.size),
    Function.Injective (fun (x : Fin n → U) (w : W) => c.program.trace I x w) → n ≤ W.ncard

/-- Over a finite alphabet every circuit has linear capacity: `k` wires take at most `|U| ^ k`
values. -/
theorem Circuit.linearCapacity_of_finite [Finite U] [Nontrivial U] (c : Circuit σ n m)
    (I : Interpretation σ U) : c.LinearCapacity I := by
  intro W hW
  have h := Nat.card_le_card_of_injective _ hW
  rw [Nat.card_fun, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin,
    Nat.card_coe_set_eq] at h
  exact (Nat.pow_le_pow_iff_right Finite.one_lt_card).mp h

/-- Circuits over the affine basis have linear capacity: the values of `k` wires are an affine
function of the input, which is injective only if `n ≤ k`. -/
theorem Circuit.linearCapacity_affine {F : Type*} [Field F] (c : Circuit (affineSignature F) n m) :
    c.LinearCapacity (affineInterpretation F) := by
  intro W hW
  have := Fintype.ofFinite W
  choose L b hL using fun w : W => c.program.exists_affine_trace w.val
  let Φ : (Fin n → F) →ₗ[F] (W → F) := LinearMap.pi L
  have hΦ : Function.Injective Φ := fun x y hxy => hW (funext fun w => by
    have := congrFun hxy w
    simp only [LinearMap.pi_apply, Φ] at this
    simp only [hL, this])
  have := LinearMap.finrank_le_finrank_of_injective hΦ
  rwa [Module.finrank_fin_fun, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
    Nat.card_coe_set_eq] at this

end Capacity

namespace Frontier

/-! ### Directed edge cuts -/

namespace Multigraph

variable {V E : Type*} (G : Multigraph V E)

/-- The *entering* (backward) edge cut of `P`: edges with source outside `P` and target in `P`. -/
def inCut (P : Set V) : Set E :=
  {e | G.src e ∉ P ∧ G.tgt e ∈ P}

/-- The *leaving* (forward) edge cut of `P`: edges with source in `P` and target outside `P`. -/
def outCut (P : Set V) : Set E :=
  {e | G.src e ∈ P ∧ G.tgt e ∉ P}

@[simp] theorem mem_inCut {P : Set V} {e : E} :
    e ∈ G.inCut P ↔ G.src e ∉ P ∧ G.tgt e ∈ P :=
  Iff.rfl

@[simp] theorem mem_outCut {P : Set V} {e : E} :
    e ∈ G.outCut P ↔ G.src e ∈ P ∧ G.tgt e ∉ P :=
  Iff.rfl

/-- The entering cut of the complement is the leaving cut. -/
theorem inCut_compl (P : Set V) : G.inCut Pᶜ = G.outCut P := by
  ext e
  simp only [mem_inCut, mem_outCut, mem_compl_iff, not_not]

/-- The undirected edge cut splits into the entering and leaving cuts. -/
theorem edgeCut_eq_inCut_union_outCut (P : Set V) :
    G.edgeCut P = G.inCut P ∪ G.outCut P := by
  ext e
  simp only [mem_edgeCut, mem_union, mem_inCut, mem_outCut]
  tauto

/-- The entering and leaving cuts are disjoint. -/
theorem disjoint_inCut_outCut (P : Set V) : Disjoint (G.inCut P) (G.outCut P) :=
  disjoint_left.mpr fun _ he₁ he₂ => he₁.1 he₂.1

/-- The size of the undirected edge cut is the sum of the entering and leaving cut sizes. -/
theorem ncard_edgeCut_eq_add [Finite E] (P : Set V) :
    (G.edgeCut P).ncard = (G.inCut P).ncard + (G.outCut P).ncard := by
  rw [G.edgeCut_eq_inCut_union_outCut P, ncard_union_eq (G.disjoint_inCut_outCut P)]

end Multigraph

/-! ### The graph of a circuit for a totally regular map -/

namespace Compiler

variable {F : Type u} [Field F] {σ : Signature.{v}} {I : Interpretation σ F} {N : ℕ}
  {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N}

/-- A set of coordinates and its complement together have `N` elements. -/
private theorem ncard_add_ncard_compl_fin (S : Set (Fin N)) : S.ncard + Sᶜ.ncard = N := by
  rw [ncard_add_ncard_compl, Nat.card_eq_fintype_card, Fintype.card_fin]

/-- The outputs of a circuit computing `x ↦ M x`. -/
private theorem eval_eq_mulVec (hc : c.Computes I fun x => M *ᵥ x) (x : Fin N → F) (o : Fin N) :
    c.eval I x o = (M *ᵥ x) o :=
  congrFun (hc x) o

/-- **Every output of a totally regular map depends on every input**, so in the graph of a
circuit computing it the vertex of every input is joined to every output vertex. -/
theorem exists_reachable_of_isTotallyRegular (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (i o : Fin N) :
    ∃ hi : Reach c (.input i),
      (graph c).toSimpleGraph.Reachable (.signal ⟨.input i, hi⟩) (.output o) := by
  classical
  refine exists_reachable_of_eval_ne (I := I) (x := 0) (y := Pi.single i 1) (fun k hk => ?_) ?_
  · simp [hk]
  · rw [eval_eq_mulVec hc, eval_eq_mulVec hc, mulVec_zero, mulVec_single_one]
    exact (hM.apply_ne_zero o i).symm

/-- The graph of a circuit computing a totally regular map with at least one input is
connected. -/
theorem connected_of_isTotallyRegular (hN : 0 < N) (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) : (graph c).toSimpleGraph.Connected := by
  obtain ⟨hi, -⟩ := exists_reachable_of_isTotallyRegular hM hc ⟨0, hN⟩ ⟨0, hN⟩
  exact connected_of_reachable (v₀ := .signal ⟨.input ⟨0, hN⟩, hi⟩) fun o =>
    (exists_reachable_of_isTotallyRegular hM hc ⟨0, hN⟩ o).2

/-- A circuit computing a totally regular map reads all of its inputs. -/
theorem read_eq_univ_of_isTotallyRegular (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x) (Acc : Fin N → Set F) :
    (network c I Acc).read = univ := by
  rw [read_network]
  exact eq_univ_of_forall fun i => (exists_reachable_of_isTotallyRegular hM hc i i).1

omit [Field F] in
/-- In the network of a circuit computing a function, a vertex reads one input or holds one
output, or neither. -/
theorem ncard_readAt_add_ncard_le (v : Vertex c) :
    ((network c I fun _ => univ).readAt v).ncard + {o | Vertex.output o = v}.ncard ≤ 1 := by
  rcases v with w | j | o
  · have h : {o | (Vertex.output o : Vertex c) = .signal w} = ∅ :=
      eq_empty_of_forall_notMem fun o ho => by cases ho
    rw [h, ncard_empty, add_zero]
    exact ncard_readAt_le I _ _
  · have h1 : (network c I fun _ => univ).readAt (.junction j) = ∅ :=
      eq_empty_of_forall_notMem fun i hi => by
        obtain ⟨_, h⟩ := site_eq_some (c := c) hi
        cases h
    have h2 : {o | (Vertex.output o : Vertex c) = .junction j} = ∅ :=
      eq_empty_of_forall_notMem fun o ho => by cases ho
    simp [h1]
  · have h1 : (network c I fun _ => univ).readAt (.output o) = ∅ :=
      eq_empty_of_forall_notMem fun i hi => by
        obtain ⟨_, h⟩ := site_eq_some (c := c) hi
        cases h
    have h2 : {o' | (Vertex.output o' : Vertex c) = .output o}.ncard ≤ 1 :=
      (ncard_le_one (toFinite _)).mpr fun o₁ h₁ o₂ h₂ => by
        rw [mem_ofPred_eq, Vertex.output.injEq] at h₁ h₂
        rw [h₁, h₂]
    rw [h1, ncard_empty, zero_add]
    exact h2

/-- **Some frontier of every layout determines the input.** For a circuit computing a totally
regular map, every layout of its graph has a time at which the values of the circuit on the
frontier determine the input. -/
theorem exists_injective_frontier (hM : M.IsTotallyRegular) (hc : c.Computes I fun x => M *ᵥ x)
    (π : Layout (Vertex c)) :
    ∃ t, Function.Injective fun (x : Fin N → F) (e : (graph c).frontier π t) =>
      c.program.trace I x e.val.signal.val := by
  classical
  set G := network c I fun _ => univ
  -- `a t` counts the inputs read and the outputs held by the first `t` vertices.
  let outs : Set (Vertex c) → Set (Fin N) := fun P => {o | .output o ∈ P}
  let a : ℕ → ℕ := fun t => (G.readIn (π.initial t)).ncard + (outs (π.initial t)).ncard
  have h0 : a 0 = 0 := by simp [a, outs]
  have hT : N ≤ a (Nat.card (Vertex c)) := by
    -- All outputs are held at the end.
    simp only [a, outs, π.initial_of_card_le le_rfl, mem_univ, ofPred_true, ncard_univ,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  have hstep : ∀ t < Nat.card (Vertex c), a (t + 1) ≤ a t + 1 := by
    intro t ht
    set v := π.symm ⟨t, ht⟩
    have hsucc := π.initial_succ ht
    have hread : G.readIn (π.initial (t + 1)) ⊆ G.readIn (π.initial t) ∪ G.readAt v := by
      rw [hsucc]
      exact G.readIn_insert_subset _ _
    have houts : outs (π.initial (t + 1)) ⊆ outs (π.initial t) ∪ {o | .output o = v} := by grind
    have := ncard_le_ncard hread (toFinite _)
    have := ncard_le_ncard houts (toFinite _)
    have := ncard_union_le (G.readIn (π.initial t)) (G.readAt v)
    have := ncard_union_le (outs (π.initial t)) {o | .output o = v}
    have : (G.readAt v).ncard + {o | Vertex.output o = v}.ncard ≤ 1 :=
      ncard_readAt_add_ncard_le v
    simp only [a]
    omega
  obtain ⟨t, -, hat⟩ := Nat.exists_eq_of_forall_le_add_one (h0.trans_le (Nat.zero_le N)) hT hstep
  refine ⟨t, fun x x' hxx' => ?_⟩
  set P := π.initial t
  set X := G.readIn P
  set Y := outs P
  have hXY : X.ncard + Y.ncard = N := hat
  have hcut : ∀ e ∈ (graph c).edgeCut P,
      c.program.trace I x e.signal.val = c.program.trace I x' e.signal.val :=
    fun e he => congrFun hxx' ⟨e, he⟩
  have hcompl : ∀ S : Set (Fin N), Sᶜ.ncard = N - S.ncard := fun S => by
    have := ncard_add_ncard_compl_fin S; omega
  -- Two inputs that agree on a set `B` of coordinates, and whose outputs agree on a set `R` of at
  -- least `|Bᶜ|` outputs, are equal: the matrix is totally regular.
  have key (B R : Set (Fin N)) (z y : Fin N → F) (hBR : Bᶜ.ncard ≤ R.ncard) (hzy : EqOn z y B)
      (hout : ∀ o ∈ R, c.eval I z o = c.eval I y o) : z = y := by
    refine sub_eq_zero.mp (hM.eq_zero_of_mulVec_eq_zero (rows := R.toFinset) (cols := Bᶜ.toFinset)
      (by rwa [← ncard_eq_toFinset_card', ← ncard_eq_toFinset_card']) (fun j hj => ?_)
      fun o ho => ?_)
    · simp [hzy (by simpa using hj)]
    · rw [mulVec_sub, Pi.sub_apply, ← eval_eq_mulVec hc, ← eval_eq_mulVec hc,
        hout o (by simpa using ho), sub_self]
  -- Off `X`: splice `x` at `P` with `x'` elsewhere; the outputs in `Y` are those of `x`.
  have hoff : X.piecewise x x' = x :=
    key X Y _ x (by rw [hcompl]; omega) (X.piecewise_eqOn x x') fun o ho =>
      (eval_splice hcut (X.piecewise_eqOn x x') (X.piecewise_eqOn_compl x x') o).1 ho
  -- On `X`: splice `x'` at `P` with `x` elsewhere; the outputs off `Y` are those of `x`.
  have hon : X.piecewise x' x = x :=
    key Xᶜ Yᶜ _ x (by rw [compl_compl, hcompl]; omega) (X.piecewise_eqOn_compl x' x) fun o ho =>
      (eval_splice (fun e he => (hcut e he).symm) (X.piecewise_eqOn x' x)
        (X.piecewise_eqOn_compl x' x) o).2 ho
  funext j
  by_cases hj : j ∈ X
  · simpa [X.piecewise_eq_of_mem _ _ hj] using (congrFun hon j).symm
  · simpa [X.piecewise_eq_of_notMem _ _ hj] using (congrFun hoff j).symm

/-- **Every layout is wide.** Every layout of the graph of a circuit with linear capacity
computing a totally regular map `F^N → F^N` has width at least `N`. -/
private theorem le_width_of_isTotallyRegular (hM : M.IsTotallyRegular)
    (hc : c.Computes I fun x => M *ᵥ x)
    (hcap : c.LinearCapacity I) (π : Layout (Vertex c)) : N ≤ (graph c).width π := by
  obtain ⟨t, ht⟩ := exists_injective_frontier hM hc π
  -- The wires carried by the frontier.
  set W := (fun e : Edge c => e.signal.val) '' (graph c).frontier π t
  have hW : Function.Injective fun (x : Fin N → F) (w : W) => c.program.trace I x w :=
    fun x x' h => ht (funext fun e => congrFun h ⟨_, mem_image_of_mem _ e.property⟩)
  exact (hcap W hW).trans ((ncard_image_le (toFinite _)).trans
    ((graph c).ncard_frontier_le_width π t))

/-! ### One-way and unbalanced cut demands -/

section DirectedDemand

/-- **One-way wire determinism across an entering cut.** In `Compiler.graph c`, if two inputs `x`
and `x'` agree on the inputs read in `P` and produce equal values on every signal carried by an
edge entering `P` from `Pᶜ`, then `c` produces equal outputs on `x` and `x'` at every output vertex
in `P`. -/
theorem eval_eq_of_eqOn_inCut {U : Type*} {n m : ℕ} {c : Circuit σ n m} (I : Interpretation σ U)
    {P : Set (Vertex c)} {x x' : Fin n → U}
    (hin : EqOn x x' ((network c I fun _ => univ).readIn P))
    (hcut : ∀ e ∈ (graph c).inCut P,
      c.program.trace I x e.signal.val = c.program.trace I x' e.signal.val)
    {o : Fin m} (ho : Vertex.output o ∈ P) :
    c.eval I x o = c.eval I x' o := by
  have hjunc : ∀ (w : Signal c),
      (Vertex.signal w ∈ P → c.program.trace I x w.val = c.program.trace I x' w.val) →
        ∀ (k : ℕ) (hk : k < fanout c w), Vertex.junction ⟨w, ⟨k, hk⟩⟩ ∈ P →
          c.program.trace I x w.val = c.program.trace I x' w.val := by
    intro w hw k
    induction k with
    | zero => exact fun hk hj => (em _).elim hw fun hs => hcut (.feed ⟨w, ⟨0, hk⟩⟩) ⟨hs, hj⟩
    | succ k ih => exact fun hk hj =>
        (em _).elim (ih (Nat.lt_of_succ_lt hk)) fun hs => hcut (.feed ⟨w, ⟨k + 1, hk⟩⟩) ⟨hs, hj⟩
  have hwire : ∀ (w : Wire n c.size) (hw : Reach c w),
      Vertex.signal ⟨w, hw⟩ ∈ P → c.program.trace I x w = c.program.trace I x' w := by
    refine c.program.wire_induction (fun i hi hP => hin ⟨_, hP, site_of_reach hi⟩) ?_
    intro g ih hg hP
    rw [c.program.trace_gate, c.program.trace_gate]
    refine congrArg _ (funext fun a => ?_)
    set e := argEdge hg a
    have htgt : (graph c).tgt e = Vertex.signal ⟨.gate g, hg⟩ := tgt_deliverEdge (.inl ⟨⟨g, a⟩, hg⟩)
    have hsig : e.signal.val = (c.program.lines g).wires a :=
      congrArg Subtype.val (signal_deliverEdge (.inl ⟨⟨g, a⟩, hg⟩))
    by_cases hs : (graph c).src e ∈ P
    · set j := (junctionEquiv c).symm (.inl ⟨⟨g, a⟩, hg⟩)
      have hjP : Vertex.junction j ∈ P := hs
      have hj1 : j.1 = ⟨(c.program.lines g).wires a, .arg a hg⟩ :=
        fst_junctionEquiv_symm (.inl ⟨⟨g, a⟩, hg⟩)
      have hval := hjunc j.1 (fun hsigP => by
        rw [hj1] at hsigP ⊢
        exact ih a (.arg a hg) hsigP) j.2.val j.2.isLt hjP
      rwa [hj1] at hval
    · exact hsig ▸ hcut e ⟨hs, htgt ▸ hP⟩
  have htgt : (graph c).tgt (outEdge c o) = Vertex.output o := tgt_deliverEdge (.inr o)
  have hsig : (outEdge c o).signal.val = c.outputs o :=
    congrArg Subtype.val (signal_deliverEdge (.inr o))
  change c.program.trace I x (c.outputs o) = c.program.trace I x' (c.outputs o)
  by_cases hs : (graph c).src (outEdge c o) ∈ P
  · set j := (junctionEquiv c).symm (.inr o)
    have hjP : Vertex.junction j ∈ P := hs
    have hjw : j.1.val = c.outputs o :=
      congrArg Subtype.val (fst_junctionEquiv_symm (.inr o))
    exact hjw ▸ hjunc j.1 (hwire j.1.val j.1.property) j.2.val j.2.isLt hjP
  · exact hsig ▸ hcut (outEdge c o) ⟨hs, htgt ▸ ho⟩

/-- **Entering cut demand for totally regular maps.** For every set `P` of vertices in the graph of
a circuit with linear capacity computing `x ↦ M x` for a totally regular `N × N` matrix `M`, at
least `min (N - |X(P)|) |Y(P)|` edges enter `P` from outside `P`. -/
theorem min_le_ncard_inCut (hM : M.IsTotallyRegular) (hc : c.Computes I fun x => M *ᵥ x)
    (hcap : c.LinearCapacity I) (P : Set (Vertex c)) :
    min (N - ((network c I fun _ => univ).readIn P).ncard)
      {o : Fin N | Vertex.output o ∈ P}.ncard ≤ ((graph c).inCut P).ncard := by
  classical
  set X := (network c I fun _ => univ).readIn P
  set Y : Set (Fin N) := {o | Vertex.output o ∈ P}
  set k := min (N - X.ncard) Y.ncard
  have hXcompl : Xᶜ.toFinset.card = N - X.ncard := by
    rw [← ncard_eq_toFinset_card']; have := ncard_add_ncard_compl_fin X; omega
  obtain ⟨C₀, hC₀X, hC₀k⟩ := Finset.exists_subset_card_eq
    (s := Xᶜ.toFinset) (n := k) (by omega)
  set B : Set (Fin N) := (C₀ : Set (Fin N))ᶜ
  have hXB : X ⊆ B := fun i hi hiC => (mem_toFinset.mp (hC₀X hiC)) hi
  have hBc : Bᶜ.toFinset.card = k := by
    rw [← ncard_eq_toFinset_card', compl_compl, ncard_coe_finset, hC₀k]
  have hBcard : B.ncard = N - k := by
    have := ncard_add_ncard_compl_fin B
    rw [compl_compl, ncard_coe_finset, hC₀k] at this
    omega
  set Win : Set (Wire N c.size) := (fun e : Edge c => e.signal.val) '' (graph c).inCut P
  set W' : Set (Wire N c.size) := Win ∪ (Wire.input '' B)
  have hinj : Function.Injective fun (x : Fin N → F) (w : W') => c.program.trace I x w := by
    intro x x' hxx'
    have hB : EqOn x x' B := fun i hi => congrFun hxx' ⟨.input i, Or.inr ⟨i, hi, rfl⟩⟩
    have hcut : ∀ e ∈ (graph c).inCut P,
        c.program.trace I x e.signal.val = c.program.trace I x' e.signal.val :=
      fun e he => congrFun hxx' ⟨e.signal.val, Or.inl ⟨e, he, rfl⟩⟩
    have hout : ∀ o ∈ Y, c.eval I x o = c.eval I x' o :=
      fun o ho => eval_eq_of_eqOn_inCut I (hB.mono hXB) hcut ho
    refine sub_eq_zero.mp (hM.eq_zero_of_mulVec_eq_zero (rows := Y.toFinset)
      (cols := Bᶜ.toFinset) ?_ (fun j hj => ?_) fun o ho => ?_)
    · rw [hBc, ← ncard_eq_toFinset_card']
      exact min_le_right _ _
    · simp [hB (by simpa [B] using hj)]
    · rw [mulVec_sub, Pi.sub_apply, ← eval_eq_mulVec hc, ← eval_eq_mulVec hc,
        hout o (by simpa using ho), sub_self]
  have hNle : N ≤ W'.ncard := hcap W' hinj
  have hWle : W'.ncard ≤ ((graph c).inCut P).ncard + (N - k) := by
    calc W'.ncard ≤ Win.ncard + (Wire.input '' B).ncard := ncard_union_le _ _
      _ ≤ ((graph c).inCut P).ncard + B.ncard :=
          Nat.add_le_add (ncard_image_le (toFinite _)) (ncard_image_le (toFinite _))
      _ = ((graph c).inCut P).ncard + (N - k) := by rw [hBcard]
  have hkN : k ≤ N := (min_le_left _ _).trans (Nat.sub_le _ _)
  omega

/-- **Leaving cut demand for totally regular maps.** Dual to `min_le_ncard_inCut`: at least
`min |X(P)| (N - |Y(P)|)` edges leave `P` to `Pᶜ`. -/
theorem min_le_ncard_outCut (hM : M.IsTotallyRegular) (hc : c.Computes I fun x => M *ᵥ x)
    (hcap : c.LinearCapacity I) (P : Set (Vertex c)) :
    min ((network c I fun _ => univ).readIn P).ncard
      (N - {o : Fin N | Vertex.output o ∈ P}.ncard) ≤ ((graph c).outCut P).ncard := by
  have h := min_le_ncard_inCut hM hc hcap Pᶜ
  rw [(graph c).inCut_compl] at h
  set G := network c I fun _ => univ
  have hread_compl : G.readIn Pᶜ = (G.readIn P)ᶜ := by
    ext i
    obtain ⟨hi, -⟩ := exists_reachable_of_isTotallyRegular hM hc i i
    constructor
    · rintro ⟨v, hvP, hsite⟩ ⟨u, huP, hsite'⟩
      exact hvP (Option.some.inj (hsite.symm.trans hsite') ▸ huP)
    · exact fun hiP =>
        ⟨.signal ⟨.input i, hi⟩, fun hP => hiP ⟨_, hP, site_of_reach hi⟩, site_of_reach hi⟩
  have hX := ncard_add_ncard_compl_fin (G.readIn P)
  have hY := ncard_add_ncard_compl_fin {o : Fin N | Vertex.output o ∈ P}
  rw [hread_compl] at h
  change min (N - (G.readIn P)ᶜ.ncard) {o : Fin N | Vertex.output o ∈ P}ᶜ.ncard ≤ _ at h
  omega

/-- **Unbalanced cut demand for totally regular maps.** For *every* set `P` of vertices in the
graph of a circuit with linear capacity computing `x ↦ M x` for a totally regular `N × N` matrix
`M`, writing `w(P) = |X(P)| + |Y(P)|`, at least `min (w(P)) (2 N - w(P))` edges cross `edgeCut P`.
When `w(P) = N`, this recovers the balanced demand `N`. -/
theorem min_le_ncard_edgeCut (hM : M.IsTotallyRegular) (hc : c.Computes I fun x => M *ᵥ x)
    (hcap : c.LinearCapacity I) (P : Set (Vertex c)) :
    min (((network c I fun _ => univ).readIn P).ncard + {o : Fin N | Vertex.output o ∈ P}.ncard)
      (2 * N - (((network c I fun _ => univ).readIn P).ncard +
        {o : Fin N | Vertex.output o ∈ P}.ncard)) ≤
      ((graph c).edgeCut P).ncard := by
  have hin := min_le_ncard_inCut hM hc hcap P
  have hout := min_le_ncard_outCut hM hc hcap P
  have hX := ncard_add_ncard_compl_fin ((network c I fun _ => univ).readIn P)
  have hY := ncard_add_ncard_compl_fin {o : Fin N | Vertex.output o ∈ P}
  rw [(graph c).ncard_edgeCut_eq_add P]
  omega

end DirectedDemand

end Compiler

/-! ### The lower bound -/

variable {F : Type u} [Field F] {σ : Signature.{v}} {I : Interpretation σ F} {N r : ℕ}
  {M : Matrix (Fin N) (Fin N) F} {c : Circuit σ N N}

/-- **The reduction theorem for linear maps.** A circuit with `s` inner gates of fan-in at most
`r ≥ 2` and linear capacity, computing a totally regular map `F^N → F^N` with `N ≥ 1`, yields a
connected, loopless multigraph of maximum degree `r + 1` with at most `2 r s + 3 N` vertices and
cycle rank at most `(r - 1) s + 1 - N`, every layout of which has width at least `N`. -/
theorem exists_graph_of_isTotallyRegular (hN : 0 < N) (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    (hM : M.IsTotallyRegular) (hc : c.Computes I fun x => M *ᵥ x) (hcap : c.LinearCapacity I) :
    ∃ (V E : Type) (_ : Finite V) (_ : Finite E) (G : Multigraph V E),
      G.toSimpleGraph.Connected ∧ G.Loopless ∧ G.MaxDegreeLE (r + 1) ∧
      Nat.card V ≤ 2 * r * c.innerSize + 3 * N ∧
      G.cycleRank + N ≤ (r - 1) * c.innerSize + 1 ∧
      ∀ π : Layout V, N ≤ G.width π := by
  have hconn := Compiler.connected_of_isTotallyRegular hN hM hc
  have hrank := Compiler.cycleRank_add_ncard_read_le I (fun _ => univ) hfan hconn
  rw [Compiler.read_eq_univ_of_isTotallyRegular hM hc, ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin] at hrank
  exact ⟨_, _, inferInstance, inferInstance, Compiler.graph c, hconn, Compiler.loopless,
    Compiler.maxDegreeLE hr hfan, Compiler.card_vertex_le hfan, hrank,
    Compiler.le_width_of_isTotallyRegular hM hc hcap⟩

/-- **The frontier lower bound for linear maps.** Let `r ≥ 2` and assume the layout hypothesis
for maximum degree `r + 1` with coefficient `A > 0`. For every `ε > 0` and all large `N`, every
circuit of fan-in at most `r` with linear capacity, over any field and any basis, that computes
`x ↦ M x` for a totally regular `N × N` matrix `M`, has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  obtain ⟨η, hη, H⟩ := eventually_lt_of_demand hA (κ := 4) (by norm_num) hε
  obtain ⟨C, hC⟩ := hlayout η hη
  have he : (fun _ : ℕ => (1 : ℝ)) =o[atTop] fun N => (N : ℝ) :=
    isLittleO_const_left.mpr (Or.inr (tendsto_norm_atTop_atTop.comp tendsto_natCast_atTop_atTop))
  filter_upwards [H η hη le_rfl C _ he, eventually_ge_atTop 1] with N hN hN1
  intro F _ σ I M c hM hfan hc hcap
  obtain ⟨V, E, _, _, G, hconn, hloop, hdeg, hV, hrank, hwidth⟩ :=
    exists_graph_of_isTotallyRegular hN1 hr hfan hM hc hcap
  obtain ⟨π, hπ⟩ := hC V E G hconn hloop hdeg
  -- The quantities of the comparison.
  set s : ℝ := (r - 1) * c.innerSize
  have hcast : (((r - 1) * c.innerSize : ℕ) : ℝ) = s := by
    rw [Nat.cast_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have hs : 0 ≤ s := hcast ▸ Nat.cast_nonneg _
  have hVs : (Nat.card V : ℝ) ≤ 4 * (N + s + 1) := by
    -- `2 r s + 3 N ≤ 4 (r - 1) s + 4 N`, since `2 r ≤ 4 (r - 1)`.
    have : 2 * r * c.innerSize + 3 * N ≤ 4 * ((r - 1) * c.innerSize) + 4 * N := by
      have : 2 * r ≤ 4 * (r - 1) := by omega
      nlinarith
    have h4 : (Nat.card V : ℝ) ≤ 4 * ((r - 1) * c.innerSize : ℕ) + 4 * N := by
      exact_mod_cast hV.trans this
    rw [hcast] at h4
    linarith
  refine hN s (Nat.card V) (G.width π) hs (Nat.cast_nonneg _) hVs ?_ ?_
  · -- The demand: every layout has width at least `N`.
    have h1 : (N : ℝ) ≤ G.width π := by exact_mod_cast hwidth π
    have h2 : 0 ≤ Real.log (Nat.card V + 1) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) (Nat.card V)])
    linarith
  · -- The supply: the layout hypothesis, with the cycle rank of the reduction.
    have hrank' : (G.cycleRank : ℝ) ≤ s - N + 1 := by cast_linarith [hrank]
    have := mul_le_mul_of_nonneg_left hrank' (by linarith : 0 ≤ A + η)
    linarith

/-- **The frontier lower bound for linear maps over finite fields**, for every basis. Under the
hypotheses of `eventually_lt_mul_innerSize_of_isTotallyRegular`, for every `ε > 0` and all large
`N`, every circuit of fan-in at most `r` over a finite field `F`, over any basis, that computes
`x ↦ M x` for a totally regular `N × N` matrix `M` has `s` inner gates with
`(r - 1) s > (1 + 1/A - ε) N`. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular_finite (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        M.IsTotallyRegular → c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_isTotallyRegular.{u, v} hr hA hlayout hε]
    with N hN
  intro F _ _ σ I M c hM hfan hc
  exact hN F σ I M c hM hfan hc (c.linearCapacity_of_finite I)

/-- **The frontier lower bound for linear maps over the affine basis**, over every field. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular_affine (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (M : Matrix (Fin N) (Fin N) F)
      (c : Circuit (affineSignature F) N N), M.IsTotallyRegular → c.FanInAtMost r →
        c.Computes (affineInterpretation F) (fun x => M *ᵥ x) →
          (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_isTotallyRegular.{u, u} hr hA hlayout hε]
    with N hN
  intro F _ M c hM hfan hc
  exact hN F _ _ M c hM hfan hc c.linearCapacity_affine

/-- **The frontier lower bound for linear maps over infinite fields**, for every basis of
polynomial operations: their coefficients and degrees are arbitrary. -/
theorem eventually_lt_mul_innerSize_of_isTotallyRegular_isPolynomial (hr : 2 ≤ r) {A : ℝ}
    (hA : 0 < A) (hlayout : LayoutBound (r + 1) A) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), I.IsPolynomial → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), M.IsTotallyRegular → c.FanInAtMost r →
          c.Computes I (fun x => M *ᵥ x) → (1 + 1 / A - ε) * N < (r - 1) * c.innerSize := by
  filter_upwards [eventually_lt_mul_innerSize_of_isTotallyRegular_affine.{u} hr hA hlayout hε]
    with N hN
  intro F _ _ σ I hI M c hM hfan hc
  obtain ⟨c', -, hinner, hfan', -, hc'⟩ := hc.exists_affine hI
  rw [← hinner]
  exact hN F M c' hM ((hfan' r).mpr hfan) hc'

end Frontier

end Cslib.Circuits
