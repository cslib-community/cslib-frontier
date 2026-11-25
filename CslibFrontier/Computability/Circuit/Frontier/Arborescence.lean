/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Closure
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.ArborescenceIndep
import CslibFrontier.Computability.Circuit.FanIn
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Arborescence 2-SAT frontier bounds for fan-in-two `U₂` circuits

When a Boolean circuit `c` has fan-in at most `2`, removing the depth-one determined wires
`c.program.depthOneDetermined W` from any wire set `W` leaves every remaining wire `w ∈ R`
(`R ⊆ W \ c.program.depthOneDetermined W`) with **at most one** incoming `ClauseEdge` in `R`: if
two distinct wires `u₁, u₂ ∈ R` fed `w = .gate g`, their argument slots `a₁ ≠ a₂` would exhaust all
`≤ 2` slots of `g`, placing `w` in `depthOneDetermined W`
(`clauseEdge_subsingleton_of_sdiff_depthOneDetermined`).

Consequently, `clauseDigraph c.program I R` is a branching
(`isBranching_clauseDigraph_of_sdiff_depthOneDetermined`), its underlying simple graph
`u2ClauseGraph c.program I R` is unconditionally an acyclic forest
(`isAcyclic_u2ClauseGraph_of_sdiff_depthOneDetermined`), and
`SimpleGraph.logb_indepSetCount_fromRel_le_capped` bounds the number of distinct frontier states at
every layout step `t` by

`Real.logb 2 |States_t| ≤ |W_t| - |D| - (53 / 200) * cappedEdges - (33 / 1000) * |activeRoots|`

for any `D₀(W_t) ⊆ D ⊆ D*(W_t)` (`logb_ncard_frontierValues_le_arborescence`). Amortizing each wire
of `D₀(W_t)` against its `≤ 2` incoming and `≤ 2` two-capped outgoing clauses
(`twoCappedClauseEdges_le_add_four_mul`) yields the clean `D₀`-free `1 / 4`-per-clause bound on the
unreduced cut `W_t` (`logb_ncard_frontierValues_le_quarter_sub`). These results are original to this
library.

## Main definitions

* `Cslib.Circuits.Frontier.clauseDigraph`: the directed `ClauseEdge` graph on a wire subset `R`.
* `Cslib.Circuits.Frontier.clauseActiveRoots`, `Cslib.Circuits.Frontier.clauseCappedEdges`: active
  roots and degree-capped arc count of `clauseDigraph p I R`.
* `Cslib.Circuits.Frontier.twoCappedClauseEdges`: total outgoing `ClauseEdge`s on `W` capped at `2`
  per source wire.

## Main results

* `Cslib.Circuits.Frontier.u2ClauseGraph_eq_fromRel`: `u2ClauseGraph` equals `SimpleGraph.fromRel`
  of `(clauseDigraph p I R).Adj`.
* `Cslib.Circuits.Frontier.clauseEdge_subsingleton_of_sdiff_depthOneDetermined`,
  `Cslib.Circuits.Frontier.isBranching_clauseDigraph_of_sdiff_depthOneDetermined`: for fan-in at
  most `2`, `clauseDigraph p I R` is a branching whenever `R ⊆ W \ p.depthOneDetermined W`.
* `Cslib.Circuits.Frontier.isAcyclic_u2ClauseGraph_of_sdiff_depthOneDetermined`,
  `Cslib.Circuits.Frontier.isAcyclic_u2ClauseGraph_cutWires_sdiff`: reduced `U₂` clause graphs are
  acyclic forests.
* `Cslib.Circuits.Frontier.logb_indepSetCount_u2ClauseGraph_le_capped`,
  `Cslib.Circuits.Frontier.logb_indepSetCount_u2ClauseGraph_le`: `(53 / 200)` edge and
  `(33 / 1000)` active-root `indepSetCount` bounds on `u2ClauseGraph`.
* `Cslib.Circuits.Frontier.logb_ncard_frontierValues_le_arborescence`,
  `Cslib.Circuits.Frontier.ncard_frontierValues_le_rpow_arborescence`,
  `Cslib.Circuits.Frontier.logb_ncard_frontierValues_le_arborescence_depthOne`: frontier state
  bounds along any layout `π`.
* `Cslib.Circuits.Frontier.twoCappedClauseEdges_le_add_four_mul`,
  `Cslib.Circuits.Frontier.logb_ncard_frontierValues_le_quarter_sub`: `4 * |D₀|` clause-loss bound
  and `D₀`-free `1 / 4`-per-clause amortized frontier bound on `cutWires c (π.initial t)`.
-/

public section

namespace Cslib.Circuits.Frontier

open Set

universe v

section OutForest

variable {σ : Signature.{v}} {n s m : ℕ}

/-- Strict topological index of a wire in `Program σ n s`: inputs `0 .. n - 1` precede gates
`n .. n + s - 1`. -/
private def wireRank : Wire n s → ℕ
  | .input i => i.val
  | .gate g => n + g.val

private theorem wireRank_lt_of_clauseEdge {p : Program σ n s} {I : Interpretation σ Bool}
    {u w : Wire n s} (h : ClauseEdge p I u w) : wireRank u < wireRank w := by
  obtain ⟨g, a, rfl, hwire, -⟩ := h
  cases u with
  | input i =>
    dsimp only [wireRank]
    have := i.isLt
    omega
  | gate j =>
    dsimp only [wireRank]
    have hlt := p.lt_of_lines_wires_eq_gate g a j hwire
    omega

/-- Directed `ClauseEdge` graph on a wire subset `R : Set (Wire n s)`. -/
@[expose] def clauseDigraph (p : Program σ n s) (I : Interpretation σ Bool)
    (R : Set (Wire n s)) : Digraph R where
  Adj u w := ClauseEdge p I u.1 w.1

@[simp]
theorem clauseDigraph_adj (p : Program σ n s) (I : Interpretation σ Bool)
    (R : Set (Wire n s)) (u w : R) :
    (clauseDigraph p I R).Adj u w ↔ ClauseEdge p I u.1 w.1 := Iff.rfl

/-- `u2ClauseGraph p I R` is `SimpleGraph.fromRel` of `(clauseDigraph p I R).Adj`. -/
theorem u2ClauseGraph_eq_fromRel (p : Program σ n s) (I : Interpretation σ Bool)
    (R : Set (Wire n s)) :
    u2ClauseGraph p I R = SimpleGraph.fromRel (clauseDigraph p I R).Adj := by
  ext u w
  rw [u2ClauseGraph_adj, SimpleGraph.fromRel_adj]
  constructor
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h1 | h2 <;> exact (wireRank_lt_of_clauseEdge ‹_›).ne rfl
  · exact fun h => h.2

/-- **At most one cut input (`d_in ≤ 1`).** In a fan-in-at-most-2 program `p`, removing
`p.depthOneDetermined W` ensures every wire in any subset `R ⊆ W \ p.depthOneDetermined W` has at
most one incoming `ClauseEdge` from `R`. -/
theorem clauseEdge_subsingleton_of_sdiff_depthOneDetermined {p : Program σ n s}
    (hfan : p.FanInAtMost 2) (I : Interpretation σ Bool) {W R : Set (Wire n s)}
    (hR : R ⊆ W \ p.depthOneDetermined W) (w : R) :
    {u : R | ClauseEdge p I u.1 w.1}.Subsingleton := by
  intro u₁ hu₁ u₂ hu₂
  by_contra hne
  have hne_val : u₁.1 ≠ u₂.1 := fun h => hne (Subtype.ext h)
  obtain ⟨g₁, a₁, hw₁, hwire₁, -⟩ := hu₁
  obtain ⟨g₂, a₂, hw₂, hwire₂, -⟩ := hu₂
  have hg : g₁ = g₂ := Wire.gate.inj (hw₁.symm.trans hw₂)
  subst hg
  have ha_ne : a₁ ≠ a₂ := fun ha => hne_val (hwire₁.symm.trans (ha ▸ hwire₂))
  have harity : σ.Arity (p.lines g₁).op ≤ 2 := Program.fanInAtMost_iff.mp hfan g₁
  have hw_mem := hR w.2
  refine hw_mem.2 ⟨hw_mem.1, g₁, hw₁, fun a => ?_⟩
  have ha_lt := a.isLt
  have ha1_lt := a₁.isLt
  have ha2_lt := a₂.isLt
  have ha12_ne : a₁.val ≠ a₂.val := fun hv => ha_ne (Fin.ext hv)
  have ha_cases : a = a₁ ∨ a = a₂ := by
    rcases (by omega : a.val = a₁.val ∨ a.val = a₂.val) with h1 | h2
    · exact Or.inl (Fin.ext h1)
    · exact Or.inr (Fin.ext h2)
  rcases ha_cases with rfl | rfl
  · rw [hwire₁]
    exact (hR u₁.2).1
  · rw [hwire₂]
    exact (hR u₂.2).1

/-- **Branching property of `clauseDigraph`.** For any fan-in-at-most-2 program `p` and any
`R ⊆ W \ p.depthOneDetermined W`, `clauseDigraph p I R` is a branching. -/
theorem isBranching_clauseDigraph_of_sdiff_depthOneDetermined {p : Program σ n s}
    (hfan : p.FanInAtMost 2) (I : Interpretation σ Bool) {W R : Set (Wire n s)}
    (hR : R ⊆ W \ p.depthOneDetermined W) :
    (clauseDigraph p I R).IsBranching :=
  Digraph.IsBranching.of_rank (rk := fun u : R => wireRank u.1)
    (fun _ _ h => wireRank_lt_of_clauseEdge h)
    (fun _ _ w h1 h2 => clauseEdge_subsingleton_of_sdiff_depthOneDetermined hfan I hR w h1 h2)

/-- **Out-forest acyclicity of `u2ClauseGraph`.** For any fan-in-at-most-2 program `p` and any
`R ⊆ W \ p.depthOneDetermined W`, `u2ClauseGraph p I R` is an acyclic forest. -/
theorem isAcyclic_u2ClauseGraph_of_sdiff_depthOneDetermined {p : Program σ n s}
    (hfan : p.FanInAtMost 2) (I : Interpretation σ Bool) {W R : Set (Wire n s)}
    (hR : R ⊆ W \ p.depthOneDetermined W) :
    (u2ClauseGraph p I R).IsAcyclic := by
  rw [u2ClauseGraph_eq_fromRel]
  exact (isBranching_clauseDigraph_of_sdiff_depthOneDetermined hfan I hR).toSimpleGraph_isAcyclic

/-- Reduced `u2ClauseGraph` on `cutWires c P \ D` is acyclic whenever
`c.program.depthOneDetermined (cutWires c P) ⊆ D` (including both `D = D₀` and `D = D*`). -/
theorem isAcyclic_u2ClauseGraph_cutWires_sdiff {c : Circuit σ n m} (hfan : c.FanInAtMost 2)
    (I : Interpretation σ Bool) (P : Set (Compiler.Vertex c)) {D : Set (Wire n c.size)}
    (hD : c.program.depthOneDetermined (cutWires c P) ⊆ D) :
    (u2ClauseGraph c.program I (cutWires c P \ D)).IsAcyclic :=
  isAcyclic_u2ClauseGraph_of_sdiff_depthOneDetermined hfan I fun _ hw =>
    ⟨hw.1, fun hd => hw.2 (hD hd)⟩

/-! ### Exact rational Tree-DP frontier bounds (`α = 53 / 200`, `δ_root = 33 / 1000`) -/

/-- Active roots of the `ClauseEdge` out-forest on `R`: wires in `R` with no incoming `ClauseEdge`
from `R` and at least one outgoing `ClauseEdge` into `R`. -/
@[expose] def clauseActiveRoots (p : Program σ n s) (I : Interpretation σ Bool)
    (R : Set (Wire n s)) : Set R :=
  SimpleGraph.arborescenceActiveRoots (clauseDigraph p I R)

/-- Total outgoing `ClauseEdge`s in `R` after capping non-roots at `2` and roots at `3`. -/
@[expose] noncomputable def clauseCappedEdges (p : Program σ n s) (I : Interpretation σ Bool)
    (R : Set (Wire n s)) : ℕ :=
  SimpleGraph.arborescenceCappedEdges (clauseDigraph p I R)

/-- **Arborescence `indepSetCount` bound on `u2ClauseGraph` (arbitrary out-degrees).** -/
theorem logb_indepSetCount_u2ClauseGraph_le_capped {p : Program σ n s} (hfan : p.FanInAtMost 2)
    (I : Interpretation σ Bool) {W R : Set (Wire n s)}
    (hR : R ⊆ W \ p.depthOneDetermined W) :
    Real.logb 2 ((u2ClauseGraph p I R).indepSetCount : ℝ) ≤
      (R.ncard : ℝ) - (53 / 200 : ℝ) * (clauseCappedEdges p I R : ℝ) -
        (33 / 1000 : ℝ) * ((clauseActiveRoots p I R).ncard : ℝ) := by
  have h := SimpleGraph.logb_indepSetCount_fromRel_le_capped
    (isBranching_clauseDigraph_of_sdiff_depthOneDetermined hfan I hR)
  rw [← u2ClauseGraph_eq_fromRel, Nat.card_coe_set_eq] at h
  exact h

/-- **Arborescence `indepSetCount` bound on `u2ClauseGraph` (bounded out-degrees).** When internal
wires in `R` have at most `2` outgoing clauses in `R` and roots in `R` have at most `3`,
`clauseCappedEdges` equals `(u2ClauseGraph p I R).edgeSet.ncard`. -/
theorem logb_indepSetCount_u2ClauseGraph_le {p : Program σ n s} (hfan : p.FanInAtMost 2)
    (I : Interpretation σ Bool) {W R : Set (Wire n s)}
    (hR : R ⊆ W \ p.depthOneDetermined W)
    (hout_int : ∀ w : R, (∃ u : R, ClauseEdge p I u.1 w.1) →
      {v : R | ClauseEdge p I w.1 v.1}.ncard ≤ 2)
    (hout_root : ∀ r : R, (¬∃ u : R, ClauseEdge p I u.1 r.1) →
      {v : R | ClauseEdge p I r.1 v.1}.ncard ≤ 3) :
    Real.logb 2 ((u2ClauseGraph p I R).indepSetCount : ℝ) ≤
      (R.ncard : ℝ) - (53 / 200 : ℝ) * ((u2ClauseGraph p I R).edgeSet.ncard : ℝ) -
        (33 / 1000 : ℝ) * ((clauseActiveRoots p I R).ncard : ℝ) := by
  have h := SimpleGraph.logb_indepSetCount_fromRel_le
    (isBranching_clauseDigraph_of_sdiff_depthOneDetermined hfan I hR)
    hout_int hout_root
  rw [← u2ClauseGraph_eq_fromRel, Nat.card_coe_set_eq] at h
  exact h

private theorem logb_ncard_le_logb_pos {m k : ℕ} (hle : m ≤ k) (hk : 0 < k) :
    Real.logb 2 (m : ℝ) ≤ Real.logb 2 (k : ℝ) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp only [Nat.cast_zero, Real.logb_zero]
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    exact Real.logb_nonneg (by norm_num) hk1
  · exact Real.logb_le_logb_of_le (by norm_num) (Nat.cast_pos.mpr hm) (by exact_mod_cast hle)

/-- **Combined `D*(∂)` + Arborescence frontier state bound.** Along any layout `π` of a fan-in-2
Boolean circuit `c`, for any `D` with `D₀(W_t) ⊆ D ⊆ D*(W_t)` (`W_t = cutWires c (π.initial t)`),
the base-`2` log of the number of distinct frontier states at step `t` is at most
`|W_t| - |D| - (53 / 200) * clauseCappedEdges - (33 / 1000) * |clauseActiveRoots|`. -/
theorem logb_ncard_frontierValues_le_arborescence {c : Circuit σ n m} (hfan : c.FanInAtMost 2)
    (I : Interpretation σ Bool) (Acc : Fin m → Set Bool) (π : Layout (Compiler.Vertex c)) (t : ℕ)
    {D : Set (Wire n c.size)}
    (hD₀ : c.program.depthOneDetermined (cutWires c (π.initial t)) ⊆ D)
    (hD : D ⊆ c.program.forwardDetermined (cutWires c (π.initial t)))
    (X : Set (Fin n → Bool)) :
    Real.logb 2 (((fun x => (Compiler.network c I Acc).frontierValues π t
        (fun e => c.program.trace I x e.signal.1)) '' X).ncard : ℝ) ≤
      ((cutWires c (π.initial t)).ncard : ℝ) - (D.ncard : ℝ) -
        (53 / 200 : ℝ) * (clauseCappedEdges c.program I (cutWires c (π.initial t) \ D) : ℝ) -
        (33 / 1000 : ℝ) *
          ((clauseActiveRoots c.program I (cutWires c (π.initial t) \ D)).ncard : ℝ) := by
  set W := cutWires c (π.initial t)
  set R := W \ D
  have hindep := ncard_frontierValues_le_indepSetCount c I Acc π t hD X
  have hpos : 0 < (u2ClauseGraph c.program I R).indepSetCount :=
    (u2ClauseGraph c.program I R).indepSetCount_pos
  have hlog := logb_ncard_le_logb_pos hindep hpos
  have harb := logb_indepSetCount_u2ClauseGraph_le_capped hfan I
    (W := W) (R := R) (fun _ hw => ⟨hw.1, fun hd => hw.2 (hD₀ hd)⟩)
  have hcard : (R.ncard : ℝ) = (W.ncard : ℝ) - (D.ncard : ℝ) := by
    have hadd := c.program.ncard_sdiff_add_ncard_of_subset_forwardDetermined hD
    have hcast : (R.ncard : ℝ) + (D.ncard : ℝ) = (W.ncard : ℝ) := by exact_mod_cast hadd
    linarith
  linarith

/-- Exponential (`2 ^ ·`) companion to `logb_ncard_frontierValues_le_arborescence`. -/
theorem ncard_frontierValues_le_rpow_arborescence {c : Circuit σ n m} (hfan : c.FanInAtMost 2)
    (I : Interpretation σ Bool) (Acc : Fin m → Set Bool) (π : Layout (Compiler.Vertex c)) (t : ℕ)
    {D : Set (Wire n c.size)}
    (hD₀ : c.program.depthOneDetermined (cutWires c (π.initial t)) ⊆ D)
    (hD : D ⊆ c.program.forwardDetermined (cutWires c (π.initial t)))
    (X : Set (Fin n → Bool)) :
    (((fun x => (Compiler.network c I Acc).frontierValues π t
        (fun e => c.program.trace I x e.signal.1)) '' X).ncard : ℝ) ≤
      (2 : ℝ) ^ (((cutWires c (π.initial t)).ncard : ℝ) - (D.ncard : ℝ) -
        (53 / 200 : ℝ) * (clauseCappedEdges c.program I (cutWires c (π.initial t) \ D) : ℝ) -
        (33 / 1000 : ℝ) *
          ((clauseActiveRoots c.program I (cutWires c (π.initial t) \ D)).ncard : ℝ)) := by
  set S := (fun x => (Compiler.network c I Acc).frontierValues π t
    (fun e => c.program.trace I x e.signal.1)) '' X
  rcases Nat.eq_zero_or_pos S.ncard with h0 | hpos
  · rw [h0, Nat.cast_zero]
    exact (Real.rpow_pos_of_pos (by norm_num) _).le
  · rw [← Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
      (Nat.cast_pos.mpr hpos)]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (logb_ncard_frontierValues_le_arborescence hfan I Acc π t hD₀ hD X)

/-- Specialization of `logb_ncard_frontierValues_le_arborescence` to
`D = c.program.depthOneDetermined (cutWires c (π.initial t))`. -/
theorem logb_ncard_frontierValues_le_arborescence_depthOne {c : Circuit σ n m}
    (hfan : c.FanInAtMost 2) (I : Interpretation σ Bool) (Acc : Fin m → Set Bool)
    (π : Layout (Compiler.Vertex c)) (t : ℕ) (X : Set (Fin n → Bool)) :
    Real.logb 2 (((fun x => (Compiler.network c I Acc).frontierValues π t
        (fun e => c.program.trace I x e.signal.1)) '' X).ncard : ℝ) ≤
      ((cutWires c (π.initial t)).ncard : ℝ) -
        ((c.program.depthOneDetermined (cutWires c (π.initial t))).ncard : ℝ) -
        (53 / 200 : ℝ) * (clauseCappedEdges c.program I
          (cutWires c (π.initial t) \
            c.program.depthOneDetermined (cutWires c (π.initial t))) : ℝ) -
        (33 / 1000 : ℝ) * ((clauseActiveRoots c.program I
          (cutWires c (π.initial t) \
            c.program.depthOneDetermined (cutWires c (π.initial t)))).ncard : ℝ) :=
  logb_ncard_frontierValues_le_arborescence hfan I Acc π t Subset.rfl
    (c.program.depthOneDetermined_subset_forwardDetermined _) X

/-! ### Amortized `1 / 4`-per-clause `D₀`-free bound -/

open Classical in
/-- Total outgoing `ClauseEdge`s on `W` capped at `2` per source wire. -/
@[expose] noncomputable def twoCappedClauseEdges (p : Program σ n s) (I : Interpretation σ Bool)
    (W : Set (Wire n s)) : ℕ :=
  ∑ᶠ u : W, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2

/-- Every wire `w : W` in a fan-in-at-most-2 program has at most `2` incoming `ClauseEdge`s in `W`.
-/
private theorem inDeg_clauseEdge_le_two {p : Program σ n s} (hfan : p.FanInAtMost 2)
    (I : Interpretation σ Bool) (W : Set (Wire n s)) (w : W) :
    {u : W | ClauseEdge p I u.1 w.1}.ncard ≤ 2 := by
  rcases w with ⟨w_val, hw_mem⟩
  cases w_val with
  | input i =>
    have hemp : {u : W | ClauseEdge p I u.1 (.input i)} = ∅ := by
      ext u
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      rintro ⟨g, a, h, -⟩
      cases h
    change {u : W | ClauseEdge p I u.1 (.input i)}.ncard ≤ 2
    rw [hemp, ncard_empty]
    omega
  | gate g =>
    have har : σ.Arity (p.lines g).op ≤ 2 := Program.fanInAtMost_iff.mp hfan g
    change {u : W | ClauseEdge p I u.1 (.gate g)}.ncard ≤ 2
    calc {u : W | ClauseEdge p I u.1 (.gate g)}.ncard
        ≤ ((fun a => (p.lines g).wires a) '' univ).ncard := by
          refine ncard_le_ncard_of_injOn (fun u => u.1) (fun u hu => ?_)
            (fun _ _ _ _ h => Subtype.ext h) (toFinite _)
          obtain ⟨g', a, hg', hwire, -⟩ := hu
          cases Wire.gate.inj hg'
          exact ⟨a, mem_univ a, hwire⟩
      _ ≤ (univ : Set (Fin (σ.Arity (p.lines g).op))).ncard := ncard_image_le (toFinite _)
      _ = σ.Arity (p.lines g).op := by rw [ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
      _ ≤ 2 := har

/-- Removing `D₀ = p.depthOneDetermined W` reduces `twoCappedClauseEdges` by at most `4 * |D₀|`:
at most `2 * |D₀|` from sources `u ∈ D₀` and at most `2 * |D₀|` from targets `w ∈ D₀`. -/
theorem twoCappedClauseEdges_le_add_four_mul {p : Program σ n s} (hfan : p.FanInAtMost 2)
    (I : Interpretation σ Bool) (W : Set (Wire n s)) :
    twoCappedClauseEdges p I W ≤
      clauseCappedEdges p I (W \ p.depthOneDetermined W) +
        4 * (p.depthOneDetermined W).ncard := by
  classical
  set D₀ := p.depthOneDetermined W
  set R := W \ D₀
  cases nonempty_fintype W
  cases nonempty_fintype R
  have hD₀_sub : D₀ ⊆ W := p.depthOneDetermined_subset_forwardDetermined W |>.trans
    (p.forwardDetermined_subset W)
  let Dfin : Finset W := Finset.univ.filter fun u : W => u.1 ∈ D₀
  let Rfin : Finset W := Finset.univ.filter fun u : W => u.1 ∉ D₀
  have hDfin_card : Dfin.card = D₀.ncard := by
    rw [← ncard_coe_finset]
    refine ncard_congr (fun (u : W) _ => u.1)
      (fun u hu => (Finset.mem_filter.mp hu).2)
      (fun _ _ _ _ h => Subtype.ext h)
      (fun w hw => ⟨⟨w, hD₀_sub hw⟩, Finset.mem_coe.mpr
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw⟩), rfl⟩)
  -- Split `∑ u : W` into `Dfin` (`≤ 2 * Dfin.card`) and `Rfin`:
  have hsplit : twoCappedClauseEdges p I W =
      (∑ u ∈ Dfin, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2) +
      (∑ u ∈ Rfin, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2) := by
    rw [twoCappedClauseEdges, finsum_eq_sum_of_fintype]
    exact (Finset.sum_filter_add_sum_filter_not Finset.univ (fun u : W => u.1 ∈ D₀)
      (fun u : W => min {w : W | ClauseEdge p I u.1 w.1}.ncard 2)).symm
  have hD_sum : (∑ u ∈ Dfin, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2) ≤ 2 * D₀.ncard := by
    calc ∑ u ∈ Dfin, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2
        ≤ ∑ _u ∈ Dfin, 2 := Finset.sum_le_sum fun _ _ => Nat.min_le_right _ _
      _ = 2 * D₀.ncard := by rw [Finset.sum_const, smul_eq_mul, mul_comm, hDfin_card]
  -- For each `u : R`, `{w : W | ClauseEdge u w}` splits into `w.1 ∉ D₀` (`R`) and `w.1 ∈ D₀`:
  have hR_term : ∀ u : R, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2 ≤
      min {w : R | ClauseEdge p I u.1 w.1}.ncard
        (if ∃ v : R, ClauseEdge p I v.1 u.1 then 2 else 3) +
      {w ∈ Dfin | ClauseEdge p I u.1 w.1}.card := by
    intro u
    have hle_split : {w : W | ClauseEdge p I u.1 w.1}.ncard ≤
        {w : R | ClauseEdge p I u.1 w.1}.ncard +
          (Dfin.filter fun w : W => ClauseEdge p I u.1 w.1).card := by
      set SR : Set W := {w : W | w.1 ∉ D₀ ∧ ClauseEdge p I u.1 w.1}
      set SD : Set W := {w : W | w.1 ∈ D₀ ∧ ClauseEdge p I u.1 w.1}
      have hun : {w : W | ClauseEdge p I u.1 w.1} ⊆ SR ∪ SD := fun w hw =>
        (em (w.1 ∈ D₀)).elim (fun h => Or.inr ⟨h, hw⟩) fun h => Or.inl ⟨h, hw⟩
      have hSR : SR.ncard = {w : R | ClauseEdge p I u.1 w.1}.ncard := by
        refine ncard_congr (fun (w : W) (hw : w ∈ SR) => (⟨w.1, w.2, hw.1⟩ : R))
          (fun _ hw => hw.2)
          (fun _ _ _ _ h => Subtype.ext (Subtype.mk.inj h))
          (fun w hw => ⟨⟨w.1, w.2.1⟩, ⟨w.2.2, hw⟩, Subtype.ext rfl⟩)
      have hSD : SD.ncard = (Dfin.filter fun w : W => ClauseEdge p I u.1 w.1).card := by
        rw [← ncard_coe_finset]; congr 1; ext w; simp [SD, Dfin]
      calc {w : W | ClauseEdge p I u.1 w.1}.ncard
          ≤ (SR ∪ SD).ncard := ncard_le_ncard hun (toFinite _)
        _ ≤ SR.ncard + SD.ncard := ncard_union_le SR SD
        _ = _ := by rw [hSR, hSD]
    have h23 : 2 ≤ (if ∃ v : R, ClauseEdge p I v.1 u.1 then 2 else 3) := by split_ifs <;> omega
    omega
  -- Sum over `Rfin ≃ R`:
  have hRfin (f : Wire n s → ℕ) : ∑ u ∈ Rfin, f u.1 = ∑ u : R, f u.1 :=
    Finset.sum_bij (fun u hu => (⟨u.1, u.2, (Finset.mem_filter.mp hu).2⟩ : R))
      (fun _ _ => Finset.mem_univ _)
      (fun _ _ _ _ h => Subtype.ext (Subtype.mk.inj h))
      (fun u _ => ⟨⟨u.1, u.2.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, u.2.2⟩,
        Subtype.ext rfl⟩)
      (fun _ _ => rfl)
  -- And `∑ u : R, (Dfin.filter (ClauseEdge u ·)).card ≤ ∑ w ∈ Dfin, inDeg w ≤ 2 * D₀.ncard`:
  have htarget_D : (∑ u : R, (Dfin.filter fun w : W => ClauseEdge p I u.1 w.1).card) ≤
      2 * D₀.ncard := by
    calc (∑ u : R, (Dfin.filter fun w : W => ClauseEdge p I u.1 w.1).card)
        ≤ ∑ u : W, (Dfin.filter fun w : W => ClauseEdge p I u.1 w.1).card := by
          rw [← hRfin fun u => (Dfin.filter fun w : W => ClauseEdge p I u w.1).card]
          exact Finset.sum_le_sum_of_subset (Finset.subset_univ Rfin)
      _ = ∑ w ∈ Dfin, (Finset.univ.filter fun u : W => ClauseEdge p I u.1 w.1).card := by
          simp_rw [Finset.card_filter]
          exact Finset.sum_comm
      _ ≤ ∑ _w ∈ Dfin, 2 := by
          refine Finset.sum_le_sum fun w _ => ?_
          have hnc : (Finset.univ.filter fun u : W => ClauseEdge p I u.1 w.1).card =
              {u : W | ClauseEdge p I u.1 w.1}.ncard := by
            rw [← ncard_coe_finset]; congr 1; ext u; simp
          rw [hnc]
          exact inDeg_clauseEdge_le_two hfan I W w
      _ = 2 * D₀.ncard := by rw [Finset.sum_const, smul_eq_mul, mul_comm, hDfin_card]
  have hcap_eq : (∑ u : R, min {w : R | ClauseEdge p I u.1 w.1}.ncard
      (if ∃ v : R, ClauseEdge p I v.1 u.1 then 2 else 3)) = clauseCappedEdges p I R := by
    rw [clauseCappedEdges, SimpleGraph.arborescenceCappedEdges, finsum_eq_sum_of_fintype]
    refine Finset.sum_congr rfl fun u _ => ?_
    by_cases h : ∃ v : R, ClauseEdge p I v.1 u.1 <;> simp [clauseDigraph, h]
  have hsum_R : (∑ u : R, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2) ≤
      clauseCappedEdges p I R + 2 * D₀.ncard := by
    calc (∑ u : R, min {w : W | ClauseEdge p I u.1 w.1}.ncard 2)
        ≤ ∑ u : R, (min {w : R | ClauseEdge p I u.1 w.1}.ncard
            (if ∃ v : R, ClauseEdge p I v.1 u.1 then 2 else 3) +
            (Dfin.filter fun w : W => ClauseEdge p I u.1 w.1).card) :=
          Finset.sum_le_sum fun u _ => hR_term u
      _ = clauseCappedEdges p I R +
            ∑ u : R, (Dfin.filter fun w : W => ClauseEdge p I u.1 w.1).card := by
          rw [Finset.sum_add_distrib, hcap_eq]
      _ ≤ clauseCappedEdges p I R + 2 * D₀.ncard := Nat.add_le_add_left htarget_D _
  rw [hsplit, hRfin fun u => min {w : W | ClauseEdge p I u w.1}.ncard 2]
  omega

/-- **`D₀`-free amortized `1 / 4`-per-clause frontier state bound.** Along any layout `π` of a
fan-in-at-most-2 Boolean circuit `c`, each wire in `D₀` touches at most `4` two-capped clauses (`2`
in + `2` out), so `53 / 200 ≥ 1 / 4` amortizes `D₀` completely:
`Real.logb 2 |States_t| ≤ |cutWires| - (1 / 4) * twoCappedClauseEdges`. -/
theorem logb_ncard_frontierValues_le_quarter_sub {c : Circuit σ n m} (hfan : c.FanInAtMost 2)
    (I : Interpretation σ Bool) (Acc : Fin m → Set Bool) (π : Layout (Compiler.Vertex c)) (t : ℕ)
    (X : Set (Fin n → Bool)) :
    Real.logb 2 (((fun x => (Compiler.network c I Acc).frontierValues π t
        (fun e => c.program.trace I x e.signal.1)) '' X).ncard : ℝ) ≤
      ((cutWires c (π.initial t)).ncard : ℝ) -
        (1 / 4 : ℝ) * (twoCappedClauseEdges c.program I (cutWires c (π.initial t)) : ℝ) := by
  set W := cutWires c (π.initial t)
  set D₀ := c.program.depthOneDetermined W
  have harb := logb_ncard_frontierValues_le_arborescence_depthOne hfan I Acc π t X
  have hamort : (twoCappedClauseEdges c.program I W : ℝ) ≤
      (clauseCappedEdges c.program I (W \ D₀) : ℝ) + 4 * (D₀.ncard : ℝ) := by
    exact_mod_cast twoCappedClauseEdges_le_add_four_mul hfan I W
  have hcap_nn : (0 : ℝ) ≤ (clauseCappedEdges c.program I (W \ D₀) : ℝ) := Nat.cast_nonneg _
  have hroot_nn : (0 : ℝ) ≤ ((clauseActiveRoots c.program I (W \ D₀)).ncard : ℝ) :=
    Nat.cast_nonneg _
  linarith

end OutForest

end Cslib.Circuits.Frontier
