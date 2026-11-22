/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.Basic
public import CslibFrontier.Computability.Complexity.Problems.NCL.Simulation

/-!
# Simulations between constraint graphs

Every transformation of a constraint graph in [HearnDemaine2005] (replacing crossings by
crossover gadgets, vertices by subgraphs, renumbering the result) must preserve and reflect the
three decision questions of [HearnDemaine2005, Section 2.1]. A simulation of a constraint graph
`G` by `G'` (`Cslib.Complexity.NCL.ConstraintGraph.Simulation`) is a simulation of the moves of
`G` by the moves of `G'` (`Cslib.Complexity.NCL.Simulation`) whose abstraction and encoding also
map configurations to configurations. The latter is needed because a configuration without moves
is still a configuration.

Then:

* an orientation is a configuration exactly when its encoding is one
  (`Cslib.Complexity.NCL.ConstraintGraph.Simulation.legal_enc_iff`);
* configuration-to-configuration reachability between encodings is reachability in `G`
  (`Cslib.Complexity.NCL.Simulation.reachable_enc_iff`, inherited);
* an edge of `G` can be reversed from a configuration exactly when an edge of `G'` that tracks
  it can be reversed from the encoding
  (`Cslib.Complexity.NCL.ConstraintGraph.Simulation.canReverse_enc_iff`).

## Main definitions

* `Cslib.Complexity.NCL.ConstraintGraph.Simulation`: a simulation of one constraint graph by
  another.
* `Cslib.Complexity.NCL.ConstraintGraph.Simulation.refl`,
  `Cslib.Complexity.NCL.ConstraintGraph.Simulation.trans`,
  `Cslib.Complexity.NCL.ConstraintGraph.Simulation.ofLegalEquiv`,
  `Cslib.Complexity.NCL.ConstraintGraph.Simulation.ofEquiv`: identity, composition, graphs whose
  configurations correspond, and renaming of vertices and edges.

## Main results

* `Cslib.Complexity.NCL.ConstraintGraph.Simulation.legal_enc_iff`: configurations.
* `Cslib.Complexity.NCL.ConstraintGraph.Simulation.canReverse_enc_iff`: configuration-to-edge
  reachability.
* `Cslib.Complexity.NCL.ConstraintGraph.Simulation.exists_legal_reachable_iff`: edge-to-edge
  reachability.

## References

* [R. A. Hearn and E. D. Demaine, *PSPACE-completeness of sliding-block puzzles and other
  problems through the nondeterministic constraint logic model of computation*][HearnDemaine2005]
-/

public section

namespace Cslib.Complexity.NCL.ConstraintGraph

variable {V V' V'' E E' E'' : Type*} [DecidableEq E] [DecidableEq E'] [DecidableEq E'']

/-- A simulation of the constraint graph `G` by `G'`: a simulation of the moves of `G` by the
moves of `G'` whose abstraction and encoding map configurations to configurations. -/
structure Simulation (G : ConstraintGraph V E) (G' : ConstraintGraph V' E') extends
    NCL.Simulation G.Step G'.Step where
  /-- A configuration of `G'` stands for a configuration of `G`. -/
  legal_abs {s' : E' → Bool} : G'.Legal s' → G.Legal (abs s')
  /-- A configuration of `G` is encoded by a configuration of `G'`. -/
  legal_enc {s : E → Bool} : G.Legal s → G'.Legal (enc s)

namespace Simulation

variable {G : ConstraintGraph V E} {G' : ConstraintGraph V' E'} {G'' : ConstraintGraph V'' E''}

/-- An orientation is a configuration of `G` exactly when its encoding is one of `G'`. -/
theorem legal_enc_iff (S : Simulation G G') {s : E → Bool} : G'.Legal (S.enc s) ↔ G.Legal s :=
  ⟨fun h => S.abs_enc s ▸ S.legal_abs h, S.legal_enc⟩

/-- An edge that tracks an abstract edge under abstraction also tracks it under encoding. -/
private theorem enc_apply_of_abs_apply (S : Simulation G G') {e : E} {e' : E'}
    (habs : ∀ s', S.abs s' e = s' e') (s : E → Bool) : S.enc s e' = s e :=
  (habs (S.enc s)).symm.trans (congrFun (S.abs_enc s) e)

/-- **Configuration-to-edge reachability is preserved and reflected**, for an edge `e'` of `G'`
that tracks the edge `e` of `G`. -/
theorem canReverse_enc_iff (S : Simulation G G') {e : E} {e' : E'}
    (habs : ∀ s', S.abs s' e = s' e') {s : E → Bool} :
    G'.CanReverse (S.enc s) e' ↔ G.CanReverse s e := by
  unfold CanReverse
  rw [S.enc_apply_of_abs_apply habs]
  exact S.exists_reachable_enc_iff (P := fun t => t e ≠ s e) (P' := fun t' => t' e' ≠ s e)
    (fun t' => by rw [habs]) s

/-- **Edge-to-edge reachability is preserved and reflected**, for edges `eA'`, `eB'` of `G'` that
track the edges `eA`, `eB` of `G`. -/
theorem exists_legal_reachable_iff (S : Simulation G G') {eA eB : E} {eA' eB' : E'}
    (habsA : ∀ s', S.abs s' eA = s' eA') (habsB : ∀ s', S.abs s' eB = s' eB')
    (dA dB : Bool) :
    (∃ s' t', G'.Legal s' ∧ s' eA' = dA ∧ t' eB' = dB ∧ G'.Reachable s' t') ↔
      ∃ s t, G.Legal s ∧ s eA = dA ∧ t eB = dB ∧ G.Reachable s t := by
  constructor
  · rintro ⟨s', t', hs, hA, hB, hr⟩
    exact ⟨S.abs s', S.abs t', S.legal_abs hs, (habsA s').trans hA, (habsB t').trans hB,
      S.reachable_abs hr⟩
  · rintro ⟨s, t, hs, hA, hB, hr⟩
    exact ⟨S.enc s, S.enc t, S.legal_enc hs, (S.enc_apply_of_abs_apply habsA s).trans hA,
      (S.enc_apply_of_abs_apply habsB t).trans hB,
      S.reachable_enc hr⟩

/-- The identity simulation. -/
@[expose] def refl (G : ConstraintGraph V E) : Simulation G G where
  toSimulation := .refl G.Step
  legal_abs h := h
  legal_enc h := h

/-- The composition of simulations: `G'` simulates `G`, and `G''` simulates `G'`. -/
@[expose] def trans (S : Simulation G G') (T : Simulation G' G'') : Simulation G G'' where
  toSimulation := S.toSimulation.trans T.toSimulation
  legal_abs h := S.legal_abs (T.legal_abs h)
  legal_enc h := T.legal_enc (S.legal_enc h)

/-- **Graphs with corresponding configurations simulate each other.** If, along a renaming `σ`
of the edges, the configurations of `G'` are exactly those of `G`, then so are the moves, since a
move reverses one edge between two configurations. The vertices and their ports need not
correspond: a vertex may list its ports in another order, or be split differently. -/
@[expose] def ofLegalEquiv (G : ConstraintGraph V E) (G' : ConstraintGraph V' E') (σ : E ≃ E')
    (h : ∀ s, G'.Legal (s ∘ σ.symm) ↔ G.Legal s) : Simulation G G' :=
  have h' : ∀ s', G'.Legal s' ↔ G.Legal (s' ∘ σ) := fun s' => by
    simpa only [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id] using h (s' ∘ σ)
  { abs := fun s' => s' ∘ σ
    enc := fun s => s ∘ σ.symm
    abs_enc := fun s => by simp [Function.comp_assoc]
    step_abs := by
      rintro s' t' ⟨hs, ht, e, rfl⟩
      exact .single ⟨(h' _).1 hs, (h' _).1 ht, σ.symm e, reverse_comp_equiv σ s' e⟩
    step_enc := by
      rintro s t ⟨hs, ht, e, rfl⟩
      exact .single ⟨(h s).2 hs, (h _).2 ht, σ e, by simpa using reverse_comp_equiv σ.symm s e⟩
    legal_abs := fun hs => (h' _).1 hs
    legal_enc := fun hs => (h _).2 hs }

/-- Renaming the edges along `σ` and reindexing the vertices along `τ` is a simulation. -/
@[expose] def ofEquiv (G : ConstraintGraph V E) (σ : E ≃ E') (τ : V' ≃ V) :
    Simulation G (ConstraintGraph.map (G ∘ τ) σ) :=
  ofLegalEquiv G _ σ fun s => by
    rw [legal_map, legal_comp G τ.surjective]
    simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]

@[simp] theorem ofEquiv_abs (G : ConstraintGraph V E) (σ : E ≃ E') (τ : V' ≃ V)
    (s' : E' → Bool) : (ofEquiv G σ τ).abs s' = s' ∘ σ :=
  rfl

@[simp] theorem ofEquiv_enc (G : ConstraintGraph V E) (σ : E ≃ E') (τ : V' ≃ V)
    (s : E → Bool) : (ofEquiv G σ τ).enc s = s ∘ σ.symm :=
  rfl

end Simulation

end Cslib.Complexity.NCL.ConstraintGraph
