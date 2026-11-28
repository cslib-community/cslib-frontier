/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Computability.Circuit.Basic
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Open
import CslibFrontier.Computability.Circuit.Frontier.Compiler
import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Constraint
import Mathlib.Algebra.BigOperators.Pi

/-!
# A Boolean circuit as an open bit tensor network

The constraint graph of a circuit checks its unique trace. Place each input wire at the vertex
reading it. For an unread input, supply a vertex with constant table one. The resulting network
has a fixed graph for every input, and its contraction is the indicator of the circuit's output
over any commutative semiring.

* `Compiler.exists_trivalent_openBitNetwork` bounds the network volume for a circuit with
  fan-in at most two. Trivalency counts both internal and exterior wires.
-/

namespace Cslib.Circuits.Frontier.Compiler

open Set

variable {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (I : Interpretation σ Bool)
  (R : Type*) [CommSemiring R]

private noncomputable abbrev inputSite (i : Fin n) : Vertex c ⊕ Fin n :=
  (site c i).elim (.inr i) Sum.inl

private theorem inputSite_inl {i : Fin n} {v : Vertex c} :
    inputSite c i = .inl v ↔ site c i = some v := by
  cases h : site c i <;> simp [inputSite, h]

open Classical in
private noncomputable def openNetwork : OpenBitNetwork R (Fin n) (Vertex c ⊕ Fin n) (Edge c) where
  src e := .inl (src e)
  tgt e := .inl (tgt e)
  site := inputSite c
  tensor v α x := match v with
    | .inl v => ((network c I fun _ => {true}).toTensorNetwork R x).tensor v α
    | .inr _ => 1
  tensor_congr v α β h := by
    funext x
    cases v with
    | inl v =>
      exact TensorNetwork.tensor_congr _ _ _ _ fun e he => h e (he.imp (congrArg _) (congrArg _))
    | inr i => rfl
  exterior_congr v α x y h := by
    cases v with
    | inr i => rfl
    | inl v =>
      let N := network c I fun _ => {true}
      change (if N.Constraint v x α then (1 : R) else 0) = (if N.Constraint v y α then 1 else 0)
      have hxy : ∀ i, N.site i = some v → x i = y i := fun i hi => h i ((inputSite_inl c).2 hi)
      exact if_congr ⟨N.constraint_congr v x y α α hxy (fun _ _ => rfl),
        N.constraint_congr v y x α α (fun i hi => (hxy i hi).symm) (fun _ _ => rfl)⟩ rfl rfl

private theorem openNetwork_trivalent (hfan : c.FanInAtMost 2) : (openNetwork c I R).Trivalent := by
  classical
  intro v
  let N := openNetwork c I R
  have hd : Disjoint {e | N.src e = v} {e | N.tgt e = v} :=
    Set.disjoint_left.2 fun e hs ht => loopless (c := c) e (Sum.inl.inj (hs.trans ht.symm))
  rw [← Set.ncard_union_eq hd (Set.toFinite _) (Set.toFinite _)]
  change (N.incidenceSet v).ncard + {i | inputSite c i = v}.ncard ≤ 3
  cases v with
  | inr i =>
    have he : N.incidenceSet (.inr i) = ∅ := by
      ext e
      simp [Multigraph.mem_incidenceSet, N, openNetwork]
    have hi : {j | inputSite c j = .inr i} ⊆ {i} := by
      intro j hj
      change inputSite c j = .inr i at hj
      cases h : site c j with
      | none => simpa [inputSite, h] using hj
      | some v => simp [inputSite, h] at hj
    rw [he, Set.ncard_empty, zero_add]
    exact (Set.ncard_le_ncard hi).trans (by simp)
  | inl v =>
    let G := network c I fun _ => {true}
    have he : N.incidenceSet (.inl v) = (graph c).incidenceSet v := by
      ext e
      simp [Multigraph.mem_incidenceSet, N, openNetwork]
    have hi : {i | inputSite c i = .inl v} = G.readAt v := Set.ext fun _ => inputSite_inl c
    rw [he, hi]
    rcases (G.readAt v).eq_empty_or_nonempty with he | ⟨i, hi⟩
    · rw [he, Set.ncard_empty, add_zero]
      exact maxDegreeLE (by decide) hfan v
    · have ha := ncard_incidenceSet_site_le_one (c := c) (i := i) (v := v) hi
      have hb : (G.readAt v).ncard ≤ 1 := ncard_readAt_le I (fun _ => {true}) v
      lia

private noncomputable local instance : Fintype (Vertex c) := Fintype.ofFinite _
private noncomputable local instance : Fintype (Edge c) := Fintype.ofFinite _
private noncomputable local instance : DecidableEq (Edge c) := Classical.decEq _

private theorem openNetwork_contraction (x : Fin n → Bool) :
    (openNetwork c I R).contraction x = if c.eval I x 0 then 1 else 0 := by
  classical
  let N := network c I fun _ => {true}
  calc _ = (N.toTensorNetwork R x).contraction := by
         simp [TensorNetwork.contraction, openNetwork, Fintype.prod_sum_type, N]
       _ = _ := by
         rw [Network.contraction_toTensorNetwork]
         have h : {α | N.Satisfies x α} =
             if c.eval I x 0 then {fun e => c.program.trace I x e.signal.val} else ∅ := by
           ext α
           cases hb : c.eval I x 0 <;>
             simp [N, satisfies_iff, Subsingleton.elim (α := Fin 1) _ 0, hb]
         rw [h]
         cases c.eval I x 0 <;> simp

/-- A circuit with `n` input bits, one output and fan-in at most two computes the contraction
of a trivalent open bit network over any commutative semiring. Its volume counts all exterior
bits, internal edges and vertices. Circuit size counts operation gates. -/
public theorem exists_trivalent_openBitNetwork (hfan : c.FanInAtMost 2) :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (N : OpenBitNetwork R (Fin n) V E), N.Trivalent ∧ N.volume ≤ 2 * n + 8 * c.size + 5 ∧
        ∀ x, N.contraction x = if c.eval I x 0 then 1 else 0 := by
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, openNetwork c I R,
    openNetwork_trivalent c I R hfan, ?_, openNetwork_contraction c I R⟩
  rw [OpenBitNetwork.volume, Nat.card_sum, Nat.card_fin]
  have hv := card_vertex_le hfan
  have he := card_edge_le hfan
  have hg := c.innerSize_le_size
  lia

end Cslib.Circuits.Frontier.Compiler
