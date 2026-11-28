/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Arborescences
public import CslibFrontier.Foundations.Combinatorics.Multidigraph.BEST
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Factorial
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Foundations.Data.List.OfFn

/-!
# Polynomial-time Eulerian-circuit counting via the BEST theorem

Polynomial-time evaluation of the exact number of Eulerian circuits starting with a given arc in a
finite multidigraph (`Cslib.Complexity.Graph`), combining the BEST theorem (`Multidigraph.BEST`),
Tutte's directed matrix-tree theorem (`Arborescences`), and
`Cslib.Circuits.Rational.detRows_polytime`.

Isolated declared vertices (`outdeg = 0`) do not affect `Multidigraph.IsEulerianCircuit`, so the
algorithm filters to `Graph.activeVertices` before applying the reduced-Laplacian formula.

## Main definitions

* `Cslib.Complexity.Graph.outdeg`, `Cslib.Complexity.Graph.indeg`: outgoing and incoming arc counts
  in `G.validArcs`.
* `Cslib.Complexity.Graph.isBalancedBool`: Boolean check that `outdeg v = indeg v` for every
  declared vertex.
* `Cslib.Complexity.Graph.activeVertices`: duplicate-free list of declared vertices with positive
  out-degree.
* `Cslib.Complexity.Graph.eulerianCircuitCount`: exact count of Eulerian circuits starting at arc
  index `eIdx` via the BEST determinant formula (`0` if `eIdx` is out of range or `G` is not
  balanced).

## Main results

* `Cslib.Complexity.Graph.eulerianCircuitCount_eq_natCard`: exact equality with
  `Nat.card {l // Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l}`.
* `Cslib.Complexity.Graph.computableInPolyTime_eulerianCircuitCount`,
  `Cslib.Complexity.Graph.computableInPolyTime_natCard_isEulerianCircuit`: polynomial-time
  computability on `encPair encGraph encNat`.
-/

public section

namespace Cslib.Complexity.Graph

open Turing MultiTapeTM

/-- Out-degree of `v` in the valid-arc multidigraph `G.validArcs`. -/
@[expose]
def outdeg (G : Graph) (v : ℕ) : ℕ :=
  G.validArcs.countP fun e => decide (e.1 = v)

/-- In-degree of `v` in the valid-arc multidigraph `G.validArcs`. -/
@[expose]
def indeg (G : Graph) (v : ℕ) : ℕ :=
  G.validArcs.countP fun e => decide (e.2 = v)

/-- Boolean check that every declared vertex of `G` has equal out-degree and in-degree in
`G.validArcs`. -/
@[expose]
def isBalancedBool (G : Graph) : Bool :=
  G.distinctVertices.all fun v => decide (G.outdeg v = G.indeg v)

/-- Duplicate-free list of declared vertices of `G` with at least one outgoing arc in
`G.validArcs`. -/
@[expose]
def activeVertices (G : Graph) : List ℕ :=
  G.distinctVertices.filter fun v => decide (G.outdeg v ≠ 0)

/-- Number of Eulerian circuits of `(G.arcSrc, G.arcTgt)` starting with arc `eIdx` (`0` if
`eIdx ≥ G.validArcs.length` or `G` is not balanced), computed via the BEST theorem. -/
@[expose]
def eulerianCircuitCount (G : Graph) (eIdx : ℕ) : ℕ :=
  if decide (eIdx < G.validArcs.length) && G.isBalancedBool then
    let r := (G.validArcs.getD eIdx (0, 0)).1
    multiLaplacianCount G.activeVertices G.validArcs r *
      (G.activeVertices.map fun v => ((G.outdeg v - 1).factorial : ℤ)).prod.toNat
  else 0

private theorem activeVertices_nodup (G : Graph) : G.activeVertices.Nodup :=
  G.nodup_distinctVertices.filter _

private theorem card_fin_filter_subtype_eq {xs : List ℕ} {ys : List (ℕ × ℕ)} (p : ℕ × ℕ → ℕ)
    (hp : ∀ e ∈ ys, p e ∈ xs) (v : {x // x ∈ xs}) :
    (Finset.univ.filter fun i : Fin ys.length =>
      (⟨p ys[i], hp _ (List.getElem_mem i.isLt)⟩ : {x // x ∈ xs}) = v).card =
      ys.countP fun e => decide (p e = v.1) := by
  rw [List.countP_eq_card_filter_getElem]
  exact congrArg Finset.card (Finset.ext fun _ => by simp [Subtype.ext_iff])

private theorem mem_activeVertices_of_validArc (G : Graph) (hbal : G.isBalancedBool = true)
    {e : ℕ × ℕ} (he : e ∈ G.validArcs) :
    e.1 ∈ G.activeVertices ∧ e.2 ∈ G.activeVertices := by
  have hv := (mem_validArcs.1 he).2
  have h1 : 0 < G.outdeg e.1 := List.countP_pos_iff.2 ⟨e, he, decide_eq_true rfl⟩
  have h2 : 0 < G.indeg e.2 := List.countP_pos_iff.2 ⟨e, he, decide_eq_true rfl⟩
  simp only [isBalancedBool, List.all_eq_true, decide_eq_true_eq] at hbal
  have h2_eq := hbal e.2 (Graph.mem_distinctVertices.2 hv.2)
  exact ⟨List.mem_filter.2 ⟨Graph.mem_distinctVertices.2 hv.1, decide_eq_true (by omega)⟩,
    List.mem_filter.2 ⟨Graph.mem_distinctVertices.2 hv.2, decide_eq_true (by omega)⟩⟩

/-- **Polynomial-time BEST theorem evaluation**: `G.eulerianCircuitCount eIdx` equals the number
of Eulerian circuits of `(G.arcSrc, G.arcTgt)` starting at arc `eIdx` (and `0` when `eIdx` is out
of range). -/
theorem eulerianCircuitCount_eq_natCard (G : Graph) (eIdx : ℕ) :
    G.eulerianCircuitCount eIdx =
      if he : eIdx < G.validArcs.length then
        Nat.card {l : List (Fin G.validArcs.length) //
          Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l}
      else 0 := by
  classical
  by_cases he : eIdx < G.validArcs.length
  · rw [dite_eq_left he]
    by_cases hbalB : G.isBalancedBool = true
    · simp only [eulerianCircuitCount, he, hbalB, decide_true, Bool.true_and, ↓reduceIte]
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem he, Option.getD_some]
      have harcs : ∀ e ∈ G.validArcs, e.1 ∈ G.activeVertices ∧ e.2 ∈ G.activeVertices :=
        fun _ => G.mem_activeVertices_of_validArc hbalB
      let srcAct : Fin G.validArcs.length → {v // v ∈ G.activeVertices} := fun i =>
        ⟨G.validArcs[i].1, (harcs _ (List.getElem_mem i.isLt)).1⟩
      let tgtAct : Fin G.validArcs.length → {v // v ∈ G.activeVertices} := fun i =>
        ⟨G.validArcs[i].2, (harcs _ (List.getElem_mem i.isLt)).2⟩
      have hcirc_iff (l) : Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l ↔
          Multidigraph.IsEulerianCircuit srcAct tgtAct ⟨eIdx, he⟩ l := by
        constructor <;> rintro ⟨hnd, hmem, hh, hch, hgl⟩ <;>
          exact ⟨hnd, hmem, hh,
            hch.imp fun _ _ hab => by
              simpa only [Subtype.ext_iff, arcSrc, arcTgt, srcAct, tgtAct] using hab,
            fun a ha => by
              simpa only [Subtype.ext_iff, arcSrc, arcTgt, srcAct, tgtAct] using hgl a ha⟩
      have hbal_act (v : {v // v ∈ G.activeVertices}) :
          (Finset.univ.filter fun e => srcAct e = v).card =
            (Finset.univ.filter fun e => tgtAct e = v).card := by
        rw [card_fin_filter_subtype_eq Prod.fst (fun e h => (harcs e h).1) v,
          card_fin_filter_subtype_eq Prod.snd (fun e h => (harcs e h).2) v]
        simp only [isBalancedBool, List.all_eq_true, decide_eq_true_eq] at hbalB
        exact hbalB v.1 (List.mem_filter.1 v.2).1
      have hpos_act (v : {v // v ∈ G.activeVertices}) : ∃ e, srcAct e = v := by
        have hpos : 0 < G.outdeg v.1 :=
          Nat.pos_of_ne_zero (of_decide_eq_true (List.mem_filter.1 v.2).2)
        obtain ⟨e, he_mem, he_fst⟩ := List.countP_pos_iff.1 hpos
        obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.1 he_mem
        exact ⟨⟨i, hi⟩, Subtype.ext (by simpa [srcAct, hget] using of_decide_eq_true he_fst)⟩
      let eAct := G.activeVertices_nodup.getEquiv G.activeVertices
      have hprod :
          (G.activeVertices.map fun v => ((G.outdeg v - 1).factorial : ℤ)).prod =
            ((∏ v : {v // v ∈ G.activeVertices},
              ((Finset.univ.filter fun e => srcAct e = v).card - 1).factorial : ℕ) : ℤ) := by
        rw [← Fin.prod_univ_fun_getElem, Nat.cast_prod, ← Equiv.prod_comp eAct]
        refine Finset.prod_congr rfl fun i _ => ?_
        rw [card_fin_filter_subtype_eq Prod.fst (fun e h => (harcs e h).1) (eAct i)]
        rfl
      rw [Nat.card_congr (Equiv.subtypeEquivRight hcirc_iff),
        Multidigraph.natCard_isEulerianCircuit srcAct tgtAct hbal_act hpos_act ⟨eIdx, he⟩,
        multiLaplacianCount_eq_natCard G.activeVertices_nodup (fun _ => .rfl) G.validArcs harcs
          (harcs _ (List.getElem_mem he)).1, hprod, Int.toNat_natCast]
      rfl
    · simp only [eulerianCircuitCount, hbalB, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
      have : IsEmpty {l // Multidigraph.IsEulerianCircuit G.arcSrc G.arcTgt ⟨eIdx, he⟩ l} :=
        ⟨fun ⟨l, hl⟩ => hbalB <| List.all_eq_true.2 fun v hv => decide_eq_true <| by
          let vSub : {x // x ∈ G.1} := ⟨v, Graph.mem_distinctVertices.1 hv⟩
          rw [outdeg, indeg, show v = vSub.1 from rfl,
            ← card_fin_filter_subtype_eq Prod.fst (fun _ h => (mem_validArcs.1 h).2.1) vSub,
            ← card_fin_filter_subtype_eq Prod.snd (fun _ h => (mem_validArcs.1 h).2.2) vSub]
          exact hl.card_filter_src_eq vSub⟩
      exact Nat.card_of_isEmpty.symm
  · simp [eulerianCircuitCount, he]

/-! ### Polynomial-time computability -/

@[fun_prop]
theorem computableInPolyTime_outdeg {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → Graph} {v : γ → ℕ}
    (hg : ComputableInPolyTime g encIn encGraph)
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => (g x).outdeg (v x)) encIn encUnary := by
  fun_prop [outdeg]

@[fun_prop]
theorem computableInPolyTime_indeg {γ : Type} {encIn : γ ↪ List Bool}
    {g : γ → Graph} {v : γ → ℕ}
    (hg : ComputableInPolyTime g encIn encGraph)
    (hv : ComputableInPolyTime v encIn encNat) :
    ComputableInPolyTime (fun x => (g x).indeg (v x)) encIn encUnary := by
  fun_prop [indeg]

@[fun_prop]
theorem computableInPolyTime_isBalancedBool :
    ComputableInPolyTime isBalancedBool encGraph encBool := by
  fun_prop [isBalancedBool]

@[fun_prop]
theorem computableInPolyTime_activeVertices :
    ComputableInPolyTime activeVertices encGraph (encList encNat) := by
  fun_prop [activeVertices]

/-- `Graph.eulerianCircuitCount` is computable in polynomial time on `encPair encGraph encNat`. -/
@[fun_prop]
theorem computableInPolyTime_eulerianCircuitCount :
    ComputableInPolyTime (fun p : Graph × ℕ => p.1.eulerianCircuitCount p.2)
      (encPair encGraph encNat) encNat := by
  dsimp only [eulerianCircuitCount]
  have hlt : ComputableInPolyTime (fun p : Graph × ℕ => decide (p.2 < p.1.validArcs.length))
      (encPair encGraph encNat) encBool :=
    ComputableInPolyTime.binary_lt' (by fun_prop)
      (ComputableInPolyTime.unary_to_binary.comp (by fun_prop))
  have hr : ComputableInPolyTime (fun p : Graph × ℕ => (p.1.validArcs.getD p.2 (0, 0)).1)
      (encPair encGraph encNat) encNat :=
    (ComputableInPolyTime.fst encNat encNat).comp
      (ComputableInPolyTime.listGetD_binary (encA := encPair encNat encNat) (0, 0)
        (by fun_prop) (by fun_prop))
  fun_prop

/-- The number of Eulerian circuits starting with arc `eIdx` in the multidigraph
`(G.arcSrc, G.arcTgt)` is computable in polynomial time on `encPair encGraph encNat`. -/
theorem computableInPolyTime_natCard_isEulerianCircuit :
    ComputableInPolyTime
      (fun p : Graph × ℕ =>
        if he : p.2 < p.1.validArcs.length then
          Nat.card {l : List (Fin p.1.validArcs.length) //
            Multidigraph.IsEulerianCircuit p.1.arcSrc p.1.arcTgt ⟨p.2, he⟩ l}
        else 0)
      (encPair encGraph encNat) encNat := by
  refine computableInPolyTime_eulerianCircuitCount.of_enc_eq fun p => ?_
  rw [eulerianCircuitCount_eq_natCard]

end Cslib.Complexity.Graph
