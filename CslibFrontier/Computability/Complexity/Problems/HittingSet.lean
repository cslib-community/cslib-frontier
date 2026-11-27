/-
Copyright (c) 2026 Shriya Thakur, Hugo Akitaya, Freddy Stock,
Adriano Corbelino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hugo Akitaya, Shriya Thakur, Freddy Stock, Adriano Corbelino
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.SetCover
public import CslibFrontier.Computability.Complexity.Problems.VertexCover
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Tactic.EncLen

/-!
# Hitting Set

`HittingSet` is problem SP8 of [Garey and Johnson][GareyJohnson1979]. Its instances
(`Cslib.Complexity.HittingSetInstance`, encoded by `Cslib.Complexity.encHittingSet`) pair a set
system (`Cslib.Complexity.SetSystem`: a ground list and a list of subsets) with a number `k`. An
instance is in the problem when at most `k` distinct ground elements meet every listed subset.

Garey and Johnson ask, for a collection `C` of subsets of a finite set `S` and a positive integer
`K ≤ |S|`, for a set `S' ⊆ S` with `|S'| ≤ K` that contains an element of every member of `C`.
This formalization differs in three ways:

* `k` is any natural number. With `k = 0` only an empty collection is hit, and a `k` above the
  number of distinct ground elements behaves like that number.
* The listed subsets need not lie in the ground list. Only ground elements are chosen, so a subset
  without a ground element is never hit.
* Repeated ground entries count once.

For `1 ≤ k ≤ |S|` and subsets of the ground list, this is the problem of Garey and Johnson.

`NP` membership uses `subsetVerifier`: the certificate selects distinct ground elements, and
`HittingSet.verifier` checks their number and `HittingSet.isHitting`.

## The reduction from vertex cover

Garey and Johnson credit the transformation from VERTEX COVER to [Karp1972].
`VertexCover.toHittingSet` keeps the declared vertices as the ground list and `k`, and turns every
edge between two distinct declared vertices (`VertexCover.properEdges`) into the subset `[u, v]`.
A set of declared vertices meets every such subset exactly when it is a vertex cover. Every subset
has at most two elements, the case that Garey and Johnson note remains NP-complete. `VertexCover`
asks for exactly `k` vertices and rejects every `k` above the number `n` of distinct declared
vertices (`mem_VertexCover_iff_exists_card_le`), while `HittingSet` asks for at most `k`. For
`k > n` the reduction therefore produces a fixed instance with only the empty subset, which no set
meets.

## Main definitions

* `Cslib.Complexity.HittingSetInstance`, `Cslib.Complexity.encHittingSet`.
* `Cslib.Complexity.HittingSet`, with `Cslib.Complexity.mem_HittingSet_iff` reading hitting sets
  as finite sets of natural numbers.
* `Cslib.Complexity.HittingSet.isHitting`, with
  `Cslib.Complexity.HittingSet.isHitting_eq_true_iff`: the executable test that every subset
  meets the selected elements.
* `Cslib.Complexity.HittingSet.verifier`: the `NP` verifier.
* `Cslib.Complexity.VertexCover.toHittingSet`: the reduction from `VertexCover`.

## Main results

* `Cslib.Complexity.HittingSet.isVerifier`,
  `Cslib.Complexity.HittingSet.computableInPolyTime_verifier`,
  `Cslib.Complexity.HittingSet.mem_NP`: `HittingSet ∈ NP encHittingSet`.
* `Cslib.Complexity.VertexCover.toHittingSet_mem_iff`,
  `Cslib.Complexity.VertexCover.computableInPolyTime_toHittingSet`,
  `Cslib.Complexity.polyTimeReducible_VertexCover_HittingSet`: the reduction.
* `Cslib.Complexity.HittingSet_npHard`, `Cslib.Complexity.HittingSet_npComplete`:
  `HittingSet` is `NP`-complete.

## References

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979], Problem SP8.
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

/-- An instance `(system, k)` of **Hitting Set**. -/
@[ext]
structure HittingSetInstance where
  /-- The ground elements that may be chosen, and the subsets to hit. -/
  system : SetSystem
  /-- The largest number of ground elements allowed in a hitting set. -/
  k : ℕ
  deriving DecidableEq, Repr

/-- Framed `encSetSystem` followed by binary `encNat`, encoding `HittingSetInstance`. The ground
list and the subsets are framed lists of binary labels. -/
enc_structure encHittingSet : HittingSetInstance where
  system : encSetSystem,
  k : encNat

attribute [fun_prop] encHittingSet_system_polyTime encHittingSet_k_polyTime
  encHittingSet_mk_polyTime

/-- The instances with a hitting set of at most `k` ground elements [Garey and Johnson, Problem
SP8][GareyJohnson1979]: at most `k` distinct ground elements such that every listed subset contains
one of them. -/
def HittingSet : Set HittingSetInstance :=
  {x | ∃ H : Finset {u // u ∈ x.system.ground},
    H.card ≤ x.k ∧ ∀ S ∈ x.system.sets, ∃ u ∈ H, (u : ℕ) ∈ S}

/-- Membership in `HittingSet` as a finite set of at most `k` ground elements that meets every
listed subset. -/
theorem mem_HittingSet_iff (x : HittingSetInstance) :
    x ∈ HittingSet ↔ ∃ H : Finset ℕ, (∀ u ∈ H, u ∈ x.system.ground) ∧ H.card ≤ x.k ∧
      ∀ S ∈ x.system.sets, ∃ u ∈ H, u ∈ S := by
  unfold HittingSet
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨H, hcard, hhit⟩
    -- Forget the membership proofs of the elements of `H`.
    refine ⟨H.map (Function.Embedding.subtype _), ?_, ?_, ?_⟩
    · intro u hu
      obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hu
      exact v.property
    · rw [Finset.card_map]
      exact hcard
    · intro S hS
      obtain ⟨u, huH, huS⟩ := hhit S hS
      exact ⟨u, Finset.mem_map.mpr ⟨u, huH, rfl⟩, huS⟩
  · rintro ⟨H, hmem, hcard, hhit⟩
    -- Attach to every element of `H` its membership in the ground list.
    let H' : Finset {u // u ∈ x.system.ground} :=
      H.attach.map ⟨fun u => ⟨u.val, hmem u.val u.property⟩, by
        intro a b h
        exact Subtype.ext (congrArg (fun v : {u // u ∈ x.system.ground} => v.val) h)⟩
    refine ⟨H', ?_, ?_⟩
    · change (H.attach.map _).card ≤ x.k
      rw [Finset.card_map, Finset.card_attach]
      exact hcard
    · intro S hS
      obtain ⟨u, huH, huS⟩ := hhit S hS
      refine ⟨⟨u, hmem u huH⟩, ?_, huS⟩
      exact Finset.mem_map.mpr ⟨⟨u, huH⟩, Finset.mem_attach H ⟨u, huH⟩, rfl⟩

namespace HittingSet

/-- Whether every set in `sets` contains an element of `selected`. For example,
`isHitting [[1, 2], [2, 3], [3, 4]] [2, 3] = true`. -/
def isHitting (sets : List (List ℕ)) (selected : List ℕ) : Bool :=
  sets.all fun S => S.any fun u => selected.contains u

/-- `isHitting sets selected` holds exactly when every set in `sets` contains an element of
`selected`. -/
theorem isHitting_eq_true_iff (sets : List (List ℕ)) (selected : List ℕ) :
    isHitting sets selected = true ↔ ∀ S ∈ sets, ∃ u ∈ selected, u ∈ S := by
  simp only [isHitting, List.all_eq_true, List.any_eq_true, List.contains_iff_mem, and_comm]

/-- The hitting test is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_isHitting :
    ComputableInPolyTime (fun p : List (List ℕ) × List ℕ => isHitting p.1 p.2)
      (encPair encNatSetList (encList encNat)) encBool := by
  unfold isHitting
  fun_prop

/-! ### Membership in `NP` -/

/-- Verify a Hitting Set certificate: select distinct ground elements by the certificate mask,
then check that there are at most `k` of them and that they meet every listed subset. -/
def verifier : HittingSetInstance × List Bool → Bool :=
  subsetVerifier (fun x => x.system.ground) fun y =>
    decide (y.2.length ≤ y.1.k) && isHitting y.1.system.sets y.2

/-- `HittingSet.verifier` verifies `HittingSet` with certificates as long as the encoded
instance. -/
theorem isVerifier : IsVerifier encHittingSet Polynomial.X verifier HittingSet := by
  have hset : HittingSet = {x | ∃ H : Finset ℕ, (∀ u ∈ H, u ∈ x.system.ground) ∧
      H.card ≤ x.k ∧ ∀ S ∈ x.system.sets, ∃ u ∈ H, u ∈ S} :=
    Set.ext fun x => mem_HittingSet_iff x
  rw [hset]
  refine isVerifier_subsetVerifier
    (fun x => by
      have := length_le_length_encList encNat x.system.ground
      enc_len [Polynomial.eval_X, encHittingSet_apply, encHittingSetFields, encSetSystem_apply])
    fun x l hl _ => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, isHitting_eq_true_iff, List.mem_toFinset,
    List.toFinset_card_of_nodup hl]

/-- The `HittingSet` verifier is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_verifier :
    ComputableInPolyTime verifier (encPair encHittingSet encBits) encBool := by
  fun_prop [verifier]

/-- `HittingSet` belongs to `NP`: the certificate selects ground elements, and the verifier checks
their number and `isHitting`. -/
theorem mem_NP : HittingSet ∈ NP encHittingSet :=
  ⟨Polynomial.X, verifier, computableInPolyTime_verifier, isVerifier⟩

end HittingSet

/-! ### Reduction from vertex covers -/

namespace VertexCover

/-- **Karp's reduction from `VertexCover`**: keep the declared vertices as the ground list and the
target, and make every edge `(u, v)` between two distinct declared vertices the subset `[u, v]`, or
produce a fixed instance with only the empty subset, which no set meets, when the target exceeds
the number of distinct declared vertices. -/
def toHittingSet : VertexCoverInstance → HittingSetInstance := fun x =>
  if x.k ≤ x.graph.vertices.toFinset.card then
    ⟨⟨x.graph.vertices, (properEdges x.graph).map fun e => [e.1, e.2]⟩, x.k⟩
  else ⟨⟨[], [[]]⟩, 0⟩

/-- **Vertex covers of `G` are hitting sets of its edges.** -/
theorem toHittingSet_mem_iff (x : VertexCoverInstance) :
    toHittingSet x ∈ HittingSet ↔ x ∈ VertexCover := by
  obtain ⟨G, k⟩ := x
  rw [mem_VertexCover_iff_exists_card_le_mk]
  simp only [toHittingSet]
  split_ifs with hk
  · -- Both sides ask for the same set of at most `k` declared vertices: hitting the subset
    -- `[u, v]` of every proper edge is covering the graph.
    rw [mem_HittingSet_iff, and_iff_right hk]
    refine exists_congr fun H => and_congr_right fun _ => and_comm.trans (and_congr_left
      fun _ => ⟨fun h u hu v hv huv => ?_, fun h S hS => ?_⟩)
    · have hpair : ∀ a b, (a, b) ∈ properEdges G → a ∈ H ∨ b ∈ H := fun a b hab => by
        obtain ⟨w, hw, hwab⟩ := h [a, b] (List.mem_map.2 ⟨(a, b), hab, rfl⟩)
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hwab
        rcases hwab with rfl | rfl
        exacts [Or.inl hw, Or.inr hw]
      obtain ⟨hne, he | he⟩ := Graph.toSimpleGraph_adj.1 huv
      · exact hpair u v (mem_properEdges.2 ⟨he, hu, hv, hne⟩)
      · exact (hpair v u (mem_properEdges.2 ⟨he, hv, hu, Ne.symm hne⟩)).symm
    · obtain ⟨e, he, rfl⟩ := List.mem_map.1 hS
      obtain ⟨he, hu, hv, hne⟩ := mem_properEdges.1 he
      rcases h e.1 hu e.2 hv (Graph.toSimpleGraph_adj.2 ⟨hne, Or.inl he⟩) with h1 | h2
      · exact ⟨e.1, h1, List.mem_cons_self⟩
      · exact ⟨e.2, h2, List.mem_cons_of_mem _ List.mem_cons_self⟩
  · refine iff_of_false ?_ fun h => hk h.1
    rw [mem_HittingSet_iff]
    rintro ⟨H, -, -, hhit⟩
    obtain ⟨u, -, hu⟩ := hhit [] List.mem_cons_self
    exact List.not_mem_nil hu

/-- The reduction `toHittingSet` is polynomial-time: the binary target is compared with the number
of distinct declared vertices, computed in unary. -/
@[fun_prop]
theorem computableInPolyTime_toHittingSet :
    ComputableInPolyTime toHittingSet encVertexCoverInstance encHittingSet := by
  unfold toHittingSet
  -- `fun_prop` has no rule for `toFinset.card`, but has one for `distinctVertices.length`.
  simp_rw [← Graph.length_distinctVertices]
  fun_prop

end VertexCover

/-- `VertexCover` reduces to `HittingSet` in polynomial time via `VertexCover.toHittingSet`. -/
theorem polyTimeReducible_VertexCover_HittingSet :
    PolyTimeReducible encVertexCoverInstance encHittingSet VertexCover HittingSet :=
  ⟨VertexCover.toHittingSet, VertexCover.computableInPolyTime_toHittingSet,
    fun x => (VertexCover.toHittingSet_mem_iff x).symm⟩

/-- `HittingSet` is `NP`-hard. -/
theorem HittingSet_npHard : NPHard encHittingSet HittingSet :=
  VertexCover_npHard.trans polyTimeReducible_VertexCover_HittingSet

/-- **`HittingSet` is NP-complete** [Garey and Johnson, Problem SP8][GareyJohnson1979], with the
target in binary. -/
theorem HittingSet_npComplete : NPComplete encHittingSet HittingSet :=
  ⟨HittingSet.mem_NP, HittingSet_npHard⟩

end Cslib.Complexity
