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

* `k` is any natural number. An empty collection is hit for every `k`, by the empty set, and with
  `k = 0` nothing else is. A `k` above the number of distinct ground elements behaves like that
  number.
* The listed subsets need not lie in the ground list. Only ground elements are chosen, so a subset
  without a ground element, such as the empty subset, is never hit.
* Repeated ground entries count once, and repeated subsets add no constraint.

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

* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979], Problem SP8,
  p. 222.
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
  constructor
  · rintro ⟨H, hcard, hhit⟩
    refine ⟨H.map (.subtype _), fun u hu => ?_, (Finset.card_map _).trans_le hcard,
      fun S hS => ?_⟩
    · obtain ⟨v, -, rfl⟩ := Finset.mem_map.1 hu
      exact v.property
    · obtain ⟨u, huH, huS⟩ := hhit S hS
      exact ⟨u, Finset.mem_map_of_mem _ huH, huS⟩
  · rintro ⟨H, hmem, hcard, hhit⟩
    have hmap : (H.subtype (· ∈ x.system.ground)).map (.subtype _) = H :=
      (Finset.subtype_map _).trans (Finset.filter_eq_self.mpr hmem)
    refine ⟨H.subtype (· ∈ x.system.ground),
      by rw [← Finset.card_map (.subtype _), hmap]; exact hcard, fun S hS => ?_⟩
    obtain ⟨u, huH, huS⟩ := hhit S hS
    exact ⟨⟨u, hmem u huH⟩, Finset.mem_subtype.2 huH, huS⟩

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
    refine exists_congr fun H => and_congr_right fun _ => and_comm.trans
      (and_congr_left fun _ => ?_)
    rw [← covers_properEdges_iff]
    change (∀ S ∈ (properEdges G).map (fun e => [e.1, e.2]), ∃ u ∈ H, u ∈ S) ↔ _
    simp only [List.forall_mem_map, List.mem_cons, List.not_mem_nil, or_false, and_or_left,
      exists_or, exists_eq_right]
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

/-- **`HittingSet` is NP-complete** [Garey and Johnson, Problem SP8, p. 222][GareyJohnson1979],
with the target in binary. -/
theorem HittingSet_npComplete : NPComplete encHittingSet HittingSet :=
  ⟨HittingSet.mem_NP, HittingSet_npHard⟩

end Cslib.Complexity
