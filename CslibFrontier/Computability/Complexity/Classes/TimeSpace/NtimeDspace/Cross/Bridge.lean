/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.EdgeNetBasic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD

/-!
# From Complexitylib's described networks to edge networks

A rows-first bipartite described network `d` (`DescribedNetwork.IsRowsFirstBipartite d r`) is an
edge network (`EdgeNet`) on its vertices `Fin d.vertices.length`:

* `EdgeNet.ofDescribed d r hd eval`: the edges are `Fin d.numEdges`, the end `u i` of edge `i` is
  the row vertex (index `< r`) that has `i` as a port and `w i` is the column vertex that has it;
  the ports of a vertex are its ports in `d`, in order, and its table is `eval` at its descriptor.
* `EdgeNet.nodup_ports_ofDescribed`: no edge is a port of a vertex twice.
* `EdgeNet.length_ports_ofDescribed`: a vertex has as many ports as in `d`.
* `EdgeNet.value_ofDescribed`: the value of the edge network is the contraction of `d`.
* `EdgeNet.ofExplicit`, `EdgeNet.value_ofExplicit`, `EdgeNet.value_ofExplicit_zmod`: for an explicit
  network over `ℕ` with its tables read into a commutative ring (such as `ZMod p`), the value is
  the cast of `ExplicitTensorNetwork.contraction`, the contraction used by the block networks.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Finset Cslib.Circuits.Frontier

namespace Bridge

/-- A list sum over a prefix is the sum over the indices below the cut. -/
theorem sum_map_take {α : Type*} (L : List α) (f : α → ℕ) (r : ℕ) :
    ((L.take r).map f).sum = ∑ j : Fin L.length with j.1 < r, f L[j.1] := by
  conv_lhs => rw [← List.ofFn_getElem (xs := L)]
  rw [List.map_take, List.map_ofFn, List.sum_take_ofFn]
  rfl

/-- A list sum over a suffix is the sum over the indices at or above the cut. -/
theorem sum_map_drop {α : Type*} (L : List α) (f : α → ℕ) (r : ℕ) :
    ((L.drop r).map f).sum = ∑ j : Fin L.length with ¬ j.1 < r, f L[j.1] := by
  have h := List.sum_take_add_sum_drop (L.map f) r
  rw [← List.map_take, ← List.map_drop, sum_map_take] at h
  have htot : (L.map f).sum = ∑ j : Fin L.length, f L[j.1] := (Fin.sum_univ_fun_getElem L f).symm
  have hsplit := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j : Fin L.length => j.1 < r)
    (fun j => f L[j.1])
  omega

/-- If a sum of naturals over `s` is `1`, some term is positive, every term is at most `1`, and at
most one term is positive. -/
theorem of_sum_eq_one {ι : Type*} [DecidableEq ι] {s : Finset ι} {c : ι → ℕ}
    (h : ∑ j ∈ s, c j = 1) :
    (∃ j ∈ s, 0 < c j) ∧ (∀ j ∈ s, c j ≤ 1) ∧
      ∀ j ∈ s, ∀ j' ∈ s, 0 < c j → 0 < c j' → j = j' := by
  refine ⟨?_, fun j hj => h ▸ Finset.single_le_sum (fun _ _ => Nat.zero_le _) hj, ?_⟩
  · obtain ⟨j, hj, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero (h ▸ one_ne_zero)
    exact ⟨j, hj, Nat.pos_of_ne_zero hne⟩
  · intro j hj j' hj' hc hc'
    by_contra hne
    have hsub : ({j, j'} : Finset ι) ⊆ s := by
      intro a ha
      rcases Finset.mem_insert.1 ha with rfl | ha
      · exact hj
      · rw [Finset.mem_singleton.1 ha]; exact hj'
    have := Finset.sum_le_sum_of_subset (f := c) hsub
    rw [Finset.sum_pair hne] at this
    omega

theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) {i : ℕ} (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

/-- On ports that name edges, the bits of `List.ofFn x` are the values of `x`. -/
theorem map_pmap_mk {n : ℕ} (x : Fin n → Bool) :
    ∀ (l : List ℕ) (H : ∀ i ∈ l, i < n),
      (l.pmap Fin.mk H).map x = DescribedNetwork.wordBits (List.ofFn x) l
  | [], _ => rfl
  | i :: l, H => by
    rw [List.pmap_cons, List.map_cons, map_pmap_mk x l, DescribedNetwork.wordBits,
      DescribedNetwork.wordBits, List.map_cons, getD_ofFn x (H i List.mem_cons_self)]

end Bridge

namespace EdgeNet

open Bridge

section Described

variable {T : Type*} (d : DescribedNetwork T) (r : ℕ) (hd : d.IsRowsFirstBipartite r)
include hd

/-- Every port names an edge. -/
theorem port_lt {v : Fin d.vertices.length} {i : ℕ} (hi : i ∈ (d.vertices[v.1]).1) :
    i < d.numEdges :=
  hd.1 _ (List.getElem_mem _) i hi

/-- The row-side and column-side counts of an edge. -/
theorem sums_count {i : ℕ} (hi : i < d.numEdges) :
    ∑ j : Fin d.vertices.length with j.1 < r, (d.vertices[j.1]).1.count i = 1 ∧
      ∑ j : Fin d.vertices.length with ¬ j.1 < r, (d.vertices[j.1]).1.count i = 1 := by
  obtain ⟨h1, h2⟩ := hd.2 i hi
  rw [sum_map_take] at h1
  rw [sum_map_drop] at h2
  exact ⟨h1, h2⟩

/-- Every edge is a port of a row. -/
theorem exists_row (i : Fin d.numEdges) :
    ∃ j : Fin d.vertices.length, j.1 < r ∧ i.1 ∈ (d.vertices[j.1]).1 := by
  obtain ⟨j, hj, hc⟩ := (of_sum_eq_one (sums_count d r hd i.2).1).1
  exact ⟨j, (Finset.mem_filter.1 hj).2, List.count_pos_iff.1 hc⟩

/-- Every edge is a port of a column. -/
theorem exists_col (i : Fin d.numEdges) :
    ∃ j : Fin d.vertices.length, ¬ j.1 < r ∧ i.1 ∈ (d.vertices[j.1]).1 := by
  obtain ⟨j, hj, hc⟩ := (of_sum_eq_one (sums_count d r hd i.2).2).1
  exact ⟨j, (Finset.mem_filter.1 hj).2, List.count_pos_iff.1 hc⟩

/-- An edge is a port of at most one row. -/
theorem row_unique {i : ℕ} (hi : i < d.numEdges) {j j' : Fin d.vertices.length} (hj : j.1 < r)
    (hj' : j'.1 < r) (h : i ∈ (d.vertices[j.1]).1) (h' : i ∈ (d.vertices[j'.1]).1) : j = j' :=
  (of_sum_eq_one (sums_count d r hd hi).1).2.2 j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩) j'
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'⟩)
    (List.count_pos_iff.2 h) (List.count_pos_iff.2 h')

/-- An edge is a port of at most one column. -/
theorem col_unique {i : ℕ} (hi : i < d.numEdges) {j j' : Fin d.vertices.length} (hj : ¬ j.1 < r)
    (hj' : ¬ j'.1 < r) (h : i ∈ (d.vertices[j.1]).1) (h' : i ∈ (d.vertices[j'.1]).1) : j = j' :=
  (of_sum_eq_one (sums_count d r hd hi).2).2.2 j (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj⟩) j'
      (Finset.mem_filter.2 ⟨Finset.mem_univ _, hj'⟩)
    (List.count_pos_iff.2 h) (List.count_pos_iff.2 h')

/-- No edge is a port of a vertex twice. -/
theorem nodup_described (v : Fin d.vertices.length) : (d.vertices[v.1]).1.Nodup := by
  refine List.nodup_iff_count_le_one.2 fun i => ?_
  by_cases hi : i ∈ (d.vertices[v.1]).1
  · have hlt := port_lt d r hd hi
    by_cases hv : v.1 < r
    · exact (of_sum_eq_one (sums_count d r hd hlt).1).2.1 v
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩)
    · exact (of_sum_eq_one (sums_count d r hd hlt).2).2.1 v
        (Finset.mem_filter.2 ⟨Finset.mem_univ _, hv⟩)
  · rw [List.count_eq_zero_of_not_mem hi]; exact Nat.zero_le _

/-- The row end of an edge. -/
noncomputable def rowOf (i : Fin d.numEdges) : Fin d.vertices.length :=
  Classical.choose (exists_row d r hd i)

/-- The column end of an edge. -/
noncomputable def colOf (i : Fin d.numEdges) : Fin d.vertices.length :=
  Classical.choose (exists_col d r hd i)

theorem rowOf_spec (i : Fin d.numEdges) :
    (rowOf d r hd i).1 < r ∧ i.1 ∈ (d.vertices[(rowOf d r hd i).1]).1 :=
  Classical.choose_spec (exists_row d r hd i)

theorem colOf_spec (i : Fin d.numEdges) :
    ¬ (colOf d r hd i).1 < r ∧ i.1 ∈ (d.vertices[(colOf d r hd i).1]).1 :=
  Classical.choose_spec (exists_col d r hd i)

/-- The ports of a vertex, as edges. -/
def portsOf (v : Fin d.vertices.length) : List (Fin d.numEdges) :=
  (d.vertices[v.1]).1.pmap Fin.mk fun _ hi => port_lt d r hd hi

theorem mem_portsOf (v : Fin d.vertices.length) (i : Fin d.numEdges) :
    i ∈ portsOf d r hd v ↔ i.1 ∈ (d.vertices[v.1]).1 := by
  rw [portsOf, List.mem_pmap]
  constructor
  · rintro ⟨a, ha, rfl⟩; exact ha
  · intro h; exact ⟨i.1, h, rfl⟩

/-- A rows-first bipartite described network as an edge network. -/
noncomputable def ofDescribed {R : Type} (eval : T → List Bool → R) :
    EdgeNet R (Fin d.vertices.length) where
  M := d.numEdges
  u := rowOf d r hd
  w := colOf d r hd
  huw i h := (colOf_spec d r hd i).1 (h ▸ (rowOf_spec d r hd i).1)
  ports := portsOf d r hd
  hports v i := by
    rw [mem_portsOf]
    constructor
    · intro h
      by_cases hv : v.1 < r
      · exact Or.inl (row_unique d r hd i.2 (rowOf_spec d r hd i).1 hv (rowOf_spec d r hd i).2 h)
      · exact Or.inr (col_unique d r hd i.2 (colOf_spec d r hd i).1 hv (colOf_spec d r hd i).2 h)
    · rintro (rfl | rfl)
      · exact (rowOf_spec d r hd i).2
      · exact (colOf_spec d r hd i).2
  eval v := eval (d.vertices[v.1]).2

variable {R : Type} (eval : T → List Bool → R)

@[simp] theorem M_ofDescribed : (ofDescribed d r hd eval).M = d.numEdges := rfl

theorem ports_ofDescribed (v : Fin d.vertices.length) :
    (ofDescribed d r hd eval).ports v = portsOf d r hd v := rfl

theorem eval_ofDescribed (v : Fin d.vertices.length) (bs : List Bool) :
    (ofDescribed d r hd eval).eval v bs = eval (d.vertices[v.1]).2 bs := rfl

/-- The ends of an edge are a row and a column that have it as a port. -/
theorem u_ofDescribed (i : Fin d.numEdges) :
    ((ofDescribed d r hd eval).u i).1 < r ∧
      i.1 ∈ (d.vertices[((ofDescribed d r hd eval).u i).1]).1 :=
  rowOf_spec d r hd i

theorem w_ofDescribed (i : Fin d.numEdges) :
    ¬ ((ofDescribed d r hd eval).w i).1 < r ∧
      i.1 ∈ (d.vertices[((ofDescribed d r hd eval).w i).1]).1 :=
  colOf_spec d r hd i

/-- No edge is a port of a vertex twice. -/
theorem nodup_ports_ofDescribed (v : Fin d.vertices.length) :
    ((ofDescribed d r hd eval).ports v).Nodup :=
  (nodup_described d r hd v).pmap fun _ _ _ _ h => Fin.mk.inj h

/-- The degree: a vertex has as many ports as in the described network. -/
theorem length_ports_ofDescribed (v : Fin d.vertices.length) :
    ((ofDescribed d r hd eval).ports v).length = (d.vertices[v.1]).1.length :=
  List.length_pmap

/-- The bits on the ports of a vertex are those that `DescribedNetwork.wordBits` reads. -/
theorem map_ports_ofDescribed (v : Fin d.vertices.length) (x : Fin d.numEdges → Bool) :
    ((ofDescribed d r hd eval).ports v).map x =
      DescribedNetwork.wordBits (List.ofFn x) (d.vertices[v.1]).1 :=
  map_pmap_mk x _ _

/-- The value is the contraction. -/
theorem value_ofDescribed [CommRing R] :
    (ofDescribed d r hd eval).value = d.contraction eval := by
  unfold EdgeNet.value DescribedNetwork.contraction
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← Fin.prod_univ_fun_getElem]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact congrArg _ (map_ports_ofDescribed d r hd eval v x)

end Described

/-! ### Explicit networks over `ℕ` -/

/-- An explicit network over `ℕ`, rows-first bipartite, as an edge network with its table entries
read into `S`. -/
noncomputable def ofExplicit (S : Type) [CommRing S] (d : ExplicitTensorNetwork ℕ) (r : ℕ)
    (hd : d.IsRowsFirstBipartite r) : EdgeNet S (Fin d.vertices.length) :=
  ofDescribed d r hd fun t bs => ((ExplicitTensorNetwork.entry t bs : ℕ) : S)

/-- The value is the cast of the contraction. -/
theorem value_ofExplicit (S : Type) [CommRing S] (d : ExplicitTensorNetwork ℕ) (r : ℕ)
    (hd : d.IsRowsFirstBipartite r) :
    (ofExplicit S d r hd).value = ((d.contraction : ℕ) : S) := by
  rw [ofExplicit, value_ofDescribed, ← DescribedNetwork.contraction_entry]
  exact (DescribedNetwork.map_contraction (Nat.castRingHom S) _ _).symm

/-- Modulo `p`: the value of the edge network over `ZMod p` is the contraction mod `p`. -/
theorem value_ofExplicit_zmod (p : ℕ) (d : ExplicitTensorNetwork ℕ) (r : ℕ)
    (hd : d.IsRowsFirstBipartite r) :
    (ofExplicit (ZMod p) d r hd).value = ((d.contraction : ℕ) : ZMod p) :=
  value_ofExplicit (ZMod p) d r hd

end EdgeNet

/-! ### Axiom audit -/

end Cslib.Complexity.NtimeDspace.Cross
