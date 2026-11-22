/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.EdgeNetBasic
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Clique

/-!
# The first clique (Lemma 4.3)

From a network `G` with `M` edges and maximum degree `Δ`, and `K ≥ 1`, build a clique `firstClique`
on `q = 2K` nodes: the nodes `i < K` are the *vertex groups*, the nodes `K + τ` the *test groups*.

* A vertex `v` goes into vertex group `min (K-1) (pre v / D₀)`, where `pre v` counts the ports of
the
  vertices before `v` and `D₀ = max 1 ⌈2M/K⌉`. Ports are counted by `deg`, the number of edges at a
  vertex, so that the counts add up to `2M` even if a port list repeats an edge.
* Every edge is subdivided by an equality test. The tests of the edges between two vertex groups
  `{i, j}` (including `i = j`), listed by edge name, go cyclically to the test groups: the edge in
  position `ν` of that list goes to test group `ν mod K`.
* The pair (vertex group `i`, test group `τ`) carries the half-edges between them, listed by edge
  name and, for an edge inside group `i`, by end; its width `b` is their number, and its budget is
  `b(b+1)/2`. Every other pair has budget `0`.
* A string `θ ∈ {0,1}^b` is encoded by the label `enc θ` with one request of type `p` for every
  position `p < b`, in the first multiset if `θ p` is set and in the second otherwise; its weight
  is `b(b+1)/2`.
* A vertex-group table is `0` unless each of its labels encodes a string of the width of its pair,
  and otherwise it is the product of the functions of its vertices at the bits read from those
  strings. A test-group table is likewise `0` unless its labels encode strings, and otherwise the
  product of the equality tests of its subdividing vertices.

## Main results

* `enc`, `enc_wt`, `enc_isEnc`, `decEnc_enc`, `enc_decEnc`: the encoding of strings.
* `firstClique_value` (Lemma 4.3 (b)): the clique has value `Z(G)`. The assignments of `G` are in
  bijection (`encLab`, `decLab`) with the labelings at which no table vanishes.
* `sum_deg_group_le`, `card_tgroup_le`, `width_mul_le`, `width_bound`: a vertex group has at most
  `D₀ + Δ` ports, the cyclic distribution sends at most `m / K + 1` of `m` edges to a test group,
  and so `K² b ≤ 2 (M + K(Δ + 1) + K³)` for every width `b`.
* `firstClique_potential` (Lemma 4.3 (a)): `Φ ≤ 64 (M + K(Δ + 1) + K³)²` (the proof gives `16`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset NtimeDspace.Cross

/-! ### Encoding strings by labels -/

/-- The label encoding a string of `b` bits. -/
def enc (b : ℕ) (θ : ℕ → Bool) : Label :=
  (((List.range b).filter fun p => θ p).map id, ((List.range b).filter fun p => !θ p).map id)

/-- A label encodes a string of `b` bits: every type below `b` occurs once in its two multisets
together, and no other type occurs. -/
def IsEnc (b : ℕ) (l : Label) : Prop := l.1 + l.2 = ↑(List.range b)

instance (b : ℕ) (l : Label) : Decidable (IsEnc b l) := by unfold IsEnc; infer_instance

/-- The bit `p` of the string encoded by a label. -/
def decEnc (l : Label) (p : ℕ) : Bool := decide (p ∈ l.1)

theorem enc_isEnc (b : ℕ) (θ : ℕ → Bool) : IsEnc b (enc b θ) := by
  unfold IsEnc enc
  simp only [List.map_id, Multiset.coe_add]
  exact Multiset.coe_eq_coe.mpr (List.filter_append_perm _ _)

private theorem sum_range_succ_mul_two (b : ℕ) : (∑ i ∈ range b, (i + 1)) * 2 = b * (b + 1) := by
  induction b with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, add_mul, ih]; ring

theorem wt_range (b : ℕ) : wt (↑(List.range b) : Multiset ℕ) = b * (b + 1) / 2 := by
  have h : wt (↑(List.range b) : Multiset ℕ) = ∑ i ∈ range b, (i + 1) := by
    rw [Finset.sum_eq_multiset_sum, Finset.range_val, ← Multiset.coe_range]; rfl
  rw [h]
  exact (Nat.div_eq_of_eq_mul_left (by norm_num) (sum_range_succ_mul_two b).symm).symm

theorem enc_wt (b : ℕ) (θ : ℕ → Bool) : labelWt (enc b θ) = b * (b + 1) / 2 := by
  rw [labelWt, ← wt_add, enc_isEnc b θ, wt_range]

theorem decEnc_enc (b : ℕ) (θ : ℕ → Bool) {p : ℕ} (hp : p < b) : decEnc (enc b θ) p = θ p := by
  simp [decEnc, enc, hp]

theorem enc_decEnc {b : ℕ} {l : Label} (h : IsEnc b l) : enc b (decEnc l) = l := by
  unfold IsEnc at h
  have hnd : (l.1 + l.2).Nodup := by rw [h]; exact Multiset.coe_nodup.mpr (List.nodup_range)
  obtain ⟨hnd1, hnd2, hdis⟩ := Multiset.nodup_add.mp hnd
  have hmem : ∀ p, p ∈ l.1 ∨ p ∈ l.2 ↔ p < b := fun p => by
    rw [← Multiset.mem_add, h, Multiset.mem_coe, List.mem_range]
  refine Prod.ext ?_ ?_
  · refine (Multiset.Nodup.ext ?_ hnd1).mpr fun p => ?_
    · simp only [enc, List.map_id]; exact Multiset.coe_nodup.mpr ((List.nodup_range).filter _)
    · simp only [enc, decEnc, List.map_id, Multiset.mem_coe, List.mem_filter, List.mem_range,
        decide_eq_true_eq]
      constructor
      · exact fun h => h.2
      · exact fun h' => ⟨(hmem p).mp (Or.inl h'), h'⟩
  · refine (Multiset.Nodup.ext ?_ hnd2).mpr fun p => ?_
    · simp only [enc, List.map_id]; exact Multiset.coe_nodup.mpr ((List.nodup_range).filter _)
    · simp only [enc, decEnc, List.map_id, Multiset.mem_coe, List.mem_filter, List.mem_range,
        Bool.not_eq_true', decide_eq_false_iff_not]
      constructor
      · rintro ⟨hp, hn⟩; exact ((hmem p).mpr hp).resolve_left hn
      · exact fun h' => ⟨(hmem p).mp (Or.inr h'), fun h1 => Multiset.disjoint_left.mp hdis h1 h'⟩

/-- `enc` only reads the first `b` bits. -/
theorem enc_congr {b : ℕ} {θ θ' : ℕ → Bool} (h : ∀ p < b, θ p = θ' p) : enc b θ = enc b θ' := by
  have h1 : (List.range b).filter (fun p => θ p) = (List.range b).filter (fun p => θ' p) :=
    List.filter_congr fun p hp => h p (List.mem_range.mp hp)
  have h2 : (List.range b).filter (fun p => !θ p) = (List.range b).filter (fun p => !θ' p) :=
    List.filter_congr fun p hp => by rw [h p (List.mem_range.mp hp)]
  simp only [enc, h1, h2]

/-! ### The groups -/

variable {V : ℕ} (G : EdgeNet ℤ (Fin V)) (K : ℕ)

/-- The number of edges at a vertex: its number of ports, counted without repetition (the length
of its port list when that list has no repeated edge). -/
def deg (v : Fin V) : ℕ := ((univ : Finset (Fin G.M)).filter fun e => G.u e = v ∨ G.w e = v).card

/-- The number of ports of the vertices before `v` (each edge at a vertex counted once). -/
def pre (v : Fin V) : ℕ := ∑ u : Fin V, if u < v then deg G u else 0

/-- `D₀ = max 1 ⌈2M/K⌉`. -/
def blockD (G : EdgeNet ℤ (Fin V)) (K : ℕ) : ℕ := max 1 ((2 * G.M + K - 1) / K)

/-- The vertex group of a vertex. -/
def vgroup (v : Fin V) : ℕ := min (K - 1) (pre G v / blockD G K)

/-- The position of edge `e` among the edges between the groups of its ends, by edge name. -/
def edgePos (e : Fin G.M) : ℕ :=
  ((univ : Finset (Fin G.M)).filter fun e' => e' < e ∧
    ({vgroup G K (G.u e'), vgroup G K (G.w e')} : Finset ℕ) =
      {vgroup G K (G.u e), vgroup G K (G.w e)}).card

/-- The test group of the subdividing vertex of edge `e`. -/
def tgroup (e : Fin G.M) : ℕ := edgePos G K e % K

/-- The half-edges between vertex group `i` and test group `τ`, in order: edges by name and, for an
edge inside group `i`, its `u` end before its `w` end. A half-edge is an edge and an end
(`false` = the `u` end, `true` = the `w` end). -/
def halfEdges (i τ : ℕ) : List (Fin G.M × Bool) :=
  ((List.finRange G.M).filter fun e => tgroup G K e = τ).flatMap fun e =>
    (if vgroup G K (G.u e) = i then [(e, false)] else []) ++
      (if vgroup G K (G.w e) = i then [(e, true)] else [])

/-- The width of the pair (vertex group `i`, test group `τ`). -/
def width (i τ : ℕ) : ℕ := (halfEdges G K i τ).length

/-- The node of vertex group `i`, of test group `τ`. -/
def vNode (i : ℕ) : ℕ := i
/-- The node of test group `τ`. -/
def tNode (τ : ℕ) : ℕ := K + τ

/-- The budgets of the first clique: `b(b+1)/2` on (vertex group, test group) pairs, `0`
elsewhere (`u < v` canonical). -/
def firstBudget (u v : Fin (2 * K)) : ℕ :=
  if u.val < K ∧ K ≤ v.val then width G K u.val (v.val - K) * (width G K u.val (v.val - K) + 1) / 2
  else 0

/-- The label of `Θ` at a node given by its number (the empty label out of range). -/
def labelOfNode (Θ : Fin (2 * K) → Label) (n : ℕ) : Label := if h : n < 2 * K then Θ
    ⟨n, h⟩ else (0, 0)

/-- The bit carried by half-edge `he` in the string encoded by the label `l` of the pair
(vertex group `i`, test group `τ`). -/
def heBit (l : Label) (i τ : ℕ) (he : Fin G.M × Bool) : Bool :=
  match (halfEdges G K i τ).idxOf? he with
  | some p => decEnc l p
  | none => false

/-- The table of vertex group `i`. -/
def vTable (i : ℕ) (Θ : Fin (2 * K) → Label) : ℤ :=
  if ∀ τ < K, IsEnc (width G K i τ) (labelOfNode K Θ (K + τ)) then
    ∏ v : Fin V, if vgroup G K v = i then
      G.eval v ((G.ports v).map fun e =>
        heBit G K (labelOfNode K Θ (K + tgroup G K e)) i (tgroup G K e) (e, decide (G.w e = v)))
    else 1
  else 0

/-- The table of test group `τ`: the equality tests of its subdividing vertices. The labels are
read in their canonical orientation (vertex group first), as the vertex groups read them. -/
def tTable (τ : ℕ) (Θ : Fin (2 * K) → Label) : ℤ :=
  if ∀ i < K, IsEnc (width G K i τ) (labelOfNode K Θ i) then
    ∏ e : Fin G.M, if tgroup G K e = τ then
      (if heBit G K (labelOfNode K Θ (vgroup G K (G.u e))) (vgroup G K (G.u e)) τ (e, false) =
          heBit G K (labelOfNode K Θ (vgroup G K (G.w e))) (vgroup G K (G.w e)) τ (e, true)
        then 1 else 0) else 1
  else 0

/-- **The first clique.** -/
def firstClique : Clique where
  q := 2 * K
  a := firstBudget G K
  T := fun w Θ => if w.val < K then vTable G K w.val Θ else tTable G K (w.val - K) Θ

/-! ### The value (Lemma 4.3 (b)) -/

section Value

variable {G K}

theorem vgroup_lt (hK : 1 ≤ K) (v : Fin V) : vgroup G K v < K := by
  unfold vgroup; omega

theorem tgroup_lt (hK : 1 ≤ K) (e : Fin G.M) : tgroup G K e < K := Nat.mod_lt _ (by omega)

theorem mem_halfEdges {i τ : ℕ} {e : Fin G.M} {b : Bool} :
    (e, b) ∈ halfEdges G K i τ ↔
      tgroup G K e = τ ∧ vgroup G K (if b then G.w e else G.u e) = i := by
  simp only [halfEdges, List.mem_flatMap, List.mem_filter, List.mem_finRange, true_and,
    decide_eq_true_eq, List.mem_append]
  constructor
  · rintro ⟨e', he', h⟩
    rcases h with h | h <;> split_ifs at h with hc <;>
      simp only [List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at h <;>
      obtain ⟨rfl, rfl⟩ := h <;> simp_all
  · rintro ⟨h1, h2⟩
    refine ⟨e, h1, ?_⟩
    cases b <;> simp_all

theorem nodup_halfEdges (i τ : ℕ) : (halfEdges G K i τ).Nodup := by
  unfold halfEdges
  rw [List.nodup_flatMap]
  refine ⟨fun e _ => ?_, ?_⟩
  · split_ifs <;> simp
  · refine ((List.nodup_finRange _).filter _).imp fun {a b} hab => ?_
    intro x hxa hxb
    have key : ∀ c : Fin G.M, x ∈ ((if vgroup G K (G.u c) = i then [(c, false)] else []) ++
        (if vgroup G K (G.w c) = i then [(c, true)] else [])) → x.1 = c := by
      intro c hc
      rw [List.mem_append] at hc
      rcases hc with hc | hc <;> split_ifs at hc <;> simp at hc <;> simp [hc]
    exact hab ((key a hxa).symm.trans (key b hxb))

theorem heBit_getElem (l : Label) (i τ n : ℕ) (hn : n < (halfEdges G K i τ).length) :
    heBit G K l i τ (halfEdges G K i τ)[n] = decEnc l n := by
  have h : (halfEdges G K i τ).idxOf? (halfEdges G K i τ)[n] = some n :=
    List.idxOf?_eq_some_iff.mpr ⟨hn, rfl, fun j hj h => by
      have := (nodup_halfEdges i τ).getElem_inj_iff.mp h; omega⟩
  unfold heBit
  rw [h]

variable (G K) in
/-- The string of the pair (vertex group `i`, test group `τ`) under an assignment `x` of `G`. -/
def strOf (x : Fin G.M → Bool) (i τ : ℕ) (n : ℕ) : Bool :=
  ((halfEdges G K i τ).map fun he => x he.1).getD n false

theorem heBit_enc (x : Fin G.M → Bool) {i τ : ℕ} {he : Fin G.M × Bool}
    (h : he ∈ halfEdges G K i τ) :
    heBit G K (enc (width G K i τ) (strOf G K x i τ)) i τ he = x he.1 := by
  obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.mp h
  rw [heBit_getElem _ _ _ _ hn, decEnc_enc (width G K i τ) _ (hn : n < width G K i τ)]
  simp [strOf, hn]

variable (K) in
/-- The label on the pair (vertex group `i`, test group `τ`). -/
def pairLabel (θ : Pairs (2 * K) → Label) (i τ : ℕ) : Label :=
  if h : i < K ∧ τ < K then
    θ ⟨(⟨i, by omega⟩, ⟨K + τ, by omega⟩), Fin.mk_lt_mk.mpr (by omega)⟩ else (0, 0)

theorem pairLabel_eq (θ : Pairs (2 * K) → Label) (p : Pairs (2 * K)) (h1 : p.1.1.val < K)
    (h2 : K ≤ p.1.2.val) : pairLabel K θ p.1.1.val (p.1.2.val - K) = θ p := by
  have : p.1.2.val < 2 * K := p.1.2.isLt
  unfold pairLabel
  rw [dite_eq_left ⟨h1, by omega⟩]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext; simp only; omega

theorem labelOfNode_vert (θ : Pairs (2 * K) → Label) (w : Fin (2 * K)) (hw : w.val < K) {τ : ℕ}
    (hτ : τ < K) : labelOfNode K (Clique.labelAt θ w) (K + τ) = pairLabel K θ w.val τ := by
  have hA : K + τ < 2 * K := by omega
  have hB : ¬ ((⟨K + τ, hA⟩ : Fin (2 * K)) < w) := fun h => by
    have : K + τ < w.val := h
    omega
  have hC : w < (⟨K + τ, hA⟩ : Fin (2 * K)) := show w.val < K + τ by omega
  unfold labelOfNode pairLabel Clique.labelAt
  rw [dite_eq_left hA, dite_eq_right hB, dite_eq_left hC, dite_eq_left
      (⟨hw, hτ⟩ : w.val < K ∧ τ < K)]

theorem labelOfNode_test (θ : Pairs (2 * K) → Label) (w : Fin (2 * K)) (hw : K ≤ w.val) {i : ℕ}
    (hi : i < K) : labelOfNode K (Clique.labelAt θ w) i = pairLabel K θ i (w.val - K) := by
  have : w.val < 2 * K := w.isLt
  have hA : i < 2 * K := by omega
  have hC : (⟨i, hA⟩ : Fin (2 * K)) < w := show i < w.val by omega
  unfold labelOfNode pairLabel Clique.labelAt
  rw [dite_eq_left hA, dite_eq_left hC, dite_eq_left (⟨hi, by omega⟩ : i < K ∧ w.val - K < K)]
  congr 1
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · apply Fin.ext; simp only; omega

variable (G K) in
/-- The labeling of the first clique of an assignment of `G`. -/
def encLab (x : Fin G.M → Bool) : Pairs (2 * K) → Label := fun p =>
  if p.1.1.val < K ∧ K ≤ p.1.2.val then
    enc (width G K p.1.1.val (p.1.2.val - K)) (strOf G K x p.1.1.val (p.1.2.val - K))
  else (0, 0)

theorem pairLabel_encLab (x : Fin G.M → Bool) {i τ : ℕ} (hi : i < K) (hτ : τ < K) :
    pairLabel K (encLab G K x) i τ = enc (width G K i τ) (strOf G K x i τ) := by
  unfold pairLabel encLab
  rw [dite_eq_left ⟨hi, hτ⟩]
  simp [hi]

variable (G K) in
/-- The assignment of `G` read from a labeling of the first clique: the bit of an edge is read at
its `u` end. -/
def decLab (θ : Pairs (2 * K) → Label) (e : Fin G.M) : Bool :=
  heBit G K (pairLabel K θ (vgroup G K (G.u e)) (tgroup G K e)) (vgroup G K (G.u e)) (tgroup G K e)
    (e, false)

theorem decLab_encLab (hK : 1 ≤ K) (x : Fin G.M → Bool) : decLab G K (encLab G K x) = x := by
  funext e
  unfold decLab
  rw [pairLabel_encLab x (vgroup_lt hK _) (tgroup_lt hK _),
    heBit_enc x (mem_halfEdges.mpr ⟨rfl, by simp⟩)]

theorem eq_zero_of_labelWt {l : Label} (h : labelWt l = 0) : l = (0, 0) := by
  unfold labelWt at h
  have h1 := card_le_wt l.1
  have h2 := card_le_wt l.2
  exact Prod.ext (Multiset.card_eq_zero.mp (by omega)) (Multiset.card_eq_zero.mp (by omega))

theorem encLab_mem (x : Fin G.M → Bool) : encLab G K x ∈ (firstClique G K).labelings := by
  change encLab G K x ∈ Fintype.piFinset fun p : Pairs (2 * K) =>
    labelsEq (firstBudget G K p.1.1 p.1.2)
  rw [Fintype.mem_piFinset]
  intro p
  rw [mem_labelsEq]
  unfold encLab firstBudget
  split_ifs
  · exact enc_wt _ _
  · rfl

theorem prod_encLab (hK : 1 ≤ K) (x : Fin G.M → Bool) :
    ∏ w, (firstClique G K).T w (Clique.labelAt (encLab G K x) w) =
      ∏ v, G.eval v ((G.ports v).map x) := by
  change ∏ w : Fin (2 * K), (if w.val < K then vTable G K w.val (Clique.labelAt (encLab G K x) w)
    else tTable G K (w.val - K) (Clique.labelAt (encLab G K x) w)) = _
  have hT : ∀ w : Fin (2 * K), (if w.val < K then vTable G K w.val (Clique.labelAt (encLab G K x) w)
      else tTable G K (w.val - K) (Clique.labelAt (encLab G K x) w)) =
      if w.val < K then ∏ v : Fin V, (if vgroup G K v = w.val then G.eval v ((G.ports v).map x)
        else 1) else 1 := by
    intro w
    by_cases hw : w.val < K
    · rw [ite_eq_left hw, ite_eq_left hw]
      unfold vTable
      rw [ite_eq_left (fun τ hτ => by
        rw [labelOfNode_vert _ w hw hτ, pairLabel_encLab x hw hτ]; exact enc_isEnc _ _)]
      refine Finset.prod_congr rfl fun v _ => ?_
      split_ifs with hv
      · congr 1
        refine List.map_congr_left fun e he => ?_
        rw [labelOfNode_vert _ w hw (tgroup_lt hK e), pairLabel_encLab x hw (tgroup_lt hK e)]
        refine heBit_enc x (mem_halfEdges.mpr ⟨rfl, ?_⟩)
        rcases (G.hports v e).mp he with h | h
        · have : G.w e ≠ v := h ▸ (G.huw e).symm
          simp [this, h, hv]
        · simp [h, hv]
      · rfl
    · rw [ite_eq_right hw, ite_eq_right hw]
      have hw' : K ≤ w.val := by omega
      unfold tTable
      rw [ite_eq_left (fun i hi => by
        rw [labelOfNode_test _ w hw' hi, pairLabel_encLab x hi (by have := w.isLt; omega)]
        exact enc_isEnc _ _)]
      refine Finset.prod_eq_one fun e _ => ?_
      split_ifs with he hne
      · rfl
      · exfalso; apply hne
        rw [labelOfNode_test _ w hw' (vgroup_lt hK _), labelOfNode_test _ w hw' (vgroup_lt hK _),
          pairLabel_encLab x (vgroup_lt hK _) (by have := w.isLt; omega),
          pairLabel_encLab x (vgroup_lt hK _) (by have := w.isLt; omega),
          heBit_enc x (mem_halfEdges.mpr ⟨he, by simp⟩),
          heBit_enc x (mem_halfEdges.mpr ⟨he, by simp⟩)]
      · rfl
  rw [Finset.prod_congr rfl fun w _ => hT w]
  have : ∀ w : Fin (2 * K), (if w.val < K then ∏ v : Fin V, (if vgroup G K v = w.val then
      G.eval v ((G.ports v).map x) else 1) else 1) =
      ∏ v : Fin V, (if w = ⟨vgroup G K v, by have := vgroup_lt (G := G) hK v; omega⟩ then
        G.eval v ((G.ports v).map x) else 1) := by
    intro w
    split_ifs with hw
    · refine Finset.prod_congr rfl fun v _ => ?_
      exact if_congr (by rw [Fin.ext_iff, eq_comm]) rfl rfl
    · refine (Finset.prod_eq_one fun v _ => ?_).symm
      rw [ite_eq_right]
      intro h; rw [h] at hw; exact hw (vgroup_lt hK v)
  rw [Finset.prod_congr rfl fun w _ => this w, Finset.prod_comm]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [Finset.prod_ite_eq' Finset.univ]
  simp

theorem eq_encLab_of_ne_zero (hK : 1 ≤ K) {θ : Pairs (2 * K) → Label}
    (hθ : θ ∈ (firstClique G K).labelings)
    (hne : ∏ w, (firstClique G K).T w (Clique.labelAt θ w) ≠ 0) :
    θ = encLab G K (decLab G K θ) := by
  change θ ∈ Fintype.piFinset (fun p : Pairs (2 * K) => labelsEq (firstBudget G K p.1.1 p.1.2))
    at hθ
  change ∏ w : Fin (2 * K), (if w.val < K then vTable G K w.val (Clique.labelAt θ w)
    else tTable G K (w.val - K) (Clique.labelAt θ w)) ≠ 0 at hne
  have hT := Finset.prod_ne_zero_iff.mp hne
  -- the encoding tests of the vertex groups
  have henc : ∀ i < K, ∀ τ < K, IsEnc (width G K i τ) (pairLabel K θ i τ) := by
    intro i hi τ hτ
    have h := hT ⟨i, by omega⟩ (Finset.mem_univ _)
    simp only [ite_eq_left hi] at h
    unfold vTable at h
    split_ifs at h with hc
    · have := hc τ hτ
      rwa [labelOfNode_vert _ ⟨i, by omega⟩ hi hτ] at this
    · exact absurd rfl h
  -- the equality tests of the test groups
  have htest : ∀ e : Fin G.M,
      heBit G K (pairLabel K θ (vgroup G K (G.u e)) (tgroup G K e))
          (vgroup G K (G.u e)) (tgroup G K e)
          (e, false) =
        heBit G K (pairLabel K θ (vgroup G K (G.w e)) (tgroup G K e))
            (vgroup G K (G.w e)) (tgroup G K e)
          (e, true) := by
    intro e
    have hτ := tgroup_lt hK e
    have h := hT ⟨K + tgroup G K e, by omega⟩ (Finset.mem_univ _)
    simp only [show ¬ K + tgroup G K e < K by omega, ite_false, Nat.add_sub_cancel_left] at h
    unfold tTable at h
    split_ifs at h with hc
    · have h' := Finset.prod_ne_zero_iff.mp h e (Finset.mem_univ _)
      rw [ite_eq_left rfl] at h'
      split_ifs at h' with hb
      · rw [labelOfNode_test _ ⟨K + tgroup G K e, by omega⟩ (by simp) (vgroup_lt hK _),
          labelOfNode_test _ ⟨K + tgroup G K e, by omega⟩ (by simp) (vgroup_lt hK _)] at hb
        simpa only [Nat.add_sub_cancel_left] using hb
      · exact absurd rfl h'
    · exact absurd rfl h
  funext p
  have hp := (Fintype.mem_piFinset.mp hθ) p
  rw [mem_labelsEq] at hp
  unfold encLab
  unfold firstBudget at hp
  split_ifs with hc
  · obtain ⟨h1, h2⟩ := hc
    have hτ : p.1.2.val - K < K := by have := p.1.2.isLt; omega
    rw [← pairLabel_eq θ p h1 h2]
    rw [← enc_decEnc (henc _ h1 _ hτ)]
    refine enc_congr fun n hn => ?_
    have hn' : n < (halfEdges G K p.1.1.val (p.1.2.val - K)).length := hn
    obtain ⟨⟨e, b⟩, hmem⟩ : ∃ he, (halfEdges G K p.1.1.val (p.1.2.val - K))[n]'hn' = he :=
      ⟨_, rfl⟩
    have hstr : strOf G K (decLab G K θ) p.1.1.val (p.1.2.val - K) n = decLab G K θ e := by
      simp [strOf, List.getElem?_eq_getElem hn', hmem]
    rw [hstr, ← heBit_getElem _ _ _ _ hn', hmem]
    have hin : (e, b) ∈ halfEdges G K p.1.1.val (p.1.2.val - K) := hmem ▸ List.getElem_mem hn
    obtain ⟨hte, hve⟩ := mem_halfEdges.mp hin
    unfold decLab
    cases b
    · simp only [Bool.false_eq_true, ite_false] at hve
      rw [hve, hte]
    · simp only [ite_true] at hve
      rw [htest e, hve, hte]
  · rw [ite_eq_right hc] at hp
    exact eq_zero_of_labelWt hp

end Value

/-- **Lemma 4.3 (b).** The first clique has value `Z(G)`. -/
theorem firstClique_value (hK : 1 ≤ K) : (firstClique G K).value = G.value := by
  unfold Clique.value EdgeNet.value
  symm
  refine Finset.sum_of_injOn (encLab G K) ?_ ?_ ?_ ?_
  · intro x _ y _ h
    have := congrArg (decLab G K) h
    rwa [decLab_encLab hK, decLab_encLab hK] at this
  · intro x _
    exact encLab_mem x
  · intro θ hθ hnot
    by_contra hne
    exact hnot ⟨decLab G K θ, by simp, (eq_encLab_of_ne_zero hK hθ hne).symm⟩
  · intro x _
    exact (prod_encLab hK x).symm

/-! ### The potential (Lemma 4.3 (a)) -/

section Potential

variable {G K}

/-! #### Degrees and the vertex groups -/

theorem deg_eq (v : Fin V) : deg G v = ((univ : Finset (Fin G.M)).filter fun e => G.u e = v).card +
    ((univ : Finset (Fin G.M)).filter fun e => G.w e = v).card := by
  unfold deg
  rw [Finset.filter_or]
  exact Finset.card_union_eq_card_add_card.mpr
    (Finset.disjoint_filter.mpr fun e _ h1 h2 => G.huw e (h1.trans h2.symm))

/-- The edges at a set of vertices, counted with the number of their ends in the set. -/
theorem sum_deg (S : Finset (Fin V)) : ∑ v ∈ S, deg G v =
    ((univ : Finset (Fin G.M)).filter fun e => G.u e ∈ S).card +
      ((univ : Finset (Fin G.M)).filter fun e => G.w e ∈ S).card := by
  simp only [deg_eq, Finset.sum_add_distrib, Finset.card_filter]
  rw [Finset.sum_comm, Finset.sum_comm (s := S)]
  simp [Finset.sum_ite_eq]

theorem deg_le {Δ : ℕ} (hΔ : ∀ v, (G.ports v).length ≤ Δ) (v : Fin V) : deg G v ≤ Δ := by
  calc deg G v ≤ (G.ports v).toFinset.card := Finset.card_le_card fun e he => by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
        exact List.mem_toFinset.mpr ((G.hports v e).mpr he)
    _ ≤ (G.ports v).length := List.toFinset_card_le _
    _ ≤ Δ := hΔ v

theorem pre_add_deg (v : Fin V) : pre G v + deg G v = ∑ u, if u ≤ v then deg G u else 0 := by
  have h : ∀ u, (if u ≤ v then deg G u else 0) =
      (if u < v then deg G u else 0) + (if u = v then deg G u else 0) := by
    intro u
    rcases lt_trichotomy u v with h | rfl | h
    · simp [h.le, h.ne, not_le.mpr h]
    · simp
    · simp [not_le.mpr h, not_lt.mpr h.le, h.ne']
  rw [Finset.sum_congr rfl fun u _ => h u, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp [pre]

theorem pre_add_deg_le_of_lt {u v : Fin V} (h : u < v) : pre G u + deg G u ≤ pre G v := by
  rw [pre_add_deg]
  unfold pre
  refine Finset.sum_le_sum fun x _ => ?_
  split_ifs with h1 h2
  · exact le_rfl
  · exact absurd (lt_of_le_of_lt h1 h) h2
  · exact Nat.zero_le _
  · exact le_rfl

theorem pre_add_deg_le_total (v : Fin V) : pre G v + deg G v ≤ 2 * G.M := by
  rw [pre_add_deg]
  calc (∑ u, if u ≤ v then deg G u else 0) ≤ ∑ u, deg G u :=
        Finset.sum_le_sum fun u _ => by split_ifs <;> simp
    _ = 2 * G.M := by rw [sum_deg]; simp; ring

/-- The vertices whose ports lie in a window `[lo, hi)` of the port list have at most `hi - lo`
ports. -/
theorem sum_deg_le_window (S : Finset (Fin V)) (lo hi : ℕ)
    (h : ∀ v ∈ S, lo ≤ pre G v ∧ pre G v + deg G v ≤ hi) : ∑ v ∈ S, deg G v ≤ hi - lo := by
  have hcard : ∑ v ∈ S, deg G v =
      (S.biUnion fun v => Finset.Ico (pre G v) (pre G v + deg G v)).card := by
    rw [Finset.card_biUnion]
    · simp
    · intro x _ y _ hxy
      rw [Function.onFun, Finset.disjoint_left]
      intro n hx hy
      simp only [Finset.mem_Ico] at hx hy
      rcases lt_or_gt_of_ne hxy with hl | hl
      · have := pre_add_deg_le_of_lt (G := G) hl; omega
      · have := pre_add_deg_le_of_lt (G := G) hl; omega
  rw [hcard]
  calc _ ≤ (Finset.Ico lo hi).card := Finset.card_le_card fun n hn => by
          simp only [Finset.mem_biUnion, Finset.mem_Ico] at hn ⊢
          obtain ⟨v, hv, h1, h2⟩ := hn
          have := h v hv
          omega
    _ = hi - lo := Nat.card_Ico lo hi

theorem one_le_blockD : 1 ≤ blockD G K := le_max_left _ _

theorem mul_blockD_le (hK : 1 ≤ K) : K * blockD G K ≤ 2 * G.M + K := by
  unfold blockD
  rcases le_total 1 ((2 * G.M + K - 1) / K) with h | h
  · rw [max_eq_right h]
    have := Nat.mul_div_le (2 * G.M + K - 1) K
    omega
  · rw [max_eq_left h]; omega

theorem two_M_le (hK : 1 ≤ K) : 2 * G.M ≤ K * blockD G K := by
  unfold blockD
  have h1 := Nat.div_add_mod (2 * G.M + K - 1) K
  have h2 := Nat.mod_lt (2 * G.M + K - 1) (show 0 < K by omega)
  have h3 : K * ((2 * G.M + K - 1) / K) ≤ K * max 1 ((2 * G.M + K - 1) / K) :=
    Nat.mul_le_mul_left _ (le_max_right _ _)
  omega

/-- **The ports of a vertex group.** Vertex group `i` has at most `D₀ + Δ` ports. -/
theorem sum_deg_group_le (hK : 1 ≤ K) {Δ : ℕ} (hΔ : ∀ v, (G.ports v).length ≤ Δ) (i : ℕ) :
    ∑ v ∈ (univ : Finset (Fin V)).filter (fun v => vgroup G K v = i), deg G v ≤
      blockD G K + Δ := by
  have hD := one_le_blockD (G := G) (K := K)
  have hKD := two_M_le (G := G) hK
  have e : K * blockD G K = (K - 1) * blockD G K + blockD G K := by
    rw [← Nat.succ_mul]; congr 1; omega
  by_cases hlast : i = K - 1
  · refine (sum_deg_le_window _ ((K - 1) * blockD G K) (2 * G.M) fun v hv => ?_).trans (by omega)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    refine ⟨?_, pre_add_deg_le_total v⟩
    unfold vgroup at hv
    have : K - 1 ≤ pre G v / blockD G K := by omega
    exact (Nat.le_div_iff_mul_le hD).mp this
  · refine (sum_deg_le_window _ (i * blockD G K) ((i + 1) * blockD G K + Δ) fun v hv => ?_).trans
      (by rw [Nat.add_mul, one_mul]; omega)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    unfold vgroup at hv
    have hq : pre G v / blockD G K = i := by omega
    have h1 := Nat.div_mul_le_self (pre G v) (blockD G K)
    have h2 := Nat.lt_mul_div_succ (pre G v) hD
    have h3 := deg_le hΔ v
    rw [hq] at h1 h2
    constructor
    · exact h1
    · rw [Nat.add_mul, one_mul]
      rw [Nat.mul_add, mul_one, mul_comm] at h2
      omega

/-! #### The cyclic distribution of the tests -/

variable (G K) in
/-- The pair of vertex groups of the ends of an edge. -/
def edgeCls (e : Fin G.M) : Finset ℕ := {vgroup G K (G.u e), vgroup G K (G.w e)}

theorem edgePos_eq (e : Fin G.M) : edgePos G K e =
    ((univ : Finset (Fin G.M)).filter fun e' => e' < e ∧ edgeCls G K e' = edgeCls G K e).card :=
  rfl

theorem edgePos_lt_of_lt {e₁ e₂ : Fin G.M} (hc : edgeCls G K e₁ = edgeCls G K e₂) (h : e₁ < e₂) :
    edgePos G K e₁ < edgePos G K e₂ := by
  rw [edgePos_eq, edgePos_eq]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨e₁, by simp [h, hc], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact ⟨hx.1.trans h, hx.2.trans hc⟩

theorem edgePos_lt_card (e : Fin G.M) : edgePos G K e <
    ((univ : Finset (Fin G.M)).filter fun e' => edgeCls G K e' = edgeCls G K e).card := by
  rw [edgePos_eq]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨e, by simp, by simp⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.2

/-- **The cyclic distribution.** Of the edges between two given vertex groups, at most
`⌈m / K⌉ ≤ m / K + 1` go to a given test group. -/
theorem card_tgroup_le (c : Finset ℕ) (τ : ℕ) :
    K * ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = c ∧ tgroup G K e = τ).card ≤
      ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = c).card + K := by
  set n := ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = c).card
  have h1 : ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = c ∧ tgroup G K e = τ).card ≤
      (range (n / K + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun e => edgePos G K e / K)
    · intro e he
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he
      have := edgePos_lt_card (G := G) (K := K) e
      rw [he.1] at this
      simp only [Finset.coe_range, Set.mem_Iio]
      exact Nat.lt_succ_of_le (Nat.div_le_div_right this.le)
    · intro e₁ he₁ e₂ he₂ heq
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at he₁ he₂ heq
      have hpos : edgePos G K e₁ = edgePos G K e₂ := by
        have a1 := Nat.div_add_mod (edgePos G K e₁) K
        have a2 := Nat.div_add_mod (edgePos G K e₂) K
        unfold tgroup at he₁ he₂
        rw [heq, he₁.2] at a1
        rw [he₂.2] at a2
        omega
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · exact absurd hpos (edgePos_lt_of_lt (he₁.1.trans he₂.1.symm) h).ne
      · exact absurd hpos (edgePos_lt_of_lt (he₂.1.trans he₁.1.symm) h).ne'
  rw [Finset.card_range] at h1
  calc _ ≤ K * (n / K + 1) := Nat.mul_le_mul_left _ h1
    _ = K * (n / K) + K := by ring
    _ ≤ n + K := by have := Nat.mul_div_le n K; omega

/-! #### The width of a pair -/

theorem width_eq (i τ : ℕ) : width G K i τ = ∑ e : Fin G.M, if tgroup G K e = τ then
    (if vgroup G K (G.u e) = i then 1 else 0) + (if vgroup G K (G.w e) = i then 1 else 0)
    else 0 := by
  have hlen : ∀ e : Fin G.M, ((if vgroup G K (G.u e) = i then [(e, false)] else []) ++
      (if vgroup G K (G.w e) = i then [(e, true)] else [])).length =
      (if vgroup G K (G.u e) = i then 1 else 0) + (if vgroup G K (G.w e) = i then 1 else 0) := by
    intro e; split_ifs <;> simp
  unfold width halfEdges
  rw [List.length_flatMap, Fin.sum_univ_def]
  simp only [hlen]
  generalize List.finRange G.M = l
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.filter_cons]
    split_ifs with h <;> simp_all

theorem pair_eq_pair_iff' {a b c d : ℕ} :
    ({a, b} : Finset ℕ) = {c, d} ↔ (a = c ∧ b = d) ∨ (a = d ∧ b = c) := by
  rw [← Finset.coe_inj, Finset.coe_pair, Finset.coe_pair, Set.pair_eq_pair_iff]

private theorem ends_le_of_other (a b i j : ℕ) (h : (if a = i then b else a) = j) :
    (if a = i then 1 else 0) + (if b = i then 1 else 0) ≤
      if ({a, b} : Finset ℕ) = {i, j} then (if j = i then 2 else 1) else 0 := by
  by_cases ha : a = i
  · rw [ite_eq_left ha] at h
    subst ha h
    by_cases hb : b = a
    · subst hb; simp
    · simp [hb]
  · rw [ite_eq_right ha] at h
    subst h
    rw [ite_eq_right ha]
    by_cases hb : b = i
    · subst hb
      rw [ite_eq_left rfl, ite_eq_left (Finset.pair_comm _ _), ite_eq_right ha]
    · simp [hb]

private theorem cls_le_ends (a b i j : ℕ) :
    (if ({a, b} : Finset ℕ) = {i, j} then (if j = i then 2 else 1) else 0) ≤
      if j = (if a = i then b else a) then
        (if a = i then 1 else 0) + (if b = i then 1 else 0) else 0 := by
  by_cases hc : ({a, b} : Finset ℕ) = {i, j}
  · rw [ite_eq_left hc]
    rcases pair_eq_pair_iff'.mp hc with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · by_cases hb : b = a
      · subst hb; simp
      · simp [hb]
    · by_cases hab : a = b
      · subst hab; simp
      · simp [hab]
  · rw [ite_eq_right hc]; exact Nat.zero_le _

/-- **The width bound.** `K b ≤ d_i + K (K + 1)` for the width `b` of a pair (vertex group `i`,
test group `τ`), where `d_i` counts the half-edges at vertex group `i`. -/
theorem width_mul_le (hK : 1 ≤ K) {i : ℕ} (hi : i < K) (τ : ℕ) :
    K * width G K i τ ≤
      (((univ : Finset (Fin G.M)).filter fun e => vgroup G K (G.u e) = i).card +
        ((univ : Finset (Fin G.M)).filter fun e => vgroup G K (G.w e) = i).card) + K * (K + 1) := by
  set gu : Fin G.M → ℕ := fun e => vgroup G K (G.u e) with hgu
  set gw : Fin G.M → ℕ := fun e => vgroup G K (G.w e) with hgw
  set o : Fin G.M → ℕ := fun e => if gu e = i then gw e else gu e with ho_def
  set ends : Fin G.M → ℕ := fun e => (if gu e = i then 1 else 0) + (if gw e = i then 1 else 0)
    with hends
  set cj : ℕ → ℕ := fun j => if j = i then 2 else 1 with hcj
  have ho : ∀ e, o e ∈ range K := fun e => by
    simp only [ho_def, Finset.mem_range]
    split_ifs
    · exact vgroup_lt hK _
    · exact vgroup_lt hK _
  have hcls : ∀ e, edgeCls G K e = {gu e, gw e} := fun e => rfl
  -- Step A: split the width by the other end of a half-edge.
  have hA : width G K i τ ≤ ∑ j ∈ range K, cj j *
      ((univ : Finset
          (Fin G.M)).filter fun e => edgeCls G K e = {i, j} ∧ tgroup G K e = τ).card := by
    rw [width_eq, ← Finset.sum_fiberwise_of_maps_to (g := o) (t := range K) (fun e _ => ho e)]
    refine Finset.sum_le_sum fun j _ => ?_
    calc _ ≤ ∑ e ∈ (univ : Finset (Fin G.M)).filter (fun e => o e = j),
          (if edgeCls G K e = {i, j} ∧ tgroup G K e = τ then cj j else 0) := by
          refine Finset.sum_le_sum fun e he => ?_
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at he
          by_cases ht : tgroup G K e = τ
          · simp only [ht, and_true, ite_true, hcls]
            exact ends_le_of_other _ _ i j he
          · simp [ht]
      _ ≤ ∑ e : Fin G.M, (if edgeCls G K e = {i, j} ∧ tgroup G K e = τ then cj j else 0) :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ = _ := by rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, smul_eq_mul,
          add_zero, mul_comm]
  -- Step B: the cyclic distribution.
  have hB : K * width G K i τ ≤ ∑ j ∈ range K, cj j *
      (((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = {i, j}).card + K) := by
    calc K * width G K i τ ≤ K * ∑ j ∈ range K, cj j *
          ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = {i, j} ∧
            tgroup G K e = τ).card := Nat.mul_le_mul_left _ hA
      _ = ∑ j ∈ range K, cj j * (K *
          ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = {i, j} ∧
            tgroup G K e = τ).card) := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
      _ ≤ _ := Finset.sum_le_sum fun j _ => Nat.mul_le_mul_left _ (card_tgroup_le _ τ)
  -- Step C: the multiplicities add up to `K + 1`.
  have hC : ∑ j ∈ range K, cj j = K + 1 := by
    calc ∑ j ∈ range K, cj j = ∑ j ∈ range K, (1 + if j = i then 1 else 0) :=
          Finset.sum_congr rfl fun j _ => by simp only [hcj]; split_ifs <;> rfl
      _ = K + 1 := by rw [Finset.sum_add_distrib, Finset.sum_ite_eq']; simp [hi]
  -- Step D: the edges between group `i` and the other groups are its half-edges.
  have hD : ∑ j ∈ range K, cj j *
      ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = {i, j}).card ≤
      ((univ : Finset (Fin G.M)).filter fun e => gu e = i).card +
        ((univ : Finset (Fin G.M)).filter fun e => gw e = i).card := by
    calc _ = ∑ j ∈ range K, ∑ e : Fin G.M, (if edgeCls G K e = {i, j} then cj j else 0) :=
          Finset.sum_congr rfl fun j _ => by rw [Finset.card_filter, Finset.mul_sum]; simp
      _ = ∑ e : Fin G.M, ∑ j ∈ range K, (if edgeCls G K e = {i, j} then cj j else 0) :=
          Finset.sum_comm
      _ ≤ ∑ e : Fin G.M, ∑ j ∈ range K, (if j = o e then ends e else 0) :=
          Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun j _ => by
            rw [hcls]; exact cls_le_ends _ _ i j
      _ ≤ ∑ e : Fin G.M, ends e := Finset.sum_le_sum fun e _ => by
          rw [Finset.sum_ite_eq']; split_ifs <;> simp
      _ = _ := by
          simp only [hends, Finset.sum_add_distrib, Finset.card_filter]
  calc K * width G K i τ ≤ _ := hB
    _ = ∑ j ∈ range K, cj j *
          ((univ : Finset (Fin G.M)).filter fun e => edgeCls G K e = {i, j}).card +
          K * ∑ j ∈ range K, cj j := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ _ := by rw [hC]; exact Nat.add_le_add_right hD _

/-- `K² b ≤ 2 (M + K(Δ + 1) + K³)` for every width `b`. -/
theorem width_bound (hK : 1 ≤ K) {Δ : ℕ} (hΔ : ∀ v, (G.ports v).length ≤ Δ) {i : ℕ} (hi : i < K)
    (τ : ℕ) : K * K * width G K i τ ≤ 2 * (G.M + K * (Δ + 1) + K ^ 3) := by
  have h1 := width_mul_le (G := G) hK hi τ
  have h2 := sum_deg_group_le (G := G) hK hΔ i
  rw [sum_deg] at h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h2
  have h3 := mul_blockD_le (G := G) hK
  have h4 : K ^ 2 ≤ K ^ 3 := Nat.pow_le_pow_right hK (by norm_num)
  calc K * K * width G K i τ = K * (K * width G K i τ) := by ring
    _ ≤ K * (blockD G K + Δ + K * (K + 1)) := Nat.mul_le_mul_left _ (h1.trans (by omega))
    _ = K * blockD G K + K * Δ + K ^ 3 + K ^ 2 := by ring
    _ ≤ 2 * (G.M + K * (Δ + 1) + K ^ 3) := by nlinarith

end Potential

/-- **Lemma 4.3 (a).** `Φ(𝒞₀) ≤ 64 (M + K(Δ + 1) + K³)²`, where `Δ` bounds the degrees. -/
theorem firstClique_potential (hK : 1 ≤ K) (Δ : ℕ) (hΔ : ∀ v, (G.ports v).length ≤ Δ) :
    (firstClique G K).potential ≤ 64 * (G.M + K * (Δ + 1) + K ^ 3) ^ 2 := by
  set S := G.M + K * (Δ + 1) + K ^ 3
  change (2 * K - 1) ^ 2 * ∑ p : Pairs (2 * K), firstBudget G K p.1.1 p.1.2 ≤ 64 * S ^ 2
  have hb : ∀ x : Fin (2 * K) × Fin (2 * K), K ^ 4 * firstBudget G K x.1 x.2 ≤
      if x.1.val < K ∧ K ≤ x.2.val then 4 * S ^ 2 else 0 := by
    intro x
    unfold firstBudget
    split_ifs with h
    · set b := width G K x.1.val (x.2.val - K)
      have hw : K * K * b ≤ 2 * S := width_bound hK hΔ h.1 _
      have hbb : b * (b + 1) / 2 ≤ b * b := Nat.div_le_of_le_mul (by nlinarith)
      calc K ^ 4 * (b * (b + 1) / 2) ≤ K ^ 4 * (b * b) := Nat.mul_le_mul_left _ hbb
        _ = (K * K * b) ^ 2 := by ring
        _ ≤ (2 * S) ^ 2 := Nat.pow_le_pow_left hw 2
        _ = 4 * S ^ 2 := by ring
    · simp
  have hcount : ((univ : Finset (Fin (2 * K) × Fin (2 * K))).filter
      fun x => x.1.val < K ∧ K ≤ x.2.val).card ≤ K * K := by
    calc _ ≤ (range K ×ˢ range K).card := by
          apply Finset.card_le_card_of_injOn (fun x => (x.1.val, x.2.val - K))
          · intro x hx
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx
            have := x.2.isLt
            simp only [Finset.coe_product, Finset.coe_range, Set.mem_prod, Set.mem_Iio]
            omega
          · intro x hx y hy hxy
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hx hy
            simp only [Prod.mk.injEq] at hxy
            exact Prod.ext (Fin.ext hxy.1) (Fin.ext (by omega))
      _ = K * K := by rw [Finset.card_product, Finset.card_range]
  have hsum : K ^ 4 * ∑ p : Pairs (2 * K), firstBudget G K p.1.1 p.1.2 ≤ K * K * (4 * S ^ 2) := by
    rw [Finset.mul_sum]
    rw [← Finset.sum_subtype ((univ : Finset (Fin (2 * K) × Fin (2 * K))).filter
      fun x => x.1 < x.2) (by simp) (fun x => K ^ 4 * firstBudget G K x.1 x.2)]
    calc _ ≤ ∑ x : Fin (2 * K) × Fin (2 * K), K ^ 4 * firstBudget G K x.1 x.2 :=
          Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
      _ ≤ ∑ x : Fin (2 * K) × Fin (2 * K), (if x.1.val < K ∧ K ≤ x.2.val then 4 * S ^ 2 else 0) :=
          Finset.sum_le_sum fun x _ => hb x
      _ = ((univ : Finset (Fin (2 * K) × Fin (2 * K))).filter
            fun x => x.1.val < K ∧ K ≤ x.2.val).card * (4 * S ^ 2) := by
          rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, smul_eq_mul, add_zero]
      _ ≤ K * K * (4 * S ^ 2) := Nat.mul_le_mul_right _ hcount
  have hq : (2 * K - 1) ^ 2 ≤ 4 * K ^ 2 := by
    calc (2 * K - 1) ^ 2 ≤ (2 * K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
      _ = 4 * K ^ 2 := by ring
  have hK4 : 0 < K ^ 4 := by positivity
  refine Nat.le_of_mul_le_mul_left ?_ hK4
  calc K ^ 4 * ((2 * K - 1) ^ 2 * ∑ p : Pairs (2 * K), firstBudget G K p.1.1 p.1.2)
      = (2 * K - 1) ^ 2 * (K ^ 4 * ∑ p : Pairs (2 * K), firstBudget G K p.1.1 p.1.2) := by ring
    _ ≤ (4 * K ^ 2) * (K * K * (4 * S ^ 2)) := Nat.mul_le_mul hq hsum
    _ = K ^ 4 * (16 * S ^ 2) := by ring
    _ ≤ K ^ 4 * (64 * S ^ 2) := Nat.mul_le_mul_left _ (by omega)

end Cslib.Complexity.NtimeDspace.Cube
