/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Orthogonal.Simple
import Aesop
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Diagonal boxes and upper tracks for finite orthogonal layouts

Vertex `v` is centered at `(8v+4,8v+4)`. Its three ports leave to the left, up, and right,
and then rise on columns `8v+2`, `8v+4`, and `8v+6`. Edge `e` travels horizontally on row
`8n+2e+2`, above all `n` vertex boxes. All data are explicit finite lists.

## Main definitions

* `Cslib.Orthogonal.Layout.center`, `Cslib.Orthogonal.Layout.column`: vertex centers and ports.
* `Cslib.Orthogonal.Layout.route`: six listed points defining a five-segment route.

## Main results

* `Cslib.Orthogonal.Layout.route_orthogonal`: the routes are proper and orthogonal.
* `Cslib.Orthogonal.Layout.route_bounds`: explicit linear grid sides.
* `Cslib.Orthogonal.Layout.route_simple`: continuous simplicity.
* `Cslib.Orthogonal.Layout.route_contact`: shared endpoint or strict transverse crossing.
* `Cslib.Orthogonal.Layout.center_mem_support_iff`: no incidental vertex contacts.

## References

The box/track construction and its proofs are original.
-/

@[expose] public section

namespace Cslib.Orthogonal.Layout

/-- Vertex center inside its diagonal box of side eight. -/
def center (v : ℕ) : Point := (8 * (v : ℤ) + 4, 8 * (v : ℤ) + 4)

/-- The three distinct upward port columns, ordered left to right. -/
def column (v : ℕ) (s : Fin 3) : ℤ := 8 * (v : ℤ) + 2 * (s : ℕ) + 2

/-- A two-unit initial step to the left, up, or right. -/
def elbow (v : ℕ) (s : Fin 3) : Point :=
  (column v s, (center v).2 + if s = 1 then 2 else 0)

/-- A private upper horizontal row for the indexed edge. -/
def track (n e : ℕ) : ℤ := 8 * (n : ℤ) + 2 * (e : ℤ) + 2

/-- A route from port `s` at vertex `u` to port `t` at vertex `v`, on edge track `e`.
The middle port has two consecutive collinear vertical segments. -/
def route (n e u v : ℕ) (s t : Fin 3) : Route :=
  [center u, elbow u s, (column u s, track n e),
    (column v t, track n e), elbow v t, center v]

/-- The local initial segment inside one vertex box. -/
def fan (v : ℕ) (s : Fin 3) : Set (ℝ × ℝ) := segment (center v) (elbow v s)

/-- The upward part of a port, from its local elbow to the private edge track. -/
def stem (n e v : ℕ) (s : Fin 3) : Set (ℝ × ℝ) :=
  segment (elbow v s) (column v s, track n e)

/-- The upper horizontal part of an edge. -/
def bridge (n e u v : ℕ) (s t : Fin 3) : Set (ℝ × ℝ) :=
  segment (column u s, track n e) (column v t, track n e)

/-- Decompose the continuous route into its two local fans, two stems, and upper bridge. -/
theorem support_route (n e u v : ℕ) (s t : Fin 3) :
    support (route n e u v s t) =
      fan u s ∪ stem n e u s ∪ bridge n e u v s t ∪ stem n e v t ∪ fan v t := by
  simp only [route, support_cons_cons, segment,
    segment_symm ℝ (realPoint (column v t, track n e)) (realPoint (elbow v t)),
    segment_symm ℝ (realPoint (elbow v t)) (realPoint (center v))]
  ext p
  have hc : realPoint (center v) ∈ fan v t := left_mem_segment ℝ _ _
  simp only [fan, stem, bridge, segment, support, List.consecutivePairs, List.tail_cons,
    List.zip_nil_right, List.not_mem_nil, List.mem_singleton,
    exists_eq_left, Set.mem_ofPred_eq, Set.mem_union] at *
  aesop

/-- Port columns uniquely identify both the vertex and the port. -/
theorem column_injective {u v : ℕ} {s t : Fin 3} (h : column u s = column v t) :
    u = v ∧ s = t := by
  have hs := s.isLt
  have ht := t.isLt
  simp only [column] at h
  exact ⟨by omega, Fin.ext (by omega)⟩

/-- All points of the local fan stay in its vertex's small diagonal box. -/
theorem fan_bounds {v : ℕ} {s : Fin 3} {p : ℝ × ℝ} (hp : p ∈ fan v s) :
    8 * (v : ℝ) + 2 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 6 ∧
    8 * (v : ℝ) + 4 ≤ p.2 ∧ p.2 ≤ 8 * (v : ℝ) + 6 := by
  have hb := mem_segment_bounds hp
  have hs' : (s : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ s.isLt
  have hs0 : (0 : ℝ) ≤ s := by positivity
  simp only [center, elbow, column, Set.mem_uIcc] at hb
  push_cast at hb
  split_ifs at hb <;> rcases hb with ⟨hx | hx, hy | hy⟩
  all_goals refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith

/-- Distinct vertex boxes have disjoint local fans. -/
theorem fan_disjoint {u v : ℕ} (huv : u ≠ v) (s t : Fin 3) :
    Disjoint (fan u s) (fan v t) := by
  refine Set.disjoint_left.2 fun p hp hq => ?_
  have hp' := fan_bounds hp
  rcases lt_or_gt_of_ne huv with h | h <;> cast_linarith [fan_bounds hq]

/-- Membership in a stem fixes its column and its closed vertical interval. -/
theorem mem_stem {n e v : ℕ} {s : Fin 3} {p : ℝ × ℝ} :
    p ∈ stem n e v s ↔ p.1 = (column v s : ℝ) ∧
      p.2 ∈ Set.uIcc ((elbow v s).2 : ℝ) (track n e : ℝ) := mem_vertical

/-- Membership in a bridge fixes its row and its closed horizontal interval. -/
theorem mem_bridge {n e u v : ℕ} {s t : Fin 3} {p : ℝ × ℝ} :
    p ∈ bridge n e u v s t ↔ p.2 = (track n e : ℝ) ∧
      p.1 ∈ Set.uIcc (column u s : ℝ) (column v t : ℝ) := mem_horizontal

/-- The three local fans, in left/up/right order, have these explicit real supports. -/
theorem mem_fan {v : ℕ} {s : Fin 3} {p : ℝ × ℝ} :
    p ∈ fan v s ↔
      (s = 0 ∧ p.2 = 8 * (v : ℝ) + 4 ∧
        8 * (v : ℝ) + 2 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 4) ∨
      (s = 1 ∧ p.1 = 8 * (v : ℝ) + 4 ∧
        8 * (v : ℝ) + 4 ≤ p.2 ∧ p.2 ≤ 8 * (v : ℝ) + 6) ∨
      (s = 2 ∧ p.2 = 8 * (v : ℝ) + 4 ∧
        8 * (v : ℝ) + 4 ≤ p.1 ∧ p.1 ≤ 8 * (v : ℝ) + 6) := by
  fin_cases s <;> norm_num only [fan, segment, realPoint, center, elbow, column,
    Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
    Int.cast_add, Int.cast_mul, Int.cast_natCast,
    and_true, and_false, true_and, false_and, or_true, or_false, true_or, false_or]
  all_goals ring_nf
  all_goals first | rw [mem_horizontal] | rw [mem_vertical]
  all_goals simp only [Set.mem_uIcc]
  all_goals
    constructor
    · rintro ⟨h, h' | h'⟩ <;> exact ⟨h, by constructor <;> linarith⟩
    · exact fun ⟨h, h'⟩ => ⟨h, by tauto⟩

/-- Every edge row lies strictly above every vertex box. -/
theorem elbow_below_track {n e v : ℕ} (hv : v < n) (s : Fin 3) :
    (elbow v s).2 < track n e := by
  simp only [elbow, center, track]
  split_ifs <;> omega

/-- The fixed initial segment is proper and orthogonal. -/
theorem center_elbow_axisAligned (v : ℕ) (s : Fin 3) : AxisAligned (center v) (elbow v s) := by
  fin_cases s <;> norm_num only [AxisAligned, center, elbow, column, ne_eq, Prod.mk.injEq,
    Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte]
  all_goals omega

/-- The complete route has exactly five segments. -/
theorem route_segments_length (n e u v : ℕ) (s t : Fin 3) :
    (route n e u v s t).consecutivePairs.length = 5 := rfl

/-- The route starts and ends at the specified centers. -/
@[simp] theorem route_head (n e u v : ℕ) (s t : Fin 3) :
    (route n e u v s t).head? = some (center u) := rfl

/-- The route starts and ends at the specified centers. -/
@[simp] theorem route_last (n e u v : ℕ) (s t : Fin 3) :
    (route n e u v s t).getLast? = some (center v) := rfl

/-- Proper orthogonality uses only distinct vertices and the vertex range bounds. -/
theorem route_orthogonal {n e u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (s t : Fin 3) : IsOrthogonal (route n e u v s t) := by
  intro a ha
  simp only [route, List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl
  · exact center_elbow_axisAligned u s
  · exact ⟨Or.inl rfl, fun h => (ne_of_lt (elbow_below_track (e := e) hu s)) (congrArg Prod.snd h)⟩
  · exact ⟨Or.inr rfl, fun h => huv (column_injective (congrArg Prod.fst h)).1⟩
  · exact ⟨Or.inl rfl, fun h => (ne_of_gt (elbow_below_track (e := e) hv t)) (congrArg Prod.snd h)⟩
  · exact ⟨(center_elbow_axisAligned v t).1.imp Eq.symm Eq.symm,
      (center_elbow_axisAligned v t).2.symm⟩

/-- All six listed points lie in a rectangle with width `8n` and height `8n+2m`.
The convention permits an empty graph and uses only edges `e < m`. -/
theorem route_bounds {n m e u v : ℕ} (he : e < m) (hu : u < n) (hv : v < n)
    (s t : Fin 3) {p : Point} (hp : p ∈ route n e u v s t) :
    0 ≤ p.1 ∧ p.1 ≤ 8 * (n : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ 8 * (n : ℤ) + 2 * m := by
  have hs := s.isLt
  have ht := t.isLt
  simp only [route, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [center, elbow, column, track] <;> (try split_ifs) <;> omega

/-- One edge has wire length at most `80n+10m`, with no assumption on degree. -/
theorem route_wireLength_le {n m e u v : ℕ} (he : e < m) (hu : u < n) (hv : v < n)
    (s t : Fin 3) : wireLength (route n e u v s t) ≤ 80 * n + 10 * m := by
  have hb := wireLength_le_box (w := 8 * n) (h := 8 * n + 2 * m) (r := route n e u v s t)
    fun _ hp => mod_cast route_bounds he hu hv s t hp
  rw [route_segments_length] at hb; omega

/-- A route visits no vertex center except its two prescribed endpoints. This concerns the
whole real segment support, not only its six listed points. -/
theorem center_mem_support_iff {n e u v w : ℕ} (hu : u < n) (hv : v < n)
    (hw : w < n) (huv : u ≠ v) (s t : Fin 3) :
    realPoint (center w) ∈ support (route n e u v s t) ↔ w = u ∨ w = v := by
  rw [realPoint_mem_support_iff (route_orthogonal hu hv huv s t)]
  fin_cases s <;> fin_cases t <;>
    simp only [route, center, elbow, column, track, List.consecutivePairs, List.tail_cons,
      List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
      or_false, or_and_right, exists_or, exists_eq_left, Fin.reduceFinMk, Fin.isValue,
      Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, mul_zero, mul_one, add_zero,
      ↓reduceIte, Prod.mk.injEq] <;> omega

/-- Two different ports in a single vertex box meet only at the vertex center. -/
theorem fan_contact {v : ℕ} {s t : Fin 3} (hst : s ≠ t) {p : ℝ × ℝ}
    (hs : p ∈ fan v s) (ht : p ∈ fan v t) : p = realPoint (center v) := by
  rw [mem_fan] at hs ht
  rcases hs with ⟨hs, hy, hx⟩ | ⟨hs, hx, hy⟩ | ⟨hs, hy, hx⟩ <;>
    rcases ht with ⟨ht, hy', hx'⟩ | ⟨ht, hx', hy'⟩ | ⟨ht, hy', hx'⟩ <;>
    subst s <;> subst t <;> try contradiction
  all_goals apply Prod.ext <;> simp only [realPoint, center] <;> push_cast <;> linarith

/-- A fan can contact a stem only when both belong to the same port. -/
theorem fan_stem_port_eq {n e u v : ℕ} (hv : v < n) {s t : Fin 3} {p : ℝ × ℝ}
    (hp : p ∈ fan u s) (hq : p ∈ stem n e v t) : u = v ∧ s = t := by
  have hb := fan_bounds hp
  have hcol := (mem_stem.1 hq).1
  have ht : (t : ℝ) ≤ 2 := by exact_mod_cast Nat.le_of_lt_succ t.isLt
  have ht0 : (0 : ℝ) ≤ t := by positivity
  have huv : u = v := by
    by_contra h
    simp only [column] at hcol
    push_cast at hcol
    rcases lt_or_gt_of_ne h with h | h <;> cast_linarith
  subst v
  refine ⟨rfl, ?_⟩
  rw [mem_stem, Set.uIcc_of_le (mod_cast (elbow_below_track (e := e) hv t).le)] at hq
  rw [mem_fan] at hp
  rcases hp with ⟨rfl, hy, hx⟩ | ⟨rfl, hx, hy⟩ | ⟨rfl, hy, hx⟩ <;>
    fin_cases t <;> norm_num only [column, elbow, center, Fin.ext_iff, Fin.val_mk, Fin.val_zero,
      Fin.val_one, Fin.val_two, ↓reduceIte,
      Int.cast_add, Int.cast_mul, Int.cast_natCast, Set.mem_Icc] at hq ⊢ <;> linarith

/-- Different port columns give disjoint stems, independently of their edge heights. -/
theorem stem_disjoint {n e f u v : ℕ} {s t : Fin 3} (h : (u, s) ≠ (v, t)) :
    Disjoint (stem n e u s) (stem n f v t) :=
  Set.disjoint_left.2 fun _ hp hq => h <| Prod.ext_iff.2 <| column_injective <| by
    exact_mod_cast (mem_stem.1 hp).1.symm.trans (mem_stem.1 hq).1

/-- A local fan lies strictly below every upper bridge. -/
theorem fan_bridge_disjoint {n e u v w : ℕ} (hw : w < n) (s t q : Fin 3) :
    Disjoint (fan w q) (bridge n e u v s t) := by
  refine Set.disjoint_left.2 fun p hp hq => ?_
  have hy := (mem_bridge.1 hq).1
  simp only [track] at hy
  cast_linarith [hw, fan_bounds hp, (Nat.cast_nonneg e : (0 : ℝ) ≤ e)]

/-- Distinct edge tracks give disjoint upper bridges. -/
theorem bridge_disjoint {n e f u v a b : ℕ} (hef : e ≠ f) (s t q r : Fin 3) :
    Disjoint (bridge n e u v s t) (bridge n f a b q r) := by
  refine Set.disjoint_left.2 fun p hp hq => hef ?_
  have ht : track n e = track n f := mod_cast (mem_bridge.1 hp).1.symm.trans (mem_bridge.1 hq).1
  simp only [track] at ht; omega

/-- Fans and stems at distinct ports are disjoint, even within one vertex box. -/
theorem fan_stem_disjoint {n e u v : ℕ} (hv : v < n) {s t : Fin 3}
    (h : (u, s) ≠ (v, t)) : Disjoint (fan u s) (stem n e v t) :=
  Set.disjoint_left.2 fun _ hp hq => h (Prod.ext_iff.2 (fan_stem_port_eq hv hp hq))

/-- The two consecutive parts of one port meet only at their common elbow. -/
theorem fan_stem_endpointContacts {n e v : ℕ} (hv : v < n) (s : Fin 3) :
    EndpointContacts (center v) (elbow v s) (elbow v s) (column v s, track n e) := by
  intro p hp hq
  change p ∈ fan v s at hp
  change p ∈ stem n e v s at hq
  rw [mem_stem, Set.uIcc_of_le (mod_cast (elbow_below_track (e := e) hv s).le)] at hq
  have heq : p = realPoint (elbow v s) := by
    apply Prod.ext hq.1
    rw [mem_fan] at hp
    rcases hp with ⟨rfl, hy, hx⟩ | ⟨rfl, hx, hy⟩ | ⟨rfl, hy, hx⟩ <;>
      norm_num only [realPoint, elbow, center, column, Fin.ext_iff, Fin.val_mk, Fin.val_zero,
        Fin.val_one, Fin.val_two, ↓reduceIte,
        Int.cast_add, Int.cast_mul, Int.cast_natCast, Set.mem_Icc] at hq ⊢ <;> linarith
  exact ⟨Or.inr heq, Or.inl heq⟩

/-- A stem meets its own bridge only at their common upper endpoint. -/
theorem stem_bridge_endpointContacts (n e u v : ℕ) (s t : Fin 3) :
    EndpointContacts (elbow u s) (column u s, track n e)
      (column u s, track n e) (column v t, track n e) := fun _ hp hq =>
  let heq := Prod.ext (mem_stem.1 hp).1 (mem_bridge.1 hq).1
  ⟨Or.inr heq, Or.inl heq⟩

/-- The six listed points are distinct for an edge with distinct endpoints. -/
theorem route_nodup {n e u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (s t : Fin 3) : (route n e u v s t).Nodup := by
  fin_cases s <;> fin_cases t <;>
    norm_num only [route, center, elbow, column, track, List.nodup_cons, Prod.mk.injEq,
      Fin.ext_iff, Fin.val_mk, Fin.val_zero, Fin.val_one, Fin.val_two, ↓reduceIte,
      List.mem_cons, List.not_mem_nil, or_false,
      not_false_eq_true, and_true, List.nodup_nil] <;> omega

/-- The whole real polygonal route is simple: distinct consecutive segments contact only at
their common listed endpoints, and no listed point is repeated. -/
theorem route_simple {n e u v : ℕ} (hu : u < n) (hv : v < n) (huv : u ≠ v)
    (s t : Fin 3) : IsSimple (route n e u v s t) := by
  have hport : (u, s) ≠ (v, t) := fun h => huv (congrArg Prod.fst h)
  have h01 := fan_stem_endpointContacts (e := e) hu s
  have h02 := endpointContacts_of_disjoint (fan_bridge_disjoint (e := e) (u := u) (v := v) hu s t s)
  have h03 := (endpointContacts_of_disjoint (fan_stem_disjoint (e := e) hv hport)).reverse_right
  have h04 := (endpointContacts_of_disjoint (fan_disjoint huv s t)).reverse_right
  have h12 := stem_bridge_endpointContacts n e u v s t
  have h13 := (endpointContacts_of_disjoint
    (stem_disjoint (n := n) (e := e) (f := e) hport)).reverse_right
  have h14 := (endpointContacts_of_disjoint
    (fan_stem_disjoint (e := e) hu hport.symm).symm).reverse_right
  have h23 := (stem_bridge_endpointContacts n e v u t s).reverse_right.symm.reverse_right
  have h24 := (endpointContacts_of_disjoint
    (fan_bridge_disjoint (e := e) (u := u) (v := v) hv s t t).symm).reverse_right
  have h34 := (fan_stem_endpointContacts (e := e) hv t).symm.reverse_left.reverse_right
  refine ⟨route_nodup hu hv huv s t, ?_⟩
  intro first hf second hg hne
  simp only [route, List.consecutivePairs, List.tail_cons, List.zip_cons_cons, List.zip_nil_right,
    List.mem_cons, List.not_mem_nil, or_false] at hf hg
  rcases hf with rfl | rfl | rfl | rfl | rfl <;>
    rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    first | exact (hne rfl).elim | assumption | exact EndpointContacts.symm ‹_›

/-- Every contact of an upper bridge with another edge's distinct port stem is a genuine
transverse crossing, strictly inside both segments. In particular it is never at a bend. -/
theorem bridge_stem_transverse {n e f u v w : ℕ} (hw : w < n) (hef : e ≠ f)
    {s t q : Fin 3} (hu : (w, q) ≠ (u, s)) (hv : (w, q) ≠ (v, t)) {p : ℝ × ℝ}
    (hp : p ∈ bridge n e u v s t) (hq : p ∈ stem n f w q) :
    Transverse (column u s, track n e) (column v t, track n e)
      (elbow w q) (column w q, track n f) p := by
  have hb := mem_bridge.1 hp
  have hs := mem_stem.1 hq
  have hcol : ∀ {x i}, (w, q) ≠ (x, i) → column w q ≠ column x i := fun h hc =>
    h (Prod.ext_iff.2 (column_injective hc))
  have hcu := hcol hu
  have hcv := hcol hv
  have hx : min (column u s) (column v t) < column w q ∧
      column w q < max (column u s) (column v t) := by
    have hmem := hb.2
    rw [hs.1, Set.mem_uIcc] at hmem
    norm_cast at hmem
    omega
  have hlow := elbow_below_track (e := e) hw q
  have hfhigh := elbow_below_track (e := f) hw q
  have hy : (elbow w q).2 < track n e ∧ track n e < track n f := by
    have hmem := hs.2
    have hfh : ((elbow w q).2 : ℝ) ≤ track n f := by exact_mod_cast hfhigh.le
    rw [Set.uIcc_of_le hfh, hb.1] at hmem
    have hupper : track n e ≤ track n f := by exact_mod_cast hmem.2
    have hne : track n e ≠ track n f := by simp only [track]; omega
    exact ⟨hlow, lt_of_le_of_ne hupper hne⟩
  exact Or.inl ⟨rfl, rfl, Prod.ext hs.1 hb.1, hx.1, hx.2,
    (min_eq_left hfhigh.le).trans_lt hy.1, hy.2.trans_eq (max_eq_right hfhigh.le).symm⟩

/-- A bridge/stem transverse crossing has its exact integer column/row coordinates. -/
theorem bridge_stem_crossing_point {n e f u v w : ℕ} {s t q : Fin 3} {p : ℝ × ℝ}
    (h : Transverse (column u s, track n e) (column v t, track n e)
      (elbow w q) (column w q, track n f) p) :
    p = realPoint (column w q, track n e) :=
  h.elim (fun ⟨_, _, hp, _⟩ => hp) fun ⟨_, _, _, hlo, hhi, _⟩ => by
    simp only [elbow, min_self, max_self] at hlo hhi; omega

/-- Distinct ports' fans can contact only at their common graph endpoint. -/
theorem fan_pair_contact {u v : ℕ} {s t : Fin 3} (h : (u, s) ≠ (v, t))
    {p : ℝ × ℝ} (hp : p ∈ fan u s) (hq : p ∈ fan v t) :
    u = v ∧ p = realPoint (center u) := by
  rcases eq_or_ne u v with rfl | huv
  · exact ⟨rfl, fan_contact (fun hst => h (Prod.ext rfl hst)) hp hq⟩
  · exact False.elim (Set.disjoint_left.1 (fan_disjoint huv s t) hp hq)

/-- Any pairwise route contact is either a shared graph endpoint or a strict transverse
bridge/stem crossing. The four port inequalities require different edge incidences to use
different ports, including at a shared vertex. All statements concern continuous real supports. -/
theorem route_contact {n e f u v a b : ℕ}
    (hu : u < n) (hv : v < n) (ha : a < n) (hb : b < n) (hef : e ≠ f)
    {s t q r : Fin 3} (huaq : (u, s) ≠ (a, q)) (hubr : (u, s) ≠ (b, r))
    (hvaq : (v, t) ≠ (a, q)) (hvbr : (v, t) ≠ (b, r)) {p : ℝ × ℝ}
    (hp : p ∈ support (route n e u v s t)) (hq : p ∈ support (route n f a b q r)) :
    (∃ w, (w = u ∨ w = v) ∧ (w = a ∨ w = b) ∧ p = realPoint (center w)) ∨
    Transverse (column u s, track n e) (column v t, track n e)
      (elbow a q) (column a q, track n f) p ∨
    Transverse (column u s, track n e) (column v t, track n e)
      (elbow b r) (column b r, track n f) p ∨
    Transverse (column a q, track n f) (column b r, track n f)
      (elbow u s) (column u s, track n e) p ∨
    Transverse (column a q, track n f) (column b r, track n f)
      (elbow v t) (column v t, track n e) p := by
  rw [support_route] at hp hq
  simp only [Set.mem_union] at hp hq
  have hfs : ∀ {x y k : ℕ} {i j : Fin 3}, y < n → (x, i) ≠ (y, j) → p ∈ fan x i →
      p ∈ stem n k y j → False := fun hy hne hp hq =>
    hne (Prod.ext_iff.2 (fan_stem_port_eq hy hp hq))
  have hfan {w : ℕ} {i : Fin 3} (hw : w < n) (hwuv : w = u ∨ w = v)
      (hwaq : (w, i) ≠ (a, q)) (hwbr : (w, i) ≠ (b, r)) (hp : p ∈ fan w i) :
      ∃ w', (w' = u ∨ w' = v) ∧ (w' = a ∨ w' = b) ∧ p = realPoint (center w') := by
    rcases hq with (((hq | hq) | hq) | hq) | hq
    exacts [⟨w, hwuv, (fan_pair_contact hwaq hp hq).imp Or.inl id⟩, (hfs ha hwaq hp hq).elim,
      (Set.disjoint_left.1 (fan_bridge_disjoint hw _ _ _) hp hq).elim, (hfs hb hwbr hp hq).elim,
      ⟨w, hwuv, (fan_pair_contact hwbr hp hq).imp Or.inr id⟩]
  have hstem {w : ℕ} {i : Fin 3} (hw : w < n) (hwaq : (w, i) ≠ (a, q))
      (hwbr : (w, i) ≠ (b, r)) (hp : p ∈ stem n e w i) :
      Transverse (column a q, track n f) (column b r, track n f)
        (elbow w i) (column w i, track n e) p := by
    rcases hq with (((hq | hq) | hq) | hq) | hq
    exacts [(hfs hw hwaq.symm hq hp).elim, (Set.disjoint_left.1 (stem_disjoint hwaq) hp hq).elim,
      bridge_stem_transverse hw hef.symm hwaq hwbr hq hp,
      (Set.disjoint_left.1 (stem_disjoint hwbr) hp hq).elim, (hfs hw hwbr.symm hq hp).elim]
  rcases hp with (((hp | hp) | hp) | hp) | hp
  · exact Or.inl (hfan hu (Or.inl rfl) huaq hubr hp)
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hstem hu huaq hubr hp))))
  · rcases hq with (((hq | hq) | hq) | hq) | hq
    · exact (Set.disjoint_left.1 (fan_bridge_disjoint ha _ _ _) hq hp).elim
    · exact Or.inr (Or.inl (bridge_stem_transverse ha hef huaq.symm hvaq.symm hp hq))
    · exact (Set.disjoint_left.1 (bridge_disjoint hef _ _ _ _) hp hq).elim
    · exact Or.inr (Or.inr (Or.inl (bridge_stem_transverse hb hef hubr.symm hvbr.symm hp hq)))
    · exact (Set.disjoint_left.1 (fan_bridge_disjoint hb _ _ _) hq hp).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inr (hstem hv hvaq hvbr hp))))
  · exact Or.inl (hfan hv (Or.inr rfl) hvaq hvbr hp)

end Cslib.Orthogonal.Layout
