/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpace
import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CycleSpaceConverse
import CslibFrontier.Foundations.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

/-!
# Clockwise dart colors for actual face boundaries

A face coloring gives the color at the clockwise corner following a dart by reading the
face of its reverse. With the existing `faceNext = rotate⁻¹ ∘ reverse`, these colors satisfy
`P (rotate d) = P d.reverse`. The reversal is essential: reading the face of `d` directly
would give the opposite recurrence. Conversely this recurrence descends to actual face colors.
The existing cycle-space converse then gives a numerical genus criterion in these coordinates.
`color_ends_eq_of_dart_path` sums route transport along consecutive darts, and
`color_sum_eq_true_iff_inverse_rotate_of_three_darts` reads the order at a degree-three vertex.
`inverse_rotate_iff_not_inverse_rotate_of_three_paths` compares the two orders of three arms.
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- The actual face color at the clockwise corner following an indexed dart. -/
@[expose] def faceDartColor (q : r.Face → Bool) (d : Dart G) : Bool :=
  q (Quotient.mk _ d.reverse)

/-- Positive vertex rotation moves to the clockwise color at the reverse dart. -/
theorem faceDartColor_rotate (q : r.Face → Bool) (d : Dart G) :
    r.faceDartColor q (r.rotate d) = r.faceDartColor q d.reverse := by
  have h := congrArg q (r.face_eq_next ((r.rotate d).reverse))
  have hnext : r.faceNext (r.rotate d).reverse = d := by
    unfold faceNext
    change r.rotate.symm (r.rotate d).reverse.reverse = d
    rw [Dart.reverse_reverse, r.rotate.symm_apply_apply]
  rw [hnext] at h
  simpa only [faceDartColor, Dart.reverse_reverse] using h.symm

/-- The colors at the two indexed ends recover the original face-boundary edge bit. -/
theorem faceDartColor_xor_reverse (q : r.Face → Bool) (d : Dart G) :
    (r.faceDartColor q d ^^ r.faceDartColor q d.reverse) = r.faceBoundary q d.1 := by
  rw [r.faceBoundary_dart]
  simp only [faceDartColor, Dart.reverse_reverse]
  exact Bool.xor_comm _ _

/-- Clockwise dart colors satisfying the actual rotation recurrence descend to face colors,
with exactly the same edge boundary. No genus, connectedness or degree premise is needed. -/
theorem exists_faceColors_of_dartColors (x : Fin G.edges.length → Bool)
    (P : Dart G → Bool) (hP : ∀ d, P (r.rotate d) = P d.reverse)
    (hx : ∀ d, (P d ^^ P d.reverse) = x d.1) :
    ∃ q : r.Face → Bool, r.faceBoundary q = x := by
  let Q : Dart G → Bool := fun d => P d.reverse
  have hQ : Function.Semiconj Q r.faceNext (1 : Equiv.Perm Bool) := by
    intro d
    have h := hP (r.faceNext d)
    have he : r.rotate (r.faceNext d) = d.reverse :=
      r.rotate.apply_symm_apply d.reverse
    rw [he] at h
    exact h.symm
  let q : r.Face → Bool := Quotient.lift Q fun d e he =>
    Equiv.Perm.sameCycle_one.mp (he.map_of_semiconj hQ)
  refine ⟨q, funext fun i => ?_⟩
  change (P (i, true) ^^ P (i, false)) = x i
  exact hx (i, true)

/-- Face boundaries are exactly the edge labels obtained from compatible clockwise dart
colors. This equivalence requires neither genus zero nor any endpoint declaration premise. -/
theorem exists_faceColors_iff_exists_dartColors (x : Fin G.edges.length → Bool) :
    (∃ q : r.Face → Bool, r.faceBoundary q = x) ↔
      ∃ P : Dart G → Bool, (∀ d, P (r.rotate d) = P d.reverse) ∧
        ∀ d, (P d ^^ P d.reverse) = x d.1 := by
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨r.faceDartColor q, r.faceDartColor_rotate q, r.faceDartColor_xor_reverse q⟩
  · rintro ⟨P, hP, hx⟩
    exact r.exists_faceColors_of_dartColors x P hP hx

/-- The existing componentwise numerical genus criterion in explicit clockwise coordinates.
Applications must construct the colors from each actual vertex-even edge labeling. -/
theorem numericalGenusZero_of_vertexEven_dartColors
    (hG : ∀ v ∈ G.incidenceVertices, v ∈ G.vertices)
    (hcolor : ∀ x : Fin G.edges.length → Bool, G.VertexEven x →
      ∃ P : Dart G → Bool, (∀ d, P (r.rotate d) = P d.reverse) ∧
        ∀ d, (P d ^^ P d.reverse) = x d.1) : r.NumericalGenusZero := by
  apply r.numericalGenusZero_of_vertexEven_faceBoundary hG
  intro x hx
  obtain ⟨P, hP, he⟩ := hcolor x hx
  exact r.exists_faceColors_of_dartColors x P hP he

/-- Along a nonempty path of consecutive darts, the sum of its endpoint colors is the
last edge label plus the sum of all route contributions. Each internal turn follows the
inverse vertex rotation, as it does at the internal vertices of a degree-two path. -/
theorem color_ends_eq_of_dart_path {n : ℕ} (path : Fin (n + 1) → Dart G)
    (color : Dart G → Bool) (label crossing : Fin G.edges.length → Bool)
    (hstep : ∀ i : Fin n, r.rotate.symm (path i.castSucc).reverse = path i.succ)
    (hedge : ∀ d, color d + color d.reverse = label d.1 + crossing d.1)
    (hsector : ∀ d, color d + color (r.rotate.symm d) = label d.1) :
    color (path 0) + color (path (Fin.last n)).reverse =
      label (path (Fin.last n)).1 + ∑ i, crossing (path i).1 := by
  let entry (i : Fin (n + 1)) := color (path i)
  let exit (i : Fin (n + 1)) := color (path i).reverse
  have across (i : Fin (n + 1)) :
      exit i - entry i = label (path i).1 + crossing (path i).1 := by
    rw [BooleanRing.sub_eq_add, add_comm]
    exact hedge (path i)
  have turn (i : Fin n) : entry i.succ - exit i.castSucc = label (path i.castSucc).1 := by
    rw [BooleanRing.sub_eq_add, add_comm]
    have h := hsector (path i.castSucc).reverse
    rw [hstep i] at h
    exact h
  have telescope := Fin.sum_univ_adjacent_differences entry exit
  simp_rw [across, turn] at telescope
  rw [Finset.sum_add_distrib, Fin.sum_univ_castSucc (fun i => label (path i).1)] at telescope
  calc
    _ = exit (Fin.last n) - entry 0 := by rw [BooleanRing.sub_eq_add, add_comm]
    _ = _ := by
      rw [← telescope]
      generalize (∑ i : Fin n, label (path i.castSucc).1) = s
      calc
        _ = (label (path (Fin.last n)).1 + ∑ i, crossing (path i).1) + (s + s) := by ac_rfl
        _ = _ := by rw [BooleanRing.add_self, add_zero]

/-- At a vertex with exactly the given three darts, a selected dart followed by an
unselected dart in counterclockwise order is detected by their clockwise-side colors.
The two other positions are distinguished using the actual vertex permutation. -/
theorem color_sum_eq_true_iff_inverse_rotate_of_three_darts
    (color : Dart G → Bool) (label : Fin G.edges.length → Bool)
    (hsector : ∀ d, color d + color (r.rotate.symm d) = label d.1)
    (a b c : Dart G) (hab : a.vertex = b.vertex) (hac : a.vertex = c.vertex)
    (hab' : a ≠ b) (hac' : a ≠ c) (hbc : b ≠ c)
    (hall : ∀ d, d.vertex = a.vertex → d = a ∨ d = b ∨ d = c)
    (ha : label a.1 = true) (hc : label c.1 = false) :
    color a + color c = true ↔ r.rotate.symm a = c := by
  have vertex (d : Dart G) : (r.rotate.symm d).vertex = d.vertex := by
    rw [← r.vertex_rotate (r.rotate.symm d), r.rotate.apply_symm_apply]
  have not_fixed (d f : Dart G) (hv : f.vertex = d.vertex) (hne : f ≠ d) :
      r.rotate.symm d ≠ d := by
    intro h
    have heq := congrArg r.rotate h
    rw [r.rotate.apply_symm_apply] at heq
    exact hne (((r.sameCycle_iff f d).mpr hv).eq_of_right heq.symm)
  by_cases h : r.rotate.symm a = c
  · exact ⟨fun _ => h, fun _ => by simpa only [h, ha] using hsector a⟩
  · have habNext : r.rotate.symm a = b :=
      ((hall _ (vertex a)).resolve_left (not_fixed a b hab.symm hab'.symm)).resolve_right h
    have hcNext : r.rotate.symm c = a := by
      rcases hall _ ((vertex c).trans hac.symm) with he | he | he
      · exact he
      · exact (hac' (r.rotate.symm.injective (habNext.trans he.symm))).elim
      · exact (not_fixed c b (hab.symm.trans hac) hbc he).elim
    have hzero : color a + color c = false := by
      rw [add_comm]
      simpa only [hcNext, hc] using hsector c
    simp [hzero, h]

/-- The order comparison for three nonempty dart paths following the inverse rotation at
their internal joints. The two port equivalences enumerate the paths in the same order.
The first two arms are selected, so the crossing contributions within the first arm
cancel in pairs. Even crossings between distinct arms make the third arm's total zero.
This is the dart-color step for the opposite-orders assertion of Claim B in
[FulekKynclPalvolgyi2017], §3. Its hypotheses are algebraic, with dart colors supplied. -/
theorem inverse_rotate_iff_not_inverse_rotate_of_three_paths {u v : ℕ}
    {length : Fin 3 → ℕ} (path : ∀ k, Fin (length k + 1) → Dart G)
    (start : Fin 3 ≃ {d : Dart G // d.vertex = u})
    (finish : Fin 3 ≃ {d : Dart G // d.vertex = v})
    (hstart : ∀ k, (start k).val = path k 0)
    (hfinish : ∀ k, (finish k).val = (path k (Fin.last (length k))).reverse)
    (hstep : ∀ k (i : Fin (length k)), r.rotate.symm (path k i.castSucc).reverse = path k i.succ)
    (hfirst : Function.Injective fun i => (path 0 i).1)
    (color : Dart G → Bool) (label : Fin G.edges.length → Bool)
    (hlabel : ∀ e, label e = true ↔ ∃ k : Fin 3, k ≠ 2 ∧ ∃ i, (path k i).1 = e)
    (hlast : ∀ i, label (path 2 i).1 = false)
    (crosses : Fin G.edges.length → Fin G.edges.length → Bool)
    (hsymm : ∀ e f, crosses e f = crosses f e) (hdiag : ∀ e, crosses e e = 0)
    (hcross : ∀ (a b : Fin 3), a ≠ b → ∀ i j, crosses (path a i).1 (path b j).1 = 0)
    (hedge : ∀ d, color d + color d.reverse = label d.1 + ∑ f, label f * crosses f d.1)
    (hsector : ∀ d, color d + color (r.rotate.symm d) = label d.1) :
    r.rotate.symm (start 0).val = (start 2).val ↔
      r.rotate.symm (finish 0).val ≠ (finish 2).val := by
  classical
  let firstEdge : Fin (length 0 + 1) ↪ Fin G.edges.length := ⟨fun i => (path 0 i).1, hfirst⟩
  let firstEdges := Finset.univ.map firstEdge
  let contribution (e : Fin G.edges.length) := ∑ f, label f * crosses f e
  have firstLabel (i : Fin (length 0 + 1)) : label (firstEdge i) = true :=
    (hlabel _).mpr ⟨0, by decide, i, rfl⟩
  have firstRow (i : Fin (length 0 + 1)) :
      contribution (firstEdge i) = ∑ j, crosses (firstEdge j) (firstEdge i) := by
    have outside (f : Fin G.edges.length) (hf : f ∉ firstEdges) :
        label f * crosses f (firstEdge i) = 0 := by
      cases hbit : label f
      · simp [← Bool.zero_eq_false]
      · obtain ⟨k, _, j, rfl⟩ := (hlabel _).mp hbit
        have hk : k ≠ 0 := by
          rintro rfl
          exact hf (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
        change true * crosses (path k j).1 (path 0 i).1 = 0
        rw [hcross k 0 hk j i, mul_zero]
    rw [show contribution (firstEdge i) = ∑ f, label f * crosses f (firstEdge i) from rfl,
      ← Finset.sum_subset (Finset.subset_univ firstEdges) (fun f _ => outside f)]
    simp [firstEdges, Finset.sum_map, firstLabel, ← Bool.one_eq_true]
  have firstTotal : (∑ i, contribution (firstEdge i)) = 0 := by
    simp_rw [firstRow]
    rw [← Fintype.sum_prod_type (fun a : Fin (length 0 + 1) × Fin (length 0 + 1) =>
      crosses (firstEdge a.2) (firstEdge a.1))]
    refine Finset.sum_ninvolution Prod.swap ?_ ?_ (fun _ => Finset.mem_univ _) Prod.swap_swap
    · intro a
      change crosses (firstEdge a.2) (firstEdge a.1) +
        crosses (firstEdge a.1) (firstEdge a.2) = 0
      rw [hsymm (firstEdge a.2) (firstEdge a.1), BooleanRing.add_self]
    · rintro ⟨i, j⟩ hne he
      have hij : j = i := congrArg Prod.fst he
      exact hne (hij ▸ hdiag (firstEdge i))
  have lastRow (i : Fin (length 2 + 1)) : contribution (path 2 i).1 = 0 := by
    apply Finset.sum_eq_zero
    intro f _
    cases hbit : label f
    · simp [← Bool.zero_eq_false]
    · obtain ⟨k, hk, j, rfl⟩ := (hlabel _).mp hbit
      rw [hcross k 2 hk j i, mul_zero]
  have firstEnds := r.color_ends_eq_of_dart_path (path 0) color label contribution
    (hstep 0) hedge hsector
  change _ = label (firstEdge (Fin.last (length 0))) + ∑ i, contribution (firstEdge i)
    at firstEnds
  rw [firstLabel, firstTotal, add_zero] at firstEnds
  have lastEnds := r.color_ends_eq_of_dart_path (path 2) color label contribution
    (hstep 2) hedge hsector
  simp only [hlast, lastRow, Finset.sum_const_zero, add_zero] at lastEnds
  have order {w : ℕ} (ports : Fin 3 ≃ {d : Dart G // d.vertex = w})
      (h0 : label (ports 0).val.1 = true) (h2 : label (ports 2).val.1 = false) :
      color (ports 0).val + color (ports 2).val = true ↔
        r.rotate.symm (ports 0).val = (ports 2).val := by
    have distinct {a b : Fin 3} (hne : a ≠ b) :
        (ports a).val ≠ (ports b).val :=
      fun he => hne (ports.injective (Subtype.ext he))
    refine r.color_sum_eq_true_iff_inverse_rotate_of_three_darts color label hsector
      (ports 0).val (ports 1).val (ports 2).val
      ((ports 0).property.trans (ports 1).property.symm)
      ((ports 0).property.trans (ports 2).property.symm)
      (distinct (by decide)) (distinct (by decide)) (distinct (by decide)) ?_ h0 h2
    intro d hd
    obtain ⟨k, hk⟩ := ports.surjective ⟨d, hd.trans (ports 0).property⟩
    have he := congrArg Subtype.val hk.symm
    fin_cases k
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  have startOrder := order start (by rw [hstart]; exact firstLabel _)
    (by rw [hstart]; exact hlast _)
  have finishOrder := order finish (by rw [hfinish]; exact firstLabel _)
    (by rw [hfinish]; exact hlast _)
  have opposite : ∀ p q s t : Bool, p + q = true → s + t = false →
      (p + s = true ↔ q + t ≠ true) := by decide
  have colorsOpposite : color (start 0).val + color (start 2).val = true ↔
      color (finish 0).val + color (finish 2).val ≠ true := by
    rw [hstart 0, hstart 2, hfinish 0, hfinish 2]
    exact opposite _ _ _ _ firstEnds lastEnds
  exact startOrder.symm.trans (colorsOpposite.trans finishOrder.not)

end Cslib.Complexity.Graph.RotationSystem
