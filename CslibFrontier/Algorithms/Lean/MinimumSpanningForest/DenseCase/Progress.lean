/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MinimumSpanningForest.DenseCase
import all CslibFrontier.Algorithms.Lean.MinimumSpanningForest.DenseCase
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# The progress of a bounded-frontier dense pass

In the analysis of [FredmanTarjan1987], §5, the first growth in each surviving component
overflows its priority queue. Later growths may attach to it. We follow the three stopping
conditions in the implementation to count the incident edge labels of every final component
that still has a neighbor. An edge internalized later in the pass still pays for its original
incidences. This yields the bound on the number of surviving components used in §2.3 of
[PettieRamachandran2002].
-/

public section

namespace Cslib.Multigraph.PettieRamachandran.DenseCase

open Finset PrimPartition.SearchState

variable {V E W : Type*} [DecidableEq V] [DecidableEq E] [LinearOrder W]
variable {ends : E → Sym2 V} {S : Finset E}

/-- Input edge labels incident to a particular output representative. -/
private def incident (q : V → V) (ends : E → Sym2 V) (S : Finset E) (z : V) : Finset E :=
  S.filter fun e => z ∈ (ends e).map q

/-- Each reached class is either finished or has strictly more incident edges than the cutoff. -/
private def settled (q : V → V) (ends : E → Sym2 V) (S : Finset E) (k : ℕ) (z : V) : Prop :=
  (∀ e ∈ incident q ends S z, ((ends e).map q).IsDiag) ∨ k < (incident q ends S z).card

omit [DecidableEq E] in
private theorem overflow (q : V → V) (C : Finset V) (z : V)
    (one : ∀ v ∈ C, q v = z) : (frontier ends S C).card ≤ (incident q ends S z).card := by
  classical
  let cut := (toGraph ends).edgeCut (C : Set V)
  let outside (e : E) := if h : e ∈ cut then (Graph.mem_edgeCut_iff.mp h).choose_spec.choose
    else z
  have subset : frontier ends S C ⊆ (incident q ends S z).image outside := by
    intro v hv
    obtain ⟨hun, fresh⟩ := mem_sdiff.mp hv
    obtain ⟨e, he, hv⟩ := mem_biUnion.mp hun
    obtain ⟨act, boundary⟩ := mem_filter.mp he
    have hcut : e ∈ cut := boundary
    let a := (Graph.mem_edgeCut_iff.mp hcut).choose
    let b := (Graph.mem_edgeCut_iff.mp hcut).choose_spec.choose
    have ⟨inc, ha, _⟩ := (Graph.mem_edgeCut_iff.mp hcut).choose_spec.choose_spec
    change ends e = s(a, b) at inc
    have mem : e ∈ incident q ends S z := mem_filter.mpr ⟨act, by simp [inc, one a ha]⟩
    rw [inc, Sym2.mem_toFinset, Sym2.mem_iff] at hv
    have eq := hv.resolve_left (fun eq => fresh (eq ▸ ha))
    exact mem_image.mpr ⟨e, mem, by simpa [outside, hcut, b] using eq.symm⟩
  exact (card_le_card subset).trans card_image_le

omit [DecidableEq E] in
private theorem settled_closed (q : V → V)
    (connected : ∀ x y, q x = q y → Joins ends S x y) {C : Finset V} {seed : V} (hs : seed ∈ C)
    (one : ∀ v ∈ C, q v = q seed)
    (closed : ¬∃ e ∈ S, e ∈ (toGraph ends).edgeCut (C : Set V)) (k : ℕ) :
    settled q ends S k (q seed) := by
  left
  have inside {x : V} (j : Joins ends S seed x) : x ∈ C :=
    by_contra fun h => closed (j.exists_mem_edgeCut (P := (C : Set V)) hs h)
  intro e he
  obtain ⟨heS, hz⟩ := mem_filter.mp he
  obtain ⟨x, hx, eq⟩ := Sym2.mem_map.mp hz
  let y := hx.other
  have inc : ends e = s(x, y) := (Sym2.other_spec hx).symm
  have path := connected _ _ eq.symm
  have hy := inside (path.trans (Joins.of_mem heS inc))
  simp [inc, eq, one y hy]

omit [DecidableEq E] in
private theorem no_cut_of_exhausted {C : Finset V} (hex : (support ends S \ C).card = 0) :
    ¬∃ e ∈ S, e ∈ (toGraph ends).edgeCut (C : Set V) := by
  rintro ⟨e, he, h⟩
  obtain ⟨a, b, hab, ha, hb⟩ := Graph.mem_edgeCut_iff.mp h
  change ends e = s(a, b) at hab
  have nd : a ≠ b := fun eq => hb (eq ▸ ha)
  have mem : b ∈ support ends S := mem_support.mpr
    ⟨e, he, by simpa [hab] using nd, by simp [hab]⟩
  exact (Nat.not_lt_zero _ ((Finset.card_pos.mpr ⟨b, mem_sdiff.mpr ⟨mem, hb⟩⟩).trans_le hex.le))

private def monoEdges (q : V → V) (ends : E → Sym2 V) (F : Finset E) : Prop :=
  ∀ f ∈ F, ((ends f).map q).IsDiag

private theorem grow_settled (q : V → V) (connected : ∀ x y, q x = q y → Joins ends S x y)
    (w : E → W) (k : ℕ) (marked : Finset V) (hm : ∀ v ∈ marked, settled q ends S k (q v))
    (fuel : ℕ) (C : Finset V) (seed : V) (hs : seed ∈ C) (one : ∀ v ∈ C, q v = q seed)
    (enough : (support ends S \ C).card ≤ fuel) :
    let r := grow ends S w k marked fuel C
    monoEdges q ends r.2 → (∀ v ∈ r.1, q v = q seed) ∧ settled q ends S k (q seed) := by
  dsimp only
  induction fuel generalizing C with
  | zero =>
    intro _
    exact ⟨one, settled_closed q connected hs one (no_cut_of_exhausted (by omega)) k⟩
  | succ fuel ih =>
    simp only [grow]
    split
    next big => exact fun _ => ⟨one, Or.inr (big.trans_le (overflow q C _ one))⟩
    next =>
      split
      next empty =>
        apply fun _ => And.intro one (settled_closed q connected hs one ?_ k)
        intro exit
        obtain ⟨x, hx⟩ := exists_minExit w exit
        simp [empty] at hx
      next x found =>
        split
        next dead =>
          intro monochrome
          have same : q x.inside = q x.outside := by
            simpa [x.inc] using monochrome x.edge (mem_singleton_self _)
          have eq := same.symm.trans (one _ x.left_mem)
          exact ⟨fun v hv => (mem_insert.mp hv).elim (fun h => h ▸ eq) (one _),
            eq ▸ hm _ dead⟩
        next =>
          intro monochrome
          have same : q x.inside = q x.outside := by
            simpa [x.inc] using monochrome x.edge (mem_insert_self ..)
          have eq := same.symm.trans (one _ x.left_mem)
          apply ih (insert x.outside C) (mem_insert_of_mem hs)
            (fun v hv => (mem_insert.mp hv).elim (fun h => h ▸ eq) (one _)) ?_
            (fun f hf => monochrome f (mem_insert_of_mem hf))
          have nd : x.inside ≠ x.outside := fun h => x.right_notMem (h ▸ x.left_mem)
          have mem : x.outside ∈ support ends S :=
            mem_support.mpr ⟨x.edge, x.active, by simpa [x.inc] using nd, by simp [x.inc]⟩
          have proper : (support ends S \ insert x.outside C) ⊂ (support ends S \ C) := by
            apply (ssubset_iff_of_subset (fun v hv => mem_sdiff.mpr
              ⟨(mem_sdiff.mp hv).1, fun h => (mem_sdiff.mp hv).2 (mem_insert_of_mem h)⟩)).mpr
            exact ⟨x.outside, mem_sdiff.mpr ⟨mem, x.right_notMem⟩,
              fun h => (mem_sdiff.mp h).2 (mem_insert_self ..)⟩
          have := card_lt_card proper
          omega

private theorem settle_seed (q : V → V) (conn : ∀ x y, q x = q y → Joins ends S x y)
    (w : E → W) (k : ℕ) (marked : Finset V) (hm : ∀ v ∈ marked, settled q ends S k (q v))
    (seed : V) :
    let r := grow ends S w k marked (support ends S).card {seed}
    monoEdges q ends r.2 → (∀ v ∈ r.1, q v = q seed) ∧ settled q ends S k (q seed) :=
  grow_settled q conn w k marked hm _ _ seed (mem_singleton_self _)
    (by simp) (card_le_card sdiff_subset)

private theorem scan_settled (q : V → V) (conn : ∀ x y, q x = q y → Joins ends S x y)
    (w : E → W) (k : ℕ) (marked : Finset V) (hm : ∀ v ∈ marked, settled q ends S k (q v))
    (vs : List V) (safe : monoEdges q ends (scan ends S w k (support ends S).card marked vs)) :
    ∀ v ∈ vs, settled q ends S k (q v) := by
  induction vs generalizing marked with
  | nil => simp
  | cons v vs ih =>
    by_cases already : v ∈ marked
    · rw [scan, ite_eq_left already] at safe
      exact List.forall_mem_cons.mpr ⟨hm v already, ih marked hm safe⟩
    · rw [scan, ite_eq_right already] at safe
      let r := grow ends S w k marked (support ends S).card {v}
      obtain ⟨same, good⟩ := settle_seed q conn w k marked hm v
        (fun e he => safe e (mem_union_left _ he))
      refine List.forall_mem_cons.mpr ⟨good, ih (marked ∪ r.1) ?_
        (fun e he => safe e (mem_union_right _ he))⟩
      intro u hu
      rcases mem_union.mp hu with old | new
      · exact hm u old
      · exact (same u new) ▸ good

private theorem phase_settled (m : ℕ) (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (h : (support ends S).Nonempty) :
    let q := contract ends (phase m ends S w h : Set E)
    ∀ v ∈ support ends S, settled q ends S (queueLimit m ends S h) (q v) := by
  classical
  let F := phase m ends S w h
  let q := contract ends (F : Set E)
  let k := queueLimit m ends S h
  let seed := firstSeed ends S h
  have ctx := (phase_subset_msf m ends S w h).trans (msf_subset w)
  have conn (u v : V) (eq : q u = q v) : Joins ends S u v :=
    (contract_eq_contract_iff.mp eq).mono (show (F : Set E) ⊆ S from ctx)
  have mono : monoEdges q ends F := by
    intro e he
    obtain ⟨a, b, inc⟩ : ∃ a b, ends e = s(a, b) :=
      Sym2.inductionOn (ends e) fun a b => ⟨a, b, rfl⟩
    have eq : q a = q b := contract_eq_contract_iff.mpr (Joins.of_mem he inc)
    simp [inc, eq]
  let r := grow ends S w k ∅ (support ends S).card {seed}
  obtain ⟨same, good⟩ := settle_seed q conn w k ∅ (by simp) seed
    (fun e he => mono e (mem_union_left _ he))
  change ∀ v ∈ support ends S, settled q ends S k (q v)
  intro v hv
  exact scan_settled q conn w k r.1 (fun u hu => (same u hu) ▸ good)
    (support ends S).toList (fun e he => mono e (mem_union_right _ he)) v (mem_toList.mpr hv)

/-- A pass whose queue bound is `k` leaves at most `2 |S| / (k+1)` non-isolated contracted
vertices. An incident input edge can occur in at most two of the final incidence sets. -/
theorem phase_vertex_bound (m : ℕ) (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (h : (support ends S).Nonempty) :
    let F := phase m ends S w h
    let after := Sym2.map (contract ends (F : Set E)) ∘ ends
    (support after (S \ F)).card * (queueLimit m ends S h + 1) ≤ 2 * S.card := by
  classical
  let F := phase m ends S w h
  let q := contract ends (F : Set E)
  let after := Sym2.map q ∘ ends
  let X := support after (S \ F)
  let k := queueLimit m ends S h
  have heavy (z : V) (hz : z ∈ X) : k + 1 ≤ (incident q ends S z).card := by
    obtain ⟨e, he, nd, inc⟩ := mem_support.mp hz
    obtain ⟨a, ha, rfl⟩ := Sym2.mem_map.mp inc
    have original : ¬(ends e).IsDiag := fun diag => nd diag.map
    have haS : a ∈ support ends S := mem_support.mpr ⟨e, (mem_sdiff.mp he).1, original, ha⟩
    rcases phase_settled m ends S w h a haS with done | weight
    · exact False.elim (nd (done e (mem_filter.mpr ⟨(mem_sdiff.mp he).1, inc⟩)))
    · exact weight
  calc
    X.card * (k + 1) = ∑ _z ∈ X, (k + 1) := by simp
    _ ≤ ∑ z ∈ X, (incident q ends S z).card := sum_le_sum heavy
    _ = ∑ e ∈ S, (X.filter fun z => z ∈ (ends e).map q).card := by
      simp only [incident, card_filter]
      exact sum_comm
    _ ≤ ∑ _e ∈ S, 2 := by
      apply sum_le_sum
      intro e _
      apply le_trans (card_le_card (t := ((ends e).map q).toFinset) ?_)
      · rw [Sym2.card_toFinset]
        split <;> decide
      · intro z hz
        exact Sym2.mem_toFinset.mpr (mem_filter.mp hz).2
    _ = 2 * S.card := by simp [Nat.mul_comm]

/-- The input to the dense solver after the specified number of its contraction passes.
An already finished graph stays fixed. The pair records endpoints and original edge labels. -/
noncomputable def afterPasses (m : ℕ) (w : E → W) (ends : E → Sym2 V) (S : Finset E) :
    ℕ → (E → Sym2 V) × Finset E
  | 0 => (ends, S)
  | n + 1 => by
    classical
    let G := afterPasses m w ends S n
    exact if h : (support G.1 G.2).Nonempty then
      let F := phase m G.1 G.2 w h
      (Sym2.map (contract G.1 (F : Set E)) ∘ G.1, G.2 \ F)
    else G

private theorem edges_afterPasses (m : ℕ) (w : E → W) (ends : E → Sym2 V) (S : Finset E)
    (n : ℕ) : (afterPasses m w ends S n).2 ⊆ S := by
  induction n with
  | zero => exact Subset.rfl
  | succ n ih =>
    rw [afterPasses]
    dsimp only
    split
    · exact sdiff_subset.trans ih
    · exact ih

private theorem square_le_pow (z : ℕ) : z * z ≤ 2 ^ (z + 1) := by
  induction z with
  | zero => decide
  | succ z ih =>
    rw [pow_succ]
    by_cases small : z ≤ 2
    · interval_cases z <;> decide
    · nlinarith [Nat.zero_le ((z - 1) * (z - 3)), Nat.sub_add_cancel (show 1 ≤ z by omega),
          Nat.sub_add_cancel (show 3 ≤ z by omega)]

/-- After contraction by a factor of the triple-logarithmic cutoff, four bounded-frontier
passes suffice. Here `N` is the original number of active vertices and `m` is a fixed upper
bound for the edge counts. The proof uses the integer density and the actual output of every
pass, also when a contraction removes parallel edges or produces loops. -/
theorem four_passes_suffice (N m : ℕ) (ends : E → Sym2 V) (S : Finset E) (w : E → W)
    (budget : S.card ≤ m) (vertices : N ≤ 2 * m)
    (dense : (support ends S).card * (N.log2.log2.log2 + 1) ≤ N) :
    let G := afterPasses m w ends S 4
    support G.1 G.2 = ∅ := by
  classical
  let G := afterPasses m w ends S
  let t (i : ℕ) := (support (G i).1 (G i).2).card
  let k (i : ℕ) := 2 ^ (2 * m / t i)
  have next (i : ℕ) : t (i + 1) * (k i + 1) ≤ 2 * m ∧ (t i = 0 → t (i + 1) = 0) := by
    let g := G i
    have edges := (card_le_card (edges_afterPasses m w ends S i)).trans budget
    change (support (G (i+1)).1 (G (i+1)).2).card * (k i+1) ≤ 2*m ∧ _
    by_cases h : (support g.1 g.2).Nonempty
    · have eq : G (i+1) =
          (Sym2.map (contract g.1 (phase m g.1 g.2 w h : Set E)) ∘ g.1,
            g.2 \ phase m g.1 g.2 w h) := by simp [G, afterPasses, g, h]
      have hphase := phase_vertex_bound m g.1 g.2 w h
      dsimp only at hphase
      rw [queueLimit_eq m _ _ h edges] at hphase
      refine ⟨by rw [eq]; exact hphase.trans (Nat.mul_le_mul_left 2 edges), ?_⟩
      exact fun zero => False.elim ((card_pos.mpr h).ne' zero)
    · have eq : G (i+1) = g := by simp [G, afterPasses, g, h]
      have z : t (i+1) = 0 := by
        change (support (G (i+1)).1 (G (i+1)).2).card = 0
        rw [eq, not_nonempty_iff_eq_empty.mp h]
        rfl
      exact ⟨by change t (i+1) * _ ≤ _; simp [z], fun _ => z⟩
  suffices t 4 = 0 from card_eq_zero.mp this
  by_contra nonzero
  have back (i : ℕ) (pos : 0 < t (i+1)) : 0 < t i := by
    by_contra! zero
    exact pos.ne' ((next i).2 (by omega))
  have p4 : 0 < t 4 := Nat.pos_of_ne_zero nonzero
  have p3 := back 3 p4
  have p2 := back 2 p3
  have p1 := back 1 p2
  have p0 := back 0 p1
  have grows (i : ℕ) (pos : 0 < t (i+1)) : 2 ^ (k i + 1) ≤ k (i+1) :=
    Nat.pow_le_pow_right (by decide) ((Nat.le_div_iff_mul_le pos).mpr
      (by simpa [Nat.mul_comm] using (next i).1))
  have start : N.log2.log2.log2 + 1 ≤ 2*m / t 0 :=
    (Nat.le_div_iff_mul_le p0).mpr (by simpa [t, G, afterPasses, Nat.mul_comm] using
      (dense.trans vertices))
  have tower : N < k 2 := by
    apply Nat.lt_pow_of_log_lt (by decide : 1 < 2)
    have floor : k 1 + 1 ≤ 2*m / t 2 := (Nat.le_div_iff_mul_le p2).mpr
      (by simpa [Nat.mul_comm] using (next 1).1)
    apply lt_of_lt_of_le _ floor
    apply Nat.lt_succ_of_le
    apply le_trans _ (grows 0 p1)
    apply le_of_lt
    apply Nat.lt_pow_of_log_lt (by decide : 1 < 2)
    apply Nat.lt_succ_of_le
    change _ ≤ 2 ^ (2 * m / t 0)
    apply Nat.le_of_lt
    apply Nat.lt_pow_of_log_lt (by decide : 1 < 2)
    simpa only [Nat.log2_eq_log_two] using (Nat.lt_of_succ_le start)
  have nt : t 0 ≤ N :=
    (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)).trans dense
  have first : 2*m / t 0 + 1 ≤ k 2 := by
    have h01 := grows 0 p1
    have h12 := grows 1 p2
    have ha : 2*m / t 0 < k 0 := Nat.lt_two_pow_self
    have hb : k 0 + 1 ≤ 2^(k 0 + 1) := Nat.lt_two_pow_self.le
    have hc : k 1 + 1 ≤ 2^(k 1 + 1) := Nat.lt_two_pow_self.le
    exact (Nat.succ_le_of_lt ha).trans ((Nat.le_succ _).trans (hb.trans (h01.trans
      ((Nat.le_succ _).trans (hc.trans h12)))))
  have lt : 2*m < (2*m / t 0 + 1) * t 0 := by
    rw [Nat.mul_comm (2*m / t 0 + 1)]
    exact Nat.lt_mul_div_succ _ p0
  have last := calc
    2*m < (2*m / t 0 + 1) * t 0 := lt
    _ ≤ k 2 * k 2 := Nat.mul_le_mul first (nt.trans tower.le)
    _ ≤ 2^(k 2 + 1) := square_le_pow _
    _ ≤ k 3 := grows 2 p3
  have bound := (next 3).1
  have lower := Nat.le_mul_of_pos_left (k 3 + 1) p4
  exact (Nat.not_lt_of_ge (lower.trans bound)) (last.trans (Nat.lt_succ_self _))

end Cslib.Multigraph.PettieRamachandran.DenseCase
