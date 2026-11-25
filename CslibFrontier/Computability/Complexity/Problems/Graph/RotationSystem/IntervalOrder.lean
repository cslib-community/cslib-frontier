/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity
import Mathlib.Data.Finset.Max
import Mathlib.Dynamics.PeriodicPts.Lemmas
import CslibFrontier.Tactic.LRATTauto

/-!
# Linear ranks and literal directed rotation intervals

Cutting a finite vertex cycle at any one of its darts gives first-hit ranks. These ranks
retain the direction of the supplied rotation, without a geometric realization or any
restriction on the graph's loops or components.

* `Cslib.Complexity.Graph.RotationSystem.exists_consecutive_class_of_no_alternates` finds a
  class that forms a consecutive interval when distinct classes do not alternate.
* `Cslib.Complexity.Graph.RotationSystem.rotationDistance_le_iff_portRank_between` turns an
  inclusive interval of linear ranks into an interval of first-hit distances.

These support the cut-vertex argument in Claim A of [FulekKynclPalvolgyi2017], §3,
tracked in [issue #3091](https://github.com/cslib-community/cslib-frontier/issues/3091).
-/

public section

namespace Cslib.Complexity.Graph.RotationSystem

variable {G : Graph} (r : RotationSystem G)

/-- First-hit distance is bounded by any successful forward iterate. -/
theorem rotationDistance_le {a b : Dart G} (hab : a.vertex = b.vertex) {n : ℕ}
    (hn : (r.rotate ^ n) a = b) : r.rotationDistance a b ≤ n := by
  classical
  rw [rotationDistance, dite_eq_left ((r.sameCycle_iff a b).mpr hab)]
  exact Nat.find_min' _ hn

private theorem period_pos (a : Dart G) : 0 < Function.minimalPeriod r.rotate a :=
  Function.minimalPeriod_pos_of_mem_periodicPts (r.rotate.injective.mem_periodicPts a)

/-- First-hit ranks fit in one complete vertex cycle, including singleton cycles. -/
theorem rotationDistance_lt_period {a b : Dart G} (hab : a.vertex = b.vertex) :
    r.rotationDistance a b < Function.minimalPeriod r.rotate a := by
  have hm : (r.rotate ^ (r.rotationDistance a b % Function.minimalPeriod r.rotate a)) a = b := by
    rw [← r.rotate.iterate_eq_pow, Function.iterate_mod_minimalPeriod_eq,
      r.rotate.iterate_eq_pow]
    exact r.pow_rotationDistance a b hab
  exact (r.rotationDistance_le hab hm).trans_lt (Nat.mod_lt _ (r.period_pos a))

/-- First-hit ranks from a common origin distinguish darts on that vertex cycle. -/
theorem rotationDistance_eq_iff_eq (o a b : Dart G) (hoa : o.vertex = a.vertex)
    (hob : o.vertex = b.vertex) :
    r.rotationDistance o a = r.rotationDistance o b ↔ a = b := by
  refine ⟨fun h => ?_, fun h => congrArg _ h⟩
  rw [← r.pow_rotationDistance o a hoa, ← r.pow_rotationDistance o b hob, h]

/-- The rank of a forward iterate is its exponent reduced modulo the vertex period. -/
theorem rotationDistance_pow (o : Dart G) (k : ℕ) :
    r.rotationDistance o ((r.rotate ^ k) o) = k % Function.minimalPeriod r.rotate o := by
  have hv : o.vertex = ((r.rotate ^ k) o).vertex :=
    (r.sameCycle_iff _ _).mp (Equiv.Perm.sameCycle_pow_right.mpr .rfl)
  apply r.rotationDistance_eq _ _ hv
  · rw [← r.rotate.iterate_eq_pow, Function.iterate_mod_minimalPeriod_eq,
      r.rotate.iterate_eq_pow]
  · intro j hj heq
    have hlt := Nat.mod_lt k (r.period_pos o)
    have hiter : (r.rotate^[j]) o = (r.rotate^[k % Function.minimalPeriod r.rotate o]) o := by
      rw [r.rotate.iterate_eq_pow, heq, ← r.rotate.iterate_eq_pow,
        Function.iterate_mod_minimalPeriod_eq]
    have := (Function.iterate_eq_iterate_iff_of_lt_minimalPeriod (hj.trans hlt) hlt).mp hiter
    omega

/-- Forward rotation adds to a rank modulo the same vertex period. -/
theorem rotationDistance_pow_from (o a : Dart G) (hoa : o.vertex = a.vertex) (k : ℕ) :
    r.rotationDistance o ((r.rotate ^ k) a) =
      (r.rotationDistance o a + k) % Function.minimalPeriod r.rotate o := by
  calc
    _ = r.rotationDistance o ((r.rotate ^ (r.rotationDistance o a + k)) o) := by
      rw [Nat.add_comm (r.rotationDistance o a) k, pow_add, Equiv.Perm.mul_apply,
        r.pow_rotationDistance o a hoa]
    _ = _ := r.rotationDistance_pow _ _

private theorem period_eq (o a : Dart G) (hoa : o.vertex = a.vertex) :
    Function.minimalPeriod r.rotate a = Function.minimalPeriod r.rotate o := by
  have h := Function.minimalPeriod_apply_iterate (r.rotate.injective.mem_periodicPts o)
    (r.rotationDistance o a)
  simpa only [r.rotate.iterate_eq_pow, r.pow_rotationDistance o a hoa] using h

private theorem add_mod_eq_iff {a b c n : ℕ} (ha : a < n) (hb : b < n) (hc : c < n) :
    (a + b) % n = c ↔ a + b = c ∨ a + b = c + n := by
  by_cases h : a + b < n
  · rw [Nat.mod_eq_of_lt h]
    omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    omega

/-- The actual directed rotation interval is the cyclic order of first-hit ranks at
any chosen cut. All three darts must be distinct and belong to that vertex cycle. -/
theorem mem_rotationInterval_iff_ranks (o a b c : Dart G)
    (hoa : o.vertex = a.vertex) (hob : o.vertex = b.vertex) (hoc : o.vertex = c.vertex)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔
      (r.rotationDistance o a < r.rotationDistance o b ∧
        r.rotationDistance o b < r.rotationDistance o c) ∨
      (r.rotationDistance o b < r.rotationDistance o c ∧
        r.rotationDistance o c < r.rotationDistance o a) ∨
      (r.rotationDistance o c < r.rotationDistance o a ∧
        r.rotationDistance o a < r.rotationDistance o b) := by
  classical
  let n := Function.minimalPeriod r.rotate o
  let ra := r.rotationDistance o a
  let rb := r.rotationDistance o b
  let rc := r.rotationDistance o c
  let dist := r.rotationDistance a c
  have ha : ra < n := r.rotationDistance_lt_period hoa
  have hb : rb < n := r.rotationDistance_lt_period hob
  have hc : rc < n := r.rotationDistance_lt_period hoc
  have hd : dist < n := by
    have h := r.rotationDistance_lt_period (hoa.symm.trans hoc)
    rwa [r.period_eq o a hoa] at h
  have hneab : ra ≠ rb := fun h => hab ((r.rotationDistance_eq_iff_eq o a b hoa hob).mp h)
  have hnebc : rb ≠ rc := fun h => hbc ((r.rotationDistance_eq_iff_eq o b c hob hoc).mp h)
  have hneac : ra ≠ rc := fun h => hac ((r.rotationDistance_eq_iff_eq o a c hoa hoc).mp h)
  have hdist : ra + dist = rc ∨ ra + dist = rc + n := by
    apply (add_mod_eq_iff ha hd hc).mp
    have h := r.rotationDistance_pow_from o a hoa dist
    rw [r.pow_rotationDistance a c (hoa.symm.trans hoc)] at h
    exact h.symm
  have pow_iff (k : ℕ) : (r.rotate ^ k) a = b ↔ (ra + k) % n = rb := by
    have hv : o.vertex = ((r.rotate ^ k) a).vertex :=
      hoa.trans ((r.sameCycle_iff _ _).mp
        (Equiv.Perm.sameCycle_pow_right.mpr .rfl))
    rw [← r.rotationDistance_eq_iff_eq o _ b hv hob, r.rotationDistance_pow_from o a hoa]
  constructor
  · intro hmem
    obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp hmem
    have hk' : k < dist := Finset.mem_range.mp hk
    have hsum := (add_mod_eq_iff ha (show k + 1 < n by omega) hb).mp
      ((pow_iff (k + 1)).mp heq)
    change (ra < rb ∧ rb < rc) ∨ (rb < rc ∧ rc < ra) ∨ (rc < ra ∧ ra < rb)
    omega
  · intro horder
    change (ra < rb ∧ rb < rc) ∨ (rb < rc ∧ rc < ra) ∨ (rc < ra ∧ ra < rb) at horder
    let m := if ra < rb then rb - ra else rb + n - ra
    have hm_pos : 0 < m := by dsimp [m]; split_ifs <;> omega
    have hm_le : m ≤ dist := by dsimp [m]; split_ifs <;> omega
    refine Finset.mem_image.mpr ⟨m - 1, Finset.mem_range.mpr (by omega), (pow_iff _).mpr ?_⟩
    rw [Nat.sub_add_cancel hm_pos]
    exact (add_mod_eq_iff ha (by omega) hb).mpr (by dsimp [m]; split_ifs <;> omega)

private noncomputable def vertexDart (v : ℕ) (h : ∃ d : Dart G, d.vertex = v) : Dart G :=
  Classical.choose h

/-- A zero-based linear rank of an incident dart, cutting each literal vertex cycle at
one classically chosen dart. Different indexed ends, including loop ends, remain distinct. -/
noncomputable def portRank (d : Dart G) : ℕ :=
  r.rotationDistance (vertexDart d.vertex ⟨d, rfl⟩) d

private theorem portRank_at (a d : Dart G) (had : a.vertex = d.vertex) :
    r.portRank d = r.rotationDistance (vertexDart a.vertex ⟨a, rfl⟩) d := by
  simp only [portRank, ← had]

/-- Ranks distinguish every actual dart at a vertex. -/
theorem portRank_injective (a b : Dart G) (hab : a.vertex = b.vertex)
    (heq : r.portRank a = r.portRank b) : a = b := by
  let o := vertexDart a.vertex ⟨a, rfl⟩
  have hoa : o.vertex = a.vertex := Classical.choose_spec (show ∃ d : Dart G,
    d.vertex = a.vertex from ⟨a, rfl⟩)
  rw [r.portRank_at a a rfl, r.portRank_at a b hab] at heq
  exact (r.rotationDistance_eq_iff_eq o a b hoa (hoa.trans hab)).mp heq

/-- The chosen linear ranks retain the supplied clockwise cyclic interval. -/
theorem mem_rotationInterval_iff_portRank (a b c : Dart G)
    (hab : a.vertex = b.vertex) (hbc : b.vertex = c.vertex)
    (hneab : a ≠ b) (hnebc : b ≠ c) (hneac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔
      (r.portRank a < r.portRank b ∧ r.portRank b < r.portRank c) ∨
      (r.portRank b < r.portRank c ∧ r.portRank c < r.portRank a) ∨
      (r.portRank c < r.portRank a ∧ r.portRank a < r.portRank b) := by
  let o := vertexDart a.vertex ⟨a, rfl⟩
  have hoa : o.vertex = a.vertex := Classical.choose_spec (show ∃ d : Dart G,
    d.vertex = a.vertex from ⟨a, rfl⟩)
  rw [r.portRank_at a a rfl, r.portRank_at a b hab, r.portRank_at a c (hab.trans hbc)]
  exact r.mem_rotationInterval_iff_ranks o a b c hoa (hoa.trans hab)
    (hoa.trans (hab.trans hbc)) hneab hnebc hneac

/-- If no two distinct color classes alternate at a vertex, some nonempty class forms
a consecutive interval in the linear ranks cut from its clockwise rotation.
This is the order-theoretic step in Claim A of [FulekKynclPalvolgyi2017], §3. -/
theorem exists_consecutive_class_of_no_alternates {ι : Type*} (color : Dart G → ι) {v : ℕ}
    (hv : ∃ a : Dart G, a.vertex = v)
    (hnonalt : ∀ a b c d : Dart G, a.vertex = v → color a = color b → color c = color d →
      color a ≠ color c → ¬r.Alternates a b c d) :
    ∃ a b : Dart G, a.vertex = v ∧ b.vertex = v ∧ color a = color b ∧
      ∀ d : Dart G, d.vertex = v →
        (color d = color a ↔ r.portRank a ≤ r.portRank d ∧ r.portRank d ≤ r.portRank b) := by
  classical
  let covers (a b : Dart G) : Prop :=
    a.vertex = v ∧ b.vertex = v ∧ color a = color b ∧
      ∀ d : Dart G, d.vertex = v → color d = color a →
        r.portRank a ≤ r.portRank d ∧ r.portRank d ≤ r.portRank b
  have classBounds (w : Dart G) (hw : w.vertex = v) :
      ∃ a b, covers a b ∧ color a = color w := by
    let S := Finset.univ.filter fun d : Dart G => d.vertex = v ∧ color d = color w
    have hmem (d : Dart G) : d ∈ S ↔ d.vertex = v ∧ color d = color w := by simp [S]
    have hne : S.Nonempty := ⟨w, (hmem w).mpr ⟨hw, rfl⟩⟩
    obtain ⟨a, has, hmin⟩ := S.exists_min_image r.portRank hne
    obtain ⟨b, hbs, hmax⟩ := S.exists_max_image r.portRank hne
    obtain ⟨ha, hac⟩ := (hmem a).mp has
    obtain ⟨hb, hbc⟩ := (hmem b).mp hbs
    refine ⟨a, b, ⟨ha, hb, hac.trans hbc.symm, ?_⟩, hac⟩
    intro d hd hc
    have hds := (hmem d).mpr ⟨hd, hc.trans hac⟩
    exact ⟨hmin d hds, hmax d hds⟩
  have hex : ∃ n : ℕ, ∃ a b, covers a b ∧ r.portRank b - r.portRank a = n := by
    obtain ⟨w, hw⟩ := hv
    obtain ⟨a, b, hab, _⟩ := classBounds w hw
    exact ⟨_, a, b, hab, rfl⟩
  obtain ⟨a, b, hbounds, hwidth⟩ := Nat.find_spec hex
  obtain ⟨ha, hb, hab, hcover⟩ := hbounds
  refine ⟨a, b, ha, hb, hab, fun z hz => ⟨hcover z hz, ?_⟩⟩
  intro hzspan
  by_contra hza
  have hnA (d : Dart G) (hd : d.vertex = v) (hc : color d ≠ color a) :
      r.portRank d ≠ r.portRank a :=
    fun h => hc (congrArg color (r.portRank_injective d a (hd.trans ha.symm) h))
  have hnB (d : Dart G) (hd : d.vertex = v) (hc : color d ≠ color a) :
      r.portRank d ≠ r.portRank b :=
    fun h => hc ((congrArg color (r.portRank_injective d b (hd.trans hb.symm) h)).trans hab.symm)
  have hzi : r.portRank a < r.portRank z ∧ r.portRank z < r.portRank b := by
    have := hnA z hz hza
    have := hnB z hz hza
    omega
  have inside (d : Dart G) (hd : d.vertex = v) (hc : color d = color z) :
      r.portRank a < r.portRank d ∧ r.portRank d < r.portRank b := by
    by_contra hn
    have hda : color d ≠ color a := fun h => hza (hc.symm.trans h)
    have hA := hnA d hd hda
    have hB := hnB d hd hda
    have hout : r.portRank d < r.portRank a ∨ r.portRank b < r.portRank d := by omega
    have hzda : z ≠ d := fun he => by subst he; omega
    have hab' : a ≠ b := fun he => by subst he; omega
    have hza' : z ≠ a := fun h => hza (congrArg color h)
    have hzb' : z ≠ b := fun h => hza ((congrArg color h).trans hab.symm)
    have hda' : d ≠ a := fun h => hda (congrArg color h)
    have hdb' : d ≠ b := fun h => hda ((congrArg color h).trans hab.symm)
    have hzm := (r.mem_rotationInterval_iff_portRank a z b (ha.trans hz.symm)
      (hz.trans hb.symm) hza'.symm hzb' hab').mpr (Or.inl hzi)
    have hdm : d ∉ r.rotationInterval a b := by
      rw [r.mem_rotationInterval_iff_portRank a d b (ha.trans hd.symm)
        (hd.trans hb.symm) hda'.symm hdb' hab']
      omega
    exact hnonalt z d a b hz hc.symm hab hza
      ⟨hzda, hab', hza', hzb', hda', hdb', hz.trans hd.symm, ha.trans hb.symm,
        hz.trans ha.symm, iff_of_true hzm hdm⟩
  obtain ⟨c, d, hcd, hcz⟩ := classBounds z hz
  have hci := inside c hcd.1 hcz
  have hdi := inside d hcd.2.1 (hcd.2.2.1.symm.trans hcz)
  have hmin := Nat.find_min' hex ⟨c, d, hcd, rfl⟩
  omega

/-- A vertex cycle first reaches its starting dart at exponent zero. -/
@[simp] theorem rotationDistance_self (a : Dart G) : r.rotationDistance a a = 0 := by
  apply r.rotationDistance_eq a a rfl 0 rfl
  intro k hk
  omega

/-- A different dart in the same source cycle has positive first-hit rank. -/
theorem rotationDistance_pos_of_ne {G : Graph} (r : RotationSystem G)
    (o a : Dart G) (hoa : o.vertex = a.vertex) (hne : a ≠ o) :
    0 < r.rotationDistance o a := by
  by_contra hn
  have hzero : r.rotationDistance o a = 0 := by omega
  have h := r.pow_rotationDistance o a hoa
  rw [hzero, pow_zero, Equiv.Perm.one_apply] at h
  exact hne h.symm

/-- A forward source step adds one to the first-hit rank until it returns to the
specified cycle cut. -/
theorem rotationDistance_rotate_of_ne {G : Graph} (r : RotationSystem G)
    (o a : Dart G) (hoa : o.vertex = a.vertex) (hne : r.rotate a ≠ o) :
    r.rotationDistance o (r.rotate a) = r.rotationDistance o a + 1 := by
  have hk := r.rotationDistance_lt_period hoa
  have hkn : r.rotationDistance o a + 1 < Function.minimalPeriod r.rotate o := by
    refine lt_of_le_of_ne hk fun heq => hne ?_
    calc r.rotate a = (r.rotate ^ (r.rotationDistance o a + 1)) o := by
          rw [pow_succ', Equiv.Perm.mul_apply, r.pow_rotationDistance o a hoa]
      _ = o := by rw [heq, ← r.rotate.iterate_eq_pow, Function.iterate_minimalPeriod]
  have hp := r.rotationDistance_pow_from o a hoa 1
  rwa [pow_one, Nat.mod_eq_of_lt hkn] at hp

/-- The predecessor of a source cycle cut has its last rank, including unary cycles. -/
theorem rotationDistance_of_rotate_eq {G : Graph} (r : RotationSystem G)
    (o a : Dart G) (hoa : o.vertex = a.vertex) (heq : r.rotate a = o) :
    r.rotationDistance o a = Function.minimalPeriod r.rotate o - 1 := by
  let k := r.rotationDistance o a
  have hperiod : Function.IsPeriodicPt r.rotate (k + 1) o := by
    change (r.rotate : Dart G → Dart G)^[k + 1] o = o
    rw [r.rotate.iterate_eq_pow, pow_succ', Equiv.Perm.mul_apply,
      r.pow_rotationDistance o a hoa, heq]
  have hle := hperiod.minimalPeriod_le (Nat.succ_pos k)
  have hlt := r.rotationDistance_lt_period hoa
  change k = _
  omega

/-- The source vertex cycle after omitting its specified dart, in the original forward
order. A unary vertex cycle gives `Fin 0`, without inventing a corner dart. -/
@[expose] noncomputable def sourceTailEquiv {G : Graph} (r : RotationSystem G) (o : Dart G) :
    {d : Dart G // d.vertex = o.vertex ∧ d ≠ o} ≃
      Fin (Function.minimalPeriod r.rotate o - 1) where
  toFun d := ⟨r.rotationDistance o d.val - 1, by
    have hlt := r.rotationDistance_lt_period d.property.1.symm
    have hpos := r.rotationDistance_pos_of_ne o d.val d.property.1.symm d.property.2
    omega⟩
  invFun i := ⟨(r.rotate ^ (i.val + 1)) o, by
    have hv : ((r.rotate ^ (i.val + 1)) o).vertex = o.vertex :=
      (r.sameCycle_iff _ _).mp (Equiv.Perm.sameCycle_pow_left.mpr .rfl)
    refine ⟨hv, ?_⟩
    intro heq
    have hi : i.val + 1 < Function.minimalPeriod r.rotate o := by omega
    have hzero := r.rotationDistance_self o
    have hrank := r.rotationDistance_pow o (i.val + 1)
    rw [heq, Nat.mod_eq_of_lt hi] at hrank
    omega⟩
  left_inv d := by
    apply Subtype.ext
    have hpos := r.rotationDistance_pos_of_ne o d.val d.property.1.symm d.property.2
    change (r.rotate ^ (r.rotationDistance o d.val - 1 + 1)) o = d.val
    rw [Nat.sub_add_cancel hpos, r.pow_rotationDistance o d.val d.property.1.symm]
  right_inv i := by
    apply Fin.ext
    change r.rotationDistance o ((r.rotate ^ (i.val + 1)) o) - 1 = i.val
    rw [r.rotationDistance_pow, Nat.mod_eq_of_lt (by omega)]
    omega

/-- The actual tail enumeration follows the original successor powers, rather than
reusing contracted distances that have changed when the selected darts were removed. -/
theorem sourceTailEquiv_symm_val {G : Graph} (r : RotationSystem G) (o : Dart G)
    (i : Fin (Function.minimalPeriod r.rotate o - 1)) :
    ((r.sourceTailEquiv o).symm i).val = (r.rotate ^ (i.val + 1)) o := rfl

/-- A strict interval based at its rank origin compares the two terminal ranks. -/
theorem mem_rotationInterval_iff_lt_distance (a b c : Dart G)
    (hab : a.vertex = b.vertex) (hac : a.vertex = c.vertex)
    (hneab : a ≠ b) (hnebc : b ≠ c) (hneac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔ r.rotationDistance a b < r.rotationDistance a c := by
  rw [r.mem_rotationInterval_iff_ranks a a b c rfl hab hac hneab hnebc hneac,
    r.rotationDistance_self]
  have hpos := r.rotationDistance_pos_of_ne a b hab hneab.symm
  omega

/-- Strict literal rotation intervals are cyclic in three distinct incident darts. -/
theorem mem_rotationInterval_cyclic (a b c : Dart G)
    (hab : a.vertex = b.vertex) (hbc : b.vertex = c.vertex)
    (hneab : a ≠ b) (hnebc : b ≠ c) (hneac : a ≠ c) :
    b ∈ r.rotationInterval a c ↔ c ∈ r.rotationInterval b a := by
  rw [r.mem_rotationInterval_iff_portRank a b c hab hbc hneab hnebc hneac,
    r.mem_rotationInterval_iff_portRank b c a hbc (hab.trans hbc).symm
      hnebc hneac.symm hneab.symm]
  lrat_tauto

/-- Between ordered endpoints in the chosen linear ranks, the inclusive interval starts at
the first endpoint and ends at its first forward visit to the last endpoint. -/
theorem rotationDistance_le_iff_portRank_between (a b d : Dart G)
    (hab : a.vertex = b.vertex) (had : a.vertex = d.vertex)
    (hrank : r.portRank a ≤ r.portRank b) :
    r.rotationDistance a d ≤ r.rotationDistance a b ↔
      r.portRank a ≤ r.portRank d ∧ r.portRank d ≤ r.portRank b := by
  by_cases hda : d = a
  · subst d
    simp [hrank]
  by_cases hdb : d = b
  · subst d
    simp [hrank]
  have hrd : r.portRank d ≠ r.portRank a :=
    fun h => hda (r.portRank_injective d a had.symm h)
  have hrb : r.portRank d ≠ r.portRank b :=
    fun h => hdb (r.portRank_injective d b (had.symm.trans hab) h)
  have hdist : r.rotationDistance a d ≠ r.rotationDistance a b := by
    intro h
    exact hdb ((r.pow_rotationDistance a d had).symm.trans
      (h ▸ r.pow_rotationDistance a b hab))
  by_cases he : a = b
  · subst b
    have hpos := r.rotationDistance_pos_of_ne a d had hda
    rw [r.rotationDistance_self]
    omega
  have had' : a ≠ d := Ne.symm hda
  have hinterval := (r.mem_rotationInterval_iff_lt_distance a d b had hab
    had' hdb he).symm.trans
      (r.mem_rotationInterval_iff_portRank a d b had (had.symm.trans hab) had' hdb he)
  omega

/-- The clockwise betweenness of distinct triples starting at a dart fixes its successor.
This also covers endpoint fibers with fewer than three darts. -/
theorem rotate_eq_of_same_incident_intervals (s : RotationSystem G) (a : Dart G)
    (horder : ∀ b c : Dart G, a.vertex = b.vertex → b.vertex = c.vertex →
      a ≠ b → b ≠ c → a ≠ c → (b ∈ r.rotationInterval a c ↔ b ∈ s.rotationInterval a c)) :
    r.rotate a = s.rotate a := by
  classical
  have fixed (t u : RotationSystem G) (ht : t.rotate a = a) : u.rotate a = a := by
    have hcycle := (t.sameCycle_iff a (u.rotate a)).mpr (u.vertex_rotate a).symm
    obtain ⟨n, hn⟩ := hcycle.exists_nat_pow_eq
    have hpow (k : ℕ) : (t.rotate ^ k) a = a := by
      induction k with
      | zero => rfl
      | succ k ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, ht]
    exact hn.symm.trans (hpow n)
  by_cases hr : r.rotate a = a
  · exact hr.trans (fixed r s hr).symm
  by_cases hs : s.rotate a = a
  · exact (fixed s r hs).trans hs.symm
  by_contra hne
  have hpos := s.rotationDistance_pos_of_ne a (r.rotate a) (r.vertex_rotate a).symm hr
  have hm : s.rotate a ∈ s.rotationInterval a (r.rotate a) :=
    Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hpos, by simp only [zero_add, pow_one]⟩
  have h := (horder (s.rotate a) (r.rotate a) (s.vertex_rotate a).symm
    ((s.vertex_rotate a).trans (r.vertex_rotate a).symm)
    (Ne.symm hs) (Ne.symm hne) (Ne.symm hr)).mpr hm
  obtain ⟨k, hk, heq⟩ := Finset.mem_image.mp h
  have hlt := Finset.mem_range.mp hk
  rw [r.rotationDistance_rotate_of_ne a a rfl hr, r.rotationDistance_self] at hlt
  have hk0 : k = 0 := by omega
  exact hne (by simpa only [hk0, zero_add, pow_one] using heq)

end Cslib.Complexity.Graph.RotationSystem
