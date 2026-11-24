/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Clique.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Powerset

/-!
# Bounding 2-SAT solutions by the number of independent sets

Every edge of a 2-SAT instance on a simple graph `G = (V, E)` forbids at least one of the four
Boolean value pairs `(b_u, b_v) ∈ Bool × Bool` across its endpoints. Aligning polarities one vertex
at a time (`Finset.card_union_add_card_inter`) shows that the number of satisfying truth
assignments never exceeds `G.indepSetCount`, the number of independent sets of `G` (realized when
every edge forbids `(true, true)`).

## Main definitions

* `SimpleGraph.indepSetCount`: the number `i(G)` of independent sets of a finite simple graph.

## Main results

* `SimpleGraph.ncard_le_indepSetCount_of_forall_adj`: any set of Boolean assignments forbidding at
  least one pair of values on every edge of `G` has cardinality at most `G.indepSetCount`.
* `SimpleGraph.indepSetCount_bot`: the edgeless graph on `V` has `2 ^ |V|` independent sets.
* `SimpleGraph.indepSetCount_star`: a star with `d` leaves has `2 ^ d + 1` independent sets.
* `SimpleGraph.indepSetCount_pathGraph`: the `n`-vertex path `P_n` has `F_{n + 2}` independent
  sets.
-/

public section

open Set

namespace SimpleGraph

variable {V : Type*}

/-- The number `i(G)` of independent sets of a finite simple graph `G`. The finite vertex type
ensures that `Set.ncard` counts independent sets rather than returning `0` on an infinite family
(such as `∅` and all singletons). -/
-- Finiteness restricts the public domain; `ncard` itself does not require it.
@[expose, nolint unusedArguments]
noncomputable def indepSetCount [Finite V] (G : SimpleGraph V) : ℕ :=
  {s : Set V | G.IsIndepSet s}.ncard

/-- Every finite simple graph has at least one independent set (`∅`), so `0 < G.indepSetCount`. -/
theorem indepSetCount_pos [Finite V] (G : SimpleGraph V) : 0 < G.indepSetCount :=
  (ncard_pos (toFinite _)).mpr ⟨∅, by simp⟩

/-- Boolean indicators of independent sets: assignments with no adjacent `true` pair. -/
private def IsIndepVec (G : SimpleGraph V) (x : V → Bool) : Prop :=
  ∀ u w, G.Adj u w → ¬(x u = true ∧ x w = true)

private theorem ncard_isIndepVec [Finite V] (G : SimpleGraph V) :
    {x : V → Bool | IsIndepVec G x}.ncard = G.indepSetCount := by
  classical
  have hinj : Function.Injective (fun x : V → Bool => {v | x v = true}) := by
    intro x y h
    funext v
    rw [Bool.eq_iff_iff]
    exact Set.ext_iff.mp h v
  have himg : (fun x : V → Bool => {v | x v = true}) '' {x | IsIndepVec G x} =
      {s : Set V | G.IsIndepSet s} := by
    ext s
    constructor
    · rintro ⟨x, hx, rfl⟩ u hu w hw _ hadj
      exact hx u w hadj ⟨hu, hw⟩
    · intro hs
      refine ⟨fun v => decide (v ∈ s), fun u w hadj ⟨hu, hw⟩ => ?_, ?_⟩
      · simp only [decide_eq_true_eq] at hu hw
        exact hs hu hw (G.ne_of_adj hadj) hadj
      · ext v
        simp
  rw [indepSetCount, ← himg, ncard_image_of_injective _ hinj]

section PolarityHelpers

variable [DecidableEq V]

/-- Flip every forbidden polarity at vertex `v₀` to `true`. -/
private def flipAt (v₀ : V) (p : V → V → Bool × Bool) (u w : V) : Bool × Bool :=
  (if u = v₀ then true else (p u w).1, if w = v₀ then true else (p u w).2)

private theorem flipAt_symm (G : SimpleGraph V) {v₀ : V} {p : V → V → Bool × Bool}
    (hp : ∀ u w, G.Adj u w → p w u = (p u w).swap) :
    ∀ u w, G.Adj u w → flipAt v₀ p w u = (flipAt v₀ p u w).swap := by
  intro u w hadj
  have h := hp u w hadj
  ext <;> simp [flipAt, h]

/-- Toggle coordinate `v₀` of a Boolean assignment. -/
private def toggleAt (v₀ : V) (x : V → Bool) : V → Bool :=
  Function.update x v₀ (!x v₀)

private theorem toggleAt_involutive (v₀ : V) : Function.Involutive (toggleAt (V := V) v₀) := by
  intro x
  funext w
  by_cases hw : w = v₀
  · subst hw
    simp [toggleAt]
  · simp [toggleAt, hw]

end PolarityHelpers

section PolarityCompression

variable [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Assignments avoiding the forbidden pair `p u w` on every edge `G.Adj u w`. -/
private def twoSatFinset (p : V → V → Bool × Bool) : Finset (V → Bool) :=
  Finset.univ.filter fun x => ∀ u w, G.Adj u w → ¬(x u = (p u w).1 ∧ x w = (p u w).2)

/-- One step of vertex polarity compression: replacing `p` by `flipAt v₀ p` never decreases the
number of satisfying assignments. -/
private theorem card_twoSatFinset_le_flipAt (v₀ : V) {p : V → V → Bool × Bool}
    (hp : ∀ u w, G.Adj u w → p w u = (p u w).swap) :
    (twoSatFinset G p).card ≤ (twoSatFinset G (flipAt v₀ p)).card := by
  set R : Finset (V → Bool) := Finset.univ.filter fun x =>
    x v₀ = false ∧ ∀ u w, u ≠ v₀ → w ≠ v₀ → G.Adj u w → ¬(x u = (p u w).1 ∧ x w = (p u w).2)
  have split_card (q : V → V → Bool × Bool)
      (hq : ∀ u w, G.Adj u w → q w u = (q u w).swap)
      (hrest : ∀ u w, u ≠ v₀ → w ≠ v₀ → q u w = p u w) :
      (twoSatFinset G q).card =
        (R.filter fun x => ∀ w, G.Adj v₀ w → (q v₀ w).1 = false → x w ≠ (q v₀ w).2).card +
        (R.filter fun x => ∀ w, G.Adj v₀ w → (q v₀ w).1 = true → x w ≠ (q v₀ w).2).card := by
    set S := twoSatFinset G q
    rw [← Finset.card_filter_add_card_filter_not (s := S) (p := fun x => x v₀ = false)]
    congr 1
    · refine congrArg Finset.card (Finset.ext fun x => ?_)
      simp only [S, twoSatFinset, R, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hx, hx0⟩
        refine ⟨⟨hx0, fun u w hu hw hadj => hrest u w hu hw ▸ hx u w hadj⟩,
          fun w hadj hq0 hxw => hx v₀ w hadj ⟨hx0.trans hq0.symm, hxw⟩⟩
      · rintro ⟨⟨hx0, hR⟩, hA⟩
        refine ⟨fun u w hadj ⟨hxu, hxw⟩ => ?_, hx0⟩
        by_cases hu : u = v₀
        · rw [hu] at hadj hxu hxw
          exact hA w hadj (hxu.symm.trans hx0) hxw
        · by_cases hw : w = v₀
          · rw [hw] at hadj hxu hxw
            have hsym := hq v₀ u hadj.symm
            have h1 : (q u v₀).1 = (q v₀ u).2 := congrArg Prod.fst hsym
            have h2 : (q u v₀).2 = (q v₀ u).1 := congrArg Prod.snd hsym
            exact hA u hadj.symm (h2.symm.trans (hxw.symm.trans hx0)) (hxu.trans h1)
          · exact hR u w hu hw hadj ⟨(congrArg Prod.fst (hrest u w hu hw)) ▸ hxu,
              (congrArg Prod.snd (hrest u w hu hw)) ▸ hxw⟩
    · have hinj : Function.Injective (toggleAt (V := V) v₀) :=
        (toggleAt_involutive v₀).injective
      rw [← Finset.card_image_of_injective _ hinj]
      refine congrArg Finset.card (Finset.ext fun x => ?_)
      simp only [Finset.mem_image, S, twoSatFinset, R, Finset.mem_filter, Finset.mem_univ,
        true_and, Bool.not_eq_false]
      constructor
      · rintro ⟨y, ⟨hy, hyv₀⟩, rfl⟩
        have hxv₀ : toggleAt v₀ y v₀ = false := by simp [toggleAt, hyv₀]
        have hne : ∀ w, w ≠ v₀ → toggleAt v₀ y w = y w := fun w hw => by simp [toggleAt, hw]
        refine ⟨⟨hxv₀, fun u w hu hw hadj => ?_⟩, fun w hadj hq1 hxw => ?_⟩
        · rw [hne u hu, hne w hw, ← hrest u w hu hw]
          exact hy u w hadj
        · rw [hne w (G.ne_of_adj hadj).symm] at hxw
          exact hy v₀ w hadj ⟨hyv₀.trans hq1.symm, hxw⟩
      · rintro ⟨⟨hx0, hR⟩, hB⟩
        refine ⟨toggleAt v₀ x, ⟨fun u w hadj ⟨hxu, hxw⟩ => ?_, by simp [toggleAt, hx0]⟩,
          toggleAt_involutive v₀ x⟩
        have hne : ∀ z, z ≠ v₀ → toggleAt v₀ x z = x z := fun z hz => by simp [toggleAt, hz]
        have htv₀ : toggleAt v₀ x v₀ = true := by simp [toggleAt, hx0]
        by_cases hu : u = v₀
        · rw [hu] at hadj hxu hxw
          have hw : w ≠ v₀ := (G.ne_of_adj hadj).symm
          exact hB w hadj (hxu.symm.trans htv₀) ((hne w hw).symm.trans hxw)
        · by_cases hw : w = v₀
          · rw [hw] at hadj hxu hxw
            have hsym := hq v₀ u hadj.symm
            have h1 : (q u v₀).1 = (q v₀ u).2 := congrArg Prod.fst hsym
            have h2 : (q u v₀).2 = (q v₀ u).1 := congrArg Prod.snd hsym
            exact hB u hadj.symm (h2.symm.trans (hxw.symm.trans htv₀))
              (((hne u hu).symm.trans hxu).trans h1)
          · exact hR u w hu hw hadj
              ⟨(congrArg Prod.fst (hrest u w hu hw)) ▸ ((hne u hu).symm.trans hxu),
                (congrArg Prod.snd (hrest u w hu hw)) ▸ ((hne w hw).symm.trans hxw)⟩
  have hp_card := split_card p hp (fun _ _ _ _ => rfl)
  have hflip_card := split_card (flipAt v₀ p) (flipAt_symm G hp) (fun u w hu hw => by
    simp [flipAt, hu, hw])
  set A := R.filter fun x => ∀ w, G.Adj v₀ w → (p v₀ w).1 = false → x w ≠ (p v₀ w).2
  set B := R.filter fun x => ∀ w, G.Adj v₀ w → (p v₀ w).1 = true → x w ≠ (p v₀ w).2
  have hA' : (R.filter fun x =>
      ∀ w, G.Adj v₀ w → (flipAt v₀ p v₀ w).1 = false → x w ≠ (flipAt v₀ p v₀ w).2) = R := by
    ext x
    simp [flipAt]
  have hB' : (R.filter fun x =>
      ∀ w, G.Adj v₀ w → (flipAt v₀ p v₀ w).1 = true → x w ≠ (flipAt v₀ p v₀ w).2) = A ∩ B := by
    ext x
    simp only [Finset.mem_inter, A, B, Finset.mem_filter, flipAt, ↓reduceIte, true_imp_iff]
    refine ⟨fun ⟨hxR, hall⟩ => ⟨⟨hxR, fun w hadj _ => ?_⟩, ⟨hxR, fun w hadj _ => ?_⟩⟩,
      fun ⟨⟨hxR, hA0⟩, ⟨_, hB1⟩⟩ => ⟨hxR, fun w hadj => ?_⟩⟩
    · simpa [G.ne_of_adj hadj |>.symm] using hall w hadj
    · simpa [G.ne_of_adj hadj |>.symm] using hall w hadj
    · have hw : w ≠ v₀ := (G.ne_of_adj hadj).symm
      simp only [hw, ↓reduceIte]
      cases h01 : (p v₀ w).1
      · exact hA0 w hadj h01
      · exact hB1 w hadj h01
  rw [hp_card, hflip_card, hA', hB', ← Finset.card_union_add_card_inter A B]
  exact Nat.add_le_add_right
    (Finset.card_le_card (Finset.union_subset (Finset.filter_subset _ R)
      (Finset.filter_subset _ R))) _

private theorem card_twoSatFinset_le_allTrue {p : V → V → Bool × Bool}
    (hp : ∀ u w, G.Adj u w → p w u = (p u w).swap) :
    (twoSatFinset G p).card ≤ (twoSatFinset G fun _ _ => (true, true)).card := by
  suffices ∀ s : Finset V, ∀ q : V → V → Bool × Bool,
      (∀ u w, G.Adj u w → q w u = (q u w).swap) →
      ∃ q' : V → V → Bool × Bool,
        (∀ u w, G.Adj u w → q' w u = (q' u w).swap) ∧
        (∀ v ∈ s, ∀ w, (q' v w).1 = true ∧ (q' w v).2 = true) ∧
        (twoSatFinset G q).card ≤ (twoSatFinset G q').card by
    obtain ⟨q', _, hq', hle⟩ := this Finset.univ p hp
    have heq : twoSatFinset G q' = twoSatFinset G fun _ _ => (true, true) := by
      ext x
      simp only [twoSatFinset, Finset.mem_filter, Finset.mem_univ, true_and]
      refine forall₂_congr fun u w => imp_congr_right fun _ => ?_
      rw [(hq' u (Finset.mem_univ u) w).1, (hq' w (Finset.mem_univ w) u).2]
    exact heq ▸ hle
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro q hq
    exact ⟨q, hq, fun _ hv => absurd hv (Finset.notMem_empty _), le_rfl⟩
  | @insert v₀ s hv₀ ih =>
    intro q hq
    obtain ⟨q₁, hq₁sym, hq₁s, hle₁⟩ := ih q hq
    refine ⟨flipAt v₀ q₁, flipAt_symm G hq₁sym, fun v hv w => ?_,
      hle₁.trans (card_twoSatFinset_le_flipAt G v₀ hq₁sym)⟩
    rcases Finset.mem_insert.mp hv with rfl | hvs
    · simp [flipAt]
    · obtain ⟨h1, h2⟩ := hq₁s v hvs w
      constructor
      · simp [flipAt, h1]
      · simp [flipAt, h2]

end PolarityCompression

/-- **2-SAT solutions are at most `i(G)`.** If for every adjacent pair `G.Adj u w` in a finite
simple graph `G`, at least one pair of Boolean values `(bu, bw)` is forbidden across `S`, then
`S.ncard ≤ G.indepSetCount`. -/
theorem ncard_le_indepSetCount_of_forall_adj [Finite V] (G : SimpleGraph V)
    {S : Set (V → Bool)}
    (hS : ∀ ⦃u w⦄, G.Adj u w → ∃ bu bw : Bool, ∀ x ∈ S, ¬(x u = bu ∧ x w = bw)) :
    S.ncard ≤ G.indepSetCount := by
  classical
  cases nonempty_fintype V
  set e := Fintype.equivFin V
  let raw : V → V → Bool × Bool := fun u w =>
    if h : G.Adj u w then ((hS h).choose, (hS h).choose_spec.choose) else (true, true)
  let p : V → V → Bool × Bool := fun u w =>
    if e u < e w then raw u w else (raw w u).swap
  have hp : ∀ u w, G.Adj u w → p w u = (p u w).swap := by
    intro u w hadj
    have hne : e u ≠ e w := e.injective.ne (G.ne_of_adj hadj)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hnlt : ¬e w < e u := asymm hlt
      simp [p, hlt, hnlt]
    · have hnlt : ¬e u < e w := asymm hgt
      simp [p, hgt, hnlt]
  have hsub : S ⊆ (twoSatFinset G p : Set (V → Bool)) := by
    intro x hx
    refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ x, fun u w hadj => ?_⟩)
    have hne : e u ≠ e w := e.injective.ne (G.ne_of_adj hadj)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · simp only [p, hlt, ↓reduceIte, raw, hadj, ↓reduceDIte]
      exact (hS hadj).choose_spec.choose_spec x hx
    · have hnlt : ¬e u < e w := asymm hgt
      simp only [p, hnlt, ↓reduceIte, raw, hadj.symm, ↓reduceDIte, Prod.swap_prod_mk]
      rintro ⟨hxu, hxw⟩
      exact (hS hadj.symm).choose_spec.choose_spec x hx ⟨hxw, hxu⟩
  have hindep : (twoSatFinset G fun _ _ => (true, true)).card = G.indepSetCount := by
    rw [← ncard_coe_finset, ← ncard_isIndepVec G]
    refine congrArg Set.ncard (Set.ext fun x => ?_)
    simp [twoSatFinset, IsIndepVec]
  calc S.ncard ≤ (twoSatFinset G p : Set (V → Bool)).ncard := ncard_le_ncard hsub (toFinite _)
    _ = (twoSatFinset G p).card := ncard_coe_finset _
    _ ≤ (twoSatFinset G fun _ _ => (true, true)).card := card_twoSatFinset_le_allTrue G hp
    _ = G.indepSetCount := hindep

/-! ### Exact independent-set counts on basic families -/

/-- The edgeless graph on a finite vertex type `V` has `2 ^ |V|` independent sets. -/
@[simp] theorem indepSetCount_bot [Finite V] :
    (⊥ : SimpleGraph V).indepSetCount = 2 ^ Nat.card V := by
  rw [← ncard_isIndepVec]
  have huniv : {x : V → Bool | IsIndepVec ⊥ x} = univ :=
    eq_univ_of_forall fun _ _ _ h => absurd ((bot_adj _ _).mp h) False.elim
  rw [huniv, ncard_univ, Nat.card_fun, Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool]

/-- **Independent sets of a star (`K_{1, d}`).** If every edge of `G` meets `v₀` and `v₀` is
adjacent to every other vertex, then `G.indepSetCount = 2 ^ (|V| - 1) + 1`. -/
theorem indepSetCount_star [Finite V] (G : SimpleGraph V) (v₀ : V)
    (hstar : ∀ ⦃u w⦄, G.Adj u w → u = v₀ ∨ w = v₀)
    (hfull : ∀ w, w ≠ v₀ → G.Adj v₀ w) :
    G.indepSetCount = 2 ^ (Nat.card V - 1) + 1 := by
  classical
  rw [← ncard_isIndepVec]
  set S0 : Set (V → Bool) := {x | x v₀ = false}
  set S1 : Set (V → Bool) := {fun w => decide (w = v₀)}
  have hdecomp : {x : V → Bool | IsIndepVec G x} = S0 ∪ S1 := by
    ext x
    simp only [mem_ofPred_eq, IsIndepVec, S0, S1, mem_union, mem_singleton_iff]
    constructor
    · intro hx
      cases hv : x v₀
      · exact Or.inl rfl
      · right
        funext w
        by_cases hw : w = v₀
        · subst hw
          simpa using hv
        · simp only [hw, decide_false, Bool.eq_false_iff]
          intro hxw
          exact hx v₀ w (hfull w hw) ⟨hv, hxw⟩
    · rintro (hx0 | rfl) u w hadj ⟨hxu, hxw⟩
      · rcases hstar hadj with rfl | rfl
        · exact Bool.false_ne_true (hx0.symm.trans hxu)
        · exact Bool.false_ne_true (hx0.symm.trans hxw)
      · simp only [decide_eq_true_eq] at hxu hxw
        exact G.ne_of_adj hadj (hxu.trans hxw.symm)
  have hdisj : Disjoint S0 S1 := by
    rw [disjoint_singleton_right]
    simp [S0]
  have hcard0 : S0.ncard = 2 ^ (Nat.card V - 1) := by
    set R : Set V := ({v₀} : Set V)ᶜ
    have heq : S0 = range
        (fun (y : R → Bool) (w : V) => if h : w = v₀ then false else y ⟨w, h⟩) := by
      ext x
      simp only [S0, mem_ofPred_eq, mem_range]
      refine ⟨fun hx0 => ⟨fun w => x w.1, funext fun w => ?_⟩, ?_⟩
      · by_cases hw : w = v₀
        · subst hw
          simp [hx0]
        · simp [hw]
      · rintro ⟨y, rfl⟩
        simp
    have hinj : Function.Injective
        (fun (y : R → Bool) (w : V) => if h : w = v₀ then false else y ⟨w, h⟩) := by
      intro y₁ y₂ h
      funext ⟨w, hw⟩
      have hw' : w ≠ v₀ := hw
      simpa [hw'] using congrFun h w
    have hRcard : Nat.card R = Nat.card V - 1 := by
      rw [Nat.card_coe_set_eq, ncard_compl, ncard_singleton]
    rw [heq, ncard_range_of_injective hinj, Nat.card_fun,
      Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, hRcard]
  rw [hdecomp, ncard_union_eq hdisj (toFinite _) (toFinite _), hcard0, ncard_singleton]

/-- **Independent sets of a path (`i(P_n) = F_{n + 2}`).** The `n`-vertex path `pathGraph n` has
`Nat.fib (n + 2)` independent sets (`1, 2, 3, 5, 8, ...` for `n = 0, 1, 2, 3, 4, ...`). -/
theorem indepSetCount_pathGraph : ∀ n : ℕ, (pathGraph n).indepSetCount = Nat.fib (n + 2)
  | 0 => by
    rw [← ncard_isIndepVec]
    have h1 : {x : Fin 0 → Bool | IsIndepVec (pathGraph 0) x} = {Fin.elim0} := by
      ext x
      simp only [mem_ofPred_eq, mem_singleton_iff]
      exact ⟨fun _ => Subsingleton.elim _ _, fun _ u => u.elim0⟩
    rw [h1, ncard_singleton]
    rfl
  | 1 => by
    have hbot : pathGraph 1 = ⊥ := by
      ext i j
      simp only [pathGraph_adj, bot_adj, iff_false]
      have hi : (i : ℕ) < 1 := i.isLt
      have hj : (j : ℕ) < 1 := j.isLt
      rintro (h | h) <;> omega
    rw [hbot, indepSetCount_bot, Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  | n + 2 => by
    rw [← ncard_isIndepVec]
    set S := {x : Fin (n + 2) → Bool | IsIndepVec (pathGraph (n + 2)) x}
    set S0 := {x ∈ S | x (Fin.last (n + 1)) = false}
    set S1 := {x ∈ S | x (Fin.last (n + 1)) = true}
    have hunion : S = S0 ∪ S1 := by
      ext x
      simp only [S0, S1, mem_union, mem_sep_iff]
      constructor
      · intro hx
        cases x (Fin.last (n + 1))
        · exact Or.inl ⟨hx, rfl⟩
        · exact Or.inr ⟨hx, rfl⟩
      · rintro (⟨hx, _⟩ | ⟨hx, _⟩) <;> exact hx
    have hdisj : Disjoint S0 S1 := by
      rw [Set.disjoint_left]
      intro _ hx0 hx1
      exact Bool.false_ne_true (hx0.2.symm.trans hx1.2)
    let ext0 : (Fin (n + 1) → Bool) → (Fin (n + 2) → Bool) :=
      fun y => Fin.snoc y false
    have hinj0 : Function.Injective ext0 := fun x y h => by
      funext i
      simpa [ext0] using congrFun h i.castSucc
    have himg0 : ext0 '' {y | IsIndepVec (pathGraph (n + 1)) y} = S0 := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        refine ⟨fun i j hadj ⟨hi, hj⟩ => ?_, by simp [ext0]⟩
        induction i using Fin.lastCases with
        | last => simp [ext0] at hi
        | cast i =>
          induction j using Fin.lastCases with
          | last => simp [ext0] at hj
          | cast j =>
            simp only [ext0, Fin.snoc_castSucc] at hi hj
            exact hy i j (by simpa [pathGraph_adj] using hadj) ⟨hi, hj⟩
      · rintro ⟨hx, hxlast⟩
        refine ⟨fun i => x i.castSucc, fun i j hadj ⟨hi, hj⟩ =>
          hx i.castSucc j.castSucc (by simpa [pathGraph_adj] using hadj) ⟨hi, hj⟩, ?_⟩
        funext k
        induction k using Fin.lastCases with
        | last => simp [ext0, hxlast]
        | cast i => simp [ext0]
    let ext1 : (Fin n → Bool) → (Fin (n + 2) → Bool) :=
      fun z => Fin.snoc (Fin.snoc z false) true
    have hinj1 : Function.Injective ext1 := fun x y h => by
      funext i
      simpa [ext1] using congrFun h i.castSucc.castSucc
    have himg1 : ext1 '' {z | IsIndepVec (pathGraph n) z} = S1 := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨fun i j hadj ⟨hi, hj⟩ => ?_, by simp [ext1]⟩
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact (pathGraph (n + 2)).ne_of_adj hadj rfl
          | cast j =>
            induction j using Fin.lastCases with
            | last => simp [ext1] at hj
            | cast j =>
              simp only [pathGraph_adj, Fin.val_last, Fin.val_castSucc] at hadj
              have := j.isLt
              omega
        | cast i =>
          induction i using Fin.lastCases with
          | last => simp [ext1] at hi
          | cast i =>
            induction j using Fin.lastCases with
            | last =>
              simp only [pathGraph_adj, Fin.val_castSucc, Fin.val_last] at hadj
              have := i.isLt
              omega
            | cast j =>
              induction j using Fin.lastCases with
              | last => simp [ext1] at hj
              | cast j =>
                simp only [ext1, Fin.snoc_castSucc] at hi hj
                exact hz i j (by simpa [pathGraph_adj] using hadj) ⟨hi, hj⟩
      · rintro ⟨hx, hxlast⟩
        have hxprev : x (Fin.last n).castSucc = false := by
          rw [Bool.eq_false_iff]
          intro htrue
          exact hx (Fin.last n).castSucc (Fin.last (n + 1))
            (pathGraph_adj.mpr (Or.inl (by simp))) ⟨htrue, hxlast⟩
        refine ⟨fun i => x i.castSucc.castSucc, fun i j hadj ⟨hi, hj⟩ =>
          hx i.castSucc.castSucc j.castSucc.castSucc (by simpa [pathGraph_adj] using hadj)
            ⟨hi, hj⟩, ?_⟩
        funext k
        induction k using Fin.lastCases with
        | last => simp [ext1, hxlast]
        | cast k =>
          induction k using Fin.lastCases with
          | last => simp [ext1, hxprev]
          | cast i => simp [ext1]
    rw [hunion, ncard_union_eq hdisj (toFinite _) (toFinite _), ← himg0,
      ncard_image_of_injective _ hinj0, ← himg1, ncard_image_of_injective _ hinj1,
      ncard_isIndepVec, ncard_isIndepVec, indepSetCount_pathGraph (n + 1),
      indepSetCount_pathGraph n, add_comm, ← Nat.fib_add_two]

end SimpleGraph
