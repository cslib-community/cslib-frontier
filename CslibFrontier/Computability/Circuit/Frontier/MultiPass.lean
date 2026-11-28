/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.BranchingProgram
public import Mathlib.Analysis.SpecialFunctions.Log.Base
import CslibFrontier.Foundations.Data.Set.Card
import CslibFrontier.Tactic.LinarithCast
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-pass sweeps and slice-restriction bounds

This module extends the dynamic charging lemma `Cslib.Circuits.Frontier.Sweep.ncard_le` from
read-once branching programs (`Cslib.Circuits.Frontier.ReadOnceNBP`) to **oblivious multi-pass
branching programs** and **partial-overlap coordinate restrictions**:

1. **Exact slice invariance (`RectangleFree.restrictSlice`, `RectangleBias.restrictSlice`)**:
   fixing any subset of coordinates `O ⊆ ι` to any assignment `a : O → U` preserves both
   `RectangleFree · K` and `RectangleBias · K b` on `restrictSlice S O a` with the **exact same**
   threshold `K` (and bias `b`). By pigeonhole (`exists_le_mul_ncard_restrictSlice`), some slice
   satisfies `|S| ≤ |U| ^ |O| · |restrictSlice S O a|`.
2. **Alternating (`boustrophedon`) `k`-pass branching programs (`AlternatingPassNBP`)**:
   even passes scan `0, ..., T - 1` forward while odd passes scan `T - 1, ..., 0` backward.
   At every cut `0 < τ < T`, all `k - 1` pass-turnaround states lie strictly on one side of
   `revealed τ | (revealed τ)ᶜ`, so the dynamic sweep message `AlternatingPassNBP.sweep` holds only
   the `k` active pass states (`M ^ k`). Consequently, a `k`-pass program with per-label fiber
   capacity `C` (`C = |M|` when deterministic) satisfies
   `|accepted| ≤ (K - 1) ^ 2 · (∑_{t < T} |U| ^ |newly t|) · C ^ k`, yielding state-width lower
   bound `k · log_q |M| ≥ log_q |S| - 2 log_q K - log_q T - 1` (`w ≥ n / k - o(n)`), avoiding the
   factor-of-two loss of static single-cut reductions [Jukna2012].
3. **Same-order `k`-pass branching programs (`SameOrderPassNBP`)**:
   when all `k` passes scan `0, ..., T - 1` in the same order, `k - 1` inter-pass turnaround states
   also cross every interior cut `0 < τ < T` without changing between consecutive sweep steps,
   giving `|accepted| ≤ (K - 1) ^ 2 · (∑_{t < T} |U| ^ |newly t|) · |M| ^ (k - 1) · C ^ k`
   (`(2 k - 1) · log_q |M| ≥ log_q |S| - 2 log_q K - log_q T - 1`, i.e. `w ≥ n / (2 k - 1) - o(n)`
   when deterministic).

## Main definitions

* `Cslib.Circuits.Frontier.extendAssign`, `Cslib.Circuits.Frontier.restrictSlice`: coordinate-slice
  extension and restriction.
* `Cslib.Circuits.Frontier.AlternatingPassNBP`: layered alternating (`boustrophedon`) `k`-pass
  nondeterministic branching program and its `sweep`.
* `Cslib.Circuits.Frontier.SameOrderPassNBP`: layered same-order `k`-pass nondeterministic
  branching program and its `sweep`.
* `Cslib.Circuits.Frontier.ReadOnceNBP.Deterministic`,
  `Cslib.Circuits.Frontier.ReadOnceNBP.toAlternatingPassNBP`: determinism predicate and embedding
  of a `ReadOnceNBP` as a `1`-pass `AlternatingPassNBP`.

## Main results

* `Cslib.Circuits.Frontier.RectangleFree.restrictSlice`,
  `Cslib.Circuits.Frontier.RectangleBias.restrictSlice`,
  `Cslib.Circuits.Frontier.exists_le_mul_ncard_restrictSlice`: restriction invariance and dense
  slice existence.
* `Cslib.Circuits.Frontier.Sweep.ncard_le_of_ncard_transition_le`: shared sweep cardinality bound
  from a per-step state-fiber factor.
* `Cslib.Circuits.Frontier.AlternatingPassNBP.ncard_accepted_le_of_hasFiberBound`,
  `Cslib.Circuits.Frontier.AlternatingPassNBP.ncard_accepted_le_deterministic`,
  `Cslib.Circuits.Frontier.AlternatingPassNBP.le_passes_mul_logb_card`: alternating `k`-pass
  counting and `w ≥ n / k - o(n)` width lower bounds.
* `Cslib.Circuits.Frontier.SameOrderPassNBP.ncard_accepted_le_of_hasFiberBound`,
  `Cslib.Circuits.Frontier.SameOrderPassNBP.ncard_accepted_le_deterministic`,
  `Cslib.Circuits.Frontier.SameOrderPassNBP.le_two_mul_passes_sub_one_mul_logb_card`: same-order
  `k`-pass counting and `w ≥ n / (2 k - 1) - o(n)` width lower bounds.
* `Cslib.Circuits.Frontier.le_passes_mul_logb_card_of_slice`,
  `Cslib.Circuits.Frontier.le_logb_card_of_slice_readOnce`: partial-overlap slice bounds for
  `k`-pass (`AlternatingPassNBP`) and read-once (`ReadOnceNBP`) programs (`w ≥ (1 - α) n - o(n)`).

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*, Ch. 16][Jukna2012]
-/

public section

namespace Cslib.Circuits.Frontier

open Set

/-! ### Coordinate slices and exact restriction invariance -/

section RestrictSlice

variable {ι U : Type*}

/-- Combine an assignment `a : O → U` on `O` and `y : ↥Oᶜ → U` outside `O` into `ι → U`. -/
noncomputable def extendAssign (O : Set ι) (a : O → U) (y : ↥Oᶜ → U) : ι → U :=
  open Classical in
  fun i => if h : i ∈ O then a ⟨i, h⟩ else y ⟨i, h⟩

/-- The slice `{y : ↥Oᶜ → U | extendAssign O a y ∈ S}` of `S` fixing `O` to `a`. -/
@[expose] noncomputable def restrictSlice (S : Set (ι → U)) (O : Set ι) (a : O → U) :
    Set (↥Oᶜ → U) :=
  extendAssign O a ⁻¹' S

@[simp]
theorem extendAssign_mem {O : Set ι} {a : O → U} {y : ↥Oᶜ → U} {i : ι} (hi : i ∈ O) :
    extendAssign O a y i = a ⟨i, hi⟩ := by
  classical
  exact dite_eq_left hi

@[simp]
theorem extendAssign_notMem {O : Set ι} {a : O → U} {y : ↥Oᶜ → U} {i : ι} (hi : i ∉ O) :
    extendAssign O a y i = y ⟨i, hi⟩ := by
  classical
  exact dite_eq_right hi

@[simp]
theorem domRestrict_extendAssign_left (O : Set ι) (a : O → U) (y : ↥Oᶜ → U) :
    O.domRestrict (extendAssign O a y) = a :=
  funext fun ⟨_, hi⟩ => extendAssign_mem hi

@[simp]
theorem domRestrict_extendAssign_right (O : Set ι) (a : O → U) (y : ↥Oᶜ → U) :
    Oᶜ.domRestrict (extendAssign O a y) = y :=
  funext fun ⟨_, hi⟩ => extendAssign_notMem hi

@[simp]
theorem extendAssign_domRestrict (O : Set ι) (x : ι → U) :
    extendAssign O (O.domRestrict x) (Oᶜ.domRestrict x) = x :=
  funext fun i => by
    by_cases hi : i ∈ O
    · exact extendAssign_mem hi
    · exact extendAssign_notMem hi

/-- Extending with a fixed `a : O → U` is injective on `↥Oᶜ → U`. -/
theorem extendAssign_injective (O : Set ι) (a : O → U) : Function.Injective (extendAssign O a) := by
  intro y₁ y₂ h
  funext ⟨i, hi⟩
  simpa only [extendAssign_notMem hi] using congrFun h i

private def liftSliceLeft {O : Set ι} (Y : Set ↥Oᶜ) (u : Y → U) : (Subtype.val '' Y) → U :=
  fun x =>
    have hxO : x.val ∉ O := by
      obtain ⟨w, _, heq⟩ := x.property
      exact heq ▸ w.property
    have hxY : (⟨x.val, hxO⟩ : ↥Oᶜ) ∈ Y := by
      obtain ⟨w, hw, heq⟩ := x.property
      have hw' : w = ⟨x.val, hxO⟩ := Subtype.ext heq
      exact hw' ▸ hw
    u ⟨⟨x.val, hxO⟩, hxY⟩

private theorem liftSliceLeft_injective {O : Set ι} (Y : Set ↥Oᶜ) :
    Function.Injective (liftSliceLeft (U := U) Y) := by
  intro u₁ u₂ h
  funext ⟨w, hw⟩
  have hx := congrFun h ⟨w.val, ⟨w, hw, rfl⟩⟩
  simpa only [liftSliceLeft] using hx

private noncomputable def liftSliceRight {O : Set ι} (a : O → U) (Y : Set ↥Oᶜ) (v : ↥Yᶜ → U) :
    ↥(Subtype.val '' Y)ᶜ → U :=
  open Classical in
  fun x =>
    if hO : x.val ∈ O then a ⟨x.val, hO⟩
    else v ⟨⟨x.val, hO⟩, fun hy => x.property ⟨⟨x.val, hO⟩, hy, rfl⟩⟩

private theorem liftSliceRight_notMem {O : Set ι} (a : O → U) (Y : Set ↥Oᶜ) (v : ↥Yᶜ → U)
    (x : ↥(Subtype.val '' Y)ᶜ) (hO : x.val ∉ O) :
    liftSliceRight a Y v x = v ⟨⟨x.val, hO⟩, fun hy => x.property ⟨⟨x.val, hO⟩, hy, rfl⟩⟩ := by
  classical
  exact dite_eq_right hO

private theorem liftSliceRight_mem {O : Set ι} (a : O → U) (Y : Set ↥Oᶜ) (v : ↥Yᶜ → U)
    (x : ↥(Subtype.val '' Y)ᶜ) (hO : x.val ∈ O) :
    liftSliceRight a Y v x = a ⟨x.val, hO⟩ := by
  classical
  exact dite_eq_left hO

private theorem liftSliceRight_injective {O : Set ι} (a : O → U) (Y : Set ↥Oᶜ) :
    Function.Injective (liftSliceRight a Y) := by
  intro v₁ v₂ h
  funext ⟨w, hw⟩
  have hxX : w.val ∉ Subtype.val '' Y := by
    rintro ⟨w', hw', heq⟩
    exact hw (Subtype.ext heq ▸ hw')
  have hx := congrFun h ⟨w.val, hxX⟩
  rw [liftSliceRight_notMem _ _ _ _ w.property, liftSliceRight_notMem _ _ _ _ w.property] at hx
  exact hx

private theorem image_extendAssign_rectangle {O : Set ι} (a : O → U) (Y : Set ↥Oᶜ)
    (A : Set (Y → U)) (B : Set (↥Yᶜ → U)) :
    extendAssign O a '' rectangle Y A B =
      rectangle (Subtype.val '' Y) (liftSliceLeft Y '' A) (liftSliceRight a Y '' B) := by
  ext z
  constructor
  · rintro ⟨y, ⟨hyA, hyB⟩, rfl⟩
    refine ⟨⟨Y.domRestrict y, hyA, ?_⟩, ⟨Yᶜ.domRestrict y, hyB, ?_⟩⟩
    · funext x
      obtain ⟨w, _, heq⟩ := x.property
      have hxO : x.val ∉ O := heq ▸ w.property
      simp only [liftSliceLeft, domRestrict]
      rw [extendAssign_notMem hxO]
    · funext x
      by_cases hO : x.val ∈ O
      · rw [liftSliceRight_mem _ _ _ _ hO]
        exact (extendAssign_mem hO).symm
      · rw [liftSliceRight_notMem _ _ _ _ hO]
        exact (extendAssign_notMem hO).symm
  · rintro ⟨⟨u, huA, hzu⟩, ⟨v, hvB, hzv⟩⟩
    refine ⟨Oᶜ.domRestrict z, ⟨?_, ?_⟩, ?_⟩
    · have heq : Y.domRestrict (Oᶜ.domRestrict z) = u := by
        funext ⟨w, hw⟩
        have hx := congrFun hzu ⟨w.val, ⟨w, hw, rfl⟩⟩
        simpa only [liftSliceLeft, domRestrict] using hx.symm
      exact heq ▸ huA
    · have heq : Yᶜ.domRestrict (Oᶜ.domRestrict z) = v := by
        funext ⟨w, hw⟩
        have hxX : w.val ∉ Subtype.val '' Y := by
          rintro ⟨w', hw', heq'⟩
          exact hw (Subtype.ext heq' ▸ hw')
        have hx := congrFun hzv ⟨w.val, hxX⟩
        rw [liftSliceRight_notMem _ _ _ _ w.property] at hx
        exact hx.symm
      exact heq ▸ hvB
    · funext i
      by_cases hO : i ∈ O
      · have hiX : i ∉ Subtype.val '' Y := by
          rintro ⟨w, _, rfl⟩
          exact w.property hO
        have hx := congrFun hzv ⟨i, hiX⟩
        rw [extendAssign_mem hO, ← liftSliceRight_mem a Y v ⟨i, hiX⟩ hO]
        exact hx
      · simp [extendAssign_notMem hO, domRestrict]

private theorem encard_lt_of_image_injective {α β : Type*} {s : Set α} {f : α → β} {K : ℕ}
    (hf : Function.Injective f) (h : (f '' s).encard < K) : s.encard < K := by
  obtain ⟨hfin, hlt⟩ := encard_lt_coe_iff_finite_ncard_lt.mp h
  rw [ncard_image_of_injective s hf] at hlt
  exact encard_lt_coe_iff_finite_ncard_lt.mpr ⟨hfin.of_finite_image hf.injOn, hlt⟩

/-- **Exact restriction invariance of `RectangleFree`.** Fixing any coordinate subset `O` to any
assignment `a : O → U` preserves `K`-rectangle-freeness with the exact same threshold `K`. -/
theorem RectangleFree.restrictSlice {S : Set (ι → U)} {K : ℕ} (hS : RectangleFree S K)
    (O : Set ι) (a : O → U) : RectangleFree (Frontier.restrictSlice S O a) K := by
  intro Y A B hAB
  have himg :
      rectangle (Subtype.val '' Y) (liftSliceLeft Y '' A) (liftSliceRight a Y '' B) ⊆ S := by
    rw [← image_extendAssign_rectangle]
    rintro _ ⟨y, hy, rfl⟩
    exact hAB hy
  rcases hS _ _ _ himg with hL | hR
  · exact Or.inl (encard_lt_of_image_injective (liftSliceLeft_injective Y) hL)
  · exact Or.inr (encard_lt_of_image_injective (liftSliceRight_injective a Y) hR)

/-- **Exact restriction invariance of `RectangleBias`.** Fixing any coordinate subset `O` to any
assignment `a : O → U` preserves `(K, b)`-rectangle-bias on `restrictSlice S O a`. -/
theorem RectangleBias.restrictSlice {S : Set (ι → U)} {K : ℕ} {b : ℝ}
    (hS : RectangleBias S K b) (O : Set ι) (a : O → U) :
    RectangleBias (Frontier.restrictSlice S O a) K b := by
  intro Y A B hA hB
  have hA' : K ≤ (liftSliceLeft Y '' A).ncard := by
    rwa [ncard_image_of_injective A (liftSliceLeft_injective Y)]
  have hB' : K ≤ (liftSliceRight a Y '' B).ncard := by
    rwa [ncard_image_of_injective B (liftSliceRight_injective a Y)]
  have hbias := hS (Subtype.val '' Y) (liftSliceLeft Y '' A) (liftSliceRight a Y '' B) hA' hB'
  rw [← image_extendAssign_rectangle] at hbias
  have hinj := extendAssign_injective O a
  have hcard1 : (extendAssign O a '' rectangle Y A B).ncard = (rectangle Y A B).ncard :=
    ncard_image_of_injective _ hinj
  have hinter : extendAssign O a '' (rectangle Y A B ∩ Frontier.restrictSlice S O a) =
      extendAssign O a '' rectangle Y A B ∩ S := by
    ext z
    constructor
    · rintro ⟨y, ⟨hyR, hyS⟩, rfl⟩
      exact ⟨⟨y, hyR, rfl⟩, hyS⟩
    · rintro ⟨⟨y, hyR, rfl⟩, hzS⟩
      exact ⟨y, ⟨hyR, hzS⟩, rfl⟩
  have hcard2 : (extendAssign O a '' rectangle Y A B ∩ S).ncard =
      (rectangle Y A B ∩ Frontier.restrictSlice S O a).ncard := by
    rw [← hinter, ncard_image_of_injective _ hinj]
  rwa [hcard1, hcard2] at hbias

/-- **Pigeonhole dense slice.** Over finite coordinates and a nonempty finite alphabet, some
assignment `a : O → U` gives `|S| ≤ |U| ^ |O| · |restrictSlice S O a|`. -/
theorem exists_le_mul_ncard_restrictSlice [Finite ι] [Finite U] [Nonempty U] (S : Set (ι → U))
    (O : Set ι) :
    ∃ a : O → U, S.ncard ≤ Nat.card U ^ O.ncard * (restrictSlice S O a).ncard := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : Fintype U := Fintype.ofFinite U
  obtain ⟨a₀, ha₀⟩ := Finite.exists_max (fun a : O → U => (restrictSlice S O a).ncard)
  refine ⟨a₀, ?_⟩
  have hpart : S.ncard = ∑ a : O → U, (restrictSlice S O a).ncard := by
    have hfib := ncard_eq_sum_ncard_fiberwise (f := O.domRestrict) (s := S) (toFinite S)
      (t := Finset.univ) fun x _ => Finset.mem_univ _
    rw [hfib]
    refine Finset.sum_congr rfl fun a _ => ?_
    have himg : extendAssign O a '' restrictSlice S O a = {x ∈ S | O.domRestrict x = a} := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨hy, domRestrict_extendAssign_left O a y⟩
      · rintro ⟨hx, rfl⟩
        exact ⟨Oᶜ.domRestrict x, by simpa [restrictSlice] using hx, extendAssign_domRestrict O x⟩
    rw [← himg, ncard_image_of_injective _ (extendAssign_injective O a)]
  have hcardO : Fintype.card (O → U) = Nat.card U ^ O.ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_coe_set_eq]
  calc S.ncard
      = ∑ a : O → U, (restrictSlice S O a).ncard := hpart
    _ ≤ ∑ _a : O → U, (restrictSlice S O a₀).ncard :=
        Finset.sum_le_sum fun a _ => ha₀ a
    _ = Nat.card U ^ O.ncard * (restrictSlice S O a₀).ncard := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, hcardO]

end RestrictSlice

/-! ### Shared sweep transition-capacity and logarithmic width helpers -/

private theorem ncard_pi_univ_le {k : ℕ} {α : Type*} [Finite α] (F : Fin k → Set α) {C : ℕ}
    (hF : ∀ p, (F p).ncard ≤ C) : (Set.univ.pi F).ncard ≤ C ^ k := by
  induction k with
  | zero =>
    have : Subsingleton (Fin 0 → α) := inferInstance
    calc (Set.univ.pi F).ncard
        ≤ (Set.univ : Set (Fin 0 → α)).ncard := ncard_le_ncard (subset_univ _) (toFinite _)
      _ ≤ 1 := by
          rw [ncard_univ, Nat.card_eq_fintype_card]
          exact Fintype.card_le_one_iff_subsingleton.mpr inferInstance
      _ = C ^ 0 := (pow_zero C).symm
  | succ k ih =>
    let splitEquiv : (Fin (k + 1) → α) ≃ α × (Fin k → α) :=
      Fin.consEquiv (fun _ => α) |>.symm
    have hsub : splitEquiv '' Set.univ.pi F ⊆ F 0 ×ˢ Set.univ.pi (fun p : Fin k => F p.succ) := by
      rintro _ ⟨g, hg, rfl⟩
      exact ⟨hg 0 (mem_univ _), fun p _ => hg p.succ (mem_univ _)⟩
    calc (Set.univ.pi F).ncard
        = (splitEquiv '' Set.univ.pi F).ncard :=
          (ncard_image_of_injective _ splitEquiv.injective).symm
      _ ≤ (F 0 ×ˢ Set.univ.pi (fun p : Fin k => F p.succ)).ncard :=
          ncard_le_ncard hsub ((toFinite (F 0)).prod (toFinite _))
      _ = (F 0).ncard * (Set.univ.pi fun p : Fin k => F p.succ).ncard := ncard_prod
      _ ≤ C * C ^ k := Nat.mul_le_mul (hF 0) (ih (fun p => F p.succ) fun p => hF p.succ)
      _ = C ^ (k + 1) := (pow_succ' C k).symm

/-- Codes `(a, q)` with `q p ∈ fiber p a` for every `p` number at most `|H| · C ^ k` when every
fiber has at most `C` elements. -/
private theorem ncard_fiberCodes_le {k : ℕ} {H α : Type*} [Fintype H] [Finite α]
    (fiber : Fin k → H → Set α) {C : ℕ} (hC : ∀ p a, (fiber p a).ncard ≤ C) :
    {z : H × (Fin k → α) | z.2 ∈ Set.univ.pi fun p => fiber p z.1}.ncard ≤
      Fintype.card H * C ^ k := by
  classical
  calc _ = ∑ a : H,
        {z ∈ {z : H × (Fin k → α) | z.2 ∈ Set.univ.pi fun p => fiber p z.1} | z.1 = a}.ncard :=
        ncard_eq_sum_ncard_fiberwise (f := Prod.fst) (toFinite _) fun _ _ => Finset.mem_univ _
    _ ≤ ∑ _a : H, C ^ k := Finset.sum_le_sum fun a _ => by
        refine le_trans (ncard_le_ncard_of_injOn Prod.snd (fun z hz => ?_)
          (fun z₁ hz₁ z₂ hz₂ h => Prod.ext (hz₁.2.trans hz₂.2.symm) h) (toFinite _))
          (ncard_pi_univ_le (fun p => fiber p a) fun p => hC p a)
        rw [← hz.2]
        exact hz.1
    _ = Fintype.card H * C ^ k := by simp

/-- **Sweep bound from per-step state-fiber capacity.** If `W : Sweep S M` has `0 < W.length` and
at most `|U| ^ |W.newly t| · F` transitions at each step `t < W.length`, then for any
`K`-rectangle-free `S`,
`|S| ≤ (K - 1) ^ 2 · (∑_{t < W.length} |U| ^ |W.newly t|) · F`. -/
theorem Sweep.ncard_le_of_ncard_transition_le {ι U M : Type*} [Finite ι] [Finite U]
    {S : Set (ι → U)} (W : Sweep S M) (hL : 0 < W.length) {F K : ℕ}
    (htrans : ∀ t < W.length, (W.transition t '' S).ncard ≤ Nat.card U ^ (W.newly t).ncard * F)
    (hS : RectangleFree S K) :
    S.ncard ≤
      (K - 1) ^ 2 * (∑ t ∈ Finset.range W.length, Nat.card U ^ (W.newly t).ncard) * F := by
  rcases S.eq_empty_or_nonempty with hempty | hne
  · simp [hempty]
  by_cases hK : K ≤ S.ncard
  · calc S.ncard
        ≤ (K - 1) ^ 2 * W.transitionCount := W.ncard_le hS hK
      _ ≤ (K - 1) ^ 2 * ∑ t ∈ Finset.range W.length, Nat.card U ^ (W.newly t).ncard * F :=
          Nat.mul_le_mul_left _ (Finset.sum_le_sum fun t ht => htrans t (Finset.mem_range.mp ht))
      _ = (K - 1) ^ 2 * (∑ t ∈ Finset.range W.length, Nat.card U ^ (W.newly t).ncard) * F := by
          rw [← Finset.sum_mul, mul_assoc]
  · obtain ⟨x, hx⟩ := hne
    have hK1 : 1 < K := hS.one_lt ⟨x, hx⟩
    have h1 : 1 ≤ Nat.card U ^ (W.newly 0).ncard * F := by
      calc 1 ≤ (W.transition 0 '' S).ncard :=
            (ncard_pos ((toFinite S).image _)).mpr ⟨_, x, hx, rfl⟩
        _ ≤ Nat.card U ^ (W.newly 0).ncard * F := htrans 0 hL
    have hsum1 : 1 ≤ (∑ t ∈ Finset.range W.length, Nat.card U ^ (W.newly t).ncard) * F := by
      rw [Finset.sum_mul]
      exact h1.trans (Finset.single_le_sum (f := fun t => Nat.card U ^ (W.newly t).ncard * F)
        (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hL))
    calc S.ncard ≤ K - 1 := by omega
      _ ≤ (K - 1) ^ 2 * 1 := by
          rw [sq, mul_one]
          exact Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ (K - 1) ^ 2 * (∑ t ∈ Finset.range W.length, Nat.card U ^ (W.newly t).ncard) * F := by
          rw [mul_assoc]
          exact Nat.mul_le_mul_left _ hsum1

private theorem sum_pow_newly_le {ι : Type*} (U : Type*) [Finite U] [Nonempty U]
    {L : ℕ} {newly : ℕ → Set ι} (hunit : ∀ t < L, (newly t).ncard ≤ 1) :
    (∑ t ∈ Finset.range L, Nat.card U ^ (newly t).ncard) ≤ L * Nat.card U := by
  calc (∑ t ∈ Finset.range L, Nat.card U ^ (newly t).ncard)
      ≤ ∑ _t ∈ Finset.range L, Nat.card U ^ 1 :=
        Finset.sum_le_sum fun t ht =>
          Nat.pow_le_pow_right Nat.card_pos (hunit t (Finset.mem_range.mp ht))
    _ = L * Nat.card U := by simp

private theorem le_mul_logb_of_ncard_le {ι U : Type*} [Finite ι] [Finite U] [Nontrivial U]
    {S : Set (ι → U)} {K L m E : ℕ} (hL : 0 < L) (hm : 0 < m)
    (hS : RectangleFree S K) (hne : S.Nonempty)
    (hcnt : S.ncard ≤ (K - 1) ^ 2 * L * Nat.card U * m ^ E) :
    Real.logb (Nat.card U) S.ncard - 2 * Real.logb (Nat.card U) K -
        Real.logb (Nat.card U) L - 1 ≤
      (E : ℝ) * Real.logb (Nat.card U) m := by
  have hq1 : (1 : ℝ) < Nat.card U := by exact_mod_cast (Finite.one_lt_card (α := U))
  have hK1 : 1 < K := hS.one_lt hne
  have hS_pos : 0 < S.ncard := (ncard_pos (toFinite _)).mpr hne
  have hcnt' : S.ncard ≤ K ^ 2 * L * Nat.card U * m ^ E :=
    hcnt.trans (by gcongr; omega)
  have hcntR : (S.ncard : ℝ) ≤ (K : ℝ) ^ 2 * L * Nat.card U * (m : ℝ) ^ E := by
    exact_mod_cast hcnt'
  have hlog := Real.logb_le_logb_of_le hq1 (by exact_mod_cast hS_pos) hcntR
  rw [Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_mul (by positivity) (by positivity),
    Real.logb_pow, Real.logb_pow, Real.logb_self_eq_one hq1] at hlog
  cast_linarith

/-- A deterministic relation `R : M → M → Prop` on a finite state space `M` has at most `|M|`
related pairs. -/
private theorem ncard_fiber_le_card_of_deterministic {M : Type*} [Finite M] {R : M → M → Prop}
    (hdet : ∀ m m₁ m₂, R m m₁ → R m m₂ → m₁ = m₂) :
    {q : M × M | R q.1 q.2}.ncard ≤ Nat.card M := by
  calc {q : M × M | R q.1 q.2}.ncard
      ≤ (Set.univ : Set M).ncard := by
        refine ncard_le_ncard_of_injOn Prod.fst (fun _ _ => mem_univ _) ?_ (toFinite _)
        rintro ⟨m₁, m₁'⟩ h₁ ⟨m₂, m₂'⟩ h₂ (rfl : m₁ = m₂)
        exact Prod.ext rfl (hdet m₁ m₁' m₂' h₁ h₂)
    _ = Nat.card M := ncard_univ M

/-! ### Alternating (`boustrophedon`) `k`-pass branching programs -/

/-- Base coordinate index read at local step `s` of pass `p` in an alternating `k`-pass schedule of
length `T`: `s` when `p` is even, and `T - 1 - s` when `p` is odd. -/
@[expose] def passCoord (T p s : ℕ) : ℕ :=
  if p % 2 = 0 then s else T - 1 - s

/-- Local step of pass `p` that reads coordinate block `t < T` in an alternating schedule. -/
private def passStep (T p t : ℕ) : ℕ :=
  if p % 2 = 0 then t else T - 1 - t

/-- Layer of pass `p` separating `revealed τ` from `(revealed τ)ᶜ` in an alternating schedule. -/
@[expose] def passBoundary (T p τ : ℕ) : ℕ :=
  if p % 2 = 0 then τ else T - τ

private theorem passCoord_passStep {T : ℕ} (p : ℕ) {t : ℕ} (ht : t < T) :
    passCoord T p (passStep T p t) = t := by
  unfold passCoord passStep
  split_ifs <;> omega

/-- A *layered alternating `k`-pass nondeterministic branching program* (`boustrophedon` schedule)
over inputs `ι → U` with state space `M`. Even passes scan `0, ..., length - 1` forward; odd passes
scan `length - 1, ..., 0` backward; consecutive passes share their turnaround state. -/
structure AlternatingPassNBP (ι U M : Type*) where
  /-- Number of passes `k ≥ 1`. -/
  passes : ℕ
  /-- At least one pass is performed. -/
  passes_pos : 0 < passes
  /-- Number of coordinate blocks per pass. -/
  length : ℕ
  /-- Monotone coordinate filtration `∅ = revealed 0 ⊆ ... ⊆ revealed length = univ`. -/
  revealed : ℕ → Set ι
  /-- Nothing is revealed before block `0`. -/
  revealed_zero : revealed 0 = ∅
  /-- Everything is revealed by block `length`. -/
  revealed_length : revealed length = univ
  /-- Revealed coordinates grow monotonically. -/
  revealed_mono : Monotone revealed
  /-- Initial state at the start of pass `0`. -/
  start : M
  /-- Accepting state at the end of pass `passes - 1`. -/
  accept : M
  /-- `Edge p s m a m'` holds when pass `p` at local step `s` transitions from `m` to `m'` upon
  reading `a` on block `passCoord length p s`. -/
  Edge : (p s : ℕ) → M →
    (↥(revealed (passCoord length p s + 1) \ revealed (passCoord length p s)) → U) → M → Prop

namespace AlternatingPassNBP

variable {ι U M : Type*} (P : AlternatingPassNBP ι U M)

/-- Coordinates in block `t`: `revealed (t + 1) \ revealed t`. -/
abbrev newly (t : ℕ) : Set ι :=
  P.revealed (t + 1) \ P.revealed t

/-- Coordinates read at local step `s` of pass `p`. -/
abbrev stepCoords (p s : ℕ) : Set ι :=
  P.newly (passCoord P.length p s)

/-- `γ` is an accepting `k`-pass trajectory for input `x`. -/
structure IsAcceptingPath (x : ι → U) (γ : ℕ → ℕ → M) : Prop where
  /-- Pass `0` starts at `P.start`. -/
  start : γ 0 0 = P.start
  /-- Pass `passes - 1` ends at `P.accept`. -/
  accept : γ (P.passes - 1) P.length = P.accept
  /-- Consecutive passes share their turnaround state. -/
  turnaround : ∀ p, p + 1 < P.passes → γ (p + 1) 0 = γ p P.length
  /-- Every local step follows a valid labelled edge. -/
  edge : ∀ p < P.passes, ∀ s < P.length,
    P.Edge p s (γ p s) ((P.stepCoords p s).domRestrict x) (γ p (s + 1))

/-- The inputs accepted by `P`. -/
@[expose] def accepted : Set (ι → U) :=
  {x | ∃ γ, P.IsAcceptingPath x γ}

/-- Per-label state-transition capacity bound `C` at every pass and step. -/
@[expose] def HasFiberBound (C : ℕ) : Prop :=
  ∀ p < P.passes, ∀ s < P.length, ∀ a : P.stepCoords p s → U,
    {q : M × M | P.Edge p s q.1 a q.2}.ncard ≤ C

/-- `P` is deterministic when every `(p, s, m, a)` has at most one successor state `m'`. -/
@[expose] def Deterministic : Prop :=
  ∀ p < P.passes, ∀ s < P.length, ∀ m a m₁ m₂,
    P.Edge p s m a m₁ → P.Edge p s m a m₂ → m₁ = m₂

/-- A deterministic alternating `k`-pass program over a finite state space `M` has fiber bound
`Nat.card M`. -/
theorem Deterministic.hasFiberBound [Finite M] {P : AlternatingPassNBP ι U M}
    (hdet : P.Deterministic) : P.HasFiberBound (Nat.card M) :=
  fun p hp s hs a => ncard_fiber_le_card_of_deterministic fun m => hdet p hp s hs m a

private theorem newly_subset_revealed {s t : ℕ} (h : s < t) : P.newly s ⊆ P.revealed t :=
  fun _ hi => P.revealed_mono (Nat.succ_le_of_lt h) hi.1

private theorem newly_subset_compl {s t : ℕ} (h : t ≤ s) : P.newly s ⊆ (P.revealed t)ᶜ :=
  fun _ hi hit => hi.2 (P.revealed_mono h hit)

private theorem revealed_eq_univ_of_le {t : ℕ} (ht : P.length ≤ t) : P.revealed t = univ :=
  univ_subset_iff.mp (P.revealed_length ▸ P.revealed_mono ht)

/-- **Boustrophedon splicing.** Two accepting trajectories agreeing at the `k` moving boundary
states `passBoundary P.length p τ` (`0 < τ < P.length`) splice across the cut `P.revealed τ` with
no extra turnaround state. -/
theorem IsAcceptingPath.splice {P : AlternatingPassNBP ι U M} {x y z : ι → U} {γ δ : ℕ → ℕ → M}
    (hγ : P.IsAcceptingPath x γ) (hδ : P.IsAcceptingPath y δ) {τ : ℕ} (hτ0 : 0 < τ)
    (hτT : τ < P.length)
    (hagree : ∀ p < P.passes,
      γ p (passBoundary P.length p τ) = δ p (passBoundary P.length p τ))
    (hzx : EqOn z x (P.revealed τ)) (hzy : EqOn z y (P.revealed τ)ᶜ) :
    P.IsAcceptingPath z fun p s =>
      if p % 2 = 0 then (if s ≤ τ then γ p s else δ p s)
      else (if s ≤ P.length - τ then δ p s else γ p s) := by
  have h1 : ¬P.length ≤ τ := by omega
  have h2 : ¬P.length ≤ P.length - τ := by omega
  have hdomx {p s : ℕ} (h : passCoord P.length p s < τ) :
      (P.stepCoords p s).domRestrict z = (P.stepCoords p s).domRestrict x :=
    funext fun i => hzx (P.newly_subset_revealed h i.property)
  have hdomy {p s : ℕ} (h : τ ≤ passCoord P.length p s) :
      (P.stepCoords p s).domRestrict z = (P.stepCoords p s).domRestrict y :=
    funext fun i => hzy (P.newly_subset_compl h i.property)
  refine ⟨by simp [hγ.start], ?_, fun p hp1 => ?_, fun p hp s hs => ?_⟩
  · by_cases hp : (P.passes - 1) % 2 = 0 <;> simp [hp, h1, h2, hγ.accept, hδ.accept]
  · by_cases hp : p % 2 = 0
    · simp [hp, show (p + 1) % 2 ≠ 0 by omega, h1, hδ.turnaround p hp1]
    · simp [hp, show (p + 1) % 2 = 0 by omega, h2, hγ.turnaround p hp1]
  by_cases heven : p % 2 = 0
  · simp only [heven, ↓reduceIte]
    have hcoord : passCoord P.length p s = s := by simp [passCoord, heven]
    rcases lt_or_ge s τ with hst | hts
    · rw [ite_eq_left hst.le, ite_eq_left (by omega : s + 1 ≤ τ), hdomx (by omega)]
      exact hγ.edge p hp s hs
    · have hsrc : (if s ≤ τ then γ p s else δ p s) = δ p s := by
        split_ifs with hle
        · obtain rfl : s = τ := by omega
          simpa [passBoundary, heven] using hagree p hp
        · rfl
      rw [hsrc, ite_eq_right (by omega : ¬s + 1 ≤ τ), hdomy (by omega)]
      exact hδ.edge p hp s hs
  · simp only [heven, ↓reduceIte]
    have hcoord : passCoord P.length p s = P.length - 1 - s := by simp [passCoord, heven]
    rcases lt_or_ge s (P.length - τ) with hst | hts
    · rw [ite_eq_left hst.le, ite_eq_left (by omega : s + 1 ≤ P.length - τ), hdomy (by omega)]
      exact hδ.edge p hp s hs
    · have hsrc : (if s ≤ P.length - τ then δ p s else γ p s) = γ p s := by
        split_ifs with hle
        · obtain rfl : s = P.length - τ := by omega
          simpa [passBoundary, heven] using (hagree p hp).symm
        · rfl
      rw [hsrc, ite_eq_right (by omega : ¬s + 1 ≤ P.length - τ), hdomx (by omega)]
      exact hγ.edge p hp s hs

open Classical in
/-- Chosen accepting trajectory for each accepted input. -/
private noncomputable def path (x : ι → U) : ℕ → ℕ → M :=
  if h : ∃ γ, P.IsAcceptingPath x γ then h.choose else fun _ _ => P.start

private theorem isAcceptingPath_path {x : ι → U} (hx : x ∈ P.accepted) :
    P.IsAcceptingPath x (P.path x) := by
  unfold path
  split_ifs with h
  · exact h.choose_spec
  · exact absurd hx h

/-- **Dynamic sweep of an alternating `k`-pass branching program.** At interior times
`0 < t < P.length`, the message records only the `k` active pass boundary states; at `t = 0` and
`t ≥ P.length`, the message is `none`. -/
noncomputable def sweep : Sweep P.accepted (Option (Fin P.passes → M)) where
  length := P.length
  revealed := P.revealed
  revealed_zero := P.revealed_zero
  revealed_length := P.revealed_length
  message t x :=
    open Classical in
    if 0 < t ∧ t < P.length then
      some fun p => P.path x p.val (passBoundary P.length p.val t)
    else none
  message_length _ _ _ _ := by simp
  splice t x hx y hy hmsg z hzx hzy := by
    classical
    by_cases ht0 : t = 0
    · subst t
      have hzy_eq : z = y := funext fun i => hzy (by simp [P.revealed_zero])
      exact hzy_eq ▸ hy
    · by_cases htT : P.length ≤ t
      · have hzx_eq : z = x := funext fun i => hzx (by simp [P.revealed_eq_univ_of_le htT])
        exact hzx_eq ▸ hx
      · have hcond : 0 < t ∧ t < P.length := ⟨Nat.pos_of_ne_zero ht0, not_le.mp htT⟩
        simp only [hcond, and_self, ↓reduceIte, Option.some.injEq] at hmsg
        refine ⟨_, (P.isAcceptingPath_path hx).splice (P.isAcceptingPath_path hy) hcond.1 hcond.2
          (fun p hp => congrFun hmsg ⟨p, hp⟩) hzx hzy⟩

/-- At step `t < P.length`, the number of sweep transitions is at most
`|U| ^ |newly t| · C ^ passes` under `P.HasFiberBound C`. -/
theorem ncard_transition_sweep_le [Finite ι] [Finite U] [Finite M] {C : ℕ}
    (hC : P.HasFiberBound C) {t : ℕ} (ht : t < P.length) :
    (P.sweep.transition t '' P.accepted).ncard ≤
      Nat.card U ^ (P.newly t).ncard * C ^ P.passes := by
  classical
  let _ : Fintype (P.newly t → U) := Fintype.ofFinite _
  let castLabel (p : Fin P.passes) (a : P.newly t → U) :
      P.stepCoords p.val (passStep P.length p.val t) → U :=
    fun i => a ⟨i.val, by simpa only [stepCoords, passCoord_passStep p.val ht] using i.property⟩
  let fiber (p : Fin P.passes) (a : P.newly t → U) : Set (M × M) :=
    {q | P.Edge p.val (passStep P.length p.val t) q.1 (castLabel p a) q.2}
  let code (x : ι → U) : (P.newly t → U) × (Fin P.passes → M × M) :=
    ((P.newly t).domRestrict x, fun p =>
      (P.path x p.val (passStep P.length p.val t),
        P.path x p.val (passStep P.length p.val t + 1)))
  have hfactors : (P.sweep.transition t '' P.accepted).ncard ≤ (code '' P.accepted).ncard := by
    refine ncard_image_le_ncard_image_of_factorsThrough (toFinite _) fun x _ y _ hxy => ?_
    obtain ⟨hnew, hpairs⟩ := Prod.mk.injEq .. |>.mp hxy
    have hb (p : Fin P.passes) (u : ℕ)
        (hu : u = passStep P.length p.val t ∨ u = passStep P.length p.val t + 1) :
        P.path x p.val u = P.path y p.val u := by
      have hp := Prod.mk.injEq .. |>.mp (congrFun hpairs p)
      rcases hu with rfl | rfl
      exacts [hp.1, hp.2]
    refine Prod.ext ?_ (Prod.ext ?_ hnew) <;> dsimp only [Sweep.transition, sweep] <;> split_ifs
    all_goals first
      | exact congrArg some <| funext fun p =>
          hb p _ (by unfold passBoundary passStep; split_ifs <;> omega)
      | rfl
  have hstep (p : Fin P.passes) : passStep P.length p.val t < P.length := by
    unfold passStep; split_ifs <;> omega
  let validCodes : Set ((P.newly t → U) × (Fin P.passes → M × M)) :=
    {z | z.2 ∈ Set.univ.pi fun p => fiber p z.1}
  have hsub : code '' P.accepted ⊆ validCodes := by
    rintro _ ⟨x, hx, rfl⟩ p -
    exact (P.isAcceptingPath_path hx).edge p.val p.isLt _ (hstep p)
  have hcardU : Fintype.card (P.newly t → U) = Nat.card U ^ (P.newly t).ncard := by
    rw [← Nat.card_eq_fintype_card, Nat.card_fun, Nat.card_coe_set_eq]
  calc (P.sweep.transition t '' P.accepted).ncard
      ≤ (code '' P.accepted).ncard := hfactors
    _ ≤ validCodes.ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ _ := ncard_fiberCodes_le fiber fun p a => hC p.val p.isLt _ (hstep p) (castLabel p a)
    _ = Nat.card U ^ (P.newly t).ncard * C ^ P.passes := by rw [hcardU]

/-- **Alternating `k`-pass rectangle bound.** If `P.accepted` is `K`-rectangle-free and `P` has
per-label fiber bound `C`, then
`|accepted| ≤ (K - 1) ^ 2 · (∑_{t < length} |U| ^ |newly t|) · C ^ passes`. -/
theorem ncard_accepted_le_of_hasFiberBound [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length)
    {C K : ℕ} (hC : P.HasFiberBound C) (hS : RectangleFree P.accepted K) :
    P.accepted.ncard ≤
      (K - 1) ^ 2 * (∑ t ∈ Finset.range P.length, Nat.card U ^ (P.newly t).ncard) *
        C ^ P.passes :=
  P.sweep.ncard_le_of_ncard_transition_le hL (fun _ ht => P.ncard_transition_sweep_le hC ht) hS

/-- **Deterministic alternating `k`-pass rectangle bound (unit coordinate steps).** When each block
`newly t` reads at most one coordinate and `P` is deterministic,
`|accepted| ≤ (K - 1) ^ 2 · length · |U| · |M| ^ passes`. -/
theorem ncard_accepted_le_deterministic [Finite ι] [Finite U] [Nonempty U] [Finite M]
    (hdet : P.Deterministic) (hL : 0 < P.length) (hunit : ∀ t < P.length, (P.newly t).ncard ≤ 1)
    {K : ℕ} (hS : RectangleFree P.accepted K) :
    P.accepted.ncard ≤ (K - 1) ^ 2 * P.length * Nat.card U * Nat.card M ^ P.passes := by
  calc P.accepted.ncard
      ≤ (K - 1) ^ 2 * (∑ t ∈ Finset.range P.length, Nat.card U ^ (P.newly t).ncard) *
          Nat.card M ^ P.passes :=
        P.ncard_accepted_le_of_hasFiberBound hL hdet.hasFiberBound hS
    _ ≤ (K - 1) ^ 2 * (P.length * Nat.card U) * Nat.card M ^ P.passes :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (sum_pow_newly_le U hunit))
    _ = (K - 1) ^ 2 * P.length * Nat.card U * Nat.card M ^ P.passes := by ring

/-- **Alternating `k`-pass logarithmic state-width lower bound (`w ≥ n / k - o(n)`).** Over a
finite alphabet `U` with `q = |U| ≥ 2`, a deterministic alternating `k`-pass program reading at
most one coordinate per step on a nonempty `K`-rectangle-free set satisfies
`log_q |accepted| - 2 log_q K - log_q length - 1 ≤ passes · log_q |M|`. -/
theorem le_passes_mul_logb_card [Finite ι] [Finite U] [Nontrivial U] [Finite M]
    (hdet : P.Deterministic) (hL : 0 < P.length) (hunit : ∀ t < P.length, (P.newly t).ncard ≤ 1)
    {K : ℕ} (hS : RectangleFree P.accepted K) (hne : P.accepted.Nonempty) :
    Real.logb (Nat.card U) P.accepted.ncard - 2 * Real.logb (Nat.card U) K -
        Real.logb (Nat.card U) P.length - 1 ≤
      (P.passes : ℝ) * Real.logb (Nat.card U) (Nat.card M) :=
  le_mul_logb_of_ncard_le hL (@Nat.card_pos M ⟨P.start⟩ _) hS hne
    (P.ncard_accepted_le_deterministic hdet hL hunit hS)

end AlternatingPassNBP

/-! ### Same-order `k`-pass branching programs -/

/-- A *layered same-order `k`-pass nondeterministic branching program* over inputs `ι → U` with
state space `M`. Every pass `0 ≤ p < passes` scans `0, ..., length - 1` in the same forward order,
with turnaround identification `γ (p + 1) 0 = γ p length`. -/
structure SameOrderPassNBP (ι U M : Type*) where
  /-- Number of passes `k ≥ 1`. -/
  passes : ℕ
  /-- At least one pass is performed. -/
  passes_pos : 0 < passes
  /-- Number of coordinate blocks per pass. -/
  length : ℕ
  /-- Monotone coordinate filtration `∅ = revealed 0 ⊆ ... ⊆ revealed length = univ`. -/
  revealed : ℕ → Set ι
  /-- Nothing is revealed before block `0`. -/
  revealed_zero : revealed 0 = ∅
  /-- Everything is revealed by block `length`. -/
  revealed_length : revealed length = univ
  /-- Revealed coordinates grow monotonically. -/
  revealed_mono : Monotone revealed
  /-- Initial state at the start of pass `0`. -/
  start : M
  /-- Accepting state at the end of pass `passes - 1`. -/
  accept : M
  /-- `Edge p s m a m'` holds when pass `p` at step `s` transitions from `m` to `m'` upon reading
  `a` on `revealed (s + 1) \ revealed s`. -/
  Edge : (p s : ℕ) → M → (↥(revealed (s + 1) \ revealed s) → U) → M → Prop

namespace SameOrderPassNBP

variable {ι U M : Type*} (P : SameOrderPassNBP ι U M)

/-- Coordinates read at step `t`: `revealed (t + 1) \ revealed t`. -/
abbrev newly (t : ℕ) : Set ι :=
  P.revealed (t + 1) \ P.revealed t

/-- `γ` is an accepting same-order `k`-pass trajectory for input `x`. -/
structure IsAcceptingPath (x : ι → U) (γ : ℕ → ℕ → M) : Prop where
  /-- Pass `0` starts at `P.start`. -/
  start : γ 0 0 = P.start
  /-- Pass `passes - 1` ends at `P.accept`. -/
  accept : γ (P.passes - 1) P.length = P.accept
  /-- Consecutive passes share their turnaround state. -/
  turnaround : ∀ p, p + 1 < P.passes → γ (p + 1) 0 = γ p P.length
  /-- Every step follows a valid labelled edge. -/
  edge : ∀ p < P.passes, ∀ s < P.length,
    P.Edge p s (γ p s) ((P.newly s).domRestrict x) (γ p (s + 1))

/-- The inputs accepted by `P`. -/
@[expose] def accepted : Set (ι → U) :=
  {x | ∃ γ, P.IsAcceptingPath x γ}

/-- Per-label state-transition capacity bound `C` at every pass and step. -/
@[expose] def HasFiberBound (C : ℕ) : Prop :=
  ∀ p < P.passes, ∀ s < P.length, ∀ a : P.newly s → U,
    {q : M × M | P.Edge p s q.1 a q.2}.ncard ≤ C

/-- `P` is deterministic when every `(p, s, m, a)` has at most one successor state `m'`. -/
@[expose] def Deterministic : Prop :=
  ∀ p < P.passes, ∀ s < P.length, ∀ m a m₁ m₂,
    P.Edge p s m a m₁ → P.Edge p s m a m₂ → m₁ = m₂

/-- A deterministic same-order `k`-pass program over a finite state space `M` has fiber bound
`Nat.card M`. -/
theorem Deterministic.hasFiberBound [Finite M] {P : SameOrderPassNBP ι U M}
    (hdet : P.Deterministic) : P.HasFiberBound (Nat.card M) :=
  fun p hp s hs a => ncard_fiber_le_card_of_deterministic fun m => hdet p hp s hs m a

private theorem newly_subset_revealed {s t : ℕ} (h : s < t) : P.newly s ⊆ P.revealed t :=
  fun _ hi => P.revealed_mono (Nat.succ_le_of_lt h) hi.1

private theorem newly_subset_compl {s t : ℕ} (h : t ≤ s) : P.newly s ⊆ (P.revealed t)ᶜ :=
  fun _ hi hit => hi.2 (P.revealed_mono h hit)

private theorem revealed_eq_univ_of_le {t : ℕ} (ht : P.length ≤ t) : P.revealed t = univ :=
  univ_subset_iff.mp (P.revealed_length ▸ P.revealed_mono ht)

/-- **Same-order `k`-pass splicing.** Two trajectories agreeing on both the `k` moving layer-`τ`
states and the `k - 1` inter-pass turnaround states splice across `P.revealed τ`
(`0 < τ < length`). -/
theorem IsAcceptingPath.splice {P : SameOrderPassNBP ι U M} {x y z : ι → U} {γ δ : ℕ → ℕ → M}
    (hγ : P.IsAcceptingPath x γ) (hδ : P.IsAcceptingPath y δ) {τ : ℕ} (hτT : τ < P.length)
    (hmove : ∀ p < P.passes, γ p τ = δ p τ)
    (hturn : ∀ p, p + 1 < P.passes → γ p P.length = δ p P.length)
    (hzx : EqOn z x (P.revealed τ)) (hzy : EqOn z y (P.revealed τ)ᶜ) :
    P.IsAcceptingPath z fun p s => if s ≤ τ then γ p s else δ p s := by
  have hnotT : ¬P.length ≤ τ := by omega
  refine ⟨by simp [hγ.start], by simp [hnotT, hδ.accept], ?_, ?_⟩
  · intro p hp1
    simp [hnotT, hγ.turnaround p hp1, hturn p hp1]
  · intro p hp s hs
    rcases lt_or_ge s τ with hst | hts
    · rw [ite_eq_left hst.le, ite_eq_left (by omega : s + 1 ≤ τ),
        show (P.newly s).domRestrict z = (P.newly s).domRestrict x from
          funext fun i => hzx (P.newly_subset_revealed hst i.property)]
      exact hγ.edge p hp s hs
    · have hsrc : (if s ≤ τ then γ p s else δ p s) = δ p s :=
        ite_eq_right_iff.2 fun hle => (le_antisymm hle hts) ▸ hmove p hp
      rw [hsrc, ite_eq_right (by omega : ¬s + 1 ≤ τ),
        show (P.newly s).domRestrict z = (P.newly s).domRestrict y from
          funext fun i => hzy (P.newly_subset_compl hts i.property)]
      exact hδ.edge p hp s hs

open Classical in
/-- Chosen accepting trajectory for each accepted input. -/
private noncomputable def path (x : ι → U) : ℕ → ℕ → M :=
  if h : ∃ γ, P.IsAcceptingPath x γ then h.choose else fun _ _ => P.start

private theorem isAcceptingPath_path {x : ι → U} (hx : x ∈ P.accepted) :
    P.IsAcceptingPath x (P.path x) := by
  unfold path
  split_ifs with h
  · exact h.choose_spec
  · exact absurd hx h

/-- **Dynamic sweep of a same-order `k`-pass branching program.** At interior times
`0 < t < P.length`, the message records the `k` moving layer-`t` states together with the `k - 1`
turnaround states `(path x p length)_{p < k - 1}`. -/
noncomputable def sweep :
    Sweep P.accepted (Option ((Fin P.passes → M) × (Fin (P.passes - 1) → M))) where
  length := P.length
  revealed := P.revealed
  revealed_zero := P.revealed_zero
  revealed_length := P.revealed_length
  message t x :=
    open Classical in
    if 0 < t ∧ t < P.length then
      some (fun p => P.path x p.val t, fun p => P.path x p.val P.length)
    else none
  message_length _ _ _ _ := by simp
  splice t x hx y hy hmsg z hzx hzy := by
    classical
    by_cases ht0 : t = 0
    · subst t
      have hzy_eq : z = y := funext fun i => hzy (by simp [P.revealed_zero])
      exact hzy_eq ▸ hy
    · by_cases htT : P.length ≤ t
      · have hzx_eq : z = x := funext fun i => hzx (by simp [P.revealed_eq_univ_of_le htT])
        exact hzx_eq ▸ hx
      · have hcond : 0 < t ∧ t < P.length := ⟨Nat.pos_of_ne_zero ht0, not_le.mp htT⟩
        simp only [hcond, and_self, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at hmsg
        refine ⟨_, (P.isAcceptingPath_path hx).splice (P.isAcceptingPath_path hy) hcond.2
          (fun p hp => congrFun hmsg.1 ⟨p, hp⟩)
          (fun p hp1 => congrFun hmsg.2 ⟨p, by omega⟩) hzx hzy⟩

/-- At step `t < P.length`, the number of sweep transitions of a same-order `k`-pass program is at
most `|U| ^ |newly t| · |M| ^ (passes - 1) · C ^ passes` under `P.HasFiberBound C`: the `k - 1`
turnaround states stay fixed across step `t`, so they are counted once rather than twice. -/
theorem ncard_transition_sweep_le [Finite ι] [Finite U] [Finite M] {C : ℕ}
    (hC : P.HasFiberBound C) {t : ℕ} (ht : t < P.length) :
    (P.sweep.transition t '' P.accepted).ncard ≤
      Nat.card U ^ (P.newly t).ncard * Nat.card M ^ (P.passes - 1) * C ^ P.passes := by
  classical
  let _ : Fintype (P.newly t → U) := Fintype.ofFinite _
  let _ : Fintype (Fin (P.passes - 1) → M) := Fintype.ofFinite _
  let fiber (p : Fin P.passes) (a : (P.newly t → U) × (Fin (P.passes - 1) → M)) : Set (M × M) :=
    {q | P.Edge p.val t q.1 a.1 q.2}
  let code (x : ι → U) :
      ((P.newly t → U) × (Fin (P.passes - 1) → M)) × (Fin P.passes → M × M) :=
    (((P.newly t).domRestrict x, fun p => P.path x p.val P.length),
      fun p => (P.path x p.val t, P.path x p.val (t + 1)))
  have hfactors : (P.sweep.transition t '' P.accepted).ncard ≤ (code '' P.accepted).ncard := by
    refine ncard_image_le_ncard_image_of_factorsThrough (toFinite _) fun x _ y _ hxy => ?_
    obtain ⟨hhead, hpairs⟩ := Prod.mk.injEq .. |>.mp hxy
    obtain ⟨hnew, hturn⟩ := Prod.mk.injEq .. |>.mp hhead
    have hp (p : Fin P.passes) := congrFun hpairs p
    refine Prod.ext ?_ (Prod.ext ?_ hnew)
    · dsimp only [Sweep.transition, sweep]
      split_ifs with h1
      · congr 1
        refine Prod.ext (funext fun p => (Prod.mk.injEq .. |>.mp (hp p)).1) hturn
      · rfl
    · dsimp only [Sweep.transition, sweep]
      split_ifs with h2
      · congr 1
        refine Prod.ext (funext fun p => (Prod.mk.injEq .. |>.mp (hp p)).2) hturn
      · rfl
  let validCodes :
      Set (((P.newly t → U) × (Fin (P.passes - 1) → M)) × (Fin P.passes → M × M)) :=
    {z | z.2 ∈ Set.univ.pi fun p => fiber p z.1}
  have hsub : code '' P.accepted ⊆ validCodes := by
    rintro _ ⟨x, hx, rfl⟩ p -
    exact (P.isAcceptingPath_path hx).edge p.val p.isLt t ht
  have hcardHead :
      Fintype.card ((P.newly t → U) × (Fin (P.passes - 1) → M)) =
        Nat.card U ^ (P.newly t).ncard * Nat.card M ^ (P.passes - 1) := by
    rw [Fintype.card_prod, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card,
      Nat.card_fun, Nat.card_fun, Nat.card_coe_set_eq, Nat.card_eq_fintype_card (α := Fin _),
      Fintype.card_fin]
  calc (P.sweep.transition t '' P.accepted).ncard
      ≤ (code '' P.accepted).ncard := hfactors
    _ ≤ validCodes.ncard := ncard_le_ncard hsub (toFinite _)
    _ ≤ _ := ncard_fiberCodes_le fiber fun p a => hC p.val p.isLt t ht a.1
    _ = Nat.card U ^ (P.newly t).ncard * Nat.card M ^ (P.passes - 1) * C ^ P.passes := by
        rw [hcardHead]

/-- **Same-order `k`-pass rectangle bound.** If `P.accepted` is `K`-rectangle-free and `P` has
per-label fiber bound `C`, then
`|accepted| ≤ (K - 1) ^ 2 · (∑_{t < length} |U| ^ |newly t|) · |M| ^ (passes - 1) · C ^ passes`. -/
theorem ncard_accepted_le_of_hasFiberBound [Finite ι] [Finite U] [Finite M] (hL : 0 < P.length)
    {C K : ℕ} (hC : P.HasFiberBound C) (hS : RectangleFree P.accepted K) :
    P.accepted.ncard ≤
      (K - 1) ^ 2 * (∑ t ∈ Finset.range P.length, Nat.card U ^ (P.newly t).ncard) *
        Nat.card M ^ (P.passes - 1) * C ^ P.passes := by
  have h := P.sweep.ncard_le_of_ncard_transition_le hL
    (F := Nat.card M ^ (P.passes - 1) * C ^ P.passes)
    (fun _ ht => by rw [← mul_assoc]; exact P.ncard_transition_sweep_le hC ht) hS
  rwa [← mul_assoc] at h

/-- **Deterministic same-order `k`-pass rectangle bound (unit coordinate steps).** When each block
reads at most one coordinate and `P` is deterministic,
`|accepted| ≤ (K - 1) ^ 2 · length · |U| · |M| ^ (2 · passes - 1)`. -/
theorem ncard_accepted_le_deterministic [Finite ι] [Finite U] [Nonempty U] [Finite M]
    (hdet : P.Deterministic) (hL : 0 < P.length) (hunit : ∀ t < P.length, (P.newly t).ncard ≤ 1)
    {K : ℕ} (hS : RectangleFree P.accepted K) :
    P.accepted.ncard ≤
      (K - 1) ^ 2 * P.length * Nat.card U * Nat.card M ^ (2 * P.passes - 1) := by
  have hpow : Nat.card M ^ (P.passes - 1) * Nat.card M ^ P.passes =
      Nat.card M ^ (2 * P.passes - 1) := by
    rw [← pow_add]
    congr 1
    have := P.passes_pos
    omega
  calc P.accepted.ncard
      ≤ (K - 1) ^ 2 * (∑ t ∈ Finset.range P.length, Nat.card U ^ (P.newly t).ncard) *
          Nat.card M ^ (P.passes - 1) * Nat.card M ^ P.passes :=
        P.ncard_accepted_le_of_hasFiberBound hL hdet.hasFiberBound hS
    _ = (K - 1) ^ 2 * (∑ t ∈ Finset.range P.length, Nat.card U ^ (P.newly t).ncard) *
          Nat.card M ^ (2 * P.passes - 1) := by
        rw [mul_assoc _ (Nat.card M ^ (P.passes - 1)), hpow]
    _ ≤ (K - 1) ^ 2 * (P.length * Nat.card U) * Nat.card M ^ (2 * P.passes - 1) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (sum_pow_newly_le U hunit))
    _ = (K - 1) ^ 2 * P.length * Nat.card U * Nat.card M ^ (2 * P.passes - 1) := by ring

/-- **Same-order `k`-pass logarithmic state-width lower bound (`w ≥ n / (2 k - 1) - o(n)`).** Over
a finite alphabet `U` with `q = |U| ≥ 2`, a deterministic same-order `k`-pass program reading at
most one coordinate per step on a nonempty `K`-rectangle-free set satisfies
`log_q |accepted| - 2 log_q K - log_q length - 1 ≤ (2 · passes - 1) · log_q |M|`. -/
theorem le_two_mul_passes_sub_one_mul_logb_card [Finite ι] [Finite U] [Nontrivial U] [Finite M]
    (hdet : P.Deterministic) (hL : 0 < P.length) (hunit : ∀ t < P.length, (P.newly t).ncard ≤ 1)
    {K : ℕ} (hS : RectangleFree P.accepted K) (hne : P.accepted.Nonempty) :
    Real.logb (Nat.card U) P.accepted.ncard - 2 * Real.logb (Nat.card U) K -
        Real.logb (Nat.card U) P.length - 1 ≤
      ((2 * P.passes - 1 : ℕ) : ℝ) * Real.logb (Nat.card U) (Nat.card M) :=
  le_mul_logb_of_ncard_le hL (@Nat.card_pos M ⟨P.start⟩ _) hS hne
    (P.ncard_accepted_le_deterministic hdet hL hunit hS)

end SameOrderPassNBP

/-! ### Embedding `ReadOnceNBP` into `AlternatingPassNBP` and partial-overlap slice bounds -/

namespace ReadOnceNBP

variable {ι U M : Type*} (P : ReadOnceNBP ι U M)

/-- `P` is deterministic when every `(t, m, a)` has at most one successor state `m'`. -/
@[expose] def Deterministic : Prop :=
  ∀ t < P.length, ∀ m a m₁ m₂, P.Edge t m a m₁ → P.Edge t m a m₂ → m₁ = m₂

/-- Embed a `ReadOnceNBP` as a `1`-pass `AlternatingPassNBP` with the same filtration and accepted
set. -/
@[expose] def toAlternatingPassNBP : AlternatingPassNBP ι U M where
  passes := 1
  passes_pos := Nat.one_pos
  length := P.length
  revealed := P.revealed
  revealed_zero := P.revealed_zero
  revealed_length := P.revealed_length
  revealed_mono := P.revealed_mono
  start := P.start
  accept := P.accept
  Edge p s m a m' :=
    if hp : p = 0 then
      P.Edge s m (fun i => a ⟨i.val, by subst hp; exact i.property⟩) m'
    else False

@[simp]
theorem toAlternatingPassNBP_passes : P.toAlternatingPassNBP.passes = 1 :=
  rfl

@[simp]
theorem toAlternatingPassNBP_length : P.toAlternatingPassNBP.length = P.length :=
  rfl

@[simp]
theorem toAlternatingPassNBP_newly (t : ℕ) : P.toAlternatingPassNBP.newly t = P.newly t :=
  rfl

/-- `P.toAlternatingPassNBP` accepts the exact same inputs as `P`. -/
@[simp]
theorem toAlternatingPassNBP_accepted : P.toAlternatingPassNBP.accepted = P.accepted := by
  ext x
  constructor
  · rintro ⟨γ, hstart, hacc, _, hedge⟩
    refine ⟨γ 0, hstart, hacc, fun t ht => ?_⟩
    have h := hedge 0 Nat.one_pos t ht
    dsimp only [toAlternatingPassNBP, ↓reduceDIte] at h
    exact h
  · rintro ⟨γ₀, hstart, hacc, hedge⟩
    refine ⟨fun _ t => γ₀ t, hstart, hacc, fun p hp => ?_, fun p hp t ht => ?_⟩
    · rw [toAlternatingPassNBP_passes] at hp
      omega
    · rw [toAlternatingPassNBP_passes] at hp
      have hp0 : p = 0 := by omega
      subst p
      dsimp only [toAlternatingPassNBP, ↓reduceDIte]
      exact hedge t ht

/-- Determinism of `P` transfers to `P.toAlternatingPassNBP`. -/
theorem Deterministic.toAlternatingPassNBP {P : ReadOnceNBP ι U M} (hdet : P.Deterministic) :
    P.toAlternatingPassNBP.Deterministic := by
  intro p hp t ht m a m₁ m₂ h₁ h₂
  rw [toAlternatingPassNBP_passes] at hp
  have hp0 : p = 0 := by omega
  subst p
  exact hdet t ht m a m₁ m₂ h₁ h₂

end ReadOnceNBP

/-- **Slice-induced `k`-pass lower bound (`w ≥ ((1 - α) / k) n - o(n)`).** Suppose `S ⊆ U^ι` is
nonempty and `K`-rectangle-free, `O ⊆ ι` is the subset of multi-read coordinates, and for every
fixing `a : O → U` there is a deterministic `k`-pass alternating program on `↥Oᶜ` with state space
`M` of length `T' > 0` (at most one coordinate per step) accepting `restrictSlice S O a`. Then
`log_q |S| - |O| - 2 log_q K - log_q T' - 1 ≤ k · log_q |M|`. -/
theorem le_passes_mul_logb_card_of_slice {ι U M : Type*} [Finite ι] [Finite U] [Nontrivial U]
    [Finite M] {S : Set (ι → U)} {K k T' : ℕ} (hS : RectangleFree S K) (hne : S.Nonempty)
    (hT' : 0 < T') (O : Set ι)
    (hslice : ∀ a : O → U, ∃ P : AlternatingPassNBP ↥Oᶜ U M,
      P.passes = k ∧ P.length = T' ∧ P.Deterministic ∧
        (∀ t < P.length, (P.newly t).ncard ≤ 1) ∧ P.accepted = restrictSlice S O a) :
    Real.logb (Nat.card U) S.ncard - O.ncard - 2 * Real.logb (Nat.card U) K -
        Real.logb (Nat.card U) T' - 1 ≤
      (k : ℝ) * Real.logb (Nat.card U) (Nat.card M) := by
  obtain ⟨a, ha⟩ := exists_le_mul_ncard_restrictSlice S O
  obtain ⟨P, hpk, hlen, hdet, hunit, hacc⟩ := hslice a
  have hq1 : (1 : ℝ) < Nat.card U := by exact_mod_cast (Finite.one_lt_card (α := U))
  have hS_pos : 0 < S.ncard := (ncard_pos (toFinite _)).mpr hne
  have hqO_pos : 0 < Nat.card U ^ O.ncard := pow_pos Nat.card_pos _
  have hslice_pos : 0 < (restrictSlice S O a).ncard := by
    by_contra h0
    simp only [not_lt, Nat.le_zero] at h0
    rw [h0, mul_zero] at ha
    omega
  have hslice_ne : P.accepted.Nonempty := by
    rw [hacc]
    exact (ncard_pos (toFinite _)).mp hslice_pos
  have hP := P.le_passes_mul_logb_card hdet (hlen ▸ hT') hunit
    (hacc ▸ hS.restrictSlice O a) hslice_ne
  rw [hpk, hlen, hacc] at hP
  have haR : (S.ncard : ℝ) ≤ (Nat.card U : ℝ) ^ O.ncard * (restrictSlice S O a).ncard := by
    exact_mod_cast ha
  have hlogS := Real.logb_le_logb_of_le hq1 (by exact_mod_cast hS_pos) haR
  rw [Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
    Real.logb_self_eq_one hq1, mul_one] at hlogS
  linarith

/-- **Slice-induced read-once lower bound (`w ≥ (1 - α) n - o(n)`).** Suppose `S ⊆ U^ι` is
nonempty and `K`-rectangle-free, `O ⊆ ι` is the subset of multi-read coordinates, and for every
fixing `a : O → U` there is a deterministic `ReadOnceNBP` on `↥Oᶜ` with state space `M` of length
`T' > 0` (at most one coordinate per step) accepting `restrictSlice S O a`. Then
`log_q |S| - |O| - 2 log_q K - log_q T' - 1 ≤ log_q |M|`. -/
theorem le_logb_card_of_slice_readOnce {ι U M : Type*} [Finite ι] [Finite U] [Nontrivial U]
    [Finite M] {S : Set (ι → U)} {K T' : ℕ} (hS : RectangleFree S K) (hne : S.Nonempty)
    (hT' : 0 < T') (O : Set ι)
    (hslice : ∀ a : O → U, ∃ P : ReadOnceNBP ↥Oᶜ U M,
      P.length = T' ∧ P.Deterministic ∧
        (∀ t < P.length, (P.newly t).ncard ≤ 1) ∧ P.accepted = restrictSlice S O a) :
    Real.logb (Nat.card U) S.ncard - O.ncard - 2 * Real.logb (Nat.card U) K -
        Real.logb (Nat.card U) T' - 1 ≤
      Real.logb (Nat.card U) (Nat.card M) := by
  simpa only [Nat.cast_one, one_mul] using
    le_passes_mul_logb_card_of_slice (k := 1) hS hne hT' O fun a => by
      obtain ⟨P, hlen, hdet, hunit, hacc⟩ := hslice a
      exact ⟨P.toAlternatingPassNBP, rfl, hlen, hdet.toAlternatingPassNBP, hunit,
        P.toAlternatingPassNBP_accepted.trans hacc⟩

end Cslib.Circuits.Frontier
