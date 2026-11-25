/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModel

/-!
# Slice and Buffer Map-Correspondence Combinators for `SuccinctWhpModel`

This module provides index injectivity (`sliceIdx_inj`) and the forward/congruence combinators for
`SliceMapRel` (`congr`, `step_true`, `step_false`) and `BufMapRel` (`of_some_iff`, `congr`,
`insert_fresh`) used across the pure WHP succinct dynamic dictionary step proofs.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.sliceIdx_inj`: slice-index `3 * b + r` injectivity
  for roles `r < 3`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.SliceMapRel.congr`, `SliceMapRel.step_true`,
  `SliceMapRel.step_false`: congruence and single-coordinate scan step lemmas for `SliceMapRel`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.BufMapRel.of_some_iff`, `BufMapRel.congr`,
  `BufMapRel.insert_fresh`: characterization, congruence, and fresh-insertion lemmas for
  `BufMapRel`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

theorem sliceIdx_inj {b₁ r₁ b₂ r₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3)
    (heq : 3 * b₁ + r₁ = 3 * b₂ + r₂) : b₁ = b₂ ∧ r₁ = r₂ :=
  ⟨by omega, by omega⟩

theorem SliceMapRel.congr {f f' : ℕ → ℕ} {P P' : ℕ → Prop} {X : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P X m)
    (hf : ∀ loc < X, f' loc = f loc)
    (hP : ∀ loc < X, P' loc ↔ P loc) :
    SliceMapRel f' P' X m := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · rw [hrel.1 fp]
    exact ⟨fun h loc hlt hp' => hf loc hlt ▸ h loc hlt ((hP loc hlt).mp hp'),
      fun h loc hlt hp => hf loc hlt ▸ h loc hlt ((hP loc hlt).mpr hp)⟩
  · rw [hrel.2 fp loc]
    exact ⟨fun ⟨hlt, hp, heq⟩ => ⟨hlt, (hP loc hlt).mpr hp, (hf loc hlt).trans heq⟩,
      fun ⟨hlt, hp', heq⟩ => ⟨hlt, (hP loc hlt).mp hp', (hf loc hlt).symm.trans heq⟩⟩

theorem SliceMapRel.step_true {f : ℕ → ℕ} {P : ℕ → Prop} {cur : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P cur m) (hp : P cur)
    (hfresh : ∀ loc < cur, P loc → f loc ≠ f cur) :
    SliceMapRel f P (cur + 1) (Function.update m (f cur) (some cur)) := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · by_cases hfp : fp = f cur
    · subst hfp
      simp only [Function.update_self, reduceCtorEq, false_iff, not_forall, not_not]
      exact ⟨cur, Nat.lt_succ_self cur, hp, rfl⟩
    · rw [Function.update_of_ne hfp, hrel.1 fp]
      refine ⟨fun hall loc hlt hpl => ?_, fun hall loc hlt hpl =>
        hall loc (Nat.lt_succ_of_lt hlt) hpl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
      · exact hall loc hlt' hpl
      · exact Ne.symm hfp
  · by_cases hfp : fp = f cur
    · subst hfp
      simp only [Function.update_self, Option.some.injEq]
      refine ⟨?_, ?_⟩
      · rintro rfl; exact ⟨Nat.lt_succ_self cur, hp, rfl⟩
      · rintro ⟨hlt, hpl, heq⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
        · exact absurd heq (hfresh loc hlt' hpl)
        · rfl
    · rw [Function.update_of_ne hfp, hrel.2 fp loc]
      refine ⟨fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩, ?_⟩
      rintro ⟨hlt, hpl, heq⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
      · exact ⟨hlt', hpl, heq⟩
      · exact absurd heq.symm hfp

theorem SliceMapRel.step_false {f : ℕ → ℕ} {P : ℕ → Prop} {cur : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P cur m) (hnp : ¬P cur) :
    SliceMapRel f P (cur + 1) m := by
  refine ⟨fun fp => ?_, fun fp loc => ?_⟩
  · rw [hrel.1 fp]
    refine ⟨fun hall loc hlt hpl => ?_, fun hall loc hlt hpl =>
      hall loc (Nat.lt_succ_of_lt hlt) hpl⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
    · exact hall loc hlt' hpl
    · exact absurd hpl hnp
  · rw [hrel.2 fp loc]
    refine ⟨fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩, ?_⟩
    rintro ⟨hlt, hpl, heq⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with hlt' | rfl
    · exact ⟨hlt', hpl, heq⟩
    · exact absurd hpl hnp

/-- Helper producing a full `BufMapRel` from its `some`-characterization. -/
theorem BufMapRel.of_some_iff {M tag : ℕ} {bktCnt : ℕ → ℕ} {locSt rKeyOf : ℕ → ℕ → ℕ}
    {m : ℕ → Option (ℕ × ℕ)}
    (hsome : ∀ rk b loc, m rk = some (b, loc) ↔
      b < M ∧ loc < bktCnt b ∧ locSt b loc = tag ∧ rKeyOf b loc = rk) :
    BufMapRel M tag bktCnt locSt rKeyOf m := by
  refine ⟨fun rk => ?_, hsome⟩
  rw [Option.eq_none_iff_forall_not_mem]
  refine ⟨fun hall b hb loc hloc hst heq =>
    hall (b, loc) ((hsome rk b loc).mpr ⟨hb, hloc, hst, heq⟩),
    fun hall p hmem => ?_⟩
  rcases p with ⟨b, loc⟩
  obtain ⟨hb, hloc, hst, heq⟩ := (hsome rk b loc).mp hmem
  exact hall b hb loc hloc hst heq

theorem BufMapRel.congr {M tag : ℕ} {bktCnt bktCnt' : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hcnt : ∀ b < M, bktCnt' b = bktCnt b)
    (hst : ∀ b < M, ∀ loc < bktCnt b, locSt' b loc = tag ↔ locSt b loc = tag)
    (hrk : ∀ b < M, ∀ loc < bktCnt b, rKeyOf' b loc = rKeyOf b loc) :
    BufMapRel M tag bktCnt' locSt' rKeyOf' m := by
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  rw [hrel.2 rk b loc]
  refine ⟨fun ⟨hb, hloc, hst0, hrk0⟩ =>
    ⟨hb, hcnt b hb ▸ hloc, (hst b hb loc hloc).mpr hst0, (hrk b hb loc hloc).trans hrk0⟩,
    fun ⟨hb, hloc', hst', hrk'⟩ => ?_⟩
  have hloc : loc < bktCnt b := hcnt b hb ▸ hloc'
  exact ⟨hb, hloc, (hst b hb loc hloc).mp hst', (hrk b hb loc hloc).symm.trans hrk'⟩

/-- Inserting a fresh item at `(b₀, bktCnt b₀)` into `BufMapRel`. -/
theorem BufMapRel.insert_fresh {M tag b₀ : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m)
    (hb₀ : b₀ < M)
    (hst_new : locSt' b₀ (bktCnt b₀) = tag)
    (hst_pres : ∀ b < M, ∀ loc < bktCnt b, locSt' b loc = locSt b loc)
    (hrk_pres : ∀ b < M, ∀ loc < bktCnt b, rKeyOf' b loc = rKeyOf b loc)
    (hno_coll : ∀ b < M, ∀ loc < bktCnt b, locSt b loc = tag →
      rKeyOf b loc ≠ rKeyOf' b₀ (bktCnt b₀)) :
    BufMapRel M tag (Function.update bktCnt b₀ (bktCnt b₀ + 1)) locSt' rKeyOf'
      (Function.update m (rKeyOf' b₀ (bktCnt b₀)) (some (b₀, bktCnt b₀))) := by
  set X₀ := bktCnt b₀
  set rk₀ := rKeyOf' b₀ X₀
  have hloc_iff : ∀ b loc, loc < Function.update bktCnt b₀ (X₀ + 1) b ↔
      loc < bktCnt b ∨ b = b₀ ∧ loc = X₀ := fun b loc => by
    by_cases hb : b = b₀
    · subst hb; simp only [Function.update_self, Nat.lt_succ_iff_lt_or_eq, true_and]; rfl
    · simp [hb]
  refine BufMapRel.of_some_iff fun rk b loc => ?_
  simp only [hloc_iff]
  by_cases hrk_eq : rk = rk₀
  · subst hrk_eq
    simp only [Function.update_self, Option.some.injEq, Prod.mk.injEq]
    refine ⟨by rintro ⟨rfl, rfl⟩; exact ⟨hb₀, .inr ⟨rfl, rfl⟩, hst_new, rfl⟩, ?_⟩
    rintro ⟨hb, hlt | ⟨rfl, rfl⟩, hst', hrk'⟩
    · rw [hst_pres b hb loc hlt] at hst'
      rw [hrk_pres b hb loc hlt] at hrk'
      exact absurd hrk' (hno_coll b hb loc hlt hst')
    · exact ⟨rfl, rfl⟩
  · rw [Function.update_of_ne hrk_eq, hrel.2 rk b loc]
    refine ⟨fun ⟨hb, hlt, hst0, hrk0⟩ =>
        ⟨hb, .inl hlt, (hst_pres b hb loc hlt).trans hst0, (hrk_pres b hb loc hlt).trans hrk0⟩,
      ?_⟩
    rintro ⟨hb, hlt | ⟨rfl, rfl⟩, hst', hrk'⟩
    · exact ⟨hb, hlt, (hst_pres b hb loc hlt).symm.trans hst',
        (hrk_pres b hb loc hlt).symm.trans hrk'⟩
    · exact absurd hrk'.symm hrk_eq

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
