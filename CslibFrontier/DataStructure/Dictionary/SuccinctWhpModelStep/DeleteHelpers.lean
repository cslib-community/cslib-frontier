/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.Invariants
import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModelStep.MapRel

/-!
# Shared Deletion, Relocation, and Pre-Tick Stage Helpers for `SuccinctWhpModelStep`

This internal helper module (imported privately by `DeleteLast` and `DeleteReloc`, so none of its
declarations enter the public export closure of `SuccinctWhpModelStep`) factors the shared
combinators for `fastDelete`:
* `SliceMapRel` and `BufMapRel` last-slot deletion and swap-with-last relocation;
* backyard pool release (`pool_release_last`) and dictionary/quotient preservation
  (`dict_map_after_delete`);
* epoch-buffer deletion/relocation (`buf_valid_after_delete`), `bufOld_valid` preservation
  (`bufOld_valid_after_delete`), and Stages `0, 1, 3` of `ValidEpochStagePreTick`
  (`preTick_after_delete_of_stage2`).
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp.ModelStepAux

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Finset
open scoped BigOperators

theorem rebRole_props {r₁ r₂ : ℕ} (hr₁ : r₁ < 3) (hr₂ : r₂ < 3) (hne : r₁ ≠ r₂) :
    3 - r₁ - r₂ < 3 ∧ 3 - r₁ - r₂ ≠ r₁ ∧ 3 - r₁ - r₂ ≠ r₂ :=
  ⟨by omega, by omega, by omega⟩

theorem lt_of_lt_update_le {cnt : ℕ → ℕ} {b k b' loc : ℕ} (hk : k ≤ cnt b)
    (h : loc < Function.update cnt b k b') : loc < cnt b' := by
  by_cases hbb : b' = b
  · subst hbb; rw [Function.update_self] at h; omega
  · rwa [Function.update_of_ne hbb] at h

private theorem ite_update_apply_of_ne {α β : Type*} [DecidableEq α] {P : Prop} [Decidable P]
    {m : α → β} {k₀ k : α} {x : β} (h : P → k ≠ k₀) :
    (if P then Function.update m k₀ x else m) k = m k := by
  split_ifs with hp
  · exact Function.update_of_ne (h hp) _ _
  · rfl

private theorem option_ite_update_none_eq_some {α β : Type*} [DecidableEq α]
    {P : Prop} [Decidable P] {m : α → Option β} {k₀ k : α} {v : β}
    (h : (if P then Function.update m k₀ none else m) k = some v) :
    m k = some v ∧ ¬(P ∧ k = k₀) := by
  by_cases hp : P ∧ k = k₀
  · obtain ⟨hp, rfl⟩ := hp
    rw [ite_eq_left hp, Function.update_self] at h; cases h
  · exact ⟨(ite_update_apply_of_ne fun hp' hk => hp ⟨hp', hk⟩).symm.trans h, hp⟩

private theorem option_ite_update_some_eq_some {α β : Type*} [DecidableEq α]
    {P : Prop} [Decidable P] {m : α → Option β} {k₀ k : α} {v₀ v : β}
    (h : (if P then Function.update m k₀ (some v₀) else m) k = some v) :
    (P ∧ k = k₀ ∧ v = v₀) ∨ (m k = some v ∧ ¬(P ∧ k = k₀)) := by
  by_cases hp : P ∧ k = k₀
  · obtain ⟨hp, rfl⟩ := hp
    rw [ite_eq_left hp, Function.update_self, Option.some.injEq] at h
    exact .inl ⟨hp, rfl, h.symm⟩
  · exact .inr ⟨(ite_update_apply_of_ne fun hp' hk => hp ⟨hp', hk⟩).symm.trans h, hp⟩

private theorem lt_update_of_succ_iff {cnt : ℕ → ℕ} {b₀ n b loc : ℕ} (hcnt : cnt b₀ = n + 1) :
    loc < Function.update cnt b₀ n b ↔ loc < cnt b ∧ ¬(b = b₀ ∧ loc = n) := by
  rcases eq_or_ne b b₀ with rfl | hb
  · rw [Function.update_self]; omega
  · rw [Function.update_of_ne hb]; exact ⟨fun h => ⟨h, fun h' => hb h'.1⟩, And.left⟩

private theorem sliceMapRel_of_some_iff {f : ℕ → ℕ} {P : ℕ → Prop} {X : ℕ} {m : ℕ → Option ℕ}
    (hsome : ∀ fp loc, m fp = some loc ↔ loc < X ∧ P loc ∧ f loc = fp) :
    SliceMapRel f P X m := by
  refine ⟨fun fp => ?_, hsome⟩
  rw [Option.eq_none_iff_forall_not_mem]
  refine ⟨fun hall loc hlt hp heq => hall loc ((hsome fp loc).mpr ⟨hlt, hp, heq⟩),
    fun hall loc hmem => ?_⟩
  obtain ⟨hlt, hp, heq⟩ := (hsome fp loc).mp hmem
  exact hall loc hlt hp heq

theorem sliceMapRel_delete_last {f : ℕ → ℕ} {P : ℕ → Prop} {X : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P (X + 1) m) (_hp : P X)
    (hinj : ∀ loc < X, P loc → f loc ≠ f X) :
    SliceMapRel f P X (Function.update m (f X) none) := by
  refine sliceMapRel_of_some_iff fun fp loc => ?_
  by_cases hfp : fp = f X
  · subst hfp
    simp only [Function.update_self, reduceCtorEq, false_iff]
    rintro ⟨hlt, hpl, heq⟩
    exact hinj loc hlt hpl heq
  · rw [Function.update_of_ne hfp, hrel.2 fp loc]
    exact ⟨fun ⟨hlt, hpl, heq⟩ =>
      ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) (fun h => hfp (h ▸ heq.symm)), hpl, heq⟩,
      fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩⟩

theorem sliceMapRel_skip_last {f : ℕ → ℕ} {P : ℕ → Prop} {X : ℕ} {m : ℕ → Option ℕ}
    (hrel : SliceMapRel f P (X + 1) m) (hnp : ¬P X) :
    SliceMapRel f P X m :=
  sliceMapRel_of_some_iff fun fp loc => by
    rw [hrel.2 fp loc]
    exact ⟨fun ⟨hlt, hpl, heq⟩ =>
      ⟨Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) (fun h => hnp (h ▸ hpl)), hpl, heq⟩,
      fun ⟨hlt, hpl, heq⟩ => ⟨Nat.lt_succ_of_lt hlt, hpl, heq⟩⟩

/-- Relocating `loc_last` into `loc_del < loc_last` across a full slice `0 .. loc_last`
(`loc_last + 1 → loc_last`). -/
theorem sliceMapRel_relocate_full {f f' : ℕ → ℕ} {P P' : ℕ → Prop} [DecidablePred P]
    {loc_del loc_last : ℕ} {m0 : ℕ → Option ℕ}
    (hrel : SliceMapRel f P (loc_last + 1) m0)
    (hlt_del : loc_del < loc_last)
    (hinj : ∀ l₁ < loc_last + 1, ∀ l₂ < loc_last + 1, P l₁ → P l₂ → f l₁ = f l₂ → l₁ = l₂)
    (hf_pres : ∀ loc < loc_last, loc ≠ loc_del → f' loc = f loc)
    (hf_del : f' loc_del = f loc_last)
    (hP_pres : ∀ loc < loc_last, loc ≠ loc_del → (P' loc ↔ P loc))
    (hP_del : P' loc_del ↔ P loc_last) :
    let m1 := if P loc_del then Function.update m0 (f loc_del) none else m0
    (P loc_last → (m1 (f loc_last)).isSome = true) ∧
    SliceMapRel f' P' loc_last
      (if P loc_last then Function.update m1 (f loc_last) (some loc_del) else m1) := by
  intro m1
  have hm1_last : P loc_last → (m1 (f loc_last)).isSome = true := fun hpl => by
    have h : m1 (f loc_last) = some loc_last := by
      dsimp only [m1]
      rw [ite_update_apply_of_ne fun hpd heq => Nat.ne_of_gt hlt_del
        (hinj loc_last (Nat.lt_succ_self _) loc_del (by omega) hpl hpd heq)]
      exact (hrel.2 (f loc_last) loc_last).mpr ⟨Nat.lt_succ_self _, hpl, rfl⟩
    rw [h]; rfl
  refine ⟨hm1_last, sliceMapRel_of_some_iff fun fp loc => ⟨fun hs => ?_, ?_⟩⟩
  · rcases option_ite_update_some_eq_some hs with ⟨hpl, rfl, rfl⟩ | ⟨hs, hnl⟩
    · exact ⟨hlt_del, hP_del.mpr hpl, hf_del⟩
    · obtain ⟨h0s, hnd⟩ := option_ite_update_none_eq_some hs
      obtain ⟨hlt1, hpl_loc, hfl_eq⟩ := (hrel.2 fp loc).mp h0s
      have hne_last : loc ≠ loc_last := fun h => hnl ⟨h ▸ hpl_loc, h ▸ hfl_eq.symm⟩
      have hne_del : loc ≠ loc_del := fun h => hnd ⟨h ▸ hpl_loc, h ▸ hfl_eq.symm⟩
      have hlt_ll : loc < loc_last := by omega
      exact ⟨hlt_ll, (hP_pres loc hlt_ll hne_del).mpr hpl_loc,
        (hf_pres loc hlt_ll hne_del).trans hfl_eq⟩
  · rintro ⟨hlt_ll, hp', hf'_eq⟩
    by_cases hld : loc = loc_del
    · subst hld
      obtain rfl : fp = f loc_last := hf'_eq.symm.trans hf_del
      rw [ite_eq_left (hP_del.mp hp'), Function.update_self]
    · have hpl_loc : P loc := (hP_pres loc hlt_ll hld).mp hp'
      have hfl_eq : f loc = fp := (hf_pres loc hlt_ll hld).symm.trans hf'_eq
      rw [ite_update_apply_of_ne fun hpl heq => Nat.ne_of_lt hlt_ll
        (hinj loc (by omega) loc_last (Nat.lt_succ_self _) hpl_loc hpl (hfl_eq.trans heq))]
      dsimp only [m1]
      rw [ite_update_apply_of_ne fun hpd heq =>
        hld (hinj loc (by omega) loc_del (by omega) hpl_loc hpd (hfl_eq.trans heq))]
      exact (hrel.2 fp loc).mpr ⟨by omega, hpl_loc, hfl_eq⟩

/-- Relocating `loc_last` into `loc_del < cur ≤ loc_last` across a prefix `0 .. cur - 1`, assuming
no collision between `f loc_last` and any remaining active item `< cur \ {loc_del}`. -/
theorem sliceMapRel_relocate_prefix {f f' : ℕ → ℕ} {P P' : ℕ → Prop} [DecidablePred P]
    {loc_del cur loc_last : ℕ} {m0 : ℕ → Option ℕ}
    (hrel : SliceMapRel f P cur m0)
    (hlt_cur : loc_del < cur)
    (hinj_cur : ∀ l₁ < cur, ∀ l₂ < cur, P l₁ → P l₂ → f l₁ = f l₂ → l₁ = l₂)
    (hno_coll : P loc_last → ∀ l < cur, l ≠ loc_del → P l → f l ≠ f loc_last)
    (hf_pres : ∀ loc < cur, loc ≠ loc_del → f' loc = f loc)
    (hf_del : f' loc_del = f loc_last)
    (hP_pres : ∀ loc < cur, loc ≠ loc_del → (P' loc ↔ P loc))
    (hP_del : P' loc_del ↔ P loc_last) :
    let m1 := if P loc_del then Function.update m0 (f loc_del) none else m0
    SliceMapRel f' P' cur
      (if P loc_last then Function.update m1 (f loc_last) (some loc_del) else m1) := by
  intro m1
  refine sliceMapRel_of_some_iff fun fp loc => ⟨fun hs => ?_, ?_⟩
  · rcases option_ite_update_some_eq_some hs with ⟨hpl, rfl, rfl⟩ | ⟨hs, -⟩
    · exact ⟨hlt_cur, hP_del.mpr hpl, hf_del⟩
    · obtain ⟨h0s, hnd⟩ := option_ite_update_none_eq_some hs
      obtain ⟨hlt_c, hpl_loc, hfl_eq⟩ := (hrel.2 fp loc).mp h0s
      have hne_del : loc ≠ loc_del := fun h => hnd ⟨h ▸ hpl_loc, h ▸ hfl_eq.symm⟩
      exact ⟨hlt_c, (hP_pres loc hlt_c hne_del).mpr hpl_loc,
        (hf_pres loc hlt_c hne_del).trans hfl_eq⟩
  · rintro ⟨hlt_c, hp', hf'_eq⟩
    by_cases hld : loc = loc_del
    · subst hld
      obtain rfl : fp = f loc_last := hf'_eq.symm.trans hf_del
      rw [ite_eq_left (hP_del.mp hp'), Function.update_self]
    · have hpl_loc : P loc := (hP_pres loc hlt_c hld).mp hp'
      have hfl_eq : f loc = fp := (hf_pres loc hlt_c hld).symm.trans hf'_eq
      rw [ite_update_apply_of_ne fun hpl heq =>
        hno_coll hpl loc hlt_c hld hpl_loc (hfl_eq.trans heq)]
      dsimp only [m1]
      rw [ite_update_apply_of_ne fun hpd heq =>
        hld (hinj_cur loc hlt_c loc_del hlt_cur hpl_loc hpd (hfl_eq.trans heq))]
      exact (hrel.2 fp loc).mpr ⟨hlt_c, hpl_loc, hfl_eq⟩

/-- Deleting `loc_last` when `bktCnt b₀ = loc_last + 1` shrinks to `loc_last`. -/
theorem bufMapRel_delete_last {M tag b₀ loc_last : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m0 : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m0)
    (_hb₀ : b₀ < M) (hcnt₀ : bktCnt b₀ = loc_last + 1)
    (hinj : ∀ b < M, ∀ loc < bktCnt b, locSt b loc = tag → locSt b₀ loc_last = tag →
      rKeyOf b loc = rKeyOf b₀ loc_last → b = b₀ ∧ loc = loc_last)
    (hst_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      locSt' b loc = locSt b loc)
    (hrk_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      rKeyOf' b loc = rKeyOf b loc) :
    BufMapRel M tag (Function.update bktCnt b₀ loc_last) locSt' rKeyOf'
      (if locSt b₀ loc_last = tag then Function.update m0 (rKeyOf b₀ loc_last) none else m0) := by
  refine BufMapRel.of_some_iff fun rk b loc => ⟨fun hs => ?_, ?_⟩
  · obtain ⟨h0s, hne⟩ := option_ite_update_none_eq_some hs
    obtain ⟨hb, hloc, hst0, hrk0⟩ := (hrel.2 rk b loc).mp h0s
    have hloc' := (lt_update_of_succ_iff hcnt₀).mpr
      ⟨hloc, fun ⟨h1, h2⟩ => hne ⟨h1 ▸ h2 ▸ hst0, h1 ▸ h2 ▸ hrk0.symm⟩⟩
    exact ⟨hb, hloc', (hst_pres b hb loc hloc').trans hst0,
      (hrk_pres b hb loc hloc').trans hrk0⟩
  · rintro ⟨hb, hloc', hst', hrk'⟩
    obtain ⟨hloc, hne⟩ := (lt_update_of_succ_iff hcnt₀).mp hloc'
    have hst0 : locSt b loc = tag := (hst_pres b hb loc hloc').symm.trans hst'
    have hrk0 : rKeyOf b loc = rk := (hrk_pres b hb loc hloc').symm.trans hrk'
    rw [ite_update_apply_of_ne fun htl heq => hne (hinj b hb loc hloc hst0 htl (hrk0.trans heq))]
    exact (hrel.2 rk b loc).mpr ⟨hb, hloc, hst0, hrk0⟩

/-- Relocating `(b₀, loc_last)` into `(b₀, loc_del)` (`loc_del < loc_last`) in `BufMapRel`. -/
theorem bufMapRel_relocate_last {M tag b₀ loc_del loc_last : ℕ} {bktCnt : ℕ → ℕ}
    {locSt locSt' rKeyOf rKeyOf' : ℕ → ℕ → ℕ} {m0 : ℕ → Option (ℕ × ℕ)}
    (hrel : BufMapRel M tag bktCnt locSt rKeyOf m0)
    (hb₀ : b₀ < M) (hcnt₀ : bktCnt b₀ = loc_last + 1) (hlt_del : loc_del < loc_last)
    (hinj : ∀ b₁ < M, ∀ l₁ < bktCnt b₁, ∀ b₂ < M, ∀ l₂ < bktCnt b₂,
      locSt b₁ l₁ = tag → locSt b₂ l₂ = tag → rKeyOf b₁ l₁ = rKeyOf b₂ l₂ → b₁ = b₂ ∧ l₁ = l₂)
    (hst_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      ¬(b = b₀ ∧ loc = loc_del) → locSt' b loc = locSt b loc)
    (hst_del : locSt' b₀ loc_del = locSt b₀ loc_last)
    (hrk_pres : ∀ b < M, ∀ loc < (Function.update bktCnt b₀ loc_last) b,
      ¬(b = b₀ ∧ loc = loc_del) → rKeyOf' b loc = rKeyOf b loc)
    (hrk_del : rKeyOf' b₀ loc_del = rKeyOf b₀ loc_last) :
    let m1 := if locSt b₀ loc_del = tag then Function.update m0 (rKeyOf b₀ loc_del) none else m0
    (locSt b₀ loc_last = tag → m1 (rKeyOf b₀ loc_last) = some (b₀, loc_last)) ∧
    BufMapRel M tag (Function.update bktCnt b₀ loc_last) locSt' rKeyOf'
      (if locSt b₀ loc_last = tag then
        Function.update m1 (rKeyOf b₀ loc_last) (some (b₀, loc_del))
      else m1) := by
  intro m1
  have hll_lt : loc_last < bktCnt b₀ := by omega
  have hld_lt : loc_del < bktCnt b₀ := by omega
  have hm1_last : locSt b₀ loc_last = tag → m1 (rKeyOf b₀ loc_last) = some (b₀, loc_last) := by
    intro htl
    dsimp only [m1]
    rw [ite_update_apply_of_ne fun htd heq => Nat.ne_of_gt hlt_del
      (hinj b₀ hb₀ loc_last hll_lt b₀ hb₀ loc_del hld_lt htl htd heq).2]
    exact (hrel.2 _ b₀ loc_last).mpr ⟨hb₀, hll_lt, htl, rfl⟩
  refine ⟨hm1_last, BufMapRel.of_some_iff fun rk b loc => ⟨fun hs => ?_, ?_⟩⟩
  · rcases option_ite_update_some_eq_some hs with ⟨htl, rfl, hbl⟩ | ⟨hs, hnl⟩
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hbl
      refine ⟨hb₀, ?_, hst_del.trans htl, hrk_del⟩
      rw [Function.update_self]; exact hlt_del
    · obtain ⟨h0s, hnd⟩ := option_ite_update_none_eq_some hs
      obtain ⟨hb, hloc, hst0, hrk0⟩ := (hrel.2 rk b loc).mp h0s
      have hne_del : ¬(b = b₀ ∧ loc = loc_del) := fun ⟨h1, h2⟩ =>
        hnd ⟨h1 ▸ h2 ▸ hst0, h1 ▸ h2 ▸ hrk0.symm⟩
      have hloc' := (lt_update_of_succ_iff hcnt₀).mpr
        ⟨hloc, fun ⟨h1, h2⟩ => hnl ⟨h1 ▸ h2 ▸ hst0, h1 ▸ h2 ▸ hrk0.symm⟩⟩
      exact ⟨hb, hloc', (hst_pres b hb loc hloc' hne_del).trans hst0,
        (hrk_pres b hb loc hloc' hne_del).trans hrk0⟩
  · rintro ⟨hb, hloc', hst', hrk'⟩
    by_cases hbd : b = b₀ ∧ loc = loc_del
    · rcases hbd with ⟨rfl, rfl⟩
      obtain rfl : rk = rKeyOf b loc_last := hrk'.symm.trans hrk_del
      rw [ite_eq_left (hst_del.symm.trans hst'), Function.update_self]
    · obtain ⟨hloc, hne_last⟩ := (lt_update_of_succ_iff hcnt₀).mp hloc'
      have hst0 : locSt b loc = tag := (hst_pres b hb loc hloc' hbd).symm.trans hst'
      have hrk0 : rKeyOf b loc = rk := (hrk_pres b hb loc hloc' hbd).symm.trans hrk'
      rw [ite_update_apply_of_ne fun htl heq =>
        hne_last (hinj b hb loc hloc b₀ hb₀ loc_last hll_lt hst0 htl (hrk0.trans heq))]
      dsimp only [m1]
      rw [ite_update_apply_of_ne fun htd heq =>
        hbd (hinj b hb loc hloc b₀ hb₀ loc_del hld_lt hst0 htd (hrk0.trans heq))]
      exact (hrel.2 rk b loc).mpr ⟨hb, hloc, hst0, hrk0⟩

theorem buf_del_at_ep {c n_max st rKey ep : ℕ} (buf : ℕ → BufTrie)
    (hep : ep = 0 ∨ ep = 1) :
    (if st = 2 then
        Function.update buf 0 (bufDelete (cTabWhp c) (bCharWhp n_max) (buf 0) rKey)
      else if st = 3 then
        Function.update buf 1 (bufDelete (cTabWhp c) (bCharWhp n_max) (buf 1) rKey)
      else buf) ep =
      if st = 2 + ep then bufDelete (cTabWhp c) (bCharWhp n_max) (buf ep) rKey else buf ep := by
  rcases hep with rfl | rfl <;> split_ifs <;> simp_all

theorem buf_ins_at_ep {c n_max st rKey b loc ep : ℕ} (buf : ℕ → BufTrie)
    (hep : ep = 0 ∨ ep = 1) :
    (if st = 2 then
        Function.update buf 0 (bufInsert (cTabWhp c) (bCharWhp n_max) (buf 0) rKey b loc)
      else if st = 3 then
        Function.update buf 1 (bufInsert (cTabWhp c) (bCharWhp n_max) (buf 1) rKey b loc)
      else buf) ep =
      if st = 2 + ep then bufInsert (cTabWhp c) (bCharWhp n_max) (buf ep) rKey b loc
      else buf ep := by
  rcases hep with rfl | rfl <;> split_ifs <;> simp_all

/-- Releasing `loc_last` (`fs.bktCount b = loc_last + 1`) preserves all backyard-pool invariants. -/
theorem pool_release_last {c U V n_max b loc_last : ℕ} {θ : SeedWhp c U n_max}
    {fs fs' : FastState} {dict : State U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hcnt : fs.bktCount b = loc_last + 1)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hbp' : fs'.backPtr = fs.backPtr)
    (hown' : fs'.poolOwner = fs.poolOwner)
    (htop' : fs'.poolFreeTop =
      if capFrontWhp n_max ≤ loc_last then fs.poolFreeTop + 1 else fs.poolFreeTop)
    (hstk' : fs'.poolFreeStack =
      if capFrontWhp n_max ≤ loc_last then
        Function.update fs.poolFreeStack fs.poolFreeTop
          (fs.backPtr b (loc_last - capFrontWhp n_max))
      else fs.poolFreeStack) :
    fs'.poolFreeTop ≤ poolSizeWhp n_max ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
      fs'.backPtr b' k < poolSizeWhp n_max ∧
      fs'.poolOwner (fs'.backPtr b' k) = b' * capBackWhp n_max + k) ∧
    (∀ j < fs'.poolFreeTop, fs'.poolFreeStack j < poolSizeWhp n_max) ∧
    (∀ b₁ < numBucketsWhp n_max, ∀ k₁ < fs'.bktCount b₁ - capFrontWhp n_max,
     ∀ b₂ < numBucketsWhp n_max, ∀ k₂ < fs'.bktCount b₂ - capFrontWhp n_max,
       fs'.backPtr b₁ k₁ = fs'.backPtr b₂ k₂ → b₁ = b₂ ∧ k₁ = k₂) ∧
    (∀ j₁ < fs'.poolFreeTop, ∀ j₂ < fs'.poolFreeTop,
      fs'.poolFreeStack j₁ = fs'.poolFreeStack j₂ → j₁ = j₂) ∧
    (∀ b' < numBucketsWhp n_max, ∀ k < fs'.bktCount b' - capFrontWhp n_max,
     ∀ j < fs'.poolFreeTop, fs'.backPtr b' k ≠ fs'.poolFreeStack j) ∧
    fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - capFrontWhp n_max) =
      poolSizeWhp n_max := by
  have hsub_le : ∀ b' < numBucketsWhp n_max,
      fs'.bktCount b' - capFrontWhp n_max ≤ fs.bktCount b' - capFrontWhp n_max := by
    intro b' _
    rcases eq_or_ne b' b with rfl | hbb
    · rw [hbkt', Function.update_self]; omega
    · rw [hbkt', Function.update_of_ne hbb]
  have hsum_split_old := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs.bktCount b' - capFrontWhp n_max) (Finset.mem_range.mpr hb)
  have hsum_split_new := Finset.add_sum_erase (range (numBucketsWhp n_max))
    (fun b' => fs'.bktCount b' - capFrontWhp n_max) (Finset.mem_range.mpr hb)
  have herase_eq :
      ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs'.bktCount x - capFrontWhp n_max) =
        ∑ x ∈ (range (numBucketsWhp n_max)).erase b, (fs.bktCount x - capFrontWhp n_max) := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [hbkt', Function.update_of_ne (Finset.ne_of_mem_erase hx)]
  have hcons : fs'.poolFreeTop +
      ∑ b' ∈ range (numBucketsWhp n_max), (fs'.bktCount b' - capFrontWhp n_max) =
      poolSizeWhp n_max := by
    have hpc := hc.pool_conservation
    rw [← hsum_split_old, hcnt] at hpc
    rw [← hsum_split_new, herase_eq, hbkt', Function.update_self, htop']
    split_ifs with hcf <;> omega
  refine ⟨by omega, ?_, ?_, ?_, ?_, ?_, hcons⟩
  · intro b' hb' k hk
    rw [hbp', hown']
    exact hc.backPtr_valid b' hb' k (hk.trans_le (hsub_le b' hb'))
  · intro j hj
    rw [htop'] at hj
    rw [hstk']
    split_ifs at hj ⊢ with hcf
    · rcases eq_or_ne j fs.poolFreeTop with rfl | hjeq
      · rw [Function.update_self]
        exact (hc.backPtr_valid b hb (loc_last - capFrontWhp n_max) (by omega)).1
      · rw [Function.update_of_ne hjeq]
        exact hc.freeStack_lt j (by omega)
    · exact hc.freeStack_lt j hj
  · intro b₁ hb₁ k₁ hk₁ b₂ hb₂ k₂ hk₂ heq
    rw [hbp'] at heq
    exact hc.backPtr_inj b₁ hb₁ k₁ (hk₁.trans_le (hsub_le b₁ hb₁))
      b₂ hb₂ k₂ (hk₂.trans_le (hsub_le b₂ hb₂)) heq
  · intro j₁ hj₁ j₂ hj₂ heq
    rw [htop'] at hj₁ hj₂
    rw [hstk'] at heq
    split_ifs at hj₁ hj₂ heq with hcf
    · by_cases h1 : j₁ = fs.poolFreeTop <;> by_cases h2 : j₂ = fs.poolFreeTop
      · omega
      · subst h1
        rw [Function.update_self, Function.update_of_ne h2] at heq
        exact absurd heq
          (hc.back_free_disj b hb (loc_last - capFrontWhp n_max) (by omega) j₂ (by omega))
      · subst h2
        rw [Function.update_of_ne h1, Function.update_self] at heq
        exact absurd heq.symm
          (hc.back_free_disj b hb (loc_last - capFrontWhp n_max) (by omega) j₁ (by omega))
      · rw [Function.update_of_ne h1, Function.update_of_ne h2] at heq
        exact hc.freeStack_inj j₁ (by omega) j₂ (by omega) heq
    · exact hc.freeStack_inj j₁ hj₁ j₂ hj₂ heq
  · intro b' hb' k hk j hj
    rw [htop'] at hj
    rw [hbp', hstk']
    split_ifs at hj ⊢ with hcf
    · by_cases hjeq : j = fs.poolFreeTop
      · subst hjeq
        rw [Function.update_self]
        intro heq
        obtain ⟨rfl, hkeq⟩ := hc.backPtr_inj b' hb' k (hk.trans_le (hsub_le b' hb'))
          b hb (loc_last - capFrontWhp n_max) (by omega) heq
        rw [hbkt', Function.update_self] at hk
        omega
      · rw [Function.update_of_ne hjeq]
        exact hc.back_free_disj b' hb' k (hk.trans_le (hsub_le b' hb')) j (by omega)
    · exact hc.back_free_disj b' hb' k (hk.trans_le (hsub_le b' hb')) j hj

/-- Abstract dictionary-map and quotient-injectivity preservation under deleting `(b, loc_del)` and
relocating `(b, loc_last)` (when `loc_del < loc_last`). -/
theorem dict_map_after_delete {c U V n_max b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {u : Fin U}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb_eq : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b)
    (hcnt : fs.bktCount b = loc_last + 1)
    (hld_lt : loc_del < loc_last + 1)
    (hq_del : fs.quotArr (fs.physSlot n_max b loc_del) = keyQuotient (bWhp n_max) u.val)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hother : ∀ b' < numBucketsWhp n_max, b' ≠ b → ∀ loc < fs.bktCount b',
      fs'.quotArr (fs'.physSlot n_max b' loc) = fs.quotArr (fs.physSlot n_max b' loc) ∧
      fs'.valArr (fs'.physSlot n_max b' loc) = fs.valArr (fs.physSlot n_max b' loc))
    (hfwd : ∀ loc' < loc_last, ∃ loc < loc_last + 1, loc ≠ loc_del ∧
      fs'.quotArr (fs'.physSlot n_max b loc') = fs.quotArr (fs.physSlot n_max b loc) ∧
      fs'.valArr (fs'.physSlot n_max b loc') = fs.valArr (fs.physSlot n_max b loc) ∧
      (∀ l₂ < loc_last,
        fs'.quotArr (fs'.physSlot n_max b loc') = fs'.quotArr (fs'.physSlot n_max b l₂) →
        loc' = l₂))
    (hbwd : ∀ loc < loc_last + 1, loc ≠ loc_del → ∃ loc' < loc_last,
      fs'.quotArr (fs'.physSlot n_max b loc') = fs.quotArr (fs.physSlot n_max b loc) ∧
      fs'.valArr (fs'.physSlot n_max b loc') = fs.valArr (fs.physSlot n_max b loc)) :
    (∀ b' < numBucketsWhp n_max, ∀ l₁ < fs'.bktCount b', ∀ l₂ < fs'.bktCount b',
      fs'.quotArr (fs'.physSlot n_max b' l₁) = fs'.quotArr (fs'.physSlot n_max b' l₂) →
      l₁ = l₂) ∧
    (∀ u' : Fin U,
      let b' := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val
      let q' := keyQuotient (bWhp n_max) u'.val
      ((Function.update dict u none) u' = none ↔
        ∀ loc < fs'.bktCount b', fs'.quotArr (fs'.physSlot n_max b' loc) ≠ q') ∧
      (∀ v, (Function.update dict u none) u' = some v ↔
        ∃ loc < fs'.bktCount b',
          fs'.quotArr (fs'.physSlot n_max b' loc) = q' ∧
          fs'.valArr (fs'.physSlot n_max b' loc) = v)) := by
  have hb : b < numBucketsWhp n_max := hb_eq ▸ feistelBucket_lt _ _ _
  refine ⟨fun b' hb' l₁ hl₁ l₂ hl₂ heq => ?_, fun u' => ?_⟩
  · rw [hbkt'] at hl₁ hl₂
    by_cases hbb : b' = b
    · subst hbb
      rw [Function.update_self] at hl₁ hl₂
      obtain ⟨_, _, _, _, _, hinj⟩ := hfwd l₁ hl₁
      exact hinj l₂ hl₂ heq
    · rw [Function.update_of_ne hbb] at hl₁ hl₂
      rw [(hother b' hb' hbb l₁ hl₁).1, (hother b' hb' hbb l₂ hl₂).1] at heq
      exact hc.quot_inj b' hb' l₁ hl₁ l₂ hl₂ heq
  · dsimp only
    set b' := feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val
    set q' := keyQuotient (bWhp n_max) u'.val
    have hb' : b' < numBucketsWhp n_max := feistelBucket_lt _ _ _
    by_cases hu_eq : u' = u
    · subst hu_eq
      have hb'_eq : b' = b := hb_eq
      simp only [Function.update_self, hbkt', hb'_eq, true_iff, reduceCtorEq, false_iff,
        not_exists, not_and]
      refine ⟨fun loc' hloc' hq' => ?_, fun v loc' hloc' hq' _ => ?_⟩ <;> (
        obtain ⟨loc, hloc, hne_d, hqe, _⟩ := hfwd loc' hloc'
        have h1 : fs.quotArr (fs.physSlot n_max b loc) = fs.quotArr (fs.physSlot n_max b loc_del) :=
          hqe.symm.trans (hq'.trans hq_del.symm)
        exact hne_d (hc.quot_inj b hb loc (hcnt ▸ hloc) loc_del (hcnt ▸ hld_lt) h1))
    · rw [Function.update_of_ne hu_eq]
      obtain ⟨hnone_iff, hsome_iff⟩ := hc.dict_map u'
      by_cases hbb : b' = b
      · have hq_ne : q' ≠ keyQuotient (bWhp n_max) u.val := by
          intro hqe
          apply hu_eq
          apply Fin.ext
          rw [← feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val,
            ← feistelReconstruct_feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val]
          change feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1) b' q' =
            feistelReconstruct (bWhp n_max) (bktHash c U n_max θ.1)
              (feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val)
              (keyQuotient (bWhp n_max) u.val)
          rw [hbb, hb_eq, hqe]
        have hbb_raw : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u'.val = b := hbb
        rw [hbkt', hbb, Function.update_self]
        refine ⟨?_, fun v => ?_⟩
        · rw [hnone_iff, hbb_raw, hcnt]
          refine ⟨fun hall loc' hloc' hqe' => ?_, fun hall loc hloc hqe => ?_⟩
          · obtain ⟨loc, hloc, _, hq1, _⟩ := hfwd loc' hloc'
            exact hall loc hloc (hq1.symm.trans hqe')
          · have hne_d : loc ≠ loc_del := fun h => hq_ne (hqe.symm.trans (h ▸ hq_del))
            obtain ⟨loc', hloc', hq1, _⟩ := hbwd loc hloc hne_d
            exact hall loc' hloc' (hq1.trans hqe)
        · rw [hsome_iff v, hbb_raw, hcnt]
          refine ⟨fun ⟨loc, hloc, hqe, hve⟩ => ?_, fun ⟨loc', hloc', hqe', hve'⟩ => ?_⟩
          · have hne_d : loc ≠ loc_del := fun h => hq_ne (hqe.symm.trans (h ▸ hq_del))
            obtain ⟨loc', hloc', hq1, hv1⟩ := hbwd loc hloc hne_d
            exact ⟨loc', hloc', hq1.trans hqe, hv1.trans hve⟩
          · obtain ⟨loc, hloc, _, hq1, hv1, _⟩ := hfwd loc' hloc'
            exact ⟨loc, hloc, hq1.symm.trans hqe', hv1.symm.trans hve'⟩
      · rw [hbkt', Function.update_of_ne hbb]
        refine ⟨?_, fun v => ?_⟩
        · rw [hnone_iff]
          exact ⟨fun hall loc hloc => (hother b' hb' hbb loc hloc).1.symm ▸ hall loc hloc,
            fun hall loc hloc => (hother b' hb' hbb loc hloc).1 ▸ hall loc hloc⟩
        · rw [hsome_iff v]
          refine ⟨fun ⟨loc, hloc, hqe, hve⟩ =>
            ⟨loc, hloc, (hother b' hb' hbb loc hloc).1.trans hqe,
              (hother b' hb' hbb loc hloc).2.trans hve⟩,
            fun ⟨loc, hloc, hqe, hve⟩ =>
            ⟨loc, hloc, (hother b' hb' hbb loc hloc).1.symm.trans hqe,
              (hother b' hb' hbb loc hloc).2.symm.trans hve⟩⟩

private theorem bufEnsurePath_allocations (bChar rKey : ℕ) :
    ∀ (rem off : ℕ) (tr : BufTrie) (cur : ℕ),
      (bufEnsurePath bChar rKey rem off tr cur).1.itemAlloc = tr.itemAlloc ∧
      tr.nodeAlloc ≤ (bufEnsurePath bChar rKey rem off tr cur).1.nodeAlloc ∧
      ((bufEnsurePath bChar rKey rem off tr cur).1.nodeAlloc = tr.nodeAlloc →
        (bufEnsurePath bChar rKey rem off tr cur).1 = tr ∧
        bufWalk bChar tr.trieChild rKey rem off cur =
          some (bufEnsurePath bChar rKey rem off tr cur).2)
  | 0, _, tr, cur => ⟨rfl, le_rfl, fun _ => ⟨rfl, rfl⟩⟩
  | rem + 1, off, tr, cur => by
    dsimp only [bufEnsurePath, bufWalk]
    set ch := laneGet bChar rKey off
    by_cases h0 : tr.trieChild cur ch = 0
    · simp only [h0, ↓reduceIte]
      obtain ⟨items, hle, _⟩ := bufEnsurePath_allocations bChar rKey rem (off + 1)
        { tr with
          nodeAlloc := tr.nodeAlloc + 1
          trieChild := Function.update tr.trieChild cur
            (Function.update (tr.trieChild cur) ch tr.nodeAlloc)
          nodeParent := Function.update tr.nodeParent tr.nodeAlloc cur
          nodeChar := Function.update tr.nodeChar tr.nodeAlloc ch
          nodeLeafItem := Function.update tr.nodeLeafItem tr.nodeAlloc 0 } tr.nodeAlloc
      dsimp only at items hle
      exact ⟨items, Nat.le_of_succ_le hle, fun heq => by
        rw [heq] at hle
        exact (Nat.lt_irrefl _ hle).elim⟩
    · simp only [h0, ↓reduceIte]
      exact bufEnsurePath_allocations bChar rKey rem (off + 1) tr (tr.trieChild cur ch)

private theorem bufDelete_checkSlot_some {cTab bChar rKey id b' loc' : ℕ} {tr : BufTrie}
    (h : bufCheckSlot (bufDelete cTab bChar tr rKey) id = some (b', loc')) :
    bufCheckSlot tr id = some (b', loc') := by
  dsimp only [bufDelete] at h
  cases hw : bufWalk bChar tr.trieChild rKey cTab 0 0 with
  | none => rw [hw] at h; exact h
  | some leaf =>
    rw [hw] at h; dsimp only at h
    split_ifs at h with hcond
    · exact h
    · dsimp only [bufCheckSlot] at h ⊢
      by_cases hid : id < tr.itemAlloc
      · simp only [hid, ↓reduceIte] at h ⊢
        by_cases hl : tr.itemLeaf id = leaf
        · rw [hl] at h
          simp only [Function.update_self, ne_eq, not_true_eq_false, and_false, ↓reduceIte,
            reduceCtorEq] at h
        · simp only [Function.update_of_ne hl] at h
          exact h
      · simp only [hid, ↓reduceIte, reduceCtorEq] at h

private theorem insert_same_bucket_checkSlot_some {cTab bChar rKey b loc_old loc_new
    id b' loc' : ℕ} {tr : BufTrie} {mapFn : ℕ → Option (ℕ × ℕ)}
    (hv : ValidBufTrie cTab bChar tr mapFn) (hk : rKey < 2 ^ (cTab * bChar))
    (hm : mapFn rKey = some (b, loc_old))
    (hchk : bufCheckSlot (bufInsert cTab bChar tr rKey b loc_new) id = some (b', loc')) :
    ∃ loc₁, bufCheckSlot tr id = some (b', loc₁) := by
  have hm_ne : mapFn rKey ≠ none := by rw [hm]; simp
  have hins := hv.insert_spec (b := b) (loc := loc_new) hk
  obtain ⟨hna_eq, hia_eq, hnone_pres⟩ := hins.2.2.2.2.2.2 hm_ne
  have hnot_none : bufCheckSlot tr id ≠ none := fun hn => by
    rw [hnone_pres id hn] at hchk; cases hchk
  obtain ⟨⟨b₁, loc₁⟩, hchk1⟩ := Option.ne_none_iff_exists'.mp hnot_none
  refine ⟨loc₁, ?_⟩
  have bucket_of_hit {t : BufTrie} {bucket loc : ℕ}
      (h : bufCheckSlot t id = some (bucket, loc)) : t.itemBucket id = bucket := by
    dsimp only [bufCheckSlot] at h
    split at h
    · split at h
      · exact congrArg Prod.fst (Option.some.inj h)
      · cases h
    · cases h
  obtain ⟨hp_ia, _, heq_fn⟩ := bufEnsurePath_allocations bChar rKey cTab 0 tr 0
  set p := bufEnsurePath bChar rKey cTab 0 tr 0 with hp
  have hid1_nz : p.1.nodeLeafItem p.2 ≠ 0 := by
    intro hz
    have hia_succ : (bufInsert cTab bChar tr rKey b loc_new).itemAlloc = p.1.itemAlloc + 1 := by
      dsimp only [bufInsert]; simp [p, hz]
    rw [hia_eq, hp_ia] at hia_succ
    exact Nat.ne_of_lt (Nat.lt_succ_self _) hia_succ
  have hp_na : p.1.nodeAlloc = tr.nodeAlloc := by
    have : (bufInsert cTab bChar tr rKey b loc_new).nodeAlloc = p.1.nodeAlloc := by
      dsimp only [bufInsert]; simp [p, hid1_nz]
    omega
  obtain ⟨htr_eq, hwalk⟩ := heq_fn hp_na
  have hlk := (hv.lookup_eq hk).trans hm
  dsimp only [bufLookup] at hlk
  rw [hwalk, ← htr_eq] at hlk
  dsimp only at hlk
  split_ifs at hlk with hcond
  have hb_old : tr.itemBucket (p.1.nodeLeafItem p.2 - 1) = b := by
    rw [← htr_eq]; injection hlk with hp; exact (Prod.mk.inj hp).1
  have buckets : (bufInsert cTab bChar tr rKey b loc_new).itemBucket = tr.itemBucket := by
    dsimp only [bufInsert]
    simp only [← hp, hid1_nz, ↓reduceIte]
    rw [← hb_old, htr_eq, Function.update_eq_self]
  have heq := (bucket_of_hit hchk1).symm.trans
    ((congrFun buckets id).symm.trans (bucket_of_hit hchk))
  simpa only [heq] using hchk1

private theorem rKeyAt_lt {c U n_max : ℕ} (θ : SeedWhp c U n_max) (fs : FastState)
    (b loc : ℕ) : fs.rKeyAt c U n_max θ b loc < 2 ^ (cTabWhp c * bCharWhp n_max) := by
  dsimp only [FastState.rKeyAt]
  split_ifs with h
  · exact fpReducedKey_lt c U n_max θ.2 ⟨_, h⟩
  · exact Nat.two_pow_pos _

/-- Parametric epoch-buffer preservation across `fastDelete` (applicable to both `curEp` and
`oldEp` when `rebStage ≤ 3`). -/
theorem buf_valid_after_delete {c U V n_max b loc_del loc_last ep : ℕ}
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {rKey_u : ℕ}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hcnt : fs.bktCount b = loc_last + 1)
    (hld_lt : loc_del < loc_last + 1)
    (hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u)
    (hbuf0 :
      (fs.buf ep).itemAlloc ≤ 2 * sMaxWhp c n_max ∧
      (fs.buf ep).nodeAlloc ≤ 1 + cTabWhp c * (fs.buf ep).itemAlloc ∧
      ∃ m0,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs.buf ep) m0 ∧
        BufMapRel (numBucketsWhp n_max) (2 + ep) fs.bktCount fs.locState
          (fs.rKeyAt c U n_max θ) m0)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hpres_eq : loc_del = loc_last →
      ∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b',
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc)
    (hpres_lt : loc_del < loc_last →
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b', ¬(b' = b ∧ loc = loc_del) →
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc) ∧
      fs'.locState b loc_del = fs.locState b loc_last ∧
      fs'.rKeyAt c U n_max θ b loc_del = fs.rKeyAt c U n_max θ b loc_last) :
    let tr1 :=
      if fs.locState b loc_del = 2 + ep then
        bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf ep) rKey_u
      else fs.buf ep
    let tr' :=
      if loc_del < loc_last then
        if fs.locState b loc_last = 2 + ep then
          bufInsert (cTabWhp c) (bCharWhp n_max) tr1 (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else tr1
      else tr1
    tr'.itemAlloc = (fs.buf ep).itemAlloc ∧
    tr'.nodeAlloc = (fs.buf ep).nodeAlloc ∧
    (∃ m',
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr' m' ∧
      BufMapRel (numBucketsWhp n_max) (2 + ep) fs'.bktCount fs'.locState
        (fs'.rKeyAt c U n_max θ) m') ∧
    (∀ id, bufCheckSlot (fs.buf ep) id = none → bufCheckSlot tr' id = none) ∧
    (∀ id b' loc', bufCheckSlot tr' id = some (b', loc') →
      ∃ loc₀, bufCheckSlot (fs.buf ep) id = some (b', loc₀)) := by
  intro tr1 tr'
  obtain ⟨hia_le, hna_le, m0, hv0, hrel0⟩ := hbuf0
  have hrk_u_lt : rKey_u < 2 ^ (cTabWhp c * bCharWhp n_max) :=
    hrk_del ▸ rKeyAt_lt θ fs b loc_del
  have hrk_l_lt : fs.rKeyAt c U n_max θ b loc_last < 2 ^ (cTabWhp c * bCharWhp n_max) :=
    rKeyAt_lt θ fs b loc_last
  let m1 :=
    if fs.locState b loc_del = 2 + ep then
      Function.update m0 (fs.rKeyAt c U n_max θ b loc_del) none
    else m0
  have htr1 : ValidBufTrie (cTabWhp c) (bCharWhp n_max) tr1 m1 ∧
      tr1.nodeAlloc = (fs.buf ep).nodeAlloc ∧
      tr1.itemAlloc = (fs.buf ep).itemAlloc ∧
      (∀ id, bufCheckSlot (fs.buf ep) id = none → bufCheckSlot tr1 id = none) ∧
      (∀ id b' loc', bufCheckSlot tr1 id = some (b', loc') →
        bufCheckSlot (fs.buf ep) id = some (b', loc')) := by
    dsimp only [tr1, m1]
    split_ifs with htd
    · rw [hrk_del]
      obtain ⟨hv1, hna1, hia1, _, hnone1⟩ := hv0.delete_spec hrk_u_lt
      exact ⟨hv1, hna1, hia1, hnone1, fun _ _ _ h => bufDelete_checkSlot_some h⟩
    · exact ⟨hv0, rfl, rfl, fun _ h => h, fun _ _ _ h => h⟩
  obtain ⟨hv1, hna1, hia1, hnone1, hsome1⟩ := htr1
  have hinj_ep : ∀ b₁ < numBucketsWhp n_max, ∀ l₁ < fs.bktCount b₁,
      ∀ b₂ < numBucketsWhp n_max, ∀ l₂ < fs.bktCount b₂,
        fs.locState b₁ l₁ = 2 + ep → fs.locState b₂ l₂ = 2 + ep →
        fs.rKeyAt c U n_max θ b₁ l₁ = fs.rKeyAt c U n_max θ b₂ l₂ → b₁ = b₂ ∧ l₁ = l₂ :=
    fun b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ h1 h2 =>
      hc.rKey_buf_inj b₁ hb₁ l₁ hl₁ b₂ hb₂ l₂ hl₂ (by omega) (by omega)
  by_cases hlt : loc_del < loc_last
  · dsimp only [tr']
    rw [ite_eq_left hlt]
    obtain ⟨hpres, hst_d, hrk_d⟩ := hpres_lt hlt
    obtain ⟨hm1_last, hrel2⟩ := bufMapRel_relocate_last hrel0 hb hcnt hlt hinj_ep
      (fun b' hb' loc hloc hne => (hpres b' hb' loc (hbkt' ▸ hloc) hne).1) hst_d
      (fun b' hb' loc hloc hne => (hpres b' hb' loc (hbkt' ▸ hloc) hne).2) hrk_d
    rw [← hbkt'] at hrel2
    split_ifs with htl
    · rw [ite_eq_left htl] at hrel2
      have hm1_some : m1 (fs.rKeyAt c U n_max θ b loc_last) = some (b, loc_last) := hm1_last htl
      have hm1_ne : m1 (fs.rKeyAt c U n_max θ b loc_last) ≠ none := by rw [hm1_some]; simp
      have hins := hv1.insert_spec (b := b) (loc := loc_del) hrk_l_lt
      obtain ⟨hna2, hia2, hnone2⟩ := hins.2.2.2.2.2.2 hm1_ne
      refine ⟨hia2.trans hia1, hna2.trans hna1, ⟨_, hins.1, hrel2⟩,
        fun id h => hnone2 id (hnone1 id h), fun id b' loc' hchk => ?_⟩
      obtain ⟨loc₁, hchk1⟩ := insert_same_bucket_checkSlot_some hv1 hrk_l_lt hm1_some hchk
      exact ⟨loc₁, hsome1 id b' loc₁ hchk1⟩
    · rw [ite_eq_right htl] at hrel2
      exact ⟨hia1, hna1, ⟨m1, hv1, hrel2⟩, hnone1, fun id b' loc' h => ⟨loc', hsome1 id b' loc' h⟩⟩
  · have heq_ll : loc_del = loc_last := by omega
    dsimp only [tr']
    rw [ite_eq_right hlt]
    subst heq_ll
    have hpres := hpres_eq rfl
    have hrel2 := bufMapRel_delete_last hrel0 hb hcnt
      (fun b' hb' loc hloc h1 h2 =>
        hinj_ep b' hb' loc hloc b hb loc_del (by omega) h1 h2)
      (fun b' hb' loc hloc => (hpres b' hb' loc (hbkt' ▸ hloc)).1)
      (fun b' hb' loc hloc => (hpres b' hb' loc (hbkt' ▸ hloc)).2)
    rw [← hbkt'] at hrel2
    exact ⟨hia1, hna1, ⟨m1, hv1, hrel2⟩, hnone1, fun id b' loc' h => ⟨loc', hsome1 id b' loc' h⟩⟩

/-- Unified preservation of `CoreFastInv.bufOld_valid` across both `loc_del = loc_last` and
`loc_del < loc_last` deletion cases. -/
theorem bufOld_valid_after_delete {c U V n_max b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {rKey_u : ℕ}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hb : b < numBucketsWhp n_max) (hcnt : fs.bktCount b = loc_last + 1)
    (hld_lt : loc_del < loc_last + 1)
    (hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hrs_eq : fs'.rebStage = fs.rebStage)
    (ho_eq : fs'.oldEp = fs.oldEp)
    (hbuf_old : fs'.buf fs.oldEp =
      let tr1 :=
        if fs.locState b loc_del = 2 + fs.oldEp then
          bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
        else fs.buf fs.oldEp
      if loc_del < loc_last then
        if fs.locState b loc_last = 2 + fs.oldEp then
          bufInsert (cTabWhp c) (bCharWhp n_max) tr1
            (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else tr1
      else tr1)
    (hpres_eq : loc_del = loc_last →
      ∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b',
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc)
    (hpres_lt : loc_del < loc_last →
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b', ¬(b' = b ∧ loc = loc_del) →
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc) ∧
      fs'.locState b loc_del = fs.locState b loc_last ∧
      fs'.rKeyAt c U n_max θ b loc_del = fs.rKeyAt c U n_max θ b loc_last) :
    if fs'.rebStage ≤ 3 then
      (fs'.buf fs'.oldEp).itemAlloc ≤ 2 * sMaxWhp c n_max ∧
      (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (fs'.buf fs'.oldEp).itemAlloc ∧
      ∃ oldMap,
        ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) oldMap ∧
        BufMapRel (numBucketsWhp n_max) (2 + fs'.oldEp) fs'.bktCount fs'.locState
          (fs'.rKeyAt c U n_max θ) oldMap
    else if fs'.rebStage = 4 then
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b', fs'.locState b' loc ≠ 2 + fs'.oldEp) ∧
      ClearableBufTrie (fs'.buf fs'.oldEp) ∧
      (fs'.buf fs'.oldEp).nodeAlloc ≤ 1 + cTabWhp c * (2 * sMaxWhp c n_max)
    else
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b', fs'.locState b' loc ≠ 2 + fs'.oldEp) ∧
      ValidBufTrie (cTabWhp c) (bCharWhp n_max) (fs'.buf fs'.oldEp) (fun _ => none) ∧
      (fs'.buf fs'.oldEp).nodeAlloc = 1 ∧
      (fs'.buf fs'.oldEp).itemAlloc = 0 := by
  have hbo := hc.bufOld_valid
  dsimp only at hbuf_old
  rw [ho_eq, hrs_eq]
  have hno_old_lift :
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs.bktCount b', fs.locState b' loc ≠ 2 + fs.oldEp) →
      fs'.buf fs.oldEp = fs.buf fs.oldEp ∧
      ∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b',
        fs'.locState b' loc ≠ 2 + fs.oldEp := by
    intro hno
    have hne_d : fs.locState b loc_del ≠ 2 + fs.oldEp := hno b hb loc_del (hcnt ▸ hld_lt)
    have hne_l : fs.locState b loc_last ≠ 2 + fs.oldEp := hno b hb loc_last (by omega)
    have hbe : fs'.buf fs.oldEp = fs.buf fs.oldEp := by
      rw [hbuf_old]
      by_cases hlt : loc_del < loc_last
      · rw [ite_eq_left hlt, ite_eq_right hne_l, ite_eq_right hne_d]
      · rw [ite_eq_right hlt, ite_eq_right hne_d]
    refine ⟨hbe, fun b' hb' loc hloc => ?_⟩
    by_cases hlt : loc_del < loc_last
    · obtain ⟨hpres, hst_d, _⟩ := hpres_lt hlt
      by_cases hbd : b' = b ∧ loc = loc_del
      · rcases hbd with ⟨rfl, rfl⟩; rwa [hst_d]
      · rw [(hpres b' hb' loc hloc hbd).1]
        exact hno b' hb' loc (lt_of_lt_update_le (by omega) (hbkt' ▸ hloc))
    · have heq : loc_del = loc_last := by omega
      rw [((hpres_eq heq) b' hb' loc hloc).1]
      exact hno b' hb' loc (lt_of_lt_update_le (by omega) (hbkt' ▸ hloc))
  split_ifs at hbo ⊢ with hs3 hs4
  · obtain ⟨hia_eq, hna_eq, hmap_old, _⟩ :=
      buf_valid_after_delete (ep := fs.oldEp) (fs' := fs') hc hb hcnt hld_lt hrk_del hbo hbkt'
        hpres_eq hpres_lt
    rw [← hbuf_old] at hia_eq hna_eq hmap_old
    exact ⟨hia_eq ▸ hbo.1, hna_eq ▸ hia_eq ▸ hbo.2.1, hmap_old⟩
  · obtain ⟨hbe, hno'⟩ := hno_old_lift hbo.1
    rw [hbe]; exact ⟨hno', hbo.2.1, hbo.2.2⟩
  · obtain ⟨hbe, hno'⟩ := hno_old_lift hbo.1
    rw [hbe]; exact ⟨hno', hbo.2.1, hbo.2.2.1, hbo.2.2.2⟩

/-- Discharges Stages `0, 1, 3` (and `≥ 4`) of `ValidEpochStagePreTick` uniformly across both
`fastDelete` branches, leaving only Stage `2` for the caller. -/
theorem preTick_after_delete_of_stage2 {c U V n_max b loc_del loc_last : ℕ}
    {θ : SeedWhp c U n_max} {fs fs' : FastState} {dict : State U} {rKey_u : ℕ}
    (hc : CoreFastInv c U V n_max θ fs dict)
    (hpre0 : ValidEpochStagePreTick c U n_max θ fs)
    (hb : b < numBucketsWhp n_max) (hcnt : fs.bktCount b = loc_last + 1)
    (hld_lt : loc_del < loc_last + 1)
    (hrk_del : fs.rKeyAt c U n_max θ b loc_del = rKey_u)
    (hbkt' : fs'.bktCount = Function.update fs.bktCount b loc_last)
    (hrs_eq : fs'.rebStage = fs.rebStage)
    (ho_eq : fs'.oldEp = fs.oldEp)
    (hsc_eq : fs'.stageCursor = fs.stageCursor)
    (hdc_eq : fs'.dirtyCount = fs.dirtyCount)
    (hdb_eq : fs'.dirtyBuckets = fs.dirtyBuckets)
    (hdi_eq : fs'.dirtyIdx = fs.dirtyIdx)
    (hrq_eq : fs'.rebQueued = fs.rebQueued)
    (hdn_eq : fs'.rebDoneFlag = fs.rebDoneFlag)
    (hbuf_old : fs'.buf fs.oldEp =
      let tr1 :=
        if fs.locState b loc_del = 2 + fs.oldEp then
          bufDelete (cTabWhp c) (bCharWhp n_max) (fs.buf fs.oldEp) rKey_u
        else fs.buf fs.oldEp
      if loc_del < loc_last then
        if fs.locState b loc_last = 2 + fs.oldEp then
          bufInsert (cTabWhp c) (bCharWhp n_max) tr1
            (fs.rKeyAt c U n_max θ b loc_last) b loc_del
        else tr1
      else tr1)
    (hpres_eq : loc_del = loc_last →
      ∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b',
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc)
    (hpres_lt : loc_del < loc_last →
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b', ¬(b' = b ∧ loc = loc_del) →
        fs'.locState b' loc = fs.locState b' loc ∧
        fs'.rKeyAt c U n_max θ b' loc = fs.rKeyAt c U n_max θ b' loc) ∧
      fs'.locState b loc_del = fs.locState b loc_last ∧
      fs'.rKeyAt c U n_max θ b loc_del = fs.rKeyAt c U n_max θ b loc_last)
    (hstage2 : fs.rebStage = 2 →
      fs'.dirtyCount ≤ 2 * sMaxWhp c n_max ∧
      fs'.dirtyIdx < fs'.dirtyCount ∧
      (∀ j < fs'.dirtyCount, fs'.dirtyBuckets j < numBucketsWhp n_max) ∧
      (∀ j₁ < fs'.dirtyCount, ∀ j₂ < fs'.dirtyCount,
        fs'.dirtyBuckets j₁ = fs'.dirtyBuckets j₂ → j₁ = j₂) ∧
      (∀ j < fs'.dirtyCount,
        (j < fs'.dirtyIdx → fs'.rebDoneFlag (fs'.dirtyBuckets j) = 1) ∧
        (fs'.dirtyIdx ≤ j → fs'.rebDoneFlag (fs'.dirtyBuckets j) = 0)) ∧
      (∀ b' < numBucketsWhp n_max, ∀ loc < fs'.bktCount b', fs'.locState b' loc = 2 + fs.oldEp →
        ∃ j < fs'.dirtyCount, fs'.dirtyBuckets j = b') ∧
      (fs'.rebCandSalt < sMaxWhp c n_max →
        let b_cur := fs'.dirtyBuckets fs'.dirtyIdx
        ((fs'.rebScanCursor = 0 ∧ fs'.rebInsCount = 0) ∨
         (16 ≤ fs'.rebScanCursor ∧ fs'.rebScanCursor ≤ fs'.bktCount b_cur ∧
          16 * fs'.rebInsCount ≤ 17 * fs'.rebScanCursor)) ∧
        (∀ l₁ < min (fs'.bktCount b_cur) fs'.rebScanCursor,
         ∀ l₂ < min (fs'.bktCount b_cur) fs'.rebScanCursor,
          (fs'.locState b_cur l₁ = 1 ∨ fs'.locState b_cur l₁ = 2 + fs.oldEp) →
          (fs'.locState b_cur l₂ = 1 ∨ fs'.locState b_cur l₂ = 2 + fs.oldEp) →
          fs'.fpAt c U n_max θ fs'.rebCandSalt b_cur l₁ =
            fs'.fpAt c U n_max θ fs'.rebCandSalt b_cur l₂ →
          l₁ = l₂) ∧
        ∃ rebMap,
          ValidWhpSlice n_max fs'.rebInsCount (fs'.slices (fs'.rebSliceIdx b_cur)) rebMap ∧
          SliceMapRel (fs'.fpAt c U n_max θ fs'.rebCandSalt b_cur)
            (fun loc => fs'.locState b_cur loc = 1 ∨ fs'.locState b_cur loc = 2 + fs.oldEp)
            (min (fs'.bktCount b_cur) fs'.rebScanCursor) rebMap)) :
    ValidEpochStagePreTick c U n_max θ fs' := by
  dsimp only [ValidEpochStagePreTick] at hpre0 ⊢
  rw [hrs_eq, ho_eq, hsc_eq, hdc_eq, hdb_eq, hdi_eq, hrq_eq, hdn_eq]
  have hold_props : fs.rebStage ≤ 3 →
      (fs'.buf fs.oldEp).itemAlloc = (fs.buf fs.oldEp).itemAlloc ∧
      (∀ id, bufCheckSlot (fs.buf fs.oldEp) id = none →
        bufCheckSlot (fs'.buf fs.oldEp) id = none) ∧
      (∀ id b' loc', bufCheckSlot (fs'.buf fs.oldEp) id = some (b', loc') →
        ∃ loc₀, bufCheckSlot (fs.buf fs.oldEp) id = some (b', loc₀)) := by
    intro hle3
    have hbo_v := hc.bufOld_valid
    simp only [hle3, ↓reduceIte] at hbo_v
    dsimp only at hbuf_old
    obtain ⟨hia_eq, _, _, hnone_old, hsome_old⟩ :=
      buf_valid_after_delete (ep := fs.oldEp) (fs' := fs') hc hb hcnt hld_lt hrk_del hbo_v hbkt'
        hpres_eq hpres_lt
    rw [← hbuf_old] at hia_eq hnone_old hsome_old
    exact ⟨hia_eq, hnone_old, hsome_old⟩
  split_ifs at hpre0 ⊢ with hs0 hs1 hs2 hs3
  · obtain ⟨hia_eq, _, hsome_old⟩ := hold_props (by omega)
    rw [hia_eq]
    exact ⟨hpre0.1, fun id hid b' loc' hchk =>
      (hsome_old id b' loc' hchk).elim fun loc₀ h => hpre0.2 id hid b' loc₀ h⟩
  · obtain ⟨hia_eq, _, hsome_old⟩ := hold_props (by omega)
    rcases hpre0 with ⟨hs1_1, hs1_2, hs1_3, hs1_4, hs1_5, hs1_6⟩
    rw [hia_eq]
    exact ⟨hs1_1, hs1_2, hs1_3, hs1_4,
      fun id hid b' loc' hchk =>
        (hsome_old id b' loc' hchk).elim fun loc₀ h => hs1_5 id hid b' loc₀ h,
      fun id hid b' loc' hchk =>
        (hsome_old id b' loc' hchk).elim fun loc₀ h => hs1_6 id hid b' loc₀ h⟩
  · have hs2' := hstage2 hs2
    rwa [hdc_eq, hdb_eq, hdi_eq, hdn_eq] at hs2'
  · obtain ⟨hia_eq, hnone_old, _⟩ := hold_props (by omega)
    rw [hia_eq]
    exact ⟨hpre0.1, fun id hid => hnone_old id (hpre0.2 id hid)⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp.ModelStepAux

end
