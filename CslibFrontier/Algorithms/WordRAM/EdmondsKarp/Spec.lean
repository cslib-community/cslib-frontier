/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.GomoryHu.WeightedCut
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp
import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.BfsSemantics
import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Bounds
import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Internal
import CslibFrontier.Foundations.Data.List.RowMajor
import CslibFrontier.Tactic.Realize
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Relocatable dense Edmonds–Karp solver, resource bounds, and specification

Defines the relocatable solver subroutine `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg` together
with its exact-basis realization, `O(n ^ 5)` memory budget (`ekCost`), history admissibility, frame
property, return-value bound, and end-to-end minimum-cut correctness (`ekProg_spec`).

## Main definitions

* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg`, `ekCost`: the relocatable dense Edmonds–Karp
  subroutine and its `O(n ^ 5)` memory-operation budget.

## Main results

* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_realizes`: compilation to `Basis.exact`.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.memoryCost_ekProg_le`, `validHistory_ekProg`,
  `preservesAt_ekProg`, `ekProg_result_le`: cost, admissibility, frame, and return-value bound.
* `Cslib.Algorithms.WordRAM.EdmondsKarp.ekProg_spec`: correctness of `ekProg` for minimum `s`–`t`
  cuts (`IsMinCutBetween (cutWeight W)`).
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Lean.GomoryHu Cslib.WeightedCut
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.Algorithms.WordRAM.EdmondsKarp.Internal
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

/-- `omega` after unfolding the layout abbreviations and reducing projections. -/
local macro "ek_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
    predAddr] at *
  omega))

/-! ### Semantics: the augmenting path, its bottleneck, and the augmentation -/

private def buildPath {M : ℕ} (parOf : Fin M → Fin M) : ℕ → Fin M → List (Fin M)
  | 0, cur => [cur]
  | rem + 1, cur => buildPath parOf rem (parOf cur) ++ [cur]

private theorem buildPath_ne_nil {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, buildPath parOf rem cur ≠ []
  | 0, _ => List.cons_ne_nil _ _
  | _ + 1, cur => List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil cur [])

private theorem buildPath_getLast? {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, (buildPath parOf rem cur).getLast? = some cur
  | 0, _ => rfl
  | rem + 1, cur => by
    unfold buildPath
    rw [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil cur [])]
    rfl

private theorem buildPath_props {M : ℕ} {N : Network (Fin M)} (f : N.Flow)
    (parOf : Fin M → Fin M)
    (hpar : ∀ x : Fin M, 0 < f.resDist x → f.resDist x < M →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x) :
    ∀ rem (cur : Fin M), rem < M → f.resDist cur = rem →
      (buildPath parOf rem cur).head? = some N.s ∧
      (∀ z ∈ buildPath parOf rem cur, f.resDist z ≤ rem) ∧
      (buildPath parOf rem cur).Nodup ∧
      (∀ e ∈ pathArcs (buildPath parOf rem cur), 1 ≤ f.resCap e.1 e.2)
  | 0, cur, _, hcur => by
    have hs : cur = N.s := f.eq_source_of_resDist_eq_zero hcur
    refine ⟨by simp [buildPath, hs], ?_, List.nodup_singleton cur, by simp [buildPath]⟩
    intro z hz
    simp only [buildPath, List.mem_singleton] at hz
    subst hz
    exact le_of_eq hcur
  | rem + 1, cur, hrem, hcur => by
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    obtain ⟨hhead, hle, hnd, harcs⟩ := buildPath_props f parOf hpar rem (parOf cur)
      (by omega) hp_rem
    have hne := buildPath_ne_nil parOf rem (parOf cur)
    have hlast := buildPath_getLast? parOf rem (parOf cur)
    unfold buildPath
    refine ⟨by rw [List.head?_append_of_ne_nil _ hne]; exact hhead, ?_, ?_, ?_⟩
    · intro z hz
      rcases List.mem_append.mp hz with hz1 | hz2
      · exact (hle z hz1).trans (Nat.le_succ rem)
      · simp only [List.mem_singleton] at hz2; subst hz2; omega
    · refine List.Nodup.append hnd (List.nodup_singleton cur) fun a ha hb => ?_
      simp only [List.mem_singleton] at hb
      subst hb
      have := hle a ha
      omega
    · rw [pathArcs_append_singleton hne hlast]
      intro e he
      rcases List.mem_append.mp he with he1 | he2
      · exact harcs e he1
      · simp only [List.mem_singleton] at he2; subst he2; exact hrc_p


private theorem length_buildPath {M : ℕ} (parOf : Fin M → Fin M) :
    ∀ rem cur, (buildPath parOf rem cur).length = rem + 1
  | 0, _ => rfl
  | rem + 1, cur => by
    rw [buildPath, List.length_append, length_buildPath parOf rem (parOf cur)]
    rfl

private theorem length_pathArcs_buildPath {M : ℕ} (parOf : Fin M → Fin M) (rem : ℕ)
    (cur : Fin M) : (pathArcs (buildPath parOf rem cur)).length = rem := by
  have h := length_pathArcs_add_one (buildPath_ne_nil parOf rem cur)
  rw [length_buildPath] at h
  omega

private theorem pathArcs_buildPath_succ {M : ℕ} (parOf : Fin M → Fin M) (rem : ℕ)
    (cur : Fin M) :
    pathArcs (buildPath parOf (rem + 1) cur) =
      pathArcs (buildPath parOf rem (parOf cur)) ++ [(parOf cur, cur)] := by
  rw [buildPath]
  exact pathArcs_append_singleton (buildPath_ne_nil parOf rem (parOf cur))
    (buildPath_getLast? parOf rem (parOf cur))

section Walks

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- The bottleneck walk computes, from `δ`, the minimum of `δ` and the residual capacities along
the path to `cur` built from the parent function. -/
private theorem iterate_bnStep_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f t)
    (parOf : Fin n → Fin n)
    (hpar : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x)
    (hp_mem : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
      t.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = (parOf x).1) :
    ∀ rem (cur : Fin n) (δ : ℕ), rem < n → f.resDist cur = rem →
      let δ' := ((Memory.spec 0).clientResult t
        (iterate bnStep ⟨n, mb, sb, B⟩ rem (cur.1, δ))).2
      δ' ≤ δ ∧ (∀ e ∈ pathArcs (buildPath parOf rem cur), δ' ≤ f.resCap e.1 e.2) ∧
        (δ' = δ ∨ ∃ e ∈ pathArcs (buildPath parOf rem cur), δ' = f.resCap e.1 e.2)
  | 0, cur, δ, _, _ => by
    refine ⟨le_rfl, ?_, Or.inl rfl⟩
    simp [buildPath, pathArcs_singleton]
  | rem + 1, cur, δ, hrem, hcur => by
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    have hpv := hp_mem cur (by omega) (by omega)
    set δ₁ := if f.resCap (parOf cur) cur ≤ δ then f.resCap (parOf cur) cur else δ with hδ₁
    have hstep : (Memory.spec 0).clientResult t (bnStep (⟨n, mb, sb, B⟩, (cur.1, δ))) =
        ((parOf cur).1, δ₁) := by
      unfold bnStep
      dsimp only
      rw [clientResult_bind_read, ite_eq_left cur.2, clientResult_bind_read, hpv,
        ite_eq_left (parOf cur).2, clientResult_bind,
        readResCap_state, readResCap_spec hB hW hf (parOf cur) cur]
      rw [hδ₁]
      split_ifs <;> rfl
    have hred : ((Memory.spec 0).clientResult t
        (iterate bnStep ⟨n, mb, sb, B⟩ (rem + 1) (cur.1, δ))).2 =
        ((Memory.spec 0).clientResult t
          (iterate bnStep ⟨n, mb, sb, B⟩ rem ((parOf cur).1, δ₁))).2 := by
      change ((Memory.spec 0).clientResult t
        (bnStep (⟨n, mb, sb, B⟩, (cur.1, δ)) >>= iterate bnStep ⟨n, mb, sb, B⟩ rem)).2 = _
      rw [clientResult_bind, bnStep_state, hstep]
    have hih := iterate_bnStep_spec hB hW f hf parOf hpar hp_mem rem (parOf cur) δ₁
      (by omega) hp_rem
    dsimp only at hih ⊢
    rw [hred, pathArcs_buildPath_succ]
    obtain ⟨h1, h2, h3⟩ := hih
    have hδ₁δ : δ₁ ≤ δ := by rw [hδ₁]; split_ifs <;> omega
    have hδ₁r : δ₁ ≤ f.resCap (parOf cur) cur := by rw [hδ₁]; split_ifs <;> omega
    refine ⟨h1.trans hδ₁δ, fun e he => ?_, ?_⟩
    · rcases List.mem_append.mp he with he | he
      · exact h2 e he
      · rw [List.mem_singleton] at he
        subst he
        exact h1.trans hδ₁r
    · rcases h3 with h3 | ⟨e, he, h3⟩
      · rw [h3, hδ₁]
        split_ifs
        · exact Or.inr ⟨(parOf cur, cur), List.mem_append_right _ (List.mem_singleton_self _),
            rfl⟩
        · exact Or.inl rfl
      · exact Or.inr ⟨e, List.mem_append_left _ he, h3⟩

end Walks


private theorem augStep_spec {c : Ctx} {δ cur p : ℕ} (hcur : cur < c.n) (hp : p < c.n)
    {t : Memory.State} (hpred : t.mem (predAddr c cur) = p)
    (hfB : t.mem (flowAddr c p cur) ≤ c.capBound) (hδ : δ ≤ 2 * c.capBound) :
    (Memory.spec 0).clientResult t (augStep ((c, δ), cur)) = p ∧
    (Memory.spec 0).clientState t (augStep ((c, δ), cur)) =
      ⟨Function.update (Function.update t.mem (flowAddr c cur p)
          (t.mem (flowAddr c cur p) - min δ (t.mem (flowAddr c cur p))))
        (flowAddr c p cur) (t.mem (flowAddr c p cur) + (δ - min δ (t.mem (flowAddr c cur p)))),
        t.frontier⟩ := by
  refine ⟨?_, ?_⟩
  · unfold augStep
    dsimp only
    rw [clientResult_bind_read, ite_eq_left hcur, clientResult_bind_read, hpred, ite_eq_left hp,
      clientResult_bind_read, clientResult_bind_read, ite_eq_left ⟨hfB, hδ⟩]
    rfl
  · unfold augStep
    dsimp only
    rw [clientState_bind_read, ite_eq_left hcur, clientState_bind_read, hpred, ite_eq_left hp,
      clientState_bind_read, clientState_bind_read, ite_eq_left ⟨hfB, hδ⟩]
    rfl

section AugWalk

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- The augmentation walk pushes `δ` along the path to `cur` built from the parent function,
cancelling reverse flow first, exactly as `Network.Flow.augmentFun`. -/
private theorem iterate_augStep_spec (hB : ∀ u v, W u v ≤ B) (f : (Network.mk W src snk).Flow)
    (parOf : Fin n → Fin n)
    (hpar : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x)
    (δ : ℕ) (hδ : δ ≤ 2 * B) :
    ∀ rem (cur : Fin n) (u_st : Memory.State), rem < n → f.resDist cur = rem →
      (∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        u_st.mem (predAddr ⟨n, mb, sb, B⟩ x.1) = (parOf x).1) →
      (∀ x y : Fin n,
        ((x, y) ∈ pathArcs (buildPath parOf rem cur) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem cur)) →
        u_st.mem (flowAddr ⟨n, mb, sb, B⟩ x.1 y.1) = f x y) →
      ∀ x y : Fin n,
        ((Memory.spec 0).clientState u_st
          (iterate augStep (⟨n, mb, sb, B⟩, δ) rem cur.1)).mem (flowAddr ⟨n, mb, sb, B⟩ x.1 y.1) =
          if (x, y) ∈ pathArcs (buildPath parOf rem cur) then f x y + (δ - min δ (f y x))
          else if (y, x) ∈ pathArcs (buildPath parOf rem cur) then f x y - min δ (f x y)
          else u_st.mem (flowAddr ⟨n, mb, sb, B⟩ x.1 y.1)
  | 0, cur, u_st, _, _, _, _ => fun x y => by
    simp only [iterate, buildPath, pathArcs_singleton, List.not_mem_nil, ↓reduceIte]
    rfl
  | rem + 1, cur, u_st, hrem, hcur, hp_mem, hf_sub => by
    intro x y
    set c : Ctx := ⟨n, mb, sb, B⟩
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    have hne_pc : parOf cur ≠ cur := fun h => by rw [h] at hp_rem; omega
    have harcs_eq := pathArcs_buildPath_succ parOf rem cur
    have hf_rev : u_st.mem (flowAddr c cur.1 (parOf cur).1) = f cur (parOf cur) :=
      hf_sub cur (parOf cur) (Or.inr (by rw [harcs_eq]; simp))
    have hf_fwd : u_st.mem (flowAddr c (parOf cur).1 cur.1) = f (parOf cur) cur :=
      hf_sub (parOf cur) cur (Or.inl (by rw [harcs_eq]; simp))
    have hfB : u_st.mem (flowAddr c (parOf cur).1 cur.1) ≤ c.capBound := by
      rw [hf_fwd]; exact (f.le_cap _ _).trans (hB _ _)
    obtain ⟨hres1, hst1⟩ := augStep_spec (c := c) (δ := δ) cur.2 (parOf cur).2
      (hp_mem cur (by omega) (by omega)) hfB hδ
    set u1 := (Memory.spec 0).clientState u_st (augStep ((c, δ), cur.1))
    have haddr : ∀ a b a' b' : Fin n, flowAddr c a.1 b.1 = flowAddr c a'.1 b'.1 →
        a = a' ∧ b = b' := fun a b a' b' h => by
      dsimp only [c, flowAddr] at h
      exact List.fin_mul_add_inj (by omega)
    have hflow1 : ∀ x y : Fin n, u1.mem (flowAddr c x.1 y.1) =
        if (x, y) = (parOf cur, cur) then f x y + (δ - min δ (f y x))
        else if (y, x) = (parOf cur, cur) then f x y - min δ (f x y)
        else u_st.mem (flowAddr c x.1 y.1) := by
      intro x y
      rw [hst1]
      dsimp only
      rw [hf_rev, hf_fwd]
      by_cases hxy : (x, y) = (parOf cur, cur)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
        rw [ite_eq_left rfl, Function.update_self]
      · rw [ite_eq_right hxy, Function.update_of_ne (fun h => hxy (Prod.ext (haddr _ _ _ _ h).1
          (haddr _ _ _ _ h).2))]
        by_cases hyx : (y, x) = (parOf cur, cur)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyx
          rw [ite_eq_left rfl, Function.update_self]
        · rw [ite_eq_right hyx, Function.update_of_ne (fun h => hyx (Prod.ext (haddr _ _ _ _ h).2
            (haddr _ _ _ _ h).1))]
    have hpar1 : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        u1.mem (predAddr c x.1) = (parOf x).1 := fun x hx1 hx2 => by
      rw [preservesAt_augStep (c := c) (δ := δ) (cur := cur.1) (Or.inr (by ek_omega)) u_st]
      exact hp_mem x hx1 hx2
    obtain ⟨_, hle_rem, _, _⟩ := buildPath_props f parOf hpar rem (parOf cur) (by omega) hp_rem
    have hdisj : ∀ a b : Fin n, (a, b) ∈ pathArcs (buildPath parOf rem (parOf cur)) →
        a ≠ cur ∧ b ≠ cur := by
      intro a b hab
      have ha := hle_rem a (fst_mem_of_mem_pathArcs hab)
      have hb := hle_rem b (snd_mem_of_mem_pathArcs hab)
      exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩
    have hf_sub1 : ∀ x y : Fin n,
        ((x, y) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem (parOf cur))) →
        u1.mem (flowAddr c x.1 y.1) = f x y := by
      intro x y hmem
      rw [hflow1 x y]
      rcases hmem with hxy | hyx
      · obtain ⟨_, hyc⟩ := hdisj x y hxy
        have h1 : (x, y) ≠ (parOf cur, cur) := fun h => hyc (Prod.mk.inj h).2
        have h2 : (y, x) ≠ (parOf cur, cur) := fun h => (hdisj x y hxy).1 (Prod.mk.inj h).2
        rw [ite_eq_right h1, ite_eq_right h2]
        exact hf_sub x y (Or.inl (by rw [harcs_eq]; exact List.mem_append_left _ hxy))
      · obtain ⟨hxc, _⟩ := hdisj y x hyx
        have h1 : (x, y) ≠ (parOf cur, cur) := fun h => hxc (Prod.mk.inj h).2
        have h2 : (y, x) ≠ (parOf cur, cur) := fun h => (hdisj y x hyx).2 (Prod.mk.inj h).2
        rw [ite_eq_right h1, ite_eq_right h2]
        exact hf_sub x y (Or.inr (by rw [harcs_eq]; exact List.mem_append_left _ hyx))
    have hih := iterate_augStep_spec hB f parOf hpar δ hδ rem (parOf cur) u1 (by omega) hp_rem
      hpar1 hf_sub1 x y
    change ((Memory.spec 0).clientState u_st
      (augStep ((c, δ), cur.1) >>= iterate augStep (c, δ) rem)).mem _ = _
    rw [clientState_bind, hres1, hih, hflow1 x y, harcs_eq]
    simp only [List.mem_append, List.mem_singleton]
    by_cases h1 : (x, y) ∈ pathArcs (buildPath parOf rem (parOf cur))
    · rw [ite_eq_left h1, ite_eq_left (Or.inl h1)]
    · by_cases h2 : (x, y) = (parOf cur, cur)
      · have h3 : (y, x) ∉ pathArcs (buildPath parOf rem (parOf cur)) := fun h =>
          (hdisj y x h).1 (Prod.mk.inj h2).2
        rw [ite_eq_right h1, ite_eq_right h3, ite_eq_left h2, ite_eq_left (Or.inr h2)]
      · have h12 : ¬ ((x, y) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
            (x, y) = (parOf cur, cur)) := not_or.mpr ⟨h1, h2⟩
        rw [ite_eq_right h1, ite_eq_right h12]
        by_cases h3 : (y, x) ∈ pathArcs (buildPath parOf rem (parOf cur))
        · rw [ite_eq_left h3, ite_eq_left (Or.inl h3)]
        · by_cases h4 : (y, x) = (parOf cur, cur)
          · rw [ite_eq_right h3, ite_eq_right h2, ite_eq_left h4, ite_eq_left (Or.inr h4)]
          · have h34 : ¬ ((y, x) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
                (y, x) = (parOf cur, cur)) := not_or.mpr ⟨h3, h4⟩
            rw [ite_eq_right h3, ite_eq_right h2, ite_eq_right h4, ite_eq_right h34]

end AugWalk


/-! ### Semantics: one round -/

section Round

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- One running round from a state storing the flow `f`: either `t` is not reached, and the
round leaves the flow alone and stores the residual distances, or it pushes the bottleneck along
a shortest augmenting path. -/
private theorem roundStep_spec (hst : src ≠ snk) (hB : ∀ u v, W u v ≤ B)
    (hlay : mb + n * n ≤ sb) {t : Memory.State} (hW : MatLoaded n mb W t)
    (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f t) :
    let r := (Memory.spec 0).clientResult t (roundStep ((⟨n, mb, sb, B⟩, (src.1, snk.1)), 0))
    let t' := (Memory.spec 0).clientState t (roundStep ((⟨n, mb, sb, B⟩, (src.1, snk.1)), 0))
    (r = 1 ∧ FlowStored sb f t' ∧
        (∀ x : Fin n, t'.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = f.resDist x) ∧ f.resDist snk = n) ∨
      (r = 0 ∧ ∃ (p : List (Fin n)) (hp : f.IsShortestAugmentingPath p),
        FlowStored sb (f.augmentByBottleneck p hp.isAugmentingPath) t') := by
  intro r t'
  set c : Ctx := ⟨n, mb, sb, B⟩
  obtain ⟨hb_low, hb_dist, hb_par⟩ := bfsProg_spec (B := B) (src := src) (snk := snk) hB hlay hW
    f hf
  set tb := (Memory.spec 0).clientState t (bfsProg (c, src.1))
  have hfb : FlowStored sb f tb := hf.congr hb_low
  have hWb : MatLoaded n mb W tb := hW.congr hlay hb_low
  have hred_r : r = (Memory.spec 0).clientResult tb
      (do
        let dt ← Memory.read (distAddr c snk.1)
        if 0 < dt ∧ dt < c.n then
          let r ← iterate bnStep c dt (snk.1, 2 * c.capBound)
          let _ ← iterate augStep (c, r.2) dt snk.1
          pure 0
        else pure 1) := by
    change (Memory.spec 0).clientResult t (roundStep ((c, (src.1, snk.1)), 0)) = _
    unfold roundStep
    dsimp only
    rw [clientResult_bind_read, ite_eq_left rfl, clientResult_bind]
  have hred_s : t' = (Memory.spec 0).clientState tb
      (do
        let dt ← Memory.read (distAddr c snk.1)
        if 0 < dt ∧ dt < c.n then
          let r ← iterate bnStep c dt (snk.1, 2 * c.capBound)
          let _ ← iterate augStep (c, r.2) dt snk.1
          pure 0
        else pure 1) := by
    change (Memory.spec 0).clientState t (roundStep ((c, (src.1, snk.1)), 0)) = _
    unfold roundStep
    dsimp only
    rw [clientState_bind_read, ite_eq_left rfl, clientState_bind]
  rw [clientResult_bind_read] at hred_r
  rw [clientState_bind_read] at hred_s
  have hdt : tb.mem (distAddr c snk.1) = f.resDist snk := hb_dist snk
  rw [hdt] at hred_r hred_s
  by_cases hreach : 0 < f.resDist snk ∧ f.resDist snk < c.n
  · right
    rw [ite_eq_left hreach] at hred_r hred_s
    refine ⟨?_, ?_⟩
    · rw [hred_r, clientResult_bind, clientResult_bind,
        clientResult_pure]
    let parOf : Fin n → Fin n := fun x =>
      if h : tb.mem (predAddr c x.1) < n then ⟨tb.mem (predAddr c x.1), h⟩ else x
    have hpar_spec : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        tb.mem (predAddr c x.1) = (parOf x).1 ∧
          f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x := by
      intro x hx1 hx2
      obtain ⟨u, hu1, hu2, hu3⟩ := hb_par x hx1 hx2
      have hlt : tb.mem (predAddr c x.1) < n := by rw [hu1]; exact u.2
      have hpu : parOf x = u := by
        simp only [parOf, dite_eq_left hlt]
        exact Fin.ext hu1
      exact ⟨by rw [hpu, hu1], by rw [hpu]; exact hu2, by rw [hpu]; exact hu3⟩
    have hpar : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x :=
      fun x h1 h2 => (hpar_spec x h1 h2).2
    have hp_mem : ∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        tb.mem (predAddr c x.1) = (parOf x).1 := fun x h1 h2 => (hpar_spec x h1 h2).1
    set k := f.resDist snk
    let p := buildPath parOf k snk
    obtain ⟨hhead, -, hnd, harcs⟩ := buildPath_props f parOf hpar k snk hreach.2 rfl
    have hp : f.IsShortestAugmentingPath p :=
      ⟨⟨hnd, hhead, buildPath_getLast? parOf k snk, fun e he => harcs e he⟩,
        length_pathArcs_buildPath parOf k snk⟩
    refine ⟨p, hp, ?_⟩
    -- the bottleneck
    obtain ⟨hδ1, hδ2, hδ3⟩ := iterate_bnStep_spec hB hWb f hfb parOf hpar hp_mem k snk
      (2 * B) hreach.2 rfl
    set δ := ((Memory.spec 0).clientResult tb (iterate bnStep c k (snk.1, 2 * B))).2
    have hne : pathArcs p ≠ [] := by
      intro h
      have := length_pathArcs_buildPath parOf k snk
      rw [show buildPath parOf k snk = p from rfl, h] at this
      simp at this
      omega
    have hδ_eq : δ = f.bottleneck p := by
      obtain ⟨e₀, he₀, hbe₀⟩ := f.exists_mem_pathArcs_resCap_eq_bottleneck hne
      refine le_antisymm ((hδ2 e₀ he₀).trans hbe₀.le) ?_
      rcases hδ3 with h | ⟨e, he, h⟩
      · rw [h]
        refine (f.bottleneck_le_resCap he₀).trans ?_
        have := f.resCap_le_cap_add_cap e₀.1 e₀.2
        have h1 := hB e₀.1 e₀.2
        have h2 := hB e₀.2 e₀.1
        change f.resCap e₀.1 e₀.2 ≤ W e₀.1 e₀.2 + W e₀.2 e₀.1 at this
        omega
      · rw [h]
        exact f.bottleneck_le_resCap he
    have hδB : δ ≤ 2 * B := hδ1
    -- the augmentation
    have hflows := iterate_augStep_spec (mb := mb) (sb := sb) hB f parOf hpar δ hδB k snk tb
      hreach.2 rfl hp_mem (fun x y _ => hfb x y)
    have hst_eq : t' = (Memory.spec 0).clientState tb (iterate augStep (c, δ) k snk.1) := by
      rw [hred_s, clientState_bind,
        clientState_iterate_eq_of _ _ (fun _ t'' => bnStep_state _ t''),
        clientState_bind, clientState_pure]
    intro x y
    rw [hst_eq]
    change _ = Network.Flow.augmentFun f p (f.bottleneck p) x y
    rw [hflows x y, ← hδ_eq, hfb x y]
    rfl
  · left
    rw [ite_eq_right hreach] at hred_r hred_s
    have hk : f.resDist snk = n := by
      have hle : f.resDist snk ≤ n := by simpa [Fintype.card_fin] using f.resDist_le_card snk
      by_contra hne
      have hpos : 0 < f.resDist snk := by
        by_contra h0
        exact hst (f.eq_source_of_resDist_eq_zero (by omega)).symm
      exact hreach ⟨hpos, by change _ < n; omega⟩
    rw [clientState_pure] at hred_s
    rw [clientResult_pure] at hred_r
    rw [hred_s]
    exact ⟨hred_r, hfb, hb_dist, hk⟩

end Round


/-! ### Semantics: the cut sum and the whole solver -/

private theorem sum_filter_lt_succ {n u : ℕ} (hu : u < n) (P : Fin n → Prop) [DecidablePred P]
    (g : Fin n → ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < u + 1 ∧ P x), g x =
      ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < u ∧ P x), g x +
        if P ⟨u, hu⟩ then g ⟨u, hu⟩ else 0 := by
  have h := Finset.sum_filter_add_sum_filter_not
    (Finset.univ.filter fun x : Fin n => x.1 < u + 1 ∧ P x) (fun x : Fin n => x.1 = u) g
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have e1 : (Finset.univ.filter fun x : Fin n => (x.1 < u + 1 ∧ P x) ∧ ¬ x.1 = u) =
      Finset.univ.filter fun x : Fin n => x.1 < u ∧ P x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩
  have e2 : ∑ x ∈ Finset.univ.filter (fun x : Fin n => (x.1 < u + 1 ∧ P x) ∧ x.1 = u), g x =
      if P ⟨u, hu⟩ then g ⟨u, hu⟩ else 0 := by
    split_ifs with hP
    · rw [Finset.sum_eq_single_of_mem ⟨u, hu⟩ (by simp [hP])]
      intro x hx hxu
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact absurd (Fin.ext hx.2) hxu
    · rw [Finset.sum_eq_zero]
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hxe : x = ⟨u, hu⟩ := Fin.ext hx.2
      exact absurd (hxe ▸ hx.1.2) hP
  rw [e1, e2] at h
  omega

private theorem sum_filter_lt_full {n : ℕ} (P : Fin n → Prop) [DecidablePred P]
    (g : Fin n → ℕ) :
    ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < n ∧ P x), g x =
      ∑ x ∈ Finset.univ.filter P, g x := by
  congr 1
  ext x
  simp

private theorem sum_sum_le_sq {n B : ℕ} {W : Fin n → Fin n → ℕ} (hB : ∀ u v, W u v ≤ B)
    (S T : Finset (Fin n)) : ∑ x ∈ S, ∑ y ∈ T, W x y ≤ n * n * B := by
  calc ∑ x ∈ S, ∑ y ∈ T, W x y ≤ ∑ x ∈ S, ∑ y ∈ T, B :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hB x y
    _ = S.card * (T.card * B) := by simp
    _ ≤ n * (n * B) := Nat.mul_le_mul (by simpa using S.card_le_univ)
          (Nat.mul_le_mul_right _ (by simpa using T.card_le_univ))
    _ = n * n * B := by ring

section Final

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ}

private theorem iterate_cutInner_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) (C : Finset (Fin n))
    (hC : ∀ x : Fin n, (t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n ↔ x ∉ C))
    (u : Fin n) (acc : ℕ) (hacc : acc + ∑ y ∈ Finset.univ \ C, W u y ≤ n * n * B) :
    ((Memory.spec 0).clientResult t
      (iterate cutInnerStep (⟨n, mb, sb, B⟩, u.1) n (0, acc))).2 =
      acc + ∑ y ∈ Finset.univ \ C, W u y := by
  have hinv := iterate_invariant_of cutInnerStep (⟨n, mb, sb, B⟩, u.1)
    (fun rem (va : ℕ × ℕ) t' => va.1 + rem = n ∧
      va.2 = acc + ∑ y ∈ Finset.univ.filter (fun y : Fin n => y.1 < va.1 ∧ y ∉ C), W u y ∧
      t' = t)
    (fun rem va t' ⟨hsum, hacc', ht'⟩ => by
      subst ht'
      have hv : va.1 < n := by omega
      set vFin : Fin n := ⟨va.1, hv⟩ with hvFin
      have hpart_le : ∑ y ∈ Finset.univ.filter (fun y : Fin n => y.1 < va.1 ∧ y ∉ C), W u y ≤
          ∑ y ∈ Finset.univ \ C, W u y := by
        refine Finset.sum_le_sum_of_subset fun y hy => ?_
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
        simp [hy.2]
      have hres : (Memory.spec 0).clientResult t' (cutInnerStep ((⟨n, mb, sb, B⟩, u.1), va)) =
          (va.1 + 1, if vFin ∉ C then va.2 + W u vFin else va.2) := by
        unfold cutInnerStep
        dsimp only
        rw [clientResult_bind_read, clientResult_bind_read]
        have hcap : t'.mem (capAddr ⟨n, mb, sb, B⟩ u.1 va.1) = W u vFin := hW u vFin
        rw [hcap]
        by_cases hvC : vFin ∈ C
        · have hd : t'.mem (distAddr ⟨n, mb, sb, B⟩ va.1) ≠ n := fun h => (hC vFin).mp h hvC
          rw [ite_eq_right (fun h => hd h.1), ite_eq_right (not_not.mpr hvC),
            clientResult_pure]
        · have hd := (hC vFin).mpr hvC
          rw [ite_eq_left ⟨hd, hB u vFin, by omega⟩, ite_eq_left hvC, clientResult_pure]
      refine ⟨?_, ?_, cutInnerStep_state _ t'⟩
      · rw [hres]; dsimp only; omega
      · rw [hres]
        dsimp only
        rw [sum_filter_lt_succ hv (fun y => y ∉ C), ← hvFin]
        split_ifs <;> omega)
    (n := n) (a := (0, acc)) (s := t) ⟨Nat.zero_add _, by simp, rfl⟩
  obtain ⟨hsum_end, hacc_end, -⟩ := hinv
  rw [hacc_end, show ((Memory.spec 0).clientResult t
    (iterate cutInnerStep (⟨n, mb, sb, B⟩, u.1) n (0, acc))).1 = n by omega,
    sum_filter_lt_full]
  congr 2
  ext y
  simp

private theorem iterate_cutOuter_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) (C : Finset (Fin n))
    (hC : ∀ x : Fin n, (t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n ↔ x ∉ C))
    (hC' : ∀ x : Fin n, (t.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < n ↔ x ∈ C)) :
    ((Memory.spec 0).clientResult t (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).2 =
      cutWeight W C := by
  have hinv := iterate_invariant_of cutOuterStep ⟨n, mb, sb, B⟩
    (fun rem (ua : ℕ × ℕ) t' => ua.1 + rem = n ∧
      ua.2 = ∑ x ∈ Finset.univ.filter (fun x : Fin n => x.1 < ua.1 ∧ x ∈ C),
        ∑ y ∈ Finset.univ \ C, W x y ∧ t' = t)
    (fun rem ua t' ⟨hsum, hacc', ht'⟩ => by
      subst ht'
      have hu : ua.1 < n := by omega
      set uFin : Fin n := ⟨ua.1, hu⟩ with huFin
      have hsplit := sum_filter_lt_succ hu (fun x => x ∈ C)
        (fun x => ∑ y ∈ Finset.univ \ C, W x y)
      have hres : (Memory.spec 0).clientResult t' (cutOuterStep (⟨n, mb, sb, B⟩, ua)) =
          (ua.1 + 1, if uFin ∈ C then ua.2 + ∑ y ∈ Finset.univ \ C, W uFin y else ua.2) := by
        unfold cutOuterStep
        dsimp only
        rw [clientResult_bind_read]
        by_cases huC : uFin ∈ C
        · rw [ite_eq_left ((hC' uFin).mpr huC), ite_eq_left huC, clientResult_bind,
            clientResult_pure]
          congr 1
          refine iterate_cutInner_spec hB hW C hC uFin ua.2 ?_
          rw [hacc']
          have := sum_sum_le_sq hB
            (Finset.univ.filter (fun x : Fin n => x.1 < ua.1 + 1 ∧ x ∈ C)) (Finset.univ \ C)
          rw [hsplit, ite_eq_left huC] at this
          exact this
        · rw [ite_eq_right (fun h => huC ((hC' uFin).mp h)), ite_eq_right huC,
            clientResult_pure]
      refine ⟨?_, ?_, cutOuterStep_state _ t'⟩
      · rw [hres]; dsimp only; omega
      · rw [hres]
        dsimp only
        rw [hsplit, ← huFin]
        split_ifs <;> omega)
    (n := n) (a := (0, 0)) (s := t) ⟨Nat.zero_add _, by simp, rfl⟩
  obtain ⟨hsum_end, hacc_end, -⟩ := hinv
  rw [hacc_end, show ((Memory.spec 0).clientResult t
    (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).1 = n by omega, sum_filter_lt_full,
    show Finset.univ.filter (· ∈ C) = C by ext; simp]
  rfl

end Final


private theorem roundStep_idle {d : (Ctx × (ℕ × ℕ)) × ℕ} (h : d.2 ≠ 0) (t : Memory.State) :
    (Memory.spec 0).clientResult t (roundStep d) = 1 ∧
      (Memory.spec 0).clientState t (roundStep d) = t := by
  rcases d with ⟨⟨c, ⟨s, t'⟩⟩, flag⟩
  dsimp only at h
  unfold roundStep
  dsimp only
  exact ⟨by rw [clientResult_bind_read, ite_eq_right h, clientResult_pure],
    by rw [clientState_bind_read, ite_eq_right h, clientState_pure]⟩


/-! ### The dense Edmonds–Karp solver (`ekProg`), its bounds, and specification -/

/-- **Dense Edmonds–Karp** (`d = (c, (s, t))`): clear the flow, run `n ^ 3` rounds (rounds after
`t` stops being reached do nothing), and return the weight of the reached set of the final
search. -/
def ekProg (d : Ctx × (ℕ × ℕ)) : Memory.Prog ℕ := do
  let c := d.1
  fillRange ((flowAddr c 0 0, 0), c.n * c.n)
  let _ ← iterate roundStep d (c.n * c.n * c.n) 0
  let r ← iterate cutOuterStep c c.n (0, 0)
  pure r.2

theorem ekProg_realizes :
    Realizes .exact ekProg (WordEncoding.encode (α := Ctx × (ℕ × ℕ)))
      (WordEncoding.encode (α := ℕ))
      (fun w d _ => let (c, s, t) := d; CtxFits w c ∧ s < c.n ∧ t < c.n) (fun _ _ => 0) := by
  unfold ekProg
  realize [fillRange_realizes, roundStep_realizes, cutOuterStep_realizes]
  all_goals
    obtain ⟨⟨hlay, hws, hwb⟩, hs, ht⟩ := h
    try
      dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
        predAddr] at *
      first
      | omega
      | (apply Fits.of_le hws; omega)
      | (apply Fits.of_le hwb; omega)
  · refine iterationSafe_of_stepInv _ _ w _ (fun _ _ _ => True) ?_ trivial
    intro _ _ _ _
    exact ⟨⟨⟨hlay, hws, hwb⟩, hs, ht⟩, trivial⟩
  · refine iterationSafe_of_stepInv _ _ w _
      (fun rem (ua : ℕ × ℕ) _ => ua.1 + rem = d.1.n) ?_ (Nat.zero_add _)
    intro rem ua t hsum
    dsimp only at *
    refine ⟨⟨⟨hlay, hws, hwb⟩, by omega⟩, ?_⟩
    rw [clientResult_cutOuterStep_fst]; omega

/-- Memory-operation budget of `ekProg` on `n` vertices, `O(n ^ 5)`. -/
abbrev ekCost (n : ℕ) : ℕ := 20 * (n + 1) ^ 5

theorem memoryCost_ekProg_le (c : Ctx) (s t : ℕ) (st : Memory.State) :
    memoryCost (ekProg (c, (s, t))) st ≤ ekCost c.n := by
  unfold ekProg
  dsimp only
  set n := c.n
  refine le_trans (memoryCost_bind_le (memoryCost_fillRange_le _ _ _ st) fun _ t1 =>
    memoryCost_bind_le (memoryCost_iterate_le_of roundStep (13 * (n + 1) ^ 2) (c, (s, t))
      (fun _ _ => memoryCost_roundStep_le _ _) (n * n * n) 0 t1) fun _ t2 =>
      memoryCost_bind_le (memoryCost_iterate_le_of cutOuterStep (1 + 2 * n) c
        (fun _ _ => memoryCost_cutOuterStep_le _ _) n (0, 0) t2) fun _ t3 =>
        (memoryCost_pure _ t3).le) ?_
  have h1 : 13 * (n + 1) ^ 2 * (n * n * n) ≤ 13 * (n + 1) ^ 5 := by
    have : n * n * n ≤ (n + 1) ^ 3 := by
      have := Nat.pow_le_pow_left (Nat.le_succ n) 3
      simpa [pow_succ, pow_zero, one_mul, mul_assoc] using this
    calc 13 * (n + 1) ^ 2 * (n * n * n) ≤ 13 * (n + 1) ^ 2 * (n + 1) ^ 3 :=
          Nat.mul_le_mul_left _ this
      _ = 13 * (n + 1) ^ 5 := by ring
  have h2 : (1 + 2 * n) * n + n * n ≤ 7 * (n + 1) ^ 5 := by
    have : (n + 1) ^ 2 ≤ (n + 1) ^ 5 := Nat.pow_le_pow_right (Nat.succ_pos n) (by decide)
    nlinarith
  dsimp only [ekCost]
  omega

theorem validHistory_ekProg {w : ℕ} {c : Ctx} {src snk : ℕ} {s : Memory.State}
    (hc : CtxFits w c) (hs : src < c.n) (ht : snk < c.n)
    (hwf : Memory.WellFormed w s) (hfr : c.scratchBase + ekScratch c.n ≤ s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (ekProg (c, (src, snk)))) := by
  have hr : EkReady w c s := ⟨hwf, hfr⟩
  unfold ekProg
  dsimp only
  have hfill := validHistory_fillRange (base := flowAddr c 0 0) (val := 0) (len := c.n * c.n) hwf
    (by ek_omega) (fits_zero w)
  refine validHistory_bind_step hfill ?_
  have hr1 : EkReady w c _ := MonotoneMemInv.pres hr hfill
  have hrounds := validHistory_iterate_inv (EkReady w c) roundStep (c, (src, snk))
    (fun a t' ht' => validHistory_roundStep (d := ((c, (src, snk)), a)) hc hs ht ht')
    (c.n * c.n * c.n) 0 hr1
  refine validHistory_bind_step hrounds ?_
  have hr2 : EkReady w c _ := MonotoneMemInv.pres hr1 hrounds
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := EkReady w c) c.n 0 0
      (fun u hu b t' ht' => ⟨validHistory_cutOuterStep (d := (c, (u, b))) hc.1
        (by dsimp only; omega) ht',
        ?_⟩) hr2) (validHistory_pure _ _ _)
  exact clientResult_cutOuterStep_fst _ _ _

theorem preservesAt_ekProg {a : ℕ} {c : Ctx} {src snk : ℕ} (hs : src < c.n)
    (ha : a < c.scratchBase ∨ c.scratchBase + ekScratch c.n ≤ a) :
    PreservesAt a (ekProg (c, (src, snk))) := by
  unfold ekProg
  dsimp only
  refine preservesAt_bind (fun s => (fillRange_spec _ _ _ s).2 _ (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_iterate
    (fun sv => preservesAt_roundStep (c := c) (src := src) (snk := snk) (sv := sv)
      hs ha) _ _) fun _ => ?_
  exact preservesAt_bind (fun t => congrArg (fun st : Memory.State => st.mem a)
    (clientState_iterate_eq_of _ _ (fun _ t' => cutOuterStep_state _ t') _ _ t))
    fun _ => preservesAt_pure _ _

theorem ekProg_result_le (c : Ctx) (s t : ℕ) (st : Memory.State) :
    (Memory.spec 0).clientResult st (ekProg (c, (s, t))) ≤
      c.n * c.n * c.capBound + c.capBound := by
  unfold ekProg
  rw [clientResult_bind, clientResult_bind,
    clientResult_bind, clientResult_pure]
  exact iterate_invariant_of cutOuterStep c
    (fun _ (ua : ℕ × ℕ) _ => ua.2 ≤ c.n * c.n * c.capBound + c.capBound)
    (fun _ ua t' hua => cutOuterStep_acc_le (c, ua) t' hua) (Nat.zero_le _)

/-- **Correctness of dense Edmonds–Karp on a flow network.** On a state holding the capacities
`N.cap ≤ B` at `mb`, `ekProg` leaves memory outside its scratch area unchanged, stores an integral
maximum flow `f` at `flowAddr`, marks `C = f.reachableCut` via `distAddr < n` as a minimum `s`–`t`
cut with `f.value = N.cutCapacity C`, and returns `N.cutCapacity C`. -/
private theorem ekProg_flow_spec {n mb sb B : ℕ} (N : Network (Fin n)) (hst : N.s ≠ N.t)
    (hB : ∀ u v, N.cap u v ≤ B) (hlay : mb + n * n ≤ sb) {st : Memory.State}
    (hW : ∀ u v : Fin n, st.mem (mb + u.1 * n + v.1) = N.cap u v) :
    let c : Ctx := ⟨n, mb, sb, B⟩
    let st' := (Memory.spec 0).clientState st (ekProg (c, (N.s.1, N.t.1)))
    let C : Finset (Fin n) := Finset.univ.filter fun x => st'.mem (distAddr c x.1) < n
    (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → st'.mem a = st.mem a) ∧
      ∃ f : N.Flow,
        (∀ u v : Fin n, st'.mem (flowAddr c u.1 v.1) = f u v) ∧
        (∀ x : Fin n, st'.mem (distAddr c x.1) ≤ n) ∧
        f.IsMaxFlow ∧ N.IsMinCut C ∧ C = f.reachableCut ∧
        f.value = (N.cutCapacity C : ℤ) ∧
        (Memory.spec 0).clientResult st (ekProg (c, (N.s.1, N.t.1))) = N.cutCapacity C := by
  dsimp only
  have hn : 0 < n := Nat.zero_lt_of_lt N.s.2
  have hframe : ∀ a, (a < sb ∨ sb + ekScratch n ≤ a) →
      ((Memory.spec 0).clientState st (ekProg (⟨n, mb, sb, B⟩, (N.s.1, N.t.1)))).mem a =
        st.mem a :=
    fun a ha => preservesAt_ekProg (c := ⟨n, mb, sb, B⟩) (src := N.s.1) (snk := N.t.1) N.s.2 ha st
  set s1 := (Memory.spec 0).clientState st (fillRange ((flowAddr ⟨n, mb, sb, B⟩ 0 0, 0), n * n))
  have hs1 := fillRange_spec (flowAddr ⟨n, mb, sb, B⟩ 0 0) 0 (n * n) st
  have hW1 : MatLoaded n mb N.cap s1 := fun u v => by
    rw [hs1.2 _ (Or.inl (by have := List.mul_add_lt_sq u.2 v.2; ek_omega))]
    exact hW u v
  have hf1 : FlowStored sb (Network.Flow.zero N) s1 := fun x y => by
    have h := hs1.1 (x.1 * n + y.1) (List.mul_add_lt_sq x.2 y.2)
    have he : flowAddr ⟨n, mb, sb, B⟩ 0 0 + (x.1 * n + y.1) = sb + x.1 * n + y.1 := by
      dsimp only [flowAddr]; ring
    rw [he] at h
    exact h
  have hloop := iterate_invariant_of roundStep (⟨n, mb, sb, B⟩, (N.s.1, N.t.1))
    (fun rem (sv : ℕ) tt => sv ≤ 1 ∧ MatLoaded n mb N.cap tt ∧
      ∃ (k : ℕ) (flows : ℕ → N.Flow) (paths : ℕ → List (Fin n)),
        N.IsShortestAugmentingSeq k flows paths ∧ FlowStored sb (flows k) tt ∧
        (sv = 0 → k + rem = n * n * n) ∧
        (sv = 1 → (∀ x : Fin n, tt.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = (flows k).resDist x) ∧
          (flows k).resDist N.t = n))
    (fun rem sv tt ⟨hsv, hWt, k, flows, paths, hseq, hft, h0, h1⟩ => by
      have hWt' : ∀ tt', (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → tt'.mem a = tt.mem a) →
          MatLoaded n mb N.cap tt' := fun tt' hfr u v => by
        rw [hfr _ (Or.inl (by have := List.mul_add_lt_sq u.2 v.2; omega))]
        exact hWt u v
      have hfr_round : ∀ a, (a < sb ∨ sb + ekScratch n ≤ a) →
          ((Memory.spec 0).clientState tt (roundStep ((⟨n, mb, sb, B⟩, (N.s.1, N.t.1)), sv))).mem a
            = tt.mem a :=
        fun a ha => preservesAt_roundStep (c := ⟨n, mb, sb, B⟩) (src := N.s.1)
          (snk := N.t.1) (sv := sv) N.s.2 ha tt
      by_cases hsv0 : sv = 0
      · subst hsv0
        have hk := h0 rfl
        rcases roundStep_spec (B := B) hst hB hlay hWt (flows k) hft with
          ⟨hr, hf', hd, hrt⟩ | ⟨hr, p, hp, hf'⟩
        · refine ⟨le_of_eq hr, hWt' _ hfr_round, k, flows, paths, hseq, hf',
            fun h => absurd (hr.symm.trans h) one_ne_zero, fun _ => ⟨hd, hrt⟩⟩
        · let flows' : ℕ → N.Flow := fun i =>
            if i ≤ k then flows i else (flows k).augmentByBottleneck p hp.isAugmentingPath
          let paths' : ℕ → List (Fin n) := fun i => if i = k then p else paths i
          have hseq' : N.IsShortestAugmentingSeq (k + 1) flows' paths' := by
            intro j hj
            by_cases hjk : j = k
            · subst hjk
              simp only [flows', paths', ite_eq_left (le_refl j),
                ite_eq_right (show ¬ j + 1 ≤ j by omega),
                ite_eq_left rfl]
              exact ⟨hp, trivial⟩
            · obtain ⟨hpj, hj'⟩ := hseq j (by omega)
              simp only [flows', paths', ite_eq_left (show j ≤ k by omega),
                ite_eq_left (show j + 1 ≤ k by omega), ite_eq_right hjk]
              exact ⟨hpj, hj'⟩
          have hf'' : FlowStored sb (flows' (k + 1))
              ((Memory.spec 0).clientState tt
                (roundStep ((⟨n, mb, sb, B⟩, (N.s.1, N.t.1)), 0))) := by
            simp only [flows', ite_eq_right (show ¬ k + 1 ≤ k by omega)]
            exact hf'
          refine ⟨by omega, hWt' _ hfr_round, k + 1, flows', paths', hseq', hf'',
            fun _ => by omega, fun h => absurd (hr.symm.trans h) zero_ne_one⟩
      · have hsv1 : sv = 1 := by omega
        obtain ⟨hr, hs⟩ := roundStep_idle (d := ((⟨n, mb, sb, B⟩, (N.s.1, N.t.1)), sv)) hsv0 tt
        rw [hr, hs]
        exact ⟨le_rfl, hWt, k, flows, paths, hseq, hft, fun h => absurd h one_ne_zero,
          fun _ => h1 hsv1⟩)
    (n := n * n * n) (a := 0) (s := s1)
    ⟨Nat.zero_le _, hW1, 0, fun _ => Network.Flow.zero N, fun _ => [],
      fun j hj => absurd hj (Nat.not_lt_zero _), hf1, fun _ => by omega,
      fun h => absurd h zero_ne_one⟩
  set s2 := (Memory.spec 0).clientState s1
    (iterate roundStep (⟨n, mb, sb, B⟩, (N.s.1, N.t.1)) (n * n * n) 0)
  obtain ⟨hsv, hW2, k, flows, paths, hseq, hf2, h0, h1⟩ := hloop
  have hsv1 : (Memory.spec 0).clientResult s1
      (iterate roundStep (⟨n, mb, sb, B⟩, (N.s.1, N.t.1)) (n * n * n) 0) = 1 := by
    by_contra hne
    have hk := h0 (by omega)
    have hb := N.shortestAugmentingSeq_length_le hst hseq
    have hsym := N.card_symArcs_le_card_sq
    rw [Fintype.card_fin] at hb hsym
    have h2 : N.symArcs.card * (n / 2) ≤ n * n * (n / 2) := Nat.mul_le_mul_right _ hsym
    have h3 : n * n * (n / 2) < n * n * n :=
      Nat.mul_lt_mul_of_pos_left (Nat.div_lt_self hn (by norm_num)) (Nat.mul_pos hn hn)
    omega
  obtain ⟨hdist, hres_t⟩ := h1 hsv1
  have hst_eq : (Memory.spec 0).clientState st (ekProg (⟨n, mb, sb, B⟩, (N.s.1, N.t.1))) = s2 := by
    unfold ekProg
    dsimp only
    rw [clientState_bind, clientState_bind,
      clientState_bind,
      clientState_iterate_eq_of _ _ (fun _ t' => cutOuterStep_state _ t'),
      clientState_pure]
  have hres_eq : (Memory.spec 0).clientResult st (ekProg (⟨n, mb, sb, B⟩, (N.s.1, N.t.1))) =
      ((Memory.spec 0).clientResult s2 (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).2 := by
    unfold ekProg
    dsimp only
    rw [clientResult_bind, clientResult_bind,
      clientResult_bind, clientResult_pure]
  rw [hst_eq, hres_eq]
  rw [hst_eq] at hframe
  refine ⟨hframe, flows k, ?_⟩
  set f := flows k
  set C : Finset (Fin n) := Finset.univ.filter fun x => s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < n
  have hle : ∀ x : Fin n, s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) ≤ n := fun x => by
    rw [hdist x]; simpa [Fintype.card_fin] using f.resDist_le_card x
  have hC' : ∀ x : Fin n, (s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) < n ↔ x ∈ C) := fun x => by
    simp [C]
  have hC : ∀ x : Fin n, (s2.mem (distAddr ⟨n, mb, sb, B⟩ x.1) = n ↔ x ∉ C) := fun x => by
    rw [← hC' x]
    have := hle x
    omega
  have hno : ¬ ∃ p, f.IsAugmentingPath p := by
    rw [f.exists_augmentingPath_iff_resReachable, ← f.resDist_lt_card_iff_resReachable,
      Fintype.card_fin]
    omega
  have hC_eq : C = f.reachableCut := by
    ext x
    rw [f.mem_reachableCut_iff, ← f.resDist_lt_card_iff_resReachable, Fintype.card_fin,
      ← hdist x, hC' x]
  have hval : f.value = (N.cutCapacity C : ℤ) := by
    rw [hC_eq]
    exact f.value_eq_cutCapacity_reachableCut hno
  have hmin : N.IsMinCut C := by
    rw [hC_eq]
    exact f.isMinCut_of_value_eq_cutCapacity (f.reachableCut_isCut hno)
      (f.value_eq_cutCapacity_reachableCut hno)
  have hmax : f.IsMaxFlow := (f.isMaxFlow_iff_not_exists_augmentingPath hst).mpr hno
  have hres : ((Memory.spec 0).clientResult s2 (iterate cutOuterStep ⟨n, mb, sb, B⟩ n (0, 0))).2 =
      N.cutCapacity C := iterate_cutOuter_spec hB hW2 C hC hC'
  exact ⟨fun u v => hf2 u v, hle, hmax, hmin, hC_eq, hval, hres⟩

/-- **Correctness of dense Edmonds–Karp.** On a state holding the capacities `W ≤ B` at `mb`,
`ekProg` leaves memory outside its scratch area unchanged, the set `C` of vertices whose final
distance is below `n` is a minimum `s`–`t` cut of `cutWeight W`, and the returned value is
`cutWeight W C`. -/
theorem ekProg_spec {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {s t : Fin n} (hst : s ≠ t)
    (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb) {st : Memory.State}
    (hW : ∀ u v : Fin n, st.mem (mb + u.1 * n + v.1) = W u v) :
    let c : Ctx := ⟨n, mb, sb, B⟩
    let st' := (Memory.spec 0).clientState st (ekProg (c, (s.1, t.1)))
    let C : Finset (Fin n) := Finset.univ.filter fun x => st'.mem (distAddr c x.1) < n
    (∀ a, (a < sb ∨ sb + ekScratch n ≤ a) → st'.mem a = st.mem a) ∧
      IsMinCutBetween (cutWeight W) s t C ∧
      (Memory.spec 0).clientResult st (ekProg (c, (s.1, t.1))) = cutWeight W C := by
  obtain ⟨hframe, _, _, _, _, hmin, _, _, hres⟩ :=
    ekProg_flow_spec (Network.mk W s t) hst hB hlay hW
  exact ⟨hframe, hmin.isMinCutBetween, hres⟩


end Cslib.Algorithms.WordRAM.EdmondsKarp
