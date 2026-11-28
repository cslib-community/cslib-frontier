/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxFlow.EdmondsKarp
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Internal
import CslibFrontier.Foundations.Data.List.RowMajor

/-!
# Residual-graph breadth-first search semantics for `ekProg`

Internal invariants (`MatLoaded`, `FlowStored`) and correctness specifications (`readResCap_spec`,
`bfsProg_spec`) for the layered breadth-first search subroutine of
`Cslib.Algorithms.WordRAM.EdmondsKarp`. Imported privately by
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec`.
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp

open Cslib.Algorithms.Lean.MaxFlow Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.Algorithms.WordRAM.EdmondsKarp.Internal
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write

/-- `omega` after unfolding the layout abbreviations and reducing projections. -/
local macro "ek_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
    predAddr] at *
  omega))

namespace Internal

/-! ### Semantics: residual capacities and the breadth-first search -/

section Semantics

variable {n mb sb B : ℕ} {W : Fin n → Fin n → ℕ} {src snk : Fin n}

/-- The state holds the capacities `W` at `mb`. -/
@[expose] def MatLoaded (n mb : ℕ) (W : Fin n → Fin n → ℕ) (t : Memory.State) : Prop :=
  ∀ u v : Fin n, t.mem (mb + u.val * n + v.val) = W u v

/-- The state holds the flow `f` at `sb`. -/
@[expose] def FlowStored {N : Network (Fin n)} (sb : ℕ) (f : N.Flow) (t : Memory.State) : Prop :=
  ∀ x y : Fin n, t.mem (sb + x.val * n + y.val) = f x y

theorem MatLoaded.congr {t t' : Memory.State} (hlay : mb + n * n ≤ sb)
    (hW : MatLoaded n mb W t) (h : ∀ a < sb + n * n, t'.mem a = t.mem a) :
    MatLoaded n mb W t' := fun u v => by
  rw [h _ (by have := List.mul_add_lt_sq u.isLt v.isLt; omega)]
  exact hW u v

theorem FlowStored.congr {N : Network (Fin n)} {f : N.Flow} {t t' : Memory.State}
    (hf : FlowStored sb f t) (h : ∀ a < sb + n * n, t'.mem a = t.mem a) :
    FlowStored sb f t' := fun x y => by
  rw [h _ (by have := List.mul_add_lt_sq x.isLt y.isLt; omega)]
  exact hf x y

theorem readResCap_spec (hB : ∀ u v, W u v ≤ B) {t : Memory.State}
    (hW : MatLoaded n mb W t) {f : (Network.mk W src snk).Flow} (hf : FlowStored sb f t)
    (u v : Fin n) :
    (Memory.spec 0).clientResult t (readResCap ((⟨n, mb, sb, B⟩, u.val), v.val)) =
      f.resCap u v := by
  unfold readResCap
  dsimp only [capAddr, flowAddr]
  rw [clientResult_bind_read, clientResult_bind_read, clientResult_bind_read, hW u v, hf u v,
    hf v u]
  have hc : W u v ≤ B ∧ f u v ≤ W u v ∧ f v u ≤ B :=
    ⟨hB u v, f.le_cap u v, (f.le_cap v u).trans (hB v u)⟩
  rw [ite_eq_left hc, clientResult_pure]
  rfl

/-- Invariant after the layers below `layer`: distances up to `layer` are exact, the others still
`n`, and every reached vertex other than the source has a parent one layer closer. -/
private def BfsLayerInv {N : Network (Fin n)} (mb sb B : ℕ) (f : N.Flow) (layer : ℕ)
    (t : Memory.State) : Prop :=
  (∀ x : Fin n,
    (f.resDist x ≤ layer → t.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = f.resDist x) ∧
    (layer < f.resDist x → t.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = n)) ∧
  (∀ x : Fin n,
    0 < t.mem (distAddr ⟨n, mb, sb, B⟩ x.val) → t.mem (distAddr ⟨n, mb, sb, B⟩ x.val) < n →
    ∃ u : Fin n,
      t.mem (predAddr ⟨n, mb, sb, B⟩ x.val) = u.val ∧
      f.resDist u + 1 = f.resDist x ∧
      0 < f.resCap u x)

private theorem bfsMid_spec (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb)
    {layer : ℕ} {s st : Memory.State} (hW : MatLoaded n mb W s)
    (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f s)
    (hlayer_lt : layer + 1 < n)
    (hst_low : ∀ a < sb + n * n, st.mem a = s.mem a)
    (hlinv : BfsLayerInv mb sb B f layer st) :
    let t_end :=
      (Memory.spec 0).clientState st (iterate bfsMidStep (⟨n, mb, sb, B⟩, layer) (n) 0)
    (Memory.spec 0).clientResult st (iterate bfsMidStep (⟨n, mb, sb, B⟩, layer) (n) 0) =
      n ∧
    (∀ a < sb + n * n, t_end.mem a = s.mem a) ∧
    BfsLayerInv mb sb B f (layer + 1) t_end := by
  let M := n
  have hmid := iterate_invariant_of bfsMidStep (⟨n, mb, sb, B⟩, layer)
    (fun urem (u : ℕ) t' =>
      u + urem = M ∧
      (∀ a < sb + n * n, t'.mem a = s.mem a) ∧
      (∀ x : Fin M, f.resDist x ≤ layer → t'.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = f.resDist x) ∧
      (∀ x : Fin M, layer + 1 < f.resDist x → t'.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        t'.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = layer + 1 ∨
          t'.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        (∃ u' : Fin M, u'.val < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
        t'.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = layer + 1) ∧
      (∀ x : Fin M, 0 < t'.mem (distAddr ⟨n, mb, sb, B⟩ x.val) →
        t'.mem (distAddr ⟨n, mb, sb, B⟩ x.val) < M →
        ∃ p : Fin M, t'.mem (predAddr ⟨n, mb, sb, B⟩ x.val) = p.val ∧
          f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
    (fun urem u t' ⟨husum, ht_low, hd_le, hd_gt, hd_eq, hd_found, hpar⟩ => by
      have hu_lt : u < M := by omega
      let uFin : Fin M := ⟨u, hu_lt⟩
      unfold bfsMidStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hdu : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = layer
      · rw [ite_eq_left hdu, clientResult_bind, clientState_bind, clientResult_pure,
          clientState_pure]
        have hres_u : f.resDist uFin = layer := by
          have h1 : f.resDist uFin ≤ layer → t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = f.resDist uFin :=
            hd_le uFin
          have h2 : layer + 1 < f.resDist uFin → t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = M :=
            hd_gt uFin
          have h3 : f.resDist uFin = layer + 1 → t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = layer + 1 ∨
              t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = M := hd_eq uFin
          omega
        have hinn := iterate_invariant_of bfsInnerStep ((⟨n, mb, sb, B⟩, layer), u)
          (fun vrem (v : ℕ) t'' =>
            v + vrem = M ∧
            (∀ a < sb + n * n, t''.mem a = s.mem a) ∧
            (∀ x : Fin M, f.resDist x ≤ layer →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = f.resDist x) ∧
            (∀ x : Fin M, layer + 1 < f.resDist x → t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = layer + 1 ∨
                t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              (∃ u' : Fin M, u'.val < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = layer + 1) ∧
            (∀ x : Fin M, x.val < v → 0 < f.resCap uFin x → f.resDist x = layer + 1 →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = layer + 1) ∧
            (∀ x : Fin M, 0 < t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) →
              t''.mem (distAddr ⟨n, mb, sb, B⟩ x.val) < M →
              ∃ p : Fin M, t''.mem (predAddr ⟨n, mb, sb, B⟩ x.val) = p.val ∧
                f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
          (fun vrem v t'' ⟨hvsum, hi_low, hi_le, hi_gt, hi_eq, hi_found, hi_cur, hi_par⟩ => by
            have hv_lt : v < M := by omega
            let vFin : Fin M := ⟨v, hv_lt⟩
            have hf'' : FlowStored sb f t'' := hf.congr hi_low
            have hW'' : MatLoaded n mb W t'' := hW.congr hlay hi_low
            unfold bfsInnerStep
            dsimp only
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind, clientState_bind]
            have hrc_r' : (Memory.spec 0).clientResult t''
                (readResCap ((⟨n, mb, sb, B⟩, u), v)) = f.resCap uFin vFin :=
              readResCap_spec hB hW'' hf'' uFin vFin
            have hrc_s' : (Memory.spec 0).clientState t''
                (readResCap ((⟨n, mb, sb, B⟩, u), v)) = t'' := readResCap_state _ t''
            rw [hrc_r', hrc_s']
            by_cases hcond : t''.mem (distAddr ⟨n, mb, sb, B⟩ v) = M ∧ 0 < f.resCap uFin vFin
            · rw [ite_eq_left hcond, clientResult_bind_write, clientState_bind_write,
                clientResult_bind_write,
                clientState_bind_write]
              simp only [client_simps]
              have hv_res : f.resDist vFin = layer + 1 := by
                have htri := f.resDist_le_add_one_of_pos_resCap hcond.2
                rw [hres_u] at htri
                have hnle : ¬ f.resDist vFin ≤ layer := fun hle => by
                  have h1 : t''.mem (distAddr ⟨n, mb, sb, B⟩ v) = f.resDist vFin := hi_le vFin hle
                  omega
                omega
              refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, fun x hx => ?_,
                fun x hx => ?_, fun x hx hex => ?_, fun x hx hpos hx1 => ?_,
                fun x hpos hlt => ?_⟩
              · rw [Function.update_of_ne (by ek_omega),
                  Function.update_of_ne (by ek_omega)]
                exact hi_low a ha
              · have hxv : x.val ≠ v := fun h => by obtain rfl : x = vFin := Fin.ext h; omega
                rw [Function.update_of_ne (by have := x.isLt; ek_omega),
                  Function.update_of_ne (by ek_omega)]
                exact hi_le x hx
              · have hxv : x.val ≠ v := fun h => by obtain rfl : x = vFin := Fin.ext h; omega
                rw [Function.update_of_ne (by have := x.isLt; ek_omega),
                  Function.update_of_ne (by ek_omega)]
                exact hi_gt x hx
              · rw [Function.update_of_ne (by have := x.isLt; ek_omega)]
                by_cases hxv : x.val = v
                · left; rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by ek_omega)]; exact hi_eq x hx
              · rw [Function.update_of_ne (by have := x.isLt; ek_omega)]
                by_cases hxv : x.val = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by ek_omega)]; exact hi_found x hx hex
              · rw [Function.update_of_ne (by have := x.isLt; ek_omega)]
                by_cases hxv : x.val = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by ek_omega)]
                  exact hi_cur x (by omega) hpos hx1
              · rw [Function.update_of_ne (by have := x.isLt; ek_omega)]
                  at hpos hlt
                by_cases hxv : x.val = v
                · obtain rfl : x = vFin := Fin.ext hxv
                  exact ⟨uFin, by dsimp only [vFin]; rw [Function.update_self],
                    by rw [hres_u, hv_res], hcond.2⟩
                · rw [Function.update_of_ne (by ek_omega)] at hpos hlt
                  obtain ⟨p, hp1, hp2, hp3⟩ := hi_par x hpos hlt
                  exact ⟨p, by
                    rw [Function.update_of_ne (by ek_omega),
                      Function.update_of_ne (by have := x.isLt; ek_omega)]
                    exact hp1, hp2, hp3⟩
            · rw [ite_eq_right hcond]
              simp only [client_simps]
              refine ⟨by omega, hi_low, hi_le, hi_gt, hi_eq, hi_found,
                fun x hx hpos hx1 => ?_, hi_par⟩
              by_cases hxv : x.val = v
              · obtain rfl : x = vFin := Fin.ext hxv
                exact (hi_eq _ hx1).resolve_right fun hM' => hcond ⟨hM', hpos⟩
              · exact hi_cur x (by omega) hpos hx1)
          (n := M) (a := 0) (s := t')
          ⟨Nat.zero_add _, ht_low, hd_le, hd_gt, hd_eq, hd_found,
            fun _ hx => absurd hx (Nat.not_lt_zero _), hpar⟩
        obtain ⟨hvsum_end, h1, h2, h3, h4, h5, h6, h7⟩ := hinn
        have hv_end : (Memory.spec 0).clientResult t'
            (iterate bfsInnerStep ((⟨n, mb, sb, B⟩, layer), u) M 0) = M := by omega
        rw [hv_end] at h6
        refine ⟨by omega, h1, h2, h3, h4, fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, h7⟩
        by_cases hu_eq : u'.val = u
        · obtain rfl : u' = uFin := Fin.ext hu_eq
          exact h6 x x.isLt hrc' hx
        · exact h5 x hx ⟨u', by omega, hru', hrc'⟩
      · rw [ite_eq_right hdu]
        simp only [client_simps]
        refine ⟨by omega, ht_low, hd_le, hd_gt, hd_eq,
          fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, hpar⟩
        by_cases hu_eq : u'.val = u
        · obtain rfl : u' = uFin := Fin.ext hu_eq
          have h1 : t'.mem (distAddr ⟨n, mb, sb, B⟩ u) = f.resDist uFin :=
            hd_le uFin (le_of_eq hru')
          omega
        · exact hd_found x hx ⟨u', by omega, hru', hrc'⟩)
    (n := M) (a := 0) (s := st)
    ⟨Nat.zero_add _, hst_low, fun x hx => (hlinv.1 x).1 hx,
      fun x hx => (hlinv.1 x).2 (by omega),
      fun x hx => Or.inr ((hlinv.1 x).2 (by omega)),
      fun _ _ ⟨_, hu, _⟩ => absurd hu (Nat.not_lt_zero _),
      hlinv.2⟩
  obtain ⟨husum_end, hm_low, hm_le, hm_gt, _, hm_found, hm_par⟩ := hmid
  have hu_end : (Memory.spec 0).clientResult st
      (iterate bfsMidStep (⟨n, mb, sb, B⟩, layer) M 0) = M := by omega
  rw [hu_end] at hm_found
  refine ⟨hu_end, hm_low, ⟨fun x => ⟨fun hx => ?_, fun hx => hm_gt x hx⟩, hm_par⟩⟩
  by_cases hx_eq : f.resDist x = layer + 1
  · have hcard : layer + 1 < Fintype.card (Fin M) := by rw [Fintype.card_fin]; exact hlayer_lt
    obtain ⟨u', hru', hrc'⟩ := f.exists_pred_of_resDist_eq_succ hcard hx_eq
    rw [hx_eq]
    exact hm_found x hx_eq ⟨u', u'.isLt, hru', hrc'⟩
  · exact hm_le x (by omega)

theorem bfsProg_spec (hB : ∀ u v, W u v ≤ B) (hlay : mb + n * n ≤ sb)
    {s : Memory.State} (hW : MatLoaded n mb W s)
    (f : (Network.mk W src snk).Flow) (hf : FlowStored sb f s) :
    let t := (Memory.spec 0).clientState s (bfsProg (⟨n, mb, sb, B⟩, src.val))
    (∀ a < sb + n * n, t.mem a = s.mem a) ∧
      (∀ x : Fin n, t.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = f.resDist x) ∧
      (∀ x : Fin n, 0 < f.resDist x → f.resDist x < n →
        ∃ u : Fin n,
          t.mem (predAddr ⟨n, mb, sb, B⟩ x.val) = u.val ∧
          f.resDist u + 1 = f.resDist x ∧
          0 < f.resCap u x) := by
  intro t
  have hpres : ∀ a < sb + n * n, t.mem a = s.mem a :=
    fun a ha =>
      preservesAt_bfsProg (d := (⟨n, mb, sb, B⟩, src.val)) src.isLt (Or.inl (by ek_omega)) s
  refine ⟨hpres, ?_⟩
  let M := n
  set s1 := (Memory.spec 0).clientState s (fillRange ((distAddr ⟨n, mb, sb, B⟩ 0, M), M))
  have hs1 := fillRange_spec (distAddr ⟨n, mb, sb, B⟩ 0) M M s
  set s2 : Memory.State :=
    ⟨Function.update (Function.update s1.mem (distAddr ⟨n, mb, sb, B⟩ src.val) 0)
      (predAddr ⟨n, mb, sb, B⟩ src.val) src.val, s1.frontier⟩
  have hsrc := src.isLt
  have hs2_low : ∀ a < sb + n * n, s2.mem a = s.mem a := by
    intro a ha
    have hne1 : a ≠ predAddr ⟨n, mb, sb, B⟩ src.val := by ek_omega
    have hne2 : a ≠ distAddr ⟨n, mb, sb, B⟩ src.val := by ek_omega
    dsimp only [s2]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    exact hs1.2 a (Or.inl (by ek_omega))
  have hfill : ∀ x : Fin n, s1.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = n := fun x =>
    hs1.1 x.val x.isLt
  have hinv0 : BfsLayerInv mb sb B f 0 s2 := by
    refine ⟨fun x => ⟨fun hle => ?_, fun hgt => ?_⟩, fun x hpos hlt => ?_⟩
    · have hx0 : f.resDist x = 0 := Nat.eq_zero_of_le_zero hle
      have hxs : x = src := f.eq_source_of_resDist_eq_zero hx0
      subst hxs
      dsimp only [s2]
      rw [Function.update_of_ne (by ek_omega), Function.update_self, hx0]
    · have hxs : x ≠ src := fun h => by
        rw [h] at hgt
        have := f.resDist_source
        simp only at this
        omega
      have hxne : x.val ≠ src.val := fun h => hxs (Fin.ext h)
      have hx := x.isLt
      dsimp only [s2]
      rw [Function.update_of_ne (by ek_omega), Function.update_of_ne (by ek_omega)]
      exact hfill x
    · have hx := x.isLt
      by_cases hx0 : x.val = src.val
      · dsimp only [s2] at hpos
        rw [hx0, Function.update_of_ne (by ek_omega), Function.update_self] at hpos
        omega
      · dsimp only [s2] at hlt
        rw [Function.update_of_ne (by ek_omega), Function.update_of_ne (by ek_omega),
          hfill x] at hlt
        omega
  have hlayers := iterate_invariant_of bfsLayerStep ⟨n, mb, sb, B⟩
    (fun rem (layer : ℕ) st =>
      layer + rem = M - 1 ∧ (∀ a < sb + n * n, st.mem a = s.mem a) ∧
        BfsLayerInv mb sb B f layer st)
    (fun rem layer st ⟨hsum, hst_low, hlinv⟩ => by
      have hlayer_lt : layer + 1 < M := by omega
      obtain ⟨_, hm_low, hm_inv⟩ := bfsMid_spec hB hlay hW f hf hlayer_lt hst_low hlinv
      unfold bfsLayerStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind,
        clientState_bind, clientResult_pure, clientState_pure]
      exact ⟨by omega, hm_low, hm_inv⟩)
    (n := M - 1) (a := 0) (s := s2) ⟨Nat.zero_add _, hs2_low, hinv0⟩
  obtain ⟨hsum_end, _, hinv_end⟩ := hlayers
  set s3 := (Memory.spec 0).clientState s2 (iterate bfsLayerStep ⟨n, mb, sb, B⟩ (M - 1) 0)
  have hlay_eq : ((Memory.spec 0).clientResult s2
      (iterate bfsLayerStep ⟨n, mb, sb, B⟩ (M - 1) 0)) = M - 1 := by omega
  rw [hlay_eq] at hinv_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (bfsProg (⟨n, mb, sb, B⟩, src.val)) = s3
    unfold bfsProg
    dsimp only
    rw [clientState_bind, clientState_bind_write, clientState_bind_write,
      clientState_bind, clientState_pure]
  rw [ht_eq]
  have hdist_all : ∀ x : Fin M, s3.mem (distAddr ⟨n, mb, sb, B⟩ x.val) = f.resDist x := by
    intro x
    have hle_card : f.resDist x ≤ M := by simpa [Fintype.card_fin] using f.resDist_le_card x
    by_cases hx : f.resDist x ≤ M - 1
    · exact (hinv_end.1 x).1 hx
    · have hxM : f.resDist x = M := by omega
      rw [(hinv_end.1 x).2 (by omega), hxM]
  refine ⟨hdist_all, fun x hpos hlt => ?_⟩
  rw [← hdist_all x] at hpos hlt
  exact hinv_end.2 x hpos hlt

end Semantics

end Internal

end Cslib.Algorithms.WordRAM.EdmondsKarp
