/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Core
public import CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Internal
import CslibFrontier.Foundations.Data.List.RowMajor
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Internal subroutine cost, admissibility, frame, and accumulator bounds

Memory-operation counts, `ValidHistory`, preservation frames, and cut-accumulator bounds for the
internal subroutines (`roundStep`, `cutOuterStep`, `augStep`) of
`Cslib.Algorithms.WordRAM.EdmondsKarp`. Imported privately by
`CslibFrontier.Algorithms.WordRAM.EdmondsKarp.Spec`.
-/

public section

namespace Cslib.Algorithms.WordRAM.EdmondsKarp.Internal

open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.Algorithms.WordRAM.EdmondsKarp
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write

/-- `omega` after unfolding the layout abbreviations and reducing projections. -/
local macro "ek_omega" : tactic => `(tactic| (
  dsimp -failIfUnchanged only [CtxFits, ekScratch, ekBound, capAddr, flowAddr, distAddr,
    predAddr, Prod.fst, Prod.snd] at *
  omega))

/-! ### Memory-operation counts -/

private theorem memoryCost_readResCap_le (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (readResCap d) s ≤ 3 := by
  unfold readResCap
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ _ =>
    memoryCost_bind_le (memoryCost_read _ _).le fun _ _ =>
      memoryCost_bind_le (memoryCost_read _ _).le fun _ t =>
        memoryCost_ite_le (memoryCost_pure _ t).le (memoryCost_pure _ t).le) (by decide)

private theorem memoryCost_bfsInnerStep_le (d : ((Ctx × ℕ) × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (bfsInnerStep d) s ≤ 6 := by
  unfold bfsInnerStep
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_bind_le (memoryCost_readResCap_le _ t1) fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (memoryCost_write _ _ t2).le fun _ t3 =>
        le_refl 1) (Nat.zero_le _)) (by decide)

/-- Number of `x < n` (as `Fin n`) with `lo ≤ x` satisfying `P`, split at `x = lo`. -/
private theorem card_filter_ge_split {n lo : ℕ} (hlo : lo < n) (P : Fin n → Prop)
    [DecidablePred P] :
    (Finset.univ.filter fun x : Fin n => lo ≤ x.1 ∧ P x).card =
      (Finset.univ.filter fun x : Fin n => lo + 1 ≤ x.1 ∧ P x).card +
        if P ⟨lo, hlo⟩ then 1 else 0 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun x : Fin n => lo ≤ x.1 ∧ P x) (fun x : Fin n => x.1 = lo)
  rw [Finset.filter_filter, Finset.filter_filter] at h
  have e1 : (Finset.univ.filter fun x : Fin n => (lo ≤ x.1 ∧ P x) ∧ ¬ x.1 = lo) =
      Finset.univ.filter fun x : Fin n => lo + 1 ≤ x.1 ∧ P x := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨⟨by omega, h2⟩, by omega⟩⟩
  have e2 : (Finset.univ.filter fun x : Fin n => (lo ≤ x.1 ∧ P x) ∧ x.1 = lo).card =
      if P ⟨lo, hlo⟩ then 1 else 0 := by
    split_ifs with hP
    · rw [Finset.card_eq_one]
      refine ⟨⟨lo, hlo⟩, ?_⟩
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨-, hx⟩; exact Fin.ext hx
      · rintro rfl; exact ⟨⟨le_rfl, hP⟩, rfl⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro x - ⟨⟨-, hPx⟩, hx⟩
      have hxe : x = ⟨lo, hlo⟩ := Fin.ext hx
      exact hP (hxe ▸ hPx)
  rw [e1, e2] at h
  omega

/-- Number of vertices at distance at least `lo` in `t`, split at distance exactly `lo`. -/
private theorem card_dist_ge_split (c : Ctx) (lo : ℕ) (t : Memory.State) :
    (Finset.univ.filter fun x : Fin c.n => lo ≤ t.mem (distAddr c x.1)).card =
      (Finset.univ.filter fun x : Fin c.n => lo + 1 ≤ t.mem (distAddr c x.1)).card +
        (Finset.univ.filter fun x : Fin c.n => t.mem (distAddr c x.1) = lo).card := by
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    omega
  · rw [Finset.disjoint_filter]
    intro x _ h1 h2
    omega

/-- One layer of the search costs at most `1 + n` plus `6 n` per vertex expanded, the vertices at
distance exactly `layer`. -/
private theorem memoryCost_bfsLayerStep_le (c : Ctx) (layer : ℕ) (hl : layer + 1 < c.n)
    (t : Memory.State) :
    memoryCost (bfsLayerStep (c, layer)) t ≤
      1 + c.n + 6 * c.n *
        (Finset.univ.filter fun x : Fin c.n => t.mem (distAddr c x.1) = layer).card := by
  unfold bfsLayerStep
  dsimp only
  rw [memoryCost_bind', memoryCost_read, clientState_read, memoryCost_bind',
    memoryCost_pure]
  have hmid := memoryCost_iterate_le_potential bfsMidStep (c, layer)
    (fun j (u : ℕ) t' => u + j = c.n ∧ DistRel c layer t t')
    (fun u t' => 6 * c.n *
      (Finset.univ.filter fun x : Fin c.n => u ≤ x.1 ∧ t'.mem (distAddr c x.1) = layer).card)
    1 ?_ c.n 0 t ⟨Nat.zero_add _, DistRel.refl c layer t⟩
  · have hcard : (Finset.univ.filter fun x : Fin c.n =>
        0 ≤ x.1 ∧ t.mem (distAddr c x.1) = layer) =
        Finset.univ.filter fun x : Fin c.n => t.mem (distAddr c x.1) = layer := by
      ext x; simp
    rw [hcard] at hmid
    omega
  intro j u t' ⟨hsum, hrel⟩
  have hu : u < c.n := by omega
  have hl' : layer + 1 ≠ c.n := by omega
  have hstep_rel := bfsMidStep_rel c layer u t'
  have hres : (Memory.spec 0).clientResult t' (bfsMidStep ((c, layer), u)) = u + 1 := by
    exact clientResult_bfsMidStep _ _
  rw [hres]
  refine ⟨⟨by omega, hrel.trans hstep_rel⟩, ?_⟩
  set t'' := (Memory.spec 0).clientState t' (bfsMidStep ((c, layer), u))
  have hsame : ∀ x : Fin c.n,
      t''.mem (distAddr c x.1) = layer ↔ t'.mem (distAddr c x.1) = layer := fun x => by
    rcases hstep_rel x.1 x.2 with h | ⟨h1, h2⟩
    · rw [h]
    · rw [h1, h2]; omega
  have hcnt : (Finset.univ.filter fun x : Fin c.n =>
      u + 1 ≤ x.1 ∧ t''.mem (distAddr c x.1) = layer) =
      Finset.univ.filter fun x : Fin c.n => u + 1 ≤ x.1 ∧ t'.mem (distAddr c x.1) = layer := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hsame x]
  have hcost : memoryCost (bfsMidStep ((c, layer), u)) t' ≤
      1 + if t'.mem (distAddr c u) = layer then 6 * c.n else 0 := by
    unfold bfsMidStep
    dsimp only
    rw [memoryCost_bind', memoryCost_read, clientState_read, clientResult_read]
    split_ifs with hdu
    · rw [memoryCost_bind', memoryCost_pure]
      have hin := memoryCost_iterate_le_of bfsInnerStep 6 ((c, layer), u)
        (fun v t3 => memoryCost_bfsInnerStep_le _ t3) c.n 0 t'
      omega
    · rw [memoryCost_pure]
  rw [hcnt, card_filter_ge_split hu (fun x : Fin c.n => t'.mem (distAddr c x.1) = layer)]
  change _ + _ ≤ 1 + 6 * c.n * (_ + if t'.mem (distAddr c u) = layer then 1 else 0)
  split_ifs at hcost ⊢ <;> rw [Nat.mul_add] <;> omega


private theorem memoryCost_bfsProg_le (d : Ctx × ℕ) (s : Memory.State) :
    memoryCost (bfsProg d) s ≤ 8 * (d.1.n + 1) ^ 2 := by
  obtain ⟨c, src⟩ := d
  dsimp only
  unfold bfsProg
  dsimp only
  rw [memoryCost_bind', memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write,
    memoryCost_bind', memoryCost_pure]
  have hfill := memoryCost_fillRange_le (distAddr c 0) c.n c.n s
  set t₀ := (Memory.spec 0).clientState _ (Memory.write (predAddr c src) src)
  have hlayers := memoryCost_iterate_le_potential bfsLayerStep c
    (fun j (layer : ℕ) _ => layer + j = c.n - 1)
    (fun layer t' => 6 * c.n *
      (Finset.univ.filter fun x : Fin c.n => layer ≤ t'.mem (distAddr c x.1)).card)
    (1 + c.n) ?_ (c.n - 1) 0 t₀ (Nat.zero_add _)
  · have hcard : (Finset.univ.filter fun x : Fin c.n => 0 ≤ t₀.mem (distAddr c x.1)).card ≤ c.n :=
      (Finset.card_le_univ _).trans (by simp)
    have h1 : 6 * c.n * (Finset.univ.filter fun x : Fin c.n =>
        0 ≤ t₀.mem (distAddr c x.1)).card ≤ 6 * c.n * c.n := Nat.mul_le_mul_left _ hcard
    have h2 : (1 + c.n) * (c.n - 1) ≤ (c.n + 1) * c.n := Nat.mul_le_mul (by omega) (Nat.sub_le _ _)
    have h3 : 8 * (c.n + 1) ^ 2 = 8 * (c.n * c.n) + 16 * c.n + 8 := by ring
    have h4 : (c.n + 1) * c.n = c.n * c.n + c.n := by ring
    have h5 : 6 * c.n * c.n = 6 * (c.n * c.n) := by ring
    omega
  intro j layer t' hsum
  have hl : layer + 1 < c.n := by omega
  have hres : (Memory.spec 0).clientResult t' (bfsLayerStep (c, layer)) = layer + 1 := by
    unfold bfsLayerStep; simp only [client_simps]
  rw [hres]
  refine ⟨by omega, ?_⟩
  have hcost := memoryCost_bfsLayerStep_le c layer hl t'
  have hrel : DistRel c layer t' ((Memory.spec 0).clientState t' (bfsLayerStep (c, layer))) := by
    unfold bfsLayerStep
    dsimp only
    rw [clientState_bind_read, clientState_bind,
      clientState_pure]
    exact bfsMid_iterate_rel c layer _ _ t'
  set t'' := (Memory.spec 0).clientState t' (bfsLayerStep (c, layer))
  have hsame : (Finset.univ.filter fun x : Fin c.n => layer + 1 ≤ t''.mem (distAddr c x.1)) =
      Finset.univ.filter fun x : Fin c.n => layer + 1 ≤ t'.mem (distAddr c x.1) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hrel x.1 x.2 with h | ⟨h1, h2⟩
    · rw [h]
    · rw [h1, h2]; omega
  rw [hsame, card_dist_ge_split c layer t', Nat.mul_add]
  omega

private theorem memoryCost_bnStep_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (bnStep d) s ≤ 5 := by
  unfold bnStep
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ _).le fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (memoryCost_readResCap_le _ t2) fun _ t3 =>
        memoryCost_ite_le (memoryCost_pure _ t3).le (memoryCost_pure _ t3).le)
        (Nat.zero_le _)) (Nat.zero_le _)) (by decide)

private theorem memoryCost_augStep_le (d : (Ctx × ℕ) × ℕ) (s : Memory.State) :
    memoryCost (augStep d) s ≤ 6 := by
  unfold augStep
  exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ _).le fun _ t2 =>
      memoryCost_ite_le (memoryCost_bind_le (memoryCost_read _ _).le fun _ t3 =>
        memoryCost_bind_le (memoryCost_read _ _).le fun _ t4 =>
          memoryCost_ite_le (memoryCost_bind_le (memoryCost_write _ _ t4).le fun _ t5 =>
            le_refl 1) (Nat.zero_le _))
        (Nat.zero_le _)) (Nat.zero_le _)) (by decide)

theorem memoryCost_roundStep_le (d : (Ctx × (ℕ × ℕ)) × ℕ) (s : Memory.State) :
    memoryCost (roundStep d) s ≤ 13 * (let ((c, _), _) := d; c.n + 1) ^ 2 := by
  rcases d with ⟨⟨c, ⟨src, snk⟩⟩, flag⟩
  unfold roundStep
  dsimp only
  have hbr : ∀ dt t, memoryCost
      (if 0 < dt ∧ dt < c.n then do
        let r ← iterate bnStep c dt (snk, 2 * c.capBound)
        let _ ← iterate augStep (c, r.2) dt snk
        pure 0
      else pure 1) t ≤ 11 * c.n := by
    intro dt t
    rw [memoryCost_ite]
    split_ifs with hdt
    · refine le_trans (memoryCost_bind_le
        (memoryCost_iterate_le_of bnStep 5 _ (fun _ _ => memoryCost_bnStep_le _ _) dt _ t)
        fun _ t2 => memoryCost_bind_le
          (memoryCost_iterate_le_of augStep 6 _ (fun _ _ => memoryCost_augStep_le _ _) dt _ t2)
          fun _ t3 => (memoryCost_pure _ t3).le) ?_
      omega
    · exact Nat.zero_le _
  refine le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le (memoryCost_bfsProg_le _ t1) fun _ t2 =>
      memoryCost_bind_le (memoryCost_read _ _).le fun dt t3 => hbr dt t3)
      (Nat.zero_le _)) ?_
  dsimp only
  have h : 13 * (c.n + 1) ^ 2 = 13 * (c.n * c.n) + 26 * c.n + 13 := by ring
  have h' : 8 * (c.n + 1) ^ 2 = 8 * (c.n * c.n) + 16 * c.n + 8 := by ring
  have hsq := Nat.le_mul_self c.n
  omega

theorem memoryCost_cutOuterStep_le (d : Ctx × (ℕ × ℕ)) (s : Memory.State) :
    memoryCost (cutOuterStep d) s ≤ 1 + 2 * d.1.n := by
  unfold cutOuterStep
  have hin : ∀ va t, memoryCost (cutInnerStep ((d.1, d.2.1), va)) t ≤ 2 := fun va t => by
    unfold cutInnerStep
    exact le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
      memoryCost_bind_le (memoryCost_read _ _).le fun _ t2 =>
        memoryCost_ite_le (memoryCost_pure _ t2).le (memoryCost_pure _ t2).le) (by decide)
  refine le_trans (memoryCost_bind_le (memoryCost_read _ _).le fun _ t1 =>
    memoryCost_ite_le (memoryCost_bind_le
      (memoryCost_iterate_le_of cutInnerStep 2 _ hin d.1.n _ t1) fun _ t2 =>
        (memoryCost_pure _ t2).le) (Nat.zero_le _)) ?_
  omega

/-! ### Admissibility (`ValidHistory`) -/

/-- The solver's memory invariant: well-formed memory and an allocated scratch area. -/
abbrev EkReady (w : ℕ) (c : Ctx) (t : Memory.State) : Prop :=
  Memory.WellFormed w t ∧ c.scratchBase + ekScratch c.n ≤ t.frontier

private theorem ekReady_write {w : ℕ} {c : Ctx} {t : Memory.State} (ht : EkReady w c t)
    (a v : ℕ) (hv : Fits w v) : EkReady w c ⟨Function.update t.mem a v, t.frontier⟩ := by
  refine ⟨⟨ht.1.frontier_fits, fun b => ?_⟩, ht.2⟩
  dsimp only
  by_cases hb : b = a
  · subst hb; simpa using hv
  · rw [Function.update_of_ne hb]; exact ht.1.mem_fits b

private theorem validHistory_readResCap {w : ℕ} {d : (Ctx × ℕ) × ℕ} {t : Memory.State}
    (ht : EkReady w d.1.1 t) (hlay : d.1.1.matBase + d.1.1.n * d.1.1.n ≤ d.1.1.scratchBase)
    (hu : d.1.2 < d.1.1.n) (hv : d.2 < d.1.1.n) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (readResCap d)) := by
  rcases d with ⟨⟨c, u⟩, v⟩
  dsimp only at ht hlay hu hv
  have h1 := List.mul_add_lt_sq hu hv
  have h2 := List.mul_add_lt_sq hv hu
  have hfr := ht.2
  unfold readResCap
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_read_bind (by ek_omega) ?_
  exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)

private theorem validHistory_bfsProg {w : ℕ} {d : Ctx × ℕ} {t : Memory.State}
    (hc : CtxFits w d.1) (hs : d.2 < d.1.n) (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (bfsProg d)) := by
  obtain ⟨c, src⟩ := d
  dsimp only at hc hs ht
  obtain ⟨hlay, hws, hwb⟩ := hc
  unfold bfsProg
  dsimp only
  have hfill := validHistory_fillRange (base := distAddr c 0) (val := c.n) (len := c.n) ht.1
    (by have := ht.2; ek_omega) (hws.of_le (by ek_omega))
  refine validHistory_bind_step hfill ?_
  have ht1 : EkReady w c _ := MonotoneMemInv.pres ht hfill
  refine validHistory_write_bind (by have := ht1.2; ek_omega) (fits_zero w) ?_
  have ht2 := ekReady_write ht1 (distAddr c src) 0 (fits_zero w)
  refine validHistory_write_bind (by have := ht2.2; ek_omega) (hws.of_le (by ek_omega)) ?_
  have ht3 := ekReady_write ht2 (predAddr c src) src (hws.of_le (by ek_omega))
  refine validHistory_bind_step
    (validHistory_iterate_nat (Inv := EkReady w c) (c.n - 1) 0
      (fun layer hlayer t' ht' => ⟨?_, ?_⟩) ht3) (validHistory_pure _ _ _)
  · unfold bfsLayerStep
    refine validHistory_read_bind (by have := ht'.2; ek_omega) ?_
    refine validHistory_bind_step
      (validHistory_iterate_nat (Inv := EkReady w c) c.n 0
        (fun u hu t'' ht'' => ⟨?_, ?_⟩) ht') (validHistory_pure _ _ _)
    · unfold bfsMidStep
      refine validHistory_read_bind (by have := ht''.2; ek_omega) ?_
      refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
      refine validHistory_bind_step
        (validHistory_iterate_nat (Inv := EkReady w c) c.n 0
          (fun v hv t3 ht3 => ⟨?_, ?_⟩) ht'') (validHistory_pure _ _ _)
      · unfold bfsInnerStep
        refine validHistory_read_bind (by have := ht3.2; ek_omega) ?_
        have hrc := validHistory_readResCap (d := ((c, u), v)) ht3 hlay (by ek_omega)
          (by ek_omega)
        refine validHistory_bind_step hrc ?_
        have ht4 : EkReady w c _ := MonotoneMemInv.pres ht3 hrc
        refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
        refine validHistory_write_bind (by have := ht4.2; ek_omega)
          (hws.of_le (by ek_omega)) ?_
        exact validHistory_write_bind (by have := ht4.2; ek_omega)
          (hws.of_le (by ek_omega)) (validHistory_pure _ _ _)
      · exact clientResult_bfsInnerStep _ _
    · exact clientResult_bfsMidStep _ _
  · unfold bfsLayerStep
    simp only [client_simps]

private theorem validHistory_bnStep {w : ℕ} {d : Ctx × (ℕ × ℕ)} {t : Memory.State}
    (hlay : d.1.matBase + d.1.n * d.1.n ≤ d.1.scratchBase) (hn : 0 < d.1.n) (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (bnStep d)) := by
  have hfr := ht.2
  unfold bnStep
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hcur => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hp => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_step
    (validHistory_readResCap (d := ((d.1, _), d.2.1)) ht hlay hp hcur) ?_
  exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)

private theorem validHistory_augStep {w : ℕ} {d : (Ctx × ℕ) × ℕ} {t : Memory.State}
    (hc : CtxFits w d.1.1) (hn : 0 < d.1.1.n) (ht : EkReady w d.1.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (augStep d)) := by
  rcases d with ⟨⟨c, δ⟩, cur⟩
  dsimp only at hc hn ht
  obtain ⟨hlay, hws, hwb⟩ := hc
  have hfr := ht.2
  unfold augStep
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hcur => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hp => ?_) (fun _ => validHistory_pure _ _ _)
  have h1 := List.mul_add_lt_sq hcur hp
  have h2 := List.mul_add_lt_sq hp hcur
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun hg => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_write_bind (by ek_omega) ((ht.1.mem_fits _).of_le (Nat.sub_le _ _)) ?_
  exact validHistory_write_bind (by ek_omega) (hwb.of_le (by split_ifs <;> ek_omega))
    (validHistory_pure _ _ _)

theorem validHistory_roundStep {w : ℕ} {d : (Ctx × (ℕ × ℕ)) × ℕ} {t : Memory.State}
    (hc : let ((c, _), _) := d; CtxFits w c)
    (hs : let ((c, (s, _)), _) := d; s < c.n)
    (hsnk : let ((c, (_, t')), _) := d; t' < c.n)
    (ht : EkReady w (let ((c, _), _) := d; c) t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (roundStep d)) := by
  obtain ⟨⟨c, src, snk⟩, st⟩ := d
  dsimp only at hc hs hsnk ht
  have hn : 0 < c.n := by omega
  unfold roundStep
  dsimp only
  refine validHistory_read_bind (by have := ht.2; ek_omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  have hb := validHistory_bfsProg (d := (c, src)) hc hs ht
  refine validHistory_bind_step hb ?_
  have ht1 : EkReady w c _ := MonotoneMemInv.pres ht hb
  refine validHistory_read_bind (by have := ht1.2; ek_omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  have hbn : ∀ m, (Memory.spec w).ValidHistory _ ((Memory.spec w).clientHistory _
      (iterate bnStep c m (snk, 2 * c.capBound))) := fun m =>
    validHistory_iterate_inv (EkReady w c) bnStep c
      (fun a t' ht' => validHistory_bnStep (d := (c, a)) hc.1 hn ht') m _ ht1
  refine validHistory_bind_step (hbn _) ?_
  exact validHistory_bind_step
    (validHistory_iterate_inv (EkReady w c) augStep _
      (fun a t' ht' => validHistory_augStep (d := ((c, _), a)) hc hn ht') _ snk
      (MonotoneMemInv.pres ht1 (hbn _)))
    (validHistory_pure _ _ _)

theorem validHistory_cutOuterStep {w : ℕ} {d : Ctx × (ℕ × ℕ)} {t : Memory.State}
    (hlay : d.1.matBase + d.1.n * d.1.n ≤ d.1.scratchBase)
    (hu : let (c, (u, _)) := d; u < c.n)
    (ht : EkReady w d.1 t) :
    (Memory.spec w).ValidHistory t ((Memory.spec w).clientHistory t (cutOuterStep d)) := by
  have hfr := ht.2
  unfold cutOuterStep
  refine validHistory_read_bind (by ek_omega) ?_
  refine validHistory_ite (fun _ => ?_) (fun _ => validHistory_pure _ _ _)
  refine validHistory_bind_step
    (validHistory_iterate_fst (Inv := EkReady w d.1) d.1.n 0 _
      (fun v hv b t' ht' => ⟨?_, ?_⟩) ht) (validHistory_pure _ _ _)
  · have h1 := List.mul_add_lt_sq hu (show v < d.1.n by omega)
    have hfr' := ht'.2
    unfold cutInnerStep
    refine validHistory_read_bind (by ek_omega) ?_
    refine validHistory_read_bind (by ek_omega) ?_
    exact validHistory_ite (fun _ => validHistory_pure _ _ _) (fun _ => validHistory_pure _ _ _)
  · exact clientResult_cutInnerStep_fst _ _ _

/-! ### Frame and result bound of internal subroutines -/

theorem preservesAt_augStep {a : ℕ} {c : Ctx} {δ cur : ℕ}
    (ha : a < flowAddr c 0 0 ∨ distAddr c 0 ≤ a) : PreservesAt a (augStep ((c, δ), cur)) := by
  unfold augStep
  dsimp only
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  split_ifs with hcur
  · refine preservesAt_bind (preservesAt_read _ _) fun p => ?_
    split_ifs with hp
    · have h1 := List.mul_add_lt_sq hcur hp
      have h2 := List.mul_add_lt_sq hp hcur
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
      refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
      refine preservesAt_bind (preservesAt_write _ (by ek_omega)) fun _ => ?_
      exact preservesAt_map _ (preservesAt_write _ (by ek_omega))
    · exact preservesAt_pure _ _
  · exact preservesAt_pure _ _

theorem preservesAt_roundStep {a : ℕ} {c : Ctx} {src snk sv : ℕ}
    (hs : src < c.n)
    (ha : a < c.scratchBase ∨ c.scratchBase + ekScratch c.n ≤ a) :
    PreservesAt a (roundStep ((c, (src, snk)), sv)) := by
  unfold roundStep
  dsimp only
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (preservesAt_bfsProg (d := (c, src)) hs (by ek_omega)) fun _ => ?_
  refine preservesAt_bind (preservesAt_read _ _) fun _ => ?_
  refine preservesAt_ite _ ?_ (preservesAt_pure _ _)
  refine preservesAt_bind (fun t => congrArg (fun st : Memory.State => st.mem a)
    (clientState_iterate_eq_of _ _ (fun _ t' => bnStep_state _ t') _ _ t)) fun _ => ?_
  exact preservesAt_bind
    (preservesAt_iterate (fun _ => preservesAt_augStep (c := c) (by ek_omega)) _ _)
    fun _ => preservesAt_pure _ _

private theorem cutInnerStep_acc_le (d : (Ctx × ℕ) × (ℕ × ℕ)) (t : Memory.State)
    (h : d.2.2 ≤ d.1.1.n * d.1.1.n * d.1.1.capBound + d.1.1.capBound) :
    ((Memory.spec 0).clientResult t (cutInnerStep d)).2 ≤
      d.1.1.n * d.1.1.n * d.1.1.capBound + d.1.1.capBound := by
  rcases d with ⟨⟨c, u⟩, ⟨v, acc⟩⟩
  dsimp only at h ⊢
  unfold cutInnerStep
  dsimp only
  rw [clientResult_bind_read, clientResult_bind_read]
  split_ifs with hg
  · rw [clientResult_pure]
    dsimp only
    omega
  · rw [clientResult_pure]
    exact h

theorem cutOuterStep_acc_le (d : Ctx × (ℕ × ℕ)) (t : Memory.State)
    (h : let (c, (_, acc)) := d; acc ≤ c.n * c.n * c.capBound + c.capBound) :
    ((Memory.spec 0).clientResult t (cutOuterStep d)).2 ≤
      d.1.n * d.1.n * d.1.capBound + d.1.capBound := by
  rcases d with ⟨c, ⟨u, acc⟩⟩
  dsimp only at h ⊢
  unfold cutOuterStep
  dsimp only
  rw [clientResult_bind_read]
  split_ifs
  · rw [clientResult_bind, clientResult_pure]
    exact iterate_invariant_of cutInnerStep (c, u)
      (fun _ (va : ℕ × ℕ) _ => va.2 ≤ c.n * c.n * c.capBound + c.capBound)
      (fun _ va t' hva => cutInnerStep_acc_le ((c, u), va) t' hva) h
  · rw [clientResult_pure]
    exact h

end Cslib.Algorithms.WordRAM.EdmondsKarp.Internal
