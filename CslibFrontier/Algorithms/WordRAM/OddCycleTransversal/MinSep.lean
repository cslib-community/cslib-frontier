/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.OddCycleTransversal.NetworkProg
import Mathlib.Tactic.Linarith

/-!
# Split-network semantics, BFS, and minimum-separator correctness

This module proves that `minSepProg` computes a minimum vertex cut in `splitNet` via layered BFS
and unit-capacity flow augmentation on the `(2n + 2)`-vertex split network. It depends only on
`NetworkProg` and builds in parallel with `CompressProg`, `Validity`, and `LeafSubroutines`.

## Main definitions

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.splitNet`: exact `FlowNetwork` modeled in memory.

## Main results

* `Cslib.Algorithms.WordRAM.OddCycleTransversal.minSepProg_spec`: correctness, cut-capacity bound,
  and memory-extraction specification of `minSepProg`.
-/

public section

namespace Cslib.Algorithms.WordRAM.OddCycleTransversal

open SimpleGraph
open Cslib.Algorithms.Lean.MaxFlow Cslib.Algorithms.Lean.IterativeCompression
open Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
open StateTransitionSpec (clientResult_bind clientState_bind clientResult_pure clientState_pure)

attribute [local client_simps] runClient_read runClient_write clientState_map

/-- Vertex-split `FlowNetwork` matching the in-memory `keepBase`/`flipBase`/`wBase` arrays. -/
@[expose] noncomputable def splitNet {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) : Network (Fin (splitCount n)) where
  s := ⟨0, by dsimp only [splitCount]; omega⟩
  t := ⟨1, by dsimp only [splitCount]; omega⟩
  cap x y :=
    if x.1 = 0 then
      if 2 ≤ y.1 ∧ y.1 < n + 2 then
        if s.mem (keepBase n + (y.1 - 2)) = 1 then n + 1 else 0
      else 0
    else if y.1 = 1 then
      if n + 2 ≤ x.1 ∧ x.1 < splitCount n then
        if s.mem (flipBase n + (x.1 - (n + 2))) = 1 then n + 1 else 0
      else 0
    else if 2 ≤ x.1 ∧ x.1 < n + 2 then
      if y.1 = x.1 + n then
        if s.mem (wBase n + (x.1 - 2)) = 0 then 1 else 0
      else 0
    else if h : n + 2 ≤ x.1 ∧ x.1 < splitCount n ∧ 2 ≤ y.1 ∧ y.1 < n + 2 then
      let u : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at h; omega⟩
      let v : Fin n := ⟨y.1 - 2, by omega⟩
      if (prefixGraph G m).Adj u v then n + 1 else 0
    else 0

private theorem splitNet_congr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (m : ℕ)
    {s₁ s₂ : Memory.State} (h : ∀ a < flowBase n, s₁.mem a = s₂.mem a) :
    splitNet G m s₁ = splitNet G m s₂ := by
  unfold splitNet
  congr 1
  funext x y
  dsimp only
  by_cases h1 : x.1 = 0
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases h2 : 2 ≤ y.1 ∧ y.1 < n + 2
    · rw [ite_eq_left h2, ite_eq_left h2,
        h (keepBase n + (y.1 - 2)) (by dsimp only [keepBase, flowBase]; omega)]
    · rw [ite_eq_right h2, ite_eq_right h2]
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : y.1 = 1
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : n + 2 ≤ x.1 ∧ x.1 < splitCount n
      · rw [ite_eq_left h3, ite_eq_left h3,
          h (flipBase n + (x.1 - (n + 2)))
            (by dsimp only [flipBase, flowBase, splitCount] at h3 ⊢; omega)]
      · rw [ite_eq_right h3, ite_eq_right h3]
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : 2 ≤ x.1 ∧ x.1 < n + 2
      · rw [ite_eq_left h3, ite_eq_left h3]
        by_cases h4 : y.1 = x.1 + n
        · rw [ite_eq_left h4, ite_eq_left h4,
            h (wBase n + (x.1 - 2)) (by dsimp only [wBase, flowBase]; omega)]
        · rw [ite_eq_right h4, ite_eq_right h4]
      · rw [ite_eq_right h3, ite_eq_right h3]

private theorem cap_splitNet_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) (x y : Fin (splitCount n)) :
    (splitNet G m s).cap x y ≤ n + 1 := by
  unfold splitNet
  dsimp only
  split_ifs <;> omega

private theorem clientResult_readSplitCap {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s : Memory.State} (hG : MatrixLoaded G s) (x y : Fin (splitCount n)) :
    (Memory.spec 0).clientResult s (readSplitCap (((n, m), x.1), y.1)) =
      (splitNet G m s).cap x y ∧
    (Memory.spec 0).clientState s (readSplitCap (((n, m), x.1), y.1)) = s := by
  refine ⟨?_, clientState_readSplitCap _ s⟩
  unfold readSplitCap splitNet
  dsimp only
  rw [clientResult_bind_read]
  by_cases h1 : x.1 = 0
  · rw [ite_eq_left h1, ite_eq_left h1]
    by_cases h2 : 2 ≤ y.1 ∧ y.1 < n + 2
    · rw [ite_eq_left h2, ite_eq_left h2, clientResult_bind_read]
      split_ifs <;> simp only [client_simps]
    · rw [ite_eq_right h2, ite_eq_right h2]; rfl
  · rw [ite_eq_right h1, ite_eq_right h1]
    by_cases h2 : y.1 = 1
    · rw [ite_eq_left h2, ite_eq_left h2]
      by_cases h3 : n + 2 ≤ x.1 ∧ x.1 < splitCount n
      · rw [ite_eq_left h3, ite_eq_left h3, clientResult_bind_read]
        split_ifs <;> simp only [client_simps]
      · rw [ite_eq_right h3, ite_eq_right h3]; rfl
    · rw [ite_eq_right h2, ite_eq_right h2]
      by_cases h3 : 2 ≤ x.1 ∧ x.1 < n + 2
      · rw [ite_eq_left h3, ite_eq_left h3]
        by_cases h4 : y.1 = x.1 + n
        · rw [ite_eq_left h4, ite_eq_left h4, clientResult_bind_read]
          split_ifs <;> simp only [client_simps]
        · rw [ite_eq_right h4, ite_eq_right h4]; rfl
      · rw [ite_eq_right h3, ite_eq_right h3]
        by_cases h4 : n + 2 ≤ x.1 ∧ x.1 < splitCount n ∧ 2 ≤ y.1 ∧ y.1 < n + 2
        · rw [ite_eq_left h4, dite_eq_left h4]
          let u : Fin n := ⟨x.1 - (n + 2), by dsimp only [splitCount] at h4; omega⟩
          let v : Fin n := ⟨y.1 - 2, by omega⟩
          have hmem := hG u v
          dsimp only [u, v] at hmem
          by_cases hm : x.1 - (n + 2) < m ∧ y.1 - 2 < m
          · rw [ite_eq_left hm, clientResult_bind_read, hmem]
            by_cases hadj : G.Adj u v
            · have hp : (prefixGraph G m).Adj u v := ⟨hadj, hm.1, hm.2⟩
              change (Memory.spec 0).clientResult s
                (if (if G.Adj u v then 1 else 0) = 1 then pure (n + 1) else pure 0) =
                if (prefixGraph G m).Adj u v then n + 1 else 0
              simp only [hadj, hp, ↓reduceIte, client_simps]
            · have hp : ¬ (prefixGraph G m).Adj u v := fun h => hadj h.1
              change (Memory.spec 0).clientResult s
                (if (if G.Adj u v then 1 else 0) = 1 then pure (n + 1) else pure 0) =
                if (prefixGraph G m).Adj u v then n + 1 else 0
              simp only [hadj, hp, ↓reduceIte, Nat.zero_ne_one, client_simps]
          · rw [ite_eq_right hm]
            have hp : ¬ (prefixGraph G m).Adj u v := fun h => hm ⟨h.2.1, h.2.2⟩
            change (Memory.spec 0).clientResult s (pure 0) =
              if (prefixGraph G m).Adj u v then n + 1 else 0
            simp only [hp, ↓reduceIte, client_simps]
        · rw [ite_eq_right h4, dite_eq_right h4]; rfl

private def FlowStored {n : ℕ} {N : Network (Fin (splitCount n))}
    (f : N.Flow) (s : Memory.State) : Prop :=
  ∀ x y : Fin (splitCount n), s.mem (flowBase n + x.1 * splitCount n + y.1) = f x y

private theorem clientResult_readResCap {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s₀ s : Memory.State} (hG : MatrixLoaded G s₀)
    (hlow : ∀ a < flowBase n, s.mem a = s₀.mem a)
    {f : (splitNet G m s₀).Flow} (hf : FlowStored f s) (x y : Fin (splitCount n)) :
    (Memory.spec 0).clientResult s (readResCap (((n, m), x.1), y.1)) = f.resCap x y ∧
      (Memory.spec 0).clientState s (readResCap (((n, m), x.1), y.1)) = s := by
  have hG' : MatrixLoaded G s := fun u v => by
    rw [hlow _ (by dsimp only [flowBase]; nlinarith [u.2, v.2]), hG u v]
  obtain ⟨hcap_r, hcap_s⟩ := clientResult_readSplitCap (m := m) hG' x y
  rw [splitNet_congr G m hlow] at hcap_r
  unfold readResCap
  rw [StateTransitionSpec.clientResult_bind, StateTransitionSpec.clientState_bind, hcap_r, hcap_s]
  dsimp only
  rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
    clientState_bind_read, hf x y, hf y x]
  have hc1 := cap_splitNet_le G m s₀ x y
  have hc2 := cap_splitNet_le G m s₀ y x
  have hle1 := f.le_cap x y
  have hle2 := f.le_cap y x
  have hcond : (splitNet G m s₀).cap x y ≤ n + 1 ∧ f x y ≤ (splitNet G m s₀).cap x y ∧
      f y x ≤ n + 1 := ⟨hc1, hle1, hle2.trans hc2⟩
  rw [ite_eq_left hcond, clientResult_pure, clientState_pure]
  exact ⟨rfl, rfl⟩

private def BfsLayerInv {n : ℕ} {N : Network (Fin (splitCount n))}
    (f : N.Flow) (layer : ℕ) (t : Memory.State) : Prop :=
  (∀ x : Fin (splitCount n),
    (f.resDist x ≤ layer → t.mem (distBase n + x.1) = f.resDist x) ∧
    (layer < f.resDist x → t.mem (distBase n + x.1) = splitCount n)) ∧
  (∀ x : Fin (splitCount n),
    0 < t.mem (distBase n + x.1) → t.mem (distBase n + x.1) < splitCount n →
    ∃ u : Fin (splitCount n),
      t.mem (parBase n + x.1) = u.1 ∧
      f.resDist u + 1 = f.resDist x ∧
      0 < f.resCap u x)

private theorem bfsMid_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m layer : ℕ} {s₀ s st : Memory.State} (hG : MatrixLoaded G s₀)
    (hlow : ∀ a < flowBase n, s.mem a = s₀.mem a)
    (f : (splitNet G m s₀).Flow) (hf : FlowStored f s)
    (hlayer_lt : layer + 1 < splitCount n)
    (hst_low : ∀ a < distBase n, st.mem a = s.mem a)
    (hlinv : BfsLayerInv f layer st) :
    let t_end :=
      (Memory.spec 0).clientState st (iterate bfsMidStep ((n, m), layer) (splitCount n) 0)
    (Memory.spec 0).clientResult st (iterate bfsMidStep ((n, m), layer) (splitCount n) 0) =
      splitCount n ∧
    (∀ a < distBase n, t_end.mem a = s.mem a) ∧
    BfsLayerInv f (layer + 1) t_end := by
  let M := splitCount n
  have hmid := iterate_invariant_of bfsMidStep ((n, m), layer)
    (fun urem (u : ℕ) t' =>
      u + urem = M ∧
      (∀ a < distBase n, t'.mem a = s.mem a) ∧
      (∀ x : Fin M, f.resDist x ≤ layer → t'.mem (distBase n + x.1) = f.resDist x) ∧
      (∀ x : Fin M, layer + 1 < f.resDist x → t'.mem (distBase n + x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        t'.mem (distBase n + x.1) = layer + 1 ∨ t'.mem (distBase n + x.1) = M) ∧
      (∀ x : Fin M, f.resDist x = layer + 1 →
        (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
        t'.mem (distBase n + x.1) = layer + 1) ∧
      (∀ x : Fin M, 0 < t'.mem (distBase n + x.1) → t'.mem (distBase n + x.1) < M →
        ∃ p : Fin M, t'.mem (parBase n + x.1) = p.1 ∧
          f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
    (fun urem u t' ⟨husum, ht_low, hd_le, hd_gt, hd_eq, hd_found, hpar⟩ => by
      have hu_lt : u < M := by omega
      let uFin : Fin M := ⟨u, hu_lt⟩
      unfold bfsMidStep
      dsimp only [SplitNetArgs.n, SplitNetArgs.m, SplitNetArgs.arg1]
      rw [clientResult_bind_read, clientState_bind_read]
      by_cases hdu : t'.mem (distBase n + u) = layer
      · rw [ite_eq_left hdu, clientResult_bind, clientResult_pure,
          clientState_bind, clientState_pure]
        have hres_u : f.resDist uFin = layer := by
          by_contra hne
          rcases lt_trichotomy (f.resDist uFin) layer with hlt | heq | hgt
          · have h1 : t'.mem (distBase n + u) = f.resDist uFin := hd_le uFin (le_of_lt hlt)
            omega
          · exact hne heq
          · by_cases h1 : f.resDist uFin = layer + 1
            · rcases hd_eq uFin h1 with h | h
              · have h' : t'.mem (distBase n + u) = layer + 1 := h; omega
              · have h' : t'.mem (distBase n + u) = M := h; omega
            · have h2 : t'.mem (distBase n + u) = M := hd_gt uFin (by omega)
              omega
        have hinn := iterate_invariant_of bfsInnerStep (((n, m), layer), u)
          (fun vrem (v : ℕ) t'' =>
            v + vrem = M ∧
            (∀ a < distBase n, t''.mem a = s.mem a) ∧
            (∀ x : Fin M, f.resDist x ≤ layer → t''.mem (distBase n + x.1) = f.resDist x) ∧
            (∀ x : Fin M, layer + 1 < f.resDist x → t''.mem (distBase n + x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              t''.mem (distBase n + x.1) = layer + 1 ∨ t''.mem (distBase n + x.1) = M) ∧
            (∀ x : Fin M, f.resDist x = layer + 1 →
              (∃ u' : Fin M, u'.1 < u ∧ f.resDist u' = layer ∧ 0 < f.resCap u' x) →
              t''.mem (distBase n + x.1) = layer + 1) ∧
            (∀ x : Fin M, x.1 < v → 0 < f.resCap uFin x → f.resDist x = layer + 1 →
              t''.mem (distBase n + x.1) = layer + 1) ∧
            (∀ x : Fin M, 0 < t''.mem (distBase n + x.1) → t''.mem (distBase n + x.1) < M →
              ∃ p : Fin M, t''.mem (parBase n + x.1) = p.1 ∧
                f.resDist p + 1 = f.resDist x ∧ 0 < f.resCap p x))
          (fun vrem v t'' ⟨hvsum, hi_low, hi_le, hi_gt, hi_eq, hi_found, hi_cur, hi_par⟩ => by
            have hv_lt : v < M := by omega
            let vFin : Fin M := ⟨v, hv_lt⟩
            have hf'' : FlowStored f t'' := fun x y => by
              rw [hi_low _ (by dsimp only [distBase]; nlinarith [x.2, y.2]), hf x y]
            have hlow'' : ∀ a < flowBase n, t''.mem a = s₀.mem a := fun a ha => by
              rw [hi_low _ (by dsimp only [distBase]; omega), hlow a ha]
            obtain ⟨hrc_r, hrc_s⟩ := clientResult_readResCap hG hlow'' hf'' uFin vFin
            unfold bfsInnerStep
            dsimp only [BfsInnerArgs.n, BfsInnerArgs.m, BfsInnerArgs.layer, BfsInnerArgs.u]
            rw [clientResult_bind_read, clientState_bind_read, clientResult_bind, clientState_bind]
            have hrc_r' : (Memory.spec 0).clientResult t'' (readResCap (((n, m), u), v)) =
                f.resCap uFin vFin := hrc_r
            have hrc_s' : (Memory.spec 0).clientState t'' (readResCap (((n, m), u), v)) =
                t'' := hrc_s
            rw [hrc_r', hrc_s']
            by_cases hcond : t''.mem (distBase n + v) = M ∧ 0 < f.resCap uFin vFin
            · rw [ite_eq_left hcond, clientResult_bind_write, clientState_bind_write,
              clientResult_bind_write,
                clientState_bind_write]
              simp only [client_simps]
              have hv_res : f.resDist vFin = layer + 1 := by
                have htri := f.resDist_le_add_one_of_pos_resCap hcond.2
                rw [hres_u] at htri
                have hnle : ¬ f.resDist vFin ≤ layer := fun hle => by
                  have h1 : t''.mem (distBase n + v) = f.resDist vFin := hi_le vFin hle
                  omega
                omega
              refine ⟨by omega, fun a ha => ?_, fun x hx => ?_, fun x hx => ?_,
                fun x hx => ?_, fun x hx hex => ?_, fun x hx hpos hx1 => ?_,
                fun x hpos hlt => ?_⟩
              · rw [Function.update_of_ne (by dsimp only [parBase]; omega),
                  Function.update_of_ne (by omega)]
                exact hi_low a ha
              · have hxv : x.1 ≠ v := fun h => by
                  have : x = vFin := Fin.ext h; subst this; omega
                rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
                  Function.update_of_ne (by omega)]
                exact hi_le x hx
              · have hxv : x.1 ≠ v := fun h => by
                  have : x = vFin := Fin.ext h; subst this; omega
                rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
                  Function.update_of_ne (by omega)]
                exact hi_gt x hx
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                by_cases hxv : x.1 = v
                · left; rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by omega)]; exact hi_eq x hx
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                by_cases hxv : x.1 = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by omega)]; exact hi_found x hx hex
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                by_cases hxv : x.1 = v
                · rw [hxv, Function.update_self]
                · rw [Function.update_of_ne (by omega)]
                  exact hi_cur x (by omega) hpos hx1
              · rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                  at hpos hlt
                by_cases hxv : x.1 = v
                · have hxeq : x = vFin := Fin.ext hxv
                  subst hxeq
                  exact ⟨uFin, by dsimp only [vFin]; rw [Function.update_self],
                    by rw [hres_u, hv_res], hcond.2⟩
                · rw [Function.update_of_ne (by omega)] at hpos hlt
                  obtain ⟨p, hp1, hp2, hp3⟩ := hi_par x hpos hlt
                  exact ⟨p, by
                    rw [Function.update_of_ne (by omega),
                      Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega)]
                    exact hp1, hp2, hp3⟩
            · rw [ite_eq_right hcond]
              simp only [client_simps]
              refine ⟨by omega, hi_low, hi_le, hi_gt, hi_eq, hi_found,
                fun x hx hpos hx1 => ?_, hi_par⟩
              by_cases hxv : x.1 = v
              · have hxeq : x = vFin := Fin.ext hxv
                subst hxeq
                rcases hi_eq vFin hx1 with h1 | hM'
                · exact h1
                · exact absurd ⟨hM', hpos⟩ hcond
              · exact hi_cur x (by omega) hpos hx1)
          (n := M) (a := 0) (s := t')
          ⟨Nat.zero_add _, ht_low, hd_le, hd_gt, hd_eq, hd_found,
            fun _ hx => absurd hx (Nat.not_lt_zero _), hpar⟩
        obtain ⟨hvsum_end, h1, h2, h3, h4, h5, h6, h7⟩ := hinn
        have hv_end : (Memory.spec 0).clientResult t'
            (iterate bfsInnerStep (((n, m), layer), u) M 0) = M := by omega
        rw [hv_end] at h6
        refine ⟨by omega, h1, h2, h3, h4, fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, h7⟩
        by_cases hu_eq : u'.1 = u
        · have : u' = uFin := Fin.ext hu_eq
          subst this
          exact h6 x x.2 hrc' hx
        · exact h5 x hx ⟨u', by omega, hru', hrc'⟩
      · rw [ite_eq_right hdu]
        simp only [client_simps]
        refine ⟨by omega, ht_low, hd_le, hd_gt, hd_eq,
          fun x hx ⟨u', hu', hru', hrc'⟩ => ?_, hpar⟩
        by_cases hu_eq : u'.1 = u
        · have : u' = uFin := Fin.ext hu_eq
          subst this
          have h1 : t'.mem (distBase n + u) = f.resDist uFin := hd_le uFin (le_of_eq hru')
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
      (iterate bfsMidStep ((n, m), layer) M 0) = M := by omega
  rw [hu_end] at hm_found
  refine ⟨hu_end, hm_low, ⟨fun x => ⟨fun hx => ?_, fun hx => hm_gt x hx⟩, hm_par⟩⟩
  by_cases hx_eq : f.resDist x = layer + 1
  · have hcard : layer + 1 < Fintype.card (Fin M) := by rw [Fintype.card_fin]; exact hlayer_lt
    obtain ⟨u', hru', hrc'⟩ := f.exists_pred_of_resDist_eq_succ hcard hx_eq
    rw [hx_eq]
    exact hm_found x hx_eq ⟨u', u'.2, hru', hrc'⟩
  · exact hm_le x (by omega)

private theorem bfsProg_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s₀ s : Memory.State} (hG : MatrixLoaded G s₀)
    (hlow : ∀ a < flowBase n, s.mem a = s₀.mem a)
    (f : (splitNet G m s₀).Flow) (hf : FlowStored f s) :
    let t := (Memory.spec 0).clientState s (bfsProg (n, m))
    (∀ a < distBase n, t.mem a = s.mem a) ∧
      (∀ x : Fin (splitCount n), t.mem (distBase n + x.1) = f.resDist x) ∧
      (∀ x : Fin (splitCount n), 0 < f.resDist x → f.resDist x < splitCount n →
        ∃ u : Fin (splitCount n),
          t.mem (parBase n + x.1) = u.1 ∧
          f.resDist u + 1 = f.resDist x ∧
          0 < f.resCap u x) := by
  intro t
  have hpres : ∀ a < distBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_bfsProg (Or.inl ha) s
  refine ⟨hpres, ?_⟩
  let M := splitCount n
  let N := splitNet G m s₀
  set s1 := (Memory.spec 0).clientState s (fillRange ((distBase n, M), M))
  have hs1 := fillRange_spec (distBase n) M M s
  set s2 : Memory.State :=
    ⟨Function.update (Function.update s1.mem (distBase n) 0) (parBase n) 0, s1.frontier⟩
  have hs2_low : ∀ a < distBase n, s2.mem a = s.mem a := by
    intro a ha
    have hne1 : a ≠ parBase n := by dsimp only [parBase, splitCount]; omega
    have hne2 : a ≠ distBase n := by omega
    dsimp only [s2]
    rw [Function.update_of_ne hne1, Function.update_of_ne hne2]
    exact hs1.2 a (Or.inl ha)
  have hinv0 : BfsLayerInv f 0 s2 := by
    refine ⟨fun x => ⟨fun hle => ?_, fun hgt => ?_⟩, fun x hpos hlt => ?_⟩
    · have hx0 : f.resDist x = 0 := Nat.eq_zero_of_le_zero hle
      have hxs : x = N.s := f.eq_source_of_resDist_eq_zero hx0
      have hxval : x.1 = 0 := by rw [hxs]; rfl
      dsimp only [s2]
      rw [hxval, add_zero, Function.update_of_ne
        (by dsimp only [parBase, splitCount]; omega), Function.update_self, hx0]
    · have hxs : x ≠ N.s := fun h => by rw [h, f.resDist_source] at hgt; omega
      have hxne : x.1 ≠ 0 := fun h => hxs (Fin.ext h)
      dsimp only [s2]
      rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
        Function.update_of_ne (by omega)]
      exact hs1.1 x.1 x.2
    · by_cases hx0 : x.1 = 0
      · dsimp only [s2] at hpos
        rw [hx0, add_zero, Function.update_of_ne
          (by dsimp only [parBase, splitCount]; omega), Function.update_self] at hpos
        omega
      · dsimp only [s2] at hlt
        rw [Function.update_of_ne (by dsimp only [parBase]; have := x.2; omega),
          Function.update_of_ne (by omega), hs1.1 x.1 x.2] at hlt
        omega
  have hlayers := iterate_invariant_of bfsLayerStep (n, m)
    (fun rem (layer : ℕ) st =>
      layer + rem = M - 1 ∧ (∀ a < distBase n, st.mem a = s.mem a) ∧ BfsLayerInv f layer st)
    (fun rem layer st ⟨hsum, hst_low, hlinv⟩ => by
      have hlayer_lt : layer + 1 < M := by dsimp only [M, splitCount] at hsum ⊢; omega
      obtain ⟨_, hm_low, hm_inv⟩ := bfsMid_spec hG hlow f hf hlayer_lt hst_low hlinv
      unfold bfsLayerStep
      dsimp only
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind, clientResult_pure,
        clientState_bind, clientState_pure]
      exact ⟨by omega, hm_low, hm_inv⟩)
    (n := M - 1) (a := 0) (s := s2) ⟨Nat.zero_add _, hs2_low, hinv0⟩
  obtain ⟨hsum_end, _, hinv_end⟩ := hlayers
  set s3 := (Memory.spec 0).clientState s2 (iterate bfsLayerStep (n, m) (M - 1) 0)
  have hlay_eq : ((Memory.spec 0).clientResult s2 (iterate bfsLayerStep (n, m) (M - 1) 0)) =
      M - 1 := by omega
  rw [hlay_eq] at hinv_end
  have ht_eq : t = s3 := by
    change (Memory.spec 0).clientState s (bfsProg (n, m)) = s3
    unfold bfsProg
    dsimp only
    rw [StateTransitionSpec.clientState_bind, clientState_bind_write, clientState_bind_write,
      clientState_bind, clientState_pure]
  rw [ht_eq]
  have hdist_all : ∀ x : Fin M, s3.mem (distBase n + x.1) = f.resDist x := by
    intro x
    have hle_card : f.resDist x ≤ M := by simpa [Fintype.card_fin] using f.resDist_le_card x
    by_cases hx : f.resDist x ≤ M - 1
    · exact (hinv_end.1 x).1 hx
    · have hxM : f.resDist x = M := by dsimp only [M, splitCount] at hle_card hx ⊢; omega
      rw [(hinv_end.1 x).2 (by dsimp only [M, splitCount] at hxM ⊢; omega), hxM]
  refine ⟨hdist_all, fun x hpos hlt => ?_⟩
  rw [← hdist_all x] at hpos hlt
  exact hinv_end.2 x hpos hlt

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

private theorem iterate_pushUnitStep_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s₀ : Memory.State} (f : (splitNet G m s₀).Flow)
    (parOf : Fin (splitCount n) → Fin (splitCount n))
    (hpar : ∀ x : Fin (splitCount n), 0 < f.resDist x → f.resDist x < splitCount n →
      f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x) :
    ∀ rem (cur : Fin (splitCount n)) (u_st : Memory.State),
      rem < splitCount n → f.resDist cur = rem →
      (∀ x : Fin (splitCount n), 0 < f.resDist x → f.resDist x < splitCount n →
        u_st.mem (parBase n + x.1) = (parOf x).1) →
      (∀ x y : Fin (splitCount n),
        ((x, y) ∈ pathArcs (buildPath parOf rem cur) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem cur)) →
        u_st.mem (flowBase n + x.1 * splitCount n + y.1) = f x y) →
      let t_end := (Memory.spec 0).clientState u_st (iterate pushUnitStep n rem cur.1)
      (∀ a < flowBase n, t_end.mem a = u_st.mem a) ∧
      (∀ x y : Fin (splitCount n),
        t_end.mem (flowBase n + x.1 * splitCount n + y.1) =
          if (x, y) ∈ pathArcs (buildPath parOf rem cur) then
            f x y + (1 - min 1 (f y x))
          else if (y, x) ∈ pathArcs (buildPath parOf rem cur) then
            f x y - min 1 (f x y)
          else
            u_st.mem (flowBase n + x.1 * splitCount n + y.1))
  | 0, cur, u_st, _, _, _, _ => by
    refine ⟨fun _ _ => rfl, fun x y => ?_⟩
    simp only [iterate, buildPath, pathArcs_singleton, List.not_mem_nil, ↓reduceIte]
    rfl
  | rem + 1, cur, u_st, hrem, hcur, hp_mem, hf_sub => by
    let M := splitCount n
    obtain ⟨hd_p, hrc_p⟩ := hpar cur (by omega) (by omega)
    have hp_rem : f.resDist (parOf cur) = rem := by omega
    have hne_pc : parOf cur ≠ cur := fun h => by rw [h] at hp_rem; omega
    have hpar_val : u_st.mem (parBase n + cur.1) = (parOf cur).1 :=
      hp_mem cur (by omega) (by omega)
    have hne_path := buildPath_ne_nil parOf rem (parOf cur)
    have hlast_path := buildPath_getLast? parOf rem (parOf cur)
    have harcs_eq : pathArcs (buildPath parOf (rem + 1) cur) =
        pathArcs (buildPath parOf rem (parOf cur)) ++ [(parOf cur, cur)] := by
      rw [buildPath]
      exact pathArcs_append_singleton hne_path hlast_path
    have hf_rev : u_st.mem (flowBase n + cur.1 * M + (parOf cur).1) = f cur (parOf cur) :=
      hf_sub cur (parOf cur) (Or.inr (by rw [harcs_eq]; simp))
    have hf_fwd : u_st.mem (flowBase n + (parOf cur).1 * M + cur.1) = f (parOf cur) cur :=
      hf_sub (parOf cur) cur (Or.inl (by rw [harcs_eq]; simp))
    have hstep_res_state :
        (Memory.spec 0).clientResult u_st (pushUnitStep (n, cur.1)) = (parOf cur).1 ∧
        let u1 := (Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))
        (∀ a < flowBase n, u1.mem a = u_st.mem a) ∧
        (∀ x : Fin M, u1.mem (parBase n + x.1) = u_st.mem (parBase n + x.1)) ∧
        (∀ x y : Fin M,
          u1.mem (flowBase n + x.1 * M + y.1) =
            if (x, y) = (parOf cur, cur) then f x y + (1 - min 1 (f y x))
            else if (y, x) = (parOf cur, cur) then f x y - min 1 (f x y)
            else u_st.mem (flowBase n + x.1 * M + y.1)) := by
      have hlow1 : ∀ a < flowBase n,
          ((Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))).mem a = u_st.mem a :=
        fun a ha => preservesAt_pushUnitStep (Or.inl ha) u_st
      have hpar1 : ∀ x : Fin M,
          ((Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))).mem (parBase n + x.1) =
            u_st.mem (parBase n + x.1) :=
        fun x => preservesAt_pushUnitStep (Or.inr (by dsimp only [parBase]; omega)) u_st
      refine ⟨?_, hlow1, hpar1, ?_⟩
      · unfold pushUnitStep
        dsimp only
        rw [clientResult_bind_read, ite_eq_left cur.2, clientResult_bind_read, hpar_val,
          ite_eq_left (parOf cur).2,
          clientResult_bind_read, hf_rev]
        by_cases hrev0 : 0 < f cur (parOf cur)
        · rw [ite_eq_left hrev0, clientResult_bind_write]; rfl
        · have hcap_le := cap_splitNet_le G m s₀ (parOf cur) cur
          have hf_lt_cap : f (parOf cur) cur ≤ n := by unfold Network.Flow.resCap at hrc_p; omega
          rw [ite_eq_right hrev0, clientResult_bind_read, hf_fwd, ite_eq_left hf_lt_cap,
            clientResult_bind_write]; rfl
      · intro x y
        dsimp only [M] at x y ⊢
        change ((Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))).mem
          (flowBase n + x.1 * M + y.1) = _
        unfold pushUnitStep
        dsimp only
        rw [clientState_bind_read, ite_eq_left cur.2, clientState_bind_read, hpar_val,
          ite_eq_left (parOf cur).2,
          clientState_bind_read, hf_rev]
        by_cases hrev0 : 0 < f cur (parOf cur)
        · rw [ite_eq_left hrev0, clientState_bind_write]
          change Function.update u_st.mem (flowBase n + cur.1 * M + (parOf cur).1)
            (f cur (parOf cur) - 1) (flowBase n + x.1 * M + y.1) = _
          by_cases hxy : (x, y) = (parOf cur, cur)
          · injection hxy with hx hy
            rw [hx, hy]
            simp only [↓reduceIte]
            have hne_addr : flowBase n + (parOf cur).1 * M + cur.1 ≠
                flowBase n + cur.1 * M + (parOf cur).1 := by
              intro h
              have heq := finProdFinEquiv.injective
                (a₁ := (parOf cur, cur)) (a₂ := (cur, parOf cur))
                (Fin.ext (by dsimp only [M] at h; simp [finProdFinEquiv, Nat.mul_comm]; omega))
              exact hne_pc (Prod.mk.inj heq).1
            have hmin1 : min 1 (f cur (parOf cur)) = 1 := min_eq_left hrev0
            rw [Function.update_of_ne hne_addr, hf_fwd, hmin1]
            omega
          · simp only [hxy, ↓reduceIte]
            by_cases hyx : (y, x) = (parOf cur, cur)
            · injection hyx with hy hx
              rw [hy, hx]
              simp only [↓reduceIte]
              have hmin1 : min 1 (f cur (parOf cur)) = 1 := min_eq_left hrev0
              rw [Function.update_self, hmin1]
            · simp only [hyx, ↓reduceIte]
              have hne_addr : flowBase n + x.1 * M + y.1 ≠
                  flowBase n + cur.1 * M + (parOf cur).1 := by
                intro h
                have heq := finProdFinEquiv.injective
                  (a₁ := (x, y)) (a₂ := (cur, parOf cur))
                  (Fin.ext (by dsimp only [M] at h; simp [finProdFinEquiv, Nat.mul_comm]; omega))
                obtain ⟨hx, hy⟩ := Prod.mk.inj heq
                exact hyx (Prod.ext hy hx)
              exact Function.update_of_ne hne_addr _ _
        · have hrev_eq : f cur (parOf cur) = 0 := by omega
          have hcap_le := cap_splitNet_le G m s₀ (parOf cur) cur
          have hf_lt_cap : f (parOf cur) cur ≤ n := by
            unfold Network.Flow.resCap at hrc_p
            omega
          rw [ite_eq_right hrev0, clientState_bind_read, hf_fwd, ite_eq_left hf_lt_cap,
            clientState_bind_write]
          change Function.update u_st.mem (flowBase n + (parOf cur).1 * M + cur.1)
            (f (parOf cur) cur + 1) (flowBase n + x.1 * M + y.1) = _
          by_cases hxy : (x, y) = (parOf cur, cur)
          · injection hxy with hx hy
            rw [hx, hy]
            have hmin0 : min 1 (0 : ℕ) = 0 := min_eq_right (Nat.zero_le 1)
            simp only [↓reduceIte, hrev_eq, hmin0, Nat.sub_zero]
            rw [Function.update_self]
          · simp only [hxy, ↓reduceIte]
            have hne_addr : flowBase n + x.1 * M + y.1 ≠
                flowBase n + (parOf cur).1 * M + cur.1 := by
              intro h
              have heq := finProdFinEquiv.injective
                (a₁ := (x, y)) (a₂ := (parOf cur, cur))
                (Fin.ext (by dsimp only [M] at h; simp [finProdFinEquiv, Nat.mul_comm]; omega))
              exact hxy heq
            rw [Function.update_of_ne hne_addr]
            by_cases hyx : (y, x) = (parOf cur, cur)
            · injection hyx with hy hx
              rw [hy, hx]
              simp [hf_rev, hrev_eq]
            · simp only [hyx, ↓reduceIte]; rfl
    obtain ⟨hres1, hlow1, hpar1, hflow1⟩ := hstep_res_state
    set u1 := (Memory.spec 0).clientState u_st (pushUnitStep (n, cur.1))
    obtain ⟨_, hle_rem, _, _⟩ := buildPath_props f parOf hpar rem (parOf cur) (by omega) hp_rem
    have hdisj : ∀ a b : Fin M, (a, b) ∈ pathArcs (buildPath parOf rem (parOf cur)) →
        a ≠ cur ∧ b ≠ cur := by
      intro a b hab
      have ha := hle_rem a (fst_mem_of_mem_pathArcs hab)
      have hb := hle_rem b (snd_mem_of_mem_pathArcs hab)
      exact ⟨fun h => by subst h; omega, fun h => by subst h; omega⟩
    have hf_sub1 : ∀ x y : Fin M,
        ((x, y) ∈ pathArcs (buildPath parOf rem (parOf cur)) ∨
          (y, x) ∈ pathArcs (buildPath parOf rem (parOf cur))) →
        u1.mem (flowBase n + x.1 * M + y.1) = f x y := by
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
    have hih := iterate_pushUnitStep_spec f parOf hpar rem (parOf cur) u1 (by omega) hp_rem
      (fun x hx1 hx2 => (hpar1 x).trans (hp_mem x hx1 hx2)) hf_sub1
    dsimp only [iterate]
    rw [StateTransitionSpec.clientState_bind, hres1]
    refine ⟨fun a ha => (hih.1 a ha).trans (hlow1 a ha), fun x y => ?_⟩
    rw [hih.2 x y, hflow1 x y, harcs_eq]
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

private def midCut (n : ℕ) : Finset (Fin (splitCount n)) :=
  Finset.univ.filter fun x => x.1 = 0 ∨ (2 ≤ x.1 ∧ x.1 < n + 2)

private theorem isCut_midCut {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) :
    (splitNet G m s).IsCut (midCut n) := by
  refine ⟨?_, ?_⟩
  · simp [midCut, splitNet]
  · simp [midCut, splitNet]

private theorem cutCapacity_midCut_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (m : ℕ) (s : Memory.State) :
    (splitNet G m s).cutCapacity (midCut n) ≤ n := by
  let N := splitNet G m s
  have hinner : ∀ x ∈ midCut n,
      (∑ y ∈ Finset.univ \ midCut n, N.cap x y) ≤ if x.1 = 0 then 0 else 1 := by
    intro x hx
    simp only [midCut, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rcases hx with hx0 | hx_in
    · rw [ite_eq_left hx0]
      refine le_of_eq (Finset.sum_eq_zero fun y hy => ?_)
      simp only [midCut, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      unfold N splitNet
      dsimp only
      rw [ite_eq_left hx0, ite_eq_right (fun h => hy (Or.inr h))]
    · have hxne : x.1 ≠ 0 := by omega
      rw [ite_eq_right hxne]
      let y0 : Fin (splitCount n) := ⟨x.1 + n, by dsimp only [splitCount]; omega⟩
      have hsub : (∑ y ∈ Finset.univ \ midCut n, N.cap x y) ≤ N.cap x y0 := by
        have hzero : ∀ y ∈ Finset.univ \ midCut n, y ≠ y0 → N.cap x y = 0 := by
          intro y hy hne
          simp only [midCut, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and] at hy
          have hy1 : y.1 ≠ 1 → ¬ y.1 = x.1 + n → N.cap x y = 0 := by
            intro hy_not1 hy_not_add
            unfold N splitNet
            dsimp only
            rw [ite_eq_right hxne, ite_eq_right hy_not1, ite_eq_left hx_in,
              ite_eq_right hy_not_add]
          by_cases hy_eq1 : y.1 = 1
          · unfold N splitNet
            dsimp only
            rw [ite_eq_right hxne, ite_eq_left hy_eq1, ite_eq_right (by omega)]
          · exact hy1 hy_eq1 (fun h => hne (Fin.ext h))
        by_cases hy0_mem : y0 ∈ Finset.univ \ midCut n
        · rw [Finset.sum_eq_single y0 (fun y hy hne => hzero y hy hne)
            (fun h => absurd hy0_mem h)]
        · rw [Finset.sum_eq_zero (fun y hy => hzero y hy (fun h => hy0_mem (h ▸ hy)))]
          exact Nat.zero_le _
      refine hsub.trans ?_
      unfold N splitNet
      dsimp only [y0]
      rw [ite_eq_right hxne, ite_eq_right (by omega), ite_eq_left hx_in, ite_eq_left rfl]
      split_ifs <;> omega
  calc N.cutCapacity (midCut n)
      ≤ ∑ x ∈ midCut n, (if x.1 = 0 then 0 else 1) := Finset.sum_le_sum hinner
    _ = ((midCut n).filter fun x => x.1 ≠ 0).card := by simp [Finset.sum_ite]
    _ = (Finset.univ.image (inIdx (n := n))).card := by
        congr 1
        ext x
        simp only [midCut, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, inIdx]
        constructor
        · rintro ⟨hx0 | hxin, hne⟩
          · exact absurd hx0 hne
          · exact ⟨⟨x.1 - 2, by omega⟩, Fin.ext (by dsimp only; omega)⟩
        · rintro ⟨v, hv⟩
          subst hv
          dsimp only
          exact ⟨Or.inr ⟨by omega, by omega⟩, by omega⟩
    _ ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_image_le
    _ = n := Fintype.card_fin n

/-- Minimum-cut correctness and side-indicator specification for `minSepProg`. -/
theorem minSepProg_spec {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {m : ℕ} {s : Memory.State} (hG : MatrixLoaded G s) :
    let res := (Memory.spec 0).clientResult s (minSepProg (n, m))
    let t := (Memory.spec 0).clientState s (minSepProg (n, m))
    let N := splitNet G m s
    (∀ a < flowBase n, t.mem a = s.mem a) ∧
      ∃ C : Finset (Fin (splitCount n)),
        N.IsMinCut C ∧
        N.cutCapacity C ≤ n ∧
        (∀ x : Fin (splitCount n), t.mem (distBase n + x.1) < splitCount n ↔ x ∈ C) ∧
        (∀ v : Fin n, t.mem (sepOutBase n + v.1) =
          if s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C then 1 else 0) ∧
        res = (Finset.univ.filter fun v : Fin n => t.mem (sepOutBase n + v.1) = 1).card ∧
        res ≤ N.cutCapacity C := by
  intro res t N
  have hlow_all : ∀ a < flowBase n, t.mem a = s.mem a :=
    fun a ha => preservesAt_minSepProg ha s
  refine ⟨hlow_all, ?_⟩
  let M := splitCount n
  have hst_ne : N.s ≠ N.t := by
    intro h; have := congrArg Fin.val h; dsimp only [N, splitNet] at this; omega
  set s1 := (Memory.spec 0).clientState s (fillRange ((flowBase n, 0), M * M))
  have hs1 := fillRange_spec (flowBase n) 0 (M * M) s
  have hf0 : FlowStored (Network.Flow.zero N) s1 := by
    intro x y
    have hxy := hs1.1 (x.1 * M + y.1) (by dsimp only [M]; nlinarith [x.2, y.2])
    change s1.mem (flowBase n + (x.1 * M + y.1)) = 0 at hxy
    rw [← Nat.add_assoc] at hxy
    exact hxy
  have hs1_low : ∀ a < flowBase n, s1.mem a = s.mem a := fun a ha => hs1.2 a (Or.inl ha)
  have hrounds := iterate_invariant_of augRoundStep (n, m)
    (fun rem (r : ℕ) st =>
      r + rem = n ∧
      (∀ a < flowBase n, st.mem a = s.mem a) ∧
      ∃ f : N.Flow, FlowStored f st ∧ (¬ f.ResReachable N.s N.t ∨ (r : ℤ) ≤ f.value))
    (fun rem r st ⟨hrsum, hst_low, f, hf_st, hval_or⟩ => by
      unfold augRoundStep
      dsimp only
      rw [clientResult_bind, clientState_bind, clientResult_bind_read, clientState_bind_read]
      set tb := (Memory.spec 0).clientState st (bfsProg (n, m))
      obtain ⟨htb_low, htb_dist, htb_par⟩ := bfsProg_spec hG hst_low f hf_st
      have hd1_eq : tb.mem (distBase n + 1) = f.resDist N.t := htb_dist N.t
      by_cases hd1 : tb.mem (distBase n + 1) < M
      · rw [ite_eq_left hd1, clientResult_bind, clientResult_pure,
          clientState_bind, clientState_pure]
        have ht_reach : f.ResReachable N.s N.t := by
          rw [← f.resDist_lt_card_iff_resReachable, Fintype.card_fin]
          rwa [← hd1_eq]
        have hr_le : (r : ℤ) ≤ f.value := hval_or.resolve_left (not_not.mpr ht_reach)
        let parOf : Fin M → Fin M := fun x =>
          if h : tb.mem (parBase n + x.1) < M then ⟨tb.mem (parBase n + x.1), h⟩
          else ⟨0, by dsimp only [M, splitCount]; omega⟩
        have hparOf : ∀ x : Fin M, 0 < f.resDist x → f.resDist x < M →
            tb.mem (parBase n + x.1) = (parOf x).1 ∧
            f.resDist (parOf x) + 1 = f.resDist x ∧ 0 < f.resCap (parOf x) x := by
          intro x hx1 hx2
          obtain ⟨u, hu1, hu2, hu3⟩ := htb_par x hx1 hx2
          have hu_lt : tb.mem (parBase n + x.1) < M := by rw [hu1]; exact u.2
          have hp_eq : parOf x = u :=
            Fin.ext (by dsimp only [parOf]; rw [dite_eq_left hu_lt]; exact hu1)
          rw [hp_eq]
          exact ⟨hu1, hu2, hu3⟩
        have hd1_lt : f.resDist N.t < M := by omega
        obtain ⟨hp_head, _, hp_nd, hp_arcs⟩ :=
          buildPath_props f parOf (fun x h1 h2 => (hparOf x h1 h2).2)
            (f.resDist N.t) N.t hd1_lt rfl
        have hp_last := buildPath_getLast? parOf (f.resDist N.t) N.t
        let f' := f.augment (buildPath parOf (f.resDist N.t) N.t) hp_nd hp_head hp_last 1 hp_arcs
        have hf_tb : FlowStored f tb := fun x y => by
          rw [htb_low _ (by dsimp only [distBase]; nlinarith [x.2, y.2]), hf_st x y]
        have hpush := iterate_pushUnitStep_spec f parOf (fun x h1 h2 => (hparOf x h1 h2).2)
          (f.resDist N.t) N.t tb hd1_lt rfl (fun x h1 h2 => (hparOf x h1 h2).1)
          (fun x y _ => hf_tb x y)
        have hflow_f' : FlowStored f'
            ((Memory.spec 0).clientState tb (iterate pushUnitStep n (f.resDist N.t) 1)) := by
          intro x y
          change ((Memory.spec 0).clientState tb
            (iterate pushUnitStep n (f.resDist N.t) N.t.1)).mem
            (flowBase n + x.1 * splitCount n + y.1) = f' x y
          rw [hpush.2 x y, hf_tb x y]
          rfl
        rw [hd1_eq]
        refine ⟨by omega, fun a ha => (hpush.1 a ha).trans
          ((htb_low a (by dsimp only [distBase]; omega)).trans (hst_low a ha)),
          f', hflow_f', Or.inr ?_⟩
        have hval' := f.value_augment hst_ne hp_nd hp_head hp_last 1 hp_arcs
        change ((r + 1 : ℕ) : ℤ) ≤ f'.value
        rw [hval']
        omega
      · rw [ite_eq_right hd1]
        simp only [client_simps]
        have hno_reach : ¬ f.ResReachable N.s N.t := by
          rw [← f.resDist_lt_card_iff_resReachable, Fintype.card_fin, ← hd1_eq]
          exact hd1
        have hf_tb : FlowStored f tb := fun x y => by
          rw [htb_low _ (by dsimp only [distBase]; nlinarith [x.2, y.2]), hf_st x y]
        exact ⟨by omega, fun a ha =>
          (htb_low a (by dsimp only [distBase]; omega)).trans (hst_low a ha),
          f, hf_tb, Or.inl hno_reach⟩)
    (n := n) (a := 0) (s := s1)
    ⟨Nat.zero_add _, hs1_low, Network.Flow.zero N, hf0, Or.inr (by simp)⟩
  obtain ⟨hrend, hs2_low, f_end, hf_end, hdone_or⟩ := hrounds
  set s2 := (Memory.spec 0).clientState s1 (iterate augRoundStep (n, m) n 0)
  have hr_eq_n : (Memory.spec 0).clientResult s1 (iterate augRoundStep (n, m) n 0) = n := by omega
  rw [hr_eq_n] at hdone_or
  have hno_aug : ¬ ∃ p, f_end.IsAugmentingPath p := by
    rw [f_end.exists_augmentingPath_iff_resReachable]
    rcases hdone_or with hnr | hval_ge
    · exact hnr
    · intro hreach
      obtain ⟨p, hp⟩ := f_end.exists_augmentingPath_iff_resReachable.mpr hreach
      have hlt := f_end.lt_value_augmentByBottleneck hst_ne hp
      have hle_cut := (f_end.augmentByBottleneck p hp).value_le_cutCapacity (isCut_midCut G m s)
      have hcap_mid : N.cutCapacity (midCut n) ≤ n := cutCapacity_midCut_le G m s
      change (f_end.augmentByBottleneck p hp).value ≤ (N.cutCapacity (midCut n) : ℤ) at hle_cut
      omega
  set s3 := (Memory.spec 0).clientState s2 (bfsProg (n, m))
  obtain ⟨hs3_low, hs3_dist, _⟩ := bfsProg_spec hG hs2_low f_end hf_end
  let C := f_end.reachableCut
  have hcut : N.IsCut C := f_end.reachableCut_isCut hno_aug
  have hval_cut : f_end.value = (N.cutCapacity C : ℤ) :=
    f_end.value_eq_cutCapacity_reachableCut hno_aug
  have hmin : N.IsMinCut C := f_end.isMinCut_of_value_eq_cutCapacity hcut hval_cut
  have hcapC_le : N.cutCapacity C ≤ n :=
    (hmin.2 (midCut n) (isCut_midCut G m s)).trans (cutCapacity_midCut_le G m s)
  have hdist_iff : ∀ x : Fin M, s3.mem (distBase n + x.1) < M ↔ x ∈ C := by
    intro x
    rw [hs3_dist x, f_end.mem_reachableCut_iff, ← f_end.resDist_lt_card_iff_resReachable,
      Fintype.card_fin]
  have hext := iterate_invariant_of extractSepStep n
    (fun rem (vc : ℕ × ℕ) st =>
      vc.1 + rem = n ∧
      (∀ a < sepOutBase n, st.mem a = s3.mem a) ∧
      (∀ v : Fin n, v.1 < vc.1 → st.mem (sepOutBase n + v.1) =
        if s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C then 1 else 0) ∧
      vc.2 = ((Finset.univ : Finset (Fin n)).filter fun v =>
        v.1 < vc.1 ∧ s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C).card)
    (fun rem vc st ⟨hvsum, hst_pre, hprev, hcnt⟩ => by
      have hv_lt : vc.1 < n := by omega
      let vFin : Fin n := ⟨vc.1, hv_lt⟩
      have hw_eq : st.mem (wBase n + vc.1) = s.mem (wBase n + vc.1) := by
        rw [hst_pre _ (by dsimp only [sepOutBase, parBase, distBase, flowBase, wBase]; omega),
          hs3_low _ (by dsimp only [distBase, flowBase, wBase]; omega),
          hs2_low _ (by dsimp only [flowBase, wBase]; omega)]
      have hdin_eq : st.mem (distBase n + (vc.1 + 2)) = s3.mem (distBase n + (inIdx vFin).1) :=
        hst_pre _ (by dsimp only [sepOutBase, parBase, distBase, splitCount]; omega)
      have hdout_eq : st.mem (distBase n + (vc.1 + n + 2)) =
          s3.mem (distBase n + (outIdx vFin).1) :=
        hst_pre _ (by dsimp only [sepOutBase, parBase, distBase, splitCount]; omega)
      have hout_le : s3.mem (distBase n + (outIdx vFin).1) ≤ M := by
        rw [hs3_dist]; simpa [Fintype.card_fin] using f_end.resDist_le_card (outIdx vFin)
      have hpred_iff : (s.mem (wBase n + vc.1) = 0 ∧
          s3.mem (distBase n + (inIdx vFin).1) < M ∧
          s3.mem (distBase n + (outIdx vFin).1) = M) ↔
          (s.mem (wBase n + vc.1) = 0 ∧ inIdx vFin ∈ C ∧ outIdx vFin ∉ C) := by
        rw [← hdist_iff (inIdx vFin), ← hdist_iff (outIdx vFin)]
        exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩,
          fun ⟨h1, h2, h3⟩ => ⟨h1, h2, by omega⟩⟩
      unfold extractSepStep
      dsimp only [LoopAccArgs.idx, LoopAccArgs.acc]
      rw [clientResult_bind_read, clientState_bind_read, clientResult_bind_read,
        clientState_bind_read, clientResult_bind_read, clientState_bind_read,
        hw_eq, hdin_eq, hdout_eq]
      by_cases hp : s.mem (wBase n + vc.1) = 0 ∧
          s3.mem (distBase n + (inIdx vFin).1) < M ∧
          s3.mem (distBase n + (outIdx vFin).1) = M
      · have hp' := hpred_iff.mp hp
        rw [ite_eq_left hp, clientResult_bind_write, clientState_bind_write, clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, fun a ha => ?_, fun u hu => ?_, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hst_pre a ha
        · by_cases huv : u.1 = vc.1
          · have hueq : u = vFin := Fin.ext huv
            subst hueq
            dsimp only [vFin]
            rw [Function.update_self, ite_eq_left hp']
          · rw [Function.update_of_ne (by omega)]; exact hprev u (by omega)
        · have hfilt : ((Finset.univ : Finset (Fin n)).filter fun v =>
              v.1 < vc.1 + 1 ∧ s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C) =
              insert vFin (((Finset.univ : Finset (Fin n)).filter fun v =>
                v.1 < vc.1 ∧ s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C)) := by
            ext v
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
            constructor
            · rintro ⟨hlt, hw, hin, hout⟩
              by_cases hveq : v.1 = vc.1
              · exact Or.inl (Fin.ext hveq)
              · exact Or.inr ⟨by omega, hw, hin, hout⟩
            · rintro (rfl | ⟨hlt, hw, hin, hout⟩)
              · exact ⟨by dsimp only [vFin]; omega, hp'.1, hp'.2.1, hp'.2.2⟩
              · exact ⟨by omega, hw, hin, hout⟩
          rw [hfilt, Finset.card_insert_of_notMem (by simp [vFin]), hcnt]
      · have hp' : ¬ (s.mem (wBase n + vc.1) = 0 ∧ inIdx vFin ∈ C ∧ outIdx vFin ∉ C) :=
          fun h => hp (hpred_iff.mpr h)
        rw [ite_eq_right hp, clientResult_bind_write, clientState_bind_write, clientResult_pure,
          clientState_pure]
        dsimp only
        refine ⟨by omega, fun a ha => ?_, fun u hu => ?_, ?_⟩
        · rw [Function.update_of_ne (by omega)]; exact hst_pre a ha
        · by_cases huv : u.1 = vc.1
          · have hueq : u = vFin := Fin.ext huv
            subst hueq
            dsimp only [vFin]
            rw [Function.update_self, ite_eq_right hp']
          · rw [Function.update_of_ne (by omega)]; exact hprev u (by omega)
        · rw [hcnt]
          symm
          congr 1
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          constructor
          · rintro ⟨hlt, hw, hin, hout⟩
            by_cases hveq : v.1 = vc.1
            · have hv_eq : v = vFin := Fin.ext hveq
              subst hv_eq
              exact absurd ⟨hw, hin, hout⟩ hp'
            · exact ⟨by omega, hw, hin, hout⟩
          · rintro ⟨hlt, hw, hin, hout⟩
            exact ⟨by omega, hw, hin, hout⟩)
    (n := n) (a := (0, 0)) (s := s3)
    ⟨Nat.zero_add _, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), by simp⟩
  obtain ⟨hvsum_end, hpre_end, hsep_end, hcnt_end⟩ := hext
  set s4 := (Memory.spec 0).clientState s3 (iterate extractSepStep n n (0, 0))
  set vc_end := (Memory.spec 0).clientResult s3 (iterate extractSepStep n n (0, 0))
  have hvc1 : vc_end.1 = n := by omega
  rw [hvc1] at hsep_end hcnt_end
  have hsep_fin : ∀ v : Fin n, s4.mem (sepOutBase n + v.1) =
      if s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C then 1 else 0 :=
    fun v => hsep_end v v.2
  have hcnt_fin : vc_end.2 =
      (Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1).card := by
    rw [hcnt_end]
    congr 1
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, v.2, hsep_fin v]
    by_cases h : s.mem (wBase n + v.1) = 0 ∧ inIdx v ∈ C ∧ outIdx v ∉ C <;> simp [h]
  have ht_eq : t = s4 := by
    change (Memory.spec 0).clientState s (minSepProg (n, m)) = s4
    unfold minSepProg
    dsimp only
    rw [clientState_bind, clientState_bind, clientState_bind, clientState_bind, clientState_pure]
  have hres_eq : res = vc_end.2 := by
    change (Memory.spec 0).clientResult s (minSepProg (n, m)) = vc_end.2
    unfold minSepProg
    dsimp only
    rw [clientResult_bind, clientResult_bind, clientResult_bind, clientResult_bind,
      clientResult_pure]
  rw [ht_eq, hres_eq]
  refine ⟨C, hmin, hcapC_le, ?_, hsep_fin, hcnt_fin, ?_⟩
  · intro x
    rw [hpre_end _ (by dsimp only [sepOutBase, parBase, distBase]; have := x.2; omega)]
    exact hdist_iff x
  · let X := Finset.univ.filter fun v : Fin n => s4.mem (sepOutBase n + v.1) = 1
    have hX_sub : X.image (inIdx (n := n)) ⊆ C := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, hsep_fin v] at hv
      split_ifs at hv with h
      exact h.2.1
    have hX_cap : ∀ v ∈ X, 1 ≤ ∑ y ∈ Finset.univ \ C, N.cap (inIdx v) y := by
      intro v hv
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and, hsep_fin v] at hv
      split_ifs at hv with h
      have hout_mem : outIdx v ∈ Finset.univ \ C := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h.2.2⟩
      have hcap1 : N.cap (inIdx v) (outIdx v) = 1 := by
        unfold N splitNet
        dsimp only [inIdx, outIdx]
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩,
          ite_eq_left (by omega), Nat.add_sub_cancel, ite_eq_left h.1]
      rw [← hcap1]
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hout_mem
    rw [hcnt_fin]
    calc X.card
        = (X.image (inIdx (n := n))).card :=
          (Finset.card_image_of_injective X (inIdx_injective n)).symm
      _ = ∑ _x ∈ X.image (inIdx (n := n)), 1 := by simp
      _ ≤ ∑ x ∈ X.image (inIdx (n := n)), ∑ y ∈ Finset.univ \ C, N.cap x y := by
          refine Finset.sum_le_sum fun x hx => ?_
          obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
          exact hX_cap v hv
      _ ≤ ∑ x ∈ C, ∑ y ∈ Finset.univ \ C, N.cap x y :=
          Finset.sum_le_sum_of_subset hX_sub
      _ = N.cutCapacity C := rfl

end Cslib.Algorithms.WordRAM.OddCycleTransversal
