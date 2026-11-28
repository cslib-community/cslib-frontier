/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.Arborescence.Internal.BasicProg
public import CslibFrontier.Algorithms.Lean.Arborescence.Table
import CslibFrontier.Foundations.Data.List.RowMajor

/-!
# Correctness and memory-cost specifications for basic subroutines (internal)

Proves admissibility, frame preservation, `O(n²)`/`O(n)` memory cost, and functional
correctness for `copyWordsProg`, `zeroWordsProg`, `argMinArrayProg`, `selectParentsProg`,
`findCycleProg`, and `cycleMaskProg`.
-/

namespace Cslib.Algorithms.WordRAM.Arborescence.Internal

open Cslib.Algorithms.Lean.Arborescence
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization
open Cslib.WordRAM.Realization.Signed

attribute [local client_simps] StateTransitionSpec.clientState
  StateTransitionSpec.runClient_pure'
  runClient_read runClient_write runClient_allocDirty runClient_ite
  prog_clientState_ite

/-! ### Correctness, admissibility, and `O(n³)` memory-cost specifications -/

private theorem foldl_take_finRange_succ {α : Type*} {n k : ℕ} (hk : k < n)
    (g : α → Fin n → α) (init : α) :
    ((List.finRange n).take (k + 1)).foldl g init =
      g (((List.finRange n).take k).foldl g init) ⟨k, hk⟩ := by
  rw [List.take_succ_finRange hk, List.foldl_append, List.foldl_cons, List.foldl_nil]

public theorem copyWordsProg_spec {w : ℕ} (a : CopyArgs) (s₀ : Memory.State)
    (hsrc_f : a.src + a.len ≤ s₀.frontier) (hdst_f : a.dst + a.len ≤ s₀.frontier)
    (hdisj : a.src + a.len ≤ a.dst ∨ a.dst + a.len ≤ a.src)
    (hfit_src : Fits w (a.src + a.len)) (hfit_dst : Fits w (a.dst + a.len))
    (hfit_len : Fits w a.len) (hval : ∀ i < a.len, Fits w (s₀.mem (a.src + i))) :
    let s' := (Memory.spec 0).clientState s₀ (copyWordsProg a)
    iterationSafe copyStep CopyStepSafe w a a.len 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (copyWordsProg a)) ∧
      memoryCost (copyWordsProg a) s₀ ≤ 2 * a.len ∧
      s'.frontier = s₀.frontier ∧
      (∀ x, ¬(a.dst ≤ x ∧ x < a.dst + a.len) → s'.mem x = s₀.mem x) ∧
      (∀ i < a.len, s'.mem (a.dst + i) = s₀.mem (a.src + i)) := by
  have h := iterate_spec copyStep CopyStepSafe w a 2 a.len
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧
      (∀ j < k, s.mem (a.dst + j) = s₀.mem (a.src + j)) ∧
      (∀ j < a.len, s.mem (a.src + j) = s₀.mem (a.src + j)))
    (fun x => a.dst ≤ x ∧ x < a.dst + a.len)
    (fun k hk idx s ⟨hidx, hfr, hdst, hsrc⟩ => by
      subst idx
      have hsrc_eq := hsrc k hk
      refine ⟨by dsimp only [CopyStepSafe]; exact ⟨hfit_src.of_le (by omega),
          hfit_dst.of_le (by omega), hfit_len.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold copyStep
        dsimp only
        exact validHistory_read_bind (by omega)
          (validHistory_write_bind (by omega) (hsrc_eq ▸ hval k hk) (validHistory_pure w _ _))
      · unfold copyStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [copyStep, client_simps]
      · intro x hx
        simp only [copyStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · simp [copyStep, client_simps]
      · simpa [copyStep, client_simps] using hfr
      · intro j hj
        simp only [copyStep, client_simps]
        by_cases hjk : j = k
        · subst j
          simp [hsrc_eq]
        · rw [Function.update_of_ne (by omega)]
          exact hdst j (by omega)
      · intro j hj
        simp only [copyStep, client_simps]
        rw [Function.update_of_ne (by omega)]
        exact hsrc j hj)
    0 s₀ ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ => rfl⟩
  unfold copyWordsProg
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2.1⟩

private theorem zeroWordsProg_spec {w : ℕ} (a : ZeroArgs) (s₀ : Memory.State)
    (hdst_f : a.dst + a.len ≤ s₀.frontier)
    (hfit_dst : Fits w (a.dst + a.len)) (hfit_len : Fits w a.len) :
    let s' := (Memory.spec 0).clientState s₀ (zeroWordsProg a)
    iterationSafe zeroStep ZeroStepSafe w a a.len 0 s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (zeroWordsProg a)) ∧
      memoryCost (zeroWordsProg a) s₀ ≤ a.len ∧
      s'.frontier = s₀.frontier ∧
      (∀ x, ¬(a.dst ≤ x ∧ x < a.dst + a.len) → s'.mem x = s₀.mem x) ∧
      (∀ i < a.len, s'.mem (a.dst + i) = 0) := by
  have h := iterate_spec zeroStep ZeroStepSafe w a 1 a.len
    (fun k idx s => idx = k ∧ s.frontier = s₀.frontier ∧ ∀ j < k, s.mem (a.dst + j) = 0)
    (fun x => a.dst ≤ x ∧ x < a.dst + a.len)
    (fun k hk idx s ⟨hidx, hfr, hz⟩ => by
      subst idx
      refine ⟨by dsimp only [ZeroStepSafe]; exact ⟨hfit_dst.of_le (by omega),
          hfit_len.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · unfold zeroStep
        dsimp only
        exact validHistory_write_bind
          (by rw [hfr]; omega) (fits_zero w) (validHistory_pure w _ _)
      · unfold zeroStep
        dsimp only
        rw [memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [zeroStep, client_simps]
      · intro x hx
        simp only [zeroStep, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · simp [zeroStep, client_simps]
      · simpa [zeroStep, client_simps] using hfr
      · intro j hj
        simp only [zeroStep, client_simps]
        by_cases hjk : j = k
        · subst j
          simp
        · rw [Function.update_of_ne (by omega)]
          exact hz j (by omega))
    0 s₀ ⟨rfl, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  unfold zeroWordsProg
  refine ⟨h.1, h.2.1, by simpa using h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- Encodes `some j` as `j.1` and `none` as the sentinel `n`. -/
@[expose] public def optFinIdx {n : ℕ} : Option (Fin n) → ℕ
  | some j => j.val
  | none => n

public theorem argMinArrayProg_spec {w n : ℕ} (predBase costBase : ℕ)
    (pred : Fin n → Bool) (val : Fin n → ℤ) (s₀ : Memory.State)
    (h2 : Fits w 2) (hfit_p : Fits w (predBase + n)) (hfit_c : Fits w (costBase + n))
    (hfit_n : Fits w n)
    (hp_f : predBase + n ≤ s₀.frontier) (hc_f : costBase + n ≤ s₀.frontier)
    (hp_mem : ∀ i : Fin n, s₀.mem (predBase + i.val) = if pred i then 1 else 0)
    (hc_mem : ∀ i : Fin n, s₀.mem (costBase + i.val) = Signed.encode (val i)) :
    let a : ArgMinArgs := ⟨n, predBase, costBase⟩
    iterationSafe argMinStep ArgMinStepSafe w a n ⟨0, n, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (argMinArrayProg a)) ∧
      memoryCost (argMinArrayProg a) s₀ ≤ 2 * n ∧
      (Memory.spec 0).clientState s₀ (argMinArrayProg a) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (argMinArrayProg a) = optFinIdx (argMinFin n pred val) := by
  let a : ArgMinArgs := ⟨n, predBase, costBase⟩
  let stepFn := fun (acc : Option (Fin n)) (i : Fin n) =>
    if pred i then List.argAux (fun x y => val x < val y) acc i else acc
  have h := iterate_spec argMinStep ArgMinStepSafe w a 2 n
    (fun k st s =>
      let acc := ((List.finRange n).take k).foldl stepFn none
      st.idx = k ∧ s = s₀ ∧ st.bestIdx = optFinIdx acc ∧
        ∀ j, acc = some j → st.bestCost = Signed.encode (val j))
    (fun _ => False)
    (fun k hk st s ⟨hidx, hs, hbi, hbc⟩ => by
      rcases st with ⟨idx, bestIdx, bestCost⟩
      dsimp only at hidx hbi hbc
      subst idx s
      have hp_k : s₀.mem (predBase + k) = if pred ⟨k, hk⟩ then 1 else 0 := hp_mem ⟨k, hk⟩
      have hc_k : s₀.mem (costBase + k) = Signed.encode (val ⟨k, hk⟩) := hc_mem ⟨k, hk⟩
      have hst : (Memory.spec 0).clientState s₀ (argMinStep (a, ⟨k, bestIdx, bestCost⟩)) = s₀ := by
        unfold argMinStep
        dsimp only [a]
        rw [clientState_bind_read, clientState_bind_read]
        split_ifs <;> rfl
      refine ⟨by dsimp only [ArgMinStepSafe, a]; exact ⟨h2, hfit_p.of_le (by omega),
          hfit_c.of_le (by omega), hfit_n.of_le (by omega)⟩,
        ?_, ?_, by rw [hst], fun _ _ => by rw [hst], ?_⟩
      · unfold argMinStep
        exact validHistory_read_bind (by dsimp only [a]; omega)
          (validHistory_read_bind (by dsimp only [a]; omega)
            (by dsimp only; split_ifs <;> trivial))
      · unfold argMinStep
        dsimp only [a]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read]
        split_ifs <;> simp [client_simps]
      · rw [foldl_take_finRange_succ hk stepFn none]
        generalize hacc : ((List.finRange n).take k).foldl stepFn none = acc at hbi hbc ⊢
        dsimp only [stepFn]
        unfold argMinStep
        dsimp only [a]
        simp only [client_simps, hp_k, hc_k]
        cases hp_bool : pred ⟨k, hk⟩
        · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_ne_one, client_simps]
          exact ⟨trivial, trivial, hbi, hbc⟩
        · simp only [↓reduceIte]
          cases acc with
          | none =>
            have hbin : bestIdx = n := hbi.trans (by simp [optFinIdx])
            simp [hbin, List.argAux, optFinIdx, client_simps]
          | some j =>
            have hbin : bestIdx = j.val := hbi.trans (by simp [optFinIdx])
            have hbne : bestIdx ≠ n := by omega
            have hbcj : bestCost = Signed.encode (val j) := hbc j rfl
            simp only [hbne, ↓reduceIte, hbcj, List.argAux]
            by_cases hlt : val ⟨k, hk⟩ < val j
            · have hw : SignedLtWord (Signed.encode (val ⟨k, hk⟩)) (Signed.encode (val j)) :=
                (signedLtWord_iff _ _).mpr hlt
              simp only [hlt, hw, ↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, trivial, fun j' hj' => by cases hj'; rfl⟩
            · have hnw : ¬SignedLtWord (Signed.encode (val ⟨k, hk⟩)) (Signed.encode (val j)) :=
                mt (signedLtWord_iff _ _).mp hlt
              simp only [hlt, hnw, ↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, hbin, fun j' hj' => by cases hj'; rfl⟩)
    ⟨0, n, 0⟩ s₀ ⟨rfl, rfl, rfl, fun _ h => by simp at h⟩
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  obtain ⟨hsafe, hvh, hmc, _, _, _, hs_eq, hbi_n, _⟩ := h
  unfold argMinArrayProg
  refine ⟨hsafe, validHistory_bind_step hvh (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc,
    by simp only [client_simps]; exact hs_eq,
    ?_⟩
  simp only [client_simps]
  exact hbi_n.trans (by simp [argMinFin, stepFn, htake])

private theorem fillSelectRowProg_spec {w n ws : ℕ} (vFin : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (s : Memory.State)
    (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s.frontier)
    (ha_s : ∀ u col : Fin n, s.mem (curAdjBase ws n + u.val * n + col.val) =
      if a[u.val][col.val] then 1 else 0)
    (hc_s : ∀ u col : Fin n, s.mem (curCostBase ws n + u.val * n + col.val) =
      Signed.encode c[u.val][col.val])
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.val][col.val])) :
    let rowArgs : SelectRowArgs :=
      ⟨n, vFin.val, curAdjBase ws n, curCostBase ws n, candPredBase ws n, candCostBase ws n⟩
    let s1 := (Memory.spec 0).clientState s (fillSelectRowProg rowArgs)
    iterationSafe selectRowStep SelectRowStepSafe w rowArgs n 0 s ∧
      (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (fillSelectRowProg rowArgs)) ∧
      memoryCost (fillSelectRowProg rowArgs) s ≤ 4 * n ∧
      s1.frontier = s.frontier ∧
      (∀ x, ¬(candPredBase ws n ≤ x ∧ x < candCostBase ws n + n) → s1.mem x = s.mem x) ∧
      (∀ u col : Fin n, s1.mem (curAdjBase ws n + u.val * n + col.val) =
        if a[u.val][col.val] then 1 else 0) ∧
      (∀ u col : Fin n, s1.mem (curCostBase ws n + u.val * n + col.val) =
        Signed.encode c[u.val][col.val]) ∧
      (∀ col : Fin n,
        s1.mem (candPredBase ws n + col.val) =
          (if a[vFin.val][col.val] && col != vFin then 1 else 0) ∧
        s1.mem (candCostBase ws n + col.val) = Signed.encode c[vFin.val][col.val]) := by
  let rowArgs : SelectRowArgs :=
    ⟨n, vFin.val, curAdjBase ws n, curCostBase ws n, candPredBase ws n, candCostBase ws n⟩
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have hv_lt := vFin.isLt
  have hrow := iterate_spec selectRowStep SelectRowStepSafe w rowArgs 4 n
    (fun col idx sr => idx = col ∧ sr.frontier = s.frontier ∧
      (∀ u c0 : Fin n, sr.mem (curAdjBase ws n + u.val * n + c0.val) =
        if a[u.val][c0.val] then 1 else 0) ∧
      (∀ u c0 : Fin n, sr.mem (curCostBase ws n + u.val * n + c0.val) =
        Signed.encode c[u.val][c0.val]) ∧
      (∀ c0 : Fin n, c0.val < col →
        sr.mem (candPredBase ws n + c0.val) =
          (if a[vFin.val][c0.val] && c0 != vFin then 1 else 0) ∧
        sr.mem (candCostBase ws n + c0.val) = Signed.encode c[vFin.val][c0.val]))
    (fun x => candPredBase ws n ≤ x ∧ x < candCostBase ws n + n)
    (fun col hcol idx sr ⟨hidx_c, hfr_r, ha_r, hc_r, hdone⟩ => by
      subst idx
      have ha_mc : sr.mem (curAdjBase ws n + vFin.val * n + col) =
          if a[vFin.val][col] then 1 else 0 := ha_r vFin ⟨col, hcol⟩
      have hc_mc : sr.mem (curCostBase ws n + vFin.val * n + col) =
          Signed.encode c[vFin.val][col] := hc_r vFin ⟨col, hcol⟩
      have hout : ∀ x, ¬(candPredBase ws n ≤ x ∧ x < candCostBase ws n + n) →
          ((Memory.spec 0).clientState sr (selectRowStep (rowArgs, col))).mem x = sr.mem x := by
        intro x hx
        dsimp only [candPredBase, candCostBase] at hx
        simp only [selectRowStep, rowArgs, client_simps, candPredBase, candCostBase]
        rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      refine ⟨by dsimp only [SelectRowStepSafe, rowArgs]; exact ⟨h1,
          hws.of_le (by dsimp only [wsSize, curAdjBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize, curCostBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith),
          hws.of_le (by dsimp only [wsSize]; nlinarith)⟩, ?_, ?_, ?_, hout, ?_, ?_,
        fun u c0 => (hout _ (by
          have := List.mul_add_lt_sq u.isLt c0.isLt
          dsimp only [curAdjBase, candPredBase, candCostBase]; omega)).trans (ha_r u c0),
        fun u c0 => (hout _ (by
          have := List.mul_add_lt_sq u.isLt c0.isLt
          dsimp only [curCostBase, candPredBase, candCostBase]; omega)).trans (hc_r u c0), ?_⟩
      · unfold selectRowStep
        dsimp only [rowArgs]
        exact validHistory_read_bind
          (by dsimp only [wsSize, curAdjBase] at hf hfr_r ⊢; nlinarith)
          (validHistory_read_bind
            (by dsimp only [wsSize, curCostBase] at hf hfr_r ⊢; nlinarith)
            (validHistory_write_bind
              (by dsimp only [wsSize, candPredBase] at hf hfr_r ⊢; nlinarith)
              (by split_ifs <;> first | exact h1 | exact fits_zero w)
              (validHistory_write_bind
                (by dsimp only [wsSize, candCostBase] at hf hfr_r ⊢; nlinarith)
                (hc_mc ▸ hfit_c vFin ⟨col, hcol⟩)
                (validHistory_pure w _ _))))
      · unfold selectRowStep
        dsimp only [rowArgs]
        rw [memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_read, clientResult_read, clientState_read,
          memoryCost_bind', memoryCost_write, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [selectRowStep, rowArgs, client_simps]
      · simp [selectRowStep, rowArgs, client_simps]
      · simpa [selectRowStep, rowArgs, client_simps] using hfr_r
      · intro c0 hc0
        simp only [selectRowStep, rowArgs, client_simps]
        by_cases heq : c0.val = col
        · have hc0_eq : c0 = ⟨col, hcol⟩ := Fin.ext heq
          subst hc0_eq
          simp only [Function.update_self]
          rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_self]
          simp only [ha_mc, hc_mc]
          refine ⟨?_, trivial⟩
          by_cases hab : a[vFin.val][col] = true <;> by_cases hne : col = vFin.val <;>
            simp [hab, hne, bne_iff_ne, Fin.ext_iff]
        · rw [Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by omega),
            Function.update_of_ne (by dsimp only [candPredBase, candCostBase]; omega)]
          exact hdone c0 (by omega))
    0 s ⟨rfl, rfl, ha_s, hc_s, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  unfold fillSelectRowProg
  exact ⟨hrow.1, hrow.2.1, hrow.2.2.1, hrow.2.2.2.1, hrow.2.2.2.2.1,
    hrow.2.2.2.2.2.2.2.1, hrow.2.2.2.2.2.2.2.2.1,
    fun col => hrow.2.2.2.2.2.2.2.2.2 col col.isLt⟩

public theorem selectParentsProg_spec {w n ws k : ℕ} (r : Fin n)
    (a : AdjTable n) (c : CostTable ℤ n) (s₀ : Memory.State)
    (hk : k < n) (hws : WsFits w ws n) (hf : ws + wsSize n ≤ s₀.frontier)
    (ha : ∀ u col : Fin n, s₀.mem (curAdjBase ws n + u.val * n + col.val) =
      if a[u.val][col.val] then 1 else 0)
    (hc : ∀ u col : Fin n, s₀.mem (curCostBase ws n + u.val * n + col.val) =
      Signed.encode c[u.val][col.val])
    (hfit_c : ∀ u col : Fin n, Fits w (Signed.encode c[u.val][col.val])) :
    let sa : SelectArgs := ⟨n, r.val, ws, k⟩
    let s' := (Memory.spec 0).clientState s₀ (selectParentsProg sa)
    let sel := selectParents a c r
    (Fits w 1 ∧ iterationSafe selectOuterStep SelectOuterStepSafe w sa n ⟨0, 1⟩ s₀) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (selectParentsProg sa)) ∧
      memoryCost (selectParentsProg sa) s₀ ≤ (6 * n + 2) * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ x, ¬((candPredBase ws n ≤ x ∧ x < candCostBase ws n + n) ∨
          (frameParentBase ws n k ≤ x ∧ x < frameParentBase ws n k + n)) →
        s'.mem x = s₀.mem x) ∧
      (Memory.spec 0).clientResult s₀ (selectParentsProg sa) = (if sel.feasible then 1 else 0) ∧
      (∀ v : Fin n, s'.mem (frameParentBase ws n k + v.val) = (sel.parents[v.val]).val) := by
  let sa : SelectArgs := ⟨n, r.val, ws, k⟩
  let optFn : Fin n → Option (Fin n) := fun v =>
    if v = r then some r
    else argMinFin n (fun col => a[v.val][col.val] && col != v) (fun col => c[v.val][col.val])
  have h1 : Fits w 1 := hws.of_le (by dsimp only [wsSize]; omega)
  have h2 : Fits w 2 := hws.of_le (by dsimp only [wsSize]; omega)
  have hn_pos : 0 < n := r.pos
  have hf_pos : 0 < s₀.frontier := by dsimp only [wsSize] at hf; nlinarith
  have h := iterate_spec selectOuterStep SelectOuterStepSafe w sa (6 * n + 2) n
    (fun m st s =>
      let feasM := ((List.finRange n).take m).foldl (fun acc v => acc && (optFn v).isSome) true
      st.v = m ∧ st.feas = (if feasM then 1 else 0) ∧ s.frontier = s₀.frontier ∧
        (∀ u col : Fin n, s.mem (curAdjBase ws n + u.val * n + col.val) =
          if a[u.val][col.val] then 1 else 0) ∧
        (∀ u col : Fin n, s.mem (curCostBase ws n + u.val * n + col.val) =
          Signed.encode c[u.val][col.val]) ∧
        (∀ j : Fin n, j.val < m →
          s.mem (frameParentBase ws n k + j.val) = ((optFn j).getD j).val))
    (fun x => (candPredBase ws n ≤ x ∧ x < candCostBase ws n + n) ∨
      (frameParentBase ws n k ≤ x ∧ x < frameParentBase ws n k + n))
    (fun m hm st s ⟨hv, hfeas, hfr, ha_s, hc_s, hpar⟩ => by
      rcases st with ⟨vIdx, feasBit⟩
      dsimp only at hv hfeas
      subst vIdx
      set vFin : Fin n := ⟨m, hm⟩
      let rowArgs : SelectRowArgs :=
        ⟨n, m, curAdjBase ws n, curCostBase ws n, candPredBase ws n, candCostBase ws n⟩
      have hrow := fillSelectRowProg_spec vFin a c s hws (by rw [hfr]; exact hf) ha_s hc_s hfit_c
      set s1 := (Memory.spec 0).clientState s (fillSelectRowProg rowArgs)
      have harg := argMinArrayProg_spec (candPredBase ws n) (candCostBase ws n)
        (fun col => a[m][col.val] && col != vFin) (fun col => c[m][col.val]) s1
        h2
        (hws.of_le (by dsimp only [wsSize, candPredBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize, candCostBase]; nlinarith))
        (hws.of_le (by dsimp only [wsSize]; nlinarith))
        (by dsimp only [wsSize, candPredBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (by dsimp only [wsSize, candCostBase] at hf hfr ⊢; rw [hrow.2.2.2.1]; nlinarith)
        (fun col => (hrow.2.2.2.2.2.2.2 col).1)
        (fun col => (hrow.2.2.2.2.2.2.2 col).2)
      refine ⟨by dsimp only [SelectOuterStepSafe, sa]; exact ⟨hm, hk, hws, hrow.1, harg.1⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold selectOuterStep
        dsimp only [sa]
        refine validHistory_read_bind (by omega) ?_
        by_cases hmr : m = r.val
        · simp only [hmr, ↓reduceIte]
          exact validHistory_write_bind
            (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr ⊢; nlinarith)
            (hws.of_le (by dsimp only [wsSize]; omega))
            (validHistory_pure w _ _)
        · simp only [hmr, ↓reduceIte]
          refine validHistory_bind_step hrow.2.1 ?_
          refine validHistory_bind_step harg.2.1 ?_
          rw [harg.2.2.2.1]
          split_ifs <;> exact validHistory_write_bind
            (by dsimp only [wsSize, frameParentBase, frameBase] at hf hfr ⊢;
                rw [hrow.2.2.2.1]; nlinarith)
            (hws.of_le (by dsimp only [wsSize]; omega))
            (validHistory_pure w _ _)
      · unfold selectOuterStep
        dsimp only [sa]
        rw [memoryCost_bind', memoryCost_read, clientState_read]
        by_cases hmr : m = r.val
        · simp only [hmr, ↓reduceIte, memoryCost_bind', memoryCost_write, client_simps]
          omega
        · simp only [hmr, ↓reduceIte]
          rw [memoryCost_bind', memoryCost_bind', harg.2.2.2.1]
          have hc_row : memoryCost (fillSelectRowProg rowArgs) s ≤ 4 * n := hrow.2.2.1
          have hc_arg :
              memoryCost (argMinArrayProg ⟨n, candPredBase ws n, candCostBase ws n⟩) s1 ≤
                2 * n := harg.2.2.1
          dsimp only [rowArgs, s1] at hc_row hc_arg ⊢
          split_ifs <;>
            simp only [memoryCost_bind', memoryCost_write, memoryCost_pure] <;> omega
      · unfold selectOuterStep
        dsimp only [sa]
        by_cases hmr : m = r.val
        · simp [hmr, client_simps, hfr]
        · have harg_s := harg.2.2.2.1
          have hrow_fr := hrow.2.2.2.1
          dsimp only [s1, rowArgs, vFin] at harg_s hrow_fr
          rw [StateTransitionSpec.clientState] at harg_s hrow_fr
          simp only [hmr, ↓reduceIte, client_simps]
          split_ifs <;> simp [client_simps, harg_s, hrow_fr, hfr]
      · intro x hx
        unfold selectOuterStep
        dsimp only [sa]
        have hx_p : x ≠ frameParentBase ws n k + m := by
          intro heq
          exact hx (Or.inr ⟨by omega, by omega⟩)
        by_cases hmr : m = r.val
        · simp only [hmr, ↓reduceIte, client_simps]
          rw [hmr] at hx_p
          exact Function.update_of_ne hx_p _ _
        · have harg_s := harg.2.2.2.1
          dsimp only [s1, rowArgs] at harg_s
          have hs1_x : ((Memory.spec 0).clientState s (fillSelectRowProg rowArgs)).mem x =
              s.mem x := hrow.2.2.2.2.1 x (fun hcand => hx (Or.inl hcand))
          dsimp only [rowArgs] at hs1_x
          rw [StateTransitionSpec.clientState] at harg_s hs1_x
          simp only [hmr, ↓reduceIte, client_simps]
          split_ifs <;> simp [client_simps, harg_s, Function.update_of_ne hx_p, hs1_x]
      · rw [foldl_take_finRange_succ hm]
        unfold selectOuterStep
        dsimp only [sa]
        have hne_adj (u col : Fin n) :
            curAdjBase ws n + u.val * n + col.val ≠ frameParentBase ws n k + m := by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curAdjBase, frameParentBase, frameBase]; omega
        have hne_cost (u col : Fin n) :
            curCostBase ws n + u.val * n + col.val ≠ frameParentBase ws n k + m := by
          have := List.mul_add_lt_sq u.isLt col.isLt
          dsimp only [curCostBase, frameParentBase, frameBase]; omega
        by_cases hmr : m = r.val
        · have hopt_r : optFn r = some r := by simp [optFn]
          simp only [hmr, ↓reduceIte, client_simps]
          rw [hmr] at hne_adj hne_cost
          refine ⟨trivial, ?_, hfr,
            fun u col => (Function.update_of_ne (hne_adj u col) _ _).trans (ha_s u col),
            fun u col => (Function.update_of_ne (hne_cost u col) _ _).trans (hc_s u col),
            fun j hj => ?_⟩
          · rw [show (⟨r.val, _⟩ : Fin n) = r from Fin.ext rfl, hopt_r]
            simp [hfeas, hmr]
          · by_cases hjm : j.val = m
            · obtain rfl : j = r := Fin.ext (hjm.trans hmr)
              simp [hopt_r]
            · rw [Function.update_of_ne (by omega)]
              exact hpar j (by omega)
        · have hvr : vFin ≠ r := fun h => hmr (congrArg Fin.val h)
          have hopt_v : optFn vFin =
              argMinFin n (fun col => a[m][col.val] && col != vFin) (fun col => c[m][col.val]) := by
            simp [optFn, hvr, vFin]
          have harg_s := harg.2.2.2.1
          have harg_r := harg.2.2.2.2
          dsimp only [s1, rowArgs, vFin] at harg_s harg_r
          simp only [hmr, ↓reduceIte, client_simps, harg_s, harg_r]
          rw [show (⟨m, hm⟩ : Fin n) = vFin from rfl, ← hopt_v]
          obtain ⟨-, -, -, hrow_fr, hrow_mod, hrow_a, hrow_c, -⟩ := hrow
          dsimp only [rowArgs, vFin] at hrow_fr hrow_mod hrow_a hrow_c
          cases hopt_case : optFn vFin <;>
            simp only [optFinIdx, Fin.is_lt, lt_irrefl, ↓reduceIte, client_simps,
              Option.isSome_some, Option.isSome_none, Bool.and_true, Bool.and_false] <;>
            refine ⟨trivial, by first | exact hfeas | rfl, hrow_fr.trans hfr,
              fun u col => (Function.update_of_ne (hne_adj u col) _ _).trans (hrow_a u col),
              fun u col => (Function.update_of_ne (hne_cost u col) _ _).trans (hrow_c u col),
              fun j hj => ?_⟩ <;>
            by_cases hjm : j.val = m
          all_goals first
            | (obtain rfl : j = vFin := Fin.ext hjm
               simp [hopt_case, vFin])
            | (rw [Function.update_of_ne (by omega), hrow_mod _ (by
                dsimp only [candPredBase, candCostBase, frameParentBase, frameBase]; omega)]
               exact hpar j (by omega)))
    ⟨0, 1⟩ s₀ ⟨rfl, rfl, rfl, ha, hc, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  obtain ⟨hsafe_it, hvh_it, hmc_it, hfr_it, hmod_it, _, hfeas_it, _, _, _, hpar_it⟩ := h
  unfold selectParentsProg
  refine ⟨⟨h1, hsafe_it⟩, validHistory_bind_step hvh_it (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc_it,
    by simp only [client_simps]; exact hfr_it,
    fun x hx => by simpa [client_simps] using hmod_it x hx,
    ?_, ?_⟩
  · simp only [client_simps]
    rw [hfeas_it, htake]
    unfold selectParents
    have hopts : (Vector.ofFn optFn) =
        (Vector.ofFn fun v : Fin n =>
          if v = r then some r
          else argMinFin n (fun w => a[v.val][w.val] && w != v) (fun w => c[v.val][w.val])) := rfl
    simp [← hopts]
  · intro v
    simp only [client_simps]
    rw [hpar_it v v.isLt]
    simp [selectParents, optFn]

private theorem hasCycleFromProg_spec {w n parentBase : ℕ} (x : Fin n) (f : ParentTable n)
    (s₀ : Memory.State) (h1 : Fits w 1) (hfit_p : Fits w (parentBase + n)) (hfit_n : Fits w n)
    (hp_f : parentBase + n ≤ s₀.frontier)
    (hf_mem : ∀ v : Fin n, s₀.mem (parentBase + v.val) = (f[v.val]).val) :
    iterationSafe hasCycleStep HasCycleStepSafe w ⟨n, parentBase, x.val⟩ n ⟨0, x.val, 0⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (hasCycleFromProg ⟨n, parentBase, x.val⟩)) ∧
      memoryCost (hasCycleFromProg ⟨n, parentBase, x.val⟩) s₀ ≤ n ∧
      (Memory.spec 0).clientState s₀ (hasCycleFromProg ⟨n, parentBase, x.val⟩) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (hasCycleFromProg ⟨n, parentBase, x.val⟩) =
        (if hasCycleFrom x f then 1 else 0) := by
  have h := iterate_spec hasCycleStep HasCycleStepSafe w ⟨n, parentBase, x.val⟩ 1 n
    (fun m st s =>
      let curFin := (fun i : Fin n => f[i.val])^[m] x
      let hitBool := (List.range m).any fun k => (fun i : Fin n => f[i.val])^[k + 1] x == x
      st.step = m ∧ st.cur = curFin.val ∧ st.hit = (if hitBool then 1 else 0) ∧ s = s₀)
    (fun _ => False)
    (fun m hm st s ⟨hst, hcur, hhit, hs⟩ => by
      rcases st with ⟨step, cur, hit⟩
      dsimp only at hst hcur hhit
      subst step s
      set curFin : Fin n := (fun i : Fin n => f[i.val])^[m] x
      have hcur_lt : cur < n := hcur ▸ curFin.isLt
      have hmem_cur : s₀.mem (parentBase + cur) = (f[curFin.val]).val := by
        rw [hcur]
        exact hf_mem curFin
      have hst : (Memory.spec 0).clientState s₀
          (hasCycleStep (⟨n, parentBase, x.val⟩, ⟨m, cur, hit⟩)) = s₀ := by
        unfold hasCycleStep
        dsimp only
        rw [clientState_bind_read]
        split_ifs <;> rfl
      refine ⟨by dsimp only [HasCycleStepSafe]; exact ⟨h1, hfit_p.of_le (by omega),
          hfit_n.of_le (by omega)⟩,
        ?_, ?_, by rw [hst], fun _ _ => by rw [hst], ?_⟩
      · unfold hasCycleStep
        dsimp only
        exact validHistory_read_bind (by omega) (by split_ifs <;> trivial)
      · unfold hasCycleStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read]
        split_ifs <;> simp [client_simps]
      · unfold hasCycleStep
        dsimp only
        simp only [client_simps, hmem_cur, List.range_succ, List.any_append, List.any_cons,
          List.any_nil, Bool.or_false]
        generalize
          ((List.range m).any fun k => (fun i : Fin n => f[i.val])^[k + 1] x == x) = prev at hhit ⊢
        simp only [Function.iterate_succ_apply']
        subst hhit
        cases prev
        · by_cases heq : f[curFin.val] = x
          · simp [heq, curFin, client_simps]
          · have hval : (f[curFin.val]).val ≠ x.val := fun h => heq (Fin.ext h)
            simp [heq, hval, curFin, client_simps]
        · simp [curFin, client_simps])
    ⟨0, x.val, 0⟩ s₀ ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hsafe, hvh, hmc, _, _, _, _, hhit_n, hs_n⟩ := h
  unfold hasCycleFromProg
  refine ⟨hsafe, validHistory_bind_step hvh (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc,
    by simp [client_simps, hs_n],
    ?_⟩
  simp only [client_simps]
  exact hhit_n.trans (by rw [hasCycleFrom_eq])

public theorem findCycleProg_spec {w n parentBase : ℕ} (r : Fin n) (f : ParentTable n)
    (s₀ : Memory.State) (h1 : Fits w 1) (hfit_p : Fits w (parentBase + n)) (hfit_n : Fits w n)
    (hf0 : 0 < s₀.frontier) (hp_f : parentBase + n ≤ s₀.frontier)
    (hf_mem : ∀ v : Fin n, s₀.mem (parentBase + v.val) = (f[v.val]).val) :
    iterationSafe findCycleOuterStep FindCycleOuterStepSafe w ⟨n, r.val, parentBase⟩ n ⟨0, n⟩ s₀ ∧
      (Memory.spec w).ValidHistory s₀
        ((Memory.spec w).clientHistory s₀ (findCycleProg ⟨n, r.val, parentBase⟩)) ∧
      memoryCost (findCycleProg ⟨n, r.val, parentBase⟩) s₀ ≤ (n + 1) * n ∧
      (Memory.spec 0).clientState s₀ (findCycleProg ⟨n, r.val, parentBase⟩) = s₀ ∧
      (Memory.spec 0).clientResult s₀ (findCycleProg ⟨n, r.val, parentBase⟩) =
        optFinIdx (findCycleTable r f) := by
  let stepFn := fun (acc : Option (Fin n)) (x : Fin n) =>
    match acc with
    | some x0 => some x0
    | none => if x == r then none else if hasCycleFrom x f then some x else none
  have h := iterate_spec findCycleOuterStep FindCycleOuterStepSafe w ⟨n, r.val, parentBase⟩
    (n + 1) n
    (fun m st s =>
      let acc := ((List.finRange n).take m).foldl stepFn none
      st.v = m ∧ st.found = optFinIdx acc ∧ s = s₀)
    (fun _ => False)
    (fun m hm st s ⟨hv, hfd, hs⟩ => by
      rcases st with ⟨vIdx, foundIdx⟩
      dsimp only at hv hfd
      subst vIdx s
      set vFin : Fin n := ⟨m, hm⟩
      have hcyc := hasCycleFromProg_spec vFin f s₀ h1 hfit_p hfit_n hp_f hf_mem
      have hc_s : ((Memory.spec 0).runClient s₀
          (hasCycleFromProg ⟨n, parentBase, m⟩)).2.1 = s₀ := hcyc.2.2.2.1
      have hst : (Memory.spec 0).clientState s₀
          (findCycleOuterStep (⟨n, r.val, parentBase⟩, ⟨m, foundIdx⟩)) = s₀ := by
        unfold findCycleOuterStep
        dsimp only
        simp only [client_simps]
        repeat (split_ifs <;> simp only [client_simps, hc_s])
      refine ⟨by dsimp only [FindCycleOuterStepSafe]; exact ⟨h1, hfit_n.of_le (by omega), hcyc.1⟩,
        ?_, ?_, by rw [hst], fun _ _ => by rw [hst], ?_⟩
      · unfold findCycleOuterStep
        refine validHistory_read_bind hf0 ?_
        dsimp only
        split_ifs
        · exact validHistory_pure w _ _
        · exact validHistory_pure w _ _
        · refine validHistory_bind_step hcyc.2.1 ?_
          rw [hcyc.2.2.2.1]
          split_ifs <;> exact validHistory_pure w _ _
      · unfold findCycleOuterStep
        dsimp only
        rw [memoryCost_bind', memoryCost_read, clientState_read]
        split_ifs
        · simp only [client_simps]; omega
        · simp only [client_simps]; omega
        · rw [memoryCost_bind', hcyc.2.2.2.1]
          have hc_le : memoryCost (hasCycleFromProg ⟨n, parentBase, m⟩) s₀ ≤ n := hcyc.2.2.1
          split_ifs <;> simp only [client_simps] <;> omega
      · rw [foldl_take_finRange_succ hm stepFn none]
        generalize hacc : ((List.finRange n).take m).foldl stepFn none = acc at hfd ⊢
        dsimp only [stepFn]
        unfold findCycleOuterStep
        dsimp only
        simp only [client_simps]
        cases acc with
        | some x0 =>
          have hflt : foundIdx < n := by rw [hfd]; exact x0.isLt
          simp only [hflt, ↓reduceIte, client_simps, optFinIdx]
          exact ⟨trivial, hfd, trivial⟩
        | none =>
          have hfn : ¬(foundIdx < n) := by rw [hfd, optFinIdx]; omega
          simp only [hfn, ↓reduceIte]
          by_cases hmr : m = r.val
          · have hvr : ((⟨r.val, hmr ▸ hm⟩ : Fin n) == r) = true := beq_iff_eq.mpr (Fin.ext rfl)
            simp only [hmr, hvr, ↓reduceIte, client_simps, optFinIdx]
            exact ⟨trivial, trivial, trivial⟩
          · have hvr : (⟨m, hm⟩ == r) = false :=
              beq_false_of_ne (fun h => hmr (congrArg Fin.val h))
            have hc_r : (Memory.spec 0).clientResult s₀ (hasCycleFromProg ⟨n, parentBase, m⟩) =
                if hasCycleFrom ⟨m, hm⟩ f then 1 else 0 := hcyc.2.2.2.2
            simp only [hmr, hvr, Bool.false_eq_true, ↓reduceIte, hc_r]
            cases hh : hasCycleFrom ⟨m, hm⟩ f
            · simp only [Bool.false_eq_true, Nat.zero_ne_one, ↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, by split_ifs <;> exact hc_s⟩
            · simp only [↓reduceIte, client_simps, optFinIdx]
              exact ⟨trivial, trivial, by split_ifs <;> exact hc_s⟩)
    ⟨0, n⟩ s₀ ⟨rfl, rfl, rfl⟩
  have htake : (List.finRange n).take n = List.finRange n := List.take_of_length_le (by simp)
  obtain ⟨hsafe, hvh, hmc, _, _, _, hfd_n, hs_n⟩ := h
  unfold findCycleProg
  refine ⟨hsafe, validHistory_bind_step hvh (validHistory_pure w _ _),
    by rw [memoryCost_bind']; simpa [client_simps] using hmc,
    by simp [client_simps, hs_n],
    ?_⟩
  simp only [client_simps]
  exact hfd_n.trans (by rw [htake]; rfl)

public theorem cycleMaskProg_spec {w n parentBase maskBase : ℕ} (f : ParentTable n)
    (x0 : Fin n) (s₀ : Memory.State)
    (h1 : Fits w 1) (hfit_p : Fits w (parentBase + n)) (hfit_m : Fits w (maskBase + n))
    (hfit_n : Fits w n) (hp_f : parentBase + n ≤ s₀.frontier) (hm_f : maskBase + n ≤ s₀.frontier)
    (hdisj : parentBase + n ≤ maskBase ∨ maskBase + n ≤ parentBase)
    (hf_mem : ∀ v : Fin n, s₀.mem (parentBase + v.val) = (f[v.val]).val) :
    let cm : CycleMaskArgs := ⟨n, parentBase, maskBase, x0.val⟩
    let s0z := (Memory.spec 0).clientState s₀ (zeroWordsProg ⟨maskBase, n⟩)
    let s' := (Memory.spec 0).clientState s₀ (cycleMaskProg cm)
    (iterationSafe zeroStep ZeroStepSafe w ⟨maskBase, n⟩ n 0 s₀ ∧
      iterationSafe cycleMaskStep CycleMaskStepSafe w cm n ⟨0, x0.val⟩ s0z) ∧
      (Memory.spec w).ValidHistory s₀ ((Memory.spec w).clientHistory s₀ (cycleMaskProg cm)) ∧
      memoryCost (cycleMaskProg cm) s₀ ≤ 3 * n ∧
      s'.frontier = s₀.frontier ∧
      (∀ addr, ¬(maskBase ≤ addr ∧ addr < maskBase + n) → s'.mem addr = s₀.mem addr) ∧
      (∀ y : Fin n, s'.mem (maskBase + y.val) = if (cycleMask f x0)[y.val] then 1 else 0) := by
  let cm : CycleMaskArgs := ⟨n, parentBase, maskBase, x0.val⟩
  have hzero := zeroWordsProg_spec ⟨maskBase, n⟩ s₀ hm_f hfit_m hfit_n
  set s0z := (Memory.spec 0).clientState s₀ (zeroWordsProg ⟨maskBase, n⟩)
  have hf_mem_z : ∀ v : Fin n, s0z.mem (parentBase + v.val) = (f[v.val]).val := by
    intro v
    rw [hzero.2.2.2.2.1 _ (by dsimp only; have := v.isLt; omega)]
    exact hf_mem v
  have hloop := iterate_spec cycleMaskStep CycleMaskStepSafe w cm 2 n
    (fun m st s =>
      st.step = m ∧ st.cur = ((fun i : Fin n => f[i.val])^[m] x0).val ∧
        s.frontier = s0z.frontier ∧
        (∀ v : Fin n, s.mem (parentBase + v.val) = (f[v.val]).val) ∧
        (∀ y : Fin n, s.mem (maskBase + y.val) =
          if ∃ j < m, (fun i : Fin n => f[i.val])^[j] x0 = y then 1 else 0))
    (fun addr => maskBase ≤ addr ∧ addr < maskBase + n)
    (fun m hm st s ⟨hst, hcur, hfr, hpar_s, hmask_s⟩ => by
      rcases st with ⟨step, cur⟩
      dsimp only at hst hcur
      subst step
      set curFin : Fin n := (fun i : Fin n => f[i.val])^[m] x0
      have hcur_lt : cur < n := hcur ▸ curFin.isLt
      have hmem_cur : s.mem (parentBase + cur) = (f[curFin.val]).val := by
        rw [hcur]
        exact hpar_s curFin
      refine ⟨by dsimp only [CycleMaskStepSafe, cm]; exact ⟨h1, hfit_p.of_le (by omega),
          hfit_m.of_le (by omega), hfit_n.of_le (by omega)⟩,
        ?_, ?_, ?_, ?_, ?_⟩
      · unfold cycleMaskStep
        dsimp only [cm]
        exact validHistory_read_bind (by rw [hfr, hzero.2.2.2.1]; omega)
          (validHistory_write_bind (by rw [hfr, hzero.2.2.2.1]; omega) h1
            (validHistory_pure w _ _))
      · unfold cycleMaskStep
        dsimp only [cm]
        rw [memoryCost_bind', memoryCost_read, memoryCost_bind', memoryCost_write]
        simp [client_simps]
      · simp [cycleMaskStep, cm, client_simps]
      · intro addr haddr
        simp only [cycleMaskStep, cm, client_simps]
        exact Function.update_of_ne (by omega) _ _
      · simp only [cycleMaskStep, cm, client_simps, hmem_cur, Function.iterate_succ_apply']
        refine ⟨trivial, rfl, hfr, ?_, ?_⟩
        · intro v
          rw [Function.update_of_ne (by have := v.isLt; omega)]
          exact hpar_s v
        · intro y
          by_cases hcy : y.val = cur
          · have hy_eq : (fun i : Fin n => f[i.val])^[m] x0 = y :=
              Fin.ext (hcur.symm.trans hcy.symm)
            have hex : ∃ j < m + 1, (fun i : Fin n => f[i.val])^[j] x0 = y :=
              ⟨m, Nat.lt_succ_self m, hy_eq⟩
            rw [hcy, Function.update_self, ite_eq_left hex]
          · rw [Function.update_of_ne (by omega), hmask_s y]
            have hiff : (∃ j < m + 1, (fun i : Fin n => f[i.val])^[j] x0 = y) ↔
                (∃ j < m, (fun i : Fin n => f[i.val])^[j] x0 = y) := by
              refine ⟨?_, fun ⟨j, hj, h⟩ => ⟨j, Nat.lt_succ_of_lt hj, h⟩⟩
              rintro ⟨j, hj, h⟩
              rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hj) with hlt | rfl
              · exact ⟨j, hlt, h⟩
              · exact absurd (hcur.trans (congrArg Fin.val h)).symm hcy
            rw [if_congr hiff rfl rfl])
    ⟨0, x0.val⟩ s0z
    ⟨rfl, rfl, rfl, hf_mem_z, fun y => by
      simp [hzero.2.2.2.2.2 y.val y.isLt]⟩
  unfold cycleMaskProg cycleMaskLoopProg
  refine ⟨⟨hzero.1, hloop.1⟩,
    validHistory_bind_step hzero.2.1
      (validHistory_bind_step hloop.2.1 (validHistory_pure w _ _)),
    by
      rw [memoryCost_bind', memoryCost_bind']
      have hz_c := hzero.2.2.1
      have hl_c := hloop.2.2.1
      dsimp only [cm, s0z] at hz_c hl_c ⊢
      simp only [client_simps] at hz_c hl_c ⊢
      omega,
    by
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      simp only [client_simps]
      exact hloop.2.2.2.1.trans hzero.2.2.2.1,
    fun addr haddr => by
      rw [StateTransitionSpec.clientState_bind, StateTransitionSpec.clientState_bind]
      simp only [client_simps]
      exact (hloop.2.2.2.2.1 addr haddr).trans (hzero.2.2.2.2.1 addr haddr),
    fun y => by
      obtain ⟨_, _, _, _, _, _, _, _, _, hmask_n⟩ := hloop
      simp only [client_simps]
      rw [hmask_n y]
      by_cases hcy : (cycleMask f x0)[y.val] = true
      · simp [hcy, (getElem_cycleMask f x0 y).mp hcy]
      · have hnot : ¬∃ j < n, (fun i : Fin n => f[i.val])^[j] x0 = y :=
          mt (getElem_cycleMask f x0 y).mpr hcy
        simp [hcy, hnot]⟩

end Cslib.Algorithms.WordRAM.Arborescence.Internal
