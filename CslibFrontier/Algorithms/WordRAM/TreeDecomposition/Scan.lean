/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.TreeDecomposition.BagMask
public import CslibFrontier.Computability.WordRAM.ListArray
public import CslibFrontier.Computability.WordRAM.Realization.ProgFrame
public import CslibFrontier.Computability.WordRAM.Realization.WordEncoding.Equiv
import CslibFrontier.Computability.WordRAM.InputArray
import CslibFrontier.Computability.WordRAM.Realization.Program.Standard
import CslibFrontier.Tactic.Realize

/-!
# Shared memory-block and bag-scan primitives for tree-decomposition algorithms

This module provides monotone memory-block framing (`PreservesBelow`, `HoldsIn`) and certified
`Memory.Prog` routines shared by the Word-RAM dynamic programs over tree decompositions
(`CslibFrontier.Algorithms.WordRAM.TreeDecomposition.IndependentSet` and
`CslibFrontier.Algorithms.WordRAM.TreeDecomposition.CSP`):

* `powProg`: bounded-word exponentiation `base ^ exp` in `exp` loop steps;
* `bagMemProg`: linear membership scan of a materialized bag list (`memBag`).

## Main definitions

* `Cslib.Algorithms.WordRAM.TreeDecomposition.PreservesBelow`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.HoldsIn`
* `Cslib.Algorithms.WordRAM.TreeDecomposition.powProg`
* `Cslib.Algorithms.WordRAM.TreeDecomposition.bagMemProg`

## Main results

* `Cslib.Algorithms.WordRAM.TreeDecomposition.holdsIn_alloc_zero`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.holdsIn_set`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.holdsIn_append_one`: block representation rules for
  zero-allocation and indexed writes.
* `Cslib.Algorithms.WordRAM.TreeDecomposition.powProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.powProg_realizes`
* `Cslib.Algorithms.WordRAM.TreeDecomposition.bagMemProg_spec`,
  `Cslib.Algorithms.WordRAM.TreeDecomposition.bagMemProg_realizes`
-/

public section

namespace Cslib.Algorithms.WordRAM.TreeDecomposition

open Cslib.Algorithms.Lean.TreeDecomposition
open Cslib.DataStructure
open Cslib.WordRAM
open Cslib.WordRAM.Realization

/-! ### Monotone memory preservation and materialized list blocks -/

/-- `s₁` extends `s₀`'s frontier monotonically while keeping every cell below `F` unchanged. -/
@[expose] def PreservesBelow (F : ℕ) (s₀ s₁ : Memory.State) : Prop :=
  F ≤ s₀.frontier ∧ s₀.frontier ≤ s₁.frontier ∧ ∀ a < F, s₁.mem a = s₀.mem a

theorem PreservesBelow.refl {F : ℕ} {s : Memory.State} (hF : F ≤ s.frontier) :
    PreservesBelow F s s :=
  ⟨hF, le_rfl, fun _ _ => rfl⟩

theorem PreservesBelow.mono_bound {F₁ F₂ : ℕ} {s₀ s₁ : Memory.State}
    (h : PreservesBelow F₂ s₀ s₁) (hle : F₁ ≤ F₂) : PreservesBelow F₁ s₀ s₁ :=
  ⟨hle.trans h.1, h.2.1, fun a ha => h.2.2 a (lt_of_lt_of_le ha hle)⟩

theorem PreservesBelow.trans {F : ℕ} {s₀ s₁ s₂ : Memory.State}
    (h₁ : PreservesBelow F s₀ s₁) (h₂ : PreservesBelow F s₁ s₂) :
    PreservesBelow F s₀ s₂ :=
  ⟨h₁.1, h₁.2.1.trans h₂.2.1, fun a ha => (h₂.2.2 a ha).trans (h₁.2.2 a ha)⟩

theorem preservesBelow_write {F a v : ℕ} {s : Memory.State}
    (hF : F ≤ a) (ha : a < s.frontier) :
    PreservesBelow F s ⟨Function.update s.mem a v, s.frontier⟩ :=
  ⟨by omega, le_rfl, fun x hx => Function.update_of_ne (by omega) v s.mem⟩

theorem preservesBelow_alloc (s : Memory.State) (k : ℕ) :
    PreservesBelow s.frontier s ((Memory.spec 0).clientState s (Memory.alloc k)) := by
  refine ⟨le_rfl, Nat.le_add_right _ _, fun a ha => ?_⟩
  change clear s.mem s.frontier k a = s.mem a
  exact clear_of_not_owns (by dsimp only [Block.Owns]; omega)

theorem preservesBelow_allocDirty (s : Memory.State) (k : ℕ) :
    PreservesBelow s.frontier s ((Memory.spec 0).clientState s (Memory.allocDirty k)) :=
  ⟨le_rfl, Nat.le_add_right _ _, fun _ _ => rfl⟩

/-- `xs` is stored contiguously starting at `base` within `s`'s allocated frontier. -/
@[expose] def HoldsIn (base : ℕ) (xs : List ℕ) (s : Memory.State) : Prop :=
  base + xs.length ≤ s.frontier ∧ Block.HoldsList base xs s.mem

theorem HoldsIn.mono {base : ℕ} {xs : List ℕ} {F : ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀) (hF : base + xs.length ≤ F) (hp : PreservesBelow F s₀ s₁) :
    HoldsIn base xs s₁ :=
  ⟨h.1.trans hp.2.1, h.2.frame (fun a _ ha => hp.2.2 a (lt_of_lt_of_le ha hF))⟩

theorem HoldsIn.mono_frontier {base : ℕ} {xs : List ℕ} {s₀ s₁ : Memory.State}
    (h : HoldsIn base xs s₀) (hp : PreservesBelow s₀.frontier s₀ s₁) :
    HoldsIn base xs s₁ :=
  h.mono h.1 hp

theorem HoldsIn.get {base : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (i : ℕ) (hi : i < xs.length) :
    s.mem (base + i) = xs[i] :=
  h.2.get i hi

theorem HoldsIn.nil {base : ℕ} {s : Memory.State} (h : base ≤ s.frontier) :
    HoldsIn base [] s :=
  ⟨by simpa only [List.length_nil, Nat.add_zero] using h, Block.holdsList_nil base s.mem⟩

theorem HoldsIn.cons_iff {base a : ℕ} {xs : List ℕ} {s : Memory.State} :
    HoldsIn base (a :: xs) s ↔
      base + 1 + xs.length ≤ s.frontier ∧ s.mem base = a ∧ HoldsIn (base + 1) xs s := by
  simp only [HoldsIn, List.length_cons, Block.holdsList_cons_iff]
  exact ⟨fun ⟨hb, hm, hr⟩ => ⟨by omega, hm, ⟨by omega, hr⟩⟩,
    fun ⟨hb, hm, ⟨_, hr⟩⟩ => ⟨by omega, hm, hr⟩⟩

theorem HoldsIn.append_iff {base : ℕ} {xs ys : List ℕ} {s : Memory.State} :
    HoldsIn base (xs ++ ys) s ↔
      HoldsIn base xs s ∧ HoldsIn (base + xs.length) ys s := by
  simp only [HoldsIn, List.length_append, Block.holdsList_append_iff]
  exact ⟨fun ⟨hb, hx, hy⟩ => ⟨⟨by omega, hx⟩, ⟨by omega, hy⟩⟩,
    fun ⟨⟨_, hx⟩, ⟨hby, hy⟩⟩ => ⟨by omega, hx, hy⟩⟩

theorem HoldsIn.drop {base : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (k : ℕ) (hk : k ≤ xs.length) :
    HoldsIn (base + k) (xs.drop k) s := by
  have hsplit : xs = xs.take k ++ xs.drop k := (List.take_append_drop k xs).symm
  rw [hsplit, HoldsIn.append_iff] at h
  have hh := h.2
  rwa [List.length_take_of_le hk] at hh

theorem holdsIn_init (words : List ℕ) : HoldsIn 1 words (Memory.State.init words) := by
  refine ⟨by simp [Memory.State.init, Nat.add_comm], fun i => ?_⟩
  have h := Data.init_realizes_append (r := 0) [] words [] i
  simpa [Memory.State.init] using h

theorem holdsIn_alloc_zero (s : Memory.State) (k : ℕ) :
    HoldsIn s.frontier (List.replicate k 0) ((Memory.spec 0).clientState s (Memory.alloc k)) := by
  change HoldsIn s.frontier (List.replicate k 0) ⟨clear s.mem s.frontier k, s.frontier + k⟩
  refine ⟨by simp, fun i => ?_⟩
  have hi : i.val < k := by simpa only [List.length_replicate] using i.isLt
  change clear s.mem s.frontier k (s.frontier + i.val) = (List.replicate k 0)[i.val]
  rw [List.getElem_replicate]
  exact Block.realizes_clear s.mem s.frontier k ⟨i.val, hi⟩

theorem holdsIn_set {base idx v : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) :
    HoldsIn base (xs.set idx v) ⟨Function.update s.mem (base + idx) v, s.frontier⟩ := by
  refine ⟨by simpa only [List.length_set] using h.1, fun i => ?_⟩
  have hi : i.val < xs.length := by simpa only [List.length_set] using i.isLt
  change Function.update s.mem (base + idx) v (base + i.val) = (xs.set idx v)[i.val]
  by_cases heq : i.val = idx
  · simp only [heq, Function.update_self, List.getElem_set_self]
  · rw [Function.update_of_ne (by omega), List.getElem_set_ne (Ne.symm heq)]
    exact h.get i.val hi

theorem holdsIn_write_outside {base a v : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (hout : a < base ∨ base + xs.length ≤ a) :
    HoldsIn base xs ⟨Function.update s.mem a v, s.frontier⟩ :=
  ⟨h.1, h.2.frame (fun _ _ _ => Function.update_of_ne (by omega) v s.mem)⟩

theorem holdsIn_append_one {base v : ℕ} {xs : List ℕ} {s : Memory.State}
    (h : HoldsIn base xs s) (hbound : base + xs.length + 1 ≤ s.frontier) :
    HoldsIn base (xs ++ [v]) ⟨Function.update s.mem (base + xs.length) v, s.frontier⟩ :=
  ⟨by simp only [List.length_append, List.length_singleton]; omega, h.2.append_one v⟩

/-! ### Bounded-word exponentiation (`powProg`) -/

/-- Arguments `(base, exp)` for `powProg`. -/
structure PowArgs where
  /-- Base word. -/
  base : ℕ
  /-- Exponent count. -/
  exp : ℕ

/-- Register tuple equivalence for `PowArgs`. -/
@[expose] def PowArgs.equiv : PowArgs ≃ ℕ × ℕ where
  toFun a := (a.base, a.exp)
  invFun := fun (base, exp) => ⟨base, exp⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding PowArgs := .ofEquiv PowArgs.equiv

private def powStep (env : ℕ × ℕ) : Memory.Prog ℕ := do
  let _ ← Memory.read 0
  pure (env.2 * env.1)

/-- Compute `args.base ^ args.exp` by repeated multiplication. -/
def powProg (args : PowArgs) : Memory.Prog ℕ :=
  iterate powStep args.base args.exp 1

theorem powProg_state (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (powProg args) = s := by
  unfold powProg
  exact clientState_iterate_eq_of powStep args.base (fun _ _ => rfl) args.exp 1 s

theorem powProg_result (args : PowArgs) (s : Memory.State) :
    (Memory.spec 0).clientResult s (powProg args) = args.base ^ args.exp := by
  unfold powProg
  suffices ∀ k acc,
      (Memory.spec 0).clientResult s (iterate powStep args.base k acc) = acc * args.base ^ k by
    simpa only [Nat.one_mul] using this args.exp 1
  intro k
  induction k with
  | zero =>
    intro acc
    have h0 : iterate powStep args.base 0 acc = pure acc := rfl
    rw [h0]
    simp only [Nat.pow_zero, Nat.mul_one]
    rfl
  | succ k ih =>
    intro acc
    change (Memory.spec 0).clientResult s
      (powStep (args.base, acc) >>= iterate powStep args.base k) = acc * args.base ^ (k + 1)
    rw [StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s
      (iterate powStep args.base k (acc * args.base)) = acc * args.base ^ (k + 1)
    rw [ih (acc * args.base), Nat.pow_succ, Nat.mul_comm (args.base ^ k), ← Nat.mul_assoc]

theorem powProg_spec {w : ℕ} (args : PowArgs) {s : Memory.State} (hs : 0 < s.frontier) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (powProg args)) ∧
    (Memory.spec 0).clientState s (powProg args) = s ∧
    (Memory.spec 0).clientResult s (powProg args) = args.base ^ args.exp ∧
    memoryCost (powProg args) s ≤ args.exp := by
  have hcost : memoryCost (powProg args) s ≤ args.exp := by
    unfold powProg
    simpa only [Nat.one_mul] using
      memoryCost_iterate_le_of powStep 1 args.base (fun _ _ => le_rfl) args.exp 1 s
  suffices ∀ k acc,
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s (iterate powStep args.base k acc)) ∧
      (Memory.spec 0).clientResult s (iterate powStep args.base k acc) =
        acc * args.base ^ k by
    obtain ⟨hv, hr⟩ := this args.exp 1
    refine ⟨?_, powProg_state args s, ?_, hcost⟩
    · unfold powProg; exact hv
    · unfold powProg; simpa only [Nat.one_mul] using hr
  intro k
  induction k with
  | zero =>
    intro acc
    have h0 : iterate powStep args.base 0 acc = pure acc := rfl
    rw [h0]
    exact ⟨validHistory_pure w s acc, by simp only [Nat.pow_zero, Nat.mul_one]; rfl⟩
  | succ k ih =>
    intro acc
    change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (powStep (args.base, acc) >>= iterate powStep args.base k)) ∧
      (Memory.spec 0).clientResult s
        (powStep (args.base, acc) >>= iterate powStep args.base k) =
        acc * args.base ^ (k + 1)
    obtain ⟨hv_k, hr_k⟩ := ih (acc * args.base)
    refine ⟨validHistory_bind_step (validHistory_read_bind hs (validHistory_pure w s _)) hv_k, ?_⟩
    rw [StateTransitionSpec.clientResult_bind]
    change (Memory.spec 0).clientResult s
      (iterate powStep args.base k (acc * args.base)) = acc * args.base ^ (k + 1)
    rw [hr_k, Nat.pow_succ, Nat.mul_comm (args.base ^ k), ← Nat.mul_assoc]

theorem powProg_realizes :
    Realizes .exact powProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.base ^ args.exp))
      (fun _ _ => 0) := by
  unfold powProg
  realize
  · exact h.1
  · obtain ⟨h1, hpow⟩ := h
    refine iterationSafe_of_stepInv _ _ w _
      (fun (j : ℕ) (acc : ℕ) (_ : Memory.State) =>
        j ≤ d.exp ∧ acc = d.base ^ (d.exp - j) ∧ Fits w acc)
      (fun j acc _ ⟨hj_le, hacc, _⟩ => ?_)
      ⟨le_rfl, by simp only [Nat.sub_self, Nat.pow_zero], h1⟩
    dsimp only [powStep]
    have hexp_step : d.exp - j = (d.exp - (j + 1)) + 1 := by omega
    have hprod : acc * d.base = d.base ^ (d.exp - j) := by
      rw [hacc, hexp_step, Nat.pow_succ]
    have hfit_next : Fits w (acc * d.base) := by
      rw [hprod]
      rcases Nat.eq_zero_or_pos d.base with hb0 | hb_pos
      · rw [hb0, zero_pow (by omega)]
        exact fits_zero w
      · exact hpow.of_le (Nat.pow_le_pow_right hb_pos (Nat.sub_le _ _))
    exact ⟨hfit_next, Nat.le_of_succ_le hj_le, hprod, hfit_next⟩

/-! ### Linear bag membership scan (`bagMemProg`) -/

private structure BagScanState where
  cur : ℕ
  found : ℕ

private def BagScanState.equiv : BagScanState ≃ ℕ × ℕ where
  toFun s := (s.cur, s.found)
  invFun := fun (cur, found) => ⟨cur, found⟩
  left_inv _ := rfl
  right_inv _ := rfl

private instance : WordEncoding BagScanState := .ofEquiv BagScanState.equiv

/-- Arguments `(target, base, len)` for `bagMemProg`. -/
structure BagScanArgs where
  /-- Element sought. -/
  target : ℕ
  /-- Base address of the bag list in memory. -/
  base : ℕ
  /-- Length of the bag list. -/
  len : ℕ

/-- Register tuple equivalence for `BagScanArgs`. -/
@[expose] def BagScanArgs.equiv : BagScanArgs ≃ (ℕ × ℕ) × ℕ where
  toFun a := ((a.target, a.base), a.len)
  invFun := fun ((target, base), len) => ⟨target, base, len⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : WordEncoding BagScanArgs := .ofEquiv BagScanArgs.equiv

private def bagMemStep (env : ℕ × BagScanState) : Memory.Prog BagScanState := do
  let v ← Memory.read env.2.cur
  pure ⟨env.2.cur + 1, if v = env.1 then 1 else env.2.found⟩

/-- Return `1` if `args.target` occurs in the `args.len`-word slice at `args.base`, else `0`. -/
def bagMemProg (args : BagScanArgs) : Memory.Prog ℕ := do
  let res ← iterate bagMemStep args.target args.len ⟨args.base, 0⟩
  pure res.found

theorem bagMemProg_state (args : BagScanArgs) (s : Memory.State) :
    (Memory.spec 0).clientState s (bagMemProg args) = s := by
  unfold bagMemProg
  rw [StateTransitionSpec.clientState_bind]
  exact clientState_iterate_eq_of bagMemStep args.target (fun _ _ => rfl) args.len ⟨args.base, 0⟩ s

theorem bagMemProg_spec {w : ℕ} (args : BagScanArgs) {xs : List ℕ} {s : Memory.State}
    (hxs : HoldsIn args.base xs s) (hlen : xs.length = args.len) :
    (Memory.spec w).ValidHistory s ((Memory.spec w).clientHistory s (bagMemProg args)) ∧
    (Memory.spec 0).clientState s (bagMemProg args) = s ∧
    (Memory.spec 0).clientResult s (bagMemProg args) =
      (if memBag args.target xs then 1 else 0) ∧
    memoryCost (bagMemProg args) s ≤ args.len := by
  have hcost : memoryCost (bagMemProg args) s ≤ args.len := by
    unfold bagMemProg
    rw [memoryCost_bind', memoryCost_pure, Nat.add_zero]
    simpa only [Nat.one_mul] using
      memoryCost_iterate_le_of bagMemStep 1 args.target (fun _ _ => le_rfl)
        args.len ⟨args.base, 0⟩ s
  suffices ∀ ys cur, HoldsIn cur ys s → ∀ found, (found = 0 ∨ found = 1) →
      (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate bagMemStep args.target ys.length ⟨cur, found⟩)) ∧
      ((Memory.spec 0).clientResult s
        (iterate bagMemStep args.target ys.length ⟨cur, found⟩)).found =
        if found = 1 ∨ memBag args.target ys = true then 1 else 0 by
    have hrun := this xs args.base hxs 0 (.inl rfl)
    rw [hlen] at hrun
    refine ⟨?_, bagMemProg_state args s, ?_, hcost⟩
    · unfold bagMemProg
      exact validHistory_bind_step hrun.1 (validHistory_pure w _ _)
    · unfold bagMemProg
      rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate bagMemStep args.target args.len ⟨args.base, 0⟩)).found = _
      rw [hrun.2]
      cases memBag args.target xs <;> rfl
  intro ys
  induction ys with
  | nil =>
    intro cur _ found hfd
    have h0 : iterate bagMemStep args.target 0 ⟨cur, found⟩ = pure ⟨cur, found⟩ := rfl
    simp only [List.length_nil, h0, memBag]
    refine ⟨validHistory_pure w s _, ?_⟩
    rcases hfd with rfl | rfl <;> rfl
  | cons u rest ih =>
    intro cur hcur found hfd
    rw [HoldsIn.cons_iff] at hcur
    obtain ⟨hb, hmem_u, hrest⟩ := hcur
    have hlt : cur < s.frontier := by omega
    let found' := if u = args.target then 1 else found
    have hfd' : found' = 0 ∨ found' = 1 := by
      dsimp only [found']
      split_ifs
      · exact .inr rfl
      · exact hfd
    obtain ⟨hv_rest, hr_rest⟩ := ih (cur + 1) hrest found' hfd'
    simp only [List.length_cons]
    change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (bagMemStep (args.target, ⟨cur, found⟩) >>= iterate bagMemStep args.target rest.length)) ∧
      ((Memory.spec 0).clientResult s
        (bagMemStep (args.target, ⟨cur, found⟩) >>=
          iterate bagMemStep args.target rest.length)).found = _
    have hstep_res : (Memory.spec 0).clientResult s (bagMemStep (args.target, ⟨cur, found⟩)) =
        ⟨cur + 1, found'⟩ := by
      dsimp only [bagMemStep, found']
      change (⟨cur + 1, if s.mem cur = args.target then 1 else found⟩ : BagScanState) = _
      rw [hmem_u]
    refine ⟨validHistory_bind_step (validHistory_read_bind hlt (validHistory_pure w s _)) ?_, ?_⟩
    · change (Memory.spec w).ValidHistory s
        ((Memory.spec w).clientHistory s
          (iterate bagMemStep args.target rest.length
            ((Memory.spec 0).clientResult s (bagMemStep (args.target, ⟨cur, found⟩)))))
      rwa [hstep_res]
    · rw [StateTransitionSpec.clientResult_bind]
      change ((Memory.spec 0).clientResult s
        (iterate bagMemStep args.target rest.length
          ((Memory.spec 0).clientResult s (bagMemStep (args.target, ⟨cur, found⟩))))).found = _
      rw [hstep_res, hr_rest]
      dsimp only [found', memBag]
      by_cases heq : args.target = u
      · subst heq
        simp
      · have hne : u ≠ args.target := Ne.symm heq
        simp [heq, hne]

theorem bagMemProg_realizes :
    Realizes .exact bagMemProg WordEncoding.encode WordEncoding.encode
      (fun w args _ => Fits w 1 ∧ Fits w (args.base + args.len))
      (fun _ _ => 0) := by
  unfold bagMemProg
  realize
  obtain ⟨h1, hfit⟩ := h
  refine iterationSafe_of_stepInv _ _ w _
    (fun (j : ℕ) (st : BagScanState) (_ : Memory.State) =>
      st.cur + j = d.base + d.len ∧ st.found ≤ 1)
    (fun j st m ⟨hcur, hfd⟩ => ?_)
    ⟨rfl, Nat.zero_le _⟩
  dsimp only [bagMemStep]
  have hcur_fit : Fits w (st.cur + 1) := hfit.of_le (by omega)
  have hfd' : (if m.mem st.cur = d.target then 1 else st.found) ≤ 1 := by
    split_ifs <;> omega
  refine ⟨?_, ?_, ?_⟩
  · split
    · exact ⟨hcur_fit, h1⟩
    · exact hcur_fit
  · change (st.cur + 1) + j = d.base + d.len
    omega
  · exact hfd'

end Cslib.Algorithms.WordRAM.TreeDecomposition
