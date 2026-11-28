/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.Dynamic.Spec
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpParams
public import CslibFrontier.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
public import CslibFrontier.Probability.KWiseIndependent.VarianceTail
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformBound
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# High-Probability Seed Events and Tail Bounds for the WHP Succinct Dictionary

This module defines the static hash-seed pair `SeedWhp c U n_max = BktSeed × FpSeed` (combining two
independent universe-reduced salted general-`q` double-tabulation seeds from
`BitPackedDoubleTabulation`), the concrete per-state and trailing-window deterministic seed
conditions (`GoodSeedOnState` and `GoodSeedOnWindow`), and proves the per-operation failure
probability bound:

For every exponent `c ≥ 1`, every capacity `whpThreshold c ≤ n_max`, every key universe `n_max ≤ U`,
and every admissible oblivious operation prefix `ops : List (Dynamic.Op U)`,
`(seedLawWhp c U n_max).toOuterMeasure {θ | ¬ GoodSeedOnWindow c U n_max ops θ} ≤
  (max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.BktSeed`, `FpSeed`, `SeedWhp`, `seedLawWhp`:
  combined static seed type and uniform distribution.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.bktHash`, `fpReducedKey`, `fpHash`:
  pure Feistel-bucket hash, Stage-1 reduced key, and Stage-2 salted fingerprint hash.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.BalancedBuckets`, `GoodSeedOnState`,
  `GoodSeedOnWindow`: deterministic load-balance, Stage-1 injectivity, collision-free salt
  existence, and epoch salt-collision count conditions.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.GoodSeedOnWindow.goodSeedOnState_of_mem`:
  `GoodSeedOnWindow` implies `GoodSeedOnState` on every state along the trailing `2 * Q + 2`
  operations (including the target post-state for deterministic self-healing).
* `Cslib.DataStructure.Dictionary.SuccinctWhp.toOuterMeasure_not_goodSeedOnWindow_le`:
  total failure probability across Stage-1 universe reduction, Stage-2 `k`-uniqueness, Feistel
  bucket load balance, multi-salt collision-freedom, and window salt-collision count is at most
  `(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, W. Kuszmaul,
  *Modern Hashing Made Simple*, Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
open Cslib.Probability Cslib.Probability.PMF
open Finset
open scoped BigOperators ENNReal

/-! ## Section 1: Static seed pair and pure hash evaluation wrappers -/

private theorem two_mul_doubleTabCodeBound_le_pow_q_sub_one {c n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) :
    2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c n_max) ≤
      2 ^ ((qTabWhp c - 1) * bCharWhp n_max) := by
  refine (two_mul_doubleTabCodeBound_le_pow_bCharWhp hth).trans
    (Nat.pow_le_pow_right (by decide) ?_)
  have hq := le_qTabWhp c
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- Static seed type for the Feistel quotient bucket hash (`M_out = bWhp n_max`). -/
abbrev BktSeed (c U n_max : ℕ) : Type :=
  BitPackedDoubleTabulation.Seed (w0Whp U) (cTabWhp c) (dTabWhp c) (bCharWhp n_max) (bWhp n_max)

/-- Static seed type for the salted fingerprint hash (`M_out = fpBitsWhp n_max`). -/
abbrev FpSeed (c U n_max : ℕ) : Type :=
  BitPackedDoubleTabulation.Seed (w0Whp U) (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (fpBitsWhp n_max)

/-- Combined static seed pair `(θ_bkt, θ_fp)` sampled once during `initSetup`. -/
abbrev SeedWhp (c U n_max : ℕ) : Type :=
  BktSeed c U n_max × FpSeed c U n_max

/-- Uniform probability distribution over `SeedWhp c U n_max`. -/
noncomputable abbrev seedLawWhp (c U n_max : ℕ) : PMF (SeedWhp c U n_max) :=
  PMF.uniformOfFintype (SeedWhp c U n_max)

/-- Pure Feistel bucket hash `ℕ → ℕ` induced by `θ_bkt`, mapping quotients `q < U` into
`< 2 ^ bWhp n_max = numBucketsWhp n_max` via salt `0`. -/
@[expose] def bktHash (c U n_max : ℕ) (θ₁ : BktSeed c U n_max) (q : ℕ) : ℕ :=
  if hq : q < U then
    (evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (bWhp n_max) 1 θ₁ (⟨0, Nat.zero_lt_one⟩, ⟨q, hq⟩)).val
  else 0

theorem bktHash_lt (c U n_max : ℕ) (θ₁ : BktSeed c U n_max) (q : ℕ) :
    bktHash c U n_max θ₁ q < numBucketsWhp n_max := by
  unfold bktHash numBucketsWhp
  split_ifs with hq
  · exact (evalSalted _ _ _ _ _ _ _ _ θ₁ _).isLt
  · exact Nat.two_pow_pos _

/-- Stage-1 reduced key `fpReducedKey c U n_max θ₂ u < 2 ^ rRedWhp c n_max` used for both Stage-2
salted fingerprint hashing and constant-depth `BufTrie` indexing. -/
@[expose] def fpReducedKey (c U n_max : ℕ) (θ₂ : FpSeed c U n_max) (u : Fin U) : ℕ :=
  (multiplyShiftReduced U (w0Whp U) (rRedWhp c n_max) θ₂.1 u).val

theorem fpReducedKey_lt (c U n_max : ℕ) (θ₂ : FpSeed c U n_max) (u : Fin U) :
    fpReducedKey c U n_max θ₂ u < 2 ^ (cTabWhp c * bCharWhp n_max) := by
  unfold fpReducedKey
  exact (multiplyShiftReduced _ _ _ θ₂.1 u).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _))

/-- Salted fingerprint hash `(s, u) ↦ fp < 2 ^ fpBitsWhp n_max` induced by `θ₂`. -/
@[expose] def fpHash (c U n_max : ℕ) (θ₂ : FpSeed c U n_max)
    (s : Fin (sMaxWhp c n_max)) (u : Fin U) : ℕ :=
  (evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
    (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) θ₂ (s, u)).val

theorem fpHash_lt (c U n_max : ℕ) (θ₂ : FpSeed c U n_max)
    (s : Fin (sMaxWhp c n_max)) (u : Fin U) :
    fpHash c U n_max θ₂ s u < 2 ^ fpBitsWhp n_max :=
  (evalSalted _ _ _ _ _ _ _ _ θ₂ (s, u)).isLt

/-! ## Section 2: Trailing window, `BalancedBuckets`, `GoodSeedOnState`, and `GoodSeedOnWindow` -/

/-- `(Dynamic.spec U V n_max).run` produces a post-state independent of `(V, n_max)`. -/
theorem spec_run_fst_irrel {U V₁ n₁ V₂ n₂ : ℕ} (s : State U) (ops : List (Dynamic.Op U)) :
    ((Dynamic.spec U V₁ n₁).run s ops).1 = ((Dynamic.spec U V₂ n₂).run s ops).1 := by
  induction ops generalizing s with
  | nil => rfl
  | cons o rest ih => exact ih (Dynamic.step s o).1

/-- Append law for `((Dynamic.spec U V n_max).run s (l₁ ++ l₂)).1`. -/
theorem spec_run_fst_append {U V n_max : ℕ} (s : State U) (l₁ l₂ : List (Dynamic.Op U)) :
    ((Dynamic.spec U V n_max).run s (l₁ ++ l₂)).1 =
      ((Dynamic.spec U V n_max).run ((Dynamic.spec U V n_max).run s l₁).1 l₂).1 := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons o rest ih => exact ih (Dynamic.step s o).1

/-- List of all intermediate states `[s₀, s₁, ..., s_k]` visited along `ops` from `s₀`. -/
@[expose] def stateSeq {U : ℕ} : State U → List (Dynamic.Op U) → List (State U)
  | s, [] => [s]
  | s, o :: rest => s :: stateSeq (Dynamic.step s o).1 rest

theorem length_stateSeq {U : ℕ} (s : State U) (ops : List (Dynamic.Op U)) :
    (stateSeq s ops).length = ops.length + 1 := by
  induction ops generalizing s with
  | nil => rfl
  | cons o rest ih => simp [stateSeq, ih]

theorem spec_run_fst_mem_stateSeq {U V n_max : ℕ} (s : State U) (ops : List (Dynamic.Op U)) :
    ((Dynamic.spec U V n_max).run s ops).1 ∈ stateSeq s ops := by
  induction ops generalizing s with
  | nil => simp [stateSeq]
  | cons o rest ih => exact List.mem_cons_of_mem s (ih (Dynamic.step s o).1)

theorem self_mem_stateSeq {U : ℕ} (s : State U) (ops : List (Dynamic.Op U)) :
    s ∈ stateSeq s ops := by
  cases ops <;> simp [stateSeq]

/-- Finset of all keys occurring in `.insert u v` operations in `ops`. -/
@[expose] def opInsKeys {U : ℕ} : List (Dynamic.Op U) → Finset (Fin U)
  | [] => ∅
  | .insert u _ :: rest => insert u (opInsKeys rest)
  | _ :: rest => opInsKeys rest

theorem card_opInsKeys_le {U : ℕ} (ops : List (Dynamic.Op U)) :
    #(opInsKeys ops) ≤ ops.length := by
  induction ops with
  | nil => simp [opInsKeys]
  | cons o rest ih =>
    cases o with
    | insert u _ =>
      dsimp only [opInsKeys, List.length_cons]
      exact (card_insert_le u (opInsKeys rest)).trans (Nat.add_le_add_right ih 1)
    | query _ =>
      dsimp only [opInsKeys, List.length_cons]
      omega
    | delete _ =>
      dsimp only [opInsKeys, List.length_cons]
      omega

/-- Every state visited along `ops` from `s₀` has domain contained in `dom s₀ ∪ opInsKeys ops`. -/
theorem dom_subset_union_opInsKeys {U : ℕ} (s₀ : State U) (ops : List (Dynamic.Op U)) :
    ∀ s ∈ stateSeq s₀ ops, Dictionary.dom s ⊆ Dictionary.dom s₀ ∪ opInsKeys ops := by
  induction ops generalizing s₀ with
  | nil =>
    intro s hs
    simp only [stateSeq, List.mem_singleton] at hs
    subst hs
    exact subset_union_left
  | cons o rest ih =>
    intro s hs
    simp only [stateSeq, List.mem_cons] at hs
    rcases hs with rfl | hs_rest
    · exact subset_union_left
    · have hsub := ih (Dynamic.step s₀ o).1 s hs_rest
      refine hsub.trans fun x hx => ?_
      rcases mem_union.mp hx with hx_step | hx_ins
      · cases o with
        | query _ =>
          exact mem_union_left _ hx_step
        | delete u =>
          dsimp only [Dynamic.step] at hx_step
          rw [Dynamic.dom_delete] at hx_step
          exact mem_union_left _ (mem_of_mem_erase hx_step)
        | insert u v =>
          dsimp only [Dynamic.step, opInsKeys] at hx_step ⊢
          by_cases hxu : x = u
          · subst hxu
            exact mem_union_right _ (mem_insert_self x _)
          · rw [Dictionary.mem_dom_iff, Function.update_of_ne hxu, ← Dictionary.mem_dom_iff]
              at hx_step
            exact mem_union_left _ hx_step
      · cases o <;> simp only [opInsKeys]
        · exact mem_union_right _ hx_ins
        · exact mem_union_right _ (mem_insert_of_mem hx_ins)
        · exact mem_union_right _ hx_ins

theorem card_dom_le_of_validHistory {U V n_max : ℕ} {s₀ : State U}
    (hc₀ : #(Dictionary.dom s₀) ≤ n_max) {ops : List (Dynamic.Op U)}
    (hv : (Dynamic.spec U V n_max).ValidHistory s₀ ops) :
    ∀ s ∈ stateSeq s₀ ops, #(Dictionary.dom s) ≤ n_max := by
  induction ops generalizing s₀ with
  | nil =>
    intro s hs
    simp only [stateSeq, List.mem_singleton] at hs
    rwa [hs]
  | cons o rest ih =>
    obtain ⟨hvo, hv_rest⟩ := hv
    intro s hs
    simp only [stateSeq, List.mem_cons] at hs
    rcases hs with rfl | hs_rest
    · exact hc₀
    · exact ih (Dynamic.card_dom_step_le_of_valid hc₀ hvo) hv_rest s hs_rest

/-- Trailing window length `2 * qEpochWhp n_max + 2` covering two full epochs plus transitions. -/
@[expose] def windowLenWhp (n_max : ℕ) : ℕ :=
  2 * qEpochWhp n_max + 2

/-- State at the start of the trailing `windowLenWhp n_max` operations of `ops`. -/
@[expose] def windowStartState (U n_max : ℕ) (ops : List (Dynamic.Op U)) : State U :=
  ((Dynamic.spec U 0 0).run (Dictionary.empty U) (ops.take (ops.length - windowLenWhp n_max))).1

/-- Trailing `≤ windowLenWhp n_max` operations of `ops`. -/
@[expose] def windowSuffix (U n_max : ℕ) (ops : List (Dynamic.Op U)) : List (Dynamic.Op U) :=
  ops.drop (ops.length - windowLenWhp n_max)

private theorem spec_run_window_eq (U V n_max : ℕ) (ops : List (Dynamic.Op U)) :
    ((Dynamic.spec U V n_max).run (windowStartState U n_max ops) (windowSuffix U n_max ops)).1 =
      ((Dynamic.spec U V n_max).run (Dictionary.empty U) ops).1 := by
  unfold windowStartState windowSuffix
  rw [spec_run_fst_irrel (V₁ := 0) (n₁ := 0) (V₂ := V) (n₂ := n_max) (Dictionary.empty U),
    ← spec_run_fst_append, List.take_append_drop]

private theorem length_windowSuffix_le (U n_max : ℕ) (ops : List (Dynamic.Op U)) :
    (windowSuffix U n_max ops).length ≤ windowLenWhp n_max := by
  unfold windowSuffix
  simp only [List.length_drop]
  omega

/-- Single-bucket load-balance condition `|X_b - #S / M| ≤ deltaWhp n_max` at bucket `b`. -/
@[expose] def BalancedBucketAt (U n_max : ℕ) (h1 : ℕ → ℕ) (S : Finset (Fin U))
    (b : Fin (numBucketsWhp n_max)) : Prop :=
  let X_b := #(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val)
  numBucketsWhp n_max * X_b ≤ #S + numBucketsWhp n_max * deltaWhp n_max ∧
  #S ≤ numBucketsWhp n_max * X_b + numBucketsWhp n_max * deltaWhp n_max

/-- Multiplicative bucket-balance condition `|X_b - #S / M| ≤ deltaWhp n_max` matching
`sum_sub_capFront_le_poolSize`. -/
@[expose] def BalancedBuckets (U n_max : ℕ) (h1 : ℕ → ℕ) (S : Finset (Fin U)) : Prop :=
  ∀ b : Fin (numBucketsWhp n_max), BalancedBucketAt U n_max h1 S b

/-- Concrete single-state fast-mode eligibility condition on `(θ, s)` checked during
self-healing from `fallbackMode` to `fastMode`:
1. `fpReducedKey` is injective on `dom s`;
2. `feistelBucket` satisfies `BalancedBuckets` on `dom s`;
3. Every bucket `b` of `dom s` admits at least one collision-free salt `< sMaxWhp c n_max`. -/
@[expose] def GoodSeedOnState (c U n_max : ℕ) (θ : SeedWhp c U n_max) (s : State U) : Prop :=
  Set.InjOn (fpReducedKey c U n_max θ.2) (Dictionary.dom s : Set (Fin U)) ∧
  BalancedBuckets U n_max (bktHash c U n_max θ.1) (Dictionary.dom s) ∧
  ∀ b : Fin (numBucketsWhp n_max),
    ∃ salt : Fin (sMaxWhp c n_max),
      Set.InjOn (fpHash c U n_max θ.2 salt)
        ((Dictionary.dom s).filter (fun u =>
          feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))

/-- Trailing-window good-seed event for operation history `ops`:
1. Stage-1 `fpReducedKey` is injective on `W_keys = dom s_start ∪ opInsKeys suf`;
2. `BalancedBuckets` holds on `dom s` for every state `s ∈ stateSeq s_start suf`;
3. `BalancedBuckets` holds on `W_ins = opInsKeys suf`;
4. Every window bucket `W_bkt(b)` admits a collision-free salt `< sMaxWhp c n_max`;
5. Fewer than `2 * sMaxWhp c n_max` inserted keys in `W_ins` ever collide with another key in
   their window bucket under any salt `< sMaxWhp c n_max`. -/
@[expose] def GoodSeedOnWindow (c U n_max : ℕ) (ops : List (Dynamic.Op U))
    (θ : SeedWhp c U n_max) : Prop :=
  let s_start := windowStartState U n_max ops
  let suf := windowSuffix U n_max ops
  let W_ins := opInsKeys suf
  let W_keys := Dictionary.dom s_start ∪ W_ins
  let h1 := bktHash c U n_max θ.1
  Set.InjOn (fpReducedKey c U n_max θ.2) (W_keys : Set (Fin U)) ∧
  (∀ s ∈ stateSeq s_start suf, BalancedBuckets U n_max h1 (Dictionary.dom s)) ∧
  BalancedBuckets U n_max h1 W_ins ∧
  (∀ b : Fin (numBucketsWhp n_max),
    ∃ salt : Fin (sMaxWhp c n_max),
      Set.InjOn (fpHash c U n_max θ.2 salt)
        (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) : Set (Fin U))) ∧
  #(W_ins.filter fun u =>
      ∃ v ∈ W_keys.filter (fun w =>
        feistelBucket (bWhp n_max) h1 w.val = feistelBucket (bWhp n_max) h1 u.val),
        u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
          fpHash c U n_max θ.2 salt u = fpHash c U n_max θ.2 salt v) <
    2 * sMaxWhp c n_max

/-- `GoodSeedOnWindow` implies `GoodSeedOnState` on every state along the trailing window (including
the final state `((Dynamic.spec U 0 0).run (empty U) ops).1`). -/
theorem GoodSeedOnWindow.goodSeedOnState_of_mem {c U n_max : ℕ} {ops : List (Dynamic.Op U)}
    {θ : SeedWhp c U n_max} (hg : GoodSeedOnWindow c U n_max ops θ)
    {s : State U} (hs : s ∈ stateSeq (windowStartState U n_max ops) (windowSuffix U n_max ops)) :
    GoodSeedOnState c U n_max θ s := by
  obtain ⟨hinj, hbal, _, hsalt, _⟩ := hg
  have hdom_sub : (Dictionary.dom s : Set (Fin U)) ⊆
      ((Dictionary.dom (windowStartState U n_max ops) ∪ opInsKeys (windowSuffix U n_max ops) :
        Finset (Fin U)) : Set (Fin U)) := by
    exact_mod_cast dom_subset_union_opInsKeys _ _ s hs
  refine ⟨hinj.mono hdom_sub, hbal s hs, fun b => ?_⟩
  obtain ⟨salt, hsalt_b⟩ := hsalt b
  refine ⟨salt, hsalt_b.mono fun u hu => ?_⟩
  rw [mem_coe, mem_filter] at hu ⊢
  exact ⟨hdom_sub hu.1, hu.2⟩

/-! ## Section 3: Density-to-`PMF` bridges and numerical `n_max ^ (-c)` tail lemmas -/

/-- Fundamental logarithmic scale inequality: `Nat.log 2 n_max ≤ slabScale n_max`. -/
theorem log_le_scaleWhp (n_max : ℕ) :
    Nat.log 2 n_max ≤ slabScale n_max := by
  unfold slabScale Dynamic.logLogFactor
  calc Nat.log 2 n_max
      ≤ Nat.log 2 (max n_max 4) := Nat.log_mono_right (le_max_left n_max 4)
    _ ≤ Nat.clog 2 (max n_max 4) := Nat.log_le_clog 2 _
    _ ≤ 2 ^ Nat.clog 2 (Nat.clog 2 (max n_max 4)) :=
        Nat.le_pow_clog Nat.one_lt_two _

/-- When `whpThreshold c ≤ n_max`, `6553600 ≤ slabScale n_max` and
`cEff c + 4 ≤ slabScale n_max`. -/
theorem cEff_add_four_le_scaleWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    6553600 ≤ slabScale n_max ∧ cEff c + 4 ≤ slabScale n_max := by
  have hm := bMinWhp_le_log hth
  have hlogL := log_le_scaleWhp n_max
  exact ⟨(le_bMinWhp c).trans (hm.trans hlogL),
    (cEff_add_four_le_bMinWhp c).trans (hm.trans hlogL)⟩

/-- `a * L ^ k ≤ L ^ m` for `L = slabScale n_max`, any constant `a ≤ 6553600`, and `k < m`. -/
private theorem const_mul_scale_pow_le {c n_max a k m : ℕ} (hth : whpThreshold c ≤ n_max)
    (ha : a ≤ 6553600) (hkm : k < m) : a * slabScale n_max ^ k ≤ slabScale n_max ^ m := by
  have hL := (cEff_add_four_le_scaleWhp hth).1
  calc a * slabScale n_max ^ k ≤ slabScale n_max ^ (k + 1) := by
        rw [pow_succ']; exact Nat.mul_le_mul_right _ (by omega)
    _ ≤ slabScale n_max ^ m := Nat.pow_le_pow_right (by omega) hkm

private theorem sMaxWhp_le_scale_sq {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    sMaxWhp c n_max ≤ slabScale n_max ^ 2 := by
  rw [sq]; exact Nat.mul_le_mul_right _ (cEff_add_four_le_scaleWhp hth).2

private theorem numBucketsWhp_le {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    numBucketsWhp n_max ≤ n_max :=
  (Nat.le_mul_of_pos_right _ (by have := slabScale_pos n_max; positivity)).trans
    (numBucketsWhp_mul_scale_pow12_le hth)

private theorem two_pow_fpBitsWhp (n_max : ℕ) : 2 ^ fpBitsWhp n_max = slabScale n_max ^ 36 := by
  rw [fpBitsWhp, slabScale, ← Nat.pow_mul, Nat.mul_comm]

/-- When `whpThreshold c ≤ n_max`, `(slabScale n_max) ^ 10 ≤ deltaWhp n_max`. -/
private theorem scaleWhp_pow10_le_deltaWhp {c n_max : ℕ} (hth : whpThreshold c ≤ n_max) :
    (slabScale n_max) ^ 10 ≤ deltaWhp n_max := by
  unfold deltaWhp
  rw [Nat.le_div_iff_mul_le (by have := slabScale_pos n_max; unfold numBucketsWhp; positivity)]
  calc (slabScale n_max) ^ 10 * (numBucketsWhp n_max * (8 * slabScale n_max))
      = numBucketsWhp n_max * (8 * (slabScale n_max) ^ 11) := by ring
    _ ≤ numBucketsWhp n_max * (slabScale n_max) ^ 12 := by
        gcongr; exact const_mul_scale_pow_le hth (by norm_num) (by norm_num)
    _ ≤ n_max := numBucketsWhp_mul_scale_pow12_le hth

/-- Convert `((A : ℝ) / (B : ℝ)) ^ r` with `2 ^ E * A ≤ B` into `((2 : ℝ≥0∞) ^ (E * r))⁻¹`. -/
private theorem ofReal_div_pow_le_inv_two_pow {A B E r : ℕ} (hB : 0 < B) (hAB : 2 ^ E * A ≤ B) :
    ENNReal.ofReal (((A : ℝ) / (B : ℝ)) ^ r) ≤ ((2 : ℝ≥0∞) ^ (E * r))⁻¹ := by
  have hdiv : (A : ℝ) / (B : ℝ) ≤ ((2 : ℝ) ^ E)⁻¹ := by
    rw [div_le_iff₀ (by positivity), inv_mul_eq_div, le_div_iff₀ (by positivity), mul_comm]
    exact_mod_cast hAB
  calc ENNReal.ofReal (((A : ℝ) / (B : ℝ)) ^ r)
      ≤ ENNReal.ofReal ((((2 : ℝ) ^ E)⁻¹) ^ r) := by gcongr
    _ = ((2 : ℝ≥0∞) ^ (E * r))⁻¹ := by
        rw [inv_pow, ← pow_mul, ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_pow zero_le_two, ENNReal.ofReal_ofNat]

/-- Pure `ℕ`-exponent criterion showing
`(K : ℝ≥0∞) * (2 ^ D)⁻¹ ≤ (8 : ℝ≥0∞)⁻¹ * (n_max : ℝ≥0∞)⁻¹ ^ c`. -/
private theorem mul_inv_two_pow_le_eighth_inv_pow {K D a b n_max c : ℕ}
    (hn_pos : 0 < n_max) (hK : K ≤ 2 ^ a) (hn : n_max ≤ 2 ^ b) (hexp : 3 + a + b * c ≤ D) :
    (K : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ D)⁻¹ ≤ (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  have h2D_ne : ((2 : ℝ≥0∞) ^ D) ≠ 0 := by positivity
  have h2D_top : ((2 : ℝ≥0∞) ^ D) ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top 2)
  have h8n_ne : (8 : ℝ≥0∞) * (n_max : ℝ≥0∞) ^ c ≠ 0 :=
    mul_ne_zero (by norm_num) (pow_ne_zero c (Nat.cast_ne_zero.mpr hn_pos.ne'))
  have h8n_top : (8 : ℝ≥0∞) * (n_max : ℝ≥0∞) ^ c ≠ ⊤ :=
    ENNReal.mul_ne_top (by norm_num) (ENNReal.pow_ne_top (ENNReal.natCast_ne_top _))
  rw [← ENNReal.inv_pow,
    ← ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
  rw [← div_eq_mul_inv, ENNReal.div_le_iff_le_mul (Or.inl h2D_ne) (Or.inl h2D_top),
    mul_comm _ ((2 : ℝ≥0∞) ^ D), ← div_eq_mul_inv,
    ENNReal.le_div_iff_mul_le (Or.inl h8n_ne) (Or.inl h8n_top)]
  have hnat : K * (8 * n_max ^ c) ≤ 2 ^ D := by
    calc K * (8 * n_max ^ c)
        ≤ 2 ^ a * (2 ^ 3 * (2 ^ b) ^ c) := by gcongr; norm_num
      _ = 2 ^ (a + (3 + b * c)) := by
          rw [← Nat.pow_mul, ← Nat.pow_add, ← Nat.pow_add]
      _ ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) (by omega)
  exact_mod_cast hnat

/-- A union bound over at most `n_max ^ 2` events of probability `2 ^ (-3 * sMaxWhp c n_max)`
costs at most `8⁻¹ * n_max⁻¹ ^ c`. -/
private theorem mul_inv_two_pow_sMaxWhp_le {c n_max K : ℕ} (hth : whpThreshold c ≤ n_max)
    (hK : K ≤ n_max * n_max) :
    (K : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * sMaxWhp c n_max))⁻¹ ≤
      (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  have hn_pow : n_max ≤ 2 ^ (Nat.log 2 n_max + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
  refine mul_inv_two_pow_le_eighth_inv_pow (a := 2 * Nat.log 2 n_max + 2)
    ((whpThreshold_pos c).trans_le hth)
    (hK.trans ((Nat.mul_le_mul hn_pow hn_pow).trans_eq (by rw [← Nat.pow_add]; ring_nf)))
    hn_pow ?_
  have hm_big : 6553600 ≤ Nat.log 2 n_max := (le_bMinWhp c).trans (bMinWhp_le_log hth)
  have hm_le_L : Nat.log 2 n_max ≤ slabScale n_max := log_le_scaleWhp n_max
  have hc_le : c ≤ cEff c := le_max_left c 1
  unfold sMaxWhp
  nlinarith

/-- Two-stage conditioning for a uniform `Seed`: the top table fails `GoodTop` on `W`
(`#W ≤ 2 * n_max`) with probability at most `2 * (8⁻¹ * n_max⁻¹ ^ c)`, so a bad event whose
bottom-table probability given `GoodTop` is at most `2 * (8⁻¹ * n_max⁻¹ ^ c)` has probability at
most `4 * (8⁻¹ * n_max⁻¹ ^ c)`. -/
private theorem toOuterMeasure_seed_le_of_goodTop {c U n_max M_out : ℕ}
    (hth : whpThreshold c ≤ n_max) {W : Finset (Fin U)} (hW : #W ≤ 2 * n_max)
    (Bad : BitPackedDoubleTabulation.Seed (w0Whp U) (cTabWhp c) (dTabWhp c) (bCharWhp n_max)
      M_out → Prop)
    (hbot : ∀ α T₁, GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (kIndepWhp c n_max) W α T₁ →
      (PMF.uniformOfFintype (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) M_out)).toOuterMeasure
        {T₂ | Bad (α, T₁, T₂)} ≤
        (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c + (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c) :
    (PMF.uniformOfFintype _).toOuterMeasure {θ | Bad θ} ≤
      ((8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c + (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c) +
        ((8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c + (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c) := by
  let e := (Equiv.prodAssoc (Fin (2 ^ (w0Whp U - 1)))
    (DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max))
    (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) M_out)).symm
  refine toOuterMeasure_uniformOfFintype_cond_le e
    (fun p => GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W p.1 p.2) Bad ?_ fun p hp => hbot p.1 p.2 hp
  rw [← toOuterMeasure_uniformOfFintype_fst e]
  have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le hth
  have hq1 : 1 ≤ qTabWhp c := by have := le_qTabWhp c; omega
  have hm_big : 6553600 ≤ Nat.log 2 n_max := (le_bMinWhp c).trans (bMinWhp_le_log hth)
  have hce_m : cEff c + 4 ≤ Nat.log 2 n_max :=
    (cEff_add_four_le_bMinWhp c).trans (bMinWhp_le_log hth)
  have hn_pow : n_max ≤ 2 ^ (Nat.log 2 n_max + 1) :=
    (Nat.lt_pow_succ_log_self Nat.one_lt_two n_max).le
  have hbchar_4 : Nat.log 2 n_max ≤ 4 * bCharWhp n_max + 3 := by unfold bCharWhp; omega
  have hc_le : c ≤ cEff c := le_max_left c 1
  refine (toOuterMeasure_not_goodTop_le (R := rRedWhp c n_max) (M_out := M_out)
    (w0Whp_pos U) (le_two_pow_w0Whp U) hq1 rfl (two_mul_doubleTabCodeBound_le_pow_q_sub_one hth)
    W).trans (add_le_add ?_ ?_) <;> rw [div_eq_mul_inv]
  · have hW_pow : #W ≤ 2 ^ (Nat.log 2 n_max + 2) := by rw [pow_succ]; omega
    refine mul_inv_two_pow_le_eighth_inv_pow (a := 2 * Nat.log 2 n_max + 4) hn_pos
      ((Nat.mul_le_mul hW_pow ((Nat.sub_le _ _).trans hW_pow)).trans_eq
        (by rw [← pow_add]; ring_nf)) hn_pow ?_
    unfold rRedWhp cTabWhp
    have : 2 * (cEff c + 5) * Nat.log 2 n_max ≤
        8 * (cEff c + 5) * bCharWhp n_max + 6 * (cEff c + 5) := by nlinarith [hbchar_4]
    nlinarith
  · have hcb_le : doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c n_max) ≤ 2 ^ bCharWhp n_max := by
      have := two_mul_doubleTabCodeBound_le_pow_bCharWhp hth
      omega
    have hexp : 3 + (2 * bCharWhp n_max + 1) + (Nat.log 2 n_max + 1) * c ≤
        (qTabWhp c - 1) * bCharWhp n_max * 2 := by
      unfold qTabWhp
      rw [show 4 * (cEff c + 6) + 2 - 1 = 4 * (cEff c + 6) + 1 by omega]
      nlinarith [hbchar_4]
    rw [← pow_mul]
    exact_mod_cast mul_inv_two_pow_le_eighth_inv_pow hn_pos
      (K := 2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c n_max) ^ 2)
      (by calc _ ≤ 2 * (2 ^ bCharWhp n_max) ^ 2 := by gcongr
            _ = 2 ^ (2 * bCharWhp n_max + 1) := by ring) hn_pow hexp

/-! ## Section 4: Window bucket caps, Feistel load balance, salt bounds, and main theorem -/

/-- Under `BalancedBuckets`, any set `S` of size `≤ n_max` puts at most `3 * (slabScale n_max) ^ 12`
keys into each Feistel bucket. -/
private theorem card_bucket_le_of_balanced {c U n_max : ℕ} (_hth : whpThreshold c ≤ n_max)
    {h1 : ℕ → ℕ} {S : Finset (Fin U)} (hS : #S ≤ n_max)
    (hbal : BalancedBuckets U n_max h1 S) (b : Fin (numBucketsWhp n_max)) :
    #(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
      3 * (slabScale n_max) ^ 12 := by
  have hM_pos : 0 < numBucketsWhp n_max := by unfold numBucketsWhp; positivity
  have h2M := n_max_le_two_mul_numBuckets_scale_pow12 n_max
  have hL_pos : 0 < slabScale n_max := slabScale_pos n_max
  have hδ : numBucketsWhp n_max * deltaWhp n_max ≤
      numBucketsWhp n_max * (slabScale n_max) ^ 12 := by
    have hmul : deltaWhp n_max * (numBucketsWhp n_max * (8 * slabScale n_max)) ≤
        2 * numBucketsWhp n_max * (slabScale n_max) ^ 12 :=
      (Nat.div_mul_le_self n_max _).trans h2M
    have hL2 := two_le_slabScale n_max
    nlinarith
  have hup := (hbal b).1
  have htot : numBucketsWhp n_max *
      #(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
      numBucketsWhp n_max * (3 * (slabScale n_max) ^ 12) := by
    linarith
  exact Nat.le_of_mul_le_mul_left htot hM_pos

/-- Union of two `BalancedBuckets` sets of size `≤ n_max` has at most `6 * (slabScale n_max) ^ 12`
keys in every Feistel bucket. -/
private theorem card_union_bucket_le_of_balanced {c U n_max : ℕ} (hth : whpThreshold c ≤ n_max)
    {h1 : ℕ → ℕ} {S₁ S₂ : Finset (Fin U)} (hS₁ : #S₁ ≤ n_max) (hS₂ : #S₂ ≤ n_max)
    (hb₁ : BalancedBuckets U n_max h1 S₁) (hb₂ : BalancedBuckets U n_max h1 S₂)
    (b : Fin (numBucketsWhp n_max)) :
    #((S₁ ∪ S₂).filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
      6 * (slabScale n_max) ^ 12 := by
  rw [filter_union]
  calc #(S₁.filter _ ∪ S₂.filter _)
      ≤ #(S₁.filter _) + #(S₂.filter _) := card_union_le _ _
    _ ≤ 3 * (slabScale n_max) ^ 12 + 3 * (slabScale n_max) ^ 12 :=
        Nat.add_le_add (card_bucket_le_of_balanced hth hS₁ hb₁ b)
          (card_bucket_le_of_balanced hth hS₂ hb₂ b)
    _ = 6 * (slabScale n_max) ^ 12 := by ring

/-- Map each key `u : Fin U` to its quotient `< U` packaged in `Fin U`. -/
private def keyQuotientFin {U : ℕ} (b : ℕ) (u : Fin U) : Fin U :=
  ⟨keyQuotient b u.val, (Nat.div_le_self u.val (2 ^ b)).trans_lt u.isLt⟩

/-- Per-quotient `[0, 1]` bucket indicator `g` for Feistel bucket `b` on `S`, together with its
range, expectation sum `#S / M`, and pointwise sum `X_b`. -/
private def feistelQuotScore {U : ℕ} (n_max : ℕ) (S : Finset (Fin U))
    (b : Fin (numBucketsWhp n_max)) (q : Fin U) (y : Fin (2 ^ bWhp n_max)) : ℝ :=
  (#((S.filter fun u => keyQuotient (bWhp n_max) u.val = q.val).filter
    fun u => (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val) : ℝ)

private theorem feistelQuotScore_props {U n_max : ℕ} (W_quot : Finset (Fin U))
    (S : Finset (Fin U)) (hqS : ∀ u ∈ S, keyQuotientFin (bWhp n_max) u ∈ W_quot)
    (b : Fin (numBucketsWhp n_max)) :
    let g : W_quot → Fin (2 ^ bWhp n_max) → ℝ := fun q y => feistelQuotScore n_max S b q.val y
    (∀ q ∈ (univ : Finset W_quot), ∀ y : Fin (2 ^ bWhp n_max), g q y ∈ Set.Icc (0 : ℝ) 1) ∧
    (∑ q ∈ (univ : Finset W_quot), (𝔼 y, g q y) = (#S : ℝ) / (numBucketsWhp n_max : ℝ)) ∧
    (∀ H : W_quot → Fin (2 ^ bWhp n_max), ∀ h1 : ℕ → ℕ,
      (∀ q : W_quot, h1 q.val.val = (H q).val) →
      ∑ q ∈ (univ : Finset W_quot), g q (H q) =
        (#(S.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) : ℝ)) := by
  dsimp only
  let S_q (q : W_quot) : Finset (Fin U) :=
    S.filter fun u => keyQuotient (bWhp n_max) u.val = q.val.val
  have hpart_card : ∀ (P : Fin U → Prop) [DecidablePred P],
      #(S.filter P) = ∑ q : W_quot, #((S_q q).filter P) := by
    intro P _
    simp only [S_q, filter_filter]
    rw [Finset.card_filter]
    have hpoint : ∀ u ∈ S,
        (if P u then 1 else 0) =
          ∑ q : W_quot, if keyQuotient (bWhp n_max) u.val = q.val.val ∧ P u then 1 else 0 := by
      intro u hu
      let q₀ : W_quot := ⟨keyQuotientFin (bWhp n_max) u, hqS u hu⟩
      rw [Fintype.sum_eq_single q₀]
      · simp [q₀, keyQuotientFin]
      · intro q hne
        have hval_ne : keyQuotient (bWhp n_max) u.val ≠ q.val.val := fun heq =>
          hne (Subtype.ext (Fin.ext heq.symm))
        simp [hval_ne]
    rw [Finset.sum_congr rfl hpoint, Finset.sum_comm]
    refine Fintype.sum_congr _ _ fun q => ?_
    rw [Finset.card_filter]
  refine ⟨?_, ?_, ?_⟩
  · intro q _ y
    refine ⟨Nat.cast_nonneg _, ?_⟩
    have hle1 : #((S_q q).filter fun u => (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val) ≤ 1 := by
      refine Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => ?_
      obtain ⟨hq₁, hx₁⟩ := mem_filter.mp hu₁
      obtain ⟨hq₂, hx₂⟩ := mem_filter.mp hu₂
      have hfb₁ : feistelBucket (bWhp n_max) (fun _ => y.val) u₁.val = b.val := by
        unfold feistelBucket
        rwa [Nat.mod_eq_of_lt y.isLt]
      have hfb₂ : feistelBucket (bWhp n_max) (fun _ => y.val) u₂.val = b.val := by
        unfold feistelBucket
        rwa [Nat.mod_eq_of_lt y.isLt]
      exact Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq
        (hfb₁.trans hfb₂.symm) ((mem_filter.mp hq₁).2.trans (mem_filter.mp hq₂).2.symm))
    unfold feistelQuotScore
    exact_mod_cast hle1
  · have hg_exp : ∀ q : W_quot,
        𝔼 y : Fin (2 ^ bWhp n_max), feistelQuotScore n_max S b q.val y =
          (#(S_q q) : ℝ) / (numBucketsWhp n_max : ℝ) := by
      intro q
      have hgs (y : Fin (2 ^ bWhp n_max)) :
          feistelQuotScore n_max S b q.val y = ∑ u ∈ S_q q,
            if (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val then (1 : ℝ) else 0 := by
        unfold feistelQuotScore
        rw [Finset.sum_boole]
      simp_rw [hgs]
      rw [expect_sum_comm]
      have hterm_u : ∀ u ∈ S_q q,
          (𝔼 y : Fin (2 ^ bWhp n_max),
            if (y.val ^^^ keyLow (bWhp n_max) u.val) = b.val then (1 : ℝ) else 0) =
            1 / (numBucketsWhp n_max : ℝ) := by
        intro u _
        let y₀ : Fin (2 ^ bWhp n_max) :=
          ⟨b.val ^^^ keyLow (bWhp n_max) u.val, Nat.xor_lt_two_pow b.isLt (keyLow_lt _ _)⟩
        have hiff : ∀ y : Fin (2 ^ bWhp n_max),
            ((y.val ^^^ keyLow (bWhp n_max) u.val) = b.val) ↔ y = y₀ := by
          intro y
          constructor
          · intro hy
            apply Fin.ext
            dsimp only [y₀]
            rw [← hy, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
          · rintro rfl
            dsimp only [y₀]
            rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        simp_rw [hiff]
        rw [Finset.expect_eq_sum_div_card, card_univ, Fintype.card_fin, Fintype.sum_ite_eq']
        rfl
      rw [Finset.sum_congr rfl hterm_u, sum_const, nsmul_eq_mul, mul_one_div]
    simp_rw [hg_exp, ← sum_div]
    congr 1
    have hcS := hpart_card (fun _ => True)
    rw [filter_true_of_mem (fun _ _ => trivial)] at hcS
    rw [hcS, Nat.cast_sum]
    refine Fintype.sum_congr _ _ fun q => ?_
    rw [filter_true_of_mem (fun _ _ => trivial)]
  · intro H h1 hH
    rw [hpart_card (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val), Nat.cast_sum]
    refine Fintype.sum_congr _ _ fun q => ?_
    unfold feistelQuotScore
    congr 2
    refine filter_congr fun u hu => ?_
    have hqu : keyQuotient (bWhp n_max) u.val = q.val.val := (mem_filter.mp hu).2
    unfold feistelBucket
    rw [hqu, hH q, Nat.mod_eq_of_lt (H q).isLt]


/-- Single-bucket bottom-table tail bound for Feistel bucket `b`. -/
private theorem toOuterMeasure_not_balancedBucket_single_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (W_quot : Finset (Fin U))
    {α₁ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_quot α₁ T₁)
    (S : Finset (Fin U)) (hS : #S ≤ n_max)
    (hqS : ∀ u ∈ S, keyQuotientFin (bWhp n_max) u ∈ W_quot)
    (b : Fin (numBucketsWhp n_max)) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max))).toOuterMeasure
      {T₂ | ¬ BalancedBucketAt U n_max (bktHash c U n_max (α₁, T₁, T₂)) S b} ≤
      (sMaxWhp c n_max : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ (3 * sMaxWhp c n_max))⁻¹ := by
  set r := sMaxWhp c n_max
  set δ := deltaWhp n_max
  set L := slabScale n_max
  let e_in : W_quot → Fin 1 × W_quot := fun q => (⟨0, Nat.zero_lt_one⟩, q)
  have hk_q := (isKWiseIndependentHash_evalSalted_of_goodTop (M_out := bWhp n_max) (s_max := 1)
    Nat.one_le_two_pow (Nat.min_le_right _ _) hgood).comp
    (fun _ _ h => (Prod.mk.inj h).2 : Function.Injective e_in)
  have hM_pos : 0 < numBucketsWhp n_max := Nat.two_pow_pos _
  have h10 : L ^ 10 ≤ δ := scaleWhp_pow10_le_deltaWhp hth
  have hδ_pos : 0 < δ := (pow_pos (slabScale_pos n_max) 10).trans_le h10
  obtain ⟨hg_Icc, hsum_exp, hsum_H⟩ := feistelQuotScore_props W_quot S hqS b
  have hmax_le : max ((#S : ℝ) / numBucketsWhp n_max) 1 ≤ 2 * (L : ℝ) ^ 12 := by
    have h2M := n_max_le_two_mul_numBuckets_scale_pow12 n_max
    have h1 : 1 ≤ L ^ 12 := Nat.one_le_pow _ _ (slabScale_pos n_max)
    refine max_le ?_ ?_
    · rw [div_le_iff₀ (by positivity)]
      exact_mod_cast (by linarith : #S ≤ 2 * L ^ 12 * numBucketsWhp n_max)
    · exact_mod_cast (by omega : 1 ≤ 2 * L ^ 12)
  have hdens_le :
      _ ≤ (r : ℝ) * (((r ^ 2 * (2 * L ^ 12) : ℕ) : ℝ) / ((δ ^ 2 : ℕ) : ℝ)) ^ r :=
    (hk_q.dens_filter_le_abs_sum_sub_expect_of_Icc (sMaxWhp_pos c n_max) (univ : Finset W_quot)
      _ hg_Icc (Nat.cast_pos.mpr hδ_pos)).trans (by rw [hsum_exp]; push_cast; gcongr)
  have hAB : 2 ^ 3 * (r ^ 2 * (2 * L ^ 12)) ≤ δ ^ 2 := by
    calc 2 ^ 3 * (r ^ 2 * (2 * L ^ 12)) = 16 * r ^ 2 * L ^ 12 := by ring
      _ ≤ 16 * (L ^ 2) ^ 2 * L ^ 12 := by gcongr; exact sMaxWhp_le_scale_sq hth
      _ = 16 * L ^ 16 := by ring
      _ ≤ L ^ 20 := const_mul_scale_pow_le hth (by norm_num) (by norm_num)
      _ = (L ^ 10) ^ 2 := by ring
      _ ≤ δ ^ 2 := by gcongr
  refine (toOuterMeasure_uniformOfFintype_le_of_dens_le _ _ (fun T₂ hT₂ => ?_) hdens_le).trans ?_
  · rw [mem_coe, mem_filter]
    refine ⟨mem_univ _, ?_⟩
    have hsum_T₂ := hsum_H
      (fun q => evalSalted U (w0Whp U) (cTabWhp c * bCharWhp n_max) (cTabWhp c) (dTabWhp c)
        (bCharWhp n_max) (bWhp n_max) 1 (α₁, T₁, T₂) ((e_in q).1, (e_in q).2.val))
      (bktHash c U n_max (α₁, T₁, T₂)) fun q => by
        unfold bktHash
        simp [q.val.isLt, e_in, rRedWhp]
    rw [sum_sub_distrib, hsum_T₂, hsum_exp]
    set X := #(S.filter fun u =>
      feistelBucket (bWhp n_max) (bktHash c U n_max (α₁, T₁, T₂)) u.val = b.val)
    have hM : (0 : ℝ) < numBucketsWhp n_max := Nat.cast_pos.mpr hM_pos
    have he : (numBucketsWhp n_max : ℝ) * (#S / numBucketsWhp n_max) = #S :=
      mul_div_cancel₀ _ hM.ne'
    by_contra hlt
    obtain ⟨h1, h2⟩ := abs_sub_lt_iff.mp (not_le.mp hlt)
    have h1' : (numBucketsWhp n_max * X : ℝ) ≤ #S + numBucketsWhp n_max * δ := by
      linarith [mul_lt_mul_of_pos_left h1 hM]
    have h2' : (#S : ℝ) ≤ numBucketsWhp n_max * X + numBucketsWhp n_max * δ := by
      linarith [mul_lt_mul_of_pos_left h2 hM]
    exact hT₂ ⟨by exact_mod_cast h1', by exact_mod_cast h2'⟩
  · rw [ENNReal.ofReal_mul (Nat.cast_nonneg r), ENNReal.ofReal_natCast]
    gcongr
    exact ofReal_div_pow_le_inv_two_pow (by positivity) hAB

/-- Conditional bottom-table tail bound for `BalancedBuckets` on a single set `S` (`#S ≤ n_max`)
whose quotients lie in `W_quot`, given `GoodTop` on `W_quot`. -/
private theorem toOuterMeasure_not_balancedBuckets_bot_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (W_quot : Finset (Fin U))
    {α₁ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_quot α₁ T₁)
    (S : Finset (Fin U)) (hS : #S ≤ n_max)
    (hqS : ∀ u ∈ S, keyQuotientFin (bWhp n_max) u ∈ W_quot) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (bWhp n_max))).toOuterMeasure
      {T₂ | ¬ BalancedBuckets U n_max (bktHash c U n_max (α₁, T₁, T₂)) S} ≤
      ((numBucketsWhp n_max * sMaxWhp c n_max : ℕ) : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ (3 * sMaxWhp c n_max))⁻¹ := by
  refine (MeasureTheory.measure_mono fun T₂ hT₂ => Set.mem_iUnion.mpr (not_forall.mp hT₂)).trans <|
    (MeasureTheory.measure_iUnion_fintype_le _ _).trans <|
    (Finset.sum_le_card_nsmul _ _ _ fun b _ =>
      toOuterMeasure_not_balancedBucket_single_le hth W_quot hgood S hS hqS b).trans_eq ?_
  rw [card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_assoc]

/-- Conditional bottom-table tail bound for multi-salt intra-bucket collision-freedom across all
`M` window buckets when each window bucket has size `≤ 6 * (slabScale n_max) ^ 12`. -/
private theorem toOuterMeasure_not_salt_inj_bot_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (h1 : ℕ → ℕ) (W_keys : Finset (Fin U))
    (hbkt : ∀ b : Fin (numBucketsWhp n_max),
      #(W_keys.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
        6 * (slabScale n_max) ^ 12)
    {α₂ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_keys α₂ T₁) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))).toOuterMeasure
      {T₂ | ¬ ∀ b : Fin (numBucketsWhp n_max),
        ∃ salt : Fin (sMaxWhp c n_max),
          Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
            (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
              Set (Fin U))} ≤
      (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  classical
  set L := slabScale n_max
  have hk_fp : IsKWiseIndependentHash (2 * sMaxWhp c n_max)
      (fun (T₂ : DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))
        (p : Fin (sMaxWhp c n_max) × W_keys) =>
        evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (p.1, p.2.val)) :=
    isKWiseIndependentHash_evalSalted_of_goodTop (sMaxWhp_le_pow_bChar hth)
      (Nat.min_le_right _ _) hgood
  have hper_b : ∀ b : Fin (numBucketsWhp n_max),
      (PMF.uniformOfFintype _).toOuterMeasure
        {T₂ | ¬ ∃ salt : Fin (sMaxWhp c n_max),
          Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) salt)
            (W_keys.filter (fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :
              Set (Fin U))} ≤
        ((2 : ℝ≥0∞) ^ (3 * sMaxWhp c n_max))⁻¹ := by
    intro b
    let S_b : Finset W_keys :=
      univ.filter fun u : W_keys => feistelBucket (bWhp n_max) h1 u.val.val = b.val
    have hcard_Sb : #S_b ≤ 6 * L ^ 12 := by
      rw [← Finset.card_map (Function.Embedding.subtype _)]
      refine (card_le_card fun u hu => ?_).trans (hbkt b)
      simp only [S_b, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply]
        at hu
      obtain ⟨u', hu', rfl⟩ := hu
      exact mem_filter.mpr ⟨u'.property, hu'⟩
    have hAB : 2 ^ 3 * (#S_b ^ 2) ≤ 2 ^ fpBitsWhp n_max := by
      rw [two_pow_fpBitsWhp]
      calc 2 ^ 3 * (#S_b ^ 2) ≤ 2 ^ 3 * (6 * L ^ 12) ^ 2 := by gcongr
        _ = 288 * L ^ 24 := by ring
        _ ≤ L ^ 36 := const_mul_scale_pow_le hth (by norm_num) (by norm_num)
    have hdens := hk_fp.dens_forall_salt_exists_collision_le S_b
    rw [Fintype.card_fin, ← Nat.cast_pow] at hdens
    refine (toOuterMeasure_uniformOfFintype_le_of_dens_le _ _ (fun T₂ hT₂ => ?_) hdens).trans
      (ofReal_div_pow_le_inv_two_pow (Nat.two_pow_pos _) hAB)
    simp only [mem_coe, mem_filter, mem_univ, true_and]
    intro s
    have hns : ¬ Set.InjOn (fpHash c U n_max (α₂, T₁, T₂) s) _ := fun h => hT₂ ⟨s, h⟩
    simp only [Set.InjOn, not_forall, mem_coe, mem_filter] at hns
    obtain ⟨u₁, ⟨hu₁, hb₁⟩, u₂, ⟨hu₂, hb₂⟩, hfp, hne⟩ := hns
    exact ⟨⟨u₁, hu₁⟩, mem_filter.mpr ⟨mem_univ _, hb₁⟩, ⟨u₂, hu₂⟩,
      mem_filter.mpr ⟨mem_univ _, hb₂⟩, fun h => hne (congrArg Subtype.val h), Fin.ext hfp⟩
  refine (MeasureTheory.measure_mono fun T₂ hT₂ => Set.mem_iUnion.mpr (not_forall.mp hT₂)).trans <|
    (MeasureTheory.measure_iUnion_fintype_le _ _).trans <|
    (Finset.sum_le_card_nsmul _ _ _ fun b _ => hper_b b).trans ?_
  rw [card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact mul_inv_two_pow_sMaxWhp_le hth
    ((Nat.le_mul_of_pos_right _ ((whpThreshold_pos c).trans_le hth)).trans'
      (numBucketsWhp_le hth))

/-- Conditional bottom-table tail bound on the number of keys in `W_ins` that ever collide with
another key in their window bucket under any salt `< sMaxWhp c n_max`. -/
private theorem toOuterMeasure_salt_coll_count_bot_le {c U n_max : ℕ}
    (hth : whpThreshold c ≤ n_max) (h1 : ℕ → ℕ)
    (W_ins W_keys : Finset (Fin U)) (hsub_ins : W_ins ⊆ W_keys)
    (hW_ins : #W_ins ≤ 3 * (slabScale n_max) ^ 18)
    (hbkt : ∀ b : Fin (numBucketsWhp n_max),
      #(W_keys.filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) ≤
        6 * (slabScale n_max) ^ 12)
    {α₂ : Fin (2 ^ (w0Whp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp n_max)}
    (hgood : GoodTop U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
      (bCharWhp n_max) (kIndepWhp c n_max) W_keys α₂ T₁) :
    (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))).toOuterMeasure
      {T₂ | 2 * sMaxWhp c n_max ≤
        #(W_ins.filter fun u =>
          ∃ v ∈ W_keys.filter (fun w =>
            feistelBucket (bWhp n_max) h1 w.val = feistelBucket (bWhp n_max) h1 u.val),
            u ≠ v ∧ ∃ salt : Fin (sMaxWhp c n_max),
              fpHash c U n_max (α₂, T₁, T₂) salt u =
                fpHash c U n_max (α₂, T₁, T₂) salt v)} ≤
      (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c := by
  classical
  set L := slabScale n_max
  have hk_fp : IsKWiseIndependentHash (2 * sMaxWhp c n_max)
      (fun (T₂ : DoubleTabBotSeed (dTabWhp c) (bCharWhp n_max) (fpBitsWhp n_max))
        (p : Fin (sMaxWhp c n_max) × W_keys) =>
        evalSalted U (w0Whp U) (rRedWhp c n_max) (cTabWhp c) (dTabWhp c)
          (bCharWhp n_max) (fpBitsWhp n_max) (sMaxWhp c n_max) (α₂, T₁, T₂) (p.1, p.2.val)) :=
    isKWiseIndependentHash_evalSalted_of_goodTop (sMaxWhp_le_pow_bChar hth)
      (Nat.min_le_right _ _) hgood
  let Q_set : Finset W_keys := univ.filter fun u : W_keys => u.val ∈ W_ins
  let W_of (u : W_keys) : Finset W_keys :=
    univ.filter fun v : W_keys =>
      feistelBucket (bWhp n_max) h1 v.val.val = feistelBucket (bWhp n_max) h1 u.val.val
  have hQ_card : #Q_set ≤ 3 * L ^ 18 := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    refine (card_le_card fun u hu => ?_).trans hW_ins
    simp only [Q_set, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply]
      at hu
    obtain ⟨u', hu', rfl⟩ := hu
    exact hu'
  have hw_cap : ∀ u ∈ Q_set, #(W_of u) ≤ 6 * L ^ 12 := fun u _ => by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    refine (card_le_card fun v hv => ?_).trans
      (hbkt ⟨_, feistelBucket_lt (bWhp n_max) h1 u.val.val⟩)
    simp only [W_of, mem_map, mem_filter, mem_univ, true_and, Function.Embedding.subtype_apply]
      at hv
    obtain ⟨v', hv', rfl⟩ := hv
    exact mem_filter.mpr ⟨v'.property, hv'⟩
  have hdens := hk_fp.dens_card_local_salt_colliding_ge_le Q_set W_of hw_cap
  rw [Fintype.card_fin] at hdens
  have hAB : 2 ^ 3 * (#Q_set * (6 * L ^ 12) * sMaxWhp c n_max) ≤ 2 ^ fpBitsWhp n_max := by
    rw [two_pow_fpBitsWhp]
    calc 2 ^ 3 * (#Q_set * (6 * L ^ 12) * sMaxWhp c n_max)
        ≤ 2 ^ 3 * (3 * L ^ 18 * (6 * L ^ 12) * L ^ 2) := by
          gcongr; exact sMaxWhp_le_scale_sq hth
      _ = 144 * L ^ 32 := by ring
      _ ≤ L ^ 36 := const_mul_scale_pow_le hth (by norm_num) (by norm_num)
  refine ((toOuterMeasure_uniformOfFintype_le_of_dens_le _ _ (fun T₂ hT₂ => ?_) hdens).trans
    (ofReal_div_pow_le_inv_two_pow (Nat.two_pow_pos _) hAB)).trans ?_
  · simp only [mem_coe, mem_filter, mem_univ, true_and]
    refine hT₂.trans ((card_le_card fun u hu => ?_).trans_eq
      (card_map (Function.Embedding.subtype (· ∈ W_keys))))
    obtain ⟨hu_ins, v, hv, hne_uv, s, hfp⟩ := mem_filter.mp hu
    obtain ⟨hv_W, hfb_eq⟩ := mem_filter.mp hv
    refine mem_map.mpr ⟨⟨u, hsub_ins hu_ins⟩, mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, hu_ins⟩,
      ⟨v, hv_W⟩, mem_filter.mpr ⟨mem_univ _, hfb_eq⟩,
      fun h => hne_uv (congrArg Subtype.val h), s, Fin.ext hfp⟩, rfl⟩
  · have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le hth
    simpa only [Nat.cast_one, one_mul] using
      mul_inv_two_pow_sMaxWhp_le hth (K := 1) (Nat.mul_pos hn_pos hn_pos)

/-- **Master per-operation bad-seed probability bound**:
For every capacity `whpThreshold c ≤ n_max`, exponent `c : ℕ`, and admissible oblivious operation
sequence `ops : List (Dynamic.Op U)`
(`(Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops`),
`(seedLawWhp c U n_max).toOuterMeasure {θ | ¬ GoodSeedOnWindow c U n_max ops θ} ≤
(max n_max 1 : ℝ≥0∞)⁻¹ ^ c`. -/
theorem toOuterMeasure_not_goodSeedOnWindow_le {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max)
    {ops : List (Dynamic.Op U)}
    (hv : (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    (seedLawWhp c U n_max).toOuterMeasure {θ | ¬ GoodSeedOnWindow c U n_max ops θ} ≤
      (max n_max 1 : ℝ≥0∞)⁻¹ ^ c := by
  classical
  have hn_pos : 0 < n_max := (whpThreshold_pos c).trans_le hth
  rw [max_eq_left (Nat.one_le_cast.mpr hn_pos)]
  set s_start := windowStartState U n_max ops
  set suf := windowSuffix U n_max ops
  set W_ins := opInsKeys suf
  set W_keys := Dictionary.dom s_start ∪ W_ins
  set W_quot := W_keys.image (keyQuotientFin (bWhp n_max))
  set L := slabScale n_max
  set ε := (8 : ℝ≥0∞)⁻¹ * ((n_max : ℝ≥0∞)⁻¹) ^ c with hε
  -- Window bookkeeping: the window starts in a reachable state and stays within capacity.
  obtain ⟨hv_pre, hv_suf⟩ := ((Dynamic.spec U V n_max).validHistory_append _ _ _).mp
    (by dsimp only [suf, windowSuffix]; rwa [List.take_append_drop] :
      (Dynamic.spec U V n_max).ValidHistory (Dictionary.empty U)
        (ops.take (ops.length - windowLenWhp n_max) ++ suf))
  have hs_start_eq : ((Dynamic.spec U V n_max).run (Dictionary.empty U)
      (ops.take (ops.length - windowLenWhp n_max))).1 = s_start := spec_run_fst_irrel _ _
  rw [hs_start_eq] at hv_suf
  have hdom_start : #(Dictionary.dom s_start) ≤ n_max :=
    hs_start_eq ▸ Dynamic.card_dom_run_empty_le hv_pre
  have hdom_seq := card_dom_le_of_validHistory hdom_start hv_suf
  have hL_big : 6553600 ≤ L := (cEff_add_four_le_scaleWhp hth).1
  have hL18 : L ≤ L ^ 18 := Nat.le_self_pow (by norm_num) L
  have hlen_suf : suf.length ≤ 2 * L ^ 18 + 2 := length_windowSuffix_le U n_max ops
  have hW_ins_3 : #W_ins ≤ 3 * L ^ 18 := by
    have : #W_ins ≤ suf.length := card_opInsKeys_le suf
    omega
  have hW_ins_n : #W_ins ≤ n_max := hW_ins_3.trans
    ((const_mul_scale_pow_le hth (by norm_num) (by norm_num : 18 < 96)).trans
      (slabScale_pow96_le hth))
  have hW_keys_2n : #W_keys ≤ 2 * n_max := (card_union_le _ _).trans (by omega)
  -- Stage 1: the bucket seed balances every window set, conditioned on `GoodTop` on `W_quot`.
  let Ss : Finset (Finset (Fin U)) :=
    insert W_ins ((stateSeq s_start suf).toFinset.image Dictionary.dom)
  have hSs : ∀ S ∈ Ss, #S ≤ n_max ∧ ∀ u ∈ S, keyQuotientFin (bWhp n_max) u ∈ W_quot := by
    simp only [Ss, mem_insert, mem_image, List.mem_toFinset]
    rintro S (rfl | ⟨s, hs, rfl⟩)
    · exact ⟨hW_ins_n, fun u hu => mem_image_of_mem _ (mem_union_right _ hu)⟩
    · exact ⟨hdom_seq s hs,
        fun u hu => mem_image_of_mem _ (dom_subset_union_opInsKeys _ _ s hs hu)⟩
  have hSs_card : #Ss * (numBucketsWhp n_max * sMaxWhp c n_max) ≤ n_max * n_max := by
    have h1 : #Ss ≤ 3 * L ^ 18 := by
      have : #Ss ≤ #((stateSeq s_start suf).toFinset.image Dictionary.dom) + 1 :=
        card_insert_le _ _
      have : #((stateSeq s_start suf).toFinset.image Dictionary.dom) ≤ suf.length + 1 :=
        card_image_le.trans ((List.toFinset_card_le _).trans_eq (length_stateSeq _ _))
      omega
    have h2 : #Ss * sMaxWhp c n_max ≤ n_max := by
      calc #Ss * sMaxWhp c n_max ≤ 3 * L ^ 18 * L ^ 2 :=
            Nat.mul_le_mul h1 (sMaxWhp_le_scale_sq hth)
        _ = 3 * L ^ 20 := by ring
        _ ≤ L ^ 96 := const_mul_scale_pow_le hth (by norm_num) (by norm_num)
        _ ≤ n_max := slabScale_pow96_le hth
    calc #Ss * (numBucketsWhp n_max * sMaxWhp c n_max)
        = #Ss * sMaxWhp c n_max * numBucketsWhp n_max := by ring
      _ ≤ n_max * n_max := Nat.mul_le_mul h2 (numBucketsWhp_le hth)
  let G₁ (θ₁ : BktSeed c U n_max) : Prop :=
    ∀ S ∈ Ss, BalancedBuckets U n_max (bktHash c U n_max θ₁) S
  have hbkt_bad : (PMF.uniformOfFintype (BktSeed c U n_max)).toOuterMeasure
      {θ₁ | ¬ G₁ θ₁} ≤ (ε + ε) + (ε + ε) := by
    refine toOuterMeasure_seed_le_of_goodTop hth (W := W_quot) (card_image_le.trans hW_keys_2n)
      (fun θ₁ => ¬ G₁ θ₁) fun α T₁ hp => ?_
    calc _ ≤ ∑ S ∈ Ss, (PMF.uniformOfFintype _).toOuterMeasure
          {T₂ | ¬ BalancedBuckets U n_max (bktHash c U n_max (α, T₁, T₂)) S} :=
          (MeasureTheory.measure_mono fun T₂ hT₂ => by
            obtain ⟨S, hS, h⟩ := not_forall₂.mp hT₂
            exact Set.mem_biUnion hS h).trans (MeasureTheory.measure_biUnion_finset_le Ss _)
      _ ≤ #Ss • (((numBucketsWhp n_max * sMaxWhp c n_max : ℕ) : ℝ≥0∞) *
            ((2 : ℝ≥0∞) ^ (3 * sMaxWhp c n_max))⁻¹) :=
          sum_le_card_nsmul _ _ _ fun S hS => toOuterMeasure_not_balancedBuckets_bot_le hth
            W_quot hp S (hSs S hS).1 (hSs S hS).2
      _ ≤ ε := by
          rw [nsmul_eq_mul, ← mul_assoc, ← Nat.cast_mul]
          exact mul_inv_two_pow_sMaxWhp_le hth hSs_card
      _ ≤ ε + ε := le_self_add
  -- Stage 2: given stage 1, the fingerprint seed has collision-free salts and few colliders.
  have hfp_cond : ∀ θ₁ : BktSeed c U n_max, G₁ θ₁ →
      (PMF.uniformOfFintype (FpSeed c U n_max)).toOuterMeasure
        {θ₂ | ¬ GoodSeedOnWindow c U n_max ops (θ₁, θ₂)} ≤ (ε + ε) + (ε + ε) := by
    intro θ₁ hG₁
    have hbal_seq : ∀ s ∈ stateSeq s_start suf,
        BalancedBuckets U n_max (bktHash c U n_max θ₁) (Dictionary.dom s) :=
      fun s hs => hG₁ _ (mem_insert_of_mem (mem_image_of_mem _ (List.mem_toFinset.mpr hs)))
    have hbal_ins := hG₁ _ (mem_insert_self _ _)
    have hbkt_6L12 := card_union_bucket_le_of_balanced hth hdom_start hW_ins_n
      (hbal_seq _ (self_mem_stateSeq _ _)) hbal_ins
    refine toOuterMeasure_seed_le_of_goodTop hth hW_keys_2n
      (fun θ₂ => ¬ GoodSeedOnWindow c U n_max ops (θ₁, θ₂)) fun α T₁ hp => ?_
    refine (MeasureTheory.measure_mono fun T₂ hT₂ => ?_).trans <|
      (MeasureTheory.measure_union_le _ _).trans <| add_le_add
        (toOuterMeasure_not_salt_inj_bot_le hth _ W_keys hbkt_6L12 hp)
        (toOuterMeasure_salt_coll_count_bot_le hth _ W_ins W_keys subset_union_right
          hW_ins_3 hbkt_6L12 hp)
    by_contra h
    simp only [Set.mem_union, Set.mem_ofPred_eq, not_or, not_le, not_not] at h
    exact hT₂ ⟨fun u₁ hu₁ u₂ hu₂ heq => hp.1 hu₁ hu₂ (Fin.ext heq), hbal_seq, hbal_ins, h.1, h.2⟩
  refine (toOuterMeasure_uniformOfFintype_cond_le (Equiv.refl _) G₁
    (fun θ => ¬ GoodSeedOnWindow c U n_max ops θ) hbkt_bad hfp_cond).trans_eq ?_
  rw [show ∀ x : ℝ≥0∞, x + x + (x + x) + (x + x + (x + x)) = 8 * x from fun x => by ring, hε,
    ← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
