/-
Copyright (c) 2026 Renfei Zhou, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpModel
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpPermHealProg
import CslibFrontier.Tactic.Realize

/-!
# Runtime Bundle, Capacity Bounds, and Monadic Step Combinators for `SuccinctWhp` Self-Healing

This internal support module provides the 16-word `HealRt` runtime parameter bundle, bucket/pool
conservation bounds under `GoodSeedOnState`, `clampSubProg`, stateless loop-safety induction
`iterationSafe_of_stateless_step`, and bundled `StepSpec` monadic bind/read/write combinators shared
across the parallel `csrToFastGenProg` phase modules.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.HealRt`, `mkHealRt`, `mkHealRtGenProg`:
  compact 16-word runtime parameter bundle for `csrToFastGenProg` array phases.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.clampSubProg`: saturating subtraction
  subroutine over `Basis.exact`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.StepSpec`: bundled `clientState`,
  `clientResult`, and `ValidProg` specification for single-pass monadic `do`-block proofs.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.csrToFast_bounds_of_good`, `hl_bounds`:
  backyard overflow and segment index bounds under `GoodSeedOnState` and `WhpLargeEnv`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_mkHealRtGen`,
  `mkHealRtGenProg_spec`, `realizes_clampSub`, `clampSubProg_spec`: realization and exactness
  specifications for `mkHealRtGenProg` and `clampSubProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.iterationSafe_of_stateless_step`: generic
  `iterationSafe` induction for counter-incrementing loops with state-independent preconditions.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.WordRAM
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-! ## Pure Capacity Bounds -/

/-- Recurrence, summation, and monotonicity properties of `buildBackPrefix`. -/
theorem backPrefix_spec (M cf : ℕ) (fbStart : ℕ → ℕ) :
    let bp := buildBackPrefix M cf fbStart
    bp 0 = 0 ∧
    (∀ b < M, bp (b + 1) = bp b + ((fbStart (b + 1) - fbStart b) - cf)) ∧
    (∀ k ≤ M, bp k = ∑ b ∈ range k, ((fbStart (b + 1) - fbStart b) - cf)) ∧
    (∀ x y, x ≤ y → y ≤ M → bp x ≤ bp y) := by
  have hadj : ∀ b < M,
      buildBackPrefix M cf fbStart (b + 1) =
        buildBackPrefix M cf fbStart b + ((fbStart (b + 1) - fbStart b) - cf) := fun b hb => by
    dsimp only [buildBackPrefix]; simp only [hb, ↓reduceIte]
  refine ⟨rfl, hadj, fun k hk => ?_, fbStart_mono_of_adj fun b hb => by
    rw [hadj b hb]; exact Nat.le_add_right _ _⟩
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk_lt : k < M := Nat.lt_of_succ_le hk
    rw [Finset.sum_range_succ, ← ih hk_lt.le, hadj k hk_lt]

/-- Under `GoodSeedOnState`, every bucket's backyard overflow fits within `capBackWhp n_max`, total
bucket load fits within `totalLocalCoordsWhp n_max`, and total backyard occupancy fits within
`poolSizeWhp n_max`. -/
theorem csrToFast_bounds_of_good {c U V n_max : ℕ}
    (hth : whpThreshold c ≤ n_max)
    {θ : SeedWhp c U n_max} {csr : CsrState} {dict : Dictionary.State U}
    (hcsr : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict)
    (hgood : GoodSeedOnState c U n_max θ dict) :
    let M := numBucketsWhp n_max
    let cf := capFrontWhp n_max
    let cb := capBackWhp n_max
    let bp := buildBackPrefix M cf csr.fbStart
    (∀ b < M,
      (csr.fbStart (b + 1) - csr.fbStart b) - cf < cb ∧
      csr.fbStart (b + 1) - csr.fbStart b ≤ totalLocalCoordsWhp n_max) ∧
    bp M ≤ poolSizeWhp n_max := by
  obtain ⟨hcard_b, hcard_dom⟩ := hcsr.bucket_and_dom_card
  obtain ⟨_, _, hfbM_le, _, _, _⟩ := hcsr
  obtain ⟨_, _, hbp_sum, _⟩ := backPrefix_spec (numBucketsWhp n_max) (capFrontWhp n_max)
    csr.fbStart
  let X_fin : Fin (numBucketsWhp n_max) → ℕ :=
    fun b => csr.fbStart (b.val + 1) - csr.fbStart b.val
  have hsum_X : ∑ b : Fin (numBucketsWhp n_max), X_fin b = csr.fbStart (numBucketsWhp n_max) := by
    have hdom_sum : #(Dictionary.dom dict) = ∑ b : Fin (numBucketsWhp n_max), X_fin b := by
      rw [Finset.card_eq_sum_ones]
      have h1_sum : ∀ u ∈ Dictionary.dom dict,
          (1 : ℕ) = ∑ b : Fin (numBucketsWhp n_max),
            if feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val then 1
            else 0 := by
        intro u _
        let b₀ : Fin (numBucketsWhp n_max) :=
          ⟨feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val,
            feistelBucket_lt (bWhp n_max) (bktHash c U n_max θ.1) u.val⟩
        rw [Fintype.sum_eq_single b₀]
        · simp [b₀]
        · intro b' hb'
          have hne : feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val ≠ b'.val :=
            fun h => hb' (Fin.ext h.symm)
          simp only [hne, ↓reduceIte]
      calc ∑ u ∈ Dictionary.dom dict, 1
          = ∑ u ∈ Dictionary.dom dict, ∑ b : Fin (numBucketsWhp n_max),
              if feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val then 1
              else 0 := Finset.sum_congr rfl h1_sum
        _ = ∑ b : Fin (numBucketsWhp n_max), ∑ u ∈ Dictionary.dom dict,
              if feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val then 1
              else 0 := Finset.sum_comm
        _ = ∑ b : Fin (numBucketsWhp n_max), X_fin b := by
            refine Fintype.sum_congr _ _ fun b => ?_
            rw [← Finset.card_filter, hcard_b b]
    exact hdom_sum.symm.trans hcard_dom
  obtain ⟨hback_lt_cb, _, hpool_le⟩ := sum_sub_capFront_le_poolSize hth X_fin
    (hsum_X.trans_le hfbM_le)
    (fun b => by
      have hb := (hgood.2.1 b).1
      rwa [hcard_b b, hcard_dom, ← hsum_X] at hb)
    (fun b => by
      have hb := (hgood.2.1 b).2
      rwa [hcard_b b, hcard_dom, ← hsum_X] at hb)
  have hbpM_eq : buildBackPrefix (numBucketsWhp n_max) (capFrontWhp n_max) csr.fbStart
      (numBucketsWhp n_max) = ∑ b : Fin (numBucketsWhp n_max), (X_fin b - capFrontWhp n_max) := by
    rw [hbp_sum (numBucketsWhp n_max) le_rfl, ← Fin.sum_univ_eq_sum_range]
  refine ⟨fun b hb => ?_, hbpM_eq ▸ hpool_le⟩
  have hcb := hback_lt_cb ⟨b, hb⟩
  dsimp only [X_fin] at hcb
  exact ⟨hcb, by unfold totalLocalCoordsWhp; omega⟩

/-! ## `HealRt` 16-Word Runtime Bundle -/

/-- Compact 16-word runtime bundle for `csrToFastGenProg` array phases:
`((((base, w), (nMax, M)), ((cf, cb), (totalLoc, poolSize))),`
` ((gBits, tcEntries), ((offBm, offFb), ((offBp, offPs), (offPo, offLs)))))`. -/
abbrev HealRt : Type :=
  (((ℕ × ℕ) × (ℕ × ℕ)) × ((ℕ × ℕ) × (ℕ × ℕ))) ×
    ((ℕ × ℕ) × ((ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))))

/-- Base word address in `HealRt`. -/
@[expose] def hlBase (rt : HealRt) : ℕ := rt.1.1.1.1
/-- Machine word width `w` in `HealRt`. -/
@[expose] def hlW (rt : HealRt) : ℕ := rt.1.1.1.2
/-- Capacity `n_max` in `HealRt`. -/
@[expose] def hlNMax (rt : HealRt) : ℕ := rt.1.1.2.1
/-- Bucket count `numBucketsWhp n_max` in `HealRt`. -/
@[expose] def hlM (rt : HealRt) : ℕ := rt.1.1.2.2
/-- Front-yard capacity `capFrontWhp n_max` in `HealRt`. -/
@[expose] def hlCF (rt : HealRt) : ℕ := rt.1.2.1.1
/-- Backyard pointer capacity `capBackWhp n_max` in `HealRt`. -/
@[expose] def hlCB (rt : HealRt) : ℕ := rt.1.2.1.2
/-- Per-bucket coordinate limit `totalLocalCoordsWhp n_max` in `HealRt`. -/
@[expose] def hlTotalLoc (rt : HealRt) : ℕ := rt.1.2.2.1
/-- Backyard pool size `poolSizeWhp n_max` in `HealRt`. -/
@[expose] def hlPoolSize (rt : HealRt) : ℕ := rt.1.2.2.2
/-- Global pointer bit-width `globalPtrBits n_max` in `HealRt`. -/
@[expose] def hlGBits (rt : HealRt) : ℕ := rt.2.1.1
/-- Trie child-entry count `trieChildEntriesWhp c n_max` in `HealRt`. -/
@[expose] def hlTcEntries (rt : HealRt) : ℕ := rt.2.1.2
/-- Offset `offBktMeta` in `HealRt`. -/
@[expose] def hlOffBm (rt : HealRt) : ℕ := rt.2.2.1.1
/-- Offset `offFbStart` in `HealRt`. -/
@[expose] def hlOffFb (rt : HealRt) : ℕ := rt.2.2.1.2
/-- Offset `offBackPtr` in `HealRt`. -/
@[expose] def hlOffBp (rt : HealRt) : ℕ := rt.2.2.2.1.1
/-- Offset `offPoolFreeStack` in `HealRt`. -/
@[expose] def hlOffPs (rt : HealRt) : ℕ := rt.2.2.2.1.2
/-- Offset `offPoolOwner` in `HealRt`. -/
@[expose] def hlOffPo (rt : HealRt) : ℕ := rt.2.2.2.2.1
/-- Offset `offLocState` in `HealRt`. -/
@[expose] def hlOffLs (rt : HealRt) : ℕ := rt.2.2.2.2.2

/-- Construct `HealRt` for `(c, U, V, w, n_max, base)`. -/
@[expose] def mkHealRt (c U V w n_max base : ℕ) : HealRt :=
  ((((base, w), (n_max, numBucketsWhp n_max)),
    ((capFrontWhp n_max, capBackWhp n_max),
     (totalLocalCoordsWhp n_max, poolSizeWhp n_max))),
   ((globalPtrBits n_max, trieChildEntriesWhp c n_max),
    ((offBktMeta c U V w n_max, offFbStart c U V w n_max),
     ((offBackPtr c U V w n_max, offPoolFreeStack c U V w n_max),
      (offPoolOwner c U V w n_max, offLocState c U V w n_max)))))

@[simp] theorem hlBase_mk (c U V w n_max base : ℕ) :
    hlBase (mkHealRt c U V w n_max base) = base := rfl
@[simp] theorem hlW_mk (c U V w n_max base : ℕ) :
    hlW (mkHealRt c U V w n_max base) = w := rfl
@[simp] theorem hlM_mk (c U V w n_max base : ℕ) :
    hlM (mkHealRt c U V w n_max base) = numBucketsWhp n_max := rfl
@[simp] theorem hlPoolSize_mk (c U V w n_max base : ℕ) :
    hlPoolSize (mkHealRt c U V w n_max base) = poolSizeWhp n_max := rfl
@[simp] theorem hlGBits_mk (c U V w n_max base : ℕ) :
    hlGBits (mkHealRt c U V w n_max base) = globalPtrBits n_max := rfl
@[simp] theorem hlOffBm_mk (c U V w n_max base : ℕ) :
    hlOffBm (mkHealRt c U V w n_max base) = offBktMeta c U V w n_max := rfl

/-- Parameter-free `HealRt` envelope. -/
@[expose] def HealRtEnvGen (w : ℕ) (rt : HealRt) : Prop :=
  ∃ c U V w₀ n_max, WhpLargeEnv c U V w₀ n_max w (hlBase rt) ∧
    rt = mkHealRt c U V w₀ n_max (hlBase rt)

/-- Shared precondition for per-bucket outer loops over `HealRt × ℕ`. -/
@[expose] def HealBktStepPre (w : ℕ) (d : HealRt × ℕ) (_s : Memory.State) : Prop :=
  HealRtEnvGen w d.1 ∧ d.2 < hlM d.1

/-- Assemble `HealRt` from `(WhpCoreParams, base)` in zero memory steps. -/
@[irreducible] def mkHealRtGenProg : WhpCoreParams × ℕ → Memory.Prog HealRt
  | (cp, base_in) => do
    let base ← pure base_in
    let a1 ← pure ((base, wpW cp), (wpNMax cp, wpM cp))
    let a2 ← pure ((wpCapFront cp, wpCapBack cp), (wpTotalLoc cp, wpPoolSize cp))
    let b1 ← pure (wpGlobalPtrBits cp, wpTrieChildEntries cp)
    let b2 ← pure (wpOffBktMeta cp, wpOffFbStart cp)
    let b3 ← pure (wpOffBackPtr cp, wpOffPoolFreeStack cp)
    let b4 ← pure (wpOffPoolOwner cp, wpOffLocState cp)
    pure ((a1, a2), (b1, (b2, (b3, b4))))

/-- `Realizes .exact` certificate for `mkHealRtGenProg`. -/
theorem realizes_mkHealRtGen :
    Realizes .exact mkHealRtGenProg
      (WordEncoding.encode (α := WhpCoreParams × ℕ))
      (WordEncoding.encode (α := HealRt))
      (fun w d _ => WhpLargeEnvGen w d.1 d.2)
      (fun _ _ => 0) := by
  unfold mkHealRtGenProg
  realize

/-- Exact specification of `mkHealRtGenProg` in the large regime. -/
theorem mkHealRtGenProg_spec {c U V w n_max base : ℕ}
    (hth : whpThreshold c ≤ n_max) (s : Memory.State) :
    let prog := mkHealRtGenProg (mkWhpCoreParams c U V w n_max, base)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog = mkHealRt c U V w n_max base ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  dsimp only
  unfold mkHealRtGenProg
  simp only [wp_large_w hth, wp_large_nMax hth, wp_large_M hth,
    wp_large_capFront hth, wp_large_capBack hth, wp_large_totalLoc hth, wp_large_poolSize hth,
    wp_large_globalPtrBits hth, wp_large_trieChildEntries hth, wp_large_offBktMeta hth,
    wp_large_offFbStart hth, wp_large_offBackPtr hth, wp_large_offPoolFreeStack hth,
    wp_large_offPoolOwner hth, wp_large_offLocState hth, pure_bind]
  exact ⟨rfl, rfl, validProg_pure _⟩

/-- Parameter and bit-width bounds implied by `WhpLargeEnv`. -/
theorem hl_bounds {c U V w n_max base : ℕ}
    (henv : WhpLargeEnv c U V w n_max w base) :
    let M := numBucketsWhp n_max
    M < n_max ∧
    16 * M ≤ n_max ∧
    M * capBackWhp n_max ≤ n_max ∧
    poolSizeWhp n_max ≤ n_max ∧
    2 * totalLocalCoordsWhp n_max < n_max ∧
    trieChildEntriesWhp c n_max ≤ n_max ∧
    3 ≤ w ∧
    globalPtrBits n_max ≤ w := by
  have hth := henv.2.2.2.1
  have hL2 := two_le_slabScale n_max
  have hML12 := numBucketsWhp_mul_scale_pow12_le hth
  have hM_ge := (large_bounds_lt_n_max hth).1
  have h16M := sixteen_mul_numBuckets_le_n_max hth
  have hcb_le : capBackWhp n_max ≤ (slabScale n_max) ^ 12 := by
    unfold capBackWhp
    calc 2 * (slabScale n_max) ^ 11 ≤ slabScale n_max * (slabScale n_max) ^ 11 :=
          Nat.mul_le_mul_right _ hL2
      _ = (slabScale n_max) ^ 12 := by ring
  have hMcb : numBucketsWhp n_max * capBackWhp n_max ≤ n_max :=
    (Nat.mul_le_mul_left _ hcb_le).trans hML12
  have htot3 := @totalLocalCoordsWhp_le_three_mul n_max
  have hL_pos : 1 ≤ (slabScale n_max) ^ 12 := Nat.one_le_pow 12 _ (slabScale_pos n_max)
  have h1024 : 1024 * (slabScale n_max) ^ 12 ≤ n_max :=
    (Nat.mul_le_mul_right _ hM_ge).trans hML12
  have h2tot : 2 * totalLocalCoordsWhp n_max < n_max := by
    calc 2 * totalLocalCoordsWhp n_max ≤ 6 * (slabScale n_max) ^ 12 := by omega
      _ < 1024 * (slabScale n_max) ^ 12 := by omega
      _ ≤ n_max := h1024
  have htc_le : trieChildEntriesWhp c n_max ≤ n_max := by
    have hsub := (sublinear_table_bits_le hth).2.2.2.1
    exact (Nat.le_mul_of_pos_right _ (globalPtrBits_pos_of_large hth)).trans hsub
  have hlog := henv.log_lt_w
  have hge := log_ge_mul_ell hth
  have hell := one_le_logLogFactor n_max
  exact ⟨by omega, h16M, hMcb, Nat.sub_le _ _, h2tot, htc_le, by omega,
    globalPtrBits_le_w henv.2.2.2.2.1 henv.2.2.2.2.2.1⟩

/-- Saturating subtraction `p.1 - p.2` as a zero-memory `Memory.Prog` subroutine. -/
@[irreducible] def clampSubProg (p : ℕ × ℕ) : Memory.Prog ℕ :=
  if p.2 ≤ p.1 then pure (p.1 - p.2) else pure 0

/-- `Realizes .exact` certificate for `clampSubProg`. -/
theorem realizes_clampSub :
    Realizes .exact clampSubProg
      (WordEncoding.encode (α := ℕ × ℕ))
      (WordEncoding.encode (α := ℕ))
      (fun _ _ _ => True)
      (fun _ _ => 0) := by
  unfold clampSubProg
  realize
  omega

/-- `clampSubProg` leaves caller memory and frontier unchanged. -/
theorem clientState_clampSubProg (p : ℕ × ℕ) (s : Memory.State) :
    (Memory.spec 0).clientState s (clampSubProg p) = s := by
  unfold clampSubProg; split_ifs <;> rfl

/-- Exact specification of `clampSubProg` when `tb ≤ ps`. -/
theorem clampSubProg_spec {ps tb w F : ℕ} (hle : tb ≤ ps) (s : Memory.State) :
    (Memory.spec 0).clientState s (clampSubProg (ps, tb)) = s ∧
    (Memory.spec 0).clientResult s (clampSubProg (ps, tb)) = ps - tb ∧
    ValidProg w F s (clampSubProg (ps, tb)) := by
  unfold clampSubProg
  dsimp only
  rw [ite_eq_left hle]
  exact ⟨rfl, rfl, validProg_pure _⟩

/-! ## Shared Loop-Safety & Monadic `StepSpec` Combinators -/

/-- Generic `iterationSafe` induction for counter-incrementing loops `Cfg × ℕ → Memory.Prog ℕ`
whose step precondition holds for every `i < N` independently of memory state. -/
theorem iterationSafe_of_stateless_step {Cfg : Type} (step : Cfg × ℕ → Memory.Prog ℕ)
    (Pre : ℕ → Cfg × ℕ → Memory.State → Prop) {w N : ℕ} {cfg : Cfg}
    (hpre : ∀ i < N, ∀ s, Pre w (cfg, i) s)
    (hres : ∀ i < N, ∀ s, (Memory.spec 0).clientResult s (step (cfg, i)) = i + 1) :
    ∀ rem i₀ (s : Memory.State), i₀ + rem ≤ N →
      iterationSafe step Pre w cfg rem i₀ s := by
  intro rem
  induction rem with
  | zero => intro _ _ _; exact trivial
  | succ rem ih =>
    intro i₀ s hle
    have hi : i₀ < N := by omega
    refine ⟨hpre i₀ hi s, ?_⟩
    rw [clientState_width, clientResult_width, hres i₀ hi s]
    exact ih (i₀ + 1) _ (by omega)

/-- Bundled `clientState`, `clientResult`, and `ValidProg` specification for `Memory.spec 0`,
allowing monadic `do`-blocks to be discharged in a single pass instead of three separate passes. -/
@[expose] def StepSpec {α : Type} (w F : ℕ) (s : Memory.State) (prog : Memory.Prog α)
    (s' : Memory.State) (r : α) : Prop :=
  (Memory.spec 0).clientState s prog = s' ∧
  (Memory.spec 0).clientResult s prog = r ∧
  ValidProg w F s prog

theorem StepSpec.pure {α : Type} {w F : ℕ} (s : Memory.State) (x : α) :
    StepSpec w F s (Pure.pure x) s x :=
  ⟨rfl, rfl, validProg_pure x⟩

theorem StepSpec.bind {α β : Type} {w F : ℕ} {s s₁ s₂ : Memory.State}
    {f : Memory.Prog α} {g : α → Memory.Prog β} {x : α} {y : β}
    (hf : StepSpec w F s f s₁ x) (hg : StepSpec w F s₁ (g x) s₂ y) :
    StepSpec w F s (f >>= g) s₂ y := by
  refine ⟨?_, ?_, ?_⟩
  · rw [clientState_bind, hf.1, hf.2.1]; exact hg.1
  · rw [clientResult_bind, hf.1, hf.2.1]; exact hg.2.1
  · refine validProg_bind hf.2.2 ?_; rw [hf.1, hf.2.1]; exact hg.2.2

theorem StepSpec.read {w F a : ℕ} {s : Memory.State} (ha : a < F) :
    StepSpec w F s (Memory.read a) s (s.mem a) :=
  ⟨rfl, rfl, validProg_read ha⟩

theorem StepSpec.write {w F a v : ℕ} {s : Memory.State} (ha : a < F) (hfit : Fits w v) :
    StepSpec w F s (Memory.write a v)
      { mem := Function.update s.mem a v, frontier := s.frontier } () :=
  ⟨rfl, rfl, validProg_write ha hfit⟩

theorem StepSpec.readPackedGen {N w F base off k idx : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < N) (hbnd : base + off + packedWords N k w ≤ F) :
    StepSpec w F s (readPackedGenProg (((base, off), (k, w)), idx))
      s (readPacked (base + off) k w s.mem idx) := by
  dsimp only [readPackedGenProg]
  exact ⟨clientState_readPackedProg _ _ _ _ _ _,
    clientResult_readPackedProg _ _ _ _ _ _,
    validProg_readPacked hw hidx hbnd⟩

theorem StepSpec.readPackedGen_eq {N w F base off k idx val : ℕ} {s : Memory.State}
    (hw : 0 < w) (hidx : idx < N) (hbnd : base + off + packedWords N k w ≤ F)
    (heq : readPacked (base + off) k w s.mem idx = val) :
    StepSpec w F s (readPackedGenProg (((base, off), (k, w)), idx)) s val := by
  obtain ⟨h1, h2, h3⟩ := StepSpec.readPackedGen hw hidx hbnd
  exact ⟨h1, h2.trans heq, h3⟩

theorem StepSpec.writePackedGen {N w F base off k idx v : ℕ} {s : Memory.State}
    (hw : 0 < w) (hk : k ≤ w) (hidx : idx < N)
    (hbnd : base + off + packedWords N k w ≤ F) :
    StepSpec w F s (writePackedGenProg ((((base, off), (k, w)), idx), v))
      { mem := writePacked (base + off) k w s.mem idx v, frontier := s.frontier } () := by
  dsimp only [writePackedGenProg]
  exact ⟨clientState_writePackedProg _ _ _ _ _ _ _,
    rfl,
    validProg_writePacked hw hk hidx hbnd⟩

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
