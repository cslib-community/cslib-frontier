/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.FeistelQuotient
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpParams
public import CslibFrontier.DataStructure.HashFamily.WordRAM.BitPackedDoubleTabulation
public import CslibFrontier.DataStructure.WordRAM.Resizable.Randomized.IncrementalRebuild
public import CslibFrontier.Probability.KWiseIndependent.VarianceTail
import CslibFrontier.Foundations.Data.Finset.Expect
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Epoch Hash Seeds and WHP Good-Seed Concentration for Resizable SOSA 2024

This module defines the two-family per-epoch hash seed bundle (`EpochHashSeeds`) for a large hashed
epoch `N ≥ whpThreshold c` (`N ≤ U`) of the deamortized worst-case WHP resizable succinct dictionary
([Bender, Farach-Colton, J. Kuszmaul, and W. Kuszmaul, SOSA 2024,
Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024];
[Thorup, FOCS 2013][Thorup2013]), together with the deterministic good-seed predicate
`GoodEpochSeeds` and its polynomial failure-probability bound `≤ (1 / 2) * (N : ℝ≥0∞)⁻¹ ^ c` under
exact uniform sampling (`uniform_not_goodEpochSeeds_le`).

For any oblivious trajectory window of an epoch `N`:
1. **`GoodBktSeed`**: Stage-1 reduced-quotient hashing + Stage-2 double tabulation into
   `numBucketsWhp N = 2 ^ bWhp N` Feistel buckets concentrates every live snapshot `S_t`
   (`#S_t ≤ N`) to per-bucket load `≤ capMaxWhp N = 4 * L ^ 12`, and every sub-epoch union `U_e`
   (`#U_e ≤ 2 * N`) to per-bucket load `≤ 2 * capMaxWhp N = 8 * L ^ 12`.
2. **Fingerprint conjuncts of `GoodEpochSeeds`**: Stage-1 reduced-key hashing `rKeyOf` is injective
   across the entire epoch key window `W_keys` (`#W_keys ≤ 8 * N`, guaranteeing collision-free
   `BufTrie` keys), every sub-epoch union bucket `(win.subUnions e)` admits a collision-free salt
   `s < sMaxWhp c N`, and in every sub-epoch `Q_e` (`#Q_e ≤ qEpochWhp N = L ^ 18`) fewer than
   `2 * sMaxWhp c N` keys collide with any distinct bucket-mate in `U_e` under any salt
   `s < sMaxWhp c N`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.redWidthWhp`, `redBitsWhp`,
  `BktSeed`, `FpSeed`, `EpochHashSeeds`: Stage-1/Stage-2 seed parameters and named seed bundle.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.bktHash`, `epochBucket`, `rKeyOf`,
  `fpHash`: Feistel bucket hash, Stage-1 reduced key, and salted `L ^ 36`-fingerprint evaluators.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp.EpochWindowSpec`, `GoodEpochSeeds`:
  oblivious epoch trajectory window specification and joint good-seed predicate.

## Main results

* `epochBucket_lt`, `feistelReconstruct_epochBucket`: Feistel range and exact key reconstruction.
* `uniform_not_goodEpochSeeds_le`: for every `whpThreshold c ≤ N` with `N ≤ U` and every valid
  `EpochWindowSpec c U N`, uniform `EpochHashSeeds c U N` fails `GoodEpochSeeds` with probability at
  most `((1 : ℝ≥0∞) / 2) * (N : ℝ≥0∞)⁻¹ ^ c`.
* `epochFail_le_half_max_inv_pow`: whenever `EpochCapSafe (whpThreshold c) U N n_t` holds (`n_t ≤ N`
  and `whpThreshold c ≤ N`), `((1 : ℝ≥0∞) / 2) * (N : ℝ≥0∞)⁻¹ ^ c ≤ ((1 : ℝ≥0∞) / 2) *
  ((max n_t (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c`.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul, and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–5][BenderFarachColtonKuszmaulKuszmaul2024]
* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.HashFamily.WordRAM
open Cslib.DataStructure.WordRAM.Resizable.Randomized
open Cslib.Probability
open Finset

/-! ## Section 1: Epoch Seed Bundle and Evaluators -/

/-- Stage-1 multiply-shift domain bit-width `max 1 (keyBits U)` (`> 0`, `U ≤ 2 ^ redWidthWhp U`,
and `≤ w` whenever `0 < w` and `U ≤ 2 ^ w`). -/
@[expose] def redWidthWhp (U : ℕ) : ℕ :=
  max 1 (keyBits U)

/-- Stage-1 reduced output bit-width `cTabWhp c * bCharWhp N`. -/
@[expose] def redBitsWhp (c N : ℕ) : ℕ :=
  cTabWhp c * bCharWhp N

theorem redWidthWhp_pos (U : ℕ) : 0 < redWidthWhp U :=
  Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_left 1 _)

theorem le_two_pow_redWidthWhp (U : ℕ) : U ≤ 2 ^ redWidthWhp U := by
  calc U ≤ 2 ^ keyBits U := Nat.le_pow_clog Nat.one_lt_two U
    _ ≤ 2 ^ redWidthWhp U := Nat.pow_le_pow_right (by decide) (le_max_right 1 _)

theorem redWidthWhp_le_of_le_pow {U w : ℕ} (hw : 0 < w) (hU : U ≤ 2 ^ w) :
    redWidthWhp U ≤ w :=
  max_le hw (Nat.clog_le_of_le_pow hU)

theorem two_pow_quotBitsWhp_le_redWidthWhp (U N : ℕ) :
    2 ^ quotBitsWhp U N ≤ 2 ^ redWidthWhp U := by
  refine Nat.pow_le_pow_right (by decide) ?_
  calc quotBitsWhp U N ≤ keyBits U := Nat.sub_le _ _
    _ ≤ redWidthWhp U := le_max_right 1 _

theorem min_redWidthWhp_le_mul (c U N : ℕ) :
    min (redWidthWhp U) (redBitsWhp c N) ≤ cTabWhp c * bCharWhp N :=
  min_le_right _ _

/-- Seed type for the Feistel quotient-to-bucket hash (`M_out = bWhp N`). -/
abbrev BktSeed (c U N : ℕ) : Type :=
  BitPackedDoubleTabulation.Seed (redWidthWhp U) (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N)

/-- Seed type for the salted intra-bucket `L ^ 36`-fingerprint hash (`M_out = fpBitsWhp N`). -/
abbrev FpSeed (c U N : ℕ) : Type :=
  BitPackedDoubleTabulation.Seed (redWidthWhp U) (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N)

/-- Named per-epoch seed bundle `(bkt, fp)` (`0` projection chains). -/
structure EpochHashSeeds (c U N : ℕ) where
  /-- Feistel quotient-to-bucket hash seed. -/
  bkt : BktSeed c U N
  /-- Salted intra-bucket fingerprint & Stage-1 reduced-key hash seed. -/
  fp : FpSeed c U N
  deriving DecidableEq

namespace EpochHashSeeds

/-- Canonical equivalence with `BktSeed c U N × FpSeed c U N`. -/
def equivProd (c U N : ℕ) : EpochHashSeeds c U N ≃ BktSeed c U N × FpSeed c U N where
  toFun s := (s.bkt, s.fp)
  invFun p := ⟨p.1, p.2⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨_, _⟩ => rfl

instance (c U N : ℕ) : Fintype (EpochHashSeeds c U N) :=
  Fintype.ofEquiv _ (equivProd c U N).symm

instance (c U N : ℕ) : Nonempty (EpochHashSeeds c U N) :=
  ⟨⟨Classical.arbitrary _, Classical.arbitrary _⟩⟩

end EpochHashSeeds

/-- Evaluate the Feistel quotient hash `h_bkt(q) < numBucketsWhp N` at salt `0` for any
`q : ℕ` (taking `q % 2 ^ quotBitsWhp U N` so out-of-range inputs are total). -/
@[expose] def bktHash (c U N : ℕ) (θ_bkt : BktSeed c U N) (q : ℕ) : ℕ :=
  (BitPackedDoubleTabulation.evalSalted (2 ^ quotBitsWhp U N) (redWidthWhp U) (redBitsWhp c N)
    (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) 1 θ_bkt
    (⟨0, Nat.zero_lt_one⟩, ⟨q % 2 ^ quotBitsWhp U N, Nat.mod_lt _ (Nat.two_pow_pos _)⟩)).val

/-- Feistel bucket index `epochBucket c U N θ_bkt u < numBucketsWhp N` of key `u : Fin U`. -/
@[expose] def epochBucket (c U N : ℕ) (θ_bkt : BktSeed c U N) (u : Fin U) : ℕ :=
  feistelBucket (bWhp N) (bktHash c U N θ_bkt) u.val

theorem epochBucket_lt (c U N : ℕ) (θ_bkt : BktSeed c U N) (u : Fin U) :
    epochBucket c U N θ_bkt u < numBucketsWhp N :=
  feistelBucket_lt (bWhp N) (bktHash c U N θ_bkt) u.val

theorem keyQuotient_bWhp_lt {U N : ℕ} (hnU : N ≤ U) (u : Fin U) :
    keyQuotient (bWhp N) u.val < 2 ^ quotBitsWhp U N := by
  unfold keyQuotient
  rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← Nat.pow_add, quotBitsWhp_add_bWhp hnU]
  exact u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two U)

@[simp] theorem feistelReconstruct_epochBucket (c U N : ℕ) (θ_bkt : BktSeed c U N) (u : Fin U) :
    feistelReconstruct (bWhp N) (bktHash c U N θ_bkt)
      (epochBucket c U N θ_bkt u) (keyQuotient (bWhp N) u.val) = u.val :=
  feistelReconstruct_feistelBucket (bWhp N) (bktHash c U N θ_bkt) u.val

/-- Stage-1 reduced key `rKey < 2 ^ (cTabWhp c * bCharWhp N)` indexing `BufCur` and `BufOld`. -/
@[expose] def rKeyOf (c U N : ℕ) (θ_fp : FpSeed c U N) (u : Fin U) : ℕ :=
  (multiplyShiftReduced U (redWidthWhp U) (redBitsWhp c N) θ_fp.1 u).val

theorem rKeyOf_lt (c U N : ℕ) (θ_fp : FpSeed c U N) (u : Fin U) :
    rKeyOf c U N θ_fp u < 2 ^ (cTabWhp c * bCharWhp N) :=
  (multiplyShiftReduced U (redWidthWhp U) (redBitsWhp c N) θ_fp.1 u).isLt.trans_le
    (Nat.pow_le_pow_right (by decide) (min_redWidthWhp_le_mul c U N))

/-- Salted intra-bucket fingerprint `fpHash c U N θ_fp s u < 2 ^ fpBitsWhp N`. -/
@[expose] def fpHash (c U N : ℕ) (θ_fp : FpSeed c U N) (s : Fin (sMaxWhp c N)) (u : Fin U) :
    Fin (2 ^ fpBitsWhp N) :=
  BitPackedDoubleTabulation.evalSalted U (redWidthWhp U) (redBitsWhp c N)
    (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) (sMaxWhp c N) θ_fp (s, u)

/-! ## Section 2: Oblivious Epoch Trajectory Window and `GoodEpochSeeds` -/

/-- Deterministic oblivious trajectory window of a large epoch `N`, recording:
* `allKeys`: all keys present at epoch creation or touched during the epoch (`#allKeys ≤ 8 * N`);
* `snaps`: live dictionary key sets across the `≤ 4 * N + 1` steps of the epoch (`#snaps_t ≤ N`);
* `subUnions` and `subBatches`: for each of the `≤ 4 * N + 1` sub-epochs, the union `U_e` of keys
  ever live in sub-epoch `e` (`#U_e ≤ 2 * N`) and the batch `Q_e` of keys updated in sub-epoch `e`
  (`#Q_e ≤ qEpochWhp N`). -/
structure EpochWindowSpec (c U N : ℕ) where
  /-- All keys present at epoch creation or touched during the epoch. -/
  allKeys : Finset (Fin U)
  /-- Number of live dictionary snapshots recorded across the epoch. -/
  numSnaps : ℕ
  /-- Live dictionary key sets across the snapshots of the epoch. -/
  snaps : Fin numSnaps → Finset (Fin U)
  /-- Number of sub-epochs in the epoch window. -/
  numSubs : ℕ
  /-- Union of keys ever live during each sub-epoch. -/
  subUnions : Fin numSubs → Finset (Fin U)
  /-- Batch of keys updated during each sub-epoch. -/
  subBatches : Fin numSubs → Finset (Fin U)
  /-- At most `8 * N` distinct keys appear across the epoch window. -/
  card_allKeys_le : #allKeys ≤ 8 * N
  /-- At most `4 * N + 1` snapshots are recorded across the epoch. -/
  numSnaps_le : numSnaps ≤ 4 * N + 1
  /-- Every snapshot key set is contained in `allKeys`. -/
  snap_sub : ∀ t, snaps t ⊆ allKeys
  /-- Every live snapshot contains at most `N` keys. -/
  card_snap_le : ∀ t, #(snaps t) ≤ N
  /-- At most `4 * N + 1` sub-epochs occur across the epoch. -/
  numSubs_le : numSubs ≤ 4 * N + 1
  /-- Every sub-epoch union key set is contained in `allKeys`. -/
  subUnion_sub : ∀ e, subUnions e ⊆ allKeys
  /-- Every sub-epoch union contains at most `2 * N` keys. -/
  card_subUnion_le : ∀ e, #(subUnions e) ≤ 2 * N
  /-- Every sub-epoch update batch is contained in its sub-epoch union. -/
  subBatch_sub : ∀ e, subBatches e ⊆ subUnions e
  /-- Every sub-epoch update batch has size at most `qEpochWhp N`. -/
  card_subBatch_le : ∀ e, #(subBatches e) ≤ qEpochWhp N

/-- Bucket-seed good event: every live snapshot bucket has at most `capMaxWhp N = 4 * L ^ 12` keys
and every sub-epoch union bucket has at most `2 * capMaxWhp N = 8 * L ^ 12` keys. -/
@[expose] def GoodBktSeed {c U N : ℕ} (win : EpochWindowSpec c U N)
    (θ_bkt : BktSeed c U N) : Prop :=
  (∀ t : Fin win.numSnaps, ∀ b < numBucketsWhp N,
    #((win.snaps t).filter fun u => epochBucket c U N θ_bkt u = b) ≤ capMaxWhp N) ∧
  (∀ e : Fin win.numSubs, ∀ b < numBucketsWhp N,
    #((win.subUnions e).filter fun u => epochBucket c U N θ_bkt u = b) ≤ 2 * capMaxWhp N)

/-- Joint good-seed predicate `GoodEpochSeeds win seeds`:
1. `GoodBktSeed win seeds.bkt`;
2. `rKeyOf c U N seeds.fp` is injective on `win.allKeys` (so `BufTrie` never has distinct-key
   `rKey` collisions);
3. For every sub-epoch `e` and bucket `b < numBucketsWhp N`, there exists a salt
   `s : Fin (sMaxWhp c N)` under which `fpHash` is injective across the entire sub-epoch union
   bucket `win.subUnions e` (covering all keys present at sub-epoch start or inserted during `e`);
4. In every sub-epoch `e`, fewer than `2 * sMaxWhp c N` keys `u ∈ win.subBatches e` collide under
   any salt `s : Fin (sMaxWhp c N)` with any distinct key `v ∈ win.subUnions e` in the same Feistel
   bucket `epochBucket c U N seeds.bkt u`. -/
@[expose] def GoodEpochSeeds {c U N : ℕ} (win : EpochWindowSpec c U N)
    (seeds : EpochHashSeeds c U N) : Prop :=
  GoodBktSeed win seeds.bkt ∧
  Set.InjOn (rKeyOf c U N seeds.fp) (win.allKeys : Set (Fin U)) ∧
  (∀ e : Fin win.numSubs, ∀ b < numBucketsWhp N,
    ∃ s : Fin (sMaxWhp c N), ∀ u ∈ win.subUnions e, ∀ v ∈ win.subUnions e,
      epochBucket c U N seeds.bkt u = b → epochBucket c U N seeds.bkt v = b → u ≠ v →
        fpHash c U N seeds.fp s u ≠ fpHash c U N seeds.fp s v) ∧
  (∀ e : Fin win.numSubs,
    #((win.subBatches e).filter fun u =>
      ∃ v ∈ (win.subUnions e).filter
          (fun v' => epochBucket c U N seeds.bkt v' = epochBucket c U N seeds.bkt u),
        u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
          fpHash c U N seeds.fp s u = fpHash c U N seeds.fp s v) < 2 * sMaxWhp c N)

/-! ## Section 3: Threshold Scale Lemmas (`N ≤ 2 ^ slabScale N`, `N ≤ 2 ^ (8 * bCharWhp N)`) -/

/-- Universal double-exponential ceiling inequality: `N ≤ 2 ^ slabScale N` for every `N : ℕ`. -/
theorem self_le_two_pow_slabScale (N : ℕ) : N ≤ 2 ^ slabScale N := by
  have h1 : N ≤ max N 4 := le_max_left N 4
  have h2 : max N 4 ≤ 2 ^ Nat.clog 2 (max N 4) := Nat.le_pow_clog Nat.one_lt_two _
  have h3 : Nat.clog 2 (max N 4) ≤ 2 ^ Nat.clog 2 (Nat.clog 2 (max N 4)) :=
    Nat.le_pow_clog Nat.one_lt_two _
  exact h1.trans (h2.trans (Nat.pow_le_pow_right (by decide) h3))

/-- When `whpThreshold c ≤ N`, `bMinWhp c ≤ slabScale N`. -/
private theorem bMinWhp_le_slabScale {c N : ℕ} (hth : whpThreshold c ≤ N) :
    bMinWhp c ≤ slabScale N := by
  have hm := bMinWhp_le_log hth
  have h1 : Nat.log 2 N ≤ Nat.clog 2 (max N 4) :=
    (Nat.log_mono_right (le_max_left N 4)).trans (Nat.log_le_clog 2 _)
  exact hm.trans (h1.trans (Nat.le_pow_clog Nat.one_lt_two _))

/-- When `whpThreshold c ≤ N`, `sMaxWhp c N ≤ 2 ^ bCharWhp N`. -/
theorem sMaxWhp_le_two_pow_bCharWhp {c N : ℕ} (hth : whpThreshold c ≤ N) :
    sMaxWhp c N ≤ 2 ^ bCharWhp N := by
  have hmain := codeExpWhp_mul_ell_le_bCharWhp hth
  have hell := Dynamic.one_le_logLogFactor N
  have hc_lt : cEff c + 4 ≤ 2 ^ (cTabWhp c) := by
    have hlt := (@Nat.lt_two_pow_self (cTabWhp c)).le
    have hle : cEff c + 4 ≤ cTabWhp c := by unfold cTabWhp; omega
    exact hle.trans hlt
  have hexp : cTabWhp c + Dynamic.logLogFactor N ≤ bCharWhp N := by
    have hce : cTabWhp c + 1 ≤ codeExpWhp c := by
      have hq := le_qTabWhp c
      have hc := le_cTabWhp c
      have hsq : cTabWhp c + 1 ≤ (cTabWhp c + 1) ^ 2 * qTabWhp c := by nlinarith
      have h16 : (cTabWhp c + 1) ^ 2 * qTabWhp c ≤ 16 * (cTabWhp c + 1) ^ 2 * qTabWhp c := by
        nlinarith
      rw [codeExpWhp_eq]
      linarith
    have hmul : (cTabWhp c + 1) * Dynamic.logLogFactor N ≤ bCharWhp N :=
      (Nat.mul_le_mul_right _ hce).trans hmain
    have h1 : cTabWhp c ≤ cTabWhp c * Dynamic.logLogFactor N :=
      Nat.le_mul_of_pos_right _ hell
    linarith
  calc sMaxWhp c N = (cEff c + 4) * 2 ^ Dynamic.logLogFactor N := rfl
    _ ≤ 2 ^ cTabWhp c * 2 ^ Dynamic.logLogFactor N := Nat.mul_le_mul_right _ hc_lt
    _ = 2 ^ (cTabWhp c + Dynamic.logLogFactor N) := (Nat.pow_add 2 _ _).symm
    _ ≤ 2 ^ bCharWhp N := Nat.pow_le_pow_right (by decide) hexp

/-- When `whpThreshold c ≤ N`, `N ≤ 2 ^ (8 * bCharWhp N)`. -/
private theorem le_two_pow_eight_mul_bCharWhp {c N : ℕ} (hth : whpThreshold c ≤ N) :
    N ≤ 2 ^ (8 * bCharWhp N) := by
  have hm := bMinWhp_le_log hth
  have hbmin := le_bMinWhp c
  have hlt : N < 2 ^ (Nat.log 2 N + 1) := Nat.lt_pow_succ_log_self Nat.one_lt_two N
  have h8 : Nat.log 2 N + 1 ≤ 8 * bCharWhp N := by
    unfold bCharWhp
    omega
  exact hlt.le.trans (Nat.pow_le_pow_right (by decide) h8)

/-- When `whpThreshold c ≤ N`, `16 * (cEff c + 4) ≤ slabScale N`. -/
private theorem mul_cEff_le_slabScale {c N : ℕ} (hth : whpThreshold c ≤ N) :
    16 * (cEff c + 4) ≤ slabScale N := by
  have hbm := bMinWhp_le_slabScale hth
  have hce : 16 * (cEff c + 4) ≤ bMinWhp c := by
    have h1 : cEff c + 4 ≤ codeExpWhp c := by
      rw [codeExpWhp_eq]
      unfold cTabWhp
      nlinarith [one_le_cEff c, le_qTabWhp c]
    rw [bMinWhp_eq]
    nlinarith
  exact hce.trans hbm

private theorem redBitsWhp_eq (c N : ℕ) :
    redBitsWhp c N = (8 * bCharWhp N) * (cEff c + 5) := by
  unfold redBitsWhp cTabWhp
  ring

private theorem qTabWhp_exp_bound (c N : ℕ) :
    bCharWhp N * 2 + 8 * bCharWhp N * (cEff c + 3) ≤ ((qTabWhp c - 1) * bCharWhp N) * 2 := by
  unfold qTabWhp
  have hsub : 4 * (cEff c + 6) + 2 - 1 = 4 * cEff c + 25 := by omega
  rw [hsub]
  nlinarith

private theorem whpThreshold_ge_64 (c : ℕ) : 64 ≤ whpThreshold c := by
  have hb := le_bMinWhp c
  calc 64 = 2 ^ 6 := by decide
    _ ≤ 2 ^ bMinWhp c := Nat.pow_le_pow_right (by decide) (by omega)
    _ = whpThreshold c := (whpThreshold_eq c).symm

private theorem dTabWhp_eq_init (c : ℕ) :
    dTabWhp c = 2 * qTabWhp c * (cTabWhp c + 1) := rfl

private theorem le_two_mul_numBucketsWhp_mul_pow12 (N : ℕ) :
    N ≤ 2 * numBucketsWhp N * slabScale N ^ 12 := by
  rcases Nat.eq_zero_or_pos N with rfl | _
  · exact Nat.zero_le _
  · have hlt := (Nat.lt_pow_succ_log_self Nat.one_lt_two N).le
    have hle : Nat.log 2 N + 1 ≤ bWhp N + 12 * Dynamic.logLogFactor N + 1 := by
      unfold bWhp; omega
    have hpow := hlt.trans (Nat.pow_le_pow_right (by decide) hle)
    have heq : 2 ^ (bWhp N + 12 * Dynamic.logLogFactor N + 1) =
        2 * numBucketsWhp N * slabScale N ^ 12 := by
      unfold numBucketsWhp slabScale
      rw [← Nat.pow_mul, Nat.mul_comm _ 12, Nat.pow_add, Nat.pow_add, Nat.pow_one]
      ring
    omega

private theorem fpBitsWhp_pow_eq (N : ℕ) :
    2 ^ fpBitsWhp N = slabScale N ^ 36 := by
  unfold fpBitsWhp slabScale
  rw [← Nat.pow_mul, Nat.mul_comm 36]

/-- Density-to-`toOuterMeasure` bridge on any finite nonempty seed space. -/
private theorem toOuterMeasure_uniformOfFintype_le_of_dens_le {α : Type*} [Fintype α] [Nonempty α]
    (P : α → Prop) [DecidablePred P] {B : ℝ}
    (hd : (Finset.dens (Finset.univ.filter P) : ℝ) ≤ B) :
    (PMF.uniformOfFintype α).toOuterMeasure {a | P a} ≤ ENNReal.ofReal B := by
  have htr : ((PMF.uniformOfFintype α).toOuterMeasure {a | P a}).toReal =
      (Finset.dens (Finset.univ.filter P) : ℝ) := by
    have h1 := PMF.toOuterMeasure_uniformOfFintype_toReal (α := α) {a | P a}
    have hflt : Finset.univ.filter (· ∈ ({a : α | P a} : Set α)) = Finset.univ.filter P := by
      ext a; simp
    rw [hflt, ← Finset.nnratCast_dens] at h1
    exact h1
  have hfin : (PMF.uniformOfFintype α).toOuterMeasure {a | P a} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (PMF.toOuterMeasure_le_one _ _)
  rw [← ENNReal.ofReal_toReal hfin, htr]
  exact ENNReal.ofReal_le_ofReal hd

attribute [local irreducible] cTabWhp qTabWhp dTabWhp
  bCharWhp bWhp fpBitsWhp quotBitsWhp redWidthWhp redBitsWhp slabScale

/-! ## Section 4: `GoodTop`, Feistel Bucket Concentration, and Salt/Buffer Tail Bounds -/

/-- Upper bound on `¬GoodTop` for any window `W_set` of cardinality `≤ 8 * N` at
`whpThreshold c ≤ N`. -/
private theorem not_goodTop_whp_le {c U_dom N M_out : ℕ}
    (hth : whpThreshold c ≤ N)
    {w₀ : ℕ} (hw₀_pos : 0 < w₀) (hU_w₀ : U_dom ≤ 2 ^ w₀)
    (W_set : Finset (Fin U_dom)) (hW_card : #W_set ≤ 8 * N) :
    PMF.toOuterMeasure (PMF.uniformOfFintype
        (BitPackedDoubleTabulation.Seed w₀ (cTabWhp c) (dTabWhp c) (bCharWhp N) M_out))
      {θ | ¬BitPackedDoubleTabulation.GoodTop U_dom w₀ (redBitsWhp c N) (cTabWhp c) (dTabWhp c)
        (bCharWhp N) (kIndepWhp c N) W_set θ.1 θ.top} ≤
      65 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) := by
  have hq1 : 1 ≤ qTabWhp c := (by decide : 1 ≤ 30).trans (le_qTabWhp c)
  have hcode0 := two_mul_doubleTabCodeBound_le_pow_bCharWhp hth
  have hq30 := le_qTabWhp c
  have hcode : 2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c N) ≤
      2 ^ ((qTabWhp c - 1) * bCharWhp N) := by
    refine hcode0.trans (Nat.pow_le_pow_right (by decide) ?_)
    calc bCharWhp N = 1 * bCharWhp N := (one_mul _).symm
      _ ≤ (qTabWhp c - 1) * bCharWhp N := Nat.mul_le_mul_right _ (by omega)
  have hbase := BitPackedDoubleTabulation.toOuterMeasure_not_goodTop_le
    (R := redBitsWhp c N) (M_out := M_out) hw₀_pos hU_w₀ hq1 (dTabWhp_eq_init c) hcode W_set
  have hN_pos : 0 < N := (whpThreshold_pos c).trans_le hth
  have hN_ne : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
  have hN_top : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hN_pow8 := le_two_pow_eight_mul_bCharWhp hth
  -- Term 1: `(#W * (#W - 1)) / 2 ^ R ≤ 64 * N⁻¹ ^ (cEff c + 3)`
  have hR_pow : N ^ (cEff c + 5) ≤ 2 ^ redBitsWhp c N := by
    rw [redBitsWhp_eq c N, Nat.pow_mul]
    exact Nat.pow_le_pow_left hN_pow8 _
  have hW_prod : #W_set * (#W_set - 1) ≤ 64 * N ^ 2 := by
    have h1 : #W_set - 1 ≤ 8 * N := by omega
    calc #W_set * (#W_set - 1) ≤ (8 * N) * (8 * N) := Nat.mul_le_mul hW_card h1
      _ = 64 * N ^ 2 := by ring
  have hterm1 : ((#W_set * (#W_set - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ redBitsWhp c N ≤
      64 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) := by
    have hden : ((N : ℝ≥0∞) ^ (cEff c + 5)) ≤ (2 : ℝ≥0∞) ^ redBitsWhp c N := by
      exact_mod_cast hR_pow
    have hnum : ((#W_set * (#W_set - 1) : ℕ) : ℝ≥0∞) ≤ 64 * (N : ℝ≥0∞) ^ 2 := by
      exact_mod_cast hW_prod
    calc ((#W_set * (#W_set - 1) : ℕ) : ℝ≥0∞) / (2 : ℝ≥0∞) ^ redBitsWhp c N
        ≤ (64 * (N : ℝ≥0∞) ^ 2) / ((N : ℝ≥0∞) ^ (cEff c + 5)) :=
          ENNReal.div_le_div hnum hden
      _ = 64 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) := by
          rw [show cEff c + 5 = 2 + (cEff c + 3) by omega, pow_add, div_eq_mul_inv,
            ENNReal.mul_inv (Or.inl (pow_ne_zero 2 hN_ne)) (Or.inl (ENNReal.pow_ne_top hN_top)),
            mul_assoc, ← mul_assoc ((N : ℝ≥0∞) ^ 2),
            ENNReal.mul_inv_cancel (pow_ne_zero 2 hN_ne) (ENNReal.pow_ne_top hN_top),
            one_mul, ENNReal.inv_pow]
  -- Term 2: `2 * codeBound^2 / (2 ^ ((q - 1) * bChar))^2 ≤ N⁻¹ ^ (cEff c + 3)`
  have hterm2 : (2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c N) : ℝ≥0∞) ^ 2) /
        ((2 : ℝ≥0∞) ^ ((qTabWhp c - 1) * bCharWhp N)) ^ 2 ≤
      1 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) := by
    have hcb_sq : 2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c N)) ^ 2 ≤ (2 ^ bCharWhp N) ^ 2 := by
      calc 2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c N)) ^ 2
          ≤ (2 * doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c) (kIndepWhp c N)) ^ 2 :=
            by ring_nf; omega
        _ ≤ (2 ^ bCharWhp N) ^ 2 := Nat.pow_le_pow_left hcode0 2
    have hq_exp := qTabWhp_exp_bound c N
    have hpow_den : (2 ^ bCharWhp N) ^ 2 * N ^ (cEff c + 3) ≤
        (2 ^ ((qTabWhp c - 1) * bCharWhp N)) ^ 2 := by
      calc (2 ^ bCharWhp N) ^ 2 * N ^ (cEff c + 3)
          ≤ 2 ^ (bCharWhp N * 2) * (2 ^ (8 * bCharWhp N)) ^ (cEff c + 3) := by
            rw [Nat.pow_mul]
            exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN_pow8 _)
        _ = 2 ^ (bCharWhp N * 2 + 8 * bCharWhp N * (cEff c + 3)) := by
            rw [← Nat.pow_mul, ← Nat.pow_add]
        _ ≤ 2 ^ (((qTabWhp c - 1) * bCharWhp N) * 2) := Nat.pow_le_pow_right (by decide) hq_exp
        _ = (2 ^ ((qTabWhp c - 1) * bCharWhp N)) ^ 2 := by rw [Nat.pow_mul]
    have hnum_cast : (2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
        (kIndepWhp c N) : ℝ≥0∞) ^ 2) ≤ ((2 : ℝ≥0∞) ^ bCharWhp N) ^ 2 := by
      exact_mod_cast hcb_sq
    have hden_cast : ((2 : ℝ≥0∞) ^ bCharWhp N) ^ 2 * (N : ℝ≥0∞) ^ (cEff c + 3) ≤
        ((2 : ℝ≥0∞) ^ ((qTabWhp c - 1) * bCharWhp N)) ^ 2 := by
      exact_mod_cast hpow_den
    have hd1_ne : (((2 : ℝ≥0∞) ^ bCharWhp N) ^ 2) ≠ 0 := by positivity
    have hd1_top : (((2 : ℝ≥0∞) ^ bCharWhp N) ^ 2) ≠ ⊤ :=
      ENNReal.pow_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top 2))
    calc (2 * (doubleTabCodeBound (cTabWhp c + 1) (dTabWhp c) (qTabWhp c)
          (kIndepWhp c N) : ℝ≥0∞) ^ 2) /
          ((2 : ℝ≥0∞) ^ ((qTabWhp c - 1) * bCharWhp N)) ^ 2
        ≤ (((2 : ℝ≥0∞) ^ bCharWhp N) ^ 2) /
            (((2 : ℝ≥0∞) ^ bCharWhp N) ^ 2 * (N : ℝ≥0∞) ^ (cEff c + 3)) :=
          ENNReal.div_le_div hnum_cast hden_cast
      _ = 1 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) := by
          rw [div_eq_mul_inv,
            ENNReal.mul_inv (Or.inl hd1_ne) (Or.inl hd1_top),
            ← mul_assoc, ENNReal.mul_inv_cancel hd1_ne hd1_top, one_mul, one_mul, ENNReal.inv_pow]
  calc (PMF.uniformOfFintype _).toOuterMeasure _
      ≤ _ := hbase
    _ ≤ 64 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) + 1 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) :=
        add_le_add hterm1 hterm2
    _ = 65 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) := by ring

private abbrev keyQuotFin {U N : ℕ} (hnU : N ≤ U) (u : Fin U) : Fin (2 ^ quotBitsWhp U N) :=
  ⟨keyQuotient (bWhp N) u.val, keyQuotient_bWhp_lt hnU u⟩

/-- Abstract Feistel single-bucket upper-tail bound for any `2 * sMaxWhp c N`-wise independent
quotient hash family `H : ι → Q_set → Fin (2 ^ bWhp N)` (factoring out `evalSalted` /
`DoubleTabBotSeed` so kernel checking never unfolds tabulation hashes). -/
private theorem kwise_feistel_bucket_tail_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {c U N : ℕ} (hth : whpThreshold c ≤ N) (hnU : N ≤ U)
    (U_set : Finset (Fin U)) {mult : ℕ} (hm1 : 1 ≤ mult)
    (hcard_U : #U_set ≤ mult * N)
    (H : ι → (U_set.image (keyQuotFin hnU)) → Fin (2 ^ bWhp N))
    (hind : IsKWiseIndependentHash (2 * sMaxWhp c N) H)
    (b : ℕ) (hb : b < numBucketsWhp N)
    (BucketPred : ι → Fin U → Prop) [∀ i, DecidablePred (BucketPred i)]
    (hbp : ∀ i, ∀ u ∈ U_set,
      ∀ hmem : keyQuotFin hnU u ∈ U_set.image (keyQuotFin hnU),
        (BucketPred i u ↔ ((H i ⟨keyQuotFin hnU u, hmem⟩).val ^^^ keyLow (bWhp N) u.val) = b)) :
    (PMF.uniformOfFintype ι).toOuterMeasure
      {i | mult * capMaxWhp N < #(U_set.filter (BucketPred i))} ≤
      (N : ℝ≥0∞)⁻¹ ^ (cEff c + 4) := by
  let Q_fin : Fin U → Fin (2 ^ quotBitsWhp U N) := keyQuotFin hnU
  let Q_set : Finset (Fin (2 ^ quotBitsWhp U N)) := U_set.image Q_fin
  let S_univ : Finset Q_set := Q_set.attach
  let g : Q_set → Fin (2 ^ bWhp N) → ℝ := fun q y =>
    (#((U_set.filter fun u => Q_fin u = q.val).filter
      fun u => (y.val ^^^ keyLow (bWhp N) u.val) = b) : ℝ)
  have hg_le1 : ∀ q ∈ S_univ, ∀ y : Fin (2 ^ bWhp N), g q y ∈ Set.Icc (0 : ℝ) 1 := by
    intro q _ y
    refine ⟨Nat.cast_nonneg _, ?_⟩
    suffices hcard1 :
        #((U_set.filter fun u => Q_fin u = q.val).filter
          fun u => (y.val ^^^ keyLow (bWhp N) u.val) = b) ≤ 1 by
      dsimp only [g]
      exact_mod_cast hcard1
    refine Finset.card_le_one.mpr fun u₁ hu₁ u₂ hu₂ => ?_
    obtain ⟨hu₁_q, hu₁_b⟩ := mem_filter.mp hu₁
    obtain ⟨hu₂_q, hu₂_b⟩ := mem_filter.mp hu₂
    have hq₁ : keyQuotient (bWhp N) u₁.val = q.val.val := congrArg Fin.val (mem_filter.mp hu₁_q).2
    have hq₂ : keyQuotient (bWhp N) u₂.val = q.val.val := congrArg Fin.val (mem_filter.mp hu₂_q).2
    have hfb₁ : feistelBucket (bWhp N) (fun _ => y.val) u₁.val = b := by
      unfold feistelBucket; rw [Nat.mod_eq_of_lt y.isLt]; exact hu₁_b
    have hfb₂ : feistelBucket (bWhp N) (fun _ => y.val) u₂.val = b := by
      unfold feistelBucket; rw [Nat.mod_eq_of_lt y.isLt]; exact hu₂_b
    have hval_eq : u₁.val = u₂.val := by
      rw [← feistelReconstruct_feistelBucket (bWhp N) (fun _ => y.val) u₁.val,
        ← feistelReconstruct_feistelBucket (bWhp N) (fun _ => y.val) u₂.val,
        hfb₁, hfb₂, hq₁, hq₂]
    exact Fin.ext hval_eq
  have hsum_g : ∀ i : ι,
      ∑ q ∈ S_univ, g q (H i q) = (#(U_set.filter (BucketPred i)) : ℝ) := by
    intro i
    have hpart : #(U_set.filter (BucketPred i)) =
        ∑ q ∈ Q_set, #((U_set.filter fun u => Q_fin u = q).filter (BucketPred i)) := by
      rw [← card_biUnion]
      · congr 1
        ext u
        simp only [mem_filter, mem_biUnion, Q_set, mem_image]
        constructor
        · rintro ⟨hu, hb_u⟩
          exact ⟨Q_fin u, ⟨u, hu, rfl⟩, ⟨hu, rfl⟩, hb_u⟩
        · rintro ⟨_, _, ⟨hu, _⟩, hb_u⟩
          exact ⟨hu, hb_u⟩
      · intro q₁ _ q₂ _ hne
        exact disjoint_left.mpr fun u hu₁ hu₂ =>
          hne ((mem_filter.mp (mem_filter.mp hu₁).1).2.symm.trans
            (mem_filter.mp (mem_filter.mp hu₂).1).2)
    rw [hpart, Nat.cast_sum, ← Finset.sum_attach Q_set]
    refine Finset.sum_congr rfl fun q _ => ?_
    dsimp only [g]
    congr 1
    refine congrArg Finset.card ?_
    ext u
    simp only [mem_filter]
    refine and_congr_right fun ⟨hu_U, hu_q⟩ => ?_
    have hmem_u : Q_fin u ∈ Q_set := mem_image_of_mem Q_fin hu_U
    have hsub_eq : (⟨Q_fin u, hmem_u⟩ : Q_set) = q := Subtype.ext hu_q
    rw [hbp i u hu_U hmem_u, hsub_eq]
  have hexp_g : ∀ q : Q_set,
      (𝔼 y : Fin (2 ^ bWhp N), g q y) =
        (#(U_set.filter fun u => Q_fin u = q.val) : ℝ) / (numBucketsWhp N : ℝ) := by
    intro q
    rw [Fintype.expect_eq_sum_div_card, Fintype.card_fin]
    congr 1
    dsimp only [g]
    simp_rw [← Nat.cast_sum]
    congr 1
    let F_q := U_set.filter fun u => Q_fin u = q.val
    have hswap : (∑ y : Fin (2 ^ bWhp N), #(F_q.filter fun u =>
        (y.val ^^^ keyLow (bWhp N) u.val) = b)) =
        ∑ u ∈ F_q, #(Finset.univ.filter fun y : Fin (2 ^ bWhp N) =>
          (y.val ^^^ keyLow (bWhp N) u.val) = b) := by
      simp_rw [Finset.card_filter]
      exact Finset.sum_comm
    rw [hswap]
    have h1 : ∀ u ∈ F_q, #(Finset.univ.filter fun y : Fin (2 ^ bWhp N) =>
        (y.val ^^^ keyLow (bWhp N) u.val) = b) = 1 := by
      intro u _
      let y₀ : Fin (2 ^ bWhp N) := ⟨b ^^^ keyLow (bWhp N) u.val,
        Nat.xor_lt_two_pow hb (keyLow_lt (bWhp N) u.val)⟩
      have heq : (Finset.univ.filter fun y : Fin (2 ^ bWhp N) =>
          (y.val ^^^ keyLow (bWhp N) u.val) = b) = {y₀} := by
        ext y
        simp only [mem_filter, mem_univ, true_and, mem_singleton]
        constructor
        · intro hy
          apply Fin.ext
          dsimp only [y₀]
          rw [← hy, Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
        · rintro rfl
          dsimp only [y₀]
          rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
      rw [heq, card_singleton]
    rw [Finset.sum_congr rfl h1, sum_const, smul_eq_mul, mul_one]
  set L := slabScale N
  have hL2 := two_le_slabScale N
  have hM_pos : 0 < numBucketsWhp N := by unfold numBucketsWhp; positivity
  have hN_le_2ML12 : N ≤ 2 * numBucketsWhp N * L ^ 12 := le_two_mul_numBucketsWhp_mul_pow12 N
  have hmu_le : ∑ q ∈ S_univ, (𝔼 y : Fin (2 ^ bWhp N), g q y) ≤
      (mult * (2 * L ^ 12) : ℕ) := by
    simp_rw [hexp_g, ← Finset.sum_div]
    have hsum_card : (∑ q ∈ S_univ, (#(U_set.filter fun u => Q_fin u = q.val) : ℝ)) =
        (#U_set : ℝ) := by
      rw [← Nat.cast_sum]
      congr 1
      have hp : #U_set = ∑ q ∈ Q_set, #(U_set.filter fun u => Q_fin u = q) := by
        rw [← card_biUnion]
        · congr 1
          ext u
          simp only [mem_biUnion, mem_filter, Q_set, mem_image]
          exact ⟨fun hu => ⟨Q_fin u, ⟨u, hu, rfl⟩, hu, rfl⟩, fun ⟨_, _, hu, _⟩ => hu⟩
        · intro q₁ _ q₂ _ hne
          exact disjoint_left.mpr fun u hu₁ hu₂ =>
            hne ((mem_filter.mp hu₁).2.symm.trans (mem_filter.mp hu₂).2)
      rw [hp, ← Finset.sum_attach Q_set]
    rw [hsum_card, div_le_iff₀ (Nat.cast_pos.mpr hM_pos)]
    have hnat : #U_set ≤ (mult * (2 * L ^ 12)) * numBucketsWhp N := by
      calc #U_set ≤ mult * N := hcard_U
        _ ≤ mult * (2 * numBucketsWhp N * L ^ 12) := Nat.mul_le_mul_left _ hN_le_2ML12
        _ = (mult * (2 * L ^ 12)) * numBucketsWhp N := by ring
    exact_mod_cast hnat
  set m := sMaxWhp c N
  have hm_pos : 1 ≤ m := by
    unfold m sMaxWhp
    exact Nat.mul_pos (by have := one_le_cEff c; omega) (by omega)
  set a : ℝ := ((mult * (2 * L ^ 12) : ℕ) : ℝ)
  have ha_pos : 0 < a := by
    dsimp only [a]
    exact_mod_cast (show 0 < mult * (2 * L ^ 12) by positivity)
  have hconc := hind.dens_filter_le_abs_sum_sub_expect_of_Icc hm_pos S_univ g hg_le1 ha_pos
  have hsub : (Finset.univ.filter fun i : ι =>
        mult * capMaxWhp N < #(U_set.filter (BucketPred i))) ⊆
      (Finset.univ.filter fun i : ι =>
        a ≤ |∑ q ∈ S_univ, (g q (H i q) - 𝔼 y, g q y)|) := by
    intro i hi
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    rw [Finset.sum_sub_distrib, hsum_g i]
    have hgt : ((mult * capMaxWhp N : ℕ) : ℝ) < (#(U_set.filter (BucketPred i)) : ℝ) := by
      exact_mod_cast hi
    have hcap_eq : ((mult * capMaxWhp N : ℕ) : ℝ) = 2 * a := by
      dsimp only [a]; unfold capMaxWhp; push_cast; ring
    have habs := le_abs_self ((#(U_set.filter (BucketPred i)) : ℝ) -
      ∑ q ∈ S_univ, 𝔼 y, g q y)
    linarith only [hgt, hcap_eq, hmu_le, habs]
  have hm_le_L2 : m ≤ L ^ 2 := by
    have h16 := mul_cEff_le_slabScale hth
    unfold m sMaxWhp
    dsimp only [L] at h16 ⊢
    calc (cEff c + 4) * L
        ≤ (16 * (cEff c + 4)) * L := Nat.mul_le_mul_right L (by omega)
      _ ≤ L * L := Nat.mul_le_mul_right L h16
      _ = L ^ 2 := (sq L).symm
  have hratio : (m : ℝ) ^ 2 * max (∑ q ∈ S_univ, 𝔼 y, g q y) 1 / a ^ 2 ≤ (1 : ℝ) / 4 := by
    have hmax_le : max (∑ q ∈ S_univ, 𝔼 y, g q y) 1 ≤ a := by
      refine max_le hmu_le ?_
      dsimp only [a]
      have hL12 : 1 ≤ L ^ 12 := Nat.one_le_pow 12 L (by omega)
      exact_mod_cast (Nat.mul_pos hm1 (by omega))
    have hm_r : (m : ℝ) ^ 2 ≤ ((L : ℝ) ^ 2) ^ 2 := by
      gcongr; exact_mod_cast hm_le_L2
    have hL8 : 8 * ((L : ℝ) ^ 2) ^ 2 ≤ a := by
      dsimp only [a]
      have hnat : 8 * (L ^ 2) ^ 2 ≤ mult * (2 * L ^ 12) := by
        have h4_12 : 4 * L ^ 4 ≤ L ^ 12 := by
          have h8_ge : 4 ≤ L ^ 8 := by
            calc 4 ≤ 2 ^ 8 := by decide
              _ ≤ L ^ 8 := Nat.pow_le_pow_left hL2 8
          calc 4 * L ^ 4 ≤ L ^ 8 * L ^ 4 := Nat.mul_le_mul_right _ h8_ge
            _ = L ^ 12 := by ring
        calc 8 * (L ^ 2) ^ 2 = 2 * (4 * L ^ 4) := by ring
          _ ≤ 2 * L ^ 12 := Nat.mul_le_mul_left 2 h4_12
          _ = 1 * (2 * L ^ 12) := (one_mul _).symm
          _ ≤ mult * (2 * L ^ 12) := Nat.mul_le_mul_right _ hm1
      exact_mod_cast hnat
    rw [div_le_iff₀ (pow_pos ha_pos 2)]
    have hL8' : ((L : ℝ) ^ 2) ^ 2 ≤ (1 / 8 : ℝ) * a := by linarith only [hL8]
    calc (m : ℝ) ^ 2 * max (∑ q ∈ S_univ, 𝔼 y, g q y) 1
        ≤ ((L : ℝ) ^ 2) ^ 2 * a :=
          mul_le_mul hm_r hmax_le (le_trans zero_le_one (le_max_right _ _)) (by positivity)
      _ ≤ ((1 / 8 : ℝ) * a) * a := mul_le_mul_of_nonneg_right hL8' ha_pos.le
      _ = (1 / 8 : ℝ) * a ^ 2 := by ring
      _ ≤ (1 : ℝ) / 4 * a ^ 2 := mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg a)
  have hrhs_le : (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ q ∈ S_univ, 𝔼 y, g q y) 1 / a ^ 2) ^ m ≤
      (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) := by
    have hpow_14 : ((m : ℝ) ^ 2 * max (∑ q ∈ S_univ, 𝔼 y, g q y) 1 / a ^ 2) ^ m ≤
        ((1 : ℝ) / 4) ^ m := by
      refine pow_le_pow_left₀ ?_ hratio m
      exact div_nonneg (mul_nonneg (sq_nonneg _) (le_trans zero_le_one (le_max_right _ _)))
        (sq_nonneg _)
    have hm_2m : (m : ℝ) ≤ (2 : ℝ) ^ m := by
      have hnat : m ≤ 2 ^ m := (@Nat.lt_two_pow_self m).le
      exact_mod_cast hnat
    calc (m : ℝ) * ((m : ℝ) ^ 2 * max (∑ q ∈ S_univ, 𝔼 y, g q y) 1 / a ^ 2) ^ m
        ≤ (2 : ℝ) ^ m * ((1 : ℝ) / 4) ^ m := by
          refine mul_le_mul hm_2m hpow_14 ?_ (by positivity)
          exact pow_nonneg (div_nonneg (mul_nonneg (sq_nonneg _)
            (le_trans zero_le_one (le_max_right _ _))) (sq_nonneg _)) m
      _ = ((1 : ℝ) / 2) ^ m := by
          rw [← mul_pow]; norm_num
      _ = (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) := by
          have hm_eq : m = L * (cEff c + 4) := by unfold m sMaxWhp; dsimp only [L]; ring
          rw [hm_eq, pow_mul, one_div, inv_pow, Nat.cast_pow, Nat.cast_ofNat]
  have hdens : (Finset.dens (Finset.univ.filter fun i : ι =>
        mult * capMaxWhp N < #(U_set.filter (BucketPred i))) : ℝ) ≤
      (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) :=
    ((NNRat.cast_le (K := ℝ)).mpr (Finset.dens_le_dens hsub)).trans (hconc.trans hrhs_le)
  have hmeas := toOuterMeasure_uniformOfFintype_le_of_dens_le _ hdens
  refine hmeas.trans ?_
  have hN_le_2L : N ≤ 2 ^ L := self_le_two_pow_slabScale N
  have hofReal : ENNReal.ofReal ((((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4)) =
      ((2 ^ L : ℕ) : ℝ≥0∞)⁻¹ ^ (cEff c + 4) := by
    rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
      ENNReal.ofReal_natCast]
  rw [hofReal]
  exact pow_le_pow_left' (ENNReal.inv_le_inv.mpr (by exact_mod_cast hN_le_2L)) (cEff c + 4)

/-- Conditional single-bucket upper-tail bound under `kIndepWhp c N`-wise independence of
`θ_bkt.bot`: for any `U_set : Finset (Fin U)` with `#U_set ≤ mult * N` (`1 ≤ mult`, `mult ≤ 2`), the
probability over `T₂ : DoubleTabBotSeed` that bucket `b < numBucketsWhp N` receives more than
`mult * capMaxWhp N` items is at most `(N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)`. -/
private theorem bot_bucket_load_gt_le {c U N : ℕ} (hth : whpThreshold c ≤ N) (hnU : N ≤ U)
    {α : Fin (2 ^ (redWidthWhp U - 1))}
    {T₁ : DoubleTabTopSeed (cTabWhp c + 1) (dTabWhp c) (bCharWhp N)}
    (U_set : Finset (Fin U)) {mult : ℕ} (hm1 : 1 ≤ mult) (_hm2 : mult ≤ 2)
    (hcard_U : #U_set ≤ mult * N)
    (hgood : BitPackedDoubleTabulation.GoodTop (2 ^ quotBitsWhp U N) (redWidthWhp U)
      (redBitsWhp c N) (cTabWhp c) (dTabWhp c) (bCharWhp N) (kIndepWhp c N)
      (U_set.image (keyQuotFin hnU)) α T₁)
    (b : ℕ) (hb : b < numBucketsWhp N) :
    (PMF.uniformOfFintype (DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (bWhp N))).toOuterMeasure
      {T₂ | mult * capMaxWhp N <
        #((U_set).filter fun u => epochBucket c U N (α, T₁, T₂) u = b)} ≤
      (N : ℝ≥0∞)⁻¹ ^ (cEff c + 4) := by
  let Q_set : Finset (Fin (2 ^ quotBitsWhp U N)) := U_set.image (keyQuotFin hnU)
  have hs1 : 1 ≤ 2 ^ bCharWhp N := Nat.one_le_two_pow
  have hcov : min (redWidthWhp U) (redBitsWhp c N) ≤ cTabWhp c * bCharWhp N :=
    min_redWidthWhp_le_mul c U N
  have hind0 := BitPackedDoubleTabulation.isKWiseIndependentHash_evalSalted_of_goodTop
    (M_out := bWhp N) (s_max := 1) hs1 hcov hgood
  have hinj : Function.Injective (fun q : Q_set => ((⟨0, Nat.zero_lt_one⟩ : Fin 1), q)) :=
    fun _ _ h => Prod.mk.inj h |>.2
  have hind := IsKWiseIndependentHash.comp hind0
    (e := fun q : Q_set => ((⟨0, Nat.zero_lt_one⟩ : Fin 1), q)) hinj
  refine kwise_feistel_bucket_tail_le hth hnU U_set hm1 hcard_U _ hind
    b hb (fun T₂ u => epochBucket c U N (α, T₁, T₂) u = b) fun T₂ u _ hmem => ?_
  let v := BitPackedDoubleTabulation.evalSalted (2 ^ quotBitsWhp U N) (redWidthWhp U)
    (redBitsWhp c N) (cTabWhp c) (dTabWhp c) (bCharWhp N) (bWhp N) 1 (α, T₁, T₂)
    (⟨0, Nat.zero_lt_one⟩, keyQuotFin hnU u)
  have heq_val : epochBucket c U N (α, T₁, T₂) u = (v.val ^^^ keyLow (bWhp N) u.val) := by
    have hfin : (⟨keyQuotient (bWhp N) u.val % 2 ^ quotBitsWhp U N,
        Nat.mod_lt _ (Nat.two_pow_pos _)⟩ : Fin (2 ^ quotBitsWhp U N)) = keyQuotFin hnU u := by
      apply Fin.ext
      exact Nat.mod_eq_of_lt (keyQuotient_bWhp_lt hnU u)
    have hbkt : bktHash c U N (α, T₁, T₂) (keyQuotient (bWhp N) u.val) = v.val := by
      unfold bktHash
      dsimp only [v]
      rw [hfin]
    unfold epochBucket feistelBucket
    rw [hbkt, Nat.mod_eq_of_lt v.isLt]
  rw [heq_val]

/-- Outer-measure bound for a product seed `(α, T₁, T₂)` where `GoodTop` holds w.p. `1 - ε_top` and,
conditioned on `GoodTop`, `BadBot α T₁` holds on `T₂` w.p. `≤ ε_bot`. -/
private theorem uniform_seed_bad_le_add {w₀ c_tab d b_char M_out : ℕ}
    (GoodT : Fin (2 ^ (w₀ - 1)) → DoubleTabTopSeed (c_tab + 1) d b_char → Prop)
    (Bad : BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out → Prop)
    {ε_top ε_bot : ℝ≥0∞}
    (htop : PMF.toOuterMeasure
      (PMF.uniformOfFintype (BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out))
      {θ | ¬GoodT θ.1 θ.top} ≤ ε_top)
    (hbot : ∀ α T₁, GoodT α T₁ →
      PMF.toOuterMeasure (PMF.uniformOfFintype (DoubleTabBotSeed d b_char M_out))
        {T₂ | Bad (α, T₁, T₂)} ≤ ε_bot) :
    PMF.toOuterMeasure
      (PMF.uniformOfFintype (BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out))
      {θ | Bad θ} ≤ ε_top + ε_bot := by
  classical
  let μ := PMF.uniformOfFintype (BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out)
  let S₁ : Set (BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out) := {θ | ¬GoodT θ.1 θ.top}
  let S₂ : Set (BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out) :=
    {θ | GoodT θ.1 θ.top ∧ Bad θ}
  have hsub : ({θ | Bad θ} : Set _) ⊆ S₁ ∪ S₂ := by
    intro θ hθ
    rw [Set.mem_ofPred_eq] at hθ
    by_cases hg : GoodT θ.1 θ.top
    · exact Or.inr ⟨hg, hθ⟩
    · exact Or.inl hg
  have hunion : μ.toOuterMeasure {θ | Bad θ} ≤ μ.toOuterMeasure S₁ + μ.toOuterMeasure S₂ :=
    calc μ.toOuterMeasure {θ | Bad θ}
        ≤ μ.toOuterMeasure (S₁ ∪ S₂) := μ.toOuterMeasure.mono hsub
      _ ≤ μ.toOuterMeasure S₁ + μ.toOuterMeasure S₂ := MeasureTheory.measure_union_le S₁ S₂
  refine hunion.trans (add_le_add htop ?_)
  -- Factor `Seed = α × T₁ × T₂` into `(α × T₁)` and `T₂` (`0` projection chains)
  let TopPair := Fin (2 ^ (w₀ - 1)) × DoubleTabTopSeed (c_tab + 1) d b_char
  let eAssoc : TopPair × DoubleTabBotSeed d b_char M_out ≃
      BitPackedDoubleTabulation.Seed w₀ c_tab d b_char M_out :=
    { toFun := fun ⟨⟨α, T₁⟩, T₂⟩ => (α, T₁, T₂)
      invFun := fun ⟨α, T₁, T₂⟩ => ((α, T₁), T₂)
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _, _⟩ => rfl }
  have hμ_eq : μ = (PMF.uniformOfFintype TopPair).bind fun p =>
      (PMF.uniformOfFintype (DoubleTabBotSeed d b_char M_out)).map fun T₂ => eAssoc (p, T₂) := by
    dsimp only [μ]
    rw [← PMF.uniformOfFintype_map_equiv eAssoc, ← PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
  dsimp only [S₂]
  rw [hμ_eq, PMF.toOuterMeasure_bind_apply]
  calc ∑' p : TopPair, PMF.uniformOfFintype TopPair p *
        ((PMF.uniformOfFintype (DoubleTabBotSeed d b_char M_out)).map
          fun T₂ => eAssoc (p, T₂)).toOuterMeasure {θ | GoodT θ.1 θ.top ∧ Bad θ}
      ≤ ∑' p : TopPair, PMF.uniformOfFintype TopPair p * ε_bot := by
        gcongr with p
        rcases p with ⟨α, T₁⟩
        rw [PMF.toOuterMeasure_map_apply]
        by_cases hg : GoodT α T₁
        · refine ((PMF.uniformOfFintype _).toOuterMeasure.mono ?_).trans (hbot α T₁ hg)
          intro T₂ hT₂; exact hT₂.2
        · have hemp : (fun T₂ => eAssoc ((α, T₁), T₂)) ⁻¹' {θ | GoodT θ.1 θ.top ∧ Bad θ} = ∅ := by
            ext T₂; simp [eAssoc, hg]
          rw [hemp, MeasureTheory.measure_empty]
          exact zero_le
    _ = ε_bot := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Probability bound on `¬GoodBktSeed`: at most `75 * (N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)`. -/
private theorem uniform_not_goodBktSeed_le {c U N : ℕ} (hth : whpThreshold c ≤ N) (hnU : N ≤ U)
    (win : EpochWindowSpec c U N) :
    (PMF.uniformOfFintype (BktSeed c U N)).toOuterMeasure
      {θ_bkt | ¬GoodBktSeed win θ_bkt} ≤
      75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
  let Q_fin : Fin U → Fin (2 ^ quotBitsWhp U N) := keyQuotFin hnU
  let W_Q : Finset (Fin (2 ^ quotBitsWhp U N)) := win.allKeys.image Q_fin
  have hWQ_card : #W_Q ≤ 8 * N := card_image_le.trans win.card_allKeys_le
  let GoodT := BitPackedDoubleTabulation.GoodTop (2 ^ quotBitsWhp U N) (redWidthWhp U)
    (redBitsWhp c N) (cTabWhp c) (dTabWhp c) (bCharWhp N) (kIndepWhp c N) W_Q
  have htop := not_goodTop_whp_le (M_out := bWhp N) hth
    (redWidthWhp_pos U) (two_pow_quotBitsWhp_le_redWidthWhp U N) W_Q hWQ_card
  have hN_pos : 0 < N := (whpThreshold_pos c).trans_le hth
  have hN_ne : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
  have hN_top : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hM_le_N : numBucketsWhp N ≤ N := by
    have h12 := numBucketsWhp_mul_scale_pow12_le hth
    exact (Nat.le_mul_of_pos_right _ (Nat.one_le_pow 12 _ (slabScale_pos N))).trans h12
  have hbot : ∀ α T₁, GoodT α T₁ →
      (PMF.uniformOfFintype (DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (bWhp N))).toOuterMeasure
        {T₂ | ¬GoodBktSeed win (α, T₁, T₂)} ≤
        10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
    intro α T₁ hgood
    let μ_b := (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (bWhp N))).toOuterMeasure
    let E_snap : Set _ := {T₂ | ∃ t : Fin win.numSnaps, ∃ b < numBucketsWhp N,
      capMaxWhp N < #((win.snaps t).filter fun u => epochBucket c U N (α, T₁, T₂) u = b)}
    let E_sub : Set _ := {T₂ | ∃ e : Fin win.numSubs, ∃ b < numBucketsWhp N,
      2 * capMaxWhp N < #((win.subUnions e).filter fun u => epochBucket c U N (α, T₁, T₂) u = b)}
    have hcov_bad : ({T₂ | ¬GoodBktSeed win (α, T₁, T₂)} : Set _) ⊆ E_snap ∪ E_sub := by
      intro T₂ h; rw [Set.mem_ofPred_eq, GoodBktSeed, not_and_or] at h
      rcases h with h1 | h2
      · left; push Not at h1; exact h1
      · right; push Not at h2; exact h2
    -- Bound `μ_b E_snap`:
    have hsnap_le : μ_b E_snap ≤ 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
      have hunion1 : E_snap ⊆ ⋃ (t : Fin win.numSnaps) (b : Fin (numBucketsWhp N)),
          {T₂ | 1 * capMaxWhp N <
            #((win.snaps t).filter fun u => epochBucket c U N (α, T₁, T₂) u = b.val)} := by
        intro T₂ ⟨t, b, hb, hgt⟩
        exact Set.mem_iUnion.mpr ⟨t, Set.mem_iUnion.mpr ⟨⟨b, hb⟩, by simpa using hgt⟩⟩
      refine (μ_b.mono hunion1).trans ?_
      refine (MeasureTheory.measure_iUnion_fintype_le μ_b _).trans ?_
      have hper_t : ∀ t : Fin win.numSnaps,
          μ_b (⋃ b : Fin (numBucketsWhp N),
            {T₂ | 1 * capMaxWhp N <
              #((win.snaps t).filter fun u => epochBucket c U N (α, T₁, T₂) u = b.val)}) ≤
          (numBucketsWhp N : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
        intro t
        refine (MeasureTheory.measure_iUnion_fintype_le μ_b _).trans ?_
        have hg_sub : BitPackedDoubleTabulation.GoodTop (2 ^ quotBitsWhp U N) (redWidthWhp U)
            (redBitsWhp c N) (cTabWhp c) (dTabWhp c) (bCharWhp N) (kIndepWhp c N)
            ((win.snaps t).image Q_fin) α T₁ :=
          ⟨hgood.1.mono (Finset.coe_subset.mpr (Finset.image_subset_image (win.snap_sub t))),
            hgood.2⟩
        calc ∑ b : Fin (numBucketsWhp N), μ_b _
            ≤ ∑ _b : Fin (numBucketsWhp N), ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) :=
              Finset.sum_le_sum fun b _ =>
                bot_bucket_load_gt_le hth hnU (win.snaps t) le_rfl (by decide)
                  (by simpa using win.card_snap_le t) hg_sub b.val b.isLt
          _ = (numBucketsWhp N : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
              rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc ∑ t : Fin win.numSnaps, μ_b _
          ≤ ∑ _t : Fin win.numSnaps, (numBucketsWhp N : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) :=
            Finset.sum_le_sum fun t _ => hper_t t
        _ = ((win.numSnaps * numBucketsWhp N : ℕ) : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
        _ ≤ (5 * (N : ℝ≥0∞) ^ 2) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            gcongr
            have hcnt : win.numSnaps * numBucketsWhp N ≤ 5 * N ^ 2 := by
              have hs_le : win.numSnaps ≤ 5 * N := by have := win.numSnaps_le; omega
              calc win.numSnaps * numBucketsWhp N ≤ (5 * N) * N := Nat.mul_le_mul hs_le hM_le_N
                _ = 5 * N ^ 2 := by ring
            exact_mod_cast hcnt
        _ = 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
            rw [show cEff c + 4 = 2 + (cEff c + 2) by omega, pow_add,
              mul_assoc 5, ← mul_assoc ((N : ℝ≥0∞) ^ 2), ← ENNReal.inv_pow,
              ENNReal.mul_inv_cancel (pow_ne_zero 2 hN_ne) (ENNReal.pow_ne_top hN_top), one_mul]
    -- Bound `μ_b E_sub` identically:
    have hsub_le : μ_b E_sub ≤ 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
      have hunion2 : E_sub ⊆ ⋃ (e : Fin win.numSubs) (b : Fin (numBucketsWhp N)),
          {T₂ | 2 * capMaxWhp N <
            #((win.subUnions e).filter fun u => epochBucket c U N (α, T₁, T₂) u = b.val)} := by
        intro T₂ ⟨e, b, hb, hgt⟩
        exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hgt⟩⟩
      refine (μ_b.mono hunion2).trans ?_
      refine (MeasureTheory.measure_iUnion_fintype_le μ_b _).trans ?_
      have hper_e : ∀ e : Fin win.numSubs,
          μ_b (⋃ b : Fin (numBucketsWhp N),
            {T₂ | 2 * capMaxWhp N <
              #((win.subUnions e).filter fun u => epochBucket c U N (α, T₁, T₂) u = b.val)}) ≤
          (numBucketsWhp N : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
        intro e
        refine (MeasureTheory.measure_iUnion_fintype_le μ_b _).trans ?_
        have hg_sub : BitPackedDoubleTabulation.GoodTop (2 ^ quotBitsWhp U N) (redWidthWhp U)
            (redBitsWhp c N) (cTabWhp c) (dTabWhp c) (bCharWhp N) (kIndepWhp c N)
            ((win.subUnions e).image Q_fin) α T₁ :=
          ⟨hgood.1.mono (Finset.coe_subset.mpr (Finset.image_subset_image (win.subUnion_sub e))),
            hgood.2⟩
        calc ∑ b : Fin (numBucketsWhp N), μ_b _
            ≤ ∑ _b : Fin (numBucketsWhp N), ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) :=
              Finset.sum_le_sum fun b _ =>
                bot_bucket_load_gt_le hth hnU (win.subUnions e) (by decide) le_rfl
                  (win.card_subUnion_le e) hg_sub b.val b.isLt
          _ = (numBucketsWhp N : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
              rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc ∑ e : Fin win.numSubs, μ_b _
          ≤ ∑ _e : Fin win.numSubs, (numBucketsWhp N : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) :=
            Finset.sum_le_sum fun e _ => hper_e e
        _ = ((win.numSubs * numBucketsWhp N : ℕ) : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul, mul_assoc]
        _ ≤ (5 * (N : ℝ≥0∞) ^ 2) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            gcongr
            have hcnt : win.numSubs * numBucketsWhp N ≤ 5 * N ^ 2 := by
              have hs_le : win.numSubs ≤ 5 * N := by have := win.numSubs_le; omega
              calc win.numSubs * numBucketsWhp N ≤ (5 * N) * N := Nat.mul_le_mul hs_le hM_le_N
                _ = 5 * N ^ 2 := by ring
            exact_mod_cast hcnt
        _ = 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
            rw [show cEff c + 4 = 2 + (cEff c + 2) by omega, pow_add,
              mul_assoc 5, ← mul_assoc ((N : ℝ≥0∞) ^ 2), ← ENNReal.inv_pow,
              ENNReal.mul_inv_cancel (pow_ne_zero 2 hN_ne) (ENNReal.pow_ne_top hN_top), one_mul]
    calc μ_b {T₂ | ¬GoodBktSeed win (α, T₁, T₂)}
        ≤ μ_b (E_snap ∪ E_sub) := μ_b.mono hcov_bad
      _ ≤ μ_b E_snap + μ_b E_sub := MeasureTheory.measure_union_le E_snap E_sub
      _ ≤ 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) + 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) :=
          add_le_add hsnap_le hsub_le
      _ = 10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by ring
  have hsum := uniform_seed_bad_le_add GoodT (fun θ => ¬GoodBktSeed win θ) htop hbot
  refine hsum.trans ?_
  have hle_inv : (N : ℝ≥0∞)⁻¹ ^ (cEff c + 3) ≤ (N : ℝ≥0∞)⁻¹ ^ (cEff c + 2) := by
    rw [show cEff c + 3 = (cEff c + 2) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_right zero_le
      (ENNReal.inv_le_one.mpr (by exact_mod_cast hN_pos))
  calc 65 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) + 10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2))
      ≤ 65 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) + 10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by gcongr
    _ = 75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by ring

/-- Conditional on ANY `θ_bkt` satisfying `GoodBktSeed win θ_bkt`, a uniform `θ_fp : FpSeed c U N`
fails the `GoodEpochSeeds` conditions w.p. at most `75 * (N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)`. -/
private theorem uniform_not_goodFp_given_bkt_le {c U N : ℕ} (hth : whpThreshold c ≤ N)
    (win : EpochWindowSpec c U N) {θ_bkt : BktSeed c U N} (hbkt : GoodBktSeed win θ_bkt) :
    (PMF.uniformOfFintype (FpSeed c U N)).toOuterMeasure
      {θ_fp | ¬GoodEpochSeeds win ⟨θ_bkt, θ_fp⟩} ≤
      75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
  classical
  let GoodT := BitPackedDoubleTabulation.GoodTop U (redWidthWhp U) (redBitsWhp c N)
    (cTabWhp c) (dTabWhp c) (bCharWhp N) (kIndepWhp c N) win.allKeys
  have htop := not_goodTop_whp_le (M_out := fpBitsWhp N) hth
    (redWidthWhp_pos U) (le_two_pow_redWidthWhp U)
    win.allKeys win.card_allKeys_le
  have hN_pos : 0 < N := (whpThreshold_pos c).trans_le hth
  have hN_ne : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr hN_pos.ne'
  have hN_top : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have hM_le_N : numBucketsWhp N ≤ N :=
    (Nat.le_mul_of_pos_right _ (Nat.one_le_pow 12 _ (slabScale_pos N))).trans
      (numBucketsWhp_mul_scale_pow12_le hth)
  set L := slabScale N
  have hL2 := two_le_slabScale N
  have hN_le_2L : N ≤ 2 ^ L := self_le_two_pow_slabScale N
  have hs_le_bchar := sMaxWhp_le_two_pow_bCharWhp hth
  have hcov := min_redWidthWhp_le_mul c U N
  have hbot : ∀ α T₁, GoodT α T₁ →
      PMF.toOuterMeasure
        (PMF.uniformOfFintype (DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (fpBitsWhp N)))
        {T₂ | ¬GoodEpochSeeds win ⟨θ_bkt, (α, T₁, T₂)⟩} ≤
        10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
    intro α T₁ hgood
    have hinj_rKey : Set.InjOn (rKeyOf c U N (α, T₁, Classical.arbitrary _))
        (win.allKeys : Set (Fin U)) := by
      intro u₁ hu₁ u₂ hu₂ heq
      exact hgood.1 hu₁ hu₂ (Fin.ext heq)
    have hind := BitPackedDoubleTabulation.isKWiseIndependentHash_evalSalted_of_goodTop
      (M_out := fpBitsWhp N) hs_le_bchar hcov hgood
    let μ_f := (PMF.uniformOfFintype
      (DoubleTabBotSeed (dTabWhp c) (bCharWhp N) (fpBitsWhp N))).toOuterMeasure
    let E_salt : Set _ := {T₂ | ∃ e : Fin win.numSubs, ∃ b < numBucketsWhp N,
      ∀ s : Fin (sMaxWhp c N), ∃ u ∈ win.subUnions e, ∃ v ∈ win.subUnions e,
        epochBucket c U N θ_bkt u = b ∧ epochBucket c U N θ_bkt v = b ∧ u ≠ v ∧
          fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v}
    let E_buf : Set _ := {T₂ | ∃ e : Fin win.numSubs,
      2 * sMaxWhp c N ≤ #((win.subBatches e).filter fun u =>
        ∃ v ∈ (win.subUnions e).filter
            (fun v' => epochBucket c U N θ_bkt v' = epochBucket c U N θ_bkt u),
          u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
            fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v)}
    have hcov_bad : ({T₂ | ¬GoodEpochSeeds win ⟨θ_bkt, (α, T₁, T₂)⟩} : Set _) ⊆
        E_salt ∪ E_buf := by
      intro T₂ h
      rw [Set.mem_ofPred_eq, GoodEpochSeeds] at h
      have hinj_T₂ : Set.InjOn (rKeyOf c U N (α, T₁, T₂)) (win.allKeys : Set (Fin U)) := hinj_rKey
      by_cases hs_ok : ∀ e : Fin win.numSubs, ∀ b < numBucketsWhp N,
          ∃ s : Fin (sMaxWhp c N), ∀ u ∈ win.subUnions e, ∀ v ∈ win.subUnions e,
            epochBucket c U N θ_bkt u = b → epochBucket c U N θ_bkt v = b → u ≠ v →
              fpHash c U N (α, T₁, T₂) s u ≠ fpHash c U N (α, T₁, T₂) s v
      · right
        dsimp only [E_buf, Set.mem_ofPred_eq]
        by_contra hnb
        push Not at hnb
        exact h ⟨hbkt, hinj_T₂, hs_ok, hnb⟩
      · left
        push Not at hs_ok
        obtain ⟨e, b, hb, hall⟩ := hs_ok
        refine ⟨e, b, hb, fun s => ?_⟩
        obtain ⟨u, hu, v, hv, hub, hvb, hne, hcoll⟩ := hall s
        exact ⟨u, hu, v, hv, hub, hvb, hne, hcoll⟩
    -- 1. Salt collision bound via `dens_forall_salt_exists_collision_le`:
    have hfp_card : (Fintype.card (Fin (2 ^ fpBitsWhp N)) : ℝ) = ((L ^ 36 : ℕ) : ℝ) := by
      rw [Fintype.card_fin]
      exact_mod_cast fpBitsWhp_pow_eq N
    have hsalt_le : μ_f E_salt ≤ 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
      have hunion1 : E_salt ⊆ ⋃ (e : Fin win.numSubs) (b : Fin (numBucketsWhp N)),
          {T₂ | ∀ s : Fin (sMaxWhp c N), ∃ u ∈ win.subUnions e, ∃ v ∈ win.subUnions e,
            epochBucket c U N θ_bkt u = b.val ∧ epochBucket c U N θ_bkt v = b.val ∧ u ≠ v ∧
              fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v} := by
        intro T₂ ⟨e, b, hb, hs⟩
        exact Set.mem_iUnion.mpr ⟨e, Set.mem_iUnion.mpr ⟨⟨b, hb⟩, hs⟩⟩
      refine (μ_f.mono hunion1).trans ?_
      refine (MeasureTheory.measure_iUnion_fintype_le μ_f _).trans ?_
      have hper_tb : ∀ (e : Fin win.numSubs) (b : Fin (numBucketsWhp N)),
          μ_f {T₂ | ∀ s : Fin (sMaxWhp c N), ∃ u ∈ win.subUnions e, ∃ v ∈ win.subUnions e,
            epochBucket c U N θ_bkt u = b.val ∧ epochBucket c U N θ_bkt v = b.val ∧ u ≠ v ∧
              fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v} ≤
            ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
        intro e b
        let S_tb : Finset win.allKeys := win.allKeys.attach.filter fun u =>
          u.val ∈ win.subUnions e ∧ epochBucket c U N θ_bkt u.val = b.val
        have hcard_Stb : #S_tb ≤ 2 * capMaxWhp N := by
          have hinj_val : Set.InjOn Subtype.val (S_tb : Set win.allKeys) :=
            fun _ _ _ _ h => Subtype.ext h
          have himg : S_tb.image Subtype.val ⊆
              (win.subUnions e).filter (fun u => epochBucket c U N θ_bkt u = b.val) := by
            intro u hu
            obtain ⟨x, hx, rfl⟩ := mem_image.mp hu
            exact mem_filter.mpr (mem_filter.mp hx).2
          calc #S_tb = #(S_tb.image Subtype.val) := (card_image_of_injOn hinj_val).symm
            _ ≤ #((win.subUnions e).filter fun u => epochBucket c U N θ_bkt u = b.val) :=
              card_le_card himg
            _ ≤ 2 * capMaxWhp N := hbkt.2 e b.val b.isLt
        have hd_salt := hind.dens_forall_salt_exists_collision_le S_tb
        have hsub_ev : (Finset.univ.filter fun T₂ =>
            ∀ s : Fin (sMaxWhp c N), ∃ u ∈ win.subUnions e, ∃ v ∈ win.subUnions e,
              epochBucket c U N θ_bkt u = b.val ∧ epochBucket c U N θ_bkt v = b.val ∧ u ≠ v ∧
                fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v) ⊆
            (Finset.univ.filter fun T₂ =>
              ∀ s : Fin (sMaxWhp c N), ∃ u ∈ S_tb, ∃ v ∈ S_tb, u ≠ v ∧
                BitPackedDoubleTabulation.evalSalted U (redWidthWhp U) (redBitsWhp c N)
                  (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) (sMaxWhp c N) (α, T₁, T₂)
                  (s, u.val) =
                BitPackedDoubleTabulation.evalSalted U (redWidthWhp U) (redBitsWhp c N)
                  (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) (sMaxWhp c N) (α, T₁, T₂)
                  (s, v.val)) := by
          intro T₂ hT₂
          simp only [mem_filter, mem_univ, true_and] at hT₂ ⊢
          intro s
          obtain ⟨u, hu, v, hv, hub, hvb, hne, hcoll⟩ := hT₂ s
          refine ⟨⟨u, win.subUnion_sub e hu⟩,
            mem_filter.mpr ⟨mem_attach _ _, hu, hub⟩,
            ⟨v, win.subUnion_sub e hv⟩,
            mem_filter.mpr ⟨mem_attach _ _, hv, hvb⟩,
            fun heq => hne (congrArg Subtype.val heq), hcoll⟩
        have hbase_r : ((#S_tb : ℝ) ^ 2 / Fintype.card (Fin (2 ^ fpBitsWhp N))) ≤ (1 : ℝ) / 2 := by
          rw [hfp_card, div_le_iff₀ (by positivity)]
          have hnat : 2 * #S_tb ^ 2 ≤ L ^ 36 := by
            have hc1 : #S_tb ≤ 8 * L ^ 12 := by unfold capMaxWhp at hcard_Stb; dsimp only [L]; omega
            have h128 : 128 ≤ L ^ 12 := by
              calc 128 ≤ 2 ^ 12 := by decide
                _ ≤ L ^ 12 := Nat.pow_le_pow_left hL2 12
            calc 2 * #S_tb ^ 2 ≤ 2 * (8 * L ^ 12) ^ 2 :=
                  Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hc1 2)
              _ = 128 * L ^ 24 := by ring
              _ ≤ L ^ 12 * L ^ 24 := Nat.mul_le_mul_right _ h128
              _ = L ^ 36 := by ring
          have hnat_r : (2 : ℝ) * (#S_tb : ℝ) ^ 2 ≤ ((L ^ 36 : ℕ) : ℝ) := by exact_mod_cast hnat
          linarith
        have hpow_r : ((#S_tb : ℝ) ^ 2 / Fintype.card (Fin (2 ^ fpBitsWhp N))) ^ sMaxWhp c N ≤
            (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) := by
          calc ((#S_tb : ℝ) ^ 2 / Fintype.card (Fin (2 ^ fpBitsWhp N))) ^ sMaxWhp c N
              ≤ ((1 : ℝ) / 2) ^ sMaxWhp c N :=
                pow_le_pow_left₀ (by positivity) hbase_r _
            _ = (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) := by
                have hm_eq : sMaxWhp c N = L * (cEff c + 4) := by
                  unfold sMaxWhp; dsimp only [L]; ring
                rw [hm_eq, pow_mul, one_div, inv_pow, Nat.cast_pow, Nat.cast_ofNat]
        have hdens : (Finset.dens _ : ℝ) ≤ (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) :=
          ((NNRat.cast_le (K := ℝ)).mpr (Finset.dens_le_dens hsub_ev)).trans
            (hd_salt.trans hpow_r)
        have hmeas := toOuterMeasure_uniformOfFintype_le_of_dens_le _ hdens
        refine hmeas.trans ?_
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_natCast]
        exact pow_le_pow_left' (ENNReal.inv_le_inv.mpr (by exact_mod_cast hN_le_2L)) _
      calc ∑ e : Fin win.numSubs, μ_f _
          ≤ ∑ e : Fin win.numSubs, ∑ b : Fin (numBucketsWhp N), μ_f _ :=
            Finset.sum_le_sum fun e _ => MeasureTheory.measure_iUnion_fintype_le μ_f _
        _ ≤ ∑ _e : Fin win.numSubs, ∑ _b : Fin (numBucketsWhp N),
              ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) :=
            Finset.sum_le_sum fun e _ => Finset.sum_le_sum fun b _ => hper_tb e b
        _ = ((win.numSubs * numBucketsWhp N : ℕ) : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul,
              mul_assoc]
        _ ≤ (5 * (N : ℝ≥0∞) ^ 2) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            gcongr
            have hs_le : win.numSubs ≤ 5 * N := by have := win.numSubs_le; omega
            have hcnt : win.numSubs * numBucketsWhp N ≤ 5 * N ^ 2 :=
              calc win.numSubs * numBucketsWhp N ≤ (5 * N) * N := Nat.mul_le_mul hs_le hM_le_N
                _ = 5 * N ^ 2 := by ring
            exact_mod_cast hcnt
        _ = 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
            rw [show cEff c + 4 = 2 + (cEff c + 2) by omega, pow_add,
              mul_assoc 5, ← mul_assoc ((N : ℝ≥0∞) ^ 2), ← ENNReal.inv_pow,
              ENNReal.mul_inv_cancel (pow_ne_zero 2 hN_ne) (ENNReal.pow_ne_top hN_top), one_mul]
    -- 2. Sub-epoch `BufTrie` collision budget via `dens_card_local_salt_colliding_ge_le`:
    have hbuf_le : μ_f E_buf ≤ 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
      have hunion2 : E_buf ⊆ ⋃ e : Fin win.numSubs,
          {T₂ | 2 * sMaxWhp c N ≤ #((win.subBatches e).filter fun u =>
            ∃ v ∈ (win.subUnions e).filter
                (fun v' => epochBucket c U N θ_bkt v' = epochBucket c U N θ_bkt u),
              u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
                fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v)} := by
        intro T₂ ⟨e, he⟩; exact Set.mem_iUnion.mpr ⟨e, he⟩
      refine (μ_f.mono hunion2).trans ?_
      refine (MeasureTheory.measure_iUnion_fintype_le μ_f _).trans ?_
      have hper_e : ∀ e : Fin win.numSubs,
          μ_f {T₂ | 2 * sMaxWhp c N ≤ #((win.subBatches e).filter fun u =>
            ∃ v ∈ (win.subUnions e).filter
                (fun v' => epochBucket c U N θ_bkt v' = epochBucket c U N θ_bkt u),
              u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
                fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v)} ≤
            ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
        intro e
        let Q_e : Finset win.allKeys := win.allKeys.attach.filter fun u => u.val ∈ win.subBatches e
        let W_of : win.allKeys → Finset win.allKeys := fun u =>
          win.allKeys.attach.filter fun v =>
            v.val ∈ win.subUnions e ∧ epochBucket c U N θ_bkt v.val = epochBucket c U N θ_bkt u.val
        have hQe_card : #Q_e ≤ qEpochWhp N := by
          have hinj_v : Set.InjOn Subtype.val (Q_e : Set win.allKeys) :=
            fun _ _ _ _ h => Subtype.ext h
          have himg : Q_e.image Subtype.val ⊆ win.subBatches e := by
            intro x hx; obtain ⟨y, hy, rfl⟩ := mem_image.mp hx; exact (mem_filter.mp hy).2
          exact (card_image_of_injOn hinj_v).symm.trans_le
            ((card_le_card himg).trans (win.card_subBatch_le e))
        have hW_cap : ∀ u ∈ Q_e, #(W_of u) ≤ 2 * capMaxWhp N := by
          intro u _
          have hinj_v : Set.InjOn Subtype.val (W_of u : Set win.allKeys) :=
            fun _ _ _ _ h => Subtype.ext h
          have himg : (W_of u).image Subtype.val ⊆ (win.subUnions e).filter
              (fun v' => epochBucket c U N θ_bkt v' = epochBucket c U N θ_bkt u.val) := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := mem_image.mp hx
            exact mem_filter.mpr (mem_filter.mp hy).2
          exact (card_image_of_injOn hinj_v).symm.trans_le
            ((card_le_card himg).trans (hbkt.2 e _ (epochBucket_lt c U N θ_bkt u.val)))
        have hd_loc := hind.dens_card_local_salt_colliding_ge_le Q_e W_of hW_cap
        have hsub_ev : (Finset.univ.filter fun T₂ =>
            2 * sMaxWhp c N ≤ #((win.subBatches e).filter fun u =>
              ∃ v ∈ (win.subUnions e).filter
                  (fun v' => epochBucket c U N θ_bkt v' = epochBucket c U N θ_bkt u),
                u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
                  fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v)) ⊆
            (Finset.univ.filter fun T₂ =>
              2 * sMaxWhp c N ≤ #(Q_e.filter fun u =>
                ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
                  BitPackedDoubleTabulation.evalSalted U (redWidthWhp U) (redBitsWhp c N)
                    (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) (sMaxWhp c N) (α, T₁, T₂)
                    (s, u.val) =
                  BitPackedDoubleTabulation.evalSalted U (redWidthWhp U) (redBitsWhp c N)
                    (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) (sMaxWhp c N) (α, T₁, T₂)
                    (s, v.val))) := by
          intro T₂ hT₂
          let B_orig := (win.subBatches e).filter fun u =>
            ∃ v ∈ (win.subUnions e).filter
                (fun v' => epochBucket c U N θ_bkt v' = epochBucket c U N θ_bkt u),
              u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
                fpHash c U N (α, T₁, T₂) s u = fpHash c U N (α, T₁, T₂) s v
          let B_sub := Q_e.filter fun u =>
            ∃ v ∈ W_of u, u ≠ v ∧ ∃ s : Fin (sMaxWhp c N),
              BitPackedDoubleTabulation.evalSalted U (redWidthWhp U) (redBitsWhp c N)
                (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) (sMaxWhp c N) (α, T₁, T₂)
                (s, u.val) =
              BitPackedDoubleTabulation.evalSalted U (redWidthWhp U) (redBitsWhp c N)
                (cTabWhp c) (dTabWhp c) (bCharWhp N) (fpBitsWhp N) (sMaxWhp c N) (α, T₁, T₂)
                (s, v.val)
          have hT₂' : 2 * sMaxWhp c N ≤ #B_orig := (mem_filter.mp hT₂).2
          refine mem_filter.mpr ⟨mem_univ _, hT₂'.trans ?_⟩
          have hsub_img : B_orig ⊆ B_sub.image Subtype.val := by
            intro u hu
            obtain ⟨hu_b, v, hv_f, hne_uv, s, hcoll⟩ := mem_filter.mp hu
            obtain ⟨hv_u, hb_eq⟩ := mem_filter.mp hv_f
            have hu_all : u ∈ win.allKeys := win.subUnion_sub e (win.subBatch_sub e hu_b)
            have hv_all : v ∈ win.allKeys := win.subUnion_sub e hv_u
            refine mem_image.mpr ⟨⟨u, hu_all⟩, ?_, rfl⟩
            refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_attach _ _, hu_b⟩,
              ⟨v, hv_all⟩, mem_filter.mpr ⟨mem_attach _ _, hv_u, hb_eq⟩,
              fun heq => hne_uv (congrArg Subtype.val heq), s, hcoll⟩
          exact (card_le_card hsub_img).trans card_image_le
        have hbase_r : (((#Q_e * (2 * capMaxWhp N) * sMaxWhp c N : ℕ) : ℝ) /
            Fintype.card (Fin (2 ^ fpBitsWhp N))) ≤ (1 : ℝ) / 2 := by
          rw [hfp_card, div_le_iff₀ (by positivity)]
          have h16 := mul_cEff_le_slabScale hth
          have hnat : 2 * (#Q_e * (2 * capMaxWhp N) * sMaxWhp c N) ≤ L ^ 36 := by
            have h1 : #Q_e * (2 * capMaxWhp N) ≤ 8 * L ^ 30 := by
              calc #Q_e * (2 * capMaxWhp N) ≤ L ^ 18 * (8 * L ^ 12) :=
                    Nat.mul_le_mul hQe_card (by unfold capMaxWhp; dsimp only [L]; omega)
                _ = 8 * L ^ 30 := by ring
            have h2 : 16 * sMaxWhp c N ≤ L ^ 2 := by
              unfold sMaxWhp
              dsimp only [L] at h16 ⊢
              calc 16 * ((cEff c + 4) * L)
                  = (16 * (cEff c + 4)) * L := by ring
                _ ≤ L * L := Nat.mul_le_mul_right L h16
                _ = L ^ 2 := (sq L).symm
            have h3 : L ^ 32 ≤ L ^ 36 := Nat.pow_le_pow_right (by omega) (by decide)
            calc 2 * (#Q_e * (2 * capMaxWhp N) * sMaxWhp c N)
                ≤ 2 * ((8 * L ^ 30) * sMaxWhp c N) :=
                  Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right _ h1)
              _ = L ^ 30 * (16 * sMaxWhp c N) := by ring
              _ ≤ L ^ 30 * L ^ 2 := Nat.mul_le_mul_left _ h2
              _ = L ^ 32 := by ring
              _ ≤ L ^ 36 := h3
          have hnat_r : (2 : ℝ) * ((#Q_e * (2 * capMaxWhp N) * sMaxWhp c N : ℕ) : ℝ) ≤
              ((L ^ 36 : ℕ) : ℝ) := by exact_mod_cast hnat
          linarith only [hnat_r]
        have hpow_r : (((#Q_e * (2 * capMaxWhp N) * sMaxWhp c N : ℕ) : ℝ) /
            Fintype.card (Fin (2 ^ fpBitsWhp N))) ^ sMaxWhp c N ≤
            (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) := by
          calc _ ≤ ((1 : ℝ) / 2) ^ sMaxWhp c N :=
                pow_le_pow_left₀ (by positivity) hbase_r _
            _ = (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) := by
                have hm_eq : sMaxWhp c N = L * (cEff c + 4) := by
                  unfold sMaxWhp; dsimp only [L]; ring
                rw [hm_eq, pow_mul, one_div, inv_pow, Nat.cast_pow, Nat.cast_ofNat]
        have hdens : (Finset.dens _ : ℝ) ≤ (((2 ^ L : ℕ) : ℝ)⁻¹) ^ (cEff c + 4) :=
          ((NNRat.cast_le (K := ℝ)).mpr (Finset.dens_le_dens hsub_ev)).trans
            (hd_loc.trans hpow_r)
        have hmeas := toOuterMeasure_uniformOfFintype_le_of_dens_le _ hdens
        refine hmeas.trans ?_
        rw [ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_inv_of_pos (by positivity),
          ENNReal.ofReal_natCast]
        exact pow_le_pow_left' (ENNReal.inv_le_inv.mpr (by exact_mod_cast hN_le_2L)) _
      calc ∑ e : Fin win.numSubs, μ_f _
          ≤ ∑ _e : Fin win.numSubs, ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) :=
            Finset.sum_le_sum fun e _ => hper_e e
        _ = (win.numSubs : ℝ≥0∞) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ ≤ (5 * (N : ℝ≥0∞) ^ 2) * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 4)) := by
            gcongr
            have hs_le : win.numSubs ≤ 5 * N ^ 2 := by
              have h1 : win.numSubs ≤ 5 * N := by have := win.numSubs_le; omega
              calc win.numSubs ≤ 5 * N := h1
                _ ≤ (5 * N) * N := Nat.le_mul_of_pos_right _ hN_pos
                _ = 5 * N ^ 2 := by ring
            exact_mod_cast hs_le
        _ = 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
            rw [show cEff c + 4 = 2 + (cEff c + 2) by omega, pow_add,
              mul_assoc 5, ← mul_assoc ((N : ℝ≥0∞) ^ 2), ← ENNReal.inv_pow,
              ENNReal.mul_inv_cancel (pow_ne_zero 2 hN_ne) (ENNReal.pow_ne_top hN_top), one_mul]
    calc μ_f {T₂ | ¬GoodEpochSeeds win ⟨θ_bkt, (α, T₁, T₂)⟩}
        ≤ μ_f (E_salt ∪ E_buf) := μ_f.mono hcov_bad
      _ ≤ μ_f E_salt + μ_f E_buf := MeasureTheory.measure_union_le E_salt E_buf
      _ ≤ 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) + 5 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) :=
          add_le_add hsalt_le hbuf_le
      _ = 10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by ring
  have hsum := uniform_seed_bad_le_add GoodT (fun θ_fp => ¬GoodEpochSeeds win ⟨θ_bkt, θ_fp⟩)
    htop hbot
  refine hsum.trans ?_
  have hle_inv : (N : ℝ≥0∞)⁻¹ ^ (cEff c + 3) ≤ (N : ℝ≥0∞)⁻¹ ^ (cEff c + 2) := by
    rw [show cEff c + 3 = (cEff c + 2) + 1 by omega, pow_succ]
    exact mul_le_of_le_one_right zero_le
      (ENNReal.inv_le_one.mpr (by exact_mod_cast hN_pos))
  calc 65 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 3)) + 10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2))
      ≤ 65 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) + 10 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by gcongr
    _ = 75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by ring

/-- **Master Epoch Good-Seed Concentration Theorem (`uniform_not_goodEpochSeeds_le`).**
For any `whpThreshold c ≤ N` with `N ≤ U` and any deterministic oblivious trajectory window
`win : EpochWindowSpec c U N`, an independent uniform draw `seeds ← PMF.uniformOfFintype
(EpochHashSeeds c U N)` fails `GoodEpochSeeds win seeds` with probability at most
`((1 : ℝ≥0∞) / 2) * (N : ℝ≥0∞)⁻¹ ^ c`. -/
theorem uniform_not_goodEpochSeeds_le {c U N : ℕ} (hth : whpThreshold c ≤ N) (hnU : N ≤ U)
    (win : EpochWindowSpec c U N) :
    (PMF.uniformOfFintype (EpochHashSeeds c U N)).toOuterMeasure
      {seeds | ¬GoodEpochSeeds win seeds} ≤
      ((1 : ℝ≥0∞) / 2) * ((N : ℝ≥0∞)⁻¹ ^ c) := by
  classical
  have hμ_eq : PMF.uniformOfFintype (EpochHashSeeds c U N) =
      (PMF.uniformOfFintype (BktSeed c U N)).bind fun b =>
        (PMF.uniformOfFintype (FpSeed c U N)).map fun f => EpochHashSeeds.mk b f := by
    rw [← PMF.uniformOfFintype_map_equiv (EpochHashSeeds.equivProd c U N).symm,
      ← PMF.uniformOfFintype_prod, PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def, EpochHashSeeds.equivProd]
    rfl
  let BadAll : Set (EpochHashSeeds c U N) := {s | ¬GoodEpochSeeds win s}
  let BadBkt : Set (EpochHashSeeds c U N) := {s | ¬GoodBktSeed win s.bkt}
  let BadFp : Set (EpochHashSeeds c U N) := {s | GoodBktSeed win s.bkt ∧ ¬GoodEpochSeeds win s}
  have hsub : BadAll ⊆ BadBkt ∪ BadFp := by
    intro s hs
    by_cases hb : GoodBktSeed win s.bkt
    · exact Or.inr ⟨hb, hs⟩
    · exact Or.inl hb
  let μ := PMF.uniformOfFintype (EpochHashSeeds c U N)
  have hm_bkt : μ.toOuterMeasure BadBkt ≤ 75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
    have hfst : μ.map EpochHashSeeds.bkt = PMF.uniformOfFintype (BktSeed c U N) := by
      dsimp only [μ]
      have hfn : EpochHashSeeds.bkt = Prod.fst ∘ EpochHashSeeds.equivProd c U N := rfl
      rw [hfn, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]
      exact PMF.uniformOfFintype_prod_map_fst
    have heq_m : μ.toOuterMeasure BadBkt =
        (PMF.uniformOfFintype (BktSeed c U N)).toOuterMeasure {b | ¬GoodBktSeed win b} := by
      rw [← hfst, PMF.toOuterMeasure_map_apply]; rfl
    rw [heq_m]
    exact uniform_not_goodBktSeed_le hth hnU win
  have hm_fp : μ.toOuterMeasure BadFp ≤ 75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
    dsimp only [μ]
    rw [hμ_eq, PMF.toOuterMeasure_bind_apply]
    calc ∑' b : BktSeed c U N, PMF.uniformOfFintype (BktSeed c U N) b *
          ((PMF.uniformOfFintype (FpSeed c U N)).map (EpochHashSeeds.mk b)).toOuterMeasure BadFp
        ≤ ∑' b : BktSeed c U N, PMF.uniformOfFintype (BktSeed c U N) b *
            (75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2))) := by
          gcongr with b
          rw [PMF.toOuterMeasure_map_apply]
          by_cases hb : GoodBktSeed win b
          · refine ((PMF.uniformOfFintype _).toOuterMeasure.mono ?_).trans
              (uniform_not_goodFp_given_bkt_le hth win hb)
            intro f hf; exact hf.2
          · have hemp : EpochHashSeeds.mk b ⁻¹' BadFp = ∅ := by
              ext f; simp [BadFp, hb]
            rw [hemp, MeasureTheory.measure_empty]
            exact zero_le
      _ = 75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
          rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have h150 : μ.toOuterMeasure BadAll ≤ 150 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by
    calc μ.toOuterMeasure BadAll
        ≤ μ.toOuterMeasure (BadBkt ∪ BadFp) := μ.toOuterMeasure.mono hsub
      _ ≤ μ.toOuterMeasure BadBkt + μ.toOuterMeasure BadFp :=
          MeasureTheory.measure_union_le BadBkt BadFp
      _ ≤ 75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) + 75 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) :=
          add_le_add hm_bkt hm_fp
      _ = 150 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2)) := by ring
  refine h150.trans ?_
  -- Absorb `150 * N⁻¹ ^ 2 ≤ 1 / 2` using `N ≥ whpThreshold c ≥ 2 ^ 6553600 ≥ 64`:
  have hN64 : 64 ≤ N := (whpThreshold_ge_64 c).trans hth
  have hN_ne : (N : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hN_top : (N : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top N
  have h150_half : 150 * ((N : ℝ≥0∞)⁻¹ ^ 2) ≤ (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.div_eq_inv_mul, mul_one]
    have hmul : (300 : ℝ≥0∞) ≤ (N : ℝ≥0∞) ^ 2 := by
      have hnat : 300 ≤ N ^ 2 := by nlinarith only [hN64]
      exact_mod_cast hnat
    rw [← ENNReal.inv_pow]
    calc (150 : ℝ≥0∞) * ((N : ℝ≥0∞) ^ 2)⁻¹
        = ((2 : ℝ≥0∞)⁻¹ * 300) * ((N : ℝ≥0∞) ^ 2)⁻¹ := by
          congr 1
          rw [show (300 : ℝ≥0∞) = 2 * 150 by norm_num, ← mul_assoc,
            ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ ((2 : ℝ≥0∞)⁻¹ * (N : ℝ≥0∞) ^ 2) * ((N : ℝ≥0∞) ^ 2)⁻¹ := by gcongr
      _ = (2 : ℝ≥0∞)⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel (pow_ne_zero 2 hN_ne) (ENNReal.pow_ne_top hN_top),
            mul_one]
  have hc_le : c ≤ cEff c := le_max_left c 1
  have hpow_c : (N : ℝ≥0∞)⁻¹ ^ cEff c ≤ (N : ℝ≥0∞)⁻¹ ^ c := by
    obtain ⟨d, hd⟩ : ∃ d, cEff c = c + d := ⟨cEff c - c, by omega⟩
    rw [hd, pow_add]
    exact mul_le_of_le_one_right zero_le
      (pow_le_one₀ zero_le (ENNReal.inv_le_one.mpr (by exact_mod_cast (show 1 ≤ N by omega))))
  calc 150 * ((N : ℝ≥0∞)⁻¹ ^ (cEff c + 2))
      = (150 * ((N : ℝ≥0∞)⁻¹ ^ 2)) * ((N : ℝ≥0∞)⁻¹ ^ cEff c) := by rw [pow_add]; ring
    _ ≤ ((1 : ℝ≥0∞) / 2) * ((N : ℝ≥0∞)⁻¹ ^ c) := by gcongr

/-- Under `EpochCapSafe (whpThreshold c) U N n_t` (`N > 0`), `max n_t (whpThreshold c) ≤ N`, so
`((1 : ℝ≥0∞) / 2) * (N : ℝ≥0∞)⁻¹ ^ c ≤
((1 : ℝ≥0∞) / 2) * ((max n_t (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c`. -/
theorem epochFail_le_half_max_inv_pow {c U N n_t : ℕ} (hN_pos : 0 < N)
    (hsafe : EpochCapSafe (whpThreshold c) U N n_t) :
    ((1 : ℝ≥0∞) / 2) * ((N : ℝ≥0∞)⁻¹ ^ c) ≤
      ((1 : ℝ≥0∞) / 2) * (((max n_t (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹ ^ c) := by
  have hN_ne : N ≠ 0 := hN_pos.ne'
  simp only [EpochCapSafe, hN_ne, ↓reduceIte] at hsafe
  obtain ⟨hth_s, _, _, hnt_s⟩ := hsafe
  have hmax_le : max n_t (whpThreshold c) ≤ N := max_le hnt_s hth_s
  have hpow : ((N : ℝ≥0∞)⁻¹) ^ c ≤ (((max n_t (whpThreshold c) : ℕ) : ℝ≥0∞)⁻¹) ^ c :=
    pow_le_pow_left' (ENNReal.inv_le_inv.mpr (by exact_mod_cast hmax_le)) c
  gcongr

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinctWhp
