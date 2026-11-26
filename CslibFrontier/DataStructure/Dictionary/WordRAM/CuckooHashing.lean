/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Evict
public import CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Rehash
public import CslibFrontier.DataStructure.WordRAM.Randomized.StateTransition
import CslibFrontier.Computability.WordRAM.Randomized.SymbolicExec
import CslibFrontier.Computability.WordRAM.SymbolicExec.Call
import CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Analysis
import CslibFrontier.Tactic.WramOmega

/-!
# Pagh–Rodler Cuckoo Hashing on the Randomized Word RAM

This module packages Pagh and Rodler's two-table cuckoo hashing dictionary [PaghRodler2004] on the
randomized Word RAM (`Cslib.WordRAM.Basis.exact` and `Cslib.WordRAM.Basis.standard`), realizing the
bounded-capacity lookup-and-insert specification `Cslib.DataStructure.Dictionary.spec U V n_max` via
a composable, assumption-free `Cslib.DataStructure.WordRAM.Randomized.StateTransitionImpl`
certificate (`seedSlack := 2`, `potential := 0`) and an expected-amortized sequence theorem
`cuckoo_seq_expected_amortized`.

## Design overview

1. **Memory layout, lookup, and bounded displacement
   (`CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Evict`):**
   - Contiguous `[base, base + space c_exp n_max)` block of `O_{c_exp}(n_max + 1)` words
     (`space_le`) storing a `20`-word header, the regime-switched hash pair (`KWise` below
     `doubleTabThreshold c_exp`, Thorup's `DoubleTabulation` [Thorup2013] at or above it), two
     sub-tables `T₁, T₂` of size `tableSize n_max ≥ 32 * max n_max 4`, and insertion-order arrays
     `insKeys`, `insVals`.
   - Deterministic two-probe lookup `queryCode` (`queryCode_execWithin`) and bounded displacement
     loop `evictLoopCode` (`evictLoopCode_execWithin`).

2. **Las Vegas rehashing and insertion
   (`CslibFrontier.DataStructure.Dictionary.WordRAM.CuckooHashing.Rehash`):**
   - `rehashLoopCode` resamples `(h₁, h₂)`, clears `T₁, T₂`, and replays `insKeys` in insertion
     order until all stored keys settle, yielding an exact conditional-uniform exit law over
     `survivingSeeds` (`rehashLoopCode_execCodeDist`).
   - `insertCode` updates present keys in place and inserts absent keys via bounded displacement
     followed by Las Vegas rehashing on overflow (`insertCode_execCodeDist`).

3. **Unconditional `O_{c_exp}(1)` expected-amortized bounds (`seedSlack = 2`, `potential = 0`):**
   - Because `Dictionary.spec` has no deletion operation and `rehashLoopCode` replays `insKeys` in
     exact insertion order, the surviving-seed set shrinks monotonically across operations, so
     keeping surviving seeds and rejection-sampling uniformly on overflow maintains the exact
     conditional uniform distribution (`unifOn_rehash_eq`), bounded by `2 * seedLaw`.
   - Whenever `U ≤ max n_max 4 ^ c_exp`, `isCuckooHashFamily_tableBits` discharges
     `IsCuckooHashFamily c_exp U n_max (tableBits n_max) (maxEvictions n_max) 3 4` unconditionally
     via `isCuckooHashPair_provableFamily` [PaghRodler2004, Thorup2013], giving `O_{c_exp}(1)`
     worst-case lookup and `O_{c_exp}(1)` expected-amortized insertion (`expectedOpCharge c_exp`)
     independent of `n_max` and `U`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.opCode`: combined operation body dispatching
  between `queryCode` and `insertCode`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.cuckooCode`: `SubroutineCode .exact 19 2`
  packaging `allocSpan`, `initSetup`, and `opCode`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.charge`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.expectedOpCharge`: per-operation amortized
  instruction charges and capacity/universe-independent `O_{c_exp}(1)` charge bound.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.impl`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.implStandard`: composable randomized
  Word-RAM `StateTransitionImpl` certificates over `Basis.exact` and `Basis.standard`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.isCuckooHashFamily_tableBits`: unconditional
  `IsCuckooHashFamily` instance (`C_walk = 3`, `C_reh = 4`) for every `n_max : ℕ` under
  `U ≤ max n_max 4 ^ c_exp`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.charge_le_expectedOpCharge`: bounds `charge`
  by `expectedOpCharge c_exp` whenever `U ≤ max n_max 4 ^ c_exp`.
* `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.cuckoo_steps_expected_amortized`,
  `Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing.cuckoo_seq_expected_amortized`:
  continuation and end-to-end expected-time bounds across arbitrary valid `query`/`insert` histories
  under `U ≤ max n_max 4 ^ c_exp`.

## References

* [R. Pagh and F. F. Rodler, "Cuckoo hashing"][PaghRodler2004] (8 December 2003 author manuscript,
  Section 2.3, "Analysis", pp. 6–10: Lemma 1 on p. 7, Eq. (3) on p. 9, and rehash
  analysis on pp. 9–10).
* [M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High
  Independence"][Thorup2013] (FOCS 2013, pp. 90–99; `arXiv:1311.3121v2`, Theorem 1(a) and Lemma 2
  on pp. 4–5, and Section 3, Theorem 7(a) and Lemmas 8–9 on pp. 11–13).
* [M. Mitzenmacher and E. Upfal, *Probability and Computing*, 2nd ed.][MitzenmacherUpfal2017]
* [J. L. Carter and M. N. Wegman, "Universal classes of hash functions"][CarterWegman1979]
* [M. N. Wegman and J. L. Carter, "New hash functions and their use in authentication and set
  equality"][WegmanCarter1981]
* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to Algorithms*][CLRS2009]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing

open Cslib.DataStructure.Dictionary.CuckooHashing
open Cslib.WordRAM
open Cslib.Probability
open Cslib.Probability.PMF
open Cslib.DataStructure.WordRAM Cslib.DataStructure.WordRAM.Randomized
open Cslib.DataStructure.HashFamily.WordRAM
open scoped ENNReal

/-! ### Register encoding, `opCode`, and amortized charge definitions -/

/-- Standalone register encoding for `Dictionary.Op U`:
* `query u` sets `reg 2 = 0` (selector) and `reg 3 = u.val`.
* `insert u v` sets `reg 2 = 1` (selector), `reg 3 = u.val`, and `reg 4 = v`. -/
@[expose]
def encode {U : ℕ} (o : Dictionary.Op U) (i : Fin 19) : ℕ :=
  match o with
  | .query u =>
    if i = 2 then 0
    else if i = 3 then u.val
    else 0
  | .insert u v =>
    if i = 2 then 1
    else if i = 3 then u.val
    else if i = 4 then v
    else 0

/-- Partial argument-matching predicate for inline callers on `Fin 19 → ℕ`. -/
@[expose]
def argMatch {U : ℕ} (o : Dictionary.Op U) (regs : Fin 19 → ℕ) : Prop :=
  match o with
  | .query u => regs 2 = 0 ∧ regs 3 = u.val
  | .insert u v => regs 2 = 1 ∧ regs 3 = u.val ∧ regs 4 = v

/-- Output decoder reading `Option ((Dictionary.spec U V n_max).Result o)` from final registers. -/
@[expose]
def decode {U V n_max : ℕ} (o : Dictionary.Op U) (regs : Fin 19 → ℕ) :
    Option ((Dictionary.spec U V n_max).Result o) :=
  match o with
  | .query _ => some (decodeOptionNat (regs 2))
  | .insert _ _ => some ()

/-- Combined operation body (`opCode`): dispatches on `reg 2 = 0` (`queryCode`) vs `reg 2 ≠ 0`
(`insertCode`). -/
def opCode (c_exp n_max : ℕ) : Code .exact 19 :=
  .seq (.op (.const 15 0))
  (.branch (.eq 2 15)
    (queryCode c_exp n_max)
    (insertCode c_exp n_max))

private def rehashAmortizedSteps (c_exp n_max U : ℕ) : ℕ :=
  (maxEvictions n_max * evictIterSteps c_exp n_max U + rehashLoopSteps c_exp n_max U + 2) /
    (max n_max 1 * max (maxEvictions n_max) 1) + 1

private def insertCharge (c_exp n_max U C_walk C_reh : ℕ) : ℕ :=
  2 * (insertBaseSteps c_exp n_max U + 3 + C_walk * evictIterSteps c_exp n_max U +
    C_reh * rehashAmortizedSteps c_exp n_max U)

/-- Per-operation amortized instruction charge for `Dictionary.Op U`. -/
def charge (c_exp n_max U C_walk C_reh : ℕ) (_s : Dictionary.State U) : Dictionary.Op U → ℕ
  | .query _ => querySteps c_exp n_max U + 2
  | .insert _ _ => insertCharge c_exp n_max U C_walk C_reh

/-- State-independent expected step bound for a single `opCode` invocation under an arbitrary
input distribution (used in the standalone `Randomized.StateTransitionImpl` certificate, while
`cuckoo_seq_expected_amortized` establishes the tighter `charge` / `expectedOpCharge` bound along
valid trajectories from `initFresh`). -/
def stepWorstCharge (c_exp n_max U : ℕ) (_s : Dictionary.State U) : Dictionary.Op U → ℕ
  | .query _ => querySteps c_exp n_max U + 2
  | .insert _ _ => insertWorstSteps c_exp n_max U + 3

private noncomputable def opSeedSteps (c_exp n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed c_exp n_max U (tableBits n_max)) (s : Dictionary.State U) : Dictionary.Op U → ℝ≥0∞
  | .query _ => (querySteps c_exp n_max U + 2 : ℕ)
  | .insert u _ => insertSeedSteps c_exp n_max U ks θ s u + 3

private theorem opSeedSteps_le_stepWorstCharge (c_exp n_max U : ℕ) (ks : List (Fin U))
    (θ : Seed c_exp n_max U (tableBits n_max)) (s : Dictionary.State U) (o : Dictionary.Op U) :
    opSeedSteps c_exp n_max U ks θ s o ≤ (stepWorstCharge c_exp n_max U s o : ℝ≥0∞) := by
  cases o with
  | query _ => exact le_rfl
  | insert u _ =>
    dsimp only [opSeedSteps, stepWorstCharge]
    push_cast
    exact add_le_add (insertSeedSteps_le_insertWorstSteps c_exp n_max U ks θ s u) le_rfl

open Classical in
private theorem opCode_execCodeDist {w base c_exp n_max U V : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U}
    (o : Dictionary.Op U) {x : Data 19}
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hrep : RepWithKeys w base c_exp n_max U V ks s x)
    (hvalid : (Dictionary.spec U V n_max).valid s o)
    (harg : argMatch o x.regs)
    (hfit_ev : Fits w (maxEvictions n_max))
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_V : Fits w V)
    (hfit_q : Fits w (2 ^ Probability.trinomialDeg U (tableBits n_max))) :
    let θ_mem := extractSeed (hashBase base) c_exp n_max U (tableBits n_max) x.mem
    ∃ (μ_op : PMF (Data 19))
      (hE' : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max)
        (stepKeys ks o)).Nonempty),
      ExecCodeDist w (opCode c_exp n_max) x μ_op (opSeedSteps c_exp n_max U ks θ_mem s o) ∧
      μ_op.map (fun y => extractSeed (hashBase base) c_exp n_max U (tableBits n_max) y.mem) =
        (if θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) then
          PMF.pure θ_mem
         else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE') ∧
      ∀ y ∈ μ_op.support,
        decode (V := V) (n_max := n_max) o y.regs =
          some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
        RepWithKeys w base c_exp n_max U V (stepKeys ks o)
          ((Dictionary.spec U V n_max).stepFn s o).1 y ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint x.mem y.mem := by
  classical
  intro θ_mem
  have hfit_0 : Fits w 0 := hfit_end.of_le (Nat.zero_le _)
  have hs1_rep : RepWithKeys w base c_exp n_max U V ks s (x.set 15 0) :=
    RepWithKeys.supported (x := x) (x' := x.set 15 0) (by simp +decide) (fun _ _ => rfl)
      ((Exec.const (B := .exact) (d := 15) hfit_0).bounded hrep.1) hrep
  cases o with
  | query u =>
    obtain ⟨h2, h3⟩ := harg
    obtain ⟨y, he_g, hy_2, hy_rep, hy_seed, hy_mod⟩ :=
      queryCode_execWithin (u := u) hs1_rep (by wram_simp [h3]) hw hfit_end hfit_V
    have hθ_surv : θ_mem ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks :=
      hrep.extractSeed_mem_survivingSeeds
    refine ⟨PMF.pure y, ⟨θ_mem, hθ_surv⟩, ?_, ?_, ?_⟩
    · dsimp only [opSeedSteps]
      unfold opCode
      wram_rand_exec [h2]
      wram_rand_call he_g
      exact ⟨rfl, by norm_cast; omega⟩
    · simp only [stepKeys, hθ_surv, ↓reduceIte, PMF.map, PMF.pure_bind, Function.comp_apply,
        hy_seed]
      rfl
    · intro z hz
      rw [PMF.mem_support_pure_iff] at hz
      subst hz
      refine ⟨?_, hy_rep, hy_mod⟩
      simp [decode, Dictionary.spec, hy_2, decodeOptionNat_encodeOptionNat]
  | insert u v =>
    obtain ⟨h2, h3, h4⟩ := harg
    obtain ⟨μ_ins, hE', hins_dist, hins_law, hins_supp⟩ :=
      insertCode_execCodeDist hreh hs1_rep (by wram_simp [h3])
        (by wram_simp [h4]) hvalid hfit_ev hw hfit_end hfit_q
    refine ⟨μ_ins, hE', ?_, hins_law, fun y hy => ⟨rfl, (hins_supp y hy).2.1, (hins_supp y hy).2.2⟩⟩
    unfold opCode opSeedSteps
    wram_rand_exec [h2]
    wram_rand_call hins_dist
    refine ⟨rfl, le_of_eq ?_⟩
    dsimp only [θ_mem, Data.set]
    push_cast; ring

private theorem tsum_seedLaw_insertSeedSteps_le {c_exp n_max U V C_walk C_reh v : ℕ}
    {ks : List (Fin U)} {s : Dictionary.State U} {u : Fin U}
    (hfam : IsCuckooHashFamily c_exp U n_max (tableBits n_max) (maxEvictions n_max) C_walk C_reh)
    (hnodup : ks.Nodup)
    (hdom : ∀ x, x ∈ ks ↔ x ∈ Dictionary.dom s)
    (hvalid : (Dictionary.spec U V n_max).valid s (.insert u v)) :
    (∑' θ : Seed c_exp n_max U (tableBits n_max),
      seedLaw c_exp n_max U (tableBits n_max) θ *
        (insertSeedSteps c_exp n_max U ks θ s u + 3)) ≤
      (insertBaseSteps c_exp n_max U + 3 + C_walk * evictIterSteps c_exp n_max U +
        C_reh * rehashAmortizedSteps c_exp n_max U : ℕ) := by
  classical
  set M := tableBits n_max
  set p := seedLaw c_exp n_max U M
  by_cases hu : u ∈ Dictionary.dom s
  · simp_rw [insertSeedSteps, ite_eq_left hu]
    rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
    exact_mod_cast (by omega : insertBaseSteps c_exp n_max U + 3 ≤
      insertBaseSteps c_exp n_max U + 3 + C_walk * evictIterSteps c_exp n_max U +
        C_reh * rehashAmortizedSteps c_exp n_max U)
  · have hu_ks : u ∉ ks := fun h => hu ((hdom u).mp h)
    have hnone_u : s u = none := Dictionary.notMem_dom_iff.mp hu
    have hcard_lt : (Dictionary.dom s).card < n_max := by
      rcases hvalid.1 with hlt | hsome
      · exact hlt
      · rw [hnone_u] at hsome; exact Bool.noConfusion hsome
    have htoFinset : ks.toFinset = Dictionary.dom s := Finset.ext fun x => by simp [hdom x]
    have hlen_lt : ks.length < n_max := by
      rwa [← List.toFinset_card_of_nodup hnodup, htoFinset]
    let F : Set (Seed c_exp n_max U M) :=
      {θ | (pureReplay (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) ks).isSome ∧
        (pureReplay (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) (ks ++ [u])).isNone}
    set R := maxEvictions n_max * evictIterSteps c_exp n_max U + rehashLoopSteps c_exp n_max U + 2
    have hpw : ∀ θ : Seed c_exp n_max U M,
        p θ * (insertSeedSteps c_exp n_max U ks θ s u + 3) ≤
          p θ * (insertBaseSteps c_exp n_max U + 3 : ℝ≥0∞) +
          (p θ * (cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max)
            (Dictionary.dom s) u : ℝ≥0∞)) * (evictIterSteps c_exp n_max U : ℝ≥0∞) +
          F.indicator (fun θ => p θ) θ * (R : ℝ≥0∞) := by
      intro θ
      dsimp only [insertSeedSteps]
      simp only [hu, ↓reduceIte]
      by_cases hcond :
          θ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (ks ++ [u]) ∨
          θ ∉ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks
      · have hnotF : θ ∉ F := by
          rintro ⟨hf1, hf2⟩
          rcases hcond with h1 | h2
          · rw [mem_survivingSeeds, Option.isNone_iff_eq_none.mp hf2] at h1
            cases h1
          · exact h2 (mem_survivingSeeds.mpr hf1)
        simp only [hcond, ↓reduceIte, Set.indicator_of_notMem hnotF, zero_mul, add_zero]
        push_cast
        exact le_of_eq (by ring)
      · have hmemF : θ ∈ F := by
          rw [not_or, Classical.not_not, mem_survivingSeeds, mem_survivingSeeds] at hcond
          exact ⟨hcond.2, Option.isNone_iff_eq_none.mpr
            (Option.not_isSome_iff_eq_none.mp hcond.1)⟩
        simp only [hcond, ↓reduceIte, Set.indicator_of_mem hmemF]
        have hw_eq : (insertWorstSteps c_exp n_max U : ℝ≥0∞) + 3 =
            (insertBaseSteps c_exp n_max U + 3 : ℝ≥0∞) + (R : ℝ≥0∞) := by
          dsimp only [insertWorstSteps, R]; push_cast; ring
        rw [hw_eq, mul_add]
        gcongr
        exact le_self_add
    calc (∑' θ : Seed c_exp n_max U M, p θ * (insertSeedSteps c_exp n_max U ks θ s u + 3))
      _ ≤ ∑' θ : Seed c_exp n_max U M,
            (p θ * (insertBaseSteps c_exp n_max U + 3 : ℝ≥0∞) +
            (p θ * (cuckooWalkRounds (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max)
              (Dictionary.dom s) u : ℝ≥0∞)) * (evictIterSteps c_exp n_max U : ℝ≥0∞) +
            F.indicator (fun θ => p θ) θ * (R : ℝ≥0∞)) :=
          tsum_le_tsum hpw
      _ = (∑' θ : Seed c_exp n_max U M, p θ * (insertBaseSteps c_exp n_max U + 3 : ℝ≥0∞)) +
          (∑' θ : Seed c_exp n_max U M, (p θ * (cuckooWalkRounds (evalHash1 θ) (evalHash2 θ)
            (maxEvictions n_max) (Dictionary.dom s) u : ℝ≥0∞)) *
              (evictIterSteps c_exp n_max U : ℝ≥0∞)) +
          (∑' θ : Seed c_exp n_max U M, F.indicator (fun θ => p θ) θ * (R : ℝ≥0∞)) := by
          rw [Summable.tsum_add CompleteLattice.summable CompleteLattice.summable,
            Summable.tsum_add CompleteLattice.summable CompleteLattice.summable]
      _ ≤ (insertBaseSteps c_exp n_max U + 3 : ℝ≥0∞) +
          (C_walk : ℝ≥0∞) * (evictIterSteps c_exp n_max U : ℝ≥0∞) +
          (C_reh : ℝ≥0∞) * (rehashAmortizedSteps c_exp n_max U : ℝ≥0∞) := by
          refine add_le_add (add_le_add ?_ ?_) ?_
          · rw [ENNReal.tsum_mul_right, p.tsum_coe, one_mul]
          · rw [ENNReal.tsum_mul_right]
            exact mul_le_mul' (hfam.expected_walk_le (Dictionary.dom s) u hcard_lt hu) le_rfl
          · rw [ENNReal.tsum_mul_right, ← PMF.toOuterMeasure_apply]
            set D := max n_max 1 * max (maxEvictions n_max) 1
            have hD_pos : 0 < D :=
              Nat.mul_pos (le_max_right n_max 1) (le_max_right (maxEvictions n_max) 1)
            have hR_le : R ≤ D * rehashAmortizedSteps c_exp n_max U :=
              le_of_lt (Nat.lt_mul_div_succ R hD_pos)
            have hprob' : p.toOuterMeasure F ≤ (C_reh : ℝ≥0∞) / (D : ℝ≥0∞) := by
              simpa only [D, Nat.cast_mul, Nat.mono_cast.map_max, Nat.cast_one] using
                hfam.step_rehash_prob_le ks u hnodup hlen_lt hu_ks
            calc p.toOuterMeasure F * (R : ℝ≥0∞)
              _ ≤ ((C_reh : ℝ≥0∞) / (D : ℝ≥0∞)) *
                    ((D : ℝ≥0∞) * (rehashAmortizedSteps c_exp n_max U : ℝ≥0∞)) :=
                  mul_le_mul' hprob' (by exact_mod_cast hR_le)
              _ = (C_reh : ℝ≥0∞) *
                    (((D : ℝ≥0∞)⁻¹ * (D : ℝ≥0∞)) *
                      (rehashAmortizedSteps c_exp n_max U : ℝ≥0∞)) := by
                  rw [div_eq_mul_inv, mul_assoc, mul_assoc]
              _ = (C_reh : ℝ≥0∞) * (rehashAmortizedSteps c_exp n_max U : ℝ≥0∞) := by
                  rw [ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr hD_pos.ne')
                    (ENNReal.natCast_ne_top D), one_mul]
      _ = (insertBaseSteps c_exp n_max U + 3 + C_walk * evictIterSteps c_exp n_max U +
            C_reh * rehashAmortizedSteps c_exp n_max U : ℕ) := by
          push_cast; ring

/-! ### `cuckooCode`, `impl`, and expected-amortized sequence theorems -/

/-- Relocatable `SubroutineCode` bundle for Pagh–Rodler cuckoo hashing over `Basis.exact`. -/
@[expose]
def cuckooCode (c_exp n_max : ℕ) : SubroutineCode .exact 19 2 where
  allocSpan := allocSpan c_exp n_max
  initSetup := initSetup c_exp n_max
  code := opCode c_exp n_max
  frontierReg := 1
  baseReg := 0
  initParams := ![3, 4]
  curReg := 16
  zeroReg := 17
  oneReg := 18
  incCur := .exactBin .add 16 16 18
  input := fun i => decide (0 < i.val)
  output := 2

private theorem initSetup_coupled_spec {w base c_exp n_max U V : ℕ} {x₁ : Data 19}
    (hx₁ : x₁.Bounded w)
    (hb : x₁.regs 0 = base)
    (hfr : x₁.regs 1 = base + space c_exp n_max)
    (hpar : ∀ j : Fin 2, x₁.regs (![3, 4] j) = ![n_max, U] j)
    (hz : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x₁.mem a = 0)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w) :
    ∃ ν₀ : PMF (Seed c_exp n_max U (tableBits n_max) × Data 19),
      ExecCodeDist w (initSetup c_exp n_max) x₁ (ν₀.map Prod.snd) (setupSteps c_exp n_max U) ∧
      (∀ θ, (ν₀.map Prod.fst) θ ≤ 2 * seedLaw c_exp n_max U (tableBits n_max) θ) ∧
      ∀ p ∈ ν₀.support,
        p.2.regs 1 = base + space c_exp n_max ∧
        Rep w base c_exp n_max U V (Dictionary.empty U) p.2 ∧
        (0 : ℕ) ≤ 0 ∧
        Modifies (Block.mk base (space c_exp n_max)).footprint x₁.mem p.2.mem := by
  have hd_pos : 0 < Probability.trinomialDeg U (tableBits n_max) :=
    lt_of_lt_of_le (tableBits_pos n_max) (Probability.le_trinomialDeg U (tableBits n_max))
  have hfit_q := KWise.fits_two_pow_trinomialDeg hw
  have hfit_ev : Fits w (maxEvictions n_max) :=
    hfit_q.of_le ((maxEvictions_le_tableSize n_max).trans
      (Nat.pow_le_pow_right two_pos (Probability.le_trinomialDeg U (tableBits n_max))))
  have hfit_U : Fits w (max U 2 + 1) := by
    have hU : max U 2 ≤ 2 ^ Probability.trinomialDeg U (tableBits n_max) :=
      (Nat.le_pow_clog one_lt_two _).trans (Nat.pow_le_pow_right two_pos
        ((le_max_left _ _).trans
          (Probability.trinomialTargetBits_le_trinomialDeg U (tableBits n_max))))
    have hpow : 2 ^ Probability.trinomialDeg U (tableBits n_max) * 2 ≤ 2 ^ w := by
      rw [← pow_succ]
      exact Nat.pow_le_pow_right two_pos (by omega)
    rw [fits_iff]
    omega
  obtain ⟨ν₀, hdist, hseed, hsupp⟩ :=
    initSetup_spec (U := U) (V := V) hx₁ hb hfr (hpar 0) (hpar 1) hz hfit_ev hfit_U hfit_q
  refine ⟨ν₀, hdist, fun θ => ?_, fun p hp => ?_⟩
  · rw [hseed, two_mul]
    exact le_self_add
  · obtain ⟨_, hfr', hrep, hmod⟩ := hsupp p hp
    exact ⟨hfr', hrep.toRep, le_rfl, hmod⟩

private theorem opCode_coupled_step_spec {w base c_exp n_max U V : ℕ}
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (ν : PMF (Seed c_exp n_max U (tableBits n_max) × Data 19))
    (hreh : ∀ (S : Finset (Fin U)), S.card ≤ n_max →
      (seedLaw c_exp n_max U (tableBits n_max)).toOuterMeasure
        {θ : Seed c_exp n_max U (tableBits n_max) |
          ¬ GoodForSet (evalHash1 θ) (evalHash2 θ) (maxEvictions n_max) S} ≤ 1 / 2)
    (hv : (Dictionary.spec U V n_max).valid s o)
    (hseed : ∀ θ, (ν.map Prod.fst) θ ≤ 2 * seedLaw c_exp n_max U (tableBits n_max) θ)
    (hsupp : ∀ p ∈ ν.support, Rep w base c_exp n_max U V s p.2 ∧ argMatch o p.2.regs)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_V : Fits w V) :
    ∃ (μ_step : Seed c_exp n_max U (tableBits n_max) × Data 19 →
        PMF (Seed c_exp n_max U (tableBits n_max) × Data 19))
      (T_step : Seed c_exp n_max U (tableBits n_max) × Data 19 → ℝ≥0∞),
      (∀ p ∈ ν.support,
        ExecCodeDist w (cuckooCode c_exp n_max).code p.2 ((μ_step p).map Prod.snd) (T_step p) ∧
        ∀ q ∈ (μ_step p).support,
          decode (V := V) (n_max := n_max) o q.2.regs =
            some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
          Rep w base c_exp n_max U V ((Dictionary.spec U V n_max).stepFn s o).1 q.2 ∧
          Modifies (Block.mk base (space c_exp n_max)).footprint p.2.mem q.2.mem) ∧
      (∀ θ', ((ν.bind μ_step).map Prod.fst) θ' ≤
        2 * seedLaw c_exp n_max U (tableBits n_max) θ') ∧
      (∑' p, ν p * (T_step p + ∑' q, (μ_step p) q * (0 : ℕ))) ≤
        (stepWorstCharge c_exp n_max U s o : ℝ≥0∞) + ∑' p, ν p * (0 : ℕ) := by
  classical
  have hfit_q := KWise.fits_two_pow_trinomialDeg hw
  let μ_raw : Seed c_exp n_max U (tableBits n_max) × Data 19 → PMF (Data 19) := fun p =>
    if hp : Rep w base c_exp n_max U V s p.2 ∧ argMatch o p.2.regs then
      Classical.choose
        (opCode_execCodeDist o hreh (Classical.choose_spec hp.1)
          hv hp.2 hfit_ev hw hfit_end hfit_V hfit_q)
    else PMF.pure p.2
  let μ_step : Seed c_exp n_max U (tableBits n_max) × Data 19 →
      PMF (Seed c_exp n_max U (tableBits n_max) × Data 19) :=
    fun p => (μ_raw p).map fun y => (p.1, y)
  let T_step : Seed c_exp n_max U (tableBits n_max) × Data 19 → ℝ≥0∞ :=
    fun _ => (stepWorstCharge c_exp n_max U s o : ℝ≥0∞)
  refine ⟨μ_step, T_step, ?_, ?_, ?_⟩
  · intro p hp_mem
    have hp := hsupp p hp_mem
    obtain ⟨_, hex, _, hpost⟩ := Classical.choose_spec
      (opCode_execCodeDist o hreh (Classical.choose_spec hp.1)
        hv hp.2 hfit_ev hw hfit_end hfit_V hfit_q)
    have hsnd_eq : (μ_step p).map Prod.snd = μ_raw p :=
      (PMF.map_comp _ _ _).trans (PMF.map_id _)
    refine ⟨?_, ?_⟩
    · dsimp only [cuckooCode, T_step]
      rw [hsnd_eq]
      simpa only [μ_raw, hp, and_self, ↓reduceDIte] using
        hex.mono (opSeedSteps_le_stepWorstCharge _ _ _ _ _ _ _)
    · intro q hq
      rw [PMF.mem_support_map_iff] at hq
      obtain ⟨y, hy, rfl⟩ := hq
      obtain ⟨hdec, hrep', hmod⟩ :=
        hpost y (by simpa only [μ_raw, hp, and_self, ↓reduceDIte] using hy)
      exact ⟨hdec, hrep'.toRep, hmod⟩
  · intro θ'
    have hfst : (ν.bind μ_step).map Prod.fst = ν.map Prod.fst := by
      rw [PMF.map_bind]
      exact congrArg ν.bind (funext fun p => (PMF.map_comp _ _ _).trans (PMF.map_const _ _))
    exact hfst ▸ hseed θ'
  · simp only [T_step, Nat.cast_zero, mul_zero, tsum_zero, add_zero]
    rw [ENNReal.tsum_mul_right, ν.tsum_coe, one_mul]

private theorem cuckoo_arguments_fit {w n_max U V : ℕ}
    (hfit_U : Fits w (max U 2 + 1)) (hfit_V : Fits w V)
    {s : Dictionary.State U} (o : Dictionary.Op U)
    (hv : (Dictionary.spec U V n_max).valid s o) (i : Fin 19) :
    Fits w (encode o i) := by
  cases o with
  | query u =>
    dsimp only [encode]
    split_ifs <;> exact hfit_U.of_le (by have := u.isLt; omega)
  | insert u v =>
    dsimp only [encode]
    split_ifs
    · exact hfit_U.of_le (by omega)
    · exact hfit_U.of_le (by have := u.isLt; omega)
    · exact hfit_V.of_le hv.2.le
    · exact hfit_U.of_le (Nat.zero_le _)

private theorem cuckoo_span_exec {w base c_exp n_max U : ℕ}
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    {x : Data 19} (_hx : x.Bounded w) (hfr : x.regs 1 = base)
    (hpar : ∀ j : Fin 2, x.regs (![3, 4] j) = ![n_max, U] j) :
    ∃ x₁ : Data 19,
      ExecWithin w (allocSpan c_exp n_max) x x₁ spanSteps ∧
      x₁.mem = x.mem ∧
      x₁.regs 0 = base ∧
      x₁.regs 1 = base + space c_exp n_max ∧
      ∀ j : Fin 2, x₁.regs (![3, 4] j) = ![n_max, U] j := by
  obtain ⟨x₁, he, hm, h0, h1, h3, h4⟩ :=
    allocSpan_execWithin hfr (hpar 0) (hpar 1) hfit_end hfit_ev
  exact ⟨x₁, he, hm, h0, h1, fun j => by fin_cases j <;> assumption⟩

/-- **Unconditional Pagh–Rodler cuckoo hash family certificate at `tableBits n_max` (`C_walk = 3`,
`C_reh = 4`):**
whenever `U ≤ max n_max 4 ^ c_exp`, the regime-switched Word-RAM cuckoo hash pair (`KWise`
below `doubleTabThreshold c_exp`, `DoubleTabulation` at or above `doubleTabThreshold c_exp`)
satisfies `IsCuckooHashFamily c_exp U n_max (tableBits n_max) (maxEvictions n_max) 3 4` for
**every** capacity `n_max : ℕ` (`[PaghRodler2004]`, `[Thorup2013]`). -/
theorem isCuckooHashFamily_tableBits {c_exp U n_max : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) :
    IsCuckooHashFamily c_exp U n_max (tableBits n_max) (maxEvictions n_max) 3 4 :=
  isCuckooHashPair_provableFamily hU (thirtyTwo_mul_max_le_tableSize n_max)

/-- `O(c_exp⁴) = O_{c_exp}(1)` worst-case instruction bound for `query` via `opCode c_exp n_max`. -/
@[expose]
def queryChargeBound (c_exp : ℕ) : ℕ :=
  queryStepsBound c_exp + 2

/-- `O(c_exp⁴) = O_{c_exp}(1)` expected amortized instruction bound for `insert` (`C_walk = 3`,
`C_reh = 4`), independent of `n_max` and `U` whenever `U ≤ max n_max 4 ^ c_exp`. -/
@[expose]
def insertChargeBound (c_exp : ℕ) : ℕ :=
  let evictIterBound := 2 * (evalHashBound c_exp + 54) + 59
  let insertBaseBound := 2 * (evalHashBound c_exp + 35) + 78
  let resampleAtBaseFactor :=
    max (10 * cuckooKBound c_exp + 35)
      (80 * ((DoubleTabulation.provableC c_exp + 1) *
        DoubleTabulation.provableD c_exp) + 63)
  let rehashAmortizedBound := 3 * evictIterBound + 2 * resampleAtBaseFactor + 4290 + 1
  2 * (insertBaseBound + 3 + 3 * evictIterBound + 4 * rehashAmortizedBound)

/-- `O(c_exp⁴) = O_{c_exp}(1)` expected amortized per-operation instruction charge for Pagh–Rodler
cuckoo hashing, completely independent of `n_max` and `U` whenever `U ≤ max n_max 4 ^ c_exp`. -/
@[expose]
def expectedOpCharge (c_exp : ℕ) {U : ℕ} (_s : Dictionary.State U) : Dictionary.Op U → ℕ
  | .query _ => queryChargeBound c_exp
  | .insert _ _ => insertChargeBound c_exp

private theorem le_rehashScale (n_max : ℕ) :
    1 ≤ max n_max 1 * max (maxEvictions n_max) 1 ∧
      n_max ≤ max n_max 1 * max (maxEvictions n_max) 1 ∧
      maxEvictions n_max ≤ max n_max 1 * max (maxEvictions n_max) 1 :=
  ⟨Nat.mul_pos (le_max_right n_max 1) (le_max_right (maxEvictions n_max) 1),
    (le_max_left n_max 1).trans
      (Nat.le_mul_of_pos_right _ (le_max_right (maxEvictions n_max) 1)),
    (le_max_left (maxEvictions n_max) 1).trans
      (Nat.le_mul_of_pos_left _ (le_max_right n_max 1))⟩

private theorem resampleAtBaseSteps_le_mul (c_exp n_max : ℕ) :
    resampleAtBaseSteps c_exp n_max ≤
      max (10 * cuckooKBound c_exp + 35)
        (80 * ((DoubleTabulation.provableC c_exp + 1) *
          DoubleTabulation.provableD c_exp) + 63) *
        (max n_max 1 * max (maxEvictions n_max) 1) := by
  obtain ⟨h1_D, hn_D, hev_D⟩ := le_rehashScale n_max
  set D := max n_max 1 * max (maxEvictions n_max) 1
  set rf := max (10 * cuckooKBound c_exp + 35)
    (80 * ((DoubleTabulation.provableC c_exp + 1) * DoubleTabulation.provableD c_exp) + 63)
  have hev18 := eighteen_le_maxEvictions n_max
  have hmax4_D : max n_max 4 ≤ D := by omega
  dsimp only [resampleAtBaseSteps, resampleHashPairSteps, resampleSingleSteps]
  split_ifs with hlt
  · have hk := cuckooK_le_cuckooKBound_of_lt hlt
    have hfac : 10 * cuckooKBound c_exp + 35 ≤ rf := le_max_left _ _
    calc 2 * (5 * cuckooK n_max + 10) + 4 + 4
      _ ≤ 10 * cuckooKBound c_exp + 35 := by omega
      _ ≤ rf * 1 := by omega
      _ ≤ rf * D := Nat.mul_le_mul_left _ h1_D
  · have hb : 2 ^ DoubleTabulation.provableB n_max ≤ 8 * D := by
      have h2b := DoubleTabulation.two_pow_provableB_le n_max
      omega
    set S := (DoubleTabulation.provableC c_exp + 1) * DoubleTabulation.provableD c_exp
    have hfac : 80 * S + 63 ≤ rf := le_max_right _ _
    have hmul : S * 2 ^ DoubleTabulation.provableB n_max ≤ S * (8 * D) :=
      Nat.mul_le_mul_left S hb
    calc 2 * DoubleTabulation.resampleSteps
            (DoubleTabulation.provableC c_exp)
            (DoubleTabulation.provableD c_exp)
            (DoubleTabulation.provableB n_max) + 4 + 4
      _ ≤ 10 * (S * 2 ^ DoubleTabulation.provableB n_max) + 63 := by
          dsimp only [DoubleTabulation.resampleSteps, DoubleTabulation.space, S]
          omega
      _ ≤ 10 * (S * (8 * D)) + 63 * D := by omega
      _ = (80 * S + 63) * D := by ring
      _ ≤ rf * D := Nat.mul_le_mul_right D hfac

private theorem rehashAmortizedSteps_le {c_exp n_max U : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) :
    rehashAmortizedSteps c_exp n_max U ≤
      3 * (2 * (evalHashBound c_exp + 54) + 59) +
        2 * max (10 * cuckooKBound c_exp + 35)
          (80 * ((DoubleTabulation.provableC c_exp + 1) *
            DoubleTabulation.provableD c_exp) + 63) + 4290 + 1 := by
  obtain ⟨h1_D, hn_D, hev_D⟩ := le_rehashScale n_max
  set D := max n_max 1 * max (maxEvictions n_max) 1
  set evB := 2 * (evalHashBound c_exp + 54) + 59
  set rf := max (10 * cuckooKBound c_exp + 35)
    (80 * ((DoubleTabulation.provableC c_exp + 1) * DoubleTabulation.provableD c_exp) + 63)
  have hnev_D : n_max * maxEvictions n_max ≤ D :=
    Nat.mul_le_mul (le_max_left n_max 1) (le_max_left (maxEvictions n_max) 1)
  have hmax4_D : max n_max 4 ≤ 4 * D := by omega
  have hiter : evictIterSteps c_exp n_max U ≤ evB := evictIterSteps_le_add hU
  have hres : resampleAtBaseSteps c_exp n_max ≤ rf * D :=
    resampleAtBaseSteps_le_mul c_exp n_max
  have hts := tableSize_le_sixtyFour_mul_max n_max
  have hclear : 8 * tableSize n_max + 10 ≤ 2058 * D := by omega
  have h_ev_mul : maxEvictions n_max * evictIterSteps c_exp n_max U ≤ D * evB :=
    Nat.mul_le_mul hev_D hiter
  have h_nev_mul : (n_max * maxEvictions n_max) * evictIterSteps c_exp n_max U ≤ D * evB :=
    Nat.mul_le_mul hnev_D hiter
  have hreplay :
      n_max * (maxEvictions n_max * evictIterSteps c_exp n_max U + 54) + 23 ≤
        (evB + 77) * D := by
    calc n_max * (maxEvictions n_max * evictIterSteps c_exp n_max U + 54) + 23
      _ = (n_max * maxEvictions n_max) * evictIterSteps c_exp n_max U + 54 * n_max + 23 := by ring
      _ ≤ D * evB + 54 * D + 23 * D := by omega
      _ = (evB + 77) * D := by ring
  have hnum : maxEvictions n_max * evictIterSteps c_exp n_max U +
        rehashLoopSteps c_exp n_max U + 2 ≤
      D * (3 * evB + 2 * rf + 4290) := by
    rw [rehashLoopSteps_eq]
    calc maxEvictions n_max * evictIterSteps c_exp n_max U +
          (2 * (resampleAtBaseSteps c_exp n_max + (8 * tableSize n_max + 10) +
            (n_max * (maxEvictions n_max * evictIterSteps c_exp n_max U + 54) + 23) + 4) + 10) + 2
      _ ≤ D * evB +
          (2 * (rf * D + 2058 * D + (evB + 77) * D + 4 * D) + 10 * D) + 2 * D := by omega
      _ = D * (3 * evB + 2 * rf + 4290) := by ring
  dsimp only [rehashAmortizedSteps]
  exact Nat.add_le_add_right (Nat.div_le_of_le_mul hnum) 1

theorem charge_le_expectedOpCharge {c_exp n_max U : ℕ}
    (hU : U ≤ max n_max 4 ^ c_exp) (s : Dictionary.State U) (o : Dictionary.Op U) :
    charge c_exp n_max U 3 4 s o ≤ expectedOpCharge c_exp s o := by
  cases o with
  | query _ =>
    dsimp only [charge, expectedOpCharge, queryChargeBound]
    have hg := querySteps_le hU
    omega
  | insert _ _ =>
    dsimp only [charge, expectedOpCharge, insertCharge, insertChargeBound, insertBaseSteps]
    have hp := probeKeySteps_le hU
    have he := evictIterSteps_le_add hU
    have hr := rehashAmortizedSteps_le hU
    omega

/-- Composable randomized Word-RAM `StateTransitionImpl` certificate for Pagh–Rodler cuckoo hashing
over `Basis.exact`, unconditional whenever `U ≤ max n_max 4 ^ c_exp`. -/
@[expose]
noncomputable def impl (w base c_exp n_max U V : ℕ)
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V) :
    Randomized.StateTransitionImpl (cuckooCode c_exp n_max) (Dictionary.spec U V n_max)
      w base ![n_max, U] (Dictionary.empty U) :=
  Randomized.StateTransitionImpl.ofFn
    (Seed := Seed c_exp n_max U (tableBits n_max))
    (seedLaw := seedLaw c_exp n_max U (tableBits n_max))
    (seedSlack := 2)
    (space := space c_exp n_max)
    (spanTime := spanSteps)
    (setupTime := setupSteps c_exp n_max U)
    (initPotential := 0)
    (charge := stepWorstCharge c_exp n_max U)
    (rep := fun _ => Rep w base c_exp n_max U V)
    (potential := fun _ _ => 0)
    (encode := encode)
    (argMatch := argMatch)
    (decode := decode (V := V) (n_max := n_max))
    (bounded := by exact fun h => h.bounded)
    (arguments_fit := by exact fun {_s} o hv i _ => cuckoo_arguments_fit hfit_U hfit_V o hv i)
    (encode_matches := by intro o _regs; cases o <;> simp +decide [cuckooCode, argMatch, encode])
    (rep_supported := by exact fun hreg hmem hbdd hrep => Rep.supported (hreg 0 rfl) hmem hbdd hrep)
    (potential_supported := by exact fun _ _ _ => rfl)
    (clear_nodup := by dsimp only [cuckooCode]; decide)
    (params_not_clear := by dsimp only [cuckooCode]; decide)
    (incCur_eval := by
      intro x h1 hfit
      change Data.put w x 16 (x.regs 16 + x.regs 18) =
        some (x.set (cuckooCode c_exp n_max).curReg (x.regs (cuckooCode c_exp n_max).curReg + 1))
      change x.regs 18 = 1 at h1
      rw [h1]
      exact Data.put_of_fits hfit)
    (span_exec := by exact fun hx hfr hpar => cuckoo_span_exec hfit_end hfit_ev hx hfr hpar)
    (setup_exec := by exact fun hx₁ hb hfr hpar hz => initSetup_coupled_spec hx₁ hb hfr hpar hz hw)
    (step_exec := by
      exact fun {_s} o ν hv hseed hsupp =>
        opCode_coupled_step_spec o ν (isCuckooHashFamily_tableBits hU).rehash_prob_le_half
          hv hseed hsupp hw hfit_end hfit_ev hfit_V)

/-- Standard-basis (`Basis.standard`) randomized `StateTransitionImpl` certificate for Pagh–Rodler
cuckoo hashing, unconditional whenever `U ≤ max n_max 4 ^ c_exp`. -/
noncomputable abbrev implStandard (w base c_exp n_max U V : ℕ)
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V) :
    Randomized.StateTransitionImpl (cuckooCode c_exp n_max).toStandard (Dictionary.spec U V n_max)
      w base ![n_max, U] (Dictionary.empty U) :=
  (impl w base c_exp n_max U V hU hw hfit_end hfit_ev hfit_U hfit_V).toStandard

/-- Coupled multi-step execution telescope for Pagh–Rodler cuckoo hashing maintaining the exact
conditional-uniform in-memory seed marginal
`PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE` across an
operation sequence `ops`. -/
theorem cuckoo_steps_expected_amortized (w base c_exp n_max U V : ℕ)
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V)
    (ops : List (Dictionary.Op U))
    {ks : List (Fin U)} {s : Dictionary.State U}
    (ν : PMF (Seed c_exp n_max U (tableBits n_max) × Data 19))
    (hv : (Dictionary.spec U V n_max).ValidHistory s ops)
    (hE : (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).Nonempty)
    (hseed : ν.map Prod.fst =
      PMF.uniformOfFinset (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks) hE)
    (hsupp : ∀ p ∈ ν.support,
      p.1 = extractSeed (hashBase base) c_exp n_max U (tableBits n_max) p.2.mem ∧
      RepWithKeys w base c_exp n_max U V ks s p.2) :
    let C := impl w base c_exp n_max U V hU hw hfit_end hfit_ev hfit_U hfit_V
    ∃ (ν_final : PMF (Seed c_exp n_max U (tableBits n_max) × Data 19)) (T_ops : ℝ≥0∞),
      C.ExecStepsOfFn s ops ν ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 2 * seedLaw c_exp n_max U (tableBits n_max) θ) ∧
      (∀ p ∈ ν_final.support,
        Rep w base c_exp n_max U V ((Dictionary.spec U V n_max).run s ops).1 p.2) ∧
      T_ops ≤
        ((Dictionary.spec U V n_max).totalCost (expectedOpCharge c_exp) s ops : ℝ≥0∞) := by
  classical
  intro C
  have hfam := isCuckooHashFamily_tableBits hU
  have hfit_q := KWise.fits_two_pow_trinomialDeg hw
  induction ops generalizing ks s ν with
  | nil =>
    obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
    have hrep₀ := (hsupp p₀ hp₀).2
    have hcard := (survivingSeeds_card_and_nonempty (c_exp := c_exp) (U := U) (n_max := n_max)
      hfam.rehash_prob_le_half hrep₀.2.2.2.2.1.1 hrep₀.2.2.2.2.1.2.1).1
    exact ⟨ν, 0, Randomized.StateTransitionImpl.ExecStepsOfFn.nil (C := C) s ν,
      fun θ => hseed ▸ uniformOfFinset_le_two_mul_uniformOfFintype hE hcard θ,
      fun p hp => (hsupp p hp).2.toRep, by simp⟩
  | cons o os ih =>
    obtain ⟨hvo, hvos⟩ := hv
    obtain ⟨p₀, hp₀⟩ := ν.support_nonempty
    have hrep₀ := (hsupp p₀ hp₀).2
    have hnodup : ks.Nodup := hrep₀.2.2.2.2.1.1
    have hlen_le : ks.length ≤ n_max := hrep₀.2.2.2.2.1.2.1
    have hdom : ∀ x, x ∈ ks ↔ x ∈ Dictionary.dom s := hrep₀.2.2.2.2.1.2.2.2.1
    have hcard : Fintype.card (Seed c_exp n_max U (tableBits n_max)) ≤
        2 * (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ks).card :=
      (survivingSeeds_card_and_nonempty (c_exp := c_exp) (U := U) (n_max := n_max)
        hfam.rehash_prob_le_half hnodup hlen_le).1
    have hseed_le : ∀ θ, (ν.map Prod.fst) θ ≤ 2 * seedLaw c_exp n_max U (tableBits n_max) θ :=
      fun θ => hseed ▸ uniformOfFinset_le_two_mul_uniformOfFintype hE hcard θ
    have hprep_ok : ∀ p ∈ ν.support,
        p.1 = extractSeed (hashBase base) c_exp n_max U (tableBits n_max)
          (C.prepare o p.2).mem ∧
        RepWithKeys w base c_exp n_max U V ks s (C.prepare o p.2) ∧
        argMatch o (C.prepare o p.2).regs := by
      intro p hp
      obtain ⟨hp1, hrep_p⟩ := hsupp p hp
      refine ⟨hp1, ?_, C.prepare_argMatch o p.2⟩
      exact RepWithKeys.supported
        (C.prepare_regs_of_not_input (i := 0) rfl o p.2)
        (fun _ _ => rfl)
        (C.prepare_bounded hrep_p.1 (C.arguments_fit o hvo))
        hrep_p
    obtain ⟨_, hrep_p₀, harg_p₀⟩ := hprep_ok p₀ hp₀
    obtain ⟨_, hE', _⟩ := opCode_execCodeDist o hfam.rehash_prob_le_half hrep_p₀ hvo harg_p₀
      hfit_ev hw hfit_end hfit_V hfit_q
    let μ_raw : Seed c_exp n_max U (tableBits n_max) × Data 19 → PMF (Data 19) := fun p =>
      if hp : RepWithKeys w base c_exp n_max U V ks s (C.prepare o p.2) ∧
          argMatch o (C.prepare o p.2).regs then
        Classical.choose
          (opCode_execCodeDist o hfam.rehash_prob_le_half hp.1 hvo hp.2
            hfit_ev hw hfit_end hfit_V hfit_q)
      else PMF.pure (C.prepare o p.2)
    let μ_step : Seed c_exp n_max U (tableBits n_max) × Data 19 →
        PMF (Seed c_exp n_max U (tableBits n_max) × Data 19) :=
      fun p => coupleExtractedSeed base c_exp n_max U (μ_raw p)
    let T_step : Seed c_exp n_max U (tableBits n_max) × Data 19 → ℝ≥0∞ :=
      fun p => opSeedSteps c_exp n_max U ks p.1 s o
    have hstep_spec : ∀ p ∈ ν.support,
        ExecCodeDist w (cuckooCode c_exp n_max).code (C.prepare o p.2)
          ((μ_step p).map Prod.snd) (T_step p) ∧
        (μ_step p).map Prod.fst =
          (if p.1 ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) then
            PMF.pure p.1
           else
            PMF.uniformOfFinset
              (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE') ∧
        ∀ q ∈ (μ_step p).support,
          C.decode o q.2.regs = some ((Dictionary.spec U V n_max).stepFn s o).2 ∧
          q.1 = extractSeed (hashBase base) c_exp n_max U (tableBits n_max) q.2.mem ∧
          RepWithKeys w base c_exp n_max U V (stepKeys ks o)
            ((Dictionary.spec U V n_max).stepFn s o).1 q.2 ∧
          Modifies (Block.mk base C.space).footprint p.2.mem q.2.mem := by
      intro p hp_mem
      obtain ⟨hp1, hrep_prep, harg_prep⟩ := hprep_ok p hp_mem
      have hp : RepWithKeys w base c_exp n_max U V ks s (C.prepare o p.2) ∧
          argMatch o (C.prepare o p.2).regs := ⟨hrep_prep, harg_prep⟩
      obtain ⟨_, hex, hlaw, hpost⟩ := Classical.choose_spec
        (opCode_execCodeDist o hfam.rehash_prob_le_half hp.1 hvo hp.2
          hfit_ev hw hfit_end hfit_V hfit_q)
      refine ⟨?_, ?_, ?_⟩
      · change ExecCodeDist w (opCode c_exp n_max) _ _ _
        simpa only [μ_step, T_step, map_snd_coupleExtractedSeed, μ_raw, hp, and_self,
          ↓reduceDIte, hp1] using hex
      · simp only [μ_step, map_fst_coupleExtractedSeed, μ_raw, hp, and_self, ↓reduceDIte, hp1, hlaw]
      · intro q hq
        obtain ⟨hq1, hy⟩ := mem_support_coupleExtractedSeed hq
        simp only [μ_raw, hp, and_self, ↓reduceDIte] at hy
        obtain ⟨hdec, hrep', hmod⟩ := hpost q.2 hy
        exact ⟨hdec, hq1, hrep', hmod⟩
    let ν₁ := ν.bind μ_step
    have hseed₁ : ν₁.map Prod.fst =
        PMF.uniformOfFinset
          (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE' := by
      let f : Seed c_exp n_max U (tableBits n_max) →
          PMF (Seed c_exp n_max U (tableBits n_max)) := fun θ =>
        if θ ∈ survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o) then
          PMF.pure θ
        else
          PMF.uniformOfFinset
            (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) (stepKeys ks o)) hE'
      have hmap_bind : ν₁.map Prod.fst = (ν.map Prod.fst).bind f := by
        ext θ'
        rw [PMF.map_bind, PMF.bind_apply, PMF.bind_apply,
          Cslib.Probability.PMF.tsum_map_mul ν Prod.fst (fun θ => f θ θ')]
        refine tsum_congr fun p => ?_
        by_cases hp : p ∈ ν.support
        · rw [(hstep_spec p hp).2.1]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hp]
      rw [hmap_bind, hseed]
      exact unifOn_rehash_eq (survivingSeeds_stepKeys_subset c_exp n_max ks o) hE hE'
    have hsupp₁ : ∀ q ∈ ν₁.support,
        q.1 = extractSeed (hashBase base) c_exp n_max U (tableBits n_max) q.2.mem ∧
        RepWithKeys w base c_exp n_max U V (stepKeys ks o)
          ((Dictionary.spec U V n_max).stepFn s o).1 q.2 := fun q hq => by
      rw [PMF.mem_support_bind_iff] at hq
      obtain ⟨p, hp, hq_step⟩ := hq
      exact ⟨((hstep_spec p hp).2.2 q hq_step).2.1, ((hstep_spec p hp).2.2 q hq_step).2.2.1⟩
    obtain ⟨ν_final, T_rest, hex_rest, hseed_final, hrep_final, hamort_rest⟩ :=
      ih ν₁ hvos hE' hseed₁ hsupp₁
    have hex_cons : C.ExecStepsOfFn s (o :: os) ν ν_final ((∑' p, ν p * T_step p) + T_rest) := by
      refine Randomized.StateTransitionImpl.ExecStepsOfFn.cons (C := C) (μ_step := μ_step)
        (T_step := T_step) (fun p hp => ?_) hex_rest
      obtain ⟨hex, _, hpost⟩ := hstep_spec p hp
      refine ⟨hex, fun q hq => ?_⟩
      obtain ⟨hdec, _, hrep', hmod⟩ := hpost q hq
      exact ⟨hdec, hrep'.toRep, hmod⟩
    have hstep_cost :
        (∑' p, ν p * T_step p) ≤ (expectedOpCharge c_exp s o : ℝ≥0∞) := by
      have hstep_ch :
          (∑' p, ν p * T_step p) ≤ (charge c_exp n_max U 3 4 s o : ℝ≥0∞) := by
        have hmap_lhs :
            (∑' p : Seed c_exp n_max U (tableBits n_max) × Data 19, ν p * T_step p) =
              ∑' θ : Seed c_exp n_max U (tableBits n_max),
                (ν.map Prod.fst) θ * opSeedSteps c_exp n_max U ks θ s o :=
          (Cslib.Probability.PMF.tsum_map_mul ν Prod.fst
            (fun θ => opSeedSteps c_exp n_max U ks θ s o)).symm
        rw [hmap_lhs]
        cases o with
        | query u =>
          dsimp only [opSeedSteps, charge]
          rw [ENNReal.tsum_mul_right, (ν.map Prod.fst).tsum_coe, one_mul]
        | insert u v =>
          dsimp only [opSeedSteps, charge, insertCharge]
          calc (∑' θ : Seed c_exp n_max U (tableBits n_max),
                (ν.map Prod.fst) θ * (insertSeedSteps c_exp n_max U ks θ s u + 3))
            _ ≤ ∑' θ : Seed c_exp n_max U (tableBits n_max),
                  (2 * seedLaw c_exp n_max U (tableBits n_max) θ) *
                    (insertSeedSteps c_exp n_max U ks θ s u + 3) :=
                tsum_le_tsum fun θ => mul_le_mul' (hseed_le θ) le_rfl
            _ = 2 * ∑' θ : Seed c_exp n_max U (tableBits n_max),
                  seedLaw c_exp n_max U (tableBits n_max) θ *
                    (insertSeedSteps c_exp n_max U ks θ s u + 3) := by
                simp_rw [mul_assoc]
                rw [ENNReal.tsum_mul_left]
            _ ≤ 2 * (insertBaseSteps c_exp n_max U + 3 + 3 * evictIterSteps c_exp n_max U +
                  4 * rehashAmortizedSteps c_exp n_max U : ℕ) :=
                mul_le_mul' le_rfl (tsum_seedLaw_insertSeedSteps_le hfam hnodup hdom hvo)
            _ = (2 * (insertBaseSteps c_exp n_max U + 3 + 3 * evictIterSteps c_exp n_max U +
                  4 * rehashAmortizedSteps c_exp n_max U) : ℕ) := by
                push_cast; ring
      exact hstep_ch.trans (Nat.cast_le.mpr (charge_le_expectedOpCharge hU s o))
    exact ⟨ν_final, (∑' p, ν p * T_step p) + T_rest, hex_cons, hseed_final, hrep_final,
      (add_le_add hstep_cost hamort_rest).trans_eq (Nat.cast_add _ _).symm⟩

/-- **Unconditional end-to-end expected-amortized theorem for Pagh–Rodler cuckoo hashing.**
Whenever `U ≤ max n_max 4 ^ c_exp`, starting from zeroed memory in
`[base, base + space c_exp n_max)`, initializing `cuckooCode c_exp n_max` and executing any valid
sequence `ops : List (Dictionary.Op U)` of `query` and `insert` operations takes expected
instruction cost at most `spanSteps + setupSteps c_exp n_max U +
  (Dictionary.spec U V n_max).totalCost (expectedOpCharge c_exp) (Dictionary.empty U) ops`,
where `expectedOpCharge c_exp` charges `O(c_exp⁴) = O_{c_exp}(1)` instructions per `query` and
`insert` operation (completely independent of `n_max` and `U`!) and `space c_exp n_max ≤
spaceFactor c_exp * (n_max + 1)` uses `O_{c_exp}(n_max + 1)` words of memory across every
capacity `n_max : ℕ` (`[PaghRodler2004]`, `[Thorup2013]`). -/
theorem cuckoo_seq_expected_amortized (w base c_exp n_max U V : ℕ)
    (hU : U ≤ max n_max 4 ^ c_exp)
    (hw : 2 * Probability.trinomialDeg U (tableBits n_max) ≤ w)
    (hfit_end : Fits w (base + space c_exp n_max))
    (hfit_ev : Fits w (maxEvictions n_max))
    (hfit_U : Fits w (max U 2 + 1))
    (hfit_V : Fits w V)
    {x : Data 19} (ops : List (Dictionary.Op U))
    (hx : x.Bounded w) (hfr : x.regs 1 = base)
    (h3 : x.regs 3 = n_max) (h4 : x.regs 4 = U)
    (hz : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x.mem a = 0)
    (hv : (Dictionary.spec U V n_max).ValidHistory (Dictionary.empty U) ops) :
    let C := impl w base c_exp n_max U V hU hw hfit_end hfit_ev hfit_U hfit_V
    ∃ (ν₀ ν_final : PMF (Seed c_exp n_max U (tableBits n_max) × Data 19)) (T_ops : ℝ≥0∞),
      ExecCodeDist w (cuckooCode c_exp n_max).initFresh x (ν₀.map Prod.snd) C.initTime ∧
      C.ExecStepsOfFn (Dictionary.empty U) ops ν₀ ν_final T_ops ∧
      (∀ θ, (ν_final.map Prod.fst) θ ≤ 2 * seedLaw c_exp n_max U (tableBits n_max) θ) ∧
      (∀ p ∈ ν_final.support,
        Rep w base c_exp n_max U V
          ((Dictionary.spec U V n_max).run (Dictionary.empty U) ops).1 p.2) ∧
      C.initTime + T_ops ≤
        C.initTime +
          ((Dictionary.spec U V n_max).totalCost (expectedOpCharge c_exp)
            (Dictionary.empty U) ops : ℝ≥0∞) := by
  classical
  intro C
  have hfit_q := KWise.fits_two_pow_trinomialDeg hw
  obtain ⟨x₁, ⟨t_span, ht_span, he_span⟩, hm₁, hb₁, hfr₁, h3₁, h4₁⟩ :=
    allocSpan_execWithin hfr h3 h4 hfit_end hfit_ev
  have hx₁_bdd : x₁.Bounded w := he_span.bounded hx
  have hz₁ : ∀ a ∈ (Block.mk base (space c_exp n_max)).footprint, x₁.mem a = 0 := by
    intro a ha; rw [hm₁]; exact hz a ha
  obtain ⟨ν₀, hdist_setup, hseed_setup, hsupp_setup⟩ :=
    initSetup_spec (V := V) hx₁_bdd hb₁ hfr₁ h3₁ h4₁ hz₁ hfit_ev hfit_U hfit_q
  have he_init :
      ExecCodeDist w (cuckooCode c_exp n_max).initFresh x (ν₀.map Prod.snd) C.initTime :=
    ((ExecCodeDist.of_exec he_span).seq_pure hdist_setup).mono
      (add_le_add (by exact_mod_cast ht_span) le_rfl)
  have hE₀ :
      (survivingSeeds (Θ := Seed c_exp n_max U (tableBits n_max)) evalHash1 evalHash2
        (maxEvictions n_max) ([] : List (Fin U))).Nonempty := by simp [survivingSeeds_nil]
  have hseed₀ : ν₀.map Prod.fst =
      PMF.uniformOfFinset
        (survivingSeeds evalHash1 evalHash2 (maxEvictions n_max) ([] : List (Fin U))) hE₀ := by
    rw [hseed_setup]
    ext θ
    rw [seedLaw, PMF.uniformOfFintype_apply, PMF.uniformOfFinset_apply]
    simp [survivingSeeds_nil]
  have hsupp₀ : ∀ p ∈ ν₀.support,
      p.1 = extractSeed (hashBase base) c_exp n_max U (tableBits n_max) p.2.mem ∧
      RepWithKeys w base c_exp n_max U V [] (Dictionary.empty U) p.2 :=
    fun p hp => ⟨(hsupp_setup p hp).1, (hsupp_setup p hp).2.2.1⟩
  obtain ⟨ν_final, T_ops, hex_steps, hseed_final, hrep_final, hamort⟩ :=
    cuckoo_steps_expected_amortized w base c_exp n_max U V hU hw hfit_end hfit_ev hfit_U
      hfit_V ops ν₀ hv hE₀ hseed₀ hsupp₀
  exact ⟨ν₀, ν_final, T_ops, he_init, hex_steps, hseed_final, hrep_final,
    add_le_add le_rfl hamort⟩

end Cslib.DataStructure.Dictionary.WordRAM.CuckooHashing
