/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Pre
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.Helpers
import CslibFrontier.DataStructure.Dictionary.WordRAM.SuccinctWhpBTreeProg.LocateHit
import CslibFrontier.Tactic.Realize

/-!
# Certified SWAR B+-Tree Lookup (`btreeLookupGenProg`)

Parameter-free `Memory.Prog` implementation, `O(1)` specification, and `Realizes .exact`
certificate for `btreeLookup`.

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeLookupGenProg`: parameter-free
  `Memory.Prog` implementation of `btreeLookup`.

## Main results

* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.btreeLookupGenProg_spec`: exact refinement,
  `memoryCost ≤ 262`, and `ValidProg`.
* `Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp.realizes_btreeLookupGen`: `Realizes .exact`
  certificate with zero local work.
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

open Finset
open scoped BigOperators
open Cslib.WordRAM Cslib.WordRAM.Realization
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.StateTransitionSpec (clientState_bind clientResult_bind)
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.SuccinctWhp
open Cslib.DataStructure.Dictionary.Dynamic (logLogFactor one_le_logLogFactor)
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct

/-- Parameter-free `btreeLookup` (`d = (((cp, base), sIdx), q)`), returning `(1, val)` on hit or
`(0, 0)` on miss. -/
@[irreducible] def btreeLookupGenProg :
    ((WhpCoreParams × ℕ) × ℕ) × ℕ → Memory.Prog (ℕ × ℕ)
  | (((cp, base), sIdx), q) => do
    let loc ← btreeLocateHitGenProg (((cp, base), sIdx), q)
    let (hitFlag, rest) := loc
    let (lr, nd) := rest
    let (_, r) := lr
    let (_, kv) := nd
    let (_, vW) := kv
    let z0 ← pure 0
    if hitFlag = z0 then
      pure (z0, z0)
    else do
      let v_r ← laneGetGenProg ((wpWVal cp, vW), r)
      let z1 ← pure 1
      pure (z1, v_r)

theorem btreeLookupGenProg_spec {c U V w n_max base sIdx insCount q : ℕ}
    {sl : BTreeSlice} {mapFn : ℕ → Option ℕ} {s : Memory.State}
    (henv : WhpLargeEnv c U V w n_max w base)
    (hsIdx : sIdx < 3 * numBucketsWhp n_max)
    (hins : insCount ≤ 8 * (slabScale n_max) ^ 12)
    (hrep : BTreeSliceMemRep base c U V w n_max sIdx sl s.mem)
    (hv : ValidWhpSlice n_max insCount sl mapFn)
    (hq : q < 2 ^ fpBitsWhp n_max) :
    let prog := btreeLookupGenProg (((mkWhpCoreParams c U V w n_max, base), sIdx), q)
    (Memory.spec 0).clientState s prog = s ∧
    (Memory.spec 0).clientResult s prog =
      (match mapFn q with | some v => (1, v) | none => (0, 0)) ∧
    memoryCost prog s ≤ 262 ∧
    ValidProg w (base + largeSpaceWhp c U V w n_max) s prog := by
  obtain ⟨hst, hmc, hvp, hres⟩ :=
    btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
  dsimp only at hst hmc hvp hres ⊢
  unfold btreeLookupGenProg
  simp only [wp_large_wVal henv.2.2.2.1, pure_bind]
  rcases hres with ⟨hres0, hmap0, _, _⟩ |
      ⟨_, r, hres1, _, _, _, _, _, _, _, hmap1, _, _⟩
  · refine ⟨by rw [clientState_bind, hst, hres0]; rfl,
      by rw [clientResult_bind, hst, hres0, hmap0]; rfl, ?_,
      validProg_bind hvp <| by
        rw [hst, hres0]
        exact validProg_pure _⟩
    rw [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres0]
    simpa only [↓reduceIte, memoryCost_pure, Nat.add_zero] using hmc
  · refine ⟨?_, ?_, ?_, ?_⟩
    · rw [clientState_bind, hst, hres1]
      simp only [Nat.one_ne_zero, ↓reduceIte]
      rw [clientState_bind, clientState_laneGetGenProg]; rfl
    · simp only [client_simps, hst, hres1, hmap1, Nat.one_ne_zero, ↓reduceIte,
      clientResult_laneGetGenProg]
    · simp only [← PFunctor.FreeM.bind_eq_bind, memoryCost_bind, hst, hres1, Nat.one_ne_zero,
        ↓reduceIte, memoryCost_laneGetGenProg, memoryCost_pure]
      omega
    · refine validProg_bind hvp ?_
      simp only [hst, hres1, Nat.one_ne_zero, ↓reduceIte]
      refine validProg_bind (validWhpProg_laneGetGenProg _) ?_
      rw [clientState_laneGetGenProg]
      exact validProg_pure _

theorem realizes_btreeLookupGen :
    Realizes .exact btreeLookupGenProg
      (WordEncoding.encode (α := ((WhpCoreParams × ℕ) × ℕ) × ℕ))
      (WordEncoding.encode (α := ℕ × ℕ))
      BTreeQueryGenPre
      (fun _ _ => 0) := by
  unfold btreeLookupGenProg
  have hloc := realizes_btreeLocateHitGen
  have hlg := realizes_laneGetGen
  realize
  all_goals
    rcases d with ⟨⟨⟨cp, base⟩, sIdx⟩, q⟩
    dsimp only [BTreeQueryGenPre] at *
    obtain ⟨c, U, V, w₀, n_max, insCount, sl, mapFn,
      henv, rfl, hsIdx, hins, hrep, hv, hq⟩ := h
    have hth := henv.2.2.2.1
    obtain rfl := henv.2.2.1
  · exact ⟨c, U, V, w, n_max, insCount, sl, mapFn, henv, rfl, hsIdx, hins, hrep, hv, hq⟩
  · rw [wp_large_wVal hth]
    exact (Nat.le_mul_of_pos_left _ (by have := eight_le_tMinWhp hth; omega)).trans_lt
      henv.valsWordBits_lt_w
  · obtain ⟨_, _, _, hres⟩ := btreeLocateHitGenProg_spec henv hsIdx hins hrep hv hq (s := s)
    rcases hres with ⟨hres0, _⟩ | ⟨_, r, hres1, _, hrc, hcnt_le, _⟩
    · simp_all
    · simp only [hres1, wp_large_wVal hth] at *
      exact ((Nat.mul_le_mul_right _ (hrc.le.trans (by omega))).trans_lt
        henv.valsWordBits_lt_w).trans Nat.lt_two_pow_self
  · exact henv.fits_const (by decide)

end Cslib.DataStructure.Dictionary.WordRAM.SuccinctWhp

end
