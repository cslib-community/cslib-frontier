/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.RecordData
import Mathlib.Data.List.Nodup

/-!
# The value of an actual decoded producer query block

The actual occurrence list is exactly the existing finite `chunkOf`, without repetitions,
and its `i`-th pair has class rank `k*queryCap+i`. Consumers can use original ET pairs directly
through this packaged readback; no alternative query notion or supplied routing table is added.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle

/-- The actual decoded list consists of all pairs of the existing chunk, once each, in
increasing class rank. The indexed equation specifies the order as well as set membership. -/
theorem decodedQueries_chunkOf {n D g p : ℕ} (values : ℕ → ℤ)
    (wAB : Fin n → Fin n → ℤ) (hn : 0 < n) (hp : p ≠ 0)
    (hAB : ∀ a b, values (pairIndex (a, b)) = wAB a b)
    (hD : 1 ≤ D) (hDn : D ≤ n)
    {initial y : Data 64} (h : Instances.Output n D g p values initial y)
    (rho : Fin p) (k : ℕ)
    (hk : k < numChunks (residueClass wAB p rho) (queryCap n D)) :
    let q := 5 + 6 * (n * n) + p + 2 * rho.val * (n * n) + 2 * (k * queryCap n D)
    let Q := min (queryCap n D) ((residueClass wAB p rho).card - k * queryCap n D)
    let qs := decodedQueries hn y.mem q Q
    (∀ i : Fin qs.length, qs.get i ∈ chunkOf wAB D p rho k ∧
      rankIn (residueClass wAB p rho) (qs.get i) = k * queryCap n D + i.val) ∧
      qs.Nodup ∧ qs.toFinset = chunkOf wAB D p rho k := by
  let S := residueClass wAB p rho
  let cap := queryCap n D
  let q := 5 + 6 * (n * n) + p + 2 * rho.val * (n * n) + 2 * (k * cap)
  let Q := min cap (S.card - k * cap)
  let qs := decodedQueries hn y.mem q Q
  obtain ⟨-, hpair⟩ := output_query_coordinates values wAB hp hAB hD hDn h rho k hk
  have hget (i : Fin qs.length) : qs.get i ∈ chunkOf wAB D p rho k ∧
      rankIn S (qs.get i) = k * cap + i.val := by
    obtain ⟨pair, ⟨hmem, hrank, hvA, hvB⟩, -⟩ :=
      hpair i.val (by simpa only [qs, decodedQueries_length] using i.isLt)
    obtain ⟨h1, h2⟩ := decodedQueries_get_val hn y.mem q Q i
      (hvA ▸ pair.1.isLt) (hvB ▸ pair.2.isLt)
    exact Prod.ext (Fin.ext (h1.trans hvA)) (Fin.ext (h2.trans hvB)) ▸ ⟨hmem, hrank⟩
  refine ⟨hget, List.nodup_iff_injective_get.mpr fun i j hij => Fin.ext (Nat.add_left_cancel
    ((hget i).2.symm.trans ((congrArg (rankIn S) hij).trans (hget j).2))), ?_⟩
  ext pair
  simp only [List.mem_toFinset, List.mem_iff_get]
  refine ⟨fun ⟨i, he⟩ => he ▸ (hget i).1, fun hm => ?_⟩
  obtain ⟨hS, hk_eq⟩ : pair ∈ S ∧ rankIn S pair / cap = k := by
    simpa only [chunkOf, chunk, Finset.mem_filter, S, cap] using hm
  have hrank := rankIn_lt_card hS
  have hrem := Nat.mod_lt (rankIn S pair) (one_le_queryCap hD hDn)
  have hsplit := Nat.div_add_mod (rankIn S pair) cap
  rw [hk_eq, Nat.mul_comm cap k] at hsplit
  let i : Fin qs.length := ⟨rankIn S pair % cap, by
    rw [decodedQueries_length]
    dsimp only [Q, cap] at hsplit ⊢; omega⟩
  exact ⟨i, rankIn_injOn S (Finset.mem_filter.mp (hget i).1).1 hS
    (((hget i).2).trans hsplit)⟩

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
