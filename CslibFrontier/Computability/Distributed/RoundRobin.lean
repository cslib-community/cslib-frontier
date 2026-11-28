/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.Dedup

/-!
# Round-Robin Coordinator Selection

Deterministic round-robin leader/coordinator selection `rotatingCoordinator` over a deduplicated
process enumeration `procs.dedup`, shared across round- and view-based distributed consensus
protocols (such as `Cslib.Distributed.PartialSynchrony` and
`Cslib.Distributed.FailureDetectors`).

## Main definitions

* `Cslib.Distributed.rotatingCoordinator`: round-robin coordinator `procs.dedup[r % L]` for round
  or view `r` (`fallback` is unused whenever `procs` is nonempty).

## Main results

* `Cslib.Distributed.exists_rotatingCoordinator_eq`: every target process `qStar` listed in `procs`
  becomes `rotatingCoordinator` within `procs.dedup.length` consecutive slots starting from any
  `r₀`.
* `Cslib.Distributed.exists_rotatingCoordinator_notMem`: pigeonhole non-faulty coordinator window —
  when `procs` enumerates `P` and `F.card ≤ t < Fintype.card P`, every window `[r₀, r₀ + t]` of
  `t + 1` consecutive slots contains at least one slot `rStar` with
  `rotatingCoordinator procs fallback rStar ∉ F`.
-/

public section

namespace Cslib.Distributed

open Finset

/-- Deterministic round-robin coordinator for round or view `r`, indexing into `procs.dedup` modulo
`procs.dedup.length` (`fallback` is unused whenever `procs` is nonempty). -/
@[expose] def rotatingCoordinator {P : Type*} [DecidableEq P]
    (procs : List P) (fallback : P) (r : ℕ) : P :=
  if h : r % procs.dedup.length < procs.dedup.length then
    procs.dedup[r % procs.dedup.length]
  else fallback

/-- Original round-robin hit lemma: every target process `qStar` listed in `procs` becomes
`rotatingCoordinator` within `procs.dedup.length` consecutive slots starting from any `r₀`. -/
theorem exists_rotatingCoordinator_eq {P : Type*} [DecidableEq P]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (fallback : P) (qStar : P) (r₀ : ℕ) :
    ∃ rStar, r₀ ≤ rStar ∧ rStar < r₀ + procs.dedup.length ∧
      rotatingCoordinator procs fallback rStar = qStar := by
  have hmem : qStar ∈ procs.dedup := List.mem_dedup.mpr (hprocs qStar)
  obtain ⟨idx, hidx, hget⟩ := List.mem_iff_getElem.mp hmem
  let L := procs.dedup.length
  have hL_pos : 0 < L := Nat.zero_lt_of_lt hidx
  let delta := (idx + L - r₀ % L) % L
  let rStar := r₀ + delta
  have hdelta_lt : delta < L := Nat.mod_lt _ hL_pos
  have hmod : rStar % L = idx := by
    have h := Nat.div_add_mod r₀ L
    have hr₀_lt : r₀ % L < L := Nat.mod_lt r₀ hL_pos
    have hsum : r₀ + (idx + L - r₀ % L) = idx + L * (r₀ / L + 1) := by
      rw [Nat.mul_add, Nat.mul_one]; omega
    rw [Nat.add_mod_mod, hsum, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hidx]
  refine ⟨rStar, Nat.le_add_right r₀ delta, by omega, ?_⟩
  simp only [rotatingCoordinator, show rStar % procs.dedup.length = idx from hmod, hidx,
    ↓reduceDIte, hget]

/-- Original pigeonhole coordinator window: when `procs` enumerates `P` and
`F.card ≤ t < Fintype.card P`, every window `[r₀, r₀ + t]` of `t + 1` consecutive slots contains at
least one slot `rStar` whose `rotatingCoordinator` lies outside `F`. -/
theorem exists_rotatingCoordinator_notMem {P : Type*} [Fintype P] [DecidableEq P]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    {F : Finset P} {t : ℕ} (hF : F.card ≤ t) (ht : t < Fintype.card P) (r₀ : ℕ) :
    ∃ rStar, r₀ ≤ rStar ∧ rStar ≤ r₀ + t ∧ rotatingCoordinator procs fallback rStar ∉ F := by
  have hlen : procs.dedup.length = Fintype.card P := by
    rw [← List.toFinset_card_of_nodup procs.nodup_dedup,
      Finset.eq_univ_iff_forall.mpr fun p =>
        List.mem_toFinset.mpr (List.mem_dedup.mpr (hprocs p)),
      Finset.card_univ]
  have hpos : 0 < procs.dedup.length := by omega
  let f : Fin (t + 1) → P := fun k => rotatingCoordinator procs fallback (r₀ + k.val)
  have hinj : Function.Injective f := by
    intro k₁ k₂ heq
    simp only [f, rotatingCoordinator, Nat.mod_lt _ hpos, ↓reduceDIte] at heq
    have hmod : (r₀ + k₁.val) % procs.dedup.length = (r₀ + k₂.val) % procs.dedup.length :=
      (List.Nodup.getElem_inj_iff (List.nodup_dedup procs)).1 heq
    have hd₁ := Nat.div_add_mod (r₀ + k₁.val) procs.dedup.length
    have hd₂ := Nat.div_add_mod (r₀ + k₂.val) procs.dedup.length
    rw [hmod] at hd₁
    ext
    rcases lt_trichotomy ((r₀ + k₁.val) / procs.dedup.length)
      ((r₀ + k₂.val) / procs.dedup.length) with h | h | h
    · have := Nat.mul_le_mul_left procs.dedup.length (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this; omega
    · rw [h] at hd₁; omega
    · have := Nat.mul_le_mul_left procs.dedup.length (Nat.succ_le_of_lt h)
      rw [Nat.mul_succ] at this; omega
  have hcard : F.card < (Finset.univ.image f).card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
    omega
  obtain ⟨_, hp_img, hpF⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hp_img
  exact ⟨r₀ + k.val, Nat.le_add_right r₀ k.val, by omega, hpF⟩

end Cslib.Distributed
