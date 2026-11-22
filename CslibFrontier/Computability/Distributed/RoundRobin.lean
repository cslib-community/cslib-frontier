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
    have hr₀_lt : r₀ % L < L := Nat.mod_lt r₀ hL_pos
    calc rStar % L
        = (r₀ % L + delta % L) % L := Nat.add_mod r₀ delta L
      _ = ((r₀ % L) % L + (idx + L - r₀ % L) % L) % L := by
          rw [Nat.mod_eq_of_lt hr₀_lt]
          simp only [delta, Nat.mod_mod]
      _ = (r₀ % L + (idx + L - r₀ % L)) % L :=
          (Nat.add_mod (r₀ % L) (idx + L - r₀ % L) L).symm
      _ = (idx + L) % L := by congr 1; omega
      _ = idx := by rw [Nat.add_mod_right, Nat.mod_eq_of_lt hidx]
  refine ⟨rStar, Nat.le_add_right r₀ delta, by omega, ?_⟩
  unfold rotatingCoordinator
  change (if h : rStar % L < L then procs.dedup[rStar % L] else fallback) = qStar
  simp only [hmod, L, hidx, ↓reduceDIte]
  exact hget

/-- Original pigeonhole coordinator window: when `procs` enumerates `P` and
`F.card ≤ t < Fintype.card P`, every window `[r₀, r₀ + t]` of `t + 1` consecutive slots contains at
least one slot `rStar` whose `rotatingCoordinator` lies outside `F`. -/
theorem exists_rotatingCoordinator_notMem {P : Type*} [Fintype P] [DecidableEq P]
    {procs : List P} (hprocs : ∀ p : P, p ∈ procs) (fallback : P)
    {F : Finset P} {t : ℕ} (hF : F.card ≤ t) (ht : t < Fintype.card P) (r₀ : ℕ) :
    ∃ rStar, r₀ ≤ rStar ∧ rStar ≤ r₀ + t ∧ rotatingCoordinator procs fallback rStar ∉ F := by
  have huniv : procs.dedup.toFinset = (Finset.univ : Finset P) :=
    Finset.eq_univ_iff_forall.mpr fun p => List.mem_toFinset.mpr (List.mem_dedup.mpr (hprocs p))
  have hlen : procs.dedup.length = Fintype.card P := by
    rw [← List.toFinset_card_of_nodup procs.nodup_dedup, huniv, Finset.card_univ]
  have hpos : 0 < procs.dedup.length := by omega
  let f : Fin (t + 1) → P := fun k => rotatingCoordinator procs fallback (r₀ + k.val)
  have hinj : Function.Injective f := by
    intro k₁ k₂ heq
    have hlt₁ : (r₀ + k₁.val) % procs.dedup.length < procs.dedup.length := Nat.mod_lt _ hpos
    have hlt₂ : (r₀ + k₂.val) % procs.dedup.length < procs.dedup.length := Nat.mod_lt _ hpos
    simp only [f, rotatingCoordinator, hlt₁, hlt₂, ↓reduceDIte] at heq
    have hmod : (r₀ + k₁.val) % procs.dedup.length = (r₀ + k₂.val) % procs.dedup.length :=
      (List.Nodup.getElem_inj_iff (List.nodup_dedup procs)).1 heq
    have hk₁ : k₁.val < procs.dedup.length := by omega
    have hk₂ : k₂.val < procs.dedup.length := by omega
    have hcancel : ∀ a b, a < procs.dedup.length → b < procs.dedup.length → a ≤ b →
        (r₀ + a) % procs.dedup.length = (r₀ + b) % procs.dedup.length → a = b := by
      intro a b _ _ _ hrem
      have hd₁ := Nat.div_add_mod (r₀ + a) procs.dedup.length
      have hd₂ := Nat.div_add_mod (r₀ + b) procs.dedup.length
      have hle_div : (r₀ + a) / procs.dedup.length ≤ (r₀ + b) / procs.dedup.length :=
        Nat.div_le_div_right (by omega)
      rcases eq_or_lt_of_le hle_div with hdiv_eq | hdiv_lt
      · rw [hdiv_eq, hrem] at hd₁
        omega
      · have hmul : procs.dedup.length * ((r₀ + a) / procs.dedup.length + 1) ≤
            procs.dedup.length * ((r₀ + b) / procs.dedup.length) :=
          Nat.mul_le_mul_left _ hdiv_lt
        rw [Nat.mul_add, Nat.mul_one] at hmul
        rw [hrem] at hd₁
        omega
    ext
    rcases le_total k₁.val k₂.val with hle | hle
    · exact hcancel k₁.val k₂.val hk₁ hk₂ hle hmod
    · exact (hcancel k₂.val k₁.val hk₂ hk₁ hle hmod.symm).symm
  let img : Finset P := Finset.univ.image f
  have hcard : img.card = t + 1 := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_fin]
  obtain ⟨p, hp_img, hpF⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (show F.card < img.card by omega)
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.1 hp_img
  exact ⟨r₀ + k.val, Nat.le_add_right r₀ k.val, by omega, hpF⟩

end Cslib.Distributed
