/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.WordRAM.ResizableSuccinct.Params
import CslibFrontier.Tactic.UpdateSimp

/-!
# Circular Tail-to-Dense Compaction Bijection, Key Reconstruction, and `CompactedRep`

This module defines the circular tail-to-dense bijection (`denseOfCirc`, `WindowInv`,
`TailDenseInv`), direct $O(1)$ owner-bucket and logical-slot recovery on dense slots `d ∈ [0, n)`
(`ownerBucketOfDense`, `logicalIdxOfDense`), and the array-coupling invariants (`WindowCoupled`,
`FixedCoupled`) for the resizable succinct dynamic dictionary of [Bender, Farach-Colton,
J. Kuszmaul and W. Kuszmaul, SOSA 2024][BenderFarachColtonKuszmaulKuszmaul2024].

## Design

1. **Circular `[b_win, b_win + n_win)` tail window (`denseOfCirc`, `WindowInv`):**
   Active full-slab slots `phys < gm 0 * slabSize N` map directly to dense index `d = phys`.
   Active tail slots `phys = N - 1 - t` (`t < gm 1`) store a circular residue `c = td t < M`
   (`M = maxTailItems N`) and resolve to `d = denseOfCirc M b_win c ∈ [b_win, b_win + n_win)`,
   with inverse `dt (d % M) = t`. Shifting `b_win` by `± 1` (`winGrowLeft`, `winShrinkLeft`) or
   resizing `n_win` by `± 1` (`winGrowRight`, `winShrinkRight`) updates only $O(1)$ entries of
   `(td, dt)` without reindexing untouched tail items.
2. **Array-level coupling (`WindowCoupled`, `FixedCoupled`):**
   `WindowCoupled` separates `metaBase` from `itemBase` so both resting in-epoch states and
   single-tape epoch migration (Zone 1 metadata + Zone 3 shared item arena) couple directly to the
   fixed-capacity `Succinct` array extractors (`gmAt`, `lmAt`, `quotAt`, `valAt`).

## Main definitions

* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.denseOfCirc`, `WindowInv`,
  `TailDenseInv`, `canonTD`, `canonDT`, `denseOfPhys`, `physByBase`, `winGrowRight`, `winGrowLeft`,
  `winShrinkRight`, `winShrinkLeft`: circular tail-to-dense bijection and $O(1)$ window updates.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ownerBucketOfDense`,
  `logicalIdxOfDense`: $O(1)$ owner-bucket and logical-slot recovery on dense slots `d ∈ [0, n)`.
* `Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct.ghostW`, `WindowCoupled`,
  `FixedCoupled`: fixed-capacity array coupling invariants.

## Main results

* `winGrowRight_spec`, `winGrowLeft_spec`, `winShrinkRight_spec`, `winShrinkLeft_spec`,
  `physByBase_winGrowRight`, `physByBase_winGrowLeft`, `physByBase_winShrinkRight`,
  `physByBase_winShrinkLeft`: invariant preservation and slot-mapping laws for window transitions.
* `ownerBucketOfDense_lt_and_slotOf`, `denseOfPhys_slotOf_lt_and_inv`,
  `physOfDense_eq_slotOf_owner`: exact bijection between dense slots and active bucket slots.

## References

* [M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, *Modern Hashing Made Simple*,
  Sections 3–4][BenderFarachColtonKuszmaulKuszmaul2024]
-/

public section

namespace Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct

open Cslib.WordRAM Cslib.WordRAM.Resizable
open Cslib.DataStructure Cslib.DataStructure.Memory
open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Cslib.DataStructure.Dictionary.SuccinctBucket
open Cslib.DataStructure.Dictionary.WordRAM.BitPackedArray
open Cslib.DataStructure.Dictionary.WordRAM.Succinct
open Cslib.DataStructure.HashFamily.WordRAM

/-! ## Section 1: Circular Tail-to-Dense Window Bijection (`denseOfCirc`, `WindowInv`) -/

/-- Recover the unique `d ∈ [base_tail, base_tail + M)` with `d % M = c` (for `0 < M`, `c < M`). -/
@[expose] def denseOfCirc (M base_tail c : ℕ) : ℕ :=
  if M = 0 then base_tail else base_tail + (c + M - base_tail % M) % M

theorem denseOfCirc_ge (M b c : ℕ) : b ≤ denseOfCirc M b c := by
  unfold denseOfCirc; split_ifs <;> omega

theorem denseOfCirc_mod {M base_tail c : ℕ} (hM : 0 < M) (hc : c < M) :
    denseOfCirc M base_tail c % M = c := by
  unfold denseOfCirc
  have hsplit : base_tail + (c + M - base_tail % M) = c + M * (base_tail / M + 1) := by
    have := Nat.div_add_mod base_tail M
    have := Nat.mod_lt base_tail hM
    rw [Nat.mul_add, Nat.mul_one]; omega
  rw [ite_eq_right hM.ne', Nat.add_mod_mod, hsplit, Nat.add_mul_mod_self_left,
    Nat.mod_eq_of_lt hc]

theorem denseOfCirc_mod_self {M base_tail d : ℕ} (hM : 0 < M)
    (hlo : base_tail ≤ d) (hhi : d < base_tail + M) :
    denseOfCirc M base_tail (d % M) = d := by
  set x := denseOfCirc M base_tail (d % M)
  have hx_lo : base_tail ≤ x := denseOfCirc_ge M base_tail (d % M)
  have hx_hi : x < base_tail + M := by
    simp only [x, denseOfCirc, ite_eq_right hM.ne']
    exact Nat.add_lt_add_left (Nat.mod_lt _ hM) _
  have hmod : x % M = d % M := denseOfCirc_mod hM (Nat.mod_lt d hM)
  have hx_div := Nat.div_add_mod x M
  have hd_div := Nat.div_add_mod d M
  have h1 : x / M ≤ d / M := Nat.le_of_lt_succ <|
    Nat.lt_of_mul_lt_mul_left (a := M) (by rw [Nat.mul_succ]; omega)
  have h2 : d / M ≤ x / M := Nat.le_of_lt_succ <|
    Nat.lt_of_mul_lt_mul_left (a := M) (by rw [Nat.mul_succ]; omega)
  rw [← hx_div, ← hd_div, Nat.le_antisymm h1 h2, hmod]

theorem denseOfCirc_eq_self_iff {M b c d : ℕ} (hM : 0 < M) (hc : c < M)
    (hlo : b ≤ d) (hhi : d < b + M) :
    denseOfCirc M b c = d ↔ c = d % M :=
  ⟨fun heq => by rw [← heq, denseOfCirc_mod hM hc], fun h => h ▸ denseOfCirc_mod_self hM hlo hhi⟩

theorem denseOfCirc_succ_of_ne_mod {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M b c < b + M) (hne : c ≠ b % M) :
    denseOfCirc M (b + 1) c = denseOfCirc M b c := by
  set d := denseOfCirc M b c
  have hlo : b ≤ d := denseOfCirc_ge M b c
  have hne_d : d ≠ b := fun hd => hne ((denseOfCirc_eq_self_iff hM hc le_rfl (by omega)).mp hd)
  rw [← denseOfCirc_mod (base_tail := b) hM hc]
  exact denseOfCirc_mod_self hM (by omega) (by omega)

theorem denseOfCirc_pred_of_lt {M b c : ℕ} (hM : 0 < M) (hc : c < M)
    (hhi : denseOfCirc M (b + 1) c < b + M) :
    denseOfCirc M b c = denseOfCirc M (b + 1) c ∧ c ≠ b % M := by
  set d := denseOfCirc M (b + 1) c
  have hlo : b + 1 ≤ d := denseOfCirc_ge M (b + 1) c
  have heq : denseOfCirc M b c = d :=
    denseOfCirc_mod hM hc ▸ denseOfCirc_mod_self hM (by omega) hhi
  refine ⟨heq, fun hmod_b => ?_⟩
  have hdb : denseOfCirc M b c = b := hmod_b ▸ denseOfCirc_mod_self hM le_rfl (by omega)
  omega

/-- Circular tail-to-dense bijection invariant on `[b, b + n)` modulo `M`. -/
structure WindowInv (M b n : ℕ) (td dt : ℕ → ℕ) : Prop where
  td_lt : ∀ t < n, td t < M
  dense_lt : ∀ t < n, denseOfCirc M b (td t) < b + n
  dt_td : ∀ t < n, dt (td t) = t
  owner_valid : ∀ d, b ≤ d → d < b + n → dt (d % M) < n ∧ td (dt (d % M)) = d % M

/-- Specialization of `WindowInv` to the resting tail window `[n_slabs * slabSize N, +n_tails)`. -/
@[expose] def TailDenseInv (N n_slabs n_tails : ℕ) (td dt : ℕ → ℕ) : Prop :=
  WindowInv (maxTailItems N) (n_slabs * slabSize N) n_tails td dt

theorem windowInv_zero (M b : ℕ) (td dt : ℕ → ℕ) : WindowInv M b 0 td dt :=
  ⟨by omega, by omega, by omega, by omega⟩

/-- Canonical `td` mapping `(b + t) % M` for initial / rebuilt epochs. -/
@[expose] def canonTD (M b t : ℕ) : ℕ := if M = 0 then 0 else (b + t) % M

/-- Canonical `dt` mapping `(c + M - b % M) % M` for initial / rebuilt epochs. -/
@[expose] def canonDT (M b c : ℕ) : ℕ := if M = 0 then 0 else (c + M - b % M) % M

theorem windowInv_canon {M b n : ℕ} (hn : n ≤ M) :
    WindowInv M b n (canonTD M b) (canonDT M b) ∧
    (∀ i, canonTD M b i < max M 1) ∧ (∀ i, canonDT M b i < max M 1) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · obtain rfl : n = 0 := by omega
    refine ⟨windowInv_zero 0 b _ _, fun _ => ?_, fun _ => ?_⟩ <;> simp [canonTD, canonDT]
  · have hM0 : M ≠ 0 := hM.ne'
    have hmax : max M 1 = M := max_eq_left hM
    have htd_eq (t : ℕ) : canonTD M b t = (b + t) % M := ite_eq_right hM0
    have hdt_eq (c : ℕ) : canonDT M b c = (c + M - b % M) % M := ite_eq_right hM0
    have hcirc (c : ℕ) : denseOfCirc M b c = b + canonDT M b c := by
      simp only [denseOfCirc, hM0, ↓reduceIte, hdt_eq]
    refine ⟨⟨fun t _ => by rw [htd_eq]; exact Nat.mod_lt _ hM, fun t ht => ?_, fun t ht => ?_,
      fun d hlo hhi => ?_⟩,
      fun i => by rw [hmax, htd_eq]; exact Nat.mod_lt _ hM,
      fun i => by rw [hmax, hdt_eq]; exact Nat.mod_lt _ hM⟩
    · rw [htd_eq, denseOfCirc_mod_self hM (by omega) (by omega)]; omega
    · have h1 := htd_eq t ▸ denseOfCirc_mod_self hM (base_tail := b) (d := b + t)
        (by omega) (by omega)
      rw [hcirc] at h1
      omega
    · have h1 := denseOfCirc_mod_self hM hlo (by omega : d < b + M)
      rw [hcirc] at h1
      have hdt : canonDT M b (d % M) = d - b := by omega
      rw [hdt]
      exact ⟨by omega, by rw [htd_eq, Nat.add_sub_of_le hlo]⟩

/-- Map a physical slot `phys < N` to its dense index `d < n`:
when `bucketBits N = 0`, `phys`; else `phys` on full slabs `< gm 0 * slabSize N` and
`denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td (N - 1 - phys))` on tail slots. -/
@[expose] def denseOfPhys (N : ℕ) (gm td : ℕ → ℕ) (phys : ℕ) : ℕ :=
  if bucketBits N = 0 then phys
  else if phys < gm 0 * slabSize N then phys
  else denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td (N - 1 - phys))

/-- Physical slot of dense item `d` parameterized by tail window base `b_tail`. -/
@[expose] def physByBase (N b_tail : ℕ) (dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < b_tail then d
  else N - 1 - dt (d % maxTailItems N)

/-- Resting specialization `physByBase N (gm 0 * slabSize N) dt`. -/
@[expose] def physOfDense (N : ℕ) (gm dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  physByBase N (gm 0 * slabSize N) dt d

private theorem mod_ne_of_mem_window {M b d₁ d₂ : ℕ} (hM : 0 < M)
    (h₁lo : b ≤ d₁) (h₁hi : d₁ < b + M) (h₂lo : b ≤ d₂) (h₂hi : d₂ < b + M) (hne : d₁ ≠ d₂) :
    d₁ % M ≠ d₂ % M := fun heq =>
  hne ((denseOfCirc_mod_self hM h₁lo h₁hi).symm.trans (heq ▸ denseOfCirc_mod_self hM h₂lo h₂hi))

private theorem winGrow_core_spec {M b₀ b n d_new : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b₀ n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M)
    (hd_new_lo : b ≤ d_new) (hd_new_hi : d_new < b + (n + 1))
    (hdense : ∀ t < n, denseOfCirc M b (td t) < b + (n + 1) ∧ td t ≠ d_new % M)
    (howner : ∀ d, b ≤ d → d < b + (n + 1) → d ≠ d_new → b₀ ≤ d ∧ d < b₀ + n) :
    let c_new := d_new % M
    let td' := Function.update td n c_new
    let dt' := Function.update dt c_new n
    WindowInv M b (n + 1) td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  intro c_new td' dt'
  have hM_pos : 0 < M := by omega
  have hc_lt : c_new < M := Nat.mod_lt d_new hM_pos
  have hcirc_new : denseOfCirc M b c_new = d_new :=
    denseOfCirc_mod_self hM_pos hd_new_lo (by omega)
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl <;> dsimp only [td'] <;> update_simp
    · exact hw.td_lt t ht'
    · exact hc_lt
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl <;> dsimp only [td'] <;> update_simp
    · exact (hdense t ht').1
    · rw [hcirc_new]; exact hd_new_hi
  · rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht' | rfl <;> dsimp only [td', dt']
    · have := (hdense t ht').2; update_simp; exact hw.dt_td t ht'
    · update_simp
  · by_cases hd : d = d_new <;> dsimp only [td', dt']
    · subst hd; update_simp; exact ⟨Nat.lt_succ_self n, rfl⟩
    · obtain ⟨hlo₀, hhi₀⟩ := howner d hlo hhi hd
      have hown := hw.owner_valid d hlo₀ hhi₀
      have : d % M ≠ c_new := by rw [← hown.2]; exact (hdense _ hown.1).2
      have := hown.1; update_simp; exact ⟨by omega, hown.2⟩
  · by_cases hi : i = n <;> dsimp only [td'] <;> update_simp <;> [exact hc_lt; exact htd_b i]
  · by_cases hi : i = c_new <;> dsimp only [dt'] <;> update_simp <;> [omega; exact hdt_b i]

/-- Grow the circular window `[b, b + n)` on the right by 1 to `[b, b + (n + 1))`. -/
@[expose] def winGrowRight (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c := (b + n) % M
    (Function.update td n c, Function.update dt c n)

theorem winGrowRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winGrowRight M b n (td, dt) with
    | (td', dt') => WindowInv M b (n + 1) td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winGrowRight]
  refine winGrow_core_spec hw hM htd_b hdt_b (d_new := b + n) (by omega) (by omega)
    (fun t ht => ⟨by have := hw.dense_lt t ht; omega, fun heq => ?_⟩)
    (fun d hlo hhi hne => ⟨hlo, by omega⟩)
  have hlt := hw.dense_lt t ht
  rw [heq, denseOfCirc_mod_self (by omega) (by omega) (by omega)] at hlt
  omega

/-- Grow the circular window `[b + 1, b + 1 + n)` on the left by 1 to `[b, b + (n + 1))`. -/
@[expose] def winGrowLeft (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c := b % M
    (Function.update td n c, Function.update dt c n)

theorem winGrowLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M (b + 1) n td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winGrowLeft M b n (td, dt) with
    | (td', dt') => WindowInv M b (n + 1) td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winGrowLeft]
  refine winGrow_core_spec hw hM htd_b hdt_b (d_new := b) le_rfl (by omega)
    (fun t ht => ?_) (fun _ _ _ _ => ⟨by omega, by omega⟩)
  obtain ⟨heq, hne⟩ := denseOfCirc_pred_of_lt (b := b) (by omega) (hw.td_lt t ht)
    (by have := hw.dense_lt t ht; omega)
  exact ⟨heq.trans_lt (by have := hw.dense_lt t ht; omega), hne⟩

private theorem WindowInv.td_inj {M b n : ℕ} {td dt : ℕ → ℕ} (hw : WindowInv M b n td dt)
    {t₁ t₂ : ℕ} (ht₁ : t₁ < n) (ht₂ : t₂ < n) (heq : td t₁ = td t₂) : t₁ = t₂ := by
  rw [← hw.dt_td t₁ ht₁, ← hw.dt_td t₂ ht₂, heq]

/-- Shrink the circular window `[b, b + (n + 1))` on the right by 1 to `[b, b + n)`. -/
@[expose] def winShrinkRight (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c_rem := (b + n) % M
    let t_rem := dt c_rem
    let c_last := td n
    (Function.update td t_rem c_last, Function.update dt c_last t_rem)

private theorem winShrink_core_spec {M b b' n : ℕ} {td dt : ℕ → ℕ} {c_rem : ℕ}
    (hw : WindowInv M b (n + 1) td dt)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M)
    (hown_rem : dt c_rem < n + 1 ∧ td (dt c_rem) = c_rem)
    (hlt_b' : ∀ t < n + 1, t ≠ dt c_rem → denseOfCirc M b' (td t) < b' + n)
    (hne_crem : ∀ d, b' ≤ d → d < b' + n → d % M ≠ c_rem)
    (howner : ∀ d, b' ≤ d → d < b' + n → dt (d % M) < n + 1 ∧ td (dt (d % M)) = d % M) :
    let t_rem := dt c_rem
    let c_last := td n
    let td' := Function.update td t_rem c_last
    let dt' := Function.update dt c_last t_rem
    WindowInv M b' n td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  intro t_rem c_last td' dt'
  have ht_rem_lt : t_rem < n + 1 := hown_rem.1
  have htd_trem : td t_rem = c_rem := hown_rem.2
  have hc_last_lt : c_last < M := hw.td_lt n (Nat.lt_succ_self n)
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun t ht => ?_, fun d hlo hhi => ?_⟩,
    fun i => ?_, fun i => ?_⟩
  · by_cases heq : t = t_rem <;> dsimp only [td'] <;> update_simp
    · exact hc_last_lt
    · exact hw.td_lt t (by omega)
  · by_cases heq : t = t_rem <;> dsimp only [td'] <;> update_simp
    · exact hlt_b' n (Nat.lt_succ_self n) (by omega)
    · exact hlt_b' t (by omega) heq
  · by_cases heq : t = t_rem <;> dsimp only [td', dt']
    · update_simp; exact heq.symm
    · have : td t ≠ c_last := fun hc =>
        Nat.ne_of_lt ht (hw.td_inj (by omega) (Nat.lt_succ_self n) hc)
      update_simp; exact hw.dt_td t (by omega)
  · have hown := howner d hlo hhi
    have hne_c := hne_crem d hlo hhi
    have hne_trem : dt (d % M) ≠ t_rem := fun heq => hne_c (by rw [← hown.2, heq, htd_trem])
    by_cases hclast : d % M = c_last <;> dsimp only [dt', td'] <;> update_simp
    · have : t_rem ≠ n := fun heq => hne_c (by rw [hclast, ← htd_trem, heq])
      exact ⟨by omega, hclast.symm⟩
    · have : dt (d % M) ≠ n := fun heq => hclast (by rw [← hown.2, heq])
      exact ⟨by omega, hown.2⟩
  · by_cases hi : i = t_rem <;> dsimp only [td'] <;> update_simp <;>
      [exact hc_last_lt; exact htd_b i]
  · by_cases hi : i = c_last <;> dsimp only [dt'] <;> update_simp <;>
      [exact hdt_b c_rem; exact hdt_b i]

theorem winShrinkRight_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winShrinkRight M b n (td, dt) with
    | (td', dt') => WindowInv M b n td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winShrinkRight]
  have hM_pos : 0 < M := by omega
  have hown_rem := hw.owner_valid (b + n) (by omega) (by omega)
  have hlt_bn : ∀ t < n + 1, t ≠ dt ((b + n) % M) → denseOfCirc M b (td t) < b + n :=
    fun t ht hne => by
    have hlt := hw.dense_lt t ht
    have hne_d : denseOfCirc M b (td t) ≠ b + n := fun hd => by
      have hmod := (denseOfCirc_eq_self_iff hM_pos (hw.td_lt t ht) (by omega) (by omega)).mp hd
      exact hne (hw.td_inj ht hown_rem.1 (hmod.trans hown_rem.2.symm))
    omega
  exact winShrink_core_spec hw htd_b hdt_b hown_rem hlt_bn
    (fun d hlo hhi => mod_ne_of_mem_window hM_pos hlo (by omega) (by omega) (by omega) (by omega))
    (fun d hlo hhi => hw.owner_valid d hlo (by omega))

/-- Shrink the circular window `[b, b + (n + 1))` on the left by 1 to `[b + 1, b + 1 + n)`. -/
@[expose] def winShrinkLeft (M b n : ℕ) : (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | (td, dt) =>
    let c_rem := b % M
    let t_rem := dt c_rem
    let c_last := td n
    (Function.update td t_rem c_last, Function.update dt c_last t_rem)

theorem winShrinkLeft_spec {M b n : ℕ} {td dt : ℕ → ℕ}
    (hw : WindowInv M b (n + 1) td dt) (hM : n + 1 ≤ M)
    (htd_b : ∀ i, td i < M) (hdt_b : ∀ i, dt i < M) :
    match winShrinkLeft M b n (td, dt) with
    | (td', dt') => WindowInv M (b + 1) n td' dt' ∧ (∀ i, td' i < M) ∧ (∀ i, dt' i < M) := by
  dsimp only [winShrinkLeft]
  have hM_pos : 0 < M := by omega
  have hown_rem := hw.owner_valid b le_rfl (by omega)
  have hsucc : ∀ t < n + 1, t ≠ dt (b % M) → denseOfCirc M (b + 1) (td t) < b + 1 + n :=
    fun t ht hne => by
      have hlt := hw.dense_lt t ht
      have hne_c : td t ≠ b % M := fun hc =>
        hne (hw.td_inj ht hown_rem.1 (hc.trans hown_rem.2.symm))
      rw [denseOfCirc_succ_of_ne_mod hM_pos (hw.td_lt t ht) (by omega) hne_c]; omega
  exact winShrink_core_spec hw htd_b hdt_b hown_rem hsucc
    (fun d hlo hhi => mod_ne_of_mem_window hM_pos (by omega) (by omega) le_rfl (by omega)
      (by omega))
    (fun d hlo hhi => hw.owner_valid d (by omega) (by omega))

theorem physByBase_winGrowRight {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hM : n + 1 ≤ maxTailItems N) :
    match winGrowRight (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      physByBase N b dt' (b + n) = N - 1 - n ∧
      (∀ d < b + n, physByBase N b dt' d = physByBase N b dt d) := by
  dsimp only [winGrowRight]
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < maxTailItems N := by omega
  refine ⟨?_, fun d hd => ?_⟩
  · unfold physByBase; rw [ite_eq_right hb0, ite_eq_right (by omega)]; update_simp
  · simp only [physByBase, hb0, ↓reduceIte]
    split_ifs with hlt
    · rfl
    · have : d % maxTailItems N ≠ (b + n) % maxTailItems N :=
        mod_ne_of_mem_window (b := b) hM_pos (by omega) (by omega) (by omega) (by omega) (by omega)
      update_simp

theorem physByBase_winGrowLeft {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hM : n + 1 ≤ maxTailItems N) :
    match winGrowLeft (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      physByBase N b dt' b = N - 1 - n ∧
      (∀ d < b + 1 + n, d ≠ b → physByBase N b dt' d = physByBase N (b + 1) dt d) := by
  dsimp only [winGrowLeft]
  have hb0 : bucketBits N ≠ 0 := Nat.ne_of_gt hb_pos
  have hM_pos : 0 < maxTailItems N := by omega
  refine ⟨?_, fun d hd hne => ?_⟩
  · unfold physByBase; rw [ite_eq_right hb0, ite_eq_right (by omega)]; update_simp
  · have h1 : d < b + 1 ↔ d < b := by omega
    simp only [physByBase, hb0, h1, ↓reduceIte]
    split_ifs
    · rfl
    · have := mod_ne_of_mem_window hM_pos (by omega) (by omega) le_rfl (by omega) hne
      update_simp

private theorem physByBase_update_dt_last {N b b' n t_rem : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b (n + 1) td dt)
    (hM : n + 1 ≤ maxTailItems N) :
    let d_last := denseOfCirc (maxTailItems N) b (td n)
    let dt' := Function.update dt (td n) t_rem
    b ≤ d_last ∧ d_last < b + n + 1 ∧
    (¬(d_last < b') → physByBase N b' dt' d_last = N - 1 - t_rem) ∧
    (∀ d < b + n + 1, (d < b' ↔ d < b) → d ≠ d_last →
      physByBase N b' dt' d = physByBase N b dt d) := by
  set M := maxTailItems N
  set d_last := denseOfCirc M b (td n)
  have hb0 : bucketBits N ≠ 0 := hb_pos.ne'
  have hM_pos : 0 < M := by omega
  have hd_last_lt : d_last < b + n + 1 := hw.dense_lt n (Nat.lt_succ_self n)
  have hd_last_ge : b ≤ d_last := denseOfCirc_ge M b (td n)
  have hd_last_mod : d_last % M = td n :=
    denseOfCirc_mod hM_pos (hw.td_lt n (Nat.lt_succ_self n))
  refine ⟨hd_last_ge, hd_last_lt, fun hnot => ?_, fun d hd hiff hne => ?_⟩
  · simp only [physByBase, hb0, hnot, ↓reduceIte]; update_simp
  · simp only [physByBase, hb0, ↓reduceIte]
    by_cases hlt : d < b
    · simp only [hlt, hiff.mpr hlt, ↓reduceIte]
    · simp only [hlt, mt hiff.mp hlt, ↓reduceIte]
      have : d % M ≠ td n := hd_last_mod ▸
        mod_ne_of_mem_window hM_pos (by omega) (by omega) hd_last_ge (by omega) hne
      update_simp

theorem physByBase_winShrinkRight {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b (n + 1) td dt)
    (hM : n + 1 ≤ maxTailItems N) :
    match winShrinkRight (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      let d_last := denseOfCirc (maxTailItems N) b (td n)
      d_last < b + n + 1 ∧
      physByBase N b dt' d_last = physByBase N b dt (b + n) ∧
      (∀ d < b + n, d ≠ d_last → physByBase N b dt' d = physByBase N b dt d) := by
  dsimp only [winShrinkRight]
  obtain ⟨hge, hlt, hlast, hkeep⟩ := physByBase_update_dt_last (b' := b)
    (t_rem := dt ((b + n) % maxTailItems N)) hb_pos hw hM
  refine ⟨hlt, (hlast (by omega)).trans ?_, fun d hd hne => hkeep d (by omega) Iff.rfl hne⟩
  simp only [physByBase, hb_pos.ne', Nat.not_lt.mpr (Nat.le_add_right b n), ↓reduceIte]

theorem physByBase_winShrinkLeft {N b n : ℕ} {td dt : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hw : WindowInv (maxTailItems N) b (n + 1) td dt)
    (hM : n + 1 ≤ maxTailItems N) :
    match winShrinkLeft (maxTailItems N) b n (td, dt) with
    | (_, dt') =>
      let d_last := denseOfCirc (maxTailItems N) b (td n)
      b ≤ d_last ∧ d_last < b + n + 1 ∧
      (b < d_last → physByBase N (b + 1) dt' d_last = N - 1 - dt (b % maxTailItems N)) ∧
      (∀ d < b + 1 + n, d ≠ b → d ≠ d_last →
        physByBase N (b + 1) dt' d = physByBase N b dt d) := by
  dsimp only [winShrinkLeft]
  obtain ⟨hge, hlt, hlast, hkeep⟩ := physByBase_update_dt_last (b' := b + 1)
    (t_rem := dt (b % maxTailItems N)) hb_pos hw hM
  exact ⟨hge, hlt, fun hgt => hlast (by omega),
    fun d hd hneb hne => hkeep d (by omega) (by omega) hne⟩

/-! ## Section 2: Direct $O(1)$ Bucket-Owner and Logical-Slot Inversion on Dense Indices -/

/-- Recover the owning Feistel bucket `b < numBuckets N` of dense index `d < totalSlots N gm` from
`GlobalMeta` (`gm`) and `DenseToTail` (`dt`). -/
@[expose] def ownerBucketOfDense (N : ℕ) (gm dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then 0
  else if d < gm 0 * slabSize N then gm (gmSlabOwnerBIdx N (d / slabSize N))
  else gm (gmTailOwnerIdx N (dt (d % maxTailItems N))) / tailCapPerBucket N

/-- Recover the logical within-bucket slot index `j < bCount N gm b` of dense index `d`. -/
@[expose] def logicalIdxOfDense (N : ℕ) (gm dt : ℕ → ℕ) (d : ℕ) : ℕ :=
  if bucketBits N = 0 then d
  else if d < gm 0 * slabSize N then
    let p := d / slabSize N
    gm (gmSlabOwnerSIdx N p) * slabSize N + (slabSize N - 1 - d % slabSize N)
  else
    let desc := gm (gmTailOwnerIdx N (dt (d % maxTailItems N)))
    let b := desc / tailCapPerBucket N
    gm (gmQIdx b) * slabSize N + desc % tailCapPerBucket N

theorem denseOfPhys_slab {N : ℕ} (gm td : ℕ → ℕ) {g : ℕ} (hg : g < gm 0 * slabSize N) :
    denseOfPhys N gm td g = g := by
  unfold denseOfPhys; split_ifs <;> rfl

theorem denseOfPhys_tail {N : ℕ} (hb : 0 < bucketBits N) {gm : ℕ → ℕ}
    (hSN : gm 0 * slabSize N + gm 1 ≤ N) (td : ℕ → ℕ) {t : ℕ} (ht : t < gm 1) :
    denseOfPhys N gm td (N - 1 - t) =
      denseOfCirc (maxTailItems N) (gm 0 * slabSize N) (td t) := by
  unfold denseOfPhys
  rw [ite_eq_right hb.ne', ite_eq_right (by omega), Nat.sub_sub_self (by omega)]

theorem physOfDense_denseOfPhys_slab {N : ℕ} (gm td dt : ℕ → ℕ) {g : ℕ}
    (hg : g < gm 0 * slabSize N) :
    physOfDense N gm dt (denseOfPhys N gm td g) = g := by
  rw [denseOfPhys_slab gm td hg]
  unfold physOfDense physByBase; split_ifs <;> rfl

theorem physOfDense_denseOfPhys_tail {N : ℕ} {gm td dt : ℕ → ℕ}
    (htd : TailDenseInv N (gm 0) (gm 1) td dt) (hb : 0 < bucketBits N)
    (hSN : gm 0 * slabSize N + gm 1 ≤ N) {t : ℕ} (ht : t < gm 1) :
    physOfDense N gm dt (denseOfPhys N gm td (N - 1 - t)) = N - 1 - t := by
  rw [denseOfPhys_tail hb hSN td ht]
  have hc_lt : td t < maxTailItems N := htd.td_lt t ht
  have hge := denseOfCirc_ge (maxTailItems N) (gm 0 * slabSize N) (td t)
  unfold physOfDense physByBase
  rw [ite_eq_right hb.ne', ite_eq_right (by omega), denseOfCirc_mod (by omega) hc_lt,
    htd.dt_td t ht]

/-- Active slot count (`= Succinct.totalSlots N gm`). -/
abbrev epochTotalSlots (N : ℕ) (gm : ℕ → ℕ) : ℕ :=
  if bucketBits N = 0 then gm 0 else gm 0 * slabSize N + gm 1

/-- Under `SlotStoreInv N gm` and `TailDenseInv N (gm 0) (gm 1) td dt`, every dense index
`d < epochTotalSlots N gm` maps via `(ownerBucketOfDense, logicalIdxOfDense)` to a valid active
bucket slot `(b, j)` with `denseOfPhys N gm td (slotOf N gm b j) = d`. -/
theorem ownerBucketOfDense_lt_and_slotOf {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {d : ℕ} (hd : d < epochTotalSlots N gm) :
    let b := ownerBucketOfDense N gm dt d
    let j := logicalIdxOfDense N gm dt d
    b < numBuckets N ∧ j < bCount N gm b ∧ denseOfPhys N gm td (slotOf N gm b j) = d := by
  intro b j
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · unfold epochTotalSlots at hd
    simp only [hb0, ↓reduceIte] at hd
    simp [b, j, ownerBucketOfDense, logicalIdxOfDense, numBuckets, bCount, denseOfPhys, slotOf,
      hb0, hd]
  · have htd' := htd hb_pos
    have hb_ne : bucketBits N ≠ 0 := by omega
    unfold epochTotalSlots at hd; rw [ite_eq_right hb_ne] at hd
    have hK : 0 < slabSize N := slabSize_pos N
    have hslab := hslot.multi_slab hb_pos
    have htail := hslot.multi_tail hb_pos
    have hSN := hslot.multi_total_le hb_pos
    by_cases hdS : d < gm 0 * slabSize N
    · have hp_lt : d / slabSize N < gm 0 := (Nat.div_lt_iff_lt_mul hK).mpr hdS
      have hrem_lt : d % slabSize N < slabSize N := Nat.mod_lt d hK
      obtain ⟨hb_lt, hs_lt, hptr_eq⟩ := hslab.owner_valid (d / slabSize N)
        (by rwa [← hslab.nslabs_eq])
      have hb_def : b = gm (gmSlabOwnerBIdx N (d / slabSize N)) := by
        simp [b, ownerBucketOfDense, hb_ne, hdS]
      have hj_def : j = gm (gmSlabOwnerSIdx N (d / slabSize N)) * slabSize N +
          (slabSize N - 1 - d % slabSize N) := by simp [j, logicalIdxOfDense, hb_ne, hdS]
      have hj_slab : j < gm (gmQIdx b) * slabSize N := by
        rw [hj_def, hb_def]
        have hsub : slabSize N - 1 - d % slabSize N < slabSize N := by omega
        simpa [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt hs_lt hsub
      have hj_div : j / slabSize N = gm (gmSlabOwnerSIdx N (d / slabSize N)) := by
        rw [hj_def, Nat.add_comm, Nat.add_mul_div_right _ _ hK,
          Nat.div_eq_of_lt (by omega), Nat.zero_add]
      have hj_mod : j % slabSize N = slabSize N - 1 - d % slabSize N := by
        rw [hj_def, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (by omega)]
      have hslot_eq : slotOf N gm b j = d := by
        unfold slotOf
        rw [ite_eq_right hb_ne, ite_eq_left hj_slab, hj_div, hj_mod, hb_def, hptr_eq,
          Nat.sub_sub_self (by omega), Nat.mul_comm, Nat.div_add_mod]
      exact ⟨hb_def ▸ hb_lt,
        by simp only [bCount, hb_ne, ↓reduceIte, hb_def ▸ hb_lt]; omega,
        by rw [hslot_eq, denseOfPhys_slab gm td hdS]⟩
    · have hd_ge : gm 0 * slabSize N ≤ d := by omega
      obtain ⟨ht_lt, htd_eq⟩ := htd'.owner_valid d hd_ge hd
      set t := dt (d % maxTailItems N)
      set desc := gm (gmTailOwnerIdx N t)
      obtain ⟨hb_lt, hr_lt, hptr_eq⟩ := htail.owner_valid t (by rwa [← htail.ntails_eq])
      have hb_def : b = desc / tailCapPerBucket N := by
        simp [b, ownerBucketOfDense, hb_ne, hdS, t, desc]
      have hr_lt' : desc % tailCapPerBucket N < gm (gmRIdx b) := hb_def ▸ hr_lt
      have hj_def : j = gm (gmQIdx b) * slabSize N + desc % tailCapPerBucket N := by
        simp [j, logicalIdxOfDense, hb_ne, hdS, t, desc, hb_def]
      have hslot_eq : slotOf N gm b j = N - 1 - t := by
        unfold slotOf gmTailPtrIdx
        rw [ite_eq_right hb_ne, ite_eq_right (by omega), hj_def, Nat.add_sub_cancel_left,
          hb_def, Nat.mul_comm, Nat.div_add_mod, hptr_eq]
      have hM_le : gm 1 ≤ maxTailItems N := htail.ntails_eq.trans_le htail.ntails_le
      have hM_pos : 0 < maxTailItems N := by have := htd'.td_lt t ht_lt; omega
      refine ⟨hb_def ▸ hb_lt, by simp only [bCount, hb_ne, ↓reduceIte, hb_def ▸ hb_lt]; omega, ?_⟩
      rw [hslot_eq, denseOfPhys_tail hb_pos hSN td ht_lt, htd_eq]
      exact denseOfCirc_mod_self hM_pos hd_ge (by omega)

private theorem slotOf_slab_lt_or_tail_eq {N : ℕ} {gm : ℕ → ℕ}
    (hb_pos : 0 < bucketBits N) (hslot : SlotStoreInv N gm)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < bCount N gm b) :
    slotOf N gm b j < gm 0 * slabSize N ∨
      ∃ t < gm 1, slotOf N gm b j = N - 1 - t := by
  have hb_ne : bucketBits N ≠ 0 := hb_pos.ne'
  have hK : 0 < slabSize N := slabSize_pos N
  simp only [bCount, hb_ne, ↓reduceIte, hb] at hj
  by_cases hj_slab : j < gm (gmQIdx b) * slabSize N
  · left
    have hp_lt : slabPtrOf N gm b (j / slabSize N) < gm 0 :=
      (hslot.multi_slab hb_pos).nslabs_eq ▸
        (hslot.multi_slab hb_pos).ptr_lt b hb _ ((Nat.div_lt_iff_lt_mul hK).mpr hj_slab)
    have hsub_lt : slabSize N - 1 - j % slabSize N < slabSize N := by omega
    unfold slotOf; rw [ite_eq_right hb_ne, ite_eq_left hj_slab]
    simpa [Nat.mul_comm] using Nat.mul_add_lt_mul_of_lt_of_lt hp_lt hsub_lt
  · right
    refine ⟨_, (hslot.multi_tail hb_pos).ntails_eq ▸
      (hslot.multi_tail hb_pos).ptr_lt b hb (j - gm (gmQIdx b) * slabSize N) (by omega), ?_⟩
    simp only [slotOf, hb_ne, hj_slab, ↓reduceIte]

theorem physOfDense_denseOfPhys_slotOf {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < bCount N gm b) :
    physOfDense N gm dt (denseOfPhys N gm td (slotOf N gm b j)) = slotOf N gm b j := by
  rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
  · simp [physOfDense, physByBase, denseOfPhys, hb0]
  · rcases slotOf_slab_lt_or_tail_eq hb_pos hslot hb hj with hlt | ⟨t, ht, heq⟩
    · exact physOfDense_denseOfPhys_slab gm td dt hlt
    · exact heq ▸ physOfDense_denseOfPhys_tail (htd hb_pos) hb_pos (hslot.multi_total_le hb_pos) ht

theorem denseOfPhys_slotOf_lt_and_inv {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {b j : ℕ} (hb : b < numBuckets N) (hj : j < bCount N gm b) :
    let d := denseOfPhys N gm td (slotOf N gm b j)
    d < epochTotalSlots N gm ∧ ownerBucketOfDense N gm dt d = b ∧
      logicalIdxOfDense N gm dt d = j := by
  intro d
  have hd_lt : d < epochTotalSlots N gm := by
    rcases Nat.eq_zero_or_pos (bucketBits N) with hb0 | hb_pos
    · obtain rfl : b = 0 := Nat.lt_one_iff.mp (by simpa [numBuckets, hb0] using hb)
      simpa [d, denseOfPhys, slotOf, epochTotalSlots, bCount, hb0] using hj
    · unfold epochTotalSlots; rw [ite_eq_right hb_pos.ne']
      rcases slotOf_slab_lt_or_tail_eq hb_pos hslot hb hj with hlt | ⟨t, ht, heq⟩
      · exact (denseOfPhys_slab gm td hlt).trans_lt (by omega)
      · simpa only [d, heq, denseOfPhys_tail hb_pos (hslot.multi_total_le hb_pos) td ht] using
          (htd hb_pos).dense_lt t ht
  obtain ⟨hb'_lt, hj'_lt, hd_round⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd_lt
  have hvirt_eq := congrArg (physOfDense N gm dt) hd_round
  rw [physOfDense_denseOfPhys_slotOf hslot htd hb'_lt hj'_lt,
    physOfDense_denseOfPhys_slotOf hslot htd hb hj] at hvirt_eq
  exact ⟨hd_lt, (slotOf_lt_and_injective hslot).2 _ hb'_lt _ hj'_lt b hb j hj hvirt_eq⟩

theorem physOfDense_eq_slotOf_owner {N : ℕ} {gm td dt : ℕ → ℕ}
    (hslot : SlotStoreInv N gm) (htd : 0 < bucketBits N → TailDenseInv N (gm 0) (gm 1) td dt)
    {d : ℕ} (hd : d < epochTotalSlots N gm) :
    physOfDense N gm dt d =
      slotOf N gm (ownerBucketOfDense N gm dt d) (logicalIdxOfDense N gm dt d) := by
  obtain ⟨hb_lt, hj_lt, hd_eq⟩ := ownerBucketOfDense_lt_and_slotOf hslot htd hd
  conv_lhs => rw [← hd_eq]
  exact physOfDense_denseOfPhys_slotOf hslot htd hb_lt hj_lt

/-! ## Section 3: Fixed-Capacity Array Coupling Invariants (`WindowCoupled`, `FixedCoupled`) -/

/-- Ghost word width `w + 16` used for the mathematical fixed-capacity reference state `s_fix`,
ensuring `Fits (ghostW w) (Succinct.space U V (ghostW w) N)` for all `N ≤ U ≤ 2 ^ w`. -/
@[expose] def ghostW (w : ℕ) : ℕ := w + 16

/-- Coupling invariant between a fixed-capacity state `s_fix` (at `base = 0`, `ghostW w`)
and a compacted state `s` at `(metaBase, itemBase)` over window `[b_win, b_win + n_win)`. -/
structure WindowCoupled (metaBase itemBase U V w N b_win n_win m_items : ℕ)
    (s_fix s : Memory.State) : Prop where
  gm_eq : compGmAt metaBase U w N s.mem =
    gmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  lm_eq : compLmAt metaBase U w N s.mem =
    lmAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
  win_inv : WindowInv (maxTailItems N) b_win n_win
    (compTDAt metaBase U w N s.mem) (compDTAt metaBase U w N s.mem)
  td_lt : ∀ i, compTDAt metaBase U w N s.mem i < max (maxTailItems N) 1
  dt_lt : ∀ i, compDTAt metaBase U w N s.mem i < max (maxTailItems N) 1
  quot_eq : ∀ d < m_items, compQuotAt itemBase U V w N m_items s.mem d =
    quotAt 0 U (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physByBase N b_win (compDTAt metaBase U w N s.mem) d)
  val_eq : ∀ d < m_items, compValAt itemBase U V w N m_items s.mem d =
    valAt 0 U V (ghostW w) N (epochHashSpace U (ghostW w) N) s_fix.mem
      (physByBase N b_win (compDTAt metaBase U w N s.mem) d)

/-- Resting window coupling (`b_win = gm 0 * slabSize N`, and `n_win = gm 1` when
`0 < bucketBits N`). -/
@[expose] def FixedCoupled (metaBase itemBase U V w N : ℕ) (s_fix s : Memory.State) : Prop :=
  let gm := compGmAt metaBase U w N s.mem
  WindowCoupled metaBase itemBase U V w N (gm 0 * slabSize N)
    (if bucketBits N = 0 then 0 else gm 1) (epochTotalSlots N gm) s_fix s

end Cslib.DataStructure.Dictionary.WordRAM.ResizableSuccinct
