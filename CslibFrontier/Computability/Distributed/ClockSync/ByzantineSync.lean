/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ApproxAgreement.TrimmedMidpoint
public import CslibFrontier.Computability.Distributed.ClockSync.Basic
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Lockstep drift-free Byzantine trimmed-midpoint resynchronization step

This module proves a **separated lockstep-round, drift-free** (`hardwareClock c p t = t + c p`,
zero clock drift) **step** after [Welch and Lynch][WelchLynch1988], and is **not** the cited
paper's asynchronous local-timer-triggered periodic resynchronization result under nonzero bounded
hardware clock drift (which remains open in
[#7202](https://github.com/cslib-community/cslib-frontier/issues/7202)).

When up to `t` processes with `3 * t < Fintype.card P` suffer Byzantine clock faults—reporting
arbitrary, recipient-dependent timestamps to different honest processes—averaging all offset
estimates (`lockstepClockAvg`) can be skewed arbitrarily by a single faulty clock. Reusing the
kernel-reducible trimmed-extremes midpoint operator
`Cslib.Distributed.ApproxAgreement.multisetMidTrim` from
`CslibFrontier.Computability.Distributed.ApproxAgreement.TrimmedMidpoint`, each process forms its
`n = Fintype.card P` midpoint-delay offset estimates (`estDiff`), discards the `t` smallest and `t`
largest values, and adjusts its clock by the midpoint of the surviving extremes
(`lockstepByzantineClockStep`).

By clamping honest offset estimates within `± (d_max - d_min) / 2` onto the common honest offset
vector `c` and applying translation equivariance and pointwise monotonicity of `multisetMidTrim`,
this module reduces lockstep drift-free Byzantine clock resynchronization directly to
`ApproxAgreement.multisetMidTrim_map_mem_Icc` and `ApproxAgreement.abs_multisetMidTrim_map_sub_le`:

* **Honest-interval step (`lockstepDriftFreeByzantineOffset_mem_Icc`):** In one lockstep drift-free
  resynchronization round (`2 * t < Fintype.card P`, `F.card ≤ t`), if all honest initial offsets
  lie in `[lo, hi]` and honest message delays lie in `[d_min, d_max]`, every honest process's
  updated offset lies in `[lo - (d_max - d_min) / 2, hi + (d_max - d_min) / 2]`.
* **Per-round skew-halving step (`lockstepDriftFreeByzantineOffset_abs_sub_le`):** In one lockstep
  drift-free resynchronization round (`3 * t < Fintype.card P`, `F.card ≤ t`), if honest initial
  offsets have skew at most `δ₀` (`∀ p ∉ F, ∀ q ∉ F, |c p - c q| ≤ δ₀`) and honest message delays
  lie in `[d_min, d_max]`, every pair of honest processes satisfies
  `|offset p - offset q| ≤ δ₀ / 2 + (d_max - d_min)`.
* **Iterated `R`-round lockstep step (`lockstepDriftFreeByzantineOffsetIter_abs_sub_le`):**
  Iterating `R` separated lockstep drift-free resynchronization rounds against round-dependent
  equivocating Byzantine adversaries contracts initial honest skew `δ₀` to
  `δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min)`.

## Main definitions

* `Cslib.Distributed.ClockSync.lockstepByzantineClockStep`: 1-round local Byzantine-resilient clock
  adjustment computed from observed arrival timestamps via `ApproxAgreement.multisetMidTrim`.
* `Cslib.Distributed.ClockSync.lockstepByzantineArrival`,
  `lockstepDriftFreeByzantineOffset`, `lockstepDriftFreeByzantineOffsetIter`: 1-round and `R`-round
  lockstep drift-free synchronized clock offsets under equivocating Byzantine faults `F`.

## Main results

* `Cslib.Distributed.ClockSync.lockstepDriftFreeByzantineOffset_mem_Icc`: lockstep drift-free
  honest interval preservation up to `(d_max - d_min) / 2` (`#7202`).
* `Cslib.Distributed.ClockSync.lockstepDriftFreeByzantineOffset_abs_sub_le`: 1-round lockstep
  drift-free skew contraction to `δ₀ / 2 + (d_max - d_min)` when `3 * t < Fintype.card P` and
  `F.card ≤ t` (`#7202`).
* `Cslib.Distributed.ClockSync.lockstepDriftFreeByzantineOffsetIter_abs_sub_le`: `R`-round lockstep
  drift-free geometric contraction `δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min)` (`#7202`).

## References

* [D. Dolev, N. A. Lynch, S. S. Pinter, E. W. Stark, W. E. Weihl, *Reaching approximate agreement
  in the presence of faults*][DolevLynchPinterStarkWeihl1986]
* [J. L. Welch, N. Lynch,
  *A new fault-tolerant algorithm for clock synchronization*][WelchLynch1988]
-/

public section

namespace Cslib.Distributed.ClockSync

open Cslib.Distributed.ApproxAgreement

universe u v

/-! ### Translation equivariance and pointwise monotonicity of `multisetMidTrim` -/

section MidTrimOrder

variable {K : Type v}

private theorem sortLE_map_add [AddCommGroup K] [LinearOrder K] [IsOrderedAddMonoid K]
    (a : K) (xs : List K) :
    sortLE (xs.map (a + ·)) = (sortLE xs).map (a + ·) := by
  rw [sortLE_eq_mergeSort, sortLE_eq_mergeSort]
  have hpair : ((xs.mergeSort (· ≤ ·)).map (a + ·)).SortedLE :=
    ((List.sortedLE_mergeSort (l := xs)).pairwise.map (a + ·)
      (fun _ _ h => add_le_add_right h a)).sortedLE
  have hperm : ((xs.map (a + ·)).mergeSort (· ≤ ·)).Perm ((xs.mergeSort (· ≤ ·)).map (a + ·)) :=
    (List.mergeSort_perm _ _).trans ((List.mergeSort_perm xs _).symm.map (a + ·))
  exact hperm.eq_of_sortedLE List.sortedLE_mergeSort hpair

private theorem add_midTrim [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : K) (t : ℕ) {xs : List K} (h2t : 2 * t < xs.length) :
    a + midTrim t xs = midTrim t (xs.map (a + ·)) := by
  have h2t_map : 2 * t < (xs.map (a + ·)).length := by rwa [List.length_map]
  rw [midTrim_eq_endpoints h2t, midTrim_eq_endpoints h2t_map]
  simp only [sortLE_map_add, List.length_map, List.getElem_map]
  ring

private theorem add_multisetMidTrim [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    (a : K) (t : ℕ) {s : Multiset K} (h2t : 2 * t < s.card) :
    a + multisetMidTrim t s = multisetMidTrim t (s.map (a + ·)) :=
  Quot.inductionOn s (fun _ h2t => add_midTrim a t h2t) h2t

private theorem sortLE_getElem_map_mono {α : Type*} [LinearOrder K] {xs : List α} {f g : α → K}
    (hfg : ∀ x ∈ xs, f x ≤ g x) {k : ℕ} (hk : k < xs.length) :
    (sortLE (xs.map f))[k]'(by rw [length_sortLE, List.length_map]; exact hk) ≤
      (sortLE (xs.map g))[k]'(by rw [length_sortLE, List.length_map]; exact hk) := by
  set sf := sortLE (xs.map f)
  set sg := sortLE (xs.map g)
  have hsg_len : sg.length = xs.length := by simp only [sg, length_sortLE, List.length_map]
  have hsf_sort : sf.SortedLE :=
    (congrArg List.SortedLE (sortLE_eq_mergeSort _)).mpr List.sortedLE_mergeSort
  have hsg_sort : sg.SortedLE :=
    (congrArg List.SortedLE (sortLE_eq_mergeSort _)).mpr List.sortedLE_mergeSort
  have hsf_perm : sf.Perm (xs.map f) :=
    (List.Perm.of_eq (sortLE_eq_mergeSort (xs.map f))).trans (List.mergeSort_perm _ _)
  have hsg_perm : sg.Perm (xs.map g) :=
    (List.Perm.of_eq (sortLE_eq_mergeSort (xs.map g))).trans (List.mergeSort_perm _ _)
  set B := sg[k]'(by omega)
  have hcnt_g : k + 1 ≤ (xs.map g).countP (· ≤ B) := by
    rw [← hsg_perm.countP_eq]
    refine le_of_eq_of_le ?_ (List.take_sublist (k + 1) sg).countP_le
    rw [List.countP_eq_length.mpr, List.length_take_of_le (by omega)]
    intro y hy
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hy
    rw [List.getElem_take, decide_eq_true_eq]
    rw [List.length_take] at hi
    exact hsg_sort.getElem_le_getElem_of_le (by omega)
  have hcnt_f : k + 1 ≤ sf.countP (· ≤ B) := by
    simp only [hsf_perm.countP_eq, List.countP_map] at hcnt_g ⊢
    exact hcnt_g.trans (List.countP_mono_left fun x hx hgx =>
      decide_eq_true ((hfg x hx).trans (of_decide_eq_true hgx)))
  by_contra! hlt
  have hdrop : (sf.drop k).countP (· ≤ B) = 0 := List.countP_eq_zero.mpr fun y hy => by
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
    rw [List.length_drop] at hj
    rw [List.getElem_drop, decide_eq_true_eq, not_le]
    exact hlt.trans_le (hsf_sort.getElem_le_getElem_of_le (Nat.le_add_right k j))
  have htake : (sf.take k).countP (· ≤ B) ≤ k :=
    List.countP_le_length.trans (List.length_take_le k sf)
  rw [← List.take_append_drop k sf, List.countP_append] at hcnt_f
  omega

private theorem multisetMidTrim_map_mono {α : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (t : ℕ) {s : Multiset α} {f g : α → K}
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    multisetMidTrim t (s.map f) ≤ multisetMidTrim t (s.map g) := by
  refine Quot.inductionOn s (fun xs hfg => ?_) hfg
  change midTrim t (xs.map f) ≤ midTrim t (xs.map g)
  by_cases h2t : 2 * t < xs.length
  · rw [midTrim_eq_endpoints (by rwa [List.length_map]),
      midTrim_eq_endpoints (by rwa [List.length_map])]
    have h1 := sortLE_getElem_map_mono (fun x hx => hfg x (Multiset.mem_coe.mpr hx))
      (k := t) (by omega)
    have h2 := sortLE_getElem_map_mono (fun x hx => hfg x (Multiset.mem_coe.mpr hx))
      (k := xs.length - 1 - t) (by omega)
    simp only [List.length_map]
    linarith
  · have hnil (h : α → K) : trimmed t (xs.map h) = [] := by
      rw [← List.length_eq_zero_iff, length_trimmed, List.length_map]
      omega
    simp only [midTrim, hnil, le_rfl]

end MidTrimOrder

/-! ### 1-round and `R`-round lockstep drift-free Byzantine clock resynchronization -/

section ByzantineProtocol

variable {P : Type u} [Fintype P] [DecidableEq P]
variable {K : Type v} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- 1-round lockstep Byzantine-resilient trimmed-midpoint clock adjustment step (a separated
lockstep-round, drift-free step after [Welch and Lynch][WelchLynch1988], `#7202`): process `p`
forms `estDiff d_min d_max p recv j` from its observed arrival readings `recv : P → K` across all
senders `j : P`, discards the `t` smallest and `t` largest estimates via
`ApproxAgreement.multisetMidTrim`, and outputs the midpoint of the surviving range. -/
@[expose] def lockstepByzantineClockStep (t : ℕ) (d_min d_max : K) (p : P) (recv : P → K) : K :=
  multisetMidTrim t (Finset.univ.val.map (estDiff d_min d_max p recv))

/-- Arrival reading observed at `p` from sender `j` in a 1-round lockstep synchronization broadcast
on drift-free clocks with faulty processes `F` and equivocating adversary `adv`: a faulty clock
`j ∈ F` induces an arbitrary recipient-dependent timestamp `adv j p`, whereas an honest clock
`j ∉ F` sends at local reading `0` and arrives at `arrivalReading c (fun _ => δ) 0 j p 0`. -/
@[expose] def lockstepByzantineArrival {P : Type u} [DecidableEq P] {K : Type v} [AddCommGroup K]
    (F : Finset P) (adv : P → P → K) (c : P → K) (δ : P → P → K) (j p : P) : K :=
  if j ∈ F then adv j p else arrivalReading c (fun _ => δ) 0 j p 0

/-- Process `p`'s updated synchronized clock offset after one separated lockstep round of
`lockstepByzantineClockStep` on drift-free clocks under faulty set `F`, equivocating adversary
`adv`, initial offsets `c`, and transit delays `δ` (`#7202`). -/
@[expose] def lockstepDriftFreeByzantineOffset (t : ℕ) (d_min d_max : K) (F : Finset P)
    (adv : P → P → K) (c : P → K) (δ : P → P → K) (p : P) : K :=
  c p + lockstepByzantineClockStep t d_min d_max p (fun j => lockstepByzantineArrival F adv c δ j p)

/-- Updated clock offsets after `R` separated lockstep drift-free resynchronization rounds against
round-indexed equivocating adversaries `adv : ℕ → P → P → K` and round transit delays
`δ : ℕ → P → P → K` (`#7202`). -/
@[expose] def lockstepDriftFreeByzantineOffsetIter (t : ℕ) (d_min d_max : K) (F : Finset P)
    (adv : ℕ → P → P → K) (c : P → K) (δ : ℕ → P → P → K) : ℕ → P → K
  | 0 => c
  | r + 1 =>
    lockstepDriftFreeByzantineOffset t d_min d_max F (adv r)
      (lockstepDriftFreeByzantineOffsetIter t d_min d_max F adv c δ r) (δ r)

private theorem offset_eq_multisetMidTrim {t : ℕ} (ht : 2 * t < Fintype.card P)
    (d_min d_max : K) (F : Finset P) (adv : P → P → K) (c : P → K) (δ : P → P → K) (p : P) :
    lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ p =
      multisetMidTrim t
        (Finset.univ.val.map fun j =>
          c p + estDiff d_min d_max p (fun k => lockstepByzantineArrival F adv c δ k p) j) := by
  dsimp only [lockstepDriftFreeByzantineOffset, lockstepByzantineClockStep]
  rw [add_multisetMidTrim (c p) t (by rw [Multiset.card_map, Finset.card_val]; exact ht),
    Multiset.map_map]
  rfl

/-- A separated lockstep-round, drift-free step after [Welch and Lynch][WelchLynch1988], and not
the cited asynchronous nonzero-drift resynchronization theorem (`#7202`): when
`2 * t < Fintype.card P`, `F.card ≤ t`, every honest process's initial offset lies in `[lo, hi]`,
and honest-to-honest transit delays lie in `[d_min, d_max]`, every honest process's updated offset
lies in `[lo - (d_max - d_min) / 2, hi + (d_max - d_min) / 2]`. -/
theorem lockstepDriftFreeByzantineOffset_mem_Icc {t : ℕ} (ht : 2 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {d_min d_max lo hi : K}
    (adv : P → P → K) (c : P → K) (δ : P → P → K)
    (hc : ∀ j ∉ F, lo ≤ c j ∧ c j ≤ hi)
    (hδ : ∀ j ∉ F, ∀ p ∉ F, d_min ≤ δ j p ∧ δ j p ≤ d_max)
    {p : P} (hp : p ∉ F) :
    lo - (d_max - d_min) / 2 ≤ lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ p ∧
      lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ p ≤ hi + (d_max - d_min) / 2 := by
  have hd : d_min ≤ d_max := (hδ p hp p hp).1.trans (hδ p hp p hp).2
  rw [offset_eq_multisetMidTrim ht]
  exact multisetMidTrim_map_mem_Icc hF (S := Finset.univ) (by rwa [Finset.card_univ])
    fun j _ hj => by
      have herr := abs_add_estDiff_sub_le hd c p j (fun k => lockstepByzantineArrival F adv c δ k p)
        (d := δ j p)
        (fun _ => by simp only [lockstepByzantineArrival, hj, ↓reduceIte, arrivalReading, zero_add])
        (fun _ => (hδ j hj p hp).1) (fun _ => (hδ j hj p hp).2)
      rw [abs_le] at herr
      have hcj := hc j hj
      exact ⟨by linarith, by linarith⟩

/-- A separated lockstep-round, drift-free step after [Welch and Lynch][WelchLynch1988], and not
the cited asynchronous nonzero-drift resynchronization theorem (`#7202`): when
`3 * t < Fintype.card P`, `F.card ≤ t`, initial honest offsets have skew at most `δ₀`, and honest
message delays lie in `[d_min, d_max]`, one lockstep round of `lockstepByzantineClockStep` on
drift-free clocks contracts the skew between any two honest processes `p, q ∉ F` to at most
`δ₀ / 2 + (d_max - d_min)`. -/
theorem lockstepDriftFreeByzantineOffset_abs_sub_le {t : ℕ} (ht : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {d_min d_max δ₀ : K}
    (adv : P → P → K) (c : P → K) (δ : P → P → K)
    (hc : ∀ p ∉ F, ∀ q ∉ F, |c p - c q| ≤ δ₀)
    (hδ : ∀ j ∉ F, ∀ p ∉ F, d_min ≤ δ j p ∧ δ j p ≤ d_max)
    {p q : P} (hp : p ∉ F) (hq : q ∉ F) :
    |lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ p -
        lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ q| ≤
      δ₀ / 2 + (d_max - d_min) := by
  have hd : d_min ≤ d_max := (hδ p hp p hp).1.trans (hδ p hp p hp).2
  set u : K := d_max - d_min
  set e : K := u / 2
  let H : Finset P := Finset.univ \ F
  have hH_ne : H.Nonempty := ⟨p, Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hp⟩⟩
  let lo : K := H.inf' hH_ne c
  let hi : K := H.sup' hH_ne c
  have hhi_lo : hi - lo ≤ δ₀ := by
    obtain ⟨j_hi, hj_hi, hhi_eq⟩ := Finset.exists_mem_eq_sup' hH_ne c
    obtain ⟨j_lo, hj_lo, hlo_eq⟩ := Finset.exists_mem_eq_inf' hH_ne c
    rw [Finset.mem_sdiff] at hj_hi hj_lo
    linarith [le_abs_self (c j_hi - c j_lo), hc j_hi hj_hi.2 j_lo hj_lo.2]
  have hc_Icc : ∀ j ∉ F, c j ∈ Set.Icc lo hi := fun j hj => by
    have hjH : j ∈ H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ j, hj⟩
    exact ⟨Finset.inf'_le c hjH, Finset.le_sup' c hjH⟩
  suffices hdir : ∀ {a b : P}, a ∉ F → b ∉ F →
      lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ a -
        lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ b ≤ δ₀ / 2 + u by
    exact abs_le.mpr ⟨by linarith [hdir hq hp], hdir hp hq⟩
  intro a b ha hb
  let xa : P → K :=
    fun j => c a + estDiff d_min d_max a (fun k => lockstepByzantineArrival F adv c δ k a) j
  let xb : P → K :=
    fun j => c b + estDiff d_min d_max b (fun k => lockstepByzantineArrival F adv c δ k b) j
  let ya : P → K := fun j => if j ∈ F then xa j - e else c j
  let zb : P → K := fun j => if j ∈ F then xb j + e else c j
  have herr_honest : ∀ {w : P}, w ∉ F → ∀ {j : P}, j ∉ F →
      |(c w + estDiff d_min d_max w (fun k => lockstepByzantineArrival F adv c δ k w) j) - c j| ≤
        e := fun {w} hw {j} hj =>
    abs_add_estDiff_sub_le hd c w j
      (fun k => lockstepByzantineArrival F adv c δ k w) (d := δ j w)
      (fun _ => by simp only [lockstepByzantineArrival, hj, ↓reduceIte, arrivalReading, zero_add])
      (fun _ => (hδ j hj w hw).1) (fun _ => (hδ j hj w hw).2)
  have hxa_le : ∀ j ∈ Finset.univ.val, xa j ≤ e + ya j := fun j _ => by
    dsimp only [ya, xa]
    split_ifs with hj
    · linarith
    · linarith [(abs_le.mp (herr_honest ha hj)).2]
  have hzb_le : ∀ j ∈ Finset.univ.val, -e + zb j ≤ xb j := fun j _ => by
    dsimp only [zb, xb]
    split_ifs with hj
    · linarith
    · linarith [(abs_le.mp (herr_honest hb hj)).1]
  have h2t : 2 * t < Fintype.card P := by omega
  have hma : lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ a ≤
      e + multisetMidTrim t (Finset.univ.val.map ya) := by
    rw [offset_eq_multisetMidTrim h2t,
      add_multisetMidTrim e t (by rw [Multiset.card_map, Finset.card_val]; exact h2t),
      Multiset.map_map]
    exact multisetMidTrim_map_mono t hxa_le
  have hmb : -e + multisetMidTrim t (Finset.univ.val.map zb) ≤
      lockstepDriftFreeByzantineOffset t d_min d_max F adv c δ b := by
    rw [offset_eq_multisetMidTrim h2t,
      add_multisetMidTrim (-e) t (by rw [Multiset.card_map, Finset.card_val]; exact h2t),
      Multiset.map_map]
    exact multisetMidTrim_map_mono t hzb_le
  have hcore := abs_multisetMidTrim_map_sub_le hF (S₁ := Finset.univ) (S₂ := Finset.univ)
    (by simp only [Finset.card_univ]; omega) hc_Icc (f₁ := ya) (f₂ := zb)
    (fun j _ hj => ite_eq_right hj) (fun j _ hj => ite_eq_right hj)
  have he : 2 * e = u := by dsimp only [e]; ring
  linarith [(le_abs_self _).trans hcore]

/-- A separated lockstep-round, drift-free `R`-round step after [Welch and Lynch][WelchLynch1988],
and not the cited asynchronous nonzero-drift resynchronization theorem (`#7202`): iterating `R`
separated lockstep rounds of `lockstepByzantineClockStep` on drift-free clocks with
`3 * t < Fintype.card P` and `F.card ≤ t` contracts initial honest skew `δ₀` geometrically to
`δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min)`. -/
theorem lockstepDriftFreeByzantineOffsetIter_abs_sub_le {t : ℕ} (ht : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {d_min d_max δ₀ : K}
    (adv : ℕ → P → P → K) (c : P → K) (δ : ℕ → P → P → K)
    (hc : ∀ p ∉ F, ∀ q ∉ F, |c p - c q| ≤ δ₀)
    (hδ : ∀ r, ∀ j ∉ F, ∀ p ∉ F, d_min ≤ δ r j p ∧ δ r j p ≤ d_max) (R : ℕ) :
    ∀ {p q : P}, p ∉ F → q ∉ F →
      |lockstepDriftFreeByzantineOffsetIter t d_min d_max F adv c δ R p -
          lockstepDriftFreeByzantineOffsetIter t d_min d_max F adv c δ R q| ≤
        δ₀ / 2 ^ R + 2 * (1 - 1 / 2 ^ R) * (d_max - d_min) := by
  induction R with
  | zero => exact fun hp hq => by simpa [lockstepDriftFreeByzantineOffsetIter] using hc _ hp _ hq
  | succ r ih =>
    intro p q hp hq
    refine (lockstepDriftFreeByzantineOffset_abs_sub_le ht hF (adv r) _ (δ r)
      (fun a ha b hb => ih ha hb) (hδ r) hp hq).trans_eq ?_
    rw [pow_succ]
    ring

end ByzantineProtocol

end Cslib.Distributed.ClockSync
