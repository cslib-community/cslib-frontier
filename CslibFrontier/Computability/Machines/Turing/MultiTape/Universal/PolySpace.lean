/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.SpaceBudget
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Foundations.Data.BitString.ShortWords
import Mathlib.Data.List.GetD

/-!
# Polynomial-space simulation and configuration-count clocks

This module provides general configuration-count clock theorems and polynomial-space simulation
certificates for `Turing.MultiTapeTM.Universal`:

* **Configuration-count clocks (`exists_simSpace_le_and_universal_eq_true_iff`,
  `exists_budgetedUniversal_eq_true_iff`):** Any simulation of `d` on `x` that stays within `s`
  visited work-tape cells (or within a `b`-bit encoded configuration budget) and halts at some step
  `t` already halts with the same output at some step `t₀ ≤ 2 ^ (b + 1)` where
  `cfgSpaceBound (descLen d) x.length d.tapes s ≤ b`. Before the first halting step `t₀`, every
  step visits a distinct configuration in `Cslib.BitString.shortWords b`.
* **Visited-cell-budgeted universal simulation (`spaceBoundedUniversal`,
  `computableInPolySpace_spaceBoundedUniversal`):** While `budgetedUniversal` bounds the bit-length
  of encoded configurations, `spaceBoundedUniversal (d, x, t, s)` tracks the per-tape head
  excursions of `run d x` and enforces the exact visited work-tape cell bound `simSpace d x t ≤ s`.
  Both `budgetedUniversal` and `spaceBoundedUniversal` are computable in polynomial space with
  respect to `eInS` and `eOut`.

## Main definitions

* `Turing.MultiTapeTM.Universal.initBounds`, `Turing.MultiTapeTM.Universal.updateBounds`,
  `Turing.MultiTapeTM.Universal.boundsSpace`, `Turing.MultiTapeTM.Universal.boundsAt`: per-tape
  left/right head excursion bounds for `run d x` and their total visited cell count.
* `Turing.MultiTapeTM.Universal.SpaceLoopState`, `Turing.MultiTapeTM.Universal.spaceLoopInit`,
  `Turing.MultiTapeTM.Universal.spaceLoopStep`: the loop state and transition for visited-space
  bounded simulation.
* `Turing.MultiTapeTM.Universal.spaceBoundedUniversal`: universal simulation enforcing the exact
  visited work-tape cell budget `simSpace d x t ≤ s`.

## Main results

* `Turing.MultiTapeTM.Universal.boundsSpace_boundsAt`: `boundsSpace (boundsAt d x j) =
  simSpace d x j`.
* `Turing.MultiTapeTM.Universal.exists_simSpace_le_and_universal_eq_true_iff`: a simulation halts
  within `s` visited work-tape cells with a given output at some step if and only if it has halted
  within `s` visited cells with that output by step `2 ^ (b + 1)`.
* `Turing.MultiTapeTM.Universal.exists_budgetedUniversal_eq_true_iff`: clocked equivalence for
  `budgetedUniversal`.
* `Turing.MultiTapeTM.Universal.spaceBoundedUniversal_eq_singleton_true_iff`:
  `spaceBoundedUniversal (d, x, t, s) = ([n], true) ↔
    simSpace d x t ≤ s ∧ universal (d, x, t) = ([n], true)`.
* `Turing.MultiTapeTM.Universal.computableInPolySpace_budgetedUniversal`,
  `Turing.MultiTapeTM.Universal.computableInPolySpace_spaceBoundedUniversal`: polynomial-space
  certificates for `budgetedUniversal` and `spaceBoundedUniversal`.
-/

public section

namespace Turing.MultiTapeTM.Universal

open Cslib.BitString

variable (d : Desc) (x : List ℕ) (b : ℕ)

/-! ### Halting and space stabilization for `run`, `universal`, and `simSpace` -/

/-- Iterating `fun c => (step d x c).1` from `run d x j` advances `run d x` by `m` steps. -/
theorem step_fst_iterate_run (j m : ℕ) :
    (fun c => (step d x c).1)^[m] (run d x j) = run d x (j + m) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, ← Nat.add_assoc, ← run_succ]

/-- A halted simulated configuration is a fixed point of `step`, emitting no output. -/
theorem step_of_state_eq_none {c : SCfg} (h : c.state = none) :
    step d x c = (c, none) := by
  simp [step, h]

/-- Once `run d x t` has halted, `stepOut d x` is a fixed point at all later steps `T ≥ t`. -/
theorem stepOut_iterate_eq_of_state_eq_none {t T : ℕ}
    (hhalt : (run d x t).state = none) (hT : t ≤ T) :
    (stepOut d x)^[T] (init d, []) = (stepOut d x)^[t] (init d, []) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  clear hT
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih]
    have hcfg : ((stepOut d x)^[t] (init d, [])).1 = run d x t := rfl
    simp only [stepOut, hcfg, step_of_state_eq_none d x hhalt, Option.toList_none, List.append_nil]
    exact Prod.mk.eta

/-- Once `run d x t` has halted, `run d x T = run d x t` for all `T ≥ t`. -/
theorem run_eq_of_state_eq_none {t T : ℕ}
    (hhalt : (run d x t).state = none) (hT : t ≤ T) :
    run d x T = run d x t :=
  congrArg Prod.fst (stepOut_iterate_eq_of_state_eq_none d x hhalt hT)

/-- Once `universal (d, x, t)` reports halting, increasing the step count `t ≤ T` leaves its result
unchanged. -/
theorem universal_eq_of_snd {t T : ℕ}
    (hhalt : (universal (d, x, t)).2 = true) (hT : t ≤ T) :
    universal (d, x, T) = universal (d, x, t) := by
  have hstate : (run d x t).state = none := Option.isNone_iff_eq_none.mp hhalt
  simp only [universal, simulate, stepOut_iterate_eq_of_state_eq_none d x hstate hT]

/-- Once `run d x t` has halted, the visited positions of each tape stabilize for all `T ≥ t`. -/
theorem visited_eq_of_state_eq_none {t T : ℕ}
    (hhalt : (run d x t).state = none) (hT : t ≤ T) (i : ℕ) :
    visited d x T i = visited d x t i := by
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    rcases le_or_gt j t with hjt | hjt
    · exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), rfl⟩
    · rw [headAt, run_eq_of_state_eq_none d x hhalt hjt.le, ← headAt]
      exact headAt_mem d x t i
  · exact visited_mono d x hT i

/-- Once `run d x t` has halted, `simSpace d x T = simSpace d x t` for all `T ≥ t`. -/
theorem simSpace_eq_of_state_eq_none {t T : ℕ}
    (hhalt : (run d x t).state = none) (hT : t ≤ T) :
    simSpace d x T = simSpace d x t := by
  simp only [simSpace, visited_eq_of_state_eq_none d x hhalt hT]

private lemma le_two_pow_of_first_halt {t₀ : ℕ}
    (ht₀ : (run d x t₀).state.isNone = true)
    (hmin : ∀ m < t₀, (run d x m).state.isNone = true → False)
    (hcfg_le : ∀ k < t₀, (eCfg (run d x (k + 1))).length ≤ b) :
    t₀ ≤ 2 ^ (b + 1) := by
  have hlt_false : ∀ {i j}, i < j → j < t₀ → run d x (i + 1) = run d x (j + 1) → False := by
    intro i j hlt hj hcfg
    have hshift : run d x (i + 1 + (t₀ - (j + 1))) = run d x t₀ := by
      rw [← step_fst_iterate_run d x (i + 1), hcfg, step_fst_iterate_run d x (j + 1),
        Nat.add_sub_of_le (by omega)]
    exact hmin _ (by omega) (hshift ▸ ht₀)
  have hinj : Set.InjOn (fun k => eCfg (run d x (k + 1))) ↑(Finset.range t₀) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with hlt | rfl | hgt
    · exact False.elim (hlt_false hlt hj (eCfg.injective hij))
    · rfl
    · exact False.elim (hlt_false hgt hi (eCfg.injective hij.symm))
  have hsub : (Finset.range t₀).image (fun k => eCfg (run d x (k + 1))) ⊆ shortWords b := by
    intro w hw
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
    exact mem_shortWords.mpr (hcfg_le k (Finset.mem_range.mp hk))
  calc t₀ = (Finset.range t₀).card := (Finset.card_range t₀).symm
    _ = ((Finset.range t₀).image (fun k => eCfg (run d x (k + 1)))).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (shortWords b).card := Finset.card_le_card hsub
    _ ≤ 2 ^ (b + 1) := (card_shortWords_lt b).le

/-- **Configuration-count clock for visited-space simulations:** if `universal (d, x, t)` halts at
some step `t` with `simSpace d x t ≤ s`, then for any `b ≥ cfgSpaceBound (descLen d) x.length
d.tapes s`, it already halts with the same output at some step `t₀ ≤ 2 ^ (b + 1)` with
`simSpace d x t₀ ≤ s`. -/
theorem exists_simSpace_le_and_universal_le_two_pow {t s b : ℕ}
    (hsp : simSpace d x t ≤ s) (hhalt : (universal (d, x, t)).2 = true)
    (hb : cfgSpaceBound (descLen d) x.length d.tapes s ≤ b) :
    ∃ t₀ ≤ 2 ^ (b + 1), simSpace d x t₀ ≤ s ∧
      universal (d, x, t₀) = universal (d, x, t) := by
  classical
  have hex : ∃ k, (run d x k).state.isNone = true := ⟨t, hhalt⟩
  let t₀ := Nat.find hex
  have ht₀ : (run d x t₀).state.isNone = true := Nat.find_spec hex
  have ht₀_le : t₀ ≤ t := Nat.find_min' hex hhalt
  have ht₀_sp : simSpace d x t₀ ≤ s := (simSpace_mono d x ht₀_le).trans hsp
  have hcfg_le : ∀ k < t₀, (eCfg (run d x (k + 1))).length ≤ b := by
    intro k hk
    have hk_sp : simSpace d x (k + 1) ≤ s := (simSpace_mono d x (by omega)).trans ht₀_sp
    refine (length_eCfg_le_space d x (k + 1)).trans (le_trans ?_ hb)
    unfold cfgSpaceBound
    gcongr
  exact ⟨t₀, le_two_pow_of_first_halt d x b ht₀ (fun _ hm => Nat.find_min hex hm) hcfg_le,
    ht₀_sp, (universal_eq_of_snd d x ht₀ ht₀_le).symm⟩

/-- **Clocked equivalence for visited-space simulations:** for any `b ≥ cfgSpaceBound (descLen d)
x.length d.tapes s` and any step count `T ≥ 2 ^ (b + 1)`, there exists a step `t` with
`simSpace d x t ≤ s` and `universal (d, x, t) = (out, true)` if and only if `simSpace d x T ≤ s`
and `universal (d, x, T) = (out, true)`. -/
theorem exists_simSpace_le_and_universal_eq_true_iff (s : ℕ) (out : List ℕ) {b T : ℕ}
    (hb : cfgSpaceBound (descLen d) x.length d.tapes s ≤ b) (hT : 2 ^ (b + 1) ≤ T) :
    (∃ t, simSpace d x t ≤ s ∧ universal (d, x, t) = (out, true)) ↔
      (simSpace d x T ≤ s ∧ universal (d, x, T) = (out, true)) := by
  refine ⟨fun ⟨t, hsp, ht⟩ => ?_, fun h => ⟨T, h⟩⟩
  have hhalt : (universal (d, x, t)).2 = true := by rw [ht]
  obtain ⟨t₀, ht₀_le, ht₀_sp, ht₀_eq⟩ :=
    exists_simSpace_le_and_universal_le_two_pow d x hsp hhalt hb
  have ht₀_halt : (universal (d, x, t₀)).2 = true := by rw [ht₀_eq, ht]
  have ht₀_state : (run d x t₀).state = none := Option.isNone_iff_eq_none.mp ht₀_halt
  have hT_le : t₀ ≤ T := ht₀_le.trans hT
  exact ⟨simSpace_eq_of_state_eq_none d x ht₀_state hT_le ▸ ht₀_sp,
    by rw [universal_eq_of_snd d x ht₀_halt hT_le, ht₀_eq, ht]⟩

/-! ### Configuration-count clock and polynomial-space certificate for `budgetedUniversal` -/

/-- Once `budgetStep` reaches a halted configuration with at most `2` output symbols, it is a fixed
point. -/
theorem budgetStep_of_state_eq_none {p : SCfg × List ℕ} (hstate : p.1.state = none)
    (hlen : p.2.length ≤ 2) : budgetStep d x b p = p := by
  rcases p with ⟨c, out⟩
  dsimp only at hstate hlen
  simp only [budgetStep, step, hstate, Option.toList_none, List.append_nil,
    List.take_of_length_le hlen, ite_self]

/-- Once the budgeted run from `(init d, [])` halts at step `t`, it remains at the same pair at
every later step `T ≥ t`. -/
theorem budgetStep_iterate_eq_of_le {t T : ℕ}
    (hhalt : ((budgetStep d x b)^[t] (init d, [])).1.state.isNone = true) (hT : t ≤ T) :
    (budgetStep d x b)^[T] (init d, []) = (budgetStep d x b)^[t] (init d, []) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hT
  clear hT
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, Function.iterate_succ_apply', ih]
    refine budgetStep_of_state_eq_none d x b (Option.isNone_iff_eq_none.mp hhalt) ?_
    obtain ⟨j, -, heq, -⟩ := budgetStep_iterate d x b t
    rw [heq]
    exact List.length_take_le _ _

/-- Once `budgetedUniversal (d, x, t, b)` reports halting, increasing the step count `t ≤ T` leaves
its result unchanged. -/
theorem budgetedUniversal_eq_of_le_of_snd {t T : ℕ}
    (hhalt : (budgetedUniversal (d, x, t, b)).2 = true) (hT : t ≤ T) :
    budgetedUniversal (d, x, T, b) = budgetedUniversal (d, x, t, b) := by
  simp only [budgetedUniversal] at hhalt ⊢
  rw [budgetStep_iterate_eq_of_le d x b hhalt hT]

/-- **Configuration-count clock for `budgetedUniversal`:** if `budgetedUniversal (d, x, t, b)`
halts at some step `t`, then it already halts with the same output at some step `t₀ ≤ 2 ^ (b + 1)`.
Before the first halting step `t₀`, every step must fit within the `b`-bit configuration budget and
visit a distinct configuration in `shortWords b`. -/
theorem exists_budgetedUniversal_le_two_pow {t : ℕ}
    (hhalt : (budgetedUniversal (d, x, t, b)).2 = true) :
    ∃ t₀ ≤ 2 ^ (b + 1), budgetedUniversal (d, x, t₀, b) = budgetedUniversal (d, x, t, b) := by
  classical
  have hex : ∃ k, ((budgetStep d x b)^[k] (init d, [])).1.state.isNone = true := ⟨t, hhalt⟩
  let t₀ := Nat.find hex
  have ht₀ : ((budgetStep d x b)^[t₀] (init d, [])).1.state.isNone = true := Nat.find_spec hex
  have ht₀_le : t₀ ≤ t := Nat.find_min' hex hhalt
  have hstep :
      ∀ k < t₀, (eCfg (step d x ((budgetStep d x b)^[k] (init d, [])).1).1).length ≤ b := by
    intro k hk
    by_contra hnot
    have hfix : budgetStep d x b ((budgetStep d x b)^[k] (init d, [])) =
        (budgetStep d x b)^[k] (init d, []) := by
      simp only [budgetStep, hnot, ↓reduceIte]
    have hstay : (budgetStep d x b)^[t₀] (init d, []) =
        (budgetStep d x b)^[k] (init d, []) := by
      rw [← Nat.sub_add_cancel hk.le, Function.iterate_add_apply,
        Function.iterate_fixed hfix (t₀ - k)]
    exact Nat.find_min hex hk (hstay ▸ ht₀)
  have hfst : ∀ k ≤ t₀, ((budgetStep d x b)^[k] (init d, [])).1 = run d x k := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih =>
      have hk_lt : k < t₀ := Nat.lt_of_succ_le hk
      have hle := hstep k hk_lt
      rw [Function.iterate_succ_apply', budgetStep]
      split_ifs
      rw [ih hk_lt.le, run_succ]
  have hb : ∀ k < t₀, (eCfg (run d x (k + 1))).length ≤ b := fun k hk => by
    simpa only [hfst k hk.le, ← run_succ] using hstep k hk
  exact ⟨t₀,
    le_two_pow_of_first_halt d x b (hfst t₀ le_rfl ▸ ht₀)
      (fun m hm h => Nat.find_min hex hm (hfst m hm.le ▸ h)) hb,
    (budgetedUniversal_eq_of_le_of_snd d x b ht₀ ht₀_le).symm⟩

/-- **Clocked equivalence for `budgetedUniversal`:** for any step count `T ≥ 2 ^ (b + 1)`, there
exists a step `t` at which `budgetedUniversal (d, x, t, b) = (out, true)` if and only if
`budgetedUniversal (d, x, T, b) = (out, true)`. -/
theorem exists_budgetedUniversal_eq_true_iff (out : List ℕ) {T : ℕ} (hT : 2 ^ (b + 1) ≤ T) :
    (∃ t, budgetedUniversal (d, x, t, b) = (out, true)) ↔
      budgetedUniversal (d, x, T, b) = (out, true) := by
  refine ⟨fun ⟨t, ht⟩ => ?_, fun h => ⟨T, h⟩⟩
  have hhalt : (budgetedUniversal (d, x, t, b)).2 = true := by rw [ht]
  obtain ⟨t₀, ht₀_le, ht₀_eq⟩ := exists_budgetedUniversal_le_two_pow d x b hhalt
  rw [← ht, ← ht₀_eq]
  exact budgetedUniversal_eq_of_le_of_snd d x b (by rw [ht₀_eq, ht]) (ht₀_le.trans hT)

private lemma listMax_le_length_encList_encUnary (x : List ℕ) :
    x.foldr max 0 ≤ (encList encUnary x).length := by
  induction x with
  | nil => rfl
  | cons a x ih =>
    simp only [List.foldr_cons, encList_cons, List.length_append, length_frame, encUnary_apply,
      List.length_replicate]
    omega

/-- **`budgetedUniversal` is computable in polynomial space** (in fact linear space) with respect
to `eInS` and `eOut`. -/
theorem computableInPolySpace_budgetedUniversal :
    ComputableInPolySpace budgetedUniversal eInS eOut := by
  obtain ⟨c, hc, hl⟩ := computableInO_budgetedUniversal
  exact ComputableInPolySpace.of_inSpace
    (by growth_poly [budgetSpace_le, listMax_le_length_encList_encUnary]) ⟨_, c, hc, hl⟩

/-! ### Visited-cell-budgeted universal simulation (`spaceBoundedUniversal`) -/

/-- Canonical encoding of per-tape head excursion bounds `List (ℕ × ℕ)`. -/
abbrev eBounds : List (ℕ × ℕ) ↪ List Bool :=
  encList (encPair encUnary encUnary)

/-- Initial per-tape head excursion bounds `(leftMax, rightMax) = (0, 0)` for each of `d.tapes`
work tapes. -/
@[expose] def initBounds (d : Desc) : List (ℕ × ℕ) :=
  List.replicate d.tapes (0, 0)

/-- Update per-tape head excursion bounds `(leftMax, rightMax)` from the current work-tape head
positions. -/
@[expose] def updateBounds (tapes : List Tape) (bounds : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (tapes.zip bounds).map fun p =>
    let b := p.2
    (max b.1 (-p.1.head).toNat, max b.2 p.1.head.toNat)

/-- Total number of visited work-tape cells represented by per-tape excursion bounds
`bounds : List (ℕ × ℕ)`, where an excursion interval `[ -l, r ]` covers `l + r + 1` cells. -/
@[expose] def boundsSpace (bounds : List (ℕ × ℕ)) : ℕ :=
  (bounds.flatMap fun p => List.replicate (p.1 + p.2 + 1) true).length

/-- The per-tape head excursion bounds along the simulated run `run d x` after `j` steps. -/
@[expose] def boundsAt (d : Desc) (x : List ℕ) : ℕ → List (ℕ × ℕ)
  | 0 => initBounds d
  | j + 1 => updateBounds (run d x (j + 1)).workTapes (boundsAt d x j)

@[simp]
theorem boundsAt_zero : boundsAt d x 0 = initBounds d := rfl

theorem boundsAt_succ (j : ℕ) :
    boundsAt d x (j + 1) = updateBounds (run d x (j + 1)).workTapes (boundsAt d x j) := rfl

theorem boundsSpace_eq_sum_map (bounds : List (ℕ × ℕ)) :
    boundsSpace bounds = (bounds.map fun p => p.1 + p.2 + 1).sum := by
  simp [boundsSpace, List.length_flatMap]

private lemma sum_map_eq_sum_range {α : Type} (defVal : α) (l : List α) (f : α → ℕ) :
    (l.map f).sum = ∑ i ∈ Finset.range l.length, f (l.getD i defVal) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.length_cons, Finset.sum_range_succ']
    simp [Nat.add_comm]

theorem length_boundsAt (j : ℕ) : (boundsAt d x j).length = d.tapes := by
  induction j with
  | zero => simp [boundsAt, initBounds]
  | succ j ih =>
    simp [boundsAt, updateBounds, length_run_workTapes, ih]

private lemma getD_updateBounds (tapes : List Tape) (bounds : List (ℕ × ℕ)) {i : ℕ}
    (ht : i < tapes.length) (hb : i < bounds.length) :
    (updateBounds tapes bounds).getD i (0, 0) =
      (max (bounds.getD i (0, 0)).1 (-(tapes.getD i .blank).head).toNat,
        max (bounds.getD i (0, 0)).2 (tapes.getD i .blank).head.toNat) := by
  have hmap : i < (updateBounds tapes bounds).length := by simp [updateBounds, ht, hb]
  rw [List.getD_eq_getElem _ _ hmap, List.getD_eq_getElem _ _ ht, List.getD_eq_getElem _ _ hb]
  simp [updateBounds]

private lemma visited_succ (j i : ℕ) :
    visited d x (j + 1) i = insert (headAt d x (j + 1) i) (visited d x j i) := by
  simp [visited, Finset.range_add_one]

private lemma insert_Icc_of_step {a b h h' : ℤ} (hab : a ≤ h ∧ h ≤ b)
    (hstep : h' = h - 1 ∨ h' = h ∨ h' = h + 1) :
    insert h' (Finset.Icc a b) = Finset.Icc (min a h') (max b h') := by
  ext z
  simp only [Finset.mem_insert, Finset.mem_Icc]
  omega

/-- At step `j`, for every work tape `i < d.tapes`, the visited positions `visited d x j i` form
the integer interval `[ -l, r ]` where `(l, r) = (boundsAt d x j).getD i (0, 0)`, and the current
head `headAt d x j i` lies in `[ -l, r ]`. -/
theorem visited_eq_Icc_boundsAt (j : ℕ) {i : ℕ} (hi : i < d.tapes) :
    visited d x j i =
        Finset.Icc (-(((boundsAt d x j).getD i (0, 0)).1 : ℤ))
          (((boundsAt d x j).getD i (0, 0)).2 : ℤ) ∧
      -(((boundsAt d x j).getD i (0, 0)).1 : ℤ) ≤ headAt d x j i ∧
      headAt d x j i ≤ (((boundsAt d x j).getD i (0, 0)).2 : ℤ) := by
  induction j with
  | zero =>
    have hget : (boundsAt d x 0).getD i (0, 0) = (0, 0) := by
      simp [boundsAt, initBounds, hi]
    rw [hget, headAt_zero]
    simp [visited, headAt_zero]
  | succ j ih =>
    obtain ⟨hvis, hlo, hhi⟩ := ih
    have hlen_tapes : (run d x (j + 1)).workTapes.length = d.tapes :=
      length_run_workTapes d x (j + 1)
    have hlen_bounds : (boundsAt d x j).length = d.tapes := length_boundsAt d x j
    have hi_tapes : i < (run d x (j + 1)).workTapes.length := hlen_tapes ▸ hi
    have hi_bounds : i < (boundsAt d x j).length := hlen_bounds ▸ hi
    have hget : (boundsAt d x (j + 1)).getD i (0, 0) =
        (max ((boundsAt d x j).getD i (0, 0)).1 (-(headAt d x (j + 1) i)).toNat,
          max ((boundsAt d x j).getD i (0, 0)).2 (headAt d x (j + 1) i).toNat) := by
      rw [boundsAt_succ, getD_updateBounds _ _ hi_tapes hi_bounds, headAt]
    obtain ⟨a, ha⟩ := step_tape d x (run d x j) i
    have hstep : headAt d x (j + 1) i = headAt d x j i - 1 ∨
        headAt d x (j + 1) i = headAt d x j i ∨
        headAt d x (j + 1) i = headAt d x j i + 1 := by
      simp only [headAt, run_succ, ha]
      exact head_apply _ a
    set l := ((boundsAt d x j).getD i (0, 0)).1
    set r := ((boundsAt d x j).getD i (0, 0)).2
    set h' := headAt d x (j + 1) i
    have hl' : -((max l (-h').toNat : ℕ) : ℤ) = min (-(l : ℤ)) h' := by omega
    have hr' : ((max r h'.toNat : ℕ) : ℤ) = max (r : ℤ) h' := by omega
    rw [hget]
    dsimp only
    rw [visited_succ, hvis, insert_Icc_of_step ⟨hlo, hhi⟩ hstep, hl', hr']
    exact ⟨rfl, by omega, by omega⟩

theorem card_visited_eq_boundsAt (j : ℕ) {i : ℕ} (hi : i < d.tapes) :
    (visited d x j i).card =
      ((boundsAt d x j).getD i (0, 0)).1 + ((boundsAt d x j).getD i (0, 0)).2 + 1 := by
  rw [(visited_eq_Icc_boundsAt d x j hi).1, Int.card_Icc]
  omega

/-- **`boundsSpace (boundsAt d x j)` equals `simSpace d x j`.** -/
theorem boundsSpace_boundsAt (j : ℕ) : boundsSpace (boundsAt d x j) = simSpace d x j := by
  rw [boundsSpace_eq_sum_map, sum_map_eq_sum_range (0, 0),
    length_boundsAt, simSpace]
  refine Finset.sum_congr rfl fun i hi => ?_
  exact (card_visited_eq_boundsAt d x j (Finset.mem_range.mp hi)).symm

/-- At step `0`, `simSpace d x 0 = d.tapes`. -/
theorem simSpace_zero : simSpace d x 0 = d.tapes := by
  rw [← boundsSpace_boundsAt d x 0, boundsAt_zero, initBounds, boundsSpace_eq_sum_map]
  simp

/-- Loop state for visited-space bounded universal simulation. -/
structure SpaceLoopState where
  /-- Description of the simulated machine. -/
  desc : Desc
  /-- Simulated input symbols. -/
  input : List ℕ
  /-- Visited work-tape cell budget. -/
  space : ℕ
  /-- Current simulated configuration. -/
  cfg : SCfg
  /-- First two output symbols emitted so far. -/
  output : List ℕ
  /-- Per-tape head excursion bounds `(leftMax, rightMax)`. -/
  bounds : List (ℕ × ℕ)
  /-- Whether every step up to the current configuration stayed within `space` visited cells. -/
  withinSpace : Bool
deriving Inhabited

/-- Canonical encoding of `SpaceLoopState`. -/
enc_structure eSpaceLoopState : SpaceLoopState where
  desc : eDesc,
  input : (encList encUnary),
  space : encUnary,
  cfg : eCfg,
  output : (encList encUnary),
  bounds : eBounds,
  withinSpace : encBool

/-- Initial state for `spaceBoundedUniversal (d, x, t, s)`. -/
@[expose] def spaceLoopInit (i : Desc × List ℕ × ℕ × ℕ) : SpaceLoopState :=
  let rest := i.2
  let ts := rest.2
  { desc := i.1
    input := rest.1
    space := ts.2
    cfg := init i.1
    output := []
    bounds := initBounds i.1
    withinSpace := decide (i.1.tapes ≤ ts.2) }

/-- One step of visited-space bounded simulation: if `st.withinSpace` holds, compute the next
simulated configuration and updated excursion bounds; if the resulting visited cell count
`boundsSpace bounds'` stays within `st.space`, advance to the new configuration and bounds,
otherwise freeze the state and record `withinSpace := false`. -/
@[expose] def spaceLoopStep (st : SpaceLoopState) : SpaceLoopState :=
  if st.withinSpace then
    let next := step st.desc st.input st.cfg
    let bounds' := updateBounds next.1.workTapes st.bounds
    if decide (boundsSpace bounds' ≤ st.space) then
      { st with
        cfg := next.1
        output := (st.output ++ next.2.toList).take 2
        bounds := bounds' }
    else
      { st with withinSpace := false }
  else st

/-- **Visited-cell-budgeted universal simulation:** run `spaceLoopStep` for `t` steps on
`spaceLoopInit i` and return the first two output symbols together with whether the run stayed
within `s` visited work-tape cells and halted. -/
@[expose] def spaceBoundedUniversal (i : Desc × List ℕ × ℕ × ℕ) : List ℕ × Bool :=
  let rest := i.2
  let ts := rest.2
  let final := spaceLoopStep^[ts.1] (spaceLoopInit i)
  (final.output, final.withinSpace && final.cfg.state.isNone)

/-- Characterization of `spaceLoopStep^[k] (spaceLoopInit (d, x, t, s))`:
* when `simSpace d x k ≤ s`, the loop state is at step `k` of `run d x` with `withinSpace = true`;
* when `¬ simSpace d x k ≤ s`, `withinSpace = false` and the loop state is frozen at some step
  `j ≤ k` with `j = 0 ∨ simSpace d x j ≤ s`. -/
theorem spaceLoopStep_iterate (t s k : ℕ) :
    (simSpace d x k ≤ s →
      spaceLoopStep^[k] (spaceLoopInit (d, x, t, s)) =
        ⟨d, x, s, run d x k, ((stepOut d x)^[k] (init d, [])).2.take 2, boundsAt d x k, true⟩) ∧
    (¬ simSpace d x k ≤ s →
      ∃ j ≤ k, (j = 0 ∨ simSpace d x j ≤ s) ∧
        spaceLoopStep^[k] (spaceLoopInit (d, x, t, s)) =
          ⟨d, x, s, run d x j, ((stepOut d x)^[j] (init d, [])).2.take 2,
            boundsAt d x j, false⟩) := by
  induction k with
  | zero =>
    rw [simSpace_zero]
    refine ⟨fun h => ?_, fun h => ⟨0, le_rfl, Or.inl rfl, ?_⟩⟩ <;> simp [spaceLoopInit, run, h]
  | succ k ih =>
    obtain ⟨ih_le, ih_gt⟩ := ih
    refine ⟨fun hle => ?_, fun hgt => ?_⟩
    · have hk : simSpace d x k ≤ s := (simSpace_mono d x (Nat.le_succ k)).trans hle
      rw [Function.iterate_succ_apply', ih_le hk]
      have hb : boundsSpace (boundsAt d x (k + 1)) ≤ s := (boundsSpace_boundsAt d x _).trans_le hle
      simp only [spaceLoopStep, ↓reduceIte, decide_eq_true_eq, stepOut_iterate_succ,
        take_two_append_take_two, ← run_succ, ← boundsAt_succ, hb]
    · by_cases hk : simSpace d x k ≤ s
      · refine ⟨k, Nat.le_succ k, Or.inr hk, ?_⟩
        rw [Function.iterate_succ_apply', ih_le hk]
        have hb : ¬ boundsSpace (boundsAt d x (k + 1)) ≤ s := by rwa [boundsSpace_boundsAt]
        simp only [spaceLoopStep, ↓reduceIte, decide_eq_true_eq, ← run_succ, ← boundsAt_succ, hb]
      · obtain ⟨j, hj, hj_sp, heq⟩ := ih_gt hk
        refine ⟨j, hj.trans (Nat.le_succ k), hj_sp, ?_⟩
        rw [Function.iterate_succ_apply', heq]
        rfl

/-- Every reachable state of `spaceLoopStep` from `spaceLoopInit (d, x, t, s)` is at some step
`j ≤ k` of `run d x` with `j = 0 ∨ simSpace d x j ≤ s`. -/
theorem exists_spaceLoopStep_iterate (t s k : ℕ) :
    ∃ j ≤ k, ∃ ok : Bool, (j = 0 ∨ simSpace d x j ≤ s) ∧
      spaceLoopStep^[k] (spaceLoopInit (d, x, t, s)) =
        ⟨d, x, s, run d x j, ((stepOut d x)^[j] (init d, [])).2.take 2, boundsAt d x j, ok⟩ := by
  by_cases hk : simSpace d x k ≤ s
  · exact ⟨k, le_rfl, true, Or.inr hk, (spaceLoopStep_iterate d x t s k).1 hk⟩
  · obtain ⟨j, hj, hj_sp, heq⟩ := (spaceLoopStep_iterate d x t s k).2 hk
    exact ⟨j, hj, false, hj_sp, heq⟩

/-- When `simSpace d x t ≤ s`, `spaceBoundedUniversal (d, x, t, s)` returns the first two output
symbols of `universal (d, x, t)` and whether it has halted. -/
theorem spaceBoundedUniversal_eq_of_simSpace_le {t s : ℕ} (hsp : simSpace d x t ≤ s) :
    spaceBoundedUniversal (d, x, t, s) =
      ((universal (d, x, t)).1.take 2, (universal (d, x, t)).2) := by
  simp only [spaceBoundedUniversal, (spaceLoopStep_iterate d x t s t).1 hsp, Bool.true_and,
    universal, simulate]
  rfl

/-- When `¬ simSpace d x t ≤ s`, `spaceBoundedUniversal (d, x, t, s)` reports `false` in its second
component. -/
theorem spaceBoundedUniversal_snd_eq_false_of_gt {t s : ℕ} (hsp : ¬ simSpace d x t ≤ s) :
    (spaceBoundedUniversal (d, x, t, s)).2 = false := by
  obtain ⟨j, -, -, heq⟩ := (spaceLoopStep_iterate d x t s t).2 hsp
  simp [spaceBoundedUniversal, heq]

/-- **Characterization of `spaceBoundedUniversal` acceptance:**
`spaceBoundedUniversal (d, x, t, s) = (out, true)` holds if and only if `simSpace d x t ≤ s`,
`(universal (d, x, t)).1.take 2 = out`, and `(universal (d, x, t)).2 = true`. -/
theorem spaceBoundedUniversal_eq_true_iff (t s : ℕ) (out : List ℕ) :
    spaceBoundedUniversal (d, x, t, s) = (out, true) ↔
      simSpace d x t ≤ s ∧
        (universal (d, x, t)).1.take 2 = out ∧
        (universal (d, x, t)).2 = true := by
  by_cases hsp : simSpace d x t ≤ s
  · rw [spaceBoundedUniversal_eq_of_simSpace_le d x hsp, Prod.mk.injEq]
    exact ⟨fun h => ⟨hsp, h⟩, fun h => h.2⟩
  · exact ⟨fun h => absurd (spaceBoundedUniversal_snd_eq_false_of_gt d x hsp) (by simp [h]),
      fun h => absurd h.1 hsp⟩

/-- Taking the first `2` elements of a list equals a singleton `[a]` if and only if the list itself
equals `[a]`. -/
theorem take_two_eq_singleton_iff {α : Type*} {l : List α} {a : α} :
    l.take 2 = [a] ↔ l = [a] := by
  rcases l with _ | ⟨x, _ | ⟨y, rest⟩⟩ <;> simp

/-- **Singleton-output characterization of `spaceBoundedUniversal`:**
`spaceBoundedUniversal (d, x, t, s) = ([n], true)` holds if and only if `simSpace d x t ≤ s` and
`universal (d, x, t) = ([n], true)`. -/
theorem spaceBoundedUniversal_eq_singleton_true_iff (t s n : ℕ) :
    spaceBoundedUniversal (d, x, t, s) = ([n], true) ↔
      simSpace d x t ≤ s ∧ universal (d, x, t) = ([n], true) := by
  rw [spaceBoundedUniversal_eq_true_iff, take_two_eq_singleton_iff, ← Prod.mk.injEq, Prod.mk.eta]

/-- **Clocked equivalence for `spaceBoundedUniversal` with singleton output:** for any
`b ≥ cfgSpaceBound (descLen d) x.length d.tapes s` and `T ≥ 2 ^ (b + 1)`, there exists a step `t`
at which `spaceBoundedUniversal (d, x, t, s) = ([n], true)` if and only if
`spaceBoundedUniversal (d, x, T, s) = ([n], true)`. -/
theorem exists_spaceBoundedUniversal_eq_singleton_true_iff (s n : ℕ) {b T : ℕ}
    (hb : cfgSpaceBound (descLen d) x.length d.tapes s ≤ b) (hT : 2 ^ (b + 1) ≤ T) :
    (∃ t, spaceBoundedUniversal (d, x, t, s) = ([n], true)) ↔
      spaceBoundedUniversal (d, x, T, s) = ([n], true) := by
  simp_rw [spaceBoundedUniversal_eq_singleton_true_iff]
  exact exists_simSpace_le_and_universal_eq_true_iff d x s [n] hb hT

/-! ### Polynomial-time step and polynomial-space certificate for `spaceBoundedUniversal` -/

/-- `init` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_init :
    ComputableInPolyTime init eDesc eCfg :=
  init_inO.computableInPolyTime
    (PolyBounded.of_forall_le 1 2 fun _ => by simp)
    (PolyBounded.of_forall_le 1 1 fun _ => by simp)

/-- `step` is computable in polynomial time on contexts `eCtx`. -/
@[fun_prop]
theorem computableInPolyTime_step :
    ComputableInPolyTime (fun c : Ctx => step c.desc c.input c.cfg) eCtx (encPair eCfg eSym) :=
  step_inO.computableInPolyTime (by growth_poly [table_le]) (by growth_poly)

/-- Keeping the first two output symbols after appending an optional symbol is computable in
polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_keepTwo :
    ComputableInPolyTime (fun p : List ℕ × Option ℕ => (p.1 ++ p.2.toList).take 2)
      (encPair (encList encUnary) eSym) (encList encUnary) :=
  keepTwo_inO.computableInPolyTime
    (PolyBounded.of_forall_le 1 1 fun _ => by simp)
    (PolyBounded.of_forall_le 1 1 fun _ => by simp)

/-- `initBounds` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_initBounds :
    ComputableInPolyTime initBounds eDesc eBounds := by
  unfold initBounds eBounds
  fun_prop

/-- `updateBounds` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_updateBounds :
    ComputableInPolyTime (fun p : List Tape × List (ℕ × ℕ) => updateBounds p.1 p.2)
      (encPair (encList eTape) eBounds) eBounds := by
  unfold updateBounds eBounds
  fun_prop

/-- `boundsSpace` is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_boundsSpace :
    ComputableInPolyTime boundsSpace eBounds encUnary := by
  unfold boundsSpace eBounds
  exact (ComputableInPolyTime.length_list encBool).comp (by fun_prop)

/-- `spaceLoopInit` is computable in polynomial time from `eInS` to `eSpaceLoopState`. -/
@[fun_prop]
theorem computableInPolyTime_spaceLoopInit :
    ComputableInPolyTime spaceLoopInit eInS eSpaceLoopState := by
  unfold spaceLoopInit
  fun_prop

/-- `spaceLoopStep` is computable in polynomial time on `eSpaceLoopState`. -/
@[fun_prop]
theorem computableInPolyTime_spaceLoopStep :
    ComputableInPolyTime spaceLoopStep eSpaceLoopState eSpaceLoopState := by
  have hstep : ComputableInPolyTime (fun st : SpaceLoopState => step st.desc st.input st.cfg)
      eSpaceLoopState (encPair eCfg eSym) :=
    (computableInPolyTime_step.comp (g := fun st : SpaceLoopState => ((st.desc, st.input), st.cfg))
      (by fun_prop)).of_enc_eq fun _ => rfl
  have hout : ComputableInPolyTime
      (fun st : SpaceLoopState => (st.output ++ (step st.desc st.input st.cfg).2.toList).take 2)
      eSpaceLoopState (encList encUnary) :=
    computableInPolyTime_keepTwo.comp
      (g := fun st : SpaceLoopState => (st.output, (step st.desc st.input st.cfg).2)) (by fun_prop)
  unfold spaceLoopStep
  dsimp only
  fun_prop

private lemma le_of_mem_boundsAt {j s : ℕ} (hsp : j = 0 ∨ simSpace d x j ≤ s)
    {p : ℕ × ℕ} (hp : p ∈ boundsAt d x j) : p.1 ≤ s ∧ p.2 ≤ s := by
  rcases hsp with rfl | hsp
  · simp [List.eq_of_mem_replicate hp]
  · have hmem : p.1 + p.2 + 1 ∈ (boundsAt d x j).map (fun q => q.1 + q.2 + 1) :=
      List.mem_map_of_mem hp
    have hle : p.1 + p.2 + 1 ≤ s :=
      (List.le_sum_of_mem hmem).trans
        (by rw [← boundsSpace_eq_sum_map, boundsSpace_boundsAt]; exact hsp)
    omega

private lemma length_boundsAt_le {j s : ℕ} (hsp : j = 0 ∨ simSpace d x j ≤ s) :
    (encList (encPair encUnary encUnary) (boundsAt d x j)).length ≤
      descLen d * (6 * s + 3) := by
  have hlen := length_encList_le (encPair encUnary encUnary) (boundsAt d x j) (b := 3 * s + 1)
    fun p hp => by
      obtain ⟨h₁, h₂⟩ := le_of_mem_boundsAt d x hsp hp
      simp only [length_encPair, encUnary_apply, List.length_replicate]
      omega
  rw [length_boundsAt] at hlen
  exact hlen.trans (Nat.mul_le_mul (tapes_le d) (by omega))

private lemma length_eSpaceLoopState_iterate_le (i : Desc × List ℕ × ℕ × ℕ) (k : ℕ) :
    (eSpaceLoopState (spaceLoopStep^[k] (spaceLoopInit i))).length ≤
      1200 * ((eInS i).length + 1) ^ 2 := by
  rcases i with ⟨d, x, t, s⟩
  obtain ⟨j, -, ok, hsp, heq⟩ := exists_spaceLoopStep_iterate d x t s k
  rw [heq]
  set N := (eInS (d, x, t, s)).length
  have hd : descLen d ≤ N := by
    simp only [N, descLen, length_encPair]; omega
  have hx : (encList encUnary x).length ≤ N := by
    simp only [N, length_encPair]; omega
  have hs : s ≤ N := by
    simp only [N, length_encPair, encUnary_apply, List.length_replicate]; omega
  have hxlen : x.length ≤ N := (length_le_length_encList encUnary x).trans hx
  have hnat : (encNat (x.length + 1)).length ≤ N + 1 :=
    (length_encNat_le_self (x.length + 1)).trans (by omega)
  have htapes : d.tapes ≤ N := (tapes_le d).trans hd
  have hcfg : (eCfg (run d x j)).length ≤ 12 * N ^ 2 + 41 * N + 6 := by
    rcases hsp with rfl | hsp'
    · have hinit := length_eCfg_init_le d
      change (eCfg (init d)).length ≤ _
      nlinarith
    · have hsp_le := length_eCfg_le_space d x j
      have hmul : (2 * descLen d + 5) * simSpace d x j ≤ (2 * N + 5) * N :=
        Nat.mul_le_mul (by omega) (hsp'.trans hs)
      nlinarith
  have hout_len : (((stepOut d x)^[j] (init d, [])).2.take 2).length ≤ 2 :=
    List.length_take_le 2 _
  have hout : (encList encUnary (((stepOut d x)^[j] (init d, [])).2.take 2)).length ≤
      4 * N + 2 := by
    have h₁ := length_encList_le encUnary (((stepOut d x)^[j] (init d, [])).2.take 2)
      (b := descLen d) fun o ho => by
        rw [encUnary_apply, List.length_replicate]
        exact (inv_iterate d x j).2.2 o (List.mem_of_mem_take ho)
    have h₂ := Nat.mul_le_mul_right (2 * descLen d + 1) hout_len
    nlinarith
  have hbounds : (encList (encPair encUnary encUnary) (boundsAt d x j)).length ≤
      6 * N ^ 2 + 3 * N := by
    have h₁ := length_boundsAt_le d x hsp
    have h₂ : descLen d * (6 * s + 3) ≤ N * (6 * N + 3) :=
      Nat.mul_le_mul hd (by omega)
    nlinarith
  simp only [eSpaceLoopState_apply, length_encPair, encUnary_apply, List.length_replicate,
    encBool_apply, List.length_singleton, descLen] at *
  nlinarith

/-- **`spaceBoundedUniversal` is computable in polynomial space** with respect to `eInS` and
`eOut`. -/
theorem computableInPolySpace_spaceBoundedUniversal :
    ComputableInPolySpace spaceBoundedUniversal eInS eOut := by
  have hclock : ComputableInPolyTime (fun i : Desc × List ℕ × ℕ × ℕ => i.2.2.1) eInS encNat := by
    fun_prop
  have hiter : ComputableInPolySpace
      (fun i : Desc × List ℕ × ℕ × ℕ => spaceLoopStep^[i.2.2.1] (spaceLoopInit i))
      eInS eSpaceLoopState :=
    ComputableInPolySpace.iterate hclock
      (ComputableInPolySpace.of_polyTime computableInPolyTime_spaceLoopInit)
      (ComputableInPolySpace.of_polyTime computableInPolyTime_spaceLoopStep)
      (PolyBounded.of_forall_le 1200 2 fun _ => le_rfl)
      (fun i k _ => length_eSpaceLoopState_iterate_le i k)
  have hisNone : ComputableInPolyTime (fun o : Option ℕ => o.isNone) eSym encBool := by
    have hisSome : ComputableInPolyTime (fun o : Option ℕ => o.isSome) eSym encBool :=
      ComputableInPolyTime.optionIsSome .id'
    refine (ComputableInPolyTime.bool_not.comp hisSome).of_enc_eq fun o => ?_
    cases o <;> rfl
  have hid : ComputableInPolyTime (fun st : SpaceLoopState => st)
      eSpaceLoopState eSpaceLoopState := .id'
  have hfinish : ComputableInPolyTime
      (fun st : SpaceLoopState => (st.output, st.withinSpace && st.cfg.state.isNone))
      eSpaceLoopState eOut :=
    (eSpaceLoopState_output_polyTime hid).prod
      (ComputableInPolyTime.bool_and.comp
        ((eSpaceLoopState_withinSpace_polyTime hid).prod
          (hisNone.comp (eCfg_state_polyTime (eSpaceLoopState_cfg_polyTime hid)))))
  exact (ComputableInPolySpace.of_polyTime hfinish).comp hiter

end Turing.MultiTapeTM.Universal
