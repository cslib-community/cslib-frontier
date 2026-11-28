/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BitString.List
public import CslibFrontier.Probability.IID

/-!
# Multi-segment and block-row splitting of uniform bit lists

Saved-coin evaluators parse one flat uniform tape into sequential segments with `List.take` and
`List.drop`, and into fixed-width blocks with `BitString.listRows`. This module lifts
`BitString.uniformList_bind_split` and `BitString.uniformList_listRows` directly to `PMF.map` and
`PMF.iid`, avoiding manual unfolding of `PMF.map` into `PMF.pure` binds:

* **Sequential heterogeneous segments** (`uniformList_map_split`, `uniformList_map_split3`, and
  suffix projection `uniformList_drop`): splitting a uniform tape of total length `n₁ + n₂` or
  `n₁ + (n₂ + n₃)` along nested `take`/`drop` offsets yields independent uniform segments,
  including when any segment has width zero.
* **Homogeneous block rows** (`uniformList_map_listRows`): mapping any evaluator `f : List Bool → α`
  over `listRows count width` of a `count * width`-bit uniform tape realizes `count` independent
  draws from `(uniformList width).map f` (`PMF.iid`), without requiring `α` to be finite.

## Main results

* `Cslib.BitString.uniformList_map_split`, `Cslib.BitString.uniformList_map_split3`: two- and
  three-segment `PMF.map` splitting laws for `uniformList`.
* `Cslib.BitString.uniformList_drop`: dropping a `k`-bit prefix from `uniformList (k + n)` gives
  `uniformList n`.
* `Cslib.BitString.uniformList_map_listRows`: mapping an evaluator over `listRows count width`
  gives `(PMF.iid ((uniformList width).map f) count).map List.ofFn`.
-/

public section

namespace Cslib.BitString

open Probability

/-- Mapping a two-argument evaluator across the `n₁`-bit prefix and `n₂`-bit suffix of a uniform
`(n₁ + n₂)`-bit tape gives two independent uniform segments, including when either width is zero. -/
theorem uniformList_map_split {α : Type*} (n₁ n₂ : ℕ)
    (f : List Bool → List Bool → α) :
    (uniformList (n₁ + n₂)).map (fun tape => f (tape.take n₁) (tape.drop n₁)) =
      (uniformList n₁).bind fun s₁ => (uniformList n₂).map (f s₁) := by
  simp only [PMF.map, Function.comp_def]
  exact uniformList_bind_split n₁ n₂ fun s₁ s₂ => PMF.pure (f s₁ s₂)

/-- Dropping a `k`-bit prefix from a uniform `(k + n)`-bit word leaves a uniform `n`-bit word,
with no condition on the discarded prefix. -/
theorem uniformList_drop (k n : ℕ) :
    (uniformList (k + n)).map (List.drop k) = uniformList n := by
  have h := uniformList_map_split k n fun _ => id
  simpa only [id_eq, PMF.bind_const, PMF.map_id] using h

/-- Mapping a three-argument evaluator across sequential `take`/`drop` slices of widths `n₁`, `n₂`,
and `n₃` gives three independent uniform segments. -/
theorem uniformList_map_split3 {α : Type*} (n₁ n₂ n₃ : ℕ)
    (f : List Bool → List Bool → List Bool → α) :
    (uniformList (n₁ + (n₂ + n₃))).map
        (fun tape => f (tape.take n₁) ((tape.drop n₁).take n₂) ((tape.drop n₁).drop n₂)) =
      (uniformList n₁).bind fun s₁ =>
        (uniformList n₂).bind fun s₂ => (uniformList n₃).map (f s₁ s₂) := by
  rw [uniformList_map_split n₁ (n₂ + n₃) fun s₁ rest => f s₁ (rest.take n₂) (rest.drop n₂)]
  congr 1 with s₁ : 1
  exact uniformList_map_split n₂ n₃ (f s₁)

/-- Mapping an evaluator `f` over the `count` fixed-width `width`-bit rows of a uniform
`(count * width)`-bit tape realizes `count` independent draws from `(uniformList width).map f`,
including at zero rows or zero width and without requiring `α` to be finite. -/
theorem uniformList_map_listRows {α : Type*} (count width : ℕ) (f : List Bool → α) :
    (uniformList (count * width)).map (fun w => (listRows count width w).map f) =
      (PMF.iid ((uniformList width).map f) count).map List.ofFn := by
  rw [show (fun w => (listRows count width w).map f) = List.map f ∘ listRows count width from rfl,
    ← PMF.map_comp, uniformList_listRows, PMF.map_comp, uniformList, PMF.map_comp,
    PMF.iid_map, PMF.iid_uniformOfFintype, PMF.map_comp]
  congr 1; funext rows; simp [Function.comp_def]

end Cslib.BitString
