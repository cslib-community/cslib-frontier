/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Exact
import Mathlib.Algebra.Ring.Int.Defs

/-! Tests of the correctness of the universal machine under ordinary imports:

* the input word of a tree, the cost of a step of the evaluation and the number of steps;
* the formula coded by a tree, by its opcode;
* the universal machine and the universal series on a concrete plain instance `z₁`: the program
  that multiplies by the constant with the name `[true]`, for a weight `θ₁` supported on
  `{[true]}` with `θ₁ [true] = 5`. The accepting runs of the machine are checked globally
  (`Mach.GV`), their weights sum to `θ₁ [true]` and they have at most `181` steps; the series is
  bounded at the word of `z₁` and has the value `θ₁ [true]` there. -/

set_option linter.privateModule false

namespace CslibFrontierTests.UniEval

open Cslib.Automata.Weighted Cslib.Circuits.Arithmetic.Separation Uni Interpreter Tape

/-- The word of a tree lists its brackets in preorder. -/
example : tbits (.cons .nil (.cons .nil .nil)) = [true, false, true, false, false] := rfl

/-- Names of the support `{[true], [true, false, true]}` have at most three bits, so a step of
the evaluation costs at most `40 + 2 * 3` steps of the machine. -/
example : nameLength {[true], [true, false, true]} = 3 ∧
    codeCost {[true], [true, false, true]} = 46 := by decide

example : runLength {[true], [true, false, true]} 5 7 = 3 * 7 + 46 * 5 + 10 := by decide

/-- The opcode `2` is `hd`. -/
example (a : Tree) : Fm.ofTree (.cons (Tree.num 2) a) = .hd (Fm.ofTree a) := by
  simp [Fm.ofTree.eq_2]

/-- Numbers from `11` on are no opcodes: the formula fails. -/
example (a : Tree) : Fm.ofTree (.cons (Tree.num 11) a) = .fail := by
  simp [Fm.ofTree.eq_2]

/-! ### A concrete plain instance -/

/-- A weight supported on `{[true]}`, with `θ₁ [true] = 5`. -/
private def θ₁ (q : List Bool) : ℤ := if q = [true] then 5 else 0

private theorem θ₁_eq_zero : ∀ q, q ∉ ({[true]} : Finset (List Bool)) → θ₁ q = 0 := by
  intro q hq
  rw [Finset.mem_singleton] at hq
  simp [θ₁, hq]

example : θ₁ [true] = 5 := rfl

/-- The program that multiplies by the constant with the name `[true]`. -/
private def prog₁ : Fm := .theta (.quote (Tree.ofBits [true]))

/-- The instance: the program `prog₁` at the empty argument. -/
private def z₁ : Tree := .cons prog₁.code .nil

private theorem ofTree_hd_z₁ : Fm.ofTree z₁.hd = prog₁ := Fm.ofTree_code prog₁

/-- `prog₁` has one accepting run: two steps, the weight `θ₁ [true]`, no named constants. -/
private theorem ev₁ : Ev θ₁ prog₁ .nil [⟨2, θ₁ [true], [], .nil⟩] := by
  simpa [Run.det, prog₁] using (Ev.quote (θ := θ₁) (Tree.ofBits [true]) .nil).theta

private theorem plain₁ : Plain θ₁ 2 z₁ := by
  refine ⟨by rw [ofTree_hd_z₁]; exact ev₁.hl, fun r hr => ?_⟩
  rw [ofTree_hd_z₁, show z₁.tl = .nil from rfl, ev₁.evl, List.mem_singleton] at hr
  subst hr
  exact ⟨rfl, le_rfl⟩

/-- The plain sum of `z₁` is the constant `θ₁ [true]`. -/
private theorem pv₁ : pv θ₁ z₁ = θ₁ [true] := by
  rw [pv, ofTree_hd_z₁, show z₁.tl = .nil from rfl, ev₁.evl]
  simp [pval]

/-- `z₁` has `29` nodes, so the runs on it have at most `3 * 29 + (40 + 2) * 2 + 10` steps. -/
private theorem runLength₁ : z₁.size = 29 ∧ runLength {[true]} 2 z₁.size = 181 := by decide

/-- The accepting runs of the universal machine on `z₁`: checked globally, with weights that sum
to `θ₁ [true]`, of at most `181` steps. -/
example : ∃ R : Finset (List (universalMachine θ₁ {[true]}).Step),
    (∀ tr, tr ∈ R ↔ Mach.GV (initState {[true]} z₁) tr) ∧ ∑ tr ∈ R, Mach.wts tr = θ₁ [true] ∧
      ∀ tr ∈ R, tr.length ≤ 181 := by
  obtain ⟨R, h₁, h₂, h₃⟩ := exists_runs_universalMachine θ₁_eq_zero plain₁
  exact ⟨R, h₁, h₂.trans pv₁, fun tr htr => runLength₁.2 ▸ h₃ tr htr⟩

/-- The universal series at the word of `z₁`: bounded on contents of length at most
`C * ((z₁.size + 2 + 2) * lg (z₁.size + 2 + 2) ^ 2)`, with the value `θ₁ [true]` there. -/
example : ∃ S₀ : Series ℤ (Zc RecKind × Sy (Mode (Name {[true]})) RecKind),
    RatLe (dimX (universalMachine θ₁ {[true]})) S₀ ∧ ∃ C : ℕ,
      Bdd (C * ((z₁.size + 2 + 2) * lg (z₁.size + 2 + 2) ^ 2)) S₀
          (fun _ => (tbits z₁).map .bit) ∧
        val (C * ((z₁.size + 2 + 2) * lg (z₁.size + 2 + 2) ^ 2)) S₀
          (fun _ => (tbits z₁).map .bit) = θ₁ [true] := by
  obtain ⟨S₀, h₁, C, h₂⟩ := exists_series_universal θ₁ {[true]} θ₁_eq_zero
  obtain ⟨h₃, h₄⟩ := h₂ 2 z₁ plain₁
  exact ⟨S₀, h₁, C, h₃, h₄.trans pv₁⟩

end CslibFrontierTests.UniEval
