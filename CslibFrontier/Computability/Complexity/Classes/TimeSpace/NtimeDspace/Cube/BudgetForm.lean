/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.BudgetNum
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Formula

/-!
# Index widths of the formula from budget arrays

The widths of the indices of the formula (`Formula.lean`) depend on a clique only through its
budgets, so the machine of Lemma 6.4 reads them from the budget array (`BudgetNum.lean`). Each
lemma here identifies a numeric width of `BudgetNum.lean` with the width of the formula, when
the budgets fit in the field width (`Fits`).

## Main results

* `argOffN_eq`, `argWidN_eq`, `sliceOffN_eq`, `sliceN_eq`, `copiesWidN_eq`: `argOffset`,
  `argWidth`, `sliceOffset`, `slice`, `copiesWidth`.
* `holders_eq`, `quad_eq`: the holders of the copies and the digits of a quadruple index.
* `xiWidN_eq`: `Setup.xiWidth`, for a parent on a square grid and a choice code with even grades.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset NtimeDspace.Cube

variable {fw : ℕ}

theorem argOffN_eq (C : Clique) (h : Fits fw C.a) (v u : ℕ) :
    argOffN (arrN C.q fw (extN C.a)) C.q fw v u = argOffset C v u := by
  unfold argOffN argOffset
  refine sum_congr rfl fun u' _ => ?_
  by_cases hc : u' < C.q ∧ v < C.q
  · rw [ite_eq_left hc, dite_eq_left hc]
    by_cases he : u' = v
    · rw [ite_eq_left he, ite_eq_left he]
    · rw [ite_eq_right he, ite_eq_right he]
      exact congrArg codeWidth (budgetN_ext h (u := ⟨v, hc.2⟩) (v := ⟨u', hc.1⟩)
        fun e => he (congrArg Fin.val e).symm)
  · rw [ite_eq_right hc, dite_eq_right hc]

theorem argWidN_eq (C : Clique) (h : Fits fw C.a) (w : ℕ) :
    argWidN (arrN C.q fw (extN C.a)) C.q fw w = argWidth C w := argOffN_eq C h w C.q

theorem sliceOffN_eq (C : Clique) (h : Fits fw C.a) (nodes : ℕ → ℕ) (p : ℕ) :
    sliceOffN (arrN C.q fw (extN C.a)) C.q fw nodes p = sliceOffset C nodes p :=
  sum_congr rfl fun p' _ => argWidN_eq C h (nodes p')

theorem sliceN_eq (C : Clique) (h : Fits fw C.a) (nodes : ℕ → ℕ) (ξ p : ℕ) :
    sliceN (arrN C.q fw (extN C.a)) C.q fw nodes ξ p = slice C nodes ξ p := by
  rw [sliceN, slice, sliceOffN_eq C h, argWidN_eq C h]

theorem copiesWidN_eq (C : Clique) (h : Fits fw C.a) (nodes : ℕ → ℕ) (n : ℕ) :
    copiesWidN (arrN C.q fw (extN C.a)) C.q fw nodes n = copiesWidth C nodes n :=
  sliceOffN_eq C h nodes n

theorem holders_eq (g v : ℕ) (row : Bool) :
    Setup.holders g v row = fun p => if row then v * g + p else p * g + v := rfl

theorem quad_eq (g t : ℕ) : quad g t = (qd g t 3, qd g t 2, qd g t 1, qd g t 0) := by
  simp only [quad, qd, pow_one, pow_zero, Nat.div_one]

/-- **The width of the copies** of node `v` of the child at `i :: rest`, from the array of the
parent `S.clique rest` (on a square grid, at a choice code with even grades). -/
theorem xiWidN_eq (S : Setup) (rest : List ℕ) (i v : ℕ)
    (hsq : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q)
    (h : Fits S.fw (S.clique rest).a)
    (he : ∀ r, Even (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1) :
    xiWidN (arrN (S.clique rest).q S.fw (extN (S.clique rest).a)) (S.clique rest).q S.fw
      (Nat.sqrt (S.clique rest).q) i v = S.xiWidth rest i v := by
  have e : ∀ n (hn : (S.clique rest).q = n),
      orientN (arrN n S.fw (extN (q := n) ((S.clique rest).recast n hn).a)) n S.fw
        (Nat.sqrt (S.clique rest).q) i =
      orientN (arrN (S.clique rest).q S.fw (extN (S.clique rest).a)) (S.clique rest).q S.fw
        (Nat.sqrt (S.clique rest).q) i := by
    intro n hn; subst hn; rfl
  have ho := (e _ hsq).symm.trans
    (orientN_eq (g := Nat.sqrt (S.clique rest).q) (h.recast _ hsq) he)
  simp only [Setup.xiWidth, Setup.parentGrid, dite_eq_left hsq]
  rw [xiWidN, ho, copiesWidN_eq _ h, holders_eq]

end Cslib.Complexity.NtimeDspace.Cube.Num
