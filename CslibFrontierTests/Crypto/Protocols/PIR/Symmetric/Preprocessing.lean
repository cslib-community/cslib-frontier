/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module

public import CslibFrontier.Crypto.Protocols.PIR.Symmetric.Preprocessing
public import CslibFrontier.Crypto.Protocols.PIR.Symmetric.Toy

/-!
# Tests for symmetric PIR with client preprocessing

Concrete witnesses and sanity checks for `Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing`:

1. **Joint satisfiability of the core lower-bound hypotheses**: `toyScheme 2 1` (`n = 2`, `k = 1`)
   is simultaneously perfectly correct (`IsCorrectWith 1`), perfectly private
   (`IsPerfectlyPrivate`), and perfectly data private (`IsPerfectlyDataPrivate`), and satisfies
   `Scheme.correct_le_card_div_two_pow` and `Scheme.two_pow_le_card_state` with
   `Fintype.card (ToyState 2) = 8`.
2. **Necessity of the `2 ≤ n` hypothesis in Theorem 6.2**: at `n = k = 1`, the zero-storage
   scheme `downloadOneBitScheme` (`St = Unit`, `Fintype.card Unit = 1 = 2 ^ 0`, `s = 0 < k = 1`)
   that downloads `D 0` in the online phase is perfectly correct (`IsCorrectWith 1`), perfectly
   private, and vacuously perfectly data private (since `D₀ ∘ Q = D₁ ∘ Q` forces `D₀ = D₁` when
   `n = k = 1`), showing that `2 ≤ n` cannot be dropped from `Scheme.eval_onlineTranscript_eq`,
   `Scheme.correct_le_card_div_two_pow`, or `Scheme.batchSPIR_limitation`.
3. **Concrete execution and repeated-query counterexample for `toyScheme`**: concrete evaluation of
   `query`, `answer`, and `reconstruct` on a `3`-bit database and `2`-query batch, concrete
   instantiation of `not_exists_scheme_of_lt` (`s = 1 < k = 2 ≤ n = 4`), and the `n = k = 2`
   counterexample `¬ (toyScheme 2 2).IsPerfectlyPrivate`.
-/

public section

namespace CslibTests.Crypto.Protocols.PIR.Symmetric.Preprocessing

open Cslib
open Cslib.Crypto.Protocols.PIR.Symmetric.Preprocessing

/-! ### 1. Joint satisfiability at `n = 2, k = 1` -/

/-- At `n = 2`, the client state of `toyScheme 2 1` has `2 ^ 2 * 2! = 8` elements. -/
example : Fintype.card (ToyState 2) = 8 := by
  rw [card_toyState]
  decide

/-- `toyScheme 2 1` satisfies all three hypotheses of the core theorem simultaneously:
`IsCorrectWith 1`, `IsPerfectlyPrivate`, and `IsPerfectlyDataPrivate`. -/
example :
    (toyScheme 2 1).IsCorrectWith 1 ∧
      (toyScheme 2 1).IsPerfectlyPrivate ∧
      (toyScheme 2 1).IsPerfectlyDataPrivate :=
  ⟨toyScheme_isCorrectWith_one 2 1,
    toyScheme_isPerfectlyPrivate_of_le_one (by decide),
    toyScheme_isPerfectlyDataPrivate 2 1⟩

/-- Instantiating `Scheme.correct_le_card_div_two_pow` and `Scheme.two_pow_le_card_state` on
`toyScheme 2 1` yields the concrete bounds `1 ≤ 8 / 2` and `2 ≤ 8`. -/
example : (1 : ℝ) ≤ (Fintype.card (ToyState 2) : ℝ) / 2 ^ 1 ∧ 2 ^ 1 ≤ Fintype.card (ToyState 2) :=
  ⟨(toyScheme 2 1).correct_le_card_div_two_pow (by decide) (by decide)
      (toyScheme_isPerfectlyPrivate_of_le_one (by decide))
      (toyScheme_isPerfectlyDataPrivate 2 1)
      (toyScheme_isCorrectWith_one 2 1),
    (toyScheme 2 1).two_pow_le_card_state (by decide) (by decide)
      (toyScheme_isPerfectlyPrivate_of_le_one (by decide))
      (toyScheme_isPerfectlyDataPrivate 2 1)
      (toyScheme_isCorrect 2 1)⟩

/-! ### 2. Necessity of `2 ≤ n` (`n = k = 1`, `s = 0` counterexample to unguarded Theorem 6.2) -/

/-- At `n = k = 1`, a zero-storage scheme (`St = Unit`, `s = 0`) that sends `D 0` as the online
download message. -/
def downloadOneBitScheme : Scheme 1 1 Unit Unit Unit Unit Bool where
  rLaw := pure ()
  setup _ _ := pure ((), ())
  query _ _ := ()
  answer D _ _ := D 0
  reconstruct _ _ b := fun _ => b

theorem downloadOneBitScheme_isCorrect : downloadOneBitScheme.IsCorrect := by
  intro D Q
  have hQ : (fun _ : Fin 1 => D 0) = D ∘ Q := by
    funext j
    fin_cases j
    have h0 : Q 0 = 0 := Subsingleton.elim _ _
    simp [h0]
  simp [Scheme.run, Scheme.runAt, downloadOneBitScheme, hQ]

theorem downloadOneBitScheme_isPerfectlyPrivate : downloadOneBitScheme.IsPerfectlyPrivate := by
  intro D Q₀ Q₁
  rfl

theorem downloadOneBitScheme_isPerfectlyDataPrivate :
    downloadOneBitScheme.IsPerfectlyDataPrivate := by
  intro D₀ D₁ Q hD
  have hQ0 : Q 0 = 0 := Subsingleton.elim _ _
  have hD0 : D₀ 0 = D₁ 0 := by
    have h := congrFun hD 0
    simpa [Function.comp_apply, hQ0] using h
  simp [Scheme.clientView, Scheme.clientViewAt, downloadOneBitScheme, hD0]

/-- At `n = k = 1` and `s = 0` (`s < k ≤ n`), `downloadOneBitScheme` has `Fintype.card Unit ≤ 2 ^ 0`
and achieves `IsCorrectWith 1`, `IsPerfectlyPrivate`, and `IsPerfectlyDataPrivate` simultaneously,
confirming that `2 ≤ n` is needed in `Scheme.batchSPIR_limitation` (Theorem 6.2). -/
example :
    Fintype.card Unit ≤ 2 ^ 0 ∧
      downloadOneBitScheme.IsCorrectWith 1 ∧
      downloadOneBitScheme.IsPerfectlyPrivate ∧
      downloadOneBitScheme.IsPerfectlyDataPrivate :=
  ⟨by decide,
    downloadOneBitScheme_isCorrect.isCorrectWith_one,
    downloadOneBitScheme_isPerfectlyPrivate,
    downloadOneBitScheme_isPerfectlyDataPrivate⟩

/-! ### 3. Concrete execution, impossibility instance, and repeated-query counterexample -/

/-- Concrete online execution of `toyScheme 3 2` on database `D = ![true, false, true]`,
server mask `r = ![false, true, true]`, permutation `π = Equiv.swap 0 2`, and batch query
`Q = ![2, 0]`: reconstruction recovers `D ∘ Q = ![true, true]`. -/
example :
    let D : Fin 3 → Bool := ![true, false, true]
    let r : Fin 3 → Bool := ![false, true, true]
    let π : Equiv.Perm (Fin 3) := Equiv.swap 0 2
    let st : ToyState 3 := (fun i => xor (D i) (r (π i)), π)
    let Q : Fin 2 → Fin 3 := ![2, 0]
    let τu := (toyScheme 3 2).query st Q
    let τd := (toyScheme 3 2).answer D r τu
    (toyScheme 3 2).reconstruct st Q τd = D ∘ Q := by
  decide

/-- Concrete instantiation of `not_exists_scheme_of_lt` (Theorem 6.2): on a `4`-bit database
(`n = 4`) with `1`-bit client storage (`St = Bool`, `s = 1`) and batch size `k = 2`, no scheme
can achieve correctness `3 / 4 > 1 - 2 ^ (1 - 2) = 1 / 2` together with perfect privacy and
perfect data privacy. -/
example {R Toff Tu Td : Type} :
    ¬ ∃ P : Scheme 4 2 R Bool Toff Tu Td,
      P.IsCorrectWith (3 / 4) ∧ P.IsPerfectlyPrivate ∧ P.IsPerfectlyDataPrivate :=
  not_exists_scheme_of_lt (s := 1) (by decide) (by decide) (by decide) (by decide) (by norm_num)

/-- Concrete repeated-query counterexample at `n = 2, k = 2`: `toyScheme 2 2` is private on
injective batch tuples, but not over all batch tuples with repeats allowed. -/
example :
    (toyScheme 2 2).IsPerfectlyPrivateOn {Q | Function.Injective Q} ∧
      ¬ (toyScheme 2 2).IsPerfectlyPrivate :=
  ⟨toyScheme_isPerfectlyPrivateOn_injective 2 2,
    toyScheme_not_isPerfectlyPrivate (by decide) (by decide)⟩

end CslibTests.Crypto.Protocols.PIR.Symmetric.Preprocessing
