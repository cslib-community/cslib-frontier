/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cutting.ComputationPieces
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cutting.OneCut
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Cutting.Pieces
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Laws.Existence
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.TwoCases.Cube

/-! Tests of the pieces of thin trees, the pieces of a computation (Proposition J.2) and the cuts
(Theorems J.3 and J.4), as a client that sees only the public statements.

* Over `ℚ`, by Theorem D.2 and Theorem G.2: the flat case holds, or the one-state automaton with
  weight `1` and the one-bit code of its symbols has pieces of its computation (Proposition J.2);
  the flat case holds, or there are a ring, a table of generators and the cut hypothesis
  (Theorem J.4), with both properties of the table.
* For thin trees: the bounds of a piece for the cut by `2`, and the program of the pieces: its
  length, that it accepts the numbers of initial units `0`, and that it accepts only numbers within
  the load.
* For the pieces of a computation: the number of units with one holder in a piece, as a
  quotient. -/

set_option linter.privateModule false

namespace CslibFrontierTests.SeparationCutting

open Finset Cslib Cslib.Circuits.Arithmetic.Separation Cslib.Circuits.Arithmetic.Separation.Cut
  Cslib.Circuits.Arithmetic.Separation.Trees Cslib.Circuits.Arithmetic.Separation.TwoCases
  Cslib.Circuits.Arithmetic.Separation.Interpreter

/-! ### Closed examples over `ℚ` -/

/-- The code of the symbols `none` and `some ()` by one bit. -/
private def unitCode : Option Unit → BitString 1 := fun z _ => z.isSome

private theorem unitCode_injective : Function.Injective unitCode := by
  rintro (_ | _) (_ | _) h
  all_goals first | rfl | exact absurd (congrFun h 0) (by simp [unitCode])

/-- **Proposition J.2 over `ℚ`**: the flat case holds, or for the laws of Theorem G.2 over a
subring `A` of `ℚ` there are `a` and `e ≥ 300` such that the one-state automaton with weight `1`
and the one-bit code of its symbols has, for all large `v`, `K = v ^ e` blocks of `T ≥ v ^ a` steps
and `2 ≤ k ≤ v ^ 64`, pieces of its computation. -/
example : FlatCase ℚ ∨ ∃ (A : Subring ℚ) (laws : List (Cut.Law A)) (b G a e : ℕ), 300 ≤ e ∧
    ∃ C v₀ : ℕ, ∀ v, v₀ ≤ v → ∃ K, v ^ e ≤ K ∧ K ≤ C * v ^ e ∧ ∀ T k, v ^ a ≤ T → 2 ≤ k →
      k ≤ v ^ 64 → Nonempty (Cutting.ComputationPieces laws
        (fun _ : Tape.Letter Unit Unit Unit => (1 : Matrix Unit Unit A)) unitCode b G v K T k
          C) := by
  refine (flatCase_or_contractingCase ℚ).imp_right fun hK => ?_
  obtain ⟨h, _, h3, A, -, FL, hC, -⟩ := Laws.exists_vertexLaws hK
  obtain ⟨a, e, he, hP⟩ := Cutting.exists_computationPieces h3 FL hC
  exact ⟨A, _, _, _, a, e, he, hP A Unit Unit Unit _ unitCode unitCode_injective one_pos⟩

/-- **Theorem J.4 over `ℚ`**: the flat case holds, or there are a finitely generated subring `A`
of `ℚ`, a table `θ` of finite support whose formulas give every element of `A`, and `h ≥ 17` with
the cut hypothesis at the scales `v ^ H`, `H = 16 h`. -/
example : FlatCase ℚ ∨ ∃ (A : Subring ℚ) (θ : List Bool → A) (h C₀ v₀ : ℕ),
    Algebra.FiniteType ℤ A ∧ (Function.support θ).Finite ∧ (∀ a, ∃ w : WE, w.val θ = a) ∧
      17 ≤ h ∧ CutHyp θ (16 * h) C₀ v₀ := by
  refine (flatCase_or_contractingCase ℚ).imp_right fun hK => ?_
  obtain ⟨A, hA, θ, h, C₀, v₀, hfin, hgen, hh, hcut⟩ := Cutting.exists_cutHyp hK
  exact ⟨A, θ, h, C₀, v₀, hA, hfin, hgen, hh, hcut⟩

/-! ### Thin trees under hypotheses -/

section ThinTrees

variable {R : Type} [CommSemiring R] {laws : List (Cut.Law R)} {K N ℓ M b G C : ℕ} {γ : ℝ}

/-- **The bounds of a piece** for the cut by `2`: for good outcomes and at most `N` initial units
at every base party, a piece has at most `2 (K + K)` base parties, and its units with exactly one
holder, with the gain `w`, are at most `Y + M ^ C w`. -/
example (TT : ThinTrees laws (K + K) N ℓ M b G C γ) (hK : 0 < K) (hM : 0 < M)
    {n : Fin (K + K) → Fin (K + K) → Fin (N + 1)} {o : TT.moves.Channel → Fin TT.U1}
    (hn : ∀ a, ∑ c, ((n a c : ℕ) + n c a) ≤ N) (hg : ∀ x, TT.plan.Good n o x) {w : ℕ}
    (hw : ∀ X : ℕ, (X : ℝ) ≤ (lg M ^ C : ℕ) * (M : ℝ) ^ (1 - γ) * (N + (M : ℝ) ^ 2) →
      X * w ≤ lg M ^ C * M * (N + M ^ 2)) (g : Fin (TT.pieceCount 2)) :
    #{p : Fin (K + K) | TT.piece two_pos n o (Fin.castAdd TT.A' p) = g} ≤ 2 * (K + K) ∧
      #((TT.plan.cur n o TT.E).filter (Dealing.OneIn (UnitId.holder TT.moves.channelParty)
        (TT.piece two_pos n o) g)) * w ≤ lg M ^ C * M * (N + M ^ 2) + M ^ C * w := by
  refine ⟨?_, TT.card_oneIn_piece_le two_pos hn hg hw g⟩
  have := TT.card_base_piece_le (n := n) (o := o) two_pos (by omega) hM g
  omega

/-- **The program of the pieces** has at most `Y ^ 15` steps, accepts the numbers of initial units
`0`, and accepts only numbers with at most `N` units at every base party. -/
example (TT : ThinTrees laws (K + K) N ℓ M b G C γ) {k Y : ℕ} (hk : 0 < k) (hY : 6 ≤ Y)
    (hMN : (M * N) ^ C ≤ Y) (hN : N ≤ Y) (hdepth : TT.depth ≤ Y)
    (hin : (K + K) * (K + K) + Fintype.card TT.moves.Channel ≤ Y) :
    ∃ (nI pS : ℕ) (tab : Dealing.SlpTab TT.plan (fun x => TT.piece hk x.counts x.outcomes)
      (Y ^ 4) nI pS), pS ≤ Y ^ 15 ∧ tab.Valid (fun _ _ => 0) ∧
        ∀ n, tab.Valid n → ∀ p, ∑ a, ((n p a : ℕ) + n a p) ≤ N := by
  obtain ⟨nI, pS, tab, hpS, hvalid⟩ := TT.exists_slpTab hk hY hMN hN hdepth hin
  exact ⟨nI, pS, tab, hpS, (hvalid _).2 fun p => by simp, fun n hn => (hvalid n).1 hn⟩

end ThinTrees

section Pieces

variable {R : Type} [CommRing R] {laws : List (Cut.Law R)} {Γ S Q : Type} [Fintype Γ]
  [DecidableEq Γ] [Fintype S] [DecidableEq S] [Fintype Q] [DecidableEq Q]
  {mu : Tape.Letter S Unit Γ → Matrix Q Q R} {c : ℕ} {cb : Option Γ → BitString c}
  {b G v K T k C : ℕ}

/-- **The cut units of a piece of a computation** (Proposition J.2): for valid numbers of initial
units and good outcomes, a piece has at most `K T Λ / (ub v ^ 300)` units with exactly one holder
in it, `Λ = lg v ^ C`, at a scale `v > 0`. -/
example (pc : Cutting.ComputationPieces laws mu cb b G v K T k C) (hv : 0 < v)
    {n : Fin (K + K) → Fin (K + K) → Fin (pc.load + 1)} {o : pc.moves.Channel → Fin pc.U1}
    (hn : pc.program.Valid n) (hg : ∀ x, pc.plan.Good n o x) (g : Fin pc.num) :
    #((pc.plan.cur n o pc.E).filter (Dealing.OneIn (UnitId.holder pc.moves.channelParty)
      (pc.piece ⟨n, o⟩) g)) ≤ K * T * lg v ^ C / (pc.ub * v ^ 300) := by
  rw [Nat.le_div_iff_mul_le (Nat.mul_pos pc.ub_pos (pow_pos hv 300)), ← Nat.mul_assoc]
  exact pc.card_oneIn_le n o hn hg g

end Pieces

end CslibFrontierTests.SeparationCutting
