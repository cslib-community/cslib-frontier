/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.GenQuery

/-!
# The bit evaluator at one parameter

`SumProduct.gen_decidable` packages Proposition 3.2 for a generated recursion as a decision
procedure, with the input length as the only parameter of the programs. The counting theorem needs
the evaluator inside a larger program, at a parameter `n` that packs the size, the bit index, the
precision and the schedule. `GenProg.main_spec` is the evaluator at one input `w` and one
parameter `n`: the term `mainT G.queries rootP XP`, run on `[n]`, returns bit `k₀` of the value
of the generated recursion, with all values below `2^(X+1)`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NatList SPTree

namespace GenProg

/-- **Proposition 3.2 for a generated recursion, at one input and one parameter.** -/
theorem main_spec (G : GenProg) (w : List Bool) (n k0 ℓ V X : ℕ) {rootP XP : Prog}
    (hroot : Prog'.closed 1 rootP = true) (hXP : Prog'.closed 1 XP = true)
    (hℓ : 1 ≤ ℓ) (hprec : (G.tree w n).PrecLe (2 ^ ℓ))
    (hV : ∀ π, Valid (G.tree w n) π → (node (G.tree w n) π).prec + (node (G.tree w n) π).param ≤ V)
    (hk0V : k0 ≤ V) (hXcost : 34 * (G.tree w n).cost ℓ + 2 * V.size + 16 ≤ X)
    (hrootv : rootP.eval w [n] = k0 ∧ rootP.Bounded w (2 ^ (X + 1)) [n])
    (hXv : XP.eval w [n] = X ∧ XP.Bounded w (2 ^ (X + 1)) [n])
    (hpath : ∀ π, Valid (G.tree w n) π → G.PathBounded (w := w) n (2 ^ (X + 1)) π)
    (hbit : ∀ π k, Valid (G.tree w n) π → (node (G.tree w n) π).tag = 0 →
      k < (node (G.tree w n) π).prec →
      G.bit.Bounded w (2 ^ (X + 1)) [k, (G.toFun w n).stateAt (G.init₀ w n) π, n]) :
    (mainT G.queries rootP XP).denote w [n] = ((G.tree w n).value.testBit k0).toNat ∧
      (mainT G.queries rootP XP).Bnd w (2 ^ (X + 1)) [n] := by
  have h16 : 16 ≤ X := by omega
  have h4 : 4 ≤ 2 ^ (X + 1) :=
    calc 4 = 2 ^ 2 := rfl
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine RunHyp.main_spec ⟨hℓ, hprec, hV, hk0V, hXcost, fun π hπ => ?_, fun π k hπ ht hk => ?_⟩
    hroot hXP hrootv hXv
  · have hag := (GenFun.agrees_tree _ (G.fuel₀ w n) (G.init₀ w n) π hπ).1
    rw [List.append_nil] at hag
    have hp := hpath π hπ
    refine ⟨?_, ?_, ?_, G.bnd_queries_tag hp h4, G.bnd_queries_prec hp h4,
      G.bnd_queries_param hp h4⟩
    · rw [G.queries_tag, hag]; rfl
    · rw [G.queries_prec, hag]; rfl
    · rw [G.queries_param, hag]; rfl
  · have hag := (GenFun.agrees_tree _ (G.fuel₀ w n) (G.init₀ w n) π hπ).2 k ht hk
    rw [List.append_nil] at hag
    refine ⟨?_, G.bnd_queries_bit (hpath π hπ) (hbit π k hπ ht hk)⟩
    rw [G.queries_bit, hag]
    rfl

end GenProg

end Cslib.Complexity.NtimeDspace.SumProduct
