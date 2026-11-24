/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.NetFamily
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.SqrtLogSublinear

/-!
# The statement of Theorem 2.3 in bit form

`CubeCounting` is the paper's Theorem 2.3 (`thm:counting`) in the program model of
`LogspaceNetFamily`: one closed program on `[s, |w|, j]` computes bit `j` of `Z(G)` for every `j`,
with every value of its evaluation at most `2^(C · SqrtLog s)`. The vertex functions of the family
take values in `{0, …, (s+2)^C}`, so `Z(G) ≥ 0` (`value_nonneg`) and `Z(G) < 2^E` for
`E = (C + 1)(s + 2)^(C + 2)` (`toNat_value_lt`).

The statement lives apart from its consequences (`CubeCounting.lean`) and its proof
(`CubeFinal.lean`), so that the proof does not import the consequences.

## Main definitions

* `CubeCounting`: Theorem 2.3 in bit form, for every family with logspace access.
* `CubeCounting.expE`: the exponent `E`.

## Main results

* `CubeCounting.value_nonneg`, `CubeCounting.value_le`, `CubeCounting.toNat_value_lt`.

## References

* The paper (`separating-ntime-from-space.tex`), §2, Definition 2.1 (`def:access`) and Theorem 2.3
(`thm:counting`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang Finset NtimeDspace.SumProduct

/-- **Theorem 2.3** (bit form): for every family of networks with logspace access, one closed
program over `[s, |w|, j]` computes bit `j` of `Z(G)` for every description `w` of a network `G` of
the
family
at size `s ≥ s₀`, with every value of its evaluation below `2^(C · SqrtLog s)`. -/
def CubeCounting : Prop :=
  ∀ F : LogspaceNetFamily, ∃ (Q : Prog) (C s₀ : ℕ), Prog'.closed 3 Q = true ∧
    ∀ (w : List Bool) (s j : ℕ), F.Mem w s → s₀ ≤ s →
      Q.eval w [s, w.length, j] = (F.net w s).value.toNat / 2 ^ j % 2 ∧
        Q.Bounded w (2 ^ (C * SqrtLog s)) [s, w.length, j]

namespace CubeCounting

/-! ### The value of a network of the family -/

section Value

variable (F : LogspaceNetFamily) {w : List Bool} {s : ℕ}

/-- `Z(G) ≥ 0`: the vertex functions are nonnegative. -/
theorem value_nonneg (hm : F.Mem w s) : 0 ≤ (F.net w s).value :=
  sum_nonneg fun _ _ => prod_nonneg fun v _ => (F.eval_mem w s hm v _ (by simp)).1

/-- `Z(G) ≤ 2^M · ((s + 2)^C)^V`. -/
theorem value_le (hm : F.Mem w s) :
    (F.net w s).value ≤ ((2 ^ (F.net w s).M * ((s + 2) ^ F.C) ^ F.V w s : ℕ) : ℤ) := by
  unfold EdgeNet.value
  calc _ ≤ ∑ _x : Fin (F.net w s).M → Bool, (((s + 2) ^ F.C : ℕ) : ℤ) ^ F.V w s :=
        sum_le_sum fun x _ => by
          calc _ ≤ ∏ _v : Fin (F.V w s), (((s + 2) ^ F.C : ℕ) : ℤ) :=
                Finset.prod_le_prod₀ (fun v _ => (F.eval_mem w s hm v _ (List.length_map _)).1)
                  fun v _ => (F.eval_mem w s hm v _ (List.length_map _)).2
            _ = _ := by simp
    _ = _ := by simp

/-- The exponent `E = (C + 1)(s + 2)^(C + 2)` with `Z(G) < 2^E`. -/
abbrev expE (C s : ℕ) : ℕ := (C + 1) * (s + 2) ^ (C + 2)

theorem exp_lt (C s : ℕ) : C * (s + 1) + (s + 2) * C * (s + 2) ^ C < expE C s := by
  have hP : 1 ≤ (s + 2) ^ C := Nat.one_le_pow _ _ (by omega)
  have e : (s + 2) ^ (C + 2) = (s + 2) ^ C * (s + 2) * (s + 2) := by ring
  rw [expE, e]
  have f1 : C * (s + 2) ^ C * (s + 2) * 2 ≤ C * (s + 2) ^ C * (s + 2) * (s + 2) :=
    Nat.mul_le_mul_left _ (by omega)
  have f2 : C * (s + 2) ≤ C * (s + 2) ^ C * (s + 2) := by
    rw [mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ hP)
  have f3 : 1 ≤ (s + 2) ^ C * (s + 2) * (s + 2) :=
    Nat.mul_pos (Nat.mul_pos hP (by omega)) (by omega)
  nlinarith

/-- `Z(G) < 2^E`. -/
theorem toNat_value_lt (hm : F.Mem w s) : (F.net w s).value.toNat < 2 ^ expE F.C s := by
  have h1 : (F.net w s).value.toNat ≤ 2 ^ (F.net w s).M * ((s + 2) ^ F.C) ^ F.V w s :=
    Int.toNat_le.mpr (value_le F hm)
  have h2 : ((s + 2) ^ F.C) ^ F.V w s ≤ 2 ^ ((s + 2) * F.C * (s + 2) ^ F.C) := by
    calc ((s + 2) ^ F.C) ^ F.V w s ≤ ((2 ^ (s + 2)) ^ F.C) ^ F.V w s :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _) _
      _ = 2 ^ ((s + 2) * F.C * F.V w s) := by rw [← pow_mul, ← pow_mul, mul_assoc]
      _ ≤ _ := Nat.pow_le_pow_right (by omega)
          (Nat.mul_le_mul_left _ (F.verts_le w s hm))
  have h3 : 2 ^ (F.net w s).M ≤ 2 ^ (F.C * (s + 1)) :=
    Nat.pow_le_pow_right (by omega) (F.edges_le w s hm)
  calc _ ≤ 2 ^ (F.C * (s + 1)) * 2 ^ ((s + 2) * F.C * (s + 2) ^ F.C) :=
        h1.trans (Nat.mul_le_mul h3 h2)
    _ = 2 ^ (F.C * (s + 1) + (s + 2) * F.C * (s + 2) ^ F.C) := by rw [pow_add]
    _ < _ := Nat.pow_lt_pow_right (by omega) (exp_lt F.C s)

end Value

end CubeCounting

end Cslib.Complexity.NtimeDspace.Cross
