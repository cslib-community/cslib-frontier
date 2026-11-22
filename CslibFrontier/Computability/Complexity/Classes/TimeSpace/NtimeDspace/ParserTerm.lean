/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.WeightTerm

/-!
# Comparison and the binary logarithm as terms

`leT a b` is `1` when `a ≤ b` and `0` otherwise (`denote_leT`), and `log2T K c` computes
`Nat.log2 c` for `1 ≤ c < 2 ^ (K + 1)` by counting the `i < K` with `2 ^ (i + 1) ≤ c`
(`log2T_denote`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

@[simp] theorem zero_lt_ite_one (P : Prop) [Decidable P] :
    (0 < if P then (1 : ℕ) else 0) ↔ P := by
  split_ifs <;> simp_all

/-- `1` if `a ≤ b`. -/
def leT (a b : Term) : Term := sub (const 1) (lt b a)

@[simp] theorem denote_leT (a b : Term) (env : List ℕ) :
    (leT a b).denote w env = if a.denote w env ≤ b.denote w env then 1 else 0 := by
  simp only [leT, denote_sub, denote_const, denote_lt]
  split_ifs <;> omega

/-- `log₂ c` for `1 ≤ c < 2^(K+1)`: the number of `i < K` with `2^(i+1) ≤ c`. -/
def log2T (K c : Term) : Term :=
  sumT K fun i => lt (const 0) (divPowT (const 2) c (add i (const 1)))

theorem sum_lt_indicator (K L : ℕ) :
    ∑ i ∈ Finset.range K, (if i < L then 1 else 0) = min K L := by
  induction K with
  | zero => simp
  | succ K ih => rw [Finset.sum_range_succ, ih]; split_ifs <;> omega

theorem log2T_denote (K c : Term) (env : List ℕ) (hc : StableAt w c env)
    (hpos : 1 ≤ c.denote w env) (hlt : c.denote w env < 2 ^ (K.denote w env + 1)) :
    (log2T K c).denote w env = (c.denote w env).log2 := by
  rw [log2T, denote_sumT _ _ env (fun i => if i < (c.denote w env).log2 then 1 else 0)
    (fun acc i => ?_), sum_lt_indicator]
  · have : (c.denote w env).log2 < K.denote w env + 1 :=
      (Nat.log2_lt (by omega)).mpr hlt
    omega
  · simp only [denote_lt, divPowT_denote _ _ _ _ (stableAt_const _ _), denote_add,
      denote_lvl_index, denote_const, hc.cons₂]
    have hne : c.denote w env ≠ 0 := by omega
    by_cases h : i < (c.denote w env).log2
    · rw [ite_eq_left (Nat.div_pos_iff.mpr ⟨by positivity, (Nat.le_log2 hne).mp h⟩), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h ((Nat.le_log2 hne).mpr (Nat.div_pos_iff.mp h').2)), ite_eq_right
        h]

end Cslib.Complexity.NtimeDspace.ProgTerm
