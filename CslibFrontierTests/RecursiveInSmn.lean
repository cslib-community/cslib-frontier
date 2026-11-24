/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module

public import CslibFrontier.Foundations.Computability.RecursiveInSmn

/-! Clients of the oracle-uniform s-m-n API under module encapsulation. A two-argument oracle
program `⟨m, n⟩ ↦ ⟨g m, n⟩` is specialized at `m = 3`. The specialized code queries the oracle: it
gives different outputs under two total oracles and diverges under the empty partial oracle, so
the uniformity in the oracle is not vacuous. The index-level s-m-n theorem then specializes the
same program through its Gödel number. -/

public section

namespace CslibFrontierTests.RecursiveInSmn

open Encodable Denumerable Nat.RecursiveIn.Code

/-- The two-argument oracle program `⟨m, n⟩ ↦ ⟨g m, n⟩`. -/
def queryFirst : Nat.RecursiveIn.Code := pair (comp oracle left) right

/-- Relative to every oracle, the specialization at `m` maps `n` to `⟨g m, n⟩`. -/
theorem eval_curry_queryFirst (g : ℕ →. ℕ) (m n : ℕ) :
    eval g (curry queryFirst m) n = (g m).map (Nat.pair · n) := by
  have h : (Part.some m >>= g) = g m := Part.bind_some m g
  rw [eval_curry]
  simp [queryFirst, eval, Seq.seq, Part.bind_some_eq_map, h, Part.map_map, Function.comp_def]

-- Under the squaring oracle, the specialized program sends `5` to `⟨9, 5⟩`.
example : eval (fun x : ℕ => x * x : ℕ → ℕ) (curry queryFirst 3) 5 = Part.some (Nat.pair 9 5) := by
  rw [eval_curry_queryFirst]; rfl

-- The same specialized code gives `⟨3, 5⟩` under the identity oracle: its output depends on the
-- oracle, so the oracle-independent specialization is not a constant computation.
example : eval (fun x : ℕ => x : ℕ → ℕ) (curry queryFirst 3) 5 = Part.some (Nat.pair 3 5) := by
  rw [eval_curry_queryFirst]; rfl

example : eval (fun x : ℕ => x * x : ℕ → ℕ) (curry queryFirst 3) 5 ≠
    eval (fun x : ℕ => x : ℕ → ℕ) (curry queryFirst 3) 5 := by
  rw [eval_curry_queryFirst, eval_curry_queryFirst]
  simp [Nat.pair]

-- Under the nowhere-defined oracle the specialized program diverges.
example : ¬(eval (fun _ => Part.none : ℕ →. ℕ) (curry queryFirst 3) 5).Dom := by
  have h (g : ℕ →. ℕ) (hg : ¬(g 3).Dom) : ¬(eval g (curry queryFirst 3) 5).Dom := by
    rw [eval_curry_queryFirst]
    simpa using hg
  exact h _ (by simp)

-- Specialization is a primitive recursive operation on codes.
example : Primrec fun m => curry queryFirst m :=
  primrec₂_curry.comp (Primrec.const (α := ℕ) queryFirst) Primrec.id

-- The index-level s-m-n map specializes the Gödel number of `queryFirst`, for every oracle.
example : ∃ s : ℕ → ℕ → ℕ, Primrec₂ s ∧ ∀ (g : ℕ →. ℕ) (m n : ℕ),
    eval g (ofNat Nat.RecursiveIn.Code (s (encode queryFirst) m)) n = (g m).map (Nat.pair · n) := by
  obtain ⟨s, hs, hsmn⟩ := exists_primrec₂_smn
  refine ⟨s, hs, fun g m n => ?_⟩
  rw [hsmn, ofNat_encode, ← eval_curry, eval_curry_queryFirst]

end CslibFrontierTests.RecursiveInSmn
