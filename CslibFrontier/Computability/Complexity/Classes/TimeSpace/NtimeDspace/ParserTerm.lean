/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.WeightTerm

/-!
# The support parser as a term

`stepT` mirrors `ParserFold.stepNat` on packed states, and `scanT` folds it over
the bits of a candidate number. With `PackedParser` and `ParserFold.scan_eq_fold`
its meaning is the packed result of `BoundedSupportParser.scan` on the
candidate's word.
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

def packT (M t c r f z a : Term) : Term :=
  add t (mul (const 4) (add c (mul M (add r (mul M (add f (mul M (add z (mul M a)))))))))

def finishT (B Cap q M c r f gap : Term) : Term :=
  ite (mul (mul (lt (const 0) gap) (leT gap (sub B c))) (lt r Cap))
    (packT M (const 1) (add c gap) (add r (const 1))
      (ite (add (eqT f (const 1)) (eqT (add c gap) q)) (const 1) (const 0)) (const 0) (const 0))
    (const 0)

def prefixT (B Cap Lb q M c r f z b : Term) : Term :=
  ite (eqT b (const 0))
    (ite (lt z Lb) (packT M (const 2) c r f (add z (const 1)) (const 0)) (const 0))
    (ite (lt (const 0) B)
      (ite (eqT z (const 0)) (finishT B Cap q M c r f (const 1))
        (packT M (const 3) c r f z (const 1)))
      (const 0))

def payloadT (B Cap q M c r f z a b : Term) : Term :=
  ite (mul (leT b B) (leT a (div (sub B b) (const 2))))
    (ite (eqT (sub z (const 1)) (const 0))
      (finishT B Cap q M c r f (add (mul (const 2) a) b))
      (packT M (const 3) c r f (sub z (const 1)) (add (mul (const 2) a) b)))
    (const 0)

/-- The packed transition. -/
def stepT (B Cap Lb q M x b : Term) : Term :=
  ite (eqT (mod x (const 4)) (const 1))
    (ite (lt (mod (div (div x (const 4)) M) M) Cap)
      (prefixT B Cap Lb q M (mod (div x (const 4)) M) (mod (div (div x (const 4)) M) M)
        (mod (div (div (div x (const 4)) M) M) M) (const 0) b)
      (const 0))
    (ite (eqT (mod x (const 4)) (const 2))
      (prefixT B Cap Lb q M (mod (div x (const 4)) M) (mod (div (div x (const 4)) M) M)
        (mod (div (div (div x (const 4)) M) M) M)
        (mod (div (div (div (div x (const 4)) M) M) M) M) b)
      (ite (eqT (mod x (const 4)) (const 3))
        (payloadT B Cap q M (mod (div x (const 4)) M) (mod (div (div x (const 4)) M) M)
          (mod (div (div (div x (const 4)) M) M) M)
          (mod (div (div (div (div x (const 4)) M) M) M) M)
          (div (div (div (div (div x (const 4)) M) M) M) M) b)
        (const 0)))

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

/-- The parser over the word of candidate `c`. -/
def scanT (B Cap Lb q M K c : Term) : Term :=
  foldT (log2T K c) (const 1) fun acc j => stepT B Cap Lb q M acc (bit c j)

/-- Validity of a packed final state. -/
def validT (x : Term) : Term := eqT (mod x (const 4)) (const 1)
/-- The membership register of a packed final state. -/
def foundT (M x : Term) : Term := mod (div (div (div x (const 4)) M) M) M
/-- The rank register of a packed final state. -/
def rankT (M x : Term) : Term := mod (div (div x (const 4)) M) M

end Cslib.Complexity.NtimeDspace.ProgTerm
