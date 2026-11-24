/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.InnerLoopTerm
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ParserTerm

/-!
# Arithmetic helper terms

Terms for `Nat.clog 2`, ceiling division and primality by trial division. Powers of a loop
variable are avoided: `2^i < m` is tested as `0 < (m-1)/2^i` by repeated
division (`divPowT`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgTerm

open Term

variable {w : List Bool}

/-! ### `clog 2` -/

/-- `Nat.clog 2 m` for `1 ≤ m`: the number of `i < m` with `2^i < m`. -/
def clogT (m : Term) : Term :=
  sumT m fun i => lt (const 0) (divPowT (const 2) (sub m (const 1)) i)

theorem lt_clog_iff {m i : ℕ} : 2 ^ i < m ↔ i < Nat.clog 2 m := by
  rw [← not_le, ← not_le, Nat.clog_le_iff_le_pow (by norm_num)]

theorem clog_le_self (m : ℕ) : Nat.clog 2 m ≤ m := by
  rcases Nat.lt_or_ge (Nat.clog 2 m) (m + 1) with h | h
  · by_contra hc
    push Not at hc
    have := lt_clog_iff.mpr hc
    have : m < 2 ^ m := Nat.lt_two_pow_self
    omega
  · have : 2 ^ m < m := lt_clog_iff.mpr (by omega)
    have : m < 2 ^ m := Nat.lt_two_pow_self
    omega

theorem denote_clogT {m : Term} {env : List ℕ} (hm : StableAt w m env) (hpos : 1 ≤ m.denote w env) :
    (clogT m).denote w env = Nat.clog 2 (m.denote w env) := by
  rw [clogT, denote_sumT _ _ env (fun i => if i < Nat.clog 2 (m.denote w env) then 1 else 0)
    (fun acc i => ?_), sum_lt_indicator, min_eq_right (clog_le_self _)]
  simp only [denote_lt, denote_const, divPowT_denote _ _ _ _ (stableAt_const _ _), denote_sub,
    hm.cons₂, denote_lvl_index]
  by_cases h : i < Nat.clog 2 (m.denote w env)
  · have := lt_clog_iff.mpr h
    rw [ite_eq_left h, ite_eq_left (Nat.div_pos_iff.mpr ⟨by positivity, by omega⟩)]
  · have : ¬ 2 ^ i < m.denote w env := fun h' => h (lt_clog_iff.mp h')
    rw [ite_eq_right h, ite_eq_right (by rw [Nat.div_pos_iff]; omega)]

theorem StableAt.clogT {m : Term} {env : List ℕ} (hm : StableAt w m env)
    (hpos : 1 ≤ m.denote w env) : StableAt w (clogT m) env := fun extra => by
  rw [denote_clogT (hm.extend extra) (by rw [hm extra]; exact hpos), denote_clogT hm hpos, hm extra]

/-! ### Ceiling division and maximum -/

/-- The term computing the ceiling division `⌈a / b⌉`, as `(a + b - 1) / b`. -/
def ceilDivT (a b : Term) : Term := div (sub (add a b) (const 1)) b

theorem denote_ceilDivT (a b : Term) (env : List ℕ) :
    (ceilDivT a b).denote w env = (a.denote w env + b.denote w env - 1) / b.denote w env := by
  simp [ceilDivT]

/-- `1` if `p` is prime: `2 ≤ p` and no `d` with `2 ≤ d < p` divides `p`. -/
def primeT (p : Term) : Term :=
  mul (lt (const 1) p) (allT (sub p (const 2)) fun d => lt (const 0) (mod p (add d (const 2))))

theorem prime_iff_no_small_divisor {p : ℕ} (h2 : 1 < p) :
    (∀ d < p - 2, ¬ (d + 2) ∣ p) ↔ p.Prime := by
  rw [Nat.prime_def_lt]
  constructor
  · intro h
    refine ⟨h2, fun m hm hdvd => ?_⟩
    rcases m with _ | _ | m
    · rw [Nat.zero_dvd] at hdvd; omega
    · rfl
    · exact absurd hdvd (h m (by omega))
  · rintro ⟨_, h⟩ d hd hdvd
    have := h (d + 2) (by omega) hdvd
    omega

theorem denote_primeT {p : Term} {env : List ℕ} (hp : StableAt w p env) :
    (primeT p).denote w env = if (p.denote w env).Prime then 1 else 0 := by
  rw [primeT, denote_mul, denote_lt, denote_const,
    allT_denote _ _ env (fun d => ¬ (d + 2) ∣ p.denote w env) (fun acc d => by
      simp only [denote_lt, denote_const, denote_mod, denote_add, denote_lvl_index, hp.cons₂]
      by_cases h : (d + 2) ∣ p.denote w env
      · rw [ite_eq_right (by rw [Nat.mod_eq_zero_of_dvd h]; omega), ite_eq_right (not_not.mpr h)]
      · rw [ite_eq_left (Nat.pos_of_ne_zero (fun h0 => h (Nat.dvd_of_mod_eq_zero h0))),
          ite_eq_left h])]
  by_cases h2 : 1 < p.denote w env
  · rw [ite_eq_left h2, one_mul]
    by_cases hq : (p.denote w env).Prime
    · rw [ite_eq_left hq]
      exact ite_eq_left ((prime_iff_no_small_divisor h2).mpr hq)
    · rw [ite_eq_right hq]
      exact ite_eq_right (fun hall => hq ((prime_iff_no_small_divisor h2).mp hall))
  · rw [ite_eq_right h2, zero_mul, ite_eq_right (fun hq => h2 hq.one_lt)]

end Cslib.Complexity.NtimeDspace.ProgTerm
