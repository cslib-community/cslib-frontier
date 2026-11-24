/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ClockedInterface
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactProg

/-!
# The bits of an accept count at a clock

`ClockedBits` is the bit form of the accept count at an arbitrary clock: for every closed fair-coin
table `M` there is a program `P` over `[τ, n, j]` computing bit `j` of the accept count of `M` at
the padded time of the clock `τ`, in values below `2^(C·SqrtLog τ)`. It follows from the clocked
residues, a residue form of Theorem 2.3 (`clockedBits_of_clockedResidues`), by the Chinese
remainder step (`exists_bitsProg`) with the exponent `E = paddedTime τ` and the width
`W = SqrtLog τ`. The size condition of the elementary lemma holds for large clocks because
`log(window) = O(log τ)` and `E = O(τ)`, so the number of groups is polylogarithmic
(`sizes_eventually`).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset
  Cslib.Complexity Cslib.Complexity.CountingSimulation _root_.Turing

variable {w : List Bool} {env : List ℕ} {M : ℕ}

/-! ### `⌊√x⌋`, `SqrtLog` and the padded time as terms -/

/-- `⌊√x⌋`: the number of `r < x` with `(r+1)² ≤ x`. -/
def sqrtT' (x : Term) : Term :=
  sumT x fun r => lt (mul (add r (const 1)) (add r (const 1))) (add x (const 1))

theorem sum_sqrt (a : ℕ) :
    ∑ r ∈ range a, (if (r + 1) * (r + 1) < a + 1 then 1 else 0) = Nat.sqrt a := by
  have key : ∀ r, (r + 1) * (r + 1) < a + 1 ↔ r < Nat.sqrt a := fun r => by
    rw [Nat.lt_succ_iff, ← Nat.le_sqrt, Nat.succ_le_iff]
  simp only [key]
  rw [sum_boole]
  have : (range a).filter (· < Nat.sqrt a) = range (Nat.sqrt a) := by
    ext r; simp only [mem_filter, mem_range]; have := Nat.sqrt_le_self a; omega
  rw [this, card_range]; rfl

theorem val_sqrtT' {x : Term} {a : ℕ} (hx : Val w x env a) : Val w (sqrtT' x) env (Nat.sqrt a) := by
  have := val_sumT hx (body := fun r => lt (mul (add r (const 1)) (add r (const 1)))
    (add x (const 1))) (F := fun r => if (r + 1) * (r + 1) < a + 1 then 1 else 0)
    fun pre u b hu => val_lt (val_mul (val_add hu (val_const 1 _)) (val_add hu (val_const 1 _)))
      (val_add (hx.ext pre) (val_const 1 _))
  rwa [sum_sqrt] at this

theorem bd_sqrtT' {x : Term} {a : ℕ} (hx : Val w x env a) (hbx : Bd w M x env)
    (ha : (a + 1) * (a + 1) ≤ M) : Bd w M (sqrtT' x) env := by
  have ha1 : a + 1 ≤ M := le_trans (Nat.le_mul_of_pos_right _ (by omega)) ha
  refine bd_sumT hx (F := fun r => if (r + 1) * (r + 1) < a + 1 then 1 else 0)
    (fun pre u b hu => val_lt (val_mul (val_add hu (val_const 1 _)) (val_add hu (val_const 1 _)))
      (val_add (hx.ext pre) (val_const 1 _))) hbx (by omega) ?_ fun pre u b hb hu hbu => ?_
  · calc _ ≤ ∑ _r ∈ range a, 1 := sum_le_sum fun r _ => by split_ifs <;> omega
      _ ≤ M := by simp; omega
  · have h1 : b + 1 ≤ M := by omega
    refine bd_lt (bd_mul (bd_add hbu (bd_const (by omega) _) hu (val_const 1 _) h1)
      (bd_add hbu (bd_const (by omega) _) hu (val_const 1 _) h1) (val_add hu (val_const 1 _))
      (val_add hu (val_const 1 _)) (le_trans (Nat.mul_le_mul (by omega) (by omega)) ha))
      (bd_add (hbx.ext pre) (bd_const (by omega) _) (hx.ext pre) (val_const 1 _) ha1)

/-- `SqrtLog x = x / ⌊√⌊log₂ x⌋⌋ + 1`, for `x ≥ 1`. -/
def sqrtLogT' (x : Term) : Term := add (div x (sqrtT' (sub (bitLenT x) (const 1)))) (const 1)

theorem val_sqrtLogT' {x : Term} {a : ℕ} (hx : Val w x env a) (ha : 1 ≤ a) :
    Val w (sqrtLogT' x) env (SqrtLog a) := by
  have h := val_add (val_div hx (val_sqrtT' (val_sub (val_bitLenT hx ha) (val_const 1 env))))
    (val_const 1 env)
  have e : SqrtLog a = a / Nat.sqrt (Nat.log 2 a + 1 - 1) + 1 := by
    simp [SqrtLog, Nat.log2_eq_log_two]
  rw [e]; exact h

theorem bd_sqrtLogT' {x : Term} {a : ℕ} (hx : Val w x env a) (hbx : Bd w M x env) (ha : 1 ≤ a)
    (hM : (a + 2) * (a + 2) ≤ M) : Bd w M (sqrtLogT' x) env := by
  have ha2 : a + 2 ≤ M := le_trans (Nat.le_mul_of_pos_right _ (by omega)) hM
  have hl : Nat.log 2 a ≤ a := Nat.log_le_self 2 a
  refine bd_add (bd_div hbx (bd_sqrtT' (val_sub (val_bitLenT hx ha) (val_const 1 env))
    (bd_sub (bd_bitLenT hx hbx (by omega)) (bd_const (by omega) _)) ?_)) (bd_const (by omega) _)
    (val_div hx (val_sqrtT' (val_sub (val_bitLenT hx ha) (val_const 1 env)))) (val_const 1 env) ?_
  · exact le_trans (Nat.mul_le_mul (by omega) (by omega)) hM
  · have := Nat.div_le_self a (Nat.sqrt (Nat.log 2 a + 1 - 1)); omega

theorem clog_eq_log_add_one (t : ℕ) : Nat.clog 2 (t + 2) = Nat.log 2 (t + 1) + 1 := by
  refine le_antisymm ((Nat.clog_le_iff_le_pow (by norm_num)).mpr ?_) ?_
  · have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (t + 1); omega
  · by_contra h
    have h' : Nat.clog 2 (t + 2) ≤ Nat.log 2 (t + 1) := by omega
    have := (Nat.clog_le_iff_le_pow (by norm_num)).mp h'
    have := Nat.pow_log_le_self 2 (show t + 1 ≠ 0 by omega)
    omega

/-- The padded time `numBlocks t · blockLength t`. -/
def padT (x : Term) : Term :=
  letT (bitLenT (add x (const 1))) fun bl => mul (div (sub (add x bl) (const 1)) bl) bl

theorem val_padT {x : Term} {a : ℕ} (hx : Val w x env a) : Val w (padT x) env (paddedTime a) := by
  refine val_letT (val_bitLenT (val_add hx (val_const 1 env)) (by omega)) fun pre u hu => ?_
  have := val_mul (val_div (val_sub (val_add (hx.ext pre) hu) (val_const 1 _)) hu) hu
  refine fun extra => (this extra).trans ?_
  rw [paddedTime, numBlocks, blockLength, clog_eq_log_add_one, Nat.ceilDiv_eq_add_pred_div]

theorem bd_padT {x : Term} {a : ℕ} (hx : Val w x env a) (hbx : Bd w M x env) (ha : 2 ≤ a)
    (hM : 2 * a + 2 ≤ M) : Bd w M (padT x) env := by
  have hbl : Nat.log 2 (a + 1) + 1 ≤ a := by
    have := Nat.log_lt_self 2 (show a + 1 ≠ 0 by omega)
    have h2 : Nat.log 2 (a + 1) < a := by
      obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
      have : b + 3 < 2 ^ (b + 2) := by
        have := Nat.lt_two_pow_self (n := b)
        have : 2 ^ (b + 2) = 2 ^ b * 4 := by rw [pow_add]; rfl
        omega
      exact Nat.log_lt_of_lt_pow (by omega) this
    omega
  refine bd_letT (val_bitLenT (val_add hx (val_const 1 env)) (by omega))
    (bd_bitLenT (val_add hx (val_const 1 env)) (bd_add hbx (bd_const (by omega) _) hx
      (val_const 1 _) (by omega)) (by omega)) fun pre u hu hbu => ?_
  have hpad : paddedTime a + 1 ≤ 2 * a := paddedTime_add_one_le ha
  have hv := val_padT (w := w) hx
  refine bd_mul (bd_div (bd_sub (bd_add (hbx.ext pre) hbu (hx.ext pre) hu (by omega))
    (bd_const (by omega) _)) hbu) hbu (val_div (val_sub (val_add (hx.ext pre) hu)
      (val_const 1 _)) hu) hu ?_
  have : (a + (Nat.log 2 (a + 1) + 1) - 1) / (Nat.log 2 (a + 1) + 1) *
      (Nat.log 2 (a + 1) + 1) = paddedTime a := by
    rw [paddedTime, numBlocks, blockLength, clog_eq_log_add_one, Nat.ceilDiv_eq_add_pred_div]
  omega

/-- The program computing the padded time of the clock `τ`. -/
def padProg : Prog := closeAt 1 (padT (lvl 0) 1)

/-- The program computing `SqrtLog τ`. -/
def sqrtLogProg : Prog := closeAt 1 (sqrtLogT' (lvl 0) 1)

theorem eval_padProg (τ : ℕ) : padProg.eval w [τ] = paddedTime τ := by
  rw [padProg, eval_closeAt _ 1 [τ] rfl]
  exact (val_padT (val_lvl (env := [τ]) (l := 0) (by simp))).eq

theorem bounded_padProg {τ : ℕ} (hτ : 2 ≤ τ) (hM : 2 * τ + 2 ≤ M) : padProg.Bounded w M [τ] := by
  rw [padProg, bounded_closeAt _ 1 [τ] rfl]
  exact (bd_padT (val_lvl (env := [τ]) (l := 0) (by simp)) (bd_lvl _ _) hτ hM).bnd

theorem eval_sqrtLogProg {τ : ℕ} (hτ : 1 ≤ τ) : sqrtLogProg.eval w [τ] = SqrtLog τ := by
  rw [sqrtLogProg, eval_closeAt _ 1 [τ] rfl]
  exact (val_sqrtLogT' (val_lvl (env := [τ]) (l := 0) (by simp)) hτ).eq

theorem bounded_sqrtLogProg {τ : ℕ} (hτ : 1 ≤ τ) (hM : (τ + 2) * (τ + 2) ≤ M) :
    sqrtLogProg.Bounded w M [τ] := by
  rw [sqrtLogProg, bounded_closeAt _ 1 [τ] rfl]
  exact (bd_sqrtLogT' (val_lvl (env := [τ]) (l := 0) (by simp)) (bd_lvl _ _) hτ hM).bnd

theorem closed_padProg : Prog'.closed 1 padProg = true := closed_closeAt _ _

theorem closed_sqrtLogProg : Prog'.closed 1 sqrtLogProg = true := closed_closeAt _ _

/-! ### Sizes at large clocks -/

/-- `n / (log₂ n + 1) ≤ SqrtLog n` for `n ≥ 2`. -/
theorem div_log_le_sqrtLog' {n : ℕ} (hn : 2 ≤ n) : n / (Nat.log 2 n + 1) ≤ SqrtLog n := by
  unfold SqrtLog
  rw [Nat.log2_eq_log_two]
  have hl : 1 ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by simpa using hn)
  have hs : 1 ≤ Nat.sqrt (Nat.log 2 n) := Nat.le_sqrt.mpr (by simpa using hl)
  have : n / (Nat.log 2 n + 1) ≤ n / Nat.sqrt (Nat.log 2 n) :=
    Nat.div_le_div_left (by have := Nat.sqrt_le_self (Nat.log 2 n); omega) hs
  omega

/-- Cubes of logarithms are eventually below `SqrtLog`. -/
theorem polylog3_le_sqrtLog (D : ℕ) : ∀ᶠ n in Filter.atTop, D * (Nat.log 2 n + 2) ^ 3 ≤ SqrtLog
    n := by
  filter_upwards [Polylog.eventually_polylog_le (D + 8) 4, Filter.eventually_ge_atTop 2]
    with n hn hn2
  rw [Nat.log2_eq_log_two] at hn
  set l := Nat.log 2 n
  have key : D * (l + 2) ^ 3 * (l + 1) ≤ n := by
    calc D * (l + 2) ^ 3 * (l + 1) ≤ D * (2 * (l + 1)) ^ 3 * (l + 1) := by gcongr; omega
      _ = (8 * D) * (l + 1) ^ 4 := by ring
      _ ≤ (D + 8) ^ 4 * (l + 1) ^ 4 := by
          gcongr
          calc 8 * D ≤ (D + 8) * (D + 8) := by nlinarith
            _ ≤ (D + 8) ^ 4 := by
              rw [show (D + 8) ^ 4 = (D + 8) * (D + 8) * ((D + 8) * (D + 8)) by ring]
              exact Nat.le_mul_of_pos_right _ (by positivity)
      _ = ((D + 8) * (l + 1)) ^ 4 := by ring
      _ ≤ n := hn
  exact ((Nat.le_div_iff_mul_le (by omega)).mpr key).trans (div_log_le_sqrtLog' hn2)

theorem sqrtLog_le_succ' (τ : ℕ) : SqrtLog τ ≤ τ + 1 :=
  Nat.add_le_add_right (Nat.div_le_self _ _) _

theorem sqrtLog_mul_sqrt_ge {τ : ℕ} (hτ : 2 ≤ τ) : τ + 1 ≤ SqrtLog τ * Nat.sqrt (Nat.log 2 τ) := by
  have hl : 1 ≤ Nat.log 2 τ := Nat.le_log_of_pow_le (by norm_num) (by simpa using hτ)
  have hq : 1 ≤ Nat.sqrt (Nat.log 2 τ) := Nat.le_sqrt.mpr (by simpa using hl)
  unfold SqrtLog
  rw [Nat.log2_eq_log_two]
  have := Nat.lt_div_mul_add (a := τ) (b := Nat.sqrt (Nat.log 2 τ)) (by omega)
  nlinarith

/-- **The size conditions of the Chinese remainder step at large clocks**, for every window end
`X ≤ (τ+2)^C`, with `E = paddedTime τ`, `W = SqrtLog τ` and the bound `2^(8·SqrtLog τ)`. -/
theorem sizes_eventually (C : ℕ) : ∃ τ₁, ∀ τ, τ₁ ≤ τ → ∀ X, X ≤ (τ + 2) ^ C →
    2 ≤ SqrtLog τ ∧ X + 1 ≤ 2 ^ (SqrtLog τ - 1) ∧ paddedTime τ + 1 ≤ 2 ^ (8 * SqrtLog τ) ∧
      4 * ((X + 1) * 2 ^ SqrtLog τ *
        (SqrtLog τ ^ numGroups X (paddedTime τ) (SqrtLog τ) + 1)) ≤ 2 ^ (8 * SqrtLog τ) := by
  obtain ⟨τ₁, hτ₁⟩ := Filter.eventually_atTop.mp
    ((polylog3_le_sqrtLog (8 * (C + 1))).and (Filter.eventually_ge_atTop 4))
  refine ⟨τ₁, fun τ hτ X hX => ?_⟩
  obtain ⟨hpoly, hτ4⟩ := hτ₁ τ hτ
  set S := SqrtLog τ
  set L := Nat.log 2 τ
  set q := Nat.sqrt L
  set A := (L + 2) * C + 1
  have hL1 : 1 ≤ L := Nat.le_log_of_pow_le (by norm_num) (by simpa using (by omega : 2 ≤ τ))
  have hq1 : 1 ≤ q := Nat.le_sqrt.mpr (by simpa using hL1)
  have hqL : q ≤ L := Nat.sqrt_le_self L
  have hL3 : (L + 2) ≤ (L + 2) ^ 3 := Nat.le_self_pow (by norm_num) _
  have h83 : 8 ≤ (L + 2) ^ 3 := by
    calc 8 = 2 ^ 3 := rfl
      _ ≤ (L + 2) ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hpoly' : 8 * (C + 1) * (L + 2) ^ 3 ≤ S := hpoly
  -- the window end
  have hτ2 : τ + 2 ≤ 2 ^ (L + 2) := by
    have h : τ < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) τ
    have : 2 ^ (L + 2) = 2 ^ (L + 1) * 2 := pow_succ _ _
    have := Nat.one_le_two_pow (n := L + 1)
    omega
  have hX2 : X ≤ 2 ^ ((L + 2) * C) := by
    rw [pow_mul]; exact hX.trans (Nat.pow_le_pow_left hτ2 C)
  have hXA : X + 1 ≤ 2 ^ A := by
    rw [show A = (L + 2) * C + 1 from rfl, pow_succ]; have := Nat.one_le_two_pow (n := (L + 2) * C)
    omega
  have hlX : Nat.log 2 X + 1 ≤ A := by
    rcases Nat.eq_zero_or_pos X with h0 | hpos
    · simp [h0, A]
    · have := Nat.log_lt_of_lt_pow (b := 2) (by omega) (show X < 2 ^ ((L + 2) * C + 1) by
        rw [pow_succ]; have := Nat.one_le_two_pow (n := (L + 2) * C); omega)
      omega
  have hAS : A + 2 ≤ S := by
    have : A + 2 ≤ (C + 1) * (L + 2) + 2 := by
      change (L + 2) * C + 1 + 2 ≤ _; nlinarith
    nlinarith
  have hS2 : 2 ≤ S := by omega
  have hτS : τ < 2 ^ S := Nat.lt_log2_self.trans_le
    (Nat.pow_le_pow_right (by norm_num) (log2_add_one_le_sqrtLog τ))
  refine ⟨hS2, hXA.trans (Nat.pow_le_pow_right (by norm_num) (by omega)), ?_, ?_⟩
  · have := paddedTime_add_one_le (show 2 ≤ τ by omega)
    have h2S : 2 ^ (S + 1) ≤ 2 ^ (8 * S) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ] at h2S
    omega
  · -- the number of groups is polylogarithmic
    set lX := Nat.log 2 X + 1
    set r := grpSize X S
    set E := paddedTime τ
    have hr : r = S / lX := rfl
    have hr1 : 1 ≤ r := (Nat.le_div_iff_mul_le (by omega)).mpr (by omega)
    have hrS : S < (r + 1) * lX := by
      have := Nat.lt_div_mul_add (a := S) (b := lX) (by omega); rw [hr]; nlinarith
    have hSq : τ + 1 ≤ S * q := sqrtLog_mul_sqrt_ge (by omega)
    have hE : E + 1 ≤ 2 * τ := paddedTime_add_one_le (by omega)
    have hErq : E < r * (4 * A * q) := by
      have h1 : S * q < (r + 1) * lX * q := Nat.mul_lt_mul_of_pos_right hrS (by omega)
      have h2 : (r + 1) * lX * q ≤ (r + 1) * A * q := by gcongr
      have h3 : (r + 1) * A * q ≤ 2 * r * A * q := by gcongr; omega
      have : r * (4 * A * q) = 2 * (2 * r * A * q) := by ring
      omega
    have hg : numGroups X E S ≤ 4 * A * q := by
      change E / r + 1 ≤ _
      have := (Nat.div_lt_iff_lt_mul hr1).mpr (by rw [mul_comm]; exact hErq)
      omega
    set g := numGroups X E S
    have hSL : S ≤ 2 ^ (L + 2) := by
      have : S ≤ τ + 1 := sqrtLog_le_succ' τ; omega
    have hSg : S ^ g + 1 ≤ 2 ^ ((L + 2) * (4 * A * q) + 1) := by
      have h1 : S ^ g ≤ 2 ^ ((L + 2) * g) := by
        rw [pow_mul]; exact Nat.pow_le_pow_left hSL g
      have h2 : 2 ^ ((L + 2) * g) ≤ 2 ^ ((L + 2) * (4 * A * q)) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left _ hg)
      have h3 := Nat.one_le_two_pow (n := (L + 2) * (4 * A * q))
      rw [pow_succ]; omega
    have hexp : 3 + A + (L + 2) * (4 * A * q) ≤ 7 * S := by
      have hA : A ≤ (C + 1) * (L + 2) := by change (L + 2) * C + 1 ≤ _; nlinarith
      have h1 : (L + 2) * (4 * A * q) ≤ 4 * (C + 1) * (L + 2) ^ 3 := by
        calc (L + 2) * (4 * A * q) ≤ (L + 2) * (4 * ((C + 1) * (L + 2)) * (L + 2)) := by
              gcongr; omega
          _ = 4 * (C + 1) * (L + 2) ^ 3 := by ring
      have h2 : 3 + A ≤ 4 * (C + 1) * (L + 2) ^ 3 := by
        have : (C + 1) * (L + 2) ≤ (C + 1) * (L + 2) ^ 3 := Nat.mul_le_mul_left _ hL3
        nlinarith
      nlinarith
    calc 4 * ((X + 1) * 2 ^ S * (S ^ g + 1))
        ≤ 2 ^ 2 * (2 ^ A * 2 ^ S * 2 ^ ((L + 2) * (4 * A * q) + 1)) := by
          rw [show (2 : ℕ) ^ 2 = 4 from rfl]
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul hXA le_rfl) hSg)
      _ = 2 ^ (3 + A + S + (L + 2) * (4 * A * q)) := by
          rw [← pow_add, ← pow_add, ← pow_add]; congr 1; ring
      _ ≤ 2 ^ (8 * S) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### The clocked bits -/

/-- **The bits of the clocked accept count** (at an arbitrary clock). For every closed
fair-coin table `M` there is a program `P` closed over `[τ, n, j]` computing bit `j` of the accept
count of `M` at the padded time of the clock `τ`, in values below `2^(C·SqrtLog τ)`, on every
input `w` with `|w| ≤ τ` and every clock `τ ≥ τ₀`. -/
def ClockedBits : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State),
    ∃ (P : Prog) (C τ₀ : ℕ), Prog'.closed 3 P = true ∧
      ∀ (w : List Bool) (τ j : ℕ), w.length ≤ τ → τ₀ ≤ τ →
        P.eval w [τ, w.length, j] = M.acceptCount w (paddedTime τ) / 2 ^ j % 2 ∧
          P.Bounded w (2 ^ (C * SqrtLog τ)) [τ, w.length, j]

/-- **The Chinese remainder step at an arbitrary clock, elementary version**: the clocked residues
(a residue form of Theorem 2.3) give the clocked bits. -/
theorem clockedBits_of_clockedResidues (h : ClockedResidues) : ClockedBits := by
  intro k State _ _ M
  obtain ⟨R, Hp, Xp, C, τ₀, hR, hHc, hXc, hspec⟩ := h k State M
  obtain ⟨P, hPc, hP⟩ := exists_bitsProg R Hp Xp padProg sqrtLogProg hR hHc hXc closed_padProg
    closed_sqrtLogProg
  obtain ⟨τ₁, hτ₁⟩ := sizes_eventually C
  refine ⟨P, C + 8, max (max τ₀ τ₁) 4, hPc, fun w τ j hw hτ => ?_⟩
  have hτ0 : τ₀ ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ
  have hτ1 : τ₁ ≤ τ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ
  have hτ4 : 4 ≤ τ := le_trans (le_max_right _ _) hτ
  obtain ⟨hprod, h2H, hXle, hbH, hbX, hres⟩ := hspec w τ hw hτ0
  set S := SqrtLog τ
  obtain ⟨hS2, hK, hE1, hM⟩ := hτ₁ τ hτ1 (Xp.eval w [τ]) hXle
  have hMle : 2 ^ (C * S) ≤ 2 ^ ((C + 8) * S) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have h8 : 2 ^ (8 * S) ≤ 2 ^ ((C + 8) * S) := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hτS : τ < 2 ^ S := Nat.lt_log2_self.trans_le
    (Nat.pow_le_pow_right (by norm_num) (log2_add_one_le_sqrtLog τ))
  have h2S : 2 ^ (2 * S + 2) ≤ 2 ^ ((C + 8) * S) := Nat.pow_le_pow_right
      (by norm_num) (by nlinarith)
  have hsq : (τ + 2) * (τ + 2) ≤ 2 ^ ((C + 8) * S) := by
    have : τ + 2 ≤ 2 ^ (S + 1) := by rw [pow_succ]; omega
    calc (τ + 2) * (τ + 2) ≤ 2 ^ (S + 1) * 2 ^ (S + 1) := Nat.mul_le_mul this this
      _ = 2 ^ (2 * S + 2) := by rw [← pow_add]; congr 1; ring
      _ ≤ _ := h2S
  have hlin : 2 * τ + 2 ≤ 2 ^ ((C + 8) * S) := by nlinarith
  have := hP w τ w.length (M.acceptCount w (paddedTime τ)) (2 ^ ((C + 8) * S))
  simp only [eval_padProg, eval_sqrtLogProg (show 1 ≤ τ by omega)] at this
  exact this h2H hprod acceptCount_le_two_pow
    (fun p hp hHp hpX => ⟨(hres p hp hHp hpX).1, bounded_mono hMle _ _ (hres p hp hHp hpX).2⟩)
    (bounded_mono hMle _ _ hbH) (bounded_mono hMle _ _ hbX) (bounded_padProg (by omega) hlin)
    (bounded_sqrtLogProg (by omega) hsq) hS2 hK (hE1.trans h8) (hM.trans h8) j

end Cslib.Complexity.NtimeDspace.Cross.Exact
