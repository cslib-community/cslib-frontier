/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ColumnAdder
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ScaleInterface

/-!
# The column adder at a general scale

`ColumnAdder.lean` turns the bits of the block networks (`BlockBits`, Theorem 2.3 for the block
networks) into the bits of the accept count (`ClockedBits`) and then into the clocked counter
(`ClockedCounting`), all at the scale `SqrtLog`. Here the same two steps take the scale `D` as a
parameter, which is what the remark of §8 ("improving Theorem 1.1 this way would improve the
simulation of `PPTIME[t]` as well") needs: a version of Theorem 2.3 at a smaller scale `D` is used
exactly as the `SqrtLog` one is.

The column adder sums the contractions of all `N = 3 ^ ((k + 1) · numBlocks τ)` block networks of
the clock `τ`, so its carry and its column sums are below `N`; it is run with values below
`2 ^ (C · D τ)`, which needs `log₂ N = Θ(numBlocks τ) = Θ(τ / log τ)` to be `O(D τ)`. This is the
only hypothesis on `D` besides `log₂ τ + 1 ≤ D τ` (which bounds the clock itself and the padded
time below `2 ^ D τ`): `CarryFits D`, i.e. `numBlocks τ ≤ c · D τ` for large `τ`. Every scale at
least `τ / (log₂ τ + 1)` satisfies it (`carryFits_of_div_log_le`), in particular `SqrtLog`
(`carryFits_sqrtLog`), and conversely every scale that fits the carry is `Ω(τ / log τ)`
(`CarryFits.div_log_le`); so this route cannot go below `t / log t`, which is the target scale
of the paper's remark.

## Main definitions

* `Cslib.Complexity.NtimeDspace.Cross.Exact.BlockBitsAt D`,
`Cslib.Complexity.NtimeDspace.Cross.Exact.ClockedBitsAt D`: `BlockBits`
  and `ClockedBits` with `D τ` in place of `SqrtLog τ` (`blockBitsAt_sqrtLog`,
  `clockedBitsAt_sqrtLog`: at `D = SqrtLog` they are those definitions). `BlockBitsAt.mono`:
  only `D` up to a constant factor matters.
* `Cslib.Complexity.NtimeDspace.Cross.Exact.CarryFits D`: `numBlocks τ = O(D τ)`.

## Main results

* `Cslib.Complexity.NtimeDspace.Cross.Exact.clockedBitsAt_of_blockBitsAt`: for `log₂ n + 1 ≤ D n`
and
  `CarryFits D`, `BlockBitsAt D → ClockedBitsAt D` (the column adder over schedules).
* `Cslib.Complexity.NtimeDspace.Cross.Exact.clockedCountingAt_of_clockedBitsAt`: for `log₂ n + 1 ≤ D
n`,
  `ClockedBitsAt D → ClockedCountingAt D` (the count test).
* `Cslib.Complexity.NtimeDspace.Cross.Exact.numBlocks_le_div_log2`: `numBlocks n ≤ n / (log₂ n + 1)
+ 1`;
  `carryFits_of_div_log_le`, `carryFits_sqrtLog`, `CarryFits.div_log_le`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset
  Cslib.Complexity Cslib.Complexity.CountingSimulation _root_.Turing Filter

variable {w : List Bool} {env : List ℕ} {M : ℕ}

/-! ### The statements at a scale `D` -/

/-- `BlockBits` at the scale `D`: for every machine and state enumeration, one closed program over
`[τ, n, σ, j]` computes bit `j` of the contraction of the block network of schedule `σ` at clock
`τ`, in values below `2 ^ (C · D τ)`. -/
def BlockBitsAt (D : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State)
    (s : ℕ) (e : State ≃ Fin s),
    ∃ (B : Prog) (C τ₀ : ℕ), Prog'.closed 4 B = true ∧
      ∀ (w : List Bool) (τ σ j : ℕ), w.length ≤ τ → τ₀ ≤ τ → σ < scheduleCount (k + 1) τ →
        B.eval w [τ, w.length, σ, j] = (blockNetworkOf M e (w, τ, σ)).2.contraction / 2 ^ j % 2 ∧
          B.Bounded w (2 ^ (C * D τ)) [τ, w.length, σ, j]

/-- `ClockedBits` at the scale `D`: bit `j` of the accept count at the padded time of the clock
`τ`, by one closed program over `[τ, n, j]` in values below `2 ^ (C · D τ)`. -/
def ClockedBitsAt (D : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State),
    ∃ (P : Prog) (C τ₀ : ℕ), Prog'.closed 3 P = true ∧
      ∀ (w : List Bool) (τ j : ℕ), w.length ≤ τ → τ₀ ≤ τ →
        P.eval w [τ, w.length, j] = M.acceptCount w (paddedTime τ) / 2 ^ j % 2 ∧
          P.Bounded w (2 ^ (C * D τ)) [τ, w.length, j]

theorem blockBitsAt_sqrtLog : BlockBitsAt SqrtLog ↔ BlockBits := Iff.rfl

theorem clockedBitsAt_sqrtLog : ClockedBitsAt SqrtLog ↔ ClockedBits := Iff.rfl

/-- `BlockBitsAt` depends on the scale only up to a constant factor. -/
theorem BlockBitsAt.mono {D D' : ℕ → ℕ} {c : ℕ} (hDD : ∀ n, D n ≤ c * D' n)
    (h : BlockBitsAt D) : BlockBitsAt D' := by
  intro k State _ _ M s e
  obtain ⟨B, C, τ₀, hBc, hB⟩ := h k State M s e
  refine ⟨B, C * c, τ₀, hBc, fun w τ σ j hw hτ hσ => ⟨(hB w τ σ j hw hτ hσ).1, ?_⟩⟩
  refine bounded_mono (Nat.pow_le_pow_right (by norm_num) ?_) _ _ (hB w τ σ j hw hτ hσ).2
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left _ (hDD τ)

/-- **The carry of the column adder fits the scale**: `numBlocks τ ≤ c · D τ` for large `τ`. The
column adder over the `3 ^ ((k + 1) · numBlocks τ)` schedules has column sums and a carry of
`Θ(numBlocks τ)` bits, and it runs in values below `2 ^ (C · D τ)`. -/
def CarryFits (D : ℕ → ℕ) : Prop := ∃ c, ∀ᶠ n in atTop, numBlocks n ≤ c * D n

/-! ### The number of blocks -/

/-- `numBlocks n ≤ n / (log₂ n + 1) + 1`: the blocks have length `⌈log₂ (n + 2)⌉ ≥ log₂ n + 1`. -/
theorem numBlocks_le_div_log2 (n : ℕ) : numBlocks n ≤ n / (n.log2 + 1) + 1 := by
  have hb : Nat.log 2 n + 1 ≤ blockLength n := by
    rw [blockLength, clog_eq_log_add_one]; exact Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have h1 : numBlocks n ≤ n / blockLength n + 1 := by
    rw [numBlocks, Nat.ceilDiv_eq_add_pred_div]
    calc (n + blockLength n - 1) / blockLength n ≤ (n + blockLength n) / blockLength n :=
          Nat.div_le_div_right (by omega)
      _ = n / blockLength n + 1 := by rw [Nat.add_div_right _ (by omega)]
  have h2 : n / blockLength n ≤ n / (Nat.log 2 n + 1) := Nat.div_le_div_left hb (by omega)
  rw [Nat.log2_eq_log_two]
  omega

/-- Every scale with `1 ≤ D n` and eventually `n / (log₂ n + 1) ≤ c · D n` fits the carry. -/
theorem carryFits_of_div_log_le {D : ℕ → ℕ} (h1 : ∀ n, 1 ≤ D n) {c : ℕ}
    (h : ∀ᶠ n in atTop, n / (n.log2 + 1) ≤ c * D n) : CarryFits D := by
  refine ⟨c + 1, h.mono fun n hn => ?_⟩
  have := numBlocks_le_div_log2 n
  have := h1 n
  nlinarith

/-- `SqrtLog` fits the carry: `numBlocks n ≤ n / (log₂ n + 1) + 1 ≤ SqrtLog n + 1`. -/
theorem carryFits_sqrtLog : CarryFits SqrtLog := by
  refine carryFits_of_div_log_le (c := 1) (fun n => Nat.le_add_left _ _) ?_
  filter_upwards [eventually_ge_atTop 2] with n hn
  rw [one_mul, Nat.log2_eq_log_two]
  exact div_log_le_sqrtLog' hn

/-- Conversely, `CarryFits D` forces `D n = Ω(n / log n)`: `n / (log₂ n + 2) ≤ numBlocks n`. -/
theorem CarryFits.div_log_le {D : ℕ → ℕ} (h : CarryFits D) :
    ∃ c, ∀ᶠ n in atTop, n / (n.log2 + 2) ≤ c * D n := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c, hc.mono fun n hn => le_trans ?_ hn⟩
  have hb : blockLength n ≤ n.log2 + 2 := by
    rw [blockLength, clog_eq_log_add_one]
    have hlt : n + 1 < 2 ^ (n.log2 + 2) := by
      have := Nat.lt_log2_self (n := n); rw [pow_succ]; omega
    have := Nat.log_lt_of_lt_pow (b := 2) (by omega) hlt
    omega
  have hb0 : 0 < blockLength n := by rw [blockLength, clog_eq_log_add_one]; omega
  calc n / (n.log2 + 2) ≤ n / blockLength n := Nat.div_le_div_left hb hb0
    _ ≤ numBlocks n := by
        rw [numBlocks, Nat.ceilDiv_eq_add_pred_div]; exact Nat.div_le_div_right (by omega)

/-! ### Sizes -/

/-- `n < 2 ^ D n` when `log₂ n + 1 ≤ D n`. -/
theorem lt_two_pow_of_log_le {D : ℕ → ℕ} (hlog : ∀ n, n.log2 + 1 ≤ D n) (n : ℕ) : n < 2 ^ D n :=
  Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) (hlog n))

/-- `2τ + 2 ≤ 2 ^ (E · D τ)` for `E ≥ 2`, when `log₂ τ + 1 ≤ D τ`. -/
theorem lin_le_two_pow_at {D : ℕ → ℕ} (hlog : ∀ n, n.log2 + 1 ≤ D n) (τ : ℕ) {E : ℕ}
    (hE : 2 ≤ E) : 2 * τ + 2 ≤ 2 ^ (E * D τ) := by
  have hS1 : 1 ≤ D τ := le_trans (Nat.le_add_left _ _) (hlog τ)
  have hτS := lt_two_pow_of_log_le hlog τ
  have h1 : 2 * τ + 2 ≤ 2 ^ (D τ + 1) := by rw [pow_succ]; omega
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

/-- The value bounds of the column adder at the bound `2 ^ ((C + 2(k+1)c + k + 4) · D τ)`, when
`numBlocks τ ≤ c · D τ`. -/
theorem adder_sizesAt {D : ℕ → ℕ} (hlog : ∀ n, n.log2 + 1 ≤ D n) (k C c : ℕ) {τ : ℕ}
    (hnb : numBlocks τ ≤ c * D τ) :
    2 * τ + 2 ≤ 2 ^ ((C + 2 * (k + 1) * c + k + 4) * D τ) ∧
      k + 3 ≤ 2 ^ ((C + 2 * (k + 1) * c + k + 4) * D τ) ∧
      (k + 1) * numBlocks τ ≤ 2 ^ ((C + 2 * (k + 1) * c + k + 4) * D τ) ∧
      2 * 3 ^ ((k + 1) * numBlocks τ) ≤ 2 ^ ((C + 2 * (k + 1) * c + k + 4) * D τ) ∧
      2 ^ (C * D τ) ≤ 2 ^ ((C + 2 * (k + 1) * c + k + 4) * D τ) := by
  have hS1 : 1 ≤ D τ := le_trans (Nat.le_add_left _ _) (hlog τ)
  set E := C + 2 * (k + 1) * c + k + 4 with hE
  set S := D τ
  set x := (k + 1) * numBlocks τ
  have hmono : ∀ m, m ≤ E * S → 2 ^ m ≤ 2 ^ (E * S) :=
    fun m hm => Nat.pow_le_pow_right (by norm_num) hm
  have hx : 2 * x + 1 ≤ E * S := by
    have h1 : x ≤ (k + 1) * (c * S) := Nat.mul_le_mul_left _ hnb
    have h2 : (2 * (k + 1) * c + 1) * S ≤ E * S := Nat.mul_le_mul_right _ (by omega)
    have h3 : 2 * ((k + 1) * (c * S)) + 1 ≤ (2 * (k + 1) * c + 1) * S := by
      have : (2 * (k + 1) * c + 1) * S = 2 * ((k + 1) * (c * S)) + S := by ring
      omega
    omega
  have h3 : 2 * 3 ^ x ≤ 2 ^ (E * S) := by
    have h34 : 3 ^ x ≤ 2 ^ (2 * x) :=
      (Nat.pow_le_pow_left (show 3 ≤ 2 ^ 2 by norm_num) x).trans_eq (pow_mul 2 2 x).symm
    calc 2 * 3 ^ x ≤ 2 * 2 ^ (2 * x) := Nat.mul_le_mul_left _ h34
      _ = 2 ^ (2 * x + 1) := by rw [pow_succ]; ring
      _ ≤ _ := hmono _ hx
  refine ⟨lin_le_two_pow_at hlog τ (by omega), ?_, ?_, h3,
    hmono _ (Nat.mul_le_mul_right _ (by omega))⟩
  · have h1 : k + 3 < 2 ^ (k + 3) := Nat.lt_two_pow_self
    have h2 : k + 3 ≤ E * S := le_trans (show k + 3 ≤ E by omega) (Nat.le_mul_of_pos_right _ hS1)
    exact h1.le.trans (hmono _ h2)
  · have h1 : x < 2 ^ x := Nat.lt_two_pow_self
    have h2 : 2 ^ x ≤ 3 ^ x := Nat.pow_le_pow_left (by norm_num) x
    omega

/-! ### The column adder and the count test at a scale `D` -/

/-- **The sum over schedules at a scale `D`** (the column adder of the proof of Theorem 7.1): if
`log₂ n + 1 ≤ D n` and the carry fits the scale, the bits of the block networks in values below
`2 ^ (C · D τ)` give the bits of the accept count at the padded time of every large clock, in
values below `2 ^ (C' · D τ)`. -/
theorem clockedBitsAt_of_blockBitsAt {D : ℕ → ℕ} (hlog : ∀ n, n.log2 + 1 ≤ D n)
    (hc : CarryFits D) (h : BlockBitsAt D) : ClockedBitsAt D := by
  intro k State _ _ Mc
  obtain ⟨c, hcev⟩ := hc
  obtain ⟨τ₁, hτ₁⟩ := eventually_atTop.mp hcev
  obtain ⟨B, C, τ₀, hBc, hB⟩ := h k State Mc _ (Finite.equivFin State)
  refine ⟨closeAt 3 (adderT k B 3), C + 2 * (k + 1) * c + k + 4, max (max τ₀ τ₁) 2,
    closed_closeAt 3 _, fun w τ j hw hτ => ?_⟩
  have hτ0 : τ₀ ≤ τ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hτ
  have hτ1 : τ₁ ≤ τ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hτ
  have hτ2 : 2 ≤ τ := le_trans (le_max_right _ _) hτ
  obtain ⟨hlin, hk3, hm, h3, hCM⟩ := adder_sizesAt hlog k C c (hτ₁ τ hτ1)
  set Mb := 2 ^ ((C + 2 * (k + 1) * c + k + 4) * D τ)
  set N := scheduleCount (k + 1) τ with hNdef
  set T := paddedTime τ with hTdef
  have hNe : N = 3 ^ ((k + 1) * numBlocks τ) := rfl
  set Z : ℕ → ℕ := fun σ => (blockNetworkOf Mc (Finite.equivFin State) (w, τ, σ)).2.contraction
  have hA : ∑ σ ∈ range N, Z σ = Mc.acceptCount w T :=
    sum_contraction_blockNetworkOf Mc (Finite.equivFin State) w hτ2
  have hAle : Mc.acceptCount w T ≤ 2 ^ T := acceptCount_le_two_pow
  have hT1 : T + 1 ≤ 2 * τ := paddedTime_add_one_le hτ2
  have hZ : ∀ σ < N, Z σ < 2 ^ (T + 1) := fun σ hσ => by
    have h1 : Z σ ≤ ∑ σ ∈ range N, Z σ :=
      single_le_sum (f := Z) (fun _ _ => Nat.zero_le _) (mem_range.mpr hσ)
    have h2 : 2 ^ T < 2 ^ (T + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hspec : ∀ σ < N, ∀ i, B.eval w [τ, w.length, σ, i] = Z σ / 2 ^ i % 2 ∧
      B.Bounded w Mb [τ, w.length, σ, i] := fun σ hσ i =>
    ⟨(hB w τ σ i hw hτ0 hσ).1, bounded_mono hCM _ _ (hB w τ σ i hw hτ0 hσ).2⟩
  have hCf : ∀ i, ∑ σ ∈ range N, B.eval w [τ, w.length, σ, i] =
      ∑ σ ∈ range N, Z σ / 2 ^ i % 2 :=
    fun i => sum_congr rfl fun σ hσ => (hspec σ (mem_range.mp hσ) i).1
  have hCle : ∀ i, ∑ σ ∈ range N, B.eval w [τ, w.length, σ, i] ≤ N := fun i => by
    rw [hCf]
    calc ∑ σ ∈ range N, Z σ / 2 ^ i % 2 ≤ ∑ _σ ∈ range N, 1 :=
          sum_le_sum fun σ _ => div_mod_two_le_one _
      _ = N := by simp
  -- the environment
  have hτ : Val w (lvl 2) [τ, w.length, j] τ := val_lvl (by simp)
  have hn : Val w (lvl 1) [τ, w.length, j] w.length := val_lvl (by simp)
  have hj : Val w (lvl 0) [τ, w.length, j] j := val_lvl (by simp)
  have hNv : Val w (call1 (schedProg k) (lvl 2)) [τ, w.length, j] N := by
    have := val_call1 (closed_schedProg k) hτ; rwa [eval_schedProg] at this
  have hTv : Val w (call1 padProg (lvl 2)) [τ, w.length, j] T := by
    have := val_call1 closed_padProg hτ; rwa [eval_padProg] at this
  -- the value
  have hval : Val w (adderT k B) [τ, w.length, j]
      (if 0 < (if T < j then 1 else 0) then 0
        else bitOf (fun i => ∑ σ ∈ range N, B.eval w [τ, w.length, σ, i]) j) := by
    refine val_letT hNv fun p1 N' hN' => ?_
    refine val_letT (hTv.ext p1) fun p2 T' hT' => ?_
    exact val_ite (val_lt hT' ((hj.ext p1).ext p2)) (val_const 0 _)
      (val_bitOfT (fval_colT hBc ((hτ.ext p1).ext p2) ((hn.ext p1).ext p2) (hN'.ext p2))
        ((hj.ext p1).ext p2))
  -- the bounds
  have hbd : Bd w Mb (adderT k B) [τ, w.length, j] := by
    have hbs := bd_call1 (closed_schedProg k) hτ (bd_lvl _ _)
      (bounded_schedProg (w := w) k hlin hk3 hm (by omega))
    have hbp := bd_call1 closed_padProg hτ (bd_lvl _ _) (bounded_padProg (w := w) hτ2 hlin)
    refine bd_letT hNv hbs fun p1 N' hN' hbN' => ?_
    refine bd_letT (hTv.ext p1) (hbp.ext p1) fun p2 T' hT' hbT' => ?_
    refine bd_ite (bd_lt hbT' (bd_lvl _ _)) (val_lt hT' ((hj.ext p1).ext p2))
      (fun _ => bd_const (Nat.zero_le _) _) fun hneg => ?_
    have hjT : j ≤ T := by
      by_contra hc
      exact hneg (by rw [ite_eq_left (show T < j by omega)]; exact Nat.one_pos)
    refine bd_bitOfT (fval_colT hBc ((hτ.ext p1).ext p2) ((hn.ext p1).ext p2) (hN'.ext p2))
      ((hj.ext p1).ext p2) (bd_lvl _ _) (by omega) (D := N) (fun i _ => hCle i) (by omega)
      (by omega) fun pre u i hi hu hbu => ?_
    exact bd_colT hBc (((hτ.ext p1).ext p2).ext pre) (((hn.ext p1).ext p2).ext pre)
      ((hN'.ext p2).ext pre) (bd_lvl _ _) (bd_lvl _ _) ((hbN'.ext p2).ext pre) hu hbu (by omega)
      ((hCle i).trans (by omega)) fun σ hσ => (hspec σ hσ i).2
  refine ⟨?_, ?_⟩
  · rw [eval_closeAt _ 3 [τ, w.length, j] rfl]
    refine hval.eq.trans ?_
    by_cases hTj : T < j
    · rw [ite_eq_left hTj, ite_eq_left Nat.one_pos]
      have : Mc.acceptCount w T < 2 ^ j :=
        lt_of_le_of_lt hAle (Nat.pow_lt_pow_right (by norm_num) hTj)
      rw [Nat.div_eq_of_lt this]
    · rw [ite_eq_right hTj, ite_eq_right (lt_irrefl 0), ← hA, bit_sum_eq_bitOf Z hZ (by omega)]
      exact congrArg (bitOf · j) (funext hCf)
  · rw [bounded_closeAt _ 3 [τ, w.length, j] rfl]
    exact hbd.bnd

/-- **The clocked counter from the clocked bits at a scale `D`**, for `log₂ n + 1 ≤ D n`. -/
theorem clockedCountingAt_of_clockedBitsAt {D : ℕ → ℕ} (hlog : ∀ n, n.log2 + 1 ≤ D n)
    (h : ClockedBitsAt D) : ClockedCountingAt D := by
  intro k State _ _ Mc
  obtain ⟨P, C, τ₀, hPc, hP⟩ := h k State Mc
  refine ⟨closeAt 3 (cntBitsT P 3), C + 3, max τ₀ 2, closed_closeAt 3 _,
    fun w τ b hw hτ hb => ?_⟩
  have hτ0 : τ₀ ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ2 : 2 ≤ τ := le_trans (le_max_right _ _) hτ
  set Mb := 2 ^ ((C + 3) * D τ)
  have hlin : 2 * τ + 2 ≤ Mb := lin_le_two_pow_at hlog τ (by omega)
  have hCM : 2 ^ (C * D τ) ≤ Mb :=
    Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ (by omega))
  have h1M : 1 ≤ Mb := by omega
  set T := paddedTime τ with hTdef
  set A := Mc.acceptCount w T
  have hAle : A ≤ 2 ^ T := acceptCount_le_two_pow
  have hT1 : T + 1 ≤ 2 * τ := paddedTime_add_one_le hτ2
  have hspec : ∀ j, P.eval w [τ, w.length, j] = A / 2 ^ j % 2 ∧
      P.Bounded w Mb [τ, w.length, j] := fun j =>
    ⟨(hP w τ j hw hτ0).1, bounded_mono hCM _ _ (hP w τ j hw hτ0).2⟩
  have hτ : Val w (lvl 2) [τ, w.length, b] τ := val_lvl (by simp)
  have hn : Val w (lvl 1) [τ, w.length, b] w.length := val_lvl (by simp)
  have hbv : Val w (lvl 0) [τ, w.length, b] b := val_lvl (by simp)
  have hTv : Val w (call1 padProg (lvl 2)) [τ, w.length, b] T := by
    have := val_call1 closed_padProg hτ; rwa [eval_padProg] at this
  have hF : ∀ p1 T', Val w T' (p1 ++ [τ, w.length, b]) T →
      FVal w (fun j => sub (const 1) (eqT (call3 P (lvl 2) (lvl 1) j) (mul (lvl 0) (eqT j T'))))
        (p1 ++ [τ, w.length, b])
        (fun j => 1 - if P.eval w [τ, w.length, j] = b * (if j = T then 1 else 0) then 1 else 0) :=
    fun p1 T' hT' pre u q hu => val_sub (val_const 1 _) (val_eqT
      (val_call3 hPc ((hτ.ext p1).ext pre) ((hn.ext p1).ext pre) hu)
      (val_mul ((hbv.ext p1).ext pre) (val_eqT hu (hT'.ext pre))))
  have hval : Val w (cntBitsT P) [τ, w.length, b] (∑ j ∈ range (T + 1),
      (1 - if P.eval w [τ, w.length, j] = b * (if j = T then 1 else 0) then 1 else 0)) :=
    val_letT hTv fun p1 T' hT' => val_sumT (val_add hT' (val_const 1 _)) (hF p1 T' hT')
  have hbd : Bd w Mb (cntBitsT P) [τ, w.length, b] := by
    have hbp := bd_call1 closed_padProg hτ (bd_lvl _ _) (bounded_padProg (w := w) hτ2 hlin)
    refine bd_letT hTv hbp fun p1 T' hT' hbT' => ?_
    refine bd_sumT (val_add hT' (val_const 1 _)) (hF p1 T' hT')
      (bd_add hbT' (bd_const (by omega) _) hT' (val_const 1 _) (by omega)) (by omega) ?_
      fun pre u q hq hu hbu => ?_
    · calc _ ≤ ∑ _j ∈ range (T + 1), 1 := sum_le_sum fun j _ => Nat.sub_le _ _
        _ ≤ Mb := by rw [sum_const, card_range, smul_eq_mul, mul_one]; omega
    · have hPq := hspec q
      have hP1 : P.eval w [τ, w.length, q] ≤ 1 := by rw [hPq.1]; exact div_mod_two_le_one _
      have hb1 : b * (if q = T then 1 else 0) ≤ 1 := by split_ifs <;> omega
      refine bd_sub (bd_const (by omega) _) (bd_eqT
        (bd_call3 hPc ((hτ.ext p1).ext pre) ((hn.ext p1).ext pre) hu (bd_lvl _ _) (bd_lvl _ _) hbu
          hPq.2)
        (bd_mul (bd_lvl _ _) (bd_eqT hbu (hbT'.ext pre) hu (hT'.ext pre) (by omega) (by omega)
          (by omega)) ((hbv.ext p1).ext pre) (val_eqT hu (hT'.ext pre)) (hb1.trans h1M))
        (val_call3 hPc ((hτ.ext p1).ext pre) ((hn.ext p1).ext pre) hu)
        (val_mul ((hbv.ext p1).ext pre) (val_eqT hu (hT'.ext pre))) (hP1.trans h1M)
        (hb1.trans h1M) h1M)
  refine ⟨?_, ?_⟩
  · rw [eval_closeAt _ 3 [τ, w.length, b] rfl]
    have hv : (cntBitsT P 3).eval w [τ, w.length, b] = _ := hval.eq
    rw [hv, ← cnt_pos_iff hAle hb]
    refine Iff.of_eq (congrArg (0 < ·) (sum_congr rfl fun j _ => ?_))
    rw [(hspec j).1]
  · rw [bounded_closeAt _ 3 [τ, w.length, b] rfl]
    exact hbd.bnd

/-! ### The case `D = SqrtLog` -/

/-- At `D = SqrtLog` the general column adder gives back `clockedBits_of_blockBits`. -/
theorem clockedBits_of_blockBits_viaAt (h : BlockBits) : ClockedBits :=
  clockedBitsAt_of_blockBitsAt log2_add_one_le_sqrtLog carryFits_sqrtLog h

/-- At `D = SqrtLog` the general count test gives back `clockedCounting_of_clockedBits`. -/
theorem clockedCounting_of_clockedBits_viaAt (h : ClockedBits) : ClockedCounting :=
  clockedCountingAt_of_clockedBitsAt log2_add_one_le_sqrtLog h

end Cslib.Complexity.NtimeDspace.Cross.Exact
