/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.BlockNetworks
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ExactClocked

/-!
# The column adder: bits of the accept count from bits of the block networks

The accept count at the padded time of a clock `τ` is the sum of the contractions `Z_σ` of the
block networks of the `N = scheduleCount (k + 1) τ` schedules (`sum_contraction_blockNetworkOf`).
`BlockBits` asks for one closed program over `[τ, n, σ, j]` computing bit `j` of `Z_σ` in values
below `2^(C·SqrtLog τ)`. From such a program the column adder (schoolbook addition, one column at
a time with a carry) computes bit `j` of the sum: column `i` is the number of schedules whose
network has bit `i`, the carry chain is `chain` of `ExactArith.lean`, and the carry stays below
`N < 2^(C·SqrtLog τ)`. Bits above `paddedTime τ` are `0`, since the count is at most
`2^paddedTime τ`; the program returns `0` there, so the column loop runs at most
`paddedTime τ + 1` times.

A program for the bits of the count then decides whether the count differs from
`b · 2^paddedTime τ` (`b ≤ 1`), by comparing its bits `j ≤ paddedTime τ` with those of
`b · 2^paddedTime τ`.

## Main definitions

* `Cslib.Complexity.NtimeDspace.Cross.Exact.BlockBits`: the bits of the block networks as one closed
program.
* `Cslib.Complexity.NtimeDspace.Cross.Exact.adderT`: the column adder over `[τ, n, j]`.
* `Cslib.Complexity.NtimeDspace.Cross.Exact.cntBitsT`: the count test over `[τ, n, b]` from a bits
program.

## Main results

* `Cslib.Complexity.NtimeDspace.Cross.Exact.clockedBits_of_blockBits : BlockBits → ClockedBits`.
* `Cslib.Complexity.NtimeDspace.Cross.Exact.clockedCounting_of_clockedBits : ClockedBits →
ClockedCounting`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross.Exact

open NtimeDspace.ProgLang NtimeDspace.ProgTerm Term NtimeDspace.SumProduct Finset
  Cslib.Complexity Cslib.Complexity.CountingSimulation _root_.Turing

variable {w : List Bool} {env : List ℕ} {M : ℕ}

/-- Bits of the block networks: for every machine and state enumeration, one closed program over
`[τ, n, σ, j]` computes bit `j` of the contraction of the block network of schedule `σ` at clock
`τ`. -/
def BlockBits : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State)
    (s : ℕ) (e : State ≃ Fin s),
    ∃ (B : Prog) (C τ₀ : ℕ), Prog'.closed 4 B = true ∧
      ∀ (w : List Bool) (τ σ j : ℕ), w.length ≤ τ → τ₀ ≤ τ → σ < scheduleCount (k + 1) τ →
        B.eval w [τ, w.length, σ, j] = (blockNetworkOf M e (w, τ, σ)).2.contraction / 2 ^ j % 2 ∧
          B.Bounded w (2 ^ (C * SqrtLog τ)) [τ, w.length, σ, j]

/-! ### Calling a program closed in four variables -/

/-- Run a program closed in four variables on four argument terms. -/
def call4 (q : Prog) (a b c d : Term) : Term :=
  fun m => .letIn (d m) (.letIn (c (m + 1)) (.letIn (b (m + 2)) (.letIn (a (m + 3)) q)))

theorem val_call4 {q : Prog} (hq : Prog'.closed 4 q = true) {a b c d : Term} {x y z u : ℕ}
    (ha : Val w a env x) (hb : Val w b env y) (hc : Val w c env z) (hd : Val w d env u) :
    Val w (call4 q a b c d) env (q.eval w [x, y, z, u]) := fun extra => by
  change Prog.eval w (.letIn _ (.letIn _ (.letIn _ (.letIn _ q)))) _ = _
  simp only [Prog.eval]
  have e1 : (d (extra ++ env).length).eval w (extra ++ env) = u := hd extra
  rw [e1]
  have e2 : (c ((extra ++ env).length + 1)).eval w (u :: (extra ++ env)) = z := hc (u :: extra)
  rw [e2]
  have e3 : (b ((extra ++ env).length + 2)).eval w (z :: u :: (extra ++ env)) = y :=
    hb (z :: u :: extra)
  rw [e3]
  have e4 : (a ((extra ++ env).length + 3)).eval w (y :: z :: u :: (extra ++ env)) = x :=
    ha (y :: z :: u :: extra)
  rw [e4]
  exact Prog'.eval_append q [x, y, z, u] (extra ++ env) hq

theorem bd_call4 {q : Prog} (hq : Prog'.closed 4 q = true) {a b c d : Term} {x y z u : ℕ}
    (ha : Val w a env x) (hb : Val w b env y) (hc : Val w c env z) (hd : Val w d env u)
    (hba : Bd w M a env) (hbb : Bd w M b env) (hbc : Bd w M c env) (hbd : Bd w M d env)
    (h : q.Bounded w M [x, y, z, u]) : Bd w M (call4 q a b c d) env := fun extra => by
  change Prog.Bounded w M (.letIn _ (.letIn _ (.letIn _ (.letIn _ q)))) _
  simp only [Prog.Bounded]
  have e1 : (d (extra ++ env).length).eval w (extra ++ env) = u := hd extra
  have e2 : (c ((extra ++ env).length + 1)).eval w (u :: (extra ++ env)) = z := hc (u :: extra)
  have e3 : (b ((extra ++ env).length + 2)).eval w (z :: u :: (extra ++ env)) = y :=
    hb (z :: u :: extra)
  have e4 : (a ((extra ++ env).length + 3)).eval w (y :: z :: u :: (extra ++ env)) = x :=
    ha (y :: z :: u :: extra)
  refine ⟨hbd extra, ?_⟩
  rw [e1]
  refine ⟨hbc (u :: extra), ?_⟩
  rw [e2]
  refine ⟨hbb (z :: u :: extra), ?_⟩
  rw [e3]
  refine ⟨hba (y :: z :: u :: extra), ?_⟩
  rw [e4]
  exact (Prog'.bounded_append M q [x, y, z, u] (extra ++ env) hq).mpr h

/-! ### The number of schedules as a program -/

/-- The number of blocks `⌈x / blockLength x⌉`. -/
def nbT (x : Term) : Term :=
  letT (bitLenT (add x (const 1))) fun bl => div (sub (add x bl) (const 1)) bl

theorem val_nbT {x : Term} {a : ℕ} (hx : Val w x env a) : Val w (nbT x) env (numBlocks a) := by
  refine val_letT (val_bitLenT (val_add hx (val_const 1 env)) (by omega)) fun pre u hu => ?_
  have := val_div (val_sub (val_add (hx.ext pre) hu) (val_const 1 _)) hu
  refine fun extra => (this extra).trans ?_
  rw [numBlocks, blockLength, clog_eq_log_add_one, Nat.ceilDiv_eq_add_pred_div]

theorem bd_nbT {x : Term} {a : ℕ} (hx : Val w x env a) (hbx : Bd w M x env)
    (hM : 2 * a + 2 ≤ M) : Bd w M (nbT x) env := by
  have hl := Nat.log_lt_self 2 (show a + 1 ≠ 0 by omega)
  refine bd_letT (val_bitLenT (val_add hx (val_const 1 env)) (by omega))
    (bd_bitLenT (val_add hx (val_const 1 env)) (bd_add hbx (bd_const (by omega) _) hx
      (val_const 1 _) (by omega)) (by omega)) fun pre u hu hbu => ?_
  exact bd_div (bd_sub (bd_add (hbx.ext pre) hbu (hx.ext pre) hu (by omega))
    (bd_const (by omega) _)) hbu

/-- The number of schedules `3 ^ ((k + 1) · numBlocks x)`. -/
def schedT (k : ℕ) (x : Term) : Term := pwT (const 3) (mul (const (k + 1)) (nbT x))

theorem val_schedT (k : ℕ) {x : Term} {a : ℕ} (hx : Val w x env a) :
    Val w (schedT k x) env (scheduleCount (k + 1) a) :=
  val_pwT (val_const 3 env) (val_mul (val_const (k + 1) env) (val_nbT hx))

theorem bd_schedT (k : ℕ) {x : Term} {a : ℕ} (hx : Val w x env a) (hbx : Bd w M x env)
    (hM : 2 * a + 2 ≤ M) (hk : k + 3 ≤ M) (hm : (k + 1) * numBlocks a ≤ M)
    (h3 : 3 ^ ((k + 1) * numBlocks a) ≤ M) : Bd w M (schedT k x) env :=
  bd_pwT (val_const 3 env) (val_mul (val_const (k + 1) env) (val_nbT hx)) (bd_const (by omega) _)
    (bd_mul (bd_const (by omega) _) (bd_nbT hx hbx hM) (val_const _ env) (val_nbT hx) hm) le_rfl
    h3 (by norm_num) hm

/-- The program computing the number of schedules `scheduleCount (k + 1) τ` of the clock `τ`. -/
def schedProg (k : ℕ) : Prog := closeAt 1 (schedT k (lvl 0) 1)

theorem closed_schedProg (k : ℕ) : Prog'.closed 1 (schedProg k) = true := closed_closeAt _ _

theorem eval_schedProg (k τ : ℕ) : (schedProg k).eval w [τ] = scheduleCount (k + 1) τ := by
  rw [schedProg, eval_closeAt _ 1 [τ] rfl]
  exact (val_schedT k (val_lvl (env := [τ]) (l := 0) (by simp))).eq

theorem bounded_schedProg (k : ℕ) {τ : ℕ} (hM : 2 * τ + 2 ≤ M) (hk : k + 3 ≤ M)
    (hm : (k + 1) * numBlocks τ ≤ M) (h3 : 3 ^ ((k + 1) * numBlocks τ) ≤ M) :
    (schedProg k).Bounded w M [τ] := by
  rw [schedProg, bounded_closeAt _ 1 [τ] rfl]
  exact (bd_schedT k (val_lvl (env := [τ]) (l := 0) (by simp)) (bd_lvl _ _) hM hk hm h3).bnd

/-! ### Column sums -/

/-- A sum of numbers below `2^J`, regrouped by bit position: column `i` counts the summands with
bit `i`. -/
theorem sum_eq_sum_cols {N J : ℕ} (Z : ℕ → ℕ) (hZ : ∀ σ < N, Z σ < 2 ^ J) :
    ∑ σ ∈ range N, Z σ = ∑ i ∈ range J, (∑ σ ∈ range N, Z σ / 2 ^ i % 2) * 2 ^ i := by
  calc ∑ σ ∈ range N, Z σ = ∑ σ ∈ range N, ∑ i ∈ range J, Z σ / 2 ^ i % 2 * 2 ^ i :=
        sum_congr rfl fun σ hσ => (sum_bits_eq (hZ σ (mem_range.mp hσ))).symm
    _ = _ := by rw [sum_comm]; simp only [sum_mul]

/-- **The column adder.** Bit `j < J` of a sum of numbers below `2^J` is the carry-chain bit of
its columns. -/
theorem bit_sum_eq_bitOf {N J j : ℕ} (Z : ℕ → ℕ) (hZ : ∀ σ < N, Z σ < 2 ^ J) (hj : j < J) :
    (∑ σ ∈ range N, Z σ) / 2 ^ j % 2 = bitOf (fun i => ∑ σ ∈ range N, Z σ / 2 ^ i % 2) j :=
  div_two_pow_mod_two_eq_bitOf (sum_eq_sum_cols Z hZ) hj

/-- Column `i` of the sum over the schedules `σ < N`: the sum of the bits `i` of the networks. -/
def colT (B : Prog) (τT nT NT : Term) (i : Term) : Term := sumT NT fun σ => call4 B τT nT σ i

theorem fval_colT {B : Prog} (hB : Prog'.closed 4 B = true) {τT nT NT : Term} {τ n N : ℕ}
    (hτ : Val w τT env τ) (hn : Val w nT env n) (hN : Val w NT env N) :
    FVal w (colT B τT nT NT) env (fun i => ∑ σ ∈ range N, B.eval w [τ, n, σ, i]) :=
  fun pre _ _ hu => val_sumT (hN.ext pre) fun pre' _ _ hσ =>
    val_call4 hB ((hτ.ext pre).ext pre') ((hn.ext pre).ext pre') hσ (hu.ext pre')

theorem bd_colT {B : Prog} (hB : Prog'.closed 4 B = true) {τT nT NT : Term} {τ n N : ℕ}
    (hτ : Val w τT env τ) (hn : Val w nT env n) (hN : Val w NT env N) (hbτ : Bd w M τT env)
    (hbn : Bd w M nT env) (hbN : Bd w M NT env) {i : Term} {p : ℕ} (hi : Val w i env p)
    (hbi : Bd w M i env) (hNM : N ≤ M) (hsum : ∑ σ ∈ range N, B.eval w [τ, n, σ, p] ≤ M)
    (hbB : ∀ σ < N, B.Bounded w M [τ, n, σ, p]) : Bd w M (colT B τT nT NT i) env :=
  bd_sumT hN (fun pre' _ _ hσ => val_call4 hB (hτ.ext pre') (hn.ext pre') hσ (hi.ext pre')) hbN
    hNM hsum fun pre' _ q hq hσ hbσ => bd_call4 hB (hτ.ext pre') (hn.ext pre') hσ (hi.ext pre')
      (hbτ.ext pre') (hbn.ext pre') hbσ (hbi.ext pre') (hbB q hq)

/-! ### The column adder program -/

/-- **The column adder** over `[τ, n, j]`: `0` above the padded time, and otherwise the
carry-chain bit `j` of the columns of the sum over the schedules. -/
def adderT (k : ℕ) (B : Prog) : Term :=
  letT (call1 (schedProg k) (lvl 2)) fun N => letT (call1 padProg (lvl 2)) fun T =>
    ite (lt T (lvl 0)) (const 0) (bitOfT (colT B (lvl 2) (lvl 1) N) (lvl 0))

theorem lt_two_pow_sqrtLog (τ : ℕ) : τ < 2 ^ SqrtLog τ :=
  Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) (log2_add_one_le_sqrtLog τ))

/-- `numBlocks t ≤ SqrtLog t + 1`. This restates `WalkTerm.numBlocks_le_sqrtLog` from
WalkFacts, whose import closure is far larger than this module's; it should move to a
small module imported by both. -/
private theorem numBlocks_le_sqrtLog_aux {t : ℕ} (ht : 2 ≤ t) : numBlocks t ≤ SqrtLog t + 1 := by
  have hb : Nat.log 2 t + 1 ≤ blockLength t := by
    rw [blockLength, clog_eq_log_add_one]; exact Nat.succ_le_succ (Nat.log_mono_right (by omega))
  have h1 : numBlocks t ≤ t / blockLength t + 1 := by
    rw [numBlocks, Nat.ceilDiv_eq_add_pred_div]
    calc (t + blockLength t - 1) / blockLength t ≤ (t + blockLength t) / blockLength t :=
          Nat.div_le_div_right (by omega)
      _ = t / blockLength t + 1 := by rw [Nat.add_div_right _ (by omega)]
  have h2 : t / blockLength t ≤ t / (Nat.log 2 t + 1) := Nat.div_le_div_left hb (by omega)
  have h3 := div_log_le_sqrtLog' ht
  omega

/-- The value bounds of the column adder at the bound `2^((C + 4k + 8)·SqrtLog τ)`. -/
theorem adder_sizes (k C : ℕ) {τ : ℕ} (hτ : 2 ≤ τ) :
    2 * τ + 2 ≤ 2 ^ ((C + 4 * k + 8) * SqrtLog τ) ∧ k + 3 ≤ 2 ^ ((C + 4 * k + 8) * SqrtLog τ) ∧
      (k + 1) * numBlocks τ ≤ 2 ^ ((C + 4 * k + 8) * SqrtLog τ) ∧
      2 * 3 ^ ((k + 1) * numBlocks τ) ≤ 2 ^ ((C + 4 * k + 8) * SqrtLog τ) ∧
      2 ^ (C * SqrtLog τ) ≤ 2 ^ ((C + 4 * k + 8) * SqrtLog τ) := by
  have hS1 : 1 ≤ SqrtLog τ := Nat.le_add_left _ _
  have hτS := lt_two_pow_sqrtLog τ
  have hnb : numBlocks τ ≤ SqrtLog τ + 1 := numBlocks_le_sqrtLog_aux hτ
  set S := SqrtLog τ
  set x := (k + 1) * numBlocks τ
  have hx : 2 * x + 1 ≤ (4 * k + 8) * S := by
    have : x ≤ (k + 1) * (S + 1) := Nat.mul_le_mul_left _ hnb
    nlinarith [Nat.mul_le_mul_left k hS1]
  have hmono : ∀ m, m ≤ (C + 4 * k + 8) * S → 2 ^ m ≤ 2 ^ ((C + 4 * k + 8) * S) :=
    fun m hm => Nat.pow_le_pow_right (by norm_num) hm
  have h3 : 2 * 3 ^ x ≤ 2 ^ ((C + 4 * k + 8) * S) := by
    have h34 : 3 ^ x ≤ 2 ^ (2 * x) := by
      exact (Nat.pow_le_pow_left (show 3 ≤ 2 ^ 2 by norm_num) x).trans_eq (pow_mul 2 2 x).symm
    calc 2 * 3 ^ x ≤ 2 * 2 ^ (2 * x) := Nat.mul_le_mul_left _ h34
      _ = 2 ^ (2 * x + 1) := by rw [pow_succ]; ring
      _ ≤ _ := hmono _ (by nlinarith [Nat.zero_le (C * S)])
  have hCS : C + 4 * k + 8 ≤ (C + 4 * k + 8) * S := by
    simpa using Nat.mul_le_mul_left (C + 4 * k + 8) hS1
  have hSS : 8 * S ≤ (C + 4 * k + 8) * S := Nat.mul_le_mul_right _ (by omega)
  refine ⟨?_, ?_, ?_, h3, hmono _ (Nat.mul_le_mul_right _ (by omega))⟩
  · have : 2 * τ + 2 ≤ 2 ^ (S + 1) := by rw [pow_succ]; omega
    exact this.trans (hmono _ (by omega))
  · have : k + 3 < 2 ^ (k + 3) := Nat.lt_two_pow_self
    exact this.le.trans (hmono _ (by omega))
  · have h1 : x < 2 ^ x := Nat.lt_two_pow_self
    have h2 : 2 ^ x ≤ 3 ^ x := Nat.pow_le_pow_left (by norm_num) x
    omega

/-- **The sum over schedules** (the column adder of the proof of Theorem 7.1): the bits of the
block networks give the bits of the accept count at the padded time of every large clock. -/
theorem clockedBits_of_blockBits (h : BlockBits) : ClockedBits := by
  intro k State _ _ Mc
  obtain ⟨B, C, τ₀, hBc, hB⟩ := h k State Mc _ (Finite.equivFin State)
  refine ⟨closeAt 3 (adderT k B 3), C + 4 * k + 8, max τ₀ 2, closed_closeAt 3 _,
    fun w τ j hw hτ => ?_⟩
  have hτ0 : τ₀ ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ2 : 2 ≤ τ := le_trans (le_max_right _ _) hτ
  obtain ⟨hlin, hk3, hm, h3, hCM⟩ := adder_sizes k C hτ2
  set Mb := 2 ^ ((C + 4 * k + 8) * SqrtLog τ)
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

/-! ### The count test from the bits -/

/-- Bit `j ≤ T` of `b · 2^T`, for `b ≤ 1`. -/
theorem bit_mul_two_pow {b T j : ℕ} (hb : b ≤ 1) (hj : j ≤ T) :
    b * 2 ^ T / 2 ^ j % 2 = b * (if j = T then 1 else 0) := by
  rcases Nat.lt_or_ge j T with h | h
  · rw [ite_eq_right (show j ≠ T by omega), mul_zero]
    obtain ⟨d, rfl⟩ : ∃ d, T = j + (d + 1) := ⟨T - j - 1, by omega⟩
    rw [show b * 2 ^ (j + (d + 1)) = b * 2 ^ d * 2 * 2 ^ j by rw [pow_add, pow_succ]; ring,
      Nat.mul_div_cancel _ (Nat.two_pow_pos j), Nat.mul_mod_left]
  · have hjT : j = T := by omega
    subst hjT
    rw [ite_eq_left rfl, mul_one, Nat.mul_div_cancel _ (Nat.two_pow_pos j)]
    omega

/-- Two numbers below `2^J` differ iff one of their bits `j < J` differs. -/
theorem ne_iff_exists_bit_ne {A c J : ℕ} (hA : A < 2 ^ J) (hc : c < 2 ^ J) :
    A ≠ c ↔ ∃ j < J, A / 2 ^ j % 2 ≠ c / 2 ^ j % 2 := by
  constructor
  · intro hne
    by_contra hall
    simp only [not_exists, not_and, ne_eq, not_not] at hall
    apply hne
    rw [← sum_bits_eq hA, ← sum_bits_eq hc]
    exact sum_congr rfl fun j hj => by rw [hall j (mem_range.mp hj)]
  · rintro ⟨j, -, hj⟩ rfl
    exact hj rfl

/-- **The count test from the bits.** For `A ≤ 2^T` and `b ≤ 1`, the number of `j ≤ T` at which
bit `j` of `A` differs from that of `b · 2^T` is positive iff `A ≠ b · 2^T`. -/
theorem cnt_pos_iff {A T b : ℕ} (hA : A ≤ 2 ^ T) (hb : b ≤ 1) :
    0 < ∑ j ∈ range (T + 1),
        (1 - if A / 2 ^ j % 2 = b * (if j = T then 1 else 0) then 1 else 0) ↔
      A ≠ b * 2 ^ T := by
  have hT : 2 ^ T < 2 ^ (T + 1) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hc : b * 2 ^ T ≤ 2 ^ T := by
    calc b * 2 ^ T ≤ 1 * 2 ^ T := Nat.mul_le_mul_right _ hb
      _ = 2 ^ T := one_mul _
  rw [ne_iff_exists_bit_ne (A := A) (c := b * 2 ^ T) (J := T + 1) (by omega) (by omega),
    sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  refine exists_congr fun j => ?_
  rw [mem_range]
  constructor
  · rintro ⟨hj, hp⟩
    refine ⟨hj, ?_⟩
    rw [bit_mul_two_pow hb (show j ≤ T by omega)]
    intro heq
    rw [ite_eq_left heq] at hp
    simp at hp
  · rintro ⟨hj, hp⟩
    refine ⟨hj, ?_⟩
    rw [bit_mul_two_pow hb (show j ≤ T by omega)] at hp
    rw [ite_eq_right hp]
    exact Nat.one_pos

/-- **The count test** over `[τ, n, b]` from a bits program `P` over `[τ, n, j]`: the number of
`j ≤ paddedTime τ` at which bit `j` of the count differs from bit `j` of `b · 2^paddedTime τ`. -/
def cntBitsT (P : Prog) : Term :=
  letT (call1 padProg (lvl 2)) fun T =>
    sumT (add T (const 1)) fun j =>
      sub (const 1) (eqT (call3 P (lvl 2) (lvl 1) j) (mul (lvl 0) (eqT j T)))

/-- `2τ + 2 ≤ 2^(c·SqrtLog τ)` for `c ≥ 2`. -/
theorem lin_le_two_pow_sqrtLog (τ : ℕ) {c : ℕ} (hc : 2 ≤ c) :
    2 * τ + 2 ≤ 2 ^ (c * SqrtLog τ) := by
  have hS1 : 1 ≤ SqrtLog τ := Nat.le_add_left _ _
  have hτS := lt_two_pow_sqrtLog τ
  have h1 : 2 * τ + 2 ≤ 2 ^ (SqrtLog τ + 1) := by rw [pow_succ]; omega
  exact h1.trans (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

/-- **The clocked counter from the clocked bits.** -/
theorem clockedCounting_of_clockedBits (h : ClockedBits) : ClockedCounting := by
  intro k State _ _ Mc
  obtain ⟨P, C, τ₀, hPc, hP⟩ := h k State Mc
  refine ⟨closeAt 3 (cntBitsT P 3), C + 3, max τ₀ 2, closed_closeAt 3 _,
    fun w τ b hw hτ hb => ?_⟩
  have hτ0 : τ₀ ≤ τ := le_trans (le_max_left _ _) hτ
  have hτ2 : 2 ≤ τ := le_trans (le_max_right _ _) hτ
  set Mb := 2 ^ ((C + 3) * SqrtLog τ)
  have hlin : 2 * τ + 2 ≤ Mb := lin_le_two_pow_sqrtLog τ (by omega)
  have hCM : 2 ^ (C * SqrtLog τ) ≤ Mb := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
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

end Cslib.Complexity.NtimeDspace.Cross.Exact
