/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.ProgLength

/-!
# Deciders that search for a clock

The decider in the proof of the transfer theorem does not know its time bound.
It tries the clocks `t₀, 2t₀, 4t₀, …`, where `t₀` is computed from the input
length, and stops at the first clock at which a test reports that every
computation has halted; it then decides with that clock.

`clockStmt T0 H P` is this search as a structured counter program. It counts the
input bits into register `0` (`lengthStmt`), sets the clock register `1` to
`T0(n)`, evaluates the test `H` at `[t, n]` into register `2`, and while the test
is `0` doubles the clock and evaluates the test again. It finally evaluates the
decision term `P` at `[t, n]` into register `2`. Variable `0` of `H` and `P` is the
clock and variable `1` the input length.

## Main definitions

* `clockAt T0 w k`: the `k`-th clock `T0(|w|) * 2^k`.
* `clockStmt T0 H P`: the clock search followed by the decision term.

## Main results

* `decidable_of_prog_clock`: if the test is `0` at the clocks before a stage and
  positive at that stage, every value arising up to that stage is at most `2^K`
  with `K ≤ c * budget`, and `P` at the final clock decides `L`, then `L` is
  decidable in simultaneous time `2^(C * budget)` and space `C * budget`.
* `decidable_of_prog_clock_first`: the same with the stage taken to be the first
  clock at which the test is positive; bounds are needed only at clocks not
  preceded by a positive test.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.ProgLang

open _root_.Turing _root_.Turing.CounterProgram Structured Prog _root_.Turing.MultiTapeTM

/-- The `k`-th clock of the doubling search on input `w`: `T0(|w|) * 2^k`. -/
def clockAt (T0 : Prog) (w : List Bool) (k : ℕ) : ℕ := T0.eval w [w.length] * 2 ^ k

theorem clockAt_succ (T0 : Prog) (w : List Bool) (k : ℕ) :
    clockAt T0 w (k + 1) = clockAt T0 w k + clockAt T0 w k := by
  simp only [clockAt, pow_succ]; ring

theorem clockAt_mono (T0 : Prog) (w : List Bool) {k k' : ℕ} (h : k ≤ k') :
    clockAt T0 w k ≤ clockAt T0 w k' :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) h)

/-- The doubling loop: while register `2` is `0`, double the clock in register `1`
and evaluate the test into register `2`. -/
def clockLoop (H : Prog) : Stmt :=
  .loop (.reg 2) (.const 1) (.seq (.assign 1 (.add (.reg 1) (.reg 1))) (H.compile [1, 0] 2 4))

/-- The clock search, followed by the decision term, whose value ends in register `2`. -/
def clockStmt (T0 H P : Prog) : Stmt :=
  .seq lengthStmt
    (.seq (T0.compile [0] 1 4)
      (.seq (H.compile [1, 0] 2 4)
        (.seq (clockLoop H) (P.compile [1, 0] 2 4))))

/-- Registers `1` and `0` hold the environment `[t, n]`. -/
theorem envOK_clock {r : List ℕ} {t n : ℕ} (h0 : r.getD 0 0 = n) (h1 : r.getD 1 0 = t) :
    EnvOK [1, 0] [t, n] r 4 := by
  refine ⟨rfl, fun i hi => ?_⟩
  simp only [List.length_cons, List.length_nil] at hi
  match i, hi with
  | 0, _ => exact ⟨by norm_num, by simpa using h1⟩
  | 1, _ => exact ⟨by norm_num, by simpa using h0⟩

/-- The doubling loop from stage `k` with the test value in register `2` ends at
`stage` with the clock of that stage in register `1`. -/
theorem clockLoop_exec {w : List Bool} {B : ℕ} (hB : 2 ≤ B) (T0 H : Prog) (R stage : ℕ)
    (hR : 4 + H.span ≤ R)
    (halts : 0 < H.eval w [clockAt T0 w stage, w.length])
    (running : ∀ k < stage, H.eval w [clockAt T0 w k, w.length] = 0)
    (clock_le : clockAt T0 w stage ≤ B)
    (H_bounded : ∀ k ≤ stage, H.Bounded w B [clockAt T0 w k, w.length]) :
    ∀ d k (r : List ℕ), k + d = stage → r.length = R → r.getD 0 0 = w.length →
      r.getD 1 0 = clockAt T0 w k → r.getD 2 0 = H.eval w [clockAt T0 w k, w.length] →
      LeB B r →
      ∃ r', Exec w (LeB B) (clockLoop H) r r' ∧ r'.length = R ∧ r'.getD 0 0 = w.length ∧
        r'.getD 1 0 = clockAt T0 w stage ∧ LeB B r' := by
  intro d
  induction d with
  | zero =>
    intro k r hk hl h0 h1 h2 hb
    obtain rfl : k = stage := by omega
    refine ⟨r, .loop_done hb ?_, hl, h0, h1, hb⟩
    simp only [Expr.eval_reg, Expr.eval_const]
    omega
  | succ d ih =>
    intro k r hk hl h0 h1 h2 hb
    have hk' : k < stage := by omega
    have hcl : clockAt T0 w (k + 1) ≤ B := (clockAt_mono T0 w (by omega)).trans clock_le
    set r1 := r.set 1 ((Expr.add (.reg 1) (.reg 1)).eval r)
    have hv : (Expr.add (.reg 1) (.reg 1)).eval r = clockAt T0 w (k + 1) := by
      simp only [Expr.eval, h1, clockAt_succ]
    have hb1 : LeB B r1 := forall_set_le hb (hv ▸ hcl)
    have hl1 : r1.length = R := by simp [r1, hl]
    have h10 : r1.getD 0 0 = w.length := by rw [getD_set_ne _ (by norm_num)]; exact h0
    have h11 : r1.getD 1 0 = clockAt T0 w (k + 1) := by
      rw [getD_set_self _ (by omega)]; exact hv
    obtain ⟨r2, e2, l2, v2, fr2, b2⟩ := compile_correct (w := w) hB H
      [clockAt T0 w (k + 1), w.length] [1, 0] 2 4 r1 (envOK_clock h10 h11) (by norm_num)
      (by omega) hb1 (H_bounded (k + 1) (by omega))
    have h20 : r2.getD 0 0 = w.length := by rw [fr2 0 (by norm_num) (by norm_num)]; exact h10
    have h21 : r2.getD 1 0 = clockAt T0 w (k + 1) := by
      rw [fr2 1 (by norm_num) (by norm_num)]; exact h11
    obtain ⟨r', e', l', v0', v1', b'⟩ := ih (k + 1) r2 (by omega) (by rw [l2, hl1]) h20 h21 v2 b2
    refine ⟨r', .loop_step hb ?_ (.seq (.assign hb) e2) b2 e', l', v0', v1', b'⟩
    simp only [Expr.eval_reg, Expr.eval_const, h2, running k hk']
    norm_num

/-- **Clock search.** Suppose that on each input `a`, with `n = |enc a|` and clocks
`clockAt T0 (enc a) k = T0(n) * 2^k`, the test `H` at `[clock, n]` is `0` at every
stage before `stage a` and positive at `stage a`; that every value arising in `T0`,
in `H` at stages up to `stage a`, and in `P` at the final clock, and the final clock
itself, is at most `2^K a`, where `K a ≤ c * budget a`; and that `P` at the final
clock is positive exactly on `L`. Then `L` is decidable in simultaneous time
`2^(C * budget)` and space `C * budget`. -/
theorem decidable_of_prog_clock {α : Type} {enc : α ↪ List Bool} (L : Set α) (T0 H P : Prog)
    (budget K stage : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (K_pos : ∀ a, 1 ≤ K a) (K_le : ∀ a, K a ≤ c * budget a)
    (len_le : ∀ a, (enc a).length ≤ 2 ^ K a)
    (T0_bounded : ∀ a, T0.Bounded (enc a) (2 ^ K a) [(enc a).length])
    (halts : ∀ a, 0 < H.eval (enc a) [clockAt T0 (enc a) (stage a), (enc a).length])
    (running : ∀ a, ∀ k < stage a, H.eval (enc a) [clockAt T0 (enc a) k, (enc a).length] = 0)
    (clock_le : ∀ a, clockAt T0 (enc a) (stage a) ≤ 2 ^ K a)
    (H_bounded : ∀ a, ∀ k ≤ stage a,
      H.Bounded (enc a) (2 ^ K a) [clockAt T0 (enc a) k, (enc a).length])
    (P_bounded : ∀ a,
      P.Bounded (enc a) (2 ^ K a) [clockAt T0 (enc a) (stage a), (enc a).length])
    (decides : ∀ a,
      (1 ≤ P.eval (enc a) [clockAt T0 (enc a) (stage a), (enc a).length] ↔ a ∈ L)) :
    ∃ C, DecidableInTimeAndSpace L enc (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  set R := T0.span + H.span + P.span + 4
  have hbudget (a : α) : 1 ≤ budget a := (Nat.le_add_left _ _).trans (logarithmic a)
  have hreg (a : α) {x : List ℕ} (hx : LeB (2 ^ K a) x) (hl : x.length = R) :
      (encList encNat x).length ≤ (R * (2 * c + 3)) * budget a := by
    refine (encList_le_of_LeB hx).trans ?_
    rw [hl, Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (by nlinarith [K_le a, hbudget a])
  have hB (a : α) : 2 ≤ 2 ^ K a := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (K_pos a); simpa using this
  have run (a : α) : ∃ final, Exec (enc a) (LeB (2 ^ K a)) (clockStmt T0 H P)
      (List.replicate R 0) final ∧
      final.length = R ∧
      final.getD 2 0 = P.eval (enc a) [clockAt T0 (enc a) (stage a), (enc a).length] ∧
      LeB (2 ^ K a) final := by
    set w := enc a
    set r0 : List ℕ := List.replicate R 0
    have hz : LeB (2 ^ K a) r0 := fun x hx => by
      rw [List.eq_of_mem_replicate hx]; exact Nat.zero_le _
    set r1 := r0.set 1 1
    have hb1 : LeB (2 ^ K a) r1 := forall_set_le hz ((hB a).trans' (by norm_num))
    have hlen1 : r1.length = R := by simp [r1, r0]
    -- count the input bits into register `0`
    obtain ⟨r2, e2, l2, v2, -, b2⟩ := lengthLoop_exec (w := w) (len_le a)
      ((hB a).trans' (by norm_num)) w.length r1
      (by simp [r1, r0, List.getD_eq_getElem?_getD, R])
      (by simp [r1, r0, List.getD_eq_getElem?_getD, R])
      (by rw [hlen1]; omega) hb1
    -- the first clock into register `1`
    obtain ⟨r3, e3, l3, v3, fr3, b3⟩ := compile_correct (w := w) (B := 2 ^ K a) (hB a)
      T0 [w.length] [0] 1 4 r2
      ⟨rfl, fun i hi => by
        simp only [List.length_singleton, Nat.lt_one_iff] at hi
        subst hi; simpa using v2⟩
      (by norm_num) (by rw [l2, hlen1]; omega) b2 (T0_bounded a)
    have h30 : r3.getD 0 0 = w.length := by rw [fr3 0 (by norm_num) (by norm_num)]; exact v2
    have h31 : r3.getD 1 0 = clockAt T0 w 0 := by rw [v3]; simp [clockAt]
    -- the first test into register `2`
    obtain ⟨r4, e4, l4, v4, fr4, b4⟩ := compile_correct (w := w) (B := 2 ^ K a) (hB a)
      H [clockAt T0 w 0, w.length] [1, 0] 2 4 r3 (envOK_clock h30 h31) (by norm_num)
      (by rw [l3, l2, hlen1]; omega) b3 (H_bounded a 0 (Nat.zero_le _))
    have h40 : r4.getD 0 0 = w.length := by rw [fr4 0 (by norm_num) (by norm_num)]; exact h30
    have h41 : r4.getD 1 0 = clockAt T0 w 0 := by
      rw [fr4 1 (by norm_num) (by norm_num)]; exact h31
    -- the doubling loop
    obtain ⟨r5, e5, l5, v50, v51, b5⟩ := clockLoop_exec (w := w) (hB a) T0 H R (stage a)
      (by omega) (halts a) (running a) (clock_le a) (H_bounded a) (stage a) 0 r4
      (by omega) (by rw [l4, l3, l2, hlen1]) h40 h41 v4 b4
    -- the decision at the final clock into register `2`
    obtain ⟨r6, e6, l6, v6, -, b6⟩ := compile_correct (w := w) (B := 2 ^ K a) (hB a)
      P [clockAt T0 w (stage a), w.length] [1, 0] 2 4 r5 (envOK_clock v50 v51) (by norm_num)
      (by rw [l5]; omega) b5 (P_bounded a)
    exact ⟨r6, .seq (.seq (.assign hz) e2) (.seq e3 (.seq e4 (.seq e5 e6))),
      by rw [l6, l5], v6, b6⟩
  choose final hfinal using run
  refine Structured.decidable_of_exec L (clockStmt T0 H P) 2 R budget
    (R * (2 * c + 3)) logarithmic final (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · obtain ⟨e, -⟩ := hfinal a
    exact (exec_weaken e fun x hx hl => hreg a hx (by simpa using hl)).1
  · obtain ⟨_, l, _, b⟩ := hfinal a
    exact hreg a b l
  · obtain ⟨_, _, v, _⟩ := hfinal a
    rw [v]; exact decides a

/-- **Clock search, first positive test.** The search stops at the first clock
at which the test `H` is positive, which exists by `stops`. Bounds are required
only at clocks `k` at which every earlier test is `0`, and correctness of `P` only at
such clocks with a positive test. -/
theorem decidable_of_prog_clock_first {α : Type} {enc : α ↪ List Bool} (L : Set α)
    (T0 H P : Prog) (budget K : α → ℕ) (c : ℕ)
    (logarithmic : ∀ a, (enc a).length.log2 + 1 ≤ budget a)
    (K_pos : ∀ a, 1 ≤ K a) (K_le : ∀ a, K a ≤ c * budget a)
    (len_le : ∀ a, (enc a).length ≤ 2 ^ K a)
    (T0_bounded : ∀ a, T0.Bounded (enc a) (2 ^ K a) [(enc a).length])
    (stops : ∀ a, ∃ k, 0 < H.eval (enc a) [clockAt T0 (enc a) k, (enc a).length])
    (H_bounded : ∀ a k, (∀ j < k, H.eval (enc a) [clockAt T0 (enc a) j, (enc a).length] = 0) →
      H.Bounded (enc a) (2 ^ K a) [clockAt T0 (enc a) k, (enc a).length] ∧
        clockAt T0 (enc a) k ≤ 2 ^ K a)
    (P_correct : ∀ a k, (∀ j < k, H.eval (enc a) [clockAt T0 (enc a) j, (enc a).length] = 0) →
      0 < H.eval (enc a) [clockAt T0 (enc a) k, (enc a).length] →
      P.Bounded (enc a) (2 ^ K a) [clockAt T0 (enc a) k, (enc a).length] ∧
        (1 ≤ P.eval (enc a) [clockAt T0 (enc a) k, (enc a).length] ↔ a ∈ L)) :
    ∃ C, DecidableInTimeAndSpace L enc (fun a => 2 ^ (C * budget a)) (fun a => C * budget a) := by
  classical
  have running (a : α) : ∀ k < Nat.find (stops a),
      H.eval (enc a) [clockAt T0 (enc a) k, (enc a).length] = 0 := fun k hk =>
    Nat.eq_zero_of_not_pos (Nat.find_min (stops a) hk)
  have before (a : α) {k : ℕ} (hk : k ≤ Nat.find (stops a)) :
      ∀ j < k, H.eval (enc a) [clockAt T0 (enc a) j, (enc a).length] = 0 :=
    fun j hj => running a j (hj.trans_le hk)
  exact decidable_of_prog_clock L T0 H P budget K (fun a => Nat.find (stops a)) c logarithmic
    K_pos K_le len_le T0_bounded (fun a => Nat.find_spec (stops a)) running
    (fun a => (H_bounded a _ (before a le_rfl)).2)
    (fun a k hk => (H_bounded a k (before a hk)).1)
    (fun a => (P_correct a _ (before a le_rfl) (Nat.find_spec (stops a))).1)
    (fun a => (P_correct a _ (before a le_rfl) (Nat.find_spec (stops a))).2)

end Cslib.Complexity.NtimeDspace.ProgLang
