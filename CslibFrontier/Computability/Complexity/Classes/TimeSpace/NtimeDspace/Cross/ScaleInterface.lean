/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.ClockedInterface
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.SqrtLogGrowth

/-!
# The clocked counter and Theorem 1.1 at a general scale

`ClockedInterface.lean` states the interface between Theorems 2.3 and 2.4 for the scale `SqrtLog`.
Here the same statements take the scale `D` as a parameter, so that Theorem 2.4 can be run with the
space bound of other pieces, giving other bounds such as `D = RootLog 3`, i.e. `n / (log n)^{1/8}`:

* `ClockedResiduesAt D`, `ClockedCountingAt D`, `GeneralSimulationAt D`: the statements of
  `ClockedResidues`, `ClockedCounting` and `GeneralSimulation` with `D` in place of `SqrtLog`;
  at `D = SqrtLog` they are those definitions (`clockedResiduesAt_sqrtLog`, …).
* `Scale D`: the regularity Theorem 2.4 asks of `D`: `log₂ n + 1 ≤ D n`, linear changes of the
  argument change `D` by a constant factor, and `D` is sublinear. `scale_sqrtLog`, `scale_rootLog`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang NtimeDspace.ProgTerm NtimeDspace.SumProduct Cslib.Complexity
  Cslib.Complexity.CountingSimulation _root_.Turing Filter

/-- `ClockedResidues` at the scale `D`. -/
def ClockedResiduesAt (D : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State),
    ∃ (R Hp Xp : Prog) (C τ₀ : ℕ), Prog'.closed 3 R = true ∧ Prog'.closed 1 Hp = true ∧
      Prog'.closed 1 Xp = true ∧
      ∀ (w : List Bool) (τ : ℕ), w.length ≤ τ → τ₀ ≤ τ →
        2 ^ (paddedTime τ + 1) < ∏ p ∈ (Finset.Ioc (Hp.eval w [τ])
            (Xp.eval w [τ])).filter Nat.Prime, p ∧
        2 ≤ Hp.eval w [τ] ∧ Xp.eval w [τ] ≤ (τ + 2) ^ C ∧
        Hp.Bounded w (2 ^ (C * D τ)) [τ] ∧ Xp.Bounded w (2 ^ (C * D τ)) [τ] ∧
        ∀ p, p.Prime → Hp.eval w [τ] < p → p ≤ Xp.eval w [τ] →
          R.eval w [τ, w.length, p] = M.acceptCount w (paddedTime τ) % p ∧
            R.Bounded w (2 ^ (C * D τ)) [τ, w.length, p]

/-- `ClockedCounting` at the scale `D`. -/
def ClockedCountingAt (D : ℕ → ℕ) : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State),
    ∃ (Q : Prog) (C τ₀ : ℕ), Prog'.closed 3 Q = true ∧
      ∀ (w : List Bool) (τ b : ℕ), w.length ≤ τ → τ₀ ≤ τ → b ≤ 1 →
        (0 < Q.eval w [τ, w.length, b] ↔ M.acceptCount w (paddedTime τ) ≠ b * 2 ^ paddedTime τ) ∧
        Q.Bounded w (2 ^ (C * D τ)) [τ, w.length, b]

/-- `GeneralSimulation` at the scale `D`: every problem in `NTIME[t]`, `t(n) ≥ n`, is decided in
simultaneous time `2^(C·D(t n))` and space `C·D(t n)`. -/
def GeneralSimulationAt (D : ℕ → ℕ) : Prop :=
  ∀ (t : ℕ → ℕ), (∀ n, n ≤ t n) → ∀ {A : Set (List Bool)}, A ∈ NTIME Turing.MultiTapeTM.encBits t →
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace A Turing.MultiTapeTM.encBits
      (fun a => 2 ^ (C * D (t a.length))) (fun a => C * D (t a.length))

theorem clockedResiduesAt_sqrtLog : ClockedResiduesAt SqrtLog ↔ ClockedResidues := Iff.rfl

theorem clockedCountingAt_sqrtLog : ClockedCountingAt SqrtLog ↔ ClockedCounting := Iff.rfl

theorem generalSimulationAt_sqrtLog : GeneralSimulationAt SqrtLog ↔ GeneralSimulation := Iff.rfl

/-- The regularity of a space bound `D` that Theorem 2.4 uses. -/
structure Scale (D : ℕ → ℕ) : Prop where
  log_le : ∀ n, n.log2 + 1 ≤ D n
  linear : ∀ {τ m : ℕ} (a b : ℕ), 1 ≤ a → τ ≤ a * m + b → D τ ≤ 2 * (a + b + 1) * D m
  sublinear : ∀ c, ∀ᶠ n in atTop, c * D n + c ≤ n

theorem scale_sqrtLog : Scale SqrtLog :=
  ⟨log2_add_one_le_sqrtLog, fun a b ha h => sqrtLog_le_of_le_mul_add a b ha h, sqrtLog_sublinear⟩

namespace Scale

variable {D : ℕ → ℕ} (hD : Scale D)
include hD

theorem one_le (n : ℕ) : 1 ≤ D n := le_trans (Nat.le_add_left _ _) (hD.log_le n)

/-- `n < 2 ^ D n`. -/
theorem lt_two_pow (n : ℕ) : n < 2 ^ D n :=
  Nat.lt_log2_self.trans_le (Nat.pow_le_pow_right (by norm_num) (hD.log_le n))

end Scale

end Cslib.Complexity.NtimeDspace.Cross
