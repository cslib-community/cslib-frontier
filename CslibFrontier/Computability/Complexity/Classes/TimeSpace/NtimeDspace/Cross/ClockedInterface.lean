/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.Interfaces
public import CslibFrontier.Computability.Complexity.Classes.Time.AcceptCount
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cross.SqrtLogSublinear
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Closed

/-!
# The clocked counter (interface between Theorems 2.3 and 2.4 at an arbitrary clock)

The transfer theorem (Theorem 2.4) for a time bound `t` that need not be constructible tries the
clocks `τ = t₀, 2t₀, …`. At each clock it needs two tests on the accept count of a closed fair-coin
table at the padded time `paddedTime τ` (the length of the coin strings of the block networks at
clock `τ`, `sum_contraction_blockNetworkOf`):

* is the count different from `0`? (membership, at the final clock);
* is the count different from `2 ^ paddedTime τ`? (some replay still runs, for the halt marker of
  `HaltCount`).

`ClockedCounting` asks for one closed program over `[τ, n, b]` deciding whether the count differs
from `b · 2 ^ paddedTime τ` (`b ∈ {0, 1}`), in values below `2^(C·SqrtLog τ)`, for every input of
length `n ≤ τ` and every large clock `τ`. This is Theorem 2.3 at one clock (in space
`O(τ/√log τ)`) combined with the test of Theorem 2.4 at one clock; it follows from the bits of the
accept count (`Exact.clockedCounting_of_clockedBits`). `ClockedResidues` is a residue form.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open NtimeDspace.ProgLang NtimeDspace.ProgTerm NtimeDspace.SumProduct Cslib.Complexity
    Cslib.Complexity.CountingSimulation _root_.Turing

/-- **The clocked counter.** For every closed fair-coin table `M` there is a closed program `Q` over
`[τ, n, b]` with `0 < Q ↔ acceptCount M w (paddedTime τ) ≠ b · 2^(paddedTime τ)` and values below
`2^(C·SqrtLog τ)`, on every input `w` with `|w| ≤ τ` and every clock `τ ≥ τ₀`. -/
def ClockedCounting : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State),
    ∃ (Q : Prog) (C τ₀ : ℕ), Prog'.closed 3 Q = true ∧
      ∀ (w : List Bool) (τ b : ℕ), w.length ≤ τ → τ₀ ≤ τ → b ≤ 1 →
        (0 < Q.eval w [τ, w.length, b] ↔ M.acceptCount w (paddedTime τ) ≠ b * 2 ^ paddedTime τ) ∧
        Q.Bounded w (2 ^ (C * SqrtLog τ)) [τ, w.length, b]

/-- **The clocked residues** (a residue form of Theorem 2.3 at an arbitrary clock). For every
closed fair-coin table `M` there are closed programs `R` over `[τ, n, p]` and `Hp`, `Xp` over `[τ]`
such that, for every input `w` with `|w| ≤ τ` and every clock `τ ≥ τ₀`, the primes of the window
`(Hp τ, Xp τ]` have product above `2^(paddedTime τ + 1)`, the window ends below `(τ + 2)^C`, and `R`
computes the residue of the accept count at `paddedTime τ` modulo every prime of the window; all
values stay
below `2^(C·SqrtLog τ)`. -/
def ClockedResidues : Prop :=
  ∀ (k : ℕ) (State : Type) [Finite State] [DecidableEq State] (M : MultiTapePTM k Bool State),
    ∃ (R Hp Xp : Prog) (C τ₀ : ℕ), Prog'.closed 3 R = true ∧ Prog'.closed 1 Hp = true ∧
      Prog'.closed 1 Xp = true ∧
      ∀ (w : List Bool) (τ : ℕ), w.length ≤ τ → τ₀ ≤ τ →
        2 ^ (paddedTime τ + 1) < ∏ p ∈ (Finset.Ioc (Hp.eval w [τ])
            (Xp.eval w [τ])).filter Nat.Prime, p ∧
        2 ≤ Hp.eval w [τ] ∧ Xp.eval w [τ] ≤ (τ + 2) ^ C ∧
        Hp.Bounded w (2 ^ (C * SqrtLog τ)) [τ] ∧ Xp.Bounded w (2 ^ (C * SqrtLog τ)) [τ] ∧
        ∀ p, p.Prime → Hp.eval w [τ] < p → p ≤ Xp.eval w [τ] →
          R.eval w [τ, w.length, p] = M.acceptCount w (paddedTime τ) % p ∧
            R.Bounded w (2 ^ (C * SqrtLog τ)) [τ, w.length, p]

/-- **Theorem 1.1 for every `t(n) ≥ n`** (simultaneous time and space), as a statement. -/
def GeneralSimulation : Prop :=
  ∀ (t : ℕ → ℕ), (∀ n, n ≤ t n) → ∀ {A : Set (List Bool)}, A ∈ NTIME Turing.MultiTapeTM.encBits t →
    ∃ C, Turing.MultiTapeTM.DecidableInTimeAndSpace A Turing.MultiTapeTM.encBits
      (fun a => 2 ^ (C * SqrtLog (t a.length))) (fun a => C * SqrtLog (t a.length))

end Cslib.Complexity.NtimeDspace.Cross
