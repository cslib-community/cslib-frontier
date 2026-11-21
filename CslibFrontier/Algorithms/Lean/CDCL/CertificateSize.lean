/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.CDCL.Watched
public import CslibFrontier.Logics.Propositional.Resolution.LRATLowerBound

/-! # The size of the CDCL solver's certificates

On an unsatisfiable formula, the CDCL solver (`Cslib.Algorithms.Lean.CDCL.solve`) returns an LRAT
certificate that `Cslib.Logic.PL.CNF.checkLRAT` accepts (`Cslib.Algorithms.Lean.CDCL.solve_unsat`).
Every accepted certificate translates to a resolution refutation with at most
`|φ| + min (H) (S · N)` lines, where `H` is its number of hints, `S` its number of steps and `N` the
number of variables (`Cslib.Logic.PL.CNF.refutableInSize_of_checkLRAT`). So the resolution lower
bounds apply to the solver's output:

* on the pigeonhole formula `PHP^{n+1}_n`, numbered along any injective map, the certificate
  satisfies `2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min (H) (S · (n + 1) n)`
  (`Cslib.Algorithms.Lean.CDCL.two_pow_le_solve_pigeonhole`), by Haken's theorem;
* for every `n ≥ 4392000` there is an unsatisfiable formula with `m ≤ 120 n` variables and at most
  `2 ^ 120 · n` clauses of width at most `120`, the Tseitin formula of an expander, on which the
  certificate satisfies `exp (n / (960 · 36000²)) ≤ 2 ^ 120 · n + min (H) (S · m)`
  (`Cslib.Algorithms.Lean.CDCL.exists_solve_exp_le`), by the bound of Ben-Sasson and Wigderson.

These bound the solver's output, not its running time, and hold for every certificate the checker
accepts (`Cslib.Logic.PL.CNF.two_pow_le_of_checkLRAT_pigeonhole`,
`Cslib.Logic.PL.CNF.exists_forall_checkLRAT_exp_le`); the solver contributes only that it returns
one. The number of steps `S` alone is at least `(2 ^ (n / 24) - (n + 1) - n (n + 1)²) / ((n + 1) n)`
on `PHP^{n+1}_n`, still exponential in `n`.

## Main results

* `Cslib.Algorithms.Lean.CDCL.two_pow_le_solve_pigeonhole`: the solver's certificates for the
  pigeonhole formulas are exponentially long.
* `Cslib.Algorithms.Lean.CDCL.exists_solve_exp_le`: its certificates for the Tseitin formulas of
  expanders are `2 ^ Ω(n)` long.
-/

public section

namespace Cslib.Algorithms.Lean.CDCL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

/-- On an unsatisfiable formula, the solver returns a certificate. -/
private theorem exists_solve_eq_unsat {φ : CNF ℕ} (h : ¬ φ.Satisfiable) :
    ∃ cert, solve φ = .unsat cert := by
  rcases hs : solve φ with σ | cert
  · exact absurd ⟨σ, solve_sat hs⟩ h
  · exact ⟨cert, rfl⟩

/-- **The CDCL solver's certificates for the pigeonhole formulas are exponentially long.** For an
injective map `f` numbering the variables of `PHP^{n+1}_n`, the solver returns a certificate for
the relabelled formula, and with `H` hints and `S` steps it satisfies
`2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min H (S · (n + 1) n)`. A corollary of Haken's theorem
through the translation of certificates to resolution
(`Cslib.Logic.PL.CNF.two_pow_le_of_checkLRAT_pigeonhole`); it bounds the output, not the running
time. -/
theorem two_pow_le_solve_pigeonhole {n : ℕ} {f : Fin (n + 1) × Fin n → ℕ}
    (hf : Function.Injective f) :
    ∃ cert, solve ((pigeonhole (n + 1) n).relabel f) = .unsat cert ∧
      2 ^ (n / 24) ≤ (n + 1) + n * (n + 1) ^ 2 +
        min (lratHintCount cert.toList) (cert.size * ((n + 1) * n)) := by
  obtain ⟨cert, hc⟩ := exists_solve_eq_unsat
    (by rw [satisfiable_relabel hf]; exact not_satisfiable_pigeonhole (by omega))
  exact ⟨cert, hc, two_pow_le_of_checkLRAT_pigeonhole hf (solve_unsat hc)⟩

/-- **The CDCL solver's certificates for the Tseitin formulas of expanders are `2 ^ Ω(n)`
long.** For every `n ≥ 4392000` there is an unsatisfiable formula with `m ≤ 120 n` variables and at
most `2 ^ 120 · n` clauses, of width at most `120`, on which, numbered along `Fin.val`, the solver
returns a certificate with `H` hints and `S` steps satisfying
`exp (n / (960 · 36000²)) ≤ 2 ^ 120 · n + min H (S · m)`. A corollary of the bound of Ben-Sasson
and Wigderson through the translation of certificates to resolution
(`Cslib.Logic.PL.CNF.exists_forall_checkLRAT_exp_le`); it bounds the output, not the running
time. -/
theorem exists_solve_exp_le :
    ∀ n ≥ 4392000, ∃ m ≤ 120 * n, ∃ φ : CNF (Fin m),
      φ.length ≤ 2 ^ 120 * n ∧ (∀ c ∈ φ, c.width ≤ 120) ∧
      ∃ cert, solve (φ.relabel Fin.val) = .unsat cert ∧
        Real.exp (n / (960 * 36000 ^ 2)) ≤
          ((2 ^ 120 * n + min (lratHintCount cert.toList) (cert.size * m) : ℕ) : ℝ) := by
  intro n hn
  obtain ⟨m, hm, φ, hlen, hw, hunsat, hsize⟩ := exists_forall_checkLRAT_exp_le n hn
  obtain ⟨cert, hc⟩ := exists_solve_eq_unsat
    (by rw [satisfiable_relabel Fin.val_injective]; exact hunsat)
  exact ⟨m, hm, φ, hlen, hw, cert, hc, hsize cert (solve_unsat hc)⟩

end Cslib.Algorithms.Lean.CDCL
