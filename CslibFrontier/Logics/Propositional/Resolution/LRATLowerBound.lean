/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.Resolution.FromLRAT
public import CslibFrontier.Logics.Propositional.Resolution.Pigeonhole
public import CslibFrontier.Logics.Propositional.Resolution.TseitinExpander

/-! # Lower bounds on the size of LRAT certificates

A certificate that `Cslib.Logic.PL.CNF.checkLRAT` accepts becomes a resolution refutation with at
most `|φ| + min (H) (S · N)` lines, where `H` is the number of hints of the certificate, `S` its
number of steps and `N` the number of variables of the formula
(`Cslib.Logic.PL.CNF.refutableInSize_of_checkLRAT`). So the lower bounds on the size of
resolution refutations are lower bounds on the size of LRAT certificates, for every certificate
the checker accepts, whichever solver produced it.

The checker reads formulas over `ℕ`, so a formula over another type of variables is given to it
relabelled along an injective map, which changes neither its refutations' sizes
(`Cslib.Logic.PL.CNF.RefutableInSize.of_relabel`) nor its number of clauses.

* **Pigeonhole formulas.** By Haken's theorem
  (`Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole`), every accepted certificate for
  `PHP^{n+1}_n`, which has at most `(n + 1) + n (n + 1)²` clauses and `(n + 1) n` variables,
  satisfies `2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min (H) (S · (n + 1) n)`
  (`Cslib.Logic.PL.CNF.two_pow_le_of_checkLRAT_pigeonhole`).
* **Tseitin formulas on expanders.** By the bound of Ben-Sasson and Wigderson for the Tseitin
  formulas of the expander family (`Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le`),
  for every `n ≥ 4392000` there is an unsatisfiable formula with `m ≤ 120 n` variables and at most
  `2 ^ 120 · n` clauses of width at most `120` such that every accepted certificate satisfies
  `exp (n / (960 · 36000²)) ≤ 2 ^ 120 · n + min (H) (S · m)`
  (`Cslib.Logic.PL.CNF.exists_forall_checkLRAT_exp_le`).

Both are corollaries, original to this library, of the cited resolution lower bounds through the
translation. They bound the certificate, not the running time of a solver or of the checker.

## Main results

* `Cslib.Logic.PL.CNF.two_pow_le_of_checkLRAT_pigeonhole`: certificates for `PHP^{n+1}_n` are
  exponentially long.
* `Cslib.Logic.PL.CNF.exists_forall_checkLRAT_exp_le`: a family of formulas with `O(n)`
  variables and clauses whose certificates are `2 ^ Ω(n)` long.
-/

public section

namespace Cslib.Logic.PL.CNF

open Std.Tactic.BVDecide (LRAT.IntAction)

/-- A formula relabelled along any map has at most as many variables. -/
private theorem card_vars_relabel_le {V : Type*} [DecidableEq V] (f : V → ℕ) (φ : CNF V) :
    (φ.relabel f).vars.toFinset.card ≤ φ.vars.toFinset.card := by
  rw [vars_relabel, show (φ.vars.map f).toFinset = φ.vars.toFinset.image f by ext; simp]
  exact Finset.card_image_le

/-- An accepted certificate for a formula relabelled along an injective map gives a refutation of
the formula, of size bounded in its own number of clauses and of variables. -/
private theorem refutableInSize_of_checkLRAT_relabel {V : Type*} [DecidableEq V] {f : V → ℕ}
    (hf : Function.Injective f) {φ : CNF V} {cert : Array LRAT.IntAction}
    (h : (φ.relabel f).checkLRAT cert = true) :
    φ.RefutableInSize
      (φ.length + min (lratHintCount cert.toList) (cert.size * φ.vars.toFinset.card)) := by
  refine (refutableInSize_of_checkLRAT h).of_relabel hf |>.mono ?_
  have := Nat.mul_le_mul_left cert.size (card_vars_relabel_le f φ)
  have : (φ.relabel f).length = φ.length := List.length_map _
  omega

/-- **Accepted LRAT certificates for the pigeonhole formulas are exponentially long.** For an
injective map `f` numbering the variables of `PHP^{n+1}_n`, every certificate that
`Cslib.Logic.PL.CNF.checkLRAT` accepts for the relabelled formula, with `H` hints and `S` steps,
satisfies `2 ^ (n / 24) ≤ (n + 1) + n (n + 1)² + min H (S · (n + 1) n)`. A corollary of Haken's
theorem (`Cslib.Logic.PL.CNF.two_pow_le_of_refutableInSize_pigeonhole`) through the translation to
resolution (`Cslib.Logic.PL.CNF.refutableInSize_of_checkLRAT`). -/
theorem two_pow_le_of_checkLRAT_pigeonhole {n : ℕ} {f : Fin (n + 1) × Fin n → ℕ}
    (hf : Function.Injective f) {cert : Array LRAT.IntAction}
    (h : ((pigeonhole (n + 1) n).relabel f).checkLRAT cert = true) :
    2 ^ (n / 24) ≤
      (n + 1) + n * (n + 1) ^ 2 + min (lratHintCount cert.toList) (cert.size * ((n + 1) * n)) := by
  refine (two_pow_le_of_refutableInSize_pigeonhole
    (refutableInSize_of_checkLRAT_relabel hf h)).trans ?_
  have := Nat.mul_le_mul_left cert.size (card_toFinset_vars_pigeonhole_le (n + 1) n)
  have := length_pigeonhole_le (n + 1) n
  omega

/-- **A family of formulas whose accepted LRAT certificates are `2 ^ Ω(n)` long.** For every
`n ≥ 4392000` there is an unsatisfiable formula with `m ≤ 120 n` variables and at most
`2 ^ 120 · n` clauses, of width at most `120`, such that every certificate that
`Cslib.Logic.PL.CNF.checkLRAT` accepts for it, numbered along `Fin.val`, with `H` hints and `S`
steps, satisfies `exp (n / (960 · 36000²)) ≤ 2 ^ 120 · n + min H (S · m)`. The formula is the
Tseitin formula of an expander, as in `Cslib.Logic.PL.CNF.exists_forall_refutableInSize_exp_le`,
of whose resolution lower bound this is a corollary through the translation to resolution
(`Cslib.Logic.PL.CNF.refutableInSize_of_checkLRAT`). -/
theorem exists_forall_checkLRAT_exp_le :
    ∀ n ≥ 4392000, ∃ m ≤ 120 * n, ∃ φ : CNF (Fin m),
      φ.length ≤ 2 ^ 120 * n ∧ (∀ c ∈ φ, c.width ≤ 120) ∧ ¬ φ.Satisfiable ∧
      ∀ cert : Array LRAT.IntAction, (φ.relabel Fin.val).checkLRAT cert = true →
        Real.exp (n / (960 * 36000 ^ 2)) ≤
          ((2 ^ 120 * n + min (lratHintCount cert.toList) (cert.size * m) : ℕ) : ℝ) := by
  intro n hn
  obtain ⟨m, hm, φ, hlen, hw, hunsat, hsize⟩ := exists_forall_refutableInSize_exp_le n hn
  refine ⟨m, hm, φ, hlen, hw, hunsat, fun cert h => (hsize _
    (refutableInSize_of_checkLRAT_relabel Fin.val_injective h)).trans ?_⟩
  have := Nat.mul_le_mul_left cert.size
    ((Finset.card_le_univ φ.vars.toFinset).trans_eq (Fintype.card_fin m))
  exact_mod_cast (by omega :
    φ.length + min (lratHintCount cert.toList) (cert.size * φ.vars.toFinset.card) ≤
      2 ^ 120 * n + min (lratHintCount cert.toList) (cert.size * m))

end Cslib.Logic.PL.CNF
