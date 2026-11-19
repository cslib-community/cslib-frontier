/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.DPLL
public import CslibFrontier.Logics.Propositional.Resolution.TreeLikePigeonhole

/-! # The size of the DPLL solver's refutations

On an unsatisfiable formula, the search of the DPLL solver (`Cslib.Algorithms.Lean.DPLL.solve`)
ends with a tree-like resolution refutation (`Cslib.Algorithms.Lean.DPLL.refutation?`), which the
solver compiles to the LRAT certificate it returns
(`Cslib.Algorithms.Lean.DPLL.solve_eq_unsat_iff`). This file bounds the size of that output from
both sides. These are statements about what the solver returns, not running times: no cost model
is involved.

**Upper bound.** The search branches only on variables that it has not assigned
(`Cslib.Algorithms.Lean.DPLL.OpenVars.fresh`), so along every path of its search tree it branches
on each variable at most once, and its search tree has depth at most the number `N` of distinct
variables of the formula, `φ.vars.toFinset.card`. A derivation built along such a tree has fewer
than `2 ^ (N + 1)` nodes (`Cslib.Algorithms.Lean.DPLL.size_lt_of_refutation?_eq_some`), and its
certificate has at most `2 ^ N` steps (`Cslib.Algorithms.Lean.DPLL.size_le_of_solve_eq_unsat`):
the certificate of a tree-like refutation has one RUP step for each resolution step and a final
empty-clause step, so as many steps as the refutation has leaves
(`Cslib.Logic.PL.CNF.Derivation.size_toLRAT`).

**Lower bound on pigeonhole formulas.** The solver works over `ℕ`, so the pigeonhole formula
`PHP^m_n` (`Cslib.Logic.PL.CNF.pigeonhole`) is given to it relabelled along an injective map
`f : Fin m × Fin n → ℕ`, such as `(i, j) ↦ n * i + j`. A tree-like refutation of the relabelled
formula gives one of `PHP^m_n` with the same number of nodes
(`Cslib.Logic.PL.CNF.Derivation.exists_size_eq_of_relabel`), so for `m > n` the lower bound of
Beyersdorff, Galesi and Lauria [BeyersdorffGalesiLauria2010, Theorem 2]
(`Cslib.Logic.PL.CNF.Derivation.pow_le_leafCount_pigeonhole`) applies: the solver returns a
refutation with at least `(n / 2 + 1) ^ (n / 2)` nodes
(`Cslib.Algorithms.Lean.DPLL.pow_half_le_size_refutation?_pigeonhole`) and a certificate with at
least `(n / 2 + 1) ^ (n / 2)` steps
(`Cslib.Algorithms.Lean.DPLL.pow_half_le_size_solve_pigeonhole`).
This is `2 ^ Ω(n log n)`; with `m = n + 1` there are `N = (n + 1) * n` variables, so in terms of
`N` it is `2 ^ Ω(√N log N)`. Earlier, Dantchev and Riis [DantchevRiis2001, Theorem 1] proved a
`2 ^ Ω(n log n)` lower bound for regular tree resolution through a factorial estimate; it is
historical context here, and the exact bound used is that of Beyersdorff, Galesi and Lauria.

## Main definitions

* `Cslib.Algorithms.Lean.DPLL.refutation?`: the refutation found by the search.

## Main results

* `Cslib.Algorithms.Lean.DPLL.solve_eq_unsat_iff`: the solver returns the certificate of that
  refutation.
* `Cslib.Algorithms.Lean.DPLL.size_lt_of_refutation?_eq_some`,
  `Cslib.Algorithms.Lean.DPLL.size_le_of_solve_eq_unsat`: fewer than `2 ^ (N + 1)` nodes and at
  most `2 ^ N` certificate steps.
* `Cslib.Algorithms.Lean.DPLL.pow_half_le_size_refutation?_pigeonhole`,
  `Cslib.Algorithms.Lean.DPLL.pow_half_le_size_solve_pigeonhole`: at least `(n / 2 + 1) ^ (n / 2)`
  nodes and certificate steps on `PHP^m_n`, `m > n`.

## References

* [O. Beyersdorff, N. Galesi, M. Lauria, *A lower bound for the pigeonhole principle in tree-like
  Resolution by asymmetric Prover–Delayer games*][BeyersdorffGalesiLauria2010]
* [S. Dantchev, S. Riis, *Tree resolution proofs of the weak pigeon-hole
  principle*][DantchevRiis2001]
-/

public section

namespace Cslib.Algorithms.Lean.DPLL

open Cslib.Logic.PL Cslib.Logic.PL.CNF

/-! ### The refutation found by the search -/

/-- The refutation found by the search from the empty partial assignment: `none` if the search
finds a model, and otherwise the tree-like refutation whose certificate `solve` returns. -/
@[expose] def refutation? (φ : CNF ℕ) : Option (φ.Derivation []) :=
  match dpll φ with
  | .sat _ _ => none
  | .unsat c d h => some (refutationOf c d h)

/-- The solver returns a certificate exactly when the search finds a refutation, and the
certificate is that of the refutation. -/
theorem solve_eq_unsat_iff {φ : CNF ℕ} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction} :
    solve φ = .unsat cert ↔ ∃ d, refutation? φ = some d ∧ d.toLRAT = cert := by
  unfold solve refutation?
  split <;> rename_i heq <;> simp [heq, eq_comm]

/-- The search finds a refutation of every unsatisfiable formula. -/
theorem exists_refutation?_eq_some {φ : CNF ℕ} (h : ¬ φ.Satisfiable) :
    ∃ d, refutation? φ = some d := by
  cases hs : solve φ with
  | sat σ => exact absurd ⟨σ, solve_sat hs⟩ h
  | unsat cert =>
    obtain ⟨d, hd, -⟩ := solve_eq_unsat_iff.1 hs
    exact ⟨d, hd⟩

/-! ### The upper bound -/

/-- A derivation found by the search from `π` with the open variables `vs` has fewer than
`2 ^ (vs.length + 1)` nodes: each branch assigns an open variable, so the two subsearches have one
open variable fewer. -/
private theorem size_search_lt (φ : CNF ℕ) : (fuel : ℕ) → (π : List (Literal ℕ)) → (vs : List ℕ) →
    (hvs : OpenVars φ π vs) → (hfuel : vs.length ≤ fuel) → {c : Clause ℕ} →
    {d : φ.Derivation c} → {h : ∀ l ∈ c, l.negate ∈ π} →
    search φ fuel π vs hvs hfuel = .unsat c d h → d.size < 2 ^ (vs.length + 1) := by
  intro fuel
  induction fuel with
  | zero =>
    intro π vs hvs hfuel c d h hs
    obtain rfl : vs = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [search] at hs
    split at hs
    · cases hs
      simp
    · split at hs
      · cases hs
      · exact absurd (all_any_holds ‹_› fun x hx => (hvs.covers x hx).resolve_left
          List.not_mem_nil) ‹_›
  | succ fuel ih =>
    intro π vs hvs hfuel c d h hs
    rw [search] at hs
    split at hs
    · cases hs
      simp
    · split at hs
      · cases hs
      · split at hs
        · exact absurd (all_any_holds ‹_› fun x hx =>
            (‹OpenVars φ π []›.covers x hx).resolve_left List.not_mem_nil) ‹_›
        · omega
        · rename_i x xs fuel' _ _ hfe _
          obtain rfl : fuel' = fuel := by omega
          split at hs
          rename_i v b hv _
          have hlen : ((x :: xs).erase v).length = xs.length := by
            rw [List.length_erase_of_mem hv, List.length_cons, Nat.add_sub_cancel]
          have hpow : 2 ^ ((x :: xs).length + 1) = 2 * 2 ^ (xs.length + 1) := by
            rw [List.length_cons, Nat.pow_succ, Nat.mul_comm]
          rw [hpow]
          dsimp only at hs
          split at hs
          · cases hs
          · rename_i c₁ d₁ h₁ hs₁
            have ih₁ := ih _ _ _ _ hs₁
            rw [hlen] at ih₁
            split at hs
            · split at hs
              · cases hs
              · rename_i c₂ d₂ h₂ hs₂
                have ih₂ := ih _ _ _ _ hs₂
                rw [hlen] at ih₂
                split at hs
                · have : d.size = d₁.size + d₂.size + 1 := by
                    cases b
                    · simp only [resolveBranches] at hs
                      cases hs
                      simp only [Derivation.size_resolvent]
                    · simp only [resolveBranches] at hs
                      cases hs
                      simp only [Derivation.size_resolvent]
                      omega
                  omega
                · cases hs
                  omega
            · cases hs
              omega

/-- Closing the clause of the search's derivation to the empty clause keeps the derivation. -/
private theorem size_refutationOf {φ : CNF ℕ} : (c : Clause ℕ) → (d : φ.Derivation c) →
    (h : ∀ l ∈ c, l.negate ∈ ([] : List (Literal ℕ))) → (refutationOf c d h).size = d.size
  | [], _, _ => rfl
  | l :: _, _, h => absurd (h l List.mem_cons_self) List.not_mem_nil

/-- **Upper bound on the size of the solver's refutations.** The refutation found by the search
has fewer than `2 ^ (N + 1)` nodes, where `N = φ.vars.toFinset.card` is the number of distinct
variables of `φ`. This bounds the output, not the running time. -/
theorem size_lt_of_refutation?_eq_some {φ : CNF ℕ} {d : φ.Derivation []}
    (h : refutation? φ = some d) : d.size < 2 ^ (φ.vars.toFinset.card + 1) := by
  unfold refutation? at h
  split at h
  · cases h
  · rename_i c d' hc hd
    cases h
    rw [size_refutationOf, List.card_toFinset]
    exact size_search_lt φ _ _ _ _ _ hd

/-- **Upper bound on the length of the solver's certificates.** A certificate returned by the
solver has at most `2 ^ N` steps, where `N = φ.vars.toFinset.card` is the number of distinct
variables of `φ`. This bounds the output, not the running time. -/
theorem size_le_of_solve_eq_unsat {φ : CNF ℕ} {cert : Array Std.Tactic.BVDecide.LRAT.IntAction}
    (h : solve φ = .unsat cert) : cert.size ≤ 2 ^ φ.vars.toFinset.card := by
  obtain ⟨d, hd, rfl⟩ := solve_eq_unsat_iff.1 h
  have hlt := size_lt_of_refutation?_eq_some hd
  have h2 := d.two_mul_leafCount_toDecisionTree
  rw [Nat.pow_succ] at hlt
  rw [d.size_toLRAT]
  omega

/-! ### The lower bound on pigeonhole formulas -/

/-- A tree-like refutation of `PHP^m_n` relabelled along an injective map, `m > n`, has at least
`(n / 2 + 1) ^ (n / 2)` leaves. -/
private theorem pow_half_le_leafCount_relabel_pigeonhole {m n : ℕ} {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) (hnm : n < m) (d : ((pigeonhole m n).relabel f).Derivation []) :
    (n / 2 + 1) ^ (n / 2) ≤ d.toDecisionTree.leafCount := by
  obtain ⟨d', hs⟩ := Derivation.exists_size_eq_of_relabel hf d
  have h₁ := d.two_mul_leafCount_toDecisionTree
  have h₂ := d'.two_mul_leafCount_toDecisionTree
  have hle := (Nat.pow_le_pow_left (by omega : n / 2 + 1 ≤ n + 1 - n / 2) (n / 2)).trans
    (d'.pow_le_leafCount_pigeonhole (n / 2) hnm)
  omega

/-- **The solver's refutations of the pigeonhole formulas have `2 ^ Ω(n log n)` nodes.** For
`m > n` and an injective map `f` numbering the variables of `PHP^m_n`, the search finds a refutation
of the relabelled formula, and it has at least `(n / 2 + 1) ^ (n / 2)` nodes. This is the bound of
[BeyersdorffGalesiLauria2010, Theorem 2] for every tree-like refutation, applied to the solver's;
it bounds the output, not the running time. -/
theorem pow_half_le_size_refutation?_pigeonhole {m n : ℕ} {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) (hnm : n < m) :
    ∃ d, refutation? ((pigeonhole m n).relabel f) = some d ∧ (n / 2 + 1) ^ (n / 2) ≤ d.size := by
  obtain ⟨d, hd⟩ := exists_refutation?_eq_some
    (by rw [satisfiable_relabel hf]; exact not_satisfiable_pigeonhole hnm)
  exact ⟨d, hd, (pow_half_le_leafCount_relabel_pigeonhole hf hnm d).trans
    d.leafCount_toDecisionTree_le_size⟩

/-- **The solver's certificates for the pigeonhole formulas have `2 ^ Ω(n log n)` steps.** For
`m > n` and an injective map `f` numbering the variables of `PHP^m_n`, the solver returns a
certificate for the relabelled formula, with at least `(n / 2 + 1) ^ (n / 2)` steps. It has one
step for each leaf of the refutation (`Cslib.Logic.PL.CNF.Derivation.size_toLRAT`), and the bound of
[BeyersdorffGalesiLauria2010, Theorem 2] holds for the leaves. This bounds the output, not the
running time. -/
theorem pow_half_le_size_solve_pigeonhole {m n : ℕ} {f : Fin m × Fin n → ℕ}
    (hf : Function.Injective f) (hnm : n < m) :
    ∃ cert, solve ((pigeonhole m n).relabel f) = .unsat cert ∧
      (n / 2 + 1) ^ (n / 2) ≤ cert.size := by
  obtain ⟨d, hd, -⟩ := pow_half_le_size_refutation?_pigeonhole hf hnm
  exact ⟨d.toLRAT, solve_eq_unsat_iff.2 ⟨d, hd, rfl⟩,
    d.size_toLRAT ▸ pow_half_le_leafCount_relabel_pigeonhole hf hnm d⟩

end Cslib.Algorithms.Lean.DPLL
