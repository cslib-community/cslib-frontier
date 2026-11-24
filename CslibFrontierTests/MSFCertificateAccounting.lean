/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Accounting
import CslibFrontierTests.MSFCertificateCorrectness

/-!
# Tests for the accounting of the certificate procedure

On the triangle with a self-loop of `CslibFrontierTests.MSFCertificateProcedure`, with the trivial
schedule and estimator and an exact minimum spanning forest call, both hypotheses of Lemma 3.1 as
formalized hold: the estimator makes no comparison (hypothesis (ii) with `B = 0`), and every call
has at most `4 m / t` errors (hypothesis (i) with `A = 0`), since only the root has edges and its
`t` is `1`. So `Cslib.Query.Certificate.certificate_root_accounting` applies.
-/

namespace CslibFrontierTests.MSFCertificateAccounting

open Cslib Cslib.Query Cslib.Query.Certificate Cslib.Multigraph Finset
open CslibFrontierTests.MSFCertificateProcedure CslibFrontierTests.MSFCertificateCorrectness

/-- The estimator answers *find* for every edge, so no child has an edge. -/
theorem child_edges_eq_empty (o : {ι : Type} → LEQuery (Fin 4) ι → ι)
    (inst : Instance (Fin 3) (Fin 4)) (i : ℕ) : (child cfg o inst i).edges = ∅ := by
  rw [edges_child]
  refine filter_false_of_mem fun e _ => ?_
  simp only [estimate, maskAction]
  split <;> simp [cfg]

/-- Every call is the root or has no edge. -/
theorem eq_root_or_edges_eq_empty (o : {ι : Type} → LEQuery (Fin 4) ι → ι) :
    ∀ c ∈ calls cfg o root, c = root ∨ c.edges = ∅ :=
  forall_mem_calls cfg o (fun c _ _ i => Or.inr (child_edges_eq_empty o c i)) (Or.inl rfl)

/-- **Hypothesis (i)** holds with `A = 0`. -/
theorem errorBound : ErrorBound cfg w root 0 := fun c hc => by
  have hle : (#(errors cfg w c) : ℝ) ≤ #c.edges := by
    exact_mod_cast card_le_card (filter_subset _ _)
  rcases eq_root_or_edges_eq_empty _ c hc with rfl | h
  · have ht : levelT cfg.γ root.level = 1 := by simp [cfg, levelT]
    rw [ht]
    simp only [zero_mul, zero_add, Nat.cast_one, div_one]
    linarith [(Nat.cast_nonneg (#root.edges) : (0 : ℝ) ≤ _)]
  · rw [h] at hle ⊢
    simp only [card_empty, Nat.cast_zero] at hle ⊢
    simp [hle]

/-- **Hypothesis (ii)** holds with `B = 0`: the estimator makes no comparison. -/
theorem estCostBound : EstCostBound cfg w root 0 := fun c _ _ => by
  simp [estCost, cfg]

/-- **Lemma 3.1** applies to the trivial configuration: its hypotheses are satisfiable. -/
example : ∃ C : ℝ,
    (#((certificate cfg root).eval (LEQuery.keyOracle w)).forest +
        #(unsupported ends w ↑((certificate cfg root).eval (LEQuery.keyOracle w)).forest univ) +
        ((calls cfg (LEQuery.keyOracle w) root).map fun c =>
          ((msfInputs cfg (LEQuery.keyOracle w) c).map fun S' => (#S' : ℝ)).sum).sum ≤
      8 * #(univ : Finset (Fin 4)) / (1 : ℕ) + C * √(#(univ : Finset (Fin 4)) *
        #(univ : Finset (Fin 3)))) := by
  obtain ⟨C, -, h⟩ := certificate_root_accounting 1 le_rfl le_rfl
  exact ⟨C, (h cfg w univ ends univ rfl hw hmsf hS (by simp) errorBound estCostBound).1⟩

end CslibFrontierTests.MSFCertificateAccounting
