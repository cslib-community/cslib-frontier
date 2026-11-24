/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Correctness
import CslibFrontierTests.MSFCertificateProcedure

/-!
# Tests for the correctness of the certificate procedure

On the triangle with a self-loop of `CslibFrontierTests.MSFCertificateProcedure`, with the trivial
schedule and estimator and an exact minimum spanning forest call, every hypothesis of Claim 3.5
and Lemma 3.7 holds (`hw`, `hmsf`, the ends of the edges among the vertices). The consequences
checked: the returned forest is an acyclic set of at most `n - 1 = 2` root edges (Claim 3.5), the
root rejects nothing, and the counting consequence of Lemma 3.7 bounds the unsupported edges.
-/

namespace CslibFrontierTests.MSFCertificateCorrectness

open Cslib Cslib.Query Cslib.Query.Certificate Cslib.Multigraph Finset
open CslibFrontierTests.MSFCertificateProcedure

theorem hw : Function.Injective w := Fin.val_injective

theorem hmsf : cfg.ExactMsf w := fun _ _ => rfl

theorem hS : ∀ e ∈ (univ : Finset (Fin 4)), ∀ v ∈ ends e, v ∈ (univ : Finset (Fin 3)) :=
  fun _ _ _ _ => mem_univ _

/-- The result of the root call. -/
noncomputable abbrev res : Result (Fin 4) :=
  (certificate cfg root).eval (LEQuery.keyOracle w)

/-- **Claim 3.5**: the returned forest is acyclic, so it has at most `n - 1 = 2` edges. -/
example : IsAcyclic ends ↑res.forest ∧ #res.forest ≤ 2 := by
  have h := sound_certificate hw hmsf root root_wellFormed
  refine ⟨h.forest_acyclic, ?_⟩
  have := h.forest_acyclic.card_le (X := univ) fun _ _ _ _ => mem_univ _
  simpa using this

/-- The root rejects nothing. -/
example : res.rejected = ∅ := rejected_certificate_root hw hmsf hS

/-- **The counting consequence of Lemma 3.7**: the unsupported root edges, plus the rejected edges,
number at most the errors over all calls. -/
example : #(unsupported ends w ↑res.forest univ) +
      ((calls cfg (LEQuery.keyOracle w) root).map fun c =>
        ∑ i ∈ range (levelT cfg.γ c.level ^ 2), #(absorbed cfg (LEQuery.keyOracle w) c i)).sum ≤
    ((calls cfg (LEQuery.keyOracle w) root).map fun c => #(errors cfg w c)).sum :=
  card_unsupported_add_sum_absorbed_le hw hmsf hS

end CslibFrontierTests.MSFCertificateCorrectness
