/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.Certificate.Errors
import CslibFrontierTests.MSFCertificateProcedure

/-!
# Tests for the histories, schedule and estimator of the certificate procedure

On the triangle with a self-loop of `CslibFrontierTests.MSFCertificateProcedure` (weights the edge
indices), with the derandomized configuration for `γ = 1` (the schedule of Lemma 3.11, the
estimator of §3.5) and `msf` as the exact call, every hypothesis of the history bound holds. The
checks: the actual history is in the family of Lemma 3.10, the family has `log |𝓗| ≤ 7 √(m n)`
(here `t = 1`), the error bound of §3.6 applies, and the estimator's comparisons over the root
call are bounded. The tagged order makes a spoke win the tie with the same edge as a forest edge.

These are instantiation checks, not strong ones: with `t = 1` every round is bad for every edge,
so the error bound already follows from `#errors ≤ m`. The exact call `pure (msf ends w S)` reads
the weights, so it only shows that `ExactMsf` is satisfiable for each `w`; it is not a comparison
program. An honest exact minimum spanning forest program is the knot that M8 ties by induction.
-/

namespace CslibFrontierTests.MSFCertificateErrors

open Cslib Cslib.Query Cslib.Query.Certificate Cslib.Multigraph Finset
open CslibFrontierTests.MSFCertificateProcedure (ends w root root_wellFormed)

/-- The derandomized configuration with `γ = 1` and `msf` as the exact call. -/
noncomputable abbrev dcfg : Config (Fin 3) (Fin 4) :=
  Config.derandomized 1 one_pos fun ends S => pure (msf ends w S)

theorem hw : Function.Injective w := Fin.val_injective

theorem hmsf : dcfg.ExactMsf w := fun _ _ => rfl

/-- **Lemma 3.10, membership**: the history of the root call is a candidate history. -/
example : history dcfg w root ∈ histories dcfg.γ root :=
  history_mem_histories dcfg w hw hmsf root_wellFormed

/-- **Lemma 3.10, size**: at level `1` with `γ = 1`, `t = 1`, so `log |𝓗| ≤ 7 √(4 · 3)`. -/
example : Real.log #(histories 1 root) ≤ 7 * √(4 * 3) := by
  have h := log_card_histories_le 1 root
  simpa [levelT] using h

/-- **The errors of the root call** (§3.6): at most `11 √(4 · 3) + 4 · 4`. -/
example : (#(errors dcfg w root) : ℝ) ≤ 11 * √(4 * 3) + 4 * 4 := by
  have h := card_errors_le 1 one_pos (fun ends S => pure (msf ends w S)) hw hmsf root_wellFormed
  simpa [levelT] using h

/-- **The estimator's comparisons over the root call** (§3.5): at most `16 t² n + 49 t² √(m n)`
with `t = 1`, `n = 3` and `m = 4`. -/
example : ∑ i ∈ range (levelT dcfg.γ root.level ^ 2),
      ((estimator dcfg.γ root (snapshot dcfg (LEQuery.keyOracle w) root i).state
        (acting dcfg root i)).countQueries (LEQuery.keyOracle w) : ℝ) ≤
      16 * (levelT dcfg.γ root.level : ℝ) ^ 2 * 3 +
        49 * (levelT dcfg.γ root.level : ℝ) ^ 2 * √(4 * 3) := by
  have h := sum_countQueries_estimator_le dcfg w hw hmsf root_wellFormed
  simpa using h

/-- **Spokes win ties** (p. 20): edge `0` as a spoke beats edge `0` as a forest edge. -/
example : tagKey w (false, 0) < tagKey w (true, 0) := by
  decide

end CslibFrontierTests.MSFCertificateErrors
