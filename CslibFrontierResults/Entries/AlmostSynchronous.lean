/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

-- upstream: local-only (result registry collection)
import CslibFrontierResults.Registry
import CslibFrontier.Computability.PCP.TwoProverGame.AlmostSynchronous

/-! # Spectral rounding of almost-synchronous strategies -/

register_result "almost-synchronous-projective-spectral-mixture" where
  title := "Vidick: finite projective mixture of almost-synchronous symmetric strategies"
  topic := "nonlocal games"
  sources := [
    { paper := Vidick2022, theorem := "Theorem 3.1",
      locator := "arXiv:2103.02468v3, pp. 11 and 14–16, equations (19)–(20)" }
  ]
  theorems := [
    Cslib.PCP.QuantumStrategy.exists_projective_spectral_mixture,
    Cslib.PCP.QuantumStrategy.partialTraceRight_pureState_ofSpectralCut,
    Cslib.PCP.QuantumStrategy.spectralCutDensity_isDensityMatrix
  ]
  scope := "A finite symmetric tensor-product strategy in its joint Schmidt basis, with arbitrary \
    finite outcome and question sets and a question law given by a PMF. The cut probabilities and \
    totally mixed component densities depend only on the original spectrum. The weighted reduced \
    densities recover the original reduced state exactly. The projective components are \
    synchronous. Their average squared state-dependent error is at most 9δ + 10√(2δ). The defect δ \
    is one minus the average diagonal answer agreement. The finite convex sum follows the remark \
    after Theorem 3.1. This entry covers the symmetric-strategy theorem."
