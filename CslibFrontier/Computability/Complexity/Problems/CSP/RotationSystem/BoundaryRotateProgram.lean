/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.CertificateReindex

/-!
# One directed boundary rotation on raw successor tables

The body-prefix occurrence count and boundary length determine the probe window.
Only that window is shifted; binary indices outside it stay fixed. Counts zero and one
return the entire supplied certificate, including malformed or surplus entries.

## Main definitions

* `OrderedBoundary.rotateBoundaryCertificate`: one forward probe-index shift, with its
  separate inverse lookup map and the existing transformed-zero fallback.
-/

public section

namespace Cslib.Complexity.CSP.OrderedBoundary

/-- Execute one left boundary-word rotation's numeric table transport. The reversed probe
moves old argument slots forward by one; lookup uses the inverse shift. No validity check
or entry-bound premise is used. Short boundaries retain the exact original certificate. -/
@[expose] def rotateBoundaryCertificate (M N : ℕ) (c : Graph.RotationCertificate) :
    Graph.RotationCertificate :=
  if N ≤ 1 then c else
    Graph.RotationCertificate.reindex c (2 * (M + N))
      (fun i => if 2 * M ≤ i ∧ i < 2 * (M + N) then
        2 * (M + ((i / 2 - M + 1) % N)) + i % 2 else i)
      (fun i => if 2 * M ≤ i ∧ i < 2 * (M + N) then
        2 * (M + ((i / 2 - M + N - 1) % N)) + i % 2 else i)

end Cslib.Complexity.CSP.OrderedBoundary
