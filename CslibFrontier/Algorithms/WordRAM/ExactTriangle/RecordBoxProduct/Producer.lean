/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct.Exec
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordProduct.Producer

/-!
# Box products from genuine native producer outputs

The complete descriptor, original zero/one matrix blocks, coordinate spans and
occurrence sparsity are derived from the actual `Instances.Output`. The selected
record invokes the new compiled box product and retains the producer catalogue.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open RecordProduct

/-- Full adapter execution over a genuine producer output. Every descriptor and source-span
premise of `exec` is derived here from the actual output; none remains an independent caller
certificate. A following initialized client obtains this output by executing the producer. -/
theorem exec_of_output {W m n g p : ℕ} (values : ℕ → ℤ)
    (initial : Data 64) (x : Data 320)
    (h : Instances.Output n (D m) g p values initial (x.comap producerBank))
    (hD : 16 ≤ D m) (hg : 1 ≤ g) (hp : p ≠ 0) (hN : D m ^ 18 ≤ n)
    (hheaderD : initial.mem 1 = D m) (hheaderN : initial.mem 3 = n)
    (idx : InstanceIndex p)
    (hidx : idx ∈ instanceIndices (fun a b : Fin n => values (pairIndex (a, b))) (D m) g p)
    (hi : x.regs Reg.ordinal = recordOrdinal n (D m) g p values idx)
    (hfit : Fits W (2 * x.regs 42 +
      4 * CallableProduct.windowSize n (recordQueryCount n (D m) p values idx) + 1024)) :
    backend.OutputPost (W := W) (g := g) hD hN values x idx :=
  backend.exec_of_output values initial x h hD hg hp hN hheaderD hheaderN idx hidx hi hfit

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct
