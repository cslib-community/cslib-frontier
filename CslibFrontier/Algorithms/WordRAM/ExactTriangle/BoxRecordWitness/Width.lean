/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness.Exec
public import CslibFrontier.Algorithms.WordRAM.ExactTriangle.RecordWitness.Width
import CslibFrontier.Computability.WordRAM.Admission

/-!
# Original-input admission for product-selected witness recovery

One positive width threshold covers the original producer/product admission, all real
descriptor/query/address arithmetic and both signed additions of original weights. It depends
on the original scalar headers and magnitude envelope, not on the physical width chosen by
the caller. The reserved product window is an address bound, not a charged clearing operation.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness

open Cslib.WordRAM RecordWitness
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The existing product's output slice precedes its admitted virtual-window boundary. -/
theorem outputBase_lt_window {m n Q : ℕ} (hN : D m ^ 18 ≤ n) :
    QueriedProduct.outputBase (21 * m) m n Q < CallableProduct.windowSize n Q := by
  have hbox : QueriedProduct.wordBudget (21 * m) m n Q ≤
      BoxProduct.wordBudget (21 * m) m (m / 9) n Q := by
    unfold BoxProduct.wordBudget
    omega
  exact ((QueriedProduct.outputBase_le_wordBudget (21 * m) m n Q).trans hbox).trans_lt
    (CallableBoxProduct.source_admission (Nat.div_le_self m 9) hN).2.2

/-- Every pointer and temporary of the actual per-record caller fits from the original
producer word bound and the actual chunk count. No intermediate fit certificate is supplied. -/
theorem physical_fits {w m n g p A heap Q : ℕ}
    (hheap : heap ≤ PreparationInput.wordBound n (D m) g p A)
    (hQ : Q ≤ n ^ 2) (hN : D m ^ 18 ≤ n)
    (hW : admissionWidth n (D m) g p A ≤ w + 2) :
    Fits (w + 2) (witnessWindow n (D m) g heap Q
      (QueriedProduct.outputBase (21 * m) m n Q)) :=
  physical_fits_of_lt_window hheap hQ (outputBase_lt_window hN) hW

end Cslib.Algorithms.WordRAM.ExactTriangle.BoxRecordWitness
