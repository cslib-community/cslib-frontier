/-
Copyright (c) 2026 Christian Reitwiessner, Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Matthew Doty
-/

module
import CslibFrontier.Computability.Machines.Turing.TM2.Computable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat
import Mathlib.Computability.Ackermann

/-! Computable functions as multi-tape machines: instances beyond primitive recursion, a run of
the finite-label stack program, and the converse direction of the characterization. -/

open Turing Turing.MultiTapeTM Turing.PartrecToTM2

/-- The diagonal of the Ackermann function is not primitive recursive, but it is computed by a
total multi-tape machine. -/
example : ¬Primrec (fun n => ack n n) ∧ IsComputable (fun n => ack n n)
    ((Encodable.encode' ℕ).trans encNat) ((Encodable.encode' ℕ).trans encNat) :=
  ⟨not_primrec_ack_self, (computable₂_ack.comp Computable.id Computable.id).isComputable⟩

/-- The finite-label program of the successor code halts on `[3]` with `[4]` on the main stack. -/
example : halt [4] ∈ TM2.Cfg.mapLabel Subtype.val <$>
    StateTransition.eval (TM2.step (finProgram .succ)) (finInit .succ [3]) := by
  rw [eval_finProgram]
  exact Part.mem_map halt (by simp [ToPartrec.Code.eval])

/-- A native transducer certificate for the binary successor gives Mathlib computability. -/
example : Computable Nat.succ :=
  isComputable_iff_computable.1 computableInTimeAndSpace_succ.isComputable
