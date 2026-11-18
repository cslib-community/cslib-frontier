/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Circuit
meta import CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning

/-!
# Quantum access to the ML-DSA signing experiment

Two coherent queries with a classical signing call between them restore an arbitrary device
state. The signing reply and log are those of the actual hedged signer throughout.
-/

set_option linter.privateModule false
set_option linter.hashCommand false

open Cslib Cslib.Crypto Cslib.Crypto.MLDSA.FIPS204 Cslib.Quantum Cslib.Probability

-- First bytes of SHAKE128 and SHAKE256 applied to the empty string, in wire order.
#guard List.ofFn (Xofs.shake.queryTable 2 1 (Xofs.queryAddress 2 false [] (by decide))) ==
  [true, true, true, true, true, true, true, false]
#guard List.ofFn (Xofs.shake.queryTable 2 1 (Xofs.queryAddress 2 true [] (by decide))) ==
  [false, true, true, false, false, false, true, false]

private theorem unquery {a b m : ℕ} (H : BitString a → BitString b)
    (st : DeviceState m Unit Unit) : (st.instruction H .query).instruction H .query = st := by
  let codes : OracleCircuit := [.query]
  let U := (OracleCircuit.toCircuit m H codes).matrix
  have cancel : U * U = 1 := by
    apply Subtype.ext
    ext i j
    have h := congrArg (fun ψ : Qubits m => ψ.ofLp i)
      (OracleCircuit.eval_toCircuit_replicate_query_pairs H 1 (ket j))
    change ((OracleCircuit.toCircuit m H (codes ++ codes)).eval (ket j)).ofLp i = _ at h
    simpa [Circuit.eval, OracleCircuit.toCircuit_append, Circuit.matrix_append, U, ket_apply,
      Matrix.one_apply, Matrix.mulVec, dotProduct, eq_comm] using h
  rw [DeviceState.instruction_eq_evolve, DeviceState.instruction_eq_evolve]
  change (st.evolve U).evolve U = st
  rw [← DeviceState.evolve_mul, cancel, DeviceState.evolve_one]

open QuantumSigningForger in
example (C : QuantumSigningForger) (H : Xofs) (s : Level) (sk : List Byte) (q : SigningQuery)
    (st : C.State) :
    ((C.commands H s sk (.inl .query) st).bind fun p =>
      (C.commands H s sk (.inr q) p.2).bind fun r =>
        (C.commands H s sk (.inl .query) r.2).map (fun u => (r.1, u.2))) =
      (H.signingOracle s sk q st.2).map (fun r => (r.1, st.1, r.2)) := by
  simp [commands, OracleComp.sumHandler, deviceHandler_query,
    Function.comp_def, unquery, PMF.map]
