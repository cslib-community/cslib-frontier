/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.RandomXof
import CslibFrontier.Crypto.Computational.MLDSA.RandomXofCoverage
import CslibFrontier.Crypto.Computational.MLDSA.RandomXofMask
import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Circuit
meta import CslibFrontier.Crypto.Computational.MLDSA.RandomXof

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

-- Even when the empty string is the only permitted input, the two SHAKE variants return
-- independent bytes. Equating the variants would give a distribution supported on the diagonal.
example (base : Xofs) : ((base.uniformPrefixes 0 1).map fun H =>
    (H.h128.byteAt [] 0, H.h256.byteAt [] 0)) = PMF.uniformOfFintype (Byte × Byte) := by
  let empty := word (a := 0) [] (by decide)
  have unique (w : RawWord 0) : w = empty := by
    obtain ⟨⟨n, hn⟩, bits⟩ := w
    obtain rfl : n = 0 := by lia
    have eq : bits = BitString.ofList 0 [] := Subsingleton.elim _ _
    cases eq
    rfl
  let e : Table 0 1 ≃ Byte := {
    toFun := fun t => t (empty, 0)
    invFun := fun b _ => b
    left_inv := by
      intro t
      funext ⟨w, i⟩
      rw [unique w, Subsingleton.elim i 0]
    right_inv := fun _ => rfl }
  have eq := PMF.uniformOfFintype_map_equiv ((Equiv.prodCongr e e).trans (Equiv.prodComm _ _))
  rw [independent_tables, PMF.uniformOfFintype_bind_map, PMF.map_comp]
  refine Eq.trans ?_ eq
  congr 1
  funext ⟨t₂, t₁⟩
  simp [byteAt_install, e, empty]

-- Algorithm 33 reads 481 bytes at this same 64-byte seed and little-endian nonce.
-- Both the secret sampler and Algorithm 34 must see the prefix of the same packed mask.
example {base H : Xofs} {s : Level} {a b : ℕ} {ha : 528 ≤ a} {hb : maskPolyBytes s ≤ b}
    {masks : MaskTable s} (h : H ∈ (base.sampleWithMasks ha hb masks).support)
    (seed : FixedBytes 64) (nonce : ℕ) :
    H.h256.readBytes (nonceInput seed.toList nonce) 481 =
      (packSigned (s.params.γ₁.log2 + 1) s.params.γ₁ (fun _ : Fin 1 => fun j =>
        ((masks (maskAddress seed nonce) j).val : ZMod 8380417))).take 481 := by
  rw [← Xofs.read_mask_of_mem_sampleWithMasks h seed nonce]
  exact (H.h256.take_read _ (show 481 ≤ maskPolyBytes s by cases s <;> decide)).symm

-- Request a signature on three bits and submit the reply against a different one-bit message.
private def switchMessage : QuantumSigningForger where
  addressBits := 2
  responseBytes := 1
  workQubits := 0
  program _ := .liftBind (.inr (.inr ⟨[], [true, false, true]⟩)) fun reply =>
    .pure ⟨[], [false], reply.getD []⟩

private theorem fits_three : switchMessage.MessagesFit 3 := by
  intro pk
  constructor
  · exact OracleComp.QueriesSatisfy.liftBind_iff.mpr
      ⟨le_rfl, fun _ => OracleComp.QueriesSatisfy.pure _⟩
  · intro f hf
    simp only [switchMessage, OracleComp.support, OracleComp.supportWith, Set.mem_iUnion,
      Set.mem_univ, Set.mem_singleton_iff, exists_prop, true_and] at hf
    obtain ⟨_, rfl⟩ := hf
    exact (by decide : 1 ≤ 3)

example : ¬ switchMessage.MessagesFit 2 := fun fit =>
  (by decide : ¬ 3 ≤ 2) (OracleComp.QueriesSatisfy.liftBind_iff.mp (fit []).1).1

-- The public key determines the cutoff for this forger. Doubling both windows and
-- changing both background streams preserves its whole ML-DSA-44 winning distribution.
example (lo hi : Xofs) :
    switchMessage.randomPrefixGame .mlDSA44 lo 10496 894 =
      switchMessage.randomPrefixGame .mlDSA44 hi 20992 1788 :=
  switchMessage.randomPrefixGame_stable .mlDSA44 fits_three (by decide) (by decide)
    (by decide) (by decide) lo hi
