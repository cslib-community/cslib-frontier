/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.QuantumCommitmentRegister
public import CslibFrontier.Crypto.Computational.MLDSA.SharedDigest
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.RandomOracle
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Oracle
public import CslibFrontier.Probability.Product
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Tactic.PMFSwap

/-!
# Coherent key-only extraction with the FIPS 204 commitment digest

A clocked classical controller operates a persistent quantum device and can make coherent
XOR queries to the matrix and commitment tables. Its only input is the rounded public-key
bytes. Both the forger and the final byte verifier use the same fixed-length raw commitment
table. The verifier and the systematic lattice check use Algorithm 29 on its digest.

Dilithium v3.1 [BaiEtAl2021Dilithium], §§6.1–6.2.1, gives the SelfTargetMSIS adversary
coherent access to a function into the sparse challenge set. FIPS 204 [NISTFIPS204],
Algorithms 8 and 29, exposes and compares the digest before expanding it. This module
proves the forward extraction for this byte interface. A reduction to the polynomial-valued
oracle must still simulate the exposed digest register.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumKeyOnly

open Cslib.Probability Cslib.Quantum Turing Turing.MultiTapeTM OracleComp
open SharedDigest (GridPoint gridAddress)

variable (s : Level)

/-- One raw Algorithm 8 query word, returning all bits of its digest in little-endian order. -/
abbrev DigestTable := BitString s.commitmentInputBits → BitString (8 * digestBytes s)

/-- Read the digest at the literal FIPS word corresponding to a module product. An input
whose message representative has the wrong width is outside the verifier's interface. -/
def pointReply (H : DigestTable s) (p : ModuleSIS.SelfTarget.Point s.params.k 256 8380417) :
    FixedBytes (digestBytes s) :=
  if p.1.length = 512 then
    (Keccak.fixedBytesEquivBitsLE _).symm
      (H (BitString.ofList _ (commitmentInput s (highBitsVec s.params p.2) p.1)))
  else 0

private theorem pointReply_grid (H : DigestTable s) (p : GridPoint s) :
    pointReply s H (List.ofFn p.1, p.2.val) =
      (Keccak.fixedBytesEquivBitsLE _).symm (H (gridAddress s p)) := by
  simp only [pointReply, List.length_ofFn, ite_true]
  rfl

/-- On the full canonical grid the expanded random-oracle table has *independent*
coordinates, each with precisely the pushforward of a uniform digest through Algorithm 29.
This computes its joint law including the probability of exhaustion. -/
theorem expanded_grid_table_law :
    (PMF.uniformOfFintype (DigestTable s)).map (fun (H : DigestTable s) (p : GridPoint s) =>
      expandDigest s (pointReply s H (List.ofFn p.1, p.2.val))) =
        PMF.pi (fun _ : GridPoint s =>
          (PMF.uniformOfFintype (FixedBytes (digestBytes s))).map (expandDigest s)) := by
  classical
  let convertBytes := Equiv.piCongrRight fun _ : GridPoint s =>
    (Keccak.fixedBytesEquivBitsLE (digestBytes s)).symm
  have restriction := PMF.uniformOfFintype_pi_map_comp_embedding
    (α := BitString (8 * digestBytes s)) (gridAddress s)
  calc
    _ = (PMF.uniformOfFintype (DigestTable s)).map
        (fun H (p : GridPoint s) =>
          expandDigest s ((Keccak.fixedBytesEquivBitsLE _).symm (H (gridAddress s p)))) := by
      apply congrArg (fun f : DigestTable s → GridPoint s → Option Poly =>
        (PMF.uniformOfFintype (DigestTable s)).map f)
      funext H p
      exact congrArg (expandDigest s) (pointReply_grid s H p)
    _ = _ := by
      rw [PMF.pi_map, PMF.pi_uniformOfFintype, ← PMF.uniformOfFintype_map_equiv convertBytes,
        ← restriction, PMF.map_comp, PMF.map_comp]
      rfl

/-- The oracle word involves neither truncation nor padding on a verifier input. Substituting
the SHAKE256 commitment-digest register yields FIPS 204 byte verification at the supplied
matrix `A`. -/
theorem verify_readDigestRegister_iff (bytes : List Byte) (A : PublicMatrix s) (f : Forgery) :
    interpret (m := Id) (pointReply s (Xofs.shake.readDigestRegister s))
      (SharedDigest.verify s bytes A f) = true ↔
      verifyWithExpansion s (fun _ => some A) bytes f.message f.context f.signature =
        some true := by
  rw [SharedDigest.interpret_verify_congr (m := Id) bytes A f _ (SharedDigest.shakeReply s)]
  · exact SharedDigest.verify_shakeReply_iff s bytes A f
  · intro p hp _
    funext i
    simp only [pointReply, hp, ite_true, Xofs.readDigestRegister_apply, Equiv.symm_apply_apply,
      BitString.ofFn_ofList (commitmentInput_length s _ hp), SharedDigest.shakeReply,
      commitmentDigest, Xofs.commitmentDigest, List.get_eq_getElem]
    exact (ExtendableOutput.getElem_read _ _ i.isLt).symm

/-- Full matrix response in row, column, coefficient, bit order. Twenty-three low bits
recover the entire canonical representative modulo the FIPS modulus. -/
def matrixRegister : PublicMatrix s ↪ BitString (s.params.k * s.params.ℓ * 256 * 23) where
  toFun A idx :=
    let (coeff, bit) := finProdFinEquiv.symm idx
    let (entry, degree) := finProdFinEquiv.symm coeff
    let (row, col) := finProdFinEquiv.symm entry
    (A row col degree).val.testBit bit.val
  inj' := by
    intro A B h
    funext row col degree
    have bound (z : ZMod 8380417) := (ZMod.val_lt z).trans (by decide : 8380417 < 2 ^ 23)
    apply ZMod.val_injective 8380417
    apply BitString.lowBits_injective_of_lt (bound _) (bound _)
    rw [BitString.lowBits_eq_ofFn, BitString.lowBits_eq_ofFn]
    congr 1
    funext bit
    simpa only [Equiv.symm_apply_apply] using congrFun h
      (finProdFinEquiv (finProdFinEquiv (finProdFinEquiv (row, col), degree), bit))

/-- Two native device interfaces act on one joint quantum state. The first query XORs a
commitment digest. The second XORs all matrix entries in row, column, coefficient, bit order.
Both interfaces support gates and measurements on the same active wires. -/
private noncomputable def handler {m : ℕ} (H : DigestTable s)
    (E : FixedBytes 32 → PublicMatrix s) :
    (DeviceOperation ⊕ DeviceOperation) × List Bool →
      StateT (DeviceState m Unit Unit) PMF (List Bool)
  | (.inl op, word) => deviceWordHandler H
      (fun p : Empty × List Bool => p.1.elim (C := StateT Unit PMF (Fin 0 → Bool))) (.inl op, word)
  | (.inr op, word) => deviceWordHandler
      (fun x => matrixRegister s (E ((Keccak.fixedBytesEquivBitsLE 32).symm x)))
      (fun p : Empty × List Bool => p.1.elim (C := StateT Unit PMF (Fin 0 → Bool))) (.inl op, word)

private noncomputable def initial (m : ℕ) : DeviceState m Unit Unit :=
  ⟨pureState (ket ((fun _ => false), ())), isDensityMatrix_pureState (norm_ket _), ()⟩

/-- The output begins with a framed bit-string message and framed context bits, followed
by the signature bits. Non-byte-aligned context or signature fields decode to a rejecting
empty signature. -/
def readForgery (out : List Bool) : Forgery :=
  let tail := dropFrame out
  let ctx := unframe tail
  let sig := dropFrame tail
  if 8 ∣ ctx.length ∧ 8 ∣ sig.length then
    ⟨(bitsToFixedBytesBE (ctx.length / 8) ctx).toList, unframe out,
      (bitsToFixedBytesBE (sig.length / 8) sig).toList⟩
  else ⟨[], [], []⟩

private theorem decodeBytes_encode (bytes : List Byte) :
    (bitsToFixedBytesBE bytes.length (bytesToBitsBE bytes)).toList = bytes := by
  let out := (bitsToFixedBytesBE bytes.length (bytesToBitsBE bytes)).toList
  have hl : out.length = bytes.length := FixedBytes.length_toList _
  have bits : bytesToBitsBE out = bytesToBitsBE bytes :=
    bytesToBitsBE_bitsToFixedBytesBE _ _ (length_bytesToBitsBE bytes)
  rcases lt_trichotomy out bytes with h | h | h
  · exact ((lt_irrefl _) (bits ▸ (bytesToBitsBE_lt_iff_lt hl).2 h)).elim
  · exact h
  · exact ((lt_irrefl _) (bits ▸ (bytesToBitsBE_lt_iff_lt hl.symm).2 h)).elim

/-- Every message, context and byte signature is representable by a controller output. -/
theorem readForgery_encoded (f : Forgery) :
    readForgery (frame f.message ++ frame (bytesToBitsBE f.context) ++
      bytesToBitsBE f.signature) = f := by
  obtain ⟨ctx, msg, sig⟩ := f
  rw [List.append_assoc]
  unfold readForgery
  dsimp only
  rw [dropFrame_frame_append, unframe_frame_append, dropFrame_frame_append,
    unframe_frame_append, length_bytesToBitsBE, length_bytesToBitsBE]
  have div (n : ℕ) : 8 * n / 8 = n := by omega
  simp only [dvd_mul_right, and_self, ite_true, Forgery.mk.injEq, true_and]
  constructor <;> rw [div, decodeBytes_encode]

/-- One retained finite classical machine, clock and active device width. Its output is
interpreted by `readForgery`. Private fair coins and quantum measurements may drive its
later gates or coherent queries. -/
structure Controller where
  /-- Number of work tapes. -/
  tapes : ℕ
  /-- Classical finite control numbered from zero. -/
  states : ℕ
  /-- The machine whose commands control the quantum device. -/
  machine : MultiTapePTM tapes Bool (Fin states) (DeviceOperation ⊕ DeviceOperation)
  /-- Maximum number of machine steps. -/
  clock : ℕ
  /-- Number of zero-initialized active qubits. -/
  qubits : ℕ

private noncomputable def output (C : Controller) (H : DigestTable s)
    (E : FixedBytes 32 → PublicMatrix s) (key : List Byte) : PMF Forgery :=
  (ProbOracleComp.runWith (handler s H E) (C.machine.runOracle C.clock (bytesToBitsBE key))
    (initial C.qubits)).map fun result => readForgery result.1

/-- Fixed-table verification after the native coherent run. -/
noncomputable def forgeryGame (C : Controller) (H : DigestTable s)
    (E : FixedBytes 32 → PublicMatrix s) (rho : FixedBytes 32) (t : Fin s.params.k → Poly) : Game :=
  let bytes := encodePublic s rho.toList t
  (output s C H E bytes).map fun f =>
    interpret (m := Id) (pointReply s H) (SharedDigest.verify s bytes (E rho) f)

/-- Check the canonical full product, shortness and expanded digest of a systematic witness. -/
def accepts (H : DigestTable s)
    (M : Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly)
    (y : List Bool × (Fin (s.params.k + s.params.ℓ + 1) → Fin 256 → ℤ)) : Bool :=
  let v := ModuleSIS.SelfTarget.product M y.2
  decide (y.1.length = 512 ∧ SharedDigest.OnCommitmentGrid s v) &&
    ModuleSIS.SelfTarget.accepts (expandDigest s) (compressedSelfTargetRadius s.params 13)
      y.2 (pointReply s H (y.1, v))

/-- Run the same controller once, then extract the message and short systematic witness from
its final word. Quantum registers are discarded only after its final output. -/
noncomputable def solver (C : Controller) (H : DigestTable s)
    (E : FixedBytes 32 → PublicMatrix s) (rho : FixedBytes 32) (t : Fin s.params.k → Poly) :
    PMF (List Bool × (Fin (s.params.k + s.params.ℓ + 1) → Fin 256 → ℤ)) :=
  let bytes := encodePublic s rho.toList t
  (output s C H E bytes).map (SharedDigest.extract s ⟨E rho, t⟩ bytes)

/-- Every accepted byte forgery yields a short witness whose last polynomial is Algorithm 29
of the same oracle digest at its systematic product. This is a straight-line bound for
each table and public key, without measuring, rewinding or resampling any coherent query. -/
theorem forgeryGame_le_solver (C : Controller) (H : DigestTable s)
    (E : FixedBytes 32 → PublicMatrix s) (rho : FixedBytes 32) (t : Fin s.params.k → Poly) :
    forgeryGame s C H E rho t true ≤ ((solver s C H E rho t).map
      (accepts s H (SharedDigest.systematic s (E rho) t))) true := by
  simp only [forgeryGame, solver, PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
  apply PMF.bind_apply_mono_on_support
  intro f _
  by_cases hv : interpret (m := Id) (pointReply s H)
      (SharedDigest.verify s (encodePublic s rho.toList t) (E rho) f) = true
  · have h := SharedDigest.accepts_extract_of_verify rho (E rho) t (pointReply s H) f hv
    simp [hv, accepts, h.1, h.2]
  · simp [Bool.eq_false_of_not_eq_true hv]

/-- Sample each entire oracle once. Key generation reads the matrix at the published seed,
and the controller continues with the same coherent table. Secrets and errors are sampled
coefficientwise from the Dilithium short law. -/
noncomputable def keyOnlyGame (C : Controller) : Game := do
  let s₁ ← MatrixOracle.shortVectorLaw s s.params.ℓ
  let s₂ ← MatrixOracle.shortVectorLaw s s.params.k
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  let E ← PMF.uniformOfFintype (FixedBytes 32 → PublicMatrix s)
  Quantum.RandomOracle.sample fun H =>
    forgeryGame s C H E rho (moduleSISMap (E rho) s₁ + s₂)

/-- On the challenge `(A,t)`, program the public seed to `A` in the fixed matrix table before
any coherent query. The device implements XOR against that whole updated function. -/
noncomputable def distinguisher (C : Controller)
    (challenge : PublicMatrix s × (Fin s.params.k → Poly)) : Game := do
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  let E ← PMF.uniformOfFintype (FixedBytes 32 → PublicMatrix s)
  Quantum.RandomOracle.sample fun H =>
    forgeryGame s C H (Function.update E rho challenge.1) rho challenge.2

/-- Programming an independent challenge matrix at the published seed gives exactly the
honest joint law, including the entire device's coherent access to the matrix function. -/
theorem keyOnlyGame_eq_real (C : Controller) :
    keyOnlyGame s C = (ModuleLWE.sampleLaw (MatrixOracle.shortVectorLaw s s.params.ℓ)
      (MatrixOracle.shortVectorLaw s s.params.k)).bind (distinguisher s C) := by
  have plant (s₁ : Fin s.params.ℓ → Poly) (s₂ : Fin s.params.k → Poly) (rho : FixedBytes 32) :=
    PMF.bind_uniformOfFintype_update rho (fun E : FixedBytes 32 → PublicMatrix s =>
      Quantum.RandomOracle.sample fun H : DigestTable s =>
        forgeryGame s C H E rho (moduleSISMap (E rho) s₁ + s₂))
  simp only [Function.update_self] at plant
  simp only [keyOnlyGame, ModuleLWE.sampleLaw, distinguisher, pmf_norm, plant]
  pmf_swap

/-- The self-target experiment receives the public systematic matrix. It publishes the public
bytes reconstructed from its two nonidentity blocks and runs one coherent controller with
the digest table shared by its final witness test. -/
noncomputable def digestSelfTargetGame (C : Controller)
    (M : Matrix (Fin s.params.k) (Fin (s.params.k + s.params.ℓ + 1)) Poly) : Game := do
  let pk := SharedDigest.fullKey s M
  let rho ← PMF.uniformOfFintype (FixedBytes 32)
  let E ← PMF.uniformOfFintype (FixedBytes 32 → PublicMatrix s)
  Quantum.RandomOracle.sample fun H : DigestTable s =>
    (solver s C H (Function.update E rho pk.A) rho pk.t).map (accepts s H M)

/-- Finite key-only bound with two coherent random oracles. The first term is the explicit
distinguisher's advantage on the short-secret Module-LWE and uniform challenge laws. The
second is its straight-line systematic solver's success with the byte-digest oracle and
Algorithm 29. Both reductions use independent ideal auxiliary tables. -/
theorem keyOnly_le_decision_add_digestSelfTarget (C : Controller) :
    let real := ModuleLWE.sampleLaw (MatrixOracle.shortVectorLaw s s.params.ℓ)
      (MatrixOracle.shortVectorLaw s s.params.k)
    let uniform := PMF.uniformOfFintype (PublicMatrix s × (Fin s.params.k → Poly))
    (keyOnlyGame s C).succProbability ≤
      Game.advantage (real.bind (distinguisher s C)) (uniform.bind (distinguisher s C)) +
        Game.succProbability ((SharedDigest.instances s).bind (digestSelfTargetGame s C)) := by
  let uniform := PMF.uniformOfFintype (PublicMatrix s × (Fin s.params.k → Poly))
  have h : (uniform.bind (distinguisher s C)) true ≤
      ((SharedDigest.instances s).bind (digestSelfTargetGame s C)) true := by
    simp only [uniform, ← PMF.uniformOfFintype_prod, SharedDigest.instances_eq_sample,
      distinguisher, digestSelfTargetGame, Quantum.RandomOracle.sample_eq, pmf_norm,
      SharedDigest.fullKey_systematic]
    iterate 5
      apply PMF.bind_apply_mono_on_support
      intro _ _
    rename_i A _ t _ rho _ E _ H _
    simpa only [Function.update_self] using
      forgeryGame_le_solver s C H (Function.update E rho A) rho t
  rw [keyOnlyGame_eq_real]
  exact (Game.succProbability_le_add_of_advantage_le
    (g₁ := uniform.bind (distinguisher s C)) le_rfl).trans
      (by rw [add_comm]; exact add_le_add le_rfl (Game.succProbability_mono h))

end Cslib.Crypto.MLDSA.FIPS204.QuantumKeyOnly
