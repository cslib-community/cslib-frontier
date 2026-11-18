/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SignedMatrix
public import CslibFrontier.Computability.Circuit.Quantum.Oracle.Controller.Handler
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Crypto.Game.CloseTo
import CslibFrontier.Probability.PMF.Bool

/-!
# Adaptive quantum queries and classical FIPS 204 signing

The adversary receives the generated public bytes and controls one persistent quantum register.
Its elementary gates, coherent XOR queries, single-wire measurements and classical requests for
hedged signatures may depend on previous replies. The two raw XOFs used by the device are also
used by [FIPS 204][NISTFIPS204], Algorithms 2, 3, 6, 7 and 8. This is the measured-signing
access convention of [Dilithium v3.1][BaiEtAl2021Dilithium], §6.2, equation (6).
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204

open Cslib.Probability Cslib.Quantum

namespace Xofs

/-- Encode a raw word of at most `a` bits in the coherent address register. The first bit
selects SHAKE256 when set and SHAKE128 otherwise. Leading zero padding and a one-bit delimiter
preserve the input length, including empty inputs and inputs starting with zero. -/
def queryAddress (a : ℕ) (strength : Bool) (x : List Bool) (_ : x.length ≤ a) :
    BitString (a + 2) :=
  Fin.cons strength (BitString.ofList (a + 1) (List.replicate (a - x.length) false ++ true :: x))

private def unpad : List Bool → Option (List Bool)
  | [] => none
  | true :: x => some x
  | false :: x => unpad x

private theorem unpad_word (k : ℕ) (x : List Bool) :
    unpad (List.replicate k false ++ true :: x) = some x := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [List.replicate_succ, List.cons_append, unpad] using ih

/-- The XOR oracle's output bits in FIPS 202 least-significant-bit-first order.
An address without a delimiter has the all-zero response. -/
def queryTable (H : Xofs) (a bytes : ℕ) (address : BitString (a + 2)) : BitString (8 * bytes) :=
  match unpad (List.ofFn (fun i : Fin (a + 1) => address i.succ)) with
  | none => 0
  | some x => BitString.ofList (8 * bytes)
      (Keccak.bytesToBitsLE ((if address 0 then H.h256 else H.h128).read x bytes))

/-- A coherent query at each encodable raw word reads the very stream used by FIPS, at
the full device response length. Shorter reads use its prefix. -/
theorem queryTable_queryAddress (H : Xofs) (a bytes : ℕ) (strength : Bool) (x : List Bool)
    (hx : x.length ≤ a) :
    List.ofFn (H.queryTable a bytes (queryAddress a strength x hx)) =
      Keccak.bytesToBitsLE ((if strength then H.h256 else H.h128).read x bytes) := by
  have len : (List.replicate (a - x.length) false ++ true :: x).length = a + 1 := by
    simp only [List.length_append, List.length_replicate, List.length_cons]
    lia
  simp only [queryTable, queryAddress, Fin.cons_succ, BitString.ofFn_ofList len, unpad_word,
    Fin.cons_zero]
  apply BitString.ofFn_ofList
  let stream := if strength then H.h256 else H.h128
  change (Keccak.bytesToBitsLE (stream.read x bytes)).length = 8 * bytes
  have lenRead := stream.length_read x bytes
  simp [Keccak.bytesToBitsLE, Keccak.byteBitsLE, lenRead, Nat.mul_comm]

/-- Sample one finite prefix table for both raw XOFs before the execution. Each raw input of
at most `a` bits receives `bytes` independent uniform bytes for each SHAKE variant. The
background supplies longer inputs and bytes beyond these prefixes. -/
noncomputable def uniformPrefixes (background : Xofs) (a bytes : ℕ) : PMF Xofs :=
  (PMF.uniformOfFintype (BitString (a + 2) → FixedBytes bytes)).map fun T =>
    let row (strength : Bool) (x : List Bool) :=
      if h : x.length ≤ a then some ((T (queryAddress a strength x h)).toList) else none
    ⟨background.h128.withPrefixes (row false), background.h256.withPrefixes (row true)⟩

end Xofs

/-- An adaptive program runs elementary quantum instructions and asks for classical signatures.
The argument and XOR output registers fit alongside the stated number of work qubits. The only
initial classical input is the published key. -/
structure QuantumSigningForger where
  /-- Longest raw bit string addressable by a coherent query. -/
  addressBits : ℕ
  /-- Number of output bytes XORed by a coherent query. -/
  responseBytes : ℕ
  /-- Additional zero-initialized working qubits. -/
  workQubits : ℕ
  /-- Direct gates, coherent queries, measurements, classical signing calls and private coins. -/
  program : List Byte → ProbOracleComp (OracleSpec.sum
    (fun _ : DeviceRequest (addressBits + 2 + 8 * responseBytes + workQubits) Empty => List Bool)
    (fun _ : SigningQuery => Option (List Byte))) Forgery

namespace QuantumSigningForger

private abbrev Width (C : QuantumSigningForger) :=
  C.addressBits + 2 + 8 * C.responseBytes + C.workQubits

private abbrev Device (C : QuantumSigningForger) := DeviceState (Width C) Unit Unit

private abbrev State (C : QuantumSigningForger) := Device C × List Forgery

private noncomputable def initial (C : QuantumSigningForger) : State C :=
  (⟨pureState (ket ((fun _ => false), ())), isDensityMatrix_pureState (norm_ket _), ()⟩, [])

private noncomputable def commands (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (sk : List Byte) := OracleComp.sumHandler (m := StateT (State C) PMF)
    (spec₁ := fun _ : DeviceRequest (Width C) Empty => List Bool)
    (spec₂ := fun _ : SigningQuery => Option (List Byte))
    (fun cmd (st : State C) => (deviceHandler (m := Width C) (κ := Unit)
      (H.queryTable C.addressBits C.responseBytes)
      (fun p : Empty × List Bool => p.1.elim (C := StateT Unit PMF (Fin 0 → Bool))) cmd st.1).map
      fun (reply, device) => (reply, device, st.2))
    (fun (q : SigningQuery) (st : State C) => (H.signingOracle s sk q st.2).map
      fun (reply, log) => (reply, st.1, log))

/-- The forger receives its classical replies and its conditional post-measurement state.
The final output and signing log are retained, and the residual device is discarded only
after the program terminates. -/
noncomputable def transcript (C : QuantumSigningForger) (H : Xofs) (s : Level)
    (keys : KeyPair) : PMF (Forgery × List Forgery) :=
  (ProbOracleComp.runWith (C.commands H s keys.secretKey) (C.program keys.publicKey)
    C.initial).map fun (f, st) => (f, st.2)

/-- Every response in the log of a quantum execution passes the FIPS verifier, including
after coherent queries, measurements and subsequent adaptive signing requests. -/
theorem verify_of_mem_transcript (C : QuantumSigningForger) {H : Xofs} {s : Level}
    {seed : FixedBytes 32} {keys : KeyPair} {f g : Forgery} {log : List Forgery}
    (hg : H.keyGen s seed = some keys) (hr : (f, log) ∈ (C.transcript H s keys).support)
    (hmem : g ∈ log) : H.verify s keys.publicKey g.message g.context g.signature = some true := by
  obtain ⟨⟨out, st⟩, hst, eq⟩ := (PMF.mem_support_map_iff ..).mp hr
  cases eq
  let inv (st : State C) := ∀ g ∈ st.2,
    H.verify s keys.publicKey g.message g.context g.signature = some true
  suffices h : inv st from h _ hmem
  apply ProbOracleComp.runWith_invariant _ inv ?_ _ C.initial (by simp [initial, inv]) _ _ hst
  intro q current ih reply next hs
  dsimp only [inv] at ih ⊢
  cases q with
  | inl cmd =>
    obtain ⟨⟨_, dev⟩, _, eq⟩ := (PMF.mem_support_map_iff ..).mp hs
    have logEq := congrArg (fun r => r.2.2) eq
    change current.2 = next.2 at logEq
    exact logEq ▸ ih
  | inr sign =>
    obtain ⟨⟨sig, log'⟩, hs', eq⟩ := (PMF.mem_support_map_iff ..).mp hs
    have logEq := congrArg (fun r => r.2.2) eq
    change log' = next.2 at logEq
    exact logEq ▸ signingOracle_preserves_verified hg sign current.2 ih hs'

/-- Strong forgery against seeded FIPS at a fixed pair of raw XOFs. The seed and all signing
hedges are random, and a failed setup loses. The parameter `H` may be the concrete FIPS sponges. -/
noncomputable def forgeryGame (C : QuantumSigningForger) (H : Xofs) (s : Level) : Game :=
  H.keyExperiment s fun keys =>
    (C.transcript H s keys).map fun (f, log) => H.winsForgery s keys.publicKey f log

/-- The finite random-XOF experiment samples both tables once before the key seed, keeping
them fixed through the coherent execution and final FIPS verification. The sampled widths
can exceed the forger's register widths to cover the honest algorithm inputs and outputs. -/
noncomputable def randomPrefixGame (C : QuantumSigningForger) (s : Level)
    (background : Xofs) (a bytes : ℕ) : Game :=
  (background.uniformPrefixes a bytes).bind fun H => C.forgeryGame H s

private noncomputable def runAtSetup (C : QuantumSigningForger) (s : Level)
    (z : Xofs × Option (PublicMatrix s × KeyPair)) : PMF (Option (SignedMatrixTrial s)) :=
  match z with
  | (_, none) => pure none
  | (H, some (A, keys)) => (C.transcript H s keys).map fun (f, log) =>
      some ⟨H, A, keys.publicKey, f, log⟩

/-- Program the SHAKE128 rows of the public matrix before running any of the forger's
quantum operations. The solver can run this experiment on an external coefficient matrix. -/
noncomputable def programmedTrial (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) : PMF (Option (SignedMatrixTrial s)) := do
  let setup ← (programmedMatrixSetup H s A).eval
  C.runAtSetup s setup

/-- The comparison experiment samples the actual raw matrix prefixes at the derived seed and
recovers the optional matrix by reading the same XOF on the published key. -/
noncomputable def matrixTrial (C : QuantumSigningForger) (s : Level) (H : Xofs) :
    PMF (Option (SignedMatrixTrial s)) := do
  let setup ← matrixSetup H s
  C.runAtSetup s setup

/-- Supplying a uniform matrix to the program preserves the joint distribution of the
forger's final output, complete successful signing history, raw XOFs, public key and matrix.
Arbitrary interleaving of coherent queries, measurements and signing requests is permitted. -/
theorem uniform_programmedTrial (C : QuantumSigningForger) (s : Level) (H : Xofs) :
    (PMF.uniformOfFintype (PublicMatrix s)).bind (fun A => C.programmedTrial s H A) =
      C.matrixTrial s H := by
  simp only [programmedTrial, matrixTrial, PMF.monad_bind_eq_bind, ← uniform_programmedMatrixSetup,
    PMF.bind_bind]

/-- The semantic output law of the quantum Hermite MSIS solver. It runs the adversary once
on its supplied matrix, then extracts the vector using only the final classical transcript. -/
noncomputable def matrixSolver (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) : PMF (Fin (s.params.k + s.params.ℓ) → Fin s.params.n → ℤ) :=
  (C.programmedTrial s H A).map vectorOfTrial

private theorem verified_programmedTrial (C : QuantumSigningForger) {H : Xofs} {s : Level}
    {A : PublicMatrix s} {u : SignedMatrixTrial s}
    (hu : some u ∈ (C.programmedTrial s H A).support) :
    u.matrix = A ∧ u.xofs.expandA s (u.publicKey.take 32) = some A ∧
      ∀ f ∈ u.log, u.xofs.verify s u.publicKey f.message f.context f.signature = some true := by
  simp only [programmedTrial, PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at hu
  obtain ⟨⟨G, setup⟩, hs, h⟩ := hu
  cases setup with
  | none => simp [runAtSetup] at h
  | some pair =>
    obtain ⟨B, keys⟩ := pair
    obtain ⟨rfl, ⟨seed, hg⟩, hm⟩ := keyGen_of_mem_programmedMatrixSetup hs
    obtain ⟨⟨f, log⟩, hr, eq⟩ := (PMF.mem_support_map_iff ..).mp h
    simp only [Option.some.injEq] at eq
    subst u
    exact ⟨rfl, hm, fun _ hmem => C.verify_of_mem_transcript hg hr hmem⟩

/-- The full strong-forgery probability in the quantum matrix-prefix hybrid is bounded by
fresh-digest forgeries, computed SHAKE256 collisions and the explicit solver's success on
a uniform Hermite right block. Signing is classical and the two XOFs are coherently accessible
through the persistent device. This inequality concerns success probabilities at the given
register sizes. The fresh-digest bound and gate and query costs remain open. -/
theorem matrixTrial_forgery_le (C : QuantumSigningForger) (s : Level) (H : Xofs) :
    let trial := C.matrixTrial s H
    Game.succProbability (trial.map (·.any SignedMatrixTrial.wins)) ≤
      Game.succProbability (trial.map (·.any SignedMatrixTrial.newDigestWin)) +
      (Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
        Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
          (C.matrixSolver s H A).map fun v => decide (ModuleSIS.IsSolution
            (ModuleSIS.hermiteMatrix A) (max (2 * (s.params.γ₁ - s.params.β))
              (4 * s.params.γ₂ + 2)) v))) := by
  intro trial
  have h := SignedMatrixTrial.bound_of_verifiedLog (fun A => C.programmedTrial s H A)
    (fun _ _ hu => C.verified_programmedTrial hu)
  simpa only [uniform_programmedTrial, matrixSolver, PMF.map_comp, Function.comp_def, trial] using h

end QuantumSigningForger

end Cslib.Crypto.MLDSA.FIPS204
