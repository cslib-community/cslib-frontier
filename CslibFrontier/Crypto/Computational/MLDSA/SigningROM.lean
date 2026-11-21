/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SigningSimulation
public import CslibFrontier.Crypto.Protocols.Signature.RandomOracle
import CslibFrontier.Crypto.Game.CloseTo.RejectedProgramming
import CslibFrontier.Languages.Probabilistic.Simulation
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Languages.Probabilistic.QueryCount.Scale
import CslibFrontier.Languages.Probabilistic.Traverse.FindM

/-!
# Adaptive programming at ML-DSA signing commitments

The signer runs the bounded retry loop of [NISTFIPS204], Algorithm 7, with independent ideal
masks. Signing and direct digest queries use a shared classical lazy random oracle on algebraic
high bits and message representatives. The fresh-overwrite hybrid programs every attempted
commitment, including those whose signatures are rejected. The digest returned on success is
retained alongside its polynomial expansion in the algebraic signature.

For a fixed matrix, the distance between these executions is bounded by the largest commitment
atom times the number of pairs of queries that could collide. The bound covers arbitrary
interleavings and early termination of the signing loop. Erasing the writes of rejected trials
costs at most the number of trial/direct-query pairs times the same largest atom. Replacing the
remaining accepted responses with the full-public-key simulator preserves their joint law.
-/

public section

namespace Cslib.Crypto.MLDSA

open Cslib.OracleComp Cslib.Probability Cslib.Crypto.Protocols.ROMSignature
open scoped ENNReal

variable (P : Params)

/-- The algebraic input to the commitment hash: high bits of the mask commitment and a message
representative, in the order used by `MLDSA.Hash`. -/
abbrev SigningHashPoint := (Fin P.k → Fin P.n → ℤ) × List Bool

/-- The shared signing and digest-query interface. Successful signing replies retain the digest
and the compressed algebraic signature, and a bounded signing loop may return `none`. -/
abbrev SigningROMSpec (Digest : Type) :=
  ForgerSpec (List Bool) (SigningHashPoint P) (Option (Digest × CompressedSignature P)) Digest

variable {Digest α : Type}

/-- Expand each signing request into up to `K` attempts on its message, stopping at the first
accepted signature. Direct digest requests pass through unchanged. -/
@[expose] def expandSigningRetries (K : ℕ) (program : OracleComp (SigningROMSpec P Digest) α) :
    OracleComp (SigningROMSpec P Digest) α :=
  interpret (sumHandler
    (fun msg => (List.range K).findSomeM? fun _ =>
      query (spec := SigningROMSpec P Digest) (.inl msg))
    (fun point => query (.inr point))) program

private theorem cost_expandSigningRetries (K s h : ℕ)
    {program : OracleComp (SigningROMSpec P Digest) α}
    {bound : ℕ}
    (hb : IsCostBounded (Sum.elim (fun _ => K * s) (fun _ => h)) program bound) :
    IsCostBounded (Sum.elim (fun _ => s) (fun _ => h))
      (expandSigningRetries P K program) bound := by
  refine hb.interpret fun q => ?_
  cases q with
  | inl msg =>
    simp only [Sum.elim_inl]
    simpa only [List.length_range] using
      (IsCostBounded.findSomeM? (xs := List.range K) (n := s)
        (f := fun _ => query (spec := SigningROMSpec P Digest) (.inl msg))
        (cost := Sum.elim (fun _ => s) (fun _ => h))
        (fun _ _ => IsCostBounded.query (spec := SigningROMSpec P Digest) (.inl msg)))
  | inr point => exact IsCostBounded.query _

private theorem costs_expandSigningRetries (K : ℕ)
    {program : OracleComp (SigningROMSpec P Digest) α}
    {S H : ℕ} (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) (expandSigningRetries P K program) (S * K) ∧
    IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) (expandSigningRetries P K program) H := by
  constructor
  · exact cost_expandSigningRetries P K 1 0 (hS.mul_of_le (c := K) (by
      intro q
      cases q <;> simp [signingCost]))
  · exact cost_expandSigningRetries P K 0 1 (hH.of_le (by
      intro q
      cases q <;> simp [hashCost]))

/-- The largest atom of `HighBits(A y)` when `y` is one ideal signing mask. -/
@[expose] noncomputable def commitmentGuessProbability (hγ : 0 < P.γ₁)
    (A : Matrix (Fin P.k) (Fin P.ℓ) (Fin P.n → ZMod P.q)) : ℝ≥0∞ :=
  ⨆ w, ((signingMaskLaw P hγ).map fun y => highBitsVec P (moduleSISMap A y)) w

private def trialPoint (sk : SecretKey P) (msg : List Bool) (y : Fin P.ℓ → Fin P.n → ZMod P.q) :
    SigningHashPoint P := (highBitsVec P (moduleSISMap sk.A y), msg)

private theorem trialPoint_le (hγ : 0 < P.γ₁) (sk : SecretKey P) (m q) :
    ((signingMaskLaw P hγ).map (trialPoint P sk m)) q ≤ commitmentGuessProbability P hγ sk.A :=
  RandomOracle.map_comp_apply_le_of_injective
    (emb := fun w => (w, m)) (fun _ _ h => (Prod.mk.inj h).1)
    (fun w => le_iSup (fun w => ((signingMaskLaw P hγ).map fun y =>
      highBitsVec P (moduleSISMap sk.A y)) w) w) q

private def trialReply (d ω : ℕ) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    (msg : List Bool) (y : Fin P.ℓ → Fin P.n → ZMod P.q) (c : Digest) (_ : Unit) :
    Option (Digest × CompressedSignature P) × Unit :=
  ((compressedSignAttempt P d ω (fun _ => expand c) sk msg y).map (Prod.mk c), ())

/-- Run an adaptive program from an empty digest table. Under `overwrite = false` the signer
reads the ordinary lazy hash at every trial commitment. Under `overwrite = true` it samples a
fresh digest and writes it there, including on rejected attempts. The entire final digest table
is retained. -/
noncomputable def runBoundedSigningROM (overwrite : Bool) (d ω K : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  let handler := if overwrite then
    RandomOracle.overwriteProgramHandler dist (fun _ : List Bool => true)
      (fun _ h _ => Bool.noConfusion h) (fun _ => signingMaskLaw P hγ)
      (trialPoint P sk) (trialReply P d ω expand sk)
  else
    RandomOracle.lazyProgramHandler dist (fun _ : List Bool => true)
      (fun _ h _ => Bool.noConfusion h) (fun _ => signingMaskLaw P hγ)
      (trialPoint P sk) (trialReply P d ω expand sk)
  ((interpret handler (expandSigningRetries P K program)).run ([], ())).map (Prod.map id Prod.fst)

/-- For `S` adaptive signing queries and `H` direct hash queries, at most `T = S K` trial
commitments are programmed. The honest and fresh-overwrite executions, including the final
table, are within `(T H + choose(T,2))` times the largest commitment atom for the actual matrix. -/
theorem closeTo_runBoundedSigningROM_overwrite (d ω K : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    {program : OracleComp (SigningROMSpec P Digest) α} {S H : ℕ}
    (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    CloseTo (runBoundedSigningROM P false d ω K hγ dist expand sk program)
      (runBoundedSigningROM P true d ω K hγ dist expand sk program)
      (((S * K) * H + (S * K).choose 2 : ℕ) * commitmentGuessProbability P hγ sk.A) := by
  obtain ⟨hs, hh⟩ := costs_expandSigningRetries P K hS hH
  have hop := RandomOracle.closeTo_run_lazyProgramHandler_overwriteProgramHandler_choose_two
    dist (fun _ : List Bool => true) (fun _ h _ => Bool.noConfusion h)
    (fun _ => signingMaskLaw P hγ) (trialPoint P sk) (trialReply P d ω expand sk)
    (fun msg _ => trialPoint_le P hγ sk msg)
    hs hh [] ()
  simpa only [List.length_nil, Nat.mul_zero, zero_add, runBoundedSigningROM, Bool.false_eq_true,
    ↓reduceIte] using hop.map (Prod.map id Prod.fst)

/-- Run a signer that samples a digest and an optional transcript independently of the cache
at each attempt. Only accepted commitments are written. Direct hash queries use the same table,
and the bounded retry loop ends at the first success. -/
noncomputable def runAcceptedSigningROM (K : ℕ) (dist : PMF Digest)
    (attempt : Digest → PMF (Option (AttemptTranscript P)))
    (program : OracleComp (SigningROMSpec P Digest) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  let handler : (q : List Bool ⊕ SigningHashPoint P) →
      StateT (List (SigningHashPoint P × Digest)) PMF (SigningROMSpec P Digest q) :=
    sumHandler (fun msg cache => do
      let c ← dist
      let out ← attempt c
      match out with
      | none => return (none, cache)
      | some t => return (some (c, t.signature), ((t.commitment, msg), c) :: cache))
      (memoize fun _ => dist)
  (interpret handler (expandSigningRetries P K program)).run []

/-- For every adaptive signing and hash program, the accepted-write hybrid using the real
masked response has exactly the law of the simulator using only the full public key. The
equality includes all retry outcomes and the final table of accepted commitments and hash
queries. -/
theorem runAcceptedSigningROM_eq_simulate (hP : P.Valid) (hq : 2 * P.γ₁ < P.q)
    (hβ : P.β < P.γ₁) (d ω K : ℕ) (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q)
    (sk : SecretKey P) (hs₁ : ∀ i j, |(sk.s₁ i j).valMinAbs| ≤ P.η)
    (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η) (hc : ∀ c, InBall P.τ (expand c))
    (program : OracleComp (SigningROMSpec P Digest) α) :
    runAcceptedSigningROM P K dist (fun c => freshSigningAttempt P d ω (by lia) sk (expand c))
        program =
      runAcceptedSigningROM P K dist
        (fun c => simulateFreshSigningAttempt P d ω hβ sk.publicKey (expand c)) program := by
  exact congrArg (fun attempt => runAcceptedSigningROM P K dist attempt program)
    (funext fun c => freshSigningAttempt_eq_simulate P hP hq hβ d ω sk hs₁ hs₂ (hc c))

private noncomputable def trialCoins (hγ : 0 < P.γ₁) (dist : PMF Digest) :=
  dist.bind fun c => (signingMaskLaw P hγ).map (c, ·)

private noncomputable def programmedTrial (aborts : Bool) (d ω : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P) :
    (q : List Bool ⊕ SigningHashPoint P) →
      StateT (List (SigningHashPoint P × Digest)) PMF (SigningROMSpec P Digest q) :=
  fun q st => (trialCoins P hγ dist).map fun x =>
    RandomOracle.programmedTrialStep aborts (fun m x => trialPoint P sk m x.2)
      Prod.fst (fun m x => (trialReply P d ω expand sk m x.2 x.1 ()).1) q x st

private theorem trial_hash (aborts : Bool) (d ω : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    (q : SigningHashPoint P) (st : List (SigningHashPoint P × Digest)) :
    programmedTrial P aborts d ω hγ dist expand sk (.inr q) st = memoize (fun _ => dist) q st := by
  cases e : st.lookup q <;>
    simp [programmedTrial, trialCoins, RandomOracle.programmedTrialStep, memoize, e,
      Function.comp_def, PMF.map, PMF.bind_const,
      PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind]

private theorem run_overwrite (d ω K : ℕ) (hγ : 0 < P.γ₁) (dist : PMF Digest)
    (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    runBoundedSigningROM P true d ω K hγ dist expand sk program =
      (interpret (programmedTrial P true d ω hγ dist expand sk)
        (expandSigningRetries P K program)).run [] := by
  simp only [runBoundedSigningROM, ↓reduceIte]
  apply run_interpret_map_state _ _ Prod.fst
  intro q ⟨cache, log⟩
  cases q with
  | inr k =>
    rw [trial_hash]
    simp only [RandomOracle.overwriteProgramHandler, PMF.map_comp, Function.comp_def, Prod.mk.eta]
    apply PMF.map_id
  | inl m =>
    simp only [RandomOracle.overwriteProgramHandler, ↓reduceDIte, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, programmedTrial, trialCoins,
      PMF.map_comp, Function.comp_def, RandomOracle.programmedTrialStep, Bool.true_or, ↓reduceIte]
    rw [PMF.bind_comm]
    rfl

private theorem run_accepted (d ω K : ℕ) (hγ : 0 < P.γ₁) (dist : PMF Digest)
    (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    runAcceptedSigningROM P K dist (fun c => freshSigningAttempt P d ω hγ sk (expand c)) program =
      (interpret (programmedTrial P false d ω hγ dist expand sk)
        (expandSigningRetries P K program)).run [] := by
  unfold runAcceptedSigningROM
  apply congrArg (fun h : (q : List Bool ⊕ SigningHashPoint P) →
    StateT (List (SigningHashPoint P × Digest)) PMF (SigningROMSpec P Digest q) =>
      (interpret h (expandSigningRetries P K program)).run [])
  funext q cache
  cases q with
  | inr k => exact (trial_hash P false d ω hγ dist expand sk k cache).symm
  | inl m =>
    simp only [sumHandler, freshSigningAttempt, programmedTrial, trialCoins,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      RandomOracle.programmedTrialStep, Bool.false_or, trialPoint, trialReply, Function.comp_def]
    congr 1 with c : 1
    rw [PMF.map]
    congr 1 with y : 1
    have he : compressedSignAttempt P d ω (fun _ => expand c) sk m y =
        compressedSignAttempt P d ω (fun _ => expand c) sk [] y := rfl
    simp only [Function.comp_apply, he]
    cases compressedSignAttempt P d ω (fun _ => expand c) sk [] y <;> rfl

/-- Adaptive classical-ROM simulation of bounded ML-DSA signing with ideal masks, for a fixed
key and a digest law whose expansion is sparse. The simulator uses the full public key. For
`T = S K` internal attempts and `H` direct queries, prior hash collisions cost
`(T H + choose(T,2)) δ` and later reads of erased rejected commitments cost `T H δ`, where
`δ` is the largest commitment atom for the actual matrix. The adversary sees only its output. -/
theorem closeTo_runBoundedSigningROM_simulate (hP : P.Valid) (hq : 2 * P.γ₁ < P.q)
    (hβ : P.β < P.γ₁) (d ω K : ℕ) (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q)
    (sk : SecretKey P) (hs₁ : ∀ i j, |(sk.s₁ i j).valMinAbs| ≤ P.η)
    (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η) (hc : ∀ c, InBall P.τ (expand c))
    {program : OracleComp (SigningROMSpec P Digest) α} {S H : ℕ}
    (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    CloseTo ((runBoundedSigningROM P false d ω K (by lia) dist expand sk program).map Prod.fst)
      ((runAcceptedSigningROM P K dist
        (fun c => simulateFreshSigningAttempt P d ω hβ sk.publicKey (expand c)) program).map
          Prod.fst)
      ((2 * (S * K) * H + (S * K).choose 2 : ℕ) * commitmentGuessProbability P (by lia) sk.A) := by
  have hγ : 0 < P.γ₁ := by lia
  have first := (closeTo_runBoundedSigningROM_overwrite P d ω K hγ dist expand sk hS hH).map
    Prod.fst
  rw [run_overwrite] at first
  rw [← runAcceptedSigningROM_eq_simulate P hP hq hβ d ω K dist expand sk hs₁ hs₂ hc, run_accepted]
  obtain ⟨hs, hh⟩ := costs_expandSigningRetries P K hS hH
  have hmass (m q) : ((trialCoins P hγ dist).map (fun x => trialPoint P sk m x.2)) q ≤
      commitmentGuessProbability P hγ sk.A := by
    simp only [trialCoins, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]
    exact trialPoint_le P hγ sk m q
  have erased := RandomOracle.closeTo_eraseRejectedTrialWrites (trialCoins P hγ dist)
    (fun m x => trialPoint P sk m x.2) Prod.fst
    (fun m x => (trialReply P d ω expand sk m x.2 x.1 ()).1) hs hh hmass []
  exact (first.trans erased).mono (by push_cast; ring_nf; rfl)

end Cslib.Crypto.MLDSA
