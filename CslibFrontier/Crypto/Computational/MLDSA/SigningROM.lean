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
import CslibFrontier.Foundations.Data.List.Lookup
public import CslibFrontier.Languages.Probabilistic.Transcript
public import CslibFrontier.Languages.Probabilistic.RandomOracle.Programming
import CslibFrontier.Languages.Probabilistic.QueryCount.Demand
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
For a partial digest expander the simulator also records the terminal failed attempt, with a
fresh commitment drawn from the public matrix. This preserves expansion errors exactly.

The transcript of the partial simulator identifies the newest writer at the verifier’s actual
digest read. Either a direct oracle call supplied the digest or the signing history contains an
accepted response on the same representative. In the latter case a fresh signature gives the
ordinary Module-SIS witness of [BaiEtAl2021Dilithium], §6.2.2, equation (8).
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

variable {Digest Reply α : Type}

/-- The primitive trial interface. `none` asks for another trial. A terminal value of type
`Reply` may itself report a fatal error from a partial digest expansion. -/
abbrev SigningTrialSpec (Digest Reply : Type) :=
  ForgerSpec (List Bool) (SigningHashPoint P) (Option Reply) Digest

/-- Expand each signing request into up to `K` attempts on its message, stopping at the first
terminal trial. Direct digest requests pass through unchanged. -/
@[expose] def expandSigningRetries (K : ℕ)
    (program : OracleComp (SigningTrialSpec P Digest Reply) α) :
    OracleComp (SigningTrialSpec P Digest Reply) α :=
  interpret (sumHandler
    (fun msg => (List.range K).findSomeM? fun _ =>
      query (spec := SigningTrialSpec P Digest Reply) (.inl msg))
    (fun point => query (.inr point))) program

private theorem costs_expandSigningRetries (K : ℕ)
    {program : OracleComp (SigningTrialSpec P Digest Reply) α}
    {S H : ℕ} (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    IsCostBounded (Sum.elim (fun _ => 1) (fun _ => 0)) (expandSigningRetries P K program) (S * K) ∧
    IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 1)) (expandSigningRetries P K program) H := by
  let cost (channel : Bool) : List Bool ⊕ SigningHashPoint P → ℕ :=
    Sum.elim (fun _ => if channel then 0 else 1) (fun _ => if channel then 1 else 0)
  let budget (i : Bool) := if i then H else S
  let demand : Bool → Bool → ℕ
    | false, false => K
    | true, true => 1
    | _, _ => 0
  have bound : ∀ i, IsCostBounded (cost i) program (budget i)
    | false => hS.of_le fun q => by cases q <;> rfl
    | true => hH.of_le fun q => by cases q <;> rfl
  have hx (j : Bool) : IsCostBounded (cost j) (expandSigningRetries P K program)
      (∑ i, budget i * demand i j) := by
    refine IsCostBounded.interpret_demand cost cost demand _ (fun q c => ?_) bound j
    rcases q with m | point
    · have trial := IsCostBounded.findSomeM? (xs := List.range K) (n := if c then 0 else 1)
        (f := fun _ => query (spec := SigningTrialSpec P Digest Reply) (.inl m))
        (cost := cost c) fun _ _ => IsCostBounded.query _
      cases c <;> simpa [cost, demand, Fintype.sum_bool] using trial
    · have direct := IsCostBounded.query (spec := SigningTrialSpec P Digest Reply) (cost := cost c)
        (.inr point)
      cases c <;> simpa [cost, demand, Fintype.sum_bool] using direct
  exact ⟨by simpa [cost, budget, demand, Fintype.sum_bool] using hx false,
    by simpa [cost, budget, demand, Fintype.sum_bool] using hx true⟩

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

/-- The underlying trial experiment for either form of challenge expansion. -/
private noncomputable def runTrials (overwrite : Bool) (K : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (sk : SecretKey P)
    (result : (Fin P.ℓ → Fin P.n → ZMod P.q) → Digest → Option Reply)
    (program : OracleComp (SigningTrialSpec P Digest Reply) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  let handler := if overwrite then
    RandomOracle.overwriteProgramHandler dist (fun _ : List Bool => true)
      (fun _ h _ => Bool.noConfusion h) (fun _ => signingMaskLaw P hγ)
      (trialPoint P sk) (fun _ y c _ => (result y c, ()))
  else
    RandomOracle.lazyProgramHandler dist (fun _ : List Bool => true)
      (fun _ h _ => Bool.noConfusion h) (fun _ => signingMaskLaw P hγ)
      (trialPoint P sk) (fun _ y c _ => (result y c, ()))
  ((interpret handler (expandSigningRetries P K program)).run ([], ())).map (Prod.map id Prod.fst)

/-- For `S` adaptive signing queries and `H` direct hash queries, at most `T = S K` trial
commitments are programmed. The honest and fresh-overwrite executions, including the final
table, are within `(T H + choose(T,2))` times the largest commitment atom for the actual matrix. -/
private theorem closeTo_runTrials_overwrite (K : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (sk : SecretKey P)
    (result : (Fin P.ℓ → Fin P.n → ZMod P.q) → Digest → Option Reply)
    {program : OracleComp (SigningTrialSpec P Digest Reply) α} {S H : ℕ}
    (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    CloseTo (runTrials P false K hγ dist sk result program)
      (runTrials P true K hγ dist sk result program)
      (((S * K) * H + (S * K).choose 2 : ℕ) * commitmentGuessProbability P hγ sk.A) := by
  obtain ⟨hs, hh⟩ := costs_expandSigningRetries P K hS hH
  simpa only [List.length_nil, Nat.mul_zero, zero_add, runTrials, Bool.false_eq_true,
    ↓reduceIte] using
    (RandomOracle.closeTo_run_lazyProgramHandler_overwriteProgramHandler_choose_two
      dist (fun _ : List Bool => true) (fun _ h _ => Bool.noConfusion h)
      (fun _ => signingMaskLaw P hγ) (trialPoint P sk) (fun _ y c _ => (result y c, ()))
      (fun msg _ => trialPoint_le P hγ sk msg) hs hh [] ()).map (Prod.map id Prod.fst)

/-- One terminal trial or a direct digest call, retaining the chosen annotation on each write. -/
private noncomputable def terminalTrialHandler {Entry : Type} (dist : PMF Digest)
    (attempt : Digest → PMF (Option ((Fin P.k → Fin P.n → ℤ) × Reply)))
    (ambient : Digest → Entry) (terminal : Digest → Reply → Entry) (digest : Entry → Digest) :
    (q : List Bool ⊕ SigningHashPoint P) →
      StateT (List (SigningHashPoint P × Entry)) PMF (SigningTrialSpec P Digest Reply q) :=
  sumHandler (fun msg cache => do
    let c ← dist
    let out ← attempt c
    match out with
    | none => return (none, cache)
    | some (w, reply) => return (some reply, ((w, msg), terminal c reply) :: cache))
    (fun point cache => match cache.lookup point with
      | some entry => pure (digest entry, cache)
      | none => do
        let c ← dist
        return (c, (point, ambient c) :: cache))

/-- Only terminal trials write their point. A terminal reply can be a signature or an error. -/
private noncomputable def runTerminalTrials (K : ℕ) (dist : PMF Digest)
    (attempt : Digest → PMF (Option ((Fin P.k → Fin P.n → ℤ) × Reply)))
    (program : OracleComp (SigningTrialSpec P Digest Reply) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  (interpret (terminalTrialHandler P dist attempt id (fun c _ => c) id)
    (expandSigningRetries P K program)).run []

private noncomputable def trialCoins (hγ : 0 < P.γ₁) (dist : PMF Digest) :=
  dist.bind fun c => (signingMaskLaw P hγ).map (c, ·)

private noncomputable def programmedTrial (aborts : Bool) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (sk : SecretKey P)
    (result : (Fin P.ℓ → Fin P.n → ZMod P.q) → Digest → Option Reply) :
    (q : List Bool ⊕ SigningHashPoint P) →
      StateT (List (SigningHashPoint P × Digest)) PMF (SigningTrialSpec P Digest Reply q) :=
  fun q st => (trialCoins P hγ dist).map fun x =>
    RandomOracle.programmedTrialStep aborts (fun m x => trialPoint P sk m x.2)
      Prod.fst (fun _ x => result x.2 x.1) q x st

private theorem trial_hash (aborts : Bool) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (sk : SecretKey P)
    (result : (Fin P.ℓ → Fin P.n → ZMod P.q) → Digest → Option Reply)
    (q : SigningHashPoint P) (st : List (SigningHashPoint P × Digest)) :
    programmedTrial P aborts hγ dist sk result (.inr q) st = memoize (fun _ => dist) q st := by
  cases e : st.lookup q <;>
    simp [programmedTrial, trialCoins, RandomOracle.programmedTrialStep, memoize, e,
      Function.comp_def, PMF.map, PMF.bind_const,
      PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind]

private theorem run_overwrite (K : ℕ) (hγ : 0 < P.γ₁) (dist : PMF Digest)
    (sk : SecretKey P) (result : (Fin P.ℓ → Fin P.n → ZMod P.q) → Digest → Option Reply)
    (program : OracleComp (SigningTrialSpec P Digest Reply) α) :
    runTrials P true K hγ dist sk result program =
      (interpret (programmedTrial P true hγ dist sk result)
        (expandSigningRetries P K program)).run [] := by
  simp only [runTrials, ↓reduceIte]
  apply run_interpret_map_state _ _ Prod.fst
  rintro (m | k) ⟨cache, log⟩
  · simp only [RandomOracle.overwriteProgramHandler, ↓reduceDIte, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map, programmedTrial, trialCoins,
      PMF.map_comp, Function.comp_def, RandomOracle.programmedTrialStep, Bool.true_or, ↓reduceIte]
    exact PMF.bind_comm ..
  · rw [trial_hash]
    simp only [RandomOracle.overwriteProgramHandler, PMF.map_comp, Function.comp_def, Prod.mk.eta]
    exact PMF.map_id _

private theorem run_accepted (K : ℕ) (hγ : 0 < P.γ₁) (dist : PMF Digest)
    (sk : SecretKey P) (result : (Fin P.ℓ → Fin P.n → ZMod P.q) → Digest → Option Reply)
    (program : OracleComp (SigningTrialSpec P Digest Reply) α) :
    runTerminalTrials P K dist (fun c => (signingMaskLaw P hγ).map fun y =>
      (result y c).map (Prod.mk (trialPoint P sk [] y).1)) program =
      (interpret (programmedTrial P false hγ dist sk result)
        (expandSigningRetries P K program)).run [] := by
  unfold runTerminalTrials
  congr 2
  funext q cache
  rcases q with m | k
  · simp only [terminalTrialHandler, sumHandler, programmedTrial, trialCoins,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_map, PMF.map_bind, PMF.map_comp,
      RandomOracle.programmedTrialStep, Bool.false_or, trialPoint, Function.comp_def]
    congr 1 with c : 1
    rw [PMF.map]
    congr 1 with y : 1
    simp only [Function.comp_apply]
    cases result y c <;> rfl
  · exact (trial_hash P false hγ dist sk result k cache).symm

private theorem closeTo_terminalTrials (K : ℕ) (hγ : 0 < P.γ₁) (dist : PMF Digest)
    (sk : SecretKey P) (result : (Fin P.ℓ → Fin P.n → ZMod P.q) → Digest → Option Reply)
    {program : OracleComp (SigningTrialSpec P Digest Reply) α} {S H : ℕ}
    (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    CloseTo ((runTrials P false K hγ dist sk result program).map Prod.fst)
      ((runTerminalTrials P K dist (fun c => (signingMaskLaw P hγ).map fun y =>
        (result y c).map (Prod.mk (trialPoint P sk [] y).1)) program).map Prod.fst)
      ((2 * (S * K) * H + (S * K).choose 2 : ℕ) * commitmentGuessProbability P hγ sk.A) := by
  have first := (closeTo_runTrials_overwrite P K hγ dist sk result hS hH).map
    Prod.fst
  rw [run_overwrite] at first
  rw [run_accepted]
  obtain ⟨hs, hh⟩ := costs_expandSigningRetries P K hS hH
  have hmass (m q) : ((trialCoins P hγ dist).map (fun x => trialPoint P sk m x.2)) q ≤
      commitmentGuessProbability P hγ sk.A := by
    simpa only [trialCoins, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const] using
      trialPoint_le P hγ sk m q
  have erased := RandomOracle.closeTo_eraseRejectedTrialWrites (trialCoins P hγ dist)
    (fun m x => trialPoint P sk m x.2) Prod.fst
    (fun _ x => result x.2 x.1) hs hh hmass []
  exact (first.trans erased).mono (by push_cast; ring_nf; rfl)

private def totalResult (d ω : ℕ) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    (y : Fin P.ℓ → Fin P.n → ZMod P.q) (c : Digest) : Option (Digest × CompressedSignature P) :=
  (compressedSignAttempt P d ω (fun _ => expand c) sk [] y).map (Prod.mk c)

/-- Run an adaptive program from an empty digest table. Under `overwrite = false` the signer
reads the ordinary lazy hash at every trial commitment. Under `overwrite = true` it samples a
fresh digest and writes it there, including on rejected attempts. The entire final digest table
is retained. -/
noncomputable def runBoundedSigningROM (overwrite : Bool) (d ω K : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  runTrials P overwrite K hγ dist sk (totalResult P d ω expand sk) program

/-- For `S` adaptive signing queries and `H` direct hash queries, at most `T = S K` trial
commitments are programmed. The honest and fresh-overwrite executions, including the final
table, are within `(T H + choose(T,2))` times the largest commitment atom for the actual matrix. -/
theorem closeTo_runBoundedSigningROM_overwrite (d ω K : ℕ) (hγ : 0 < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Fin P.n → ZMod P.q) (sk : SecretKey P)
    {program : OracleComp (SigningROMSpec P Digest) α} {S H : ℕ}
    (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    CloseTo (runBoundedSigningROM P false d ω K hγ dist expand sk program)
      (runBoundedSigningROM P true d ω K hγ dist expand sk program)
      (((S * K) * H + (S * K).choose 2 : ℕ) * commitmentGuessProbability P hγ sk.A) :=
  closeTo_runTrials_overwrite P K hγ dist sk (totalResult P d ω expand sk) hS hH

/-- Run a signer that samples a digest and an optional transcript independently of the cache
at each attempt. Only accepted commitments are written. Direct hash queries use the same table,
and the bounded retry loop ends at the first success. -/
noncomputable def runAcceptedSigningROM (K : ℕ) (dist : PMF Digest)
    (attempt : Digest → PMF (Option (AttemptTranscript P)))
    (program : OracleComp (SigningROMSpec P Digest) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  runTerminalTrials P K dist (fun c => (attempt c).map fun out =>
    out.map fun t => (t.commitment, c, t.signature)) program

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
        (fun c => simulateFreshSigningAttempt P d ω hβ sk.publicKey (expand c)) program :=
  congrArg (fun attempt => runAcceptedSigningROM P K dist attempt program)
    (funext fun c => freshSigningAttempt_eq_simulate P hP hq hβ d ω sk hs₁ hs₂ (hc c))

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
  rw [← runAcceptedSigningROM_eq_simulate P hP hq hβ d ω K dist expand sk hs₁ hs₂ hc]
  simpa only [runBoundedSigningROM, runAcceptedSigningROM, totalResult, freshSigningAttempt,
    PMF.map_comp, Function.comp_def, Option.map_map, trialPoint] using
    closeTo_terminalTrials P K (by lia) dist sk (totalResult P d ω expand sk) hS hH

/-- Route a signing request to the bounded trial loop. A terminal trial carries either a
signature or an expansion error. After the loop the caller gets the signature, or one error
value for either expansion failure or exhaustion of the trial budget. -/
@[expose] def partialSigningProgram (program : OracleComp (SigningROMSpec P Digest) α) :
    OracleComp (SigningTrialSpec P Digest (Option (Digest × CompressedSignature P))) α :=
  interpret (sumHandler
    (fun m => Option.join <$> query
      (spec := SigningTrialSpec P Digest (Option (Digest × CompressedSignature P))) (.inl m))
    (fun q => query (.inr q))) program

private theorem partialSigningProgram_cost {cost : List Bool ⊕ SigningHashPoint P → ℕ}
    {n : ℕ} {program : OracleComp (SigningROMSpec P Digest) α} (h : IsCostBounded cost program n) :
    IsCostBounded cost (partialSigningProgram P program) n :=
  h.interpret fun
    | .inl _ => (isCostBounded_map_iff _ _ _).mpr (IsCostBounded.query _)
    | .inr _ => IsCostBounded.query _

private def partialResult (d ω : ℕ) (expand : Digest → Option (Fin P.n → ZMod P.q))
    (sk : SecretKey P) (y : Fin P.ℓ → Fin P.n → ZMod P.q) (c : Digest) :
    Option (Option (Digest × CompressedSignature P)) :=
  match expand c with
  | none => some none
  | some poly => ((compressedSignAttempt P d ω (fun _ => poly) sk [] y).map (Prod.mk c)).map some

/-- Honest signing in the classical digest ROM with a partial challenge expander. An
expansion error stops this signing request, even when further retries remain. A norm or
hint rejection advances to the next fresh ideal mask. -/
noncomputable def runPartialSigningROM (d ω K : ℕ) (hγ : 0 < P.γ₁) (dist : PMF Digest)
    (expand : Digest → Option (Fin P.n → ZMod P.q)) (sk : SecretKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  runTrials P false K hγ dist sk (partialResult P d ω expand sk) (partialSigningProgram P program)

private def terminalTranscript (c : Digest) (out : Option (AttemptTranscript P)) :=
  out.map fun t => (t.commitment, some (c, t.signature))

/-- One attempt of the partial-expansion signing simulator. An outer `none` requests another
mask. A terminal outcome records the programmed commitment and either the error or the
digest and signature returned to the adversary. -/
noncomputable def simulatePartialTrial (d ω : ℕ) (hβ : P.β < P.γ₁)
    (expand : Digest → Option (Fin P.n → ZMod P.q)) (pk : PublicKey P) (raw : Digest) :
    PMF (Option ((Fin P.k → Fin P.n → ℤ) × Option (Digest × CompressedSignature P))) :=
  match expand raw with
  | none => (signingMaskLaw P (by lia)).map fun y =>
      some (highBitsVec P (moduleSISMap pk.A y), none)
  | some poly => (simulateFreshSigningAttempt P d ω hβ pk poly).map (terminalTranscript P raw)

/-- A fresh verifying response at a commitment written by the partial signing simulator
yields Dilithium's ordinary MSIS witness (v3.1, §6.2.2, equation (8)). Successful expansion
of the programmed raw digest rules out a terminal signing error. The simulator's own response
supplies the second short witness, including for arbitrary uniform public vectors. -/
theorem isSolution_of_forgery_at_simulated_digest (hP : P.Valid) (hq : 2 * P.γ₁ < P.q)
    (hγq : 4 * P.γ₂ < P.q) (d ω : ℕ) (hβ : P.β < P.γ₁) (pk : PublicKey P)
    (expand : Digest → Option (Fin P.n → ZMod P.q)) (raw : Digest)
    {w : Fin P.k → Fin P.n → ℤ} {sent : Option (Digest × CompressedSignature P)}
    (ht : some (w, sent) ∈ (simulatePartialTrial P d ω hβ expand pk raw).support)
    {σ : CompressedSignature P} (hfresh : sent ≠ some (raw, σ))
    (hexpand : expand raw = some σ.c) (hz : ResponseShort P σ.z) (hw : σ.recover d pk = w) :
    ∃ other, sent = some (raw, other) ∧ ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix pk.A)
      (max (2 * (P.γ₁ - P.β)) (4 * P.γ₂ + 2)) (responseDifference d pk σ other) := by
  simp only [simulatePartialTrial, hexpand, PMF.mem_support_map_iff, terminalTranscript] at ht
  rcases ht with ⟨_ | t, hout, ⟨⟩⟩
  obtain ⟨hc, hshort, _, hrec⟩ :=
    simulateFreshSigningAttempt_support P hP hq hγq d ω hβ pk σ.c hout
  exact ⟨t.signature, rfl, isSolution_responseDifference hP hγq d pk
    (fun h => hfresh (h ▸ rfl)) hc.symm (hw.trans hrec.symm) hz hshort⟩

/-- Simulate bounded signing against the public matrix and full public vector with the same
partial digest expander. On an expansion error, independently sample a mask, program the
terminal trial's commitment, and return the public error. Successful expansions use the
fresh-transcript simulator. -/
noncomputable def simulatePartialSigningROM (d ω K : ℕ) (hβ : P.β < P.γ₁) (dist : PMF Digest)
    (expand : Digest → Option (Fin P.n → ZMod P.q)) (pk : PublicKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    PMF (α × List (SigningHashPoint P × Digest)) :=
  runTerminalTrials P K dist (simulatePartialTrial P d ω hβ expand pk)
    (partialSigningProgram P program)

/-- The adaptive signing-oracle simulation bound for partial challenge expansion. Expansions
may fail with arbitrary probability. Both experiments propagate that stopping event exactly
in the fresh-digest hybrid, including the attempted commitment written to the hash table.
Only queries colliding with earlier or erased commitments contribute to the error bound. -/
theorem closeTo_partialSigningROM (hP : P.Valid) (hq : 2 * P.γ₁ < P.q)
    (hβ : P.β < P.γ₁) (d ω K : ℕ) (dist : PMF Digest)
    (expand : Digest → Option (Fin P.n → ZMod P.q)) (sk : SecretKey P)
    (hs₁ : ∀ i j, |(sk.s₁ i j).valMinAbs| ≤ P.η) (hs₂ : ∀ i j, |(sk.s₂ i j).valMinAbs| ≤ P.η)
    (hc : ∀ c poly, expand c = some poly → InBall P.τ poly)
    {program : OracleComp (SigningROMSpec P Digest) α} {S H : ℕ}
    (hS : IsCostBounded signingCost program S) (hH : IsCostBounded hashCost program H) :
    CloseTo ((runPartialSigningROM P d ω K (by lia) dist expand sk program).map Prod.fst)
      ((simulatePartialSigningROM P d ω K hβ dist expand sk.publicKey program).map Prod.fst)
      ((2 * (S * K) * H + (S * K).choose 2 : ℕ) * commitmentGuessProbability P (by lia) sk.A) := by
  have he : simulatePartialTrial P d ω hβ expand sk.publicKey = fun c =>
      (signingMaskLaw P (by lia)).map fun y =>
        (partialResult P d ω expand sk y c).map (Prod.mk (trialPoint P sk [] y).1) := by
    funext c
    cases e : expand c with
    | none => simp [simulatePartialTrial, partialResult, e, trialPoint, SecretKey.publicKey]
    | some poly =>
      simp only [simulatePartialTrial, e,
        ← freshSigningAttempt_eq_simulate P hP hq hβ d ω sk hs₁ hs₂ (hc c poly e),
        freshSigningAttempt, PMF.map_comp, Function.comp_def, terminalTranscript, Option.map_map,
        partialResult, trialPoint]
  rw [simulatePartialSigningROM, he]
  exact closeTo_terminalTrials P K (by lia) dist sk (partialResult P d ω expand sk)
    (partialSigningProgram_cost P hS) (partialSigningProgram_cost P hH)

/-- A digest cache write records the direct hash reply or the terminal answer of a signing
request. A signing error is a terminal write, while an erased rejection makes no entry. -/
inductive SigningWrite (Digest Reply : Type) where
  /-- First direct query at an unassigned point. -/
  | ambient (raw : Digest)
  /-- Terminal signing trial, including a possible expansion error in `reply`. -/
  | signing (raw : Digest) (reply : Reply)

/-- The raw digest that a later lookup observes. -/
def SigningWrite.digest : SigningWrite Digest Reply → Digest
  | .ambient raw | .signing raw _ => raw

private abbrev SignReply (P : Params) (Digest : Type) :=
  Option (Digest × CompressedSignature P)

private noncomputable def observedTrial (dist : PMF Digest)
    (attempt : Digest → PMF (Option ((Fin P.k → Fin P.n → ℤ) × Reply))) :=
  terminalTrialHandler P dist attempt SigningWrite.ambient SigningWrite.signing SigningWrite.digest

private def outerSigningQuery (K : ℕ) :
    (q : List Bool ⊕ SigningHashPoint P) →
      OracleComp (SigningTrialSpec P Digest (SignReply P Digest)) (SigningROMSpec P Digest q) :=
  sumHandler (fun m => Option.join <$> (List.range K).findSomeM? fun _ =>
      query (spec := SigningTrialSpec P Digest (SignReply P Digest)) (.inl m))
    (fun point => query (spec := SigningTrialSpec P Digest (SignReply P Digest)) (.inr point))

private theorem expand_partialSigningProgram (K : ℕ)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    expandSigningRetries P K (partialSigningProgram P program) =
      interpret (outerSigningQuery P K) program := by
  simp only [expandSigningRetries, partialSigningProgram, interpret_interpret]
  congr 1 with (_ | _) <;> simp [sumHandler, outerSigningQuery]

/-- Execute the partial signing simulator, recording the last writer at each cache entry and
the actual outward query/reply transcript. Both lists are newest first. Retry attempts are
internal to a signing query and do not appear in the outward transcript. -/
noncomputable def simulatePartialSigningTranscript (d ω K : ℕ) (hβ : P.β < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Option (Fin P.n → ZMod P.q)) (pk : PublicKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    PMF (α × List (SigningHashPoint P ×
      SigningWrite Digest (Option (Digest × CompressedSignature P))) ×
        Transcript (SigningROMSpec P Digest)) :=
  let primitive := observedTrial P dist (simulatePartialTrial P d ω hβ expand pk)
  (interpret (withTranscript fun q => interpret primitive (outerSigningQuery P K q)) program).run
    ([], [])

/-- Forgetting write annotations and the outward transcript recovers the original joint law
of the adversary's output and the complete simulated digest cache. -/
theorem simulatePartialSigningTranscript_forget (d ω K : ℕ) (hβ : P.β < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Option (Fin P.n → ZMod P.q)) (pk : PublicKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) :
    (simulatePartialSigningTranscript P d ω K hβ dist expand pk program).map
      (fun (a, cache, _) => (a, cache.map fun (key, entry) => (key, entry.digest))) =
      simulatePartialSigningROM P d ω K hβ dist expand pk program := by
  let erase := List.map fun (e : SigningHashPoint P × SigningWrite Digest (SignReply P Digest)) =>
    (e.1, e.2.digest)
  have forget := congrArg (PMF.map (Prod.map id erase)) (run_interpret_withTranscript
    (fun q => interpret (observedTrial P dist (simulatePartialTrial P d ω hβ expand pk))
      (outerSigningQuery P K q)) program [] [])
  rw [PMF.map_comp, ← interpret_interpret] at forget
  refine forget.trans ?_
  rw [simulatePartialSigningROM, runTerminalTrials, expand_partialSigningProgram]
  apply run_interpret_map_state _ _ erase
  rintro (m | point) st
  · simp only [observedTrial, terminalTrialHandler, sumHandler, PMF.monad_bind_eq_bind,
      PMF.monad_pure_eq_pure, PMF.map_bind]
    congr 1 with raw : 1
    congr 1 with (_ | ⟨w, reply⟩) : 1 <;> simp [erase, SigningWrite.digest]
  · simp only [observedTrial, terminalTrialHandler, sumHandler, erase, List.lookup_map_snd]
    cases st.lookup point <;>
      simp [SigningWrite.digest, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind]

private theorem retry_support (dist : PMF Digest)
    (attempt : Digest → PMF (Option ((Fin P.k → Fin P.n → ℤ) × Reply))) (msg : List Bool)
    (xs : List ℕ) (cache : List (SigningHashPoint P × SigningWrite Digest Reply)) {reply next}
    (h : (reply, next) ∈ ((interpret (observedTrial P dist attempt) (xs.findSomeM? fun _ =>
      query (spec := SigningTrialSpec P Digest Reply) (.inl msg))).run cache).support) :
    (reply = none ∧ next = cache) ∨ ∃ raw w sent, reply = some sent ∧
      next = ((w, msg), .signing raw sent) :: cache ∧ some (w, sent) ∈ (attempt raw).support := by
  induction xs with
  | nil =>
    simpa only [List.findSomeM?_nil, interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
      PMF.mem_support_pure_iff, Prod.mk.injEq] using Or.inl h
  | cons _ xs ih =>
    simp only [List.findSomeM?_cons, interpret_bind, interpret_query, StateT.run_bind,
      PMF.monad_bind_eq_bind, PMF.mem_support_bind_iff] at h
    obtain ⟨⟨one, st⟩, hone, htail⟩ := h
    simp only [observedTrial, terminalTrialHandler, sumHandler, StateT.run, PMF.monad_bind_eq_bind,
      PMF.mem_support_bind_iff] at hone
    obtain ⟨raw, _, _ | ⟨w, sent⟩, ht, hs⟩ := hone <;>
      simp only [PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hs <;>
      obtain ⟨rfl, rfl⟩ := hs
    · exact ih htail
    · simp only [interpret_pure, StateT.run_pure, PMF.monad_pure_eq_pure,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at htail
      exact Or.inr ⟨raw, w, sent, htail.1, htail.2, ht⟩

private def writeRecorded
    (attempt : Digest → PMF (Option ((Fin P.k → Fin P.n → ℤ) × SignReply P Digest)))
    (log : Transcript (SigningROMSpec P Digest))
    (e : SigningHashPoint P × SigningWrite Digest (SignReply P Digest)) : Prop :=
  match e.2 with
  | .ambient raw => ⟨.inr e.1, raw⟩ ∈ log
  | .signing raw sent => ⟨.inl e.1.2, sent⟩ ∈ log ∧ some (e.1.1, sent) ∈ (attempt raw).support

private theorem writeRecorded_cons {attempt log e} (event)
    (h : writeRecorded P (Digest := Digest) attempt log e) :
    writeRecorded P attempt (event :: log) e := by
  rcases e with ⟨_, raw | ⟨raw, sent⟩⟩
  · exact List.mem_cons_of_mem _ h
  · exact ⟨List.mem_cons_of_mem _ h.1, h.2⟩

private theorem recorded_of_mem_simulatePartialSigningTranscript (d ω K : ℕ) (hβ : P.β < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Option (Fin P.n → ZMod P.q)) (pk : PublicKey P)
    (program : OracleComp (SigningROMSpec P Digest) α) {a cache log}
    (hrun : (a, cache, log) ∈ (simulatePartialSigningTranscript P d ω K hβ dist expand pk
      program).support) :
    ∀ e ∈ cache, writeRecorded P (simulatePartialTrial P d ω hβ expand pk) log e := by
  let attempt := simulatePartialTrial P d ω hβ expand pk
  let primitive := observedTrial P dist attempt
  refine run_interpret_invariant
    (withTranscript fun q => interpret primitive (outerSigningQuery P K q))
    (fun st => ∀ e ∈ st.1, writeRecorded P attempt st.2 e)
    (fun q ⟨st, prev⟩ hprev answer after h => ?_) program ([], []) (by simp) a (cache, log) hrun
  obtain ⟨⟨_, next⟩, hquery, ⟨⟩⟩ := (PMF.mem_support_map_iff ..).1 h
  have old : ∀ e ∈ st, writeRecorded P attempt (⟨q, answer⟩ :: prev) e :=
    fun e he => writeRecorded_cons P ⟨q, answer⟩ (hprev e he)
  rcases q with msg | point
  · change (answer, next) ∈
      ((interpret primitive (outerSigningQuery P K (.inl msg))).run st).support at hquery
    simp only [outerSigningQuery, sumHandler, interpret_map, StateT.run_map,
      PMF.monad_map_eq_map, PMF.mem_support_map_iff] at hquery
    obtain ⟨⟨_, _⟩, hsearch, ⟨⟩⟩ := hquery
    rcases retry_support P dist attempt msg (List.range K) st hsearch with
      ⟨rfl, rfl⟩ | ⟨raw, w, sent, rfl, rfl, ht⟩
    · exact old
    · exact List.forall_mem_cons.mpr ⟨⟨List.mem_cons_self, ht⟩, old⟩
  · simp only [outerSigningQuery, sumHandler, interpret_query, primitive, observedTrial,
      terminalTrialHandler] at hquery
    cases eq : st.lookup point with
    | some entry =>
      simp only [eq, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hquery
      exact hquery.2 ▸ old
    | none =>
      simp only [eq, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
        PMF.mem_support_pure_iff, Prod.mk.injEq] at hquery
      obtain ⟨raw, _, rfl, rfl⟩ := hquery
      exact List.forall_mem_cons.mpr ⟨List.mem_cons_self, old⟩

/-- A candidate forgery in the compressed signing ROM: a message representative, a transmitted
commitment digest, and a decoded compressed signature. -/
@[ext] structure ForgeryCandidate (Digest : Type) where
  /-- The message representative bits. -/
  message : List Bool
  /-- The commitment digest carried by the candidate signature. -/
  digest : Digest
  /-- The response, hint vector, and sparse challenge. -/
  signature : CompressedSignature P

/-- Append the verifier's commitment-digest query to the forger, using its output message
representative and the high bits recovered from its output response. Return the candidate and
the oracle answer so that verification compares the transmitted digest with the actual read. -/
@[expose] def queryForgeryDigest (d : ℕ) (pk : PublicKey P)
    (forger : OracleComp (SigningROMSpec P Digest) (ForgeryCandidate P Digest)) :
    OracleComp (SigningROMSpec P Digest) (ForgeryCandidate P Digest × Digest) := do
  let forged ← forger
  let reply ← query (spec := SigningROMSpec P Digest)
    (.inr (forged.signature.recover d pk, forged.message))
  return (forged, reply)

private theorem lookup_of_queryForgeryDigest (d ω K : ℕ) (hβ : P.β < P.γ₁)
    (dist : PMF Digest) (expand : Digest → Option (Fin P.n → ZMod P.q)) (pk : PublicKey P)
    (forger : OracleComp (SigningROMSpec P Digest) (ForgeryCandidate P Digest))
    {forged reply cache log} (h : ((forged, reply), cache, log) ∈
      (simulatePartialSigningTranscript P d ω K hβ dist expand pk
        (queryForgeryDigest P d pk forger)).support) :
    (cache.lookup (forged.signature.recover d pk, forged.message)).map SigningWrite.digest =
      some reply := by
  simp only [simulatePartialSigningTranscript, queryForgeryDigest, interpret_bind, interpret_query,
    interpret_pure, StateT.run_bind, StateT.run_pure, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at h
  obtain ⟨⟨forged, st, _⟩, _, ⟨_, _⟩, hquery, ⟨⟩⟩ := h
  obtain ⟨⟨_, _⟩, hreply, ⟨⟩⟩ := (PMF.mem_support_map_iff ..).1 hquery
  simp only [outerSigningQuery, sumHandler, interpret_query, observedTrial, terminalTrialHandler]
    at hreply
  cases eq : st.lookup (forged.signature.recover d pk, forged.message) with
  | some entry =>
    simp only [eq, PMF.monad_pure_eq_pure, PMF.mem_support_pure_iff, Prod.mk.injEq] at hreply
    simp [hreply.1, hreply.2, eq]
  | none =>
    simp only [eq, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff, Prod.mk.injEq] at hreply
    obtain ⟨c, _, rfl, rfl⟩ := hreply
    simp [SigningWrite.digest]

/-- At a fresh verifying lookup in the adaptive simulator, the newest entry is either a direct
oracle answer or a signing reply on this same message representative. In the latter case the
reply is in the outward transcript and subtracting it from the forgery gives an ordinary MSIS
solution. Overwritten entries, signing errors and exhausted retries require no freshness
assumptions. A first read by the verifier is covered by the direct-oracle case. -/
theorem ambient_or_isSolution_of_fresh_lookup (hP : P.Valid) (hq : 2 * P.γ₁ < P.q)
    (hγq : 4 * P.γ₂ < P.q) (d ω K : ℕ) (hβ : P.β < P.γ₁) (dist : PMF Digest)
    (expand : Digest → Option (Fin P.n → ZMod P.q)) (pk : PublicKey P)
    (forger : OracleComp (SigningROMSpec P Digest) (ForgeryCandidate P Digest))
    {forged : ForgeryCandidate P Digest} {cache log}
    (hrun : ((forged, forged.digest), cache, log) ∈ (simulatePartialSigningTranscript P d ω K hβ
      dist expand pk (queryForgeryDigest P d pk forger)).support)
    (hfresh : ⟨.inl forged.message, some (forged.digest, forged.signature)⟩ ∉ log)
    (hexpand : expand forged.digest = some forged.signature.c)
    (hz : ResponseShort P forged.signature.z) :
    (cache.lookup (forged.signature.recover d pk, forged.message) =
        some (.ambient forged.digest) ∧
      ⟨.inr (forged.signature.recover d pk, forged.message), forged.digest⟩ ∈ log) ∨
    ∃ other, cache.lookup (forged.signature.recover d pk, forged.message) =
        some (.signing forged.digest (some (forged.digest, other))) ∧
      ⟨.inl forged.message, some (forged.digest, other)⟩ ∈ log ∧
      ModuleSIS.IsSolution (ModuleSIS.hermiteMatrix pk.A)
        (max (2 * (P.γ₁ - P.β)) (4 * P.γ₂ + 2))
        (responseDifference d pk forged.signature other) := by
  obtain ⟨entry, he, hd⟩ := Option.map_eq_some_iff.mp
    (lookup_of_queryForgeryDigest P d ω K hβ dist expand pk forger hrun)
  obtain ⟨_, _, hs, _⟩ := List.lookup_eq_some_iff.mp he
  have recorded := recorded_of_mem_simulatePartialSigningTranscript P d ω K hβ dist expand pk
    _ hrun ((forged.signature.recover d pk, forged.message), entry) (by simp [hs])
  rcases entry with x | ⟨x, sent⟩ <;> change x = forged.digest at hd <;> subst x
  · exact Or.inl ⟨he, recorded⟩
  · obtain ⟨inLog, ht⟩ := recorded
    obtain ⟨other, rfl, sol⟩ := isSolution_of_forgery_at_simulated_digest P hP hq hγq d ω hβ pk
      expand _ ht (fun e => hfresh (e ▸ inLog)) hexpand hz rfl
    exact Or.inr ⟨other, he, inLog, sol⟩

end Cslib.Crypto.MLDSA
