/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.ProgrammedContinuation
-- Reads private `simulated`, `simulated_eq_run`, `simulated_gap`, and `prefixRun` internals.
import all CslibFrontier.Crypto.Computational.MLDSA.ProgrammedContinuation
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Adaptive ML-DSA signing simulation

The hybrid at index `j` serves the first `j` signing requests using native private-expansion
rows. All later requests use the simulated service on the same evolving SHAKE stream. Each
comparison preserves the state of the quantum device, the signing log and the byte verifier.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
open Cslib.Probability Cslib.Quantum
open scoped BigOperators

private noncomputable def mixed (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (prog : C.Program Forgery)
    (i : ℕ) (D : Register s) (d : C.Device) (log : List Forgery) (rows : List (Row s)) : Game :=
  C.prefixRun s (H.withDigestRegister s D) keys prog i d log rows fun x st l _ =>
    C.simulated s H A sk keys.publicKey (resumeProgram x) D st l

private theorem cut_at_budget {C : QuantumSigningForger} (prog : C.Program Forgery) (n : ℕ)
    (calls : OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) prog n) :
    cut prog n = Boundary.finished <$> prog := by
  induction prog generalizing n with
  | pure f => rfl
  | liftBind cmd k ih =>
    obtain ⟨enough, tail⟩ := OracleComp.IsCostBounded.liftBind_iff.mp calls
    rcases cmd with coin | op | q
    any_goals exact congrArg (PFunctor.FreeM.liftBind _) (funext fun r => ih r n (tail r))
    cases n with
    | zero => simp [isSigningCall] at enough
    | succ n => exact congrArg (PFunctor.FreeM.liftBind _) (funext fun r => ih r n (tail r))

private theorem mixed_all_native (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (prog : C.Program Forgery)
    (n : ℕ) (calls : OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) prog n)
    (D : Register s) (d : C.Device) (log : List Forgery) (rows : List (Row s)) :
    C.mixed s H A keys sk prog n D d log rows =
      C.expansionContinuation s (H.withDigestRegister s D) A keys prog d log rows := by
  simp only [mixed, prefixRun, prefixInteraction, cut_at_budget prog n calls,
    OracleComp.run_interpret_map, PMF.monad_map_eq_map, PMF.bind_map, Prod.map_fst,
    Prod.map_snd, id_eq, Function.comp_def, resumeProgram,
    simulated, expansionContinuation, scored, POVM.measureDensity_const, PMF.monad_pure_eq_pure]

private theorem mixed_all_simulated (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (prog : C.Program Forgery)
    (D : Register s) (d : C.Device) (log : List Forgery) (rows : List (Row s)) :
    C.mixed s H A keys sk prog 0 D d log rows =
      C.simulated s H A sk keys.publicKey prog D d log := by
  let G := H.withDigestRegister s D
  induction prog generalizing d log rows with
  | pure f => simp [mixed, prefixRun, prefixInteraction, cut, interp_norm, pmf_norm, resumeProgram]
  | liftBind cmd k ih =>
    have step (skip : isSigningCall cmd = false)
        (push : cut (C := C) (.liftBind cmd k) 0 = .liftBind cmd (fun r => cut (k r) 0)) :
        C.mixed s H A keys sk (.liftBind cmd k) 0 D d log rows =
          (C.signingCommand G (fun q => G.signWithExpansionRow s keys.secretKey q 0)
            cmd (d, log)).bind fun (r, st, l) =>
            C.simulated s H A sk keys.publicKey (k r) D st l := by
      rw [mixed, prefixRun_step C s G keys k 0 0 push]
      simp only [OracleComp.withSampleListWhen, skip, Bool.false_eq_true, ↓reduceIte, StateT.run,
        PMF.bind_map, Function.comp_def]
      exact congrArg (PMF.bind _ ·) (funext fun ⟨r, dev, l⟩ => ih r dev l rows)
    rcases cmd with coin | op | q
    · rw [step rfl rfl]
      simp [signingCommand, OracleComp.sumHandler, StateT.lift, simulated, pmf_norm]
    · rw [step rfl rfl]
      simp only [signingCommand, deviceCommand, OracleComp.sumHandler, PMF.bind_map,
        Function.comp_def, simulated, G]
    · simp only [mixed, prefixRun, prefixInteraction, cut, PFunctor.FreeM.pure_eq_pure,
        OracleComp.run_interpret_pure, PMF.monad_pure_eq_pure, PMF.pure_bind, resumeProgram]

-- Cutting one signing request later executes the stopped request and cuts its continuation
-- at the next one. If the forger already returned, both cuts retain the same forgery.
private def nextCut {C : QuantumSigningForger} : Boundary C → C.Program (Boundary C)
  | .finished f => .pure (.finished f)
  | .signing q k => .liftBind (.inr (.inr q)) fun r => cut (C := C) (k r) 0

private theorem cut_succ {C : QuantumSigningForger} (prog : C.Program Forgery) (i : ℕ) :
    cut prog (i + 1) = (cut prog i >>= nextCut) := by
  induction prog generalizing i with
  | pure f => rfl
  | liftBind cmd k ih =>
    rcases cmd with coin | op | q
    any_goals exact congrArg (PFunctor.FreeM.liftBind _) (funext fun r => ih r i)
    cases i with
    | zero => rfl
    | succ i => exact congrArg (PFunctor.FreeM.liftBind _) (funext fun r => ih r i)

private noncomputable def nativeThenSimulated (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (D : Register s) :
    Resume C s := fun x d l t =>
  match x with
  | .finished f => C.simulated s H A sk keys.publicKey (.pure f) D d l
  | .signing q k =>
    let r := (H.withDigestRegister s D).signWithExpansionRow s keys.secretKey q (t.headD 0)
    C.simulated s H A sk keys.publicKey (k r) D d (q.logReply r l)

private theorem mixed_succ (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (prog : C.Program Forgery)
    (i : ℕ) (D : Register s) (d : C.Device) (log : List Forgery) (rows : List (Row s)) :
    C.mixed s H A keys sk prog (i + 1) D d log rows =
      C.prefixRun s (H.withDigestRegister s D) keys prog i d log rows
        (C.nativeThenSimulated s H A keys sk D) := by
  rw [mixed, prefixRun, prefixInteraction, cut_succ]
  simp only [OracleComp.run_interpret_bind, PMF.monad_bind_eq_bind, PMF.bind_bind]
  apply congrArg (PMF.bind _ ·)
  funext ⟨x, ⟨dev, l⟩, t⟩
  cases x with
  | finished f => simp [nextCut, interp_norm, pmf_norm, resumeProgram, nativeThenSimulated]
  | signing q k =>
    let G := H.withDigestRegister s D
    let r := G.signWithExpansionRow s keys.secretKey q (t.headD 0)
    dsimp only [nextCut, nativeThenSimulated]
    rw [← C.mixed_all_simulated s H A keys sk (k r) D dev (q.logReply r l) t.tail]
    change PMF.bind (StateT.run (OracleComp.interpret _
      (OracleComp.query (.inr (.inr q) : Request C) >>= fun v => cut (C := C) (k v) 0))
        ((dev, l), t)) _ = _
    rw [OracleComp.run_interpret_bind, OracleComp.run_interpret_query]
    simp [r, G, OracleComp.withSampleListWhen, OracleComp.withSampleList,
      isSigningCall, signingCommand, OracleComp.sumHandler, pmf_norm, mixed, prefixRun,
      prefixInteraction]

private noncomputable def simulatedAfter (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (sk : PrivateKey s) (pk : List Byte) : AfterCall C s where
  run T prog d l _ := C.simulated s H A sk pk prog T d l
  readout T prog l _ := C.simulated_readout s H A sk pk prog T l

private theorem mixed_read_window (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    {n : ℕ} (i : Fin n) (D : Register s) :
    let rows := PMF.uniformOfFintype (Fin n → Row s)
    let next := C.simulatedAfter s H A sk keys.publicKey
    (rows.bind fun t => (maskList s 814).bind fun ys =>
      C.callWindow s H A keys sk next i (List.ofFn t) ys 0 D) =
      rows.bind fun t => C.mixed s H A keys sk (C.program keys.publicKey) (i + 1) D
        C.initialDevice [] (List.ofFn t) := by
  intro rows next
  let G := H.withDigestRegister s D
  let go (ys : List (Mask s)) : Resume C s := fun x d l t =>
    C.resumeRetries s H A next sk D 0 x (scanned s G A sk ys x) l t d
  simp only [mixed_succ]
  refine uniform_tape_eq s i
    (fun t => (maskList s 814).bind fun ys =>
      C.prefixRun s G keys (C.program keys.publicKey) i C.initialDevice [] t (go ys))
    (fun t => C.prefixRun s G keys (C.program keys.publicKey) i C.initialDevice [] t
      (C.nativeThenSimulated s H A keys sk D)) fun pre rest len => ?_
  simp only [← len]
  apply prefixRun_mix
  · intros; rfl
  · exact C.all_reads_sign s H keys sk A key mat next D

private theorem mixed_write_window (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s)
    {qH n : ℕ} (hash : C.XofCallsLe qH) (calls : C.SigningCallsLe n) (i : ℕ)
    (D : Register s) (t : List (Row s)) :
    let next := C.simulatedAfter s H A sk keys.publicKey
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    |prob (C.callWindow s H A keys sk next i t [] 814 D) -
      prob (C.mixed s H A keys sk (C.program keys.publicKey) i D C.initialDevice [] t)| ≤
      814 * (4 * qH * √δ + (n + 2) * δ) := by
  intro next δ
  let G := H.withDigestRegister s D
  apply C.cut_bind_gap s G keys i t _ _ (by positivity)
  intro x dev l rows possible
  cases x with
  | finished f =>
    simp only [resumeRetries, resumeProgram, next, simulatedAfter, sub_self, abs_zero]
    positivity
  | signing q k =>
    let done T r := C.simulated s H A sk keys.publicKey (k r) T dev (q.logReply r l)
    change |prob (C.resumeRetries s H A next sk D 814 (.signing q k)
      (scanned s G A sk [] (.signing q k)) l rows dev) -
      prob (registerRequest s H A sk q D false done)| ≤ _
    by_cases big : 255 < q.context.length
    · simp only [scanned, preparedPrefix, registerRequest, big, ↓reduceIte, resumeRetries,
        next, simulatedAfter, done, sub_self, abs_zero]
      positivity
    · simp only [scanned, preparedPrefix, registerRequest, big, ↓reduceIte, List.findSome?_nil,
        resumeRetries, installedAttempt_eq, next, simulatedAfter, done]
      apply eraseRetries_le _ _ _ _ _ (by positivity)
      intro T value r
      exact (C.simulated_gap s H A sk keys.publicKey _ (k r)
        (cut_cost_after (hash _) i possible r) (cut_cost_after (calls _) i possible r)
        T value dev (q.logReply r l)).trans_eq (by ring)

private noncomputable def fixedHybrid (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (A : PublicMatrix s) (keys : KeyPair) (sk : PrivateKey s) (n j : ℕ) : Game :=
  (PMF.uniformOfFintype (Fin n → Row s)).bind fun rs => (PMF.uniformOfFintype (Register s)).bind
    fun D => C.mixed s H A keys sk (C.program keys.publicKey) j D C.initialDevice [] (List.ofFn rs)

private theorem hybrid_adjacent (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    {n qH : ℕ} (calls : C.SigningCallsLe n) (hash : C.XofCallsLe qH) (i : Fin n) :
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    let law := C.fixedHybrid s H A keys sk n
    |prob (law i) - prob (law (i.val + 1))| ≤ 814 * (4 * qH * √δ + (n + 2) * δ) +
      814 * (2 * (4 * qH * √δ + (815 * i.val + 814) * δ)) := by
  intro δ law
  let S := PMF.uniformOfFintype (Fin n → Row s)
  let U := PMF.uniformOfFintype (Register s)
  let next := C.simulatedAfter s H A sk keys.publicKey
  let trial (rs : Fin n → Row s) := C.callWindow s H A keys sk next i (List.ofFn rs)
  let middle := S.bind fun rs => U.bind (trial rs [] 814)
  let start (rs : Fin n → Row s) := (maskList s 814).bind fun ys => U.bind (trial rs ys 0)
  have read : S.bind start = law (i.val + 1) := by
    dsimp only [start, law, fixedHybrid]
    rw [PMF.bind_comm S U]
    simp_rw [PMF.bind_comm (maskList s 814) U, PMF.bind_comm S U]
    exact congrArg (PMF.bind U ·) (funext fun D => C.mixed_read_window s H keys sk A key mat i D)
  have erase : |prob (law i) - prob middle| ≤ 814 * (4 * qH * √δ + (n + 2) * δ) := by
    rw [abs_sub_comm]
    apply abs_common_bind S
    intro rs
    exact abs_common_bind U _ _ fun D => C.mixed_write_window s H A keys sk hash calls i D _
  have retry : |prob middle - prob (law (i.val + 1))| ≤
      814 * (2 * (4 * qH * √δ + (815 * i.val + 814) * δ)) := by
    rw [← read]
    apply abs_common_bind S
    intro rs
    simpa only [List.nil_append, Nat.cast_ofNat, trial, start, δ] using
      C.all_windows s H A keys sk next i (List.ofFn rs) [] 814 (by simp) hash
  exact (abs_sub_le _ (prob middle) _).trans (add_le_add erase retry)

private theorem hybrid_total (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (keys : KeyPair) (sk : PrivateKey s) (A : PublicMatrix s)
    (key : decodePrivate s keys.secretKey = some sk) (mat : H.expandA s sk.rho = some A)
    {n qH : ℕ} (calls : C.SigningCallsLe n) (hash : C.XofCallsLe qH) :
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
    let law := C.fixedHybrid s H A keys sk n
    |prob (law 0) - prob (law n)| ≤ ∑ i ∈ Finset.range n,
      (814 * (4 * qH * √δ + (n + 2) * δ) + 814 * (2 * (4 * qH * √δ + (815 * i + 814) * δ))) := by
  intro δ law
  apply dist_le_range_sum_of_dist_le (f := fun j => prob (law j)) n
  intro k hk
  exact C.hybrid_adjacent s H keys sk A key mat calls hash ⟨k, hk⟩

private noncomputable def seededHybrid (C : QuantumSigningForger) (s : Level) (n j : ℕ)
    (H : Xofs) (seed : FixedBytes 32) : Game :=
  match H.keyGen s seed with
  | none => pure false
  | some keys => match decodePrivate s keys.secretKey, H.expandA s (keys.publicKey.take 32) with
    | some sk, some A => C.fixedHybrid s H A keys sk n j
    | _, _ => pure false

private theorem seeded_all_native (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n : ℕ} (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b)
    (calls : C.SigningCallsLe n) :
    ((base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind (C.seededHybrid s n n H)) =
      C.freshExpansionGame s base a b := by
  rw [C.freshExpansionGame_eq_expansionContinuation s base a b calls]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  apply average_register s base ha hb
  intro H seed
  simp only [seededHybrid, Xofs.keyGen_withDigestRegister]
  cases kg : H.keyGen s seed with
  | none => simp
  | some keys =>
    obtain ⟨rho, pair, mat, pk, sk, _⟩ := privateKey_of_keyGen kg
    have pub : H.expandA s (keys.publicKey.take 32) = some pair.A := by
      rw [pk, take_encodePublic, mat]
    simp only [sk, pub, Xofs.expandA_congr (K := H.withDigestRegister s _) (H := H) rfl s,
      fixedHybrid, C.mixed_all_native s H pair.A keys _ _ n (calls keys.publicKey)]
    rw [PMF.bind_comm]

private theorem seeded_all_simulated (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b) (n : ℕ) :
    ((base.uniformPrefixes a b).bind fun H =>
      (PMF.uniformOfFintype (FixedBytes 32)).bind (C.seededHybrid s n 0 H)) =
      (base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s fun rho pair =>
        (C.publicPairSigning s H rho pair).map (·.trial.newDigestWin) := by
  rw [← C.freshMask_newDigestGame_eq_publicPair]
  unfold Xofs.keyExperiment
  apply average_register s base ha hb
  intro H seed
  simp only [seededHybrid, Xofs.keyGen_withDigestRegister]
  cases kg : H.keyGen s seed with
  | none => simp
  | some keys =>
    obtain ⟨rho, pair, mat, pk, key, _⟩ := privateKey_of_keyGen kg
    have pub : H.expandA s (keys.publicKey.take 32) = some pair.A := by
      rw [pk, take_encodePublic, mat]
    simp only [key, pub, fixedHybrid, mixed_all_simulated, PMF.bind_const]
    apply congrArg (PMF.bind (PMF.uniformOfFintype (Register s)) ·)
    funext D
    have expand : (H.withDigestRegister s D).expandA s rho.toList = some pair.A :=
      (Xofs.expandA_congr (H := H) rfl s _).trans mat
    simp only [freshMaskSigning, key, expand, runProgrammed, runSigningProgram,
      PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.map_bind, PMF.pure_map]
    exact C.simulated_eq_run s H (H.withDigestRegister s D) pair.A _ keys.publicKey
      (C.program keys.publicKey) D C.initialDevice ⟨_, [], [], .initial, by simp, by simp⟩ rfl

/-- Loss from replacing the native commitment digests of all signing requests by independent
samples and erasing rejected writes. The cap is the 814-attempt option of FIPS 204. Each summand
uses the actual matrix's maximum commitment probability and its zero-based signing index. Failed
setup contributes zero. -/
@[expose] noncomputable def adaptiveSigningLoss (s : Level) (base : Xofs) (a b n qH : ℕ) : ℝ :=
  let matrices := (base.uniformPrefixes a b).bind fun H =>
    (PMF.uniformOfFintype (FixedBytes 32)).map fun seed => do
      let keys ← H.keyGen s seed
      H.expandA s (keys.publicKey.take 32)
  ∑ A : Option (PublicMatrix s), (matrices A).toReal * (A.elim 0 fun M =>
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) M).toReal
    ∑ i ∈ Finset.range n, (814 * (4 * qH * √δ + (n + 2) * δ) +
      814 * (2 * (4 * qH * √δ + (815 * i + 814) * δ))))


-- Sum the charges for the earlier native prefix and the later simulated calls.
private theorem sum_request_loss (δ : ℝ) (n qH p : ℕ) :
    (∑ i ∈ Finset.range p, (814 * (4 * qH * √δ + (n + 2) * δ) +
      814 * (2 * (4 * qH * √δ + (815 * i + 814) * δ)))) =
      814 * p * (12 * qH * √δ + (n + 815 * p + 815) * δ) := by
  induction p with
  | zero => simp
  | succ p ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- The total adaptive-signing loss in the seeded FIPS game is bounded by the uniform-matrix
average of the square root of the largest commitment probability. The coefficient includes
all the native and simulated requests and all 814 attempts per request. -/
theorem adaptiveSigningLoss_le_mean_sqrt (s : Level) (base : Xofs) {a b : ℕ} (n qH : ℕ)
    (ha : 272 ≤ a) (hb : 894 ≤ b) :
    adaptiveSigningLoss s base a b n qH ≤ 814 * n * (12 * qH + 816 * n + 815) *
      (𝔼 A : PublicMatrix s, Real.sqrt
        (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal) := by
  classical
  let U := PMF.uniformOfFintype (PublicMatrix s)
  let δ (A : PublicMatrix s) :=
    (commitmentGuessProbability s.params (by cases s <;> decide) A).toReal
  let c : ℝ := 814 * n * (12 * qH + 816 * n + 815)
  have mean : (∑ A, (U A).toReal * (c * √(δ A))) = c * (𝔼 A, √(δ A)) := by
    simp only [U, PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      ← Finset.mul_sum, Finset.expect_eq_sum_div_card, Finset.card_univ, div_eq_inv_mul]
    ring
  change _ ≤ c * (𝔼 A, √(δ A))
  rw [← mean]
  unfold adaptiveSigningLoss
  rw [Fintype.sum_option]
  simp only [Option.elim_none, mul_zero, Option.elim_some, zero_add, sum_request_loss]
  apply Finset.sum_le_sum
  intro A _
  have atom := ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (generatedMatrix_apply_some_le_uniform s base ha hb A)
  apply mul_le_mul atom _ (by positivity) ENNReal.toReal_nonneg
  have le : δ A ≤ √(δ A) := Real.le_sqrt_self_iff.mpr
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa [commitmentGuessProbability] using
      (iSup_le fun w => PMF.coe_le_one _ w : commitmentGuessProbability s.params
        (by cases s <;> decide) A ≤ 1)))
  change 814 * (n : ℝ) * (12 * qH * √(δ A) + (n + 815 * n + 815) * δ A) ≤ c * √(δ A)
  calc
    _ ≤ 814 * (n : ℝ) * (12 * qH * √(δ A) + (n + 815 * n + 815) * √(δ A)) := by gcongr
    _ = _ := by dsimp only [c]; ring

/-- Replace every adaptive signing request in the fresh private-expansion game by the public-pair
simulator. Keys come from the FIPS byte sampler. The left and right games both score fresh-digest
forgeries on their final shared SHAKE streams. At signing index `i` the two losses pay for erasing
rejected writes in the programmed future and for refreshing all digest reads after the native
prefix. The expectation uses the generated matrices, with zero loss at failed setup. -/
theorem abs_freshExpansionGame_sub_publicPairSigning_le (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n qH : ℕ} (ha : s.commitmentInputBits ≤ a) (hb : digestBytes s ≤ b)
    (calls : C.SigningCallsLe n) (hash : C.XofCallsLe qH) :
    let publicGame := (base.uniformPrefixes a b).bind fun H =>
      H.fullPairExperiment s fun rho pair =>
        (C.publicPairSigning s H rho pair).map (·.trial.newDigestWin)
    |(Game.succProbability (C.freshExpansionGame s base a b) : ℝ) -
      Game.succProbability publicGame| ≤
      adaptiveSigningLoss s base a b n qH := by
  intro publicGame
  let test (isNative : Bool) := C.seededHybrid s n (if isNative then n else 0)
  let cost (A : Option (PublicMatrix s)) := A.elim 0 fun M =>
    let δ := (commitmentGuessProbability s.params (by cases s <;> decide) M).toReal
    ∑ i ∈ Finset.range n, (814 * (4 * qH * √δ + (n + 2) * δ) +
      814 * (2 * (4 * qH * √δ + (815 * i + 814) * δ)))
  rw [← C.seeded_all_native s base ha hb calls, show publicGame = _ from
    (C.seeded_all_simulated s base ha hb n).symm]
  apply seeded_gap_le s base a b test cost
  intro H seed
  cases kg : H.keyGen s seed with
  | none => simp [test, seededHybrid, kg, generatedMatrix, cost]
  | some keys =>
    obtain ⟨rho, pair, mat, pk, sk, _⟩ := privateKey_of_keyGen kg
    have pub : H.expandA s (keys.publicKey.take 32) = some pair.A := by
      rw [pk, take_encodePublic, mat]
    simp only [test, seededHybrid, kg, pub, sk, Bool.false_eq_true, ↓reduceIte, generatedMatrix,
      Option.bind_eq_bind, Option.bind_some, cost, Option.elim_some]
    rw [abs_sub_comm]
    exact C.hybrid_total s H keys _ pair.A sk mat calls hash

/-- Strong-forgery bound for the native finite-random-stream experiment after simulating every
adaptive signature. The fresh-digest term uses only the generated full lattice public pair.
The other two terms score the raw hash collision and the constructed Hermite-MSIS solver. -/
theorem randomPrefixGame_forgery_le_publicPairSigning (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n qH : ℕ} (ha : s.commitmentInputBits ≤ a) (hb : 894 ≤ b)
    (calls : C.SigningCallsLe n) (size : n ≤ 2 ^ 256) (hash : C.XofCallsLe qH) :
    let R := base.uniformPrefixes a b
    let trial := R.bind (C.matrixTrial s)
    let publicGame := R.bind fun H => H.fullPairExperiment s fun rho pair =>
      (C.publicPairSigning s H rho pair).map (·.trial.newDigestWin)
    let fresh := (Game.succProbability publicGame : ℝ) + adaptiveSigningLoss s base a b n qH
    let expansion := (√fresh + 2 * qH * √(n / 2 ^ 512)) ^ 2 + 2 * n / 2 ^ 512 +
      ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 513
    let seedLoss : ℝ := 2 * qH * √(2 * n / 2 ^ 256) * (√(2 / 2 ^ 256) + qH * (2 / 2 ^ 128))
    (Game.succProbability (C.randomPrefixGame s base a b) : ℝ) ≤
      (√(expansion + n / 2 ^ 256) + seedLoss) ^ 2 + ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 +
      Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
      Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
        (R.bind fun H => C.matrixSolver s H A).map fun v => decide (ModuleSIS.IsSolution
          (ModuleSIS.hermiteMatrix A) (max (2 * (s.params.γ₁ - s.params.β))
            (4 * s.params.γ₂ + 2)) v)) := by
  intro R trial publicGame fresh expansion seedLoss
  have width : 1024 ≤ s.commitmentInputBits := by cases s <;> decide
  have bytes : digestBytes s ≤ 894 := by cases s <;> decide
  have gap := C.abs_freshExpansionGame_sub_publicPairSigning_le s base ha (bytes.trans hb)
    calls hash
  have le : (Game.succProbability (C.freshExpansionGame s base a b) : ℝ) ≤ fresh := by
    change |_ - (Game.succProbability publicGame : ℝ)| ≤ _ at gap
    exact sub_le_iff_le_add'.mp (abs_le.mp gap).2
  apply (C.randomPrefixGame_forgery_le_freshExpansionGame s base (width.trans ha) hb
    calls size hash).trans
  dsimp only [expansion, seedLoss]
  gcongr

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
