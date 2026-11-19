/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.KeySeedSearch
import all CslibFrontier.Crypto.Computational.MLDSA.KeySeedSearch
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Probability.Hellinger
import CslibFrontier.Foundations.Quantum.POVM.Mixture
import CslibFrontier.Foundations.Quantum.Measurement.Classical

/-!
# Adaptive key-seed prediction in ML-DSA

After at most `j` prior coherent SHAKE calls, the probability of predicting the 32-byte
private signing seed in the experiment of `KeySeedSearch` is at most
`(√(2 / 2^256) + 2j / 2^128)^2` at every FIPS level. A classical signature or a measured wire
can determine the next operation. The signer supplies an independent private row of mask seeds
for each signing call, with a fallback when its tape runs out. It runs the FIPS retry loop
using those seeds. If the program stops before query `j`, the public-key hash can still score.

The proof applies the query-magnitude argument of [Bennett et al.][BBBV1997], §3.1,
Theorem 3.3, to the key-generation input of [FIPS 204][NISTFIPS204], Algorithm 6.
For fixed classical history, we pull the continuation measurement back to the retained register.
Replacing a query changes this vector of square roots of acceptance probabilities by at most
`2 / 2^128` in norm, with one coordinate per uniformly weighted hidden key-generation seed.
Classical branching contracts this distance. The background experiment gives two guesses for
the independent signing seed, giving the first term.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

open Cslib.Quantum Cslib.Probability
open scoped ENNReal

private abbrev Test (C : QuantumSigningForger) := POVM Bool ((Fin (Width C) → Bool) × Unit)

private noncomputable def scored {C : QuantumSigningForger} {α : Type} (prog : Program C α)
    (H : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (dev : Device C)
    (log : List Forgery) (tape : List Row) : PMF Bool :=
  ((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (fun _ _ => 0)
    (fun row => C.signingCommand H (sign row))) prog).run ((dev, log), tape)).bind
    fun (x, (st, log'), tape') => (test x log' tape').measureDensity st.density st.isDensityMatrix

private theorem scored_step {C : QuantumSigningForger} {α : Type} {q : Request C}
    {k : _ → Program C α} (H : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (d : Device C)
    (log : List Forgery) (tape : List Row) :
    scored (OracleComp.query q >>= k) H sign test d log tape =
      ((OracleComp.withSampleListWhen isSigningCall (fun _ _ => 0)
        (fun row => C.signingCommand H (sign row)) q).run ((d, log), tape)).bind
        fun (x, (dev, l), t) => scored (k x) H sign test dev l t := by
  simp only [scored, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
  rfl

private theorem scored_coin {C : QuantumSigningForger} {α : Type}
    {coin : ℕ} {k : Fin (coin + 1) → Program C α}
    (T : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (d : Device C) (log : List Forgery)
    (tape : List Row) :
    scored (OracleComp.query (.inl coin) >>= k) T sign test d log tape =
      (ProbComp.unifOracle coin).bind fun i => scored (k i) T sign test d log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, OracleComp.sumHandler,
    StateT.lift, StateT.run, pmf_norm]

private theorem scored_gate {C : QuantumSigningForger} {α : Type}
    {code : PhaseGateCode} {k : List Bool → Program C α}
    (T : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (d : Device C) (log : List Forgery)
    (tape : List Row) :
    scored (OracleComp.query (.inr (.inl (.gate code))) >>= k) T sign test d log tape =
      scored (k []) T sign test
        (d.instruction (T.queryTable C.addressBits C.responseBytes) (.gate code)) log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, deviceCommand,
    OracleComp.sumHandler, deviceHandler_gate, StateT.run, pmf_norm]

private theorem scored_query {C : QuantumSigningForger} {α : Type}
    {k : List Bool → Program C α}
    (T : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (d : Device C) (log : List Forgery)
    (tape : List Row) :
    scored (OracleComp.query (.inr (.inl .query)) >>= k) T sign test d log tape =
      scored (k []) T sign test
        (d.instruction (T.queryTable C.addressBits C.responseBytes) .query) log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, deviceCommand,
    OracleComp.sumHandler, deviceHandler_query, StateT.run, pmf_norm]

private theorem scored_measure {C : QuantumSigningForger} {α : Type}
    {wire : Fin (Width C)} {k : List Bool → Program C α}
    (T : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (d : Device C) (log : List Forgery)
    (tape : List Row) :
    scored (OracleComp.query (.inr (.inl (.measure wire))) >>= k) T sign test d log tape =
      (d.measure (fun x => x wire)).bind
        fun (y, next) => scored (k [y]) T sign test next log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, deviceCommand,
    OracleComp.sumHandler, deviceHandler_measure, StateT.run, pmf_norm]

private theorem scored_sign {C : QuantumSigningForger} {α : Type}
    {ask : SigningQuery} {k : Option (List Byte) → Program C α}
    (T : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (d : Device C) (log : List Forgery)
    (tape : List Row) :
    let sig := sign (tape.headD (fun _ _ => 0)) ask
    scored (OracleComp.query (.inr (.inr ask)) >>= k) T sign test d log tape =
      scored (k sig) T sign test d (ask.logReply sig log) tape.tail := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, OracleComp.withSampleList, isSigningCall,
    signingCommand, OracleComp.sumHandler, StateT.run, pmf_norm]

private theorem measure_map {C : QuantumSigningForger} (d : Device C) (wire : Fin (Width C)) :
    ∃ (p : PMF Bool) (next : Bool → Device C),
      d.measure (fun x => x wire) = p.map (fun y => (y, next y)) := by
  classical
  let f := fun z : (Fin (Width C) → Bool) × Unit => z.1 wire
  let p := (POVM.basis.measureDensity d.density d.isDensityMatrix).map f
  let next (y : Bool) : Device C := if hy : y ∈ p.support then
    ⟨normalizeDensity (classicalDensityBranch f y d.density),
      isDensityMatrix_normalize_classicalDensityBranch _ _ _ _ hy, d.serviceState⟩ else d
  refine ⟨p, next, ?_⟩
  have law := DeviceState.measure_bind (fun x => x wire) d (fun y st => PMF.pure (y, st))
  simp only [Prod.mk.eta, PMF.bind_pure] at law
  rw [law]
  conv_rhs => rw [← PMF.bind_pure_comp, ← PMF.bindOnSupport_eq_bind]
  congr 1
  funext y hy
  change y ∈ p.support at hy
  simp only [Function.comp_apply, next, dite_eq_left hy]
  rfl

private theorem test_instruction {C : QuantumSigningForger} (H : Xofs) (code : OracleGateCode)
    (M : Test C) : ∃ E : Test C, ∀ d : Device C,
      let next := d.instruction (H.queryTable C.addressBits C.responseBytes) code
      M.measureDensity next.density next.isDensityMatrix =
        E.measureDensity d.density d.isDensityMatrix := by
  cases h : code.toPlacedGate? (Width C) (H.queryTable C.addressBits C.responseBytes) with
  | none => exact ⟨M, fun d => by simp only [DeviceState.instruction_apply, h]⟩
  | some g =>
    let U := onFirst (κ := Unit) g.matrix
    refine ⟨M.comap U U.property, fun d => ?_⟩
    ext b
    simp only [POVM.measureDensity_apply, POVM.densityProb_comap, DeviceState.instruction_apply,
      h, DeviceState.evolve_density, U, coe_onFirst]

-- Pull the terminal effect back through the actual adaptive program. Fixing the log and tape
-- leaves a single measurement that works for every density matrix on the retained register.
private theorem scored_readout {C : QuantumSigningForger} {α : Type} (prog : Program C α)
    (H : Xofs) (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C) (log : List Forgery) (tape : List Row) :
    ∃ M : Test C, ∀ d : Device C,
      scored prog H sign test d log tape = M.measureDensity d.density d.isDensityMatrix := by
  classical
  induction prog generalizing log tape with
  | pure x =>
    exact ⟨test x log tape, fun d => by simp [scored, interp_norm, pmf_norm]⟩
  | liftBind q k ih =>
    choose M eq using ih
    change ∃ M : Test C, ∀ d : Device C, scored (OracleComp.query q >>= k) _ _ _ d log tape = _
    rcases q with coin | cmd | ask
    · exact ⟨POVM.mixture (ProbComp.unifOracle coin) (fun i => M i log tape), fun d => by
        simp only [scored_coin (C := C) (k := k) (coin := coin), eq, POVM.measureDensity_mixture]⟩
    · cases cmd with
      | service op _ => exact op.elim
      | gate g =>
        simpa only [scored_gate (C := C) (k := k) (code := g), eq] using
          test_instruction H (.gate g) (M [] log tape)
      | query =>
        simpa only [scored_query (C := C) (k := k), eq] using
          test_instruction H .query (M [] log tape)
      | measure wire =>
        let f := fun (z : (Fin (Width C) → Bool) × Unit) => z.1 wire
        refine ⟨POVM.afterRead f (fun y => M [y] log tape), fun d => ?_⟩
        simp only [scored_measure (C := C) (k := k) (wire := wire), eq,
          POVM.measureDensity_afterRead]
        exact DeviceState.measure_bind (fun x => x wire) d
          (fun y dev => (M [y] log tape).measureDensity dev.density dev.isDensityMatrix)
    · exact ⟨_, fun d => by rw [scored_sign (C := C) (k := k) (ask := ask), eq]⟩

private noncomputable def amps (games : FixedBytes 32 → PMF Bool) :
    EuclideanSpace ℝ (FixedBytes 32) :=
  PMF.weightedSqrt (PMF.uniformOfFintype (FixedBytes 32)) fun seed => (games seed true).toReal

private theorem amps_sq (f g : FixedBytes 32 → PMF Bool) :
    ‖amps f - amps g‖ ^ 2 = ∑ seed : FixedBytes 32,
      ((PMF.uniformOfFintype (FixedBytes 32)) seed).toReal *
        (√((f seed true).toReal) - √((g seed true).toReal)) ^ 2 :=
  PMF.norm_sub_weightedSqrt_sq ..

private theorem amps_bind_le {β : Type} [Finite β] (p : PMF β)
    (f g : β → FixedBytes 32 → PMF Bool) {r : ℝ} (hr : 0 ≤ r)
    (h : ∀ a, ‖amps (f a) - amps (g a)‖ ≤ r) :
    ‖amps (fun i => p.bind fun a => f a i) - amps (fun i => p.bind fun a => g a i)‖ ≤ r := by
  let _ := Fintype.ofFinite β
  let w (i : FixedBytes 32) := ((PMF.uniformOfFintype (FixedBytes 32)) i).toReal
  rw [← sq_le_sq₀ (norm_nonneg _) hr, amps_sq]
  calc
    _ ≤ ∑ i, w i * ∑ a, (p a).toReal *
        (√((f a i true).toReal) - √((g a i true).toReal)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [PMF.bind_apply_toReal]
      exact mul_le_mul_of_nonneg_left (PMF.sq_sqrt_mean_sub_le p _ _
        (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)) ENNReal.toReal_nonneg
    _ = ∑ a, (p a).toReal * ‖amps (f a) - amps (g a)‖ ^ 2 := by
      simp only [amps_sq, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => mul_left_comm ..
    _ ≤ ∑ a, (p a).toReal * r ^ 2 := Finset.sum_le_sum fun a _ =>
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (h a) 2) ENNReal.toReal_nonneg
    _ = r ^ 2 := by rw [← Finset.sum_mul, PMF.sum_toReal, one_mul]

-- In the query case insert one background call followed by the planted continuation.
-- Both continuations then start from the same background state in the inductive comparison.
private theorem scored_bound {C : QuantumSigningForger} {α : Type} {prog : Program C α} {j : ℕ}
    (cost : OracleComp.IsCostBounded (fun q => (isXofQuery (C := C) q).toNat) prog j)
    (s : Level) (H : Xofs) (out : FixedBytes 128)
    (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C)
    (d : Device C) (log : List Forgery) (tape : List Row) :
    ‖amps (fun seed => scored prog (H.withKeySeedExpansion s seed out) sign test d log tape) -
      amps (fun _ => scored prog H sign test d log tape)‖ ≤ j * (2 / 2 ^ 128) := by
  classical
  let G := fun seed => H.withKeySeedExpansion s seed out
  induction cost generalizing d log tape with
  | pure x j =>
    simp [scored, interp_norm, pmf_norm]
  | liftBind q k n _ ih =>
    rcases q with coin | cmd | ask
    · simp only [scored_coin (C := C) (k := k) (coin := coin), isXofQuery, Bool.toNat_false,
        Nat.add_zero]
      exact amps_bind_le _ _ _ (by positivity) fun i => ih i d log tape
    · cases cmd with
      | service op _ => exact op.elim
      | gate g =>
        let next := d.instruction (H.queryTable C.addressBits C.responseBytes) (.gate g)
        simpa only [scored_gate (C := C) (k := k) (code := g), isXofQuery, Bool.toNat_false,
          Nat.add_zero, next,
          DeviceState.instruction_apply, OracleGateCode.toPlacedGate?] using ih [] next log tape
      | measure wire =>
        obtain ⟨p, next, hm⟩ := measure_map d wire
        simp only [scored_measure (C := C) (k := k) (wire := wire), hm, PMF.bind_map,
          Function.comp_def, isXofQuery, Bool.toNat_false, Nat.add_zero]
        exact amps_bind_le _ _ _ (by positivity) fun y => ih [y] (next y) log tape
      | query =>
        let next (T : Xofs) := d.instruction (T.queryTable C.addressBits C.responseBytes) .query
        let tail (T : Xofs) (dev : Device C) := scored (k []) T sign test dev log tape
        choose M hm using fun seed => scored_readout (k []) (G seed) sign test log tape
        have one : ‖amps (fun i => tail (G i) (next (G i))) -
            amps (fun i => tail (G i) (next H))‖ ≤ 2 / 2 ^ 128 := by
          rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), amps_sq]
          have born (i) (dev : Device C) : (tail (G i) dev true).toReal =
              (M i).densityProb dev.density true := by
            simp only [tail, hm, POVM.measureDensity_apply, ENNReal.toReal_ofReal
              ((M i).densityProb_nonneg dev.isDensityMatrix.posSemidef _)]
          simp only [born]
          exact (C.mean_sq_sqrt_keySeedQuery_readout_le s H out d M).trans_eq (by norm_num)
        simp only [scored_query (C := C) (k := k), isXofQuery, Bool.toNat_true, Nat.cast_add,
          Nat.cast_one, add_mul, one_mul]
        change ‖amps (fun i => tail (G i) (next (G i))) - amps (fun _ => tail H (next H))‖ ≤ _
        calc
          _ ≤ ‖amps (fun i => tail (G i) (next (G i))) -
              amps (fun i => tail (G i) (next H))‖ +
              ‖amps (fun i => tail (G i) (next H)) - amps (fun _ => tail H (next H))‖ :=
            norm_sub_le_norm_sub_add_norm_sub ..
          _ ≤ _ := (add_le_add one (ih [] (next H) log tape)).trans_eq (add_comm ..)
    · let sig := sign (tape.headD (fun _ _ => 0)) ask
      simp only [scored_sign (C := C) (k := k) (ask := ask), isXofQuery, Bool.toNat_false,
        Nat.add_zero]
      exact ih sig d (ask.logReply sig log) tape.tail

private theorem prefix_queries_le {C : QuantumSigningForger} {α : Type}
    (p : Program C α) (j : ℕ) :
    OracleComp.IsCostBounded (fun q => (isXofQuery (C := C) q).toNat) (queryPrefix p j) j := by
  induction p generalizing j with
  | pure a => exact .pure _ _
  | liftBind q k ih =>
    rw [queryPrefix]
    split
    · exact .pure _ _
    · rename_i h
      apply OracleComp.IsCostBounded.liftBind_iff.mpr
      refine ⟨?_, fun a => ih a _⟩
      cases hq : isXofQuery (C := C) q <;> simp_all
      lia

private noncomputable def basisScore {C : QuantumSigningForger}
    (f : (Fin (Width C) → Bool) × Unit → Bool) : Test C :=
  POVM.afterRead f (fun y => POVM.const y)

private theorem basisScore_law {C : QuantumSigningForger}
    (f : (Fin (Width C) → Bool) × Unit → Bool) (d : Device C) :
    (basisScore f).measureDensity d.density d.isDensityMatrix =
      (POVM.basis.measureDensity d.density d.isDensityMatrix).map f := by
  simp only [basisScore, POVM.measureDensity_afterRead, POVM.measureDensity_const,
    PMF.bindOnSupport_pure]

private theorem addressTest (C : QuantumSigningForger) (accept : Option (Address C) → Bool)
    (found : Bool) : ∃ M : Test C, ∀ st : State C,
      (addressRead C (found, st)).map accept =
        M.measureDensity st.1.density st.1.isDensityMatrix := by
  cases found with
  | false => exact ⟨POVM.const (accept none), fun st => by simp [addressRead]⟩
  | true =>
    let A := Fin.castLEEmb (Nat.le_add_right (C.addressBits + 2 + 8 * C.responseBytes) C.workQubits)
    let f := fun (z : (Fin (Width C) → Bool) × Unit) =>
      accept (some ((queryRegisters (a := C.addressBits + 2) (b := 8 * C.responseBytes) A z.1).1))
    exact ⟨basisScore f, fun st => by
      simp [addressRead, basisScore_law, PMF.map_comp, Function.comp_def, f, A]⟩

private theorem observations_bound (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (out : FixedBytes 128) (sv : Option RowSigner) {n : ℕ} (rows : SigningMaskSeeds n)
    (j : ℕ) (accept : List (List Bool) → Bool) :
    ‖amps (fun seed =>
        (C.observations (H.withKeySeedExpansion s seed out) s sv rows j).map accept) -
      amps (fun _ => (C.observations H s sv rows j).map accept)‖ ≤ j * (2 / 2 ^ 128) := by
  let report := accept ∘ signingSeedCandidates (C := C) (sv.map RowSigner.hash)
  choose M hm using addressTest C report
  simp only [observations, serviceAddress, addressLaw, PMF.map_comp, withTrialSetup,
    Xofs.expandA_congr (H := H) (K := H.withKeySeedExpansion s _ out) rfl]
  cases sv with
  | none => simp
  | some sv =>
    dsimp only
    cases hA : H.expandA s (sv.publicKey.take 32) with
    | none => simp
    | some A =>
      let p := queryPrefix (C := C) (C.program sv.publicKey) j
      let test := fun (found : Bool) (_ : List Forgery) (_ : List Row) => M found
      let tape := List.ofFn fun i μ => rows (i, μ)
      have law (T : Xofs) :
          ((((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (fun _ _ => 0)
            (fun row => C.signingCommand T (sv.reply row))) p).run (C.initial, tape)).map
              (fun (found, st, _) => (found, st))).bind (addressRead C)).map report =
            scored p T sv.reply test C.initial.1 C.initial.2 tape := by
        simp only [scored, PMF.map_bind, PMF.bind_map, Function.comp_def, hm]
        rfl
      have bound := scored_bound (prefix_queries_le (C.program sv.publicKey) j) s H out
        sv.reply test C.initial.1 C.initial.2 tape
      simpa only [← law, report, p, tape] using bound

private theorem norm_amps_sq (f : FixedBytes 32 → PMF Bool) :
    ‖amps f‖ ^ 2 = (((PMF.uniformOfFintype (FixedBytes 32)).bind f) true).toReal := by
  rw [amps, PMF.norm_weightedSqrt_sq _ _ (fun _ => ENNReal.toReal_nonneg), PMF.bind_apply_toReal]

-- Average over the signing seed K before taking norms. The background gives two guesses
-- independent of K even after the forger has used every available signing row.
private theorem fixed_observations_le (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (p : FixedBytes 96) (sv : Option RowSigner) {n : ℕ} (rows : SigningMaskSeeds n) (j : ℕ) :
    let seeds := PMF.uniformOfFintype (FixedBytes 32)
    (seeds.bind fun seed => seeds.bind fun K =>
      (C.observations (H.withKeySeedExpansion s seed (Fin.append p K)) s sv rows j).map
        fun guesses => guesses.contains (Keccak.bytesToBitsLE K.toList)) true ≤
      ENNReal.ofReal ((√(2 / 2 ^ 256) + j * (2 / 2 ^ 128)) ^ 2) := by
  intro seeds
  let test (K : FixedBytes 32) (xs : List (List Bool)) :=
    xs.contains (Keccak.bytesToBitsLE K.toList)
  let run K (T : Xofs) := (C.observations T s sv rows j).map (test K)
  let game := fun seed =>
    seeds.bind (fun K => run K (H.withKeySeedExpansion s seed (Fin.append p K)))
  let ref := seeds.bind (fun K => run K H)
  have hdist : ‖amps game - amps (fun _ => ref)‖ ≤ j * (2 / 2 ^ 128) :=
    amps_bind_le seeds _ _ (by positivity) fun K => observations_bound C s H (Fin.append p K)
      sv rows j (test K)
  have hmass : ref true ≤ 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    simp only [ref, run, observations, PMF.map_comp]
    change (seeds.bind fun K => (C.serviceAddress H s sv rows j).bind fun addr =>
      PMF.pure (test K (signingSeedCandidates (C := C) (sv.map RowSigner.hash) addr))) true ≤ _
    rw [PMF.bind_comm]
    apply PMF.bind_apply_le_on_support
    intro addr _
    exact two_guesses (C := C) (sv.map RowSigner.hash) addr
  have href : ‖amps (fun _ => ref)‖ ≤ √(2 / 2 ^ 256) := by
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), norm_amps_sq, PMF.bind_const,
      Real.sq_sqrt (by positivity)]
    have r := ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
      (ENNReal.inv_ne_top.mpr (by positivity))) hmass
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_inv,
      ENNReal.toReal_pow, div_eq_mul_inv] using r
  have bound : ‖amps game‖ ≤ √(2 / 2 ^ 256) + j * (2 / 2 ^ 128) := by
    calc
      _ ≤ ‖amps game - amps (fun _ => ref)‖ + ‖amps (fun _ => ref)‖ := by
        simpa only [sub_add_cancel] using norm_add_le (amps game - amps (fun _ => ref))
          (amps (fun _ => ref))
      _ ≤ _ := (add_le_add hdist href).trans_eq (add_comm ..)
  change (seeds.bind game) true ≤ _
  rw [ENNReal.le_ofReal_iff_toReal_le ((seeds.bind game).apply_ne_top true) (sq_nonneg _)]
  rw [← norm_amps_sq]
  exact pow_le_pow_left₀ (norm_nonneg _) bound 2

/-- Predict the 32-byte signing seed with adaptive signatures generated from independent private
mask-seed rows. After `j` earlier coherent queries the square root of success is at most
`2j / 2^128` above the two-guess background bound. On runs ending before the selected call,
the public-key hash remains the only candidate. The probability includes these runs. -/
theorem signingSeedPredictionGame_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b : ℕ} (ha : 272 ≤ a) (hb : 128 ≤ b) (n j : ℕ) :
    (Game.succProbability (C.signingSeedPredictionGame s base a b n j) : ℝ) ≤
      (√(2 / 2 ^ 256) + j * (2 / 2 ^ 128)) ^ 2 := by
  rw [← C.keySeedDeviceGame_true s base ha hb n j, Game.coe_succProbability]
  let bound : ℝ := (√(2 / 2 ^ 256) + j * (2 / 2 ^ 128)) ^ 2
  suffices h : C.keySeedDeviceGame s base a b n j true true ≤ ENNReal.ofReal bound by
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ bound from sq_nonneg _)] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simp only [keySeedDeviceGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ↓reduceIte]
  rw [PMF.bind_comm]
  apply PMF.bind_apply_le_on_support
  intro rows _
  rw [PMF.bind_comm]
  apply PMF.bind_apply_le_on_support
  intro H _
  rw [PMF.bind_comm]
  apply PMF.bind_apply_le_on_support
  intro p _
  exact fixed_observations_le C s H p (rowSigner (setupOracle H s p) s fun _ => 0) rows j

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
