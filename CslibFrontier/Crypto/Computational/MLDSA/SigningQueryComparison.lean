/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import CslibFrontier.Computability.Circuit.Quantum.Oracle.QueryDisturbance
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import all CslibFrontier.Crypto.Computational.MLDSA.SigningMaskSeeds
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Languages.Probabilistic.Presample
import CslibFrontier.Probability.Hellinger
import CslibFrontier.Foundations.Quantum.POVM.Mixture
import CslibFrontier.Foundations.Quantum.Measurement.Classical

/-!
# Comparing coherent SHAKE access in a signed ML-DSA game

Classical signing replies use the same oracle and tape in the two executions. Only the device's
coherent XOR table changes. Each charged probability reads the address in the background run.
The proof applies the query-magnitude argument of [Bennett et al.][BBBV1997], §3.1, Theorem 3.3,
to an adaptive controller with classical signing and intermediate measurements. Each continuation
induces a POVM on the retained state. Classical branching contracts the squared difference of
square roots of acceptance probabilities.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

open Cslib.Quantum Cslib.Probability
open scoped ENNReal

private abbrev Test (C : QuantumSigningForger) := POVM Bool ((Fin (Width C) → Bool) × Unit)

private noncomputable def scored {C : QuantumSigningForger} {α V : Type} [Zero V]
    (prog : Program C α) (H : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (dev : Device C)
    (log : List Forgery) (tape : List V) : PMF Bool :=
  ((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (0 : V)
    (fun row => C.signingCommand H (sign row))) prog).run ((dev, log), tape)).bind
    fun (x, (st, log'), tape') => (test x log' tape').measureDensity st.density st.isDensityMatrix

private theorem scored_step {C : QuantumSigningForger} {α V : Type} [Zero V] {q : Request C}
    {k : _ → Program C α} (H : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C)
    (log : List Forgery) (tape : List V) :
    scored (OracleComp.query q >>= k) H sign test d log tape =
      ((OracleComp.withSampleListWhen isSigningCall (0 : V)
        (fun row => C.signingCommand H (sign row)) q).run ((d, log), tape)).bind
        fun (x, (dev, l), t) => scored (k x) H sign test dev l t := by
  simp only [scored, OracleComp.run_interpret_bind, OracleComp.run_interpret_query,
    Probability.PMF.monad_bind_eq_bind, PMF.bind_bind]
  rfl

private theorem scored_coin {C : QuantumSigningForger} {α V : Type} [Zero V]
    {coin : ℕ} {k : Fin (coin + 1) → Program C α}
    (T : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    scored (OracleComp.query (.inl coin) >>= k) T sign test d log tape =
      (ProbComp.unifOracle coin).bind fun i => scored (k i) T sign test d log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, OracleComp.sumHandler,
    StateT.lift, StateT.run, pmf_norm]

private theorem scored_device {C : QuantumSigningForger} {α V : Type} [Zero V]
    {cmd : DeviceRequest (Width C) Empty} {k : List Bool → Program C α}
    (H : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    scored (OracleComp.query (.inr (.inl cmd)) >>= k) H sign test d log tape =
      (C.deviceCommand H cmd (d, log)).bind
        fun (r, st, _) => scored (k r) H sign test st log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, deviceCommand,
    OracleComp.sumHandler, StateT.run, pmf_norm, Function.comp_def]

private theorem scored_gate {C : QuantumSigningForger} {α V : Type} [Zero V]
    {code : PhaseGateCode} {k : List Bool → Program C α}
    (T : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    scored (OracleComp.query (.inr (.inl (.gate code))) >>= k) T sign test d log tape =
      scored (k []) T sign test
        (d.instruction (T.queryTable C.addressBits C.responseBytes) (.gate code)) log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, deviceCommand,
    OracleComp.sumHandler, deviceHandler_gate, StateT.run, pmf_norm]

private theorem scored_query {C : QuantumSigningForger} {α V : Type} [Zero V]
    {k : List Bool → Program C α}
    (T : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    scored (OracleComp.query (.inr (.inl .query)) >>= k) T sign test d log tape =
      scored (k []) T sign test
        (d.instruction (T.queryTable C.addressBits C.responseBytes) .query) log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, deviceCommand,
    OracleComp.sumHandler, deviceHandler_query, StateT.run, pmf_norm]

private theorem scored_measure {C : QuantumSigningForger} {α V : Type} [Zero V]
    {wire : Fin (Width C)} {k : List Bool → Program C α}
    (T : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    scored (OracleComp.query (.inr (.inl (.measure wire))) >>= k) T sign test d log tape =
      (d.measure (fun x => x wire)).bind
        fun (y, next) => scored (k [y]) T sign test next log tape := by
  rw [scored_step]
  simp [OracleComp.withSampleListWhen, isSigningCall, signingCommand, deviceCommand,
    OracleComp.sumHandler, deviceHandler_measure, StateT.run, pmf_norm]

private theorem scored_sign {C : QuantumSigningForger} {α V : Type} [Zero V]
    {ask : SigningQuery} {k : Option (List Byte) → Program C α}
    (T : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    let sig := sign (tape.headD 0) ask
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

-- Pull a readout back through one actual device instruction, with the rest of the
-- computation allowed to depend on a measured reply.
private theorem device_readout {C : QuantumSigningForger} {σ : Type} (G : Xofs)
    (cmd : DeviceRequest (Width C) Empty) (s : σ) (tail : List Bool → Device C → Game)
    (test : ∀ r, ∃ M : Test C, ∀ d : Device C,
      tail r d = M.measureDensity d.density d.isDensityMatrix) :
    ∃ E : Test C, ∀ d : Device C,
      ((C.deviceCommand G cmd (d, s)).bind fun (r, st, _) => tail r st) =
        E.measureDensity d.density d.isDensityMatrix := by
  choose M law using test
  cases cmd with
  | service op _ => exact op.elim
  | gate g =>
    simpa only [deviceCommand, deviceHandler_gate, pmf_norm, Function.comp_def, law] using
      test_instruction G (.gate g) (M [])
  | query =>
    simpa only [deviceCommand, deviceHandler_query, pmf_norm, Function.comp_def, law] using
      test_instruction G .query (M [])
  | measure wire =>
    let f := fun (z : (Fin (Width C) → Bool) × Unit) => z.1 wire
    refine ⟨POVM.afterRead f (fun y => M [y]), fun d => ?_⟩
    simp only [deviceCommand, deviceHandler_measure, pmf_norm, Function.comp_def, law,
      POVM.measureDensity_afterRead]
    exact DeviceState.measure_bind (fun x => x wire) d
      (fun y st => (M [y]).measureDensity st.density st.isDensityMatrix)

-- Pull the terminal effect back through the actual adaptive program. Fixing the log and tape
-- leaves a single measurement that works for every density matrix on the retained register.
private theorem scored_readout {C : QuantumSigningForger} {α V : Type} [Zero V]
    (prog : Program C α) (H : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (log : List Forgery) (tape : List V) :
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
    · simp only [scored_device (C := C) (cmd := cmd) (k := k)]
      exact device_readout H cmd log _ (fun r => ⟨M r log tape, eq r log tape⟩)
    · exact ⟨_, fun d => by rw [scored_sign (C := C) (k := k) (ask := ask), eq]⟩

private noncomputable def basisScore {C : QuantumSigningForger}
    (f : (Fin (Width C) → Bool) × Unit → Bool) : Test C :=
  POVM.afterRead f (fun y => POVM.const y)

private theorem basisScore_law {C : QuantumSigningForger}
    (f : (Fin (Width C) → Bool) × Unit → Bool) (d : Device C) :
    (basisScore f).measureDensity d.density d.isDensityMatrix =
      (POVM.basis.measureDensity d.density d.isDensityMatrix).map f := by
  simp only [basisScore, POVM.measureDensity_afterRead, POVM.measureDensity_const,
    PMF.bindOnSupport_pure]

private noncomputable def addressTest (C : QuantumSigningForger)
    (accept : Option (Address C) → Bool) (found : Bool) : Test C :=
  if found then
    let A := Fin.castLEEmb (Nat.le_add_right (C.addressBits + 2 + 8 * C.responseBytes) C.workQubits)
    basisScore fun z => accept (some
      ((queryRegisters (a := C.addressBits + 2) (b := 8 * C.responseBytes) A z.1).1))
  else POVM.const (accept none)

private theorem addressTest_law (C : QuantumSigningForger) (accept : Option (Address C) → Bool)
    (found : Bool) (st : State C) :
    (addressRead C (found, st)).map accept =
      (addressTest C accept found).measureDensity st.1.density st.1.isDensityMatrix := by
  cases found <;> simp [addressTest, addressRead, basisScore_law, PMF.map_comp, Function.comp_def]

private noncomputable def gap (p q : PMF Bool) : ℝ :=
  (√((p true).toReal) - √((q true).toReal)) ^ 2

private noncomputable def changed (C : QuantumSigningForger) (G H : Xofs) (addr : Address C) :=
  decide (G.queryTable C.addressBits C.responseBytes addr ≠
    H.queryTable C.addressBits C.responseBytes addr)

private noncomputable def detector (C : QuantumSigningForger) (G H : Xofs)
    (found : Bool) : Test C :=
  addressTest C (fun a => a.any (changed C G H)) found

private noncomputable def hit {C : QuantumSigningForger} {α V : Type} [Zero V] (prog : Program C α)
    (G H : Xofs) (sign : V → SigningQuery → Option (List Byte)) (d : Device C)
    (log : List Forgery) (tape : List V) (j : ℕ) : PMF Bool :=
  scored (queryPrefix prog j) H sign (fun found _ _ => detector C G H found) d log tape

private theorem hit_mean_le {C : QuantumSigningForger} {α V ι : Type} [Zero V]
    (p : PMF ι) (G : ι → Xofs) (H : Xofs) (prog : Program C α)
    (sign : V → SigningQuery → Option (List Byte)) (dev : Device C) (log : List Forgery)
    (tape : List V) (j : ℕ) {ε : ℝ≥0∞}
    (bound : ∀ a : Option (Address C),
      (p.bind fun i => PMF.pure (a.any (changed C (G i) H))) true ≤ ε) :
    (p.bind fun i => hit prog (G i) H sign dev log tape j) true ≤ ε := by
  simp only [hit, scored]
  rw [PMF.bind_comm]
  apply PMF.bind_apply_le_on_support
  rintro ⟨found, ⟨st, hist⟩, rest⟩ _
  simp only [detector, ← addressTest_law C _ found (st, hist), ← PMF.bind_pure_comp,
    Function.comp_def]
  rw [PMF.bind_comm]
  exact PMF.bind_apply_le_on_support _ fun a _ => bound a

private theorem gap_bind_mean {β : Type} [Fintype β] (p : PMF β) (x y : β → PMF Bool)
    (B : β → ℝ) (h : ∀ b, gap (x b) (y b) ≤ B b) :
    gap (p.bind x) (p.bind y) ≤ ∑ b, (p b).toReal * B b := by
  unfold gap
  simp only [PMF.bind_apply_toReal]
  exact (PMF.sq_sqrt_mean_sub_le p _ _ (fun _ => ENNReal.toReal_nonneg)
    (fun _ => ENNReal.toReal_nonneg)).trans (Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_left (h b) ENNReal.toReal_nonneg)

-- The same finite classical choice precedes both executions and every measured prefix.
private theorem gap_bind_le {β : Type} [Finite β] (p : PMF β) (x y : β → PMF Bool)
    (hits : β → ℕ → PMF Bool) (n : ℕ)
    (h : ∀ b, gap (x b) (y b) ≤ 4 * n * ∑ j ∈ Finset.range n, (hits b j true).toReal) :
    gap (p.bind x) (p.bind y) ≤
      4 * n * ∑ j ∈ Finset.range n, ((p.bind fun b => hits b j) true).toReal := by
  let _ := Fintype.ofFinite β
  apply (gap_bind_mean p x y _ h).trans_eq
  simp only [PMF.bind_apply_toReal, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => mul_left_comm ..

private theorem gap_step {u v w h B : ℝ} (n : ℕ) (hB : 0 ≤ B)
    (one : (u - v) ^ 2 ≤ 4 * h) (rest : (v - w) ^ 2 ≤ 4 * n * B) :
    (u - w) ^ 2 ≤ 4 * (n + 1 : ℕ) * (h + B) := by
  cases n with
  | zero =>
    simp only [Nat.cast_zero, mul_zero, zero_mul] at rest
    obtain rfl : v = w := by nlinarith [sq_nonneg (v - w)]
    push_cast
    linarith
  | succ n =>
    let m : ℝ := (n : ℝ) + 1
    have hm : 0 < m := by dsimp [m]; positivity
    change (v - w) ^ 2 ≤ 4 * ((n + 1 : ℕ) : ℝ) * B at rest
    push_cast at rest ⊢
    change (v - w) ^ 2 ≤ 4 * m * B at rest
    change (u - w) ^ 2 ≤ 4 * (m + 1) * (h + B)
    apply le_of_mul_le_mul_left _ hm
    have a := mul_le_mul_of_nonneg_left one (show 0 ≤ m * (m + 1) by positivity)
    have b := mul_le_mul_of_nonneg_left rest (show 0 ≤ m + 1 by positivity)
    nlinarith only [a, b, sq_nonneg (m * (u - v) - (v - w))]

private theorem single_gap (C : QuantumSigningForger) (G H : Xofs) (d : Device C) (M : Test C) :
    let next := fun (T : Xofs) => d.instruction (T.queryTable C.addressBits C.responseBytes) .query
    gap (M.measureDensity (next G).density (next G).isDensityMatrix)
        (M.measureDensity (next H).density (next H).isDensityMatrix) ≤
      4 * (((detector C G H true).measureDensity d.density d.isDensityMatrix) true).toReal := by
  classical
  intro next
  let A := Fin.castLEEmb (Nat.le_add_right (C.addressBits + 2 + 8 * C.responseBytes) C.workQubits)
  have born (T : Xofs) :
      ((M.measureDensity (next T).density (next T).isDensityMatrix) true).toReal =
        M.densityProb (next T).density true := by
    rw [POVM.measureDensity_apply, ENNReal.toReal_ofReal
      (M.densityProb_nonneg (next T).isDensityMatrix.posSemidef true)]
  simp only [gap, born, detector, addressTest, ↓reduceIte, Option.any_some, basisScore_law]
  exact (d.sq_sqrt_query_readout_sub_le M true (G.queryTable C.addressBits C.responseBytes)
    (H.queryTable C.addressBits C.responseBytes)).trans
    (xorQueryDisturbance_le _ _ A d.isDensityMatrix)

private theorem hit_skip {C : QuantumSigningForger} {α V : Type} [Zero V]
    (q : Request C) (k : _ → Program C α) (hq : isXofQuery q = false)
    (G H : Xofs) (sign : V → SigningQuery → Option (List Byte)) (dev : Device C)
    (log : List Forgery) (tape : List V) (j : ℕ) :
    hit (OracleComp.query q >>= k) G H sign dev log tape j =
      scored (OracleComp.query q >>= fun x => queryPrefix (C := C) (k x) j) H sign
        (fun found _ _ => detector C G H found) dev log tape := by
  change scored (queryPrefix (C := C) (.liftBind q k) j) _ _ _ _ _ _ = _
  rw [queryPrefix]
  simp only [hq, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.sub_zero]
  rfl

private theorem scored_gap_le {C : QuantumSigningForger} {α V : Type} [Zero V]
    {prog : Program C α} {m : ℕ}
    (cost : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) prog m)
    (G H : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    gap (scored prog G sign test d log tape) (scored prog H sign test d log tape) ≤
      4 * m * ∑ j ∈ Finset.range m, (hit prog G H sign d log tape j true).toReal := by
  classical
  induction cost generalizing d log tape with
  | pure x n =>
    simp only [scored, interp_norm, pmf_norm, gap, sub_self, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    positivity
  | liftBind q k n _ ih =>
    rcases q with coin | cmd | ask
    · simp only [hit_skip (.inl coin) k rfl, scored_coin (C := C) (coin := coin),
        isXofQuery, Bool.toNat_false, Nat.add_zero]
      exact gap_bind_le _ _ _ (fun i j => hit (k i) G H sign d log tape j) n
        fun i => ih i d log tape
    · cases cmd with
      | service op _ => exact op.elim
      | gate g =>
        let next := d.instruction (H.queryTable C.addressBits C.responseBytes) (.gate g)
        simp only [hit_skip (.inr (.inl (.gate g))) k rfl, scored_gate (C := C) (code := g),
          isXofQuery, Bool.toNat_false, Nat.add_zero]
        simpa only [hit, next, DeviceState.instruction_apply, OracleGateCode.toPlacedGate?] using
          ih [] next log tape
      | measure wire =>
        obtain ⟨p, next, hm⟩ := measure_map d wire
        simp only [hit_skip (.inr (.inl (.measure wire))) k rfl,
          scored_measure (C := C) (wire := wire), hm, PMF.bind_map,
          Function.comp_def, isXofQuery, Bool.toNat_false, Nat.add_zero]
        exact gap_bind_le _ _ _ (fun y j => hit (k [y]) G H sign (next y) log tape j) n
          fun y => ih [y] (next y) log tape
      | query =>
        -- Keep the suffix on G while changing this call, then compare suffixes from next H.
        let next (T : Xofs) := d.instruction (T.queryTable C.addressBits C.responseBytes) .query
        let tail (T : Xofs) (dev : Device C) := scored (k []) T sign test dev log tape
        let h := ((detector C G H true).measureDensity d.density d.isDensityMatrix true).toReal
        have hz : hit (OracleComp.query (.inr (.inl .query)) >>= k) G H sign d log tape 0 =
            (detector C G H true).measureDensity d.density d.isDensityMatrix := by
          change scored (queryPrefix (C := C) (.liftBind (.inr (.inl .query)) k) 0) _ _ _ _ _ _ = _
          rw [queryPrefix]
          simp [isXofQuery, scored, interp_norm, pmf_norm]
        have hs (j : ℕ) :
            hit (OracleComp.query (.inr (.inl .query)) >>= k) G H sign d log tape (j + 1) =
              hit (k []) G H sign (next H) log tape j := by
          change scored (queryPrefix (C := C)
            (.liftBind (.inr (.inl .query)) k) (j + 1)) _ _ _ _ _ _ = _
          rw [queryPrefix]
          simp only [isXofQuery, Nat.succ_ne_zero, beq_iff_eq, Bool.true_and, Bool.toNat_true,
            ↓reduceIte, Nat.add_sub_cancel]
          exact scored_query (C := C) (k := fun x => queryPrefix (C := C) (k x) j) ..
        obtain ⟨M, eq⟩ := scored_readout (k []) G sign test log tape
        have one : gap (tail G (next G)) (tail G (next H)) ≤ 4 * h := by
          simpa only [tail, eq, h, next] using single_gap C G H d M
        have rest := ih [] (next H) log tape
        simp only [scored_query (C := C) (k := k), isXofQuery, Bool.toNat_true,
          Finset.sum_range_succ', hs, hz]
        rw [add_comm (∑ _ ∈ _, _)]
        exact gap_step n (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) one rest
    · let sig := sign (tape.headD 0) ask
      simp only [hit_skip (.inr (.inr ask)) k rfl, scored_sign (C := C) (ask := ask),
        isXofQuery, Bool.toNat_false, Nat.add_zero]
      simpa only [hit, sig] using ih sig d (ask.logReply sig log) tape.tail

/-- Every execution of the forger, for every published key, makes at most `m` coherent
queries to the shared XOFs. Classical signing and private gates have zero cost here. -/
@[expose] def XofCallsLe (C : QuantumSigningForger) (m : ℕ) : Prop :=
  ∀ pk, OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) (C.program pk) m

private theorem setup_gap_le (C : QuantumSigningForger) (s : Level) (seed : FixedBytes 32)
    {n m : ℕ} (t : Fin n ↪ FixedBytes 32) (pair : SigningMaskSeedOracles)
    (hm : C.XofCallsLe m) (score : SignedMatrixTrial s → Bool) :
    gap (C.scoreWithSetup s pair.shared pair.shared (pair.background.keyGen s seed)
        (List.ofFn t) score)
        (C.scoreWithSetup s pair.background pair.shared (pair.background.keyGen s seed)
        (List.ofFn t) score) ≤
      4 * m * ∑ j ∈ Finset.range m,
        (((C.actualAddress s seed t pair j).map (differs C pair)) true).toReal := by
  classical
  simp only [scoreWithSetup, scoreTranscript, actualAddress, addressLaw, withTrialSetup]
  cases hkey : pair.background.keyGen s seed with
  | none => simp [gap, differs]
  | some keys =>
    dsimp only
    cases hA : pair.shared.expandA s (keys.publicKey.take 32) with
    | none => simp [gap, differs]
    | some A =>
      let prog := C.program keys.publicKey
      let sign := fun (r : FixedBytes 32) (q : SigningQuery) =>
        pair.shared.sign s keys.secretKey q.message q.context r
      let test := fun (f : Forgery) (log : List Forgery) (_ : List (FixedBytes 32)) =>
        (POVM.const (score ⟨pair.shared, A, keys.publicKey, f, log⟩) : Test C)
      have law (T : Xofs) :
          (C.transcriptWithHedges T pair.shared s keys (List.ofFn t)).map
            (fun (f, log) => score ⟨pair.shared, A, keys.publicKey, f, log⟩) =
          scored prog T sign test C.initial.1 C.initial.2 (List.ofFn t) := by
        simp only [transcriptWithHedges, scored, test, POVM.measureDensity_const, PMF.map_comp,
          Function.comp_def]
        rfl
      have measure (found : Bool) (dev : Device C) (log : List Forgery) :
          ((addressRead C (found, dev, log)).map (differs C pair)) =
            (detector C pair.shared pair.background found).measureDensity dev.density
              dev.isDensityMatrix := by
        have eq (a : Option (Address C)) : differs C pair a =
            a.any (changed C pair.shared pair.background) := by cases a <;> rfl
        simpa only [funext eq, detector] using
          addressTest_law C (fun a => a.any (changed C pair.shared pair.background))
            found (dev, log)
      simp only [law, PMF.map_bind, PMF.bind_map, Function.comp_def, measure]
      exact scored_gap_le (hm keys.publicKey) pair.shared pair.background sign test
        C.initial.1 C.initial.2 (List.ofFn t)

/-- Squared change in square-root success between the two complete signed mask-seed games.
Each summand measures the actual address before the corresponding call in the background
execution. Both sides retain the signing transcript and evaluate the same final event. -/
theorem maskSeedGame_sq_sqrt_sub_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n m : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (hm : C.XofCallsLe m) (score : SignedMatrixTrial s → Bool) :
    (√(Game.succProbability (C.maskSeedGame s base ha hb hn hsize true score) : ℝ) -
      √(Game.succProbability (C.maskSeedGame s base ha hb hn hsize false score) : ℝ)) ^ 2 ≤
      4 * m * ∑ j ∈ Finset.range m,
        (Game.succProbability (C.maskSeedQueryHit s base ha hb hsize j) : ℝ) := by
  classical
  simp only [Game.coe_succProbability]
  change gap _ _ ≤ _
  simp only [maskSeedGame, maskSeedQueryHit, withMaskSeedOracles, Xofs.sampleSigningMaskSeeds,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, PMF.bind_bind, PMF.pure_bind,
    ↓reduceIte]
  apply gap_bind_le
  intro t
  apply gap_bind_le
  intro seed
  apply gap_bind_le
  intro rows
  apply gap_bind_le
  intro T₁
  apply gap_bind_le
  intro T₂
  exact setup_gap_le C s seed t _ hm score

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
