/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import CslibFrontier.Computability.Circuit.Quantum.Oracle.QueryDisturbance
-- Reads private `Address`, `addressLaw`, `actualAddress`, `addressRead`, and `differs`.
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Probability.Hellinger
import CslibFrontier.Foundations.Quantum.POVM.Mixture
import CslibFrontier.Foundations.Quantum.Measurement.Classical

/-!
# Comparing coherent SHAKE access in a signed ML-DSA game

Classical signing replies use the same oracle and tape in the two executions. Only the device's
coherent XOR table changes. Each charged probability reads the address in the background run.
[Bennett et al.][BBBV1997], §3.1, Theorem 3.3 bounds the Euclidean disturbance of a unitary
query computation. We extend that argument to measured acceptance probabilities with adaptive
classical signing, finite-support randomized replies and history-dependent query tables.
Each continuation induces a POVM on the retained state. Classical branching contracts the squared
difference of square roots of acceptance probabilities.
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

private theorem support_law {α : Type} (p : PMF α) :
    ∃ r : PMF p.support, r.map Subtype.val = p := by
  refine ⟨p.bindOnSupport (fun a ha => PMF.pure ⟨a, ha⟩), ?_⟩
  rw [PMF.map, ← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.pure_bindOnSupport, Function.comp_apply, PMF.bindOnSupport_pure]

section StatefulSigning

variable {C : QuantumSigningForger} {σ : Type}
  (sign : SigningQuery → σ → PMF (Option (List Byte) × σ)) (raw : σ → Xofs)

private noncomputable def measured (sign : SigningQuery → σ → PMF (Option (List Byte) × σ))
    (raw : σ → Xofs) {α : Type} (prog : Program C α)
    (test : α → σ → Test C) (d : Device C) (st : σ) : PMF Bool :=
  (ProbOracleComp.runWith (C.statefulSigningCommands raw sign)
    prog (d, st)).bind fun (x, dev, t) => (test x t).measureDensity dev.density dev.isDensityMatrix

private theorem measured_step {α : Type} {q : Request C} {k : _ → Program C α}
    (test : α → σ → Test C) (d : Device C) (st : σ) :
    measured sign raw (OracleComp.query q >>= k) test d st =
      (OracleComp.sumHandler (m := StateT (Device C × σ) PMF)
        (fun n z => (ProbComp.unifOracle n).map (·, z))
        (C.statefulSigningCommands raw sign) q (d, st)).bind
        fun (x, dev, t) => measured sign raw (k x) test dev t := by
  simp only [measured, ProbOracleComp.runWith, OracleComp.runWith_bind, OracleComp.runWith_query,
    PMF.bind_bind]
  rfl

private theorem measured_pure {α : Type} (x : α) (test : α → σ → Test C)
    (d : Device C) (st : σ) :
    measured sign raw (pure x) test d st =
      (test x st).measureDensity d.density d.isDensityMatrix := by
  simp [measured, ProbOracleComp.runWith_pure]

private theorem measured_coin {α : Type} {coin : ℕ} {k : Fin (coin + 1) → Program C α}
    (test : α → σ → Test C) (d : Device C) (st : σ) :
    measured sign raw (OracleComp.query (.inl coin) >>= k) test d st =
      (ProbComp.unifOracle coin).bind fun i => measured sign raw (k i) test d st := by
  rw [measured_step]
  simp [OracleComp.sumHandler, pmf_norm]

private theorem measured_device {α : Type} {cmd : DeviceRequest (Width C) Empty}
    {k : List Bool → Program C α} (test : α → σ → Test C) (d : Device C) (st : σ) :
    measured sign raw (OracleComp.query (.inr (.inl cmd)) >>= k) test d st =
      (C.deviceCommand (raw st) cmd (d, st)).bind
        fun (r, dev, _) => measured sign raw (k r) test dev st := by
  rw [measured_step]
  simp [statefulSigningCommands, OracleComp.sumHandler, deviceCommand, pmf_norm, Function.comp_def]

private theorem measured_gate {α : Type} {g : PhaseGateCode} {k : List Bool → Program C α}
    (test : α → σ → Test C) (d : Device C) (st : σ) :
    measured sign raw (OracleComp.query (.inr (.inl (.gate g))) >>= k) test d st =
      measured sign raw (k []) test
        (d.instruction ((raw st).queryTable C.addressBits C.responseBytes) (.gate g)) st := by
  rw [measured_step]
  simp [statefulSigningCommands, OracleComp.sumHandler, deviceCommand, deviceHandler_gate, pmf_norm]

private theorem measured_query {α : Type} {k : List Bool → Program C α}
    (test : α → σ → Test C) (d : Device C) (st : σ) :
    measured sign raw (OracleComp.query (.inr (.inl .query)) >>= k) test d st =
      measured sign raw (k []) test
        (d.instruction ((raw st).queryTable C.addressBits C.responseBytes) .query) st := by
  rw [measured_step]
  simp [statefulSigningCommands, OracleComp.sumHandler, deviceCommand, deviceHandler_query,
    pmf_norm]

private theorem measured_measure {α : Type} {wire : Fin (Width C)} {k : List Bool → Program C α}
    (test : α → σ → Test C) (d : Device C) (st : σ) :
    measured sign raw (OracleComp.query (.inr (.inl (.measure wire))) >>= k) test d st =
      (d.measure (fun x => x wire)).bind fun (y, dev) => measured sign raw (k [y]) test dev st := by
  rw [measured_step]
  simp [statefulSigningCommands, OracleComp.sumHandler, deviceCommand, deviceHandler_measure,
    pmf_norm]

private theorem measured_sign {α : Type} {ask : SigningQuery}
    {k : Option (List Byte) → Program C α}
    (test : α → σ → Test C) (d : Device C) (st : σ) :
    measured sign raw (OracleComp.query (.inr (.inr ask)) >>= k) test d st =
      (sign ask st).bind fun (r, t) =>
        measured sign raw (k r) test d t := by
  rw [measured_step]
  simp [statefulSigningCommands, OracleComp.sumHandler, pmf_norm]

private theorem measured_readout {α : Type}
    (finiteSign : ∀ q st, (sign q st).support.Finite) (p : Program C α)
    (test : α → σ → Test C) (st : σ) :
    ∃ M : Test C, ∀ d, measured sign raw p test d st =
      M.measureDensity d.density d.isDensityMatrix := by
  classical
  induction p generalizing st with
  | pure x =>
    exact ⟨test x st, fun d => by simp [measured, interp_norm, pmf_norm]⟩
  | liftBind q k ih =>
    choose M eq using ih
    change ∃ M : Test C, ∀ d, measured _ _ (OracleComp.query q >>= k) _ d st = _
    rcases q with coin | cmd | ask
    · exact ⟨POVM.mixture (ProbComp.unifOracle coin) (fun i => M i st), fun d => by
        simp only [measured_coin sign raw (coin := coin) (k := k), eq,
          POVM.measureDensity_mixture]⟩
    · simp only [measured_device sign raw (cmd := cmd) (k := k)]
      exact device_readout (raw st) cmd st _ (fun r => ⟨M r st, eq r st⟩)
    · simp only [measured_sign sign raw (ask := ask) (k := k)]
      let p := sign ask st
      obtain ⟨r, law⟩ := support_law p
      let _ := (finiteSign ask st).fintype
      refine ⟨POVM.mixture r (fun z => M z.1.1 z.1.2), fun d => ?_⟩
      simp only [eq, POVM.measureDensity_mixture]
      change p.bind _ = _
      conv_lhs => rw [← law, PMF.bind_map]
      rfl

private noncomputable def changedAt {α : Type} (G R : σ → Xofs)
    (p : Program C α) (d : Device C) (st : σ) (j : ℕ) : PMF Bool :=
  measured sign R (queryPrefix p j) (fun b t => detector C (G t) (R t) b) d st

private theorem changedAt_skip {α : Type} (G R : σ → Xofs)
    (q : Request C) (k : _ → Program C α) (hq : isXofQuery q = false)
    (d : Device C) (st : σ) (j : ℕ) :
    changedAt sign G R (OracleComp.query q >>= k) d st j =
      measured sign R (OracleComp.query q >>= fun x => queryPrefix (C := C) (k x) j)
        (fun found t => detector C (G t) (R t) found) d st := by
  change measured sign R (queryPrefix (C := C) (.liftBind q k) j) _ _ _ = _
  rw [queryPrefix]
  simp only [hq, Bool.false_and, Bool.false_eq_true, ↓reduceIte, Bool.toNat_false, Nat.sub_zero]
  rfl

private theorem finite_gap {β : Type} (p : PMF β) (hp : p.support.Finite)
    (x y : β → PMF Bool) (hits : β → ℕ → PMF Bool) (n : ℕ)
    (h : ∀ b, gap (x b) (y b) ≤ 4 * n * ∑ j ∈ Finset.range n, (hits b j true).toReal) :
    gap (p.bind x) (p.bind y) ≤
      4 * n * ∑ j ∈ Finset.range n, ((p.bind fun b => hits b j) true).toReal := by
  obtain ⟨r, law⟩ := support_law p
  let _ := hp.fintype
  have eq {γ : Type} (k : β → PMF γ) : p.bind k = r.bind (k ∘ Subtype.val) := by
    conv_lhs => rw [← law, PMF.bind_map]
  simp only [eq]
  exact gap_bind_le r _ _ (fun b => hits b.val) n fun b => h b

private theorem measured_gap {α : Type}
    (finiteSign : ∀ q st, (sign q st).support.Finite) (G R : σ → Xofs)
    {p : Program C α} {m : ℕ}
    (cost : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) p m)
    (test : α → σ → Test C) (d : Device C) (st : σ) :
    gap (measured sign G p test d st) (measured sign R p test d st) ≤
      4 * m * ∑ j ∈ Finset.range m, (changedAt sign G R p d st j true).toReal := by
  classical
  induction cost generalizing d st with
  | pure x n =>
    simp only [measured_pure, gap, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    positivity
  | liftBind q k n _ ih =>
    rcases q with coin | cmd | ask
    · have runPrefix (j : ℕ) := (changedAt_skip sign G R (.inl coin) k rfl d st j).trans
          (measured_coin sign R (coin := coin) (k := fun x => queryPrefix (k x) j) _ d st)
      rw [measured_coin sign G (k := k), measured_coin sign R (k := k)]
      simp only [runPrefix, isXofQuery, Bool.toNat_false, Nat.add_zero]
      exact gap_bind_le _ _ _ (fun i j => changedAt sign G R (k i) d st j) n fun i => ih i d st
    · cases cmd with
      | service op _ => exact op.elim
      | gate g =>
        let dev := d.instruction ((R st).queryTable C.addressBits C.responseBytes) (.gate g)
        have runPrefix (j : ℕ) :=
          (changedAt_skip sign G R (.inr (.inl (.gate g))) k rfl d st j).trans
            (measured_gate sign R (g := g) (k := fun x => queryPrefix (k x) j) _ d st)
        rw [measured_gate sign G (k := k), measured_gate sign R (k := k)]
        simp only [runPrefix, isXofQuery, Bool.toNat_false, Nat.add_zero]
        simpa only [changedAt, dev, DeviceState.instruction_apply, OracleGateCode.toPlacedGate?]
          using ih [] dev st
      | measure wire =>
        obtain ⟨r, next, hm⟩ := measure_map d wire
        have runPrefix (j : ℕ) :=
          (changedAt_skip sign G R (.inr (.inl (.measure wire))) k rfl d st j).trans
            (measured_measure sign R (wire := wire) (k := fun x => queryPrefix (k x) j) _ d st)
        rw [measured_measure sign G (k := k), measured_measure sign R (k := k)]
        simp only [runPrefix, hm, PMF.bind_map, Function.comp_def, isXofQuery, Bool.toNat_false,
          Nat.add_zero]
        exact gap_bind_le _ _ _ (fun y j => changedAt sign G R (k [y]) (next y) st j) n
          fun y => ih [y] (next y) st
      | query =>
        let next (T : σ → Xofs) :=
          d.instruction ((T st).queryTable C.addressBits C.responseBytes) .query
        let h :=
          ((detector C (G st) (R st) true).measureDensity d.density d.isDensityMatrix true).toReal
        have hz : changedAt sign G R (OracleComp.query (.inr (.inl .query)) >>= k) d st 0 =
            (detector C (G st) (R st) true).measureDensity d.density d.isDensityMatrix := by
          change measured sign R
            (queryPrefix (C := C) (.liftBind (.inr (.inl .query)) k) 0) _ _ _ = _
          rw [queryPrefix]
          simp [isXofQuery, measured, interp_norm, pmf_norm]
        have hs (j : ℕ) :
            changedAt sign G R (OracleComp.query (.inr (.inl .query)) >>= k) d st (j + 1) =
              changedAt sign G R (k []) (next R) st j := by
          change measured sign R
            (queryPrefix (C := C) (.liftBind (.inr (.inl .query)) k) (j + 1)) _ _ _ = _
          rw [queryPrefix]
          simp only [isXofQuery, Nat.succ_ne_zero, beq_iff_eq, Bool.true_and, Bool.toNat_true,
            ↓reduceIte, Nat.add_sub_cancel]
          change measured sign R (OracleComp.query _ >>= _) _ _ _ = _
          simp only [measured_query (C := C) sign
            (k := fun x => queryPrefix (C := C) (k x) j)]
          rfl
        obtain ⟨M, eq⟩ := measured_readout sign G finiteSign (k []) test st
        have one : gap (measured sign G (k []) test (next G) st)
            (measured sign G (k []) test (next R) st) ≤ 4 * h := by
          simpa only [eq, h, next] using single_gap C (G st) (R st) d M
        have rest := ih [] (next R) st
        simp only [measured_query (C := C) sign (k := k), isXofQuery, Bool.toNat_true,
          Finset.sum_range_succ', hs, hz]
        rw [add_comm (∑ _ ∈ _, _)]
        exact gap_step n (Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg) one rest
    · have runPrefix (j : ℕ) := (changedAt_skip sign G R (.inr (.inr ask)) k rfl d st j).trans
          (measured_sign sign R (ask := ask) (k := fun x => queryPrefix (k x) j) _ d st)
      rw [measured_sign sign G (k := k), measured_sign sign R (k := k)]
      simp only [runPrefix, isXofQuery, Bool.toNat_false, Nat.add_zero]
      exact finite_gap _ (finiteSign ask st) _ _
        (fun z j => changedAt sign G R (k z.1) d z.2 j) n fun z => ih z.1 d z.2

end StatefulSigning

private noncomputable def tapeReply {V : Type} [Zero V]
    (sign : V → SigningQuery → Option (List Byte)) (q : SigningQuery)
    (st : List Forgery × List V) : PMF (Option (List Byte) × List Forgery × List V) :=
  let sig := sign (st.2.headD 0) q
  PMF.pure (sig, q.logReply sig st.1, st.2.tail)

-- Regroup the device, signing log and hedge tape in the original interpreter.
private theorem scored_eq_measured {C : QuantumSigningForger} {α V : Type} [Zero V]
    (p : Program C α) (T : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    scored p T sign test d log tape =
      measured (tapeReply sign) (fun _ => T) p (fun x st => test x st.1 st.2) d (log, tape) := by
  let reassoc := fun z : (Device C × List Forgery) × List V => (z.1.1, z.1.2, z.2)
  let f := OracleComp.withSampleListWhen isSigningCall (0 : V)
    (fun row => C.signingCommand T (sign row))
  let g := OracleComp.sumHandler (m := StateT (Device C × List Forgery × List V) PMF)
    (fun n => StateT.lift (ProbComp.unifOracle n))
    (C.statefulSigningCommands (fun _ => T) (tapeReply sign))
  have step (q : Request C) (z : (Device C × List Forgery) × List V) :
      (f q z).map (fun (x, next) => (x, reassoc next)) = g q (reassoc z) := by
    rcases q with coin | cmd | ask
    · simp [f, g, reassoc, isSigningCall, OracleComp.withSampleListWhen, signingCommand,
        OracleComp.sumHandler, StateT.lift, pmf_norm]
    · simp [f, g, reassoc, isSigningCall, OracleComp.withSampleListWhen, signingCommand,
        statefulSigningCommands, OracleComp.sumHandler, deviceCommand, pmf_norm, Function.comp_def]
    · simp [f, g, reassoc, isSigningCall, OracleComp.withSampleListWhen, OracleComp.withSampleList,
        signingCommand, statefulSigningCommands, OracleComp.sumHandler, tapeReply, pmf_norm]
  have law := OracleComp.run_interpret_map_state f g reassoc step p ((d, log), tape)
  unfold scored measured
  rw [ProbOracleComp.runWith_eq_run_interpret]
  change _ = ((OracleComp.interpret g p).run (reassoc ((d, log), tape))).bind _
  rw [← law, PMF.bind_map]
  rfl

-- Pull the terminal effect back through the actual adaptive program. Fixing the log and tape
-- leaves a single measurement that works for every density matrix on the retained register.
private theorem scored_readout {C : QuantumSigningForger} {α V : Type} [Zero V]
    (prog : Program C α) (H : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (log : List Forgery) (tape : List V) :
    ∃ M : Test C, ∀ d : Device C,
      scored prog H sign test d log tape = M.measureDensity d.density d.isDensityMatrix := by
  obtain ⟨M, hM⟩ := measured_readout (tapeReply sign) (fun _ => H)
    (fun _ _ => by simp [tapeReply]) prog (fun x st => test x st.1 st.2) (log, tape)
  exact ⟨M, fun d => (scored_eq_measured ..).trans (hM d)⟩

private theorem scored_gap_le {C : QuantumSigningForger} {α V : Type} [Zero V]
    {prog : Program C α} {m : ℕ}
    (cost : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) prog m)
    (G H : Xofs) (sign : V → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List V → Test C) (d : Device C) (log : List Forgery)
    (tape : List V) :
    gap (scored prog G sign test d log tape) (scored prog H sign test d log tape) ≤
      4 * m * ∑ j ∈ Finset.range m, (hit prog G H sign d log tape j true).toReal := by
  have hf (q : SigningQuery) (st : List Forgery × List V) :
      ((tapeReply sign) q st).support.Finite := by simp [tapeReply]
  simpa only [hit, scored_eq_measured, changedAt] using
    measured_gap (tapeReply sign) hf (fun _ => G) (fun _ => H) cost
      (fun x st => test x st.1 st.2) d (log, tape)

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
