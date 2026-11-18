/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.SigningMaskSeeds
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import CslibFrontier.Tactic.PMFSwap

/-!
# Measuring the address of a coherent ML-DSA hash query

Run the background-oracle side of the mask-seed comparison from the strong-forgery bound.
At the selected coherent call measure the XOR address. The event tests whether the two
actual query tables return different words there. The execution up to the measurement includes
the forger's adaptive classical signing requests and earlier coherent operations.

For a budget of `n` signatures the probability of this event is at most `2 * n / 2^256`.
One term covers changes to the message representative, the other the measured address.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

open Cslib.Probability Cslib.Quantum ExtendableOutput

private abbrev Program (C : QuantumSigningForger) := ProbOracleComp (OracleSpec.sum
  (fun _ : DeviceRequest (Width C) Empty => List Bool)
  (fun _ : SigningQuery => Option (List Byte)))

private def isXofQuery {C : QuantumSigningForger} : Request C → Bool
  | .inr (.inl .query) => true
  | _ => false

/-- Stop just before the zero-based selected query. Early return reports that it was never made. -/
private def queryPrefix {C : QuantumSigningForger} {α : Type} :
    Program C α → ℕ → Program C Bool
  | .pure _, _ => .pure false
  | .liftBind q k, j =>
    if isXofQuery (C := C) q && j == 0 then .pure true
    else .liftBind q fun a => queryPrefix (C := C) (k a) (j - (isXofQuery (C := C) q).toNat)

private theorem queryPrefix_bounded {C : QuantumSigningForger} {α : Type} {p : Program C α}
    {n : ℕ} (h : OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) p n) (j : ℕ) :
    OracleComp.IsCostBounded (fun q => (isSigningCall q).toNat) (queryPrefix (C := C) p j) n := by
  induction h generalizing j with
  | pure a n => exact .pure false n
  | liftBind q k n _ ih =>
    change OracleComp.IsCostBounded _ (queryPrefix (C := C) (.liftBind q k) j) _
    rw [queryPrefix]
    split
    · exact .pure true _
    · exact .liftBind q _ n fun a => ih a _

private abbrev Address (C : QuantumSigningForger) := BitString (C.addressBits + 2)

/-- Measure the argument register of the very placement used by `OracleGateCode.query`. -/
private noncomputable def addressRead (C : QuantumSigningForger) (result : Bool × State C) :
    PMF (Option (Address C)) :=
  if result.1 then
    let A := Fin.castLEEmb (Nat.le_add_right (C.addressBits + 2 + 8 * C.responseBytes) C.workQubits)
    let dev := result.2.1
    (POVM.basis.measureDensity dev.density dev.isDensityMatrix).map fun z =>
      some ((queryRegisters (a := C.addressBits + 2) (b := 8 * C.responseBytes) A z.1).1)
  else PMF.pure none

private noncomputable def addressLaw (C : QuantumSigningForger) (matrixXof : Xofs) (s : Level)
    (keys : Option KeyPair) {V : Type} (fallback : V) (tape : List V)
    (command : KeyPair → V → (q : Request C) → StateT (State C) PMF
      (probOracleSpec (OracleSpec.sum (fun _ : DeviceRequest (Width C) Empty => List Bool)
        (fun _ : SigningQuery => Option (List Byte))) q)) (j : ℕ) : PMF (Option (Address C)) :=
  withTrialSetup matrixXof s keys none fun keys _ =>
    let p := queryPrefix (C := C) (C.program keys.publicKey) j
    let outcomes := (OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall fallback
      (command keys)) p).run (C.initial, tape)
    (outcomes.map (fun (found, st, _) => (found, st))).bind (addressRead C)

private noncomputable def actualAddress (C : QuantumSigningForger) (s : Level)
    (seed : FixedBytes 32) {n : ℕ} (t : Fin n ↪ FixedBytes 32) (p : SigningMaskSeedOracles) :=
  C.addressLaw p.shared s (p.background.keyGen s seed) (fun _ => 0) (List.ofFn t)
    (fun k => C.hedgeCommand p.background p.shared s k.secretKey)

private noncomputable def rowAddress (C : QuantumSigningForger) (s : Level)
    (seed : FixedBytes 32) {n : ℕ} (rows : SigningMaskSeeds n) (H : Xofs) :=
  C.addressLaw H s (H.keyGen s seed) (fun _ _ => 0) (List.ofFn fun i μ => rows (i, μ))
    (C.rowCommand H s)

private theorem actualAddress_eq {C : QuantumSigningForger} {base : Xofs} {s : Level}
    {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a}
    {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (good : ¬representativeBad s seed p) (hn : C.SigningCallsLe n) (j : ℕ) :
    C.actualAddress s seed t p j = C.rowAddress s seed rows p.background j := by
  simp only [actualAddress, rowAddress, addressLaw, withTrialSetup,
    Xofs.expandA_congr (agree_off_sampleSigningMaskSeeds hp).1]
  cases hg : p.background.keyGen s seed with
  | none => rfl
  | some keys =>
    dsimp only
    cases p.background.expandA s (keys.publicKey.take 32) with
    | none => rfl
    | some A =>
      apply congrArg (fun law => PMF.bind law (addressRead C))
      apply run_eq_rows C hp hg _ (queryPrefix_bounded (C := C) (hn keys.publicKey) j)
      intro m
      by_contra ne
      exact good ⟨keys, hg, m, ne⟩

private def differs (C : QuantumSigningForger) (p : SigningMaskSeedOracles) :
    Option (Address C) → Bool
  | none => false
  | some addr => decide (p.shared.queryTable C.addressBits C.responseBytes addr ≠
      p.background.queryTable C.addressBits C.responseBytes addr)

/-- The hedge field of a raw mask-seed input, with an arbitrary default off that domain. -/
private noncomputable def targetHedge {C : QuantumSigningForger} (key : List Byte)
    (addr : Option (Address C)) : FixedBytes 32 := by
  classical
  let word := addr.bind fun x =>
    Xofs.unpad (List.ofFn (fun i : Fin (C.addressBits + 1) => x i.succ))
  exact if h : ∃ (r : FixedBytes 32) (μ : BitString 512),
    word = some (maskSeedInput key r (List.ofFn μ)) then h.choose else fun _ => 0

private theorem target_mem_of_differs {C : QuantumSigningForger} {base : Xofs} {s : Level}
    {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a}
    {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support) {addr : Option (Address C)}
    (hd : differs C p addr = true) :
    targetHedge (C := C) ((p.background.expandKeySeed s seed).drop 96) addr ∈ Set.range t := by
  classical
  obtain ⟨same128, off⟩ := agree_off_sampleSigningMaskSeeds hp
  cases addr with
  | none => contradiction
  | some addr =>
    replace hd := of_decide_eq_true hd
    simp only [Xofs.queryTable] at hd
    cases hx : Xofs.unpad (List.ofFn (fun i : Fin (C.addressBits + 1) => addr i.succ)) with
    | none => exact (hd (by rw [hx])).elim
    | some x =>
      rw [hx] at hd
      cases strength : addr 0 with
      | false => exact (hd (by simp [strength, same128])).elim
      | true =>
        let key := (p.background.expandKeySeed s seed).drop 96
        have hit : ∃ (i : Fin n) (μ : BitString 512),
            maskSeedInput key (t i) (List.ofFn μ) = x := by
          by_contra! miss
          have same := read_eq_of_byteAt_eq (n := C.responseBytes) (fun k _ => off x k (.inr miss))
          exact hd (by simp only [strength, ↓reduceIte, same])
        obtain ⟨i, μ, eq⟩ := hit
        refine ⟨i, ?_⟩
        unfold targetHedge
        simp only [Option.bind_some, hx, Option.some.injEq]
        split
        next h =>
          obtain ⟨ν, hv⟩ := h.choose_spec
          exact hedge_eq_of_maskSeedInput_eq (eq.trans hv)
        next h => exact (h ⟨t i, μ, eq.symm⟩).elim


private noncomputable def fixedQueryGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (seed : FixedBytes 32) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b)
    [Nonempty (Fin n ↪ FixedBytes 32)] (rows : SigningMaskSeeds n) (j : ℕ) : Game := do
  let t ← PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)
  let p ← base.sampleSigningMaskSeeds s seed t ha hb rows
  (C.actualAddress s seed t p j).map (differs C p)

/-- Measure the address just before coherent query number `j` (zero based) in the
background-device experiment. Signing uses the shared programmed XOFs. Return true if the
two XOR tables differ at the measured address. Early termination and failed setup lose. -/
noncomputable def maskSeedQueryHit (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (hsize : n ≤ 2 ^ 256) (j : ℕ) : Game :=
  withMaskSeedOracles s base ha hb hsize fun t seed p =>
    (C.actualAddress s seed t p j).map (differs C p)

private theorem fixedQueryGame_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (seed : FixedBytes 32) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b)
    (hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 256) [Nonempty (Fin n ↪ FixedBytes 32)]
    (rows : SigningMaskSeeds n) (j : ℕ) :
    C.fixedQueryGame s base seed ha hb rows j true ≤ ENNReal.ofReal (2 * n / 2 ^ 256) := by
  classical
  let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)
  let draw := fun t => base.sampleSigningMaskSeeds s seed t ha hb rows
  let bad (p : SigningMaskSeedOracles) := PMF.pure (decide (representativeBad s seed p))
  let report (H : Xofs) (t : Fin n ↪ FixedBytes 32) :=
    (C.rowAddress s seed rows H j).bind fun addr => PMF.pure
      (decide (targetHedge (C := C) ((H.expandKeySeed s seed).drop 96) addr ∈ Set.range t))
  let success (t : Fin n ↪ FixedBytes 32) (p : SigningMaskSeedOracles) :=
    (C.actualAddress s seed t p j).map (differs C p)
  have compare t p (hp : p ∈ (draw t).support) :
      success t p true ≤ bad p true + report p.background t true := by
    by_cases h : representativeBad s seed p
    · exact (PMF.coe_le_one _ _).trans (by simp [bad, h])
    · simp only [success, bad, h, decide_false, show PMF.pure false true = 0 from by simp,
        zero_add, actualAddress_eq hp h hn j]
      apply PMF.map_true_mono
      exact fun addr _ diff => decide_eq_true (target_mem_of_differs hp diff)
  have cost (t) : (draw t).bind (fun p => report p.background t) =
      (base.uniformPrefixes a b).bind (fun H => report H t) := by
    rw [← base.background_sampleSigningMaskSeeds s seed t ha hb rows, PMF.bind_map]
    rfl
  have split : C.fixedQueryGame s base seed ha hb rows j true ≤
      ((tapes.bind draw).bind bad) true +
        (tapes.bind fun t => (base.uniformPrefixes a b).bind fun H => report H t) true := by
    simp only [fixedQueryGame, PMF.monad_bind_eq_bind, PMF.bind_bind, ← cost]
    apply PMF.bind_apply_le_add_on_support tapes
    exact fun t _ => PMF.bind_apply_le_add_on_support (draw t) true (compare t)
  have badBound : ((tapes.bind draw).bind bad) true ≤ ENNReal.ofReal (n / 2 ^ 256) := by
    change ((tapes.bind draw).bind (fun p => PMF.pure (decide (representativeBad s seed p)))) _ ≤ _
    rw [PMF.bind_pure_decide_apply_true, ENNReal.le_ofReal_iff_toReal_le
      (PMF.toOuterMeasure_ne_top _ _) (by positivity)]
    exact base.prob_representative_ne_sampleSigningMaskSeeds s seed ha hb hsize rows
  have hitBound : (tapes.bind fun t => (base.uniformPrefixes a b).bind fun H => report H t) true ≤
      ENNReal.ofReal (n / 2 ^ 256) := by
    rw [PMF.bind_comm]
    apply PMF.bind_apply_le_on_support
    intro H _
    simp only [report]
    rw [PMF.bind_comm]
    apply PMF.bind_apply_le_on_support
    intro addr _
    rw [PMF.bind_pure_decide_apply_true, ENNReal.le_ofReal_iff_toReal_le
      (PMF.toOuterMeasure_ne_top _ _) (by positivity), prob_uniformOfFintype_embedding_mem_range]
    simp only [Fintype.card_fin, card_hedge, Nat.cast_pow, Nat.cast_ofNat, le_refl]
  apply split.trans ((add_le_add badBound hitBound).trans ?_)
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  ring_nf
  rfl

/-- For every adaptive forger and every fixed coherent query index, the probability of
measuring an address at which the two actual XOR tables differ is at most twice the signing
budget divided by the 256-bit hedge space. -/
theorem maskSeedQueryHit_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (j : ℕ) :
    (Game.succProbability (C.maskSeedQueryHit s base (n := n) ha hb hsize j) : ℝ) ≤
      2 * n / 2 ^ 256 := by
  let _ : Nonempty (Fin n ↪ FixedBytes 32) := hedgeEmbedding_nonempty hsize
  have law : C.maskSeedQueryHit s base ha hb hsize j =
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
        (PMF.uniformOfFintype (SigningMaskSeeds n)).bind fun rows =>
          C.fixedQueryGame s base seed ha hb rows j := by
    simp only [maskSeedQueryHit, withMaskSeedOracles, fixedQueryGame, PMF.monad_bind_eq_bind]
    pmf_swap with seed
    pmf_swap with rows
    rfl
  rw [law, Game.coe_succProbability]
  apply (ENNReal.le_ofReal_iff_toReal_le (PMF.apply_ne_top _ _) (by positivity)).mp
  apply PMF.bind_apply_le_on_support
  intro seed _
  apply PMF.bind_apply_le_on_support
  exact fun rows _ => fixedQueryGame_le C s base seed ha hb hn hsize rows j

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
