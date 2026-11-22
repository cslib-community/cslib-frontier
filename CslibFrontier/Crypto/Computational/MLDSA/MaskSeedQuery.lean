/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.PrivateMaskSeedGame
import all CslibFrontier.Crypto.Computational.MLDSA.FIPS204
import all CslibFrontier.Crypto.Computational.MLDSA.SigningMaskSeeds
import all CslibFrontier.Crypto.Computational.MLDSA.SigningHedges
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import CslibFrontier.Probability.PMF.DensityBounds
import CslibFrontier.Tactic.PMFSwap

/-!
# Measuring the address of a coherent ML-DSA hash query

Run the background-oracle side of the mask-seed comparison from the strong-forgery bound.
At the selected coherent call measure the XOR address. The event tests whether the two
actual query tables return different words there. The execution up to the measurement includes
the forger's adaptive classical signing requests and earlier coherent operations.

For a budget of `n` signatures the probability of this event is at most `2 * n / 2^256`.
The sharper bound multiplies this coefficient by the probability that a candidate from the
public-key hash or the measured SHAKE256 input predicts the 32-byte private signing seed `K`.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

open Cslib.Probability Cslib.Quantum ExtendableOutput

/-- A coherent raw XOF query, charged once against the device query budget. -/
@[expose] def isXofQuery {width : ℕ} :
    ℕ ⊕ DeviceRequest width Empty ⊕ SigningQuery → Bool
  | .inr (.inl .query) => true
  | _ => false

/-- Stop just before the zero-based selected query. Early return reports that it was never made. -/
private def queryPrefix {C : QuantumSigningForger} {α : Type} :
    Program C α → ℕ → Program C Bool
  | .pure _, _ => .pure false
  | .liftBind q k, j =>
    if isXofQuery q && j == 0 then .pure true
    else .liftBind q fun a => queryPrefix (C := C) (k a) (j - (isXofQuery q).toNat)

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
    {κ : Type} (publicKey : κ → List Byte) (keys : Option κ) {V : Type}
    (fallback : V) (tape : List V)
    (command : κ → V → (q : Request C) → StateT (State C) PMF
      (probOracleSpec (OracleSpec.sum (fun _ : DeviceRequest (Width C) Empty => List Bool)
        (fun _ : SigningQuery => Option (List Byte))) q)) (j : ℕ) : PMF (Option (Address C)) :=
  withTrialSetup matrixXof s publicKey keys none fun keys _ =>
    let p := queryPrefix (C := C) (C.program (publicKey keys)) j
    let outcomes := (OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall fallback
      (command keys)) p).run (C.initial, tape)
    (outcomes.map (fun (found, st, _) => (found, st))).bind (addressRead C)

private noncomputable def actualAddress (C : QuantumSigningForger) (s : Level)
    (seed : FixedBytes 32) {n : ℕ} (t : Fin n ↪ FixedBytes 32) (p : SigningMaskSeedOracles) :=
  C.addressLaw p.shared s KeyPair.publicKey (p.background.keyGen s seed) (fun _ => 0) (List.ofFn t)
    (fun k => C.hedgeCommand p.background p.shared s k.secretKey)

private noncomputable def rowAddress (C : QuantumSigningForger) (s : Level)
    (keys : Option KeyPair) {n : ℕ} (rows : SigningMaskSeeds n) (H : Xofs) :=
  C.addressLaw H s KeyPair.publicKey keys (fun _ _ => 0) (List.ofFn fun i μ => rows (i, μ))
    (C.rowCommand H s)

private theorem actualAddress_eq {C : QuantumSigningForger} {base : Xofs} {s : Level}
    {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a}
    {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (good : ¬representativeBad s seed p) (hn : C.SigningCallsLe n) (j : ℕ) :
    C.actualAddress s seed t p j =
      C.rowAddress s (p.background.keyGen s seed) rows p.background j := by
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

private def queryKeyPrefix {C : QuantumSigningForger} (addr : Option (Address C)) :
    Option (List Bool) := (Xofs.shake256QueryInput addr).map (·.take 256)

private theorem seed_hedge_of_differs {C : QuantumSigningForger} {base : Xofs} {s : Level}
    {seed : FixedBytes 32} {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a}
    {hb : 64 ≤ b} {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support) {addr : Option (Address C)}
    (hd : differs C p addr = true) :
    queryKeyPrefix (C := C) addr =
      some (Keccak.bytesToBitsLE ((p.background.expandKeySeed s seed).drop 96)) ∧
    targetHedge (C := C) ((p.background.expandKeySeed s seed).drop 96) addr ∈ Set.range t := by
  classical
  obtain ⟨same128, off⟩ := agree_off_sampleSigningMaskSeeds hp
  have diff : addr.any (fun v => decide (p.shared.queryTable C.addressBits C.responseBytes v ≠
      p.background.queryTable C.addressBits C.responseBytes v)) = true := by cases addr <;> exact hd
  obtain ⟨x, decoded, ne⟩ := Xofs.shake256QueryInput_of_queryTable_ne same128 diff
  let key := (p.background.expandKeySeed s seed).drop 96
  have hit : ∃ (i : Fin n) (μ : BitString 512), maskSeedInput key (t i) (List.ofFn μ) = x := by
    by_contra! miss
    exact ne (read_eq_of_byteAt_eq fun k _ => off x k (.inr miss))
  obtain ⟨i, μ, eq⟩ := hit
  have word : (addr.bind fun v => Xofs.unpad (List.ofFn fun j : Fin (C.addressBits + 1) =>
      v j.succ)) = some x := by
    cases addr with
    | none => contradiction
    | some v =>
      cases tag : v 0 <;> simp_all only [Xofs.shake256QueryInput, Option.bind_some,
        Bool.false_eq_true, ↓reduceIte, reduceCtorEq]
  refine ⟨?_, i, ?_⟩
  · have len : (Keccak.bytesToBitsLE key).length = 256 := by
      change (Keccak.bytesToBitsLE (signingSeedBytes p.background s seed)).length = 256
      rw [Keccak.length_bytesToBitsLE, signingSeedBytes_length]
    simp only [queryKeyPrefix, decoded, Option.map_some]
    rw [← eq]
    change some ((Keccak.bytesToBitsLE (key ++ (t i).toList) ++ List.ofFn μ).take 256) = _
    rw [show Keccak.bytesToBitsLE (key ++ (t i).toList) =
        Keccak.bytesToBitsLE key ++ Keccak.bytesToBitsLE (t i).toList from List.flatMap_append,
      List.append_assoc]
    apply congrArg some
    simpa only [len] using (List.take_left (l₁ := Keccak.bytesToBitsLE key)
      (l₂ := Keccak.bytesToBitsLE (t i).toList ++ List.ofFn μ))
  · unfold targetHedge
    simp only [word, Option.some.injEq]
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


private def publicHash (H : Xofs) (pk : Option (List Byte)) : Option (List Byte) :=
  pk.map fun bytes => H.h256.readBytes bytes 64

private def signingSeedCandidates {C : QuantumSigningForger} (hash : Option (List Byte))
    (addr : Option (Address C)) : List (List Bool) :=
  (hash.map (fun tr => Keccak.bytesToBitsLE (tr.take 32))).toList ++
    (queryKeyPrefix (C := C) addr).toList

private noncomputable def fixedPrediction (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (seed : FixedBytes 32) (a b : ℕ) {n : ℕ} (rows : SigningMaskSeeds n) (j : ℕ) : Game :=
  (base.uniformPrefixes a b).bind fun H =>
    let keys := H.keyGen s seed
    let hash := publicHash H (keys.map KeyPair.publicKey)
    (C.rowAddress s keys rows H j).map fun addr =>
      (signingSeedCandidates (C := C) hash addr).contains
        (Keccak.bytesToBitsLE (signingSeedBytes H s seed))

/-- Predict the 32-byte private signing seed `K` in the encoded FIPS 204 private key.
The candidates are the first 32 bytes of the public-key hash and the first 256 input bits
at the selected SHAKE256 query, using independent mask-seed rows. The experiment makes one extra
64-byte SHAKE256 read at the published key on successful key generation, independently of the
forger's register widths. Missing candidates cannot win. -/
noncomputable def signingSeedPredictionGame (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (a b n j : ℕ) : Game := do
  let seed ← PMF.uniformOfFintype (FixedBytes 32)
  let rows ← PMF.uniformOfFintype (SigningMaskSeeds n)
  C.fixedPrediction s base seed a b rows j

private theorem representative_collision {base : Xofs} {s : Level} {seed : FixedBytes 32}
    {a b n : ℕ} {t : Fin n ↪ FixedBytes 32} {ha : 1024 ≤ a} {hb : 64 ≤ b}
    {rows : SigningMaskSeeds n} {p : SigningMaskSeedOracles}
    (hp : p ∈ (base.sampleSigningMaskSeeds s seed t ha hb rows).support)
    (bad : representativeBad s seed p) :
    ∃ i, publicHash p.background ((p.background.keyGen s seed).map KeyPair.publicKey) =
      some (signingSeedBytes p.background s seed ++ (t i).toList) := by
  obtain ⟨keys, hg, m, ne⟩ := bad
  rw [Xofs.messageRepresentative, publicKeyHash_eq_of_mem_sampleSigningMaskSeeds hp hg] at ne
  obtain ⟨i, h⟩ := seed_hedge_of_representative_ne hp _ (p.background.h256.length_read ..) _ ne
  exact ⟨i, by simpa only [publicHash, hg, Option.map_some, Option.some.injEq,
    signingSeedBytes, ExtendableOutput.readBytes] using h⟩

private theorem fixedQueryGame_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    (seed : FixedBytes 32) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b)
    (hn : C.SigningCallsLe n) [Nonempty (Fin n ↪ FixedBytes 32)]
    (rows : SigningMaskSeeds n) (j : ℕ) :
    C.fixedQueryGame s base seed ha hb rows j true ≤ ENNReal.ofReal (2 * n / 2 ^ 256) *
      C.fixedPrediction s base seed a b rows j true := by
  classical
  let tapes := PMF.uniformOfFintype (Fin n ↪ FixedBytes 32)
  let draw := fun t => base.sampleSigningMaskSeeds s seed t ha hb rows
  let key (H : Xofs) := signingSeedBytes H s seed
  let hash (H : Xofs) := publicHash H ((H.keyGen s seed).map KeyPair.publicKey)
  let covers (H : Xofs) (t : Fin n ↪ FixedBytes 32) :=
    ∃ i, hash H = some (key H ++ (t i).toList)
  let atQuery (H : Xofs) (addr : Option (Address C)) (t : Fin n ↪ FixedBytes 32) :=
    queryKeyPrefix (C := C) addr = some (Keccak.bytesToBitsLE (key H)) ∧
      targetHedge (C := C) (key H) addr ∈ Set.range t
  let report H t := (C.rowAddress s (H.keyGen s seed) rows H j).map fun addr =>
    decide (covers H t ∨ atQuery H addr t)
  have compare t p (hp : p ∈ (draw t).support) :
      ((C.actualAddress s seed t p j).map (differs C p)) true ≤ report p.background t true := by
    by_cases bad : representativeBad s seed p
    · have h : covers p.background t := representative_collision hp bad
      exact (PMF.coe_le_one _ _).trans (by
        simp only [report, h, true_or, decide_true]
        change 1 ≤ ((C.rowAddress s (p.background.keyGen s seed) rows p.background j).bind
          fun _ => PMF.pure true) true
        rw [PMF.bind_const, PMF.pure_apply_self])
    · rw [actualAddress_eq hp bad hn j]
      apply PMF.map_true_mono
      exact fun addr _ diff => decide_eq_true (Or.inr (seed_hedge_of_differs hp diff))
  have ref : C.fixedQueryGame s base seed ha hb rows j true ≤
      (tapes.bind fun t => (base.uniformPrefixes a b).bind fun H => report H t) true := by
    apply PMF.bind_apply_mono_on_support tapes
    intro t _
    rw [← base.background_sampleSigningMaskSeeds s seed t ha hb rows, PMF.bind_map]
    exact PMF.bind_apply_mono_on_support (draw t) true (compare t)
  apply ref.trans
  rw [PMF.bind_comm]
  apply PMF.bind_apply_le_mul_bind_apply
  intro H
  change (tapes.bind fun t => (C.rowAddress s (H.keyGen s seed) rows H j).bind fun addr =>
    PMF.pure (decide (covers H t ∨ atQuery H addr t))) true ≤ _
  rw [PMF.bind_comm]
  apply PMF.bind_apply_le_mul_bind_apply
  intro addr
  let R := ENNReal.ofReal ((n : ℝ) / 2 ^ 256)
  have single (v : FixedBytes 32) :
      (tapes.map (fun t : Fin n ↪ FixedBytes 32 => decide (v ∈ Set.range t))) true ≤ R := by
    change (tapes.bind (fun t => PMF.pure (decide (v ∈ Set.range t)))) true ≤ _
    rw [PMF.bind_pure_decide_apply_true, ENNReal.le_ofReal_iff_toReal_le
      (PMF.toOuterMeasure_ne_top _ _) (by positivity), prob_uniformOfFintype_embedding_mem_range]
    simp only [Fintype.card_fin, FixedBytes.card, Nat.cast_pow, Nat.cast_ofNat, le_refl]
  simp only [Function.comp_apply]
  by_cases guess : (signingSeedCandidates (C := C) (hash H) addr).contains
      (Keccak.bytesToBitsLE (key H))
  · rw [guess, PMF.pure_apply_self, mul_one]
    have publicBound : (tapes.map (fun t => decide (covers H t))) true ≤ R := by
      by_cases existsTarget : ∃ r : FixedBytes 32, hash H = some (key H ++ r.toList)
      · obtain ⟨r, eq⟩ := existsTarget
        apply le_trans _ (single r)
        apply PMF.map_true_mono
        intro t _ h
        obtain ⟨i, hi⟩ := of_decide_eq_true h
        exact decide_eq_true ⟨i, List.ofFn_inj.mp
          (List.append_cancel_left (Option.some.inj (hi.symm.trans eq)))⟩
      · have no (t) : ¬ covers H t := fun ⟨i, h⟩ => existsTarget ⟨t i, h⟩
        simp only [no, decide_false]
        change ((tapes.bind fun _ => PMF.pure false) true) ≤ R
        rw [PMF.bind_const]
        simp
    have queryBound : (tapes.map (fun t => decide (atQuery H addr t))) true ≤ R := by
      apply le_trans _ (single (targetHedge (C := C) (key H) addr))
      apply PMF.map_true_mono
      exact fun t _ h => decide_eq_true (of_decide_eq_true h).2
    apply (PMF.map_true_le_add tapes (E := fun t => decide (covers H t ∨ atQuery H addr t))
      (A := fun t => decide (covers H t))
      (B := fun t => decide (atQuery H addr t)) fun t _ h =>
        (of_decide_eq_true h).imp decide_eq_true decide_eq_true).trans
    apply (add_le_add publicBound queryBound).trans
    rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  · have no t : ¬ (covers H t ∨ atQuery H addr t) := by
      intro hit
      apply guess
      rw [List.contains_iff_mem, signingSeedCandidates, List.mem_append]
      rcases hit with ⟨i, eq⟩ | ⟨eq, _⟩
      · left
        rw [eq]
        simp only [Option.map_some, Option.toList_some, List.mem_singleton]
        apply congrArg Keccak.bytesToBitsLE
        simpa only [key, signingSeedBytes_length] using
          (List.take_left (l₁ := signingSeedBytes H s seed) (l₂ := (t i).toList)).symm
      · right
        simp [eq]
    simp only [no, decide_false, PMF.bind_const]
    simp

/-- Detecting a changed row requires the hedge tape to cover a candidate and the private
signing seed `K` to match one of two predicted prefixes in the independent background execution. -/
theorem maskSeedQueryHit_le_signingSeedPrediction (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (j : ℕ) :
    (Game.succProbability (C.maskSeedQueryHit s base ha hb hsize j) : ℝ) ≤
      (2 * n / 2 ^ 256) * Game.succProbability (C.signingSeedPredictionGame s base a b n j) := by
  let _ : Nonempty (Fin n ↪ FixedBytes 32) := hedgeEmbedding_nonempty hsize
  have law : C.maskSeedQueryHit s base ha hb hsize j =
      (PMF.uniformOfFintype (FixedBytes 32)).bind fun seed =>
        (PMF.uniformOfFintype (SigningMaskSeeds n)).bind fun rows =>
          C.fixedQueryGame s base seed ha hb rows j := by
    simp only [maskSeedQueryHit, withMaskSeedOracles, fixedQueryGame, PMF.monad_bind_eq_bind]
    pmf_swap with seed
    pmf_swap with rows
    rfl
  have h : C.maskSeedQueryHit s base ha hb hsize j true ≤
      ENNReal.ofReal (2 * n / 2 ^ 256) * C.signingSeedPredictionGame s base a b n j true := by
    rw [law]
    apply PMF.bind_apply_le_mul_bind_apply
    intro seed
    exact PMF.bind_apply_le_mul_bind_apply _ fun rows =>
      fixedQueryGame_le C s base seed ha hb hn rows j
  have real := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (PMF.apply_ne_top _ _)) h
  simpa only [Game.coe_succProbability, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 2 * n / 2 ^ 256)]
    using real

/-- For every adaptive forger and every fixed coherent query index, the probability of
measuring an address at which the two actual XOR tables differ is at most twice the signing
budget divided by the 256-bit hedge space. -/
theorem maskSeedQueryHit_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n : ℕ} (ha : 1024 ≤ a) (hb : 64 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (j : ℕ) :
    (Game.succProbability (C.maskSeedQueryHit s base (n := n) ha hb hsize j) : ℝ) ≤
      2 * n / 2 ^ 256 := by
  apply (C.maskSeedQueryHit_le_signingSeedPrediction s base ha hb hn hsize j).trans
  apply mul_le_of_le_one_right (by positivity)
  exact_mod_cast Game.succProbability_le_one _


end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
