/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.SecretRowServices
public import CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.SecretRowServices
import all CslibFrontier.Crypto.Computational.MLDSA.SecretRowPrediction
import all CslibFrontier.Crypto.Computational.MLDSA.SharedSecretExpansion
import all CslibFrontier.Crypto.Computational.MLDSA.PublicPairSigning
import all CslibFrontier.Crypto.Computational.MLDSA.SigningSimulation
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
import all CslibFrontier.Crypto.Computational.MLDSA.QuantumSigning
import all CslibFrontier.Crypto.Computational.MLDSA.MaskSeedQuery

/-!
# The key-distribution switch for the adaptive ML-DSA public-pair signer

After signing simulation the native seeded key and the forger still share SHAKE. Compare its
coherent query device and the independent-expansion device to the same refreshed device.
Signing uses the same classical service in all three games. Every terminal signing write updates
the table for the next coherent query, and intermediate measurements retain the conditional state.

The adaptive query comparison in `SigningQueryComparison` bounds the squared change in
square-root success by four times the query budget times the sum of the measured hit probabilities.
Here the finite-support signing service samples both a response and terminal writes.
The private-input estimates give an increment of `4m / 2^128` on the square root, plus a
single `2^-512` probability for the public-key hash exception.

The resulting probability comparison is an original step toward strong unforgeability of
[FIPS 204][NISTFIPS204]. The distinguishing term is evaluated on the constructed test. Certifying
its resource overhead and producing the standard sparse-oracle solver are separate obligations.
-/

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
open Cslib.Probability Cslib.Quantum

private theorem finite_bind {α β : Type} {p : PMF α} (hp : p.support.Finite)
    {k : α → PMF β} (hk : ∀ a ∈ p.support, (k a).support.Finite) :
    (p.bind k).support.Finite := by
  rw [PMF.support_bind]
  exact hp.biUnion hk

private theorem finite_draw (s : Level) (pair : MLDSA.PublicKey s.params) (H : Xofs) :
    (publicDraw s pair H).support.Finite := by
  classical
  have : NeZero s.params.q := ⟨by cases s <;> decide⟩
  unfold publicDraw draw
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  apply finite_bind (Set.toFinite _)
  intro d _
  split
  · apply finite_bind (Set.toFinite _)
    intro _ _
    simp
  · apply finite_bind
    · unfold simulateFreshSigningAttempt
      rw [PMF.support_map]
      exact (Set.toFinite _).image _
    · intro _ _
      simp

private theorem finite_retries {α ι : Type} (p : PMF (Option α)) (hp : p.support.Finite)
    (l : List ι) : (l.findSomeM? fun _ => p).support.Finite := by
  induction l with
  | nil => simp [List.findSomeM?_nil, PMF.monad_pure_eq_pure]
  | cons _ l ih =>
    rw [List.findSomeM?_cons, PMF.monad_bind_eq_bind]
    apply finite_bind hp
    rintro (_ | x) _
    · exact ih
    · simp [PMF.monad_pure_eq_pure]

private theorem finite_signingCall (s : Level) (pair : MLDSA.PublicKey s.params) {H : Xofs}
    (tr : List Byte) (q : SigningQuery) (st : History s H tr) :
    (signingCall s tr (publicDraw s pair) q st).support.Finite := by
  classical
  unfold signingCall
  split
  · simp [PMF.monad_pure_eq_pure]
  · simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    apply finite_bind (finite_retries _ (finite_draw ..) _)
    rintro (_ | w) _
    all_goals simp

private theorem publicPair_gap (C : QuantumSigningForger) (s : Level) (G H : Xofs)
    (rho : FixedBytes 32) (pair : MLDSA.PublicKey s.params) {m : ℕ} (cost : C.XofCallsLe m) :
    gap (C.publicPairWinWithDevice s G H rho pair) (C.publicPairWinWithDevice s H H rho pair) ≤
      4 * m * ∑ j ∈ Finset.range m,
        (C.publicPairResponseChange s j G H rho pair true).toReal := by
  let pk := encodePublic s rho.toList pair.t
  let tr := H.h256.readBytes pk 64
  let start : History s H tr := ⟨H, [], [], .initial, by simp, by simp⟩
  let raw (D : Xofs) (t : History s H tr) := TerminalSigningWrite.replay D t.writes
  let sign := signingCall s (base := H) tr (publicDraw s pair)
  have honest : raw H = (·.xofs) := funext fun t => t.trace.replay_eq
  let test (f : Forgery) (t : History s H tr) : Test C := POVM.const
    (SignedMatrixTrial.newDigestWin ⟨t.xofs, pair.A, pk, f, t.log⟩)
  have win (D : Xofs) : C.publicPairWinWithDevice s D H rho pair =
      measured sign (raw D) (C.program pk) test C.initial.1 start := by
    simp only [publicPairWinWithDevice, scoreProgram, measured, test, POVM.measureDensity_const,
      PMF.map, Function.comp_def]
    rfl
  have hit (j : ℕ) : C.publicPairResponseChange s j G H rho pair =
      changedAt sign (raw G) (raw H) (C.program pk) C.initial.1 start j := by
    simp only [publicPairResponseChange, queryWrites, changedAt, measured, runSigningProgram,
      PMF.map_bind, PMF.map_comp, Function.comp_def, honest]
    apply congrArg (PMF.bind _ ·)
    funext ⟨found, dev, t⟩
    have eq : (fun a => C.queryChanged G H (t.writes, a)) =
        fun a => a.any (changed C (raw G t) t.xofs) := by
      funext a
      cases a with
      | none => rfl
      | some a => simp only [queryChanged, Option.any_some, changed, raw, t.trace.replay_eq]
    rw [eq]
    exact addressTest_law C _ found (dev, t.log)
  simp only [win, hit]
  exact measured_gap sign (finite_signingCall s pair tr) (raw G) (raw H) (cost pk) test
    C.initial.1 start

private theorem secretRow_sq_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b m : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) (cost : C.XofCallsLe m) (share : Bool) :
    let ref := (base.sampleSecretExpansionViews s ha hb).bind fun v =>
      if v.publicHashMatch then PMF.pure false else v.refreshKeySeed.bind fun H =>
        (v.pair.map (C.publicPairWinWithDevice s H H v.publicSeed)).getD (PMF.pure false)
    gap (C.secretRowDeviceGame s base ha hb share) ref ≤ (2 * (m : ℝ) / 2^128)^2 := by
  classical
  intro ref
  let V := base.sampleSecretExpansionViews s ha hb
  let hits (v : SecretExpansionViews s) (H : Xofs) (j : ℕ) : Game := match v.pair with
    | none => PMF.pure false
    | some pk => C.publicPairResponseChange s j (if share then v.shared else v.background)
        H v.publicSeed pk
  have fin : V.support.Finite := by
    dsimp only [V, Xofs.sampleSecretExpansionViews]
    apply finite_bind (Set.toFinite _)
    intro _ _
    apply finite_bind (Set.toFinite _)
    intro _ _
    apply finite_bind (Set.toFinite _)
    intro _ _
    rw [PMF.support_map]
    exact (Set.toFinite _).image _
  have bound : gap (C.secretRowDeviceGame s base ha hb share) ref ≤ 4 * m *
      ∑ j ∈ Finset.range m,
        ((V.bind fun v => v.refreshKeySeed.bind fun H => hits v H j) true).toReal := by
    apply finite_gap V fin
    intro v
    by_cases h : v.publicHashMatch = true
    · simp only [h, ↓reduceIte, gap, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow]
      positivity
    simp only [h, Bool.false_eq_true, ↓reduceIte]
    have hv : v.refreshKeySeed.support.Finite := by
      rw [SecretExpansionViews.refreshKeySeed, PMF.support_map]
      exact (Set.toFinite _).image _
    apply finite_gap _ hv
    intro H
    cases hp : v.pair with
    | none => simp [hits, hp, gap]
    | some pk =>
      simpa only [hits, hp, Option.map_some, Option.getD_some] using
        publicPair_gap C s (if share then v.shared else v.background) H v.publicSeed pk cost
  apply bound.trans
  calc
    _ ≤ 4 * (m : ℝ) * ∑ _j ∈ Finset.range m, ((2 : ℝ) ^ 256)⁻¹ := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro j _
      have p := C.secretRow_changedResponse_le s base ha hb share j
      change ((V.bind fun v => v.refreshKeySeed.bind fun H => hits v H j) true) ≤ _ at p
      exact (ENNReal.toReal_mono (by norm_num : (2 ^ 256 : ENNReal)⁻¹ ≠ ⊤) p).trans_eq (by
        rw [ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat])
    _ = _ := by
      simp
      ring

private theorem nativeFullPair_le_independentExpandS (C : QuantumSigningForger) (s : Level)
    (base : Xofs)
    {a b m : ℕ} (ha : 528 ≤ a) (hb : 481 ≤ b) (cost : C.XofCallsLe m) :
    let native := (base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s
      (fun rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin))
    (native true).toReal ≤ (√((C.independentExpandSGame s base a b true).toReal) +
      4 * (m : ℝ) / 2^128)^2 + ((2 : ℝ)^512)⁻¹ := by
  intro native
  obtain ⟨left, right⟩ := C.secretRowDeviceGame_bounds s base ha hb
  have h₁ := C.secretRow_sq_le s base ha hb cost true
  have h₂ := C.secretRow_sq_le s base ha hb cost false
  dsimp only [gap] at h₁ h₂
  have u := le_of_sq_le_sq h₁ (by positivity)
  rw [sub_sq_comm] at h₂
  have v := le_of_sq_le_sq h₂ (by positivity)
  have inc := Real.sqrt_le_sqrt (ENNReal.toReal_mono
    ((C.independentExpandSGame s base a b).apply_ne_top true) right)
  have roots : √((C.secretRowDeviceGame s base ha hb true true).toReal) ≤
      √((C.independentExpandSGame s base a b true).toReal) + 4 * (m : ℝ) / 2^128 := by
    linarith only [u, v, inc]
  have sq := pow_le_pow_left₀ (Real.sqrt_nonneg _) roots 2
  rw [Real.sq_sqrt ENNReal.toReal_nonneg] at sq
  have e := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨(C.secretRowDeviceGame s base ha hb true).apply_ne_top true,
      by norm_num⟩) left
  rw [ENNReal.toReal_add ((C.secretRowDeviceGame s base ha hb true).apply_ne_top true)
    (by norm_num),
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at e
  exact e.trans (add_le_add_left sq _)

/-- Transfer fresh-digest success of the native-key public-pair signer to a uniform MLWE pair
plus the real-versus-uniform advantage of its explicit test. Each coherent query contributes
to the square-root loss. Both branches use the same public-pair test and retain setup failure. -/
public theorem nativeFullPair_le_uniformPair (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b m : ℕ} (ha : 528 ≤ a) (hb : 894 ≤ b) (cost : C.XofCallsLe m) :
    let native := (base.uniformPrefixes a b).bind fun H => H.fullPairExperiment s
      (fun rho pk => (C.publicPairSigning s H rho pk).map (·.trial.newDigestWin))
    let test := C.fullPairMLWETest s base a b
    let real := (MLDSA.keyLaw s.params (MatrixOracle.shortCoefficientLaw s)).bind test
    let uniform := (MLDSA.uniformKeyLaw s.params).bind test
    (native true).toReal ≤ (√((uniform true).toReal + (Game.advantage real uniform : ℝ)) +
      4 * (m : ℝ) / 2^128)^2 + ((2 : ℝ)^512)⁻¹ := by
  intro native test real uniform
  have bound := C.nativeFullPair_le_independentExpandS s base ha (by lia : 481 ≤ b) cost
  rw [C.independentExpandSGame_eq_mlwe s base ha hb] at bound
  apply bound.trans
  apply add_le_add_left
  apply pow_le_pow_left₀ (by positivity)
  apply add_le_add_left
  apply Real.sqrt_le_sqrt
  exact Game.coe_succProbability_le_add_of_advantage_le (g₀ := real) (g₁ := uniform) le_rfl

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
