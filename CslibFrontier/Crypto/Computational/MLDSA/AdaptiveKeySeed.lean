/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.MLDSA.KeySeedSearch
public import CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison
-- Reads private `RowSigner`, `changed_keySeed_le`, and `keySeedDeviceGame` internals.
import all CslibFrontier.Crypto.Computational.MLDSA.KeySeedSearch
import CslibFrontier.Probability.Hellinger
-- Reads private `Test`, `addressTest`, `addressTest_law`, `hit`, and `scored_gap_le`.
import all CslibFrontier.Crypto.Computational.MLDSA.SigningQueryComparison

/-!
# Adaptive key-seed prediction and the signed ML-DSA forgery bound

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

The same controller comparison bounds the effect of the programmed mask-seed rows on the
final forgery event. For the original finite random-XOF experiment the remaining terms are
the private-mask fresh-digest game, a raw collision, and the repeated-digest Hermite MSIS solver.
-/

public section

namespace Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger

open Cslib.Quantum Cslib.Probability
open scoped ENNReal Cslib.Probability.PMF

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
        (√((f a i true).toReal) - √((g a i true).toReal)) ^ 2 :=
      Finset.sum_le_sum fun i _ => by
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

-- The background execution is independent of the seed. After measuring its address, at most
-- one seed can select that address for the 128-byte key-expansion override.
private theorem mean_keySeed_hit {C : QuantumSigningForger} {α V : Type} [Zero V]
    (prog : Program C α) (s : Level) (H : Xofs) (out : FixedBytes 128)
    (sign : V → SigningQuery → Option (List Byte)) (d : Device C) (log : List Forgery)
    (tape : List V) (j : ℕ) :
    ∑ seed, ((PMF.uniformOfFintype (FixedBytes 32)) seed).toReal *
      (hit prog (H.withKeySeedExpansion s seed out) H sign d log tape j true).toReal ≤
        1 / 2 ^ 256 := by
  simpa only [PMF.bind_apply_toReal, ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat,
    one_div] using ENNReal.toReal_mono (by simp)
      (hit_mean_le (PMF.uniformOfFintype (FixedBytes 32))
        (fun seed => H.withKeySeedExpansion s seed out) H prog sign d log tape j
        fun a => changed_keySeed_le C s H out a)

private theorem scored_bound {C : QuantumSigningForger} {α : Type} {prog : Program C α} {j : ℕ}
    (cost : OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) prog j)
    (s : Level) (H : Xofs) (out : FixedBytes 128)
    (sign : Row → SigningQuery → Option (List Byte))
    (test : α → List Forgery → List Row → Test C)
    (d : Device C) (log : List Forgery) (tape : List Row) :
    ‖amps (fun seed => scored prog (H.withKeySeedExpansion s seed out) sign test d log tape) -
      amps (fun _ => scored prog H sign test d log tape)‖ ≤ j * (2 / 2 ^ 128) := by
  classical
  let G := fun seed => H.withKeySeedExpansion s seed out
  let w := fun seed => ((PMF.uniformOfFintype (FixedBytes 32)) seed).toReal
  let h := fun seed i => (hit prog (G seed) H sign d log tape i true).toReal
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), amps_sq]
  calc
    _ ≤ ∑ seed, w seed * (4 * j * ∑ i ∈ Finset.range j, h seed i) :=
      Finset.sum_le_sum fun seed _ => mul_le_mul_of_nonneg_left
        (scored_gap_le cost (G seed) H sign test d log tape) ENNReal.toReal_nonneg
    _ = 4 * j * ∑ i ∈ Finset.range j, ∑ seed, w seed * h seed i := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun seed _ => mul_left_comm ..
    _ ≤ 4 * j * ∑ _i ∈ Finset.range j, (1 / 2 ^ 256 : ℝ) := by
      gcongr with i
      exact mean_keySeed_hit prog s H out sign d log tape i
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

private theorem prefix_queries_le {C : QuantumSigningForger} {α : Type}
    (p : Program C α) (j : ℕ) :
    OracleComp.IsCostBounded (fun q => (isXofQuery q).toNat) (queryPrefix p j) j := by
  induction p generalizing j with
  | pure a => exact .pure _ _
  | liftBind q k ih =>
    rw [queryPrefix]
    split
    · exact .pure _ _
    · refine OracleComp.IsCostBounded.liftBind_iff.mpr ⟨?_, fun a => ih a _⟩
      cases hq : isXofQuery q <;> simp_all
      lia

private theorem observations_bound (C : QuantumSigningForger) (s : Level) (H : Xofs)
    (out : FixedBytes 128) (sv : Option RowSigner) {n : ℕ} (rows : SigningMaskSeeds n)
    (j : ℕ) (accept : List (List Bool) → Bool) :
    ‖amps (fun seed =>
        (C.observations (H.withKeySeedExpansion s seed out) s sv rows j).map accept) -
      amps (fun _ => (C.observations H s sv rows j).map accept)‖ ≤ j * (2 / 2 ^ 128) := by
  let report := accept ∘ signingSeedCandidates (C := C) (sv.map RowSigner.hash)
  simp only [observations, serviceAddress, addressLaw, PMF.map_comp, withTrialSetup,
    Xofs.expandA_congr (H := H) (K := H.withKeySeedExpansion s _ out) rfl]
  rcases sv with _ | sv
  · simp
  · dsimp only
    cases hA : H.expandA s (sv.publicKey.take 32)
    · simp
    · let p := queryPrefix (C := C) (C.program sv.publicKey) j
      let tape := List.ofFn fun i μ => rows (i, μ)
      have law (T : Xofs) :
          ((((OracleComp.interpret (OracleComp.withSampleListWhen isSigningCall (fun _ _ => 0)
            (fun row => C.signingCommand T (sv.reply row))) p).run (C.initial, tape)).map
              (fun (found, st, _) => (found, st))).bind (addressRead C)).map report =
            scored p T sv.reply (fun found _ _ => addressTest C report found)
              C.initial.1 C.initial.2 tape := by
        simp only [scored, PMF.map_bind, PMF.bind_map, Function.comp_def, addressTest_law C report]
        rfl
      simpa only [← law, report, p, tape] using
        scored_bound (prefix_queries_le (C.program sv.publicKey) j) s H out sv.reply
          (fun found _ _ => addressTest C report found) C.initial.1 C.initial.2 tape

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
  let game seed := seeds.bind fun K =>
    (C.observations (H.withKeySeedExpansion s seed (Fin.append p K)) s sv rows j).map (test K)
  let ref := seeds.bind fun K => (C.observations H s sv rows j).map (test K)
  have hmass : ref true ≤ 2 * (2 ^ 256 : ℝ≥0∞)⁻¹ := by
    simp only [ref, observations, PMF.map_comp]
    change (seeds.bind fun K => (C.serviceAddress H s sv rows j).bind fun addr =>
      PMF.pure (test K (signingSeedCandidates (C := C) (sv.map RowSigner.hash) addr))) true ≤ _
    rw [PMF.bind_comm]
    exact PMF.bind_apply_le_on_support _ fun addr _ =>
      two_guesses (C := C) (sv.map RowSigner.hash) addr
  have href : ‖amps (fun _ => ref)‖ ≤ √(2 / 2 ^ 256) := by
    rw [← sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _), norm_amps_sq, PMF.bind_const,
      Real.sq_sqrt (by positivity)]
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_inv,
      ENNReal.toReal_pow, div_eq_mul_inv] using
        ENNReal.toReal_mono (ENNReal.mul_ne_top (by simp)
          (ENNReal.inv_ne_top.mpr (by positivity))) hmass
  have bound : ‖amps game‖ ≤ √(2 / 2 ^ 256) + j * (2 / 2 ^ 128) := by
    calc
      _ ≤ ‖amps game - amps (fun _ => ref)‖ + ‖amps (fun _ => ref)‖ := by
        simpa using norm_add_le (amps game - amps fun _ => ref) (amps fun _ => ref)
      _ ≤ _ := (add_le_add (amps_bind_le seeds _ _ (by positivity) fun K =>
        observations_bound C s H (Fin.append p K) sv rows j (test K)) href).trans_eq (add_comm ..)
  change (seeds.bind game) true ≤ _
  rw [ENNReal.le_ofReal_iff_toReal_le ((seeds.bind game).apply_ne_top true) (sq_nonneg _),
    ← norm_amps_sq]
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
  refine ENNReal.toReal_le_of_le_ofReal (sq_nonneg _) ?_
  simp only [keySeedDeviceGame, PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, ↓reduceIte]
  rw [PMF.bind_comm]
  refine PMF.bind_apply_le_on_support _ fun rows _ => ?_
  rw [PMF.bind_comm]
  refine PMF.bind_apply_le_on_support _ fun H _ => ?_
  rw [PMF.bind_comm]
  exact PMF.bind_apply_le_on_support _ fun p _ =>
    fixed_observations_le C s H p (rowSigner (setupOracle H s p) s fun _ => 0) rows j

/-- Upper bound on the shared-device success amplitude for any final signed-trial event.
The private signing-seed prediction bound controls the address measured at each coherent
query. The background success term includes every classical signing request. -/
theorem sqrt_maskSeedGame_le (C : QuantumSigningForger) (s : Level) (base : Xofs)
    {a b n m : ℕ} (ha : 1024 ≤ a) (hb : 128 ≤ b) (hn : C.SigningCallsLe n)
    (hsize : n ≤ 2 ^ 256) (hm : C.XofCallsLe m) (score : SignedMatrixTrial s → Bool) :
    let view := C.maskSeedGame s base ha ((by decide : 64 ≤ 128).trans hb) hn hsize
    √(Game.succProbability (view true score) : ℝ) ≤
      √(Game.succProbability (view false score) : ℝ) +
      2 * m * √(2 * n / 2 ^ 256) * (√(2 / 2 ^ 256) + m * (2 / 2 ^ 128)) := by
  intro view
  let rate : ℝ := 2 * n / 2 ^ 256
  let pred (i : ℕ) : ℝ := √(2 / 2 ^ 256) + i * (2 / 2 ^ 128)
  let hit := C.maskSeedQueryHit s base ha ((by decide : 64 ≤ 128).trans hb) hsize
  have bound (i : ℕ) (hi : i ∈ Finset.range m) :
      (Game.succProbability (hit i) : ℝ) ≤ rate * pred m ^ 2 := by
    have mono : pred i ≤ pred m := add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (by exact_mod_cast (Finset.mem_range.mp hi).le) (by positivity))
    exact (C.maskSeedQueryHit_le_signingSeedPrediction s base ha
      ((by decide : 64 ≤ 128).trans hb) hn hsize i).trans (mul_le_mul_of_nonneg_left
      ((C.signingSeedPredictionGame_le s base ((by decide : 272 ≤ 1024).trans ha) hb n i).trans
        (pow_le_pow_left₀ (by dsimp [pred]; positivity) mono 2)) (by positivity))
  let loss := 2 * m * √rate * pred m
  have sq : (√(Game.succProbability (view true score) : ℝ) -
      √(Game.succProbability (view false score) : ℝ)) ^ 2 ≤ loss ^ 2 := by
    refine (C.maskSeedGame_sq_sqrt_sub_le s base ha ((by decide : 64 ≤ 128).trans hb)
      hn hsize hm score).trans ?_
    calc
      _ ≤ 4 * m * ∑ _i ∈ Finset.range m, (rate * pred m ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum bound) (by positivity)
      _ = _ := by
        have hrate : 0 ≤ rate := by positivity
        simp only [loss, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_pow,
          Real.sq_sqrt hrate]
        ring
  exact sub_le_iff_le_add'.mp ((le_abs_self _).trans ((sq_le_sq₀ (abs_nonneg _)
    (by positivity)).mp (by simpa only [sq_abs] using sq)))

/-- Concrete comparison from the original strong-forgery event to the fresh-digest game with
private signing mask seeds. The remaining probability terms are that private game, raw hash
collision and repeated-digest Hermite MSIS extraction. The two budgets count classical signing
calls and coherent XOF calls, respectively. -/
theorem randomPrefixGame_forgery_le_of_query_budget (C : QuantumSigningForger) (s : Level)
    (base : Xofs) {a b n m : ℕ} (ha : 1024 ≤ a) (hb : 894 ≤ b)
    (hn : C.SigningCallsLe n) (hsize : n ≤ 2 ^ 256) (hm : C.XofCallsLe m) :
    let R := base.uniformPrefixes a b
    let trial := R.bind (C.matrixTrial s)
    let loss : ℝ := 2 * m * √(2 * n / 2 ^ 256) * (√(2 / 2 ^ 256) + m * (2 / 2 ^ 128))
    (Game.succProbability (C.randomPrefixGame s base a b) : ℝ) ≤
      (√((Game.succProbability (C.privateMaskSeedGame s base a b) : ℝ) + n / 2 ^ 256) +
        loss) ^ 2 + ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 +
      Game.succProbability (trial.map (·.any SignedMatrixTrial.hashCollision)) +
      Game.succProbability ((PMF.uniformOfFintype (PublicMatrix s)).bind fun A =>
        (R.bind fun H => C.matrixSolver s H A).map fun v => decide (ModuleSIS.IsSolution
          (ModuleSIS.hermiteMatrix A)
          (max (2 * (s.params.γ₁ - s.params.β)) (4 * s.params.γ₂ + 2)) v)) := by
  intro R trial loss
  let fresh := trial.map (·.any SignedMatrixTrial.newDigestWin)
  let priv := C.privateMaskSeedGame s base a b
  let view (shared : Bool) := C.maskSeedGame s base ha ((by decide : 64 ≤ 894).trans hb)
    hn hsize shared SignedMatrixTrial.newDigestWin
  have birthday : dist fresh (view true) ≤ ((n * (n - 1) : ℕ) : ℝ) / 2 ^ 257 :=
    C.dist_matrixTrial_sharedMaskSeedGame s base ha hb hn hsize _
  have ref : dist (view false) priv ≤ n / 2 ^ 256 :=
    C.dist_maskSeedGame_privateMaskSeedGame s base ha _ hn hsize
  rw [← coe_nndist, ← Game.advantage_eq_nndist] at birthday ref
  have amp : √(Game.succProbability (view true) : ℝ) ≤
      √((Game.succProbability priv : ℝ) + n / 2 ^ 256) + loss :=
    (C.sqrt_maskSeedGame_le s base ha ((by decide : 128 ≤ 894).trans hb)
      hn hsize hm SignedMatrixTrial.newDigestWin).trans
      (add_le_add (Real.sqrt_le_sqrt (Game.coe_succProbability_le_add_of_advantage_le ref)) le_rfl)
  have primary := pow_le_pow_left₀ (Real.sqrt_nonneg _) amp 2
  rw [Real.sq_sqrt (NNReal.coe_nonneg _)] at primary
  have branch := NNReal.coe_le_coe.mpr
    (C.randomPrefixGame_forgery_le s base ((by decide : 272 ≤ 1024).trans ha) hb)
  simp only [NNReal.coe_add] at branch
  exact branch.trans ((add_le_add ((Game.coe_succProbability_le_add_of_advantage_le
    birthday).trans (add_le_add primary le_rfl)) le_rfl).trans_eq (add_assoc ..).symm)

end Cslib.Crypto.MLDSA.FIPS204.QuantumSigningForger
