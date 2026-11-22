/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle.Computational
import CslibFrontier.Computability.Interactive.Security.Oracle
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Game.CloseTo.UniformNat
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Tests for computational random-oracle KDF over encoded non-bit-string finite families

Exercises `CslibFrontier.Crypto.Computational.KeyDerivation.RandomOracle.Computational` over
non-power-of-two finite residue rings `ZMod q` (`q` a power of `3`):

1. **Canonical residue codec and approximate fair-coin residue sampler**: `encZModVal q`,
   `decZModVal q`, `sampleZModModNat width q`, and their `ComputableInPolyTime` / `IsPPTOn` /
   `StatisticallyIndistinguishable` certificates.
2. **Subtle model boundary witnesses** on `ZMod 3`: non-canonical trailing-zero queries (`[false]`),
   canonical-`ℕ` out-of-range queries (`[true, true]` for `3`), and repeated valid queries
   (`encZModVal 3 2 = [false, true]`), verifying malformed-query rejection (`[]` and cache
   exclusion), repeated-query deduplication (`[2]`), and the exact non-dyadic advantage `2 / 3`.
3. **End-to-end computational Theorem 8.10 over dependent non-bit-string families**: uniform secrets
   in `ZMod (3 ^ (2 * (n + 1)))` leaking `ZMod.castHom ... : ZMod (3 ^ (2 * (n + 1))) →
   ZMod (3 ^ (n + 1))`, with keys in `ZMod 3` sampled via `sampleZModModNat n 3`, together with a
   concrete `WordRODistinguisher.IsPPT` witness reading the leaked `ZMod (3 ^ (n + 1))` residue.
-/

public section

namespace CslibFrontierTests.Crypto.RandomOracleKDFEncoded

open Cslib Probability Cslib.Crypto Cslib.Crypto.KeyDerivation Turing.MultiTapeTM
open Cslib.Probability.PMF (uniformOfFintype)
open scoped ENNReal NNReal Cslib.Probability.PMF

/-! ### 1. Canonical binary-value codec and fair-coin sampler for `ZMod q` -/

/-- Canonical unsigned binary encoding of `ZMod q` (`[NeZero q]`) via `ZMod.val` and `encNat`. -/
@[expose] def encZModVal (q : ℕ) [NeZero q] : ZMod q ↪ List Bool :=
  ⟨fun a => encNat a.val, encNat.injective.comp (ZMod.val_injective q)⟩

/-- Strict partial decoder for `encZModVal q`: accepts `w` iff `w` has no trailing `false` digits
(`encNat (ofBits w) = w`) and `ofBits w < q`. -/
@[expose] def decZModVal (q : ℕ) [NeZero q] (w : List Bool) : Option (ZMod q) :=
  if encNat (ofBits w) = w ∧ ofBits w < q then some (ofBits w : ZMod q) else none

theorem decZModVal_eq_some_iff (q : ℕ) [NeZero q] (w : List Bool) (a : ZMod q) :
    decZModVal q w = some a ↔ encZModVal q a = w := by
  unfold decZModVal encZModVal
  simp only [Function.Embedding.coeFn_mk]
  constructor
  · intro h
    split_ifs at h with hcond
    obtain ⟨hcanon, hlt⟩ := hcond
    cases Option.some.inj h
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt hlt]
    exact hcanon
  · rintro rfl
    have hob : ofBits (encNat a.val) = a.val := Decoder.nat.decode_enc a.val
    have hcond : encNat (ofBits (encNat a.val)) = encNat a.val ∧ ofBits (encNat a.val) < q := by
      rw [hob]
      exact ⟨rfl, ZMod.val_lt a⟩
    rw [ite_eq_left hcond, hob, ZMod.natCast_zmod_val]

theorem computableInPolyTime_isSome_decZModVal {q : ℕ → ℕ} [∀ n, NeZero (q n)]
    (hq : ComputableInPolyTime q encUnary encNat) :
    ComputableInPolyTime (fun p : ℕ × List Bool => (decZModVal (q p.1) p.2).isSome)
      (encPair encUnary encBits) encBool := by
  let E := encPair encUnary encBits
  have hn : ComputableInPolyTime (fun p : ℕ × List Bool => p.1) E encUnary := by fun_prop
  have hw : ComputableInPolyTime (fun p : ℕ × List Bool => p.2) E encBits := by fun_prop
  have hval : ComputableInPolyTime (fun p : ℕ × List Bool => ofBits p.2) E encNat :=
    ComputableInPolyTime.bitsToNat.comp hw
  have hcanon_word : ComputableInPolyTime (fun p : ℕ × List Bool => encNat (ofBits p.2))
      E encBits :=
    hval.of_enc_eq fun _ => rfl
  have hcanon : ComputableInPolyTime (fun p : ℕ × List Bool => encNat (ofBits p.2) == p.2)
      E encBool :=
    ComputableInPolyTime.beq hcanon_word hw
  have hlt : ComputableInPolyTime (fun p : ℕ × List Bool => decide (ofBits p.2 < q p.1))
      E encBool :=
    ComputableInPolyTime.binary_lt' hval (hq.comp hn)
  have heq : (fun p : ℕ × List Bool => (decZModVal (q p.1) p.2).isSome) =
      fun p : ℕ × List Bool => (encNat (ofBits p.2) == p.2) && decide (ofBits p.2 < q p.1) := by
    funext p
    unfold decZModVal
    by_cases h1 : (ofBits p.2).bits = p.2 <;> by_cases h2 : ofBits p.2 < q p.1 <;>
      simp [encNat_apply, h1, h2]
  rw [heq]
  fun_prop

/-- Fair-coin modular sampler on `ZMod q`. -/
@[expose] noncomputable def sampleZModModNat (width q : ℕ) : ProbComp (ZMod q) :=
  (Nat.cast : ℕ → ZMod q) <$> ProbComp.sampleModNat width q

theorem isPPTOn_encZModVal_sampleZModModNat {width q : ℕ → ℕ} [∀ n, NeZero (q n)]
    (hwidth : ComputableInPolyTime width encUnary encUnary)
    (hq : ComputableInPolyTime q encUnary encNat) :
    IsPPTOn encUnary encBits fun n => encZModVal (q n) <$> sampleZModModNat (width n) (q n) := by
  obtain ⟨k, State, hfin, machine, c, d, hrun⟩ := isPPTOn_sampleModNat hwidth hq
  refine ⟨k, State, hfin, machine, c, d, fun n => ?_⟩
  rw [← hrun n]
  simp only [sampleZModModNat, ProbComp.eval_map, PMF.map_comp, Function.comp_def, encBits_apply]
  rw [PMF.map, PMF.map]
  refine PMF.bind_congr_on_support _ _ _ fun m hm => ?_
  rw [ProbComp.eval_sampleModNat, PMF.mem_support_map_iff] at hm
  obtain ⟨x, -, rfl⟩ := hm
  have hlt : x.val % q n < q n := Nat.mod_lt _ (NeZero.pos (q n))
  simp [encZModVal, ZMod.val_natCast, Nat.mod_eq_of_lt hlt]

theorem statisticallyIndistinguishable_uniform_sampleZModModNat (q : ℕ) [NeZero q] :
    StatisticallyIndistinguishable (fun _ => uniformOfFintype (ZMod q))
      (fun n => ProbComp.eval (sampleZModModNat n q)) := by
  refine ⟨fun n => (q : ℝ≥0) / 2 ^ n, ?_, fun n => ?_⟩
  · have hmul : (fun n : ℕ => (q : ℝ≥0) / 2 ^ n) = fun n => (q : ℝ≥0) * (1 / 2 ^ n) := by
      funext n
      ring
    rw [hmul]
    exact negligible_one_div_two_pow.const_mul (q : ℝ≥0)
  · simpa only [sampleZModModNat, ProbComp.eval_map, ENNReal.coe_div (pow_ne_zero _ two_ne_zero),
      ENNReal.coe_natCast, ENNReal.coe_pow, ENNReal.coe_ofNat] using
        closeTo_uniform_sampleModNat n q

/-! ### 2. Boundary witnesses on `ZMod 3`: malformed queries, deduplication, exact `2 / 3` -/

/-- Non-canonical trailing-zero word `[false]` (`ofBits [false] = 0 < 3`, but `encNat 0 = []`) is
rejected by `decZModVal 3`. -/
theorem decZModVal_three_trailing_zero : decZModVal 3 [false] = none := by
  decide

/-- Canonical binary word `[true, true]` (`ofBits [true, true] = 3 ≥ 3`) is rejected as out of range
for `ZMod 3`. -/
theorem decZModVal_three_out_of_range : decZModVal 3 [true, true] = none := by
  decide

/-- Canonical encoding of `(2 : ZMod 3)` is `[false, true]` and decodes to `some 2`. -/
theorem decZModVal_three_two :
    encZModVal 3 (2 : ZMod 3) = [false, true] ∧ decZModVal 3 [false, true] = some 2 := by
  decide

/-- Boundary distinguisher on `ZMod 3`: issues two malformed queries (`[false]` and `[true, true]`)
and two identical valid queries (`[false, true]`, encoding `2 : ZMod 3`), checking that malformed
queries return `[]`, repeated valid queries return equal replies, and the valid reply matches `z`.
-/
def boundaryZMod3Distinguisher : WordRODistinguisher (fun _ => Unit) :=
  fun _ _ z => do
    let r₁ ← ProbOracleComp.query ((), [false])
    let r₂ ← ProbOracleComp.query ((), [true, true])
    let y₁ ← ProbOracleComp.query ((), [false, true])
    let y₂ ← ProbOracleComp.query ((), [false, true])
    return decide (r₁ = [] ∧ r₂ = [] ∧ y₁ = y₂ ∧ y₁ = z)

theorem isQueryBounded_boundaryZMod3Distinguisher (n : ℕ) (z : List Bool) :
    (boundaryZMod3Distinguisher n () z).IsQueryBounded 4 := by
  unfold boundaryZMod3Distinguisher
  have h1 := ProbOracleComp.IsQueryBounded.query (spec := fun _ : Unit × List Bool => List Bool)
    ((), [false])
  have h2 := ProbOracleComp.IsQueryBounded.query (spec := fun _ : Unit × List Bool => List Bool)
    ((), [true, true])
  have h3 := ProbOracleComp.IsQueryBounded.query (spec := fun _ : Unit × List Bool => List Bool)
    ((), [false, true])
  refine (h1.bind fun r₁ => (h2.bind fun r₂ => (h3.bind fun y₁ => (h3.bind fun y₂ =>
    OracleComp.IsCostBounded.pure (decide (r₁ = [] ∧ r₂ = [] ∧ y₁ = y₂ ∧ y₁ = z)) 0)))).mono ?_
  omega

/-- Every list output by `lazyROToListGuess` on `boundaryZMod3Distinguisher` equals `[2]`: both
malformed queries (`[false]`, `[true, true]`) are excluded from the cache, and the second valid
query (`[false, true]`) hits the existing cache entry without duplicating `2`. -/
theorem eq_singleton_two_of_mem_support_lazyROToListGuess_boundary (n : ℕ)
    {l : List (ZMod 3)}
    (hl : l ∈ (ProbComp.eval
      (lazyROToListGuess (fun _ => decZModVal 3) (fun _ => encZModVal 3)
        (fun m => sampleZModModNat m 3) boundaryZMod3Distinguisher n ())).support) :
    l = [2] := by
  have hbad₁ : (decZModVal 3 [false]).isSome = false := by
    rw [decZModVal_three_trailing_zero]; rfl
  have hbad₂ : (decZModVal 3 [true, true]).isSome = false := by
    rw [decZModVal_three_out_of_range]; rfl
  have hgood : (decZModVal 3 [false, true]).isSome = true := by
    rw [decZModVal_three_two.2]; rfl
  have hprog (t : ZMod 3) :
      ((boundaryZMod3Distinguisher n () (encZModVal 3 t)).runState fun req =>
        cachedSamplerOracle (fun w => (decZModVal 3 w).isSome)
          (encZModVal 3 <$> sampleZModModNat n 3) req.2).run [] =
        (fun v => (decide (v = encZModVal 3 t), [([false, true], v)])) <$>
          (encZModVal 3 <$> sampleZModModNat n 3) := by
    simp only [boundaryZMod3Distinguisher, ProbOracleComp.runState_bind,
      ProbOracleComp.runState_query, ProbOracleComp.runState_pure, StateT.run_bind,
      StateT.run_pure]
    dsimp only [StateT.run]
    simp [cachedSamplerOracle, hbad₁, hbad₂, hgood, Cslib.memoize]
  simp only [lazyROToListGuess, hprog, ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_map_iff, PMF.mem_support_pure_iff] at hl
  obtain ⟨t, -, bc, ⟨v, -, hbc⟩, rfl⟩ := hl
  rw [← hbc]
  simp [decZModVal_three_two.2]

/-- On deterministic secret `2 : ZMod 3`, `boundaryZMod3Distinguisher` achieves exact non-dyadic
random-oracle KDF distinguishing advantage `2 / 3`, and satisfies the concrete approximate-sampler
bound `roAdvantage_toRODistinguisher_le_listGuessAdvantage_add`. -/
theorem roAdvantage_boundaryZMod3Distinguisher_eq_two_thirds (n : ℕ) :
    roAdvantage (PMF.pure (2 : ZMod 3)) (fun _ => ())
      (toRODistinguisher (fun _ => decZModVal 3) (fun _ => encZModVal 3)
        boundaryZMod3Distinguisher n) = 2 / 3 := by
  let D := toRODistinguisher (fun _ => decZModVal 3) (fun _ => encZModVal 3)
    boundaryZMod3Distinguisher n
  have hrun (table : ZMod 3 → ZMod 3) (t : ZMod 3) :
      ProbComp.eval ((D () t).run fun q => pure (table q)) =
        PMF.pure (decide (table 2 = t)) := by
    simp [D, toRODistinguisher, boundaryZMod3Distinguisher, decZModVal_three_trailing_zero,
      decZModVal_three_out_of_range, decZModVal_three_two.2]
  have hreal : roRealOutput (PMF.pure (2 : ZMod 3)) (fun _ => ()) D true = 1 := by
    unfold roRealOutput realOutput
    simp [hrun, PMF.bind_const]
  have hideal : roIdealOutput (PMF.pure (2 : ZMod 3)) (fun _ => ()) D true = (3 : ℝ≥0∞)⁻¹ := by
    unfold roIdealOutput idealOutput
    simp only [PMF.pure_bind, hrun]
    rw [PMF.bind_apply]
    have hpt (table : ZMod 3 → ZMod 3) :
        ((uniformOfFintype (ZMod 3)).bind fun z => PMF.pure (decide (table 2 = z))) true =
          (3 : ℝ≥0∞)⁻¹ := by
      rw [Probability.PMF.bind_pure_decide_eq_apply_true, PMF.uniformOfFintype_apply,
        ZMod.card 3]
      norm_num
    simp only [hpt, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [← NNReal.coe_inj, roAdvantage, Game.coe_advantage, Game.coe_succProbability,
    Game.coe_succProbability, hreal, hideal]
  norm_num

theorem roAdvantage_boundaryZMod3_le_listGuessAdvantage_add (n : ℕ) :
    roAdvantage (PMF.pure (2 : ZMod 3)) (fun _ => ())
      (toRODistinguisher (fun _ => decZModVal 3) (fun _ => encZModVal 3)
        boundaryZMod3Distinguisher n) ≤
      listGuessAdvantage (PMF.pure (2 : ZMod 3)) (fun _ => ())
        (lazyROToListGuess (fun _ => decZModVal 3) (fun _ => encZModVal 3)
          (fun m => sampleZModModNat m 3) boundaryZMod3Distinguisher n) +
        (4 + 1 : ℕ) * ((3 : ℝ≥0) / 2 ^ n) :=
  roAdvantage_toRODistinguisher_le_listGuessAdvantage_add
    (fun _ => decZModVal_eq_some_iff 3) (fun _ => encZModVal 3) (fun m => sampleZModModNat m 3)
    (fun _ => PMF.pure (2 : ZMod 3)) (fun _ _ => ()) boundaryZMod3Distinguisher n 4
    (by
      simpa only [sampleZModModNat, ProbComp.eval_map, ENNReal.coe_div (pow_ne_zero _ two_ne_zero),
        ENNReal.coe_pow, ENNReal.coe_ofNat, Nat.cast_ofNat] using closeTo_uniform_sampleModNat n 3)
    (fun _ _ _ _ => isQueryBounded_boundaryZMod3Distinguisher n _)

/-! ### 3. End-to-end Theorem 8.10 over `ZMod (3 ^ (2 * (n + 1))) → ZMod (3 ^ (n + 1))` & `ZMod 3`
-/

private instance instNeZeroThreePow (k : ℕ) : NeZero (3 ^ k) :=
  ⟨pow_ne_zero k (by decide)⟩

/-- Uniform secret in `ZMod (3 ^ (2 * (n + 1)))` leaking its residue modulo `3 ^ (n + 1)`. -/
def zmodLeakInfo (n : ℕ) : ZMod (3 ^ (2 * (n + 1))) → ZMod (3 ^ (n + 1)) :=
  ZMod.castHom (pow_dvd_pow 3 (by omega : n + 1 ≤ 2 * (n + 1))) (ZMod (3 ^ (n + 1)))

/-- `SecretGuessHard` for uniform secrets in `ZMod (3 ^ (2 * (n + 1)))` leaking `zmodLeakInfo n`:
every guessing adversary has advantage at most `(3 ^ (n + 1))⁻¹ ≤ (2 ^ n)⁻¹`. -/
theorem secretGuessHard_zmodPow_castHom :
    SecretGuessHard (fun n => encZModVal (3 ^ (n + 1)))
      (fun n => encZModVal (3 ^ (2 * (n + 1))))
      (fun n => uniformOfFintype (ZMod (3 ^ (2 * (n + 1))))) zmodLeakInfo := by
  intro A _
  refine negligible_of_le negligible_one_div_two_pow fun n => ?_
  have hcard := guessAdvantage_le_card_mul_of_mass_le
    (uniformOfFintype (ZMod (3 ^ (2 * (n + 1))))) (zmodLeakInfo n)
    (mass := ((3 ^ (2 * (n + 1)) : ℕ) : ℝ≥0)⁻¹)
    (fun s => by
      rw [PMF.uniformOfFintype_apply, ZMod.card]
      push_cast
      exact le_rfl)
    (A n)
  refine hcard.trans ?_
  rw [ZMod.card (3 ^ (n + 1))]
  have hpow : (2 ^ n : ℝ≥0) ≤ (3 ^ (n + 1) : ℕ) := by
    exact_mod_cast (Nat.pow_le_pow_left (by decide : 2 ≤ 3) n).trans
      (Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_succ n))
  have hmul : ((3 ^ (n + 1) : ℕ) : ℝ≥0) * ((3 ^ (2 * (n + 1)) : ℕ) : ℝ≥0)⁻¹ =
      ((3 ^ (n + 1) : ℕ) : ℝ≥0)⁻¹ := by
    have hsplit : 3 ^ (2 * (n + 1)) = 3 ^ (n + 1) * 3 ^ (n + 1) := by
      rw [← pow_add]
      congr 1
      omega
    have hne : ((3 ^ (n + 1) : ℕ) : ℝ≥0) ≠ 0 := by positivity
    rw [hsplit, Nat.cast_mul, mul_inv, mul_comm, inv_mul_cancel_right₀ hne]
  rw [hmul, one_div]
  exact inv_anti₀ (by positivity) hpow

/-- **End-to-end application of `SecretGuessHard.negligible_roAdvantage`** over non-bit-string
secret, side-information, and digest families (`ZMod (3 ^ (2 * (n + 1)))`, `ZMod (3 ^ (n + 1))`, and
`ZMod 3`). -/
theorem negligible_roAdvantage_zmodPow_zmod3
    {D : WordRODistinguisher (fun n => ZMod (3 ^ (n + 1)))}
    (hD : D.IsPPT (fun n => encZModVal (3 ^ (n + 1)))) :
    Negligible fun n =>
      roAdvantage (uniformOfFintype (ZMod (3 ^ (2 * (n + 1))))) (zmodLeakInfo n)
        (toRODistinguisher (fun n => decZModVal (3 ^ (2 * (n + 1))))
          (fun _ => encZModVal 3) D n) := by
  have hq : ComputableInPolyTime (fun n : ℕ => 3 ^ (2 * (n + 1))) encUnary encNat :=
    ComputableInPolyTime.binary_pow' (.const 3) (by fun_prop)
  have hdefault : ComputableInPolyTime
      (fun n : ℕ => encZModVal (3 ^ (2 * (n + 1))) 0) encUnary encBits := by
    have heq : (fun n : ℕ => encZModVal (3 ^ (2 * (n + 1))) 0) = fun _ => ([] : List Bool) := by
      funext n
      simp [encZModVal, ZMod.val_zero]
    rw [heq]
    exact .const []
  have hinfo : ∃ c d, ∀ n, ∀ s ∈ (uniformOfFintype (ZMod (3 ^ (2 * (n + 1))))).support,
      (encZModVal (3 ^ (n + 1)) (zmodLeakInfo n s)).length ≤ c * (n + 1) ^ d := by
    refine ⟨2, 1, fun n s _ => ?_⟩
    simp only [encZModVal, Function.Embedding.coeFn_mk, encNat_apply, pow_one]
    have hsize : (zmodLeakInfo n s).val.bits.length = (zmodLeakInfo n s).val.size := by
      simp [Nat.size_eq_bits_len]
    rw [hsize, Nat.size_le]
    have hlt : (zmodLeakInfo n s).val < 3 ^ (n + 1) := ZMod.val_lt _
    have hpow : 3 ^ (n + 1) ≤ 2 ^ (2 * (n + 1)) := by
      calc 3 ^ (n + 1) ≤ 4 ^ (n + 1) := Nat.pow_le_pow_left (by decide) _
        _ = (2 ^ 2) ^ (n + 1) := by norm_num
        _ = 2 ^ (2 * (n + 1)) := (pow_mul 2 2 (n + 1)).symm
    exact hlt.trans_le hpow
  exact secretGuessHard_zmodPow_castHom.negligible_roAdvantage
    (fun n => decZModVal_eq_some_iff (3 ^ (2 * (n + 1))))
    (computableInPolyTime_isSome_decZModVal hq)
    hdefault
    (isPPTOn_encZModVal_sampleZModModNat .id' (.const 3))
    (statisticallyIndistinguishable_uniform_sampleZModModNat 3)
    hinfo hD

/-- Concrete `WordRODistinguisher` over dependent `X n = ZMod (3 ^ (n + 1))`: queries the random
oracle at the leaked residue's canonical bit word and compares two reply bits with `z`. -/
def leakedResidueProbeDistinguisher : WordRODistinguisher (fun n => ZMod (3 ^ (n + 1))) :=
  fun n x z => do
    let reply ← List.take 2 <$> ProbOracleComp.query ((), encZModVal (3 ^ (n + 1)) x)
    return reply == z.take 2

theorem isPPT_leakedResidueProbeDistinguisher :
    leakedResidueProbeDistinguisher.IsPPT (fun n => encZModVal (3 ^ (n + 1))) := by
  let encX : ∀ n, ZMod (3 ^ (n + 1)) ↪ List Bool := fun n => encZModVal (3 ^ (n + 1))
  let E := encWordROInput encX
  have hraw : ComputableInPolyTime
      (fun y : WordROInput (fun n => ZMod (3 ^ (n + 1))) =>
        (y.secParam, encX y.secParam y.sideInfo, y.key))
      E (encPair encUnary (encPair encBits encBits)) :=
    ComputableInPolyTime.of_enc_eq (ComputableInPolyTime.id' (encIn := E)) fun y => by
      simp [E, encWordROInput_apply]
  have hx : ComputableInPolyTime
      (fun y : WordROInput (fun n => ZMod (3 ^ (n + 1))) => encX y.secParam y.sideInfo)
      E encBits :=
    hraw.snd'.fst'
  have hz : ComputableInPolyTime
      (fun y : WordROInput (fun n => ZMod (3 ^ (n + 1))) => y.key) E encBits :=
    hraw.snd'.snd'
  have hquery : IsOraclePPTOn E encBits
      (fun y : WordROInput (fun n => ZMod (3 ^ (n + 1))) =>
        List.take 2 <$> ProbOracleComp.query ((), encX y.secParam y.sideInfo)) :=
    IsOraclePPTOn.query_take () hx (.const 2)
  have hcmp : ComputableInPolyTime
      (fun p : WordROInput (fun n => ZMod (3 ^ (n + 1))) × List Bool =>
        p.2 == p.1.key.take 2)
      (encPair E encBits) encBool := by
    have hp₁ := ComputableInPolyTime.fst E encBits
    have hp₂ := ComputableInPolyTime.snd E encBits
    have htake : ComputableInPolyTime
        (fun p : WordROInput (fun n => ZMod (3 ^ (n + 1))) × List Bool => p.1.key.take 2)
        (encPair E encBits) encBits := by
      have hz' := hz.comp hp₁
      fun_prop
    exact ComputableInPolyTime.beq hp₂ htake
  simpa only [leakedResidueProbeDistinguisher, WordRODistinguisher.IsPPT, bind_pure_comp] using
    hquery.map_with (f := fun y reply => reply == y.key.take 2) hcmp

/-- Concrete witness instantiation: `leakedResidueProbeDistinguisher` has negligible random-oracle
KDF advantage on `ZMod (3 ^ (2 * (n + 1))) → ZMod 3`. -/
theorem negligible_roAdvantage_leakedResidueProbeDistinguisher :
    Negligible fun n =>
      roAdvantage (uniformOfFintype (ZMod (3 ^ (2 * (n + 1))))) (zmodLeakInfo n)
        (toRODistinguisher (fun n => decZModVal (3 ^ (2 * (n + 1))))
          (fun _ => encZModVal 3) leakedResidueProbeDistinguisher n) :=
  negligible_roAdvantage_zmodPow_zmod3 isPPT_leakedResidueProbeDistinguisher

end CslibFrontierTests.Crypto.RandomOracleKDFEncoded
