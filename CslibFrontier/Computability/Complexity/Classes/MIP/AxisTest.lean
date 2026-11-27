/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Code.MultilinearitySoundness
public import CslibFrontier.Probability.PMF.Expect
public import CslibFrontier.Computability.Complexity.Classes.PCP.ProofWord
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Finset.Expect
public import Mathlib.Algebra.Field.ZMod
public import CslibFrontier.Languages.Probabilistic.UniformNat.Residue
import CslibFrontier.Languages.Probabilistic.UniformNat.Support
import CslibFrontier.Computability.Probabilistic.UniformNat.ModIndex
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Probability.PMF.Uniform
import Mathlib.Data.List.GetD
import CslibFrontier.Probability.StatisticalDistance.CloseTo

/-!
# Axis-line verification for a bit-valued proof oracle

This verifier uses the approximate-line implication of [Babai, Fortnow and Lund, Theorem
5.13 and §7.1][BabaiFortnowLund1991] over a prime field. The verifier reads a value at a
field point and an affine function on the axis-parallel line containing it. A static
bit proof supplies three field values, the point value and the two coefficients of that line.
Zeroing the selected coordinate before querying the line prevents the proof from supplying
different affine functions for different positions on that line.

## Main definitions

* `checkAxis` compares a point value with the affine function reported for its axis line.
* `axisRound` samples the axis and point with fair bits and reads the three binary numbers.

## Main results

* `isOraclePPTOn_axisRound` certifies the strict polynomial running time of the verifier.
* `closeTo_axisRound` bounds the difference from the uniform field test by `2 / 2^precision`.
* `exists_assignment_of_axisRound` gives a multilinear polynomial differing from the point table
  on less than a `1/(100 (n+1))` fraction of the cube when the field has at least `1000 (n+1)^3`
  elements and rejection plus the sampling error is below `1/(10^6 (n+1)^7)`.
* `exists_axisTable_of_mem_restrictDegree` supplies an axis table for each multilinear polynomial
  that passes every round.
-/

public section

namespace Cslib.Complexity.MIP

open Cslib.Code Cslib.Probability Finset MvPolynomial
open scoped BigOperators

variable {n : ℕ} {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Coefficients of an axis-parallel affine restriction reported by a proof oracle. -/
structure LineAnswer (F : Type) where
  /-- The change in value per unit step along the selected axis. -/
  slope : F
  /-- The value where that coordinate vanishes. -/
  intercept : F

/-- Compare the proof's claimed value at a point with its affine restriction to one axis.
The line address zeroes that coordinate, so it is independent of the point along the line. -/
@[expose] def checkAxis (f : (Fin n → F) → F) (lines : Fin n → (Fin n → F) → LineAnswer F)
    (i : Fin n) (x : Fin n → F) : Bool :=
  let line := lines i (Function.update x i 0)
  decide (line.slope * x i + line.intercept = f x)

omit [Fintype F] in
/-- Every evaluation table of a multilinear polynomial has a line table passing every check. -/
theorem exists_checkAxis_of_mem_restrictDegree {A : MvPolynomial (Fin n) F}
    (hA : A ∈ restrictDegree (Fin n) F 1) :
    ∃ lines, ∀ i x, checkAxis (fun z => eval z A) lines i x = true := by
  classical
  have hm := isMultilinear_eval_of_mem_restrictDegree hA
  choose a b hab using hm
  refine ⟨fun i z => ⟨a z i, b z i⟩, fun i x => ?_⟩
  have h := hab (Function.update x i 0) i (x i)
  simpa [checkAxis, lineRestrict, Function.update_idem, Function.update_eq_self] using h.symm

/-- The uniformly random axis check is a finite experiment on a single axis and field point. -/
@[expose] noncomputable def uniformAxisCheck [NeZero n] (f : (Fin n → F) → F)
    (lines : Fin n → (Fin n → F) → LineAnswer F) : PMF Bool :=
  (PMF.uniformOfFintype (Fin n × (Fin n → F))).map (fun (i, x) => checkAxis f lines i x)

private theorem uniformAxisCheck_false [NeZero n] (f : (Fin n → F) → F)
    (lines : Fin n → (Fin n → F) → LineAnswer F) :
    (uniformAxisCheck f lines false).toReal = 𝔼 i : Fin n, 𝔼 x : Fin n → F,
      if checkAxis f lines i x then (0 : ℝ) else 1 := by
  classical
  rw [uniformAxisCheck, Probability.PMF.toReal_uniformOfFintype_map_apply,
    ← Fintype.expect_boole, Fintype.expect_prod_type]
  refine expect_congr rfl fun i _ => expect_congr rfl fun x _ => ?_
  cases h : checkAxis f lines i x <;> simp [h]

/-- A uniformly sampled axis and point detect a proof table that is too far from every
multilinear assignment for local correction. The correction step can make `n + 1` queries
per literal, so the exceptional fraction here scales inversely with that number. -/
theorem exists_assignment_of_checkAxis [NeZero n]
    (f : (Fin n → F) → F) (lines : Fin n → (Fin n → F) → LineAnswer F)
    (hq : 1000 * (n + 1) ^ 3 ≤ Fintype.card F)
    (hrej : (uniformAxisCheck f lines false).toReal < 1 / (10 ^ 6 * (n + 1 : ℝ) ^ 7)) :
    ∃ A ∈ restrictDegree (Fin n) F 1,
      (hammingDist f (fun x => eval x A) : ℝ) < Fintype.card F ^ n / (100 * (n + 1)) := by
  rw [uniformAxisCheck_false] at hrej
  let d : ℝ := n + 1
  let η : ℝ := 1 / (1000 * d ^ 3)
  let L (i : Fin n) (z : Fin n → F) (t : F) := (lines i z).slope * t + (lines i z).intercept
  have hn : 0 < n := NeZero.pos n
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : (0 : ℝ) < d := by dsimp [d]; positivity
  have hnd : (n : ℝ) ≤ d := by dsimp [d]; linarith
  have hqr : (1000 : ℝ) * d ^ 3 ≤ Fintype.card F := by dsimp [d]; exact_mod_cast hq
  have hdeg : 40 * n ^ 2 ≤ Fintype.card F := le_trans (by
    calc 40 * n ^ 2 ≤ 1000 * (n + 1) ^ 2 := by gcongr <;> omega
      _ ≤ 1000 * (n + 1) ^ 3 := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by omega : 0 < n + 1) (by decide : 2 ≤ 3))) hq
  have hδ : η ≤ 1 / (400 * (n : ℝ) ^ 2) := by
    apply one_div_le_one_div_of_le (by positivity)
    calc 400 * (n : ℝ) ^ 2 ≤ 1000 * d ^ 2 := by gcongr; norm_num
      _ ≤ 1000 * d ^ 3 := mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (by dsimp [d]; linarith : 1 ≤ d) (by decide : 2 ≤ 3)) (by norm_num)
  have hε : η ≤ 1 / (800 * (n : ℝ) ^ 3) := by
    apply one_div_le_one_div_of_le (by positivity)
    gcongr; norm_num
  have hgap : (1 : ℝ) / (10 ^ 6 * d ^ 7) ≤ η * η / n := by
    dsimp [η]
    calc 1 / (10 ^ 6 * d ^ 7) = (1 / (1000 * d ^ 3)) * (1 / (1000 * d ^ 3)) / d := by
          field_simp
          ring
      _ ≤ _ := by gcongr
  obtain ⟨g, hg, hfg⟩ := exists_isMultilinear_hammingDist_lt_of_lineOracle f L
    (fun i z => ⟨(lines i z).slope, (lines i z).intercept, fun _ => rfl⟩)
    hn hdeg (show 0 ≤ η by dsimp [η]; positivity) hδ hε (by
      simpa [checkAxis, L] using hrej.trans_le hgap)
  obtain ⟨A, hA, rfl⟩ := isMultilinear_iff_exists_mem_restrictDegree.mp hg
  refine ⟨A, hA, hfg.trans_le ?_⟩
  rw [div_eq_inv_mul _ (100 * ((n : ℝ) + 1))]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  have hqinv : (1 / (Fintype.card F : ℝ)) ≤ η :=
    one_div_le_one_div_of_le (by positivity) hqr
  calc 3 * (n : ℝ) ^ 2 * (η + η + 1 / Fintype.card F) ≤ 3 * d ^ 2 * (η + η + η) := by gcongr
    _ ≤ (100 * d)⁻¹ := by
      dsimp [η]
      field_simp
      nlinarith [sq_nonneg d]

open Turing.MultiTapeTM

/-- A proof's point table uses the tag `0` followed by a framed list of unary residues. -/
@[expose] def pointTableKey (point : List ℕ) : List Bool :=
  false :: encList encUnary point

/-- An axis-line table key contains tags `10`, a slope/intercept selector, a unary axis,
and a framed list of unary coordinates with the selected coordinate zeroed. -/
@[expose] def axisTableKey (slope : Bool) (i : ℕ) (point : List ℕ) : List Bool :=
  true :: false :: encPair encBool (encPair encUnary (encList encUnary)) (slope, i, point.set i 0)

private def axisKeys (i : ℕ) (point : List ℕ) : List (List Bool) :=
  [pointTableKey point, axisTableKey true i point, axisTableKey false i point]

private def checkValues (p x : ℕ) (values : List ℕ) : Bool :=
  decide ((values.getD 1 0 * x + values.getD 2 0) % p = values.getD 0 0 % p)

/-- Read the field value, slope and intercept from the proof, then check the axis equation mod `p`.
The verifier uses `p.size` bits of each table value. -/
def checkAxisAt (p i : ℕ) (point : List ℕ) : WordOracleComp Unit Bool := do
  let values ← ProofWord.readValues (axisKeys i point) p.size
  pure (checkValues p (point.getD i 0) values)

/-- The point table induced by a fixed proof over the given residue ring. -/
@[expose] def proofPoint (π : List Bool → Bool) (p : ℕ) (x : Fin n → ZMod p) : ZMod p :=
  ProofWord.value π (pointTableKey (List.ofFn fun k => (x k).val)) p.size

/-- The two coefficients returned by the fixed proof for a canonical axis-parallel line. -/
@[expose] def proofAxis (π : List Bool → Bool) (p : ℕ) (i : Fin n) (x : Fin n → ZMod p) :
    LineAnswer (ZMod p) :=
  let coords := List.ofFn fun k => (x k).val
  ⟨ProofWord.value π (axisTableKey true i coords) p.size,
    ProofWord.value π (axisTableKey false i coords) p.size⟩

/-- A run of the word verifier on field elements agrees with an affine line query on the two
tables represented by the proof, including malformed field representatives reduced modulo `p`. -/
theorem run_checkAxisAt (π : List Bool → Bool) {p : ℕ} [Fact p.Prime] (i : Fin n)
    (x : Fin n → ZMod p) :
    (Prover.ofProof π).run (checkAxisAt p i (List.ofFn fun k => (x k).val)) () =
      PMF.pure (checkAxis (proofPoint π p) (proofAxis π p) i x, ()) := by
  have hcan : (List.ofFn fun k => ((Function.update x i 0) k).val).set i 0 =
      (List.ofFn fun k => (x k).val).set i 0 := by
    rw [List.set_ofFn, List.set_ofFn]
    congr 1
    funext j
    by_cases h : j = i <;> simp [Function.update_apply, h]
  simp only [checkAxisAt, Prover.run_bind, ProofWord.run_readValues, PMF.pure_bind,
    Prover.run_pure, List.getD_ofFn]
  congr 2
  unfold checkValues checkAxis proofPoint proofAxis
  simp only [axisKeys, List.map_cons, List.map_nil, List.getD_cons_succ, List.getD_cons_zero,
    axisTableKey, hcan]
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, ← ZMod.natCast_eq_natCast_iff', Nat.cast_add, Nat.cast_mul,
    ZMod.natCast_zmod_val]

private theorem checkValues_polyTime {α : Type} {enc : α ↪ List Bool}
    {p x : α → ℕ} {values : α → List ℕ} (hp : ComputableInPolyTime p enc encNat)
    (hx : ComputableInPolyTime x enc encNat)
    (hv : ComputableInPolyTime values enc (encList encNat)) :
    ComputableInPolyTime (fun a => checkValues (p a) (x a) (values a)) enc encBool := by
  have get (k : ℕ) : ComputableInPolyTime (fun a => (values a).getD k 0) enc encNat :=
    (ComputableInPolyTime.listGetD 0).comp (hv.prod (.const k))
  exact ComputableInPolyTime.decide_eq'
    (.binary_mod' (.binary_add' (.binary_mul' (get 1) hx) (get 2)) hp)
    (.binary_mod' (get 0) hp)

/-- The axis check is a strict polynomial-time verifier for unary moduli, coordinates and axes. -/
theorem isOraclePPTOn_checkAxisAt {α : Type} {enc : α ↪ List Bool}
    {p i : α → ℕ} {point : α → List ℕ} (hp : ComputableInPolyTime p enc encUnary)
    (hi : ComputableInPolyTime i enc encUnary)
    (hpoint : ComputableInPolyTime point enc (encList encUnary)) :
    IsOraclePPTOn enc encBool (fun a => checkAxisAt (p a) (i a) (point a)) := by
  have hpointKey : ComputableInPolyTime (fun a => pointTableKey (point a)) enc encBits :=
    .bitsCons (.const _) (.encoding_comp hpoint)
  have hbase := ComputableInPolyTime.listSetWithInput encUnary hpoint hi (.const 0)
  have hlineKey (b : Bool) :
      ComputableInPolyTime (fun a => axisTableKey b (i a) (point a)) enc encBits :=
    .bitsCons (.const _) (.bitsCons (.const _) (.encoding_comp
      ((ComputableInPolyTime.const b).prod (hi.prod hbase))))
  have hkeys : ComputableInPolyTime (fun a => axisKeys (i a) (point a)) enc (encList encBits) :=
    (ComputableInPolyTime.cons encBits).comp (hpointKey.prod
      ((ComputableInPolyTime.cons encBits).comp ((hlineKey true).prod
        ((ComputableInPolyTime.cons encBits).comp ((hlineKey false).prod (.const []))))))
  have hpb := ComputableInPolyTime.unary_to_binary.comp hp
  have hx := ComputableInPolyTime.unary_to_binary.comp
    ((ComputableInPolyTime.listGetD 0).comp (hpoint.prod hi))
  simpa only [checkAxisAt, bind_pure_comp, Function.comp_apply] using
    (ProofWord.isOraclePPTOn_readValues hkeys (ComputableInPolyTime.binary_size.comp hpb)).map_with
      (f := fun a values => checkValues (p a) ((point a).getD (i a) 0) values)
      (checkValues_polyTime (hpb.comp (.fst _ _)) (hx.comp (.fst _ _)) (.snd _ _))

private def decodePoint {n p : ℕ} (word : List ℕ) (i : Fin n) : ZMod p := word.getD i 0

private theorem decodePoint_vals {n p : ℕ} [NeZero p] (x : Fin n → ZMod p) :
    decodePoint (List.ofFn fun k => (x k).val) = x := by
  funext k
  simp [decodePoint]

private theorem decodePoint_set {n p : ℕ} [NeZero p] (x : Fin n → ZMod p) (i : Fin n) :
    decodePoint ((List.ofFn fun k => (x k).val).set i 0) = Function.update x i 0 := by
  rw [List.set_ofFn]
  funext j
  by_cases h : j = i <;> simp [decodePoint, h]

/-- Populate the point and axis tables for a given dimension and field. Other tags retain their
background values, permitting the same proof to store sumcheck and correction data. -/
noncomputable def extendAxisTable {n p : ℕ} (f : (Fin n → ZMod p) → ZMod p)
    (lines : Fin n → (Fin n → ZMod p) → LineAnswer (ZMod p)) (other : List Bool → ℕ) :
    List Bool → ℕ
  | false :: tail => Function.extend (encList encUnary)
      (fun point => (f (decodePoint point)).val) (fun _ => 0) tail
  | true :: false :: tail => Function.extend (encPair encBool (encPair encUnary (encList encUnary)))
      (fun ⟨slope, i, point⟩ => if h : i < n then
        let line := lines ⟨i, h⟩ (decodePoint point)
        (if slope then line.slope else line.intercept).val else 0) (fun _ => 0) tail
  | key => other key

/-- The `11` tag subspace can carry additional parts of the static proof. -/
theorem extendAxisTable_reserved {n p : ℕ} (f : (Fin n → ZMod p) → ZMod p)
    (lines : Fin n → (Fin n → ZMod p) → LineAnswer (ZMod p)) (other : List Bool → ℕ)
    (tail : List Bool) : extendAxisTable f lines other (true :: true :: tail) =
      other (true :: true :: tail) := by rfl

/-- Reading the two populated tables recovers their values. It suffices to represent the table
at its own tags and access width. The rest of the proof may answer arbitrarily. -/
private theorem proofTables_eq_of_extend {n p : ℕ} [NeZero p] (f : (Fin n → ZMod p) → ZMod p)
    (lines : Fin n → (Fin n → ZMod p) → LineAnswer (ZMod p)) (other : List Bool → ℕ)
    (π : List Bool → Bool)
    (hπ : ∀ key, key.take 2 ≠ [true, true] →
      ProofWord.value π key p.size = extendAxisTable f lines other key % 2 ^ p.size) :
    proofPoint π p = f ∧ ∀ i (x : Fin n → ZMod p),
      proofAxis π p i x = lines i (Function.update x i 0) := by
  have small (v : ZMod p) : v.val < 2 ^ p.size := (ZMod.val_lt _).trans (Nat.lt_size_self p)
  constructor
  · funext x
    unfold proofPoint
    rw [hπ _ (by simp [pointTableKey])]
    simp only [pointTableKey, extendAxisTable, (encList encUnary).injective.extend_apply,
      decodePoint_vals, Nat.mod_eq_of_lt (small _), ZMod.natCast_zmod_val]
  · intro i x
    have value (b : Bool) : ProofWord.value π
        (axisTableKey b i (List.ofFn fun k => (x k).val)) p.size =
        (if b then (lines i (Function.update x i 0)).slope
          else (lines i (Function.update x i 0)).intercept).val := by
      rw [hπ _ (by simp [axisTableKey])]
      simp only [axisTableKey, extendAxisTable,
        (encPair encBool (encPair encUnary (encList encUnary))).injective.extend_apply,
        dite_eq_left i.isLt, decodePoint_set, Nat.mod_eq_of_lt (small _)]
    simp only [proofAxis, value, ↓reduceIte, Bool.false_eq_true, ZMod.natCast_zmod_val]

open scoped ENNReal

/-- Use fair bits to sample both a direction and an `n`-dimensional field point. -/
private noncomputable def sampleAxisChallenge (n p precision : ℕ) : ProbComp (ℕ × List ℕ) := do
  let i ← OracleComp.replicate 1 (ProbComp.sampleModIndex (1 + n.size + precision) n)
  Prod.mk (i.headD 0) <$> OracleComp.replicate n
    (ProbComp.sampleModIndex (n.size + p.size + precision) p)

private theorem isPPTOn_sampleAxisChallenge {α : Type} {enc : α ↪ List Bool}
    {n p precision : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary)
    (hprec : ComputableInPolyTime precision enc encUnary) :
    IsPPTOn enc (encPair encUnary (encList encUnary))
      (fun a => sampleAxisChallenge (n a) (p a) (precision a)) := by
  have hsize {f : α → ℕ} (h : ComputableInPolyTime f enc encUnary) :
      ComputableInPolyTime (fun a => (f a).size) enc encUnary :=
    ComputableInPolyTime.binary_size.comp (ComputableInPolyTime.unary_to_binary.comp h)
  have hsn := hsize hn
  have hsp := hsize hp
  have hI : IsPPTOn enc (encList encUnary) (fun a => OracleComp.replicate 1
      (ProbComp.sampleModIndex (1 + (n a).size + precision a) (n a))) :=
    (isPPTOn_sampleModIndex (by fun_prop) hn).replicate (.const 1)
  have hX : IsPPTOn enc (encList encUnary) (fun a => OracleComp.replicate (n a)
      (ProbComp.sampleModIndex ((n a).size + (p a).size + precision a) (p a))) :=
    (isPPTOn_sampleModIndex (by fun_prop) hp).replicate hn
  unfold sampleAxisChallenge
  apply hI.bind_with (second := fun a l => (fun xs => (l.headD 0, xs)) <$> _)
  simpa only [Function.comp_apply] using
    (hX.preprocess (ComputableInPolyTime.fst enc (encList encUnary))).pair
      ((ComputableInPolyTime.headD 0).comp (ComputableInPolyTime.snd enc (encList encUnary)))

/-- The fair-bit samples deviate from the uniform axis and field point on any event
by at most two individual sampling errors. -/
private theorem closeTo_sampleAxisChallenge (n p precision : ℕ) [hzero : NeZero n] [NeZero p] :
    CloseTo ((PMF.uniformOfFintype (Fin n × (Fin n → ZMod p))).map fun (i, x) =>
      (i.val, List.ofFn fun j => (x j).val))
      (ProbComp.eval (sampleAxisChallenge n p precision))
      (1 / 2 ^ precision + 1 / 2 ^ precision) := by
  let e := (Equiv.funUnique (Fin 1) (ZMod n)).trans (ZMod.finEquiv n).symm.toEquiv
  have hi := (ProbComp.closeTo_replicate_sampleModIndex_precision 1 n precision).map
    (fun v => v.headD 0)
  have hf : ((PMF.uniformOfFintype (Fin 1 → ZMod n)).map
        (fun v => List.ofFn fun j => (v j).val)).map (fun v => v.headD 0) =
      (PMF.uniformOfFintype (Fin n)).map Fin.val := by
    rw [← PMF.uniformOfFintype_map_equiv e, _root_.PMF.map_comp, _root_.PMF.map_comp]
    congr 1
    funext v
    cases n with
    | zero => exact (NeZero.ne (0 : ℕ) rfl).elim
    | succ k => simp [e, Function.comp_def, List.ofFn_succ, Equiv.funUnique, ZMod.finEquiv]; rfl
  rw [hf] at hi
  have hx := ProbComp.closeTo_replicate_sampleModIndex_precision n p precision
  have joint := hi.bind (fun i _ => hx.map (Prod.mk i))
  convert joint using 1
  · rw [_root_.PMF.bind_map]
    simpa only [Function.comp_def, _root_.PMF.map_comp] using
      (PMF.uniformOfFintype_bind_map (fun (i : Fin n) (x : Fin n → ZMod p) =>
        (i.val, List.ofFn fun j => (x j).val))).symm
  · simp only [sampleAxisChallenge, ProbComp.eval_bind, ProbComp.eval_map, _root_.PMF.bind_map]
    rfl

/-- A strict oracle program for the point-versus-axis-line check over dyadic random coins. -/
noncomputable def axisRound (n p precision : ℕ) : WordOracleComp Unit Bool := do
  let challenge ← ProbOracleComp.sample (sampleAxisChallenge n p precision)
  checkAxisAt p challenge.1 challenge.2

theorem isOraclePPTOn_axisRound {α : Type} {enc : α ↪ List Bool}
    {n p precision : α → ℕ} (hn : ComputableInPolyTime n enc encUnary)
    (hp : ComputableInPolyTime p enc encUnary)
    (hprec : ComputableInPolyTime precision enc encUnary) :
    IsOraclePPTOn enc encBool (fun a => axisRound (n a) (p a) (precision a)) :=
  (isPPTOn_sampleAxisChallenge hn hp hprec).isOraclePPTOn.bind_with
    (isOraclePPTOn_checkAxisAt (hp.comp (.fst _ _)) ((ComputableInPolyTime.snd _ _).fst')
      ((ComputableInPolyTime.snd _ _).snd'))

/-- The distribution of the bounded-coin verifier on a fixed bit proof differs from the uniform
field test on the tables encoded by that very proof by at most the sampling error. -/
theorem closeTo_axisRound (π : List Bool → Bool) (n p precision : ℕ) [NeZero n] [Fact p.Prime] :
    CloseTo (uniformAxisCheck (n := n) (proofPoint π p) (proofAxis π p))
      (((Prover.ofProof π).run (axisRound n p precision) ()).map Prod.fst)
      (1 / 2 ^ precision + 1 / 2 ^ precision) := by
  let verdict (c : ℕ × List ℕ) : PMF Bool :=
    ((Prover.ofProof π).run (checkAxisAt p c.1 c.2) ()).map Prod.fst
  have h := (closeTo_sampleAxisChallenge n p precision).bind_left verdict
  convert h using 1
  · rw [_root_.PMF.bind_map]
    unfold uniformAxisCheck
    rw [← _root_.PMF.bind_pure_comp]
    congr 1
    funext ⟨i, x⟩
    change PMF.pure _ = ((Prover.ofProof π).run (checkAxisAt p i _) ()).map Prod.fst
    rw [run_checkAxisAt, _root_.PMF.pure_map]
  · simp only [axisRound, Prover.run_bind, Prover.run_sample, _root_.PMF.map_bind,
      _root_.PMF.bind_map]
    rfl

/-- A proof passing the strict verifier with low enough rejection encodes a point table
close to the evaluation table of an individual-degree-one polynomial. -/
theorem exists_assignment_of_axisRound (π : List Bool → Bool) {n p : ℕ}
    [NeZero n] [Fact p.Prime] (hq : 1000 * (n + 1) ^ 3 ≤ p) (precision : ℕ)
    (hrej : (((Prover.ofProof π).run (axisRound n p precision) ()).map Prod.fst false).toReal +
      2 / 2 ^ precision < 1 / (10 ^ 6 * (n + 1 : ℝ) ^ 7)) :
    ∃ A ∈ MvPolynomial.restrictDegree (Fin n) (ZMod p) 1,
      (hammingDist (proofPoint π p) (fun x => MvPolynomial.eval x A) : ℝ) <
        p ^ n / (100 * (n + 1)) := by
  have h := closeTo_axisRound π n p precision ({false} : Set Bool)
  rw [_root_.PMF.toOuterMeasure_apply_singleton, _root_.PMF.toOuterMeasure_apply_singleton] at h
  have he : (1 / 2 ^ precision : ENNReal) ≠ ⊤ := by finiteness
  have hm : ((Prover.ofProof π).run (axisRound n p precision) ()).map Prod.fst false ≠ ⊤ :=
    _root_.PMF.apply_ne_top _ _
  have h' := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hm, ENNReal.add_ne_top.mpr ⟨he, he⟩⟩) h
  simp only [ENNReal.toReal_add hm (ENNReal.add_ne_top.mpr ⟨he, he⟩), ENNReal.toReal_add he he,
    ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_pow, ENNReal.toReal_ofNat] at h'
  rw [← add_div, one_add_one_eq_two] at h'
  have hb := exists_assignment_of_checkAxis (proofPoint π p) (proofAxis π p)
    (n := n) (by simpa only [ZMod.card] using hq) (h'.trans_lt hrej)
  simpa only [ZMod.card] using hb

private theorem valid_of_mem_axisChallenge {n p precision : ℕ} [NeZero n] [NeZero p]
    {c : ℕ × List ℕ} (hc : c ∈ (ProbComp.eval (sampleAxisChallenge n p precision)).support) :
    ∃ (i : Fin n) (x : Fin n → ZMod p), c = (i.val, List.ofFn fun j => (x j).val) := by
  rw [sampleAxisChallenge, ProbComp.eval_bind, PMF.mem_support_bind_iff] at hc
  obtain ⟨inds, hinds, hx⟩ := hc
  rw [ProbComp.eval_map, PMF.mem_support_map_iff] at hx
  obtain ⟨xs, hxs, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := ProbComp.exists_vector_of_mem_support_replicate_sampleModIndex hinds
  obtain ⟨x, rfl⟩ := ProbComp.exists_vector_of_mem_support_replicate_sampleModIndex hxs
  exact ⟨⟨(v 0).val, ZMod.val_lt _⟩, x, by simp [List.ofFn_succ]⟩

/-- The verifier accepts with certainty whenever the represented point and line tables
agree on every axis and point, independently of the precision used for sampling. -/
private theorem run_axisRound_of_checkAxis (π : List Bool → Bool) {n p : ℕ}
    [NeZero n] [Fact p.Prime]
    (hall : ∀ (i : Fin n) (x : Fin n → ZMod p),
      checkAxis (proofPoint π p) (proofAxis π p) i x = true)
    (precision : ℕ) :
    (Prover.ofProof π).run (axisRound n p precision) () = PMF.pure (true, ()) := by
  simp only [axisRound, Prover.run_bind, Prover.run_sample, PMF.bind_map]
  refine Probability.PMF.bind_eq_pure_of_forall_mem_support fun c hc => ?_
  obtain ⟨i, x, rfl⟩ := valid_of_mem_axisChallenge hc
  change (Prover.ofProof π).run (checkAxisAt p i (List.ofFn fun j => (x j).val)) () = _
  rw [run_checkAxisAt, hall]

/-- Every multilinear assignment admits a fixed axis table whose encoded point values are
the polynomial evaluations and whose verifier accepts on every choice of fair coins.
The same bit proof can use the other tag addresses for the remaining verification phases. -/
theorem exists_axisTable_of_mem_restrictDegree {n p : ℕ} [NeZero n] [Fact p.Prime]
    {A : MvPolynomial (Fin n) (ZMod p)} (hA : A ∈ restrictDegree (Fin n) (ZMod p) 1) :
    ∃ lines, ∀ (other : List Bool → ℕ) (π : List Bool → Bool),
      (∀ key, key.take 2 ≠ [true, true] → ProofWord.value π key p.size =
        extendAxisTable (fun x => eval x A) lines other key % 2 ^ p.size) →
      proofPoint π p = (fun x => eval x A) ∧ ∀ precision,
        (Prover.ofProof π).run (axisRound n p precision) () = PMF.pure (true, ()) := by
  obtain ⟨lines, honest⟩ := exists_checkAxis_of_mem_restrictDegree hA
  refine ⟨lines, fun other π hπ => ?_⟩
  obtain ⟨hf, hl⟩ := proofTables_eq_of_extend (fun x => eval x A) lines other π hπ
  refine ⟨hf, run_axisRound_of_checkAxis π fun i x => ?_⟩
  simpa only [checkAxis, hf, hl, Function.update_idem] using! honest i x

end Cslib.Complexity.MIP
