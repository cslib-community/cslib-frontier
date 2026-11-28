/-
Copyright (c) 2026 Jonathan Katz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jonathan Katz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.CriticalPath
public import CslibFrontier.Crypto.Computational.PseudorandomFunction
public import CslibFrontier.Crypto.Computational.PseudorandomFunction.TruthTable
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Circuit.InnerSize
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Foundations.Data.BitString.List.LowBits
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.Uniform
import CslibFrontier.Probability.PMF.Finiteness
import CslibFrontier.Tactic.PPT
import CslibFrontier.Tactic.Negligible

/-!
# Unconditional `2n - 2` `B₂`-circuit size lower bound for pseudorandom functions

For every Boolean-output PRF ensemble, at all sufficiently large input lengths `n`, some
function in its support requires at least `2 * n - 2` gates. This gives the worst-case bound
of [FanLiYang2022, Theorem 7.5, p. 41] over the complete two-input Boolean basis `B₂`.
Definition 4.9 (p. 28) takes the maximum of the minimum gate counts over the collection `Fₙ`
supporting the distribution. A witness in the support belongs to every such collection.

The proof establishes the stronger distributional bound that the probability of sampling a
function below the threshold is negligible. The keyed corollaries apply this bound to the first
output bit of a word-valued PRF and then to circuits computing all its output bits.

## Proof architecture and design notes

* **Boolean PRF ensemble (`BooleanPRF`) and bridge from `PseudorandomFunction`**:
  Fan, Li, and Yang (Definitions 4.4–4.5) model a PRF as a sequence of distributions
  `D : ∀ n, PMF (BooleanFunction n)` on `1`-bit-output Boolean functions indistinguishable from
  `PMF.uniformOfFintype (BooleanFunction n)` by uniform oracle-PPT distinguishers. We define this
  model (`booleanOracle`, `booleanPRFRealGame`, `booleanPRFIdealGame`, `BooleanPRF`) and prove that
  projecting `Cslib.Crypto.PseudorandomFunction` (`{0, 1}^n × {0, 1}^n → {0, 1}^n`) to its first
  output bit yields a `BooleanPRF` (`PseudorandomFunction.booleanPRF`). Because designating output
  wires is gate-free in `Cslib.Circuits.Circuit`, the `2 * n - 2` lower bound transfers immediately
  both to the first-output-bit ensemble and to `n`-output `B₂` circuits computing the full keyed
  function.
* **Deterministic distinct restrictions via `BitString.lowBits`**:
  Instead of sampling random restrictions and bounding repeat-collision probabilities, both oracle
  distinguishers evaluate `n` deterministic distinct restrictions encoded by
  `BitString.lowBits (n - 1) t` (injective on `t < n` for `2 ≤ n`) and
  `BitString.lowBits (n - 2) t` (injective on `t < n` for `5 ≤ n`), issued in one batch through
  `KabanetsCai.queryTable`. For a uniformly random `f : BooleanFunction n`, surjective `GF(2)`
  linear projections (`PMF.uniformOfFintype_map_addHom`) show the `n` restricted subfunctions for
  any fixed variable or variable pair are i.i.d. uniform.
* **Isolated-variable distinguisher (Lemma 7.3)**:
  Note that Lemma 7.3's brief prose ("all `n` sampled restrictions give the same output") refers to
  each `(n - 1)`-bit restriction on `Fin n \ {x}` yielding a constant `1`-bit function
  `f (ρ[x := false]) = f (ρ[x := true])` (matching the isolated-variable collision pairs `I_n` in
  the proof of Theorem 7.6 in Section 7.2 of [FanLiYang2022]), which occurs with probability
  `(1 / 2) ^ n` per coordinate `x` against a random function and probability `1` when `x` is
  isolated.
* **Critical-path intersection distinguisher (Lemma 7.2)**:
  For each `x < y` in `Fin n`, `criticalPathDistinguisher` tests whether none of the `n` restricted
  `2`-bit functions on `(x, y)` is AND-type (`8 / 16 = 1 / 2` of `B₂` gates) or none is XOR-type
  (`2 / 16 = 1 / 8` of `B₂` gates, so `14 / 16 = 7 / 8` are non-XOR-type). By
  `not_isAndType_or_not_isXorType_of_not_disjoint_criticalPath`, intersecting critical paths force
  acceptance with probability `1`, whereas a uniform random function is accepted with probability at
  most `n ^ 2 * ((1 / 2) ^ n + (7 / 8) ^ n)`.

## Main definitions

* `Cslib.Crypto.booleanOracle`, `Cslib.Crypto.evalBooleanOracle`,
  `Cslib.Crypto.booleanPRFRealGame`, `Cslib.Crypto.booleanPRFIdealGame`, `Cslib.Crypto.BooleanPRF`:
  Boolean-output PRF ensembles ([FanLiYang2022], Definitions 4.4–4.5).
* `Cslib.Crypto.prfFirstBitEnsemble`, `Cslib.Crypto.firstBitDistinguisher`: first-output-bit
  ensemble and distinguisher adapter for a word-valued family.
* `Cslib.Crypto.isolatedVarDistinguisher`: oracle-PPT distinguisher for functions with an isolated
  coordinate ([FanLiYang2022], Lemma 7.3).
* `Cslib.Crypto.criticalPathDistinguisher`: oracle-PPT distinguisher for functions whose
  `NoDeadGates` `B₂` circuit has intersecting critical paths ([FanLiYang2022], Lemma 7.2).

## Main results

* `Cslib.Crypto.isOraclePPT_firstBitDistinguisher`,
  `Cslib.Crypto.booleanPRFRealGame_prfFirstBitEnsemble_eq`,
  `Cslib.Crypto.booleanPRFIdealGame_eq_prfIdealGame`,
  `Cslib.Crypto.PseudorandomFunction.booleanPRF`: a word-valued `PseudorandomFunction` induces a
  `BooleanPRF` on its first output bit.
* `Cslib.Crypto.isOraclePPT_isolatedVarDistinguisher`,
  `Cslib.Crypto.succProbability_isolatedVarDistinguisher_of_hasIsolatedVar`,
  `Cslib.Crypto.succProbability_booleanPRFIdealGame_isolatedVarDistinguisher_le`,
  `Cslib.Crypto.negligible_booleanPRFIdealGame_isolatedVarDistinguisher`: Lemma 7.3.
* `Cslib.Crypto.isOraclePPT_criticalPathDistinguisher`,
  `Cslib.Crypto.succProbability_criticalPathDistinguisher_of_not_disjoint_criticalPath`,
  `Cslib.Crypto.succProbability_booleanPRFIdealGame_criticalPathDistinguisher_le`,
  `Cslib.Crypto.negligible_booleanPRFIdealGame_criticalPathDistinguisher`: Lemma 7.2.
* `Cslib.Crypto.BooleanPRF.eventually_exists_mem_support_two_mul_sub_two_le_complexity`:
  the eventual worst-case gate lower bound of [FanLiYang2022, Theorem 7.5].
* `Cslib.Crypto.BooleanPRF.negligible_complexity_lt_two_mul_sub_two`: the probability of sampling
  a function below this bound is negligible.
* `Cslib.Crypto.PseudorandomFunction.negligible_complexity_restriction_lt_two_mul_sub_two`,
  `Cslib.Crypto.PseudorandomFunction.negligible_complexity_lt_two_mul_sub_two`,
  `Cslib.Crypto.PseudorandomFunction.eventually_exists_key_two_mul_sub_two_le_complexity`:
  keyed corollaries for the first output bit and the full word-valued function.

## References

* [Z. Fan, J. Li, and T. Yang, *The Exact Complexity of Pseudorandom Functions and the Black-Box
  Natural Proof Barrier for Bootstrapping Results in Computational Complexity*][FanLiYang2022],
  ECCC TR21-125, Revision 1, §§4.1–4.2, 4.4 and 7.1.
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM Circuits Circuits.Boolean
open scoped BigOperators ENNReal NNReal

/-! ### Boolean-output PRF ensembles and first-bit reduction -/

/-- A deterministic word-channel oracle exposing `f : BooleanFunction n` on `n`-bit queries and
returning `[]` on malformed queries. -/
@[expose] def booleanOracle (n : ℕ) (f : BooleanFunction n) (query : List Bool) : List Bool :=
  if query.length = n then [f (BitString.ofList n query)] else []

/-- Run an `OracleDistinguisher` against a fixed `f : BooleanFunction n` at parameter `n`. -/
@[expose] noncomputable def evalBooleanOracle (adversary : OracleDistinguisher) (n : ℕ)
    (f : BooleanFunction n) : Game :=
  ProbComp.eval ((adversary n []).run fun request => pure (booleanOracle n f request.2))

/-- Real security game for a Boolean PRF ensemble `D : ∀ n, PMF (BooleanFunction n)`. -/
@[expose] noncomputable def booleanPRFRealGame (D : ∀ n, PMF (BooleanFunction n))
    (adversary : OracleDistinguisher) (n : ℕ) : Game :=
  (D n).bind (evalBooleanOracle adversary n)

/-- Ideal security game for a Boolean PRF: sample `f` uniformly from `BooleanFunction n`. -/
@[expose] noncomputable def booleanPRFIdealGame (adversary : OracleDistinguisher) (n : ℕ) : Game :=
  (PMF.uniformOfFintype (BooleanFunction n)).bind (evalBooleanOracle adversary n)

/-- A Boolean-output PRF ensemble [FanLiYang2022, Definitions 4.4–4.5, pp. 26–27]. Every uniform
strict oracle-PPT adversary on unary parameter `n` has negligible distinguishing advantage between
a single function drawn from `D n` and a uniform Boolean function on `n` bits. The source takes
`n ≥ 1`. Here `n = 0` is immaterial to negligibility, and both word oracles return `[]` on queries
of other lengths. The distribution and its functions may be inefficient to sample and evaluate.
In particular, the uniform function ensemble satisfies this condition. -/
@[expose] def BooleanPRF (D : ∀ n, PMF (BooleanFunction n)) : Prop :=
  Game.Indistinguishable (booleanPRFRealGame D) booleanPRFIdealGame (IsOraclePPT encBool)

/-- The Boolean function ensemble obtained from a keyed word family by sampling a uniform `n`-bit
key and reading the first output bit on `n`-bit inputs. -/
@[expose] noncomputable def prfFirstBitEnsemble (family : List Bool → List Bool → List Bool)
    (n : ℕ) : PMF (BooleanFunction n) :=
  (BitString.uniformList n).map fun key => KabanetsCai.restriction (family key) n n

/-- Forward a single-channel query and truncate the oracle's reply to at most `1` bit. -/
private def firstBitQuery (request : Unit × List Bool) : WordOracleComp Unit (List Bool) :=
  List.take 1 <$> ProbOracleComp.query ((), request.2)

/-- Convert an adversary expecting `1`-bit oracle replies into an adversary against an `n`-bit PRF
oracle by truncating every oracle reply to its first bit. -/
def firstBitDistinguisher (adversary : OracleDistinguisher) : OracleDistinguisher :=
  fun n aux =>
    OracleComp.interpret
      (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) firstBitQuery)
      (adversary n aux)

private theorem interpret_firstBitDistinguisher (oracle : Unit × List Bool → ProbComp (List Bool))
    (adversary : OracleDistinguisher) (n : ℕ) (aux : List Bool) :
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin oracle)
      (firstBitDistinguisher adversary n aux) =
    OracleComp.interpret (OracleComp.sumHandler ProbComp.unifFin (fun request =>
      List.take 1 <$> oracle ((), request.2))) (adversary n aux) := by
  simp only [firstBitDistinguisher, OracleComp.interpret_interpret,
    OracleComp.interpret_sumHandler, ProbOracleComp.interpret_sample, firstBitQuery,
    OracleComp.interpret_map, ProbOracleComp.interpret_query]
  congr 1

/-- Truncating every oracle reply to `1` bit preserves uniform strict oracle-PPT admissibility. -/
theorem isOraclePPT_firstBitDistinguisher {adversary : OracleDistinguisher}
    (hadversary : IsOraclePPT encBool adversary) :
    IsOraclePPT encBool (firstBitDistinguisher adversary) :=
  (hadversary.on.interpret_preprocess_open' (operationEncoding := encFinEnum Unit)
    (handler := fun _ => firstBitQuery) (prepare := id) (resources := fun _ _ => 1)
    ComputableInPolyTime.id' (by ppt [firstBitQuery]) (ComputableInPolyTime.const 1)
    fun _ _ _ hreply => by
      obtain ⟨raw, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hreply
      exact List.length_take_le _ _).isOraclePPT

private theorem evalBooleanOracle_eq_run_firstBit (adversary : OracleDistinguisher) {n : ℕ}
    {f : BooleanFunction n} (oracle : List Bool → List Bool)
    (hagree : ∀ q, booleanOracle n f q = (oracle q).take 1) :
    evalBooleanOracle adversary n f =
      ProbComp.eval ((firstBitDistinguisher adversary n []).run
        fun request => pure (oracle request.2)) := by
  unfold evalBooleanOracle ProbOracleComp.run
  rw [interpret_firstBitDistinguisher]
  refine congrArg (fun h => ProbComp.eval (OracleComp.interpret
    (OracleComp.sumHandler ProbComp.unifFin h) (adversary n []))) (funext fun request => ?_)
  simp only [map_pure, hagree]

/-- For `0 < n`, the real `BooleanPRF` game on `prfFirstBitEnsemble family` agrees with the real
`PseudorandomFunction` game of `firstBitDistinguisher adversary`. -/
theorem booleanPRFRealGame_prfFirstBitEnsemble_eq {family : List Bool → List Bool → List Bool}
    (hlen : ∀ key query, query.length = key.length → (family key query).length = key.length)
    (adversary : OracleDistinguisher) {n : ℕ} (hn : 0 < n) :
    booleanPRFRealGame (prfFirstBitEnsemble family) adversary n =
      ProbComp.eval (prfRealGame id family (firstBitDistinguisher adversary) n) := by
  simp only [booleanPRFRealGame, prfFirstBitEnsemble, PMF.bind_map, prfRealGame, id_eq,
    ProbOracleComp.run, ProbComp.eval_bind, BitString.eval_sampleList]
  refine PMF.bind_congr_on_support _ _ _ fun key hkey => ?_
  have hklen := BitString.length_of_mem_support_uniformList hkey
  refine evalBooleanOracle_eq_run_firstBit adversary (prfOracle family n key) fun q => ?_
  by_cases hq : q.length = n
  · simp only [booleanOracle, hq, ↓reduceIte, KabanetsCai.restriction, Nat.sub_self,
      List.replicate_zero, List.nil_append, BitString.ofFn_ofList hq, prfOracle]
    have hout : (family key q).length = n := hklen ▸ hlen key q (hq.trans hklen.symm)
    cases hfam : family key q <;> simp_all
  · simp only [booleanOracle, prfOracle, hq, ↓reduceIte, List.take_nil]

/-- For `0 < n`, the ideal `BooleanPRF` game agrees with the ideal `PseudorandomFunction` game of
`firstBitDistinguisher adversary`. -/
theorem booleanPRFIdealGame_eq_prfIdealGame (adversary : OracleDistinguisher) {n : ℕ}
    (hn : 0 < n) :
    booleanPRFIdealGame adversary n =
      ProbComp.eval (prfIdealGame id id (firstBitDistinguisher adversary) n) := by
  rw [booleanPRFIdealGame, ← KabanetsCai.uniformOfFintype_map_restrictTable hn le_rfl,
    PMF.bind_map]
  simp only [prfIdealGame, id_eq, ProbComp.eval_bind, ProbComp.eval_uniform]
  refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
  refine evalBooleanOracle_eq_run_firstBit adversary (randomFunctionOracle n table) fun q => ?_
  by_cases hq : q.length = n
  · simp only [booleanOracle, hq, ↓reduceIte, KabanetsCai.restrictTable, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, Nat.sub_self, List.replicate_zero, List.nil_append, BitString.ofList_ofFn,
      randomFunctionOracle]
    obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
    simp only [List.ofFn_succ, List.take_succ_cons, List.take_zero]
    rfl
  · simp only [booleanOracle, randomFunctionOracle, hq, ↓reduceIte, List.take_nil]

/-- **First-bit projection of a PRF is a `BooleanPRF`**: any `PseudorandomFunction` induces a
`BooleanPRF` via its first output bit on `n`-bit inputs. -/
theorem PseudorandomFunction.booleanPRF {family : List Bool → List Bool → List Bool}
    (hF : PseudorandomFunction family) : BooleanPRF (prfFirstBitEnsemble family) := by
  intro adversary hadversary
  have hsec := hF.secure (firstBitDistinguisher adversary)
    (isOraclePPT_firstBitDistinguisher hadversary)
  refine negligible_of_eventually_le hsec ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [booleanPRFRealGame_prfFirstBitEnsemble_eq hF.length_eq adversary hn,
    booleanPRFIdealGame_eq_prfIdealGame adversary hn]

/-! ### Bit-splicing and deterministic distinct restrictions -/

/-- Insert bit `b` at position `i` of `w` (`w.take i ++ b :: w.drop i`). -/
private def insertBitAt (w : List Bool) (i : ℕ) (b : Bool) : List Bool :=
  w.take i ++ b :: w.drop i

@[simp]
private theorem length_insertBitAt (w : List Bool) (i : ℕ) (b : Bool) :
    (insertBitAt w i b).length = w.length + 1 := by
  simp only [insertBitAt, List.length_append, List.length_take, List.length_cons, List.length_drop]
  omega

private theorem insertBitAt_inj {w₁ w₂ : List Bool} {i : ℕ} {b₁ b₂ : Bool}
    (hi₁ : i ≤ w₁.length) (hi₂ : i ≤ w₂.length)
    (h : insertBitAt w₁ i b₁ = insertBitAt w₂ i b₂) :
    w₁ = w₂ ∧ b₁ = b₂ := by
  have hlen : (w₁.take i).length = (w₂.take i).length := by
    simp only [List.length_take]
    omega
  obtain ⟨htake, hcons⟩ := List.append_inj h hlen
  injection hcons with hb hdrop
  refine ⟨?_, hb⟩
  rw [← List.take_append_drop i w₁, ← List.take_append_drop i w₂, htake, hdrop]

private theorem getD_insertBitAt_eq {w : List Bool} {i : ℕ} (hi : i ≤ w.length) (b : Bool) :
    (insertBitAt w i b).getD i false = b := by
  have hlen : (w.take i).length = i := List.length_take_of_le hi
  simp only [insertBitAt, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega : (w.take i).length ≤ i), hlen, Nat.sub_self,
    List.getElem?_cons_zero, Option.getD_some]

private theorem getD_insertBitAt_of_lt {w : List Bool} {k i : ℕ} (hk : k < i) (hi : i ≤ w.length)
    (b : Bool) :
    (insertBitAt w i b).getD k false = w.getD k false := by
  have hlen : (w.take i).length = i := List.length_take_of_le hi
  simp only [insertBitAt, List.getD_eq_getElem?_getD,
    List.getElem?_append_left (by omega : k < (w.take i).length),
    List.getElem?_take_of_lt hk]

private theorem getD_insertBitAt_of_gt {w : List Bool} {k i : ℕ} (hi : i ≤ w.length) (hk : i < k)
    (b : Bool) :
    (insertBitAt w i b).getD k false = w.getD (k - 1) false := by
  have hlen : (w.take i).length = i := List.length_take_of_le hi
  obtain ⟨d, rfl⟩ : ∃ d, k = i + 1 + d := ⟨k - i - 1, by omega⟩
  simp only [insertBitAt, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by omega : (w.take i).length ≤ i + 1 + d), hlen,
    show i + 1 + d - i = d + 1 by omega, List.getElem?_cons_succ, List.getElem?_drop,
    show i + d = i + 1 + d - 1 by omega]

private theorem getD_insertBitAt_ne {w : List Bool} {k i : ℕ} (hi : i ≤ w.length) (hne : k ≠ i)
    (b b' : Bool) :
    (insertBitAt w i b).getD k false = (insertBitAt w i b').getD k false := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · rw [getD_insertBitAt_of_lt hlt hi, getD_insertBitAt_of_lt hlt hi]
  · rw [getD_insertBitAt_of_gt hi hgt, getD_insertBitAt_of_gt hi hgt]

private theorem ofList_insertBitAt {n : ℕ} {w : List Bool} (hw : w.length = n - 1) (x : Fin n)
    (b : Bool) :
    BitString.ofList n (insertBitAt w x.val b) =
      Function.update (BitString.ofList n (insertBitAt w x.val false)) x b := by
  have hxle : x.val ≤ w.length := by omega
  funext j
  by_cases hj : j = x
  · subst hj; simp only [BitString.ofList, Function.update_self, getD_insertBitAt_eq hxle]
  · simp only [Function.update_of_ne hj, BitString.ofList]
    exact getD_insertBitAt_ne hxle (Fin.val_ne_of_ne hj) b false

private theorem le_two_pow_sub_one {n : ℕ} (hn : 2 ≤ n) : n ≤ 2 ^ (n - 1) := by
  have := Nat.lt_two_pow_self (n := n - 1)
  omega

private theorem le_two_pow_sub_two {n : ℕ} (hn : 5 ≤ n) : n ≤ 2 ^ (n - 2) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  clear hn
  induction k with
  | zero => decide
  | succ k ih =>
    rw [show k + 5 - 2 = k + 3 by omega] at ih
    rw [show k + 1 + 5 - 2 = k + 3 + 1 by omega, Nat.pow_succ]
    omega

/-- Splicing one bit `b` at coordinate `x` into the `(n - 1)`-bit restriction `t`. -/
private def spliceOne (n x t : ℕ) (b : Bool) : List Bool :=
  insertBitAt (BitString.lowBits (n - 1) t) x b

@[simp]
private theorem length_spliceOne {n : ℕ} (hn : 1 ≤ n) (x t : ℕ) (b : Bool) :
    (spliceOne n x t b).length = n := by
  simp only [spliceOne, length_insertBitAt, BitString.length_lowBits]
  omega

private theorem ofList_spliceOne {n : ℕ} (x : Fin n) (t : ℕ) (b : Bool) :
    BitString.ofList n (spliceOne n x.val t b) =
      Function.update (BitString.ofList n (spliceOne n x.val t false)) x b :=
  ofList_insertBitAt (BitString.length_lowBits (n - 1) t) x b

private theorem ofList_spliceOne_injective {n : ℕ} (hn : 2 ≤ n) (x : Fin n) :
    Function.Injective fun p : Fin n × Bool =>
      BitString.ofList n (spliceOne n x.val p.1.val p.2) := by
  rintro ⟨t₁, b₁⟩ ⟨t₂, b₂⟩ h
  have hlist := congrArg List.ofFn h
  rw [BitString.ofFn_ofList (length_spliceOne (by omega) _ _ _),
    BitString.ofFn_ofList (length_spliceOne (by omega) _ _ _)] at hlist
  dsimp only [spliceOne] at hlist
  have hxle : ∀ t : ℕ, x.val ≤ (BitString.lowBits (n - 1) t).length := by
    intro t
    simp only [BitString.length_lowBits]
    omega
  obtain ⟨hlow, rfl⟩ := insertBitAt_inj (hxle t₁.val) (hxle t₂.val) hlist
  have hpow := le_two_pow_sub_one hn
  have ht := BitString.lowBits_injective_of_lt (t₁.isLt.trans_le hpow) (t₂.isLt.trans_le hpow) hlow
  exact Prod.ext (Fin.ext ht) rfl

/-- Splicing bits `bx, by_` at coordinates `x < y` into the `(n - 2)`-bit restriction `t`. -/
private def spliceTwo (n x y t : ℕ) (bx by_ : Bool) : List Bool :=
  insertBitAt (insertBitAt (BitString.lowBits (n - 2) t) x bx) y by_

@[simp]
private theorem length_spliceTwo {n : ℕ} (hn : 2 ≤ n) (x y t : ℕ) (bx by_ : Bool) :
    (spliceTwo n x y t bx by_).length = n := by
  simp only [spliceTwo, length_insertBitAt, BitString.length_lowBits]
  omega

private theorem ofList_spliceTwo {n : ℕ} {x y : Fin n} (hxy : x < y) (t : ℕ) (bx by_ : Bool) :
    BitString.ofList n (spliceTwo n x.val y.val t bx by_) =
      Function.update (Function.update
        (BitString.ofList n (spliceTwo n x.val y.val t false false)) x bx) y by_ := by
  have hxle : x.val ≤ (BitString.lowBits (n - 2) t).length := by
    simp only [BitString.length_lowBits]; omega
  have hyle (b : Bool) : y.val ≤ (insertBitAt (BitString.lowBits (n - 2) t) x.val b).length := by
    simp only [length_insertBitAt, BitString.length_lowBits]; omega
  funext j
  by_cases hjy : j = y
  · subst hjy
    simp only [Function.update_self, BitString.ofList, spliceTwo, getD_insertBitAt_eq (hyle bx)]
  · simp only [Function.update_of_ne hjy]
    by_cases hjx : j = x
    · subst hjx
      simp only [Function.update_self, BitString.ofList, spliceTwo,
        getD_insertBitAt_of_lt hxy (hyle bx), getD_insertBitAt_eq hxle]
    · simp only [Function.update_of_ne hjx, BitString.ofList, spliceTwo]
      rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hjy) with hlty | hgty
      · rw [getD_insertBitAt_of_lt hlty (hyle bx), getD_insertBitAt_of_lt hlty (hyle false)]
        exact getD_insertBitAt_ne hxle (Fin.val_ne_of_ne hjx) bx false
      · rw [getD_insertBitAt_of_gt (hyle bx) hgty, getD_insertBitAt_of_gt (hyle false) hgty]
        exact getD_insertBitAt_ne hxle (by have : x.val < y.val := hxy; omega) bx false

private theorem ofList_spliceTwo_injective {n : ℕ} (hn : 5 ≤ n) {x y : Fin n} (hxy : x < y) :
    Function.Injective fun p : Fin n × Bool × Bool =>
      BitString.ofList n (spliceTwo n x.val y.val p.1.val p.2.1 p.2.2) := by
  rintro ⟨t₁, bx₁, by₁⟩ ⟨t₂, bx₂, by₂⟩ h
  have hlist := congrArg List.ofFn h
  rw [BitString.ofFn_ofList (length_spliceTwo (by omega) _ _ _ _ _),
    BitString.ofFn_ofList (length_spliceTwo (by omega) _ _ _ _ _)] at hlist
  have hlowLen : ∀ t : ℕ, x.val ≤ (BitString.lowBits (n - 2) t).length := fun t => by
    simp only [BitString.length_lowBits]; have : x.val < y.val := hxy; omega
  have hmidLen : ∀ t b, y.val ≤ (insertBitAt (BitString.lowBits (n - 2) t) x.val b).length :=
    fun t b => by simp only [length_insertBitAt, BitString.length_lowBits]; omega
  obtain ⟨hmid, rfl⟩ := insertBitAt_inj (hmidLen t₁.val bx₁) (hmidLen t₂.val bx₂) hlist
  obtain ⟨hlow, rfl⟩ := insertBitAt_inj (hlowLen t₁.val) (hlowLen t₂.val) hmid
  have hpow := le_two_pow_sub_two hn
  exact Prod.ext (Fin.ext (BitString.lowBits_injective_of_lt
    (t₁.isLt.trans_le hpow) (t₂.isLt.trans_le hpow) hlow)) rfl

/-! ### Polynomial-time certificates and uniform finite-probability helpers -/

private theorem bitsLowUnary {α : Type} {input : α ↪ List Bool} {width value : α → ℕ}
    (hwidth : ComputableInPolyTime width input encUnary)
    (hvalue : ComputableInPolyTime value input encUnary) :
    ComputableInPolyTime (fun a => BitString.lowBits (width a) (value a)) input encBits :=
  ComputableInPolyTime.bitsLow hwidth (ComputableInPolyTime.unary_to_binary.comp' hvalue)

private theorem insertBitAt_poly {α : Type} {input : α ↪ List Bool}
    {w : α → List Bool} {i : α → ℕ} {b : α → Bool}
    (hw : ComputableInPolyTime w input encBits)
    (hi : ComputableInPolyTime i input encUnary)
    (hb : ComputableInPolyTime b input encBool) :
    ComputableInPolyTime (fun a => insertBitAt (w a) (i a) (b a)) input encBits :=
  ComputableInPolyTime.bitsAppend
    (ComputableInPolyTime.bitsTakeWithInput hw hi)
    (ComputableInPolyTime.bitsCons hb
      (ComputableInPolyTime.bitsDropWithInput hw hi))

private theorem spliceOne_poly {α : Type} {input : α ↪ List Bool}
    {n x t : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hx : ComputableInPolyTime x input encUnary)
    (ht : ComputableInPolyTime t input encUnary) (b : Bool) :
    ComputableInPolyTime (fun a => spliceOne (n a) (x a) (t a) b) input encBits :=
  insertBitAt_poly (bitsLowUnary (hn.unary_sub' (.const 1)) ht) hx (.const b)

private theorem spliceTwo_poly {α : Type} {input : α ↪ List Bool}
    {n x y t : α → ℕ} (hn : ComputableInPolyTime n input encUnary)
    (hx : ComputableInPolyTime x input encUnary)
    (hy : ComputableInPolyTime y input encUnary)
    (ht : ComputableInPolyTime t input encUnary) (bx by_ : Bool) :
    ComputableInPolyTime (fun a => spliceTwo (n a) (x a) (y a) (t a) bx by_) input encBits :=
  insertBitAt_poly
    (insertBitAt_poly (bitsLowUnary (hn.unary_sub' (.const 2)) ht) hx (.const bx))
    hy (.const by_)

private theorem uniformOfFintype_exists_le {α ι : Type*} [Fintype α] [Nonempty α] [Fintype ι]
    (P : ι → α → Bool) [DecidablePred fun a => ∃ i, P i a = true] :
    ((PMF.uniformOfFintype α).map (fun a => decide (∃ i, P i a = true)) true).toNNReal ≤
      ∑ i : ι, ((PMF.uniformOfFintype α).map (fun a => P i a) true).toNNReal := by
  have h := ENNReal.toNNReal_mono (by finiteness)
    (PMF.map_true_le_sum (PMF.uniformOfFintype α) Finset.univ
      (E := fun a => decide (∃ i, P i a = true)) (F := P) fun a _ ha => by
        obtain ⟨i, hi⟩ := of_decide_eq_true ha
        exact ⟨i, Finset.mem_univ i, hi⟩)
  rwa [ENNReal.toNNReal_sum fun i _ => PMF.apply_ne_top _ _] at h

private theorem uniformOfFintype_hom_forall_fin_eq {α β : Type*} [AddGroup α] [Fintype α]
    [AddGroup β] [Fintype β] {n : ℕ} (hom : α →+ Fin n → β)
    (hs : Function.Surjective hom) (q : β → Bool) (c : ℕ)
    (hc : (Finset.univ.filter fun b : β => q b = true).card = c) :
    ((PMF.uniformOfFintype α).map
      (fun f => decide (∀ t : Fin n, q (hom f t) = true)) true).toNNReal =
      ((c : ℝ≥0) / Fintype.card β) ^ n := by
  classical
  have hcomp : (fun f : α => decide (∀ t : Fin n, q (hom f t) = true)) =
      (fun T : Fin n → β => decide (∀ t : Fin n, q (T t) = true)) ∘ hom := rfl
  rw [hcomp, ← _root_.PMF.map_comp, PMF.uniformOfFintype_map_addHom hom hs,
    PMF.uniformOfFintype_map_apply, ENNReal.toNNReal_div, ENNReal.toNNReal_natCast,
    ENNReal.toNNReal_natCast]
  have hequiv : {T : Fin n → β // decide (∀ t : Fin n, q (T t) = true) = true} ≃
      (Fin n → {b : β // q b = true}) :=
    (Equiv.subtypeEquivRight (fun _ => decide_eq_true_iff)).trans
      (Equiv.subtypePiEquivPi (β := fun _ : Fin n => β) (p := fun _ b => q b = true))
  rw [Nat.card_congr hequiv, Nat.card_eq_fintype_card, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_subtype, hc, Fintype.card_fun, Fintype.card_fin]
  push_cast
  rw [div_pow]

private theorem listRow_range_flatMap {n w : ℕ} (f : ℕ → List Bool)
    (hf : ∀ i < n, (f i).length = w) {i : ℕ} (hi : i < n) :
    BitString.listRow w i ((List.range n).flatMap f) = f i := by
  have hrow := BitString.listRow_flatMap_append (width := w) f (List.range n)
    (fun k hk => hf k (List.mem_range.mp hk)) [] i (by simpa only [List.length_range])
  simpa only [List.append_nil, List.getElem_range] using hrow

/-! ### Lemma 7.3: Distinguishing isolated variables -/

/-- The `2 * n ^ 2` deterministic query words used by `isolatedVarDistinguisher`. -/
private def isoQueries (n : ℕ) : List (List Bool) :=
  (List.range n).flatMap fun x =>
    (List.range n).flatMap fun t =>
      [spliceOne n x t false, spliceOne n x t true]

private def rowEq2 (rx : List Bool) (t : ℕ) : Bool :=
  (BitString.listRow 2 t rx).getD 0 false == (BitString.listRow 2 t rx).getD 1 false

/-- Check whether some coordinate `x < n` gives equal answers across all `n` restrictions. -/
private def checkIsoAnswers (n : ℕ) (answers : List Bool) : Bool :=
  (List.range n).any fun x =>
    (List.range n).all fun t =>
      rowEq2 (BitString.listRow (2 * n) x answers) t

/-- **Fan–Li–Yang Lemma 7.3 distinguisher**: query `2 * n ^ 2` deterministic restrictions via
`KabanetsCai.queryTable` and accept if some coordinate `x` is insensitive on all `n`
restrictions. -/
def isolatedVarDistinguisher : OracleDistinguisher :=
  fun n _ => checkIsoAnswers n <$> KabanetsCai.queryTable (isoQueries n)

private theorem computableInPolyTime_isoQueries :
    ComputableInPolyTime (fun p : ℕ × List Bool => isoQueries p.1)
      (encPair encUnary encBits) (encList encBits) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 encUnary
  let hn0 := ComputableInPolyTime.fst encUnary encBits
  let hn1 := (ComputableInPolyTime.fst E0 encUnary).fst'
  let hp2 := ComputableInPolyTime.fst E1 encUnary
  exact ComputableInPolyTime.flatMapWithInput hn0.unary_range'
    (ComputableInPolyTime.flatMapWithInput hn1.unary_range'
      ((spliceOne_poly hp2.fst'.fst' hp2.snd' (ComputableInPolyTime.snd E1 encUnary) false).cons'
        ((spliceOne_poly hp2.fst'.fst' hp2.snd' (ComputableInPolyTime.snd E1 encUnary) true).cons'
          (.const []))))

private theorem computableInPolyTime_rowEq2 :
    ComputableInPolyTime (fun p : List Bool × ℕ => rowEq2 p.1 p.2)
      (encPair encBits encUnary) encBool :=
  let hrow := ComputableInPolyTime.bitsRowWithInput (.const 2)
    (ComputableInPolyTime.snd encBits encUnary) (ComputableInPolyTime.fst encBits encUnary)
  (ComputableInPolyTime.bitsGetDWithInput hrow (.const 0) false).beq
    (ComputableInPolyTime.bitsGetDWithInput hrow (.const 1) false)

private theorem computableInPolyTime_checkIsoAnswers :
    ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => checkIsoAnswers p.1.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool := by
  let E0 := encPair (encPair encUnary encBits) encBits
  let hp1 := ComputableInPolyTime.fst E0 encUnary
  let hn1 := hp1.fst'.fst'
  exact ComputableInPolyTime.anyWithInput
    (ComputableInPolyTime.fst (encPair encUnary encBits) encBits).fst'.unary_range'
    (ComputableInPolyTime.allWithEncoding computableInPolyTime_rowEq2
      (ComputableInPolyTime.bitsRowWithInput
        ((ComputableInPolyTime.const 2).unary_mul' hn1)
        (ComputableInPolyTime.snd E0 encUnary) hp1.snd')
      hn1.unary_range')

/-- `isolatedVarDistinguisher` is a uniform strict oracle-PPT adversary. -/
theorem isOraclePPT_isolatedVarDistinguisher : IsOraclePPT encBool isolatedVarDistinguisher := by
  have hq := computableInPolyTime_isoQueries
  have hc := computableInPolyTime_checkIsoAnswers
  ppt [isolatedVarDistinguisher]

private theorem evalBooleanOracle_isolatedVarDistinguisher (n : ℕ) (f : BooleanFunction n) :
    evalBooleanOracle isolatedVarDistinguisher n f =
      PMF.pure (checkIsoAnswers n
        ((isoQueries n).map fun word => (booleanOracle n f word).headD false)) := by
  simp only [evalBooleanOracle, ProbOracleComp.run, isolatedVarDistinguisher,
    OracleComp.interpret_map,
    KabanetsCai.interpret_queryTable, map_pure, ProbComp.eval_pure]

private theorem checkIsoAnswers_map_isoQueries {n : ℕ} (hn : 1 ≤ n) (f : BooleanFunction n) :
    checkIsoAnswers n ((isoQueries n).map fun word => (booleanOracle n f word).headD false) =
      decide (∃ x : Fin n, ∀ t : Fin n,
        f (BitString.ofList n (spliceOne n x.val t.val false)) =
          f (BitString.ofList n (spliceOne n x.val t.val true))) := by
  set answers := (isoQueries n).map fun word => (booleanOracle n f word).headD false
  let rowT (x t : ℕ) : List Bool :=
    [f (BitString.ofList n (spliceOne n x t false)),
     f (BitString.ofList n (spliceOne n x t true))]
  have hg (x t : ℕ) (b : Bool) :
      (booleanOracle n f (spliceOne n x t b)).headD false =
        f (BitString.ofList n (spliceOne n x t b)) := by
    simp only [booleanOracle, length_spliceOne hn, ↓reduceIte, List.headD_cons]
  have houter (x : ℕ) (hx : x < n) :
      BitString.listRow (2 * n) x answers = (List.range n).flatMap (rowT x) := by
    have hmap : answers =
        (List.range n).flatMap fun x' => (List.range n).flatMap (rowT x') := by
      simp only [answers, isoQueries, List.map_flatMap, List.map_cons, List.map_nil, hg, rowT]
    rw [hmap]
    refine listRow_range_flatMap _ (fun x' _ => ?_) hx
    simp only [List.length_flatMap, rowT, List.length_cons, List.length_nil, Nat.reduceAdd,
      List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  have hinner (x t : ℕ) (hx : x < n) (ht : t < n) :
      BitString.listRow 2 t (BitString.listRow (2 * n) x answers) = rowT x t := by
    rw [houter x hx]
    exact listRow_range_flatMap (rowT x) (fun _ _ => rfl) ht
  rw [Bool.eq_iff_iff]
  simp only [checkIsoAnswers, rowEq2, List.any_eq_true, List.mem_range, List.all_eq_true,
    beq_iff_eq, decide_eq_true_eq, Fin.exists_iff, Fin.forall_iff, exists_prop]
  refine exists_congr fun x => and_congr_right fun hx => forall₂_congr fun t ht => ?_
  simp only [hinner x t hx ht, rowT, List.getD_cons_zero, List.getD_cons_succ]

/-- **Fan–Li–Yang Lemma 7.3 (completeness)**: if `C` computes `single f` (`1 ≤ n`) and has an
isolated variable, `isolatedVarDistinguisher` accepts `f` with probability `1`. -/
theorem succProbability_isolatedVarDistinguisher_of_hasIsolatedVar {n : ℕ} (hn : 1 ≤ n)
    {C : Circuit (fullSignature 2 Bool) n 1} {f : BooleanFunction n}
    (hcomp : C.Computes fullInterpretation (single f)) (hiso : C.HasIsolatedVar) :
    Game.succProbability (evalBooleanOracle isolatedVarDistinguisher n f) = 1 := by
  obtain ⟨x, hout, hnotOut⟩ := hiso
  have hindep : ∀ (ρ : BitString n) (b : Bool), f (Function.update ρ x b) = f ρ := by
    intro ρ b
    have h1 := Circuit.computes_single_iff.mp hcomp (Function.update ρ x b)
    have h2 := Circuit.computes_single_iff.mp hcomp ρ
    have h3 := congrFun (C.eval_update_of_outDeg_input_eq_zero fullInterpretation
      hout hnotOut ρ b) 0
    exact h1.symm.trans (h3.trans h2)
  have htrue :
      checkIsoAnswers n ((isoQueries n).map fun word => (booleanOracle n f word).headD false) =
        true := by
    rw [checkIsoAnswers_map_isoQueries hn, decide_eq_true_eq]
    refine ⟨x, fun t => ?_⟩
    have hup := ofList_spliceOne x t.val true
    rw [hup, hindep]
  rw [evalBooleanOracle_isolatedVarDistinguisher, htrue]
  simp only [Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

private def evalSingleHom (n : ℕ) (x : Fin n) : BooleanFunction n →+ (Fin n → Bool × Bool) where
  toFun f t :=
    (f (BitString.ofList n (spliceOne n x.val t.val false)),
     f (BitString.ofList n (spliceOne n x.val t.val true)))
  map_zero' := rfl
  map_add' _ _ := rfl

private theorem evalSingleHom_surjective {n : ℕ} (hn : 2 ≤ n) (x : Fin n) :
    Function.Surjective (evalSingleHom n x) := by
  intro φ
  let emb : Fin n × Bool → BitString n :=
    fun p => BitString.ofList n (spliceOne n x.val p.1.val p.2)
  let g : Fin n × Bool → Bool := fun p => if p.2 then (φ p.1).2 else (φ p.1).1
  have hext := (ofList_spliceOne_injective hn x).extend_apply g (fun _ => false)
  exact ⟨Function.extend emb g (fun _ => false),
    funext fun t => Prod.ext (hext (t, false)) (hext (t, true))⟩

/-- **Fan–Li–Yang Lemma 7.3 (soundness against random functions)**: for `2 ≤ n`,
`isolatedVarDistinguisher` accepts a uniformly random Boolean function with probability at most
`n * (1 / 2) ^ n`. -/
theorem succProbability_booleanPRFIdealGame_isolatedVarDistinguisher_le {n : ℕ} (hn : 2 ≤ n) :
    Game.succProbability (booleanPRFIdealGame isolatedVarDistinguisher n) ≤
      (n : ℝ≥0) * (1 / 2 : ℝ≥0) ^ n := by
  have heq : booleanPRFIdealGame isolatedVarDistinguisher n =
      (PMF.uniformOfFintype (BooleanFunction n)).map fun f =>
        decide (∃ x : Fin n,
          decide (∀ t : Fin n,
            ((evalSingleHom n x f t).1 == (evalSingleHom n x f t).2) = true) = true) := by
    rw [booleanPRFIdealGame, ← _root_.PMF.bind_pure_comp]
    refine PMF.bind_congr_on_support _ _ _ fun f _ => ?_
    rw [evalBooleanOracle_isolatedVarDistinguisher,
      checkIsoAnswers_map_isoQueries (by omega : 1 ≤ n)]
    simp only [Function.comp_apply, evalSingleHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
      beq_iff_eq, decide_eq_true_eq]
  rw [Game.succProbability, heq]
  refine (uniformOfFintype_exists_le (fun (x : Fin n) (f : BooleanFunction n) =>
    decide (∀ t : Fin n,
      ((evalSingleHom n x f t).1 == (evalSingleHom n x f t).2) = true))).trans ?_
  have hterm (x : Fin n) :
      ((PMF.uniformOfFintype (BooleanFunction n)).map
        (fun f => decide (∀ t : Fin n,
          ((evalSingleHom n x f t).1 == (evalSingleHom n x f t).2) = true)) true).toNNReal =
        (1 / 2 : ℝ≥0) ^ n := by
    rw [uniformOfFintype_hom_forall_fin_eq (evalSingleHom n x) (evalSingleHom_surjective hn x)
      (fun p : Bool × Bool => p.1 == p.2) 2 (by decide),
      (by decide : Fintype.card (Bool × Bool) = 4)]
    norm_num
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact le_rfl

/-- The ideal-game acceptance probability of `isolatedVarDistinguisher` is negligible. -/
theorem negligible_booleanPRFIdealGame_isolatedVarDistinguisher :
    Negligible
      (fun n => Game.succProbability (booleanPRFIdealGame isolatedVarDistinguisher n)) := by
  negligible eventually (Filter.eventually_ge_atTop 2).mono fun _ hn =>
    succProbability_booleanPRFIdealGame_isolatedVarDistinguisher_le hn

/-! ### Lemma 7.2: Distinguishing intersecting critical paths -/

/-- Test whether a `4`-bit truth table `(h 0 0, h 1 0, h 0 1, h 1 1)` is AND-type (`GF(2)` degree
`2`). -/
private def isAnd4 (b00 b10 b01 b11 : Bool) : Bool :=
  b00 ^^ b10 ^^ b01 ^^ b11

/-- Test whether a `4`-bit truth table `(h 0 0, h 1 0, h 0 1, h 1 1)` is XOR-type (`x ⊕ y` or
`¬(x ⊕ y)`). -/
private def isXor4 (b00 b10 b01 b11 : Bool) : Bool :=
  !(b00 ^^ b10 ^^ b01 ^^ b11) && (b00 != b10) && (b00 != b01)

private theorem not_isAnd4_eq_true_iff (h : Bool → Bool → Bool) :
    (!isAnd4 (h false false) (h true false) (h false true) (h true true)) = true ↔
      ¬ IsAndType h := by
  unfold isAnd4 IsAndType SemiCircuit.IsAffineOp
  cases h false false <;> cases h true false <;> cases h false true <;> cases h true true <;>
    decide

private theorem not_isXor4_eq_true_iff (h : Bool → Bool → Bool) :
    (!isXor4 (h false false) (h true false) (h false true) (h true true)) = true ↔
      ¬ IsXorType h := by
  unfold isXor4 IsXorType SemiCircuit.IsAffineOp
  cases h false false <;> cases h true false <;> cases h false true <;> cases h true true <;>
    decide

/-- The `4 * n ^ 3` deterministic query words used by `criticalPathDistinguisher`. -/
private def critQueries (n : ℕ) : List (List Bool) :=
  (List.range n).flatMap fun x =>
    (List.range n).flatMap fun y =>
      (List.range n).flatMap fun t =>
        [spliceTwo n x y t false false, spliceTwo n x y t true false,
         spliceTwo n x y t false true, spliceTwo n x y t true true]

private abbrev QuadBool := Bool × Bool × Bool × Bool

private def rowNotAnd4 (rxy : List Bool) (t : ℕ) : Bool :=
  !isAnd4 ((BitString.listRow 4 t rxy).getD 0 false)
    ((BitString.listRow 4 t rxy).getD 1 false)
    ((BitString.listRow 4 t rxy).getD 2 false)
    ((BitString.listRow 4 t rxy).getD 3 false)

private def rowNotXor4 (rxy : List Bool) (t : ℕ) : Bool :=
  !isXor4 ((BitString.listRow 4 t rxy).getD 0 false)
    ((BitString.listRow 4 t rxy).getD 1 false)
    ((BitString.listRow 4 t rxy).getD 2 false)
    ((BitString.listRow 4 t rxy).getD 3 false)

/-- Check whether some pair `x < y < n` either never induces an AND-type `2`-bit subfunction or
never induces an XOR-type `2`-bit subfunction across all `n` restrictions. -/
private def checkCritAnswers (n : ℕ) (answers : List Bool) : Bool :=
  (List.range n).any fun x =>
    (List.range n).any fun y =>
      decide (x < y) &&
        (((List.range n).all fun t =>
            rowNotAnd4
              (BitString.listRow (4 * n) y (BitString.listRow (n * (4 * n)) x answers)) t) ||
         ((List.range n).all fun t =>
            rowNotXor4
              (BitString.listRow (4 * n) y (BitString.listRow (n * (4 * n)) x answers)) t))

/-- **Fan–Li–Yang Lemma 7.2 distinguisher**: query `4 * n ^ 3` deterministic restrictions via
`KabanetsCai.queryTable` and accept if some coordinate pair `x < y` either never induces an
AND-type `2`-bit subfunction or never induces an XOR-type `2`-bit subfunction. -/
def criticalPathDistinguisher : OracleDistinguisher :=
  fun n _ => checkCritAnswers n <$> KabanetsCai.queryTable (critQueries n)

private theorem computableInPolyTime_critQueries :
    ComputableInPolyTime (fun p : ℕ × List Bool => critQueries p.1)
      (encPair encUnary encBits) (encList encBits) := by
  let E0 := encPair encUnary encBits
  let E1 := encPair E0 encUnary
  let E2 := encPair E1 encUnary
  let hp3 := ComputableInPolyTime.fst E2 encUnary
  have hs (bx by_ : Bool) := spliceTwo_poly hp3.fst'.fst'.fst' hp3.fst'.snd' hp3.snd'
    (ComputableInPolyTime.snd E2 encUnary) bx by_
  exact ComputableInPolyTime.flatMapWithInput
    (ComputableInPolyTime.fst encUnary encBits).unary_range'
    (ComputableInPolyTime.flatMapWithInput (ComputableInPolyTime.fst E0 encUnary).fst'.unary_range'
      (ComputableInPolyTime.flatMapWithInput
        (ComputableInPolyTime.fst E1 encUnary).fst'.fst'.unary_range'
        ((hs false false).cons' ((hs true false).cons'
          ((hs false true).cons' ((hs true true).cons' (ComputableInPolyTime.const [])))))))

private theorem computableInPolyTime_rowQuadTest (f : QuadBool → Bool) :
    ComputableInPolyTime
      (fun p : List Bool × ℕ =>
        f ((BitString.listRow 4 p.2 p.1).getD 0 false,
           (BitString.listRow 4 p.2 p.1).getD 1 false,
           (BitString.listRow 4 p.2 p.1).getD 2 false,
           (BitString.listRow 4 p.2 p.1).getD 3 false))
      (encPair encBits encUnary) encBool := by
  have hrow := ComputableInPolyTime.bitsRowWithInput (.const 4)
    (ComputableInPolyTime.snd encBits encUnary) (ComputableInPolyTime.fst encBits encUnary)
  have h := (ComputableInPolyTime.of_finite
    (encIn := encPair encBool (encPair encBool (encPair encBool encBool)))
    (encOut := encBool) f).comp'
    ((ComputableInPolyTime.bitsGetDWithInput hrow (.const 0) false).prod
      ((ComputableInPolyTime.bitsGetDWithInput hrow (.const 1) false).prod
        ((ComputableInPolyTime.bitsGetDWithInput hrow (.const 2) false).prod
          (ComputableInPolyTime.bitsGetDWithInput hrow (.const 3) false))))
  exact h

private theorem computableInPolyTime_checkCritAnswers :
    ComputableInPolyTime (fun p : (ℕ × List Bool) × List Bool => checkCritAnswers p.1.1 p.2)
      (encPair (encPair encUnary encBits) encBits) encBool := by
  let E0 := encPair (encPair encUnary encBits) encBits
  let E1 := encPair E0 encUnary
  let hp2 := ComputableInPolyTime.fst E1 encUnary
  let hn2 := hp2.fst'.fst'.fst'
  let hy2 := ComputableInPolyTime.snd E1 encUnary
  have h4n2 := (ComputableInPolyTime.const 4).unary_mul' hn2
  have hrxy2 := ComputableInPolyTime.bitsRowWithInput h4n2 hy2
    (ComputableInPolyTime.bitsRowWithInput (hn2.unary_mul' h4n2) hp2.snd' hp2.fst'.snd')
  have hbody := (ComputableInPolyTime.of_finite
    (encIn := encPair encBool (encPair encBool encBool))
    (encOut := encBool)
    (fun b : Bool × Bool × Bool => b.1 && (b.2.1 || b.2.2))).comp'
    ((hp2.snd'.unary_lt' hy2).prod
      ((ComputableInPolyTime.allWithEncoding
          (computableInPolyTime_rowQuadTest fun q => !isAnd4 q.1 q.2.1 q.2.2.1 q.2.2.2)
          hrxy2 hn2.unary_range').prod
        (ComputableInPolyTime.allWithEncoding
          (computableInPolyTime_rowQuadTest fun q => !isXor4 q.1 q.2.1 q.2.2.1 q.2.2.2)
          hrxy2 hn2.unary_range')))
  exact ComputableInPolyTime.anyWithInput
    (ComputableInPolyTime.fst (encPair encUnary encBits) encBits).fst'.unary_range'
    (ComputableInPolyTime.anyWithInput
      (ComputableInPolyTime.fst E0 encUnary).fst'.fst'.unary_range' hbody)

/-- `criticalPathDistinguisher` is a uniform strict oracle-PPT adversary. -/
theorem isOraclePPT_criticalPathDistinguisher : IsOraclePPT encBool criticalPathDistinguisher := by
  have hq := computableInPolyTime_critQueries
  have hc := computableInPolyTime_checkCritAnswers
  ppt [criticalPathDistinguisher]

private theorem evalBooleanOracle_criticalPathDistinguisher (n : ℕ) (f : BooleanFunction n) :
    evalBooleanOracle criticalPathDistinguisher n f =
      PMF.pure (checkCritAnswers n
        ((critQueries n).map fun word => (booleanOracle n f word).headD false)) := by
  simp only [evalBooleanOracle, ProbOracleComp.run, criticalPathDistinguisher,
    OracleComp.interpret_map,
    KabanetsCai.interpret_queryTable, map_pure, ProbComp.eval_pure]

private def quadAt (n : ℕ) (x y : Fin n) (f : BooleanFunction n) (t : Fin n) : QuadBool :=
  (f (BitString.ofList n (spliceTwo n x.val y.val t.val false false)),
   f (BitString.ofList n (spliceTwo n x.val y.val t.val true false)),
   f (BitString.ofList n (spliceTwo n x.val y.val t.val false true)),
   f (BitString.ofList n (spliceTwo n x.val y.val t.val true true)))

private theorem checkCritAnswers_map_critQueries {n : ℕ} (hn : 2 ≤ n) (f : BooleanFunction n) :
    checkCritAnswers n ((critQueries n).map fun word => (booleanOracle n f word).headD false) =
      decide (∃ x y : Fin n, x < y ∧
        ((∀ t : Fin n,
            (!isAnd4 (quadAt n x y f t).1 (quadAt n x y f t).2.1
              (quadAt n x y f t).2.2.1 (quadAt n x y f t).2.2.2) = true) ∨
         (∀ t : Fin n,
            (!isXor4 (quadAt n x y f t).1 (quadAt n x y f t).2.1
              (quadAt n x y f t).2.2.1 (quadAt n x y f t).2.2.2) = true))) := by
  set answers := (critQueries n).map fun word => (booleanOracle n f word).headD false
  let rowT (x y t : ℕ) : List Bool :=
    [f (BitString.ofList n (spliceTwo n x y t false false)),
     f (BitString.ofList n (spliceTwo n x y t true false)),
     f (BitString.ofList n (spliceTwo n x y t false true)),
     f (BitString.ofList n (spliceTwo n x y t true true))]
  have hg (x y t : ℕ) (bx by_ : Bool) :
      (booleanOracle n f (spliceTwo n x y t bx by_)).headD false =
        f (BitString.ofList n (spliceTwo n x y t bx by_)) := by
    simp only [booleanOracle, length_spliceTwo hn, ↓reduceIte, List.headD_cons]
  have hlenY (x' y : ℕ) : ((List.range n).flatMap (rowT x' y)).length = 4 * n := by
    simp only [List.length_flatMap, rowT, List.length_cons, List.length_nil, Nat.reduceAdd,
      List.map_const', List.length_range, List.sum_replicate, smul_eq_mul, Nat.mul_comm]
  have hrowX (x : ℕ) (hx : x < n) :
      BitString.listRow (n * (4 * n)) x answers =
        (List.range n).flatMap fun y => (List.range n).flatMap (rowT x y) := by
    have hmap : answers = (List.range n).flatMap fun x' =>
        (List.range n).flatMap fun y => (List.range n).flatMap (rowT x' y) := by
      simp only [answers, critQueries, List.map_flatMap, List.map_cons, List.map_nil, hg, rowT]
    rw [hmap]
    refine listRow_range_flatMap _ (fun x' _ => ?_) hx
    rw [List.length_flatMap, List.map_congr_left fun y _ => hlenY x' y]
    simp only [List.map_const', List.length_range, List.sum_replicate, smul_eq_mul]
  have hrowXY (x y : ℕ) (hx : x < n) (hy : y < n) :
      BitString.listRow (4 * n) y (BitString.listRow (n * (4 * n)) x answers) =
        (List.range n).flatMap (rowT x y) := by
    rw [hrowX x hx]
    exact listRow_range_flatMap _ (fun y' _ => hlenY x y') hy
  have hrowXYT (x y t : ℕ) (hx : x < n) (hy : y < n) (ht : t < n) :
      BitString.listRow 4 t
          (BitString.listRow (4 * n) y (BitString.listRow (n * (4 * n)) x answers)) =
        rowT x y t := by
    rw [hrowXY x y hx hy]
    exact listRow_range_flatMap (rowT x y) (fun _ _ => rfl) ht
  rw [Bool.eq_iff_iff]
  simp only [checkCritAnswers, rowNotAnd4, rowNotXor4, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, List.all_eq_true]
  constructor
  · rintro ⟨x, hx, y, hy, hlt, hor⟩
    refine ⟨⟨x, hx⟩, ⟨y, hy⟩, hlt, hor.imp (fun h t => ?_) (fun h t => ?_)⟩ <;>
    · simpa only [hrowXYT x y t.val hx hy t.isLt, rowT, quadAt, List.getD_cons_zero,
        List.getD_cons_succ] using h t.val t.isLt
  · rintro ⟨x, y, hlt, hor⟩
    refine ⟨x.val, x.isLt, y.val, y.isLt, hlt, hor.imp (fun h t ht => ?_) (fun h t ht => ?_)⟩ <;>
    · simpa only [hrowXYT x.val y.val t x.isLt y.isLt ht, rowT, quadAt, List.getD_cons_zero,
        List.getD_cons_succ] using h ⟨t, ht⟩

/-- **Fan–Li–Yang Lemma 7.2 (completeness)**: if `C` is a single-output `B₂` circuit with
`NoDeadGates` (*normalized* in [FanLiYang2022]) computing `single f` (`2 ≤ n`) whose critical paths
are not pairwise disjoint, then `criticalPathDistinguisher` accepts `f` with probability `1`. -/
theorem succProbability_criticalPathDistinguisher_of_not_disjoint_criticalPath {n : ℕ} (hn : 2 ≤ n)
    {C : Circuit (fullSignature 2 Bool) n 1} {f : BooleanFunction n}
    (hcomp : C.Computes fullInterpretation (single f)) (hnoDead : C.NoDeadGates)
    (hnotDisj :
      ¬ Pairwise fun x y => Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset) :
    Game.succProbability (evalBooleanOracle criticalPathDistinguisher n f) = 1 := by
  have hfeq : ∀ z : BitString n, C.eval fullInterpretation z 0 = f z :=
    Circuit.computes_single_iff.mp hcomp
  unfold Pairwise at hnotDisj
  push Not at hnotDisj
  obtain ⟨x₀, y₀, hne, hinter⟩ := hnotDisj
  obtain ⟨x, y, hxy, hne', hinter'⟩ : ∃ x y : Fin n, x < y ∧ x ≠ y ∧
      ¬ Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset :=
    (lt_or_gt_of_ne hne).elim (fun h => ⟨x₀, y₀, h, hne, hinter⟩)
      (fun h => ⟨y₀, x₀, h, hne.symm, fun hd => hinter hd.symm⟩)
  have hor := not_isAndType_or_not_isXorType_of_not_disjoint_criticalPath C hnoDead hne' hinter'
  simp only [hfeq] at hor
  have htrue :
      checkCritAnswers n ((critQueries n).map fun word => (booleanOracle n f word).headD false) =
        true := by
    rw [checkCritAnswers_map_critQueries hn, decide_eq_true_eq]
    have hq (t : Fin n) : quadAt n x y f t =
        (let ρ := BitString.ofList n (spliceTwo n x.val y.val t.val false false)
         let h : Bool → Bool → Bool := fun bx by_ =>
           f (Function.update (Function.update ρ x bx) y by_)
         (h false false, h true false, h false true, h true true)) := by
      simp only [quadAt, ← ofList_spliceTwo hxy]
    refine ⟨x, y, hxy, hor.imp (fun hand t => ?_) (fun hxor t => ?_)⟩
    · rw [hq t]; dsimp only; exact (not_isAnd4_eq_true_iff _).mpr (hand _)
    · rw [hq t]; dsimp only; exact (not_isXor4_eq_true_iff _).mpr (hxor _)
  rw [evalBooleanOracle_criticalPathDistinguisher, htrue]
  simp only [Game.succProbability, PMF.pure_apply_self, ENNReal.toNNReal_one]

private def evalPairHom (n : ℕ) (x y : Fin n) : BooleanFunction n →+ (Fin n → QuadBool) where
  toFun f t := quadAt n x y f t
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp]
private theorem evalPairHom_apply (n : ℕ) (x y : Fin n) (f : BooleanFunction n) (t : Fin n) :
    evalPairHom n x y f t = quadAt n x y f t := rfl

private theorem evalPairHom_surjective {n : ℕ} (hn : 5 ≤ n) {x y : Fin n} (hxy : x < y) :
    Function.Surjective (evalPairHom n x y) := by
  intro φ
  let emb : Fin n × Bool × Bool → BitString n :=
    fun p => BitString.ofList n (spliceTwo n x.val y.val p.1.val p.2.1 p.2.2)
  let g : Fin n × Bool × Bool → Bool := fun p => match p.2.1, p.2.2 with
    | false, false => (φ p.1).1 | true, false => (φ p.1).2.1
    | false, true => (φ p.1).2.2.1 | true, true => (φ p.1).2.2.2
  have hext := (ofList_spliceTwo_injective hn hxy).extend_apply g (fun _ => false)
  exact ⟨Function.extend emb g (fun _ => false), funext fun t => Prod.ext (hext (t, false, false))
    (Prod.ext (hext (t, true, false)) (Prod.ext (hext (t, false, true)) (hext (t, true, true))))⟩

/-- **Fan–Li–Yang Lemma 7.2 (soundness against random functions)**: for `5 ≤ n`,
`criticalPathDistinguisher` accepts a uniformly random Boolean function with probability at most
`n ^ 2 * ((1 / 2) ^ n + (7 / 8) ^ n)`. -/
theorem succProbability_booleanPRFIdealGame_criticalPathDistinguisher_le {n : ℕ} (hn : 5 ≤ n) :
    Game.succProbability (booleanPRFIdealGame criticalPathDistinguisher n) ≤
      (n : ℝ≥0) ^ 2 * ((1 / 2 : ℝ≥0) ^ n + (7 / 8 : ℝ≥0) ^ n) := by
  let PairLt := {p : Fin n × Fin n // p.1 < p.2}
  let test : Bool → QuadBool → Bool := fun b q =>
    if b then !isXor4 q.1 q.2.1 q.2.2.1 q.2.2.2 else !isAnd4 q.1 q.2.1 q.2.2.1 q.2.2.2
  let P : PairLt × Bool → BooleanFunction n → Bool := fun idx f =>
    decide (∀ t : Fin n, test idx.2 (evalPairHom n idx.1.1.1 idx.1.1.2 f t) = true)
  have heq : booleanPRFIdealGame criticalPathDistinguisher n =
      (PMF.uniformOfFintype (BooleanFunction n)).map fun f =>
        decide (∃ idx : PairLt × Bool, P idx f = true) := by
    rw [booleanPRFIdealGame, ← _root_.PMF.bind_pure_comp]
    refine PMF.bind_congr_on_support _ _ _ fun f _ => ?_
    rw [evalBooleanOracle_criticalPathDistinguisher,
      checkCritAnswers_map_critQueries (by omega : 2 ≤ n)]
    dsimp only [Function.comp_apply]
    congr 1
    rw [Bool.eq_iff_iff]
    simp only [decide_eq_true_eq, P, test, evalPairHom_apply]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, y, hxy, hand | hxor⟩
      · exact ⟨(⟨(x, y), hxy⟩, false), by simpa using hand⟩
      · exact ⟨(⟨(x, y), hxy⟩, true), by simpa using hxor⟩
    · rintro ⟨⟨⟨⟨x, y⟩, hxy⟩, false | true⟩, hb⟩
      · exact ⟨x, y, hxy, Or.inl (by simpa using hb)⟩
      · exact ⟨x, y, hxy, Or.inr (by simpa using hb)⟩
  rw [Game.succProbability, heq]
  refine (uniformOfFintype_exists_le P).trans ?_
  have hc2 : Fintype.card QuadBool = 16 := by decide
  have hAnd (p : PairLt) :
      ((PMF.uniformOfFintype (BooleanFunction n)).map (P (p, false)) true).toNNReal =
        (1 / 2 : ℝ≥0) ^ n := by
    rw [uniformOfFintype_hom_forall_fin_eq (evalPairHom n p.1.1 p.1.2)
      (evalPairHom_surjective hn p.2) (test false) 8 (by decide), hc2]
    norm_num
  have hXor (p : PairLt) :
      ((PMF.uniformOfFintype (BooleanFunction n)).map (P (p, true)) true).toNNReal =
        (7 / 8 : ℝ≥0) ^ n := by
    rw [uniformOfFintype_hom_forall_fin_eq (evalPairHom n p.1.1 p.1.2)
      (evalPairHom_surjective hn p.2) (test true) 14 (by decide), hc2]
    norm_num
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool, hXor, hAnd, add_comm]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : Fintype.card PairLt ≤ n ^ 2 :=
    (Fintype.card_subtype_le _).trans_eq (by simp only [Fintype.card_prod, Fintype.card_fin, sq])
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)

/-- The ideal-game acceptance probability of `criticalPathDistinguisher` is negligible. -/
theorem negligible_booleanPRFIdealGame_criticalPathDistinguisher :
    Negligible
      (fun n => Game.succProbability (booleanPRFIdealGame criticalPathDistinguisher n)) := by
  negligible eventually (Filter.eventually_ge_atTop 5).mono fun _ hn =>
    succProbability_booleanPRFIdealGame_criticalPathDistinguisher_le hn

/-! ### Theorem 7.5: `2n - 2` `B₂`-circuit lower bound for PRFs -/

private theorem succProbability_le_advantage_add (g₁ g₂ : Game) :
    Game.succProbability g₁ ≤ Game.advantage g₁ g₂ + Game.succProbability g₂ := by
  simpa only [Game.advantage_pure_false] using Game.advantage_triangle g₁ g₂ (PMF.pure false)

private theorem evalBooleanOracle_true_eq_one {d : OracleDistinguisher} {n : ℕ}
    {f : BooleanFunction n} (h : Game.succProbability (evalBooleanOracle d n f) = 1) :
    evalBooleanOracle d n f true = 1 := by
  simpa only [Game.succProbability, ENNReal.coe_toNNReal (PMF.apply_ne_top _ _),
    ENNReal.coe_one] using congrArg (fun x : ℝ≥0 => (x : ℝ≥0∞)) h

private theorem lt_two_mul_sub_two_distinguishers_ge_one {n : ℕ} (hn : 2 ≤ n)
    {f : BooleanFunction n}
    (hlt : complexity (fullInterpretation (k := 2)) (single f) < 2 * n - 2) :
    1 ≤ evalBooleanOracle isolatedVarDistinguisher n f true +
      evalBooleanOracle criticalPathDistinguisher n f true := by
  obtain ⟨C₀, hC₀comp, hC₀size⟩ :=
    exists_computes_size_eq_complexity (I := fullInterpretation (k := 2)) (f := single f)
  obtain ⟨C, hCnoDead, hCsize, hCeval, -⟩ := C₀.exists_noDeadGates
  have hCcomp : C.Computes fullInterpretation (single f) := by
    rw [Circuit.computes_single_iff]
    exact fun z => (congrFun (hCeval fullInterpretation z) 0).trans
      (Circuit.computes_single_iff.mp hC₀comp z)
  by_cases hiso : C.HasIsolatedVar
  · rw [evalBooleanOracle_true_eq_one
      (succProbability_isolatedVarDistinguisher_of_hasIsolatedVar (by omega : 1 ≤ n)
        hCcomp hiso)]
    exact le_self_add
  · have hnotDisj :
        ¬ Pairwise fun x y =>
          Disjoint (C.criticalPath x).toFinset (C.criticalPath y).toFinset := fun hdisj => by
      have := C.two_mul_sub_two_mul_le_size C.fanInAtMost_fullSignature hCnoDead hiso hdisj
      omega
    rw [evalBooleanOracle_true_eq_one
      (succProbability_criticalPathDistinguisher_of_not_disjoint_criticalPath
        hn hCcomp hCnoDead hnotDisj)]
    exact le_add_self

/-- Distributional strengthening of [FanLiYang2022, Theorem 7.5]. For every Boolean PRF
ensemble, the probability of sampling a function with `B₂`-circuit complexity strictly below
`2 * n - 2` is negligible in `n`. -/
theorem BooleanPRF.negligible_complexity_lt_two_mul_sub_two {D : ∀ n, PMF (BooleanFunction n)}
    (hD : BooleanPRF D) :
    Negligible (fun n =>
      ((D n).map (fun f =>
        decide (complexity (fullInterpretation (k := 2)) (single f) < 2 * n - 2))
        true).toNNReal) := by
  have hbound : Negligible (fun n =>
      (Game.advantage (booleanPRFRealGame D isolatedVarDistinguisher n)
          (booleanPRFIdealGame isolatedVarDistinguisher n) +
        Game.succProbability (booleanPRFIdealGame isolatedVarDistinguisher n)) +
      (Game.advantage (booleanPRFRealGame D criticalPathDistinguisher n)
          (booleanPRFIdealGame criticalPathDistinguisher n) +
        Game.succProbability (booleanPRFIdealGame criticalPathDistinguisher n))) :=
    ((hD isolatedVarDistinguisher isOraclePPT_isolatedVarDistinguisher).add
      negligible_booleanPRFIdealGame_isolatedVarDistinguisher).add
      ((hD criticalPathDistinguisher isOraclePPT_criticalPathDistinguisher).add
        negligible_booleanPRFIdealGame_criticalPathDistinguisher)
  refine negligible_of_eventually_le hbound ?_
  filter_upwards [Filter.eventually_ge_atTop 2] with n hn
  refine le_trans ?_ (add_le_add
    (succProbability_le_advantage_add (booleanPRFRealGame D isolatedVarDistinguisher n)
      (booleanPRFIdealGame isolatedVarDistinguisher n))
    (succProbability_le_advantage_add (booleanPRFRealGame D criticalPathDistinguisher n)
      (booleanPRFIdealGame criticalPathDistinguisher n)))
  have htsum :
      ((D n).map (fun f =>
        decide (complexity (fullInterpretation (k := 2)) (single f) < 2 * n - 2))) true ≤
      booleanPRFRealGame D isolatedVarDistinguisher n true +
        booleanPRFRealGame D criticalPathDistinguisher n true := by
    refine PMF.bind_apply_le_add_on_support (D n) true fun f _ => ?_
    by_cases hlt : complexity (fullInterpretation (k := 2)) (single f) < 2 * n - 2
    · simpa only [Function.comp_apply, hlt, decide_true, PMF.pure_apply_self] using
        lt_two_mul_sub_two_distinguishers_ge_one hn hlt
    · simp only [Function.comp_apply, hlt, decide_false, PMF.pure_apply, Bool.true_eq_false,
        ↓reduceIte, zero_le]
  simpa only [Game.succProbability,
    ENNReal.toNNReal_add (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)] using
    ENNReal.toNNReal_mono (by finiteness) htsum

/-- The worst-case lower bound of [FanLiYang2022, §7.1, Theorem 7.5, p. 41]. For every
`BooleanPRF D` and all sufficiently large `n`, a function in the support of `D n` needs at least
`2 * n - 2` gates. Inputs and output wires are free. Each binary Boolean gate and each nullary
constant costs one gate. For `n ≥ 2`, a constant binary gate on two input wires realizes the same
constant at the same cost in the source’s `B₂` basis. -/
theorem BooleanPRF.eventually_exists_mem_support_two_mul_sub_two_le_complexity
    {D : ∀ n, PMF (BooleanFunction n)} (hD : BooleanPRF D) :
    ∀ᶠ n in Filter.atTop,
      ∃ f ∈ (D n).support, 2 * n - 2 ≤ complexity (fullInterpretation (k := 2)) (single f) := by
  have hnegl := hD.negligible_complexity_lt_two_mul_sub_two
  have hev := hnegl.eventually_le_inv_polynomial (p := fun _ => 2)
    (PolynomiallyBounded.const 2) (fun _ => by omega)
  filter_upwards [hev] with n hn
  by_contra hall
  push Not at hall
  have hmap : ((D n).map (fun f =>
      decide (complexity (fullInterpretation (k := 2)) (single f) < 2 * n - 2))) =
      PMF.pure true := by
    rw [← _root_.PMF.bind_pure_comp, ← PMF.bind_const (D n) (PMF.pure true)]
    refine PMF.bind_congr_on_support _ _ _ fun f hf => ?_
    simp only [Function.comp_apply, hall f hf, decide_true]
  rw [hmap, PMF.pure_apply_self, ENNReal.toNNReal_one, NNReal.coe_one] at hn
  norm_num at hn

/-- For a uniform key of a word-valued PRF, the probability that its first output bit is
computable with fewer than `2 * n - 2` gates is negligible. -/
theorem PseudorandomFunction.negligible_complexity_restriction_lt_two_mul_sub_two
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    Negligible (fun n =>
      ((BitString.uniformList n).map (fun key =>
        decide (complexity (fullInterpretation (k := 2))
          (single (KabanetsCai.restriction (family key) n n)) < 2 * n - 2)) true).toNNReal) := by
  simpa only [prfFirstBitEnsemble, _root_.PMF.map_comp, Function.comp_def] using
    hF.booleanPRF.negligible_complexity_lt_two_mul_sub_two

/-- Under a uniform `n`-bit PRF key, the probability that the full `n`-output function has
`B₂`-circuit complexity below `2 * n - 2` is negligible. A circuit for all outputs also computes
the first bit by selecting that output wire. -/
theorem PseudorandomFunction.negligible_complexity_lt_two_mul_sub_two
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    Negligible (fun n =>
      ((BitString.uniformList n).map (fun key =>
        decide (complexity (fullInterpretation (k := 2))
          (fun x : BitString n => BitString.ofList n (family key (List.ofFn x))) <
            2 * n - 2)) true).toNNReal) := by
  refine negligible_of_eventually_le hF.negligible_complexity_restriction_lt_two_mul_sub_two ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have hproj : ∀ key : List Bool,
      complexity (fullInterpretation (k := 2))
        (single (KabanetsCai.restriction (family key) n n)) ≤
      complexity (fullInterpretation (k := 2))
        (fun x : BitString n => BitString.ofList n (family key (List.ofFn x))) := by
    intro key
    let F : BitString n → BitString n :=
      fun x => BitString.ofList n (family key (List.ofFn x))
    let w : Fin 1 → Fin n := fun _ => ⟨0, hn⟩
    have hcomp := complexity_comp_le (I := fullInterpretation (k := 2)) F
      (fun y : BitString n => y ∘ w)
    have hfun : (fun y : BitString n => y ∘ w) ∘ F =
        single (KabanetsCai.restriction (family key) n n) := by
      funext x j
      rw [Subsingleton.elim j 0]
      simp only [Function.comp_apply, F, w, BitString.ofList, single_apply, KabanetsCai.restriction,
        Nat.sub_self, List.replicate_zero, List.nil_append]
      cases family key (List.ofFn x) <;> rfl
    rwa [hfun, complexity_wiring w, Nat.add_zero] at hcomp
  refine ENNReal.toNNReal_mono (PMF.apply_ne_top _ _)
    (PMF.map_true_mono _ fun key _ hlt =>
      decide_eq_true ((hproj key).trans_lt (of_decide_eq_true hlt)))

/-- For every `PseudorandomFunction family` and all sufficiently large `n`, there exists an `n`-bit
key whose first-output-bit function has `B₂`-circuit complexity at least `2 * n - 2`. -/
theorem PseudorandomFunction.eventually_exists_key_two_mul_sub_two_le_complexity
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    ∀ᶠ n in Filter.atTop,
      ∃ key : BitString n,
        2 * n - 2 ≤ complexity (fullInterpretation (k := 2))
          (single (KabanetsCai.restriction (family (List.ofFn key)) n n)) := by
  filter_upwards [hF.booleanPRF.eventually_exists_mem_support_two_mul_sub_two_le_complexity]
    with n ⟨f, hf, hle⟩
  simp only [prfFirstBitEnsemble, PMF.mem_support_map_iff] at hf
  obtain ⟨keyList, hkey, rfl⟩ := hf
  have hklen := BitString.length_of_mem_support_uniformList hkey
  refine ⟨BitString.ofList n keyList, ?_⟩
  rwa [BitString.ofFn_ofList hklen]

end Cslib.Crypto
