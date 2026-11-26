/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.PseudorandomFunction.Finite
public import CslibFrontier.Crypto.Computational.PseudorandomPermutation
public import CslibFrontier.Crypto.Primitives.PRP.BirthdayAttack
public import CslibFrontier.Foundations.Data.BitString.List.LowBits

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Max
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Languages.Probabilistic.Oracle.Codec
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation
import CslibFrontier.Tactic.PolyTime

/-!
# Word-level birthday attack on block ciphers

Formalizes the word-level collision distinguisher of Boneh–Shoup (§4.4.3, p. 134) against a
`BlockCipher` viewed as a pseudorandom function, wrapping the finite birthday distinguisher
`PRP.birthdayDistinguisher` with an explicit polynomial-time oracle adversary.

## Main definitions

* `Cslib.Crypto.wordBirthdayDistinguisher`: queries `min (Q n) (2 ^ blockLen n)` distinct
  `blockLen n`-bit strings generated via `BitString.lowBits`, returning `true` on any collision.
* `Cslib.Crypto.birthdayQueries`: the corresponding `Fin q → BitString m` indexing map.

## Main results

* `Cslib.Crypto.isQueryBounded_wordBirthdayDistinguisher`: exact query bound
  `min (Q n) (2 ^ blockLen n)`.
* `Cslib.Crypto.isOraclePPT_wordBirthdayDistinguisher`: polynomial-time oracle certification for
  polynomial-time computable `blockLen` and `Q`.
* `Cslib.Crypto.coe_advantage_wordBirthdayDistinguisher`,
  `Cslib.Crypto.min_le_advantage_wordBirthdayDistinguisher`,
  `Cslib.Crypto.half_le_advantage_wordBirthdayDistinguisher`: concrete advantage formula and lower
  bounds relating `E.prpRealGame` vs `prfIdealGame` to `PRP.birthdayDistinguisher`, together with
  their `prfRealGame` counterparts `BlockCipher.coe_prfAdvantage_wordBirthdayDistinguisher`,
  `BlockCipher.min_le_prfAdvantage_wordBirthdayDistinguisher`, and
  `BlockCipher.half_le_prfAdvantage_wordBirthdayDistinguisher` when `E.keyLen = id`.
* `Cslib.Crypto.BlockCipher.not_indistinguishable_prpRealGame_prfIdealGame` and
  `Cslib.Crypto.BlockCipher.not_pseudorandomFunctionOver_of_not_negligible`: when
  `((2 : ℝ≥0) ^ E.blockLen n)⁻¹` is not negligible (for eventually nonzero `E.blockLen`), `E`
  cannot be a `PseudorandomFunctionOver` `E.blockLen` `E.blockLen`, showing that the
  super-polynomial block-size hypothesis in
  `BlockCipher.prp_iff_indistinguishable_prpRealGame_prfIdealGame` and
  `BlockCipher.prp_iff_pseudorandomFunctionOver_of_keyLen_eq_id` is necessary.

The deterministic counter-mode birthday attack of §4.4.4.1 is not formalized here.

## References

* [BonehShoup2023] D. Boneh and V. Shoup, *A Graduate Course in Applied Cryptography*, v0.6,
  Section 4.4.3, p. 134.
-/

namespace Cslib.Crypto

public section

open Probability Turing.MultiTapeTM Filter
open scoped NNReal

section Defs

private def wordBirthdayStep (blockLen : ℕ → ℕ) (n : ℕ)
    (state : List (List Bool) × Bool) : WordOracleComp Unit (List (List Bool) × Bool) := do
  let raw ← ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
    ((), BitString.lowBits (blockLen n) state.1.length)
  let reply := raw.take (blockLen n)
  return (reply :: state.1, state.2 || state.1.any fun prev => decide (prev = reply))

/-- Word-level birthday distinguisher querying `min (Q n) (2 ^ blockLen n)` distinct
`blockLen n`-bit inputs (via `BitString.lowBits`) and returning `true` iff two truncated outputs
collide. -/
def wordBirthdayDistinguisher (blockLen Q : ℕ → ℕ) : OracleDistinguisher :=
  fun n _ => Prod.snd <$>
    OracleComp.iterate (min (Q n) (2 ^ blockLen n)) (wordBirthdayStep blockLen n) ([], false)

/-- Finite `BitString m` query family corresponding to the first `q` queries made by
`wordBirthdayDistinguisher`. -/
@[expose] def birthdayQueries (m q : ℕ) : Fin q → BitString m :=
  fun i => BitString.ofList m (BitString.lowBits m i)

/-- `birthdayQueries m q` is injective whenever `q ≤ 2 ^ m`. -/
theorem injective_birthdayQueries {m q : ℕ} (hq : q ≤ 2 ^ m) :
    Function.Injective (birthdayQueries m q) := by
  intro i j hij
  have hij' := congrArg List.ofFn hij
  simp only [birthdayQueries, BitString.ofFn_ofList (BitString.length_lowBits m _)] at hij'
  exact Fin.ext
    (BitString.lowBits_injective_of_lt (i.isLt.trans_le hq) (j.isLt.trans_le hq) hij')

/-- `birthdayQueries m (2 ^ m)` enumerates every `m`-bit string bijectively. -/
theorem bijective_birthdayQueries {m : ℕ} :
    Function.Bijective (birthdayQueries m (2 ^ m)) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨injective_birthdayQueries le_rfl, by simp⟩

end Defs

section PolyTime

private theorem isOraclePPTOn_wordBirthdayStep {blockLen : ℕ → ℕ}
    (hblockLen : ComputableInPolyTime blockLen encUnary encUnary) :
    IsOraclePPTOn (encPair encUnary (encPair (encList encBits) encBool))
      (encPair (encList encBits) encBool)
      (fun pair : ℕ × (List (List Bool) × Bool) => wordBirthdayStep blockLen pair.1 pair.2) := by
  let inp : (ℕ × (List (List Bool) × Bool)) ↪ List Bool :=
    encPair encUnary (encPair (encList encBits) encBool)
  have hn : ComputableInPolyTime (fun p : ℕ × (List (List Bool) × Bool) => p.1) inp encUnary :=
    .fst _ _
  have hq : ComputableInPolyTime
      (fun p : ℕ × (List (List Bool) × Bool) => BitString.lowBits (blockLen p.1) p.2.1.length)
      inp encBits :=
    ComputableInPolyTime.bitsLow (hblockLen.comp hn) (ComputableInPolyTime.unary_to_binary.comp
      ((ComputableInPolyTime.length_list encBits).comp (.fst' (.snd _ _))))
  have hquery : IsOraclePPTOn inp (encPair inp encBits)
      (fun p => (fun r => (p, r)) <$>
        (List.take (blockLen p.1) <$>
          ProbOracleComp.query (spec := fun _ : Unit × List Bool => List Bool)
            ((), BitString.lowBits (blockLen p.1) p.2.1.length))) :=
    (IsOraclePPTOn.query_take () hq (hblockLen.comp hn)).keep_input
  have hmap : ComputableInPolyTime
      (fun q : (ℕ × (List (List Bool) × Bool)) × List Bool =>
        (q.2 :: q.1.2.1, q.1.2.2 || q.1.2.1.any fun prev => decide (prev = q.2)))
      (encPair inp encBits) (encPair (encList encBits) encBool) := by
    have hp : ComputableInPolyTime
        (fun q : (ℕ × (List (List Bool) × Bool)) × List Bool => q.1)
        (encPair inp encBits) inp := .fst _ _
    have hqseen : ComputableInPolyTime
        (fun q : (ℕ × (List (List Bool) × Bool)) × List Bool => q.1.2.1)
        (encPair inp encBits) (encList encBits) := .fst' (.snd' hp)
    have hany : ComputableInPolyTime
        (fun q : (ℕ × (List (List Bool) × Bool)) × List Bool =>
          q.1.2.1.any fun prev => decide (prev = q.2))
        (encPair inp encBits) encBool :=
      hqseen.anyWithInput (ComputableInPolyTime.decide_eq' (.snd _ _)
        ((ComputableInPolyTime.snd _ _).comp (.fst _ _)))
    have hor : ComputableInPolyTime
        (fun q : (ℕ × (List (List Bool) × Bool)) × List Bool =>
          q.1.2.2 || q.1.2.1.any fun prev => decide (prev = q.2))
        (encPair inp encBits) encBool :=
      (ComputableInPolyTime.of_finite (encIn := encPair encBool encBool) (encOut := encBool)
        fun p : Bool × Bool => p.1 || p.2).comp (hp.snd'.snd'.prod hany)
    exact ((ComputableInPolyTime.snd _ _).cons' hqseen).prod hor
  convert hquery.map hmap using 1
  funext pair
  simp [wordBirthdayStep, bind_pure_comp]

/-- `wordBirthdayDistinguisher blockLen Q` runs in probabilistic polynomial time when `blockLen`
and `Q` are computable in polynomial time on unary inputs. -/
theorem isOraclePPT_wordBirthdayDistinguisher {blockLen Q : ℕ → ℕ}
    (hblockLen : ComputableInPolyTime blockLen encUnary encUnary)
    (hQ : ComputableInPolyTime Q encUnary encUnary) :
    IsOraclePPT encBool (wordBirthdayDistinguisher blockLen Q) := by
  have hcount : ComputableInPolyTime (fun n => min (Q n) (2 ^ blockLen n)) encUnary encUnary :=
    ComputableInPolyTime.binary_min_unary' hQ (ComputableInPolyTime.binary_two_pow.comp hblockLen)
  have hinit : ComputableInPolyTime (fun _ : ℕ => (([] : List (List Bool)), false))
      encUnary (encPair (encList encBits) encBool) := ComputableInPolyTime.const _
  have hpoly : PolyBounded (fun n => (encUnary n).length) (fun n => 4 * blockLen n + 10) := by
    growth_poly
  have hgrowth : ∀ n (state next : List (List Bool) × Bool),
      next ∈ OracleComp.support (wordBirthdayStep blockLen n state) →
      (encPair (encList encBits) encBool next).length ≤
        (encPair (encList encBits) encBool state).length + (4 * blockLen n + 10) := by
    intro n state next hnext
    obtain ⟨seen, collided⟩ := state
    simp only [wordBirthdayStep, OracleComp.mem_supportWith_bind_iff] at hnext
    rcases hnext with ⟨raw, -, hnext⟩
    rcases OracleComp.eq_of_mem_supportWith_pure hnext with rfl
    have hlen : (raw.take (blockLen n)).length ≤ blockLen n := List.length_take_le _ _
    have hencBool : ∀ b : Bool, (encBool b).length = 1 := by intro b; cases b <;> rfl
    enc_len [hencBool]
  have hiter : IsOraclePPTOn encUnary (encPair (encList encBits) encBool)
      (fun n => OracleComp.iterate (min (Q n) (2 ^ blockLen n))
        (wordBirthdayStep blockLen n) ([], false)) :=
    IsOraclePPTOn.iterateWith_of_bounded_growth hcount hinit
      (isOraclePPTOn_wordBirthdayStep hblockLen) hpoly hgrowth
  exact ((hiter.map (by fun_prop)).preprocess
    (ComputableInPolyTime.fst encUnary encBits)).isOraclePPT

end PolyTime

section Semantics

private theorem isQueryBounded_wordBirthdayStep (blockLen : ℕ → ℕ) (n : ℕ)
    (state : List (List Bool) × Bool) :
    ProbOracleComp.IsQueryBounded (wordBirthdayStep blockLen n state) 1 :=
  (ProbOracleComp.IsQueryBounded.query
    (spec := fun _ : Unit × List Bool => List Bool)
    ((), BitString.lowBits (blockLen n) state.1.length)).bind
    (fun _ => OracleComp.IsCostBounded.pure _ 0)

/-- `wordBirthdayDistinguisher blockLen Q n aux` makes at most `min (Q n) (2 ^ blockLen n)`
oracle queries. -/
theorem isQueryBounded_wordBirthdayDistinguisher (blockLen Q : ℕ → ℕ) (n : ℕ) (aux : List Bool) :
    ProbOracleComp.IsQueryBounded (wordBirthdayDistinguisher blockLen Q n aux)
      (min (Q n) (2 ^ blockLen n)) := by
  have hiter : ∀ k, ProbOracleComp.IsQueryBounded
      (OracleComp.iterate k (wordBirthdayStep blockLen n) ([], false) :
        WordOracleComp Unit (List (List Bool) × Bool)) k := by
    intro k
    induction k with
    | zero => exact OracleComp.IsCostBounded.pure _ 0
    | succ k ih =>
      rw [OracleComp.iterate_succ]
      exact OracleComp.IsCostBounded.bind ih (isQueryBounded_wordBirthdayStep blockLen n)
  rw [wordBirthdayDistinguisher, ← bind_pure_comp, ← Nat.add_zero (min (Q n) (2 ^ blockLen n))]
  exact OracleComp.IsCostBounded.bind (hiter (min (Q n) (2 ^ blockLen n)))
    (fun _ => OracleComp.IsCostBounded.pure _ 0)

private theorem run_iterate_wordBirthdayStep (blockLen : ℕ → ℕ) (n : ℕ)
    (f : List Bool → List Bool) (k : ℕ) :
    ProbOracleComp.run (spec := fun _ : Unit × List Bool => List Bool)
        (OracleComp.iterate k (wordBirthdayStep blockLen n) ([], false))
        (fun req => pure (f req.2)) =
      pure (List.ofFn (fun j : Fin k =>
          (f (BitString.lowBits (blockLen n) (k - 1 - j))).take (blockLen n)),
        decide (¬ Function.Injective (fun j : Fin k =>
          (f (BitString.lowBits (blockLen n) j)).take (blockLen n)))) := by
  induction k with
  | zero =>
    change ProbOracleComp.run (spec := fun _ : Unit × List Bool => List Bool)
        (pure ([], false)) (fun req => pure (f req.2)) =
      pure ([], decide (¬ Function.Injective (Fin.elim0 : Fin 0 → List Bool)))
    simp [Function.injective_of_subsingleton]
  | succ k ih =>
    rw [OracleComp.iterate_succ, ProbOracleComp.run_bind, ih]
    simp only [wordBirthdayStep, ProbOracleComp.run_bind, ProbOracleComp.run_query,
      ProbOracleComp.run_pure]
    refine congrArg (pure : _ → ProbComp _) (Prod.ext ?_ ?_)
    · rw [List.ofFn_succ]
      refine congrArg₂ List.cons ?_ ?_
      · simp
      · refine congrArg List.ofFn (funext fun j => ?_)
        simp only [Fin.val_succ]
        congr 3
        omega
    · -- The new reply extends the earlier ones (`Fin.snoc`), which the state stores in reverse.
      have hg : (fun j : Fin (k + 1) => (f (BitString.lowBits (blockLen n) j)).take (blockLen n)) =
          Fin.snoc (fun j : Fin k => (f (BitString.lowBits (blockLen n) j)).take (blockLen n))
            ((f (BitString.lowBits (blockLen n) k)).take (blockLen n)) :=
        (Fin.snoc_init_self _).symm
      have hrev : (fun j : Fin k =>
            (f (BitString.lowBits (blockLen n) (k - 1 - j))).take (blockLen n)) =
          (fun j : Fin k => (f (BitString.lowBits (blockLen n) j)).take (blockLen n)) ∘
            Fin.rev := by
        funext j
        simp only [Function.comp_apply, Fin.val_rev]
        congr 3
        omega
      rw [Bool.eq_iff_iff]
      simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, List.length_ofFn, hrev,
        List.mem_ofFn', Fin.rev_surjective.range_comp, exists_eq_right, hg, Fin.snoc_injective_iff,
        not_and_or, not_not]

/-- Deterministic execution of `wordBirthdayDistinguisher` against an arbitrary word oracle `f`. -/
theorem run_wordBirthdayDistinguisher (blockLen Q : ℕ → ℕ) (n : ℕ)
    (f : List Bool → List Bool) :
    (wordBirthdayDistinguisher blockLen Q n []).run (fun req => pure (f req.2)) =
      pure (decide (¬ Function.Injective (fun j : Fin (min (Q n) (2 ^ blockLen n)) =>
        (f (BitString.lowBits (blockLen n) j)).take (blockLen n)))) := by
  rw [wordBirthdayDistinguisher, ProbOracleComp.run_map, run_iterate_wordBirthdayStep]
  simp

/-- Against `randomFunctionOracle`, `wordBirthdayDistinguisher` matches the finite distinguisher
`PRP.birthdayDistinguisher` on `birthdayQueries`. -/
theorem run_wordBirthdayDistinguisher_randomFunctionOracle (blockLen Q : ℕ → ℕ) (n : ℕ)
    (f : BitString (blockLen n) → BitString (blockLen n)) :
    (wordBirthdayDistinguisher blockLen Q n []).run
        (fun req => pure (randomFunctionOracle (blockLen n) f req.2)) =
      (PRP.birthdayDistinguisher
          (birthdayQueries (blockLen n) (min (Q n) (2 ^ blockLen n)))).run
        (fun d => pure (f d)) := by
  rw [run_wordBirthdayDistinguisher, PRP.run_birthdayDistinguisher]
  congr 2
  refine propext (not_congr ?_)
  constructor
  · intro hinj i j hij
    apply hinj
    have hij' := congrArg List.ofFn hij
    simpa [randomFunctionOracle, BitString.length_lowBits, birthdayQueries,
      List.take_of_length_le List.length_ofFn.le] using hij'
  · intro hinj i j hij
    apply hinj
    have hij' := congrArg (BitString.ofList (blockLen n)) hij
    simpa [randomFunctionOracle, BitString.length_lowBits, birthdayQueries,
      List.take_of_length_le List.length_ofFn.le, BitString.ofList_ofFn] using hij'

/-- Output distribution of `wordBirthdayDistinguisher` in `E.prpRealGame` coincides with
`PRP.realExperiment` on `E.permEquiv`. -/
theorem eval_prpRealGame_wordBirthdayDistinguisher (E : BlockCipher) (Q : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (E.prpRealGame (wordBirthdayDistinguisher E.blockLen Q) n) =
      ProbComp.eval (PRP.realExperiment
        (fun k : BitString (E.keyLen n) => E.permEquiv n (List.ofFn k) List.length_ofFn)
        (PRP.birthdayDistinguisher
          (birthdayQueries (E.blockLen n) (min (Q n) (2 ^ E.blockLen n))))) := by
  rw [BlockCipher.prpRealGame, ProbComp.eval_bind, BitString.eval_sampleList,
    BitString.uniformList, PMF.bind_map, PRP.realExperiment, PRF.eval_realExperiment]
  congr 1 with key : 1
  dsimp only [Function.comp_def]
  simp_rw [E.prpOracle_eq_randomPermOracle (hkey := List.length_ofFn), randomPermOracle]
  simpa only [ProbOracleComp.eval_run, ProbComp.eval_pure] using
    congrArg ProbComp.eval (run_wordBirthdayDistinguisher_randomFunctionOracle E.blockLen Q n
      ⇑(E.permEquiv n (List.ofFn key) List.length_ofFn))

/-- In `E.prpRealGame`, `wordBirthdayDistinguisher` outputs `false` almost surely. -/
theorem eval_prpRealGame_wordBirthdayDistinguisher_pure_false (E : BlockCipher) (Q : ℕ → ℕ)
    (n : ℕ) :
    ProbComp.eval (E.prpRealGame (wordBirthdayDistinguisher E.blockLen Q) n) = PMF.pure false := by
  rw [eval_prpRealGame_wordBirthdayDistinguisher]
  exact PRP.eval_realExperiment_birthdayDistinguisher _
    (injective_birthdayQueries (Nat.min_le_right _ _))

/-- Output distribution of `wordBirthdayDistinguisher` in `prfIdealGame` coincides with
`PRF.idealExperiment` on `PRP.birthdayDistinguisher`. -/
theorem eval_prfIdealGame_wordBirthdayDistinguisher (blockLen Q : ℕ → ℕ) (n : ℕ) :
    ProbComp.eval (prfIdealGame blockLen blockLen (wordBirthdayDistinguisher blockLen Q) n) =
      ProbComp.eval (PRF.idealExperiment
        (PRP.birthdayDistinguisher
          (birthdayQueries (blockLen n) (min (Q n) (2 ^ blockLen n))))) := by
  rw [prfIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform, PRF.eval_idealExperiment]
  congr 1 with f : 1
  simpa only [ProbOracleComp.eval_run, ProbComp.eval_pure] using
    congrArg ProbComp.eval (run_wordBirthdayDistinguisher_randomFunctionOracle blockLen Q n f)

/-- Exact real-valued advantage of `wordBirthdayDistinguisher` between `E.prpRealGame` and
`prfIdealGame`. -/
theorem coe_advantage_wordBirthdayDistinguisher (E : BlockCipher) (Q : ℕ → ℕ) (n : ℕ) :
    (Game.advantage
      (ProbComp.eval (E.prpRealGame (wordBirthdayDistinguisher E.blockLen Q) n))
      (ProbComp.eval (prfIdealGame E.blockLen E.blockLen
        (wordBirthdayDistinguisher E.blockLen Q) n)) : ℝ) =
      1 - ((2 ^ E.blockLen n).descFactorial (min (Q n) (2 ^ E.blockLen n)) : ℝ) /
        ((2 : ℝ) ^ E.blockLen n) ^ (min (Q n) (2 ^ E.blockLen n)) := by
  rw [eval_prpRealGame_wordBirthdayDistinguisher, eval_prfIdealGame_wordBirthdayDistinguisher]
  simpa [BitString.card] using PRP.coe_advantage_birthdayDistinguisher
    (fun k : BitString (E.keyLen n) => E.permEquiv n (List.ofFn k) List.length_ofFn)
    (injective_birthdayQueries (Nat.min_le_right _ _))

/-- Concrete quadratic birthday lower bound on `wordBirthdayDistinguisher` against
`E.prpRealGame` vs `prfIdealGame`. -/
theorem min_le_advantage_wordBirthdayDistinguisher (E : BlockCipher) (Q : ℕ → ℕ) (n : ℕ) :
    let q := min (Q n) (2 ^ E.blockLen n)
    min ((q : ℝ) * (q - 1) / (4 * (2 : ℝ) ^ E.blockLen n)) 0.63 ≤
      (Game.advantage
        (ProbComp.eval (E.prpRealGame (wordBirthdayDistinguisher E.blockLen Q) n))
        (ProbComp.eval (prfIdealGame E.blockLen E.blockLen
          (wordBirthdayDistinguisher E.blockLen Q) n)) : ℝ) := by
  rw [eval_prpRealGame_wordBirthdayDistinguisher, eval_prfIdealGame_wordBirthdayDistinguisher]
  simpa [BitString.card] using PRP.min_le_advantage_birthdayDistinguisher
    (fun k : BitString (E.keyLen n) => E.permEquiv n (List.ofFn k) List.length_ofFn)
    (injective_birthdayQueries (Nat.min_le_right _ _))

/-- Constant `1 / 2` lower bound once `1 ≤ E.blockLen n` and `2 ^ E.blockLen n ≤ Q n`. -/
theorem half_le_advantage_wordBirthdayDistinguisher (E : BlockCipher) (Q : ℕ → ℕ) {n : ℕ}
    (hpos : 1 ≤ E.blockLen n) (hQ : 2 ^ E.blockLen n ≤ Q n) :
    (1 / 2 : ℝ≥0) ≤
      Game.advantage
        (ProbComp.eval (E.prpRealGame (wordBirthdayDistinguisher E.blockLen Q) n))
        (ProbComp.eval (prfIdealGame E.blockLen E.blockLen
          (wordBirthdayDistinguisher E.blockLen Q) n)) := by
  rw [eval_prpRealGame_wordBirthdayDistinguisher, eval_prfIdealGame_wordBirthdayDistinguisher]
  have hmin : min (Q n) (2 ^ E.blockLen n) = 2 ^ E.blockLen n := min_eq_right hQ
  have hcard : 2 ≤ Fintype.card (BitString (E.blockLen n)) := by
    simpa [BitString.card] using Nat.pow_le_pow_right Nat.two_pos hpos
  exact_mod_cast PRP.half_le_advantage_birthdayDistinguisher_of_bijective
    (fun k : BitString (E.keyLen n) => E.permEquiv n (List.ofFn k) List.length_ofFn)
    (hmin ▸ bijective_birthdayQueries) hcard

/-- Exact real-valued PRF advantage of `wordBirthdayDistinguisher` for a `BlockCipher` with
`E.keyLen = id`. -/
theorem BlockCipher.coe_prfAdvantage_wordBirthdayDistinguisher (E : BlockCipher)
    (hkey : E.keyLen = id) (Q : ℕ → ℕ) (n : ℕ) :
    (Game.advantage
      (ProbComp.eval (prfRealGame E.blockLen
        (fun key query => E.encrypt key.length key query)
        (wordBirthdayDistinguisher E.blockLen Q) n))
      (ProbComp.eval (prfIdealGame E.blockLen E.blockLen
        (wordBirthdayDistinguisher E.blockLen Q) n)) : ℝ) =
      1 - ((2 ^ E.blockLen n).descFactorial (min (Q n) (2 ^ E.blockLen n)) : ℝ) /
        ((2 : ℝ) ^ E.blockLen n) ^ (min (Q n) (2 ^ E.blockLen n)) := by
  rw [← eval_prpRealGame_eq_eval_prfRealGame hkey, coe_advantage_wordBirthdayDistinguisher]

/-- Quadratic birthday lower bound on the PRF advantage of `wordBirthdayDistinguisher` for a
`BlockCipher` with `E.keyLen = id`. -/
theorem BlockCipher.min_le_prfAdvantage_wordBirthdayDistinguisher (E : BlockCipher)
    (hkey : E.keyLen = id) (Q : ℕ → ℕ) (n : ℕ) :
    let q := min (Q n) (2 ^ E.blockLen n)
    min ((q : ℝ) * (q - 1) / (4 * (2 : ℝ) ^ E.blockLen n)) 0.63 ≤
      (Game.advantage
        (ProbComp.eval (prfRealGame E.blockLen
          (fun key query => E.encrypt key.length key query)
          (wordBirthdayDistinguisher E.blockLen Q) n))
        (ProbComp.eval (prfIdealGame E.blockLen E.blockLen
          (wordBirthdayDistinguisher E.blockLen Q) n)) : ℝ) := by
  rw [← eval_prpRealGame_eq_eval_prfRealGame hkey]
  exact min_le_advantage_wordBirthdayDistinguisher E Q n

/-- Constant `1 / 2` PRF advantage lower bound once `1 ≤ E.blockLen n` and
`2 ^ E.blockLen n ≤ Q n`. -/
theorem BlockCipher.half_le_prfAdvantage_wordBirthdayDistinguisher (E : BlockCipher)
    (hkey : E.keyLen = id) (Q : ℕ → ℕ) {n : ℕ}
    (hpos : 1 ≤ E.blockLen n) (hQ : 2 ^ E.blockLen n ≤ Q n) :
    (1 / 2 : ℝ≥0) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame E.blockLen
          (fun key query => E.encrypt key.length key query)
          (wordBirthdayDistinguisher E.blockLen Q) n))
        (ProbComp.eval (prfIdealGame E.blockLen E.blockLen
          (wordBirthdayDistinguisher E.blockLen Q) n)) := by
  rw [← eval_prpRealGame_eq_eval_prfRealGame hkey]
  exact half_le_advantage_wordBirthdayDistinguisher E Q hpos hQ

end Semantics

section Asymptotics

private theorem exists_freq_le_poly_of_not_negligible_inv_two_pow {f : ℕ → ℕ}
    (hf : ¬ Negligible fun n => if f n = 0 then (0 : ℝ≥0) else ((2 : ℝ≥0) ^ f n)⁻¹) :
    ∃ k c : ℕ, 0 < c ∧ ∃ᶠ n in atTop, 1 ≤ f n ∧ 2 ^ f n ≤ c * (n + 1) ^ k := by
  rw [negligible_iff] at hf
  push Not at hf
  obtain ⟨k, δ, hδ, hfreq⟩ := hf
  refine ⟨k, Nat.ceil (δ⁻¹ : ℝ≥0) + 1, Nat.succ_pos _, Filter.frequently_atTop.mpr fun m => ?_⟩
  obtain ⟨n, hn_ge, hn⟩ := hfreq m
  refine ⟨n, hn_ge, ?_⟩
  by_cases h0 : f n = 0
  · simp only [h0, ↓reduceIte, mul_zero] at hn
    exact absurd hn (not_le_of_gt hδ)
  · simp only [h0, ↓reduceIte] at hn
    refine ⟨Nat.one_le_iff_ne_zero.mpr h0, ?_⟩
    have hpow : (2 : ℝ≥0) ^ f n ≤ δ⁻¹ * (n : ℝ≥0) ^ k := by
      calc (2 : ℝ≥0) ^ f n = δ⁻¹ * δ * (2 : ℝ≥0) ^ f n := by rw [inv_mul_cancel₀ hδ.ne', one_mul]
        _ ≤ δ⁻¹ * ((n : ℝ≥0) ^ k * ((2 : ℝ≥0) ^ f n)⁻¹) * (2 : ℝ≥0) ^ f n := by gcongr
        _ = δ⁻¹ * (n : ℝ≥0) ^ k := by
          rw [mul_assoc, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ two_ne_zero), mul_one]
    have hc : δ⁻¹ ≤ ((Nat.ceil (δ⁻¹ : ℝ≥0) + 1 : ℕ) : ℝ≥0) := by
      calc δ⁻¹ ≤ (Nat.ceil (δ⁻¹ : ℝ≥0) : ℝ≥0) := Nat.le_ceil _
        _ ≤ ((Nat.ceil (δ⁻¹ : ℝ≥0) + 1 : ℕ) : ℝ≥0) := by exact_mod_cast Nat.le_add_right _ 1
    have hnn : (n : ℝ≥0) ≤ ((n : ℝ≥0) + 1) := le_add_of_nonneg_right zero_le
    have hreal : ((2 ^ f n : ℕ) : ℝ≥0) ≤
        ((Nat.ceil (δ⁻¹ : ℝ≥0) + 1 : ℕ) : ℝ≥0) * ((n + 1 : ℕ) : ℝ≥0) ^ k := by
      push_cast at hc ⊢
      exact hpow.trans (mul_le_mul' hc (pow_le_pow_left' hnn k))
    exact_mod_cast hreal

/-- If `((2 : ℝ≥0) ^ E.blockLen n)⁻¹` on nonzero blocks is not negligible, `E.prpRealGame` and
`prfIdealGame` are not indistinguishable for PPT adversaries: some PPT adversary distinguishes them,
namely `wordBirthdayDistinguisher` with a polynomial query count, whose advantage is at least
`1 / 2` for infinitely many `n`. -/
theorem BlockCipher.not_indistinguishable_prpRealGame_prfIdealGame {E : BlockCipher}
    (hnot : ¬ Negligible fun n =>
      if E.blockLen n = 0 then (0 : ℝ≥0) else ((2 : ℝ≥0) ^ E.blockLen n)⁻¹) :
    ¬ Game.Indistinguishable
      (fun adversary n => ProbComp.eval (E.prpRealGame adversary n))
      (fun adversary n => ProbComp.eval (prfIdealGame E.blockLen E.blockLen adversary n))
      (IsOraclePPT encBool) := by
  obtain ⟨k, c, -, hfreq⟩ := exists_freq_le_poly_of_not_negligible_inv_two_pow hnot
  let Q : ℕ → ℕ := fun n => c * (n + 1) ^ k
  intro hind
  have hadv := isOraclePPT_wordBirthdayDistinguisher (Q := Q) E.blockLen_polyTime
    (ComputableInPolyTime.unary_mul' (ComputableInPolyTime.const c)
      ((ComputableInPolyTime.unary_pow k).comp (by polytime)))
  refine not_negligible_of_frequently_ge (by norm_num : (1 / 2 : ℝ≥0) ≠ 0) ?_
    (hind (wordBirthdayDistinguisher E.blockLen Q) hadv)
  exact hfreq.mono fun n ⟨hpos, hQ⟩ =>
    half_le_advantage_wordBirthdayDistinguisher E Q hpos hQ

/-- Necessity of super-polynomial block size in
`BlockCipher.prp_iff_pseudorandomFunctionOver_of_keyLen_eq_id`:
when `E.keyLen = id`, `1 ≤ E.blockLen n` eventually, and `((2 : ℝ≥0) ^ E.blockLen n)⁻¹` is not
negligible, `E` cannot be a `PseudorandomFunctionOver` `E.blockLen` `E.blockLen`. -/
theorem BlockCipher.not_pseudorandomFunctionOver_of_not_negligible {E : BlockCipher}
    (hkey : E.keyLen = id) (hpos : ∀ᶠ n in atTop, 1 ≤ E.blockLen n)
    (hnot : ¬ Negligible fun n => ((2 : ℝ≥0) ^ E.blockLen n)⁻¹) :
    ¬ PseudorandomFunctionOver E.blockLen E.blockLen
      (fun key query => E.encrypt key.length key query) := by
  have hnot' : ¬ Negligible fun n =>
      if E.blockLen n = 0 then (0 : ℝ≥0) else ((2 : ℝ≥0) ^ E.blockLen n)⁻¹ := fun hzero =>
    hnot (hzero.congr' (hpos.mono fun _ hn => by simp [Nat.ne_of_gt hn]))
  refine fun hprf => E.not_indistinguishable_prpRealGame_prfIdealGame hnot' fun A hA => ?_
  simpa only [eval_prpRealGame_eq_eval_prfRealGame hkey A] using hprf.secure A hA

end Asymptotics

end

end Cslib.Crypto
