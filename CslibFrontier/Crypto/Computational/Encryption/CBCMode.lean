/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Encryption.RandomFunctionHybrid
public import CslibFrontier.Crypto.Primitives.BlockCipher.Modes
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Crypto.Primitives.PRP.Finite
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Probability.PMF.Support

/-!
# CBC mode with a random IV: typed random-function, random-permutation and keyed bounds

Cipher block chaining with a random initialization vector ([BonehShoup2023], Section 5.4.3,
printed pp. 194–195) encrypts the blocks `m₁, …, m_k` under a block function `f` as `c₀ = iv`
uniform and `cᵢ = f (cᵢ₋₁ + mᵢ)` (`cbcEncryptBlocks`). Theorem 5.4 of [BonehShoup2023]
(printed pp. 195–199) states that it is CPA secure for a secure block cipher, with bound (5.22),
`CPAadv ≤ 2 Q² ℓ² / N + 2 BCadv`, for `Q` queries of at most `ℓ` blocks over `N` blocks.

This file proves the concrete typed steps of Theorem 5.4, not the asymptotic theorem: Games 1 to 3
and bound (5.28) against a uniform random function, the resulting bound with the block cipher
replaced by a uniform random permutation of `BitString n`, and the concrete keyed PRF and
block-cipher bounds (`advantage_cbcCpaGame_prf_le` and `advantage_cbcCpaGame_le`). The security
notion is the left-or-right experiment of `RandomFunctionHybrid.lean` (`blockModeCpaExperiment`),
and the advantage is the distance between the experiments for the two challenge bits, the book's
`CPAadv`. The word-level cipher, the certified oracle-PPT distinguisher and the asymptotic Theorem
5.4 are in `CslibFrontier/Crypto/Computational/Encryption/CBCMode/Uniform.lean`.

The proof:
1. The CBC experiment is the real PRF experiment for the reduction `cbcReduction`, which computes
   each ciphertext with its oracle (`cbcCpaGame_eq_realExperiment`, an application of
   `blockModeCpaExperiment_eq_realExperiment_simulate`); the reduction makes one oracle call per
   block (`isQueryBounded_cbcReduction`).
2. Against a uniform random function sampled afresh, every ciphertext block is uniform, and a
   query of `k` blocks against a table of `t` inputs repeats an input with probability at most
   `(k t + k.choose 2) / 2 ^ n` (`toOuterMeasure_badChain_le`). The generic step
   `advantage_idealExperiment_simulate_le` of `RandomFunctionHybrid.lean` then bounds the distance
   to `blockModeIdealExperiment` by `K.choose 2 / 2 ^ n` when the queries ask at most `K` blocks in
   total (`advantage_idealExperiment_cbcReduction_le`).
3. The ideal experiment does not depend on the challenge bit. With the PRP/PRF switching bound
   `PRP.advantage_idealExperiment_prfIdealExperiment_le` (Theorem 4.6; the book's proof cites its
   block-cipher form, Theorem 4.4) for each bit, the advantage against a uniform random
   permutation is at most `4 K.choose 2 / 2 ^ n` (`advantage_cbcCpaGame_randomPermutation_le`).
4. For a keyed function `F`, combining `cbcCpaGame_eq_realExperiment` with the two random-function
   hybrids bounds the CPA advantage by the two PRF advantages plus `2 K.choose 2 / 2 ^ n`
   (`advantage_cbcCpaGame_prf_le`). For a keyed permutation `E`, applying
   `PRP.prfAdvantage_le_advantage_add` (Theorem 4.4) to each `K`-query reduction gives the keyed
   bound `PRP.advantage E (cbcReduction ℓ false adversary) +
   PRP.advantage E (cbcReduction ℓ true adversary) + 4 K.choose 2 / 2 ^ n`
   (`advantage_cbcCpaGame_le`).

The bounds hold for every adversary. The query bound of the reduction is proved
(`isQueryBounded_cbcReduction`); no running-time certificate is claimed here (tracked in #4894 and
#5293 section 2).

Comparison with the book:
* `K` counts the blocks of all queries. With `Q` queries of at most `ℓ` blocks, `K ≤ Q ℓ`, so the
  per-bit random-function bound `K.choose 2 / 2 ^ n` is at most (5.28)'s `Q² ℓ² / (2N)`, and
  `4 K.choose 2 / 2 ^ n ≤ 2 Q² ℓ² / N`, the additive term of (5.22).
* Equation (5.22) uses one coin-flipping block-cipher distinguisher with factor `2`
  (`2 BCadv[B, E]`); `advantage_cbcCpaGame_le` sums the PRP advantages of the two fixed-bit
  reductions `cbcReduction ℓ false adversary` and `cbcReduction ℓ true adversary`.
* On p. 199 the book states the bit-guessing bound before the switching step as
  `CPAadv* ≤ Q² ℓ² / N + PRFadv[B, E]`. This is a misprint in one displayed line: the printed
  inequality is true but too weak; (5.22)/(5.23)/(5.28) stand. For a uniform random function the
  bound proved here gives `CPAadv* = CPAadv / 2 ≤ K.choose 2 / 2 ^ n ≤ Q² ℓ² / (2N)`, the
  constant that steps (5.24)–(5.29) give.
* The bit-guessing form (5.23) is half of (5.22) and is not stated separately.
* A query whose two messages differ in length, or exceed `ℓ` blocks, encrypts the empty message
  and costs nothing (`blockModeSelect`); the book requires equal-length messages of at most `ℓ`
  blocks. `ℓ = 0` is allowed.

## Main definitions

* `Cslib.Crypto.cbcCpaGame`: the CBC left-or-right experiment for a keyed block function.
* `Cslib.Crypto.cbcChainQueries`, `Cslib.Crypto.cbcQueryProgram`, `Cslib.Crypto.cbcReduction`:
  the PRF distinguisher built from a `BlockModeAdversary`.

## Main results

* `Cslib.Crypto.cbcCpaGame_eq_realExperiment`: the CBC experiment is the real PRF experiment for
  the reduction.
* `Cslib.Crypto.isQueryBounded_cbcReduction`: the reduction makes at most `K` oracle calls.
* `Cslib.Crypto.advantage_idealExperiment_cbcReduction_le`: with a uniform random function, the
  reduction's view is within `K.choose 2 / 2 ^ n` of `blockModeIdealExperiment`.
* `Cslib.Crypto.advantage_cbcCpaGame_randomFunction_le`: CBC mode with a uniform random function
  has left-or-right advantage at most `2 K.choose 2 / 2 ^ n`.
* `Cslib.Crypto.advantage_cbcCpaGame_randomPermutation_le`: CBC mode with a uniform random
  permutation has left-or-right advantage at most `4 K.choose 2 / 2 ^ n`.
* `Cslib.Crypto.advantage_cbcCpaGame_prf_le`: keyed PRF CPA bound for CBC mode.
* `Cslib.Crypto.advantage_cbcCpaGame_le`: keyed block-cipher CPA bound for CBC mode, corresponding
  to (5.22).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 5.4.3, Theorem 5.4 and its proof, (5.22) and (5.28); Theorems 4.4 and 4.6.
-/

public section

namespace Cslib.Crypto

open Cslib.Probability
open scoped ENNReal

variable {n : ℕ}

/-- The CBC left-or-right experiment for the keyed block function `F` with challenge bit `b`
([BonehShoup2023], Attack Game 5.2, Section 5.4.3): a uniform key, then the adversary with access
to random-IV CBC encryption under that key. -/
@[expose]
noncomputable def cbcCpaGame {Key : Type} [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool) (adversary : BlockModeAdversary n) :
    Game :=
  ProbComp.eval (blockModeCpaExperiment (fun key => cbcEncryptBlocks (F key)) ℓ b adversary)

/-- The CBC ciphertext blocks of `ms` from chaining value `c`, computed with one call to the
function oracle per block: the input of each call is the previous ciphertext block plus the next
message block. -/
@[expose]
def cbcChainQueries :
    BitString n → List (BitString n) →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n))
  | _, [] => pure []
  | c, m :: ms => do
    let c' ← ProbOracleComp.query (c + m)
    let cs ← cbcChainQueries c' ms
    return c' :: cs

/-- One CBC encryption computed with a function oracle: a private uniform initialization vector,
then the ciphertext blocks of the selected plaintext from the oracle. -/
@[expose]
noncomputable def cbcQueryProgram (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n) :
    ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)) := do
  let iv ← ProbOracleComp.sample (ProbComp.uniform (BitString n))
  let cs ← cbcChainQueries iv (blockModeSelect ℓ b q)
  return (iv, cs)

/-- The PRF distinguisher built from a left-or-right adversary against CBC mode ([BonehShoup2023],
proof of Theorem 5.4, adversary `B`): run the adversary and answer each query by CBC encryption
with the oracle, under the challenge bit `b`. -/
@[expose]
noncomputable def cbcReduction (ℓ : ℕ) (b : Bool) (adversary : BlockModeAdversary n) :
    PRF.Adversary (BitString n) (BitString n) :=
  ProbOracleComp.simulate (cbcQueryProgram ℓ b) adversary

/-- Answering the chain calls with a fixed function `f` computes CBC encryption under `f`. -/
theorem run_cbcChainQueries (f : BitString n → BitString n) (c : BitString n)
    (ms : List (BitString n)) :
    (cbcChainQueries c ms).run (fun y => pure (f y)) = pure (cbcEncryptBlocks f c ms) := by
  induction ms generalizing c with
  | nil => rfl
  | cons m ms ih =>
    simp only [cbcChainQueries, cbcEncryptBlocks, ProbOracleComp.run_bind,
      ProbOracleComp.run_query, ih, pure_bind, ProbOracleComp.run_pure]

/-- The CBC experiment for the keyed block function `F` is the real PRF experiment for `F` and
the reduction `cbcReduction ℓ b adversary`. -/
theorem cbcCpaGame_eq_realExperiment {Key : Type} [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool) (adversary : BlockModeAdversary n) :
    cbcCpaGame F ℓ b adversary =
      ProbComp.eval (PRF.realExperiment F (cbcReduction ℓ b adversary)) :=
  congrArg ProbComp.eval <| blockModeCpaExperiment_eq_realExperiment_simulate _ _ F ℓ b adversary
    fun key q => by
      simp only [blockModeOracle, cbcQueryProgram, ProbOracleComp.run_bind,
        ProbOracleComp.run_sample, run_cbcChainQueries, pure_bind, ProbOracleComp.run_pure]

/-- The chain makes one oracle call per block. -/
theorem isQueryBounded_cbcChainQueries (c : BitString n) (ms : List (BitString n)) :
    ProbOracleComp.IsQueryBounded (cbcChainQueries c ms) ms.length := by
  induction ms generalizing c with
  | nil =>
    simp only [cbcChainQueries]
    exact OracleComp.IsCostBounded.pure _ _
  | cons m ms ih =>
    simp only [cbcChainQueries]
    exact OracleComp.IsCostBounded.mono
      (OracleComp.IsCostBounded.bind (OracleComp.IsCostBounded.query (Sum.inr (c + m)))
        fun c' => OracleComp.IsCostBounded.bind (ih c') fun cs =>
          OracleComp.IsCostBounded.pure (c' :: cs) 0)
      (by simp only [Sum.elim_inr, List.length_cons]; omega)

/-- If the queries of `adversary` ask at most `K` blocks in total, the reduction makes at most
`K` oracle calls. -/
theorem isQueryBounded_cbcReduction (ℓ : ℕ) (b : Bool) {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    ProbOracleComp.IsQueryBounded (cbcReduction ℓ b adversary) K := by
  refine ProbOracleComp.isCostBounded_simulate (cost := blockModeBlocks ℓ) (fun q => ?_) h
  have hq := OracleComp.IsCostBounded.bind
    (ProbOracleComp.isCostBounded_sample (spec := fun _ : BitString n => BitString n)
      (fun _ => 1) (ProbComp.uniform (BitString n))) fun iv =>
    OracleComp.IsCostBounded.bind (isQueryBounded_cbcChainQueries iv (blockModeSelect ℓ b q))
      fun cs => OracleComp.IsCostBounded.pure (iv, cs) 0
  exact OracleComp.IsCostBounded.mono hq (by simp)

/-! ### Fresh sampling -/

/-- The table after fresh sampling along the chain of `ms` from `c` with draws `us`: each draw is
recorded under the input that produced it. -/
private def cbcChainCache :
    List (BitString n × BitString n) → BitString n → List (BitString n) → List (BitString n) →
      List (BitString n × BitString n)
  | t, c, m :: ms, u :: us => cbcChainCache ((c + m, u) :: t) u ms us
  | t, _, _, _ => t

/-- Whether fresh sampling along the chain of `ms` from `c` with draws `us` meets an input
already in the table. -/
private def cbcChainFlag :
    List (BitString n × BitString n) → BitString n → List (BitString n) → List (BitString n) → Bool
  | t, c, m :: ms, u :: us => (t.lookup (c + m)).isSome || cbcChainFlag ((c + m, u) :: t) u ms us
  | _, _, _, _ => false

private theorem length_cbcChainCache (t : List (BitString n × BitString n)) (c : BitString n)
    (ms us : List (BitString n)) (h : us.length = ms.length) :
    (cbcChainCache t c ms us).length = t.length + ms.length := by
  induction ms generalizing t c us with
  | nil => simp [cbcChainCache]
  | cons m ms ih =>
    cases us with
    | nil => simp at h
    | cons u us =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [cbcChainCache, ih _ _ _ h, List.length_cons]
      omega

private theorem not_goodChain_of_cbcChainFlag (t : List (BitString n × BitString n))
    (c : BitString n) (ms us : List (BitString n)) (h : cbcChainFlag t c ms us = true) :
    ¬goodChain (t.map Prod.fst) c ms us := by
  induction ms generalizing t c us with
  | nil => simp [cbcChainFlag] at h
  | cons m ms ih =>
    cases us with
    | nil => simp [cbcChainFlag] at h
    | cons u us =>
      simp only [goodChain, not_and]
      intro hc
      simp only [cbcChainFlag, Bool.or_eq_true] at h
      rcases h with h | h
      · obtain ⟨p, hp, hcp⟩ := List.lookup_isSome_iff.1 h
        exact absurd (List.mem_map.2 ⟨p, hp, (beq_iff_eq.1 hcp).symm⟩) hc
      · exact ih ((c + m, u) :: t) u us h

/-- Fresh sampling along the chain of `ms` draws `ms.length` uniform blocks, which are the
ciphertext blocks. -/
private theorem runWith_freshStep_cbcChainQueries (c : BitString n) (ms : List (BitString n))
    (s : FlagState n) :
    ProbOracleComp.runWith freshStep (cbcChainQueries c ms) s =
      (uniformBlocks ms.length).map fun us =>
        (us, (cbcChainCache s.1 c ms us, s.2 || cbcChainFlag s.1 c ms us)) := by
  induction ms generalizing c s with
  | nil => simp [cbcChainQueries, cbcChainCache, cbcChainFlag]
  | cons m ms ih =>
    simp only [cbcChainQueries, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_query,
      ProbOracleComp.runWith_pure, freshStep, List.length_cons, uniformBlocks_succ]
    rw [PMF.bind_map, PMF.map_bind]
    refine congrArg _ (funext fun u => ?_)
    simp only [Function.comp_def, ih, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind,
      cbcChainCache, cbcChainFlag, Bool.or_assoc]

/-- One CBC encryption under fresh sampling: a uniform initialization vector and uniform
ciphertext blocks. -/
private theorem runWith_freshStep_cbcQueryProgram (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n)
    (s : FlagState n) :
    ProbOracleComp.runWith freshStep (cbcQueryProgram ℓ b q) s =
      ((PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (blockModeSelect ℓ b q).length).map (iv, ·)).map fun p =>
          (p, (cbcChainCache s.1 p.1 (blockModeSelect ℓ b q) p.2,
            s.2 || cbcChainFlag s.1 p.1 (blockModeSelect ℓ b q) p.2)) := by
  simp only [cbcQueryProgram, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbComp.eval_uniform, runWith_freshStep_cbcChainQueries, ProbOracleComp.runWith_pure,
    PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind]

private theorem map_unit_runWith_freshStep_cbcQueryProgram (ℓ : ℕ) (b : Bool)
    (q : BlockModeQuery n) (s : FlagState n) :
    (ProbOracleComp.runWith freshStep (cbcQueryProgram ℓ b q) s).map (fun x => (x.1, ())) =
      (ProbComp.eval (blockModeIdealOracle ℓ q)).map (·, ()) := by
  rw [runWith_freshStep_cbcQueryProgram, eval_blockModeIdealOracle, PMF.map_comp,
    length_blockModeSelect]
  rfl

private theorem length_of_mem_support_cbcQueryProgram (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n)
    (s : FlagState n) (x : (BitString n × List (BitString n)) × FlagState n)
    (hx : x ∈ (ProbOracleComp.runWith freshStep (cbcQueryProgram ℓ b q) s).support) :
    x.2.1.length = s.1.length + blockModeBlocks ℓ q := by
  rw [runWith_freshStep_cbcQueryProgram, PMF.support_map] at hx
  obtain ⟨⟨iv, us⟩, hp, rfl⟩ := hx
  have hlen : us.length = (blockModeSelect ℓ b q).length :=
    length_snd_of_mem_support_uniformDraws hp
  rw [length_cbcChainCache _ _ _ _ hlen, length_blockModeSelect]

private theorem toOuterMeasure_repeated_cbcQueryProgram_le (ℓ : ℕ) (b : Bool)
    (q : BlockModeQuery n) (s : FlagState n) (hs : ¬s.2 = true) :
    (ProbOracleComp.runWith freshStep (cbcQueryProgram ℓ b q) s).toOuterMeasure
        {x | x.2.2 = true} ≤
      ((blockModeBlocks ℓ q * s.1.length + (blockModeBlocks ℓ q).choose 2 : ℕ) : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [runWith_freshStep_cbcQueryProgram, PMF.toOuterMeasure_map_apply]
  have hbad := toOuterMeasure_badChain_le (blockModeSelect ℓ b q) (s.1.map Prod.fst)
  rw [List.length_map] at hbad
  refine le_trans (PMF.toOuterMeasure_mono _ ?_) (hbad.trans_eq ?_)
  · rintro ⟨iv, us⟩ ⟨hflag, -⟩
    have hs' : s.2 = false := by simpa using hs
    have hflag' : cbcChainFlag s.1 iv (blockModeSelect ℓ b q) us = true := by
      simpa [hs'] using hflag
    exact not_goodChain_of_cbcChainFlag s.1 iv _ us hflag'
  · rw [length_blockModeSelect]

/-! ### Security of CBC mode -/

/-- **The reduction against a uniform random function** ([BonehShoup2023], proof of
Theorem 5.4, Games 1 to 3 and (5.28)). If the queries of `adversary` ask at most `K` blocks in
total, then with a uniform random function the output of `cbcReduction ℓ b adversary` is within
`K.choose 2 / 2 ^ n` of `blockModeIdealExperiment`, whatever the challenge bit `b`. -/
theorem advantage_idealExperiment_cbcReduction_le (ℓ : ℕ) (b : Bool)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage (ProbComp.eval (PRF.idealExperiment (cbcReduction ℓ b adversary)))
        (ProbComp.eval (blockModeIdealExperiment ℓ adversary)) : ℝ) ≤
      (K.choose 2 : ℝ) / 2 ^ n :=
  advantage_idealExperiment_simulate_le (cbcQueryProgram ℓ b) ℓ
    (map_unit_runWith_freshStep_cbcQueryProgram ℓ b)
    (toOuterMeasure_repeated_cbcQueryProgram_le ℓ b)
    (fun q s y t f hx => (length_of_mem_support_cbcQueryProgram ℓ b q s (y, t, f) hx).le) h

/-- **CBC mode with a uniform random function.** If the queries of `adversary` ask at most `K`
blocks in total, its left-or-right advantage against CBC mode with a uniform random block
function is at most `2 K.choose 2 / 2 ^ n`. -/
theorem advantage_cbcCpaGame_randomFunction_le (ℓ : ℕ) {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage (cbcCpaGame (fun f : BitString n → BitString n => f) ℓ false adversary)
        (cbcCpaGame (fun f : BitString n → BitString n => f) ℓ true adversary) : ℝ) ≤
      2 * ((K.choose 2 : ℝ) / 2 ^ n) := by
  have e : ∀ b, cbcCpaGame (fun f : BitString n → BitString n => f) ℓ b adversary =
      ProbComp.eval (PRF.idealExperiment (cbcReduction ℓ b adversary)) := fun b => by
    rw [cbcCpaGame_eq_realExperiment]
    rfl
  rw [e, e]
  have h₀ := advantage_idealExperiment_cbcReduction_le ℓ false h
  have h₁ := advantage_idealExperiment_cbcReduction_le ℓ true h
  refine (advantage_le_two _ (ProbComp.eval (blockModeIdealExperiment ℓ adversary)) _).trans ?_
  linarith

/-- **Keyed PRF step of [BonehShoup2023], Theorem 5.4, not the asymptotic theorem** (typed
reduction without a running-time certificate, tracked in #4894 and #5293 section 2; see
`CslibFrontier/Crypto/Computational/Encryption/CBCMode/Uniform.lean` for the certified uniform
theorem). If the queries of `adversary` ask at most `K` blocks in total, its left-or-right
advantage against CBC mode with the keyed function `F` is at most the PRF advantages of
`cbcReduction ℓ false adversary` and `cbcReduction ℓ true adversary`, each making at most `K`
oracle calls (`isQueryBounded_cbcReduction`), plus `2 K.choose 2 / 2 ^ n`. -/
theorem advantage_cbcCpaGame_prf_le {Key : Type} [Fintype Key] [Nonempty Key]
    (F : Key → BitString n → BitString n) (ℓ : ℕ) {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage (cbcCpaGame F ℓ false adversary) (cbcCpaGame F ℓ true adversary) : ℝ) ≤
      PRF.advantage F (cbcReduction ℓ false adversary) +
        PRF.advantage F (cbcReduction ℓ true adversary) + 2 * ((K.choose 2 : ℝ) / 2 ^ n) := by
  rw [cbcCpaGame_eq_realExperiment, cbcCpaGame_eq_realExperiment]
  have h₀ := advantage_idealExperiment_cbcReduction_le ℓ false h
  have h₁ := advantage_idealExperiment_cbcReduction_le ℓ true h
  refine (advantage_le_four _
    (ProbComp.eval (PRF.idealExperiment (cbcReduction ℓ false adversary)))
    (ProbComp.eval (blockModeIdealExperiment ℓ adversary))
    (ProbComp.eval (PRF.idealExperiment (cbcReduction ℓ true adversary))) _).trans ?_
  linarith

/-- **Keyed block-cipher step (5.22) of [BonehShoup2023], Theorem 5.4, not the asymptotic theorem**
(typed reduction without a running-time certificate, tracked in #4894 and #5293 section 2; see
`CslibFrontier/Crypto/Computational/Encryption/CBCMode/Uniform.lean` for the certified uniform
theorem). If the queries of `adversary` ask at most `K` blocks in total, its left-or-right
advantage against CBC mode with the keyed permutation `E` is at most the PRP advantages of
`cbcReduction ℓ false adversary` and `cbcReduction ℓ true adversary`, each making at most `K`
oracle calls (`isQueryBounded_cbcReduction`), plus `4 K.choose 2 / 2 ^ n`. With `Q` queries of at
most `ℓ` blocks, `K ≤ Q ℓ` and `4 K.choose 2 ≤ 2 Q ^ 2 ℓ ^ 2`, matching (5.22). -/
theorem advantage_cbcCpaGame_le {Key : Type} [Fintype Key] [Nonempty Key]
    (E : Key → Equiv.Perm (BitString n)) (ℓ : ℕ) {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage (cbcCpaGame (fun k => ⇑(E k)) ℓ false adversary)
        (cbcCpaGame (fun k => ⇑(E k)) ℓ true adversary) : ℝ) ≤
      PRP.advantage E (cbcReduction ℓ false adversary) +
        PRP.advantage E (cbcReduction ℓ true adversary) + 4 * ((K.choose 2 : ℝ) / 2 ^ n) := by
  have hprf := advantage_cbcCpaGame_prf_le (fun k => ⇑(E k)) ℓ h
  have hs (b : Bool) : (PRF.advantage (fun k => ⇑(E k)) (cbcReduction ℓ b adversary) : ℝ) ≤
      PRP.advantage E (cbcReduction ℓ b adversary) + (K.choose 2 : ℝ) / 2 ^ n := by
    simpa [BitString.card] using
      PRP.prfAdvantage_le_advantage_add E (isQueryBounded_cbcReduction ℓ b h)
  have hs₀ := hs false
  have hs₁ := hs true
  linarith

/-- **CBC mode with a uniform random permutation: a step of the proof of [BonehShoup2023],
Theorem 5.4, not the theorem.** The block cipher is replaced by a uniform random permutation of
`BitString n`. If the queries of `adversary` ask at most `K` blocks in total, its left-or-right
advantage is at most `4 K.choose 2 / 2 ^ n`: `advantage_cbcCpaGame_le` for the identity family on
`Equiv.Perm (BitString n)`. With `Q` queries of at most `ℓ` blocks, `K ≤ Q ℓ` and
`4 K.choose 2 ≤ 2 Q ^ 2 ℓ ^ 2`, the additive term of (5.22). -/
theorem advantage_cbcCpaGame_randomPermutation_le (ℓ : ℕ) {adversary : BlockModeAdversary n}
    {K : ℕ} (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage (cbcCpaGame (fun π : Equiv.Perm (BitString n) => ⇑π) ℓ false adversary)
        (cbcCpaGame (fun π : Equiv.Perm (BitString n) => ⇑π) ℓ true adversary) : ℝ) ≤
      4 * ((K.choose 2 : ℝ) / 2 ^ n) := by
  simpa [PRP.advantage, PRP.realExperiment, PRF.realExperiment, PRP.idealExperiment] using
    advantage_cbcCpaGame_le (id : Equiv.Perm (BitString n) → Equiv.Perm (BitString n)) ℓ h

end Cslib.Crypto
