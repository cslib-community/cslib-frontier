/-
Copyright (c) 2026 Karn Seth, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.BlockCipher.Modes
public import CslibFrontier.Crypto.Primitives.PRF.Finite
public import CslibFrontier.Foundations.Data.BitString.Basic
public import CslibFrontier.Languages.Probabilistic.Oracle.Interaction
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Crypto.Game.UntilBad
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.RunWith
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Support
import CslibFrontier.Tactic.ENNRealToReal
import Mathlib.Tactic.Linarith

/-!
# Lazy-vs-Fresh Random Function Hybrid and Shared Block-Mode CPA Utilities

Shared random-function hybrid and left-or-right block-mode CPA experiment machinery for symmetric
block-cipher modes of operation (such as OFB, CTR and CBC):
- replaces a lazily sampled random function (`PRF.idealExperiment`) by fresh independent uniform
  sampling (`freshStep`) up to the repetition bad event that an oracle query hits a previously
  sampled input;
- provides the mode-independent left-or-right block-mode query/cost/ideal-experiment interface
  (`BlockModeQuery`, `BlockModeSpec`, `BlockModeAdversary`, `blockModeSelect`, `blockModeBlocks`,
  `blockModeCost`, `blockModeOracle`, `blockModeIdealOracle`, `blockModeCpaExperiment`,
  `blockModeIdealExperiment`), generic PRF distinguisher builder (`blockModeQueryProgram`,
  `blockModeReduction`, a `ProbOracleComp.simulate` substitution), real-experiment / query-bound /
  ideal-experiment lifting lemmas (`blockModeCpaExperiment_eq_realExperiment`,
  `isQueryBounded_blockModeReduction`, `freshGame_eq_blockModeIdealExperiment`), and advantage
  triangle helpers;
- for an arbitrary per-query program run by `ProbOracleComp.simulate`, identifies the real
  experiment when each program computes the encryption oracle
  (`blockModeCpaExperiment_eq_realExperiment_simulate`), and reduces the random-function step to
  three per-query facts under fresh sampling: each answer has the law of `blockModeIdealOracle`,
  and a query of `k` blocks against a table of `t` entries adds at most `k` entries and raises the
  flag with probability at most `(k t + k.choose 2) / 2 ^ n`
  (`freshGame_simulate_eq_blockModeIdealExperiment`, `advantage_idealExperiment_simulate_le`).

## Main definitions

* `Cslib.Crypto.FlagState`, `Cslib.Crypto.FlagState.repeated`: association list of queried
  `BitString n` pairs paired with a Boolean repetition flag and its named accessor.
* `Cslib.Crypto.lazyStep`: lazy random-function handler that returns cached outputs on repeats and
  latches the repetition flag.
* `Cslib.Crypto.freshStep`: fresh uniform random-function handler that always samples uniformly and
  latches the repetition flag on repeats.
* `Cslib.Crypto.BlockModeQuery`, `Cslib.Crypto.BlockModeSpec`, `Cslib.Crypto.BlockModeAdversary`:
  left-or-right block-mode queries, oracle spec, and adaptive adversaries.
* `Cslib.Crypto.blockModeSelect`, `Cslib.Crypto.blockModeBlocks`, `Cslib.Crypto.blockModeCost`:
  query selection, block count, and query-block cost.
* `Cslib.Crypto.blockModeOracle`, `Cslib.Crypto.blockModeIdealOracle`,
  `Cslib.Crypto.blockModeCpaExperiment`, `Cslib.Crypto.blockModeIdealExperiment`: generic real and
  ideal random-IV block-mode left-or-right experiments.
* `Cslib.Crypto.blockModeQueryProgram`, `Cslib.Crypto.blockModeReduction`: generic PRF distinguisher
  from a left-or-right block-mode adversary and keystream oracle program.

## Main results

* `Cslib.Crypto.idealExperiment_eq_runWith_lazyStep`: `PRF.idealExperiment` equals running
  `lazyStep` from `([], false)`.
* `Cslib.Crypto.advantage_lazy_fresh_le`: the advantage between `lazyStep` and `freshStep` is at
  most the bad-flag probability under `freshStep`.
* `Cslib.Crypto.advantage_idealExperiment_freshStep_le`: the advantage between
  `PRF.idealExperiment` and `freshStep` is at most the bad-flag probability under `freshStep`.
* `Cslib.Crypto.length_blockModeSelect`, `Cslib.Crypto.blockModeBlocks_le`,
  `Cslib.Crypto.blockModeCpaExperiment_eq_realExperiment`,
  `Cslib.Crypto.isQueryBounded_blockModeReduction`,
  `Cslib.Crypto.freshGame_eq_blockModeIdealExperiment`: shared left-or-right block-mode CPA
  lemmas.
* `Cslib.Crypto.eval_blockModeIdealOracle`: the ideal oracle is a uniform initialization vector
  and `blockModeBlocks ℓ q` uniform blocks.
* `Cslib.Crypto.blockModeCpaExperiment_eq_realExperiment_simulate`: a per-query program that
  computes the encryption oracle gives the real PRF experiment.
* `Cslib.Crypto.freshGame_simulate_eq_blockModeIdealExperiment`: a per-query program whose
  fresh-sampling answers have the ideal law gives exactly `blockModeIdealExperiment` under fresh
  sampling.
* `Cslib.Crypto.advantage_idealExperiment_simulate_le`: if in addition a query of `k` blocks adds
  at most `k` table entries and, from a table of `t` entries, raises the flag with probability at
  most `(k t + k.choose 2) / 2 ^ n`, the program run against a uniform random function is within
  `K.choose 2 / 2 ^ n` of `blockModeIdealExperiment` when the queries ask at most `K` blocks in
  total.
* `Cslib.Crypto.advantage_le_two`, `Cslib.Crypto.advantage_le_four`: two-step and four-step
  triangle-inequality bounds for `Game.advantage`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*, 3rd ed.][KatzLindell2020],
  Section 3.6.3 (Definition 3.22, Theorem 3.33).
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Chapter 4.
-/

public section

namespace Cslib.Crypto

open Cslib.Probability
open OracleComp (sumHandler)
open scoped ENNReal NNReal

variable {n : ℕ}

/-- A lazily sampled random-function table and a flag recording a repeated input. -/
abbrev FlagState (n : ℕ) : Type := List (BitString n × BitString n) × Bool

/-- Whether a `FlagState` has recorded a repeated oracle input. -/
abbrev FlagState.repeated (s : FlagState n) : Bool := s.2

/-- Lazy sampling of a uniform function: a cached input returns its cached value and raises the
flag, and a new input draws a uniform value. -/
@[expose]
noncomputable def lazyStep (x : BitString n) : StateT (FlagState n) PMF (BitString n) :=
  fun s => match s.1.lookup x with
    | some y => PMF.pure (y, (s.1, true))
    | none => (PMF.uniformOfFintype (BitString n)).map fun u => (u, ((x, u) :: s.1, s.2))

/-- Fresh sampling of a uniform function: every input draws a new uniform value, and a repeated
input raises the flag. -/
@[expose]
noncomputable def freshStep (x : BitString n) : StateT (FlagState n) PMF (BitString n) :=
  fun s => (PMF.uniformOfFintype (BitString n)).map fun u =>
    (u, ((x, u) :: s.1, s.2 || (s.1.lookup x).isSome))

private theorem lazyStep_map_fst (x : BitString n) (c : List (BitString n × BitString n))
    (b : Bool) :
    (lazyStep x (c, b)).map (Prod.map id Prod.fst) =
      memoize (fun _ => PMF.uniformOfFintype (BitString n)) x c := by
  unfold lazyStep
  cases h : c.lookup x with
  | some y =>
    rw [memoize_of_some _ _ _ _ h]
    simp only [PMF.pure_map, Probability.PMF.monad_pure_eq_pure, Prod.map_apply, id_eq]
  | none =>
    rw [memoize_of_none _ _ _ h]
    simp only [PMF.map, Function.comp_def, PMF.bind_bind, PMF.pure_bind,
      Probability.PMF.monad_bind_eq_bind, Probability.PMF.monad_pure_eq_pure,
      Prod.map_apply, id_eq]

private theorem runWith_memoize_eq {α : Type}
    (program : ProbOracleComp (fun _ : BitString n => BitString n) α) :
    (ProbOracleComp.runWith (memoize fun _ => PMF.uniformOfFintype (BitString n)) program
      []).map Prod.fst =
      (ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst := by
  rw [← ProbOracleComp.runWith_map_fst lazyStep
    (memoize fun _ => PMF.uniformOfFintype (BitString n)) lazyStep_map_fst program [] false,
    PMF.map_comp]
  exact congrArg (fun f => PMF.map f _) (funext fun ⟨_, _⟩ => rfl)

private theorem identicalUntilBad_lazyStep_freshStep :
    ProbOracleComp.IdenticalUntilBad (lazyStep (n := n)) (freshStep (n := n))
      OracleComp.FlagBad := by
  refine ProbOracleComp.IdenticalUntilBad.of_flag ?_ ?_ ?_
  · intro x c z hz
    simp only [lazyStep] at hz
    split at hz
    · obtain rfl := (PMF.mem_support_pure_iff _ _).1 hz
      rfl
    · obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      rfl
  · intro x c z hz
    obtain ⟨_, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    rfl
  · intro x c a c'
    simp only [lazyStep, freshStep, Bool.false_or]
    cases h : c.lookup x with
    | none => simp only [Option.isSome_none]
    | some y =>
      simp only [Option.isSome_some]
      have h1 : (PMF.pure (y, (c, true)) : PMF (BitString n × FlagState n)) (a, (c', false)) = 0 :=
        (PMF.apply_eq_zero_iff _ _).2 fun hz => by cases (PMF.mem_support_pure_iff _ _).1 hz
      have h2 : ((PMF.uniformOfFintype (BitString n)).map fun u =>
          (u, ((x, u) :: c, true))) (a, (c', false)) = 0 :=
        (PMF.apply_eq_zero_iff _ _).2 fun hz => by
          obtain ⟨_, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
          cases heq
      rw [h1, h2]

/-- `PRF.idealExperiment` against a uniform random function on `BitString n` equals the output of
`ProbOracleComp.runWith lazyStep program ([], false)`. -/
theorem idealExperiment_eq_runWith_lazyStep (program : PRF.Adversary (BitString n) (BitString n)) :
    ProbComp.eval (PRF.idealExperiment program) =
      (ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst := by
  rw [← runWith_memoize_eq, PRF.eval_idealExperiment_eq_runWith_memoize]

/-- The advantage between `lazyStep` and `freshStep` is bounded by the probability of raising the
repetition flag under `freshStep`. -/
theorem advantage_lazy_fresh_le (program : PRF.Adversary (BitString n) (BitString n)) :
    (Game.advantage ((ProbOracleComp.runWith lazyStep program ([], false)).map Prod.fst)
        ((ProbOracleComp.runWith freshStep program ([], false)).map Prod.fst) : ℝ) ≤
      ((ProbOracleComp.runWith freshStep program ([], false)).toOuterMeasure
        {x | x.2.repeated = true}).toReal := by
  have h := identicalUntilBad_lazyStep_freshStep.advantage_le program ([], false)
    fun x => PMF.pure x.1
  rw [identicalUntilBad_lazyStep_freshStep.bad_eq] at h
  simpa only [← PMF.bind_pure_comp, Function.comp_def] using h

/-- The advantage between `PRF.idealExperiment` and fresh independent sampling `freshStep` is
bounded by the probability of raising the repetition flag under `freshStep`. -/
theorem advantage_idealExperiment_freshStep_le
    (program : PRF.Adversary (BitString n) (BitString n)) :
    (Game.advantage (ProbComp.eval (PRF.idealExperiment program))
        ((ProbOracleComp.runWith freshStep program ([], false)).map Prod.fst) : ℝ) ≤
      ((ProbOracleComp.runWith freshStep program ([], false)).toOuterMeasure
        {x | x.2.repeated = true}).toReal := by
  rw [idealExperiment_eq_runWith_lazyStep]
  exact advantage_lazy_fresh_le program

/-- Two-hop triangle inequality for real-valued `Game.advantage`. -/
theorem advantage_le_two (g₀ g₁ g₂ : Game) :
    (Game.advantage g₀ g₂ : ℝ) ≤ Game.advantage g₀ g₁ + Game.advantage g₂ g₁ := by
  rw [Game.advantage_comm g₂ g₁]
  exact_mod_cast Game.advantage_triangle g₀ g₁ g₂

/-- Four-hop symmetric triangle inequality for real-valued `Game.advantage`. -/
theorem advantage_le_four (g₀ g₁ g₂ g₃ g₄ : Game) :
    (Game.advantage g₀ g₄ : ℝ) ≤
      Game.advantage g₀ g₁ + Game.advantage g₁ g₂ + Game.advantage g₃ g₂ +
        Game.advantage g₄ g₃ := by
  have h₁ : (Game.advantage g₀ g₄ : ℝ) ≤ Game.advantage g₀ g₁ + Game.advantage g₁ g₄ := by
    exact_mod_cast Game.advantage_triangle g₀ g₁ g₄
  have h₂ : (Game.advantage g₁ g₄ : ℝ) ≤ Game.advantage g₁ g₂ + Game.advantage g₂ g₄ := by
    exact_mod_cast Game.advantage_triangle g₁ g₂ g₄
  have h₃ : (Game.advantage g₂ g₄ : ℝ) ≤ Game.advantage g₃ g₂ + Game.advantage g₄ g₃ :=
    (advantage_le_two g₂ g₃ g₄).trans_eq (by rw [Game.advantage_comm g₂ g₃, add_comm])
  linarith

/-! ### Shared Left-or-Right Block-Mode CPA Experiment -/

/-- A left-or-right query: two candidate plaintexts, each a list of `n`-bit blocks. -/
abbrev BlockModeQuery (n : ℕ) : Type := List (BitString n) × List (BitString n)

/-- The answer to a left-or-right block-mode query: an initialization vector and ciphertext blocks.
-/
abbrev BlockModeSpec (n : ℕ) : BlockModeQuery n → Type := fun _ => BitString n × List (BitString n)

/-- An adaptive adversary in a left-or-right block-mode experiment, with private coins. -/
abbrev BlockModeAdversary (n : ℕ) : Type := ProbOracleComp (BlockModeSpec n) Bool

/-- The plaintext encrypted for query `q` under challenge bit `b`: the right message if `b = true`
and the left one otherwise. Queries whose messages differ in length or exceed `ℓ` blocks encrypt
the empty message. -/
@[expose]
def blockModeSelect (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n) : List (BitString n) :=
  if q.1.length = q.2.length ∧ q.1.length ≤ ℓ then (if b then q.2 else q.1) else []

/-- The number of blocks encrypted for query `q`: the common length of a valid query, or `0`. -/
@[expose]
def blockModeBlocks (ℓ : ℕ) (q : BlockModeQuery n) : ℕ :=
  if q.1.length = q.2.length ∧ q.1.length ≤ ℓ then q.1.length else 0

/-- The encrypted plaintext has `blockModeBlocks ℓ q` blocks, regardless of the challenge bit. -/
@[simp]
theorem length_blockModeSelect (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n) :
    (blockModeSelect ℓ b q).length = blockModeBlocks ℓ q := by
  unfold blockModeSelect blockModeBlocks
  split_ifs <;> simp_all

/-- Every query encrypts at most `ℓ` blocks. -/
theorem blockModeBlocks_le (ℓ : ℕ) (q : BlockModeQuery n) : blockModeBlocks ℓ q ≤ ℓ := by
  unfold blockModeBlocks
  split_ifs with h
  · exact h.2
  · exact Nat.zero_le ℓ

/-- The cost of a call in a left-or-right block-mode experiment: private draws are free and each
encryption query costs its block length. -/
@[expose]
def blockModeCost (ℓ : ℕ) : ℕ ⊕ BlockModeQuery n → ℕ :=
  Sum.elim (fun _ => 0) (blockModeBlocks ℓ)

/-- Generic random-IV left-or-right encryption oracle for block encryption operator `enc` and
challenge bit `b`. -/
@[expose]
noncomputable def blockModeOracle (enc : BitString n → List (BitString n) → List (BitString n))
    (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n) :
    ProbComp (BitString n × List (BitString n)) := do
  let iv ← ProbComp.uniform (BitString n)
  return (iv, enc iv (blockModeSelect ℓ b q))

/-- The ideal left-or-right oracle: a uniform initialization vector and `blockModeBlocks ℓ q`
independent uniform ciphertext blocks, independent of the challenge bit. -/
@[expose]
noncomputable def blockModeIdealOracle (ℓ : ℕ) (q : BlockModeQuery n) :
    ProbComp (BitString n × List (BitString n)) := do
  let iv ← ProbComp.uniform (BitString n)
  let c ← ProbComp.uniform (Fin (blockModeBlocks ℓ q) → BitString n)
  return (iv, List.ofFn c)

/-- Generic random-IV left-or-right experiment for keyed block encryption `enc` and challenge bit
`b`: sample one uniform key and answer every query with `blockModeOracle (enc key) ℓ b`
([KatzLindell2020], Definition 3.22). -/
@[expose]
noncomputable def blockModeCpaExperiment {Key : Type} [Fintype Key] [Nonempty Key]
    (enc : Key → BitString n → List (BitString n) → List (BitString n)) (ℓ : ℕ) (b : Bool)
    (adversary : BlockModeAdversary n) : ProbComp Bool := do
  let key ← ProbComp.uniform Key
  adversary.run (blockModeOracle (enc key) ℓ b)

/-- The ideal left-or-right experiment: the adversary receives fresh uniform ciphertext blocks. -/
@[expose]
noncomputable def blockModeIdealExperiment (ℓ : ℕ) (adversary : BlockModeAdversary n) :
    ProbComp Bool :=
  adversary.run (blockModeIdealOracle ℓ)

/-- One block-mode encryption computed from a keystream oracle program `keystream iv k`. -/
@[expose]
noncomputable def blockModeQueryProgram
    (keystream : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n)))
    (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n) :
    ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)) := do
  let iv ← ProbOracleComp.sample (ProbComp.uniform (BitString n))
  let ks ← keystream iv (blockModeSelect ℓ b q).length
  return (iv, List.zipWith (· + ·) ks (blockModeSelect ℓ b q))

/-- Generic PRF distinguisher built from a left-or-right block-mode adversary and keystream
program: the adversary with each encryption query replaced by `blockModeQueryProgram`. -/
@[expose]
noncomputable def blockModeReduction
    (keystream : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n)))
    (ℓ : ℕ) (b : Bool) (adversary : BlockModeAdversary n) :
    PRF.Adversary (BitString n) (BitString n) :=
  ProbOracleComp.simulate (blockModeQueryProgram keystream ℓ b) adversary

/-- **The real experiment of a block-mode query program.** If `program q`, run with `F key` as its
oracle, is the encryption oracle `blockModeOracle (enc key) ℓ b q`, then
`blockModeCpaExperiment enc` is `PRF.realExperiment F` for the adversary run with `program`. -/
theorem blockModeCpaExperiment_eq_realExperiment_simulate {Key : Type} [Fintype Key] [Nonempty Key]
    (enc : Key → BitString n → List (BitString n) → List (BitString n))
    (program : BlockModeQuery n →
      ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)))
    (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool) (adversary : BlockModeAdversary n)
    (hprogram : ∀ key q,
      (program q).run (fun y => pure (F key y)) = blockModeOracle (enc key) ℓ b q) :
    blockModeCpaExperiment enc ℓ b adversary =
      PRF.realExperiment F (ProbOracleComp.simulate program adversary) := by
  unfold blockModeCpaExperiment PRF.realExperiment
  refine bind_congr fun key => ?_
  rw [ProbOracleComp.run_simulate]
  congr 1
  funext q
  exact (hprogram key q).symm

/-- When `keystream iv ms.length` evaluates with `F key` to the mask XORed by `enc key iv ms`,
`blockModeCpaExperiment enc` is `PRF.realExperiment F (blockModeReduction keystream ℓ b adversary)`.
-/
theorem blockModeCpaExperiment_eq_realExperiment {Key : Type} [Fintype Key] [Nonempty Key]
    (enc : Key → BitString n → List (BitString n) → List (BitString n))
    (keystream : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n)))
    (F : Key → BitString n → BitString n) (ℓ : ℕ) (b : Bool)
    (adversary : BlockModeAdversary n)
    (hks : ∀ key iv ms,
      ∃ raw : List (BitString n),
        (keystream iv ms.length).run (fun y => pure (F key y)) = pure raw ∧
        List.zipWith (· + ·) raw ms = enc key iv ms) :
    blockModeCpaExperiment enc ℓ b adversary =
      PRF.realExperiment F (blockModeReduction keystream ℓ b adversary) :=
  blockModeCpaExperiment_eq_realExperiment_simulate enc _ F ℓ b adversary fun key q => by
    simp only [blockModeOracle, blockModeQueryProgram, ProbOracleComp.run_bind,
      ProbOracleComp.run_sample, ProbOracleComp.run_pure]
    refine bind_congr fun iv => ?_
    obtain ⟨raw, hraw, henc⟩ := hks key iv (blockModeSelect ℓ b q)
    rw [hraw, pure_bind, henc]

/-- If `keystream iv k` makes at most `k` oracle calls for every `k ≤ ℓ`, and `adversary` asks
at most `K` blocks in total, then `blockModeReduction keystream ℓ b adversary` makes at most `K`
oracle calls. -/
theorem isQueryBounded_blockModeReduction
    (keystream : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n)))
    (ℓ : ℕ) (b : Bool) {adversary : BlockModeAdversary n} {K : ℕ}
    (hks : ∀ iv k, k ≤ ℓ → ProbOracleComp.IsQueryBounded (keystream iv k) k)
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    ProbOracleComp.IsQueryBounded (blockModeReduction keystream ℓ b adversary) K := by
  refine ProbOracleComp.isCostBounded_simulate (cost := blockModeBlocks ℓ) (fun q => ?_) h
  have hq := OracleComp.IsCostBounded.bind
    (ProbOracleComp.isCostBounded_sample (spec := fun _ : BitString n => BitString n)
      (fun _ => 1) (ProbComp.uniform (BitString n))) fun iv =>
    OracleComp.IsCostBounded.bind
      (hks iv (blockModeSelect ℓ b q).length
        (by rw [length_blockModeSelect]; exact blockModeBlocks_le ℓ q))
      fun ks =>
        OracleComp.IsCostBounded.pure (iv, List.zipWith (· + ·) ks (blockModeSelect ℓ b q)) 0
  exact OracleComp.IsCostBounded.mono hq (by simp)

/-- The law of the ideal oracle: a uniform initialization vector and `blockModeBlocks ℓ q`
independent uniform blocks. -/
theorem eval_blockModeIdealOracle (ℓ : ℕ) (q : BlockModeQuery n) :
    ProbComp.eval (blockModeIdealOracle ℓ q) =
      (PMF.uniformOfFintype (BitString n)).bind fun iv =>
        (uniformBlocks (n := n) (blockModeBlocks ℓ q)).map (iv, ·) := by
  simp only [blockModeIdealOracle, ProbComp.eval_bind, ProbComp.eval_uniform, ProbComp.eval_pure,
    uniformBlocks_eq, Function.comp_def, ← PMF.bind_pure_comp, PMF.bind_bind, PMF.pure_bind]

private theorem map_unit_runWith_freshStep_blockModeQueryProgram
    (keystream : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n)))
    (ℓ : ℕ) (b : Bool) (q : BlockModeQuery n) (s : FlagState n)
    (hks : ∀ iv s,
      (ProbOracleComp.runWith freshStep (keystream iv (blockModeBlocks ℓ q)) s).map Prod.fst =
        uniformBlocks (blockModeBlocks ℓ q)) :
    (ProbOracleComp.runWith freshStep
        (blockModeQueryProgram keystream ℓ b q) s).map (fun x => (x.1, ())) =
      (ProbComp.eval (blockModeIdealOracle ℓ q)).map (·, ()) := by
  have hpad := map_iv_uniformBlocks_zipWith (blockModeSelect ℓ b q)
  rw [length_blockModeSelect] at hpad
  rw [eval_blockModeIdealOracle, ← hpad]
  simp only [blockModeQueryProgram, ProbOracleComp.runWith_bind, ProbOracleComp.runWith_sample,
    ProbComp.eval_uniform, length_blockModeSelect, ProbOracleComp.runWith_pure,
    PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]
  refine PMF.bind_congr_on_support _ _ _ fun iv _ => ?_
  have hk := hks iv s
  rw [← hk]
  simp only [PMF.map_comp, Function.comp_def]
  rfl

/-- **Fresh sampling of a block-mode query program.** If every answer of `program`, under fresh
sampling and with the table forgotten, has the law of the ideal oracle, then the adversary run
with `program` under fresh sampling is `blockModeIdealExperiment`. -/
theorem freshGame_simulate_eq_blockModeIdealExperiment
    (program : BlockModeQuery n →
      ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)))
    (ℓ : ℕ) (adversary : BlockModeAdversary n)
    (hprogram : ∀ q s,
      (ProbOracleComp.runWith freshStep (program q) s).map (fun x => (x.1, ())) =
        (ProbComp.eval (blockModeIdealOracle ℓ q)).map (·, ())) :
    (ProbOracleComp.runWith freshStep
        (ProbOracleComp.simulate program adversary) ([], false)).map Prod.fst =
      ProbComp.eval (blockModeIdealExperiment ℓ adversary) := by
  have hstate :
      (ProbOracleComp.runWith (fun q => ProbOracleComp.runWith freshStep (program q))
          adversary ([], false)).map (fun x => (x.1, ())) =
        ProbOracleComp.runWith
          (fun q (u : Unit) => (ProbComp.eval (blockModeIdealOracle ℓ q)).map (·, u))
          adversary () :=
    ProbOracleComp.runWith_map_state
      (fun q => ProbOracleComp.runWith freshStep (program q))
      (fun q (u : Unit) => (ProbComp.eval (blockModeIdealOracle ℓ q)).map (·, u))
      (fun _ => ()) (fun q s => hprogram q s) adversary ([], false)
  have hro :
      ProbOracleComp.runWith
          (fun q (u : Unit) => (ProbComp.eval (blockModeIdealOracle ℓ q)).map (·, u)) adversary () =
        (OracleComp.interpret
          (sumHandler ProbComp.unifOracle fun q => ProbComp.eval (blockModeIdealOracle ℓ q))
          adversary).map (·, ()) :=
    by simpa only [OracleComp.evalWith_eq_interpret] using
      ProbOracleComp.runWith_readOnly (fun q _ => ProbComp.eval (blockModeIdealOracle ℓ q))
        adversary ()
  rw [ProbOracleComp.runWith_simulate]
  calc
    (ProbOracleComp.runWith (fun q => ProbOracleComp.runWith freshStep (program q))
          adversary ([], false)).map Prod.fst
        = ((ProbOracleComp.runWith (fun q => ProbOracleComp.runWith freshStep (program q))
              adversary ([], false)).map fun x => (x.1, ())).map Prod.fst :=
          (PMF.map_comp (fun x : Bool × FlagState n => (x.1, ())) _ Prod.fst).symm
    _ = ((OracleComp.interpret
            (sumHandler ProbComp.unifOracle fun q => ProbComp.eval (blockModeIdealOracle ℓ q))
            adversary).map (·, ())).map Prod.fst := by rw [hstate, hro]
    _ = ProbComp.eval (blockModeIdealExperiment ℓ adversary) := by
          rw [(PMF.map_comp (·, ()) _ Prod.fst).trans (PMF.map_id _),
            blockModeIdealExperiment, ProbOracleComp.eval_run]

/-- Under fresh sampling, whenever the keystream program outputs uniform blocks on every query,
`blockModeReduction` has the exact same output distribution as `blockModeIdealExperiment`. -/
theorem freshGame_eq_blockModeIdealExperiment
    (keystream : BitString n → ℕ →
      ProbOracleComp (fun _ : BitString n => BitString n) (List (BitString n)))
    (ℓ : ℕ) (b : Bool) (adversary : BlockModeAdversary n)
    (hks : ∀ (q : BlockModeQuery n) iv s,
      (ProbOracleComp.runWith freshStep (keystream iv (blockModeBlocks ℓ q)) s).map Prod.fst =
        uniformBlocks (blockModeBlocks ℓ q)) :
    (ProbOracleComp.runWith freshStep
        (blockModeReduction keystream ℓ b adversary) ([], false)).map Prod.fst =
      ProbComp.eval (blockModeIdealExperiment ℓ adversary) :=
  freshGame_simulate_eq_blockModeIdealExperiment _ ℓ adversary fun q s =>
    map_unit_runWith_freshStep_blockModeQueryProgram keystream ℓ b q s (hks q)

/-- The flag bound behind `advantage_idealExperiment_simulate_le`: summing the per-query bound
`(k t + k.choose 2) / 2 ^ n` over queries of `K` blocks in total gives `K.choose 2 / 2 ^ n`. -/
private theorem toOuterMeasure_repeated_freshStep_simulate_le
    (program : BlockModeQuery n →
      ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)))
    (ℓ : ℕ)
    (hbad : ∀ q (s : FlagState n), ¬s.repeated = true →
      (ProbOracleComp.runWith freshStep (program q) s).toOuterMeasure {x | x.2.repeated = true} ≤
        ((blockModeBlocks ℓ q * s.1.length + (blockModeBlocks ℓ q).choose 2 : ℕ) : ℝ≥0∞) *
          ((2 : ℝ≥0∞) ^ n)⁻¹)
    (hlen : ∀ q (s : FlagState n) a (t : List (BitString n × BitString n)) (f : Bool),
      (a, t, f) ∈ (ProbOracleComp.runWith freshStep (program q) s).support →
        t.length ≤ s.1.length + blockModeBlocks ℓ q)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (ProbOracleComp.runWith freshStep (ProbOracleComp.simulate program adversary)
        ([], false)).toOuterMeasure {x | x.2.repeated = true} ≤
      ((K.choose 2 : ℕ) : ℝ≥0∞) * ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  rw [ProbOracleComp.runWith_simulate]
  simpa using
    ProbOracleComp.toOuterMeasure_bad_choose_two_cost_le
      (handler := fun q => ProbOracleComp.runWith freshStep (program q))
      (bad := fun s : FlagState n => s.repeated = true) (blockModeBlocks ℓ) (fun _ => 0)
      (fun s => s.1.length) ((2 : ℝ≥0∞) ^ n)⁻¹ hbad
      (fun q s _ x hx _ => by obtain ⟨y, t, f⟩ := x; exact hlen q s y t f hx) h
      (OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun q => by cases q <;> rfl) adversary)
      (s := ([], false)) (by simp)

/-- **A block-mode query program against a uniform random function.** Suppose that under fresh
sampling every answer of `program` has the law of the ideal oracle, adds at most
`k = blockModeBlocks ℓ q` entries to the table, and from a table of `t` entries raises the flag
with probability at most `(k t + k.choose 2) / 2 ^ n`. Then against a uniform random function the
adversary run with `program`, if its queries ask at most `K` blocks in total, is within
`K.choose 2 / 2 ^ n` of `blockModeIdealExperiment`. -/
theorem advantage_idealExperiment_simulate_le
    (program : BlockModeQuery n →
      ProbOracleComp (fun _ : BitString n => BitString n) (BitString n × List (BitString n)))
    (ℓ : ℕ)
    (hprogram : ∀ q s,
      (ProbOracleComp.runWith freshStep (program q) s).map (fun x => (x.1, ())) =
        (ProbComp.eval (blockModeIdealOracle ℓ q)).map (·, ()))
    (hbad : ∀ q (s : FlagState n), ¬s.repeated = true →
      (ProbOracleComp.runWith freshStep (program q) s).toOuterMeasure {x | x.2.repeated = true} ≤
        ((blockModeBlocks ℓ q * s.1.length + (blockModeBlocks ℓ q).choose 2 : ℕ) : ℝ≥0∞) *
          ((2 : ℝ≥0∞) ^ n)⁻¹)
    (hlen : ∀ q (s : FlagState n) a (t : List (BitString n × BitString n)) (f : Bool),
      (a, t, f) ∈ (ProbOracleComp.runWith freshStep (program q) s).support →
        t.length ≤ s.1.length + blockModeBlocks ℓ q)
    {adversary : BlockModeAdversary n} {K : ℕ}
    (h : OracleComp.IsCostBounded (blockModeCost ℓ) adversary K) :
    (Game.advantage
        (ProbComp.eval (PRF.idealExperiment (ProbOracleComp.simulate program adversary)))
        (ProbComp.eval (blockModeIdealExperiment ℓ adversary)) : ℝ) ≤
      (K.choose 2 : ℝ) / 2 ^ n := by
  rw [← freshGame_simulate_eq_blockModeIdealExperiment program ℓ adversary hprogram]
  refine (advantage_idealExperiment_freshStep_le _).trans ?_
  rw [div_eq_mul_inv]
  ennreal_to_real using toOuterMeasure_repeated_freshStep_simulate_le program ℓ hbad hlen h

end Cslib.Crypto
