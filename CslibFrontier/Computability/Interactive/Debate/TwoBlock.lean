/-
Copyright (c) 2026 Richard Dodson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Dodson
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Interactive.Debate.Machine
public import CslibFrontier.Probability.PMF.Coin
import CslibFrontier.Foundations.Analysis.ENNRealNatDiv
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Figure 1 is not sound for a machine with oracle queries of length at most two

The soundness step of `Debate.lean` holds under
[BrownCohenIrvingPiliouras2024, Definition 6.1] for machines whose every step queries an
encoding of the whole transcript so far (`soundness_of_lipschitzAt_run_prefixMachine`). That
reading of the source, and what it costs, are recorded in #7579. This module shows that the
assumption on the queries is needed: for a machine whose every step is an oracle query, but
whose queries have at most two bits, the protocol of
[BrownCohenIrvingPiliouras2024, Figure 1] is not sound under Definition 6.1. `CopyChain.lean`
shows separately that it is needed that every step is a query.

Every step is an oracle query. The two blocks reuse the same one-bit address `false`. The
proposer gives it a positive probability in the first block and zero in the second, whereas a
fixed replacement oracle gives it one probability in both. Definition 6.1 controls the change
under a fixed oracle only.

## The machine

The *two-block machine* runs two blocks. A block is one query at the empty address followed by
`m` queries, each at the previous bit. The last step queries the pair `(u, v)` of the last bits
of the two blocks. The oracle answers `false` at the empty address, answers a one-bit address
with that bit, and answers the pair with `true` with probability `c + c (u - v)`.

The machine has seven addresses, the strings of at most two bits (`TwoBlockQuery`). The source's
oracle has addresses of one fixed length `l` (`dedebate.tex`, lines 127 and 239). An injective
recoding into three-bit addresses preserves the argument, with one address unused, so the
example is one with constant-length queries.

* Under any one oracle the two blocks are independent and have the same law, so the expected
  answer of the original pair lookup is `c`, and the lookup itself moves by at most the
  perturbation. The machine is `1`-Lipschitz at its oracle, for every `m`, and accepts with
  probability `c`.
* The proposer claims a small positive probability `k / N` at the address `false` in the first
  block. At every other start and copy step it reports the exact probability, and at the final
  lookup it reports grid approximations `κ₁ / N` and `κ₀ / N` of the two probabilities that can
  occur. Every claim before the last round is within the verifier's tolerance of a
  deterministic answer, so an abort there is accepted. The first block ends at `true` with
  probability `1 - (1 - k / N) ^ m` and the second at `false`. With `a = κ₀ / N` and
  `κ₁ = 2 κ₀`: conditional on the first block ending at `true` the final bit is `true` with
  probability `2 a`, and unconditionally with probability `a (2 - (1 - k / N) ^ m)`, against
  `c` for the machine.

## Reading of the source

* The printed Definition 6.1 has a strict inequality. For it the relevant statement is
  `not_sound_figure1_two_of_lipschitzAt_run_twoBlockMachine`, with the constants of Figure 1
  for `K = 2`: the output law of this machine moves by at most the distance between the
  oracles, which is strictly less than twice that distance when the distance is positive. The
  constant `1` is attained (raise the answer at every pair by the same amount), so the machine
  does not satisfy the strict inequality with `K = 1`.
  `not_sound_figure1_of_lipschitzAt_run_twoBlockMachine`, with the constants for `K = 1`, is
  under the non-strict reading of Definition 6.1, which is `ProbOracleComp.LipschitzAt`.
* The protocol is the interpreter `Debate.run`: claims and coins lie on a grid, and the bit of each
  round is computed by the interpreter from the claim and the two coins, as in the authors'
  formalization, which the source says uses external randomness in place of the two shares
  (`dedebate.tex`, line 294). The order of events is that of Figure 1, where the challenger may
  abort (step 2(e), line 259) after the bit of the round is set (step 2(d), line 258).
* The checked conclusions are about `Debate.run`. In Figure 1 the proposer can announce the
  same grid probabilities, supply a uniform share of the coin, and set the bit as prescribed;
  the probabilities and the argument for an abort are then the same.
* The constants are `Params.figure1`.

## Main definitions

* `Cslib.Interactive.Debate.twoBlockMachine`, `Cslib.Interactive.Debate.twoBlockOracle`: the
  machine and its oracle.
* `Cslib.Interactive.Debate.twoBlockProposer`: the proposer that wins against it.

## Main results

* `Cslib.Interactive.Debate.evalWith_run_twoBlockMachine`,
  `Cslib.Interactive.Debate.lipschitzAt_run_twoBlockMachine`: the machine accepts with
  probability `c` and satisfies Definition 6.1 with constant `1`, non-strictly.
* `Cslib.Interactive.Debate.le_evalWith_run_twoBlockProposer`: the acceptance bound against
  every challenger, for general parameters, with the verifier's rejection probability in the last
  round as a hypothesis.
* `Cslib.Interactive.Debate.not_sound_figure1_two_of_lipschitzAt_run_twoBlockMachine`: with the
  constants of Figure 1 for `K = 2`, the protocol is not sound for this machine. This covers the
  printed, strict Definition 6.1.
* `Cslib.Interactive.Debate.not_sound_figure1_of_lipschitzAt_run_twoBlockMachine`: the same with
  the constants for `K = 1`, under the non-strict reading.

## References

* [J. Brown-Cohen, G. Irving, G. Piliouras, *Scalable AI safety via doubly-efficient debate*,
  Section 6 and Appendix D][BrownCohenIrvingPiliouras2024]
-/

public section

namespace Cslib.Interactive.Debate

open OracleComp (sumHandler)
open ProbOracleComp (LipschitzAt)
open scoped ENNReal NNReal

/-! ### The machine and its oracle -/

/-- The addresses of the two-block machine: the empty address, a one-bit address and a two-bit
address. These are the seven strings of at most two bits. -/
abbrev TwoBlockQuery : Type := Unit ⊕ Bool ⊕ (Bool × Bool)

/-- The two-block machine. A block is one query at the empty address followed by `m` queries,
each at the previous bit. The machine runs two blocks and then queries the pair of the last
bits of the two blocks. Every one of its `2 m + 3` steps is an oracle query, and every query
has at most two bits. -/
@[expose] def twoBlockMachine (m : ℕ) : Machine TwoBlockQuery where
  step bits :=
    if bits.length = 0 ∨ bits.length = m + 1 then .ask (.inl ())
    else if bits.length < 2 * m + 2 then .ask (.inr (.inl (bits.headD false)))
    else .ask (.inr (.inr (bits.getD (m + 1) false, bits.headD false)))

/-- The oracle of the two-block machine: `start` at the empty address; the address itself at a
one-bit address; and at a pair `(u, v)` the answer `true` with probability `c + c (u - v)`, that
is `2 c` at `(1, 0)`, `0` at `(0, 1)` and `c` otherwise. -/
@[expose] noncomputable def twoBlockOracle (start : PMF Bool) (c : ℝ) (hc0 : 0 ≤ c)
    (hc1 : 2 * c ≤ 1) : TwoBlockQuery → PMF Bool
  | .inl _ => start
  | .inr (.inl u) => PMF.pure u
  | .inr (.inr (true, false)) => Probability.PMF.coin ⟨2 * c, by positivity, hc1⟩
  | .inr (.inr (false, true)) => PMF.pure false
  | .inr (.inr _) => Probability.PMF.coin ⟨c, hc0, by linarith⟩

variable {m : ℕ}

/-- The step law at the first step of a block. -/
theorem stepLaw_twoBlockMachine_start (O : TwoBlockQuery → PMF Bool) {bits : List Bool}
    (h : bits.length = 0 ∨ bits.length = m + 1) :
    (twoBlockMachine m).stepLaw O bits = O (.inl ()) := by
  simp only [Machine.stepLaw, twoBlockMachine, h, ↓reduceIte]

/-- The step law at a later step of a block. -/
theorem stepLaw_twoBlockMachine_copy (O : TwoBlockQuery → PMF Bool) {bits : List Bool}
    (h0 : bits.length ≠ 0) (h1 : bits.length ≠ m + 1) (h2 : bits.length < 2 * m + 2) :
    (twoBlockMachine m).stepLaw O bits = O (.inr (.inl (bits.headD false))) := by
  simp only [Machine.stepLaw, twoBlockMachine, h0, h1, h2, or_self, ↓reduceIte]

/-- The step law at the last step. -/
theorem stepLaw_twoBlockMachine_pair (O : TwoBlockQuery → PMF Bool) {bits : List Bool}
    (h : bits.length = 2 * m + 2) :
    (twoBlockMachine m).stepLaw O bits =
      O (.inr (.inr (bits.getD (m + 1) false, bits.headD false))) := by
  have h0 : bits.length ≠ 0 := by omega
  have h1 : bits.length ≠ m + 1 := by omega
  have h2 : ¬ bits.length < 2 * m + 2 := by omega
  simp only [Machine.stepLaw, twoBlockMachine, h0, h1, h2, or_self, ↓reduceIte]

/-! ### The law of the run -/

/-- Transcripts of `n` steps have length `n`. -/
private theorem length_of_mem_support_transcript (M : Machine TwoBlockQuery)
    (O : TwoBlockQuery → PMF Bool) :
    ∀ n, ∀ bits ∈ (OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      (M.transcript n)).support, bits.length = n
  | 0 => by
    intro bits hbits
    have : bits = [] := by simpa [Machine.transcript] using hbits
    rw [this]; rfl
  | n + 1 => by
    intro bits hbits
    simp only [Machine.transcript, OracleComp.evalWith_bind, OracleComp.evalWith_pure,
      PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hbits
    obtain ⟨prev, hprev, bit, -, rfl⟩ := hbits
    rw [List.length_cons, length_of_mem_support_transcript M O n prev hprev]

/-- A statistic of the transcript after one more step, from a statistic of the transcript
before it. -/
private theorem map_transcript_succ (M : Machine TwoBlockQuery) (O : TwoBlockQuery → PMF Bool)
    (n : ℕ) {β γ : Type} (f : List Bool → β) (g : List Bool → γ) (κ : γ → PMF β)
    (h : ∀ bits : List Bool, bits.length = n →
      (M.stepLaw O bits).map (fun bit => f (bit :: bits)) = κ (g bits)) :
    (OracleComp.evalWith (sumHandler ProbComp.unifOracle O) (M.transcript (n + 1))).map f =
      ((OracleComp.evalWith (sumHandler ProbComp.unifOracle O) (M.transcript n)).map g).bind κ := by
  simp only [Machine.transcript, OracleComp.evalWith_bind, OracleComp.evalWith_pure,
    Machine.evalWith_next, PMF.map_bind, PMF.bind_map, PMF.pure_map]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun bits hbits => ?_
  rw [Function.comp_apply, ← h bits (length_of_mem_support_transcript M O n bits hbits)]
  rfl

/-- The law of the last bit of a block of `j + 1` steps: a query at the empty address and then
`j` queries at the previous bit. -/
private noncomputable def blockLaw (O : TwoBlockQuery → PMF Bool) : ℕ → PMF Bool
  | 0 => O (.inl ())
  | j + 1 => (blockLaw O j).bind fun bit => O (.inr (.inl bit))

private theorem map_headD_transcript_block (O : TwoBlockQuery → PMF Bool) :
    ∀ j, j ≤ m → (OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((twoBlockMachine m).transcript (j + 1))).map (fun bits => bits.headD false) =
        blockLaw O j
  | 0, _ => by
    rw [map_transcript_succ _ O 0 _ (fun _ => ()) (fun _ => O (.inl ()))]
    · simp [Machine.transcript, blockLaw]
    · intro bits hbits
      rw [stepLaw_twoBlockMachine_start O (Or.inl hbits)]
      exact PMF.map_id _
  | j + 1, hj => by
    rw [map_transcript_succ _ O (j + 1) _ (fun bits => bits.headD false)
      (fun bit => O (.inr (.inl bit))), map_headD_transcript_block O j (by omega), blockLaw]
    intro bits hbits
    rw [stepLaw_twoBlockMachine_copy O (by omega) (by omega) (by omega)]
    exact PMF.map_id _

private theorem map_pair_transcript (O : TwoBlockQuery → PMF Bool) :
    ∀ j, j ≤ m → (OracleComp.evalWith (sumHandler ProbComp.unifOracle O)
      ((twoBlockMachine m).transcript (m + 2 + j))).map
        (fun bits => (bits.getD (j + 1) false, bits.headD false)) =
        (blockLaw O m).bind fun u => (blockLaw O j).map fun v => (u, v)
  | 0, _ => by
    rw [show m + 2 + 0 = (m + 1) + 1 from rfl,
      map_transcript_succ _ O (m + 1) _ (fun bits => bits.headD false)
        (fun u => (O (.inl ())).map fun v => (u, v)),
      map_headD_transcript_block O m le_rfl]
    · rfl
    · intro bits hbits
      rw [stepLaw_twoBlockMachine_start O (Or.inr hbits)]
      cases bits <;> rfl
  | j + 1, hj => by
    rw [show m + 2 + (j + 1) = (m + 2 + j) + 1 from rfl,
      map_transcript_succ _ O (m + 2 + j) _
        (fun bits => (bits.getD (j + 1) false, bits.headD false))
        (fun p => (O (.inr (.inl p.2))).map fun v => (p.1, v)),
      map_pair_transcript O j (by omega)]
    · simp only [blockLaw, PMF.bind_bind, PMF.bind_map, PMF.map_bind]
      rfl
    · intro bits hbits
      rw [stepLaw_twoBlockMachine_copy O (by omega) (by omega) (by omega)]
      rfl

/-- **The law of the run.** Against any oracle, the output of the two-block machine is the
answer at the pair of two independent draws of the block law. -/
private theorem evalWith_run_twoBlockMachine_eq_bind (m : ℕ) (O : TwoBlockQuery → PMF Bool) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle O) ((twoBlockMachine m).run (2 * m + 3)) =
      (blockLaw O m).bind fun u => (blockLaw O m).bind fun v => O (.inr (.inr (u, v))) := by
  rw [Machine.run, OracleComp.evalWith_map, show 2 * m + 3 = (m + 2 + m) + 1 by omega,
    map_transcript_succ _ O (m + 2 + m) _
      (fun bits => (bits.getD (m + 1) false, bits.headD false))
      (fun p => O (.inr (.inr p))),
    map_pair_transcript O m le_rfl]
  · simp only [PMF.bind_bind, PMF.bind_map]
    rfl
  · intro bits hbits
    rw [stepLaw_twoBlockMachine_pair O (by omega)]
    exact PMF.map_id _

/-! ### Definition 6.1 -/

/-- Two independent draws of any law give the pair lookup the expected answer `c`. -/
private theorem bind_pair_apply_true (μ start : PMF Bool) (c : ℝ) (hc0 : 0 ≤ c)
    (hc1 : 2 * c ≤ 1) :
    (μ.bind fun u => μ.bind fun v => twoBlockOracle start c hc0 hc1 (.inr (.inr (u, v)))) true =
      ENNReal.ofReal c := by
  have hab := Probability.PMF.apply_true_add_apply_false μ
  have h2 : ENNReal.ofReal (2 * c) = 2 * ENNReal.ofReal c := by
    rw [ENNReal.ofReal_mul (by norm_num)]
    simp
  simp only [PMF.bind_apply, tsum_bool, twoBlockOracle, Probability.PMF.coin_apply,
    PMF.pure_apply, h2]
  simp only [Bool.true_eq_false, ↓reduceIte, mul_zero, add_zero]
  calc _ = ENNReal.ofReal c * (μ true + μ false) ^ 2 := by ring
    _ = ENNReal.ofReal c := by rw [hab, one_pow, mul_one]

/-- The two-block machine accepts with probability exactly `c`, whatever the start law. -/
theorem evalWith_run_twoBlockMachine (m : ℕ) (start : PMF Bool) (c : ℝ) (hc0 : 0 ≤ c)
    (hc1 : 2 * c ≤ 1) :
    OracleComp.evalWith (sumHandler ProbComp.unifOracle (twoBlockOracle start c hc0 hc1))
      ((twoBlockMachine m).run (2 * m + 3)) true = ENNReal.ofReal c := by
  rw [evalWith_run_twoBlockMachine_eq_bind, bind_pair_apply_true]

/-- **The two-block machine satisfies Definition 6.1 with constant `1`, non-strictly**, for every
`m`, every start law and every `c`. Under any one oracle the two blocks are independent with the
same law, so the original pair lookup has expected answer `c`, and the lookup itself moves by at
most the perturbation. -/
theorem lipschitzAt_run_twoBlockMachine (m : ℕ) (start : PMF Bool) (c : ℝ) (hc0 : 0 ≤ c)
    (hc1 : 2 * c ≤ 1) :
    LipschitzAt 1 (twoBlockOracle start c hc0 hc1) ((twoBlockMachine m).run (2 * m + 3)) := by
  intro O' ε hε
  have heq : ((blockLaw (twoBlockOracle start c hc0 hc1) m).bind fun u =>
      (blockLaw (twoBlockOracle start c hc0 hc1) m).bind fun v =>
        twoBlockOracle start c hc0 hc1 (.inr (.inr (u, v)))) =
      (blockLaw O' m).bind fun u => (blockLaw O' m).bind fun v =>
        twoBlockOracle start c hc0 hc1 (.inr (.inr (u, v))) :=
    Probability.PMF.ext_bool (by rw [bind_pair_apply_true, bind_pair_apply_true])
  rw [evalWith_run_twoBlockMachine_eq_bind, evalWith_run_twoBlockMachine_eq_bind, heq,
    ENNReal.coe_one, one_mul]
  exact Probability.CloseTo.bind_right _ fun u _ =>
    Probability.CloseTo.bind_right _ fun v _ => hε _

/-! ### The attack -/

/-- The claims of the attacking proposer, as a function of the bits written so far. At a start
step it claims `0`, and at a copy step the probability `1` or `0` given by the previous bit,
which are the exact probabilities, except that in the first block it claims `k / N` at the
address `false`. At the final lookup it claims `κ₁ / N` when the first block ended at `true`
and `κ₀ / N` otherwise; `κ₁` and `κ₀` are parameters, meant as grid approximations of the two
probabilities that can occur there. -/
@[expose] def twoBlockClaim {N : ℕ} (m : ℕ) (k κ₁ κ₀ : Fin (N + 1)) (bits : List Bool) :
    Fin (N + 1) :=
  if bits.length = 0 ∨ bits.length = m + 1 then 0
  else if bits.length < 2 * m + 2 then
    if bits.headD false then Fin.last N else if bits.length ≤ m then k else 0
  else if bits.getD (m + 1) false then κ₁ else κ₀

/-- The proposer that wins against the two-block machine. It has no state, draws no samples,
and its copy returns a uniform coin, as the honest proposer's does. -/
noncomputable def twoBlockProposer (P : Params) (m : ℕ) (k κ₁ κ₀ : Fin (P.grid + 1)) :
    Proposer P.grid where
  State := Unit
  init := ()
  claim history := pure (twoBlockClaim m k κ₁ κ₀ history.bits)
  coin := (honestProposer P).coin

/-- One round with a known claim and a uniform coin from the proposer's side: if `g` bounds the
acceptance probability after the round, and an abort is accepted at least that often, then the
round is worth the mean of `g` under the claimed probability. The challenger decides after the
bit is set, as in Figure 1. -/
private theorem le_evalWith_runFrom_succ {law : List Bool → PMF Bool} (P : Params)
    [NeZero P.grid] (A : Proposer P.grid) (B : Challenger P.grid) (n : ℕ)
    (history : History P.grid) (stateA stateA' : A.State) (stateB : B.State)
    (claim : Fin (P.grid + 1))
    (hclaim : OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
      ((A.claim history).run stateA) = PMF.pure (claim, stateA'))
    (hcoin : OracleComp.evalWith (sumHandler ProbComp.unifOracle law) (A.coin history claim) =
      Probability.PMF.uniformOfFintype (ZMod P.grid))
    (g : Bool → ℝ≥0∞)
    (hab : ∀ bit, g bit ≤
      OracleComp.evalWith (sumHandler ProbComp.unifOracle law) (verdict P history.bits claim) true)
    (hnext : ∀ coinA coinB stateB', g (coinBit claim coinA coinB) ≤
      OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
        (runFrom P A B n (⟨claim, coinA, coinB⟩ :: history) stateA' stateB') true) :
    (claim.val : ℝ≥0∞) / P.grid * g true + (1 - (claim.val : ℝ≥0∞) / P.grid) * g false ≤
      OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
        (runFrom P A B (n + 1) history stateA stateB) true := by
  simp only [runFrom, OracleComp.evalWith_bind,
    apply_ite (OracleComp.evalWith (sumHandler ProbComp.unifOracle law)), hclaim, hcoin,
    PMF.pure_bind]
  refine Probability.PMF.le_bind_apply_on_support _ fun coinA _ => ?_
  rw [PMF.bind_apply]
  have htrue := map_coinBit_uniformOfFintype_right claim coinA
  have hfalse := map_coinBit_uniformOfFintype_right_false claim coinA
  calc _ = ∑' coinB, Probability.PMF.uniformOfFintype (ZMod P.grid) coinB *
        g (coinBit claim coinA coinB) := by
        rw [← Probability.PMF.tsum_map_mul (Probability.PMF.uniformOfFintype (ZMod P.grid))
          (fun coinB => coinBit claim coinA coinB) g, tsum_bool, hfalse, htrue, add_comm]
    _ ≤ _ := tsum_le_tsum fun coinB => mul_le_mul_right ?_ _
  refine Probability.PMF.le_bind_apply_on_support _ fun r _ => ?_
  by_cases hr : r.1 = true
  · simp only [hr, ↓reduceIte]
    exact hab _
  · simp only [hr]
    exact hnext coinA coinB r.2

/-- The acceptance bound of the attack from a given transcript: scaled by `s`, the value `2 a`
once the first block has reached `true`, and `a + a (1 - (1 - δ) ^ j)` with `j` flips left. -/
private noncomputable def twoBlockBound (m : ℕ) (s a δ : ℝ≥0∞) (bits : List Bool) : ℝ≥0∞ :=
  if bits.length = 0 then s * (a + a * (1 - (1 - δ) ^ m))
  else if bits.length ≤ m + 1 then
    if bits.headD false then s * (2 * a)
    else s * (a + a * (1 - (1 - δ) ^ (m + 1 - bits.length)))
  else if bits.length ≤ 2 * m + 2 then
    if bits.headD false then 0
    else if bits.getD (bits.length - (m + 1)) false then s * (2 * a) else s * a
  else if bits.headD false then s else 0

section Bound

variable {s a δ : ℝ≥0∞} {bits : List Bool}

private theorem twoBlockBound_block1 (h0 : bits.length ≠ 0) (h1 : bits.length ≤ m + 1) :
    twoBlockBound m s a δ bits =
      if bits.headD false then s * (2 * a)
      else s * (a + a * (1 - (1 - δ) ^ (m + 1 - bits.length))) := by
  simp only [twoBlockBound, h0, h1, ↓reduceIte]

private theorem twoBlockBound_block2 (h1 : m + 1 < bits.length) (h2 : bits.length ≤ 2 * m + 2) :
    twoBlockBound m s a δ bits =
      if bits.headD false then 0
      else if bits.getD (bits.length - (m + 1)) false then s * (2 * a) else s * a := by
  have h0 : bits.length ≠ 0 := by omega
  have h1' : ¬ bits.length ≤ m + 1 := by omega
  simp only [twoBlockBound, h0, h1', h2, ↓reduceIte]

private theorem twoBlockBound_end (h : 2 * m + 2 < bits.length) :
    twoBlockBound m s a δ bits = if bits.headD false then s else 0 := by
  have h0 : bits.length ≠ 0 := by omega
  have h1 : ¬ bits.length ≤ m + 1 := by omega
  have h2 : ¬ bits.length ≤ 2 * m + 2 := by omega
  simp only [twoBlockBound, h0, h1, h2, ↓reduceIte]

private theorem twoBlockBound_le_one (hs : s ≤ 1) (ha : 2 * a ≤ 1) :
    twoBlockBound m s a δ bits ≤ 1 := by
  have h2 : s * (2 * a) ≤ 1 := mul_le_one' hs ha
  have h1 (x : ℝ≥0∞) : s * (a + a * (1 - x)) ≤ 1 := by
    refine le_trans ?_ h2
    gcongr
    calc a + a * (1 - x) ≤ a + a * 1 := by gcongr; exact tsub_le_self
      _ = 2 * a := by ring
  have h0 : s * a ≤ 1 := le_trans (by gcongr; exact le_mul_of_one_le_left zero_le (by norm_num)) h2
  unfold twoBlockBound
  split_ifs <;> first | exact h1 _ | exact h2 | exact h0 | exact hs | exact zero_le

end Bound

/-- One more round of the first block. -/
private theorem twoBlockBound_step {s a δ : ℝ≥0∞} (hδ : δ ≤ 1) (j : ℕ) :
    s * (a + a * (1 - (1 - δ) ^ (j + 1))) ≤
      δ * (s * (2 * a)) + (1 - δ) * (s * (a + a * (1 - (1 - δ) ^ j))) := by
  have h1 : 1 - δ + δ = 1 := tsub_add_cancel_of_le hδ
  calc s * (a + a * (1 - (1 - δ) ^ (j + 1)))
      ≤ s * (a * (1 - δ + δ) + a * ((1 - δ) * (1 - (1 - δ) ^ j) + δ)) := by
        rw [h1, mul_one]
        gcongr
        exact ENNReal.one_sub_pow_succ_le hδ j
    _ = _ := by ring

section Claim

variable {N : ℕ} {k κ₁ κ₀ : Fin (N + 1)} {bits : List Bool}

private theorem twoBlockClaim_copy (h0 : bits.length ≠ 0) (h1 : bits.length ≠ m + 1)
    (h2 : bits.length < 2 * m + 2) :
    twoBlockClaim m k κ₁ κ₀ bits =
      if bits.headD false then Fin.last N else if bits.length ≤ m then k else 0 := by
  simp only [twoBlockClaim, h0, h1, h2, or_self, ↓reduceIte]

private theorem twoBlockClaim_pair (h : bits.length = 2 * m + 2) :
    twoBlockClaim m k κ₁ κ₀ bits = if bits.getD (m + 1) false then κ₁ else κ₀ := by
  have h0 : bits.length ≠ 0 := by omega
  have h1 : bits.length ≠ m + 1 := by omega
  have h2 : ¬ bits.length < 2 * m + 2 := by omega
  simp only [twoBlockClaim, h0, h1, h2, or_self, ↓reduceIte]

end Claim

/-- The acceptance bound of the attack from any transcript of the right length. -/
private theorem twoBlockBound_le_evalWith_runFrom {law : List Bool → PMF Bool} (P : Params)
    [NeZero P.grid] (m : ℕ) (k κ₁ κ₀ : Fin (P.grid + 1)) (v a : ℝ≥0∞)
    (hstart : ∀ bits : List Bool, bits.length = 0 ∨ bits.length = m + 1 →
      law bits = PMF.pure false)
    (hcopy : ∀ bits : List Bool, bits.length ≠ 0 → bits.length ≠ m + 1 →
      bits.length < 2 * m + 2 → law bits = PMF.pure (bits.headD false))
    (hk0 : 0 < (k.val : ℝ) / P.grid) (hk : (k.val : ℝ) / P.grid < P.verifierTolerance)
    (hsamples : 0 < P.verifierSamples)
    (ha : (κ₀.val : ℝ≥0∞) / P.grid = a) (ha₁ : (κ₁.val : ℝ≥0∞) / P.grid = 2 * a)
    (ha2 : 2 * a ≤ 1)
    (hver : ∀ bits : List Bool, bits.length = 2 * m + 2 → bits.headD false = false →
      1 - v ≤ OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
        (verdict P bits (twoBlockClaim m k κ₁ κ₀ bits)) true)
    (B : Challenger P.grid) :
    ∀ n (history : History P.grid) (stateA : (twoBlockProposer P m k κ₁ κ₀).State)
      (stateB : B.State), history.bits.length + n = 2 * m + 3 →
      twoBlockBound m (1 - v) a ((k.val : ℝ≥0∞) / P.grid) history.bits ≤
        OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
          (runFrom P (twoBlockProposer P m k κ₁ κ₀) B n history stateA stateB) true
  | 0, history, stateA, stateB, hlen => by
    rw [runFrom, OracleComp.evalWith_pure, PMF.pure_apply, twoBlockBound_end (by omega)]
    cases history.bits.headD false <;> simp
  | n + 1, history, stateA, stateB, hlen => by
    have hN : (P.grid : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P.grid)
    have hNe : (P.grid : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne P.grid)
    have hs : 1 - v ≤ 1 := tsub_le_self
    have htol : 0 < P.verifierTolerance := hk0.trans hk
    have hδ : (k.val : ℝ≥0∞) / P.grid ≤ 1 :=
      ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Nat.lt_succ_iff.1 k.2)
    -- One round, with the bound for the next transcript as the value after it.
    have key := fun hab => le_evalWith_runFrom_succ (law := law) P (twoBlockProposer P m k κ₁ κ₀)
      B n history stateA stateA stateB (twoBlockClaim m k κ₁ κ₀ history.bits) rfl
      (evalWith_uniformCoin law)
      (fun bit => twoBlockBound m (1 - v) a ((k.val : ℝ≥0∞) / P.grid) (bit :: history.bits)) hab
      (fun coinA coinB stateB' => twoBlockBound_le_evalWith_runFrom P m k κ₁ κ₀ v a hstart hcopy
        hk0 hk hsamples ha ha₁ ha2 hver B n
        (⟨twoBlockClaim m k κ₁ κ₀ history.bits, coinA, coinB⟩ :: history) stateA stateB'
        (by simp only [History.bits, List.map_cons, List.length_cons] at hlen ⊢; omega))
    -- An abort at a deterministic step is accepted.
    have hpure (bit : Bool) (hlaw : law history.bits = PMF.pure bit)
        (hclose : |((twoBlockClaim m k κ₁ κ₀ history.bits).val : ℝ) / P.grid -
          (if bit then 1 else 0)| < P.verifierTolerance) (bit' : Bool) :
        twoBlockBound m (1 - v) a ((k.val : ℝ≥0∞) / P.grid) (bit' :: history.bits) ≤
          OracleComp.evalWith (sumHandler ProbComp.unifOracle law)
            (verdict P history.bits (twoBlockClaim m k κ₁ κ₀ history.bits)) true := by
      rw [evalWith_verdict_of_pure P hsamples hlaw _ hclose, PMF.pure_apply_self]
      exact twoBlockBound_le_one hs ha2
    have hzero (x y : ℝ≥0∞) :
        (((0 : Fin (P.grid + 1)).val : ℕ) : ℝ≥0∞) / P.grid * x +
          (1 - (((0 : Fin (P.grid + 1)).val : ℕ) : ℝ≥0∞) / P.grid) * y = y := by
      simp
    have hlast (x y : ℝ≥0∞) :
        (((Fin.last P.grid).val : ℕ) : ℝ≥0∞) / P.grid * x +
          (1 - (((Fin.last P.grid).val : ℕ) : ℝ≥0∞) / P.grid) * y = x := by
      rw [Fin.val_last, ENNReal.div_self hNe (ENNReal.natCast_ne_top _)]
      simp
    generalize hbits : history.bits = bits at *
    have hL : bits.length ≤ 2 * m + 2 := by omega
    rcases Nat.eq_zero_or_pos bits.length with h0 | h0
    · -- The first step: the truth is `false` and the claim is `0`.
      have hclaim : twoBlockClaim m k κ₁ κ₀ bits = 0 := by
        simp only [twoBlockClaim, h0, true_or, ↓reduceIte]
      rw [hclaim] at key hpure
      refine le_trans ?_ (key (hpure false (hstart bits (Or.inl h0)) (by simpa using htol)))
      rw [hzero, twoBlockBound_block1 (bits := false :: bits) (by simp)
        (by rw [List.length_cons]; omega)]
      simp only [twoBlockBound, h0, ↓reduceIte, List.headD_cons, Bool.false_eq_true,
        List.length_cons, zero_add, Nat.add_sub_cancel]
      exact le_rfl
    rcases Nat.lt_or_ge bits.length (m + 1) with h1 | h1
    · -- A later step of the first block.
      have hclaim := twoBlockClaim_copy (m := m) (k := k) (κ₁ := κ₁) (κ₀ := κ₀) (bits := bits)
        (by omega) (by omega) (by omega)
      have hlaw := hcopy bits (by omega) (by omega) (by omega)
      have hm : bits.length ≤ m := by omega
      rw [twoBlockBound_block1 (by omega) (by omega)]
      rcases Bool.eq_false_or_eq_true (bits.headD false) with hhead | hhead
      · simp only [hhead, ↓reduceIte] at hclaim hlaw ⊢
        rw [hclaim] at key hpure
        refine le_trans ?_ (key (hpure true hlaw (by simpa [hN] using htol)))
        rw [hlast, twoBlockBound_block1 (bits := true :: bits) (by simp)
          (by rw [List.length_cons]; omega)]
        simp
      · simp only [hhead, Bool.false_eq_true, hm, ↓reduceIte] at hclaim hlaw ⊢
        rw [hclaim] at key hpure
        refine le_trans ?_ (key (hpure false hlaw (by simpa [abs_of_pos hk0] using hk)))
        rw [twoBlockBound_block1 (bits := true :: bits) (by simp)
            (by rw [List.length_cons]; omega),
          twoBlockBound_block1 (bits := false :: bits) (by simp)
            (by rw [List.length_cons]; omega)]
        simp only [List.headD_cons, ↓reduceIte, Bool.false_eq_true, List.length_cons]
        rw [show m + 1 - bits.length = (m + 1 - (bits.length + 1)) + 1 by omega]
        exact twoBlockBound_step hδ _
    rcases Nat.eq_or_lt_of_le h1 with h2 | h2
    · -- The first step of the second block: the truth is `false` and the claim is `0`.
      have hclaim : twoBlockClaim m k κ₁ κ₀ bits = 0 := by
        simp only [twoBlockClaim, ← h2, or_true, ↓reduceIte]
      rw [hclaim] at key hpure
      refine le_trans ?_ (key (hpure false (hstart bits (Or.inr h2.symm)) (by simpa using htol)))
      rw [hzero, twoBlockBound_block1 (bits := bits) (by omega) (by omega),
        twoBlockBound_block2 (bits := false :: bits) (by rw [List.length_cons]; omega)
          (by rw [List.length_cons]; omega)]
      simp only [List.headD_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons, ← h2,
        Nat.add_sub_cancel_left, List.getD_cons_succ, ← List.headD_eq_getD,
        pow_zero, tsub_self, mul_zero, add_zero]
      exact le_rfl
    rw [twoBlockBound_block2 (by omega) hL]
    rcases Bool.eq_false_or_eq_true (bits.headD false) with hhead | hhead
    · simp only [hhead, ↓reduceIte]
      exact zero_le
    simp only [hhead, Bool.false_eq_true, ↓reduceIte]
    rcases Nat.lt_or_ge bits.length (2 * m + 2) with h3 | h3
    · -- A later step of the second block: the last bit is `false` and the claim is `0`.
      have hclaim := twoBlockClaim_copy (m := m) (k := k) (κ₁ := κ₁) (κ₀ := κ₀) (bits := bits)
        (by omega) (by omega) (by omega)
      have hlaw := hcopy bits (by omega) (by omega) (by omega)
      have hm : ¬ bits.length ≤ m := by omega
      simp only [hhead, Bool.false_eq_true, hm, ↓reduceIte] at hclaim hlaw
      rw [hclaim] at key hpure
      refine le_trans ?_ (key (hpure false hlaw (by simpa using htol)))
      rw [hzero, twoBlockBound_block2 (bits := false :: bits) (by rw [List.length_cons]; omega)
        (by rw [List.length_cons]; omega)]
      simp only [List.headD_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      simp only [show bits.length + 1 - (m + 1) = (bits.length - (m + 1)) + 1 by omega,
        List.getD_cons_succ]
      exact le_rfl
    · -- The last step: the claim is near the truth, and the bit is `true` as often as claimed.
      have hlen' : bits.length = 2 * m + 2 := by omega
      have hclaim := twoBlockClaim_pair (k := k) (κ₁ := κ₁) (κ₀ := κ₀) hlen'
      refine le_trans ?_ (key fun bit => ?_)
      · rw [twoBlockBound_end (bits := true :: bits) (by rw [List.length_cons]; omega),
          twoBlockBound_end (bits := false :: bits) (by rw [List.length_cons]; omega), hclaim,
          show bits.length - (m + 1) = m + 1 by omega]
        simp only [List.headD_cons, ↓reduceIte, Bool.false_eq_true, mul_zero, add_zero]
        split_ifs
        · rw [ha₁, mul_comm]
        · rw [ha, mul_comm]
      · refine le_trans ?_ (hver bits hlen' hhead)
        rw [twoBlockBound_end (by rw [List.length_cons]; omega)]
        split_ifs
        · exact le_rfl
        · exact zero_le

/-- **The attack on a machine with oracle queries of length at most two.** Let the oracle answer
`false` at the empty address, let its parameter satisfy `0 ≤ c` and `2 c ≤ 1`, and let the protocol
have `2 m + 3` rounds and at least one verifier sample. For any claim `k / N` that is positive and
below the verifier's tolerance, and any last claims `κ₁ = 2 κ₀`, `twoBlockProposer` makes the
verifier accept on the two-block machine with probability at least
`(1 - v) (a + a (1 - (1 - k / N) ^ m))` against every challenger, where `a = κ₀ / N` and `v` bounds
the probability that the verifier rejects the last claim after an abort. The machine itself accepts
with probability `c`, and the bound is close to `c + c (1 - (1 - k / N) ^ m)` when `a` is close to
`c` and `v` is small.

The challenger is an arbitrary program with private state. As in Figure 1, it decides whether
to abort after the bit of the round is set. Before the last round an abort does not help it:
every answer is deterministic, so the verifier's samples are exact and it accepts the claim.
In the last round the verifier's rejection probability after an abort is at most `v`. -/
theorem le_evalWith_run_twoBlockProposer (P : Params) (m : ℕ) (hrounds : P.rounds = 2 * m + 3)
    (k κ₁ κ₀ : Fin (P.grid + 1)) (hk0 : 0 < (k.val : ℝ) / P.grid)
    (hk : (k.val : ℝ) / P.grid < P.verifierTolerance) (hsamples : 0 < P.verifierSamples)
    (hκ : κ₁.val = 2 * κ₀.val) (c : ℝ) (hc0 : 0 ≤ c) (hc1 : 2 * c ≤ 1) (v : ℝ≥0∞)
    (hver : ∀ bits : List Bool, bits.length = 2 * m + 2 → bits.headD false = false →
      1 - v ≤ OracleComp.evalWith
        (sumHandler ProbComp.unifOracle
          ((twoBlockMachine m).stepLaw (twoBlockOracle (PMF.pure false) c hc0 hc1)))
        (verdict P bits (twoBlockClaim m k κ₁ κ₀ bits)) true)
    (B : Challenger P.grid) :
    (1 - v) * ((κ₀.val : ℝ≥0∞) / P.grid +
        (κ₀.val : ℝ≥0∞) / P.grid * (1 - (1 - (k.val : ℝ≥0∞) / P.grid) ^ m)) ≤
      OracleComp.evalWith
        (sumHandler ProbComp.unifOracle
          ((twoBlockMachine m).stepLaw (twoBlockOracle (PMF.pure false) c hc0 hc1)))
        (run P (twoBlockProposer P m k κ₁ κ₀) B) true := by
  have hN : P.grid ≠ 0 := by
    intro h
    have hcast : (P.grid : ℝ) = 0 := by exact_mod_cast h
    rw [hcast, div_zero] at hk0
    exact lt_irrefl _ hk0
  have : NeZero P.grid := ⟨hN⟩
  have ha₁ : (κ₁.val : ℝ≥0∞) / P.grid = 2 * ((κ₀.val : ℝ≥0∞) / P.grid) := by
    rw [hκ, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc]
  have ha2 : 2 * ((κ₀.val : ℝ≥0∞) / P.grid) ≤ 1 := by
    rw [← ha₁]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact_mod_cast Nat.lt_succ_iff.1 κ₁.2)
  have h := twoBlockBound_le_evalWith_runFrom
    (law := (twoBlockMachine m).stepLaw (twoBlockOracle (PMF.pure false) c hc0 hc1)) P m k κ₁ κ₀
    v _ (fun bits hbits => stepLaw_twoBlockMachine_start _ hbits)
    (fun bits h0 h1 h2 => stepLaw_twoBlockMachine_copy _ h0 h1 h2) hk0 hk hsamples rfl ha₁ ha2
    hver B P.rounds [] (twoBlockProposer P m k κ₁ κ₀).init B.init (by simp [History.bits, hrounds])
  exact h

/-! ### The constants of the source -/

private theorem one_sub_le_apply_true {p : PMF Bool} {v : ℝ≥0∞} (h : p false ≤ v) :
    1 - v ≤ p true := by
  rw [tsub_le_iff_right, ← Probability.PMF.apply_true_add_apply_false p]
  gcongr

private theorem exp_neg_six_le : Real.exp (-6) ≤ 1 / 400 := by
  have h6 : (400 : ℝ) ≤ Real.exp 6 := by
    have h := Real.exp_one_gt_d9
    have hpow : (2.7182818283 : ℝ) ^ 6 ≤ Real.exp 1 ^ 6 := by gcongr
    rw [← Real.exp_nat_mul] at hpow
    norm_num at hpow ⊢
    linarith
  rw [Real.exp_neg, one_div]
  exact inv_anti₀ (by norm_num) h6

private theorem exp_neg_one_le : Real.exp (-1) ≤ 37 / 100 := by
  rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos 1) (by norm_num)]
  linarith [Real.exp_one_gt_d9]

/-- The attack with the constants of Figure 1, for a Lipschitz constant `K` with
`d = ⌈150 K⌉ ≥ 150` and at least `4 d + 1` steps in a block. -/
private theorem exists_proposer_two_fifths_lt_twoBlock (K : ℝ≥0) (d : ℕ)
    (hd : ⌈150 * (K : ℝ)⌉₊ = d) (hd150 : 150 ≤ d) (m : ℕ) (hm : 4 * d + 1 ≤ m) :
    ∃ A : Proposer (Params.figure1 K (2 * m + 3)).grid,
      ∀ B : Challenger (Params.figure1 K (2 * m + 3)).grid,
        2 / 5 < OracleComp.evalWith
          (sumHandler ProbComp.unifOracle ((twoBlockMachine m).stepLaw
            (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))))
          (run (Params.figure1 K (2 * m + 3)) A B) true := by
  have hdR : (150 : ℝ) ≤ d := by exact_mod_cast hd150
  have hd0 : (0 : ℝ) < d := by linarith
  -- The grid and the verifier's sample count are large.
  have hgrid : 192 * (d : ℝ) ^ 2 ≤ ((Params.figure1 K (2 * m + 3)).grid : ℝ) := by
    have hlog : (1 : ℝ) ≤ Real.log (100 * ((2 * m + 3 : ℕ) : ℝ)) := by
      have h3 : (3 : ℝ) ≤ ((2 * m + 3 : ℕ) : ℝ) := by exact_mod_cast (by omega : 3 ≤ 2 * m + 3)
      rw [Real.le_log_iff_exp_le (by positivity)]
      linarith [Real.exp_one_lt_d9]
    calc 192 * (d : ℝ) ^ 2
        ≤ 192 * ((⌈150 * (K : ℝ)⌉₊ : ℕ) : ℝ) ^ 2 * Real.log (100 * ((2 * m + 3 : ℕ) : ℝ)) := by
          rw [hd]
          exact le_mul_of_one_le_right (by positivity) hlog
      _ ≤ _ := Nat.le_ceil _
  have hr : 192 * (d : ℝ) ^ 2 ≤ ((Params.figure1 K (2 * m + 3)).verifierSamples : ℝ) := by
    have hlog : (1 : ℝ) ≤ Real.log 100 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      linarith [Real.exp_one_lt_d9]
    calc 192 * (d : ℝ) ^ 2 ≤ 192 * ((⌈150 * (K : ℝ)⌉₊ : ℕ) : ℝ) ^ 2 * Real.log 100 := by
          rw [hd]
          exact le_mul_of_one_le_right (by positivity) hlog
      _ ≤ _ := Nat.le_ceil _
  have htol : (Params.figure1 K (2 * m + 3)).verifierTolerance = 1 / (4 * (d : ℝ)) := by
    change 1 / (4 * ((⌈150 * (K : ℝ)⌉₊ : ℕ) : ℝ)) = _
    rw [hd]
  have hrounds : (Params.figure1 K (2 * m + 3)).rounds = 2 * m + 3 := rfl
  generalize Params.figure1 K (2 * m + 3) = P at hgrid hr htol hrounds ⊢
  have hNbig : (4320000 : ℝ) ≤ (P.grid : ℝ) := by nlinarith
  have hNpos : (0 : ℝ) < (P.grid : ℝ) := by linarith
  have hNnat : 0 < P.grid := by exact_mod_cast hNpos
  have hsamples : 0 < P.verifierSamples := by
    have : (0 : ℝ) < (P.verifierSamples : ℝ) := by nlinarith
    exact_mod_cast this
  -- The claim `k / N` of the first block lies in `[1 / (4 d + 1), 1 / (4 d))`.
  have hx0 : (0 : ℝ) < (P.grid : ℝ) / (4 * d + 1) := by positivity
  have hx : (P.grid : ℝ) / (4 * d + 1) * (4 * d + 1) = P.grid :=
    div_mul_cancel₀ _ (by positivity)
  have hx4 : 4 * (d : ℝ) ≤ (P.grid : ℝ) / (4 * d + 1) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  have hkge : (P.grid : ℝ) / (4 * d + 1) ≤ (⌈(P.grid : ℝ) / (4 * d + 1)⌉₊ : ℝ) := Nat.le_ceil _
  have hklt : (⌈(P.grid : ℝ) / (4 * d + 1)⌉₊ : ℝ) < (P.grid : ℝ) / (4 * d + 1) + 1 :=
    Nat.ceil_lt_add_one hx0.le
  generalize ⌈(P.grid : ℝ) / (4 * d + 1)⌉₊ = k at hkge hklt
  generalize (P.grid : ℝ) / (4 * d + 1) = x at hx0 hx hx4 hkge hklt
  have hkN : k ≤ P.grid := by
    have : (k : ℝ) ≤ P.grid := by nlinarith
    exact_mod_cast this
  have hk0 : 0 < (k : ℝ) / P.grid := div_pos (by linarith) hNpos
  have hk : (k : ℝ) / P.grid < P.verifierTolerance := by
    rw [htol, div_lt_div_iff₀ hNpos (by positivity)]
    nlinarith
  have hδ₀ : 1 / (4 * (d : ℝ) + 1) ≤ (k : ℝ) / P.grid := by
    rw [div_le_div_iff₀ (by positivity) hNpos]
    nlinarith
  -- The last claims `2 ⌊N / 4⌋ / N` and `⌊N / 4⌋ / N` are near `1 / 2` and `1 / 4`.
  have hq1 : 4 * ((P.grid / 4 : ℕ) : ℝ) ≤ (P.grid : ℝ) := by
    exact_mod_cast (by omega : 4 * (P.grid / 4) ≤ P.grid)
  have hq2 : (P.grid : ℝ) < 4 * ((P.grid / 4 : ℕ) : ℝ) + 4 := by
    exact_mod_cast (by omega : P.grid < 4 * (P.grid / 4) + 4)
  have hupper : ((P.grid / 4 : ℕ) : ℝ) / P.grid ≤ 1 / 4 := by
    rw [div_le_div_iff₀ hNpos (by norm_num)]
    linarith
  have hlower : 1 / 4 - 1 / (P.grid : ℝ) ≤ ((P.grid / 4 : ℕ) : ℝ) / P.grid := by
    rw [sub_le_iff_le_add, ← add_div, div_le_div_iff₀ (by norm_num) hNpos]
    linarith
  have hinv : 2 / (P.grid : ℝ) ≤ 1 / (8 * d) := by
    rw [div_le_div_iff₀ hNpos (by positivity)]
    nlinarith
  have hinv' : 1 / (P.grid : ℝ) ≤ 1 / 10000 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hhalf : 1 / (8 * (d : ℝ)) + 1 / (8 * d) = 1 / (4 * d) := by
    field_simp
    norm_num
  have h2N : 2 / (P.grid : ℝ) = 2 * (1 / P.grid) := by ring
  -- After an abort in the last round the verifier rejects with probability at most `1 / 200`.
  have hver : ∀ bits : List Bool, bits.length = 2 * m + 2 → bits.headD false = false →
      1 - ENNReal.ofReal (1 / 200) ≤ OracleComp.evalWith
        (sumHandler ProbComp.unifOracle ((twoBlockMachine m).stepLaw
          (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))))
        (verdict P bits (twoBlockClaim m ⟨k, Nat.lt_succ_of_le hkN⟩
          ⟨2 * (P.grid / 4), by omega⟩ ⟨P.grid / 4, by omega⟩ bits)) true := by
    intro bits hlen hhead
    refine one_sub_le_apply_true (le_trans (evalWith_verdict_false_le _ P hsamples bits _
      (e := 1 / (8 * d)) (by positivity) ?_) (ENNReal.ofReal_le_ofReal ?_))
    · rw [twoBlockClaim_pair hlen, stepLaw_twoBlockMachine_pair _ hlen, hhead, htol]
      rcases Bool.eq_false_or_eq_true (bits.getD (m + 1) false) with hU | hU
      · rw [hU]
        simp only [↓reduceIte, twoBlockOracle, Probability.PMF.coin_apply_toReal,
          Nat.cast_mul, Nat.cast_ofNat]
        rw [mul_div_assoc]
        have := abs_le.2 ⟨(by linarith : -(2 / (P.grid : ℝ)) ≤
          2 * (((P.grid / 4 : ℕ) : ℝ) / P.grid) - 2 * (1 / 4)), (by linarith)⟩
        linarith
      · rw [hU]
        simp only [Bool.false_eq_true, ↓reduceIte, twoBlockOracle,
          Probability.PMF.coin_apply_toReal]
        have := abs_le.2 ⟨(by linarith : -(2 / (P.grid : ℝ)) ≤
          ((P.grid / 4 : ℕ) : ℝ) / P.grid - 1 / 4), (by linarith)⟩
        linarith
    · have hexp : Real.exp (-2 * (P.verifierSamples : ℝ) * (1 / (8 * d)) ^ 2) ≤ Real.exp (-6) := by
        refine Real.exp_le_exp.2 ?_
        have : (6 : ℝ) ≤ 2 * (P.verifierSamples : ℝ) * (1 / (8 * d)) ^ 2 := by
          rw [one_div, inv_pow, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
          nlinarith
        linarith
      linarith [exp_neg_six_le]
  refine ⟨twoBlockProposer P m ⟨k, Nat.lt_succ_of_le hkN⟩ ⟨2 * (P.grid / 4), by omega⟩
    ⟨P.grid / 4, by omega⟩, fun B => ?_⟩
  refine lt_of_lt_of_le ?_ (le_evalWith_run_twoBlockProposer P m hrounds _ _ _ hk0 hk hsamples rfl
    (1 / 4) (by norm_num) (by norm_num) (ENNReal.ofReal (1 / 200)) hver B)
  dsimp only
  have ha : ENNReal.ofReal (2499 / 10000) ≤ ((P.grid / 4 : ℕ) : ℝ≥0∞) / P.grid := by
    rw [← ENNReal.ofReal_div_natCast _ _ hNnat]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  have hδ : ENNReal.ofReal (1 / (4 * (d : ℝ) + 1)) ≤ (k : ℝ≥0∞) / P.grid := by
    rw [← ENNReal.ofReal_div_natCast _ _ hNnat]
    exact ENNReal.ofReal_le_ofReal hδ₀
  have hpow : (1 - (k : ℝ≥0∞) / P.grid) ^ m ≤ ENNReal.ofReal (37 / 100) := by
    have hδ1 : 1 / (4 * (d : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    have hmR : 4 * (d : ℝ) + 1 ≤ m := by exact_mod_cast hm
    calc (1 - (k : ℝ≥0∞) / P.grid) ^ m
        ≤ (1 - ENNReal.ofReal (1 / (4 * (d : ℝ) + 1))) ^ m :=
          pow_le_pow_left' (tsub_le_tsub_left hδ 1) m
      _ = ENNReal.ofReal ((1 - 1 / (4 * (d : ℝ) + 1)) ^ m) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by positivity),
          ENNReal.ofReal_pow (by linarith)]
      _ ≤ ENNReal.ofReal (37 / 100) := ENNReal.ofReal_le_ofReal ?_
    calc (1 - 1 / (4 * (d : ℝ) + 1)) ^ m
        ≤ Real.exp (-(1 / (4 * (d : ℝ) + 1))) ^ m :=
          pow_le_pow_left₀ (by linarith) (Real.one_sub_le_exp_neg _) m
      _ = Real.exp (m * -(1 / (4 * (d : ℝ) + 1))) := (Real.exp_nat_mul _ _).symm
      _ ≤ Real.exp (-1) := by
        refine Real.exp_le_exp.2 ?_
        rw [mul_neg, neg_le_neg_iff, mul_one_div, le_div_iff₀ (by positivity)]
        linarith
      _ ≤ 37 / 100 := exp_neg_one_le
  have hsub : ENNReal.ofReal (63 / 100) ≤ 1 - (1 - (k : ℝ≥0∞) / P.grid) ^ m := by
    calc ENNReal.ofReal (63 / 100) = 1 - ENNReal.ofReal (37 / 100) := by
          rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
          norm_num
      _ ≤ _ := tsub_le_tsub_left hpow 1
  have hs : ENNReal.ofReal (199 / 200) ≤ 1 - ENNReal.ofReal (1 / 200) := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by norm_num)]
    norm_num
  calc (2 / 5 : ℝ≥0∞) = ENNReal.ofReal (2 / 5) := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num)]
        simp
    _ < ENNReal.ofReal (199 / 200 * (2499 / 10000 + 2499 / 10000 * (63 / 100))) :=
      (ENNReal.ofReal_lt_ofReal_iff (by norm_num)).2 (by norm_num)
    _ = ENNReal.ofReal (199 / 200) *
        (ENNReal.ofReal (2499 / 10000) +
          ENNReal.ofReal (2499 / 10000) * ENNReal.ofReal (63 / 100)) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_add (by norm_num) (by norm_num),
        ENNReal.ofReal_mul (by norm_num)]
    _ ≤ _ := by gcongr

/-- **Under the non-strict reading of Definition 6.1, the protocol of Figure 1 is not sound for
a machine with oracle queries of length at most two.** With the constants of
[BrownCohenIrvingPiliouras2024, Figure 1] for `K = 1` (`Params.figure1 1`) and `m ≥ 601`, the
two-block machine of `2 m + 3` steps, against the oracle that answers `false` at the empty
address and has `c = 1 / 4`, is `1`-Lipschitz at its oracle in the non-strict sense and outputs
`true` with probability `1 / 4`, yet some proposer makes the verifier accept with probability
above `2 / 5` against every challenger, where the protocol the source gives for
[BrownCohenIrvingPiliouras2024, Theorem 6.2] claims soundness `2 / 5`. The theorem's existence
claim is not refuted: another protocol may meet it.

The printed Definition 6.1 has a strict inequality, which this machine does not satisfy with
`K = 1`; `not_sound_figure1_two_of_lipschitzAt_run_twoBlockMachine` is the statement for the
printed definition. The checked conclusion is about `Debate.run`, with `2 m + 3` rounds, one
for each step of the machine: claims and coins lie on a grid and the interpreter computes the
bit of each round. In Figure 1 the proposer can announce the same grid probabilities, supply a
uniform share and set the bit as prescribed, with the same probabilities and the same argument
for an abort. The sample counts are rounded up and the logarithm is natural (`Params.figure1`). -/
theorem not_sound_figure1_of_lipschitzAt_run_twoBlockMachine (m : ℕ) (hm : 601 ≤ m) :
    LipschitzAt 1 (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))
        ((twoBlockMachine m).run (2 * m + 3)) ∧
      OracleComp.evalWith (sumHandler ProbComp.unifOracle
        (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num)))
        ((twoBlockMachine m).run (2 * m + 3)) true ≤ 1 / 3 ∧
      ∃ A : Proposer (Params.figure1 1 (2 * m + 3)).grid,
        ∀ B : Challenger (Params.figure1 1 (2 * m + 3)).grid,
          2 / 5 < OracleComp.evalWith
            (sumHandler ProbComp.unifOracle ((twoBlockMachine m).stepLaw
              (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))))
            (run (Params.figure1 1 (2 * m + 3)) A B) true := by
  refine ⟨lipschitzAt_run_twoBlockMachine m _ _ _ _, ?_, ?_⟩
  · rw [evalWith_run_twoBlockMachine, ENNReal.ofReal_div_of_pos (by norm_num)]
    simp only [ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    exact ENNReal.div_le_div_left (by norm_num) 1
  · refine exists_proposer_two_fifths_lt_twoBlock 1 150 ?_ le_rfl m (by omega)
    rw [NNReal.coe_one, mul_one]
    exact Nat.ceil_natCast 150

/-- **The protocol of Figure 1 is not sound under Definition 6.1 for a machine with oracle
queries of length at most two.** With the constants of [BrownCohenIrvingPiliouras2024, Figure 1]
for `K = 2` (`Params.figure1 2`) and `m ≥ 1201`, the two-block machine of `2 m + 3` steps is
`2`-Lipschitz at its oracle and outputs `true` with probability `1 / 4`, yet some proposer makes
the verifier accept with probability above `2 / 5` against every challenger. The existence
claim of [BrownCohenIrvingPiliouras2024, Theorem 6.2] is not refuted: another protocol may meet
it.

This covers the printed Definition 6.1, which has a strict inequality. By
`lipschitzAt_run_twoBlockMachine` the output law of this machine moves by at most the distance
between the oracles, which is strictly less than twice that distance whenever the distance is
positive. So the machine satisfies the strict inequality with `K = 2` against every oracle at
positive distance.

The checked conclusion is about `Debate.run`, with `2 m + 3` rounds: claims and coins lie on a
grid and the interpreter computes the bit of each round. In Figure 1 the proposer can announce
the same grid probabilities, supply a uniform share and set the bit as prescribed, with the same
probabilities and the same argument for an abort. The constants are read as in
`not_sound_figure1_of_lipschitzAt_run_twoBlockMachine`. -/
theorem not_sound_figure1_two_of_lipschitzAt_run_twoBlockMachine (m : ℕ) (hm : 1201 ≤ m) :
    LipschitzAt 2 (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))
        ((twoBlockMachine m).run (2 * m + 3)) ∧
      OracleComp.evalWith (sumHandler ProbComp.unifOracle
        (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num)))
        ((twoBlockMachine m).run (2 * m + 3)) true ≤ 1 / 3 ∧
      ∃ A : Proposer (Params.figure1 2 (2 * m + 3)).grid,
        ∀ B : Challenger (Params.figure1 2 (2 * m + 3)).grid,
          2 / 5 < OracleComp.evalWith
            (sumHandler ProbComp.unifOracle ((twoBlockMachine m).stepLaw
              (twoBlockOracle (PMF.pure false) (1 / 4) (by norm_num) (by norm_num))))
            (run (Params.figure1 2 (2 * m + 3)) A B) true := by
  refine ⟨(lipschitzAt_run_twoBlockMachine m _ _ _ _).mono (by norm_num),
    (not_sound_figure1_of_lipschitzAt_run_twoBlockMachine m (by omega)).2.1, ?_⟩
  refine exists_proposer_two_fifths_lt_twoBlock 2 300 ?_ (by norm_num) m (by omega)
  rw [NNReal.coe_ofNat, show (150 : ℝ) * 2 = ((300 : ℕ) : ℝ) by norm_num]
  exact Nat.ceil_natCast 300

end Cslib.Interactive.Debate
