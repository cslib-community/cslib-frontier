/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MAC.CarterWegman.Nonce
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Languages.Probabilistic.UntilBad.ChooseTwo
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformBound
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Probability.Uniform
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PMFSwap
import CslibFrontier.Tactic.SuppCases

/-!
# Randomized-nonce Carter–Wegman message authentication codes

This module formalizes Boneh–Shoup Section 7.4 ([BonehShoup2023], pp. 267–270) and the
information-theoretic and statistical-DUF computational steps toward Theorem 7.9 (p. 270).

When the signer samples a fresh uniform nonce `x_i ← PMF.uniformOfFintype N` on each signing query,
a birthday union bound combines with the distinct-nonce reduction of `CarterWegman.Nonce` to bound
any `Q`-query adaptive `RandomNonceForger` by `Q ^ 2 / (2 * |N|) + 1 / |Y| + ε` under a truly random
pad function. Replacing that pad function with a uniform `PseudorandomFunction` via
`prfRandomNonceToPrfDistinguisher` yields quantitative SUF-CMA bounds for `carterWegmanRandomMAC`
and asymptotic `SUFCMA`, `EUFCMA`, and `OneTimeEUFCMA` steps under a statistical DUF
(`Negligible ε`, [BonehShoup2023], Definition 7.5, p. 269). Theorem 7.9 assumes only a
computational DUF (Attack Game 7.3, p. 268); that step is open (#5293). Concrete hash
instantiations (including `linearHashRandomMAC`, realizing Theorem 7.9 for Boolean-matrix linear
hashing) live in `CslibFrontier.Crypto.Protocols.MAC.CarterWegman.Instantiations`.

## Main definitions

* `Cslib.Crypto.Protocols.CarterWegman.RandomNonceForger`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceFnHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceSimHandler`,
  `Cslib.Crypto.Protocols.CarterWegman.checkRandomNonceSUF`,
  `Cslib.Crypto.Protocols.CarterWegman.checkRandomNonceEUF`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedRandomNonceStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.maskedRandomNonceGame`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceStrongGame`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceGame`: randomized Carter–Wegman handlers,
  verification predicates, and experiments (Boneh–Shoup Section 7.4, Theorem 7.9).
* `Cslib.Crypto.Protocols.CarterWegman.carterWegmanRandomMAC`,
  `Cslib.Crypto.Protocols.CarterWegman.prfRandomNonceToPrfDistinguisher`: word-level `MACScheme`
  packaging and `OracleDistinguisher` PRF reduction.

## Main results

* `Cslib.Crypto.Protocols.CarterWegman.uniform_bind_run_interpret_randomNonceFnHandler`,
`Cslib.Crypto.Protocols.CarterWegman.probOracleComp_uniform_bind_run_interpret_randomNonceFnHandler`
  (`ProbOracleComp` lift),
  `Cslib.Crypto.Protocols.CarterWegman.probOracleComp_randomNonceSimHandler_not_nodup_le`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceSimHandler_not_nodup_le`,
  `Cslib.Crypto.Protocols.CarterWegman.seed_uniform_probOracleComp_checkRandomNonceSUF_le`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceStrongGame_le_sum_add_max`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceStrongGame_le`,
  `Cslib.Crypto.Protocols.CarterWegman.randomNonceGame_le`: birthday collision and ideal
  random-function bounds (after Boneh–Shoup Section 7.4, Theorem 7.9, p. 270).
* `Cslib.Crypto.Protocols.CarterWegman.isOraclePPT_prfRandomNonceToPrfDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfRealGame_prfRandomNonceToPrfDistinguisher`,
  `Cslib.Crypto.Protocols.CarterWegman.eval_prfIdealGame_prfRandomNonceToPrfDistinguisher_le`,
  `Cslib.Crypto.Protocols.CarterWegman.sufCmaGame_carterWegmanRandomMAC_toReal_le`: `IsOraclePPT`
  admissibility and quantitative SUF-CMA reduction bounds for `carterWegmanRandomMAC`.
* `Cslib.Crypto.PseudorandomFunction.sufCma_carterWegmanRandomMAC_of_statisticalDUF`,
  `Cslib.Crypto.PseudorandomFunction.eufCma_carterWegmanRandomMAC_of_statisticalDUF`,
  `Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_carterWegmanRandomMAC_of_statisticalDUF`:
  statistical-DUF steps toward Boneh–Shoup Theorem 7.9 (p. 270); the computational-DUF theorem is
  open (#5293).

## References

* [M. N. Wegman, J. L. Carter, *New Hash Functions and Their Use in Authentication and Set
  Equality*][WegmanCarter1981]
* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 7.4.
-/

public section

namespace Cslib.Crypto.Protocols.CarterWegman

open Cslib.Probability Cslib.Probability.PMF Turing.MultiTapeTM
open scoped NNReal ENNReal

@[local fun_prop]
private theorem computableInPolyTime_encPair_coe {γ : Type} {encIn : γ ↪ List Bool}
    {u v : γ → List Bool}
    (hu : ComputableInPolyTime u encIn encBits)
    (hv : ComputableInPolyTime v encIn encBits) :
    ComputableInPolyTime (fun a => (encPair encBits encBits) (u a, v a)) encIn encBits :=
  ComputableInPolyTime.encoding_comp (hu.prod hv)

/-! ### Randomized Carter–Wegman MAC (Boneh–Shoup Section 7.4, Theorem 7.9) -/

section Randomized

variable {K M N Y : Type} [AddGroup Y]

/-- An adaptive multi-query forger against the randomized Carter–Wegman MAC ([BonehShoup2023],
Section 7.4, Theorem 7.9, p. 270): it draws private coins `s ← coins`, makes adaptive signing
queries `m : M` (receiving `(x, t) : N × Y` where `x` is a random nonce chosen by the signer), and
outputs a candidate forgery `((m', x'), t') : (M × N) × Y`. -/
structure RandomNonceForger (M N Y : Type) where
  /-- Type of the forger's private coins. -/
  Coins : Type
  /-- Distribution of the forger's private coins. -/
  coins : PMF Coins
  /-- Adaptive oracle program making signing queries `m : M` and outputting a candidate forgery
  `((m', x'), t') : (M × N) × Y`. -/
  forge : Coins → OracleComp (fun _ : M => N × Y) ((M × N) × Y)

/-- Randomized Carter–Wegman signing handler driven by a pad function `padFn : N → Y`
([BonehShoup2023], Section 7.4, p. 267): on signing query `m`, sample a uniform nonce
`x ← PMF.uniformOfFintype N`, compute `t = sign hash k (padFn x) m`, append `((m, x), t)` to the
transcript `tr`, and return `(x, t)`. -/
noncomputable def randomNonceFnHandler [Fintype N] [Nonempty N]
    (hash : K → M → Y) (k : K) (padFn : N → Y) (m : M) :
    StateT (List ((M × N) × Y)) PMF (N × Y) := fun tr => do
  let x ← PMF.uniformOfFintype N
  let t := sign hash k (padFn x) m
  return ((x, t), tr ++ [((m, x), t)])

/-- Simulated key-independent randomized signing handler: on query `m`, sample independent uniform
`(x, t) ← PMF.uniformOfFintype N × PMF.uniformOfFintype Y`, append `((m, x), t)` to `tr`, and
return `(x, t)`. -/
noncomputable def randomNonceSimHandler [Fintype N] [Nonempty N] [Fintype Y] [Nonempty Y]
    (m : M) : StateT (List ((M × N) × Y)) PMF (N × Y) := fun tr => do
  let x ← PMF.uniformOfFintype N
  let t ← PMF.uniformOfFintype Y
  return ((x, t), tr ++ [((m, x), t)])

/-- **Multi-query simulation equivalence for `randomNonceFnHandler` on `ProbOracleComp` programs
under a random function**: for any post-processing `post` that collapses to a constant distribution
`c` whenever the transcript has a repeated nonce (`¬ (tr'.map (fun ((_, x), _) => x)).Nodup`),
running `prog` (with private coin flips) against
`randomNonceFnHandler hash k (reconstructPadFn hash k tr table)` over
`table ← PMF.uniformOfFintype (N → Y)` has the exact same distribution as running `prog` against
`randomNonceSimHandler` and reconstructing `reconstructPadFn hash k res.2 table` at the end. -/
theorem probOracleComp_uniform_bind_run_interpret_randomNonceFnHandler {α β : Type}
    [Fintype N] [Nonempty N] [DecidableEq N] [Fintype Y] [Nonempty Y]
    (hash : K → M → Y) (k : K)
    (prog : ProbOracleComp (fun _ : M => N × Y) α) (tr : List ((M × N) × Y))
    (post : α → List ((M × N) × Y) → (N → Y) → PMF β) (c : PMF β)
    (hpost : ∀ a tr' padFn, ¬ (tr'.map (fun ((_, x), _) => x)).Nodup → post a tr' padFn = c) :
    ((PMF.uniformOfFintype (N → Y)).bind fun table =>
      (ProbOracleComp.runWith (randomNonceFnHandler hash k (reconstructPadFn hash k tr table))
          prog tr).bind
        fun res => post res.1 res.2 (reconstructPadFn hash k tr table)) =
    ((ProbOracleComp.runWith randomNonceSimHandler prog tr).bind fun res =>
      (PMF.uniformOfFintype (N → Y)).bind fun table =>
        post res.1 res.2 (reconstructPadFn hash k res.2 table)) := by
  let step (m : M) : ProbOracleComp (fun _ : M × N => Y) (N × Y) := do
    let x ← ProbOracleComp.sample (ProbComp.uniform N)
    let t ← ProbOracleComp.query (m, x)
    return (x, t)
  have hfn (padFn : N → Y) :
      (fun m => ProbOracleComp.runWith (nonceFnHandler hash k padFn) (step m)) =
        randomNonceFnHandler hash k padFn :=
    funext₂ fun m state => by
      simp [step, ProbComp.eval_uniform, nonceFnHandler, randomNonceFnHandler, pmf_norm]
  have hsim : (fun m => ProbOracleComp.runWith nonceSimHandler (step m)) =
      randomNonceSimHandler :=
    funext₂ fun m state => by
      simp [step, ProbComp.eval_uniform, nonceSimHandler, randomNonceSimHandler, pmf_norm]
  simpa only [ProbOracleComp.runWith_interpret_sumHandler, hfn, hsim] using
    probOracleComp_uniform_bind_run_interpret_nonceFnHandler hash k
      (OracleComp.interpret
        (OracleComp.sumHandler (fun n => ProbOracleComp.sample (ProbComp.unifFin n)) step)
        prog)
      tr post c hpost

/-- **Multi-query simulation equivalence for `randomNonceFnHandler` under a random function**:
specialization of `probOracleComp_uniform_bind_run_interpret_randomNonceFnHandler` to deterministic
`OracleComp` programs. -/
theorem uniform_bind_run_interpret_randomNonceFnHandler {α β : Type}
    [Fintype N] [Nonempty N] [DecidableEq N] [Fintype Y] [Nonempty Y]
    (hash : K → M → Y) (k : K)
    (prog : OracleComp (fun _ : M => N × Y) α) (tr : List ((M × N) × Y))
    (post : α → List ((M × N) × Y) → (N → Y) → PMF β) (c : PMF β)
    (hpost : ∀ a tr' padFn, ¬ (tr'.map (fun ((_, x), _) => x)).Nodup → post a tr' padFn = c) :
    ((PMF.uniformOfFintype (N → Y)).bind fun table =>
      ((OracleComp.interpret
        (randomNonceFnHandler hash k (reconstructPadFn hash k tr table)) prog).run tr).bind
        fun res => post res.1 res.2 (reconstructPadFn hash k tr table)) =
    (((OracleComp.interpret randomNonceSimHandler prog).run tr).bind fun res =>
      (PMF.uniformOfFintype (N → Y)).bind fun table =>
        post res.1 res.2 (reconstructPadFn hash k res.2 table)) := by
  simpa only [ProbOracleComp.runWith_liftRight, OracleComp.runWith_eq_run_interpret] using
    probOracleComp_uniform_bind_run_interpret_randomNonceFnHandler hash k
      (OracleComp.liftRight prog) tr post c hpost

omit [AddGroup Y] in
/-- Birthday-collision bound for `randomNonceSimHandler` on `ProbOracleComp` programs: starting
from `tr`, any `Q`-query-bounded `ProbOracleComp` program produces a transcript with a repeated
nonce with probability at most
`((∑ i ∈ Finset.range Q, (tr.length + i) : ℕ) : ℝ≥0∞) / Fintype.card N` when
`(tr.map (fun ((_, x), _) => x)).Nodup`, and at most `1` otherwise. -/
theorem probOracleComp_randomNonceSimHandler_not_nodup_le {α : Type}
    [Fintype N] [Nonempty N] [DecidableEq N] [Fintype Y] [Nonempty Y]
    {prog : ProbOracleComp (fun _ : M => N × Y) α} {Q : ℕ}
    (hprog : prog.IsQueryBounded Q) (tr : List ((M × N) × Y)) :
    ((ProbOracleComp.runWith randomNonceSimHandler prog tr).bind fun res =>
      PMF.pure (!decide (res.2.map (fun ((_, x), _) => x)).Nodup)) true ≤
      if (tr.map (fun ((_, x), _) => x)).Nodup then
        ((∑ i ∈ Finset.range Q, (tr.length + i) : ℕ) : ℝ≥0∞) / Fintype.card N
      else 1 := by
  have hnd (l : List ((M × N) × Y)) :
      l.map (fun ((_, x), _) => x) = l.map (fun e => e.1.2) := rfl
  simp only [hnd]
  by_cases hnodup : (tr.map (fun e => e.1.2)).Nodup
  · simp only [hnodup, ↓reduceIte, ← _root_.decide_not, bind_pure_decide_apply_true,
      ProbOracleComp.runWith_eq_run_interpret]
    refine (OracleComp.toOuterMeasure_bad_choose_two_of_isCostBounded
      (bad := fun s : List ((M × N) × Y) => ¬ (s.map (fun e => e.1.2)).Nodup)
      (Sum.elim (fun _ => 0) (fun _ => 1)) List.length (Fintype.card N : ℝ≥0∞)⁻¹
      ?_ ?_ hprog (not_not.mpr hnodup)).trans_eq ?_
    · intro q s hs
      have hs' : (s.map (fun e => e.1.2)).Nodup := not_not.mp hs
      rw [← bind_pure_decide_apply_true]
      cases q with
      | inl num =>
        simp [OracleComp.sumHandler, StateT.lift, hs']
      | inr m =>
        have hbad (x : N) (t : Y) :
            ¬ ((s ++ [((m, x), t)]).map (fun e => e.1.2)).Nodup ↔
              x ∈ s.map (fun e => e.1.2) := by
          simp [List.nodup_append, hs']
        have hc12 : Nat.choose 1 2 = 0 := rfl
        simp only [pmf_norm, OracleComp.sumHandler, randomNonceSimHandler, hbad,
          PMF.bind_const, Sum.elim_inr, one_mul, hc12, add_zero]
        simpa only [bind_pure_decide_apply_true, List.length_map, one_div] using
          Probability.PMF.toOuterMeasure_uniformOfFintype_mem_list_le (s.map (fun e => e.1.2))
    · rintro (num | m) s _ x hmem _
      · supp_cases hmem [OracleComp.sumHandler, StateT.lift] with ⟨_, -, rfl⟩
        simp
      · supp_cases hmem [OracleComp.sumHandler, randomNonceSimHandler] with ⟨_, _, rfl⟩
        simp
    · rw [← div_eq_mul_inv]
      congr 1
      norm_cast
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
        Finset.sum_range_id, Nat.choose_two_right]
  · simpa only [hnodup, ↓reduceIte] using PMF.coe_le_one _ _

omit [AddGroup Y] in
/-- Birthday-collision bound for `randomNonceSimHandler`: specialization of
`probOracleComp_randomNonceSimHandler_not_nodup_le` to deterministic `OracleComp` programs. -/
theorem randomNonceSimHandler_not_nodup_le {α : Type} [Fintype N] [Nonempty N] [DecidableEq N]
    [Fintype Y] [Nonempty Y]
    {prog : OracleComp (fun _ : M => N × Y) α} {Q : ℕ}
    (hprog : prog.IsQueryBounded Q) (tr : List ((M × N) × Y)) :
    (((OracleComp.interpret randomNonceSimHandler prog).run tr).bind fun res =>
      PMF.pure (!decide (res.2.map (fun ((_, x), _) => x)).Nodup)) true ≤
      if (tr.map (fun ((_, x), _) => x)).Nodup then
        ((∑ i ∈ Finset.range Q, (tr.length + i) : ℕ) : ℝ≥0∞) / Fintype.card N
      else 1 := by
  simpa only [ProbOracleComp.runWith_liftRight, OracleComp.runWith_eq_run_interpret] using
    probOracleComp_randomNonceSimHandler_not_nodup_le
      (OracleComp.IsCostBounded.liftRight hprog fun _ => le_rfl) tr

variable [DecidableEq M] [DecidableEq N] [DecidableEq Y]

/-- Randomized Carter–Wegman SUF-CMA verification predicate ([BonehShoup2023], Section 7.4,
Theorem 7.9, p. 270): the candidate `out = ((m', x'), t')` was not returned by any signing query
(`!tr.contains out`) and `verify hash k (padFn x') m' t' = true`. -/
@[expose]
def checkRandomNonceSUF (hash : K → M → Y) (k : K) (padFn : N → Y) (tr : List ((M × N) × Y))
    (out : (M × N) × Y) : Bool :=
  let cand := out.1
  let m' := cand.1
  let x' := cand.2
  let t' := out.2
  !tr.contains out && verify hash k (padFn x') m' t'

/-- Randomized Carter–Wegman EUF-CMA (message-freshness) verification predicate: the message
`m'` was never queried (`!(tr.map (fun ((m, _), _) => m)).contains m'`) and
`verify hash k (padFn x') m' t' = true`. -/
def checkRandomNonceEUF (hash : K → M → Y) (k : K) (padFn : N → Y) (tr : List ((M × N) × Y))
    (out : (M × N) × Y) : Bool :=
  let cand := out.1
  let m' := cand.1
  let x' := cand.2
  let t' := out.2
  !(tr.map (fun ((m, _), _) => m)).contains m' && verify hash k (padFn x') m' t'

private def checkRandomNonceOrCollision (hash : K → M → Y) (k : K) (padFn : N → Y)
    (tr : List ((M × N) × Y)) (out : (M × N) × Y) : Bool :=
  !decide (tr.map (fun e => e.1.2)).Nodup || checkNonceSUF hash k padFn tr out

/-- Randomized Carter–Wegman EUF-CMA implies SUF-CMA (`checkRandomNonceSUF`), since a fresh message
`m'` cannot appear in any issued transcript triple `((mᵢ, xᵢ), tᵢ) ∈ tr`. -/
theorem checkRandomNonceEUF_imp_checkRandomNonceSUF (hash : K → M → Y) (k : K) (padFn : N → Y)
    (tr : List ((M × N) × Y)) (out : (M × N) × Y) :
    checkRandomNonceEUF hash k padFn tr out = true →
      checkRandomNonceSUF hash k padFn tr out = true := by
  simp only [checkRandomNonceEUF, checkRandomNonceSUF, Bool.and_eq_true, Bool.not_eq_true',
    List.contains_eq_mem, decide_eq_false_iff_not, List.mem_map]
  rintro ⟨hnotm, hv⟩
  exact ⟨fun hout => hnotm ⟨out, hout, rfl⟩, hv⟩

private theorem checkRandomNonceSUF_imp_checkRandomNonceOrCollision (hash : K → M → Y) (k : K)
    (padFn : N → Y) (tr : List ((M × N) × Y)) (out : (M × N) × Y) :
    checkRandomNonceSUF hash k padFn tr out = true →
      checkRandomNonceOrCollision hash k padFn tr out = true := by
  unfold checkRandomNonceSUF checkRandomNonceOrCollision checkNonceSUF
  cases decide (tr.map (fun e => e.1.2)).Nodup <;> simp

variable [Fintype N] [Nonempty N]

/-- The randomized Carter–Wegman SUF-CMA experiment under an arbitrary pad-function distribution
`rfDist : PMF (N → Y)`. -/
noncomputable def maskedRandomNonceStrongGame (seed : PMF K) (rfDist : PMF (N → Y))
    (hash : K → M → Y) (forger : RandomNonceForger M N Y) : PMF Bool := do
  let k ← seed
  let rf ← rfDist
  let s ← forger.coins
  let res ← (OracleComp.interpret (randomNonceFnHandler hash k rf) (forger.forge s)).run []
  return checkRandomNonceSUF hash k rf res.2 res.1

/-- The randomized Carter–Wegman EUF-CMA (message-freshness) experiment under an arbitrary
pad-function distribution `rfDist : PMF (N → Y)`. -/
noncomputable def maskedRandomNonceGame (seed : PMF K) (rfDist : PMF (N → Y))
    (hash : K → M → Y) (forger : RandomNonceForger M N Y) : PMF Bool := do
  let k ← seed
  let rf ← rfDist
  let s ← forger.coins
  let res ← (OracleComp.interpret (randomNonceFnHandler hash k rf) (forger.forge s)).run []
  return checkRandomNonceEUF hash k rf res.2 res.1

/-- In `maskedRandomNonceGame`, message-freshness forgery probability is bounded by strong
unforgeability (`maskedRandomNonceStrongGame`). -/
theorem maskedRandomNonceGame_le_maskedRandomNonceStrongGame (seed : PMF K) (rfDist : PMF (N → Y))
    (hash : K → M → Y) (forger : RandomNonceForger M N Y) :
    maskedRandomNonceGame seed rfDist hash forger true ≤
      maskedRandomNonceStrongGame seed rfDist hash forger true :=
  bind_apply_mono_on_support seed true fun k _ =>
    bind_apply_mono_on_support rfDist true fun rf _ =>
      bind_apply_mono_on_support forger.coins true fun s _ =>
        map_true_mono
          ((OracleComp.interpret (randomNonceFnHandler hash k rf) (forger.forge s)).run [])
          fun res _ => checkRandomNonceEUF_imp_checkRandomNonceSUF hash k rf res.2 res.1

variable [Fintype Y] [Nonempty Y]

/-- The ideal randomized Carter–Wegman SUF-CMA experiment ([BonehShoup2023], Section 7.4,
Theorem 7.9, p. 270) under a truly random function `rf ← PMF.uniformOfFintype (N → Y)`. -/
noncomputable def randomNonceStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : RandomNonceForger M N Y) : PMF Bool :=
  maskedRandomNonceStrongGame seed (PMF.uniformOfFintype (N → Y)) hash forger

/-- The ideal randomized Carter–Wegman EUF-CMA (message-freshness) experiment under a truly random
function `rf ← PMF.uniformOfFintype (N → Y)`. -/
noncomputable def randomNonceGame (seed : PMF K) (hash : K → M → Y)
    (forger : RandomNonceForger M N Y) : PMF Bool :=
  maskedRandomNonceGame seed (PMF.uniformOfFintype (N → Y)) hash forger

/-- In `randomNonceGame`, message-freshness forgery probability is bounded by strong
unforgeability (`randomNonceStrongGame`). -/
theorem randomNonceGame_le_randomNonceStrongGame (seed : PMF K) (hash : K → M → Y)
    (forger : RandomNonceForger M N Y) :
    randomNonceGame seed hash forger true ≤ randomNonceStrongGame seed hash forger true :=
  maskedRandomNonceGame_le_maskedRandomNonceStrongGame seed (PMF.uniformOfFintype (N → Y))
    hash forger

private theorem seed_uniform_probOracleComp_checkRandomNonceSUF_le_sum_add_max {α : Type}
    {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε)
    {prog : ProbOracleComp (fun _ : M => N × Y) α} {Q : ℕ}
    (hprog : prog.IsQueryBounded Q) (out : α → (M × N) × Y) :
    (seed.bind fun k =>
      (PMF.uniformOfFintype (N → Y)).bind fun rf =>
        (ProbOracleComp.runWith (randomNonceFnHandler hash k rf) prog []).bind
          fun res => PMF.pure (checkRandomNonceSUF hash k rf res.2 (out res.1))) true ≤
      ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / Fintype.card N +
        max ε (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  refine (bind_apply_mono_on_support seed true fun k _ =>
    bind_apply_mono_on_support (PMF.uniformOfFintype (N → Y)) true fun rf _ =>
      map_true_mono (ProbOracleComp.runWith (randomNonceFnHandler hash k rf) prog []) fun res _ =>
        checkRandomNonceSUF_imp_checkRandomNonceOrCollision hash k rf res.2 (out res.1)).trans ?_
  have hsim (k : K) :
      ((PMF.uniformOfFintype (N → Y)).bind fun rf =>
        (ProbOracleComp.runWith (randomNonceFnHandler hash k rf) prog []).bind
          fun res => PMF.pure (checkRandomNonceOrCollision hash k rf res.2 (out res.1))) =
      ((ProbOracleComp.runWith randomNonceSimHandler prog []).bind fun res =>
        (PMF.uniformOfFintype (N → Y)).bind fun table =>
          PMF.pure
            (checkRandomNonceOrCollision hash k
              (reconstructPadFn hash k res.2 table) res.2 (out res.1))) := by
    simpa only [reconstructPadFn_nil] using
      probOracleComp_uniform_bind_run_interpret_randomNonceFnHandler hash k prog []
        (fun a tr' padFn => PMF.pure (checkRandomNonceOrCollision hash k padFn tr' (out a)))
        (PMF.pure true)
        (fun a tr' padFn hnot => by simp [checkRandomNonceOrCollision, hnot])
  simp only [PMF.map, Function.comp_def, hsim]
  let simPMF := ProbOracleComp.runWith randomNonceSimHandler prog []
  pmf_hoist simPMF
  have hpoint (res : α × List ((M × N) × Y)) :
      (seed.bind fun k =>
        (PMF.uniformOfFintype (N → Y)).bind fun table =>
          PMF.pure
            (checkRandomNonceOrCollision hash k
              (reconstructPadFn hash k res.2 table) res.2 (out res.1))) true ≤
      (PMF.pure (!decide (res.2.map (fun e => e.1.2)).Nodup)) true +
        max ε (Fintype.card Y : ℝ≥0∞)⁻¹ := by
    by_cases hnodup : (res.2.map (fun e => e.1.2)).Nodup
    · simp only [checkRandomNonceOrCollision, decide_eq_true hnodup, Bool.not_true, Bool.false_or,
        PMF.pure_apply, Bool.true_eq_false, ↓reduceIte, zero_add]
      exact seed_uniform_checkNonceSUF_le hh res.2 (out res.1)
    · simpa only [decide_eq_false hnodup, Bool.not_false, PMF.pure_apply, ↓reduceIte] using
        (PMF.coe_le_one _ _).trans le_self_add
  refine (bind_apply_le_add_const_on_support simPMF true fun res _ => hpoint res).trans
    (add_le_add ?_ le_rfl)
  simpa only [List.map_nil, List.nodup_nil, ↓reduceIte, List.length_nil, zero_add] using
    probOracleComp_randomNonceSimHandler_not_nodup_le hprog []

private theorem sum_range_div_add_max_le (Q cN cY : ℕ) (ε : ℝ≥0∞) :
    ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / cN + max ε (cY : ℝ≥0∞)⁻¹ ≤
      (Q : ℝ≥0∞) ^ 2 / (2 * cN) + (cY : ℝ≥0∞)⁻¹ + ε := by
  have hsum_nat : 2 * (∑ i ∈ Finset.range Q, i) ≤ Q ^ 2 := by
    rw [Finset.sum_range_id, sq]
    exact (Nat.mul_div_le (Q * (Q - 1)) 2).trans (Nat.mul_le_mul_left Q (Nat.sub_le Q 1))
  have hsum : ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / cN ≤ (Q : ℝ≥0∞) ^ 2 / (2 * cN) := by
    rw [← ENNReal.mul_div_mul_left _ _ (by norm_num : (2 : ℝ≥0∞) ≠ 0) ENNReal.ofNat_ne_top]
    gcongr
    exact_mod_cast hsum_nat
  rw [add_assoc]
  exact add_le_add hsum ((max_le_add_of_nonneg zero_le zero_le).trans_eq (add_comm _ _))

/-- **Ideal randomized Carter–Wegman SUF-CMA security (`∑ i < Q` + `max` bound)**, a step of the
proof of [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), with a truly random function in place
of the PRF: under `IsDeltaUniversalHash seed hash ε`, any `Q`-query-bounded `RandomNonceForger`
wins `randomNonceStrongGame` with probability at most
`((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / Fintype.card N + max ε (Fintype.card Y : ℝ≥0∞)⁻¹`. -/
theorem randomNonceStrongGame_le_sum_add_max {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) {forger : RandomNonceForger M N Y} {Q : ℕ}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded Q) :
    randomNonceStrongGame seed hash forger true ≤
      ((∑ i ∈ Finset.range Q, i : ℕ) : ℝ≥0∞) / Fintype.card N +
        max ε (Fintype.card Y : ℝ≥0∞)⁻¹ := by
  dsimp only [randomNonceStrongGame, maskedRandomNonceStrongGame, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure]
  pmf_hoist forger.coins
  refine bind_apply_le_on_support forger.coins fun s _ => ?_
  simpa only [ProbOracleComp.runWith_liftRight, OracleComp.runWith_eq_run_interpret] using
    seed_uniform_probOracleComp_checkRandomNonceSUF_le_sum_add_max hh
      (OracleComp.IsCostBounded.liftRight (hforger s) fun _ => le_rfl) (fun x => x)

/-- **Ideal randomized Carter–Wegman SUF-CMA security**, a step of the proof of [BonehShoup2023],
Theorem 7.9 (Section 7.4, p. 270), with a truly random function in place of the PRF: under
`IsDeltaUniversalHash seed hash ε`, any `Q`-query-bounded `RandomNonceForger` wins
`randomNonceStrongGame` with probability at most
`(Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + (Fintype.card Y : ℝ≥0∞)⁻¹ + ε`. -/
theorem randomNonceStrongGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) {forger : RandomNonceForger M N Y} {Q : ℕ}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded Q) :
    randomNonceStrongGame seed hash forger true ≤
      (Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + (Fintype.card Y : ℝ≥0∞)⁻¹ + ε :=
  (randomNonceStrongGame_le_sum_add_max hh hforger).trans (sum_range_div_add_max_le _ _ _ _)

/-- **Ideal randomized Carter–Wegman EUF-CMA (message-freshness) security**, after the proof of
[BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), with a truly random function in place of the
PRF. -/
theorem randomNonceGame_le {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε) {forger : RandomNonceForger M N Y} {Q : ℕ}
    (hforger : ∀ s, (forger.forge s).IsQueryBounded Q) :
    randomNonceGame seed hash forger true ≤
      (Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + (Fintype.card Y : ℝ≥0∞)⁻¹ + ε :=
  (randomNonceGame_le_randomNonceStrongGame seed hash forger).trans
    (randomNonceStrongGame_le hh hforger)

/-- **Ideal randomized Carter–Wegman SUF-CMA bound for `ProbOracleComp` programs**:
under `IsDeltaUniversalHash seed hash ε`, any `Q`-query-bounded `ProbOracleComp` program `prog`
against `randomNonceFnHandler` satisfies `checkRandomNonceSUF` on `out res.1` with probability at
most `(Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + (Fintype.card Y : ℝ≥0∞)⁻¹ + ε`. -/
theorem seed_uniform_probOracleComp_checkRandomNonceSUF_le {α : Type}
    {seed : PMF K} {hash : K → M → Y} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash seed hash ε)
    {prog : ProbOracleComp (fun _ : M => N × Y) α} {Q : ℕ}
    (hprog : prog.IsQueryBounded Q) (out : α → (M × N) × Y) :
    (seed.bind fun k =>
      (PMF.uniformOfFintype (N → Y)).bind fun rf =>
        (ProbOracleComp.runWith (randomNonceFnHandler hash k rf) prog []).bind
          fun res => PMF.pure (checkRandomNonceSUF hash k rf res.2 (out res.1))) true ≤
      (Q : ℝ≥0∞) ^ 2 / (2 * Fintype.card N) + (Fintype.card Y : ℝ≥0∞)⁻¹ + ε :=
  (seed_uniform_probOracleComp_checkRandomNonceSUF_le_sum_add_max hh hprog out).trans
    (sum_range_div_add_max_le _ _ _ _)

/-! #### Word-level `MACScheme` packaging and `IsOraclePPT` PRF reduction (Theorem 7.9) -/

/-- **Computational randomized Carter–Wegman MAC (`MACScheme`)**
([BonehShoup2023], Section 7.4, Theorem 7.9, pp. 267–270):
given a polynomial-time message-length schedule `msgLen : ℕ → ℕ`, a strict-PPT hash-key sampler
`seed : ℕ → ProbComp (List Bool)`, a polynomial-time hash evaluator
`hash : ℕ → List Bool → List Bool → List Bool`, and a polynomial-time PRF family
`family : List Bool → List Bool → List Bool`:
* `keyGen n` samples `k ← seed n` and `prfKey ← BitString.sampleList n`, returning the framed pair
  `encPair encBits encBits (k, prfKey)`.
* `sign sk msg` recovers `k := unframe sk`, `prfKey := dropFrame sk`, and `n := prfKey.length`,
  samples a fresh uniform `n`-bit nonce `nonce ← BitString.sampleList n`, and when
  `msg.length == msgLen n` returns the framed pair `encPair encBits encBits (nonce, tag)` where
  `tag = BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n]` (and `[]`
  otherwise).
* `verify sk msg fullTag` decodes `nonce := unframe fullTag`, computes the expected `n`-bit tag
  `tag := BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n]`, and checks
  `msg.length == msgLen n`, `nonce.length == n`, and
  `encPair encBits encBits (nonce, tag) == fullTag`. -/
noncomputable def carterWegmanRandomMAC (msgLen : ℕ → ℕ)
    (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool)
    (family : List Bool → List Bool → List Bool)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits) : MACScheme where
  msgLen := msgLen
  msgLen_polyTime := hmsgLen
  keyGen := carterWegmanKeyGen seed
  sign sk msg := do
    let nonce ← BitString.sampleList (dropFrame sk).length
    let k := unframe sk
    let prfKey := dropFrame sk
    let n := prfKey.length
    return if msg.length == msgLen n then
      encPair encBits encBits
        (nonce, BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n])
    else
      []
  verify sk msg fullTag :=
    let k := unframe sk
    let prfKey := dropFrame sk
    let n := prfKey.length
    let nonce := unframe fullTag
    let tag := BitString.listXor n [hash n k msg, (prfOracle family n prfKey nonce).take n]
    (msg.length == msgLen n) && (nonce.length == n) &&
      (encPair encBits encBits (nonce, tag) == fullTag)
  keyGen_ppt := isPPTOn_carterWegmanKeyGen hseed
  sign_ppt := by
    have hh : ComputableInPolyTime
        (fun p : (List Bool × List Bool) × List Bool =>
          hash (dropFrame p.1.1).length (unframe p.1.1) p.1.2)
        (encPair (encPair encBits encBits) encBits) encBits :=
      hhash.comp (ComputableInPolyTime.prod (by fun_prop)
        (ComputableInPolyTime.prod (by fun_prop) (by fun_prop)))
    refine (ComputableInPolyTime.sampleList (by fun_prop)).bind_with ?_
    apply ComputableInPolyTime.isPPTOn
    fun_prop
  verify_polyTime := by
    have hh : ComputableInPolyTime
        (fun p : List Bool × List Bool × List Bool =>
          hash (dropFrame p.1).length (unframe p.1) p.2.1)
        (encPair encBits (encPair encBits encBits)) encBits :=
      hhash.comp (ComputableInPolyTime.prod (by fun_prop)
        (ComputableInPolyTime.prod (by fun_prop) (by fun_prop)))
    dsimp only
    fun_prop
  verify_sign := by
    intro n sk hsk msg hmsg fullTag htag
    simp only [carterWegmanKeyGen, ProbComp.eval_bind, ProbComp.eval_pure,
      BitString.eval_sampleList, PMF.mem_support_bind_iff, PMF.mem_support_pure_iff] at hsk htag
    rcases hsk with ⟨k, -, prfKey, hprfKey, rfl⟩
    have hprfLen : prfKey.length = n := BitString.length_of_mem_support_uniformList hprfKey
    rcases htag with ⟨nonce, hnonce, rfl⟩
    simp only [encPair_apply, encBits_apply, dropFrame_frame_append, unframe_frame_append,
      hprfLen, hmsg, beq_self_eq_true, ↓reduceIte] at hnonce ⊢
    have hnonceLen : nonce.length = n := BitString.length_of_mem_support_uniformList hnonce
    simp [hnonceLen]

private noncomputable def cwRandomNonceLogHandler (msgLen : ℕ → ℕ)
    (hash : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (k : List Bool) (request : Unit × List Bool) :
    StateT (List (List Bool × List Bool)) (WordOracleComp Unit) (List Bool) :=
  fun queriedPairs =>
    let msg := request.2
    if msg.length == msgLen n then do
      let nonce ← ProbOracleComp.sample (BitString.sampleList n)
      (fun pad =>
        let tag := BitString.listXor n [hash n k msg, pad]
        let fullTag := encPair encBits encBits (nonce, tag)
        (fullTag, (msg, fullTag) :: queriedPairs)) <$>
        (List.take n <$> ProbOracleComp.query ((), nonce))
    else
      pure ([], queriedPairs)

/-- Oracle reduction turning an adaptive word-level `Forger` into an `OracleDistinguisher`
for the PRF security game ([BonehShoup2023], Section 7.4, Theorem 7.9, p. 270) via
`prfLogDistinguisher`. -/
noncomputable def prfRandomNonceToPrfDistinguisher (msgLen : ℕ → ℕ)
    (seed : ℕ → ProbComp (List Bool))
    (hash : ℕ → List Bool → List Bool → List Bool) (adversary : Forger) :
    OracleDistinguisher :=
  prfLogDistinguisher seed (cwRandomNonceLogHandler msgLen hash) adversary
    (fun ((_, fullTag), _) => unframe fullTag)
    (fun n k ((msg, fullTag), tr) pad =>
      let nonce := unframe fullTag
      let tag := BitString.listXor n [hash n k msg, pad]
      (msg.length == msgLen n) && (nonce.length == n) && !tr.contains (msg, fullTag) &&
        (encPair encBits encBits (nonce, tag) == fullTag))

/-- `prfRandomNonceToPrfDistinguisher` is uniformly strict oracle-PPT (`IsOraclePPT encBool`)
whenever `msgLen`, `seed`, `hash`, and `adversary` are uniformly polynomial-time / strict PPT. -/
theorem isOraclePPT_prfRandomNonceToPrfDistinguisher
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool} {adversary : Forger}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hadversary : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT encBool (prfRandomNonceToPrfDistinguisher msgLen seed hash adversary) := by
  have hhash' : ComputableInPolyTime
      (fun p : ℕ × List Bool × List Bool => hash p.1 p.2.1 p.2.2)
      (encKeyedInput encBits) encBits := hhash
  have hhandler : IsOraclePPTOn
      (encHandlerCall encLogCaller (encFinite Unit) (encList (encPair encBits encBits)))
      (encPair encBits (encList (encPair encBits encBits)))
      (fun ⟨((n, _), k), request, log⟩ => cwRandomNonceLogHandler msgLen hash n k request log) := by
    unfold cwRandomNonceLogHandler
    exact IsOraclePPTOn.cond (by fun_prop)
      (((ComputableInPolyTime.sampleList (by fun_prop)).isOraclePPTOn
          (Operation := Unit)).bind_with
        ((IsOraclePPTOn.query_take () (by fun_prop) (by fun_prop)).map_with (by fun_prop)))
      ((ComputableInPolyTime.isOraclePPTOn (Operation := Unit)) (by fun_prop))
  unfold prfRandomNonceToPrfDistinguisher
  refine isOraclePPT_prfLogDistinguisher hseed hadversary hhandler
    (fun caller query => 6 * caller.1.1 + 4 * query.length + 10) (by fun_prop) ?_
    (by dsimp only; fun_prop)
    (by dsimp only; simp only [List.contains_eq_mem]; fun_prop)
  intro np k request queriedPairs result hresult
  dsimp only [cwRandomNonceLogHandler] at hresult
  by_cases hcond : (request.2.length == msgLen np.1) = true
  · simp only [hcond, ↓reduceIte, OracleComp.mem_supportWith_bind_iff,
      OracleComp.mem_supportWith_map_iff] at hresult
    rcases hresult with ⟨nonce, hnonce, pad, -, rfl⟩
    have hnonceLen : nonce.length = np.1 :=
      BitString.length_of_mem_support_uniformList
        (by simpa [ProbOracleComp.support_sample, BitString.eval_sampleList] using hnonce)
    exact ⟨by dsimp only; enc_len [hnonceLen, BitString.length_listXor],
      by dsimp only; enc_len [hnonceLen, BitString.length_listXor]⟩
  · obtain rfl : result = ([], queriedPairs) := by simpa [Bool.eq_false_iff.mpr hcond] using hresult
    exact ⟨by simp, by enc_len⟩

/-- **Real-game simulation for `prfRandomNonceToPrfDistinguisher`**, a step of the proof of
[BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270): running `prfRandomNonceToPrfDistinguisher` in
`prfRealGame id family` at security parameter `n` has the exact same acceptance distribution as the
computational `MACScheme.sufCmaGame` of `carterWegmanRandomMAC`. -/
theorem eval_prfRealGame_prfRandomNonceToPrfDistinguisher
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    (adversary : Forger) (n : ℕ) :
    ProbComp.eval (prfRealGame id family
      (prfRandomNonceToPrfDistinguisher msgLen seed hash adversary) n) =
    ProbComp.eval
      ((carterWegmanRandomMAC msgLen seed hash family hmsgLen hseed hhash hfamily).sufCmaGame
        adversary n) := by
  let M := carterWegmanRandomMAC msgLen seed hash family hmsgLen hseed hhash hfamily
  unfold prfRandomNonceToPrfDistinguisher MACScheme.sufCmaGame
  refine eval_prfRealGame_prfLogDistinguisher family seed (cwRandomNonceLogHandler msgLen hash)
    adversary _ _ (M.signingPairOracle n)
    (fun sk out =>
      (out.1.1.length == M.msgLen n) && !out.2.contains out.1 &&
        M.verify sk out.1.1 out.1.2) n ?_ ?_
  · intro k prfKey hprfLen request state
    dsimp only [cwRandomNonceLogHandler, MACScheme.signingPairOracle,
      MACScheme.signingPairOracleOn, M, carterWegmanRandomMAC]
    simp only [encPair_apply, encBits_apply, unframe_frame_append, dropFrame_frame_append,
      hprfLen]
    by_cases hcond : (request.2.length == msgLen n) = true
    · simp [hcond, pmf_norm, Functor.map_map, OracleComp.interpret_bind,
        OracleComp.interpret_map, ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query,
        ProbComp.interpret_unifFin]
    · simp [Bool.eq_false_iff.mpr hcond]
  · intro k prfKey hprfLen ⟨⟨msg, fullTag⟩, tr⟩
    simp only [M, carterWegmanRandomMAC, encPair_apply, encBits_apply, unframe_frame_append,
      dropFrame_frame_append, hprfLen]
    cases (msg.length == msgLen n) <;> cases ((unframe fullTag).length == n) <;>
      cases tr.contains (msg, fullTag) <;> rfl

open scoped List

private def toRandomBitTriple (msgLen : ℕ → ℕ) (n : ℕ) (out : List Bool × List Bool) :
    (BitString (msgLen n) × BitString n) × BitString n :=
  ((BitString.ofList (msgLen n) out.1, BitString.ofList n (unframe out.2)),
    BitString.ofList n (dropFrame out.2))

private def ofRandomBitTriple {m n : ℕ} (e : (BitString m × BitString n) × BitString n) :
    List Bool × List Bool :=
  (List.ofFn e.1.1, encPair encBits encBits (List.ofFn e.1.2, List.ofFn e.2))

private def adaptRandomNonceStep (msgLen : ℕ → ℕ) (n : ℕ) (request : Unit × List Bool)
    (queriedPairs : List (List Bool × List Bool)) :
    ProbOracleComp (fun _ : BitString (msgLen n) => BitString n × BitString n)
      (List Bool × List (List Bool × List Bool)) :=
  let msg := request.2
  if msg.length == msgLen n then
    (fun xt : BitString n × BitString n =>
      let fullTag := encPair encBits encBits (List.ofFn xt.1, List.ofFn xt.2)
      (fullTag, (msg, fullTag) :: queriedPairs)) <$>
      ProbOracleComp.query (BitString.ofList (msgLen n) msg)
  else
    pure ([], queriedPairs)

private theorem isQueryBounded_adaptRandomNonceStep (msgLen : ℕ → ℕ) (n : ℕ)
    {α : Type} {prog : WordOracleComp Unit α} {Q : ℕ} (hprog : prog.IsQueryBounded Q)
    (init : List (List Bool × List Bool)) :
    ((OracleComp.interpret
      (OracleComp.sumHandler
        (fun m => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin m)))
        (adaptRandomNonceStep msgLen n))
      prog).run init).IsQueryBounded Q := by
  refine OracleComp.IsCostBounded.run_interpret (fun q s => ?_) hprog init
  cases q with
  | inl m =>
    simp only [OracleComp.sumHandler, StateT.run_lift, Sum.elim_inl]
    simpa using (ProbOracleComp.IsQueryBounded.sample (ProbComp.unifFin m)).bind
      fun a => .pure (a, s) 0
  | inr req =>
    dsimp only [OracleComp.sumHandler, StateT.run, adaptRandomNonceStep, Sum.elim_inr]
    split_ifs
    · rw [OracleComp.isCostBounded_map_iff]
      exact ProbOracleComp.IsQueryBounded.query (BitString.ofList (msgLen n) req.2)
    · exact OracleComp.IsCostBounded.pure _ 1

private theorem cwRandomNonceAccept_imp_checkRandomNonceSUF
    (msgLen : ℕ → ℕ) (hash : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (k : List Bool) (table : BitString n → BitString n)
    (cand : List Bool × List Bool) (init : List (List Bool × List Bool))
    (tr : List ((BitString (msgLen n) × BitString n) × BitString n))
    (hsub : tr.map ofRandomBitTriple <+ init.reverse)
    (hcheck : ((cand.1.length == msgLen n) && ((unframe cand.2).length == n) &&
      !init.contains cand &&
      (encPair encBits encBits (unframe cand.2,
        BitString.listXor n
          [hash n k cand.1, (randomFunctionOracle n table (unframe cand.2)).take n]) ==
        cand.2)) = true) :
    checkRandomNonceSUF
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m)))
      k table tr (toRandomBitTriple msgLen n cand) = true := by
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
    beq_iff_eq] at hcheck
  rcases hcheck with ⟨⟨⟨hmsg, hnonce⟩, hnotmem⟩, hfullTag⟩
  have hdrop :
      dropFrame cand.2 =
        BitString.listXor n
          [hash n k cand.1, (randomFunctionOracle n table (unframe cand.2)).take n] := by
    simpa only [encPair_apply, encBits_apply, dropFrame_frame_append] using
      congrArg dropFrame hfullTag.symm
  have htag : (dropFrame cand.2).length = n := hdrop ▸ BitString.length_listXor _ _
  have hround : ofRandomBitTriple (toRandomBitTriple msgLen n cand) = cand := by
    dsimp only [ofRandomBitTriple, toRandomBitTriple]
    rw [BitString.ofFn_ofList hmsg, BitString.ofFn_ofList hnonce, BitString.ofFn_ofList htag,
      hdrop, hfullTag]
  simp only [checkRandomNonceSUF, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
    decide_eq_false_iff_not]
  refine ⟨fun hin => hnotmem (List.mem_reverse.mp (hsub.subset (hround ▸ List.mem_map_of_mem hin))),
    ?_⟩
  simp only [verify, toRandomBitTriple, BitString.ofFn_ofList hmsg, decide_eq_true_eq, hdrop,
    randomFunctionOracle, hnonce, ↓reduceIte, BitString.listXor_pair, BitString.ofList_take,
    BitString.ofList_ofFn]

private theorem step_cwRandomNonceLogHandler_randomFunctionOracle
    (msgLen : ℕ → ℕ) (hash : ℕ → List Bool → List Bool → List Bool)
    (n : ℕ) (k : List Bool) (table : BitString n → BitString n)
    (request : Unit × List Bool)
    (init : List (List Bool × List Bool))
    (tr : List ((BitString (msgLen n) × BitString n) × BitString n))
    (hsub : tr.map ofRandomBitTriple <+ init.reverse) :
    let hashBit := fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))
    let rhs := ProbOracleComp.runWith (randomNonceFnHandler hashBit k table)
      (adaptRandomNonceStep msgLen n request init) tr
    rhs.map Prod.fst =
      ProbComp.eval
        (OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifFin
            (fun req => pure (randomFunctionOracle n table req.2)))
          (cwRandomNonceLogHandler msgLen hash n k request init)) ∧
      ∀ reply wstate' tstate', ((reply, wstate'), tstate') ∈ rhs.support →
        tstate'.map ofRandomBitTriple <+ wstate'.reverse := by
  dsimp only [cwRandomNonceLogHandler, adaptRandomNonceStep]
  set msg := request.2
  by_cases hcond : (msg.length == msgLen n) = true
  · simp only [hcond, ↓reduceIte, ProbOracleComp.runWith_map, ProbOracleComp.runWith_query,
      randomNonceFnHandler, Functor.map_map, OracleComp.interpret_bind, OracleComp.interpret_map,
      ProbOracleComp.interpret_sample, ProbOracleComp.interpret_query,
      ProbComp.interpret_unifFin, BitString.eval_sampleList, BitString.uniformList, PMF.map,
      pmf_norm]
    simp only [beq_iff_eq] at hcond
    let mBit := BitString.ofList (msgLen n) msg
    let tOf (x : BitString n) := sign
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m)))
      k (table x) mBit
    have htag (x : BitString n) : List.ofFn (tOf x) =
        BitString.listXor n
          [hash n k msg, (randomFunctionOracle n table (List.ofFn x)).take n] := by
      simp only [tOf, mBit, sign, BitString.ofFn_ofList hcond, randomFunctionOracle,
        List.length_ofFn, ↓reduceIte, BitString.listXor_pair, BitString.ofList_take,
        BitString.ofList_ofFn]
    refine ⟨congrArg _ (funext fun x => by simp [mBit, tOf, htag]), ?_⟩
    rintro _ _ _ hmem
    supp_cases hmem with ⟨x, -, rfl⟩
    simp only [id_eq, List.map_append, List.map_singleton, List.reverse_cons,
      ofRandomBitTriple, BitString.ofFn_ofList hcond]
    exact hsub.append (List.Sublist.refl _)
  · simp only [Bool.eq_false_iff.mpr hcond, Bool.false_eq_true, ↓reduceIte,
      ProbOracleComp.runWith_pure, OracleComp.interpret_pure, ProbComp.eval_pure, PMF.pure_map,
      PMF.support_pure, Set.mem_singleton_iff]
    exact ⟨trivial, fun | _, _, _, rfl => hsub⟩

/-- **Ideal-game bound for `prfRandomNonceToPrfDistinguisher`**, a step of the proof of
[BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270): under
`IsDeltaUniversalHash (ProbComp.eval (seed n)) ... ε`, if `adversary n []` makes at most `Q` signing
queries, the ideal-game acceptance probability of
`prfRandomNonceToPrfDistinguisher msgLen seed hash adversary` at parameter `n` is at most
`(Q : ℝ≥0∞) ^ 2 / (2 * (2 : ℝ≥0∞) ^ n) + ((2 : ℝ≥0∞) ^ n)⁻¹ + ε`. -/
theorem eval_prfIdealGame_prfRandomNonceToPrfDistinguisher_le
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool} {n Q : ℕ} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) ε)
    {adversary : Forger} (hq : (adversary n []).IsQueryBounded Q) :
    ProbComp.eval
      (prfIdealGame id id (prfRandomNonceToPrfDistinguisher msgLen seed hash adversary) n) true ≤
      (Q : ℝ≥0∞) ^ 2 / (2 * (2 : ℝ≥0∞) ^ n) + ((2 : ℝ≥0∞) ^ n)⁻¹ + ε := by
  let hashBit : List Bool → BitString (msgLen n) → BitString n :=
    fun k m => BitString.ofList n (hash n k (List.ofFn m))
  unfold prfRandomNonceToPrfDistinguisher
  refine (eval_prfIdealGame_prfLogDistinguisher_le seed (cwRandomNonceLogHandler msgLen hash)
    adversary _ _ n (randomNonceFnHandler hashBit) (adaptRandomNonceStep msgLen n) []
    (fun tr init => tr.map ofRandomBitTriple <+ init.reverse)
    (fun k table res =>
      checkRandomNonceSUF hashBit k table res.2 (toRandomBitTriple msgLen n res.1.1))
    (List.Sublist.refl [])
    (step_cwRandomNonceLogHandler_randomFunctionOracle msgLen hash n)
    (cwRandomNonceAccept_imp_checkRandomNonceSUF msgLen hash n)).trans ?_
  simpa only [BitString.card, Nat.cast_pow, Nat.cast_ofNat] using
    seed_uniform_probOracleComp_checkRandomNonceSUF_le hh
      (isQueryBounded_adaptRandomNonceStep msgLen n hq []) fun x => toRandomBitTriple msgLen n x.1

/-- **Quantitative SUF-CMA bound for `carterWegmanRandomMAC`** (after [BonehShoup2023],
Theorem 7.9, Section 7.4, p. 270, for a hash that is an `ε`-DUF at parameter `n`, with `ε` in place
of the theorem's DUF advantage): at security parameter `n`, the SUF-CMA forgery probability of any
`Q`-query `Forger` against `carterWegmanRandomMAC` is at most
`(Q : ℝ) ^ 2 / (2 * (2 : ℝ) ^ n) + ((2 : ℝ) ^ n)⁻¹ + ε.toReal` plus the PRF distinguishing
advantage of `prfRandomNonceToPrfDistinguisher msgLen seed hash adversary`. -/
theorem sufCmaGame_carterWegmanRandomMAC_toReal_le
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    (hfamily : ComputableInPolyTime
      (fun p : List Bool × List Bool => family p.1 p.2)
      (encPair encBits encBits) encBits)
    {n Q : ℕ} {ε : ℝ≥0∞}
    (hh : IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) ε)
    (hε : ε ≠ ⊤) {adversary : Forger} (hq : (adversary n []).IsQueryBounded Q) :
    (ProbComp.eval
      ((carterWegmanRandomMAC msgLen seed hash family hmsgLen hseed hhash hfamily).sufCmaGame
        adversary n) true).toReal ≤
      (Q : ℝ) ^ 2 / (2 * (2 : ℝ) ^ n) + ((2 : ℝ) ^ n)⁻¹ + ε.toReal +
        (Game.advantage
          (ProbComp.eval
            (prfRealGame id family
              (prfRandomNonceToPrfDistinguisher msgLen seed hash adversary) n))
          (ProbComp.eval
            (prfIdealGame id id
              (prfRandomNonceToPrfDistinguisher msgLen seed hash adversary) n)) : ℝ) := by
  rw [← eval_prfRealGame_prfRandomNonceToPrfDistinguisher hmsgLen hseed hhash hfamily adversary n,
    ← Game.coe_succProbability]
  refine (Game.coe_succProbability_le_add_of_advantage_le le_rfl).trans (add_le_add ?_ le_rfl)
  rw [Game.coe_succProbability]
  have hcol_ne_top : (Q : ℝ≥0∞) ^ 2 / (2 * (2 : ℝ≥0∞) ^ n) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.pow_ne_top (ENNReal.natCast_ne_top Q))
      (mul_ne_zero (by norm_num) (pow_ne_zero n (by norm_num)))
  have hinv_ne_top : ((2 : ℝ≥0∞) ^ n)⁻¹ ≠ ⊤ := by simp
  simpa only [ENNReal.toReal_add hcol_ne_top hinv_ne_top, ENNReal.toReal_div, ENNReal.toReal_pow,
    ENNReal.toReal_natCast, ENNReal.toReal_mul, ENNReal.toReal_ofNat, ENNReal.toReal_inv] using
    ENNReal.toReal_le_add (eval_prfIdealGame_prfRandomNonceToPrfDistinguisher_le hh hq)
      (ENNReal.add_ne_top.mpr ⟨hcol_ne_top, hinv_ne_top⟩) hε

/-- Statistical-DUF step toward [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), not the cited
result: if `family` is a `PseudorandomFunction` and `(seed n, hash n)` is an
`(ε n)`-almost-Δ-universal hash family on `BitString (msgLen n)` into `BitString n` with
`Negligible ε`, then `carterWegmanRandomMAC` satisfies `MACScheme.SUFCMA`.

The hash is assumed to be an `ε n`-DUF with negligible `ε`, that is, a statistical DUF
([BonehShoup2023], Definition 7.5, p. 269), whose bound holds against every adversary, efficient or
not. Theorem 7.9 assumes only a computational DUF: negligible advantage in Attack Game 7.3
(p. 268) for every efficient adversary. Every statistical DUF is a computational DUF, so this
premise is the stronger one and the theorem does not follow from this step. The computational-DUF
theorem is open (#5293). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.sufCma_carterWegmanRandomMAC_of_statisticalDUF
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) (ε n))
    (hε : Negligible ε) :
    (carterWegmanRandomMAC msgLen seed hash family hmsgLen hseed hhash hprf.polyTime).SUFCMA := by
  refine MACScheme.SUFCMA.of_negligible fun adversary hadversary => ?_
  obtain ⟨c, d, hbound⟩ := hadversary.query_bounds
  let Q (n : ℕ) : ℕ := c * (n + 2) ^ d
  have hdist := hprf.secure (prfRandomNonceToPrfDistinguisher msgLen seed hash adversary)
    (isOraclePPT_prfRandomNonceToPrfDistinguisher hmsgLen hseed hhash hadversary)
  negligible using fun n =>
    sufCmaGame_carterWegmanRandomMAC_toReal_le hmsgLen hseed hhash hprf.polyTime
      (hh n) ENNReal.coe_ne_top (by simpa [Q] using (hbound n []).1)

/-- Statistical-DUF step toward [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), not the cited
result: `MACScheme.EUFCMA` security of `carterWegmanRandomMAC` under the premises of
`PseudorandomFunction.sufCma_carterWegmanRandomMAC_of_statisticalDUF`. The hash is assumed to be an
`ε n`-DUF with negligible `ε`, a statistical DUF ([BonehShoup2023], Definition 7.5, p. 269), where
the theorem assumes only a computational DUF (Attack Game 7.3, p. 268). The computational-DUF
theorem is open (#5293). -/
theorem _root_.Cslib.Crypto.PseudorandomFunction.eufCma_carterWegmanRandomMAC_of_statisticalDUF
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) (ε n))
    (hε : Negligible ε) :
    (carterWegmanRandomMAC msgLen seed hash family hmsgLen hseed hhash hprf.polyTime).EUFCMA :=
  (hprf.sufCma_carterWegmanRandomMAC_of_statisticalDUF hmsgLen hseed hhash hh hε).eufCma

/-- Statistical-DUF step toward [BonehShoup2023], Theorem 7.9 (Section 7.4, p. 270), not the cited
result: `MACScheme.OneTimeEUFCMA` security of `carterWegmanRandomMAC` under the premises of
`PseudorandomFunction.sufCma_carterWegmanRandomMAC_of_statisticalDUF`. The hash is assumed to be an
`ε n`-DUF with negligible `ε`, a statistical DUF ([BonehShoup2023], Definition 7.5, p. 269), where
the theorem assumes only a computational DUF (Attack Game 7.3, p. 268). The computational-DUF
theorem is open (#5293). -/
theorem
    _root_.Cslib.Crypto.PseudorandomFunction.oneTimeEUFCMA_carterWegmanRandomMAC_of_statisticalDUF
    {msgLen : ℕ → ℕ} {seed : ℕ → ProbComp (List Bool)}
    {hash : ℕ → List Bool → List Bool → List Bool}
    {family : List Bool → List Bool → List Bool}
    (hprf : PseudorandomFunction family)
    (hmsgLen : ComputableInPolyTime msgLen encUnary encUnary)
    (hseed : IsPPTOn encUnary encBits seed)
    (hhash : ComputableInPolyTime
      (fun ((n, k, m) : ℕ × List Bool × List Bool) => hash n k m)
      (encKeyedInput encBits) encBits)
    {ε : ℕ → ℝ≥0}
    (hh : ∀ n, IsDeltaUniversalHash (ProbComp.eval (seed n))
      (fun k (m : BitString (msgLen n)) => BitString.ofList n (hash n k (List.ofFn m))) (ε n))
    (hε : Negligible ε) :
    (carterWegmanRandomMAC msgLen seed hash family
      hmsgLen hseed hhash hprf.polyTime).OneTimeEUFCMA :=
  (hprf.sufCma_carterWegmanRandomMAC_of_statisticalDUF hmsgLen hseed hhash hh hε).oneTimeEUFCMA

end Randomized

end Cslib.Crypto.Protocols.CarterWegman
