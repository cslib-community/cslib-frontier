/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.Garbling.Asymptotic
public import CslibFrontier.Crypto.Protocols.MPC.Yao.Family
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.DPi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Pi
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Composition
import CslibFrontier.Crypto.Protocols.MPC.EmptyCoalition
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Steps for Yao's protocol in the ideal oblivious-transfer hybrid model

`CslibFrontier/Crypto/Protocols/MPC/Yao/Family.lean` runs Yao's protocol over a garbling scheme `G`
in the ideal `batchOTWorld` (`batchOTSpec`) oblivious-transfer hybrid model (#6045) as both the
one-sided protocol family `Yao.oneSidedFamily G` ([BellareHoangRogaway2012], §7.1, Fig. 16, p. 34)
and the two-output protocol family `Yao.family G` ([LindellPinkas2009], Protocol 2, §4.2, p. 15),
proving the corrupted-garbler steps (`Yao.hybridSemiHonestSecure_oneSided_garbler`,
`Yao.hybridSemiHonestSecure_garbler`). This module proves the corrupted-evaluator steps from
simulation privacy of `G`
(`Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure_evaluator`,
`Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure_evaluator`) and combines the cases into
`Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure` (across all static coalitions
`I : Finset (Fin 2)`) and `Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure`, rather than
plain-model Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15) or Theorem 14 of
[BellareHoangRogaway2012] (§7.1, p. 35), which compose with a concrete semi-honest 1-out-of-2
oblivious-transfer protocol.

**The assumption.** `ProtocolFamily.SemiHonestSecure` asks for one simulator family for every
environment, and the reductions below build one garbling adversary per environment. So the scheme
needs one `prv.sim` simulator for every adversary, `Scheme.PrvSimSecureUniversal`.
`Scheme.PrvSimSecure`, with the quantifiers `∀ B ∃ S` of [BellareHoangRogaway2012] (§3.4, p. 9),
would give one simulator per environment. For arbitrary side information the one-simulator form is
novel to this library; [ZahurRosulekEvans2015] (§2, p. 5) state it for the side information
`Φ_circ`. So the theorems of this module rest on a novel assumption and are steps, named after it.
Point-and-permute and half-gates garbling satisfy it
(`CslibFrontier/Crypto/Protocols/MPC/Yao/Instances.lean`), so the instances there rest only on the
standard assumptions `PseudorandomFunction` and `CircularCorrelationRobust`.

**The simulators.** `Yao.oneSidedEvaluatorSim G Φ S` and `Yao.evaluatorSim G Φ S` run a garbling
simulator `S` on the security parameter, the evaluator's output and `Φ(f)`, and read the
evaluator's view from the simulated `(F, X, d)` (`Yao.oneSidedViewOfPrvView`,
`Yao.viewOfPrvView`): `X` splits into `G.inLen f` tokens of equal width, the first `garblerLen` of
which go into the garbler's message with `F` and `d`, and the others are the tokens that the
oblivious transfer delivers. They play the role of the simulator `S₂` of Case 2 of the proof of
Theorem 7 of [LindellPinkas2009] (pp. 18–19), with the garbling simulator in place of their fake
garbled circuit; in the hybrid model their first step, simulating the evaluator's view of the
oblivious-transfer protocol, is empty. Both are PPT when `S` is, `Φ` is computed in polynomial time
and `G` reads input lengths in polynomial time (`Yao.isPPT_oneSidedEvaluatorSim`,
`Yao.isPPT_evaluatorSim`).

**The reductions.** `Yao.oneSidedEvaluatorToPrvSim samp Z` and `Yao.evaluatorToPrvSim samp Z` turn
an environment `Z` into a `prv.sim` adversary, sharing the state `Yao.ReductionState` and its
encoding `Yao.encReductionState`. Their choice stages draw the public parameters with `samp`, run
`Z.choose` and query the function on the garbler's bits followed by the evaluator's; their guess
stages read the evaluator's view from `(F, X, d)` and run `Z.guess`, with `Yao.oneSidedOutputs`
(`[]` for the garbler, the function's output for the evaluator) or the function's output for both
parties. On a real garbled view, `oneSidedViewOfPrvView` and `viewOfPrvView` give the evaluator's
real view (`Yao.oneSidedViewOfPrvView_gb`, `Yao.viewOfPrvView_gb`), so from `n = 1` on an
environment's advantage is the `prv.sim` advantage of the reduction
(`Yao.advantage_oneSidedEvaluator_eq`, `Yao.advantage_evaluator_eq`), and both reductions are PPT
whenever `Z` is (`Yao.isPPT_oneSidedEvaluatorToPrvSim`, `Yao.isPPT_evaluatorToPrvSim`).

## Comparison with [LindellPinkas2009], Theorem 7, and [BellareHoangRogaway2012], Theorem 14

`Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure` and
`Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure` are steps towards Theorem 7 (§4.2, p. 15)
and Theorem 14 (§7.1, p. 35), not those theorems:

* **Oblivious transfer.** The transfers are the ideal `batchOTSpec`. Both Theorem 7 and Theorem 14
  assume an oblivious transfer protocol secure against semi-honest adversaries, and their proofs
  simulate that protocol's views; composition with a protocol is not formalized here (#6045).
* **Garbling scheme and assumption.** Any garbling scheme with polynomial-time algorithms, correct
  from `n = 1` on, with the encoding `projectiveEncode` (projective in one word layout, with tokens
  of one width) and `prv.sim` secure with one simulator, in place of the double-encryption
  construction of [LindellPinkas2009] (§4.1, p. 12). This modular form follows
  [BellareHoangRogaway2012], §7.1 (Fig. 16, p. 34; Theorem 14, p. 35), whose quantifiers are
  `∀ B ∃ S` on both sides.
* **Environments.** Uniform PPT environments that choose the inputs after seeing the public
  parameters, the uniform variant of `ProtocolFamily.SemiHonestSecure`; Definition 1 (p. 5) of
  Lindell and Pinkas quantifies over all inputs against non-uniform distinguishers.
* **The function.** The function description is a public parameter drawn by a PPT sampler; a
  uniform family of functions is the case of a deterministic sampler. In Lindell and Pinkas the
  circuit is auxiliary input. The reduction draws the function itself, so security against the
  evaluator needs an efficient sampler; security against the garbler holds for every setup law.
* **Inputs and outputs.** The garbler holds the first `garblerLen` input bits and the evaluator the
  rest, where Lindell and Pinkas give each party `n` bits. `Yao.oneSidedFamily` delivers `[]` to
  the garbler and `G.ev fn x` to the evaluator (as in [BellareHoangRogaway2012], §7.1, Fig. 16);
  `Yao.family` delivers `G.ev fn x` to both parties (as in [LindellPinkas2009], Protocol 2).

## Main definitions

* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedViewOfPrvView`,
  `Cslib.Crypto.Protocols.MPC.Yao.viewOfPrvView`: the evaluator's view from a garbled view.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedEvaluatorSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.evaluatorSim`: the simulators for a corrupted evaluator.
* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedEvaluatorToPrvSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.evaluatorToPrvSim`: the reductions to `prv.sim`, sharing
  `Cslib.Crypto.Protocols.MPC.Yao.ReductionState` and
  `Cslib.Crypto.Protocols.MPC.Yao.encReductionState`.

## Main results

* `Cslib.Crypto.Protocols.MPC.Yao.oneSidedViewOfPrvView_gb`,
  `Cslib.Crypto.Protocols.MPC.Yao.viewOfPrvView_gb`: on a real garbled view, the evaluator's real
  view.
* `Cslib.Crypto.Protocols.MPC.Yao.advantage_oneSidedEvaluator_eq`,
  `Cslib.Crypto.Protocols.MPC.Yao.advantage_evaluator_eq`: the reductions are exact.
* `Cslib.Crypto.Protocols.MPC.Yao.isPPT_oneSidedEvaluatorSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.isPPT_oneSidedEvaluatorToPrvSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.isPPT_evaluatorSim`,
  `Cslib.Crypto.Protocols.MPC.Yao.isPPT_evaluatorToPrvSim`: the simulators and reductions are PPT.
* `Cslib.Crypto.Garbling.Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure_evaluator`,
  `Cslib.Crypto.Garbling.Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure_evaluator`: steps
  for a corrupted evaluator in the ideal `batchOTWorld` hybrid (#6045).
* `Cslib.Crypto.Garbling.Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure`: step
  across all static coalitions `I : Finset (Fin 2)` for `Yao.oneSidedFamily` in the ideal
  `batchOTWorld` hybrid (#6045).
* `Cslib.Crypto.Garbling.Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure`: step against
  either party for `Yao.family` in the ideal `batchOTWorld` hybrid (#6045).

## References

* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009], cited in the ePrint version 2004/175 of June 26, 2006:
  Definition 1 (§2.1, p. 5), §4.1 (p. 12), Theorem 7 (§4.2, p. 15), Case 2 (pp. 18–19).
* [M. Bellare, V. T. Hoang, P. Rogaway, *Foundations of Garbled Circuits*][BellareHoangRogaway2012],
  §3.4 (p. 9) and §7.1 (Fig. 16, p. 34; Theorem 14, p. 35).
* [S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole: Reducing Data Transfer in Garbled
  Circuits using Half Gates*][ZahurRosulekEvans2015], §2 (p. 5).
-/

public section

namespace Cslib.Crypto.Protocols.MPC.Yao

open Cslib.Crypto.Garbling Probability Turing.MultiTapeTM

variable {Fn Λ : Type} {G : Scheme Fn}

/-! ### The evaluator's view from a garbled view -/

/-- The evaluator's view in `oneSidedProtocol` that a `prv.sim` view `(F, X, d)` gives: `X` is
split into `G.inLen c.fn` tokens of equal width, the first `c.garblerLen` of which go into the
garbler's message with `F` and `d`, and the others are the tokens that the oblivious transfer
delivers. -/
@[expose] def oneSidedViewOfPrvView (c : Params G) (x₁ : BitString c.evaluatorLen) (V : PrvView) :
    PartyView (Input c) Coins (oneSidedSchedule c) 1 :=
  let tokens := BitString.listRows (G.inLen c.fn) (V.input.length / G.inLen c.fn) V.input
  oneSidedEvaluatorView c x₁ ⟨V.fn, tokens.take c.garblerLen, V.decInfo⟩
    fun j => tokens.getD (c.garblerLen + j) []

/-- The evaluator's view in `protocol` that a `prv.sim` view `(F, X, d)` gives: `X` is split into
`G.inLen c.fn` tokens of equal width, the first `c.garblerLen` of which go into the garbler's
message with `F` and `d`, and the others are the tokens that the oblivious transfer delivers. -/
@[expose] def viewOfPrvView (c : Params G) (x₁ : BitString c.evaluatorLen) (V : PrvView) :
    PartyView (Input c) Coins (schedule c) 1 :=
  let tokens := BitString.listRows (G.inLen c.fn) (V.input.length / G.inLen c.fn) V.input
  evaluatorView c x₁ ⟨V.fn, tokens.take c.garblerLen, V.decInfo⟩
    fun j => tokens.getD (c.garblerLen + j) []

/-- On the real garbled view of the function's input with the garbler's coins `coins`,
`oneSidedViewOfPrvView` is the evaluator's view in `oneSidedProtocol` with these coins, when the
encoding of `G` is `projectiveEncode`. -/
theorem oneSidedViewOfPrvView_gb (hproj : G.encode = projectiveEncode) (n : ℕ) (c : Params G)
    (x : (i : Fin 2) → Input c i) (coins : List Bool) :
    oneSidedViewOfPrvView c (x 1) ⟨(G.gb n c.fn coins).fn,
        G.encode (G.gb n c.fn coins).encInfo (circuitInput x), (G.gb n c.fn coins).decInfo⟩ =
      oneSidedEvaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
        (fun j => garblerOffer G n c coins j (x 1 j)) := by
  set e := (G.gb n c.fn coins).encInfo
  have hle := c.garblerLen_le
  set T : List (List Bool) :=
    List.ofFn (fun i : Fin c.garblerLen => projectiveToken e (G.inLen c.fn) i (x 0 i)) ++
      List.ofFn (fun j : Fin c.evaluatorLen =>
        projectiveToken e (G.inLen c.fn) (c.garblerLen + j) (x 1 j)) with hTdef
  have hX : G.encode e (circuitInput x) = T.flatten := by
    rw [hproj, projectiveEncode_eq_flatten_ofFn, hTdef, ofFn_projectiveToken_append]
  have hT : T.length = G.inLen c.fn := by
    simp only [hTdef, List.length_append, List.length_ofFn, Params.evaluatorLen]
    omega
  have hwidth : ∀ w ∈ T, w.length = e.length / (2 * G.inLen c.fn) := by
    intro w hw
    simp only [hTdef, List.mem_append, List.mem_ofFn] at hw
    obtain ⟨i, rfl⟩ | ⟨j, rfl⟩ := hw <;> simp [projectiveToken]
  have hrows : BitString.listRows (G.inLen c.fn) (T.flatten.length / G.inLen c.fn) T.flatten =
      T := by
    rcases Nat.eq_zero_or_pos (G.inLen c.fn) with hN | hN
    · have hT0 : T = [] := List.length_eq_zero_iff.mp (hT.trans hN)
      simp [hT0, hN, BitString.listRows]
    · have hflat : T.flatten.length = G.inLen c.fn * (e.length / (2 * G.inLen c.fn)) := by
        rw [List.length_flatten, List.map_congr_left hwidth, List.map_const', List.sum_replicate,
          smul_eq_mul, hT]
      rw [hflat, Nat.mul_div_cancel_left _ hN]
      have h := BitString.listRows_flatten T hwidth
      rwa [hT] at h
  simp only [oneSidedViewOfPrvView, hX, hrows]
  congr 1
  · refine Message.ext rfl ?_ rfl
    exact List.take_left' (List.length_ofFn)
  · funext j
    have hj : c.garblerLen + j < T.length := by
      rw [hT]
      have := j.isLt
      simp only [Params.evaluatorLen] at this
      omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some,
      List.getElem_append_right (by simp), List.getElem_ofFn]
    simp only [List.length_ofFn, Nat.add_sub_cancel_left]
    rfl

/-- On the real garbled view of the function's input with the garbler's coins `coins`,
`viewOfPrvView` is the evaluator's view in `protocol` with these coins, when the encoding of `G` is
`projectiveEncode`. -/
theorem viewOfPrvView_gb (hproj : G.encode = projectiveEncode) (n : ℕ) (c : Params G)
    (x : (i : Fin 2) → Input c i) (coins : List Bool) :
    viewOfPrvView c (x 1) ⟨(G.gb n c.fn coins).fn,
        G.encode (G.gb n c.fn coins).encInfo (circuitInput x), (G.gb n c.fn coins).decInfo⟩ =
      evaluatorView c (x 1) (garblerMessage G n c (x 0) coins)
        (fun j => garblerOffer G n c coins j (x 1 j)) := by
  have h := congrArg PartyView.received (oneSidedViewOfPrvView_gb hproj n c x coins)
  dsimp only [oneSidedViewOfPrvView] at h
  exact PartyView.ext rfl rfl (by simp only [viewOfPrvView, evaluatorView, h])

/-! ### The simulator for a corrupted evaluator -/

variable (G) in
/-- The simulator family for a corrupted evaluator in `oneSidedFamily`, from a garbling simulator
`S` for the side information `Φ`: run `S` on the security parameter, the evaluator's output and
`Φ(c.fn)`, and read the evaluator's view from its garbled view (`oneSidedViewOfPrvView`). -/
@[expose] noncomputable def oneSidedEvaluatorSim (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) :
    SimulatorFamily (oneSidedFamily G) {1} :=
  fun n c xI yI => do
    let V ← S n (yI ⟨1, Finset.mem_singleton_self 1⟩) (Φ.phi c.fn)
    return singletonView (oneSidedViewOfPrvView c (xI ⟨1, Finset.mem_singleton_self 1⟩) V)

variable (G) in
/-- The simulator family for a corrupted evaluator in `family`, from a garbling simulator `S` for
the side information `Φ`: run `S` on the security parameter, the evaluator's output and `Φ(c.fn)`,
and read the evaluator's view from its garbled view (`viewOfPrvView`). -/
@[expose] noncomputable def evaluatorSim (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) :
    SimulatorFamily (family G) {1} :=
  fun n c xI yI => do
    let V ← S n (yI ⟨1, Finset.mem_singleton_self 1⟩) (Φ.phi c.fn)
    return singletonView (viewOfPrvView c (xI ⟨1, Finset.mem_singleton_self 1⟩) V)

/-! ### The reduction to simulation privacy -/

/-- What `oneSidedEvaluatorToPrvSim` and `evaluatorToPrvSim` keep between their stages: the public
parameters, the environment's state, the word of the evaluator's input bits and the function's
output. -/
structure ReductionState (G : Scheme Fn) where
  /-- The public parameters. -/
  params : Params G
  /-- The environment's state. -/
  envState : List Bool
  /-- The word of the evaluator's input bits. -/
  evaluatorInput : List Bool
  /-- The function's output on the chosen inputs. -/
  output : List Bool

/-- The encoding of the reduction's state: each field in turn, all but the last framed, with the
public parameters written by `encParams encFn`. -/
enc_structure encReductionState (encFn : Fn ↪ List Bool) : ReductionState G where
  params : (encParams (G := G) encFn), envState : encBits, evaluatorInput : encBits,
  output : encBits

/-- **The one-sided reduction** from an environment `Z` against a corrupted evaluator in
`oneSidedFamily` to a `prv.sim` adversary against `G`, for public parameters drawn by `samp`. Its
choice stage draws `c` with `samp k`, runs `Z.choose`, and queries `c.fn` on the garbler's bits
followed by the evaluator's; its guess stage reads the evaluator's view from `(F, X, d)`
(`oneSidedViewOfPrvView`) and runs `Z.guess` with `oneSidedOutputs` (`[]` for the garbler and the
output for the evaluator). -/
@[expose] noncomputable def oneSidedEvaluatorToPrvSim (samp : ℕ → ProbComp (Params G))
    (Z : Environment (oneSidedFamily G) {1}) (k : ℕ) : PrvSimAdversary Fn (ReductionState G) where
  choose _ := do
    let c ← samp k
    let ch ← Z.choose k c
    return (⟨c.fn, circuitInput ch.inputs⟩,
      ⟨c, ch.state, List.ofFn (ch.inputs 1), G.ev c.fn (circuitInput ch.inputs)⟩)
  guess st V := Z.guess k st.params st.envState
    (singletonView (oneSidedViewOfPrvView st.params (BitString.ofList _ st.evaluatorInput)
      (V.getD ⟨[], [], []⟩)), oneSidedOutputs st.output)

/-- **The reduction** from an environment `Z` against a corrupted evaluator to a `prv.sim`
adversary against `G`, for public parameters drawn by `samp`. Its choice stage draws `c` with
`samp k`, runs `Z.choose`, and queries the function `c.fn` on the garbler's bits followed by the
evaluator's; it keeps `c`, the environment's state, the evaluator's input word and the function's
output. Its guess stage reads the evaluator's view from the garbled view `(F, X, d)`
(`viewOfPrvView`) and runs `Z.guess` on it and on the output as both parties' outputs. -/
@[expose] noncomputable def evaluatorToPrvSim (samp : ℕ → ProbComp (Params G))
    (Z : Environment (family G) {1}) (k : ℕ) : PrvSimAdversary Fn (ReductionState G) where
  choose _ := do
    let c ← samp k
    let ch ← Z.choose k c
    return (⟨c.fn, circuitInput ch.inputs⟩,
      ⟨c, ch.state, List.ofFn (ch.inputs 1), G.ev c.fn (circuitInput ch.inputs)⟩)
  guess st V := Z.guess k st.params st.envState
    (singletonView (viewOfPrvView st.params (BitString.ofList _ st.evaluatorInput)
      (V.getD ⟨[], [], []⟩)), fun _ => st.output)

/-- Lift an environment against a corrupted evaluator of `oneSidedFamily` to one of `family` by
dropping the empty return round on party `1`'s view and setting party `0`'s output to `[]`. -/
private noncomputable def liftEvaluatorEnv (Z : Environment (oneSidedFamily G) {1}) :
    Environment (family G) {1} where
  choose n c := (fun ch => ⟨ch.inputs, ch.state⟩) <$> Z.choose n c
  guess n c st r := Z.guess n c st
    (singletonView (let v := r.1 ⟨1, Finset.mem_singleton_self 1⟩
      ⟨v.input, v.coins, (Schedule.Received.split (sc₁ := oneSidedSchedule c) v.received).1⟩),
      oneSidedOutputs (r.2 1))

private theorem eval_prvSimExperiment_oneSidedEvaluatorToPrvSim (samp : ℕ → ProbComp (Params G))
    (Z : Environment (oneSidedFamily G) {1}) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    (n : ℕ) (b : Bool) :
    ProbComp.eval (prvSimExperiment G Φ n (S n) (oneSidedEvaluatorToPrvSim samp Z n) b) =
      ProbComp.eval
        (prvSimExperiment G Φ n (S n) (evaluatorToPrvSim samp (liftEvaluatorEnv Z) n) b) := by
  have hchoose : ProbComp.eval ((oneSidedEvaluatorToPrvSim samp Z n).choose ()) =
      ProbComp.eval ((evaluatorToPrvSim samp (liftEvaluatorEnv Z) n).choose ()) := by
    simp only [oneSidedEvaluatorToPrvSim, evaluatorToPrvSim, liftEvaluatorEnv, pmf_norm]
  have hguess : (oneSidedEvaluatorToPrvSim samp Z n).guess =
      (evaluatorToPrvSim samp (liftEvaluatorEnv Z) n).guess := rfl
  simp only [prvSimExperiment, ProbComp.eval_bind, hchoose, hguess]

/-- The ideal game with `evaluatorSim G Φ S` is the experiment `PrvSim` of the reduction with the
simulator `S n`, on the simulated side (`b = false`), at every parameter. -/
theorem idealGame_evaluator_eq (samp : ℕ → ProbComp (Params G))
    (Z : Environment (family G) {1}) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) (n : ℕ) :
    (family G).idealGame (fun n => ProbComp.eval (samp n)) {1} (evaluatorSim G Φ S) Z n =
      ProbComp.eval (prvSimExperiment G Φ n (S n) (evaluatorToPrvSim samp Z n) false) := by
  simp only [ProtocolFamily.idealGame, prvSimExperiment, evaluatorToPrvSim, pmf_norm]
  refine congrArg _ (funext fun c => congrArg _ (funext fun ch => ?_))
  simp only [length_circuitInput, ↓reduceIte, Bool.false_eq_true]
  simp only [idealJoint, functionality, Functionality.ofDeterministic, evaluatorSim,
    Option.getD_some, BitString.ofList_ofFn (n := c.evaluatorLen) (ch.inputs 1), pmf_norm]
  rfl

/-- At every parameter `n ≥ 1`, the real game against a corrupted evaluator is the experiment
`PrvSim` of the reduction on the real side (`b = true`), when `G` is correct and its encoding is
`projectiveEncode`. -/
theorem realGame_evaluator_eq (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (samp : ℕ → ProbComp (Params G)) (Z : Environment (family G) {1})
    (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) :
    (family G).realGame (fun n => ProbComp.eval (samp n)) {1} Z n =
      ProbComp.eval (prvSimExperiment G Φ n (S n) (evaluatorToPrvSim samp Z n) true) := by
  simp only [ProtocolFamily.realGame, prvSimExperiment, evaluatorToPrvSim, pmf_norm]
  refine congrArg _ (funext fun c => congrArg _ (funext fun ch => ?_))
  simp only [length_circuitInput, ↓reduceIte]
  simp only [realJoint_evaluator, Scheme.prvView, Scheme.garble, BitString.eval_sampleList,
    Option.getD_some, BitString.ofList_ofFn (n := c.evaluatorLen) (ch.inputs 1), pmf_norm]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
  simp only [viewOfPrvView_gb hproj,
    runOutput_eq hproj hcorrect hn c ch.inputs (BitString.mem_support_uniformList_iff.mp hcoins)]

/-- In `oneSidedFamily`, the ideal game with `oneSidedEvaluatorSim G Φ S` is the experiment
`PrvSim` of `oneSidedEvaluatorToPrvSim` with `S n` on the simulated side (`b = false`). -/
theorem idealGame_oneSidedEvaluator_eq (samp : ℕ → ProbComp (Params G))
    (Z : Environment (oneSidedFamily G) {1}) (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ)
    (n : ℕ) :
    (oneSidedFamily G).idealGame (fun n => ProbComp.eval (samp n)) {1}
        (oneSidedEvaluatorSim G Φ S) Z n =
      ProbComp.eval (prvSimExperiment G Φ n (S n) (oneSidedEvaluatorToPrvSim samp Z n) false) := by
  rw [eval_prvSimExperiment_oneSidedEvaluatorToPrvSim, ← idealGame_evaluator_eq]
  simp only [ProtocolFamily.idealGame, liftEvaluatorEnv, idealJoint, oneSidedFunctionality,
    functionality, Functionality.ofDeterministic, oneSidedEvaluatorSim, evaluatorSim, pmf_norm]
  rfl

/-- At every parameter `n ≥ 1` in `oneSidedFamily`, the real game against a corrupted evaluator is
the experiment `PrvSim` of `oneSidedEvaluatorToPrvSim` on the real side (`b = true`), when `G` is
correct and its encoding is `projectiveEncode`. -/
theorem realGame_oneSidedEvaluator_eq (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (samp : ℕ → ProbComp (Params G)) (Z : Environment (oneSidedFamily G) {1})
    (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) :
    (oneSidedFamily G).realGame (fun n => ProbComp.eval (samp n)) {1} Z n =
      ProbComp.eval (prvSimExperiment G Φ n (S n) (oneSidedEvaluatorToPrvSim samp Z n) true) := by
  rw [eval_prvSimExperiment_oneSidedEvaluatorToPrvSim, ← realGame_evaluator_eq hproj hcorrect hn]
  simp only [ProtocolFamily.realGame, liftEvaluatorEnv, realJoint_oneSided_evaluator,
    realJoint_evaluator, pmf_norm]
  rfl

/-! ### Efficiency -/

/-- The words of the evaluator's view that a `prv.sim` view `V` gives
(`evaluatorViewWords_viewOfPrvView`), from the function's input length `N`, the garbler's input
length `g` and the word `x₁` of the evaluator's bits. -/
private def viewWordsOfPrvView (N g : ℕ) (x₁ : List Bool) (V : PrvView) : EvaluatorViewWords :=
  let tokens := BitString.listRows N (V.input.length / N) V.input
  ⟨x₁, V.fn, tokens.take g, V.decInfo, (List.range (N - g)).map fun j => tokens.getD (g + j) []⟩

/-- `viewWordsOfPrvView` gives the words of `oneSidedViewOfPrvView`. -/
private theorem oneSidedEvaluatorViewWords_viewOfPrvView (c : Params G)
    (x₁ : BitString c.evaluatorLen) (V : PrvView) :
    oneSidedEvaluatorViewWords (oneSidedViewOfPrvView c x₁ V) =
      viewWordsOfPrvView (G.inLen c.fn) c.garblerLen (List.ofFn x₁) V := by
  change EvaluatorViewWords.mk _ _ _ _ (List.ofFn fun j : Fin c.evaluatorLen =>
    (BitString.listRows (G.inLen c.fn) (V.input.length / G.inLen c.fn) V.input).getD
      (c.garblerLen + j) []) = _
  congr 1
  refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_map, List.length_range]
  · simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]

/-- `viewWordsOfPrvView` gives the words of `viewOfPrvView`. -/
private theorem evaluatorViewWords_viewOfPrvView (c : Params G) (x₁ : BitString c.evaluatorLen)
    (V : PrvView) :
    evaluatorViewWords (viewOfPrvView c x₁ V) =
      viewWordsOfPrvView (G.inLen c.fn) c.garblerLen (List.ofFn x₁) V :=
  oneSidedEvaluatorViewWords_viewOfPrvView c x₁ V

/-- `viewWordsOfPrvView` of computed arguments is computed in polynomial time. -/
private theorem viewWordsOfPrvView_polyTime {γ : Type} {enc : γ ↪ List Bool} {N g : γ → ℕ}
    {x₁ : γ → List Bool} {V : γ → PrvView} (hN : ComputableInPolyTime N enc encUnary)
    (hg : ComputableInPolyTime g enc encUnary) (hx : ComputableInPolyTime x₁ enc encBits)
    (hV : ComputableInPolyTime V enc encPrvView) :
    ComputableInPolyTime (fun a => viewWordsOfPrvView (N a) (g a) (x₁ a) (V a)) enc
      encEvaluatorViewWords := by
  unfold viewWordsOfPrvView
  dsimp only
  exact encEvaluatorViewWords_mk_polyTime hx (encPrvView_fn_polyTime hV)
    (ComputableInPolyTime.listTakeWithInput
      (ComputableInPolyTime.bitsRowsWithInput hN (by fun_prop) (encPrvView_input_polyTime hV)) hg)
    (encPrvView_decInfo_polyTime hV)
    (ComputableInPolyTime.mapWithInput (by fun_prop) (by fun_prop))

/-- The word that the evaluator's simulator writes: the one-entry table of the evaluator's view
words. -/
private noncomputable def evaluatorSimWord (N g : ℕ) (x₁ : List Bool) (V : PrvView) : List Bool :=
  encPi encBits fun _ : ({1} : Finset (Fin 2)) =>
    encEvaluatorViewWords (viewWordsOfPrvView N g x₁ V)

/-- **The evaluator's simulator is PPT** for `encoding G encFn` when the garbling simulator `S` is
PPT on `(1^k, y, φ)`, `Φ` is computed in polynomial time and `G` reads input lengths in polynomial
time (`hinLen`). -/
theorem isPPT_evaluatorSim {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool} {Φ : SideInfo Fn Λ}
    {S : ℕ → PrvSimulator Λ} (hinLen : ComputableInPolyTime G.inLen encFn encUnary)
    (hΦ : ComputableInPolyTime Φ.phi encFn encΛ)
    (hS : IsPPTOn (encPair encUnary (encPair encBits encΛ)) encPrvView
      (fun (k, y, φ) => S k y φ)) :
    (evaluatorSim G Φ S).IsPPT (encoding G encFn) := by
  have hn : ComputableInPolyTime (fun x : SimInput (family G) {1} => x.secParam)
      (encSimInput (encoding G encFn)) encUnary :=
    encSimInput_secParam_polyTime (encoding G encFn) .id'
  have hc : ComputableInPolyTime (fun x : SimInput (family G) {1} => x.desc)
      (encSimInput (encoding G encFn)) (encParams encFn) :=
    encSimInput_desc_polyTime (encoding G encFn) .id'
  have hfn := encParams_fn_polyTime hc
  have hx₁ := (encoding G encFn).input.encCoalition_apply_polyTime
    (encSimInput_inputs_polyTime (encoding G encFn) .id')
    (⟨1, Finset.mem_singleton_self 1⟩ : ({1} : Finset (Fin 2)))
  have hy := (encoding G encFn).output.encCoalition_apply_polyTime
    (encSimInput_outputs_polyTime (encoding G encFn) .id')
    (⟨1, Finset.mem_singleton_self 1⟩ : ({1} : Finset (Fin 2)))
  have hprep : ComputableInPolyTime (fun x : SimInput (family G) {1} =>
      (x.secParam, (encoding G encFn).output.rep x.secParam x.desc 1
        (x.outputs ⟨1, Finset.mem_singleton_self 1⟩), Φ.phi x.desc.fn))
      (encSimInput (encoding G encFn)) (encPair encUnary (encPair encBits encΛ)) :=
    hn.prod (hy.prod (hΦ.comp hfn))
  have hword : ComputableInPolyTime (fun p : SimInput (family G) {1} × PrvView =>
      evaluatorSimWord (G.inLen p.1.desc.fn) p.1.desc.garblerLen
        ((encoding G encFn).input.rep p.1.secParam p.1.desc 1
          (p.1.inputs ⟨1, Finset.mem_singleton_self 1⟩)) p.2)
      (encPair (encSimInput (encoding G encFn)) encPrvView) encBits :=
    (ComputableInPolyTime.pi fun _ => (viewWordsOfPrvView_polyTime
      ((hinLen.comp hfn).comp (.fst _ _)) ((encParams_garblerLen_polyTime hc).comp (.fst _ _))
      (hx₁.comp (.fst _ _)) (.snd _ _)).encoding_comp).encoding_comp
  have hprog : IsPPTOn (encSimInput (encoding G encFn)) encBits
      (fun x : SimInput (family G) {1} =>
        (fun V => evaluatorSimWord (G.inLen x.desc.fn) x.desc.garblerLen
          ((encoding G encFn).input.rep x.secParam x.desc 1
            (x.inputs ⟨1, Finset.mem_singleton_self 1⟩)) V) <$>
          S x.secParam ((encoding G encFn).output.rep x.secParam x.desc 1
            (x.outputs ⟨1, Finset.mem_singleton_self 1⟩)) (Φ.phi x.desc.fn)) :=
    (hS.preprocess hprep).map_with hword
  refine isPPTOn_iff_encoded.mpr (hprog.congr fun x => ?_)
  obtain ⟨n, c, xs, ys⟩ := x
  simp only [evaluatorSim, ← PMF.bind_pure_comp, pmf_norm]
  refine congrArg _ (funext fun V => congrArg PMF.pure ?_)
  refine Eq.trans ?_ ((encoding G encFn).view.encCoalition_singleton n c 1 _).symm
  exact congrArg (encPi encBits) (funext fun _ => congrArg encEvaluatorViewWords
    (evaluatorViewWords_viewOfPrvView c _ V).symm)

/-- **The one-sided evaluator simulator is PPT** for `oneSidedEncoding G encFn` when the garbling
simulator `S` is PPT on `(1^k, y, φ)`, `Φ` is computed in polynomial time and `G` reads input
lengths in polynomial time (`hinLen`). -/
theorem isPPT_oneSidedEvaluatorSim {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    {Φ : SideInfo Fn Λ} {S : ℕ → PrvSimulator Λ}
    (hinLen : ComputableInPolyTime G.inLen encFn encUnary)
    (hΦ : ComputableInPolyTime Φ.phi encFn encΛ)
    (hS : IsPPTOn (encPair encUnary (encPair encBits encΛ)) encPrvView
      (fun (k, y, φ) => S k y φ)) :
    (oneSidedEvaluatorSim G Φ S).IsPPT (oneSidedEncoding G encFn) := by
  have htwo := isPPTOn_iff_encoded.mp (isPPT_evaluatorSim (G := G) (encFn := encFn) hinLen hΦ hS)
  have hto : ComputableInPolyTime
      (fun x : SimInput (oneSidedFamily G) {1} =>
        (⟨x.secParam, x.desc, x.inputs, x.outputs⟩ : SimInput (family G) {1}))
      (encSimInput (oneSidedEncoding G encFn)) (encSimInput (encoding G encFn)) :=
    .of_eq fun _ => rfl
  refine isPPTOn_iff_encoded.mpr ((htwo.preprocess hto).congr fun ⟨n, c, xs, ys⟩ => ?_)
  simp only [evaluatorSim, oneSidedEvaluatorSim, ← PMF.bind_pure_comp, pmf_norm]
  refine congrArg _ (funext fun V => congrArg PMF.pure ?_)
  simp only [encDPi_apply]
  refine congrArg (encPi encBits) (funext fun ⟨j, hj⟩ => ?_)
  obtain rfl := Finset.mem_singleton.mp hj
  rfl

/-- The words of the environment's guessing input that the reduction's guess stage writes, laid
out as `encGuessInputFields`: the security parameter, the public parameters, the environment's
state, the one-entry table of the evaluator's view words and the table of the two outputs. -/
private noncomputable def guessWords (k : ℕ) (st : ReductionState G) (V : Option PrvView) :
    ℕ × Params G × List Bool × List Bool × List Bool :=
  (k, st.params, st.envState,
    evaluatorSimWord (G.inLen st.params.fn) st.params.garblerLen
      ((st.evaluatorInput ++ List.replicate st.params.evaluatorLen false).take
        st.params.evaluatorLen) (V.getD ⟨[], [], []⟩),
    encPi encBits fun _ : Fin 2 => st.output)

/-- **The reduction is PPT** whenever the environment `Z` is PPT for `encoding G encFn`, the public
parameters are drawn by a PPT sampler `samp`, and `G` reads input lengths (`hinLen`) and evaluates
`ev` (`hev`) in polynomial time. -/
theorem isPPT_evaluatorToPrvSim {encFn : Fn ↪ List Bool} {samp : ℕ → ProbComp (Params G)}
    {Z : Environment (family G) {1}} (hinLen : ComputableInPolyTime G.inLen encFn encUnary)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    (hsamp : IsPPTOn encUnary (encParams encFn) samp) (hZ : Z.IsPPT (encoding G encFn)) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool
      (encReductionState (G := G) encFn) (evaluatorToPrvSim samp Z) where
  choose := by
    let E₁ := encPair (encPair encUnary encUnit) (encParams (G := G) encFn)
    let E₂ := encPair E₁ (encPair (encDPi (encoding G encFn).input.enc) encBits)
    have hfn : ComputableInPolyTime (fun q : ((ℕ × Unit) × Params G) ×
        (((i : Fin 2) → List Bool) × List Bool) => q.1.2.fn) E₂ encFn :=
      encParams_fn_polyTime ((ComputableInPolyTime.snd _ _).comp (.fst _ _))
    have htable : ComputableInPolyTime (fun q : ((ℕ × Unit) × Params G) ×
        (((i : Fin 2) → List Bool) × List Bool) => q.2.1) E₂
        (encDPi (encoding G encFn).input.enc) :=
      (ComputableInPolyTime.fst _ _).comp (.snd _ _)
    have hx₀ := (ComputableInPolyTime.dpi_apply (encoding G encFn).input.enc 0).comp htable
    have hx₁ := (ComputableInPolyTime.dpi_apply (encoding G encFn).input.enc 1).comp htable
    have happ := ComputableInPolyTime.bitsAppend hx₀ hx₁
    have hout : ComputableInPolyTime (fun q : ((ℕ × Unit) × Params G) ×
        (((i : Fin 2) → List Bool) × List Bool) =>
          ((⟨q.1.2.fn, q.2.1 0 ++ q.2.1 1⟩ : Query Fn),
            (⟨q.1.2, q.2.2, q.2.1 1, G.ev q.1.2.fn (q.2.1 0 ++ q.2.1 1)⟩ : ReductionState G)))
        E₂ (encPair (encQuery Fn encFn) (encReductionState (G := G) encFn)) :=
      (encQuery_mk_polyTime Fn encFn hfn happ).prod (encReductionState_mk_polyTime encFn
        ((ComputableInPolyTime.snd _ _).comp (.fst _ _))
        ((ComputableInPolyTime.snd _ _).comp (.snd _ _)) hx₁
        (hev.comp (hfn.prod happ)))
    have hprog : IsPPTOn (encPair encUnary encUnit)
        (encPair (encQuery Fn encFn) (encReductionState (G := G) encFn)) (fun x : ℕ × Unit => do
          let c ← samp x.1
          let cw : ((i : Fin 2) → List Bool) × List Bool ←
            (fun ch => ((fun i => (encoding G encFn).input.rep x.1 c i (ch.inputs i)),
              ch.state)) <$> Z.choose x.1 c
          pure ((⟨c.fn, cw.1 0 ++ cw.1 1⟩ : Query Fn),
            (⟨c, cw.2, cw.1 1, G.ev c.fn (cw.1 0 ++ cw.1 1)⟩ : ReductionState G))) := by
      refine IsPPTOn.bind_with (hsamp.preprocess (prepare := fun x : ℕ × Unit => x.1)
        (.fst _ _)) ?_
      refine IsPPTOn.bind_with (hZ.choose.preprocess
        (prepare := fun p : (ℕ × Unit) × Params G => (p.1.1, p.2))
        (((ComputableInPolyTime.fst _ _).comp (.fst _ _)).prod (.snd _ _))) ?_
      exact hout.isPPTOn
    refine hprog.congr fun x => ?_
    simp only [evaluatorToPrvSim, pmf_norm]
    rfl
  guess := by
    obtain ⟨W, hW, hWeq⟩ := hZ.guess.exists_bool_factor (encGuessInput_apply (encoding G encFn))
    let E := encPair encUnary (encPair (encReductionState (G := G) encFn) (encOption encPrvView))
    have hk : ComputableInPolyTime (fun p : ℕ × ReductionState G × Option PrvView => p.1) E
        encUnary := .fst _ _
    have hst : ComputableInPolyTime (fun p : ℕ × ReductionState G × Option PrvView => p.2.1) E
        (encReductionState (G := G) encFn) := (ComputableInPolyTime.fst _ _).comp (.snd _ _)
    have hV : ComputableInPolyTime (fun p : ℕ × ReductionState G × Option PrvView => p.2.2) E
        (encOption encPrvView) := (ComputableInPolyTime.snd _ _).comp (.snd _ _)
    have hc := encReductionState_params_polyTime encFn hst
    have hfn := encParams_fn_polyTime hc
    have hN := hinLen.comp hfn
    have hg := encParams_garblerLen_polyTime hc
    have hw := encReductionState_evaluatorInput_polyTime encFn hst
    have hout := encReductionState_output_polyTime encFn hst
    have hx₁ : ComputableInPolyTime (fun p : ℕ × ReductionState G × Option PrvView =>
        (p.2.1.evaluatorInput ++ List.replicate p.2.1.params.evaluatorLen false).take
          p.2.1.params.evaluatorLen) E encBits := by
      simp only [Params.evaluatorLen]
      fun_prop
    have hview : ComputableInPolyTime (fun p : ℕ × ReductionState G × Option PrvView =>
        p.2.2.getD ⟨[], [], []⟩) E encPrvView := by
      fun_prop
    have hwords : ComputableInPolyTime (fun p : ℕ × ReductionState G × Option PrvView =>
        guessWords p.1 p.2.1 p.2.2) E (encGuessInputFields (encoding G encFn)) :=
      hk.prod (hc.prod ((encReductionState_envState_polyTime encFn hst).prod
        ((ComputableInPolyTime.pi fun _ => (viewWordsOfPrvView_polyTime hN hg hx₁
          hview).encoding_comp).encoding_comp.prod
          (ComputableInPolyTime.pi fun _ => hout).encoding_comp)))
    refine (hW.preprocess hwords).congr fun ⟨k, st, V⟩ => ?_
    refine congrArg ProbComp.eval
      (Eq.trans (congrArg W ?_) (hWeq ⟨k, st.params, st.envState, _, _⟩).symm)
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl)))
    refine Eq.trans ?_ ((encoding G encFn).view.encCoalition_singleton k st.params 1 _).symm
    refine congrArg (encPi encBits) (funext fun _ => congrArg encEvaluatorViewWords ?_)
    rw [← BitString.ofFn_ofList_eq_take]
    exact (evaluatorViewWords_viewOfPrvView st.params _ _).symm

private theorem isPPT_liftEvaluatorEnv {encFn : Fn ↪ List Bool}
    {Z : Environment (oneSidedFamily G) {1}} (hZ : Z.IsPPT (oneSidedEncoding G encFn)) :
    (liftEvaluatorEnv Z).IsPPT (encoding G encFn) where
  choose := hZ.choose.congr fun ⟨n, d⟩ => by
    change _ = ProbComp.eval ((fun c : InputChoice (family G) n d =>
      ((fun i => (encoding G encFn).input.rep n d i (c.inputs i)), c.state)) <$>
        (fun ch => ⟨ch.inputs, ch.state⟩) <$> Z.choose n d)
    simp only [ProbComp.eval_map, PMF.map_comp]
    rfl
  guess := by
    let E₁ := oneSidedEncoding G encFn
    let E₂ := encoding G encFn
    obtain ⟨W, hW, hWeq⟩ := hZ.guess.exists_bool_factor (encGuessInput_apply (I := {1}) E₁)
    have hn := encGuessInput_secParam_polyTime E₂ (I := {1}) .id'
    have hd := encGuessInput_desc_polyTime E₂ (I := {1}) .id'
    have hst := encGuessInput_state_polyTime E₂ (I := {1}) .id'
    have hviews := encGuessInput_views_polyTime E₂ (I := {1}) .id'
    have houtAll := encGuessInput_outputs_polyTime E₂ (I := {1}) .id'
    have hy₁ : ComputableInPolyTime (fun y : GuessInput (family G) {1} => y.outputs 1)
        (encGuessInput E₂) encBits :=
      (ComputableInPolyTime.dpi_apply E₂.output.enc 1).comp (houtAll.of_enc_eq fun _ => rfl)
    have hout : ComputableInPolyTime
        (fun y : GuessInput (family G) {1} =>
          E₁.output.encAll y.secParam y.desc (oneSidedOutputs (y.outputs 1)))
        (encGuessInput E₂) encBits := by
      refine (ComputableInPolyTime.dpi (enc := E₁.output.enc) fun i => ?_).encoding_comp
      refine Fin.cases (motive := fun i => ComputableInPolyTime
          (fun y : GuessInput (family G) {1} => oneSidedOutputs (y.outputs 1) i)
          (encGuessInput E₂) (E₁.output.enc i))
        (ComputableInPolyTime.const []) (fun _ => hy₁) i
    have hprep : ComputableInPolyTime
        (fun y : GuessInput (family G) {1} =>
          (y.secParam, (y.desc : Params G), y.state,
            E₂.view.encCoalition y.secParam y.desc {1} y.views,
            E₁.output.encAll y.secParam y.desc (oneSidedOutputs (y.outputs 1))))
        (encGuessInput E₂) (encGuessInputFields (P := oneSidedFamily G) E₁) :=
      hn.prod (hd.prod (hst.prod (hviews.prod hout)))
    refine (hW.preprocess hprep).congr fun y => ?_
    refine congrArg ProbComp.eval
      (Eq.trans (congrArg W ?_) (hWeq ⟨y.secParam, y.desc, y.state, _, _⟩).symm)
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl)))
    simp only [PartyEncoding.encCoalition, Function.Embedding.coeFn_mk, encDPi_apply]
    refine congrArg (encPi encBits) (funext fun ⟨j, hj⟩ => ?_)
    obtain rfl := Finset.mem_singleton.mp hj
    rfl

/-- **The one-sided reduction is PPT** whenever the environment `Z` is PPT for
`oneSidedEncoding G encFn`, the public parameters are drawn by a PPT sampler `samp`, and `G` reads
input lengths (`hinLen`) and evaluates `ev` (`hev`) in polynomial time. -/
theorem isPPT_oneSidedEvaluatorToPrvSim {encFn : Fn ↪ List Bool} {samp : ℕ → ProbComp (Params G)}
    {Z : Environment (oneSidedFamily G) {1}} (hinLen : ComputableInPolyTime G.inLen encFn encUnary)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    (hsamp : IsPPTOn encUnary (encParams encFn) samp) (hZ : Z.IsPPT (oneSidedEncoding G encFn)) :
    TwoStage.IsPPT encUnit (encQuery Fn encFn) (encOption encPrvView) encBool
      (encReductionState (G := G) encFn) (oneSidedEvaluatorToPrvSim samp Z) := by
  have h := isPPT_evaluatorToPrvSim hinLen hev hsamp (isPPT_liftEvaluatorEnv hZ)
  refine ⟨h.choose.congr fun ⟨k, ()⟩ => ?_, h.guess⟩
  simp only [evaluatorToPrvSim, oneSidedEvaluatorToPrvSim, liftEvaluatorEnv, pmf_norm]

/-! ### Empty and full coalitions of `oneSidedFamily` -/

private theorem idealJoint_oneSided_empty (hproj : G.encode = projectiveEncode)
    (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i) :
    ProbComp.eval (idealJoint (oneSidedFunctionality G c) ∅
        (SimulatorFamily.empty (oneSidedFamily G) n c) x) =
      (oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) ∅ x := by
  rw [realJoint_oneSided, ← PMF.bind_pure_comp]
  simp only [idealJoint, oneSidedFunctionality, Functionality.ofDeterministic,
    SimulatorFamily.empty, ProbComp.eval_bind, ProbComp.eval_pure, PMF.pure_bind]
  symm
  refine (Probability.PMF.bind_congr_on_support (BitString.uniformList (G.coins n c.fn)) _
    (fun _ => PMF.pure ((fun i : (∅ : Finset (Fin 2)) => isEmptyElim i),
      oneSidedOutputs (G.ev c.fn (circuitInput x)))) fun coins hcoins => ?_).trans
    (PMF.bind_const _ _)
  simp only [Function.comp_apply,
    runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins)]
  exact congrArg PMF.pure (Prod.ext (funext fun i => nomatch i.2) rfl)

/-- Simulator for `I = Finset.univ` (both parties corrupted) in `oneSidedFamily`: draws `G.coins`
fair coins and constructs both parties' exact views from their inputs. -/
private noncomputable def oneSidedFullSim (G : Scheme Fn) :
    SimulatorFamily (oneSidedFamily G) Finset.univ :=
  fun n c xI _ => do
    let coins ← BitString.sampleList (G.coins n c.fn)
    return Finset.univ.restrict (oneSidedViews G n c (fun i => xI ⟨i, Finset.mem_univ i⟩) coins)

private theorem idealJoint_oneSidedFullSim (hproj : G.encode = projectiveEncode)
    (hcorrect : G.Correct) {n : ℕ} (hn : 0 < n) (c : Params G) (x : (i : Fin 2) → Input c i) :
    ProbComp.eval
        (idealJoint (oneSidedFunctionality G c) Finset.univ (oneSidedFullSim G n c) x) =
      (oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool))
        Finset.univ x := by
  rw [realJoint_oneSided]
  simp only [pmf_norm, idealJoint, oneSidedFunctionality, Functionality.ofDeterministic,
    oneSidedFullSim, BitString.eval_sampleList]
  rw [← PMF.bind_pure_comp]
  refine Probability.PMF.bind_congr_on_support _ _ _ fun coins hcoins => ?_
  simp only [Function.comp_apply,
    runOutput_eq hproj hcorrect hn c x (BitString.mem_support_uniformList_iff.mp hcoins)]
  rfl

private theorem isPPT_oneSidedFullSim {encFn : Fn ↪ List Bool}
    (heff : G.IsEfficient encFn) (hproj : G.encode = projectiveEncode) :
    (oneSidedFullSim G).IsPPT (oneSidedEncoding G encFn) := by
  let E := oneSidedEncoding G encFn
  let P := encPair (encSimInput (I := Finset.univ) E) encBits
  have hnSim := encSimInput_secParam_polyTime E (I := Finset.univ) .id'
  have hcSim := encSimInput_desc_polyTime E (I := Finset.univ) .id'
  have hfnSim := encParams_fn_polyTime hcSim
  have hcount : ComputableInPolyTime
      (fun x : SimInput (oneSidedFamily G) Finset.univ => G.coins x.secParam x.desc.fn)
      (encSimInput E) encUnary :=
    heff.coins.comp (hnSim.prod hfnSim)
  have hp1 : ComputableInPolyTime
      (fun p : SimInput (oneSidedFamily G) Finset.univ × List Bool => p.1) P (encSimInput E) :=
    .fst _ _
  have hcoinsArg : ComputableInPolyTime
      (fun p : SimInput (oneSidedFamily G) Finset.univ × List Bool => p.2) P encBits := .snd _ _
  have hn := hnSim.comp hp1
  have hc := hcSim.comp hp1
  have hfn := hfnSim.comp hp1
  have hx₀ := (E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E .id')
    (⟨0, Finset.mem_univ 0⟩ : (Finset.univ : Finset (Fin 2)))).comp hp1
  have hx₁ := (E.input.encCoalition_apply_polyTime (encSimInput_inputs_polyTime E .id')
    (⟨1, Finset.mem_univ 1⟩ : (Finset.univ : Finset (Fin 2)))).comp hp1
  have hgb := heff.gb.comp (hn.prod (hfn.prod hcoinsArg))
  have hX := heff.encode.comp ((Scheme.encGarbled_encInfo_polyTime hgb).prod (hx₀.bitsAppend hx₁))
  have hprv := encPrvView_mk_polyTime (Scheme.encGarbled_fn_polyTime hgb) hX
    (Scheme.encGarbled_decInfo_polyTime hgb)
  have heval := viewWordsOfPrvView_polyTime (heff.inLen.comp hfn)
    (encParams_garblerLen_polyTime hc) hx₁ hprv
  have hgarb := encOneSidedGarblerViewWords_mk_polyTime hx₀ hcoinsArg
  have hreps : ComputableInPolyTime
      (fun (p : SimInput (oneSidedFamily G) Finset.univ × List Bool)
          (i : (Finset.univ : Finset (Fin 2))) =>
        Fin.cases (motive := fun j => E.view.Rep j)
          (OneSidedGarblerViewWords.mk
            (List.ofFn (p.1.inputs ⟨0, Finset.mem_univ 0⟩)) p.2)
          (fun _ => viewWordsOfPrvView (G.inLen p.1.desc.fn) p.1.desc.garblerLen
            (List.ofFn (p.1.inputs ⟨1, Finset.mem_univ 1⟩))
            ⟨(G.gb p.1.secParam p.1.desc.fn p.2).fn,
              G.encode (G.gb p.1.secParam p.1.desc.fn p.2).encInfo
                (List.ofFn (p.1.inputs ⟨0, Finset.mem_univ 0⟩) ++
                  List.ofFn (p.1.inputs ⟨1, Finset.mem_univ 1⟩)),
              (G.gb p.1.secParam p.1.desc.fn p.2).decInfo⟩) i.1)
      P (encDPi fun i : (Finset.univ : Finset (Fin 2)) => E.view.enc i) := by
    refine ComputableInPolyTime.dpi fun ⟨j, hj⟩ => ?_
    fin_cases j
    · exact hgarb
    · exact heval
  refine (IsPPTOn.of_seeded hcount hreps).congr fun ⟨n, c, xs, _⟩ => ?_
  simp only [oneSidedFullSim, ← PMF.bind_pure_comp, pmf_norm]
  congr 1
  funext coins
  congr 1
  funext ⟨j, hj⟩
  fin_cases j
  · rfl
  · exact (oneSidedEvaluatorViewWords_viewOfPrvView c (xs ⟨1, Finset.mem_univ 1⟩) _).symm.trans
      (congrArg oneSidedEvaluatorViewWords
        (oneSidedViewOfPrvView_gb hproj n c (fun i => xs ⟨i, Finset.mem_univ i⟩) coins))

/-! ### Security -/

/-- **The one-sided reduction is exact**: at every parameter `n ≥ 1`, the advantage of an
environment `Z` between the real game of `oneSidedFamily` and the ideal game with
`oneSidedEvaluatorSim G Φ S` equals the `prv.sim` advantage of `oneSidedEvaluatorToPrvSim samp Z`
against `S n`, when `G` is correct and its encoding is `projectiveEncode`. -/
theorem advantage_oneSidedEvaluator_eq (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (samp : ℕ → ProbComp (Params G)) (Z : Environment (oneSidedFamily G) {1})
    (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) :
    Game.advantage ((oneSidedFamily G).realGame (fun n => ProbComp.eval (samp n)) {1} Z n)
        ((oneSidedFamily G).idealGame (fun n => ProbComp.eval (samp n)) {1}
          (oneSidedEvaluatorSim G Φ S) Z n) =
      prvSimAdvantage G Φ n (S n) (oneSidedEvaluatorToPrvSim samp Z n) := by
  rw [realGame_oneSidedEvaluator_eq hproj hcorrect hn samp Z Φ S,
    idealGame_oneSidedEvaluator_eq samp Z Φ S n, Game.advantage_comm]
  rfl

/-- **The reduction is exact**: at every parameter `n ≥ 1`, the advantage of an environment `Z`
between the real game and the ideal game with `evaluatorSim G Φ S` equals the `prv.sim` advantage
of the reduction `evaluatorToPrvSim samp Z` against `S n`, when `G` is correct and its encoding is
`projectiveEncode`. -/
theorem advantage_evaluator_eq (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    {n : ℕ} (hn : 0 < n) (samp : ℕ → ProbComp (Params G)) (Z : Environment (family G) {1})
    (Φ : SideInfo Fn Λ) (S : ℕ → PrvSimulator Λ) :
    Game.advantage ((family G).realGame (fun n => ProbComp.eval (samp n)) {1} Z n)
        ((family G).idealGame (fun n => ProbComp.eval (samp n)) {1} (evaluatorSim G Φ S) Z n) =
      prvSimAdvantage G Φ n (S n) (evaluatorToPrvSim samp Z n) := by
  rw [realGame_evaluator_eq hproj hcorrect hn samp Z Φ S,
    idealGame_evaluator_eq samp Z Φ S n, Game.advantage_comm]
  rfl

/-- Perfect privacy from `n = 1` on with a PPT simulator gives `SemiHonestSecure` for
`oneSidedFamily`. -/
private theorem oneSided_semiHonestSecure_of_pos_perfect {setup : ℕ → PMF (Params G)}
    {I : Finset (Fin 2)} {encFn : Fn ↪ List Bool}
    {S : SimulatorFamily (oneSidedFamily G) I} (hS : S.IsPPT (oneSidedEncoding G encFn))
    (h : ∀ {n : ℕ}, 0 < n → ∀ c x,
      ProbComp.eval (idealJoint (oneSidedFunctionality G c) I (S n c) x) =
        (oneSidedProtocol G n c).realJoint (batchOTWorld c.evaluatorLen (List Bool)) I x) :
    (oneSidedFamily G).SemiHonestSecure setup I (oneSidedEncoding G encFn) := by
  refine ⟨S, hS, fun Z _ => ?_⟩
  refine negligible_of_eventually_le negligible_zero ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  have heq : (oneSidedFamily G).realGame setup I Z n =
      (oneSidedFamily G).idealGame setup I S Z n := by
    simp only [ProtocolFamily.realGame, ProtocolFamily.idealGame, h hn]
  rw [heq, Game.advantage_self]

/-- Unconditional semi-honest security of `oneSidedFamily` for `I = ∅` (no corrupted parties) from
correctness at `n ≥ 1`. -/
private theorem hybridSemiHonestSecure_oneSided_empty {encFn : Fn ↪ List Bool}
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct) (setup : ℕ → PMF (Params G)) :
    (oneSidedFamily G).SemiHonestSecure setup ∅ (oneSidedEncoding G encFn) :=
  oneSided_semiHonestSecure_of_pos_perfect (SimulatorFamily.isPPT_empty _)
    (fun hn c x => idealJoint_oneSided_empty hproj hcorrect hn c x)

/-- Unconditional semi-honest security of `oneSidedFamily` for `I = Finset.univ` (both parties
corrupted) from correctness at `n ≥ 1` and polynomial-time scheme algorithms. -/
private theorem hybridSemiHonestSecure_oneSided_univ {encFn : Fn ↪ List Bool}
    (heff : G.IsEfficient encFn) (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    (setup : ℕ → PMF (Params G)) :
    (oneSidedFamily G).SemiHonestSecure setup Finset.univ (oneSidedEncoding G encFn) :=
  oneSided_semiHonestSecure_of_pos_perfect (isPPT_oneSidedFullSim heff hproj)
    (fun hn c x => idealJoint_oneSidedFullSim hproj hcorrect hn c x)

end Cslib.Crypto.Protocols.MPC.Yao

namespace Cslib.Crypto.Garbling

open Protocols.MPC Probability Turing.MultiTapeTM

variable {Fn Λ : Type} {G : Scheme Fn}

/-- Step in the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), under the novel
assumption `Scheme.PrvSimSecureUniversal`: semi-honest security of `Yao.oneSidedFamily G` against a
corrupted evaluator, towards Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15; Case
2, pp. 18–19) and Theorem 14 of [BellareHoangRogaway2012] (§7.1, p. 35), not those plain-model
theorems, which compose with a concrete semi-honest 1-out-of-2 oblivious-transfer protocol. When
`G` satisfies `Scheme.PrvSimSecureUniversal` for side information `Φ` computed in polynomial time,
is correct, has encoding `projectiveEncode`, and reads input lengths and evaluates `ev` in
polynomial time, then for public parameters drawn by any PPT sampler the PPT simulator family
`Yao.oneSidedEvaluatorSim G Φ S` makes the real and ideal games indistinguishable for every PPT
environment through the certified reduction `Yao.oneSidedEvaluatorToPrvSim`
(`Yao.advantage_oneSidedEvaluator_eq`, `Yao.isPPT_oneSidedEvaluatorToPrvSim`). -/
theorem Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure_evaluator
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    {Φ : SideInfo Fn Λ} (hG : G.PrvSimSecureUniversal Φ encFn encΛ)
    (hinLen : ComputableInPolyTime G.inLen encFn encUnary)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    (hΦ : ComputableInPolyTime Φ.phi encFn encΛ) {samp : ℕ → ProbComp (Yao.Params G)}
    (hsamp : IsPPTOn encUnary (Yao.encParams encFn) samp) :
    (Yao.oneSidedFamily G).SemiHonestSecure (fun n => ProbComp.eval (samp n)) {1}
      (Yao.oneSidedEncoding G encFn) := by
  obtain ⟨S, hS, hsec⟩ := hG
  refine ⟨Yao.oneSidedEvaluatorSim G Φ S, Yao.isPPT_oneSidedEvaluatorSim hinLen hΦ hS,
    fun Z hZ => ?_⟩
  refine negligible_of_eventually_le (hsec _ (Yao.encReductionState (G := G) encFn) _
    (Yao.isPPT_oneSidedEvaluatorToPrvSim hinLen hev hsamp hZ)) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [Yao.advantage_oneSidedEvaluator_eq hproj hcorrect hn samp Z Φ S]

/-- Step in the ideal `batchOTWorld` oblivious-transfer hybrid model (#6045), under the novel
assumption `Scheme.PrvSimSecureUniversal`: semi-honest security of `Yao.oneSidedFamily G` across
every static coalition `I : Finset (Fin 2)`, towards Theorem 7 of [LindellPinkas2009] (ePrint
2004/175, §4.2, p. 15) and Theorem 14 of [BellareHoangRogaway2012] (§7.1, p. 35), not those
plain-model theorems, which compose with a concrete semi-honest 1-out-of-2 oblivious-transfer
protocol. The oblivious transfers are the ideal `batchOTWorld` (`batchOTSpec`), party `0` outputs
`[]` and party `1` outputs `G.ev fn x` (as in [BellareHoangRogaway2012], §7.1, Fig. 16, p. 34), and
the module documentation lists the other deviations (uniform environments that choose the inputs, a
setup law, the scheme as a parameter). Under `Scheme.PrvSimSecureUniversal`, `Scheme.IsEfficient`,
`G.encode = projectiveEncode`, `G.Correct`, polynomial-time `Φ.phi`, and a PPT public-parameter
sampler `samp`, `Yao.oneSidedFamily G` satisfies `ProtocolFamily.SemiHonestSecure` at every static
coalition `I`:
* `I = ∅` (no corruption): exact simulation from `n = 1` on;
* `I = {0}` (corrupted garbler): `Yao.hybridSemiHonestSecure_oneSided_garbler` (no computational
  assumption);
* `I = {1}` (corrupted evaluator):
  `Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure_evaluator` via the certified
  reduction `Yao.oneSidedEvaluatorToPrvSim`;
* `I = Finset.univ` (both parties corrupted): exact simulation from `n = 1` on. -/
theorem Scheme.PrvSimSecureUniversal.yaoOneSidedHybridSemiHonestSecure {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {Φ : SideInfo Fn Λ} (hG : G.PrvSimSecureUniversal Φ encFn encΛ)
    (heff : G.IsEfficient encFn) (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    (hΦ : ComputableInPolyTime Φ.phi encFn encΛ) {samp : ℕ → ProbComp (Yao.Params G)}
    (hsamp : IsPPTOn encUnary (Yao.encParams encFn) samp) (I : Finset (Fin 2)) :
    (Yao.oneSidedFamily G).SemiHonestSecure (fun n => ProbComp.eval (samp n)) I
      (Yao.oneSidedEncoding G encFn) := by
  have hcases : ∀ J : Finset (Fin 2), J = ∅ ∨ J = {0} ∨ J = {1} ∨ J = Finset.univ := by decide
  rcases hcases I with rfl | rfl | rfl | rfl
  · exact Yao.hybridSemiHonestSecure_oneSided_empty hproj hcorrect _
  · exact Yao.hybridSemiHonestSecure_oneSided_garbler heff.coins hproj hcorrect _
  · exact hG.yaoOneSidedHybridSemiHonestSecure_evaluator heff.inLen heff.ev hproj hcorrect hΦ hsamp
  · exact Yao.hybridSemiHonestSecure_oneSided_univ heff hproj hcorrect _

/-- Semi-honest security of `Yao.family G` against a corrupted evaluator in the ideal `batchOTWorld`
oblivious-transfer hybrid model (#6045), under the novel assumption `Scheme.PrvSimSecureUniversal`:
a step towards Theorem 7 of [LindellPinkas2009] (ePrint 2004/175, §4.2, p. 15), not plain-model
Theorem 7 or its Case 2 (pp. 18–19), which compose with a concrete semi-honest 1-out-of-2
oblivious-transfer protocol. Case 2 first replaces the oblivious-transfer protocol by its simulator,
then the real garbled circuit by a fake one; with the ideal `batchOTWorld` (`batchOTSpec`) the first
step is empty, and the second is the `prv.sim` security of `G`. When `G` is `prv.sim` secure with
one simulator `S` for every adversary (`Scheme.PrvSimSecureUniversal`) for side information `Φ`
computed in polynomial time, `G` is correct, its encoding is `projectiveEncode`, and it reads input
lengths and evaluates `ev` in polynomial time, then for public parameters drawn by any PPT sampler
the PPT simulator family `Yao.evaluatorSim G Φ S` makes the real and ideal games indistinguishable
for every PPT environment: from `n = 1` on, an environment's advantage is the `prv.sim` advantage
of the certified reduction `Yao.evaluatorToPrvSim` (`Yao.advantage_evaluator_eq`,
`Yao.isPPT_evaluatorToPrvSim`). The other deviations are those of the module documentation. -/
theorem Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure_evaluator
    {encFn : Fn ↪ List Bool} {encΛ : Λ ↪ List Bool}
    {Φ : SideInfo Fn Λ} (hG : G.PrvSimSecureUniversal Φ encFn encΛ)
    (hinLen : ComputableInPolyTime G.inLen encFn encUnary)
    (hev : ComputableInPolyTime (fun (f, x) => G.ev f x) (encPair encFn encBits) encBits)
    (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    (hΦ : ComputableInPolyTime Φ.phi encFn encΛ) {samp : ℕ → ProbComp (Yao.Params G)}
    (hsamp : IsPPTOn encUnary (Yao.encParams encFn) samp) :
    (Yao.family G).SemiHonestSecure (fun n => ProbComp.eval (samp n)) {1}
      (Yao.encoding G encFn) := by
  obtain ⟨S, hS, hsec⟩ := hG
  refine ⟨Yao.evaluatorSim G Φ S, Yao.isPPT_evaluatorSim hinLen hΦ hS, fun Z hZ => ?_⟩
  refine negligible_of_eventually_le (hsec _ (Yao.encReductionState (G := G) encFn) _
    (Yao.isPPT_evaluatorToPrvSim hinLen hev hsamp hZ)) ?_
  filter_upwards [Filter.eventually_gt_atTop 0] with n hn
  rw [Yao.advantage_evaluator_eq hproj hcorrect hn samp Z Φ S]

/-- Semi-honest security of `Yao.family G` against the corruption of either party in the ideal
`batchOTWorld` oblivious-transfer hybrid model (#6045), under the novel assumption
`Scheme.PrvSimSecureUniversal`: a step towards Theorem 7 of [LindellPinkas2009] (ePrint 2004/175,
§4.2, p. 15), not plain-model Theorem 7, which composes with a concrete semi-honest 1-out-of-2
oblivious-transfer protocol. The oblivious transfers are the ideal `batchOTWorld` (`batchOTSpec`),
and the module documentation lists the other deviations (uniform environments that choose the
inputs, a setup law, the scheme as a parameter). The garbling scheme `G` is `prv.sim` secure with
one simulator for every adversary (`Scheme.PrvSimSecureUniversal`) for side information `Φ` computed
in polynomial time; it has polynomial-time algorithms (`Scheme.IsEfficient`), it is correct, and its
encoding is `projectiveEncode`; and the public parameters are drawn by a PPT sampler `samp`. Then
`Yao.family G` is semi-honest secure, in the sense of `ProtocolFamily.SemiHonestSecure`, against
the corruption of the garbler (`Yao.hybridSemiHonestSecure_garbler`, which needs no assumption) and
of the evaluator (`Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure_evaluator`, through the
certified reduction `Yao.evaluatorToPrvSim`). The modular form over a garbling scheme follows
[BellareHoangRogaway2012], §7.1 (Theorem 14, p. 35), whose quantifiers are `∀ B ∃ S` on both
sides. -/
theorem Scheme.PrvSimSecureUniversal.yaoHybridSemiHonestSecure {encFn : Fn ↪ List Bool}
    {encΛ : Λ ↪ List Bool} {Φ : SideInfo Fn Λ} (hG : G.PrvSimSecureUniversal Φ encFn encΛ)
    (heff : G.IsEfficient encFn) (hproj : G.encode = projectiveEncode) (hcorrect : G.Correct)
    (hΦ : ComputableInPolyTime Φ.phi encFn encΛ) {samp : ℕ → ProbComp (Yao.Params G)}
    (hsamp : IsPPTOn encUnary (Yao.encParams encFn) samp) (i : Fin 2) :
    (Yao.family G).SemiHonestSecure (fun n => ProbComp.eval (samp n)) {i}
      (Yao.encoding G encFn) := by
  fin_cases i
  · exact Yao.hybridSemiHonestSecure_garbler heff.coins hproj hcorrect _
  · exact hG.yaoHybridSemiHonestSecure_evaluator heff.inLen heff.ev hproj hcorrect hΦ hsamp

end Cslib.Crypto.Garbling
