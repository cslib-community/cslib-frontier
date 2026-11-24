/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Probabilistic.Parameter
public import CslibFrontier.Crypto.Computational.TwoStage
public import CslibFrontier.Crypto.Game.CloseTo
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
public import CslibFrontier.Languages.Probabilistic.Lift
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.StatisticalDistance.Product

/-!
# Computational special honest-verifier zero knowledge

Boneh and Shoup's computational relaxation of special HVZK ([BonehShoup2023], Section 20.4.2,
Attack Game 20.4 and Definition 20.6, p. 840) for an indexed family of Sigma protocols `P i` over a
parameter distribution `setup : ℕ → PMF I` ([BonehShoup2023], Section 2.3.4).

Attack Game 20.4 is first stated at one index. `chvzkExperiment R conv A` runs a two-stage
adversary `A : TwoStage Unit (X × Y) (T × C × Z) Bool σ`: it chooses a witness-statement pair
`(x, y)` and a saved state; if `R x y` fails the experiment outputs `false`, and otherwise it
samples a conversation from `conv x y` and outputs `A`'s guess on it.

* **Experiment 0** uses the honest conversation `(P i).conversation x y`.
* **Experiment 1** uses `simulatedConversation sim i y`: sample a uniform challenge `c` and run the
  typed simulator `sim i y c` without `x`.

The games `chvzkRealGame` and `chvzkSimGame` draw `i ← setup n` and run the experiment at `i` with
the adversary `A n i` of a family `A : CHVZKAdversary I X Y T C Z σ`. Adversaries receive and
return typed values; their efficiency is stated on encodings by `CHVZKAdversary.IsPPT`. The choice
stage writes `((encW i x, enc.statement i y), state)`, the layout of the word-level adversaries
when `σ := List Bool`. The guessing stage reads the record `CHVZKGuessInput`, encoded by
`encCHVZKGuessInput` as the unary security parameter, the state, the index and the encoded
commitment, challenge and response.

`ComputationalSpecialHVZK P R enc encW setup sim δ` bundles, for a typed simulator family
`sim : Simulator I Y T C Z`:

1. Uniform strict PPT admissibility of `sim` (`Simulator.IsPPT`), the only place where its
   encodings appear.
2. Acceptance on every `(i, y, c)` with probability at least `1 - δ i` (exact Definition 20.6
   acceptance when `δ = 0`; relaxed by `δ` when a strict PPT fair-coin simulator approximates a
   non-dyadic distribution).
3. Negligible distinguishing advantage between `chvzkRealGame` and `chvzkSimGame` for every state
   type, state encoding and uniform strict PPT `CHVZKAdversary`.

Every `EfficientSpecialHVZK` protocol whose realization error `δ` is bounded along `setup` by a
negligible function satisfies `ComputationalSpecialHVZK`, in fact against arbitrary, even
computationally unbounded adversaries at each index
(`SimulatorRealizedBy.advantage_chvzkExperiment_le`,
`EfficientSpecialHVZK.exists_computationalSpecialHVZK`). As in `EfficientSpecialHVZK`, `δ` is an
explicit parameter of `ComputationalSpecialHVZK` rather than a bundled `Negligible` condition on the
acceptance error alone; exact Definition 20.6 acceptance corresponds to `δ = fun _ => 0` (which
Schnorr's simulator achieves in `PrimeOrderGroupFamily.computationalSpecialHVZK_schnorr`).

When an ideal-sampling `PMF` prover `P` is replaced by a fair-coin prover `P'` whose honest
transcripts are within statistical distance `ε` of `P`'s on valid pairs, pointwise transcript
closeness (`SimulatorRealizedBy.closeTo_transcript_of_closeTo`), Attack Game 20.4 advantage bounds
(`advantage_chvzkRealGame_le_of_closeTo_transcript`,
`SimulatorRealizedBy.advantage_chvzkGame_le_of_closeTo_transcript`), and `ComputationalSpecialHVZK`
(`ComputationalSpecialHVZK.of_closeTo_transcript`) transfer without requiring `P` and `P'` to share
a private-state type.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.chvzkExperiment`: Attack Game 20.4 at one index, for a
  given conversation law.
* `Cslib.Crypto.Protocols.SigmaProtocol.CHVZKAdversary`,
  `Cslib.Crypto.Protocols.SigmaProtocol.CHVZKGuessInput`,
  `Cslib.Crypto.Protocols.SigmaProtocol.encCHVZKGuessInput`,
  `Cslib.Crypto.Protocols.SigmaProtocol.CHVZKAdversary.IsPPT`: families of typed two-stage
  adversaries and their uniform strict PPT admissibility.
* `Cslib.Crypto.Protocols.SigmaProtocol.simulatedConversation`: the conversation of a typed
  simulator at a uniform challenge.
* `Cslib.Crypto.Protocols.SigmaProtocol.chvzkRealGame`,
  `Cslib.Crypto.Protocols.SigmaProtocol.chvzkSimGame`: Attack Game 20.4 over `setup`.
* `Cslib.Crypto.Protocols.SigmaProtocol.ComputationalSpecialHVZK`: Definition 20.6 with explicit
  simulator and acceptance error `δ`.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.advantage_chvzkExperiment_le`: conversation laws that are
  `ε`-close on valid pairs give advantage at most `ε` against every adversary.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.closeTo_simulatedConversation`:
  statistical closeness of honest and simulated conversations.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.advantage_chvzkExperiment_le`,
  `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.advantage_chvzkGame_le`: concrete
  advantage bounds in Attack Game 20.4 against arbitrary adversaries.
* `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.computationalSpecialHVZK_of_accepts`,
  `Cslib.Crypto.Protocols.SigmaProtocol.SimulatorRealizedBy.computationalSpecialHVZK`,
  `Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialHVZK.exists_computationalSpecialHVZK`:
  statistical special HVZK with negligible realization error along `setup` implies computational
  special HVZK.
* `EfficientSpecialSoundness.of_verify_eq`,
  `SimulatorRealizedBy.closeTo_transcript_of_closeTo`,
  `advantage_chvzkRealGame_le_of_closeTo_transcript`,
  `SimulatorRealizedBy.advantage_chvzkGame_le_of_closeTo_transcript`,
  `ComputationalSpecialHVZK.of_closeTo_transcript`,
  `closeTo_andProof_transcript`, `closeTo_orProofWith_transcript`,
  `closeTo_parallelRepetition_transcript`
* `Cslib.Crypto.Protocols.SigmaProtocol.exists_negligible_inv_two_pow_map`: uniform `1 / 2 ^ n`
  error along any `(setup n).map (n, ·)` distribution is negligibly bounded.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 2.3.4 and Section 20.4.2 (Attack Game 20.4 and
  Definition 20.6, p. 840).
-/

@[expose] public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Turing.MultiTapeTM Interactive
open scoped ENNReal NNReal

/-! ### Attack Game 20.4 at one index -/

section Fixed

variable {X Y T C Z σ : Type}

open Classical in
/-- Attack Game 20.4 ([BonehShoup2023], Section 20.4.2, p. 840) at one index, with conversation
law `conv`. The adversary chooses a witness-statement pair `(x, y)` and a state. If `R x y` holds,
the challenger samples a conversation from `conv x y` and the experiment outputs the adversary's
guess on it; it outputs `false` when `R x y` fails. -/
noncomputable def chvzkExperiment (R : X → Y → Prop) (conv : X → Y → PMF (T × C × Z))
    (A : TwoStage Unit (X × Y) (T × C × Z) Bool σ) : Game := do
  let ((x, y), state) ← A.choose ()
  if R x y then
    let conversation ← conv x y
    A.guess state conversation
  else
    return false

/-- Conversation laws that are `ε`-close on every valid pair give Attack Game 20.4 advantage at
most `ε` against every adversary, including computationally unbounded ones. -/
theorem advantage_chvzkExperiment_le {R : X → Y → Prop}
    {conv₀ conv₁ : X → Y → PMF (T × C × Z)} {ε : ℝ≥0}
    (h : ∀ x y, R x y → CloseTo (conv₀ x y) (conv₁ x y) ε)
    (A : TwoStage Unit (X × Y) (T × C × Z) Bool σ) :
    Game.advantage (chvzkExperiment R conv₀ A) (chvzkExperiment R conv₁ A) ≤ ε := by
  classical
  simp only [chvzkExperiment, PMF.monad_bind_eq_bind]
  refine Game.advantage_bind_le_nnreal _ _ _ fun ⟨⟨x, y⟩, state⟩ => ?_
  by_cases hxy : R x y
  · simp only [hxy, ↓reduceIte]
    exact Game.advantage_bind_le_of_closeTo (h x y hxy) _
  · simp only [hxy, ↓reduceIte, Game.advantage_self, zero_le]

end Fixed

/-! ### Adversary families and their efficiency -/

variable {I : Type} {X Y T C Z : I → Type} {σ : Type}

variable (I X Y T C Z σ) in
/-- A family of Attack Game 20.4 adversaries: at security parameter `n` and index `i`, a two-stage
adversary that chooses a pair in `X i × Y i` with a state of type `σ`, then guesses from the state
and a conversation in `T i × C i × Z i`. `CHVZKAdversary.IsPPT` states its efficiency on
encodings. -/
abbrev CHVZKAdversary : Type :=
  ℕ → (i : I) → TwoStage Unit (X i × Y i) (T i × C i × Z i) Bool σ

variable (I T C Z σ) in
/-- The input of the guessing stage: the security parameter, the saved state, the index and a
conversation at that index. -/
structure CHVZKGuessInput where
  /-- The security parameter. -/
  secParam : ℕ
  /-- The state saved by the choice stage. -/
  state : σ
  /-- The index. -/
  index : I
  /-- The commitment. -/
  commitment : T index
  /-- The challenge. -/
  challenge : C index
  /-- The response. -/
  response : Z index

/-- The encoding of a guessing-stage input: the unary security parameter, the state encoded by
`encσ`, the index and the words of the commitment, challenge and response under `enc` at that
index, each framed except the last (`encCHVZKGuessInput_apply`). -/
enc_structure encCHVZKGuessInput (enc : Encoding I Y T C Z) (encσ : σ ↪ List Bool) :
    CHVZKGuessInput I T C Z σ where
  secParam : encUnary, state : encσ, index : enc.index,
  commitment : (enc.commitment index) using (enc.commitment index).injective,
  challenge : (enc.challenge index) using (enc.challenge index).injective,
  response : (enc.response index) using (enc.response index).injective

/-- A family of Attack Game 20.4 adversaries is uniform strict PPT: one machine runs each stage at
every security parameter and index. The choice stage reads the unary security parameter and the
encoded index and writes the encoded witness, statement and state; the guessing stage reads
`encCHVZKGuessInput` and writes the guess. Each clock charges the complete encoded input,
including the saved state. -/
structure CHVZKAdversary.IsPPT (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (encσ : σ ↪ List Bool) (A : CHVZKAdversary I X Y T C Z σ) : Prop where
  /-- The choice stage is uniform strict PPT on the security parameter and the index. -/
  choose : IsPPTOn (encPair encUnary enc.index) (encPair (encPair encBits encBits) encσ)
    fun (⟨n, i⟩ : ℕ × I) =>
      (fun out => ((encW i out.1.1, enc.statement i out.1.2), out.2)) <$> (A n i).choose ()
  /-- The guessing stage is uniform strict PPT on the encoded guessing-stage input. -/
  guess : IsPPTOn (encCHVZKGuessInput enc encσ) encBool
    fun g => (A g.secParam g.index).guess g.state (g.commitment, g.challenge, g.response)

/-! ### The real and simulated games -/

/-- The simulated conversation on `(i, y)` ([BonehShoup2023], Section 20.4.2, Attack Game 20.4,
Experiment 1, p. 840): sample a uniform challenge `c : C i` and run `sim i y c`. -/
noncomputable def simulatedConversation [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (sim : Simulator I Y T C Z) (i : I) (y : Y i) : PMF (T i × C i × Z i) := do
  let c ← PMF.uniformOfFintype (C i)
  let tz ← sim i y c
  return (tz.1, c, tz.2)

/-- Experiment 0 of Attack Game 20.4 ([BonehShoup2023], Section 20.4.2, p. 840): draw `i ← setup n`
and give the adversary an honest conversation of `P i` on its valid pair. -/
noncomputable def chvzkRealGame
    (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (R : ∀ i, X i → Y i → Prop) (setup : ℕ → PMF I) (A : CHVZKAdversary I X Y T C Z σ)
    (n : ℕ) : Game := do
  let i ← setup n
  chvzkExperiment (R i) (P i).conversation (A n i)

/-- Experiment 1 of Attack Game 20.4 ([BonehShoup2023], Section 20.4.2, p. 840): draw `i ← setup n`
and give the adversary a conversation simulated from the statement of its valid pair, without the
witness. -/
noncomputable def chvzkSimGame
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (R : ∀ i, X i → Y i → Prop) (setup : ℕ → PMF I) (sim : Simulator I Y T C Z)
    (A : CHVZKAdversary I X Y T C Z σ) (n : ℕ) : Game := do
  let i ← setup n
  chvzkExperiment (R i) (fun _ y => simulatedConversation sim i y) (A n i)

/-- **Computational special honest-verifier zero knowledge** ([BonehShoup2023], Section 20.4.2,
Definition 20.6, p. 840), for a family `P` of Sigma protocols over `setup` with explicit typed
simulator `sim` and acceptance error `δ`: `sim` is uniform strict PPT, outputs an accepting
conversation on every `(i, y, c)` with probability at least `1 - δ i` (exact Definition 20.6
acceptance when `δ = fun _ => 0`), and for every state type and state encoding, every uniform
strict PPT `CHVZKAdversary` has negligible distinguishing advantage between `chvzkRealGame` and
`chvzkSimGame`. -/
structure ComputationalSpecialHVZK
    (P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i))
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    (R : ∀ i, X i → Y i → Prop)
    (enc : Encoding I Y T C Z) (encW : ∀ i, X i ↪ List Bool)
    (setup : ℕ → PMF I) (sim : Simulator I Y T C Z) (δ : I → ℝ≥0∞) : Prop where
  /-- The simulator family is uniform strict PPT. -/
  ppt : Simulator.IsPPT enc sim
  /-- On every statement and challenge, `sim` outputs an accepting conversation with probability
  at least `1 - δ i`. -/
  accepts : ∀ i (y : Y i) (c : C i),
    1 - δ i ≤ (ProbComp.eval (sim i y c)).toOuterMeasure {tz | (P i).Accepts y tz.1 c tz.2}
  /-- Honest and simulated conversations are computationally indistinguishable in Attack Game
  20.4, for every state type and state encoding. -/
  indistinguishable : ∀ {σ : Type} (encσ : σ ↪ List Bool),
    Game.Indistinguishable (chvzkRealGame P R setup (σ := σ)) (chvzkSimGame R setup sim)
      (CHVZKAdversary.IsPPT enc encW encσ)

/-- Relaxing the acceptance-error bound preserves `ComputationalSpecialHVZK`. -/
theorem ComputationalSpecialHVZK.mono_error
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
    {setup : ℕ → PMF I} {sim : Simulator I Y T C Z} {δ δ' : I → ℝ≥0∞}
    (h : ComputationalSpecialHVZK P R enc encW setup sim δ) (hle : ∀ i, δ i ≤ δ' i) :
    ComputationalSpecialHVZK P R enc encW setup sim δ' where
  ppt := h.ppt
  accepts i y c := (tsub_le_tsub_left (hle i) 1).trans (h.accepts i y c)
  indistinguishable := h.indistinguishable

/-! ### Bridging statistical `EfficientSpecialHVZK` to `ComputationalSpecialHVZK` -/

section StatisticalBridge

variable {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
  [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
  {R : ∀ i, X i → Y i → Prop}
  {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
  {setup : ℕ → PMF I}
  {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z} {δ : I → ℝ≥0∞}

/-- A simulator realizing a perfect special HVZK simulator up to `δ i` gives simulated
conversations within statistical distance `δ i` of honest conversations, for every valid
witness-statement pair. -/
theorem SimulatorRealizedBy.closeTo_simulatedConversation
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ)
    {i : I} {x : X i} {y : Y i} (hxy : R i x y) :
    CloseTo ((P i).conversation x y) (simulatedConversation sim i y) (δ i) := by
  rw [(hS i).conversation_eq hxy]
  exact CloseTo.bind_right _ fun c _ => (h i y c).bind_left _

/-- When `δ i ≤ ε`, a simulator realizing a perfect special HVZK simulator has Attack Game 20.4
advantage at most `ε` at index `i` against *every* adversary (including computationally unbounded
adversaries). -/
theorem SimulatorRealizedBy.advantage_chvzkExperiment_le
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ) (i : I) {ε : ℝ≥0} (hδ : δ i ≤ ε)
    (A : TwoStage Unit (X i × Y i) (T i × C i × Z i) Bool σ) :
    Game.advantage (chvzkExperiment (R i) (P i).conversation A)
      (chvzkExperiment (R i) (fun _ y => simulatedConversation sim i y) A) ≤ ε :=
  SigmaProtocol.advantage_chvzkExperiment_le
    (fun _ _ hxy => (h.closeTo_simulatedConversation hS hxy).mono hδ) A

/-- When `δ i ≤ ε` on `(setup n).support`, a simulator realizing a perfect special HVZK simulator
has Attack Game 20.4 advantage at most `ε` against *every* adversary family (including
computationally unbounded adversaries). -/
theorem SimulatorRealizedBy.advantage_chvzkGame_le
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (h : SimulatorRealizedBy simulate sim δ)
    {n : ℕ} {ε : ℝ≥0} (hδ : ∀ i ∈ (setup n).support, δ i ≤ ε)
    (A : CHVZKAdversary I X Y T C Z σ) :
    Game.advantage (chvzkRealGame P R setup A n) (chvzkSimGame R setup sim A n) ≤ ε :=
  Game.advantage_bind_le_of_support (setup n) _ _ fun i hi =>
    h.advantage_chvzkExperiment_le hS i (hδ i hi) (A n i)

/-- A strict PPT simulator realizing a perfect special HVZK simulator with negligible statistical
error along `setup` gives `ComputationalSpecialHVZK`, retaining any independently proved acceptance
error `δ'`. -/
theorem SimulatorRealizedBy.computationalSpecialHVZK_of_accepts
    {δ' : I → ℝ≥0∞}
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (hppt : Simulator.IsPPT enc sim)
    (hreal : SimulatorRealizedBy simulate sim δ)
    (hacc : ∀ i (y : Y i) (c : C i),
      1 - δ' i ≤ (ProbComp.eval (sim i y c)).toOuterMeasure {tz | (P i).Accepts y tz.1 c tz.2})
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, ∀ i ∈ (setup n).support, δ i ≤ ε n) :
    ComputationalSpecialHVZK P R enc encW setup sim δ' where
  ppt := hppt
  accepts := hacc
  indistinguishable _ adversary _ := by
    obtain ⟨ε, hε, hle⟩ := hnegl
    exact negligible_of_le hε fun n => hreal.advantage_chvzkGame_le hS (hle n) adversary

/-- A strict PPT simulator realizing a perfect special HVZK simulator with negligible statistical
error along `setup` satisfies `ComputationalSpecialHVZK` with acceptance error `δ`. -/
theorem SimulatorRealizedBy.computationalSpecialHVZK
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (hppt : Simulator.IsPPT enc sim)
    (hreal : SimulatorRealizedBy simulate sim δ)
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, ∀ i ∈ (setup n).support, δ i ≤ ε n) :
    ComputationalSpecialHVZK P R enc encW setup sim δ :=
  hreal.computationalSpecialHVZK_of_accepts hS hppt (hreal.one_sub_le_accepts hS) hnegl

/-- **Efficient statistical special HVZK implies computational special HVZK** whenever the
realization error `δ` is bounded along `setup` by a negligible function. -/
theorem EfficientSpecialHVZK.exists_computationalSpecialHVZK
    (h : EfficientSpecialHVZK P R enc simulate δ)
    (encW : ∀ i, X i ↪ List Bool) (setup : ℕ → PMF I)
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧ ∀ n, ∀ i ∈ (setup n).support, δ i ≤ ε n) :
    ∃ sim, ComputationalSpecialHVZK P R enc encW setup sim δ := by
  obtain ⟨sim, hppt, hreal⟩ := h.realized
  exact ⟨sim, hreal.computationalSpecialHVZK h.specialHVZK hppt hnegl⟩

end StatisticalBridge

/-! ### Transfer across protocols with close honest transcripts -/

section TranscriptTransfer

/-- Efficient special soundness depends only on `verify` and transfers across protocol families with
the same verifier. -/
theorem EfficientSpecialSoundness.of_verify_eq
    {P P' : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    {W : I → Type} {R : ∀ i, W i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, W i ↪ List Bool}
    {extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i}
    (h : EfficientSpecialSoundness P R enc encW extract)
    (hver : ∀ i, (P' i).verify = (P i).verify) :
    EfficientSpecialSoundness P' R enc encW extract where
  specialSoundness i y t c z c' z' hc hz hz' := by
    simp only [Accepts, hver i] at hz hz'
    exact h.specialSoundness i y t c z c' z' hc hz hz'
  polyTime := h.polyTime

/-- Combining a perfect special HVZK simulator for `P`, a typed simulator realizing it up to
`δS i`, and a second protocol family `P'` whose honest transcript is within `δP i` of `(P i)`'s
yields `δP i + δS i` pointwise transcript closeness for `P'`. -/
theorem SimulatorRealizedBy.closeTo_transcript_of_closeTo
    {P P' : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    {R : ∀ i, X i → Y i → Prop}
    {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z}
    {δP δS : I → ℝ≥0∞}
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (hreal : SimulatorRealizedBy simulate sim δS)
    {i : I} {x : X i} {y : Y i} (hxy : R i x y) {c : C i}
    (htrans : CloseTo ((P i).transcript x y c) ((P' i).transcript x y c) (δP i)) :
    CloseTo ((P' i).transcript x y c) (ProbComp.eval (sim i y c)) (δP i + δS i) :=
  htrans.symm.trans (hreal.closeTo_transcript hS hxy c)

/-- Replacing `P` by a protocol family `P'` whose honest transcripts are within `ε` on valid pairs
over `(setup n).support` changes Experiment 0 of Attack Game 20.4 (`chvzkRealGame`) by at most `ε`
in `Game.advantage`, against every adversary (including computationally unbounded ones). -/
theorem advantage_chvzkRealGame_le_of_closeTo_transcript
    {P P' : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    {R : ∀ i, X i → Y i → Prop}
    {setup : ℕ → PMF I} {n : ℕ} {ε : ℝ≥0}
    (htrans : ∀ i ∈ (setup n).support, ∀ x y, R i x y → ∀ c,
      CloseTo ((P i).transcript x y c) ((P' i).transcript x y c) ε)
    (A : CHVZKAdversary I X Y T C Z σ) :
    Game.advantage (chvzkRealGame P' R setup A n) (chvzkRealGame P R setup A n) ≤ ε := by
  refine Game.advantage_bind_le_of_support (setup n) _ _ fun i hi => ?_
  refine advantage_chvzkExperiment_le (fun x y hxy => ?_) (A n i)
  rw [(P' i).conversation_eq_bind_transcript, (P i).conversation_eq_bind_transcript]
  exact CloseTo.bind_right _ fun c _ => ((htrans i hi x y hxy c).symm).bind_left _

/-- Combining `advantage_chvzkRealGame_le_of_closeTo_transcript` and
`SimulatorRealizedBy.advantage_chvzkGame_le` bounds Attack Game 20.4 distinguishing advantage for
`P'` by `εP + εS` against every adversary (including computationally unbounded ones). -/
theorem SimulatorRealizedBy.advantage_chvzkGame_le_of_closeTo_transcript
    {P P' : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    {R : ∀ i, X i → Y i → Prop}
    {setup : ℕ → PMF I}
    {simulate : ∀ i, Y i → C i → PMF (T i × Z i)} {sim : Simulator I Y T C Z}
    {δ : I → ℝ≥0∞} {n : ℕ} {εP εS : ℝ≥0}
    (hS : ∀ i, (P i).SpecialHVZK (R i) (simulate i))
    (hreal : SimulatorRealizedBy simulate sim δ)
    (htrans : ∀ i ∈ (setup n).support, ∀ x y, R i x y → ∀ c,
      CloseTo ((P i).transcript x y c) ((P' i).transcript x y c) εP)
    (hδ : ∀ i ∈ (setup n).support, δ i ≤ εS)
    (A : CHVZKAdversary I X Y T C Z σ) :
    Game.advantage (chvzkRealGame P' R setup A n) (chvzkSimGame R setup sim A n) ≤ εP + εS :=
  (Game.advantage_triangle _ _ _).trans
    (add_le_add (advantage_chvzkRealGame_le_of_closeTo_transcript htrans A)
      (hreal.advantage_chvzkGame_le hS hδ A))

/-- `ComputationalSpecialHVZK` transfers from `P` to `P'` with the same simulator `sim` and
acceptance error `δ` whenever `P'` accepts every conversation `P` accepts and their honest
transcripts are within a negligible statistical distance along `setup` on valid pairs. -/
theorem ComputationalSpecialHVZK.of_closeTo_transcript
    {P P' : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)}
    [∀ i, Fintype (C i)] [∀ i, Nonempty (C i)]
    {R : ∀ i, X i → Y i → Prop}
    {enc : Encoding I Y T C Z} {encW : ∀ i, X i ↪ List Bool}
    {setup : ℕ → PMF I} {sim : Simulator I Y T C Z} {δ : I → ℝ≥0∞}
    (h : ComputationalSpecialHVZK P R enc encW setup sim δ)
    (hacc : ∀ i y t c z, (P i).Accepts y t c z → (P' i).Accepts y t c z)
    (hnegl : ∃ ε : ℕ → ℝ≥0, Negligible ε ∧
      ∀ n, ∀ i ∈ (setup n).support, ∀ x y, R i x y → ∀ c,
        CloseTo ((P i).transcript x y c) ((P' i).transcript x y c) (ε n)) :
    ComputationalSpecialHVZK P' R enc encW setup sim δ where
  ppt := h.ppt
  accepts i y c := (h.accepts i y c).trans
    (MeasureTheory.measure_mono fun tz htz => hacc i y tz.1 c tz.2 htz)
  indistinguishable encσ A hA := by
    obtain ⟨ε, hε, hle⟩ := hnegl
    refine negligible_of_le (hε.add (h.indistinguishable encσ A hA)) fun n => ?_
    exact (Game.advantage_triangle _ _ _).trans
      (add_le_add (advantage_chvzkRealGame_le_of_closeTo_transcript (hle n) A) le_rfl)

/-- Honest transcripts of `andProof` add their component transcript distances (`δ₀ + δ₁`). -/
theorem closeTo_andProof_transcript {X₀ Y₀ T₀ Z₀ X₁ Y₁ T₁ Z₁ C : Type}
    {P₀ P₀' : SigmaProtocol X₀ Y₀ T₀ C Z₀} {P₁ P₁' : SigmaProtocol X₁ Y₁ T₁ C Z₁}
    {x : X₀ × X₁} {y : Y₀ × Y₁} {c : C} {δ₀ δ₁ : ℝ≥0∞}
    (h₀ : CloseTo (P₀.transcript x.1 y.1 c) (P₀'.transcript x.1 y.1 c) δ₀)
    (h₁ : CloseTo (P₁.transcript x.2 y.2 c) (P₁'.transcript x.2 y.2 c) δ₁) :
    CloseTo ((P₀.andProof P₁).transcript x y c) ((P₀'.andProof P₁').transcript x y c)
      (δ₀ + δ₁) := by
  rw [andProof_transcript, andProof_transcript]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  exact h₀.bind fun _ _ => h₁.bind_left _

/-- Honest transcripts of `orProofWith` on any valid witness-statement pair (`orRelation R₀ R₁`)
add the challenge-sampling error `δC`, the simulated-side error `δS`, and the witness-side honest
transcript error `δP`. -/
theorem closeTo_orProofWith_transcript {X₀ Y₀ T₀ Z₀ X₁ Y₁ T₁ Z₁ C : Type} [AddCommGroup C]
    {sampleChallenge sampleChallenge' : PMF C}
    {P₀ P₀' : SigmaProtocol X₀ Y₀ T₀ C Z₀} {P₁ P₁' : SigmaProtocol X₁ Y₁ T₁ C Z₁}
    {R₀ : X₀ → Y₀ → Prop} {R₁ : X₁ → Y₁ → Prop}
    {simulate₀ simulate₀' : Y₀ → C → PMF (T₀ × Z₀)}
    {simulate₁ simulate₁' : Y₁ → C → PMF (T₁ × Z₁)}
    {x : X₀ ⊕ X₁} {y : Y₀ × Y₁} (hxy : orRelation R₀ R₁ x y) (c : C) {δC δS δP : ℝ≥0∞}
    (hc : CloseTo sampleChallenge sampleChallenge' δC)
    (hs₀ : ∀ c₀, CloseTo (simulate₀ y.1 c₀) (simulate₀' y.1 c₀) δS)
    (hs₁ : ∀ c₁, CloseTo (simulate₁ y.2 c₁) (simulate₁' y.2 c₁) δS)
    (hp₀ : ∀ x₀, R₀ x₀ y.1 → ∀ c₀,
      CloseTo (P₀.transcript x₀ y.1 c₀) (P₀'.transcript x₀ y.1 c₀) δP)
    (hp₁ : ∀ x₁, R₁ x₁ y.2 → ∀ c₁,
      CloseTo (P₁.transcript x₁ y.2 c₁) (P₁'.transcript x₁ y.2 c₁) δP) :
    CloseTo ((orProofWith sampleChallenge P₀ P₁ simulate₀ simulate₁).transcript x y c)
      ((orProofWith sampleChallenge' P₀' P₁' simulate₀' simulate₁').transcript x y c)
      (δC + (δS + δP)) := by
  rcases x with x₀ | x₁
  · rw [orProofWith_transcript_inl, orProofWith_transcript_inl]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    exact hc.bind fun c₁ _ => (hs₁ c₁).bind fun _ _ => (hp₀ x₀ hxy (c - c₁)).bind_left _
  · rw [orProofWith_transcript_inr, orProofWith_transcript_inr]
    simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
    exact hc.bind fun c₀ _ => (hs₀ c₀).bind fun _ _ => (hp₁ x₁ hxy (c - c₀)).bind_left _

/-- Honest transcripts of `k`-fold `parallelRepetition` multiply a uniform coordinate transcript
distance `δ` by `k`. -/
theorem closeTo_parallelRepetition_transcript {X Y T C Z : Type}
    {P P' : SigmaProtocol X Y T C Z} {k : ℕ} {x : X} {y : Y} {c : Fin k → C} {δ : ℝ≥0∞}
    (h : ∀ j, CloseTo (P.transcript x y (c j)) (P'.transcript x y (c j)) δ) :
    CloseTo ((P.parallelRepetition k).transcript x y c)
      ((P'.parallelRepetition k).transcript x y c) (k * δ) := by
  rw [parallelRepetition_transcript, parallelRepetition_transcript]
  exact (CloseTo.piFin h).map _

end TranscriptTransfer

/-- `1 / 2 ^ n` is bounded along any distribution paired with the security parameter by a
negligible geometric sequence. -/
theorem exists_negligible_inv_two_pow_map {D : Type} (setup : ℕ → PMF D) :
    ∃ ε : ℕ → ℝ≥0, Negligible ε ∧
      ∀ n, ∀ i ∈ ((setup n).map (n, ·)).support, (1 / 2 ^ i.1 : ℝ≥0∞) ≤ ε n := by
  refine ⟨fun n => (1 / 2 : ℝ≥0) ^ n, negligible_geometric (by norm_num), fun n i hi => ?_⟩
  obtain ⟨d, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hi
  dsimp only
  rw [one_div_pow, ENNReal.coe_div (pow_ne_zero _ two_ne_zero), ENNReal.coe_one, ENNReal.coe_pow,
    ENNReal.coe_ofNat]

end Cslib.Crypto.Protocols.SigmaProtocol
