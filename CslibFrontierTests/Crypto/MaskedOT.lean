/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.MaskedOT
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition
import CslibFrontier.Probability.Uniform

/-!
# Tests for the oblivious transfer of masked values

A client of `CslibFrontier.Crypto.Protocols.MPC.MaskedOT` under module encapsulation.

* The conventions are checked on the one-time pad of `ZMod 5`: the sender's message carries the
  two masked values in the order of the values, the choice bit `true` selects the second pad and
  the second component, and the simulated message puts the chosen value in the chosen component.
  A transposed pair or a swapped choice fails these checks.
* The recovery hypothesis of the theorems is satisfiable: for the one-time pad of `ZMod 5` the
  execution outputs `otOutputs`, and a corrupted sender has advantage zero.
* The pad-hiding term of `semiHonestAdvantage_maskedOT_receiver_eq` can vanish: with independent
  uniform pads and a uniform simulated value, the one-time-pad transfer on `ZMod 5` has advantage
  zero against a corrupted receiver as well.
* `semiHonestAdvantage_maskedOT_compose_le_add` is applied to a plain-model pad transfer that the
  library already has: the three-message DDH transfer over `ZMod 5`, which is perfectly private
  against a corrupted sender. The masked transfer of words over it then has advantage zero against
  a corrupted sender, so both hypotheses of that theorem are satisfiable by a protocol without
  oracles, with the bound attained at zero.
* The masked transfer composes with `seqBatchOT` and with `Yao.composedProtocol`: the batched
  transfer of words over the masked transfer over the DDH transfer has advantage zero against a
  corrupted sender, for every number of transfers, and is accepted as the transfer subprotocol of
  Yao's protocol.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.MaskedOT

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC Cslib.Probability
open scoped ENNReal

/-- The one-time pad of `ZMod 5`: the value shifted by the pad. -/
def addMask (r m : ZMod 5) : ZMod 5 := r + m

/-- Removing the pad. -/
def subMask (r c : ZMod 5) : ZMod 5 := c - r

/-- Removing the pad inverts the one-time pad. -/
theorem subMask_addMask (r m : ZMod 5) : subMask r (addMask r m) = m :=
  add_sub_cancel_left r m

/-- The inputs: the sender offers `1` and `2`, and the receiver chooses with `σ`. -/
def inputs (σ : Bool) : (i : Fin 2) → OTIn (ZMod 5) i :=
  Fin.cases (motive := fun i => OTIn (ZMod 5) i) ((1, 2) : ZMod 5 × ZMod 5) fun _ => σ

/-- The sender's message carries the first value under the first pad, then the second value under
the second pad. -/
example : maskedOTMsg addMask ((1, 2) : ZMod 5 × ZMod 5) (3, 4) = (4, 1) := by decide

/-- The simulated message puts the chosen value in the second component for the choice bit `true`
and in the first for `false`. -/
example : maskedOTSimMsg true (1 : ZMod 5) 2 = (2, 1) ∧
    maskedOTSimMsg false (1 : ZMod 5) 2 = (1, 2) := ⟨rfl, rfl⟩

/-- With the choice bit `true` the receiver obtains the second pad. -/
example (r : ZMod 5 × ZMod 5) : maskedOTViews addMask (inputs true) r 1 =
    maskedOTReceiverView true r.2 (addMask r.1 1, addMask r.2 2) := rfl

/-- With the choice bit `false` the receiver obtains the first pad. -/
example (r : ZMod 5 × ZMod 5) : maskedOTViews addMask (inputs false) r 1 =
    maskedOTReceiverView false r.1 (addMask r.1 1, addMask r.2 2) := rfl

/-- The receiver's output is the value of its choice: `2` for `true` and `1` for `false`. -/
example : otOutputs (inputs true) 1 = (2 : ZMod 5) ∧ otOutputs (inputs false) 1 = (1 : ZMod 5) :=
  ⟨rfl, rfl⟩

/-- For every distribution of the pads, the execution of the one-time-pad transfer outputs
`otOutputs`. -/
example (samplePads : ProbComp (ZMod 5 × ZMod 5)) (σ : Bool) :
    ((maskedOT addMask subMask samplePads).evalWith (otWorld (ZMod 5)) (inputs σ)).map Prod.snd =
      PMF.pure (otOutputs (inputs σ)) := by
  rw [evalWith_maskedOT addMask subMask samplePads (inputs σ) fun r => subMask_addMask r _,
    PMF.map_bind]
  simp only [PMF.pure_map]
  exact PMF.bind_const _ _

/-- A corrupted sender has advantage zero against the one-time-pad transfer. -/
example (samplePads : ProbComp (ZMod 5 × ZMod 5)) (x : (i : Fin 2) → OTIn (ZMod 5) i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView (OTIn (ZMod 5)) (MaskedOTCoins (ZMod 5))
        (maskedOTSchedule (ZMod 5) (ZMod 5)) i) × ((i : Fin 2) → OTOut (ZMod 5) i) →
      ProbComp Bool) :
    semiHonestAdvantage (maskedOT addMask subMask samplePads) (otWorld (ZMod 5))
      (otFunctionality (ZMod 5)) {0} (maskedOTSenderSim samplePads) x D = 0 :=
  semiHonestAdvantage_maskedOT_sender addMask subMask samplePads x (fun r => subMask_addMask r _) D

/-- Two independent uniform pads in `ZMod 5`. -/
noncomputable def uniformPads : ProbComp (ZMod 5 × ZMod 5) := do
  let r₀ ← ProbComp.uniform (ZMod 5)
  let r₁ ← ProbComp.uniform (ZMod 5)
  return (r₀, r₁)

/-- **The one-time-pad transfer on `ZMod 5`, corrupted receiver.** With independent uniform pads
the masked unchosen value is uniform and independent of the receiver's pad, so the pad-hiding
advantage of `semiHonestAdvantage_maskedOT_receiver_eq` is zero for the simulator that fills the
unchosen component with a uniform value. -/
example (x : (i : Fin 2) → OTIn (ZMod 5) i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (ZMod 5)) (MaskedOTCoins (ZMod 5))
        (maskedOTSchedule (ZMod 5) (ZMod 5)) i) × ((i : Fin 2) → OTOut (ZMod 5) i) →
      ProbComp Bool) :
    semiHonestAdvantage (maskedOT addMask subMask uniformPads) (otWorld (ZMod 5))
      (otFunctionality (ZMod 5)) {1}
      (maskedOTReceiverSim addMask uniformPads (ProbComp.uniform (ZMod 5))) x D = 0 := by
  have hshift : ∀ (c : ZMod 5) (g : ZMod 5 → PMF Bool),
      ((PMF.uniformOfFintype (ZMod 5)).bind fun r => g (r + c)) =
        (PMF.uniformOfFintype (ZMod 5)).bind g := fun c g => by
    conv_rhs => rw [← PMF.uniformOfFintype_map_add_right c, PMF.bind_map]
    rfl
  have key : ∀ T : ZMod 5 → ZMod 5 → ProbComp Bool,
      ProbComp.eval (do
        let r ← uniformPads
        let u ← ProbComp.uniform (ZMod 5)
        let σ : Bool := x 1
        T (if σ then r.2 else r.1) u) =
      ProbComp.eval (do
        let r ← uniformPads
        let σ : Bool := x 1
        T (if σ then r.2 else r.1)
          (if σ then addMask r.1 (x 0).1 else addMask r.2 (x 0).2)) := by
    intro T
    simp only [uniformPads, addMask, ProbComp.eval_bind, ProbComp.eval_uniform, bind_assoc,
      pure_bind]
    split_ifs with hσ
    · rw [PMF.bind_const]
      conv_rhs => rw [PMF.bind_comm]
      exact congrArg _ (funext fun r₁ =>
        (hshift (x 0).1 fun u => ProbComp.eval (T r₁ u)).symm)
    · refine congrArg _ (funext fun r₀ => ?_)
      rw [PMF.bind_const]
      exact (hshift (x 0).2 fun u => ProbComp.eval (T r₀ u)).symm
  rw [semiHonestAdvantage_maskedOT_receiver_eq addMask subMask uniformPads
    (ProbComp.uniform (ZMod 5)) x fun r => subMask_addMask r _, key]
  exact Game.advantage_self _

section Composition

variable (mask unmask : ZMod 5 → List Bool → List Bool)
  (hmask : ∀ r m, unmask r (mask r m) = m) (samplePads : ProbComp (ZMod 5 × ZMod 5))
  (S₁ : (J : Finset (Fin 2)) → CoalitionSimulator (maskedOTSchedule (ZMod 5) (List Bool))
    (OTIn (List Bool)) (MaskedOTCoins (ZMod 5)) (OTOut (List Bool)) J)
  (hS₁ : S₁ {0} = maskedOTSenderSim samplePads)
  (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (ZMod 5)) (OTIn (ZMod 5))
    (DDHOTCoins 5) (OTOut (ZMod 5)) J)
  (hS₂ : S₂ {0} = ddhOTSenderSim (1 : ZMod 5) 5)

/-- A mask of words by pads in `ZMod 5` with a left inverse exists: the hypothesis `hmask` of this
section is satisfiable. This mask hides nothing; it only witnesses the hypothesis. -/
example : ∃ mask unmask : ZMod 5 → List Bool → List Bool, ∀ r m, unmask r (mask r m) = m :=
  ⟨fun _ m => m.reverse, fun _ c => c.reverse, fun _ m => m.reverse_reverse⟩

include hmask hS₁ hS₂ in
/-- **The masked transfer of words over the DDH transfer on `ZMod 5`, corrupted sender.** Both
hypotheses of `semiHonestAdvantage_maskedOT_compose_le_add` hold with bound zero for the coalition
`{0}`, so the plain-model masked transfer has advantage zero against a corrupted sender. -/
theorem maskedOT_ddhOT_sender (q : (i : Fin 2) → OTIn (List Bool) i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView (OTIn (List Bool))
        (Schedule.ComposedCoins (fun _ => DDHOTCoins 5) (MaskedOTCoins (ZMod 5))
          (maskedOTSchedule (ZMod 5) (List Bool)))
        (Schedule.compose (fun _ => ddhOTSchedule (ZMod 5))
          (maskedOTSchedule (ZMod 5) (List Bool))) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    (semiHonestAdvantage
      ((maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5)
      noOracleWorld (otFunctionality (List Bool)) {0}
      (composeSim (maskedOT mask unmask samplePads) (S₁ {0}) (fun _ => S₂)) q D : ℝ≥0∞) ≤ 0 := by
  have h := semiHonestAdvantage_maskedOT_compose_le_add mask unmask samplePads noOracleWorld
    (ddhOTProtocol (1 : ZMod 5) 5) S₁ S₂ {0} 0 0 q
    (fun D' => by
      rw [hS₁, semiHonestAdvantage_maskedOT_sender mask unmask samplePads q
        (fun r => hmask r _) D', ENNReal.coe_zero])
    (fun q' D' => by
      rw [hS₂, semiHonestAdvantage_ddhOT_sender (1 : ZMod 5) 5 q' D', ENNReal.coe_zero]) D
  rwa [add_zero] at h

include hmask hS₁ hS₂ in
/-- **The batched transfer of words over the masked transfer over the DDH transfer on `ZMod 5`,
corrupted sender.** `semiHonestAdvantage_seqBatchOT_compose_le_mul` applies with `ε = 0`, so the
plain-model batched transfer of `k` words has advantage zero against a corrupted sender. -/
theorem seqBatchOT_maskedOT_ddhOT_sender (k : ℕ)
    (x : (i : Fin 2) → (batchOTSpec k (List Bool)).Query () i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView ((batchOTSpec k (List Bool)).Query ())
        (Schedule.ComposedCoins
          (fun _ => Schedule.ComposedCoins (fun _ => DDHOTCoins 5) (MaskedOTCoins (ZMod 5))
            (maskedOTSchedule (ZMod 5) (List Bool)))
          (fun _ => Unit) (seqBatchOTSchedule k (List Bool)))
        (Schedule.compose
          (fun _ => Schedule.compose (fun _ => ddhOTSchedule (ZMod 5))
            (maskedOTSchedule (ZMod 5) (List Bool)))
          (seqBatchOTSchedule k (List Bool))) i) ×
      ((i : Fin 2) → (batchOTSpec k (List Bool)).Answer () i) → ProbComp Bool) :
    (semiHonestAdvantage
      ((seqBatchOT k (List Bool)).compose fun _ =>
        (maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5)
      noOracleWorld (batchOTFunctionality k (List Bool)) {0}
      (composeSim (seqBatchOT k (List Bool)) (seqBatchOTSim k (List Bool) {0})
        (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂))) x D :
      ℝ≥0∞) ≤ 0 := by
  have h := semiHonestAdvantage_seqBatchOT_compose_le_mul k (List Bool) noOracleWorld
    ((maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5)
    (fun J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂)) {0} 0
    (maskedOT_ddhOT_sender mask unmask hmask samplePads S₁ hS₁ S₂ hS₂) x D
  rwa [mul_zero] at h

include hmask hS₁ hS₂ in
/-- **Yao's protocol over the batched masked transfer over the DDH transfer on `ZMod 5`, corrupted
garbler.** The garbler is the sender of every transfer, so the transfer term of
`Yao.semiHonestAdvantage_composedProtocol_garbler_le_transfer` vanishes: this plain-model protocol
has advantage zero against a corrupted garbler, at every parameter `n ≥ 1`, for a correct garbling
scheme with a projective encoding. -/
example {Fn : Type} (Gs : Garbling.Scheme Fn) (hproj : Gs.encode = Garbling.projectiveEncode)
    (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n) (c : Yao.Params Gs)
    (x : (i : Fin 2) → Yao.Input c i) (D : _) :
    semiHonestAdvantage
      (Yao.composedProtocol Gs n c ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
        (maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5))
      noOracleWorld (Yao.functionality Gs c) {0}
      (composeSim (Yao.protocol Gs n c) (Yao.garblerSim Gs n c)
        (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
          (seqBatchOTSim c.evaluatorLen (List Bool) J)
          (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂))))
      x D = 0 := by
  have h := Yao.semiHonestAdvantage_composedProtocol_garbler_le_transfer hproj hcorrect hn c
    ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
      (maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5)
    noOracleWorld
    (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
      (seqBatchOTSim c.evaluatorLen (List Bool) J)
      (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂))) x D
  have h0 : ∀ J, J = ({0} : Finset (Fin 2)) → ∀ q D',
      (semiHonestAdvantage
        ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
          (maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5)
        noOracleWorld (batchOTFunctionality c.evaluatorLen (List Bool)) J
        (composeSim (seqBatchOT c.evaluatorLen (List Bool))
          (seqBatchOTSim c.evaluatorLen (List Bool) J)
          (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂))) q D' :
        ℝ≥0∞) = 0 := by
    rintro J rfl q D'
    exact nonpos_iff_eq_zero.mp (seqBatchOT_maskedOT_ddhOT_sender mask unmask hmask samplePads
      S₁ hS₁ S₂ hS₂ c.evaluatorLen q D')
  rw [tsum_eq_zero_iff.mpr fun r => by
    rw [h0 _ (Finset.ext fun _ => Composition.mem_subCoalition), mul_zero],
    nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at h
  exact h

/-- **The batched masked transfer as the transfer subprotocol of Yao's protocol.** For every
protocol `Sub` for a single transfer of pads in `G`, `seqBatchOT` over `maskedOT` over `Sub` has
the input and output types of `batchOTSpec c.evaluatorLen (List Bool)` and so is accepted by
`Yao.composedProtocol`. -/
noncomputable example {Fn G : Type} (Gs : Garbling.Scheme Fn) (n : ℕ) (c : Yao.Params Gs)
    (mask unmask : G → List Bool → List Bool) (samplePads : ProbComp (G × G))
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (Sub : Protocol 2 spec₂ sc₂ (OTIn G) Coins₂ (OTOut G)) :=
  Yao.composedProtocol Gs n c ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
    (maskedOT mask unmask samplePads).compose fun _ => Sub)

end Composition

/-- **Yao's protocol over the batched masked transfer, corrupted evaluator, with uniform bounds.**
For any pad transfer `Sub`, if every test has advantage at most `ε₁` against `maskedOT` with the
ideal pad transfer and at most `ε₂` against `Sub`, for the coalition `{1}`, then the advantage
against Yao's protocol over `seqBatchOT` over `maskedOT` over `Sub` is at most the `prv.sim`
advantage of the reduction plus `c.evaluatorLen * (ε₁ + ε₂)`: one masked transfer for each of the
evaluator's input bits. The hypotheses range over all tests, so this instance concerns
statistically secure components; for the DDH transfer against a corrupted receiver they do not
hold with a small `ε₂`. -/
example {Fn Λ G : Type} (Gs : Garbling.Scheme Fn) (hproj : Gs.encode = Garbling.projectiveEncode)
    (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n) (c : Yao.Params Gs) (Φ : Garbling.SideInfo Fn Λ)
    (S : ℕ → Garbling.PrvSimulator Λ)
    (mask unmask : G → List Bool → List Bool) (samplePads : ProbComp (G × G))
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (W₂ : MultiOracleWorld spec₂) (Sub : Protocol 2 spec₂ sc₂ (OTIn G) Coins₂ (OTOut G))
    (S₁ : (J : Finset (Fin 2)) → CoalitionSimulator (maskedOTSchedule G (List Bool))
      (OTIn (List Bool)) (MaskedOTCoins G) (OTOut (List Bool)) J)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator sc₂ (OTIn G) Coins₂ (OTOut G) J)
    (ε₁ ε₂ : ℝ≥0∞)
    (h₁ : ∀ q D', (semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld G)
      (otFunctionality (List Bool)) {1} (S₁ {1}) q D' : ℝ≥0∞) ≤ ε₁)
    (h₂ : ∀ q D', (semiHonestAdvantage Sub W₂ (otFunctionality G) {1} (S₂ {1}) q D' : ℝ≥0∞) ≤ ε₂)
    (x : (i : Fin 2) → Yao.Input c i) (D : _) :
    (semiHonestAdvantage
      (Yao.composedProtocol Gs n c ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
        (maskedOT mask unmask samplePads).compose fun _ => Sub))
      W₂ (Yao.functionality Gs c) {1}
      (composeSim (Yao.protocol Gs n c) (Yao.evaluatorSim Gs Φ S n c)
        (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
          (seqBatchOTSim c.evaluatorLen (List Bool) J)
          (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂))))
      x D : ℝ≥0∞) ≤
      Garbling.prvSimAdvantage Gs Φ n (S n) (Yao.evaluatorDistinguisherToPrvSim c x
        (composeDistinguisher (Yao.protocol Gs n c)
          (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
            (seqBatchOTSim c.evaluatorLen (List Bool) J)
            (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂)))
          {1} x D)) +
        c.evaluatorLen * (ε₁ + ε₂) := by
  refine (Yao.semiHonestAdvantage_composedProtocol_evaluator_le_transfer hproj hcorrect hn c Φ S
    ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
      (maskedOT mask unmask samplePads).compose fun _ => Sub) W₂
    (fun _ J => composeSim (seqBatchOT c.evaluatorLen (List Bool))
      (seqBatchOTSim c.evaluatorLen (List Bool) J)
      (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂))) x D).trans
    (add_le_add le_rfl ?_)
  have hOT : ∀ J, J = ({1} : Finset (Fin 2)) → ∀ q D',
      (semiHonestAdvantage
        ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ =>
          (maskedOT mask unmask samplePads).compose fun _ => Sub)
        W₂ (batchOTFunctionality c.evaluatorLen (List Bool)) J
        (composeSim (seqBatchOT c.evaluatorLen (List Bool))
          (seqBatchOTSim c.evaluatorLen (List Bool) J)
          (fun _ J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂))) q D' :
        ℝ≥0∞) ≤ c.evaluatorLen * (ε₁ + ε₂) := by
    rintro J rfl q D'
    exact semiHonestAdvantage_seqBatchOT_compose_le_mul c.evaluatorLen (List Bool) W₂
      ((maskedOT mask unmask samplePads).compose fun _ => Sub)
      (fun J => composeSim (maskedOT mask unmask samplePads) (S₁ J) (fun _ => S₂)) {1} (ε₁ + ε₂)
      (fun q' D'' => semiHonestAdvantage_maskedOT_compose_le_add mask unmask samplePads W₂ Sub
        S₁ S₂ {1} ε₁ ε₂ q' (h₁ q') h₂ D'') q D'
  calc _ ≤ ∑' r, ProbComp.eval (OracleComp.pi (Yao.protocol Gs n c).sampleCoins) r *
        (c.evaluatorLen * (ε₁ + ε₂)) :=
        tsum_le_tsum fun r => mul_le_mul' le_rfl
          (hOT _ (Finset.ext fun _ => Composition.mem_subCoalition) _ _)
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end CslibFrontierTests.Crypto.MaskedOT
