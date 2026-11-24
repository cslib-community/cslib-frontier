/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDF
import CslibFrontier.Crypto.Protocols.MPC.MaskedOT.DDHProb
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.KDF
import CslibFrontierTests.Crypto.PrimeFieldGroups

/-!
# Tests for the masked transfer with a key-derivation mask and over the DDH transfer

A client of `CslibFrontier.Crypto.Protocols.MPC.MaskedOT.KDF`,
`CslibFrontier.Crypto.Protocols.MPC.MaskedOT.DDH`,
`CslibFrontier.Crypto.Protocols.MPC.MaskedOT.DDHProb`,
`CslibFrontier.Crypto.Protocols.MPC.Composition.Cost`,
`CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT` and
`CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT.KDF` under module encapsulation.

* The key-derivation mask is checked on the groups `ZMod p` of `primeFields` with a constant
  two-bit key: masking twice recovers a two-bit word, and every masked word has the width of the
  key, which is why the per-instance theorem asks for the length of the receiver's output.
* The hypotheses of `semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf` are satisfiable: they hold
  for that key and two-bit inputs at the prime `5`. The constant key hides nothing; the instance
  only witnesses the hypotheses.
* `semiHonestAdvantage_maskedOT_ddhOT_receiver_le` applies to the DDH transfer over `ZMod 5`, whose
  generator hypothesis holds for `1`, and a family of simulators of the DDH transfer whose member
  at `{1}` is `ddhOTReceiverSim` exists.
* The per-transfer cost `ddhMaskedOTReceiverCost` is `⊤` away from the coalition `{1}`.
* The bound for Yao's protocol applies over `ZMod 5`.
* With the key-derivation mask at the prime `5` of `primeFields`: a family of simulators of the
  masked transfer whose member at `{1}` is `maskedOTReceiverSim` exists; the bound for one transfer
  over the DDH transfer applies to two-bit inputs under the constant two-bit key; the cost
  `kdfDDHMaskedOTReceiverCost` is `⊤` away from the coalition `{1}`; and the statements for Yao's
  protocol, for a corrupted evaluator and for a corrupted garbler, apply when the offered values
  are two bits long.
* Over the fair-coin DDH transfer `ddhOTProbProtocol` at the prime `5`: a family of simulators whose
  member at `{1}` is `ddhOTReceiverSimProb` exists, and the bound for one masked transfer applies.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoPlainDDHOT

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC Cslib.Probability
open CslibFrontierTests.Crypto.PrimeFieldGroups
open scoped ENNReal

/-! ### The key-derivation mask -/

/-- The prime `5` as group parameters of `primeFields`. -/
def five : primeFields.Desc := ⟨5, Nat.prime_five⟩

/-- A key-derivation function with the constant two-bit key `[true, false]`. It hides nothing and
only witnesses the length hypothesis. -/
def constKDF : primeFields.Desc × List Bool → List Bool := fun _ => [true, false]

/-- Masking twice recovers a word of the key's length: the hypothesis of `kdfMask_kdfMask` holds
for a two-bit word under the two-bit key. -/
example (r : primeFields.Carrier five) :
    primeFields.kdfMask constKDF five r (primeFields.kdfMask constKDF five r [true, true]) =
      [true, true] :=
  primeFields.kdfMask_kdfMask constKDF five r rfl

/-- The mask works at the width of the key: every masked word has the two bits of the key, so a
longer word is cut and masking twice cannot recover it. This is why the per-instance theorem asks
for the length of the receiver's output. -/
example (r : primeFields.Carrier five) (w : List Bool) :
    (primeFields.kdfMask constKDF five r w).length = 2 :=
  Cslib.BitString.length_listXor _ _

/-- The inputs: the sender offers `[true, true]` and `[false, false]`, and the receiver chooses
with `σ`. -/
def wordInputs (σ : Bool) : (i : Fin 2) → OTIn (List Bool) i :=
  Fin.cases (motive := fun i => OTIn (List Bool) i)
    (([true, true], [false, false]) : List Bool × List Bool) fun _ => σ

/-- **The hypotheses of `semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf` are satisfiable.** At the
prime `5`, with the constant two-bit key and two-bit inputs, the advantage against a corrupted
receiver is the key-derivation advantage of the reduction. -/
example (σ : Bool)
    (D : (n : ℕ) → (d : primeFields.Desc) →
      ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool))
          (MaskedOTCoins (primeFields.Carrier d))
          (maskedOTSchedule (primeFields.Carrier d) (List Bool)) i) ×
        ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) (n : ℕ) :
    semiHonestAdvantage
        (maskedOT (primeFields.kdfMask constKDF five) (primeFields.kdfMask constKDF five)
          (primeFields.kdfPads five))
        (otWorld (primeFields.Carrier five)) (otFunctionality (List Bool)) {1}
        (maskedOTReceiverSim (primeFields.kdfMask constKDF five) (primeFields.kdfPads five)
          (Cslib.BitString.sampleList 2)) (wordInputs σ) (D n five) =
      Game.advantage
        (primeFields.kdfIdealGame (fun _ => PMF.pure five) (fun _ => 2)
          (primeFields.maskedOTReceiverToKDFDistinguisher constKDF (fun _ _ => wordInputs σ) D) n)
        (primeFields.kdfRealGame (fun _ => PMF.pure five) constKDF
          (primeFields.maskedOTReceiverToKDFDistinguisher constKDF (fun _ _ => wordInputs σ) D)
          n) :=
  primeFields.semiHonestAdvantage_kdfMaskedOT_receiver_eq_kdf constKDF (fun _ => 2)
    (fun _ _ => wordInputs σ) D n five (fun _ => rfl) (by cases σ <;> rfl)

/-! ### The DDH transfer over `ZMod 5` -/

/-- `1` generates `ZMod 5`. -/
theorem one_generates (y : ZMod 5) : ∃ k : ZMod 5, k • (1 : ZMod 5) = y :=
  ⟨y, by rw [smul_eq_mul, mul_one]⟩

/-- **A family of simulators of the DDH transfer with `ddhOTReceiverSim` at `{1}` exists**, so the
hypothesis `hS₂` of the theorems is satisfiable. At the other coalitions the family returns the
views of one fixed execution; it only inhabits the type. -/
example : ∃ S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (ZMod 5)) (OTIn (ZMod 5)) (DDHOTCoins 5) (OTOut (ZMod 5)) J,
    S₂ {1} = ddhOTReceiverSim (1 : ZMod 5) 5 := by
  classical
  obtain ⟨⟨v, -⟩, -⟩ := ((ddhOTProtocol (1 : ZMod 5) 5).evalWith noOracleWorld
    (Fin.cases (motive := fun i => OTIn (ZMod 5) i) ((0, 0) : ZMod 5 × ZMod 5)
      fun _ => false)).support_nonempty
  exact ⟨fun J => if h : J = {1} then h ▸ ddhOTReceiverSim (1 : ZMod 5) 5
    else fun _ _ => pure fun i => v i.1, dite_eq_left rfl⟩

section Composition

variable (mask unmask : ZMod 5 → List Bool → List Bool) (samplePads : ProbComp (ZMod 5 × ZMod 5))
  (S₁ : (J : Finset (Fin 2)) → CoalitionSimulator (maskedOTSchedule (ZMod 5) (List Bool))
    (OTIn (List Bool)) (MaskedOTCoins (ZMod 5)) (OTOut (List Bool)) J)
  (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (ZMod 5)) (OTIn (ZMod 5))
    (DDHOTCoins 5) (OTOut (ZMod 5)) J)
  (hS₂ : S₂ {1} = ddhOTReceiverSim (1 : ZMod 5) 5)

include hS₂ in
/-- **The masked transfer of words over the DDH transfer on `ZMod 5`, corrupted receiver.** The
bound for one distinguisher applies: the advantage is at most the pad-hiding advantage plus the
expected DDH advantage of `maskedOTToDDHDistinguisher`. -/
example (x : (i : Fin 2) → OTIn (List Bool) i)
    (D : ((i : ({1} : Finset (Fin 2))) → PartyView (OTIn (List Bool))
        (Schedule.ComposedCoins (fun _ => DDHOTCoins 5) (MaskedOTCoins (ZMod 5))
          (maskedOTSchedule (ZMod 5) (List Bool)))
        (Schedule.compose (fun _ => ddhOTSchedule (ZMod 5))
          (maskedOTSchedule (ZMod 5) (List Bool))) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    (semiHonestAdvantage
        ((maskedOT mask unmask samplePads).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5)
        noOracleWorld (otFunctionality (List Bool)) {1}
        (composeSim (maskedOT mask unmask samplePads) S₁ (fun _ => S₂) {1}) x D : ℝ≥0∞) ≤
      semiHonestAdvantage (maskedOT mask unmask samplePads) (otWorld (ZMod 5))
          (otFunctionality (List Bool)) {1} (S₁ {1}) x
          (composeDistinguisher (maskedOT mask unmask samplePads) (fun _ => S₂) {1} x D) +
        ∑' c, ProbComp.eval (OracleComp.pi (maskedOT mask unmask samplePads).sampleCoins) c *
          (ddhAdvantage 5 (1 : ZMod 5)
            (maskedOTToDDHDistinguisher (1 : ZMod 5) 5 mask unmask S₂ x c D) : ℝ≥0∞) :=
  semiHonestAdvantage_maskedOT_ddhOT_receiver_le (1 : ZMod 5) 5 one_generates mask unmask
    samplePads S₁ S₂ hS₂ x D

/-- **The per-transfer cost is stated for a corrupted receiver only.** At the coalition `{0}` it is
`⊤`, so it bounds nothing there. -/
example (x : (i : Fin 2) → OTIn (List Bool) i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView (OTIn (List Bool))
        (Schedule.ComposedCoins (fun _ => DDHOTCoins 5) (MaskedOTCoins (ZMod 5))
          (maskedOTSchedule (ZMod 5) (List Bool)))
        (Schedule.compose (fun _ => ddhOTSchedule (ZMod 5))
          (maskedOTSchedule (ZMod 5) (List Bool))) i) ×
      ((i : Fin 2) → OTOut (List Bool) i) → ProbComp Bool) :
    ddhMaskedOTReceiverCost (1 : ZMod 5) 5 mask unmask samplePads S₁ S₂ () {0} x D = ⊤ :=
  dite_eq_right (by decide)

include hS₂ in
/-- **Yao's protocol over the batched masked transfer over the DDH transfer on `ZMod 5`, corrupted
evaluator.** The bound of
`Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_evaluator_le` applies at every
parameter `n ≥ 1`, for a correct garbling scheme with a projective encoding. -/
example {Fn Λ : Type} (Gs : Garbling.Scheme Fn) (hproj : Gs.encode = Garbling.projectiveEncode)
    (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n) (c : Yao.Params Gs) (Φ : Garbling.SideInfo Fn Λ)
    (S : ℕ → Garbling.PrvSimulator Λ)
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule c) (Yao.Input c) Yao.Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {1} = Yao.evaluatorSim Gs Φ S n c) (x : (i : Fin 2) → Yao.Input c i) (D : _) :=
  Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_evaluator_le hproj hcorrect hn c Φ S
    (1 : ZMod 5) 5 one_generates mask unmask samplePads T₁ hT₁ S₁ S₂ hS₂ x D

end Composition

/-! ### The key-derivation mask over the DDH transfer -/

/-- **A family of simulators of the masked transfer with `maskedOTReceiverSim` at `{1}` exists**,
so the hypothesis `hS₁` of the theorems is satisfiable. At the other coalitions the family returns
the views of one fixed execution; it only inhabits the type. -/
example : ∃ S₁ : (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (primeFields.Carrier five) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (primeFields.Carrier five)) (OTOut (List Bool)) J,
    S₁ {1} = maskedOTReceiverSim (primeFields.kdfMask constKDF five) (primeFields.kdfPads five)
      (Cslib.BitString.sampleList 2) := by
  classical
  obtain ⟨⟨v, -⟩, -⟩ := ((maskedOT (primeFields.kdfMask constKDF five)
    (primeFields.kdfMask constKDF five) (primeFields.kdfPads five)).evalWith
      (otWorld (primeFields.Carrier five)) (wordInputs false)).support_nonempty
  exact ⟨fun J => if h : J = {1} then h ▸ maskedOTReceiverSim (primeFields.kdfMask constKDF five)
      (primeFields.kdfPads five) (Cslib.BitString.sampleList 2)
    else fun _ _ => pure fun i => v i.1, dite_eq_left rfl⟩

section KDFComposition

/-- `primeFields` is reducible, so instance search sees its order at `five` unfolded and does not
find the family's instance `NeZero (F.order d)`; it is supplied from the primality of the order. -/
local instance : NeZero (primeFields.order five) := ⟨(primeFields.prime_order five).ne_zero⟩

variable
  (S₁ : (J : Finset (Fin 2)) → CoalitionSimulator
    (maskedOTSchedule (primeFields.Carrier five) (List Bool)) (OTIn (List Bool))
    (MaskedOTCoins (primeFields.Carrier five)) (OTOut (List Bool)) J)
  (hS₁ : S₁ {1} = maskedOTReceiverSim (primeFields.kdfMask constKDF five)
    (primeFields.kdfPads five) (Cslib.BitString.sampleList 2))
  (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (primeFields.Carrier five))
    (OTIn (primeFields.Carrier five)) (DDHOTCoins (primeFields.order five))
    (OTOut (primeFields.Carrier five)) J)
  (hS₂ : S₂ {1} = ddhOTReceiverSim (primeFields.generator five) (primeFields.order five))

include hS₁ hS₂ in
/-- **The hypotheses of `semiHonestAdvantage_kdfMaskedOT_ddhOT_receiver_le` are satisfiable.** At
the prime `5`, with the constant two-bit key and two-bit inputs, the advantage against a corrupted
receiver of the masked transfer over the DDH transfer is at most the key-derivation advantage of
`maskedOTReceiverToKDFDistinguisherAt` plus the expected DDH advantage. The constant key hides
nothing; the instance only witnesses the hypotheses. -/
example (σ : Bool) (n : ℕ) (D : _) :=
  primeFields.semiHonestAdvantage_kdfMaskedOT_ddhOT_receiver_le constKDF (fun _ => 2) n five
    (fun _ => rfl) S₁ hS₁ S₂ hS₂ (wordInputs σ) (by cases σ <;> rfl) D

/-- **The key-derivation cost is stated for a corrupted receiver only.** At the coalition `{0}` it
is `⊤`. -/
example (σ : Bool) (n : ℕ) (D : _) :
    primeFields.kdfDDHMaskedOTReceiverCost constKDF (fun _ => 2) n five S₂ () {0}
      (wordInputs σ) D = ⊤ :=
  dite_eq_right (by decide)

include hS₁ hS₂ in
/-- **Yao's protocol over the batched masked transfer with the key-derivation mask over the DDH
transfer at the prime `5`, corrupted evaluator.** The bound of
`Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_evaluator_le` applies at every parameter
`n ≥ 1`, for a correct garbling scheme with a projective encoding whose offered values are two
bits long. -/
example {Fn Λ : Type} (Gs : Garbling.Scheme Fn) (hproj : Gs.encode = Garbling.projectiveEncode)
    (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n) (c : Yao.Params Gs) (Φ : Garbling.SideInfo Fn Λ)
    (S : ℕ → Garbling.PrvSimulator Λ)
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule c) (Yao.Input c) Yao.Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {1} = Yao.evaluatorSim Gs Φ S n c) (x : (i : Fin 2) → Yao.Input c i)
    (hlen : ∀ (r : (i : Fin 2) → Yao.Coins i) (j : Fin c.evaluatorLen) (b : Bool),
      (Yao.transferQueries n c x r 0 j b).length = 2) (D : _) :=
  Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_evaluator_le primeFields constKDF
    (fun _ => 2) hproj hcorrect hn c Φ S five (fun _ => rfl) x hlen T₁ hT₁ S₁ hS₁ S₂ hS₂ D

/-- **The same protocol, corrupted garbler.** The statement of
`Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_garbler_eq_zero` applies at every
parameter `n ≥ 1`, for a correct garbling scheme with a projective encoding whose offered values
are two bits long, with the sender simulators at the coalition `{0}`. -/
example {Fn : Type} (Gs : Garbling.Scheme Fn) (hproj : Gs.encode = Garbling.projectiveEncode)
    (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n) (c : Yao.Params Gs)
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule c) (Yao.Input c) Yao.Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {0} = Yao.garblerSim Gs n c) (x : (i : Fin 2) → Yao.Input c i)
    (hlen : ∀ (r : (i : Fin 2) → Yao.Coins i) (j : Fin c.evaluatorLen) (b : Bool),
      (Yao.transferQueries n c x r 0 j b).length = 2)
    (R₁ : (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (primeFields.Carrier five) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (primeFields.Carrier five)) (OTOut (List Bool)) J)
    (hR₁ : R₁ {0} = maskedOTSenderSim (primeFields.kdfPads five))
    (R₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (primeFields.Carrier five))
      (OTIn (primeFields.Carrier five)) (DDHOTCoins (primeFields.order five))
      (OTOut (primeFields.Carrier five)) J)
    (hR₂ : R₂ {0} = ddhOTSenderSim (primeFields.generator five) (primeFields.order five))
    (D : _) :=
  Yao.semiHonestAdvantage_composedProtocol_kdfDDHMaskedOT_garbler_eq_zero primeFields constKDF
    (fun _ => 2) hproj hcorrect hn c five (fun _ => rfl) x hlen T₁ hT₁ R₁ hR₁ R₂ hR₂ D

end KDFComposition

/-! ### The masked transfer over the fair-coin DDH transfer -/

/-- **A family of simulators of the fair-coin DDH transfer with `ddhOTReceiverSimProb` at `{1}`
exists**, so the hypothesis `hS₂` of `semiHonestAdvantage_maskedOT_ddhOTProb_receiver_le` is
satisfiable. At the other coalitions the family returns the views of one fixed execution; it only
inhabits the type. -/
example (n : ℕ) : ∃ S₂ : (J : Finset (Fin 2)) → CoalitionSimulator
      (ddhOTSchedule (primeFields.Carrier five)) (OTIn (primeFields.Carrier five))
      (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (primeFields.Carrier five)) J,
    S₂ {1} = primeFields.ddhOTReceiverSimProb n five := by
  classical
  obtain ⟨⟨v, -⟩, -⟩ := ((primeFields.ddhOTProbProtocol n five).evalWith noOracleWorld
    (Fin.cases (motive := fun i => OTIn (primeFields.Carrier five) i)
      ((0, 0) : primeFields.Carrier five × primeFields.Carrier five)
      fun _ => false)).support_nonempty
  exact ⟨fun J => if h : J = {1} then h ▸ primeFields.ddhOTReceiverSimProb n five
    else fun _ _ => pure fun i => v i.1, dite_eq_left rfl⟩

/-- **The masked transfer of words over the fair-coin DDH transfer at the prime `5`, corrupted
receiver.** The bound for one distinguisher applies at every security parameter: the advantage is
at most the pad-hiding advantage plus the expected DDH advantage of
`maskedOTToDDHProbDistinguisher` plus `14 / 2 ^ n`. -/
example (n : ℕ) (mask unmask : primeFields.Carrier five → List Bool → List Bool)
    (samplePads : ProbComp (primeFields.Carrier five × primeFields.Carrier five))
    (S₁ : (J : Finset (Fin 2)) → CoalitionSimulator
      (maskedOTSchedule (primeFields.Carrier five) (List Bool)) (OTIn (List Bool))
      (MaskedOTCoins (primeFields.Carrier five)) (OTOut (List Bool)) J)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator
      (ddhOTSchedule (primeFields.Carrier five)) (OTIn (primeFields.Carrier five))
      (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (primeFields.Carrier five)) J)
    (hS₂ : S₂ {1} = primeFields.ddhOTReceiverSimProb n five)
    (x : (i : Fin 2) → OTIn (List Bool) i) (D : _) :=
  primeFields.semiHonestAdvantage_maskedOT_ddhOTProb_receiver_le n five mask unmask samplePads S₁
    S₂ hS₂ x D

end CslibFrontierTests.Crypto.YaoPlainDDHOT
