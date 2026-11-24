/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT

/-!
# Tests for Yao's protocol over the DDH transfer against a corrupted garbler

A client of `CslibFrontier.Crypto.Protocols.MPC.Yao.PlainDDHOT` under module encapsulation.

* The hypotheses of the corrupted-sender and corrupted-garbler theorems hold together over
  `ZMod 5` with the generator `1`: a mask of words with a left inverse exists, and families of
  simulators of `maskedOT` and of the DDH transfer whose members at `{0}` are `maskedOTSenderSim`
  and `ddhOTSenderSim` exist.
* `semiHonestAdvantage_ddhMaskedOT_sender` and `semiHonestAdvantage_ddhMaskedBatchOT_sender` apply
  over `ZMod 5`.
* `Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_garbler_eq_zero` applies over `ZMod 5`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.YaoPlainDDHOTGarbler

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC Cslib.Probability
open scoped ENNReal

/-- A mask of words by pads in `ZMod 5` with a left inverse exists, so the hypothesis `hmask` of
the theorems is satisfiable. This mask hides nothing; it only witnesses the hypothesis. -/
example : ∃ mask unmask : ZMod 5 → List Bool → List Bool, ∀ r m, unmask r (mask r m) = m :=
  ⟨fun _ m => m.reverse, fun _ c => c.reverse, fun _ m => m.reverse_reverse⟩

/-- **A family of simulators of `maskedOT` with `maskedOTSenderSim` at `{0}` exists**, so the
hypothesis `hS₁` of the theorems is satisfiable. At the other coalitions the family returns the
views of one fixed execution; it only inhabits the type. -/
example (mask unmask : ZMod 5 → List Bool → List Bool)
    (samplePads : ProbComp (ZMod 5 × ZMod 5)) :
    ∃ S₁ : (J : Finset (Fin 2)) → CoalitionSimulator (maskedOTSchedule (ZMod 5) (List Bool))
        (OTIn (List Bool)) (MaskedOTCoins (ZMod 5)) (OTOut (List Bool)) J,
      S₁ {0} = maskedOTSenderSim samplePads := by
  classical
  obtain ⟨⟨v, -⟩, -⟩ := ((maskedOT mask unmask samplePads).evalWith (otWorld (ZMod 5))
    (Fin.cases (motive := fun i => OTIn (List Bool) i) (([], []) : List Bool × List Bool)
      fun _ => false)).support_nonempty
  exact ⟨fun J => if h : J = {0} then h ▸ maskedOTSenderSim samplePads
    else fun _ _ => pure fun i => v i.1, dite_eq_left rfl⟩

/-- **A family of simulators of the DDH transfer with `ddhOTSenderSim` at `{0}` exists**, so the
hypothesis `hS₂` of the theorems is satisfiable. At the other coalitions the family returns the
views of one fixed execution; it only inhabits the type. -/
example : ∃ S₂ : (J : Finset (Fin 2)) →
      CoalitionSimulator (ddhOTSchedule (ZMod 5)) (OTIn (ZMod 5)) (DDHOTCoins 5) (OTOut (ZMod 5)) J,
    S₂ {0} = ddhOTSenderSim (1 : ZMod 5) 5 := by
  classical
  obtain ⟨⟨v, -⟩, -⟩ := ((ddhOTProtocol (1 : ZMod 5) 5).evalWith noOracleWorld
    (Fin.cases (motive := fun i => OTIn (ZMod 5) i) ((0, 0) : ZMod 5 × ZMod 5)
      fun _ => false)).support_nonempty
  exact ⟨fun J => if h : J = {0} then h ▸ ddhOTSenderSim (1 : ZMod 5) 5
    else fun _ _ => pure fun i => v i.1, dite_eq_left rfl⟩

section Composition

variable (mask unmask : ZMod 5 → List Bool → List Bool)
  (hmask : ∀ r m, unmask r (mask r m) = m) (samplePads : ProbComp (ZMod 5 × ZMod 5))
  (S₁ : (J : Finset (Fin 2)) → CoalitionSimulator (maskedOTSchedule (ZMod 5) (List Bool))
    (OTIn (List Bool)) (MaskedOTCoins (ZMod 5)) (OTOut (List Bool)) J)
  (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (ZMod 5)) (OTIn (ZMod 5))
    (DDHOTCoins 5) (OTOut (ZMod 5)) J)
  (hS₁ : S₁ {0} = maskedOTSenderSim samplePads)
  (hS₂ : S₂ {0} = ddhOTSenderSim (1 : ZMod 5) 5)

include hmask hS₁ hS₂ in
/-- **The masked transfer of words over the DDH transfer on `ZMod 5`, corrupted sender.** The
advantage is zero on every input. -/
example (x : (i : Fin 2) → OTIn (List Bool) i) (D : _) :
    semiHonestAdvantage (ddhMaskedOT (1 : ZMod 5) 5 mask unmask samplePads) noOracleWorld
      (otFunctionality (List Bool)) {0} (ddhMaskedOTSim mask unmask samplePads S₁ S₂ {0}) x D =
      0 :=
  semiHonestAdvantage_ddhMaskedOT_sender (1 : ZMod 5) 5 mask unmask samplePads S₁ S₂ hS₁ hS₂ x
    (fun r => hmask r _) D

include hmask hS₁ hS₂ in
/-- **The batched masked transfer of words over the DDH transfer on `ZMod 5`, corrupted sender.**
The advantage is zero for every number of transfers. -/
example (k : ℕ) (x : (i : Fin 2) → (batchOTSpec k (List Bool)).Query () i) (D : _) :
    semiHonestAdvantage (ddhMaskedBatchOT k (1 : ZMod 5) 5 mask unmask samplePads) noOracleWorld
      (batchOTFunctionality k (List Bool)) {0}
      (ddhMaskedBatchOTSim k mask unmask samplePads S₁ S₂ {0}) x D = 0 :=
  semiHonestAdvantage_ddhMaskedBatchOT_sender k (1 : ZMod 5) 5 mask unmask hmask samplePads S₁ S₂
    hS₁ hS₂ x D

include hmask hS₁ hS₂ in
/-- **Yao's protocol over the batched masked transfer over the DDH transfer on `ZMod 5`, corrupted
garbler.** `Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_garbler_eq_zero` applies at every
parameter `n ≥ 1`, for a correct garbling scheme with a projective encoding: the advantage is
zero. -/
example {Fn : Type} (Gs : Garbling.Scheme Fn) (hproj : Gs.encode = Garbling.projectiveEncode)
    (hcorrect : Gs.Correct) {n : ℕ} (hn : 0 < n) (c : Yao.Params Gs)
    (T₁ : (I : Finset (Fin 2)) →
      CoalitionSimulator (Yao.schedule c) (Yao.Input c) Yao.Coins (fun _ => List Bool) I)
    (hT₁ : T₁ {0} = Yao.garblerSim Gs n c) (x : (i : Fin 2) → Yao.Input c i) (D : _) :
    semiHonestAdvantage
      (Yao.composedProtocol Gs n c
        (ddhMaskedBatchOT c.evaluatorLen (1 : ZMod 5) 5 mask unmask samplePads))
      noOracleWorld (Yao.functionality Gs c) {0}
      (composeSim (Yao.protocol Gs n c) T₁
        (fun _ => ddhMaskedBatchOTSim c.evaluatorLen mask unmask samplePads S₁ S₂) {0})
      x D = 0 :=
  Yao.semiHonestAdvantage_composedProtocol_ddhMaskedOT_garbler_eq_zero hproj hcorrect hn c
    (1 : ZMod 5) 5 mask unmask hmask samplePads T₁ hT₁ S₁ S₂ hS₁ hS₂ x D

end Composition

end CslibFrontierTests.Crypto.YaoPlainDDHOTGarbler
