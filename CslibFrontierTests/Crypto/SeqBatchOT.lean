/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Protocols.MPC.BatchOT.Sequential
import CslibFrontier.Crypto.Protocols.MPC.DDHOT.Family
import CslibFrontier.Crypto.Protocols.MPC.IKNP
import CslibFrontier.Crypto.Protocols.MPC.Yao.PlainComposition

/-!
# Tests for the batched transfer from sequential single transfers

A client of `CslibFrontier.Crypto.Protocols.MPC.BatchOT.Sequential` under module encapsulation.

* The choice-bit convention is checked on two transfers of natural numbers with four distinct
  offered values: the choice bit `true` selects the value offered at `true`, which the sender
  submits as the second component of its pair, and the receiver's output lists the answers in the
  order of the transfers. A transposed pair or a reversed order fails these checks.
* The boundary `k = 0` has the empty schedule, and `k` transfers have `k` oracle rounds.
* In the single-transfer hybrid model every distinguisher has advantage zero against
  `seqBatchOT k M`, for every coalition.
* `semiHonestAdvantage_seqBatchOT_compose_le_mul` is applied to a plain-model single transfer that
  the library already has: the three-message DDH transfer over `ZMod 5`, which is perfectly private
  against a corrupted sender. The batched transfer over it then has advantage zero against a
  corrupted sender, for every number of transfers. So the hypothesis of that theorem is satisfiable
  by a protocol without oracles, and its bound is attained with value zero.
* `seqBatchOT` composes with the fair-coin DDH transfer `ddhOTProbProtocol` of `ddhOTProbFamily` as
  it stands, giving a plain-model protocol for the batched transfer of group elements, and
  `semiHonestAdvantage_seqBatchOT_compose_le` applies to it for any simulators of the DDH transfer.
* With words as values, `seqBatchOT` over any single transfer of words is a transfer subprotocol
  of `Yao.composedProtocol`: it has the input and output types of `batchOTSpec k (List Bool)`.
* With `m`-bit strings as values, `seqBatchOT κ (BitString m)` over any single transfer of `m`-bit
  strings is a subprotocol for the base-transfer oracle of the IKNP extension `iknpProtocol`.
-/

-- This regression module checks ordinary imports and exports no test fixtures.
set_option linter.privateModule false

namespace CslibFrontierTests.Crypto.SeqBatchOT

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.MPC Cslib.Probability
open scoped ENNReal

/-- The sender's values in two transfers: transfer `j` offers `10 * j` at `false` and `10 * j + 1`
at `true`. -/
def offers : Fin 2 → Bool → ℕ := fun j b => 10 * j.val + if b then 1 else 0

/-- The receiver's choice bits: `true` in transfer `0` and `false` in transfer `1`. -/
def choices : Fin 2 → Bool := fun j => decide (j = 0)

/-- The input pair of the two transfers. -/
def inputs : (i : Fin 2) → (batchOTSpec 2 ℕ).Query () i :=
  Fin.cases offers fun _ => choices

/-- In transfer `0` the sender submits the pair `(0, 1)`: the value offered at `false` first. -/
example : batchOTQueryAt (0 : Fin 2) 0 (inputs 0) = ((0, 1) : ℕ × ℕ) := rfl

/-- In transfer `1` the sender submits the pair `(10, 11)`. -/
example : batchOTQueryAt (1 : Fin 2) 0 (inputs 0) = ((10, 11) : ℕ × ℕ) := rfl

/-- The receiver submits its choice bits in the order of the transfers. -/
example : batchOTQueryAt (0 : Fin 2) 1 (inputs 1) = true ∧
    batchOTQueryAt (1 : Fin 2) 1 (inputs 1) = false := ⟨rfl, rfl⟩

/-- The single transfers answer `1` (the value at `true` of transfer `0`) and `10` (the value at
`false` of transfer `1`). -/
example : otOutputs (fun s => batchOTQueryAt (0 : Fin 2) s (inputs s)) 1 = (1 : ℕ) ∧
    otOutputs (fun s => batchOTQueryAt (1 : Fin 2) s (inputs s)) 1 = (10 : ℕ) := ⟨rfl, rfl⟩

/-- The execution of `seqBatchOT 2 ℕ` on `inputs` is deterministic, and the receiver outputs `1`
and `10`, in the order of the transfers. -/
example : ((seqBatchOT 2 ℕ).evalWith (otWorld ℕ) inputs).map (fun r => (r.2 1 0, r.2 1 1)) =
    PMF.pure ((1, 10) : ℕ × ℕ) := by
  rw [evalWith_seqBatchOT, PMF.pure_map]
  rfl

/-- No transfers: the schedule is empty. -/
example (M : Type) : seqBatchOTSchedule 0 M = [] := rfl

/-- `k` transfers take `k` oracle rounds. -/
example (k : ℕ) (M : Type) : (seqBatchOTSchedule k M).length = k := List.length_replicate

/-- In the single-transfer hybrid model, every distinguisher has advantage zero against
`seqBatchOT k M`, for every coalition, including both parties and none. -/
example (k : ℕ) (M : Type) (I : Finset (Fin 2)) (x : (i : Fin 2) → (batchOTSpec k M).Query () i)
    (D : ((i : I) → PartyView ((batchOTSpec k M).Query ()) (fun _ => Unit)
        (seqBatchOTSchedule k M) i) × ((i : Fin 2) → (batchOTSpec k M).Answer () i) →
      ProbComp Bool) :
    semiHonestAdvantage (seqBatchOT k M) (otWorld M) (batchOTFunctionality k M) I
      (seqBatchOTSim k M I) x D = 0 :=
  (perfectSemiHonestPrivate_seqBatchOT k M).semiHonestAdvantage_eq_zero I x D

/-- **The batched transfer over the DDH transfer on `ZMod 5`, corrupted sender.** The three-message
DDH transfer is perfectly private against a corrupted sender (`semiHonestAdvantage_ddhOT_sender`),
so the hypothesis of `semiHonestAdvantage_seqBatchOT_compose_le_mul` holds with `ε = 0` for the
coalition `{0}`, for any family of simulators whose sender simulator is `ddhOTSenderSim`. The
plain-model batched transfer of `k` values then has advantage zero against a corrupted sender. -/
example (k : ℕ)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (ZMod 5)) (OTIn (ZMod 5))
      (DDHOTCoins 5) (OTOut (ZMod 5)) J)
    (hS : S₂ {0} = ddhOTSenderSim (1 : ZMod 5) 5)
    (x : (i : Fin 2) → (batchOTSpec k (ZMod 5)).Query () i)
    (D : ((i : ({0} : Finset (Fin 2))) → PartyView ((batchOTSpec k (ZMod 5)).Query ())
        (Schedule.ComposedCoins (fun _ => DDHOTCoins 5) (fun _ => Unit)
          (seqBatchOTSchedule k (ZMod 5)))
        (Schedule.compose (fun _ => ddhOTSchedule (ZMod 5)) (seqBatchOTSchedule k (ZMod 5))) i) ×
      ((i : Fin 2) → (batchOTSpec k (ZMod 5)).Answer () i) → ProbComp Bool) :
    semiHonestAdvantage ((seqBatchOT k (ZMod 5)).compose fun _ => ddhOTProtocol (1 : ZMod 5) 5)
      noOracleWorld (batchOTFunctionality k (ZMod 5)) {0}
      (composeSim (seqBatchOT k (ZMod 5)) (seqBatchOTSim k (ZMod 5) {0}) (fun _ => S₂)) x D =
      0 := by
  have h := semiHonestAdvantage_seqBatchOT_compose_le_mul k (ZMod 5) noOracleWorld
    (ddhOTProtocol (1 : ZMod 5) 5) S₂ {0} 0
    (fun q D' => by rw [hS, semiHonestAdvantage_ddhOT_sender (1 : ZMod 5) 5 q D', ENNReal.coe_zero])
    x D
  rw [mul_zero, nonpos_iff_eq_zero, ENNReal.coe_eq_zero] at h
  exact h

/-- **The batched transfer over the fair-coin DDH transfer of `ddhOTProbFamily`.** At every security
parameter `n` and group description `d`, `seqBatchOT` composes with `ddhOTProbProtocol` as it
stands, giving a plain-model protocol for `k` transfers of group elements, and
`semiHonestAdvantage_seqBatchOT_compose_le` bounds its semi-honest advantage by the hybrid bound
over the `k` DDH transfers, for any simulators of the DDH transfer. -/
example (F : PrimeOrderGroupFamily) (k n : ℕ) (d : F.Desc)
    (S₂ : (J : Finset (Fin 2)) → CoalitionSimulator (ddhOTSchedule (F.Carrier d))
      (OTIn (F.Carrier d)) (DDHOTCoinsWith DDHOTSenderBitCoins (List Bool)) (OTOut (F.Carrier d)) J)
    (I : Finset (Fin 2)) (x : (i : Fin 2) → (batchOTSpec k (F.Carrier d)).Query () i)
    (D : ((i : I) → PartyView ((batchOTSpec k (F.Carrier d)).Query ())
        (Schedule.ComposedCoins (fun _ => DDHOTCoinsWith DDHOTSenderBitCoins (List Bool))
          (fun _ => Unit) (seqBatchOTSchedule k (F.Carrier d)))
        (Schedule.compose (fun _ => ddhOTSchedule (F.Carrier d))
          (seqBatchOTSchedule k (F.Carrier d))) i) ×
      ((i : Fin 2) → (batchOTSpec k (F.Carrier d)).Answer () i) → ProbComp Bool) :
    (semiHonestAdvantage ((seqBatchOT k (F.Carrier d)).compose fun _ => F.ddhOTProbProtocol n d)
        noOracleWorld (batchOTFunctionality k (F.Carrier d)) I
        (composeSim (seqBatchOT k (F.Carrier d)) (seqBatchOTSim k (F.Carrier d) I) (fun _ => S₂))
        x D : ℝ≥0∞) ≤
      Composition.replacementBound (otWorld (F.Carrier d)) noOracleWorld
        (fun _ => F.ddhOTProbProtocol n d) (fun _ => S₂) I (seqBatchOT k (F.Carrier d)).steps
        (fun i => (x i, ()))
        (fun res => D (fun i : I => ⟨x i.1, ((), (res.1 i).1), (res.1 i).2⟩, res.2)) :=
  semiHonestAdvantage_seqBatchOT_compose_le k (F.Carrier d) noOracleWorld
    (F.ddhOTProbProtocol n d) S₂ I x D

/-- **The batched transfer of words as the transfer subprotocol of Yao's protocol.** For every
protocol `Sub` for a single transfer of words, `seqBatchOT` over `Sub` has the input and output
types of `batchOTSpec c.evaluatorLen (List Bool)` and so is accepted by `Yao.composedProtocol`. -/
noncomputable example {Fn : Type} (G : Garbling.Scheme Fn) (n : ℕ) (c : Yao.Params G)
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (Sub : Protocol 2 spec₂ sc₂ (OTIn (List Bool)) Coins₂ (OTOut (List Bool))) :=
  Yao.composedProtocol G n c ((seqBatchOT c.evaluatorLen (List Bool)).compose fun _ => Sub)

/-- **The batched transfer as the base transfers of the IKNP extension.** `iknpProtocol H` takes
`batchOTSpec κ (BitString m)` as its base-transfer oracle. For every protocol `Sub` for a single
transfer of `m`-bit strings, `seqBatchOT κ (BitString m)` over `Sub` is a subprotocol for that
oracle, so the composition is a protocol for `m` transfers of values in `L` in the model of
`Sub`. -/
noncomputable example {κ m : ℕ} {L : Type} [AddCommGroup L] (H : Fin m → BitString κ → L)
    {spec₂ : MultiOracleSpec} {sc₂ : Schedule 2 spec₂} {Coins₂ : Fin 2 → Type}
    (Sub : Protocol 2 spec₂ sc₂ (OTIn (BitString m)) Coins₂ (OTOut (BitString m))) :=
  (iknpProtocol H).compose fun _ => (seqBatchOT κ (BitString m)).compose fun _ => Sub

end CslibFrontierTests.Crypto.SeqBatchOT
