/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.LogSpace.Randomized.ConfigurationReader
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.StoredLoop
import CslibFrontier.Foundations.Data.Nat.FindCode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.FindCode
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.InSpace.InputBit
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.BitsGetElem
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.CounterProgram.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Correctness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.ConfigurationGraph.Deterministic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.Words
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.NatLength
import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure

/-!
# Replaying a fair-coin machine on computed coins, in space

A fair-coin machine (`Turing.MultiTapePTM`) remembers between coins only its view, and under a
logarithmic space bound the compact configuration graph (`Turing.MultiTapeNTM.ConfigurationGraph`)
packs every reachable view into an ID of `O(log n)` bits. This module replays such a machine
deterministically on coins that are themselves computed on demand. A stored loop
(`Turing.MultiTapeTM.ComputableInSpace.loopWith`) holds the number of coins read, the ID of the
current view and the input position it reads; a round computes the next coin, reads the one input
bit at that position, and moves to the ID of the coin successor. The coin successor is found by
searching the IDs below the size of the compact graph for the target of the edge of the machine
with that coin fixed. That machine is deterministic, so the target is unique
(`Turing.MultiTapeNTM.ConfigurationGraph.edgeWithSymbol_target_unique`), and on fitting views it is
the ID of the view that `Turing.MultiTapePTM.viewCoinStep` reaches.

So whether the machine accepts a computed coin string of computed length is computable within the
space of the coins and of their number, plus `O(log n)` for the IDs
(`Turing.MultiTapePTM.replayCoins_inSpace`). When the input of the machine is the second component
of a pair whose first component is stored, as with a seed of a pseudorandom generator, the
predicate is in the context form of `Turing.MultiTapeTM.ComputableInSpace.countWith`
(`Turing.MultiTapePTM.replayCoins_inSpace_context`). This is the replay step of Nisan's
deterministic simulation of randomized logarithmic space in space `O(log² n)` [Nisan1992]. It
makes no claim about which coins are replayed and does not derandomize anything by itself.

## Main results

* `Turing.MultiTapePTM.replayCoins_inSpace`: replaying a logspace fair-coin machine on computed
  coins, within the space of the coins plus `O(log n)`.
* `Turing.MultiTapePTM.replayCoins_inSpace_context`: the same with a stored first component of
  the input, in context form.

## References

* [N. Nisan, *Pseudorandom generators for space-bounded computation*][Nisan1992]
-/

public section

namespace Turing.MultiTapePTM.ConfigurationGraph

open MultiTapeNTM.ConfigurationGraph
open Cslib.Turing MultiTapeTM ComputableInSpace

variable {k : ℕ} {State : Type} [Fintype State]

/-- **The coin successor of a compact configuration ID**: the first ID below `vertexBound B` that
the compact graph of the machine with its coin fixed to `bit` joins to `u`, on input length `n` and
supplied input symbol `symbol`; `0` when there is none. On the ID of a view whose coin successor
fits the radix, it is the ID of that successor (`coinSuccID_vertexID`). -/
private noncomputable def coinSuccID (machine : MultiTapePTM k Bool State) (B n u : ℕ)
    (symbol : Option Bool) (bit : Bool) : ℕ :=
  (Cslib.findCode
    (fun v => edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B n u v symbol)
    0 (vertexBound (k := k) B)).getD 0

/-- **The coin successor of an ID is the ID of the coin successor**: on the ID of a view `a`
fitting the radix, reading the input bit at its `queryIndex`, the coin successor is the ID of
`machine.viewCoinStep a bit`, when that view fits the radix too. -/
private theorem coinSuccID_vertexID (machine : MultiTapePTM k Bool State) {B : ℕ}
    {a : FiniteCfg k Bool State} (bit : Bool) (hfitA : Fits B (registers a))
    (hfitB : Fits B (registers (machine.viewCoinStep a bit))) :
    coinSuccID machine B a.input.length (vertexID B a)
        a.input[queryIndex (k := k) B (vertexID B a)]? bit =
      vertexID B (machine.viewCoinStep a bit) := by
  have hedge : edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B a.input.length
      (vertexID B a) (vertexID B (machine.viewCoinStep a bit))
      a.input[queryIndex (k := k) B (vertexID B a)]? = true :=
    edge_complete hfitA hfitB ((viewStep_withCoin_iff machine bit).mpr rfl)
  have hmem : vertexID B (machine.viewCoinStep a bit) ∈
      List.range' 0 (vertexBound (k := k) B) :=
    List.mem_range'_1.mpr ⟨Nat.zero_le _, by simpa using vertexID_lt hfitB⟩
  rw [coinSuccID, Cslib.findCode_eq]
  cases hx : (List.range' 0 (vertexBound (k := k) B)).find? fun v =>
      edgeWithSymbol (machine.withCoin bit).toTM.toMultiTapeNTM B a.input.length (vertexID B a) v
        a.input[queryIndex (k := k) B (vertexID B a)]? with
  | none => exact absurd hedge (List.find?_eq_none.mp hx _ hmem)
  | some x =>
    have hpx := List.find?_some hx
    exact edgeWithSymbol_target_unique _ hpx hedge

/-- The arguments of the coin successor. -/
private structure SuccQuery where
  /-- The radix. -/
  radix : ℕ
  /-- The input length. -/
  len : ℕ
  /-- The source ID. -/
  id : ℕ
  /-- The supplied input symbol. -/
  symbol : Option Bool
  /-- The coin. -/
  bit : Bool

/-- Arguments of the coin successor, as their fields. -/
private enc_structure encSuccQuery : SuccQuery where
  radix : encNat, len : encNat, id : encNat, symbol : (encOption encBool), bit : encBool

/-- The edge test of the coin successor, within space linear in its arguments. -/
private theorem coinEdge_inSpace (machine : MultiTapePTM k Bool State) :
    ComputableInSpace
      (fun p : SuccQuery × ℕ => edgeWithSymbol (machine.withCoin p.1.bit).toTM.toMultiTapeNTM
        p.1.radix p.1.len p.1.id p.2 p.1.symbol)
      (encPair encSuccQuery encNat) encBool fun p => (encPair encSuccQuery encNat p).length := by
  have hq := fst encSuccQuery encNat
  have hv := snd encSuccQuery encNat
  have he (bit : Bool) := edgeWithSymbol_budget (machine.withCoin bit).toTM.toMultiTapeNTM
    (encSuccQuery_radix_budget hq) (encSuccQuery_len_budget hq) (encSuccQuery_id_budget hq) hv
    (encSuccQuery_symbol_budget hq)
  refine (budget_ite (encSuccQuery_bit_budget hq) (he true) (he false)).of_enc_eq fun p => ?_
  rcases p with ⟨⟨B, n, u, s, b⟩, v⟩
  cases b <;> rfl

variable {α : Type} {enc : α ↪ List Bool} {S : α → ℕ}
  {B n u : α → ℕ} {symbol : α → Option Bool} {bit : α → Bool}

/-- The coin successor preserves any common space budget of its arguments: a search over the
IDs below `vertexBound B`, testing each with `edgeWithSymbol_budget`. -/
private theorem coinSuccID_budget (machine : MultiTapePTM k Bool State)
    (hB : ComputableInSpace B enc encNat S)
    (hn : ComputableInSpace n enc encNat S)
    (hu : ComputableInSpace u enc encNat S)
    (hs : ComputableInSpace symbol enc (encOption encBool) S)
    (hbit : ComputableInSpace bit enc encBool S) :
    ComputableInSpace (fun a => coinSuccID machine (B a) (n a) (u a) (symbol a) (bit a))
      enc encNat S :=
  (budget_optionGetD 0 (budget_comp_linear (findCode (coinEdge_inSpace machine))
    (budget_prod (encSuccQuery_mk_budget hB hn hu hs hbit)
      (budget_prod (budget_const 0) (vertexBound_budget (k := k) hB))))).of_enc_eq fun _ => rfl

end Turing.MultiTapePTM.ConfigurationGraph

namespace Turing.MultiTapePTM

open MultiTapeNTM.ConfigurationGraph ConfigurationGraph
open Cslib.Turing MultiTapeTM ComputableInSpace

/-- The registers of the replay loop. -/
private structure ReplayRegs where
  /-- The number of coins to read. -/
  bound : ℕ
  /-- The input length. -/
  len : ℕ
  /-- The radix of the compact IDs. -/
  radix : ℕ
  /-- The number of coins read. -/
  idx : ℕ
  /-- The compact ID of the current view. -/
  id : ℕ
  /-- The input position read by the current view. -/
  query : ℕ

/-- Registers of the replay loop, as their fields. -/
private enc_structure encReplayRegs : ReplayRegs logspace where
  bound : encNat, len : encNat, radix : encNat, idx : encNat, id : encNat, query : encNat

variable {k : ℕ} {State : Type} {β : Type}

/-- The body of the replay loop: read the next coin and move to the coin successor, or stop
after the last coin. -/
private noncomputable def replayStep [Fintype State] (machine : MultiTapePTM k Bool State)
    (w : β → List Bool) (coin : ℕ × β → Bool) (q : ReplayRegs × β) : Option ReplayRegs :=
  if q.1.idx < q.1.bound then
    some ⟨q.1.bound, q.1.len, q.1.radix, q.1.idx + 1,
      coinSuccID machine q.1.radix q.1.len q.1.id (w q.2)[q.1.query]? (coin (q.1.idx, q.2)),
      queryIndex (k := k) q.1.radix
        (coinSuccID machine q.1.radix q.1.len q.1.id (w q.2)[q.1.query]? (coin (q.1.idx, q.2)))⟩
  else none

/-- The body of the replay loop in context form. -/
private theorem replayStep_inSpace [Fintype State] (machine : MultiTapePTM k Bool State)
    {encB : β ↪ List Bool} {w : β → List Bool} {coin : ℕ × β → Bool} {S : β → ℕ}
    (hbit : ComputableInSpace (fun q : ℕ × β => (w q.2)[q.1]?) (encPair encNat encB)
      (encOption encBool) fun q => (encNat q.1).length + S q.2)
    (hcoin : ComputableInSpace coin (encPair encNat encB) encBool
      fun q => (encNat q.1).length + S q.2)
    (hlog : ∀ b, Nat.log2 (encB b).length ≤ S b) :
    ComputableInSpace (replayStep machine w coin) (encPair encReplayRegs encB)
      (encOption encReplayRegs) fun q => (encReplayRegs q.1).length + S q.2 := by
  have hreg : ComputableInSpace (fun q : ReplayRegs × β => q.1) (encPair encReplayRegs encB)
      encReplayRegs fun q => (encReplayRegs q.1).length + S q.2 :=
    ((ComputableInLogSpace.fst encReplayRegs encB).inSpace_context
      (.of_le fun _ => Nat.le_add_right _ _)).mono_le fun q => by
        have := hlog q.2
        omega
  have hsym : ComputableInSpace (fun q : ReplayRegs × β => (w q.2)[q.1.query]?)
      (encPair encReplayRegs encB) (encOption encBool)
      fun q => (encReplayRegs q.1).length + S q.2 :=
    hbit.comp_logSpace_context (f := fun q : ReplayRegs × β => (q.1.query, q.2)) (by fun_prop)
      (.of_le fun q => by
        simp only [encReplayRegs_apply, encReplayRegsFields, length_encPair]; omega)
      hlog
  have hc : ComputableInSpace (fun q : ReplayRegs × β => coin (q.1.idx, q.2))
      (encPair encReplayRegs encB) encBool fun q => (encReplayRegs q.1).length + S q.2 :=
    hcoin.comp_logSpace_context (f := fun q : ReplayRegs × β => (q.1.idx, q.2)) (by fun_prop)
      (.of_le fun q => by
        simp only [encReplayRegs_apply, encReplayRegsFields, length_encPair]; omega)
      hlog
  have hbound := encReplayRegs_bound_budget hreg
  have hlen := encReplayRegs_len_budget hreg
  have hradix := encReplayRegs_radix_budget hreg
  have hidx := encReplayRegs_idx_budget hreg
  have hu := coinSuccID_budget machine hradix hlen (encReplayRegs_id_budget hreg) hsym hc
  exact (budget_ite (budget_natLt hidx hbound)
    (budget_optionSome (encReplayRegs_mk_budget hbound hlen hradix (budget_natSucc hidx) hu
      (queryIndex_budget (k := k) hradix hu)))
    (budget_const none)).of_enc_eq fun q => by
      unfold replayStep
      by_cases h : q.1.idx < q.1.bound <;> simp [h]

/-- The view after the first `j` coins. -/
private noncomputable def replayView (machine : MultiTapePTM k Bool State) (w : β → List Bool)
    (coin : ℕ × β → Bool) (b : β) (j : ℕ) : FiniteCfg k Bool State :=
  ((List.range j).map fun i => coin (i, b)).foldl machine.viewCoinStep
    (machine.toNTM.initView (w b))

/-- The registers of the replay loop after the first `j` coins. -/
private noncomputable def replayRegsAt [Fintype State] (machine : MultiTapePTM k Bool State)
    (c : ℕ) (w : β → List Bool) (L : β → ℕ) (coin : ℕ × β → Bool) (b : β) (j : ℕ) :
    ReplayRegs :=
  ⟨L b, (w b).length, radix (radixExponent State c) (w b).length, j,
    vertexID (radix (radixExponent State c) (w b).length) (replayView machine w coin b j),
    queryIndex (k := k) (radix (radixExponent State c) (w b).length)
      (vertexID (radix (radixExponent State c) (w b).length) (replayView machine w coin b j))⟩

/-- The logarithm of a successor exceeds the logarithm by at most one. -/
private theorem log2_succ_le (n : ℕ) : Nat.log2 (n + 1) ≤ Nat.log2 n + 1 := by
  simpa only [Nat.log2_eq_log_two] using Nat.log_add_one_le 2 n

/-- **Replaying a fair-coin machine on computed coins, in space.** Let the machine run within
space `c (log₂ |w b| + 1)` on the input `w b`, and let the input length, the input bit at a stored
position, the number `L b` of coins and the coin `coin (j, b)` at a stored index `j` be computable
within `S b` beyond their stored arguments, where `S b` is at least the logarithms of `|encB b|` and
of `|w b|`. Then whether the replay of the coins `coin (0, b), …, coin (L b - 1, b)` from the
initial configuration on `w b` ends halted with output `[true]` is computable within
`S b + log₂ |encB b|`. No halting time is assumed; the predicate is the acceptance of
`Turing.MultiTapePTM.acceptNisanSeeds` on the given coins. -/
theorem replayCoins_inSpace [Finite State] (machine : MultiTapePTM k Bool State) (c : ℕ)
    {encB : β ↪ List Bool} {w : β → List Bool} {L : β → ℕ} {coin : ℕ × β → Bool} {S : β → ℕ}
    (hs : ∀ b, machine.toNTM.RunsInSpace (w b) (c * (Nat.log2 (w b).length + 1)))
    (hlen : ComputableInSpace (fun b => (w b).length) encB encNat S)
    (hbit : ComputableInSpace (fun q : ℕ × β => (w q.2)[q.1]?) (encPair encNat encB)
      (encOption encBool) fun q => (encNat q.1).length + S q.2)
    (hL : ComputableInSpace L encB encNat S)
    (hcoin : ComputableInSpace coin (encPair encNat encB) encBool
      fun q => (encNat q.1).length + S q.2)
    (hlog : ∀ b, Nat.log2 (encB b).length ≤ S b)
    (hlogw : ∀ b, Nat.log2 (w b).length ≤ S b) :
    ComputableInSpace (fun b => decide
      ((machine.stepCoins (List.ofFn fun j : Fin (L b) => coin (j, b))
          (machine.toNTM.initCfg (w b))).Halted ∧
        (machine.stepCoins (List.ofFn fun j : Fin (L b) => coin (j, b))
          (machine.toNTM.initCfg (w b))).output = [true]))
      encB encBool fun b => S b + Nat.log2 (encB b).length := by
  have := Fintype.ofFinite State
  have hreach (b : β) (j : ℕ) : Relation.ReflTransGen machine.toNTM.ViewStep
      (machine.toNTM.initView (w b)) (replayView machine w coin b j) :=
    reflTransGen_viewStep_toNTM_iff.mpr ⟨_, rfl⟩
  have hfit (b : β) (j : ℕ) :
      Fits (radix (radixExponent State c) (w b).length)
        (registers (replayView machine w coin b j)) :=
    fits_of_runsInSpace c (hs b) (hreach b j)
  have hinput (b : β) (j : ℕ) : (replayView machine w coin b j).input = w b :=
    input_of_reachable (hreach b j)
  have hview (b : β) (j : ℕ) : replayView machine w coin b (j + 1) =
      machine.viewCoinStep (replayView machine w coin b j) (coin (j, b)) := by
    simp only [replayView, List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.foldl_append, List.foldl_cons, List.foldl_nil]
  -- the start registers
  have hB := radix_budget (radixExponent State c) hlen
  have hstart := startID_budget machine.toNTM hB
  have hinit := encReplayRegs_mk_budget hL hlen hB (budget_const 0) hstart
    (queryIndex_budget (k := k) hB hstart)
  -- the bound on the registers along the run
  obtain ⟨cL, hcL⟩ := hL.length_le
  set K := cL + (radixExponent State c + 1) +
    (radixExponent State c * Fintype.card (Register k) + 1) + 2 with hK
  have hT (b : β) (j : ℕ) (hj : j ≤ L b) :
      (encReplayRegs (replayRegsAt machine c w L coin b j)).length + S b ≤
        11 * (K * (S b + 2)) + 5 + S b := by
    have hℓ := hlogw b
    have h₁ : (encNat (L b)).length ≤ K * (S b + 2) :=
      (hcL b).trans (Nat.mul_le_mul (by omega) (Nat.succ_le_succ (Nat.le_succ _)))
    have h₂ : (encNat j).length ≤ K * (S b + 2) := (length_encNat_mono hj).trans h₁
    have h₃ : (encNat (w b).length).length ≤ K * (S b + 2) :=
      (length_encNat_le_of_le_pow (N := (w b).length) (d := 1) (by simp)).trans
        (Nat.mul_le_mul (by omega) (Nat.succ_le_succ (hℓ.trans (Nat.le_succ _))))
    have h₄ : (encNat (radix (radixExponent State c) (w b).length)).length ≤ K * (S b + 2) :=
      (length_encNat_le_of_le_pow_add_two le_rfl).trans
        (Nat.mul_le_mul (by omega) (Nat.add_le_add_right hℓ 2))
    have h₅ : (encNat (vertexID (radix (radixExponent State c) (w b).length)
        (replayView machine w coin b j))).length ≤ K * (S b + 2) :=
      (length_vertexID_le_of_runsInSpace c (hs b) (hreach b j)).trans
        (Nat.mul_le_mul (by omega)
          (Nat.succ_le_succ ((log2_succ_le _).trans (Nat.add_le_add_right hℓ 1))))
    have hq : queryIndex (k := k) (radix (radixExponent State c) (w b).length)
        (vertexID (radix (radixExponent State c) (w b).length) (replayView machine w coin b j)) ≤
          ((w b).length + 2) ^ 1 := by
      have hpos := (replayView machine w coin b j).inputPos.isLt
      have hlen := congrArg List.length (hinput b j)
      simp only [queryIndex, readRegisters_vertexID (hfit b j), registers, pow_one]
      omega
    have h₆ : _ ≤ K * (S b + 2) := (length_encNat_le_of_le_pow_add_two hq).trans
      (Nat.mul_le_mul (by omega) (Nat.add_le_add_right hℓ 2))
    simp only [replayRegsAt, encReplayRegs_apply, encReplayRegsFields, length_encPair]
    omega
  have hloop := ComputableInSpace.loopWith (step := replayStep machine w coin)
    (T := fun q => (encReplayRegs q.1).length + S q.2)
    (B := fun b => 11 * (K * (S b + 2)) + 5 + S b)
    (replayRegsAt machine c w L coin) L hinit (replayStep_inSpace machine hbit hcoin hlog)
    (fun b => by
      simp only [replayRegsAt, replayView, List.range_zero, List.map_nil, List.foldl_nil,
        vertexID_init])
    (fun b j hj => by
      have hsucc := coinSuccID_vertexID machine (coin (j, b)) (hfit b j)
        (hview b j ▸ hfit b (j + 1))
      rw [hinput b j] at hsucc
      simp only [replayStep, replayRegsAt, hj, ↓reduceIte, hsucc, ← hview])
    (fun b => by simp [replayStep, replayRegsAt])
    hT
  -- the final test
  have hid := budget_id (enc := encReplayRegs) (.refl _)
  have hbad := bad_budget (k := k) (State := State) (encReplayRegs_radix_budget hid)
    (encReplayRegs_len_budget hid) (encReplayRegs_id_budget hid)
  refine ((budget_comp_linear hbad hloop).of_enc_eq fun b => congrArg encBool ?_).weaken
    ⟨22 * K + 8, fun b => ?_⟩
  · have hacc := bad_vertexID (k := k) (hfit b (L b))
    rw [hinput b (L b)] at hacc
    have hofn : List.ofFn (fun j : Fin (L b) => coin (j, b)) =
        (List.range (L b)).map fun i => coin (i, b) :=
      List.ext_getElem (by simp) fun i _ _ => by simp
    rw [Bool.eq_iff_iff, decide_eq_true_iff, hofn, stepCoins_accepts_iff_foldl_viewCoinStep]
    exact hacc.symm
  · dsimp only
    nlinarith [Nat.zero_le (K * S b), Nat.zero_le (K * Nat.log2 (encB b).length)]

/-- **Replaying a fair-coin machine on computed coins, with a stored seed.** The case of
`Turing.MultiTapePTM.replayCoins_inSpace` whose input is a stored number `z` (such as a seed)
paired with an instance `a`, on which the machine runs: the coin count `L` and the coins are in
context form over the instance, charged the stored arguments plus `S a ≥ log₂ |enc a|`. Then whether
the machine accepts `enc a` on the coins `coin (j, (z, a))`, `j < L (z, a)`, is in context form
too, with the budget `S`. -/
theorem replayCoins_inSpace_context [Finite State] (machine : MultiTapePTM k Bool State) (c : ℕ)
    {α : Type} {enc : α ↪ List Bool} {L : ℕ × α → ℕ} {coin : ℕ × (ℕ × α) → Bool} {S : α → ℕ}
    (hs : ∀ a, machine.toNTM.RunsInSpace (enc a) (c * (Nat.log2 (enc a).length + 1)))
    (hL : ComputableInSpace L (encPair encNat enc) encNat fun q => (encNat q.1).length + S q.2)
    (hcoin : ComputableInSpace coin (encPair encNat (encPair encNat enc)) encBool
      fun q => (encNat q.1).length + ((encNat q.2.1).length + S q.2.2))
    (hlogS : ∀ a, Nat.log2 (enc a).length ≤ S a) :
    ComputableInSpace (fun q : ℕ × α => decide
      ((machine.stepCoins (List.ofFn fun j : Fin (L q) => coin (j, q))
          (machine.toNTM.initCfg (enc q.2))).Halted ∧
        (machine.stepCoins (List.ofFn fun j : Fin (L q) => coin (j, q))
          (machine.toNTM.initCfg (enc q.2))).output = [true]))
      (encPair encNat enc) encBool fun q => (encNat q.1).length + S q.2 := by
  have hlogP (q : ℕ × α) := log2_length_encPair_le encNat enc q
  have hsnd : ComputableInLogSpace (fun q : ℕ × α => enc q.2) (encPair encNat enc) encBits :=
    (ComputableInLogSpace.of_eq (encMid := encBits) fun _ => rfl).comp'
      (ComputableInLogSpace.snd encNat enc)
  have hlen : ComputableInSpace (fun q : ℕ × α => (enc q.2).length) (encPair encNat enc) encNat
      fun q => 2 * (encNat q.1).length + S q.2 + 2 :=
    ((computableInLogSpace_bitsLength.comp' hsnd).inSpace_context
      ⟨2, fun q => (length_encNat_le_of_le_pow (N := (enc q.2).length) (d := 1)
        (by simp)).trans (by dsimp only; omega)⟩).mono_le fun q => by
          have := hlogS q.2
          omega
  have hbit : ComputableInSpace (fun q : ℕ × (ℕ × α) => (enc q.2.2)[q.1]?)
      (encPair encNat (encPair encNat enc)) (encOption encBool)
      fun q => (encNat q.1).length + (2 * (encNat q.2.1).length + S q.2.2 + 2) :=
    ((ComputableInSpace.inputBit enc).comp_logSpace_context
      (f := fun q : ℕ × (ℕ × α) => (q.1, q.2.2))
      (S := fun q : ℕ × α => 2 * (encNat q.1).length + S q.2 + 2)
      (ComputableInLogSpace.pair (ComputableInLogSpace.fst _ _)
        ((ComputableInLogSpace.snd encNat enc).comp' (ComputableInLogSpace.snd _ _)))
      (.of_le fun q => by
        have := hlogS q.2.2
        dsimp only
        omega)
      fun q => (hlogP q).trans (by have := hlogS q.2; omega))
  refine (replayCoins_inSpace machine c (w := fun q => enc q.2) (fun q => hs q.2) hlen hbit
    (hL.mono_le fun q => by omega) (hcoin.mono_le fun q => by omega)
    (fun q => (hlogP q).trans (by have := hlogS q.2; omega))
    (fun q => by have := hlogS q.2; omega)).weaken ⟨8, fun q => ?_⟩
  have := hlogP q
  have := hlogS q.2
  dsimp only
  omega

end Turing.MultiTapePTM
