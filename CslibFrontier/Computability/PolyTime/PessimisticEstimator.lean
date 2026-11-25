/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Capabilities
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Nat.Bits
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import CslibFrontier.Computability.Machines.Turing.MultiTape.PolyTime
public import CslibFrontier.Foundations.Combinatorics.PessimisticEstimator
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeLoops
import CslibFrontier.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial.Automation

/-!
# Polynomial-time transfer for greedy pessimistic-estimator and multi-choice derandomization

`PolyTimeGreedyInput` packages an input-parameterized instance of
`Cslib.PessimisticEstimator.greedy` (round list, initial state, binary branch transition, and
pessimistic estimator / conditional expectation) and proves plain multi-tape polynomial-time
computability (`Turing.MultiTapeTM.ComputableInPolyTime`) whenever:
1. `rounds`, `init`, `branch`, `estimate`, and the order comparison `(· ≤ ·)` on `M` are
   `ComputableInPolyTime`; and
2. taking either branch on any round `r ∈ rounds x` grows the encoded state by at most a
   polynomially bounded additive budget `growth x`.

`run_polyTime_spec` and `run_polyTime_spec_of_add_le` pair this plain complexity certificate with
the invariant and deterministic objective bound `estimate x (run x) ≤ estimate x (init x)` from
`Cslib.PessimisticEstimator.greedy_spec`.

`PolyTimeChoiceGreedyInput` generalizes the transfer from binary choices to arbitrary finite
per-round candidate lists `choices : I → R → List A` (such as finite-product coordinate fixing in
`Cslib.Algorithms.Lean.PessimisticEstimator.ProductDerandomizer`), certifying
`ComputableInPolyTime` via `ComputableInPolyTime.foldlWith` and `foldlWithInput_of_bounded_growth`.

## Main definitions

* `Cslib.Computability.PolyTimeGreedyInput`: input-parameterized binary greedy /
  pessimistic-estimator specification.
* `Cslib.Computability.PolyTimeGreedyInput.encBranchInput`: tuple encoding for binary branch
  transitions.
* `Cslib.Computability.PolyTimeGreedyInput.run`: execute `Cslib.PessimisticEstimator.greedy` on an
  input `x`.
* `Cslib.Computability.PolyTimeChoiceGreedyInput`: input-parameterized multi-choice greedy /
  conditional-expectation specification.
* `Cslib.Computability.PolyTimeChoiceGreedyInput.encChoiceInput`: tuple encoding for candidate
  branch transitions.
* `Cslib.Computability.PolyTimeChoiceGreedyInput.scanStep`,
  `Cslib.Computability.PolyTimeChoiceGreedyInput.stepRound`,
  `Cslib.Computability.PolyTimeChoiceGreedyInput.run`: execute multi-choice greedy rounds on an
  input `x`.

## Main results

* `Cslib.Computability.PolyTimeGreedyInput.computableInPolyTime_run`: plain polynomial-time
  transfer for general order encodings `encM`.
* `Cslib.Computability.PolyTimeGreedyInput.computableInPolyTime_run_nat`: specialization to binary
  natural-number estimators (`encNat`).
* `Cslib.Computability.PolyTimeGreedyInput.run_polyTime_spec`,
  `Cslib.Computability.PolyTimeGreedyInput.run_polyTime_spec_of_add_le`: combined polynomial-time
  and pessimistic-estimator correctness specifications.
* `Cslib.Computability.PolyTimeChoiceGreedyInput.computableInPolyTime_run`,
  `Cslib.Computability.PolyTimeChoiceGreedyInput.computableInPolyTime_run_nat`: plain
  polynomial-time transfer for multi-choice candidate scanning.
* `Cslib.Computability.PolyTimeChoiceGreedyInput.run_spec`,
  `Cslib.Computability.PolyTimeChoiceGreedyInput.run_polyTime_spec`: minimizing invariant and
  objective guarantee (`G.estimate x (G.run x) ≤ G.estimate x (G.init x)`), pure and paired with
  `ComputableInPolyTime`.
-/

public section

namespace Cslib.Computability

open Cslib.PessimisticEstimator Turing.MultiTapeTM ComputableInPolyTime

/-- Input-parameterized greedy binary-choice derandomization bundle. -/
structure PolyTimeGreedyInput (I R S M : Type) [LE M] [DecidableRel (α := M) (· ≤ ·)] where
  /-- Ordered list of decision rounds extracted from input `x`. -/
  rounds : I → List R
  /-- Initial state constructed from input `x`. -/
  init : I → S
  /-- Branch transition for input `x`, round `r`, choice `b`, and state `s`. -/
  branch : I → R → Bool → S → S
  /-- Pessimistic-estimator / conditional-expectation value on state `s` under input `x`. -/
  estimate : I → S → M

namespace PolyTimeGreedyInput

/-- Tuple encoding `(((I × S) × R) × Bool)` for input-parameterized greedy branch transitions. -/
abbrev encBranchInput {I R S : Type}
    (encI : I ↪ List Bool) (encS : S ↪ List Bool) (encR : R ↪ List Bool) :
    (((I × S) × R) × Bool) ↪ List Bool :=
  encPair (encPair (encPair encI encS) encR) encBool

section Execution

variable {I R S M : Type} [LE M] [DecidableRel (α := M) (· ≤ ·)]
  (G : PolyTimeGreedyInput I R S M)

/-- Run `Cslib.PessimisticEstimator.greedy` on input `x`. -/
@[expose] def run (x : I) : S :=
  greedy (G.branch x) (G.estimate x) (G.rounds x) (G.init x)

private theorem run_eq_foldl (x : I) :
    G.run x =
      (G.rounds x).foldl
        (fun s r =>
          if G.estimate x (G.branch x r true s) ≤ G.estimate x (G.branch x r false s) then
            G.branch x r true s
          else
            G.branch x r false s)
        (G.init x) :=
  rfl

/-- Plain `ComputableInPolyTime` transfer for `G.run` when `rounds`, `init`, `branch`, `estimate`,
and `(· ≤ ·)` are polynomial-time and each round increases `(encS s).length` by at most a
polynomially bounded `growth x`. -/
theorem computableInPolyTime_run
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x) :
    ComputableInPolyTime G.run encI encS := by
  let encStep := encPair (encPair encI encS) encR
  have hid : ComputableInPolyTime id encStep encStep := id'
  have hx : ComputableInPolyTime (fun ((input, _state), _round) => input) encStep encI :=
    (fst (encPair encI encS) encR).fst'
  have hbr (b : Bool) : ComputableInPolyTime
      (fun ((input, state), round) => G.branch input round b state) encStep encS :=
    hbranch.comp (hid.prod (const b))
  have hest (b : Bool) : ComputableInPolyTime
      (fun ((input, state), round) =>
        G.estimate input (G.branch input round b state)) encStep encM :=
    hestimate.comp (hx.prod (hbr b))
  have hcmp : ComputableInPolyTime
      (fun ((input, state), round) =>
        decide (G.estimate input (G.branch input round true state) ≤
          G.estimate input (G.branch input round false state)))
      encStep encBool :=
    hle.comp ((hest true).prod (hest false))
  have hstep : ComputableInPolyTime
      (fun ((input, state), round) =>
        if G.estimate input (G.branch input round true state) ≤
            G.estimate input (G.branch input round false state) then
          G.branch input round true state
        else
          G.branch input round false state)
      encStep encS := by
    simpa only [decide_eq_true_eq] using ite hcmp (hbr true) (hbr false)
  refine foldlWithInput_of_bounded_growth hinit ⟨hrounds, hstep, inferInstance, inferInstance⟩
    ⟨hpoly, fun x s r hr => ?_⟩
  dsimp only [greedyStep]
  split_ifs <;> exact hgrowth x s r _ hr

end Execution

section NatSpecialization

variable {I R S : Type} (G : PolyTimeGreedyInput I R S ℕ)

/-- Specialization of `computableInPolyTime_run` to `ℕ`-valued estimators encoded in binary
(`encNat`). -/
theorem computableInPolyTime_run_nat
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encNat)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x) :
    ComputableInPolyTime G.run encI encS :=
  G.computableInPolyTime_run hrounds hinit hbranch hestimate
    (binary_le' (fst encNat encNat) (snd encNat encNat)) hpoly hgrowth

end NatSpecialization

section CombinedSpec

variable {I R S M : Type} [LinearOrder M] (G : PolyTimeGreedyInput I R S M)

/-- Pairs the plain `ComputableInPolyTime` certificate for `G.run` with the terminal invariant and
deterministic bound `G.estimate x (G.run x) ≤ G.estimate x (G.init x)`. -/
theorem run_polyTime_spec
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x)
    (Inv : I → List R → S → Prop)
    (hinv_init : ∀ x, Inv x (G.rounds x) (G.init x))
    (hinv_branch : ∀ x r rs s b, Inv x (r :: rs) s → Inv x rs (G.branch x r b s))
    (hmin : ∀ x r rs s, Inv x (r :: rs) s →
      min (G.estimate x (G.branch x r true s)) (G.estimate x (G.branch x r false s)) ≤
        G.estimate x s) :
    ComputableInPolyTime G.run encI encS ∧
      ∀ x, Inv x [] (G.run x) ∧ G.estimate x (G.run x) ≤ G.estimate x (G.init x) :=
  ⟨G.computableInPolyTime_run hrounds hinit hbranch hestimate hle hpoly hgrowth, fun x =>
    greedy_spec (G.branch x) (G.estimate x) (Inv x) (hinv_branch x) (hmin x)
      (G.rounds x) (G.init x) (hinv_init x)⟩

/-- Averaging form of `run_polyTime_spec` when the two branch estimates sum to at most twice the
current estimate. -/
theorem run_polyTime_spec_of_add_le [AddCommMonoid M] [IsOrderedCancelAddMonoid M]
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encL : List R ↪ List Bool}
    [ListEncoding encR encL] [SizedListEncoding encR encL]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encL)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encBranchInput encI encS encR) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r b, r ∈ G.rounds x →
      (encS (G.branch x r b s)).length ≤ (encS s).length + growth x)
    (Inv : I → List R → S → Prop)
    (hinv_init : ∀ x, Inv x (G.rounds x) (G.init x))
    (hinv_branch : ∀ x r rs s b, Inv x (r :: rs) s → Inv x rs (G.branch x r b s))
    (havg : ∀ x r rs s, Inv x (r :: rs) s →
      G.estimate x (G.branch x r true s) + G.estimate x (G.branch x r false s) ≤
        G.estimate x s + G.estimate x s) :
    ComputableInPolyTime G.run encI encS ∧
      ∀ x, Inv x [] (G.run x) ∧ G.estimate x (G.run x) ≤ G.estimate x (G.init x) :=
  G.run_polyTime_spec hrounds hinit hbranch hestimate hle hpoly hgrowth Inv hinv_init hinv_branch
    fun x r rs s h => min_le_of_add_le_two_nsmul ((havg x r rs s h).trans_eq (two_nsmul _).symm)

end CombinedSpec

end PolyTimeGreedyInput

/-- Input-parameterized multi-choice greedy / conditional-expectation derandomization bundle:
at each round `r ∈ rounds x`, evaluates `estimate x (branch x r a s)` across `a ∈ choices x r`
and selects a minimizing choice. -/
structure PolyTimeChoiceGreedyInput (I R A S M : Type) [LE M] [DecidableRel (α := M) (· ≤ ·)] where
  /-- Ordered list of decision rounds extracted from input `x`. -/
  rounds : I → List R
  /-- Candidate domain choices tested at round `r` on input `x`. -/
  choices : I → R → List A
  /-- Initial state constructed from input `x`. -/
  init : I → S
  /-- State transition for input `x`, round `r`, candidate `a`, and state `s`. -/
  branch : I → R → A → S → S
  /-- Pessimistic-estimator / conditional-expectation value on state `s` under input `x`. -/
  estimate : I → S → M

namespace PolyTimeChoiceGreedyInput

/-- Left-associated pair encoding `(((I × S) × R) × A)` for candidate branch transitions: encodes
`(((input, state), round), choice)` as
`frame (frame (frame (encI input) ++ encS state) ++ encR round) ++ encA choice`, framing each
nested left component with `Turing.MultiTapeTM.frame` followed by the unframed `encA choice`. -/
abbrev encChoiceInput {I R A S : Type}
    (encI : I ↪ List Bool) (encS : S ↪ List Bool) (encR : R ↪ List Bool) (encA : A ↪ List Bool) :
    (((I × S) × R) × A) ↪ List Bool :=
  encPair (encPair (encPair encI encS) encR) encA

section Execution

variable {I R A S M : Type} [LE M] [DecidableRel (α := M) (· ≤ ·)]
  (G : PolyTimeChoiceGreedyInput I R A S M)

/-- Fold step updating the best `(candidate, estimate)` pair seen so far at round `r`. -/
@[expose] def scanStep (x : I) (s : S) (r : R) (best : Option (A × M)) (a : A) : Option (A × M) :=
  let val := G.estimate x (G.branch x r a s)
  best.elim (some (a, val)) fun bm => if val ≤ bm.2 then some (a, val) else some bm

/-- Execute one multi-choice round `r` on state `s` (leaving `s` unchanged if `G.choices x r` is
empty). -/
@[expose] def stepRound (x : I) (s : S) (r : R) : S :=
  ((G.choices x r).foldl (G.scanStep x s r) none).elim s fun bm => G.branch x r bm.1 s

/-- Execute all rounds in `G.rounds x` sequentially starting from `G.init x`. -/
@[expose] def run (x : I) : S :=
  (G.rounds x).foldl (G.stepRound x) (G.init x)

private theorem scanStep_foldl_mem (x : I) (s : S) (r : R) (all : List A) :
    ∀ (cs : List A) (best : Option (A × M)),
      (best = none ∨ ∃ a ∈ all, best = some (a, G.estimate x (G.branch x r a s))) →
      (∀ a ∈ cs, a ∈ all) →
      let out := cs.foldl (G.scanStep x s r) best
      out = none ∨ ∃ a ∈ all, out = some (a, G.estimate x (G.branch x r a s))
  | [], _, hbest, _ => hbest
  | a :: cs, best, hbest, hsub => by
    have ha : a ∈ all := hsub a List.mem_cons_self
    have hnext : G.scanStep x s r best a = none ∨
        ∃ b ∈ all, G.scanStep x s r best a = some (b, G.estimate x (G.branch x r b s)) := by
      rcases hbest with rfl | ⟨b, hb, rfl⟩
      · exact Or.inr ⟨a, ha, rfl⟩
      · dsimp only [scanStep, Option.elim]
        split_ifs
        · exact Or.inr ⟨a, ha, rfl⟩
        · exact Or.inr ⟨b, hb, rfl⟩
    exact scanStep_foldl_mem x s r all cs _ hnext fun c hc => hsub c (List.mem_cons_of_mem a hc)

/-- Plain `ComputableInPolyTime` transfer for `G.run` when `rounds`, `choices`, `init`, `branch`,
`estimate`, and `(· ≤ ·)` are polynomial-time and taking any candidate `a ∈ G.choices x r` on any
round `r ∈ G.rounds x` increases `(encS s).length` by at most a polynomially bounded `growth x`. -/
theorem computableInPolyTime_run
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encLR : List R ↪ List Bool}
    [ListEncoding encR encLR] [SizedListEncoding encR encLR]
    {encA : A ↪ List Bool} {encLA : List A ↪ List Bool}
    [ListEncoding encA encLA] [hSA : SizedListEncoding encA encLA]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encLR)
    (hchoices : ComputableInPolyTime (fun (input, round) => G.choices input round)
      (encPair encI encR) encLA)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encChoiceInput encI encS encR encA) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r a, r ∈ G.rounds x → a ∈ G.choices x r →
      (encS (G.branch x r a s)).length ≤ (encS s).length + growth x) :
    ComputableInPolyTime G.run encI encS := by
  let encRound := encPair (encPair encI encS) encR
  let encAM := encPair encA encM
  let encOpt := encOption encAM
  let encScanIn := encPair (encPair encRound encOpt) encA
  have hlist_p : ComputableInPolyTime (fun p : (I × S) × R => G.choices p.1.1 p.2)
      encRound encLA := by
    fun_prop
  have hval_pa : ComputableInPolyTime
      (fun pa : ((I × S) × R) × A =>
        G.estimate pa.1.1.1 (G.branch pa.1.1.1 pa.1.2 pa.2 pa.1.1.2))
      (encChoiceInput encI encS encR encA) encM := by
    fun_prop
  have hround_scan : ComputableInPolyTime
      (fun q : (((I × S) × R) × Option (A × M)) × A => q.1.1) encScanIn encRound :=
    (fst (encPair encRound encOpt) encA).fst'
  have ha_scan : ComputableInPolyTime
      (fun q : (((I × S) × R) × Option (A × M)) × A => q.2) encScanIn encA :=
    snd (encPair encRound encOpt) encA
  have hval_scan : ComputableInPolyTime
      (fun q : (((I × S) × R) × Option (A × M)) × A =>
        G.estimate q.1.1.1.1 (G.branch q.1.1.1.1 q.1.1.2 q.2 q.1.1.1.2))
      encScanIn encM :=
    hval_pa.comp (hround_scan.prod ha_scan)
  have hnew_some : ComputableInPolyTime
      (fun q : (((I × S) × R) × Option (A × M)) × A =>
        some (q.2, G.estimate q.1.1.1.1 (G.branch q.1.1.1.1 q.1.1.2 q.2 q.1.1.1.2)))
      encScanIn encOpt := by
    fun_prop
  have hscan_step : ComputableInPolyTime
      (fun q : (((I × S) × R) × Option (A × M)) × A =>
        G.scanStep q.1.1.1.1 q.1.1.1.2 q.1.1.2 q.1.2 q.2)
      encScanIn encOpt := by
    refine optionElimWithInput (by fun_prop) hnew_some ?_
    let encBody := encPair encScanIn encAM
    have hq_b : ComputableInPolyTime _ encBody encScanIn := fst encScanIn encAM
    have hbm_b : ComputableInPolyTime _ encBody encAM := snd encScanIn encAM
    have hcmp : ComputableInPolyTime
        (fun w : ((((I × S) × R) × Option (A × M)) × A) × (A × M) =>
          decide (G.estimate w.1.1.1.1.1 (G.branch w.1.1.1.1.1 w.1.1.1.2 w.1.2 w.1.1.1.1.2) ≤
            w.2.2))
        encBody encBool :=
      hle.comp ((hval_scan.comp hq_b).prod ((snd encA encM).comp hbm_b))
    simpa only [decide_eq_true_eq, Function.comp_def] using
      ite hcmp (hnew_some.comp hq_b) ((optionSome encAM).comp hbm_b)
  obtain ⟨cV, dV, hV⟩ := hval_pa.polyBounded_length.exists_le
  let B_opt (p : (I × S) × R) : ℕ :=
    let L := (encLA (G.choices p.1.1 p.2)).length
    2 * L + cV * (2 * (encRound p).length + 1 + L + 1) ^ dV + 2
  have hB_opt : PolyBounded (fun p => (encRound p).length) B_opt := by growth_poly
  have hscan_fold : ComputableInPolyTime
      (fun p : (I × S) × R =>
        (G.choices p.1.1 p.2).foldl (G.scanStep p.1.1 p.1.2 p.2) none)
      encRound encOpt := by
    refine foldlWith id' hlist_p (const none) hscan_step hB_opt fun p k _ => ?_
    rcases G.scanStep_foldl_mem p.1.1 p.1.2 p.2 (G.choices p.1.1 p.2)
        ((G.choices p.1.1 p.2).take k) none (Or.inl rfl)
        (fun a ha => List.mem_of_mem_take ha) with hnone | ⟨a, ha, hsome⟩
    · rw [hnone]
      simp [encOpt, B_opt]
    · rw [hsome]
      have ha_len : (encA a).length ≤ (encLA (G.choices p.1.1 p.2)).length :=
        hSA.length_elem_le (G.choices p.1.1 p.2) a ha
      have hpa_len : (encChoiceInput encI encS encR encA (p, a)).length ≤
          2 * (encRound p).length + 1 + (encLA (G.choices p.1.1 p.2)).length := by
        change (encPair encRound encA (p, a)).length ≤ _
        rw [length_encPair]
        dsimp only
        omega
      have hv_len : (encM (G.estimate p.1.1 (G.branch p.1.1 p.2 a p.1.2))).length ≤
          cV * (2 * (encRound p).length + 1 + (encLA (G.choices p.1.1 p.2)).length + 1) ^ dV :=
        (hV (p, a)).trans
          (Nat.mul_le_mul_left cV (Nat.pow_le_pow_left (Nat.add_le_add_right hpa_len 1) dV))
      simp only [encOpt, encAM, encOption_some, List.length_cons, length_encPair, B_opt]
      omega
  have hstep_round : ComputableInPolyTime
      (fun p : (I × S) × R => G.stepRound p.1.1 p.1.2 p.2)
      encRound encS := by
    refine optionElimWithInput hscan_fold (by fun_prop) ?_
    exact hbranch.comp ((fst encRound encAM).prod ((fst encA encM).comp (snd encRound encAM)))
  refine foldlWithInput_of_bounded_growth hinit ⟨hrounds, hstep_round, inferInstance, inferInstance⟩
    ⟨hpoly, fun x s r hr => ?_⟩
  dsimp only [stepRound]
  rcases G.scanStep_foldl_mem x s r (G.choices x r) (G.choices x r) none (Or.inl rfl)
      (fun _ h => h) with hnone | ⟨a, ha, hsome⟩
  · rw [hnone]
    simp only [Option.elim]
    omega
  · rw [hsome]
    exact hgrowth x s r a hr ha

end Execution

section NatSpecialization

variable {I R A S : Type} (G : PolyTimeChoiceGreedyInput I R A S ℕ)

/-- Specialization of `computableInPolyTime_run` to `ℕ`-valued estimators encoded in binary
(`encNat`). -/
theorem computableInPolyTime_run_nat
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encLR : List R ↪ List Bool}
    [ListEncoding encR encLR] [SizedListEncoding encR encLR]
    {encA : A ↪ List Bool} {encLA : List A ↪ List Bool}
    [ListEncoding encA encLA] [SizedListEncoding encA encLA]
    {encS : S ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encLR)
    (hchoices : ComputableInPolyTime (fun (input, round) => G.choices input round)
      (encPair encI encR) encLA)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encChoiceInput encI encS encR encA) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encNat)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r a, r ∈ G.rounds x → a ∈ G.choices x r →
      (encS (G.branch x r a s)).length ≤ (encS s).length + growth x) :
    ComputableInPolyTime G.run encI encS :=
  G.computableInPolyTime_run hrounds hchoices hinit hbranch hestimate
    (binary_le' (fst encNat encNat) (snd encNat encNat)) hpoly hgrowth

end NatSpecialization

section CombinedSpec

variable {I R A S M : Type} [LinearOrder M] (G : PolyTimeChoiceGreedyInput I R A S M)

private theorem scanStep_foldl_spec (x : I) (s : S) (r : R) (all : List A) :
    ∀ (cs : List A) (a₀ : A) (m₀ : M),
      a₀ ∈ all →
      m₀ = G.estimate x (G.branch x r a₀ s) →
      (∀ a ∈ cs, a ∈ all) →
      ∃ b ∈ all,
        cs.foldl (G.scanStep x s r) (some (a₀, m₀)) =
          some (b, G.estimate x (G.branch x r b s)) ∧
        G.estimate x (G.branch x r b s) ≤ m₀ ∧
        ∀ a ∈ cs, G.estimate x (G.branch x r b s) ≤ G.estimate x (G.branch x r a s)
  | [], a₀, m₀, ha₀, hm₀, _ =>
    ⟨a₀, ha₀, congrArg (fun m => some (a₀, m)) hm₀, hm₀.symm.le, by simp⟩
  | c :: cs, a₀, m₀, ha₀, hm₀, hsub => by
    have hc : c ∈ all := hsub c List.mem_cons_self
    have hsub' : ∀ a ∈ cs, a ∈ all := fun a ha => hsub a (List.mem_cons_of_mem c ha)
    dsimp only [List.foldl_cons, scanStep, Option.elim]
    let val := G.estimate x (G.branch x r c s)
    split_ifs with hle
    · obtain ⟨b, hb, hout, hle_c, hforall⟩ := scanStep_foldl_spec x s r all cs c val hc rfl hsub'
      refine ⟨b, hb, hout, hle_c.trans hle, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hle_c
      · exact hforall a ha'
    · have hm₀_le : m₀ ≤ val := le_of_not_ge hle
      obtain ⟨b, hb, hout, hle_0, hforall⟩ := scanStep_foldl_spec x s r all cs a₀ m₀ ha₀ hm₀ hsub'
      refine ⟨b, hb, hout, hle_0, fun a ha => ?_⟩
      rcases List.mem_cons.mp ha with rfl | ha'
      · exact hle_0.trans hm₀_le
      · exact hforall a ha'

private theorem foldl_stepRound_spec
    (Inv : I → List R → S → Prop)
    (hinv_branch : ∀ x r rs s a,
      Inv x (r :: rs) s → a ∈ G.choices x r → Inv x rs (G.branch x r a s))
    (hmin : ∀ x r rs s, Inv x (r :: rs) s →
      ∃ a ∈ G.choices x r, G.estimate x (G.branch x r a s) ≤ G.estimate x s)
    (x : I) :
    ∀ (rs : List R) (s : S), Inv x rs s →
      Inv x [] (rs.foldl (G.stepRound x) s) ∧
        G.estimate x (rs.foldl (G.stepRound x) s) ≤ G.estimate x s
  | [], _, hinv => ⟨hinv, le_rfl⟩
  | r :: rs, s, hinv => by
    obtain ⟨a_star, ha_star, ha_le⟩ := hmin x r rs s hinv
    cases hcs : G.choices x r with
    | nil =>
      rw [hcs] at ha_star
      cases ha_star
    | cons a₀ cs =>
      obtain ⟨b, hb, hout, hle_0, hforall⟩ :=
        G.scanStep_foldl_spec x s r (a₀ :: cs) cs a₀
          (G.estimate x (G.branch x r a₀ s)) List.mem_cons_self rfl
          fun a ha => List.mem_cons_of_mem a₀ ha
      have hb_choices : b ∈ G.choices x r := hcs ▸ hb
      have hstep : G.stepRound x s r = G.branch x r b s := by
        simp [stepRound, hcs, scanStep, hout]
      have hle_star : G.estimate x (G.branch x r b s) ≤ G.estimate x (G.branch x r a_star s) := by
        rw [hcs] at ha_star
        rcases List.mem_cons.mp ha_star with rfl | hmem_cs
        · exact hle_0
        · exact hforall a_star hmem_cs
      obtain ⟨hinv_end, hest_end⟩ :=
        foldl_stepRound_spec Inv hinv_branch hmin x rs (G.branch x r b s)
          (hinv_branch x r rs s b hinv hb_choices)
      simpa only [List.foldl_cons, hstep] using
        ⟨hinv_end, hest_end.trans (hle_star.trans ha_le)⟩

/-- Minimizing correctness specification for `G.run`: if `Inv` holds initially, is preserved by
taking any candidate `a ∈ G.choices x r`, and each round admits at least one candidate in
`G.choices x r` not increasing `G.estimate x`, then `G.run x` satisfies `Inv x []` and
`G.estimate x (G.run x) ≤ G.estimate x (G.init x)`. -/
theorem run_spec
    (Inv : I → List R → S → Prop)
    (hinv_init : ∀ x, Inv x (G.rounds x) (G.init x))
    (hinv_branch : ∀ x r rs s a,
      Inv x (r :: rs) s → a ∈ G.choices x r → Inv x rs (G.branch x r a s))
    (hmin : ∀ x r rs s, Inv x (r :: rs) s →
      ∃ a ∈ G.choices x r, G.estimate x (G.branch x r a s) ≤ G.estimate x s)
    (x : I) :
    Inv x [] (G.run x) ∧ G.estimate x (G.run x) ≤ G.estimate x (G.init x) :=
  G.foldl_stepRound_spec Inv hinv_branch hmin x (G.rounds x) (G.init x) (hinv_init x)

/-- Pairs the plain `ComputableInPolyTime` certificate for `G.run` with the terminal invariant and
minimizing bound `G.estimate x (G.run x) ≤ G.estimate x (G.init x)` from `run_spec`. -/
theorem run_polyTime_spec
    {encI : I ↪ List Bool} {encR : R ↪ List Bool} {encLR : List R ↪ List Bool}
    [ListEncoding encR encLR] [SizedListEncoding encR encLR]
    {encA : A ↪ List Bool} {encLA : List A ↪ List Bool}
    [ListEncoding encA encLA] [SizedListEncoding encA encLA]
    {encS : S ↪ List Bool} {encM : M ↪ List Bool}
    (hrounds : ComputableInPolyTime G.rounds encI encLR)
    (hchoices : ComputableInPolyTime (fun (input, round) => G.choices input round)
      (encPair encI encR) encLA)
    (hinit : ComputableInPolyTime G.init encI encS)
    (hbranch : ComputableInPolyTime
      (fun (((input, state), round), choice) => G.branch input round choice state)
      (encChoiceInput encI encS encR encA) encS)
    (hestimate : ComputableInPolyTime (fun (input, state) => G.estimate input state)
      (encPair encI encS) encM)
    (hle : ComputableInPolyTime (fun (m₁, m₂) => decide (m₁ ≤ m₂))
      (encPair encM encM) encBool)
    {growth : I → ℕ} (hpoly : PolyBounded (fun x => (encI x).length) growth)
    (hgrowth : ∀ x s r a, r ∈ G.rounds x → a ∈ G.choices x r →
      (encS (G.branch x r a s)).length ≤ (encS s).length + growth x)
    (Inv : I → List R → S → Prop)
    (hinv_init : ∀ x, Inv x (G.rounds x) (G.init x))
    (hinv_branch : ∀ x r rs s a,
      Inv x (r :: rs) s → a ∈ G.choices x r → Inv x rs (G.branch x r a s))
    (hmin : ∀ x r rs s, Inv x (r :: rs) s →
      ∃ a ∈ G.choices x r, G.estimate x (G.branch x r a s) ≤ G.estimate x s) :
    ComputableInPolyTime G.run encI encS ∧
      ∀ x, Inv x [] (G.run x) ∧ G.estimate x (G.run x) ≤ G.estimate x (G.init x) :=
  ⟨G.computableInPolyTime_run hrounds hchoices hinit hbranch hestimate hle hpoly hgrowth,
    G.run_spec Inv hinv_init hinv_branch hmin⟩

end CombinedSpec

end PolyTimeChoiceGreedyInput

end Cslib.Computability
