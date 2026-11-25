/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game
public import CslibFrontier.Languages.Probabilistic.Basic
public import Mathlib.Data.Fintype.Pi
import CslibFrontier.Probability.PMF.Support

/-!
# Selective failure attacks on cryptographic protocols

A protocol that is private against passive (semi-honest) adversaries may still leak an honest
party's secret input `w : Secret` when a corrupted participant deviates actively from its
prescribed response and observes whether the honest party's reconstruction fails (produces an
incorrect output, fails a consistency check, or aborts). The formal model and theorems in this
module are original to this library, motivated by active deviations against passive protocols such
as private information retrieval ([ChorGoldreichKushilevitzSudan1998]), oblivious transfer,
semi-honest Yao two-party computation ([LindellPinkas2009], background on semi-honest Yao and OT),
and semi-honest multi-party computation ([Goldreich2004]).

This module provides a protocol-agnostic framework (`SelectiveFailure.Model Secret Dev Out`) that
applies uniformly across private information retrieval (`PIR.Scheme`), oblivious transfer
(`MPC.batchOTFunctionality`), garbled-circuit two-party computation (`MPC.yaoProtocol`), and
multi-party computation (`MPC.Protocol`):

* **Model and failure games (`Model`, `Model.failureRun`, `Model.failureGame`,
  `Model.failureProb`, `Model.advantage`).** A `Model Secret Dev Out` specifies the ideal output
  `target : Secret → Out` expected by the honest party on secret input `w : Secret` and the
  distribution `exec : Dev → Secret → ProbComp Out` of the honest party's output when the adversary
  applies active deviation `dev : Dev`. The failure experiment `M.failureGame dev w` tests whether
  the reconstructed output `out ← M.exec dev w` differs from `M.target w`, and
  `M.advantage dev w₀ w₁` measures the distinguishing advantage (`Game.advantage`) between candidate
  secrets `w₀` and `w₁` from observing this 1-bit failure signal.
* **Selective-failure freedom (`Model.IsSelectiveFailureFree`) vs. deterministic selective failure
  (`Model.IsDeterministicAttack`).** `M.IsSelectiveFailureFree` requires
  `M.advantage dev w₀ w₁ = 0` (equivalently `M.failureGame dev w₀ = M.failureGame dev w₁`) for all
  deviations `dev` and secrets `w₀, w₁`. Conversely, `M.IsDeterministicAttack dev pred` states that
  under deviation `dev`, the failure indicator `decide (out ≠ M.target w)` equals `pred w` with
  probability one for every secret `w`, yielding `M.advantage dev w₀ w₁ = 1` whenever
  `pred w₀ ≠ pred w₁`.
* **Reusable structural attack and immunity combinators:**
  1. *Indexed-slot selection (`Model.isDeterministicAttack_of_slot`):* when a party sends a table
     `Slot → α` and the honest party's reconstruction on secret `w` reads slot `sel w` (as in
     matrix-balanced PIR `PIR.Scheme.rows`, covering-code PIR `PIR.RadiusOneCover.scheme`,
     1-out-of-2 / batch OT, and Yao input-wire transfer), perturbing slot `slot₀` causes a
     deterministic failure if and only if `sel w = slot₀`.
  2. *Nonlinear indicator thresholding (`Model.isDeterministicAttack_of_decide_eq_one`):* when a
     Boolean-output protocol reconstructs via `decide (L = 1)` over a ring/field `F` where honest
     executions evaluate `L` to `if target w then 1 else 0` (as in Shamir polynomial PIR
     `PIR.shamir` and `PIR.shamirCube`), shifting `L` by any `Δ ∈ F` with `1 + Δ ≠ 1` and `Δ ≠ 1`
     causes a failure if and only if `target w = true`.
  3. *Passive-view factorization (`Model.isSelectiveFailureFree_of_map_eq`):* when the failure
     indicator factors through a secret-independent passive view law (as in 1-bit XOR-sum PIR
     `PIR.twoServer` and `PIR.cube`), no single-party query-only deviation gains any selective
     failure advantage.
* **Input-indexed payload selection (`indexedPayloadModel`, `indexedPayloadPerturb`,
  `isDeterministicAttack_indexedPayload`, `advantage_indexedPayload_eq_one`,
  `not_isSelectiveFailureFree_indexedPayload`).** Direct instantiation for 1-out-of-`N` / batch
  oblivious transfer and input-wire selection protocols where a sender supplies a table
  `m : κ → Slot → α` and a receiver with secret choice `b : κ → Slot` reconstructs
  `fun j => m j (b j)`.

## Main definitions

* `Cslib.Crypto.Protocols.SelectiveFailure.Model`: protocol execution model under active
  deviations against an ideal target output.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.failureRun`,
  `Cslib.Crypto.Protocols.SelectiveFailure.Model.failureGame`,
  `Cslib.Crypto.Protocols.SelectiveFailure.Model.failureProb`,
  `Cslib.Crypto.Protocols.SelectiveFailure.Model.advantage`: canonical output-failure experiment,
  failure probability, and selective-failure distinguishing advantage.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.IsSelectiveFailureFree`: zero selective-failure
  advantage for all deviations and secret pairs.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.IsDeterministicAttack`: deterministic selective
  failure matching a secret predicate `pred : Secret → Bool`.
* `Cslib.Crypto.Protocols.SelectiveFailure.indexedPayloadModel`,
  `Cslib.Crypto.Protocols.SelectiveFailure.indexedPayloadPerturb`: selective-failure model and
  single-slot perturbation attack for input-indexed payload transfer (such as 1-out-of-`N` and
  batch oblivious transfer).

## Main results

* `Cslib.Crypto.Protocols.SelectiveFailure.Model.isSelectiveFailureFree_iff`:
  `IsSelectiveFailureFree` holds iff the failure game distribution is invariant across secrets.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.isDeterministicAttack_iff`: support
  characterization of `IsDeterministicAttack`.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.IsDeterministicAttack.failureProb_eq`,
  `Cslib.Crypto.Protocols.SelectiveFailure.Model.IsDeterministicAttack.advantage_eq_one`,
  `Cslib.Crypto.Protocols.SelectiveFailure.Model.IsDeterministicAttack.not_isSelectiveFailureFree`:
  exact failure probabilities (`0` or `1`), advantage `1`, and refutation of
  `IsSelectiveFailureFree` for deterministic selective failure attacks.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.isDeterministicAttack_of_slot`: slot-selection
  selective failure combinator.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.isDeterministicAttack_of_decide_eq_one`: nonlinear
  `= 1` threshold selective failure combinator.
* `Cslib.Crypto.Protocols.SelectiveFailure.Model.isSelectiveFailureFree_of_map_eq`: immunity
  combinator when the failure indicator factors through a secret-independent view law.
* `Cslib.Crypto.Protocols.SelectiveFailure.isDeterministicAttack_indexedPayload`,
  `Cslib.Crypto.Protocols.SelectiveFailure.advantage_indexedPayload_eq_one`,
  `Cslib.Crypto.Protocols.SelectiveFailure.not_isSelectiveFailureFree_indexedPayload`:
  selective-failure vulnerability of input-indexed payload transfer / batch OT.

## References

* [O. Goldreich, *Foundations of Cryptography, Volume 2: Basic Applications*][Goldreich2004]
  (background on semi-honest vs. malicious security in multi-party protocols)
* [Y. Lindell, B. Pinkas, *A Proof of Security of Yao's Protocol for Two-Party
  Computation*][LindellPinkas2009] (background on semi-honest Yao garbled circuits and OT)
* [B. Chor, O. Goldreich, E. Kushilevitz, M. Sudan, *Private information
  retrieval*][ChorGoldreichKushilevitzSudan1998], Sections 2–4
-/

public section

namespace Cslib.Crypto.Protocols.SelectiveFailure

open Probability
open scoped NNReal

/-- A protocol model for analyzing selective failure attacks, parameterized by the honest party's
secret input type `Secret`, the adversary's active deviation type `Dev`, and the honest party's
output type `Out`. -/
structure Model (Secret Dev Out : Type) where
  /-- The ideal (uncorrupted) output expected by the honest party on secret input `w`. -/
  target : Secret → Out
  /-- The distribution of the honest party's reconstructed output when the corrupted party applies
  active deviation `dev : Dev` on secret input `w : Secret`. -/
  exec : Dev → Secret → ProbComp Out

namespace Model

variable {Secret Dev Out : Type} [DecidableEq Out] (M : Model Secret Dev Out)

/-! ### Canonical output-failure games -/

/-- The probabilistic computation outputting `true` iff the honest party's reconstructed output
under deviation `dev` on secret `w` differs from the ideal output `M.target w`. -/
@[expose] def failureRun (dev : Dev) (w : Secret) : ProbComp Bool :=
  (fun out => decide (out ≠ M.target w)) <$> M.exec dev w

/-- The Boolean failure experiment (`Game`) under deviation `dev` on secret `w`: succeeds (`true`)
when the honest party suffers a reconstruction failure (`out ≠ M.target w`). -/
@[expose] noncomputable def failureGame (dev : Dev) (w : Secret) : Game :=
  ProbComp.eval (M.failureRun dev w)

/-- The probability (`ℝ≥0`) that the honest party suffers a reconstruction failure
(`out ≠ M.target w`) under deviation `dev` on secret `w`. -/
@[expose] noncomputable def failureProb (dev : Dev) (w : Secret) : ℝ≥0 :=
  Game.succProbability (M.failureGame dev w)

/-- The selective-failure distinguishing advantage (`ℝ≥0`) between candidate secrets `w₀` and `w₁`
under active deviation `dev`: the absolute difference between their failure probabilities. -/
@[expose] noncomputable def advantage (dev : Dev) (w₀ w₁ : Secret) : ℝ≥0 :=
  Game.advantage (M.failureGame dev w₀) (M.failureGame dev w₁)

/-- A protocol model is *selective-failure free* if no active deviation `dev` produces any
distinguishing advantage between any two secrets `w₀, w₁` from the failure signal. -/
@[expose] def IsSelectiveFailureFree : Prop :=
  ∀ dev w₀ w₁, M.advantage dev w₀ w₁ = 0

/-- An active deviation `dev` is a *deterministic selective failure attack* for predicate
`pred : Secret → Bool` if, for every secret `w`, the failure indicator `decide (out ≠ M.target w)`
equals `pred w` with probability one. -/
@[expose] def IsDeterministicAttack (dev : Dev) (pred : Secret → Bool) : Prop :=
  ∀ w, M.failureGame dev w = PMF.pure (pred w)

theorem eval_failureRun (dev : Dev) (w : Secret) :
    ProbComp.eval (M.failureRun dev w) =
      (ProbComp.eval (M.exec dev w)).map (fun out => decide (out ≠ M.target w)) :=
  ProbComp.eval_map _ _

@[simp] theorem advantage_self (dev : Dev) (w : Secret) :
    M.advantage dev w w = 0 :=
  Game.advantage_self _

/-- Two Boolean games have zero advantage iff they are equal as `PMF Bool` distributions. -/
private theorem game_advantage_eq_zero_iff (g₁ g₂ : Game) :
    Game.advantage g₁ g₂ = 0 ↔ g₁ = g₂ := by
  rw [Game.advantage, nndist_eq_zero]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have hfail : Game.failProbability g₁ = Game.failProbability g₂ := by
    rw [Game.failProbability_eq, Game.failProbability_eq, h]
  ext (_ | _)
  · exact (ENNReal.toNNReal_eq_toNNReal_iff' (PMF.apply_ne_top g₁ false)
      (PMF.apply_ne_top g₂ false)).mp hfail
  · exact (ENNReal.toNNReal_eq_toNNReal_iff' (PMF.apply_ne_top g₁ true)
      (PMF.apply_ne_top g₂ true)).mp h

/-- `IsSelectiveFailureFree` holds iff for every deviation `dev`, the failure game distribution
`M.failureGame dev w` is independent of the secret `w`. -/
theorem isSelectiveFailureFree_iff :
    M.IsSelectiveFailureFree ↔ ∀ dev w₀ w₁, M.failureGame dev w₀ = M.failureGame dev w₁ :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun _ =>
    game_advantage_eq_zero_iff _ _

/-- Support characterization of `IsDeterministicAttack`: under deviation `dev`, every output in the
support of `M.exec dev w` has failure indicator `decide (out ≠ M.target w) = pred w`. -/
theorem isDeterministicAttack_iff {dev : Dev} {pred : Secret → Bool} :
    M.IsDeterministicAttack dev pred ↔
      ∀ w out, out ∈ (ProbComp.eval (M.exec dev w)).support →
        decide (out ≠ M.target w) = pred w := by
  refine forall_congr' fun w => ?_
  rw [failureGame, eval_failureRun, Probability.PMF.map_eq_pure_iff]

variable {M}

/-- Under a deterministic selective failure attack for `pred`, the failure probability on `w` is `1`
when `pred w = true` and `0` when `pred w = false`. -/
theorem IsDeterministicAttack.failureProb_eq {dev : Dev} {pred : Secret → Bool}
    (h : M.IsDeterministicAttack dev pred) (w : Secret) :
    M.failureProb dev w = if pred w then 1 else 0 := by
  rw [failureProb, h w, Game.succProbability]
  cases pred w <;> simp

theorem IsDeterministicAttack.failureProb_eq_one {dev : Dev} {pred : Secret → Bool}
    (h : M.IsDeterministicAttack dev pred) {w : Secret} (hw : pred w = true) :
    M.failureProb dev w = 1 := by
  rw [h.failureProb_eq, hw]
  simp

theorem IsDeterministicAttack.failureProb_eq_zero {dev : Dev} {pred : Secret → Bool}
    (h : M.IsDeterministicAttack dev pred) {w : Secret} (hw : pred w = false) :
    M.failureProb dev w = 0 := by
  rw [h.failureProb_eq, hw]
  simp

/-- A deterministic selective failure attack achieves maximum distinguishing advantage `1` between
any two secrets `w₀, w₁` on which `pred` differs (`pred w₀ ≠ pred w₁`). -/
theorem IsDeterministicAttack.advantage_eq_one {dev : Dev} {pred : Secret → Bool}
    (h : M.IsDeterministicAttack dev pred) {w₀ w₁ : Secret} (hne : pred w₀ ≠ pred w₁) :
    M.advantage dev w₀ w₁ = 1 := by
  rw [advantage, h w₀, h w₁]
  cases hp₀ : pred w₀ <;> cases hp₁ : pred w₁ <;>
    first | exact (hne (hp₀.trans hp₁.symm)).elim | simp [Game.succProbability]

/-- Any deterministic selective failure attack for a non-constant predicate `pred` refutes
`IsSelectiveFailureFree`. -/
theorem IsDeterministicAttack.not_isSelectiveFailureFree {dev : Dev} {pred : Secret → Bool}
    (h : M.IsDeterministicAttack dev pred) {w₀ w₁ : Secret} (hne : pred w₀ ≠ pred w₁) :
    ¬ M.IsSelectiveFailureFree :=
  fun hfree => zero_ne_one (hfree dev w₀ w₁ ▸ h.advantage_eq_one hne)

/-! ### General structural attack and immunity combinators -/

variable (M)

/-- **Slot-selection selective failure combinator.** Suppose that on secret `w`, the execution
`M.exec dev w` is obtained by mapping `reconstruct w` over a context distribution `sample w`, where
for every supported context `ctx`:
* reconstructing from the perturbed slot `slot₀` yields an output different from `M.target w` when
  `sel w = slot₀`, and
* reconstructing from the perturbed slot `slot₀` yields `M.target w` when `sel w ≠ slot₀`.
Then `dev` is a deterministic selective failure attack for `fun w => decide (sel w = slot₀)`. -/
theorem isDeterministicAttack_of_slot {Ctx Slot : Type} [DecidableEq Slot]
    (sample : Secret → ProbComp Ctx)
    (reconstruct : Secret → Ctx → Out)
    (sel : Secret → Slot) (slot₀ : Slot) (dev : Dev)
    (hexec : ∀ w, M.exec dev w = reconstruct w <$> sample w)
    (hhit : ∀ w ctx, ctx ∈ (ProbComp.eval (sample w)).support →
      sel w = slot₀ → reconstruct w ctx ≠ M.target w)
    (hmiss : ∀ w ctx, ctx ∈ (ProbComp.eval (sample w)).support →
      sel w ≠ slot₀ → reconstruct w ctx = M.target w) :
    M.IsDeterministicAttack dev (fun w => decide (sel w = slot₀)) := by
  rw [isDeterministicAttack_iff]
  intro w out hout
  rw [hexec w, ProbComp.eval_map] at hout
  obtain ⟨ctx, hctx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hout
  by_cases hsel : sel w = slot₀
  · simp [hsel, hhit w ctx hctx hsel]
  · simp [hsel, hmiss w ctx hctx hsel]

/-- **Nonlinear `= 1` threshold selective failure combinator.** For a Boolean-output protocol
(`Out = Bool`) that reconstructs via `decide (evalField w ctx = 1)` in a type `F` with `Zero F` and
`One F`, if under deviation `dev` every supported context `ctx` satisfies:
* `evalField w ctx ≠ 1` when `M.target w = true` (forcing `false ≠ true`), and
* `evalField w ctx ≠ 1` when `M.target w = false` (preserving `false = false`),
i.e., `evalField w ctx ≠ 1` regardless of `M.target w`, then `dev` causes a failure if and only if
`M.target w = true`. -/
theorem isDeterministicAttack_of_decide_eq_one {Ctx F : Type} [One F] [DecidableEq F]
    (M : Model Secret Dev Bool) (sample : Secret → ProbComp Ctx)
    (evalField : Secret → Ctx → F) (dev : Dev)
    (hexec : ∀ w, M.exec dev w = (fun ctx => decide (evalField w ctx = 1)) <$> sample w)
    (hne_one : ∀ w ctx, ctx ∈ (ProbComp.eval (sample w)).support → evalField w ctx ≠ 1) :
    M.IsDeterministicAttack dev M.target := by
  rw [isDeterministicAttack_iff]
  intro w out hout
  rw [hexec w, ProbComp.eval_map] at hout
  obtain ⟨ctx, hctx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hout
  have hne := hne_one w ctx hctx
  cases htar : M.target w <;> simp [hne]

/-- **Passive-view factorization immunity combinator.** If for every deviation `dev`, the failure
game `M.failureGame dev w` is the pushforward `(ProbComp.eval (view dev w)).map (err dev)` of a
passive view `view : Dev → Secret → ProbComp View` whose distribution is independent of `w`, then
`M` is `IsSelectiveFailureFree`. -/
theorem isSelectiveFailureFree_of_map_eq {View : Type}
    (view : Dev → Secret → ProbComp View) (err : Dev → View → Bool)
    (hview : ∀ dev w₀ w₁, ProbComp.eval (view dev w₀) = ProbComp.eval (view dev w₁))
    (hfactor : ∀ dev w, M.failureGame dev w = (ProbComp.eval (view dev w)).map (err dev)) :
    M.IsSelectiveFailureFree := by
  rw [isSelectiveFailureFree_iff]
  intro dev w₀ w₁
  rw [hfactor dev w₀, hfactor dev w₁, hview dev w₀ w₁]

end Model

/-! ### Input-indexed payload transfer (1-out-of-`N` and batch oblivious transfer) -/

section IndexedPayload

variable {κ Slot α : Type} [Fintype κ] [DecidableEq κ] [DecidableEq Slot] [DecidableEq α]

/-- Selective-failure model for an input-indexed payload transfer protocol (such as 1-out-of-`N` or
batch oblivious transfer `MPC.batchOTFunctionality`): the sender holds a table
`m : κ → Slot → α`, the receiver holds a secret choice vector `b : κ → Slot` and expects
`fun j => m j (b j)`, and a deviating sender substitutes a modified table `m' : κ → Slot → α`. -/
@[expose] def indexedPayloadModel (m : κ → Slot → α) :
    Model (κ → Slot) (κ → Slot → α) (κ → α) where
  target b j := m j (b j)
  exec m' b := pure fun j => m' j (b j)

/-- Single-slot sender perturbation in `indexedPayloadModel`: replaces entry `(j₀, s₀)` of the
sender's table `m` with `a'` while leaving all other slots unchanged. -/
@[expose] def indexedPayloadPerturb (m : κ → Slot → α) (j₀ : κ) (s₀ : Slot) (a' : α) :
    κ → Slot → α :=
  Function.update m j₀ (Function.update (m j₀) s₀ a')

/-- **Deterministic selective failure on input-indexed payload transfer / batch OT**: perturbing
slot `(j₀, s₀)` to `a' ≠ m j₀ s₀` causes the receiver's output to differ from the honest output if
and only if the receiver's secret choice at `j₀` is `s₀` (`b j₀ = s₀`). -/
theorem isDeterministicAttack_indexedPayload (m : κ → Slot → α) (j₀ : κ) (s₀ : Slot) {a' : α}
    (hne : a' ≠ m j₀ s₀) :
    (indexedPayloadModel m).IsDeterministicAttack (indexedPayloadPerturb m j₀ s₀ a')
      (fun b => decide (b j₀ = s₀)) := by
  refine (indexedPayloadModel m).isDeterministicAttack_of_slot
    (fun _ => pure ())
    (fun b _ j => indexedPayloadPerturb m j₀ s₀ a' j (b j))
    (fun b => b j₀) s₀ (indexedPayloadPerturb m j₀ s₀ a')
    (fun _ => rfl) ?_ ?_
  · intro b _ _ hbs heq
    have hj := congrFun heq j₀
    simp only [indexedPayloadModel, indexedPayloadPerturb, Function.update_self, hbs] at hj
    exact hne hj
  · intro b _ _ hbs
    funext j
    by_cases hj : j = j₀
    · subst hj
      simp [indexedPayloadModel, indexedPayloadPerturb, hbs]
    · simp [indexedPayloadModel, indexedPayloadPerturb, hj]

/-- Perturbing slot `(j₀, s₀)` in `indexedPayloadModel` distinguishes any choice vector `b₀` with
`b₀ j₀ = s₀` from any `b₁` with `b₁ j₀ ≠ s₀` with selective-failure advantage `1`. -/
theorem advantage_indexedPayload_eq_one (m : κ → Slot → α) (j₀ : κ) (s₀ : Slot) {a' : α}
    (hne : a' ≠ m j₀ s₀) {b₀ b₁ : κ → Slot} (hb₀ : b₀ j₀ = s₀) (hb₁ : b₁ j₀ ≠ s₀) :
    (indexedPayloadModel m).advantage (indexedPayloadPerturb m j₀ s₀ a') b₀ b₁ = 1 :=
  (isDeterministicAttack_indexedPayload m j₀ s₀ hne).advantage_eq_one (by simp [hb₀, hb₁])

omit [DecidableEq κ] [DecidableEq Slot] in
/-- Input-indexed payload transfer is not selective-failure free whenever the index set `κ` is
nonempty and the slot type `Slot` and payload type `α` are nontrivial. -/
theorem not_isSelectiveFailureFree_indexedPayload [Nonempty κ] [Nontrivial Slot] [Nontrivial α]
    (m : κ → Slot → α) :
    ¬ (indexedPayloadModel m).IsSelectiveFailureFree := by
  classical
  obtain ⟨j₀⟩ := ‹Nonempty κ›
  obtain ⟨s₀, s₁, hs⟩ := exists_pair_ne Slot
  obtain ⟨a', ha'⟩ := exists_ne (m j₀ s₀)
  exact (isDeterministicAttack_indexedPayload m j₀ s₀ ha').not_isSelectiveFailureFree
    (w₀ := fun _ => s₀) (w₁ := fun _ => s₁) (by simp [hs.symm])

end IndexedPayload

end Cslib.Crypto.Protocols.SelectiveFailure
