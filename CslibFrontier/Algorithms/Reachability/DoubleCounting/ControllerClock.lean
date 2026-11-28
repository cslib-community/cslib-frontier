/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Controller
public import CslibFrontier.Algorithms.Reachability.DoubleCounting.Scan
import CslibFrontier.Foundations.Control.Monad.Clock
import Mathlib.Tactic.Ring

/-!
# Callback-action bounds for the controller

The actual controller runs in `OptionT (StateM σ)`: a callback can return either Boolean or
reject, while its state records the charge even on rejection. The chosen clock can count edge
calls, membership calls, or actions inside the callbacks. No correctness hypothesis on replies
or tallies is used. Every initial provider state is covered, including ties, rejecting calls
and fuel exhaustion.

## Main results

* `scanNextRound_clock`: with edge cost `E` and membership cost `M`, a round costs at most
  `n * (M + n * (E + M))`.
* `runController_clock`: at most `n³ * E + (n³ + n² + 1) * M`, including the final target
  membership call. Thus edges cost at most `n³` calls and membership at most `n³ + n² + 1`.
* `runController_scan_clock`: composing the streaming membership scan gives the degree-five
  bound `n³ + (n³ + n² + 1) * (n * (2*n + 2))` on primitive callback actions.

These are bounds on the state clock, not physical runtime or workspace. In particular they
do not implement the callbacks or certify native halting; those obligations remain in #6747.
A primitive callback can record one action before returning a value or rejection. The weighted
bound also composes with a membership routine's own action bound. See the ordinary-import client
`CslibFrontierTests.DoubleCountingControllerClock` for separate counters and composition with
`Scan.tallyM_clock`.
-/

public section
namespace Cslib.DoubleCounting

private theorem predecessorStep_clock {σ : Type} {n : ℕ} (clock : σ → ℕ) (E M : ℕ)
    (edge : Fin n → Fin n → OptionT (StateM σ) Bool)
    (member : Fin n → OptionT (StateM σ) Bool)
    (he : ∀ u v s, clock ((edge u v).run s).2 ≤ clock s + E)
    (hm : ∀ v s, clock ((member v).run s).2 ≤ clock s + M)
    (v u : Fin n) (c : ℕ) (s : σ) :
    clock ((predecessorStep edge member v c u).run s).2 ≤ clock s + (E + M) := by
  unfold predecessorStep
  refine bind_optionT_clock clock E M _ _ (he u v) (fun answer state => ?_) s
  cases answer
  · exact Nat.le_add_right _ _
  · simpa using bind_optionT_clock clock M 0 (member u) _ (hm u)
      (fun hit state => by cases hit <;> exact Nat.le_add_right _ _) state

private theorem countPredecessors_clock {σ : Type} {n : ℕ} (clock : σ → ℕ) (E M : ℕ)
    (edge : Fin n → Fin n → OptionT (StateM σ) Bool)
    (member : Fin n → OptionT (StateM σ) Bool)
    (he : ∀ u v s, clock ((edge u v).run s).2 ≤ clock s + E)
    (hm : ∀ v s, clock ((member v).run s).2 ≤ clock s + M)
    (v : Fin n) (s : σ) :
    clock ((countPredecessors edge member v).run s).2 ≤ clock s + n * (E + M) := by
  apply foldlM_optionT_clock
  exact fun c u => predecessorStep_clock clock E M edge member he hm v u c

private theorem scanVertex_clock {σ : Type} {n : ℕ} (clock : σ → ℕ) (E M : ℕ)
    (edge : Fin n → Fin n → OptionT (StateM σ) Bool)
    (member : Fin n → OptionT (StateM σ) Bool)
    (he : ∀ u v s, clock ((edge u v).run s).2 ≤ clock s + E)
    (hm : ∀ v s, clock ((member v).run s).2 ≤ clock s + M)
    (k : ℕ) (a : RoundUpdate) (v : Fin n) (s : σ) :
    clock ((scanVertex edge member k a v).run s).2 ≤ clock s + (M + n * (E + M)) := by
  unfold scanVertex
  refine bind_optionT_clock clock M (n * (E + M)) _ _ (hm v) (fun answer state => ?_) s
  cases answer
  · simpa using bind_optionT_clock clock (n * (E + M)) 0 (countPredecessors edge member v)
      (fun p => pure (a.addVertex k p))
      (countPredecessors_clock clock E M edge member he hm v)
      (fun _ s' => Nat.le_refl (clock s')) state
  · change clock state ≤ _
    omega

/-- Arbitrary replying or rejecting callbacks cost at most one membership test per vertex,
then at most one edge and one membership test per predecessor. Tied rounds are covered. -/
theorem scanNextRound_clock {σ : Type} {n : ℕ} (clock : σ → ℕ) (E M : ℕ)
    (edge : Fin n → Fin n → OptionT (StateM σ) Bool)
    (member : MembershipScan (OptionT (StateM σ)) n) (k : ℕ) (t : Tally)
    (he : ∀ u v s, clock ((edge u v).run s).2 ≤ clock s + E)
    (hm : ∀ v s, clock ((member k t v).run s).2 ≤ clock s + M) (s : σ) :
    clock ((scanNextRound edge member k t).run s).2 ≤
      clock s + n * (M + n * (E + M)) := by
  apply foldlM_optionT_clock
  exact fun a v => scanVertex_clock clock E M edge (member k t) he hm k a v

/-- A fuel-bounded run spends at most the round budget per unit of fuel, plus one terminal
membership budget. Only radii below `limit` need a membership certificate. -/
theorem runRounds_clock {σ : Type} {n : ℕ} (clock : σ → ℕ) (E M limit : ℕ)
    (edge : Fin n → Fin n → OptionT (StateM σ) Bool)
    (member : MembershipScan (OptionT (StateM σ)) n)
    (he : ∀ u v s, clock ((edge u v).run s).2 ≤ clock s + E)
    (hm : ∀ k < limit, ∀ t v s, clock ((member k t v).run s).2 ≤ clock s + M)
    (target : Fin n) (fuel k : ℕ) (t : Tally) (hk : k + fuel ≤ limit) (s : σ) :
    clock ((runRounds edge member target fuel k t).run s).2 ≤
      clock s + fuel * (n * (M + n * (E + M))) + M := by
  induction fuel generalizing k t s with
  | zero => change clock s ≤ _; omega
  | succ fuel ih =>
    have hkl : k < limit := by omega
    rw [runRounds, runRoundsWith]
    calc
      _ ≤ clock s + (n * (M + n * (E + M)) +
          (fuel * (n * (M + n * (E + M))) + M)) := by
        refine bind_optionT_clock clock (n * (M + n * (E + M)))
          (fuel * (n * (M + n * (E + M))) + M) _ _
          (scanNextRound_clock clock E M edge member k t he (hm k hkl t))
          (fun a state => ?_) s
        split
        · change clock state ≤ _; omega
        split
        · have h := bind_optionT_clock clock M 0 (member k t target)
            (fun hit => pure (some (ControllerVerdict.decided hit))) (hm k hkl t target)
            (fun _ s' => Nat.le_refl (clock s')) state
          simp only [Nat.add_zero] at h
          exact h.trans (by omega)
        · simpa only [runRounds, Nat.add_assoc] using ih (k + 1) a.tally (by omega) state
      _ = _ := by rw [Nat.succ_mul]; omega

/-- The actual controller uses at most `n³` edge calls and `n³+n²+1` membership calls.
Set `(E,M)` to `(1,0)` or `(0,1)` for separate counters; arbitrary weighted callback clocks
compose through the same statement. The final state includes charges on rejecting branches. -/
theorem runController_clock {σ : Type} {n : ℕ} (clock : σ → ℕ) (E M : ℕ)
    (edge : Fin n → Fin n → OptionT (StateM σ) Bool)
    (member : MembershipScan (OptionT (StateM σ)) n)
    (he : ∀ u v s, clock ((edge u v).run s).2 ≤ clock s + E)
    (hm : ∀ k < n, ∀ t v s, clock ((member k t v).run s).2 ≤ clock s + M)
    (target : Fin n) (s : σ) :
    clock ((runController edge member target).run s).2 ≤
      clock s + n * n * n * E + (n * n * n + n * n + 1) * M := by
  have h := runRounds_clock clock E M n edge member he hm target n 0 ⟨1, 0⟩ (by simp) s
  simp only [runController]
  calc
    _ ≤ clock s + n * (n * (M + n * (E + M))) + M := h
    _ = _ := by ring

/-- Composing the real membership scan costs at most a degree-five polynomial in `n` primitive
callback actions. Each inner selection, destination read and edge callback costs at most one;
the final tally check costs none. The outer edge query also costs at most one. Rejection retains
its charge. This composes action clocks, not physical runtime or native workspace. -/
theorem runController_scan_clock {σ : Type} {n : ℕ} (clock : σ → ℕ)
    (edge : Fin n → Fin n → OptionT (StateM σ) Bool)
    (select : Fin n → StateM σ Bool) (next : StateM σ (Option (Fin n)))
    (scanEdge : Fin n → Fin n → StateM σ Bool) (source target : Fin n)
    (he : ∀ u v s, clock ((edge u v).run s).2 ≤ clock s + 1)
    (hs : ∀ v s, clock (select v s).2 ≤ clock s + 1)
    (hn : ∀ s, clock (next s).2 ≤ clock s + 1)
    (hse : ∀ u v s, clock (scanEdge u v s).2 ≤ clock s + 1) (s : σ) :
    clock ((runController edge
      (fun k t v => OptionT.mk (Scan.runM select next scanEdge source v k t)) target).run s).2 ≤
      clock s + n * n * n + (n * n * n + n * n + 1) * (n * (2 * n + 2)) := by
  have hmember (k : ℕ) (hk : k < n) (t : Tally) (v : Fin n) (state : σ) :
      clock (Scan.runM select next scanEdge source v k t state).2 ≤
        clock state + n * (2 * n + 2) := by
    have h := Scan.runM_clock clock select next scanEdge source v k t hs hn hse state
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_left n (by omega)) _)
  simpa only [Nat.mul_one] using runController_clock clock 1 (n * (2 * n + 2)) edge
    (fun k t v => OptionT.mk (Scan.runM select next scanEdge source v k t)) he hmember target s

end Cslib.DoubleCounting
