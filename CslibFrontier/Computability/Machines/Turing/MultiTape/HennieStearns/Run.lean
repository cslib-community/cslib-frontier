/-
Copyright (c) 2026 Bolton Bailey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.HennieStearns.Encode
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Steps of the Hennie–Stearns machine

`hcfg st p A B pA pB out` is the configuration of `hennieStearns tm` in state `st`, with input head
`p`, work tapes `A` and `B` with heads `pA` and `pB`, and output `out`. A step in a move phase
applies `opTr` to the two cells under the work heads (`step_op`), and an `act` changes only the
work tapes and the state (`act_apply`). A run is computed from its steps (`runFrom_of_step`).
-/

@[expose] public section

namespace Turing.MultiTapeTM.HennieStearns

variable {k : ℕ} {Symbol State : Type} {input : List (HSym k Symbol)}

/-- A configuration of the Hennie–Stearns machine. -/
def hcfg (st : Option (HState k State)) (p : Fin (input.length + 2))
    (A B : ℤ → Option (HSym k Symbol)) (pA pB : ℤ) (out : List (HSym k Symbol)) :
    Cfg 2 (HSym k Symbol) (HState k State) input :=
  ⟨st, p, ![A, B], ![pA, pB], out⟩

lemma act_apply (wA : Option (Option (HSym k Symbol))) (mA : SignType)
    (wB : Option (Option (HSym k Symbol))) (mB : SignType) (q : Option (HState k State))
    (st : Option (HState k State)) (p : Fin (input.length + 2)) (A B : ℤ → Option (HSym k Symbol))
    (pA pB : ℤ) (out : List (HSym k Symbol)) :
    (act wA mA wB mB q).apply (hcfg st p A B pA pB out) =
      hcfg q p (wA.elim A (Function.update A pA)) (wB.elim B (Function.update B pB))
        (pA + mA) (pB + mB) out := by
  refine Cfg.ext rfl ?_ ?_ ?_ ?_
  · simp [Action.apply, act, hcfg]
  · funext j
    fin_cases j <;> simp only [Action.apply, act, hcfg] <;> [cases wA; cases wB] <;> rfl
  · funext j
    fin_cases j <;> rfl
  · simp [Action.apply, act, hcfg]

variable (tm : MultiTapeTM k Symbol State)

lemma step_hcfg (st : HState k State) (p : Fin (input.length + 2))
    (A B : ℤ → Option (HSym k Symbol)) (pA pB : ℤ) (out : List (HSym k Symbol)) :
    (hennieStearns tm).step (hcfg (some st) p A B pA pB out) =
      (hsTr tm st (hcfg (some st) p A B pA pB out).inputSymbol ![A pA, B pB]).apply
        (hcfg (some st) p A B pA pB out) := by
  rw [step_of_state rfl]
  simp only [hennieStearns, tr_ofTr]
  congr 2
  funext j
  fin_cases j <;> rfl

lemma step_op (q : State) (mv : Fin k → SignType) (i : Fin k) (ph : Phase)
    (p : Fin (input.length + 2)) (A B : ℤ → Option (HSym k Symbol)) (pA pB : ℤ)
    (out : List (HSym k Symbol)) :
    (hennieStearns tm).step (hcfg (some (.op q mv i ph)) p A B pA pB out) =
      (opTr q mv i ph (readA (A pA)) (readB (B pB))).apply
        (hcfg (some (.op q mv i ph)) p A B pA pB out) := by
  rw [step_hcfg]
  rfl

/-- A run is computed from its steps. -/
lemma runFrom_of_step {G : ℕ → Cfg 2 (HSym k Symbol) (HState k State) input} {W : ℕ}
    (h : ∀ t < W, (hennieStearns tm).step (G t) = G (t + 1)) :
    (hennieStearns tm).runFrom (G 0) W = G W := by
  induction W with
  | zero => rfl
  | succ W ih => rw [runFrom_succ, ih fun t ht => h t (by omega), h W (by omega)]

/-- Runs compose. -/
lemma runFrom_trans {c c' c'' : Cfg 2 (HSym k Symbol) (HState k State) input} {a b : ℕ}
    (h₁ : (hennieStearns tm).runFrom c a = c') (h₂ : (hennieStearns tm).runFrom c' b = c'') :
    (hennieStearns tm).runFrom c (a + b) = c'' := by
  rw [runFrom_add, h₁, h₂]

/-- **Walking.** While the transitions on the cells passed leave the tapes and the state
alone, the heads move by `σA` and `σB` per step. -/
lemma runFrom_walk (q : State) (mv : Fin k → SignType) (i : Fin k) (ph : Phase)
    (p : Fin (input.length + 2)) (A B : ℤ → Option (HSym k Symbol)) (pA pB : ℤ)
    (out : List (HSym k Symbol)) (σA σB : SignType) (W : ℕ)
    (h : ∀ u < W, opTr q mv i ph (readA (A (pA + σA * u))) (readB (B (pB + σB * u))) =
      act none σA none σB (some (.op q mv i ph))) :
    (hennieStearns tm).runFrom (hcfg (some (.op q mv i ph)) p A B pA pB out) W =
      hcfg (some (.op q mv i ph)) p A B (pA + σA * W) (pB + σB * W) out := by
  have := runFrom_of_step tm (G := fun t => hcfg (some (.op q mv i ph)) p A B (pA + σA * t)
    (pB + σB * t) out) (W := W) fun t ht => by
      rw [step_op, h t ht, act_apply]
      simp only [Option.elim_none]
      congr 1 <;> push_cast <;> ring
  simpa only [Nat.cast_zero, mul_zero, add_zero] using this

end Turing.MultiTapeTM.HennieStearns
