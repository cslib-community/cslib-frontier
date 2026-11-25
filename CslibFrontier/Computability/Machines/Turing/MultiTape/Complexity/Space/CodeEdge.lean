/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Space
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.FiniteCases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Cases
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Configuration
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Decode
import CslibFrontier.Tactic.OptionMatch

/-!
# The edge test of view codes in quadratic time and space

The step test of views `Turing.MultiTapeNTM.viewStepB` and the edge test of their codes
`Turing.MultiTapeNTM.codeEdge` run in time and charged space quadratic in their encoded input,
as `Turing.MultiTapeTM.ComputableInO` certificates. The step test branches on the finite key of
the first view (`Turing.MultiTapeTM.ComputableInO.finite_cases`) and compares the second view with
the results of a fixed finite list of actions (`Turing.MultiTapeTM.ComputableInO.list_any`). The
edge test reads the views of both codes and applies the step test. These sharpen the
polynomial-time certificates `Turing.MultiTapeNTM.computableInPolyTime_viewStepB` and
`Turing.MultiTapeNTM.computableInPolyTime_codeEdge`.

## Main results

* `Turing.MultiTapeNTM.computableInO_viewStepB`: the step test in quadratic time and space.
* `Turing.MultiTapeNTM.computableInO_codeEdge`: the edge test in quadratic time and space.
-/

public section

namespace Turing.MultiTapeNTM

open MultiTapeTM

variable {k : ℕ} {State : Type} [Finite State] (ntm : MultiTapeNTM k Bool State)

/-- A comparison against a linearly long computed view costs quadratic time. -/
private theorem quad_bound {N a b s c : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hs : s ≤ c * (a + 1)) :
    N + (N + (a + 1) ^ 2) + (b + 1) * (b + s + 1) ≤ (c + 4) * ((N + 1) ^ 2 + 1) := by
  nlinarith [Nat.mul_le_mul (show b + 1 ≤ N + 1 by omega)
    (show b + s + 1 ≤ (c + 1) * (N + 1) by nlinarith),
    Nat.pow_le_pow_left (show a + 1 ≤ N + 1 by omega) 2]

/-- A comparison against a linearly long computed view costs quadratic space. -/
private theorem lin_bound {N a b s c e : ℕ} (ha : a ≤ N) (hb : b ≤ N) (hs : s ≤ c * (a + 1))
    (he : e = 2 * b + 1 + s) :
    N + (N + a) + e ≤ (c + 4) * ((N + 1) ^ 2 + 1) := by
  nlinarith [Nat.mul_le_mul_left c (show a + 1 ≤ (N + 1) ^ 2 + 1 by nlinarith)]

/-- **The step test of views is quadratic** in time and charged space, in the encoded pair of
views. -/
theorem computableInO_viewStepB :
    ComputableInO ntm.viewStepB (encPair encFiniteCfg encFiniteCfg) encBool
      (fun p => ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2)
      (fun p => ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2) := by
  classical
  -- branch on the finite key of the first view
  let key (views : FiniteCfg k Bool State × FiniteCfg k Bool State) :
      Option State × Option Bool × (Fin k → Option Bool) :=
    (views.1.state, views.1.inputSymbol, views.1.workTapeSymbols)
  let branch (tag : Option State × Option Bool × (Fin k → Option Bool))
      (views : FiniteCfg k Bool State × FiniteCfg k Bool State) : Bool :=
    match tag.1 with
    | none => decide (views.2 = views.1)
    | some state => (ntm.actions state tag.2.1 tag.2.2).any
        fun action => decide (views.2 = (views.1.step action).summarizeOutput)
  have heq : ntm.viewStepB = fun views => branch (key views) views := funext fun _ => rfl
  have h₁ (p : FiniteCfg k Bool State × FiniteCfg k Bool State) :=
    length_le_encPair_left (encFiniteCfg (k := k) (State := State)) encFiniteCfg p
  have h₂ (p : FiniteCfg k Bool State × FiniteCfg k Bool State) :=
    length_le_encPair_right (encFiniteCfg (k := k) (State := State)) encFiniteCfg p
  have hfst := ComputableInO.fst (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  have hsnd := ComputableInO.snd (encFiniteCfg (k := k) (State := State))
    (encFiniteCfg (k := k) (State := State))
  have hkey : ComputableInO key (encPair encFiniteCfg encFiniteCfg)
      (encPair (encFinite _) (encPair (encFinEnum _) (encFinEnum _)))
      (fun p => ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2)
      (fun p => ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2) := by
    refine (ComputableInO.finiteCfg_key.comp hfst).mono 2 (fun p => ?_) fun p => ?_ <;>
    · have := h₁ p
      nlinarith
  have hbranch (tag : Option State × Option Bool × (Fin k → Option Bool)) :
      ComputableInO (branch tag) (encPair encFiniteCfg encFiniteCfg) encBool
        (fun p => ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2)
        (fun p => ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2) := by
    rcases tag with ⟨_ | state, symbol, work⟩
    · refine (ComputableInO.eq' hsnd hfst).mono 4 (fun p => by nlinarith [h₁ p, h₂ p]) fun p => ?_
      simp only [length_encPair]; nlinarith [h₁ p, h₂ p]
    · dsimp only [branch]
      refine (ComputableInO.list_any _ (T := fun p =>
          ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2)
        (S := fun p => ((encPair encFiniteCfg encFiniteCfg p).length + 1) ^ 2) fun action _ => ?_)
        |>.mono 2 (fun _ => by nlinarith) fun _ => by nlinarith
      obtain ⟨c, hc⟩ := ComputableInO.length_encFiniteCfg_step_summarizeOutput_le action
      exact (ComputableInO.eq' hsnd ((ComputableInO.finiteCfg_step_summarizeOutput
        action).comp hfst)).mono (c + 4) (fun p => quad_bound (h₁ p) (h₂ p) (hc p.1))
        fun p => lin_bound (h₁ p) (h₂ p) (hc p.1) (length_encPair _)
  rw [heq]
  exact (ComputableInO.finite_cases hkey hbranch).mono 2 (fun p => by nlinarith)
    fun p => by nlinarith

/-- A square of a linearly bounded quantity is quadratically bounded. -/
private theorem sq_le {L c X : ℕ} (hX : X ≤ c * (L + 1)) : X ^ 2 ≤ c ^ 2 * ((L + 1) ^ 2 + 1) :=
  calc X ^ 2 ≤ (c * (L + 1)) ^ 2 := Nat.pow_le_pow_left hX 2
    _ = c ^ 2 * (L + 1) ^ 2 := mul_pow c (L + 1) 2
    _ ≤ c ^ 2 * ((L + 1) ^ 2 + 1) := Nat.mul_le_mul_left _ (Nat.le_succ _)

/-- A linearly bounded quantity is quadratically bounded. -/
private theorem lin_le {L c X : ℕ} (hX : X ≤ c * (L + 1)) : X ≤ c * ((L + 1) ^ 2 + 1) :=
  hX.trans (Nat.mul_le_mul_left _ (by nlinarith))

/-- Case analysis on the view read from a computed code, within quadratic bounds when the code is
linear and the branch for a view is quadratic in the input paired with the view. -/
private theorem elim_decodeView {γ : Type} {encC : γ ↪ List Bool} {code : γ → List Bool}
    {g : γ × FiniteCfg k Bool State → Bool}
    (hcode : ComputableInO code encC encBits (fun x => (encC x).length)
      (fun x => (encC x).length))
    (hlen : ∀ x, (code x).length ≤ (encC x).length)
    (hg : ComputableInO g (encPair encC encFiniteCfg) encBool
      (fun q => ((encPair encC encFiniteCfg q).length + 1) ^ 2)
      (fun q => ((encPair encC encFiniteCfg q).length + 1) ^ 2)) :
    ComputableInO (fun x => (decodeView (code x)).elim false fun finite => g (x, finite)) encC
      encBool (fun x => ((encC x).length + 1) ^ 2) (fun x => ((encC x).length + 1) ^ 2) := by
  obtain ⟨c, hc⟩ := ComputableInO.length_encOption_decodeView_le (k := k) (State := State)
  have hpre := (ComputableInO.id' (encMid := encC)).prod
    ((ComputableInO.decodeView (k := k) (State := State)).comp hcode)
  refine ((ComputableInO.optionElimSnd (f := fun _ : γ => false) (ComputableInO.const false)
    hg).comp hpre).mono ((c + 2) ^ 2 + c + 5) (fun x => ?_) fun x => ?_ <;>
  · have hL := hlen x
    have hcx := hc (code x)
    have hsq := Nat.pow_le_pow_left (show (code x).length + 1 ≤ (encC x).length + 1 by omega) 2
    have hcx' := Nat.mul_le_mul_left c (show (code x).length + 1 ≤ (encC x).length + 1 by omega)
    simp only [Function.comp_apply, length_encPair]
    cases hv : decodeView (k := k) (State := State) (code x) with
    | none =>
      simp only [Option.elim_none, encOption_none, List.length_nil]
      exact (by nlinarith : _ ≤ 6 * (((encC x).length + 1) ^ 2 + 1)).trans
        (Nat.mul_le_mul_right _ (by nlinarith))
    | some a =>
      rw [hv] at hcx
      simp only [Option.elim_some, encOption_some, List.length_cons] at hcx ⊢
      have hX : 2 * (encC x).length + 1 + (encFiniteCfg a).length + 1 ≤
          (c + 2) * ((encC x).length + 1) := by nlinarith
      nlinarith [sq_le hX, lin_le hX]

/-- **The edge test of codes is quadratic** in time and charged space, in the encoded pair of
codes. -/
theorem computableInO_codeEdge :
    ComputableInO (fun p : List Bool × List Bool => ntm.codeEdge p.1 p.2)
      (encPair encBits encBits) encBool (fun p => (encPair encBits encBits p).length ^ 2)
      fun p => (encPair encBits encBits p).length ^ 2 := by
  classical
  -- the codes and the first view, held while testing the second code
  have hq12 := (ComputableInO.fst (encPair encBits encBits)
    (encFiniteCfg (k := k) (State := State))).snd'
  have hq2 := ComputableInO.snd (encPair encBits encBits) (encFiniteCfg (k := k) (State := State))
  have hhead := (ComputableInDegree.headD (enc₁ := encBool) (enc := encBits)
    false).inO_one.comp_linear hq12
  have hacc := ComputableInO.and'
    (ComputableInO.decideEq' none (ComputableInO.finiteCfg_state.comp_linear hq2))
    (ComputableInO.eq' (ComputableInO.finiteCfg_output.comp_linear hq2)
      (ComputableInO.const [true]))
  have hv : ComputableInO (fun r : ((List Bool × List Bool) × FiniteCfg k Bool State) ×
        FiniteCfg k Bool State => ntm.viewStepB (r.1.2, r.2))
      (encPair (encPair (encPair encBits encBits) encFiniteCfg) encFiniteCfg) encBool
      (fun r => ((encPair (encPair (encPair encBits encBits) encFiniteCfg) encFiniteCfg
        r).length + 1) ^ 2)
      (fun r => ((encPair (encPair (encPair encBits encBits) encFiniteCfg) encFiniteCfg
        r).length + 1) ^ 2) := by
    refine ((ntm.computableInO_viewStepB).comp ((ComputableInO.fst _ _).snd'.prod
      (ComputableInO.snd _ _))).mono 3 (fun r => ?_) fun r => ?_ <;>
    · have h := length_le_encPair_right (encPair encBits encBits)
        (encFiniteCfg (k := k) (State := State)) r.1
      have hle : (encPair encFiniteCfg encFiniteCfg (r.1.2, r.2)).length ≤
          (encPair (encPair (encPair encBits encBits) encFiniteCfg) encFiniteCfg r).length := by
        simp only [length_encPair (p := (r.1.2, r.2)), length_encPair (p := r)]
        omega
      have hsq := Nat.pow_le_pow_left (Nat.add_le_add_right hle 1) 2
      nlinarith
  have hstep := elim_decodeView
    (code := fun q : (List Bool × List Bool) × FiniteCfg k Bool State => q.1.2)
    (g := fun r => ntm.viewStepB (r.1.2, r.2)) hq12
    (fun q => (length_le_encPair_right encBits encBits q.1).trans
      (length_le_encPair_left _ _ q)) hv
  have hout (q : (List Bool × List Bool) × FiniteCfg k Bool State) :
      (encBits q.2.output).length ≤
        (encPair (encPair encBits encBits) encFiniteCfg q).length := by
    simp only [length_encPair, encFiniteCfg_apply]
    omega
  have hpair (q : (List Bool × List Bool) × FiniteCfg k Bool State) :
      (encPair encBits encBits (q.2.output, [true])).length ≤
        2 * (encPair (encPair encBits encBits) encFiniteCfg q).length + 2 := by
    have := hout q
    rw [length_encPair]
    simp only [encBits_apply, List.length_cons, List.length_nil] at this ⊢
    omega
  have htrue : (encBits [true]).length = 1 := rfl
  have hg : ComputableInO (fun q : (List Bool × List Bool) × FiniteCfg k Bool State =>
        if q.1.2.headD false then decide (q.2.state = none) && decide (q.2.output = [true])
        else (decodeView q.1.2).elim false fun next => ntm.viewStepB (q.2, next))
      (encPair (encPair encBits encBits) encFiniteCfg) encBool
      (fun q => ((encPair (encPair encBits encBits) encFiniteCfg q).length + 1) ^ 2)
      (fun q => ((encPair (encPair encBits encBits) encFiniteCfg q).length + 1) ^ 2) := by
    refine (ComputableInO.ite hhead hacc hstep).mono 6 (fun q => ?_) fun q => ?_ <;>
    · have ho := hout q
      have hp := hpair q
      simp only [Function.comp_apply, htrue]
      split_ifs <;> nlinarith [Nat.mul_le_mul (by omega : (encBits q.2.output).length + 1 ≤
        (encPair (encPair encBits encBits) encFiniteCfg q).length + 1) (by omega :
        (encBits q.2.output).length + 1 + 1 ≤
          (encPair (encPair encBits encBits) encFiniteCfg q).length + 1 + 1)]
  have hall := elim_decodeView (encC := encPair encBits encBits) (code := Prod.fst)
    (ComputableInO.fst encBits encBits) (fun p => length_le_encPair_left encBits encBits p) hg
  refine (hall.of_enc_eq fun p => congrArg encBool ?_).mono 4 (fun p => ?_) fun p => ?_
  · unfold codeEdge
    option_match_to_elim; rfl
  all_goals nlinarith [Nat.le_self_pow two_ne_zero (encPair encBits encBits p).length]

end Turing.MultiTapeNTM
