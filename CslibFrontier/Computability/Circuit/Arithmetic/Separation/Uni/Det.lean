/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Rules
import Mathlib.Tactic.FinCases

/-!
# The universal machine is deterministic but for the guesses and the input

In each mode, the kind of the loaded record determines the rule (`Uni.nextRule`), except for the
rules that read an input bit or guess (`Uni.IsChosen`). Configurations whose heap has the nil record
at `0`, addresses below the counter and one record per address (`Uni.WellFormed`) stay so
(`Uni.WellFormed.step`). In such a configuration a step fires exactly when its rule matches the mode
and the loaded record (`Uni.fire_iff`), so the run sum is the weight of the forced rule times the
run
sum after it (`Uni.sumTo_rule`), or `0` if no rule matches (`Uni.sumTo_stuck`).

## Main definitions

* `Uni.nextRule`, `Uni.IsChosen`, `Uni.Config`, `Uni.WellFormed`, `Uni.env`, `Uni.step`.

## Main results

* `Uni.nextRule_rule`, `Uni.WellFormed.step`, `Uni.fire_iff`, `Uni.sumTo_rule`, `Uni.sumTo_stuck`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Nc.Uni.Det`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The rule for a mode and the kind of the record that is loaded. -/
@[expose] def nextRule (supp : Finset (List Bool)) : Mode (Name supp) → RecKind → Option (Rule supp)
  | .start₀, .nil => some (.base .start₀)
  | .start₁, .nil => some (.base .start₁)
  | .parseRec, .parseA => some (.base .parseA)
  | .parseRec, .parseB => some (.base .parseB)
  | .parseRec, .parseEnd => some (.base .parseEnd)
  | .start₂, .cons => some (.base (.start₂ true))
  | .start₂, .nil => some (.base (.start₂ false))
  | .eval, .nil => some (.base .evalNil)
  | .eval, .cons => some (.base .evalCons)
  | .decode j, .cons => if h : j.1 < 10 then some (.base (.decodeStep ⟨j.1, h⟩)) else none
  | .decode 0, .nil => some (.base .decode₀)
  | .decode 1, .nil => some (.base .decode₁)
  | .decode 2, .nil => some (.base .decode₂)
  | .decode 3, .nil => some (.base .decode₃)
  | .decode 4, .nil => some (.base .decode₄)
  | .decode 5, .nil => some (.base .decode₅)
  | .decode 6, .nil => some (.base .decode₆)
  | .decode 9, .nil => some (.base .decodeTheta)
  | .frameCons, .cons => some (.base (.frameCons true))
  | .frameCons, .nil => some (.base (.frameCons false))
  | .frameIte, .cons => some (.base (.frameIte true))
  | .frameIte, .nil => some (.base (.frameIte false))
  | .frameRun, .cons => some (.base (.frameRun true))
  | .frameRun, .nil => some (.base (.frameRun false))
  | .ret, .head => some (.base .retHead)
  | .ret, .tail => some (.base .retTail)
  | .ret, .cons₁ => some (.base .retCons₁)
  | .ret, .cons₂ => some (.base .retCons₂)
  | .ret, .ite => some (.base .retIte)
  | .ret, .run₁ => some (.base .retRun₁)
  | .ret, .run₂ => some (.base .retRun₂)
  | .ret, .halt => some (.base .retHalt)
  | .ret, .theta => if h : [] ∈ prefixes supp then some (.thetaStart h) else none
  | .head, .cons => some (.base (.head true))
  | .head, .nil => some (.base (.head false))
  | .tail, .cons => some (.base (.tail true))
  | .tail, .nil => some (.base (.tail false))
  | .ite, .cons => some (.base .iteCons)
  | .ite, .nil => some (.base .iteNil)
  | .ite₁, .cons => some (.base (.ite₁ true))
  | .ite₁, .nil => some (.base (.ite₁ false))
  | .ite₂, .cons => some (.base (.ite₂ true))
  | .ite₂, .nil => some (.base (.ite₂ false))
  | .thetaHead p, .nil => some (.thetaRead p)
  | .thetaHead p, .cons => some (.thetaNext p)
  | .thetaBit p, .cons =>
    if h : p.1 ++ [true] ∈ prefixes supp then some (.thetaBit p ⟨_, h⟩ true rfl) else none
  | .thetaBit p, .nil =>
    if h : p.1 ++ [false] ∈ prefixes supp then some (.thetaBit p ⟨_, h⟩ false rfl) else none
  | _, _ => none

/-- The rules that are chosen by the input or by a guess. -/
def IsChosen (r : Rule supp) : Prop :=
  r = .base .readEnd ∨ r = .base .readBit ∨ ∃ b, r = .base (.decodeGuess b)

theorem nextRule_rule (r : Rule supp) (hr : ¬ IsChosen r) :
    nextRule supp (rule θ supp r).src (rule θ supp r).lk = some r := by
  cases r with
  | base r =>
    cases r with
    | readEnd => exact absurd (Or.inl rfl) hr
    | readBit => exact absurd (Or.inr (Or.inl rfl)) hr
    | decodeGuess b => exact absurd (Or.inr (Or.inr ⟨b, rfl⟩)) hr
    | start₂ b | frameCons b | frameIte b | frameRun b
    | head b | tail b | ite₁ b | ite₂ b => cases b <;> rfl
    | decodeStep j => exact dite_eq_left j.2
    | _ => rfl
  | thetaStart h => exact dite_eq_left h
  | thetaRead _ | thetaNext _ => rfl
  | thetaBit _ p' b hx =>
    obtain ⟨_, hp'⟩ := p'
    cases hx
    cases b <;> exact dite_eq_left hp'

private theorem rd_eq_none (r : Rule supp) (hr : ¬ IsChosen r) : (rule θ supp r).rd = none := by
  cases r with
  | base r =>
    cases r with
    | readEnd => exact absurd (Or.inl rfl) hr
    | readBit => exact absurd (Or.inr (Or.inl rfl)) hr
    | decodeGuess b => exact absurd (Or.inr (Or.inr ⟨b, rfl⟩)) hr
    | _ => rfl
  | _ => rfl

theorem src_ne_halt (r : Rule supp) : (rule θ supp r).src ≠ .halt := by
  cases r with
  | base r =>
    cases r with
    | decodeGuess b => cases b <;> simp [rule, baseRule, RuleData.basic]
    | _ => simp [rule, baseRule, RuleData.basic]
  | _ => simp [rule, RuleData.basic]

/-- States of the universal machine. -/
abbrev Config (supp : Finset (List Bool)) := Mach.State (Mode (Name supp)) RecKind

/-- A heap that can be used. -/
structure WellFormed (σ : Config supp) : Prop where
  nil : ((.nil, ![0, 0, 0, 0]) : Rec RecKind) ∈ σ.heap
  le : ∀ c ∈ σ.heap, c.2 0 ≤ σ.n
  fn : ∀ c ∈ σ.heap, ∀ c' ∈ σ.heap, c.2 0 = c'.2 0 → c = c'
  r0 : σ.regs 0 = 0

/-- The values of the variables. -/
@[expose] def env (σ : Config supp) (p q s : ℕ) : Fin 9 → ℕ :=
  ![σ.regs 0, σ.regs 1, σ.regs 2, σ.regs 3, σ.regs 4, p, q, s, σ.n + 1]

/-- The state after a step. -/
@[expose] noncomputable def step (θ : List Bool → A) (σ : Config supp) (r : Rule supp)
    (p q s : ℕ) : Config supp :=
  Mach.nxt (P := universalMachine θ supp) σ (r, env σ p q s)

private theorem dr_zero (r : Rule supp) : (rule θ supp r).dr 0 = 0 := by
  cases r with
  | base r =>
    cases r with
    | decodeGuess b => cases b <;> rfl
    | _ => rfl
  | _ => rfl

theorem WellFormed.step {σ : Config supp} (hσ : WellFormed σ) (r : Rule supp)
    (p q s : ℕ) : WellFormed (step θ σ r p q s) := by
  have ha : (Mach.al (P := universalMachine θ supp) (r, env σ p q s)).2 0 = σ.n + 1 := rfl
  constructor
  · exact List.mem_append_left _ hσ.nil
  · intro c hc
    rcases List.mem_append.1 hc with hc | hc
    · exact (hσ.le c hc).trans (Nat.le_succ _)
    · rw [List.mem_singleton] at hc
      subst hc
      exact ha.le
  · intro c hc c' hc' e
    rcases List.mem_append.1 hc with hc | hc <;> rcases List.mem_append.1 hc' with hc' | hc'
    · exact hσ.fn c hc c' hc' e
    · rw [List.mem_singleton] at hc'
      subst hc'
      have := hσ.le c hc
      omega
    · rw [List.mem_singleton] at hc
      subst hc
      have := hσ.le c' hc'
      omega
    · rw [List.mem_singleton] at hc hc'
      rw [hc, hc']
  · change env σ p q s ((rule θ supp r).dr 0) = 0
    rw [dr_zero]
    exact hσ.r0

theorem heap_subset_step (σ : Config supp) (r : Rule supp)
    (p q s : ℕ) : σ.heap ⊆ (step θ σ r p q s).heap :=
  fun _ hc => List.mem_append_left _ hc

/-- The record that is allocated is in the heap. -/
theorem mem_heap_step (σ : Config supp) (r : Rule supp) (p q s : ℕ) :
    ((rule θ supp r).ak,
        ![σ.n + 1, env σ p q s ((rule θ supp r).af 0), env σ p q s ((rule θ supp r).af 1),
      env σ p q s ((rule θ supp r).af 2)]) ∈ (step θ σ r p q s).heap :=
  List.mem_append_right _ (List.mem_singleton_self _)

theorem inp_step (σ : Config supp) (r : Rule supp) (p q s : ℕ) :
    (step θ σ r p q s).inp = σ.inp.drop (rule θ supp r).rd.toList.length := rfl

/-- The possible steps. -/
theorem fire_iff {σ : Config supp} (hσ : WellFormed σ) {κ : RecKind} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (loadReg σ.mode), p, q, s]) ∈ σ.heap)
        (st : (universalMachine θ supp).Step) :
    Mach.Fire σ st ↔ (rule θ supp st.1).src = σ.mode ∧ (rule θ supp st.1).lk = κ ∧
      (rule θ supp st.1).rd.toList <+: σ.inp ∧ st.2 = env σ p q s := by
  have hla : ∀ r,
      (universalMachine θ supp).la r = loadReg (rule θ supp r).src := fun r => la_eq θ supp r
  constructor
  · intro hf
    have hs : (rule θ supp st.1).src = σ.mode := hf.src
    have h0 : (Mach.ld st).2 0 = σ.regs (loadReg σ.mode) := by
      have : (Mach.ld st).2 0 = st.2 (rv ((universalMachine θ supp).la st.1)) := rfl
      rw [this, hf.regs, hla, hs]
    have h1 := hσ.fn _ hf.load _ hrec h0
    have h2 := congrArg Prod.fst h1
    have h3 := fun i => congrFun (congrArg Prod.snd h1) i
    refine ⟨hs, h2, hf.read, ?_⟩
    funext i
    fin_cases i
    exacts [hf.regs 0, hf.regs 1, hf.regs 2, hf.regs 3, hf.regs 4, h3 1, h3 2, h3 3, hf.fresh]
  · rintro ⟨hs, hk, hr, he⟩
    have hregs : ∀ j, st.2 (rv j) = σ.regs j := by
      intro j
      rw [he]
      fin_cases j <;> rfl
    refine ⟨hs, hregs, by rw [he]; rfl, ?_, hr⟩
    have : Mach.ld st = (κ, ![σ.regs (loadReg σ.mode), p, q, s]) := by
      refine Prod.ext hk ?_
      have h0 : st.2 (rv ((universalMachine θ supp).la st.1)) = σ.regs (loadReg σ.mode) :=
          by rw [hregs, hla, hs]
      change ![st.2 (rv ((universalMachine θ supp).la st.1)), st.2 5, st.2 6, st.2 7] = _
      rw [h0, he]
      rfl
    rw [this]
    exact hrec

/-- A rule that applies in a mode other than `parse`, and not to the nil record in the mode
`decode 7`, is not chosen. -/
private theorem not_isChosen {r : Rule supp} {m : Mode (Name supp)} {κ : RecKind}
    (hs : (rule θ supp r).src = m) (hk : (rule θ supp r).lk = κ) (hm : m ≠ .parse)
    (hd : ¬ (m = .decode 7 ∧ κ = .nil)) : ¬ IsChosen r := by
  rintro (rfl | rfl | ⟨b, rfl⟩)
  · exact hm hs.symm
  · exact hm hs.symm
  · cases b <;> exact hd ⟨hs.symm, hk.symm⟩

/-- A step that is forced. -/
theorem sumTo_rule {σ : Config supp} (hσ : WellFormed σ) {κ : RecKind} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (loadReg σ.mode), p, q, s]) ∈ σ.heap) (r : Rule supp)
        (hr : nextRule supp σ.mode κ = some r)
    (hm : σ.mode ≠ .parse) (hd : ¬ (σ.mode = .decode 7 ∧ κ = .nil))
        (hs : (rule θ supp r).src = σ.mode) (hk : (rule θ supp r).lk = κ)
    {S : A} {B : ℤ} (h : Mach.SumTo (universalMachine θ supp) (step θ σ r p q s) S B) :
    Mach.SumTo (universalMachine θ supp) σ ((rule θ supp r).wt * S) (B + 1) := by
  have hz : σ.mode ≠ (universalMachine θ supp).mh := by
    rw [← hs]
    exact src_ne_halt r
  refine Mach.SumTo.one hz (r, env σ p q s) (fun st' => ?_) h
  rw [fire_iff hσ hrec]
  constructor
  · rintro ⟨h1, h2, -, h4⟩
    have h5 := nextRule_rule (θ := θ) st'.1 (not_isChosen h1 h2 hm hd)
    rw [h1, h2, hr] at h5
    exact Prod.ext (Option.some_injective _ h5).symm h4
  · rintro rfl
    refine ⟨hs, hk, ?_, rfl⟩
    rw [rd_eq_none r (not_isChosen hs hk hm hd)]
    exact List.nil_prefix

/-- No rule applies. -/
theorem sumTo_stuck {σ : Config supp} (hσ : WellFormed σ) {κ : RecKind} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (loadReg σ.mode), p, q, s]) ∈ σ.heap) (hr : nextRule supp σ.mode κ = none)
    (hm : σ.mode ≠ .parse) (hd : ¬ (σ.mode = .decode 7 ∧ κ = .nil)) (hz : σ.mode ≠ .halt) (B : ℤ) :
    Mach.SumTo (universalMachine θ supp) σ 0 B := by
  refine Mach.SumTo.none hz (fun st hf => ?_) B
  rw [fire_iff hσ hrec] at hf
  obtain ⟨h1, h2, -, -⟩ := hf
  have h5 := nextRule_rule (θ := θ) st.1 (not_isChosen h1 h2 hm hd)
  rw [h1, h2, hr] at h5
  exact absurd h5 (by simp)

end Cslib.Circuits.Arithmetic.Separation.Uni
