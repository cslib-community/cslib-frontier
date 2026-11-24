/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Det
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Machine
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Trees in the heap, opcodes and names

An address represents a tree when its records spell the tree out (`Uni.Represents`).
`Uni.Returns θ supp H k inp o S B` says what happens when the value `o` is returned to the frame at
address `k`: the run sum is `S` within `B` steps. Reading an opcode takes as many steps as the
opcode (`Uni.sumTo_decode`), and opcodes of `11` or more are stuck (`Uni.sumTo_decode_stuck`), so
a formula reaches the mode of its opcode (`Uni.sumTo_opcode`) or is stuck (`Uni.sumTo_noOpcode`).
Reading a name `w` of `θ` from the heap multiplies by `θ w` (`Uni.sumTo_readName`).

## Main definitions

* `Uni.Represents`, `Uni.Returns`, `Uni.nameLength`.

## Main results

* `Uni.sumTo_base`, `Uni.sumTo_decode`, `Uni.sumTo_decode_stuck`, `Uni.sumTo_opcode`,
  `Uni.sumTo_noOpcode`, `Uni.sumTo_readName`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Cslib.Circuits.Arithmetic.Separation.Uni.EvalU`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Cslib.Circuits.Arithmetic.Separation.Interpreter

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}

/-- The address a represents the tree. -/
@[expose] def Represents (H : List (Rec RecKind)) : ℕ → Tree → Prop
  | a, .nil => a = 0
  | a, .cons t1 t2 => ∃ p q s,
      ((.cons, ![a, p, q, s]) : Rec RecKind) ∈ H ∧ Represents H p t1 ∧ Represents H q t2

theorem Represents.mono {H H' : List (Rec RecKind)} (hH : H ⊆ H')
    {a : ℕ} {t : Tree} (h : Represents H a t) : Represents H' a t := by
  induction t generalizing a with
  | nil => exact h
  | cons t1 t2 ih1 ih2 =>
    obtain ⟨p, q, s, h1, h2, h3⟩ := h
    exact ⟨p, q, s, hH h1, ih1 h2, ih2 h3⟩

/-- The record at an address that represents a tree. -/
theorem Represents.load {σ : Config supp} (hσ : WellFormed σ)
    {a : ℕ} {t : Tree} (h : Represents σ.heap a t) :
    ∃ p q s,
        ((consOrNil (decide (t ≠ .nil)), ![a, p, q, s]) : Rec RecKind) ∈ σ.heap ∧
            Represents σ.heap p t.hd ∧ Represents σ.heap q t.tl := by
  cases t with
  | nil =>
    have h0 : a = 0 := h
    subst h0
    exact ⟨0, 0, 0, hσ.nil, rfl, rfl⟩
  | cons t1 t2 =>
    obtain ⟨p, q, s, h1, h2, h3⟩ := h
    exact ⟨p, q, s, h1, h2, h3⟩

/-- What happens when the value o is returned to the frame k. -/
@[expose] def Returns (θ : List Bool → A) (supp : Finset (List Bool)) (H : List (Rec RecKind))
    (k : ℕ) (inp : List Bool) (o : Tree) (S : A)
    (B : ℤ) : Prop :=
  ∀ (σ : Config supp) (v : ℕ),
      WellFormed σ → σ.mode = .ret → σ.regs 1 = v → σ.regs 2 = k → H ⊆ σ.heap → σ.inp = inp →
    Represents σ.heap v o → Mach.SumTo (universalMachine θ supp) σ S B

theorem Returns.heap {H H' : List (Rec RecKind)} (hH : H ⊆ H')
    {k : ℕ} {inp : List Bool} {o : Tree} {S : A} {B : ℤ}
    (h : Returns θ supp H k inp o S B) : Returns θ supp H' k inp o S B :=
  fun σ v h1 h2 h3 h4 h5 h6 h7 => h σ v h1 h2 h3 h4 (fun _ hc => h5 (hH hc)) h6 h7

theorem baseRule_wt (r : BaseRule) : (baseRule r : RuleData A (Name supp)).wt = 1 := by
  cases r with
  | decodeGuess b => cases b <;> rfl
  | _ => rfl

/-- A forced step with a rule without names. -/
theorem sumTo_base {σ : Config supp} (hσ : WellFormed σ) {κ : RecKind} {p q s : ℕ}
    (hrec : (κ, ![σ.regs (loadReg σ.mode), p, q, s]) ∈ σ.heap) (r : BaseRule)
        (hr : nextRule supp σ.mode κ = some (.base r))
    (hm : σ.mode ≠ .parse) (hd : ¬ (σ.mode = .decode 7 ∧ κ = .nil))
        (hs : (baseRule r : RuleData A (Name supp)).src = σ.mode)
    (hk : (baseRule r : RuleData A (Name supp)).lk = κ)
    {S : A} {B : ℤ} (h : Mach.SumTo (universalMachine θ supp) (step θ σ (.base r) p q s) S B) :
    Mach.SumTo (universalMachine θ supp) σ S (B + 1) := by
  have h1 := sumTo_rule hσ hrec (.base r) hr hm hd hs hk h
  have h2 : (rule θ supp (.base r)).wt = 1 := baseRule_wt r
  rw [h2, one_mul] at h1
  exact h1

theorem rd_base (r : BaseRule) (h : r ≠ .readEnd)
    (h' : r ≠ .readBit) : (rule θ supp (.base r)).rd = none := by
  cases r with
  | readEnd => exact absurd rfl h
  | readBit => exact absurd rfl h'
  | decodeGuess b => cases b <;> rfl
  | _ => rfl

theorem inp_step_base (σ : Config supp) (r : BaseRule) (h : r ≠ .readEnd) (h' : r ≠ .readBit)
    (p q s : ℕ) : (step θ σ (.base r) p q s).inp = σ.inp := by
  rw [inp_step, rd_base r h h']
  rfl

/-- Reading the number of an opcode. -/
theorem sumTo_decode {S : A} {B : ℤ} (o : Tree) : ∀ (j : ℕ) (hj : j < 11) (σ : Config supp)
    (po : ℕ), WellFormed σ → σ.mode = .decode ⟨j, hj⟩ →
    σ.regs 1 = po → Represents σ.heap po o → ∀ (hl : j + o.len < 11),
    (∀ σ' : Config supp,
        WellFormed σ' → σ'.mode = .decode ⟨j + o.len, hl⟩ → σ'.regs 1 = 0 → σ'.regs 2 = σ.regs 2 →
      σ'.regs 3 = σ.regs 3 → σ'.regs 4 = σ.regs 4 → σ.heap ⊆ σ'.heap → σ'.inp = σ.inp →
          Mach.SumTo (universalMachine θ supp) σ' S B) →
    Mach.SumTo (universalMachine θ supp) σ S (B + o.len) := by
  induction o with
  | nil =>
    intro j hj σ po hσ hm h1 hr hl h
    have h0 : po = 0 := hr
    subst h0
    have := h σ hσ hm h1 rfl rfl rfl (fun _ hc => hc) rfl
    simpa [Tree.len] using this
  | cons a b _ ih =>
    intro j hj σ po hσ hm h1 hr hl h
    obtain ⟨p, q, s, hrec, -, hq⟩ := hr
    have hl' : j + 1 + b.len < 11 := by
      simp only [Tree.len] at hl
      omega
    have hj' : j < 10 := by omega
    have hrec' : ((.cons, ![σ.regs (loadReg σ.mode), p, q, s]) : Rec RecKind) ∈ σ.heap := by
      rw [hm]
      change ((.cons, ![σ.regs 1, p, q, s]) : Rec RecKind) ∈ σ.heap
      rw [h1]
      exact hrec
    have h2 := ih (j + 1) (by omega)
        (step θ σ (.base (.decodeStep ⟨j, hj'⟩)) p q s) q (hσ.step _ _ _ _) rfl rfl
      (hq.mono (heap_subset_step σ _ _ _ _)) hl' (fun σ' a1 a2 a3 a4 a5 a6 a7 a8 => h σ' a1 (by
        rw [a2]
        congr 2
        simp only [Tree.len]
        omega) a3 (a4.trans rfl) (a5.trans rfl) (a6.trans rfl)
            (fun _ hc => a7 (heap_subset_step σ _ _ _ _ hc))
        (a8.trans (inp_step_base σ _ (by simp) (by simp) _ _ _)))
    have h3 := sumTo_base hσ hrec' (.decodeStep ⟨j, hj'⟩) (by rw [hm]; exact dite_eq_left hj')
        (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl h2
    refine h3.mono ?_
    simp only [Tree.len]
    push_cast
    omega

/-- Numbers that are no opcodes. -/
theorem sumTo_decode_stuck {B : ℤ} (o : Tree) : ∀ (j : ℕ) (hj : j < 11) (σ : Config supp) (po : ℕ),
    WellFormed σ → σ.mode = .decode ⟨j, hj⟩ →
    σ.regs 1 = po → Represents σ.heap po o → 11 ≤ j + o.len →
        Mach.SumTo (universalMachine θ supp) σ 0 B := by
  induction o generalizing B with
  | nil =>
    intro j hj σ po hσ hm h1 hr hl
    simp only [Tree.len] at hl
    omega
  | cons a b _ ih =>
    intro j hj σ po hσ hm h1 hr hl
    obtain ⟨p, q, s, hrec, -, hq⟩ := hr
    simp only [Tree.len] at hl
    have hrec' : ((.cons, ![σ.regs (loadReg σ.mode), p, q, s]) : Rec RecKind) ∈ σ.heap := by
      rw [hm]
      change ((.cons, ![σ.regs 1, p, q, s]) : Rec RecKind) ∈ σ.heap
      rw [h1]
      exact hrec
    by_cases hj' : j < 10
    · have h2 := ih (B := B - 1) (j + 1) (by omega)
        (step θ σ (.base (.decodeStep ⟨j, hj'⟩)) p q s) q (hσ.step _ _ _ _) rfl rfl
        (hq.mono (heap_subset_step σ _ _ _ _)) (by omega)
      have h3 := sumTo_base hσ hrec' (.decodeStep ⟨j, hj'⟩) (by rw [hm]; exact dite_eq_left hj')
          (by rw [hm]; simp) (by simp)
        (by rw [hm]; rfl) rfl h2
      exact h3.mono (by omega)
    · refine sumTo_stuck hσ hrec' ?_ (by rw [hm]; simp) (by simp) (by rw [hm]; simp) B
      rw [hm]
      exact dite_eq_right hj'

/-- From a formula to its opcode. -/
theorem sumTo_opcode {S : A} {B : ℤ} {σ : Config supp} (hσ : WellFormed σ) (hm : σ.mode = .eval)
    {o a : Tree}
    (hr : Represents σ.heap (σ.regs 1) (.cons o a)) (hl : o.len < 11)
    (h : ∀ σ' : Config supp,
        WellFormed σ' → σ'.mode = .decode ⟨o.len, hl⟩ → σ'.regs 1 = 0 →
            Represents σ'.heap (σ'.regs 2) a →
      σ'.regs 3 = σ.regs 2 → σ'.regs 4 = σ.regs 3 → σ.heap ⊆ σ'.heap → σ'.inp = σ.inp →
      Mach.SumTo (universalMachine θ supp) σ' S B) : Mach.SumTo (universalMachine θ supp) σ S
          (B + 11) := by
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hr
  have hrec' : ((.cons, ![σ.regs (loadReg σ.mode), p, q, s]) : Rec RecKind) ∈ σ.heap := by
    rw [hm]
    exact hrec
  have h2 := sumTo_decode (θ := θ) (S := S) (B := B) o 0 (by omega)
      (step θ σ (.base .evalCons) p q s) p (hσ.step _ _ _ _) rfl rfl
    (hp.mono (heap_subset_step σ _ _ _ _)) (by omega) (fun σ' a1 a2 a3 a4 a5 a6 a7 a8 => by
      refine h σ' a1 (by rw [a2]; congr 2; omega) a3 ?_ (a5.trans rfl) (a6.trans rfl)
        (fun _ hc => a7 (heap_subset_step σ _ _ _ _ hc))
            (a8.trans (inp_step_base σ _ (by simp) (by simp) _ _ _))
      rw [a4]
      exact (hq.mono (heap_subset_step σ _ _ _ _)).mono a7)
  have h3 := sumTo_base hσ hrec' .evalCons (by rw [hm]; rfl) (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl h2
  refine h3.mono ?_
  have : (o.len : ℤ) ≤ 10 := by exact_mod_cast Nat.le_of_lt_succ hl
  linarith

theorem sumTo_noOpcode {B : ℤ} {σ : Config supp} (hσ : WellFormed σ) (hm : σ.mode = .eval)
    {o a : Tree}
    (hr : Represents σ.heap (σ.regs 1) (.cons o a))
        (hl : 11 ≤ o.len) : Mach.SumTo (universalMachine θ supp) σ 0 B := by
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hr
  have hrec' : ((.cons, ![σ.regs (loadReg σ.mode), p, q, s]) : Rec RecKind) ∈ σ.heap := by
    rw [hm]
    exact hrec
  have h2 := sumTo_decode_stuck (θ := θ) (B := B - 1) o 0 (by omega)
      (step θ σ (.base .evalCons) p q s) p (hσ.step _ _ _ _) rfl rfl
    (hp.mono (heap_subset_step σ _ _ _ _)) (by omega)
  have h3 := sumTo_base hσ hrec' .evalCons (by rw [hm]; rfl) (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl h2
  exact h3.mono (by omega)

/-- The bound for the lengths of names. -/
@[expose] def nameLength (supp : Finset (List Bool)) : ℕ := supp.sup List.length

theorem length_le_nameLength {p : List Bool} (hp : p ∈ prefixes supp) : p.length ≤
    nameLength supp := by
  obtain ⟨q, hq, h⟩ := mem_prefixes.1 hp
  exact h.length_le.trans (Finset.le_sup (f := List.length) hq)

theorem theta_eq_zero_of_not_mem {p : List Bool} (hp : p ∉ prefixes supp)
    (hθ : ∀ q, q ∉ supp → θ q = 0) (w : List Bool) : θ (p ++ w) = 0 := by
  refine hθ _ fun h => hp (mem_prefixes.2 ⟨_, h, List.prefix_append _ _⟩)

/-- Reading a name. -/
theorem sumTo_readName (hθ : ∀ q, q ∉ supp → θ q = 0)
    {S : A} {B : ℤ} (w : Tree) : ∀ (p : Name supp) (σ : Config supp), WellFormed σ →
    σ.mode = .thetaHead p → Represents σ.heap (σ.regs 1) w →
        Returns θ supp σ.heap (σ.regs 2) σ.inp .nil S B →
    Mach.SumTo (universalMachine θ supp) σ (θ (p.1 ++ w.path) * S)
        (B + 1 + 2 * (nameLength supp - p.1.length : ℕ)) := by
  induction w with
  | nil =>
    intro p σ hσ hm hr hk
    have h0 : σ.regs 1 = 0 := hr
    have hrec' : ((.nil, ![σ.regs (loadReg σ.mode), 0, 0, 0]) : Rec RecKind) ∈ σ.heap := by
      rw [hm]
      change ((.nil, ![σ.regs 1, 0, 0, 0]) : Rec RecKind) ∈ σ.heap
      rw [h0]
      exact hσ.nil
    have h2 :=
        hk (step θ σ (.thetaRead p) 0 0 0) 0 (hσ.step _ _ _ _) rfl hσ.r0 rfl
            (heap_subset_step σ _ _ _ _) rfl rfl
    have h3 := sumTo_rule hσ hrec' (.thetaRead p) (by rw [hm]; rfl) (by rw [hm]; simp)
        (by rw [hm]; simp)
      (by rw [hm]; rfl) rfl h2
    have hw : (rule θ supp (.thetaRead p)).wt = θ p.1 := rfl
    rw [hw] at h3
    simp only [Tree.path, List.append_nil]
    refine h3.mono ?_
    have : (0 : ℤ) ≤ ((nameLength supp - p.1.length : ℕ) : ℤ) := Int.natCast_nonneg _
    linarith
  | cons a b _ ih =>
    intro p σ hσ hm hr hk
    obtain ⟨pa, pb, s, hrec, ha, hb⟩ := hr
    have hrec' : ((.cons, ![σ.regs (loadReg σ.mode), pa, pb, s]) : Rec RecKind) ∈ σ.heap := by
      rw [hm]
      exact hrec
    let σ1 := step θ σ (.thetaNext p) pa pb s
    have hσ1 : WellFormed σ1 := hσ.step _ _ _ _
    have ha1 : Represents σ1.heap pa a := ha.mono (heap_subset_step σ _ _ _ _)
    have hb1 : Represents σ1.heap pb b := hb.mono (heap_subset_step σ _ _ _ _)
    obtain ⟨x1, x2, x3, hx, -, -⟩ := ha1.load hσ1
    have hrec1 :
        ((consOrNil (decide (a ≠ .nil)), ![σ1.regs (loadReg σ1.mode), x1, x2, x3]) : Rec RecKind) ∈
            σ1.heap := hx
    have hpath : (Tree.cons a b).path = decide (a ≠ .nil) :: b.path := rfl
    rw [hpath]
    have key : Mach.SumTo (universalMachine θ supp) σ1 (θ (p.1 ++ decide (a ≠ .nil) :: b.path) * S)
        (B + 2 * (nameLength supp - p.1.length : ℕ)) := by
      generalize decide (a ≠ .nil) = bt at hrec1 ⊢
      have hsplit : p.1 ++ bt :: b.path = (p.1 ++ [bt]) ++ b.path := by simp
      by_cases hp : p.1 ++ [bt] ∈ prefixes supp
      · have hnext : nextRule supp σ1.mode (consOrNil bt) = some (.thetaBit p ⟨_, hp⟩ bt rfl) := by
          change nextRule supp (.thetaBit p) (consOrNil bt) = _
          cases bt
          · exact dite_eq_left hp
          · exact dite_eq_left hp
        have h2 := ih ⟨_, hp⟩ (step θ σ1 (.thetaBit p ⟨_, hp⟩ bt rfl) x1 x2 x3)
            (hσ1.step _ _ _ _) rfl
          (hb1.mono (heap_subset_step σ1 _ _ _ _))
              (Returns.heap
                  (fun _ hc => heap_subset_step σ1 _ _ _ _ (heap_subset_step σ _ _ _ _ hc)) hk)
        have h3 := sumTo_rule hσ1 hrec1 _ hnext (by change Mode.thetaBit p ≠ .parse; simp)
          (by rintro ⟨h, -⟩; exact absurd h (by change Mode.thetaBit p ≠ .decode 7; simp)) rfl rfl
              h2
        have hw : (rule θ supp (.thetaBit p ⟨_, hp⟩ bt rfl)).wt = 1 := rfl
        rw [hw, one_mul] at h3
        rw [hsplit]
        refine h3.mono ?_
        have h5 := length_le_nameLength hp
        simp only [List.length_append, List.length_singleton] at h5 ⊢
        have h6 : ((nameLength supp - p.1.length : ℕ) : ℤ) =
            ((nameLength supp - (p.1.length + 1) : ℕ) : ℤ) + 1 := by
          have : nameLength supp - p.1.length = nameLength supp - (p.1.length + 1) + 1 := by omega
          rw [this]
          push_cast
          ring
        rw [h6]
        linarith
      · have hz : θ (p.1 ++ bt :: b.path) = 0 :=
          by rw [hsplit]; exact theta_eq_zero_of_not_mem hp hθ _
        rw [hz, zero_mul]
        refine sumTo_stuck hσ1 hrec1 ?_ (by change Mode.thetaBit p ≠ .parse; simp)
          (by rintro ⟨h, -⟩; exact absurd h (by change Mode.thetaBit p ≠ .decode 7; simp))
              (by change Mode.thetaBit p ≠ .halt; simp) _
        change nextRule supp (.thetaBit p) (consOrNil bt) = none
        cases bt
        · exact dite_eq_right hp
        · exact dite_eq_right hp
    have h3 := sumTo_rule hσ hrec' (.thetaNext p) (by rw [hm]; rfl) (by rw [hm]; simp) (by simp)
      (by rw [hm]; rfl) rfl key
    have hw : (rule θ supp (.thetaNext p)).wt = 1 := rfl
    rw [hw, one_mul] at h3
    exact h3.mono (by linarith)

end Cslib.Circuits.Arithmetic.Separation.Uni
