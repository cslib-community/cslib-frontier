/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.EvalCore
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Accel
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Interpreter.Util
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.EvalRun
import Mathlib.Algebra.Order.Group.Unbundled.Int
import Mathlib.Tactic.Linarith

/-!
# The universal machine: input and result

The input of the universal machine is the word of a tree `z`, its brackets in preorder
(`Interpreter.tbits`). The machine reads the word and builds the tree in its heap, with a frame for
every subtree that is being read (`Uni.sumTo_parse`), and then evaluates the formula with the
code `z.hd` at `z.tl`. For a plain instance `z` the sum of the weights of its runs is the plain
sum `Interpreter.pv θ z`, and the runs are short (`Uni.sumTo_universalMachine`).

## Main definitions

* `Uni.ParsesReturns`, `Uni.initState`.

## Main results

* `Uni.sumTo_parse`: reading a tree.
* `Uni.wellFormed_initState`.
* `Uni.plainValue_one`: the sum `Uni.plainValue` with the factors `1` is `Interpreter.pval`.
* `Uni.sumTo_universalMachine`: the universal machine is exact.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  Proposition I.1 (the part "The pointer machine" of its proof), module `Nc.Uni.TopU`
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Interpreter (Tree Fm Run Plain pv pval evl tbits)

variable {A : Type} [CommRing A] {θ : List Bool → A} {supp : Finset (List Bool)}
  {σ : Config supp} {H : List (Rec RecKind)} {k : ℕ} {S : A} {B : ℤ}

/-- What happens when a tree `o` that has been read is returned to the frame at the
address `k`: the run sum is `S`, within `B` steps. -/
@[expose] def ParsesReturns (θ : List Bool → A) (supp : Finset (List Bool))
    (H : List (Rec RecKind)) (k : ℕ) (inp : List Bool) (o : Tree) (S : A) (B : ℤ) : Prop :=
  ∀ σ : Config supp, InMode σ .parseRec H inp → σ.regs 2 = k →
    Represents σ.heap (σ.regs 1) o → Mach.SumTo (universalMachine θ supp) σ S B

/-- The rules for the mode `parse` read a bracket. -/
private theorem eq_read {r : Rule supp} (hs : (rule θ supp r).src = .parse) :
    r = .base .readEnd ∨ r = .base .readBit := by
  cases r with
  | base r =>
    cases r <;> first | exact .inl rfl | exact .inr rfl | cases hs |
      (rename_i b; cases b <;> cases hs)
  | _ => cases hs

/-- A step that reads the bracket `b`: the rule is chosen by the input. -/
private theorem sumTo_read {b : Bool} {rest : List Bool} (hσ : InMode σ .parse H (b :: rest))
    (h : InMode (step θ σ (.base (bif b then .readBit else .readEnd)) 0 0 0)
        (bif b then .parse else .parseRec) H rest →
      Mach.SumTo (universalMachine θ supp)
        (step θ σ (.base (bif b then .readBit else .readEnd)) 0 0 0) S (B - 1)) :
    Mach.SumTo (universalMachine θ supp) σ S B := by
  have hrec : ((.nil, ![σ.regs (loadReg σ.mode), 0, 0, 0]) : Rec RecKind) ∈ σ.heap := by
    rw [hσ.mode]
    exact hσ.wf.nil_mem hσ.wf.r0
  have h' := h ⟨hσ.wf.step _ 0 0 0, by cases b <;> rfl,
    List.Subset.trans hσ.heap (heap_subset_step σ _ 0 0 0), by
      rw [inp_step, hσ.inp]
      cases b <;> rfl⟩
  have := Mach.SumTo.one (by rw [hσ.mode]; rintro ⟨⟩) _ (fun st => ?_) h'
  · cases b <;> simpa [universalMachine, rule, baseRule, RuleData.basic] using this
  rw [fire_iff hσ.wf hrec, hσ.mode, hσ.inp]
  constructor
  · rintro ⟨e₁, -, e₃, e₄⟩
    refine Prod.ext ?_ e₄
    rcases eq_read e₁ with e | e <;> rw [e] at e₃ ⊢ <;> cases b <;>
      first | rfl | simp [rule, baseRule, RuleData.basic] at e₃
  · rintro rfl
    cases b <;> exact ⟨rfl, rfl, by simp [rule, baseRule, RuleData.basic], rfl⟩

/-- **Reading a tree**: from the mode `parse` with the frame at register `1`, the machine reads
the word of `a`, builds `a` in the heap and returns it to the frame, in `3 * a.size` steps. -/
theorem sumTo_parse (a : Tree) : ∀ (B : ℤ) (H : List (Rec RecKind)) (k : ℕ) (σ : Config supp)
    (rest : List Bool), InMode σ .parse H (tbits a ++ rest) → σ.regs 1 = k →
    ParsesReturns θ supp H k rest a S B →
    Mach.SumTo (universalMachine θ supp) σ S (B + 3 * a.size) := by
  induction a with
  | nil =>
    intro B H k σ rest hσ hk h
    refine sumTo_read hσ fun h₁ => .mono (h _ h₁ hk hσ.wf.r0) (by simp only [Tree.size]; omega)
  | cons a b iha ihb =>
    intro B H k σ rest hσ hk h
    rw [tbits, List.cons_append, List.append_assoc] at hσ
    refine sumTo_read hσ fun h₁ => ?_
    refine .mono (iha (B + 3 * b.size + 2) _ _ _ _ h₁.self rfl fun σ₂ h₂ hk₂ hv => ?_) (by
      simp only [Tree.size]
      omega)
    refine h₂.sumTo_step (h₂.frame_mem hk₂) rfl fun h₃ => ?_
    refine .mono (ihb (B + 1) _ _ _ _ h₃.self rfl fun σ₄ h₄ hk₄ hv' => ?_) (by omega)
    refine h₄.sumTo_step (h₄.frame_mem hk₄) rfl fun h₅ => ?_
    exact .mono (h _ ((h₅.mono h₃.heap).mono h₁.heap) hk
      ⟨_, _, _, mem_heap_step σ₄ _ _ _ _, (hv.step.mono h₄.heap).step, hv'.step⟩) (by omega)

variable (supp) in
/-- The first state: the mode `start₀`, the empty record, and the word of `z` as the input. -/
@[expose] def initState (z : Tree) : Config supp :=
  ⟨.start₀, fun _ => 0, [(.nil, ![0, 0, 0, 0])], 0, tbits z⟩

theorem wellFormed_initState (z : Tree) : WellFormed (initState supp z) :=
  ⟨List.mem_singleton_self _, fun c hc => by rw [List.mem_singleton.1 hc]; exact le_rfl,
    fun c hc c' hc' _ => by rw [List.mem_singleton.1 hc, List.mem_singleton.1 hc'], rfl⟩

/-- The sum over runs that name no constants, with the factors `1`, is the plain value. -/
theorem plainValue_one {l : List (Run A)} (h : ∀ r ∈ l, r.bill = []) :
    plainValue (fun _ => 1) l = pval l := by
  simp only [plainValue, pval, mul_one]
  exact congrArg List.sum (List.map_congr_left fun r hr => by simp [plainWeight, h r hr])

/-- **The universal machine is exact**: started at the word of a plain instance `z`, the sum of
the weights of its accepting runs is the plain sum of `z`, and the runs have at most
`3 * z.size + codeCost supp * τ + 10` steps. -/
theorem sumTo_universalMachine (hθ : ∀ q, q ∉ supp → θ q = 0) {τ : ℕ} {z : Tree}
    (h : Plain θ τ z) : Mach.SumTo (universalMachine θ supp) (initState supp z) (pv θ z)
      (3 * z.size + codeCost supp * τ + 10) := by
  have hC := codeCost_ge (supp := supp)
  have h₀ : InMode (initState supp z) .start₀ (initState supp z).heap (tbits z ++ []) :=
    ⟨wellFormed_initState z, rfl, List.Subset.refl _, (List.append_nil _).symm⟩
  refine h₀.sumTo_step (h₀.wf.nil_mem rfl) rfl fun h₁ => ?_
  have hh := mem_heap_step (θ := θ) (initState supp z) (.base .start₀) 0 0 0
  refine h₁.sumTo_step (h₁.wf.nil_mem rfl) rfl fun h₂ => ?_
  refine .mono (sumTo_parse z (codeCost supp * τ + 3) _ _ _ [] h₂.self rfl
    fun σ₃ h₃ hk₃ hv => ?_) (by linarith)
  refine h₃.sumTo_step (h₃.frame_mem hk₃) rfl fun h₄ => ?_
  obtain ⟨p, q, s, hrec, hp, hq⟩ := hv.step.load h₄.wf
  rw [pv, ← plainValue_one fun r hr => (h.2 r hr).1]
  generalize decide (z ≠ .nil) = c at hrec
  cases c
  all_goals
    refine h₄.sumTo_step hrec rfl fun h₅ => ?_
    refine .mono (EvalsTo.of_ev hθ h.1.ev _ rfl _ _ _ _ ⟨h₅, hp.step, hq.step, rfl⟩ _
      (codeCost supp * τ + 1) fun r hr _ σ₆ h₆ hk₆ _ => ?_) (by omega)
    refine h₆.sumTo_step (h₆.mem_of_eq (heap_subset_step _ _ _ _ _ hh) hk₆) rfl fun h₇ =>
      .mono (.halt rfl h₇.inp src_ne_halt) ?_
    nlinarith [(Nat.cast_le (α := ℤ)).2 (h.2 r hr).2]

end Cslib.Circuits.Arithmetic.Separation.Uni
