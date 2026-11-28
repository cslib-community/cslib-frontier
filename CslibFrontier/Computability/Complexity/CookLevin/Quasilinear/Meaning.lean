/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.CookLevin.Quasilinear.Layout

/-!
# What the constraints of the quasilinear formula say

Each constraint of `Cslib.Complexity.CookLevin.Quasilinear.Layout` consists of gadgets defining
fresh variables and gates asserting something about their outputs. Once the defining gates hold,
the assertions hold exactly when a statement about the other variables does
(`Layout.forall_famCons_iff`): the constants are `true` and `false`; a list of literals holds; some
pattern of a table holds; one list of literals implies another; a number written in binary is the
previous one plus one, minus one or unchanged; a switch selects one of two variables; and the keys
of consecutive sorted records increase, with each symbol read equal to what the previous visit
left.

## Main definitions

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.Meaning`: the statement of each constraint.

## Main results

* `Cslib.Complexity.CookLevin.Quasilinear.Layout.forall_famCons_iff`: the assertions of a
  constraint hold exactly when its statement does.
-/

@[expose] public section

namespace Cslib.Complexity.CookLevin.Quasilinear

open Turing Cslib.BitonicSort

namespace Layout

variable (Λ : Layout) (D : MachineData) (x : List Bool)

/-- The literals of `lits` all hold. -/
abbrev LitsHold (σ : ℕ → Bool) (lits : List (ℕ × Bool)) : Prop := ∀ l ∈ lits, σ l.1 = l.2

/-- The statement of constraint `inst` of family `fam`, about the variables other than the fresh
ones. -/
def Meaning (σ : ℕ → Bool) (fam : Family) (inst : ℕ) : Prop :=
  match fam with
  | .consts => σ vTT = true ∧ σ vFF = false
  | .init => LitsHold σ (Λ.initLits D)
  | .final => LitsHold σ (Λ.finalLits D)
  | .step => ∃ π ∈ Λ.stepPats D inst, LitsHold σ π
  | .inMove =>
    LitsHold σ (Λ.inMoveLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3)) →
      LitsHold σ (Λ.inNextLits (inst / 3 / Λ.I) (inst / 3 % Λ.I) (inst % 3))
  | .inSym =>
    LitsHold σ (Λ.inAtLits (inst / Λ.I) (inst % Λ.I)) →
      LitsHold σ (Λ.inSymLits x (inst / Λ.I) (inst % Λ.I))
  | .workMove =>
    ∀ i < (Λ.posPairs (inst / Λ.k) (inst % Λ.k)).length,
      σ ((Λ.posPairs (inst / Λ.k) (inst % Λ.k)).getD i (0, 0)).2 =
        addTarget (σ (Λ.vRec (inst / Λ.k) (Λ.offTape (inst % Λ.k) + 4)))
          (σ (Λ.vRec (inst / Λ.k) (Λ.offTape (inst % Λ.k) + 5)))
          (fun i => σ ((Λ.posPairs (inst / Λ.k) (inst % Λ.k)).getD i (0, 0)).1) i
  | .switch =>
    σ (Λ.arrAt (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L + 1) (inst / Λ.P % Λ.N)
        (inst % Λ.P)) =
      cond (σ (Λ.vFlag (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L)
          (low (Λ.expo (inst / Λ.P / Λ.N % Λ.L)) (inst / Λ.P % Λ.N))))
        (σ (Λ.arrAt (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L)
          (partner (Λ.expo (inst / Λ.P / Λ.N % Λ.L)) (inst / Λ.P % Λ.N)) (inst % Λ.P)))
        (σ (Λ.arrAt (inst / Λ.P / Λ.N / Λ.L) (inst / Λ.P / Λ.N % Λ.L) (inst / Λ.P % Λ.N)
          (inst % Λ.P)))
  | .sorted =>
    if inst % Λ.N = 0 then
      σ (Λ.arrAt (inst / Λ.N) Λ.L 0 (Λ.τ + Λ.W)) = false ∧
        σ (Λ.arrAt (inst / Λ.N) Λ.L 0 (Λ.τ + Λ.W + 1)) = false
    else
      bitsVal (fun i => σ ((Λ.keyPairs (inst / Λ.N) (inst % Λ.N)).getD i (0, 0)).1)
          (Λ.keyPairs (inst / Λ.N) (inst % Λ.N)).length <
        bitsVal (fun i => σ ((Λ.keyPairs (inst / Λ.N) (inst % Λ.N)).getD i (0, 0)).2)
          (Λ.keyPairs (inst / Λ.N) (inst % Λ.N)).length ∧
      ((∀ p ∈ Λ.samePairs (inst / Λ.N) (inst % Λ.N), σ p.1 = σ p.2) →
        σ (Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W)) =
            σ (Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N - 1) (Λ.τ + Λ.W + 2)) ∧
          σ (Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W + 1)) =
            σ (Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N - 1) (Λ.τ + Λ.W + 3))) ∧
      (σ (Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W)) = true →
        ∀ p ∈ Λ.samePairs (inst / Λ.N) (inst % Λ.N), σ p.1 = σ p.2) ∧
      (σ (Λ.arrAt (inst / Λ.N) Λ.L (inst % Λ.N) (Λ.τ + Λ.W + 1)) = true →
        ∀ p ∈ Λ.samePairs (inst / Λ.N) (inst % Λ.N), σ p.1 = σ p.2)

/-- The pairs of keys of sorted positions have the width of a key. -/
theorem length_keyPairs (j u : ℕ) : (Λ.keyPairs j u).length = Λ.τ + Λ.W := by
  simp [keyPairs]

/-- The pairs of positions of sorted positions have the width of a position. -/
theorem length_samePairs (j u : ℕ) : (Λ.samePairs j u).length = Λ.W := by
  simp [samePairs]

/-- The pairs of positions of a work head have the width of a position. -/
theorem length_posPairs (t j : ℕ) : (Λ.posPairs t j).length = Λ.W := by
  simp [posPairs]

/-- **Once its defining gates hold, the assertions of a constraint hold exactly when its statement
does.** The gadgets of the families other than the constants need the constants. -/
theorem forall_famCons_iff (σ : ℕ → Bool) (fam : Family) (inst : ℕ)
    (hd : ∀ g ∈ Λ.famDefs D x fam inst, g.Holds σ)
    (hc : fam ≠ .consts → σ vTT = true ∧ σ vFF = false) :
    (∀ g ∈ Λ.famCons D x fam inst, g.Holds σ) ↔ Λ.Meaning D x σ fam inst := by
  cases fam
  · -- constants
    simp only [famDefs, famCons, Meaning, List.mem_singleton, forall_eq] at hd ⊢
    rw [Gate.holds_not] at hd
    simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
      Gate.holds_assert, hd]
    cases σ vFF <;> simp
  · obtain ⟨htt, -⟩ := hc (by decide)
    simp only [famDefs, famCons, Meaning] at hd ⊢
    simp only [List.mem_singleton, forall_eq, Gate.holds_assert,
      matchGadget_out σ hd htt, decide_eq_true_iff, LitsHold]
  · obtain ⟨htt, -⟩ := hc (by decide)
    simp only [famDefs, famCons, Meaning] at hd ⊢
    simp only [List.mem_singleton, forall_eq, Gate.holds_assert,
      matchGadget_out σ hd htt, decide_eq_true_iff, LitsHold]
  · obtain ⟨htt, hff⟩ := hc (by decide)
    simp only [famDefs, famCons, Meaning] at hd ⊢
    simp only [List.mem_singleton, forall_eq, Gate.holds_assert,
      tableGadget_out σ hd htt hff, decide_eq_true_iff, LitsHold]
  · obtain ⟨htt, -⟩ := hc (by decide)
    simp only [famDefs, famCons, Meaning] at hd ⊢
    have h1 := matchGadget_out σ (fun g hg => hd g (List.mem_append_left _ hg)) htt
    have h2 := matchGadget_out σ (fun g hg => hd g (List.mem_append_right _ hg)) htt
    simp only [List.mem_singleton, forall_eq, Gate.holds_imp, h1, h2, decide_eq_true_iff,
      LitsHold]
  · obtain ⟨htt, -⟩ := hc (by decide)
    simp only [famDefs, famCons, Meaning] at hd ⊢
    have h1 := matchGadget_out σ (fun g hg => hd g (List.mem_append_left _ hg)) htt
    have h2 := matchGadget_out σ (fun g hg => hd g (List.mem_append_right _ hg)) htt
    simp only [List.mem_singleton, forall_eq, Gate.holds_imp, h1, h2, decide_eq_true_iff,
      LitsHold]
  · obtain ⟨htt, -⟩ := hc (by decide)
    simp only [famDefs, famCons, Meaning] at hd ⊢
    have h := addGadget_out σ hd htt
    rw [length_posPairs] at h
    simp only [List.mem_singleton, forall_eq, Gate.holds_assert, h, decide_eq_true_iff,
      length_posPairs]
  · simp only [famCons, Meaning, List.mem_singleton, forall_eq, Gate.holds_mux]
  · obtain ⟨htt, hff⟩ := hc (by decide)
    simp only [famDefs, famCons, Meaning] at hd ⊢
    split_ifs at hd ⊢ with hu
    · have h0 := hd _ (List.mem_cons_self ..)
      have h1 := hd _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
      rw [Gate.holds_not] at h0 h1
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
        Gate.holds_assert, h0, h1, Bool.not_eq_true']
    · have hlt := ltGadget_out σ
        (fun g hg => hd g (List.mem_append_left _ (List.mem_append_left _ hg))) hff
      have heq := eqGadget_out σ
        (fun g hg => hd g (List.mem_append_left _ (List.mem_append_right _ hg))) htt
      have hx0 := hd _ (List.mem_append_right _ (List.mem_cons_self ..))
      have hx1 := hd _ (List.mem_append_right _ (List.mem_cons_of_mem _
        (List.mem_cons_self ..)))
      rw [Gate.holds_xnor] at hx0 hx1
      rw [length_keyPairs] at hlt
      rw [length_samePairs] at heq
      simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq,
        Gate.holds_assert, Gate.holds_imp, hlt, heq, hx0, hx1, decide_eq_true_iff,
        beq_iff_eq, length_keyPairs]
      tauto

end Layout

end Cslib.Complexity.CookLevin.Quasilinear
