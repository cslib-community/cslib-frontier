/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.SlpStep
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Notation.Indicator
import Mathlib.Algebra.Order.Group.Indicator
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Costs of straight-line programs over all operations on a finite set

`Cslib.Circuits.SlpN inp p H`: the functions of `H` are computed by a straight-line program with
`p` gates over all operations on `Fin D` (`fullSignature 2 (Fin D)`), from the inputs `inp`. Gates
are added one at a time (`Cslib.Circuits.SlpN.snoc`), and the inputs take one gate each
(`Cslib.Circuits.SlpN.inputs`).

`Cslib.Circuits.Cost D A c h` is the calculus on top: `h` is computed in `c` further gates from the
functions of `A`, by constants and binary operations whose values stay below `D`. It is turned into
gates by `Cslib.Circuits.Cost.run` and, for a family, by `Cslib.Circuits.SlpN.stage`.
`Cslib.Circuits.CostP` is the same for properties, through their indicators, with rules for
relations, connectives, bounded quantifiers and choice (`Cslib.Circuits.Cost.ite`).

## Main definitions

* `Cslib.Circuits.SlpN`, `Cslib.Circuits.Cost`, `Cslib.Circuits.CostP`.

## Main results

* `Cslib.Circuits.SlpN.snoc`, `SlpN.le`, `SlpN.inputs`, `Cost.run`, `SlpN.stage`.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  module `Nc.SlpCalc`
-/

public section

namespace Cslib.Circuits

open Finset

variable {Inp : Type} {D n : ℕ}

/-- The functions of `H` (with values in `ℕ`) are computed by a straight-line program with `p`
gates over all operations on `Fin D`, from the inputs `inp`. -/
@[expose] def SlpN (inp : Fin n → Inp → Fin D) (p : ℕ) (H : Set (Inp → ℕ)) : Prop :=
  ∃ P : Program (fullSignature 2 (Fin D)) n p,
    ∀ h ∈ H, ∃ k : Fin p, ∀ x, ((P.eval fullInterpretation (fun i => inp i x) k : Fin D) : ℕ) = h x

variable {inp : Fin n → Inp → Fin D}

theorem SlpN.mono {p : ℕ} {H H' : Set (Inp → ℕ)} (h : SlpN inp p H) (hs : H' ⊆ H) :
    SlpN inp p H' := by
  obtain ⟨P, hP⟩ := h
  exact ⟨P, fun f hf => hP f (hs hf)⟩

theorem SlpN.empty : SlpN inp 0 ∅ := ⟨.empty, fun _ hf => absurd hf (Set.notMem_empty _)⟩

/-- One gate more: an input, a constant, or a binary operation of two computed functions. -/
theorem SlpN.snoc {p : ℕ} {H : Set (Inp → ℕ)} (h : SlpN inp p H) (f : Inp → Fin D)
    (hf : (∃ i, f = inp i) ∨ (∃ c, f = fun _ => c) ∨ ∃ h1 ∈ H, ∃ h2 ∈ H,
        ∃ φ : Fin D → Fin D → Fin D,
      ∀ (x : Inp) (a b : Fin D), (a : ℕ) = h1 x → (b : ℕ) = h2 x → f x = φ a b) :
    SlpN inp (p + 1) (insert (fun x => (f x : ℕ)) H) := by
  obtain ⟨P, hP⟩ := h
  have step : ∃ line : Line (fullSignature 2 (Fin D)) n p, ∀ x,
      line.eval fullInterpretation (fun i => inp i x)
        (P.eval fullInterpretation (fun i => inp i x)) = f x := by
    rcases hf with ⟨i, rfl⟩ | ⟨c, rfl⟩ | ⟨h1, hh1, h2, hh2, φ, hφ⟩
    · exact ⟨⟨.fn fun a => a 0, (![Wire.input i, Wire.input i] : Fin 2 → Wire n p)⟩,
        fun x => rfl⟩
    · exact ⟨⟨.con c, Fin.elim0⟩, fun x => by simp [Line.eval, fullInterpretation]⟩
    · obtain ⟨k1, hk1⟩ := hP h1 hh1
      obtain ⟨k2, hk2⟩ := hP h2 hh2
      refine ⟨⟨.fn fun a => φ (a 0) (a 1), (![Wire.gate k1, Wire.gate k2] : Fin 2 → Wire n p)⟩,
        fun x => ?_⟩
      simp only [Line.eval, fullInterpretation]
      exact (hφ x _ _ (hk1 x) (hk2 x)).symm
  obtain ⟨line, hline⟩ := step
  refine ⟨.gate P line, fun g hg => ?_⟩
  rcases Set.mem_insert_iff.1 hg with rfl | hg
  · exact ⟨Fin.last p, fun x => by rw [Program.eval_gate_last, hline]⟩
  · obtain ⟨k, hk⟩ := hP g hg
    exact ⟨k.castSucc, fun x => by rw [Program.eval_gate_castSucc, hk]⟩

/-- More gates do not hurt. -/
theorem SlpN.le (hD : 0 < D) {p q : ℕ} (hpq : p ≤ q) {H : Set (Inp → ℕ)} (h : SlpN inp p H) :
    SlpN inp q H := by
  induction q, hpq using Nat.le_induction with
  | base => exact h
  | succ q _ ih =>
    exact (ih.snoc (fun _ => ⟨0, hD⟩) (Or.inr (Or.inl ⟨_, rfl⟩))).mono (Set.subset_insert _ _)

/-- The inputs take one gate each. -/
theorem SlpN.inputs (inp : Fin n → Inp → Fin D) :
    SlpN inp n (Set.range fun i x => (inp i x : ℕ)) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact ⟨.empty, by rintro _ ⟨i, -⟩; exact i.elim0⟩
  · obtain ⟨P, hP⟩ := exists_program_of_isSlpStep (p := n) inp
      (fun k => if h : k < n then inp ⟨k, h⟩ else inp ⟨0, hn⟩) fun k hk =>
        Or.inl ⟨⟨k, hk⟩, by simp [hk]⟩
    refine ⟨P, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact ⟨i, fun x => by rw [hP i x]; simp⟩

/-- `h` is computed in at most `c` steps from functions of `A`. -/
inductive Cost (D : ℕ) (A : Set (Inp → ℕ)) : ℕ → (Inp → ℕ) → Prop
  /-- available -/
  | base {h : Inp → ℕ} : h ∈ A → Cost D A 0 h
  /-- constants -/
  | const (c : ℕ) : c < D → Cost D A 1 fun _ => c
  /-- binary operations -/
  | op {p q : ℕ} {h1 h2 : Inp → ℕ} (φ : ℕ → ℕ → ℕ) : Cost D A p h1 → Cost D A q h2 →
      (∀ x, φ (h1 x) (h2 x) < D) → Cost D A (p + q + 1) fun x => φ (h1 x) (h2 x)
  /-- idle steps -/
  | mono {p q : ℕ} {h : Inp → ℕ} : Cost D A p h → p ≤ q → Cost D A q h

variable {A : Set (Inp → ℕ)}

/-- Running a computation. -/
theorem Cost.run (hD : 0 < D) {c : ℕ} {h : Inp → ℕ} (hc : Cost D A c h) :
    ∀ {p : ℕ} {H : Set (Inp → ℕ)}, A ⊆ H → SlpN inp p H → SlpN inp (p + c) (insert h H) := by
  induction hc with
  | base hA =>
    intro p H hs hH
    rw [Set.insert_eq_of_mem (hs hA)]
    exact hH
  | const c hc =>
    intro p H _ hH
    exact hH.snoc (fun _ => ⟨c, hc⟩) (Or.inr (Or.inl ⟨_, rfl⟩))
  | @op p q h1 h2 φ _ _ hφ ih1 ih2 =>
    intro p' H hs hH
    have a1 := ih1 hs hH
    have a2 := ih2 (hs.trans (Set.subset_insert h1 H)) a1
    have a3 := a2.snoc (fun x => ⟨φ (h1 x) (h2 x), hφ x⟩) (Or.inr (Or.inr ⟨h1,
      Set.mem_insert_of_mem _ (Set.mem_insert _ _), h2, Set.mem_insert _ _,
      fun a b => if hlt : φ a b < D then ⟨φ a b, hlt⟩ else ⟨0, hD⟩, by
        intro x a b ha hb
        simp only [ha, hb, dite_eq_left (hφ x)]⟩))
    have e : p' + (p + q + 1) = p' + p + q + 1 := by ring
    rw [e]
    refine a3.mono ?_
    intro f hf
    rcases Set.mem_insert_iff.mp hf with hf | hf
    · rw [hf]; exact Set.mem_insert _ _
    · exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ hf))
  | mono _ hpq ih =>
    intro p' H hs hH
    exact (ih hs hH).le hD (by omega)

/-- A family of functions. -/
theorem SlpN.stage (hD : 0 < D)
    {κ : Type*} [Fintype κ] {p : ℕ} {H : Set (Inp → ℕ)} (h : SlpN inp p H)
    (f : κ → Inp → ℕ) (c : ℕ) (hf : ∀ i, Cost D H c (f i)) :
    SlpN inp (p + Fintype.card κ * c) (H ∪ Set.range f) := by
  classical
  have : ∀ s : Finset κ, SlpN inp (p + s.card * c) (H ∪ f '' (s : Set κ)) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using h
    | insert i s hi ih =>
      rw [card_insert_of_notMem hi]
      have e : p + (s.card + 1) * c = p + s.card * c + c := by ring
      rw [e]
      refine ((hf i).run hD Set.subset_union_left ih).mono ?_
      intro g hg
      rcases hg with hg | ⟨j, hj, rfl⟩
      · exact Set.mem_insert_of_mem _ (Or.inl hg)
      · rcases mem_insert.mp (mem_coe.mp hj) with h | h
        · subst h; exact Set.mem_insert _ _
        · exact Set.mem_insert_of_mem _ (Or.inr ⟨j, mem_coe.mpr h, rfl⟩)
  have h2 := this univ
  rw [coe_univ, Set.image_univ, card_univ] at h2
  exact h2

namespace Cost

lemma congr {c : ℕ} {h h' : Inp → ℕ} (hc : Cost D A c h) (e : ∀ x, h x = h' x) : Cost D A c h' := by
  have : h = h' := funext e
  rwa [← this]

lemma weaken {A' : Set (Inp → ℕ)} (hA : A ⊆ A') {c : ℕ} {h : Inp → ℕ} (hc : Cost D A c h) :
    Cost D A' c h := by
  induction hc with
  | base hh => exact base (hA hh)
  | const c hc => exact const c hc
  | op φ _ _ hφ ih1 ih2 => exact op φ ih1 ih2 hφ
  | mono _ hpq ih => exact mono ih hpq

/-- A unary operation. -/
lemma op1 (hD : 0 < D) {p : ℕ} {h : Inp → ℕ} (φ : ℕ → ℕ) (hc : Cost D A p h)
    (hφ : ∀ x, φ (h x) < D) :
    Cost D A (p + 2) fun x => φ (h x) :=
  op (fun a _ => φ a) hc (const 0 hD) hφ

/-- Sums. -/
lemma sum (hD : 0 < D) {κ : Type*} (s : Finset κ)
    {c : ℕ} {h : κ → Inp → ℕ} (hc : ∀ i ∈ s, Cost D A c (h i))
    (hb : ∀ x, ∑ i ∈ s, h i x < D) : Cost D A (s.card * (c + 1) + 1) fun x => ∑ i ∈ s, h i x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (A := A) 0 hD
  | insert i s hi ih =>
    have hb' : ∀ x, ∑ i ∈ s, h i x < D := fun x => by
      have := hb x
      rw [sum_insert hi] at this
      omega
    have h1 := ih (fun j hj => hc j (mem_insert_of_mem hj)) hb'
    have h2 := op (fun a b => a + b) (hc i (mem_insert_self _ _)) h1 (fun x => by
      have := hb x
      rw [sum_insert hi] at this
      exact this)
    refine (h2.congr fun x => by rw [sum_insert hi]).mono ?_
    rw [card_insert_of_notMem hi]
    ring_nf
    omega

end Cost

/-- A property is decided in at most `c` steps. -/
def CostP (D : ℕ) (A : Set (Inp → ℕ)) (c : ℕ) (P : Inp → Prop) : Prop :=
  Cost D A c ({x | P x}.indicator 1)

/-- A property is decided in `c` steps when its indicator is computed in `c` steps. -/
theorem costP_iff {c : ℕ} {P : Inp → Prop} : CostP D A c P ↔ Cost D A c ({x | P x}.indicator 1) :=
  Iff.rfl

namespace CostP

lemma congr {c : ℕ} {P Q : Inp → Prop} (hc : CostP D A c P) (h : ∀ x, P x ↔ Q x) : CostP D A c Q :=
    by
  have : P = Q := funext fun x => propext (h x)
  rwa [← this]

lemma mono {p q : ℕ} {P : Inp → Prop} (hc : CostP D A p P) (h : p ≤ q) : CostP D A q P :=
    Cost.mono hc h

/-- A relation between two values. -/
lemma rel (hD : 1 < D) {p q : ℕ} {h1 h2 : Inp → ℕ} (r : ℕ → ℕ → Prop) (c1 : Cost D A p h1)
    (c2 : Cost D A q h2) :
    CostP D A (p + q + 1) fun x => r (h1 x) (h2 x) := by
  classical
  have := Cost.op (fun a b => if r a b then 1 else 0) c1 c2 (fun x => by split_ifs <;> omega)
  refine this.congr fun x => ?_
  by_cases h : r (h1 x) (h2 x)
  · rw [Set.indicator_of_mem (s := {x | r (h1 x) (h2 x)}) h, Pi.one_apply, ite_eq_left h]
  · rw [Set.indicator_of_notMem (s := {x | r (h1 x) (h2 x)}) h, ite_eq_right h]

/-- A property of a value. -/
lemma rel1 (hD : 1 < D) {p : ℕ} {h : Inp → ℕ} (r : ℕ → Prop) (c1 : Cost D A p h) :
    CostP D A (p + 2) fun x => r (h x) :=
  rel hD (fun a _ => r a) c1 (Cost.const 0 (by omega))

lemma true' (hD : 1 < D) : CostP D A 1 fun _ => True := by
  refine (Cost.const 1 hD).congr fun x => ?_
  rw [Set.indicator_of_mem (s := {_x : Inp | True}) (a := x) trivial, Pi.one_apply]

lemma false' (hD : 1 < D) : CostP D A 1 fun _ => False := by
  refine (Cost.const 0 (by omega)).congr fun x => ?_
  rw [Set.indicator_of_notMem (s := {_x : Inp | False}) (a := x) (fun h => h)]

/-- A constant property. -/
lemma const (hD : 1 < D) (P : Prop) : CostP D A 1 fun _ => P := by
  by_cases h : P
  · exact (true' hD).congr fun _ => by simp [h]
  · exact (false' hD).congr fun _ => by simp [h]

lemma and (hD : 1 < D) {p q : ℕ} {P Q : Inp → Prop} (c1 : CostP D A p P) (c2 : CostP D A q Q) :
    CostP D A (p + q + 1) fun x => P x ∧ Q x := by
  refine (rel hD (fun a b => a = 1 ∧ b = 1) c1 c2).congr fun x => ?_
  by_cases h1 : P x <;> by_cases h2 : Q x <;> simp [Set.indicator, h1, h2]

lemma or (hD : 1 < D) {p q : ℕ} {P Q : Inp → Prop} (c1 : CostP D A p P) (c2 : CostP D A q Q) :
    CostP D A (p + q + 1) fun x => P x ∨ Q x := by
  refine (rel hD (fun a b => a = 1 ∨ b = 1) c1 c2).congr fun x => ?_
  by_cases h1 : P x <;> by_cases h2 : Q x <;> simp [Set.indicator, h1, h2]

lemma not (hD : 1 < D) {p : ℕ} {P : Inp → Prop} (c1 : CostP D A p P) :
    CostP D A (p + 2) fun x => ¬ P x := by
  refine (rel1 hD (fun a => a = 0) c1).congr fun x => ?_
  by_cases h1 : P x <;> simp [Set.indicator, h1]

lemma exists_mem (hD : 1 < D) {κ : Type*} (s : Finset κ) {c : ℕ} {P : κ → Inp → Prop}
    (hc : ∀ i ∈ s, CostP D A c (P i)) : CostP D A (s.card * (c + 1) + 1) fun x => ∃ i ∈ s,
        P i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((false' hD).congr fun x => by simp).mono (by simp)
  | insert i s hi ih =>
    have h1 := ih fun j hj => hc j (mem_insert_of_mem hj)
    refine ((hc i (mem_insert_self _ _)).or hD h1 |>.congr fun x => by simp).mono ?_
    rw [card_insert_of_notMem hi]
    ring_nf
    omega

lemma forall_mem (hD : 1 < D) {κ : Type*} (s : Finset κ) {c : ℕ} {P : κ → Inp → Prop}
    (hc : ∀ i ∈ s, CostP D A c (P i)) : CostP D A (s.card * (c + 1) + 1) fun x => ∀ i ∈ s,
        P i x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ((true' hD).congr fun x => by simp).mono (by simp)
  | insert i s hi ih =>
    have h1 := ih fun j hj => hc j (mem_insert_of_mem hj)
    refine ((hc i (mem_insert_self _ _)).and hD h1 |>.congr fun x => by simp).mono ?_
    rw [card_insert_of_notMem hi]
    ring_nf
    omega

end CostP

/-- A choice. -/
lemma Cost.ite {c p q : ℕ} {P : Inp → Prop} [DecidablePred P] {h1 h2 : Inp → ℕ}
    (c0 : CostP D A c P) (c1 : Cost D A p h1) (c2 : Cost D A q h2) (b1 : ∀ x, h1 x < D)
        (b2 : ∀ x, h2 x < D) :
    Cost D A (2 * c + p + q + 3) fun x => if P x then h1 x else h2 x := by
  have a1 := Cost.op (fun a b => a * b) c0 c1 (fun x => by
    have : ({x | P x}.indicator 1 : Inp → ℕ) x ≤ 1 := Set.indicator_le_self _ _ x
    have := b1 x
    nlinarith)
  have a2 := Cost.op (fun a b => (1 - a) * b) c0 c2 (fun x => by
    have : ({x | P x}.indicator 1 : Inp → ℕ) x ≤ 1 := Set.indicator_le_self _ _ x
    have := b2 x
    have : 1 - ({x | P x}.indicator 1 : Inp → ℕ) x ≤ 1 := by omega
    nlinarith)
  have a3 := Cost.op (fun a b => a + b) a1 a2 (fun x => by
    have := b1 x
    have := b2 x
    by_cases h : P x
    · simp only [Set.indicator_of_mem (s := {x | P x}) h, Pi.one_apply]; omega
    · simp only [Set.indicator_of_notMem (s := {x | P x}) h]; omega)
  refine (a3.congr fun x => ?_).mono (by ring_nf; omega)
  by_cases h : P x
  · simp only [Set.indicator_of_mem (s := {x | P x}) h, Pi.one_apply, ite_eq_left h]; omega
  · simp only [Set.indicator_of_notMem (s := {x | P x}) h, ite_eq_right h]; omega


end Cslib.Circuits
