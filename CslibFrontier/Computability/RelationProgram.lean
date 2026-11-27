/-
Copyright (c) 2026 vhalan anandarajah. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vhalan anandarajah
-/

module
-- upstream: candidate

public import Mathlib.Order.FixedPoints
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Finite Boolean relation programs

This formalizes the six positive equation forms on bit-vector addresses from Section 4.1
of [Balasubramanian and Majumdar][BalasubramanianMajumdar2026Pushdown]. The ground facts form a
finite space. The least closed set is obtained by iterating the consequence operator from the
empty set for at most `r * 2 ^ H` steps. This module gives a semantics and a finite decision
procedure. The construction here does not include the paper's pushdown simulation.

## Main definitions

* `Equation`, `Program`, `Fact` describe the finite system.
* `consequence` is its monotone operator and `evaluate` decides derivability.

## Main results

* `derives_fixed`, `derives_iff_all_closed`, `lfp_consequence`, `evaluate_eq_true_iff`.

## References

* [A. R. Balasubramanian, R. Majumdar, Pushdown Reachability Requires N² Time on Multitape Turing
  Machines][BalasubramanianMajumdar2026Pushdown], arXiv:2611.27814v2, Section 4.1.
-/

@[expose] public section

namespace Cslib.RelationProgram

variable {r H : ℕ}

/-- The six positive equation forms in Balasubramanian and Majumdar's
relation programs. Assignment modifies the queried address, not the program. -/
inductive Equation (r H : Nat)
  | top
  | bot
  | test (position : Fin H) (value : Bool)
  | disj (left right : Fin r)
  | conj (left right : Fin r)
  | write (source : Fin r) (position : Fin H) (value : Bool)

/-- One positive equation for each predicate. -/
abbrev Program (r H : Nat) := Fin r → Equation r H
/-- An application of a predicate to a Boolean address. -/
structure Fact (r H : ℕ) where
  /-- Predicate applied by this fact. -/
  predicate : Fin r
  /-- Its Boolean address. -/
  address : BitVec H
  deriving DecidableEq

/-- Set one bit of an address, preserving the other bits. -/
def overwrite (u : BitVec H) (p : Fin H) (b : Bool) : BitVec H :=
  let mask := BitVec.twoPow H p.val
  if b then u ||| mask else u &&& ~~~mask

/-- Reading an overwritten bit returns the new value. Other bits are unchanged. -/
theorem overwrite_bit (u : BitVec H) (p q : Fin H) (b : Bool) :
    (overwrite u p b).getLsbD q.val = (if p.val = q.val then b else u.getLsbD q.val) := by
  cases b <;> by_cases e : p.val = q.val <;>
    simp [overwrite, q.isLt, e, eq_comm]


/-- Apply all positive equations once to a candidate set of facts. -/
def step (P : Program r H) (X : Fact r H → Prop) (f : Fact r H) : Prop :=
  match P f.predicate with
  | .top => True
  | .bot => False
  | .test p b => f.address.getLsbD p.val = b
  | .disj a b => X ⟨a, f.address⟩ ∨ X ⟨b, f.address⟩
  | .conj a b => X ⟨a, f.address⟩ ∧ X ⟨b, f.address⟩
  | .write a p b => X ⟨a, overwrite f.address p b⟩

/-- The consequence operator is monotone. -/
theorem step_mono (P : Program r H) {X Y : Fact r H → Prop}
    (h : ∀ f, X f → Y f) (f : Fact r H) : step P X f → step P Y f := by
  unfold step
  split
  · exact id
  · exact id
  · exact id
  · exact Or.imp (h _) (h _)
  · exact And.imp (h _) (h _)
  · exact h _

/-- Iterate the consequence operator starting with no facts. -/
def stage (P : Program r H) : Nat → Fact r H → Prop
  | 0 => fun _ => False
  | j + 1 => step P (stage P j)

/-- Later stages contain every fact from earlier stages. -/
theorem stage_le (P : Program r H) {i j : Nat} (h : i ≤ j) (f : Fact r H) :
    stage P i f → stage P j f := by
  have next (k : Nat) (f : Fact r H) : stage P k f → stage P (k + 1) f := by
    induction k generalizing f with
    | zero => simp [stage]
    | succ k ih => exact step_mono P ih f
  induction h with
  | refl => exact id
  | step _ ih => exact fun hf => next _ _ (ih hf)

/-- A fact is derivable if it occurs at a finite stage. -/
def derives (P : Program r H) (f : Fact r H) : Prop := ∃ j, stage P j f

/-- A set is closed when it contains all of its immediate consequences. -/
def Closed (P : Program r H) (X : Fact r H → Prop) : Prop :=
  ∀ f, step P X f → X f

/-- The set of derivable facts is closed. -/
theorem derives_closed (P : Program r H) : Closed P (derives P) := by
  rintro ⟨a, u⟩
  unfold step
  split
  · intro _
    exact ⟨1, by simp_all [stage, step]⟩
  · exact False.elim
  · intro h
    exact ⟨1, by simpa [stage, step, *] using h⟩
  · rintro (⟨i, hi⟩ | ⟨j, hj⟩)
    · exact ⟨i + 1, by simp_all [stage, step]⟩
    · exact ⟨j + 1, by simp_all [stage, step]⟩
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨max i j + 1, by
      simpa [stage, step, *] using
        And.intro (stage_le P (le_max_left i j) _ hi) (stage_le P (le_max_right i j) _ hj)⟩
  · rintro ⟨i, hi⟩
    exact ⟨i + 1, by simp [stage, step, *]⟩

/-- A fact is derivable exactly when every closed set contains it. -/
theorem derives_iff_all_closed (P : Program r H) (f : Fact r H) :
    derives P f ↔ ∀ X, Closed P X → X f := by
  constructor
  · rintro ⟨j, hj⟩ X hX
    have subset (i : Nat) : ∀ g, stage P i g → X g := by
      induction i with
      | zero => intro g h; exact h.elim
      | succ i ih => exact fun g hg => hX g (step_mono P ih g hg)
    exact subset j f hj
  · exact fun hall => hall (derives P) (derives_closed P)

/-- One consequence step preserves the derivable facts. -/
theorem derives_fixed (P : Program r H) (f : Fact r H) :
    step P (derives P) f ↔ derives P f := by
  refine ⟨derives_closed P f, ?_⟩
  rintro ⟨_ | j, hj⟩
  · exact hj.elim
  · exact step_mono P (fun g hg => ⟨j, hg⟩) f hj

/-- Flatten the predicate and address into a binary variable index. -/
def name (f : Fact r H) : Nat := f.predicate.val * 2 ^ H + f.address.toNat

/-- The variable index is bounded by the number of ground facts. -/
theorem name_lt (f : Fact r H) : name f < r * 2 ^ H := by
  calc
    _ < (f.predicate.val + 1) * 2 ^ H := by
      rw [name, Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left f.address.isLt _
    _ ≤ _ := Nat.mul_le_mul_right _ f.predicate.isLt

/-- Distinct ground facts get distinct indices. -/
theorem name_injective : Function.Injective (@name r H) := by
  rintro ⟨a, u⟩ ⟨b, v⟩ h
  have pos : 0 < 2 ^ H := Nat.pow_pos (by decide)
  change a.val * 2 ^ H + u.toNat = b.val * 2 ^ H + v.toNat at h
  have add (i j : Nat) (hj : j < 2 ^ H) :
      (i * 2 ^ H + j) / (2 ^ H) = i := by
    rw [Nat.mul_comm, Nat.mul_add_div pos, Nat.div_eq_of_lt hj, Nat.add_zero]
  have e := congrArg (· / (2 ^ H)) h
  rw [add _ _ u.isLt, add _ _ v.isLt] at e
  have ab : a = b := Fin.ext e
  subst b
  have huv := BitVec.eq_of_toNat_eq (Nat.add_left_cancel h)
  subst v
  rfl

/-- Enumerate all ground facts in predicate and address order. -/
def facts (r H : Nat) : List (Fact r H) :=
  (List.finRange r).flatMap fun a =>
    (List.finRange (2 ^ H)).map fun u => ⟨a, BitVec.ofFin u⟩

/-- The finite enumeration contains every ground fact. -/
theorem mem_facts (f : Fact r H) : f ∈ facts r H := by
  rcases f with ⟨a, u⟩
  exact List.mem_flatMap.mpr ⟨a, by simp, List.mem_map.mpr ⟨u.toFin, by simp, by simp⟩⟩

/-- There are `r * 2 ^ H` ground facts. -/
theorem facts_length (r H : Nat) : (facts r H).length = r * 2 ^ H := by
  simp [facts, List.length_flatMap, List.map_const', List.sum_replicate]

/-- The order homomorphism on sets of ground facts induced by a relation program. -/
def consequence (P : Program r H) : Set (Fact r H) →o Set (Fact r H) where
  toFun X := {f | step P (· ∈ X) f}
  monotone' _ _ h := fun f => step_mono P h f

/-- The least fixed point of the consequence operator is the set of derivable facts. -/
theorem lfp_consequence (P : Program r H) : (consequence P).lfp = {f | derives P f} := by
  apply le_antisymm
  · exact OrderHom.lfp_le (consequence P) (derives_closed P)
  · intro f hf
    apply (derives_iff_all_closed P f).mp hf (· ∈ (consequence P).lfp)
    intro g hg
    change g ∈ consequence P (consequence P).lfp at hg
    rwa [OrderHom.map_lfp] at hg

/-- Iteration over the grounded facts reaches the least model in at most one stage per fact. -/
theorem derives_iff_stage_card (P : Program r H) (f : Fact r H) :
    derives P f ↔ stage P (r * 2 ^ H) f := by
  classical
  let N := r * 2 ^ H
  let groundFacts := (facts r H).toFinset
  let level (i : ℕ) := groundFacts.filter (stage P i)
  have memLevel (i : ℕ) (g : Fact r H) : g ∈ level i ↔ stage P i g := by
    simp [level, groundFacts, mem_facts]
  have bound (i : ℕ) : (level i).card ≤ N :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      ((List.toFinset_card_le _).trans_eq (facts_length r H))
  have stationary : ∃ i ≤ N, level i = level (i + 1) := by
    by_contra! h
    have growth (i : ℕ) (hi : i ≤ N + 1) : i ≤ (level i).card := by
      induction i with
      | zero => exact Nat.zero_le _
      | succ i ih =>
        have sub : level i ⊆ level (i + 1) := fun g hg =>
          (memLevel _ g).mpr (stage_le P (Nat.le_succ i) _ ((memLevel _ g).mp hg))
        have strict : level i ⊂ level (i + 1) :=
          Finset.ssubset_iff_subset_ne.mpr ⟨sub, h i (by omega)⟩
        exact Nat.succ_le_of_lt ((ih (by omega)).trans_lt (Finset.card_lt_card strict))
    have hcard := growth (N + 1) le_rfl
    have hbound := bound (N + 1)
    omega
  obtain ⟨i, hi, eq⟩ := stationary
  have closed : Closed P (stage P i) := by
    intro g hg
    apply (memLevel i g).mp
    rw [eq]
    exact (memLevel (i + 1) g).mpr hg
  exact ⟨fun h => stage_le P hi f ((derives_iff_all_closed P f).mp h _ closed),
    fun h => ⟨N, h⟩⟩

/-- One executable round of the positive equations. -/
def next (P : Program r H) (X : Fact r H → Bool) (f : Fact r H) : Bool :=
  match P f.predicate with
  | .top => true
  | .bot => false
  | .test p b => f.address.getLsbD p.val == b
  | .disj a b => X ⟨a, f.address⟩ || X ⟨b, f.address⟩
  | .conj a b => X ⟨a, f.address⟩ && X ⟨b, f.address⟩
  | .write a p b => X ⟨a, overwrite f.address p b⟩

private theorem next_eq_true (P : Program r H) (X : Fact r H → Bool) (f : Fact r H) :
    next P X f = true ↔ step P (fun g => X g = true) f := by
  unfold next step
  split <;> simp

private theorem iterate_next_eq_true (P : Program r H) (i : ℕ) (f : Fact r H) :
    ((next P)^[i] (fun _ => false)) f = true ↔ stage P i f := by
  induction i generalizing f with
  | zero => simp [stage]
  | succ i ih =>
    rw [Function.iterate_succ_apply', next_eq_true, stage]
    have eq : (fun g => ((next P)^[i] (fun _ => false)) g = true) = stage P i :=
      funext fun g => propext (ih g)
    rw [eq]

/-- Decide derivability by iterating over the finite address space. -/
def evaluate (P : Program r H) (f : Fact r H) : Bool :=
  ((next P)^[r * 2 ^ H] (fun _ => false)) f

/-- The executable iteration returns true exactly on derivable facts. -/
theorem evaluate_eq_true_iff (P : Program r H) (f : Fact r H) :
    evaluate P f = true ↔ derives P f :=
  (iterate_next_eq_true P _ f).trans (derives_iff_stage_card P f).symm

end Cslib.RelationProgram
