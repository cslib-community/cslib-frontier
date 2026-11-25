/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Order.Filter.Extr

import Mathlib.Basic.Finite.Prod
import Mathlib.Basic.Finite.Sigma
import Mathlib.Order.WellFounded

/-!
# Layered semi-unbounded Boolean circuits and proof trees

A *layered semi-unbounded Boolean circuit* has leaves carrying fixed Boolean values (such as
evaluated input literals), AND gates of fan-in one or two, and unbounded fan-in OR gates, with
every child strictly one layer below its parent. A circuit is in *alternating normal form with an
AND first layer* (`LayeredSemiUnboundedCircuit.InNormalForm`) when layer `0` consists of leaves,
odd layers consist of AND gates, and positive even layers consist of OR gates.

A *proof tree* (`LayeredSemiUnboundedCircuit.ProofTree`) lives in the circuit's tree unfolding:
leaves must evaluate to `true`, AND gates keep all children, and OR gates select one child.
This file develops the structural combinatorics of proof trees (part of work package 1 of
cslib-frontier #7920; original formalization adapting the layered-digraph isolation framework of
`Cslib.LayeredDigraph`):

* `eval_iff_nonempty_proofTree`: a gate evaluates to `true` iff it admits a proof tree.
* `ProofTree.andNodes_level_profile`: in normal form, a proof tree rooted at AND-level `m`
  contains at most `2 ^ (m - k)` copies of AND gates at each AND-level `k ≤ m`.
* `isMinIsolating_of_separated`: if at every OR gate, distinct children have distinct minimum
  proof-tree weights, then bottom-up induction gives every true gate a unique minimum-weight
  proof tree.

## Main definitions

* `Cslib.Circuits.Boolean.AndInputs`: unary or ordered binary inputs of an AND gate.
* `Cslib.Circuits.Boolean.GateKind`: leaf, AND gate, or unbounded OR gate.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit`: layered semi-unbounded circuits.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.InNormalForm`: alternating AND-first-layer
  normal form.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.Eval`: Boolean gate evaluation.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.ProofTree`: inductive proof trees over the
  tree unfolding, with `ProofTree.weight` and `ProofTree.andNodes`.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.IsMinIsolating`: uniqueness of minimum-weight
  proof trees at every gate evaluating to `true`.

## Main results

* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.eval_iff_nonempty_proofTree`: evaluation
  equals existence of a proof tree.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.ProofTree.andNodes_and_profile`: the
  `2 ^ (m - k)` AND-level multiplicity bound below a root AND gate.
* `Cslib.Circuits.Boolean.LayeredSemiUnboundedCircuit.isMinIsolating_of_separated`: separation at
  every OR gate implies min-isolation for every true gate.
-/

public section

namespace Cslib.Circuits.Boolean

/-- The inputs of an AND gate of fan-in one or two. -/
inductive AndInputs (G : Type*) where
  /-- A fan-in-one AND gate with a single child. -/
  | unary (child : G)
  /-- A fan-in-two AND gate with ordered left and right children. -/
  | binary (left right : G)
  deriving DecidableEq

/-- The role of a gate in a layered semi-unbounded circuit. -/
inductive GateKind (G : Type*) where
  /-- A leaf carrying a fixed Boolean truth value (for example an evaluated literal). -/
  | leaf (val : Bool)
  /-- An AND gate of fan-in one or two. -/
  | and (inputs : AndInputs G)
  /-- An unbounded fan-in OR gate, whose children are given by `orChild`. -/
  | or
  deriving DecidableEq

/-- A layered semi-unbounded Boolean circuit: leaves carry Boolean values, AND gates have fan-in
one or two, OR gates have unbounded fan-in (as a child relation with no duplicate edges), and
every child lies strictly one layer below its parent. -/
structure LayeredSemiUnboundedCircuit (G : Type*) where
  /-- The layer of each gate. -/
  layer : G → ℕ
  /-- The gate kind and, for leaves and AND gates, its truth value or inputs. -/
  kind : G → GateKind G
  /-- The child relation for OR gates: `orChild g c` means `c` is an input to OR gate `g`. -/
  orChild : G → G → Prop
  /-- Every child of a fan-in-one AND gate lies one layer below it. -/
  layer_andUnary {g c : G} : kind g = .and (.unary c) → layer c + 1 = layer g
  /-- Both children of a fan-in-two AND gate lie one layer below it. -/
  layer_andBinary {g l r : G} : kind g = .and (.binary l r) →
    layer l + 1 = layer g ∧ layer r + 1 = layer g
  /-- Every child of an OR gate lies one layer below it. -/
  layer_orChild {g c : G} : kind g = .or → orChild g c → layer c + 1 = layer g

namespace LayeredSemiUnboundedCircuit

variable {G : Type*}

/-- Alternating normal form with an AND first layer above the leaves: layer `0` consists of
leaves, odd layers consist of AND gates, and positive even layers consist of OR gates. -/
structure InNormalForm (C : LayeredSemiUnboundedCircuit G) : Prop where
  /-- Layer zero consists of leaves. -/
  leaf_of_layer_zero {g : G} : C.layer g = 0 → ∃ b, C.kind g = .leaf b
  /-- Odd layers consist of AND gates. -/
  and_of_odd {g : G} : Odd (C.layer g) → ∃ inp, C.kind g = .and inp
  /-- Positive even layers consist of OR gates. -/
  or_of_pos_even {g : G} : 0 < C.layer g → Even (C.layer g) → C.kind g = .or

namespace InNormalForm

variable {C : LayeredSemiUnboundedCircuit G}

/-- In normal form, every AND gate sits at an odd layer. -/
theorem odd_of_and (h : C.InNormalForm) {g : G} {inp : AndInputs G}
    (hg : C.kind g = .and inp) : Odd (C.layer g) := by
  by_contra hnot
  have heven : Even (C.layer g) := Nat.not_odd_iff_even.mp hnot
  rcases Nat.eq_zero_or_pos (C.layer g) with h0 | hpos
  · obtain ⟨b, hb⟩ := h.leaf_of_layer_zero h0
    rw [hb] at hg
    cases hg
  · have hor := h.or_of_pos_even hpos heven
    rw [hor] at hg
    cases hg

/-- In normal form, every OR gate sits at a positive even layer. -/
theorem pos_even_of_or (h : C.InNormalForm) {g : G} (hg : C.kind g = .or) :
    0 < C.layer g ∧ Even (C.layer g) := by
  have hne : C.layer g ≠ 0 := by
    intro h0
    obtain ⟨b, hb⟩ := h.leaf_of_layer_zero h0
    rw [hb] at hg
    cases hg
  refine ⟨Nat.pos_of_ne_zero hne, ?_⟩
  by_contra hnot
  obtain ⟨inp, hinp⟩ := h.and_of_odd (Nat.not_even_iff_odd.mp hnot)
  rw [hinp] at hg
  cases hg

/-- In normal form, every leaf sits at layer zero. -/
theorem layer_zero_of_leaf (h : C.InNormalForm) {g : G} {b : Bool} (hg : C.kind g = .leaf b) :
    C.layer g = 0 := by
  by_contra hne
  have hpos := Nat.pos_of_ne_zero hne
  rcases Nat.even_or_odd (C.layer g) with heven | hodd
  · have hor := h.or_of_pos_even hpos heven
    rw [hor] at hg
    cases hg
  · obtain ⟨inp, hinp⟩ := h.and_of_odd hodd
    rw [hinp] at hg
    cases hg

/-- In normal form, every child of an OR gate is an AND gate at an odd layer. -/
theorem and_of_orChild (h : C.InNormalForm) {g c : G} (hg : C.kind g = .or)
    (hc : C.orChild g c) : Odd (C.layer c) ∧ ∃ inp, C.kind c = .and inp := by
  obtain ⟨hpos, k, hk⟩ := h.pos_even_of_or hg
  have hlayer := C.layer_orChild hg hc
  have hodd : Odd (C.layer c) := ⟨k - 1, by omega⟩
  exact ⟨hodd, h.and_of_odd hodd⟩

end InNormalForm

/-- The zero-based AND-level of a gate: for an AND gate at layer `2 * k + 1`, this is `k`. -/
@[expose] def andLevel (C : LayeredSemiUnboundedCircuit G) (g : G) : ℕ :=
  C.layer g / 2

/-- Boolean evaluation of a gate in a layered semi-unbounded circuit, defined by recursion on
its layer. -/
def Eval (C : LayeredSemiUnboundedCircuit G) (g : G) : Prop :=
  match _h : C.kind g with
  | .leaf b => b = true
  | .and (.unary c) => C.Eval c
  | .and (.binary l r) => C.Eval l ∧ C.Eval r
  | .or => ∃ c, ∃ _ : C.orChild g c, C.Eval c
termination_by C.layer g
decreasing_by
  all_goals first
    | (have := C.layer_andUnary _h; omega)
    | (have := (C.layer_andBinary _h).1; omega)
    | (have := (C.layer_andBinary _h).2; omega)
    | (have := C.layer_orChild _h ‹_›; omega)

/-- A leaf evaluates to its truth value. -/
theorem eval_leaf (C : LayeredSemiUnboundedCircuit G) {g : G} {b : Bool}
    (h : C.kind g = .leaf b) : C.Eval g ↔ b = true := by
  rw [Eval]
  split <;> simp_all

/-- A fan-in-one AND gate evaluates to the value of its child. -/
theorem eval_andUnary (C : LayeredSemiUnboundedCircuit G) {g c : G}
    (h : C.kind g = .and (.unary c)) : C.Eval g ↔ C.Eval c := by
  rw [Eval]
  split <;> simp_all

/-- A fan-in-two AND gate evaluates to the conjunction of its two children. -/
theorem eval_andBinary (C : LayeredSemiUnboundedCircuit G) {g l r : G}
    (h : C.kind g = .and (.binary l r)) : C.Eval g ↔ C.Eval l ∧ C.Eval r := by
  rw [Eval]
  split <;> simp_all

/-- An OR gate evaluates to `true` iff at least one of its children evaluates to `true`. -/
theorem eval_or (C : LayeredSemiUnboundedCircuit G) {g : G} (h : C.kind g = .or) :
    C.Eval g ↔ ∃ c, C.orChild g c ∧ C.Eval c := by
  rw [Eval]
  split <;> simp_all [exists_prop]

/-- A proof tree witnessing that gate `g` evaluates to `true` in the tree unfolding of `C`:
leaves are true, AND gates keep all children, and OR gates choose a single child. -/
inductive ProofTree (C : LayeredSemiUnboundedCircuit G) : G → Type _ where
  /-- Witness at a true leaf. -/
  | leaf {g : G} (hkind : C.kind g = .leaf true) : ProofTree C g
  /-- Witness at a fan-in-one AND gate. -/
  | andUnary {g c : G} (hkind : C.kind g = .and (.unary c)) (sub : ProofTree C c) :
      ProofTree C g
  /-- Witness at a fan-in-two AND gate. -/
  | andBinary {g l r : G} (hkind : C.kind g = .and (.binary l r))
      (left : ProofTree C l) (right : ProofTree C r) : ProofTree C g
  /-- Witness at an OR gate, keeping one satisfied child. -/
  | orChoice {g c : G} (hkind : C.kind g = .or) (hchild : C.orChild g c)
      (sub : ProofTree C c) : ProofTree C g

/-- A gate evaluates to `true` iff it has a proof tree. -/
theorem eval_iff_nonempty_proofTree (C : LayeredSemiUnboundedCircuit G) (g : G) :
    C.Eval g ↔ Nonempty (ProofTree C g) := by
  constructor
  · intro heval
    suffices h : ∀ n g, C.layer g = n → C.Eval g → Nonempty (ProofTree C g) from h _ g rfl heval
    intro n
    induction n using Nat.strong_induction_on with
    | ind n ih =>
      intro g hn hg
      match hk : C.kind g with
      | .leaf b =>
        have hb : b = true := (C.eval_leaf hk).mp hg
        subst hb
        exact ⟨.leaf hk⟩
      | .and (.unary c) =>
        have hc : C.layer c < n := by have := C.layer_andUnary hk; omega
        obtain ⟨sub⟩ := ih _ hc c rfl ((C.eval_andUnary hk).mp hg)
        exact ⟨.andUnary hk sub⟩
      | .and (.binary l r) =>
        have hlr := C.layer_andBinary hk
        have ⟨hl, hr⟩ := (C.eval_andBinary hk).mp hg
        obtain ⟨tl⟩ := ih _ (by omega) l rfl hl
        obtain ⟨tr⟩ := ih _ (by omega) r rfl hr
        exact ⟨.andBinary hk tl tr⟩
      | .or =>
        obtain ⟨c, hch, hc⟩ := (C.eval_or hk).mp hg
        have hlc : C.layer c < n := by have := C.layer_orChild hk hch; omega
        obtain ⟨sub⟩ := ih _ hlc c rfl hc
        exact ⟨.orChoice hk hch sub⟩
  · rintro ⟨t⟩
    induction t with
    | leaf hkind => exact (C.eval_leaf hkind).mpr rfl
    | andUnary hkind _ ih => exact (C.eval_andUnary hkind).mpr ih
    | andBinary hkind _ _ ihl ihr => exact (C.eval_andBinary hkind).mpr ⟨ihl, ihr⟩
    | orChoice hkind hchild _ ih => exact (C.eval_or hkind).mpr ⟨_, hchild, ih⟩

instance [Finite G] (C : LayeredSemiUnboundedCircuit G) (g : G) : Finite (ProofTree C g) := by
  suffices h : ∀ n g, C.layer g = n → Finite (ProofTree C g) from h _ g rfl
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro g hn
    match hk : C.kind g with
    | .leaf b =>
      refine Finite.of_injective (fun _ : ProofTree C g => ()) fun t₁ t₂ _ => ?_
      cases t₁ with
      | leaf h₁ =>
        cases t₂ with
        | leaf h₂ => rfl
        | andUnary h₂ _ => rw [h₁] at h₂; cases h₂
        | andBinary h₂ _ _ => rw [h₁] at h₂; cases h₂
        | orChoice h₂ _ _ => rw [h₁] at h₂; cases h₂
      | andUnary h₁ _ => rw [hk] at h₁; cases h₁
      | andBinary h₁ _ _ => rw [hk] at h₁; cases h₁
      | orChoice h₁ _ _ => rw [hk] at h₁; cases h₁
    | .and (.unary c) =>
      have hc : Finite (ProofTree C c) := ih _ (by have := C.layer_andUnary hk; omega) c rfl
      let f : ProofTree C g → ProofTree C c
        | .leaf h => by rw [hk] at h; cases h
        | .andUnary h sub => by
          have h' := hk.symm.trans h
          cases h'
          exact sub
        | .andBinary h _ _ => by rw [hk] at h; cases h
        | .orChoice h _ _ => by rw [hk] at h; cases h
      refine Finite.of_injective f fun t₁ t₂ heq => ?_
      cases t₁ with
      | leaf h => rw [hk] at h; cases h
      | andBinary h _ _ => rw [hk] at h; cases h
      | orChoice h _ _ => rw [hk] at h; cases h
      | andUnary h₁ sub₁ =>
        cases t₂ with
        | leaf h => rw [hk] at h; cases h
        | andBinary h _ _ => rw [hk] at h; cases h
        | orChoice h _ _ => rw [hk] at h; cases h
        | andUnary h₂ sub₂ =>
          have hc₁ := hk.symm.trans h₁
          have hc₂ := hk.symm.trans h₂
          cases hc₁
          cases hc₂
          simp only [f] at heq
          subst heq
          rfl
    | .and (.binary l r) =>
      have hlr := C.layer_andBinary hk
      have hl : Finite (ProofTree C l) := ih _ (by omega) l rfl
      have hr : Finite (ProofTree C r) := ih _ (by omega) r rfl
      let f : ProofTree C g → ProofTree C l × ProofTree C r
        | .leaf h => by rw [hk] at h; cases h
        | .andUnary h _ => by rw [hk] at h; cases h
        | .andBinary h tl tr => by
          have h' := hk.symm.trans h
          cases h'
          exact (tl, tr)
        | .orChoice h _ _ => by rw [hk] at h; cases h
      refine Finite.of_injective f fun t₁ t₂ heq => ?_
      cases t₁ with
      | leaf h => rw [hk] at h; cases h
      | andUnary h _ => rw [hk] at h; cases h
      | orChoice h _ _ => rw [hk] at h; cases h
      | andBinary h₁ tl₁ tr₁ =>
        cases t₂ with
        | leaf h => rw [hk] at h; cases h
        | andUnary h _ => rw [hk] at h; cases h
        | orChoice h _ _ => rw [hk] at h; cases h
        | andBinary h₂ tl₂ tr₂ =>
          have h₁' := hk.symm.trans h₁
          have h₂' := hk.symm.trans h₂
          cases h₁'
          cases h₂'
          simp only [f] at heq
          rcases heq with ⟨rfl, rfl⟩
          rfl
    | .or =>
      have hsub : ∀ c : {c : G // C.orChild g c}, Finite (ProofTree C c.1) := fun c =>
        ih _ (by have := C.layer_orChild hk c.2; omega) c.1 rfl
      let f : ProofTree C g → Σ c : {c : G // C.orChild g c}, ProofTree C c.1
        | .leaf h => by rw [hk] at h; cases h
        | .andUnary h _ => by rw [hk] at h; cases h
        | .andBinary h _ _ => by rw [hk] at h; cases h
        | .orChoice _ hch sub => ⟨⟨_, hch⟩, sub⟩
      refine Finite.of_injective f fun t₁ t₂ heq => ?_
      cases t₁ with
      | leaf h => rw [hk] at h; cases h
      | andUnary h _ => rw [hk] at h; cases h
      | andBinary h _ _ => rw [hk] at h; cases h
      | orChoice h₁ hc₁ sub₁ =>
        cases t₂ with
        | leaf h => rw [hk] at h; cases h
        | andUnary h _ => rw [hk] at h; cases h
        | andBinary h _ _ => rw [hk] at h; cases h
        | orChoice h₂ hc₂ sub₂ =>
          simp only [f, Sigma.mk.injEq] at heq
          obtain ⟨hc, hsub⟩ := heq
          have hce : _ = _ := congrArg Subtype.val hc
          subst hce
          cases eq_of_heq hsub
          rfl

namespace ProofTree

variable {C : LayeredSemiUnboundedCircuit G}

/-- The weight of a proof tree under a gate weighting `w`, summing over all gate occurrences
with multiplicity from the tree unfolding. -/
@[expose] def weight (w : G → ℕ) : {g : G} → ProofTree C g → ℕ
  | g, .leaf _ => w g
  | g, .andUnary _ sub => w g + sub.weight w
  | g, .andBinary _ left right => w g + left.weight w + right.weight w
  | g, .orChoice _ _ sub => w g + sub.weight w

/-- The list of AND-gate occurrences in a proof tree, with multiplicity from the tree
unfolding. -/
@[expose] def andNodes : {g : G} → ProofTree C g → List G
  | _, .leaf _ => []
  | g, .andUnary _ sub => g :: sub.andNodes
  | g, .andBinary _ left right => g :: (left.andNodes ++ right.andNodes)
  | _, .orChoice _ _ sub => sub.andNodes

/-- In normal form, every AND-gate occurrence in a proof tree rooted at `g` is an AND gate
whose doubled AND-level lies strictly below `C.layer g`. -/
private theorem andNodes_layer_lt (hnorm : C.InNormalForm) {g : G} (t : ProofTree C g) :
    ∀ x ∈ t.andNodes, (∃ inp, C.kind x = .and inp) ∧ 2 * C.andLevel x < C.layer g := by
  induction t with
  | leaf _ => intro _ hx; cases hx
  | andUnary hkind sub ih =>
    have hlayer := C.layer_andUnary hkind
    have hodd := hnorm.odd_of_and hkind
    intro x hx
    simp only [andNodes, List.mem_cons] at hx
    rcases hx with rfl | hx
    · refine ⟨⟨_, hkind⟩, ?_⟩
      obtain ⟨m, hm⟩ := hodd
      simp only [andLevel, hm]
      omega
    · obtain ⟨hk, hlt⟩ := ih x hx
      exact ⟨hk, by omega⟩
  | andBinary hkind left right ihl ihr =>
    have hlr := C.layer_andBinary hkind
    have hodd := hnorm.odd_of_and hkind
    intro x hx
    simp only [andNodes, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · refine ⟨⟨_, hkind⟩, ?_⟩
      obtain ⟨m, hm⟩ := hodd
      simp only [andLevel, hm]
      omega
    · obtain ⟨hk, hlt⟩ := ihl x hx
      exact ⟨hk, by omega⟩
    · obtain ⟨hk, hlt⟩ := ihr x hx
      exact ⟨hk, by omega⟩
  | orChoice hkind hchild sub ih =>
    have hlayer := C.layer_orChild hkind hchild
    intro x hx
    obtain ⟨hk, hlt⟩ := ih x hx
    exact ⟨hk, by omega⟩

private theorem andNodes_filter_eq_nil_of_le (hnorm : C.InNormalForm) {g : G} (t : ProofTree C g)
    {m : ℕ} (hle : C.layer g ≤ 2 * m) :
    (t.andNodes.filter fun x => decide (C.andLevel x = m)) = [] := by
  rw [List.filter_eq_nil_iff]
  intro x hx
  have hlt := (t.andNodes_layer_lt hnorm x hx).2
  simp only [decide_eq_true_eq]
  omega

/-- In normal form, a proof tree rooted at gate `g` contains at most
`2 ^ ((C.layer g - 1) / 2 - k)` copies of AND gates at each AND-level `k` with
`2 * k < C.layer g`. -/
theorem andNodes_level_profile (hnorm : C.InNormalForm) {g : G} (t : ProofTree C g) :
    ∀ k : ℕ, 2 * k < C.layer g →
      (t.andNodes.filter fun x => decide (C.andLevel x = k)).length ≤
        2 ^ ((C.layer g - 1) / 2 - k) := by
  induction t with
  | leaf hkind =>
    intro k hk
    rw [hnorm.layer_zero_of_leaf hkind] at hk
    omega
  | @orChoice g c hkind hchild sub ih =>
    intro k hk
    have hlayer := C.layer_orChild hkind hchild
    obtain ⟨_, m, hm⟩ := hnorm.pos_even_of_or hkind
    have hk' : 2 * k < C.layer c := by omega
    have hexp : (C.layer g - 1) / 2 = (C.layer c - 1) / 2 := by omega
    simpa only [andNodes, hexp] using ih k hk'
  | @andUnary g c hkind sub ih =>
    intro k hk
    have hlayer := C.layer_andUnary hkind
    obtain ⟨m, hm⟩ := hnorm.odd_of_and hkind
    have hgm : C.andLevel g = m := by simp only [andLevel, hm]; omega
    simp only [andNodes, List.filter_cons]
    by_cases hkm : m = k
    · subst hkm
      have hzero := sub.andNodes_filter_eq_nil_of_le hnorm (by omega : C.layer c ≤ 2 * m)
      rw [hm, show (2 * m + 1 - 1) / 2 - m = 0 by omega, pow_zero]
      simp [hgm, hzero]
    · have hne : decide (C.andLevel g = k) = false := by
        simp only [decide_eq_false_iff_not, hgm]
        exact hkm
      simp only [hne, Bool.false_eq_true, ↓reduceIte]
      have hk' : 2 * k < C.layer c := by omega
      refine (ih k hk').trans ?_
      exact Nat.pow_le_pow_right (by decide) (by omega)
  | @andBinary g l r hkind left right ihl ihr =>
    intro k hk
    have hlr := C.layer_andBinary hkind
    obtain ⟨m, hm⟩ := hnorm.odd_of_and hkind
    have hgm : C.andLevel g = m := by simp only [andLevel, hm]; omega
    simp only [andNodes, List.filter_cons, List.filter_append]
    by_cases hkm : m = k
    · subst hkm
      have hzl := left.andNodes_filter_eq_nil_of_le hnorm (by omega : C.layer l ≤ 2 * m)
      have hzr := right.andNodes_filter_eq_nil_of_le hnorm (by omega : C.layer r ≤ 2 * m)
      rw [hm, show (2 * m + 1 - 1) / 2 - m = 0 by omega, pow_zero]
      simp [hgm, hzl, hzr]
    · have hne : decide (C.andLevel g = k) = false := by
        simp only [decide_eq_false_iff_not, hgm]
        exact hkm
      simp only [hne, Bool.false_eq_true, ↓reduceIte, List.length_append]
      have hkl : 2 * k < C.layer l := by omega
      have hkr : 2 * k < C.layer r := by omega
      have hl := ihl k hkl
      have hr := ihr k hkr
      have hexpl : (C.layer l - 1) / 2 - k = m - 1 - k := by omega
      have hexpr : (C.layer r - 1) / 2 - k = m - 1 - k := by omega
      have hexpg : (C.layer g - 1) / 2 - k = (m - 1 - k) + 1 := by omega
      rw [hexpl] at hl
      rw [hexpr] at hr
      rw [hexpg, pow_succ]
      omega

/-- In normal form, the AND-gate occurrences of a proof tree rooted at an AND gate `u` split as
`u :: rest`, where every node in `rest` sits strictly below `C.andLevel u` and at most
`2 ^ (C.andLevel u - k)` nodes sit at each AND-level `k < C.andLevel u`. -/
theorem andNodes_and_profile (hnorm : C.InNormalForm) {u : G} {inp : AndInputs G}
    (hkind : C.kind u = .and inp) (t : ProofTree C u) :
    ∃ rest : List G, t.andNodes = u :: rest ∧
      (∀ x ∈ rest, C.andLevel x < C.andLevel u) ∧
      ∀ k < C.andLevel u,
        (rest.filter fun x => decide (C.andLevel x = k)).length ≤ 2 ^ (C.andLevel u - k) := by
  obtain ⟨m, hm⟩ := hnorm.odd_of_and hkind
  have hum : C.andLevel u = m := by simp only [andLevel, hm]; omega
  have hprof := t.andNodes_level_profile hnorm
  cases t with
  | leaf h => rw [hkind] at h; cases h
  | orChoice h _ _ => rw [hkind] at h; cases h
  | andUnary h sub =>
    have hlayer := C.layer_andUnary h
    refine ⟨sub.andNodes, rfl, fun x hx => ?_, fun k hk => ?_⟩
    · have hlt := (sub.andNodes_layer_lt hnorm x hx).2
      omega
    · have hk' : 2 * k < C.layer u := by omega
      have hp := hprof k hk'
      simp only [andNodes, List.filter_cons,
        show decide (C.andLevel u = k) = false by simp only [decide_eq_false_iff_not]; omega] at hp
      exact hp.trans (Nat.pow_le_pow_right (by decide) (by omega))
  | andBinary h left right =>
    have hlr := C.layer_andBinary h
    refine ⟨left.andNodes ++ right.andNodes, rfl, fun x hx => ?_, fun k hk => ?_⟩
    · simp only [List.mem_append] at hx
      rcases hx with hx | hx
      · have hlt := (left.andNodes_layer_lt hnorm x hx).2; omega
      · have hlt := (right.andNodes_layer_lt hnorm x hx).2; omega
    · have hk' : 2 * k < C.layer u := by omega
      have hp := hprof k hk'
      simp only [andNodes, List.filter_cons,
        show decide (C.andLevel u = k) = false by simp only [decide_eq_false_iff_not]; omega] at hp
      exact hp.trans (Nat.pow_le_pow_right (by decide) (by omega))

end ProofTree

/-- A gate weighting is min-isolating if every gate evaluating to `true` has a unique
minimum-weight proof tree. -/
@[expose] def IsMinIsolating (C : LayeredSemiUnboundedCircuit G) (w : G → ℕ) : Prop :=
  ∀ g : G, C.Eval g → ∃! t : ProofTree C g, IsMinOn (ProofTree.weight w) Set.univ t

variable {C : LayeredSemiUnboundedCircuit G} (w : G → ℕ)

/-- Minimizing a proof tree of a fan-in-one AND gate is equivalent to minimizing its child's
proof tree. -/
theorem isMinOn_andUnary_iff {g c : G} (hkind : C.kind g = .and (.unary c))
    (t : ProofTree C c) :
    IsMinOn (ProofTree.weight w) Set.univ (.andUnary hkind t) ↔
      IsMinOn (ProofTree.weight w) Set.univ t := by
  rw [isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro h t'
    have := h (.andUnary hkind t')
    simp only [ProofTree.weight] at this
    omega
  · intro h p
    cases p with
    | leaf h' => rw [hkind] at h'; cases h'
    | andBinary h' _ _ => rw [hkind] at h'; cases h'
    | orChoice h' _ _ => rw [hkind] at h'; cases h'
    | andUnary h' t' =>
      have hc := hkind.symm.trans h'
      cases hc
      simp only [ProofTree.weight]
      exact Nat.add_le_add_left (h t') _

/-- Minimizing a proof tree of a fan-in-two AND gate is equivalent to minimizing both children's
proof trees independently. -/
theorem isMinOn_andBinary_iff {g l r : G} (hkind : C.kind g = .and (.binary l r))
    (tl : ProofTree C l) (tr : ProofTree C r) :
    IsMinOn (ProofTree.weight w) Set.univ (.andBinary hkind tl tr) ↔
      IsMinOn (ProofTree.weight w) Set.univ tl ∧ IsMinOn (ProofTree.weight w) Set.univ tr := by
  rw [isMinOn_univ_iff, isMinOn_univ_iff, isMinOn_univ_iff]
  constructor
  · intro h
    refine ⟨fun tl' => ?_, fun tr' => ?_⟩
    · have := h (.andBinary hkind tl' tr)
      simp only [ProofTree.weight] at this
      omega
    · have := h (.andBinary hkind tl tr')
      simp only [ProofTree.weight] at this
      omega
  · rintro ⟨hl, hr⟩ p
    cases p with
    | leaf h' => rw [hkind] at h'; cases h'
    | andUnary h' _ => rw [hkind] at h'; cases h'
    | orChoice h' _ _ => rw [hkind] at h'; cases h'
    | andBinary h' tl' tr' =>
      have hlr := hkind.symm.trans h'
      cases hlr
      simp only [ProofTree.weight]
      exact Nat.add_le_add (Nat.add_le_add_left (hl tl') _) (hr tr')

/-- The chosen child subtree of a minimum-weight proof tree at an OR gate is itself a
minimum-weight proof tree of that child. -/
theorem isMinOn_orChoice_sub {g c : G} (hkind : C.kind g = .or) (hchild : C.orChild g c)
    {t : ProofTree C c}
    (hmin : IsMinOn (ProofTree.weight w) Set.univ (.orChoice hkind hchild t)) :
    IsMinOn (ProofTree.weight w) Set.univ t := by
  rw [isMinOn_univ_iff] at hmin ⊢
  intro t'
  have := hmin (.orChoice hkind hchild t')
  simp only [ProofTree.weight] at this
  omega

/-- If at every OR gate, distinct satisfied children have distinct minimum proof-tree weights,
then the weighting is min-isolating for every gate evaluating to `true`. -/
theorem isMinIsolating_of_separated (C : LayeredSemiUnboundedCircuit G)
    (separated : ∀ g : G, C.kind g = .or →
      ∀ ⦃u v : G⦄, C.orChild g u → C.orChild g v → u ≠ v →
        ∀ ⦃tu : ProofTree C u⦄ ⦃tv : ProofTree C v⦄,
          IsMinOn (ProofTree.weight w) Set.univ tu →
          IsMinOn (ProofTree.weight w) Set.univ tv →
          tu.weight w ≠ tv.weight w) :
    C.IsMinIsolating w := by
  have existsMin (g : G) (hg : C.Eval g) :
      ∃ t : ProofTree C g, IsMinOn (ProofTree.weight w) Set.univ t := by
    obtain ⟨t₀⟩ := (C.eval_iff_nonempty_proofTree g).mp hg
    let _ : Nonempty (ProofTree C g) := ⟨t₀⟩
    exact ⟨Function.argmin (ProofTree.weight w),
      isMinOn_univ_iff.mpr fun q => le_of_not_gt (Function.not_lt_argmin _ q)⟩
  suffices h : ∀ n g, C.layer g = n → C.Eval g →
      ∃! t : ProofTree C g, IsMinOn (ProofTree.weight w) Set.univ t from
    fun g hg => h _ g rfl hg
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro g hn hg
    obtain ⟨p, hp⟩ := existsMin g hg
    refine ⟨p, hp, fun q hq => ?_⟩
    cases p with
    | leaf h₁ =>
      cases q with
      | leaf _ => rfl
      | andUnary h₂ _ => rw [h₁] at h₂; cases h₂
      | andBinary h₂ _ _ => rw [h₁] at h₂; cases h₂
      | orChoice h₂ _ _ => rw [h₁] at h₂; cases h₂
    | @andUnary _ c₁ h₁ sub₁ =>
      cases q with
      | leaf h₂ => rw [h₁] at h₂; cases h₂
      | andBinary h₂ _ _ => rw [h₁] at h₂; cases h₂
      | orChoice h₂ _ _ => rw [h₁] at h₂; cases h₂
      | @andUnary _ c₂ h₂ sub₂ =>
        have hc := h₁.symm.trans h₂
        cases hc
        have hlc : C.layer c₁ < n := by have := C.layer_andUnary h₁; omega
        obtain ⟨_, _, huniq⟩ := ih _ hlc c₁ rfl ((C.eval_andUnary h₁).mp hg)
        have hs₁ := (isMinOn_andUnary_iff w h₁ sub₁).mp hp
        have hs₂ := (isMinOn_andUnary_iff w h₁ sub₂).mp hq
        rw [(huniq _ hs₂).trans (huniq _ hs₁).symm]
    | @andBinary _ l₁ r₁ h₁ tl₁ tr₁ =>
      cases q with
      | leaf h₂ => rw [h₁] at h₂; cases h₂
      | andUnary h₂ _ => rw [h₁] at h₂; cases h₂
      | orChoice h₂ _ _ => rw [h₁] at h₂; cases h₂
      | @andBinary _ l₂ r₂ h₂ tl₂ tr₂ =>
        have hlr := h₁.symm.trans h₂
        cases hlr
        have hlayer := C.layer_andBinary h₁
        have ⟨hevalL, hevalR⟩ := (C.eval_andBinary h₁).mp hg
        obtain ⟨_, _, huniqL⟩ := ih _ (by omega) l₁ rfl hevalL
        obtain ⟨_, _, huniqR⟩ := ih _ (by omega) r₁ rfl hevalR
        obtain ⟨hl₁, hr₁⟩ := (isMinOn_andBinary_iff w h₁ tl₁ tr₁).mp hp
        obtain ⟨hl₂, hr₂⟩ := (isMinOn_andBinary_iff w h₁ tl₂ tr₂).mp hq
        rw [(huniqL _ hl₂).trans (huniqL _ hl₁).symm,
          (huniqR _ hr₂).trans (huniqR _ hr₁).symm]
    | @orChoice _ c₁ h₁ hc₁ sub₁ =>
      cases q with
      | leaf h₂ => rw [h₁] at h₂; cases h₂
      | andUnary h₂ _ => rw [h₁] at h₂; cases h₂
      | andBinary h₂ _ _ => rw [h₁] at h₂; cases h₂
      | @orChoice _ c₂ h₂ hc₂ sub₂ =>
        have hs₁ := isMinOn_orChoice_sub w h₁ hc₁ hp
        have hs₂ := isMinOn_orChoice_sub w h₁ hc₂ hq
        have heqW : sub₁.weight w = sub₂.weight w := by
          have hle₁ := isMinOn_univ_iff.mp hp (.orChoice h₁ hc₂ sub₂)
          have hle₂ := isMinOn_univ_iff.mp hq (.orChoice h₁ hc₁ sub₁)
          simp only [ProofTree.weight] at hle₁ hle₂
          omega
        have hchildEq : c₁ = c₂ := by
          by_contra hne
          exact separated g h₁ hc₁ hc₂ hne hs₁ hs₂ heqW
        subst hchildEq
        have hlc : C.layer c₁ < n := by have := C.layer_orChild h₁ hc₁; omega
        have hevalC : C.Eval c₁ := (C.eval_iff_nonempty_proofTree c₁).mpr ⟨sub₁⟩
        obtain ⟨_, _, huniq⟩ := ih _ hlc c₁ rfl hevalC
        rw [(huniq _ hs₂).trans (huniq _ hs₁).symm]

end LayeredSemiUnboundedCircuit

end Cslib.Circuits.Boolean
