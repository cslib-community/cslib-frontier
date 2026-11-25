/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Matrix.HamiltonianCycle
import Mathlib.Tactic.Ring

/-!
# Sums over two families of bits as Hamiltonian cycle sums

A *grid sum* `∑ x, ∑ r, ∏ n, W n (x (v n)) (r (w n))` over two families of bits, for surjections
`v : N → V` and `w : N → K` of finite types (see `Matrix.exists_permanent_eq_gridSum`), is the
Hamiltonian cycle sum of a matrix of size `40 * |N|` with entries `0`, `1` and single weights, in
every commutative semiring (`Matrix.exists_hamiltonianCycleSum_eq_gridSum`).

The matrix is the weighted adjacency matrix of a graph built from a *row of segments*: the
segments are closed to a cycle, and every segment offers some *options*, each a path from the head
of the segment to the head of the next one. An *exclusive-or gadget* has two tips and a middle
vertex, with edges both ways between each tip and the middle; it joins two options, which run
through it in opposite directions. The Hamiltonian cycles are the selections of one option in
every segment that use every gadget exactly once. For a grid,
there is a segment for every bit of the two families and seven for every incidence, joined by ten
gadgets per incidence, so that the valid selections are exactly the pairs of families of bits.
Padding segments fill up any larger size.

## Main results

* `Matrix.exists_hamiltonianCycleSum_eq_gridSum`: grid sums are Hamiltonian cycle sums.

## References

* [Claude, *VP ≠ VNP over every field*][AnthropicVPVNP2026], Proposition prop:hc-grid
-/


namespace Matrix.HamiltonianCycleGrid

open Finset


open Finset

/-- A vertex of the graph: the head of a segment, or one of the three vertices of a gadget. -/
inductive Vtx (I G : Type*) where
  | head (i : I)
  | tip (g : G) (s : Bool)
  | mid (g : G)
  deriving DecidableEq

namespace Vtx

variable {I G : Type*}

/-- The vertices as a disjoint union. -/
def equivSum : Vtx I G ≃ I ⊕ (G × Bool) ⊕ G where
  toFun
    | head i => .inl i
    | tip g s => .inr (.inl (g, s))
    | mid g => .inr (.inr g)
  invFun
    | .inl i => head i
    | .inr (.inl (g, s)) => tip g s
    | .inr (.inr g) => mid g
  left_inv := by rintro (_ | _ | _) <;> rfl
  right_inv := by rintro (_ | ⟨_, _⟩ | _) <;> rfl

instance [Fintype I] [Fintype G] : Fintype (Vtx I G) := Fintype.ofEquiv _ equivSum.symm

instance [Finite I] [Finite G] : Finite (Vtx I G) := Finite.of_equiv _ equivSum.symm

/-- There is one vertex for every segment and three for every gadget. -/
theorem card_eq [Fintype I] [Fintype G] :
    Fintype.card (Vtx I G) = Fintype.card I + 3 * Fintype.card G := by
  rw [Fintype.card_congr equivSum]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool]
  ring

end Vtx

/-- A row of segments with gadgets: the successor of each segment, and for each gadget and each of
its two sides the option that runs through the gadget on this side. -/
structure Row {I : Type*} (O : I → Type*) (G : Type*) where
  /-- the next segment -/
  next : Equiv.Perm I
  /-- the option through a side of a gadget -/
  port : G × Bool → Σ i, O i

namespace Row

variable {I G : Type*} {O : I → Type*} [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G]
  [∀ i, Fintype (O i)] [∀ i, DecidableEq (O i)] (T : Row O G)

/-- The number of gadgets on an option. -/
def len (o : Σ i, O i) : ℕ := Fintype.card {p // T.port p = o}

/-- The place of a side of a gadget on its option: the gadgets of an option are put in some order.
-/
noncomputable def slot : G × Bool ≃ Σ o, Fin (T.len o) :=
  (Equiv.sigmaFiberEquiv T.port).symm.trans (Equiv.sigmaCongrRight fun _ => Fintype.equivFin _)

omit [Fintype I] [∀ i, Fintype (O i)] [DecidableEq G] in
theorem slot_fst (p : G × Bool) : (T.slot p).1 = T.port p := rfl

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem port_slot_symm (o : Σ i, O i) (j : Fin (T.len o)) : T.port (T.slot.symm ⟨o, j⟩) = o := by
  rw [← T.slot_fst, Equiv.apply_symm_apply]

/-- The entry of the gadget in place j on an option; behind the last gadget, the head of the next
segment. -/
noncomputable def place (o : Σ i, O i) (j : ℕ) : Vtx I G :=
  if h : j < T.len o then Vtx.tip (T.slot.symm ⟨o, j, h⟩).1 (T.slot.symm ⟨o, j, h⟩).2
  else Vtx.head (T.next o.1)

/-- The vertex that follows a side of a gadget on its option. -/
noncomputable def after (p : G × Bool) : Vtx I G := T.place (T.slot p).1 (((T.slot p).2 : ℕ) + 1)

/-- The edges. -/
def Edge : Vtx I G → Vtx I G → Prop
  | .head i, q => ∃ o : O i, q = T.place ⟨i, o⟩ 0
  | .tip g s, q => q = .mid g ∨ q = T.after (g, !s)
  | .mid g, q => ∃ s, q = .tip g s

open Classical in
/-- The weights of the edges: the first edge of an option carries the weight of the option, every
other edge 1. -/
noncomputable def weight {R : Type*} [CommSemiring R] (w : ∀ i, O i → R) : Vtx I G → Vtx I G → R
  | .head i, q => ∑ o : O i with T.place ⟨i, o⟩ 0 = q, w i o
  | p, q => if T.Edge p q then 1 else 0

/-- No two options of one segment avoid all gadgets. -/
def NoParallel : Prop :=
  ∀ i (o o' : O i), (∀ p, T.port p ≠ ⟨i, o⟩) → (∀ p, T.port p ≠ ⟨i, o'⟩) → o = o'

/-- The option at a side of a gadget is selected. -/
def Sel (J : ∀ i, O i) (p : G × Bool) : Prop := J (T.port p).1 = (T.port p).2

/-- A selection uses every gadget exactly once. -/
def Valid (J : ∀ i, O i) : Prop := ∀ g, T.Sel J (g, true) ↔ ¬ T.Sel J (g, false)

open Classical in
/-- The side of a gadget that is used by a selection. -/
noncomputable def side (J : ∀ i, O i) (g : G) : Bool := decide (T.Sel J (g, true))

/-- The successor of a vertex, for a selection and one side for every gadget. -/
noncomputable def route (J : ∀ i, O i) (d : G → Bool) : Vtx I G → Vtx I G
  | .head i => T.place ⟨i, J i⟩ 0
  | .tip g s => if d g = s then .mid g else T.after (g, !s)
  | .mid g => .tip g (!d g)

variable {T}

omit [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] [∀ i, Fintype (O i)]
  [∀ i, DecidableEq (O i)] in
theorem sel_iff {J : ∀ i, O i} (h : T.Valid J) (g : G) (s : Bool) :
    T.Sel J (g, s) ↔ T.side J g = s := by
  have := h g
  unfold side
  cases s <;> simp
  tauto

omit [Fintype I] [DecidableEq I] [Fintype G] [DecidableEq G] [∀ i, Fintype (O i)]
  [∀ i, DecidableEq (O i)] in
theorem sel_eq {J : ∀ i, O i} {p : G × Bool} (h : T.Sel J p) :
    T.port p = ⟨(T.port p).1, J (T.port p).1⟩ :=
  Sigma.ext rfl (heq_of_eq h.symm)

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem sel_slot_symm (J : ∀ i, O i) (i : I) (j : Fin (T.len ⟨i, J i⟩)) :
    T.Sel J (T.slot.symm ⟨⟨i, J i⟩, j⟩) := by
  unfold Sel
  rw [T.port_slot_symm]

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem after_slot_symm (o : Σ i, O i) (j : Fin (T.len o)) :
    T.after (T.slot.symm ⟨o, j⟩) = T.place o ((j : ℕ) + 1) := by
  unfold after
  rw [Equiv.apply_symm_apply]

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem place_len (o : Σ i, O i) : T.place o (T.len o) = .head (T.next o.1) :=
  dite_eq_right (lt_irrefl _)

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- The successor along a selection is always an edge. -/
theorem edge_route (J : ∀ i, O i) (d : G → Bool) (p : Vtx I G) : T.Edge p (T.route J d p) := by
  rcases p with i | ⟨g, s⟩ | g
  · exact ⟨J i, rfl⟩
  · simp only [route]
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr rfl
  · exact ⟨_, rfl⟩

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- The first edges of different options of one segment differ. -/
theorem place_zero_injective (h : T.NoParallel) {i : I} {o o' : O i}
    (e : T.place ⟨i, o⟩ 0 = T.place ⟨i, o'⟩ 0) : o = o' := by
  unfold place at e
  split_ifs at e with h1 h2 h3
  · simp only [Vtx.tip.injEq] at e
    have := congrArg T.port (Prod.ext e.1 e.2)
    rw [T.port_slot_symm, T.port_slot_symm] at this
    exact eq_of_heq (Sigma.mk.inj_iff.1 this).2
  · have hno : ∀ o : Σ i, O i, ¬ 0 < T.len o → ∀ p, T.port p ≠ o := fun o ho p hp =>
      ho (Fintype.card_pos_iff.2 ⟨⟨p, hp⟩⟩)
    exact h i o o' (hno _ h1) (hno _ h3)

/-! ## From a selection to a cycle -/

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- Following a selection that uses every gadget exactly once, one
comes from the head of any segment to every vertex. -/
theorem route_reaches [Finite I] (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i}
    (hJ : T.Valid J) (i₀ : I) (v : Vtx I G) :
    ∃ m, (T.route J (T.side J))^[m] (.head i₀) = v := by
  set f := T.route J (T.side J)
  let Rch : Vtx I G → Prop := fun v => ∃ m, f^[m] (.head i₀) = v
  have hstep : ∀ v, Rch v → Rch (f v) := by
    rintro v ⟨m, rfl⟩
    exact ⟨m + 1, Function.iterate_succ_apply' f m _⟩
  have hchain : ∀ i, Rch (.head i) → ∀ j ≤ T.len ⟨i, J i⟩, Rch (T.place ⟨i, J i⟩ j) := by
    intro i hi j
    induction j with
    | zero => exact fun _ => hstep _ hi
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      rw [place, dite_eq_left (show j < _ by omega)] at h
      generalize hp : T.slot.symm ⟨⟨i, J i⟩, ⟨j, by omega⟩⟩ = p at h
      have hs : T.side J p.1 = p.2 := (sel_iff hJ p.1 p.2).1 (hp ▸ sel_slot_symm J i _)
      have h3 := hstep _ (hstep _ (hstep _ h))
      have e : f (f (f (.tip p.1 p.2))) = T.after p := by
        simp only [f, route, hs, ite_true, Bool.not_not]
        rw [ite_eq_right (by cases p.2 <;> simp)]
      rw [e, ← hp, after_slot_symm] at h3
      exact h3
  have hheads : ∀ i, Rch (.head i) := by
    intro i
    obtain ⟨m, hm⟩ := (hnext.2 (Set.mem_univ i₀) (Set.mem_univ i)).exists_nat_pow_eq
    rw [← hm]
    clear hm
    induction m with
    | zero => exact ⟨0, rfl⟩
    | succ m ih =>
      have h := hchain _ ih _ le_rfl
      rw [place_len] at h
      rwa [pow_succ', Equiv.Perm.mul_apply]
  have hgad : ∀ g, Rch (.tip g (T.side J g)) ∧ Rch (.mid g) ∧ Rch (.tip g (!T.side J g)) := by
    intro g
    have hsel : T.Sel J (g, T.side J g) := (sel_iff hJ g _).2 rfl
    obtain ⟨⟨o, j⟩, e⟩ : ∃ q, T.slot.symm q = (g, T.side J g) := T.slot.symm.surjective _
    have ho : o = ⟨o.1, J o.1⟩ := by
      have h1 : T.port (g, T.side J g) = o := by rw [← e, T.port_slot_symm]
      exact h1 ▸ sel_eq hsel
    have h := hchain o.1 (hheads o.1) (j : ℕ) (by rw [← ho]; exact j.2.le)
    rw [← ho, place, dite_eq_left j.2, Fin.eta, e] at h
    have h2 := hstep _ h
    have e1 : f (.tip g (T.side J g)) = .mid g := by simp [f, route]
    rw [e1] at h2
    exact ⟨h, h2, hstep _ h2⟩
  rcases v with i | ⟨g, s⟩ | g
  · exact hheads i
  · by_cases hs : s = T.side J g
    · exact hs ▸ (hgad g).1
    · exact Bool.eq_not_of_ne hs ▸ (hgad g).2.2
  · exact (hgad g).2.1

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- Following such a selection is a permutation of the vertices. -/
theorem route_bijective [Finite I] (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i}
    (hJ : T.Valid J) :
    Function.Bijective (T.route J (T.side J)) := by
  refine Finite.surjective_iff_bijective.1 fun v => ?_
  rcases v with i | ⟨g, s⟩ | g
  · -- the head is the end of the option selected in the segment before it
    set i' := T.next.symm i with hi'
    by_cases h : T.len ⟨i', J i'⟩ = 0
    · refine ⟨.head i', ?_⟩
      change T.place ⟨i', J i'⟩ 0 = _
      rw [show (0 : ℕ) = T.len ⟨i', J i'⟩ from h.symm, place_len]
      simp [hi']
    · let j : Fin (T.len ⟨i', J i'⟩) := ⟨T.len ⟨i', J i'⟩ - 1, by omega⟩
      generalize hp : T.slot.symm ⟨⟨i', J i'⟩, j⟩ = p
      have hs : T.side J p.1 = p.2 := (sel_iff hJ p.1 p.2).1 (hp ▸ sel_slot_symm J i' j)
      refine ⟨.tip p.1 (!p.2), ?_⟩
      simp only [route, hs, Bool.not_not]
      rw [ite_eq_right (by cases p.2 <;> simp), ← hp, after_slot_symm,
        show (j : ℕ) + 1 = T.len ⟨i', J i'⟩ by
        simp only [j]; omega, place_len]
      simp [hi']
  all_goals
    obtain ⟨i₀, -⟩ := T.port (g, true)
  · obtain ⟨_ | m, hm⟩ := route_reaches hnext hJ i₀ (.tip g s)
    · cases hm
    · exact ⟨_, (Function.iterate_succ_apply' _ m _).symm.trans hm⟩
  · obtain ⟨_ | m, hm⟩ := route_reaches hnext hJ i₀ (.mid g)
    · cases hm
    · exact ⟨_, (Function.iterate_succ_apply' _ m _).symm.trans hm⟩

/-- The cycle of a selection. -/
noncomputable def routePerm (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i} (hJ : T.Valid J) :
    Equiv.Perm (Vtx I G) :=
  Equiv.ofBijective _ (route_bijective hnext hJ)

omit [DecidableEq G] [∀ i, Fintype (O i)] in
/-- It is one cycle through all vertices. -/
theorem routePerm_isCycleOn (hnext : T.next.IsCycleOn Set.univ) {J : ∀ i, O i} (hJ : T.Valid J) :
    (routePerm hnext hJ).IsCycleOn Set.univ := by
  refine ⟨Set.bijOn_univ.2 (Equiv.bijective _), ?_⟩
  intro u _ v _
  obtain ⟨i₀⟩ : Nonempty I := by
    rcases u with i | ⟨g, _⟩ | g
    exacts [⟨i⟩, ⟨(T.port (g, true)).1⟩, ⟨(T.port (g, true)).1⟩]
  have key : ∀ v, (routePerm hnext hJ).SameCycle (.head i₀) v := by
    intro v
    obtain ⟨m, hm⟩ := route_reaches hnext hJ i₀ v
    exact ⟨m, by rwa [zpow_natCast, Equiv.Perm.coe_pow]⟩
  exact (key u).symm.trans (key v)

/-! ## From a cycle to a selection -/

variable {σ : Equiv.Perm (Vtx I G)}

/-- In one cycle through all vertices, no two vertices are a cycle of their own if there is a third
one. -/
theorem not_two_cycle {A : Type*} [Finite A] {τ : Equiv.Perm A} (hτ : τ.IsCycleOn Set.univ)
    {a b c : A}
    (hca : c ≠ a) (hcb : c ≠ b) (h : τ a = b) : τ b ≠ a := by
  intro h'
  obtain ⟨m, hm⟩ := (hτ.2 (Set.mem_univ a) (Set.mem_univ c)).exists_nat_pow_eq
  have : (τ ^ m) a = a ∨ (τ ^ m) a = b := by
    clear hm
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', Equiv.Perm.mul_apply]
      rcases ih with e | e <;> rw [e] <;> [exact Or.inr h; exact Or.inl h']
  rw [hm] at this
  exact this.elim hca hcb

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
theorem place_ne_mid (o : Σ i, O i) (j : ℕ) (g : G) : T.place o j ≠ .mid g := by
  unfold place
  split_ifs <;> simp

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- A cycle through all vertices runs through every gadget in one of two
ways: from one tip over the middle to the other tip, and then on along the option of that side. -/
theorem exists_traverse [Finite I] (hσ : σ.IsCycleOn Set.univ) (he : ∀ p, T.Edge p (σ p)) (g : G) :
    ∃ s, σ (.tip g s) = .mid g ∧ σ (.mid g) = .tip g (!s) ∧ σ (.tip g (!s)) = T.after (g, s) := by
  obtain ⟨t, ht⟩ := he (.mid g)
  refine ⟨!t, ?_⟩
  rw [Bool.not_not]
  have h2 : σ (.tip g t) ≠ .mid g :=
    not_two_cycle hσ (c := .tip g (!t)) (by simp) (by simp) ht
  have h3 : σ (.tip g (!t)) = .mid g := by
    obtain ⟨v, hv⟩ := σ.surjective (.mid g)
    have hev := he v
    rw [hv] at hev
    rcases v with i | ⟨g', s⟩ | g'
    · obtain ⟨o, ho⟩ := hev
      exact absurd ho.symm (place_ne_mid _ _ _)
    · rcases hev with e | e
      · obtain rfl : g = g' := Vtx.mid.inj e
        have : s = !t := by
          revert h2 hv
          cases s <;> cases t <;> simp +contextual
        exact this ▸ hv
      · exact absurd e.symm (place_ne_mid _ _ _)
    · obtain ⟨s, e⟩ := hev
      cases e
  exact ⟨h3, ht, (he (.tip g t)).resolve_left h2⟩

omit [Fintype I] [DecidableEq G] [∀ i, Fintype (O i)] in
/-- In a cycle through all vertices every option that is entered at the head of its segment is
followed to its end, and every gadget lies on exactly one of these options. So the cycle is the one
of a selection that uses every gadget exactly once. -/
theorem exists_selection [Finite I] (hσ : σ.IsCycleOn Set.univ) (he : ∀ p, T.Edge p (σ p)) :
    ∃ J, T.Valid J ∧ ∀ p, σ p = T.route J (T.side J) p := by
  choose J hJ using fun i => (he (.head i) : ∃ o : O i, _)
  choose d hd using exists_traverse hσ he
  have hrouteD : ∀ p, σ p = T.route J d p := by
    rintro (i | ⟨g, s⟩ | g)
    · exact hJ i
    · simp only [route]
      split_ifs with h
      · exact h ▸ (hd g).1
      · rw [Bool.eq_not_of_ne (Ne.symm h), Bool.not_not]
        exact (hd g).2.2
    · exact (hd g).2.1
  have hactive : ∀ g s v, σ v = .tip g s → v ≠ .mid g → d g = s := by
    intro g s v hv hne
    by_contra hs
    exact hne (σ.injective (hv.trans (Bool.eq_not_of_ne (Ne.symm hs) ▸ (hd g).2.1).symm))
  have hchosen : ∀ i (j : ℕ) (hj : j < T.len ⟨i, J i⟩),
      d (T.slot.symm ⟨⟨i, J i⟩, j, hj⟩).1 = (T.slot.symm ⟨⟨i, J i⟩, j, hj⟩).2 := by
    intro i j
    induction j with
    | zero =>
      intro hj
      refine hactive _ _ (.head i) ?_ (by simp)
      rw [hJ i, place, dite_eq_left hj]
    | succ j ih =>
      intro hj
      have h := ih (by omega)
      generalize hp : T.slot.symm ⟨⟨i, J i⟩, j, by omega⟩ = p at h
      refine hactive _ _ (.tip p.1 (!p.2)) ?_ (by simp)
      rw [hrouteD, route, ite_eq_right (by rw [h]; cases p.2 <;> simp), Bool.not_not, ← hp,
        after_slot_symm, place,
        dite_eq_left hj]
  have hsel : ∀ p, T.Sel J p → d p.1 = p.2 := by
    intro p hp
    obtain ⟨⟨o, j⟩, rfl⟩ := T.slot.symm.surjective p
    have ho := sel_eq hp
    rw [T.port_slot_symm] at ho
    obtain ⟨i, a⟩ := o
    obtain rfl : a = J i := eq_of_heq (Sigma.mk.inj_iff.1 ho).2
    exact hchosen i j j.2
  have hall : ∀ g, T.Sel J (g, d g) := by
    intro g
    let A : Vtx I G → Prop
      | .head _ => True
      | .tip g _ => T.Sel J (g, d g)
      | .mid g => T.Sel J (g, d g)
    have hplace : ∀ i j, A (T.place ⟨i, J i⟩ j) := by
      intro i j
      unfold place
      split_ifs with h
      · simp only [A]
        rw [hchosen i j h]
        exact sel_slot_symm J i _
      · trivial
    have hstep : ∀ v, A v → A (σ v) := by
      rintro (i | ⟨g', s⟩ | g') hv
      · rw [hJ i]
        exact hplace i 0
      · rw [hrouteD, route]
        split_ifs with h
        · exact hv
        · have : (!s) = d g' := by revert h; cases s <;> cases d g' <;> simp
          have hs : (T.slot (g', !s)).1 = ⟨(T.port (g', !s)).1, J (T.port (g', !s)).1⟩ :=
            (T.slot_fst _).trans (sel_eq (this ▸ hv))
          unfold after
          generalize ((T.slot (g', !s)).2 : ℕ) + 1 = j
          rw [hs]
          exact hplace _ _
      · rw [(hd g').2.1]
        exact hv
    obtain ⟨m, hm⟩ :=
      (hσ.2 (Set.mem_univ (Vtx.head (T.port (g, true)).1))
        (Set.mem_univ (Vtx.mid g))).exists_nat_pow_eq
    have : ∀ m : ℕ, A ((σ ^ m) (.head (T.port (g, true)).1)) := by
      intro m
      induction m with
      | zero => trivial
      | succ m ih => rw [pow_succ', Equiv.Perm.mul_apply]; exact hstep _ ih
    exact (hm ▸ this m : A (.mid g))
  have hiff : ∀ g s, T.Sel J (g, s) ↔ d g = s := fun g s => ⟨hsel (g, s), fun h => h ▸ hall g⟩
  have hv : T.Valid J := fun g => by rw [hiff, hiff]; cases d g <;> simp
  refine ⟨J, hv, fun p => ?_⟩
  rw [hrouteD, show T.side J = d from funext fun g => (sel_iff hv g _).1 (hall g)]

/-! ## The sum -/

/-- The sum over the cycles through all vertices of the products of the edge weights is the sum over
the selections that use every gadget exactly once of the products of the weights of the selected
options, provided that no two options of one segment avoid all gadgets. -/
theorem hamiltonianCycleSum_weight {R : Type*} [CommSemiring R] (hnext : T.next.IsCycleOn Set.univ)
    (hpar : T.NoParallel)
    (w : ∀ i, O i → R) [DecidablePred T.Valid] :
    hamiltonianCycleSum (T.weight w) = ∑ J : ∀ i, O i with T.Valid J, ∏ i, w i (J i) := by
  classical
  unfold hamiltonianCycleSum
  rw [← Finset.sum_filter_of_ne (p := fun σ : Equiv.Perm (Vtx I G) => ∀ p, T.Edge p (σ p))]
  swap
  · intro σ _ hne p
    by_contra hp
    refine hne (Finset.prod_eq_zero (mem_univ p) ?_)
    rcases p with i | ⟨g, s⟩ | g
    · simp only [weight]
      refine Finset.sum_eq_zero fun o ho => absurd ⟨o, ?_⟩ hp
      exact (mem_filter.1 ho).2.symm
    all_goals exact ite_eq_right hp
  rw [Finset.filter_filter]
  symm
  refine Finset.sum_bij (fun J hJ => routePerm hnext (mem_filter.1 hJ).2) ?_ ?_ ?_ ?_
  · intro J hJ
    exact mem_filter.2 ⟨mem_univ _, routePerm_isCycleOn _ _, fun p => edge_route J _ p⟩
  · intro J hJ J' hJ' e
    funext i
    exact place_zero_injective hpar (DFunLike.congr_fun e (Vtx.head i))
  · intro σ hσ
    obtain ⟨-, hc, he⟩ := mem_filter.1 hσ
    obtain ⟨J, hv, hp⟩ := exists_selection hc he
    exact ⟨J, mem_filter.2 ⟨mem_univ _, hv⟩, Equiv.ext fun p => (hp p).symm⟩
  · intro J hJ
    have hv := (mem_filter.1 hJ).2
    rw [← Vtx.equivSum.symm.prod_comp, Fintype.prod_sum_type]
    have h1 : ∀ i, T.weight w (.head i) (routePerm hnext hv (.head i)) = w i (J i) := by
      intro i
      simp only [weight]
      refine Finset.sum_eq_single_of_mem (J i) (mem_filter.2 ⟨mem_univ _, rfl⟩) fun o ho hne => ?_
      exact absurd (place_zero_injective hpar (mem_filter.1 ho).2) hne
    have h2 : ∀ p : (G × Bool) ⊕ G, T.weight w (Vtx.equivSum.symm (.inr p))
        (routePerm hnext hv (Vtx.equivSum.symm (.inr p))) = 1 := by
      rintro (⟨g, s⟩ | g) <;> exact ite_eq_left (edge_route J _ _)
    rw [Finset.prod_congr rfl fun p _ => h2 p, Finset.prod_const_one, mul_one]
    exact Finset.prod_congr rfl fun i _ => (h1 i).symm

end Row



/-- The segments of a grid: one for every bit of the two families; for every incidence the one that
chooses the weight, one for each of the two sides and one for each of the four pairs of bits; and
some for padding. -/
inductive Seg (N V K P : Type) where
  | var (a : V)
  | row (b : K)
  | edge (n : N)
  | left (n : N)
  | right (n : N)
  | tab (n : N) (t : Bool × Bool)
  | pad (p : P)
  deriving DecidableEq

variable {N V K P : Type}

/-- The segments as a disjoint union. -/
def Seg.equivSum : Seg N V K P ≃ V ⊕ K ⊕ N ⊕ N ⊕ N ⊕ (N × Bool × Bool) ⊕ P where
  toFun
    | .var a => .inl a
    | .row b => .inr (.inl b)
    | .edge n => .inr (.inr (.inl n))
    | .left n => .inr (.inr (.inr (.inl n)))
    | .right n => .inr (.inr (.inr (.inr (.inl n))))
    | .tab n t => .inr (.inr (.inr (.inr (.inr (.inl (n, t))))))
    | .pad p => .inr (.inr (.inr (.inr (.inr (.inr p)))))
  invFun
    | .inl a => .var a
    | .inr (.inl b) => .row b
    | .inr (.inr (.inl n)) => .edge n
    | .inr (.inr (.inr (.inl n))) => .left n
    | .inr (.inr (.inr (.inr (.inl n)))) => .right n
    | .inr (.inr (.inr (.inr (.inr (.inl (n, t)))))) => .tab n t
    | .inr (.inr (.inr (.inr (.inr (.inr p))))) => .pad p
  left_inv := by rintro (_ | _ | _ | _ | _ | _ | _) <;> rfl
  right_inv := by rintro (_ | _ | _ | _ | _ | _ | _) <;> rfl

instance [Fintype N] [Fintype V] [Fintype K] [Fintype P] : Fintype (Seg N V K P) :=
  Fintype.ofEquiv _ Seg.equivSum.symm

/-- The options of a segment. -/
abbrev Opt : Seg N V K P → Type
  | .var _ => Bool
  | .row _ => Bool
  | .edge _ => Bool × Bool
  | .left _ => Option Bool
  | .right _ => Option Bool
  | .tab _ _ => Bool
  | .pad _ => Unit

instance (i : Seg N V K P) : Fintype (Opt i) := by cases i <;> infer_instance

instance (i : Seg N V K P) : DecidableEq (Opt i) := by cases i <;> infer_instance

/-- The ten gadgets of an incidence. -/
abbrev Gad (N : Type) : Type := N × ((Bool × Bool) ⊕ Option Bool ⊕ Option Bool)

/-- The two options of every gadget. -/
def gridPort (v : N → V) (w : N → K) : Gad N × Bool → Σ i : Seg N V K P, Opt i
  | ((n, .inl t), true) => ⟨.edge n, t⟩
  | ((n, .inl t), false) => ⟨.tab n t, false⟩
  | ((n, .inr (.inl o)), true) => ⟨.left n, o⟩
  | ((n, .inr (.inl (some b))), false) => ⟨.tab n (true, b), false⟩
  | ((n, .inr (.inl none)), false) => ⟨.var (v n), true⟩
  | ((n, .inr (.inr o)), true) => ⟨.right n, o⟩
  | ((n, .inr (.inr (some b))), false) => ⟨.tab n (b, true), false⟩
  | ((n, .inr (.inr none)), false) => ⟨.row (w n), true⟩

/-- The row of segments of a grid. -/
def gridRow (v : N → V) (w : N → K) (next : Equiv.Perm (Seg N V K P)) :
    Row (Opt (N := N) (V := V) (K := K) (P := P)) (Gad N) where
  next := next
  port := gridPort v w

/-- The selection that belongs to two families of bits. -/
def choice (v : N → V) (w : N → K) (x : V → Bool) (r : K → Bool) : ∀ i : Seg N V K P, Opt i
  | .var a => x a
  | .row b => r b
  | .edge n => (x (v n), r (w n))
  | .left n => if x (v n) then some (r (w n)) else none
  | .right n => if r (w n) then some (x (v n)) else none
  | .tab n t => decide (t = (x (v n), r (w n)))
  | .pad _ => ()

/-- The weights of the options: only the choices at the incidences carry one. -/
def gridWeight {R : Type*} [One R] (W : N → Bool → Bool → R) : ∀ i : Seg N V K P, Opt i → R
  | .edge n, t => W n t.1 t.2
  | _, _ => 1

variable {v : N → V} {w : N → K} {next : Equiv.Perm (Seg N V K P)}

/-- The three kinds of gadgets at one incidence. -/
theorem choice_cases :
    (∀ (t : Bool × Bool) (a c : Bool), (a, c) = t ↔ ¬decide (t = (a, c)) = false) ∧
    (∀ a c : Bool, (if a then some c else none) = none ↔ ¬a = true) ∧
    (∀ a c b : Bool, (if a then some c else none) = some b ↔ ¬decide ((true, b) = (a, c)) = false) ∧
    ∀ a c b : Bool,
      (if a then some c else none) = some b ↔ ¬decide ((b, true) = (c, a)) = false := by
  decide

/-- The selection of two families of bits uses every gadget exactly once. -/
theorem valid_choice (x : V → Bool) (r : K → Bool) : (gridRow v w next).Valid (choice v w x r) := by
  obtain ⟨h1, h2, h3, h4⟩ := choice_cases
  rintro ⟨n, t | (_ | b) | (_ | b)⟩
  exacts [h1 t _ _, h2 _ _, h3 _ _ b, h2 _ _, h4 _ _ b]

/-- The pair chosen at an incidence is the pair of the bits of its two ends. -/
theorem incidence_cases : ∀ (e : Bool × Bool) (l h : Option Bool) (a c : Bool),
    (∀ b, l = some b ↔ e = (true, b)) → (l = none ↔ a = false) →
    (∀ b, h = some b ↔ e = (b, true)) → (h = none ↔ c = false) →
      e = (a, c) ∧ l = (if a then some c else none) ∧ h = (if c then some a else none) := by
  decide

/-- The selections that use every gadget exactly once are those of the
pairs of families of bits. -/
theorem eq_choice_of_valid {J : ∀ i : Seg N V K P, Opt i} (h : (gridRow v w next).Valid J) :
    J = choice v w (fun a => J (.var a)) (fun b => J (.row b)) := by
  have key : ∀ n, J (.edge n) = (J (.var (v n)), J (.row (w n))) ∧
      J (.left n) = (if J (.var (v n)) then some (J (.row (w n))) else none) ∧
      J (.right n) = (if J (.row (w n)) then some (J (.var (v n))) else none) ∧
      ∀ t, J (.tab n t) = decide (t = J (.edge n)) := by
    intro n
    have ht : ∀ t, J (.edge n) = t ↔ ¬ J (.tab n t) = false := fun t => h (n, .inl t)
    have hl : ∀ b, J (.left n) = some b ↔ ¬ J (.tab n (true, b)) = false :=
      fun b => h (n, .inr (.inl (some b)))
    have hr : ∀ b, J (.right n) = some b ↔ ¬ J (.tab n (b, true)) = false :=
      fun b => h (n, .inr (.inr (some b)))
    have hl0 : J (.left n) = none ↔ ¬ J (.var (v n)) = true := h (n, .inr (.inl none))
    have hr0 : J (.right n) = none ↔ ¬ J (.row (w n)) = true := h (n, .inr (.inr none))
    obtain ⟨he, h1, h2⟩ := incidence_cases _ _ _ _ _ (fun b => (hl b).trans (ht _).symm)
      (hl0.trans Bool.eq_false_iff.symm) (fun b => (hr b).trans (ht _).symm)
      (hr0.trans Bool.eq_false_iff.symm)
    refine ⟨he, h1, h2, fun t => ?_⟩
    rw [Bool.eq_iff_iff, decide_eq_true_iff, eq_comm (a := t), ht t, Bool.not_eq_false]
  funext i
  rcases i with a | b | n | n | n | ⟨n, t⟩ | p
  · rfl
  · rfl
  · exact (key n).1
  · exact (key n).2.1
  · exact (key n).2.2.1
  · exact ((key n).2.2.2 t).trans (by rw [(key n).1]; rfl)
  · rfl

/-- Every option of a grid, except at most one in its segment, runs through a gadget. -/
theorem gridRow_noParallel (hv : Function.Surjective v) (hw : Function.Surjective w) :
    (gridRow v w next).NoParallel := by
  intro i o o' h h'
  rcases i with a | b | n | n | n | ⟨n, t⟩ | p
  · obtain ⟨n, rfl⟩ := hv a
    cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inr (.inl none)), false)) |
      exact absurd rfl (h' ((n, .inr (.inl none)), false))
  · obtain ⟨n, rfl⟩ := hw b
    cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inr (.inr none)), false)) |
      exact absurd rfl (h' ((n, .inr (.inr none)), false))
  · exact absurd rfl (h ((n, .inl o), true))
  · exact absurd rfl (h ((n, .inr (.inl o)), true))
  · exact absurd rfl (h ((n, .inr (.inr o)), true))
  · cases o <;> cases o' <;> first | rfl | exact absurd rfl (h ((n, .inl t), false)) |
      exact absurd rfl (h' ((n, .inl t), false))
  · rfl

variable [Fintype N] [DecidableEq N] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
  [Fintype P] [DecidableEq P]

/-- Over every commutative semiring, a sum over two families of bits of products of weights, one for
every incidence, is the sum over the cycles through all vertices of the grid graph. -/
theorem hamiltonianCycleSum_grid {R : Type*} [CommSemiring R] (hv : Function.Surjective v)
    (hw : Function.Surjective w)
    (hnext : next.IsCycleOn Set.univ) (W : N → Bool → Bool → R) :
    hamiltonianCycleSum ((gridRow v w next).weight (gridWeight W)) =
      ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  rw [Row.hamiltonianCycleSum_weight (T := gridRow v w next) hnext (gridRow_noParallel hv hw),
    ← Fintype.sum_prod_type']
  symm
  refine Finset.sum_bij' (fun p _ => choice v w p.1 p.2)
    (fun J _ => (fun a => J (.var a), fun b => J (.row b)))
    (fun p _ => mem_filter.2 ⟨mem_univ _, valid_choice _ _⟩) (fun _ _ => mem_univ _)
    (fun _ _ => rfl)
    (fun J hJ => (eq_choice_of_valid (mem_filter.1 hJ).2).symm) fun p _ => ?_
  refine Fintype.prod_of_injective Seg.edge (fun a b h => Seg.edge.inj h) _ _ (fun i hi => ?_)
    fun n => rfl
  rcases i with _ | _ | n | _ | _ | _ | _ <;> first | rfl | exact absurd ⟨n, rfl⟩ hi

omit [DecidableEq N] [DecidableEq V] [DecidableEq K] [DecidableEq P] in
/-- The number of vertices of a grid. -/
theorem card_gridVtx :
    Fintype.card (Vtx (Seg N V K P) (Gad N)) =
      Fintype.card V + Fintype.card K + 37 * Fintype.card N + Fintype.card P := by
  rw [Vtx.card_eq, Fintype.card_congr (Seg.equivSum (N := N) (V := V) (K := K) (P := P))]
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Fintype.card_option]
  ring


end Matrix.HamiltonianCycleGrid

namespace Matrix

open Finset HamiltonianCycleGrid

/-- **Grid sums are Hamiltonian cycle sums** [Claude, *VP ≠ VNP over every
field*][AnthropicVPVNP2026], Proposition prop:hc-grid. In every commutative semiring, for
surjections `v : N → V` and `w : N → K` of finite types and weights `W n x r`, the grid sum `∑ x, ∑
r, ∏ n, W n (x (v n)) (r (w n))` is the Hamiltonian cycle sum of an `S × S` matrix, for every `S ≥
40 * |N|`, whose entries are `0`, `1` and single values `W n x r`. -/
public theorem exists_hamiltonianCycleSum_eq_gridSum {R : Type*} [CommSemiring R] {N V K : Type}
    [Fintype N] [Fintype V] [DecidableEq V] [Fintype K] [DecidableEq K]
    (v : N → V) (w : N → K) (hv : Function.Surjective v) (hw : Function.Surjective w)
    (W : N → Bool → Bool → R) {S : ℕ} (hS : 40 * Fintype.card N ≤ S) :
    ∃ M : Matrix (Fin S) (Fin S) R, (∀ i j, M i j = 0 ∨ M i j = 1 ∨ ∃ n x r, M i j = W n x r) ∧
      M.hamiltonianCycleSum = ∑ x : V → Bool, ∑ r : K → Bool, ∏ n, W n (x (v n)) (r (w n)) := by
  classical
  have hV := Fintype.card_le_of_surjective v hv
  have hK := Fintype.card_le_of_surjective w hw
  let P := Fin (S - (Fintype.card V + Fintype.card K + 37 * Fintype.card N))
  obtain ⟨next, hnext, -⟩ := Finset.exists_cycleOn (Finset.univ : Finset (Seg N V K P))
  rw [Finset.coe_univ] at hnext
  have hcard : Fintype.card (Vtx (Seg N V K P) (Gad N)) = Fintype.card (Fin S) := by
    rw [card_gridVtx, Fintype.card_fin, Fintype.card_fin]
    omega
  let e := Fintype.equivOfCardEq hcard
  let T := gridRow v w next
  refine ⟨(Matrix.of (T.weight (gridWeight W))).submatrix e.symm e.symm, fun i j => ?_,
    (hamiltonianCycleSum_submatrix_equiv e.symm _).trans (hamiltonianCycleSum_grid hv hw hnext W)⟩
  simp only [submatrix_apply, of_apply]
  generalize e.symm i = a, e.symm j = b
  rcases a with s | ⟨g, side⟩ | g
  · simp only [Row.weight]
    by_cases hex : ∃ o : Opt s, T.place ⟨s, o⟩ 0 = b
    · obtain ⟨o, ho⟩ := hex
      rw [Finset.sum_eq_single_of_mem o (mem_filter.2 ⟨mem_univ o, ho⟩) fun o' ho' hne =>
        absurd (Row.place_zero_injective (gridRow_noParallel hv hw)
          ((mem_filter.1 ho').2.trans ho.symm)) hne]
      cases s with
      | edge n => exact Or.inr (Or.inr ⟨n, o.1, o.2, rfl⟩)
      | _ => exact Or.inr (Or.inl rfl)
    · exact Or.inl (Finset.sum_eq_zero fun o ho => absurd ⟨o, (mem_filter.1 ho).2⟩ hex)
  all_goals
    simp only [Row.weight]
    split_ifs
    exacts [Or.inr (Or.inl rfl), Or.inl rfl]




end Matrix
