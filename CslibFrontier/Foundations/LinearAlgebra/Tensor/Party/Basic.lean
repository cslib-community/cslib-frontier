/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Order.Basic
public import Mathlib.Tactic.GCongr.Core
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring

/-!
# Tensors over a finite set of parties, restrictions and covers

A tensor over a finite set `I` of *parties* with entries in `K` (`Cslib.PartyTensor K I`) has,
for each party `p`, a finite index set `Index p` (the leg of `p`), and an entry for each choice
of one index per party. The order-three tensors of bilinear complexity (`Cslib.Tensor`) have
three parties and index types fixed in their type; here there may be any finite set of parties,
and the index sets are part of the tensor.

Following Strassen, `s` is a *restriction* of `t`, written `s ≤ t`, when `s` arises from `t`
by one linear map on each leg: `s x = ∑ y, (∏ p, L p (x p) (y p)) * t y`. Restriction is a preorder
(`PartyTensor.instPreorder`) and is compatible with the product, party by party
(`MulLeftMono`, `MulRightMono`), so `mul_le_mul'` and `gcongr` apply to it. `s` is *covered*
by a finite family `b` (`PartyTensor.CoveredBy`) when `s` is a sum of restrictions of the
members of `b`, one of each (a restriction may be `0`).

The constructions are the product `s * t` (Kronecker product, party by party) and its unit `1`,
the product `prod b` of a finite family, the powers `t ^ k`, the *push-forward* `push π t`,
which gives the leg `j` of a tensor over `J` to the party `π j`, the unit tensor `unit K J r`
of size `r` and the wire `wire K n p q` of dimension `n` between two parties.

## Main definitions

* `Cslib.PartyTensor`: tensors over a finite set of parties.
* `Cslib.PartyTensor.localApply`: one linear map on each leg, applied to an array.
* `Cslib.PartyTensor.prod`, `Cslib.PartyTensor.push`, `Cslib.PartyTensor.unit`,
  `Cslib.PartyTensor.wire`: products of families, push-forwards, unit tensors and wires.
* `Cslib.PartyTensor.CoveredBy`: sums of restrictions.

## Main results

* `Cslib.PartyTensor.instPreorder`: restriction is a preorder, compatible with products
  (`Cslib.PartyTensor.prod_le_prod`) and push-forwards (`Cslib.PartyTensor.push_le_push`).
* `Cslib.PartyTensor.le_of_map`: a tensor whose entries are those of `t` at a leg-wise map of
  the indices, times leg-wise factors, is a restriction of `t`.
* `Cslib.PartyTensor.CoveredBy.bind`, `Cslib.PartyTensor.CoveredBy.of_le`,
  `Cslib.PartyTensor.CoveredBy.mono`, `Cslib.PartyTensor.CoveredBy.mul`,
  `Cslib.PartyTensor.CoveredBy.push`: covers compose and are compatible with the operations.

## References

* [Anthropic, *VP ≠ VNP over every field*, paper and Lean formalization][AnthropicVPVNP2026],
  §A.1 of the paper; modules `Ov.Core.Tensor` and `Ov.Core.Basic`
-/

@[expose] public section

namespace Cslib

open Finset

/-- A tensor over the parties `I` with entries in `K`: for each party `p` a finite index set
`Index p`, and an entry for each choice of one index per party. The zero array is allowed. -/
structure PartyTensor (K : Type) (I : Type) where
  /-- The index set of the leg of a party. -/
  Index : I → Type
  [fintype : ∀ p, Fintype (Index p)]
  [decEq : ∀ p, DecidableEq (Index p)]
  /-- The entry at a choice of one index per party. -/
  entry : (∀ p, Index p) → K

attribute [instance] PartyTensor.fintype PartyTensor.decEq

namespace PartyTensor

variable {K : Type} {I J : Type}

/-! ### Constructions -/

/-- The push-forward: the leg `j` of a tensor over `J` is given to the party `π j`. A party may
get several legs, or none (then its index set has one element). -/
def push [DecidableEq I] [Fintype J] [DecidableEq J] (π : J → I) (t : PartyTensor K J) :
    PartyTensor K I where
  Index q := ∀ j : {j : J // π j = q}, t.Index j.1
  entry x := t.entry (fun j => x (π j) ⟨j, rfl⟩)

theorem push_entry [DecidableEq I] [Fintype J] [DecidableEq J] (π : J → I) (t : PartyTensor K J)
    (x : ∀ q, (push π t).Index q) : (push π t).entry x = t.entry (fun j => x (π j) ⟨j, rfl⟩) :=
  rfl

/-- The same legs with another array. -/
def withEntry (t : PartyTensor K I) (v : (∀ p, t.Index p) → K) : PartyTensor K I where
  Index := t.Index
  entry := v

@[simp] theorem withEntry_entry (t : PartyTensor K I) (v : (∀ p, t.Index p) → K) :
    (t.withEntry v).entry = v := rfl

section Constructions

variable [CommSemiring K]

/-- The tensor `1`: all legs one-dimensional, the entry `1`. -/
instance : One (PartyTensor K I) := ⟨{ Index := fun _ => Unit, entry := fun _ => 1 }⟩

/-- The product (Kronecker product, party by party). -/
instance : Mul (PartyTensor K I) where
  mul s t :=
    { Index := fun p => s.Index p × t.Index p
      entry := fun x : ∀ p, s.Index p × t.Index p =>
        s.entry (fun p => (x p).1) * t.entry (fun p => (x p).2) }

/-- The product of a finite family. -/
def prod {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → PartyTensor K I) : PartyTensor K I where
  Index p := ∀ k, (b k).Index p
  entry x := ∏ k, (b k).entry (fun p => x p k)

/-- The `k`-th power, the product of `k` copies: its indices are `k`-tuples. -/
instance : Pow (PartyTensor K I) ℕ := ⟨fun t k => prod fun _ : Fin k => t⟩

/-- The unit tensor `⟨r⟩_J` of size `r`: the entry is `1` where all indices agree. -/
def unit (K : Type) [CommSemiring K] (J : Type) [Fintype J] (r : ℕ) : PartyTensor K J where
  Index _ := Fin r
  entry x := if ∀ i j, x i = x j then 1 else 0

/-- The wire `⟨n⟩_pq` of dimension `n` between the parties `p` and `q`. -/
def wire (K : Type) [CommSemiring K] {I : Type} [DecidableEq I] (n : ℕ) (p q : I) :
    PartyTensor K I :=
  push ![p, q] (unit K (Fin 2) n)

@[simp] theorem one_entry (x : ∀ p, (1 : PartyTensor K I).Index p) :
    (1 : PartyTensor K I).entry x = 1 := rfl

theorem mul_entry (s t : PartyTensor K I) (x : ∀ p, (s * t).Index p) :
    (s * t).entry x = s.entry (fun p => (x p).1) * t.entry (fun p => (x p).2) := rfl

theorem prod_entry {κ : Type} [Fintype κ] [DecidableEq κ] (b : κ → PartyTensor K I)
    (x : ∀ p, (prod b).Index p) : (prod b).entry x = ∏ k, (b k).entry (fun p => x p k) := rfl

theorem pow_eq_prod (t : PartyTensor K I) (k : ℕ) : t ^ k = prod fun _ : Fin k => t := rfl

theorem unit_entry [Fintype J] (r : ℕ) (x : J → Fin r) :
    (unit K J r).entry x = if ∀ i j, x i = x j then 1 else 0 := rfl

end Constructions

variable [CommSemiring K] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-! ### Local maps applied to arrays -/

/-- One linear map on each leg, as a matrix `L p : α p → β p → K`, applied to an array `f` on
the index tuples of `β`. -/
def localApply {α β : I → Type} [∀ p, Fintype (β p)] (L : ∀ p, α p → β p → K)
    (f : (∀ p, β p) → K) (x : ∀ p, α p) : K :=
  ∑ y, (∏ p, L p (x p) (y p)) * f y

/-- Local maps compose. -/
theorem localApply_comp {α β γ : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (γ p)]
    (L : ∀ p, α p → β p → K) (M : ∀ p, β p → γ p → K) (f : (∀ p, γ p) → K) (x : ∀ p, α p) :
    localApply L (localApply M f) x = localApply (fun p a c => ∑ b, L p a b * M p b c) f x := by
  simp only [localApply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Fintype.prod_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.prod_mul_distrib, mul_assoc]

/-- Local maps applied to a sum. -/
theorem localApply_sum {α β : I → Type} [∀ p, Fintype (β p)] {κ : Type} [Fintype κ]
    (L : ∀ p, α p → β p → K) (f : κ → (∀ p, β p) → K) (x : ∀ p, α p) :
    localApply L (fun y => ∑ k, f k y) x = ∑ k, localApply L (f k) x := by
  simp only [localApply, Finset.mul_sum]
  exact Finset.sum_comm

/-- Local maps applied to a product of two arrays. -/
theorem localApply_mul {α β α' β' : I → Type} [∀ p, Fintype (β p)] [∀ p, Fintype (β' p)]
    (L : ∀ p, α p → β p → K) (L' : ∀ p, α' p → β' p → K)
    (f : (∀ p, β p) → K) (g : (∀ p, β' p) → K) (x : ∀ p, α p × α' p) :
    localApply (β := fun p => β p × β' p) (fun p a b => L p a.1 b.1 * L' p a.2 b.2)
      (fun y => f (fun p => (y p).1) * g (fun p => (y p).2)) x =
    localApply L f (fun p => (x p).1) * localApply L' g (fun p => (x p).2) := by
  simp only [localApply]
  rw [Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  refine Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow I β β') _ _ fun y => ?_
  simp only [Equiv.arrowProdEquivProdArrow_apply, Finset.prod_mul_distrib]
  ring

/-- Local maps applied to a product of a family of arrays. -/
theorem localApply_prod {κ : Type} [Fintype κ] [DecidableEq κ] {α β : κ → I → Type}
    [∀ k p, Fintype (β k p)] (L : ∀ k p, α k p → β k p → K) (f : ∀ k, (∀ p, β k p) → K)
    (x : ∀ p k, α k p) :
    localApply (β := fun p => ∀ k, β k p) (fun p a b => ∏ k, L k p (a k) (b k))
      (fun y => ∏ k, f k (fun p => y p k)) x =
    ∏ k, localApply (L k) (f k) (fun p => x p k) := by
  simp only [localApply]
  rw [Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piComm _) _ _ fun y => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  rfl

/-- Local maps applied to an array whose legs are sorted by parties. -/
theorem localApply_push (π : J → I) {α β : J → Type} [∀ j, Fintype (β j)]
    (L : ∀ j, α j → β j → K) (f : (∀ j, β j) → K) (x : ∀ q, ∀ j : {j : J // π j = q}, α j.1) :
    localApply (β := fun q => ∀ j : {j : J // π j = q}, β j.1)
      (fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j))
      (fun y => f (fun j => y (π j) ⟨j, rfl⟩)) x =
    localApply L f (fun j => x (π j) ⟨j, rfl⟩) := by
  simp only [localApply]
  refine Fintype.sum_equiv (Equiv.piCongrFiberwise (f := π) fun _ => Equiv.refl _).symm _ _
    fun y => ?_
  congr 1
  rw [← Fintype.prod_fiberwise π]
  refine Finset.prod_congr rfl fun q _ => Finset.prod_congr rfl fun ⟨j, hj⟩ _ => ?_
  subst hj
  rfl

/-- Local maps whose matrices have at most one nonzero entry in each row: the row `a` of the
matrix of `p` has the entry `w p a` in the column `g p a`. -/
theorem localApply_map {α β : I → Type} [∀ p, Fintype (β p)] [∀ p, DecidableEq (β p)]
    (w : ∀ p, α p → K) (g : ∀ p, α p → β p) (f : (∀ p, β p) → K) (x : ∀ p, α p) :
    localApply (fun p a b => if b = g p a then w p a else 0) f x =
      (∏ p, w p (x p)) * f (fun p => g p (x p)) := by
  rw [localApply, Finset.sum_eq_single (fun p => g p (x p))]
  · simp
  · intro y _ hy
    obtain ⟨p, hp⟩ := Function.ne_iff.1 hy
    rw [Finset.prod_eq_zero (Finset.mem_univ p) (ite_eq_right hp), zero_mul]
  · exact fun h => absurd (Finset.mem_univ _) h

/-! ### Restrictions -/

/-- `s ≤ t`: `s` is a *restriction* of `t`, it arises from `t` by one linear map on each leg. -/
instance : LE (PartyTensor K I) :=
  ⟨fun s t => ∃ L : ∀ p, s.Index p → t.Index p → K, ∀ x, s.entry x = localApply L t.entry x⟩

theorem le_def {s t : PartyTensor K I} :
    s ≤ t ↔ ∃ L : ∀ p, s.Index p → t.Index p → K, ∀ x, s.entry x = localApply L t.entry x :=
  Iff.rfl

/-- If the entry of `s` at `x` is a product of leg-wise factors times the entry of `t` at
`g x`, where `g` acts leg by leg, then `s` is a restriction of `t`. -/
theorem le_of_map {s t : PartyTensor K I} (w : ∀ p, s.Index p → K) (g : ∀ p, s.Index p → t.Index p)
    (h : ∀ x, s.entry x = (∏ p, w p (x p)) * t.entry (fun p => g p (x p))) : s ≤ t :=
  ⟨fun p a b => if b = g p a then w p a else 0, fun x => by rw [h, localApply_map]⟩

/-- If the entry of `s` at `x` is the entry of `t` at `g x`, where `g` acts leg by leg, then `s`
is a restriction of `t`. -/
theorem le_of_entry_eq {s t : PartyTensor K I} (g : ∀ p, s.Index p → t.Index p)
    (h : ∀ x, s.entry x = t.entry (fun p => g p (x p))) : s ≤ t :=
  le_of_map (fun _ _ => 1) g (by simpa using h)

/-- Restriction is a preorder. -/
instance instPreorder : Preorder (PartyTensor K I) where
  le_refl t := le_of_entry_eq (fun _ a => a) fun _ => rfl
  le_trans s t u := by
    rintro ⟨L, hL⟩ ⟨M, hM⟩
    refine ⟨fun p a c => ∑ b, L p a b * M p b c, fun x => ?_⟩
    rw [hL, ← localApply_comp]
    exact congrArg (localApply L · x) (funext hM)

/-- Products of restrictions are restrictions; clients use `mul_le_mul'`. -/
private theorem mul_le_mul_aux {s t s' t' : PartyTensor K I} (h : s ≤ s') (h' : t ≤ t') :
    s * t ≤ s' * t' := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun p a b => L p a.1 b.1 * M p a.2 b.2, fun x => ?_⟩
  rw [mul_entry, hL, hM]
  exact (localApply_mul L M s'.entry t'.entry x).symm

instance : MulLeftMono (PartyTensor K I) := ⟨fun _ _ _ h => mul_le_mul_aux le_rfl h⟩

instance : MulRightMono (PartyTensor K I) := ⟨fun _ _ _ h => mul_le_mul_aux h le_rfl⟩

/-- Products of families of restrictions are restrictions. -/
@[gcongr]
theorem prod_le_prod {κ : Type} [Fintype κ] [DecidableEq κ] {a b : κ → PartyTensor K I}
    (h : ∀ k, a k ≤ b k) : prod a ≤ prod b := by
  choose L hL using h
  refine ⟨fun p x y => ∏ k, L k p (x k) (y k), fun x => ?_⟩
  rw [prod_entry]
  exact (Finset.prod_congr rfl fun k _ => hL k _).trans
    (localApply_prod (α := fun k p => (a k).Index p) (β := fun k p => (b k).Index p) L
      (fun k => (b k).entry) x).symm

/-- Restrictions stay restrictions when the legs are given to other parties. -/
@[gcongr]
theorem push_le_push (π : J → I) {s t : PartyTensor K J} (h : s ≤ t) : push π s ≤ push π t := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun q a b => ∏ j : {j : J // π j = q}, L j.1 (a j) (b j), fun x => ?_⟩
  rw [push_entry, hL]
  exact (localApply_push π L t.entry x).symm

theorem monotone_push (π : J → I) : Monotone (push π : PartyTensor K J → PartyTensor K I) :=
  fun _ _ => push_le_push π

/-- `1` is a restriction of every tensor with a nonzero entry, if there is a party. -/
theorem one_le_of_entry_ne_zero {K : Type} [Field K] [Nonempty I] {t : PartyTensor K I}
    {y : ∀ p, t.Index p} (h : t.entry y ≠ 0) : 1 ≤ t := by
  classical
  let p₀ : I := Classical.arbitrary I
  refine le_of_map (fun p _ => if p = p₀ then (t.entry y)⁻¹ else 1) (fun p _ => y p) fun x => ?_
  rw [Finset.prod_ite_eq' Finset.univ p₀]
  simp [h]

/-! ### Covers: sums of restrictions -/

/-- `s` is *covered* by the family `b`: it is a sum of restrictions of its members, one
restriction of each `b k` (which may be `0`). -/
def CoveredBy {κ : Type} [Fintype κ] (s : PartyTensor K I) (b : κ → PartyTensor K I) : Prop :=
  ∃ L : ∀ k p, s.Index p → (b k).Index p → K, ∀ x, s.entry x = ∑ k, localApply (L k) (b k).entry x

section Cover

variable {κ κ' : Type} [Fintype κ] [Fintype κ']

/-- `s` is covered by the `b k` if and only if its array is a sum of arrays, the `k`-th of which
is a restriction of `b k`. -/
theorem coveredBy_iff {s : PartyTensor K I} {b : κ → PartyTensor K I} :
    s.CoveredBy b ↔ ∃ v : κ → (∀ p, s.Index p) → K,
      (∀ x, s.entry x = ∑ k, v k x) ∧ ∀ k, s.withEntry (v k) ≤ b k := by
  constructor
  · rintro ⟨L, hL⟩
    exact ⟨fun k x => localApply (L k) (b k).entry x, hL, fun k => ⟨L k, fun _ => rfl⟩⟩
  · rintro ⟨v, hv, h⟩
    choose L hL using h
    exact ⟨L, fun x => (hv x).trans (Finset.sum_congr rfl fun k _ => hL k x)⟩

/-- If the array of `s` is the sum of the arrays `v k`, then `s` is covered by the tensors with
these arrays. -/
theorem CoveredBy.withEntry (s : PartyTensor K I) (v : κ → (∀ p, s.Index p) → K)
    (h : ∀ x, s.entry x = ∑ k, v k x) : s.CoveredBy fun k => s.withEntry (v k) :=
  coveredBy_iff.2 ⟨v, h, fun _ => le_rfl⟩

/-- A restriction is covered by a family with one member. -/
theorem CoveredBy.single {s t : PartyTensor K I} (h : s ≤ t) : s.CoveredBy fun _ : Unit => t := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun _ => L, fun x => by simpa using hL x⟩

/-- A tensor whose array is `0` is covered by the empty family. -/
theorem CoveredBy.of_entry_eq_zero [IsEmpty κ] {s : PartyTensor K I} (h : ∀ x, s.entry x = 0)
    (b : κ → PartyTensor K I) : s.CoveredBy b :=
  ⟨fun k => isEmptyElim k, fun x => by simp [h]⟩

/-- Covers compose: if `s` is covered by the `b k` and each `b k` by the `c k m`, then `s` is
covered by all the `c k m`. -/
theorem CoveredBy.bind {μ : κ → Type} [∀ k, Fintype (μ k)] {s : PartyTensor K I}
    {b : κ → PartyTensor K I} {c : ∀ k, μ k → PartyTensor K I} (h : s.CoveredBy b)
    (h' : ∀ k, (b k).CoveredBy (c k)) : s.CoveredBy fun x : Σ k, μ k => c x.1 x.2 := by
  obtain ⟨L, hL⟩ := h
  choose M hM using h'
  refine ⟨fun x p a d => ∑ b, L x.1 p a b * M x.1 x.2 p b d, fun x => ?_⟩
  rw [hL, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (b k).entry = _ from funext (hM k), localApply_sum]
  exact Finset.sum_congr rfl fun m _ => localApply_comp _ _ _ _

/-- A restriction of a covered tensor is covered by the same family. -/
theorem CoveredBy.of_le {s t : PartyTensor K I} {b : κ → PartyTensor K I} (h : s ≤ t)
    (h' : t.CoveredBy b) : s.CoveredBy b := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p a d => ∑ b, L p a b * M k p b d, fun x => ?_⟩
  rw [hL, show t.entry = _ from funext hM, localApply_sum]
  exact Finset.sum_congr rfl fun m _ => localApply_comp _ _ _ _

/-- Each member of a cover may be replaced by a tensor of which it is a restriction. -/
theorem CoveredBy.mono {s : PartyTensor K I} {b c : κ → PartyTensor K I} (h : s.CoveredBy b)
    (h' : ∀ k, b k ≤ c k) : s.CoveredBy c := by
  obtain ⟨v, hv, h⟩ := coveredBy_iff.1 h
  exact coveredBy_iff.2 ⟨v, hv, fun k => (h k).trans (h' k)⟩

/-- The members of a cover may be renamed. -/
theorem CoveredBy.reindex {s : PartyTensor K I} {b : κ → PartyTensor K I} (h : s.CoveredBy b)
    (e : κ' ≃ κ) : s.CoveredBy fun k => b (e k) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨fun k => L (e k), fun x => (hL x).trans (Fintype.sum_equiv e _ _ fun _ => rfl).symm⟩

/-- The product of two covered tensors is covered by the products of two members. -/
theorem CoveredBy.mul {s t : PartyTensor K I} {b : κ → PartyTensor K I} {c : κ' → PartyTensor K I}
    (h : s.CoveredBy b) (h' : t.CoveredBy c) :
    (s * t).CoveredBy fun k : κ × κ' => b k.1 * c k.2 := by
  obtain ⟨L, hL⟩ := h
  obtain ⟨M, hM⟩ := h'
  refine ⟨fun k p x y => L k.1 p x.1 y.1 * M k.2 p x.2 y.2, fun x => ?_⟩
  rw [mul_entry, hL, hM, Finset.sum_mul_sum, ← Fintype.sum_prod_type']
  exact Finset.sum_congr rfl fun k _ =>
    (localApply_mul (L k.1) (M k.2) (b k.1).entry (c k.2).entry x).symm

/-- A cover stays a cover when the legs are given to other parties. -/
theorem CoveredBy.push (π : J → I) {s : PartyTensor K J} {b : κ → PartyTensor K J}
    (h : s.CoveredBy b) : (push π s).CoveredBy fun k => PartyTensor.push π (b k) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨fun k q x y => ∏ j : {j : J // π j = q}, L k j.1 (x j) (y j), fun x => ?_⟩
  rw [push_entry, hL]
  exact Finset.sum_congr rfl fun k _ => (localApply_push π (L k) (b k).entry x).symm

end Cover

end PartyTensor

end Cslib
