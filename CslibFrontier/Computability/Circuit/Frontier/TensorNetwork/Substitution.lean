/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Open
public import Mathlib.Basic.Real.Basic
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Data.Fintype.BigOperators

/-!
# Connecting open tensor networks

Pairing two exterior bits makes them one internal wire. Its contraction sums over their common
value, including when they belong to the same vertex. The disjoint union of local realizations
can thus be wired in any pattern, including cycles and wires between two replaced vertices.
-/

public section

namespace Cslib.Circuits.Frontier.OpenBitNetwork

section Connect

variable {R J I Q V E : Type*} [Finite J] [Finite I] [Finite Q] [Finite V] [Finite E]
  (N : OpenBitNetwork R J V E) (legs : (Q ⊕ Q) ⊕ I ≃ J)

/-- Replace each indicated pair of exterior legs by one internal wire. The two legs can be at
any vertices, including the same vertex. Legs indexed by `I` remain exposed. -/
def connect : OpenBitNetwork R I V (E ⊕ Q) where
  src := Sum.elim N.src (fun q => N.site (legs (.inl (.inl q))))
  tgt := Sum.elim N.tgt (fun q => N.site (legs (.inl (.inr q))))
  site i := N.site (legs (.inr i))
  tensor v α x := N.tensor v (α ∘ Sum.inl)
    (Sum.elim (Sum.elim (α ∘ Sum.inr) (α ∘ Sum.inr)) x ∘ legs.symm)
  tensor_congr v α β h := by
    funext x
    rw [N.tensor_congr v (α ∘ Sum.inl) (β ∘ Sum.inl) (fun e he => h (.inl e) he)]
    apply N.exterior_congr
    intro j hj
    obtain ⟨(q | q) | i, rfl⟩ := legs.surjective j
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl] using
        h (.inr q) (.inl hj)
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr] using
        h (.inr q) (.inr hj)
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr]
  exterior_congr v α x y h := by
    apply N.exterior_congr
    intro j hj
    obtain ⟨(q | q) | i, rfl⟩ := legs.surjective j
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl]
    · simp only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
    · simpa only [Function.comp_apply, Equiv.symm_apply_apply, Sum.elim_inr] using h i hj

/-- Connecting exterior legs leaves the incidence count at each vertex unchanged. -/
theorem Trivalent.connect (hN : N.Trivalent) : (N.connect legs).Trivalent := by
  intro v
  have h := hN v
  change Nat.card {e // N.src e = v} + Nat.card {e // N.tgt e = v} +
    Nat.card {i // N.site i = v} ≤ 3 at h
  rw [Nat.card_subtype_eq_add_of_equiv_sum legs.symm, Nat.card_subtype_sum] at h
  change Nat.card {e // (N.connect legs).src e = v} + Nat.card {e // (N.connect legs).tgt e = v} +
    Nat.card {i // N.site (legs (.inr i)) = v} ≤ 3
  simp only [Nat.card_subtype_sum]
  change Nat.card {e // N.src e = v} + Nat.card {q // N.site (legs (.inl (.inl q))) = v} +
    (Nat.card {e // N.tgt e = v} + Nat.card {q // N.site (legs (.inl (.inr q))) = v}) +
    Nat.card {i // N.site (legs (.inr i)) = v} ≤ 3
  simp only [Equiv.symm_symm] at h
  lia

/-- Each joined pair decreases volume by one, independently of topology and tensor values. -/
theorem volume_connect : (N.connect legs).volume + Nat.card Q = N.volume := by
  have h := Nat.card_congr legs
  simp only [Nat.card_sum] at h
  simp only [volume, Nat.card_sum]
  lia

/-- Contraction of a joined network sums the old tensor over the common value of each pair. -/
theorem contraction_connect [CommSemiring R] [Fintype V] [Fintype E] [Fintype Q] [DecidableEq E]
    [DecidableEq Q] (x : I → Bool) :
    (N.connect legs).contraction x = ∑ γ : Q → Bool,
      N.contraction (Sum.elim (Sum.elim γ γ) x ∘ legs.symm) := by
  classical
  simp only [TensorNetwork.contraction, Finset.sum_apply, Finset.prod_apply]
  rw [← (Equiv.sumArrowEquivProdArrow E Q Bool).symm.sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

end Connect

section Family

variable {R A : Type*} {J V E : A → Type*} [Finite A] [∀ a, Finite (J a)]
  [∀ a, Finite (V a)] [∀ a, Finite (E a)] (B : ∀ a, OpenBitNetwork R (J a) (V a) (E a))

/-- Disjoint union of a finite family, retaining every component's named exterior legs. -/
def disjointUnion : OpenBitNetwork R (Σ a, J a) (Σ a, V a) (Σ a, E a) where
  src e := ⟨e.1, (B e.1).src e.2⟩
  tgt e := ⟨e.1, (B e.1).tgt e.2⟩
  site j := ⟨j.1, (B j.1).site j.2⟩
  tensor v α x := (B v.1).tensor v.2 (fun e => α ⟨v.1, e⟩) (fun i => x ⟨v.1, i⟩)
  tensor_congr v α β h := by
    funext x
    exact congrFun ((B v.1).tensor_congr v.2 _ _ fun e he =>
      h ⟨v.1, e⟩ (he.imp (congrArg (Sigma.mk v.1)) (congrArg (Sigma.mk v.1)))) _
  exterior_congr v α x y h := (B v.1).exterior_congr v.2 _ _ _ fun i hi =>
    h ⟨v.1, i⟩ (congrArg (Sigma.mk v.1) hi)

private theorem card_fiber_sigma {ι : Type*} {U W : ι → Type*} (f : ∀ a, U a → W a) (a : ι)
    (w : W a) :
    Nat.card {p : Σ i, U i // Sigma.mk p.1 (f p.1 p.2) = ⟨a, w⟩} =
      Nat.card {u : U a // f a u = w} := by
  symm
  apply Nat.card_congr (Equiv.ofBijective
    (fun u => ⟨⟨a, u.val⟩, congrArg (Sigma.mk a) u.prop⟩) ?_)
  constructor
  · rintro ⟨u, hu⟩ ⟨v, hv⟩ h
    simpa using h
  · rintro ⟨⟨b, u⟩, h⟩
    have hb := congrArg Sigma.fst h
    change b = a at hb
    subst b
    exact ⟨⟨u, by simpa using h⟩, rfl⟩

/-- Trivalent components give a trivalent union, with no restriction on their order or size. -/
theorem trivalent_disjointUnion (h : ∀ a, (B a).Trivalent) : (disjointUnion B).Trivalent := by
  rintro ⟨a, v⟩
  change Nat.card {e // (disjointUnion B).src e = ⟨a, v⟩} +
    Nat.card {e // (disjointUnion B).tgt e = ⟨a, v⟩} +
    Nat.card {i // (disjointUnion B).site i = ⟨a, v⟩} ≤ 3
  simp only [disjointUnion]
  rw [card_fiber_sigma (fun a => (B a).src) a v, card_fiber_sigma (fun a => (B a).tgt) a v,
    card_fiber_sigma (fun a => (B a).site) a v]
  exact h a v

/-- The disjoint union computes the product of all the local exterior tensors. -/
theorem contraction_disjointUnion [Fintype A] [∀ a, Fintype (V a)] [∀ a, Fintype (E a)]
    [DecidableEq (Σ a, E a)] [∀ a, DecidableEq (E a)] [CommSemiring R] (x : (Σ a, J a) → Bool) :
    (disjointUnion B).contraction x = ∏ a, (B a).contraction (fun i => x ⟨a, i⟩) := by
  classical
  simp only [TensorNetwork.contraction, Finset.sum_apply, Finset.prod_apply, Fintype.prod_sum]
  refine Fintype.sum_equiv (Equiv.piCurry (fun a (_ : E a) => Bool)) _ _ fun α => ?_
  exact Fintype.prod_sigma _

/-- Counting vertices and internal and exterior wires is additive under disjoint union. -/
theorem volume_disjointUnion [Fintype A] : (disjointUnion B).volume = ∑ a, (B a).volume := by
  simp only [volume, Nat.card_sigma, Finset.sum_add_distrib]

end Family

section Substitute

variable {R I V E : Type*} [Finite I] [Finite V] [Finite E] (N : OpenBitNetwork R I V E)

/-- An incidence at `v` is the source or target end of an internal wire, or one exterior leg.
The two incidences of a loop are distinct. -/
abbrev Port (v : V) := {p : (E ⊕ E) ⊕ I // Sum.elim (Sum.elim N.src N.tgt) N.site p = v}

/-- Total arity charges each internal edge twice and each exterior bit once. -/
theorem sum_card_port [Fintype V] : ∑ v, Nat.card (N.Port v) = 2 * Nat.card E + Nat.card I := by
  rw [← Nat.card_sigma]
  exact (Nat.card_congr (Equiv.sigmaFiberEquiv _)).trans (by simp [Nat.card_sum, two_mul])

variable {J W F : V → Type*} [∀ v, Finite (J v)] [∀ v, Finite (W v)] [∀ v, Finite (F v)]
  (ports : ∀ v, N.Port v ≃ J v) (B : ∀ v, OpenBitNetwork R (J v) (W v) (F v))

private def portEquiv : (E ⊕ E) ⊕ I ≃ Σ v, J v :=
  (Equiv.sigmaFiberEquiv (Sum.elim (Sum.elim N.src N.tgt) N.site)).symm.trans
    (Equiv.sigmaCongrRight ports)

/-- Replace the table of every vertex by a network with the same incident legs, reconnecting the
old internal wires and retaining the old exterior bits. -/
def substitute : OpenBitNetwork R I (Σ v, W v) ((Σ v, F v) ⊕ E) :=
  (disjointUnion B).connect (N.portEquiv ports)

/-- Replacing every table with a trivalent network gives a trivalent result, irrespective of
how many legs the original table used. -/
theorem trivalent_substitute (h : ∀ v, (B v).Trivalent) : (N.substitute ports B).Trivalent :=
  Trivalent.connect _ _ (trivalent_disjointUnion B h)

/-- Each old internal wire joins two replacement legs and costs only once in the result. -/
theorem volume_substitute [Fintype V] :
    (N.substitute ports B).volume + Nat.card E = ∑ v, (B v).volume :=
  ((disjointUnion B).volume_connect _).trans (volume_disjointUnion B)

/-- A local cost bounded by one vertex plus `p` per incident leg bounds the entire substituted
network using the original incidence count. -/
theorem volume_substitute_le_of_incidence {p : ℝ}
    (h : ∀ v, ((B v).volume : ℝ) ≤ 1 + p * Nat.card (N.Port v)) :
    ((N.substitute ports B).volume : ℝ) ≤ Nat.card V + p * (2 * Nat.card E + Nat.card I) := by
  let := Fintype.ofFinite V
  have htotal : (∑ v, (B v).volume : ℕ) = (N.substitute ports B).volume + Nat.card E :=
    (volume_substitute N ports B).symm
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun v _ => h v)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Nat.cast_sum, ← Nat.cast_sum, N.sum_card_port,
    htotal] at hsum
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, Nat.cast_add,
    Nat.cast_mul, Nat.cast_ofNat, ← Nat.card_eq_fintype_card] at hsum
  exact (le_add_of_nonneg_right (Nat.cast_nonneg (α := ℝ) (Nat.card E))).trans hsum

/-- Pointwise equality of each replacement contraction and the old table implies equality of
both exterior tensors, including when old wires join replacements or return to the same one. -/
theorem contraction_substitute [CommSemiring R] [Fintype V] [Fintype E] [DecidableEq E]
    [∀ v, Fintype (W v)] [∀ v, Fintype (F v)] [DecidableEq (Σ v, F v)] [∀ v, DecidableEq (F v)]
    (h : ∀ v (α : E → Bool) (x : I → Bool),
      (B v).contraction (fun j => Sum.elim (Sum.elim α α) x ((ports v).symm j).val) =
        N.tensor v α x) (x : I → Bool) :
    (N.substitute ports B).contraction x = N.contraction x := by
  classical
  rw [substitute, contraction_connect]
  simp_rw [contraction_disjointUnion]
  change (∑ α : E → Bool, ∏ v, (B v).contraction
    (fun j => Sum.elim (Sum.elim α α) x ((ports v).symm j).val)) = _
  calc _ = ∑ α, ∏ v, N.tensor v α x :=
         Finset.sum_congr rfl fun α _ => Finset.prod_congr rfl fun v _ => h v α x
       _ = _ := by simp only [TensorNetwork.contraction, Finset.sum_apply, Finset.prod_apply]

end Substitute

section Calls

variable {R I V E : Type*} [Finite I] [Finite V] [Finite E] (N : OpenBitNetwork R I V E)

open scoped Classical in
/-- The existing table at `v` on a single vertex. When `v` has a loop, assignments with distinct
values at its two ends are read at the source end. Connecting the loop identifies those ends. -/
private noncomputable def originalVertex (v : V) : OpenBitNetwork R (N.Port v) Unit Empty where
  src := Empty.elim
  tgt := Empty.elim
  site _ := ()
  tensor _ _ z := N.tensor v
    (fun e => if hs : N.src e = v then z ⟨.inl (.inl e), hs⟩
      else if ht : N.tgt e = v then z ⟨.inl (.inr e), ht⟩ else false)
    (fun i => if hi : N.site i = v then z ⟨.inr i, hi⟩ else false)
  tensor_congr _ _ _ _ := rfl
  exterior_congr _ _ x y h := by rw [show x = y from funext fun i => h i rfl]

private theorem trivalent_originalVertex (v : V) (h : Nat.card (N.Port v) ≤ 3) :
    (N.originalVertex v).Trivalent := by
  rintro ⟨⟩
  change Nat.card {e : Empty // _} + Nat.card {e : Empty // _} +
    Nat.card {i : N.Port v // () = ()} ≤ 3
  simpa only [Nat.card_of_isEmpty, add_zero, zero_add] using
    (Nat.card_le_card_of_injective (Subtype.val : {i : N.Port v // () = ()} → _)
      Subtype.val_injective).trans h

private theorem contraction_originalVertex [CommSemiring R] (v : V) (α : E → Bool) (x : I → Bool) :
    (N.originalVertex v).contraction (fun j => Sum.elim (Sum.elim α α) x j.val) =
      N.tensor v α x := by
  classical
  simp only [TensorNetwork.contraction, Finset.sum_apply, Fintype.prod_unique,
    Fintype.sum_unique, originalVertex]
  refine (congrFun (N.tensor_congr v _ α ?_) _).trans (N.exterior_congr v _ _ _ ?_)
  · intro e he
    by_cases hs : N.src e = v
    · simp [hs]
    · simp [hs, he.resolve_left hs]
  · intro i hi
    simp [hi]

/-- The total number of call arguments is bounded by the host's charged incidences, even if
one internal wire connects two calls or supplies both ends at the same call. -/
theorem call_arity_le {I O C E L : Type*} [Finite I] [Finite O] [Finite C] [Finite E]
    (N : OpenBitNetwork R I (O ⊕ C) E) (ports : ∀ c, N.Port (.inr c) ≃ L) :
    Nat.card C * Nat.card L ≤ 2 * Nat.card E + Nat.card I := by
  let := Fintype.ofFinite O
  let := Fintype.ofFinite C
  rw [← N.sum_card_port, Fintype.sum_sum_type]
  have h (c : C) := Nat.card_congr (ports c)
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card,
    Nat.cast_id]
  exact Nat.le_add_left ..

/-- Different calls can use different exact tables and exterior label sets on the same vertex and
internal wire types. The formula counts the new interior once per call. -/
theorem exists_replace_call_family {I O C E U H : Type} {L : C → Type} [Finite I] [Fintype O]
    [Fintype C] [Fintype E] [DecidableEq E] [∀ c, Finite (L c)] [Fintype U] [Fintype H]
    [DecidableEq H] [CommSemiring R]
    (N : OpenBitNetwork R I (O ⊕ C) E) (D : ∀ c, OpenBitNetwork R (L c) U H)
    (ports : ∀ c, N.Port (.inr c) ≃ L c)
    (ho : ∀ o, Nat.card (N.Port (.inl o)) ≤ 3) (hD : ∀ c, (D c).Trivalent)
    (h : ∀ c (α : E → Bool) (x : I → Bool),
      (D c).contraction (fun j => Sum.elim (Sum.elim α α) x ((ports c).symm j).val) =
        N.tensor (.inr c) α x) :
    ∃ (W F : Type) (_ : Fintype W) (_ : Fintype F) (_ : DecidableEq F)
      (M : OpenBitNetwork R I W F), M.Trivalent ∧
      M.volume = Nat.card O + Nat.card E + Nat.card I + Nat.card C * (Nat.card U + Nat.card H) ∧
      ∀ x, M.contraction x = N.contraction x := by
  classical
  let J : O ⊕ C → Type := Sum.elim (fun o => N.Port (.inl o)) L
  let W : O ⊕ C → Type := Sum.elim (fun _ => Unit) (fun _ => U)
  let F : O ⊕ C → Type := Sum.elim (fun _ => Empty) (fun _ => H)
  let (v : O ⊕ C) : Finite (J v) := by cases v <;> dsimp [J] <;> infer_instance
  let (v : O ⊕ C) : Fintype (W v) := by cases v <;> dsimp [W] <;> infer_instance
  let (v : O ⊕ C) : Fintype (F v) := by cases v <;> dsimp [F] <;> infer_instance
  let (v : O ⊕ C) : DecidableEq (F v) := by cases v <;> dsimp [F] <;> infer_instance
  let legs : ∀ v, N.Port v ≃ J v := fun | .inl _ => Equiv.refl _ | .inr c => ports c
  let B : ∀ v, OpenBitNetwork R (J v) (W v) (F v) :=
    fun | .inl o => N.originalVertex (.inl o) | .inr c => D c
  refine ⟨_, _, inferInstance, inferInstance, inferInstance, N.substitute legs B, ?_, ?_, ?_⟩
  · apply trivalent_substitute
    rintro (o | c)
    · exact trivalent_originalVertex N _ (ho o)
    · exact hD c
  · simp only [volume, Nat.card_sum, Nat.card_sigma, Fintype.sum_sum_type, W, F, Sum.elim_inl,
      Sum.elim_inr, Nat.card_unique, Nat.card_of_isEmpty, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one, mul_zero, zero_add, ← Nat.card_eq_fintype_card, Nat.cast_id,
      Nat.mul_add]
    ac_rfl
  · apply contraction_substitute
    rintro (o | c) α x
    · exact contraction_originalVertex N _ α x
    · convert! h c α x using 2


/-- Replace each designated call in `N` by the same exact verifier. Other vertices retain their
tables. The implementation adds just the verifier's inner vertices and wires per call. Any old
wires between calls, or from a call to itself, are counted and reconnected exactly once. -/
theorem exists_replace_calls {I O C E L U H : Type} [Finite I] [Fintype O] [Fintype C]
    [Fintype E] [DecidableEq E] [Finite L] [Fintype U] [Fintype H] [DecidableEq H] [CommSemiring R]
    (N : OpenBitNetwork R I (O ⊕ C) E) (D : OpenBitNetwork R L U H)
    (ports : ∀ c, N.Port (.inr c) ≃ L)
    (ho : ∀ o, Nat.card (N.Port (.inl o)) ≤ 3) (hD : D.Trivalent)
    (h : ∀ c (α : E → Bool) (x : I → Bool),
      D.contraction (fun j => Sum.elim (Sum.elim α α) x ((ports c).symm j).val) =
        N.tensor (.inr c) α x) :
    ∃ (W F : Type) (_ : Fintype W) (_ : Fintype F) (_ : DecidableEq F)
      (M : OpenBitNetwork R I W F), M.Trivalent ∧
      M.volume = Nat.card O + Nat.card E + Nat.card I + Nat.card C * (Nat.card U + Nat.card H) ∧
      ∀ x, M.contraction x = N.contraction x :=
  exists_replace_call_family N (fun _ => D) ports ho (fun _ => hD) h

end Calls

end Cslib.Circuits.Frontier.OpenBitNetwork
