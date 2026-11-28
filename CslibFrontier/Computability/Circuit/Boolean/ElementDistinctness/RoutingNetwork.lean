/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.TaggedPermutation
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Open
import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.VolumeToSize
import CslibFrontier.Foundations.Data.BitString.Support.Equiv
import Mathlib.Logic.Equiv.Bool
import Mathlib.Tactic.DeriveFintype
import Mathlib.Tactic.Ring

/-!
# Routing records with one distinctness network

A source record carries its destination and its payload. Each destination has an independent
selector. Put the selector in the first bit of its request record and use a common zero
padding bit in every record. Each address or payload bit occupies a single exterior wire.
The signed comparison of `taggedPermutation_eq_sum_elementDistinctness` is therefore a
contraction against unary tables. The construction applies to a joint realization of any
number of lists, including networks that share their internal wires among lists.

This sharpens the construction in [OpenAI2026MatrixExponentNineFourths, “Checking a tagged
permutation”]. At the paper's exact word width, `exists_taggedPermutationNetwork` uses the
given network once and bounds the new volume by the old volume over any commutative ring.
-/

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Finset Function Frontier

/-- Exterior bits of a tagged-permutation test on `2 ^ h` records of `h` bits each. -/
public inductive RoutingBit (h : ℕ) where
  /-- A binary digit of the destination requested by an incoming record. -/
  | tag (row : Fin (2 ^ h)) (bit : Fin h)
  /-- A bit of the payload at an incoming record. -/
  | input (row : Fin (2 ^ h)) (bit : Fin h)
  /-- A bit of the expected payload at a destination. -/
  | output (row : Fin (2 ^ h)) (bit : Fin h)
  deriving DecidableEq, Fintype

/-- The binary tags form a permutation, and the input at each row equals the output at its tag. -/
@[expose] public def TaggedPermutation {h : ℕ} (z : RoutingBit h → Bool) : Prop :=
  let dest (i : Fin (2 ^ h)) := BitString.equivFin h fun b => z (.tag i b)
  Bijective dest ∧ ∀ i b, z (.input i b) = z (.output (dest i) b)

private abbrev Live (n k : ℕ) :=
  (Fin n × Fin (Nat.clog 2 n)) ⊕ (Fin n × Fin k) ⊕ (Fin n × Fin k)

private inductive PinnedWire (I A : Type*) where
  | sourceFlag (i : I)
  | sourcePad (i : I)
  | requestPad (i : I)
  | requestTag (i : I) (b : A)
  deriving DecidableEq, Fintype

private abbrev Fixed (n : ℕ) := PinnedWire (Fin n) (Fin (Nat.clog 2 n))

-- Classify a physical bit by its half, row, and position within the record.
private def rearrange {I A P : Type*} :
    (I ⊕ I) × Option (A ⊕ Option P) ≃
      ((I × A) ⊕ (I × P) ⊕ (I × P)) ⊕ I ⊕ PinnedWire I A where
  toFun
    | (.inl i, none) => .inr (.inr (.sourceFlag i))
    | (.inl i, some (.inl b)) => .inl (.inl (i, b))
    | (.inl i, some (.inr none)) => .inr (.inr (.sourcePad i))
    | (.inl i, some (.inr (some b))) => .inl (.inr (.inl (i, b)))
    | (.inr i, none) => .inr (.inl i)
    | (.inr i, some (.inl b)) => .inr (.inr (.requestTag i b))
    | (.inr i, some (.inr none)) => .inr (.inr (.requestPad i))
    | (.inr i, some (.inr (some b))) => .inl (.inr (.inr (i, b)))
  invFun
    | .inl (.inl (i, b)) => (.inl i, some (.inl b))
    | .inl (.inr (.inl (i, b))) => (.inl i, some (.inr (some b)))
    | .inl (.inr (.inr (i, b))) => (.inr i, some (.inr (some b)))
    | .inr (.inl i) => (.inr i, none)
    | .inr (.inr (.sourceFlag i)) => (.inl i, none)
    | .inr (.inr (.sourcePad i)) => (.inl i, some (.inr none))
    | .inr (.inr (.requestPad i)) => (.inr i, some (.inr none))
    | .inr (.inr (.requestTag i b)) => (.inr i, some (.inl b))
  left_inv := by rintro ⟨(i | i), (_ | (b | (_ | b)))⟩ <;> rfl
  right_inv := by rintro ((p | (p | p)) | (i | (_ | _ | _ | _))) <;> rfl

private def split (n k : ℕ) : Fin ((n + n) * (Nat.clog 2 n + (k + 1) + 1)) ≃
    (Fin n ⊕ Fin n) × Option (Fin (Nat.clog 2 n) ⊕ Option (Fin k)) :=
  finProdFinEquiv.symm.trans <| finSumFinEquiv.symm.prodCongr <| (finSuccEquiv _).trans <|
    Equiv.optionCongr <| finSumFinEquiv.symm.trans <| Equiv.sumCongr (Equiv.refl _) (finSuccEquiv _)

/-- Each bit of a comparison belongs to exactly one live data wire, reserve bit or fixed bit. -/
private def layout (n k : ℕ) :
    Fin ((n + n) * (Nat.clog 2 n + (k + 1) + 1)) ≃ Live n k ⊕ Fin n ⊕ Fixed n :=
  (split n k).trans rearrange

private def fixedBits (n : ℕ) : Fixed n → Bool
  | .sourceFlag _ | .sourcePad _ | .requestPad _ => false
  | .requestTag i b => BitString.indexBits i b

private def liveBits {n k : ℕ} (tag : Fin n → Fin n)
    (x y : Fin n → BitString k) : Live n k → Bool :=
  Sum.elim (fun p => BitString.indexBits (tag p.1) p.2)
    (Sum.elim (fun p => x p.1 p.2) (fun p => y p.1 p.2))

private theorem comparison_eq_layout {n k : ℕ} (tag : Fin n → Fin n)
    (x y : Fin n → BitString k) (S : Finset (Fin n)) :
    comparisonInput (fun i => Fin.append (BitString.indexBits (tag i)) (Fin.cons false (x i)))
      (fun j => Fin.append (BitString.indexBits j) (Fin.cons false (y j))) S =
      Sum.elim (liveBits tag x y)
        (Sum.elim (fun j => decide (j ∉ S)) (fixedBits n)) ∘ layout n k := by
  funext p
  obtain ⟨⟨row, col⟩, rfl⟩ := (split n k).symm.surjective p
  simp only [Function.comp_apply, layout, Equiv.trans_apply, Equiv.apply_symm_apply]
  rcases row with i | i <;> rcases col with _ | (b | (_ | b)) <;>
    simp [comparisonInput, split, rearrange, liveBits, fixedBits, ← Equiv.optionCongr_symm,
      -Fin.natAdd_eq_addNat]

private def unary {R : Type*} [CommRing R] {I P : Type*} (pin : P → Bool) :
    I ⊕ P → Bool → R :=
  Sum.elim (fun _ s => if s then 1 else -1) (fun i b => if b = pin i then 1 else 0)

private theorem sum_unary {R I P : Type*} [CommRing R] [Fintype I] [Fintype P]
    [DecidableEq I] [DecidableEq P] (pin : P → Bool) (f : (I ⊕ P → Bool) → R) :
    (∑ hidden, (∏ i, unary pin i (hidden i)) * f hidden) =
      ∑ S : Finset I, (-1 : R) ^ #S * f (Sum.elim (fun j => decide (j ∉ S)) pin) := by
  classical
  let split := Equiv.sumArrowEquivProdArrow I P Bool
  let reserve : Finset I ≃ (I → Bool) :=
    BitString.supportEquiv.symm.trans ((Equiv.refl I).arrowCongr Equiv.boolNot)
  have reserve_apply (S : Finset I) (j : I) : reserve S j = decide (j ∉ S) := by
    simp [reserve, Equiv.boolNot]
  have hsplit (s : I → Bool) (b : P → Bool) : split.symm (s, b) = Sum.elim s b := rfl
  rw [← split.symm.sum_comp, Fintype.sum_prod_type, ← reserve.sum_comp]
  refine sum_congr rfl fun S _ => ?_
  simp only [hsplit, Fintype.prod_sum_type, unary, Sum.elim_inl, Sum.elim_inr, reserve_apply,
    Fintype.prod_ite_zero]
  have hsign : (∏ i, if decide (i ∉ S) then (1 : R) else -1) = (-1 : R) ^ #S := by
    simp
  rw [hsign, show reserve S = _ from funext (reserve_apply S)]
  simp [← funext_iff]

private theorem sum_ed_generic (R : Type*) [CommRing R] {n k : ℕ}
    (tag : Fin n → Fin n) (x y : Fin n → BitString k) :
    (∑ hidden : Fin n ⊕ Fixed n → Bool, (∏ i, unary (fixedBits n) i (hidden i)) *
      (if elementDistinctness (n + n) (Nat.clog 2 n + (k + 1) + 1)
        (Sum.elim (liveBits tag x y) hidden ∘ layout n k) then (1 : R) else 0)) =
      if Bijective tag ∧ ∀ i, x i = y (tag i) then 1 else 0 := by
  classical
  rw [sum_unary]
  have ht := taggedPermutation_eq_sum_elementDistinctness R tag
    (fun i => Fin.cons false (x i)) (fun j => Fin.cons false (y j))
  simp only [Fin.cons_inj, true_and] at ht
  rw [ht]
  refine sum_congr rfl fun S _ => ?_
  rw [comparison_eq_layout]
  split <;> simp

/-- Rows and bits at the exact scale of the distinctness tensor, including one zero padding
bit on every record. -/
private def dyadicLayout (h : ℕ) :
    Fin (2 ^ (h + 1) * (2 * (h + 1))) ≃ Live (2 ^ h) h ⊕ Fin (2 ^ h) ⊕ Fixed (2 ^ h) :=
  (finCongr (show 2 ^ (h + 1) * (2 * (h + 1)) =
      (2 ^ h + 2 ^ h) * (Nat.clog 2 (2 ^ h) + (h + 1) + 1) by
        rw [pow_succ, Nat.clog_pow 2 h one_lt_two]
        ring)).trans (layout _ _)

private theorem distinctness_reindex {m n a b : ℕ} (hr : m = n) (hc : a = b)
    (f : BitString (n * b)) :
    elementDistinctness m a (f ∘ finCongr (congrArg₂ (· * ·) hr hc)) =
      elementDistinctness n b f := by
  subst n
  subst b
  rfl

private theorem dyadic_eval (h : ℕ)
    (f : Live (2 ^ h) h ⊕ Fin (2 ^ h) ⊕ Fixed (2 ^ h) → Bool) :
    elementDistinctness (2 ^ (h + 1)) (2 * (h + 1)) (f ∘ dyadicLayout h) =
      elementDistinctness (2 ^ h + 2 ^ h) (Nat.clog 2 (2 ^ h) + (h + 1) + 1) (f ∘ layout _ _) :=
  distinctness_reindex (m := 2 ^ (h + 1)) (n := 2 ^ h + 2 ^ h) (a := 2 * (h + 1))
    (b := Nat.clog 2 (2 ^ h) + (h + 1) + 1) (by rw [pow_succ]; ring)
    (by rw [Nat.clog_pow 2 h one_lt_two]; lia) (f ∘ layout _ _)

private def routingBitEquiv (h : ℕ) : Live (2 ^ h) h ≃ RoutingBit h where
  toFun
    | .inl (i, b) => .tag i (b.cast (Nat.clog_pow 2 h one_lt_two))
    | .inr (.inl (i, b)) => .input i b
    | .inr (.inr (i, b)) => .output i b
  invFun
    | .tag i b => .inl (i, b.cast (Nat.clog_pow 2 h one_lt_two).symm)
    | .input i b => .inr (.inl (i, b))
    | .output i b => .inr (.inr (i, b))
  left_inv := by rintro (⟨i, b⟩ | (⟨i, b⟩ | ⟨i, b⟩)) <;> rfl
  right_inv := by rintro (⟨i, b⟩ | ⟨i, b⟩ | ⟨i, b⟩) <;> rfl

/-- The three blocks of exterior wires have exactly the port count charged by the routing test. -/
public theorem card_routingBit (h : ℕ) : Fintype.card (RoutingBit h) = 3 * 2 ^ h * h := by
  rw [← Fintype.card_congr (routingBitEquiv h)]
  simp only [Live, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    Nat.clog_pow _ _ one_lt_two]
  ring

private theorem indexBits_pow (h : ℕ) (i : Fin (2 ^ h)) (b : Fin (Nat.clog 2 (2 ^ h))) :
    BitString.indexBits i b =
      (BitString.equivFin h).symm i (b.cast (Nat.clog_pow 2 h one_lt_two)) := by
  have castDigits {a c : ℕ} (e : a = c) (j : Fin (2 ^ c)) (k : Fin a) :
      (BitString.equivFin a).symm (j.cast (congrArg (2 ^ ·) e.symm)) k =
        (BitString.equivFin c).symm j (k.cast e) := by subst c; rfl
  exact castDigits (Nat.clog_pow _ _ one_lt_two) i b

private abbrev Hidden (h : ℕ) := Fin (2 ^ h) ⊕ Fixed (2 ^ h)

private abbrev EdBit (h : ℕ) := Fin (2 ^ (h + 1) * (2 * (h + 1)))

private def routeLayout (h : ℕ) : EdBit h ≃ RoutingBit h ⊕ Hidden h :=
  (dyadicLayout h).trans <| (routingBitEquiv h).sumCongr (Equiv.refl _)

open scoped Classical in
private theorem sum_routing (R : Type*) [CommRing R] (h : ℕ) (z : RoutingBit h → Bool) :
    (∑ hidden : Hidden h → Bool, (∏ i, unary (fixedBits (2 ^ h)) i (hidden i)) *
      (if elementDistinctness (2 ^ (h + 1)) (2 * (h + 1))
        (Sum.elim z hidden ∘ routeLayout h) then (1 : R) else 0)) =
      if TaggedPermutation z then 1 else 0 := by
  classical
  let dest (i : Fin (2 ^ h)) := BitString.equivFin h fun b => z (.tag i b)
  let x (i : Fin (2 ^ h)) (b : Fin h) := z (.input i b)
  let y (i : Fin (2 ^ h)) (b : Fin h) := z (.output i b)
  have hz : liveBits dest x y = z ∘ routingBitEquiv h := by
    funext p
    rcases p with ⟨i, b⟩ | (⟨i, b⟩ | ⟨i, b⟩)
    · simp [liveBits, dest, indexBits_pow, routingBitEquiv]
    · rfl
    · rfl
  have hwire (s : Hidden h → Bool) :
      Sum.elim z s ∘ routeLayout h = Sum.elim (liveBits dest x y) s ∘ dyadicLayout h := by
    rw [hz]
    funext q
    cases he : dyadicLayout h q with
    | inl i => simp [routeLayout, he]
    | inr i => simp [routeLayout, he]
  simp_rw [hwire, dyadic_eval]
  rw [sum_ed_generic]
  apply if_congr _ rfl rfl
  simp only [TaggedPermutation, dest, x, y, funext_iff]

open scoped Classical in
/-- A trivalent realization of a batch of exact-width distinctness tensors gives a trivalent
realization of the same number of tagged-permutation tensors, with the same vertices and
internal wires and no increase in volume. The source network may share work among lists. -/
public theorem exists_taggedPermutationNetwork {R V E : Type*} [CommRing R] [Fintype V] [Fintype E]
    [DecidableEq E] {t h : ℕ}
    (N : OpenBitNetwork R (Fin t × Fin (2 ^ (h + 1) * (2 * (h + 1)))) V E) (hN : N.Trivalent)
    (hED : ∀ z, N.contraction z = ∏ i : Fin t,
      if elementDistinctness (2 ^ (h + 1)) (2 * (h + 1)) (fun q => z (i, q)) then 1 else 0) :
    ∃ M : OpenBitNetwork R (Fin t × RoutingBit h) V E, M.toMultigraph = N.toMultigraph ∧
      M.Trivalent ∧ M.volume ≤ N.volume ∧
      ∀ z, M.contraction z =
        ∏ i : Fin t, if TaggedPermutation (fun q => z (i, q)) then 1 else 0 := by
  classical
  let table (a : EdBit h → Bool) :=
    if elementDistinctness (2 ^ (h + 1)) (2 * (h + 1)) a then (1 : R) else 0
  obtain ⟨M, hgraph, hM, hvol, hc⟩ := N.exists_tensorPower_cap hN (routeLayout h).symm
    (unary (fixedBits (2 ^ h))) table hED
  refine ⟨M, hgraph, hM, hvol, fun z => (hc z).trans <| Finset.prod_congr rfl fun i _ => ?_⟩
  refine Eq.trans (Finset.sum_congr ?_ (fun _ _ => rfl)) (sum_routing R h (fun j => z (i, j)))
  exact congrArg (fun inst => @Finset.univ _ inst) (Subsingleton.elim _ _)

open scoped Classical in
/-- A Boolean circuit testing distinctness of records of width `2 * (h + 2)` realizes the
complete tagged-permutation test at width `h` over any commutative ring. The cost counts all
gates and input bits in the given circuit, including inputs used more than once. -/
public theorem exists_routingNetwork_of_computes {σ : Signature} {m h : ℕ} (hm : 1 < m)
    (hwidth : Nat.clog 2 m = h + 2) (I : Interpretation σ Bool)
    (C : Circuit σ (m * (2 * Nat.clog 2 m)) 1) (hf : C.FanInAtMost 2)
    (hc : C.Computes I (single (elementDistinctness m (2 * Nat.clog 2 m))))
    (R : Type*) [CommRing R] :
    ∃ (V E : Type) (_ : Fintype V) (_ : Fintype E) (_ : DecidableEq E)
      (M : OpenBitNetwork R (RoutingBit h) V E), M.Trivalent ∧
        M.volume ≤ m * (2 * Nat.clog 2 m) + (3 * 2 ^ h * h) + 8 * C.size + 5 ∧
        ∀ z, M.contraction z = if TaggedPermutation z then 1 else 0 := by
  classical
  have hdy := exists_dyadic_network_of_computes hm I C hf hc R
  dsimp only at hdy
  rw [show Nat.clog 2 m - 1 = h + 1 by lia] at hdy
  obtain ⟨V, E, vT, eT, dE, N, hN, hvol, htable⟩ := hdy
  let weight : Hidden h → Bool → R := unary (fixedBits (2 ^ h))
  let M := N.cap (routeLayout h).symm weight
  refine ⟨V, E, vT, eT, dE, M, hN.cap _ _, ?_, fun z => ?_⟩
  · have hcost : M.volume + (2 ^ (h + 1) * (2 * (h + 1))) = N.volume + 3 * 2 ^ h * h := by
      simp only [OpenBitNetwork.volume, Nat.card_eq_fintype_card, Fintype.card_fin, card_routingBit]
      lia
    lia
  · simp only [M, OpenBitNetwork.contraction_cap, htable, Equiv.symm_symm]
    convert! sum_routing R h z using 2
    exact congrArg (fun inst => @Finset.univ _ inst) (Subsingleton.elim _ _)

end Cslib.Circuits.Boolean.ElementDistinctness
