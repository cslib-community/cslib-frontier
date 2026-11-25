/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.DecisionTree.Basic
public import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.Union
import CslibFrontier.Probability.StatisticalDistance.Coupling
import CslibFrontier.Probability.StatisticalDistance.Event
import Mathlib.Logic.Equiv.Fin.Rotate

/-!
# Separation between fixed and adaptive bit queries

Goldreich’s guideline assigns a separate data bit to each address, using `t - 1` extra bits.
The pointer test reads an address and checks a data bit selected by that address. A sampled
word with the selected bit forced always passes, while a uniform word passes one half of
the time. To achieve the printed length of Goldreich's Exercise 8.32(1), pair up selected
addresses into edges, with one edge in each direction of the cube, and let both addresses
of each pair select the same data bit. Force opposite values on the two sides. If a fixed
projection hides the coordinate of a paired edge, swapping its side with the selected data
bit gives an exactly uniform comparison law on that part. The remaining addresses that can
affect the projection charge at most one mismatch event per observed coordinate. A
conditional equality on four bits handles the three-query case.

## Main results

* `Cslib.DecisionTree.exists_dist_map_restrict_le_and_map_eval_eq_printed_length`: the printed
  separation on exactly `2 ^ (t - 1)` bits for every positive query budget `t`.

## References

* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, draft r4]
  [Goldreich2007DraftR4]
-/

public section

open Finset
open scoped BigOperators Cslib.Probability.PMF

namespace Cslib.DecisionTree

open Probability

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Under the uniform distribution, the subcube of a set `Q` of coordinates has probability
`2 ^ (-#Q)`. -/
private theorem toOuterMeasure_uniformOfFintype_cube (Q : Finset ι) (c : ι → Bool) :
    ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure {z | ∀ i ∈ Q, z i = c i}).toReal =
      ((2 : ℝ) ^ #Q)⁻¹ := by
  have hset : {z : ι → Bool | ∀ i ∈ Q, z i = c i} =
      Q.restrict ⁻¹' ({Q.restrict c} : Set (Q → Bool)) := by
    ext z
    simp [funext_iff, Finset.restrict]
  rw [hset, ← PMF.toOuterMeasure_map_apply, Probability.PMF.uniformOfFintype_pi_map_restrict,
    PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  simp

section Pointer

/-! ### The pointer distribution from the guideline to Exercise 8.32(1)

Positions are `m` index bits `Sum.inl j` and `2 ^ m` data bits `Sum.inr v`, one for each value
`v : Fin m → Bool` of the index bits. -/

variable {m : ℕ}

/-- The address of an input whose first block consists of the address bits. -/
private def address {D : Type*} (z : Fin m ⊕ D → Bool) : Fin m → Bool :=
  z ∘ Sum.inl

/-- The data position selected at the sampled address. -/
private def point {D : Type*} (key : (Fin m → Bool) → D) (z : Fin m ⊕ D → Bool) :
    Fin m ⊕ D :=
  .inr (key (address z))

private theorem address_update_point {D : Type*} [DecidableEq D]
    (key : (Fin m → Bool) → D) (z : Fin m ⊕ D → Bool) (v : Bool) :
    address (Function.update z (point key z) v) = address z := by
  funext j
  simp [address, point]

private theorem point_update {D : Type*} [DecidableEq D] (key : (Fin m → Bool) → D)
    (z : Fin m ⊕ D → Bool) (v : Bool) :
    point key (Function.update z (point key z) v) = point key z := by
  exact congrArg (fun a => Sum.inr (key a)) (address_update_point key z v)

/-- A single query checks a bit against a prescribed value. -/
private def checkBit {J : Type*} (i : J) (b : Bool) : DecisionTree J Bool :=
  node i (leaf (!b)) (leaf b)

private theorem eval_checkBit {J : Type*} (i : J) (b : Bool) (z : J → Bool) :
    (checkBit i b).eval z = decide (z i = b) := by
  cases h : z i <;> cases b <;> simp [checkBit, h]

/-- Read the address, then check that the selected bit equals the prescribed bit. -/
private def pointerTest {D : Type*} [DecidableEq D]
    (key : (Fin m → Bool) → D) (target : (Fin m → Bool) → Bool) :
    DecisionTree (Fin m ⊕ D) Bool :=
  graft ((List.finRange m).map Sum.inl)
    (fun a => checkBit (point key a) (target (address a))) fun _ => false

private theorem eval_pointerTest {D : Type*} [DecidableEq D] (key : (Fin m → Bool) → D)
    (target : (Fin m → Bool) → Bool) (z : Fin m ⊕ D → Bool) :
    (pointerTest key target).eval z = decide (z (point key z) = target (address z)) := by
  rw [pointerTest, eval_graft, eval_checkBit]
  simp only [point, address, Function.comp_def, List.mem_map, List.mem_finRange, true_and,
    exists_eq, reduceIte, Sum.inl.injEq]
  exact Bool.decide_congr Iff.rfl

private theorem depth_pointerTest {D : Type*} [DecidableEq D] (key : (Fin m → Bool) → D)
    (target : (Fin m → Bool) → Bool) :
    (pointerTest key target).depth ≤ m + 1 := by
  unfold pointerTest
  simpa using depth_graft_le ((List.finRange m).map Sum.inl)
    (fun a => checkBit (point key a) (target (address a)))
    (fun _ => false) (d := 1) fun _ => by simp [checkBit]

private theorem bind_checkBit_uniform (b : Bool) :
    ((PMF.uniformOfFintype Bool).bind fun v => PMF.pure (decide (v = b))) =
      PMF.uniformOfFintype Bool := by
  change (PMF.uniformOfFintype Bool).bind (PMF.pure ∘ fun v => decide (v = b)) = _
  rw [PMF.bind_pure_comp]
  cases b
  · exact Probability.PMF.uniformOfFintype_map_equiv (Function.Involutive.toPerm _ Bool.not_not)
  · exact PMF.map_id _

/-- When an adaptive check chooses its coordinate and value without reading that coordinate,
it accepts a uniform word half the time and accepts a word forced at the coordinate surely. -/
private theorem map_eval_forceBit {J : Type*} [Fintype J] [DecidableEq J]
    (p : (J → Bool) → J) (b : (J → Bool) → Bool) (T : DecisionTree J Bool)
    (hp : ∀ z v, p (Function.update z (p z) v) = p z)
    (hb : ∀ z v, b (Function.update z (p z) v) = b z)
    (heval : ∀ z, T.eval z = decide (z (p z) = b z)) :
    ((PMF.uniformOfFintype (J → Bool)).map
      (fun z => Function.update z (p z) (b z))).map T.eval = PMF.pure true ∧
      (PMF.uniformOfFintype (J → Bool)).map T.eval = PMF.uniformOfFintype Bool := by
  refine ⟨?_, ?_⟩
  · have h : T.eval ∘ (fun z => Function.update z (p z) (b z)) =
        Function.const _ true := by
      funext z
      simp [heval, hp, hb]
    rw [PMF.map_comp, h]
    simp
  · have h := Probability.PMF.uniformOfFintype_bind_bind_adaptiveUpdate p hp
      (fun z => PMF.pure (T.eval z))
    simp only [heval, hp, hb, Function.update_self, bind_checkBit_uniform, PMF.bind_const] at h
    rw [funext heval, ← PMF.bind_pure_comp]
    exact h.symm

private def forcePointer {D : Type*} [DecidableEq D] (key : (Fin m → Bool) → D)
    (target : (Fin m → Bool) → Bool) (z : Fin m ⊕ D → Bool) : Fin m ⊕ D → Bool :=
  Function.update z (point key z) (target (address z))

/-- The uniform distribution with the bit at its pointer set to the prescribed value. -/
private noncomputable def pointerLaw {D : Type*} [Fintype D] [DecidableEq D]
    (key : (Fin m → Bool) → D) (target : (Fin m → Bool) → Bool) :
    PMF (Fin m ⊕ D → Bool) :=
  (PMF.uniformOfFintype _).map (forcePointer key target)

private theorem map_eval_pointerTest {D : Type*} [Fintype D] [DecidableEq D]
    (key : (Fin m → Bool) → D) (target : (Fin m → Bool) → Bool) :
    (pointerLaw key target).map (pointerTest key target).eval = PMF.pure true ∧
      (PMF.uniformOfFintype (Fin m ⊕ D → Bool)).map (pointerTest key target).eval =
        PMF.uniformOfFintype Bool :=
  map_eval_forceBit (point key) (target ∘ address) _ (point_update key)
    (fun z v => congrArg target (address_update_point key z v)) (eval_pointerTest key target)

/-- Couple a transformed word to a uniform word through any permutation of the original
uniform input. -/
private theorem dist_restrict_map_uniform_le (S : Finset ι) (f : (ι → Bool) → (ι → Bool))
    (e : Equiv.Perm (ι → Bool)) :
    dist (((PMF.uniformOfFintype (ι → Bool)).map f).map S.restrict)
        (PMF.uniformOfFintype (S → Bool)) ≤
      ((PMF.uniformOfFintype (ι → Bool)).toOuterMeasure
        {z | (S.restrict ∘ f) z ≠ (S.restrict ∘ e) z}).toReal := by
  let U := PMF.uniformOfFintype (ι → Bool)
  have hunif : U.map (S.restrict ∘ e) = PMF.uniformOfFintype (S → Bool) := by
    rw [← PMF.map_comp, Probability.PMF.uniformOfFintype_map_equiv,
      Probability.PMF.uniformOfFintype_pi_map_restrict]
  rw [← hunif, PMF.map_comp]
  exact Probability.PMF.dist_map_map_le U _ _

/-- A uniform comparison permutation bounds the projection error when each possible
mismatch can be charged to a distinct visible coordinate. -/
private theorem dist_map_restrict_pointerLaw_le {D : Type*} [Fintype D] [DecidableEq D]
    (key : (Fin m → Bool) → D) (target : (Fin m → Bool) → Bool)
    (S : Finset (Fin m ⊕ D)) (compare : Equiv.Perm (Fin m ⊕ D → Bool))
    (charge : (Fin m → Bool) → Fin m ⊕ D) (hcharge : Function.Injective charge)
    (hbad : ∀ z, S.restrict (forcePointer key target z) ≠ S.restrict (compare z) →
      charge (address z) ∈ S ∧ z (point key z) ≠ target (address z)) :
    dist ((pointerLaw key target).map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤
      (#S : ℝ) / 2 ^ (m + 1) := by
  let U := PMF.uniformOfFintype (Fin m ⊕ D → Bool)
  refine (dist_restrict_map_uniform_le S (forcePointer key target) compare).trans ?_
  let A := univ.filter fun a => charge a ∈ S
  let B (a : Fin m → Bool) : Set (Fin m ⊕ D → Bool) :=
    {z | address z = a ∧ z (.inr (key a)) = !target a}
  have hA : #A ≤ #S := Finset.card_le_card_of_injOn charge
    (fun a ha => (mem_filter.mp ha).2) hcharge.injOn
  have hsub : {z | (S.restrict ∘ forcePointer key target) z ≠ (S.restrict ∘ compare) z} ⊆
      ⋃ a ∈ A, B a := fun z hz => by
    obtain ⟨hmem, hne⟩ := hbad z hz
    refine Set.mem_iUnion.mpr ⟨address z, Set.mem_iUnion.mpr ⟨mem_filter.mpr ⟨mem_univ _, hmem⟩,
      rfl, ?_⟩⟩
    change z (point key z) = !target (address z)
    cases hv : z (point key z) <;> cases ht : target (address z) <;> simp_all
  have hB (a : Fin m → Bool) : (U.toOuterMeasure (B a)).toReal = ((2 : ℝ) ^ (m + 1))⁻¹ := by
    let Q : Finset (Fin m ⊕ D) := insert (.inr (key a)) (univ.map ⟨Sum.inl, Sum.inl_injective⟩)
    have hBQ : B a = {z | ∀ i ∈ Q, z i = Sum.elim a (fun _ => !target a) i} := by
      ext z
      simp [B, Q, address, funext_iff, and_comm]
    rw [hBQ, toOuterMeasure_uniformOfFintype_cube, card_insert_of_notMem (by simp), card_map,
      card_univ, Fintype.card_fin]
  calc (U.toOuterMeasure
        {z | (S.restrict ∘ forcePointer key target) z ≠ (S.restrict ∘ compare) z}).toReal
      ≤ (U.toOuterMeasure (⋃ a ∈ A, B a)).toReal :=
        ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top _ _)
          (U.toOuterMeasure.mono hsub)
    _ ≤ ∑ a ∈ A, (U.toOuterMeasure (B a)).toReal :=
        Probability.PMF.toOuterMeasure_toReal_biUnion_finset_le U A B
    _ = (#A : ℝ) / 2 ^ (m + 1) := by
        simp only [hB, sum_const, nsmul_eq_mul, div_eq_mul_inv]
    _ ≤ (#S : ℝ) / 2 ^ (m + 1) := by gcongr

private theorem forcePointer_eq_on {D : Type*} [DecidableEq D]
    (key : (Fin m → Bool) → D) (target : (Fin m → Bool) → Bool)
    (S : Finset (Fin m ⊕ D)) (z : Fin m ⊕ D → Bool)
    (h : point key z ∈ S → z (point key z) = target (address z)) :
    S.restrict (forcePointer key target z) = S.restrict z := by
  ext i
  by_cases hi : (i : Fin m ⊕ D) = point key z
  · have hz := h (hi ▸ i.property)
    simp [Finset.restrict, forcePointer, hi, hz]
  · simp [Finset.restrict, forcePointer, Function.update_of_ne hi]

/-- A matching of address-cube edges with one edge in each coordinate direction. -/
private structure PointerMatching (m : ℕ) where
  lower : Fin m ↪ (Fin m → Bool)
  upper : Fin m ↪ (Fin m → Bool)
  lower_bit : ∀ i, lower i i = false
  upper_eq : ∀ i, upper i = Function.update (lower i) i true
  separated : ∀ i j, lower i ≠ upper j

namespace PointerMatching

private abbrev Keys (M : PointerMatching m) :=
  (univ \ univ.map M.upper : Finset (Fin m → Bool))

private theorem mem_keys (M : PointerMatching m) (a : Fin m → Bool) :
    a ∈ M.Keys ↔ ∀ i, a ≠ M.upper i := by
  simp [Keys, eq_comm]

private def lowerKey (M : PointerMatching m) (i : Fin m) : M.Keys :=
  ⟨M.lower i, (M.mem_keys _).2 (M.separated i)⟩

/-- Upper endpoints are bijective with directions, and the other addresses index the data
block. This also gives each address a distinct coordinate to charge for a mismatch. -/
private noncomputable def charge (M : PointerMatching m) :
    (Fin m → Bool) ≃ Fin m ⊕ M.Keys :=
  (Equiv.ofBijective (Sum.elim M.upper Subtype.val) (by
    constructor
    · intro a b h
      rcases a with i | ⟨a, ha⟩ <;> rcases b with j | ⟨b, hb⟩
      · exact congrArg Sum.inl (M.upper.injective h)
      · exact ((M.mem_keys b).1 hb i h.symm).elim
      · exact ((M.mem_keys a).1 ha j h).elim
      · exact congrArg Sum.inr (Subtype.ext h)
    · intro a
      by_cases h : ∃ i, a = M.upper i
      · obtain ⟨i, rfl⟩ := h
        exact ⟨.inl i, rfl⟩
      · exact ⟨.inr ⟨a, (M.mem_keys a).2 fun i hi => h ⟨i, hi⟩⟩, rfl⟩)).symm

private theorem charge_upper (M : PointerMatching m) (i : Fin m) :
    M.charge (M.upper i) = .inl i :=
  M.charge.apply_symm_apply (.inl i)

private theorem charge_of_mem (M : PointerMatching m) {a : Fin m → Bool} (ha : a ∈ M.Keys) :
    M.charge a = .inr ⟨a, ha⟩ :=
  M.charge.apply_symm_apply (.inr ⟨a, ha⟩)

/-- Every address in an edge selects the lower endpoint as its data-bit index. Other addresses
select themselves. -/
private noncomputable def key (M : PointerMatching m) (a : Fin m → Bool) : M.Keys :=
  (M.charge a).elim M.lowerKey id

private theorem key_of_mem (M : PointerMatching m) {a : Fin m → Bool} (ha : a ∈ M.Keys) :
    M.key a = ⟨a, ha⟩ := by
  rw [key, M.charge_of_mem ha]
  rfl

private theorem key_upper (M : PointerMatching m) (i : Fin m) :
    M.key (M.upper i) = M.lowerKey i := by
  rw [key, M.charge_upper]
  rfl

private theorem key_lower (M : PointerMatching m) (i : Fin m) :
    M.key (M.lower i) = M.lowerKey i :=
  M.key_of_mem (M.lowerKey i).property

/-- Force zero on singleton addresses and lower endpoints, and one on upper endpoints. -/
private noncomputable def target (M : PointerMatching m) (a : Fin m → Bool) : Bool :=
  (M.charge a).isLeft

private def endpoint (M : PointerMatching m) (i : Fin m) (side : Bool) : Fin m → Bool :=
  if side then M.upper i else M.lower i

private theorem key_endpoint (M : PointerMatching m) (i : Fin m) (side : Bool) :
    M.key (M.endpoint i side) = M.lowerKey i := by
  cases side <;> simp [endpoint, M.key_lower, M.key_upper]

private theorem target_endpoint (M : PointerMatching m) (i : Fin m) (side : Bool) :
    M.target (M.endpoint i side) = side := by
  cases side
  · exact congrArg Sum.isLeft (M.charge_of_mem (a := M.lower i) (M.lowerKey i).property)
  · exact congrArg Sum.isLeft (M.charge_upper i)

private theorem endpoint_bit (M : PointerMatching m) (i : Fin m) (side : Bool) :
    M.endpoint i side i = side := by
  cases side
  · exact M.lower_bit i
  · simp [endpoint, M.upper_eq]

private theorem endpoint_other (M : PointerMatching m) (i : Fin m) (s t : Bool)
    {j : Fin m} (hj : j ≠ i) : M.endpoint i s j = M.endpoint i t j := by
  cases s <;> cases t <;> simp [endpoint, M.upper_eq, Function.update_of_ne hj]

private theorem edge_unique (M : PointerMatching m) {i j : Fin m} {s t : Bool}
    (h : M.endpoint i s = M.endpoint j t) : i = j := by
  have hk := congrArg M.key h
  rw [M.key_endpoint, M.key_endpoint] at hk
  exact M.lower.injective (congrArg Subtype.val hk)

/-- On one edge, exchange its side bit with the selected data bit. -/
private def swapWord (M : PointerMatching m) (i : Fin m) (z : Fin m ⊕ M.Keys → Bool) :
    Fin m ⊕ M.Keys → Bool :=
  Sum.elim (M.endpoint i (z (.inr (M.lowerKey i))))
    (Function.update (z ∘ Sum.inr) (M.lowerKey i) (address z i))

private theorem address_swapWord (M : PointerMatching m) (i : Fin m)
    (z : Fin m ⊕ M.Keys → Bool) :
    address (M.swapWord i z) = M.endpoint i (z (.inr (M.lowerKey i))) :=
  rfl

private theorem swapWord_swapWord (M : PointerMatching m) (i : Fin m) (s : Bool)
    (z : Fin m ⊕ M.Keys → Bool) (hz : address z = M.endpoint i s) :
    M.swapWord i (M.swapWord i z) = z := by
  have hs : address z i = s := by rw [hz, M.endpoint_bit]
  funext j
  cases j with
  | inl j =>
    change M.endpoint i (Function.update (z ∘ Sum.inr) (M.lowerKey i) (address z i)
      (M.lowerKey i)) j = address z j
    simp only [Function.update_self, hs, hz]
  | inr j =>
    change Function.update (Function.update (z ∘ Sum.inr) (M.lowerKey i) (address z i))
      (M.lowerKey i) (address (M.swapWord i z) i) j = (z ∘ Sum.inr) j
    rw [M.address_swapWord, M.endpoint_bit, Function.update_idem]
    exact congrFun (Function.update_eq_self _ _) j

private theorem restrict_force_eq_swapWord (M : PointerMatching m) (S : Finset (Fin m ⊕ M.Keys))
    (i : Fin m) (s : Bool) (z : Fin m ⊕ M.Keys → Bool) (hz : address z = M.endpoint i s)
    (hi : Sum.inl i ∉ S) :
    S.restrict (forcePointer M.key M.target z) = S.restrict (M.swapWord i z) := by
  have hs : address z i = s := by rw [hz, M.endpoint_bit]
  have hpoint : point M.key z = .inr (M.lowerKey i) := by rw [point, hz, M.key_endpoint]
  have htarget : M.target (address z) = s := by rw [hz, M.target_endpoint]
  funext ⟨j, hj⟩
  cases j with
  | inl j =>
    change Function.update z (point M.key z) (M.target (address z)) (.inl j) =
      M.endpoint i (z (.inr (M.lowerKey i))) j
    rw [hpoint, Function.update_of_ne (by simp)]
    change address z j = _
    rw [hz]
    exact M.endpoint_other i _ _ (fun h => hi (h ▸ hj))
  | inr j =>
    change Function.update z (point M.key z) (M.target (address z)) (.inr j) =
      Function.update (z ∘ Sum.inr) (M.lowerKey i) (address z i) j
    rw [hpoint, htarget, hs]
    by_cases h : j = M.lowerKey i
    · simp [h]
    · simp [Function.update_of_ne h, Function.update_of_ne (Sum.inr_injective.ne h)]

/-- Perform the exchange precisely on edges whose direction is hidden by the projection. -/
private noncomputable def compareWord (M : PointerMatching m) (S : Finset (Fin m ⊕ M.Keys))
    (z : Fin m ⊕ M.Keys → Bool) : Fin m ⊕ M.Keys → Bool := by
  classical
  exact if h : ∃ i, ∃ s, address z = M.endpoint i s ∧ Sum.inl i ∉ S then
    M.swapWord h.choose z
    else z

private theorem compareWord_of_hidden (M : PointerMatching m) {S : Finset (Fin m ⊕ M.Keys)}
    {z : Fin m ⊕ M.Keys → Bool} {i : Fin m} {s : Bool} (hz : address z = M.endpoint i s)
    (hi : Sum.inl i ∉ S) :
    M.compareWord S z = M.swapWord i z := by
  classical
  have h : ∃ j, ∃ t, address z = M.endpoint j t ∧ Sum.inl j ∉ S := ⟨i, s, hz, hi⟩
  obtain ⟨t, ht, _⟩ := h.choose_spec
  rw [compareWord, dite_eq_left h, M.edge_unique (ht.symm.trans hz)]

private theorem compareWord_involutive (M : PointerMatching m) (S : Finset (Fin m ⊕ M.Keys)) :
    Function.Involutive (M.compareWord S) := by
  classical
  intro z
  by_cases h : ∃ i, ∃ s, address z = M.endpoint i s ∧ Sum.inl i ∉ S
  · obtain ⟨i, s, hz, hi⟩ := h
    rw [M.compareWord_of_hidden hz hi,
      M.compareWord_of_hidden (M.address_swapWord i z) hi, M.swapWord_swapWord i s z hz]
  · have hfix : M.compareWord S z = z := by rw [compareWord, dite_eq_right h]
    rw [hfix, hfix]

private theorem dist_map_restrict_le (M : PointerMatching m) (S : Finset (Fin m ⊕ M.Keys)) :
    dist ((pointerLaw M.key M.target).map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤
      (#S : ℝ) / 2 ^ (m + 1) := by
  classical
  refine dist_map_restrict_pointerLaw_le _ _ S (M.compareWord_involutive S).toPerm M.charge
    M.charge.injective fun z hz => ?_
  change S.restrict (forcePointer M.key M.target z) ≠ S.restrict (M.compareWord S z) at hz
  have hhidden : ¬ ∃ i, ∃ s, address z = M.endpoint i s ∧ Sum.inl i ∉ S := fun ⟨i, s, ha, hi⟩ =>
    hz (M.compareWord_of_hidden ha hi ▸ M.restrict_force_eq_swapWord S i s z ha hi)
  rw [show M.compareWord S z = z by rw [compareWord, dite_eq_right hhidden]] at hz
  obtain ⟨hmem, hne⟩ : point M.key z ∈ S ∧ z (point M.key z) ≠ M.target (address z) :=
    not_imp.mp fun h => hz (forcePointer_eq_on M.key M.target S z h)
  refine ⟨?_, hne⟩
  by_cases h : ∃ i, address z = M.upper i
  · obtain ⟨i, hi⟩ := h
    rw [hi, M.charge_upper]
    by_contra hm
    exact hhidden ⟨i, true, hi, hm⟩
  · have ha : address z ∈ M.Keys := (M.mem_keys _).2 fun i hi => h ⟨i, hi⟩
    rwa [M.charge_of_mem ha, ← M.key_of_mem ha]

private def empty : PointerMatching 0 where
  lower := ⟨Fin.elim0, fun i => i.elim0⟩
  upper := ⟨Fin.elim0, fun i => i.elim0⟩
  lower_bit := fun i => i.elim0
  upper_eq := fun i => i.elim0
  separated := fun i => i.elim0

private def one : PointerMatching 1 where
  lower := ⟨fun _ _ => false, fun _ _ _ => Subsingleton.elim _ _⟩
  upper := ⟨fun _ _ => true, fun _ _ _ => Subsingleton.elim _ _⟩
  lower_bit := fun _ => rfl
  upper_eq := fun i => by
    funext j
    rw [Subsingleton.elim j i]
    exact (Function.update_self i true (fun _ => false)).symm
  separated := fun i j h => Bool.false_ne_true (congrFun h i)

/-- The cyclic edges have lower endpoint at the successor unit vector. They add their own
coordinate at the upper endpoint. Two distinct edges could share an upper endpoint only if
cyclic successor had a two-cycle. -/
private def cyclic (k : ℕ) : PointerMatching (k + 3) := by
  let σ := finRotate (k + 3)
  have hσ (i : Fin (k + 3)) : (σ i).val = if i.val = k + 2 then 0 else i.val + 1 := by
    simpa only [Fin.ext_iff, Fin.val_last] using (coe_finRotate (n := k + 2) i)
  have hsingle (i : Fin (k + 3)) : σ i ≠ i := by
    intro hi
    have h := congrArg Fin.val hi
    rw [hσ] at h
    split at h <;> omega
  have hdouble (i : Fin (k + 3)) : σ (σ i) ≠ i := by
    intro hi
    have h := congrArg Fin.val hi
    have hh := hσ i
    rw [hσ] at h
    split at hh <;> split at h <;> omega
  let lo (i j : Fin (k + 3)) := decide (j = σ i)
  let hi (i j : Fin (k + 3)) := decide (j = i ∨ j = σ i)
  refine ⟨⟨lo, ?_⟩, ⟨hi, ?_⟩, ?_, ?_, ?_⟩
  · intro i j h
    apply σ.injective
    apply of_decide_eq_true
    change lo j (σ i) = true
    rw [← congrFun h (σ i)]
    exact decide_eq_true rfl
  · intro i j h
    have hh (x) (hx : x = i ∨ x = σ i) : x = j ∨ x = σ j := by
      apply of_decide_eq_true
      change hi j x = true
      rw [← congrFun h x]
      exact decide_eq_true hx
    have h₁ := hh i (Or.inl rfl)
    have h₂ := hh (σ i) (Or.inr rfl)
    rcases h₁ with rfl | h₁
    · rfl
    rcases h₂ with h₂ | h₂
    · exact (hdouble j (h₁ ▸ h₂)).elim
    · exact σ.injective h₂
  · intro i
    change lo i i = false
    exact decide_eq_false (Ne.symm (hsingle i))
  · intro i
    change hi i = Function.update (lo i) i true
    funext j
    by_cases hij : j = i
    · simp [hij, hi]
    · simp [hi, lo, hij]
  · intro i j h
    change lo i = hi j at h
    have hh (x) (hx : x = j ∨ x = σ j) : x = σ i := by
      apply of_decide_eq_true
      change lo i x = true
      rw [congrFun h x]
      exact decide_eq_true hx
    exact hsingle j ((hh (σ j) (Or.inr rfl)).trans (hh j (Or.inl rfl)).symm)

private theorem card_positions (M : PointerMatching m) :
    Fintype.card (Fin m ⊕ M.Keys) = 2 ^ m := by
  simpa using Fintype.card_congr M.charge.symm

end PointerMatching

/-- The marginal and adaptive behavior needed by the separation, at a given set of positions. -/
private abbrev HasSeparation (ι : Type*) [Fintype ι] [DecidableEq ι] (t : ℕ) : Prop :=
  ∃ X : PMF (ι → Bool),
    (∀ S : Finset ι, #S = t →
      dist (X.map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤ t / 2 ^ t) ∧
    ∃ T : DecisionTree ι Bool, T.depth ≤ t ∧ X.map T.eval = PMF.pure true ∧
      (PMF.uniformOfFintype _).map T.eval = PMF.uniformOfFintype Bool

private theorem HasSeparation.relabel {κ : Type*} [Fintype κ] [DecidableEq κ] {t : ℕ}
    (h : HasSeparation ι t) (e : ι ≃ κ) : HasSeparation κ t := by
  obtain ⟨X, hX, T, hT, hp, hu⟩ := h
  let P := e.arrowCongr (Equiv.refl Bool)
  have he : (T.mapQueries e).eval ∘ P = T.eval := funext fun z => by
    rw [Function.comp_apply, eval_mapQueries]
    exact congrArg T.eval (funext fun i => congrArg z (e.symm_apply_apply i))
  refine ⟨X.map P, fun S hS => ?_, T.mapQueries e, by simpa,
    by rw [PMF.map_comp, he, hp],
    by rw [← Probability.PMF.uniformOfFintype_map_equiv P, PMF.map_comp, he, hu]⟩
  let R := S.map e.symm.toEmbedding
  let Q := (S.equivMap e.symm.toEmbedding).symm.arrowCongr (Equiv.refl Bool)
  rw [PMF.map_comp, show S.restrict ∘ P = Q ∘ R.restrict from rfl, ← PMF.map_comp,
    ← Probability.PMF.uniformOfFintype_map_equiv Q]
  exact (Probability.PMF.dist_map_le _ _ _).trans (hX R (by simpa [R] using hS))

private theorem PointerMatching.hasSeparation (M : PointerMatching m) :
    HasSeparation (Fin (2 ^ m)) (m + 1) := by
  have h : HasSeparation (Fin m ⊕ M.Keys) (m + 1) := by
    refine ⟨pointerLaw M.key M.target, ?_, pointerTest M.key M.target, depth_pointerTest _ _,
      map_eval_pointerTest _ _⟩
    intro S hS
    simpa only [hS] using M.dist_map_restrict_le S
  exact h.relabel (Fintype.equivOfCardEq (by rw [M.card_positions, Fintype.card_fin]))

/-- The three-query case uses one selector and checks that bit 1 equals the selected bit. -/
private def fourTarget (z : Fin 4 → Bool) : Bool := if z 0 then z 2 else z 3

private def fourForce (z : Fin 4 → Bool) : Fin 4 → Bool := Function.update z 1 (fourTarget z)

private def checkSelected (i : Fin 4) : DecisionTree (Fin 4) Bool :=
  node i (checkBit 1 false) (checkBit 1 true)

private def fourTest : DecisionTree (Fin 4) Bool :=
  node 0 (checkSelected 3) (checkSelected 2)

private theorem eval_fourTest (z : Fin 4 → Bool) :
    fourTest.eval z = decide (z 1 = fourTarget z) := by
  cases ha : z 0 <;> cases hc : z 2 <;> cases hd : z 3 <;>
    simp [fourTest, checkSelected, eval_checkBit, fourTarget, ha, hc, hd]

private theorem fourTarget_update (z : Fin 4 → Bool) (v : Bool) :
    fourTarget (Function.update z 1 v) = fourTarget z := by
  unfold fourTarget
  rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide),
    Function.update_of_ne (by decide)]

private theorem map_eval_fourTest :
    ((PMF.uniformOfFintype (Fin 4 → Bool)).map fourForce).map fourTest.eval = PMF.pure true ∧
      (PMF.uniformOfFintype (Fin 4 → Bool)).map fourTest.eval = PMF.uniformOfFintype Bool :=
  map_eval_forceBit (fun _ => 1) fourTarget fourTest (fun _ _ => rfl)
    fourTarget_update eval_fourTest

/-- Uniform comparison when coordinate `i` is hidden. With the selector missing and the two
possible values distinct, exchange the selector and comparison bit, adjusting the side labels.
With one possible value missing, exchange that value and the comparison bit only when selected. -/
private def fourCompare (i : Fin 4) (z : Fin 4 → Bool) : Fin 4 → Bool :=
  if i = 0 ∧ z 2 ≠ z 3 then
    Function.update (Function.update z 0 (decide (z 1 = z 2))) 1 (fourTarget z)
  else if (i = 2 ∧ z 0 = true) ∨ (i = 3 ∧ z 0 = false) then
    Function.update (Function.update z i (z 1)) 1 (z i)
  else z

private theorem fourCompare_involutive : ∀ i : Fin 4, Function.Involutive (fourCompare i) := by
  change ∀ (i : Fin 4) (z : Fin 4 → Bool), fourCompare i (fourCompare i z) = z
  decide

private theorem fourMismatch_card : ∀ i : Fin 4,
    #(univ.filter fun z : Fin 4 → Bool => ∃ j : Fin 4, j ≠ i ∧
      fourForce z j ≠ fourCompare i z j) ≤ 4 := by
  decide

private theorem four_hasSeparation : HasSeparation (Fin 4) 3 := by
  let U := PMF.uniformOfFintype (Fin 4 → Bool)
  refine ⟨U.map fourForce, fun S hS => ?_, fourTest, by decide, map_eval_fourTest⟩
  obtain ⟨i, _, hi⟩ := exists_mem_notMem_of_card_lt_card
    (show #S < #(univ : Finset (Fin 4)) by simp [hS])
  let e := (fourCompare_involutive i).toPerm
  let E : Set (Fin 4 → Bool) := {z | ∃ j : Fin 4, j ≠ i ∧ fourForce z j ≠ fourCompare i z j}
  have hsub : {z | (S.restrict ∘ fourForce) z ≠ (S.restrict ∘ e) z} ⊆ E := fun z hz => by
    by_contra h
    exact hz (funext fun j => by_contra fun hne => h ⟨j, fun hji => hi (hji ▸ j.property), hne⟩)
  refine (dist_restrict_map_uniform_le S fourForce e).trans
    ((ENNReal.toReal_mono (Probability.PMF.toOuterMeasure_ne_top U E)
      (U.toOuterMeasure.mono hsub)).trans ?_)
  rw [Probability.PMF.toOuterMeasure_uniformOfFintype_toReal,
    show Fintype.card (Fin 4 → Bool) = 16 by simp]
  exact (div_le_div_of_nonneg_right (by exact_mod_cast fourMismatch_card i : _ ≤ (4 : ℝ))
    (by norm_num)).trans (by norm_num)

/-- **Goldreich's separation at the printed length.**
[Goldreich, Exercise 8.32(1)][Goldreich2007DraftR4] (March 2007, printed pp. 377–378).
For every positive query budget `t`, there is a law on exactly `2 ^ (t - 1)` bits whose
marginal on every `t` coordinates is within `t / 2 ^ t` of uniform. A decision tree of depth
at most `t` accepts that law surely and accepts uniform input with probability one half.

For `t - 1 ≥ 3`, one data bit is shared by the endpoints of each edge of a matching in the
address cube whose edges use every direction exactly once. Opposite prescriptions at a shared
bit cancel whenever that direction is unobserved. The four-bit case uses a selector and a
conditional equality. -/
theorem exists_dist_map_restrict_le_and_map_eval_eq_printed_length (t : ℕ) (ht : 1 ≤ t) :
    ∃ X : PMF (Fin (2 ^ (t - 1)) → Bool),
      (∀ S : Finset (Fin (2 ^ (t - 1))), #S = t →
        dist (X.map S.restrict) (PMF.uniformOfFintype (S → Bool)) ≤ t / 2 ^ t) ∧
      ∃ T : DecisionTree (Fin (2 ^ (t - 1))) Bool, T.depth ≤ t ∧
        X.map T.eval = PMF.pure true ∧
        (PMF.uniformOfFintype _).map T.eval = PMF.uniformOfFintype Bool := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' ht
  rw [Nat.add_sub_cancel_right]
  change HasSeparation (Fin (2 ^ m)) (m + 1)
  match m with
  | 0 => exact PointerMatching.empty.hasSeparation
  | 1 => exact PointerMatching.one.hasSeparation
  | 2 => exact four_hasSeparation
  | k + 3 => exact (PointerMatching.cyclic k).hasSeparation

end Pointer

end Cslib.DecisionTree
