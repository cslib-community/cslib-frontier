/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Combinatorics.RectangleFreeMatrix
public import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Rectifier circuits (`OR`-circuits) and Nechiporuk's rectangle-free lower bound

A *rectifier `(α, β)`-circuit* (or *`OR`-circuit*, [Lupanov1956]; [JuknaSergeev2013];
[Sergeev2014ORComplement], p. 1) on a vertex type `V` is a directed graph with distinct input poles
`inp : β ↪ V` and output poles `out : α ↪ V` (`Disjoint (Set.range inp) (Set.range out)`). It
*computes* (implements) a Boolean matrix `A : Matrix α β Bool` when `A i j = true` iff there is a
directed walk from `inp j` to `out i`. Its *size* (complexity) is `#edges`, and it has *depth at
most `d`* (`HasDepthLE d`) when every directed walk in it has length at most `d` (which in
particular forces acyclicity).

For finite row and column types, `orComplexity A` (`OR(A) : ℕ`) is the minimum size of a finite
rectifier circuit computing `A`, and
`orDepthComplexity d A` (`OR_d(A) : ℕ∞`) is the minimum size over circuits of depth at most `d`
(`⊤` at `d = 0` when `A` has a `true` entry).

For `K`-rectangle-free matrices `A`, **Nechiporuk's theorem** ([JuknaSergeev2013], §3.3,
Theorem 3.9, pp. 32–33, taking both rectangle parameters `k, l` to be `K - 1`; [Nechiporuk1970];
[Sergeev2014ORComplement], p. 3 quotes the weaker denominator `K ^ 2` while p. 1 records the
`2`-free consequence) charges each `true` entry `(i, j)` of `A` via Pippenger's threshold-edge
argument to an edge along a walk from `inp j` to `out i` that covers at most `(K - 1) ^ 2`
input-output pairs, yielding `boolMatrixWeight A ≤ (K - 1) ^ 2 * C.size`
(`RectifierCircuit.Computes.boolMatrixWeight_le_sq_pred_mul_size`) and
`boolMatrixWeight A ≤ (K - 1) ^ 2 * orComplexity A`
(`boolMatrixWeight_le_sq_pred_mul_orComplexity`). At `K = 2` this matches the trivial depth-`1`
circuit (`RectifierCircuit.direct`), giving the exact identity `orComplexity A = boolMatrixWeight A`
and `orDepthComplexity d A = boolMatrixWeight A` (`1 ≤ d`) for every `2`-free Boolean matrix `A`.

## Main definitions

* `Cslib.Circuits.RectifierCircuit`: directed graph with disjoint injective input and output poles.
* `Cslib.Circuits.RectifierCircuit.Walk`, `Walk.length`, `Walk.append`, `Walk.uncons`: directed
  walks in a rectifier circuit.
* `Cslib.Circuits.RectifierCircuit.size`, `RectifierCircuit.HasDepthLE`,
  `RectifierCircuit.Computes`: edge count, bounded walk depth, and Boolean matrix implementation.
* `Cslib.Circuits.RectifierCircuit.direct`: canonical depth-`1` rectifier circuit of size
  `boolMatrixWeight A`.
* `Cslib.Circuits.orComplexity`, `Cslib.Circuits.orDepthComplexity`: `OR(A)` and `OR_d(A)`.

## Main results

* `Cslib.Circuits.le_orComplexity`, `Cslib.Circuits.le_orDepthComplexity`,
  `Cslib.Circuits.orDepthComplexity_zero_eq_top`: lower-bound introduction rules and the `d = 0`
  `⊤` boundary for nonzero matrices.
* `Cslib.Circuits.orComplexity_le_orDepthComplexity`, `Cslib.Circuits.orDepthComplexity_anti`,
  `Cslib.Circuits.orDepthComplexity_one_le_boolMatrixWeight`,
  `Cslib.Circuits.orComplexity_le_boolMatrixWeight`: monotonicity and depth-`1` upper bounds.
* `Cslib.Circuits.orComplexity_reindex`, `Cslib.Circuits.orDepthComplexity_reindex`: invariance
  under row and column permutations.
* `Cslib.Circuits.RectifierCircuit.Computes.boolMatrixWeight_le_sq_pred_mul_size`,
  `Cslib.Circuits.boolMatrixWeight_le_sq_pred_mul_orComplexity`: Nechiporuk's `K`-free rectifier
  lower bound `|A| ≤ (K - 1) ^ 2 * OR(A)`.
* `Cslib.Circuits.orComplexity_eq_boolMatrixWeight_of_isRectangleFree_two`,
  `Cslib.Circuits.orDepthComplexity_eq_boolMatrixWeight_of_isRectangleFree_two`: for `2`-free `A`,
  `OR(A) = OR_d(A) = |A|` (`1 ≤ d`).

## References

* [O. B. Lupanov, *On rectifier and switching-and-rectifier schemes*][Lupanov1956]
* [E. I. Nechiporuk, *On the topological principles of self-correction*][Nechiporuk1970]
* [S. Jukna, I. Sergeev, *Complexity of linear Boolean operators*][JuknaSergeev2013], §3.3,
  Theorem 3.9, pp. 32–33
* [I. S. Sergeev, *On relative OR-complexity of Boolean matrices and their
  complements*][Sergeev2014ORComplement], pp. 1, 3
-/

public section

namespace Cslib.Circuits

open Finset Function

variable {α β α' β' V V' : Type*}

/-- A *rectifier `(α, β)`-circuit* (`OR`-circuit) on vertex type `V`: a finite edge set with
injective input poles `inp : β ↪ V` and output poles `out : α ↪ V` having disjoint ranges
([Sergeev2014ORComplement], p. 1; [JuknaSergeev2013]). -/
structure RectifierCircuit (α β V : Type*) where
  /-- Directed edges `(u, w)` from `u` to `w`. -/
  edges : Finset (V × V)
  /-- Input pole labeling. -/
  inp : β ↪ V
  /-- Output pole labeling. -/
  out : α ↪ V
  /-- Input poles and output poles are distinct vertices. -/
  disjoint_poles : Disjoint (Set.range inp) (Set.range out)

namespace RectifierCircuit

/-- Directed walks along the edges of a rectifier circuit `C`. -/
inductive Walk (C : RectifierCircuit α β V) : V → V → Type _ where
  /-- The zero-edge walk at `u`. -/
  | nil (u : V) : C.Walk u u
  /-- Prepend a directed edge `(u, v) ∈ C.edges` to a walk from `v` to `w`. -/
  | cons {u v w : V} (h : (u, v) ∈ C.edges) (p : C.Walk v w) : C.Walk u w

namespace Walk

/-- Number of edges in a directed walk. -/
@[expose] def length {C : RectifierCircuit α β V} {u v : V} : C.Walk u v → ℕ
  | .nil _ => 0
  | .cons _ p => p.length + 1

@[simp] theorem length_nil {C : RectifierCircuit α β V} (u : V) :
    (Walk.nil (C := C) u).length = 0 :=
  rfl

@[simp] theorem length_cons {C : RectifierCircuit α β V} {u v w : V}
    (h : (u, v) ∈ C.edges) (p : C.Walk v w) : (Walk.cons h p).length = p.length + 1 :=
  rfl

/-- Concatenate two directed walks sharing an intermediate endpoint. -/
@[expose] def append {C : RectifierCircuit α β V} {u v w : V} :
    C.Walk u v → C.Walk v w → C.Walk u w
  | .nil _, q => q
  | .cons h p, q => .cons h (p.append q)

end Walk

/-- Complexity (number of edges) of a rectifier circuit ([Sergeev2014ORComplement], p. 1). -/
@[expose] def size (C : RectifierCircuit α β V) : ℕ :=
  #C.edges

/-- `C` has *depth at most `d`* if every directed walk in `C` has length at most `d`
([Sergeev2014ORComplement], p. 1). -/
@[expose] def HasDepthLE (C : RectifierCircuit α β V) (d : ℕ) : Prop :=
  ∀ ⦃u v : V⦄ (p : C.Walk u v), p.length ≤ d

theorem HasDepthLE.mono {C : RectifierCircuit α β V} {d₁ d₂ : ℕ}
    (h : C.HasDepthLE d₁) (hd : d₁ ≤ d₂) : C.HasDepthLE d₂ :=
  fun _ _ p => (h p).trans hd

/-- If a natural-number layer strictly advances by `1` on every edge and never exceeds `d`, then
the circuit has depth at most `d`. -/
theorem hasDepthLE_of_layer {C : RectifierCircuit α β V} {d : ℕ} (layer : V → ℕ)
    (hstep : ∀ ⦃u v : V⦄, (u, v) ∈ C.edges → layer v = layer u + 1)
    (htop : ∀ v : V, layer v ≤ d) : C.HasDepthLE d := by
  have hwalk {u v : V} (p : C.Walk u v) : layer v = layer u + p.length := by
    induction p with
    | nil _ => simp only [Walk.length_nil, add_zero]
    | cons h p ih =>
      rw [Walk.length_cons, ih, hstep h]
      omega
  intro u v p
  have hv := htop v
  have heq := hwalk p
  omega

/-- `C` *computes* (implements) `A : Matrix α β Bool` if `A i j = true` iff there is a directed walk
from `inp j` to `out i` ([Sergeev2014ORComplement], p. 1). -/
@[expose] def Computes (C : RectifierCircuit α β V) (A : Matrix α β Bool) : Prop :=
  ∀ (i : α) (j : β), A i j = true ↔ Nonempty (C.Walk (C.inp j) (C.out i))

theorem inp_ne_out (C : RectifierCircuit α β V) (j : β) (i : α) : C.inp j ≠ C.out i :=
  Set.disjoint_iff_forall_ne.mp C.disjoint_poles ⟨j, rfl⟩ ⟨i, rfl⟩

/-- Reindex the vertex type of a rectifier circuit along an equivalence `e : V ≃ V'`. -/
def reindexVertices (C : RectifierCircuit α β V) (e : V ≃ V') : RectifierCircuit α β V' where
  edges := C.edges.map (Equiv.prodCongr e e).toEmbedding
  inp := C.inp.trans e.toEmbedding
  out := C.out.trans e.toEmbedding
  disjoint_poles := by
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ h
    exact C.inp_ne_out j i (e.injective h)

@[simp] theorem size_reindexVertices (C : RectifierCircuit α β V) (e : V ≃ V') :
    (C.reindexVertices e).size = C.size :=
  card_map _

private def Walk.mapEquiv {C : RectifierCircuit α β V} (e : V ≃ V') {u v : V} :
    C.Walk u v → (C.reindexVertices e).Walk (e u) (e v)
  | .nil u => .nil (e u)
  | .cons h p => .cons (mem_map.mpr ⟨_, h, rfl⟩) (p.mapEquiv e)

private def Walk.unmapEquiv {C : RectifierCircuit α β V} (e : V ≃ V') {u' v' : V'} :
    (C.reindexVertices e).Walk u' v' → C.Walk (e.symm u') (e.symm v')
  | .nil u' => .nil (e.symm u')
  | @Walk.cons _ _ _ _ u' v' _ h p =>
      have he : (e.symm u', e.symm v') ∈ C.edges := by
        obtain ⟨⟨a, b⟩, hab, heq⟩ := mem_map.mp h
        simp only [Equiv.coe_toEmbedding, Equiv.prodCongr_apply, Prod.map_apply,
          Prod.mk.injEq] at heq
        rw [← heq.1, ← heq.2, e.symm_apply_apply, e.symm_apply_apply]
        exact hab
      .cons he (p.unmapEquiv e)

private theorem Walk.length_unmapEquiv {C : RectifierCircuit α β V} (e : V ≃ V') {u' v' : V'} :
    (p : (C.reindexVertices e).Walk u' v') → (p.unmapEquiv e).length = p.length
  | .nil _ => rfl
  | .cons _ p => congrArg (· + 1) (p.length_unmapEquiv e)

theorem Computes.reindexVertices {C : RectifierCircuit α β V} {A : Matrix α β Bool}
    (hC : C.Computes A) (e : V ≃ V') : (C.reindexVertices e).Computes A := by
  intro i j
  rw [hC i j]
  refine ⟨fun ⟨p⟩ => ⟨p.mapEquiv e⟩, fun ⟨q⟩ => ?_⟩
  have hq := q.unmapEquiv e
  simp only [RectifierCircuit.reindexVertices, Embedding.trans_apply, Equiv.coe_toEmbedding,
    Equiv.symm_apply_apply] at hq
  exact ⟨hq⟩

theorem HasDepthLE.reindexVertices {C : RectifierCircuit α β V} {d : ℕ}
    (hC : C.HasDepthLE d) (e : V ≃ V') : (C.reindexVertices e).HasDepthLE d := by
  intro u' v' p
  rw [← p.length_unmapEquiv e]
  exact hC (p.unmapEquiv e)

/-- Reindex the input and output pole types of a rectifier circuit along equivalences. -/
def reindexPoles (C : RectifierCircuit α β V) (eα : α ≃ α') (eβ : β ≃ β') :
    RectifierCircuit α' β' V where
  edges := C.edges
  inp := eβ.symm.toEmbedding.trans C.inp
  out := eα.symm.toEmbedding.trans C.out
  disjoint_poles := by
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨j', rfl⟩ _ ⟨i', rfl⟩ h
    exact C.inp_ne_out (eβ.symm j') (eα.symm i') h

@[simp] theorem size_reindexPoles (C : RectifierCircuit α β V) (eα : α ≃ α') (eβ : β ≃ β') :
    (C.reindexPoles eα eβ).size = C.size := by
  simp only [size, reindexPoles]

private def Walk.toReindexPoles {C : RectifierCircuit α β V} (eα : α ≃ α') (eβ : β ≃ β')
    {u v : V} : C.Walk u v → (C.reindexPoles eα eβ).Walk u v
  | .nil u => .nil u
  | .cons h p => .cons h (p.toReindexPoles eα eβ)

private def Walk.ofReindexPoles {C : RectifierCircuit α β V} (eα : α ≃ α') (eβ : β ≃ β')
    {u v : V} : (C.reindexPoles eα eβ).Walk u v → C.Walk u v
  | .nil u => .nil u
  | .cons h p => .cons h (p.ofReindexPoles eα eβ)

private theorem Walk.length_ofReindexPoles {C : RectifierCircuit α β V} (eα : α ≃ α')
    (eβ : β ≃ β') {u v : V} :
    (p : (C.reindexPoles eα eβ).Walk u v) → (p.ofReindexPoles eα eβ).length = p.length
  | .nil _ => rfl
  | .cons _ p => congrArg (· + 1) (p.length_ofReindexPoles eα eβ)

theorem HasDepthLE.reindexPoles {C : RectifierCircuit α β V} {d : ℕ}
    (hC : C.HasDepthLE d) (eα : α ≃ α') (eβ : β ≃ β') : (C.reindexPoles eα eβ).HasDepthLE d := by
  intro u v p
  rw [← p.length_ofReindexPoles eα eβ]
  exact hC (p.ofReindexPoles eα eβ)

theorem Computes.reindexPoles {C : RectifierCircuit α β V} {A : Matrix α β Bool}
    (hC : C.Computes A) (eα : α ≃ α') (eβ : β ≃ β') :
    (C.reindexPoles eα eβ).Computes (Matrix.reindex eα eβ A) := by
  intro i' j'
  simp only [Matrix.reindex_apply, Matrix.submatrix_apply, hC (eα.symm i') (eβ.symm j'),
    RectifierCircuit.reindexPoles, Embedding.trans_apply, Equiv.coe_toEmbedding]
  exact ⟨fun ⟨p⟩ => ⟨p.toReindexPoles eα eβ⟩, fun ⟨q⟩ => ⟨q.ofReindexPoles eα eβ⟩⟩

/-- The canonical depth-`1` rectifier circuit for `A : Matrix α β Bool` on vertex set `β ⊕ α`,
placing one directed edge `Sum.inl j → Sum.inr i` for each entry `A i j = true`. -/
def direct [Fintype α] [Fintype β] (A : Matrix α β Bool) : RectifierCircuit α β (β ⊕ α) where
  edges := ((univ : Finset (α × β)).filter fun p => A p.1 p.2 = true).map
    ⟨fun p => (Sum.inl p.2, Sum.inr p.1), fun p₁ p₂ h => by
      simp only [Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq] at h
      exact Prod.ext h.2 h.1⟩
  inp := Embedding.inl
  out := Embedding.inr
  disjoint_poles := by
    refine Set.disjoint_iff_forall_ne.mpr ?_
    rintro _ ⟨j, rfl⟩ _ ⟨i, rfl⟩ h
    simp only [Embedding.inl_apply, Embedding.inr_apply] at h
    nomatch h

@[simp] theorem size_direct [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    (direct A).size = boolMatrixWeight A := by
  simp only [size, direct, card_map, boolMatrixWeight]

theorem hasDepthLE_one_direct [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    (direct A).HasDepthLE 1 := by
  refine hasDepthLE_of_layer (Sum.elim (fun _ => 0) (fun _ => 1)) ?_ ?_
  · rintro u v huv
    obtain ⟨⟨i, j⟩, -, heq⟩ := mem_map.mp huv
    change (Sum.inl j, Sum.inr i) = (u, v) at heq
    rw [← (Prod.mk.inj heq).1, ← (Prod.mk.inj heq).2]
    rfl
  · rintro (j | i) <;> simp only [Sum.elim_inl, Sum.elim_inr, zero_le, le_refl]

/-- Any walk between distinct vertices `u ≠ w` begins with at least one directed edge `(u, v)`
followed by a walk from `v` to `w`. -/
theorem Walk.uncons {C : RectifierCircuit α β V} {u w : V} (hne : u ≠ w) :
    C.Walk u w → ∃ v : V, (u, v) ∈ C.edges ∧ Nonempty (C.Walk v w)
  | .nil _ => False.elim (hne rfl)
  | .cons he q => ⟨_, he, ⟨q⟩⟩

theorem computes_direct [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    (direct A).Computes A := by
  intro i j
  refine ⟨fun hij => ?_, fun ⟨p⟩ => ?_⟩
  · refine ⟨.cons (mem_map.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hij⟩, rfl⟩) (.nil _)⟩
  · obtain ⟨v, h, ⟨q⟩⟩ := p.uncons ((direct A).inp_ne_out j i)
    obtain ⟨⟨i', j'⟩, hmem, heq⟩ := mem_map.mp h
    change (Sum.inl j', Sum.inr i') = (Sum.inl j, v) at heq
    simp only [Prod.mk.injEq, Sum.inl.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    by_cases hi : i' = i
    · subst hi
      exact (mem_filter.mp hmem).2
    · obtain ⟨_, h₂, -⟩ := q.uncons fun hsum => hi (Sum.inr.inj hsum)
      obtain ⟨⟨_, _⟩, -, heq₂⟩ := mem_map.mp h₂
      change (Sum.inl _, Sum.inr _) = (Sum.inr i', _) at heq₂
      have hbad := (Prod.mk.inj heq₂).1
      nomatch hbad

private theorem card_ite_filter_embedding_le {γ : Type*} [Fintype γ] [DecidableEq V]
    (S : Finset γ) (f : γ ↪ V) (v : V) {K : ℕ} (hK : 1 < K) :
    #(if #S < K then S else univ.filter fun x => f x = v) ≤ K - 1 := by
  split_ifs with hlt
  · omega
  · have hle1 : #(univ.filter fun x : γ => f x = v) ≤ 1 :=
      card_le_one.mpr fun x₁ hx₁ x₂ hx₂ =>
        f.injective ((mem_filter.mp hx₁).2.trans (mem_filter.mp hx₂).2.symm)
    omega

/-- **Nechiporuk's rectangle-free rectifier bound** ([JuknaSergeev2013], §3.3, Theorem 3.9,
pp. 32–33, taking `k = l = K - 1`; [Nechiporuk1970]; [Sergeev2014ORComplement], p. 3 quotes the
weaker denominator `K ^ 2`): if a rectifier circuit `C` computes a `K`-free Boolean matrix `A`, then
`boolMatrixWeight A ≤ (K - 1) ^ 2 * C.size`. -/
theorem Computes.boolMatrixWeight_le_sq_pred_mul_size [Fintype α] [Fintype β]
    {C : RectifierCircuit α β V} {A : Matrix α β Bool} (hC : C.Computes A) {K : ℕ}
    (hA : IsRectangleFreeMatrix A K) :
    boolMatrixWeight A ≤ (K - 1) ^ 2 * C.size := by
  classical
  have hKpos : 0 < K := hA.pos
  rcases eq_or_lt_of_le (show 1 ≤ K by omega) with rfl | hK2
  · exact hA.boolMatrixWeight_eq_zero ▸ Nat.zero_le _
  set inSet : V → Finset β := fun v => univ.filter fun j => Nonempty (C.Walk (C.inp j) v)
  set outSet : V → Finset α := fun v => univ.filter fun i => Nonempty (C.Walk v (C.out i))
  set smallIn : V → Finset β :=
    fun u => if #(inSet u) < K then inSet u else univ.filter fun j => C.inp j = u
  set smallOut : V → Finset α :=
    fun w => if #(outSet w) < K then outSet w else univ.filter fun i => C.out i = w
  have hin_mono {u w : V} (he : (u, w) ∈ C.edges) : inSet u ⊆ inSet w := by
    intro j hj
    obtain ⟨p⟩ := (mem_filter.mp hj).2
    exact mem_filter.mpr ⟨mem_univ _, ⟨p.append (.cons he (.nil w))⟩⟩
  have hrect_vertex (v : V) (hin : K ≤ #(inSet v)) : #(outSet v) < K := by
    by_contra hout
    obtain ⟨I, hIsub, hIcard⟩ := exists_subset_card_eq (s := outSet v) (by omega : K ≤ #(outSet v))
    obtain ⟨J, hJsub, hJcard⟩ := exists_subset_card_eq (s := inSet v) hin
    refine hA I J hIcard hJcard fun i hi j hj => (hC i j).mpr ?_
    obtain ⟨p₁⟩ := (mem_filter.mp (hJsub hj)).2
    obtain ⟨p₂⟩ := (mem_filter.mp (hIsub hi)).2
    exact ⟨p₁.append p₂⟩
  have hcard_smallIn (u : V) : #(smallIn u) ≤ K - 1 :=
    card_ite_filter_embedding_le (inSet u) C.inp u hK2
  have hcard_smallOut (w : V) : #(smallOut w) ≤ K - 1 :=
    card_ite_filter_embedding_le (outSet w) C.out w hK2
  -- Walk induction: when `#(inSet u) < K`, some edge along `u →* out i` charges `(i, j)`.
  have hwalk_charge {i : α} {j : β} :
      ∀ {u z : V} (q : C.Walk u z), z = C.out i → u ≠ z → j ∈ inSet u → #(inSet u) < K →
        ∃ e ∈ C.edges, (i, j) ∈ smallOut e.2 ×ˢ smallIn e.1 := by
    intro u z q
    induction q with
    | nil _ =>
      intro _ hne
      exact False.elim (hne rfl)
    | @cons u v z he q' ih =>
      intro hz _ hju huK
      have hjin : j ∈ smallIn u := by simpa only [smallIn, huK, ↓reduceIte] using hju
      by_cases hv_out : v = z
      · subst hv_out
        subst hz
        refine ⟨(u, C.out i), he, mem_product.mpr ⟨?_, hjin⟩⟩
        dsimp only [smallOut]
        split_ifs with houtK
        · exact mem_filter.mpr ⟨mem_univ _, ⟨.nil _⟩⟩
        · exact mem_filter.mpr ⟨mem_univ _, rfl⟩
      · by_cases hvK : #(inSet v) < K
        · exact ih hz hv_out (hin_mono he hju) hvK
        · subst hz
          have hout_v : #(outSet v) < K := hrect_vertex v (by omega)
          refine ⟨(u, v), he, mem_product.mpr ⟨?_, hjin⟩⟩
          simp only [smallOut, hout_v, ↓reduceIte]
          exact mem_filter.mpr ⟨mem_univ _, ⟨q'⟩⟩
  have hcover : (univ.filter fun p : α × β => A p.1 p.2 = true) ⊆
      C.edges.biUnion fun e => smallOut e.2 ×ˢ smallIn e.1 := by
    rintro ⟨i, j⟩ hp
    obtain ⟨p⟩ := (hC i j).mp (mem_filter.mp hp).2
    rw [mem_biUnion]
    by_cases hjK : #(inSet (C.inp j)) < K
    · exact hwalk_charge p rfl (C.inp_ne_out j i)
        (mem_filter.mpr ⟨mem_univ _, ⟨.nil _⟩⟩) hjK
    · obtain ⟨v, he, ⟨q'⟩⟩ := p.uncons (C.inp_ne_out j i)
      have hv_in : K ≤ #(inSet v) :=
        (by omega : K ≤ #(inSet (C.inp j))).trans (card_le_card (hin_mono he))
      have hout_v : #(outSet v) < K := hrect_vertex v hv_in
      refine ⟨(C.inp j, v), he, mem_product.mpr ⟨?_, ?_⟩⟩
      · simp only [smallOut, hout_v, ↓reduceIte]
        exact mem_filter.mpr ⟨mem_univ _, ⟨q'⟩⟩
      · simp only [smallIn, hjK, ↓reduceIte]
        exact mem_filter.mpr ⟨mem_univ _, rfl⟩
  calc boolMatrixWeight A
      ≤ #(C.edges.biUnion fun e => smallOut e.2 ×ˢ smallIn e.1) := card_le_card hcover
    _ ≤ ∑ e ∈ C.edges, #(smallOut e.2 ×ˢ smallIn e.1) := card_biUnion_le
    _ = ∑ e ∈ C.edges, #(smallOut e.2) * #(smallIn e.1) :=
        sum_congr rfl fun e _ => card_product _ _
    _ ≤ ∑ _e ∈ C.edges, (K - 1) * (K - 1) :=
        sum_le_sum fun e _ => Nat.mul_le_mul (hcard_smallOut e.2) (hcard_smallIn e.1)
    _ = (K - 1) ^ 2 * C.size := by
        rw [sum_const, smul_eq_mul, size]
        ring

end RectifierCircuit

/-- **Rectifier (`OR`) complexity** `OR(A)` of a finite Boolean matrix `A`: the minimum number of
edges in a finite rectifier circuit computing `A` ([Sergeev2014ORComplement], p. 1).
Finite row and column types ensure that a direct circuit exists, so the feasible set is nonempty. -/
-- Finiteness restricts the public domain; `sInf` itself does not require it.
@[nolint unusedArguments]
noncomputable def orComplexity [Finite α] [Finite β] (A : Matrix α β Bool) : ℕ :=
  sInf {s : ℕ | ∃ (k : ℕ) (C : RectifierCircuit α β (Fin k)), C.Computes A ∧ C.size ≤ s}

/-- **Bounded-depth rectifier (`OR`) complexity** `OR_d(A)` of a Boolean matrix `A`: the minimum
number of edges in a finite rectifier circuit of depth at most `d` computing `A`, or `⊤` if none
exists ([Sergeev2014ORComplement], p. 1). -/
noncomputable def orDepthComplexity (d : ℕ) (A : Matrix α β Bool) : ℕ∞ :=
  ⨅ (k : ℕ) (C : RectifierCircuit α β (Fin k)) (_ : C.Computes A) (_ : C.HasDepthLE d),
    (C.size : ℕ∞)

private theorem exists_fin_rectifierCircuit [Finite α] [Finite β] (A : Matrix α β Bool) :
    {s : ℕ | ∃ (k : ℕ) (C : RectifierCircuit α β (Fin k)), C.Computes A ∧ C.size ≤ s}.Nonempty := by
  cases nonempty_fintype α
  cases nonempty_fintype β
  exact ⟨_, Fintype.card (β ⊕ α),
    (RectifierCircuit.direct A).reindexVertices (Fintype.equivFin (β ⊕ α)),
    (RectifierCircuit.computes_direct A).reindexVertices _, le_rfl⟩

/-- Any finite rectifier circuit `C` computing `A` bounds `orComplexity A` by `C.size`. -/
theorem RectifierCircuit.Computes.orComplexity_le [Finite α] [Finite β] [Finite V]
    {C : RectifierCircuit α β V} {A : Matrix α β Bool} (hC : C.Computes A) :
    orComplexity A ≤ C.size := by
  cases nonempty_fintype V
  exact Nat.sInf_le ⟨Fintype.card V, C.reindexVertices (Fintype.equivFin V),
    hC.reindexVertices _, (C.size_reindexVertices _).le⟩

/-- Any finite rectifier circuit `C` of depth at most `d` computing `A` bounds
`orDepthComplexity d A` by `C.size`. -/
theorem RectifierCircuit.Computes.orDepthComplexity_le [Finite V]
    {C : RectifierCircuit α β V} {A : Matrix α β Bool} (hC : C.Computes A) {d : ℕ}
    (hd : C.HasDepthLE d) :
    orDepthComplexity d A ≤ C.size := by
  cases nonempty_fintype V
  rw [orDepthComplexity]
  exact iInf_le_of_le (Fintype.card V) <|
    iInf_le_of_le (C.reindexVertices (Fintype.equivFin V)) <|
    iInf_le_of_le (hC.reindexVertices _) <|
    iInf_le_of_le (hd.reindexVertices _) <|
    Nat.cast_le.mpr (C.size_reindexVertices _).le

/-- A lower bound holds for `orComplexity A` whenever it holds for the size of every finite
rectifier circuit computing `A`. -/
theorem le_orComplexity [Finite α] [Finite β] {A : Matrix α β Bool} {m : ℕ}
    (h : ∀ (k : ℕ) (C : RectifierCircuit α β (Fin k)), C.Computes A → m ≤ C.size) :
    m ≤ orComplexity A := by
  obtain ⟨k, C, hC, hs⟩ := Nat.sInf_mem (exists_fin_rectifierCircuit A)
  exact (h k C hC).trans hs

/-- A lower bound holds for `orDepthComplexity d A` whenever it holds for the size of every finite
rectifier circuit of depth at most `d` computing `A`. -/
theorem le_orDepthComplexity {d : ℕ} {A : Matrix α β Bool} {m : ℕ∞}
    (h : ∀ (k : ℕ) (C : RectifierCircuit α β (Fin k)),
      C.Computes A → C.HasDepthLE d → m ≤ C.size) :
    m ≤ orDepthComplexity d A := by
  rw [orDepthComplexity]
  exact le_iInf fun k => le_iInf fun C => le_iInf fun hC => le_iInf fun hd => h k C hC hd

/-- At depth `0`, any Boolean matrix with a `true` entry has `orDepthComplexity 0 A = ⊤`, since
distinct input and output poles admit no zero-edge walk. -/
theorem orDepthComplexity_zero_eq_top {A : Matrix α β Bool} {i : α} {j : β}
    (hij : A i j = true) : orDepthComplexity 0 A = ⊤ := by
  refine top_unique (le_orDepthComplexity fun _ C hC hd => False.elim ?_)
  obtain ⟨p⟩ := (hC i j).mp hij
  obtain ⟨_, he, ⟨q⟩⟩ := p.uncons (C.inp_ne_out j i)
  exact Nat.not_succ_le_zero q.length (hd (.cons he q))

/-- Unrestricted `OR`-complexity never exceeds depth-`d` `OR`-complexity. -/
theorem orComplexity_le_orDepthComplexity [Finite α] [Finite β] (d : ℕ) (A : Matrix α β Bool) :
    (orComplexity A : ℕ∞) ≤ orDepthComplexity d A :=
  le_orDepthComplexity fun _ _ hC _ => Nat.cast_le.mpr hC.orComplexity_le

/-- Increasing the allowed depth `d` can only decrease `orDepthComplexity d A`. -/
theorem orDepthComplexity_anti {d₁ d₂ : ℕ} (hd : d₁ ≤ d₂) (A : Matrix α β Bool) :
    orDepthComplexity d₂ A ≤ orDepthComplexity d₁ A :=
  le_orDepthComplexity fun _ _ hC hd₁ => hC.orDepthComplexity_le (hd₁.mono hd)

/-- Depth-`1` `OR`-complexity is at most `boolMatrixWeight A`. -/
theorem orDepthComplexity_one_le_boolMatrixWeight [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    orDepthComplexity 1 A ≤ boolMatrixWeight A := by
  simpa only [RectifierCircuit.size_direct] using
    (RectifierCircuit.computes_direct A).orDepthComplexity_le
      (RectifierCircuit.hasDepthLE_one_direct A)

/-- Unrestricted `OR`-complexity is at most `boolMatrixWeight A`. -/
theorem orComplexity_le_boolMatrixWeight [Fintype α] [Fintype β] (A : Matrix α β Bool) :
    orComplexity A ≤ boolMatrixWeight A := by
  simpa only [RectifierCircuit.size_direct] using
    (RectifierCircuit.computes_direct A).orComplexity_le

private theorem orComplexity_reindex_le [Finite α] [Finite β] [Finite α'] [Finite β']
    (eα : α ≃ α') (eβ : β ≃ β') (A : Matrix α β Bool) :
    orComplexity (Matrix.reindex eα eβ A) ≤ orComplexity A :=
  le_orComplexity fun _ C hC => by
    simpa only [RectifierCircuit.size_reindexPoles] using
      (hC.reindexPoles eα eβ).orComplexity_le

/-- Reindexing rows and columns preserves `orComplexity`. -/
theorem orComplexity_reindex [Finite α] [Finite β] [Finite α'] [Finite β']
    (eα : α ≃ α') (eβ : β ≃ β') (A : Matrix α β Bool) :
    orComplexity (Matrix.reindex eα eβ A) = orComplexity A := by
  refine le_antisymm (orComplexity_reindex_le eα eβ A) ?_
  simpa only [← Matrix.reindex_symm, Equiv.symm_apply_apply] using
    orComplexity_reindex_le eα.symm eβ.symm (Matrix.reindex eα eβ A)

private theorem orDepthComplexity_reindex_le (d : ℕ)
    (eα : α ≃ α') (eβ : β ≃ β') (A : Matrix α β Bool) :
    orDepthComplexity d (Matrix.reindex eα eβ A) ≤ orDepthComplexity d A :=
  le_orDepthComplexity fun _ _ hC hd => by
    simpa only [RectifierCircuit.size_reindexPoles] using
      (hC.reindexPoles eα eβ).orDepthComplexity_le (hd.reindexPoles eα eβ)

/-- Reindexing rows and columns preserves `orDepthComplexity`. -/
theorem orDepthComplexity_reindex (d : ℕ) (eα : α ≃ α') (eβ : β ≃ β') (A : Matrix α β Bool) :
    orDepthComplexity d (Matrix.reindex eα eβ A) = orDepthComplexity d A := by
  refine le_antisymm (orDepthComplexity_reindex_le d eα eβ A) ?_
  simpa only [← Matrix.reindex_symm, Equiv.symm_apply_apply] using
    orDepthComplexity_reindex_le d eα.symm eβ.symm (Matrix.reindex eα eβ A)

/-- **Nechiporuk's theorem for `OR`-complexity** ([JuknaSergeev2013], §3.3, Theorem 3.9, pp. 32–33,
taking `k = l = K - 1`; [Nechiporuk1970]; [Sergeev2014ORComplement], p. 3 quotes the weaker
denominator `K ^ 2`): for every `K`-rectangle-free finite Boolean matrix `A`,
`boolMatrixWeight A ≤ (K - 1) ^ 2 * orComplexity A`. -/
theorem boolMatrixWeight_le_sq_pred_mul_orComplexity [Fintype α] [Fintype β]
    {A : Matrix α β Bool} {K : ℕ} (hA : IsRectangleFreeMatrix A K) :
    boolMatrixWeight A ≤ (K - 1) ^ 2 * orComplexity A := by
  obtain ⟨k, C, hC, hs⟩ := Nat.sInf_mem (exists_fin_rectifierCircuit A)
  exact (hC.boolMatrixWeight_le_sq_pred_mul_size hA).trans (Nat.mul_le_mul_left _ hs)

/-- For every `2`-rectangle-free finite Boolean matrix `A`, `orComplexity A = boolMatrixWeight A`
([JuknaSergeev2013], §3.3, Theorem 3.9, p. 33; [Sergeev2014ORComplement], p. 1;
[Nechiporuk1970]). -/
theorem orComplexity_eq_boolMatrixWeight_of_isRectangleFree_two [Fintype α] [Fintype β]
    {A : Matrix α β Bool} (hA : IsRectangleFreeMatrix A 2) :
    orComplexity A = boolMatrixWeight A := by
  refine le_antisymm (orComplexity_le_boolMatrixWeight A) ?_
  have h := boolMatrixWeight_le_sq_pred_mul_orComplexity hA
  linarith

/-- For every `2`-rectangle-free finite Boolean matrix `A` and every `1 ≤ d`,
`orDepthComplexity d A = boolMatrixWeight A` ([JuknaSergeev2013], §3.3, Theorem 3.9, p. 33;
[Sergeev2014ORComplement], p. 1; [Nechiporuk1970]). -/
theorem orDepthComplexity_eq_boolMatrixWeight_of_isRectangleFree_two [Fintype α] [Fintype β]
    {A : Matrix α β Bool} (hA : IsRectangleFreeMatrix A 2) {d : ℕ} (hd : 1 ≤ d) :
    orDepthComplexity d A = boolMatrixWeight A := by
  refine le_antisymm ?_ ?_
  · exact (orDepthComplexity_anti hd A).trans (orDepthComplexity_one_le_boolMatrixWeight A)
  · rw [← orComplexity_eq_boolMatrixWeight_of_isRectangleFree_two hA]
    exact orComplexity_le_orDepthComplexity d A

end Cslib.Circuits
