/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Analysis.Convex.ExtendedFormulation.Correlation
public import Mathlib.Combinatorics.SimpleGraph.Clique
import CslibFrontier.Tactic.FinIndex
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

/-!
# Exponential extension-complexity lower bound for stable set polytopes

The **stable set polytope** `stabPolytope K G` (`STAB(G)`) of a finite simple graph `G` on `V` is
the convex hull of the characteristic vectors of all independent sets of `G`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.3].

Following [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 8 and Theorem 10], for each `n` we
construct the `2 n²`-vertex gadget graph `corrGadgetGraph n` (`H_n`), whose maximum-cardinality
stable sets (`|S| = n + n (n - 1) / 2`) pick one vertex from each vertex-pair clique and one from
each edge-quadruple clique, and project linearly onto `corrPolytope K (Fin n)`. Padding with
isolated vertices to any `m ≥ 2` using `p = ⌊√(m / 2)⌋` produces a graph `stabHardGraph m` on
`Fin m` with `extensionComplexity (stabPolytope K (stabHardGraph m)) ≥ (3 / 2) ^ ⌊√(m / 2)⌋`.

## Main definitions

* `stabVertex`, `stabPolytope`: the stable set polytope `STAB(G)` of a finite simple graph `G`.
* `CorrPairIdx`, `CorrGadgetV`, `corrGadgetGraph`: the `2 n²`-vertex gadget graph `H_n`.
* `stabHardGraph`: the `m`-vertex graph on `Fin m` embedding `corrGadgetGraph ⌊√(m / 2)⌋`.

## Main results

* `extensionComplexity_corrPolytope_le_corrGadgetGraph`:
  `xc (corrPolytope K (Fin n)) ≤ xc (stabPolytope K (corrGadgetGraph n))`.
* `three_pow_le_two_pow_mul_extensionComplexity_stabPolytope`:
  for `m ≥ 2` and `p = Nat.sqrt (m / 2)`,
  `3 ^ p ≤ 2 ^ p * extensionComplexity (stabPolytope K (stabHardGraph m))`.
* `HasExtendedFormulation.three_div_two_pow_le_of_stabPolytope`: for `m ≥ 2` and
  `HasExtendedFormulation (stabPolytope K (stabHardGraph m)) r`, `(3 / 2 : F) ^ ⌊√(m / 2)⌋ ≤ r`.

## References

* [FioriniMassarPokuttaTiwaryDeWolf2015], Section 3.3 (Lemmas 8–9 and Theorem 10).
* [KaibelWeltge2015], Section 2 (Theorem 1).
-/

public section

section Defs

variable (K : Type*) [Semiring K] [PartialOrder K]

/-- Characteristic vector of a subset `S : Finset V` in `V → K`. -/
@[expose] def stabVertex {V : Type*} [DecidableEq V] (S : Finset V) : V → K :=
  fun v => if v ∈ S then 1 else 0

/-- The **stable set polytope** `STAB(G)` of a simple graph `G` on `V`
[FioriniMassarPokuttaTiwaryDeWolf2015, Section 3.3]. -/
@[expose] def stabPolytope {V : Type*} [DecidableEq V] (G : SimpleGraph V) : Set (V → K) :=
  convexHull K (Set.range fun S : {S : Finset V // G.IsIndepSet (S : Set V)} =>
    stabVertex K S.1)

end Defs

section Gadget

/-- Ordered pairs `(fst, snd)` in `Fin n` with `fst < snd`. -/
structure CorrPairIdx (n : ℕ) where
  /-- Smaller vertex index in `Fin n`. -/
  fst : Fin n
  /-- Larger vertex index in `Fin n`. -/
  snd : Fin n
  /-- Ordering witness `fst < snd`. -/
  lt : fst < snd
  deriving DecidableEq

private def corrPairIdxEquivSubtype (n : ℕ) :
    CorrPairIdx n ≃ {p : Fin n × Fin n // p.1 < p.2} where
  toFun e := ⟨(e.fst, e.snd), e.lt⟩
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[no_expose] instance (n : ℕ) : Fintype (CorrPairIdx n) :=
  Fintype.ofEquiv _ (corrPairIdxEquivSubtype n).symm

/-- Vertices of the FMPTW stable-set gadget graph `H_n`
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 8]: two vertices per node of `K_n` and four per
edge of `K_n`. -/
inductive CorrGadgetV (n : ℕ) : Type
  | vertex (i : Fin n) (val : Bool)
  | edge (e : CorrPairIdx n) (val₁ val₂ : Bool)
  deriving DecidableEq

private def corrGadgetVEquivSum (n : ℕ) :
    CorrGadgetV n ≃ (Fin n × Bool) ⊕ (CorrPairIdx n × Bool × Bool) where
  toFun
    | .vertex i b => Sum.inl (i, b)
    | .edge e b₁ b₂ => Sum.inr (e, b₁, b₂)
  invFun
    | Sum.inl (i, b) => .vertex i b
    | Sum.inr (e, b₁, b₂) => .edge e b₁ b₂
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with ⟨i, b⟩ | ⟨e, b₁, b₂⟩ <;> rfl

@[no_expose] instance (n : ℕ) : Fintype (CorrGadgetV n) :=
  Fintype.ofEquiv _ (corrGadgetVEquivSum n).symm

private def corrPairSuccEquiv (n : ℕ) : CorrPairIdx (n + 1) ≃ CorrPairIdx n ⊕ Fin n where
  toFun e :=
    if h : e.snd = Fin.last n then
      Sum.inr ⟨e.fst.1, by have := e.lt; fin_index⟩
    else
      Sum.inl ⟨e.fst.castPred (Fin.ne_last_of_lt (lt_of_lt_of_le e.lt (Fin.le_last _))),
        e.snd.castPred h, by have := e.lt; fin_index⟩
  invFun
    | Sum.inl e => ⟨e.fst.castSucc, e.snd.castSucc, by have := e.lt; fin_index⟩
    | Sum.inr i => ⟨i.castSucc, Fin.last n, Fin.castSucc_lt_last i⟩
  left_inv e := by
    dsimp only
    split_ifs with h
    · obtain ⟨f, s, lt⟩ := e
      dsimp only at h
      subst h
      simp only [Fin.castSucc_mk, Fin.eta]
    · cases e with
      | mk f s lt =>
          simp only [Fin.castSucc_castPred]
  right_inv x := by
    rcases x with e | i
    · dsimp only
      have hs : e.snd.castSucc ≠ Fin.last n := (Fin.castSucc_lt_last e.snd).ne
      simp only [hs, ↓reduceDIte, Fin.castPred_castSucc]
    · simp only [↓reduceDIte, Fin.val_castSucc, Fin.eta]

/-- Exact vertex count `|V(H_n)| = 2 n²` [FioriniMassarPokuttaTiwaryDeWolf2015, §3.3]. -/
theorem card_corrGadgetV (n : ℕ) : Fintype.card (CorrGadgetV n) = 2 * n ^ 2 := by
  have hpair : ∀ k, 2 * k + 4 * Fintype.card (CorrPairIdx k) = 2 * k ^ 2 := by
    intro k
    induction k with
    | zero =>
      have : IsEmpty (CorrPairIdx 0) := ⟨fun e => e.fst.elim0⟩
      simp
    | succ k ih =>
      rw [Fintype.card_congr (corrPairSuccEquiv k), Fintype.card_sum, Fintype.card_fin]
      nlinarith
  simp only [Fintype.card_congr (corrGadgetVEquivSum n), Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin, Fintype.card_bool]
  linarith [hpair n]

private def corrGadgetAdjRel {n : ℕ} : CorrGadgetV n → CorrGadgetV n → Prop
  | .vertex i b₁, .vertex j b₂ => i = j ∧ b₁ ≠ b₂
  | .edge e₁ c₁ d₁, .edge e₂ c₂ d₂ => e₁ = e₂ ∧ (c₁ ≠ c₂ ∨ d₁ ≠ d₂)
  | .vertex i b, .edge e c₁ c₂ => (i = e.fst ∧ b ≠ c₁) ∨ (i = e.snd ∧ b ≠ c₂)
  | .edge e c₁ c₂, .vertex i b => (i = e.fst ∧ b ≠ c₁) ∨ (i = e.snd ∧ b ≠ c₂)

/-- The FMPTW stable-set gadget graph `H_n` [FioriniMassarPokuttaTiwaryDeWolf2015, Lemma 8]. -/
def corrGadgetGraph (n : ℕ) : SimpleGraph (CorrGadgetV n) where
  Adj := corrGadgetAdjRel
  symm := ⟨fun u v h => by cases u <;> cases v <;> simp only [corrGadgetAdjRel] at h ⊢ <;> tauto⟩
  loopless := ⟨fun u h => by cases u <;> simp only [corrGadgetAdjRel] at h <;> tauto⟩

private def gadgetBlock {n : ℕ} : CorrGadgetV n → Fin n ⊕ CorrPairIdx n
  | .vertex i _ => Sum.inl i
  | .edge e _ _ => Sum.inr e

private theorem adj_of_gadgetBlock_eq {n : ℕ} {u v : CorrGadgetV n} (hne : u ≠ v)
    (heq : gadgetBlock u = gadgetBlock v) : (corrGadgetGraph n).Adj u v := by
  cases u <;> cases v <;>
    simp only [gadgetBlock, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq] at heq <;>
    simp only [corrGadgetGraph, corrGadgetAdjRel] <;> grind

/-- A stable set of the gadget graph has at most one vertex in each block. -/
private theorem injOn_gadgetBlock {n : ℕ} {S : Set (CorrGadgetV n)}
    (hS : (corrGadgetGraph n).IsIndepSet S) : Set.InjOn gadgetBlock S := fun _ hu _ hv heq =>
  by_contra fun hne => hS hu hv hne (adj_of_gadgetBlock_eq hne heq)

private theorem card_le_of_isIndepSet_corrGadgetGraph {n : ℕ} {S : Finset (CorrGadgetV n)}
    (hS : (corrGadgetGraph n).IsIndepSet (S : Set (CorrGadgetV n))) :
    S.card ≤ n + Fintype.card (CorrPairIdx n) :=
  (Finset.card_le_card_of_injOn gadgetBlock (fun _ _ => Finset.mem_univ _)
    (injOn_gadgetBlock hS)).trans_eq (by rw [Finset.card_univ, Fintype.card_sum, Fintype.card_fin])

private def liftCorrIndep {n : ℕ} (b : Finset (Fin n)) : Finset (CorrGadgetV n) :=
  (Finset.univ.image fun i => CorrGadgetV.vertex i (decide (i ∈ b))) ∪
    Finset.univ.image fun e : CorrPairIdx n =>
      CorrGadgetV.edge e (decide (e.fst ∈ b)) (decide (e.snd ∈ b))

private theorem isIndepSet_liftCorrIndep {n : ℕ} (b : Finset (Fin n)) :
    (corrGadgetGraph n).IsIndepSet (liftCorrIndep b : Set (CorrGadgetV n)) := by
  intro u hu v hv hne hadj
  simp only [Finset.mem_coe, liftCorrIndep, Finset.mem_union, Finset.mem_image,
    Finset.mem_univ, true_and] at hu hv
  rcases hu with ⟨i, rfl⟩ | ⟨e₁, rfl⟩ <;> rcases hv with ⟨j, rfl⟩ | ⟨e₂, rfl⟩ <;>
    simp only [corrGadgetGraph, corrGadgetAdjRel] at hadj <;> grind

private theorem card_liftCorrIndep {n : ℕ} (b : Finset (Fin n)) :
    (liftCorrIndep b).card = n + Fintype.card (CorrPairIdx n) := by
  rw [liftCorrIndep, Finset.card_union_of_disjoint (by simp [Finset.disjoint_left]),
    Finset.card_image_of_injective _ fun i j h => by cases h; rfl,
    Finset.card_image_of_injective _ fun e₁ e₂ h => by cases h; rfl, Finset.card_fin,
    Finset.card_univ]

private def stabToCorrLinear (K : Type*) [Semiring K] (n : ℕ) :
    (CorrGadgetV n → K) →ₗ[K] ((Fin n × Fin n) → K) where
  toFun x p :=
    if h : p.1 = p.2 then x (.vertex p.1 true)
    else if hlt : p.1 < p.2 then x (.edge ⟨p.1, p.2, hlt⟩ true true)
    else x (.edge ⟨p.2, p.1, (lt_or_gt_of_ne h).resolve_left hlt⟩ true true)
  map_add' x y := by
    ext ⟨i, j⟩
    simp only [Pi.add_apply]
    split_ifs <;> rfl
  map_smul' c x := by
    ext ⟨i, j⟩
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    split_ifs <;> rfl

private theorem stabToCorrLinear_lift {K : Type*} [Semiring K]
    {n : ℕ} (b : Finset (Fin n)) :
    stabToCorrLinear K n (stabVertex K (liftCorrIndep b)) = corrVertex K b := by
  ext ⟨i, j⟩
  rcases lt_trichotomy i j with h | rfl | h
  · simp [stabToCorrLinear, stabVertex, corrVertex, liftCorrIndep, h.ne, h]
  · simp [stabToCorrLinear, stabVertex, corrVertex, liftCorrIndep]
  · simp [stabToCorrLinear, stabVertex, corrVertex, liftCorrIndep, h.ne', h.not_gt, and_comm]

/-- A stable set of the gadget graph of maximum size takes from each block the vertex given by
the set `b` of the `i` with `vertex i true` in it. -/
private theorem exists_eq_liftCorrIndep {n : ℕ} {S : Finset (CorrGadgetV n)}
    (hS : (corrGadgetGraph n).IsIndepSet (S : Set (CorrGadgetV n)))
    (hcard : S.card = n + Fintype.card (CorrPairIdx n)) : ∃ b, S = liftCorrIndep b := by
  -- `S` meets every block.
  have hblock (x : Fin n ⊕ CorrPairIdx n) : ∃ u ∈ S, gadgetBlock u = x := by
    have him : S.image gadgetBlock = Finset.univ := Finset.eq_univ_of_card _ (by
      rw [Finset.card_image_of_injOn (injOn_gadgetBlock hS), hcard, Fintype.card_sum,
        Fintype.card_fin])
    exact Finset.mem_image.1 (him.symm ▸ Finset.mem_univ x)
  let b : Finset (Fin n) := Finset.univ.filter fun i => CorrGadgetV.vertex i true ∈ S
  have hv (i : Fin n) : .vertex i (decide (i ∈ b)) ∈ S := by
    obtain ⟨u, hu, hx⟩ := hblock (.inl i)
    rcases u with ⟨j, val⟩ | _ <;> cases hx
    by_cases h : CorrGadgetV.vertex i true ∈ S <;>
      simp only [b, Finset.mem_filter, Finset.mem_univ, true_and, h, decide_true, decide_false]
    cases val
    exacts [hu, absurd hu h]
  have he (e : CorrPairIdx n) : .edge e (decide (e.fst ∈ b)) (decide (e.snd ∈ b)) ∈ S := by
    obtain ⟨u, hu, hx⟩ := hblock (.inr e)
    rcases u with _ | ⟨e', c₁, c₂⟩ <;> cases hx
    -- The vertices of `S` at the two ends of `e` are not adjacent to its vertex in the block.
    have h1 : decide (e.fst ∈ b) = c₁ :=
      by_contra fun h => hS (hv e.fst) hu nofun (.inl ⟨rfl, h⟩)
    have h2 : decide (e.snd ∈ b) = c₂ :=
      by_contra fun h => hS (hv e.snd) hu nofun (.inr ⟨rfl, h⟩)
    rwa [h1, h2]
  refine ⟨b, (Finset.eq_of_subset_of_card_le (fun x hx => ?_)
    (by rw [hcard, card_liftCorrIndep])).symm⟩
  simp only [liftCorrIndep, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨i, rfl⟩ | ⟨e, rfl⟩
  exacts [hv i, he e]

/-- `CORR(n)` is the linear projection of a face of `STAB(corrGadgetGraph n)`
[FioriniMassarPokuttaTiwaryDeWolf2015, Lemmas 8–9]. -/
theorem extensionComplexity_corrPolytope_le_corrGadgetGraph
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (n : ℕ) :
    extensionComplexity (corrPolytope K (Fin n)) ≤
      extensionComplexity (stabPolytope K (corrGadgetGraph n)) := by
  let c : CorrGadgetV n → K := fun _ => 1
  have hdot (S : Finset (CorrGadgetV n)) : c ⬝ᵥ stabVertex K S = (S.card : K) := by
    simp [dotProduct, c, stabVertex]
  -- The face of stable sets of maximum size projects onto the correlation polytope.
  have him : stabToCorrLinear K n '' (stabPolytope K (corrGadgetGraph n) ∩
      {x | c ⬝ᵥ x = (n + Fintype.card (CorrPairIdx n) : ℕ)}) = corrPolytope K (Fin n) := by
    rw [stabPolytope, convexHull_inter_dotProduct_eq fun S => by
      rw [hdot]; exact_mod_cast card_le_of_isIndepSet_corrGadgetGraph S.2,
      LinearMap.image_convexHull, corrPolytope]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range, Subtype.exists, hdot,
      Nat.cast_inj]
    constructor
    · rintro ⟨_, ⟨S, hS, hSc, rfl⟩, rfl⟩
      obtain ⟨b, rfl⟩ := exists_eq_liftCorrIndep hS hSc
      exact ⟨b, (stabToCorrLinear_lift b).symm⟩
    · rintro ⟨b, rfl⟩
      exact ⟨_, ⟨_, isIndepSet_liftCorrIndep b, card_liftCorrIndep b, rfl⟩,
        stabToCorrLinear_lift b⟩
  rw [← him]
  exact (extensionComplexity_image_linearMap_le _ _).trans
    (extensionComplexity_inter_dotProduct_eq_le _ c _)

end Gadget

section LowerBound

private noncomputable def stabHardEmb (m : ℕ) :
    CorrGadgetV (Nat.sqrt (m / 2)) ↪ Fin m := by
  let p := Nat.sqrt (m / 2)
  have hle : Fintype.card (CorrGadgetV p) ≤ m := by
    rw [card_corrGadgetV]
    have hsq : p ^ 2 ≤ m / 2 := Nat.sqrt_le' (m / 2)
    omega
  exact (Fintype.equivFin (CorrGadgetV p)).toEmbedding.trans (Fin.castLEEmb hle)

/-- An explicit `m`-vertex graph (`m ≥ 2`) obtained by embedding `corrGadgetGraph ⌊√(m / 2)⌋`
together with isolated vertices [FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 10]. -/
noncomputable def stabHardGraph (m : ℕ) : SimpleGraph (Fin m) :=
  if hm : 2 ≤ m then
    { Adj := fun u v => ∃ a b, stabHardEmb m a = u ∧ stabHardEmb m b = v ∧
        (corrGadgetGraph (Nat.sqrt (m / 2))).Adj a b
      symm := ⟨fun _ _ ⟨a, b, ha, hb, hab⟩ => ⟨b, a, hb, ha, hab.symm⟩⟩
      loopless := ⟨fun _ ⟨a, b, ha, hb, hab⟩ => by
        have hba : a = b := (stabHardEmb m).injective (ha.trans hb.symm)
        subst hba
        exact (corrGadgetGraph (Nat.sqrt (m / 2))).ne_of_adj hab rfl⟩ }
  else ⊥

private theorem extensionComplexity_corrGadgetGraph_le_stabHardGraph
    {K : Type*} [Field K] [LinearOrder K] (m : ℕ) (hm : 2 ≤ m) :
    extensionComplexity (stabPolytope K (corrGadgetGraph (Nat.sqrt (m / 2)))) ≤
      extensionComplexity (stabPolytope K (stabHardGraph m)) := by
  classical
  let p := Nat.sqrt (m / 2)
  let emb := stabHardEmb m
  let proj : (Fin m → K) →ₗ[K] (CorrGadgetV p → K) := LinearMap.funLeft K K emb
  have hadj (a b : CorrGadgetV p) :
      (stabHardGraph m).Adj (emb a) (emb b) ↔ (corrGadgetGraph p).Adj a b := by
    simp [stabHardGraph, hm, emb, p]
  have him : proj '' stabPolytope K (stabHardGraph m) =
      stabPolytope K (corrGadgetGraph p) := by
    rw [stabPolytope, LinearMap.image_convexHull, stabPolytope]
    congr 1
    ext y
    simp only [Set.mem_image, Set.mem_range, Subtype.exists]
    constructor
    · rintro ⟨_, ⟨S, hS, rfl⟩, rfl⟩
      exact ⟨Finset.univ.filter fun a => emb a ∈ S, fun a ha b hb hab h =>
        hS (Finset.mem_filter.1 ha).2 (Finset.mem_filter.1 hb).2 (emb.injective.ne hab)
          ((hadj a b).2 h), by ext a; simp [proj, stabVertex]⟩
    · rintro ⟨T, hT, rfl⟩
      refine ⟨_, ⟨T.map emb, ?_, rfl⟩, by ext a; simp [proj, stabVertex]⟩
      rw [Finset.coe_map]
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hab h
      exact hT ha hb (fun h' => hab (congrArg emb h')) ((hadj a b).1 h)
  rw [← him]
  exact extensionComplexity_image_linearMap_le _ proj

/-- Exponential lower bound for the stable set polytope on `m ≥ 2` vertices: for
`p = Nat.sqrt (m / 2)`, `3 ^ p ≤ 2 ^ p * xc (stabPolytope K (stabHardGraph m))` in `ℕ∞`
[FioriniMassarPokuttaTiwaryDeWolf2015, Theorem 10]; [KaibelWeltge2015, Theorem 1]. -/
theorem three_pow_le_two_pow_mul_extensionComplexity_stabPolytope
    {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] (m : ℕ) (hm : 2 ≤ m) :
    ((3 ^ Nat.sqrt (m / 2) : ℕ) : ℕ∞) ≤
      (2 ^ Nat.sqrt (m / 2) : ℕ∞) * extensionComplexity (stabPolytope K (stabHardGraph m)) := by
  have : Nonempty (Fin (Nat.sqrt (m / 2))) := ⟨⟨0, Nat.sqrt_pos.2 (by omega)⟩⟩
  have h1 := three_pow_le_two_pow_mul_extensionComplexity_corrPolytope (K := K)
    (α := Fin (Nat.sqrt (m / 2)))
  rw [Fintype.card_fin] at h1
  exact h1.trans (mul_le_mul_right ((extensionComplexity_corrPolytope_le_corrGadgetGraph _).trans
    (extensionComplexity_corrGadgetGraph_le_stabHardGraph m hm)) _)

/-- Field-valued `2^{Ω(√m)}` lower bound: any extended formulation of
`stabPolytope K (stabHardGraph m)` (`m ≥ 2`) with `r` inequalities satisfies
`(3 / 2 : F) ^ Nat.sqrt (m / 2) ≤ r`. -/
theorem HasExtendedFormulation.three_div_two_pow_le_of_stabPolytope
    {K F : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [Field F] [LinearOrder F] [IsStrictOrderedRing F]
    {m r : ℕ} (hm : 2 ≤ m) (hr : HasExtendedFormulation (stabPolytope K (stabHardGraph m)) r) :
    (3 / 2 : F) ^ Nat.sqrt (m / 2) ≤ r :=
  hr.three_div_two_pow_le_of_mul_le (three_pow_le_two_pow_mul_extensionComplexity_stabPolytope m hm)

end LowerBound
