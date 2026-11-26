/-
Copyright (c) 2026 vvauted. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: vvauted
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Query.MinimumSpanningForest.DecisionTree.Basic
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Choose.Basic

/-!
# Canonical MSF Decision-Tree Complexity `T*(m, n)` and Lower Bound

A step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), formalizing the canonical
worst-case complexity function `T*(m, n)` and Propositions 5.1–5.2 (§5.1, p. 25):
isomorphism invariance (`optDepth_reindex`) and embedding monotonicity (`optDepth_le_of_inj`,
`optDepth_le_of_submask`), equivalence of the `≤ m` and exact-`m` definitions of `optDepthMN` for
`m ≤ n.choose 2` (`optDepthMN_eq_exact`), the generic query-program upper bound
(`optDepthMN_le_of_freeM`), the cycle-cover lower bound `m ≤ 2 * optDepthMN m n`
(`le_two_mul_optDepthMN`), and monotonicity (`optDepthMN_mono_m`, `optDepthMN_mono_n`).

## Main definitions

* `Cslib.Query.MinimumSpanningForest.optDepthMN`: worst-case optimal comparison depth `T*(m, n)`
  over simple graphs on `n` vertices with at most `m` edges (equal to the exact-`m` maximum when
  `m ≤ n.choose 2` by `optDepthMN_eq_exact`).

## Main results

* `Cslib.Query.MinimumSpanningForest.optDepth_reindex`,
  `Cslib.Query.MinimumSpanningForest.optDepth_le_of_inj`: isomorphism invariance and supergraph /
  embedding monotonicity of `optDepth`.
* `Cslib.Query.MinimumSpanningForest.optDepthMN_eq_exact`: equivalence with the exact-`m`-edge
  maximum for `m ≤ n.choose 2`.
* `Cslib.Query.MinimumSpanningForest.optDepth_le_optDepthMN_of_isSimple`: any `e`-edge `n`-vertex
  simple graph with `e ≤ m` satisfies `optDepth ends ≤ optDepthMN m n`.
* `Cslib.Query.MinimumSpanningForest.optDepthMN_le_of_freeM`: uniform upper bound from any
  monotone comparison-query MSF family.
* `Cslib.Query.MinimumSpanningForest.le_two_mul_optDepthMN`: Proposition 5.1 of
  [PettieRamachandran2002], `m ≤ 2 * optDepthMN m n` for `3 ≤ m`, `3 ≤ n`, `m ≤ n.choose 2`.
* `Cslib.Query.MinimumSpanningForest.optDepthMN_mono_m`,
  `Cslib.Query.MinimumSpanningForest.optDepthMN_mono_n`: Proposition 5.2 of
  [PettieRamachandran2002] (`optDepthMN m₁ n ≤ optDepthMN m₂ n` and vertex monotonicity).
-/

public section

namespace Cslib.Query.MinimumSpanningForest

/-! ## Reindexing and Canonical Reduction of Simple Graphs -/

theorem joins_reindex {E₁ E₂ V₁ V₂ : Type*} (ends₁ : E₁ → Sym2 V₁) (ends₂ : E₂ → Sym2 V₂)
    (ι : E₁ ↪ E₂) (φ : V₁ ↪ V₂)
    (hEnds : ∀ i : E₁, Sym2.map φ (ends₁ i) = ends₂ (ι i))
    (S : Finset E₁) (u v : V₁) :
    Cslib.Multigraph.Joins ends₁ (S : Set E₁) u v ↔
      Cslib.Multigraph.Joins ends₂ ((S.map ι : Finset E₂) : Set E₂) (φ u) (φ v) := by
  constructor
  · refine Cslib.Multigraph.Joins.lift φ fun e he a b hab => ?_
    exact Cslib.Multigraph.Joins.of_mem (Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨e, he, rfl⟩))
      (by simpa [hab] using (hEnds e).symm)
  · intro hc
    classical
    let pull : V₂ → V₁ := fun x => if hx : ∃ a, φ a = x then hx.choose else u
    have hpull : ∀ a : V₁, pull (φ a) = a := fun a => by
      dsimp only [pull]
      have hx : ∃ a', φ a' = φ a := ⟨a, rfl⟩
      rw [dite_eq_left_of_eq_true (eq_true hx)]
      exact φ.injective hx.choose_spec
    have hmap : Cslib.Multigraph.Joins ends₁ (S : Set E₁) (pull (φ u)) (pull (φ v)) := by
      refine Cslib.Multigraph.Joins.lift pull (fun g hg a b hab => ?_) hc
      rw [Finset.mem_coe, Finset.mem_map] at hg
      obtain ⟨e, heS, rfl⟩ := hg
      induction he : ends₁ e using Sym2.ind with
      | _ a₁ b₁ =>
        have hsym : s(φ a₁, φ b₁) = s(a, b) := by
          rw [← Sym2.map_mk (f := φ), ← he, hEnds e]
          simpa using hab
        rcases Sym2.eq_iff.mp hsym with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · have hp1 : pull a = a₁ := by rw [← h1, hpull]
          have hp2 : pull b = b₁ := by rw [← h2, hpull]
          rw [hp1, hp2]
          exact Cslib.Multigraph.Joins.of_mem heS he
        · have hp1 : pull a = b₁ := by rw [← h2, hpull]
          have hp2 : pull b = a₁ := by rw [← h1, hpull]
          rw [hp1, hp2]
          exact (Cslib.Multigraph.Joins.of_mem heS he).symm
    rwa [hpull u, hpull v] at hmap

private theorem optDepth_reindex_le {n₁ n₂ e₁ e₂ : ℕ}
    (ends₁ : Fin e₁ → Sym2 (Fin n₁)) (ends₂ : Fin e₂ → Sym2 (Fin n₂))
    (σ : Fin e₁ ≃ Fin e₂) (heq : e₁ = e₂)
    (hunique : ∀ p : Equiv.Perm (Fin e₂),
      Cslib.Multigraph.msf ends₂ p Finset.univ =
        (Cslib.Multigraph.msf ends₁
          (σ.trans (p.trans (Fin.castOrderIso heq.symm).toEquiv)) Finset.univ).map
          σ.toEmbedding) :
    optDepth ends₂ ≤ optDepth ends₁ := by
  obtain ⟨T₁, hcorr₁, hd₁⟩ := exists_opt_msfDT ends₁
  rw [MSFDT.correct_iff] at hcorr₁
  let T₂ : MSFDT e₂ := (T₁.mapLeaves (Finset.map σ.toEmbedding)).liftEmb σ
  refine (optDepth_le_of_correct (T := T₂) ((MSFDT.correct_iff _ _).mpr fun p => ?_)).trans ?_
  · let c : Equiv.Perm (Fin e₁) := σ.trans (p.trans (Fin.castOrderIso heq.symm).toEquiv)
    have heval : T₂.eval p = (T₁.eval c).map σ.toEmbedding := by
      rw [← MSFTree.mapLeaves_eval (Finset.map σ.toEmbedding) T₁ c]
      refine MSFTree.liftEmb_eval σ (T₁.mapLeaves _) c p fun a b => ?_
      dsimp only [c]
      simp [Fin.castOrderIso]
    rw [heval, hcorr₁ c, hunique p]
  · simp [T₂, hd₁]

theorem optDepth_reindex {e₁ e₂ n₁ n₂ : ℕ}
    (ends₁ : Fin e₁ → Sym2 (Fin n₁)) (ends₂ : Fin e₂ → Sym2 (Fin n₂))
    (σ : Fin e₁ ≃ Fin e₂) (φ : Fin n₁ ↪ Fin n₂)
    (hEnds : ∀ i : Fin e₁, Sym2.map φ (ends₁ i) = ends₂ (σ i)) :
    optDepth ends₁ = optDepth ends₂ := by
  have heq : e₁ = e₂ := by simpa using Fintype.card_congr σ
  have hunique : ∀ p : Equiv.Perm (Fin e₂),
      let c : Equiv.Perm (Fin e₁) := σ.trans (p.trans (Fin.castOrderIso heq.symm).toEquiv)
      Cslib.Multigraph.msf ends₂ p Finset.univ =
        (Cslib.Multigraph.msf ends₁ c Finset.univ).map σ.toEmbedding := by
    intro p c
    ext g
    rw [Finset.mem_map]
    let i := σ.symm g
    have hperm_iff : ∀ a b : Fin e₁, c a < c b ↔ p (σ a) < p (σ b) := fun a b => by
      change (c a).val < (c b).val ↔ (p (σ a)).val < (p (σ b)).val
      simp [c, Fin.castOrderIso]
    induction hi : ends₁ i using Sym2.ind with
    | _ a₁ b₁ =>
      have hg_ends : ends₂ g = s(φ a₁, φ b₁) := by
        have hsi : σ i = g := σ.apply_symm_apply g
        rw [← hsi, ← hEnds i, hi]
        rfl
      have hflt : ((Finset.univ.filter fun e' : Fin e₁ => c e' < c i).map
          σ.toEmbedding : Finset (Fin e₂)) = Finset.univ.filter fun f => p f < p g := by
        ext f
        simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
          Equiv.coe_toEmbedding]
        constructor
        · rintro ⟨e', he', rfl⟩
          exact (σ.apply_symm_apply g).symm ▸ (hperm_iff e' i).mp he'
        · intro hf
          refine ⟨σ.symm f, (hperm_iff (σ.symm f) i).mpr ?_, σ.apply_symm_apply f⟩
          simpa [i] using hf
      have hset₁ : {e' | e' ∈ (Finset.univ : Finset (Fin e₁)) ∧ c e' < c i} =
          ((Finset.univ.filter fun e' => c e' < c i : Finset (Fin e₁)) : Set (Fin e₁)) := by
        ext e'; simp
      have hset₂ : {f | f ∈ (Finset.univ : Finset (Fin e₂)) ∧ p f < p g} =
          ((Finset.univ.filter fun f => p f < p g : Finset (Fin e₂)) : Set (Fin e₂)) := by
        ext f; simp
      have hj_iff : Cslib.Multigraph.Joins ends₁
          {e' | e' ∈ (Finset.univ : Finset (Fin e₁)) ∧ c e' < c i} a₁ b₁ ↔
          Cslib.Multigraph.Joins ends₂
            {f | f ∈ (Finset.univ : Finset (Fin e₂)) ∧ p f < p g} (φ a₁) (φ b₁) := by
        rw [hset₁, hset₂, ← hflt]
        exact joins_reindex ends₁ ends₂ σ.toEmbedding φ hEnds _ a₁ b₁
      constructor
      · intro hg
        refine ⟨i, ?_, σ.apply_symm_apply g⟩
        rw [Cslib.Multigraph.mem_msf_iff p hg_ends] at hg
        rw [Cslib.Multigraph.mem_msf_iff c hi]
        exact ⟨Finset.mem_univ _, fun hc => hg.2 (hj_iff.mp hc)⟩
      · rintro ⟨e, he, hge⟩
        have hei : e = i := σ.injective (hge.trans (σ.apply_symm_apply g).symm)
        rw [hei] at he
        rw [Cslib.Multigraph.mem_msf_iff c hi] at he
        rw [Cslib.Multigraph.mem_msf_iff p hg_ends]
        exact ⟨Finset.mem_univ _, fun hc => he.2 (hj_iff.mpr hc)⟩
  have hle1 : optDepth ends₂ ≤ optDepth ends₁ :=
    optDepth_reindex_le ends₁ ends₂ σ heq hunique
  have hle2 : optDepth ends₁ ≤ optDepth ends₂ :=
    optDepth_reindex_le ends₂ ends₁ σ.symm heq.symm fun q => by
      let p : Equiv.Perm (Fin e₂) := σ.symm.trans (q.trans (Fin.castOrderIso heq).toEquiv)
      have hqp : σ.trans (p.trans (Fin.castOrderIso heq.symm).toEquiv) = q := by
        ext x; simp [p, Fin.castOrderIso]
      have hu := hunique p
      dsimp only at hu
      rw [hqp] at hu
      rw [hu, Finset.map_map]
      ext x
      simp
  exact le_antisymm hle2 hle1

theorem optDepth_endsOfMask_le {r₁ r₂ mask : ℕ} (hrr : r₁ ≤ r₂)
    (hmask : mask < 2 ^ r₁.choose 2) :
    optDepth (endsOfMask r₁ mask) = optDepth (endsOfMask r₂ mask) := by
  have hmap := maskEdgePairs_cast hrr hmask
  have hlen : (maskEdgePairs r₂ mask).length = (maskEdgePairs r₁ mask).length := by
    rw [hmap, List.length_map]
  let σ : Fin (maskEdgePairs r₁ mask).length ≃ Fin (maskEdgePairs r₂ mask).length :=
    (Fin.castOrderIso hlen.symm).toEquiv
  let φ : Fin r₁ ↪ Fin r₂ := Fin.castLEEmb hrr
  refine optDepth_reindex (endsOfMask r₁ mask) (endsOfMask r₂ mask) σ φ fun i => ?_
  have hget : (maskEdgePairs r₂ mask)[(σ i).val] =
      Prod.map (Fin.castLE hrr) (Fin.castLE hrr) (maskEdgePairs r₁ mask)[i.val] := by
    rw [List.getElem_of_eq hmap, List.getElem_map]
    rfl
  dsimp only [endsOfMask, φ]
  simp only [Fin.getElem_fin] at *
  rw [hget]
  rfl

private theorem mask_of_edgeFun_testBit {e R : ℕ} (idxFun : Fin e ↪ Fin R) (k : ℕ) :
    (∑ i : Fin e, 2 ^ (idxFun i).val).testBit k =
      decide (∃ i : Fin e, (idxFun i).val = k) := by
  let S : Finset (Fin R) := Finset.univ.map idxFun
  have hsum : (∑ i : Fin e, (2 : ℕ) ^ (idxFun i).val) = maskOfFinset S := by
    rw [maskOfFinset, Finset.sum_map]
  rw [hsum, testBit_maskOfFinset]
  apply decide_eq_decide.mpr
  constructor
  · rintro ⟨hk, hmem⟩
    rw [Finset.mem_map] at hmem
    obtain ⟨i, _, hi⟩ := hmem
    exact ⟨i, congrArg Fin.val hi⟩
  · rintro ⟨i, rfl⟩
    exact ⟨(idxFun i).isLt, Finset.mem_map.mpr ⟨i, Finset.mem_univ i, Fin.ext rfl⟩⟩

private theorem exists_ordered_pair_of_not_isDiag {n : ℕ} {s : Sym2 (Fin n)} (hnd : ¬ s.IsDiag) :
    ∃ p : Fin n × Fin n, p.1.val < p.2.val ∧ s = s(p.1, p.2) := by
  induction s using Sym2.ind with
  | _ a b =>
    rw [Sym2.mk_isDiag_iff] at hnd
    have hne : a.val ≠ b.val := fun h => hnd (Fin.ext h)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact ⟨(a, b), hlt, rfl⟩
    · exact ⟨(b, a), hgt, Sym2.eq_swap⟩

theorem optDepth_eq_endsOfMask_of_isSimple {e n : ℕ} (ends : Fin e → Sym2 (Fin n))
    (hG : IsSimple ends) :
    ∃ mask < 2 ^ n.choose 2, (maskEdgePairs n mask).length = e ∧
      optDepth ends = optDepth (endsOfMask n mask) := by
  classical
  have hG' := (isSimple_iff ends).mp hG
  let pairOf : Fin e → Fin n × Fin n := fun i =>
    Classical.choose (exists_ordered_pair_of_not_isDiag (hG'.1 i))
  have hpair_lt : ∀ i : Fin e, (pairOf i).1.val < (pairOf i).2.val := fun i =>
    (Classical.choose_spec (exists_ordered_pair_of_not_isDiag (hG'.1 i))).1
  have hpair_sym2 : ∀ i : Fin e, ends i = s((pairOf i).1, (pairOf i).2) := fun i =>
    (Classical.choose_spec (exists_ordered_pair_of_not_isDiag (hG'.1 i))).2
  let idxFun : Fin e ↪ Fin (n.choose 2) :=
    ⟨fun i => ⟨pairIdx (pairOf i).1.val (pairOf i).2.val,
        pairIdx_lt_choose_two (hpair_lt i) (pairOf i).2.isLt⟩,
     fun i₁ i₂ heq => by
       have heqv : pairIdx (pairOf i₁).1.val (pairOf i₁).2.val =
           pairIdx (pairOf i₂).1.val (pairOf i₂).2.val := congrArg Fin.val heq
       have hg₁ := getElem_allPairs_pairIdx (hpair_lt i₁)
       have hg₂ := getElem_allPairs_pairIdx (hpair_lt i₂)
       have hpeq : pairOf i₁ = pairOf i₂ := by
         rw [← Prod.mk.eta (p := pairOf i₁), ← Prod.mk.eta (p := pairOf i₂), ← hg₁, ← hg₂]
         simp only [heqv]
       refine hG'.2 ?_
       rw [hpair_sym2 i₁, hpair_sym2 i₂, hpeq]⟩
  let mask := ∑ i : Fin e, 2 ^ (idxFun i).val
  have hmask_lt : mask < 2 ^ n.choose 2 := by
    have hsum : mask = maskOfFinset (Finset.univ.map idxFun) := by
      simp [mask, maskOfFinset, Finset.sum_map]
    rw [hsum]
    exact maskOfFinset_lt _
  have hmem_iff : ∀ k : ℕ, (mask.testBit k = true) ↔ ∃ i : Fin e, (idxFun i).val = k := fun k => by
    rw [mask_of_edgeFun_testBit idxFun k, decide_eq_true_iff]
  have hmem_pairs : ∀ i : Fin e, pairOf i ∈ maskEdgePairs n mask := fun i =>
    mem_maskEdgePairs_iff.mpr ⟨hpair_lt i, (hmem_iff _).mpr ⟨i, rfl⟩⟩
  have hpairs_mem : ∀ p ∈ maskEdgePairs n mask, ∃ i : Fin e, pairOf i = p := by
    intro p hp
    obtain ⟨hlt, htb⟩ := mem_maskEdgePairs_iff.mp hp
    obtain ⟨i, hi⟩ := (hmem_iff _).mp htb
    refine ⟨i, ?_⟩
    have hget := getElem_allPairs_pairIdx (hpair_lt i)
    have hgetp := getElem_allPairs_pairIdx hlt
    have hji : pairIdx (pairOf i).1.val (pairOf i).2.val = pairIdx p.1.val p.2.val := hi
    have hpeq : (allPairs n)[pairIdx (pairOf i).1.val (pairOf i).2.val]'(by
        rw [length_allPairs]; exact pairIdx_lt_choose_two (hpair_lt i) (pairOf i).2.isLt) =
        (allPairs n)[pairIdx p.1.val p.2.val]'(by
        rw [length_allPairs]; exact pairIdx_lt_choose_two hlt p.2.isLt) := by
      simp only [hji]
    rw [hget, hgetp] at hpeq
    simpa using hpeq
  let f : Fin e → Fin (maskEdgePairs n mask).length := fun i =>
    ⟨(maskEdgePairs n mask).idxOf (pairOf i), List.idxOf_lt_length_of_mem (hmem_pairs i)⟩
  have hf_get : ∀ i : Fin e, (maskEdgePairs n mask)[(f i).val] = pairOf i := fun i =>
    List.getElem_idxOf (List.idxOf_lt_length_of_mem (hmem_pairs i))
  have hf_inj : Function.Injective f := fun i₁ i₂ he => by
    have h1 := hf_get i₁
    have h2 := hf_get i₂
    have hpeq : pairOf i₁ = pairOf i₂ := by
      rw [← h1, ← h2]
      exact congrArg
        (fun k : Fin (maskEdgePairs n mask).length => (maskEdgePairs n mask)[k.val]) he
    refine hG'.2 ?_
    rw [hpair_sym2 i₁, hpair_sym2 i₂, hpeq]
  have hf_surj : Function.Surjective f := fun k => by
    obtain ⟨i, hi⟩ := hpairs_mem _ (List.getElem_mem k.isLt)
    refine ⟨i, Fin.ext ?_⟩
    have hn : (maskEdgePairs n mask).Nodup := maskEdgePairs_nodup n mask
    have hg := hf_get i
    rw [hi] at hg
    exact hn.getElem_inj_iff.mp hg
  let σ : Fin e ≃ Fin (maskEdgePairs n mask).length := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
  have hlen : (maskEdgePairs n mask).length = e := by
    simpa using (Fintype.card_congr σ.symm)
  refine ⟨mask, hmask_lt, hlen, ?_⟩
  refine optDepth_reindex ends (endsOfMask n mask) σ (Equiv.refl (Fin n)).toEmbedding fun i => ?_
  have hget : (maskEdgePairs n mask)[(σ i).val] = pairOf i := hf_get i
  change Sym2.map id (ends i) = endsOfMask n mask (σ i)
  rw [Sym2.map_id, hpair_sym2 i]
  dsimp only [endsOfMask]
  simp only [Fin.getElem_fin, hget]
  rfl

private def findPre {e₁ e₂ : ℕ} (ι : Fin e₁ ↪ Fin e₂) (x : Fin e₂) : Option (Fin e₁) :=
  (List.finRange e₁).find? fun a => decide (ι a = x)

private theorem findPre_some {e₁ e₂ : ℕ} (ι : Fin e₁ ↪ Fin e₂) {x : Fin e₂} {a : Fin e₁}
    (h : findPre ι x = some a) : ι a = x :=
  of_decide_eq_true (List.find?_some (p := fun b => decide (ι b = x)) h)

private theorem findPre_eq_some {e₁ e₂ : ℕ} (ι : Fin e₁ ↪ Fin e₂) (a : Fin e₁) :
    findPre ι (ι a) = some a := by
  cases h : findPre ι (ι a) with
  | none =>
    have hnone := List.find?_eq_none.mp h a (List.mem_finRange a)
    simp at hnone
  | some b => exact congrArg some (ι.injective (findPre_some ι h))

private noncomputable def MSFTree.restrictEmb {e₁ e₂ : ℕ} (ι : Fin e₁ ↪ Fin e₂) :
    MSFDT e₂ → MSFDT e₁
  | .leaf ans => .leaf (ans.preimage ι ι.injective.injOn)
  | .node x y l r =>
    match findPre ι x, findPre ι y with
    | some a, some b => .node a b (l.restrictEmb ι) (r.restrictEmb ι)
    | some _, none => l.restrictEmb ι
    | none, some _ => r.restrictEmb ι
    | none, none => if x.val < y.val then l.restrictEmb ι else r.restrictEmb ι

private theorem MSFTree.restrictEmb_depth_le {e₁ e₂ : ℕ} (ι : Fin e₁ ↪ Fin e₂) (T : MSFDT e₂) :
    (T.restrictEmb ι).depth ≤ T.depth := by
  induction T with
  | leaf _ => simp [restrictEmb, depth]
  | node x y l r ihl ihr =>
    dsimp only [restrictEmb]
    cases findPre ι x <;> cases findPre ι y <;> dsimp only
    · split_ifs <;> simp only [depth] <;> omega
    · simp only [depth]; omega
    · simp only [depth]; omega
    · simp only [depth]; omega

private theorem MSFTree.restrictEmb_eval {e₁ e₂ : ℕ} (ι : Fin e₁ ↪ Fin e₂)
    (p₁ : Equiv.Perm (Fin e₁)) (w₂ : Fin e₂ → ℕ) (p₂ : Equiv.Perm (Fin e₂))
    (hw₂ : ∀ x y, (p₂ x).val < (p₂ y).val ↔ w₂ x < w₂ y)
    (hmatch : ∀ x, match findPre ι x with | some a => w₂ x = (p₁ a).val | none => w₂ x = e₁ + x.val)
    (T : MSFDT e₂) :
    (T.restrictEmb ι).eval p₁ = (T.eval p₂).preimage ι ι.injective.injOn := by
  induction T with
  | leaf ans => rfl
  | node x y l r ihl ihr =>
    dsimp only [restrictEmb, eval]
    have hxy_iff : (p₂ x).val < (p₂ y).val ↔ w₂ x < w₂ y := hw₂ x y
    have hx_spec := hmatch x
    have hy_spec := hmatch y
    cases hx : findPre ι x with
    | none =>
      rw [hx] at hx_spec
      cases hy : findPre ι y with
      | none =>
        rw [hy] at hy_spec
        dsimp only
        have hlt_iff : (p₂ x).val < (p₂ y).val ↔ x.val < y.val := by
          rw [hxy_iff, hx_spec, hy_spec]
          omega
        by_cases hlt : x.val < y.val
        · have hp2 : (p₂ x).val < (p₂ y).val := hlt_iff.mpr hlt
          simp only [hlt, ↓reduceIte, hp2]
          exact ihl
        · have hp2 : ¬ (p₂ x).val < (p₂ y).val := fun h => hlt (hlt_iff.mp h)
          simp only [hlt, ↓reduceIte, hp2]
          exact ihr
      | some b =>
        rw [hy] at hy_spec
        dsimp only
        have hp2 : ¬ (p₂ x).val < (p₂ y).val := by
          rw [hxy_iff, hx_spec, hy_spec]
          have hb := (p₁ b).isLt
          omega
        simp only [hp2, ↓reduceIte]
        exact ihr
    | some a =>
      rw [hx] at hx_spec
      cases hy : findPre ι y with
      | none =>
        rw [hy] at hy_spec
        dsimp only
        have hp2 : (p₂ x).val < (p₂ y).val := by
          rw [hxy_iff, hx_spec, hy_spec]
          have ha := (p₁ a).isLt
          omega
        simp only [hp2, ↓reduceIte]
        exact ihl
      | some b =>
        rw [hy] at hy_spec
        dsimp only [eval]
        have hlt_iff : (p₂ x).val < (p₂ y).val ↔ (p₁ a).val < (p₁ b).val := by
          rw [hxy_iff, hx_spec, hy_spec]
        by_cases hlt : (p₁ a).val < (p₁ b).val
        · have hp2 : (p₂ x).val < (p₂ y).val := hlt_iff.mpr hlt
          simp only [hlt, ↓reduceIte, hp2]
          exact ihl
        · have hp2 : ¬ (p₂ x).val < (p₂ y).val := fun h => hlt (hlt_iff.mp h)
          simp only [hlt, ↓reduceIte, hp2]
          exact ihr

/-- Embedding monotonicity of optimal decision-tree depth: adding edges and embedding vertices
cannot decrease `optDepth`. -/
theorem optDepth_le_of_inj {e₁ e₂ n₁ n₂ : ℕ}
    (ends₁ : Fin e₁ → Sym2 (Fin n₁)) (ends₂ : Fin e₂ → Sym2 (Fin n₂))
    (ι : Fin e₁ ↪ Fin e₂) (φ : Fin n₁ ↪ Fin n₂)
    (hEnds : ∀ i : Fin e₁, Sym2.map φ (ends₁ i) = ends₂ (ι i)) :
    optDepth ends₁ ≤ optDepth ends₂ := by
  obtain ⟨T₂, hcorr₂, hd₂⟩ := exists_opt_msfDT ends₂
  rw [MSFDT.correct_iff] at hcorr₂
  have hcorr₁ : (T₂.restrictEmb ι).Correct ends₁ := (MSFDT.correct_iff _ _).mpr fun p₁ => by
    let w₂ : Fin e₂ → ℕ := fun x =>
      match findPre ι x with
      | some a => (p₁ a).val
      | none => e₁ + x.val
    have hw₂ : Function.Injective w₂ := fun x y h => by
      dsimp only [w₂] at h
      cases hx : findPre ι x with
      | none =>
        cases hy : findPre ι y with
        | none =>
          simp only [hx, hy] at h
          exact Fin.ext (by omega)
        | some b =>
          simp only [hx, hy] at h
          have hb := (p₁ b).isLt
          omega
      | some a =>
        cases hy : findPre ι y with
        | none =>
          simp only [hx, hy] at h
          have ha := (p₁ a).isLt
          omega
        | some b =>
          simp only [hx, hy] at h
          have hab : a = b := p₁.injective (Fin.ext h)
          subst hab
          exact (findPre_some ι hx).symm.trans (findPre_some ι hy)
    let p₂ : Equiv.Perm (Fin e₂) := orderPerm w₂ hw₂
    have heval : (T₂.restrictEmb ι).eval p₁ =
        (T₂.eval p₂).preimage ι ι.injective.injOn :=
      T₂.restrictEmb_eval ι p₁ w₂ p₂ (orderPerm_lt_iff w₂ hw₂)
        (fun x => by cases hx : findPre ι x <;> simp [w₂, hx])
    have hmsf : (Cslib.Multigraph.msf ends₂ p₂ Finset.univ).preimage ι ι.injective.injOn =
        Cslib.Multigraph.msf ends₁ p₁ Finset.univ := by
      ext i
      rw [Finset.mem_preimage]
      rw [msf_congr_lt ends₂ p₂ w₂ Finset.univ (orderPerm_lt_iff w₂ hw₂)]
      induction hi : ends₁ i using Sym2.ind with
      | _ u v =>
        have hi₂ : ends₂ (ι i) = s(φ u, φ v) := by
          rw [← hEnds i, hi, Sym2.map_mk]
        rw [Cslib.Multigraph.mem_msf_iff w₂ hi₂, Cslib.Multigraph.mem_msf_iff p₁ hi]
        simp only [Finset.mem_univ, true_and]
        have hset : {f : Fin e₂ | w₂ f < w₂ (ι i)} =
            (((Finset.univ.filter fun j : Fin e₁ => p₁ j < p₁ i).map ι :
              Finset (Fin e₂)) : Set (Fin e₂)) := by
          ext f
          simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_map, Finset.mem_filter,
            Finset.mem_univ, true_and]
          constructor
          · intro hlt
            cases hf : findPre ι f with
            | none =>
              exfalso
              dsimp only [w₂] at hlt
              rw [hf, findPre_eq_some] at hlt
              dsimp only at hlt
              have hi_lt := (p₁ i).isLt
              omega
            | some j =>
              dsimp only [w₂] at hlt
              rw [hf, findPre_eq_some] at hlt
              dsimp only at hlt
              exact ⟨j, Fin.lt_def.mpr hlt, findPre_some ι hf⟩
          · rintro ⟨j, hj, rfl⟩
            dsimp only [w₂]
            rw [findPre_eq_some, findPre_eq_some]
            exact Fin.lt_def.mp hj
        have hset₁ : {f : Fin e₁ | p₁ f < p₁ i} =
            ((Finset.univ.filter fun j : Fin e₁ => p₁ j < p₁ i : Finset (Fin e₁)) :
              Set (Fin e₁)) := by
          ext f; simp
        rw [hset, hset₁]
        exact not_congr (joins_reindex ends₁ ends₂ ι φ hEnds _ u v).symm
    rw [heval, hcorr₂ p₂, hmsf]
  exact (optDepth_le_of_correct hcorr₁).trans ((T₂.restrictEmb_depth_le ι).trans hd₂.le)

/-- Bitmask supergraph monotonicity: turning on additional edge bits in `mask` cannot decrease
`optDepth (endsOfMask r mask)`. -/
theorem optDepth_le_of_submask {r mask₁ mask₂ : ℕ}
    (hsub : ∀ k : ℕ, mask₁.testBit k = true → mask₂.testBit k = true) :
    optDepth (endsOfMask r mask₁) ≤ optDepth (endsOfMask r mask₂) := by
  have hmem : ∀ p ∈ maskEdgePairs r mask₁, p ∈ maskEdgePairs r mask₂ := fun p hp => by
    obtain ⟨hlt, htb⟩ := mem_maskEdgePairs_iff.mp hp
    exact mem_maskEdgePairs_iff.mpr ⟨hlt, hsub _ htb⟩
  let ι : Fin (maskEdgePairs r mask₁).length ↪ Fin (maskEdgePairs r mask₂).length :=
    ⟨fun i => ⟨(maskEdgePairs r mask₂).idxOf (maskEdgePairs r mask₁)[i.val],
        List.idxOf_lt_length_of_mem (hmem _ (List.getElem_mem i.isLt))⟩,
     fun i₁ i₂ he => by
       have hget₁ : (maskEdgePairs r mask₂)[(maskEdgePairs r mask₂).idxOf
           (maskEdgePairs r mask₁)[i₁.val]]'(List.idxOf_lt_length_of_mem
             (hmem _ (List.getElem_mem i₁.isLt))) = (maskEdgePairs r mask₁)[i₁.val] :=
         List.getElem_idxOf _
       have hget₂ : (maskEdgePairs r mask₂)[(maskEdgePairs r mask₂).idxOf
           (maskEdgePairs r mask₁)[i₂.val]]'(List.idxOf_lt_length_of_mem
             (hmem _ (List.getElem_mem i₂.isLt))) = (maskEdgePairs r mask₁)[i₂.val] :=
         List.getElem_idxOf _
       have hidx : (maskEdgePairs r mask₂).idxOf (maskEdgePairs r mask₁)[i₁.val] =
           (maskEdgePairs r mask₂).idxOf (maskEdgePairs r mask₁)[i₂.val] := congrArg Fin.val he
       have hpeq : (maskEdgePairs r mask₁)[i₁.val] = (maskEdgePairs r mask₁)[i₂.val] := by
         rw [← hget₁, ← hget₂]
         simp only [hidx]
       exact Fin.ext ((maskEdgePairs_nodup r mask₁).getElem_inj_iff.mp hpeq)⟩
  refine optDepth_le_of_inj (endsOfMask r mask₁) (endsOfMask r mask₂)
    ι (Equiv.refl (Fin r)).toEmbedding fun i => ?_
  have hget : (maskEdgePairs r mask₂)[(ι i).val] = (maskEdgePairs r mask₁)[i.val] :=
    List.getElem_idxOf _
  change Sym2.map id (endsOfMask r mask₁ i) = endsOfMask r mask₂ (ι i)
  rw [Sym2.map_id]
  dsimp only [endsOfMask]
  simp only [Fin.getElem_fin, hget]
  rfl

/-! ## Worst-Case Optimal Depth `T*(m, n)` -/

/-- Worst-case optimal decision-tree depth `T*(m, n)` over all simple graphs on `n` vertices with
at most `m` edges (equal to the exact-`m` maximum for `m ≤ n.choose 2` by `optDepthMN_eq_exact`). -/
noncomputable def optDepthMN (m n : ℕ) : ℕ :=
  ((Finset.range (2 ^ n.choose 2)).filter fun mask =>
    (maskEdgePairs n mask).length ≤ m).sup fun mask => optDepth (endsOfMask n mask)

theorem optDepth_endsOfMask_le_optDepthMN {m n mask : ℕ}
    (hmask : mask < 2 ^ n.choose 2) (hlen : (maskEdgePairs n mask).length ≤ m) :
    optDepth (endsOfMask n mask) ≤ optDepthMN m n := by
  refine Finset.le_sup (f := fun k => optDepth (endsOfMask n k)) ?_
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmask, hlen⟩

theorem exists_endsOfMask_eq_optDepthMN (m n : ℕ) :
    ∃ mask < 2 ^ n.choose 2, (maskEdgePairs n mask).length ≤ m ∧
      optDepth (endsOfMask n mask) = optDepthMN m n := by
  let S := (Finset.range (2 ^ n.choose 2)).filter fun mask =>
    (maskEdgePairs n mask).length ≤ m
  have hne : S.Nonempty := ⟨0, Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr (Nat.two_pow_pos _), by simp [maskEdgePairs_zero]⟩⟩
  obtain ⟨mask, hmem, hsup⟩ := Finset.exists_mem_eq_sup S hne (fun k => optDepth (endsOfMask n k))
  rw [Finset.mem_filter, Finset.mem_range] at hmem
  exact ⟨mask, hmem.1, hmem.2, hsup.symm⟩

/-- For `m ≤ n.choose 2`, `optDepthMN m n` agrees with the exact-`m`-edge maximum `T*(m, n)` of
[PettieRamachandran2002], Section 5.1. -/
theorem optDepthMN_eq_exact {m n : ℕ} (hm : m ≤ n.choose 2) :
    optDepthMN m n = ((Finset.range (2 ^ n.choose 2)).filter fun mask =>
      (maskEdgePairs n mask).length = m).sup fun mask => optDepth (endsOfMask n mask) := by
  apply le_antisymm
  · obtain ⟨mask, hmask, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m n
    rw [← heq]
    let S₁ : Finset (Fin (n.choose 2)) :=
      Finset.univ.filter fun j => mask.testBit j.val = true
    have hS₁_card : S₁.card = (maskEdgePairs n mask).length := by
      rw [length_maskEdgePairs]
      refine Finset.card_bij (fun j _ => j.val)
        (fun j hj => by
          rw [Finset.mem_filter] at hj ⊢
          exact ⟨Finset.mem_range.mpr j.isLt, hj.2⟩)
        (fun _ _ _ _ h => Fin.ext h)
        (fun k hk => by
          rw [Finset.mem_filter, Finset.mem_range] at hk
          exact ⟨⟨k, hk.1⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk.2⟩, rfl⟩)
    let extra := (Finset.univ \ S₁).toList.take (m - S₁.card)
    let S₂ := S₁ ∪ extra.toFinset
    have hdisj : Disjoint S₁ extra.toFinset := by
      rw [Finset.disjoint_left]
      intro x hx hex
      have hxs := (Finset.mem_sdiff.mp
        (Finset.mem_toList.mp (List.mem_of_mem_take (List.mem_toFinset.mp hex)))).2
      exact hxs hx
    have hcard_sdiff : m - S₁.card ≤ (Finset.univ \ S₁).toList.length := by
      rw [Finset.length_toList, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
        Fintype.card_fin]
      omega
    have hS₂_card : S₂.card = m := by
      rw [Finset.card_union_of_disjoint hdisj, List.toFinset_card_of_nodup
        ((Finset.nodup_toList _).sublist (List.take_sublist _ _)), List.length_take,
        Nat.min_eq_left hcard_sdiff]
      omega
    let mask₂ := maskOfFinset S₂
    have hmask₂_lt : mask₂ < 2 ^ n.choose 2 := maskOfFinset_lt S₂
    have hsub : ∀ k : ℕ, mask.testBit k = true → mask₂.testBit k = true := by
      intro k hk
      have hk_lt : k < n.choose 2 := by
        by_contra hge
        have hpow : mask < 2 ^ k :=
          hmask.trans_le (Nat.pow_le_pow_right (by omega) (Nat.le_of_not_lt hge))
        exact absurd (Nat.testBit_eq_false_of_lt hpow) (by simp [hk])
      have hmem₁ : (⟨k, hk_lt⟩ : Fin (n.choose 2)) ∈ S₁ :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      have hmem₂ : (⟨k, hk_lt⟩ : Fin (n.choose 2)) ∈ S₂ := Finset.mem_union_left _ hmem₁
      simpa [mask₂, testBit_maskOfFinset, hk_lt] using hmem₂
    have hlen₂ : (maskEdgePairs n mask₂).length = m := by
      rw [length_maskEdgePairs]
      have hcard₂ : ((Finset.range (n.choose 2)).filter fun j => mask₂.testBit j).card =
          S₂.card := by
        refine Finset.card_bij (fun k hk => ⟨k, (Finset.mem_range.mp
            (Finset.mem_filter.mp hk).1)⟩)
          (fun k hk => by
            have hfk := Finset.mem_filter.mp hk
            have hk_lt := Finset.mem_range.mp hfk.1
            simpa [mask₂, testBit_maskOfFinset, hk_lt] using hfk.2)
          (fun _ _ _ _ h => congrArg Fin.val h)
          (fun j hj => ⟨j.val, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr j.isLt, by
            simpa [mask₂, testBit_maskOfFinset, j.isLt] using hj⟩, Fin.ext rfl⟩)
      rw [hcard₂, hS₂_card]
    exact (optDepth_le_of_submask hsub).trans (Finset.le_sup
      (f := fun k => optDepth (endsOfMask n k))
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hmask₂_lt, hlen₂⟩))
  · refine Finset.sup_mono fun mask hmask => ?_
    rw [Finset.mem_filter] at hmask ⊢
    exact ⟨hmask.1, hmask.2.le⟩

theorem optDepth_le_optDepthMN_of_isSimple {e n m : ℕ} (ends : Fin e → Sym2 (Fin n))
    (hG : IsSimple ends) (hle : e ≤ m) :
    optDepth ends ≤ optDepthMN m n := by
  obtain ⟨mask, hmask, hlen, heq⟩ := optDepth_eq_endsOfMask_of_isSimple ends hG
  rw [heq]
  exact optDepth_endsOfMask_le_optDepthMN hmask (hlen ▸ hle)

/-- Uniform decision-tree upper bound `T*(m, n) ≤ f m` from any monotone comparison-query MSF
algorithm family solving simple graphs on `r` vertices with `e` edges in at most `f e` queries. -/
theorem optDepthMN_le_of_freeM (m n : ℕ) (f : ℕ → ℕ) (hf_mono : Monotone f)
    (alg : ∀ {e r : ℕ}, (Fin e → Sym2 (Fin r)) → FreeM (LEQuery (Fin e)) (Finset (Fin e)))
    (hcorr : ∀ {e r : ℕ} (ends : Fin e → Sym2 (Fin r)), IsSimple ends →
      ∀ p : Equiv.Perm (Fin e),
        (alg ends).eval (LEQuery.keyOracle p) = Cslib.Multigraph.msf ends p Finset.univ)
    (hdepth : ∀ {e r : ℕ} (ends : Fin e → Sym2 (Fin r)), IsSimple ends →
      ∀ p : Equiv.Perm (Fin e),
        (alg ends).countQueries (LEQuery.keyOracle p) ≤ f e) :
    optDepthMN m n ≤ f m := by
  obtain ⟨mask, _, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m n
  rw [← heq]
  have hs := endsOfMask_isSimple n mask
  exact (optDepth_le_of_freeM (endsOfMask n mask) (alg (endsOfMask n mask))
    (f (maskEdgePairs n mask).length) (hcorr _ hs) (hdepth _ hs)).trans (hf_mono hlen)

/-! ## Propositions 5.1 and 5.2 ([PettieRamachandran2002]) -/

/-- Path variables inspected along decision tree `T` when following permutation `p`. -/
def MSFTree.traceVars {e : ℕ} {α : Type} :
    MSFTree e α → Equiv.Perm (Fin e) → Finset (Fin e)
  | .leaf _, _ => ∅
  | .node i j l r, p => {i, j} ∪ if (p i).val < (p j).val then l.traceVars p else r.traceVars p

theorem MSFTree.card_traceVars_le {e : ℕ} {α : Type} (T : MSFTree e α)
    (p : Equiv.Perm (Fin e)) : (T.traceVars p).card ≤ 2 * T.depth := by
  induction T with
  | leaf _ => simp [MSFTree.traceVars, MSFTree.depth]
  | node i j l r ihl ihr =>
    dsimp only [MSFTree.traceVars, MSFTree.depth]
    have hpair : ({i, j} : Finset (Fin e)).card ≤ 2 := Finset.card_insert_le _ _
    have hu := Finset.card_union_le ({i, j} : Finset (Fin e))
      (if (p i).val < (p j).val then l.traceVars p else r.traceVars p)
    split_ifs at hu ⊢
    · omega
    · omega

theorem MSFTree.eval_eq_of_not_mem_traceVars {e : ℕ} {α : Type} (T : MSFTree e α)
    (p q : Equiv.Perm (Fin e)) (iStar : Fin e) (hnot : iStar ∉ T.traceVars p)
    (hagree : ∀ a b : Fin e, a ≠ iStar → b ≠ iStar →
      ((q a).val < (q b).val ↔ (p a).val < (p b).val)) :
    T.eval q = T.eval p := by
  induction T with
  | leaf _ => rfl
  | node a b l r ihl ihr =>
    dsimp only [MSFTree.traceVars] at hnot
    have han : a ≠ iStar := fun h => hnot (Finset.mem_union_left _ (by simp [h]))
    have hbn : b ≠ iStar := fun h => hnot (Finset.mem_union_left _ (by simp [h]))
    have hsub : iStar ∉ if (p a).val < (p b).val then l.traceVars p else r.traceVars p :=
      fun h => hnot (Finset.mem_union_right _ h)
    dsimp only [MSFTree.eval]
    by_cases hlt : (p a).val < (p b).val
    · have hltq : (q a).val < (q b).val := (hagree a b han hbn).mpr hlt
      simp only [hlt, ↓reduceIte] at hsub ⊢
      simp only [hltq, ↓reduceIte]
      exact ihl hsub
    · have hltq : ¬ ((q a).val < (q b).val) := fun h => hlt ((hagree a b han hbn).mp h)
      simp only [hlt, ↓reduceIte] at hsub ⊢
      simp only [hltq, ↓reduceIte]
      exact ihr hsub

private theorem exists_perm_min_and_max {e : ℕ} (iStar : Fin e) :
    (∃ pMin : Equiv.Perm (Fin e), pMin iStar = ⟨0, Nat.zero_lt_of_lt iStar.isLt⟩ ∧
      ∀ a b : Fin e, a ≠ iStar → b ≠ iStar → ((pMin a).val < (pMin b).val ↔ a.val < b.val)) ∧
    (∃ pMax : Equiv.Perm (Fin e),
      pMax iStar = ⟨e - 1, Nat.sub_lt (Nat.zero_lt_of_lt iStar.isLt) Nat.one_pos⟩ ∧
      ∀ a b : Fin e, a ≠ iStar → b ≠ iStar → ((pMax a).val < (pMax b).val ↔ a.val < b.val)) := by
  have hepos : 0 < e := Nat.zero_lt_of_lt iStar.isLt
  let fMin : Fin e → Fin e := fun j =>
    if j = iStar then ⟨0, hepos⟩
    else if hlt : j.val < iStar.val then ⟨j.val + 1, by have := iStar.isLt; omega⟩
    else j
  have hfMin_pos : ∀ x : Fin e, x ≠ iStar → 0 < (fMin x).val := fun x hx => by
    dsimp only [fMin]
    simp only [hx, ↓reduceIte]
    split_ifs with hlt
    · simp
    · have hxne : x.val ≠ iStar.val := fun h => hx (Fin.ext h)
      omega
  have hfMin_inj : Function.Injective fMin := fun a b hab => by
    by_cases ha : a = iStar <;> by_cases hb : b = iStar
    · exact ha.trans hb.symm
    · have h0 : (fMin a).val = 0 := by simp [fMin, ha]
      have hpos := hfMin_pos b hb
      rw [← hab, h0] at hpos
      omega
    · have h0 : (fMin b).val = 0 := by simp [fMin, hb]
      have hpos := hfMin_pos a ha
      rw [hab, h0] at hpos
      omega
    dsimp only [fMin] at hab
    simp only [ha, hb, ↓reduceIte] at hab
    split_ifs at hab with h1 h2
    · exact Fin.ext (by have := congrArg Fin.val hab; simp at this; omega)
    · have hne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
      have := congrArg Fin.val hab; simp at this; omega
    · have hne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
      have := congrArg Fin.val hab; simp at this; omega
    · exact hab
  let pMin := Equiv.ofBijective fMin
    ((Fintype.bijective_iff_injective_and_card fMin).mpr ⟨hfMin_inj, rfl⟩)
  let fMax : Fin e → Fin e := fun j =>
    if j = iStar then ⟨e - 1, Nat.sub_lt hepos Nat.one_pos⟩
    else if hlt : j.val < iStar.val then j
    else ⟨j.val - 1, by have := j.isLt; omega⟩
  have hfMax_lt : ∀ x : Fin e, x ≠ iStar → (fMax x).val < e - 1 := fun x hx => by
    dsimp only [fMax]
    simp only [hx, ↓reduceIte]
    split_ifs with hlt
    · have hxlt := x.isLt; have := iStar.isLt; omega
    · have hxlt := x.isLt
      have hxne : x.val ≠ iStar.val := fun h => hx (Fin.ext h)
      dsimp only
      omega
  have hfMax_inj : Function.Injective fMax := fun a b hab => by
    by_cases ha : a = iStar <;> by_cases hb : b = iStar
    · exact ha.trans hb.symm
    · have he1 : (fMax a).val = e - 1 := by simp [fMax, ha]
      have hlt := hfMax_lt b hb
      rw [← hab, he1] at hlt
      omega
    · have he1 : (fMax b).val = e - 1 := by simp [fMax, hb]
      have hlt := hfMax_lt a ha
      rw [hab, he1] at hlt
      omega
    dsimp only [fMax] at hab
    simp only [ha, hb, ↓reduceIte] at hab
    split_ifs at hab with h1 h2
    · exact hab
    · have hne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
      have hb_lt := b.isLt
      have := congrArg Fin.val hab; dsimp only at this; omega
    · have hne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
      have ha_lt := a.isLt
      have := congrArg Fin.val hab; dsimp only at this; omega
    · exact Fin.ext (by
        have ha_ne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
        have hb_ne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
        have := congrArg Fin.val hab; simp at this; omega)
  let pMax := Equiv.ofBijective fMax
    ((Fintype.bijective_iff_injective_and_card fMax).mpr ⟨hfMax_inj, rfl⟩)
  refine ⟨⟨pMin, ?_, ?_⟩, ⟨pMax, ?_, ?_⟩⟩
  · simp [pMin, fMin]
  · intro a b ha hb
    simp only [pMin, Equiv.ofBijective_apply, fMin, ha, hb, ↓reduceIte]
    have ha_ne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
    have hb_ne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
    split_ifs <;> simp <;> omega
  · simp [pMax, fMax]
  · intro a b ha hb
    simp only [pMax, Equiv.ofBijective_apply, fMax, ha, hb, ↓reduceIte]
    have ha_ne : a.val ≠ iStar.val := fun h => ha (Fin.ext h)
    have hb_ne : b.val ≠ iStar.val := fun h => hb (Fin.ext h)
    split_ifs <;> simp <;> omega

/-- General cycle-cover lower bound: if every edge of `ends : Fin e → Sym2 (Fin n)` has
distinct endpoints and lies on a simple cycle, then `e ≤ 2 * optDepth ends`. -/
theorem edges_le_two_mul_optDepth_of_all_on_cycle {e n : ℕ}
    (ends : Fin e → Sym2 (Fin n)) (hnoloop : ∀ i : Fin e, ¬ (ends i).IsDiag)
    (hcyc : ∀ i : Fin e, ∀ a b : Fin n, ends i = s(a, b) →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e)) a b) :
    e ≤ 2 * optDepth ends := by
  by_contra hlt
  have hcard : 2 * optDepth ends < e := by omega
  obtain ⟨T, hcorr, hd⟩ := exists_opt_msfDT ends
  rw [MSFDT.correct_iff] at hcorr
  let p0 : Equiv.Perm (Fin e) := Equiv.refl _
  have htv_lt : (T.traceVars p0).card < Finset.univ.card (α := Fin e) := by
    have := T.card_traceVars_le p0
    rw [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨iStar, _, hiStar⟩ := Finset.exists_mem_notMem_of_card_lt_card htv_lt
  obtain ⟨⟨pMin, hpMin0, hpMin_ord⟩, ⟨pMax, hpMaxE, hpMax_ord⟩⟩ :=
    exists_perm_min_and_max iStar
  have hevMin : T.eval pMin = T.eval p0 :=
    T.eval_eq_of_not_mem_traceVars p0 pMin iStar hiStar fun a b ha hb => by
      simpa [p0] using hpMin_ord a b ha hb
  have hevMax : T.eval pMax = T.eval p0 :=
    T.eval_eq_of_not_mem_traceVars p0 pMax iStar hiStar fun a b ha hb => by
      simpa [p0] using hpMax_ord a b ha hb
  have huEq : Cslib.Multigraph.msf ends pMin Finset.univ =
      Cslib.Multigraph.msf ends pMax Finset.univ := by
    rw [← hcorr pMin, ← hcorr pMax, hevMin, hevMax]
  induction hi : ends iStar using Sym2.ind with
  | _ a b =>
    have hin : iStar ∈ Cslib.Multigraph.msf ends pMin Finset.univ := by
      rw [Cslib.Multigraph.mem_msf_iff pMin hi]
      refine ⟨Finset.mem_univ _, fun hc => ?_⟩
      have hemp : {f | f ∈ (Finset.univ : Finset (Fin e)) ∧ pMin f < pMin iStar} = ∅ := by
        ext x
        simp [Fin.lt_def, hpMin0]
      rw [hemp, Cslib.Multigraph.joins_empty_iff] at hc
      subst hc
      exact hnoloop iStar (by simp [hi])
    have hout : iStar ∉ Cslib.Multigraph.msf ends pMax Finset.univ := by
      refine Cslib.Multigraph.notMem_msf_of_joins (w := pMax)
        (X := (Finset.univ.erase iStar : Finset (Fin e))) (by simp) (fun f hf => ?_) hi
        (hcyc iStar a b hi)
      rw [Finset.coe_erase, Set.mem_sdiff, Set.mem_singleton_iff] at hf
      change (pMax f).val < (pMax iStar).val
      rw [hpMaxE]
      have he_pos : 0 < e := Nat.zero_lt_of_lt iStar.isLt
      have hlt_val : (pMax f).val < e := (pMax f).isLt
      have hne : (pMax f).val ≠ e - 1 := fun he => hf.2 (pMax.injective (by
        rw [hpMaxE]; exact Fin.ext he))
      dsimp only
      omega
    exact hout (huEq ▸ hin)

private theorem nat_cycle_edge_on_cycle {e n : ℕ} (ends : Fin e → Sym2 (Fin n))
    (k : ℕ) (hk3 : 3 ≤ k) (hkn : k ≤ n)
    (hverts : ∀ t : Fin k, ∀ _ht : t.val + 1 < k,
      ∃ i : Fin e, ends i = s(⟨t.val, Nat.lt_of_lt_of_le t.isLt hkn⟩, ⟨t.val + 1, by omega⟩))
    (hwrap : ∃ i : Fin e, ends i = s(⟨0, by omega⟩, ⟨k - 1, by omega⟩))
    (hother : ∀ i : Fin e, ∀ v ∈ ends i, v.val < k) :
    ∀ i : Fin e, ∀ a b : Fin n, ends i = s(a, b) →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e)) a b := by
  classical
  let cEdge : ℕ → Fin e := fun t =>
    if ht : t + 1 < k then (hverts ⟨t, by omega⟩ ht).choose else hwrap.choose
  have hcEdge_sym : ∀ t (ht : t + 1 < k),
      ends (cEdge t) = s(⟨t, by omega⟩, ⟨t + 1, by omega⟩) := fun t ht => by
    simp only [cEdge, ht, ↓reduceDIte]
    exact (hverts ⟨t, by omega⟩ ht).choose_spec
  have hcWrap_sym : ends (cEdge (k - 1)) = s(⟨0, by omega⟩, ⟨k - 1, by omega⟩) := by
    have hnot : ¬ (k - 1 + 1 < k) := by omega
    simp only [cEdge, hnot, ↓reduceDIte]
    exact hwrap.choose_spec
  have conn_chain : ∀ (i : Fin e) (a b : ℕ), ∀ hab : a ≤ b, ∀ hbk : b < k,
      (∀ t, a ≤ t → t < b → cEdge t ≠ i) →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e))
        ⟨a, by omega⟩ ⟨b, by omega⟩ := by
    intro i a b hab hbk havoid
    induction b with
    | zero =>
      have : a = 0 := by omega
      subst this; exact Cslib.Multigraph.Joins.refl _
    | succ b ih =>
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact Cslib.Multigraph.Joins.refl _
      · have ih' := ih (by omega) (by omega) fun t ht1 ht2 => havoid t ht1 (by omega)
        have he_mem : cEdge b ∈ ((Finset.univ.erase i : Finset (Fin e)) : Set (Fin e)) :=
          Finset.mem_coe.mpr (Finset.mem_erase.mpr
            ⟨havoid b (by omega) (Nat.lt_succ_self b), Finset.mem_univ _⟩)
        exact ih'.trans (Cslib.Multigraph.Joins.of_mem he_mem (hcEdge_sym b hbk))
  have conn_wrap : ∀ (i : Fin e), cEdge (k - 1) ≠ i →
      Cslib.Multigraph.Joins ends (Finset.univ.erase i : Finset (Fin e))
        ⟨0, by omega⟩ ⟨k - 1, by omega⟩ := fun i hne =>
    Cslib.Multigraph.Joins.of_mem
      (Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ _⟩)) hcWrap_sym
  intro i a b hab
  have h1 : a.val < k := hother i a (hab ▸ Sym2.mem_mk_left a b)
  have h2 : b.val < k := hother i b (hab ▸ Sym2.mem_mk_right a b)
  by_cases hcy : ∃ t < k, cEdge t = i
  · obtain ⟨t, htk, rfl⟩ := hcy
    by_cases htk1 : t + 1 < k
    · have hne_all : ∀ s < k, s ≠ t → cEdge s ≠ cEdge t := fun s hs hst h => by
        by_cases hs1 : s + 1 < k
        · have hseq : s((⟨s, by omega⟩ : Fin n), ⟨s + 1, by omega⟩) =
              s((⟨t, by omega⟩ : Fin n), ⟨t + 1, by omega⟩) :=
            (hcEdge_sym s hs1).symm.trans (h ▸ hcEdge_sym t htk1)
          rcases Sym2.eq_iff.mp hseq with ⟨e1, _⟩ | ⟨e1, e2⟩
          · exact hst (congrArg Fin.val e1)
          · have v1 : s = t + 1 := congrArg Fin.val e1
            have v2 : s + 1 = t := congrArg Fin.val e2
            omega
        · have hsk : s = k - 1 := by omega
          subst hsk
          have hseq : s((⟨0, by omega⟩ : Fin n), ⟨k - 1, by omega⟩) =
              s((⟨t, by omega⟩ : Fin n), ⟨t + 1, by omega⟩) :=
            hcWrap_sym.symm.trans (h ▸ hcEdge_sym t htk1)
          rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨e1, _⟩
          · have v1 : 0 = t := congrArg Fin.val e1
            have v2 : k - 1 = t + 1 := congrArg Fin.val e2
            omega
          · have v1 : 0 = t + 1 := congrArg Fin.val e1
            omega
      have p1 := conn_chain (cEdge t) (t + 1) (k - 1) (by omega) (by omega) fun s hs1 hs2 =>
        hne_all s (by omega) (by omega)
      have p2 := (conn_wrap (cEdge t) (hne_all (k - 1) (by omega) (by omega))).symm
      have p3 := conn_chain (cEdge t) 0 t (Nat.zero_le _) (by omega) fun s _ hs2 =>
        hne_all s (by omega) (by omega)
      have hconn_tt1 := (p1.trans (p2.trans p3)).symm
      have hseq : s(⟨t, by omega⟩, ⟨t + 1, by omega⟩) = s(a, b) :=
        (hcEdge_sym t htk1).symm.trans hab
      rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact hconn_tt1
      · rw [← e1, ← e2]; exact hconn_tt1.symm
    · have htk_eq : t = k - 1 := by omega
      subst htk_eq
      have hne_pre : ∀ s, s + 1 < k → cEdge s ≠ cEdge (k - 1) := fun s hs h => by
        have hseq : s((⟨s, by omega⟩ : Fin n), ⟨s + 1, by omega⟩) =
            s((⟨0, by omega⟩ : Fin n), ⟨k - 1, by omega⟩) :=
          (hcEdge_sym s hs).symm.trans (h ▸ hcWrap_sym)
        rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨_, e2⟩
        · have v1 : s = 0 := congrArg Fin.val e1
          have v2 : s + 1 = k - 1 := congrArg Fin.val e2
          omega
        · have v2 : s + 1 = 0 := congrArg Fin.val e2
          omega
      have p := conn_chain (cEdge (k - 1)) 0 (k - 1) (Nat.zero_le _) (by omega)
        fun s _ hs => hne_pre s (by omega)
      have hseq : s(⟨0, by omega⟩, ⟨k - 1, by omega⟩) = s(a, b) := hcWrap_sym.symm.trans hab
      rcases Sym2.eq_iff.mp hseq with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [← e1, ← e2]; exact p
      · rw [← e1, ← e2]; exact p.symm
  · have hall : ∀ s, s < k - 1 → cEdge s ≠ i := fun s hs h => hcy ⟨s, by omega, h⟩
    have p1 := conn_chain i 0 a.val (Nat.zero_le _) h1 fun s _ hs => hall s (by omega)
    have p2 := conn_chain i 0 b.val (Nat.zero_le _) h2 fun s _ hs => hall s (by omega)
    exact p1.symm.trans p2

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Proposition 5.1 (§5.1, p. 25):
for `3 ≤ m`, `3 ≤ n`, and `m ≤ n.choose 2`, `m ≤ 2 * optDepthMN m n`. -/
theorem le_two_mul_optDepthMN {m n : ℕ} (hm : 3 ≤ m) (hn : 3 ≤ n) (hle : m ≤ n.choose 2) :
    m ≤ 2 * optDepthMN m n := by
  classical
  let k := min m n
  have hk3 : 3 ≤ k := le_min hm hn
  have hkm : k ≤ m := min_le_left m n
  have hkn : k ≤ n := min_le_right m n
  let cycIdxs : List (Fin (n.choose 2)) :=
    (List.finRange (k - 1)).map (fun a =>
      ⟨pairIdx a.val (a.val + 1), pairIdx_lt_choose_two (Nat.lt_succ_self _) (by omega)⟩) ++
    [⟨pairIdx 0 (k - 1), pairIdx_lt_choose_two (by omega) (by omega)⟩]
  have hpair_inj : ∀ {a₁ a₂ b₁ b₂ : ℕ}, a₁ < b₁ → b₁ < n → a₂ < b₂ → b₂ < n →
      pairIdx a₁ b₁ = pairIdx a₂ b₂ → a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ a₂ b₁ b₂ h11 h12 h21 h22 heq
    have g1 := getElem_allPairs_pairIdx (r := n) (a := ⟨a₁, by omega⟩) (b := ⟨b₁, h12⟩) h11
    have g2 := getElem_allPairs_pairIdx (r := n) (a := ⟨a₂, by omega⟩) (b := ⟨b₂, h22⟩) h21
    have hprod : (allPairs n)[pairIdx a₁ b₁]'(by
        rw [length_allPairs]; exact pairIdx_lt_choose_two h11 h12) =
        (allPairs n)[pairIdx a₂ b₂]'(by
        rw [length_allPairs]; exact pairIdx_lt_choose_two h21 h22) := by
      simp only [heq]
    rw [g1, g2] at hprod
    exact ⟨congrArg (fun p : Fin n × Fin n => p.1.val) hprod,
      congrArg (fun p : Fin n × Fin n => p.2.val) hprod⟩
  have hcyc_nd : cycIdxs.Nodup := by
    refine List.nodup_append.mpr ⟨?_, List.nodup_singleton _, fun x hx y hy hxy => ?_⟩
    · refine (List.nodup_finRange (k - 1)).map fun a b hab => ?_
      have hidx : pairIdx a.val (a.val + 1) = pairIdx b.val (b.val + 1) := congrArg Fin.val hab
      have heq := hpair_inj (Nat.lt_succ_self _) (by omega) (Nat.lt_succ_self _) (by omega) hidx
      exact Fin.ext heq.1
    · rw [List.mem_map] at hx
      rw [List.mem_singleton] at hy
      obtain ⟨a, _, rfl⟩ := hx
      subst hy
      have hidx : pairIdx a.val (a.val + 1) = pairIdx 0 (k - 1) := congrArg Fin.val hxy
      have heq := hpair_inj (Nat.lt_succ_self _) (by omega) (by omega) (by omega) hidx
      omega
  have hcyc_len : cycIdxs.length = k := by
    simp only [cycIdxs, List.length_append, List.length_map, List.length_finRange,
      List.length_singleton]
    omega
  let rest : List (Fin (n.choose 2)) :=
    (List.finRange (n.choose 2)).filter fun x => x ∉ cycIdxs
  have hrest_part : cycIdxs.toFinset ∪ rest.toFinset = Finset.univ := by
    ext x
    simp only [Finset.mem_union, List.mem_toFinset, Finset.mem_univ, iff_true, rest,
      List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
    exact em (x ∈ cycIdxs)
  have hrest_disj : Disjoint cycIdxs.toFinset rest.toFinset := by
    rw [Finset.disjoint_left]
    intro x hx hrx
    simp only [List.mem_toFinset, rest, List.mem_filter, decide_eq_true_eq] at hx hrx
    exact hrx.2 hx
  have hrest_len : k + rest.length = n.choose 2 := by
    rw [← hcyc_len, ← List.toFinset_card_of_nodup hcyc_nd,
      ← List.toFinset_card_of_nodup ((List.nodup_finRange _).filter _),
      ← Finset.card_union_of_disjoint hrest_disj, hrest_part, Finset.card_univ, Fintype.card_fin]
  let extra := rest.take (m - k)
  have hextra_len : extra.length = m - k := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  let chosen := cycIdxs ++ extra
  have hchosen_nd : chosen.Nodup := by
    refine List.nodup_append.mpr ⟨hcyc_nd,
      ((List.nodup_finRange _).filter _).sublist (List.take_sublist _ _),
      fun x hx y hy hxy => ?_⟩
    subst hxy
    have hyr := List.mem_of_mem_take hy
    simp only [rest, List.mem_filter, decide_eq_true_eq] at hyr
    exact hyr.2 hx
  have hchosen_len : chosen.length = m := by
    simp only [chosen, extra, List.length_append, List.length_take, hcyc_len]
    omega
  let S : Finset (Fin (n.choose 2)) := chosen.toFinset
  have hS_card : S.card = m := by
    rw [List.toFinset_card_of_nodup hchosen_nd, hchosen_len]
  let mask := maskOfFinset S
  have hmask_lt : mask < 2 ^ n.choose 2 := maskOfFinset_lt S
  have hlen_mask : (maskEdgePairs n mask).length = m := by
    rw [length_maskEdgePairs]
    have hfilt : ((Finset.range (n.choose 2)).filter fun j =>
        mask.testBit j) = S.map ⟨Fin.val, Fin.val_injective⟩ := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_map,
        Function.Embedding.coeFn_mk, mask, testBit_maskOfFinset, decide_eq_true_eq]
      constructor
      · rintro ⟨_, hj', hmem⟩
        exact ⟨⟨j, hj'⟩, hmem, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.isLt, x.isLt, hx⟩
    rw [hfilt, Finset.card_map, hS_card]
  have hmem_pair : ∀ x ∈ cycIdxs, (allPairs n)[x.val]'(by
      rw [length_allPairs]; exact x.isLt) ∈ maskEdgePairs n mask := by
    intro x hx
    have hlt_all : x.val < (allPairs n).length := by rw [length_allPairs]; exact x.isLt
    rw [mem_maskEdgePairs_iff]
    refine ⟨allPairs_lt (List.getElem_mem hlt_all), ?_⟩
    rw [pairIdx_getElem_allPairs hlt_all]
    simp only [mask, testBit_maskOfFinset, decide_eq_true_eq]
    exact ⟨x.isLt, List.mem_toFinset.mpr (List.mem_append_left _ hx)⟩
  let ends := endsOfMask n mask
  have hverts : ∀ t : Fin k, ∀ _ht : t.val + 1 < k,
      ∃ i : Fin (maskEdgePairs n mask).length,
        ends i = s(⟨t.val, Nat.lt_of_lt_of_le t.isLt hkn⟩, ⟨t.val + 1, by omega⟩) := by
    intro t ht
    let idx : Fin (n.choose 2) :=
      ⟨pairIdx t.val (t.val + 1), pairIdx_lt_choose_two (Nat.lt_succ_self _) (by omega)⟩
    have hidx_cyc : idx ∈ cycIdxs := by
      refine List.mem_append_left _ (List.mem_map.mpr ?_)
      exact ⟨⟨t.val, by omega⟩, List.mem_finRange _, rfl⟩
    have hp := hmem_pair idx hidx_cyc
    obtain ⟨pos, hpos⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨pos, hpos.1⟩, ?_⟩
    dsimp only [ends, endsOfMask]
    have hget := getElem_allPairs_pairIdx (r := n)
      (a := ⟨t.val, by omega⟩) (b := ⟨t.val + 1, by omega⟩) (Nat.lt_succ_self _)
    simp only [Fin.getElem_fin, hpos.2, idx]
    rw [hget]
  have hwrap : ∃ i : Fin (maskEdgePairs n mask).length,
      ends i = s(⟨0, by omega⟩, ⟨k - 1, by omega⟩) := by
    let idx : Fin (n.choose 2) :=
      ⟨pairIdx 0 (k - 1), pairIdx_lt_choose_two (by omega) (by omega)⟩
    have hidx_cyc : idx ∈ cycIdxs := List.mem_append_right _ (List.mem_singleton.mpr rfl)
    have hp := hmem_pair idx hidx_cyc
    obtain ⟨pos, hpos⟩ := List.mem_iff_getElem.mp hp
    refine ⟨⟨pos, hpos.1⟩, ?_⟩
    dsimp only [ends, endsOfMask]
    have hget := getElem_allPairs_pairIdx (r := n)
      (a := ⟨0, by omega⟩) (b := ⟨k - 1, by omega⟩) (by dsimp only; omega)
    simp only [Fin.getElem_fin, hpos.2, idx]
    rw [hget]
  have hother : ∀ i : Fin (maskEdgePairs n mask).length, ∀ v ∈ ends i, v.val < k := by
    intro i v hv
    by_cases hmn : m ≤ n
    · have hkm_eq : k = m := min_eq_left hmn
      have hmt : m - k = 0 := by omega
      have hmem := List.getElem_mem i.isLt
      obtain ⟨hlt, htb⟩ := mem_maskEdgePairs_iff.mp hmem
      simp only [mask, testBit_maskOfFinset, decide_eq_true_eq] at htb
      obtain ⟨hj2, hmemS⟩ := htb
      let j := pairIdx (maskEdgePairs n mask)[i.val].1.val (maskEdgePairs n mask)[i.val].2.val
      have hj : j < (allPairs n).length := by rw [length_allPairs]; exact hj2
      have hmemc : (⟨j, hj2⟩ : Fin (n.choose 2)) ∈ cycIdxs := by
        have hm' : (⟨j, hj2⟩ : Fin (n.choose 2)) ∈ chosen := List.mem_toFinset.mp hmemS
        simpa [chosen, extra, hmt] using hm'
      simp only [cycIdxs, List.mem_append, List.mem_map, List.mem_finRange,
        List.mem_singleton] at hmemc
      have hend : (maskEdgePairs n mask)[i.val] = (allPairs n)[j]'hj :=
        (getElem_allPairs_pairIdx hlt).symm
      dsimp only [ends, endsOfMask] at hv
      simp only [Fin.getElem_fin, hend] at hv
      rcases hmemc with ⟨a, _, ha⟩ | heq
      · have hjv : j = pairIdx a.val (a.val + 1) := congrArg Fin.val ha.symm
        have ha_lt := a.isLt
        have hga := getElem_allPairs_pairIdx (r := n)
          (a := ⟨a.val, by omega⟩) (b := ⟨a.val + 1, by omega⟩) (Nat.lt_succ_self _)
        have hpair : (allPairs n)[j]'hj = (⟨a.val, by omega⟩, ⟨a.val + 1, by omega⟩) := by
          simpa [hjv] using hga
        rw [hpair] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> dsimp only <;> omega
      · have hjv : j = pairIdx 0 (k - 1) := congrArg Fin.val heq
        have hga := getElem_allPairs_pairIdx (r := n)
          (a := ⟨0, by omega⟩) (b := ⟨k - 1, by omega⟩) (by dsimp only; omega)
        have hpair : (allPairs n)[j]'hj = (⟨0, by omega⟩, ⟨k - 1, by omega⟩) := by
          simpa [hjv] using hga
        rw [hpair] at hv
        rcases Sym2.mem_iff.mp hv with rfl | rfl <;> dsimp only <;> omega
    · have hkn_eq : k = n := min_eq_right (by omega)
      rw [hkn_eq]
      exact v.isLt
  have hcyc_G := nat_cycle_edge_on_cycle ends k hk3 hkn hverts hwrap hother
  have hlb := edges_le_two_mul_optDepth_of_all_on_cycle ends
    ((isSimple_iff _).mp (endsOfMask_isSimple n mask)).1 hcyc_G
  rw [← hlen_mask]
  exact hlb.trans (Nat.mul_le_mul_left 2
    (optDepth_endsOfMask_le_optDepthMN hmask_lt le_rfl))

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Proposition 5.2 (§5.1, p. 25):
`optDepthMN m₁ n ≤ optDepthMN m₂ n` when `m₁ ≤ m₂` (coupled with `optDepthMN_eq_exact` and
`optDepth_le_of_submask` for supergraph monotonicity when `m₂ ≤ n.choose 2`). -/
theorem optDepthMN_mono_m {m₁ m₂ n : ℕ} (h : m₁ ≤ m₂) : optDepthMN m₁ n ≤ optDepthMN m₂ n := by
  obtain ⟨mask, hmask, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m₁ n
  rw [← heq]
  exact optDepth_endsOfMask_le_optDepthMN hmask (hlen.trans h)

/-- Step toward Theorem 5.8 of [PettieRamachandran2002] (#8624), Proposition 5.2 (§5.1, p. 25):
`optDepthMN m n₁ ≤ optDepthMN m n₂` when `n₁ ≤ n₂`. -/
theorem optDepthMN_mono_n {m n₁ n₂ : ℕ} (h : n₁ ≤ n₂) : optDepthMN m n₁ ≤ optDepthMN m n₂ := by
  obtain ⟨mask, hmask, hlen, heq⟩ := exists_endsOfMask_eq_optDepthMN m n₁
  rw [← heq, optDepth_endsOfMask_le h hmask]
  have hpow : 2 ^ n₁.choose 2 ≤ 2 ^ n₂.choose 2 :=
    Nat.pow_le_pow_right (by omega) (Nat.choose_le_choose 2 h)
  have hlen2 : (maskEdgePairs n₂ mask).length = (maskEdgePairs n₁ mask).length := by
    rw [maskEdgePairs_cast h hmask, List.length_map]
  exact optDepth_endsOfMask_le_optDepthMN (hmask.trans_le hpow) (hlen2 ▸ hlen)

end Cslib.Query.MinimumSpanningForest
