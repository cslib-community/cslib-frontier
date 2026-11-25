/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.DataStructure.Dictionary.CellProbe.LowerBound.PoolSymmetry
import CslibFrontier.Probability.PMF.Map
import Mathlib.GroupTheory.Perm.Support
import Mathlib.Logic.Equiv.Fintype

/-!
# Section 8.1 Observation/Target Fiber Bound

Stabilizer-orbit bound (`fiber_le_queryFreePoolDist`) upper-bounding the conditional probability
mass of any `(obs8, target8)` fiber under the query-free pool distribution `innerPoolDist` using the
equivariance action from `LowerBound.PoolSymmetry`.

## Main definitions

* `Cslib.DataStructure.Dictionary.CellProbe.obs8`: observable tuple `(a, B, d)`.
* `Cslib.DataStructure.Dictionary.CellProbe.target8`: secret target `(K \ D, v|_{A ∪ B ∪ K})`.

## Main results

* `Cslib.DataStructure.Dictionary.CellProbe.fiber_le_queryFreePoolDist`: point-mass upper bound for
  `target8` conditioned on `obs8`.
-/

public section

open scoped BigOperators ENNReal

namespace Cslib.DataStructure.Dictionary.CellProbe

open Cslib.DataStructure Cslib.DataStructure.Dictionary
open Cslib.Probability

/-! #### Section 8 observation/target fiber bound and 6-piece prefix-free message -/

/-- Public observation `(a, B, d)` in the Section 8.1 communication protocol. -/
@[expose] def obs8 {U V n : ℕ} (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n)
    (sb : HardKeyValSeed U V n × Finset (Fin U)) :
    (Fin m → Fin U) × Finset (Fin U) × (Fin m → Fin U) :=
  (fun r => segInsertedKeys sb.1.keys t₀ m ht₀ r,
   sb.2,
   fun r => segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀ r)

private def obsFixedSet {U m : ℕ}
    (o : (Fin m → Fin U) × Finset (Fin U) × (Fin m → Fin U)) : Finset (Fin U) :=
  Finset.univ.image o.1 ∪ o.2.1 ∪ Finset.univ.image o.2.2

/-- Secret target `(K \ D, v|_{A ∪ B ∪ K})` recovered by the Section 8.1 protocol. -/
@[expose] def target8 {U V n : ℕ} (t₀ m : ℕ) (ht₀ : t₀ + m ≤ n)
    (sb : HardKeyValSeed U V n × Finset (Fin U)) :
    Finset (Fin U) × (Fin U → Option (Fin V)) :=
  (sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀) \
      Finset.univ.image (segDeletedKeys sb.1.keys sb.1.delPerm t₀ m ht₀),
   fun u => if u ∈ sb.1.activeKeys t₀ (Nat.le_of_add_right_le ht₀) ∪
       sb.1.insertedSet t₀ m ht₀ ∪ sb.2 then some (sb.1.kv u) else none)

private theorem ofSubtype_trans {α : Type*} {p : α → Prop} [DecidablePred p]
    (σ₁ σ₂ : Equiv.Perm {x // p x}) :
    (Equiv.Perm.ofSubtype (σ₁.trans σ₂)).toEmbedding =
      (Equiv.Perm.ofSubtype σ₁).toEmbedding.trans (Equiv.Perm.ofSubtype σ₂).toEmbedding := by
  ext z
  by_cases hz : p z
  · simp only [Equiv.coe_toEmbedding, Function.Embedding.trans_apply,
      Equiv.Perm.ofSubtype_apply_of_mem _ hz, Equiv.trans_apply]
    exact (Equiv.Perm.ofSubtype_apply_of_mem σ₂ (σ₁ ⟨z, hz⟩).2).symm
  · simp only [Equiv.coe_toEmbedding, Function.Embedding.trans_apply,
      Equiv.Perm.ofSubtype_apply_of_not_mem _ hz]

private theorem ofSubtype_symm_eq {α : Type*} {p : α → Prop} [DecidablePred p]
    (σ : Equiv.Perm {x // p x}) :
    (Equiv.Perm.ofSubtype σ.symm : Equiv.Perm α) = (Equiv.Perm.ofSubtype σ).symm :=
  Equiv.ext fun u => (Equiv.Perm.ofSubtype σ).injective (by
    rw [Equiv.apply_symm_apply]
    by_cases hu : p u
    · rw [Equiv.Perm.ofSubtype_apply_of_mem _ hu,
        Equiv.Perm.ofSubtype_apply_of_mem _ (σ.symm ⟨u, hu⟩).2, σ.apply_symm_apply]
    · rw [Equiv.Perm.ofSubtype_apply_of_not_mem _ hu, Equiv.Perm.ofSubtype_apply_of_not_mem _ hu])

open Classical in
theorem fiber_le_queryFreePoolDist {U V n t₀ m g P_size : ℕ}
    (hU : 3 * n ≤ U) (hV : 1 ≤ V) (_hm_n : 2 * m ≤ n) (hg : g < m / 2) {ht₀ : t₀ + m ≤ n}
    (ctx : PoolCtx U V n t₀ m g P_size ht₀)
    (o : (Fin m → Fin U) × Finset (Fin U) × (Fin m → Fin U))
    (T : Finset (Fin U) × (Fin U → Option (Fin V))) :
    let μ_g := innerPoolDist (by omega) hV ctx.Fg ctx.hne
    let M_nat := (U - 3 * m).choose (n - m) * V ^ (n + 2 * m - g)
    ((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal ≤
      ((μ_g.map (obs8 t₀ m ht₀)) o).toReal / (M_nat : ℝ) := by
  dsimp only
  let _ : NeZero V := ⟨by omega⟩
  let _ : Nonempty (HardKeyValSeed U V n) := ⟨⟨Fin.castLEEmb (by omega), fun _ => ⟨0, hV⟩, 1⟩⟩
  let μ_g := innerPoolDist (by omega : 2 * n ≤ U) hV ctx.Fg ctx.hne
  let M_nat := (U - 3 * m).choose (n - m) * V ^ (n + 2 * m - g)
  have hM_pos : (0 : ℝ) < (M_nat : ℝ) := by
    dsimp only [M_nat]
    exact_mod_cast Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos hV)
  rw [le_div_iff₀ hM_pos]
  by_cases ho_card : o.2.1.card = m
  · let S_comp := Finset.univ \ obsFixedSet o
    let G := Equiv.Perm ↥S_comp × (Fin U → Fin V)
    let actG (γ : G) :
        (HardKeyValSeed U V n × Finset (Fin U)) ≃ (HardKeyValSeed U V n × Finset (Fin U)) :=
      (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2).prodCongr (Equiv.refl _)
    have hfix (π_sub : Equiv.Perm ↥S_comp) {x : Fin U} (hx : x ∈ obsFixedSet o) :
        Equiv.Perm.ofSubtype π_sub x = x :=
      Equiv.Perm.ofSubtype_apply_of_not_mem π_sub (by
        simp only [S_comp, Finset.mem_sdiff, hx, not_true_eq_false, and_false, not_false_eq_true])
    have hobs_fwd (γ : G) (sb : HardKeyValSeed U V n × Finset (Fin U))
        (ho : obs8 t₀ m ht₀ sb = o) : obs8 t₀ m ht₀ (actG γ sb) = o := by
      rcases sb with ⟨s, B⟩; rcases o with ⟨a_fn, B_set, d_fn⟩
      dsimp only [obs8] at ho
      rcases Prod.mk.inj ho with ⟨ha, hBd⟩
      rcases Prod.mk.inj hBd with ⟨hB, hd⟩
      subst hB
      change obs8 t₀ m ht₀ (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s, B) = (a_fn, B, d_fn)
      dsimp only [obs8]
      refine Prod.ext (funext fun r => ?_) (Prod.ext rfl (funext fun r => ?_))
      · dsimp only
        have hr_mem : segInsertedKeys s.keys t₀ m ht₀ r ∈ obsFixedSet (a_fn, B, d_fn) :=
          Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrFun ha.symm r⟩))
        have h1 : segInsertedKeys (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s).keys
            t₀ m ht₀ r = Equiv.Perm.ofSubtype γ.1 (segInsertedKeys s.keys t₀ m ht₀ r) := by
          simp only [segInsertedKeys_apply, actSeed8Equiv, Equiv.coe_fn_mk,
            Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
        rw [h1, hfix γ.1 hr_mem, ← ha]
      · dsimp only
        have hr_mem : segDeletedKeys s.keys s.delPerm t₀ m ht₀ r ∈
            obsFixedSet (a_fn, B, d_fn) :=
          Finset.mem_union_right _
            (Finset.mem_image.mpr ⟨r, Finset.mem_univ r, congrFun hd.symm r⟩)
        have h1 : segDeletedKeys (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s).keys
            (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s).delPerm t₀ m ht₀ r =
            Equiv.Perm.ofSubtype γ.1 (segDeletedKeys s.keys s.delPerm t₀ m ht₀ r) := by
          simp only [segDeletedKeys_apply, actSeed8Equiv, Equiv.coe_fn_mk,
            Function.Embedding.trans_apply, Equiv.coe_toEmbedding]
        rw [h1, hfix γ.1 hr_mem, ← hd]
    have hobs_iff (γ : G) (sb : HardKeyValSeed U V n × Finset (Fin U)) :
        obs8 t₀ m ht₀ (actG γ sb) = o ↔ obs8 t₀ m ht₀ sb = o := by
      refine ⟨fun h => ?_, hobs_fwd γ sb⟩
      let γ_inv : G := (γ.1.symm, fun u => -γ.2 (Equiv.Perm.ofSubtype γ.1 u))
      have hsymm : actG γ_inv (actG γ sb) = sb := by
        rcases sb with ⟨s, B⟩
        change (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1.symm) γ_inv.2
          (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s), B) = (s, B)
        rw [ofSubtype_symm_eq]
        refine Prod.ext ?_ rfl
        cases s
        simp only [actSeed8Equiv, Equiv.coe_fn_mk, HardKeyValSeed.mk.injEq, and_true]
        exact ⟨by ext i; simp only [Function.Embedding.trans_apply, Equiv.coe_toEmbedding,
            Equiv.symm_apply_apply],
          by funext u; simp only [Equiv.symm_symm, Equiv.symm_apply_apply, γ_inv,
            add_neg_cancel_right]⟩
      simpa only [hsymm] using hobs_fwd γ_inv (actG γ sb) h
    have hB_fix (π_sub : Equiv.Perm ↥S_comp) {B : Finset (Fin U)} (hBo : B = o.2.1) :
        B.map (Equiv.Perm.ofSubtype π_sub).toEmbedding = B := by
      ext x; simp only [Finset.mem_map, Equiv.coe_toEmbedding]
      refine ⟨fun ⟨y, hy, hyx⟩ => ?_, fun hx => ⟨x, hx, ?_⟩⟩
      · have hy_fix := hfix π_sub (Finset.mem_union_left _ (Finset.mem_union_right _ (hBo ▸ hy)))
        rwa [← hyx, hy_fix]
      · exact hfix π_sub (Finset.mem_union_left _ (Finset.mem_union_right _ (hBo ▸ hx)))
    have hμ_obs (γ : G) (sb : HardKeyValSeed U V n × Finset (Fin U))
        (ho : obs8 t₀ m ht₀ sb = o) : (μ_g (actG γ sb)).toReal = (μ_g sb).toReal := by
      rcases sb with ⟨s, B⟩
      have hBo : B = o.2.1 := (Prod.mk.inj (Prod.mk.inj ho).2).1
      change (μ_g (actSeed8Equiv (Equiv.Perm.ofSubtype γ.1) γ.2 s, B)).toReal = (μ_g (s, B)).toReal
      conv_lhs => rw [← hB_fix γ.1 hBo]
      exact toReal_innerPoolDist_actSeed8Equiv (by omega : 2 * n ≤ U) hV ctx _ γ.2 s B
    -- Orbit bound for any supported sb with obs8 sb = o
    have horbit_le (sb : HardKeyValSeed U V n × Finset (Fin U))
        (ho : obs8 t₀ m ht₀ sb = o) (hB_Fg : sb.2 ∈ ctx.Fg sb.1) :
        ((Finset.univ.filter fun γ : G => target8 t₀ m ht₀ (actG γ sb) = T).card : ℝ) *
          (M_nat : ℝ) ≤ (Fintype.card G : ℝ) := by
      rcases sb with ⟨s, B⟩; rcases T with ⟨K_rem, kv_opt⟩
      dsimp only at hB_Fg
      have hB_fg_props := Finset.mem_filter.mp (ctx.hFg s ▸ hB_Fg)
      have hB_pool : B ⊆ ctx.pool s := (Finset.mem_powersetCard.mp hB_fg_props.1).1
      have hB_card : B.card = m := (Finset.mem_powersetCard.mp hB_fg_props.1).2
      have hAB_card : (s.insertedSet t₀ m ht₀ ∩ B).card = g := hB_fg_props.2
      let ht₀_n : t₀ ≤ n := Nat.le_of_add_right_le ht₀
      let K₀ := s.activeKeys t₀ ht₀_n \ Finset.univ.image (segDeletedKeys s.keys s.delPerm t₀ m ht₀)
      have hK₀_card : K₀.card = n - m := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (segDeletedKeys_subset_activeKeys s ht₀),
          card_activeKeys s ht₀_n, card_deletedSet s ht₀]
      have hK₀_sub : K₀ ⊆ S_comp := fun u hu => by
        obtain ⟨huK, huD⟩ := Finset.mem_sdiff.mp hu
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, fun hu_fix => ?_⟩
        dsimp only [obsFixedSet] at hu_fix
        rcases Finset.mem_union.mp hu_fix with huAB | huD'
        · rcases Finset.mem_union.mp huAB with huA | huB
          · have ha_eq : o.1 = fun r => segInsertedKeys s.keys t₀ m ht₀ r :=
              (Prod.mk.inj ho).1.symm
            rw [ha_eq] at huA
            exact Finset.disjoint_left.mp (ctx.hdisj s) (ctx.hA s huA) huK
          · have hBo : o.2.1 = B := (Prod.mk.inj (Prod.mk.inj ho).2).1.symm
            exact Finset.disjoint_left.mp (ctx.hdisj s) (hB_pool (hBo ▸ huB)) huK
        · have hd_eq : o.2.2 = fun r => segDeletedKeys s.keys s.delPerm t₀ m ht₀ r :=
            (Prod.mk.inj (Prod.mk.inj ho).2).2.symm
          rw [hd_eq] at huD'
          exact huD huD'
      have hS_comp_ge : U - 3 * m ≤ S_comp.card := by
        have h1 : (Finset.univ.image o.1).card ≤ m :=
          Finset.card_image_le.trans (by simp only [Finset.card_univ, Fintype.card_fin, le_rfl])
        have h3 : (Finset.univ.image o.2.2).card ≤ m :=
          Finset.card_image_le.trans (by simp only [Finset.card_univ, Fintype.card_fin, le_rfl])
        have ho_le : (obsFixedSet o).card ≤ 3 * m :=
          (Finset.card_union_le _ _).trans (by
            have := Finset.card_union_le (Finset.univ.image o.1) o.2.1; omega)
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
          Finset.card_univ, Fintype.card_fin]
        omega
      let stab (K' : Finset (Fin U)) := Finset.univ.filter fun π_sub : Equiv.Perm ↥S_comp =>
        K₀.map (Equiv.Perm.ofSubtype π_sub).toEmbedding = K'
      have hstab_le : (stab K_rem).card * (U - 3 * m).choose (n - m) ≤
          Fintype.card (Equiv.Perm ↥S_comp) := by
        by_cases hKr : K_rem ∈ S_comp.powersetCard (n - m)
        · have hstab_eq (K' : Finset (Fin U)) (hK' : K' ∈ S_comp.powersetCard (n - m)) :
              (stab K_rem).card = (stab K').card := by
            let subSet (A : Finset (Fin U)) : Finset ↥S_comp := Finset.univ.filter fun x => x.1 ∈ A
            have hsub_card (A : Finset (Fin U)) (hA : A ∈ S_comp.powersetCard (n - m)) :
                (subSet A).card = n - m := by
              obtain ⟨hA_sub, hA_c⟩ := Finset.mem_powersetCard.mp hA
              rw [← hA_c]
              exact Finset.card_bij (fun x _ => x.1) (fun x hx => (Finset.mem_filter.mp hx).2)
                (fun _ _ _ _ h => Subtype.ext h) fun y hy =>
                  ⟨⟨y, hA_sub hy⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩, rfl⟩
            obtain ⟨σ_sub, hσ_sub_map⟩ := Equiv.Perm.exists_map_finset_eq
              (subSet K_rem) (subSet K') ((hsub_card K_rem hKr).trans (hsub_card K' hK').symm)
            have hσ_map : K_rem.map (Equiv.Perm.ofSubtype σ_sub).toEmbedding = K' := by
              obtain ⟨hKr_sub, _⟩ := Finset.mem_powersetCard.mp hKr
              obtain ⟨hK'_sub, _⟩ := Finset.mem_powersetCard.mp hK'
              ext y; simp only [Finset.mem_map, Equiv.coe_toEmbedding]
              constructor
              · rintro ⟨x, hx, rfl⟩
                have hxS := hKr_sub hx
                rw [Equiv.Perm.ofSubtype_apply_of_mem σ_sub hxS]
                have hmem : σ_sub ⟨x, hxS⟩ ∈ subSet K' := by
                  rw [← hσ_sub_map]
                  exact Finset.mem_map.mpr ⟨⟨x, hxS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩,
                    rfl⟩
                exact (Finset.mem_filter.mp hmem).2
              · intro hy
                have hyK' : (⟨y, hK'_sub hy⟩ : ↥S_comp) ∈ subSet K' :=
                  Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩
                rw [← hσ_sub_map] at hyK'
                obtain ⟨x_sub, hxKr, hx_eq⟩ := Finset.mem_map.mp hyK'
                refine ⟨x_sub.1, (Finset.mem_filter.mp hxKr).2, ?_⟩
                rw [Equiv.Perm.ofSubtype_apply_of_mem σ_sub x_sub.2]
                exact congrArg Subtype.val hx_eq
            refine Finset.card_bij (fun π_sub _ => π_sub.trans σ_sub) (fun π_sub hπ => ?_)
              (fun _ _ _ _ h => Equiv.Perm.ext fun x => σ_sub.injective (Equiv.Perm.ext_iff.mp h x))
              (fun π' hπ' => ⟨π'.trans σ_sub.symm, ?_, by
                ext x; simp only [Equiv.trans_apply, Equiv.apply_symm_apply]⟩)
            · rw [Finset.mem_filter] at hπ ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              rw [ofSubtype_trans, ← Finset.map_map, hπ.2, hσ_map]
            · rw [Finset.mem_filter] at hπ' ⊢
              refine ⟨Finset.mem_univ _, ?_⟩
              apply Finset.map_injective (Equiv.Perm.ofSubtype σ_sub).toEmbedding
              rw [Finset.map_map, ← ofSubtype_trans, Equiv.trans_assoc, Equiv.symm_trans_self,
                Equiv.trans_refl, hπ'.2, hσ_map]
          have hdisj : ((S_comp.powersetCard (n - m) : Set (Finset (Fin U)))).PairwiseDisjoint
              stab := fun K₁ _ K₂ _ hne => Finset.disjoint_left.mpr fun π_sub h₁ h₂ =>
            hne ((Finset.mem_filter.mp h₁).2.symm.trans (Finset.mem_filter.mp h₂).2)
          calc (stab K_rem).card * (U - 3 * m).choose (n - m)
              ≤ (stab K_rem).card * (S_comp.powersetCard (n - m)).card := by
                rw [Finset.card_powersetCard]
                exact Nat.mul_le_mul_left _ (Nat.choose_le_choose _ hS_comp_ge)
            _ = ∑ K' ∈ S_comp.powersetCard (n - m), (stab K').card := by
                rw [Finset.sum_congr rfl fun K' hK' => (hstab_eq K' hK').symm,
                  Finset.sum_const, smul_eq_mul, mul_comm]
            _ ≤ Fintype.card (Equiv.Perm ↥S_comp) := by
                rw [← Finset.card_biUnion hdisj]; exact Finset.card_le_univ _
        · have hemp : stab K_rem = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun π_sub hπ => by
            apply hKr
            rw [← (Finset.mem_filter.mp hπ).2, Finset.mem_powersetCard, Finset.card_map]
            refine ⟨fun y hy => ?_, hK₀_card⟩
            rcases Finset.mem_map.mp hy with ⟨x, hx, rfl⟩
            have hxS : x ∈ S_comp := hK₀_sub hx
            change Equiv.Perm.ofSubtype π_sub x ∈ S_comp
            rw [Equiv.Perm.ofSubtype_apply_of_mem π_sub hxS]
            exact (π_sub ⟨x, hxS⟩).2
          rw [hemp, Finset.card_empty, zero_mul]; exact Nat.zero_le _
      -- Value-shift bound for each fixed π_sub
      have hval_le (π_sub : Equiv.Perm ↥S_comp) :
          ((Finset.univ.filter fun δ : Fin U → Fin V =>
              (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt).card) *
            V ^ (n + 2 * m - g) ≤ Fintype.card (Fin U → Fin V) := by
        let τ := Equiv.Perm.ofSubtype π_sub
        let U_cov := (s.activeKeys t₀ ht₀_n).map τ.toEmbedding ∪
          (s.insertedSet t₀ m ht₀).map τ.toEmbedding ∪ B
        have hB_map : B.map τ.toEmbedding = B := hB_fix π_sub (Prod.mk.inj (Prod.mk.inj ho).2).1
        have hU_cov_card : U_cov.card = n + 2 * m - g := by
          have hmap_all : U_cov =
              (s.activeKeys t₀ ht₀_n ∪ (s.insertedSet t₀ m ht₀ ∪ B)).map τ.toEmbedding := by
            dsimp only [U_cov]
            rw [Finset.union_assoc, Finset.map_union, Finset.map_union, hB_map]
          have hAB_u : (s.insertedSet t₀ m ht₀ ∪ B).card = 2 * m - g := by
            have hu := Finset.card_union_add_card_inter (s.insertedSet t₀ m ht₀) B
            rw [card_insertedSet s ht₀, hB_card, hAB_card] at hu; omega
          have hdisj_KAB : Disjoint (s.activeKeys t₀ ht₀_n) (s.insertedSet t₀ m ht₀ ∪ B) :=
            Finset.disjoint_union_right.mpr
              ⟨((ctx.hdisj s).mono_left (ctx.hA s)).symm, ((ctx.hdisj s).mono_left hB_pool).symm⟩
          rw [hmap_all, Finset.card_map, Finset.card_union_of_disjoint hdisj_KAB, hAB_u,
            card_activeKeys s ht₀_n]
          omega
        let F_δ := Finset.univ.filter fun δ : Fin U → Fin V =>
          (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt
        have hinj : Set.InjOn (fun (δ : Fin U → Fin V) (u : ↥(Finset.univ \ U_cov)) => δ u.1)
            (F_δ : Set (Fin U → Fin V)) := fun δ₁ h₁ δ₂ h₂ hrest => funext fun u => by
          by_cases hu : u ∈ U_cov
          · have heq1 := congrFun (Finset.mem_filter.mp h₁).2 u
            have heq2 := congrFun (Finset.mem_filter.mp h₂).2 u
            change (if u ∈ (actSeed8Equiv τ δ₁ s).activeKeys t₀ ht₀_n ∪
                (actSeed8Equiv τ δ₁ s).insertedSet t₀ m ht₀ ∪ B
              then some ((actSeed8Equiv τ δ₁ s).kv u) else none) = kv_opt u at heq1
            change (if u ∈ (actSeed8Equiv τ δ₂ s).activeKeys t₀ ht₀_n ∪
                (actSeed8Equiv τ δ₂ s).insertedSet t₀ m ht₀ ∪ B
              then some ((actSeed8Equiv τ δ₂ s).kv u) else none) = kv_opt u at heq2
            rw [actSeed8Equiv_activeKeys, actSeed8Equiv_insertedSet] at heq1 heq2
            change (if u ∈ U_cov then some (s.kv (τ.symm u) + δ₁ u) else none) = kv_opt u at heq1
            change (if u ∈ U_cov then some (s.kv (τ.symm u) + δ₂ u) else none) = kv_opt u at heq2
            rw [ite_eq_left hu] at heq1 heq2
            exact add_left_cancel (Option.some.inj (heq1.trans heq2.symm))
          · exact congrFun hrest ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, hu⟩⟩
        have hcard_Fδ : F_δ.card ≤ V ^ (U - (n + 2 * m - g)) := by
          refine (Finset.card_le_card_of_injOn _ (fun _ _ => Finset.mem_univ _) hinj).trans_eq ?_
          rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
            Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _), Finset.card_univ,
            Fintype.card_fin, hU_cov_card]
        calc F_δ.card * V ^ (n + 2 * m - g)
            ≤ V ^ (U - (n + 2 * m - g)) * V ^ (n + 2 * m - g) := Nat.mul_le_mul_right _ hcard_Fδ
          _ = V ^ U := by rw [← pow_add, Nat.sub_add_cancel (by omega)]
          _ = Fintype.card (Fin U → Fin V) := by
              simp only [Fintype.card_fun, Fintype.card_fin]
      -- Combine stab and F_δ over G = Perm S_comp × (Fin U → Fin V)
      have hsplit_sum : (Finset.univ.filter fun γ : G =>
            target8 t₀ m ht₀ (actG γ (s, B)) = (K_rem, kv_opt)).card =
          ∑ π_sub ∈ stab K_rem,
            (Finset.univ.filter fun δ : Fin U → Fin V =>
              (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt).card := by
        have hfst (π_sub : Equiv.Perm ↥S_comp) (δ : Fin U → Fin V) :
            (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).1 =
              K₀.map (Equiv.Perm.ofSubtype π_sub).toEmbedding := by
          change (actSeed8Equiv (Equiv.Perm.ofSubtype π_sub) δ s).activeKeys t₀ ht₀_n \
              Finset.univ.image (segDeletedKeys
                (actSeed8Equiv (Equiv.Perm.ofSubtype π_sub) δ s).keys
                (actSeed8Equiv (Equiv.Perm.ofSubtype π_sub) δ s).delPerm t₀ m ht₀) =
            K₀.map (Equiv.Perm.ofSubtype π_sub).toEmbedding
          dsimp only [K₀]
          rw [actSeed8Equiv_activeKeys, actSeed8Equiv_deletedSet, Finset.map_sdiff]
        rw [← Finset.card_sigma]
        refine Finset.card_bij (fun γ _ => ⟨γ.1, γ.2⟩)
          (fun γ hγ => by
            have hpair := Prod.mk.inj (Finset.mem_filter.mp hγ).2
            exact Finset.mem_sigma.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,
              by rw [← hfst γ.1 γ.2]; exact hpair.1⟩,
              Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpair.2⟩⟩)
          (fun ⟨_, _⟩ _ ⟨_, _⟩ _ h => by injection h with ha hb; exact Prod.ext ha hb)
          (fun ⟨π_sub, δ⟩ hσ => ⟨(π_sub, δ), by
            obtain ⟨hπ, hδ⟩ := Finset.mem_sigma.mp hσ
            refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, Prod.ext ?_
              (Finset.mem_filter.mp hδ).2⟩
            rw [hfst]; exact (Finset.mem_filter.mp hπ).2, rfl⟩)
      have hnat_ineq : (Finset.univ.filter fun γ : G =>
            target8 t₀ m ht₀ (actG γ (s, B)) = (K_rem, kv_opt)).card * M_nat ≤
          Fintype.card G := by
        dsimp only [M_nat, G]
        rw [Fintype.card_prod, hsplit_sum, mul_comm ((U - 3 * m).choose (n - m)),
          ← mul_assoc, Finset.sum_mul]
        calc (∑ π_sub ∈ stab K_rem,
              (Finset.univ.filter fun δ : Fin U → Fin V =>
                (target8 t₀ m ht₀ (actG (π_sub, δ) (s, B))).2 = kv_opt).card *
                  V ^ (n + 2 * m - g)) * (U - 3 * m).choose (n - m)
            ≤ (∑ _π_sub ∈ stab K_rem, Fintype.card (Fin U → Fin V)) *
                (U - 3 * m).choose (n - m) :=
              Nat.mul_le_mul_right _ (Finset.sum_le_sum fun π_sub _ => hval_le π_sub)
          _ = ((stab K_rem).card * (U - 3 * m).choose (n - m)) * Fintype.card (Fin U → Fin V) := by
              rw [Finset.sum_const, smul_eq_mul]; ring
          _ ≤ Fintype.card (Equiv.Perm ↥S_comp) * Fintype.card (Fin U → Fin V) :=
              Nat.mul_le_mul_right _ hstab_le
      exact_mod_cast hnat_ineq
    -- Average horbit_le over G to deduce fiber bound
    have havg_pair : (((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal) *
        (Fintype.card G : ℝ) =
        ∑ sb, (μ_g sb).toReal *
          ((Finset.univ.filter fun γ : G =>
            obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T).card : ℝ) := by
      calc _ = ∑ _γ : G, ((μ_g.map fun sb =>
              (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
        _ = ∑ γ : G, ∑ sb, (μ_g sb).toReal *
              (if obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T then (1 : ℝ) else 0) :=
            Finset.sum_congr rfl fun γ _ => by
              rw [PMF.map_apply_toReal, ← (actG γ).sum_comp]
              refine Finset.sum_congr rfl fun sb _ => ?_
              by_cases ho_sb : obs8 t₀ m ht₀ sb = o
              · have ho_act := (hobs_iff γ sb).mpr ho_sb
                rw [hμ_obs γ sb ho_sb]
                by_cases ht_act : target8 t₀ m ht₀ (actG γ sb) = T
                · have heq : (o, T) =
                      (obs8 t₀ m ht₀ (actG γ sb), target8 t₀ m ht₀ (actG γ sb)) :=
                    Prod.ext ho_act.symm ht_act.symm
                  rw [ite_eq_left heq, ite_eq_left ⟨ho_sb, ht_act⟩, mul_one]
                · have hne_p : (o, T) ≠
                      (obs8 t₀ m ht₀ (actG γ sb), target8 t₀ m ht₀ (actG γ sb)) :=
                    fun h => ht_act (Prod.mk.inj h).2.symm
                  rw [ite_eq_right hne_p, ite_eq_right fun h => ht_act h.2, mul_zero]
              · have ho_act : obs8 t₀ m ht₀ (actG γ sb) ≠ o := mt (hobs_iff γ sb).mp ho_sb
                have hne_p : (o, T) ≠
                    (obs8 t₀ m ht₀ (actG γ sb), target8 t₀ m ht₀ (actG γ sb)) :=
                  fun h => ho_act (Prod.mk.inj h).1.symm
                rw [ite_eq_right hne_p, ite_eq_right fun h => ho_sb h.1, mul_zero]
        _ = _ := by
              rw [Finset.sum_comm]
              refine Finset.sum_congr rfl fun sb _ => ?_
              rw [← Finset.mul_sum, Finset.sum_boole]
    have havg_obs : ((μ_g.map (obs8 t₀ m ht₀)) o).toReal * (Fintype.card G : ℝ) =
        ∑ sb, (μ_g sb).toReal * (if obs8 t₀ m ht₀ sb = o then (Fintype.card G : ℝ) else 0) := by
      rw [PMF.map_apply_toReal, Finset.sum_mul]
      refine Finset.sum_congr rfl fun sb _ => ?_
      by_cases ho_sb : obs8 t₀ m ht₀ sb = o
      · rw [ite_eq_left ho_sb.symm, ite_eq_left ho_sb]
      · rw [ite_eq_right (Ne.symm ho_sb), zero_mul, ite_eq_right ho_sb, mul_zero]
    have hG_pos : (0 : ℝ) < (Fintype.card G : ℝ) := Nat.cast_pos.mpr Fintype.card_pos
    refine le_of_mul_le_mul_right ?_ hG_pos
    calc ((((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal) *
            (M_nat : ℝ)) * (Fintype.card G : ℝ)
        = ((((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal) *
            (Fintype.card G : ℝ)) * (M_nat : ℝ) := by ring
      _ = ∑ sb, (μ_g sb).toReal *
            (((Finset.univ.filter fun γ : G =>
              obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T).card : ℝ) *
                (M_nat : ℝ)) := by
            rw [havg_pair, Finset.sum_mul]
            exact Finset.sum_congr rfl fun _ _ => by ring
      _ ≤ ∑ sb, (μ_g sb).toReal * (if obs8 t₀ m ht₀ sb = o then (Fintype.card G : ℝ) else 0) := by
            refine Finset.sum_le_sum fun sb _ => ?_
            by_cases hsupp : sb.2 ∈ ctx.Fg sb.1
            · by_cases ho_sb : obs8 t₀ m ht₀ sb = o
              · rw [ite_eq_left ho_sb]
                have hfilt_eq : (Finset.univ.filter fun γ : G =>
                    obs8 t₀ m ht₀ sb = o ∧ target8 t₀ m ht₀ (actG γ sb) = T) =
                    Finset.univ.filter fun γ : G => target8 t₀ m ht₀ (actG γ sb) = T := by
                  ext γ; simp only [Finset.mem_filter, Finset.mem_univ, ho_sb, true_and]
                rw [hfilt_eq]
                exact mul_le_mul_of_nonneg_left (horbit_le sb ho_sb hsupp) ENNReal.toReal_nonneg
              · simp only [ho_sb, false_and, Finset.filter_false, Finset.card_empty,
                  Nat.cast_zero, zero_mul, ↓reduceIte, mul_zero, le_rfl]
            · have h0 : (μ_g sb).toReal = 0 := by
                dsimp only [μ_g]
                rw [toReal_innerPoolDist_apply, ite_eq_right hsupp]
              rw [h0, zero_mul, zero_mul]
      _ = ((μ_g.map (obs8 t₀ m ht₀)) o).toReal * (Fintype.card G : ℝ) := havg_obs.symm
  · have hzero : ((μ_g.map fun sb => (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)) (o, T)).toReal =
        0 := by
      rw [PMF.map_apply_toReal]
      refine Finset.sum_eq_zero fun sb _ => ?_
      by_cases heq : (o, T) = (obs8 t₀ m ht₀ sb, target8 t₀ m ht₀ sb)
      · have hBo : o.2.1 = sb.2 := (Prod.mk.inj (Prod.mk.inj (Prod.mk.inj heq).1).2).1
        have hnFg : sb.2 ∉ ctx.Fg sb.1 := fun h => ho_card (hBo ▸
          (Finset.mem_powersetCard.mp (Finset.mem_filter.mp (ctx.hFg sb.1 ▸ h)).1).2)
        rw [ite_eq_left heq]
        dsimp only [μ_g]
        rw [toReal_innerPoolDist_apply, ite_eq_right hnFg]
      · rw [ite_eq_right heq]
    rw [hzero, zero_mul]
    exact ENNReal.toReal_nonneg

end Cslib.DataStructure.Dictionary.CellProbe
