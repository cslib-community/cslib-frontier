/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Compiler
import all CslibFrontier.Computability.Circuit.Frontier.Compiler.Hypergraph.Gaussian.EuclideanSheppard
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Metric

/-!
# Adaptive Bipartite Walk-Maximum Kernel and Non-Backtracking Boundary-Mass Bounds

Private pruned bipartite incidence graph (`PrunedEdge`, `BipNode`, `bipSimpleGraph`), adaptive
step attenuation `stepWeight`, walk-maximum kernel `walkMax`, and boundary-mass / square-norm
bounds imported via `import all` by downstream correlation and layout modules.
-/

-- Internal proof-only helpers; downstream correlation and layout modules import all.
set_option linter.privateModule false

public section

namespace Cslib.Circuits.Frontier.Hypergraph

open MeasureTheory ProbabilityTheory Real Set Filter Cslib.Circuits
open scoped RealInnerProductSpace Interval

/-! ### Pruned bipartite incidence graph and `walkMax` kernel -/

section BipartiteKernel

variable {σ : Signature} {n : ℕ} (c : Circuit σ n 1) (K₀ : ℕ)

/-- Live signals whose hyperedge has cardinality in `[2, K₀]`. -/
private abbrev PrunedEdge : Type :=
  {w : LiveSignal c // 2 ≤ (hyperEdge c w).card ∧ (hyperEdge c w).card ≤ K₀}

/-- Nodes of the pruned bipartite hypergraph: `HyperNode c ⊕ PrunedEdge c K₀`. -/
private abbrev BipNode : Type :=
  HyperNode c ⊕ PrunedEdge c K₀

/-- Incidence adjacency on `BipNode c K₀`. -/
private def bipAdj : BipNode c K₀ → BipNode c K₀ → Prop
  | .inl v, .inr e => v ∈ hyperEdge c e.1
  | .inr e, .inl v => v ∈ hyperEdge c e.1
  | _, _ => False

private theorem bipAdj_symm {x y : BipNode c K₀} (h : bipAdj c K₀ x y) : bipAdj c K₀ y x := by
  cases x <;> cases y <;> exact h

private theorem bipAdj_irrefl (x : BipNode c K₀) : ¬bipAdj c K₀ x x := by
  cases x <;> simp [bipAdj]

/-- Simple graph on `BipNode c K₀` induced by `bipAdj`. -/
private def bipSimpleGraph : SimpleGraph (BipNode c K₀) where
  Adj := bipAdj c K₀
  symm := ⟨fun _ _ h => bipAdj_symm c K₀ h⟩
  loopless := ⟨bipAdj_irrefl c K₀⟩

/-- Non-backtracking branching bound on `BipNode c K₀`: `r` at circuit nodes and `|e| - 1` at
pruned hyperedges. -/
private noncomputable def bipBranch (r : ℕ) : BipNode c K₀ → ℕ
  | .inl _ => r
  | .inr e => (hyperEdge c e.1).card - 1

private theorem one_le_bipBranch {r : ℕ} (hr : 2 ≤ r) (x : BipNode c K₀) :
    1 ≤ bipBranch c K₀ r x := by
  rcases x with v | e
  · exact Nat.one_le_of_lt hr
  · have := e.2.1
    dsimp only [bipBranch]
    omega

/-- Adaptive step attenuation `θ / √(√(br x) * √(br y))` along an incidence step `(x, y)`. -/
private noncomputable def stepWeight (r : ℕ) (θ : ℝ) (x y : BipNode c K₀) : ℝ :=
  θ / √(√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ))

private theorem stepWeight_nonneg (r : ℕ) {θ : ℝ} (hθ : 0 ≤ θ) (x y : BipNode c K₀) :
    0 ≤ stepWeight c K₀ r θ x y :=
  div_nonneg hθ (sqrt_nonneg _)

private theorem stepWeight_le {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ : 0 ≤ θ) (x y : BipNode c K₀) :
    stepWeight c K₀ r θ x y ≤ θ := by
  have hx1 : (1 : ℝ) ≤ (bipBranch c K₀ r x : ℝ) := by exact_mod_cast one_le_bipBranch c K₀ hr x
  have hy1 : (1 : ℝ) ≤ (bipBranch c K₀ r y : ℝ) := by exact_mod_cast one_le_bipBranch c K₀ hr y
  have hx : (1 : ℝ) ≤ √(bipBranch c K₀ r x : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr (by linarith)
  have hy : (1 : ℝ) ≤ √(bipBranch c K₀ r y : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr (by linarith)
  have hden : (1 : ℝ) ≤ √(√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ)) :=
    (le_sqrt zero_le_one (by positivity)).mpr (by nlinarith)
  exact div_le_self hθ hden

private theorem stepWeight_sq (r : ℕ) (θ : ℝ) (x y : BipNode c K₀) :
    stepWeight c K₀ r θ x y ^ 2 =
      θ ^ 2 / (√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ)) := by
  rw [stepWeight, div_pow, sq_sqrt (mul_nonneg (sqrt_nonneg _) (sqrt_nonneg _))]

open Classical in
/-- Radius-`m` walk-maximum kernel on `BipNode c K₀ → HyperNode c → ℝ`. -/
private noncomputable def walkMax (r : ℕ) (θ : ℝ) : ℕ → BipNode c K₀ → HyperNode c → ℝ
  | 0, .inl v, z => if v = z then 1 else 0
  | 0, .inr _, _ => 0
  | m + 1, x, z =>
    (insert (walkMax r θ m x z)
      ((Finset.univ.filter (bipAdj c K₀ x)).image fun y =>
        stepWeight c K₀ r θ x y * walkMax r θ m y z)).max' (Finset.insert_nonempty _ _)

private theorem walkMax_mono_step (r : ℕ) (θ : ℝ) (m : ℕ) (x : BipNode c K₀) (z : HyperNode c) :
    walkMax c K₀ r θ m x z ≤ walkMax c K₀ r θ (m + 1) x z := by
  classical
  exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)

private theorem walkMax_mono (r : ℕ) (θ : ℝ) {m₁ m₂ : ℕ} (hm : m₁ ≤ m₂) (x : BipNode c K₀)
    (z : HyperNode c) : walkMax c K₀ r θ m₁ x z ≤ walkMax c K₀ r θ m₂ x z := by
  induction hm with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (walkMax_mono_step c K₀ r θ _ x z)

private theorem walkMax_nonneg (r : ℕ) {θ : ℝ} (_hθ : 0 ≤ θ) (m : ℕ) (x : BipNode c K₀)
    (z : HyperNode c) : 0 ≤ walkMax c K₀ r θ m x z := by
  refine le_trans ?_ (walkMax_mono c K₀ r θ (Nat.zero_le m) x z)
  cases x with
  | inl v => dsimp only [walkMax]; split_ifs <;> norm_num
  | inr _ => exact le_rfl

private theorem step_mul_walkMax_le (r : ℕ) (θ : ℝ) (m : ℕ) {x y : BipNode c K₀}
    (hadj : bipAdj c K₀ x y) (z : HyperNode c) :
    stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z ≤ walkMax c K₀ r θ (m + 1) x z := by
  classical
  let img : Finset ℝ := (Finset.univ.filter (bipAdj c K₀ x)).image fun y' =>
    stepWeight c K₀ r θ x y' * walkMax c K₀ r θ m y' z
  have hmem : stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z ∈
      insert (walkMax c K₀ r θ m x z) img :=
    Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hadj⟩, rfl⟩)
  exact Finset.le_max' _ _ hmem

private theorem exists_step_of_walkMax_lt (r : ℕ) (θ : ℝ) (m : ℕ) {x : BipNode c K₀}
    {z : HyperNode c} (hlt : walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z) :
    ∃ y : BipNode c K₀, bipAdj c K₀ x y ∧
      walkMax c K₀ r θ (m + 1) x z = stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z := by
  classical
  have hmem := Finset.max'_mem (insert (walkMax c K₀ r θ m x z)
    ((Finset.univ.filter (bipAdj c K₀ x)).image fun y =>
      stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z)) (Finset.insert_nonempty _ _)
  change walkMax c K₀ r θ (m + 1) x z ∈ _ at hmem
  rcases Finset.mem_insert.mp hmem with heq | himg
  · exact absurd heq hlt.ne'
  · obtain ⟨y, hy, heq⟩ := Finset.mem_image.mp himg
    exact ⟨y, (Finset.mem_filter.mp hy).2, heq.symm⟩

private theorem one_le_norm_walkMax (r : ℕ) (θ : ℝ) (m : ℕ) (v : HyperNode c) :
    1 ≤ ‖WithLp.toLp 2 (walkMax c K₀ r θ m (.inl v))‖ := by
  have hv1 : 1 ≤ walkMax c K₀ r θ m (.inl v) v := by
    simpa [walkMax] using walkMax_mono c K₀ r θ (Nat.zero_le m) (.inl v) v
  have hsq : 1 ≤ ‖WithLp.toLp 2 (walkMax c K₀ r θ m (.inl v))‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc (1 : ℝ) ≤ walkMax c K₀ r θ m (.inl v) v ^ 2 := by nlinarith
      _ ≤ ∑ z, walkMax c K₀ r θ m (.inl v) z ^ 2 :=
          Finset.single_le_sum (fun z _ => sq_nonneg _) (Finset.mem_univ v)
  nlinarith [norm_nonneg (WithLp.toLp 2 (walkMax c K₀ r θ m (.inl v)))]

/-! ### Degree, support, and non-backtracking boundary-mass bounds -/

open Classical in
private theorem card_bipAdj_inl_le {r : ℕ} (hfan : c.FanInAtMost r) (v : HyperNode c) :
    (Finset.univ.filter (bipAdj c K₀ (.inl v))).card ≤ r + 1 := by
  let f : {y : BipNode c K₀ // y ∈ Finset.univ.filter (bipAdj c K₀ (.inl v))} →
      {w : LiveSignal c // v ∈ hyperEdge c w} := fun ⟨y, hy⟩ =>
    match y, (Finset.mem_filter.mp hy).2 with | .inr e', hadj => ⟨e'.1, hadj⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨u₁ | e₁, h₁⟩ ⟨u₂ | e₂, h₂⟩ h
    · exact False.elim (Finset.mem_filter.mp h₁).2
    · exact False.elim (Finset.mem_filter.mp h₁).2
    · exact False.elim (Finset.mem_filter.mp h₂).2
    · have he : e₁.1 = e₂.1 := congrArg (Subtype.val : {w // v ∈ hyperEdge c w} → _) h
      exact Subtype.ext (congrArg Sum.inr (Subtype.ext he))
  have hcard := Fintype.card_le_of_injective f hf_inj
  rw [Fintype.card_coe, Fintype.card_subtype] at hcard
  exact hcard.trans (card_signals_at_node_le hfan v)

open Classical in
private theorem card_bipAdj_inr_eq (e : PrunedEdge c K₀) :
    (Finset.univ.filter (bipAdj c K₀ (.inr e))).card = (hyperEdge c e.1).card := by
  refine Finset.card_bij (fun y hy => match y, (Finset.mem_filter.mp hy).2 with
    | .inl v, _ => v) (fun y hy => ?_) (fun y₁ hy₁ y₂ hy₂ h => ?_) (fun v hv => ?_)
  · rcases y with v | e'
    · exact (Finset.mem_filter.mp hy).2
    · exact False.elim (Finset.mem_filter.mp hy).2
  · rcases y₁ with v₁ | e₁ <;> rcases y₂ with v₂ | e₂
    · exact congrArg Sum.inl h
    · exact False.elim (Finset.mem_filter.mp hy₂).2
    · exact False.elim (Finset.mem_filter.mp hy₁).2
    · exact False.elim (Finset.mem_filter.mp hy₁).2
  · exact ⟨.inl v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩, rfl⟩

open Classical in
private theorem card_bipAdj_le {r : ℕ} (hfan : c.FanInAtMost r) (x : BipNode c K₀) :
    (Finset.univ.filter (bipAdj c K₀ x)).card ≤ max (r + 1) K₀ := by
  rcases x with v | e
  · exact (card_bipAdj_inl_le c K₀ hfan v).trans (le_max_left _ _)
  · exact ((card_bipAdj_inr_eq c K₀ e).trans_le e.2.2).trans (le_max_right _ _)

open Classical in
private theorem card_bipAdj_ne_le {r : ℕ} (hfan : c.FanInAtMost r) {prev x : BipNode c K₀}
    (hprev : bipAdj c K₀ prev x) :
    (Finset.univ.filter fun y => bipAdj c K₀ x y ∧ y ≠ prev).card ≤ bipBranch c K₀ r x := by
  have hmem : prev ∈ Finset.univ.filter (bipAdj c K₀ x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, bipAdj_symm c K₀ hprev⟩
  have hsub : (Finset.univ.filter fun y => bipAdj c K₀ x y ∧ y ≠ prev) ⊆
      (Finset.univ.filter (bipAdj c K₀ x)).erase prev := by
    intro y hy
    have hy' := (Finset.mem_filter.mp hy).2
    exact Finset.mem_erase.mpr ⟨hy'.2, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy'.1⟩⟩
  have hcard_le := (Finset.card_le_card hsub).trans (Finset.card_erase_of_mem hmem).le
  rcases x with v | e
  · have := card_bipAdj_inl_le c K₀ hfan v
    dsimp only [bipBranch]
    omega
  · have := card_bipAdj_inr_eq c K₀ e
    dsimp only [bipBranch]
    omega

private theorem degree_bipSimpleGraph_le {r : ℕ} (hfan : c.FanInAtMost r)
    [DecidableRel (bipSimpleGraph c K₀).Adj] (x : BipNode c K₀) :
    (bipSimpleGraph c K₀).degree x ≤ max (r + 1) K₀ := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have heq : (bipSimpleGraph c K₀).neighborFinset x = Finset.univ.filter (bipAdj c K₀ x) := by
    ext y
    rw [SimpleGraph.mem_neighborFinset, Finset.mem_filter]
    exact ⟨fun h => ⟨Finset.mem_univ y, h⟩, fun h => h.2⟩
  rw [heq]
  exact card_bipAdj_le c K₀ hfan x

private theorem edist_le_of_walkMax_ne_zero {r : ℕ} {θ : ℝ} :
    ∀ {m : ℕ} {x : BipNode c K₀} {z : HyperNode c},
      walkMax c K₀ r θ m x z ≠ 0 → (bipSimpleGraph c K₀).edist x (.inl z) ≤ m
  | 0, .inl v, z, hne => by
    dsimp only [walkMax] at hne
    by_cases h : v = z
    · subst h; simp
    · rw [ite_eq_right h] at hne
      exact absurd rfl hne
  | 0, .inr _, _, hne => absurd rfl hne
  | m + 1, x, z, hne => by
    by_cases hprev : walkMax c K₀ r θ m x z = walkMax c K₀ r θ (m + 1) x z
    · exact (edist_le_of_walkMax_ne_zero (hprev.symm ▸ hne)).trans
        (by exact_mod_cast Nat.le_succ m)
    · have hlt := lt_of_le_of_ne (walkMax_mono_step c K₀ r θ m x z) hprev
      obtain ⟨y, hadj, heq⟩ := exists_step_of_walkMax_lt c K₀ r θ m hlt
      have hy_ne : walkMax c K₀ r θ m y z ≠ 0 := by
        intro hy0
        rw [heq, hy0, mul_zero] at hne
        exact hne rfl
      have htri : (bipSimpleGraph c K₀).edist x (.inl z) ≤
          (bipSimpleGraph c K₀).edist y (.inl z) + 1 :=
        SimpleGraph.Adj.edist_le_edist_add_one (G := bipSimpleGraph c K₀) hadj
          (Sum.inl z : BipNode c K₀)
      calc (bipSimpleGraph c K₀).edist x (.inl z)
          ≤ (bipSimpleGraph c K₀).edist y (.inl z) + 1 := htri
        _ ≤ (m : ℕ∞) + 1 := add_le_add_left (edist_le_of_walkMax_ne_zero hy_ne) 1
        _ = ((m + 1 : ℕ) : ℕ∞) := by push_cast; rfl

open Classical in
/-- Non-backtracking edge-step boundary mass: coordinates `z` at which `walkMax (m + 1) prev z`
strictly improves over `walkMax m prev z` via the first step `prev → x`. -/
private noncomputable def edgeBoundaryMass (r : ℕ) (θ : ℝ) (m : ℕ) (prev x : BipNode c K₀) : ℝ :=
  ∑ z ∈ Finset.univ.filter (fun z : HyperNode c =>
      bipAdj c K₀ prev x ∧
      walkMax c K₀ r θ m prev z < walkMax c K₀ r θ (m + 1) prev z ∧
      walkMax c K₀ r θ (m + 1) prev z = stepWeight c K₀ r θ prev x * walkMax c K₀ r θ m x z),
    walkMax c K₀ r θ m x z ^ 2 / √(bipBranch c K₀ r x : ℝ)

private theorem edgeBoundaryMass_le {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    ∀ (m : ℕ) (prev x : BipNode c K₀), edgeBoundaryMass c K₀ r θ m prev x ≤ θ ^ (2 * m)
  | 0, prev, x => by
    classical
    rw [Nat.mul_zero, pow_zero]
    rcases x with v | e
    · have hsub : (Finset.univ.filter fun z : HyperNode c =>
          bipAdj c K₀ prev (.inl v) ∧
          walkMax c K₀ r θ 0 prev z < walkMax c K₀ r θ 1 prev z ∧
          walkMax c K₀ r θ 1 prev z = stepWeight c K₀ r θ prev (.inl v) *
            walkMax c K₀ r θ 0 (.inl v) z) ⊆ {v} := by
        intro z hz
        have hlt := (Finset.mem_filter.mp hz).2.2.1
        have heq := (Finset.mem_filter.mp hz).2.2.2
        have h0 : 0 ≤ walkMax c K₀ r θ 0 prev z := walkMax_nonneg c K₀ r hθ0.le 0 prev z
        refine Finset.mem_singleton.mpr ?_
        by_contra hzv
        have hzv' : v ≠ z := fun h => hzv h.symm
        have hw0 : walkMax c K₀ r θ 0 (.inl v) z = 0 := by
          dsimp only [walkMax]
          exact ite_eq_right hzv'
        rw [hw0, mul_zero] at heq
        linarith
      calc edgeBoundaryMass c K₀ r θ 0 prev (.inl v)
          ≤ ∑ z ∈ ({v} : Finset (HyperNode c)),
              walkMax c K₀ r θ 0 (.inl v) z ^ 2 / √(bipBranch c K₀ r (.inl v) : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ = 1 / √(r : ℝ) := by simp [walkMax, bipBranch]
        _ ≤ 1 := div_le_one_of_le₀
            ((le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr
              (by norm_num; exact_mod_cast Nat.one_le_of_lt hr))
            (sqrt_nonneg _)
    · have hemp : (Finset.univ.filter fun z : HyperNode c =>
          bipAdj c K₀ prev (.inr e) ∧
          walkMax c K₀ r θ 0 prev z < walkMax c K₀ r θ 1 prev z ∧
          walkMax c K₀ r θ 1 prev z = stepWeight c K₀ r θ prev (.inr e) *
            walkMax c K₀ r θ 0 (.inr e) z) = ∅ := by
        ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
          not_and]
        intro _ hlt heq
        have h0 : 0 ≤ walkMax c K₀ r θ 0 prev z := walkMax_nonneg c K₀ r hθ0.le 0 prev z
        have hw0 : walkMax c K₀ r θ 0 (.inr e) z = 0 := rfl
        rw [hw0, mul_zero] at heq
        linarith
      simp [edgeBoundaryMass, hemp]
  | m + 1, prev, x => by
    classical
    by_cases hpx : bipAdj c K₀ prev x
    · let S := Finset.univ.filter fun z : HyperNode c =>
        bipAdj c K₀ prev x ∧
        walkMax c K₀ r θ (m + 1) prev z < walkMax c K₀ r θ (m + 2) prev z ∧
        walkMax c K₀ r θ (m + 2) prev z =
          stepWeight c K₀ r θ prev x * walkMax c K₀ r θ (m + 1) x z
      let N : Finset (BipNode c K₀) := Finset.univ.filter fun y => bipAdj c K₀ x y ∧ y ≠ prev
      let Fy (y : BipNode c K₀) : Finset (HyperNode c) := Finset.univ.filter fun z =>
        bipAdj c K₀ x y ∧
        walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z ∧
        walkMax c K₀ r θ (m + 1) x z = stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z
      have hsub : S ⊆ N.biUnion Fy := by
        intro z hz
        have hlt2 := (Finset.mem_filter.mp hz).2.2.1
        have heq2 := (Finset.mem_filter.mp hz).2.2.2
        have hlt1 : walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z := by
          by_contra! hle
          have hstep := step_mul_walkMax_le c K₀ r θ m hpx z
          have hmul := mul_le_mul_of_nonneg_left hle (stepWeight_nonneg c K₀ r hθ0.le prev x)
          linarith
        obtain ⟨y, hadj_xy, heq1⟩ := exists_step_of_walkMax_lt c K₀ r θ m hlt1
        have hy_ne : y ≠ prev := by
          rintro rfl
          have hsw1 := stepWeight_le c K₀ hr hθ0.le y x
          have hsw2 := stepWeight_le c K₀ hr hθ0.le x y
          have hw0 := walkMax_nonneg c K₀ r hθ0.le m y z
          have hmono := walkMax_mono_step c K₀ r θ m y z
          have hprod : stepWeight c K₀ r θ y x *
              (stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z) ≤
              walkMax c K₀ r θ m y z := by
            have h1 : stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z ≤
                1 * walkMax c K₀ r θ m y z :=
              mul_le_mul_of_nonneg_right (hsw2.trans hθ1) hw0
            have h2 : stepWeight c K₀ r θ y x * walkMax c K₀ r θ m y z ≤
                1 * walkMax c K₀ r θ m y z :=
              mul_le_mul_of_nonneg_right (hsw1.trans hθ1) hw0
            nlinarith [stepWeight_nonneg c K₀ r hθ0.le y x]
          rw [heq1] at heq2
          linarith
        exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hadj_xy, hy_ne⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ z, hadj_xy, hlt1, heq1⟩⟩
      have hbr_pos : (0 : ℝ) < bipBranch c K₀ r x := by
        exact_mod_cast one_le_bipBranch c K₀ hr x
      have hterm (y : BipNode c K₀) :
          ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) ≤
            (θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m) := by
        have hrew : ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) =
            (θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * edgeBoundaryMass c K₀ r θ m x y := by
          rw [edgeBoundaryMass, Finset.mul_sum]
          refine Finset.sum_congr rfl fun z hz => ?_
          have heq1 := (Finset.mem_filter.mp hz).2.2.2
          rw [heq1, mul_pow, stepWeight_sq]
          have hsx_ne : √(bipBranch c K₀ r x : ℝ) ≠ 0 := (sqrt_pos.mpr hbr_pos).ne'
          by_cases hby : (bipBranch c K₀ r y : ℝ) = 0
          · simp [hby]
          · have hsy_ne : √(bipBranch c K₀ r y : ℝ) ≠ 0 :=
              (sqrt_pos.mpr (lt_of_le_of_ne (Nat.cast_nonneg _) (Ne.symm hby))).ne'
            field_simp
            rw [sq_sqrt hbr_pos.le]
            ring
        rw [hrew]
        exact mul_le_mul_of_nonneg_left (edgeBoundaryMass_le hr hfan hθ0 hθ1 m x y) (by positivity)
      calc edgeBoundaryMass c K₀ r θ (m + 1) prev x
          ≤ ∑ z ∈ N.biUnion Fy, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity
        _ ≤ ∑ y ∈ N, ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 / √(bipBranch c K₀ r x : ℝ) := by
            clear hsub
            induction N using Finset.induction_on with
            | empty => simp
            | insert a s ha ih =>
              rw [Finset.biUnion_insert, Finset.sum_insert ha]
              exact (sum_union_le_of_nonneg fun _ => by positivity).trans (add_le_add le_rfl ih)
        _ ≤ ∑ _y ∈ N, (θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m) :=
            Finset.sum_le_sum fun y _ => hterm y
        _ = N.card * ((θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (bipBranch c K₀ r x : ℝ) * ((θ ^ 2 / (bipBranch c K₀ r x : ℝ)) * θ ^ (2 * m)) := by
            gcongr
            exact_mod_cast card_bipAdj_ne_le c K₀ hfan hpx
        _ = θ ^ (2 * (m + 1)) := by
            have hne := hbr_pos.ne'
            field_simp
            ring
    · have hemp : (Finset.univ.filter fun z : HyperNode c =>
          bipAdj c K₀ prev x ∧
          walkMax c K₀ r θ (m + 1) prev z < walkMax c K₀ r θ (m + 2) prev z ∧
          walkMax c K₀ r θ (m + 2) prev z =
            stepWeight c K₀ r θ prev x * walkMax c K₀ r θ (m + 1) x z) = ∅ := by
        ext z
        simp [hpx]
      rw [edgeBoundaryMass, hemp, Finset.sum_empty]
      positivity

/-- **Non-backtracking boundary-mass bound:** for every `x : BipNode c K₀` and `m : ℕ`, the sum of
`walkMax (m + 1) x z ^ 2` over coordinates where step `m + 1` strictly improves `walkMax m x z` is
at most `max (r + 1) K₀ * θ ^ (2 (m + 1))`. -/
private theorem sum_sq_walkMax_strict_le {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r) {θ : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (m : ℕ) (x : BipNode c K₀) :
    open Classical in
    ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z),
      walkMax c K₀ r θ (m + 1) x z ^ 2 ≤
      (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) := by
  classical
  let N : Finset (BipNode c K₀) := Finset.univ.filter (bipAdj c K₀ x)
  let Fy (y : BipNode c K₀) : Finset (HyperNode c) := Finset.univ.filter fun z =>
    bipAdj c K₀ x y ∧
    walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z ∧
    walkMax c K₀ r θ (m + 1) x z = stepWeight c K₀ r θ x y * walkMax c K₀ r θ m y z
  have hsub : (Finset.univ.filter fun z =>
      walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z) ⊆ N.biUnion Fy := by
    intro z hz
    have hlt := (Finset.mem_filter.mp hz).2
    obtain ⟨y, hadj, heq⟩ := exists_step_of_walkMax_lt c K₀ r θ m hlt
    exact Finset.mem_biUnion.mpr ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ y, hadj⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ z, hadj, hlt, heq⟩⟩
  have hbr1 : (1 : ℝ) ≤ (bipBranch c K₀ r x : ℝ) := by exact_mod_cast one_le_bipBranch c K₀ hr x
  have h1_br : (1 : ℝ) ≤ √(bipBranch c K₀ r x : ℝ) :=
    (le_sqrt zero_le_one (Nat.cast_nonneg _)).mpr (by linarith)
  have hterm (y : BipNode c K₀) :
      ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 ≤ θ ^ (2 * (m + 1)) := by
    calc ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2
        ≤ ∑ z ∈ Fy y, θ ^ 2 * (walkMax c K₀ r θ m y z ^ 2 / √(bipBranch c K₀ r y : ℝ)) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have heq := (Finset.mem_filter.mp hz).2.2.2
          rw [heq, mul_pow, stepWeight_sq]
          have hby_pos : (0 : ℝ) < √(bipBranch c K₀ r y : ℝ) :=
            sqrt_pos.mpr (by exact_mod_cast one_le_bipBranch c K₀ hr y)
          calc θ ^ 2 / (√(bipBranch c K₀ r x : ℝ) * √(bipBranch c K₀ r y : ℝ)) *
                walkMax c K₀ r θ m y z ^ 2
              = (θ ^ 2 / √(bipBranch c K₀ r x : ℝ)) *
                (walkMax c K₀ r θ m y z ^ 2 / √(bipBranch c K₀ r y : ℝ)) := by ring
            _ ≤ θ ^ 2 * (walkMax c K₀ r θ m y z ^ 2 / √(bipBranch c K₀ r y : ℝ)) := by
                gcongr
                exact div_le_self (by positivity) h1_br
      _ = θ ^ 2 * edgeBoundaryMass c K₀ r θ m x y := by rw [← Finset.mul_sum, edgeBoundaryMass]
      _ ≤ θ ^ 2 * θ ^ (2 * m) :=
          mul_le_mul_of_nonneg_left (edgeBoundaryMass_le c K₀ hr hfan hθ0 hθ1 m x y) (sq_nonneg θ)
      _ = θ ^ (2 * (m + 1)) := by ring
  calc ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z),
        walkMax c K₀ r θ (m + 1) x z ^ 2
      ≤ ∑ z ∈ N.biUnion Fy, walkMax c K₀ r θ (m + 1) x z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ ∑ y ∈ N, ∑ z ∈ Fy y, walkMax c K₀ r θ (m + 1) x z ^ 2 := by
        clear hsub
        induction N using Finset.induction_on with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.biUnion_insert, Finset.sum_insert ha]
          exact (sum_union_le_of_nonneg fun _ => sq_nonneg _).trans (add_le_add le_rfl ih)
    _ ≤ ∑ _y ∈ N, θ ^ (2 * (m + 1)) := Finset.sum_le_sum fun y _ => hterm y
    _ = N.card * θ ^ (2 * (m + 1)) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) := by
        gcongr
        exact_mod_cast card_bipAdj_le c K₀ hfan x

/-- Two-step boundary mass bound: coordinates where `walkMax (m + 2) x z > walkMax m x z` have
sum of squares at most `2 * max (r + 1) K₀ * θ ^ (2 * m + 2)`. -/
private theorem sum_sq_walkMax_twoStep_strict_le {r : ℕ} (hr : 2 ≤ r) (hfan : c.FanInAtMost r)
    {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (m : ℕ) (x : BipNode c K₀) :
    open Classical in
    ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 2) x z),
      walkMax c K₀ r θ (m + 2) x z ^ 2 ≤
      2 * (max (r + 1) K₀ : ℝ) * θ ^ (2 * m + 2) := by
  classical
  let A1 := Finset.univ.filter fun z =>
    walkMax c K₀ r θ (m + 1) x z < walkMax c K₀ r θ (m + 2) x z
  let A2 := Finset.univ.filter fun z =>
    walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z ∧
    walkMax c K₀ r θ (m + 2) x z = walkMax c K₀ r θ (m + 1) x z
  have hsub : (Finset.univ.filter fun z =>
      walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 2) x z) ⊆ A1 ∪ A2 := by
    intro z hz
    have hlt := (Finset.mem_filter.mp hz).2
    by_cases h1 : walkMax c K₀ r θ (m + 1) x z < walkMax c K₀ r θ (m + 2) x z
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ z, h1⟩)
    · have heq := le_antisymm (walkMax_mono_step c K₀ r θ (m + 1) x z) (not_lt.mp h1)
      exact Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_univ z, heq ▸ hlt, heq.symm⟩)
  have hsum1 := sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 (m + 1) x
  have hsum2 : ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 ≤
      (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) := by
    calc ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2
        = ∑ z ∈ A2, walkMax c K₀ r θ (m + 1) x z ^ 2 :=
          Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.mp hz).2.2]
      _ ≤ ∑ z ∈ Finset.univ.filter (fun z =>
            walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 1) x z),
            walkMax c K₀ r θ (m + 1) x z ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun z hz => Finset.mem_filter.mpr ⟨Finset.mem_univ z, (Finset.mem_filter.mp hz).2.1⟩)
            (fun _ _ _ => sq_nonneg _)
      _ ≤ (max (r + 1) K₀ : ℝ) * θ ^ (2 * (m + 1)) :=
          sum_sq_walkMax_strict_le c K₀ hr hfan hθ0 hθ1 m x
  set D_val : ℝ := (max (r + 1) K₀ : ℝ)
  change ∑ z ∈ A1, walkMax c K₀ r θ (m + 2) x z ^ 2 ≤ D_val * θ ^ (2 * (m + 2)) at hsum1
  change ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 ≤ D_val * θ ^ (2 * (m + 1)) at hsum2
  have hD_nn : 0 ≤ D_val := by positivity
  have hpow : θ ^ (2 * (m + 2)) ≤ θ ^ (2 * m + 2) :=
    pow_le_pow_of_le_one hθ0.le hθ1 (by omega)
  have hexp : 2 * (m + 1) = 2 * m + 2 := by ring
  rw [hexp] at hsum2
  calc ∑ z ∈ Finset.univ.filter (fun z => walkMax c K₀ r θ m x z < walkMax c K₀ r θ (m + 2) x z),
        walkMax c K₀ r θ (m + 2) x z ^ 2
      ≤ ∑ z ∈ A1 ∪ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ (∑ z ∈ A1, walkMax c K₀ r θ (m + 2) x z ^ 2) +
          ∑ z ∈ A2, walkMax c K₀ r θ (m + 2) x z ^ 2 :=
        sum_union_le_of_nonneg fun _ => sq_nonneg _
    _ ≤ D_val * θ ^ (2 * (m + 2)) + D_val * θ ^ (2 * m + 2) := add_le_add hsum1 hsum2
    _ ≤ 2 * D_val * θ ^ (2 * m + 2) := by nlinarith


end BipartiteKernel

end Cslib.Circuits.Frontier.Hypergraph
