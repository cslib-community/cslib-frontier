/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.GroupTheory.SLTower.Inst
public import CslibFrontier.Foundations.GroupTheory.SLTower.Base

/-!
# The tower as a `CoveringTower.Tower`, and its routes

The coset construction of `Cslib.SLTower.Inst` packaged as a
`Cslib.CoveringTower.Tower` (`Cslib.SLTower.tower`), and routes of length `m` from words of length
`m` (`Cslib.SLTower.exists_routes`): the word `g'g⁻¹` walks from `g` to `g'`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tower.Tower`.

## Main definitions

* `Cslib.SLTower.tower h n h2`: the tower.

## Main results

* `Cslib.SLTower.exists_routes`: routes from a diameter bound.
* `Cslib.SLTower.card_XJ`: the top level has fewer than `|SL_h(F₂)| · 2^e` chambers.
-/

public section

namespace Cslib.SLTower

open Finset

attribute [-instance] Subtype.instBEq

variable (h n : ℕ) [NeZero h]

/-- **The tower.** -/
@[expose] noncomputable def tower (h2 : 2 ≤ h) : Cslib.CoveringTower.Tower h (2 ^ ee h) (2 ^ ee h)
    (JJ h n) 1 where
  X := XX h n
  Ed := EE h n h2
  V := VV h n
  Fl := U h
  Nr := NN h
  fX := instFintypeXX h n
  dX := instDecXX h n
  fE := instFintypeEE h2
  dE := instDecEE h2
  fV := instFintypeVV
  dV := instDecVV
  fF := inferInstance
  dF := inferInstance
  fN := inferInstance
  dN' := inferInstance
  e0 := fun e => e.start
  e1 := fun e => (gen h2 e.kind : G h n) • e.start
  e_ne := fun e => (gen_smul_ne h2 _ _).symm
  ty := fun e => e.kind
  card_ed := fun j _ i => card_edges h2 j i
  deg := fun j _ c i => deg_edges h2 j c i
  vx := vert
  co := cor
  vx_co := fun _ i => vert_cor_bijective _ i
  card_fl := card_U h
  cN := fun ν => ν.elt
  dN := fun ν => x h ν.idx * ν.elt
  n_ne := fun ν e => x_ne_one ν.idx (by simpa using e.symm)
  nr := fun _ i => Equiv.ofBijective _ (nearFun_bijective h2 _ i)
  nr_vx0 := fun _ i e => rfl
  nr_vx1 := fun _ i e => by
    change vert i ((gen h2 e.val.kind : G h n) • e.val.start) = vert i e.val.start
    rw [gen_idx h2 i _ e.property, vert_th]
  nr_co := fun _ i e => by
    change s(cor i e.val.start, cor i ((gen h2 e.val.kind : G h n) • e.val.start)) =
      s((npair (idx i e.val.kind e.property) (cor i e.val.start)).elt,
        x h (npair (idx i e.val.kind e.property) (cor i e.val.start)).idx *
            (npair (idx i e.val.kind e.property) (cor i e.val.start)).elt)
    rw [gen_idx h2 i _ e.property, cor_th]
    exact npair_sym _ _
  π := pr
  πE := prE h2
  πV := prV
  π_ends := fun _ e => by
    change s(pr e.start, (gen h2 e.kind : G h n) • pr e.start) =
        s(pr e.start, pr ((gen h2 e.kind : G h n) • e.start))
    rw [tower_equivariant]
  π_ty := fun _ _ => rfl
  card_X := fun _ hj => card_XX_succ hj
  fibre := fun hj d => fibre_edges h2 hj d
  π_vx := fun _ i c => vert_pr i c
  π_co := fun _ i c => cor_pr i c
  host := fun {j} i => (exists_host (n := n) j i).choose
  host_inj := fun {j} hj i => ((exists_host (n := n) j i).choose_spec hj).1
  host_vx := fun {j} hj i v => ((exists_host (n := n) j i).choose_spec hj).2 v

variable {h n}


/-- The edges along a list of types. -/
@[expose] noncomputable def path (h2 : 2 ≤ h) {j : ℕ} : List (Fin h) → XX h n j → List (EE h n h2 j)
  | [], _ => []
  | k :: l, c => edge h2 k c :: path h2 l ((gen h2 k : G h n) • c)

theorem length_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (c : XX h n j) : (path h2 l c).length =
    l.length := by
  induction l generalizing c with
  | nil => rfl
  | cons k l ih => rw [path, List.length_cons, ih, List.length_cons]

theorem step_edge (h2 : 2 ≤ h) {j : ℕ} (k : Fin h) (c : XX h n j) :
    (tower h n h2).step (edge h2 k c) c = (gen h2 k : G h n) • c := by
  change (if (edge h2 k c).start = c then
    (gen h2 (edge h2 k c).kind : G h n) • (edge h2 k c).start else (edge h2 k c).start) = _
  rcases edge_end h2 k c with e | e
  · simp [e, edge_type]
  · rw [ite_eq_right (e ▸ gen_smul_ne h2 k c), e]

theorem walk_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (c : XX h n j) :
    (tower h n h2).Walk c (path h2 l c) (((l.reverse.map (gen h2)).prod : G h n) • c : XX h n j) :=
        by
  induction l generalizing c with
  | nil => exact (one_smul _ c).symm
  | cons k l ih =>
    refine ⟨(edge_end h2 k c).imp_right fun e => ?_, ?_⟩
    · change (gen h2 (edge h2 k c).kind : G h n) • (edge h2 k c).start = c
      rw [edge_type, e, gen_gen]
    · simpa [step_edge, mul_smul] using ih ((gen h2 k : G h n) • c)

theorem count_path (h2 : 2 ≤ h) {j : ℕ} (l : List (Fin h)) (e : EE h n h2 j) :
    ∑ c : XX h n j, (path h2 l c).count e ≤ 2 * l.length := by
  induction l with
  | nil => simp [path]
  | cons k l ih =>
    have h3 : ∑ c : XX h n j, (path h2 l ((gen h2 k : G h n) • c)).count e =
        ∑ c : XX h n j, (path h2 l c).count e :=
      Equiv.sum_comp (MulAction.toPerm (gen h2 k : G h n)) fun c => (path h2 l c).count e
    have h4 : #(univ.filter fun c : XX h n j => edge h2 k c = e) ≤ 2 :=
      (card_le_card (t := {e.start, (gen h2 k : G h n) • e.start}) fun c hc => by
        rcases edge_end h2 k c with e1 | e1 <;>
          simp [← (mem_filter.1 hc).2, e1, gen_gen]).trans card_le_two
    simp only [path, List.count_cons, beq_iff_eq, sum_add_distrib, h3, ← card_filter,
      List.length_cons]
    omega

/-- The chambers of the first level are the elements of the group. -/
theorem smul_bijective (c : XX h n 0) : Function.Bijective fun g : G h n => g • c := by
  refine ⟨fun g g' e => ?_, MulAction.exists_smul_eq (G h n) c⟩
  induction c using QuotientGroup.induction_on with | H a => ?_
  have e2 := QuotientGroup.eq.1
    (e : (QuotientGroup.mk (g * a) : XX h n 0) = QuotientGroup.mk (g' * a))
  rw [Gam_zero, Subgroup.mem_bot, inv_mul_eq_one] at e2
  exact mul_right_cancel e2

/-- The route. -/
@[expose] noncomputable def rte (h2 : 2 ≤ h) (w : G h n → List (Fin h))
    (c c' : XX h n 0) : List (EE h n h2 0) :=
  path h2 (w ((Equiv.ofBijective _ (smul_bijective c)).symm c')).reverse c

theorem rte_walk (h2 : 2 ≤ h) (w : G h n → List (Fin h)) (hw : ∀ g, ((w g).map (gen h2)).prod = g)
    (c c' : XX h n 0) :
    (tower h n h2).Walk c (rte h2 w c c') c' := by
  have h1 := walk_path h2 (w ((Equiv.ofBijective _ (smul_bijective c)).symm c')).reverse c
  have h3 : ((Equiv.ofBijective _ (smul_bijective c)).symm c' : G h n) • c = c' :=
    (Equiv.ofBijective _ (smul_bijective c)).apply_symm_apply c'
  rwa [List.reverse_reverse, hw, h3] at h1

theorem rte_length (h2 : 2 ≤ h) (w : G h n → List (Fin h)) {m : ℕ} (hw : ∀ g, (w g).length ≤ m)
    (c c' : XX h n 0) :
    (rte h2 w c c').length ≤ m := by
  rw [rte, length_path, List.length_reverse]
  exact hw _

theorem rte_use (h2 : 2 ≤ h) (w : G h n → List (Fin h)) {m : ℕ} (hw : ∀ g, (w g).length ≤ m)
    (e : EE h n h2 0) :
    ∑ c, ∑ c', (rte h2 w c c').count e ≤ 2 * (Fintype.card (XX h n 0) * m) := by
  classical
  have h1 (c : XX h n 0) := Equiv.sum_comp (Equiv.ofBijective _ (smul_bijective c)).symm
    fun g => (path h2 (w g).reverse c).count e
  simp_rw [rte, h1]
  rw [sum_comm]
  calc ∑ g : G h n, ∑ c : XX h n 0, (path h2 (w g).reverse c).count e
      ≤ ∑ _g : G h n, 2 * m := sum_le_sum fun g _ =>
        (count_path h2 _ e).trans (by simpa using Nat.mul_le_mul_left 2 (hw g))
    _ = 2 * (Fintype.card (XX h n 0) * m) := by
        rw [sum_const, card_univ, smul_eq_mul,
          Fintype.card_congr (Equiv.ofBijective _ (smul_bijective (QuotientGroup.mk 1 : XX h n 0)))]
        ring

/-- **Routes.** -/
theorem exists_routes (h2 : 2 ≤ h) {m : ℕ} (hm : ∀ g : G h n, WL h2 g m) :
    Nonempty (Cslib.CoveringTower.Routes (tower h n h2) m (2 * (Fintype.card (XX h n 0) * m))) := by
  choose w hw1 hw2 using hm
  exact ⟨{ rt := rte h2 w
           walk := rte_walk h2 w hw2
           len := rte_length h2 w hw1
           use := rte_use h2 w hw1 }⟩

omit [NeZero h] in
/-- Sums over the near pairs. -/
theorem sum_NN {M : Type*} [AddCommMonoid M] (f : Fin (h - 1) → U h → M)
    (hf : ∀ l u, f l (x h l * u) = f l u) :
    ∑ l, ∑ u, f l u = ∑ ν : NN h, f ν.idx ν.elt + ∑ ν : NN h,
        f ν.idx ν.elt := by
  classical
  rw [← Fintype.sum_prod_type (fun p : Fin (h - 1) × U h => f p.1 p.2),
    ← sum_filter_add_sum_filter_not univ (fun p : Fin (h - 1) × U h => FU p.1 p.2)]
  have h1 : ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => FU p.1 p.2), f p.1 p.2 =
      ∑ ν : NN h, f ν.idx ν.elt :=
    sum_bij' (fun p hp => ⟨p.1, p.2, (mem_filter.1 hp).2⟩) (fun ν _ => (ν.idx, ν.elt))
      (fun _ _ => mem_univ _) (fun ν _ => mem_filter.2 ⟨mem_univ _, ν.first⟩)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  have h3 : ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => ¬ FU p.1 p.2), f p.1 p.2 =
      ∑ p ∈ univ.filter (fun p : Fin (h - 1) × U h => FU p.1 p.2), f p.1 p.2 :=
    sum_bij' (fun p _ => (p.1, x h p.1 * p.2)) (fun p _ => (p.1, x h p.1 * p.2))
      (fun _ hp => mem_filter.2 ⟨mem_univ _, (FU_iff _ _).2 (mem_filter.1 hp).2⟩)
      (fun _ hp => mem_filter.2 ⟨mem_univ _, fun e => (FU_iff _ _).1 e (mem_filter.1 hp).2⟩)
      (fun _ _ => Prod.ext rfl (by rw [← mul_assoc, x_mul_self, one_mul]))
      (fun _ _ => Prod.ext rfl (by rw [← mul_assoc, x_mul_self, one_mul]))
      (fun _ _ => (hf _ _).symm)
  rw [h3, h1]

section Numbers

variable (h n)

theorem card_XJ (h2 : 2 ≤ h) :
    Fintype.card ((tower h n h2).X (JJ h n)) < Nat.card (SL2 h) * 2 ^ ee h := by
  have he : 0 < ee h := by
    have : 2 * 1 ≤ h * (h - 1) := Nat.mul_le_mul h2 (by omega)
    unfold ee
    omega
  refine Nat.lt_of_mul_lt_mul_right (a := (2 ^ ee h) ^ JJ h n) ?_
  calc Fintype.card ((tower h n h2).X (JJ h n)) * (2 ^ ee h) ^ JJ h n
      = Nat.card (SL2 h) * 2 ^ ((h ^ 2 - 1) * n) := by
        have := card_XX (h := h) (n := n) (j := JJ h n) le_rfl
        rwa [card_G] at this
    _ < Nat.card (SL2 h) * (2 ^ ee h * (2 ^ ee h) ^ JJ h n) := by
        refine Nat.mul_lt_mul_of_pos_left ?_ Nat.card_pos
        rw [← pow_succ', ← pow_mul]
        exact Nat.pow_lt_pow_right (by omega) (Nat.lt_mul_div_succ _ he)
    _ = Nat.card (SL2 h) * 2 ^ ee h * (2 ^ ee h) ^ JJ h n := (mul_assoc _ _ _).symm

end Numbers

end Cslib.SLTower
