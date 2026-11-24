/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Walk
public import Mathlib.Data.Finsupp.Weight

/-!
# Grades, evaluation at one and transposition (§5.2: the grade bound, Lemmas 5.2 and 5.3)

* `piece_grade`: every grade of a routing is congruent to the total weight `W` of the four views
  modulo `2` and at most `W` in absolute value, so `Π_k = 0` unless `k ≡ W (mod 2)` and
  `|k| ≤ W`. With `wt x = wt v = a` and `wt y = wt u = b`, `W = 2H` and `Π_k = 0` unless `k` is
  even and `|k| ≤ 2H`.
* `piece_eval_one` (Lemma 5.2): if `wt x = wt v`, then `Π_{x,y,u,v}(1) = [x = v][y = u]`.
* `piece_transpose` (Lemma 5.3): `Π_{x,u,y,v}(z) = Π_{x,y,u,v}(1/z)`.
* `piece_example`: the example after Lemma 5.3, `Π = 2 - z²`.

## General tools for transport sums

* `transportG`: the transport sum with coefficients in any commutative semiring; `transport` is
  `transportG` over `Lp` (`transport_eq_transportG`).
* `map_transportG`: a ring hom of the coefficients maps the transport sum to the transport sum of
  the mapped rules.
* `transportG_map`: renaming the places injectively.
* `transportG_mem`: a graded bound; if every rule lies in `M (w s + w t)` for a multiplicative
  filtration `M`, the transport sum lies in `M (∑ w src + ∑ w tgt)`.
* `transportG_eq_of_leading`: the exhaustion argument; if every source has a rule `1` to an
  "opposite" target and every other nonzero rule goes to a target of strictly larger `ψ`-weight,
  and the target weight is at most the opposite weight, the transport sum is `[opp src = tgt]`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset LaurentPolynomial
open scoped Pointwise

/-! ### General transport sums -/

section General

variable {P : Type} [DecidableEq P]

/-- The transport sum with coefficients in any commutative semiring. -/
noncomputable def transportG {S : Type*} [CommSemiring S] (src tgt : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → S) : S :=
  ((src.map fun s : P × ℕ => ∑ t ∈ tgt.toFinset,
      MvPolynomial.C (R s.1 s.2 t.1 t.2) * MvPolynomial.X t).prod).coeff (Multiset.toFinsupp tgt)

theorem transport_eq_transportG (src tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → Lp) :
    transport src tgt R = transportG src tgt R := rfl

/-- A ring hom of the coefficients commutes with transport sums. -/
theorem map_transportG {S S' F : Type*} [CommSemiring S] [CommSemiring S'] [FunLike F S S']
    [RingHomClass F S S'] (f : F) (src tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → S) :
    f (transportG src tgt R) = transportG src tgt fun p i p' j => f (R p i p' j) := by
  unfold transportG
  rw [← RingHom.coe_coe f, ← MvPolynomial.coeff_map, map_multiset_prod, Multiset.map_map]
  congr 2
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun s _ => ?_)
  simp [map_sum, MvPolynomial.map_C, MvPolynomial.map_X]

/-- Renaming the places of a transport sum by an injective map. -/
theorem transportG_map {Q : Type} [DecidableEq Q] {S : Type*} [CommSemiring S] (e : P → Q)
    (he : Function.Injective e) (src tgt : Multiset (P × ℕ)) (R : Q → ℕ → Q → ℕ → S) :
    transportG (src.map (Prod.map e id)) (tgt.map (Prod.map e id)) R =
      transportG src tgt fun p i p' j => R (e p) i (e p') j := by
  have hf : Function.Injective (Prod.map e (id : ℕ → ℕ)) := he.prodMap Function.injective_id
  unfold transportG
  have key : Multiset.toFinsupp (tgt.map (Prod.map e id)) =
      (Multiset.toFinsupp tgt).mapDomain (Prod.map e id) := by
    rw [Multiset.toFinsupp_eq_iff, ← Finsupp.toMultiset_map, Multiset.toFinsupp_toMultiset]
  rw [key]
  conv_rhs => rw [← MvPolynomial.coeff_rename_mapDomain _ hf]
  rw [map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 2
  refine congrArg Multiset.prod (Multiset.map_congr rfl fun s _ => ?_)
  rw [Function.comp_apply, Function.comp_apply, Multiset.toFinset_map,
    Finset.sum_image fun a _ b _ h => hf h]
  simp [map_sum, MvPolynomial.rename_X]

/-- The weight of the monomial of a multiset. -/
theorem weight_toFinsupp {α M : Type*} [DecidableEq α] [AddCommMonoid M] (w : α → M)
    (l : Multiset α) : Finsupp.weight w (Multiset.toFinsupp l) = (l.map w).sum := by
  induction l using Multiset.induction_on with
  | empty => simp [Multiset.toFinsupp_zero]
  | cons a l ih =>
    rw [← Multiset.singleton_add, Multiset.toFinsupp_add, map_add, Multiset.toFinsupp_singleton,
      Finsupp.weight_single, ih, Multiset.map_add, Multiset.sum_add, Multiset.map_singleton,
      Multiset.sum_singleton, one_smul]

/-- **A graded bound for transport sums.** If `M` is a multiplicative filtration and every rule
from a source `s` to a target `t` lies in `M (w s + w t)`, the transport sum lies in
`M (∑ w src + ∑ w tgt)`. -/
theorem transportG_mem {S : Type*} [CommRing S] (M : ℕ → AddSubgroup S)
    (hmul : ∀ a b x y, x ∈ M a → y ∈ M b → x * y ∈ M (a + b)) (hone : (1 : S) ∈ M 0)
    (w : P × ℕ → ℕ) (src tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → S)
    (hR : ∀ s ∈ src, ∀ t ∈ tgt, R s.1 s.2 t.1 t.2 ∈ M (w s + w t)) :
    transportG src tgt R ∈ M ((src.map w).sum + (tgt.map w).sum) := by
  have key : ∀ l : Multiset (P × ℕ), (∀ s ∈ l, ∀ t ∈ tgt, R s.1 s.2 t.1 t.2 ∈ M (w s + w t)) →
      ∀ m, ((l.map fun s : P × ℕ => ∑ t ∈ tgt.toFinset,
        MvPolynomial.C (R s.1 s.2 t.1 t.2) * MvPolynomial.X t).prod).coeff m ∈
        M ((l.map w).sum + Finsupp.weight w m) := by
    intro l
    induction l using Multiset.induction_on with
    | empty =>
      intro _ m
      simp only [Multiset.map_zero, Multiset.prod_zero, Multiset.sum_zero, MvPolynomial.coeff_one]
      split_ifs with h
      · subst h; simpa using hone
      · exact zero_mem _
    | cons s l ih =>
      intro hl m
      have ih' := ih fun s' hs' => hl s' (Multiset.mem_cons_of_mem hs')
      simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
      rw [Finset.sum_mul, MvPolynomial.coeff_sum]
      refine sum_mem fun t ht => ?_
      rw [mul_assoc, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_mul']
      split_ifs with hm
      · have hmt : m t ≠ 0 := Finsupp.mem_support_iff.mp hm
        have hw := Finsupp.weight_sub_single_add (w := w) hmt
        have := hmul _ _ _ _ (hl s (Multiset.mem_cons_self s l) t (Multiset.mem_toFinset.mp ht))
          (ih' (m - Finsupp.single t 1))
        convert this using 2
        omega
      · rw [mul_zero]; exact zero_mem _
  have := key src hR (Multiset.toFinsupp tgt)
  rwa [weight_toFinsupp] at this

end General

/-! ### Lower bounds on weighted degrees -/

section Leading

variable {σ S : Type*} [CommRing S]

/-- Every monomial of `p` has `ψ`-weight at least `a`. -/
def WtGe (ψ : σ → ℤ) (a : ℤ) (p : MvPolynomial σ S) : Prop :=
  ∀ m ∈ p.support, a ≤ Finsupp.weight ψ m

theorem WtGe.zero (ψ : σ → ℤ) (a : ℤ) : WtGe ψ a (0 : MvPolynomial σ S) := by
  intro m hm; simp at hm

theorem WtGe.one (ψ : σ → ℤ) : WtGe ψ 0 (1 : MvPolynomial σ S) := by
  classical
  intro m hm
  rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_one] at hm
  split_ifs at hm with h
  · subst h; simp
  · exact absurd rfl hm

theorem WtGe.mono {ψ : σ → ℤ} {a b : ℤ} {p : MvPolynomial σ S} (h : WtGe ψ a p) (hb : b ≤ a) :
    WtGe ψ b p := fun m hm => hb.trans (h m hm)

theorem WtGe.add {ψ : σ → ℤ} {a : ℤ} {p q : MvPolynomial σ S} (hp : WtGe ψ a p)
    (hq : WtGe ψ a q) : WtGe ψ a (p + q) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (MvPolynomial.support_add hm) with h | h
  exacts [hp m h, hq m h]

theorem WtGe.mul {ψ : σ → ℤ} {a b c : ℤ} {p q : MvPolynomial σ S} (hp : WtGe ψ a p)
    (hq : WtGe ψ b q) (hc : c ≤ a + b) : WtGe ψ c (p * q) := by
  classical
  intro m hm
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hm)
  rw [map_add]
  have := hp x hx
  have := hq y hy
  omega

theorem WtGe.C_mul_X {ψ : σ → ℤ} {a : ℤ} (c : S) (t : σ) (h : c ≠ 0 → a ≤ ψ t) :
    WtGe ψ a (MvPolynomial.C c * MvPolynomial.X t) := by
  intro m hm
  rw [MvPolynomial.C_mul_X_eq_monomial] at hm
  have hc : c ≠ 0 := by rintro rfl; simp at hm
  rw [Finset.mem_singleton.mp (MvPolynomial.support_monomial_subset hm), Finsupp.weight_single,
    one_smul]
  exact h hc

theorem WtGe.sum {ψ : σ → ℤ} {a : ℤ} {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ S)
    (h : ∀ i ∈ s, WtGe ψ a (f i)) : WtGe ψ a (∑ i ∈ s, f i) :=
  Finset.sum_induction f (WtGe ψ a) (fun _ _ => WtGe.add) (WtGe.zero ψ a) h

/-- **Leading terms of a product.** If `G i` has weight at least `a i` and `F i - G i` weight at
least `a i + 1`, then `∏ F - ∏ G` has weight at least `∑ a + 1`. -/
theorem WtGe.prod_sub {ψ : σ → ℤ} {ι : Type*} (l : Multiset ι) (F G : ι → MvPolynomial σ S)
    (a : ι → ℤ) (hG : ∀ i ∈ l, WtGe ψ (a i) (G i)) (hFG : ∀ i ∈ l, WtGe ψ (a i + 1) (F i - G i)) :
    WtGe ψ (l.map a).sum (l.map G).prod ∧
      WtGe ψ ((l.map a).sum + 1) ((l.map F).prod - (l.map G).prod) := by
  induction l using Multiset.induction_on with
  | empty => simpa using ⟨WtGe.one ψ, WtGe.zero ψ 1⟩
  | cons i l ih =>
    obtain ⟨ih1, ih2⟩ := ih (fun j hj => hG j (Multiset.mem_cons_of_mem hj))
      (fun j hj => hFG j (Multiset.mem_cons_of_mem hj))
    have hGi := hG i (Multiset.mem_cons_self _ _)
    have hFGi := hFG i (Multiset.mem_cons_self _ _)
    have hFi : WtGe ψ (a i) (F i) := by
      have := hGi.add (hFGi.mono (by omega)); simpa using this
    simp only [Multiset.map_cons, Multiset.prod_cons, Multiset.sum_cons]
    refine ⟨hGi.mul ih1 le_rfl, ?_⟩
    have e : F i * (l.map F).prod - G i * (l.map G).prod =
        F i * ((l.map F).prod - (l.map G).prod) + (F i - G i) * (l.map G).prod := by ring
    rw [e]
    exact (hFi.mul ih2 (by omega)).add (hFGi.mul ih1 (by omega))

end Leading

section LeadingTransport

variable {P : Type} [DecidableEq P] {S : Type*} [CommRing S]

/-- **The exhaustion argument for transport sums.** Suppose every source `s` has the rule `1` to
an opposite target `opp s`, every other nonzero rule from `s` goes to a target of `ψ`-weight
larger than `ψ (opp s)`, and the total `ψ`-weight of the targets is at most that of the
opposites of the sources. Then only the routing sending every source to its opposite survives. -/
theorem transportG_eq_of_leading (ψ : P × ℕ → ℤ) (opp : P × ℕ → P × ℕ)
    (src tgt : Multiset (P × ℕ)) (R : P → ℕ → P → ℕ → S)
    (hdiag : ∀ s ∈ src, R s.1 s.2 (opp s).1 (opp s).2 = 1)
    (hoff : ∀ s ∈ src, ∀ t ∈ tgt, t ≠ opp s → R s.1 s.2 t.1 t.2 ≠ 0 → ψ (opp s) < ψ t)
    (hwt : (tgt.map ψ).sum ≤ ((src.map opp).map ψ).sum) :
    transportG src tgt R = if src.map opp = tgt then 1 else 0 := by
  classical
  let F : P × ℕ → MvPolynomial (P × ℕ) S := fun s => ∑ t ∈ tgt.toFinset,
      MvPolynomial.C (R s.1 s.2 t.1 t.2) * MvPolynomial.X t
  let G : P × ℕ → MvPolynomial (P × ℕ) S := fun s =>
    if opp s ∈ tgt then MvPolynomial.X (opp s) else 0
  have hGw : ∀ s ∈ src, WtGe ψ (ψ (opp s)) (G s) := by
    intro s _
    simp only [G]
    split_ifs
    · rw [← one_mul (MvPolynomial.X _), ← MvPolynomial.C_1]
      exact WtGe.C_mul_X _ _ fun _ => le_rfl
    · exact WtGe.zero _ _
  have hFG : ∀ s ∈ src, WtGe ψ (ψ (opp s) + 1) (F s - G s) := by
    intro s hs
    have e : F s - G s = ∑ t ∈ tgt.toFinset,
        MvPolynomial.C (if t = opp s then 0 else R s.1 s.2 t.1 t.2) * MvPolynomial.X t := by
      rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add]
      simp only [F, G, ← Finset.sum_sub_distrib, ← sub_mul, ← map_sub]
      have h1 : ∀ t : P × ℕ, R s.1 s.2 t.1 t.2 - (if t = opp s then 0 else R s.1 s.2 t.1 t.2) =
          if t = opp s then 1 else 0 := by
        intro t
        split_ifs with h
        · subst h; simp [hdiag s hs]
        · simp
      simp only [h1, apply_ite MvPolynomial.C, map_one, map_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Multiset.mem_toFinset]
    rw [e]
    refine WtGe.sum _ _ fun t ht => WtGe.C_mul_X _ _ fun hc => ?_
    split_ifs at hc with h
    · exact absurd rfl hc
    · have := hoff s hs t (Multiset.mem_toFinset.mp ht) h hc
      omega
  obtain ⟨-, hdiff⟩ := WtGe.prod_sub src F G (fun s => ψ (opp s)) hGw hFG
  have hcoeff : transportG src tgt R = ((src.map G).prod).coeff (Multiset.toFinsupp tgt) := by
    change ((src.map F).prod).coeff _ = _
    by_contra hne
    have hne' : ((src.map F).prod - (src.map G).prod).coeff (Multiset.toFinsupp tgt) ≠ 0 := by
      rw [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, sub_ne_zero]; exact hne
    have := hdiff _ (MvPolynomial.mem_support_iff.mpr hne')
    rw [weight_toFinsupp] at this
    have hwt' : (tgt.map ψ).sum ≤ (src.map fun s => ψ (opp s)).sum := by
      simpa [Multiset.map_map, Function.comp_def] using hwt
    omega
  rw [hcoeff]
  by_cases hall : ∀ s ∈ src, opp s ∈ tgt
  · have hmon : ∀ l : Multiset (P × ℕ), (∀ s ∈ l, opp s ∈ tgt) →
        (l.map G).prod = MvPolynomial.monomial (Multiset.toFinsupp (l.map opp)) 1 := by
      intro l
      induction l using Multiset.induction_on with
      | empty => intro _; simp [Multiset.toFinsupp_zero]
      | cons s l ih =>
        intro hl
        rw [Multiset.map_cons, Multiset.prod_cons, ih fun x
            hx => hl x (Multiset.mem_cons_of_mem hx),
          Multiset.map_cons, ← Multiset.singleton_add, Multiset.toFinsupp_add,
          Multiset.toFinsupp_singleton, MvPolynomial.monomial_single_add, pow_one]
        simp only [G, hl s (Multiset.mem_cons_self _ _), ↓reduceIte]
    rw [hmon src hall, MvPolynomial.coeff_monomial]
    by_cases h : src.map opp = tgt
    · simp [h]
    · have h' : Multiset.toFinsupp (src.map opp) ≠ Multiset.toFinsupp tgt :=
        fun h' => h (Multiset.toFinsupp.injective h')
      simp [h, h']
  · simp only [not_forall] at hall
    obtain ⟨s, hs, hst⟩ := hall
    have h0 : (src.map G).prod = 0 :=
      Multiset.prod_eq_zero (Multiset.mem_map.mpr ⟨s, hs, by simp [G, hst]⟩)
    have hne : src.map opp ≠ tgt := fun heq => hst (heq ▸ Multiset.mem_map_of_mem opp hs)
    rw [h0]
    simp [hne]

end LeadingTransport

/-! ### Located multisets -/

theorem map_located {P Q : Type} (g : P → Q) (c : P) (σ : Multiset ℕ) :
    (located c σ).map (fun s => (g s.1, s.2)) = located (g c) σ := by
  simp [located, Multiset.map_map]

theorem sum_map_located {P : Type} (f : P × ℕ → ℤ) (c : P) (σ : Multiset ℕ) (k : ℤ)
    (h : ∀ i, f (c, i) = k * ((i : ℤ) + 1)) : ((located c σ).map f).sum = k * (wt σ : ℤ) := by
  induction σ using Multiset.induction_on with
  | empty => simp [located]
  | cons i σ ih =>
    simp only [located, Multiset.map_cons, Multiset.sum_cons, wt_cons] at ih ⊢
    rw [ih, h]; push_cast; ring

theorem sum_map_located_succ {P : Type} (c : P) (σ : Multiset ℕ) :
    ((located c σ).map fun s : P × ℕ => s.2 + 1).sum = wt σ := by
  simp [located, wt, Multiset.map_map]

theorem proj_located {P : Type} [DecidableEq P] (c c' : P) (σ : Multiset ℕ) :
    ((located c' σ).filter (fun t => t.1 = c)).map Prod.snd = if c' = c then σ else 0 := by
  by_cases h : c' = c
  · subst h; simp [located, Multiset.filter_map]
  · simp [located, Multiset.filter_map, h]

/-! ### The grade bound -/

/-- Laurent polynomials whose exponents are `≡ n (mod 2)` and at most `n` in absolute value. -/
def gradeGroup (n : ℕ) : AddSubgroup Lp where
  carrier := {f | ∀ e, f.coeff e ≠ 0 → e % 2 = (n : ℤ) % 2 ∧ |e| ≤ n}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg e he
    simp only [Set.mem_ofPred_eq, AddMonoidAlgebra.coeff_add, Finsupp.add_apply] at hf hg he
    by_cases h : f.coeff e = 0
    · rw [h, zero_add] at he; exact hg e he
    · exact hf e h
  neg_mem' := by
    intro f hf e he
    simp only [Set.mem_ofPred_eq, AddMonoidAlgebra.coeff_neg, Finsupp.neg_apply, ne_eq,
      neg_eq_zero] at hf he
    exact hf e he

theorem mem_gradeGroup {n : ℕ} {f : Lp} :
    f ∈ gradeGroup n ↔ ∀ e, f.coeff e ≠ 0 → e % 2 = (n : ℤ) % 2 ∧ |e| ≤ n := Iff.rfl

theorem gradeGroup_mul {a b : ℕ} {x y : Lp} (hx : x ∈ gradeGroup a) (hy : y ∈ gradeGroup b) :
    x * y ∈ gradeGroup (a + b) := by
  classical
  intro e he
  obtain ⟨e₁, h₁, e₂, h₂, rfl⟩ :=
    Finset.mem_add.mp (AddMonoidAlgebra.support_coeff_mul_subset x y
        (Finsupp.mem_support_iff.mpr he))
  obtain ⟨p₁, q₁⟩ := hx e₁ (Finsupp.mem_support_iff.mp h₁)
  obtain ⟨p₂, q₂⟩ := hy e₂ (Finsupp.mem_support_iff.mp h₂)
  rw [abs_le] at q₁ q₂ ⊢
  push_cast
  refine ⟨by omega, by omega, by omega⟩

theorem gradeGroup_of_eq {a b : ℕ} {x : Lp} (hx : x ∈ gradeGroup a) (h : a = b) :
    x ∈ gradeGroup b := h ▸ hx

theorem T_mem_gradeGroup {n : ℕ} {e : ℤ} (h₁ : e % 2 = (n : ℤ) % 2) (h₂ : -(n : ℤ) ≤ e)
    (h₃ : e ≤ n) : (T e : Lp) ∈ gradeGroup n := by
  intro k hk
  rw [T_apply] at hk
  split_ifs at hk with h
  · subst h; exact ⟨h₁, abs_le.mpr ⟨h₂, h₃⟩⟩
  · exact absurd rfl hk

theorem C_mem_gradeGroup (c : ℤ) : (LaurentPolynomial.C c : Lp) ∈ gradeGroup 0 := by
  intro k hk
  rw [C_apply] at hk
  split_ifs at hk with h
  · subst h; simp
  · exact absurd rfl hk

theorem one_mem_gradeGroup : (1 : Lp) ∈ gradeGroup 0 := by
  rw [← T_zero]; exact T_mem_gradeGroup (by simp) (by simp) (by simp)

theorem cubeC_mem_gradeGroup (i j n : ℕ) (h : i + j + 2 = n) : Cube.C i j ∈ gradeGroup n := by
  have hd := d_add_mod_two i j
  have hd' := d_le_add i j
  refine gradeGroup_of_eq (gradeGroup_mul (C_mem_gradeGroup (chi i j))
    (T_mem_gradeGroup (n := n) ?_ ?_ ?_)) (by omega) <;> omega

theorem bar_cubeC_mem_gradeGroup (i j n : ℕ) (h : i + j + 2 = n) :
    bar (Cube.C i j) ∈ gradeGroup n := by
  have hd := d_add_mod_two i j
  have hd' := d_le_add i j
  rw [bar, Cube.C, map_mul, invert_C, invert_T]
  refine gradeGroup_of_eq (gradeGroup_mul (C_mem_gradeGroup (chi i j))
    (T_mem_gradeGroup (n := n) ?_ ?_ ?_)) (by omega) <;> omega

theorem oneSubZ2_mul_mem_gradeGroup (i j n : ℕ) (h : i + j + 2 = n) :
    oneSubZ2 * Cube.C i j ∈ gradeGroup n := by
  have hd := d_add_mod_two i j
  have hd' := d_le_add i j
  have h1 : oneSubZ2 ∈ gradeGroup 2 := by
    rw [oneSubZ2, ← T_zero]
    exact sub_mem (T_mem_gradeGroup (by simp) (by simp) (by simp))
      (T_mem_gradeGroup (by simp) (by simp) (by simp))
  refine gradeGroup_of_eq (gradeGroup_mul h1 (gradeGroup_mul (C_mem_gradeGroup (chi i j))
    (T_mem_gradeGroup (n := i + j) ?_ ?_ ?_))) (by omega) <;> omega

theorem oneSubZm2_mul_mem_gradeGroup (i j n : ℕ) (h : i + j + 2 = n) :
    oneSubZm2 * bar (Cube.C i j) ∈ gradeGroup n := by
  have hd := d_add_mod_two i j
  have hd' := d_le_add i j
  have h1 : oneSubZm2 ∈ gradeGroup 2 := by
    rw [oneSubZm2, ← T_zero]
    exact sub_mem (T_mem_gradeGroup (by simp) (by simp) (by simp))
      (T_mem_gradeGroup (by simp) (by simp) (by simp))
  rw [bar, Cube.C, map_mul, invert_C, invert_T]
  refine gradeGroup_of_eq (gradeGroup_mul h1 (gradeGroup_mul (C_mem_gradeGroup (chi i j))
    (T_mem_gradeGroup (n := i + j) ?_ ?_ ?_))) (by omega) <;> omega

theorem eqL_mem_gradeGroup (i j n : ℕ) (h : i + j + 2 = n) : eqL i j ∈ gradeGroup n := by
  unfold eqL
  split_ifs with hij
  · rw [← T_zero]; exact T_mem_gradeGroup (by omega) (by omega) (by omega)
  · exact zero_mem _

theorem rule_mem_gradeGroup (p : Corner) (i : ℕ) (p' : Corner) (j : ℕ) :
    rule p i p' j ∈ gradeGroup (i + 1 + (j + 1)) := by
  cases p <;> cases p' <;> simp only [rule] <;>
    first
    | with_reducible exact zero_mem _
    | (with_reducible apply eqL_mem_gradeGroup); omega
    | (with_reducible apply cubeC_mem_gradeGroup); omega
    | (with_reducible apply bar_cubeC_mem_gradeGroup); omega
    | (with_reducible apply oneSubZ2_mul_mem_gradeGroup); omega
    | (with_reducible apply oneSubZm2_mul_mem_gradeGroup); omega

/-- The total weight of the four views. -/
def totalWt (V : Corner → Label) : ℕ :=
  labelWt (V .x) + labelWt (V .y) + labelWt (V .u) + labelWt (V .v)

/-- **The grades.** Every exponent of `Π_{x,y,u,v}` is congruent to the total weight of the views
modulo `2` and at most it in absolute value. -/
theorem piece_grade (V : Corner → Label) (k : ℤ) (h : (piece V).coeff k ≠ 0) :
    k % 2 = (totalWt V : ℤ) % 2 ∧ |k| ≤ totalWt V := by
  have hmem := transportG_mem gradeGroup (fun _ _ _ _ => gradeGroup_mul) one_mem_gradeGroup
    (fun s => s.2 + 1) (sourcesOf V) (targetsOf V) rule
    (fun s _ t _ => rule_mem_gradeGroup s.1 s.2 t.1 t.2)
  have e : ((sourcesOf V).map fun s : Corner × ℕ => s.2 + 1).sum +
      ((targetsOf V).map fun s : Corner × ℕ => s.2 + 1).sum = totalWt V := by
    simp only [sourcesOf, targetsOf, Multiset.map_add, Multiset.sum_add, sum_map_located_succ,
      totalWt, labelWt]
    omega
  rw [e] at hmem
  exact hmem k h

/-! ### Evaluation at one -/

/-- The opposite corner along a diagonal. -/
def oppC : Corner → Corner
  | .x => .v
  | .v => .x
  | .y => .u
  | .u => .y

/-- The weight used in the exhaustion argument of Lemma 5.2: `-(j+1)` at `x`, `j+1` at `v`. -/
def psiE : Corner × ℕ → ℤ
  | (.x, j) => -((j : ℤ) + 1)
  | (.v, j) => (j : ℤ) + 1
  | _ => 0

theorem crossing_iff (V : Corner → Label) :
    (sourcesOf V).map (fun s => (oppC s.1, s.2)) = targetsOf V ↔ crossing V := by
  simp only [sourcesOf, Multiset.map_add, map_located]
  simp only [oppC]
  constructor
  · intro heq
    have proj := fun c => congrArg (fun M => (M.filter (fun t => t.1 = c)).map Prod.snd) heq
    have hv := proj .v
    have hu := proj .u
    have hy := proj .y
    have hx := proj .x
    simp only [targetsOf, Multiset.filter_add, Multiset.map_add, proj_located] at hv hu hy hx
    simp only [↓reduceIte, reduceCtorEq, Multiset.add_zero, Multiset.zero_add] at hv hu hy hx
    exact ⟨hv, hx.symm, hu, hy.symm⟩
  · rintro ⟨h1, h2, h3, h4⟩
    rw [targetsOf, h1, h3, ← h4, ← h2]
    abel

/-- **Lemma 5.2.** If `wt x = wt v`, then `Π_{x,y,u,v}(1) = [x = v][y = u]`. -/
theorem piece_eval_one (V : Corner → Label) (h : labelWt (V .x) = labelWt (V .v)) :
    eval₂ (RingHom.id ℤ) 1 (piece V) = if crossing V then 1 else 0 := by
  rw [piece, transport_eq_transportG, map_transportG,
    transportG_eq_of_leading psiE (fun s => (oppC s.1, s.2))]
  · simp only [crossing_iff]
  · rintro ⟨c, i⟩ -
    cases c <;> simp [rule, oppC, eqL]
  · rintro ⟨c, i⟩ - ⟨c', j⟩ - hne hR
    cases c <;> cases c' <;>
      simp [rule, oppC, eqL, psiE, oneSubZ2, oneSubZm2, eval₂_T] at hne hR ⊢ <;> omega
  · have hx : ∀ σ, ((located Corner.x σ).map psiE).sum = -1 * (wt σ : ℤ) :=
      fun σ => sum_map_located psiE _ σ (-1) fun i => by simp [psiE]
    have hv : ∀ σ, ((located Corner.v σ).map psiE).sum = 1 * (wt σ : ℤ) :=
      fun σ => sum_map_located psiE _ σ 1 fun i => by simp [psiE]
    have hy : ∀ σ, ((located Corner.y σ).map psiE).sum = 0 * (wt σ : ℤ) :=
      fun σ => sum_map_located psiE _ σ 0 fun i => by simp [psiE]
    have hu : ∀ σ, ((located Corner.u σ).map psiE).sum = 0 * (wt σ : ℤ) :=
      fun σ => sum_map_located psiE _ σ 0 fun i => by simp [psiE]
    simp only [sourcesOf, targetsOf, Multiset.map_add, Multiset.sum_add, map_located]
    simp only [oppC, hx, hv, hy, hu]
    unfold labelWt at h
    omega

/-! ### Transposition -/

theorem swapYU_injective : Function.Injective swapYU := by
  intro a b h
  cases a <;> cases b <;> simp_all [swapYU]

theorem invert_invert (f : Lp) : invert (invert f) = f := involutive_invert f

theorem map_located_prodMap {P Q : Type} (g : P → Q) (c : P) (σ : Multiset ℕ) :
    (located c σ).map (Prod.map g id) = located (g c) σ := by
  simp [located, Multiset.map_map]

/-- **Lemma 5.3.** `Π_{x,y,u,v}(z) = Π_{x,u,y,v}(1/z)`. -/
theorem piece_transpose (V : Corner → Label) : piece (transposeView V) = invert (piece V) := by
  have hsrc : sourcesOf (transposeView V) = (sourcesOf V).map (Prod.map swapYU id) := by
    simp only [sourcesOf, transposeView, Function.comp_apply, Multiset.map_add,
      map_located_prodMap, swapYU]
    abel
  have htgt : targetsOf (transposeView V) = (targetsOf V).map (Prod.map swapYU id) := by
    simp only [targetsOf, transposeView, Function.comp_apply, Multiset.map_add,
      map_located_prodMap, swapYU]
    abel
  rw [piece, piece, transport_eq_transportG, transport_eq_transportG, hsrc, htgt,
    transportG_map swapYU swapYU_injective, map_transportG]
  congr 1
  funext p i p' j
  cases p <;> cases p' <;>
    simp [rule, swapYU, bar, oneSubZ2, oneSubZm2, eqL, apply_ite invert, invert_invert]

/-! ### The example -/

/-- **The example after Lemma 5.3**: `x` and `y` each send one request of type `0`, and `v` and
`u` each receive one; then `Π_{x,y,u,v} = 2 - z²`. -/
theorem piece_example :
    piece (views ({0}, 0) ({0}, 0) (0, {0}) (0, {0})) = 2 - T 2 := by
  have hs : sourcesOf (views ({0}, 0) ({0}, 0) (0, {0}) (0, {0})) =
      (Corner.x, 0) ::ₘ {(Corner.y, 0)} := by
    simp [sourcesOf, views, located]
  have ht : targetsOf (views ({0}, 0) ({0}, 0) (0, {0}) (0, {0})) =
      (Corner.u, 0) ::ₘ {(Corner.v, 0)} := by
    simp [targetsOf, views, located]
  have hC : Cube.C 0 0 = 1 := by
    simp [Cube.C, chi, ip]
  rw [piece, transport, hs, ht]
  simp only [srcForm, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Multiset.toFinset_cons, Multiset.toFinset_singleton]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton, Finset.sum_insert (by simp),
      Finset.sum_singleton, ← Multiset.singleton_add, Multiset.toFinsupp_add,
    Multiset.toFinsupp_singleton, Multiset.toFinsupp_singleton]
  simp only [rule, eqL, ↓reduceIte, hC, mul_one, add_mul, mul_add, AddMonoidAlgebra.coeff_add,
    Finsupp.add_apply]
  have hm : ∀ (p q : Corner × ℕ) (a b : Lp), MvPolynomial.C a * MvPolynomial.X p *
      (MvPolynomial.C b * MvPolynomial.X q) =
      MvPolynomial.monomial (Finsupp.single p 1 + Finsupp.single q 1) (a * b) := by
    intro p q a b
    simp only [MvPolynomial.C_mul_X_eq_monomial, MvPolynomial.monomial_mul_monomial]
  simp only [hm, MvPolynomial.coeff_monomial]
  have e1 : (Finsupp.single ((Corner.u, 0) : Corner × ℕ) 1 + Finsupp.single (Corner.u, 0) 1) ≠
      Finsupp.single (Corner.u, 0) 1 + Finsupp.single (Corner.v, 0) 1 := by
    intro h
    have := DFunLike.congr_fun h (Corner.v, 0)
    simp at this
  have e2 : (Finsupp.single ((Corner.v, 0) : Corner × ℕ) 1 + Finsupp.single (Corner.v, 0) 1) ≠
      Finsupp.single (Corner.u, 0) 1 + Finsupp.single (Corner.v, 0) 1 := by
    intro h
    have := DFunLike.congr_fun h (Corner.u, 0)
    simp at this
  have e3 : (Finsupp.single ((Corner.v, 0) : Corner × ℕ) 1 + Finsupp.single (Corner.u, 0) 1) =
      Finsupp.single (Corner.u, 0) 1 + Finsupp.single (Corner.v, 0) 1 := add_comm _ _
  simp only [e1, e2, e3, ↓reduceIte, oneSubZ2]
  ring

end Cslib.Complexity.NtimeDspace.Cube
