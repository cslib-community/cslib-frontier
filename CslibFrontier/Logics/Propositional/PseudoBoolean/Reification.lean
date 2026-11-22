/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.PseudoBoolean.CuttingPlanes
public import CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
-- `import all`: the acceptance lemmas unfold `stepTop` and the private helpers of `redCheckOn`.
import all CslibFrontier.Logics.Propositional.PseudoBoolean.Redundance
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith

/-!
# Reification by redundance

TODO
-/

@[expose] public section

namespace Cslib.Logic.PL

open Std.Sat (Literal)

namespace PBConstr

/-! ### Implications -/

/-- The variables of the terms of a constraint. -/
def vars (c : PBConstr) : List ℕ := c.terms.map termVar

/-- **The implication `⋀ R ⇒ c`** (§2.1 of the paper): each literal `ℓ` of `R` adds the term
`d ¬ℓ`, for the degree `d` of `c`. A false literal of `R` satisfies it on its own. -/
def impl (R : List (Literal ℕ)) (c : PBConstr) : PBConstr :=
  ⟨R.map (fun l => (c.degree, Std.Sat.Literal.negate l)) ++ c.terms, c.degree⟩

theorem holds_impl (σ : ℕ → Bool) (R : List (Literal ℕ)) (c : PBConstr) :
    (impl R c).Holds σ ↔ ((∀ l ∈ R, Literal.eval σ l = true) → c.Holds σ) := by
  unfold impl Holds
  simp only [lhs_append]
  by_cases h : ∀ l ∈ R, Literal.eval σ l = true
  · have h0 : lhs σ (R.map fun l => (c.degree, Std.Sat.Literal.negate l)) = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      obtain ⟨l, hl, rfl⟩ := List.mem_map.1 ht
      simp [termVal, h l hl]
    rw [h0, Nat.zero_add]
    exact ⟨fun h' _ => h', fun h' => h' h⟩
  · push Not at h
    obtain ⟨l, hl, hf⟩ := h
    have hle : c.degree ≤ lhs σ (R.map fun l => (c.degree, Std.Sat.Literal.negate l)) := by
      refine le_trans ?_ (List.le_sum_of_mem (List.mem_map.2
        ⟨(c.degree, Std.Sat.Literal.negate l), List.mem_map.2 ⟨l, hl, rfl⟩, rfl⟩))
      simp [termVal, hf]
    exact ⟨fun _ h' => absurd (h' l hl) hf, fun _ => le_trans hle (Nat.le_add_right _ _)⟩

/-- `z ⇒ c`. -/
theorem holds_impl_pos (σ : ℕ → Bool) (z : ℕ) (c : PBConstr) :
    (impl [(z, true)] c).Holds σ ↔ (σ z = true → c.Holds σ) := by
  simp [holds_impl]

/-- `c ⇒ z`, as `¬z ⇒ ¬c`. -/
theorem holds_impl_neg_negate (σ : ℕ → Bool) (z : ℕ) (c : PBConstr) :
    (impl [(z, false)] c.negate).Holds σ ↔ (c.Holds σ → σ z = true) := by
  rw [holds_impl, holds_negate]
  simp only [List.mem_singleton, forall_eq, Literal.eval_mk]
  cases σ z <;> simp

/-! ### Linear forms of normalized constraints -/

/-- The variables of a linear form. -/
private abbrev keys (L : List (ℕ × ℤ)) : List ℕ := L.map Prod.fst

/-- The coefficients of a linear form. -/
private noncomputable abbrev sing (L : List (ℕ × ℤ)) : ℕ →₀ ℤ :=
  (L.map fun e => Finsupp.single e.1 e.2).sum

private theorem mem_keys_insertCoeff {x v : ℕ} {a : ℤ} {L : List (ℕ × ℤ)} :
    x ∈ keys (insertCoeff v a L) ↔ x = v ∨ x ∈ keys L := by
  induction L with
  | nil => simp [insertCoeff]
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    by_cases h : u = v
    · subst h; simp only [insertCoeff, ↓reduceIte, List.map_cons, List.mem_cons]; tauto
    · simp only [insertCoeff, h, ↓reduceIte, List.map_cons, List.mem_cons] at ih ⊢
      rw [ih]; tauto

private theorem nodup_keys_insertCoeff {v : ℕ} {a : ℤ} {L : List (ℕ × ℤ)}
    (h : (keys L).Nodup) : (keys (insertCoeff v a L)).Nodup := by
  induction L with
  | nil => simp [insertCoeff]
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    simp only [List.map_cons, List.nodup_cons] at h
    by_cases huv : u = v
    · subst huv; simpa [insertCoeff] using h
    · simp only [insertCoeff, huv, ↓reduceIte, List.map_cons, List.nodup_cons]
      exact ⟨fun hm => (mem_keys_insertCoeff.1 hm).elim huv h.1, ih h.2⟩

private theorem keys_toLinear_subset {x : ℕ} {ts : List (ℕ × Literal ℕ)}
    (h : x ∈ keys (toLinear ts)) : x ∈ ts.map termVar := by
  induction ts with
  | nil => simp [toLinear] at h
  | cons t ts ih =>
    rw [show toLinear (t :: ts) = insertCoeff (termVar t) (termCoeff t) (toLinear ts) from rfl,
      mem_keys_insertCoeff] at h
    rcases h with rfl | h
    · simp
    · exact List.mem_cons_of_mem _ (ih h)

private theorem nodup_keys_toLinear (ts : List (ℕ × Literal ℕ)) : (keys (toLinear ts)).Nodup := by
  induction ts with
  | nil => simp [toLinear]
  | cons t ts ih => exact nodup_keys_insertCoeff ih

private theorem nodup_keys_subLinear {L : List (ℕ × ℤ)} (h : (keys L).Nodup) :
    ∀ L' : List (ℕ × ℤ), (keys (VeriPB.subLinear L L')).Nodup
  | [] => h
  | _ :: L' => nodup_keys_insertCoeff (nodup_keys_subLinear h L')

private theorem insertCoeff_of_not_mem {v : ℕ} {a : ℤ} {L : List (ℕ × ℤ)} (h : v ∉ keys L) :
    insertCoeff v a L = L ++ [(v, a)] := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [insertCoeff, Ne.symm h.1, ih h.2]

private theorem sing_insertCoeff (v : ℕ) (a : ℤ) (L : List (ℕ × ℤ)) :
    sing (insertCoeff v a L) = Finsupp.single v a + sing L := by
  induction L with
  | nil => simp [sing, insertCoeff]
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    by_cases h : u = v
    · subst h; simp only [sing, insertCoeff, ↓reduceIte, List.map_cons, List.sum_cons,
        Finsupp.single_add]; abel
    · simp only [sing, insertCoeff, h, ↓reduceIte, List.map_cons, List.sum_cons] at ih ⊢
      rw [ih]; abel

private theorem sing_subLinear (L : List (ℕ × ℤ)) :
    ∀ L' : List (ℕ × ℤ), sing (VeriPB.subLinear L L') = sing L - sing L'
  | [] => by simp [sing, VeriPB.subLinear]
  | e :: L' => by
    rw [show VeriPB.subLinear L (e :: L') = insertCoeff e.1 (-e.2) (VeriPB.subLinear L L') from rfl,
      sing_insertCoeff, sing_subLinear L L']
    simp only [sing, List.map_cons, List.sum_cons, Finsupp.single_neg]
    abel

private theorem sing_apply_of_not_mem {x : ℕ} {L : List (ℕ × ℤ)} (h : x ∉ keys L) :
    sing L x = 0 := by
  induction L with
  | nil => simp [sing]
  | cons e L ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have := ih h.2
    simp only [sing] at this ⊢
    simp [Ne.symm h.1, this]

private theorem sing_apply_of_mem {L : List (ℕ × ℤ)} (h : (keys L).Nodup) {e : ℕ × ℤ}
    (he : e ∈ L) : sing L e.1 = e.2 := by
  induction L with
  | nil => simp at he
  | cons f L ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.1 he with rfl | he
    · have := sing_apply_of_not_mem h.1
      simp only [sing] at this ⊢
      simp [this]
    · have hne : f.1 ≠ e.1 := fun hfe => h.1 (hfe ▸ List.mem_map_of_mem he)
      have := ih h.2 he
      simp only [sing] at this ⊢
      simp [hne, this]

/-- **Weak syntactic implication from coefficients**: `D` weakly syntactically implies `C` when
each coefficient of the linear form of `D` is at most that of `C` and the bound of `C` is at most
that of `D`. -/
theorem weakImplies_of_le {D C : PBConstr} (hcf : ∀ v, cf D.terms v ≤ cf C.terms v)
    (hb : (C.degree : ℤ) - negSum C.terms ≤ (D.degree : ℤ) - negSum D.terms) :
    VeriPB.weakImplies D C = true := by
  unfold VeriPB.weakImplies
  have hnd := nodup_keys_subLinear (nodup_keys_toLinear D.terms) (toLinear C.terms)
  have h0 : VeriPB.posMass (VeriPB.subLinear (toLinear D.terms) (toLinear C.terms)) = 0 := by
    refine List.sum_eq_zero fun x hx => ?_
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
    have := sing_apply_of_mem hnd he
    rw [sing_subLinear, sing, sing, ← cf_eq_lin, ← cf_eq_lin] at this
    have := hcf e.1
    simp only [Finsupp.coe_sub, Pi.sub_apply] at *
    omega
  simp [h0, hb]


/-- The linear form with every coefficient negated. -/
private def negE (L : List (ℕ × ℤ)) : List (ℕ × ℤ) := L.map fun e => (e.1, -e.2)

private theorem insertCoeff_negE (v : ℕ) (a : ℤ) (L : List (ℕ × ℤ)) :
    insertCoeff v (-a) (negE L) = negE (insertCoeff v a L) := by
  induction L with
  | nil => simp [insertCoeff, negE]
  | cons e L ih =>
    obtain ⟨u, b⟩ := e
    by_cases h : u = v
    · subst h; simp [insertCoeff, negE]; abel
    · simp only [negE, List.map_cons, insertCoeff, h, ↓reduceIte] at ih ⊢
      rw [ih]

private theorem toLinear_map_negate (ts : List (ℕ × Literal ℕ)) :
    toLinear (ts.map fun t => (t.1, Std.Sat.Literal.negate t.2)) = negE (toLinear ts) := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    obtain ⟨a, v, b⟩ := t
    rw [List.map_cons,
      show toLinear ((a, Std.Sat.Literal.negate (v, b)) :: _) =
        insertCoeff v (termCoeff (a, Std.Sat.Literal.negate (v, b))) (toLinear _) from rfl, ih,
      termCoeff_negate, insertCoeff_negE]
    rfl

private theorem negMass_negE (L : List (ℕ × ℤ)) : negMass (negE L) = VeriPB.posMass L := by
  simp only [negMass, negE, VeriPB.posMass, List.map_map]
  congr 1; exact List.map_congr_left fun e _ => by simp

private theorem posMass_negE (L : List (ℕ × ℤ)) : VeriPB.posMass (negE L) = negMass L := by
  simp only [negMass, negE, VeriPB.posMass, List.map_map]
  congr 1

private theorem sum_filter_reverse (g : ℤ → ℕ) (hg : g 0 = 0) (L : List (ℕ × ℤ)) :
    (((L.filter fun e => e.2 != 0).reverse).map fun e => g e.2).sum =
      (L.map fun e => g e.2).sum := by
  rw [List.map_reverse, List.sum_reverse]
  induction L with
  | nil => rfl
  | cons e L ih =>
    by_cases h : e.2 = 0
    · simp [h, hg, ih]
    · simp [h, ih]

private theorem toLinear_fromLinear {L : List (ℕ × ℤ)} (h : (keys L).Nodup) (D : ℤ) :
    toLinear (fromLinear L D).terms = (L.filter fun e => e.2 != 0).reverse := by
  simp only [fromLinear]
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨v, c⟩ := e
    simp only [List.map_cons, List.nodup_cons] at h
    have hv : v ∉ keys (L.filter fun e => e.2 != 0).reverse := by
      intro hm
      simp only [List.mem_map, List.mem_reverse, List.mem_filter] at hm
      obtain ⟨e, ⟨he, -⟩, rfl⟩ := hm
      exact h.1 (List.mem_map_of_mem he)
    rw [List.filterMap_cons]
    rcases entryTerm_cases v c with ⟨hc, he⟩ | ⟨hc, he⟩ | ⟨rfl, he⟩
    · rw [he, show toLinear ((c.toNat, v, true) :: L.filterMap entryTerm) =
        insertCoeff v (termCoeff (c.toNat, v, true)) (toLinear (L.filterMap entryTerm)) from rfl,
        ih h.2, insertCoeff_of_not_mem hv]
      simp [hc.ne', termCoeff, hc.le]
    · rw [he, show toLinear (((-c).toNat, v, false) :: L.filterMap entryTerm) =
        insertCoeff v (termCoeff ((-c).toNat, v, false)) (toLinear (L.filterMap entryTerm))
          from rfl,
        ih h.2, insertCoeff_of_not_mem hv]
      simp [hc.ne, termCoeff]; omega
    · rw [he]; simp [ih h.2]

private theorem coeffSum_fromLinear (L : List (ℕ × ℤ)) (D : ℤ) :
    coeffSum (fromLinear L D).terms = VeriPB.posMass L + negMass L := by
  simp only [fromLinear]
  induction L with
  | nil => rfl
  | cons e L ih =>
    obtain ⟨v, c⟩ := e
    simp only [VeriPB.posMass, negMass, List.map_cons, List.sum_cons] at ih ⊢
    rw [List.filterMap_cons]
    rcases entryTerm_cases v c with ⟨hc, he⟩ | ⟨hc, he⟩ | ⟨rfl, he⟩
    · rw [he, coeffSum_cons, ih]; simp only; omega
    · rw [he, coeffSum_cons, ih]; simp only; omega
    · rw [he]; simp [ih]

private theorem var_mem_of_mem_fromLinear {L : List (ℕ × ℤ)} {D : ℤ} {t : ℕ × Literal ℕ}
    (ht : t ∈ (fromLinear L D).terms) : termVar t ∈ keys L := by
  obtain ⟨e, he, het⟩ := List.mem_filterMap.1 ht
  obtain ⟨v, c⟩ := e
  rcases entryTerm_cases v c with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] at het <;> cases het <;>
    exact List.mem_map_of_mem he

/-- A term of `fromLinear L D` has a positive coefficient, and its signed coefficient is that of
its variable in `L`. -/
private theorem termCoeff_of_mem_fromLinear {L : List (ℕ × ℤ)} (h : (keys L).Nodup) {D : ℤ}
    {t : ℕ × Literal ℕ} (ht : t ∈ (fromLinear L D).terms) :
    0 < t.1 ∧ termCoeff t = sing L (termVar t) := by
  obtain ⟨e, he, het⟩ := List.mem_filterMap.1 ht
  have hs := sing_apply_of_mem h he
  obtain ⟨v, c⟩ := e
  rcases entryTerm_cases v c with ⟨hc, h'⟩ | ⟨hc, h'⟩ | ⟨-, h'⟩ <;> rw [h'] at het <;> cases het
  · simp only at hs; simp [termCoeff, hs]; omega
  · simp only at hs; simp [termCoeff, hs]; omega

/-! ### Normalization -/

theorem cf_normalize (c : PBConstr) : cf c.normalize.terms = cf c.terms := by
  rw [PBConstr.normalize, cf_fromLinear, cf_eq_lin]

theorem mem_vars_of_mem_vars_normalize {c : PBConstr} {x : ℕ} (h : x ∈ c.normalize.vars) :
    x ∈ c.vars := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.1 h
  exact keys_toLinear_subset (var_mem_of_mem_fromLinear ht)

private theorem negMass_toLinear_normalize (c : PBConstr) :
    negMass (toLinear c.normalize.terms) = negMass (toLinear c.terms) := by
  rw [normalize, toLinear_fromLinear (nodup_keys_toLinear _)]
  exact sum_filter_reverse (fun a => (-a).toNat) rfl _

private theorem posMass_toLinear_normalize (c : PBConstr) :
    VeriPB.posMass (toLinear c.normalize.terms) = VeriPB.posMass (toLinear c.terms) := by
  rw [normalize, toLinear_fromLinear (nodup_keys_toLinear _)]
  exact sum_filter_reverse (fun a => a.toNat) rfl _

private theorem negSum_normalize (c : PBConstr) :
    negSum c.normalize.terms = negMass (toLinear c.terms) := negSum_fromLinear _ _

private theorem coeffSum_normalize (c : PBConstr) :
    coeffSum c.normalize.terms = VeriPB.posMass (toLinear c.terms) + negMass (toLinear c.terms) :=
  coeffSum_fromLinear _ _

private theorem degree_normalize (c : PBConstr) :
    (c.normalize.degree : ℤ) =
      max ((c.degree : ℤ) - negSum c.terms + negMass (toLinear c.terms)) 0 := by
  simp only [normalize, fromLinear]; omega

private theorem negMass_toLinear_le (ts : List (ℕ × Literal ℕ)) :
    negMass (toLinear ts) ≤ negSum ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [show toLinear (t :: ts) = insertCoeff (termVar t) (termCoeff t) (toLinear ts) from rfl,
      negSum_cons]
    suffices ∀ (v : ℕ) (a : ℤ) (L : List (ℕ × ℤ)),
        negMass (insertCoeff v a L) ≤ negMass L + (-a).toNat by
      refine (this _ _ _).trans ?_
      obtain ⟨a, v, b⟩ := t
      cases b <;> simp [termCoeff] <;> omega
    intro v a L
    induction L with
    | nil => simp [insertCoeff, negMass]
    | cons e L ihL =>
      obtain ⟨u, b⟩ := e
      by_cases h : u = v
      · subst h; simp [insertCoeff, negMass]; omega
      · simp only [insertCoeff, h, ↓reduceIte, negMass, List.map_cons, List.sum_cons] at ihL ⊢
        omega

/-- A constraint of degree `0` normalizes to degree `0`. -/
theorem normalize_degree_of_degree_zero (ts : List (ℕ × Literal ℕ)) :
    (⟨ts, 0⟩ : PBConstr).normalize.degree = 0 := by
  have := negMass_toLinear_le ts
  simp only [normalize, fromLinear]; omega

/-! ### Linear forms of implications and substitutions -/

private theorem cf_apply_of_not_mem {ts : List (ℕ × Literal ℕ)} {z : ℕ}
    (h : z ∉ ts.map termVar) : cf ts z = 0 := by
  rw [cf_eq_lin]
  exact sing_apply_of_not_mem fun hm => h (keys_toLinear_subset hm)

private theorem negMass_append_single (L : List (ℕ × ℤ)) (v : ℕ) (a : ℤ) :
    negMass (L ++ [(v, a)]) = negMass L + (-a).toNat := by
  simp [negMass]

private theorem posMass_append_single (L : List (ℕ × ℤ)) (v : ℕ) (a : ℤ) :
    VeriPB.posMass (L ++ [(v, a)]) = VeriPB.posMass L + a.toNat := by
  simp [VeriPB.posMass]

private theorem toLinear_impl_single {l : Literal ℕ} {c : PBConstr} (h : l.1 ∉ c.vars) :
    toLinear (impl [l] c).terms =
      toLinear c.terms ++ [(l.1, termCoeff (c.degree, Std.Sat.Literal.negate l))] := by
  rw [show (impl [l] c).terms = (c.degree, Std.Sat.Literal.negate l) :: c.terms from rfl,
    show toLinear ((c.degree, Std.Sat.Literal.negate l) :: c.terms) =
      insertCoeff (termVar (c.degree, Std.Sat.Literal.negate l))
        (termCoeff (c.degree, Std.Sat.Literal.negate l)) (toLinear c.terms) from rfl]
  obtain ⟨v, b⟩ := l
  exact insertCoeff_of_not_mem fun hm => h (keys_toLinear_subset hm)

private theorem vars_negate (c : PBConstr) : c.negate.vars = c.normalize.vars := by
  simp only [vars, negate, List.map_map]
  exact List.map_congr_left fun t _ => rfl

/-- The part of a constraint on the variable `z`, all of whose literals are negative. -/
private theorem zpart {z : ℕ} :
    ∀ ts : List (ℕ × Literal ℕ), (∀ t ∈ ts, termVar t = z → termPos t = false) →
      (negSum (ts.filter (termVar · == z)) : ℤ) = -(cf ts z) ∧
        cf (ts.filter (termVar · == z)) = Finsupp.single z (cf ts z)
  | [], _ => by simp
  | t :: ts, h => by
    obtain ⟨ih₁, ih₂⟩ := zpart ts fun u hu => h u (List.mem_cons_of_mem _ hu)
    by_cases ht : termVar t = z
    · have hp := h t List.mem_cons_self ht
      simp only [List.filter_cons, ht, beq_self_eq_true, ↓reduceIte, negSum_cons, hp,
        Bool.false_eq_true, cf_cons, Finsupp.add_apply, Finsupp.single_eq_same, ih₂]
      refine ⟨?_, by rw [Finsupp.single_add]⟩
      push_cast [ih₁]
      simp [termCoeff, hp]; ring
    · have hz : (Finsupp.single (termVar t) (termCoeff t)) z = 0 :=
        Finsupp.single_eq_of_ne (Ne.symm ht)
      simp only [List.filter_cons, beq_iff_eq, ht, ↓reduceIte, cf_cons, Finsupp.add_apply, hz,
        zero_add]
      exact ⟨ih₁, ih₂⟩

private theorem find_single (z : ℕ) (w : VeriPB.WVal) (v : ℕ) :
    VeriPB.Witness.find [(z, w)] v = if v = z then some w else none := by
  by_cases h : v = z
  · subst h; simp [VeriPB.Witness.find]
  · have hb : (z == v) = false := by simp [Ne.symm h]
    simp [VeriPB.Witness.find, List.find?, hb, h]

/-- A witness on one variable leaves the terms on other variables alone. -/
private theorem substTerms_of_not_mem {z : ℕ} {w : VeriPB.WVal} :
    ∀ ts : List (ℕ × Literal ℕ), z ∉ ts.map termVar →
      ts.flatMap (fun t => (VeriPB.Witness.substTerm [(z, w)] t).1) = ts ∧
        (ts.map fun t => (VeriPB.Witness.substTerm [(z, w)] t).2).sum = 0
  | [], _ => by simp
  | t :: ts, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨ih₁, ih₂⟩ := substTerms_of_not_mem (w := w) ts h.2
    have : VeriPB.Witness.substTerm [(z, w)] t = ([t], 0) := by
      simp [VeriPB.Witness.substTerm, find_single, Ne.symm h.1]
    simp [this, ih₁, ih₂]

private theorem substC_of_not_mem {z : ℕ} {w : VeriPB.WVal} {c : PBConstr} (h : z ∉ c.vars) :
    VeriPB.Witness.substC [(z, w)] c = c := by
  obtain ⟨h₁, h₂⟩ := substTerms_of_not_mem (w := w) c.terms h
  simp [VeriPB.Witness.substC, h₁, h₂]

/-- `z ↦ 1` on a constraint whose terms on `z` are negative drops those terms. -/
private theorem substC_one {z : ℕ} {c : PBConstr}
    (h : ∀ t ∈ c.terms, termVar t = z → termPos t = false) :
    VeriPB.Witness.substC [(z, .one)] c = ⟨c.terms.filter (termVar · != z), c.degree⟩ := by
  suffices ∀ ts : List (ℕ × Literal ℕ), (∀ t ∈ ts, termVar t = z → termPos t = false) →
      ts.flatMap (fun t => (VeriPB.Witness.substTerm [(z, .one)] t).1) =
        ts.filter (termVar · != z) ∧
        (ts.map fun t => (VeriPB.Witness.substTerm [(z, .one)] t).2).sum = 0 by
    obtain ⟨h₁, h₂⟩ := this c.terms h
    simp [VeriPB.Witness.substC, h₁, h₂]
  intro ts hts
  induction ts with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨ih₁, ih₂⟩ := ih fun u hu => hts u (List.mem_cons_of_mem _ hu)
    by_cases ht : termVar t = z
    · have hp := hts t List.mem_cons_self ht
      have : VeriPB.Witness.substTerm [(z, .one)] t = ([], 0) := by
        simp [VeriPB.Witness.substTerm, find_single, ht, hp]
      simp [this, ih₁, ih₂, ht]
    · have : VeriPB.Witness.substTerm [(z, .one)] t = ([t], 0) := by
        simp [VeriPB.Witness.substTerm, find_single, ht]
      simp [this, ih₁, ih₂, ht]

/-- **The reverse reification is autoproven against the forward one**: `¬(c ⇒ z)` weakly
syntactically implies `(z ⇒ c)|_{z ↦ 1}`, for `z` not in `c` and `c` not a contradiction after
normalization. Both have the linear form of `c`, and the first adds `-K z`. -/
theorem weakImplies_reify {z : ℕ} {c : PBConstr} (hz : z ∉ c.vars)
    (hnc : ¬ c.normalize.IsContradiction) :
    VeriPB.weakImplies (impl [(z, false)] c.negate).negate
      (VeriPB.Witness.substC [(z, .one)] (impl [(z, true)] c).normalize) = true := by
  set γ := cf c.terms with hγ
  set nm := negMass (toLinear c.terms) with hnm
  set pm := VeriPB.posMass (toLinear c.terms) with hpm
  have hγz : γ z = 0 := cf_apply_of_not_mem hz
  -- `N`, the normal form of `c`.
  have hNd := degree_normalize c
  have hNc := coeffSum_normalize c
  have hNs := negSum_normalize c
  unfold IsContradiction at hnc
  -- `Q = ¬c`.
  set Q := c.negate with hQ
  have hQt : Q.terms = c.normalize.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2) := rfl
  have hQd : Q.degree = coeffSum c.normalize.terms + 1 - c.normalize.degree := rfl
  have hQs : negSum Q.terms = pm := by
    have := negSum_add_negSum_negate c.normalize.terms
    rw [← hQt] at this; omega
  have hQl : toLinear Q.terms = negE (toLinear c.normalize.terms) := by
    rw [hQt, toLinear_map_negate]
  have hQcf : cf Q.terms = -γ := by rw [hQt, cf_map_negate, cf_normalize]
  have hzQ : z ∉ Q.vars := fun hm =>
    hz (mem_vars_of_mem_vars_normalize (by rwa [hQ, vars_negate] at hm))
  -- `Y = (c ⇒ z)`, and its normal form.
  set Y := impl [(z, false)] Q with hY
  have hYl : toLinear Y.terms = toLinear Q.terms ++ [(z, (Q.degree : ℤ))] := by
    rw [hY, toLinear_impl_single hzQ]; rfl
  have hYnm : negMass (toLinear Y.terms) = pm := by
    rw [hYl, negMass_append_single, hQl, negMass_negE, posMass_toLinear_normalize]; simp [hpm]
  have hYpm : VeriPB.posMass (toLinear Y.terms) = nm + Q.degree := by
    rw [hYl, posMass_append_single, hQl, posMass_negE, negMass_toLinear_normalize]; simp [hnm]
  have hYs : negSum Y.terms = pm := by
    rw [show Y.terms = (Q.degree, (z, true)) :: Q.terms from rfl, negSum_cons]; simp [hQs]
  have hYcf : cf Y.terms = Finsupp.single z (Q.degree : ℤ) - γ := by
    rw [show Y.terms = (Q.degree, (z, true)) :: Q.terms from rfl, cf_cons, hQcf]
    simp [termCoeff, sub_eq_add_neg]
  have hYd : Y.degree = Q.degree := rfl
  have hNYd := degree_normalize Y
  have hNYc := coeffSum_normalize Y
  have hNYs := negSum_normalize Y
  -- `¬(c ⇒ z)`.
  set M := Y.negate with hM
  have hMd : M.degree = coeffSum Y.normalize.terms + 1 - Y.normalize.degree := rfl
  have hMs : negSum M.terms = coeffSum Y.normalize.terms - negSum Y.normalize.terms := by
    have := negSum_add_negSum_negate Y.normalize.terms
    rw [show M.terms = Y.normalize.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2) from rfl]
    omega
  have hMcf : cf M.terms = γ - Finsupp.single z (Q.degree : ℤ) := by
    rw [show M.terms = Y.normalize.terms.map fun t => (t.1, Std.Sat.Literal.negate t.2) from rfl,
      cf_map_negate, cf_normalize, hYcf]
    abel
  -- `D`, the normal form of `z ⇒ c`, and `G = D|_{z ↦ 1}`.
  set X := impl [(z, true)] c with hX
  have hXl : toLinear X.terms = toLinear c.terms ++ [(z, -(c.degree : ℤ))] := by
    rw [hX, toLinear_impl_single hz]; rfl
  have hXnm : negMass (toLinear X.terms) = nm + c.degree := by
    rw [hXl, negMass_append_single]; simp [nm]
  have hXs : negSum X.terms = c.degree + negSum c.terms := by
    rw [show X.terms = (c.degree, (z, false)) :: c.terms from rfl, negSum_cons]; simp
  have hXcf : cf X.terms = Finsupp.single z (-(c.degree : ℤ)) + γ := by
    rw [show X.terms = (c.degree, (z, false)) :: c.terms from rfl, cf_cons]; simp [termCoeff, hγ]
  have hDd := degree_normalize X
  have hDs := negSum_normalize X
  have hneg : ∀ t ∈ X.normalize.terms, termVar t = z → termPos t = false := by
    intro t ht htz
    obtain ⟨hpos, hcoef⟩ := termCoeff_of_mem_fromLinear (nodup_keys_toLinear X.terms) ht
    rw [htz, sing, ← cf_eq_lin, hXcf] at hcoef
    simp only [Finsupp.add_apply, Finsupp.single_eq_same, hγz, add_zero] at hcoef
    by_contra hp
    simp only [Bool.not_eq_false] at hp
    simp only [termCoeff, hp, ↓reduceIte] at hcoef
    omega
  obtain ⟨hzs, hzc⟩ := zpart X.normalize.terms hneg
  have hfc := cf_filter_add (fun t => termVar t != z) X.normalize.terms
  have hfs := negSum_filter_add (fun t => termVar t != z) X.normalize.terms
  rw [VeriPB.filter_not_bne] at hfc hfs
  rw [cf_normalize, hXcf] at hzc hfc
  rw [cf_normalize, hXcf] at hzs
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, hγz, add_zero] at hzc hzs
  rw [substC_one hneg]
  have hG : cf (X.normalize.terms.filter (termVar · != z)) = γ := by
    rw [hzc, add_comm] at hfc; exact add_left_cancel hfc
  have hXd : X.degree = c.degree := rfl
  refine weakImplies_of_le (fun v => ?_) ?_
  · rw [hMcf, hG, Finsupp.sub_apply, Finsupp.single_apply]
    split_ifs <;> omega
  · simp only at hfs ⊢
    rw [hMd, hMs]
    have : (negSum X.normalize.terms : ℤ) = negSum (X.normalize.terms.filter (termVar · != z)) +
      negSum (X.normalize.terms.filter (termVar · == z)) := by exact_mod_cast hfs.symm
    rw [hNYc, hNYs, hYnm, hYpm]
    rw [hYnm, hYs, hYd] at hNYd
    rw [hXnm, hXs, hXd] at hDd
    rw [hXnm] at hDs
    rw [hNc] at hnc hQd
    omega

private theorem negMass_toLinear_eq_zero {ts : List (ℕ × Literal ℕ)} (h : ∀ v, 0 ≤ cf ts v) :
    negMass (toLinear ts) = 0 := by
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨e, he, rfl⟩ := List.mem_map.1 hx
  have := sing_apply_of_mem (nodup_keys_toLinear ts) he
  rw [sing, ← cf_eq_lin] at this
  have := h e.1
  omega

private theorem substLin_of_not_mem {z : ℕ} {w : VeriPB.WVal} :
    ∀ L : List (ℕ × ℤ), z ∉ keys L → VeriPB.Witness.substLin [(z, w)] L = (L, 0)
  | [], _ => rfl
  | e :: L, h => by
    simp only [List.map_cons, List.mem_cons, not_or] at h
    have ih := substLin_of_not_mem (w := w) L h.2
    simp only [VeriPB.Witness.substLin, Prod.mk.injEq] at ih ⊢
    have : VeriPB.Witness.substEntry [(z, w)] e = ([e], 0) := by
      simp [VeriPB.Witness.substEntry, find_single, Ne.symm h.1]
    simp [this, ih.1, ih.2]

/-- The objective goal of a witness on a variable outside the objective is trivially true. -/
theorem objGoal_normalize_degree {z : ℕ} {w : VeriPB.WVal} {f : VeriPB.Objective}
    (h : z ∉ f.lin.map (·.1)) : (VeriPB.objGoal f [(z, w)]).normalize.degree = 0 := by
  have h0 : negMass (toLinear (VeriPB.objGoal f [(z, w)]).terms) = 0 := by
    refine negMass_toLinear_eq_zero fun v => ?_
    rw [VeriPB.objGoal, substLin_of_not_mem _ h, cf_fromLinear]
    have := sing_subLinear f.lin f.lin
    simp only [sing, sub_self] at this
    simp [this]
  have hs := negSum_fromLinear (VeriPB.subLinear f.lin (VeriPB.Witness.substLin [(z, w)] f.lin).1)
    (VeriPB.Witness.substLin [(z, w)] f.lin).2
  rw [← VeriPB.objGoal] at hs
  have hd : ((VeriPB.objGoal f [(z, w)]).degree : ℤ) =
      max ((VeriPB.Witness.substLin [(z, w)] f.lin).2 +
        negMass (VeriPB.subLinear f.lin (VeriPB.Witness.substLin [(z, w)] f.lin).1)) 0 := by
    simp only [VeriPB.objGoal, fromLinear]; omega
  rw [substLin_of_not_mem _ h] at hd hs
  simp only [normalize, fromLinear, h0]
  omega

/-- `(z ⇒ c)|_{z ↦ 0}` is trivially true. -/
theorem substC_zero_impl_pos {z : ℕ} {c : PBConstr} (h : z ∉ c.vars) :
    (VeriPB.Witness.substC [(z, .zero)] (impl [(z, true)] c)).normalize.degree = 0 := by
  obtain ⟨h₁, h₂⟩ := substTerms_of_not_mem (w := .zero) c.terms h
  have hd : VeriPB.Witness.substTerm [(z, .zero)] (c.degree, Std.Sat.Literal.negate (z, true)) =
      ([], c.degree) := by
    simp [VeriPB.Witness.substTerm, find_single, Std.Sat.Literal.negate]
  have : VeriPB.Witness.substC [(z, .zero)] (impl [(z, true)] c) = ⟨c.terms, 0⟩ := by
    simp only [VeriPB.Witness.substC, impl, List.map_cons, List.map_nil, List.singleton_append,
      List.flatMap_cons, List.sum_cons, hd, h₁, h₂, List.nil_append, add_zero, Nat.sub_self]
  rw [this]; exact normalize_degree_of_degree_zero _

/-- `(c ⇒ z)|_{z ↦ 1}` is trivially true. -/
theorem substC_one_impl_neg {z : ℕ} {c : PBConstr} (h : z ∉ c.vars) :
    (VeriPB.Witness.substC [(z, .one)] (impl [(z, false)] c)).normalize.degree = 0 := by
  obtain ⟨h₁, h₂⟩ := substTerms_of_not_mem (w := .one) c.terms h
  have hd : VeriPB.Witness.substTerm [(z, .one)] (c.degree, Std.Sat.Literal.negate (z, false)) =
      ([], c.degree) := by
    simp [VeriPB.Witness.substTerm, find_single, Std.Sat.Literal.negate]
  have : VeriPB.Witness.substC [(z, .one)] (impl [(z, false)] c) = ⟨c.terms, 0⟩ := by
    simp only [VeriPB.Witness.substC, impl, List.map_cons, List.map_nil, List.singleton_append,
      List.flatMap_cons, List.sum_cons, hd, h₁, h₂, List.nil_append, add_zero, Nat.sub_self]
  rw [this]; exact normalize_degree_of_degree_zero _

theorem touchedTrue_of_not_mem {z : ℕ} {w : VeriPB.WVal} {c : PBConstr} (h : z ∉ c.vars) :
    VeriPB.Witness.touchedTrue [(z, w)] c = true := by
  simp only [VeriPB.Witness.touchedTrue, List.all_eq_true]
  intro t ht
  have : termVar t ≠ z := fun he => h (he ▸ List.mem_map_of_mem ht)
  simp [find_single, this]

theorem not_mem_vars_negate {z : ℕ} {c : PBConstr} (h : z ∉ c.vars) : z ∉ c.negate.vars :=
  fun hm => h (mem_vars_of_mem_vars_normalize (by rwa [vars_negate] at hm))

end PBConstr

namespace VeriPB

open PBConstr

/-! ### Accepted `red` steps -/

/-- **An autoproven `red` step is accepted**: `red C : ω` without a subproof, whose goals are all
covered without one, adds `C` at the next number. The witness leaves the preserved set and the
loaded order alone; the goal `C|ω` and the objective goal are trivially true after normalization;
and for each constraint `D` of the goal set (the database, or the core set in
strengthening-to-core mode), `ω` sets every literal of `D` it touches true or `¬C` weakly
syntactically implies `D|ω`. -/
theorem stepTop_red_of_covered {F : List PBConstr} {obj : Option Objective} {s : State}
    {c : PBConstr} {ω : Witness} (hp : presFree s.pres ω = true)
    (hord : ∀ L, s.order = some L → L.untouched ω = true)
    (h1 : (Witness.substC ω c).normalize.degree = 0)
    (hobj : ∀ f, s.obj = some f → (objGoal f ω).normalize.degree = 0)
    (hgs : ∀ e ∈ (if s.tcb then s.core else s.db),
      Witness.touchedTrue ω e.2 = true ∨ weakImplies c.negate (Witness.substC ω e.2) = true) :
    stepTop F obj s (.red c ω none none) = some (s.addStrengthened s.next c) := by
  have hok : redOk s.obj s.order s.db (if s.tcb then s.core else s.db) ω c false
      ((s.next, c.negate) :: s.db) [] none = true := by
    simp only [redOk, visible, List.filter_nil, List.map_nil, Bool.false_or, Bool.and_eq_true]
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · cases ho : s.order with
      | none => rfl
      | some L => simp [hord L ho]
    · simp [goalCovered, objuCovered, h1]
    · cases ho : s.order with
      | none => rfl
      | some L => simp [hord L ho]
    · simp only [substCovered, Bool.and_eq_true, List.all_eq_true]
      refine ⟨?_, fun e he => ?_⟩
      · cases hf : s.obj with
        | none => rfl
        | some f => simp [goalCovered, objuCovered, hobj f hf]
      · rcases hgs e he with h | h <;> simp [goalCovered, h]
  simp [stepTop, redCheckP, hp, redCheckOn, runGoals, hok]


/-! ### Reification -/

/-- `z` is not a variable of the objective, the preserved set or the loaded order of `s`. -/
def State.avoidsVar (s : State) (z : ℕ) : Bool :=
  s.obj.all (fun f => !(f.lin.map (·.1)).contains z) && s.pres.all (fun P => !P.contains z) &&
    s.order.all (fun L => !(L.lits.map (·.1)).contains z)

/-- `z` is **fresh** in `s`: it occurs in no constraint of the database or the core set, and
`s.avoidsVar z`. -/
def State.fresh (s : State) (z : ℕ) : Bool :=
  (s.db ++ s.core).all (fun e => !e.2.vars.contains z) && s.avoidsVar z

/-- `red z ⇒ C : z ↦ 0`: introduce half of the reification of `C` by `z`. -/
def reifyFwd (z : ℕ) (c : PBConstr) : TopStep := .red (impl [(z, true)] c) [(z, .zero)] none none

/-- `red C ⇒ z : z ↦ 1`, with `C ⇒ z` written `¬z ⇒ ¬C`: the other half. -/
def reifyBwd (z : ℕ) (c : PBConstr) : TopStep :=
  .red (impl [(z, false)] c.negate) [(z, .one)] none none

/-- **The reification `z ⇔ C`** (§2.2 of the paper): `z ⇒ C`, then `C ⇒ z`. -/
def reify (z : ℕ) (c : PBConstr) : List TopStep := [reifyFwd z c, reifyBwd z c]

private theorem avoidsVar_parts {s : State} {z : ℕ} {w : WVal} (h : s.avoidsVar z = true) :
    presFree s.pres [(z, w)] = true ∧ (∀ L, s.order = some L → L.untouched [(z, w)] = true) ∧
      ∀ f, s.obj = some f → (objGoal f [(z, w)]).normalize.degree = 0 := by
  simp only [State.avoidsVar, Bool.and_eq_true] at h
  obtain ⟨⟨ho, hp⟩, hl⟩ := h
  refine ⟨?_, fun L hL => ?_, fun f hf => ?_⟩
  · cases hP : s.pres with
    | none => rfl
    | some P =>
      simp only [hP, Option.all_some, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
        List.contains_iff_mem] at hp
      simp [presFree, hp]
  · simp only [hL, Option.all_some, Bool.not_eq_true'] at hl
    simp only [LoadedOrder.untouched, List.all_eq_true, Option.isNone_iff_eq_none]
    intro l hl'
    have : l.1 ≠ z := fun he => by
      simp only [Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at hl
      exact hl (he ▸ List.mem_map_of_mem hl')
    simp [find_single, this]
  · simp only [hf, Option.all_some, Bool.not_eq_true', Bool.eq_false_iff, ne_eq,
      List.contains_iff_mem] at ho
    exact objGoal_normalize_degree ho

/-- **`z ⇒ C` is accepted** for a fresh `z` not in `C`: the step adds it at the next number. -/
theorem stepTop_reifyFwd {F : List PBConstr} {obj : Option Objective} {s : State} {z : ℕ}
    {c : PBConstr} (hs : s.fresh z = true) (hc : z ∉ c.vars) :
    stepTop F obj s (reifyFwd z c) = some (s.addStrengthened s.next (impl [(z, true)] c)) := by
  simp only [State.fresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at hs
  obtain ⟨hdb, hv⟩ := hs
  obtain ⟨hp, hord, hobj⟩ := avoidsVar_parts (w := .zero) hv
  refine stepTop_red_of_covered hp hord (substC_zero_impl_pos hc) hobj fun e he => ?_
  refine Or.inl (touchedTrue_of_not_mem (hdb e ?_))
  split at he <;> simp [he]

/-- **`C ⇒ z` is accepted** once `z ⇒ C` is the only constraint mentioning `z`, for `C` not a
contradiction after normalization. -/
theorem stepTop_reifyBwd {F : List PBConstr} {obj : Option Objective} {s : State} {z : ℕ}
    {c : PBConstr} (hs : s.avoidsVar z = true) (hc : z ∉ c.vars)
    (hnc : ¬ c.normalize.IsContradiction)
    (hdb : ∀ e ∈ s.db ++ s.core, z ∈ e.2.vars → e.2 = (impl [(z, true)] c).normalize) :
    stepTop F obj s (reifyBwd z c) =
      some (s.addStrengthened s.next (impl [(z, false)] c.negate)) := by
  obtain ⟨hp, hord, hobj⟩ := avoidsVar_parts (w := .one) hs
  refine stepTop_red_of_covered hp hord (substC_one_impl_neg (not_mem_vars_negate hc)) hobj
    fun e he => ?_
  have he' : e ∈ s.db ++ s.core := by split at he <;> simp [he]
  by_cases hz : z ∈ e.2.vars
  · rw [hdb e he' hz]; exact Or.inr (weakImplies_reify hc hnc)
  · exact Or.inl (touchedTrue_of_not_mem hz)

/-- **The reification `z ⇔ C` is accepted** for a fresh `z` not in `C`, and `C` not a
contradiction after normalization: `z ⇒ C` takes the next number and `C ⇒ z` the one after. -/
theorem runTop_reify {F : List PBConstr} {obj : Option Objective} {s : State} {z : ℕ}
    {c : PBConstr} (hs : s.fresh z = true) (hc : z ∉ c.vars)
    (hnc : ¬ c.normalize.IsContradiction) :
    runTop F obj s (reify z c) =
      some ((s.addStrengthened s.next (impl [(z, true)] c)).addStrengthened (s.next + 1)
        (impl [(z, false)] c.negate)) := by
  have hs' := hs
  simp only [State.fresh, Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
    Bool.eq_false_iff, ne_eq, List.contains_iff_mem] at hs'
  obtain ⟨hdb, hv⟩ := hs'
  simp only [reify, runTop, stepTop_reifyFwd hs hc]
  rw [stepTop_reifyBwd (s := s.addStrengthened s.next (impl [(z, true)] c)) hv hc hnc]
  · rfl
  · intro e he hz
    simp only [State.addStrengthened, List.mem_append, List.mem_cons] at he
    rcases he with (rfl | he) | he
    · rfl
    · exact absurd hz (hdb e (List.mem_append_left _ he))
    · split at he
      · rcases List.mem_cons.1 he with rfl | he
        · rfl
        · exact absurd hz (hdb e (List.mem_append_right _ he))
      · exact absurd hz (hdb e (List.mem_append_right _ he))

end VeriPB

end Cslib.Logic.PL

end
