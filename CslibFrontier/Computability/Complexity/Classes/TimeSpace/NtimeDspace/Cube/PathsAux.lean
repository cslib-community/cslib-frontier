/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Formula
public import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Star.Real

/-!
# The budget of the formula (proof of Lemma 6.3)

A budget `Setup.bud π` paying for every node of the formula (`Setup.budgeted`), on the states of an
invariant `Setup.inv π` closed under children:

* `Setup.ChainOK`: a path of valid choice codes. Along it the clique at name length `2^(e-n)` has
  `q = 2^(2^(e-n))` nodes and potential at most `Φ₀ / 2^n` (`chainOK_facts`, by
  `two_mul_potential_childAt`
  from Lemma 6.1 and the orientation of smaller potential), so every budget sum is at most `Φ₀/2^e`
  (`spair_mul_le`).
* The descent (`BudPar.desc`): one choice code of `choiceWidth g fw` bits per merge, then the code
of
  the last label (`Λ`).
* The ascent (`BudPar.asc`): at an entry from a parent of name length `h`, the copies take at most
  `Ξ / h` bits (`xiWidth_le`, Cauchy–Schwarz in `copiesWidth_sq`), plus the balanced products.
* The transport recursion (`trB`): a pivot index and three products per level, the weight halving
  (`pivot_halves`); `trB_le_real` bounds it by `336 √W + O(log² W + ℓ log W)`.
* `part_desc`, `part_sqrt`, `part_prod`, `part_tr`: the arithmetic of the five parts of the budget.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

theorem Clique.recast_potential (C : Clique) (n : ℕ) (h : C.q = n) :
    (C.recast n h).potential = C.potential := by
  subst h; rfl

theorem two_mul_potential_mergeStep {g : ℕ} (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) {ι : Rect g → ℤ × ℤ} (hι : ι ∈ choices a) :
    2 * (mergeStep g a T ι).potential ≤ (g * g - 1) ^ 2 * ∑ p : Pairs (g * g), a p.1.1 p.1.2 := by
  have hk : ∀ r, Even (ι r).1 ∧ |(ι r).1| ≤ 2 * diagWt a r := by
    intro r
    have hr := Fintype.mem_piFinset.mp hι r
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hr
    exact ⟨hr.1.2, abs_le.mpr ⟨by linarith [hr.1.1.1], hr.1.1.2⟩⟩
  have hE := energy_le a (fun r => (ι r).1) hk
  have hrow : (rowChild g a T ι).potential =
      (g - 1) ^ 2 * ∑ p : Pairs g, rowBudget a (fun r => (ι r).1) p.1.1 p.1.2 := rfl
  have hcol : (colChild g a T ι).potential =
      (g - 1) ^ 2 * ∑ p : Pairs g, colBudget a (fun r => (ι r).1) p.1.1 p.1.2 := by
    change (g - 1) ^ 2 * ∑ p : Pairs g, (colChild g a T ι).a p.1.1 p.1.2 = _
    congr 1
    exact Finset.sum_congr rfl fun p _ => colChild_a a T ι (fun r => (hk r).1) p.2.le
  set R := ∑ p : Pairs g, rowBudget a (fun r => (ι r).1) p.1.1 p.1.2
  set Cc := ∑ p : Pairs g, colBudget a (fun r => (ι r).1) p.1.1 p.1.2
  unfold mergeStep orientRow
  split_ifs with h
  · simp only [decide_eq_true_eq] at h
    rw [hrow]
    calc 2 * ((g - 1) ^ 2 * R) = (g - 1) ^ 2 * (R + R) := by ring
      _ ≤ (g - 1) ^ 2 * (R + Cc) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := hE
  · simp only [decide_eq_true_eq] at h
    rw [hcol]
    calc 2 * ((g - 1) ^ 2 * Cc) = (g - 1) ^ 2 * (Cc + Cc) := by ring
      _ ≤ (g - 1) ^ 2 * (R + Cc) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ _ := hE

theorem dite_pos' {c : Prop} [Decidable c] (h : c) {α : Sort*} (t : c → α) (e : ¬c → α) :
    dite c t e = t h := by simp [h]

theorem dite_neg' {c : Prop} [Decidable c] (h : ¬c) {α : Sort*} (t : c → α) (e : ¬c → α) :
    dite c t e = e h := by simp [h]

theorem childAt_eq (fw : ℕ) (C : Clique) (i : ℕ) (h : C.q = Nat.sqrt C.q * Nat.sqrt C.q) :
    childAt fw C i = mergeStep (Nat.sqrt C.q) (C.recast _ h).a (C.recast _ h).T
      (decodeChoice (Nat.sqrt C.q) fw i) := by
  simp only [childAt]; rw [dite_pos' h]

theorem childAt_q (fw : ℕ) (C : Clique) (i : ℕ) (h : C.q = Nat.sqrt C.q * Nat.sqrt C.q) :
    (childAt fw C i).q = Nat.sqrt C.q := by
  rw [childAt_eq fw C i h]; unfold mergeStep; split <;> rfl

theorem two_mul_potential_childAt (fw : ℕ) (C : Clique) (i : ℕ)
    (h : C.q = Nat.sqrt C.q * Nat.sqrt C.q)
    (hv : ValidChoiceCode (C.recast _ h).a fw i) : 2 * (childAt fw C i).potential ≤
        C.potential := by
  rw [childAt_eq fw C i h, ← Clique.recast_potential C _ h]
  exact two_mul_potential_mergeStep _ _ hv.1

/-- The sum of the budgets of a clique. -/
def Clique.spair (C : Clique) : ℕ := ∑ p : Pairs C.q, C.a p.1.1 p.1.2

theorem Clique.potential_eq (C : Clique) : C.potential = (C.q - 1) ^ 2 * C.spair := rfl

theorem Clique.a_le_spair (C : Clique) {u v : Fin C.q} (h : u < v) : C.a u v ≤ C.spair :=
  Finset.single_le_sum (f := fun p : Pairs C.q => C.a p.1.1 p.1.2) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ ⟨(u, v), h⟩)

theorem Clique.budget_le_spair (C : Clique) {u v : Fin C.q} (h : u ≠ v) :
    budget C.a u v ≤ C.spair := by
  rcases lt_or_gt_of_ne h with h | h
  · rw [MergeProof.budget_of_lt _ h]; exact C.a_le_spair h
  · rw [MergeProof.budget_comm, MergeProof.budget_of_lt _ h]; exact C.a_le_spair h

theorem decodeLabel_wt {a i : ℕ} {l : Label} (h : decodeLabel a i = some l) : labelWt l ≤ a := by
  unfold decodeLabel at h
  split_ifs at h with ha hi
  · simp only [Option.some.injEq] at h; subst h; simp [labelWt, wt]
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split_ifs at h with hc
        simp only [Option.some.injEq] at h; subst h; exact hc.2

theorem labelWt_zero : labelWt ((0 : Multiset ℕ), (0 : Multiset ℕ)) = 0 := by
  simp [labelWt, wt]

theorem labelWt_decodeArgs (C : Clique) (v : Fin C.q) (args : ℕ) (u : Fin C.q) :
    labelWt (decodeArgs C v args u) ≤ C.spair := by
  unfold decodeArgs
  split_ifs with h
  · simp [labelWt_zero]
  · dsimp only
    split
    · next l hl => exact (decodeLabel_wt hl).trans (C.budget_le_spair fun e => h e.symm)
    · simp [labelWt_zero]

theorem labelWt_copyAt (C : Clique) (nodes : ℕ → ℕ) (ξ p u : ℕ) :
    labelWt (copyAt C nodes ξ p u) ≤ C.spair := by
  unfold copyAt
  split_ifs
  · exact labelWt_decodeArgs ..
  · simp [labelWt_zero]

theorem tWt_srcList (up : Bool) (x y m : Label) :
    tWt (srcList up x y m) (tgtMs up x y m) = labelWt x + labelWt y + labelWt m := by
  have hl : ∀ (p : HPlace) (σ : Multiset ℕ),
      (((σ.sort (· ≤ ·)).map fun i => (p, i)).map lwt).sum = wt σ := by
    intro p σ
    rw [List.map_map]
    conv_rhs => rw [← Multiset.sort_eq σ (· ≤ ·)]
    rw [wt, Multiset.map_coe, Multiset.sum_coe]
    rfl
  have hm : ∀ (p : HPlace) (σ : Multiset ℕ), ((located p σ).map lwt).sum = wt σ := by
    intro p σ
    unfold located
    rw [Multiset.map_map]
    rfl
  cases up <;>
    simp only [tWt, srcList, tgtMs, List.map_append, List.sum_append, Multiset.map_add,
      Multiset.sum_add, hl, hm, labelWt, Bool.false_eq_true, ↓reduceIte] <;> omega


/-! ### The chain -/

namespace Setup

variable (S : Setup)

/-- The path `chs` of choice codes is a path of valid codes through cliques of name length at least
`2`, at most `e` of them. -/
def ChainOK (e : ℕ) : List ℕ → Prop
  | [] => True
  | i :: rest => ChainOK e rest ∧ rest.length < e ∧
      ∃ h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q,
        ValidChoiceCode ((S.clique rest).recast _ h).a S.fw i

theorem clique_nil_eq : S.clique [] = S.C₀ := rfl

theorem clique_cons_childAt (i : ℕ) (rest : List ℕ) :
    S.clique (i :: rest) = childAt S.fw (S.clique rest) i := rfl

theorem chainOK_facts {e : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ e) : ∀ {chs : List ℕ}, S.ChainOK e chs →
    chs.length ≤ e ∧ (S.clique chs).q = 2 ^ 2 ^ (e - chs.length) ∧
      (S.clique chs).potential * 2 ^ chs.length ≤ S.C₀.potential
  | [], _ => ⟨Nat.zero_le _, by simpa [clique_nil_eq] using hq, by simp [clique_nil_eq]⟩
  | i :: rest, ⟨hr, hlen, hsq, hv⟩ => by
    obtain ⟨_, h2, h3⟩ := chainOK_facts hq hr
    refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
    · rw [clique_cons_childAt, childAt_q _ _ _ hsq, h2, List.length_cons,
        show e - rest.length = (e - (rest.length + 1)) + 1 by omega, pow_succ, pow_mul,
        Nat.sqrt_eq']
    · have := two_mul_potential_childAt S.fw (S.clique rest) i hsq hv
      rw [clique_cons_childAt, List.length_cons, pow_succ]
      calc (childAt S.fw (S.clique rest) i).potential * (2 ^ rest.length * 2)
          = 2 * (childAt S.fw (S.clique rest) i).potential * 2 ^ rest.length := by ring
        _ ≤ (S.clique rest).potential * 2 ^ rest.length := Nat.mul_le_mul_right _ this
        _ ≤ _ := h3

/-- Every budget sum along the chain is at most `Φ₀ / 2^e`. -/
theorem spair_mul_le {e : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ e) {chs : List ℕ} (h : S.ChainOK e chs) :
    (S.clique chs).spair * 2 ^ e ≤ S.C₀.potential := by
  obtain ⟨h1, h2, h3⟩ := S.chainOK_facts hq h
  set x := e - chs.length
  have hx : x < 2 ^ x := Nat.lt_two_pow_self
  have he : 2 ^ e = 2 ^ x * 2 ^ chs.length := by rw [← pow_add]; congr 1; omega
  have hq1 : 2 ^ x ≤ ((S.clique chs).q - 1) ^ 2 := by
    rw [h2]
    have : 2 ^ x ≤ 2 ^ 2 ^ x - 1 := by
      have := Nat.lt_two_pow_self (n := 2 ^ x); omega
    calc 2 ^ x ≤ 2 ^ 2 ^ x - 1 := this
      _ ≤ (2 ^ 2 ^ x - 1) ^ 2 := by
        rw [sq]; exact Nat.le_mul_of_pos_left _ (by have := Nat.one_le_two_pow (n := x); omega)
  rw [Clique.potential_eq] at h3
  calc (S.clique chs).spair * 2 ^ e = (S.clique chs).spair * 2 ^ x * 2 ^ chs.length := by
        rw [he, mul_assoc]
    _ ≤ (S.clique chs).spair * ((S.clique chs).q - 1) ^ 2 * 2 ^ chs.length := by gcongr
    _ = ((S.clique chs).q - 1) ^ 2 * (S.clique chs).spair * 2 ^ chs.length := by ring
    _ ≤ _ := h3

theorem parentGrid_eq_some {rest : List ℕ} (i : ℕ)
    (h : (S.clique rest).q = Nat.sqrt (S.clique rest).q * Nat.sqrt (S.clique rest).q) :
    S.parentGrid rest i = some ⟨Nat.sqrt (S.clique rest).q, ((S.clique rest).recast _ h).a,
      ((S.clique rest).recast _ h).T, decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i,
      orientRow ((S.clique rest).recast _ h).a
        fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1⟩ := by
  unfold parentGrid
  rw [dite_pos' h]

end Setup

/-! ### The budget of the transport recursion -/

theorem codeWidth_mono {a b : ℕ} (h : a ≤ b) : codeWidth a ≤ codeWidth b := by
  unfold codeWidth
  split_ifs with ha hb
  · exact le_rfl
  · exact Nat.zero_le _
  · omega
  · exact Nat.add_le_add_right (Nat.sqrt_le_sqrt (by omega)) _

theorem pivWidth_eq_sizes (W : ℕ) : pivWidth W =
    Nat.size W + Nat.size (3 * W + 3) + 3 * codeWidth W + 2 * Nat.size (2 * W) := rfl

theorem pivWidth_mono {a b : ℕ} (h : a ≤ b) : pivWidth a ≤ pivWidth b := by
  rw [pivWidth_eq_sizes, pivWidth_eq_sizes]
  have := Nat.size_le_size h
  have := Nat.size_le_size (show 3 * a + 3 ≤ 3 * b + 3 by omega)
  have := Nat.size_le_size (show 2 * a ≤ 2 * b by omega)
  have := codeWidth_mono h
  omega

/-- The budget of the transport recursion at weight `W`: a pivot index, three product nodes, and the
recursion at half the weight. -/
def trB (ℓ : ℕ) : ℕ → ℕ
  | 0 => pivWidth 0 + 3 * ℓ
  | W + 1 => pivWidth (W + 1) + 3 * ℓ + trB ℓ ((W + 1) / 2)
decreasing_by omega

theorem trB_pos (ℓ W : ℕ) (hW : 1 ≤ W) : trB ℓ W = pivWidth W + 3 * ℓ + trB ℓ (W / 2) := by
  obtain ⟨W, rfl⟩ : ∃ W', W = W' + 1 := ⟨W - 1, by omega⟩
  rw [trB]

theorem trB_ge (ℓ W : ℕ) : pivWidth W + 3 * ℓ ≤ trB ℓ W := by
  rcases Nat.eq_zero_or_pos W with rfl | hW
  · rw [trB]
  · rw [trB_pos ℓ W hW]; omega

theorem trB_mono (ℓ : ℕ) : ∀ b a, a ≤ b → trB ℓ a ≤ trB ℓ b := by
  intro b
  induction b using Nat.strong_induction_on with
  | _ b ih =>
    intro a hab
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · rcases Nat.eq_zero_or_pos b with rfl | hb
      · exact le_rfl
      · rw [trB_pos ℓ b hb, trB]
        have := pivWidth_mono (Nat.zero_le b)
        omega
    · rw [trB_pos ℓ a ha, trB_pos ℓ b (by omega)]
      have := pivWidth_mono hab
      have := ih (b / 2) (by omega) (a / 2) (Nat.div_le_div_right hab)
      omega


/-! ### The width of a code of copies (Cauchy–Schwarz) -/

/-- Twice the sum of the budgets: every pair, from both ends. -/
theorem sum_budgets (C : Clique) :
    ∑ w ∈ range C.q, ∑ u ∈ range C.q, (if h : u < C.q ∧ w < C.q then
      (if u = w then 0 else budget C.a ⟨w, h.2⟩ ⟨u, h.1⟩) else 0) = 2 * C.spair := by
  rw [← Fin.sum_univ_eq_sum_range]
  simp_rw [← Fin.sum_univ_eq_sum_range (fun u => if h : u < C.q ∧ _ < C.q then _ else 0)]
  simp only [Fin.is_lt, and_self, dite_true, Fin.eta, Fin.val_inj]
  rw [← Fintype.sum_prod_type' (f := fun w u : Fin C.q => if u = w then 0 else budget C.a w u)]
  have hsplit : ∀ x : Fin C.q × Fin C.q, (if x.2 = x.1 then 0 else budget C.a x.1 x.2) =
      (if x.1 < x.2 then C.a x.1 x.2 else 0) + (if x.2 < x.1 then C.a x.2 x.1 else 0) := by
    intro x
    rcases lt_trichotomy x.1 x.2 with h | h | h
    · simp [h, h.ne', not_lt_of_gt h, MergeProof.budget_of_lt _ h]
    · simp [h]
    · simp only [h, h.ne, not_lt_of_gt h, ite_false, ite_true, zero_add]
      rw [MergeProof.budget_comm, MergeProof.budget_of_lt _ h]
  simp only [hsplit, Finset.sum_add_distrib]
  have h1 : ∑ x : Fin C.q × Fin C.q, (if x.1 < x.2 then C.a x.1 x.2 else 0) = C.spair := by
    rw [← Finset.sum_filter, Clique.spair]
    exact Finset.sum_subtype _ (fun x => by simp) (fun x : Fin C.q × Fin C.q => C.a x.1 x.2)
  have h2 : ∑ x : Fin C.q × Fin C.q, (if x.2 < x.1 then C.a x.2 x.1 else 0) =
      ∑ x : Fin C.q × Fin C.q, (if x.1 < x.2 then C.a x.1 x.2 else 0) :=
    Fintype.sum_equiv (Equiv.prodComm _ _) _ _ fun x => rfl
  rw [h2, h1]; ring

/-- **The width of a code of copies** held by `g` nodes of a clique on `q` nodes:
`w(ξ)^2 ≤ 1800 g q ∑ a`, by `w(a)^2 ≤ 900 a` and Cauchy–Schwarz over the `g q` labels. -/
theorem copiesWidth_sq (C : Clique) (nodes : ℕ → ℕ) (g : ℕ)
    (hinj : Set.InjOn nodes (range g : Set ℕ)) :
    copiesWidth C nodes g ^ 2 ≤ 1800 * (g * C.q) * C.spair := by
  set F : ℕ → ℕ → ℕ := fun w u => if h : u < C.q ∧ w < C.q then
    (if u = w then 0 else codeWidth (budget C.a ⟨w, h.2⟩ ⟨u, h.1⟩)) else 0
  set B : ℕ → ℕ → ℕ := fun w u => if h : u < C.q ∧ w < C.q then
    (if u = w then 0 else budget C.a ⟨w, h.2⟩ ⟨u, h.1⟩) else 0
  have hX : copiesWidth C nodes g = ∑ x ∈ range g ×ˢ range C.q, F (nodes x.1) x.2 := by
    rw [Finset.sum_product]; rfl
  have hFB : ∀ w u, F w u ^ 2 ≤ 900 * B w u := by
    intro w u
    simp only [F, B]
    split_ifs
    · simp
    · exact codeWidth_sq_le _
    · simp
  have hB : ∑ p ∈ range g, ∑ u ∈ range C.q, B (nodes p) u ≤ 2 * C.spair := by
    rw [← sum_budgets C]
    rw [← Finset.sum_image (f := fun w => ∑ u ∈ range C.q, B w u) hinj]
    rw [← Finset.sum_filter_of_ne (p := fun w => w < C.q) (fun w _ hw => by
      by_contra h
      exact hw (Finset.sum_eq_zero fun u _ => by simp [B, h]))]
    exact Finset.sum_le_sum_of_subset (fun w hw => by
      simp only [Finset.mem_filter] at hw; exact Finset.mem_range.mpr hw.2)
  rw [hX]
  calc (∑ x ∈ range g ×ˢ range C.q, F (nodes x.1) x.2) ^ 2
      ≤ (range g ×ˢ range C.q).card * ∑ x ∈ range g ×ˢ range C.q, F (nodes x.1) x.2 ^ 2 :=
        sq_sum_le_card_mul_sum_sq
    _ ≤ (g * C.q) * ∑ x ∈ range g ×ˢ range C.q, 900 * B (nodes x.1) x.2 := by
        rw [Finset.card_product, Finset.card_range, Finset.card_range]
        exact Nat.mul_le_mul_left _ (Finset.sum_le_sum fun x _ => hFB _ _)
    _ = (g * C.q) * (900 * ∑ p ∈ range g, ∑ u ∈ range C.q, B (nodes p) u) := by
        rw [← Finset.mul_sum, Finset.sum_product]
    _ ≤ (g * C.q) * (900 * (2 * C.spair)) := by gcongr
    _ = 1800 * (g * C.q) * C.spair := by ring

theorem holders_injOn (g v : ℕ) (row : Bool) (hg : 0 < g) :
    Set.InjOn (Setup.holders g v row) (range g : Set ℕ) := by
  intro p _ p' _ h
  simp only [Setup.holders] at h
  cases row
  · simp only [Bool.false_eq_true, ↓reduceIte] at h
    exact Nat.eq_of_mul_eq_mul_right hg (by omega)
  · simp only [↓reduceIte] at h; omega

/-- `3k ≤ 2 + 2^k`. -/
theorem three_mul_le_two_pow (k : ℕ) : 3 * k ≤ 2 + 2 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k <;> simp
    · have : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) h
      rw [pow_succ]; omega

/-- `g q h^3 ≤ 128 (q - 1)^2` for `g = 2^(2^k)`, `q = g^2` and `h = 2^(k+1)`. -/
theorem ghq_le (k : ℕ) :
    2 ^ 2 ^ k * (2 ^ 2 ^ k * 2 ^ 2 ^ k) * (2 ^ (k + 1)) ^ 3 ≤
      128 * (2 ^ 2 ^ k * 2 ^ 2 ^ k - 1) ^ 2 := by
  set g := 2 ^ 2 ^ k
  have hg : 2 ≤ g := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ g := Nat.pow_le_pow_right (by norm_num) Nat.one_le_two_pow
  have hh : (2 ^ (k + 1)) ^ 3 ≤ 32 * g := by
    rw [← pow_mul, show 32 = 2 ^ 5 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by have := three_mul_le_two_pow k; omega)
  have hq : g * g ≤ 2 * (g * g - 1) := by
    have : 4 ≤ g * g := Nat.mul_le_mul hg hg
    omega
  calc g * (g * g) * (2 ^ (k + 1)) ^ 3 ≤ g * (g * g) * (32 * g) := Nat.mul_le_mul_left _ hh
    _ = 32 * ((g * g) * (g * g)) := by ring
    _ ≤ 32 * ((2 * (g * g - 1)) * (2 * (g * g - 1))) := by gcongr
    _ = 128 * (g * g - 1) ^ 2 := by ring

namespace Setup

variable (S : Setup)

/-- **The copies of a table entry** of a clique at a path of length `n + 1` take at most
`Ξ / h` bits, where `h = 2^(e-n)` is the name length of the parent and
`Ξ = ⌊√(230400 Φ₀ / 2^e)⌋`. -/
theorem xiWidth_le {e : ℕ} (hq : S.C₀.q = 2 ^ 2 ^ e) {i : ℕ} {rest : List ℕ}
    (hc : S.ChainOK e (i :: rest)) (v : ℕ) :
    S.xiWidth rest i v ≤ Nat.sqrt (230400 * S.C₀.potential / 2 ^ e) / 2 ^ (e - rest.length) := by
  obtain ⟨hr, hlen, hsq, -⟩ := hc
  obtain ⟨-, hqc, hpot⟩ := S.chainOK_facts hq hr
  obtain ⟨k, hk⟩ : ∃ k, e - rest.length = k + 1 := ⟨e - rest.length - 1, by omega⟩
  have hsqrt : Nat.sqrt (S.clique rest).q = 2 ^ 2 ^ k := by
    rw [hqc, hk, pow_succ, pow_mul, Nat.sqrt_eq']
  have hqq : (S.clique rest).q = 2 ^ 2 ^ k * 2 ^ 2 ^ k := by rw [hsq, hsqrt]
  have hx : S.xiWidth rest i v = copiesWidth (S.clique rest)
      (holders (Nat.sqrt (S.clique rest).q) v (orientRow ((S.clique rest).recast _ hsq).a
        fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1))
      (Nat.sqrt (S.clique rest).q) := by
    unfold xiWidth; rw [S.parentGrid_eq_some i hsq]
  have hX := copiesWidth_sq (S.clique rest) _ _ (holders_injOn (Nat.sqrt (S.clique rest).q) v
    (orientRow ((S.clique rest).recast _ hsq).a
        fun r => (decodeChoice (Nat.sqrt (S.clique rest).q) S.fw i r).1)
    (by rw [hsqrt]; positivity))
  rw [← hx, hsqrt, hqq] at hX
  rw [Clique.potential_eq, hqq] at hpot
  set X := S.xiWidth rest i v
  set g := 2 ^ 2 ^ k
  set sp := (S.clique rest).spair
  have he : 2 ^ e = 2 ^ (k + 1) * 2 ^ rest.length := by rw [← pow_add]; congr 1; omega
  have hgh := ghq_le k
  have key : (X * 2 ^ (k + 1)) ^ 2 * 2 ^ e ≤ 230400 * S.C₀.potential := by
    calc (X * 2 ^ (k + 1)) ^ 2 * 2 ^ e = X ^ 2 * (2 ^ (k + 1)) ^ 3 * 2 ^ rest.length := by
          rw [he]; ring
      _ ≤ 1800 * (g * (g * g)) * sp * (2 ^ (k + 1)) ^ 3 * 2 ^ rest.length := by gcongr
      _ = 1800 * (g * (g * g) * (2 ^ (k + 1)) ^ 3) * sp * 2 ^ rest.length := by ring
      _ ≤ 1800 * (128 * (g * g - 1) ^ 2) * sp * 2 ^ rest.length := by gcongr
      _ = 230400 * ((g * g - 1) ^ 2 * sp * 2 ^ rest.length) := by ring
      _ ≤ 230400 * S.C₀.potential := Nat.mul_le_mul_left _ hpot
  have h1 : (X * 2 ^ (k + 1)) ^ 2 ≤ 230400 * S.C₀.potential / 2 ^ e :=
    (Nat.le_div_iff_mul_le (by positivity)).mpr key
  have h2 : X * 2 ^ (k + 1) ≤ Nat.sqrt (230400 * S.C₀.potential / 2 ^ e) := Nat.le_sqrt'.mpr h1
  rw [hk]
  exact (Nat.le_div_iff_mul_le (by positivity)).mpr h2

end Setup

/-! ### The budget -/

/-- The parameters of the budget: the number `e` of merges, the product cost `ℓ`, bounds `Λ` for
the last label, `Ξ` for the copies of a table entry (`Ξ / h` from a parent of name length `h`),
`D0` and `Dm` for the depths of the products of the first clique and of the merged cliques, and
`Wm` for the weights of the transport recursion. -/
structure BudPar where
  e : ℕ
  ℓ : ℕ
  Λ : ℕ
  Ξ : ℕ
  D0 : ℕ
  Dm : ℕ
  Wm : ℕ

namespace BudPar

variable (π : BudPar)

/-- The budget of a table entry of the clique at a path of length `n`. -/
def asc : ℕ → ℕ
  | 0 => π.ℓ * (1 + π.D0) + trB π.ℓ π.Wm
  | n + 1 => π.Ξ / 2 ^ (π.e - n) + π.ℓ * (1 + π.Dm) + asc n

/-- The budget of the value of a clique `k` merges above the end of the descent. -/
def desc (fw : ℕ) : ℕ → ℕ
  | 0 => π.Λ + 2 * π.ℓ + π.asc π.e
  | k + 1 => choiceWidth (2 ^ 2 ^ k) fw + π.ℓ + desc fw k

theorem trB_le_asc : ∀ n, trB π.ℓ π.Wm ≤ π.asc n
  | 0 => by simp only [asc]; omega
  | n + 1 => by simp only [asc]; exact (trB_le_asc n).trans (Nat.le_add_left _ _)

theorem asc_le : ∀ n ≤ π.e, π.asc n ≤
    π.ℓ * (1 + π.D0) + trB π.ℓ π.Wm + n * (π.ℓ * (1 + π.Dm)) + π.Ξ / 2 ^ (π.e - n)
  | 0, _ => by simp only [asc, zero_mul, add_zero]; exact Nat.le_add_right _ _
  | n + 1, h => by
    have ih := asc_le n (by omega)
    have hd : 2 * (π.Ξ / 2 ^ (π.e - n)) ≤ π.Ξ / 2 ^ (π.e - (n + 1)) := by
      rw [show π.e - n = (π.e - (n + 1)) + 1 by omega, pow_succ, ← Nat.div_div_eq_div_mul]
      exact Nat.mul_div_le _ _
    simp only [asc]
    rw [Nat.succ_mul]
    omega

theorem desc_le (fw : ℕ) : ∀ k ≤ π.e, π.desc fw k ≤
    k * (choiceWidth (2 ^ 2 ^ (π.e - 1)) fw + π.ℓ) + π.desc fw 0
  | 0, _ => by simp
  | k + 1, h => by
    have ih := desc_le fw k (by omega)
    have hc : choiceWidth (2 ^ 2 ^ k) fw ≤ choiceWidth (2 ^ 2 ^ (π.e - 1)) fw := by
      unfold choiceWidth
      have : 2 ^ 2 ^ k ≤ 2 ^ 2 ^ (π.e - 1) :=
        Nat.pow_le_pow_right (by norm_num) (Nat.pow_le_pow_right (by norm_num) (by omega))
      gcongr
    change choiceWidth (2 ^ 2 ^ k) fw + π.ℓ + π.desc fw k ≤ _
    rw [Nat.succ_mul]
    omega

end BudPar

/-! ### The transport budget in real numbers -/

theorem size_three_le (W : ℕ) : Nat.size (3 * W + 3) ≤ Nat.size W + 2 := by
  rw [Nat.size_le, pow_add]
  have := Nat.lt_size_self W
  omega

theorem size_two_le (W : ℕ) : Nat.size (2 * W) ≤ Nat.size W + 1 := by
  rw [Nat.size_le, pow_succ]
  have := Nat.lt_size_self W
  omega

theorem size_half_lt {W : ℕ} (hW : 1 ≤ W) : Nat.size (W / 2) + 1 ≤ Nat.size W := by
  have : Nat.size (W / 2) < Nat.size W := by
    rw [Nat.lt_size]
    rcases Nat.eq_zero_or_pos (W / 2) with h | h
    · rw [h, Nat.size_zero, pow_zero]; exact hW
    · have h1 : Nat.size (W / 2) - 1 < Nat.size (W / 2) := by
        have : 0 < Nat.size (W / 2) := Nat.size_pos.mpr h
        omega
      have h2 := Nat.lt_size.mp h1
      calc 2 ^ Nat.size (W / 2) = 2 * 2 ^ (Nat.size (W / 2) - 1) := by
            rw [← pow_succ']; congr 1; omega
        _ ≤ 2 * (W / 2) := Nat.mul_le_mul_left _ h2
        _ ≤ W := Nat.mul_div_le _ _
  omega

theorem codeWidth_le_real (a : ℕ) : (codeWidth a : ℝ) ≤ 28 * Real.sqrt a + 2 := by
  unfold codeWidth
  split_ifs with ha
  · simp only [Nat.cast_zero]; positivity
  · push_cast
    have h1 := Real.nat_sqrt_le_real_sqrt (a := 784 * a)
    have h2 : Real.sqrt ((784 * a : ℕ) : ℝ) = 28 * Real.sqrt a := by
      push_cast
      rw [Real.sqrt_mul (by norm_num), show (784 : ℝ) = 28 ^
          2 by norm_num, Real.sqrt_sq (by norm_num)]
    linarith

theorem pivWidth_le_real (W : ℕ) :
    (pivWidth W : ℝ) ≤ 4 * Nat.size W + 10 + 84 * Real.sqrt W := by
  rw [pivWidth_eq_sizes]
  have h1 := size_three_le W
  have h2 := size_two_le W
  have h3 := codeWidth_le_real W
  have h4 : (Nat.size (3 * W + 3) : ℝ) ≤ Nat.size W + 2 := by exact_mod_cast h1
  have h5 : (Nat.size (2 * W) : ℝ) ≤ Nat.size W + 1 := by exact_mod_cast h2
  push_cast
  linarith

theorem sqrt_half_le (W : ℕ) : Real.sqrt ((W / 2 : ℕ) : ℝ) ≤ 3 / 4 * Real.sqrt W := by
  have h : ((W / 2 : ℕ) : ℝ) ≤ (3 / 4) ^ 2 * W := by
    have : ((W / 2 : ℕ) : ℝ) ≤ (W : ℝ) / 2 := Nat.cast_div_le
    have : (0 : ℝ) ≤ W := Nat.cast_nonneg W
    nlinarith
  calc Real.sqrt ((W / 2 : ℕ) : ℝ) ≤ Real.sqrt ((3 / 4) ^ 2 * W) := Real.sqrt_le_sqrt h
    _ = 3 / 4 * Real.sqrt W := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by norm_num)]

/-- **The transport recursion** costs `O(√W + log² W)`: `trB ℓ W ≤ 336 √W + (s+1)(4s + 10 + 3ℓ)`
with `s` the bit size of `W`. -/
theorem trB_le_real (ℓ : ℕ) : ∀ W : ℕ, (trB ℓ W : ℝ) ≤
    336 * Real.sqrt W + ((Nat.size W : ℝ) + 1) * (4 * Nat.size W + 10 + 3 * ℓ) := by
  intro W
  induction W using Nat.strong_induction_on with
  | _ W ih =>
    rcases Nat.eq_zero_or_pos W with rfl | hW
    · rw [trB]
      have := pivWidth_le_real 0
      push_cast at this ⊢
      simp only [Nat.size_zero, CharP.cast_eq_zero, Real.sqrt_zero] at this ⊢
      nlinarith
    · rw [trB_pos ℓ W hW]
      have ih' := ih (W / 2) (by omega)
      have hp := pivWidth_le_real W
      have hs := size_half_lt hW
      have hs' : ((Nat.size (W / 2) : ℕ) : ℝ) + 1 ≤ Nat.size W := by exact_mod_cast hs
      have hsq := sqrt_half_le W
      have h0 : (0 : ℝ) ≤ Nat.size (W / 2) := Nat.cast_nonneg _
      have hl : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg _
      have hr : (0 : ℝ) ≤ Real.sqrt W := Real.sqrt_nonneg _
      push_cast
      nlinarith

theorem srcSub_take (up : Bool) (x y m : Label) (lo hi ν : ℕ) (h : ν ≤ hi - lo) :
    srcSub up x y m lo (lo + ν) = (srcSub up x y m lo hi).take ν := by
  simp only [srcSub, List.take_take, Nat.add_sub_cancel_left]
  congr 1; omega

theorem srcSub_drop (up : Bool) (x y m : Label) (lo hi ν : ℕ) :
    srcSub up x y m (lo + ν + 1) hi = (srcSub up x y m lo hi).drop (ν + 1) := by
  simp only [srcSub, List.drop_take, List.drop_drop]
  rw [show hi - (lo + ν + 1) = hi - lo - (ν + 1) by omega, show lo + ν + 1 = lo + (ν + 1) by omega]

theorem rangeSt_cases (mk : ℕ → St) (mkR : ℕ → ℕ → St) (lo hi : ℕ) :
    Setup.rangeSt mk mkR lo hi = .lit 1 ∨ Setup.rangeSt mk mkR lo hi = mk lo ∨
      (2 ≤ hi - lo ∧ Setup.rangeSt mk mkR lo hi = mkR lo hi) := by
  unfold Setup.rangeSt
  split_ifs with h1 h2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr ⟨by omega, rfl⟩)

theorem clog_half {L L' : ℕ} (hL : 2 ≤ L) (h : L' ≤ (L + 1) / 2) :
    Nat.clog 2 L' + 1 ≤ Nat.clog 2 L := by
  rw [Nat.clog_of_two_le (by norm_num) hL]
  have := Nat.clog_mono_right 2 (show L' ≤ (L + 2 - 1) / 2 by omega)
  omega

/-- A product over a factor range of at most half the length of a range of length `L ≥ 2`. -/
theorem range_step {inv : St → Prop} {bud : St → ℕ} {ℓ Bf L lo hi : ℕ} (mk : ℕ → St)
    (mkR : ℕ → ℕ → St) (hL : 2 ≤ L) (hlen : hi - lo ≤ (L + 1) / 2)
    (hlit : inv (.lit 1) ∧ bud (.lit 1) = 0) (hmk : ∀ f, inv (mk f) ∧ bud (mk f) ≤ Bf)
    (hmkR : ∀ a b, 2 ≤ b - a → inv (mkR a b) ∧ bud (mkR a b) ≤ ℓ * Nat.clog 2 (b - a) + Bf) :
    inv (Setup.rangeSt mk mkR lo hi) ∧ bud (Setup.rangeSt mk mkR lo hi) + ℓ ≤
      ℓ * Nat.clog 2 L + Bf := by
  have h1 : 1 ≤ Nat.clog 2 L := Nat.clog_pos (by norm_num) (by omega)
  have hl1 : ℓ ≤ ℓ * Nat.clog 2 L := Nat.le_mul_of_pos_right _ h1
  rcases rangeSt_cases mk mkR lo hi with h | h | ⟨h2, h⟩
  · rw [h]; refine ⟨hlit.1, ?_⟩; rw [hlit.2]; omega
  · rw [h]; refine ⟨(hmk lo).1, ?_⟩; have := (hmk lo).2; omega
  · rw [h]
    refine ⟨(hmkR lo hi h2).1, ?_⟩
    have := (hmkR lo hi h2).2
    have := Nat.mul_le_mul_left ℓ (clog_half hL hlen)
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

namespace Setup

variable (S : Setup)

/-- The budget of a state. -/
def bud (π : BudPar) : St → ℕ
  | .cl chs => π.desc S.fw (π.e - chs.length)
  | .last chs _ => π.ℓ + π.asc chs.length
  | .ent chs _ _ => π.asc chs.length
  | .rng (_ :: rest) _ _ _ lo hi => π.ℓ * Nat.clog 2 (hi - lo) + π.asc rest.length
  | .rng0 _ _ lo hi => π.ℓ * Nat.clog 2 (hi - lo)
  | .tr up x y m lo hi T _ => trB π.ℓ (tWt (srcSub up x y m lo hi) T)
  | .trm up x y m lo ν hi _ T₁ T₂ _ _ _ =>
    2 * π.ℓ + trB π.ℓ (max (tWt (srcSub up x y m lo ν) T₁) (tWt (srcSub up x y m (ν + 1) hi) T₂))
  | .trr up x y m ν hi _ T₂ _ _ => π.ℓ + trB π.ℓ (tWt (srcSub up x y m (ν + 1) hi) T₂)
  | _ => 0

/-- The invariant of the states on the paths of the formula. -/
def inv (π : BudPar) : St → Prop
  | .zero | .lit _ => True
  | .cl chs | .last chs _ | .ent chs _ _ => S.ChainOK π.e chs
  | .rng [] _ _ _ _ _ => False
  | .rng (i :: rest) _ _ _ lo hi => S.ChainOK π.e (i :: rest) ∧ 2 ≤ hi - lo
  | .rng0 _ _ lo hi => 2 ≤ hi - lo
  | .tr up x y m lo hi T _ => tWt (srcSub up x y m lo hi) T ≤ π.Wm
  | .trm up x y m lo ν hi _ T₁ T₂ _ _ _ =>
    tWt (srcSub up x y m lo ν) T₁ ≤ π.Wm ∧ tWt (srcSub up x y m (ν + 1) hi) T₂ ≤ π.Wm
  | .trr up x y m ν hi _ T₂ _ _ => tWt (srcSub up x y m (ν + 1) hi) T₂ ≤ π.Wm

theorem diagWt_recast_le (C : Clique) {g : ℕ} (h : C.q = g * g) (r : Rect g) :
    diagWt (C.recast (g * g) h).a r ≤ 2 * C.spair := by
  have h1 : (C.recast (g * g) h).a (node r.1.1.1 r.1.2.1) (node r.1.1.2 r.1.2.2) ≤ C.spair :=
    C.a_le_spair
        (by simp only [Fin.lt_def, Fin.val_cast]; exact Fin.lt_def.mp (node_lt_node r.2.1 _ _))
  have h2 : (C.recast (g * g) h).a (node r.1.1.1 r.1.2.2) (node r.1.1.2 r.1.2.1) ≤ C.spair :=
    C.a_le_spair
        (by simp only [Fin.lt_def, Fin.val_cast]; exact Fin.lt_def.mp (node_lt_node r.2.1 _ _))
  unfold diagWt
  omega

theorem wt_m_le (C : Clique) {g fw i : ℕ} (h : C.q = g * g)
    (hv : decodeChoice g fw i ∈ choices (C.recast (g * g) h).a) (r : Rect g) {m : Label}
    (hm : (labelWt m : ℤ) ≤ (diagWt (C.recast (g * g) h).a r : ℤ) + (decodeChoice g fw i r).1 / 2 ∨
      (labelWt m : ℤ) ≤ (diagWt (C.recast (g * g) h).a r : ℤ) - (decodeChoice g fw i r).1 / 2) :
    labelWt m ≤ 4 * C.spair := by
  have hr := Fintype.mem_piFinset.mp hv r
  simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hr
  have hd : (diagWt (C.recast (g * g) h).a r : ℤ) ≤ 2 * C.spair := by
    exact_mod_cast diagWt_recast_le C h r
  omega

/-- A state is a good factor of an entry at a path of length `n`. -/
def FacOK (π : BudPar) (n : ℕ) (st : St) : Prop := S.inv π st ∧ S.bud π st ≤ π.asc n

theorem facOK_ite {π : BudPar} {n : ℕ} (c : Prop) [Decidable c] (a b : St)
    (ha : c → S.FacOK π n a) (hb : ¬c → S.FacOK π n b) : S.FacOK π n (if c then a else b) := by
  split_ifs with h
  · exact ha h
  · exact hb h

theorem facOK_dite {π : BudPar} {n : ℕ} (c : Prop) [Decidable c] (a : c → St) (b : ¬c → St)
    (ha : ∀ h, S.FacOK π n (a h)) (hb : ∀ h, S.FacOK π n (b h)) : S.FacOK π n (dite c a b) := by
  split_ifs with h
  · exact ha h
  · exact hb h

/-- The factors of a table entry. -/
theorem factor_ok (π : BudPar) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hWm : 6 * (S.C₀.potential / 2 ^ π.e) ≤ π.Wm) {i : ℕ} {rest : List ℕ}
    (hc : S.ChainOK π.e (i :: rest)) (v args ξ f : ℕ) :
    S.FacOK π rest.length (S.factorSt rest i v args ξ f) := by
  obtain ⟨hr, -, hsq, hv⟩ := hc
  have hsp : (S.clique rest).spair ≤ S.C₀.potential / 2 ^ π.e :=
    (Nat.le_div_iff_mul_le (by positivity)).mpr (S.spair_mul_le hq hr)
  have htr : ∀ up x y m c, labelWt x ≤ (S.clique rest).spair → labelWt y ≤ (S.clique rest).spair →
      labelWt m ≤ 4 * (S.clique rest).spair →
      S.inv π (.tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) c) ∧
        S.bud π (.tr up x y m 0 (srcList up x y m).length (tgtMs up x y m) c) ≤
          π.asc rest.length := by
    intro up x y m c hx hy hm
    have e1 : srcSub up x y m 0 (srcList up x y m).length = srcList up x y m := by simp [srcSub]
    simp only [inv, bud, e1, tWt_srcList]
    have hW : labelWt x + labelWt y + labelWt m ≤ π.Wm := by omega
    exact ⟨hW, (trB_mono _ _ _ hW).trans (π.trB_le_asc _)⟩
  have hsw : ∀ l : Label, labelWt l ≤ (S.clique rest).spair →
      labelWt (swapLabel l) ≤ (S.clique rest).spair := fun l h => by
    rw [MergeProof.labelWt_swap]; exact h
  have hk := fun r (m : Label) => wt_m_le (S.clique rest) hsq hv.1 r (m := m)
  have z : FacOK S π rest.length .zero := ⟨trivial, Nat.zero_le _⟩
  have lt : ∀ z, FacOK S π rest.length (.lit z) := fun _ => ⟨trivial, Nat.zero_le _⟩
  change FacOK S π rest.length _
  unfold factorSt
  rw [S.parentGrid_eq_some i hsq]
  dsimp only
  refine S.facOK_ite _ _ _ (fun _ => ⟨hr, le_rfl⟩) fun _ => ?_
  refine S.facOK_ite _ _ _ (fun _ => lt _) fun _ => ?_
  refine S.facOK_ite _ _ _ (fun _ => lt _) fun _ => ?_
  refine S.facOK_dite _ _ _ (fun _ => ?_) (fun _ => lt _)
  refine S.facOK_ite _ _ _ (fun _ => ?_) (fun _ => ?_)
  · refine S.facOK_ite _ _ _
      (fun _ => S.facOK_ite _ _ _ (fun hm => htr _ _ _ _ _ (labelWt_copyAt ..)
      (labelWt_copyAt ..) (hk _ _ (Or.inl hm))) fun _ => z) fun _ => ?_
    refine S.facOK_ite _ _ _ (fun _ => S.facOK_ite _ _ _ (fun hm => htr _ _ _ _ _
      (hsw _ (labelWt_copyAt ..)) (hsw _ (labelWt_copyAt ..)) (hk _ _ (Or.inl hm))) fun _ => z)
      fun _ => lt _
  · refine S.facOK_ite _ _ _
      (fun _ => S.facOK_ite _ _ _ (fun hm => htr _ _ _ _ _ (labelWt_copyAt ..)
      (hsw _ (labelWt_copyAt ..)) (hk _ _ (Or.inr hm))) fun _ => z) fun _ => ?_
    refine S.facOK_ite _ _ _ (fun _ => S.facOK_ite _ _ _ (fun hm => htr _ _ _ _ _
      (labelWt_copyAt ..) (hsw _ (labelWt_copyAt ..)) (hk _ _ (Or.inr hm))) fun _ => z)
      fun _ => lt _

/-- The transport sum node. -/
theorem sum_tr (π : BudPar) (up : Bool) (x y m : Label) (lo hi : ℕ) (T : Multiset (HPlace × ℕ))
    (c : ℤ) (i : ℕ) (hinv : tWt (srcSub up x y m lo hi) T ≤ π.Wm) :
    S.inv π (S.gen.child (.tr up x y m lo hi T c) i) ∧
      S.bud π (S.gen.child (.tr up x y m lo hi T c) i) + S.gen.width (.tr up x y m lo hi T c) +
        π.ℓ ≤ S.bud π (.tr up x y m lo hi T c) := by
  simp only [Setup.gen]
  split_ifs with hv
  · unfold PivotValid at hv
    simp only at hv
    generalize decodePivot up (tWt (srcSub up x y m lo hi) T) i = d at hv ⊢
    obtain ⟨ν, t, T₁, c₁, c₀⟩ := d
    obtain ⟨-, hν, ht, hT₁, hpc, -⟩ := hv
    simp only at hν ht hT₁ hpc ⊢
    set l := srcSub up x y m lo hi with hl
    have hlen : l.length ≤ hi - lo := by rw [hl, srcSub]; exact List.length_take_le _ _
    have hh := pivot_halves l T ν t T₁ hν ht hT₁ hpc
    have hW1 : 1 ≤ tWt l T := by have := hpc.1; omega
    simp only [inv, bud]
    rw [srcSub_take up x y m lo hi ν (by omega), srcSub_drop up x y m lo hi ν, ← hl]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [trB_pos _ _ hW1]
    have := trB_mono π.ℓ (tWt l T / 2)
      (max (tWt (List.take ν l) T₁) (tWt (List.drop (ν + 1) l) (T - T₁ - {t})))
      (max_le (by omega) (by omega))
    omega
  · simp only [inv, bud, true_and]
    have := trB_ge π.ℓ (tWt (srcSub up x y m lo hi) T)
    omega

/-- The value of a clique: the descent. -/
theorem sum_cl (π : BudPar) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΛ : ∀ a, a * 2 ^ π.e ≤ S.C₀.potential → codeWidth a ≤ π.Λ) {chs : List ℕ}
    (hc : S.ChainOK π.e chs) (i : ℕ) :
    S.inv π (S.gen.child (.cl chs) i) ∧
      S.bud π (S.gen.child (.cl chs) i) + S.gen.width (.cl chs) + π.ℓ ≤ S.bud π (.cl chs) := by
  obtain ⟨hlen, hqc, -⟩ := S.chainOK_facts hq hc
  have hsp := S.spair_mul_le hq hc
  simp only [Setup.gen]
  by_cases h2 : (S.clique chs).q = 2
  · rw [dite_pos' h2, dite_pos' h2]
    have he : π.e - chs.length = 0 := by
      rw [h2] at hqc
      have : 2 ^ (π.e - chs.length) = 2 ^ 0 :=
        Nat.pow_right_injective (le_refl 2) (by simpa using hqc.symm)
      exact Nat.pow_right_injective (le_refl 2) this
    have hcw : codeWidth ((S.clique chs).a ⟨0, by omega⟩ ⟨1, by omega⟩) ≤ π.Λ :=
      hΛ _ ((Nat.mul_le_mul_right _ ((S.clique chs).a_le_spair (by simp [Fin.lt_def]))).trans hsp)
    have hb : S.bud π (.cl chs) = π.Λ + 2 * π.ℓ + π.asc π.e := by
      simp only [bud, he, BudPar.desc]
    rw [hb]
    have hl : chs.length = π.e := by omega
    split
    · split_ifs
      · simp only [inv, bud, hl]; exact ⟨hc, by omega⟩
      · simp only [inv, bud]; exact ⟨trivial, by omega⟩
    · simp only [inv, bud]; exact ⟨trivial, by omega⟩
  · rw [dite_neg' h2, dite_neg' h2]
    obtain ⟨k, hk⟩ : ∃ k, π.e - chs.length = k + 1 := by
      rcases Nat.eq_zero_or_pos (π.e - chs.length) with h | h
      · rw [h] at hqc; exact absurd hqc h2
      · exact ⟨_, (Nat.succ_pred_eq_of_pos h).symm⟩
    have hsqrt : Nat.sqrt (S.clique chs).q = 2 ^ 2 ^ k := by
      rw [hqc, hk, pow_succ, pow_mul, Nat.sqrt_eq']
    have hsq : (S.clique chs).q = Nat.sqrt (S.clique chs).q * Nat.sqrt (S.clique chs).q := by
      rw [hsqrt, hqc, hk, pow_succ, pow_mul, sq]
    rw [dite_pos' hsq]
    have hb : S.bud π (.cl chs) = choiceWidth (2 ^ 2 ^ k) S.fw + π.ℓ + π.desc S.fw k := by
      simp only [bud]; rw [hk, BudPar.desc]
    have hcw : choiceWidth (Nat.sqrt (S.clique chs).q) S.fw = choiceWidth (2 ^ 2 ^ k) S.fw := by
      rw [hsqrt]
    rw [hb, hcw]
    split_ifs with hv
    · simp only [inv, bud, List.length_cons]
      refine ⟨⟨hc, by omega, hsq, hv⟩, ?_⟩
      rw [show π.e - (chs.length + 1) = k by omega]
      omega
    · simp only [inv, bud]; exact ⟨trivial, by omega⟩

/-- A table entry of a merged clique: the sum over the copies. -/
theorem sum_ent (π : BudPar) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΞ : ∀ {i : ℕ} {rest : List ℕ} (v : ℕ), S.ChainOK π.e (i :: rest) →
      S.xiWidth rest i v ≤ π.Ξ / 2 ^ (π.e - rest.length))
    (hDm : ∀ k < π.e, nFac (2 ^ 2 ^ k) ≤ 2 ^ π.Dm) {i : ℕ} {rest : List ℕ}
    (hc : S.ChainOK π.e (i :: rest)) (v args ξ : ℕ) :
    S.inv π (S.gen.child (.ent (i :: rest) v args) ξ) ∧
      S.bud π (S.gen.child (.ent (i :: rest) v args) ξ) + S.gen.width (.ent (i :: rest) v args) +
        π.ℓ ≤ S.bud π (.ent (i :: rest) v args) := by
  have hx := hΞ v hc
  have hc' := hc
  obtain ⟨hr, hlen, hsq, -⟩ := hc'
  obtain ⟨-, hqc, -⟩ := S.chainOK_facts hq hr
  have hw : S.gen.width (.ent (i :: rest) v args) = S.xiWidth rest i v := rfl
  obtain ⟨k, hk⟩ : ∃ k, π.e - rest.length = k + 1 := ⟨π.e - rest.length - 1, by omega⟩
  have hsqrt : Nat.sqrt (S.clique rest).q = 2 ^ 2 ^ k := by
    rw [hqc, hk, pow_succ, pow_mul, Nat.sqrt_eq']
  have hD : Nat.clog 2 (nFac (Nat.sqrt (S.clique rest).q)) ≤ π.Dm :=
    Nat.clog_le_of_le_pow (hsqrt ▸ hDm k (by omega))
  have hb : S.bud π (.ent (i :: rest) v args) =
      π.Ξ / 2 ^ (π.e - rest.length) + π.ℓ * (1 + π.Dm) + π.asc rest.length := by
    simp only [bud, List.length_cons, BudPar.asc]
  rw [hw, hb]
  simp only [Setup.gen]
  rw [S.parentGrid_eq_some i hsq]
  dsimp only
  have hg : 2 ≤ nFac (Nat.sqrt (S.clique rest).q) := by
    rw [hsqrt, nFac]; have := Nat.one_le_two_pow (n := 2 ^ k); nlinarith
  split_ifs
  · simp only [inv, bud, Nat.sub_zero]
    refine ⟨⟨hc, hg⟩, ?_⟩
    have := Nat.mul_le_mul_left π.ℓ hD
    rw [Nat.mul_add, Nat.mul_one]
    omega
  · simp only [inv, bud]
    have : π.ℓ ≤ π.ℓ * (1 + π.Dm) := Nat.le_mul_of_pos_right _ (by omega)
    exact ⟨trivial, by omega⟩

/-- A product over the factors of an entry of a merged clique. -/
theorem prod_rng (π : BudPar) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hWm : 6 * (S.C₀.potential / 2 ^ π.e) ≤ π.Wm) {j : ℕ} {rest : List ℕ} {v args ξ lo hi : ℕ}
    (hc : S.ChainOK π.e (j :: rest)) (hL : 2 ≤ hi - lo) (b : ℕ) :
    S.inv π (S.gen.child (.rng (j :: rest) v args ξ lo hi) b) ∧
      S.bud π (S.gen.child (.rng (j :: rest) v args ξ lo hi) b) + π.ℓ ≤
        S.bud π (.rng (j :: rest) v args ξ lo hi) := by
  have hmk : ∀ f, S.inv π (S.factorSt rest j v args ξ f) ∧
      S.bud π (S.factorSt rest j v args ξ f) ≤ π.asc rest.length :=
    fun f => S.factor_ok π hq hWm hc v args ξ f
  have hmkR : ∀ a b, 2 ≤ b - a → S.inv π (.rng (j :: rest) v args ξ a b) ∧
      S.bud π (.rng (j :: rest) v args ξ a b) ≤ π.ℓ * Nat.clog 2 (b - a) + π.asc rest.length :=
    fun a b h => ⟨⟨hc, h⟩, le_rfl⟩
  have hlit : S.inv π (.lit 1) ∧ S.bud π (.lit 1) = 0 := ⟨trivial, rfl⟩
  simp only [Setup.gen]
  split_ifs
  · exact range_step _ _ hL (by omega) hlit hmk hmkR
  · exact range_step _ _ hL (by omega) hlit hmk hmkR

/-- A product over the factors of an entry of the first clique. -/
theorem prod_rng0 (π : BudPar) {v args lo hi : ℕ} (hL : 2 ≤ hi - lo) (b : ℕ) :
    S.inv π (S.gen.child (.rng0 v args lo hi) b) ∧
      S.bud π (S.gen.child (.rng0 v args lo hi) b) + π.ℓ ≤ S.bud π (.rng0 v args lo hi) := by
  have hmk : ∀ f, S.inv π ((fun f => St.lit (S.factor0 v args f)) f) ∧
      S.bud π ((fun f => St.lit (S.factor0 v args f)) f) ≤ 0 := fun f => ⟨trivial, le_rfl⟩
  have hmkR : ∀ a b, 2 ≤ b - a → S.inv π (.rng0 v args a b) ∧
      S.bud π (.rng0 v args a b) ≤ π.ℓ * Nat.clog 2 (b - a) + 0 := fun a b h => ⟨h, le_rfl⟩
  have hlit : S.inv π (.lit 1) ∧ S.bud π (.lit 1) = 0 := ⟨trivial, rfl⟩
  have key : ∀ lo' hi', hi' - lo' ≤ (hi - lo + 1) / 2 →
      S.inv π (rangeSt (fun f => St.lit (S.factor0 v args f)) (.rng0 v args) lo' hi') ∧
      S.bud π (rangeSt (fun f => St.lit (S.factor0 v args f)) (.rng0 v args) lo' hi') + π.ℓ ≤
        π.ℓ * Nat.clog 2 (hi - lo) + 0 :=
    fun lo' hi' h => range_step _ _ hL h hlit hmk hmkR
  simp only [Setup.gen]
  split_ifs
  · exact key _ _ (by omega)
  · exact key _ _ (by omega)

/-- An entry of the first clique. -/
theorem prod_ent0 (π : BudPar) (hD0 : ∀ v, S.nFac0 v ≤ 2 ^ π.D0) {v args : ℕ} (b : ℕ) :
    S.inv π (S.gen.child (.ent [] v args) b) ∧
      S.bud π (S.gen.child (.ent [] v args) b) + π.ℓ ≤ S.bud π (.ent [] v args) := by
  have hmk : ∀ f, S.inv π ((fun f => St.lit (S.factor0 v args f)) f) ∧
      S.bud π ((fun f => St.lit (S.factor0 v args f)) f) ≤ 0 := fun f => ⟨trivial, le_rfl⟩
  have hmkR : ∀ a b, 2 ≤ b - a → S.inv π (.rng0 v args a b) ∧
      S.bud π (.rng0 v args a b) ≤ π.ℓ * Nat.clog 2 (b - a) + 0 := fun a b h => ⟨h, le_rfl⟩
  have hlit : S.inv π (.lit 1) ∧ S.bud π (.lit 1) = 0 := ⟨trivial, rfl⟩
  have hcl : Nat.clog 2 (max (S.nFac0 v) 2) ≤ π.D0 + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    have := hD0 v
    have : 1 ≤ 2 ^ π.D0 := Nat.one_le_two_pow
    omega
  have key : ∀ lo' hi', hi' - lo' ≤ (max (S.nFac0 v) 2 + 1) / 2 →
      S.inv π (rangeSt (fun f => St.lit (S.factor0 v args f)) (.rng0 v args) lo' hi') ∧
      S.bud π (rangeSt (fun f => St.lit (S.factor0 v args f)) (.rng0 v args) lo' hi') + π.ℓ ≤
        π.ℓ * Nat.clog 2 (max (S.nFac0 v) 2) + 0 :=
    fun lo' hi' h => range_step _ _ (le_max_right _ _) h hlit hmk hmkR
  have hb : S.bud π (.ent [] v args) = π.ℓ * (1 + π.D0) + trB π.ℓ π.Wm := rfl
  have hl := Nat.mul_le_mul_left π.ℓ hcl
  have h1 : π.ℓ * (1 + π.D0) = π.ℓ + π.ℓ * π.D0 := by ring
  have h2 : π.ℓ * (π.D0 + 1) = π.ℓ * π.D0 + π.ℓ := by ring
  rw [hb]
  simp only [Setup.gen]
  split_ifs
  · have := key 0 (S.nFac0 v / 2) (by omega); refine ⟨this.1, ?_⟩; omega
  · have := key (S.nFac0 v / 2) (S.nFac0 v) (by omega); refine ⟨this.1, ?_⟩; omega

/-- **The budget pays for every node.** -/
theorem budgeted (π : BudPar) (hq : S.C₀.q = 2 ^ 2 ^ π.e)
    (hΛ : ∀ a, a * 2 ^ π.e ≤ S.C₀.potential → codeWidth a ≤ π.Λ)
    (hΞ : ∀ {i : ℕ} {rest : List ℕ} (v : ℕ), S.ChainOK π.e (i :: rest) →
      S.xiWidth rest i v ≤ π.Ξ / 2 ^ (π.e - rest.length))
    (hD0 : ∀ v, S.nFac0 v ≤ 2 ^ π.D0) (hDm : ∀ k < π.e, nFac (2 ^ 2 ^ k) ≤ 2 ^ π.Dm)
    (hWm : 6 * (S.C₀.potential / 2 ^ π.e) ≤ π.Wm) :
    S.gen.Budgeted (S.inv π) π.ℓ (S.bud π) where
  sum := by
    intro st hinv hk i _
    match st, hinv, hk with
    | .cl chs, hinv, _ => exact S.sum_cl π hq hΛ hinv i
    | .ent (j :: rest) v args, hinv, _ => exact S.sum_ent π hq hΞ hDm hinv v args i
    | .tr up x y m lo hi T c, hinv, _ => exact S.sum_tr π up x y m lo hi T c i hinv
    | .ent [] _ _, _, hk | .zero, _, hk | .lit _, _, hk | .last .., _, hk | .rng .., _, hk
      | .rng0 .., _, hk | .trm .., _, hk | .trr .., _, hk =>
      exact absurd hk (by simp [Setup.gen])
  prod := by
    intro st hinv hk
    match st, hinv, hk with
    | .last chs j, hinv, _ =>
      exact ⟨hinv, hinv, by simp only [Setup.gen, bud]; omega, by simp only [Setup.gen, bud]; omega⟩
    | .ent [] v args, _, _ =>
      exact ⟨(S.prod_ent0 π hD0 0).1, (S.prod_ent0 π hD0 1).1, (S.prod_ent0 π hD0 0).2,
        (S.prod_ent0 π hD0 1).2⟩
    | .rng (j :: rest) v args ξ lo hi, hinv, _ =>
      exact ⟨(S.prod_rng π hq hWm hinv.1 hinv.2 0).1, (S.prod_rng π hq hWm hinv.1 hinv.2 1).1,
        (S.prod_rng π hq hWm hinv.1 hinv.2 0).2, (S.prod_rng π hq hWm hinv.1 hinv.2 1).2⟩
    | .rng [] .., hinv, _ => exact hinv.elim
    | .rng0 v args lo hi, hinv, _ =>
      exact ⟨(S.prod_rng0 π hinv 0).1, (S.prod_rng0 π hinv 1).1, (S.prod_rng0 π hinv 0).2,
        (S.prod_rng0 π hinv 1).2⟩
    | .trm up x y m lo pos hi t T₁ T₂ c₁ c₀ c₂, hinv, _ =>
      refine ⟨hinv.1, hinv.2, ?_, ?_⟩
      · change trB π.ℓ _ + π.ℓ ≤ 2 * π.ℓ + trB π.ℓ _
        have := trB_mono π.ℓ _ _ (le_max_left (tWt (srcSub up x y m lo pos) T₁)
          (tWt (srcSub up x y m (pos + 1) hi) T₂))
        omega
      · change π.ℓ + trB π.ℓ _ + π.ℓ ≤ 2 * π.ℓ + trB π.ℓ _
        have := trB_mono π.ℓ _ _ (le_max_right (tWt (srcSub up x y m lo pos) T₁)
          (tWt (srcSub up x y m (pos + 1) hi) T₂))
        omega
    | .trr up x y m pos hi t T₂ c₀ c₂, hinv, _ =>
      refine ⟨trivial, hinv, ?_, ?_⟩
      · change 0 + π.ℓ ≤ π.ℓ + trB π.ℓ _
        omega
      · change trB π.ℓ _ + π.ℓ ≤ π.ℓ + trB π.ℓ _
        omega
    | .ent (j :: rest) v args, _, hk =>
      exfalso
      simp only [Setup.gen] at hk
      split at hk
      · cases hk
      · split_ifs at hk
    | .cl chs, _, hk =>
      exfalso
      simp only [Setup.gen] at hk
      split_ifs at hk
    | .tr .., _, hk =>
      exfalso
      simp only [Setup.gen] at hk
      split_ifs at hk
    | .zero, _, hk | .lit _, _, hk => exact absurd hk (by simp [Setup.gen])

end Setup

/-! ### Asymptotics -/

theorem two_pow_cube_le : ∀ e, 6 ≤ e → 216 * (2 ^ e) ^ 3 ≤ 2 ^ 2 ^ e := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => norm_num
  | succ e he ih =>
    have h8 : 8 ≤ 2 ^ 2 ^ e := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ 2 ^ e := Nat.pow_le_pow_right (by norm_num)
          (by calc 3 ≤ 2 ^ 2 := by norm_num
                _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega))
    calc 216 * (2 ^ (e + 1)) ^ 3 = 8 * (216 * (2 ^ e) ^ 3) := by ring
      _ ≤ 2 ^ 2 ^ e * 2 ^ 2 ^ e := Nat.mul_le_mul h8 ih
      _ = 2 ^ 2 ^ (e + 1) := by rw [← pow_add, pow_succ, mul_two]

theorem nFac_mono {a b : ℕ} (h : a ≤ b) : nFac a ≤ nFac b := by
  unfold nFac; gcongr

theorem le_of_sq_le_sq' {a b : ℕ} (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  (Nat.pow_le_pow_iff_left (by norm_num)).mp h

/-! #### The five parts of the budget, times `⌊√ log s⌋` -/

theorem part_desc {e L R q₀ s fw ℓ C₁ : ℕ} (he : e ≤ L) (hR : R ≤ L) (hfw : fw ≤ 11 * L)
    (hℓ : ℓ ≤ 2 * C₁ * L) (hLq : L ^ 3 ≤ q₀) (hq3 : q₀ ^ 3 ≤ s) (hqs : q₀ ≤ s) :
    e * (2 * q₀ ^ 2 * fw + ℓ) * R ≤ (22 + 2 * C₁) * s :=
  calc e * (2 * q₀ ^ 2 * fw + ℓ) * R ≤ L * (2 * q₀ ^ 2 * (11 * L) + 2 * C₁ * L) * L := by gcongr
    _ = L ^ 3 * (22 * q₀ ^ 2 + 2 * C₁) := by ring
    _ ≤ q₀ * (22 * q₀ ^ 2 + 2 * C₁) := Nat.mul_le_mul_right _ hLq
    _ = 22 * q₀ ^ 3 + 2 * C₁ * q₀ := by ring
    _ ≤ 22 * s + 2 * C₁ * s := by gcongr
    _ = (22 + 2 * C₁) * s := by ring

theorem part_sqrt {x R L X Φ₀ s cA c d : ℕ} (hx : x ^ 2 ≤ c * X) (hR : R ^ 2 ≤ L)
    (hXL : X * L ≤ 6 * Φ₀) (hΦ : Φ₀ ≤ 64 * (cA * s) ^ 2) (hcd : c * 384 ≤ d ^ 2) :
    x * R ≤ d * cA * s := by
  apply le_of_sq_le_sq'
  calc (x * R) ^ 2 = x ^ 2 * R ^ 2 := by ring
    _ ≤ (c * X) * L := Nat.mul_le_mul hx hR
    _ = c * (X * L) := by ring
    _ ≤ c * (6 * (64 * (cA * s) ^ 2)) := Nat.mul_le_mul_left _
        (hXL.trans (Nat.mul_le_mul_left _ hΦ))
    _ = (c * 384) * (cA * s) ^ 2 := by ring
    _ ≤ d ^ 2 * (cA * s) ^ 2 := by gcongr
    _ = (d * cA * s) ^ 2 := by ring

theorem part_prod {ℓ D0 Dm e R L C₁ s : ℕ} (hℓ : ℓ ≤ 2 * C₁ * L) (hD0 : D0 ≤ (3 * C₁ + 8) * L)
    (hDm : Dm ≤ 6 * L) (he : e ≤ L) (hR : R ≤ L) (hL1 : 1 ≤ L) (hL4 : L ^ 4 ≤ s) :
    (2 * ℓ + ℓ * (1 + D0) + e * (ℓ * (1 + Dm))) * R ≤ 2 * C₁ * (3 * C₁ + 18) * s := by
  have h1 : 1 + D0 ≤ (3 * C₁ + 9) * L := by nlinarith
  have h2 : 1 + Dm ≤ 7 * L := by omega
  have h3 : 2 ≤ 2 * L := by omega
  calc (2 * ℓ + ℓ * (1 + D0) + e * (ℓ * (1 + Dm))) * R
      ≤ (2 * L * (2 * C₁ * L) + 2 * C₁ * L * ((3 * C₁ + 9) * L) +
          L * (2 * C₁ * L * (7 * L))) * L := by gcongr
    _ = (4 * C₁ * L ^ 2 + 2 * C₁ * (3 * C₁ + 9) * L ^ 2 + 14 * C₁ * L ^ 3) * L := by ring
    _ ≤ (4 * C₁ * L ^ 3 + 2 * C₁ * (3 * C₁ + 9) * L ^ 3 + 14 * C₁ * L ^ 3) * L := by
        have : L ^ 2 ≤ L ^ 3 := Nat.pow_le_pow_right hL1 (by norm_num)
        gcongr
    _ = 2 * C₁ * (3 * C₁ + 18) * L ^ 4 := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hL4

theorem part_tr {ℓ Wm R L s cA c' C₁ q₀ : ℕ} (hWR : Wm * R ^ 2 ≤ (48 * cA * s) ^ 2)
    (hsz : Nat.size Wm ≤ (4 + c') * L) (hℓ : ℓ ≤ 2 * C₁ * L) (hR : R ≤ L) (hL1 : 1 ≤ L)
    (hLq : L ^ 3 ≤ q₀) (hqs : q₀ ≤ s) :
    trB ℓ Wm * R ≤ 16128 * cA * s + (5 + c') * (26 + 4 * c' + 6 * C₁) * s := by
  have hT := trB_le_real ℓ Wm
  have hR0 : (0 : ℝ) ≤ R := Nat.cast_nonneg _
  have hsqrt : Real.sqrt Wm * R ≤ 48 * cA * s := by
    have h1 : ((Wm * R ^ 2 : ℕ) : ℝ) ≤ ((48 * cA * s) ^ 2 : ℕ) := by exact_mod_cast hWR
    have h2 := Real.sqrt_le_sqrt h1
    push_cast at h2
    rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq hR0, Real.sqrt_sq (by positivity)] at h2
    exact h2
  have hszR : ((Nat.size Wm : ℝ) + 1) * (4 * Nat.size Wm + 10 + 3 * ℓ) * R ≤
      (5 + c') * (26 + 4 * c' + 6 * C₁) * s := by
    have h1 : (Nat.size Wm + 1) * (4 * Nat.size Wm + 10 + 3 * ℓ) * R ≤
        (5 + c') * (26 + 4 * c' + 6 * C₁) * s := by
      have ha : Nat.size Wm + 1 ≤ (5 + c') * L := by nlinarith
      have hb : 4 * Nat.size Wm + 10 + 3 * ℓ ≤ (26 + 4 * c' + 6 * C₁) * L := by nlinarith
      calc (Nat.size Wm + 1) * (4 * Nat.size Wm + 10 + 3 * ℓ) * R
          ≤ ((5 + c') * L) * ((26 + 4 * c' + 6 * C₁) * L) * L := by gcongr
        _ = (5 + c') * (26 + 4 * c' + 6 * C₁) * L ^ 3 := by ring
        _ ≤ (5 + c') * (26 + 4 * c' + 6 * C₁) * s := Nat.mul_le_mul_left _ (hLq.trans hqs)
    exact_mod_cast h1
  have : (trB ℓ Wm : ℝ) * R ≤ 16128 * cA * s + (5 + c') * (26 + 4 * c' + 6 * C₁) * s :=
    calc (trB ℓ Wm : ℝ) * R ≤ (336 * Real.sqrt Wm +
          ((Nat.size Wm : ℝ) + 1) * (4 * Nat.size Wm + 10 + 3 * ℓ)) * R :=
          mul_le_mul_of_nonneg_right hT hR0
      _ = 336 * (Real.sqrt Wm * R) +
          ((Nat.size Wm : ℝ) + 1) * (4 * Nat.size Wm + 10 + 3 * ℓ) * R := by ring
      _ ≤ 336 * (48 * cA * s) + (5 + c') * (26 + 4 * c' + 6 * C₁) * s := by gcongr
      _ = 16128 * cA * s + (5 + c') * (26 + 4 * c' + 6 * C₁) * s := by ring
  exact_mod_cast this

theorem clog_D0 {s L C₁ V M : ℕ} (hsL' : s < 2 ^ (L + 1)) (hL1 : 1 ≤ L) (hsC : C₁ ≤ s)
    (hV : V ≤ (s + 2) ^ C₁) (hM : M ≤ C₁ * (s + 1)) : Nat.clog 2 (1 + V + M) ≤
        (3 * C₁ + 8) * L := by
  apply Nat.clog_le_of_le_pow
  have hs2 : s + 2 ≤ 2 ^ (L + 2) := by rw [pow_succ, pow_succ] at *; omega
  have hb : (s + 2) ^ (C₁ + 2) ≤ 2 ^ ((L + 2) * (C₁ + 2)) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left hs2 _
  have h1 : 1 ≤ (s + 2) ^ (C₁ + 2) := Nat.one_le_pow _ _ (by omega)
  have h2 : V ≤ (s + 2) ^ (C₁ + 2) :=
    hV.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have h3 : M ≤ (s + 2) ^ (C₁ + 2) :=
    calc M ≤ C₁ * (s + 1) := hM
      _ ≤ (s + 2) * (s + 2) := Nat.mul_le_mul (by omega) (by omega)
      _ = (s + 2) ^ 2 := by ring
      _ ≤ (s + 2) ^ (C₁ + 2) := Nat.pow_le_pow_right (by omega) (by omega)
  have h4 : 2 + (L + 2) * (C₁ + 2) ≤ (3 * C₁ + 8) * L := by
    have := Nat.mul_le_mul_left C₁ hL1
    nlinarith
  have h5 : 1 + V + M ≤ 4 * 2 ^ ((L + 2) * (C₁ + 2)) := by omega
  calc 1 + V + M ≤ 4 * 2 ^ ((L + 2) * (C₁ + 2)) := h5
    _ = 2 ^ (2 + (L + 2) * (C₁ + 2)) := by rw [pow_add]; norm_num
    _ ≤ 2 ^ ((3 * C₁ + 8) * L) := Nat.pow_le_pow_right (by norm_num) h4

theorem clog_Dm {e h L q₀ : ℕ} (hh : 2 ^ e = h) (hq₀ : 2 ^ h = q₀) (hq1 : 1 ≤ q₀) (hLh : h ≤ L) :
    Nat.clog 2 (nFac (2 ^ 2 ^ e)) ≤ 6 * L := by
  apply Nat.clog_le_of_le_pow
  have hq4 : nFac (2 ^ 2 ^ e) ≤ 4 * q₀ ^ 4 := by
    rw [hh, hq₀]
    unfold nFac
    have h1 : q₀ ≤ q₀ ^ 4 := Nat.le_self_pow (by norm_num) q₀
    have h2 : q₀ * q₀ ≤ q₀ ^ 4 := by
      rw [← sq]; exact Nat.pow_le_pow_right hq1 (by norm_num)
    omega
  have hh1 : 1 ≤ h := hh ▸ Nat.one_le_two_pow
  calc nFac (2 ^ 2 ^ e) ≤ 4 * q₀ ^ 4 := hq4
    _ = 2 ^ (2 + 4 * h) := by rw [pow_add, pow_mul', hq₀]; norm_num
    _ ≤ 2 ^ (6 * L) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem size_Wm {Wm cA s L : ℕ} (hW6 : Wm ≤ 384 * cA ^ 2 * s ^ 2) (hsL' : s < 2 ^ (L + 1))
    (hL1 : 1 ≤ L) : Nat.size Wm ≤ (4 + Nat.size (384 * cA ^ 2)) * L := by
  have hlt : 384 * cA ^ 2 * s ^ 2 < 2 ^ Nat.size (384 * cA ^ 2) * 2 ^ (2 * (L + 1)) := by
    apply Nat.mul_lt_mul'' (Nat.lt_size_self _)
    rw [pow_mul']; exact Nat.pow_lt_pow_left hsL' (by norm_num)
  have : Nat.size Wm ≤ Nat.size (384 * cA ^ 2) + 2 * (L + 1) := by
    rw [Nat.size_le, pow_add]; omega
  have := Nat.mul_le_mul_left (Nat.size (384 * cA ^ 2)) hL1
  nlinarith

end Cslib.Complexity.NtimeDspace.Cube
