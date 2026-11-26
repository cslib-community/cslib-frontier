/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate (Mathlib Data/List)

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Function.Basic

/-!
# Common refinement of two factorisations of a word

Two sequences of words have the same concatenation if and only if there is a matrix of words with
staircase support (`Stair`) whose rows concatenate to the first sequence and whose columns
concatenate to the second (`IsRef`); moreover the matrix is unique.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Tape.Refine`.

## Main definitions

* `List.StairRefinement.cat`: concatenation of a `Fin K`-indexed sequence of words.
* `List.StairRefinement.Stair`: staircase-support predicate on a word matrix.
* `List.StairRefinement.IsRef`: common refinement witnessing equal concatenations.

## Main results

* `List.StairRefinement.IsRef.cat_eq`: rows and columns of a refinement have the same
  concatenation.
* `List.StairRefinement.IsRef.unique`: uniqueness of the common refinement matrix.
* `List.StairRefinement.IsRef.exists`: existence of a common refinement given equal concatenations.
* `List.StairRefinement.cat_add`, `List.StairRefinement.sum_length_cat`,
  `List.StairRefinement.length_le_cat`: concatenations of a sequence split in two, and lengths.
-/

public section

namespace List.StairRefinement

variable {Γ : Type*} {K : ℕ}

/-- Concatenation of a `Fin K`-indexed sequence of words. -/
@[expose] def cat (A : Fin K → List Γ) : List Γ := (List.ofFn A).flatten

theorem cat_succ (A : Fin (K + 1) → List Γ) : cat A = A 0 ++ cat fun i => A i.succ := by
  simp [cat, List.ofFn_succ]

theorem cat_eq_nil {A : Fin K → List Γ} : cat A = [] ↔ ∀ i, A i = [] := by
  induction K with
  | zero => simp [cat]
  | succ K ih =>
    rw [cat_succ, List.append_eq_nil_iff, ih, Fin.forall_fin_succ]

theorem cat_eq_cons {A : Fin K → List Γ} {a : Γ} {W : List Γ} (h : cat A = a :: W) :
    ∃ i l, (∀ j < i, A j = []) ∧ A i = a :: l ∧ cat (Function.update A i l) = W := by
  induction K with
  | zero => simp [cat] at h
  | succ K ih =>
    rw [cat_succ] at h
    rcases hA : A 0 with _ | ⟨b, l⟩
    · rw [hA, List.nil_append] at h
      obtain ⟨i, l, h1, h2, h3⟩ := ih h
      refine ⟨i.succ, l, Fin.cases (fun _ => hA) fun j hj => h1 j (by simpa using hj), h2, ?_⟩
      rw [cat_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm, hA, List.nil_append, ← h3]
      congr 1
      funext j
      simp only [Function.update_apply, (Fin.succ_injective _).eq_iff]
    · rw [hA, List.cons_append, List.cons.injEq] at h
      refine ⟨0, l, fun j hj => absurd hj (Fin.not_lt_zero j), by rw [hA, h.1], ?_⟩
      rw [cat_succ, Function.update_self, ← h.2]
      congr 2

theorem cat_of_cons {A : Fin K → List Γ} {a : Γ} {i : Fin K} {l : List Γ}
    (h1 : ∀ j < i, A j = []) (h2 : A i = a :: l) :
    cat A = a :: cat (Function.update A i l) := by
  induction K with
  | zero => exact i.elim0
  | succ K ih =>
    rw [cat_succ, cat_succ]
    rcases eq_or_ne i 0 with rfl | e
    · rw [h2, Function.update_self, List.cons_append]
      congr 3
    · obtain ⟨i', rfl⟩ := Fin.exists_succ_eq.2 e
      rw [Function.update_of_ne (Ne.symm e), h1 0 (Fin.succ_pos i'),
        List.nil_append, List.nil_append,
        ih (A := fun j => A j.succ) (i := i') (fun j hj => h1 _ (by simpa using hj)) h2]
      exact congrArg (a :: cat ·) (funext fun j => by simp [Function.update_apply])

/-- Staircase support condition on a matrix of words. -/
@[expose] def Stair (X : Fin K → Fin K → List Γ) : Prop :=
  ∀ a a' b b', X a b ≠ [] → X a' b' ≠ [] → a < a' → b ≤ b'

/-- `X` is a common refinement of `A` (rows) and `B` (columns). -/
structure IsRef (A B : Fin K → List Γ) (X : Fin K → Fin K → List Γ) : Prop where
  /-- Non-empty entries form a weakly increasing staircase. -/
  stair : Stair X
  /-- Each row `a` concatenates to `A a`. -/
  row : ∀ a, cat (X a) = A a
  /-- Each column `b` concatenates to `B b`. -/
  col : ∀ b, cat (fun a => X a b) = B b

private def upd (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    Fin K → Fin K → List Γ :=
  fun a' b' => if a' = a ∧ b' = b then l else X a' b'

private theorem upd_row (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    upd X a b l a = Function.update (X a) b l := by
  funext b'
  rcases eq_or_ne b' b with rfl | e <;> simp [upd, *]

private theorem upd_row_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {a' : Fin K}
    (h : a' ≠ a) : upd X a b l a' = X a' := by
  funext b'; simp [upd, h]

private theorem upd_col (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) :
    (fun a' => upd X a b l a' b) = Function.update (fun a' => X a' b) a l := by
  funext a'
  rcases eq_or_ne a' a with rfl | e <;> simp [upd, *]

private theorem upd_col_ne (X : Fin K → Fin K → List Γ) (a b : Fin K) (l : List Γ) {b' : Fin K}
    (h : b' ≠ b) : (fun a' => upd X a b l a' b') = fun a' => X a' b' := by
  funext a'; simp [upd, h]

/-- Peel the first letter from a common refinement. -/
private theorem IsRef.first {A B : Fin K → List Γ} {X : Fin K → Fin K → List Γ} (h : IsRef A B X)
    {a : Fin K} {c : Γ} {l : List Γ} (h1 : ∀ j < a, A j = []) (h2 : A a = c :: l) :
    ∃ b x m, X a b = c :: x ∧ (∀ j < b, B j = []) ∧ B b = c :: m ∧
      IsRef (Function.update A a l) (Function.update B b m) (upd X a b x) := by
  obtain ⟨b, x, hx1, hx2, hx3⟩ := cat_eq_cons ((h.row a).trans h2)
  have hrow (j : Fin K) (hj : j < a) (b' : Fin K) : X j b' = [] :=
    cat_eq_nil.1 ((h.row j).trans (h1 j hj)) b'
  have hcol (j : Fin K) (hj : j < b) (a' : Fin K) : X a' j = [] := by
    rcases lt_trichotomy a' a with h' | rfl | h'
    · exact hrow a' h' j
    · exact hx1 j hj
    · by_contra hne
      exact absurd (h.stair a a' b j (by simp [hx2]) hne h') (not_le.2 hj)
  have hB := cat_of_cons (A := fun a' => X a' b) (i := a) (l := x)
    (fun j hj => hrow j hj b) hx2
  rw [h.col b] at hB
  refine ⟨b, x, _, hx2, fun j hj => (h.col j).symm.trans (cat_eq_nil.2 (hcol j hj)), hB,
    ?_, fun a' => ?_, fun b' => ?_⟩
  · intro a₁ a₂ b₁ b₂ n1 n2 hlt
    have key (a' b' : Fin K) (hn : upd X a b x a' b' ≠ []) : X a' b' ≠ [] := by
      by_cases e : a' = a ∧ b' = b
      · obtain ⟨rfl, rfl⟩ := e; simp [hx2]
      · simpa [upd, e] using hn
    exact h.stair _ _ _ _ (key _ _ n1) (key _ _ n2) hlt
  · rcases eq_or_ne a' a with rfl | e
    · rw [upd_row, Function.update_self, hx3]
    · rw [upd_row_ne _ _ _ _ e, Function.update_of_ne e, h.row]
  · rcases eq_or_ne b' b with rfl | e
    · rw [upd_col, Function.update_self]
    · rw [upd_col_ne _ _ _ _ e, Function.update_of_ne e, h.col]

theorem IsRef.cat_eq {A B : Fin K → List Γ} {X : Fin K → Fin K → List Γ} (h : IsRef A B X) :
    cat A = cat B := by
  generalize hW : cat A = W
  induction W generalizing A B X with
  | nil =>
    rw [eq_comm, cat_eq_nil]
    rw [cat_eq_nil] at hW
    exact fun b => (h.col b).symm.trans
      (cat_eq_nil.2 fun a => cat_eq_nil.1 ((h.row a).trans (hW a)) b)
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, x, m, -, hb, hB, href⟩ := h.first h1 h2
    rw [cat_of_cons hb hB, ← ih href h3]

theorem IsRef.unique {A B : Fin K → List Γ} {X Y : Fin K → Fin K → List Γ} (h : IsRef A B X)
    (h' : IsRef A B Y) : X = Y := by
  generalize hW : cat A = W
  induction W generalizing A B X Y with
  | nil =>
    rw [cat_eq_nil] at hW
    funext a b
    rw [cat_eq_nil.1 ((h.row a).trans (hW a)) b, cat_eq_nil.1 ((h'.row a).trans (hW a)) b]
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, x, m, hx, hb, hB, href⟩ := h.first h1 h2
    obtain ⟨b', y, m', hy, hb', hB', href'⟩ := h'.first h1 h2
    obtain rfl : b = b' := le_antisymm
      (not_lt.1 fun e => by simp [hb b' e] at hB')
      (not_lt.1 fun e => by simp [hb' b e] at hB)
    obtain rfl : m = m' := by simpa [hB] using hB'
    have hrec := ih href href' h3
    funext a' b'
    have h4 := congrFun (congrFun hrec a') b'
    by_cases e : a' = a ∧ b' = b
    · obtain ⟨rfl, rfl⟩ := e
      simp only [upd, and_self, ite_true] at h4
      rw [hx, hy, h4]
    · simpa [upd, e] using h4

theorem IsRef.exists {A B : Fin K → List Γ} (h : cat A = cat B) : ∃ X, IsRef A B X := by
  generalize hW : cat A = W
  induction W generalizing A B with
  | nil =>
    have hB : cat B = [] := h ▸ hW
    rw [cat_eq_nil] at hW hB
    exact ⟨fun _ _ => [], fun _ _ _ _ hne => absurd rfl hne,
      fun a => (cat_eq_nil.2 fun _ => rfl).trans (hW a).symm,
      fun b => (cat_eq_nil.2 fun _ => rfl).trans (hB b).symm⟩
  | cons c W ih =>
    obtain ⟨a, l, h1, h2, h3⟩ := cat_eq_cons hW
    obtain ⟨b, m, g1, g2, g3⟩ := cat_eq_cons (h ▸ hW)
    obtain ⟨X, hX⟩ := ih (h3.trans g3.symm) h3
    have hrow (j : Fin K) (hj : j < a) (b' : Fin K) : X j b' = [] :=
      cat_eq_nil.1 ((hX.row j).trans (by rw [Function.update_of_ne hj.ne, h1 j hj])) b'
    have hcol (j : Fin K) (hj : j < b) (a' : Fin K) : X a' j = [] :=
      cat_eq_nil.1 ((hX.col j).trans (by rw [Function.update_of_ne hj.ne, g1 j hj])) a'
    refine ⟨upd X a b (c :: X a b), ?_, fun a' => ?_, fun b' => ?_⟩
    · have key (a' b' : Fin K) (hn : upd X a b (c :: X a b) a' b' ≠ []) :
          ((a' = a ∧ b' = b) ∨ X a' b' ≠ []) ∧ a ≤ a' ∧ b ≤ b' := by
        by_cases e : a' = a ∧ b' = b
        · obtain ⟨rfl, rfl⟩ := e
          exact ⟨Or.inl ⟨rfl, rfl⟩, le_rfl, le_rfl⟩
        · have hne : X a' b' ≠ [] := by simpa [upd, e] using hn
          exact ⟨Or.inr hne, not_lt.1 fun hl => hne (hrow _ hl _),
            not_lt.1 fun hl => hne (hcol _ hl _)⟩
      intro a₁ a₂ b₁ b₂ n1 n2 hlt
      rcases (key a₁ b₁ n1).1 with ⟨rfl, rfl⟩ | m1
      · exact (key _ _ n2).2.2
      · rcases (key a₂ b₂ n2).1 with ⟨rfl, rfl⟩ | m2
        · exact absurd (key _ _ n1).2.1 (not_le.2 hlt)
        · exact hX.stair _ _ _ _ m1 m2 hlt
    · rcases eq_or_ne a' a with rfl | e
      · rw [upd_row, cat_of_cons
          (fun j hj => (Function.update_of_ne hj.ne _ _).trans (hcol j hj a'))
          (Function.update_self b (c :: X a' b) (X a')), Function.update_idem,
          Function.update_eq_self, hX.row, Function.update_self, h2]
      · rw [upd_row_ne _ _ _ _ e, hX.row, Function.update_of_ne e]
    · rcases eq_or_ne b' b with rfl | e
      · rw [upd_col, cat_of_cons
          (fun j hj => (Function.update_of_ne hj.ne _ _).trans (hrow j hj b'))
          (Function.update_self a (c :: X a b') fun a' => X a' b'), Function.update_idem,
          Function.update_eq_self (f := fun a' => X a' b') a, hX.col, Function.update_self, g2]
      · rw [upd_col_ne _ _ _ _ e, hX.col, Function.update_of_ne e]

section Lengths

variable {K' : ℕ}

/-- The concatenation of `K + K'` words is that of the first `K` and then of the last `K'`. -/
theorem cat_add (X : Fin (K + K') → List Γ) :
    cat X = cat (fun κ => X (Fin.castAdd K' κ)) ++ cat fun κ => X (Fin.natAdd K κ) := by
  simp only [cat]
  rw [List.ofFn_add, List.flatten_append]
  rfl

/-- The length of a concatenation is the sum of the lengths. -/
theorem sum_length_cat (X : Fin K → List Γ) : ∑ b, (X b).length = (cat X).length := by
  rw [cat, List.length_flatten, List.map_ofFn, List.sum_ofFn]
  rfl

/-- Every word of a sequence is at most as long as the concatenation. -/
theorem length_le_cat (X : Fin K → List Γ) (b : Fin K) : (X b).length ≤ (cat X).length :=
  (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)).trans_eq
    (sum_length_cat X)

/-- Staircase support is decidable. -/
instance (X : Fin K → Fin K → List Γ) : Decidable (Stair X) :=
  inferInstanceAs (Decidable (∀ a a' b b', X a b ≠ [] → X a' b' ≠ [] → a < a' → b ≤ b'))

end Lengths

end List.StairRefinement
