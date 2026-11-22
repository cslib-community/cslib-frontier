/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Merge

/-!
# The chain of cliques along a path (§6.2)

* `Clique.recast`: the same clique on `Fin n` for `n = q`.
* `colTable`: the table of a column of the column clique written directly, without the transposed
  clique: a sum over the copies held in the column, with the old tables at their own nodes.
  `colChild_T`: it is the table of `colChild`, and `colChild_a`: the budgets of `colChild` are the
  column budgets (both for even grades, where `(-k) / 2 = -(k / 2)`).
* `choiceCode`/`decodeChoice`: a choice is written in one field of `fw` bits for each grade and each
  split, at the quadruple `(A, A', B, B')` of its rectangle (fields of non-rectangles are `0`); a
  field (`choiceDigit`) holds `z + 2^(fw-1)` for `z ∈ [-2^(fw-1), 2^(fw-1))`.
* `orientRow`: the orientation of a choice of grades, rows unless the column potential is smaller.
* `mergeStep`: the child of a clique on `g × g` nodes at a choice, in the orientation of its grades.
* `chainAt`: the clique at a path of choice codes (latest first), from a first clique.
* `value_childAt`: the value of a clique is the sum over the valid choice codes of the values of its
  children (Lemma 6.2 through the codes).
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

/-! ### Recasting -/

/-- The same clique on `Fin n`. -/
def Clique.recast (C : Clique) (n : ℕ) (h : C.q = n) : Clique where
  q := n
  a := fun u v => C.a (Fin.cast h.symm u) (Fin.cast h.symm v)
  T := fun v Θ => C.T (Fin.cast h.symm v) fun u => Θ (Fin.cast h u)

theorem Clique.value_recast (C : Clique) (n : ℕ) (h : C.q = n) : (C.recast n h).value =
    C.value := by
  subst h; rfl

/-! ### The column clique, directly -/

variable {g : ℕ}

/-- The settings of the old nodes of column `B`. -/
def colSettings (a : Fin (g * g) → Fin (g * g) → ℕ) (B : Fin g) :
    Finset (Fin g → Fin (g * g) → Label) :=
  Fintype.piFinset fun A => Fintype.piFinset fun u =>
    if u = node A B then {((0 : Multiset ℕ), (0 : Multiset ℕ))} else labelsEq
        (budget a (node A B) u)

/-- The rectangle factor in the table of column `B` (column cut of Corollary 5.5): with the left
column `B₁` it holds `x = (A₁, B₁)` and `u = (A₂, B₁)`, with the right column `y = (A₁, B₂)` and
`v = (A₂, B₂)`. -/
noncomputable def colPsi (a : Fin (g * g) → Fin (g * g) → ℕ) (ι : Rect g → ℤ × ℤ) (B : Fin g)
    (Θ : Fin g → Label) (ξ : Fin g → Fin (g * g) → Label) (r : Rect g) : ℤ :=
  let A₁ := r.1.1.1; let A₂ := r.1.1.2; let B₁ := r.1.2.1; let B₂ := r.1.2.2
  let k := (ι r).1; let c := (ι r).2
  let H : ℤ := diagWt a r
  if B = B₁ then
    let m := unpack (packL g) (Θ B₂) (rStream g A₁ A₂)
    if (labelWt m : ℤ) ≤ H - k / 2 then
      (nUp (ξ A₁ (node A₂ B₂)) (swapLabel (ξ A₂ (node A₁ B₂))) m).coeff (-k - c) else 0
  else if B = B₂ then
    let m := unpack (packL g) (Θ B₁) (rStream g A₁ A₂)
    if (labelWt m : ℤ) ≤ H - k / 2 then
      (nDown (ξ A₁ (node A₂ B₁)) (swapLabel (ξ A₂ (node A₁ B₁))) m).coeff c else 0
  else 1

/-- **The table of column `B`** of the column clique, directly. -/
noncomputable def colTable (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (B : Fin g)
    (Θ : Fin g → Label) : ℤ :=
  if ∀ B', B' ≠ B → validLabel (packL g) (Θ B') then
    ∑ ξ ∈ colSettings a B,
      (∏ A, T (node A B) (ξ A)) *
      (∏ A, ∏ A', if A < A' ∧ ξ A (node A' B) ≠ ξ A' (node A B) then 0 else 1) *
      (∏ B', ∏ A, if B' ≠ B ∧ ξ A (node A B') ≠ unpack (packL g) (Θ B') (vStream A) then 0 else 1) *
      ∏ r : Rect g, colPsi a ι B Θ ξ r
  else 0

/-! #### Transposition bookkeeping -/

private theorem chn_node_lt_iff {A B A' B' : Fin g} :
    node A B < node A' B' ↔ A < A' ∨ (A = A' ∧ B < B') := by
  rcases lt_trichotomy A A' with h | rfl | h
  · simp [h, node_lt_node h]
  · simp only [lt_irrefl, false_or, true_and]
    rw [Fin.lt_def, Fin.lt_def]
    change A.val * g + B.val < A.val * g + B'.val ↔ B.val < B'.val
    omega
  · have h' := node_lt_node h B' B
    simp only [lt_asymm h, h.ne', false_and, or_false, iff_false]
    exact lt_asymm h'

private theorem chn_trNode_node (A B : Fin g) : trNode (node A B) = node B A := by
  have hg : 0 < g := A.pos
  have h1 : (A.val * g + B.val) % g = B.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt B.isLt]
  have h2 : (A.val * g + B.val) / g = A.val := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hg, Nat.div_eq_of_lt B.isLt, Nat.zero_add]
  unfold trNode
  congr 1
  · exact Fin.ext h1
  · exact Fin.ext h2

private theorem chn_trNode_trNode (w : Fin (g * g)) : trNode (trNode w) = w := by
  change trNode (node _ _) = w
  rw [chn_trNode_node]
  exact Fin.ext (Nat.div_add_mod' w.val g)

private theorem chn_budget_comm {n : ℕ} (a : Fin n → Fin n → ℕ) (u v : Fin n) :
    budget a u v = budget a v u := by
  simp only [budget, min_comm, max_comm]

private theorem chn_budget_of_le {n : ℕ} (a : Fin n → Fin n → ℕ) {u v : Fin n} (h : u ≤ v) :
    budget a u v = a u v := by
  simp only [budget, min_eq_left h, max_eq_right h]

private theorem chn_budget_tr (a : Fin (g * g) → Fin (g * g) → ℕ) (u v : Fin (g * g)) :
    budget (trBudget a) u v = budget a (trNode u) (trNode v) := by
  change budget a (trNode (min u v)) (trNode (max u v)) = _
  rcases le_total u v with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, chn_budget_comm]

private theorem chn_labelWt_swap (l : Label) : labelWt (swapLabel l) = labelWt l :=
  Nat.add_comm _ _

/-- The setting of the old nodes of column `B` read off a setting of the transposed row `B`: the
copy at `node A B` of the label of `{node A B, u}` is the copy at `node B A` of the transposed
pair, reversed when the order of the pair flips. -/
private def chnTr (B : Fin g) (ξ : Fin g → Fin (g * g) → Label) : Fin g → Fin (g * g) → Label :=
  fun A u =>
    if (node B A < trNode u ↔ node A B < u) then ξ A (trNode u) else swapLabel (ξ A (trNode u))

/-- The inverse of `chnTr`. -/
private def chnUntr (B : Fin g) (ξ : Fin g → Fin (g * g) → Label) : Fin g → Fin (g * g) → Label :=
  fun A w =>
    if (node B A < w ↔ node A B < trNode w) then ξ A (trNode w) else swapLabel (ξ A (trNode w))

private theorem chnTr_node (B : Fin g) (ξ : Fin g → Fin (g * g) → Label) (A X Y : Fin g) :
    chnTr B ξ A (node X Y) = if (node B A < node Y X ↔ node A B < node X Y) then ξ A (node Y X)
      else swapLabel (ξ A (node Y X)) := by
  simp only [chnTr, chn_trNode_node]

private theorem chn_untr_tr (B : Fin g) (ξ : Fin g → Fin (g * g) → Label) :
    chnUntr B (chnTr B ξ) = ξ := by
  funext A w
  simp only [chnUntr, chnTr, chn_trNode_trNode]
  split_ifs <;> rfl

private theorem chn_tr_untr (B : Fin g) (ξ : Fin g → Fin (g * g) → Label) :
    chnTr B (chnUntr B ξ) = ξ := by
  funext A u
  simp only [chnUntr, chnTr, chn_trNode_trNode]
  split_ifs <;> rfl

private theorem chn_tr_mem (a : Fin (g * g) → Fin (g * g) → ℕ) (B : Fin g)
    {ξ : Fin g → Fin (g * g) → Label} (h : ξ ∈ rowSettings (trBudget a) B) :
    chnTr B ξ ∈ colSettings a B := by
  simp only [rowSettings, colSettings, Fintype.mem_piFinset] at h ⊢
  intro A u
  have hA := h A (trNode u)
  by_cases hu : u = node A B
  · subst hu
    rw [chn_trNode_node, ite_eq_left rfl, Finset.mem_singleton] at hA
    rw [ite_eq_left rfl, Finset.mem_singleton, chnTr_node, hA]
    split_ifs <;> rfl
  · have hu' : trNode u ≠ node B
      A := fun e => hu (by rw [← chn_trNode_trNode u, e, chn_trNode_node])
    rw [ite_eq_right hu', mem_labelsEq, chn_budget_tr, chn_trNode_node, chn_trNode_trNode] at hA
    rw [ite_eq_right hu, mem_labelsEq]
    unfold chnTr
    split_ifs
    · exact hA
    · rw [chn_labelWt_swap]; exact hA

private theorem chn_untr_mem (a : Fin (g * g) → Fin (g * g) → ℕ) (B : Fin g)
    {ξ : Fin g → Fin (g * g) → Label} (h : ξ ∈ colSettings a B) :
    chnUntr B ξ ∈ rowSettings (trBudget a) B := by
  simp only [rowSettings, colSettings, Fintype.mem_piFinset] at h ⊢
  intro A w
  have hA := h A (trNode w)
  by_cases hw : w = node B A
  · subst hw
    rw [chn_trNode_node, ite_eq_left rfl, Finset.mem_singleton] at hA
    rw [ite_eq_left rfl, Finset.mem_singleton]
    simp only [chnUntr, chn_trNode_node, hA]
    split_ifs <;> rfl
  · have hw' : trNode w ≠ node A
      B := fun e => hw (by rw [← chn_trNode_trNode w, e, chn_trNode_node])
    rw [ite_eq_right hw', mem_labelsEq] at hA
    rw [ite_eq_right hw, mem_labelsEq, chn_budget_tr, chn_trNode_node]
    unfold chnUntr
    split_ifs
    · exact hA
    · rw [chn_labelWt_swap]; exact hA

private theorem chn_diagWt_tr (a : Fin (g * g) → Fin (g * g) → ℕ) (r : Rect g) :
    diagWt (trBudget a) r = diagWt a (trRect r) := by
  obtain ⟨⟨⟨B₁, B₂⟩, A₁, A₂⟩, hB, hA⟩ := r
  simp only [diagWt, trRect, trBudget, chn_trNode_node]
  rw [chn_budget_of_le a (node_lt_node hA B₁ B₂).le, chn_budget_comm a (node A₂ B₁),
    chn_budget_of_le a (node_lt_node hA B₂ B₁).le]

/-- Transposition of rectangles, as an equivalence. -/
private def chnRectEquiv : Rect g ≃ Rect g := ⟨trRect, trRect, fun _ => rfl, fun _ => rfl⟩

private theorem chn_psi (a : Fin (g * g) → Fin (g * g) → ℕ) (ι : Rect g → ℤ × ℤ)
    (hk : ∀ r, Even (ι r).1) (B : Fin g) (Θ : Fin g → Label) (ξ : Fin g → Fin (g * g) → Label)
    (r : Rect g) :
    rowPsi (trBudget a) (fun r => (-(ι (trRect r)).1, (ι (trRect r)).2)) B Θ ξ r =
      colPsi a ι B Θ (chnTr B ξ) (trRect r) := by
  have hdiv : -(ι (trRect r)).1 / 2 = -((ι (trRect r)).1 / 2) :=
    Int.neg_ediv_of_dvd (even_iff_two_dvd.mp (hk _))
  dsimp only [rowPsi, colPsi]
  rw [chn_diagWt_tr, hdiv, ← Int.sub_eq_add_neg]
  obtain ⟨⟨⟨B₁, B₂⟩, A₁, A₂⟩, hB, hA⟩ := r
  dsimp only [trRect]
  by_cases h1 : B = B₁
  · subst h1
    simp [chnTr_node, chn_node_lt_iff, hA, hB, lt_asymm hA, hA.ne, hA.ne']
    rfl
  · by_cases h2 : B = B₂
    · subst h2
      simp [h1, chnTr_node, chn_node_lt_iff, hA, lt_asymm hA, lt_asymm hB, hA.ne, hA.ne']
      rfl
    · simp [h1, h2]

/-- **The column clique has the direct column tables** (for even grades, so that
`(-k) / 2 = -(k / 2)`). -/
theorem colChild_T (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) (hk : ∀ r, Even (ι r).1)
    (B : Fin g) (Θ : Fin g → Label) : (colChild g a T ι).T B Θ = colTable a T ι B Θ := by
  change rowTable (trBudget a) (trTable T) _ B Θ = _
  unfold rowTable colTable
  by_cases hv : ∀ B', B' ≠ B → validLabel (packL g) (Θ B')
  swap
  · rw [ite_eq_right hv, ite_eq_right hv]
  rw [ite_eq_left hv, ite_eq_left hv]
  refine Finset.sum_nbij' (chnTr B) (chnUntr B) (fun ξ h => chn_tr_mem a B h)
    (fun ξ h => chn_untr_mem a B h) (fun ξ _ => chn_untr_tr B ξ) (fun ξ _ => chn_tr_untr B ξ) ?_
  intro ξ _
  congr 1
  · congr 1
    · congr 1
      · refine Finset.prod_congr rfl fun A _ => ?_
        simp only [trTable, chn_trNode_node]
        rfl
      · refine Finset.prod_congr rfl fun A _ => Finset.prod_congr rfl fun A' _ => ?_
        simp [chnTr_node, chn_node_lt_iff]
    · refine Finset.prod_congr rfl fun B' _ => Finset.prod_congr rfl fun A _ => ?_
      simp [chnTr_node, chn_node_lt_iff]
  · exact Fintype.prod_equiv chnRectEquiv _ _ fun r => chn_psi a ι hk B Θ ξ r

/-- The budgets of the column clique are the column budgets (for even grades, on pairs
`B ≤ B'`). -/
theorem colChild_a (a : Fin (g * g) → Fin (g * g) → ℕ) (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ)
    (ι : Rect g → ℤ × ℤ) (hk : ∀ r, Even (ι r).1) {B B' : Fin g} (hBB : B ≤ B') :
    (colChild g a T ι).a B B' = colBudget a (fun r => (ι r).1) B B' := by
  change rowBudget (trBudget a) _ B B' = _
  have hd : ∀ r, -(ι r).1 / 2 = -((ι r).1 / 2) := fun r =>
    Int.neg_ediv_of_dvd (even_iff_two_dvd.mp (hk r))
  unfold rowBudget colBudget
  congr 2
  · refine Finset.sum_congr rfl fun A _ => ?_
    change budget a (trNode (node B A)) (trNode (node B' A)) = _
    rw [chn_trNode_node, chn_trNode_node, chn_budget_of_le]
    rcases hBB.lt_or_eq with h | rfl
    · exact (node_lt_node_right A h).le
    · exact le_rfl
  · exact Fintype.sum_equiv chnRectEquiv _ _ fun r => by
      simp only [chn_diagWt_tr, hd, ← Int.sub_eq_add_neg]
      rfl

/-! ### Codes of choices -/

/-- The quadruple index of a rectangle. -/
def rectIdx (r : Rect g) : ℕ :=
  ((r.1.1.1.val * g + r.1.1.2.val) * g + r.1.2.1.val) * g + r.1.2.2.val

/-- The field `t` of width `fw` of a code, as an integer. -/
def field (fw i t : ℕ) : ℤ := ((i / 2 ^ (t * fw)) % 2 ^ fw : ℕ) - 2 ^ (fw - 1)

/-- The choice written in a code. -/
def decodeChoice (g fw i : ℕ) : Rect g → ℤ × ℤ := fun r =>
  (field fw i (2 * rectIdx r), field fw i (2 * rectIdx r + 1))

/-- The field `t` of the code of a choice: the grade (`t = 2 · rectIdx R`) or the split
(`t = 2 · rectIdx R + 1`) of a rectangle `R`, or `0` off the rectangles, plus `2^(fw-1)`. -/
noncomputable def choiceDigit (g fw : ℕ) (ι : Rect g → ℤ × ℤ) (t : ℕ) : ℕ :=
  ((if h : ∃ r : Rect g, 2 * rectIdx r = t then (ι h.choose).1
    else if h : ∃ r : Rect g, 2 * rectIdx r + 1 = t then (ι h.choose).2 else 0) +
    2 ^ (fw - 1)).toNat

/-- The code of a choice: the fields `choiceDigit` in base `2^fw`. -/
noncomputable def choiceCode (g fw : ℕ) (ι : Rect g → ℤ × ℤ) : ℕ :=
  ∑ t ∈ range (2 * g ^ 4), (2 ^ fw) ^ t * choiceDigit g fw ι t

/-- The width of a choice code. -/
def choiceWidth (g fw : ℕ) : ℕ := 2 * g ^ 4 * fw

/-- A code is valid: it is the code of a choice in `choices a`. -/
def ValidChoiceCode (a : Fin (g * g) → Fin (g * g) → ℕ) (fw i : ℕ) : Prop :=
  decodeChoice g fw i ∈ choices a ∧ choiceCode g fw (decodeChoice g fw i) = i

private theorem chn_lt_mul_add {x m y n : ℕ} (hx : x < m) (hy : y < n) : x * n + y < m * n :=
  calc x * n + y < x * n + n := by omega
    _ = (x + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right _ hx

private theorem chn_mul_add_inj {x y x' y' n : ℕ} (hy : y < n) (hy' : y' < n)
    (h : x * n + y = x' * n + y') : x = x' ∧ y = y' := by
  have hn : 0 < n := by omega
  have e1 : ∀ {x y : ℕ}, y < n → (x * n + y) / n = x := fun hy => by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hn, Nat.div_eq_of_lt hy, Nat.zero_add]
  have e2 : ∀ {x y : ℕ}, y < n → (x * n + y) % n = y := fun hy => by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hy]
  exact ⟨by rw [← e1 (x := x) hy, h, e1 hy'], by rw [← e2 (x := x) hy, h, e2 hy']⟩

private theorem chn_rectIdx_lt (r : Rect g) : rectIdx r < g ^ 4 := by
  have := chn_lt_mul_add (chn_lt_mul_add (chn_lt_mul_add r.1.1.1.isLt r.1.1.2.isLt)
    r.1.2.1.isLt) r.1.2.2.isLt
  unfold rectIdx
  calc _ < g * g * g * g := this
    _ = g ^ 4 := by ring

private theorem chn_rectIdx_inj {r r' : Rect g} (h : rectIdx r = rectIdx r') : r = r' := by
  obtain ⟨h1, h2⟩ := chn_mul_add_inj r.1.2.2.isLt r'.1.2.2.isLt h
  obtain ⟨h3, h4⟩ := chn_mul_add_inj r.1.2.1.isLt r'.1.2.1.isLt h1
  obtain ⟨h5, h6⟩ := chn_mul_add_inj r.1.1.2.isLt r'.1.1.2.isLt h3
  exact Subtype.ext (Prod.ext (Prod.ext (Fin.ext h5) (Fin.ext h6))
      (Prod.ext (Fin.ext h4) (Fin.ext h2)))

/-- Digits in base `b`: a number written with digits below `b` is below `b ^ n`, and its digits
are read back by division and remainder. -/
private theorem chn_digits {b : ℕ} (hb : 0 < b) (n : ℕ) : ∀ d : ℕ → ℕ, (∀ t < n, d t < b) →
    (∑ t ∈ range n, b ^ t * d t) < b ^ n ∧
      ∀ s < n, (∑ t ∈ range n, b ^ t * d t) / b ^ s % b = d s := by
  induction n with
  | zero => exact fun d _ => ⟨by simp, fun s hs => absurd hs (Nat.not_lt_zero _)⟩
  | succ n ih =>
    intro d hd
    have ih' := ih (fun t => d (t + 1)) fun t ht => hd _ (by omega)
    have e : ∑ t ∈ range (n + 1), b ^ t * d t = d 0 + b * ∑ t ∈ range n, b ^ t * d (t + 1) := by
      rw [Finset.sum_range_succ', Finset.mul_sum, pow_zero, one_mul, add_comm]
      congr 1
      refine Finset.sum_congr rfl fun t _ => ?_
      ring
    have hd0 := hd 0 (by omega)
    rw [e]
    set X := ∑ t ∈ range n, b ^ t * d (t + 1)
    refine ⟨?_, fun s hs => ?_⟩
    · calc d 0 + b * X < b + b * X := by omega
        _ = b * (X + 1) := by ring
        _ ≤ b * b ^ n := Nat.mul_le_mul_left _ ih'.1
        _ = b ^ (n + 1) := by ring
    · cases s with
      | zero => rw [pow_zero, Nat.div_one, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd0]
      | succ s =>
        rw [pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_left _ _ hb,
          Nat.div_eq_of_lt hd0, Nat.zero_add]
        exact ih'.2 s (by omega)

/-- The code of a choice is a code of width `choiceWidth g fw`, and it decodes to the choice. -/
private theorem chn_code (a : Fin (g * g) → Fin (g * g) → ℕ) (fw : ℕ) (hfw0 : 1 ≤ fw)
    (hfw : ∀ r : Rect g, 6 * diagWt a r < 2 ^ (fw - 1)) {ι : Rect g → ℤ × ℤ}
    (hι : ι ∈ choices a) :
    choiceCode g fw ι < 2 ^ choiceWidth g fw ∧ decodeChoice g fw (choiceCode g fw ι) = ι := by
  have h2 : ((2 ^ fw : ℕ) : ℤ) = 2 * (2 : ℤ) ^ (fw - 1) := by
    push_cast
    rw [← pow_succ']
    congr 1
    omega
  have hb : ∀ r, 0 ≤ (ι r).1 + (2 : ℤ) ^ (fw - 1) ∧ (ι r).1 + (2 : ℤ) ^ (fw - 1) < 2
      * 2 ^ (fw - 1) ∧
      0 ≤ (ι r).2 + (2 : ℤ) ^ (fw - 1) ∧ (ι r).2 + (2 : ℤ) ^ (fw - 1) < 2 * 2 ^ (fw - 1) := by
    intro r
    have hr := Fintype.mem_piFinset.mp hι r
    simp only [Finset.mem_product, Finset.mem_filter, Finset.mem_Icc] at hr
    have := hfw r
    have h6 : (6 * diagWt a r : ℤ) < (2 : ℤ) ^ (fw - 1) := by exact_mod_cast this
    generalize (2 : ℤ) ^ (fw - 1) = Q at h6 ⊢
    omega
  have hdig : ∀ t, choiceDigit g fw ι t < 2 ^ fw := by
    intro t
    unfold choiceDigit
    have hpos : (0 : ℤ) < (2 : ℤ) ^ (fw - 1) := by positivity
    split_ifs with h h'
    · have := hb h.choose
      generalize (2 : ℤ) ^ (fw - 1) = Q at this h2 hpos ⊢
      generalize 2 ^ fw = N at h2 ⊢
      omega
    · have := hb h'.choose
      generalize (2 : ℤ) ^ (fw - 1) = Q at this h2 hpos ⊢
      generalize 2 ^ fw = N at h2 ⊢
      omega
    · generalize (2 : ℤ) ^ (fw - 1) = Q at h2 hpos ⊢
      generalize 2 ^ fw = N at h2 ⊢
      omega
  obtain ⟨hlt, hext⟩ := chn_digits (b := 2 ^ fw) (by positivity) (2 * g ^ 4) (choiceDigit g fw ι)
    fun t _ => hdig t
  have hc : choiceCode g fw ι = ∑ t ∈ range (2 * g ^ 4), (2 ^ fw) ^ t * choiceDigit g fw ι t := rfl
  have hfield : ∀ t < 2 * g ^ 4, field fw (choiceCode g fw ι) t =
      (choiceDigit g fw ι t : ℤ) - 2 ^ (fw - 1) := fun t ht => by
    unfold field
    rw [show 2 ^ (t * fw) = (2 ^ fw) ^ t by rw [← pow_mul, Nat.mul_comm], hc, hext t ht]
  refine ⟨?_, ?_⟩
  · rw [hc, choiceWidth, show 2 * g ^ 4 * fw = fw * (2 * g ^ 4) from Nat.mul_comm _ _, pow_mul]
    exact hlt
  · funext r
    have hr := chn_rectIdx_lt r
    have e1 : choiceDigit g fw ι (2 * rectIdx r) = ((ι r).1 + 2 ^ (fw - 1)).toNat := by
      have hex : ∃ r' : Rect g, 2 * rectIdx r' = 2 * rectIdx r := ⟨r, rfl⟩
      unfold choiceDigit
      rw [dite_eq_left hex, chn_rectIdx_inj
          (by have := hex.choose_spec; omega : rectIdx hex.choose = rectIdx r)]
    have e2 : choiceDigit g fw ι (2 * rectIdx r + 1) = ((ι r).2 + 2 ^ (fw - 1)).toNat := by
      have hn : ¬ ∃ r' : Rect g, 2 * rectIdx r' = 2 * rectIdx r + 1 := fun ⟨r', h⟩ => by omega
      have hex : ∃ r' : Rect g, 2 * rectIdx r' + 1 = 2 * rectIdx r + 1 := ⟨r, rfl⟩
      unfold choiceDigit
      rw [dite_eq_right hn, dite_eq_left hex,
        chn_rectIdx_inj (by have := hex.choose_spec; omega : rectIdx hex.choose = rectIdx r)]
    refine Prod.ext ?_ ?_
    · change field fw _ _ = _
      rw [hfield _ (by omega), e1, Int.toNat_of_nonneg (hb r).1, add_sub_cancel_right]
    · change field fw _ _ = _
      rw [hfield _ (by omega), e2, Int.toNat_of_nonneg (hb r).2.2.1, add_sub_cancel_right]

/-! ### The orientation and the child -/

/-- Rows, unless the column potential is smaller (ties go to the rows). -/
def orientRow (a : Fin (g * g) → Fin (g * g) → ℕ) (k : Rect g → ℤ) : Bool :=
  decide (∑ p : Pairs g, rowBudget a k p.1.1 p.1.2 ≤ ∑ p : Pairs g, colBudget a k p.1.1 p.1.2)

/-- The child of a clique on `g × g` nodes at a choice, in the orientation of its grades. -/
noncomputable def mergeStep (g : ℕ) (a : Fin (g * g) → Fin (g * g) → ℕ)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) (ι : Rect g → ℤ × ℤ) : Clique :=
  if orientRow a (fun r => (ι r).1) then rowChild g a T ι else colChild g a T ι

/-- The child of a clique at a choice code (the clique itself if its node count is not a square). -/
noncomputable def childAt (fw : ℕ) (C : Clique) (i : ℕ) : Clique :=
  let g := Nat.sqrt C.q
  if h : C.q = g * g then
    let C' := C.recast (g * g) h
    mergeStep g C'.a C'.T (decodeChoice g fw i)
  else C

/-- **The clique at a path** of choice codes, latest first. -/
noncomputable def chainAt (fw : ℕ) (C₀ : Clique) : List ℕ → Clique
  | [] => C₀
  | i :: rest => childAt fw (chainAt fw C₀ rest) i

open Classical in
/-- **Lemma 6.2 through the codes.** If the field width is positive and represents every grade and
split of the choices, the value of a clique on `g × g` nodes is the sum, over the valid codes of
width `choiceWidth g fw`, of the values of its children. -/
theorem value_childAt (fw : ℕ) (C : Clique) (hg : 1 ≤ Nat.sqrt C.q)
    (hsq : C.q = Nat.sqrt C.q * Nat.sqrt C.q)
    (hfw0 : 1 ≤ fw)
    (hfw : ∀ r : Rect (Nat.sqrt C.q), 6 * diagWt (C.recast _ hsq).a r < 2 ^ (fw - 1)) :
    C.value = ∑ i ∈ range (2 ^ choiceWidth (Nat.sqrt C.q) fw),
      if ValidChoiceCode (C.recast _ hsq).a fw i then (childAt fw C i).value else 0 := by
  have hchild : ∀ i, childAt fw C i = mergeStep (Nat.sqrt C.q) (C.recast _ hsq).a
      (C.recast _ hsq).T (decodeChoice (Nat.sqrt C.q) fw i) := fun i => by
    simp only [childAt, dite_eq_left hsq]
  have hm := merge (g := Nat.sqrt C.q) hg (C.recast _ hsq).a (C.recast _ hsq).T
    (orientRow (C.recast _ hsq).a)
  have hcode : ∀ ι ∈ choices (C.recast _ hsq).a,
      choiceCode (Nat.sqrt C.q) fw ι < 2 ^ choiceWidth (Nat.sqrt C.q) fw ∧
        decodeChoice (Nat.sqrt C.q) fw (choiceCode (Nat.sqrt C.q) fw ι) = ι :=
    fun ι hι => chn_code _ fw hfw0 hfw hι
  rw [← Clique.value_recast C _ hsq]
  refine hm.trans ?_
  change ∑ ι ∈ choices _, (mergeStep _ (C.recast _ hsq).a (C.recast _ hsq).T ι).value = _
  simp only [hchild]
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_nbij' (s := (range (2 ^ choiceWidth (Nat.sqrt C.q) fw)).filter
      (ValidChoiceCode (C.recast _ hsq).a fw)) (t := choices (C.recast _ hsq).a)
    (f := fun i => (mergeStep _ (C.recast _ hsq).a (C.recast _ hsq).T
      (decodeChoice (Nat.sqrt C.q) fw i)).value)
    (g := fun ι => (mergeStep _ (C.recast _ hsq).a (C.recast _ hsq).T ι).value)
    (decodeChoice (Nat.sqrt C.q) fw) (choiceCode (Nat.sqrt C.q) fw)
    (fun i hi => (Finset.mem_filter.mp hi).2.1) (fun ι hι => ?_)
    (fun i hi => (Finset.mem_filter.mp hi).2.2) (fun ι hι => (hcode ι hι).2) (fun _ _ => rfl)
  obtain ⟨hlt, hdec⟩ := hcode ι hι
  have hv : ValidChoiceCode (C.recast _ hsq).a fw (choiceCode (Nat.sqrt C.q) fw ι) := by
    unfold ValidChoiceCode
    rw [hdec]
    exact ⟨hι, rfl⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlt, hv⟩

end Cslib.Complexity.NtimeDspace.Cube
