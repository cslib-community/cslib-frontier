/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Chain
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.Codes

/-!
# Budget arrays as numbers (Lemma 6.4)

The machine of Lemma 6.4 keeps the budget array of the current clique and of its child. This
module fixes the array as one number and states, in plain arithmetic on `ℕ`, everything the
machine reads from it; `BudgetTerm.lean` computes these functions by terms.

## Layout

* `digitN fw x t = x / 2^(t·fw) % 2^fw` is digit `t` of width `fw` (the digits of `field`), and
  `packN fw n d = ∑_{t<n} (2^fw)^t · d t` the number with digits `d 0, …, d (n-1)` (the layout of
  `choiceCode`).
* `arrN q fw b`: the budget array on `q` nodes, with `b u v` at digit `u·q + v` for `u < v < q`
  and `0` at every other digit of `q·q`. For a clique, `b = extN C.a`.
* `budgetN A q fw u v`: the budget of the pair `{u, v}` read from an array, with the symmetric
  convention of `budget`.

`ArrFits q fw b` (every stored budget is below `2^fw`) makes the layout faithful:
`digitN_arrN`, `budgetN_ext`.

## Main definitions

* Rectangles by their quadruple index (`rectIdx`): `qd g x k = x / g^k % g` (the digits of `quad`),
  `IsRectN`, `diagN` (`diagWt`); `sum_rect`, `forall_rect`.
* `rowBN`, `colBN`, `orientN`, `childN`: the candidate budgets, the orientation and the child array
  from the parent array and a choice code.
* `RectOkN`, `PadOkN`, `FieldOkN`, `ValidN`: validity of a choice code.
* `argOffN`, `argWidN`, `sliceOffN`, `sliceN`, `copiesWidN`, `xiWidN`: index widths, from the
  array (their agreement with `Formula.lean` is in `BudgetForm.lean`).

## Main results

* `diagN_eq`: `diagWt a r` from the array.
* `rowBN_eq`, `colBN_eq`, `orientN_eq`: the row and column budgets (for even grades) and
  `orientRow`.
* `childN_eq_mergeStep`, `childN_eq_childAt`: the child array is the array of the child clique.
* `validN_iff`: `ValidN` decides `ValidChoiceCode`.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube.Num

open Finset NtimeDspace.Cube

/-! ### Fixed-width digits -/

/-- Digit `t` of width `fw` of `x`. -/
def digitN (fw x t : ℕ) : ℕ := x / 2 ^ (t * fw) % 2 ^ fw

/-- The number with digits `d 0, …, d (n-1)` of width `fw`. -/
def packN (fw n : ℕ) (d : ℕ → ℕ) : ℕ := ∑ t ∈ range n, (2 ^ fw) ^ t * d t

theorem field_eq_digitN (fw i t : ℕ) : field fw i t = (digitN fw i t : ℤ) - 2 ^ (fw - 1) := rfl

theorem digitN_lt (fw x t : ℕ) : digitN fw x t < 2 ^ fw := Nat.mod_lt _ (by positivity)

theorem choiceCode_eq_packN (g fw : ℕ) (ι : Rect g → ℤ × ℤ) :
    choiceCode g fw ι = packN fw (2 * g ^ 4) (choiceDigit g fw ι) := rfl

theorem packN_succ (fw n : ℕ) (d : ℕ → ℕ) :
    packN fw (n + 1) d = packN fw n d + 2 ^ (n * fw) * d n := by
  rw [packN, sum_range_succ, ← pow_mul, Nat.mul_comm fw n]; rfl

theorem packN_lt {fw n : ℕ} {d : ℕ → ℕ} (hd : ∀ t < n, d t < 2 ^ fw) :
    packN fw n d < 2 ^ (n * fw) := by
  induction n with
  | zero => simp [packN]
  | succ n ih =>
    rw [packN_succ]
    have h1 := ih fun t ht => hd t (by omega)
    have h2 := hd n (by omega)
    calc packN fw n d + 2 ^ (n * fw) * d n < 2 ^ (n * fw) + 2 ^ (n * fw) * d n := by omega
      _ = 2 ^ (n * fw) * (d n + 1) := by ring
      _ ≤ 2 ^ (n * fw) * 2 ^ fw := Nat.mul_le_mul_left _ h2
      _ = 2 ^ ((n + 1) * fw) := by rw [← pow_add, Nat.add_mul, Nat.one_mul]

theorem digitN_packN {fw n : ℕ} {d : ℕ → ℕ} (hd : ∀ t < n, d t < 2 ^ fw) (s : ℕ) :
    digitN fw (packN fw n d) s = if s < n then d s else 0 := by
  induction n with
  | zero => simp [packN, digitN]
  | succ n ih =>
    have hd' : ∀ t < n, d t < 2 ^ fw := fun t ht => hd t (by omega)
    have ih' := ih hd'
    have hlt := packN_lt hd'
    have hdn := hd n (by omega)
    rw [packN_succ]
    unfold digitN at ih' ⊢
    rcases lt_trichotomy s n with h | rfl | h
    · have e : 2 ^ (n * fw) * d n = 2 ^ (s * fw) * (2 ^ fw * (2 ^ ((n - s - 1) * fw) * d n)) := by
        rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
        congr 2
        have : n = s + 1 + (n - s - 1) := by omega
        conv_lhs => rw [this]
        ring
      rw [e, Nat.add_mul_div_left _ _ (by positivity), Nat.add_mul_mod_self_left, ih',
        ite_eq_left_iff.mpr (fun h' => absurd h h'), ite_eq_left_iff.mpr
            (fun h' => absurd (by omega) h')]
    · rw [Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlt, Nat.zero_add,
        Nat.mod_eq_of_lt hdn, ite_eq_left_iff.mpr (fun h' => absurd (by omega) h')]
    · have hx : packN fw n d + 2 ^ (n * fw) * d n < 2 ^ (s * fw) := by
        calc _ < 2 ^ ((n + 1) * fw) := by
              have := packN_lt (n := n + 1) hd
              rwa [packN_succ] at this
          _ ≤ 2 ^ (s * fw) := Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ h)
      rw [Nat.div_eq_of_lt hx, Nat.zero_mod, ite_eq_right_iff.mpr (fun h' => absurd h' (by omega))]

theorem packN_digitN (fw x n : ℕ) : packN fw n (digitN fw x) = x % 2 ^ (n * fw) := by
  induction n with
  | zero => simp [packN, Nat.mod_one]
  | succ n ih =>
    rw [packN_succ, ih, digitN, show (n + 1) * fw = n * fw + fw by ring, pow_add, Nat.mod_mul]

/-- A number is the number of digits `d` iff it is short and has those digits. -/
theorem packN_eq_iff {fw n x : ℕ} {d : ℕ → ℕ} (hd : ∀ t < n, d t < 2 ^ fw) :
    packN fw n d = x ↔ x < 2 ^ (n * fw) ∧ ∀ t < n, digitN fw x t = d t := by
  constructor
  · rintro rfl
    exact ⟨packN_lt hd, fun t ht => by rw [digitN_packN hd, ite_eq_left_iff.mpr (absurd ht)]⟩
  · rintro ⟨hx, hdig⟩
    rw [← Nat.mod_eq_of_lt hx, ← packN_digitN]
    exact sum_congr rfl fun t ht => by rw [hdig t (mem_range.mp ht)]

/-! ### Budget arrays -/

/-- **The budget array** on `q` nodes: `b u v` at digit `u·q + v` for `u < v < q`. -/
def arrN (q fw : ℕ) (b : ℕ → ℕ → ℕ) : ℕ :=
  packN fw (q * q) fun t => if t / q < t % q then b (t / q) (t % q) else 0

/-- The budget of the pair `{u, v}` read from an array. -/
def budgetN (A q fw u v : ℕ) : ℕ := digitN fw A (min u v * q + max u v)

/-- Every stored budget is below `2^fw`. -/
def ArrFits (q fw : ℕ) (b : ℕ → ℕ → ℕ) : Prop := ∀ u v, u < v → v < q → b u v < 2 ^ fw

/-- The budgets of a clique as a function on numbers (`0` off the nodes). -/
def extN {q : ℕ} (a : Fin q → Fin q → ℕ) (u v : ℕ) : ℕ :=
  if h : u < q ∧ v < q then a ⟨u, h.1⟩ ⟨v, h.2⟩ else 0

/-- Every budget `a u v`, `u < v`, of a clique is below `2^fw`. -/
def Fits (fw : ℕ) {q : ℕ} (a : Fin q → Fin q → ℕ) : Prop := ∀ u v : Fin q, u < v → a u v < 2 ^ fw

theorem arrN_congr {q fw : ℕ} {b b' : ℕ → ℕ → ℕ} (h : ∀ u v, u < v → v < q → b u v = b' u v) :
    arrN q fw b = arrN q fw b' := by
  unfold arrN packN
  refine sum_congr rfl fun t ht => ?_
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · simp [h0] at ht
    · exact h0
  dsimp only
  split_ifs with hlt
  · rw [h _ _ hlt (Nat.mod_lt _ hq)]
  · rfl

theorem slot_div {q u v : ℕ} (hv : v < q) : (u * q + v) / q = u := by
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]

theorem slot_mod {q u v : ℕ} (hv : v < q) : (u * q + v) % q = v := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem slot_lt {q u v : ℕ} (hu : u < q) (hv : v < q) : u * q + v < q * q :=
  calc u * q + v < u * q + q := by omega
    _ = (u + 1) * q := by ring
    _ ≤ q * q := Nat.mul_le_mul_right _ hu

theorem arrN_digits_lt {q fw : ℕ} {b : ℕ → ℕ → ℕ} (hb : ArrFits q fw b) :
    ∀ t < q * q, (if t / q < t % q then b (t / q) (t % q) else 0) < 2 ^ fw := by
  intro t ht
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h0 | h0
    · simp [h0] at ht
    · exact h0
  split_ifs with h
  · exact hb _ _ h (Nat.mod_lt _ hq)
  · positivity

theorem arrN_lt {q fw : ℕ} {b : ℕ → ℕ → ℕ} (hb : ArrFits q fw b) : arrN q fw b < 2 ^ (q * q * fw) :=
  packN_lt (arrN_digits_lt hb)

/-- The digit of a pair `u < v` of an array. -/
theorem digitN_arrN {q fw : ℕ} {b : ℕ → ℕ → ℕ} (hb : ArrFits q fw b) {u v : ℕ} (huv : u < v)
    (hv : v < q) : digitN fw (arrN q fw b) (u * q + v) = b u v := by
  rw [arrN, digitN_packN (arrN_digits_lt hb), ite_eq_left_iff.mpr (fun h => absurd
    (slot_lt (by omega) hv) h), slot_div hv, slot_mod hv, ite_eq_left_iff.mpr
        (fun h => absurd huv h)]

theorem budgetN_arrN {q fw : ℕ} {b : ℕ → ℕ → ℕ} (hb : ArrFits q fw b) {u v : ℕ} (hu : u < q)
    (hv : v < q) (huv : u ≠ v) : budgetN (arrN q fw b) q fw u v = b (min u v) (max u v) :=
  digitN_arrN hb (by omega) (by omega)

theorem Fits.arr {fw q : ℕ} {a : Fin q → Fin q → ℕ} (h : Fits fw a) : ArrFits q fw (extN a) :=
  fun u v huv hv => by
    rw [extN, dite_eq_left ⟨by omega, hv⟩]
    exact h _ _ (Fin.mk_lt_mk.mpr huv)

theorem extN_fin {q : ℕ} (a : Fin q → Fin q → ℕ) (u v : Fin q) : extN a u v = a u v := by
  rw [extN, dite_eq_left ⟨u.isLt, v.isLt⟩]

/-- The budget of a pair of distinct nodes of a clique, from its array. -/
theorem budgetN_ext {fw q : ℕ} {a : Fin q → Fin q → ℕ} (h : Fits fw a) {u v : Fin q} (huv : u ≠ v) :
    budgetN (arrN q fw (extN a)) q fw u v = budget a u v := by
  rw [budgetN_arrN h.arr u.isLt v.isLt (fun e => huv (Fin.ext e)), budget]
  rcases le_total u v with h' | h'
  · rw [min_eq_left h', max_eq_right h', min_eq_left (Fin.le_def.mp h'),
      max_eq_right (Fin.le_def.mp h'), extN_fin]
  · rw [min_eq_right h', max_eq_left h', min_eq_right (Fin.le_def.mp h'),
      max_eq_left (Fin.le_def.mp h'), extN_fin]

theorem budgetN_ext_lt {fw q : ℕ} {a : Fin q → Fin q → ℕ} (h : Fits fw a) {u v : Fin q}
    (huv : u < v) : budgetN (arrN q fw (extN a)) q fw u v = a u v := by
  rw [budgetN_ext h huv.ne, budget, min_eq_left huv.le, max_eq_right huv.le]

theorem extN_recast (C : Clique) (n : ℕ) (h : C.q = n) :
    extN (q := n) (C.recast n h).a = extN C.a := by
  subst h; rfl

theorem Fits.recast {fw : ℕ} {C : Clique} (hC : Fits fw C.a) (n : ℕ) (h : C.q = n) :
    Fits fw (C.recast n h).a := by
  subst h; exact hC

/-! ### Rectangles by their index -/

/-- Digit `k` in base `g` (`quad g x = (qd g x 3, qd g x 2, qd g x 1, x % g)`). -/
def qd (g x k : ℕ) : ℕ := x / g ^ k % g

/-- The index `x` is a rectangle: rows `qd 3 < qd 2` and columns `qd 1 < qd 0`. -/
def IsRectN (g x : ℕ) : Prop := qd g x 3 < qd g x 2 ∧ qd g x 1 < qd g x 0

instance (g x : ℕ) : Decidable (IsRectN g x) := by unfold IsRectN; infer_instance

theorem qd_zero (g x : ℕ) : qd g x 0 = x % g := by simp [qd]

private theorem quad_digits {g a b c d : ℕ} (hb : b < g) (hc : c < g) (hd : d < g) (ha : a < g) :
    qd g (((a * g + b) * g + c) * g + d) 3 = a ∧ qd g (((a * g + b) * g + c) * g + d) 2 = b ∧
      qd g (((a * g + b) * g + c) * g + d) 1 = c ∧ qd g (((a * g + b) * g + c) * g + d) 0 = d := by
  have e3 : g ^ 3 = g * g * g := by ring
  have e2 : g ^ 2 = g * g := by ring
  have h1 := slot_div (u := (a * g + b) * g + c) hd
  have h2 := slot_div (u := a * g + b) hc
  have h3 := slot_div (u := a) hb
  simp only [qd, e3, e2, pow_one, pow_zero, Nat.div_one, ← Nat.div_div_eq_div_mul, h1, h2, h3]
  exact ⟨Nat.mod_eq_of_lt ha, slot_mod hb, slot_mod hc, slot_mod hd⟩

variable {g : ℕ}

theorem qd_rectIdx (r : Rect g) :
    qd g (rectIdx r) 3 = r.1.1.1 ∧ qd g (rectIdx r) 2 = r.1.1.2 ∧ qd g (rectIdx r) 1 = r.1.2.1 ∧
      qd g (rectIdx r) 0 = r.1.2.2 :=
  quad_digits r.1.1.2.isLt r.1.2.1.isLt r.1.2.2.isLt r.1.1.1.isLt

private theorem lt_mul_add {x m y n : ℕ} (hx : x < m) (hy : y < n) : x * n + y < m * n :=
  calc x * n + y < x * n + n := by omega
    _ = (x + 1) * n := by ring
    _ ≤ m * n := Nat.mul_le_mul_right _ hx

theorem rectIdx_lt (r : Rect g) : rectIdx r < g ^ 4 := by
  have := lt_mul_add (lt_mul_add (lt_mul_add r.1.1.1.isLt r.1.1.2.isLt) r.1.2.1.isLt) r.1.2.2.isLt
  unfold rectIdx
  calc _ < g * g * g * g := this
    _ = g ^ 4 := by ring

theorem idx_qd {x : ℕ} (hx : x < g ^ 4) :
    ((qd g x 3 * g + qd g x 2) * g + qd g x 1) * g + qd g x 0 = x := by
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hx
    · exact h
  have e3 : g ^ 3 = g * g * g := by ring
  have e2 : g ^ 2 = g * g := by ring
  have h3 : x / g / g / g < g := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, Nat.div_lt_iff_lt_mul (by positivity)]
    calc x < g ^ 4 := hx
      _ = _ := by ring
  simp only [qd, e3, e2, pow_one, pow_zero, Nat.div_one, ← Nat.div_div_eq_div_mul,
    Nat.mod_eq_of_lt h3, Nat.div_add_mod']

/-- The indices of rectangles. -/
theorem exists_rectIdx_iff {x : ℕ} : (∃ r : Rect g, rectIdx r = x) ↔ x < g ^ 4 ∧ IsRectN g x := by
  constructor
  · rintro ⟨r, rfl⟩
    obtain ⟨h3, h2, h1, h0⟩ := qd_rectIdx r
    refine ⟨rectIdx_lt r, ?_⟩
    rw [IsRectN, h3, h2, h1, h0]
    exact ⟨r.2.1, r.2.2⟩
  · rintro ⟨hx, h1, h2⟩
    have hg : 0 < g := by
      rcases Nat.eq_zero_or_pos g with h | h
      · subst h; simp at hx
      · exact h
    refine ⟨⟨((⟨qd g x 3, Nat.mod_lt _ hg⟩, ⟨qd g x 2, Nat.mod_lt _ hg⟩),
      (⟨qd g x 1, Nat.mod_lt _ hg⟩, ⟨qd g x 0, Nat.mod_lt _ hg⟩)), h1, h2⟩, ?_⟩
    exact idx_qd hx

theorem rectIdx_injective : Function.Injective (rectIdx (g := g)) := by
  intro r r' h
  obtain ⟨a3, a2, a1, a0⟩ := qd_rectIdx r
  obtain ⟨b3, b2, b1, b0⟩ := qd_rectIdx r'
  rw [h] at a3 a2 a1 a0
  exact Subtype.ext (Prod.ext (Prod.ext (Fin.ext (a3.symm.trans b3)) (Fin.ext (a2.symm.trans b2)))
    (Prod.ext (Fin.ext (a1.symm.trans b1)) (Fin.ext (a0.symm.trans b0))))

/-- A sum over the rectangles, by their indices. -/
theorem sum_rect {M : Type*} [AddCommMonoid M] (F : ℕ → M) :
    ∑ r : Rect g, F (rectIdx r) = ∑ x ∈ range (g ^ 4), if IsRectN g x then F x else 0 := by
  rw [← sum_filter, ← sum_image (s := univ) (g := rectIdx) (fun r _ r' _ h => rectIdx_injective h)]
  congr 1
  ext x
  simp only [mem_image, mem_univ, true_and, mem_filter, mem_range]
  exact exists_rectIdx_iff

theorem forall_rect (P : ℕ → Prop) :
    (∀ r : Rect g, P (rectIdx r)) ↔ ∀ x < g ^ 4, IsRectN g x → P x := by
  constructor
  · intro h x hx hr
    obtain ⟨r, rfl⟩ := exists_rectIdx_iff.mpr ⟨hx, hr⟩
    exact h r
  · intro h r
    obtain ⟨h1, h2⟩ := exists_rectIdx_iff.mp ⟨r, rfl⟩
    exact h _ h1 h2

/-- A sum over the pairs `u < v` of `Fin g`. -/
theorem sum_pairs {M : Type*} [AddCommMonoid M] (F : ℕ → ℕ → M) :
    ∑ p : Pairs g, F p.1.1 p.1.2 =
      ∑ u ∈ range g, ∑ v ∈ range g, if u < v then F u v else 0 := by
  rw [← sum_subtype (univ.filter fun p : Fin g × Fin g => p.1 < p.2) (by simp)
    (fun p => F p.1 p.2), sum_filter, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range]
  refine sum_congr rfl fun u _ => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun v => if (u : ℕ) < v then F u v else 0)]
  rfl

/-! ### Diagonal weights, candidate budgets and the child array -/

/-- The diagonal weight `H_R` of the rectangle of index `x`, from an array (node `(A, B)` is the
number `A·g + B`). -/
def diagN (ar q fw g x : ℕ) : ℕ :=
  budgetN ar q fw (qd g x 3 * g + qd g x 1) (qd g x 2 * g + qd g x 0) +
    budgetN ar q fw (qd g x 3 * g + qd g x 0) (qd g x 2 * g + qd g x 1)

/-- The share `(H_R + k_R/2)^+` of the rows, for the grade `k_R = digit - 2^(fw-1)`. -/
def rowTermN (ar q fw g i x : ℕ) : ℕ := (2 * diagN ar q fw g x + digitN fw i (2 * x) - 2 ^ (fw - 1))
    / 2

/-- The share `(H_R - k_R/2)^+` of the columns. -/
def colTermN (ar q fw g i x : ℕ) : ℕ := (2 * diagN ar q fw g x + 2 ^ (fw - 1) - digitN fw i (2 * x))
    / 2

/-- **The row budget** `A^row_{u v}` (`rowBudget`), from the array and the choice code `i`. -/
def rowBN (ar q fw g i u v : ℕ) : ℕ :=
  packL g * ((∑ B ∈ range g, budgetN ar q fw (u * g + B) (v * g + B)) +
    ∑ x ∈ range (g ^ 4), if IsRectN g x then
      (if qd g x 3 = u ∧ qd g x 2 = v then rowTermN ar q fw g i x else 0) else 0)

/-- **The column budget** `A^col_{u v}` (`colBudget`). -/
def colBN (ar q fw g i u v : ℕ) : ℕ :=
  packL g * ((∑ A ∈ range g, budgetN ar q fw (A * g + u) (A * g + v)) +
    ∑ x ∈ range (g ^ 4), if IsRectN g x then
      (if qd g x 1 = u ∧ qd g x 0 = v then colTermN ar q fw g i x else 0) else 0)

/-- The sum of a function over the pairs `u < v < g`. -/
def pairSumN (g : ℕ) (F : ℕ → ℕ → ℕ) : ℕ := ∑ u ∈ range g, ∑ v ∈ range g, if u < v then F u v else 0

/-- **The orientation** (`orientRow`): rows unless the column potential is smaller. -/
def orientN (ar q fw g i : ℕ) : Bool :=
  decide (pairSumN g (rowBN ar q fw g i) ≤ pairSumN g (colBN ar q fw g i))

/-- **The child array**: the array on `g` nodes of the cheaper candidate budgets. -/
def childN (ar q fw g i : ℕ) : ℕ :=
  arrN g fw fun u v => if orientN ar q fw g i then rowBN ar q fw g i u v else colBN ar q fw g i u v

variable {fw i : ℕ} {a : Fin (g * g) → Fin (g * g) → ℕ}

theorem diagN_eq (h : Fits fw a) (r : Rect g) :
    diagN (arrN (g * g) fw (extN a)) (g * g) fw g (rectIdx r) = diagWt a r := by
  obtain ⟨h3, h2, h1, h0⟩ := qd_rectIdx r
  rw [diagN, h3, h2, h1, h0]
  have e1 := budgetN_ext_lt h (node_lt_node r.2.1 r.1.2.1 r.1.2.2)
  have e2 := budgetN_ext_lt h (node_lt_node r.2.1 r.1.2.2 r.1.2.1)
  unfold node at e1 e2
  rw [e1, e2]
  rfl

private theorem half_row {H D Q : ℕ} (he : Even ((D : ℤ) - Q)) :
    ((H : ℤ) + ((D : ℤ) - Q) / 2).toNat = (2 * H + D - Q) / 2 := by
  obtain ⟨m, hm⟩ := he; omega

private theorem half_col {H D Q : ℕ} (he : Even ((D : ℤ) - Q)) :
    ((H : ℤ) - ((D : ℤ) - Q) / 2).toNat = (2 * H + Q - D) / 2 := by
  obtain ⟨m, hm⟩ := he; omega

private theorem two_pow_int (fw : ℕ) : (2 : ℤ) ^ (fw - 1) =
    ((2 ^ (fw - 1) : ℕ) : ℤ) := by push_cast; rfl

theorem grade_eq (r : Rect g) :
    (decodeChoice g fw i r).1 = (digitN fw i (2 * rectIdx r) : ℤ) - ((2 ^ (fw - 1) : ℕ) : ℤ) := by
  rw [← two_pow_int]; rfl

theorem rowBN_eq (h : Fits fw a) (he : ∀ r, Even (decodeChoice g fw i r).1) {A A' : Fin g}
    (hA : A < A') :
    rowBN (arrN (g * g) fw (extN a)) (g * g) fw g i A A' =
      rowBudget a (fun r => (decodeChoice g fw i r).1) A A' := by
  unfold rowBN rowBudget
  congr 2
  · rw [← Fin.sum_univ_eq_sum_range (fun B => budgetN (arrN (g * g) fw (extN a)) (g * g) fw
      (A * g + B) (A' * g + B))]
    exact sum_congr rfl fun B _ => budgetN_ext_lt h (node_lt_node hA B B)
  · have key : ∀ r : Rect g, (if r.1.1.1 = A ∧ r.1.1.2 = A' then
        ((diagWt a r : ℤ) + (decodeChoice g fw i r).1 / 2).toNat else 0) =
        (fun x => if qd g x 3 = A ∧ qd g x 2 = A' then
          rowTermN (arrN (g * g) fw (extN a)) (g * g) fw g i x else 0) (rectIdx r) := by
      intro r
      obtain ⟨h3, h2, -, -⟩ := qd_rectIdx r
      have hk := he r
      rw [grade_eq] at hk ⊢
      simp only [h3, h2, ← Fin.ext_iff, rowTermN, diagN_eq h, half_row hk]
    rw [sum_congr rfl fun r _ => key r]
    exact (sum_rect _).symm

theorem colBN_eq (h : Fits fw a) (he : ∀ r, Even (decodeChoice g fw i r).1) {B B' : Fin g}
    (hB : B < B') :
    colBN (arrN (g * g) fw (extN a)) (g * g) fw g i B B' =
      colBudget a (fun r => (decodeChoice g fw i r).1) B B' := by
  unfold colBN colBudget
  congr 2
  · rw [← Fin.sum_univ_eq_sum_range (fun A => budgetN (arrN (g * g) fw (extN a)) (g * g) fw
      (A * g + B) (A * g + B'))]
    exact sum_congr rfl fun A _ => budgetN_ext_lt h (node_lt_node_right A hB)
  · have key : ∀ r : Rect g, (if r.1.2.1 = B ∧ r.1.2.2 = B' then
        ((diagWt a r : ℤ) - (decodeChoice g fw i r).1 / 2).toNat else 0) =
        (fun x => if qd g x 1 = B ∧ qd g x 0 = B' then
          colTermN (arrN (g * g) fw (extN a)) (g * g) fw g i x else 0) (rectIdx r) := by
      intro r
      obtain ⟨-, -, h1, h0⟩ := qd_rectIdx r
      have hk := he r
      rw [grade_eq] at hk ⊢
      simp only [h1, h0, ← Fin.ext_iff, colTermN, diagN_eq h, half_col hk]
    rw [sum_congr rfl fun r _ => key r]
    exact (sum_rect _).symm

theorem orientN_eq (h : Fits fw a) (he : ∀ r, Even (decodeChoice g fw i r).1) :
    orientN (arrN (g * g) fw (extN a)) (g * g) fw g i =
      orientRow a (fun r => (decodeChoice g fw i r).1) := by
  have hr : ∑ p : Pairs g, rowBudget a (fun r => (decodeChoice g fw i r).1) p.1.1 p.1.2 =
      pairSumN g (rowBN (arrN (g * g) fw (extN a)) (g * g) fw g i) := by
    rw [pairSumN, ← sum_pairs]
    exact sum_congr rfl fun p _ => (rowBN_eq h he p.2).symm
  have hc : ∑ p : Pairs g, colBudget a (fun r => (decodeChoice g fw i r).1) p.1.1 p.1.2 =
      pairSumN g (colBN (arrN (g * g) fw (extN a)) (g * g) fw g i) := by
    rw [pairSumN, ← sum_pairs]
    exact sum_congr rfl fun p _ => (colBN_eq h he p.2).symm
  rw [orientN, orientRow, hr, hc]

/-- **The child array** is the array of the child clique at the choice (even grades). -/
theorem childN_eq_mergeStep (h : Fits fw a) (he : ∀ r, Even (decodeChoice g fw i r).1)
    (T : Fin (g * g) → (Fin (g * g) → Label) → ℤ) :
    arrN g fw (extN (mergeStep g a T (decodeChoice g fw i)).a) =
      childN (arrN (g * g) fw (extN a)) (g * g) fw g i := by
  unfold childN
  rw [orientN_eq h he]
  cases hc : orientRow a (fun r => (decodeChoice g fw i r).1)
  · have hm : mergeStep g a T (decodeChoice g fw i) = colChild g a T (decodeChoice g fw i) := by
      simp only [mergeStep, hc, Bool.false_eq_true, ite_false]
    rw [hm]
    refine arrN_congr fun u v huv hv => ?_
    have e := extN_fin (q := g) (colChild g a T (decodeChoice g fw i)).a ⟨u, by omega⟩ ⟨v, hv⟩
    refine e.trans ?_
    rw [colChild_a a T _ (fun r => he r) (Fin.mk_le_mk.mpr huv.le),
      ← colBN_eq h he (Fin.mk_lt_mk.mpr huv)]
    simp only [Bool.false_eq_true, ite_false]
  · have hm : mergeStep g a T (decodeChoice g fw i) = rowChild g a T (decodeChoice g fw i) := by
      simp only [mergeStep, hc, ite_true]
    rw [hm]
    refine arrN_congr fun u v huv hv => ?_
    have e := extN_fin (q := g) (rowChild g a T (decodeChoice g fw i)).a ⟨u, by omega⟩ ⟨v, hv⟩
    refine e.trans ?_
    simp only [ite_true]
    exact (rowBN_eq h he (Fin.mk_lt_mk.mpr huv)).symm

/-- The grades of a valid choice code are even. -/
theorem ValidChoiceCode.even (hv : ValidChoiceCode a fw i) (r : Rect g) :
    Even (decodeChoice g fw i r).1 := by
  have := Fintype.mem_piFinset.mp hv.1 r
  simp only [mem_product, mem_filter] at this
  exact this.1.2

/-- **The child array of a clique** at a choice code with even grades, from its array. -/
theorem childN_eq_childAt (C : Clique) (hsq : C.q = Nat.sqrt C.q * Nat.sqrt C.q)
    (h : Fits fw C.a) (he : ∀ r, Even (decodeChoice (Nat.sqrt C.q) fw i r).1) :
    arrN (Nat.sqrt C.q) fw (extN (childAt fw C i).a) =
      childN (arrN C.q fw (extN C.a)) C.q fw (Nat.sqrt C.q) i := by
  have hc : childAt fw C i = mergeStep (Nat.sqrt C.q) (C.recast _ hsq).a (C.recast _ hsq).T
      (decodeChoice (Nat.sqrt C.q) fw i) := by
    simp only [childAt, dite_eq_left hsq]
  have key := childN_eq_mergeStep (g := Nat.sqrt C.q) (h.recast _ hsq) he (C.recast _ hsq).T
  rw [hc, key, extN_recast, ← hsq]

/-! ### Validity of a choice code -/

/-- The grade and split of the rectangle of index `x` are in range, with an even grade:
`k = D - 2^(fw-1)`, `c = C - 2^(fw-1)` for the digits `D`, `C` at fields `2x`, `2x + 1`. -/
def RectOkN (ar q fw g i x : ℕ) : Prop :=
  ((digitN fw i (2 * x) + 2 ^ (fw - 1)) % 2 = 0 ∧
    digitN fw i (2 * x) ≤ 2 ^ (fw - 1) + 2 * diagN ar q fw g x ∧
    2 ^ (fw - 1) ≤ digitN fw i (2 * x) + 2 * diagN ar q fw g x) ∧
  (digitN fw i (2 * x + 1) ≤ 2 ^ (fw - 1) + 3 * diagN ar q fw g x ∧
    2 ^ (fw - 1) ≤ digitN fw i (2 * x + 1) + 3 * diagN ar q fw g x)

/-- The two fields of a non-rectangle hold the offset `2^(fw-1)` (the value `0`). -/
def PadOkN (fw i x : ℕ) : Prop := digitN fw i (2 * x) = 2 ^ (fw - 1) ∧ digitN fw i (2 * x + 1) = 2 ^
    (fw - 1)

/-- The two fields at the quadruple index `x` are valid. -/
def FieldOkN (ar q fw g i x : ℕ) : Prop := if IsRectN g x then RectOkN ar q fw g i x else PadOkN fw
    i x

/-- **A valid choice code** (`ValidChoiceCode`), from the array. -/
def ValidN (ar q fw g i : ℕ) : Prop := i < 2 ^ choiceWidth g fw ∧ ∀ x < g ^ 4, FieldOkN ar q fw g i
    x

instance (ar q fw g i x : ℕ) : Decidable (RectOkN ar q fw g i x) := by
  unfold RectOkN; infer_instance

instance (fw i x : ℕ) : Decidable (PadOkN fw i x) := by unfold PadOkN; infer_instance

instance (ar q fw g i x : ℕ) : Decidable (FieldOkN ar q fw g i x) := by
  unfold FieldOkN; infer_instance

instance (ar q fw g i : ℕ) : Decidable (ValidN ar q fw g i) := by unfold ValidN; infer_instance

/-- The digit of the code of a decoded choice: the digit of the code at the fields of rectangles,
the offset elsewhere. -/
theorem choiceDigit_decode (t : ℕ) :
    choiceDigit g fw (decodeChoice g fw i) t =
      if ∃ r : Rect g, rectIdx r = t / 2 then digitN fw i t else 2 ^ (fw - 1) := by
  unfold choiceDigit
  by_cases h1 : ∃ r : Rect g, 2 * rectIdx r = t
  · rw [dite_eq_left h1, ite_eq_left ⟨h1.choose, by have := h1.choose_spec; omega⟩]
    show (field fw i (2 * rectIdx h1.choose) + 2 ^ (fw - 1)).toNat = _
    rw [h1.choose_spec, field_eq_digitN, sub_add_cancel, Int.toNat_natCast]
  · rw [dite_eq_right h1]
    by_cases h2 : ∃ r : Rect g, 2 * rectIdx r + 1 = t
    · rw [dite_eq_left h2, ite_eq_left ⟨h2.choose, by have := h2.choose_spec; omega⟩]
      show (field fw i (2 * rectIdx h2.choose + 1) + 2 ^ (fw - 1)).toNat = _
      rw [h2.choose_spec, field_eq_digitN, sub_add_cancel, Int.toNat_natCast]
    · rw [dite_eq_right h2, ite_eq_right (fun ⟨r, hr⟩ => by
        rcases Nat.even_or_odd' t with ⟨m, hm | hm⟩
        · exact h1 ⟨r, by omega⟩
        · exact h2 ⟨r, by omega⟩), zero_add, two_pow_int, Int.toNat_natCast]

private theorem choiceCode_decode_iff (hfw : 1 ≤ fw) :
    choiceCode g fw (decodeChoice g fw i) = i ↔
      i < 2 ^ choiceWidth g fw ∧ ∀ x < g ^ 4, ¬ IsRectN g x → PadOkN fw i x := by
  have hQ : 2 ^ (fw - 1) < 2 ^ fw := Nat.pow_lt_pow_right (by norm_num) (by omega)
  rw [choiceCode_eq_packN, packN_eq_iff fun t _ => by
    rw [choiceDigit_decode]; split_ifs
    · exact digitN_lt _ _ _
    · exact hQ]
  refine and_congr Iff.rfl ⟨fun H x hx hn => ?_, fun H t ht => ?_⟩
  · have hnr : ∀ t, t / 2 = x → ¬ ∃ r : Rect g, rectIdx r = t / 2 := fun t ht ⟨r, hr⟩ =>
      hn (exists_rectIdx_iff.mp ⟨r, hr.trans ht⟩).2
    have e1 := H (2 * x) (by omega)
    have e2 := H (2 * x + 1) (by omega)
    rw [choiceDigit_decode, ite_eq_right (hnr _ (by omega))] at e1 e2
    exact ⟨e1, e2⟩
  · rw [choiceDigit_decode]
    split_ifs with hr
    · rfl
    · have hn : ¬ IsRectN g (t / 2) := fun h' => hr (exists_rectIdx_iff.mpr ⟨by omega, h'⟩)
      obtain ⟨p1, p2⟩ := H (t / 2) (by omega) hn
      rcases Nat.even_or_odd' t with ⟨m, hm | hm⟩
      · rw [show t = 2 * (t / 2) by omega]; exact p1
      · rw [show t = 2 * (t / 2) + 1 by omega]; exact p2

private theorem mem_choices_iff (h : Fits fw a) :
    decodeChoice g fw i ∈ choices a ↔
      ∀ r : Rect g, RectOkN (arrN (g * g) fw (extN a)) (g * g) fw g i (rectIdx r) := by
  simp only [choices, Fintype.mem_piFinset, mem_product, mem_filter, mem_Icc]
  refine forall_congr' fun r => ?_
  have e1 : (decodeChoice g fw i r).1 = (digitN fw i (2 * rectIdx r) : ℤ) -
      ((2 ^ (fw - 1) : ℕ) : ℤ) :=
    grade_eq r
  have e2 : (decodeChoice g fw i r).2 =
      (digitN fw i (2 * rectIdx r + 1) : ℤ) - ((2 ^ (fw - 1) : ℕ) : ℤ) := by
    rw [← two_pow_int]; rfl
  rw [e1, e2, ← diagN_eq h r, RectOkN, Int.even_iff]
  generalize 2 ^ (fw - 1) = Q
  generalize digitN fw i (2 * rectIdx r) = D
  generalize digitN fw i (2 * rectIdx r + 1) = C
  generalize diagN (arrN (g * g) fw (extN a)) (g * g) fw g (rectIdx r) = H
  omega

/-- **`ValidN` decides `ValidChoiceCode`** when the budgets fit in the field width. -/
theorem validN_iff (h : Fits fw a) (hfw : 1 ≤ fw) :
    ValidN (arrN (g * g) fw (extN a)) (g * g) fw g i ↔ ValidChoiceCode a fw i := by
  rw [ValidChoiceCode, mem_choices_iff h, choiceCode_decode_iff hfw,
    forall_rect (RectOkN (arrN (g * g) fw (extN a)) (g * g) fw g i), ValidN]
  unfold FieldOkN
  constructor
  · rintro ⟨hi, H⟩
    refine ⟨fun x hx hr => ?_, hi, fun x hx hn => ?_⟩
    · have := H x hx; rwa [ite_eq_left hr] at this
    · have := H x hx; rwa [ite_eq_right hn] at this
  · rintro ⟨H1, hi, H2⟩
    refine ⟨hi, fun x hx => ?_⟩
    split_ifs with hr
    · exact H1 x hx hr
    · exact H2 x hx hr

/-! ### Index widths -/

/-- The offset of the label to `u` in an argument code of node `v` (`argOffset`). -/
def argOffN (ar q fw v u : ℕ) : ℕ :=
  ∑ u' ∈ range u, if u' < q ∧ v < q then
    (if u' = v then 0 else codeWidth (budgetN ar q fw v u')) else 0

/-- The width of an argument code of node `w` (`argWidth`). -/
def argWidN (ar q fw w : ℕ) : ℕ := argOffN ar q fw w q

/-- The offset of the slice of position `p` in a code of copies (`sliceOffset`). -/
def sliceOffN (ar q fw : ℕ) (nodes : ℕ → ℕ) (p : ℕ) : ℕ :=
  ∑ p' ∈ range p, argWidN ar q fw (nodes p')

/-- The slice of position `p` of a code of copies (`slice`). -/
def sliceN (ar q fw : ℕ) (nodes : ℕ → ℕ) (ξ p : ℕ) : ℕ :=
  ξ / 2 ^ sliceOffN ar q fw nodes p % 2 ^ argWidN ar q fw (nodes p)

/-- The width of a code of copies held by `n` nodes (`copiesWidth`). -/
def copiesWidN (ar q fw : ℕ) (nodes : ℕ → ℕ) (n : ℕ) : ℕ := sliceOffN ar q fw nodes n

/-- The width of the copies of node `v` of the child at the choice code `i` (`xiWidth`): the
holders are the row `v` of the parent grid (`v·g + p`) or its column `v` (`p·g + v`). -/
def xiWidN (ar q fw g i v : ℕ) : ℕ :=
  copiesWidN ar q fw (fun p => if orientN ar q fw g i then v * g + p else p * g + v) g

end Cslib.Complexity.NtimeDspace.Cube.Num
