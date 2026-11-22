/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.FirstClique
public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.RowCut
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# The one-bit routing polynomial and the worked examples of §5

The specialized examples use the views `exV`: `x` and `y` each send one request of type
`0`, and `u` and `v` each receive one. In Lean a view is `(out, in)`, so
`exV = views ({0}, ∅) ({0}, ∅) (∅, {0}) (∅, {0})` in the corner order `x, y, u, v`; every view has
weight `1`, so `a = b = 1` and `H = 2`.

The general one-bit example uses `oneBitViews`, with `enc 1` at the upper corners and reversed
labels at the lower corners. `oneBit_piece` proves the three-pairing formula. Its only nonzero
coefficients are at `-2, 0, 2`; `oneBit_coeff_zero` is twice the indicator that the two row sums
agree. The six `oneBitRow_*_rank` and `oneBitCol_*_rank` theorems give the ranks of their rational
flattenings, and `oneBitCrossingRow_rank` and `oneBitCrossingCol_rank` give rank four for the
crossing. The proofs use surjective pullbacks of diagonal matrices. `oneBitViews_transpose`
records the complemented exchanged bits required when transposing encoded views.

## The example after Lemma 5.3 ("A small example shows both lemmas at work")

* `ex_piece` (this is `piece_example` of `PieceFacts.lean`): `Π_{x,y,u,v} = 2 - z²`.
* `ex_coeff_zero`, `ex_coeff_two`, `ex_pieces_sum`: `Π_0 = 2`, `Π_2 = -1`, and their sum is the
  crossing, which holds (`ex_crossing`); `ex_eval_one` is Lemma 5.2 at work.
* `ex_piece_transpose`: transposed, `Π_{x,u,y,v} = 2 - z⁻²` (Lemma 5.3 at work).

## The example after Corollary 5.5

A message is `m = (η, ζ)`, `η` sent downward and `ζ` upward across the row cut. The paper writes
`η = {0, n}` for the message of the row cut, with `ζ = ∅`.

* Row cut: `ex_nUp_00`, `ex_nDown_00`: `N↑(x, y; ({0,0}, ∅)) = 1 - z²`,
  `N↓(u, v; ({0,0}, ∅)) = 2`; `ex_nUp_01`, `ex_nDown_01`: `N↑(x, y; ({0,1}, ∅)) = (1 - z²) z`,
  `N↓(u, v; ({0,1}, ∅)) = z`. `ex_nUp_row_support`: every other message of weight at most
  `H + k/2 = 3` has `N↑(x, y; m) = 0`.
* Column cut: `ex_nUp_col`, `ex_nDown_col`: `N↑(x, u; ∅) = 1 - z⁻²` and `N↓(y, v; ∅) = 1`;
  `ex_nUp_col_support`: every nonempty message of weight at most `H - k/2 = 1` has
  `N↑(x, u; m) = 0`. In Lean, `N↑(x, u; m)` is `nUp (V .x) (V .u) m`: the transposed rectangle
  puts `u` in the place of the upper corner `y`.
* The split contributions. `rowSplit V H k c` is the contribution of the split `c` to the row cut
  of Corollary 5.5, `∑_{m ∈ Λ_≤(H + k/2)} [z^{k-c}] N↑(x, y; m) · [z^c] N↓(u, v; m)`, and
  `colSplit V H k c` that to the column cut. `rowCut_splits` and `colCut_splits` (for any views
  with `wt x = wt v = a` and `wt y = wt u = b`) show that `Π_k` is the sum of the split
  contributions over a window of splits; this is Corollary 5.5 with the sums over `m` and `c`
  exchanged, since outside the window of each `m` the terms vanish (Lemma 5.4).
* `ex_rowSplit`: the row cut at `k = 2` contributes `-2` at `c = 0`, `1` at `c = 1`, and `0` at
  every other split; `ex_colSplit`: the column cut contributes `-1` at `c = 0` and `0` elsewhere.
  `ex_rowCut_total`, `ex_colCut_total`: both totals are `Π_2 = -1`.
* `ex_mixed`: the column cut at `c = 0` plus the row cut at `c = 1` gives `0`.

The paper's numbers are confirmed exactly.

## General tool

* `card_eq_of_transport_ne_zero`: a nonzero transport sum has as many sources as targets.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset LaurentPolynomial

/-! ### Tools -/

/-- A nonzero transport sum has as many sources as targets. -/
theorem card_eq_of_transport_ne_zero {P : Type} [DecidableEq P] (R : P → ℕ → P → ℕ → Lp)
    (src : Multiset (P × ℕ)) :
    ∀ tgt : Multiset (P × ℕ), transport src tgt R ≠ 0 →
      Multiset.card src = Multiset.card tgt := by
  induction src using Multiset.induction_on with
  | empty =>
    intro tgt h
    rw [transport_zero] at h
    split_ifs at h with h'
    · subst h'; rfl
    · exact absurd rfl h
  | cons s src ih =>
    intro tgt h
    rw [transport_cons] at h
    obtain ⟨t, ht, h1⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have ht' := Multiset.mem_toFinset.mp ht
    have hi := ih _ (right_ne_zero_of_mul h1)
    rw [Multiset.card_cons, hi]
    exact Multiset.card_erase_add_one ht'

theorem transport_singleton {P : Type} [DecidableEq P] (s : P × ℕ) (tgt : Multiset (P × ℕ))
    (R : P → ℕ → P → ℕ → Lp) :
    transport {s} tgt R =
      ∑ t ∈ tgt.toFinset, R s.1 s.2 t.1 t.2 * (if tgt.erase t = 0 then 1 else 0) := by
  rw [← Multiset.cons_zero, transport_cons]
  simp only [transport_zero]

theorem coeff_one_Lp (e : ℤ) : (1 : Lp).coeff e = if (0 : ℤ) = e then 1 else 0 := by
  rw [← T_zero, T_apply]

theorem coeff_two_Lp (e : ℤ) : (2 : Lp).coeff e = if (0 : ℤ) = e then 2 else 0 := by
  rw [← one_add_one_eq_two, AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_one_Lp]
  split_ifs <;> norm_num

theorem C_zero_zero : Cube.C 0 0 = 1 := by simp [Cube.C, chi, ip]

theorem C_zero_one : Cube.C 0 1 = T 1 := by simp [Cube.C, chi, ip, d]

/-! ### The split contributions of Corollary 5.5 -/

/-- The contribution of the split `c` to the row cut of Corollary 5.5 for `Π_k`:
`∑_{m ∈ Λ_≤(H + k/2)} [z^{k-c}] N↑(x, y; m) · [z^c] N↓(u, v; m)`. -/
noncomputable def rowSplit (V : Corner → Label) (H : ℕ) (k c : ℤ) : ℤ :=
  ∑ m ∈ labelsLE ((H : ℤ) + k / 2).toNat,
    (nUp (V .x) (V .y) m).coeff (k - c) * (nDown (V .u) (V .v) m).coeff c

/-- The contribution of the split `c` to the column cut of Corollary 5.5 for `Π_k`:
`∑_{m ∈ Λ_≤(H - k/2)} [z^{-k-c}] N↑(x, u; m) · [z^c] N↓(y, v; m)`. -/
noncomputable def colSplit (V : Corner → Label) (H : ℕ) (k c : ℤ) : ℤ :=
  ∑ m ∈ labelsLE ((H : ℤ) - k / 2).toNat,
    (nUp (V .x) (V .u) m).coeff (-k - c) * (nDown (V .y) (V .v) m).coeff c

/-- **The row cut, split by split.** `Π_k` is the sum of the contributions of the splits
`-H ≤ c ≤ H + k`. -/
theorem rowCut_splits (V : Corner → Label) (a b : ℕ) (hx : labelWt (V .x) = a)
    (hv : labelWt (V .v) = a) (hy : labelWt (V .y) = b) (hu : labelWt (V .u) = b) (k : ℤ) :
    (piece V).coeff k = ∑ c ∈ Icc (-((a + b : ℕ) : ℤ)) ((a + b : ℕ) + k), rowSplit V (a + b) k
        c := by
  rw [rowCut V a b hx hv hy hu k]
  unfold rowSplit
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr (by push_cast; rfl) fun m _ => ?_
  apply Finset.sum_subset
  · intro c hc
    simp only [mem_Icc] at hc ⊢
    push_cast
    omega
  · intro c _ hc
    rw [mem_Icc] at hc
    by_cases h1 : (labelWt m : ℤ) - (a + b) ≤ c
    · have : (nUp (V .x) (V .y) m).coeff (k - c) = 0 := by
        by_contra hne
        have := nUp_lower _ _ m _ hne
        rw [hx, hy] at this
        exact hc ⟨h1, by omega⟩
      rw [this, zero_mul]
    · have : (nDown (V .u) (V .v) m).coeff c = 0 := by
        by_contra hne
        have := nDown_lower _ _ m _ hne
        rw [hu, hv] at this
        omega
      rw [this, mul_zero]

/-- **The column cut, split by split.** For even `k`, `Π_k` is the sum of the contributions of
the splits `-H ≤ c ≤ H - k`. -/
theorem colCut_splits (V : Corner → Label) (a b : ℕ) (hx : labelWt (V .x) = a)
    (hv : labelWt (V .v) = a) (hy : labelWt (V .y) = b) (hu : labelWt (V .u) = b) (k : ℤ)
    (hk : Even k) :
    (piece V).coeff k = ∑ c ∈ Icc (-((a + b : ℕ) : ℤ)) ((a + b : ℕ) - k), colSplit V (a + b) k
        c := by
  rw [colCut V a b hx hv hy hu k hk]
  unfold colSplit
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr (by push_cast; rfl) fun m _ => ?_
  apply Finset.sum_subset
  · intro c hc
    simp only [mem_Icc] at hc ⊢
    push_cast
    omega
  · intro c _ hc
    rw [mem_Icc] at hc
    by_cases h1 : (labelWt m : ℤ) - (a + b) ≤ c
    · have : (nUp (V .x) (V .u) m).coeff (-k - c) = 0 := by
        by_contra hne
        have := nUp_lower _ _ m _ hne
        rw [hx, hu] at this
        exact hc ⟨h1, by omega⟩
      rw [this, zero_mul]
    · have : (nDown (V .y) (V .v) m).coeff c = 0 := by
        by_contra hne
        have := nDown_lower _ _ m _ hne
        rw [hy, hv] at this
        omega
      rw [this, mul_zero]

/-! ### The example after Lemma 5.3 -/

/-- The views of the examples: `x` and `y` each send one request of type `0`, and `u` and `v`
each receive one. -/
def exV : Corner → Label := views ({0}, 0) ({0}, 0) (0, {0}) (0, {0})

theorem exV_wt (c : Corner) : labelWt (exV c) = 1 := by
  cases c <;> simp [exV, views, labelWt]

/-- `Π_{x,y,u,v} = 2 - z²` (`piece_example`). -/
theorem ex_piece : piece exV = 2 - T 2 := piece_example

theorem ex_coeff_zero : (piece exV).coeff 0 = 2 := by
  rw [ex_piece, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_two_Lp, T_apply]; norm_num

theorem ex_coeff_two : (piece exV).coeff 2 = -1 := by
  rw [ex_piece, AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_two_Lp, T_apply]; norm_num

theorem ex_crossing : crossing exV := ⟨rfl, rfl, rfl, rfl⟩

/-- The pieces `Π_0 = 2` and `Π_2 = -1` sum to the crossing. -/
theorem ex_pieces_sum :
    (piece exV).coeff 0 + (piece exV).coeff 2 = if crossing exV then 1 else 0 := by
  rw [ex_coeff_zero, ex_coeff_two]; simp [ex_crossing]

/-- Lemma 5.2 at work: `Π_{x,y,u,v}(1) = [x = v][y = u] = 1`. -/
theorem ex_eval_one : eval₂ (RingHom.id ℤ) 1 (piece exV) = 1 := by
  rw [piece_eval_one exV (by rw [exV_wt, exV_wt])]; simp [ex_crossing]

/-- Lemma 5.3 at work: transposed, `Π_{x,u,y,v} = 2 - z⁻²`. -/
theorem ex_piece_transpose : piece (transposeView exV) = 2 - T (-2) := by
  rw [piece_transpose, ex_piece, map_sub, invert_T, map_ofNat]

/-! ### The example after Corollary 5.5: the half-routing sums -/

theorem ex_nUp_00 : nUp (exV .x) (exV .y) ({0, 0}, 0) = 1 - T 2 := by
  simp [nUp, exV, views, located, transport_cons, transport_singleton, upRule, eqL, C_zero_zero,
    oneSubZ2]

theorem ex_nDown_00 : nDown (exV .u) (exV .v) ({0, 0}, 0) = 2 := by
  simp [nDown, exV, views, located, transport_cons, transport_singleton, downRule, eqL,
    C_zero_zero]
  norm_num

theorem ex_nUp_01 : nUp (exV .x) (exV .y) ({0, 1}, 0) = (1 - T 2) * T 1 := by
  simp [nUp, exV, views, located, transport_cons, transport_singleton, upRule, eqL, C_zero_one,
    C_zero_zero, oneSubZ2]

theorem ex_nDown_01 : nDown (exV .u) (exV .v) ({0, 1}, 0) = T 1 := by
  simp [nDown, exV, views, located, transport_cons, transport_singleton, downRule, eqL,
    C_zero_one, C_zero_zero]

theorem ex_nUp_col : nUp (exV .x) (exV .u) (0, 0) = 1 - T (-2) := by
  simp [nUp, exV, views, located, transport_singleton, upRule, C_zero_zero, oneSubZm2, bar]

theorem ex_nDown_col : nDown (exV .y) (exV .v) (0, 0) = 1 := by
  simp [nDown, exV, views, located, transport_singleton, downRule, C_zero_zero, bar]

/-- On the row cut, the only messages of weight at most `3` with `N↑(x, y; m) ≠ 0` are
`({0,0}, ∅)` and `({0,1}, ∅)`. -/
theorem ex_nUp_row_support {m : Label} (hm : labelWt m ≤ 3)
    (h : nUp (exV .x) (exV .y) m ≠ 0) : m = ({0, 0}, 0) ∨ m = ({0, 1}, 0) := by
  unfold nUp at h
  have hc := card_eq_of_transport_ne_zero _ _ _ h
  obtain ⟨η, ζ⟩ := m
  simp only [exV, views, located, Multiset.card_add, Multiset.card_map,
    Multiset.card_singleton, Multiset.card_zero] at hc
  have h1 := card_le_wt η
  have h2 := card_le_wt ζ
  unfold labelWt at hm
  have hζ : ζ = 0 := Multiset.card_eq_zero.mp (by simp only at hm; omega)
  subst hζ
  simp only [Multiset.card_zero, add_zero] at hc
  obtain ⟨p, q, rfl⟩ := Multiset.card_eq_two.mp (show Multiset.card η = 2 by omega)
  simp only [Multiset.insert_eq_cons, wt_cons, wt_singleton, wt_zero] at hm
  have hpq : p + q ≤ 1 := by omega
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rcases Nat.eq_zero_or_pos q with rfl | hq
    · left; rfl
    · right; rw [show q = 1 by omega]
  · right
    rw [show p = 1 by omega, show q = 0 by omega, Multiset.pair_comm]

/-- On the column cut, the only message of weight at most `1` with `N↑(x, u; m) ≠ 0` is the
empty message. -/
theorem ex_nUp_col_support {m : Label} (hm : labelWt m ≤ 1)
    (h : nUp (exV .x) (exV .u) m ≠ 0) : m = (0, 0) := by
  unfold nUp at h
  have hc := card_eq_of_transport_ne_zero _ _ _ h
  obtain ⟨η, ζ⟩ := m
  simp only [exV, views, located, Multiset.card_add, Multiset.card_map,
    Multiset.card_singleton, Multiset.card_zero] at hc
  have h1 := card_le_wt η
  have h2 := card_le_wt ζ
  unfold labelWt at hm
  simp only at hm hc
  rw [Multiset.card_eq_zero.mp (by omega : Multiset.card η = 0),
    Multiset.card_eq_zero.mp (by omega : Multiset.card ζ = 0)]

/-! ### The example after Corollary 5.5: the split contributions -/

/-- The row cut at `k = 2`, split by split: `-2` at `c = 0`, `1` at `c = 1`, `0` elsewhere. -/
theorem ex_rowSplit (c : ℤ) : rowSplit exV 2 2 c = if c = 0 then -2 else if c =
    1 then 1 else 0 := by
  have hidx : (((2 : ℕ) : ℤ) + 2 / 2).toNat = 3 := by decide
  unfold rowSplit
  rw [hidx]
  have hne : (({0, 0}, 0) : Label) ≠ ({0, 1}, 0) := by
    intro h
    have := congrArg (fun m : Label => m.1.count 1) h
    simp at this
  have hmem : ∀ m : Label, labelWt m ≤ 3 → m ∈ labelsLE 3 := fun m h => mem_labelsLE.mpr h
  rw [Finset.sum_eq_add_of_mem (({0, 0}, 0) : Label) ({0, 1}, 0)
    (hmem _ (by simp [labelWt])) (hmem _ (by simp [labelWt])) hne]
  · rw [ex_nUp_00, ex_nDown_00, ex_nUp_01, ex_nDown_01,
      show (1 - T 2 : Lp) * T 1 = T 1 - T 3 by rw [sub_mul, one_mul, ← T_add]; norm_num]
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_one_Lp, coeff_two_Lp,
      T_apply]
    split_ifs <;> omega
  · rintro m hm ⟨h1, h2⟩
    have : nUp (exV .x) (exV .y) m = 0 := by
      by_contra hn
      rcases ex_nUp_row_support (mem_labelsLE.mp hm) hn with h | h
      · exact h1 h
      · exact h2 h
    rw [this, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_mul]

/-- The column cut at `k = 2`, split by split: `-1` at `c = 0`, `0` elsewhere. -/
theorem ex_colSplit (c : ℤ) : colSplit exV 2 2 c = if c = 0 then -1 else 0 := by
  have hidx : (((2 : ℕ) : ℤ) - 2 / 2).toNat = 1 := by decide
  unfold colSplit
  rw [hidx, Finset.sum_eq_single ((0, 0) : Label)]
  · rw [ex_nUp_col, ex_nDown_col]
    simp only [AddMonoidAlgebra.coeff_sub, Finsupp.sub_apply, coeff_one_Lp, T_apply]
    split_ifs <;> omega
  · intro m hm hm0
    have : nUp (exV .x) (exV .u) m = 0 := by
      by_contra hn
      exact hm0 (ex_nUp_col_support (mem_labelsLE.mp hm) hn)
    rw [this, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, zero_mul]
  · intro h
    exact absurd (mem_labelsLE.mpr (by simp [labelWt])) h

/-- The total of the row cut is `Π_2 = -1`. -/
theorem ex_rowCut_total :
    (piece exV).coeff 2 = ∑ c ∈ Icc (-2 : ℤ) 4, rowSplit exV 2 2 c ∧
      ∑ c ∈ Icc (-2 : ℤ) 4, rowSplit exV 2 2 c = rowSplit exV 2 2 0 + rowSplit exV 2 2 1 ∧
      rowSplit exV 2 2 0 + rowSplit exV 2 2 1 = -1 := by
  have h := rowCut_splits exV 1 1 (exV_wt _) (exV_wt _) (exV_wt _) (exV_wt _) 2
  refine ⟨h, ?_, ?_⟩
  · refine Finset.sum_eq_add_of_mem 0 1 (by simp) (by simp) (by norm_num) ?_
    rintro c - ⟨h0, h1⟩
    simp [ex_rowSplit, h0, h1]
  · rw [ex_rowSplit, ex_rowSplit]; norm_num

/-- The total of the column cut is `Π_2 = -1`. -/
theorem ex_colCut_total :
    (piece exV).coeff 2 = ∑ c ∈ Icc (-2 : ℤ) 0, colSplit exV 2 2 c ∧
      ∑ c ∈ Icc (-2 : ℤ) 0, colSplit exV 2 2 c = colSplit exV 2 2 0 ∧
      colSplit exV 2 2 0 = -1 := by
  have h := colCut_splits exV 1 1 (exV_wt _) (exV_wt _) (exV_wt _) (exV_wt _) 2 even_two
  refine ⟨h, ?_, ?_⟩
  · refine Finset.sum_eq_single 0 (fun c _ h0 => by simp [ex_colSplit, h0]) (by simp)
  · rw [ex_colSplit]; norm_num

/-- **The two cuts agree only after the sum over the splits**: the column cut at `c = 0` and
the row cut at `c = 1` would give `0`, not `Π_2 = -1`. -/
theorem ex_mixed : colSplit exV 2 2 0 + rowSplit exV 2 2 1 = 0 := by
  rw [ex_colSplit, ex_rowSplit]; norm_num

/-! ### All one-bit views -/

/-- The one-bit views use `enc` at the upper corners and its reversal at the lower corners.
Thus `true` sends a request upstairs and receives a request downstairs. -/
def oneBitViews (x y u v : Bool) : Corner → Label :=
  views (enc 1 (fun _ => x)) (enc 1 (fun _ => y))
    (enc 1 (fun _ => u)).swap (enc 1 (fun _ => v)).swap

/-- The one-bit routing polynomial is the sum of the three pairings of the four requests.
The vertical and horizontal pairings carry `1-z²` and `1-z⁻²`, respectively. -/
theorem oneBit_piece (x y u v : Bool) :
    piece (oneBitViews x y u v) =
      (if x = v ∧ y = u then 1 else 0) +
      (1 - T 2) * (if x = u ∧ y = v then 1 else 0) +
      (1 - T (-2)) * (if x ≠ y ∧ u ≠ v then 1 else 0) := by
  cases x <;> cases y <;> cases u <;> cases v <;>
    simp [piece, oneBitViews, enc, sourcesOf, targetsOf, views, located,
      transport_cons, transport_singleton, transport_zero, rule, eqL, C_zero_zero, bar,
      oneSubZ2, oneSubZm2] <;>
    ring

/-- The central coefficient is twice the indicator of conservation of the two input bits. -/
theorem oneBit_coeff_zero (x y u v : Bool) :
    (piece (oneBitViews x y u v)).coeff 0 =
      if x.toNat + y.toNat = u.toNat + v.toNat then 2 else 0 := by
  rw [oneBit_piece]
  cases x <;> cases y <;> cases u <;> cases v <;>
    norm_num [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
      Finsupp.add_apply, Finsupp.sub_apply, coeff_one_Lp, T_apply]

/-- The positive coefficient is minus the vertical-pairing indicator. -/
theorem oneBit_coeff_two (x y u v : Bool) :
    (piece (oneBitViews x y u v)).coeff 2 = if x = u ∧ y = v then -1 else 0 := by
  rw [oneBit_piece]
  split_ifs <;>
    norm_num [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
      Finsupp.add_apply, Finsupp.sub_apply, coeff_one_Lp, T_apply]

/-- The negative coefficient is minus the horizontal-pairing indicator. -/
theorem oneBit_coeff_neg_two (x y u v : Bool) :
    (piece (oneBitViews x y u v)).coeff (-2) = if x ≠ y ∧ u ≠ v then -1 else 0 := by
  rw [oneBit_piece]
  split_ifs <;>
    norm_num [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
      Finsupp.add_apply, Finsupp.sub_apply, coeff_one_Lp, T_apply]

/-- There are no other coefficients in the one-bit routing polynomial. -/
theorem oneBit_coeff_eq_zero (x y u v : Bool) (k : ℤ)
    (h0 : k ≠ 0) (h2 : k ≠ 2) (hn2 : k ≠ -2) :
    (piece (oneBitViews x y u v)).coeff k = 0 := by
  rw [oneBit_piece]
  split_ifs <;>
    simp [AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_sub,
      Finsupp.add_apply, Finsupp.sub_apply, coeff_one_Lp, T_apply,
      Ne.symm h0, Ne.symm h2, Ne.symm hn2]

/-- In bit coordinates, transposing views complements the two exchanged bits. -/
theorem oneBitViews_transpose (x y u v : Bool) :
    transposeView (oneBitViews x y u v) = oneBitViews x (!u) (!y) v := by
  funext c
  cases c <;> cases y <;> cases u <;>
    simp [transposeView, oneBitViews, views, swapYU, enc]

/-- The crossing predicate on these encoded bits is the usual pair of diagonal equalities. -/
theorem oneBit_crossing (x y u v : Bool) :
    crossing (oneBitViews x y u v) ↔ x = v ∧ y = u := by
  cases x <;> cases y <;> cases u <;> cases v <;>
    simp [crossing, oneBitViews, views, enc]

/-- The original example is the all-true bit assignment. -/
theorem oneBitViews_true : oneBitViews true true true true = exV := by
  funext c
  cases c <;> simp [oneBitViews, exV, views, enc]

/-- Its transpose has bits `(1,0,0,1)`, rather than the unchanged all-true assignment. -/
theorem oneBitViews_true_transpose :
    transposeView exV = oneBitViews true false false true := by
  rw [← oneBitViews_true, oneBitViews_transpose]
  rfl

/-! ### Ranks of the two flattenings over the rationals -/

/-- The row flattening, with rows `(x,y)` and columns `(u,v)`. -/
noncomputable def oneBitRow (k : ℤ) : Matrix (Bool × Bool) (Bool × Bool) ℚ :=
  fun r c => ((piece (oneBitViews r.1 r.2 c.1 c.2)).coeff k : ℚ)

/-- The column flattening, with rows `(x,u)` and columns `(y,v)`. -/
noncomputable def oneBitCol (k : ℤ) : Matrix (Bool × Bool) (Bool × Bool) ℚ :=
  fun r c => ((piece (oneBitViews r.1 c.1 r.2 c.2)).coeff k : ℚ)

/-- Pulling a matrix back along surjective row and column maps preserves its rank:
the original matrix is recovered by choosing one representative of each index. -/
private theorem rank_submatrix_surjective {m n m' n' : Type}
    [Fintype m] [Fintype n] [Fintype m'] [Fintype n']
    (A : Matrix m n ℚ) (r : m' → m) (c : n' → n)
    (hr : Function.Surjective r) (hc : Function.Surjective c) :
    (A.submatrix r c).rank = A.rank := by
  obtain ⟨r', hr'⟩ := hr.hasRightInverse
  obtain ⟨c', hc'⟩ := hc.hasRightInverse
  apply le_antisymm (A.rank_submatrix_le r c)
  have h := (A.submatrix r c).rank_submatrix_le r' c'
  have heq : (A.submatrix r c).submatrix r' c' = A := by
    ext i j
    exact congrArg₂ A (hr' i) (hc' j)
  rwa [heq] at h

/-- The number of ones in a pair of bits. Its three fibers are the three row blocks. -/
private def bitSum (p : Bool × Bool) : Fin 3 :=
  ⟨p.1.toNat + p.2.toNat, by rcases p with ⟨a, b⟩; cases a <;> cases b <;> decide⟩

private theorem bitSum_surjective : Function.Surjective bitSum := by
  intro i
  fin_cases i
  · exact ⟨(false, false), rfl⟩
  · exact ⟨(false, true), rfl⟩
  · exact ⟨(true, true), rfl⟩

private def bitEqual (p : Bool × Bool) : Bool := p.1 == p.2

private theorem bitEqual_surjective : Function.Surjective bitEqual := by
  intro i
  cases i
  · exact ⟨(false, true), rfl⟩
  · exact ⟨(false, false), rfl⟩

private def bitDifferent (p : Bool × Bool) : Bool := !(p.1 == p.2)

private theorem bitDifferent_surjective : Function.Surjective bitDifferent := by
  intro i
  cases i
  · exact ⟨(false, false), rfl⟩
  · exact ⟨(false, true), rfl⟩

private theorem diagonal_pair_rank (c : ℚ) (hc : c ≠ 0) :
    (Matrix.diagonal (fun _ : Bool × Bool => c)).rank = 4 := by
  simp [Matrix.rank_diagonal, hc]

private theorem diagonal_three_rank (c : ℚ) (hc : c ≠ 0) :
    (Matrix.diagonal (fun _ : Fin 3 => c)).rank = 3 := by
  simp [Matrix.rank_diagonal, hc]

private theorem diagonal_true_rank :
    (Matrix.diagonal (fun b : Bool => if b then (-1 : ℚ) else 0)).rank = 1 := by
  rw [Matrix.rank_diagonal]
  norm_num [Fintype.card_subtype]

/-- `Π₂` is minus the identity on the row cut. -/
theorem oneBitRow_two_rank : (oneBitRow 2).rank = 4 := by
  have h : oneBitRow 2 = Matrix.diagonal (fun _ : Bool × Bool => (-1 : ℚ)) := by
    ext ⟨x, y⟩ ⟨u, v⟩
    simp [oneBitRow, oneBit_coeff_two, Matrix.diagonal, Prod.mk.injEq]
  rw [h]
  exact diagonal_pair_rank _ (by norm_num)

/-- On the column cut `Π₂` has just one nonzero rectangular block. -/
theorem oneBitCol_two_rank : (oneBitCol 2).rank = 1 := by
  have h : oneBitCol 2 =
      (Matrix.diagonal (fun b : Bool => if b then (-1 : ℚ) else 0)).submatrix
        bitEqual bitEqual := by
    ext ⟨x, u⟩ ⟨y, v⟩
    cases x <;> cases y <;> cases u <;> cases v <;>
      simp [oneBitCol, oneBit_coeff_two, Matrix.submatrix, Matrix.diagonal, bitEqual]
  rw [h, rank_submatrix_surjective _ _ _ bitEqual_surjective bitEqual_surjective]
  exact diagonal_true_rank

/-- On the row cut `Π₋₂` has just one nonzero rectangular block. -/
theorem oneBitRow_neg_two_rank : (oneBitRow (-2)).rank = 1 := by
  have h : oneBitRow (-2) =
      (Matrix.diagonal (fun b : Bool => if b then (-1 : ℚ) else 0)).submatrix
        bitDifferent bitDifferent := by
    ext ⟨x, y⟩ ⟨u, v⟩
    cases x <;> cases y <;> cases u <;> cases v <;>
      simp [oneBitRow, oneBit_coeff_neg_two, Matrix.submatrix, Matrix.diagonal, bitDifferent]
  rw [h, rank_submatrix_surjective _ _ _ bitDifferent_surjective bitDifferent_surjective]
  exact diagonal_true_rank

/-- On the column cut `Π₋₂` is a signed permutation matrix (complement both column bits). -/
theorem oneBitCol_neg_two_rank : (oneBitCol (-2)).rank = 4 := by
  let flip : Bool × Bool → Bool × Bool := fun p => (!p.1, !p.2)
  have hf : Function.Surjective flip := by
    intro p
    exact ⟨flip p, by simp [flip]⟩
  have h : oneBitCol (-2) =
      (Matrix.diagonal (fun _ : Bool × Bool => (-1 : ℚ))).submatrix id flip := by
    ext ⟨x, u⟩ ⟨y, v⟩
    cases x <;> cases y <;> cases u <;> cases v <;>
      simp [oneBitCol, oneBit_coeff_neg_two, Matrix.submatrix, Matrix.diagonal, flip]
  rw [h, rank_submatrix_surjective _ _ _ Function.surjective_id hf]
  exact diagonal_pair_rank _ (by norm_num)

/-- The three nonzero blocks of the central row flattening are indexed by bit sum. -/
theorem oneBitRow_zero_rank : (oneBitRow 0).rank = 3 := by
  have h : oneBitRow 0 =
      (Matrix.diagonal (fun _ : Fin 3 => (2 : ℚ))).submatrix bitSum bitSum := by
    ext ⟨x, y⟩ ⟨u, v⟩
    simp [oneBitRow, oneBit_coeff_zero, Matrix.submatrix, Matrix.diagonal, bitSum, Fin.ext_iff]
  rw [h, rank_submatrix_surjective _ _ _ bitSum_surjective bitSum_surjective]
  exact diagonal_three_rank _ (by norm_num)

/-- The central column blocks are indexed by `1+x-u = 1+v-y`, taking three values. -/
theorem oneBitCol_zero_rank : (oneBitCol 0).rank = 3 := by
  let r : Bool × Bool → Fin 3 := fun p => bitSum (p.1, !p.2)
  let c : Bool × Bool → Fin 3 := fun p => bitSum (!p.1, p.2)
  have hr : Function.Surjective r := by
    intro i
    obtain ⟨⟨a, b⟩, h⟩ := bitSum_surjective i
    exact ⟨(a, !b), by simpa [r] using h⟩
  have hc : Function.Surjective c := by
    intro i
    obtain ⟨⟨a, b⟩, h⟩ := bitSum_surjective i
    exact ⟨(!a, b), by simpa [c] using h⟩
  have h : oneBitCol 0 =
      (Matrix.diagonal (fun _ : Fin 3 => (2 : ℚ))).submatrix r c := by
    ext ⟨x, u⟩ ⟨y, v⟩
    cases x <;> cases y <;> cases u <;> cases v <;>
      simp [oneBitCol, oneBit_coeff_zero, Matrix.submatrix, Matrix.diagonal, r, c, bitSum]
  rw [h, rank_submatrix_surjective _ _ _ hr hc]
  exact diagonal_three_rank _ (by norm_num)

/-- The crossing on the row cut, with the encoded-view convention used above. -/
noncomputable def oneBitCrossingRow : Matrix (Bool × Bool) (Bool × Bool) ℚ :=
  fun r c => if crossing (oneBitViews r.1 r.2 c.1 c.2) then 1 else 0

/-- The crossing on the column cut. -/
noncomputable def oneBitCrossingCol : Matrix (Bool × Bool) (Bool × Bool) ℚ :=
  fun r c => if crossing (oneBitViews r.1 c.1 r.2 c.2) then 1 else 0

/-- The row crossing is a permutation matrix, exchanging the two column bits. -/
theorem oneBitCrossingRow_rank : oneBitCrossingRow.rank = 4 := by
  have h : oneBitCrossingRow =
      (Matrix.diagonal (fun _ : Bool × Bool => (1 : ℚ))).submatrix id Prod.swap := by
    ext ⟨x, y⟩ ⟨u, v⟩
    simp [oneBitCrossingRow, oneBit_crossing, Matrix.submatrix, Matrix.diagonal, Prod.mk.injEq]
  rw [h, rank_submatrix_surjective _ _ _ Function.surjective_id
    (fun p => ⟨p.swap, rfl⟩)]
  exact diagonal_pair_rank _ (by norm_num)

/-- The column crossing is the same permutation matrix as the row crossing. -/
theorem oneBitCrossingCol_rank : oneBitCrossingCol.rank = 4 := by
  have h : oneBitCrossingCol = oneBitCrossingRow := by
    ext ⟨x, u⟩ ⟨y, v⟩
    simp [oneBitCrossingCol, oneBitCrossingRow, oneBit_crossing, eq_comm]
  rw [h, oneBitCrossingRow_rank]

end Cslib.Complexity.NtimeDspace.Cube
