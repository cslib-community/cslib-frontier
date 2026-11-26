/-
Copyright (c) 2026 Uladzislau Artsemyeu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Uladzislau Artsemyeu
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Program
public import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Ring
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Valiant depth reduction for bounded-fan-in programs

Formalizes Valiant's bit-level depth-reduction lemma [Valiant1977] for arbitrary bounded-fan-in
straight-line programs `p : Program σ n g` (`p.FanInAtMost r`): for every `0 < k` and `t ≤ k` such
that `∀ j : Fin g, p.wireDepths (.gate j) < 2 ^ k`, there exists a gate cut `cut : Finset (Fin g)`
of size at most `r * t * g / k` such that every wire has residual depth strictly below
`2 ^ (k - t)` (`Program.valiantDepthReduction`), with the single-bit halving specialization at
`t = 1` (`Program.valiant_halving_cut`).

## Main definitions

* `Cslib.Circuits.Program.residualWireDepths`: depth of every wire after resetting cut gates (and
  `0`-ary constant gates) to residual depth `0`.
* `Cslib.Circuits.Program.valiantCut`: gates whose depth differs from some operand's depth in a
  highest bit lying in `S : Finset (Fin k)`.

## Main results

* `Cslib.Circuits.Program.valiantDepthReduction`: cuts at most `r * t * g / k` gates to reduce all
  residual wire depths strictly below `2 ^ (k - t)`.
* `Cslib.Circuits.Program.valiant_halving_cut`: cuts at most `r * g / k` gates to reduce all
  residual wire depths strictly below `2 ^ (k - 1)`.

## References

* [L. G. Valiant, *Graph-Theoretic Arguments in Low-Level Complexity*][Valiant1977]
-/

public section

namespace Cslib.Circuits

section BitCompression

/-- Highest differing bit index strictly below `k` between `x` and `y` (`0` when `k = 0`). -/
private def highestDiffBit : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | k + 1, x, y =>
    if x / 2 ^ k = y / 2 ^ k then highestDiffBit k (x % 2 ^ k) (y % 2 ^ k) else k

private theorem highestDiffBit_lt {k x y : ℕ} (hk : 0 < k) : highestDiffBit k x y < k := by
  induction k generalizing x y with
  | zero => cases hk
  | succ k ih =>
    simp only [highestDiffBit]
    split_ifs
    · cases k with
      | zero => simp [highestDiffBit]
      | succ k' => exact Nat.lt_trans (ih (Nat.succ_pos k')) (Nat.lt_succ_self _)
    · exact Nat.lt_succ_self k

/-- Count of bit positions strictly below `m` retained outside `S`. -/
private def keepCount (S : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | m + 1 => keepCount S m + if S m then 0 else 1

private theorem keepCount_add_filter_card (k : ℕ) (S : Finset (Fin k)) :
    ∀ m, m ≤ k →
      keepCount (fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)) m +
        (S.filter (fun b : Fin k => b.val < m)).card = m
  | 0, _ => by
    simp only [keepCount, Nat.zero_add]
    have hEmpty : S.filter (fun b : Fin k => b.val < 0) = ∅ := by
      ext b
      simp
    rw [hEmpty, Finset.card_empty]
  | m + 1, hm => by
    have ih := keepCount_add_filter_card k S m (Nat.le_of_succ_le hm)
    let fPred : ℕ → Bool := fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)
    let bm : Fin k := ⟨m, hm⟩
    have hSplit :
        (S.filter (fun b : Fin k => b.val < m + 1)).card =
          (S.filter (fun b : Fin k => b.val < m)).card + if bm ∈ S then 1 else 0 := by
      by_cases hMem : bm ∈ S
      · have hEq : S.filter (fun b : Fin k => b.val < m + 1) =
            insert bm (S.filter (fun b : Fin k => b.val < m)) := by
          ext b
          simp only [Finset.mem_filter, Finset.mem_insert, Fin.ext_iff, bm]
          constructor
          · rintro ⟨hbS, hbLt⟩
            by_cases hbEq : b.val = m
            · exact Or.inl hbEq
            · exact Or.inr ⟨hbS, by omega⟩
          · rintro (hbEq | ⟨hbS, hbLt⟩)
            · subst hbEq
              exact ⟨hMem, Nat.lt_succ_self _⟩
            · exact ⟨hbS, Nat.lt_trans hbLt (Nat.lt_succ_self m)⟩
        have hNotMem : bm ∉ S.filter (fun b : Fin k => b.val < m) := by simp [bm]
        rw [hEq, Finset.card_insert_of_notMem hNotMem]
        simp [hMem]
      · have hEq : S.filter (fun b : Fin k => b.val < m + 1) =
            S.filter (fun b : Fin k => b.val < m) := by
          ext b
          simp only [Finset.mem_filter]
          constructor
          · rintro ⟨hbS, hbLt⟩
            refine ⟨hbS, ?_⟩
            by_contra hGe
            have hbEq : b = bm := Fin.ext (by dsimp [bm]; omega)
            exact hMem (hbEq ▸ hbS)
          · rintro ⟨hbS, hbLt⟩
            exact ⟨hbS, Nat.lt_trans hbLt (Nat.lt_succ_self m)⟩
        rw [hEq]
        simp [hMem]
    have hF : fPred m = decide (bm ∈ S) := by
      simp only [fPred, bm, decide_eq_decide]
      exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hm, h⟩⟩
    have ih' : keepCount fPred m + (S.filter (fun b : Fin k => b.val < m)).card = m := ih
    change keepCount fPred m + (if fPred m then 0 else 1) +
        (S.filter (fun b : Fin k => b.val < m + 1)).card = m + 1
    rw [hSplit, hF]
    by_cases hMem' : bm ∈ S
    · simp only [hMem', decide_true, ↓reduceIte]
      omega
    · simp only [hMem', decide_false, Bool.false_eq_true, ↓reduceIte]
      omega

private theorem keepCount_finset (k : ℕ) (S : Finset (Fin k)) :
    keepCount (fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)) k = k - S.card := by
  have h := keepCount_add_filter_card k S k (le_refl k)
  have hFull : S.filter (fun b : Fin k => b.val < k) = S := by
    ext b
    simp
  rw [hFull] at h
  omega

/-- Drops bit positions in `S` from the `k`-bit binary representation of `d`. -/
private def compressBits (S : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, d =>
    if S k then compressBits S k (d % 2 ^ k)
    else ((d / 2 ^ k) % 2) * 2 ^ keepCount S k + compressBits S k (d % 2 ^ k)

private theorem compressBits_lt (S : ℕ → Bool) :
    ∀ k d : ℕ, compressBits S k d < 2 ^ keepCount S k
  | 0, _ => by simp [compressBits, keepCount]
  | k + 1, d => by
    have ih := compressBits_lt S k (d % 2 ^ k)
    simp only [compressBits, keepCount]
    split_ifs with hSk
    · simpa using ih
    · have hBit : (d / 2 ^ k) % 2 ≤ 1 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      have hMul : ((d / 2 ^ k) % 2) * 2 ^ keepCount S k ≤ 1 * 2 ^ keepCount S k :=
        Nat.mul_le_mul_right _ hBit
      rw [Nat.pow_succ]
      omega

private theorem compressBits_lt_of_avoid (S : ℕ → Bool) :
    ∀ k x y : ℕ, x < y → y < 2 ^ k → S (highestDiffBit k x y) = false →
      compressBits S k x < compressBits S k y
  | 0, _, _, _, hy, _ => by
    simp only [pow_zero] at hy
    omega
  | k + 1, x, y, hxy, hy, hAvoid => by
    by_cases hEq : x / 2 ^ k = y / 2 ^ k
    · have hDiff : highestDiffBit (k + 1) x y = highestDiffBit k (x % 2 ^ k) (y % 2 ^ k) := by
        simp [highestDiffBit, hEq]
      rw [hDiff] at hAvoid
      have hxMod : x % 2 ^ k < y % 2 ^ k := by
        have hx := Nat.div_add_mod x (2 ^ k)
        have hy' := Nat.div_add_mod y (2 ^ k)
        rw [hEq] at hx
        omega
      have hyMod : y % 2 ^ k < 2 ^ k := Nat.mod_lt y (Nat.two_pow_pos k)
      have ih := compressBits_lt_of_avoid S k (x % 2 ^ k) (y % 2 ^ k) hxMod hyMod hAvoid
      simp only [compressBits]
      split_ifs with hSk
      · exact ih
      · rw [hEq]
        exact Nat.add_lt_add_left ih _
    · have hDiff : highestDiffBit (k + 1) x y = k := by
        simp [highestDiffBit, hEq]
      rw [hDiff] at hAvoid
      have hy2 : y / 2 ^ k < 2 := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos k)]
        simpa [Nat.pow_succ, Nat.mul_comm] using hy
      have hxLe : x / 2 ^ k ≤ y / 2 ^ k := Nat.div_le_div_right (le_of_lt hxy)
      have hyPos : 0 < y / 2 ^ k := Nat.pos_of_ne_zero fun hy0 => by
        have hx0 : x / 2 ^ k = 0 := Nat.eq_zero_of_le_zero (hxLe.trans_eq hy0)
        exact hEq (hx0.trans hy0.symm)
      have hy1 : y / 2 ^ k = 1 := Nat.le_antisymm (Nat.lt_succ_iff.mp hy2) hyPos
      have hxZero : x / 2 ^ k = 0 := by
        rw [hy1] at hxLe
        rcases Nat.eq_zero_or_pos (x / 2 ^ k) with h0 | hxPos
        · exact h0
        · exact absurd ((Nat.le_antisymm hxLe hxPos).trans hy1.symm) hEq
      have hLtX := compressBits_lt S k (x % 2 ^ k)
      simp only [compressBits, hAvoid, Bool.false_eq_true, ↓reduceIte, hxZero, hy1]
      omega

private theorem exists_subset_sum_le {k : ℕ} (hk : 0 < k) (f : Fin k → ℕ) :
    ∀ t ≤ k, ∃ S : Finset (Fin k), S.card = t ∧
      k * ∑ b ∈ S, f b ≤ t * ∑ b : Fin k, f b
  | 0, _ => ⟨∅, by simp⟩
  | t + 1, ht => by
    obtain ⟨S, hCard, hBound⟩ := exists_subset_sum_le hk f t (Nat.le_of_succ_le ht)
    let R : Finset (Fin k) := Finset.univ \ S
    have hSub : S ⊆ Finset.univ := Finset.subset_univ S
    have hRCard : R.card = k - t := by
      rw [Finset.card_sdiff_of_subset hSub, Finset.card_univ, Fintype.card_fin, hCard]
    have hRPos : 0 < R.card := by omega
    obtain ⟨b₀, hb₀R, hb₀Min⟩ := Finset.exists_min_image R f (Finset.card_pos.mp hRPos)
    have hb₀NotS : b₀ ∉ S := (Finset.mem_sdiff.mp hb₀R).2
    have hRSum : (k - t) * f b₀ ≤ ∑ b ∈ R, f b := by
      calc (k - t) * f b₀ = ∑ _ ∈ R, f b₀ := by rw [Finset.sum_const, Nat.nsmul_eq_mul, hRCard]
        _ ≤ ∑ b ∈ R, f b := Finset.sum_le_sum fun b hb => hb₀Min b hb
    have hSplit : ∑ b ∈ S, f b + ∑ b ∈ R, f b = ∑ b : Fin k, f b :=
      Finset.sum_add_sum_compl S f
    have hktPos : 0 < k - t := by omega
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hktPos.ne'
    have hKt : m + t + 1 = k := by omega
    have hStep : (k - t) * (k * ∑ b ∈ insert b₀ S, f b) ≤
        (k - t) * ((t + 1) * ∑ b : Fin k, f b) := by
      rw [Finset.sum_insert hb₀NotS]
      have hSplitK : k * ∑ b ∈ S, f b + k * ∑ b ∈ R, f b = k * ∑ b : Fin k, f b := by
        rw [← Nat.mul_add, hSplit]
      have h1 : k * ((k - t) * f b₀) ≤ k * ∑ b ∈ R, f b := Nat.mul_le_mul_left k hRSum
      have h2 : m * (k * ∑ b ∈ S, f b) ≤ m * (t * ∑ b : Fin k, f b) :=
        Nat.mul_le_mul_left m hBound
      have hLHS : (k - t) * (k * (f b₀ + ∑ b ∈ S, f b)) =
          k * ((k - t) * f b₀) + m * (k * ∑ b ∈ S, f b) + k * ∑ b ∈ S, f b := by
        rw [hm, Nat.succ_eq_add_one]
        ring
      have hMulMT : (m + 1) * (t + 1) = m * t + (m + t + 1) := by ring
      have hRHS : (k - t) * ((t + 1) * ∑ b : Fin k, f b) =
          m * (t * ∑ b : Fin k, f b) + k * ∑ b : Fin k, f b := by
        rw [hm, Nat.succ_eq_add_one, ← Nat.mul_assoc, hMulMT, hKt, Nat.add_mul, Nat.mul_assoc]
      omega
    refine ⟨insert b₀ S, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hb₀NotS, hCard]
    · exact Nat.le_of_mul_le_mul_left hStep hktPos

end BitCompression

section ProgramDepths

variable {σ : Signature} {n g : ℕ}

private theorem foldl_max_ge_init (m : ℕ) (f : Fin m → ℕ) (init : ℕ) :
    init ≤ Fin.foldl m (fun acc k => max acc (f k)) init := by
  induction m generalizing init with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Fin.foldl_succ]
    exact (le_max_left init _).trans (ih (fun k => f k.succ) (max init (f 0)))

private theorem le_foldl_max (m : ℕ) (f : Fin m → ℕ) (init : ℕ) (i : Fin m) :
    f i ≤ Fin.foldl m (fun acc k => max acc (f k)) init := by
  induction m generalizing init with
  | zero => exact Fin.elim0 i
  | succ m ih =>
    rw [Fin.foldl_succ]
    cases i using Fin.cases with
    | zero =>
      exact (le_max_right init (f 0)).trans (foldl_max_ge_init m (fun k => f k.succ) _)
    | succ j =>
      exact ih (fun k => f k.succ) (max init (f 0)) j

private theorem foldl_max_le (m : ℕ) (f : Fin m → ℕ) (init bound : ℕ)
    (hinit : init ≤ bound) (hf : ∀ i, f i ≤ bound) :
    Fin.foldl m (fun acc k => max acc (f k)) init ≤ bound := by
  induction m generalizing init with
  | zero => simpa using hinit
  | succ m ih =>
    rw [Fin.foldl_succ]
    exact ih (fun k => f k.succ) (max init (f 0)) (max_le hinit (hf 0)) fun j => hf j.succ

private theorem line_depth_mapWires {g₁ g₂ : ℕ} (line : Line σ n g₁)
    (ρ : Wire n g₁ → Wire n g₂) (d : Wire n g₂ → ℕ) :
    (line.mapWires ρ).depth d = line.depth (d ∘ ρ) := rfl

private theorem wireDepths_gate_castSucc (p : Program σ n g) (line : Line σ n g) (w : Wire n g) :
    (p.gate line).wireDepths w.castSucc = p.wireDepths w := by
  cases w with
  | input i => rfl
  | gate j =>
    simp only [Program.wireDepths, Wire.castSucc, Wire.elim_gate, Program.depths,
      Fin.lastCases_castSucc]

private theorem wireDepths_gate (p : Program σ n g) (j : Fin g) :
    p.wireDepths (.gate j) = (p.lines j).depth p.wireDepths := by
  induction p with
  | empty => exact Fin.elim0 j
  | @gate g p line ih =>
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp only [Program.wireDepths, Wire.elim_gate, Program.depths, Fin.lastCases_last,
        Program.lines_gate_last, line_depth_mapWires]
      congr 1
      funext w
      exact (wireDepths_gate_castSucc p line w).symm
    · have hCast : p.wireDepths = (p.gate line).wireDepths ∘ Wire.Renaming.castSucc := by
        funext w
        exact (wireDepths_gate_castSucc p line w).symm
      rw [Program.lines_gate_castSucc, line_depth_mapWires, ← hCast]
      have hLhs : (p.gate line).wireDepths (.gate j'.castSucc) = p.wireDepths (.gate j') :=
        wireDepths_gate_castSucc p line (.gate j')
      exact hLhs.trans (ih j')

private theorem lt_wireDepths_gate (p : Program σ n g) (j : Fin g)
    (s : Fin (σ.Arity (p.lines j).op)) :
    p.wireDepths ((p.lines j).wires s) < p.wireDepths (.gate j) := by
  rw [wireDepths_gate]
  unfold Line.depth
  exact Nat.lt_succ_of_le
    (le_foldl_max (σ.Arity (p.lines j).op) (fun k => p.wireDepths ((p.lines j).wires k)) 0 s)

private def residualDepthsBool : {g : ℕ} → Program σ n g → (Fin g → Bool) → Fin g → ℕ
  | _, .empty, _ => Fin.elim0
  | _, .gate p line, cut =>
    let prior := residualDepthsBool p (cut ∘ Fin.castSucc)
    let wd : Wire n _ → ℕ := Wire.elim (fun _ => 0) prior
    let dLast :=
      if cut (Fin.last _) || decide (σ.Arity line.op = 0) then 0 else line.depth wd
    Fin.lastCases dLast prior

private def residualWireDepthsBool (p : Program σ n g) (cut : Fin g → Bool) : Wire n g → ℕ :=
  Wire.elim (fun _ => 0) (residualDepthsBool p cut)

private theorem residualWireDepthsBool_gate_castSucc (p : Program σ n g) (line : Line σ n g)
    (cut : Fin (g + 1) → Bool) (w : Wire n g) :
    residualWireDepthsBool (p.gate line) cut w.castSucc =
      residualWireDepthsBool p (cut ∘ Fin.castSucc) w := by
  cases w with
  | input i => rfl
  | gate j =>
    simp only [residualWireDepthsBool, Wire.castSucc, Wire.elim_gate, residualDepthsBool,
      Fin.lastCases_castSucc]

private theorem residualWireDepthsBool_gate (p : Program σ n g) (cut : Fin g → Bool) (j : Fin g) :
    residualWireDepthsBool p cut (.gate j) =
      if cut j || decide (σ.Arity (p.lines j).op = 0) then 0
      else (p.lines j).depth (residualWireDepthsBool p cut) := by
  induction p with
  | empty => exact Fin.elim0 j
  | @gate g p line ih =>
    have hCast : residualWireDepthsBool p (cut ∘ Fin.castSucc) =
        residualWireDepthsBool (p.gate line) cut ∘ Wire.Renaming.castSucc := by
      funext w
      exact (residualWireDepthsBool_gate_castSucc p line cut w).symm
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · rw [Program.lines_gate_last, Line.mapWires_op, line_depth_mapWires, ← hCast]
      simp only [residualWireDepthsBool, Wire.elim_gate, residualDepthsBool, Fin.lastCases_last]
    · rw [Program.lines_gate_castSucc, Line.mapWires_op, line_depth_mapWires, ← hCast]
      have hLhs :
          residualWireDepthsBool (p.gate line) cut (.gate j'.castSucc) =
            residualWireDepthsBool p (cut ∘ Fin.castSucc) (.gate j') :=
        residualWireDepthsBool_gate_castSucc p line cut (.gate j')
      exact hLhs.trans (ih (cut ∘ Fin.castSucc) j')

/-- Residual depth of each gate when every gate in `cut` (and every `0`-ary gate) is reset
to `0`. -/
noncomputable def Program.residualDepths (p : Program σ n g) (cut : Finset (Fin g)) : Fin g → ℕ :=
  open scoped Classical in residualDepthsBool p (fun j => decide (j ∈ cut))

/-- Residual depth of every input or gate wire when every gate in `cut` (and every `0`-ary gate)
is reset to `0`. -/
noncomputable def Program.residualWireDepths (p : Program σ n g) (cut : Finset (Fin g)) :
    Wire n g → ℕ :=
  Wire.elim (fun _ => 0) (p.residualDepths cut)

@[simp] theorem Program.residualWireDepths_input (p : Program σ n g) (cut : Finset (Fin g))
    (i : Fin n) : p.residualWireDepths cut (.input i) = 0 := by
  simp [Program.residualWireDepths]

/-- Residual depth equation at any gate wire `j`. -/
theorem Program.residualWireDepths_gate (p : Program σ n g) (cut : Finset (Fin g)) (j : Fin g) :
    p.residualWireDepths cut (.gate j) =
      open scoped Classical in
      if j ∈ cut ∨ σ.Arity (p.lines j).op = 0 then 0
      else (p.lines j).depth (p.residualWireDepths cut) := by
  classical
  change residualWireDepthsBool p (fun q => decide (q ∈ cut)) (.gate j) = _
  rw [residualWireDepthsBool_gate]
  simp [Program.residualWireDepths, Program.residualDepths, residualWireDepthsBool]

/-- Cut gates of bit-level schedule `S`: gates whose depth differs from some operand depth in a
highest differing bit belonging to `S`. -/
def Program.valiantCut (p : Program σ n g) (k : ℕ) (S : Finset (Fin k)) : Finset (Fin g) :=
  Finset.univ.filter fun j =>
    ∃ s : Fin (σ.Arity (p.lines j).op),
      ∃ hlt : highestDiffBit k (p.wireDepths ((p.lines j).wires s))
          (p.wireDepths (.gate j)) < k,
        ⟨highestDiffBit k (p.wireDepths ((p.lines j).wires s))
          (p.wireDepths (.gate j)), hlt⟩ ∈ S

private theorem valiantCut_subset_biUnion (p : Program σ n g) (k : ℕ) (S : Finset (Fin k)) :
    p.valiantCut k S ⊆ S.biUnion fun b => p.valiantCut k {b} := by
  intro j hj
  simp only [Program.valiantCut, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_biUnion, Finset.mem_singleton] at hj ⊢
  obtain ⟨s, hlt, hbS⟩ := hj
  exact ⟨_, hbS, s, hlt, rfl⟩

private theorem sum_valiantCut_singleton_le (p : Program σ n g) {r k : ℕ}
    (hr : p.FanInAtMost r) :
    ∑ b : Fin k, (p.valiantCut k {b}).card ≤ r * g := by
  have hArity := Program.fanInAtMost_iff.mp hr
  have hGateCard (j : Fin g) :
      (Finset.univ.filter fun b : Fin k => j ∈ p.valiantCut k {b}).card ≤ r := by
    let bits : Finset (Fin k) := Finset.univ.filter fun b : Fin k =>
      ∃ s : Fin (σ.Arity (p.lines j).op),
        (b : ℕ) = highestDiffBit k (p.wireDepths ((p.lines j).wires s)) (p.wireDepths (.gate j))
    have hSub : (Finset.univ.filter fun b : Fin k => j ∈ p.valiantCut k {b}) ⊆ bits := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Program.valiantCut,
        Finset.mem_singleton] at hb
      obtain ⟨s, hlt, hbEq⟩ := hb
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, ?_⟩
      simpa using (congrArg Fin.val hbEq).symm
    have hBits : bits.card ≤ σ.Arity (p.lines j).op := by
      let f : Fin (σ.Arity (p.lines j).op) → ℕ := fun s =>
        highestDiffBit k (p.wireDepths ((p.lines j).wires s)) (p.wireDepths (.gate j))
      have hInj : Set.InjOn Fin.val (bits : Set (Fin k)) := Fin.val_injective.injOn
      have hImg : bits.image Fin.val ⊆ Finset.univ.image f := by
        intro x hx
        obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨s, hs⟩ := (Finset.mem_filter.mp hb).2
        exact Finset.mem_image.mpr ⟨s, Finset.mem_univ _, hs.symm⟩
      calc
        bits.card = (bits.image Fin.val).card := (Finset.card_image_of_injOn hInj).symm
        _ ≤ (Finset.univ.image f).card := Finset.card_le_card hImg
        _ ≤ (Finset.univ : Finset (Fin (σ.Arity (p.lines j).op))).card := Finset.card_image_le
        _ = σ.Arity (p.lines j).op := Fintype.card_fin _
    exact (Finset.card_le_card hSub).trans (hBits.trans (hArity j))
  calc
    ∑ b : Fin k, (p.valiantCut k {b}).card
      = ∑ b : Fin k, ∑ j : Fin g, if j ∈ p.valiantCut k {b} then 1 else 0 := by
        congr 1
        funext b
        simp only [Finset.card_eq_sum_ones, ← Finset.sum_filter,
          Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = ∑ j : Fin g, ∑ b : Fin k, if j ∈ p.valiantCut k {b} then 1 else 0 := Finset.sum_comm
    _ = ∑ j : Fin g, (Finset.univ.filter fun b : Fin k => j ∈ p.valiantCut k {b}).card := by
        congr 1
        funext j
        simp only [Finset.card_eq_sum_ones, ← Finset.sum_filter]
    _ ≤ ∑ _j : Fin g, r := Finset.sum_le_sum fun j _ => hGateCard j
    _ = r * g := by simp [Finset.sum_const, Nat.mul_comm]

private theorem residualWireDepths_le_compressBits (p : Program σ n g) (k : ℕ)
    (S : Finset (Fin k)) (hDepth : ∀ w : Wire n g, p.wireDepths w < 2 ^ k) :
    ∀ w : Wire n g, p.residualWireDepths (p.valiantCut k S) w ≤
      compressBits (fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)) k (p.wireDepths w) := by
  let Sfn : ℕ → Bool := fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)
  refine p.wire_induction (P := fun w =>
    p.residualWireDepths (p.valiantCut k S) w ≤ compressBits Sfn k (p.wireDepths w)) ?_ ?_
  · intro i
    simp [Program.residualWireDepths_input]
  · intro j ih
    classical
    rw [Program.residualWireDepths_gate]
    split_ifs with hSkip
    · exact Nat.zero_le _
    · push Not at hSkip
      obtain ⟨hNotCut, hArityPos⟩ := hSkip
      have hArityPos' : 0 < σ.Arity (p.lines j).op := Nat.pos_of_ne_zero hArityPos
      let dOut := p.wireDepths (.gate j)
      have hdOut : dOut < 2 ^ k := hDepth (.gate j)
      have hOperandLt (s : Fin (σ.Arity (p.lines j).op)) :
          compressBits Sfn k (p.wireDepths ((p.lines j).wires s)) < compressBits Sfn k dOut := by
        have hsLt : p.wireDepths ((p.lines j).wires s) < dOut := lt_wireDepths_gate p j s
        have hAvoid :
            Sfn (highestDiffBit k (p.wireDepths ((p.lines j).wires s)) dOut) = false := by
          simp only [Sfn, decide_eq_false_iff_not]
          rintro ⟨hlt, hMem⟩
          exact hNotCut (Finset.mem_filter.mpr ⟨Finset.mem_univ _, s, hlt, hMem⟩)
        exact compressBits_lt_of_avoid Sfn k _ dOut hsLt hdOut hAvoid
      have hCompPos : 0 < compressBits Sfn k dOut := by
        have hStrict := hOperandLt ⟨0, hArityPos'⟩
        omega
      let resFn := fun s => p.residualWireDepths (p.valiantCut k S) ((p.lines j).wires s)
      have hFoldLe :
          Fin.foldl (σ.Arity (p.lines j).op) (fun acc s => max acc (resFn s)) 0 ≤
            compressBits Sfn k dOut - 1 := by
        refine foldl_max_le _ resFn 0 (compressBits Sfn k dOut - 1) (Nat.zero_le _) fun s => ?_
        exact (ih s).trans (Nat.le_pred_of_lt (hOperandLt s))
      change Line.depth (p.lines j) (p.residualWireDepths (p.valiantCut k S)) ≤
        compressBits Sfn k dOut
      unfold Line.depth
      dsimp only [resFn] at hFoldLe
      omega

/-- **Valiant Depth-Reduction Lemma** [Valiant1977]: for any `0 < k` and `t ≤ k`, every bounded
fan-in program `p : Program σ n g` (`p.FanInAtMost r`) of wire depth `< 2 ^ k` admits a gate cut
`cut : Finset (Fin g)` of size at most `r * t * g / k` such that every wire has residual depth
strictly below `2 ^ (k - t)`. -/
theorem Program.valiantDepthReduction (p : Program σ n g) {r k t : ℕ}
    (hr : p.FanInAtMost r) (hk : 0 < k) (ht : t ≤ k)
    (hDepth : ∀ w : Wire n g, p.wireDepths w < 2 ^ k) :
    ∃ cut : Finset (Fin g),
      cut.card ≤ r * t * g / k ∧
      ∀ w : Wire n g, p.residualWireDepths cut w < 2 ^ (k - t) := by
  obtain ⟨S, hCard, hSum⟩ :=
    exists_subset_sum_le hk (fun b : Fin k => (p.valiantCut k {b}).card) t ht
  refine ⟨p.valiantCut k S, ?_, ?_⟩
  · have hCutLeSum : (p.valiantCut k S).card ≤ ∑ b ∈ S, (p.valiantCut k {b}).card :=
      (Finset.card_le_card (valiantCut_subset_biUnion p k S)).trans Finset.card_biUnion_le
    have hTotal : ∑ b : Fin k, (p.valiantCut k {b}).card ≤ r * g :=
      sum_valiantCut_singleton_le p hr
    have hMul : k * (p.valiantCut k S).card ≤ r * t * g := by
      calc
        k * (p.valiantCut k S).card
          ≤ k * ∑ b ∈ S, (p.valiantCut k {b}).card := Nat.mul_le_mul_left k hCutLeSum
        _ ≤ t * ∑ b : Fin k, (p.valiantCut k {b}).card := hSum
        _ ≤ t * (r * g) := Nat.mul_le_mul_left t hTotal
        _ = r * t * g := by ring
    exact (Nat.le_div_iff_mul_le hk).mpr (by simpa [Nat.mul_comm] using hMul)
  · intro w
    let Sfn : ℕ → Bool := fun j => decide (∃ hj : j < k, ⟨j, hj⟩ ∈ S)
    have hRes := residualWireDepths_le_compressBits p k S hDepth w
    have hComp := compressBits_lt Sfn k (p.wireDepths w)
    have hKeep : keepCount Sfn k = k - t := by
      rw [keepCount_finset, hCard]
    rw [hKeep] at hComp
    exact lt_of_le_of_lt hRes hComp

/-- Single-bit halving specialization (`t = 1`) of `Program.valiantDepthReduction`: cuts at most
`r * g / k` gates to reduce every residual wire depth strictly below `2 ^ (k - 1)`. -/
theorem Program.valiant_halving_cut (p : Program σ n g) {r k : ℕ}
    (hr : p.FanInAtMost r) (hk : 1 ≤ k)
    (hDepth : ∀ w : Wire n g, p.wireDepths w < 2 ^ k) :
    ∃ cut : Finset (Fin g),
      cut.card ≤ r * g / k ∧
      ∀ w : Wire n g, p.residualWireDepths cut w < 2 ^ (k - 1) := by
  simpa using p.valiantDepthReduction hr (by omega) hk hDepth

end ProgramDepths

end Cslib.Circuits
