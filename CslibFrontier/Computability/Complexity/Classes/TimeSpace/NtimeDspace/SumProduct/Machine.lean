/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.SumProduct.Tree

/-!
# Depth-first evaluation of a sum–product recursion

The procedure `Bit(ν, k)` of the proof of Proposition 3.2, as a small-step machine
with an explicit stack. A state is a mode (calling a node, or returning a bit
to the node below), a value (the requested bit, or the returned bit), a stack of
frames and the path of the current node. A frame holds the requested bit `k`,
the current column `j`, the current split `l` (product nodes) and the carry
`c`. The symbol of the child currently being evaluated sits at the head of the
path, so the path is exactly the list of current indices.

The machine sees the recursion only through two oracles: `q π` reports the
kind, precision and parameter of the node at `π`, and `lb π k` reports bit `k`
of a leaf value. They need to be correct only on valid paths (`Agrees`).

## Main results

* `reaches_call`: from a call at a node whose oracles agree with a subtree, the
  machine reaches the return of the requested bit of its value, with the stack
  below it unchanged.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.SumProduct

open Finset SPTree

/-- What the explicit machine reports about a node. -/
structure Info where
  /-- The kind of the node: `0` leaf, `1` sum, `2` product, `3` shift (see `SPTree.tag`). -/
  tag : ℕ
  /-- The precision of the node. -/
  prec : ℕ
  /-- The index length of a sum node, the shift of a shift node, and `0` otherwise. -/
  param : ℕ
deriving DecidableEq

/-- The report for a node. -/
def SPTree.info (t : SPTree) : Info := ⟨t.tag, t.prec, t.param⟩

/-- A frame of the evaluation stack. -/
structure Frame where
  /-- The bit requested of the node. -/
  k : ℕ
  /-- The current column. -/
  j : ℕ
  /-- The current split (used at product nodes). -/
  l : ℕ
  /-- The carry. -/
  c : ℕ
deriving DecidableEq

/-- A state of the evaluator. -/
structure State where
  /-- The mode: `true` when calling the current node, `false` when returning a bit below it. -/
  call : Bool
  /-- The requested bit index in call mode, or the returned bit in return mode. -/
  v : ℕ
  /-- The evaluation stack, innermost frame first. -/
  frames : List Frame
  /-- The path of the current node, deepest symbol first. -/
  path : List ℕ
deriving DecidableEq

section Step

variable (q : List ℕ → Info) (lb : List ℕ → ℕ → Bool)

/-- After the term of split `l` of column `j` at a product node at `ρ`. -/
def advanceProd (k j l c : ℕ) (fr : List Frame) (ρ : List ℕ) : State :=
  if l < j then ⟨true, l + 1, ⟨k, j, l + 1, c⟩ :: fr, 0 :: ρ⟩
  else if j < k then ⟨true, 0, ⟨k, j + 1, 0, c / 2⟩ :: fr, 0 :: ρ⟩
  else ⟨false, c % 2, fr, ρ⟩

/-- One step of the evaluator. -/
def step : State → State
  | ⟨true, k, fr, π⟩ =>
    if (q π).prec ≤ k then ⟨false, 0, fr, π⟩
    else if (q π).tag = 0 then ⟨false, (lb π k).toNat, fr, π⟩
    else if (q π).tag = 1 ∨ (q π).tag = 2 then ⟨true, 0, ⟨k, 0, 0, 0⟩ :: fr, 0 :: π⟩
    else if (q π).tag = 3 then ⟨true, k + (q π).param, ⟨k, 0, 0, 0⟩ :: fr, 0 :: π⟩
    else ⟨false, 0, fr, π⟩
  | ⟨false, b, [], π⟩ => ⟨false, b, [], π⟩
  | ⟨false, b, ⟨k, j, l, c⟩ :: fr, π⟩ =>
    if (q π.tail).tag = 1 then
      if π.headD 0 + 1 < 2 ^ (q π.tail).param then
        ⟨true, j, ⟨k, j, l, c + b⟩ :: fr, (π.headD 0 + 1) :: π.tail⟩
      else if j < k then ⟨true, j + 1, ⟨k, j + 1, l, (c + b) / 2⟩ :: fr, 0 :: π.tail⟩
      else ⟨false, (c + b) % 2, fr, π.tail⟩
    else if (q π.tail).tag = 2 then
      if π.headD 0 = 0 then
        if b = 0 then advanceProd k j l c fr π.tail
        else ⟨true, j - l, ⟨k, j, l, c⟩ :: fr, 1 :: π.tail⟩
      else advanceProd k j l (c + b) fr π.tail
    else ⟨false, b, fr, π.tail⟩

/-- `a` reaches `b` in some number of steps. -/
def Reaches (a b : State) : Prop := ∃ n, (step q lb)^[n] a = b

variable {q lb}

theorem Reaches.refl (a : State) : Reaches q lb a a := ⟨0, rfl⟩

theorem Reaches.trans {a b c : State} (h1 : Reaches q lb a b) (h2 : Reaches q lb b c) :
    Reaches q lb a c := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨n, rfl⟩ := h2
  exact ⟨n + m, Function.iterate_add_apply _ _ _ _⟩

theorem Reaches.head {a b : State} (h : Reaches q lb (step q lb a) b) : Reaches q lb a b := by
  obtain ⟨n, rfl⟩ := h
  exact ⟨n + 1, Function.iterate_succ_apply _ _ _⟩

end Step

/-! ### Agreement of the oracles with a tree -/

/-- The oracles are correct at every valid extension of `π`, for the subtree `s`. -/
def Agrees (q : List ℕ → Info) (lb : List ℕ → ℕ → Bool) (s : SPTree) (π : List ℕ) : Prop :=
  ∀ ρ, Valid s ρ → q (ρ ++ π) = (node s ρ).info ∧
    ∀ k, (node s ρ).tag = 0 → k < (node s ρ).prec → lb (ρ ++ π) k = (node s ρ).value.testBit k

variable {q : List ℕ → Info} {lb : List ℕ → ℕ → Bool}

theorem Agrees.self {s : SPTree} {π : List ℕ} (h : Agrees q lb s π) : q π = s.info :=
  (h [] trivial).1

theorem Agrees.leaf {s : SPTree} {π : List ℕ} (h : Agrees q lb s π) {k : ℕ} (ht : s.tag = 0)
    (hk : k < s.prec) : lb π k = s.value.testBit k :=
  (h [] trivial).2 k ht hk

theorem Agrees.child {s : SPTree} {π : List ℕ} (h : Agrees q lb s π) {i : ℕ}
    (hi : s.ValidChild i) : Agrees q lb (s.child i) (i :: π) := by
  intro ρ hρ
  have hv : Valid s (ρ ++ [i]) := (valid_append s ρ [i]).mpr ⟨⟨trivial, hi⟩, hρ⟩
  have := h (ρ ++ [i]) hv
  simpa [node_append] using this

/-! ### The simulation -/

theorem toNat_decide_mod (n : ℕ) : (decide (n % 2 = 1)).toNat = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- A call whose bit is at or above the precision returns `0` at once. -/
theorem reaches_call_of_le {s : SPTree} {π : List ℕ} (h : Agrees q lb s π) {k : ℕ}
    (fr : List Frame) (hk : s.prec ≤ k) :
    Reaches q lb ⟨true, k, fr, π⟩ ⟨false, (s.value.testBit k).toNat, fr, π⟩ := by
  refine Reaches.head ?_
  rw [testBit_value_of_le hk]
  simp only [step, h.self, SPTree.info, hk, ite_true]
  exact Reaches.refl _

section SumLoop

variable {P w : ℕ} {f : ℕ → SPTree} {π : List ℕ} {k : ℕ} {fr : List Frame}

/-- The end of a column at a sum node. -/
def sumColEnd (k j : ℕ) (fr : List Frame) (π : List ℕ) (c : ℕ) : State :=
  if j < k then ⟨true, j + 1, ⟨k, j + 1, 0, c / 2⟩ :: fr, 0 :: π⟩ else ⟨false, c % 2, fr, π⟩

theorem sum_index_loop (h : Agrees q lb (sum P w f) π)
    (ih : ∀ i < 2 ^ w, ∀ k' fr', Reaches q lb ⟨true, k', fr', i :: π⟩
      ⟨false, ((f i).value.testBit k').toNat, fr', i :: π⟩) (j : ℕ) :
    ∀ m i c, i + m = 2 ^ w → i < 2 ^ w →
      Reaches q lb ⟨true, j, ⟨k, j, 0, c⟩ :: fr, i :: π⟩
        (sumColEnd k j fr π (c + ∑ t ∈ range m, ((f (i + t)).value.testBit j).toNat)) := by
  intro m
  induction m with
  | zero => intro i c hm hi; omega
  | succ m ihm =>
    intro i c hm hi
    refine (ih i hi j _).trans (Reaches.head ?_)
    have hq : q π = (sum P w f).info := h.self
    by_cases hlast : i + 1 < 2 ^ w
    · simp only [step, List.tail_cons, List.headD_cons, hq, SPTree.info, SPTree.tag,
        SPTree.param, ite_true, hlast]
      have := ihm (i + 1) (c + ((f i).value.testBit j).toNat) (by omega) hlast
      convert this using 2
      have e : ∑ t ∈ range m, ((f (i + 1 + t)).value.testBit j).toNat =
          ∑ t ∈ range m, ((f (i + (t + 1))).value.testBit j).toNat :=
        Finset.sum_congr rfl fun t _ => by rw [show i + 1 + t = i + (t + 1) by omega]
      rw [Finset.sum_range_succ', e]
      simp only [Nat.add_zero]
      omega
    · have hm0 : m = 0 := by omega
      subst hm0
      simp only [step, List.tail_cons, List.headD_cons, hq, SPTree.info, SPTree.tag,
        SPTree.param, ite_true, hlast, ite_false, sumColEnd]
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, Nat.add_zero]
      exact Reaches.refl _

theorem sum_column_loop (h : Agrees q lb (sum P w f) π)
    (ih : ∀ i < 2 ^ w, ∀ k' fr', Reaches q lb ⟨true, k', fr', i :: π⟩
      ⟨false, ((f i).value.testBit k').toNat, fr', i :: π⟩) :
    ∀ d j, j + d = k →
      Reaches q lb ⟨true, j, ⟨k, j, 0, colCarry (sumCol (2 ^ w) fun i => (f i).value) j⟩ :: fr,
          0 :: π⟩
        ⟨false, (colCarry (sumCol (2 ^ w) fun i => (f i).value) k +
          sumCol (2 ^ w) (fun i => (f i).value) k) % 2, fr, π⟩ := by
  intro d
  induction d with
  | zero =>
    intro j hj
    subst hj
    have := sum_index_loop (k := j) (fr := fr) h ih j (2 ^ w) 0
      (colCarry (sumCol (2 ^ w) fun i => (f i).value) j) (by omega) (by positivity)
    simpa [sumColEnd, sumCol] using this
  | succ d ihd =>
    intro j hj
    have := sum_index_loop (k := k) (fr := fr) h ih j (2 ^ w) 0
      (colCarry (sumCol (2 ^ w) fun i => (f i).value) j) (by omega) (by positivity)
    refine this.trans ?_
    have hjk : j < k := by omega
    simp only [sumColEnd, hjk, ite_true, Nat.zero_add]
    exact ihd (j + 1) (by omega)

end SumLoop

section ProdLoop

variable {P : ℕ} {a b : SPTree} {π : List ℕ} {k : ℕ} {fr : List Frame}

/-- The end of a column at a product node. -/
def prodColEnd (k j : ℕ) (fr : List Frame) (π : List ℕ) (c : ℕ) : State :=
  if j < k then ⟨true, 0, ⟨k, j + 1, 0, c / 2⟩ :: fr, 0 :: π⟩ else ⟨false, c % 2, fr, π⟩

theorem prod_split_loop (h : Agrees q lb (prod P a b) π)
    (iha : ∀ k' fr', Reaches q lb ⟨true, k', fr', 0 :: π⟩
      ⟨false, (a.value.testBit k').toNat, fr', 0 :: π⟩)
    (ihb : ∀ k' fr', Reaches q lb ⟨true, k', fr', 1 :: π⟩
      ⟨false, (b.value.testBit k').toNat, fr', 1 :: π⟩) (j : ℕ) :
    ∀ m l c, l + m = j + 1 → l ≤ j →
      Reaches q lb ⟨true, l, ⟨k, j, l, c⟩ :: fr, 0 :: π⟩
        (prodColEnd k j fr π (c + ∑ t ∈ range m,
          (a.value.testBit (l + t)).toNat * (b.value.testBit (j - (l + t))).toNat)) := by
  have hq : q π = (prod P a b).info := h.self
  intro m
  induction m with
  | zero => intro l c hm hl; omega
  | succ m ihm =>
    intro l c hm hlj
    -- The advance after split `l`, with the carry `c'`.
    have hadv : ∀ c', Reaches q lb (advanceProd k j l c' fr π)
        (prodColEnd k j fr π (c' + ∑ t ∈ range m,
          (a.value.testBit (l + (t + 1))).toNat *
              (b.value.testBit (j - (l + (t + 1)))).toNat)) := by
      intro c'
      by_cases hl : l < j
      · simp only [advanceProd, hl, ite_true]
        have := ihm (l + 1) c' (by omega) (by omega)
        have e : ∀ t, l + 1 + t = l + (t + 1) := fun t => by omega
        simpa only [e] using this
      · have hm0 : m = 0 := by omega
        subst hm0
        simp only [advanceProd, hl, ite_false, prodColEnd, Finset.range_zero, Finset.sum_empty,
          Nat.add_zero]
        exact Reaches.refl _
    refine (iha l _).trans (Reaches.head ?_)
    rw [Finset.sum_range_succ']
    simp only [Nat.add_zero]
    cases hx : a.value.testBit l with
    | false =>
      simp only [step, List.tail_cons, List.headD_cons, hq, SPTree.info, SPTree.tag,
        Bool.toNat_false, ite_true, Nat.zero_mul, Nat.add_zero]
      exact hadv c
    | true =>
      simp only [step, List.tail_cons, List.headD_cons, hq, SPTree.info, SPTree.tag,
        Bool.toNat_true, ite_true, ite_false, Nat.one_mul, one_ne_zero]
      refine (ihb (j - l) _).trans (Reaches.head ?_)
      simp only [step, List.tail_cons, List.headD_cons, hq, SPTree.info, SPTree.tag,
        ite_true, ite_false, one_ne_zero]
      rw [show ∀ S y : ℕ, c + (S + y) = c + y + S from fun S y => by omega]
      exact hadv _

theorem prod_column_loop (h : Agrees q lb (prod P a b) π)
    (iha : ∀ k' fr', Reaches q lb ⟨true, k', fr', 0 :: π⟩
      ⟨false, (a.value.testBit k').toNat, fr', 0 :: π⟩)
    (ihb : ∀ k' fr', Reaches q lb ⟨true, k', fr', 1 :: π⟩
      ⟨false, (b.value.testBit k').toNat, fr', 1 :: π⟩) :
    ∀ d j, j + d = k →
      Reaches q lb ⟨true, 0, ⟨k, j, 0, colCarry (prodCol a.value b.value) j⟩ :: fr, 0 :: π⟩
        ⟨false, (colCarry (prodCol a.value b.value) k + prodCol a.value b.value k) % 2,
          fr, π⟩ := by
  intro d
  induction d with
  | zero =>
    intro j hj
    subst hj
    have := prod_split_loop (k := j) (fr := fr) h iha ihb j (j + 1) 0
      (colCarry (prodCol a.value b.value) j) (by omega) (by omega)
    simpa [prodColEnd, prodCol] using this
  | succ d ihd =>
    intro j hj
    have := prod_split_loop (k := k) (fr := fr) h iha ihb j (j + 1) 0
      (colCarry (prodCol a.value b.value) j) (by omega) (by omega)
    refine this.trans ?_
    have hjk : j < k := by omega
    simp only [prodColEnd, hjk, ite_true, Nat.zero_add]
    have e : (colCarry (prodCol a.value b.value) j +
        ∑ t ∈ range (j + 1), (a.value.testBit t).toNat * (b.value.testBit (j - t)).toNat) / 2 =
        colCarry (prodCol a.value b.value) (j + 1) := rfl
    rw [e]
    exact ihd (j + 1) (by omega)

end ProdLoop

/-- **The evaluator is correct.** A call at a node whose oracles agree with a
subtree `s` returns bit `k` of the value of `s`, leaving the stack below it
unchanged. -/
theorem reaches_call : ∀ (s : SPTree) (π : List ℕ) (k : ℕ) (fr : List Frame),
    Agrees q lb s π →
      Reaches q lb ⟨true, k, fr, π⟩ ⟨false, (s.value.testBit k).toNat, fr, π⟩
  | .leaf P v, π, k, fr, h => by
    by_cases hk : P ≤ k
    · exact reaches_call_of_le h fr hk
    · refine Reaches.head ?_
      have hq := h.self
      simp only [step, hq, SPTree.info, SPTree.tag, SPTree.prec, hk, ite_false, ite_true]
      rw [h.leaf rfl (by simp [SPTree.prec]; omega)]
      exact Reaches.refl _
  | .shift P σ a, π, k, fr, h => by
    by_cases hk : P ≤ k
    · exact reaches_call_of_le h fr hk
    · refine Reaches.head ?_
      have hq := h.self
      simp only [step, hq, SPTree.info, SPTree.tag, SPTree.prec, SPTree.param, hk, ite_false,
        ite_true, OfNat.ofNat_ne_zero, OfNat.ofNat_ne_one, false_or]
      have iha := reaches_call a (0 :: π) (k + σ) (⟨k, 0, 0, 0⟩ :: fr)
        (h.child (i := 0) rfl)
      refine iha.trans (Reaches.head ?_)
      simp only [step, List.tail_cons, hq, SPTree.info, SPTree.tag, ite_false,
        OfNat.ofNat_ne_one]
      have : (shift P σ a).value.testBit k = a.value.testBit (k + σ) := by
        simp only [SPTree.value, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]
        simp only [show k < P by omega, decide_true, Bool.true_and]
      rw [this]
      exact Reaches.refl _
  | .sum P w f, π, k, fr, h => by
    by_cases hk : P ≤ k
    · exact reaches_call_of_le h fr hk
    · refine Reaches.head ?_
      have hq := h.self
      simp only [step, hq, SPTree.info, SPTree.tag, SPTree.prec, hk, ite_false,
        one_ne_zero, true_or, ite_true]
      have ih : ∀ i < 2 ^ w, ∀ k' fr', Reaches q lb ⟨true, k', fr', i :: π⟩
          ⟨false, ((f i).value.testBit k').toNat, fr', i :: π⟩ :=
        fun i hi k' fr' => reaches_call (f i) (i :: π) k' fr' (h.child (i := i) hi)
      have := sum_column_loop (k := k) (fr := fr) h ih k 0 (by omega)
      have hv : (sum P w f).value.testBit k =
          decide ((colCarry (sumCol (2 ^ w) fun i => (f i).value) k +
            sumCol (2 ^ w) (fun i => (f i).value) k) % 2 = 1) := by
        simp only [SPTree.value, Nat.testBit_mod_two_pow, show k < P by omega, decide_true,
          Bool.true_and]
        exact testBit_sum_eq _ _ _
      rw [hv, toNat_decide_mod]
      simpa [colCarry] using this
  | .prod P a b, π, k, fr, h => by
    by_cases hk : P ≤ k
    · exact reaches_call_of_le h fr hk
    · refine Reaches.head ?_
      have hq := h.self
      simp only [step, hq, SPTree.info, SPTree.tag, SPTree.prec, hk, ite_false,
        OfNat.ofNat_ne_zero, or_true, ite_true]
      have iha : ∀ k' fr', Reaches q lb ⟨true, k', fr', 0 :: π⟩
          ⟨false, (a.value.testBit k').toNat, fr', 0 :: π⟩ :=
        fun k' fr' => reaches_call a (0 :: π) k' fr' (h.child (i := 0) (show (0 : ℕ) < 2 by omega))
      have ihb : ∀ k' fr', Reaches q lb ⟨true, k', fr', 1 :: π⟩
          ⟨false, (b.value.testBit k').toNat, fr', 1 :: π⟩ :=
        fun k' fr' => reaches_call b (1 :: π) k' fr' (h.child (i := 1) (show (1 : ℕ) < 2 by omega))
      have := prod_column_loop (k := k) (fr := fr) h iha ihb k 0 (by omega)
      have hv : (prod P a b).value.testBit k =
          decide ((colCarry (prodCol a.value b.value) k + prodCol a.value b.value k) % 2 = 1) := by
        simp only [SPTree.value, Nat.testBit_mod_two_pow, show k < P by omega, decide_true,
          Bool.true_and]
        exact testBit_mul_eq _ _ _
      rw [hv, toNat_decide_mod]
      simpa [colCarry] using this

end Cslib.Complexity.NtimeDspace.SumProduct
