/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init

/-!
# Filtered list positions and order-preserving index helpers

Generic list-indexing helpers for positions of elements matching a Boolean predicate `pred`:

* `List.nthFilterPos`: position in `l` of the `n`-th element satisfying `pred`, with bounds,
  strict monotonicity, injectivity, and append equations.
* `List.filter_getElem_count_take`: the `((cs.take k).filter pred).length`-th element of
  `cs.filter pred` is `cs[k]` whenever `pred cs[k] = true`.
* `List.filter_strictMono_indices` and `List.map_eq_of_strictMono_surj`: strictly monotone index
  embeddings for filtered sublists and equality criteria via surjective strictly monotone
  position maps.

## Main definitions

* `List.nthFilterPos`: index of the `n`-th element of a list satisfying a Boolean predicate.

## Main results

* `List.nthFilterPos_strictMono`, `List.nthFilterPos_inj`: `nthFilterPos` is strictly monotone and
  injective in the filtered rank `n`.
* `List.filter_getElem_count_take`: lookup in `cs.filter pred` at the prefix count
  `(cs.take k).filter pred`.
* `List.map_eq_of_strictMono_surj`: a list whose positions are strictly monotone, bounded, and
  surjective onto `0 ..< dst.length` maps onto `dst`.
-/

public section

namespace List

/-- Position in `l` of the `n`-th element satisfying `pred` (`none` if at most `n` elements in `l`
satisfy `pred`). -/
@[expose]
def nthFilterPos {α : Type*} (pred : α → Bool) : List α → ℕ → Option ℕ
  | [], _ => none
  | a :: rest, 0 =>
    if pred a then some 0 else (nthFilterPos pred rest 0).map (· + 1)
  | a :: rest, n + 1 =>
    if pred a then (nthFilterPos pred rest n).map (· + 1)
    else (nthFilterPos pred rest (n + 1)).map (· + 1)

@[simp]
theorem nthFilterPos_nil {α : Type*} (pred : α → Bool) (n : ℕ) :
    nthFilterPos pred [] n = none :=
  rfl

/-- Skipping a head element with `pred a = false` shifts `nthFilterPos` by `1` for every `n`. -/
theorem nthFilterPos_cons_of_false {α : Type*} {pred : α → Bool} {a : α}
    (rest : List α) (n : ℕ) (h : pred a = false) :
    nthFilterPos pred (a :: rest) n = (nthFilterPos pred rest n).map (· + 1) := by
  cases n <;> simp only [nthFilterPos, h, Bool.false_eq_true, ↓reduceIte]

/-- Matching head element at rank `0` occurs at index `0`. -/
theorem nthFilterPos_cons_zero_of_true {α : Type*} {pred : α → Bool} {a : α}
    (rest : List α) (h : pred a = true) :
    nthFilterPos pred (a :: rest) 0 = some 0 := by
  simp only [nthFilterPos, h, ↓reduceIte]

/-- Matching head element at rank `n + 1` shifts the `n`-th match in `rest` by `1`. -/
theorem nthFilterPos_cons_succ_of_true {α : Type*} {pred : α → Bool} {a : α}
    (rest : List α) (n : ℕ) (h : pred a = true) :
    nthFilterPos pred (a :: rest) (n + 1) = (nthFilterPos pred rest n).map (· + 1) := by
  simp only [nthFilterPos, h, ↓reduceIte]

/-- `nthFilterPos pred l n` is `some` iff `l.filter pred` has length strictly greater than `n`. -/
theorem nthFilterPos_isSome_iff {α : Type*} (pred : α → Bool) (l : List α) (n : ℕ) :
    (nthFilterPos pred l n).isSome = true ↔ n < (l.filter pred).length := by
  induction l generalizing n with
  | nil =>
    simp only [nthFilterPos_nil, Option.isSome_none, Bool.false_eq_true, List.filter_nil,
      List.length_nil, Nat.not_lt_zero]
  | cons a rest ih =>
    cases hpa : pred a
    · simp only [nthFilterPos_cons_of_false rest n hpa, List.filter, hpa, Option.isSome_map, ih n]
    · cases n with
      | zero =>
        simp only [nthFilterPos_cons_zero_of_true rest hpa, List.filter, hpa, Option.isSome_some,
          List.length_cons, Nat.zero_lt_succ]
      | succ n =>
        simp only [nthFilterPos_cons_succ_of_true rest n hpa, List.filter, hpa, Option.isSome_map,
          List.length_cons, ih n]
        omega

/-- If `nthFilterPos pred l n = some pos`, then `pos < l.length`, `l[pos]? = (l.filter pred)[n]?`,
and `pred` holds at `l[pos]?`. -/
theorem nthFilterPos_lt_length {α : Type*} {pred : α → Bool} {l : List α} {n pos : ℕ}
    (h : nthFilterPos pred l n = some pos) :
    pos < l.length ∧ l[pos]? = (l.filter pred)[n]? ∧ l[pos]?.map pred = some true := by
  induction l generalizing n pos with
  | nil => simp only [nthFilterPos_nil, reduceCtorEq] at h
  | cons a rest ih =>
    cases hpa : pred a
    · rw [nthFilterPos_cons_of_false rest n hpa, Option.map_eq_some_iff] at h
      obtain ⟨pos', hpos', rfl⟩ := h
      obtain ⟨hlt, hget, hpr⟩ := ih hpos'
      exact ⟨Nat.succ_lt_succ hlt, by simpa [hpa] using hget, by simpa using hpr⟩
    · cases n with
      | zero =>
        obtain rfl : 0 = pos := by simpa [nthFilterPos_cons_zero_of_true rest hpa] using h
        simp [hpa]
      | succ n =>
        rw [nthFilterPos_cons_succ_of_true rest n hpa, Option.map_eq_some_iff] at h
        obtain ⟨pos', hpos', rfl⟩ := h
        obtain ⟨hlt, hget, hpr⟩ := ih hpos'
        exact ⟨Nat.succ_lt_succ hlt, by simpa [hpa] using hget, by simpa using hpr⟩

/-- `nthFilterPos` is strictly monotone in the filtered rank `m < n`. -/
theorem nthFilterPos_strictMono {α : Type*} {pred : α → Bool} {l : List α}
    {m n i j : ℕ} (hmn : m < n) (hm : nthFilterPos pred l m = some i)
    (hn : nthFilterPos pred l n = some j) : i < j := by
  induction l generalizing m n i j with
  | nil => simp only [nthFilterPos_nil, reduceCtorEq] at hm
  | cons a rest ih =>
    cases hpa : pred a
    · rw [nthFilterPos_cons_of_false rest m hpa, Option.map_eq_some_iff] at hm
      rw [nthFilterPos_cons_of_false rest n hpa, Option.map_eq_some_iff] at hn
      obtain ⟨i', hi', rfl⟩ := hm
      obtain ⟨j', hj', rfl⟩ := hn
      exact Nat.succ_lt_succ (ih hmn hi' hj')
    · cases n with
      | zero => omega
      | succ n =>
        rw [nthFilterPos_cons_succ_of_true rest n hpa, Option.map_eq_some_iff] at hn
        obtain ⟨j', hj', rfl⟩ := hn
        cases m with
        | zero =>
          obtain rfl : 0 = i := by simpa [nthFilterPos_cons_zero_of_true rest hpa] using hm
          exact Nat.zero_lt_succ _
        | succ m =>
          rw [nthFilterPos_cons_succ_of_true rest m hpa, Option.map_eq_some_iff] at hm
          obtain ⟨i', hi', rfl⟩ := hm
          exact Nat.succ_lt_succ (ih (Nat.lt_of_succ_lt_succ hmn) hi' hj')

/-- `nthFilterPos` is injective in the filtered rank `n`. -/
theorem nthFilterPos_inj {α : Type*} {pred : α → Bool} {l : List α} {u v w : ℕ}
    (hu : nthFilterPos pred l u = some w) (hv : nthFilterPos pred l v = some w) : u = v := by
  rcases Nat.lt_trichotomy u v with hlt | rfl | hgt
  · exact absurd (nthFilterPos_strictMono hlt hu hv) (Nat.lt_irrefl w)
  · rfl
  · exact absurd (nthFilterPos_strictMono hgt hv hu) (Nat.lt_irrefl w)

/-- Ranks inside `l₁.filter pred` have unchanged positions in `l₁ ++ l₂`. -/
theorem nthFilterPos_append_left {α : Type*} {pred : α → Bool} {l₁ : List α}
    (l₂ : List α) {n : ℕ} (hn : n < (l₁.filter pred).length) :
    nthFilterPos pred (l₁ ++ l₂) n = nthFilterPos pred l₁ n := by
  induction l₁ generalizing n with
  | nil => simp only [List.filter_nil, List.length_nil] at hn; omega
  | cons a rest ih =>
    cases hpa : pred a
    · simp only [List.filter, hpa] at hn
      simp only [List.cons_append, nthFilterPos_cons_of_false _ n hpa, ih hn]
    · cases n with
      | zero => simp only [List.cons_append, nthFilterPos_cons_zero_of_true _ hpa]
      | succ n =>
        simp only [List.filter, hpa, List.length_cons] at hn
        simp only [List.cons_append, nthFilterPos_cons_succ_of_true _ n hpa,
          ih (n := n) (by omega)]

/-- Ranks at or beyond `(l₁.filter pred).length` shift into `l₂` by `l₁.length`. -/
theorem nthFilterPos_append_right {α : Type*} {pred : α → Bool} (l₁ l₂ : List α)
    {n : ℕ} (hn : (l₁.filter pred).length ≤ n) :
    nthFilterPos pred (l₁ ++ l₂) n =
      (nthFilterPos pred l₂ (n - (l₁.filter pred).length)).map (· + l₁.length) := by
  induction l₁ generalizing n with
  | nil =>
    simp only [List.nil_append, List.filter_nil, List.length_nil, Nat.sub_zero, Nat.add_zero,
      Option.map_id']
  | cons a rest ih =>
    cases hpa : pred a
    · simp only [List.filter, hpa] at hn ⊢
      simp only [List.cons_append, nthFilterPos_cons_of_false _ n hpa, ih hn, Option.map_map,
        List.length_cons, Function.comp_def, Nat.add_assoc]
    · cases n with
      | zero => simp only [List.filter, hpa, List.length_cons] at hn; omega
      | succ n =>
        simp only [List.filter, hpa, List.length_cons] at hn ⊢
        rw [List.cons_append, nthFilterPos_cons_succ_of_true _ n hpa, ih (n := n) (by omega),
          Option.map_map]
        have hsub : n + 1 - ((rest.filter pred).length + 1) =
            n - (rest.filter pred).length := by omega
        simp only [hsub, Function.comp_def, Nat.add_assoc]

/-- Any match of `nthFilterPos pred (l₁ ++ l₂)` landing strictly before `l₁.length` comes from
`l₁`. -/
theorem nthFilterPos_of_append_lt {α : Type*} {pred : α → Bool} {l₁ l₂ : List α}
    {n pos : ℕ} (h : nthFilterPos pred (l₁ ++ l₂) n = some pos) (hlt : pos < l₁.length) :
    nthFilterPos pred l₁ n = some pos := by
  by_cases hn : n < (l₁.filter pred).length
  · rwa [nthFilterPos_append_left l₂ hn] at h
  · rw [nthFilterPos_append_right l₁ l₂ (by omega), Option.map_eq_some_iff] at h
    obtain ⟨_, _, rfl⟩ := h
    omega

/-- If `pred cs[k] = true`, then `cs[k]` sits in `cs.filter pred` at index
`((cs.take k).filter pred).length`. -/
theorem filter_getElem_count_take {α : Type*} (pred : α → Bool) :
    ∀ (cs : List α) (k : ℕ) (hk : k < cs.length), pred cs[k] = true →
      ∃ hlt : ((cs.take k).filter pred).length < (cs.filter pred).length,
        (cs.filter pred)[((cs.take k).filter pred).length]'hlt = cs[k]
  | [], _, hk, _ => by simp only [List.length_nil] at hk; omega
  | c :: rest, 0, _, hpred => by
    simp only [List.getElem_cons_zero] at hpred
    rw [List.getElem_cons_zero, List.take_zero, List.filter_nil, List.length_nil,
      List.filter_cons_of_pos hpred]
    exact ⟨Nat.zero_lt_succ _, rfl⟩
  | c :: rest, k + 1, hk, hpred => by
    obtain ⟨hlt', heq'⟩ := filter_getElem_count_take pred rest k (Nat.lt_of_succ_lt_succ hk)
      (by simpa using hpred)
    cases hpc : pred c
    · simp only [List.take_succ_cons, List.filter, hpc, List.getElem_cons_succ]
      exact ⟨hlt', heq'⟩
    · simp only [List.take_succ_cons, List.filter, hpc, List.length_cons, List.getElem_cons_succ]
      exact ⟨Nat.succ_lt_succ hlt', heq'⟩

private theorem strictMono_list_eq_range' :
    ∀ (m s : ℕ) (L : List ℕ),
      List.Pairwise (· < ·) L →
      (∀ x ∈ L, s ≤ x ∧ x < s + m) →
      (∀ k, s ≤ k → k < s + m → k ∈ L) →
      L = List.range' s m
  | 0, _, L, _, hbd, _ => by
    cases L with
    | nil => rfl
    | cons a _ => have := hbd a List.mem_cons_self; omega
  | m + 1, s, L, hpw, hbd, hsurj => by
    have hs_mem : s ∈ L := hsurj s (Nat.le_refl s) (by omega)
    cases L with
    | nil => cases hs_mem
    | cons a tail =>
      obtain ⟨ha_tail, hpw_tail⟩ := List.pairwise_cons.mp hpw
      obtain rfl : a = s := by
        rcases List.mem_cons.mp hs_mem with rfl | htail
        · rfl
        · have := ha_tail s htail
          have := (hbd a List.mem_cons_self).1
          omega
      simp only [List.range'_succ]
      refine congrArg (a :: ·) (strictMono_list_eq_range' m (a + 1) tail hpw_tail ?_ ?_)
      · intro x hx
        have := ha_tail x hx
        have := hbd x (List.mem_cons_of_mem _ hx)
        omega
      · intro k hk₁ hk₂
        rcases List.mem_cons.mp (hsurj k (by omega) (by omega)) with rfl | hkt
        · omega
        · exact hkt

/-- If `pos : β → ℕ` is strictly monotone on `src`, bounded below `dst.length`, and surjective
onto `0 ..< dst.length` with `val b = dst[pos b]`, then `src.map pos = List.range dst.length` and
`src.map val = dst`. -/
theorem map_eq_of_strictMono_surj {β γ : Type*} {src : List β} {dst : List γ}
    (pos : β → ℕ) (val : β → γ)
    (hvalid : ∀ b ∈ src, ∃ hlt : pos b < dst.length, val b = dst[pos b]'hlt)
    (hmono : ∀ i j (hi : i < src.length) (hj : j < src.length), i < j → pos src[i] < pos src[j])
    (hsurj : ∀ k < dst.length, ∃ b ∈ src, pos b = k) :
    src.map pos = List.range dst.length ∧ src.map val = dst := by
  have hpw : List.Pairwise (· < ·) (src.map pos) :=
    List.pairwise_iff_getElem.mpr fun i j hi hj hij => by
      simpa using hmono i j (by simpa using hi) (by simpa using hj) hij
  have hrange : src.map pos = List.range dst.length := by
    rw [List.range_eq_range']
    refine strictMono_list_eq_range' dst.length 0 (src.map pos) hpw (fun x hx => ?_)
      fun k _ hk => ?_
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hx
      obtain ⟨hlt, _⟩ := hvalid b hb
      exact ⟨Nat.zero_le _, by omega⟩
    · obtain ⟨b, hb, rfl⟩ := hsurj k (by omega)
      exact List.mem_map_of_mem hb
  have hlen : src.length = dst.length := by
    simpa using congrArg List.length hrange
  refine ⟨hrange, List.ext_getElem (by simp [hlen]) fun i hi₁ hi₂ => ?_⟩
  simp only [List.length_map] at hi₁
  have hpos_i : pos src[i] = i := by
    simpa [hi₁, hi₂] using congrArg (fun l => l[i]?) hrange
  obtain ⟨_, hval⟩ := hvalid src[i] (List.getElem_mem hi₁)
  simp only [List.getElem_map, hval, hpos_i]

private theorem exists_fin_idx_of_eq {α : Type*} {l₁ l₂ l : List α} (heq : l₁ = l₂)
    (h : ∃ idx : Fin l₂.length → Fin l.length,
      (∀ i, l₂[i.val] = l[(idx i).val]) ∧ (∀ i j, i.val < j.val → (idx i).val < (idx j).val)) :
    ∃ idx : Fin l₁.length → Fin l.length,
      (∀ i, l₁[i.val] = l[(idx i).val]) ∧ (∀ i j, i.val < j.val → (idx i).val < (idx j).val) := by
  subst heq; exact h

/-- Every filtered sublist `l.filter pred` embeds into `l` via a strictly monotone index map. -/
theorem filter_strictMono_indices {α : Type*} (l : List α) (pred : α → Bool) :
    ∃ idx : Fin (l.filter pred).length → Fin l.length,
      (∀ i, (l.filter pred)[i.val] = l[(idx i).val]) ∧
      (∀ i j, i.val < j.val → (idx i).val < (idx j).val) := by
  induction l with
  | nil => exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | cons a rest ih =>
    obtain ⟨idx', hval', hmono'⟩ := ih
    by_cases hpa : pred a = true
    · refine exists_fin_idx_of_eq (List.filter_cons_of_pos hpa)
        ⟨Fin.cases ⟨0, Nat.zero_lt_succ _⟩ (fun i' => (idx' i').succ), ?_, ?_⟩
      · refine Fin.cases rfl fun i' => ?_
        simpa only [Fin.cases_succ, Fin.val_succ, List.getElem_cons_succ] using hval' i'
      · refine Fin.cases (Fin.cases (by simp) fun _ _ => Nat.zero_lt_succ _) fun i' =>
          Fin.cases (by simp) fun j' hij => ?_
        exact Nat.succ_lt_succ (hmono' i' j' (Nat.lt_of_succ_lt_succ hij))
    · refine exists_fin_idx_of_eq (List.filter_cons_of_neg hpa)
        ⟨fun i => (idx' i).succ, fun i => ?_, fun i j hij => Nat.succ_lt_succ (hmono' i j hij)⟩
      simpa only [Fin.val_succ, List.getElem_cons_succ] using hval' i

end List
