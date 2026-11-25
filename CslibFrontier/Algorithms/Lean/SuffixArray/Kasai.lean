/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.SuffixArray.Basic

/-!
# Kasai et al.'s linear-time LCP array construction

Given a word `w` and its suffix array `sa`, the algorithm of Kasai, Lee, Arimura, Arikawa and Park
(`[KasaiLeeArimuraArikawaPark2001]`) computes the LCP array by visiting the suffixes in text order
`i = 0, 1, …, |w| - 1`. It compares the suffix at `i` with its predecessor in `sa` starting from
the previous common-prefix length minus one, which the height lemma
(`IsSuffixArray.getElem_lcpArray_sub_one_le`) shows is already a common prefix. The common-prefix
length drops by at most one per step and never exceeds the remaining length.

Machine-level `O(|w|)` running-time bounds on word arrays are proved in
`CslibFrontier.Algorithms.WordRAM.SuffixArray`.

## Source Conventions

* **Indexing:** `0`-based positions and ranks, as in `Cslib.Algorithms.Lean.SuffixArray.Basic`;
  the result has `lcp[0] = 0`.
* **Rank array:** `rankArray w.size sa.toList` stores `r` at position `sa[r]`, the inverse
  permutation of `sa`.

## Main definitions

* `Cslib.Algorithms.Lean.SuffixArray.rankArray`: inverse of a list of distinct positions.
* `Cslib.Algorithms.Lean.SuffixArray.kasaiLoop`, `kasaiArray`, `kasai`: pure Kasai LCP construction
  on arrays and its list wrapper.

## Main results

* `Cslib.Algorithms.Lean.SuffixArray.getElem!_rankArray`: `rankArray n sa` inverts `sa`.
* `Cslib.Algorithms.Lean.SuffixArray.rankArray_append_singleton`: incremental scatter step of
  `rankArray`.
* `Cslib.Algorithms.Lean.SuffixArray.kasaiArray_toList` and `kasai_eq_lcpArray`: on a suffix array
  the algorithm returns the LCP array.

## References

* [T. Kasai, G. Lee, H. Arimura, S. Arikawa, and K. Park, *Linear-Time Longest-Common-Prefix
  Computation in Suffix Arrays and Its Applications*][KasaiLeeArimuraArikawaPark2001]
-/

public section

namespace Cslib.Algorithms.Lean.SuffixArray

variable {α : Type*}

/-! ## Kasai et al.: the algorithm -/

/-- Inverse of a list of positions: `rankArray n sa` has size `n` and stores `r` at position
`sa[r]`. -/
def rankArray (n : ℕ) (sa : List ℕ) : Array ℕ :=
  go sa 0 (Array.replicate n 0)
where
  /-- Store ranks `r, r + 1, …` at the positions listed in `l`. -/
  go : List ℕ → ℕ → Array ℕ → Array ℕ
    | [], _, rk => rk
    | i :: l, r, rk => go l (r + 1) (rk.set! i r)

@[simp] theorem rankArray_nil (n : ℕ) : rankArray n [] = Array.replicate n 0 := by rfl

private theorem rankArray_go_append (l₁ l₂ : List ℕ) (r : ℕ) (rk : Array ℕ) :
    rankArray.go (l₁ ++ l₂) r rk = rankArray.go l₂ (r + l₁.length) (rankArray.go l₁ r rk) := by
  induction l₁ generalizing r rk with
  | nil => simp only [List.nil_append, List.length_nil, Nat.add_zero, rankArray.go]
  | cons i l₁ ih =>
    simp only [List.cons_append, List.length_cons, rankArray.go, ih]
    congr 1
    omega

/-- Scattering one additional suffix-array entry appends a single `Array.set!` at rank
`sa.length`. -/
theorem rankArray_append_singleton (n : ℕ) (sa : List ℕ) (i : ℕ) :
    rankArray n (sa ++ [i]) = (rankArray n sa).set! i sa.length := by
  simp only [rankArray, rankArray_go_append, Nat.zero_add, rankArray.go]

private theorem rankArray_go_getElem?_of_not_mem (l : List ℕ) (r : ℕ) (rk : Array ℕ) {x : ℕ}
    (hx : x ∉ l) : (rankArray.go l r rk)[x]? = rk[x]? := by
  induction l generalizing r rk with
  | nil => rfl
  | cons i l ih =>
    rw [List.mem_cons, not_or] at hx
    rw [rankArray.go, ih _ _ hx.2, Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
    simp only [Ne.symm hx.1, ↓reduceIte]

private theorem size_rankArray_go (l : List ℕ) (r : ℕ) (rk : Array ℕ) :
    (rankArray.go l r rk).size = rk.size := by
  induction l generalizing r rk with
  | nil => rfl
  | cons i l ih => rw [rankArray.go, ih, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]

private theorem rankArray_go_getElem? {l : List ℕ} (hl : l.Nodup) (r : ℕ) {rk : Array ℕ}
    (hlt : ∀ i ∈ l, i < rk.size) (k : ℕ) (hk : k < l.length) :
    (rankArray.go l r rk)[l[k]]? = some (r + k) := by
  induction l generalizing r rk k with
  | nil => simp only [List.length_nil] at hk; omega
  | cons i l ih =>
    rw [List.nodup_cons] at hl
    have hi : i < rk.size := hlt i List.mem_cons_self
    rw [rankArray.go]
    cases k with
    | zero =>
      rw [List.getElem_cons_zero, rankArray_go_getElem?_of_not_mem _ _ _ hl.1,
        Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds_self_of_lt hi, Nat.add_zero]
    | succ k =>
      rw [List.getElem_cons_succ, ih hl.2 (r + 1) (fun j hj => by
        rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
        exact hlt j (List.mem_cons_of_mem i hj)) k (by simp only [List.length_cons] at hk; omega)]
      congr 1
      omega

@[simp] theorem size_rankArray (n : ℕ) (sa : List ℕ) : (rankArray n sa).size = n := by
  rw [rankArray, size_rankArray_go, Array.size_replicate]

/-- `rankArray n sa` inverts `sa` when `sa` lists distinct positions below `n`. -/
theorem getElem!_rankArray {n : ℕ} {sa : List ℕ} (hnd : sa.Nodup) (hlt : ∀ i ∈ sa, i < n)
    {r : ℕ} (hr : r < sa.length) : (rankArray n sa)[sa[r]]! = r := by
  have h := rankArray_go_getElem? hnd 0 (rk := Array.replicate n 0)
    (fun i hi => by rw [Array.size_replicate]; exact hlt i hi) r hr
  rw [Nat.zero_add] at h
  have hlt' : sa[r] < (rankArray n sa).size := by
    rw [size_rankArray]; exact hlt _ (List.getElem_mem hr)
  rw [getElem!_pos (rankArray n sa) sa[r] hlt']
  exact Option.some.inj (by rwa [← getElem?_pos (rankArray n sa) sa[r] hlt', rankArray])

section Algorithm

variable [DecidableEq α]

/-- Starting from a known common prefix length `h`, extend the common prefix of the suffixes
of `w` at positions `j` and `i` one character at a time. -/
private def extend (w : Array α) (j i h : ℕ) : ℕ :=
  if hlt : j + h < w.size ∧ i + h < w.size then
    if w[j + h]'hlt.1 = w[i + h]'hlt.2 then
      extend w j i (h + 1)
    else
      h
  else
    h
termination_by w.size - (i + h)

/-- Extending the common prefix of the suffixes at `j` and `i` from `h` yields
`h + List.lcpLen (w.drop (j + h)) (w.drop (i + h))`. -/
private theorem extend_eq_add_lcpLen (w : Array α) (j i h : ℕ) :
    extend w j i h = h + List.lcpLen (w.toList.drop (j + h)) (w.toList.drop (i + h)) := by
  fun_induction extend w j i h with
  | case1 h hlt heq ih =>
    rw [ih, List.drop_eq_getElem_cons (i := j + h) (l := w.toList) (by simpa using hlt.1),
      List.drop_eq_getElem_cons (i := i + h) (l := w.toList) (by simpa using hlt.2),
      Array.getElem_toList, Array.getElem_toList, heq, List.lcpLen_cons_cons_self,
      show j + (h + 1) = j + h + 1 by omega, show i + (h + 1) = i + h + 1 by omega]
    omega
  | case2 h hlt hne =>
    rw [List.drop_eq_getElem_cons (i := j + h) (l := w.toList) (by simpa using hlt.1),
      List.drop_eq_getElem_cons (i := i + h) (l := w.toList) (by simpa using hlt.2),
      Array.getElem_toList, Array.getElem_toList, List.lcpLen_cons_cons]
    simp only [hne, ↓reduceIte, Nat.add_zero]
  | case3 h hlt =>
    have h1 := List.lcpLen_le_length_left (w.toList.drop (j + h)) (w.toList.drop (i + h))
    have h2 := List.lcpLen_le_length_right (w.toList.drop (j + h)) (w.toList.drop (i + h))
    simp only [List.length_drop, Array.length_toList] at h1 h2
    omega

/-- The main loop of Kasai et al.'s construction at text position `i`, with current common-prefix
length `h`. -/
def kasaiLoop (w : Array α) (sa rk : Array ℕ) (i h : ℕ) (lcp : Array ℕ) : Array ℕ :=
  if i < w.size then
    if rk[i]! = 0 then
      kasaiLoop w sa rk (i + 1) h lcp
    else
      let h' := extend w sa[rk[i]! - 1]! i h
      kasaiLoop w sa rk (i + 1) (h' - 1) (lcp.set! rk[i]! h')
  else
    lcp
termination_by w.size - i

/-- Once `i` reaches `w.size`, `kasaiLoop` returns the accumulated `lcp` array. -/
theorem kasaiLoop_of_le (w : Array α) (sa rk : Array ℕ) {i : ℕ} (hi : w.size ≤ i) (h : ℕ)
    (lcp : Array ℕ) : kasaiLoop w sa rk i h lcp = lcp := by
  rw [kasaiLoop, ite_eq_right (Nat.not_lt.mpr hi)]

/-- At rank `0`, `kasaiLoop` advances `i` without modifying `h` or `lcp`. -/
theorem kasaiLoop_of_rk_zero (w : Array α) (sa rk : Array ℕ) {i : ℕ} (hi : i < w.size)
    (hr : rk[i]! = 0) (h : ℕ) (lcp : Array ℕ) :
    kasaiLoop w sa rk i h lcp = kasaiLoop w sa rk (i + 1) h lcp := by
  rw [kasaiLoop, ite_eq_left hi, ite_eq_left hr]

/-- At a nonzero rank `rk[i]!`, `kasaiLoop` extends `h` by the longest common prefix from
`sa[rk[i]! - 1]! + h` and `i + h`, records `h'` at `rk[i]!`, and continues from `h' - 1`. -/
theorem kasaiLoop_of_rk_ne_zero (w : Array α) (sa rk : Array ℕ) {i : ℕ} (hi : i < w.size)
    (hr : rk[i]! ≠ 0) (h : ℕ) (lcp : Array ℕ) :
    kasaiLoop w sa rk i h lcp =
      let h' := h + List.lcpLen (w.toList.drop (sa[rk[i]! - 1]! + h)) (w.toList.drop (i + h))
      kasaiLoop w sa rk (i + 1) (h' - 1) (lcp.set! rk[i]! h') := by
  rw [kasaiLoop, ite_eq_left hi, ite_eq_right hr, extend_eq_add_lcpLen]

@[simp] theorem size_kasaiLoop (w : Array α) (sa rk : Array ℕ) (i h : ℕ) (lcp : Array ℕ) :
    (kasaiLoop w sa rk i h lcp).size = lcp.size := by
  fun_induction kasaiLoop w sa rk i h lcp with
  | case1 _ _ _ _ _ ih => exact ih
  | case2 _ _ _ _ _ _ ih =>
    rw [ih, Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
  | case3 => rfl

/-- Kasai et al.'s LCP construction on arrays: visit the positions `i = 0, 1, …` in text order,
extend the common prefix of the suffix at `i` and its predecessor in `sa` from the previous length
minus one, and record it at rank `rank[i]`. -/
@[expose] def kasaiArray (w : Array α) (sa : Array ℕ) : Array ℕ :=
  kasaiLoop w sa (rankArray w.size sa.toList) 0 0 (Array.replicate w.size 0)

@[simp] theorem size_kasaiArray (w : Array α) (sa : Array ℕ) :
    (kasaiArray w sa).size = w.size := by
  rw [kasaiArray, size_kasaiLoop, Array.size_replicate]

/-- Kasai et al.'s LCP construction on lists. -/
@[expose] def kasai (w : List α) (sa : List ℕ) : List ℕ :=
  (kasaiArray w.toArray sa.toArray).toList

@[simp] theorem length_kasai (w : List α) (sa : List ℕ) : (kasai w sa).length = w.length := by
  rw [kasai, Array.length_toList, size_kasaiArray, List.size_toArray]

end Algorithm

/-! ## Correctness -/

section Correctness

variable [LinearOrder α]

/-- Loop invariant: `h` is a lower bound for the LCP entry of the suffix at `i`, and the entries
of all ranks whose suffixes start before `i` (and rank `0`) are already correct. -/
private theorem kasaiLoop_spec {w : Array α} {sa rk : Array ℕ}
    (hsa : IsSuffixArray w.toList sa.toList)
    (hrk : ∀ (r : ℕ) (hr : r < sa.size), rk[sa[r]]! = r) {i h : ℕ} {lcp : Array ℕ}
    (hi : i ≤ w.size) (hsize : lcp.size = w.size)
    (hh : ∀ (r : ℕ) (hr : r < sa.size), sa[r] = i →
      h ≤ (lcpArray w.toList sa.toList)[r]'(by simpa using hr))
    (hdone : ∀ (r : ℕ) (hr : r < sa.size), (r = 0 ∨ sa[r] < i) →
      lcp[r]'(by have := hsa.length_eq; simp only [Array.length_toList] at this; omega) =
        (lcpArray w.toList sa.toList)[r]'(by simpa using hr)) :
    (kasaiLoop w sa rk i h lcp).toList = lcpArray w.toList sa.toList := by
  have hlen : sa.size = w.size := by simpa only [Array.length_toList] using hsa.length_eq
  have hinj : ∀ (r r' : ℕ) (hr : r < sa.size) (hr' : r' < sa.size), sa[r] = sa[r'] → r = r' :=
    fun r r' hr hr' h => (hsa.nodup.getElem_inj_iff (i := r) (j := r')
      (hi := by simpa using hr) (hj := by simpa using hr')).1
      (by simpa only [Array.getElem_toList] using h)
  have hsalt : ∀ (r : ℕ) (hr : r < sa.size), sa[r] < w.size := fun r hr => by
    have := hsa.getElem_lt (r := r) (by simpa using hr)
    simpa only [Array.getElem_toList, Array.length_toList] using this
  have hrank : ∀ {i : ℕ}, i < w.size →
      ∃ r, ∃ hr : r < sa.size, sa[r] = i ∧ rk[i]! = r := fun {i} hiw => by
    obtain ⟨r, hr, hri⟩ := hsa.exists_getElem_eq (by simpa only [Array.length_toList] using hiw)
    simp only [Array.length_toList, Array.getElem_toList] at hr hri
    exact ⟨r, hr, hri, hri ▸ hrk r hr⟩
  have hprev : ∀ {i r r' : ℕ} (hr : r < sa.size) (hr' : r' < sa.size),
      sa[r] = i → r ≠ r' → (r' = 0 ∨ sa[r'] < i + 1) → r' = 0 ∨ sa[r'] < i := by
    rintro i r r' hr hr' rfl hne (rfl | hlt)
    · exact Or.inl rfl
    · exact Or.inr (Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hlt) fun h =>
        hne (hinj r r' hr hr' h.symm))
  fun_induction kasaiLoop w sa rk i h lcp with
  | case1 i h lcp hiw hr0 ih =>
    obtain ⟨r, hr, hri, hrki⟩ := hrank hiw
    rw [hrki] at hr0; subst hr0
    refine ih (by omega) hsize (fun r' hr' hr'i => ?_) (fun r' hr' hr'd => ?_)
    · have h0 := hh 0 hr hri
      rw [getElem_lcpArray_zero] at h0; omega
    · exact hdone r' hr' ((eq_or_ne 0 r').elim (Or.inl ∘ Eq.symm) fun hne =>
        hprev hr hr' hri hne hr'd)
  | case2 i h lcp hiw hr0 h' ih =>
    obtain ⟨r, hr, hri, hrki⟩ := hrank hiw
    rw [hrki] at hr0
    have hr1 : r - 1 < sa.size := by omega
    have hlcpr : (lcpArray w.toList sa.toList)[r]'(by simpa using hr) =
        List.lcpLen (w.toList.drop sa[r - 1]) (w.toList.drop i) := by
      rw [getElem_lcpArray_of_pos _ _ _ (Nat.pos_of_ne_zero hr0)]
      simp only [Array.getElem_toList, hri]
    have hext : h' = (lcpArray w.toList sa.toList)[r]'(by simpa using hr) := by
      change extend w sa[rk[i]! - 1]! i h = _
      rw [hrki, getElem!_pos sa (r - 1) hr1, extend_eq_add_lcpLen, hlcpr]
      symm
      rw [List.lcpLen_eq_add_lcpLen_drop (hlcpr ▸ hh r hr hri), List.drop_drop, List.drop_drop]
    have hsize' : (lcp.set! rk[i]! h').size = w.size := by
      rwa [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds]
    refine ih (by omega) hsize' (fun r' hr' hr'i => ?_) (fun r' hr' hr'd => ?_)
    · rw [hext]
      exact hsa.getElem_lcpArray_sub_one_le (r := r) (r' := r') (by simpa using hr)
        (by simpa using hr') (by simp only [Array.getElem_toList, hri, hr'i])
    · simp only [hrki, hext, Array.set!_eq_setIfInBounds]
      rcases eq_or_ne r r' with rfl | hrr
      · rw [Array.getElem_setIfInBounds_self]
      · rw [Array.getElem_setIfInBounds_ne (by omega) hrr]
        exact hdone r' hr' (hprev hr hr' hri hrr hr'd)
  | case3 i h lcp hiw =>
    apply List.ext_getElem (by simp only [Array.length_toList, length_lcpArray]; omega)
    intro r h1 h2
    simp only [Array.length_toList] at h1
    rw [Array.getElem_toList]
    exact hdone r (by omega) (Or.inr (by have := hsalt r (by omega); omega))

/-- **Correctness of Kasai et al.'s algorithm**: on a suffix array, `kasaiArray` returns the LCP
array. -/
theorem kasaiArray_toList {w : Array α} {sa : Array ℕ} (hsa : IsSuffixArray w.toList sa.toList) :
    (kasaiArray w sa).toList = lcpArray w.toList sa.toList := by
  refine kasaiLoop_spec hsa (fun r hr => ?_) (Nat.zero_le _) Array.size_replicate
    (fun _ _ _ => Nat.zero_le _) (fun r hr hr0 => ?_)
  · have := getElem!_rankArray (n := w.size) hsa.nodup (fun i hi => by
      simpa only [Array.length_toList] using hsa.mem_iff.mp hi) (r := r) (by simpa using hr)
    simpa only [Array.getElem_toList] using this
  · rcases hr0 with rfl | hlt
    · rw [Array.getElem_replicate, getElem_lcpArray_zero]
    · omega

/-- **Correctness of Kasai et al.'s algorithm** on lists. -/
theorem kasai_eq_lcpArray {w : List α} {sa : List ℕ} (hsa : IsSuffixArray w sa) :
    kasai w sa = lcpArray w sa :=
  kasaiArray_toList (w := w.toArray) (sa := sa.toArray) hsa

end Correctness

end Cslib.Algorithms.Lean.SuffixArray
