/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.KMP.Search
public import CslibFrontier.Algorithms.Lean.ZFunction.Basic

/-!
# From a KMP prefix table to a Z-array

`prefixWord` assigns a representative index to each position, reading the prefix table from
left to right. A positive proper border forces its last letter to equal the last letter of the
corresponding prefix. A zero entry leaves the position free to introduce a fresh letter.

`fromPrefix_computePrefix` proves that the existing Z algorithm on this word recovers the Z-array
of every original word realizing the table. Representatives may distinguish equal original
letters, but they preserve every match against the start of the word.
-/

public section

namespace Cslib.Algorithms.Lean.ZFunction

private def appendLetter (word : Array ℕ) (k : ℕ) : Array ℕ :=
  word.push (if h : 0 < k ∧ k ≤ word.size then word[k - 1]'(by omega) else word.size)

private def buildWord (pi word : Array ℕ) : Array ℕ :=
  if h : word.size < pi.size then
    buildWord pi (appendLetter word pi[word.size])
  else word
termination_by pi.size - word.size
decreasing_by simp only [appendLetter, Array.size_push]; omega

/-- A word of representative indices determined by a numeric prefix table. At position `i`,
a positive entry `k ≤ i` copies the representative at `k - 1`. A zero or out-of-range entry
introduces `i` as a fresh letter. -/
def prefixWord (pi : Array ℕ) : Array ℕ := buildWord pi #[]

private def EntriesAgree (pi word : Array ℕ) : Prop :=
  ∀ i (hi : i < word.size) (hp : i < pi.size),
    word[i] = if h : 0 < pi[i] ∧ pi[i] ≤ i then word[pi[i] - 1]'(by omega) else i

private theorem entriesAgree_appendLetter {pi word : Array ℕ} (hp : word.size < pi.size)
    (hw : EntriesAgree pi word) : EntriesAgree pi (appendLetter word pi[word.size]) := by
  intro i hi hi'
  unfold appendLetter at hi ⊢
  by_cases h : i < word.size
  · rw [Array.getElem_push_lt h, hw i h hi']
    split
    · exact (Array.getElem_push_lt (by omega)).symm
    · rfl
  · have heq : i = word.size := by simp only [Array.size_push] at hi; omega
    subst i
    rw [Array.getElem_push_eq]
    split
    · exact (Array.getElem_push_lt (by omega)).symm
    · rfl

private theorem buildWord_spec (pi word : Array ℕ) (hle : word.size ≤ pi.size)
    (hw : EntriesAgree pi word) :
    (buildWord pi word).size = pi.size ∧ EntriesAgree pi (buildWord pi word) := by
  fun_induction buildWord pi word with
  | case1 word hp ih =>
    exact ih (by simp only [appendLetter, Array.size_push]; omega) (entriesAgree_appendLetter hp hw)
  | case2 word hp => exact ⟨by omega, hw⟩

@[simp] theorem size_prefixWord (pi : Array ℕ) : (prefixWord pi).size = pi.size :=
  (buildWord_spec pi #[] (Nat.zero_le _) (fun _ h _ => by simp at h)).1

/-- Each entry of the representative word is either a previously assigned letter or its own
position. This recurrence also specifies the result on malformed tables. -/
theorem getElem_prefixWord (pi : Array ℕ) (i : ℕ) (hi : i < pi.size) :
    (prefixWord pi)[i]'(by simpa only [size_prefixWord] using hi) =
      if h : 0 < pi[i] ∧ pi[i] ≤ i then
        (prefixWord pi)[pi[i] - 1]'(by rw [size_prefixWord]; omega)
      else i :=
  (buildWord_spec pi #[] (Nat.zero_le _) (fun _ h _ => by simp at h)).2 i
    (by change i < (prefixWord pi).size; simpa only [size_prefixWord] using hi) hi

/-- Convert a numeric KMP prefix table into a Z-array by executing the Z algorithm on its word
of representative indices. -/
@[expose] def fromPrefix (pi : Array ℕ) : Array ℕ := zArray (prefixWord pi)

private theorem border_iff_letters {α : Type*} (s : Array α) {k q : ℕ} (hk : k < q)
    (hq : q ≤ s.size) :
    KMP.IsProperBorderLen (s.toList.take q) k ↔
      ∀ j (hj : j < k), s[j]'(by omega) = s[q - k + j]'(by omega) := by
  rw [KMP.isProperBorderLen_iff_isPeriod]
  have hlen : (s.toList.take q).length = q := List.length_take_of_le (by simpa only
    [Array.length_toList] using hq)
  simp only [KMP.IsPeriod, hlen, hk, true_and, List.getElem_take, Array.getElem_toList]
  exact ⟨fun h j hj => by simpa only [Nat.add_comm] using h j (by omega),
    fun h j hj => by simpa only [Nat.add_comm] using h j (by omega)⟩

private theorem le_lcpLen_iff_letters {α : Type*} [DecidableEq α] (s : Array α)
    {t k : ℕ} (h : t + k ≤ s.size) :
    k ≤ List.lcpLen s.toList (s.toList.drop t) ↔
      ∀ j (hj : j < k), s[j]'(by omega) = s[t + j]'(by omega) := by
  have hk : k ≤ s.size := by omega
  have hdrop : k ≤ s.size - t := by omega
  simp only [List.le_lcpLen_iff, List.ext_getElem_iff, List.length_take, List.length_drop,
    Array.length_toList, Nat.min_eq_left hk, Nat.min_eq_left hdrop, hk, hdrop, true_and,
    List.getElem_take, List.getElem_drop, Array.getElem_toList]
  exact ⟨fun h j hj => h j hj hj, fun h j hj _ => h j hj⟩

variable {α : Type*} [DecidableEq α]

-- A total read avoids carrying bounds through each step down a border chain.
private abbrev letter (s : Array α) (i : ℕ) : ℕ :=
  (prefixWord (KMP.computePrefix s)).getD i 0

private theorem letter_at (s : Array α) (i : ℕ) (hi : i < s.size) :
    letter s i = (prefixWord (KMP.computePrefix s))[i]'(by simpa using hi) := by
  rw [letter, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa using hi),
    Option.getD_some]

private theorem letter_step (s : Array α) (i : ℕ) (hi : i < s.size) :
    letter s i = if KMP.borderLen s.toList (i + 1) = 0 then i
      else letter s (KMP.borderLen s.toList (i + 1) - 1) := by
  have hip : i < (KMP.computePrefix s).size := by simpa only [KMP.computePrefix_size] using hi
  have hle := KMP.isDecreasingTable_computePrefix s i hip
  have htab := KMP.getElem_computePrefix s i hip
  rw [letter_at s i hi, getElem_prefixWord _ i hip]
  split
  · rename_i h
    rw [ite_eq_right (by omega), ← letter_at s _ (by omega), htab]
  · rename_i h
    rw [ite_eq_left (by omega)]

private theorem longest_border (s : Array α) (i : ℕ) (hi : i < s.size) :
    KMP.IsProperBorderLen (s.toList.take (i + 1)) (KMP.borderLen s.toList (i + 1)) :=
  KMP.isProperBorderLen_maxBorderLen (by simp only [List.length_take, Array.length_toList]; omega)

-- A positive border ends with the same representative as the prefix it matches. Strictly
-- shorter borders are borders of the longest one, whose endpoint is earlier in the word.
private theorem letter_of_border (s : Array α) {i j : ℕ} (hi : i < s.size)
    (hb : KMP.IsProperBorderLen (s.toList.take (i + 1)) (j + 1)) : letter s i = letter s j := by
  induction i using Nat.strong_induction_on generalizing j with
  | ind i ih =>
    have hm := longest_border s i hi
    have hle := KMP.le_maxBorderLen_of_isProperBorderLen hb
    change j + 1 ≤ KMP.borderLen s.toList (i + 1) at hle
    generalize heq : KMP.borderLen s.toList (i + 1) = b at hm hle
    cases b with
    | zero => omega
    | succ m =>
      have hmi := hm.1
      simp only [List.length_take, Array.length_toList] at hmi
      rw [letter_step s i hi, heq, ite_eq_right (by omega), Nat.add_one_sub_one]
      rcases Nat.eq_or_lt_of_le hle with h | h
      · congr 1; omega
      · have hsmall := hb.to_take hm h
        rw [List.take_take, Nat.min_eq_left (by omega)] at hsmall
        exact ih m (by omega) (by omega) hsmall

-- Reading the original word at a representative recovers the letter at the original position.
private theorem decode_letter (s : Array α) (i : ℕ) (hi : i < s.size) :
    s[letter s i]? = s[i]? := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    have hm := longest_border s i hi
    generalize heq : KMP.borderLen s.toList (i + 1) = b at hm
    rw [letter_step s i hi, heq]
    cases b with
    | zero => rfl
    | succ m =>
      have hmi := hm.1
      simp only [List.length_take, Array.length_toList] at hmi
      simp only [Nat.succ_ne_zero, ↓reduceIte, Nat.add_one_sub_one]
      rw [ih m (by omega) (by omega), Array.getElem?_eq_getElem (by omega),
        Array.getElem?_eq_getElem hi]
      have h := (border_iff_letters s (by omega) (by omega)).mp hm m (by omega)
      have hend : i + 1 - (m + 1) + m = i := by omega
      simpa only [hend] using congrArg some h

private theorem representative_match (s : Array α) {t k : ℕ} (ht : 0 < t)
    (hlen : t + k ≤ s.size) (hs : k ≤ List.lcpLen s.toList (s.toList.drop t)) :
    ∀ j < k, letter s j = letter s (t + j) := by
  have hmatch := (le_lcpLen_iff_letters s hlen).mp hs
  intro j hj
  apply (letter_of_border s (by omega) ?_).symm
  apply (border_iff_letters s (by omega) (by omega)).mpr
  intro a ha
  have heq : t + j + 1 - (j + 1) = t := by omega
  simpa only [heq] using hmatch a (by omega)

/-- Conversion from the KMP table recovers the Z-array for every input word, including the
empty word. -/
theorem fromPrefix_computePrefix (s : Array α) :
    fromPrefix (KMP.computePrefix s) = zArray s := by
  let w := prefixWord (KMP.computePrefix s)
  have hsize : w.size = s.size := by simp [w]
  change zArray w = zArray s
  apply Array.ext (by simp [hsize])
  intro t ht _
  rw [getElem_zArray w, getElem_zArray s]
  by_cases ht0 : t = 0
  · simp [ht0, hsize]
  have ht' : t < s.size := by simpa [hsize] using ht
  apply le_antisymm
  · let k := List.lcpLen w.toList (w.toList.drop t)
    have h := List.lcpLen_le_length_right w.toList (w.toList.drop t)
    change k ≤ _ at h
    simp only [List.length_drop, Array.length_toList, hsize] at h
    have hlen : t + k ≤ s.size := by omega
    have hmatch := (le_lcpLen_iff_letters w (hsize ▸ hlen)).mp (le_refl k)
    apply (le_lcpLen_iff_letters s hlen).mpr
    intro j hj
    have heq : letter s j = letter s (t + j) := by
      rw [letter_at s j (by omega), letter_at s (t + j) (by omega)]
      exact hmatch j hj
    have hletters := (decode_letter s j (by omega)).symm.trans
      ((congrArg (fun a => s[a]?) heq).trans (decode_letter s (t + j) (by omega)))
    simpa only [Array.getElem?_eq_getElem (show j < s.size by omega),
      Array.getElem?_eq_getElem (show t + j < s.size by omega), Option.some.injEq] using hletters
  · let k := List.lcpLen s.toList (s.toList.drop t)
    have h := List.lcpLen_le_length_right s.toList (s.toList.drop t)
    change k ≤ _ at h
    simp only [List.length_drop, Array.length_toList] at h
    have hlen : t + k ≤ s.size := by omega
    apply (le_lcpLen_iff_letters w (hsize ▸ hlen)).mpr
    intro j hj
    have heq := representative_match s (by omega) hlen (le_refl k) j hj
    simpa only [letter_at s j (by omega), letter_at s (t + j) (by omega)] using heq

end Cslib.Algorithms.Lean.ZFunction
