/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.CommonPrefix

/-!
# Extending a common prefix of two array suffixes

Kasai's LCP array construction and the Z-algorithm both resume comparisons after a prefix whose
length is already known. `Array.extendLcp` compares the remaining entries in place.
`Array.extendLcp_eq_add_lcpLen` specifies how much it adds, and `Array.extendLcp_eq_lcpLen`
recovers the full length when the skipped prefix is known to agree.
-/

public section

namespace Array

variable {α : Type*} [DecidableEq α]

/-- Starting with length `h`, compare entries at `i + h` and `j + h` and advance while they agree.
The first `h` entries of the two suffixes are skipped. -/
def extendLcp (w : Array α) (i j h : ℕ) : ℕ :=
  if hlt : i + h < w.size ∧ j + h < w.size then
    if w[i + h]'hlt.1 = w[j + h]'hlt.2 then
      extendLcp w i j (h + 1)
    else
      h
  else
    h
termination_by w.size - (j + h)

/-- The returned length is the starting length plus the common prefix of the unexamined suffixes. -/
theorem extendLcp_eq_add_lcpLen (w : Array α) (i j h : ℕ) :
    extendLcp w i j h = h + List.lcpLen (w.toList.drop (i + h)) (w.toList.drop (j + h)) := by
  fun_induction extendLcp w i j h with
  | case1 h hlt heq ih =>
    rw [ih, List.drop_eq_getElem_cons hlt.1, List.drop_eq_getElem_cons hlt.2,
      Array.getElem_toList, Array.getElem_toList, heq, List.lcpLen_cons_cons_self,
      ← Nat.add_assoc, ← Nat.add_assoc]
    omega
  | case2 h hlt hne =>
    rw [List.drop_eq_getElem_cons hlt.1, List.drop_eq_getElem_cons hlt.2,
      Array.getElem_toList, Array.getElem_toList, List.lcpLen_cons_cons, ite_eq_right hne,
      Nat.add_zero]
  | case3 h hlt =>
    have h1 := List.lcpLen_le_length_left (w.toList.drop (i + h)) (w.toList.drop (j + h))
    have h2 := List.lcpLen_le_length_right (w.toList.drop (i + h)) (w.toList.drop (j + h))
    simp only [List.length_drop, Array.length_toList] at h1 h2
    omega

/-- Given a known common prefix of length `h`, resuming the scan returns the full common-prefix
length of the suffixes at `i` and `j`. -/
theorem extendLcp_eq_lcpLen (w : Array α) (i j h : ℕ)
    (hh : h ≤ List.lcpLen (w.toList.drop i) (w.toList.drop j)) :
    w.extendLcp i j h = List.lcpLen (w.toList.drop i) (w.toList.drop j) := by
  rw [extendLcp_eq_add_lcpLen]
  simpa only [List.drop_drop] using (List.lcpLen_eq_add_lcpLen_drop hh).symm

end Array
