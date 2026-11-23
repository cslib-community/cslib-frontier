/-
Copyright (c) 2026 Anton Kovsharov, Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov, Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Mathlib.Data.List.GetD

/-!
# Native tests of pairwise list relations

An efficiently decidable relation gives an efficiently decidable pairwise property of a framed
list. The machine checks all pairs of positions in increasing order, so it also works for
asymmetric relations and does not require transitivity. This shares the indexed-list test used
by canonical sparse polynomials and ordered port certificates.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.pairwise`: a native polynomial-time pairwise test.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Test a relation on every pair of positions in increasing order in a framed list. The bound is
polynomial in its complete encoding, including the encoded sizes of its elements. -/
theorem pairwise {α : Type} (enc : α ↪ List Bool) (r : α → α → Prop) [DecidableRel r]
    (hr : ComputableInPolyTime (fun p : α × α => decide (r p.1 p.2))
      (encPair enc enc) encBool) :
    ComputableInPolyTime (fun l : List α => decide (l.Pairwise r)) (encList enc) encBool := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    let encL := encList enc
    let encP := encPair encL encUnary
    have hget := listGetD (encA := enc) (encL := encL) fallback
    have hlist := (fst encP encUnary).fst'
    have hleft := hget.comp (hlist.prod (snd encP encUnary))
    have hright := hget.comp (hlist.prod (fst encP encUnary).snd')
    have htest := hr.comp (hleft.prod hright)
    have hinner := range.comp (snd encL encUnary)
    have houter := range.comp (length_list enc)
    have hcheck := allWithEncoding (allWithEncoding htest id' hinner) id' houter
    apply hcheck.of_enc_eq
    intro l
    congr 1
    rw [Bool.eq_iff_iff, decide_eq_true_eq, List.pairwise_iff_getElem]
    simp only [Function.comp_apply, List.all_eq_true, List.mem_range, decide_eq_true_eq]
    symm
    refine ⟨fun h j i hj hi hji => ?_, fun h i hi j hji => ?_⟩
    · simpa only [List.getD_eq_getElem l fallback hj,
        List.getD_eq_getElem l fallback hi] using h i hi j hji
    · rw [List.getD_eq_getElem l fallback (lt_trans hji hi),
        List.getD_eq_getElem l fallback hi]
      exact h j i (lt_trans hji hi) hi hji

end Turing.MultiTapeTM.ComputableInPolyTime
