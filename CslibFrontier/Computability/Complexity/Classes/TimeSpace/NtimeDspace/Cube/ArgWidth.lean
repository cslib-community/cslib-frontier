/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.EntryTerm3

/-!
# The widths of argument codes, from the potential

An argument code of node `u` of a clique holds one label code for every other node `u'`, of width
`w(a_{uu'})` with `w(a)² ≤ 900 a` (`codeWidth_sq_le`). By the Cauchy–Schwarz inequality the total
width is at most `√(900 q Σ_{u'} a_{uu'}) ≤ √(900 q Σ_p a_p)`, and along a valid path
`q (q - 1)² Σ_p a_p · 2^{|chs|} ≤ q Φ₀`. Since `q = 2^{2^{e - |chs|}}`, this gives
`w(args)² · 2^e ≤ 3600 Φ₀` at every clique of a valid path (`argWidth_sq_mul_le`), which is
`O(s² / log s)` for the setup of size `s`. The uniform bound `q₀ (fw + B) < L` of
`SizeOK.of_lt` charges `q₀` widths of size `B` to one argument code, which is too much when
`q₀ ≈ s^{1/3}` and `B ≈ s / √log s`; `SizeOK.of_potential` uses the bound above instead.

## Main results

* `Clique.row_le_spair`: the budgets at one node add up to at most the total budget.
* `Clique.argWidth_sq_le`: `w(args)² ≤ 900 q Σ_p a_p`.
* `Num.argWidth_sq_mul_le`: `w(args)² · 2^e ≤ 3600 Φ₀` along a valid path, for `2K = 2^(2^e)`.
* `Num.SizeOK.of_potential`: the size conditions from `q₀² fw ≤ L` and `3600 Φ₀ < L² · 2^e`.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset

namespace Clique

/-- **The budgets at one node** add up to at most the total budget. -/
theorem row_le_spair (C : Clique) (u : Fin C.q) :
    ∑ u' ∈ univ.filter (· ≠ u), budget C.a u u' ≤ C.spair := by
  classical
  have hsp : C.spair = ∑ p ∈ univ.filter (fun p : Fin C.q × Fin C.q => p.1 < p.2), C.a p.1 p.2 :=
    (Finset.sum_subtype _ (fun p => by simp) (fun p : Fin C.q × Fin C.q => C.a p.1 p.2)).symm
  rw [hsp]
  refine Finset.sum_le_sum_of_injOn (fun u' => (min u u', max u u')) ?_ ?_ (fun _ _ => le_rfl)
    (fun _ _ _ => Nat.zero_le _)
  · intro a ha b hb hab
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
    simp only [Prod.mk.injEq] at hab
    have ha' : a.val ≠ u.val := fun h => ha (Fin.ext h)
    have hb' : b.val ≠ u.val := fun h => hb (Fin.ext h)
    have h1 := congrArg Fin.val hab.1
    have h2 := congrArg Fin.val hab.2
    simp only [Fin.val_min, Fin.val_max] at h1 h2
    exact Fin.ext (by omega)
  · intro p hp
    simp only [mem_image, mem_filter, mem_univ, true_and] at hp ⊢
    obtain ⟨u', hu', rfl⟩ := hp
    rw [Fin.lt_def]
    have : u'.val ≠ u.val := fun h => hu' (Fin.ext h)
    simp only [Fin.val_min, Fin.val_max]
    omega

/-- **The width of an argument code**: `w(args)² ≤ 900 q Σ_p a_p`, by the Cauchy–Schwarz
inequality and `w(a)² ≤ 900 a`. -/
theorem argWidth_sq_le (C : Clique) (u : ℕ) : argWidth C u ^ 2 ≤ 900 * C.q * C.spair := by
  classical
  unfold argWidth argOffset
  set F : ℕ → ℕ := fun u' => if h : u' < C.q ∧ u < C.q then
    (if u' = u then 0 else codeWidth (budget C.a ⟨u, h.2⟩ ⟨u', h.1⟩)) else 0 with hF
  set G : ℕ → ℕ := fun u' => if h : u' < C.q ∧ u < C.q then
    (if u' = u then 0 else budget C.a ⟨u, h.2⟩ ⟨u', h.1⟩) else 0 with hG
  have h1 : (∑ u' ∈ range C.q, F u') ^ 2 ≤ C.q * ∑ u' ∈ range C.q, F u' ^ 2 := by
    have := sq_sum_le_card_mul_sum_sq (s := range C.q) (f := F)
    rwa [card_range] at this
  have h2 : ∑ u' ∈ range C.q, F u' ^ 2 ≤ 900 * ∑ u' ∈ range C.q, G u' := by
    rw [mul_sum]
    refine sum_le_sum fun u' _ => ?_
    simp only [hF, hG]
    by_cases hc : u' < C.q ∧ u < C.q
    · rw [dite_eq_left hc, dite_eq_left hc]
      by_cases he : u' = u
      · rw [ite_eq_left he, ite_eq_left he]; simp
      · rw [ite_eq_right he, ite_eq_right he]; exact codeWidth_sq_le _
    · rw [dite_eq_right hc, dite_eq_right hc]; simp
  have h3 : ∑ u' ∈ range C.q, G u' ≤ C.spair := by
    by_cases hu : u < C.q
    · have e1 : ∑ u' ∈ range C.q, G u' = ∑ u' ∈ univ.filter (· ≠ (⟨u, hu⟩ : Fin C.q)),
          budget C.a ⟨u, hu⟩ u' := by
        rw [Finset.sum_range, Finset.sum_filter]
        refine sum_congr rfl fun i _ => ?_
        simp only [hG]
        rw [dite_eq_left ⟨i.2, hu⟩]
        by_cases he : (i : ℕ) = u
        · rw [ite_eq_left he, ite_eq_right (fun h => h (Fin.ext he))]
        · rw [ite_eq_right he, ite_eq_left (fun h => he (congrArg Fin.val h))]
      rw [e1]
      exact row_le_spair C ⟨u, hu⟩
    · have : ∀ u' ∈ range C.q, G u' = 0 := fun u' _ => by
        simp only [hG]; rw [dite_eq_right (fun h => hu h.2)]
      rw [sum_eq_zero this]
      exact Nat.zero_le _
  calc (∑ u' ∈ range C.q, F u') ^ 2 ≤ C.q * ∑ u' ∈ range C.q, F u' ^ 2 := h1
    _ ≤ C.q * (900 * C.spair) := Nat.mul_le_mul_left _ (h2.trans (Nat.mul_le_mul_left _ h3))
    _ = 900 * C.q * C.spair := by ring

end Clique

namespace Num

open SumProduct

/-- **The width of an argument code along a valid path**: `w(args)² · 2^e ≤ 3600 Φ₀`, for
`2K = 2^(2^e)`. -/
theorem argWidth_sq_mul_le (S : Setup) {e : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e) {chs : List ℕ}
    (hp : S.PathOK chs) (u : ℕ) :
    argWidth (S.clique chs) u ^ 2 * 2 ^ e ≤ 3600 * S.C₀.potential := by
  obtain ⟨hk, hq, hpot⟩ := S.chainOK_facts (e := e) he (S.pathOK_chainOK he chs hp)
  have hw := (S.clique chs).argWidth_sq_le u
  rw [Clique.potential_eq, hq] at hpot
  rw [hq] at hw
  generalize (S.clique chs).spair = A at hw hpot
  generalize argWidth (S.clique chs) u = W at hw
  obtain ⟨x, hx⟩ : ∃ x, e = x + chs.length := ⟨e - chs.length, by omega⟩
  rw [hx, Nat.add_sub_cancel] at hpot hw
  rw [hx, pow_add]
  generalize hQ : 2 ^ 2 ^ x = Q at hw hpot
  generalize 2 ^ chs.length = Y at hpot ⊢
  have hxQ : 2 ^ x ≤ Q := hQ ▸ Nat.pow_le_pow_right (by norm_num) Nat.lt_two_pow_self.le
  have hQ2 : 2 ≤ Q := hQ ▸ (Nat.le_self_pow (Nat.two_pow_pos x).ne' 2)
  obtain ⟨r, rfl⟩ : ∃ r, Q = r + 1 := ⟨Q - 1, by omega⟩
  rw [Nat.add_sub_cancel] at hpot
  have hr : (r + 1) * (r + 1) ≤ 4 * r ^ 2 := by nlinarith
  calc W ^ 2 * (2 ^ x * Y) ≤ 900 * (r + 1) * A * (2 ^ x * Y) := Nat.mul_le_mul_right _ hw
    _ ≤ 900 * (r + 1) * A * ((r + 1) * Y) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hxQ)
    _ = 900 * ((r + 1) * (r + 1)) * A * Y := by ring
    _ ≤ 900 * (4 * r ^ 2) * A * Y :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hr))
    _ = 3600 * (r ^ 2 * A * Y) := by ring
    _ ≤ 3600 * S.C₀.potential := Nat.mul_le_mul_left _ hpot

/-- **The size conditions from the potential**: `q₀² fw ≤ L` and `3600 Φ₀ < L² · 2^e`, for a good
setup with `2K = 2^(2^e)`. -/
theorem SizeOK.of_potential {S : Setup} (hS : S.Good) {e L : ℕ} (he : 2 * S.K = 2 ^ 2 ^ e)
    (hArr : 2 * S.K * (2 * S.K) * S.fw ≤ L) (harg : 3600 * S.C₀.potential < L ^ 2 * 2 ^ e) :
    SizeOK S L where
  arr chs hp := by
    have h1 := q_le_first S chs hp
    have h2 : S.C₀.q = 2 * S.K := rfl
    have h3 : 1 ≤ S.K := hS.1
    calc (S.clique chs).q * S.fw ≤ 2 * S.K * S.fw := Nat.mul_le_mul_right _ (h2 ▸ h1)
      _ ≤ 2 * S.K * (2 * S.K) * S.fw := by
          rw [mul_assoc (2 * S.K)]; exact Nat.le_mul_of_pos_left _ (by omega)
      _ ≤ L := hArr
  arg chs hp u := by
    rw [argWidN_eq _ (fits_path S hS hp)]
    have h := (argWidth_sq_mul_le S he hp u).trans_lt harg
    have h' : argWidth (S.clique chs) u ^ 2 < L ^ 2 :=
      Nat.lt_of_mul_lt_mul_right h
    exact lt_of_pow_lt_pow_left₀ 2 (Nat.zero_le _) h'

end Num

end Cslib.Complexity.NtimeDspace.Cube
