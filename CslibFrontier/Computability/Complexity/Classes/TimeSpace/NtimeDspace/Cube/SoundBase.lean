/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.TimeSpace.NtimeDspace.Cube.SoundCopies

/-!
# The two ends of the formula

* `Setup.ent0`: an entry of the first clique is the product of its leaf factors.
* `value_two`: the value of a clique with two nodes is a sum over the codes of its one label.
-/

public section

namespace Cslib.Complexity.NtimeDspace.Cube

open Finset MergeProof

/-- **An entry of the first clique** is the product of its factors. -/
theorem Setup.ent0 (S : Setup) (v args : ℕ) (hv : v < 2 * S.K) :
    cEntry S.C₀ v args = ∏ f ∈ range (S.nFac0 v), S.factor0 v args f := by
  have hq : v < S.C₀.q := hv
  have hΘ : ∀ u : Fin (2 * S.K), (if h : v < S.C₀.q then decodeArgs S.C₀ ⟨v, h⟩ args
      ⟨u.val, by simp [Setup.C₀, firstClique]⟩ else (0, 0)) = decodeArgs S.C₀ ⟨v, hq⟩ args u := by
    intro u; rw [dif_pos hq]; rfl
  unfold cEntry
  rw [dif_pos hq]
  unfold Setup.nFac0
  rw [prod_range_add, prod_range_one]
  by_cases hK : v < S.K
  · rw [if_pos hK]
    show (if v < S.K then vTable S.G S.K v _ else tTable S.G S.K (v - S.K) _) = _
    rw [if_pos hK, ← Fin.prod_univ_eq_prod_range]
    simp only [Setup.factor0, hΘ, if_pos hK, if_true]
    unfold vTable
    have e : ∀ x : Fin S.V, (if h : 1 + (x : ℕ) - 1 < S.V then
        (if vgroup S.G S.K ⟨1 + (x : ℕ) - 1, h⟩ = v then
          S.G.eval ⟨1 + (x : ℕ) - 1, h⟩ ((S.G.ports ⟨1 + (x : ℕ) - 1, h⟩).map fun e =>
            heBit S.G S.K (labelOfNode S.K (decodeArgs S.C₀ ⟨v, hq⟩ args) (S.K + tgroup S.G S.K e))
                v
              (tgroup S.G S.K e) (e, decide (S.G.w e = ⟨1 + (x : ℕ) - 1, h⟩))) else 1) else 1) =
        if vgroup S.G S.K x = v then
          S.G.eval x ((S.G.ports x).map fun e =>
            heBit S.G S.K (labelOfNode S.K (decodeArgs S.C₀ ⟨v, hq⟩ args) (S.K + tgroup S.G S.K e))
                v
              (tgroup S.G S.K e) (e, decide (S.G.w e = x))) else 1 := by
      intro x
      have hx : (⟨1 + (x : ℕ) - 1, by omega⟩ : Fin S.V) = x := Fin.ext (by simp)
      rw [dif_pos (by omega), hx]
    have e1 : ∀ x : Fin S.V, (1 + (x : ℕ) = 0) =
        False := fun x => by simp only [eq_iff_iff, iff_false]; omega
    simp only [e1, if_false, e]
    split_ifs <;> simp
  · rw [if_neg hK]
    show (if v < S.K then vTable S.G S.K v _ else tTable S.G S.K (v - S.K) _) = _
    rw [if_neg hK, ← Fin.prod_univ_eq_prod_range]
    simp only [Setup.factor0, hΘ, if_neg hK, if_true]
    unfold tTable
    have e : ∀ x : Fin S.G.M, (if h : 1 + (x : ℕ) - 1 < S.G.M then
        (if tgroup S.G S.K ⟨1 + (x : ℕ) - 1, h⟩ = v - S.K then
          (if heBit S.G S.K (labelOfNode S.K (decodeArgs S.C₀ ⟨v, hq⟩ args)
                (vgroup S.G S.K (S.G.u ⟨1 + (x : ℕ) - 1, h⟩)))
                    (vgroup S.G S.K (S.G.u ⟨1 + (x : ℕ) - 1, h⟩))
                (v - S.K) (⟨1 + (x : ℕ) - 1, h⟩, false) =
              heBit S.G S.K (labelOfNode S.K (decodeArgs S.C₀ ⟨v, hq⟩ args)
                (vgroup S.G S.K (S.G.w ⟨1 + (x : ℕ) - 1, h⟩)))
                    (vgroup S.G S.K (S.G.w ⟨1 + (x : ℕ) - 1, h⟩))
                (v - S.K) (⟨1 + (x : ℕ) - 1, h⟩, true) then 1 else 0) else 1) else 1) =
        if tgroup S.G S.K x = v - S.K then
          (if heBit S.G S.K (labelOfNode S.K (decodeArgs S.C₀ ⟨v, hq⟩ args)
              (vgroup S.G S.K (S.G.u x)))
                (vgroup S.G S.K (S.G.u x)) (v - S.K) (x, false) =
              heBit S.G S.K (labelOfNode S.K (decodeArgs S.C₀ ⟨v, hq⟩ args)
                  (vgroup S.G S.K (S.G.w x)))
                (vgroup S.G S.K (S.G.w x)) (v - S.K) (x, true) then 1 else 0) else 1 := by
      intro x
      have hx : (⟨1 + (x : ℕ) - 1, by omega⟩ : Fin S.G.M) = x := Fin.ext (by simp)
      rw [dif_pos (by omega), hx]
    have e1 : ∀ x : Fin S.G.M, (1 + (x : ℕ) = 0) = False := fun x => by
      simp only [eq_iff_iff, iff_false]; omega
    simp only [e1, if_false, e]
    split_ifs <;> simp

/-! ### Two nodes -/

theorem sum_codes_elim {M : Type*} [AddCommMonoid M] (a : ℕ) (f : Label → M) :
    (∑ i ∈ range (2 ^ codeWidth a), (decodeLabel a i).elim
        0 fun l => if labelWt l = a then f l else 0) =
      ∑ l ∈ labelsEq a, f l := by
  rw [← sum_codes]
  refine sum_congr rfl fun i _ => ?_
  cases decodeLabel a i <;> rfl

theorem pairs_two_eq (p : Pairs 2) : p = ⟨((0 : Fin 2), (1 : Fin 2)), by decide⟩ := by
  obtain ⟨⟨u, v⟩, h⟩ := p
  have h' : u.val < v.val := h
  have hu : u = 0 := Fin.ext (by have := v.isLt; simp; omega)
  have hv : v = 1 := Fin.ext (by have := v.isLt; simp; omega)
  subst hu hv; rfl

theorem value_two' (a : Fin 2 → Fin 2 → ℕ) (T : Fin 2 → (Fin 2 → Label) → ℤ) :
    (⟨2, a, T⟩ : Clique).value = ∑ i ∈ range (2 ^ codeWidth (a 0 1)),
      match decodeLabel (a 0 1) i with
      | some l => if labelWt l = a 0 1 then
          cEntry ⟨2, a, T⟩ 0 i * cEntry ⟨2, a, T⟩ 1 i else 0
      | none => 0 := by
  classical
  let lab0 : Label → Fin 2 → Label := fun l u => if u = 0 then (0, 0) else l
  let lab1 : Label → Fin 2 → Label := fun l u => if u = 1 then (0, 0) else l
  have hent : ∀ i l, i < 2 ^ codeWidth (a 0 1) → decodeLabel (a 0 1) i = some l →
      cEntry ⟨2, a, T⟩ 0 i * cEntry ⟨2, a, T⟩ 1 i = T 0 (lab0 l) * T 1 (lab1 l) := by
    intro i l hi hl
    have hb : budget a 0 1 = a 0 1 := budget_of_lt a (by decide)
    have hb' : budget a 1 0 = a 0 1 := by rw [budget_comm]; exact hb
    have ho : argOffset ⟨2, a, T⟩ ((0 : Fin 2) : ℕ) ((1 : Fin 2) : ℕ) = 0 := by simp [argOffset]
    have ho' : argOffset ⟨2, a, T⟩ ((1 : Fin 2) : ℕ) ((0 : Fin 2) : ℕ) = 0 := by simp [argOffset]
    have hf : fieldOf ⟨2, a, T⟩ 0 1 i = i := by
      unfold fieldOf
      rw [ho, hb, pow_zero, Nat.div_one, Nat.mod_eq_of_lt hi]
    have hf' : fieldOf ⟨2, a, T⟩ 1 0 i = i := by
      unfold fieldOf
      rw [ho', hb', pow_zero, Nat.div_one, Nat.mod_eq_of_lt hi]
    have h0 : decodeArgs ⟨2, a, T⟩ 0 i = lab0 l := by
      funext u
      rw [decodeArgs_eq]
      by_cases hu : u = 0
      · rw [if_pos hu]; simp [lab0, hu]
      · have hu1 : u = 1 := by fin_cases u <;> simp_all
        subst hu1
        rw [if_neg (by simp), hf, hb, hl]
        simp [lab0]
    have h1 : decodeArgs ⟨2, a, T⟩ 1 i = lab1 l := by
      funext u
      rw [decodeArgs_eq]
      by_cases hu : u = 1
      · rw [if_pos hu]; simp [lab1, hu]
      · have hu0 : u = 0 := by fin_cases u <;> simp_all
        subst hu0
        rw [if_neg (by simp), hf', hb', hl]
        simp [lab1]
    unfold cEntry
    rw [dif_pos (show 0 < 2 by decide), dif_pos (show 1 < 2 by decide)]
    exact congrArg₂ _ (congrArg (T 0) h0) (congrArg (T 1) h1)
  have hR : (∑ i ∈ range (2 ^ codeWidth (a 0 1)),
      match decodeLabel (a 0 1) i with
      | some l => if labelWt l = a 0 1 then
          cEntry ⟨2, a, T⟩ 0 i * cEntry ⟨2, a, T⟩ 1 i else 0
      | none => 0) = ∑ i ∈ range (2 ^ codeWidth (a 0 1)),
      (decodeLabel (a 0 1) i).elim
          0 fun l => if labelWt l = a 0 1 then T 0 (lab0 l) * T 1 (lab1 l) else 0 := by
    refine sum_congr rfl fun i hi => ?_
    rcases hd : decodeLabel (a 0 1) i with _ | l
    · rfl
    · simp only [Option.elim]
      rw [hent i l (mem_range.mp hi) hd]
  rw [hR, sum_codes_elim]
  unfold Clique.value Clique.labelings
  refine Finset.sum_nbij' (fun θ => θ ⟨((0 : Fin 2), (1 : Fin 2)), by simp⟩) (fun l _ => l) ?_ ?_ ?_
      ?_ ?_
  · intro θ hθ
    have := Fintype.mem_piFinset.mp hθ ⟨((0 : Fin 2), (1 : Fin 2)), by simp⟩
    exact this
  · intro l hl
    refine Fintype.mem_piFinset.mpr fun p => ?_
    rw [pairs_two_eq p]
    exact hl
  · intro θ _
    funext p
    rw [pairs_two_eq p]
  · intro l _; rfl
  · intro θ _
    rw [Fin.prod_univ_two]
    congr 2
    · funext u
      fin_cases u
      · simp [Clique.labelAt, lab0]
      · simp [Clique.labelAt, lab0]
    · funext u
      fin_cases u
      · simp [Clique.labelAt, lab1]
      · simp [Clique.labelAt, lab1]

/-- **The value of a clique with two nodes.** -/
theorem value_two (C : Clique) (hq : C.q = 2) :
    C.value = ∑ i ∈ range (2 ^ codeWidth (C.a ⟨0, by omega⟩ ⟨1, by omega⟩)),
      match decodeLabel (C.a ⟨0, by omega⟩ ⟨1, by omega⟩) i with
      | some
          l => if labelWt l = C.a ⟨0, by omega⟩ ⟨1, by omega⟩ then cEntry C 0 i * cEntry C 1 i else 0
      | none => 0 := by
  obtain ⟨q, a, T⟩ := C
  simp only at hq
  subst hq
  exact value_two' a T

end Cslib.Complexity.NtimeDspace.Cube
