/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.RewriteOccurrence

/-!
# Local behavior of the complete source readout

Pair coordinates determine their corresponding source letters. Changing a special symbol
preserves the readout; changing the two coordinates of a pair can be split through a legal
mixed pair. These facts apply to arbitrary legal intermediate words.

## Main results

* `HWord.RewriteGadget.readout_eq_of_special`: changing a non-pair symbol preserves all letters.
* `HWord.RewriteGadget.mixed_pair_legal`: separate the two coordinates of a pair update.
-/

public section

namespace Cslib.Complexity.NCL.HWord.RewriteGadget

variable {n q r : ℕ} (rules : Fin r → Rule q)
  {u v : Fin (n + 3) → Fin (Fintype.card (Symbol q r))}

/-- A pair's second coordinate is the source letter shared with the next position. -/
theorem readout_pair_right (hu : HWord.Legal (compatibility rules) u) (i : Fin n)
    (a b : Option (Fin q))
    (hp : code.symm (u ⟨i.val + 1, by omega⟩) = .pair a b) :
    b = some (readout rules u hu i) := by
  have h := readout_spec rules u hu i
  simpa only [decode, hp, read] using h

private theorem read_right {a b : Option (Fin q)} {p : Symbol q r} {x : Fin q}
    (hp : Compatible rules p (.pair a b)) (hx : read p (.pair a b) = some x) :
    a = some x := by
  cases p with
  | start => exact hx
  | finish => exact False.elim hp
  | marker i => exact hx
  | pair c d =>
    obtain ⟨y, hd, ha⟩ := hp
    exact ha.trans (hd.symm.trans hx)

/-- A pair's first coordinate is the source letter shared with the preceding position. -/
theorem readout_pair_left (hu : HWord.Legal (compatibility rules) u) (i : Fin n)
    (a b : Option (Fin q))
    (hp : code.symm (u ⟨i.val + 2, by omega⟩) = .pair a b) :
    a = some (readout rules u hu i) := by
  have he := edge_view rules hu ⟨i.val + 1, by omega⟩ ⟨i.val + 2, by omega⟩ rfl
  have h := readout_spec rules u hu i
  rw [hp] at he
  simp only [decode, hp] at h
  exact read_right rules he h

private theorem readout_eq_of_views (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (i : Fin n)
    (hleft : code.symm (u ⟨i.val + 1, by omega⟩) = code.symm (v ⟨i.val + 1, by omega⟩))
    (hright : code.symm (u ⟨i.val + 2, by omega⟩) = code.symm (v ⟨i.val + 2, by omega⟩)) :
    readout rules u hu i = readout rules v hv i := by
  have h := readout_spec rules u hu i
  have h' := readout_spec rules v hv i
  simp only [decode, hleft, hright] at h
  exact Option.some.inj (h.symm.trans h')

private theorem readout_eq_of_eq_off (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (i : Fin n)
    (h1 : (⟨i.val + 1, by omega⟩ : Fin (n + 3)) = k →
      readout rules u hu i = readout rules v hv i)
    (h2 : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) = k →
      readout rules u hu i = readout rules v hv i) :
    readout rules u hu i = readout rules v hv i := by
  by_cases hk1 : (⟨i.val + 1, by omega⟩ : Fin (n + 3)) = k
  · exact h1 hk1
  · by_cases hk2 : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) = k
    · exact h2 hk2
    · exact readout_eq_of_views rules hu hv i (congrArg code.symm (he _ hk1))
        (congrArg code.symm (he _ hk2))

/-- Changing only a pair's first coordinate can affect only the source letter on its left. -/
theorem readout_first_off (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a a' b : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a' b)
    (i : Fin n) (hi : i.val + 2 ≠ k.val) :
    readout rules u hu i = readout rules v hv i :=
  readout_eq_of_eq_off rules hu hv k he i
    (fun hk => Option.some.inj
      ((readout_pair_right rules hu i a b (hk ▸ hpu)).symm.trans
        (readout_pair_right rules hv i a' b (hk ▸ hpv))))
    (fun hk => absurd (congrArg Fin.val hk) hi)

/-- Changing only a pair's second coordinate can affect only the source letter on its right. -/
theorem readout_second_off (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a b b' : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a b')
    (i : Fin n) (hi : i.val + 1 ≠ k.val) :
    readout rules u hu i = readout rules v hv i :=
  readout_eq_of_eq_off rules hu hv k he i
    (fun hk => absurd (congrArg Fin.val hk) hi)
    (fun hk => Option.some.inj
      ((readout_pair_left rules hu i a b (hk ▸ hpu)).symm.trans
        (readout_pair_left rules hv i a b' (hk ▸ hpv))))

private theorem special_after {p q' : Symbol q r}
    (hp : ∀ a b, p ≠ .pair a b) (h : Compatible rules p q') :
    ∃ a b, q' = .pair a b := by
  cases p <;> cases q' <;> simp_all [Compatible]

private theorem special_before {p q' : Symbol q r}
    (hp : ∀ a b, p ≠ .pair a b) (h : Compatible rules q' p) :
    ∃ a b, q' = .pair a b := by
  cases p <;> cases q' <;> simp_all [Compatible]

/-- A legal change of a special symbol leaves the complete decoded source word unchanged. -/
theorem readout_eq_of_special (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j)
    (hspecial : ∀ a b, code.symm (u k) ≠ .pair a b) :
    readout rules u hu = readout rules v hv := by
  funext i
  refine readout_eq_of_eq_off rules hu hv k he i (fun h1 => ?_) (fun h2 => ?_)
  · have hne : (⟨i.val + 2, by omega⟩ : Fin (n + 3)) ≠ k :=
      fun h => by have := congrArg Fin.val (h1.trans h.symm); dsimp at this; omega
    have hedge := h1 ▸ edge_view rules hu ⟨i.val + 1, by omega⟩ ⟨i.val + 2, by omega⟩ rfl
    obtain ⟨a, b, hp⟩ := special_after rules hspecial hedge
    exact Option.some.inj ((readout_pair_left rules hu i a b hp).symm.trans
      (readout_pair_left rules hv i a b (he _ hne ▸ hp)))
  · have hne : (⟨i.val + 1, by omega⟩ : Fin (n + 3)) ≠ k :=
      fun h => by have := congrArg Fin.val (h2.trans h.symm); dsimp at this; omega
    have hedge := h2 ▸ edge_view rules hu ⟨i.val + 1, by omega⟩ ⟨i.val + 2, by omega⟩ rfl
    obtain ⟨a, b, hp⟩ := special_before rules hspecial hedge
    exact Option.some.inj ((readout_pair_right rules hu i a b hp).symm.trans
      (readout_pair_right rules hv i a b (he _ hne ▸ hp)))

private theorem incoming_mix {p : Symbol q r} {a a' b b' : Option (Fin q)}
    (h : Compatible rules p (.pair a b)) (h' : Compatible rules p (.pair a' b')) :
    Compatible rules p (.pair a' b) := by
  cases p <;> simp_all [Compatible]

private theorem outgoing_mix {p : Symbol q r} {a a' b b' : Option (Fin q)}
    (h : Compatible rules (.pair a b) p) (h' : Compatible rules (.pair a' b') p) :
    Compatible rules (.pair a' b) p := by
  cases p <;> simp_all [Compatible]

/-- The mixed pair separates a simultaneous two-coordinate update into legal local updates. -/
theorem mixed_pair_legal (hu : HWord.Legal (compatibility rules) u)
    (hv : HWord.Legal (compatibility rules) v) (k : Fin (n + 3))
    (he : ∀ j, j ≠ k → u j = v j) (a a' b b' : Option (Fin q))
    (hpu : code.symm (u k) = .pair a b) (hpv : code.symm (v k) = .pair a' b') :
    HWord.Legal (compatibility rules) (Function.update u k (code (.pair a' b))) := by
  intro i j hij
  by_cases hi : i = k
  · subst k
    have hj : j ≠ i := Fin.ne_of_val_ne (by omega)
    have hs := hpu ▸ edge_view rules hu i j hij
    have ht := he j hj ▸ (hpv ▸ edge_view rules hv i j hij)
    simpa only [Function.update_self, Function.update_of_ne hj, Equiv.apply_symm_apply] using
      (compatibility_adj rules _ _).mpr (outgoing_mix rules hs ht)
  · by_cases hj : j = k
    · subst k
      have hs := hpu ▸ edge_view rules hu i j hij
      have ht := he i hi ▸ (hpv ▸ edge_view rules hv i j hij)
      simpa only [Function.update_self, Function.update_of_ne hi, Equiv.apply_symm_apply] using
        (compatibility_adj rules _ _).mpr (incoming_mix rules hs ht)
    · simpa only [Function.update_of_ne hi, Function.update_of_ne hj] using hu i j hij

end Cslib.Complexity.NCL.HWord.RewriteGadget
