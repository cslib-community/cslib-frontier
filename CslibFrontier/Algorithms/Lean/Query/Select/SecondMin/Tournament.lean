/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.Query.Select.MinMax.Basic
public import CslibFrontier.Algorithms.Lean.Query.Select.SecondMin.Spec
public import Mathlib.Data.Nat.Log

/-!
# Second smallest by a balanced knockout tournament

Each comparison advances a winner and records the opponent it defeated. Every element except
the champion lies above some direct opponent of the champion. Finding the minimum among those
opponents therefore selects rank one, counting repetitions, even when the minimum occurs twice.

The knockout uses exactly `n - 1` comparisons and the champion plays at most `Nat.clog 2 n`
matches. With the final minimum scan, the algorithm uses at most `n + Nat.clog 2 n - 2`
comparisons under every oracle, including for unbalanced final levels. This is the construction
of [Schreier][Schreier1932], preliminary remark 2, equation (1), p. 156, with the order reversed
to select the second smallest. The correctness proof also covers total preorders with ties.
-/

public section

namespace Cslib.Query

variable {α : Type}

private structure Champion (α : Type) where
  winner : α
  opponents : List α

private def Champion.beats (a b : Champion α) : Champion α :=
  ⟨a.winner, b.winner :: a.opponents⟩

/-- Seed each half with one entrant, distribute the remaining entrants as evenly as possible,
then play the final between the two champions. -/
private def knockout (x : α) : (xs : List α) → FreeM (LEQuery α) (Champion α)
  | [] => return ⟨x, []⟩
  | y :: ys => do
    let a ← knockout x (ys.take (ys.length / 2))
    let b ← knockout y (ys.drop (ys.length / 2))
    return if ← LEQuery.ask a.winner b.winner then a.beats b else b.beats a
termination_by xs => xs.length
decreasing_by all_goals simp

/-- Return the second smallest entry, counting multiplicities, by scanning the opponents
directly defeated by the champion. Lists shorter than two have no second entry. -/
def findSecondMin : List α → FreeM (LEQuery α) (Option α)
  | [] | [_] => return none
  | x :: y :: ys => do
    let champion ← knockout x (y :: ys)
    findMin champion.opponents

private theorem knockout_cost (oracle : {ι : Type} → LEQuery α ι → ι) (x : α) (xs : List α) :
    (knockout x xs).countQueries oracle = xs.length ∧
      ((knockout x xs).eval oracle).opponents.length ≤ Nat.clog 2 (xs.length + 1) := by
  cases xs with
  | nil => simp [knockout]
  | cons y ys =>
    obtain ⟨ca, ha⟩ := knockout_cost oracle x (ys.take (ys.length / 2))
    obtain ⟨cb, hb⟩ := knockout_cost oracle y (ys.drop (ys.length / 2))
    have hsplit := Nat.clog_of_two_le (b := 2) (n := ys.length + 1 + 1) (by decide) (by omega)
    have hleft := Nat.clog_mono_right 2 (show (ys.take (ys.length / 2)).length + 1 ≤
        (ys.length + 1 + 1 + 2 - 1) / 2 by simp; omega)
    have hright := Nat.clog_mono_right 2 (show (ys.drop (ys.length / 2)).length + 1 ≤
        (ys.length + 1 + 1 + 2 - 1) / 2 by simp; omega)
    simp only [knockout, FreeM.countQueries_bind, FreeM.eval_bind, LEQuery.ask,
      FreeM.eval_lift, FreeM.countQueries_lift, FreeM.countQueries_pure, FreeM.eval_pure, ca, cb]
    constructor
    · simp only [List.length_take, List.length_drop, List.length_cons]
      omega
    · let a := (knockout x (ys.take (ys.length / 2))).eval oracle
      let b := (knockout y (ys.drop (ys.length / 2))).eval oracle
      change (if oracle (.le a.winner b.winner) then a.beats b else b.beats a).opponents.length ≤ _
      rcases Bool.eq_false_or_eq_true (oracle (.le a.winner b.winner)) with h | h <;>
        simp only [h, Bool.false_eq_true, ↓reduceIte, Champion.beats, List.length_cons, a, b] <;>
        omega
termination_by xs.length
decreasing_by all_goals simp

/-- The knockout tournament followed by a scan of its champion's direct opponents makes at most
`n + Nat.clog 2 n - 2` comparisons on lists of length at most `n`, against every oracle. -/
theorem findSecondMin_upperBound :
    UpperBound (findSecondMin (α := α)) List.length (fun n => n + Nat.clog 2 n - 2) := by
  apply UpperBound.of_pointwise
  · intro m n h
    exact Nat.sub_le_sub_right (Nat.add_le_add h (Nat.clog_mono_right 2 h)) 2
  · intro oracle xs
    cases xs with
    | nil => simp [findSecondMin]
    | cons x xs =>
      cases xs with
      | nil => simp [findSecondMin]
      | cons y ys =>
        obtain ⟨hc, hh⟩ := knockout_cost oracle x (y :: ys)
        simp only [findSecondMin, FreeM.countQueries_bind, hc, countQueries_findMin,
          List.length_cons]
        have := Nat.clog_pos (b := 2) (n := ys.length + 1 + 1) (by decide) (by omega)
        simp only [List.length_cons] at hh
        omega

private def Covers (r : α → α → Prop) (xs : List α) (a : Champion α) : Prop :=
  ∃ rest, xs.Perm (a.winner :: rest) ∧ (∀ x ∈ rest, r a.winner x) ∧
    (∀ b ∈ a.opponents, b ∈ rest) ∧ (∀ x ∈ rest, ∃ b ∈ a.opponents, r b x)

private theorem Covers.of_perm {r : α → α → Prop} {xs ys : List α} {a : Champion α}
    (h : Covers r ys a) (p : xs.Perm ys) : Covers r xs a := by
  obtain ⟨rest, hp, hr⟩ := h
  exact ⟨rest, p.trans hp, hr⟩

private theorem Covers.beats {r : α → α → Prop} [Std.Total r] [IsTrans α r]
    {xs ys : List α} {a b : Champion α} (ha : Covers r xs a) (hb : Covers r ys b)
    (hw : r a.winner b.winner) : Covers r (xs ++ ys) (a.beats b) := by
  obtain ⟨as, pa, mina, suba, cova⟩ := ha
  obtain ⟨bs, pb, minb, _, _⟩ := hb
  refine ⟨as ++ b.winner :: bs, pa.append pb, ?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact mina x hx
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact hw
      · exact _root_.trans hw (minb x hx)
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_append_right _ (List.mem_cons_self ..)
    · exact List.mem_append_left _ (suba x hx)
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨z, hz, hzx⟩ := cova x hx
      exact ⟨z, List.mem_cons_of_mem _ hz, hzx⟩
    · refine ⟨b.winner, List.mem_cons_self .., ?_⟩
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (Std.Total.total b.winner b.winner).elim id id
      · exact minb x hx

private theorem knockout_covers (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (ho : ∀ a b, oracle (.le a b) = decide (r a b))
    (x : α) (xs : List α) : Covers r (x :: xs) ((knockout x xs).eval oracle) := by
  cases xs with
  | nil =>
    simp only [knockout, FreeM.eval_pure]
    exact ⟨[], List.Perm.refl _, by simp, by simp, by simp⟩
  | cons y ys =>
    let ls := ys.take (ys.length / 2)
    let rs := ys.drop (ys.length / 2)
    let a := (knockout x ls).eval oracle
    let b := (knockout y rs).eval oracle
    have ha := knockout_covers r oracle ho x ls
    have hb := knockout_covers r oracle ho y rs
    have hp : (x :: y :: ys).Perm ((x :: ls) ++ y :: rs) :=
      List.Perm.cons x (List.perm_cons_append_cons y (by rw [List.take_append_drop]))
    simp only [knockout, FreeM.eval_bind, LEQuery.ask, FreeM.eval_lift, ho, FreeM.eval_pure]
    change Covers r _ (if decide (r a.winner b.winner) then a.beats b else b.beats a)
    by_cases hw : r a.winner b.winner
    · simpa only [hw, decide_true, ↓reduceIte] using (ha.beats hb hw).of_perm hp
    · have hw' : r b.winner a.winner := (Std.Total.total _ _).resolve_left hw
      simpa only [hw, decide_false, Bool.false_eq_true, ↓reduceIte] using
        (hb.beats ha hw').of_perm (hp.trans List.perm_append_comm)
termination_by xs.length
decreasing_by all_goals simp [*]

/-- Against a total preorder, the second smallest has rank one in the original list, counting
repetitions. In particular, two copies of a least element occupy its first two ranks. -/
theorem findSecondMin_correct (r : α → α → Prop) [DecidableRel r] [Std.Total r] [IsTrans α r]
    (oracle : {ι : Type} → LEQuery α ι → ι) (horacle : ∀ a b, oracle (.le a b) = decide (r a b))
    {xs : List α} (h : 2 ≤ xs.length) :
    ∃ y, (findSecondMin xs).eval oracle = some y ∧ xs.IsOrderStatistic r 1 y := by
  obtain _ | ⟨x, xs⟩ := xs
  · simp at h
  obtain _ | ⟨q, qs⟩ := xs
  · simp at h
  let a := (knockout x (q :: qs)).eval oracle
  obtain ⟨rest, hp, ha, sub, covered⟩ := knockout_covers r oracle horacle x (q :: qs)
  have hne : a.opponents ≠ [] := by
    obtain ⟨u, hu⟩ : ∃ u, u ∈ rest := by
      have := hp.length_eq
      cases rest <;> simp_all
    obtain ⟨b, hb, _⟩ := covered u hu
    intro he
    simpa [a] using (he ▸ hb : b ∈ ([] : List α))
  obtain ⟨y, hy, hmem, hmin⟩ := findMin_correct r oracle horacle hne
  have hyr := sub y hmem
  have hleast (u) (hu : u ∈ rest) : r y u := by
    obtain ⟨b, hb, hbu⟩ := covered u hu
    exact _root_.trans (hmin b hb) hbu
  refine ⟨y, ?_, hp.mem_iff.mpr (List.mem_cons_of_mem _ hyr), ?_, ?_⟩
  · simpa only [findSecondMin, FreeM.eval_bind] using hy
  · rw [hp.countP_eq, List.countP_cons]
    have hz : rest.countP (fun u => decide (¬r y u)) = 0 :=
      List.countP_eq_zero.mpr fun u hu => by simp [hleast u hu]
    rw [hz]
    split <;> decide
  · rw [hp.countP_eq, List.countP_cons]
    have hpos : 0 < rest.countP (fun u => decide (r u y)) :=
      List.countP_pos_iff.mpr ⟨y, hyr, by simp [hleast y hyr]⟩
    simp only [ha y hyr, decide_true, ↓reduceIte]
    omega

/-- The tournament meets the distinct-key specification assumed by comparison lower bounds. -/
theorem findSecondMin_isSecondMinAlg : IsSecondMinAlg (findSecondMin (α := α)) where
  correct r _ _ oracle ho _xs _hnodup hlen := findSecondMin_correct r oracle ho hlen

/-- Lists shorter than two have no second element under any oracle. -/
theorem eval_findSecondMin_eq_none (oracle : {ι : Type} → LEQuery α ι → ι)
    {xs : List α} (h : xs.length < 2) : (findSecondMin xs).eval oracle = none := by
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp_all [findSecondMin]

end Cslib.Query
