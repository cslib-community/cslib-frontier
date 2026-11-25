/-
Copyright (c) 2026 Jesse Alama. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jesse Alama
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.List.SortedAssoc
import Mathlib.Data.List.TakeWhile

/-!
# Range restriction of a concatenation of sorted association lists

A sorted association list that is stored as a sequence of non-empty blocks, such as the leaves of
a B+-tree, is restricted to a closed interval block by block. The blocks that contribute form a
contiguous run, and every block of the run other than its first and last is kept whole.

## Main result

* `Cslib.SortedAssoc.exists_run_range_flatten`: the blocks split as a prefix, a run and a suffix;
  the restriction of the concatenation is that of the run, every block of the run contributes,
  and every block of the run other than the first and last is unchanged.
-/

public section

universe u v

namespace Cslib.SortedAssoc

variable {α : Type u} {β : Type v} [LinearOrder α] {lo hi : α}

/-- A block with a non-empty restriction has an entry in the interval. -/
private theorem exists_mem_of_range_ne_nil {l : List (α × β)} (h : range lo hi l ≠ []) :
    ∃ p ∈ l, lo ≤ p.1 ∧ p.1 ≤ hi :=
  (List.exists_mem_of_ne_nil _ h).imp fun _ hp => mem_range_iff.1 hp

/-- Restricting a concatenation of non-empty blocks with strictly increasing keys to a closed
interval: the blocks split as a prefix, a run and a suffix such that the restriction is that of
the run, every block of the run contributes, and every block of the run other than its first and
last is kept whole. -/
theorem exists_run_range_flatten {L : List (List (α × β))} (hs : L.flatten.IsSortedAssoc)
    (hne : ∀ l ∈ L, l ≠ []) (lo hi : α) :
    ∃ pre run post : List (List (α × β)), L = pre ++ run ++ post ∧
      range lo hi L.flatten = (run.map (range lo hi)).flatten ∧
      (∀ l ∈ run, range lo hi l ≠ []) ∧
      ∀ l ∈ (run.drop 1).dropLast, range lo hi l = l := by
  have hp : L.Pairwise fun a b => ∀ p ∈ a, ∀ q ∈ b, p.1 < q.1 :=
    (List.pairwise_flatten.1 hs.pairwise).2
  let P : List (α × β) → Bool := fun l => (range lo hi l).isEmpty
  let R := L.dropWhile P
  have hL : L = L.takeWhile P ++ (R.takeWhile (fun l => !P l) ++ R.dropWhile fun l => !P l) := by
    rw [List.takeWhile_append_dropWhile, List.takeWhile_append_dropWhile]
  generalize hpre : L.takeWhile P = pre at hL
  generalize hrun : R.takeWhile (fun l => !P l) = run at hL
  generalize hpost : R.dropWhile (fun l => !P l) = post at hL
  have hpre' : ∀ l ∈ pre, range lo hi l = [] := fun l hl =>
    List.isEmpty_iff.1 (List.mem_takeWhile_imp (p := P) (hpre ▸ hl))
  have hrun' : ∀ l ∈ run, range lo hi l ≠ [] := fun l hl =>
    List.isEmpty_eq_false_iff.1
      ((Bool.not_eq_true' _).mp (List.mem_takeWhile_imp (p := fun l => !P l) (hrun ▸ hl)))
  rw [hL, List.pairwise_append, List.pairwise_append] at hp
  obtain ⟨-, ⟨hpr, hpp, hrp⟩, -⟩ := hp
  have hpost' : ∀ l ∈ post, range lo hi l = [] := by
    cases hpo : post with
    | nil => exact fun _ h => absurd h List.not_mem_nil
    | cons p₀ ps =>
      have hp₀ : range lo hi p₀ = [] := by
        have hne' : R.dropWhile (fun l => !P l) ≠ [] := hpost ▸ hpo ▸ List.cons_ne_nil p₀ ps
        have hhead := List.head_dropWhile_not (fun l => !P l) hne'
        simp only [hpost, hpo, List.head_cons] at hhead
        exact List.isEmpty_iff.1 ((Bool.not_eq_false' _).mp hhead)
      obtain ⟨r, hr⟩ : ∃ r, r ∈ run := by
        cases hR : R with
        | nil =>
          rw [hR, List.dropWhile_nil] at hpost
          exact absurd (hpo.symm.trans hpost.symm) (List.cons_ne_nil p₀ ps)
        | cons r₀ R' =>
          have hR' : L.dropWhile P ≠ [] := show R ≠ [] from hR ▸ List.cons_ne_nil r₀ R'
          have h₀ : P r₀ = false := by
            have hhead := List.head_dropWhile_not P hR'
            change P (R.head _) = false at hhead
            simpa only [hR, List.head_cons] using hhead
          exact ⟨r₀, by simp [← hrun, hR, h₀]⟩
      obtain ⟨x, hx, hlo, -⟩ := exists_mem_of_range_ne_nil (hrun' r hr)
      obtain ⟨y, hy⟩ := List.exists_mem_of_ne_nil p₀ (hne p₀ (by simp [hL, hpo]))
      have hxy : x.1 < y.1 := hrp r hr p₀ (hpo ▸ List.mem_cons_self) x hx y hy
      have hhi : hi < y.1 :=
        (range_eq_nil_iff.1 hp₀ y hy).resolve_left fun h => lt_asymm h (hlo.trans_lt hxy)
      rw [hpo] at hpp
      intro l hl
      rcases List.mem_cons.1 hl with rfl | hl
      · exact hp₀
      · exact range_eq_nil_iff.2 fun q hq =>
          Or.inr (hhi.trans ((List.pairwise_cons.1 hpp).1 l hl y hy q hq))
  refine ⟨pre, run, post, by rw [hL, List.append_assoc], ?_, hrun', ?_⟩
  · have h₁ : (pre.map (range lo hi)).flatten = [] :=
      List.flatten_eq_nil_iff.2 (List.forall_mem_map.2 hpre')
    have h₂ : (post.map (range lo hi)).flatten = [] :=
      List.flatten_eq_nil_iff.2 (List.forall_mem_map.2 hpost')
    have hf : range lo hi (pre ++ (run ++ post)).flatten =
        ((pre ++ (run ++ post)).map (range lo hi)).flatten := List.filter_flatten ..
    rw [hL, hf, List.map_append, List.map_append, List.flatten_append, List.flatten_append,
      h₁, h₂, List.nil_append, List.append_nil]
  · intro l hl
    cases hT : run with
    | nil => simp [hT] at hl
    | cons a T =>
      rw [hT] at hl hpr hrun'
      simp only [List.drop_one, List.tail_cons] at hl
      have hTne : T ≠ [] := fun hTe => by simp [hTe] at hl
      have hlT : l ∈ T := List.mem_of_mem_dropLast hl
      obtain ⟨x, hx, hlo, -⟩ := exists_mem_of_range_ne_nil (hrun' a List.mem_cons_self)
      obtain ⟨z, hz, -, hhi⟩ := exists_mem_of_range_ne_nil
        (hrun' (T.getLast hTne) (List.mem_cons_of_mem _ (List.getLast_mem hTne)))
      have hTp := (List.pairwise_cons.1 hpr).2
      rw [← List.dropLast_append_getLast hTne, List.pairwise_append] at hTp
      rw [range_def, List.filter_eq_self]
      intro q hq
      have h₁ : x.1 < q.1 := (List.pairwise_cons.1 hpr).1 l hlT x hx q hq
      have h₂ : q.1 < z.1 := hTp.2.2 l hl _ (List.mem_singleton_self _) q hq z hz
      exact decide_eq_true ⟨hlo.trans h₁.le, h₂.le.trans hhi⟩

end Cslib.SortedAssoc
