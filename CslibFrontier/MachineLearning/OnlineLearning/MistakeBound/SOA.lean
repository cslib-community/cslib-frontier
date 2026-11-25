/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone

/-!
# The standard optimal algorithm

The **standard optimal algorithm** (SOA) [Littlestone1988, §3, Algorithm 2;
DanielySabatoBenDavidShalevShwartz2015] keeps the version space `V` of the history. On instance `x`,
for each label `y : β` it considers the restriction `V_y = {c ∈ V | c x = y}` and predicts a label
`y₀` whose restriction is nonempty and maximizes `littlestoneDim V_y` among all nonempty
restrictions at `x` (or an arbitrary label in `β` when no such maximizer exists).

After a mistake `soa C h x ≠ y` on an example `(x, y)` consistent with `V`, the Littlestone
dimension of `V` drops by at least one (`littlestoneDim_add_one_le_of_soa_ne`): if a maximizing
branch `y₀ ≠ y` existed, complete mistake trees for `V_y` and `V_{y₀}` combine under `(x, y, y₀)`;
if no maximizing branch existed, the nonempty branches at `x` form a strictly increasing chain of
Littlestone dimensions, forcing `littlestoneDim V = ⊤`. Hence SOA makes at most `littlestoneDim C`
mistakes [Littlestone1988, §3, Lemma 2; DanielySabatoBenDavidShalevShwartz2015]. With the lower
bound of `CslibFrontier.MachineLearning.OnlineLearning.MistakeBound.Littlestone`, this gives
**Littlestone's theorem** for arbitrary nonempty label types `β`:
`optimalMistakeBound C = littlestoneDim C`, and SOA attains it
[Littlestone1988, §3, Theorem 3; DanielySabatoBenDavidShalevShwartz2015]. Both sides may be `⊤`. The
assumption `[Nonempty β]` is necessary: when `α` is nonempty and `β` is empty, `OnlineLearner α β`
is empty so `optimalMistakeBound ∅ = ⊤`, whereas `littlestoneDim ∅ = 0`.

`soa` is a noncomputable specification: it tests emptiness and compares Littlestone dimensions of
arbitrary classes classically. The running time of the algorithm is not modelled.

## Main definitions

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.soa`: the (binary or multiclass) standard
  optimal algorithm.

## Main results

* `Cslib.MachineLearning.OnlineLearning.MistakeBound.mistakeBound_soa`: SOA makes exactly
  `littlestoneDim C` mistakes in the worst case.
* `Cslib.MachineLearning.OnlineLearning.MistakeBound.optimalMistakeBound_eq_littlestoneDim`:
  [Littlestone1988, §3, Theorem 3; DanielySabatoBenDavidShalevShwartz2015], the optimal mistake
  bound is the Littlestone dimension.

## References

* [A. Daniely, S. Sabato, S. Ben-David, S. Shalev-Shwartz, *Multiclass Learnability and the ERM
  Principle*][DanielySabatoBenDavidShalevShwartz2015]
* [N. Littlestone, *Learning quickly when irrelevant attributes abound: a new linear-threshold
  algorithm*][Littlestone1988]
* [S. Shalev-Shwartz, S. Ben-David, *Understanding Machine Learning: From Theory to
  Algorithms*][ShalevShwartzBenDavid2014]
-/

public section

namespace Cslib.MachineLearning.OnlineLearning.MistakeBound

open PACLearning (ConceptClass)

variable {α β : Type*}

/-- `IsMaxBranch C h x y` holds when `(x, y)` is consistent with `versionSpace C h` and maximizes
the Littlestone dimension among all consistent labels at `x`. -/
private def IsMaxBranch (C : ConceptClass α β) (h : List (α × β)) (x : α) (y : β) : Prop :=
  (versionSpace C (h ++ [(x, y)])).Nonempty ∧
    ∀ y' : β, (versionSpace C (h ++ [(x, y')])).Nonempty →
      littlestoneDim (versionSpace C (h ++ [(x, y')])) ≤
        littlestoneDim (versionSpace C (h ++ [(x, y)]))

open Classical in
/-- The standard optimal algorithm [Littlestone1988, §3, Algorithm 2;
DanielySabatoBenDavidShalevShwartz2015]. After the history `h`, on instance `x`, predict a
consistent label maximizing `littlestoneDim (versionSpace C (h ++ [(x, y)]))` if one exists, and an
arbitrary label in `β` otherwise. -/
noncomputable def soa [Nonempty β] (C : ConceptClass α β) : OnlineLearner α β := fun h x =>
  if hex : ∃ y : β, IsMaxBranch C h x y then hex.choose else Classical.arbitrary β

/-- After a mistake of SOA on an example `(x, y)` consistent with some concept of the version
space, the Littlestone dimension of the version space drops by at least one. -/
theorem littlestoneDim_add_one_le_of_soa_ne [Nonempty β] (C : ConceptClass α β)
    (h : List (α × β)) (x : α) (y : β) (hne : soa C h x ≠ y)
    (hy : (versionSpace C (h ++ [(x, y)])).Nonempty) :
    littlestoneDim (versionSpace C (h ++ [(x, y)])) + 1 ≤ littlestoneDim (versionSpace C h) := by
  classical
  by_cases hex : ∃ y₀ : β, IsMaxBranch C h x y₀
  · have hsoa : soa C h x = hex.choose := dite_eq_left hex
    set y₀ := hex.choose
    have hne₀ : y ≠ y₀ := fun h => hne (hsoa.trans h.symm)
    obtain ⟨hy₀, hle⟩ := hex.choose_spec
    have hy' : (versionSpace (versionSpace C h) [(x, y)]).Nonempty := by
      rwa [← versionSpace_append]
    have hy₀' : (versionSpace (versionSpace C h) [(x, y₀)]).Nonempty := by
      rwa [← versionSpace_append]
    have hmin := min_littlestoneDim_add_one_le (versionSpace C h) x hne₀ hy' hy₀'
    simp only [← versionSpace_append] at hmin
    rwa [min_eq_left (hle y hy)] at hmin
  · have hstep : ∀ z : β, (versionSpace C (h ++ [(x, z)])).Nonempty →
        ∃ z' : β, (versionSpace C (h ++ [(x, z')])).Nonempty ∧
          littlestoneDim (versionSpace C (h ++ [(x, z)])) <
            littlestoneDim (versionSpace C (h ++ [(x, z')])) := by
      intro z hz
      have hnot : ¬ IsMaxBranch C h x z := fun hm => hex ⟨z, hm⟩
      simp only [IsMaxBranch, not_and, not_forall, not_le] at hnot
      obtain ⟨z', hz', hlt⟩ := hnot hz
      exact ⟨z', hz', hlt⟩
    have hchain : ∀ n : ℕ, ∃ z : β, (versionSpace C (h ++ [(x, z)])).Nonempty ∧
        (n : ℕ∞) ≤ littlestoneDim (versionSpace C (h ++ [(x, z)])) := by
      intro n
      induction n with
      | zero => exact ⟨y, hy, bot_le⟩
      | succ n ih =>
        obtain ⟨z, hz, hnz⟩ := ih
        obtain ⟨z', hz', hlt⟩ := hstep z hz
        exact ⟨z', hz', Order.add_one_le_of_lt (hnz.trans_lt hlt)⟩
    have htop : littlestoneDim (versionSpace C h) = ⊤ := by
      refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
      obtain ⟨z₀, hz₀, hn₀⟩ := hchain n
      obtain ⟨z₁, hz₁, hlt⟩ := hstep z₀ hz₀
      have hne01 : z₀ ≠ z₁ := fun heq => (heq ▸ hlt).false
      have hz₀' : (versionSpace (versionSpace C h) [(x, z₀)]).Nonempty := by
        rwa [← versionSpace_append]
      have hz₁' : (versionSpace (versionSpace C h) [(x, z₁)]).Nonempty := by
        rwa [← versionSpace_append]
      have hmin := min_littlestoneDim_add_one_le (versionSpace C h) x hne01 hz₀' hz₁'
      simp only [← versionSpace_append] at hmin
      rw [min_eq_left hlt.le] at hmin
      exact hn₀.trans ((le_self_add).trans hmin)
    rw [htop]
    exact le_top

section MistakeBound

variable [DecidableEq β] [Nonempty β]

/-- After the history `h`, SOA makes at most `littlestoneDim (versionSpace C h)` mistakes on
rounds `S` such that `h ++ S` is realizable
[Littlestone1988, §3, Lemma 2; DanielySabatoBenDavidShalevShwartz2015]. -/
theorem mistakesFrom_soa_le (C : ConceptClass α β) (h S : List (α × β))
    (hS : Realizable C (h ++ S)) :
    (mistakesFrom (soa C) h S : ℕ∞) ≤ littlestoneDim (versionSpace C h) := by
  induction S generalizing h with
  | nil => simp
  | cons p S ih =>
    obtain ⟨x, y⟩ := p
    have hS' : Realizable C ((h ++ [(x, y)]) ++ S) := by simpa using hS
    have ih' := ih _ hS'
    have hy : (versionSpace C (h ++ [(x, y)])).Nonempty := by
      obtain ⟨c, hc⟩ := hS'
      rw [versionSpace_append] at hc
      exact ⟨c, hc.1⟩
    rw [mistakesFrom_cons]
    split
    · rw [zero_add]
      refine ih'.trans (littlestoneDim_mono ?_)
      rw [versionSpace_append]
      exact versionSpace_subset _ _
    · rename_i hne
      have hdrop := littlestoneDim_add_one_le_of_soa_ne C h x y hne hy
      push_cast
      rw [add_comm]
      calc ((mistakesFrom (soa C) (h ++ [(x, y)]) S : ℕ∞) + 1)
          ≤ littlestoneDim (versionSpace C (h ++ [(x, y)])) + 1 := by gcongr
        _ ≤ _ := hdrop

theorem mistakeBound_soa_le (C : ConceptClass α β) :
    mistakeBound (soa C) C ≤ littlestoneDim C :=
  mistakeBound_le_iff.mpr fun S hS => by
    have := mistakesFrom_soa_le C [] S (by simpa using hS)
    rwa [versionSpace_nil] at this

/-- SOA makes exactly `littlestoneDim C` mistakes in the worst case. -/
theorem mistakeBound_soa (C : ConceptClass α β) :
    mistakeBound (soa C) C = littlestoneDim C :=
  le_antisymm (mistakeBound_soa_le C) (littlestoneDim_le_mistakeBound _ C)

/-- **Littlestone's theorem** [Littlestone1988, §3, Theorem 3;
DanielySabatoBenDavidShalevShwartz2015]: the optimal mistake bound of a concept class over a
nonempty label type is its Littlestone dimension. Both sides are `⊤` when there are complete mistake
trees of every height. -/
theorem optimalMistakeBound_eq_littlestoneDim (C : ConceptClass α β) :
    optimalMistakeBound C = littlestoneDim C :=
  le_antisymm ((optimalMistakeBound_le (soa C) C).trans (mistakeBound_soa_le C))
    (littlestoneDim_le_optimalMistakeBound C)

/-- SOA is an optimal learner. -/
theorem mistakeBound_soa_eq_optimalMistakeBound (C : ConceptClass α β) :
    mistakeBound (soa C) C = optimalMistakeBound C := by
  rw [mistakeBound_soa, optimalMistakeBound_eq_littlestoneDim]

end MistakeBound

end Cslib.MachineLearning.OnlineLearning.MistakeBound
