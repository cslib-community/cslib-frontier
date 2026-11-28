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
  · obtain ⟨hy₀, hle⟩ := hex.choose_spec
    have hne₀ : y ≠ hex.choose := fun h => hne ((dite_eq_left hex).trans h.symm)
    have hmin := min_littlestoneDim_add_one_le (versionSpace C h) x hne₀
      (by rwa [← versionSpace_append]) (by rwa [← versionSpace_append])
    simpa only [← versionSpace_append, min_eq_left (hle y hy)] using hmin
  · have hstep (z : β) (hz : (versionSpace C (h ++ [(x, z)])).Nonempty) :
        ∃ z', (versionSpace C (h ++ [(x, z')])).Nonempty ∧
          littlestoneDim (versionSpace C (h ++ [(x, z)])) <
            littlestoneDim (versionSpace C (h ++ [(x, z')])) := by
      have hnot : ¬ IsMaxBranch C h x z := fun hm => hex ⟨z, hm⟩
      simp only [IsMaxBranch, not_and, not_forall, not_le, exists_prop] at hnot
      exact hnot hz
    have hchain (n : ℕ) : ∃ z, (versionSpace C (h ++ [(x, z)])).Nonempty ∧
        (n : ℕ∞) ≤ littlestoneDim (versionSpace C (h ++ [(x, z)])) := by
      induction n with
      | zero => exact ⟨y, hy, bot_le⟩
      | succ n ih =>
        obtain ⟨z, hz, hnz⟩ := ih
        obtain ⟨z', hz', hlt⟩ := hstep z hz
        exact ⟨z', hz', Order.add_one_le_of_lt (hnz.trans_lt hlt)⟩
    have htop : littlestoneDim (versionSpace C h) = ⊤ :=
      ENat.eq_top_iff_forall_ge.mpr fun n => by
        obtain ⟨z₀, hz₀, hn₀⟩ := hchain n
        obtain ⟨z₁, hz₁, hlt⟩ := hstep z₀ hz₀
        have hmin := min_littlestoneDim_add_one_le (versionSpace C h) x (y₀ := z₀) (y₁ := z₁)
          (fun heq => (heq ▸ hlt).false) (by rwa [← versionSpace_append])
          (by rwa [← versionSpace_append])
        simp only [← versionSpace_append, min_eq_left hlt.le] at hmin
        exact hn₀.trans (le_self_add.trans hmin)
    simp [htop]

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
    obtain ⟨c, hc⟩ := hS'
    rw [versionSpace_append] at hc
    rw [mistakesFrom_cons]
    split
    · simpa only [zero_add] using
        ih'.trans (littlestoneDim_mono (versionSpace_append .. ▸ versionSpace_subset _ _))
    · rename_i hne
      push_cast
      rw [add_comm]
      calc ((mistakesFrom (soa C) (h ++ [(x, y)]) S : ℕ∞) + 1)
          ≤ littlestoneDim (versionSpace C (h ++ [(x, y)])) + 1 := by gcongr
        _ ≤ _ := littlestoneDim_add_one_le_of_soa_ne C h x y hne ⟨c, hc.1⟩

theorem mistakeBound_soa_le (C : ConceptClass α β) :
    mistakeBound (soa C) C ≤ littlestoneDim C :=
  mistakeBound_le_iff.mpr fun S hS => by
    have h := mistakesFrom_soa_le C [] S (by simpa using hS)
    rwa [versionSpace_nil] at h

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
