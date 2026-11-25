/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.Basic
public import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.Basic

/-!
# The core of the two-sided matching game

This module proves that the **core** (and, under strict preferences, the **weak core**) of the
one-to-one two-sided matching game coincides with the set of **stable matchings**
([SchummerVohra2007], Theorem 10.12, p. 257; see also [RothSotomayor1990], Chapter 2), for both:
* strict complete preference lists (`Instance n`), and
* strict, possibly incomplete preference lists with unequal sides (`IncompleteInstance m n`).

A coalition `(P, R)` *strictly blocks* a matching `μ` via `μ'` when `P ∪ R` is nonempty, `μ'`
matches members of `P` only to members of `R` (and vice versa), and every agent in `P ∪ R`
strictly prefers its outcome under `μ'` to its outcome under `μ`. Under strict preferences on
`IncompleteInstance m n`, unacceptable partners are strictly dispreferred to staying unmatched
(`none`), so singleton coalitions `{p}` and `{r}` force individual rationality.

A coalition `(P, R)` *weakly blocks* `μ` via `μ'` when every member of `P ∪ R` weakly prefers its
outcome under `μ'` to `μ` (`o₁ = o₂` or strict preference), and at least one member strictly
prefers `μ'`. Because preferences are strict, both cores coincide with stability.

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.Instance.IsBlockingCoalition`,
  `Cslib.Algorithms.Lean.StableMatching.Instance.IsWeaklyBlockingCoalition`,
  `Cslib.Algorithms.Lean.StableMatching.Instance.InCore`,
  `Cslib.Algorithms.Lean.StableMatching.Instance.InWeakCore`: strict and weak blocking coalitions
  and cores for `Instance n`.
* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.IsBlockingCoalition`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.IsWeaklyBlockingCoalition`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.InCore`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.InWeakCore`: the same for
  `IncompleteInstance m n`, with strict preference ordering treating unacceptable partners as
  strictly worse than staying unmatched (`none`).

## Main results

* `Cslib.Algorithms.Lean.StableMatching.Instance.isStable_iff_inCore`: **Theorem 10.12**
  ([SchummerVohra2007], p. 257): `I.IsStable μ ↔ I.InCore μ`.
* `Cslib.Algorithms.Lean.StableMatching.Instance.isStable_iff_inWeakCore`: under strict complete
  preferences, the weak core also equals the set of stable matchings.
* `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.isStable_iff_inCore`,
  `Cslib.Algorithms.Lean.StableMatching.IncompleteInstance.isStable_iff_inWeakCore`: the
  incomplete-list counterparts with unequal sides.

## References

* [SchummerVohra2007]
* [RothSotomayor1990]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace Instance

variable {n : ℕ} (I : Instance n)

/-- A nonempty coalition `(P, R)` strictly blocks a complete matching `μ` via `μ'`
([SchummerVohra2007], p. 257) when `μ'` maps `P` into `R` and `R` into `P`, and every agent in
`P ∪ R` strictly prefers its partner in `μ'` to its partner in `μ`. -/
@[expose] def IsBlockingCoalition (μ : Matching n) (P R : Set (Fin n)) (μ' : Matching n) : Prop :=
  (P.Nonempty ∨ R.Nonempty) ∧
    (∀ p ∈ P, μ' p ∈ R ∧ I.propRank p (μ' p) < I.propRank p (μ p)) ∧
    (∀ r ∈ R, μ'.symm r ∈ P ∧ I.recvRank r (μ'.symm r) < I.recvRank r (μ.symm r))

/-- A coalition `(P, R)` weakly blocks `μ` via `μ'` when `μ'` maps `P` into `R` and `R` into `P`,
every agent in `P ∪ R` weakly prefers its partner in `μ'` to `μ`, and at least one agent strictly
prefers `μ'`. -/
@[expose] def IsWeaklyBlockingCoalition (μ : Matching n) (P R : Set (Fin n)) (μ' : Matching n) :
    Prop :=
  (∀ p ∈ P, μ' p ∈ R ∧ I.propRank p (μ' p) ≤ I.propRank p (μ p)) ∧
    (∀ r ∈ R, μ'.symm r ∈ P ∧ I.recvRank r (μ'.symm r) ≤ I.recvRank r (μ.symm r)) ∧
    ((∃ p ∈ P, I.propRank p (μ' p) < I.propRank p (μ p)) ∨
      (∃ r ∈ R, I.recvRank r (μ'.symm r) < I.recvRank r (μ.symm r)))

/-- The **core** of the matching game `I`: no nonempty coalition strictly blocks `μ`. -/
@[expose] def InCore (μ : Matching n) : Prop :=
  ∀ (P R : Set (Fin n)) (μ' : Matching n), ¬ I.IsBlockingCoalition μ P R μ'

/-- The **weak core** of `I`: no coalition weakly blocks `μ`. -/
@[expose] def InWeakCore (μ : Matching n) : Prop :=
  ∀ (P R : Set (Fin n)) (μ' : Matching n), ¬ I.IsWeaklyBlockingCoalition μ P R μ'

private theorem inWeakCore_of_isStable {μ : Matching n} (hμ : I.IsStable μ) : I.InWeakCore μ := by
  rintro P R μ' ⟨hP, hR, ⟨p, hp, hlt⟩ | ⟨r, hr, hlt⟩⟩
  · have hleR : I.recvRank (μ' p) p ≤ I.recvRank (μ' p) (μ.symm (μ' p)) := by
      simpa using (hR (μ' p) (hP p hp).1).2
    refine hμ p (μ' p) ⟨hlt, lt_of_le_of_ne hleR fun heq => lt_irrefl (I.propRank p (μ' p)) ?_⟩
    rwa [← μ.symm_apply_eq.1 (I.recvRank_injective (μ' p) heq).symm] at hlt
  · have hleP : I.propRank (μ'.symm r) r ≤ I.propRank (μ'.symm r) (μ (μ'.symm r)) := by
      simpa using (hP (μ'.symm r) (hR r hr).1).2
    refine hμ (μ'.symm r) r ⟨lt_of_le_of_ne hleP fun heq =>
      lt_irrefl (I.recvRank r (μ'.symm r)) ?_, hlt⟩
    rwa [μ.symm_apply_eq.2 (I.propRank_injective (μ'.symm r) heq)] at hlt

private theorem isStable_of_inCore {μ : Matching n} (hμ : I.InCore μ) : I.IsStable μ := by
  classical
  rintro p r ⟨hp, hr⟩
  let σ : Matching n := μ.trans (Equiv.swap (μ p) r)
  have hσp : σ p = r := by simp [σ, Equiv.swap_apply_left]
  have hσr : σ.symm r = p := (Equiv.symm_apply_eq σ).2 hσp.symm
  refine hμ {p} {r} σ ⟨Or.inl ⟨p, rfl⟩, ?_, ?_⟩
  · rintro _ rfl
    exact ⟨hσp, hσp ▸ hp⟩
  · rintro _ rfl
    exact ⟨hσr, hσr ▸ hr⟩

private theorem inCore_of_inWeakCore {μ : Matching n} (hμ : I.InWeakCore μ) : I.InCore μ := by
  rintro P R μ' ⟨⟨p, hp⟩ | ⟨r, hr⟩, hP, hR⟩
  · exact hμ P R μ' ⟨fun p hp => ⟨(hP p hp).1, (hP p hp).2.le⟩,
      fun r hr => ⟨(hR r hr).1, (hR r hr).2.le⟩, Or.inl ⟨p, hp, (hP p hp).2⟩⟩
  · exact hμ P R μ' ⟨fun p hp => ⟨(hP p hp).1, (hP p hp).2.le⟩,
      fun r hr => ⟨(hR r hr).1, (hR r hr).2.le⟩, Or.inr ⟨r, hr, (hR r hr).2⟩⟩

/-- **Theorem 10.12** ([SchummerVohra2007], p. 257): a complete matching lies in the core of `I`
if and only if it is stable. -/
theorem isStable_iff_inCore (μ : Matching n) : I.IsStable μ ↔ I.InCore μ :=
  ⟨fun h => I.inCore_of_inWeakCore (I.inWeakCore_of_isStable h), I.isStable_of_inCore⟩

/-- Under strict complete preferences, the weak core coincides with the set of stable
matchings. -/
theorem isStable_iff_inWeakCore (μ : Matching n) : I.IsStable μ ↔ I.InWeakCore μ :=
  ⟨I.inWeakCore_of_isStable, fun h => I.isStable_of_inCore (I.inCore_of_inWeakCore h)⟩

end Instance

namespace IncompleteInstance

variable {m n : ℕ} (I : IncompleteInstance m n)

/-- Strict preference score for proposer `p` on an outcome `o : Option (Fin n)`: acceptable
partners receive their list index (`< length`), staying unmatched (`none`) receives `length`, and
unacceptable partners receive `length + 1` (strictly worse than staying unmatched). -/
@[expose] def propScore (p : Fin m) : Option (Fin n) → ℕ
  | some r => if r ∈ I.propPref p then (I.propPref p).idxOf r else (I.propPref p).length + 1
  | none => (I.propPref p).length

/-- Strict preference score for receiver `r` on an outcome `o : Option (Fin m)`. -/
@[expose] def recvScore (r : Fin n) : Option (Fin m) → ℕ
  | some p => if p ∈ I.recvPref r then (I.recvPref r).idxOf p else (I.recvPref r).length + 1
  | none => (I.recvPref r).length

private theorem propScore_lt_iff_some_of_mem {p : Fin m} {r : Fin n} (hmem : r ∈ I.propPref p)
    {o : Option (Fin n)} (ho : ∀ r', o = some r' → r' ∈ I.propPref p) :
    I.propScore p (some r) < I.propScore p o ↔ I.propRank p (some r) < I.propRank p o := by
  simp only [propScore, hmem, ↓reduceIte, propRank]
  cases o with
  | none => rfl
  | some r' => simp only [ho r' rfl, ↓reduceIte]

/-- Proposer `p` strictly prefers outcome `o₁` to outcome `o₂` (`none` strictly beats every
unacceptable partner, and every acceptable partner strictly beats `none` in list order). -/
@[expose] def PropPrefers (p : Fin m) (o₁ o₂ : Option (Fin n)) : Prop :=
  I.propScore p o₁ < I.propScore p o₂

/-- Receiver `r` strictly prefers outcome `o₁` to outcome `o₂` (`none` strictly beats every
unacceptable partner, and every acceptable partner strictly beats `none` in list order). -/
@[expose] def RecvPrefers (r : Fin n) (o₁ o₂ : Option (Fin m)) : Prop :=
  I.recvScore r o₁ < I.recvScore r o₂

private theorem propPrefers_irrefl (p : Fin m) (o : Option (Fin n)) : ¬ I.PropPrefers p o o :=
  lt_irrefl _

/-- A nonempty coalition `(P, R)` strictly blocks a partial matching `μ` via `μ'` when `μ'` only
matches agents of `P` inside `R` (and vice versa), leaving partners optionally unmatched, and
every member of `P ∪ R` strictly prefers its outcome under `μ'` to `μ`. -/
@[expose] def IsBlockingCoalition (μ : PartialMatching m n) (P : Set (Fin m)) (R : Set (Fin n))
    (μ' : PartialMatching m n) : Prop :=
  (P.Nonempty ∨ R.Nonempty) ∧
    (∀ p ∈ P, (∀ r, μ' p = some r → r ∈ R) ∧ I.PropPrefers p (μ' p) (μ p)) ∧
    (∀ r ∈ R, (∀ p, μ'.symm r = some p → p ∈ P) ∧ I.RecvPrefers r (μ'.symm r) (μ.symm r))

/-- A coalition `(P, R)` weakly blocks `μ` via `μ'` when `μ'` matches `P` inside `R` (and vice
versa), every member weakly prefers `μ'` to `μ` (either equal outcome or strictly preferred), and
at least one member strictly prefers `μ'`. -/
@[expose] def IsWeaklyBlockingCoalition (μ : PartialMatching m n) (P : Set (Fin m))
    (R : Set (Fin n)) (μ' : PartialMatching m n) : Prop :=
  (∀ p ∈ P, (∀ r, μ' p = some r → r ∈ R) ∧ (μ' p = μ p ∨ I.PropPrefers p (μ' p) (μ p))) ∧
    (∀ r ∈ R, (∀ p, μ'.symm r = some p → p ∈ P) ∧
      (μ'.symm r = μ.symm r ∨ I.RecvPrefers r (μ'.symm r) (μ.symm r))) ∧
    ((∃ p ∈ P, I.PropPrefers p (μ' p) (μ p)) ∨ (∃ r ∈ R, I.RecvPrefers r (μ'.symm r) (μ.symm r)))

/-- The **core** of `IncompleteInstance m n`: no nonempty coalition strictly blocks `μ`. -/
@[expose] def InCore (μ : PartialMatching m n) : Prop :=
  ∀ (P : Set (Fin m)) (R : Set (Fin n)) (μ' : PartialMatching m n),
    ¬ I.IsBlockingCoalition μ P R μ'

/-- The **weak core** of `IncompleteInstance m n`: no coalition weakly blocks `μ`. -/
@[expose] def InWeakCore (μ : PartialMatching m n) : Prop :=
  ∀ (P : Set (Fin m)) (R : Set (Fin n)) (μ' : PartialMatching m n),
    ¬ I.IsWeaklyBlockingCoalition μ P R μ'

private theorem propPrefers_implies_propRank_lt {p : Fin m} {r : Fin n} {o : Option (Fin n)}
    (ho : ∀ r', o = some r' → r' ∈ I.propPref p) (h : I.PropPrefers p (some r) o) :
    I.propRank p (some r) < I.propRank p o := by
  refine (I.propScore_lt_iff_some_of_mem (by_contra fun hnm => ?_) ho).1 h
  simp only [PropPrefers, propScore, hnm, ↓reduceIte] at h
  rcases o with _ | r'
  · dsimp only [propScore] at h; omega
  · have := List.idxOf_lt_length_iff.2 (ho r' rfl)
    simp only [ho r' rfl, ↓reduceIte] at h; omega

private theorem inWeakCore_of_isStable {μ : PartialMatching m n} (hμ : I.IsStable μ) :
    I.InWeakCore μ := by
  rintro P R μ' ⟨hP, hR, ⟨p, hp, hlt⟩ | ⟨r, hr, hlt⟩⟩ <;>
    have hP_acc : ∀ p r', μ p = some r' → r' ∈ I.propPref p := fun p r' h => (hμ.1 p r' h).1 <;>
    have hR_acc : ∀ r p', μ.symm r = some p' → p' ∈ I.recvPref r := fun r p' h =>
      (hμ.1 p' r (μ.eq_some_iff.1 h)).2
  · rcases hμ'p : μ' p with _ | r
    · rw [hμ'p] at hlt
      rcases hμp : μ p with _ | r'
      · exact lt_irrefl _ (hμp ▸ hlt)
      · have := List.idxOf_lt_length_iff.2 (hP_acc p r' hμp)
        simp only [PropPrefers, propScore, hμp, hP_acc p r' hμp, ↓reduceIte] at hlt; omega
    · have hsymm : μ'.symm r = some p := μ'.eq_some_iff.2 hμ'p
      rcases (hR r ((hP p hp).1 r hμ'p)).2 with heq | hltR
      · rw [hμ'p, μ.eq_some_iff.1 (hsymm ▸ heq.symm)] at hlt
        exact I.propPrefers_irrefl p _ hlt
      · exact hμ.2 p r ⟨I.propPrefers_implies_propRank_lt (hP_acc p) (hμ'p ▸ hlt),
          I.swap.propPrefers_implies_propRank_lt (hR_acc r) (hsymm ▸ hltR)⟩
  · rcases hμ'r : μ'.symm r with _ | p
    · rw [hμ'r] at hlt
      rcases hμr : μ.symm r with _ | p'
      · exact lt_irrefl _ (hμr ▸ hlt)
      · have := List.idxOf_lt_length_iff.2 (hR_acc r p' hμr)
        simp only [RecvPrefers, recvScore, hμr, hR_acc r p' hμr, ↓reduceIte] at hlt; omega
    · have hfwd : μ' p = some r := μ'.eq_some_iff.1 hμ'r
      rcases (hP p ((hR r hr).1 p hμ'r)).2 with heq | hltP
      · rw [hμ'r, μ.eq_some_iff.2 (hfwd ▸ heq.symm)] at hlt
        exact lt_irrefl _ hlt
      · exact hμ.2 p r ⟨I.propPrefers_implies_propRank_lt (hP_acc p) (hfwd ▸ hltP),
          I.swap.propPrefers_implies_propRank_lt (hR_acc r) (hμ'r ▸ hlt)⟩

private theorem isStable_of_inCore {μ : PartialMatching m n} (hμ : I.InCore μ) :
    I.IsStable μ := by
  let emptyM : PartialMatching m n :=
    PartialMatching.ofInjOn (fun _ => none) (fun _ _ _ h => by cases h)
  have hempty_symm (r : Fin n) : emptyM.symm r = none :=
    Option.eq_none_iff_forall_not_mem.2 fun p h => by simpa [emptyM] using emptyM.eq_some_iff.1 h
  have hir : I.IsIndividuallyRational μ := fun p r hpr => by
    refine ⟨by_contra fun hnm => ?_, by_contra fun hnm => ?_⟩
    · refine hμ {p} ∅ emptyM ⟨Or.inl ⟨p, rfl⟩, ?_, fun _ hr => hr.elim⟩
      rintro x rfl
      refine ⟨fun _ h => by simp [emptyM] at h, ?_⟩
      simp only [PropPrefers, show emptyM x = none from rfl, hpr, propScore, hnm, ↓reduceIte]
      omega
    · refine hμ ∅ {r} emptyM ⟨Or.inr ⟨r, rfl⟩, fun _ hp => hp.elim, ?_⟩
      rintro _ rfl
      refine ⟨fun _ h => by simp [hempty_symm] at h, ?_⟩
      simp only [RecvPrefers, hempty_symm, μ.eq_some_iff.2 hpr, recvScore, hnm, ↓reduceIte]
      omega
  refine ⟨hir, fun p r ⟨hp, hr⟩ => ?_⟩
  let σ : PartialMatching m n := PartialMatching.ofInjOn
    (fun x => if x = p then some r else none)
    (fun x y s hx hy => by
      split_ifs at hx with hxp
      split_ifs at hy with hyp
      exact hxp.trans hyp.symm)
  have hσp : σ p = some r := by simp [σ]
  have hσr : σ.symm r = some p := σ.eq_some_iff.2 hσp
  have hr_mem : r ∈ I.propPref p :=
    (I.propRank_some_lt_none_iff p r).1 (lt_of_lt_of_le hp (I.propRank_le_propRank_none p _))
  have hp_mem : p ∈ I.recvPref r :=
    (I.recvRank_some_lt_none_iff r p).1 (lt_of_lt_of_le hr (I.recvRank_le_recvRank_none r _))
  refine hμ {p} {r} σ ⟨Or.inl ⟨p, rfl⟩, ?_, ?_⟩
  · rintro x rfl
    exact ⟨fun r' hr' => Option.some.inj (hr'.symm.trans hσp), hσp ▸
      (I.propScore_lt_iff_some_of_mem hr_mem fun r' h => (hir x r' h).1).2 hp⟩
  · rintro y rfl
    exact ⟨fun p' hp' => Option.some.inj (hp'.symm.trans hσr), hσr ▸
      (I.swap.propScore_lt_iff_some_of_mem hp_mem
        fun p' h => (hir p' y (μ.eq_some_iff.1 h)).2).2 hr⟩

private theorem inCore_of_inWeakCore {μ : PartialMatching m n} (hμ : I.InWeakCore μ) :
    I.InCore μ := by
  rintro P R μ' ⟨⟨p, hp⟩ | ⟨r, hr⟩, hP, hR⟩
  · exact hμ P R μ' ⟨fun p hp => ⟨(hP p hp).1, Or.inr (hP p hp).2⟩,
      fun r hr => ⟨(hR r hr).1, Or.inr (hR r hr).2⟩, Or.inl ⟨p, hp, (hP p hp).2⟩⟩
  · exact hμ P R μ' ⟨fun p hp => ⟨(hP p hp).1, Or.inr (hP p hp).2⟩,
      fun r hr => ⟨(hR r hr).1, Or.inr (hR r hr).2⟩, Or.inr ⟨r, hr, (hR r hr).2⟩⟩

/-- **Theorem 10.12** ([SchummerVohra2007], p. 257; incomplete-list extension): a partial matching
lies in the core of `IncompleteInstance m n` if and only if it is stable. -/
theorem isStable_iff_inCore (μ : PartialMatching m n) : I.IsStable μ ↔ I.InCore μ :=
  ⟨fun h => I.inCore_of_inWeakCore (I.inWeakCore_of_isStable h), I.isStable_of_inCore⟩

/-- Under strict incomplete preferences, the weak core coincides with the set of stable partial
matchings. -/
theorem isStable_iff_inWeakCore (μ : PartialMatching m n) : I.IsStable μ ↔ I.InWeakCore μ :=
  ⟨I.inWeakCore_of_isStable, fun h => I.isStable_of_inCore (I.inCore_of_inWeakCore h)⟩

end IncompleteInstance

end Cslib.Algorithms.Lean.StableMatching
