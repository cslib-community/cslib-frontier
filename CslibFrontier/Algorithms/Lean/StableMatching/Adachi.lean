/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.Lattice
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Fintype.Option
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.FixedPoints
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Adachi's Tarski fixed-point characterization of stable matchings

Adachi [Adachi2000] observed that stable matchings can be characterized as the fixed points of a
monotone operator on the complete lattice of **pre-matchings** (called *semi-matchings* in
[SchummerVohra2007], Section 10.4.1, pp. 259–260). A pre-matching `ν : I.PreMatching` assigns each
proposer `p` a tentative outcome `ν.propPartner p : Option (Fin n)` and each receiver `r` an
independent tentative outcome `ν.recvPartner r : Option (Fin n)` (`none` representing remaining
single, ranked strictly below every acceptable partner).

Ordering `I.PreMatching` by opposing preferences (`ν ≤ ν'` when every proposer weakly prefers `ν'`
to `ν` and every receiver weakly prefers `ν` to `ν'`; note the printed typo `μ(m) = μ(m)` for
`μ(m) = ν(m)` in item `(i)` on p. 259 of [SchummerVohra2007]) makes `I.PreMatching` a finite
complete lattice. Adachi's operator `I.adachiMap : I.PreMatching →o I.PreMatching` maps `ν` to the
pre-matching in which each proposer chooses its favourite receiver willing to accept it over
`ν.recvPartner`, and symmetrically for receivers against `ν.propPartner`.

We prove that `I.adachiMap` is monotone, that its fixed points are precisely the embedded stable
matchings `PreMatching.ofMatching I μ` (`isFixedPt_adachiMap_iff`), that `Function.fixedPoints
I.adachiMap` is order-isomorphic to `I.Stable` (`fixedPointsOrderIsoStable`), and that Tarski's
greatest and least fixed points `I.adachiMap.gfp` and `I.adachiMap.lfp` recover proposer-proposing
and receiver-proposing deferred acceptance (`adachiMap_gfp`, `adachiMap_lfp`).

## Main definitions

* `Instance.PreMatching`: pre-matchings `(propPartner, recvPartner)` on `Option (Fin n)`, with
  `PartialOrder` and `CompleteLattice` instances.
* `Instance.PreMatching.ofMatching`: embed a `Matching n` into `I.PreMatching`.
* `Instance.willingReceivers`, `Instance.willingProposers`, `Instance.adachiMap`: Adachi's monotone
  operator `I.PreMatching →o I.PreMatching`.
* `Instance.fixedPointsOrderIsoStable`: order isomorphism `Function.fixedPoints I.adachiMap ≃o
  I.Stable`.

## Main results

* `Instance.isFixedPt_ofMatching_iff`, `Instance.isFixedPt_adachiMap_iff`: **Adachi's
  characterization** ([Adachi2000]; [SchummerVohra2007], Section 10.4.1, Theorem 10.14, p. 260):
  the fixed points of `I.adachiMap` are precisely the stable matchings of `I`.
* `Instance.adachiMap_gfp`, `Instance.adachiMap_lfp`: Tarski's greatest and least fixed points of
  `I.adachiMap` equal `I.deferredAcceptance` and `I.receiverDeferredAcceptance`.

## References

* [Adachi2000] (primary PDF unverified; cited via [SchummerVohra2007])
* [SchummerVohra2007], Section 10.4.1, Theorem 10.14, pp. 259–260
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

namespace Instance

variable {n : ℕ} (I : Instance n)

/-! ### Option ranks and the complete lattice of pre-matchings -/

/-- Rank of a tentative outcome `Option (Fin n)` for proposer `p` in `Fin (n + 1)`: `some r` has
rank `(I.propRank p r).castSucc < n`, and remaining single (`none`) has worst rank `Fin.last n`. -/
@[expose] def propOptRank (p : Fin n) : Option (Fin n) ≃ Fin (n + 1) where
  toFun
    | some r => (I.propRank p r).castSucc
    | none => Fin.last n
  invFun k :=
    if h : k.val < n then some (I.propPref p ⟨k.val, h⟩) else none
  left_inv
    | some r => by simp [Fin.is_lt, propPref_propRank]
    | none => by simp
  right_inv k := by
    by_cases h : k.val < n
    · simp only [h, ↓reduceDIte, propRank_propPref]
      ext
      simp
    · simp only [h, ↓reduceDIte]
      ext
      simp only [Fin.val_last]
      have hle : k.val ≤ n := Nat.lt_succ_iff.1 k.isLt
      omega

/-- Rank of a tentative outcome `Option (Fin n)` for receiver `r` in `Fin (n + 1)`: `some p` has
rank `(I.recvRank r p).castSucc < n`, and remaining single (`none`) has worst rank `Fin.last n`. -/
@[expose] def recvOptRank (r : Fin n) : Option (Fin n) ≃ Fin (n + 1) where
  toFun
    | some p => (I.recvRank r p).castSucc
    | none => Fin.last n
  invFun k :=
    if h : k.val < n then some (I.recvPref r ⟨k.val, h⟩) else none
  left_inv
    | some p => by
      have hpr : I.recvPref r (I.recvRank r p) = p := (I.recvPref r).apply_symm_apply p
      simp [Fin.is_lt, hpr]
    | none => by simp
  right_inv k := by
    by_cases h : k.val < n
    · have hrp : I.recvRank r (I.recvPref r ⟨k.val, h⟩) = ⟨k.val, h⟩ :=
        (I.recvPref r).symm_apply_apply _
      simp only [h, ↓reduceDIte, hrp]
      ext
      simp
    · simp only [h, ↓reduceDIte]
      ext
      simp only [Fin.val_last]
      have hle : k.val ≤ n := Nat.lt_succ_iff.1 k.isLt
      omega

@[simp] theorem propOptRank_some (p r : Fin n) :
    I.propOptRank p (some r) = (I.propRank p r).castSucc := rfl

@[simp] theorem propOptRank_none (p : Fin n) :
    I.propOptRank p none = Fin.last n := rfl

@[simp] theorem recvOptRank_some (r p : Fin n) :
    I.recvOptRank r (some p) = (I.recvRank r p).castSucc := rfl

@[simp] theorem recvOptRank_none (r : Fin n) :
    I.recvOptRank r none = Fin.last n := rfl

/-- A **pre-matching** (or *semi-matching*, [Adachi2000]; [SchummerVohra2007], Section 10.4.1,
p. 259) assigns each proposer and each receiver an independent tentative partner in
`Option (Fin n)`. -/
@[ext]
structure PreMatching (I : Instance n) where
  /-- Tentative receiver (or `none`) held by proposer `p`. -/
  propPartner : Fin n → Option (Fin n)
  /-- Tentative proposer (or `none`) held by receiver `r`. -/
  recvPartner : Fin n → Option (Fin n)

instance (I : Instance n) : DecidableEq I.PreMatching :=
  fun ν ν' => decidable_of_iff
    (ν.propPartner = ν'.propPartner ∧ ν.recvPartner = ν'.recvPartner)
    ⟨fun ⟨h₁, h₂⟩ => PreMatching.ext h₁ h₂, fun h => h ▸ ⟨rfl, rfl⟩⟩

namespace PreMatching

variable {I}

/-- Embed a one-to-one `Matching n` as a consistent `PreMatching`. -/
@[expose] def ofMatching (I : Instance n) (μ : Matching n) : I.PreMatching where
  propPartner p := some (μ p)
  recvPartner r := some (μ.symm r)

theorem ofMatching_injective : Function.Injective (ofMatching I) := by
  intro μ ν h
  refine Equiv.ext fun p => ?_
  have hp := congrFun (congrArg propPartner h) p
  exact Option.some_injective _ hp

instance : Fintype I.PreMatching :=
  Fintype.ofEquiv ((Fin n → Option (Fin n)) × (Fin n → Option (Fin n)))
    { toFun := fun x => ⟨x.fst, x.snd⟩
      invFun := fun ν => (ν.propPartner, ν.recvPartner)
      left_inv := fun x => by cases x; rfl
      right_inv := fun ν => by cases ν; rfl }

/-- Equivalence between `I.PreMatching` and `(Fin n → (Fin (n + 1))ᵒᵈ) × (Fin n → Fin (n + 1))`,
orienting proposer ranks so better partners are larger and receiver ranks so worse partners are
larger. -/
@[expose] def ranksEquiv (I : Instance n) :
    I.PreMatching ≃ (Fin n → (Fin (n + 1))ᵒᵈ) × (Fin n → Fin (n + 1)) where
  toFun ν :=
    (fun p => OrderDual.toDual (I.propOptRank p (ν.propPartner p)),
     fun r => I.recvOptRank r (ν.recvPartner r))
  invFun x :=
    { propPartner := fun p => (I.propOptRank p).symm (OrderDual.ofDual (x.fst p))
      recvPartner := fun r => (I.recvOptRank r).symm (x.snd r) }
  left_inv ν := by
    cases ν
    simp only [Equiv.symm_apply_apply, OrderDual.ofDual_toDual]
  right_inv x := by
    cases x
    ext p <;> simp

open Classical in
noncomputable instance : CompleteLattice I.PreMatching :=
  letI : PartialOrder I.PreMatching :=
    PartialOrder.lift (ranksEquiv I) (ranksEquiv I).injective
  letI : SupSet I.PreMatching :=
    ⟨fun s => (ranksEquiv I).symm ((Finset.univ.filter (· ∈ s)).sup (ranksEquiv I))⟩
  completeLatticeOfSup I.PreMatching fun s => by
    refine ⟨fun ν hν => ?_, fun w hw => ?_⟩
    · change ranksEquiv I ν ≤ ranksEquiv I ((ranksEquiv I).symm _)
      rw [Equiv.apply_symm_apply]
      exact Finset.le_sup (f := ranksEquiv I) (Finset.mem_filter.2 ⟨Finset.mem_univ ν, hν⟩)
    · change ranksEquiv I ((ranksEquiv I).symm _) ≤ ranksEquiv I w
      rw [Equiv.apply_symm_apply]
      exact Finset.sup_le fun ν hν => hw (Finset.mem_filter.1 hν).2

theorem le_iff {ν ν' : I.PreMatching} :
    ν ≤ ν' ↔
      (∀ p, I.propOptRank p (ν'.propPartner p) ≤ I.propOptRank p (ν.propPartner p)) ∧
      (∀ r, I.recvOptRank r (ν.recvPartner r) ≤ I.recvOptRank r (ν'.recvPartner r)) :=
  Iff.rfl

end PreMatching

/-! ### Adachi's monotone operator -/

/-- Receivers willing to accept proposer `p` at pre-matching `ν`: those ranking `some p` at least as
well as `ν.recvPartner r`. -/
@[expose] def willingReceivers (ν : I.PreMatching) (p : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun r => I.recvOptRank r (some p) ≤ I.recvOptRank r (ν.recvPartner r)

/-- Proposers willing to accept receiver `r` at pre-matching `ν`: those ranking `some r` at least as
well as `ν.propPartner p`. -/
@[expose] def willingProposers (ν : I.PreMatching) (r : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun p => I.propOptRank p (some r) ≤ I.propOptRank p (ν.propPartner p)

/-- Proposer `p`'s best choice among `willingReceivers ν p`, or `none` if none are willing. -/
@[expose] def bestWillingReceiver (ν : I.PreMatching) (p : Fin n) : Option (Fin n) :=
  if h : (I.willingReceivers ν p).Nonempty then
    some (I.propPref p (((I.willingReceivers ν p).image (I.propRank p)).min' (h.image _)))
  else none

/-- Receiver `r`'s best choice among `willingProposers ν r`, or `none` if none are willing. -/
@[expose] def bestWillingProposer (ν : I.PreMatching) (r : Fin n) : Option (Fin n) :=
  if h : (I.willingProposers ν r).Nonempty then
    some (I.recvPref r (((I.willingProposers ν r).image (I.recvRank r)).min' (h.image _)))
  else none

private theorem bestWillingReceiver_mem {ν : I.PreMatching} {p r : Fin n}
    (h : I.bestWillingReceiver ν p = some r) : r ∈ I.willingReceivers ν p := by
  unfold bestWillingReceiver at h
  split_ifs at h with hne
  · injection h with hr
    obtain ⟨r', hr', hmin⟩ :=
      Finset.mem_image.1 (((I.willingReceivers ν p).image (I.propRank p)).min'_mem (hne.image _))
    rw [← hr, ← hmin, propPref_propRank]
    exact hr'

private theorem propOptRank_bestWillingReceiver_le {ν : I.PreMatching} {p r : Fin n}
    (hr : r ∈ I.willingReceivers ν p) :
    I.propOptRank p (I.bestWillingReceiver ν p) ≤ I.propOptRank p (some r) := by
  have hne : (I.willingReceivers ν p).Nonempty := ⟨r, hr⟩
  simp only [bestWillingReceiver, hne, ↓reduceDIte, propOptRank_some, propRank_propPref,
    Fin.castSucc_le_castSucc_iff]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hr)

private theorem bestWillingProposer_mem {ν : I.PreMatching} {r p : Fin n}
    (h : I.bestWillingProposer ν r = some p) : p ∈ I.willingProposers ν r := by
  unfold bestWillingProposer at h
  split_ifs at h with hne
  · injection h with hp
    obtain ⟨p', hp', hmin⟩ :=
      Finset.mem_image.1 (((I.willingProposers ν r).image (I.recvRank r)).min'_mem (hne.image _))
    have hpr : I.recvPref r (I.recvRank r p') = p' := (I.recvPref r).apply_symm_apply p'
    rw [← hp, ← hmin, hpr]
    exact hp'

private theorem recvOptRank_bestWillingProposer_le {ν : I.PreMatching} {r p : Fin n}
    (hp : p ∈ I.willingProposers ν r) :
    I.recvOptRank r (I.bestWillingProposer ν r) ≤ I.recvOptRank r (some p) := by
  have hne : (I.willingProposers ν r).Nonempty := ⟨p, hp⟩
  have hrp : ∀ k, I.recvRank r (I.recvPref r k) = k := (I.recvPref r).symm_apply_apply
  simp only [bestWillingProposer, hne, ↓reduceDIte, recvOptRank_some, hrp,
    Fin.castSucc_le_castSucc_iff]
  exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ hp)

/-- **Adachi's monotone pre-matching operator** ([Adachi2000]; [SchummerVohra2007], Section 10.4.1,
p. 260). -/
@[expose] def adachiMap : I.PreMatching →o I.PreMatching where
  toFun ν :=
    { propPartner := I.bestWillingReceiver ν
      recvPartner := I.bestWillingProposer ν }
  monotone' ν ν' hle := by
    rw [PreMatching.le_iff] at hle ⊢
    dsimp only
    refine ⟨fun p => ?_, fun r => ?_⟩
    · cases h : I.bestWillingReceiver ν p with
      | none =>
        rw [propOptRank_none]
        exact Fin.le_last _
      | some r =>
        have hr_mem : r ∈ I.willingReceivers ν p := I.bestWillingReceiver_mem h
        have hr_mem' : r ∈ I.willingReceivers ν' p := by
          simp only [willingReceivers, Finset.mem_filter, Finset.mem_univ, true_and] at hr_mem ⊢
          exact hr_mem.trans (hle.2 r)
        exact I.propOptRank_bestWillingReceiver_le hr_mem'
    · cases h : I.bestWillingProposer ν' r with
      | none =>
        rw [recvOptRank_none]
        exact Fin.le_last _
      | some p =>
        have hp_mem' : p ∈ I.willingProposers ν' r := I.bestWillingProposer_mem h
        have hp_mem : p ∈ I.willingProposers ν r := by
          simp only [willingProposers, Finset.mem_filter, Finset.mem_univ, true_and] at hp_mem' ⊢
          exact hp_mem'.trans (hle.1 p)
        exact I.recvOptRank_bestWillingProposer_le hp_mem

@[simp] theorem adachiMap_propPartner (ν : I.PreMatching) (p : Fin n) :
    (I.adachiMap ν).propPartner p = I.bestWillingReceiver ν p := rfl

@[simp] theorem adachiMap_recvPartner (ν : I.PreMatching) (r : Fin n) :
    (I.adachiMap ν).recvPartner r = I.bestWillingProposer ν r := rfl

/-! ### Fixed-point characterization of stable matchings (Theorem 10.14) -/

/-- For any one-to-one matching `μ`, its pre-matching `PreMatching.ofMatching I μ` is a fixed point
of `I.adachiMap` if and only if `μ` is stable ([Adachi2000]; [SchummerVohra2007], Section 10.4.1,
Theorem 10.14, p. 260). -/
theorem isFixedPt_ofMatching_iff (μ : Matching n) :
    Function.IsFixedPt I.adachiMap (PreMatching.ofMatching I μ) ↔ I.IsStable μ := by
  constructor
  · intro hfix p r ⟨hp, hr⟩
    have hr_will : r ∈ I.willingReceivers (PreMatching.ofMatching I μ) p := by
      simpa [willingReceivers, PreMatching.ofMatching] using hr.le
    have hle := I.propOptRank_bestWillingReceiver_le hr_will
    rw [← adachiMap_propPartner, congrFun (congrArg PreMatching.propPartner hfix) p,
      PreMatching.ofMatching, propOptRank_some, propOptRank_some, Fin.castSucc_le_castSucc_iff]
      at hle
    exact not_lt_of_ge hle hp
  · intro hstab
    refine PreMatching.ext (funext fun p => ?_) (funext fun r => ?_)
    · rw [adachiMap_propPartner]
      have hle1 := I.propOptRank_bestWillingReceiver_le (ν := PreMatching.ofMatching I μ) (p := p)
        (r := μ p) (by simp [willingReceivers, PreMatching.ofMatching])
      cases hbest : I.bestWillingReceiver (PreMatching.ofMatching I μ) p with
      | none =>
        rw [hbest, propOptRank_none, propOptRank_some] at hle1
        exact absurd (Fin.castSucc_lt_last (I.propRank p (μ p))) (not_lt_of_ge hle1)
      | some r =>
        have hr_will := I.bestWillingReceiver_mem hbest
        simp only [willingReceivers, PreMatching.ofMatching, Finset.mem_filter, Finset.mem_univ,
          true_and, recvOptRank_some, Fin.castSucc_le_castSucc_iff] at hr_will
        have hge : I.propRank p (μ p) ≤ I.propRank p r := by
          by_contra! hlt
          exact hstab p r ⟨hlt, lt_of_le_of_ne hr_will fun heq => (ne_of_lt hlt)
            (congrArg (I.propRank p) (by rw [I.recvRank_injective r heq, Equiv.apply_symm_apply]))⟩
        rw [hbest, propOptRank_some] at hle1
        simp only [PreMatching.ofMatching,
          I.propRank_injective p (le_antisymm (Fin.castSucc_le_castSucc_iff.1 hle1) hge)]
    · rw [adachiMap_recvPartner]
      have hle1 := I.recvOptRank_bestWillingProposer_le (ν := PreMatching.ofMatching I μ) (r := r)
        (p := μ.symm r) (by simp [willingProposers, PreMatching.ofMatching])
      cases hbest : I.bestWillingProposer (PreMatching.ofMatching I μ) r with
      | none =>
        rw [hbest, recvOptRank_none, recvOptRank_some] at hle1
        exact absurd (Fin.castSucc_lt_last (I.recvRank r (μ.symm r))) (not_lt_of_ge hle1)
      | some p =>
        have hp_will := I.bestWillingProposer_mem hbest
        simp only [willingProposers, PreMatching.ofMatching, Finset.mem_filter, Finset.mem_univ,
          true_and, propOptRank_some, Fin.castSucc_le_castSucc_iff] at hp_will
        have hge : I.recvRank r (μ.symm r) ≤ I.recvRank r p := by
          by_contra! hlt
          exact hstab p r ⟨lt_of_le_of_ne hp_will fun heq => (ne_of_lt hlt)
            (congrArg (I.recvRank r) (by rw [I.propRank_injective p heq, Equiv.symm_apply_apply])),
            hlt⟩
        rw [hbest, recvOptRank_some] at hle1
        simp only [PreMatching.ofMatching,
          I.recvRank_injective r (le_antisymm (Fin.castSucc_le_castSucc_iff.1 hle1) hge)]

private theorem fixedPt_mutual {ν : I.PreMatching} (hfix : Function.IsFixedPt I.adachiMap ν)
    (p r : Fin n) : ν.propPartner p = some r ↔ ν.recvPartner r = some p := by
  have hprop := congrFun (congrArg PreMatching.propPartner hfix) p
  have hrecv := congrFun (congrArg PreMatching.recvPartner hfix) r
  refine ⟨fun hp => ?_, fun hr => ?_⟩
  · have hr_will := I.bestWillingReceiver_mem (adachiMap_propPartner I ν p ▸ hprop.trans hp)
    simp only [willingReceivers, Finset.mem_filter, Finset.mem_univ, true_and] at hr_will
    have hle := I.recvOptRank_bestWillingProposer_le (ν := ν) (r := r) (p := p)
      (by rw [willingProposers, Finset.mem_filter]; simp [hp])
    rw [← adachiMap_recvPartner, hrecv] at hle
    exact (I.recvOptRank r).injective (le_antisymm hle hr_will)
  · have hp_will := I.bestWillingProposer_mem (adachiMap_recvPartner I ν r ▸ hrecv.trans hr)
    simp only [willingProposers, Finset.mem_filter, Finset.mem_univ, true_and] at hp_will
    have hle := I.propOptRank_bestWillingReceiver_le (ν := ν) (p := p) (r := r)
      (by rw [willingReceivers, Finset.mem_filter]; simp [hr])
    rw [← adachiMap_propPartner, hprop] at hle
    exact (I.propOptRank p).injective (le_antisymm hle hp_will)

/-- **Theorem 10.14** ([SchummerVohra2007], Section 10.4.1, p. 260; [Adachi2000]): a pre-matching
`ν` is a fixed point of `I.adachiMap` if and only if `ν = PreMatching.ofMatching I μ` for a stable
matching `μ`. -/
theorem isFixedPt_adachiMap_iff (ν : I.PreMatching) :
    Function.IsFixedPt I.adachiMap ν ↔
      ∃ μ : Matching n, I.IsStable μ ∧ ν = PreMatching.ofMatching I μ := by
  constructor
  · intro hfix
    have hprop_fix : ∀ p, I.bestWillingReceiver ν p = ν.propPartner p :=
      fun p => congrFun (congrArg PreMatching.propPartner hfix) p
    have hall_some : ∀ p : Fin n, ∃ r : Fin n, ν.propPartner p = some r := by
      intro p
      cases hp : ν.propPartner p with
      | some r => exact ⟨r, rfl⟩
      | none =>
        exfalso
        -- If every receiver r had some partner q_r, card image would force p to be matched.
        by_cases hall_recv : ∀ r : Fin n, ∃ q : Fin n, ν.recvPartner r = some q
        · choose g hg using hall_recv
          have hg_inj : Function.Injective g := by
            intro r₁ r₂ heq
            have h1 := (I.fixedPt_mutual hfix (g r₁) r₁).2 (hg r₁)
            have h2 := (I.fixedPt_mutual hfix (g r₁) r₂).2 (heq ▸ hg r₂)
            exact Option.some_injective _ (h1.symm.trans h2)
          obtain ⟨r₀, hr₀⟩ := (Finite.injective_iff_bijective.1 hg_inj).2 p
          have hp_some := (I.fixedPt_mutual hfix p r₀).2 (hr₀ ▸ hg r₀)
          rw [hp] at hp_some
          nomatch hp_some
        · push Not at hall_recv
          obtain ⟨r₀, hr₀⟩ := hall_recv
          have hr₀_none : ν.recvPartner r₀ = none := by
            cases hr : ν.recvPartner r₀ with
            | none => rfl
            | some q => exact False.elim (hr₀ q hr)
          have hr₀_will : r₀ ∈ I.willingReceivers ν p := by
            rw [willingReceivers, Finset.mem_filter]
            simp only [Finset.mem_univ, true_and, hr₀_none, recvOptRank_some, recvOptRank_none]
            exact (Fin.castSucc_lt_last _).le
          have hle := I.propOptRank_bestWillingReceiver_le hr₀_will
          rw [hprop_fix p, hp, propOptRank_none, propOptRank_some] at hle
          exact not_lt_of_ge hle (Fin.castSucc_lt_last _)
    choose f hf using hall_some
    have hf_inj : Function.Injective f := by
      intro p₁ p₂ heq
      have h1 := (I.fixedPt_mutual hfix p₁ (f p₁)).1 (hf p₁)
      have h2 := (I.fixedPt_mutual hfix p₂ (f p₁)).1 (heq ▸ hf p₂)
      exact Option.some_injective _ (h1.symm.trans h2)
    let μ : Matching n := permOfInjective f hf_inj
    have hν_eq : ν = PreMatching.ofMatching I μ := by
      refine PreMatching.ext (funext fun x => hf x) (funext fun x => ?_)
      simp only [PreMatching.ofMatching]
      have hx := hf (μ.symm x)
      have hμx : f (μ.symm x) = x := μ.apply_symm_apply x
      rw [hμx] at hx
      exact (I.fixedPt_mutual hfix (μ.symm x) x).1 hx
    refine ⟨μ, (I.isFixedPt_ofMatching_iff μ).1 (hν_eq ▸ hfix), hν_eq⟩
  · rintro ⟨μ, hstab, rfl⟩
    exact (I.isFixedPt_ofMatching_iff μ).2 hstab

/-- Order isomorphism between Tarski's fixed-point set `Function.fixedPoints I.adachiMap` and the
lattice `I.Stable` of stable matchings ([Adachi2000]; [SchummerVohra2007], Section 10.4.1,
Theorem 10.14, p. 260). -/
noncomputable def fixedPointsOrderIsoStable :
    Function.fixedPoints I.adachiMap ≃o I.Stable where
  toFun ν :=
    let h := (I.isFixedPt_adachiMap_iff ν.val).1 ν.property
    ⟨Classical.choose h, (Classical.choose_spec h).1⟩
  invFun μ :=
    ⟨PreMatching.ofMatching I μ.val, (I.isFixedPt_ofMatching_iff μ.val).2 μ.property⟩
  left_inv ν := by
    apply Subtype.ext
    exact (Classical.choose_spec ((I.isFixedPt_adachiMap_iff ν.val).1 ν.property)).2.symm
  right_inv μ := by
    apply Subtype.ext
    apply PreMatching.ofMatching_injective
    exact (Classical.choose_spec
      ((I.isFixedPt_adachiMap_iff (PreMatching.ofMatching I μ.val)).1
        ((I.isFixedPt_ofMatching_iff μ.val).2 μ.property))).2.symm
  map_rel_iff' {ν₁ ν₂} := by
    set h₁ := (I.isFixedPt_adachiMap_iff ν₁.val).1 ν₁.property
    set h₂ := (I.isFixedPt_adachiMap_iff ν₂.val).1 ν₂.property
    set μ₁ : Matching n := Classical.choose h₁
    set μ₂ : Matching n := Classical.choose h₂
    have hν₁ : ν₁.val = PreMatching.ofMatching I μ₁ := (Classical.choose_spec h₁).2
    have hν₂ : ν₂.val = PreMatching.ofMatching I μ₂ := (Classical.choose_spec h₂).2
    have hstab₁ : I.IsStable μ₁ := (Classical.choose_spec h₁).1
    change (∀ p, I.propRank p (μ₂ p) ≤ I.propRank p (μ₁ p)) ↔ ν₁.val ≤ ν₂.val
    rw [hν₁, hν₂, PreMatching.le_iff]
    simp only [PreMatching.ofMatching, propOptRank_some, recvOptRank_some,
      Fin.castSucc_le_castSucc_iff]
    exact ⟨fun h => ⟨h, I.recvRank_le_of_propRank_le hstab₁ h⟩, fun h => h.1⟩

/-- Tarski's greatest fixed point `I.adachiMap.gfp` is the proposer-optimal deferred-acceptance
matching ([Adachi2000]; [SchummerVohra2007], Section 10.4.1, Theorem 10.14, p. 260). -/
theorem adachiMap_gfp :
    I.adachiMap.gfp = PreMatching.ofMatching I I.deferredAcceptance := by
  obtain ⟨μ, hstab, h_eq⟩ := (I.isFixedPt_adachiMap_iff I.adachiMap.gfp).1
    I.adachiMap.isGreatest_gfp.1
  have hp : ∀ p, I.propRank p (I.deferredAcceptance p) ≤ I.propRank p (μ p) :=
    fun p => I.propRank_deferredAcceptance_le hstab p
  refine h_eq.trans (le_antisymm ?_ (h_eq ▸ I.adachiMap.isGreatest_gfp.2
    ((I.isFixedPt_ofMatching_iff _).2 I.isStable_deferredAcceptance)))
  rw [PreMatching.le_iff]
  simpa [PreMatching.ofMatching] using ⟨hp, I.recvRank_le_of_propRank_le hstab hp⟩

/-- Tarski's least fixed point `I.adachiMap.lfp` is the receiver-optimal deferred-acceptance
matching ([Adachi2000]; [SchummerVohra2007], Section 10.4.1, Theorem 10.14, p. 260). -/
theorem adachiMap_lfp :
    I.adachiMap.lfp = PreMatching.ofMatching I I.receiverDeferredAcceptance := by
  obtain ⟨μ, hstab, h_eq⟩ := (I.isFixedPt_adachiMap_iff I.adachiMap.lfp).1
    I.adachiMap.isLeast_lfp.1
  have hp : ∀ p, I.propRank p (μ p) ≤ I.propRank p (I.receiverDeferredAcceptance p) :=
    fun p => I.isProposerPessimal_receiverDeferredAcceptance.2 μ hstab p
  refine h_eq.trans (le_antisymm (h_eq ▸ I.adachiMap.isLeast_lfp.2
    ((I.isFixedPt_ofMatching_iff _).2 I.isStable_receiverDeferredAcceptance)) ?_)
  rw [PreMatching.le_iff]
  simpa [PreMatching.ofMatching] using
    ⟨hp, I.recvRank_le_of_propRank_le I.isStable_receiverDeferredAcceptance hp⟩

end Instance

end Cslib.Algorithms.Lean.StableMatching
