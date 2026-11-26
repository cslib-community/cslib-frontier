/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Card
import CslibFrontier.Algorithms.Lean.StableMatching.Incomplete.RuralHospitals
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Many-to-one Hospitals–Residents markets and Roth's Rural Hospitals Theorem

In the **Hospitals–Residents** (or **college admissions**) model ([GaleShapley1962]; [Roth1986];
[RothSotomayor1990]; see also [SchummerVohra2007], Section 10.4.3, p. 261 for the quota-extension
background), `m` residents indexed by `Fin m` apply to `n` hospitals indexed by `Fin n`, where
hospital `h` can admit up to `I.quota h` residents. Preferences are strict and possibly incomplete
lists (`I.resPref r` and `I.hospPref h`), and hospital preferences over sets of residents are
responsive to their strict ranking of individual residents via individual acceptability, quota
bounds, and pairwise blocking: a resident–hospital pair `(r, h)` blocks a matching `M` when `r`
strictly prefers `h` to its assigned outcome `M.hospital r`, `h` finds `r` acceptable, and either
`h` has an unfilled seat (`(M.residents h).card < I.quota h`) or `h` strictly prefers `r` to some
currently assigned resident `r' ∈ M.residents h`.

Via a computable seat-cloning reduction to `IncompleteInstance` (kept internal to the proofs and
algorithm implementation so all public statements speak purely in terms of `ManyToOneInstance` and
`ManyToOneMatching`), we construct resident-proposing `ManyToOneInstance.deferredAcceptance`, prove
its stability and resident-optimality, and establish **Roth's (1986) Rural Hospitals Theorem**:

1. Every stable matching matches the exact same set of residents
   (`matchedResidents_eq_of_isStable`, `unmatchedResidents_eq_of_isStable`).
2. Every hospital fills the exact same number of positions across all stable matchings
   (`card_residents_eq_of_isStable`).
3. Every hospital that fails to fill its quota in some stable matching is assigned the **exact same
   set of residents** in every stable matching (`residents_eq_of_card_lt_quota`).

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.ManyToOneInstance`: Hospitals–Residents market with strict,
  possibly incomplete preference lists and hospital quotas.
* `Cslib.Algorithms.Lean.StableMatching.ManyToOneMatching`: assignment
  `hospital : Fin m → Option (Fin n)` with named accessors `residents` and `matchedResidents`.
* `ManyToOneInstance.IsFeasible`, `ManyToOneInstance.IsIndividuallyRational`,
  `ManyToOneInstance.IsBlockingPair`, `ManyToOneInstance.IsStable`: feasibility, acceptability,
  blocking pairs, and stability.
* `ManyToOneInstance.deferredAcceptance`: computable resident-proposing deferred acceptance.

## Main results

* `ManyToOneInstance.isStable_deferredAcceptance`, `ManyToOneInstance.exists_isStable`: existence of
  a stable many-to-one matching ([GaleShapley1962]; [RothSotomayor1990]).
* `ManyToOneInstance.resRank_deferredAcceptance_le_of_isStable`: resident-optimality of resident-
  proposing deferred acceptance ([RothSotomayor1990]).
* `ManyToOneInstance.matchedResidents_eq_of_isStable`,
  `ManyToOneInstance.card_residents_eq_of_isStable`: equal matched residents and hospital headcounts
  across all stable matchings ([Roth1986]; [RothSotomayor1990]).
* `ManyToOneInstance.residents_eq_of_card_lt_quota`: **Rural Hospitals Theorem** ([Roth1986];
  [RothSotomayor1990]): any hospital with unfilled capacity receives the exact same set of residents
  in every stable matching.

## References

* [GaleShapley1962] (primary PDF unverified)
* [Roth1986] (primary PDF unverified)
* [RothSotomayor1990] (primary PDF unverified)
* [SchummerVohra2007], Section 10.4.3, p. 261 (college-admissions quota model background)
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching

/-- A many-to-one **Hospitals–Residents** market with `m` residents (`Fin m`) and `n` hospitals
(`Fin n`). Each agent lists acceptable partners on the other side from most to least preferred, and
hospital `h` has capacity `quota h`. -/
structure ManyToOneInstance (m n : ℕ) where
  /-- Acceptable hospitals for resident `r`, from most to least preferred. -/
  resPref : Fin m → List (Fin n)
  /-- Acceptable residents for hospital `h`, from most to least preferred. -/
  hospPref : Fin n → List (Fin m)
  /-- Maximum number of residents that hospital `h` can admit. -/
  quota : Fin n → ℕ

/-- A many-to-one assignment assigning each resident `r` an optional hospital `M.hospital r`. -/
@[ext]
structure ManyToOneMatching (m n : ℕ) where
  /-- Hospital assigned to resident `r`, or `none` if `r` remains unmatched. -/
  hospital : Fin m → Option (Fin n)

instance {m n : ℕ} : DecidableEq (ManyToOneMatching m n) :=
  fun M M' => decidable_of_iff (M.hospital = M'.hospital)
    ⟨ManyToOneMatching.ext, congrArg ManyToOneMatching.hospital⟩

namespace ManyToOneMatching

variable {m n : ℕ}

/-- Set of residents assigned to hospital `h` under `M`. -/
@[expose] def residents (M : ManyToOneMatching m n) (h : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun r => M.hospital r = some h

/-- Set of residents matched to some hospital under `M`. -/
@[expose] def matchedResidents (M : ManyToOneMatching m n) : Finset (Fin m) :=
  Finset.univ.filter fun r => (M.hospital r).isSome

@[simp] theorem mem_residents {M : ManyToOneMatching m n} {h : Fin n} {r : Fin m} :
    r ∈ M.residents h ↔ M.hospital r = some h := by
  simp [residents]

@[simp] theorem mem_matchedResidents {M : ManyToOneMatching m n} {r : Fin m} :
    r ∈ M.matchedResidents ↔ (M.hospital r).isSome := by
  simp [matchedResidents]

end ManyToOneMatching

namespace ManyToOneInstance

variable {m n : ℕ} (I : ManyToOneInstance m n)

/-! ### Ranks, feasibility, and stability -/

/-- Rank of outcome `o : Option (Fin n)` for resident `r` (`0` is favourite; `none` or an
unacceptable hospital has rank `(I.resPref r).length`). -/
@[expose] def resRank (r : Fin m) (o : Option (Fin n)) : ℕ :=
  match o with
  | some h => (I.resPref r).idxOf h
  | none => (I.resPref r).length

/-- Rank of resident `r` in hospital `h`'s preference list (`(I.hospPref h).length` if
unacceptable). -/
@[expose] def hospRank (h : Fin n) (r : Fin m) : ℕ :=
  (I.hospPref h).idxOf r

@[simp] theorem resRank_some (r : Fin m) (h : Fin n) :
    I.resRank r (some h) = (I.resPref r).idxOf h := rfl

@[simp] theorem resRank_none (r : Fin m) :
    I.resRank r none = (I.resPref r).length := rfl

theorem resRank_le_resRank_none (r : Fin m) (o : Option (Fin n)) :
    I.resRank r o ≤ I.resRank r none := by
  cases o with
  | none => exact le_rfl
  | some _ => exact List.idxOf_le_length

theorem resRank_some_lt_none_iff (r : Fin m) (h : Fin n) :
    I.resRank r (some h) < I.resRank r none ↔ h ∈ I.resPref r :=
  List.idxOf_lt_length_iff

theorem eq_of_resRank_eq {r : Fin m} {h : Fin n} (hh : h ∈ I.resPref r) {o : Option (Fin n)}
    (heq : I.resRank r (some h) = I.resRank r o) : o = some h := by
  cases o with
  | none =>
    have := (I.resRank_some_lt_none_iff r h).2 hh
    omega
  | some h' => exact congrArg some ((List.idxOf_inj hh).1 heq).symm

/-- `M` is feasible when every hospital admits at most its quota of residents. -/
@[expose] def IsFeasible (M : ManyToOneMatching m n) : Prop :=
  ∀ h : Fin n, (M.residents h).card ≤ I.quota h

/-- `M` is individually rational when every assigned pair `(r, h)` is mutually acceptable. -/
@[expose] def IsIndividuallyRational (M : ManyToOneMatching m n) : Prop :=
  ∀ r h, M.hospital r = some h → h ∈ I.resPref r ∧ r ∈ I.hospPref h

/-- Resident `r` and hospital `h` form a **blocking pair** for `M` ([Roth1986];
[RothSotomayor1990]) when `r` strictly prefers `h` to `M.hospital r`, `h` finds `r` acceptable, and
either `h` has an unfilled position or `h` strictly prefers `r` to some resident currently in
`M.residents h`. -/
@[expose] def IsBlockingPair (M : ManyToOneMatching m n) (r : Fin m) (h : Fin n) : Prop :=
  I.resRank r (some h) < I.resRank r (M.hospital r) ∧
  r ∈ I.hospPref h ∧
  ((M.residents h).card < I.quota h ∨ ∃ r' ∈ M.residents h, I.hospRank h r < I.hospRank h r')

/-- `M` is **stable** when it is feasible, individually rational, and admits no blocking pair. -/
@[expose] def IsStable (M : ManyToOneMatching m n) : Prop :=
  I.IsFeasible M ∧ I.IsIndividuallyRational M ∧ ∀ r h, ¬ I.IsBlockingPair M r h

/-- `M` is **resident-optimal** when it is stable and every resident weakly prefers `M.hospital r`
to its outcome in every stable matching. -/
@[expose] def IsResidentOptimal (M : ManyToOneMatching m n) : Prop :=
  I.IsStable M ∧ ∀ M', I.IsStable M' → ∀ r, I.resRank r (M.hospital r) ≤ I.resRank r (M'.hospital r)

instance (M : ManyToOneMatching m n) : Decidable (I.IsFeasible M) :=
  inferInstanceAs (Decidable (∀ _, _))

instance (M : ManyToOneMatching m n) : Decidable (I.IsIndividuallyRational M) :=
  inferInstanceAs (Decidable (∀ _ _, _))

instance (M : ManyToOneMatching m n) (r : Fin m) (h : Fin n) :
    Decidable (I.IsBlockingPair M r h) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

instance (M : ManyToOneMatching m n) : Decidable (I.IsStable M) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-! ### Seat-cloning reduction to `IncompleteInstance` -/

/-- Maximum hospital quota, computed over `List.finRange n` so kernel reduction is fast. -/
private def maxQuota : ℕ :=
  ((List.finRange n).map I.quota).foldr max 0

private theorem le_foldr_max : ∀ {l : List ℕ} {a : ℕ}, a ∈ l → a ≤ l.foldr max 0
  | [], _, h => nomatch h
  | _ :: _, _, h => by
    rcases List.mem_cons.1 h with rfl | hmem
    · exact Nat.le_max_left _ _
    · exact (le_foldr_max hmem).trans (Nat.le_max_right _ _)

private theorem quota_le_maxQuota (h : Fin n) : I.quota h ≤ I.maxQuota :=
  le_foldr_max (List.mem_map_of_mem (List.mem_finRange h))

/-- Active cloned seat `j : Fin (I.quota h)` of hospital `h` in `Fin (n * I.maxQuota)`. -/
private def seat (h : Fin n) (j : Fin (I.quota h)) : Fin (n * I.maxQuota) :=
  finProdFinEquiv (h, ⟨j.val, Nat.lt_of_lt_of_le j.isLt (I.quota_le_maxQuota h)⟩)

private theorem seat_symm (h : Fin n) (j : Fin (I.quota h)) :
    finProdFinEquiv.symm (I.seat h j) =
      (h, ⟨j.val, Nat.lt_of_lt_of_le j.isLt (I.quota_le_maxQuota h)⟩) := by
  unfold seat
  exact finProdFinEquiv.symm_apply_apply _

private theorem seat_symm_fst (h : Fin n) (j : Fin (I.quota h)) :
    (finProdFinEquiv.symm (I.seat h j)).fst = h := by
  rw [seat_symm]

private theorem seat_symm_snd_val (h : Fin n) (j : Fin (I.quota h)) :
    (finProdFinEquiv.symm (I.seat h j)).snd.val = j.val := by
  rw [seat_symm]

private theorem seat_inj_same {h : Fin n} {j₁ j₂ : Fin (I.quota h)}
    (heq : I.seat h j₁ = I.seat h j₂) : j₁ = j₂ := by
  have hsnd := congrArg (fun s => (finProdFinEquiv.symm s).snd.val) heq
  simp only [seat_symm_snd_val] at hsnd
  exact Fin.ext hsnd

private theorem eq_seat_of_lt_quota (s : Fin (n * I.maxQuota)) {h : Fin n}
    (hfst : (finProdFinEquiv.symm s).fst = h)
    (hk : (finProdFinEquiv.symm s).snd.val < I.quota h) :
    s = I.seat h ⟨(finProdFinEquiv.symm s).snd.val, hk⟩ := by
  apply finProdFinEquiv.symm.injective
  rw [seat_symm]
  exact Prod.ext hfst (Fin.ext rfl)

/-- Ordered list of active seats of hospital `h`. -/
private def seats (h : Fin n) : List (Fin (n * I.maxQuota)) :=
  (List.finRange (I.quota h)).map (I.seat h)

private theorem length_seats (h : Fin n) : (I.seats h).length = I.quota h := by
  simp [seats]

private theorem mem_seats_iff {h : Fin n} {s : Fin (n * I.maxQuota)} :
    s ∈ I.seats h ↔ ∃ j : Fin (I.quota h), I.seat h j = s := by
  simp [seats]

private theorem idxOf_seats (h : Fin n) (j : Fin (I.quota h)) :
    (I.seats h).idxOf (I.seat h j) = j.val := by
  have hlt := List.idxOf_lt_length_iff.2 (I.mem_seats_iff.2 ⟨j, rfl⟩)
  have hget : (I.seats h)[(I.seats h).idxOf (I.seat h j)] = I.seat h j := List.getElem_idxOf hlt
  simp only [seats, List.getElem_map, List.getElem_finRange] at hget
  exact congrArg Fin.val (I.seat_inj_same hget)

/-- Cloned one-to-one `IncompleteInstance` associated to `I`. -/
private def cloneInstance : IncompleteInstance m (n * I.maxQuota) where
  propPref r := (I.resPref r).flatMap I.seats
  recvPref s :=
    let p := finProdFinEquiv.symm s
    if p.snd.val < I.quota p.fst then I.hospPref p.fst else []

private theorem mem_clone_propPref_iff {r : Fin m} {s : Fin (n * I.maxQuota)} :
    s ∈ I.cloneInstance.propPref r ↔
      (finProdFinEquiv.symm s).fst ∈ I.resPref r ∧
        (finProdFinEquiv.symm s).snd.val < I.quota (finProdFinEquiv.symm s).fst := by
  simp only [cloneInstance, List.mem_flatMap, mem_seats_iff]
  refine ⟨?_, fun ⟨hh, hk⟩ => ⟨_, hh, ⟨_, hk⟩, (I.eq_seat_of_lt_quota s rfl hk).symm⟩⟩
  rintro ⟨h, hh, j, rfl⟩
  rw [seat_symm_fst, seat_symm_snd_val]
  exact ⟨hh, j.isLt⟩

private theorem mem_clone_recvPref_iff {s : Fin (n * I.maxQuota)} {r : Fin m} :
    r ∈ I.cloneInstance.recvPref s ↔
      (finProdFinEquiv.symm s).snd.val < I.quota (finProdFinEquiv.symm s).fst ∧
        r ∈ I.hospPref (finProdFinEquiv.symm s).fst := by
  dsimp only [cloneInstance]
  split_ifs with hk <;> simp only [hk, true_and, false_and, List.not_mem_nil]

private theorem clone_recvRank_seat_some (h : Fin n) (j : Fin (I.quota h)) (r : Fin m) :
    I.cloneInstance.recvRank (I.seat h j) (some r) = I.hospRank h r := by
  simp only [IncompleteInstance.recvRank_some, cloneInstance, seat_symm_fst, seat_symm_snd_val,
    j.isLt, ↓reduceIte, hospRank]

private theorem idxOf_flatMap_seat {L : List (Fin n)} {h : Fin n} (hh : h ∈ L)
    (j : Fin (I.quota h)) :
    (L.flatMap I.seats).idxOf (I.seat h j) =
      ((L.take (L.idxOf h)).flatMap I.seats).length + j.val := by
  set i := L.idxOf h
  have hi_lt : i < L.length := List.idxOf_lt_length_iff.2 hh
  have hnot_mem : I.seat h j ∉ (L.take i).flatMap I.seats := by
    rintro hmem
    obtain ⟨x, hx_take, jx, hjx⟩ := by simpa only [List.mem_flatMap, mem_seats_iff] using hmem
    obtain rfl : x = h := by
      simpa only [seat_symm_fst] using congrArg (fun s => (finProdFinEquiv.symm s).fst) hjx
    obtain ⟨k, hk_lt, hk_eq⟩ := List.mem_take_iff_getElem.1 hx_take
    exact Bool.eq_false_iff.1
      (List.not_of_lt_findIdx (p := (· == x)) (lt_of_lt_of_le hk_lt (Nat.min_le_left _ _)))
      (beq_iff_eq.2 hk_eq)
  have hsplit : L = L.take i ++ h :: L.drop (i + 1) :=
    calc L = L.take i ++ L.drop i := (List.take_append_drop i L).symm
      _ = L.take i ++ L[i] :: L.drop (i + 1) := by rw [List.drop_eq_getElem_cons hi_lt]
      _ = L.take i ++ h :: L.drop (i + 1) := by rw [List.getElem_idxOf hi_lt]
  conv_lhs => rw [hsplit]
  rw [List.flatMap_append, List.flatMap_cons, List.idxOf_append, ite_eq_right hnot_mem,
    List.idxOf_append, ite_eq_left (I.mem_seats_iff.2 ⟨j, rfl⟩), I.idxOf_seats h j, Nat.add_comm]

private theorem length_take_flatMap_add_quota_le (L : List (Fin n)) {i₁ i₂ : ℕ}
    (hlt : i₁ < i₂) (hi₁ : i₁ < L.length) :
    ((L.take i₁).flatMap I.seats).length + I.quota L[i₁] ≤
      ((L.take i₂).flatMap I.seats).length := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le (Nat.succ_le_of_lt hlt)
  rw [List.take_add, List.take_succ_eq_append_getElem hi₁]
  simp only [List.flatMap_append, List.length_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, length_seats]
  omega

private theorem clone_propRank_seat_lt_same {r : Fin m} {h : Fin n} (hh : h ∈ I.resPref r)
    {j₁ j₂ : Fin (I.quota h)} (hj : j₁ < j₂) :
    I.cloneInstance.propRank r (some (I.seat h j₁)) <
      I.cloneInstance.propRank r (some (I.seat h j₂)) := by
  simp only [IncompleteInstance.propRank_some, cloneInstance, I.idxOf_flatMap_seat hh]
  exact Nat.add_lt_add_left hj _

private theorem clone_propRank_seat_lt_of_resRank_lt {r : Fin m} {h₁ h₂ : Fin n}
    (hlt : I.resRank r (some h₁) < I.resRank r (some h₂))
    (j₁ : Fin (I.quota h₁)) (j₂ : Fin (I.quota h₂)) :
    I.cloneInstance.propRank r (some (I.seat h₁ j₁)) <
      I.cloneInstance.propRank r (some (I.seat h₂ j₂)) := by
  have hh₁ : h₁ ∈ I.resPref r :=
    (I.resRank_some_lt_none_iff r h₁).1 (lt_of_lt_of_le hlt (I.resRank_le_resRank_none r _))
  by_cases hh₂ : h₂ ∈ I.resPref r
  · simp only [IncompleteInstance.propRank_some, cloneInstance, I.idxOf_flatMap_seat hh₁,
      I.idxOf_flatMap_seat hh₂]
    have hi₁ : (I.resPref r).idxOf h₁ < (I.resPref r).length := List.idxOf_lt_length_iff.2 hh₁
    dsimp only [resRank] at hlt
    have hstep := I.length_take_flatMap_add_quota_le (I.resPref r) hlt hi₁
    rw [List.getElem_idxOf hi₁] at hstep
    have := j₁.isLt
    omega
  · have h1 : I.cloneInstance.propRank r (some (I.seat h₁ j₁)) < I.cloneInstance.propRank r none :=
      (I.cloneInstance.propRank_some_lt_none_iff r _).2 <| by
        rw [mem_clone_propPref_iff, seat_symm_fst, seat_symm_snd_val]
        exact ⟨hh₁, j₁.isLt⟩
    have h2 : I.cloneInstance.propRank r (some (I.seat h₂ j₂)) =
        I.cloneInstance.propRank r none := List.idxOf_eq_length_iff.2 <| by
      rw [mem_clone_propPref_iff, seat_symm_fst]
      exact fun h => hh₂ h.1
    omega

/-- Project a cloned one-to-one partial matching down to a many-to-one matching. -/
private def projectClone (μ : PartialMatching m (n * I.maxQuota)) : ManyToOneMatching m n where
  hospital r := (μ r).map (fun s => (finProdFinEquiv.symm s).fst)

private theorem matchedResidents_projectClone (μ : PartialMatching m (n * I.maxQuota)) :
    (I.projectClone μ).matchedResidents = PartialMatching.matchedProposers μ := by
  ext r
  simp [projectClone, PartialMatching.matchedProposers]

private theorem isSome_of_mem_residents_projectClone {μ : PartialMatching m (n * I.maxQuota)}
    {h : Fin n} {r : Fin m} (hr : r ∈ (I.projectClone μ).residents h) : (μ r).isSome := by
  obtain ⟨s, hs, -⟩ := Option.map_eq_some_iff.1 (ManyToOneMatching.mem_residents.1 hr)
  simp [hs]

private theorem card_residents_projectClone (μ : PartialMatching m (n * I.maxQuota)) (h : Fin n) :
    ((I.projectClone μ).residents h).card =
      ((PartialMatching.matchedReceivers μ).filter
        (fun s => (finProdFinEquiv.symm s).fst = h)).card := by
  refine Finset.card_bij (fun r hr => (μ r).get (I.isSome_of_mem_residents_projectClone hr))
    (fun r hr => ?_) (fun r₁ hr₁ r₂ hr₂ heq => ?_) (fun s hs => ?_)
  · obtain ⟨s, hs, hfst⟩ := Option.map_eq_some_iff.1 (ManyToOneMatching.mem_residents.1 hr)
    simp only [Finset.mem_filter, PartialMatching.mem_matchedReceivers,
      Option.get_of_eq_some _ hs, μ.eq_some_iff.2 hs, Option.isSome_some, hfst, and_self]
  · exact μ.inj (Option.some_get _).symm
      (heq ▸ (Option.some_get (I.isSome_of_mem_residents_projectClone hr₂)).symm)
  · simp only [Finset.mem_filter, PartialMatching.mem_matchedReceivers] at hs
    obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hs.1
    have hμr : μ r = some s := μ.eq_some_iff.1 hr
    exact ⟨r, ManyToOneMatching.mem_residents.2
      (by simp only [projectClone, hμr, Option.map_some, hs.2]),
      by simp only [hμr, Option.get_some]⟩

private theorem isStable_projectClone {μ : PartialMatching m (n * I.maxQuota)}
    (hμ : I.cloneInstance.IsStable μ) : I.IsStable (I.projectClone μ) := by
  rcases hμ with ⟨hμ_ir, hμ_nb⟩
  have hfeas : I.IsFeasible (I.projectClone μ) := fun h => by
    rw [I.card_residents_projectClone μ h]
    let S := (PartialMatching.matchedReceivers μ).filter
      fun s => (finProdFinEquiv.symm s).fst = h
    have hsub : S ⊆ Finset.univ.image (I.seat h) := fun s hs => by
      simp only [S, Finset.mem_filter, PartialMatching.mem_matchedReceivers] at hs
      obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 hs.1
      have hk := (I.mem_clone_recvPref_iff.1 (hμ_ir r s (μ.eq_some_iff.1 hr)).2).1
      exact Finset.mem_image.2 ⟨⟨_, hs.2 ▸ hk⟩, Finset.mem_univ _,
        (I.eq_seat_of_lt_quota s hs.2 (hs.2 ▸ hk)).symm⟩
    calc
      S.card ≤ (Finset.univ.image (I.seat h)).card := Finset.card_le_card hsub
      _ ≤ (Finset.univ : Finset (Fin (I.quota h))).card := Finset.card_image_le
      _ = I.quota h := Fintype.card_fin _
  have hir : I.IsIndividuallyRational (I.projectClone μ) := fun r h hr => by
    obtain ⟨s, hs, rfl⟩ := Option.map_eq_some_iff.1 hr
    exact ⟨(I.mem_clone_propPref_iff.1 (hμ_ir r s hs).1).1,
      (I.mem_clone_recvPref_iff.1 (hμ_ir r s hs).2).2⟩
  refine ⟨hfeas, hir, fun r h ⟨hres_lt, hr_hosp, hcap_or⟩ => ?_⟩
  have hh_res : h ∈ I.resPref r :=
    (I.resRank_some_lt_none_iff r h).1 (lt_of_lt_of_le hres_lt (I.resRank_le_resRank_none r _))
  -- Helper: any active seat `I.seat h j` is strictly preferred by `r` to `μ r` in `cloneInstance`.
  have hprop_seat (j : Fin (I.quota h)) :
      I.cloneInstance.propRank r (some (I.seat h j)) < I.cloneInstance.propRank r (μ r) := by
    cases hμr : μ r with
    | none =>
      rw [I.cloneInstance.propRank_some_lt_none_iff, mem_clone_propPref_iff, seat_symm_fst,
        seat_symm_snd_val]
      exact ⟨hh_res, j.isLt⟩
    | some s' =>
      have hk' := (I.mem_clone_recvPref_iff.1 (hμ_ir r s' hμr).2).1
      rw [I.eq_seat_of_lt_quota s' rfl hk']
      exact I.clone_propRank_seat_lt_of_resRank_lt
        (by simpa only [projectClone, hμr, Option.map_some] using hres_lt) j ⟨_, hk'⟩
  rcases hcap_or with hlt_cap | ⟨r', hr'_mem, hr'_rank⟩
  · -- Some active seat of `h` is unmatched in `μ`.
    have hcard_S : ((PartialMatching.matchedReceivers μ).filter
        (fun s => (finProdFinEquiv.symm s).fst = h)).card <
        (Finset.univ.image (I.seat h)).card := by
      rwa [Finset.card_image_of_injective _ fun _ _ => I.seat_inj_same, Finset.card_univ,
        Fintype.card_fin, ← I.card_residents_projectClone μ h]
    obtain ⟨s, hs_img, hs_not_S⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard_S
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hs_img
    have hs_none : μ.symm (I.seat h j) = none := by
      simpa only [Finset.mem_filter, PartialMatching.mem_matchedReceivers,
        I.seat_symm_fst h j, and_true, Option.not_isSome_iff_eq_none] using hs_not_S
    refine hμ_nb r (I.seat h j) ⟨hprop_seat j, ?_⟩
    rw [hs_none, I.cloneInstance.recvRank_some_lt_none_iff, mem_clone_recvPref_iff,
      seat_symm_fst, seat_symm_snd_val]
    exact ⟨j.isLt, hr_hosp⟩
  · -- Seat of `r'` in `h` prefers `r` to `r'`.
    obtain ⟨s, hs, hfst⟩ := Option.map_eq_some_iff.1 (ManyToOneMatching.mem_residents.1 hr'_mem)
    have hk : (finProdFinEquiv.symm s).snd.val < I.quota h :=
      hfst ▸ (I.mem_clone_recvPref_iff.1 (hμ_ir r' s hs).2).1
    let j : Fin (I.quota h) := ⟨(finProdFinEquiv.symm s).snd.val, hk⟩
    refine hμ_nb r (I.seat h j) ⟨hprop_seat j, ?_⟩
    rw [μ.eq_some_iff.2 (I.eq_seat_of_lt_quota s hfst hk ▸ hs),
      I.clone_recvRank_seat_some, I.clone_recvRank_seat_some]
    exact hr'_rank

/-! ### Lifting a stable `ManyToOneMatching` to `cloneInstance` -/

/-- Number of residents in `M.residents h` strictly preferred by `h` to `r`. -/
private def hospPos (M : ManyToOneMatching m n) (h : Fin n) (r : Fin m) : ℕ :=
  ((M.residents h).filter fun r' => I.hospRank h r' < I.hospRank h r).card

private theorem hospPos_lt_card {M : ManyToOneMatching m n} {h : Fin n} {r : Fin m}
    (hr : r ∈ M.residents h) : I.hospPos M h r < (M.residents h).card :=
  Finset.card_lt_card ⟨Finset.filter_subset _ _, fun hsub => by simpa using hsub hr⟩

private theorem hospPos_strictMono {M : ManyToOneMatching m n} {h : Fin n} {r₁ r₂ : Fin m}
    (hr₁ : r₁ ∈ M.residents h) (hlt : I.hospRank h r₁ < I.hospRank h r₂) :
    I.hospPos M h r₁ < I.hospPos M h r₂ := by
  refine Finset.card_lt_card ⟨fun _ hx => ?_,
    fun hsub => by simpa using hsub (Finset.mem_filter.2 ⟨hr₁, hlt⟩)⟩
  simp only [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hx.2.trans hlt⟩

private theorem hospPos_injOn {M : ManyToOneMatching m n} (hir : I.IsIndividuallyRational M)
    (h : Fin n) {r₁ r₂ : Fin m} (hr₁ : r₁ ∈ M.residents h) (hr₂ : r₂ ∈ M.residents h)
    (heq : I.hospPos M h r₁ = I.hospPos M h r₂) : r₁ = r₂ := by
  by_contra hne
  have hacc₁ : r₁ ∈ I.hospPref h := (hir r₁ h (ManyToOneMatching.mem_residents.1 hr₁)).2
  rcases lt_or_gt_of_ne (fun hrk => hne ((List.idxOf_inj hacc₁).1 hrk)) with hlt | hgt
  · exact (I.hospPos_strictMono hr₁ hlt).ne heq
  · exact (I.hospPos_strictMono hr₂ hgt).ne' heq

private theorem exists_hospPos_eq {M : ManyToOneMatching m n} (hir : I.IsIndividuallyRational M)
    (h : Fin n) {k : ℕ} (hk : k < (M.residents h).card) :
    ∃ r' ∈ M.residents h, I.hospPos M h r' = k := by
  have himg_eq : (M.residents h).image (I.hospPos M h) = Finset.range (M.residents h).card :=
    Finset.eq_of_subset_of_card_le
      (fun _ hx => by obtain ⟨r', hr', rfl⟩ := Finset.mem_image.1 hx
                      exact Finset.mem_range.2 (I.hospPos_lt_card hr'))
      (by rw [Finset.card_range,
            Finset.card_image_of_injOn fun _ h₁ _ h₂ => I.hospPos_injOn hir h h₁ h₂])
  exact Finset.mem_image.1 (himg_eq ▸ Finset.mem_range.2 hk)

private def liftCloneFun {M : ManyToOneMatching m n} (hfeas : I.IsFeasible M) (r : Fin m) :
    Option (Fin (n * I.maxQuota)) :=
  match hMr : M.hospital r with
  | none => none
  | some h =>
    some (I.seat h ⟨I.hospPos M h r,
      Nat.lt_of_lt_of_le (I.hospPos_lt_card (ManyToOneMatching.mem_residents.2 hMr)) (hfeas h)⟩)

private theorem liftCloneFun_none {M : ManyToOneMatching m n} (hfeas : I.IsFeasible M)
    {r : Fin m} (hMr : M.hospital r = none) :
    I.liftCloneFun hfeas r = none := by
  unfold liftCloneFun
  split <;> simp_all

private theorem liftCloneFun_some {M : ManyToOneMatching m n} (hfeas : I.IsFeasible M)
    {r : Fin m} {h : Fin n} (hMr : M.hospital r = some h) :
    I.liftCloneFun hfeas r =
      some (I.seat h ⟨I.hospPos M h r,
        Nat.lt_of_lt_of_le (I.hospPos_lt_card (ManyToOneMatching.mem_residents.2 hMr))
          (hfeas h)⟩) := by
  unfold liftCloneFun
  split
  · simp_all
  · rename_i h' hsome
    cases hMr.symm.trans hsome
    rfl

private def liftClone {M : ManyToOneMatching m n} (hM : I.IsStable M) :
    PartialMatching m (n * I.maxQuota) :=
  let ⟨hfeas, hir, _⟩ := hM
  PartialMatching.ofInjOn (I.liftCloneFun hfeas) (by
    intro r₁ r₂ s hs₁ hs₂
    cases h₁ : M.hospital r₁ with
    | none =>
      rw [I.liftCloneFun_none hfeas h₁] at hs₁
      nomatch hs₁
    | some hA =>
      cases h₂ : M.hospital r₂ with
      | none =>
        rw [I.liftCloneFun_none hfeas h₂] at hs₂
        nomatch hs₂
      | some hB =>
        rw [I.liftCloneFun_some hfeas h₁] at hs₁
        rw [I.liftCloneFun_some hfeas h₂] at hs₂
        have hseat_eq := (Option.some_injective _ hs₁).trans (Option.some_injective _ hs₂).symm
        have hhAB : hA = hB := by
          have := congrArg (fun x => (finProdFinEquiv.symm x).fst) hseat_eq
          simpa only [seat_symm_fst] using this
        subst hhAB
        have hpos_eq : I.hospPos M hA r₁ = I.hospPos M hA r₂ :=
          congrArg Fin.val (I.seat_inj_same hseat_eq)
        exact I.hospPos_injOn hir hA
          (ManyToOneMatching.mem_residents.2 h₁)
          (ManyToOneMatching.mem_residents.2 h₂) hpos_eq)

private theorem liftClone_apply {M : ManyToOneMatching m n} (hM : I.IsStable M) (r : Fin m) :
    I.liftClone hM r = I.liftCloneFun hM.1 r := rfl

private theorem projectClone_liftClone {M : ManyToOneMatching m n} (hM : I.IsStable M) :
    I.projectClone (I.liftClone hM) = M := by
  refine ManyToOneMatching.ext (funext fun r => ?_)
  simp only [projectClone, liftClone_apply]
  cases hMr : M.hospital r with
  | none => rw [I.liftCloneFun_none hM.1 hMr]; rfl
  | some h => rw [I.liftCloneFun_some hM.1 hMr, Option.map_some, seat_symm_fst]

private theorem isStable_liftClone {M : ManyToOneMatching m n} (hM : I.IsStable M) :
    I.cloneInstance.IsStable (I.liftClone hM) := by
  obtain ⟨hfeas, hir, hnb⟩ := hM
  let μ := I.liftClone ⟨hfeas, hir, hnb⟩
  have hμ_ir : I.cloneInstance.IsIndividuallyRational μ := fun r s hs => by
    change I.liftCloneFun hfeas r = some s at hs
    cases hMr : M.hospital r with
    | none => simp [I.liftCloneFun_none hfeas hMr] at hs
    | some h =>
      rw [I.liftCloneFun_some hfeas hMr] at hs
      obtain rfl := Option.some_injective _ hs
      have hacc := hir r h hMr
      have hlt := (I.hospPos_lt_card (ManyToOneMatching.mem_residents.2 hMr)).trans_le (hfeas h)
      simp only [mem_clone_propPref_iff, mem_clone_recvPref_iff, seat_symm_fst, seat_symm_snd_val]
      exact ⟨⟨hacc.1, hlt⟩, ⟨hlt, hacc.2⟩⟩
  refine ⟨hμ_ir, fun r s ⟨hp_lt, hr_lt⟩ => ?_⟩
  obtain ⟨hh_res, hk_lt⟩ := I.mem_clone_propPref_iff.1
    (IncompleteInstance.IsBlockingPair.mem_propPref I.cloneInstance ⟨hp_lt, hr_lt⟩)
  have hr_hosp : r ∈ I.hospPref (finProdFinEquiv.symm s).fst :=
    (I.mem_clone_recvPref_iff.1
      (IncompleteInstance.IsBlockingPair.mem_recvPref I.cloneInstance ⟨hp_lt, hr_lt⟩)).2
  set h := (finProdFinEquiv.symm s).fst
  let j : Fin (I.quota h) := ⟨(finProdFinEquiv.symm s).snd.val, hk_lt⟩
  rw [I.eq_seat_of_lt_quota s rfl hk_lt] at hp_lt hr_lt
  have hsym_of_lt_card (hj_lt : j.val < (M.residents h).card) :
      ∃ r' ∈ M.residents h, I.hospPos M h r' = j.val ∧ μ.symm (I.seat h j) = some r' := by
    obtain ⟨r', hr'_mem, hr'_pos⟩ := I.exists_hospPos_eq hir h hj_lt
    exact ⟨r', hr'_mem, hr'_pos, μ.eq_some_iff.2 <|
      (I.liftCloneFun_some hfeas (ManyToOneMatching.mem_residents.1 hr'_mem)).trans
        (congrArg (some ∘ I.seat h) (Fin.ext hr'_pos))⟩
  -- Step 1: check whether `M.hospital r = some h`.
  by_cases hMr_same : M.hospital r = some h
  · let jPos : Fin (I.quota h) := ⟨I.hospPos M h r,
      (I.hospPos_lt_card (ManyToOneMatching.mem_residents.2 hMr_same)).trans_le (hfeas h)⟩
    have hμr : μ r = some (I.seat h jPos) := I.liftCloneFun_some hfeas hMr_same
    rw [hμr] at hp_lt
    have hj_lt_pos : j.val < I.hospPos M h r := by
      by_contra! hge
      rcases eq_or_lt_of_le hge with heq | hgt
      · exact lt_irrefl _ ((show j = jPos from Fin.ext heq.symm) ▸ hp_lt)
      · exact lt_asymm hp_lt (I.clone_propRank_seat_lt_same hh_res (show jPos < j from hgt))
    obtain ⟨r', -, hr'_pos, hsym⟩ := hsym_of_lt_card
      (hj_lt_pos.trans (I.hospPos_lt_card (ManyToOneMatching.mem_residents.2 hMr_same)))
    rw [hsym, I.clone_recvRank_seat_some, I.clone_recvRank_seat_some] at hr_lt
    have := I.hospPos_strictMono (ManyToOneMatching.mem_residents.2 hMr_same) hr_lt
    omega
  · -- `M.hospital r ≠ some h`: show `I.resRank r (some h) < I.resRank r (M.hospital r)`.
    have hres_lt : I.resRank r (some h) < I.resRank r (M.hospital r) := by
      cases hMr : M.hospital r with
      | none => exact (I.resRank_some_lt_none_iff r h).2 hh_res
      | some h' =>
        change _ < I.cloneInstance.propRank r (I.liftCloneFun hfeas r) at hp_lt
        rw [I.liftCloneFun_some hfeas hMr] at hp_lt
        by_contra! hnot_lt
        have hgt_res : I.resRank r (some h') < I.resRank r (some h) :=
          lt_of_le_of_ne hnot_lt fun heq =>
            hMr_same ((Option.some_injective _ (I.eq_of_resRank_eq (hir r h' hMr).1 heq)) ▸ hMr)
        exact lt_asymm hp_lt (I.clone_propRank_seat_lt_of_resRank_lt hgt_res _ j)
    -- Now inspect `μ.symm (I.seat h j)` to get unfilled capacity or a worse resident `r'`.
    cases hsym : μ.symm (I.seat h j) with
    | none =>
      refine hnb r h ⟨hres_lt, hr_hosp, Or.inl ?_⟩
      by_contra! hge
      obtain ⟨_, -, -, hsym'⟩ := hsym_of_lt_card (lt_of_lt_of_le j.isLt hge)
      simp [hsym] at hsym'
    | some r' =>
      rw [hsym, I.clone_recvRank_seat_some, I.clone_recvRank_seat_some] at hr_lt
      have hMr' : M.hospital r' = some h := by
        simpa only [projectClone, μ, μ.eq_some_iff.1 hsym, Option.map_some, seat_symm_fst] using
          (congrArg (fun M' => M'.hospital r') (I.projectClone_liftClone ⟨hfeas, hir, hnb⟩)).symm
      exact hnb r h ⟨hres_lt, hr_hosp, Or.inr ⟨r', ManyToOneMatching.mem_residents.2 hMr', hr_lt⟩⟩

/-! ### Resident-proposing deferred acceptance and Roth's Rural Hospitals Theorem -/

/-- Computable resident-proposing **deferred acceptance** for a many-to-one Hospitals–Residents
market ([GaleShapley1962]; [RothSotomayor1990]). -/
def deferredAcceptance : ManyToOneMatching m n :=
  I.projectClone I.cloneInstance.deferredAcceptance

/-- Resident-proposing deferred acceptance produces a stable many-to-one matching
([GaleShapley1962]; [RothSotomayor1990]). -/
theorem isStable_deferredAcceptance : I.IsStable I.deferredAcceptance :=
  I.isStable_projectClone I.cloneInstance.isStable_deferredAcceptance

/-- Every Hospitals–Residents market with strict preferences admits a stable matching. -/
theorem exists_isStable : ∃ M : ManyToOneMatching m n, I.IsStable M :=
  ⟨I.deferredAcceptance, I.isStable_deferredAcceptance⟩

/-- Resident-optimality ([RothSotomayor1990]): every resident weakly prefers its outcome under
`I.deferredAcceptance` to its outcome in any stable matching `M`. -/
theorem resRank_deferredAcceptance_le_of_isStable {M : ManyToOneMatching m n} (hM : I.IsStable M)
    (r : Fin m) : I.resRank r (I.deferredAcceptance.hospital r) ≤ I.resRank r (M.hospital r) := by
  have hda_le :=
    I.cloneInstance.propRank_deferredAcceptance_le_of_isStable (I.isStable_liftClone hM) r
  cases hMr : M.hospital r with
  | none => exact I.resRank_le_resRank_none r _
  | some h₂ =>
    let j₂ : Fin (I.quota h₂) := ⟨I.hospPos M h₂ r,
      (I.hospPos_lt_card (ManyToOneMatching.mem_residents.2 hMr)).trans_le (hM.1 h₂)⟩
    have hμr : I.liftClone hM r = some (I.seat h₂ j₂) := I.liftCloneFun_some hM.1 hMr
    rw [hμr] at hda_le
    cases hdar : I.cloneInstance.deferredAcceptance r with
    | none =>
      rw [hdar] at hda_le
      exact absurd ((I.cloneInstance.propRank_some_lt_none_iff r _).2 (by
        rw [mem_clone_propPref_iff, seat_symm_fst, seat_symm_snd_val]
        exact ⟨(hM.2.1 r h₂ hMr).1, j₂.isLt⟩)) (not_lt_of_ge hda_le)
    | some s₁ =>
      rw [hdar] at hda_le
      have hk₁ := (I.mem_clone_recvPref_iff.1
        (I.cloneInstance.isIndividuallyRational_deferredAcceptance r s₁ hdar).2).1
      simp only [deferredAcceptance, projectClone, hdar, Option.map_some]
      by_contra! hgt
      have hlt_clone := I.clone_propRank_seat_lt_of_resRank_lt hgt j₂ ⟨_, hk₁⟩
      rw [← I.eq_seat_of_lt_quota s₁ rfl hk₁] at hlt_clone
      exact not_lt_of_ge hda_le hlt_clone

theorem isResidentOptimal_deferredAcceptance : I.IsResidentOptimal I.deferredAcceptance :=
  ⟨I.isStable_deferredAcceptance, fun _ hM r => I.resRank_deferredAcceptance_le_of_isStable hM r⟩

/-- **Rural Hospitals Theorem, Part 1** ([Roth1986]; [RothSotomayor1990]): the set of matched
residents is the same across all stable matchings. -/
theorem matchedResidents_eq_of_isStable {M₁ M₂ : ManyToOneMatching m n} (hM₁ : I.IsStable M₁)
    (hM₂ : I.IsStable M₂) : M₁.matchedResidents = M₂.matchedResidents := by
  rw [← I.projectClone_liftClone hM₁, ← I.projectClone_liftClone hM₂,
    I.matchedResidents_projectClone, I.matchedResidents_projectClone]
  exact I.cloneInstance.matchedProposers_eq_of_isStable
    (I.isStable_liftClone hM₁) (I.isStable_liftClone hM₂)

/-- Equivalent form of `matchedResidents_eq_of_isStable`: the set of unmatched residents is the same
across all stable matchings. -/
theorem unmatchedResidents_eq_of_isStable {M₁ M₂ : ManyToOneMatching m n} (hM₁ : I.IsStable M₁)
    (hM₂ : I.IsStable M₂) : {r | M₁.hospital r = none} = {r | M₂.hospital r = none} := by
  ext r
  simpa only [Set.mem_ofPred_eq, ManyToOneMatching.mem_matchedResidents, eq_iff_iff,
    Option.isSome_iff_ne_none, ne_eq, not_iff_not] using
    congrArg (r ∈ ·) (I.matchedResidents_eq_of_isStable hM₁ hM₂)

/-- **Rural Hospitals Theorem, Part 2** ([Roth1986]; [RothSotomayor1990]): every hospital fills the
exact same number of positions across all stable matchings. -/
theorem card_residents_eq_of_isStable {M₁ M₂ : ManyToOneMatching m n} (hM₁ : I.IsStable M₁)
    (hM₂ : I.IsStable M₂) (h : Fin n) : (M₁.residents h).card = (M₂.residents h).card := by
  conv_lhs => rw [← I.projectClone_liftClone hM₁]
  conv_rhs => rw [← I.projectClone_liftClone hM₂]
  rw [I.card_residents_projectClone, I.card_residents_projectClone,
    I.cloneInstance.matchedReceivers_eq_of_isStable
      (I.isStable_liftClone hM₁) (I.isStable_liftClone hM₂)]

private theorem deferredAcceptance_residents_eq_of_card_lt_quota {M : ManyToOneMatching m n}
    (hM : I.IsStable M) {h : Fin n} (hlt : (M.residents h).card < I.quota h) :
    I.deferredAcceptance.residents h = M.residents h := by
  refine Finset.eq_of_subset_of_card_le (fun r hr => ?_)
    (I.card_residents_eq_of_isStable hM I.isStable_deferredAcceptance h).le
  rw [ManyToOneMatching.mem_residents] at hr ⊢
  have hda_ir := I.isStable_deferredAcceptance.2.1 r h hr
  have hle := hr ▸ I.resRank_deferredAcceptance_le_of_isStable hM r
  by_contra hne
  exact hM.2.2 r h ⟨lt_of_le_of_ne hle fun heq => hne (I.eq_of_resRank_eq hda_ir.1 heq),
    hda_ir.2, Or.inl hlt⟩

/-- **Rural Hospitals Theorem, Part 3** ([Roth1986]; [RothSotomayor1990]): any hospital `h` that
does not fill its quota in some stable matching is assigned the **exact same set of residents** in
every stable matching. -/
theorem residents_eq_of_card_lt_quota {M₁ M₂ : ManyToOneMatching m n} (hM₁ : I.IsStable M₁)
    (hM₂ : I.IsStable M₂) {h : Fin n} (hlt : (M₁.residents h).card < I.quota h) :
    M₁.residents h = M₂.residents h := by
  have hlt₂ : (M₂.residents h).card < I.quota h :=
    I.card_residents_eq_of_isStable hM₁ hM₂ h ▸ hlt
  exact (I.deferredAcceptance_residents_eq_of_card_lt_quota hM₁ hlt).symm.trans
    (I.deferredAcceptance_residents_eq_of_card_lt_quota hM₂ hlt₂)

end ManyToOneInstance

end Cslib.Algorithms.Lean.StableMatching
