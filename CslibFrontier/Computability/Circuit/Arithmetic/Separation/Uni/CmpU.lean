/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.List.RadixSort
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.SortU

/-!
# Neighbour comparison on duplicate tapes

Checks whether adjacent records in a sorted list agree whenever the second record is a lookup
(`Uni.chkG`), by streaming two shifted copies (`Uni.PlG`, `Uni.QlG`) across comparison tapes
`cm false` and `cm true` (`Uni.emCm`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.CmpU`.

## Main definitions

* `Uni.chkG`: generic neighbour check over any key type `κ`.
* `Uni.RdG`, `Uni.RdG.fst`, `Uni.RdG.snd`: shifted comparison step.
* `Uni.XG`, `Uni.PlG`, `Uni.QlG`: comparison run witnessing adjacent records.
* `Uni.Rk`, `Uni.rk`, `Uni.emRd`, `Uni.emCm`, `Uni.dimCm`.

## Main results

* `Uni.chkG_map`, `Uni.exists_cmpG`, `Uni.cmpG_unique`.
* `Uni.runs_rk`, `Uni.runs_rdG`, `Uni.runs_cm`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Cslib.Automata.Weighted Cslib.Circuits.Arithmetic.Separation.Tape
open List.RadixSort (Rc chk)

section Pure

variable {κ : Type*}

/-- Generic check of neighbours: every lookup (`r.1 = true`) shares its key with `p`. -/
@[expose] def chkG : Option κ → List (Bool × κ) → Prop
  | _, [] => True
  | p, r :: l => (r.1 = false ∨ p = some r.2) ∧ chkG (some r.2) l

theorem chkG_map {n : ℕ} {B κ : Type*} (φ : (Fin n → B) → κ) (hφ : Function.Injective φ)
    (p : Option (Fin n → B)) (l : List (Rc n B)) :
    chkG (p.map φ) (l.map fun r => (r.1, φ r.2)) ↔ chk p l := by
  induction l generalizing p with
  | nil => simp [chkG, chk]
  | cons r l ih =>
    rw [List.map_cons, chkG, chk]
    have h1 := ih (some r.2)
    rw [Option.map_some] at h1
    rw [h1]
    refine and_congr (or_congr Iff.rfl ?_) Iff.rfl
    rcases p with _ | q
    · simp
    · simp [hφ.eq_iff]

/-- One round of the shifted neighbour comparison: either an entry/arbitrary step `(.inl (r, x))`
or a matching lookup step `(.inr r)`. -/
abbrev RdG (κ : Type*) := ((Bool × κ) × κ) ⊕ (Bool × κ)

/-- The record read on the second copy (`cQ`). -/
@[expose] def RdG.fst : RdG κ → Bool × κ
  | .inl (r, _) => r
  | .inr r => r

/-- The record read on the first copy (`cP`): the succeeding record. -/
@[expose] def RdG.snd : RdG κ → Bool × κ
  | .inl (_, x) => (false, x)
  | .inr r => (true, r.2)

theorem RdG.ext {d d' : RdG κ} (h1 : d.fst = d'.fst) (h2 : d.snd = d'.snd) : d = d' := by
  rcases d with ⟨r, x⟩ | r <;> rcases d' with ⟨r', x'⟩ | r' <;>
    simp_all [RdG.fst, RdG.snd]

theorem RdG.exists_iff (r r' : Bool × κ) :
    (∃ d : RdG κ, d.fst = r ∧ d.snd = r') ↔ (r'.1 = false ∨ some r.2 = some r'.2) := by
  constructor
  · rintro ⟨⟨r, x⟩ | r, rfl, rfl⟩ <;> simp [RdG.fst, RdG.snd]
  · rcases r' with ⟨f, x⟩
    rintro (h | h)
    · simp only at h
      subst h
      exact ⟨.inl (r, x), rfl, rfl⟩
    · simp only [Option.some.injEq] at h
      subst h
      cases f
      · exact ⟨.inl (r, r.2), rfl, rfl⟩
      · exact ⟨.inr r, rfl, rfl⟩

theorem cmpG_iff (r : Bool × κ) (l : List (Bool × κ)) :
    (∃ (ds : List (RdG κ)) (r' : Bool × κ),
        ds.map RdG.snd = l ∧ ds.map RdG.fst ++ [r'] = r :: l) ↔
      chkG (some r.2) l := by
  induction l generalizing r with
  | nil =>
    simp only [chkG, iff_true]
    exact ⟨[], r, rfl, rfl⟩
  | cons a l ih =>
    rw [chkG, ← ih, ← RdG.exists_iff]
    constructor
    · rintro ⟨_ | ⟨d, ds⟩, r', h1, h2⟩
      · simp at h1
      · simp only [List.map_cons, List.cons.injEq, List.cons_append] at h1 h2
        exact ⟨⟨d, h2.1, h1.1⟩, ds, r', h1.2, h2.2⟩
    · rintro ⟨⟨d, h1, h2⟩, ds, r', h3, h4⟩
      exact ⟨d :: ds, r', by simp [h2, h3], by simp [h1, h4]⟩

/-- A run of the shifted neighbour comparison between the two copies of the sorted list. -/
@[ext]
structure XG (κ : Type*) where
  /-- key of the leading table entry on the first copy -/
  head : κ
  /-- sequence of adjacent-pair comparison rounds -/
  rounds : List (RdG κ)
  /-- trailing record on the second copy -/
  last : Bool × κ

/-- The record list reconstructed on the first comparison copy (`cP`). -/
@[expose] def PlG (y : XG κ) : List (Bool × κ) :=
  (false, y.head) :: y.rounds.map RdG.snd

/-- The record list reconstructed on the second comparison copy (`cQ`). -/
@[expose] def QlG (y : XG κ) : List (Bool × κ) :=
  y.rounds.map RdG.fst ++ [y.last]

theorem exists_cmpG {l : List (Bool × κ)} (hl : l ≠ []) :
    (∃ y : XG κ, PlG y = l ∧ QlG y = l) ↔ chkG none l := by
  obtain ⟨r, l, rfl⟩ := List.exists_cons_of_ne_nil hl
  rw [chkG, ← cmpG_iff]
  constructor
  · rintro ⟨⟨x, ds, r'⟩, h1, h2⟩
    simp only [PlG, List.cons.injEq] at h1
    obtain ⟨rfl, h1⟩ := h1
    exact ⟨Or.inl rfl, ds, r', h1, h2⟩
  · rintro ⟨h, ds, r', h1, h2⟩
    have hr : r.1 = false := by simpa using h
    obtain ⟨f, x⟩ := r
    simp only at hr
    subst hr
    exact ⟨⟨x, ds, r'⟩, by simp [PlG, h1], h2⟩

theorem cmpG_unique {y y' : XG κ} (h1 : PlG y = PlG y') (h2 : QlG y = QlG y') :
    y = y' := by
  obtain ⟨x, ds, r⟩ := y
  obtain ⟨x', ds', r'⟩ := y'
  simp only [PlG, List.cons.injEq, Prod.mk.injEq, true_and] at h1
  simp only [QlG] at h2
  obtain ⟨rfl, h1⟩ := h1
  have hl : ds.length = ds'.length := by simpa using congrArg List.length h1
  obtain ⟨h4, h3⟩ := List.append_inj h2 (by simpa using hl)
  obtain rfl : r = r' := by simpa using h3
  obtain rfl : ds = ds' := by
    clear h3 h2
    induction ds generalizing ds' with
    | nil => simpa using hl.symm
    | cons d ds ih =>
      rcases ds' with _ | ⟨d', ds'⟩
      · simp at hl
      · simp only [List.map_cons, List.cons.injEq] at h1 h4
        rw [RdG.ext h4.1 h1.1, ih ds' h1.2 (by simpa using hl) h4.2]
  rfl

end Pure

variable {A : Type*} [CommRing A] {M K : Type}

/-- Records stripped of rotation marks. -/
abbrev Rk (K : Type) := Bool × List (Bl K)

/-- Tape encoding of a record without the rotation mark. -/
@[expose] def rk (r : Rk K) : List (Sy M K) := rw' r.1 (r.2.map some)

theorem rk_eq (r : Rk K) : (rk r : List (Sy M K)) = .flag r.1 :: (r.2.map be ++ [.dot]) := by
  rw [rk, rw', List.map_map]; rfl

/-- The read side of the first comparison tape copy. -/
abbrev cP : Zc K := .tp (.cm false) true

/-- The read side of the second comparison tape copy. -/
abbrev cQ : Zc K := .tp (.cm true) true

section Emit

variable [Finite M] [Fintype K] [DecidableEq K]

theorem runs_rk (zs : Finset (Zc K)) (hz : zs.Nonempty) :
    Runs (2 * (2 * zs.card + 1) + (Fintype.card (Bl K) * (2 * zs.card + 1) + 1) +
        (2 * zs.card + 1))
      (fun r : Rk K => on zs (rk r : List (Sy M K))) (fun _ => (1 : A)) := by
  have h :=
    ((Runs.letter (F := A) zs (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
      (Runs.wordstar (F := A) zs hz (be : Bl K → Sy M K))).mul
      (Runs.word (F := A) zs [(Sy.dot : Sy M K)])
  refine (h.congr
    ⟨fun r => ((r.1, r.2), ()), fun y => (y.1.1, y.1.2), fun _ => rfl, fun _ => rfl⟩
    (fun r z => ?_) fun _ => by simp).mono ?_
  · simp only [Equiv.coe_fn_mk, on_append, rk_eq]
    rfl
  · simp

/-- Emissions of a single comparison round on `cP` and `cQ`. -/
@[expose] def emRd (d : RdG (List (Bl K))) : Zc K → List (Sy M K) := fun z =>
  on {cP} (rk d.snd) z ++ on {cQ} (rk d.fst) z

theorem runs_rdG :
    Runs ((9 + (Fintype.card (Bl K) * 3 + 1) + (3 + (Fintype.card (Bl K) * 3 + 1) + 3)) +
        (6 + 3 + (Fintype.card (Bl K) * 5 + 1) + 5))
      (emRd : RdG (List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hpq : (cP : Zc K) ≠ cQ := by simp
  have h1 := (runs_rk (A := A) (M := M) (K := K) {cQ} ⟨cQ, by simp⟩).mul
    (((Runs.word (F := A) (Z := Zc K) {cP} [(Sy.flag false : Sy M K)]).mul
      (Runs.wordstar (F := A) {cP} ⟨cP, by simp⟩ (be : Bl K → Sy M K))).mul
      (Runs.word (F := A) {cP} [(Sy.dot : Sy M K)]))
  have h2 :=
    (((Runs.letter (F := A) (Z := Zc K) {cQ} (fun f : Bool => (Sy.flag f : Sy M K))
        (fun _ => 1)).mul
      (Runs.word (F := A) {cP} [(Sy.flag true : Sy M K)])).mul
      (Runs.wordstar (F := A) {cP, cQ} ⟨cP, by simp⟩ (be : Bl K → Sy M K))).mul
      (Runs.word (F := A) {cP, cQ} [(Sy.dot : Sy M K)])
  refine ((h1.add h2).congr
    ⟨Sum.map (fun y => (y.1, (((), y.2), ()))) (fun y => (((y.1, ()), y.2), ())),
     Sum.map (fun y => (y.1, y.2.1.2)) (fun y => (y.1.1.1, y.1.2)),
     fun y => by rcases y with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl,
     fun y => by rcases y with ⟨a, b⟩ | ⟨a, b⟩ <;> rfl⟩
    (fun y z => ?_) fun y => by rcases y with ⟨a, b⟩ | ⟨a, b⟩ <;> simp).mono ?_
  · rcases y with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Equiv.coe_fn_mk, Sum.map_inl, Sum.elim_inl, emRd, RdG.fst, RdG.snd, rk_eq]
      by_cases hz : z = cP
      · subst hz; simp [on]
      · simp [on, hz]
    · simp only [Equiv.coe_fn_mk, Sum.map_inr, Sum.elim_inr, emRd, RdG.fst, RdG.snd, rk_eq]
      by_cases hz : z = cP
      · subst hz; simp [on]
      · by_cases hz' : z = cQ
        · subst hz'; simp [on]
        · simp [on, hz, hz']
  · rw [Finset.card_pair hpq]
    simp only [card_singleton, List.length_singleton, Fintype.card_bool]
    omega

/-- Emissions of a full comparison run on `cP` and `cQ`. -/
@[expose] def emCm (y : XG (List (Bl K))) : Zc K → List (Sy M K) := fun z =>
  on {cP} ((PlG y).flatMap rk) z ++ on {cQ} ((QlG y).flatMap rk) z

/-- Dimension upper bound for the neighbour-comparison automaton with bucket count `k`. -/
@[expose] def dimCm (k : ℕ) : ℕ :=
  (3 + (k * 3 + 1) + 3) +
    ((((9 + (k * 3 + 1) + (3 + (k * 3 + 1) + 3)) +
      (6 + 3 + (k * 5 + 1) + 5)) + 1) + (6 + (k * 3 + 1) + 3))

theorem runs_cm : Runs (dimCm (Fintype.card (Bl K)))
    (emCm : XG (List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  have hk := (runs_rdG (A := A) (M := M) (K := K)).kstar
    fun _ => ⟨cP, by simp [emRd, on, rk_eq]⟩
  have h :=
    (((Runs.word (F := A) (Z := Zc K) {cP} [(Sy.flag false : Sy M K)]).mul
      (Runs.wordstar (F := A) {cP} ⟨cP, by simp⟩ (be : Bl K → Sy M K))).mul
      (Runs.word (F := A) {cP} [(Sy.dot : Sy M K)])).mul
      (hk.mul (runs_rk (A := A) (M := M) (K := K) {cQ} ⟨cQ, by simp⟩))
  refine (h.congr
    ⟨fun y => ((((), y.head), ()), y.rounds, y.last),
     fun y => ⟨y.1.1.2, y.2.1, y.2.2⟩,
     fun _ => rfl, fun _ => rfl⟩
    (fun y z => ?_) fun _ => by simp).mono ?_
  · obtain ⟨w, ds, r⟩ := y
    simp only [Equiv.coe_fn_mk, emCm, PlG, QlG]
    by_cases hz : z = cP
    · subst hz
      simp [on, emRd, rk_eq, List.flatMap_map]
    · by_cases hz' : z = cQ
      · subst hz'
        simp [on, emRd, rk_eq, List.flatMap_map]
      · simp [on, emRd, hz, hz']
  · unfold dimCm
    simp

end Emit

end Cslib.Circuits.Arithmetic.Separation.Uni
