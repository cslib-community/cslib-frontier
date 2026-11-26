/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Automata.Weighted.Loop
import CslibFrontier.Foundations.Data.List.KeyedFlatMap
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Sum
import Mathlib.Data.List.Nodup

/-!
# Programs given by their structured runs

A series on channels is described by a family of structured runs: every run emits words on the
channels (`em : X → Z → List Γ`) and carries a weight (`wt : X → F`). `Tape.IsRuns P em wt` says
that `hat P v` equals the sum of weights of the runs that emit `v`, and `Tape.Runs n em wt` states
that some series of dimension at most `n` represents `(em, wt)`.

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Sort.Runs`.

## Main definitions

* `Tape.IsRuns`: `hat P v` decomposes as a finite sum over `em ⁻¹' {v}`.
* `Tape.Runs`: existence of a bounded-dimension rational series realizing `(em, wt)`.
* `Tape.chanWord`: materialize a channel assignment channel-by-channel.

## Main results

* `Tape.IsRuns.mul`, `Tape.IsRuns.sum`, `Tape.IsRuns.congr`, `Tape.IsRuns.one`,
  `Tape.IsRuns.kstar`.
* `Tape.Runs.mul`, `Tape.Runs.sum`, `Tape.Runs.add`, `Tape.Runs.kstar`, `Tape.Runs.pick`,
  `Tape.Runs.const`, `Tape.Runs.pi`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Tape

open Finset Cslib.Automata.Weighted

section RunsDef

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Finite Γ]

/-- The series `P` is described by runs with emissions `em` and weights `wt`. -/
@[expose] def IsRuns (P : Series F (Z × Γ)) {X : Type*} (em : X → Z → List Γ)
    (wt : X → F) : Prop :=
  ∀ v, ∃ R : Finset X, (∀ x, x ∈ R ↔ em x = v) ∧ hat P v = ∑ x ∈ R, wt x

/-- There is a rational series of dimension at most `n` with runs `(em, wt)`. -/
@[expose] def Runs (n : ℕ) {X : Type*} (em : X → Z → List Γ) (wt : X → F) : Prop :=
  ∃ P : Series F (Z × Γ), RatLe n P ∧ IsRuns P em wt

theorem IsRuns.exists_run {P : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ}
    {wt : X → F} (h : IsRuns P em wt) {v : Z → List Γ} (hv : hat P v ≠ 0) :
    ∃ x, em x = v ∧ wt x ≠ 0 := by
  obtain ⟨R, h1, h2⟩ := h v
  rw [h2] at hv
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hv
  exact ⟨x, (h1 x).1 hx, hne⟩

theorem IsRuns.of_fib {P : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ}
    {wt : X → F} (h : IsRuns P em wt) {v : Z → List Γ} (R : Finset X)
    (hR : ∀ x, x ∈ R ↔ em x = v) : hat P v = ∑ x ∈ R, wt x := by
  obtain ⟨R', h1, h2⟩ := h v
  rwa [Finset.ext fun x => (h1 x).trans (hR x).symm] at h2

theorem IsRuns.mul {f g : Series F (Z × Γ)} {X Y : Type*}
    {em : X → Z → List Γ} {wt : X → F} {em' : Y → Z → List Γ} {wt' : Y → F}
    (hf : IsRuns f em wt) (hg : IsRuns g em' wt') :
    IsRuns (Series.mul f g)
      (fun (x : X × Y) z => em x.1 z ++ em' x.2 z) (fun x => wt x.1 * wt' x.2) := by
  classical
  intro v
  choose Rf hf1 hf2 using hf
  choose Rg hg1 hg2 using hg
  refine ⟨(anti v).biUnion fun p => Rf p.1 ×ˢ Rg p.2, ?_, ?_⟩
  · rintro ⟨x, y⟩
    simp only [Finset.mem_biUnion, Finset.mem_product, hf1, hg1, mem_anti]
    exact ⟨fun ⟨p, hp, h1, h2⟩ => funext fun z => by rw [h1, h2, hp z],
      fun h => ⟨(em x, em' y), congrFun h, rfl, rfl⟩⟩
  · rw [hat_mul, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl fun p _ => by rw [hf2, hg2, Finset.sum_mul_sum, Finset.sum_product]
    · intro p _ q _ hpq
      refine Finset.disjoint_left.mpr fun ⟨x, y⟩ h h' => ?_
      rw [Finset.mem_product, hf1, hg1] at h h'
      exact hpq (Prod.ext (h.1.symm.trans h'.1) (h.2.symm.trans h'.2))

theorem IsRuns.sum {ι : Type*} [Fintype ι] {X : ι → Type*} {P : ι → Series F (Z × Γ)}
    {em : ∀ i, X i → Z → List Γ} {wt : ∀ i, X i → F}
    (h : ∀ i, IsRuns (P i) (em i) (wt i)) :
    IsRuns (∑ i, P i) (fun (x : Σ i, X i) => em x.1 x.2) (fun x => wt x.1 x.2) := by
  intro v
  choose R h1 h2 using h
  refine ⟨univ.sigma fun i => R i v, ?_, ?_⟩
  · rintro ⟨i, x⟩
    simp [h1]
  · rw [hat_sum, Finset.sum_sigma]
    exact Finset.sum_congr rfl fun i _ => h2 i v

theorem IsRuns.congr {P : Series F (Z × Γ)} {X Y : Type*} {em : X → Z → List Γ}
    {wt : X → F} {em' : Y → Z → List Γ} {wt' : Y → F} (h : IsRuns P em wt) (e : Y ≃ X)
    (h1 : ∀ y z, em (e y) z = em' y z) (h2 : ∀ y, wt (e y) = wt' y) :
    IsRuns P em' wt' := by
  intro v
  obtain ⟨R, g1, g2⟩ := h v
  refine ⟨R.map e.symm.toEmbedding, fun y => ?_, ?_⟩
  · simp [g1, funext (h1 y)]
  · rw [g2, Finset.sum_map]
    exact Finset.sum_congr rfl fun _ _ => by simp [← h2]

theorem IsRuns.one :
    IsRuns (Series.one : Series F (Z × Γ)) (fun (_ : Unit) _ => []) (fun _ => 1) := by
  classical
  intro v
  refine ⟨if v = fun _ => [] then {()} else ∅, fun _ => ?_, ?_⟩
  · by_cases h : v = fun _ => [] <;> simp [h, Ne.symm]
  · rw [hat_one]
    split_ifs <;> simp

/-- The star: runs of `Series.kstar f` are finite lists of non-empty runs of `f`. -/
theorem IsRuns.kstar {f : Series F (Z × Γ)} {X : Type*} {em : X → Z → List Γ}
    {wt : X → F} (hf : IsRuns f em wt) (hne : ∀ x, em x ≠ fun _ => []) :
    IsRuns (Series.kstar f) (fun (l : List X) z => l.flatMap fun x => em x z)
      (fun l => (l.map wt).prod) := by
  classical
  intro v
  induction hn : ∑ z, (v z).length using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    choose Rf hf1 hf2 using hf
    have hlt : ∀ p ∈ (anti v).filter (fun p => p.1 ≠ fun _ => []),
        ∑ z, (p.2 z).length < n := by
      intro p hp
      rw [Finset.mem_filter, mem_anti] at hp
      have he : n = ∑ z, (p.1 z).length + ∑ z, (p.2 z).length := by
        rw [← hn, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun z _ => by rw [← hp.1 z, List.length_append]
      have hpos : 0 < ∑ z, (p.1 z).length := Nat.pos_iff_ne_zero.2 fun h0 => hp.2 <| funext fun z =>
        List.length_eq_zero_iff.1 (Finset.sum_eq_zero_iff.1 h0 z (Finset.mem_univ z))
      omega
    let A := (anti v).filter fun p => p.1 ≠ fun _ => []
    have ih' (p : (Z → List Γ) × (Z → List Γ)) : ∃ R : Finset (List X), p ∈ A →
        (∀ l, l ∈ R ↔ (fun z => l.flatMap fun x => em x z) = p.2) ∧
          hat (Series.kstar f) p.2 = ∑ l ∈ R, (l.map wt).prod :=
      if hp : p ∈ A then (ih _ (hlt p hp) p.2 rfl).imp fun _ h _ => h
      else ⟨∅, fun h => absurd h hp⟩
    choose Rs hRs using ih'
    let B : Finset (X × List X) := A.biUnion fun p => Rf p.1 ×ˢ Rs p
    have hB : ∀ x l, (x, l) ∈ B ↔ (fun z => em x z ++ l.flatMap fun x => em x z) = v := by
      intro x l
      simp only [B, Finset.mem_biUnion, Finset.mem_product]
      constructor
      · rintro ⟨p, hp, h1, h2⟩
        funext z
        rw [← (mem_anti.1 (Finset.mem_filter.1 hp).1) z, (hf1 _ _).1 h1,
          congrFun (((hRs p hp).1 _).1 h2) z]
      · intro h
        have hp : (em x, fun z => l.flatMap fun x => em x z) ∈ A :=
          Finset.mem_filter.2 ⟨mem_anti.2 (congrFun h), hne x⟩
        exact ⟨_, hp, (hf1 _ _).2 rfl, ((hRs _ hp).1 _).2 rfl⟩
    let C : Finset (List X) :=
      B.map ⟨fun p => p.1 :: p.2, by rintro ⟨a, b⟩ ⟨c, d⟩ h; simpa using h⟩
    have hC : ∀ l, l ∈ C ↔ l ≠ [] ∧ (fun z => l.flatMap fun x => em x z) = v := by
      intro l
      simp only [C, Finset.mem_map, Prod.exists]
      refine ⟨?_, fun ⟨h1, h2⟩ => ?_⟩
      · rintro ⟨x, l', h, rfl⟩
        exact ⟨List.cons_ne_nil _ _, (hB x l').1 h⟩
      · obtain ⟨x, l', rfl⟩ := List.exists_cons_of_ne_nil h1
        exact ⟨x, l', (hB _ _).2 h2, rfl⟩
    refine ⟨(if v = fun _ => [] then {[]} else ∅) ∪ C, fun l => ?_, ?_⟩
    · rw [Finset.mem_union, hC]
      by_cases hl : l = [] <;> by_cases h : v = fun _ => [] <;> simp [hl, h, Ne.symm]
    · rw [Finset.sum_union, hat_kstar]
      · congr 1
        · split_ifs <;> simp
        · simp only [C, Finset.sum_map, B]
          rw [Finset.sum_biUnion]
          · refine Finset.sum_congr rfl fun p hp => ?_
            rw [hf2, (hRs p hp).2, Finset.sum_mul_sum, Finset.sum_product]
            exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
              (List.prod_cons ..).symm
          · intro p hp q hq hpq
            rw [Function.onFun, Finset.disjoint_left]
            rintro ⟨x, y⟩ h h'
            rw [Finset.mem_product, hf1] at h h'
            exact hpq (Prod.ext (h.1.symm.trans h'.1)
              (((hRs p hp).1 y |>.1 h.2).symm.trans ((hRs q hq).1 y |>.1 h'.2)))
      · split_ifs <;> simp [hC]

end RunsDef

section ChanWord

variable {Z Γ : Type*} [DecidableEq Z]

/-- The channel word concatenating each channel's assignment in order. -/
@[expose] noncomputable def chanWord [Fintype Z] (w : Z → List Γ) : List (Z × Γ) :=
  (univ : Finset Z).toList.flatMap fun z => (w z).map fun a => (z, a)

private theorem proj_flatMap {ι : Type*} (l : List ι) (g : ι → List (Z × Γ)) (z : Z) :
    proj (l.flatMap g) z = l.flatMap fun i => proj (g i) z := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.flatMap_cons, List.flatMap_cons, proj_append, ih]

private theorem proj_map_mk (z z' : Z) (w : List Γ) :
    proj (w.map fun a => (z, a)) z' = if z = z' then w else [] := by
  induction w with
  | nil => simp
  | cons a w ih =>
    rw [List.map_cons, proj_cons, ih]
    split_ifs <;> rfl

theorem proj_chanWord [Fintype Z] (w : Z → List Γ) : proj (chanWord w) = w := by
  funext z
  simp_rw [chanWord, proj_flatMap, proj_map_mk]
  exact List.flatMap_ite_key_eq _ id w (by simpa using Finset.nodup_toList _) (by simp)

omit [DecidableEq Z] in
theorem length_chanWord [Fintype Z] (w : Z → List Γ) :
    (chanWord w).length = ∑ z, (w z).length := by
  classical
  rw [← sum_length_proj, proj_chanWord]

end ChanWord

namespace Runs

variable {F : Type*} [CommRing F] {Z Γ : Type*} [Fintype Z] [DecidableEq Z] [Finite Γ]

theorem mono {n m : ℕ} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (h : Runs n em wt) (hm : n ≤ m) : Runs m em wt := by
  obtain ⟨P, h1, h2⟩ := h
  exact ⟨P, h1.mono hm, h2⟩

theorem congr {n : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (h : Runs n em wt) (e : Y ≃ X)
    (h1 : ∀ y z, em (e y) z = em' y z) (h2 : ∀ y, wt (e y) = wt' y) :
    Runs n em' wt' := by
  obtain ⟨P, g1, g2⟩ := h
  exact ⟨P, g1, g2.congr e h1 h2⟩

theorem mul {n m : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : Runs n em wt) (hg : Runs m em' wt') :
    Runs (n + m) (fun (x : X × Y) z => em x.1 z ++ em' x.2 z)
      (fun x => wt x.1 * wt' x.2) := by
  classical
  obtain ⟨P, g1, g2⟩ := hf
  obtain ⟨Q, g3, g4⟩ := hg
  exact ⟨_, g1.mul g3, g2.mul g4⟩

theorem sum {ι : Type*} [Fintype ι] {n : ι → ℕ} {X : ι → Type*}
    {em : ∀ i, X i → Z → List Γ} {wt : ∀ i, X i → F}
    (h : ∀ i, Runs (n i) (em i) (wt i)) :
    Runs (∑ i, n i) (fun (x : Σ i, X i) => em x.1 x.2) (fun x => wt x.1 x.2) := by
  choose P h1 h2 using h
  exact ⟨∑ i, P i, RatLe.sum _ _ _ fun i _ => h1 i, IsRuns.sum h2⟩

theorem add {n m : ℕ} {X Y : Type*} {em : X → Z → List Γ} {wt : X → F}
    {em' : Y → Z → List Γ} {wt' : Y → F} (hf : Runs n em wt) (hg : Runs m em' wt') :
    Runs (n + m) (Sum.elim em em') (Sum.elim wt wt') := by
  classical
  obtain ⟨P, g1, g2⟩ := hf
  obtain ⟨Q, g3, g4⟩ := hg
  refine ⟨P + Q, g1.add g3, fun v => ?_⟩
  obtain ⟨R, h1, h2⟩ := g2 v
  obtain ⟨R', h3, h4⟩ := g4 v
  refine ⟨R.disjSum R', by rintro (x | x) <;> simp [h1, h3], ?_⟩
  rw [hat_add, h2, h4, Finset.sum_disjSum]
  simp

theorem kstar {n : ℕ} {X : Type*} {em : X → Z → List Γ} {wt : X → F}
    (hf : Runs n em wt) (hne : ∀ x, ∃ z, em x z ≠ []) :
    Runs (n + 1) (fun (l : List X) z => l.flatMap fun x => em x z)
      (fun l => (l.map wt).prod) := by
  obtain ⟨P, g1, g2⟩ := hf
  refine ⟨_, g1.kstar, g2.kstar fun x h => ?_⟩
  obtain ⟨z, hz⟩ := hne x
  exact hz (congrFun h z)

theorem one :
    Runs 1 (fun (_ : Unit) (_ : Z) => ([] : List Γ)) (fun _ => (1 : F)) :=
  ⟨_, RatLe.one, IsRuns.one⟩

/-- One of finitely many families of channel words, with weights `c`. -/
theorem pick {κ : Type*} [Fintype κ] (w : κ → Z → List Γ) (c : κ → F) :
    Runs (∑ k, (2 * ∑ z, (w k z).length + 1)) w c := by
  classical
  refine ⟨Series.body (fun k => chanWord (w k)) c,
    by simpa only [length_chanWord] using RatLe.body (F := F) (fun k => chanWord (w k)) c,
    fun v => ⟨univ.filter fun k => w k = v, by simp, ?_⟩⟩
  rw [hat_body, Finset.sum_filter]
  exact Finset.sum_congr rfl fun k _ => by
    rw [proj_chanWord]
    by_cases h : w k = v <;> simp [h, Ne.symm]

/-- Fixed channel words `w` with weight `1`. -/
theorem const (w : Z → List Γ) :
    Runs (2 * ∑ z, (w z).length + 1) (fun (_ : Unit) => w) (fun _ => (1 : F)) := by
  simpa using pick (F := F) (fun _ : Unit => w) (fun _ => 1)

/-- A sequence of `k` independent run choices. -/
theorem pi {k : ℕ} {n : Fin k → ℕ} {X : Fin k → Type*}
    {em : ∀ i, X i → Z → List Γ} {wt : ∀ i, X i → F}
    (h : ∀ i, Runs (n i) (em i) (wt i)) :
    Runs (∑ i, n i + 1)
      (fun (x : ∀ i, X i) z => (List.ofFn fun i => em i (x i) z).flatten)
      (fun x => ∏ i, wt i (x i)) := by
  induction k with
  | zero =>
    exact ((one (F := F) (Z := Z) (Γ := Γ)).congr
      ⟨fun _ => (), fun _ i => i.elim0, fun _ => Subsingleton.elim _ _, fun _ => rfl⟩
      (fun _ _ => by simp) (fun _ => by simp)).mono
      (by omega)
  | succ k ih =>
    have h1 := (h 0).mul
      (ih (n := fun i => n i.succ) (X := fun i => X i.succ)
        (em := fun i => em i.succ) (wt := fun i => wt i.succ) fun i => h i.succ)
    refine (h1.congr (Fin.consEquiv X).symm
      (fun y z => by simp [Fin.consEquiv, List.ofFn_succ, Fin.tail])
      fun y => by simp [Fin.consEquiv, Fin.prod_univ_succ, Fin.tail]).mono ?_
    rw [Fin.sum_univ_succ]
    omega

end Runs

end Cslib.Circuits.Arithmetic.Separation.Tape
