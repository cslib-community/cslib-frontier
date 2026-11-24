/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.SpecU

/-!
# The sorting loop: the number of passes is forced

Matching the tape equations `Uni.IMU` on an encoded block of rotated records forces the sorting
loop `Uni.XU` to execute the exact `n` radix-sort passes `Uni.canon l n 0`, terminating uniquely
when and only when every lookup key is present in the table (`Uni.imu_table`, `Uni.imu_unique`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.SpecU2`.

## Main definitions

* `Uni.rst`, `Uni.rot`, `Uni.recs`: cyclic rotation of key letters past the `none` mark.
* `Uni.dl`, `Uni.toNB`, `Uni.cps`, `Uni.canon`, `Uni.finL`: canonical radix-sort run witnesses.
* `Uni.IMU`: matched-tape condition for the sorting-and-comparison loop.

## Main results

* `Uni.passes_iff`: exact forcing of passes and final record list.
* `Uni.imu_iff`, `Uni.imu_unique`, `Uni.imu_exists`, `Uni.imu_table`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Cslib.Automata.Weighted Cslib.Circuits.Arithmetic.Separation.Tape
open List.RadixSort (Rc pass srt chk chk_table length_srt)

variable {M K : Type} [Fintype K] [DecidableEq K] {n : ℕ}

/-- The letters of a key `x` after `j` rotations, omitting the leading entry. -/
@[expose] def rst (j : ℕ) (x : Fin n → Bl K) : List (Option (Bl K)) :=
  ((List.ofFn x).drop (j + 1)).map some ++ none :: ((List.ofFn x).take j).map some

/-- The letters of a key `x` after `j` cyclic rotations past the `none` mark. -/
@[expose] def rot (j : ℕ) (x : Fin n → Bl K) : List (Option (Bl K)) :=
  ((List.ofFn x).drop j).map some ++ none :: ((List.ofFn x).take j).map some

omit [Fintype K] [DecidableEq K] in
theorem rot_cons {j : ℕ} (hj : j < n) (x : Fin n → Bl K) :
    rot j x = some (x ⟨j, hj⟩) :: rst j x := by
  rw [rot, rst, List.drop_eq_getElem_cons (by simpa using hj)]
  simp

omit [Fintype K] [DecidableEq K] in
theorem rot_succ {j : ℕ} (hj : j < n) (x : Fin n → Bl K) :
    rot (j + 1) x = rst j x ++ [some (x ⟨j, hj⟩)] := by
  rw [rot, rst, List.take_succ_eq_append_getElem (by simpa using hj)]
  simp

omit [Fintype K] [DecidableEq K] in
theorem rot_zero (x : Fin n → Bl K) : rot 0 x = (List.ofFn x).map some ++ [none] := by
  simp [rot]

omit [Fintype K] [DecidableEq K] in
theorem rot_last (x : Fin n → Bl K) : rot n x = none :: (List.ofFn x).map some := by
  rw [rot, List.drop_of_length_le (by simp), List.take_of_length_le (by simp)]
  rfl

/-- Encode a list of records after `j` key rotations. -/
@[expose] def recs (j : ℕ) (l : List (Rc n (Bl K))) :
    List (Bool × List (Option (Bl K))) :=
  l.map fun r => (r.1, rot j r.2)

/-- The canonical distribution rounds for radix pass `j`. -/
@[expose] def dl (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) : List (Dr K) :=
  l.map fun r => ⟨r.1, r.2 ⟨j, hj⟩, rst j r.2⟩

omit [Fintype K] [DecidableEq K] in
theorem dIn_dl (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) :
    dIn (dl j hj l) = recs j l := by
  rw [dIn, dl, recs, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, rot_cons hj]

omit [Fintype K] in
theorem dOut_dl (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) (b : Bl K) :
    dOut b (dl j hj l) = recs (j + 1) (l.filter fun r => r.2 ⟨j, hj⟩ = b) := by
  rw [dOut, dl, recs, List.filter_map, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, rot_succ hj]

omit [Fintype K] [DecidableEq K] in
private theorem dIn_inj : Function.Injective (dIn : List (Dr K) → _) := by
  refine List.map_injective_iff.2 ?_
  rintro ⟨f, b, w⟩ ⟨f', b', w'⟩ h
  simp only [Prod.mk.injEq, List.cons.injEq, Option.some.injEq] at h
  rw [h.1, h.2.1, h.2.2]

omit [Fintype K] [DecidableEq K] in
private theorem fIn_inj : Function.Injective (fIn : List (Rk K) → _) := by
  refine List.map_injective_iff.2 ?_
  rintro ⟨f, w⟩ ⟨f', w'⟩ h
  simp only [Prod.mk.injEq, List.cons.injEq, true_and] at h
  rw [h.1, List.map_injective_iff.2 (Option.some_injective _) h.2]

omit [Fintype K] [DecidableEq K] in
theorem fOut_inj : Function.Injective (fOut : List (Rk K) → _) := by
  refine List.map_injective_iff.2 ?_
  rintro ⟨f, w⟩ ⟨f', w'⟩ h
  simp only [Prod.mk.injEq] at h
  rw [h.1, List.map_injective_iff.2 (Option.some_injective _) h.2]

/-- Wrap a tape word free of `bar` into `List (NB M K)`. -/
@[expose] def toNB (w : List (Sy M K)) (h : Sy.bar ∉ w) : List (NB M K) :=
  w.attachWith _ fun _ hγ e => h (e ▸ hγ)

omit [Fintype K] [DecidableEq K] in
theorem toNB_val (w : List (Sy M K)) (h : Sy.bar ∉ w) :
    (toNB w h).map Subtype.val = w := by
  rw [toNB, List.attachWith_map_subtype_val]

omit [Fintype K] [DecidableEq K] in
private theorem nb_inj : Function.Injective (List.map (Subtype.val : NB M K → Sy M K)) :=
  List.map_injective_iff.2 Subtype.val_injective

/-- The canonical sorting pass `j` on record list `l`. -/
@[expose] def cps (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) : Ps M K :=
  (dl j hj l, fun b => toNB (encW (dOut b (dl j hj l))) (bar_encW _))

private theorem cOut_cps (j : ℕ) (hj : j < n) (l : List (Rc n (Bl K))) :
    cOut (cps (M := M) j hj l).2 = encW (recs (j + 1) (pass (bsl K) ⟨j, hj⟩ l)) := by
  rw [cOut, List.map_flatMap]
  simp only [cps, toNB_val, dOut_dl]
  rw [pass, recs, List.map_flatMap, encW, List.flatMap_assoc]
  rfl

/-- All `k` canonical radix-sort passes starting from coordinate `j`. -/
@[expose] noncomputable def canon (l : List (Rc n (Bl K))) : ℕ → ℕ → List (Ps M K)
  | 0, _ => []
  | k + 1, j => if hj : j < n then cps j hj (srt (bsl K) l j) :: canon l k (j + 1) else []

/-- The sorted list of records with keys materialized as lists. -/
@[expose] noncomputable def finL (l : List (Rc n (Bl K))) : List (Rk K) :=
  (srt (bsl K) l n).map fun r => (r.1, List.ofFn r.2)

theorem recs_last (l : List (Rc n (Bl K))) : recs n (srt (bsl K) l n) = fIn (finL l) := by
  rw [recs, fIn, finL, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  simp only [Function.comp_apply, rot_last]

theorem srt_ne_nil {l : List (Rc n (Bl K))} (hl : l ≠ []) (j : ℕ) :
    srt (bsl K) l j ≠ [] := by
  intro h
  have h1 := length_srt (B := Bl K) mem_bsl bsl_nodup l j
  rw [h] at h1
  exact hl (List.length_eq_zero_iff.1 h1.symm)

omit [DecidableEq K] in
theorem bar_cOut (m : Bl K → List (NB M K)) : (Sy.bar : Sy M K) ∉ cOut m := by
  rw [cOut, List.mem_map]
  rintro ⟨γ, -, h⟩
  exact γ.2 h

/-- Tape-matching on the passes and final read forces both to be the canonical ones. -/
theorem passes_iff {l : List (Rc n (Bl K))} (hl : l ≠ []) (k j : ℕ) (hjk : j + k = n)
    (ps : List (Ps M K)) (fin : List (Rk K)) :
    ((encW (recs j (srt (bsl K) l j)) :: ps.map fun p => cOut p.2) =
        (ps.map fun p => encW (dIn p.1)) ++ [encW (fIn fin)] ∧
      ∀ p ∈ ps, ∀ b, encW (dOut b p.1) = (p.2 b).map Subtype.val) ↔
      ps = canon l k j ∧ fin = finL l := by
  induction k generalizing j ps with
  | zero =>
    obtain rfl : j = n := by omega
    rw [recs_last]
    rcases ps with _ | ⟨p, ps⟩
    · simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true, canon, true_and]
      constructor
      · rintro ⟨h, -⟩
        exact (fIn_inj (encW_inj h)).symm
      · rintro rfl
        exact ⟨rfl, by simp⟩
    · simp only [canon, reduceCtorEq, false_and, iff_false]
      rintro ⟨h, -⟩
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
      have h1 := encW_inj h.1
      have hne : srt (bsl K) l j ≠ [] := srt_ne_nil hl j
      rw [finL] at h1
      obtain ⟨r, l', hr⟩ := List.exists_cons_of_ne_nil hne
      rw [hr] at h1
      rcases hp : p.1 with _ | ⟨d, d'⟩ <;> (rw [hp] at h1; simp [fIn, dIn] at h1)
  | succ k ih =>
    have hj : j < n := by omega
    have hne : srt (bsl K) l j ≠ [] := srt_ne_nil hl j
    rw [canon, dite_eq_left hj]
    rcases ps with _ | ⟨p, ps⟩
    · simp only [reduceCtorEq, false_and, iff_false]
      rintro ⟨h, -⟩
      simp only [List.map_nil, List.nil_append, List.cons.injEq, and_true] at h
      have h1 := encW_inj h
      obtain ⟨r, l', hr⟩ := List.exists_cons_of_ne_nil hne
      rw [hr, recs, List.map_cons, rot_cons hj] at h1
      rcases fin with _ | ⟨d, d'⟩ <;> simp [fIn] at h1
    · have hs : srt (bsl K) l (j + 1) = pass (bsl K) ⟨j, hj⟩ (srt (bsl K) l j) := by
        rw [srt, dite_eq_left hj]
      have key : (encW (recs j (srt (bsl K) l j)) : List (Sy M K)) = encW (dIn p.1) →
          (∀ b, encW (dOut b p.1) = (p.2 b).map Subtype.val) →
          p = cps j hj (srt (bsl K) l j) := by
        intro h1 h2
        have h3 : p.1 = dl j hj (srt (bsl K) l j) := by
          have heq := encW_inj h1
          rw [← dIn_dl j hj] at heq
          exact (dIn_inj heq).symm
        refine Prod.ext h3 ?_
        funext b
        apply nb_inj
        rw [← h2 b, h3]
        exact (toNB_val _ (bar_encW _)).symm
      constructor
      · rintro ⟨h, h2⟩
        simp only [List.map_cons, List.cons_append, List.cons.injEq] at h
        have hp := key h.1 fun b => h2 p (by simp) b
        subst hp
        rw [cOut_cps, ← hs] at h
        obtain ⟨h3, h4⟩ := (ih (j + 1) (by omega) ps).1
          ⟨h.2, fun q hq => h2 q (by simp [hq])⟩
        exact ⟨by rw [h3], h4⟩
      · rintro ⟨h, h2⟩
        rw [List.cons.injEq] at h
        obtain ⟨rfl, h3⟩ := h
        obtain ⟨h4, h5⟩ := (ih (j + 1) (by omega) ps).2 ⟨h3, h2⟩
        refine ⟨?_, ?_⟩
        · simp only [List.map_cons, List.cons_append, List.cons.injEq]
          refine ⟨by rw [cps, dIn_dl], ?_⟩
          rw [cOut_cps, ← hs]
          exact h4
        · intro q hq b
          rw [List.mem_cons] at hq
          rcases hq with rfl | hq
          · exact (toNB_val _ (bar_encW _)).symm
          · exact h5 q hq b

/-- Matched-tape condition for the sorting loop starting from initial block `w` on `ls`. -/
structure IMU (x : XU M K) (w : List (Sy M K)) : Prop where
  /-- list tape matches: initial block `w`, separator `bar`, then collected passes -/
  ls : w ++ Sy.bar :: emU x lsF = emU x lsT
  /-- every bucket tape agrees on write and read sides -/
  bk : ∀ b, emU x (.tp (.bk b) false) = emU x (.tp (.bk b) true)
  /-- both comparison copy tapes agree on write and read sides -/
  cm : ∀ k, emU x (.tp (.cm k) false) = emU x (.tp (.cm k) true)

theorem imu_iff {l : List (Rc n (Bl K))} (hl : l ≠ [])
    (x : XU M K) :
    IMU x (encW (recs 0 l)) ↔
      x.passes = canon l n 0 ∧ x.final = finL l ∧ PlG x.cmp = finL l ∧ QlG x.cmp = finL l := by
  have h0 := passes_iff hl n 0 (by omega) x.passes x.final
  change ((encW (recs 0 l) :: x.passes.map fun p => cOut p.2) =
      (x.passes.map fun p => encW (dIn p.1)) ++ [encW (fIn x.final)] ∧
      ∀ p ∈ x.passes, ∀ b, encW (dOut b p.1) = (p.2 b).map Subtype.val) ↔
    x.passes = canon l n 0 ∧ x.final = finL l at h0
  have e1 : (encW (recs 0 l) ++ Sy.bar :: emU x lsF = emU x lsT) ↔
      (encW (recs 0 l) :: x.passes.map fun p => cOut p.2) =
        (x.passes.map fun p => encW (dIn p.1)) ++ [encW (fIn x.final)] := by
    rw [emU_lsF, emU_lsT, ← blocks_cons]
    constructor
    · intro h
      refine blocks_inj ?_ ?_ h
      · intro w hw
        rw [List.mem_cons, List.mem_map] at hw
        rcases hw with rfl | ⟨p, -, rfl⟩
        · exact bar_encW _
        · exact bar_cOut _
      · intro w hw
        rw [List.mem_append, List.mem_map, List.mem_singleton] at hw
        rcases hw with ⟨p, -, rfl⟩ | rfl <;> exact bar_encW _
    · intro h
      rw [h]
  have e2 : (∀ b, emU x (.tp (.bk b) false) = emU x (.tp (.bk b) true)) ↔
      ∀ p ∈ x.passes, ∀ b, encW (dOut b p.1) = (p.2 b).map Subtype.val := by
    have e3 : ∀ b, emU x (.tp (.bk b) false) = emU x (.tp (.bk b) true) ↔
        ∀ p ∈ x.passes, encW (dOut b p.1) = (p.2 b).map Subtype.val := by
      intro b
      rw [emU_bk_false, emU_bk_true]
      constructor
      · intro h p hp
        have h2 := blocks_inj (by
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨p', -, rfl⟩ := hw
          exact bar_encW _) (by
          intro w hw
          rw [List.mem_map] at hw
          obtain ⟨p', -, rfl⟩ := hw
          rw [List.mem_map]
          rintro ⟨γ, -, hg⟩
          exact γ.2 hg) h
        exact List.map_inj_left.1 h2 p hp
      · intro h
        rw [List.map_congr_left h]
    exact ⟨fun h p hp b => (e3 b).1 (h b) p hp, fun h b => (e3 b).2 fun p hp => h p hp b⟩
  have e4 : (∀ k, emU x (.tp (.cm k) false) = emU x (.tp (.cm k) true)) ↔
      x.final = PlG x.cmp ∧ x.final = QlG x.cmp := by
    simp only [emU_cm_false, emU_cm_true]
    constructor
    · intro h
      exact ⟨fOut_inj (encW_inj (h false)), fOut_inj (encW_inj (h true))⟩
    · rintro ⟨h1, h2⟩ k
      cases k
      · simp only [Bool.false_eq_true, ↓reduceIte]; rw [h1]
      · simp only [↓reduceIte]; rw [h2]
  constructor
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨a1, a2⟩ := h0.1 ⟨e1.1 h1, e2.1 h2⟩
    obtain ⟨a3, a4⟩ := e4.1 h3
    exact ⟨a1, a2, by rw [← a3, a2], by rw [← a4, a2]⟩
  · rintro ⟨a1, a2, a3, a4⟩
    obtain ⟨b1, b2⟩ := h0.2 ⟨a1, a2⟩
    exact ⟨e1.2 b1, e2.2 b2, e4.2 ⟨by rw [a2, a3], by rw [a2, a4]⟩⟩

theorem imu_unique {l : List (Rc n (Bl K))} (hl : l ≠ [])
    {x x' : XU M K} (h : IMU x (encW (recs 0 l))) (h' : IMU x' (encW (recs 0 l))) :
    x = x' := by
  rw [imu_iff hl] at h h'
  exact XU.ext (h.1.trans h'.1.symm) (h.2.1.trans h'.2.1.symm)
    (cmpG_unique (h.2.2.1.trans h'.2.2.1.symm) (h.2.2.2.trans h'.2.2.2.symm))

theorem imu_exists {l : List (Rc n (Bl K))} (hl : l ≠ []) :
    (∃ x : XU M K, IMU x (encW (recs 0 l))) ↔ chk none (srt (bsl K) l n) := by
  have hne : finL l ≠ [] := by
    rw [finL, Ne, List.map_eq_nil_iff]
    exact srt_ne_nil hl n
  have h1 : chkG none (finL l) ↔ chk none (srt (bsl K) l n) := by
    have := chkG_map (List.ofFn : (Fin n → Bl K) → List (Bl K))
      List.ofFn_injective none (srt (bsl K) l n)
    rwa [Option.map_none] at this
  rw [← h1, ← exists_cmpG hne]
  constructor
  · rintro ⟨x, h⟩
    rw [imu_iff hl] at h
    exact ⟨x.cmp, h.2.2.1, h.2.2.2⟩
  · rintro ⟨y, h2, h3⟩
    refine ⟨⟨canon l n 0, finL l, y⟩, ?_⟩
    rw [imu_iff hl]
    exact ⟨rfl, rfl, h2, h3⟩

/-- Table entries followed by lookups: a valid matched sorting run exists iff every lookup key
belongs to the table `T`. -/
theorem imu_table (T L : List (Fin n → Bl K)) (hT : T ≠ []) :
    (∃ x : XU M K,
        IMU x (encW (recs 0 (T.map (fun x => (false, x)) ++ L.map fun x => (true, x))))) ↔
      ∀ x ∈ L, x ∈ T := by
  rw [imu_exists (by simp [hT])]
  exact chk_table mem_bsl bsl_nodup T L

end Cslib.Circuits.Arithmetic.Separation.Uni
