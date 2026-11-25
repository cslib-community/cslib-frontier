/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Uni.Alpha
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.Ring

/-!
# The radix-sorting loop on tapes

Structured run descriptions (`Tape.Runs`) for one distribution round (`Uni.Dr`, `Uni.emDr`),
bucket collection (`Uni.emCo`), a complete radix-sort pass (`Uni.Ps`, `Uni.emPs`), and the final
mark-dropping read (`Uni.emFi`).

From *VP ≠ VNP over every field* [AnthropicVPVNP2026], module `Nc.Uni.SortU`.

## Main definitions

* `Uni.lsT`, `Uni.lsF`: the read and write sides of the list tape.
* `Uni.rw'`: tape encoding of one record (flag, body with mark, dot).
* `Uni.Dr`, `Uni.emDr`: distribution round record structure and emission map.
* `Uni.Ps`, `Uni.emCo`, `Uni.emPs`, `Uni.dimPs`: bucket collection and full sorting pass.
* `Uni.bsl`: ordered list of all record key letters.
* `Uni.emFi`: final reading dropping the leading mark.

## Main results

* `Uni.runs_dr`, `Uni.runs_co`, `Uni.runs_ps`, `Uni.runs_fi`.
* `Uni.mem_bsl`, `Uni.bsl_nodup`.
-/

public section

namespace Cslib.Circuits.Arithmetic.Separation.Uni

open Finset Cslib.Automata.Weighted Cslib.Circuits.Arithmetic.Separation.Tape

/-- The list tape, read side (`true`). -/
abbrev lsT {K : Type} : Zc K := .tp .ls true

/-- The list tape, write side (`false`). -/
abbrev lsF {K : Type} : Zc K := .tp .ls false

/-- Encode a record on the list tape: flag, letters and rotation mark, then `dot`. -/
@[expose] def rw' {M K : Type} (f : Bool) (w : List (Option (Bl K))) : List (Sy M K) :=
  .flag f :: (w.map ol ++ [.dot])

/-- Tape letters other than the block-end separator `bar`. -/
abbrev NB (M K : Type) := {γ : Sy M K // γ ≠ .bar}

/-- One round of the bucket distribution: flag, leading key letter `head`, and remaining letters
`tail`. -/
@[ext]
structure Dr (K : Type) where
  /-- table entry (`false`) or lookup (`true`) flag -/
  flag : Bool
  /-- first key letter determining the target bucket -/
  head : Bl K
  /-- remaining letters and rotation mark -/
  tail : List (Option (Bl K))

/-- All record key letters listed in some fixed order. -/
@[expose] noncomputable def bsl (K : Type) [Fintype K] : List (Bl K) :=
  List.ofFn (Fintype.equivFin (Bl K)).symm

theorem mem_bsl {K : Type} [Fintype K] (b : Bl K) : b ∈ bsl K :=
  List.mem_ofFn.mpr ⟨Fintype.equivFin (Bl K) b, by simp⟩

theorem bsl_nodup {K : Type} [Fintype K] : (bsl K).Nodup :=
  List.nodup_ofFn.mpr (Equiv.injective _)

variable {A : Type*} [CommRing A] {M K : Type} [Fintype K] [DecidableEq K]

/-- Emissions of a distribution round on the list tape and the target bucket tape. -/
@[expose] def emDr (d : Dr K) : Zc K → List (Sy M K) := fun z =>
  on {lsT} (rw' d.flag (some d.head :: d.tail)) z ++
    on {.tp (.bk d.head) false} (rw' d.flag (d.tail ++ [some d.head])) z

theorem runs_dr [Finite M] :
    Runs (Fintype.card (Bl K) * (10 + 3 + (Fintype.card (Option (Bl K)) * 5 + 1) + 7))
      (emDr : Dr K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  classical
  let : Fintype M := Fintype.ofFinite M
  have h := Runs.sum (F := A) fun b : Bl K =>
    (((Runs.letter (F := A) (Z := Zc K) {lsT, .tp (.bk b) false}
        (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
      (Runs.word (F := A) {lsT} [(be b : Sy M K)])).mul
      (Runs.wordstar (F := A) {lsT, .tp (.bk b) false} ⟨lsT, by simp⟩
        (ol : Option (Bl K) → Sy M K))).mul
      (Runs.const (F := A) fun z : Zc K =>
        on {lsT} [(Sy.dot : Sy M K)] z ++ on {.tp (.bk b) false} [be b, Sy.dot] z)
  refine (h.congr
    ⟨fun d => ⟨d.head, (((d.flag, ()), d.tail), ())⟩, fun y => ⟨y.2.1.1.1, y.1, y.2.1.2⟩,
     fun _ => rfl, fun _ => rfl⟩
    (fun d z => ?_) fun _ => by simp).mono ?_
  · obtain ⟨f, b, w⟩ := d
    simp only [Equiv.coe_fn_mk, emDr, rw']
    by_cases h1 : z = lsT
    · simp [on, ol, h1]
    · by_cases h2 : z = .tp (.bk b) false
      · simp [on, ol, h2]
      · simp [on, h1, h2]
  · have hc (b : Bl K) : ({lsT, .tp (.bk b) false} : Finset (Zc K)).card = 2 :=
      Finset.card_pair (by simp)
    simp only [hc, List.length_append, Finset.sum_add_distrib, sum_on, List.length_cons,
      List.length_nil, zero_add, Finset.card_singleton, mul_one, Fintype.card_bool,
      Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact le_of_eq (by ring)

/-- Channels receiving the block-end separator `bar` during a distribution pass. -/
@[expose] def barSet : Finset (Zc K) :=
  insert lsT (univ.image fun b : Bl K => (.tp (.bk b) false : Zc K))

/-- A full radix-sort pass: a list of distribution rounds and collected non-`bar` bucket words. -/
abbrev Ps (M K : Type) := List (Dr K) × (Bl K → List (NB M K))

/-- Emissions of collecting all buckets in order `bsl K`. -/
@[expose] noncomputable def emCo (m : Bl K → List (NB M K)) : Zc K → List (Sy M K) := fun z =>
  (List.ofFn fun i =>
    on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
        ((m ((Fintype.equivFin (Bl K)).symm i)).map Subtype.val) z ++
      on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z).flatten ++
    on {lsF} [Sy.bar] z

theorem runs_co [Fintype M] :
    Runs (Fintype.card (Bl K) * (Fintype.card (Sy M K) * 5 + 1 + 3) + 1 + 3)
      (emCo : (Bl K → List (NB M K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  classical
  have h0 (i : Fin (Fintype.card (Bl K))) :
      Runs (Fintype.card (Sy M K) * 5 + 1 + 3)
        (fun (w : List (NB M K)) (z : Zc K) =>
          on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
            (w.map Subtype.val) z ++
          on {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [Sy.bar] z)
        (fun _ => (1 : A)) := by
    have h1 := (Runs.wordstar (F := A) (Z := Zc K)
          {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true, lsF}
          ⟨lsF, by simp⟩ (Subtype.val : NB M K → Sy M K)).mul
        (Runs.word (F := A) (Z := Zc K)
          {.tp (.bk ((Fintype.equivFin (Bl K)).symm i)) true} [(Sy.bar : Sy M K)])
    refine (h1.congr ⟨fun w => (w, ()), Prod.fst, fun _ => rfl, fun _ => rfl⟩
      (fun _ _ => rfl) fun _ => by simp).mono ?_
    rw [Finset.card_pair (by simp), Finset.card_singleton, List.length_singleton]
    have := Fintype.card_subtype_le (fun γ : Sy M K => γ ≠ .bar)
    omega
  have h := (Runs.pi h0).mul (Runs.word (F := A) (Z := Zc K) {lsF} [(Sy.bar : Sy M K)])
  refine (h.congr
    ⟨fun m => (fun i => m ((Fintype.equivFin (Bl K)).symm i), ()),
     fun y b => y.1 (Fintype.equivFin (Bl K) b),
     fun _ => by funext b; simp, fun ⟨_, _⟩ => by ext; simp⟩
    (fun _ _ => rfl) fun _ => by simp).mono ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul,
    Finset.card_singleton, List.length_singleton]
  omega

/-- Emissions of a complete radix-sort pass (distribution rounds, bar markers, then collection). -/
@[expose] noncomputable def emPs (p : Ps M K) : Zc K → List (Sy M K) := fun z =>
  (p.1.flatMap fun d => emDr d z) ++ (on barSet [Sy.bar] z ++ emCo p.2 z)

/-- Dimension upper bound for one radix-sort pass with alphabet size `m` and bucket count `k`. -/
@[expose] def dimPs (m k : ℕ) : ℕ :=
  (k * (10 + 3 + ((k + 1) * 5 + 1) + 7) + 1) +
    ((2 * (k + 1) + 1) + (k * (m * 5 + 1 + 3) + 1 + 3))

omit [Fintype K] in
theorem emDr_ne (d : Dr K) : ∃ z, (emDr d : Zc K → List (Sy M K)) z ≠ [] :=
  ⟨lsT, by simp [emDr, on, rw']⟩

theorem card_barSet : (barSet : Finset (Zc K)).card ≤ Fintype.card (Bl K) + 1 :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right Finset.card_image_le 1)

theorem runs_ps [Fintype M] : Runs (dimPs (Fintype.card (Sy M K)) (Fintype.card (Bl K)))
    (emPs : Ps M K → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  classical
  refine ((((runs_dr (A := A) (M := M) (K := K)).kstar emDr_ne).mul
      ((Runs.word (F := A) (Z := Zc K) barSet [(Sy.bar : Sy M K)]).mul
        (runs_co (A := A) (M := M) (K := K)))).congr (em' := emPs) (wt' := fun _ => (1 : A))
    ⟨fun p => (p.1, (), p.2), fun y => (y.1, y.2.2), fun _ => rfl, fun _ => rfl⟩
    (fun _ _ => rfl) fun _ => by simp).mono ?_
  have : (barSet : Finset (Zc K)).card ≤ Fintype.card (Bl K) + 1 := card_barSet
  simp only [dimPs, Fintype.card_option, List.length_singleton, mul_one]
  omega

/-- Emissions of the final reading: rotation marks have returned to the front and are dropped
while copying records to both comparison tapes `cm false` and `cm true`. -/
@[expose] def emFi (l : List (Bool × List (Bl K))) : Zc K → List (Sy M K) := fun z =>
  (l.flatMap fun d => on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
    on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z) ++
    on {lsT} [Sy.bar] z

theorem runs_fi [Finite M] : Runs (14 + 3 + (Fintype.card (Bl K) * 7 + 1) + 7 + 1 + 3)
    (emFi : List (Bool × List (Bl K)) → Zc K → List (Sy M K)) (fun _ => (1 : A)) := by
  classical
  let : Fintype M := Fintype.ofFinite M
  have hc : ({lsT, .tp (.cm false) false, .tp (.cm true) false} : Finset (Zc K)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp), Finset.card_pair (by simp)]
  have h2 := ((((Runs.letter (F := A) (Z := Zc K)
        {lsT, .tp (.cm false) false, .tp (.cm true) false}
        (fun f : Bool => (Sy.flag f : Sy M K)) (fun _ => 1)).mul
      (Runs.word (F := A) {lsT} [(Sy.mark : Sy M K)])).mul
      (Runs.wordstar (F := A) {lsT, .tp (.cm false) false, .tp (.cm true) false}
        ⟨lsT, by simp⟩ (be : Bl K → Sy M K))).mul
      (Runs.word (F := A) {lsT, .tp (.cm false) false, .tp (.cm true) false}
        [(Sy.dot : Sy M K)])).congr
    (em' := fun (d : Bool × List (Bl K)) z =>
      on {lsT} (rw' d.1 (none :: d.2.map some)) z ++
        on {.tp (.cm false) false, .tp (.cm true) false} (rw' d.1 (d.2.map some)) z)
    (wt' := fun _ => 1)
    ⟨fun d => (((d.1, ()), d.2), ()), fun y => (y.1.1.1, y.1.2), fun _ => rfl, fun _ => rfl⟩
    (fun ⟨f, w⟩ z => by
      have hw : (w.map some).map (ol : Option (Bl K) → Sy M K) = w.map be := by
        rw [List.map_map]; rfl
      simp only [Equiv.coe_fn_mk, rw', List.map_cons, hw]
      by_cases h1 : z = lsT
      · simp [on, ol, h1]
      · by_cases h2 : z = .tp (.cm false) false
        · simp [on, h2]
        · by_cases h3 : z = .tp (.cm true) false
          · simp [on, h3]
          · simp [on, h1, h2, h3])
    (fun _ => by simp)
  refine (((h2.kstar fun _ => ⟨lsT, by simp [on, rw']⟩).mul
      (Runs.word (F := A) (Z := Zc K) {lsT} [(Sy.bar : Sy M K)])).congr
    ⟨fun l => (l, ()), Prod.fst, fun _ => rfl, fun _ => rfl⟩
    (fun _ _ => rfl) fun _ => by simp).mono (by rw [hc]; simp)

end Cslib.Circuits.Arithmetic.Separation.Uni
