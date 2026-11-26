/-
Copyright (c) 2026 Clément Trecourt, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Clément Trecourt, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Ladner.Basic
public import CslibFrontier.Computability.Complexity.Classes.NP.Relation
public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Complexity.Problems.SAT
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Clocked
import CslibFrontier.Computability.Complexity.Classes.Ladner.PolyTime
import CslibFrontier.Computability.Complexity.Classes.NP.SelfReduction
import CslibFrontier.Computability.Complexity.Classes.P.Complement
import CslibFrontier.Computability.Complexity.Problems.SAT.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Sum
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.IterateWhile
import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.PolyTime

/-!
# Levin's universal search

Levin's universal search ([Levin1973]; [Goldreich, Theorem 2.33][Goldreich2008]; primary PDF
locators not verified against primary PDFs) searches for a witness of a polynomial-time verifiable
search problem by dovetailing over all Turing machine descriptions and verifying each halted
output.

Given an instance encoding `enc : α ↪ List Bool` and a verifier `V : α × List Bool → Bool`,
stage `K` (`Cslib.Complexity.levinStage`) runs the machines with indices `i < K` in the
enumeration `Cslib.Complexity.Ladner.word` for `K` steps each on `enc a` via
`Turing.MultiTapeTM.Universal.runWord`, and returns the first halted output `w` accepted by `V`.
When `V` is polynomial-time, `levinStage` is polynomial-time with `K` in unary
(`Cslib.Complexity.computableInPolyTime_levinStage`).

Packaging the unbounded stage loop `K = 0, 1, 2, …` through
`Turing.MultiTapeTM.exists_partial_iterateWhile` yields one fixed binary multi-tape Turing machine
(`Cslib.Complexity.exists_native_levinSearch`, instantiated for NP relations as
`Cslib.Complexity.NPRelation.exists_native_levinSearch` and for `SAT` as
`Cslib.Complexity.SAT.exists_native_levinSearch`).

## Modeling conventions and deviations from sources

* **Halting domain vs. total SAT decision:** Levin's universal search halts with a verified
  witness on yes-instances and **diverges** (`¬ tm.Halts (enc a)`) on no-instances. It is not a
  total SAT decider; whether a fixed total SAT decider runs in polynomial time iff `P = NP` is not
  claimed here.
* **Polynomial universal-simulation overhead:** Because `Turing.MultiTapeTM.Universal.universal`
  simulates a described machine for `t` steps in time polynomial in `|d| + |x| + t` (rather than
  the Hennie–Stearns `O(t log t)` multi-tape universal simulator or a unit-cost RAM), our native
  universal searcher achieves polynomial optimality: there is a universal exponent `D` (depending
  only on `enc` and `V`, not on any competing solver) such that for every finite-state binary
  multi-tape machine `M`, there is a constant `C_M` (exponential in the description length of `M`)
  for which `tm` solves every instance solved by `M` in `T` steps within time and space
  `C_M * (T + |enc a| + 1) ^ D`. In particular, for `SAT` the fixed native machine runs in
  polynomial time on satisfiable formulas if and only if `P = NP` for every encoding.

## Main definitions

* `Cslib.Complexity.levinStage`: stage `K` of Levin's universal search for an encoded verifier.
* `Cslib.Complexity.SAT.levinStage`: stage `K` of Levin's universal search for `SAT`.

## Main results

* `Cslib.Complexity.verifier_of_levinStage_eq_some`,
  `Cslib.Complexity.length_le_of_levinStage_eq_some`,
  `Cslib.Complexity.isSome_levinStage_iff`,
  `Cslib.Complexity.isSome_levinStage_mono`,
  `Cslib.Complexity.exists_levinStage_eq_some_iff`: soundness, output-length bound, monotonicity,
  and completeness of `levinStage`.
* `Cslib.Complexity.exists_index_le_two_pow_levinStage_isSome`,
  `Cslib.Complexity.exists_index_levinStage_isSome`: stage optimality against any finite-state
  multi-tape machine (the former with the explicit `2 ^ (2 * |eDesc d| + 2)` description-index
  bound).
* `Cslib.Complexity.computableInPolyTime_levinStage`: `levinStage` is polynomial-time with `K` in
  unary.
* `Cslib.Complexity.exists_native_levinSearch`,
  `Cslib.Complexity.NPRelation.exists_native_levinSearch`: fixed native universal search machine
  with soundness, exact halting domain (divergence on no-instances), stage-bounded runtime, and
  polynomial optimality against every solver.
* `Cslib.Complexity.SAT.exists_poly_levinStage_iff`: stage-level `SAT` characterization
  (polynomial stage bound on satisfiable formulas iff `P = NP`).
* `Cslib.Complexity.SAT.exists_native_levinSearch`: one fixed native `MultiTapeTM` for `SAT`
  that halts with a verified assignment iff `φ ∈ SAT`, diverges on unsatisfiable formulas, is
  polynomially optimal against every witness-finding machine, and halts in polynomial time on
  satisfiable formulas iff `P = NP`.

## References

* [L. A. Levin, *Universal Sequential Search Problems*][Levin1973] (locator not verified against
  primary PDF)
* [O. Goldreich, *Computational Complexity: A Conceptual Perspective*, Theorem 2.33][Goldreich2008]
  (locator not verified against primary PDF)
-/

public section

namespace Cslib.Complexity

open Turing Turing.MultiTapeTM Turing.MultiTapeTM.Universal ComputableInPolyTime

section General

variable {α : Type}

/-- Run the `i`-th enumerated machine on `enc a` for `t` steps and return its output word if it
halts and passes the verifier `V`. -/
private def levinTry (enc : α ↪ List Bool) (V : α × List Bool → Bool) (a : α) (i t : ℕ) :
    Option (List Bool) :=
  (runWord (decodeDesc (unframe (Ladner.word i))) (enc a) t).elim none fun w =>
    if V (a, w) then some w else none

private theorem levinTry_eq_some_iff {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    {a : α} {i t : ℕ} {w : List Bool} :
    levinTry enc V a i t = some w ↔
      runWord (decodeDesc (unframe (Ladner.word i))) (enc a) t = some w ∧ V (a, w) = true := by
  unfold levinTry
  cases runWord (decodeDesc (unframe (Ladner.word i))) (enc a) t <;> simp
  grind

/-- **Stage `K` of Levin's universal search** for a verifier `V` on instances encoded by `enc`:
checks the machines with indices `i < K` (in the enumeration `Cslib.Complexity.Ladner.word`),
each run for `K` steps on `enc a` via `Turing.MultiTapeTM.Universal.runWord`, and returns the
first halted output accepted by `V`. -/
@[expose] def levinStage (enc : α ↪ List Bool) (V : α × List Bool → Bool) (a : α) (K : ℕ) :
    Option (List Bool) :=
  let tryOne (i : ℕ) : Option (List Bool) :=
    (runWord (decodeDesc (unframe (Ladner.word i))) (enc a) K).elim none fun w =>
      if V (a, w) then some w else none
  ((List.range K).find? fun i => (tryOne i).isSome).elim none tryOne

private theorem levinStage_eq_find (enc : α ↪ List Bool) (V : α × List Bool → Bool) (a : α)
    (K : ℕ) :
    levinStage enc V a K =
      ((List.range K).find? fun i => (levinTry enc V a i K).isSome).elim none fun i =>
        levinTry enc V a i K := rfl

/-- Stage `0` runs no machines and always returns `none`. -/
@[simp]
theorem levinStage_zero (enc : α ↪ List Bool) (V : α × List Bool → Bool) (a : α) :
    levinStage enc V a 0 = none := rfl

private theorem levinTry_of_levinStage_eq_some {enc : α ↪ List Bool}
    {V : α × List Bool → Bool} {a : α} {K : ℕ} {w : List Bool}
    (h : levinStage enc V a K = some w) :
    ∃ i, levinTry enc V a i K = some w := by
  rw [levinStage_eq_find] at h
  cases hf : (List.range K).find? (fun i => (levinTry enc V a i K).isSome) with
  | none => simp [hf] at h
  | some i => exact ⟨i, by simpa only [hf, Option.elim_some] using h⟩

/-- **Soundness of `levinStage`:** every certificate returned by stage `K` is accepted by `V`. -/
theorem verifier_of_levinStage_eq_some {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    {a : α} {K : ℕ} {w : List Bool} (h : levinStage enc V a K = some w) :
    V (a, w) = true :=
  let ⟨_, hi⟩ := levinTry_of_levinStage_eq_some h
  (levinTry_eq_some_iff.mp hi).2

/-- Any certificate returned by stage `K` has length at most `K` (a machine emits at most one bit
per simulated step). -/
theorem length_le_of_levinStage_eq_some {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    {a : α} {K : ℕ} {w : List Bool} (h : levinStage enc V a K = some w) :
    w.length ≤ K :=
  let ⟨_, hi⟩ := levinTry_of_levinStage_eq_some h
  length_le_of_runWord_eq_some (levinTry_eq_some_iff.mp hi).1

/-- Stage `K` succeeds iff some machine with index `i < K` halts within `K` steps on `enc a` with
a certificate accepted by `V`. -/
theorem isSome_levinStage_iff {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    {a : α} {K : ℕ} :
    (levinStage enc V a K).isSome ↔
      ∃ i < K, ∃ w, runWord (decodeDesc (unframe (Ladner.word i))) (enc a) K = some w ∧
        V (a, w) = true := by
  rw [levinStage_eq_find]
  cases hf : (List.range K).find? (fun i => (levinTry enc V a i K).isSome) with
  | none =>
    simp only [Option.elim_none, Option.isSome_none, Bool.false_eq_true, false_iff, not_exists,
      not_and]
    intro i hi w hrun hv
    simpa [levinTry_eq_some_iff.mpr ⟨hrun, hv⟩] using
      List.find?_eq_none.mp hf i (List.mem_range.mpr hi)
  | some i =>
    have hspec := List.find?_some hf
    have hmem := List.mem_range.mp (List.mem_of_find?_eq_some hf)
    simp only [Option.elim_some, hspec, true_iff]
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hspec
    exact ⟨i, hmem, w, levinTry_eq_some_iff.mp hw⟩

/-- Monotonicity of `levinStage` in the stage index: once some stage succeeds, every later stage
also succeeds. -/
theorem isSome_levinStage_mono {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    {a : α} {K₁ K₂ : ℕ} (hK : K₁ ≤ K₂) (h : (levinStage enc V a K₁).isSome) :
    (levinStage enc V a K₂).isSome := by
  obtain ⟨i, hi, w, hrun, hv⟩ := isSome_levinStage_iff.mp h
  exact isSome_levinStage_iff.mpr ⟨i, lt_of_lt_of_le hi hK, w, runWord_mono hK hrun, hv⟩

/-- Explicit exponential upper bound on the enumeration index of a finite-state machine's
description: `i₀ + 2 ≤ 2 ^ (2 * (eDesc (desc eS eBit M)).length + 2)`, and whenever `M` halts
within `T` steps on `enc a` with a `V`-accepted output, stage `K` succeeds for every
`K ≥ max (i₀ + 1) T`. -/
theorem exists_index_le_two_pow_levinStage_isSome {enc : α ↪ List Bool}
    {V : α × List Bool → Bool} {k : ℕ} {State : Type} [Fintype State]
    (eS : State ↪ ℕ) (M : MultiTapeTM k Bool State) :
    ∃ i₀ : ℕ, i₀ + 2 ≤ 2 ^ (2 * (eDesc (desc eS eBit M)).length + 2) ∧
      ∀ (a : α) (T K : ℕ),
        (M.runFrom (M.initCfg (enc a)) T).Halted →
        V (a, (M.runFrom (M.initCfg (enc a)) T).output) = true →
        max (i₀ + 1) T ≤ K →
        (levinStage enc V a K).isSome = true := by
  let d : Desc := desc eS eBit M
  let i₀ : ℕ := Ladner.index (frame (eDesc d))
  refine ⟨i₀, ?_, fun a T K hhalt hv hK => ?_⟩
  · simpa only [i₀, length_frame] using Ladner.index_add_two_le (frame (eDesc d))
  · refine isSome_levinStage_iff.mpr ⟨i₀, by omega, _, ?_, hv⟩
    simpa only [i₀, Ladner.word_index, unframe_frame, decodeDesc_eDesc] using
      runWord_desc_of_halted eS M hhalt (by omega)

/-- **Stage optimality against every finite-state machine.** For every finite-state binary
`MultiTapeTM` `M`, there is a fixed description index `i₀` (depending only on `M`) such that
whenever `M` halts within `T` steps on `enc a` with a `V`-accepted output, stage `K` succeeds for
every `K ≥ max (i₀ + 1) T`. -/
theorem exists_index_levinStage_isSome {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    {k : ℕ} {State : Type} [Finite State] (M : MultiTapeTM k Bool State) :
    ∃ i₀ : ℕ, ∀ (a : α) (T K : ℕ),
      (M.runFrom (M.initCfg (enc a)) T).Halted →
      V (a, (M.runFrom (M.initCfg (enc a)) T).output) = true →
      max (i₀ + 1) T ≤ K →
      (levinStage enc V a K).isSome = true := by
  have := Fintype.ofFinite State
  exact (exists_index_le_two_pow_levinStage_isSome (enc := enc) (V := V)
    ((Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding) M).imp fun _ => And.right

/-- **Soundness and completeness of `levinStage`:** some stage returns a certificate on `a` if and
only if `a` has a `V`-accepted witness. -/
theorem exists_levinStage_eq_some_iff {enc : α ↪ List Bool} {V : α × List Bool → Bool} {a : α} :
    (∃ K w, levinStage enc V a K = some w) ↔ ∃ w, V (a, w) = true := by
  constructor
  · rintro ⟨K, w, hw⟩
    exact ⟨w, verifier_of_levinStage_eq_some hw⟩
  · rintro ⟨w, hw⟩
    obtain ⟨t, s, -, -, k, State, hfin, tm, htm⟩ :=
      ComputableInPolyTime.const (encIn := enc) (encOut := encBits) w
    obtain ⟨i₀, hi₀⟩ := exists_index_levinStage_isSome (enc := enc) (V := V) tm
    have hrun := (htm a).runFrom_of_le le_rfl
    obtain ⟨w', hw'⟩ := Option.isSome_iff_exists.mp
      (hi₀ a _ (max (i₀ + 1) (t (enc a).length)) hrun.1 (hrun.2.symm ▸ hw) le_rfl)
    exact ⟨_, w', hw'⟩

/-- **Stage `K` of Levin's universal search is polynomial-time** with `K` written in unary. -/
@[fun_prop]
theorem computableInPolyTime_levinStage {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (fun p : α × ℕ => levinStage enc V p.1 p.2)
      (encPair enc encUnary) (encOption encBits) := by
  have htry : ComputableInPolyTime
      (fun (p : (α × ℕ) × ℕ) => levinTry enc V p.1.1 p.2 p.1.2)
      (encPair (encPair enc encUnary) encUnary) (encOption encBits) := by
    have hrun : ComputableInPolyTime
        (fun p : (α × ℕ) × ℕ =>
          runWord (decodeDesc (unframe (Ladner.word p.2))) (enc p.1.1) p.1.2)
        (encPair (encPair enc encUnary) encUnary) (encOption encBits) :=
      computableInPolyTime_runWord (by fun_prop)
        (encoding_comp ((fst enc encUnary).comp (fst _ _)))
        ((snd enc encUnary).comp (fst _ _))
    refine hrun.optionElimWithInput (const none) ?_
    have hq1 :=
      (fst enc encUnary).comp ((fst (encPair enc encUnary) encUnary).comp (fst _ encBits))
    have hq2 := snd (encPair (encPair enc encUnary) encUnary) encBits
    exact ite' (hV.comp (hq1.prod hq2)) ((optionSome encBits).comp hq2) (const none)
  have hfind : ComputableInPolyTime
      (fun p : α × ℕ => (List.range p.2).find? fun i => (levinTry enc V p.1 i p.2).isSome)
      (encPair enc encUnary) (encOption encUnary) :=
    findWithInput (range.comp (snd enc encUnary)) (optionIsSome htry)
  exact hfind.optionElimWithInput (const none) htry

/-! ### Native dovetailed universal search machine -/

/-- State of the dovetailed stage loop: `some (.inl (a, K))` searches stage `K` on `a`,
`some (.inr w)` holds a verified witness `w` ready to output, and `none` triggers loop exit. -/
private abbrev SearchState (α : Type) := Option ((α × ℕ) ⊕ List Bool)

/-- Encoding of `SearchState α`: `none` is empty (`[]`), `some (.inl (a, K))` encodes the instance
and unary stage counter, and `some (.inr w)` encodes the witness. -/
private abbrev encSearchState (enc : α ↪ List Bool) : SearchState α ↪ List Bool :=
  encOption (encSum (encPair enc encUnary) encBits)

private def searchInit (a : α) : SearchState α := some (.inl (a, 0))

private def searchStep (enc : α ↪ List Bool) (V : α × List Bool → Bool)
    (s : SearchState α) : SearchState α :=
  s.elim none (Sum.elim
    (fun p => (levinStage enc V p.1 p.2).elim (some (.inl (p.1, p.2 + 1))) (fun w => some (.inr w)))
    (fun _ => none))

private def searchFin (s : SearchState α) : List Bool :=
  s.elim [] (Sum.elim (fun _ => []) id)

private theorem searchStep_iterate_of_none {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    {a : α} :
    ∀ n, (∀ m < n, levinStage enc V a m = none) →
      (searchStep enc V)^[n] (searchInit a) = some (.inl (a, n))
  | 0, _ => rfl
  | n + 1, h => by
    rw [Function.iterate_succ_apply',
      searchStep_iterate_of_none n fun m hm => h m (Nat.lt_succ_of_lt hm)]
    simp [searchStep, h n (Nat.lt_succ_self n)]

private theorem computableInPolyTime_searchInit (enc : α ↪ List Bool) :
    ComputableInPolyTime (searchInit (α := α)) enc (encSearchState enc) :=
  (optionSome _).comp ((sumInl _ _).comp (id'.prod (const 0)))

private theorem computableInPolyTime_searchStep {enc : α ↪ List Bool}
    {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ComputableInPolyTime (searchStep enc V) (encSearchState enc) (encSearchState enc) := by
  have hleft : ComputableInPolyTime
      (fun p : α × ℕ => (levinStage enc V p.1 p.2).elim
        (some (.inl (p.1, p.2 + 1))) (fun w => some (.inr w)))
      (encPair enc encUnary) (encSearchState enc) :=
    (computableInPolyTime_levinStage hV).optionElimWithInput
      ((optionSome _).comp ((sumInl _ _).comp ((fst enc encUnary).prod (by fun_prop))))
      ((optionSome _).comp ((sumInr _ _).comp (snd (encPair enc encUnary) encBits)))
  exact id'.optionElimWithInput (const none)
    ((sumElim hleft (const none)).comp (snd (encSearchState enc) _))

private theorem computableInPolyTime_searchFin (enc : α ↪ List Bool) :
    ComputableInPolyTime (searchFin (α := α)) (encSearchState enc) encBits :=
  id'.optionElimWithInput (const []) ((sumElim (const []) id').comp (snd (encSearchState enc) _))

/-- **Native universal search machine for any polynomial-time verifier** (after
[Levin][Levin1973] and [Goldreich, Theorem 2.33][Goldreich2008]; primary PDF locators not
verified). For any polynomial-time verifier `V` on instances encoded by `enc`, there exists one
fixed finite-state binary `MultiTapeTM` `tm` and fixed universal constants `C, D` (depending only
on `enc` and `V`) such that:
1. **Soundness:** whenever `tm` halts on `enc a` with output `w`, `V (a, w) = true`.
2. **Exact halting domain:** `tm` halts on `enc a` iff `∃ w, V (a, w) = true` (in particular, `tm`
   diverges on every no-instance).
3. **Stage-bounded running time:** whenever stage `K` succeeds on `a`, `tm` halts on `enc a` with
   a `V`-accepted witness within time and space `C * (K + (enc a).length + 1) ^ D`.
4. **Polynomial optimality against every solver:** for every finite-state binary `MultiTapeTM` `M`,
   there is a constant `C_M` (depending only on `M`, `enc`, and `V`) such that whenever `M` halts
   within `T` steps on `enc a` with a `V`-accepted output, `tm` halts with a `V`-accepted output
   within time and space `C_M * (T + (enc a).length + 1) ^ D`. -/
theorem exists_native_levinSearch {enc : α ↪ List Bool} {V : α × List Bool → Bool}
    (hV : ComputableInPolyTime V (encPair enc encBits) encBool) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (C D : ℕ),
      (∀ a w, tm.Computes (enc a) w → V (a, w) = true) ∧
      (∀ a, tm.Halts (enc a) ↔ ∃ w, V (a, w) = true) ∧
      (∀ a K, (levinStage enc V a K).isSome →
        ∃ w, V (a, w) = true ∧
          tm.ComputesInTimeAndSpace (enc a) w
            (C * (K + (enc a).length + 1) ^ D)
            (C * (K + (enc a).length + 1) ^ D)) ∧
      (∀ {k' : ℕ} {State' : Type} [Finite State'] (M : MultiTapeTM k' Bool State'),
        ∃ C_M : ℕ, ∀ (a : α) (T : ℕ),
          (M.runFrom (M.initCfg (enc a)) T).Halted →
          V (a, (M.runFrom (M.initCfg (enc a)) T).output) = true →
          ∃ w, V (a, w) = true ∧
            tm.ComputesInTimeAndSpace (enc a) w
              (C_M * (T + (enc a).length + 1) ^ D)
              (C_M * (T + (enc a).length + 1) ^ D)) := by
  classical
  obtain ⟨k, State, hfin, tm, c, d, hterm, hdiv⟩ :=
    exists_partial_iterateWhile
      (computableInPolyTime_searchInit enc)
      (computableInPolyTime_searchStep hV)
      (computableInPolyTime_searchFin enc)
  let D := d + 1
  let C := 2 * c * 4 ^ d
  have hstage : ∀ a K, (levinStage enc V a K).isSome →
      ∃ w, V (a, w) = true ∧
        tm.ComputesInTimeAndSpace (enc a) w
          (C * (K + (enc a).length + 1) ^ D)
          (C * (K + (enc a).length + 1) ^ D) := by
    intro a K hK
    have hex : ∃ m, (levinStage enc V a m).isSome := ⟨K, hK⟩
    let K₀ := Nat.find hex
    have hK₀_le : K₀ ≤ K := Nat.find_min' hex hK
    have hK₀_some : (levinStage enc V a K₀).isSome := Nat.find_spec hex
    obtain ⟨w₀, hw₀⟩ := Option.isSome_iff_exists.mp hK₀_some
    have hnone : ∀ m < K₀, levinStage enc V a m = none := fun m hm =>
      Option.not_isSome_iff_eq_none.mp (Nat.find_min hex hm)
    have hstate_le : ∀ n ≤ K₀,
        (searchStep enc V)^[n] (searchInit a) = some (.inl (a, n)) :=
      fun n hn => searchStep_iterate_of_none n fun m hm => hnone m (lt_of_lt_of_le hm hn)
    have hstate_found : (searchStep enc V)^[K₀ + 1] (searchInit a) = some (.inr w₀) := by
      rw [Function.iterate_succ_apply', hstate_le K₀ le_rfl]
      simp [searchStep, hw₀]
    have hstate_stop : (searchStep enc V)^[K₀ + 1 + 1] (searchInit a) = none :=
      (Function.iterate_succ_apply' _ (K₀ + 1) _).trans (congrArg _ hstate_found)
    have hlen_w₀ : w₀.length ≤ K₀ := length_le_of_levinStage_eq_some hw₀
    let l := 2 * (enc a).length + K₀ + 3
    have hrun := hterm a (K₀ + 1) l
      (fun n hn => by
        rcases Nat.lt_or_eq_of_le hn with hlt | rfl
        · rw [hstate_le n (Nat.lt_succ_iff.mp hlt)]
          simp only [encSearchState, encOption_some, encSum_inl, encPair_apply, encUnary_apply,
            List.length_cons, List.length_append, length_frame, List.length_replicate]
          omega
        · rw [hstate_found]
          simp only [encSearchState, encOption_some, encSum_inr, encBits_apply, List.length_cons]
          omega)
      (fun n hn => by
        rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hn) with hlt | rfl
        · simp [hstate_le (n + 1) hlt, encSearchState]
        · simp [hstate_found, encSearchState])
      (by rw [hstate_stop]; rfl)
    rw [hstate_found] at hrun
    dsimp only [searchFin, Option.elim_some, Sum.elim_inr, id_eq] at hrun
    have hbase : l + (enc a).length + 1 ≤ 4 * (K + (enc a).length + 1) := by dsimp only [l]; omega
    have hpow : (l + (enc a).length + 1) ^ d ≤ 4 ^ d * (K + (enc a).length + 1) ^ d :=
      (Nat.pow_le_pow_left hbase d).trans_eq (Nat.mul_pow _ _ _)
    have hr : K₀ + 1 + 1 ≤ 2 * (K + (enc a).length + 1) := by omega
    obtain ⟨hcomp, htime, hspace⟩ := hrun
    refine ⟨w₀, verifier_of_levinStage_eq_some hw₀, hcomp, htime.mono ?_, hspace.mono ?_⟩
    · calc _ ≤ c * (2 * (K + (enc a).length + 1)) * (4 ^ d * (K + (enc a).length + 1) ^ d) :=
            Nat.mul_le_mul (Nat.mul_le_mul_left c hr) hpow
        _ = C * (K + (enc a).length + 1) ^ D := by dsimp only [C, D]; ring
    · calc _ ≤ (2 * (K + (enc a).length + 1)) * (c * (4 ^ d * (K + (enc a).length + 1) ^ d)) :=
            (Nat.mul_le_mul_left c hpow).trans (Nat.le_mul_of_pos_left _ (by omega))
        _ = C * (K + (enc a).length + 1) ^ D := by dsimp only [C, D]; ring
  have hno : ∀ a, (¬∃ w, V (a, w) = true) → ¬tm.Halts (enc a) := by
    intro a hna
    have hnone : ∀ m, levinStage enc V a m = none := fun m => by
      cases hm : levinStage enc V a m with
      | none => rfl
      | some w => exact (hna ⟨w, verifier_of_levinStage_eq_some hm⟩).elim
    refine hdiv a fun n => ?_
    simp [searchStep_iterate_of_none (n + 1) fun m _ => hnone m, encSearchState]
  have hhalts : ∀ a, tm.Halts (enc a) ↔ ∃ w, V (a, w) = true := fun a =>
    ⟨fun hh => Classical.byContradiction fun hna => hno a hna hh, fun hex => by
      obtain ⟨K, w, hK⟩ := exists_levinStage_eq_some_iff.mpr hex
      obtain ⟨w', -, hrun⟩ := hstage a K (by rw [hK]; rfl)
      exact hrun.1.halts⟩
  have hsound : ∀ a w, tm.Computes (enc a) w → V (a, w) = true := by
    intro a w hw
    obtain ⟨K, _, hK⟩ := exists_levinStage_eq_some_iff.mpr ((hhalts a).mp hw.halts)
    obtain ⟨w', hv', hrun⟩ := hstage a K (by rw [hK]; rfl)
    exact hw.unique hrun.1 ▸ hv'
  refine ⟨k, State, hfin, tm, C, D, hsound, hhalts, hstage, ?_⟩
  intro k' State' hfin' M
  obtain ⟨i₀, hi₀⟩ := exists_index_levinStage_isSome (enc := enc) (V := V) M
  refine ⟨C * (i₀ + 2) ^ D, fun a T hhaltM hvM => ?_⟩
  obtain ⟨w, hv, hcomp, htime, hspace⟩ :=
    hstage a (max (i₀ + 1) T) (hi₀ a T (max (i₀ + 1) T) hhaltM hvM le_rfl)
  have hbound : max (i₀ + 1) T + (enc a).length + 1 ≤
      (i₀ + 1 + 1) * (T + (enc a).length + 1) := by
    have := Nat.le_mul_of_pos_right (i₀ + 1) (show 0 < T + (enc a).length + 1 by omega)
    rw [add_one_mul]
    omega
  have hmul : C * (max (i₀ + 1) T + (enc a).length + 1) ^ D ≤
      C * (i₀ + 2) ^ D * (T + (enc a).length + 1) ^ D :=
    (Nat.mul_le_mul_left C (Nat.pow_le_pow_left hbound D)).trans_eq (by rw [mul_pow]; ring)
  exact ⟨w, hv, hcomp, htime.mono hmul, hspace.mono hmul⟩

end General

/-! ### NP relations (Goldreich, Theorem 2.33) -/

namespace NPRelation

/-- **Levin's universal search for any NP relation** (after [Levin][Levin1973] and
[Goldreich, Theorem 2.33][Goldreich2008]; primary PDF locators not verified; polynomial
universal-simulation overhead as documented in the module header). -/
theorem exists_native_levinSearch {α : Type} {enc : α ↪ List Bool} (R : NPRelation enc) :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (D : ℕ),
      (∀ a w, tm.Computes (enc a) w → R.IsWitness a w) ∧
      (∀ a, tm.Halts (enc a) ↔ a ∈ R.language) ∧
      (∀ {k' : ℕ} {State' : Type} [Finite State'] (M : MultiTapeTM k' Bool State'),
        ∃ C_M : ℕ, ∀ (a : α) (T : ℕ),
          (M.runFrom (M.initCfg (enc a)) T).Halted →
          R.IsWitness a (M.runFrom (M.initCfg (enc a)) T).output →
          ∃ w, R.IsWitness a w ∧
            tm.ComputesInTimeAndSpace (enc a) w
              (C_M * (T + (enc a).length + 1) ^ D)
              (C_M * (T + (enc a).length + 1) ^ D)) := by
  let V : α × List Bool → Bool := fun p =>
    decide (p.2.length = R.certLength.eval (enc p.1).length) && R.verifier p
  have hV_iff (a : α) (w : List Bool) : V (a, w) = true ↔ R.IsWitness a w := by
    simp [V, NPRelation.isWitness_iff]
  have hV_poly : ComputableInPolyTime V (encPair enc encBits) encBool :=
    bool_and'
      (decide_eq' (length_bits.comp (snd enc encBits))
        ((unary_eval R.certLength).comp ((encoding_length enc).comp (fst enc encBits))))
      R.computableInPolyTime_verifier
  obtain ⟨k, State, hfin, tm, _, D, hsound, hhalts, _, hopt⟩ :=
    Complexity.exists_native_levinSearch hV_poly
  exact ⟨k, State, hfin, tm, D,
    fun a w hw => (hV_iff a w).mp (hsound a w hw),
    fun a => (hhalts a).trans (exists_congr fun w => hV_iff a w),
    fun {k' State'} _ M => (hopt M).imp fun C_M hM a T hhalt hW =>
      (hM a T hhalt ((hV_iff a _).mpr hW)).imp fun w ⟨hv, hrun⟩ => ⟨(hV_iff a w).mp hv, hrun⟩⟩

end NPRelation

/-! ### Universal search for SAT -/

namespace SAT

open Cslib.Logic.PL

/-- **Stage `K` of Levin's universal search for `SAT`**: runs the machines with indices `i < K`
for `K` steps each on `encCNF φ` and returns the first halted output accepted by `SAT.verifier`. -/
abbrev levinStage (φ : CNF ℕ) (K : ℕ) : Option (List Bool) :=
  Complexity.levinStage encCNF verifier φ K

private lemma exists_verifier_iff_mem {φ : CNF ℕ} :
    (∃ w, verifier (φ, w) = true) ↔ φ ∈ SAT :=
  ⟨fun ⟨w, hw⟩ => ⟨assignment φ w, hw⟩,
    fun hφ => let ⟨w, _, hw⟩ := (isVerifier φ).mp hφ; ⟨w, hw⟩⟩

/-- **Completeness and soundness of `SAT.levinStage`:** some stage succeeds on `φ` iff `φ ∈ SAT`. -/
theorem exists_levinStage_eq_some_iff {φ : CNF ℕ} :
    (∃ K w, levinStage φ K = some w) ↔ φ ∈ SAT :=
  Complexity.exists_levinStage_eq_some_iff.trans exists_verifier_iff_mem

/-- **Stage-level `P = NP` characterization for `SAT`:** there is a polynomial `p` such that every
satisfiable formula `φ` is solved by stage `p (encCNF φ).length` if and only if `P = NP` for every
encoding. -/
theorem exists_poly_levinStage_iff :
    (∃ p : Polynomial ℕ, ∀ φ ∈ SAT, (levinStage φ (p.eval (encCNF φ).length)).isSome) ↔
      ∀ {β : Type} (e : β ↪ List Bool), P e = NP e := by
  rw [← SAT_mem_P_iff]
  constructor
  · rintro ⟨p, hp⟩
    refine mem_P.mpr ⟨fun φ => (levinStage φ (p.eval (encCNF φ).length)).isSome, ?_, fun φ => ?_⟩
    · have hpair : ComputableInPolyTime (fun φ : CNF ℕ => (φ, p.eval (encCNF φ).length))
          encCNF (encPair encCNF encUnary) :=
        (ComputableInPolyTime.id' (encIn := encCNF)).prod
          ((unary_eval p).comp (encoding_length encCNF))
      exact optionIsSome (by simpa only [Function.comp_def] using
        (Complexity.computableInPolyTime_levinStage computableInPolyTime_verifier).comp hpair)
    · refine ⟨hp φ, fun hs => ?_⟩
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hs
      exact ⟨assignment φ w, verifier_of_levinStage_eq_some hw⟩
  · intro hSAT
    obtain ⟨g, ⟨t, s, ht, -, k, State, hfin, tm, htm⟩, hg⟩ := exists_search hSAT
    obtain ⟨c, e, hle⟩ := polynomiallyBounded_iff_le.mp ht
    obtain ⟨i₀, hi₀⟩ := exists_index_levinStage_isSome (enc := encCNF) (V := verifier) tm
    refine ⟨Polynomial.C (i₀ + 1) + Polynomial.C c * (Polynomial.X + 1) ^ e, fun φ hφ => ?_⟩
    have hrun := (htm φ).runFrom_of_le le_rfl
    refine hi₀ φ (t (encCNF φ).length) _ hrun.1 (hrun.2.symm ▸ (hg φ).mpr hφ) ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
      Polynomial.eval_X, Polynomial.eval_one]
    have ht' := hle (encCNF φ).length
    omega

/-- **Native universal search machine for `SAT`** (after [Levin][Levin1973] and
[Goldreich, Theorem 2.33][Goldreich2008]; primary PDF locators not verified; polynomial
universal-simulation overhead as documented in the module header).

There exists **one fixed** finite-state binary `MultiTapeTM` `tm` (independent of `P = NP` and of
any assumed `SAT` algorithm) and a universal exponent `D` such that:
1. **Soundness:** every output `w` it halts with on `encCNF φ` satisfies `SAT.verifier (φ, w)`.
2. **Exact halting domain:** `tm` halts on `encCNF φ` iff `φ ∈ SAT` (in particular, it diverges on
   every unsatisfiable formula).
3. **Polynomial optimality:** for every finite-state binary `MultiTapeTM` `M`, there is a constant
   `C_M` (depending only on `M`) such that whenever `M` finds a `SAT.verifier`-accepted assignment
   for `φ` within `T` steps, `tm` finds one within time and space `C_M * (T + |encCNF φ| + 1) ^ D`.
4. **Polynomial time on satisfiable formulas iff `P = NP`:** `tm` halts within polynomially many
   steps on all satisfiable formulas if and only if `P = NP` for every encoding. -/
theorem exists_native_levinSearch :
    ∃ (k : ℕ) (State : Type) (_ : Finite State) (tm : MultiTapeTM k Bool State) (D : ℕ),
      (∀ φ w, tm.Computes (encCNF φ) w → verifier (φ, w) = true) ∧
      (∀ φ, tm.Halts (encCNF φ) ↔ φ ∈ SAT) ∧
      (∀ {k' : ℕ} {State' : Type} [Finite State'] (M : MultiTapeTM k' Bool State'),
        ∃ C_M : ℕ, ∀ (φ : CNF ℕ) (T : ℕ),
          (M.runFrom (M.initCfg (encCNF φ)) T).Halted →
          verifier (φ, (M.runFrom (M.initCfg (encCNF φ)) T).output) = true →
          ∃ w, verifier (φ, w) = true ∧
            tm.ComputesInTimeAndSpace (encCNF φ) w
              (C_M * (T + (encCNF φ).length + 1) ^ D)
              (C_M * (T + (encCNF φ).length + 1) ^ D)) ∧
      ((∃ t : ℕ → ℕ, PolynomiallyBounded t ∧
          ∀ φ ∈ SAT, (tm.runFrom (tm.initCfg (encCNF φ)) (t (encCNF φ).length)).Halted) ↔
        ∀ {β : Type} (e : β ↪ List Bool), P e = NP e) := by
  obtain ⟨k, State, hfin, tm, _, D, hsound, hhalts, _, hopt⟩ :=
    Complexity.exists_native_levinSearch computableInPolyTime_verifier
  have hhalts_sat : ∀ φ, tm.Halts (encCNF φ) ↔ φ ∈ SAT := fun φ =>
    (hhalts φ).trans exists_verifier_iff_mem
  refine ⟨k, State, hfin, tm, D, hsound, hhalts_sat, hopt, ?_⟩
  rw [← SAT_mem_P_iff]
  constructor
  · rintro ⟨t, ht, hbound⟩
    obtain ⟨c, e, hle⟩ := polynomiallyBounded_iff_le.mp ht
    have := Fintype.ofFinite State
    let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
    let d_tm : Desc := desc eS eBit tm
    let p : Polynomial ℕ := Polynomial.C c * (Polynomial.X + 1) ^ e
    let dec : CNF ℕ → Bool := fun φ => (runWord d_tm (encCNF φ) (p.eval (encCNF φ).length)).isSome
    have hdec_poly : ComputableInPolyTime dec encCNF encBool := by
      have hp_poly : ComputableInPolyTime (fun φ : CNF ℕ => p.eval (encCNF φ).length)
          encCNF encUnary :=
        (unary_eval p).comp (encoding_length encCNF)
      exact optionIsSome (computableInPolyTime_runWord (const d_tm) (encoding_comp id') hp_poly)
    refine mem_P.mpr ⟨dec, hdec_poly, fun φ => ?_⟩
    have hp_ge : t (encCNF φ).length ≤ p.eval (encCNF φ).length := by
      simpa [p] using hle (encCNF φ).length
    constructor
    · intro hφ
      simp [dec, d_tm, runWord_desc_of_halted eS tm (hbound φ hφ) hp_ge]
    · intro htrue
      obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp htrue
      rw [runWord_desc] at hw
      split_ifs at hw with hh
      exact (hhalts_sat φ).mp ⟨_, hh⟩
  · intro hSAT
    obtain ⟨g, ⟨t, s, ht, -, k', State', hfin', M, hM⟩, hg⟩ := exists_search hSAT
    obtain ⟨C_M, hoptM⟩ := hopt M
    refine ⟨fun n => C_M * (t n + n + 1) ^ D, by fun_prop, fun φ hφ => ?_⟩
    have hrunM := (hM φ).runFrom_of_le le_rfl
    obtain ⟨w, -, hrun⟩ := hoptM φ (t (encCNF φ).length) hrunM.1 (hrunM.2.symm ▸ (hg φ).mpr hφ)
    exact (hrun.runFrom_of_le le_rfl).1

end SAT

end Cslib.Complexity
