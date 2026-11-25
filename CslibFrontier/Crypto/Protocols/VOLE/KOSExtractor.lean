/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.HashFamily
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs
import CslibFrontier.Probability.HashFamily.Collisions
import CslibFrontier.Probability.PMF.Event
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.List.Nodup
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Tactic.Module

/-!
# KOS consistency affine extractor and exact binomial loss

Section 10.6 of the FAEST v3.0 specification ([BaumEtAl2026FAEST], Lemma 10.26 and Corollary 10.27,
pp. 97–99) analyzes the `VOLEHash` consistency check through an explicit affine-line extractor
`E_{KOS,S}(H, ũ, ṽ)` over a finite collection `S` of candidate `(Δ, q)` openings:

* Given a linear hash evaluation `h : V →ₗ[F] W` and hashed target line `target = (ũ, ṽ)`, the
  extractor filters the accepted openings `S_{h, ũ, ṽ} = {(Δ, q) ∈ S | h q = Δ • ũ + ṽ}`:
  * zero accepted openings: returns `⟨0, 0⟩`;
  * one accepted challenge (every accepted opening shares `Δ₀`): returns the constant line
    `⟨0, q₀⟩`;
  * at least two accepted openings with distinct challenges `Δ₁ ≠ Δ₀`: interpolates the unique
    affine line `u = (Δ₁ - Δ₀)⁻¹ • (q₁ - q₀)`, `v = q₀ - Δ₀ • u`.
* If `S` is a response graph (`IsResponseGraph`, i.e., equal challenges in `S` carry equal
  responses, as in Corollary 10.27's `S_t = {(Δ, Resp_t(Δ)) | Resp_t(Δ) ≠ ⊥}`), any accepted
  opening `(Δ₂, q₂) ∈ S` missed by the extracted line yields an explicit failure witness
  (`KOSFailureWitness` / `kosFailureWitness`): three openings `(Δ₀, q₀), (Δ₁, q₁), (Δ₂, q₂) ∈ S`
  with pairwise distinct challenges (`HasKOSBadTriple`, matching Bad event 2 on p. 98) whose
  nonzero affine collinearity defect
  `kosAffineDefect p₀ p₁ p₂ = (Δ₁ - Δ₀) • (q₂ - q₀) - (Δ₂ - Δ₀) • (q₁ - q₀) ≠ 0` is mapped to `0`
  by `h`.
* Because `kosAffineDefect` only changes sign under permutations of its three inputs, unordered
  3-element index subsets of `responses` canonically cover all bad triples. For any `ε`-universal
  linear hash family (`Cslib.Probability.IsUniversalHash`), the union bound over
  `powersetCard 3` gives the abstract response-graph step `ε * (responses.length.choose 3)`
  (`toOuterMeasure_kosExtract_graph_failure_le`), and combining with
  `IsUniversalHash.toOuterMeasure_not_injOn_le` gives the abstract general-list step
  `ε * (responses.length.choose 2 + responses.length.choose 3)`
  (`toOuterMeasure_kosExtract_failure_le`).

## Source correspondence and scope

These theorems formalize the abstract `IsUniversalHash` steps of Lemma 10.26 and Corollary 10.27,
not FAEST's concrete `VOLEHash` endpoints:

* Lemma 10.26's statement (p. 97) writes the relaxed cubic bound `(|S|³ / 6 + |S|² / 2) ε` over a
  finite set `S`, whereas its proof (p. 98) derives the sharper binomial sum
  `(choose |S| 2 + choose |S| 3) ε` before relaxing; similarly Corollary 10.27's statement writes
  `|S_t|³ / 6 · ε_v` after eliminating Bad event 1. The theorems here retain the exact binomial
  coefficients.
* `responses : List (F × V)` counts list positions (`responses.length`), matching the source's set
  cardinality `|S|` on any duplicate-free enumeration (`responses.Nodup`) while remaining valid as
  an upper bound when duplicates are present.
* Following Lemma 10.26 (p. 97), the attacker and extractor may be computationally unbounded and
  `responses` may have exponential length (up to `2^{λ - w_grind}` in FAEST), so `kosExtract` is
  not claimed to run in polynomial time in a security parameter. Concrete `VOLEHash` universality,
  BAVC selective-opening reconstruction (#5302), Lemma 10.19's response graph, QuickSilver v3, and
  ROM/QROM signature reductions remain open under #4987.

## Main definitions

* `Cslib.Crypto.Protocols.VOLE.KOSLine` and `KOSLine.eval`: affine line `Δ ↦ Δ • slope + intercept`.
* `Cslib.Crypto.Protocols.VOLE.IsResponseGraph`: partial-function graph invariant on
  `List (F × V)`.
* `Cslib.Crypto.Protocols.VOLE.kosAffineDefect`: affine collinearity defect
  `(Δ₁ - Δ₀) • (q₂ - q₀) - (Δ₂ - Δ₀) • (q₁ - q₀)`.
* `Cslib.Crypto.Protocols.VOLE.kosExtract`: total executable affine-line extractor handling `0`,
  `1`, and `≥ 2` accepted challenges.
* `Cslib.Crypto.Protocols.VOLE.KOSFailureWitness` and `kosFailureWitness`: explicit computable
  non-collinear triple witness from any failed graph extraction.
* `Cslib.Crypto.Protocols.VOLE.HasKOSBadPair`,
  `Cslib.Crypto.Protocols.VOLE.HasKOSBadTriple`: bad-pair (Bad event 1) and distinct-challenge
  bad-triple (Bad event 2) predicates on `h` and `responses`.

## Main results

* `Cslib.Crypto.Protocols.VOLE.KOSLine.eq_of_eval_eq`: two `KOSLine`s agreeing at two distinct
  field elements are equal.
* `Cslib.Crypto.Protocols.VOLE.kosExtract_eval_eq_of_not_hasKOSBadTriple`: outside
  `HasKOSBadTriple h responses`, every accepted opening of a response graph lies on the extracted
  affine line.
* `Cslib.Crypto.Protocols.VOLE.not_hasKOSBadTriple_of_length_le_two`: lists of at most two openings
  have no bad triples.
* `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_hasKOSBadTriple_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_kosExtract_graph_failure_le`: abstract response-graph
  `ε * (responses.length.choose 3)` step toward Corollary 10.27.
* `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_hasKOSBadPair_le`,
  `Cslib.Crypto.Protocols.VOLE.toOuterMeasure_kosExtract_failure_le`: abstract
  `ε * ((responses.length.choose 2) + (responses.length.choose 3))` step of Lemma 10.26.

## References

* [C. Baum et al., *FAEST v3: Algorithm Specifications*, version 3.0, §10.6, Lemma 10.26 and
  Corollary 10.27, pp. 97–99][BaumEtAl2026FAEST]
-/

public section

namespace Cslib.Crypto.Protocols.VOLE

open Cslib.Probability
open scoped BigOperators ENNReal

/-- An affine line `Δ ↦ Δ • slope + intercept` over a module `V`
([BaumEtAl2026FAEST], §10.6, pp. 97–99, representing `(u, v)` with evaluation `u · Δ + v`). -/
@[ext]
structure KOSLine (V : Type*) where
  /-- Linear coefficient `u` (`slope`). -/
  slope : V
  /-- Constant coefficient `v` (`intercept`). -/
  intercept : V
  deriving Repr

instance {V : Type*} [DecidableEq V] : DecidableEq (KOSLine V) := fun a b =>
  decidable_of_iff (a.slope = b.slope ∧ a.intercept = b.intercept) (by cases a; cases b; simp)

namespace KOSLine

/-- Evaluate the affine line `Δ ↦ Δ • line.slope + line.intercept`. -/
@[expose] def eval {F V : Type*} [SMul F V] [Add V] (line : KOSLine V) (delta : F) : V :=
  delta • line.slope + line.intercept

/-- Two affine lines over a vector space that agree at two distinct points `Δ₀ ≠ Δ₁` are equal. -/
theorem eq_of_eval_eq {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
    {line₁ line₂ : KOSLine V} {Δ₀ Δ₁ : F} (hne : Δ₀ ≠ Δ₁)
    (h₀ : line₁.eval Δ₀ = line₂.eval Δ₀) (h₁ : line₁.eval Δ₁ = line₂.eval Δ₁) :
    line₁ = line₂ := by
  have hd : Δ₀ - Δ₁ ≠ 0 := sub_ne_zero.mpr hne
  have hsub : (Δ₀ - Δ₁) • (line₁.slope - line₂.slope) = 0 := by
    calc
      (Δ₀ - Δ₁) • (line₁.slope - line₂.slope)
          = (line₁.eval Δ₀ - line₁.eval Δ₁) - (line₂.eval Δ₀ - line₂.eval Δ₁) := by
            simp only [KOSLine.eval]
            module
      _ = 0 := by rw [h₀, h₁, sub_self]
  have hslope : line₁.slope = line₂.slope :=
    sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_left hd)
  have hinter : line₁.intercept = line₂.intercept := by
    simpa [KOSLine.eval, hslope] using h₀
  ext <;> assumption

end KOSLine

/-- `responses` is the graph of a partial response function (`S_t` in [BaumEtAl2026FAEST],
Corollary 10.27, p. 98) when equal challenges carry equal responses. -/
def IsResponseGraph {F V : Type*} (responses : List (F × V)) : Prop :=
  ∀ ⦃p₁⦄, p₁ ∈ responses → ∀ ⦃p₂⦄, p₂ ∈ responses → p₁.1 = p₂.1 → p₁.2 = p₂.2

/-- Any opening list with pairwise distinct challenges satisfies `IsResponseGraph`. -/
theorem IsResponseGraph.of_nodup_fst {F V : Type*} {responses : List (F × V)}
    (h : (responses.map Prod.fst).Nodup) : IsResponseGraph responses :=
  fun _ hp₁ _ hp₂ heq => congrArg Prod.snd (List.inj_on_of_nodup_map h hp₁ hp₂ heq)

section Algebraic

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- Affine collinearity defect of three openings `p₀, p₁, p₂ : F × V`
([BaumEtAl2026FAEST], Lemma 10.26 proof, p. 98):
`(p₁.1 - p₀.1) • (p₂.2 - p₀.2) - (p₂.1 - p₀.1) • (p₁.2 - p₀.2)`. -/
@[expose] def kosAffineDefect (p₀ p₁ p₂ : F × V) : V :=
  (p₁.1 - p₀.1) • (p₂.2 - p₀.2) - (p₂.1 - p₀.1) • (p₁.2 - p₀.2)

private def interpolateKOSLine (p₀ p₁ : F × V) : KOSLine V :=
  let slope := (p₁.1 - p₀.1)⁻¹ • (p₁.2 - p₀.2)
  ⟨slope, p₀.2 - p₀.1 • slope⟩

private theorem interpolateKOSLine_eval_left (p₀ p₁ : F × V) :
    (interpolateKOSLine p₀ p₁).eval p₀.1 = p₀.2 := by
  simp [interpolateKOSLine, KOSLine.eval]

private theorem interpolateKOSLine_eval_right {p₀ p₁ : F × V} (hne : p₁.1 ≠ p₀.1) :
    (interpolateKOSLine p₀ p₁).eval p₁.1 = p₁.2 := by
  have hd : p₁.1 - p₀.1 ≠ 0 := sub_ne_zero.mpr hne
  calc
    (interpolateKOSLine p₀ p₁).eval p₁.1
        = p₀.2 + ((p₁.1 - p₀.1) * (p₁.1 - p₀.1)⁻¹) • (p₁.2 - p₀.2) := by
          simp only [interpolateKOSLine, KOSLine.eval, smul_smul]
          module
    _ = p₁.2 := by
          rw [mul_inv_cancel₀ hd, one_smul, add_sub_cancel]

private theorem interpolateKOSLine_eval_eq_iff {p₀ p₁ : F × V} (hne : p₁.1 ≠ p₀.1) (p₂ : F × V) :
    (interpolateKOSLine p₀ p₁).eval p₂.1 = p₂.2 ↔ kosAffineDefect p₀ p₁ p₂ = 0 := by
  have hd : p₁.1 - p₀.1 ≠ 0 := sub_ne_zero.mpr hne
  have hdiff : (interpolateKOSLine p₀ p₁).eval p₂.1 - p₂.2 =
      -(p₁.1 - p₀.1)⁻¹ • kosAffineDefect p₀ p₁ p₂ := by
    calc
      (interpolateKOSLine p₀ p₁).eval p₂.1 - p₂.2
          = (p₂.1 - p₀.1) • ((p₁.1 - p₀.1)⁻¹ • (p₁.2 - p₀.2)) - (p₂.2 - p₀.2) := by
            simp only [interpolateKOSLine, KOSLine.eval]
            module
      _ = (p₂.1 - p₀.1) • ((p₁.1 - p₀.1)⁻¹ • (p₁.2 - p₀.2)) -
            ((p₁.1 - p₀.1)⁻¹ * (p₁.1 - p₀.1)) • (p₂.2 - p₀.2) := by
            rw [inv_mul_cancel₀ hd, one_smul]
      _ = -(p₁.1 - p₀.1)⁻¹ • kosAffineDefect p₀ p₁ p₂ := by
            simp only [kosAffineDefect, smul_smul]
            module
  rw [← sub_eq_zero, hdiff, neg_smul, neg_eq_zero, smul_eq_zero]
  simp [inv_ne_zero hd]

private theorem map_kosAffineDefect_eq_zero_of_collinear (h : V →ₗ[F] W) {target : KOSLine W}
    {p₀ p₁ p₂ : F × V} (h₀ : h p₀.2 = target.eval p₀.1) (h₁ : h p₁.2 = target.eval p₁.1)
    (h₂ : h p₂.2 = target.eval p₂.1) :
    h (kosAffineDefect p₀ p₁ p₂) = 0 := by
  simp only [kosAffineDefect, map_sub, map_smul, h₀, h₁, h₂, KOSLine.eval]
  module

/-- Three openings lying on a single `KOSLine` have zero `kosAffineDefect`. -/
theorem kosAffineDefect_eq_zero_of_eval_eq {line : KOSLine V} {p₀ p₁ p₂ : F × V}
    (h₀ : line.eval p₀.1 = p₀.2) (h₁ : line.eval p₁.1 = p₁.2) (h₂ : line.eval p₂.1 = p₂.2) :
    kosAffineDefect p₀ p₁ p₂ = 0 :=
  map_kosAffineDefect_eq_zero_of_collinear LinearMap.id h₀.symm h₁.symm h₂.symm

private theorem kosAffineDefect_swap₁₂ (p₀ p₁ p₂ : F × V) :
    kosAffineDefect p₀ p₂ p₁ = -kosAffineDefect p₀ p₁ p₂ := by
  simp only [kosAffineDefect]
  module

private theorem kosAffineDefect_swap₀₁ (p₀ p₁ p₂ : F × V) :
    kosAffineDefect p₁ p₀ p₂ = -kosAffineDefect p₀ p₁ p₂ := by
  simp only [kosAffineDefect]
  module

/-- Bad-triple predicate (step corresponding to Bad event 2 in [BaumEtAl2026FAEST], Lemma 10.26,
p. 98): three openings in `responses` at pairwise distinct challenges have a nonzero
`kosAffineDefect` mapped to `0` by `h`. -/
@[expose] def HasKOSBadTriple (h : V →ₗ[F] W) (responses : List (F × V)) : Prop :=
  ∃ p₀ ∈ responses, ∃ p₁ ∈ responses, ∃ p₂ ∈ responses,
    p₀.1 ≠ p₁.1 ∧ p₀.1 ≠ p₂.1 ∧ p₁.1 ≠ p₂.1 ∧
    kosAffineDefect p₀ p₁ p₂ ≠ 0 ∧ h (kosAffineDefect p₀ p₁ p₂) = 0

/-- Lists of at most two openings cannot contain three pairwise distinct challenges and therefore
never satisfy `HasKOSBadTriple`. -/
theorem not_hasKOSBadTriple_of_length_le_two (h : V →ₗ[F] W) {responses : List (F × V)}
    (hlen : responses.length ≤ 2) : ¬ HasKOSBadTriple h responses := by
  rintro ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, hne₀₁, hne₀₂, hne₁₂, _, _⟩
  obtain ⟨i₀, rfl⟩ := List.mem_iff_get.mp hp₀
  obtain ⟨i₁, rfl⟩ := List.mem_iff_get.mp hp₁
  obtain ⟨i₂, rfl⟩ := List.mem_iff_get.mp hp₂
  have hi₀₁ : i₀.val ≠ i₁.val := fun heq => hne₀₁ (by rw [Fin.ext heq])
  have hi₀₂ : i₀.val ≠ i₂.val := fun heq => hne₀₂ (by rw [Fin.ext heq])
  have hi₁₂ : i₁.val ≠ i₂.val := fun heq => hne₁₂ (by rw [Fin.ext heq])
  have := i₀.isLt
  have := i₁.isLt
  have := i₂.isLt
  omega

/-- Shared accepted-opening selector for `kosExtract` and `kosFailureWitness`: filters `responses`
to openings satisfying `h p.2 = target.eval p.1` and searches the tail for a second distinct
challenge. -/
private def selectAccepted [DecidableEq F] [DecidableEq W]
    (h : V → W) (responses : List (F × V)) (target : KOSLine W) :
    Option ((F × V) × Option (F × V)) :=
  match responses.filter (fun p => decide (h p.2 = target.eval p.1)) with
  | [] => none
  | p₀ :: rest => some (p₀, rest.find? (fun p => p.1 ≠ p₀.1))

omit [AddCommGroup V] [Module F V] in
private theorem selectAccepted_eq_none [DecidableEq F] [DecidableEq W]
    {h : V → W} {responses : List (F × V)} {target : KOSLine W}
    (hsel : selectAccepted h responses target = none) :
    ∀ p ∈ responses, h p.2 ≠ target.eval p.1 := by
  intro p hp heq
  have hmem : p ∈ responses.filter (fun q => decide (h q.2 = target.eval q.1)) :=
    List.mem_filter.mpr ⟨hp, decide_eq_true heq⟩
  unfold selectAccepted at hsel
  split at hsel
  · rename_i hfilt
    rw [hfilt] at hmem
    cases hmem
  · cases hsel

omit [AddCommGroup V] [Module F V] in
private theorem selectAccepted_eq_some_none [DecidableEq F] [DecidableEq W]
    {h : V → W} {responses : List (F × V)} {target : KOSLine W} {p₀ : F × V}
    (hsel : selectAccepted h responses target = some (p₀, none)) :
    p₀ ∈ responses ∧ h p₀.2 = target.eval p₀.1 ∧
      ∀ p ∈ responses, h p.2 = target.eval p.1 → p.1 = p₀.1 := by
  unfold selectAccepted at hsel
  split at hsel
  · cases hsel
  · rename_i q₀ rest hfilt
    obtain ⟨rfl, hfind⟩ := Prod.mk.inj (Option.some.inj hsel)
    have hp₀_acc : q₀ ∈ responses.filter (fun q => decide (h q.2 = target.eval q.1)) := by
      rw [hfilt]
      exact List.mem_cons_self
    obtain ⟨hp₀_mem, hp₀_dec⟩ := List.mem_filter.mp hp₀_acc
    refine ⟨hp₀_mem, of_decide_eq_true hp₀_dec, fun p hp hhash => ?_⟩
    have hp_acc : p ∈ q₀ :: rest := by
      rw [← hfilt]
      exact List.mem_filter.mpr ⟨hp, decide_eq_true hhash⟩
    rcases List.mem_cons.mp hp_acc with rfl | hrest
    · rfl
    · simpa using List.find?_eq_none.mp hfind p hrest

omit [AddCommGroup V] [Module F V] in
private theorem selectAccepted_eq_some_some [DecidableEq F] [DecidableEq W]
    {h : V → W} {responses : List (F × V)} {target : KOSLine W} {p₀ p₁ : F × V}
    (hsel : selectAccepted h responses target = some (p₀, some p₁)) :
    p₀ ∈ responses ∧ h p₀.2 = target.eval p₀.1 ∧
      p₁ ∈ responses ∧ h p₁.2 = target.eval p₁.1 ∧ p₁.1 ≠ p₀.1 := by
  unfold selectAccepted at hsel
  split at hsel
  · cases hsel
  · rename_i q₀ rest hfilt
    obtain ⟨rfl, hfind⟩ := Prod.mk.inj (Option.some.inj hsel)
    have hp₀_acc : q₀ ∈ responses.filter (fun q => decide (h q.2 = target.eval q.1)) := by
      rw [hfilt]
      exact List.mem_cons_self
    have hp₁_acc : p₁ ∈ responses.filter (fun q => decide (h q.2 = target.eval q.1)) := by
      rw [hfilt]
      exact List.mem_cons_of_mem q₀ (List.mem_of_find?_eq_some hfind)
    obtain ⟨hp₀_mem, hp₀_dec⟩ := List.mem_filter.mp hp₀_acc
    obtain ⟨hp₁_mem, hp₁_dec⟩ := List.mem_filter.mp hp₁_acc
    exact ⟨hp₀_mem, of_decide_eq_true hp₀_dec, hp₁_mem, of_decide_eq_true hp₁_dec,
      by simpa using List.find?_some hfind⟩

/-- Executable, total KOS affine-line extractor ([BaumEtAl2026FAEST], §10.6, Lemma 10.26 and
Corollary 10.27, pp. 97–99). Selects accepted openings via `selectAccepted` and handles `0`, `1`,
and `≥ 2` distinct accepted challenges via `interpolateKOSLine`. -/
def kosExtract [DecidableEq F] [DecidableEq W]
    (h : V → W) (responses : List (F × V)) (target : KOSLine W) : KOSLine V :=
  match selectAccepted h responses target with
  | none => ⟨0, 0⟩
  | some (p₀, none) => ⟨0, p₀.2⟩
  | some (p₀, some p₁) => interpolateKOSLine p₀ p₁

/-- `kosExtract` reads `h` only at the response vectors `p.2` for `p ∈ responses`. -/
theorem kosExtract_eq_of_eqOn_snd [DecidableEq F] [DecidableEq W]
    {h₁ h₂ : V → W} {responses : List (F × V)} (target : KOSLine W)
    (heq : ∀ p ∈ responses, h₁ p.2 = h₂ p.2) :
    kosExtract h₁ responses target = kosExtract h₂ responses target := by
  have hfilt : responses.filter (fun p => decide (h₁ p.2 = target.eval p.1)) =
      responses.filter (fun p => decide (h₂ p.2 = target.eval p.1)) :=
    List.filter_congr fun p hp => by simp [heq p hp]
  simp only [kosExtract, selectAccepted, hfilt]

@[simp]
theorem kosExtract_nil [DecidableEq F] [DecidableEq W]
    (h : V → W) (target : KOSLine W) :
    kosExtract h ([] : List (F × V)) target = ⟨0, 0⟩ := by
  rfl

/-- On a single accepted opening `p₀`, `kosExtract` returns the constant line `⟨0, p₀.2⟩`. -/
theorem kosExtract_singleton_of_eq [DecidableEq F] [DecidableEq W]
    {h : V → W} {p₀ : F × V} {target : KOSLine W} (h₀ : h p₀.2 = target.eval p₀.1) :
    kosExtract h [p₀] target = ⟨0, p₀.2⟩ := by
  simp [kosExtract, selectAccepted, h₀]

/-- Explicit computable failure witness from any failed extraction on a response graph
([BaumEtAl2026FAEST], Lemma 10.26 proof, p. 98). -/
structure KOSFailureWitness (h : V →ₗ[F] W) (responses : List (F × V)) (target : KOSLine W) where
  /-- First accepted opening `(Δ₀, q₀)` used for interpolation. -/
  p₀ : F × V
  /-- Second accepted opening `(Δ₁, q₁)` used for interpolation. -/
  p₁ : F × V
  /-- Accepted opening `(Δ₂, q₂)` missed by the interpolated line. -/
  p₂ : F × V
  p₀_mem : p₀ ∈ responses
  p₁_mem : p₁ ∈ responses
  p₂_mem : p₂ ∈ responses
  challenge_ne₀₁ : p₀.1 ≠ p₁.1
  challenge_ne₀₂ : p₀.1 ≠ p₂.1
  challenge_ne₁₂ : p₁.1 ≠ p₂.1
  hash_p₀ : h p₀.2 = target.eval p₀.1
  hash_p₁ : h p₁.2 = target.eval p₁.1
  hash_p₂ : h p₂.2 = target.eval p₂.1
  defect_ne_zero : kosAffineDefect p₀ p₁ p₂ ≠ 0
  map_defect_eq_zero : h (kosAffineDefect p₀ p₁ p₂) = 0

/-- Construct an explicit `KOSFailureWitness` whenever `kosExtract` misses an accepted opening `p`
of a response graph `responses`. -/
def kosFailureWitness [DecidableEq F] [DecidableEq W]
    (h : V →ₗ[F] W) {responses : List (F × V)} (hgraph : IsResponseGraph responses)
    {target : KOSLine W} {p : F × V} (hp : p ∈ responses) (hhash : h p.2 = target.eval p.1)
    (hfail : (kosExtract h responses target).eval p.1 ≠ p.2) :
    KOSFailureWitness h responses target :=
  match hsel : selectAccepted h responses target with
  | none => False.elim (selectAccepted_eq_none hsel p hp hhash)
  | some (p₀, none) =>
    False.elim <| by
      obtain ⟨hp₀_mem, _, hall⟩ := selectAccepted_eq_some_none hsel
      have hp_eq_fst : p.1 = p₀.1 := hall p hp hhash
      have hp_eq_snd : p.2 = p₀.2 := hgraph hp hp₀_mem hp_eq_fst
      have heval : (kosExtract h responses target).eval p.1 = p₀.2 := by
        simp [kosExtract, hsel, KOSLine.eval]
      exact hfail (heval.trans hp_eq_snd.symm)
  | some (p₀, some p₁) =>
    let ⟨hp₀_mem, h₀, hp₁_mem, h₁, hne₁₀⟩ := selectAccepted_eq_some_some hsel
    have hext_eq : kosExtract h responses target = interpolateKOSLine p₀ p₁ := by
      simp [kosExtract, hsel]
    have hfail' : (interpolateKOSLine p₀ p₁).eval p.1 ≠ p.2 := by
      rwa [← hext_eq]
    have hne₀₂ : p₀.1 ≠ p.1 := by
      intro heq
      apply hfail'
      rw [← heq, interpolateKOSLine_eval_left]
      exact hgraph hp₀_mem hp heq
    have hne₁₂ : p₁.1 ≠ p.1 := by
      intro heq
      apply hfail'
      rw [← heq, interpolateKOSLine_eval_right hne₁₀]
      exact hgraph hp₁_mem hp heq
    have hdef : kosAffineDefect p₀ p₁ p ≠ 0 :=
      mt (interpolateKOSLine_eval_eq_iff hne₁₀ p).mpr hfail'
    { p₀ := p₀
      p₁ := p₁
      p₂ := p
      p₀_mem := hp₀_mem
      p₁_mem := hp₁_mem
      p₂_mem := hp
      challenge_ne₀₁ := hne₁₀.symm
      challenge_ne₀₂ := hne₀₂
      challenge_ne₁₂ := hne₁₂
      hash_p₀ := h₀
      hash_p₁ := h₁
      hash_p₂ := hhash
      defect_ne_zero := hdef
      map_defect_eq_zero := map_kosAffineDefect_eq_zero_of_collinear h h₀ h₁ hhash }

/-- Deterministic extraction step of [BaumEtAl2026FAEST], §10.6, Lemma 10.26 and Corollary 10.27
(pp. 97–99): on a response graph `responses`, if `HasKOSBadTriple h responses` does not hold, then
every opening `p ∈ responses` accepted by `target` lies on `kosExtract h responses target`. -/
theorem kosExtract_eval_eq_of_not_hasKOSBadTriple [DecidableEq F] [DecidableEq W]
    (h : V →ₗ[F] W) {responses : List (F × V)} (hgraph : IsResponseGraph responses)
    (hnobad : ¬ HasKOSBadTriple h responses) (target : KOSLine W) {p : F × V}
    (hp : p ∈ responses) (hhash : h p.2 = target.eval p.1) :
    (kosExtract h responses target).eval p.1 = p.2 := by
  by_contra hfail
  let w := kosFailureWitness h hgraph hp hhash hfail
  exact hnobad ⟨w.p₀, w.p₀_mem, w.p₁, w.p₁_mem, w.p₂, w.p₂_mem,
    w.challenge_ne₀₁, w.challenge_ne₀₂, w.challenge_ne₁₂,
    w.defect_ne_zero, w.map_defect_eq_zero⟩

end Algebraic

section ProbabilityBounds

variable {Seed F V W : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

omit [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] in
/-- Bad-pair predicate (step corresponding to Bad event 1 in [BaumEtAl2026FAEST], Lemma 10.26,
p. 98): two openings in `responses` share the same challenge `Δ` with distinct response vectors
`q₀ ≠ q₁` whose hashes collide. Impossible when `IsResponseGraph responses` holds. -/
@[expose] def HasKOSBadPair (h : V → W) (responses : List (F × V)) : Prop :=
  ∃ p₀ ∈ responses, ∃ p₁ ∈ responses, p₀.1 = p₁.1 ∧ p₀.2 ≠ p₁.2 ∧ h p₀.2 = h p₁.2

private theorem kosAffineDefect_index_perm_eq_or_neg (responses : List (F × V))
    {i₀ i₁ i₂ j₀ j₁ j₂ : Fin responses.length}
    (hset : ({i₀, i₁, i₂} : Finset (Fin responses.length)) = {j₀, j₁, j₂})
    (hi₀₁ : i₀ ≠ i₁) (hi₀₂ : i₀ ≠ i₂) (hi₁₂ : i₁ ≠ i₂) :
    kosAffineDefect (responses.get i₀) (responses.get i₁) (responses.get i₂) =
        kosAffineDefect (responses.get j₀) (responses.get j₁) (responses.get j₂) ∨
      kosAffineDefect (responses.get i₀) (responses.get i₁) (responses.get i₂) =
        -kosAffineDefect (responses.get j₀) (responses.get j₁) (responses.get j₂) := by
  have hm₀ : i₀ ∈ ({j₀, j₁, j₂} : Finset (Fin responses.length)) := hset ▸ by simp
  have hm₁ : i₁ ∈ ({j₀, j₁, j₂} : Finset (Fin responses.length)) := hset ▸ by simp
  have hm₂ : i₂ ∈ ({j₀, j₁, j₂} : Finset (Fin responses.length)) := hset ▸ by simp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm₀ hm₁ hm₂
  rcases hm₀ with rfl | rfl | rfl <;>
    rcases hm₁ with rfl | rfl | rfl <;>
    rcases hm₂ with rfl | rfl | rfl
  all_goals try exact False.elim (hi₀₁ rfl)
  all_goals try exact False.elim (hi₀₂ rfl)
  all_goals try exact False.elim (hi₁₂ rfl)
  · exact Or.inl rfl
  · exact Or.inr (kosAffineDefect_swap₁₂ _ _ _)
  · exact Or.inr (kosAffineDefect_swap₀₁ _ _ _)
  all_goals simp only [kosAffineDefect]
  exacts [Or.inl (by module), Or.inl (by module), Or.inr (by module)]

private noncomputable def chooseTriple {α : Type*} [DecidableEq α] {T : Finset α}
    (hcard : T.card = 3) : α × α × α :=
  let j₀ := Classical.choose (Finset.card_eq_three.mp hcard)
  let h₁ := Classical.choose_spec (Finset.card_eq_three.mp hcard)
  let j₁ := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let j₂ := Classical.choose h₂
  (j₀, j₁, j₂)

private theorem chooseTriple_spec {α : Type*} [DecidableEq α] {T : Finset α} (hcard : T.card = 3) :
    T = {(chooseTriple hcard).1, (chooseTriple hcard).2.1, (chooseTriple hcard).2.2} :=
  (Classical.choose_spec
    (Classical.choose_spec (Classical.choose_spec (Finset.card_eq_three.mp hcard)))).2.2.2

omit [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W] in
/-- Bad-pair union-bound step of [BaumEtAl2026FAEST], §10.6, Lemma 10.26 (Bad event 1, p. 98),
derived from `IsUniversalHash.toOuterMeasure_not_injOn_le`: for any `ε`-universal hash family `h`,
`HasKOSBadPair (h s) responses` holds with seed probability at most
`ε * (responses.length.choose 2)`. -/
theorem toOuterMeasure_hasKOSBadPair_le
    {seed : PMF Seed} {h : Seed → V → W} {ε : ℝ≥0∞}
    (hh : IsUniversalHash seed h ε) (responses : List (F × V)) :
    seed.toOuterMeasure {s | HasKOSBadPair (h s) responses} ≤
      ε * (responses.length.choose 2 : ℝ≥0∞) := by
  classical
  let S : Finset V := (responses.map Prod.snd).toFinset
  have hsub : {s | HasKOSBadPair (h s) responses} ⊆ {s | ¬ Set.InjOn (h s) S} := by
    rintro s ⟨p₀, hp₀, p₁, hp₁, _, hqne, hcoll⟩ hinj
    exact hqne (hinj (List.mem_toFinset.mpr (List.mem_map_of_mem hp₀))
      (List.mem_toFinset.mpr (List.mem_map_of_mem hp₁)) hcoll)
  have hcard : S.card ≤ responses.length := by
    simpa [S] using List.toFinset_card_le (responses.map Prod.snd)
  have hchoose : (S.card.choose 2 : ℝ≥0∞) ≤ (responses.length.choose 2 : ℝ≥0∞) := by
    exact_mod_cast Nat.choose_le_choose 2 hcard
  calc
    seed.toOuterMeasure {s | HasKOSBadPair (h s) responses}
        ≤ seed.toOuterMeasure {s | ¬ Set.InjOn (h s) S} := seed.toOuterMeasure.mono hsub
    _ ≤ (S.card.choose 2 : ℕ) * ε := hh.toOuterMeasure_not_injOn_le S
    _ ≤ (responses.length.choose 2 : ℝ≥0∞) * ε := by gcongr
    _ = ε * (responses.length.choose 2 : ℝ≥0∞) := mul_comm _ _

/-- Bad-triple union-bound step of [BaumEtAl2026FAEST], §10.6, Lemma 10.26 (Bad event 2, p. 98):
for any `ε`-universal linear hash family `H`, `HasKOSBadTriple (H s) responses` holds with seed
probability at most `ε * (responses.length.choose 3)`. -/
theorem toOuterMeasure_hasKOSBadTriple_le
    {seed : PMF Seed} {H : Seed → V →ₗ[F] W} {ε : ℝ≥0∞}
    (hH : IsUniversalHash seed (fun s v => H s v) ε) (responses : List (F × V)) :
    seed.toOuterMeasure {s | HasKOSBadTriple (H s) responses} ≤
      ε * (responses.length.choose 3 : ℝ≥0∞) := by
  classical
  let triples : Finset (Finset (Fin responses.length)) :=
    (Finset.univ : Finset (Fin responses.length)).powersetCard 3
  let repDefect : {T // T ∈ triples} → V := fun ⟨T, hT⟩ =>
    let u := chooseTriple (Finset.mem_powersetCard.mp hT).2
    kosAffineDefect (responses.get u.1) (responses.get u.2.1) (responses.get u.2.2)
  let badSet : {T // T ∈ triples} → Set Seed := fun T =>
    {s | repDefect T ≠ 0 ∧ H s (repDefect T) = 0}
  have hcover : {s | HasKOSBadTriple (H s) responses} ⊆
      ⋃ T ∈ triples.attach, badSet T := by
    rintro s ⟨p₀, hp₀, p₁, hp₁, p₂, hp₂, hne₀₁, hne₀₂, hne₁₂, hdef, hzero⟩
    obtain ⟨i₀, rfl⟩ := List.mem_iff_get.mp hp₀
    obtain ⟨i₁, rfl⟩ := List.mem_iff_get.mp hp₁
    obtain ⟨i₂, rfl⟩ := List.mem_iff_get.mp hp₂
    have hi₀₁ : i₀ ≠ i₁ := fun heq => hne₀₁ (by rw [heq])
    have hi₀₂ : i₀ ≠ i₂ := fun heq => hne₀₂ (by rw [heq])
    have hi₁₂ : i₁ ≠ i₂ := fun heq => hne₁₂ (by rw [heq])
    let T : Finset (Fin responses.length) := {i₀, i₁, i₂}
    have hTcard : T.card = 3 :=
      Finset.card_eq_three.mpr ⟨i₀, i₁, i₂, hi₀₁, hi₀₂, hi₁₂, rfl⟩
    have hT : T ∈ triples := Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hTcard⟩
    refine Set.mem_iUnion₂.mpr ⟨⟨T, hT⟩, Finset.mem_attach _ _, ?_⟩
    have hTeq := chooseTriple_spec (Finset.mem_powersetCard.mp hT).2
    set u := chooseTriple (Finset.mem_powersetCard.mp hT).2
    have hperm := kosAffineDefect_index_perm_eq_or_neg responses hTeq hi₀₁ hi₀₂ hi₁₂
    change repDefect ⟨T, hT⟩ ≠ 0 ∧ H s (repDefect ⟨T, hT⟩) = 0
    have hrep : repDefect ⟨T, hT⟩ =
        kosAffineDefect (responses.get u.1) (responses.get u.2.1) (responses.get u.2.2) := rfl
    rw [hrep]
    rcases hperm with heq | hneg
    · exact ⟨heq ▸ hdef, heq ▸ hzero⟩
    · refine ⟨fun hr => hdef (by rw [hneg, hr, neg_zero]), ?_⟩
      rwa [hneg, map_neg, neg_eq_zero] at hzero
  have hterm (T : {T // T ∈ triples}) (_ : T ∈ triples.attach) :
      seed.toOuterMeasure (badSet T) ≤ ε := by
    by_cases hr : repDefect T = 0
    · have hemp : badSet T = ∅ := by
        ext s
        simp [badSet, hr]
      simp [hemp]
    · refine (seed.toOuterMeasure.mono ?_).trans (hH (repDefect T) 0 hr)
      intro s hs
      change H s (repDefect T) = H s 0
      rw [hs.2, map_zero]
  calc
    seed.toOuterMeasure {s | HasKOSBadTriple (H s) responses}
        ≤ seed.toOuterMeasure (⋃ T ∈ triples.attach, badSet T) :=
        seed.toOuterMeasure.mono hcover
    _ ≤ ∑ T ∈ triples.attach, seed.toOuterMeasure (badSet T) :=
        MeasureTheory.measure_biUnion_finset_le triples.attach badSet
    _ ≤ ∑ _T ∈ triples.attach, ε := Finset.sum_le_sum hterm
    _ = ε * (responses.length.choose 3 : ℝ≥0∞) := by
        simp [triples, Finset.card_powersetCard, mul_comm]

/-- Abstract response-graph step toward [BaumEtAl2026FAEST], §10.6, Corollary 10.27 (pp. 98–99),
not the concrete `VOLEHash` / Lemma 10.19 endpoint (which remains open under #4987): when
`responses` is a response graph and `H` is an `ε`-universal linear hash family, the probability
over `s ← seed` that there exists any hashed line `target` and accepted opening `p ∈ responses`
missed by `kosExtract (H s) responses target` is at most `ε * (responses.length.choose 3)`,
matching `choose |S_t| 3 · ε` on a duplicate-free enumeration of `S_t`. -/
theorem toOuterMeasure_kosExtract_graph_failure_le [DecidableEq F] [DecidableEq W]
    {seed : PMF Seed} {H : Seed → V →ₗ[F] W} {ε : ℝ≥0∞}
    (hH : IsUniversalHash seed (fun s v => H s v) ε)
    {responses : List (F × V)} (hgraph : IsResponseGraph responses) :
    seed.toOuterMeasure
      {s | ∃ (target : KOSLine W) (p : F × V),
        p ∈ responses ∧ H s p.2 = target.eval p.1 ∧
          (kosExtract (H s) responses target).eval p.1 ≠ p.2} ≤
      ε * (responses.length.choose 3 : ℝ≥0∞) := by
  refine (seed.toOuterMeasure.mono fun s hs => ?_).trans
    (toOuterMeasure_hasKOSBadTriple_le hH responses)
  rcases hs with ⟨target, p, hp, hhash, hfail⟩
  by_contra hnobad
  exact hfail (kosExtract_eval_eq_of_not_hasKOSBadTriple (H s) hgraph hnobad target hp hhash)

/-- Abstract universal-hash step of [BaumEtAl2026FAEST], §10.6, Lemma 10.26 (pp. 97–98), not the
concrete `VOLEHash` instantiation (tracked in #4987): on an arbitrary finite opening list
`responses` (without assuming `IsResponseGraph`), extraction fails with probability at most
`ε * (responses.length.choose 2 + responses.length.choose 3)`. On a duplicate-free enumeration
`responses.Nodup` of `S`, `responses.length = |S|`, matching the proof's binomial bound before
Lemma 10.26's cubic relaxation `(|S|³ / 6 + |S|² / 2) ε`. -/
theorem toOuterMeasure_kosExtract_failure_le [DecidableEq F] [DecidableEq W]
    {seed : PMF Seed} {H : Seed → V →ₗ[F] W} {ε : ℝ≥0∞}
    (hH : IsUniversalHash seed (fun s v => H s v) ε) (responses : List (F × V)) :
    seed.toOuterMeasure
      {s | ∃ (target : KOSLine W) (p : F × V),
        p ∈ responses ∧ H s p.2 = target.eval p.1 ∧
          (kosExtract (H s) responses target).eval p.1 ≠ p.2} ≤
      ε * ((responses.length.choose 2 : ℝ≥0∞) + (responses.length.choose 3 : ℝ≥0∞)) := by
  have hcover :
      {s | ∃ (target : KOSLine W) (p : F × V),
        p ∈ responses ∧ H s p.2 = target.eval p.1 ∧
          (kosExtract (H s) responses target).eval p.1 ≠ p.2} ⊆
        {s | HasKOSBadPair (H s) responses} ∪ {s | HasKOSBadTriple (H s) responses} := by
    rintro s ⟨target, p, hp, hhash, hfail⟩
    by_cases hpair : HasKOSBadPair (H s) responses
    · exact Or.inl hpair
    · right
      let accepted := responses.filter (fun q => decide (H s q.2 = target.eval q.1))
      have hgraph_acc : IsResponseGraph accepted := by
        intro p₁ hp₁ p₂ hp₂ hfst
        have hp₁' := List.mem_filter.mp hp₁
        have hp₂' := List.mem_filter.mp hp₂
        by_contra hne
        exact hpair ⟨p₁, hp₁'.1, p₂, hp₂'.1, hfst, hne,
          (of_decide_eq_true hp₁'.2).trans
            (hfst ▸ (of_decide_eq_true hp₂'.2).symm)⟩
      have hext_acc : kosExtract (H s) responses target = kosExtract (H s) accepted target := by
        simp [kosExtract, selectAccepted, accepted, List.filter_filter]
      have hp_acc : p ∈ accepted := List.mem_filter.mpr ⟨hp, decide_eq_true hhash⟩
      have hfail_acc : (kosExtract (H s) accepted target).eval p.1 ≠ p.2 := by
        rwa [← hext_acc]
      have hbad_acc : HasKOSBadTriple (H s) accepted := by
        by_contra hnobad
        exact hfail_acc
          (kosExtract_eval_eq_of_not_hasKOSBadTriple (H s) hgraph_acc hnobad target hp_acc hhash)
      rcases hbad_acc with ⟨q₀, hq₀, q₁, hq₁, q₂, hq₂, hne₀₁, hne₀₂, hne₁₂, hdef, hzero⟩
      exact ⟨q₀, (List.mem_filter.mp hq₀).1, q₁, (List.mem_filter.mp hq₁).1,
        q₂, (List.mem_filter.mp hq₂).1, hne₀₁, hne₀₂, hne₁₂, hdef, hzero⟩
  calc
    seed.toOuterMeasure
        {s | ∃ (target : KOSLine W) (p : F × V),
          p ∈ responses ∧ H s p.2 = target.eval p.1 ∧
            (kosExtract (H s) responses target).eval p.1 ≠ p.2}
        ≤ seed.toOuterMeasure
            ({s | HasKOSBadPair (H s) responses} ∪ {s | HasKOSBadTriple (H s) responses}) :=
        seed.toOuterMeasure.mono hcover
    _ ≤ seed.toOuterMeasure {s | HasKOSBadPair (H s) responses} +
          seed.toOuterMeasure {s | HasKOSBadTriple (H s) responses} :=
        MeasureTheory.measure_union_le _ _
    _ ≤ ε * (responses.length.choose 2 : ℝ≥0∞) + ε * (responses.length.choose 3 : ℝ≥0∞) :=
        add_le_add (toOuterMeasure_hasKOSBadPair_le hH responses)
          (toOuterMeasure_hasKOSBadTriple_le hH responses)
    _ = ε * ((responses.length.choose 2 : ℝ≥0∞) + (responses.length.choose 3 : ℝ≥0∞)) :=
        (mul_add _ _ _).symm

end ProbabilityBounds

end Cslib.Crypto.Protocols.VOLE
