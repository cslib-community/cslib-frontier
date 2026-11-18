/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.NP.Relation
public import CslibFrontier.Computability.Complexity.Classes.TFNP
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Counting solutions of search relations

`searchCount R a` counts all solutions of a polynomially balanced relation, without identifying
solutions of different lengths. `searchCount_mem_SharpP` bridges these counts to the library's
exact-length `acceptCount`. A solution is framed and padded with **only false bits**, making
padding unique; ignoring arbitrary padding would preserve existence but change the count.

The generic completeness theorem is [Goldreich2007Draft], Theorem 6.18 (printed p. 224,
February 2007 draft): if every polynomial-time checkable, polynomially balanced search relation
reduces parsimoniously to `R`, its count is #P-complete. The reduction is the existing
`ParsimoniousReducible` on counts, exactly Definition 6.17 on the same page. A solution bijection
implies equality of counts, but the definition does not require algorithms on solutions.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime

variable {α β : Type} {enc : α ↪ List Bool}

/-- Number of bit-string solutions of `R` at `a`. For polynomially balanced relations the set
is finite. As with `Nat.card`, this is zero on infinite solution sets. -/
@[expose]
noncomputable def searchCount (R : α → List Bool → Prop) (a : α) : ℕ :=
  Nat.card {w // R a w}

/-- An exact-length relation counts the accepted words, with no multiplicity from encodings. -/
theorem searchCount_eq_acceptCount {R : α → List Bool → Prop} {V : α × List Bool → Bool}
    {a : α} {n : ℕ} (hR : ∀ w, R a w ↔ w.length = n ∧ V (a, w) = true) :
    searchCount R a = acceptCount V a n := by
  classical
  rw [searchCount, acceptCount, ← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  symm
  apply Nat.card_eq_of_bijective
    (fun w : {w : Fin n → Bool // V (a, List.ofFn w) = true} =>
      (⟨List.ofFn w.val, (hR _).2 ⟨List.length_ofFn, w.property⟩⟩ : {w // R a w}))
  constructor
  · intro u v h
    apply Subtype.ext
    exact List.ofFn_injective (congrArg Subtype.val h)
  · rintro ⟨w, hw⟩
    obtain ⟨hlen, hV⟩ := (hR w).1 hw
    subst n
    refine ⟨⟨fun i => w[i.val], ?_⟩, ?_⟩ <;> simp_all

/-- The witnesses of an `NPRelation` are in the existing balanced search class. -/
theorem NPRelation.isWitness_mem_FNP (R : NPRelation enc) : R.IsWitness ∈ FNP enc := by
  refine ⟨⟨R.certLength, fun a w hw => hw.1.le⟩,
    fun q => decide (q.2.length = R.certLength.eval (enc q.1).length) && R.verifier q, ?_, ?_⟩
  · exact bool_and'
      (decide_eq' (length_bits.comp (snd _ _))
        ((unary_eval R.certLength).comp ((encoding_length enc).comp (fst _ _))))
      R.computableInPolyTime_verifier
  · intro a w
    simp [NPRelation.IsWitness]

/-- The exact-length count of an `NPRelation` counts its actual solutions. -/
theorem NPRelation.searchCount_eq (R : NPRelation enc) (a : α) :
    searchCount R.IsWitness a = acceptCount R.verifier a (R.certLength.eval (enc a).length) :=
  searchCount_eq_acceptCount fun _ => Iff.rfl

/-- Encode one short solution as a fixed-length word, with unique false padding. -/
private def paddedSolution (n : ℕ) (w : List Bool) : List Bool :=
  frame w ++ List.replicate (n - (frame w).length) false

private theorem unframe_paddedSolution (n : ℕ) (w : List Bool) :
    unframe (paddedSolution n w) = w :=
  unframe_frame_append _ _

/-- Counts of polynomially balanced polynomial-time decidable relations are in #P.
Framing and unique false padding reconcile arbitrary solution lengths with exact-length
verifier certificates, preserving the count rather than just the domain. -/
theorem searchCount_mem_SharpP {R : α → List Bool → Prop} (hR : R ∈ FNP enc) :
    searchCount R ∈ SharpP enc := by
  obtain ⟨⟨p, hp⟩, V, hV, hRV⟩ := hR
  let q : Polynomial ℕ := 2 * p + 1
  let V' : α × List Bool → Bool := fun x =>
    decide (paddedSolution (q.eval (enc x.1).length) (unframe x.2) = x.2) &&
      V (x.1, unframe x.2)
  have hpad : ComputableInPolyTime
      (fun x : α × List Bool => paddedSolution (q.eval (enc x.1).length) (unframe x.2))
      (encPair enc encBits) encBits := by
    have ha : ComputableInPolyTime (fun x : α × List Bool => x.1)
        (encPair enc encBits) enc := fst enc encBits
    have hw := unframe.comp (snd enc encBits)
    have hf := frame.comp hw
    have hn := (unary_eval q).comp ((encoding_length enc).comp ha)
    have hlen := length_bits.comp hf
    have hpadding : ComputableInPolyTime
        (fun x : α × List Bool => List.replicate
          (q.eval (enc x.1).length -
            (Turing.MultiTapeTM.frame (Turing.MultiTapeTM.unframe x.2)).length)
          false) (encPair enc encBits) encBits := by
      exact (bitsReplicate false).comp (unary_sub' hn hlen)
    exact bitsAppend hf hpadding
  refine ⟨q, V', bool_and' (decide_eq' hpad (snd _ _))
    (hV.comp ((fst _ _).prod (unframe.comp (snd _ _)))), fun a => ?_⟩
  let S : List Bool → Prop := fun w => w.length = q.eval (enc a).length ∧ V' (a, w) = true
  rw [← searchCount_eq_acceptCount (R := fun _ w => S w) (a := a) (fun _ => Iff.rfl)]
  unfold searchCount
  refine Nat.card_eq_of_bijective
    (fun w : {w // R a w} => (⟨paddedSolution (q.eval (enc a).length) w.val, by
      have hlen := hp a w.val w.property
      have hframe : (Turing.MultiTapeTM.frame w.val).length ≤ q.eval (enc a).length := by
        simp only [length_frame, q, Polynomial.eval_add, Polynomial.eval_mul,
          Polynomial.eval_ofNat, Polynomial.eval_one]
        omega
      constructor
      · simp only [paddedSolution, List.length_append, List.length_replicate]
        omega
      · simp only [V', unframe_paddedSolution, decide_true, Bool.true_and]
        exact (hRV a w.val).1 w.property⟩ : {w // S w})) ?_
  constructor
  · intro u v h
    apply Subtype.ext
    have := congrArg (fun w => unframe w.val) h
    simpa only [unframe_paddedSolution] using this
  · rintro ⟨w, hlen, hw⟩
    have hh : paddedSolution (q.eval (enc a).length) (unframe w) = w ∧
        V (a, unframe w) = true := by
      simpa only [V', Bool.and_eq_true, decide_eq_true_eq] using hw
    refine ⟨⟨unframe w, (hRV a _).2 hh.2⟩, ?_⟩
    exact Subtype.ext hh.1

/-- [Goldreich2007Draft], Theorem 6.18: if all balanced polynomial-time checkable search
relations reduce parsimoniously to `R`, then its solution count is #P-complete. The reduction
hypothesis is on the original solution sets, not a padded relation supplied by the caller. -/
theorem sharpPComplete_searchCount {R : α → List Bool → Prop} (hR : R ∈ FNP enc)
    (hcomplete : ∀ {β : Type} (encB : β ↪ List Bool) (S : β → List Bool → Prop),
      S ∈ FNP encB → ParsimoniousReducible encB enc (searchCount S) (searchCount R)) :
    SharpPComplete enc (searchCount R) := by
  refine ⟨searchCount_mem_SharpP hR, ?_⟩
  intro β encB f hf
  obtain ⟨p, V, hV, hf⟩ := hf
  let S : NPRelation encB := ⟨p, V, hV⟩
  have h := hcomplete encB S.IsWitness S.isWitness_mem_FNP
  convert h using 1
  funext a
  exact (hf a).trans (S.searchCount_eq a).symm

end Cslib.Complexity
