/-
Copyright (c) 2026 Samuel Schlesinger, Olivia Daniels. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Olivia Daniels
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ACC0.UniversalSimulation
public import CslibFrontier.Computability.Complexity.Classes.Space
import Cslib.Foundations.Data.Polynomial.Monotone
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolySpace.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Polynomial

/-!
# One polynomial-time evaluator for all polynomial-space functions, given advice

If `PSPACE ⊆ P/poly`, a single polynomial-time function `G` computes every function in
polynomial space from its input and a polynomial-size advice string depending on the bound
on the input length (`Cslib.Complexity.EasyWitness.exists_adviceEval_of_PSPACE_subset_PPoly`).
This is the step of [ImpagliazzoKabanetsWigderson2002] that turns a collapse of `PSPACE` into
`P/poly` into a uniform polynomial-time evaluator with advice for the best replies of a prover.

For a function `f` the advice for the bound `N` is the encoded list
`encList (encPair encBits encBits) A`, where `A !! m` is the pair of codes
(`Cslib.Circuits.Boolean.evalPrefix`) of two small circuits at input length `m`, for every
`m < 2 * B + N + 1` with `B` a bound on the length of `f x` for `|x| ≤ N`. The first circuit
decides the language of `frame (replicate j true) ++ x` with `(f x)[j] = true`, and the second the
language of those words with `j < |f x|`; both languages are in `PSPACE` and so, by the
hypothesis, have polynomial-size circuits. The evaluator `G (w, x)` decodes the list `A` from
`w`, computes the length of `f x` as the number of `j` for which the second circuit accepts
`frame (replicate j true) ++ x`, and then reads the bits of `f x` from the first circuit, running
every circuit with the polynomial-time circuit evaluator `circuitEvalLanguage`. The evaluator is
total, whatever the advice.

## Main results

* `Cslib.Complexity.EasyWitness.exists_adviceEval_of_PSPACE_subset_PPoly`: if
  `PSPACE ⊆ P/poly`, one polynomial-time `G` computes every polynomial-space function from
  polynomial-size advice, for every bound on the input length.

## References

* [R. Impagliazzo, V. Kabanets, A. Wigderson, *In search of an easy witness: exponential time vs.
  probabilistic polynomial time*][ImpagliazzoKabanetsWigderson2002]
-/

public section

namespace Cslib.Complexity.EasyWitness

open Turing.MultiTapeTM Cslib.Circuits Cslib.Circuits.Boolean

/-! ### The evaluator -/

/-- Total decoder of the advice: a list of pairs of circuit codes. -/
private def decAdvice : Decoder (encList (encPair encBits encBits)) :=
  Decoder.list (Decoder.pair Decoder.bits Decoder.bits)

/-- The word `frame (replicate j true) ++ x`, of length `2 j + 1 + |x|`, that selects the `j`-th
output bit of a function on the input `x`. -/
private def queryWord (j : ℕ) (x : List Bool) : List Bool :=
  frame (List.replicate j true) ++ x

private theorem length_queryWord (j : ℕ) (x : List Bool) :
    (queryWord j x).length = 2 * j + 1 + x.length := by
  simp only [queryWord, List.length_append, length_frame, List.length_replicate]

private theorem unframe_queryWord (j : ℕ) (x : List Bool) :
    unframe (queryWord j x) = List.replicate j true :=
  unframe_frame_append _ _

private theorem dropFrame_queryWord (j : ℕ) (x : List Bool) : dropFrame (queryWord j x) = x :=
  dropFrame_frame_append _ _

/-- **The evaluator with advice**, given a Boolean evaluator `E` of circuit-code words. On the
pair `(w, x)` it decodes `w` as a list `A` of pairs of codes and returns the list of the bits
`E (A !! m).1 ++ queryWord j x` over the `j` with `E (A !! m).2 ++ queryWord j x`, where
`m = 2 j + 1 + |x|` is a valid index of `A`. -/
private def adviceEval (E : List Bool → Bool) (p : List Bool × List Bool) : List Bool :=
  ((List.range (decAdvice.decode p.1).length).filter fun j =>
      decide ((decAdvice.decode p.1).drop (queryWord j p.2).length ≠ []) &&
        E (((decAdvice.decode p.1).getD (queryWord j p.2).length ([], [])).2 ++
          queryWord j p.2)).map
    fun j => E (((decAdvice.decode p.1).getD (queryWord j p.2).length ([], [])).1 ++
      queryWord j p.2)

open ComputableInPolyTime in
/-- The evaluator is computable in polynomial time, whatever the polynomial-time evaluator `E`
of circuit-code words. -/
private theorem adviceEval_computable {E : List Bool → Bool}
    (hE : ComputableInPolyTime E encBits encBool) :
    ComputableInPolyTime (adviceEval E) (encPair encBits encBits) encBits := by
  have hA : ComputableInPolyTime (fun p : List Bool × List Bool => decAdvice.decode p.1)
      (encPair encBits encBits) (encList (encPair encBits encBits)) :=
    decAdvice.computableInPolyTime.comp (fst encBits encBits)
  have hlenA : ComputableInPolyTime
      (fun p : List Bool × List Bool => (decAdvice.decode p.1).length)
      (encPair encBits encBits) encUnary := (length_list (encPair encBits encBits)).comp hA
  have hrange := range.comp hlenA
  have hj : ComputableInPolyTime (fun q : (List Bool × List Bool) × ℕ => q.2)
      (encPair (encPair encBits encBits) encUnary) encUnary := snd _ _
  have hrep : ComputableInPolyTime
      (fun q : (List Bool × List Bool) × ℕ => List.replicate q.2 true)
      (encPair (encPair encBits encBits) encUnary) encBits :=
    hj.of_enc_eq (encD := encBits) fun q => rfl
  have hx : ComputableInPolyTime (fun q : (List Bool × List Bool) × ℕ => q.1.2)
      (encPair (encPair encBits encBits) encUnary) encBits := (snd _ _).comp (fst _ _)
  have hq : ComputableInPolyTime (fun q : (List Bool × List Bool) × ℕ => queryWord q.2 q.1.2)
      (encPair (encPair encBits encBits) encUnary) encBits :=
    bitsAppend (ComputableInPolyTime.frame.comp hrep) hx
  have hA' : ComputableInPolyTime
      (fun q : (List Bool × List Bool) × ℕ => decAdvice.decode q.1.1)
      (encPair (encPair encBits encBits) encUnary) (encList (encPair encBits encBits)) :=
    hA.comp (fst _ _)
  have hentry : ComputableInPolyTime (fun q : (List Bool × List Bool) × ℕ =>
      (decAdvice.decode q.1.1).getD (queryWord q.2 q.1.2).length ([], []))
      (encPair (encPair encBits encBits) encUnary) (encPair encBits encBits) :=
    listGetDWithInput hA' (length_bits_comp hq) ([], [])
  have hvalid : ComputableInPolyTime (fun q : (List Bool × List Bool) × ℕ =>
      decide ((decAdvice.decode q.1.1).drop (queryWord q.2 q.1.2).length ≠ []))
      (encPair (encPair encBits encBits) encUnary) encBool :=
    decide_ne (listDropWithInput hA' (length_bits_comp hq)) (const [])
  have hbit : ComputableInPolyTime (fun q : (List Bool × List Bool) × ℕ =>
      E (((decAdvice.decode q.1.1).getD (queryWord q.2 q.1.2).length ([], [])).1 ++
        queryWord q.2 q.1.2))
      (encPair (encPair encBits encBits) encUnary) encBool :=
    hE.comp (bitsAppend ((fst _ _).comp hentry) hq)
  have hlen : ComputableInPolyTime (fun q : (List Bool × List Bool) × ℕ =>
      decide ((decAdvice.decode q.1.1).drop (queryWord q.2 q.1.2).length ≠ []) &&
      E (((decAdvice.decode q.1.1).getD (queryWord q.2 q.1.2).length ([], [])).2 ++
        queryWord q.2 q.1.2))
      (encPair (encPair encBits encBits) encUnary) encBool :=
    bool_and' hvalid (hE.comp (bitsAppend ((snd _ _).comp hentry) hq))
  have hfil := filterWithInput (test := fun (p : List Bool × List Bool) (j : ℕ) =>
      decide ((decAdvice.decode p.1).drop (queryWord j p.2).length ≠ []) &&
      E (((decAdvice.decode p.1).getD (queryWord j p.2).length ([], [])).2 ++
        queryWord j p.2)) hrange hlen
  have hmap := mapWith (f := fun q : (List Bool × List Bool) × ℕ =>
      E (((decAdvice.decode q.1.1).getD (queryWord q.2 q.1.2).length ([], [])).1 ++
        queryWord q.2 q.1.2)) hbit id' hfil
  exact (bits_encList_polyTime encBool).2.comp hmap

/-- **Correctness of the evaluator on well-formed advice.** If the entries of `A` at the indices
`2 j + 1 + |x|` decide, through `E`, the membership `j < |g|` and the bits of `g`, and `A` is long
enough, then the evaluator on the encoding of `A` and the input `x` returns `g`. -/
private theorem adviceEval_encList (E : List Bool → Bool) (A : List (List Bool × List Bool))
    (x g : List Bool)
    (hlen : ∀ j, 2 * j + 1 + x.length < A.length →
      (E ((A.getD (queryWord j x).length ([], [])).2 ++ queryWord j x) = true ↔ j < g.length))
    (hbit : ∀ j < g.length,
      E ((A.getD (queryWord j x).length ([], [])).1 ++ queryWord j x) = g.getD j false)
    (hA : 2 * g.length + x.length ≤ A.length) :
    adviceEval E (encList (encPair encBits encBits) A, x) = g := by
  unfold adviceEval
  simp only [decAdvice.decode_enc]
  have hfil : (List.range A.length).filter (fun j =>
      decide (A.drop (queryWord j x).length ≠ []) &&
        E ((A.getD (queryWord j x).length ([], [])).2 ++ queryWord j x)) =
      List.range g.length := by
    obtain ⟨k, hk⟩ : ∃ k, A.length = g.length + k := ⟨A.length - g.length, by omega⟩
    rw [hk, List.range_add, List.filter_append]
    have hleft : (List.range g.length).filter (fun j =>
        decide (A.drop (queryWord j x).length ≠ []) &&
          E ((A.getD (queryWord j x).length ([], [])).2 ++ queryWord j x)) =
        List.range g.length := by
      refine List.filter_eq_self.2 fun j hj => ?_
      have hj := List.mem_range.1 hj
      have hlt : 2 * j + 1 + x.length < A.length := by omega
      have hv : A.drop (queryWord j x).length ≠ [] := by
        rw [Ne, List.drop_eq_nil_iff, length_queryWord]
        omega
      simp only [hv, ne_eq, not_false_eq_true, decide_true, Bool.true_and]
      exact (hlen j hlt).2 hj
    have hright : ((List.range k).map (g.length + ·)).filter (fun j =>
        decide (A.drop (queryWord j x).length ≠ []) &&
          E ((A.getD (queryWord j x).length ([], [])).2 ++ queryWord j x)) = [] := by
      refine List.filter_eq_nil_iff.2 fun j hj => ?_
      obtain ⟨i, -, rfl⟩ := List.mem_map.1 hj
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro hv
      have hlt : 2 * (g.length + i) + 1 + x.length < A.length := by
        by_contra h
        exact hv (by rw [List.drop_eq_nil_iff, length_queryWord]; omega)
      rw [(hlen _ hlt)]
      omega
    rw [hleft, hright, List.append_nil]
  rw [hfil]
  refine List.ext_getElem (by simp) fun i hi₁ hi₂ => ?_
  have hi : i < g.length := by simpa using hi₁
  simp only [List.getElem_map, List.getElem_range]
  rw [hbit i hi]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-! ### Languages of the bits and of the length of a function -/

/-- The bit of `f x` selected by a query word `frame (replicate j true) ++ x`. -/
private def outputBit (f : List Bool → List Bool) (y : List Bool) : Bool :=
  (f (dropFrame y)).getD (unframe y).length false

/-- Whether the length of `f x` exceeds the index `j` of a query word
`frame (replicate j true) ++ x`. -/
private def outputLong (f : List Bool → List Bool) (y : List Bool) : Bool :=
  decide ((f (dropFrame y)).drop (unframe y).length ≠ [])

private theorem outputBit_queryWord (f : List Bool → List Bool) (j : ℕ) (x : List Bool) :
    outputBit f (queryWord j x) = (f x).getD j false := by
  simp only [outputBit, unframe_queryWord, dropFrame_queryWord, List.length_replicate]

private theorem outputLong_queryWord (f : List Bool → List Bool) (j : ℕ) (x : List Bool) :
    outputLong f (queryWord j x) = true ↔ j < (f x).length := by
  simp only [outputLong, unframe_queryWord, dropFrame_queryWord, List.length_replicate,
    decide_eq_true_eq, ne_eq, List.drop_eq_nil_iff, not_le]

private theorem outputBit_computable {f : List Bool → List Bool}
    (hf : ComputableInPolySpace f encBits encBits) :
    ComputableInPolySpace (outputBit f) encBits encBool := by
  have h2 := (hf.comp (ComputableInPolySpace.of_polyTime ComputableInPolyTime.dropFrame)).prod
    (ComputableInPolySpace.of_polyTime ComputableInPolyTime.unframe)
  have h3 : ComputableInPolySpace (fun p : List Bool × List Bool => p.1.getD p.2.length false)
      (encPair encBits encBits) encBool :=
    .of_polyTime (ComputableInPolyTime.bitsGetDWithInput (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.snd _ _)) false)
  exact h3.comp h2

private theorem outputLong_computable {f : List Bool → List Bool}
    (hf : ComputableInPolySpace f encBits encBits) :
    ComputableInPolySpace (outputLong f) encBits encBool := by
  have h2 := (hf.comp (ComputableInPolySpace.of_polyTime ComputableInPolyTime.dropFrame)).prod
    (ComputableInPolySpace.of_polyTime ComputableInPolyTime.unframe)
  have h3 : ComputableInPolySpace
      (fun p : List Bool × List Bool => decide (p.1.drop p.2.length ≠ []))
      (encPair encBits encBits) encBool :=
    .of_polyTime (ComputableInPolyTime.decide_ne
      (ComputableInPolyTime.bitsDropWithInput (ComputableInPolyTime.fst _ _)
        (ComputableInPolyTime.length_bits_comp (ComputableInPolyTime.snd _ _)))
      (ComputableInPolyTime.const []))
  exact h3.comp h2

/-! ### Circuits for the query languages -/

/-- A circuit code followed by an input word of the circuit's width is accepted by the evaluator
exactly when the circuit accepts that word. -/
private theorem eval_evalPrefix_iff {E : List Bool → Bool}
    (hE : ∀ w, w ∈ circuitEvalLanguage ↔ E w = true) {L : Language Bool} {m : ℕ}
    (C : Circuit signature m 1) (hC : C.Computes interpretation (single (L.slice m)))
    {y : List Bool} (hy : y.length = m) : E (evalPrefix C ++ y) = true ↔ y ∈ L := by
  rw [← hE]
  have h := mem_circuitEvalLanguage_evalPrefix C (Cslib.BitString.ofList m y)
  rw [Cslib.BitString.ofFn_ofList hy] at h
  rw [h, hC, single_apply, Language.slice_eq_true_iff, Cslib.BitString.ofFn_ofList hy]

/-! ### The main result -/

/-- **One evaluator with polynomial advice computes every polynomial-space function, if
`PSPACE ⊆ P/poly`.** The evaluator reads, from the advice, circuits for the bits and the length of
the function's value at every input length up to a bound, and evaluates them. -/
theorem exists_adviceEval_of_PSPACE_subset_PPoly
    (hS : ∀ L : Language Bool, (L : Set (List Bool)) ∈ PSPACE encBits → L ∈ PPoly) :
    ∃ G : List Bool × List Bool → List Bool,
      ComputableInPolyTime G (encPair encBits encBits) encBits ∧
      ∀ f : List Bool → List Bool, ComputableInPolySpace f encBits encBits →
        ∃ ℓ : Polynomial ℕ, ∀ N : ℕ, ∃ w : List Bool, w.length ≤ ℓ.eval N ∧
          ∀ x : List Bool, x.length ≤ N → G (w, x) = f x := by
  obtain ⟨E, hE, hEmem⟩ := circuitEvalLanguage_mem_P
  refine ⟨adviceEval E, adviceEval_computable hE, fun f hf => ?_⟩
  let Lb : Language Bool := {y | outputBit f y = true}
  let Ll : Language Bool := {y | outputLong f y = true}
  obtain ⟨Cb, pb, hpb, hCb⟩ := mem_PPoly_iff_exists_circuits.1
    (hS Lb ⟨outputBit f, outputBit_computable hf, fun _ => Iff.rfl⟩)
  obtain ⟨Cl, pl, hpl, hCl⟩ := mem_PPoly_iff_exists_circuits.1
    (hS Ll ⟨outputLong f, outputLong_computable hf, fun _ => Iff.rfl⟩)
  obtain ⟨r, hr⟩ := (hpb.add hpl).exists_polynomial_le
  obtain ⟨b₀, hb₀, hb₀le⟩ := hf.polyBounded_length
  obtain ⟨q, hq⟩ := hb₀.exists_polynomial_le
  -- the number of circuits in the advice, and the bound on a circuit code and on the advice
  let M : ℕ → ℕ := fun N => 2 * q.eval N + N + 1
  let bb : ℕ → ℕ := fun N => 124 * (r.eval (M N) + 1) * (M N + r.eval (M N) + 2)
  let W : ℕ → ℕ := fun N => M N * (2 * (3 * bb N + 1) + 1)
  have hW : PolynomiallyBounded W := by
    simp only [W, bb, M]
    fun_prop
  obtain ⟨ℓ, hℓ⟩ := hW.exists_polynomial_le
  refine ⟨ℓ, fun N => ?_⟩
  let A : List (List Bool × List Bool) :=
    (List.range (M N)).map fun m => (evalPrefix (Cb m), evalPrefix (Cl m))
  have hAlen : A.length = M N := by simp only [A, List.length_map, List.length_range]
  have hget : ∀ m < M N, A.getD m ([], []) = (evalPrefix (Cb m), evalPrefix (Cl m)) := by
    intro m hm
    simp only [A, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hm,
      Option.map_some, Option.getD_some]
  refine ⟨encList (encPair encBits encBits) A, ?_, fun x hx => ?_⟩
  · refine (Nat.le_trans ?_ (hℓ N).2)
    have h := length_encList_le (encPair encBits encBits) A (b := 3 * bb N + 1) ?_
    · rw [hAlen] at h
      exact h
    · rintro a ha
      obtain ⟨m, hm, rfl⟩ := List.mem_map.1 ha
      have hm := List.mem_range.1 hm
      have hrm : r.eval m ≤ r.eval (M N) := _root_.Polynomial.eval_mono r hm.le
      have hrb : (Cb m).size ≤ r.eval (M N) := by
        have := (hCb m).1
        have := (hr m).2
        omega
      have hrl : (Cl m).size ≤ r.eval (M N) := by
        have := (hCl m).1
        have := (hr m).2
        omega
      have hb : (evalPrefix (Cb m)).length ≤ bb N :=
        length_evalPrefix_le_of_le hm.le (Cb m) hrb
      have hl : (evalPrefix (Cl m)).length ≤ bb N :=
        length_evalPrefix_le_of_le hm.le (Cl m) hrl
      simp only [encPair_apply, encBits_apply, List.length_append, length_frame]
      omega
  · -- the advice computes `f x`
    have hg : (f x).length ≤ q.eval N := by
      have h1 := hb₀le x
      have h2 := (hq x.length).2
      have h3 : q.eval x.length ≤ q.eval N := _root_.Polynomial.eval_mono q hx
      simp only [encBits_apply] at h1
      omega
    have hM : 2 * (f x).length + x.length ≤ A.length := by
      rw [hAlen]
      simp only [M]
      omega
    refine adviceEval_encList E A x (f x) (fun j hj => ?_) (fun j hj => ?_) hM
    · have hm : 2 * j + 1 + x.length < M N := by omega
      rw [length_queryWord, hget _ hm, eval_evalPrefix_iff hEmem (L := Ll) (Cl _) (hCl _).2
        (by rw [length_queryWord])]
      exact outputLong_queryWord f j x
    · have hm : 2 * j + 1 + x.length < M N := by
        simp only [M]
        omega
      rw [length_queryWord, hget _ hm]
      rw [Bool.eq_iff_iff, eval_evalPrefix_iff hEmem (L := Lb) (Cb _) (hCb _).2
        (by rw [length_queryWord])]
      change outputBit f (queryWord j x) = true ↔ _
      rw [outputBit_queryWord]

end Cslib.Complexity.EasyWitness
