/-
Copyright (c) 2026 Erik Demaine, Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeNatFrontends
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListMap
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListBinaryLookup
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Fold
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Lists
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString.Cut
import CslibFrontier.Tactic.PolyTime.Init
import Mathlib.Data.List.GetD

/-!
# Polynomial-time list operations

List operations for the polynomial-time calculus, using Christian Reitwiessner's encodings,
degree-bounded operations and fold rules. Indices use `encUnary`: an index returned by `idxOf`
is at most the list length, irrespective of the encoding of its elements. In particular, looking
up a variable with a large binary label does not require a certificate as long as that label.

Predicate counts and Boolean scans use only `ListEncoding` and `SizedListEncoding`: reading the
list and bounding traversal suffice because the state is a unary counter or a Boolean. Raw bit
strings and framed lists are both instances. No output-list construction capability is needed;
counting folds a counter directly instead of constructing the matching sublist.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.filter`: filtering by a polytime predicate.
* `Turing.MultiTapeTM.ComputableInPolyTime.cons`, `.listAppend`, `.map`, `.flatten`:
  constructing lists.
* `Turing.MultiTapeTM.ComputableInPolyTime.cons'`, `.listAppend'`: composition rules
  that let `fun_prop` infer the element encoding from the result.
* `Turing.MultiTapeTM.ComputableInPolyTime.mapWith`, `.flatMapWith`: constructing lists
  with a parameter; the input list may itself have polynomial encoded length.
* `Turing.MultiTapeTM.ComputableInPolyTime.mapWithInput`, `.flatMapWithInput`,
  `.filterWithInput`, `.findWithInput`, `.anyWithInput`, `.allWithInput`:
  automation rules for traversals whose body also uses the original input.
* `Turing.MultiTapeTM.ComputableInPolyTime.mapConst`, `.flatMapConst`, `.allConst`,
  `.anyConst`: traverse a fixed list without requiring an encoding of its elements.
* `Turing.MultiTapeTM.ComputableInPolyTime.mapFilterConst`: select and map fixed parameters
  with computed guards and outputs, preserving list order and duplicates.
* `Turing.MultiTapeTM.ComputableInPolyTime.mapConst`, `.flatMapConst`, `.mapFilterConst`:
  plain certificates for fixed-list templates, without encoding the fixed parameters.
* `Turing.MultiTapeTM.ComputableInPolyTime.filterWith`, `.findWith`: filtering or searching
  a polynomial-time list with a parameterized test.
* `Turing.MultiTapeTM.ComputableInPolyTime.length`, `.range`, `.replicate`: unary lengths,
  ranges and lists of a computed length, charging each repeated value.
* `Turing.MultiTapeTM.ComputableInPolyTime.zipIdx`: number list entries with unary indices.
* `Turing.MultiTapeTM.ComputableInPolyTime.zip`: pair entries of framed lists.
* `Turing.MultiTapeTM.ComputableInPolyTime.anyWith`, `.allWith`: Boolean scans with a
  parameter, applied explicitly like the fold rules.
* `Turing.MultiTapeTM.ComputableInPolyTime.countPWith`, `.anyWithEncoding`,
  `.allWithEncoding`: direct scans over readable, size-bounded list encodings.
* `Turing.MultiTapeTM.ComputableInPolyTime.countPWithInput`, `.countWithInput`: count
  predicate matches or occurrences of a computed value.
* `Turing.MultiTapeTM.ComputableInPolyTime.idxOf`: the first occurrence of an element.
* `Turing.MultiTapeTM.ComputableInPolyTime.listGetD`: lookup by a unary index.
* `Turing.MultiTapeTM.ComputableInPolyTime.listGetD_binary`: lookup by a binary index,
  which is capped at the length of the list.
* `Turing.MultiTapeTM.ComputableInPolyTime.getElem?`: optional lookup in computed lists.
* `Turing.MultiTapeTM.ComputableInPolyTime.listIsEmpty`, `.listIsEmpty'`, `.bitsIsEmpty`,
  `.head?`: inspect a list without a default element, with inference rules for framed and raw lists.
* `Turing.MultiTapeTM.ComputableInPolyTime.listReverse`, `.listReverseWithInput`:
  reverse framed lists, charging the complete encoded size of every intermediate prefix.
* `Turing.MultiTapeTM.ComputableInPolyTime.idxOfWithInput`, `.bitsGetDWithInput`:
  compositional rules for first-occurrence lookup and raw-bit access.
* `Turing.MultiTapeTM.ComputableInPolyTime.bitsDropWithInput`, `.bitsTakeWithInput`:
  runtime bit-string slicing, with computed unary indices.
* `Turing.MultiTapeTM.ComputableInPolyTime.takeUnary`, `.listTakeWithInput`,
  `.listDropWithInput`: slice framed lists at computed unary indices.
* `Turing.MultiTapeTM.bits_encList_polyTime`, `.trans_encList_polyTime`: convert between raw
  binary words and framed lists of encoded bits, also after an arbitrary binary embedding.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

variable {α β γ π : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
  {encIn : γ ↪ List Bool} {encP : π ↪ List Bool}

/-- Concatenate raw bit strings, charging for both computed words. -/
@[fun_prop]
theorem bitsAppend {left right : γ → List Bool}
    (hleft : ComputableInPolyTime left encIn encBits)
    (hright : ComputableInPolyTime right encIn encBits) :
    ComputableInPolyTime (fun x => left x ++ right x) encIn encBits :=
by
  obtain ⟨d₁, e₁, hleft⟩ := hleft.exists_degree
  obtain ⟨d₂, e₂, hright⟩ := hright.exists_degree
  exact (hleft.append hright fun _ => rfl).computableInPolyTime

/-- Read the head of any list encoding with a fixed fallback. -/
@[fun_prop]
theorem headD {encL : List α ↪ List Bool} [ListEncoding encA encL] (fallback : α) :
    ComputableInPolyTime (fun list => list.headD fallback) encL encA :=
  (ListEncoding.headD (enc₁ := encA) (enc := encL) fallback).computableInPolyTime

/-- Read the head of a computed framed list with a computed fallback, inferring the element
encoding from the list before checking the fallback or composing with an outer projection. -/
@[fun_prop, program_certificate hlist]
theorem listHeadDWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {fallback : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hfallback : ComputableInPolyTime fallback encIn encA) :
    ComputableInPolyTime (fun a => (list a).headD (fallback a)) encIn encA :=
  (optionGetDWithInput ((head? encA).comp hlist) hfallback).of_enc_eq fun a => by
    simp only [Function.comp_apply, List.headD_eq_head?_getD]

/-- Test a framed list's emptiness, determining its element encoding for automation. -/
@[fun_prop]
theorem listIsEmpty' (enc : α ↪ List Bool) :
    ComputableInPolyTime (List.isEmpty (α := α)) (encList enc) encBool :=
  listIsEmpty (encA := enc)

/-- Drop the head of a framed list, determining its element encoding for automation. -/
@[fun_prop]
theorem listTail (enc : α ↪ List Bool) :
    ComputableInPolyTime (List.tail (α := α)) (encList enc) (encList enc) :=
  tail (encA := enc)

/-- Prepending an element to a framed list is polynomial-time. -/
@[fun_prop]
theorem cons (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : α × List α => p.1 :: p.2)
      (encPair enc (encList enc)) (encList enc) :=
  (ComputableInDegree.cons enc).computableInPolyTime

/-- Concatenating two framed lists is polynomial-time. -/
@[fun_prop]
theorem listAppend (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List α => p.1 ++ p.2)
      (encPair (encList enc) (encList enc)) (encList enc) :=
  (ComputableInDegree.listAppend enc).computableInPolyTime

/-- Reverse a framed list; the accumulator is a permutation of a prefix of the input. -/
@[fun_prop]
theorem listReverse (enc : α ↪ List Bool) :
    ComputableInPolyTime List.reverse (encList enc) (encList enc) :=
  listReverseWithInput id'

/-- Find the first element passing a polynomial-time test with a fixed parameter.
The list may have any polynomial encoded length. -/
theorem findWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).find? fun a => test (par x, a))
      encIn (encOption encA) := by
  obtain ⟨d, e, htest⟩ := htest.exists_degree
  exact (ComputableInDegree.findWith htest
    (ComputableInDegree.fst encP (encList encA))
    (ComputableInDegree.snd encP (encList encA))).computableInPolyTime.comp
      (hpar.prod hlist)

/-- Search with a predicate that captures the original input. -/
@[fun_prop]
theorem findWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).find? (test x)) encIn (encOption encA) :=
  findWith htest id' hlist

/-- Keep the elements passing a polynomial-time test with a fixed parameter.
The input list may have any polynomial encoded length. -/
theorem filterWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).filter fun a => test (par x, a))
      encIn (encList encA) := by
  obtain ⟨d, e, htest⟩ := htest.exists_degree
  exact (ComputableInDegree.filterWith htest
    (ComputableInDegree.fst encP (encList encA))
    (ComputableInDegree.snd encP (encList encA))).computableInPolyTime.comp
      (hpar.prod hlist)

/-- Filter with a predicate that captures the original input. -/
@[fun_prop]
theorem filterWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).filter (test x)) encIn (encList encA) :=
  filterWith htest id' hlist

/-- Filtering a list by a polynomial-time test is polynomial-time. -/
@[fun_prop]
theorem filter {test : α → Bool} (htest : ComputableInPolyTime test encA encBool) :
    ComputableInPolyTime (List.filter test) (encList encA) (encList encA) :=
  filterWith (htest.comp (snd encBool encA)) (const true) id'

/-- Map a polynomial-time function with a fixed parameter over a polynomial-time computable list.
The list may have any polynomial encoded length. -/
theorem mapWith {f : π × α → β} {par : γ → π} {list : γ → List α}
    (hf : ComputableInPolyTime f (encPair encP encA) encB)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).map fun a => f (par x, a))
      encIn (encList encB) := by
  obtain ⟨d, e, hf⟩ := hf.exists_degree
  exact (ComputableInDegree.mapWith hf
    (ComputableInDegree.fst encP (encList encA))
    (ComputableInDegree.snd encP (encList encA))).computableInPolyTime.comp
      (hpar.prod hlist)

/-- Map an input-dependent function over a fixed list. Only its members need certificates;
the list and its elements are not part of the computational input. -/
@[fun_prop]
theorem mapConst {ι : Type*} (l : List ι) {f : γ → ι → β}
    (hf : ∀ i ∈ l, ComputableInPolyTime (fun x => f x i) encIn encB) :
    ComputableInPolyTime (fun x => l.map (f x)) encIn (encList encB) := by
  induction l with
  | nil => exact const []
  | cons a l ih =>
    exact (cons encB).comp ((hf a (List.mem_cons_self ..)).prod
      (ih fun b hb => hf b (List.mem_cons_of_mem _ hb)))

private theorem foldl_append (l : List (List α)) (acc : List α) :
    l.foldl (· ++ ·) acc = acc ++ l.flatten := by
  simpa only [List.map_id_fun, id_eq] using
    (List.foldl_append_eq_append (l := l) (f := id) (l' := acc))

private theorem length_encList_flatten_le (enc : α ↪ List Bool) (l : List (List α)) :
    (encList enc l.flatten).length ≤ (encList (encList enc) l).length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatten_cons, encList_append, List.length_append, encList_cons, length_frame]
    lia

/-- Concatenating a list of lists is polynomial-time. -/
@[fun_prop]
theorem flatten (enc : α ↪ List Bool) :
    ComputableInPolyTime List.flatten (encList (encList enc)) (encList enc) := by
  have h := foldl' (list := id) (step := fun acc a => acc ++ a) id' (const [])
    (ComputableInDegree.listAppend enc).computableInPolyTime
    (B := fun l => (encList (encList enc) l).length) .self (fun l i _ => by
      rw [foldl_append, List.nil_append]
      exact (length_encList_flatten_le enc (l.take i)).trans
        (length_encList_take_le (encList enc) l i))
  simpa only [foldl_append, List.nil_append, id_eq] using h

/-- Concatenate polynomial-time lists computed from each element and a fixed parameter. -/
theorem flatMapWith {f : π × α → List β} {par : γ → π} {list : γ → List α}
    (hf : ComputableInPolyTime f (encPair encP encA) (encList encB))
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).flatMap fun a => f (par x, a))
      encIn (encList encB) := by
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (flatten encB).comp (mapWith hf hpar hlist)

/-- Concatenate lists computed jointly from the original input and each list element.
Like `mapWithInput`, this is a composition rule for `fun_prop`. -/
@[fun_prop]
theorem flatMapWithInput {f : γ → α → List β} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hf : ComputableInPolyTime (fun p : γ × α => f p.1 p.2)
      (encPair encIn encA) (encList encB)) :
    ComputableInPolyTime (fun x => (list x).flatMap (f x)) encIn (encList encB) :=
  flatMapWith hf id' hlist

/-- Concatenate input-dependent lists indexed by a fixed list of parameters.
No encoding of the fixed parameters is required. -/
@[fun_prop]
theorem flatMapConst {ι : Type*} (l : List ι) {f : γ → ι → List β}
    (hf : ∀ i ∈ l, ComputableInPolyTime (fun x => f x i) encIn (encList encB)) :
    ComputableInPolyTime (fun x => l.flatMap (f x)) encIn (encList encB) := by
  simpa only [Function.comp_def, List.flatten_eq_flatMap, List.flatMap_map, id_eq] using
    (flatten encB).comp (mapConst l hf)

/-- Filter and map a fixed list using computed guards and outputs. No encoding of the fixed
parameters is required; only members of the list need certificates. -/
@[fun_prop]
theorem mapFilterConst {ι : Type*} (list : List ι) {test : γ → ι → Bool} {f : γ → ι → β}
    (htest : ∀ i ∈ list, ComputableInPolyTime (fun a => test a i) encIn encBool)
    (hf : ∀ i ∈ list, ComputableInPolyTime (fun a => f a i) encIn encB) :
    ComputableInPolyTime (fun a => (list.filter (test a)).map (f a))
      encIn (encList encB) := by
  induction list with
  | nil => exact const []
  | cons a list ih =>
    have htail := ih (fun i hi => htest i (List.mem_cons_of_mem _ hi))
      (fun i hi => hf i (List.mem_cons_of_mem _ hi))
    simpa only [List.filter_cons, List.map_cons, apply_ite] using
      (htest a (List.mem_cons_self ..)).ite ((hf a (List.mem_cons_self ..)).cons' htail) htail

/-- The length of a list, in unary, including raw bit strings. -/
theorem length (enc : α ↪ List Bool) {encL : List α ↪ List Bool} [ListEncoding enc encL]
    [SizedListEncoding enc encL] :
    ComputableInPolyTime (fun l : List α => l.length) encL encUnary := by
  have h := foldl' (encA := enc) (encL := encL) (list := id)
    (step := fun n _ => n + 1) id' (const 0)
    (ComputableInDegree.unary_succ.computableInPolyTime.comp (fst encUnary enc))
    (B := fun l => (encL l).length) .self (fun l i _ => by
      simpa [List.foldl_const] using (Nat.min_le_right i l.length).trans
        (SizedListEncoding.length_le (encA := enc) (encL := encL) l))
  simpa [List.foldl_const] using h

/-- Length of a framed list; the element encoding is inferred from the list encoding. -/
@[fun_prop]
theorem length_list (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun l : List α => l.length) (encList enc) encUnary := length enc

/-- Length of a raw bit string. -/
@[fun_prop]
theorem length_bits :
    ComputableInPolyTime (fun l : List Bool => l.length) encBits encUnary := length encBool

/-- The encoded input length, computed in unary by reading the input word. -/
@[fun_prop]
theorem encoding_length (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun a => (enc a).length) enc encUnary :=
  length_bits.comp (of_eq (encOut := encBits) fun _ => rfl)

/-- Length of a computed raw bit string, fixing the intermediate encoding for proof search.
Registered after `encoding_length` so `fun_prop` first tries this rule on computed words. -/
@[fun_prop]
theorem length_bits_comp {input : α ↪ List Bool} {word : α → List Bool}
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => (word a).length) input encUnary :=
  length_bits.comp hword

/-- Count predicate matches directly over any readable, size-bounded list encoding.
The accumulator is a unary counter; the certificate does not construct a list of matches. -/
theorem countPWith {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime (fun x => (list x).countP fun a => test (par x, a))
      encIn encUnary := by
  have heq (p : π) (l : List α) (n : ℕ) :
      l.foldl (fun n a => n + (test (p, a)).toNat) n = n + l.countP fun a => test (p, a) := by
    induction l generalizing n with
    | nil => simp
    | cons a l ih =>
      cases h : test (p, a) <;> simp [h, ih, Nat.add_assoc, Nat.add_comm]
  have hstep : ComputableInPolyTime
      (fun q : (π × ℕ) × α => q.1.2 + (test (q.1.1, q.2)).toNat)
      (encPair (encPair encP encUnary) encA) encUnary := by fun_prop
  have h := foldlWith_of_bounded_growth (encA := encA) (encL := encL) (encB := encUnary)
    (step := fun p n a => n + (test (p, a)).toNat) hpar hlist (const 0) hstep
    (growth := fun _ => 1) (.const 1) (fun x n a _ => by
      simp only [encUnary_apply, List.length_replicate]
      have := Bool.toNat_le (test (par x, a))
      omega)
  simpa only [heq, Nat.zero_add] using h

/-- Count matches of a predicate that captures the original input. The count is in unary. -/
@[fun_prop]
theorem countPWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).countP (test x)) encIn encUnary :=
  countPWith htest id' hlist

/-- Count occurrences of a computed value using lawful Boolean equality. -/
@[fun_prop, program_certificate hlist]
theorem countWithInput [BEq α] [LawfulBEq α] {list : γ → List α} {value : γ → α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun x => (list x).count (value x)) encIn encUnary := by
  simp only [List.count_eq_countP]
  apply countPWithInput hlist
  fun_prop

/-- Repeat a computed value a computed unary number of times, charging every copy and delimiter. -/
@[fun_prop]
theorem replicate {count : γ → ℕ} {value : γ → α}
    (hcount : ComputableInPolyTime count encIn encUnary)
    (hvalue : ComputableInPolyTime value encIn encA) :
    ComputableInPolyTime (fun x => List.replicate (count x) (value x))
      encIn (encList encA) := by
  simpa only [Function.comp_def, List.map_const', List.length_range] using
    mapWithInput (f := fun x _ => value x) (range.comp hcount)
      (hvalue.comp (fst encIn encUnary))

/-- Scan any readable, size-bounded list encoding for a predicate match. -/
theorem anyWithEncoding {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime (fun x => (list x).any fun a => test (par x, a)) encIn encBool := by
  have heq (p : π) (l : List α) (b : Bool) :
      l.foldl (fun b a => b || test (p, a)) b = (b || l.any fun a => test (p, a)) := by
    induction l generalizing b <;> simp [*, Bool.or_assoc]
  have hstep : ComputableInPolyTime
      (fun q : (π × Bool) × α => q.1.2 || test (q.1.1, q.2))
      (encPair (encPair encP encBool) encA) encBool := by fun_prop
  have h := foldlWith (encA := encA) (encB := encBool)
    (step := fun p b a => b || test (p, a))
    hpar hlist (const false) hstep (B := fun _ => 1) (.const 1)
    (fun _ _ _ => by simp)
  simpa only [heq, Bool.false_or] using h

/-- Test every element of any readable, size-bounded list encoding. -/
theorem allWithEncoding {encL : List α ↪ List Bool} [ListEncoding encA encL]
    [SizedListEncoding encA encL] {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn encL) :
    ComputableInPolyTime (fun x => (list x).all fun a => test (par x, a)) encIn encBool := by
  have h := bool_not.comp (anyWithEncoding (bool_not.comp htest) hpar hlist)
  simpa only [Function.comp_def, ← List.all_eq_not_any_not] using h

/-- Test whether any element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem anyWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).any fun a => test (par x, a)) encIn encBool :=
  anyWithEncoding htest hpar hlist

/-- Test whether every element satisfies a polynomial-time predicate with a fixed parameter. -/
theorem allWith {test : π × α → Bool} {par : γ → π} {list : γ → List α}
    (htest : ComputableInPolyTime test (encPair encP encA) encBool)
    (hpar : ComputableInPolyTime par encIn encP)
    (hlist : ComputableInPolyTime list encIn (encList encA)) :
    ComputableInPolyTime (fun x => (list x).all fun a => test (par x, a)) encIn encBool :=
  allWithEncoding htest hpar hlist

/-- Test whether any list element satisfies a predicate that captures the original input. -/
@[fun_prop]
theorem anyWithInput {test : γ → α → Bool} {list : γ → List α}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (htest : ComputableInPolyTime (fun p : γ × α => test p.1 p.2)
      (encPair encIn encA) encBool) :
    ComputableInPolyTime (fun x => (list x).any (test x)) encIn encBool :=
  anyWith htest id' hlist

/-- Test whether any element of a fixed list satisfies its input-dependent predicate.
The fixed list needs no element encoding or uniform certificate over all possible elements. -/
@[fun_prop, program_certificate]
theorem anyConst {ι : Type*} (l : List ι) {test : γ → ι → Bool}
    (htest : ∀ i ∈ l, ComputableInPolyTime (fun x => test x i) encIn encBool) :
    ComputableInPolyTime (fun x => l.any (test x)) encIn encBool := by
  simpa only [Function.comp_def, List.any_eq_not_all_not] using
    bool_not.comp (allConst l fun i hi => bool_not.comp (htest i hi))

open Internal.ListIndex

/-- Drop a computed unary number of elements from a computed framed list. -/
@[fun_prop]
theorem listDropWithInput {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun x => (list x).drop (count x)) encIn (encList encA) :=
  (dropUnary (encA := encA)).comp (hlist.prod hcount)

/-- Take a unary number of framed-list elements using certified reversal and dropping. -/
@[fun_prop]
theorem takeUnary (enc : α ↪ List Bool) : ComputableInPolyTime
    (fun p : List α × ℕ => p.1.take p.2) (encPair (encList enc) encUnary) (encList enc) := by
  have h : ComputableInPolyTime
      (fun p : List α × ℕ => (p.1.reverse.drop (p.1.length - p.2)).reverse)
      (encPair (encList enc) encUnary) (encList enc) := by fun_prop
  simpa only [← List.reverse_take, List.reverse_reverse] using h

/-- Take a computed unary number of elements from a computed framed list. -/
@[fun_prop]
theorem listTakeWithInput {list : γ → List α} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun x => (list x).take (count x)) encIn (encList encA) :=
  (takeUnary encA).comp (hlist.prod hcount)

/-- Drop a computed unary number of bits from a computed bit string. -/
@[fun_prop]
theorem bitsDropWithInput {list : γ → List Bool} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun x => (list x).drop (count x)) encIn encBits :=
  (dropUnary (encA := encBool)).comp (hlist.prod hcount)

/-- Take a unary number of bits. Reversing and dropping reuses the certified list operations. -/
@[fun_prop]
theorem bitsTake : ComputableInPolyTime
    (fun p : List Bool × ℕ => p.1.take p.2) (encPair encBits encUnary) encBits := by
  have h : ComputableInPolyTime
      (fun p : List Bool × ℕ => (p.1.reverse.drop (p.1.length - p.2)).reverse)
      (encPair encBits encUnary) encBits := by fun_prop
  simpa only [← List.reverse_take, List.reverse_reverse] using h

/-- Take a computed unary number of bits from a computed bit string. -/
@[fun_prop]
theorem bitsTakeWithInput {list : γ → List Bool} {count : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hcount : ComputableInPolyTime count encIn encUnary) :
    ComputableInPolyTime (fun x => (list x).take (count x)) encIn encBits :=
  bitsTake.comp (hlist.prod hcount)

/-- Read a computed bit string at a computed unary index. -/
@[fun_prop]
theorem bitsGetDWithInput {list : γ → List Bool} {index : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn encBits)
    (hindex : ComputableInPolyTime index encIn encUnary) (fallback : Bool) :
    ComputableInPolyTime (fun x => (list x).getD (index x) fallback) encIn encBool :=
  (bitsGetD fallback).comp (hlist.prod hindex)

/-- Zip framed lists, charging both inputs and every pair in the output. -/
@[fun_prop]
theorem zip {α β : Type} (encA : α ↪ List Bool) (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List α × List β => p.1.zip p.2)
      (encPair (encList encA) (encList encB)) (encList (encPair encA encB)) := by
  rcases isEmpty_or_nonempty α with h | h
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.1 with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    rw [heq]
    exact const []
  rcases isEmpty_or_nonempty β with h' | h'
  · have heq : (fun p : List α × List β => p.1.zip p.2) = fun _ => [] := by
      funext p
      cases p.2 with
      | nil => simp
      | cons b _ => exact isEmptyElim b
    rw [heq]
    exact const []
  obtain ⟨a⟩ := h
  obtain ⟨b⟩ := h'
  have heq (p : List α × List β) : p.1.zip p.2 =
      (List.range (min p.1.length p.2.length)).map
        (fun i => (p.1.getD i a, p.2.getD i b)) := by
    apply List.ext_getElem (by simp)
    intro i hi hi'
    have hleft : i < p.1.length := (Nat.lt_min.mp (by simpa using hi)).1
    have hright : i < p.2.length := (Nat.lt_min.mp (by simpa using hi)).2
    simp only [List.getElem_zip, List.getElem_map, List.getElem_range,
      List.getD_eq_getElem _ _ hleft, List.getD_eq_getElem _ _ hright]
  simp_rw [heq, List.getD_eq_getElem?_getD]
  fun_prop

/-- Read a computed framed list at a computed unary index with a fixed fallback, inferring the
element encoding from the list. -/
@[fun_prop]
theorem listGetDWithInput {α γ : Type} {encA : α ↪ List Bool} {encIn : γ ↪ List Bool}
    {list : γ → List α} {index : γ → ℕ}
    (hlist : ComputableInPolyTime list encIn (encList encA))
    (hindex : ComputableInPolyTime index encIn encUnary) (fallback : α) :
    ComputableInPolyTime (fun x => (list x).getD (index x) fallback) encIn encA :=
  (listGetD fallback).comp (hlist.prod hindex)

/-- Number the entries of a framed list with unary indices, charging the list and every index. -/
@[fun_prop]
theorem zipIdx {α : Type} (enc : α ↪ List Bool) :
    ComputableInPolyTime (fun list : List α => list.zipIdx)
      (encList enc) (encList (encPair enc encUnary)) := by
  rcases isEmpty_or_nonempty α with h | h
  · exact of_finite _
  · obtain ⟨fallback⟩ := h
    have heq (list : List α) : list.zipIdx =
        (List.range list.length).map (fun i => (list.getD i fallback, i)) := by
      apply List.ext_getElem (by simp)
      intro i hi hi'
      simp only [List.length_zipIdx] at hi
      simp only [List.getElem_zipIdx, List.getElem_map, List.getElem_range,
        List.getD_eq_getElem _ _ hi, Nat.zero_add]
    simp_rw [heq, List.getD_eq_getElem?_getD]
    fun_prop

end Turing.MultiTapeTM.ComputableInPolyTime

namespace Turing.MultiTapeTM

open ComputableInPolyTime

private theorem foldl_snoc (word acc : List Bool) :
    word.foldl (fun acc bit => acc ++ [bit]) acc = acc ++ word := by
  induction word generalizing acc with
  | nil => simp
  | cons bit word ih => simp only [List.foldl_cons, ih, List.append_assoc, List.singleton_append]

/-- Framing a fixed Boolean encoding, or parsing its frames and converting each symbol, takes
polynomial time. The encodings of `false` and `true` can be arbitrary fixed words. -/
theorem bits_encList_polyTime (enc : Bool ↪ List Bool) :
    ComputableInPolyTime (fun word => word) encBits (encList enc) ∧
      ComputableInPolyTime (fun word => word) (encList enc) encBits := by
  let C := 2 * max (enc false).length (enc true).length + 1
  have hsymbol (bit : Bool) : (enc bit).length ≤ max (enc false).length (enc true).length := by
    cases bit
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hforward := foldl' (encA := encBool) (encL := encBits) (encB := encList enc)
    (step := fun acc bit => acc ++ [bit]) id' (const [])
    ((ComputableInDegree.snoc enc).computableInPolyTime.comp
      ((fst (encList enc) encBool).prod
        ((of_finite (id : Bool → Bool) (encIn := encBool) (encOut := enc)).comp
          (snd (encList enc) encBool))))
    (B := fun word : List Bool => word.length * C)
    (PolyBounded.self.mul (.const C)) (by
      intro word i hi
      simp only [foldl_snoc, List.nil_append]
      exact (length_encList_le enc _ (fun bit _ => hsymbol bit)).trans
        (Nat.mul_le_mul_right C (by simp only [List.length_take]; omega)))
  have hreverse := foldl' (encA := enc) (encL := encList enc) (encB := encBits)
    (step := fun acc bit => acc ++ [bit]) id' (const [])
    (bitsAppend (fst encBits enc)
      ((of_finite (fun bit : Bool => [bit]) (encIn := enc) (encOut := encBits)).comp
        (snd encBits enc)))
    (B := fun word : List Bool => (encList enc word).length)
    PolyBounded.self (by
      intro word i hi
      simp only [foldl_snoc, List.nil_append, encBits_apply, List.length_take]
      exact (Nat.min_le_right _ _).trans (length_le_length_encList enc word))
  constructor
  · simpa only [foldl_snoc, List.nil_append, id_eq] using hforward
  · simpa only [foldl_snoc, List.nil_append, id_eq] using hreverse

/-- The word conversion preserves an arbitrary caller-supplied encoding. No computable inverse
of `encIn` is assumed: expose its word, convert that word, and reuse the resulting encoding. -/
theorem trans_encList_polyTime {α : Type} (encIn : α ↪ List Bool)
    (enc : Bool ↪ List Bool) :
    ComputableInPolyTime (fun a => a) encIn (encIn.trans (encList enc)) ∧
      ComputableInPolyTime (fun a => a) (encIn.trans (encList enc)) encIn := by
  obtain ⟨hforward, hreverse⟩ := bits_encList_polyTime enc
  constructor
  · exact (hforward.comp (of_eq (f := encIn) (encOut := encBits) fun _ => rfl)).of_enc_eq
      fun _ => rfl
  · have hexpose : ComputableInPolyTime encIn (encIn.trans (encList enc))
        (encList enc) := of_eq fun _ => rfl
    exact (hreverse.comp hexpose).of_enc_eq fun _ => rfl

end Turing.MultiTapeTM
