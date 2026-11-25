/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Oracle.Counting
public import CslibFrontier.Computability.Complexity.Classes.SharpP.Completeness
public import CslibFrontier.Computability.Complexity.Reduction.Turing
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import CslibFrontier.Computability.Complexity.Classes.Oracle.Closure
import CslibFrontier.Computability.Complexity.Classes.Oracle.PolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import CslibFrontier.Foundations.Data.Nat.Bits

/-!
# Polynomial-time counting Turing reductions

Polynomial-time Turing reductions between counting functions (`f ≤_T^#P g`), defined using
`Cslib.Complexity.PolyTimeOracleProgram` against the bit-graph oracle predicate `AnswersBits`
([Valiant 1979][Valiant1979], [Arora and Barak][AroraBarak09]).

A counting oracle `g : β → ℕ` exposes its bits `(b, i) ↦ (g b).testBit i` through
`AnswersBits encB g A`. Any batch of oracle calls with a polynomial-time unary bit-length bound
is assembled via `queryWords` (`batchNatOracleProgram` / `PolyTimeOracleProgram.of_batchNatBits`),
and any problem in `#P` whose counting Turing reduction target lies in `FP` (with a polynomial-time
total decoder for its input encoding) drops to `FP`.

## Main definitions

* `Cslib.Complexity.CountingTuringReducible`: polynomial-time counting Turing reduction.
* `Cslib.Complexity.CountingTuringHard`, `Cslib.Complexity.CountingTuringComplete`: hardness
  and completeness for `#P` under counting Turing reductions.
* `Cslib.Complexity.queryNatBits`, `Cslib.Complexity.batchNatOracleProgram`: bit-oracle query
  programs reading bounded-width binary answers via `queryWords`.

## Main results

* `Cslib.Complexity.ParsimoniousReducible.comp_countingTuringReducible`,
  `Cslib.Complexity.SharpPHard.trans_countingTuring`: transferring `#P`-hardness from parsimonious
  hardness across a counting Turing reduction.
* `Cslib.Complexity.PolyTimeOracleProgram.of_batchNatBits`: batch builder for counting Turing
  reductions without direct oracle-monad plumbing.
* `Cslib.Complexity.CountingTuringReducible.computableInPolyTime_of_decoder`: collapsing a counting
  Turing reduction to polynomial time when the oracle function is in `FP`.

## References

* [L. G. Valiant, *The complexity of computing the permanent*][Valiant1979].
* [L. G. Valiant, *The complexity of enumeration and reliability problems*][Valiant1979Enumeration].
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09].
-/

public section

namespace Cslib.Complexity

open Probability Turing.MultiTapeTM

section Core

variable {α β γ : Type}

/-- Polynomial-time counting Turing reduction (`f ≤_T^#P g`): `f` is computed by a polynomial-time
oracle program with access to any bit-graph oracle satisfying `AnswersBits encB g`. -/
@[expose] def CountingTuringReducible (encA : α ↪ List Bool) (encB : β ↪ List Bool)
    (f : α → ℕ) (g : β → ℕ) : Prop :=
  PolyTimeOracleProgram encA encNat (AnswersBits encB g) (· = f)

/-- A counting function `g` is `#P`-hard under polynomial-time counting Turing reductions when every
function in `#P` reduces to it. -/
@[expose] def CountingTuringHard (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  ∀ ⦃α : Type⦄ (encA : α ↪ List Bool) (f : α → ℕ),
    f ∈ SharpP encA → CountingTuringReducible encA encB f g

/-- A counting function `g` is `#P`-complete under counting Turing reductions when `g ∈ #P` and `g`
is `#P`-hard under counting Turing reductions. -/
@[expose] def CountingTuringComplete (encB : β ↪ List Bool) (g : β → ℕ) : Prop :=
  g ∈ SharpP encB ∧ CountingTuringHard encB g

/-- Precomposing a counting Turing reduction with a parsimonious reduction yields a counting
Turing reduction. -/
theorem ParsimoniousReducible.comp_countingTuringReducible
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {encC : γ ↪ List Bool}
    {f : α → ℕ} {h : β → ℕ} {g : γ → ℕ}
    (hfh : ParsimoniousReducible encA encB f h)
    (hhg : CountingTuringReducible encB encC h g) :
    CountingTuringReducible encA encC f g := by
  obtain ⟨r, hr, hfr⟩ := hfh
  obtain ⟨prog, hprog, hspec⟩ := hhg
  exact ⟨fun a => prog (r a), hprog.preprocess hr, fun A hA =>
    funext fun a => (congrFun (hspec A hA) (r a)).trans (hfr a).symm⟩

/-- Every parsimoniously `#P`-hard function remains `#P`-hard under counting Turing reductions once
composed with a counting Turing reduction. -/
theorem SharpPHard.trans_countingTuring
    {encB : β ↪ List Bool} {encC : γ ↪ List Bool} {h : β → ℕ} {g : γ → ℕ}
    (hh : SharpPHard encB h) (hhg : CountingTuringReducible encB encC h g) :
    CountingTuringHard encC g := fun _ encA f hf =>
  (hh encA f hf).comp_countingTuringReducible hhg

end Core

section BatchOracle

variable {α β : Type}

/-- Query word list asking bits `0, …, K - 1` of a single oracle argument `b : β`. -/
def natBitWords (encB : β ↪ List Bool) (b : β) (K : ℕ) : List (List Bool) :=
  (List.range K).map fun i => encPair encB encNat (b, i)

/-- Query word list asking bits `0, …, K - 1` of each oracle argument in `qs`. -/
def batchNatBitWords (encB : β ↪ List Bool) (qs : List β) (K : ℕ) : List (List Bool) :=
  qs.flatMap fun b => natBitWords encB b K

/-- Decode `count` consecutive `K`-bit little-endian segments from `bits`. -/
def decodeNatBatch (count K : ℕ) (bits : List Bool) : List ℕ :=
  (List.range count).map fun j => ofBits ((bits.drop (j * K)).take K)

/-- Ask the `K` low-order bits of a single oracle call `b` and reconstruct the binary natural. -/
def queryNatBits (encB : β ↪ List Bool) (b : β) (K : ℕ) : WordQueryComp Unit ℕ :=
  ofBits <$> queryWords (natBitWords encB b K)

/-- Ask the `bound a` low-order bits of every `b ∈ queries a` in one batch and combine the
decoded naturals with `combine`. -/
def batchNatOracleProgram (encB : β ↪ List Bool) (queries : α → List β)
    (bound : α → ℕ) (combine : α × List ℕ → ℕ) (a : α) : WordQueryComp Unit ℕ :=
  (fun bits => combine (a, decodeNatBatch (queries a).length (bound a) bits)) <$>
    queryWords (batchNatBitWords encB (queries a) (bound a))

private theorem computableInPolyTime_natBitWords (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : ℕ × β => natBitWords encB p.2 p.1)
      (encPair encUnary encB) (encList encBits) :=
  ComputableInPolyTime.mapWithInput (by fun_prop) <|
    ComputableInPolyTime.encoding_comp <|
      ((ComputableInPolyTime.snd encUnary encB).comp (ComputableInPolyTime.fst _ _)).prod
        (ComputableInPolyTime.unary_to_binary.comp (ComputableInPolyTime.snd _ _))

private theorem computableInPolyTime_batchNatBitWords (encB : β ↪ List Bool) :
    ComputableInPolyTime (fun p : List β × ℕ => batchNatBitWords encB p.1 p.2)
      (encPair (encList encB) encUnary) (encList encBits) :=
  ComputableInPolyTime.flatMapWith (computableInPolyTime_natBitWords encB)
    (ComputableInPolyTime.snd (encList encB) encUnary)
    (ComputableInPolyTime.fst (encList encB) encUnary)

private theorem computableInPolyTime_decodeNatBatch :
    ComputableInPolyTime (fun p : (ℕ × ℕ) × List Bool => decodeNatBatch p.1.1 p.1.2 p.2)
      (encPair (encPair encUnary encUnary) encBits) (encList encNat) := by
  have hk : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × List Bool) × ℕ => q.1.1.2)
      (encPair (encPair (encPair encUnary encUnary) encBits) encUnary) encUnary :=
    (ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _))
  exact ComputableInPolyTime.mapWithInput (by fun_prop) <|
    ComputableInPolyTime.bitsToNat.comp <|
      ComputableInPolyTime.bitsTakeWithInput
        (ComputableInPolyTime.bitsDropWithInput
          ((ComputableInPolyTime.snd _ _).comp (ComputableInPolyTime.fst _ _))
          (ComputableInPolyTime.unary_mul.comp ((ComputableInPolyTime.snd _ _).prod hk))) hk

private theorem drop_take_flatMap_eq {γ δ : Type*} (l : List γ) (f : γ → List δ) (K : ℕ)
    (hlen : ∀ x ∈ l, (f x).length = K) {j : ℕ} (hj : j < l.length) :
    ((l.flatMap f).drop (j * K)).take K = f l[j] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons a l ih =>
    cases j with
    | zero => simpa using List.take_left' (hlen a (List.mem_cons_self ..))
    | succ j =>
      rw [List.flatMap_cons, show (j + 1) * K = K + j * K by ring, ← List.drop_drop,
        List.drop_left' (hlen a (List.mem_cons_self ..)), List.getElem_cons_succ]
      exact ih (fun x hx => hlen x (List.mem_cons_of_mem _ hx)) (Nat.lt_of_succ_lt_succ hj)

private theorem decodeNatBatch_flatMap {γ : Type*} (l : List γ) (f : γ → List Bool) (K : ℕ)
    (hlen : ∀ x ∈ l, (f x).length = K) :
    decodeNatBatch l.length K (l.flatMap f) = l.map fun x => ofBits (f x) := by
  refine List.ext_getElem (by simp [decodeNatBatch]) fun j _ hj2 => ?_
  simp only [decodeNatBatch, List.getElem_map, List.getElem_range,
    drop_take_flatMap_eq l f K hlen (by simpa using hj2)]

open Classical in
private theorem map_decide_natBitWords {encB : β ↪ List Bool}
    {g : β → ℕ} {A : Set (List Bool)} (hA : AnswersBits encB g A) (b : β) (K : ℕ) :
    (natBitWords encB b K).map (fun w => decide (w ∈ A)) = (List.range K).map (g b).testBit := by
  rw [natBitWords, List.map_map]
  exact List.map_congr_left fun i _ => by
    simp only [Function.comp_apply, hA b i]; cases (g b).testBit i <;> rfl

open Classical in
/-- Interpreting `queryNatBits encB b K` against any oracle satisfying `AnswersBits encB g`
recovers `g b` provided `(g b).size ≤ K`. -/
theorem interpret_queryNatBits {encB : β ↪ List Bool} {g : β → ℕ} {A : Set (List Bool)}
    (hA : AnswersBits encB g A) {b : β} {K : ℕ} (hsize : (g b).size ≤ K) :
    OracleComp.interpret (m := Id) (languageOracle A) (queryNatBits encB b K) = g b := by
  rw [queryNatBits, OracleComp.interpret_map, interpret_queryWords]
  change ofBits ((natBitWords encB b K).map (fun w => decide (w ∈ A))) = g b
  rw [map_decide_natBitWords hA]
  exact Nat.foldr_bit_testBit hsize

/-- Single-query bit-oracle lookup is strict oracle PPT in `(b, K)` (with `K` in unary). -/
theorem isOraclePPTOn_queryNatBits (encB : β ↪ List Bool) :
    IsOraclePPTOn (encPair encB encUnary) encNat
      (fun p => OracleComp.interpret ProbOracleComp.query (queryNatBits encB p.1 p.2)) := by
  simp only [queryNatBits, OracleComp.interpret_map]
  exact (isOraclePPTOn_queryWords.preprocess ((computableInPolyTime_natBitWords encB).comp
    ((ComputableInPolyTime.snd _ _).prod (ComputableInPolyTime.fst _ _)))).map
    ComputableInPolyTime.bitsToNat

open Classical in
/-- Batch constructor for `CountingTuringReducible`: any polynomial-time list of queries `queries`
with a polynomial-time unary bit-length bound `bound` and polynomial-time combination `combine`
witnesses `CountingTuringReducible encA encB f g`. -/
theorem PolyTimeOracleProgram.of_batchNatBits
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → ℕ} {g : β → ℕ}
    (queries : α → List β) (bound : α → ℕ) (combine : α × List ℕ → ℕ)
    (hqueries : ComputableInPolyTime queries encA (encList encB))
    (hbound : ComputableInPolyTime bound encA encUnary)
    (hcombine : ComputableInPolyTime combine (encPair encA (encList encNat)) encNat)
    (hsize : ∀ a, ∀ b ∈ queries a, (g b).size ≤ bound a)
    (hspec : ∀ a, combine (a, (queries a).map g) = f a) :
    CountingTuringReducible encA encB f g := by
  refine ⟨batchNatOracleProgram encB queries bound combine, ?_, fun A hA => funext fun a => ?_⟩
  · simp only [batchNatOracleProgram, OracleComp.interpret_map]
    have hlen := (ComputableInPolyTime.length encB).comp hqueries
    exact (isOraclePPTOn_queryWords.preprocess
      ((computableInPolyTime_batchNatBitWords encB).comp (hqueries.prod hbound))).map_with <|
      hcombine.comp <| (ComputableInPolyTime.fst _ _).prod <|
        computableInPolyTime_decodeNatBatch.comp <|
          (((hlen.comp (ComputableInPolyTime.fst _ _)).prod
            (hbound.comp (ComputableInPolyTime.fst _ _)))).prod (ComputableInPolyTime.snd _ _)
  · simp only [batchNatOracleProgram, OracleComp.interpret_map, interpret_queryWords]
    have hmap : (batchNatBitWords encB (queries a) (bound a)).map (fun w => decide (w ∈ A)) =
        (queries a).flatMap fun b => (List.range (bound a)).map (g b).testBit := by
      rw [batchNatBitWords, List.map_flatMap]
      exact congrArg List.flatten (List.map_congr_left fun b _ => map_decide_natBitWords hA b _)
    change combine (a, decodeNatBatch (queries a).length (bound a) _) = f a
    rw [hmap, decodeNatBatch_flatMap _ _ _ (fun _ _ => by simp),
      List.map_congr_left (g := g) fun b hb =>
        show ofBits ((List.range (bound a)).map (g b).testBit) = g b from
          Nat.foldr_bit_testBit (hsize a b hb),
      hspec a]

end BatchOracle

section OracleElimination

variable {α β : Type}

/-- If `f ≤_T^#P g` and the bit graph of `g` is in `P`, then `f` is computable in polynomial
time (`FP`). -/
theorem CountingTuringReducible.computableInPolyTime_of_bitGraph_mem_P
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} {f : α → ℕ} {g : β → ℕ}
    (hfg : CountingTuringReducible encA encB f g) (hP : bitGraph encB g ∈ P encBits) :
    ComputableInPolyTime f encA encNat := by
  obtain ⟨f', hf', rfl⟩ :=
    hfg.exists_computableInPolyTimeWithOracle (answersBits_bitGraph encB g)
  exact hf'.computableInPolyTime hP

/-- If `f ≤_T^#P g`, `g` is computable in polynomial time, and `encB` has a polynomial-time
total decoder, then `f` is computable in polynomial time (`FP`). -/
theorem CountingTuringReducible.computableInPolyTime_of_decoder
    {encA : α ↪ List Bool} {encB : β ↪ List Bool} (D : Decoder encB)
    {f : α → ℕ} {g : β → ℕ}
    (hfg : CountingTuringReducible encA encB f g)
    (hg : ComputableInPolyTime g encB encNat) :
    ComputableInPolyTime f encA encNat :=
  hfg.computableInPolyTime_of_bitGraph_mem_P (bitGraph_mem_P D hg)

end OracleElimination

end Cslib.Complexity
