/-
Copyright (c) 2026 Samuel Schlesinger, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Probabilistic.Oracle
public import CslibFrontier.Crypto.Primitives.UHF.XorHash
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
public import Cslib.Foundations.Data.BitString
public import Mathlib.Algebra.Ring.BooleanRing
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import CslibFrontier.Computability.Probabilistic.Fold
import CslibFrontier.Foundations.Data.BitString.List.Operations
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith

/-!
# Word-oracle evaluation of XOR-hash

The word evaluator for Figure 7.2 ([BonehShoup2023], v0.6, §7.2.3, printed pp. 260–261)
prefixes each block with a fixed-width position field. It xors successive oracle replies
into an accumulator, reading at most the current digest width. This gives a strict
oracle PPT evaluator and agrees with the finite hash when replies have the declared width.
This is an evaluation step toward Theorem 7.6 (#5790).

## Main definitions

* `Cslib.Crypto.UHF.xorHashTaggedWord`: encode a block and its zero-based position.
* `Cslib.Crypto.UHF.xorHashWordQueries`: evaluate the hash through a word oracle.

## Main results

* `Cslib.Crypto.UHF.isOraclePPTOn_xorHashWordQueries`: the uniform evaluation certificate.
* `Cslib.Crypto.UHF.run_xorHashWordQueries`: agreement with the finite XOR hash.
* `Cslib.Crypto.UHF.isQueryBounded_xorHashWordQueries`: the evaluator uses at most one call per
  retained block.
* `Cslib.Crypto.UHF.length_le_of_mem_support_xorHashWordQueries`: the digest width bounds every
  supported result, including for arbitrary oracle replies.
-/

public section

namespace Cslib.Crypto.UHF

open Cslib.Probability Turing.MultiTapeTM

/-- Prefix a block with its zero-based position in unary, padded with zeros to width `ℓ`.
For valid positions `i < ℓ`, the prefix occupies exactly `ℓ` bits. -/
@[expose] def xorHashTaggedWord (ℓ : ℕ) (block : List Bool) (i : ℕ) : List Bool :=
  (List.replicate i true ++ List.replicate (ℓ - i) false) ++ block

/-- Evaluate XOR-hash on at most the first `ℓ` blocks. The accumulator is initially
`width` zero bits. A short reply reduces the accumulator's width, so malformed replies
also have bounded processing cost. -/
@[expose] def xorHashWordQueries (ℓ width : ℕ) (blocks : List (List Bool)) :
    WordOracleComp Unit (List Bool) :=
  let requests := (blocks.take ℓ).zipIdx.map fun (block, i) => xorHashTaggedWord ℓ block i
  requests.foldlM (fun acc request =>
    (fun reply => List.zipWith Bool.xor acc (reply.take acc.length)) <$>
      ProbOracleComp.query ((), request)) (List.replicate width false)

/-- The word evaluator makes at most `ℓ` calls for any input and any oracle replies. -/
theorem isQueryBounded_xorHashWordQueries (ℓ width : ℕ) (blocks : List (List Bool)) :
    (xorHashWordQueries ℓ width blocks).IsQueryBounded ℓ := by
  refine (OracleComp.IsCostBounded.foldlM
    (fun acc req => (OracleComp.isCostBounded_map_iff _ _ _).mpr
      (ProbOracleComp.IsQueryBounded.query ((), req))) _ _).mono ?_
  simpa only [List.length_map, List.length_zipIdx, Nat.mul_one] using List.length_take_le ℓ blocks

/-- The accumulator can only shrink, so even a malformed oracle cannot expand the digest. -/
theorem length_le_of_mem_support_xorHashWordQueries {ℓ width : ℕ}
    {blocks : List (List Bool)} {out : List Bool}
    (hout : out ∈ OracleComp.support (xorHashWordQueries ℓ width blocks)) :
    out.length ≤ width := by
  let step (acc request : List Bool) : WordOracleComp Unit (List Bool) :=
    (fun reply => List.zipWith Bool.xor acc (reply.take acc.length)) <$>
      ProbOracleComp.query ((), request)
  have hfold (requests : List (List Bool)) (acc : List Bool)
      (h : out ∈ OracleComp.support (requests.foldlM step acc)) :
      out.length ≤ acc.length := by
    induction requests generalizing acc with
    | nil =>
      obtain rfl : out = acc := by simpa [OracleComp.supportWith_pure] using h
      exact le_rfl
    | cons req rest ih =>
      rw [List.foldlM_cons] at h
      obtain ⟨_, hnext, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp h
      obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
      exact (ih _ hrest).trans (by simp [List.length_zipWith])
  simpa only [List.length_replicate] using hfold _ _ hout

/-- The evaluator is strict oracle PPT with unary block cap and digest width, followed
by the framed list of blocks. The certificate covers arbitrary oracle reply lengths. -/
theorem isOraclePPTOn_xorHashWordQueries :
    IsOraclePPTOn (encPair (encPair encUnary encUnary) (encList encBits)) encBits
      (fun p : (ℕ × ℕ) × List (List Bool) => xorHashWordQueries p.1.1 p.1.2 p.2) := by
  let input := encPair (encPair encUnary encUnary) (encList encBits)
  have hrequests : ComputableInPolyTime
      (fun p : (ℕ × ℕ) × List (List Bool) =>
        (p.2.take p.1.1).zipIdx.map fun (block, i) => xorHashTaggedWord p.1.1 block i)
      input (encList encBits) := by
    refine ComputableInPolyTime.mapWithInput
      ((ComputableInPolyTime.zipIdx encBits).comp (by fun_prop)) ?_
    unfold xorHashTaggedWord
    exact ComputableInPolyTime.bitsAppend (ComputableInPolyTime.bitsAppend
      ((ComputableInPolyTime.bitsReplicate true).comp (by fun_prop))
      ((ComputableInPolyTime.bitsReplicate false).comp (by fun_prop))) (by fun_prop)
  have hstep : IsOraclePPTOn (encPair encBits encBits) encBits
      (fun p : List Bool × List Bool =>
        (fun reply => List.zipWith Bool.xor p.1 (reply.take p.1.length)) <$>
          ProbOracleComp.query ((), p.2)) := by
    simpa only [Functor.map_map, Function.comp_def] using
      (IsOraclePPTOn.query_take () (request := Prod.snd)
        (limit := fun p : List Bool × List Bool => p.1.length)
        (input := encPair encBits encBits) (by fun_prop) (by fun_prop)).map_with
        (f := fun (p : List Bool × List Bool) reply => List.zipWith Bool.xor p.1 reply)
        (ComputableInPolyTime.bitsZipWithInput Bool.xor (by fun_prop) (by fun_prop))
  refine IsOraclePPTOn.foldlM_of_bounded_growth [] hrequests
    ((ComputableInPolyTime.bitsReplicate false).comp (by fun_prop)) hstep (growth := 0)
    fun acc _ _ hnext => ?_
  obtain ⟨reply, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hnext
  simpa only [encBits_apply, List.length_zipWith, Nat.add_zero] using
    Nat.min_le_left acc.length (reply.take acc.length).length

/-- Every valid tag occupies exactly `ℓ` bits, so fixed-width blocks give fixed-width requests. -/
theorem length_xorHashTaggedWord {ℓ i : ℕ} (hi : i ≤ ℓ) (block : List Bool) :
    (xorHashTaggedWord ℓ block i).length = ℓ + block.length := by
  simp only [xorHashTaggedWord, List.length_append, List.length_replicate]
  omega

/-- A tagged request determines both the block and its valid position. -/
theorem xorHashTaggedWord_injective (ℓ : ℕ) :
    Function.Injective (fun p : List Bool × Fin ℓ => xorHashTaggedWord ℓ p.1 p.2.val) := by
  rintro ⟨block, i⟩ ⟨block', j⟩ h
  have hpre (k : Fin ℓ) :
      (List.replicate k.val true ++ List.replicate (ℓ - k.val) false).length = ℓ := by
    simp only [List.length_append, List.length_replicate]; omega
  have hblock := congrArg (List.drop ℓ) h
  simp only [xorHashTaggedWord, List.drop_left' (hpre _)] at hblock
  have htag := congrArg (fun word => (word.take ℓ).count true) h
  simp only [xorHashTaggedWord, List.take_left' (hpre _), List.count_append] at htag
  exact Prod.ext hblock (Fin.ext (by simpa [List.count_replicate] using htag))

private theorem run_wordFold {α : Type} {width : ℕ} (request : α → List Bool)
    (f : α → BitString width) (table : List Bool → List Bool) (xs : List α)
    (h : ∀ x ∈ xs, table (request x) = List.ofFn (f x)) (acc : BitString width) :
    ((xs.map request).foldlM (fun acc q =>
      (fun reply => List.zipWith Bool.xor acc (reply.take acc.length)) <$>
        (ProbOracleComp.query ((), q) : WordOracleComp Unit (List Bool))) (List.ofFn acc)).run
          (fun q => pure (table q.2)) =
        pure (List.ofFn (acc + (xs.map f).sum)) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    have htake := List.take_of_length_le (List.length_ofFn (f := f x)).le
    simp only [List.map_cons, List.foldlM_cons, ProbOracleComp.run_bind,
      ProbOracleComp.run_map, ProbOracleComp.run_query, h x (List.mem_cons_self ..), map_pure,
      pure_bind, List.length_ofFn, htake, ← BitString.ofFn_add acc (f x), List.sum_cons]
    rw [ih (fun y hy => h y (List.mem_cons_of_mem _ hy)), add_assoc]

/-- With matching fixed-width replies on valid tagged requests, the word evaluator returns the
same digest as the finite XOR hash on bounded block lists. -/
theorem run_xorHashWordQueries {X : Type} {ℓ width : ℕ} (m : {xs : List X // xs.length ≤ ℓ})
    (encode : X → List Bool) (f : X × Fin ℓ → BitString width) (table : List Bool → List Bool)
    (h : ∀ (block : X) (i : Fin ℓ),
      table (xorHashTaggedWord ℓ (encode block) i.val) = List.ofFn (f (block, i))) :
    (xorHashWordQueries ℓ width (m.val.map encode)).run (fun q => pure (table q.2)) =
      pure (List.ofFn (xorHash (Y := BitString width) f m)) := by
  have hrequests :
      (m.val.map encode).zipIdx.map (fun (block, i) => xorHashTaggedWord ℓ block i) =
        (List.ofFn (xorHashQueryAt m)).map
          (fun (block, i) => xorHashTaggedWord ℓ (encode block) i.val) := by
    refine List.ext_getElem (by simp) fun i _ _ => ?_
    simp only [List.getElem_map, List.getElem_zipIdx, List.getElem_ofFn, xorHashQueryAt,
      Function.Embedding.coeFn_mk, Fin.val_castLE, Nat.zero_add, Fin.getElem_fin]
  have hlen : (m.val.map encode).length ≤ ℓ := by simpa only [List.length_map] using m.property
  have hzero : List.ofFn (0 : BitString width) = List.replicate width false :=
    List.ofFn_const width false
  unfold xorHashWordQueries
  dsimp only
  rw [List.take_of_length_le hlen, hrequests, ← hzero]
  simpa only [List.map_ofFn, List.sum_ofFn, zero_add, xorHash, Function.comp_def] using
    run_wordFold (fun (block, i) => xorHashTaggedWord ℓ (encode block) i.val) f table
      (List.ofFn (xorHashQueryAt m)) (fun (block, i) _ => h block i) 0

end Cslib.Crypto.UHF
