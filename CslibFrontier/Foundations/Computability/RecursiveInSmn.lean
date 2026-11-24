/-
Copyright (c) 2018 Mario Carneiro, 2026 The Tau Ceti contributors, 2026 Matthew Doty.
All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, The Tau Ceti contributors, Matthew Doty
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RecursiveIn.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInCode

/-!
# The oracle-uniform s-m-n theorem

A code for a two-argument oracle program reads its arguments `m` and `n` as the paired input
`Nat.pair m n`. Specializing the first argument to a fixed parameter `m` gives the code
`Code.curry c m`, which runs `c` after pairing its own input with `m`. This file proves that
specialization is a primitive recursive operation on codes and that it preserves evaluation
relative to **every** oracle (`Code.eval_curry`). The specializing map does not depend on the
oracle: it is a syntactic operation on codes, and one primitive recursive index map works for all
oracles at once (`Code.exists_primrec₂_smn`). This is the relativized s-m-n theorem, in the
`s¹₁` form where several parameters are passed as one paired number.

On the way, the constructors of `Nat.RecursiveIn.Code` are shown primitive recursive on codes,
as is the embedding `Code.ofPartrec` of ordinary codes. Together with `Code.eval`, which composes
the evaluations of the two parts of `Code.comp cf cg`, `Code.primrec₂_comp` says that composition
of oracle programs is a primitive recursive operation on codes, for every oracle.

## Main definitions

* `Nat.RecursiveIn.Code.curry`: specialize the first argument of a code to a parameter.

## Main results

* `Nat.RecursiveIn.Code.primrec₂_pair`, `Nat.RecursiveIn.Code.primrec₂_comp`,
  `Nat.RecursiveIn.Code.primrec₂_prec`, `Nat.RecursiveIn.Code.primrec_rfind'`: the code
  constructors are primitive recursive.
* `Nat.RecursiveIn.Code.primrec_ofPartrec`: embedding ordinary codes is primitive recursive.
* `Nat.RecursiveIn.Code.eval_curry`, `Nat.RecursiveIn.Code.primrec₂_curry`: specialization
  preserves evaluation relative to every oracle, and is primitive recursive.
* `Nat.RecursiveIn.Code.exists_primrec₂_smn`: **the oracle-uniform s-m-n theorem.** One
  primitive recursive `s : ℕ → ℕ → ℕ` on indices satisfies `Φ^g_{s(e, m)}(n) ≃ Φ^g_e(⟨m, n⟩)`
  for every oracle `g`.

## Implementation notes

The constructor lemmas adapt `Nat.Partrec.Code.primrec₂_pair` and its neighbours in
`Mathlib/Computability/PartrecCode.lean` (Apache 2.0, by Mario Carneiro) to the numbering
`Code.encodeCode`, which differs from Mathlib's by the extra atomic code `oracle`. The embedding
lemma `Code.primrec_ofPartrec` and the definition of `Code.curry` through the embedded constant
code follow `Nat.Partrec.Code.primrec_toSingleOracleCode` and `TauCeti.Oracle.Single.Code.curry` in
Tau Ceti's
[`SingleOracle/Code`](https://github.com/TauCetiProject/TauCeti/blob/e1ec80368dcb61776aabcb2f7edd3858269d2d35/TauCeti/Computability/SingleOracle/Code.lean)
(Apache 2.0, by the Tau Ceti contributors), restated for this library's oracle codes and its
existing embedding `Code.ofPartrec`. `Code.curry` is the oracle analogue of
Mathlib's `Nat.Partrec.Code.curry`.

## References

* [S. C. Kleene, *Introduction to Metamathematics*][Kleene1952]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

open Encodable Denumerable Primrec

namespace Nat.RecursiveIn.Code

/-- The pairing of the Gödel numbers of two codes is primitive recursive. -/
private theorem primrec_natPair_encode :
    Primrec fun p : Code × Code => Nat.pair (encode p.1) (encode p.2) :=
  Primrec₂.natPair.comp (Primrec.encode.comp fst) (Primrec.encode.comp snd)

/-- Forming the pairing code of two codes is primitive recursive. -/
theorem primrec₂_pair : Primrec₂ pair :=
  Primrec₂.encode_iff.1 <|
    (nat_add.comp (nat_double.comp <| nat_double.comp primrec_natPair_encode)
      (const 5)).of_eq fun p => by simp [encodeCode_eq, encodeCode]

/-- Forming the composition code of two codes is primitive recursive. -/
theorem primrec₂_comp : Primrec₂ comp :=
  Primrec₂.encode_iff.1 <|
    (nat_add.comp (nat_double.comp <| nat_double_succ.comp primrec_natPair_encode)
      (const 5)).of_eq fun p => by simp [encodeCode_eq, encodeCode]

/-- Forming the primitive recursion code of two codes is primitive recursive. -/
theorem primrec₂_prec : Primrec₂ prec :=
  Primrec₂.encode_iff.1 <|
    (nat_add.comp (nat_double_succ.comp <| nat_double.comp primrec_natPair_encode)
      (const 5)).of_eq fun p => by simp [encodeCode_eq, encodeCode]

/-- Forming the unbounded search code of a code is primitive recursive. -/
theorem primrec_rfind' : Primrec rfind' :=
  Primrec.encode_iff.1 <|
    (nat_add.comp (nat_double_succ.comp <| nat_double_succ.comp Primrec.encode)
      (const 5)).of_eq fun c => by simp [encodeCode_eq, encodeCode]

/-- Embedding ordinary codes into oracle codes is primitive recursive. -/
theorem primrec_ofPartrec : Primrec ofPartrec := by
  -- The branch functions of `Nat.Partrec.Code.primrec_recOn` receive the tuple
  -- `(a, cf, cg, ofPartrec cf, ofPartrec cg)`; the two embedded subcodes are its last components.
  have h₂ {f : Code → Code → Code} (hf : Primrec₂ f) :
      Primrec fun a : Nat.Partrec.Code × Nat.Partrec.Code × Nat.Partrec.Code × Code × Code =>
        f a.2.2.2.1 a.2.2.2.2 :=
    hf.comp (fst.comp <| snd.comp <| snd.comp snd) (snd.comp <| snd.comp <| snd.comp snd)
  refine (Nat.Partrec.Code.primrec_recOn (c := id) _root_.Primrec.id (const Code.zero)
    (const Code.succ) (const Code.left) (const Code.right)
    (pr := fun _ _ _ => pair) (h₂ primrec₂_pair) (co := fun _ _ _ => comp) (h₂ primrec₂_comp)
    (pc := fun _ _ _ => prec) (h₂ primrec₂_prec) (rf := fun _ _ => rfind')
    (primrec_rfind'.comp <| snd.comp snd)).of_eq fun c => ?_
  induction c <;> simp_all [ofPartrec]

/-- Specialize the first argument of a code to the parameter `m`: on input `n`, the code
`curry c m` runs `c` on `Nat.pair m n`. It composes `c` with the pairing of the embedded constant
code for `m` and the identity code `pair left right`. -/
def curry (c : Code) (m : ℕ) : Code :=
  comp c (pair (ofPartrec (Nat.Partrec.Code.const m)) (pair left right))

/-- Specialization preserves evaluation relative to every oracle `g`, including partial ones. -/
@[simp]
theorem eval_curry (g : ℕ →. ℕ) (c : Code) (m n : ℕ) :
    eval g (curry c m) n = eval g c (Nat.pair m n) := by
  have h : eval g (pair (ofPartrec (Nat.Partrec.Code.const m)) (pair left right)) n =
      Part.some (Nat.pair m n) := by
    simp [eval, Nat.Partrec.Code.eval_const, Seq.seq]
  exact (congrArg (· >>= eval g c) h).trans (Part.bind_some _ _)

/-- Specialization is primitive recursive in the code and the parameter. -/
theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp fst <| primrec₂_pair.comp
    (primrec_ofPartrec.comp <| Nat.Partrec.Code.primrec_const.comp snd)
    (const (pair left right))

/-- **The oracle-uniform s-m-n theorem**, in the `s¹₁` form with paired arguments. A single
primitive recursive map `s` on indices specializes the first argument: for every oracle `g`,
including partial ones, every index `e` and all `m` and `n`, the program with index `s e m`
computes relative to `g` on `n` what the program with index `e` computes relative to `g` on
`Nat.pair m n`. The map `s` is chosen before the oracle, so it is the same for all oracles; it is
`fun e m => encode (curry (ofNat Code e) m)`. Relativized form of Kleene's s-m-n theorem
[Kleene1952]; see also [Soare1987] for relativization. -/
theorem exists_primrec₂_smn :
    ∃ s : ℕ → ℕ → ℕ, Primrec₂ s ∧ ∀ (g : ℕ →. ℕ) (e m n : ℕ),
      eval g (ofNat Code (s e m)) n = eval g (ofNat Code e) (Nat.pair m n) :=
  ⟨fun e m => encode (curry (ofNat Code e) m),
    Primrec.encode.comp <| primrec₂_curry.comp ((Primrec.ofNat Code).comp fst) snd,
    fun g e m n => by simp⟩

end Nat.RecursiveIn.Code
