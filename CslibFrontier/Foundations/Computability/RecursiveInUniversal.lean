/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RecursiveIn.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInEvalnPrimrec
public import CslibFrontier.Foundations.Computability.RecursiveInUniform

/-!
# A universal oracle code for total oracles

There is a single oracle code `u` that, relative to every total oracle `f`, evaluates the code
with index `e` at `n`: `eval f u ⟨e, n⟩ = eval f (ofNat Code e) n`
(`Nat.RecursiveIn.Code.exists_universal`). The code does not depend on the oracle.

The code searches for a stage `s` at which the stage-bounded evaluator `Code.evaln`, run against
the first `s` oracle values, converges. It reads those values from the oracle one at a time, and
the stage-bounded evaluator is primitive recursive (`Code.primrec_evaln`). This is the oracle
analogue of the proof of `Nat.Partrec.Code.eval_part` in Mathlib, whose search runs Mathlib's
`Nat.Partrec.Code.evaln`.

## Main results

* `Nat.RecursiveIn.Code.exists_universal`: a universal code for all total oracles.
* `Nat.RecursiveIn.Code.hasUniformCode_prefixOf`: one code computes the encoded prefixes of every
  total oracle.

## Implementation notes

The search reads the oracle at every argument below the stage, so it needs a total oracle: a
partial oracle undefined at some argument that a computation never queries would make the search
diverge. A universal code for partial oracles needs a sequential simulation instead, and is part
of #6829.

## References

* [S. C. Kleene, *Introduction to Metamathematics*][Kleene1952], §65.
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

open Encodable Denumerable

/-- Appending one entry to an encoded list is computable. -/
private theorem computable_snoc :
    Computable fun p : ℕ => encode (ofNat (List ℕ) p.unpair.1 ++ [p.unpair.2]) :=
  (Primrec.encode.comp (Primrec.list_append.comp
    ((Primrec.ofNat (List ℕ)).comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.list_cons.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const [])))).to_comp

/-- The stage-bounded run on `⟨⟨e, n⟩, s⟩` against an encoded oracle prefix is computable. -/
private theorem computable_evalnAt :
    Computable₂ fun p σ : ℕ => Nat.RecursiveIn.Code.evaln (ofNat (List ℕ) σ) p.unpair.2
      (ofNat Nat.RecursiveIn.Code p.unpair.1.unpair.1) p.unpair.1.unpair.2 :=
  let fst₂ : Primrec fun q : ℕ × ℕ => q.1.unpair.1 :=
    Primrec.fst.comp (Primrec.unpair.comp Primrec.fst)
  (Nat.RecursiveIn.Code.primrec_evaln.comp (Primrec.pair
    ((Primrec.ofNat (List ℕ)).comp Primrec.snd)
    (Primrec.pair (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp Primrec.fst))
      ((Primrec.ofNat Nat.RecursiveIn.Code).comp (Primrec.fst.comp (Primrec.unpair.comp fst₂))))
      (Primrec.snd.comp (Primrec.unpair.comp fst₂))))).to_comp

namespace Nat.RecursiveIn.Code

/-- Total oracles, as partial functions. -/
private abbrev total : (ℕ → ℕ) → ℕ →. ℕ := fun f => (f : ℕ →. ℕ)

/-- A total computable map, used by the same code for every oracle. -/
private theorem hasUniformCode_computable {g : ℕ → ℕ} (hg : Computable g) :
    HasUniformCode total fun _ n => Part.some (g n) :=
  HasUniformCode.of_computable hg

/-- One code computes the encoded prefix `k ↦ encode (prefixOf f k)` of every total oracle `f`. -/
theorem hasUniformCode_prefixOf :
    HasUniformCode (fun f : ℕ → ℕ => (f : ℕ →. ℕ)) fun f k =>
      Part.some (encode (prefixOf f k)) := by
  have hih : Computable fun q : ℕ => q.unpair.2.unpair.2 :=
    Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hy : Computable fun q : ℕ => q.unpair.2.unpair.1 :=
    Computable.fst.comp (Computable.unpair.comp (Computable.snd.comp Computable.unpair))
  have hstep : HasUniformCode total fun f q =>
      Part.some (encode (ofNat (List ℕ) q.unpair.2.unpair.2 ++ [f q.unpair.2.unpair.1])) :=
    ((hasUniformCode_computable computable_snoc).comp ((hasUniformCode_computable hih).pair
      (HasUniformCode.oracle.comp (hasUniformCode_computable hy)))).of_eq fun f q => by
      have h : ∀ a, (Part.some a >>= (f : ℕ →. ℕ)) = Part.some (f a) :=
        fun a => Part.bind_some a _
      simp [Seq.seq, h]
  refine (((hasUniformCode_computable (Computable.const 0)).prec hstep).comp
    (hasUniformCode_computable (g := Nat.pair 0)
      (Primrec₂.natPair.to_comp.comp (Computable.const 0) Computable.id))).of_eq fun f k => ?_
  simp only [Part.bind_eq_bind, Part.bind_some, Nat.unpaired, Nat.unpair_pair]
  induction k with
  | zero => simp [prefixOf]
  | succ k ih =>
    simp only [ih, Part.bind_some, ofNat_encode, prefixOf, List.range_succ,
      List.map_append, List.map_cons, List.map_nil]

/-- **A universal oracle code for total oracles.** One code `u` evaluates, relative to every total
oracle `f`, the code with index `e` at `n` when given `Nat.pair e n`. -/
theorem exists_universal :
    ∃ u : Code, ∀ (f : ℕ → ℕ) (e n : ℕ),
      eval (f : ℕ →. ℕ) u (Nat.pair e n) = eval (f : ℕ →. ℕ) (ofNat Code e) n := by
  -- The stage-bounded run on `⟨⟨e, n⟩, s⟩` against the encoded prefix `σ` of length `s`.
  let run : ℕ → ℕ → Option ℕ := fun p σ =>
    evaln (ofNat (List ℕ) σ) p.unpair.2 (ofNat Code p.unpair.1.unpair.1) p.unpair.1.unpair.2
  have hrun : Computable₂ run := computable_evalnAt
  -- The pair `⟨p, encode (prefixOf f s)⟩` for `p = ⟨x, s⟩`.
  have hwith : HasUniformCode total fun f p =>
      Part.some (Nat.pair p (encode (prefixOf f p.unpair.2))) :=
    ((hasUniformCode_computable Computable.id).pair (hasUniformCode_prefixOf.comp
      (hasUniformCode_computable (Computable.snd.comp Computable.unpair)))).of_eq
      fun f p => by simp [Seq.seq]
  have hunp : ∀ {h : ℕ → ℕ → ℕ}, Computable₂ h →
      Computable fun q : ℕ => h q.unpair.1 q.unpair.2 :=
    fun hh => hh.comp (Computable.fst.comp Computable.unpair)
      (Computable.snd.comp Computable.unpair)
  have htest : HasUniformCode total fun f p =>
      Part.some (bif (run p (encode (prefixOf f p.unpair.2))).isSome then 0 else 1) :=
    ((hasUniformCode_computable (hunp (h := fun p σ => bif (run p σ).isSome then 0 else 1)
      (Computable.cond (_root_.Primrec.option_isSome.to_comp.comp hrun) (Computable.const 0)
        (Computable.const 1)))).comp hwith).of_eq fun f p => by simp
  have hval : HasUniformCode total fun f p =>
      Part.some ((run p (encode (prefixOf f p.unpair.2))).getD 0) :=
    ((hasUniformCode_computable (hunp (h := fun p σ => (run p σ).getD 0)
      (Computable.option_getD hrun (Computable.const 0)))).comp hwith).of_eq fun f p => by simp
  -- Search for the first stage at which the run converges, and return its value.
  have hG : HasUniformCode total fun f x =>
      (Nat.rfind fun s => Part.some (run (Nat.pair x s) (encode (prefixOf f s))).isSome).bind
        fun s => Part.some ((run (Nat.pair x s) (encode (prefixOf f s))).getD 0) :=
    (hval.comp ((hasUniformCode_computable Computable.id).pair htest.rfind)).of_eq fun f x => by
      simp only [Seq.seq, Part.bind_eq_bind, Part.bind_some, Part.map_eq_map, Part.map_some,
        Part.bind_map, Nat.unpair_pair, id_eq]
      congr 2
      funext s
      cases run (Nat.pair x s) (encode (prefixOf f s)) <;> rfl
  obtain ⟨u, hu⟩ := hG
  refine ⟨u, fun f e n => ?_⟩
  rw [hu f, eval_eq_rfindOpt]
  refine Part.ext fun y => ?_
  simp only [run, Nat.unpair_pair, ofNat_encode, Nat.rfindOpt, Part.mem_bind_iff,
    Part.mem_some_iff]
  refine exists_congr fun s => and_congr_right fun hs => ?_
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (by simpa using Nat.rfind_spec hs)
  simp [hv]

end Nat.RecursiveIn.Code
