/-
Copyright (c) 2026 Matthew Doty. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matthew Doty
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Computability/RecursiveIn.lean`)

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Computability.RecursiveInCode
public import CslibFrontier.Foundations.Computability.TuringJoin
import CslibFrontier.Foundations.Computability.RecursiveInEvalnPrimrec
import CslibFrontier.Foundations.Computability.RecursiveInSmn

/-!
# The Turing join on oracle codes

The join `p ⊕ x` (`Partrec.join`) of two oracles is their least upper bound under `≤ᵀ`. This file
proves the code-level, uniform form of that fact for the oracle codes `Nat.RecursiveIn.Code`: the
reductions behind `p ≤ᵀ p ⊕ x`, `x ≤ᵀ p ⊕ x` and `join_le` are primitive recursive maps on codes
that do not depend on the oracles.

* *Substitution.* `Code.subst c d` replaces every oracle query of `c` by a call to the code `d`.
  Relative to `g` it runs `c` relative to the oracle that `d` computes from `g`
  (`Code.eval_subst`), and it is primitive recursive in both codes (`Code.primrec₂_subst`).
* *Joining codes.* `Code.join a b` computes, relative to any `g`, the join of what `a` and `b`
  compute relative to `g` (`Code.eval_join`), and is primitive recursive (`Code.primrec₂_join`).
* *Projections.* The fixed codes `Code.joinLeft` and `Code.joinRight` recover `p` and `x` from the
  oracle `p ⊕ x` (`Code.eval_joinLeft`, `Code.eval_joinRight`).

Together, a program querying `p ⊕ x` corresponds to computations relative to both oracles. A
code `c` relative to `p` becomes the code `c.subst joinLeft` relative to `p ⊕ x`
(`Code.eval_subst_joinLeft`). Conversely, a code `c` relative to `p ⊕ x`, given codes `a` and `b`
computing `p` and `x` from an oracle `h`, becomes the code `c.subst (join a b)` relative to `h`
(`Code.eval_subst_join`). Both translations are primitive recursive in the codes and the same for
all oracles; `Code.exists_primrec_joinLeft`, `Code.exists_primrec_joinRight` and
`Code.exists_primrec₂_join` state them on indices.

## Main definitions

* `Nat.RecursiveIn.Code.subst`: replace the oracle of a code by a code.
* `Nat.RecursiveIn.Code.join`: the code for the join of two codes.
* `Nat.RecursiveIn.Code.joinLeft`, `Nat.RecursiveIn.Code.joinRight`: codes for the two halves of
  a joined oracle.

## Main results

* `Nat.RecursiveIn.Code.eval_subst`, `Nat.RecursiveIn.Code.primrec₂_subst`.
* `Nat.RecursiveIn.Code.eval_join`, `Nat.RecursiveIn.Code.primrec₂_join`.
* `Nat.RecursiveIn.Code.eval_subst_joinLeft`, `Nat.RecursiveIn.Code.eval_subst_joinRight`,
  `Nat.RecursiveIn.Code.eval_subst_join`: the translations between codes relative to `p ⊕ x` and
  codes relative to `p`, `x` or an upper bound `h`.
* `Nat.RecursiveIn.Code.exists_primrec_joinLeft`, `Nat.RecursiveIn.Code.exists_primrec_joinRight`,
  `Nat.RecursiveIn.Code.exists_primrec₂_join`: the same on indices, uniformly in the oracles.

## Implementation notes

`Code.join a b` adds two branches that a primitive recursion code guards by parity: on even
inputs the first branch runs `a` and the second returns `0`, and on odd inputs the other way round.
The fallback `0` always converges, so the sum converges exactly when the selected branch does. The
fixed arithmetic codes are chosen from Mathlib's `Nat.Partrec.Code.exists_code`, so `Code.join`,
`Code.joinLeft` and `Code.joinRight` are noncomputable; they are still constants as far as
primitive recursiveness is concerned.

## References

* [S. C. Kleene and E. L. Post, *The upper semi-lattice of degrees of recursive
  unsolvability*][KleenePost1954]
* [R. I. Soare, *Recursively Enumerable Sets and Degrees*][Soare1987]
-/

public section

open Encodable Denumerable Primrec
open scoped Partrec

namespace Nat.RecursiveIn.Code

/-! ### Substituting a code for the oracle -/

/-- Replace every oracle query of `c` by a call to the code `d`. -/
@[expose] def subst (c d : Code) : Code :=
  match c with
  | zero => zero
  | succ => succ
  | left => left
  | right => right
  | oracle => d
  | pair cf cg => pair (cf.subst d) (cg.subst d)
  | comp cf cg => comp (cf.subst d) (cg.subst d)
  | prec cf cg => prec (cf.subst d) (cg.subst d)
  | rfind' cf => rfind' (cf.subst d)

/-- Relative to `g`, the substituted code runs `c` relative to the oracle that `d` computes from
`g`: the code-level form of `Nat.RecursiveIn.subst`. -/
@[simp]
theorem eval_subst (g : ℕ →. ℕ) (c d : Code) : eval g (c.subst d) = eval (eval g d) c := by
  induction c <;> simp only [subst, eval, *] <;> rfl

/-- Substitution is primitive recursive in both codes. -/
theorem primrec₂_subst : Primrec₂ subst := by
  -- The branch functions of `Code.primrec_recOn` receive `(d, cf, cg, cf.subst d, cg.subst d)`.
  have h₂ {f : Code → Code → Code} (hf : Primrec₂ f) :
      Primrec fun a : Code × Code × Code × Code × Code => f a.2.2.2.1 a.2.2.2.2 :=
    hf.comp (fst.comp <| snd.comp <| snd.comp snd) (snd.comp <| snd.comp <| snd.comp snd)
  have h := primrec_recOn (α := Code × Code) (c := Prod.fst) fst (const zero) (const succ)
    (const left) (const right) snd (pr := fun _ _ _ => pair) (h₂ primrec₂_pair)
    (co := fun _ _ _ => comp) (h₂ primrec₂_comp) (pc := fun _ _ _ => prec) (h₂ primrec₂_prec)
    (rf := fun _ _ => rfind') (primrec_rfind'.comp <| snd.comp snd)
  refine Primrec₂.mk (h.of_eq fun ⟨c, d⟩ => ?_)
  induction c <;> simp_all [subst]

/-! ### Fixed arithmetic codes -/

/-- A code for a primitive recursive function, chosen once from `Nat.Partrec.Code.exists_code`. -/
private noncomputable def primCode {f : ℕ → ℕ} (hf : Nat.Primrec f) : Code :=
  ofPartrec (Classical.choose (Nat.Partrec.Code.exists_code.1 (Nat.Partrec.of_primrec hf)))

private theorem eval_primCode {f : ℕ → ℕ} (hf : Nat.Primrec f) (g : ℕ →. ℕ) (n : ℕ) :
    eval g (primCode hf) n = Part.some (f n) := by
  rw [primCode, eval_ofPartrec,
    Classical.choose_spec (Nat.Partrec.Code.exists_code.1 (Nat.Partrec.of_primrec hf))]
  rfl

private theorem nat_primrec_double : Nat.Primrec fun n => 2 * n :=
  Primrec.nat_iff.1 nat_double

private theorem nat_primrec_double_succ : Nat.Primrec fun n => 2 * n + 1 :=
  Primrec.nat_iff.1 nat_double_succ

private theorem nat_primrec_div2 : Nat.Primrec Nat.div2 :=
  Primrec.nat_iff.1 nat_div2

private theorem nat_primrec_add : Nat.Primrec fun n => n.unpair.1 + n.unpair.2 :=
  Primrec.nat_iff.1 <| nat_add.comp (fst.comp Primrec.unpair) (snd.comp Primrec.unpair)

/-- The parity bit `1` on odd and `0` on even inputs, or the reverse when `b = false`. -/
private theorem nat_primrec_parity (b : Bool) : Nat.Primrec fun n => (n.bodd == b).toNat :=
  Primrec.nat_iff.1 <| (Primrec.encode.comp <| Primrec.beq.comp nat_bodd (const b)).of_eq
    fun n => by cases n.bodd <;> cases b <;> rfl

/-- On input `n`, the code `guard t c` returns `0` if `t` returns `0` and runs `c` on `n` if `t`
returns `1`. -/
private def guard (t c : Code) : Code :=
  comp (prec zero (comp c left)) (pair (pair left right) t)

private theorem primrec_guard {α} [Primcodable α] (t : Code) {c : α → Code} (hc : Primrec c) :
    Primrec fun a => guard t (c a) :=
  primrec₂_comp.comp (primrec₂_prec.comp (const zero) (primrec₂_comp.comp hc (const left)))
    (const _)

/-- A bind into a partial function, eta-expanded. Under the module system `ℕ →. ℕ` does not unfold
to `ℕ → Part ℕ` for `simp`, so binds into partial functions are rewritten by this lemma before
Mathlib's `Part.bind` lemmas apply. -/
theorem bind_pfun (x : Part ℕ) (f : ℕ →. ℕ) : x >>= f = x.bind fun y => f y := rfl

private theorem eval_guard_zero (g : ℕ →. ℕ) {t c : Code} {n : ℕ}
    (ht : eval g t n = Part.some 0) : eval g (guard t c) n = Part.some 0 := by
  simp [guard, eval, ht, Seq.seq, Nat.unpair_pair, bind_pfun, pure, PFun.pure]

private theorem eval_guard_one (g : ℕ →. ℕ) {t c : Code} {n : ℕ}
    (ht : eval g t n = Part.some 1) : eval g (guard t c) n = eval g c n := by
  simp [guard, eval, ht, Seq.seq, Nat.unpair_pair, bind_pfun, pure, PFun.pure]

/-! ### Joining codes -/

/-- The code for the join: relative to any oracle, `join a b` computes the join of what `a` and
`b` compute. -/
noncomputable def join (a b : Code) : Code :=
  comp (primCode nat_primrec_add) <| pair
    (guard (primCode (nat_primrec_parity false))
      (comp (primCode nat_primrec_double) (comp a (primCode nat_primrec_div2))))
    (guard (primCode (nat_primrec_parity true))
      (comp (primCode nat_primrec_double_succ) (comp b (primCode nat_primrec_div2))))

/-- Relative to every oracle `g`, the code `join a b` computes the join of the functions that
`a` and `b` compute relative to `g`. -/
@[simp]
theorem eval_join (g : ℕ →. ℕ) (a b : Code) : eval g (join a b) = (eval g a ⊕ eval g b) := by
  funext n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · rw [Partrec.Join.even]
    simp only [join, eval]
    rw [eval_guard_one g (by simp [eval_primCode]),
      eval_guard_zero g (by simp [eval_primCode, Nat.bodd_mul])]
    simp [eval, eval_primCode, bind_pfun, Seq.seq, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def]
  · rw [Partrec.Join.odd]
    simp only [join, eval]
    rw [eval_guard_zero g (by simp [eval_primCode]),
      eval_guard_one g (by simp [eval_primCode, Nat.bodd_mul])]
    simp [eval, eval_primCode, bind_pfun, Seq.seq, Part.bind_some_eq_map, Part.map_map,
      Function.comp_def]

/-- Joining codes is primitive recursive. -/
theorem primrec₂_join : Primrec₂ join :=
  primrec₂_comp.comp (const _) <| primrec₂_pair.comp
    (primrec_guard _ <| primrec₂_comp.comp (const _) <| primrec₂_comp.comp fst (const _))
    (primrec_guard _ <| primrec₂_comp.comp (const _) <| primrec₂_comp.comp snd (const _))

/-! ### The two halves of a joined oracle -/

/-- The code that reads the oracle `p` from the oracle `p ⊕ x`. -/
noncomputable def joinLeft : Code :=
  comp (primCode nat_primrec_div2) (comp oracle (primCode nat_primrec_double))

/-- The code that reads the oracle `x` from the oracle `p ⊕ x`. -/
noncomputable def joinRight : Code :=
  comp (primCode nat_primrec_div2) (comp oracle (primCode nat_primrec_double_succ))

@[simp]
theorem eval_joinLeft (p x : ℕ →. ℕ) : eval (p ⊕ x) joinLeft = p := by
  funext n
  simp [joinLeft, eval, eval_primCode, bind_pfun, Part.bind_some_eq_map, Part.map_map,
    Function.comp_def, Part.map_id']

@[simp]
theorem eval_joinRight (p x : ℕ →. ℕ) : eval (p ⊕ x) joinRight = x := by
  funext n
  simp [joinRight, eval, eval_primCode, bind_pfun, Part.bind_some_eq_map, Part.map_map,
    Function.comp_def, Part.map_id']

/-! ### Translating programs -/

/-- A code relative to `p` becomes a code relative to `p ⊕ x` computing the same function. -/
theorem eval_subst_joinLeft (p x : ℕ →. ℕ) (c : Code) :
    eval (p ⊕ x) (c.subst joinLeft) = eval p c := by
  simp

/-- A code relative to `x` becomes a code relative to `p ⊕ x` computing the same function. -/
theorem eval_subst_joinRight (p x : ℕ →. ℕ) (c : Code) :
    eval (p ⊕ x) (c.subst joinRight) = eval x c := by
  simp

/-- A code `c` relative to `p ⊕ x` becomes a code relative to `h`, given codes `a` and `b`
computing `p` and `x` from `h`: the code-level form of `join_le`. -/
theorem eval_subst_join (h : ℕ →. ℕ) (c a b : Code) :
    eval h (c.subst (join a b)) = eval (eval h a ⊕ eval h b) c := by
  simp

/-- The lift along `p ≤ᵀ p ⊕ x` is a primitive recursive map `t` on indices, the same for all
oracles `p` and `x`. -/
theorem exists_primrec_joinLeft :
    ∃ t : ℕ → ℕ, Primrec t ∧ ∀ (p x : ℕ →. ℕ) (e : ℕ),
      eval (p ⊕ x) (ofNat Code (t e)) = eval p (ofNat Code e) :=
  ⟨fun e => encode ((ofNat Code e).subst joinLeft),
    Primrec.encode.comp <| primrec₂_subst.comp (Primrec.ofNat Code) (const _), by simp⟩

/-- The lift along `x ≤ᵀ p ⊕ x` is a primitive recursive map `t` on indices, the same for all
oracles `p` and `x`. -/
theorem exists_primrec_joinRight :
    ∃ t : ℕ → ℕ, Primrec t ∧ ∀ (p x : ℕ →. ℕ) (e : ℕ),
      eval (p ⊕ x) (ofNat Code (t e)) = eval x (ofNat Code e) :=
  ⟨fun e => encode ((ofNat Code e).subst joinRight),
    Primrec.encode.comp <| primrec₂_subst.comp (Primrec.ofNat Code) (const _), by simp⟩

/-- The least upper bound property on indices: one primitive recursive `j`, the same for every
oracle `h`, sends indices of `p` and `x` relative to `h` to an index of `p ⊕ x` relative to `h`.
Composed with `primrec₂_subst`, it turns a program relative to `p ⊕ x` into one relative to `h`
(`eval_subst_join`). -/
theorem exists_primrec₂_join :
    ∃ j : ℕ → ℕ → ℕ, Primrec₂ j ∧ ∀ (h : ℕ →. ℕ) (a b : ℕ),
      eval h (ofNat Code (j a b)) = (eval h (ofNat Code a) ⊕ eval h (ofNat Code b)) :=
  ⟨fun a b => encode (join (ofNat Code a) (ofNat Code b)),
    Primrec.encode.comp <| primrec₂_join.comp ((Primrec.ofNat Code).comp fst)
      ((Primrec.ofNat Code).comp snd), by simp⟩

end Nat.RecursiveIn.Code
