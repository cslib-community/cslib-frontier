/-
Copyright (c) 2026 lean-canny contributors, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: lean-canny contributors, Erik Demaine
-/
module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Logics.RealArithmetic.Encoding
public import CslibFrontier.Foundations.Data.MvPolynomial.CoeffNorm1
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Data.ZMod.Basic

/-!
# Modular evaluation and size bounds for real-arithmetic terms

The evaluator follows the arithmetic syntax, reducing every intermediate modulo the supplied
modulus. For a positive modulus it gives the canonical residue of the integer polynomial.
The same computation can consume the constructor tokens directly from right to left, using
a stack of residues and rejecting operators with too few operands.
The term's binary word length bounds the polynomial degree and the exponent of a dyadic
coefficient norm bound, regardless of the ambient dimension.

Adapted from `TermEvaluationContext` and `EncodedTermPolynomial` in lean-canny at
`970f28a5ecefc1327402ade16c068aa4b1b2c183`, using the frontier syntax and constructor stream.

## Main results

* `Term.evalResidue_eq`: canonical modular evaluation with zero-padded coordinates.
* `Term.evalTokenStack_tokens`: evaluation of a term's prefix tokens pushes its residue.
* `Term.evalTokenStack_bounds`: a bound on the length and entries of each successful stack.
* `Term.toPolynomial_bounds`: degree and coefficient norm bounds from the encoded term.
-/

public section

namespace Cslib.Logic.RealArithmetic.Term

open MvPolynomial Turing.MultiTapeTM

/-- Evaluate an arithmetic term modulo `p`, reading absent coordinates as zero. -/
@[expose] def evalResidue {n : ℕ} (p : ℕ) (point : List ℕ) : Term n → ℕ
  | .const z => (z % (p : ℤ)).toNat
  | .var i => point[i.val]?.getD 0 % p
  | .add l r => (l.evalResidue p point + r.evalResidue p point) % p
  | .mul l r => (l.evalResidue p point * r.evalResidue p point) % p

/-- For a positive modulus the result is the canonical residue of the term polynomial
with each coordinate read from the supplied list and missing coordinates set to zero. -/
theorem evalResidue_eq {n p : ℕ} (hp : 0 < p) (point : List ℕ) (t : Term n) :
    t.evalResidue p point = (t.toPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun i => ((point[i.val]?.getD 0 : ℕ) : ZMod p))).val := by
  let : NeZero p := ⟨hp.ne'⟩
  induction t with
  | const z =>
    rw [evalResidue, toPolynomial, eval₂_C, Int.coe_castRingHom, ← ZMod.val_intCast,
      Int.toNat_natCast]
  | var i =>
    rw [evalResidue, toPolynomial, eval₂_X, ZMod.val_natCast]
  | add l r hl hr =>
    simp only [evalResidue, toPolynomial, eval₂_add, hl, hr, ZMod.val_add]
  | mul l r hl hr =>
    simp only [evalResidue, toPolynomial, eval₂_mul, hl, hr, ZMod.val_mul]

/-- Process one constructor token from the right of a prefix stream. A leaf pushes a residue.
A binary operator replaces the top two residues and fails if fewer than two are available. -/
@[expose] def evalTokenStep (p : ℕ) (point : List ℕ) :
    TermToken → List ℕ → Option (List ℕ)
  | .inl z, stack => some ((z % (p : ℤ)).toNat :: stack)
  | .inr (.inl i), stack => some (point[i]?.getD 0 % p :: stack)
  | .inr (.inr (.inl _)), l :: r :: stack => some ((l + r) % p :: stack)
  | .inr (.inr (.inr _)), l :: r :: stack => some ((l * r) % p :: stack)
  | .inr (.inr _), _ => none

/-- Process prefix tokens from right to left, starting with an existing residue stack.
Failure propagates if any operator has too few operands. -/
@[expose] def evalTokenStack (p : ℕ) (point : List ℕ)
    (tokens : List TermToken) (stack : List ℕ) : Option (List ℕ) :=
  tokens.foldr (fun token result => result.bind (evalTokenStep p point token)) (some stack)

/-- Processing a complete term stream pushes its modular value above the initial stack. -/
theorem evalTokenStack_tokens {n : ℕ} (p : ℕ) (point : List ℕ) (t : Term n) (stack : List ℕ) :
    evalTokenStack p point ((encTerm_tokens n t).map TermToken.ofFin) stack =
      some (t.evalResidue p point :: stack) := by
  induction t generalizing stack with
  | const _ | var _ => rfl
  | add l r hl hr | mul l r hl hr =>
    simp only [evalTokenStack] at hl hr
    simp only [encTerm_tokens, List.map_append, List.map_cons, List.map_nil, evalTokenStack,
      List.foldr_cons, List.foldr_append, List.foldr_nil, hr, hl, Option.bind_some]
    rfl

private theorem evalTokenStep_bounds {p : ℕ} (hp : 0 < p) (point : List ℕ)
    (token : TermToken) {stack result : List ℕ}
    (hs : ∀ x ∈ stack, x < p) (h : evalTokenStep p point token stack = some result) :
    result.length ≤ stack.length + 1 ∧ ∀ x ∈ result, x < p := by
  rcases token with z | i | _ | _
  · cases h
    exact ⟨le_rfl, List.forall_mem_cons.mpr
      ⟨(Int.toNat_lt (Int.emod_nonneg z (by omega))).2 (Int.emod_lt_of_pos z (by omega)), hs⟩⟩
  · cases h
    exact ⟨le_rfl, List.forall_mem_cons.mpr ⟨Nat.mod_lt _ hp, hs⟩⟩
  all_goals
    rcases stack with _ | ⟨l, _ | ⟨r, rest⟩⟩ <;> cases h
    exact ⟨by simp only [List.length_cons]; omega,
      List.forall_mem_cons.mpr ⟨Nat.mod_lt _ hp,
        (List.forall_mem_cons.mp (List.forall_mem_cons.mp hs).2).2⟩⟩

/-- Each successful suffix of the prefix stream grows the stack by at most one entry per token.
For positive `p`, every entry stays below `p` if the initial entries do. -/
theorem evalTokenStack_bounds {p : ℕ} (hp : 0 < p) (point : List ℕ)
    (tokens : List TermToken) {stack result : List ℕ}
    (hs : ∀ x ∈ stack, x < p) (h : evalTokenStack p point tokens stack = some result) :
    result.length ≤ stack.length + tokens.length ∧ ∀ x ∈ result, x < p := by
  induction tokens generalizing result with
  | nil =>
    cases h
    exact ⟨le_rfl, hs⟩
  | cons token tokens ih =>
    obtain ⟨mid, hmid, hstep⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hlen, hentries⟩ := ih hmid
    obtain ⟨hlen', hentries'⟩ := evalTokenStep_bounds hp point token hentries hstep
    exact ⟨by simp only [List.length_cons]; omega, hentries'⟩

private theorem length_add_mul {n : ℕ} (l r : Term n) :
    let bound := (encTerm n l).length + (encTerm n r).length + 1
    bound ≤ (encTerm n (.add l r)).length ∧ bound ≤ (encTerm n (.mul l r)).length := by
  simp only [encTerm_length, encTerm_tokens, List.map_cons, List.sum_cons, List.map_append,
    List.sum_append]
  omega

/-- The encoding length bounds both the total degree and the binary coefficient norm exponent
of the term polynomial. Negative constants use their binary magnitudes in this bound. -/
theorem toPolynomial_bounds {n : ℕ} (t : Term n) :
    t.toPolynomial.totalDegree ≤ (encTerm n t).length ∧
      t.toPolynomial.coeffNorm1 ≤ 2 ^ (encTerm n t).length := by
  induction t with
  | const z =>
    have hsize : z.natAbs.size ≤ (encTerm n (.const z)).length := by
      simp only [encTerm_length, encTerm_tokens, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, encTermTokenEncoding, length_encSum, Sum.elim_inl, length_encIntBin]
      omega
    refine ⟨(totalDegree_C z).trans_le (Nat.zero_le _), ?_⟩
    rw [toPolynomial, coeffNorm1_C]
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hsize)
  | var i =>
    have hlen : 1 ≤ (encTerm n (.var i)).length := by
      simp only [encTerm_length, encTerm_tokens, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil]
      omega
    simpa only [toPolynomial, totalDegree_X, coeffNorm1_X] using
      And.intro hlen (Nat.one_le_two_pow (n := (encTerm n (.var i)).length))
  | add l r hl hr =>
    have hlen := (length_add_mul l r).1
    let b := (encTerm n l).length + (encTerm n r).length
    refine ⟨(totalDegree_add _ _).trans (max_le (by omega) (by omega)),
      (coeffNorm1_add_le _ _).trans ?_⟩
    calc _ ≤ 2 ^ b + 2 ^ b := Nat.add_le_add
          (hl.2.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)))
          (hr.2.trans (Nat.pow_le_pow_right (by decide) (Nat.le_add_left _ _)))
      _ ≤ _ := by
        rw [← mul_two, ← pow_succ]
        exact Nat.pow_le_pow_right (by decide) hlen
  | mul l r hl hr =>
    have hlen := (length_add_mul l r).2
    refine ⟨(totalDegree_mul _ _).trans ((Nat.add_le_add hl.1 hr.1).trans (by omega)), ?_⟩
    refine (coeffNorm1_mul_le _ _).trans ((Nat.mul_le_mul hl.2 hr.2).trans ?_)
    rw [← pow_add]
    exact Nat.pow_le_pow_right (by decide) (by omega)

end Cslib.Logic.RealArithmetic.Term
