/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
public import CslibFrontier.Languages.Probabilistic.QueryCount
public import Mathlib.Data.ZMod.Basic
import CslibFrontier.Foundations.Data.BitString.List.Binary
import CslibFrontier.Languages.Probabilistic.Traverse.SupportWith
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Deterministic oracle reductions among Diffie–Hellman problems in a fixed group

[BonehShoup2023], Exercise 10.17 (p. 429), asks for deterministic polynomial-time equivalences
among four computational Diffie–Hellman problems in a cyclic group of prime order. This module
formalizes explicit deterministic `OracleComp` programs in a fixed `ZMod q`-module `G`, proofs of
correctness under `OracleComp.evalPure` against every solver that is correct on its domain, and
solver call counts under `OracleComp.IsQueryBounded` (and `OracleComp.QueriesSatisfy` where a
solver's domain excludes `0`); group operations, scalar multiplications, and running time are
not counted. The correctness theorems are therefore steps toward Exercise 10.17, not the cited
result: the exercise's reductions are deterministic algorithms whose running time, apart from the
solver calls, is polynomial in the input length, and no such bound is proved here (#5293).

For a modulus `q : ℕ` and element `g : G`, written additively (`α • g` for `g ^ α`):

* `SolvesCDH`: **(a) CDH**, computing `(α * β) • g` from `(α • g, β • g)`.
* `SolvesSqDH`: **(b) Square-DH**, computing `(α ^ 2) • g` from `α • g`.
* `SolvesInvDH`: **(c) Inverse-DH**, computing `α⁻¹ • g` from `α • g` when `α ≠ 0`.
* `SolvesDivDH`: **(d) Divisible-DH**, computing `(α * β⁻¹) • g` from `(α • g, β • g)` when
  `β ≠ 0`.

## Main definitions

* `Cslib.Crypto.SolvesCDH`, `Cslib.Crypto.SolvesSqDH`, `Cslib.Crypto.SolvesInvDH`,
  `Cslib.Crypto.SolvesDivDH`: domain-correctness predicates for solvers of problems (a)–(d).
* `Cslib.Crypto.cdhFromSqProg`: reduces CDH to Square-DH in at most `2` queries.
* `Cslib.Crypto.sqFromCDHProg`: reduces Square-DH to CDH in `1` query.
* `Cslib.Crypto.sqFromInvProg`: reduces Square-DH to Inverse-DH in at most `3` queries.
* `Cslib.Crypto.invFromDivProg`: reduces Inverse-DH to Divisible-DH in at most `1` query.
* `Cslib.Crypto.invFromCDHStep`, `Cslib.Crypto.invFromCDHProg`: reduces Inverse-DH to CDH by
  square-and-multiply for `α ^ (q - 2)` in at most `2 * (q - 2).bits.length` queries.
* `Cslib.Crypto.divFromCDHProg`: reduces Divisible-DH to CDH in at most
  `2 * (q - 2).bits.length + 1` queries.

## Main results

* `Cslib.Crypto.solvesCDH_evalPure_cdhFromSqProg`, `Cslib.Crypto.isQueryBounded_cdhFromSqProg`:
  correctness (for prime `q`) and query bound for `(a) ≤ (b)`.
* `Cslib.Crypto.solvesSqDH_evalPure_sqFromCDHProg`, `Cslib.Crypto.isQueryBounded_sqFromCDHProg`:
  correctness and query bound for `(b) ≤ (a)`.
* `Cslib.Crypto.solvesSqDH_evalPure_sqFromInvProg`, `Cslib.Crypto.isQueryBounded_sqFromInvProg`,
  `Cslib.Crypto.queriesSatisfy_sqFromInvProg`: correctness (for prime `q`), query bound, and
  nonzero-query invariant for `(b) ≤ (c)`.
* `Cslib.Crypto.solvesInvDH_evalPure_invFromDivProg`, `Cslib.Crypto.isQueryBounded_invFromDivProg`,
  `Cslib.Crypto.queriesSatisfy_invFromDivProg`: correctness (for prime `q`), query bound, and
  nonzero-second-coordinate invariant for `(c) ≤ (d)`.
* `Cslib.Crypto.solvesInvDH_evalPure_invFromCDHProg`, `Cslib.Crypto.isQueryBounded_invFromCDHProg`:
  correctness (for prime `q`) and query bound for `(c) ≤ (a)`.
* `Cslib.Crypto.solvesDivDH_evalPure_divFromCDHProg`, `Cslib.Crypto.isQueryBounded_divFromCDHProg`:
  correctness (for prime `q`) and query bound for `(d) ≤ (a)`.

## References

* [BonehShoup2023], Chapter 10, Exercise 10.17, p. 429.
-/

public section

namespace Cslib.Crypto

section Algebra

private theorem two_ne_zero_of_ne_zero_one {q : ℕ} [Fact q.Prime] {α : ZMod q}
    (h0 : α ≠ 0) (h1 : α ≠ 1) : (2 : ZMod q) ≠ 0 := by
  by_cases hq2 : q = 2
  · subst hq2
    have hu : IsUnit α := isUnit_iff_ne_zero.mpr h0
    exact absurd ((IsUnit.unit_spec hu).symm.trans
      (congrArg Units.val (Subsingleton.elim hu.unit 1))) h1
  · exact Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])

private theorem inv_sub_one_sub_inv_add_one {K : Type*} [Field K]
    {α : K} (hsub : α - 1 ≠ 0) (hadd : α + 1 ≠ 0) :
    (α - 1)⁻¹ - (α + 1)⁻¹ = 2 * ((α - 1) * (α + 1))⁻¹ := by
  field_simp; ring

private theorem two_mul_inv_sub_inv_add_one {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {α : K} (hsub : α - 1 ≠ 0) (hadd : α + 1 ≠ 0) :
    2 * ((α - 1)⁻¹ - (α + 1)⁻¹)⁻¹ + 1 = α ^ 2 := by
  rw [inv_sub_one_sub_inv_add_one hsub hadd, mul_inv, inv_inv, ← mul_assoc, mul_inv_cancel₀ h2]
  ring

private theorem inv_sub_inv_ne_zero {K : Type*} [Field K] (h2 : (2 : K) ≠ 0)
    {α : K} (hsub : α - 1 ≠ 0) (hadd : α + 1 ≠ 0) :
    (α - 1)⁻¹ - (α + 1)⁻¹ ≠ 0 := by
  rw [inv_sub_one_sub_inv_add_one hsub hadd]
  exact mul_ne_zero h2 (inv_ne_zero (mul_ne_zero hsub hadd))

end Algebra

section FixedGroupOracle

variable {G : Type} [AddCommGroup G] (q : ℕ) [Module (ZMod q) G] (g : G)

/-- A deterministic solver solves **(a) CDH** with respect to `g` when on
`(α • g, β • g)` it returns `(α * β) • g`. -/
@[expose] def SolvesCDH (cdh : G × G → G) : Prop :=
  ∀ α β : ZMod q, cdh (α • g, β • g) = (α * β) • g

/-- A deterministic solver solves **(b) Square-DH** with respect to `g`
when on `α • g` it returns `(α ^ 2) • g`. -/
@[expose] def SolvesSqDH (sq : G → G) : Prop :=
  ∀ α : ZMod q, sq (α • g) = (α ^ 2) • g

/-- A deterministic solver solves **(c) Inverse-DH** with respect to `g`
when on `α • g` with `α ≠ 0` it returns `α⁻¹ • g`. -/
@[expose] def SolvesInvDH (inv : G → G) : Prop :=
  ∀ α : ZMod q, α ≠ 0 → inv (α • g) = α⁻¹ • g

/-- A deterministic solver solves **(d) Divisible-DH** with respect to `g`
when on `(α • g, β • g)` with `β ≠ 0` it returns `(α * β⁻¹) • g`. -/
@[expose] def SolvesDivDH (div : G × G → G) : Prop :=
  ∀ α β : ZMod q, β ≠ 0 → div (α • g, β • g) = (α * β⁻¹) • g

section CDHFromSq

/-- Deterministic oracle reduction `(a) CDH ≤ (b) Square-DH`: for `q = 2`, returns `0` if
`u = 0` and `v` otherwise (since `α, β ∈ {0, 1}` gives `α * β = β` if `α = 1`, `0` if `α = 0`);
for odd prime `q`, evaluates `(4 : ZMod q)⁻¹ • (sq (u + v) - sq (u - v))` in `2` queries. -/
@[expose] def cdhFromSqProg [DecidableEq G] (u v : G) : OracleComp (fun _ : G => G) G :=
  if q = 2 then pure (if u = 0 then 0 else v)
  else do
    let w₁ ← OracleComp.query (u + v)
    let w₂ ← OracleComp.query (u - v)
    pure ((4 : ZMod q)⁻¹ • (w₁ - w₂))

/-- `cdhFromSqProg` makes at most `2` oracle calls on every execution path. -/
theorem isQueryBounded_cdhFromSqProg [DecidableEq G] (u v : G) :
    OracleComp.IsQueryBounded (cdhFromSqProg q u v) 2 := by
  unfold cdhFromSqProg
  split_ifs <;> try exact .pure _ _
  exact ((OracleComp.IsCostBounded.query (cost := fun _ => 1) (u + v)).bind fun _ =>
    (OracleComp.IsCostBounded.query (cost := fun _ => 1) (u - v)).bind fun _ =>
      .pure _ 0).mono (by decide : 1 + (1 + 0) ≤ 2)

/-- Correctness of `(a) CDH ≤ (b) Square-DH`, a step toward [BonehShoup2023], Exercise 10.17
(p. 429), not the cited result, which also bounds the reduction's running time (only solver calls
are counted, #5293): for prime `q`, any Square-DH solver `sq` turns `cdhFromSqProg` into a CDH
solver. -/
theorem solvesCDH_evalPure_cdhFromSqProg [DecidableEq G] [Fact q.Prime] {sq : G → G}
    (hsq : SolvesSqDH q g sq) :
    SolvesCDH q g fun p => OracleComp.evalPure sq (cdhFromSqProg q p.1 p.2) := by
  intro α β
  dsimp only [cdhFromSqProg]
  by_cases hq : q = 2
  · subst hq
    simp only [↓reduceIte, OracleComp.evalPure_pure]
    rcases eq_or_ne g 0 with rfl | hg
    · simp
    · rcases eq_or_ne α 0 with rfl | hα0
      · simp
      · rcases eq_or_ne α 1 with rfl | hα1
        · simp [hg]
        · exact ((two_ne_zero_of_ne_zero_one hα0 hα1) (by simpa using ZMod.natCast_self 2)).elim
  · simp only [hq, ↓reduceIte, OracleComp.evalPure_bind, OracleComp.evalPure_query,
      OracleComp.evalPure_pure]
    have h2 : (2 : ZMod q) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
    rw [← add_smul, ← sub_smul, hsq (α + β), hsq (α - β), ← sub_smul,
      show (α + β) ^ 2 - (α - β) ^ 2 = (2 * 2) * (α * β) by ring, smul_smul, ← mul_assoc,
      show (4 : ZMod q) = 2 * 2 by ring, inv_mul_cancel₀ (mul_ne_zero h2 h2), one_mul]

end CDHFromSq

section SqFromCDH

/-- Deterministic oracle reduction `(b) Square-DH ≤ (a) CDH`: queries `cdh (u, u)` in `1` call. -/
@[expose] def sqFromCDHProg (u : G) : OracleComp (fun _ : G × G => G) G :=
  OracleComp.query (u, u)

omit [AddCommGroup G] in
/-- `sqFromCDHProg` makes at most `1` oracle call. -/
theorem isQueryBounded_sqFromCDHProg (u : G) :
    OracleComp.IsQueryBounded (sqFromCDHProg u) 1 :=
  OracleComp.IsCostBounded.query (cost := fun _ => 1) (u, u)

/-- Correctness of `(b) Square-DH ≤ (a) CDH`, a step toward [BonehShoup2023], Exercise 10.17
(p. 429), not the cited result, which also bounds the reduction's running time (only solver calls
are counted, #5293): any CDH solver turns `sqFromCDHProg` into a Square-DH solver. -/
theorem solvesSqDH_evalPure_sqFromCDHProg {cdh : G × G → G} (hcdh : SolvesCDH q g cdh) :
    SolvesSqDH q g fun u => OracleComp.evalPure cdh (sqFromCDHProg u) := by
  intro α
  simpa [sqFromCDHProg, pow_two] using hcdh α α

end SqFromCDH

section SqFromInv

/-- Deterministic oracle reduction `(b) Square-DH ≤ (c) Inverse-DH`: checks `u ∈ {0, g, -g}`,
otherwise queries `inv (u - g)`, `inv (u + g)`, and `inv (inv (u - g) - inv (u + g))` to compute
`2 • ((α - 1)⁻¹ - (α + 1)⁻¹)⁻¹ • g + g = α^2 • g`. Guards `r₁ = r₂` so every query is nonzero on
every execution path against arbitrary oracle responses. -/
@[expose] def sqFromInvProg [DecidableEq G] (u : G) : OracleComp (fun _ : G => G) G :=
  if u = 0 then pure 0
  else if u = g ∨ u = -g then pure g
  else do
    let r₁ ← OracleComp.query (u - g)
    let r₂ ← OracleComp.query (u + g)
    if r₁ = r₂ then pure 0
    else do
      let r₃ ← OracleComp.query (r₁ - r₂)
      pure (2 • r₃ + g)

/-- `sqFromInvProg` makes at most `3` oracle calls on every execution path. -/
theorem isQueryBounded_sqFromInvProg [DecidableEq G] (u : G) :
    OracleComp.IsQueryBounded (sqFromInvProg g u) 3 := by
  unfold sqFromInvProg
  split_ifs <;> try exact .pure _ _
  refine ((OracleComp.IsCostBounded.query (cost := fun _ => 1) (u - g)).bind fun r₁ =>
    (OracleComp.IsCostBounded.query (cost := fun _ => 1) (u + g)).bind fun r₂ => ?_).mono
      (by decide : 1 + (1 + 1) ≤ 3)
  split_ifs
  · exact .pure _ _
  · exact (OracleComp.IsCostBounded.query (cost := fun _ => 1) (r₁ - r₂)).bind fun _ => .pure _ 0

/-- Every query emitted by `sqFromInvProg` is nonzero, on every execution path against any
oracle responses. -/
theorem queriesSatisfy_sqFromInvProg [DecidableEq G] (u : G) :
    OracleComp.QueriesSatisfy (fun qx : G => qx ≠ 0) (sqFromInvProg g u) := by
  unfold sqFromInvProg
  split_ifs with hu0 hug <;> try exact .pure _
  refine (OracleComp.QueriesSatisfy.query (p := fun qx : G => qx ≠ 0)
      (sub_ne_zero.mpr fun h => hug (.inl h))).bind fun r₁ =>
    (OracleComp.QueriesSatisfy.query (p := fun qx : G => qx ≠ 0)
      fun h => hug (.inr (eq_neg_of_add_eq_zero_left h))).bind fun r₂ => ?_
  split_ifs with hr
  · exact .pure _
  · exact (OracleComp.QueriesSatisfy.query (p := fun qx : G => qx ≠ 0)
      (sub_ne_zero.mpr hr)).bind fun _ => .pure _

/-- Correctness of `(b) Square-DH ≤ (c) Inverse-DH`, a step toward [BonehShoup2023],
Exercise 10.17 (p. 429), not the cited result, which also bounds the reduction's running time
(only solver calls are counted, #5293): for prime `q`, any Inverse-DH solver turns
`sqFromInvProg` into a Square-DH solver. -/
theorem solvesSqDH_evalPure_sqFromInvProg [DecidableEq G] [Fact q.Prime] {inv : G → G}
    (hinv : SolvesInvDH q g inv) :
    SolvesSqDH q g fun u => OracleComp.evalPure inv (sqFromInvProg g u) := by
  intro α
  dsimp only [sqFromInvProg]
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · rcases eq_or_ne α 0 with rfl | hα0
    · simp
    · rcases eq_or_ne α 1 with rfl | hα1
      · simp [hg]
      · rcases eq_or_ne α (-1) with rfl | hαneg1
        · simp [hg]
        · have hinj : Function.Injective (fun c : ZMod q => c • g) :=
            smul_left_injective (ZMod q) hg
          have hu0 : α • g ≠ 0 := (smul_eq_zero_iff_left hg).not.mpr hα0
          have hnot : ¬ (α • g = g ∨ α • g = -g) := fun h => h.elim
            (fun h => hα1 (hinj (by simpa [one_smul] using h)))
            (fun h => hαneg1 (hinj (by simpa [neg_one_smul] using h)))
          have hsub : α - 1 ≠ 0 := sub_ne_zero.mpr hα1
          have hadd : α + 1 ≠ 0 := fun h => hαneg1 (eq_neg_of_add_eq_zero_left h)
          have h2 : (2 : ZMod q) ≠ 0 := two_ne_zero_of_ne_zero_one hα0 hα1
          have hinv_ne : (α - 1)⁻¹ - (α + 1)⁻¹ ≠ 0 := inv_sub_inv_ne_zero h2 hsub hadd
          have hr_ne : (α - 1)⁻¹ • g ≠ (α + 1)⁻¹ • g := fun h => hinv_ne (sub_eq_zero.mpr (hinj h))
          simp only [hu0, hnot, ↓reduceIte, OracleComp.evalPure_bind, OracleComp.evalPure_query,
            show α • g - g = (α - 1) • g by rw [sub_smul, one_smul],
            show α • g + g = (α + 1) • g by rw [add_smul, one_smul],
            hinv (α - 1) hsub, hinv (α + 1) hadd, hr_ne, OracleComp.evalPure_pure]
          rw [← sub_smul, hinv _ hinv_ne, ← Nat.cast_smul_eq_nsmul (ZMod q), smul_smul,
            Nat.cast_ofNat, ← two_mul_inv_sub_inv_add_one h2 hsub hadd, add_smul, one_smul]

end SqFromInv

section InvFromDiv

/-- Deterministic oracle reduction `(c) Inverse-DH ≤ (d) Divisible-DH`: queries `div (g, u)` when
`u ≠ 0` and returns `0` otherwise. -/
@[expose] def invFromDivProg [DecidableEq G] (u : G) : OracleComp (fun _ : G × G => G) G :=
  if u = 0 then pure 0 else OracleComp.query (g, u)

/-- `invFromDivProg` makes at most `1` oracle call on every execution path. -/
theorem isQueryBounded_invFromDivProg [DecidableEq G] (u : G) :
    OracleComp.IsQueryBounded (invFromDivProg g u) 1 := by
  unfold invFromDivProg
  split_ifs
  · exact .pure _ _
  · exact .query _

/-- Every query emitted by `invFromDivProg` has nonzero second coordinate. -/
theorem queriesSatisfy_invFromDivProg [DecidableEq G] (u : G) :
    OracleComp.QueriesSatisfy (fun qp : G × G => qp.2 ≠ 0) (invFromDivProg g u) := by
  unfold invFromDivProg
  split_ifs with hu
  · exact .pure _
  · exact .query hu

/-- Correctness of `(c) Inverse-DH ≤ (d) Divisible-DH`, a step toward [BonehShoup2023],
Exercise 10.17 (p. 429), not the cited result, which also bounds the reduction's running time
(only solver calls are counted, #5293): for prime `q`, any Divisible-DH solver turns
`invFromDivProg` into an Inverse-DH solver. -/
theorem solvesInvDH_evalPure_invFromDivProg [DecidableEq G] [Fact q.Prime] {div : G × G → G}
    (hdiv : SolvesDivDH q g div) :
    SolvesInvDH q g fun u => OracleComp.evalPure div (invFromDivProg g u) := by
  intro α hα
  rcases eq_or_ne g 0 with rfl | hg
  · simp [invFromDivProg]
  · simpa [invFromDivProg, (smul_eq_zero_iff_left hg).not.mpr hα, one_smul] using hdiv 1 α hα

end InvFromDiv

section InvFromCDH

/-- One step of square-and-multiply in the exponent using a CDH oracle: squares `acc`, and if
`bit = true` multiplies by `u`. -/
@[expose] def invFromCDHStep (u acc : G) (bit : Bool) : OracleComp (fun _ : G × G => G) G := do
  let sq ← OracleComp.query (acc, acc)
  if bit then OracleComp.query (sq, u) else pure sq

/-- Deterministic oracle reduction `(c) Inverse-DH ≤ (a) CDH`: computes `α ^ (q - 2) • g` by
square-and-multiply along `(q - 2).bits.reverse` using at most `2 * (q - 2).bits.length` CDH
queries. -/
@[expose] def invFromCDHProg (u : G) : OracleComp (fun _ : G × G => G) G :=
  (q - 2).bits.reverse.foldlM (invFromCDHStep u) g

omit [AddCommGroup G] in
private theorem isCostBounded_invFromCDHStep (u acc : G) (bit : Bool) :
    OracleComp.IsCostBounded (fun _ => 1) (invFromCDHStep u acc bit) 2 := by
  unfold invFromCDHStep
  refine ((OracleComp.IsCostBounded.query (cost := fun _ => 1) (acc, acc)).bind
    (m := 1) fun sq => ?_).mono (by decide : 1 + 1 ≤ 2)
  cases bit <;> simp [OracleComp.IsCostBounded.pure, OracleComp.IsCostBounded.query]

omit [AddCommGroup G] [Module (ZMod q) G] in
/-- `invFromCDHProg` makes at most `2 * (q - 2).bits.length` oracle calls. -/
theorem isQueryBounded_invFromCDHProg (u : G) :
    OracleComp.IsQueryBounded (invFromCDHProg q g u) (2 * (q - 2).bits.length) := by
  simpa [invFromCDHProg, Nat.mul_comm] using
    OracleComp.IsCostBounded.foldlM (isCostBounded_invFromCDHStep u) g (q - 2).bits.reverse

private theorem evalPure_foldlM_invFromCDHStep {cdh : G × G → G} (hcdh : SolvesCDH q g cdh)
    (α : ZMod q) (word : List Bool) :
    OracleComp.evalPure cdh (word.foldlM (invFromCDHStep (α • g)) g) =
      (α ^ Cslib.BitString.binaryValue word) • g := by
  rw [OracleComp.evalPure_foldlM]
  induction word using List.reverseRecOn with
  | nil => simp [Cslib.BitString.binaryValue]
  | append_singleton ws b ih =>
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    unfold invFromCDHStep
    simp only [OracleComp.evalPure_bind, OracleComp.evalPure_query]
    rw [hcdh (α ^ Cslib.BitString.binaryValue ws) (α ^ Cslib.BitString.binaryValue ws)]
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte, OracleComp.evalPure_pure,
        Cslib.BitString.binaryValue_snoc, Bool.toNat_false, add_zero]
      congr 1; ring
    · simp only [↓reduceIte, OracleComp.evalPure_query,
        Cslib.BitString.binaryValue_snoc, Bool.toNat_true]
      rw [← pow_two, hcdh ((α ^ Cslib.BitString.binaryValue ws) ^ 2) α]
      congr 1; ring

/-- Correctness of `(c) Inverse-DH ≤ (a) CDH`, a step toward [BonehShoup2023], Exercise 10.17
(p. 429), not the cited result, which also bounds the reduction's running time (only solver calls
are counted, #5293): for prime `q`, any CDH solver turns `invFromCDHProg` into an Inverse-DH
solver. -/
theorem solvesInvDH_evalPure_invFromCDHProg [Fact q.Prime] {cdh : G × G → G}
    (hcdh : SolvesCDH q g cdh) :
    SolvesInvDH q g fun u => OracleComp.evalPure cdh (invFromCDHProg q g u) := by
  intro α hα
  dsimp only [invFromCDHProg]
  rw [evalPure_foldlM_invFromCDHStep q g hcdh α (q - 2).bits.reverse,
    Cslib.BitString.binaryValue_reverse_bits]
  have h2le : 2 ≤ q := (Fact.out : q.Prime).two_le
  rw [eq_inv_of_mul_eq_one_left (show α ^ (q - 2) * α = 1 by
    rw [← pow_succ, show q - 2 + 1 = q - 1 by omega, ZMod.pow_card_sub_one_eq_one hα])]

end InvFromCDH

section DivFromCDH

/-- Deterministic oracle reduction `(d) Divisible-DH ≤ (a) CDH`: inverts `v` with
`invFromCDHProg` and calls `cdh (u, v⁻¹)` in at most `2 * (q - 2).bits.length + 1` queries. -/
@[expose] def divFromCDHProg (u v : G) : OracleComp (fun _ : G × G => G) G := do
  let inv_v ← invFromCDHProg q g v
  OracleComp.query (u, inv_v)

omit [AddCommGroup G] [Module (ZMod q) G] in
/-- `divFromCDHProg` makes at most `2 * (q - 2).bits.length + 1` oracle calls. -/
theorem isQueryBounded_divFromCDHProg (u v : G) :
    OracleComp.IsQueryBounded (divFromCDHProg q g u v) (2 * (q - 2).bits.length + 1) := by
  unfold divFromCDHProg
  exact (isQueryBounded_invFromCDHProg q g v).bind fun inv_v =>
    OracleComp.IsCostBounded.query (cost := fun _ => 1) (u, inv_v)

/-- Correctness of `(d) Divisible-DH ≤ (a) CDH`, a step toward [BonehShoup2023], Exercise 10.17
(p. 429), not the cited result, which also bounds the reduction's running time (only solver calls
are counted, #5293): for prime `q`, any CDH solver turns `divFromCDHProg` into a Divisible-DH
solver. -/
theorem solvesDivDH_evalPure_divFromCDHProg [Fact q.Prime] {cdh : G × G → G}
    (hcdh : SolvesCDH q g cdh) :
    SolvesDivDH q g fun p => OracleComp.evalPure cdh (divFromCDHProg q g p.1 p.2) := by
  intro α β hβ
  have hinv := solvesInvDH_evalPure_invFromCDHProg q g hcdh β hβ
  dsimp only at hinv
  simp only [divFromCDHProg, OracleComp.evalPure_bind, OracleComp.evalPure_query, hinv]
  exact hcdh α β⁻¹

end DivFromCDH

end FixedGroupOracle

end Cslib.Crypto
