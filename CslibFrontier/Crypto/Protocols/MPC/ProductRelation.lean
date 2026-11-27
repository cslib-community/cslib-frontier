/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.Beaver
public import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
public import Mathlib.Algebra.Field.ZMod
import CslibFrontier.Foundations.Data.Code.ReedSolomon
import CslibFrontier.Probability.PMF.UniformBound

/-!
# Verifying Additive-Share Product Relations (Protocol 23.5 and Lemma 23.1)

This module formalizes Protocol 23.5 (proving product relations between two parties `P₁` and `P₂`
holding additive triple shares from a dealer `D`) together with Lemma 23.1 (soundness against a
corrupt dealer), polynomial identity `(23.8)`, and completeness for honest `D, P₁, P₂` from
[BonehShoup2023], Sections 23.2.4.5–23.2.4.6 (printed pp. 1014–1016).

For `m` pairs of additive triple shares `((a_{k1}, b_{k1}, c_{k1}), (a_{k2}, b_{k2}, c_{k2}))`
represented as `Cslib.Crypto.Protocols.MPC.Beaver.TripleShare (ZMod q)`, `ProductRelations t₁ t₂`
expresses `(23.7)`: `(a_{k1} + a_{k2})(b_{k1} + b_{k2}) = c_{k1} + c_{k2}` for `k = 1, ..., m`.
This general `m`-relation problem is posed in Section 23.2.4.5 (p. 1014); the reduction from an
authenticated triple in Section 23.2.4.8 and Theorem 23.9 stay outside this module, and the
simulators and Fact 23.2 privacy analysis of Section 23.2.4.7 are deferred to
`ProductRelation.Privacy`.

## Protocol model and hypotheses

* **Standing prime modulus and `2 * m < q`:** matching Section 23.2.1 (p. 1003), `q` is prime via
  `[Fact (Nat.Prime q)]`. We additionally assume `hm : 2 * m < q`, which the book leaves implicit so
  that the interpolation points `0, ..., 2m` are distinct in `ZMod q` (and ensures `m + 1 < q`, so
  the challenge set `Challenge q m := ℤ_q \ {0, ..., m}` is nonempty). `deal` and `honestC2` use
  `Lagrange.interpolate` over `ZMod q` and are `noncomputable`, carrying no running-time claim.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.ProductRelation.ProductRelations`: relation `(23.7)` on `Fin m`
  pairs of `TripleShare (ZMod q)` values.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyDeal`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.DealerExtra`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.honestC2`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.deal`: Protocol 23.5 Step 1 dealer messages and
  honest dealer distribution.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.Challenge`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.verifyPair`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.honestPartiesRun`: Protocol 23.5 Steps 2–6 challenge
  set, verification predicates, and honest-party execution.

## Main results

* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_honestPartiesRun_accept_le`: Lemma 23.1 bound
  `2m / (q - m - 1)` against arbitrary corrupt dealer messages violating `(23.7)`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.discrepancyPoly_eq_zero_of_productRelations`:
  polynomial identity `(23.8)` for honest dealer outputs.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_honestProtocol_eq_pure`: consequence of
  `(23.8)` that honest `(D, P₁, P₂)` both accept with probability `1`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 23.2.4.5–23.2.4.6, Protocol 23.5, Lemma 23.1,
  printed pp. 1014–1016 (and standing prime modulus convention in Section 23.2.1, p. 1003).
-/

public section

namespace Cslib.Crypto.Protocols.MPC.ProductRelation

open Polynomial Cslib.Probability Cslib.Crypto.Protocols.MPC.Beaver
open scoped ENNReal

/-- The product relations `(23.7)` of [BonehShoup2023] (§23.2.4.5, printed p. 1014) for `m`
pairs of 2-party triple shares `(a_{ki}, b_{ki}, c_{ki})` over `ZMod q`:
`(a_{k1} + a_{k2})(b_{k1} + b_{k2}) = c_{k1} + c_{k2}` for `k = 1, ..., m`. -/
@[expose] def ProductRelations {q m : ℕ} (t₁ t₂ : Fin m → TripleShare (ZMod q)) : Prop :=
  ∀ k : Fin m, ((t₁ k).a + (t₂ k).a) * ((t₁ k).b + (t₂ k).b) = (t₁ k).c + (t₂ k).c

instance {q m : ℕ} (t₁ t₂ : Fin m → TripleShare (ZMod q)) :
    Decidable (ProductRelations t₁ t₂) :=
  Fintype.decidableForallFintype

/-- The full message sent by the dealer `D` to party `P_i` in Protocol 23.5 Step 1(e)
([BonehShoup2023], printed p. 1015): `(a_{ki}, b_{ki})_{k=0}^m` and `(c_{ki})_{k=0}^{2m}`. -/
@[ext] structure PartyDeal (q m : ℕ) where
  /-- The values `(a_{0i}, ..., a_{mi})`: `a_{0i}` is the extra value of Step 1(a) and
  `a_{1i}, ..., a_{mi}` are the shares in `(23.7)`. -/
  a : Fin (m + 1) → ZMod q
  /-- The values `(b_{0i}, ..., b_{mi})`, in the same layout. -/
  b : Fin (m + 1) → ZMod q
  /-- The values `(c_{0i}, ..., c_{2m,i})`: `c_{0i}` of Step 1(a), the shares
  `c_{1i}, ..., c_{mi}` in `(23.7)`, then `c_{m+1,i}, ..., c_{2m,i}` of Step 1(d). -/
  c : Fin (2 * m + 1) → ZMod q
  deriving DecidableEq

/-- The `m` target triple shares `(a_{ki}, b_{ki}, c_{ki})_{k=1}^m` carried by `PartyDeal`. -/
@[expose] def PartyDeal.triples {q m : ℕ} (d : PartyDeal q m) : Fin m → TripleShare (ZMod q) :=
  fun k => ⟨d.a k.succ, d.b k.succ, d.c ⟨k.1 + 1, by omega⟩⟩

/-- Auxiliary random values chosen by an honest dealer for party `P_i` in Protocol 23.5
Steps 1(a) and 1(d): blinding share `(a_{0i}, b_{0i}, c_{0i})` and tail shares
`(c_{m+1,i}, ..., c_{2m,i})`. -/
@[ext] structure DealerExtra (q m : ℕ) where
  /-- Blinding share `a_{0i}` at evaluation node `0`. -/
  a0 : ZMod q
  /-- Blinding share `b_{0i}` at evaluation node `0`. -/
  b0 : ZMod q
  /-- Blinding product share `c_{0i}` at evaluation node `0`. -/
  c0 : ZMod q
  /-- Tail product shares `(c_{m+1,i}, ..., c_{2m,i})` at nodes `m + 1, ..., 2m`. -/
  cTail : Fin m → ZMod q
  deriving DecidableEq

instance {q m : ℕ} [NeZero q] : Fintype (DealerExtra q m) :=
  Fintype.ofEquiv
    (ZMod q × ZMod q × ZMod q × (Fin m → ZMod q))
    { toFun := fun (a0, b0, c0, cTail) => ⟨a0, b0, c0, cTail⟩
      invFun := fun e => (e.a0, e.b0, e.c0, e.cTail)
      left_inv := fun ⟨_, _, _, _⟩ => rfl
      right_inv := fun ⟨_, _, _, _⟩ => rfl }

instance {q m : ℕ} : Nonempty (DealerExtra q m) :=
  ⟨⟨0, 0, 0, 0⟩⟩

/-- Assemble party `P_i`'s full `PartyDeal` from its target triples `t` and dealer randomness
`e`. -/
def DealerExtra.toDeal {q m : ℕ} (t : Fin m → TripleShare (ZMod q)) (e : DealerExtra q m) :
    PartyDeal q m where
  a := Fin.cons e.a0 (fun k => (t k).a)
  b := Fin.cons e.b0 (fun k => (t k).b)
  c k :=
    if hk0 : k.1 = 0 then e.c0
    else if hk1 : k.1 ≤ m then (t ⟨k.1 - 1, by omega⟩).c
    else e.cTail ⟨k.1 - (m + 1), by omega⟩

@[simp] theorem DealerExtra.toDeal_a {q m : ℕ}
    (t : Fin m → TripleShare (ZMod q)) (e : DealerExtra q m) :
    (e.toDeal t).a = Fin.cons e.a0 (fun k => (t k).a) := by
  dsimp only [DealerExtra.toDeal]

@[simp] theorem DealerExtra.toDeal_b {q m : ℕ}
    (t : Fin m → TripleShare (ZMod q)) (e : DealerExtra q m) :
    (e.toDeal t).b = Fin.cons e.b0 (fun k => (t k).b) := by
  dsimp only [DealerExtra.toDeal]

@[simp] theorem DealerExtra.toDeal_c_zero {q m : ℕ}
    (t : Fin m → TripleShare (ZMod q)) (e : DealerExtra q m) :
    (e.toDeal t).c 0 = e.c0 := by
  simp only [DealerExtra.toDeal, Fin.val_zero, ↓reduceDIte]

theorem DealerExtra.toDeal_c_of_le {q m : ℕ}
    (t : Fin m → TripleShare (ZMod q)) (e : DealerExtra q m)
    {k : Fin (2 * m + 1)} (hk0 : k.1 ≠ 0) (hk1 : k.1 ≤ m) :
    (e.toDeal t).c k = (t ⟨k.1 - 1, by omega⟩).c := by
  simp only [DealerExtra.toDeal, hk0, ↓reduceDIte, hk1]

theorem DealerExtra.toDeal_c_of_lt {q m : ℕ}
    (t : Fin m → TripleShare (ZMod q)) (e : DealerExtra q m)
    {k : Fin (2 * m + 1)} (hk1 : m < k.1) :
    (e.toDeal t).c k = e.cTail ⟨k.1 - (m + 1), by omega⟩ := by
  have hk0 : k.1 ≠ 0 := by omega
  have hk1' : ¬ k.1 ≤ m := by omega
  simp only [DealerExtra.toDeal, hk0, ↓reduceDIte, hk1']

@[simp] theorem DealerExtra.toDeal_triples {q m : ℕ}
    (t : Fin m → TripleShare (ZMod q)) (e : DealerExtra q m) :
    (e.toDeal t).triples = t := by
  ext k
  · simp only [PartyDeal.triples, DealerExtra.toDeal_a, Fin.cons_succ]
  · simp only [PartyDeal.triples, DealerExtra.toDeal_b, Fin.cons_succ]
  · simp only [PartyDeal.triples]
    rw [DealerExtra.toDeal_c_of_le t e (by dsimp; omega) (by dsimp; omega)]
    simp only [Nat.add_sub_cancel, Fin.eta]

/-- Evaluation nodes `k ↦ (k : ZMod q)` for `Fin n`. -/
@[expose] def natNodes (q n : ℕ) (k : Fin n) : ZMod q := (k.1 : ZMod q)

theorem injOn_natNodes (q n : ℕ) (hn : n ≤ q) :
    Set.InjOn (natNodes q n) (Finset.univ : Finset (Fin n)) := fun i _ j _ hij =>
  Fin.ext (CharP.natCast_injOn_Iio (ZMod q) q (i.2.trans_le hn) (j.2.trans_le hn) hij)

theorem succ_lt_of_two_mul_lt {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q) : m + 1 < q := by
  cases m <;> [exact (Fact.out : Nat.Prime q).one_lt; omega]

section FieldProps

variable {q m : ℕ} [Fact (Nat.Prime q)]

/-- Lagrange interpolant of `v : Fin (n + 1) → ZMod q` at nodes `0, ..., n` in `ZMod q`. -/
@[expose] noncomputable def interpPoly {n : ℕ} (v : Fin (n + 1) → ZMod q) : (ZMod q)[X] :=
  Lagrange.interpolate Finset.univ (natNodes q (n + 1)) v

theorem interpPoly_natDegree_le {n : ℕ} (v : Fin (n + 1) → ZMod q) (hn : n + 1 ≤ q) :
    (interpPoly v).natDegree ≤ n := by
  have hdeg : (interpPoly v).degree ≤ (n : WithBot ℕ) := by
    have h := Lagrange.degree_interpolate_le v (injOn_natNodes q (n + 1) hn)
    simpa [interpPoly] using h
  exact Polynomial.natDegree_le_of_degree_le hdeg

theorem eval_interpPoly {n : ℕ} (v : Fin (n + 1) → ZMod q) (hn : n + 1 ≤ q)
    (k : Fin (n + 1)) : (interpPoly v).eval (k.1 : ZMod q) = v k :=
  Lagrange.eval_interpolate_at_node v (injOn_natNodes q (n + 1) hn) (Finset.mem_univ k)

/-- Interpolated polynomial `A_i(X)` of degree `≤ m` from `d.a` on `{0, ..., m}`. -/
@[expose] noncomputable def PartyDeal.polyA (d : PartyDeal q m) : (ZMod q)[X] :=
  interpPoly d.a

/-- Interpolated polynomial `B_i(X)` of degree `≤ m` from `d.b` on `{0, ..., m}`. -/
@[expose] noncomputable def PartyDeal.polyB (d : PartyDeal q m) : (ZMod q)[X] :=
  interpPoly d.b

/-- Interpolated polynomial `C_i(X)` of degree `≤ 2m` from `d.c` on `{0, ..., 2m}`. -/
@[expose] noncomputable def PartyDeal.polyC (d : PartyDeal q m) : (ZMod q)[X] :=
  interpPoly d.c

/-- The discrepancy polynomial `(A₁ + A₂)(B₁ + B₂) - (C₁ + C₂)` appearing in `(23.8)` and
Lemma 23.1. -/
@[expose] noncomputable def discrepancyPoly (d₁ d₂ : PartyDeal q m) : (ZMod q)[X] :=
  (d₁.polyA + d₂.polyA) * (d₁.polyB + d₂.polyB) - (d₁.polyC + d₂.polyC)

theorem discrepancyPoly_natDegree_le (d₁ d₂ : PartyDeal q m) (hm : 2 * m < q) :
    (discrepancyPoly d₁ d₂).natDegree ≤ 2 * m := by
  refine le_trans (Polynomial.natDegree_sub_le _ _) (max_le ?_ ?_)
  · calc ((d₁.polyA + d₂.polyA) * (d₁.polyB + d₂.polyB)).natDegree
        ≤ (d₁.polyA + d₂.polyA).natDegree + (d₁.polyB + d₂.polyB).natDegree :=
          Polynomial.natDegree_mul_le
      _ ≤ m + m := add_le_add
          (le_trans (Polynomial.natDegree_add_le _ _)
            (max_le (interpPoly_natDegree_le d₁.a (by omega))
              (interpPoly_natDegree_le d₂.a (by omega))))
          (le_trans (Polynomial.natDegree_add_le _ _)
            (max_le (interpPoly_natDegree_le d₁.b (by omega))
              (interpPoly_natDegree_le d₂.b (by omega))))
      _ = 2 * m := by omega
  · exact le_trans (Polynomial.natDegree_add_le _ _)
      (max_le (interpPoly_natDegree_le d₁.c (by omega))
        (interpPoly_natDegree_le d₂.c (by omega)))

theorem discrepancyPoly_ne_zero_of_not_productRelations {d₁ d₂ : PartyDeal q m} (hm : 2 * m < q)
    (hnot : ¬ ProductRelations d₁.triples d₂.triples) :
    discrepancyPoly d₁ d₂ ≠ 0 := by
  intro hzero
  apply hnot
  intro k
  have hev := congrArg (Polynomial.eval ((k.1 + 1 : ℕ) : ZMod q)) hzero
  simp only [discrepancyPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_zero, sub_eq_zero, Nat.cast_add, Nat.cast_one] at hev
  have hkA1 := eval_interpPoly d₁.a (by omega) k.succ
  have hkA2 := eval_interpPoly d₂.a (by omega) k.succ
  have hkB1 := eval_interpPoly d₁.b (by omega) k.succ
  have hkB2 := eval_interpPoly d₂.b (by omega) k.succ
  have hkC1 := eval_interpPoly d₁.c (by omega) ⟨k.1 + 1, by omega⟩
  have hkC2 := eval_interpPoly d₂.c (by omega) ⟨k.1 + 1, by omega⟩
  simp only [Fin.val_succ, Nat.cast_add, Nat.cast_one] at hkA1 hkA2 hkB1 hkB2
  simp only [Nat.cast_add, Nat.cast_one] at hkC1 hkC2
  dsimp [PartyDeal.triples, PartyDeal.polyA, PartyDeal.polyB, PartyDeal.polyC] at hev ⊢
  rw [← hkA1, ← hkA2, ← hkB1, ← hkB2, ← hkC1, ← hkC2]
  exact hev

end FieldProps

/-- Challenge set `ℤ_q \ {0, ..., m}` in Protocol 23.5 Steps 3–4
([BonehShoup2023], printed p. 1015). -/
abbrev Challenge (q m : ℕ) : Type :=
  { r : ZMod q // ∀ k : Fin (m + 1), r ≠ (k.1 : ZMod q) }

theorem card_challenge (q m : ℕ) [NeZero q] (hm : m + 1 ≤ q) :
    Fintype.card (Challenge q m) = q - m - 1 := by
  let S : Finset (ZMod q) := Finset.univ.image (natNodes q (m + 1))
  have hcardS : S.card = m + 1 := by
    rw [Finset.card_image_of_injOn (injOn_natNodes q (m + 1) hm), Finset.card_fin]
  have hsub : Fintype.card (Challenge q m) = Fintype.card { r : ZMod q // r ∉ S } := by
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun r => ?_)
    simp [S, natNodes, eq_comm]
  rw [hsub, Fintype.card_subtype_compl, Fintype.card_coe, ZMod.card q, hcardS]
  omega

theorem nonempty_challenge (q m : ℕ) [NeZero q] (hm : m + 1 < q) :
    Nonempty (Challenge q m) := by
  rw [← Fintype.card_pos_iff, card_challenge q m (by omega)]
  omega

/-- Honest party verification check on dealer messages `d₁, d₂` and challenge `r : ZMod q`,
returning `(P₁ accepts, P₂ accepts)` as in Protocol 23.5 Steps 4 and 6. -/
@[expose] noncomputable def verifyPair {q m : ℕ} [Fact (Nat.Prime q)]
    (d₁ d₂ : PartyDeal q m) (r : ZMod q) : Bool × Bool :=
  let α₁ := d₁.polyA.eval r
  let β₁ := d₁.polyB.eval r
  let γ₁ := d₁.polyC.eval r
  let α₂ := d₂.polyA.eval r
  let β₂ := d₂.polyB.eval r
  let γ₂ := d₂.polyC.eval r
  let eqCheck := decide ((α₁ + α₂) * (β₁ + β₂) = γ₁ + γ₂)
  let rOk := decide (∀ k : Fin (m + 1), r ≠ (k.1 : ZMod q))
  (eqCheck, rOk && eqCheck)

/-- Honest execution of Protocol 23.5 Steps 3–6 against dealer messages `(d₁, d₂)` when both
`P₁` and `P₂` are honest (`P₁` samples `r` uniformly from `ℤ_q \ {0, ..., m}`). -/
@[expose] noncomputable def honestPartiesRun (q m : ℕ) [Fact (Nat.Prime q)] (hm : 2 * m < q)
    (d₁ d₂ : PartyDeal q m) : ProbComp (Bool × Bool) :=
  haveI : Nonempty (Challenge q m) := nonempty_challenge q m (succ_lt_of_two_mul_lt hm)
  do
    let r ← ProbComp.uniform (Challenge q m)
    return verifyPair d₁ d₂ r.1

/-- **Lemma 23.1** ([BonehShoup2023], §23.2.4.6, printed p. 1016):
if `D` is corrupt (`d₁, d₂` arbitrary) and both `P₁` and `P₂` are honest, and relation `(23.7)`
does not hold on their triple shares, then the probability that either `P₁` or `P₂` finishes without
aborting is at most `2m / (q - m - 1)`. Adds `hm : 2 * m < q` so the interpolation nodes in `ZMod q`
are distinct and the challenge set `Challenge q m` is nonempty. -/
theorem eval_honestPartiesRun_accept_le {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q)
    {d₁ d₂ : PartyDeal q m} (hnot : ¬ ProductRelations d₁.triples d₂.triples) :
    (ProbComp.eval (honestPartiesRun q m hm d₁ d₂)).toOuterMeasure
        { res : Bool × Bool | res.1 = true ∨ res.2 = true } ≤
      (2 * m : ℝ≥0∞) / ((q - m - 1 : ℕ) : ℝ≥0∞) := by
  have hm' : m + 1 < q := succ_lt_of_two_mul_lt hm
  have : Nonempty (Challenge q m) := nonempty_challenge q m hm'
  have hne : discrepancyPoly d₁ d₂ ≠ 0 := discrepancyPoly_ne_zero_of_not_productRelations hm hnot
  have hroots : (Finset.univ.filter (fun r : Challenge q m =>
      (discrepancyPoly d₁ d₂).eval r.1 = 0)).card ≤ 2 * m :=
    le_trans (Cslib.Code.card_filter_eval_eq_zero_le Subtype.coe_injective hne)
      (discrepancyPoly_natDegree_le d₁ d₂ hm)
  have hcard :
      (q - m - 1) * (Finset.univ.filter (fun r : Challenge q m =>
          (verifyPair d₁ d₂ r.1).1 = true ∨ (verifyPair d₁ d₂ r.1).2 = true)).card ≤
        (2 * m) * Fintype.card (Challenge q m) := by
    rw [card_challenge q m (by omega), Nat.mul_comm (2 * m) (q - m - 1)]
    refine Nat.mul_le_mul_left _ (le_trans (Finset.card_le_card fun r hr => ?_) hroots)
    rw [Finset.mem_filter] at hr ⊢
    refine ⟨Finset.mem_univ r, ?_⟩
    have heq : (d₁.polyA.eval r.1 + d₂.polyA.eval r.1) *
        (d₁.polyB.eval r.1 + d₂.polyB.eval r.1) =
        d₁.polyC.eval r.1 + d₂.polyC.eval r.1 := by
      rcases hr.2 with h1 | h2
      · simpa [verifyPair] using h1
      · simp only [verifyPair, Bool.and_eq_true, decide_eq_true_eq] at h2
        exact h2.2
    simp [discrepancyPoly, heq]
  have hbound := Cslib.Probability.PMF.toOuterMeasure_uniformOfFintype_le_div
    (α := Challenge q m) (by omega : 0 < q - m - 1) hcard
  have hmap : ProbComp.eval (honestPartiesRun q m hm d₁ d₂) =
      (PMF.uniformOfFintype (Challenge q m)).map (fun r => verifyPair d₁ d₂ r.1) := by
    simp [honestPartiesRun, bind_pure_comp, ProbComp.eval_map, ProbComp.eval_uniform]
  rw [hmap, PMF.toOuterMeasure_map_apply]
  simpa [Nat.cast_mul] using hbound

/-! ### Honest Dealer, Polynomial Identity (23.8), and Completeness -/

/-- Auxiliary dealer values computed for `P₂` from `(t₁, t₂, e₁, a02, b02)` in Protocol 23.5
Step 1(a)-(d) ([BonehShoup2023], printed p. 1015). -/
noncomputable def honestC2 {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) (e₁ : DealerExtra q m) (a02 b02 : ZMod q) :
    DealerExtra q m :=
  let d₁ := e₁.toDeal t₁
  let A₂ := interpPoly (Fin.cons a02 fun k => (t₂ k).a)
  let B₂ := interpPoly (Fin.cons b02 fun k => (t₂ k).b)
  let C := (d₁.polyA + A₂) * (d₁.polyB + B₂)
  { a0 := a02
    b0 := b02
    c0 := (e₁.a0 + a02) * (e₁.b0 + b02) - e₁.c0
    cTail := fun k => C.eval ((m + 1 + k.1 : ℕ) : ZMod q) - e₁.cTail k }

@[simp] theorem honestC2_a0 {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) (e₁ : DealerExtra q m) (a02 b02 : ZMod q) :
    (honestC2 t₁ t₂ e₁ a02 b02).a0 = a02 := by
  dsimp only [honestC2]

@[simp] theorem honestC2_b0 {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) (e₁ : DealerExtra q m) (a02 b02 : ZMod q) :
    (honestC2 t₁ t₂ e₁ a02 b02).b0 = b02 := by
  dsimp only [honestC2]

@[simp] theorem honestC2_c0 {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) (e₁ : DealerExtra q m) (a02 b02 : ZMod q) :
    (honestC2 t₁ t₂ e₁ a02 b02).c0 = (e₁.a0 + a02) * (e₁.b0 + b02) - e₁.c0 := by
  dsimp only [honestC2]

@[simp] theorem honestC2_cTail {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) (e₁ : DealerExtra q m) (a02 b02 : ZMod q)
    (k : Fin m) :
    (honestC2 t₁ t₂ e₁ a02 b02).cTail k =
      (((e₁.toDeal t₁).polyA + interpPoly (Fin.cons a02 fun j => (t₂ j).a)) *
        ((e₁.toDeal t₁).polyB + interpPoly (Fin.cons b02 fun j => (t₂ j).b))).eval
          ((m + 1 + k.1 : ℕ) : ZMod q) - e₁.cTail k := by
  dsimp only [honestC2]

/-- Protocol 23.5 Step 1 (honest dealer `D`) on target triple shares `(t₁, t₂)`. -/
@[expose] noncomputable def deal {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) : ProbComp (PartyDeal q m × PartyDeal q m) := do
  let e₁ ← ProbComp.uniform (DealerExtra q m)
  let a02 ← ProbComp.uniform (ZMod q)
  let b02 ← ProbComp.uniform (ZMod q)
  return (e₁.toDeal t₁, (honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂)

/-- Polynomial identity **(23.8)** ([BonehShoup2023], printed p. 1015): for an honest dealer's
outputs `(d₁, d₂)` on inputs `(t₁, t₂)` satisfying **(23.7)** with `2 * m < q`,
`(A₁ + A₂)(B₁ + B₂) - (C₁ + C₂) = 0`. -/
theorem discrepancyPoly_eq_zero_of_productRelations {q m : ℕ} [Fact (Nat.Prime q)]
    (hm : 2 * m < q) {t₁ t₂ : Fin m → TripleShare (ZMod q)} (hrel : ProductRelations t₁ t₂)
    (e₁ : DealerExtra q m) (a02 b02 : ZMod q) :
    discrepancyPoly (e₁.toDeal t₁) ((honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂) = 0 := by
  let d₁ := e₁.toDeal t₁
  let d₂ := (honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂
  change discrepancyPoly d₁ d₂ = 0
  have hinj : Function.Injective (natNodes q (2 * m + 1)) := fun i j hij =>
    injOn_natNodes q (2 * m + 1) (by omega) (Finset.mem_univ i) (Finset.mem_univ j) hij
  have heval : ∀ k : Fin (2 * m + 1),
      (discrepancyPoly d₁ d₂).eval (natNodes q (2 * m + 1) k) = 0 := by
    intro k
    simp only [discrepancyPoly, natNodes, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_add, sub_eq_zero]
    rw [show d₁.polyC.eval (k.1 : ZMod q) = d₁.c k from eval_interpPoly d₁.c (by omega) k,
      show d₂.polyC.eval (k.1 : ZMod q) = d₂.c k from eval_interpPoly d₂.c (by omega) k]
    by_cases hk0 : k.1 = 0
    · have hk0_eq : k = 0 := Fin.ext hk0
      rw [hk0_eq]
      have hA1 := eval_interpPoly d₁.a (by omega) 0
      have hA2 := eval_interpPoly d₂.a (by omega) 0
      have hB1 := eval_interpPoly d₁.b (by omega) 0
      have hB2 := eval_interpPoly d₂.b (by omega) 0
      simp only [Fin.val_zero, Nat.cast_zero] at hA1 hA2 hB1 hB2
      dsimp only [PartyDeal.polyA, PartyDeal.polyB]
      simp only [Fin.val_zero, Nat.cast_zero, hA1, hA2, hB1, hB2]
      simp only [d₁, d₂, DealerExtra.toDeal_a, DealerExtra.toDeal_b, Fin.cons_zero,
        DealerExtra.toDeal_c_zero, honestC2_a0, honestC2_b0, honestC2_c0]
      ring
    · by_cases hk1 : k.1 ≤ m
      · let j : Fin m := ⟨k.1 - 1, by omega⟩
        have hj1 : k.1 = j.1 + 1 := by simp [j]; omega
        have hA1 := eval_interpPoly d₁.a (by omega) j.succ
        have hA2 := eval_interpPoly d₂.a (by omega) j.succ
        have hB1 := eval_interpPoly d₁.b (by omega) j.succ
        have hB2 := eval_interpPoly d₂.b (by omega) j.succ
        simp only [Fin.val_succ, ← hj1] at hA1 hA2 hB1 hB2
        dsimp only [PartyDeal.polyA, PartyDeal.polyB]
        rw [hA1, hA2, hB1, hB2]
        simp only [d₁, d₂, DealerExtra.toDeal_a, DealerExtra.toDeal_b, Fin.cons_succ]
        rw [DealerExtra.toDeal_c_of_le t₁ e₁ hk0 hk1,
          DealerExtra.toDeal_c_of_le t₂ (honestC2 t₁ t₂ e₁ a02 b02) hk0 hk1]
        exact hrel j
      · let j : Fin m := ⟨k.1 - (m + 1), by omega⟩
        have hj1 : m + 1 + j.1 = k.1 := by simp [j]; omega
        have hlt : m < k.1 := by omega
        rw [DealerExtra.toDeal_c_of_lt t₁ e₁ hlt,
          DealerExtra.toDeal_c_of_lt t₂ (honestC2 t₁ t₂ e₁ a02 b02) hlt]
        simp only [d₂, honestC2_cTail, j, hj1]
        have hd2A : (interpPoly (Fin.cons a02 fun x => (t₂ x).a)) = d₂.polyA := by
          simp [d₂, PartyDeal.polyA]
        have hd2B : (interpPoly (Fin.cons b02 fun x => (t₂ x).b)) = d₂.polyB := by
          simp [d₂, PartyDeal.polyB]
        rw [hd2A, hd2B]
        simp only [d₁, Polynomial.eval_mul, Polynomial.eval_add]
        ring
  exact Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero _ hinj heval
    (by rw [Fintype.card_fin]; exact Nat.lt_succ_of_le (discrepancyPoly_natDegree_le d₁ d₂ hm))

private theorem verifyPair_of_honest {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q)
    {t₁ t₂ : Fin m → TripleShare (ZMod q)} (hrel : ProductRelations t₁ t₂)
    (e₁ : DealerExtra q m) (a02 b02 : ZMod q) (r : Challenge q m) :
    verifyPair (e₁.toDeal t₁) ((honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂) r.1 = (true, true) := by
  have hpoly := congrArg (Polynomial.eval r.1)
    (discrepancyPoly_eq_zero_of_productRelations hm hrel e₁ a02 b02)
  simp only [discrepancyPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
    Polynomial.eval_zero, sub_eq_zero] at hpoly
  simp [verifyPair, hpoly, r.2]

/-- The consequence of **(23.8)** ([BonehShoup2023], printed p. 1015) that when `D, P₁, P₂` are
honest and `(t₁, t₂)` satisfies `(23.7)` with `2 * m < q`, both `P₁` and `P₂` accept with
probability `1`. -/
theorem eval_honestProtocol_eq_pure {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q)
    {t₁ t₂ : Fin m → TripleShare (ZMod q)} (hrel : ProductRelations t₁ t₂) :
    ProbComp.eval (do
        let dd ← deal t₁ t₂
        honestPartiesRun q m hm dd.1 dd.2) =
      PMF.pure (true, true) := by
  have hm' : m + 1 < q := succ_lt_of_two_mul_lt hm
  have : Nonempty (Challenge q m) := nonempty_challenge q m hm'
  have hsub : ProbComp.eval (do
        let dd ← deal t₁ t₂
        honestPartiesRun q m hm dd.1 dd.2) =
      (ProbComp.eval (deal t₁ t₂)).bind fun _ => PMF.pure (true, true) := by
    rw [ProbComp.eval_bind]
    refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun dd hdd => ?_
    simp only [deal, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hdd
    rcases hdd with ⟨e₁, _, a02, _, b02, _, hdd'⟩
    rcases hdd'.symm with rfl
    ext y
    rw [honestPartiesRun, ProbComp.eval_bind]
    refine Cslib.Probability.PMF.bind_apply_of_forall _ fun r => ?_
    rw [ProbComp.eval_pure, verifyPair_of_honest hm hrel e₁ a02 b02 r]
  rw [hsub, PMF.bind_const]

end Cslib.Crypto.Protocols.MPC.ProductRelation
