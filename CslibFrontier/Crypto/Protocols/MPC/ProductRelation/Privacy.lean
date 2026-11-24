/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.ProductRelation
import CslibFrontier.Foundations.Data.Polynomial.LagrangeEval
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.Uniform
import CslibFrontier.Probability.Uniform.AffineLine
import CslibFrontier.Tactic.UniformRelabel

/-!
# Simulation Privacy for Protocol 23.5 (Fact 23.2)

Formalizes the information-theoretic simulation privacy of Protocol 23.5 from Section 23.2.4.7
of [BonehShoup2023] (Fact 23.2, printed pp. 1016–1017), against a corrupt party `P₁` and against a
corrupt party `P₂`, using the dealer and verification definitions of
`CslibFrontier.Crypto.Protocols.MPC.ProductRelation`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.ProductRelation.CorruptP1Adversary`: interactive adversary
  corrupting `P₁` (chooses inputs, chooses challenge `r` from `d₁`, receives `none` on abort or
  `P₂`'s opening `(α₂, β₂, γ₂)`, sends opening `(α₁, β₁, γ₁)`, and outputs a guess given
  `Option Bool`).
* `Cslib.Crypto.Protocols.MPC.ProductRelation.simDeal`: the simulated Step 1 deal of the
  corrupt party, generated from that party's triple shares alone; `S_D^(1)` uses it for `P₁`'s
  deal and `S_D^(2)` for `P₂`'s.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.sim1Eval`: the rest of simulator `S_D^(1)`, playing
  `P₂` in Steps 4–5 of Protocol 23.5 from `(d₁, r)`: the abort check on `r` and `P₂`'s opening.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.experiment0P1`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.experiment1P1`: real and simulated privacy
  experiments for corrupt `P₁`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.CorruptP2Adversary`: interactive adversary
  corrupting `P₂`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.sim2Eval`: the rest of simulator `S_D^(2)`, playing
  `P₁` in Steps 3 and 5 from `d₂`: it chooses `r` and supplies `P₁`'s opening.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.experiment0P2`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.experiment1P2`: real and simulated privacy
  experiments for corrupt `P₂`.

## Main results

* `Cslib.Crypto.Protocols.MPC.ProductRelation.bind_honestOpening_eq_bind_uniform`: conditional
  marginal law of `(A₂(r), B₂(r), C₂(r))` given `d₁` and valid `r ∉ {0, ..., m}` matches
  `S_D^(1)`'s uniform `(α₂, β₂)` and derived `γ₂`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_experiment0P1_eq_experiment1P1`: exact
  equality of Boolean output laws between `experiment0P1` and `experiment1P1` when `2 * m < q`
  and chosen inputs satisfy `ProductRelations`. Equal laws on `Bool` give equal probability of
  outputting `true`/`1`, formalizing Fact 23.2 for corrupt `P₁`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_deal_swap`: symmetry of `deal` between `P₁`
  and `P₂`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_experiment0P2_eq_experiment1P2`: exact
  equality of Boolean output laws between `experiment0P2` and `experiment1P2` under `2 * m < q`
  and `ProductRelations`, formalizing Fact 23.2 for corrupt `P₂`.

In every experiment the corrupt party chooses its Step 5 opening after it has received the
other party's, which only strengthens the adversary relative to the simultaneous exchange of Step 5.

All simulators and experiments are `noncomputable` (evaluating Lagrange interpolants over
`ZMod q`) and establish distributional (information-theoretic) equality only, with no
running-time claim for `S_D^(1)` or `S_D^(2)`; any later running-time certificate for them
belongs to [#5829](https://github.com/cslib-community/cslib-frontier/issues/5829), whose
milestone 1 excludes them. The standing prime modulus condition from
Section 23.2.1 (`[Fact (Nat.Prime q)]`), the book's valid-input condition (`ProductRelations`),
and the added bound `2 * m < q` (ensuring `{0, ..., 2m}` are distinct in `ZMod q` and
`Challenge q m` is nonempty) are explicit parameters.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 23.2.4.7, Fact 23.2 (printed pp. 1016–1017).
-/

public section

namespace Cslib.Crypto.Protocols.MPC.ProductRelation

open Polynomial Finset Cslib Cslib.Probability Cslib.ProbComp
open Cslib.Crypto.Protocols.MPC.Beaver

private noncomputable def basisZeroAt (q m : ℕ) [Fact (Nat.Prime q)] (r : ZMod q) : ZMod q :=
  (Lagrange.basis Finset.univ (natNodes q (m + 1)) 0).eval r

private theorem basisZeroAt_ne_zero {q m : ℕ} [Fact (Nat.Prime q)] (hm : m + 1 ≤ q)
    {r : ZMod q} (hr : ∀ k : Fin (m + 1), r ≠ (k.1 : ZMod q)) : basisZeroAt q m r ≠ 0 :=
  Lagrange.eval_basis_ne_zero (injOn_natNodes q (m + 1) hm) (Finset.mem_univ 0)
    (fun j _ _ => hr j)

private noncomputable def restLinearEval (q m : ℕ) [Fact (Nat.Prime q)]
    (vals : Fin m → ZMod q) (r : ZMod q) : ZMod q :=
  ∑ k : Fin m, vals k * (Lagrange.basis Finset.univ (natNodes q (m + 1)) k.succ).eval r

private theorem eval_interpPoly_decompose {q m : ℕ} [Fact (Nat.Prime q)]
    (v : Fin (m + 1) → ZMod q) (r : ZMod q) :
    (interpPoly v).eval r =
      basisZeroAt q m r * v 0 + restLinearEval q m (fun k => v k.succ) r := by
  rw [interpPoly, Lagrange.interpolate_apply, ← Polynomial.coe_evalRingHom, map_sum,
    Fin.sum_univ_succ]
  simp only [map_mul, Polynomial.coe_evalRingHom, Polynomial.eval_C, basisZeroAt,
    restLinearEval, mul_comm (v 0)]

/-- Binding over `P₂`'s honest opening equals binding over a uniform opening: conditional on
`d₁ = e₁.toDeal t₁`, valid inputs `ProductRelations t₁ t₂`, `2 * m < q`, and any valid challenge
`r ∉ {0, ..., m}`, the joint distribution of `P₂`'s evaluation response
`(A₂(r), B₂(r), C₂(r))` over the dealer's `(a₀₂, b₀₂)` is that of `S_D^(1)`: uniform independent
`(α₂, β₂)` and `γ₂` determined by `(23.9)`. -/
theorem bind_honestOpening_eq_bind_uniform {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q)
    {t₁ t₂ : Fin m → TripleShare (ZMod q)} (hrel : ProductRelations t₁ t₂)
    (e₁ : DealerExtra q m) {r : ZMod q} (hr : ∀ k : Fin (m + 1), r ≠ (k.1 : ZMod q))
    {β : Type} (g : ZMod q × ZMod q × ZMod q → PMF β) :
    (PMF.uniformOfFintype (ZMod q)).bind (fun a02 =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun b02 =>
        let d₂ := (honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂
        g (d₂.polyA.eval r, d₂.polyB.eval r, d₂.polyC.eval r))) =
    (PMF.uniformOfFintype (ZMod q)).bind (fun α₂ =>
      (PMF.uniformOfFintype (ZMod q)).bind (fun β₂ =>
        let d₁ := e₁.toDeal t₁
        let γ₂ := (d₁.polyA.eval r + α₂) * (d₁.polyB.eval r + β₂) - d₁.polyC.eval r
        g (α₂, β₂, γ₂))) := by
  have hc : basisZeroAt q m r ≠ 0 :=
    basisZeroAt_ne_zero (succ_lt_of_two_mul_lt hm).le hr
  set offA : ZMod q := restLinearEval q m (fun k => (t₂ k).a) r
  set offB : ZMod q := restLinearEval q m (fun k => (t₂ k).b) r
  set d₁ : PartyDeal q m := e₁.toDeal t₁
  let h : ZMod q → ZMod q → PMF β := fun α₂ β₂ =>
    g (α₂, β₂, (d₁.polyA.eval r + α₂) * (d₁.polyB.eval r + β₂) - d₁.polyC.eval r)
  have hrew : ∀ a02 b02 : ZMod q,
      let d₂ := (honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂
      g (d₂.polyA.eval r, d₂.polyB.eval r, d₂.polyC.eval r) =
        h (offA + basisZeroAt q m r * a02) (offB + basisZeroAt q m r * b02) := by
    intro a02 b02
    dsimp only []
    set d₂ := (honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂
    have hA : d₂.polyA.eval r = offA + basisZeroAt q m r * a02 := by
      have hdec := eval_interpPoly_decompose d₂.a r
      change d₂.polyA.eval r = _ at hdec
      rw [hdec]
      simp only [d₂, DealerExtra.toDeal_a, honestC2_a0, Fin.cons_zero, Fin.cons_succ, offA,
        add_comm]
    have hB : d₂.polyB.eval r = offB + basisZeroAt q m r * b02 := by
      have hdec := eval_interpPoly_decompose d₂.b r
      change d₂.polyB.eval r = _ at hdec
      rw [hdec]
      simp only [d₂, DealerExtra.toDeal_b, honestC2_b0, Fin.cons_zero, Fin.cons_succ, offB,
        add_comm]
    have hdisc := congrArg (Polynomial.eval r)
      (discrepancyPoly_eq_zero_of_productRelations hm hrel e₁ a02 b02)
    simp only [discrepancyPoly, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_add,
      Polynomial.eval_zero, sub_eq_zero] at hdisc
    have hC : d₂.polyC.eval r =
        (d₁.polyA.eval r + d₂.polyA.eval r) * (d₁.polyB.eval r + d₂.polyB.eval r) -
          d₁.polyC.eval r :=
      eq_sub_of_add_eq' hdisc.symm
    rw [hA, hB] at hC ⊢
    simpa only [h] using congrArg (fun c => g (offA + basisZeroAt q m r * a02,
      offB + basisZeroAt q m r * b02, c)) hC
  have hlhs :
      ((PMF.uniformOfFintype (ZMod q)).bind fun a02 =>
        (PMF.uniformOfFintype (ZMod q)).bind fun b02 =>
          let d₂ := (honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂
          g (d₂.polyA.eval r, d₂.polyB.eval r, d₂.polyC.eval r)) =
      (PMF.uniformOfFintype (ZMod q)).bind fun a02 =>
        (PMF.uniformOfFintype (ZMod q)).bind fun b02 =>
          h (offA + basisZeroAt q m r * a02) (offB + basisZeroAt q m r * b02) := by
    congr 1 with a02 : 1
    congr 1 with b02 : 1
    exact hrew a02 b02
  rw [hlhs]
  have hinner : ∀ a02 : ZMod q,
      ((PMF.uniformOfFintype (ZMod q)).bind fun b02 =>
        h (offA + basisZeroAt q m r * a02) (offB + basisZeroAt q m r * b02)) =
      (PMF.uniformOfFintype (ZMod q)).bind
        (fun β₂ => h (offA + basisZeroAt q m r * a02) β₂) := by
    intro a02
    rw [show (fun b02 : ZMod q =>
          h (offA + basisZeroAt q m r * a02) (offB + basisZeroAt q m r * b02)) =
        (h (offA + basisZeroAt q m r * a02)) ∘ (fun b02 => offB + basisZeroAt q m r • b02) from
      funext fun _ => by simp [smul_eq_mul]]
    rw [← PMF.bind_map, Cslib.Probability.PMF.map_add_smul_uniformOfFintype offB hc]
  simp_rw [hinner]
  rw [show (fun a02 : ZMod q => (PMF.uniformOfFintype (ZMod q)).bind
        (fun β₂ => h (offA + basisZeroAt q m r * a02) β₂)) =
      (fun α₂ => (PMF.uniformOfFintype (ZMod q)).bind (fun β₂ => h α₂ β₂)) ∘
        (fun a02 => offA + basisZeroAt q m r • a02) from
    funext fun _ => by simp [smul_eq_mul]]
  rw [← PMF.bind_map, Cslib.Probability.PMF.map_add_smul_uniformOfFintype offA hc]

/-- Interactive adversary corrupting `P₁` in Protocol 23.5 (Section 23.2.4.7). -/
structure CorruptP1Adversary (q m : ℕ) (σ : Type) where
  /-- Samples `(t₁, t₂, st)`. Privacy requires `(t₁, t₂)` to satisfy `ProductRelations`. -/
  chooseInputs : ProbComp ((Fin m → TripleShare (ZMod q)) × (Fin m → TripleShare (ZMod q)) × σ)
  /-- Chooses challenge `r` after observing `P₁`'s Step 1 deal `d₁`. -/
  chooseChallenge : σ → PartyDeal q m → ProbComp (ZMod q × σ)
  /-- Chooses `P₁`'s evaluation opening after receiving honest `P₂`'s evaluation `(α₂, β₂, γ₂)`. -/
  sendOpening : σ → ZMod q × ZMod q × ZMod q → ProbComp ((ZMod q × ZMod q × ZMod q) × σ)
  /-- Outputs final Boolean bit after observing whether `P₂` aborted (`none`) or `some acc`. -/
  finish : σ → Option Bool → ProbComp Bool

/-- Real privacy experiment against corrupt `P₁` for Protocol 23.5. -/
@[expose]
noncomputable def experiment0P1 (q m : ℕ) [Fact (Nat.Prime q)] {σ : Type}
    (A : CorruptP1Adversary q m σ) : ProbComp Bool := do
  let (t₁, t₂, st) ← A.chooseInputs
  let (d₁, d₂) ← deal t₁ t₂
  let (r, st) ← A.chooseChallenge st d₁
  if ∀ k : Fin (m + 1), r ≠ (k.1 : ZMod q) then
    let α₂ := d₂.polyA.eval r
    let β₂ := d₂.polyB.eval r
    let γ₂ := d₂.polyC.eval r
    let ((α₁, β₁, γ₁), st) ← A.sendOpening st (α₂, β₂, γ₂)
    let acc := decide ((α₁ + α₂) * (β₁ + β₂) = γ₁ + γ₂)
    A.finish st (some acc)
  else
    A.finish st none

/-- The simulated Step 1 deal of the corrupt party, generated from that party's triple shares `t`
alone: `S_D^(1)` uses it for `P₁`'s deal and `S_D^(2)` for `P₂`'s. `noncomputable`, with no
running-time claim. -/
@[expose]
noncomputable def simDeal (q m : ℕ) [NeZero q] (t : Fin m → TripleShare (ZMod q)) :
    ProbComp (PartyDeal q m) := do
  let e ← ProbComp.uniform (DealerExtra q m)
  return e.toDeal t

/-- Simulator `S_D^(1)` playing `P₂` in Steps 4–5 of Protocol 23.5: given `d₁` and the
adversary's challenge `r`, aborts (`none`) when `r ∈ {0, ..., m}` (Step 4) and otherwise samples
uniform `(α₂, β₂)` and solves `(23.9)` for `γ₂` (Step 5). `noncomputable`, with no running-time
claim. -/
@[expose]
noncomputable def sim1Eval (q m : ℕ) [Fact (Nat.Prime q)]
    (d₁ : PartyDeal q m) (r : ZMod q) : ProbComp (Option (ZMod q × ZMod q × ZMod q)) :=
  if ∀ k : Fin (m + 1), r ≠ (k.1 : ZMod q) then do
    let α₂ ← ProbComp.uniform (ZMod q)
    let β₂ ← ProbComp.uniform (ZMod q)
    let γ₂ := (d₁.polyA.eval r + α₂) * (d₁.polyB.eval r + β₂) - d₁.polyC.eval r
    return some (α₂, β₂, γ₂)
  else
    return none

/-- Simulated privacy experiment against corrupt `P₁` using `S_D^(1)` (`t₂` is unused by the
simulator). `noncomputable`, with no running-time claim. -/
@[expose]
noncomputable def experiment1P1 (q m : ℕ) [Fact (Nat.Prime q)] {σ : Type}
    (A : CorruptP1Adversary q m σ) : ProbComp Bool := do
  let (t₁, _, st) ← A.chooseInputs
  let d₁ ← simDeal q m t₁
  let (r, st) ← A.chooseChallenge st d₁
  let open₂Opt ← sim1Eval q m d₁ r
  match open₂Opt with
  | none => A.finish st none
  | some (α₂, β₂, γ₂) =>
    let ((α₁, β₁, γ₁), st) ← A.sendOpening st (α₂, β₂, γ₂)
    let acc := decide ((α₁ + α₂) * (β₁ + β₂) = γ₁ + γ₂)
    A.finish st (some acc)

private theorem bind_uniform_uniform_bind_comm {q : ℕ} [NeZero q] {γ δ : Type}
    (p : PMF γ) (f : ZMod q → ZMod q → γ → PMF δ) :
    ((PMF.uniformOfFintype (ZMod q)).bind fun a =>
      (PMF.uniformOfFintype (ZMod q)).bind fun b =>
        p.bind fun c => f a b c) =
    p.bind fun c =>
      (PMF.uniformOfFintype (ZMod q)).bind fun a =>
        (PMF.uniformOfFintype (ZMod q)).bind fun b => f a b c := by
  calc _ = (PMF.uniformOfFintype (ZMod q)).bind fun a =>
        p.bind fun c => (PMF.uniformOfFintype (ZMod q)).bind fun b => f a b c := by
          congr 1 with a : 1
          exact PMF.bind_comm _ _ _
    _ = _ := PMF.bind_comm _ _ _

/-- **Fact 23.2 (corrupt `P₁`)**: under `2 * m < q` and valid inputs satisfying
`ProductRelations`, `experiment0P1` and `experiment1P1` induce identical output distributions on
`Bool` (and hence equal probabilities of outputting `true`/`1`). -/
theorem eval_experiment0P1_eq_experiment1P1 {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q)
    {σ : Type} (A : CorruptP1Adversary q m σ)
    (hrel : ∀ t₁ t₂ st, (t₁, t₂, st) ∈ (ProbComp.eval A.chooseInputs).support →
      ProductRelations t₁ t₂) :
    ProbComp.eval (experiment0P1 q m A) = ProbComp.eval (experiment1P1 q m A) := by
  simp only [experiment0P1, experiment1P1, deal, simDeal, sim1Eval, pmf_norm, ProbComp.eval_uniform]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨t₁, t₂, st⟩ hx => ?_
  have htx : ProductRelations t₁ t₂ := hrel t₁ t₂ st hx
  congr 1 with e₁ : 1
  rw [bind_uniform_uniform_bind_comm]
  congr 1 with ⟨r, st'⟩ : 1
  by_cases hr : ∀ k : Fin (m + 1), r ≠ (k.1 : ZMod q)
  · simp_rw [eq_true hr, ite_true]
    simp only [pmf_norm, ProbComp.eval_uniform]
    exact bind_honestOpening_eq_bind_uniform hm htx e₁ hr fun (α₂, β₂, γ₂) =>
      (ProbComp.eval (A.sendOpening st' (α₂, β₂, γ₂))).bind fun ((α₁, β₁, γ₁), st'') =>
        ProbComp.eval (A.finish st'' (some (decide ((α₁ + α₂) * (β₁ + β₂) = γ₁ + γ₂))))
  · simp_rw [eq_false hr, ite_false]
    simp only [pmf_norm, PMF.bind_const]

/-- Symmetry of `(23.7)` between `P₁`'s and `P₂`'s triple shares. -/
theorem productRelations_comm {q m : ℕ} {t₁ t₂ : Fin m → TripleShare (ZMod q)} :
    ProductRelations t₁ t₂ ↔ ProductRelations t₂ t₁ := by
  dsimp only [ProductRelations]
  constructor <;> intro h k
  · rw [add_comm (t₂ k).a, add_comm (t₂ k).b, add_comm (t₂ k).c]
    exact h k
  · rw [add_comm (t₁ k).a, add_comm (t₁ k).b, add_comm (t₁ k).c]
    exact h k

private theorem honestC2_involutive {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) (e₁ : DealerExtra q m) (a02 b02 : ZMod q) :
    honestC2 t₂ t₁ (honestC2 t₁ t₂ e₁ a02 b02) e₁.a0 e₁.b0 = e₁ := by
  ext k <;> simp only [honestC2_a0, honestC2_b0, honestC2_c0, honestC2_cTail,
    PartyDeal.polyA, PartyDeal.polyB, DealerExtra.toDeal_a, DealerExtra.toDeal_b]
  · ring
  · rw [add_comm (interpPoly (Fin.cons a02 fun j => (t₂ j).a)),
      add_comm (interpPoly (Fin.cons b02 fun j => (t₂ j).b))]
    ring

private theorem eval_deal_eq_map {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) :
    ProbComp.eval (deal t₁ t₂) =
      (PMF.uniformOfFintype (DealerExtra q m × ZMod q × ZMod q)).map
        (fun x => (x.1.toDeal t₁, (honestC2 t₁ t₂ x.1 x.2.1 x.2.2).toDeal t₂)) := by
  simp only [deal, pmf_norm, ProbComp.eval_uniform]
  relabel_uniform (Equiv.refl (DealerExtra q m × ZMod q × ZMod q))

/-- Symmetry of the honest dealer distribution: swapping `(d₁, d₂)` from `deal t₁ t₂` gives
`deal t₂ t₁`. -/
theorem eval_deal_swap {q m : ℕ} [Fact (Nat.Prime q)]
    (t₁ t₂ : Fin m → TripleShare (ZMod q)) :
    (ProbComp.eval (deal t₁ t₂)).map Prod.swap = ProbComp.eval (deal t₂ t₁) := by
  rw [eval_deal_eq_map, eval_deal_eq_map, PMF.map_comp]
  relabel_uniform (fun x : DealerExtra q m × ZMod q × ZMod q =>
    (honestC2 t₁ t₂ x.1 x.2.1 x.2.2, x.1.a0, x.1.b0)) with x
  · refine Function.LeftInverse.injective (g := fun z : DealerExtra q m × ZMod q × ZMod q =>
      (honestC2 t₂ t₁ z.1 z.2.1 z.2.2, z.1.a0, z.1.b0)) fun y => ?_
    ext <;> simp [honestC2_involutive, honestC2_a0, honestC2_b0]
  · exact Prod.ext rfl (congrArg (fun e => e.toDeal t₁)
      (honestC2_involutive t₁ t₂ x.1 x.2.1 x.2.2).symm)

/-- Interactive adversary corrupting `P₂` in Protocol 23.5 (Section 23.2.4.7). -/
structure CorruptP2Adversary (q m : ℕ) (σ : Type) where
  /-- Samples `(t₁, t₂, st)`. Privacy requires `(t₁, t₂)` to satisfy `ProductRelations`. -/
  chooseInputs : ProbComp ((Fin m → TripleShare (ZMod q)) × (Fin m → TripleShare (ZMod q)) × σ)
  /-- Chooses `P₂`'s evaluation opening after receiving `d₂`, `r`, and `P₁`'s evaluation
  `(α₁, β₁, γ₁)`. -/
  sendOpening :
    σ → PartyDeal q m → ZMod q → ZMod q × ZMod q × ZMod q →
      ProbComp ((ZMod q × ZMod q × ZMod q) × σ)
  /-- Outputs final Boolean bit after observing `P₁`'s acceptance decision. -/
  finish : σ → Bool → ProbComp Bool

/-- Real privacy experiment against corrupt `P₂` for Protocol 23.5 under `2 * m < q`. -/
@[expose]
noncomputable def experiment0P2 (q m : ℕ) [Fact (Nat.Prime q)] (hm : 2 * m < q) {σ : Type}
    (A : CorruptP2Adversary q m σ) : ProbComp Bool :=
  haveI : Nonempty (Challenge q m) := nonempty_challenge q m (succ_lt_of_two_mul_lt hm)
  do
    let (t₁, t₂, st) ← A.chooseInputs
    let (d₁, d₂) ← deal t₁ t₂
    let r ← ProbComp.uniform (Challenge q m)
    let α₁ := d₁.polyA.eval r.1
    let β₁ := d₁.polyB.eval r.1
    let γ₁ := d₁.polyC.eval r.1
    let ((α₂, β₂, γ₂), st) ← A.sendOpening st d₂ r.1 (α₁, β₁, γ₁)
    let acc := decide ((α₁ + α₂) * (β₁ + β₂) = γ₁ + γ₂)
    A.finish st acc

/-- Simulator `S_D^(2)` playing `P₁` in Steps 3 and 5 of Protocol 23.5: given `d₂`, samples
uniform `r ∈ Challenge q m` (Step 3) and uniform `(α₁, β₁)`, and solves `(23.9)`, with the roles
of `P₁` and `P₂` swapped, for `γ₁` (Step 5). `noncomputable`, with no running-time claim. -/
@[expose]
noncomputable def sim2Eval (q m : ℕ) [Fact (Nat.Prime q)] (hm : 2 * m < q)
    (d₂ : PartyDeal q m) : ProbComp (ZMod q × ZMod q × ZMod q × ZMod q) :=
  haveI : Nonempty (Challenge q m) := nonempty_challenge q m (succ_lt_of_two_mul_lt hm)
  do
    let r ← ProbComp.uniform (Challenge q m)
    let α₁ ← ProbComp.uniform (ZMod q)
    let β₁ ← ProbComp.uniform (ZMod q)
    let γ₁ := (α₁ + d₂.polyA.eval r.1) * (β₁ + d₂.polyB.eval r.1) - d₂.polyC.eval r.1
    return (r.1, α₁, β₁, γ₁)

/-- Simulated privacy experiment against corrupt `P₂` using `S_D^(2)` (`t₁` is unused by the
simulator). `noncomputable`, with no running-time claim. -/
@[expose]
noncomputable def experiment1P2 (q m : ℕ) [Fact (Nat.Prime q)] (hm : 2 * m < q) {σ : Type}
    (A : CorruptP2Adversary q m σ) : ProbComp Bool := do
  let (_, t₂, st) ← A.chooseInputs
  let d₂ ← simDeal q m t₂
  let (r, α₁, β₁, γ₁) ← sim2Eval q m hm d₂
  let ((α₂, β₂, γ₂), st) ← A.sendOpening st d₂ r (α₁, β₁, γ₁)
  let acc := decide ((α₁ + α₂) * (β₁ + β₂) = γ₁ + γ₂)
  A.finish st acc

/-- **Fact 23.2 (corrupt `P₂`)**: under `2 * m < q` and valid inputs satisfying
`ProductRelations`, `experiment0P2` and `experiment1P2` induce identical output distributions on
`Bool` (and hence equal probabilities of outputting `true`/`1`). -/
theorem eval_experiment0P2_eq_experiment1P2 {q m : ℕ} [Fact (Nat.Prime q)] (hm : 2 * m < q)
    {σ : Type} (A : CorruptP2Adversary q m σ)
    (hrel : ∀ t₁ t₂ st, (t₁, t₂, st) ∈ (ProbComp.eval A.chooseInputs).support →
      ProductRelations t₁ t₂) :
    ProbComp.eval (experiment0P2 q m hm A) = ProbComp.eval (experiment1P2 q m hm A) := by
  have : Nonempty (Challenge q m) := nonempty_challenge q m (succ_lt_of_two_mul_lt hm)
  simp only [experiment0P2, experiment1P2, sim2Eval, simDeal, pmf_norm, ProbComp.eval_uniform]
  refine Cslib.Probability.PMF.bind_congr_on_support _ _ _ fun ⟨t₁, t₂, st⟩ hx => ?_
  have htx : ProductRelations t₂ t₁ := productRelations_comm.mp (hrel t₁ t₂ st hx)
  have hswap : ProbComp.eval (deal t₁ t₂) = (ProbComp.eval (deal t₂ t₁)).map Prod.swap := by
    rw [← eval_deal_swap t₁ t₂, PMF.map_comp]
    simp only [Function.comp_def, Prod.swap_swap]
    exact (PMF.map_id _).symm
  rw [hswap, PMF.bind_map]
  simp only [deal, pmf_norm, ProbComp.eval_uniform, Prod.swap]
  congr 1 with e₂ : 1
  rw [bind_uniform_uniform_bind_comm]
  congr 1 with r : 1
  have h1 := bind_honestOpening_eq_bind_uniform hm htx e₂ r.2 fun (α₁, β₁, γ₁) =>
    (ProbComp.eval (A.sendOpening st (e₂.toDeal t₂) r.1 (α₁, β₁, γ₁))).bind
      fun ((α₂, β₂, γ₂), st') =>
        ProbComp.eval (A.finish st' (decide ((α₁ + α₂) * (β₁ + β₂) = γ₁ + γ₂)))
  simpa only [add_comm] using h1

end Cslib.Crypto.Protocols.MPC.ProductRelation
