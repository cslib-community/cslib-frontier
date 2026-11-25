/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.AffineDisperser4n
public import CslibFrontier.Computability.Complexity.AffineDisperser
public import CslibFrontier.Computability.Complexity.AffineDisperser.Li.PolyTime
import CslibFrontier.Tactic.LinarithCast

/-!
# Explicit `4N - o(N)` circuit lower bounds in `P` and stratified Farkas optimality

This module packages three families of consequences of `four_mul_le_cost_add` and
`four_mul_le_size_add`:

* **Unconditional `4N - O(N ^ (4 / 5))` lower bound in `P`**: instantiating `four_mul_le_cost_add`
  at `Li.primeDisperser` (`CslibFrontier.Computability.Complexity.AffineDisperser.Li.PolyTime`,
  Milestone 1 toward `#4323`) yields an unconditional language in `P` requiring at least
  `4 * N - 19332 * N ^ (4 / 5)` genuinely binary `B₂` gates (`binaryB2Cost`, with constants and
  negations free), and hence at least `4 * N - 19332 * N ^ (4 / 5)` total gates, for all
  sufficiently large `N` (`exists_mem_P_eventually_le_cost_primeDisperser`,
  `exists_mem_P_eventually_le_size_primeDisperser`). Formalizing `4n - O(log n)`
  ([MishraSanthanam2026Revision1], Theorem 1.1, p. 2) remains open pending an explicit
  `O(log n)`-dimension disperser in Lean (`#4323`).
* **Explicit `4N - O(N / log N)` lower bound via `explicitDisperser`**: instantiating at
  `explicitDisperser` improves the constant from `60 * N / (Nat.log 2 N + 1) + 10` to
  `54 * N / (Nat.log 2 N + 1) + 9` under both `binaryB2Cost` and `size`
  (`exists_mem_P_eventually_four_mul_sub_le_cost`, `exists_mem_P_eventually_four_mul_sub_le_size`).
* **Weight and `State`-grounded bigraded Farkas optimality**:
  - Rational LP optimality for uniform `0/α` weights `(α, β, c)` under `c ≤ 2 * β + 3`:
    `c - α ≤ 4` (`weight_sub_le_four`) and `c - α = 4` forces `3 ≤ β`, `5 ≤ α`, `9 ≤ c`, and
    `α = β + 2` (`weight_lower_bounds_of_sub_eq_four`).
  - **Original `State`-grounded bigraded optimality** (`stratifiedPotential`,
    `StratifiedStepSound`, `stratifiedStepSound_uniform`, `stratified_weight_sub_le_four`,
    `stratified_weight_lower_bounds_of_sub_eq_four`, extending the discussion in
    [MishraSanthanam2026Revision1], Remark 4.3): for any
    bigraded `(gateChildren, eqnChildren)` potential on `State n` that is sound across the
    `AffineDisperser4n` transitions (equation-free/pair-free initial states, `moveAffine`,
    `PairInSystem` + `unitDelete`, `Case 5b` pair creation, and `Case 5a` `andOnPairStep`),
    concrete valid `State` transitions force `c - w_init ≤ 4`, and attaining `c - w_init = 4`
    forces `ce = 1`, `3 ≤ bp 1 0 1 0`, `bp 0 1 1 0 = bp 1 0 1 0`, `5 ≤ w 2 0`, `5 ≤ w_init`,
    `9 ≤ c`, and `w 2 0 = bp 1 0 1 0 + 2` (attained by `stratifiedStepSound_uniform`).

## Main definitions

* `Cslib.Circuits.Boolean.AffineDisperser4n.stratifiedPotential`: bigraded
  `(gateChildren, eqnChildren)` potential of a `4n` state.
* `Cslib.Circuits.Boolean.AffineDisperser4n.StratifiedStepSound`: soundness of a bigraded
  potential across the `AffineDisperser4n` gate-elimination rules.

## Main results

* `Cslib.Circuits.Boolean.AffineDisperser4n.weight_sub_le_four`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.weight_lower_bounds_of_sub_eq_four`: rational Farkas
  optimality of `(α, β, c) = (5, 3, 9)` for uniform `0/α` weights.
* `Cslib.Circuits.Boolean.AffineDisperser4n.stratifiedStepSound_uniform`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.stratified_weight_sub_le_four`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.stratified_weight_lower_bounds_of_sub_eq_four`:
  non-vacuity and `State`-grounded bigraded Farkas optimality of `4n - 9d`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.eventually_four_mul_le_cost_add_explicitDisperser`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.eventually_four_mul_le_size_add_explicitDisperser`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.exists_mem_P_eventually_four_mul_sub_le_cost`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.exists_mem_P_eventually_four_mul_sub_le_size`:
  explicit `4N - O(N / log N)` lower bounds via `explicitDisperser`.
* `Cslib.Circuits.Boolean.AffineDisperser4n.exists_mem_P_eventually_le_cost_primeDisperser`,
  `Cslib.Circuits.Boolean.AffineDisperser4n.exists_mem_P_eventually_le_size_primeDisperser`:
  explicit `4N - O(N ^ (4 / 5))` lower bounds in `P` via `Li.primeDisperser`.

## References

* [O. S. Mishra and R. Santhanam, *An Explicit 4n - O(log n) Size Lower Bound against General
  Boolean Circuits*][MishraSanthanam2026Revision1], ECCC TR26-260 revision 1, Theorem 4.1
  (p. 21) and Remark 4.3 (p. 26). The `(5, 3, 9)` weights, `binaryB2Cost`, the
  `Li.primeDisperser` instantiation, and the bigraded Farkas optimality theorems are refinements
  of this formalization.
* [V. Shoup, *New algorithms for finding irreducible polynomials over finite fields*][Shoup1990]
* [X. Li, *Two source extractors for asymptotically optimal entropy, and (many) more*][Li2023]
-/

public section

namespace Cslib.Circuits.Boolean.AffineDisperser4n

open Filter Finset Cslib.BitString Cslib.Circuits Cslib.Circuits.Boolean
open Cslib.Circuits.Boolean.SemiCircuit Cslib.Circuits.Boolean.AffineDisperserCore
open Cslib.Complexity Cslib.AffineDisperser

/-! ### Rational LP optimality for `(α, β, c) = (5, 3, 9)` -/

/-- Rational Farkas lemma on the `#4322` linear constraints: under `α ≤ β + 2` and
`c ≤ 2 * α - β + 2`, the leading coefficient `c - α` cannot exceed `4`. This is a formal
algebraic refinement of the potential-reweighting discussion in [MishraSanthanam2026Revision1],
Remark 4.3 (p. 26), which states optimality without listing these inequalities. -/
theorem weight_sub_le_four {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * α - β + 2) :
    c - α ≤ 4 := by
  linarith

/-- Rational Farkas lemma on the tightened `(5, 3, 9)` linear constraints (original refinement of
`#4322`'s `c ≤ 2 * β + 2` to `c ≤ 2 * β + 3`): any rational triple `(α, β, c)` satisfying those
inequalities with `c - α = 4` satisfies `3 ≤ β`, `5 ≤ α`, `9 ≤ c`, and `α = β + 2`. -/
theorem weight_lower_bounds_of_sub_eq_four {α β c : ℚ} (h₁ : α ≤ β + 2) (h₂ : c ≤ 2 * β + 3)
    (h₃ : c ≤ 2 * α - β + 2) (h₄ : c - α = 4) :
    3 ≤ β ∧ 5 ≤ α ∧ 9 ≤ c ∧ α = β + 2 :=
  ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### `State`-grounded bigraded Farkas optimality of `4n - 9d` -/

/-- Bigraded potential of a `4n` gate-elimination state `S`: gates have unit cost `1`, equations
have cost `ce`, unpaired parameters with `dg` gate-children and `de` equation-children have weight
`w dg de`, and zero-locus pairs with endpoint bidegrees `(dg₁, de₁)` and `(dg₂, de₂)` have weight
`bp dg₁ de₁ dg₂ de₂`. -/
@[expose] def stratifiedPotential (ce : ℚ) (w : ℕ → ℕ → ℚ) (bp : ℕ → ℕ → ℕ → ℕ → ℚ) {n : ℕ}
    (S : State n) : ℚ :=
  (S.gates.card : ℚ) + ce * (S.eqns.card : ℚ) +
    (∑ x ∈ S.unpaired, w (S.gateChildren x).card (S.eqnChildren x).card) +
    (∑ pr ∈ S.pairs,
      bp (S.gateChildren pr.fst).card (S.eqnChildren pr.fst).card
        (S.gateChildren pr.snd).card (S.eqnChildren pr.snd).card)

/-- Soundness of a bigraded potential `(ce, w, bp)` with slope `c` and initial per-input budget
`w_init` across the syntactic state transitions of `AffineDisperser4n` (equation-free/pair-free
initial states such as `initialState C`, `moveAffine`, `PairInSystem` + `unitDelete`, `Case 5b`
pair creation, and `Case 5a` `andOnPairStep`). -/
structure StratifiedStepSound (ce : ℚ) (w : ℕ → ℕ → ℚ) (bp : ℕ → ℕ → ℕ → ℕ → ℚ)
    (c w_init : ℚ) : Prop where
  /-- Unused unpaired parameters carry weight `0`. -/
  w_zero : w 0 0 = 0
  /-- On any equation-free, pair-free valid state over `Finset.range n` (including
  `initialState C`), the potential is at most `gates.card + w_init * n`. -/
  init_le : ∀ {n : ℕ} {f : BooleanFunction n} {S : State n},
    S.Valid f → S.eqns = ∅ → S.pairs = ∅ → S.params = Finset.range n →
      stratifiedPotential ce w bp S ≤ (S.gates.card : ℚ) + w_init * (n : ℚ)
  /-- Moving an affine gate reading no gates into `S.eqns` does not increase the potential. -/
  moveAffine_le : ∀ {n : ℕ} {f : BooleanFunction n} {S : State n}, S.Valid f →
    ∀ {J : ℕ}, J ∈ S.gates → IsAffineOp (S.gate J).op → (∀ i, (S.gate J).Reads i → i ∉ S.gates) →
      stratifiedPotential ce w bp (S.moveAffine J S.freshEqn) ≤ stratifiedPotential ce w bp S
  /-- Case 4 (`PairInSystem` followed by `unitDelete`) satisfies `ΔP ≤ c Δa`. -/
  pairInSystem_le : ∀ {n : ℕ} {f : BooleanFunction n} {S : State n},
    S.Valid f → ¬ S.DegeneratePair → ¬ S.PartnersShareChild →
    ∀ {pr : ZeroPair}, pr ∈ S.pairs → ∀ {p e : ℕ}, pr.Contains p → e ∈ S.eqns →
      p ∈ (S.eqn e).terms → ¬ S.out.Reads p → ∀ {Hr : ℕ ⊕ ℕ}, Hr ∈ S.children (pr.partner p) →
      let S₂ := (S.fixConst (pr.partner p) (pr.partnerBias p)).deleteConstraint Hr
      S₂.deg p ≠ 0 → ∀ {Q : ℕ} {c₀ : Bool} {T : Finset ℕ}, Q ∈ S₂.aux → S₂.AffineIn Q c₀ T →
        p ∈ T →
        let S' := (S₂.swap p Q c₀ T).dropEqn e p
        stratifiedPotential ce w bp S' + c * ((S.a - S'.a : ℕ) : ℚ) ≤ stratifiedPotential ce w bp S
  /-- Case 5b (`addPair` plus deleting `G` and consumer gate `K`) satisfies `ΔP ≤ c Δa`. -/
  pairCreation_le : ∀ {n : ℕ} {f : BooleanFunction n} {S : State n}, S.Valid f →
    ∀ {G t₁ t₂ : ℕ}, G ∈ S.gates → t₁ ≠ t₂ → (S.gate G).Reads t₁ → (S.gate G).Reads t₂ →
      t₁ ∈ S.unpaired → t₂ ∈ S.unpaired → ∀ {α β γ : Bool},
      (∀ val, (S.gate G).eval val = (((val t₁ ^^ α) && (val t₂ ^^ β)) ^^ γ)) →
      ∀ {K : ℕ}, K ∈ S.gates → (S.gate K).Reads G →
      let S' := ((S.addPair ⟨t₁, α, t₂, β⟩).deleteGate G (Lit.const γ)).deleteConstraint (.inl K)
      stratifiedPotential ce w bp S' + c * ((S.a - S'.a : ℕ) : ℚ) ≤ stratifiedPotential ce w bp S
  /-- Case 5a (`andOnPairStep`) satisfies `ΔP ≤ c Δa`. -/
  andOnPair_le : ∀ {n : ℕ} {f : BooleanFunction n} {S : State n},
    S.Valid f → ¬ S.DegeneratePair → ¬ S.PartnersShareChild →
    ∀ {G p w₀ : ℕ} {pr : ZeroPair}, G ∈ S.gates → pr ∈ S.pairs → pr.Contains p →
      w₀ ∈ S.params → p ≠ w₀ → (S.gate G).Reads p → (S.gate G).Reads w₀ →
      ∀ {prw : Option ZeroPair}, (prw = none → ¬ S.Paired w₀) →
      (∀ q, prw = some q → q ∈ S.pairs ∧ q.Contains w₀) → ∀ {b c₀ : Bool},
      (∀ val : ℕ → Bool, val w₀ = b → (S.gate G).eval val = c₀) →
      ∀ {Hr Hw' : ℕ ⊕ ℕ} {K : ℕ}, Hr ∈ S.children (pr.partner p) →
      (∀ q, prw = some q → b ≠ q.bias w₀ → K ∈ S.gates ∧ (S.gate K).Reads G) →
      (∀ q, prw = some q → b ≠ q.bias w₀ → Hw' ∈ S.children (q.partner w₀)) →
      let S' := S.andOnPairStep G pr p w₀ prw b c₀ Hr K Hw'
      stratifiedPotential ce w bp S' + c * ((S.a - S'.a : ℕ) : ℚ) ≤ stratifiedPotential ce w bp S

private theorem stratifiedPotential_uniform_eq_W {n : ℕ} (S : State n) :
    stratifiedPotential 1 (fun dg de => (weight (dg + de) : ℚ)) (fun _ _ _ _ => 3) S =
      (S.W : ℚ) := by
  simp only [stratifiedPotential, AffineDisperserCore.State.W, AffineDisperserCore.State.s,
    SemiCircuit.size, AffineDisperserCore.State.q, ← SemiCircuit.deg_eq, Finset.sum_const,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
  ring

private theorem uniform_le_of_step {n : ℕ} {f : BooleanFunction n} {S S' : State n}
    (hstep : AffineDisperserCore.State.Step f S S') :
    stratifiedPotential 1 (fun dg de => (weight (dg + de) : ℚ)) (fun _ _ _ _ => 3) S' +
        9 * ((S.a - S'.a : ℕ) : ℚ) ≤
      stratifiedPotential 1 (fun dg de => (weight (dg + de) : ℚ)) (fun _ _ _ _ => 3) S := by
  rw [stratifiedPotential_uniform_eq_W, stratifiedPotential_uniform_eq_W]
  have hp := hstep.potential
  have ha := hstep.a_le
  rw [config_ca] at hp
  have hnat : S'.W + 9 * (S.a - S'.a) ≤ S.W := by omega
  exact_mod_cast hnat

/-- Non-vacuity of `StratifiedStepSound`: the uniform `(5, 3, 9)` potential of `AffineDisperser4n`
(`ce = 1`, `w dg de = weight (dg + de)`, `bp = 3`, `c = 9`, `w_init = 5`) satisfies
`StratifiedStepSound`. -/
theorem stratifiedStepSound_uniform :
    StratifiedStepSound 1 (fun dg de => (weight (dg + de) : ℚ)) (fun _ _ _ _ => 3) 9 5 where
  w_zero := rfl
  init_le {n _ S} _ heq hpairs hparams := by
    rw [stratifiedPotential_uniform_eq_W]
    have hwt : ∑ x ∈ S.unpaired, weight (S.deg x) ≤ 5 * n := by
      calc ∑ x ∈ S.unpaired, weight (S.deg x)
          ≤ ∑ _ ∈ S.unpaired, 5 := Finset.sum_le_sum fun _ _ => weight_le_five _
        _ = S.unpaired.card * 5 := Finset.sum_const_nat fun _ _ => rfl
        _ ≤ S.params.card * 5 := Nat.mul_le_mul_right 5 (Finset.card_filter_le _ _)
        _ = 5 * n := by rw [hparams, Finset.card_range, mul_comm]
    have hW : S.W ≤ S.gates.card + 5 * n := by
      unfold AffineDisperserCore.State.W AffineDisperserCore.State.s SemiCircuit.size
        AffineDisperserCore.State.q
      rw [heq, hpairs, Finset.card_empty, Finset.card_empty, config_cs, config_cq, config_weight]
      omega
    exact_mod_cast hW
  moveAffine_le {_ _ _} hS {_} hJ haff hin := by
    rw [stratifiedPotential_uniform_eq_W, stratifiedPotential_uniform_eq_W]
    exact_mod_cast (State.Valid.preparation_moveAffine hS hJ haff hin).1.W_le
  pairInSystem_le {_ _ _} hS hndeg hnsh {_} hpr {_ _} hprp he hpe hout {_} hHr h0 {_ _ _} hQ
      haff hpT :=
    uniform_le_of_step
      ((State.Valid.step_pairInSystem_of hS hndeg hnsh hpr hprp he hpe hout hHr).2.2.2.2
        h0 _ _ _ hQ haff hpT)
  pairCreation_le {_ _ _} hS {_ _ _} hG htne hGt₁ hGt₂ ht₁unp ht₂unp {_ _ _} hG_eval {_} hK hKr :=
    uniform_le_of_step
      (State.Valid.step_pairCreation_of hS hG htne hGt₁ hGt₂ ht₁unp ht₂unp hG_eval hK hKr)
  andOnPair_le {_ _ _} hS hndeg hnsh {_ _ _ _} hG hpr hprp hwpar hpw hGp hGw {_} hnone hsome
      {_ _} hbc {_ _ _} hHr hK hHw' :=
    uniform_le_of_step
      (State.Valid.step_andOnPair_of hS hndeg hnsh hG hpr hprp hwpar hpw hGp hGw hnone hsome
        hbc hHr hK hHw')

private def mkBaseState (n : ℕ) (gates : Finset ℕ) (gate : ℕ → Gate) (out : Lit) : State n where
  params := Finset.range n
  aux := ∅
  gates := gates
  gate := gate
  eqns := ∅
  eqn _ := ⟨∅, false⟩
  out := out
  pairs := ∅
  phi val i := val i

private def argLiveOK (n : ℕ) (gates : Finset ℕ) : Arg → Bool
  | .const _ => true
  | .node i => decide (i < n ∨ i ∈ gates)

private def baseStateOK {n : ℕ} (S : State n) : Bool :=
  decide (Disjoint (Finset.range n) S.gates) &&
    decide (∀ J ∈ S.gates, ∀ i ∈ S.gates, (S.gate J).Reads i → i < J) &&
    decide (∀ J ∈ S.gates, argLiveOK n S.gates (S.gate J).left = true ∧
      argLiveOK n S.gates (S.gate J).right = true) &&
    argLiveOK n S.gates S.out.arg

private theorem mem_live_of_argLiveOK {n : ℕ} {S : State n} (hp : S.params = Finset.range n)
    {a : Arg} {i : ℕ} (ha : argLiveOK n S.gates a = true) (hi : a = .node i) :
    i ∈ S.live := by
  subst hi
  rcases of_decide_eq_true ha with hlt | hg
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hp ▸ Finset.mem_range.2 hlt))
  · exact Finset.mem_union_right _ hg

private theorem exists_valid_of_baseStateOK {n : ℕ} (S : State n)
    (hp : S.params = Finset.range n) (haux : S.aux = ∅) (heq : S.eqns = ∅)
    (hpairs : S.pairs = ∅) (hphi : S.phi = fun val i => val i) (hok : baseStateOK S = true) :
    ∃ f : BooleanFunction n, S.Valid f := by
  obtain ⟨h123, hout⟩ := Bool.and_eq_true_iff.1 hok
  obtain ⟨h12, hreads'⟩ := Bool.and_eq_true_iff.1 h123
  obtain ⟨hdisj', hlt'⟩ := Bool.and_eq_true_iff.1 h12
  have hwf : S.WellFormed :=
    { disjoint_params_aux := by rw [haux]; exact Finset.disjoint_empty_right _
      disjoint_params_gates := by rw [hp]; exact of_decide_eq_true hdisj'
      disjoint_aux_gates := by rw [haux]; exact Finset.disjoint_empty_left _
      reads_lt := of_decide_eq_true hlt'
      reads_live := fun J hJ i hr => by
        obtain ⟨hl, hr'⟩ := (of_decide_eq_true hreads') J hJ
        exact hr.elim (mem_live_of_argLiveOK hp hl) (mem_live_of_argLiveOK hp hr')
      terms_subset := fun _ he => absurd (heq ▸ he) (Finset.notMem_empty _)
      card_terms_le := fun _ he => absurd (heq ▸ he) (Finset.notMem_empty _)
      out_live := fun i hi => mem_live_of_argLiveOK hp hout hi
      solvable := fun u =>
        ⟨u, fun _ _ => rfl, fun _ he => absurd (heq ▸ he) (Finset.notMem_empty _)⟩
      unique := fun _ _ _ _ _ _ hv => absurd (haux ▸ hv) (Finset.notMem_empty _) }
  have hcongr : ∀ {val val'}, S.Consistent val → S.Consistent val' →
      (∀ j ∈ S.params, val j = val' j) → ∀ k ∈ S.live, val k = val' k := by
    intro val val' hc hc' hag k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hk
      rcases Finset.mem_union.1 hk with hpa | hg
      · rcases Finset.mem_union.1 hpa with hpk | hak
        · exact hag k hpk
        · exact absurd (haux ▸ hak) (Finset.notMem_empty _)
      · rw [hc.2 k hg, hc'.2 k hg]
        refine Gate.eval_congr fun i hi => ?_
        have hilive := hwf.reads_live k hg i hi
        rcases Finset.mem_union.1 hilive with hpa' | hg'
        · rcases Finset.mem_union.1 hpa' with hp' | ha'
          · exact hag i hp'
          · exact absurd (haux ▸ ha') (Finset.notMem_empty _)
        · exact ih i (hwf.reads_lt k hg i hg' hi) hilive
  let evalFn : BooleanFunction n := fun x =>
    S.out.eval (Classical.choose
      (hwf.exists_consistent fun j => if hj : j < n then x ⟨j, hj⟩ else false))
  refine ⟨evalFn,
    { wf := hwf
      pair_mem := fun _ h => absurd (hpairs ▸ h) (Finset.notMem_empty _)
      pairs_disjoint := fun _ h => absurd (hpairs ▸ h) (Finset.notMem_empty _)
      phi_congr := fun val val' h => by
        rw [hphi]
        exact funext fun i => h i (hp ▸ Finset.mem_range.2 i.isLt)
      phi_affine := by rw [hphi]; exact fun _ _ _ => rfl
      phi_injective := fun val val' h j hj => by
        rw [hphi] at h
        exact congrFun h ⟨j, Finset.mem_range.1 (hp ▸ hj)⟩
      computes := fun val hcons _ => ?_ }⟩
  have hspec := Classical.choose_spec
    (hwf.exists_consistent fun j => if hj : j < n then S.phi val ⟨j, hj⟩ else false)
  exact Lit.eval_congr fun i hi => hcongr hcons hspec.2
    (fun j hj => by
      have hlt : j < n := Finset.mem_range.1 (hp ▸ hj)
      have hphi_j : S.phi val ⟨j, hlt⟩ = val j := by rw [hphi]
      exact ((hspec.1 j hj).trans (dite_eq_left hlt)).trans hphi_j |>.symm) i (hwf.out_live i hi)

private def gateReadsNoGate {n : ℕ} (S : State n) (J : ℕ) : Bool :=
  (match (S.gate J).left with | .const _ => true | .node i => decide (i ∉ S.gates)) &&
    (match (S.gate J).right with | .const _ => true | .node i => decide (i ∉ S.gates))

private theorem reads_notMem_of_gateReadsNoGate {n : ℕ} {S : State n} {J : ℕ}
    (h : gateReadsNoGate S J = true) : ∀ i, (S.gate J).Reads i → i ∉ S.gates := by
  obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.1 h
  rintro i (hl | hr)
  · rw [hl] at h1; exact of_decide_eq_true h1
  · rw [hr] at h2; exact of_decide_eq_true h2

private theorem valid_moveAffine_of {n : ℕ} {f : BooleanFunction n} {S : State n} (hS : S.Valid f)
    {J : ℕ} (hJ : J ∈ S.gates) (haff : IsAffineOp (S.gate J).op)
    (hr : gateReadsNoGate S J = true) : (S.moveAffine J S.freshEqn).Valid f :=
  (State.Valid.preparation_moveAffine hS hJ haff (reads_notMem_of_gateReadsNoGate hr)).1.valid

private theorem StratifiedStepSound.moveAffine_of {ce : ℚ} {w : ℕ → ℕ → ℚ}
    {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {c w_init : ℚ} (h : StratifiedStepSound ce w bp c w_init)
    {n : ℕ} {f : BooleanFunction n} {S : State n} (hS : S.Valid f) {J : ℕ}
    (hJ : J ∈ S.gates) (haff : IsAffineOp (S.gate J).op) (hr : gateReadsNoGate S J = true) :
    stratifiedPotential ce w bp (S.moveAffine J S.freshEqn) ≤ stratifiedPotential ce w bp S :=
  h.moveAffine_le hS hJ haff (reads_notMem_of_gateReadsNoGate hr)

private theorem not_degPair_of_pairs {n : ℕ} {S : State n} {F : Finset ℕ}
    (hp : ∀ pr ∈ S.pairs, pr.fst ∈ F ∧ pr.snd ∈ F) (hd : ∀ x ∈ F, S.deg x = 1) :
    ¬ S.DegeneratePair := by
  rintro ⟨p, ⟨pr, hpr, h1 | h2⟩, h02⟩
  · subst h1; have h := hd _ (hp pr hpr).1; rw [h] at h02; omega
  · subst h2; have h := hd _ (hp pr hpr).2; rw [h] at h02; omega

private theorem not_partnersShareChild_of {n : ℕ} {S : State n}
    (h : ∀ pr ∈ S.pairs, S.children pr.fst ∩ S.children pr.snd = ∅) :
    ¬ S.PartnersShareChild := by
  rintro ⟨pr, hpr, x, hx⟩
  rw [h pr hpr] at hx
  exact Finset.notMem_empty x hx

/-- `2`-input, `3`-gate state (`x₀ ∧ x₁`, `(!x₀) ∧ x₁`, `g₂ ∧ g₃`) witnessing `w 2 0 ≤ w_init`
at `init_le` and `c + bp 1 0 1 0 ≤ 2 * w 2 0 + 2` under `Case 5b`. -/
private def fanout2State : State 2 :=
  mkBaseState 2 {2, 3, 4}
    (fun j =>
      if j = 2 then ⟨(· && ·), .node 0, .node 1⟩
      else if j = 3 then ⟨fun a b => !a && b, .node 0, .node 1⟩
      else ⟨(· && ·), .node 2, .node 3⟩)
    ⟨.node 4, false⟩

private theorem fanout2_bounds {ce : ℚ} {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {c w_init : ℚ}
    (h : StratifiedStepSound ce w bp c w_init) :
    w 2 0 ≤ w_init ∧ c + bp 1 0 1 0 ≤ 2 * w 2 0 + 2 := by
  let S := fanout2State
  obtain ⟨_, hS⟩ := exists_valid_of_baseStateOK S rfl rfl rfl rfl rfl (by decide)
  have hinit := h.init_le hS rfl rfl rfl
  have hS_cards : S.gates.card = 3 ∧ S.eqns = ∅ ∧ S.unpaired = {0, 1} ∧ S.pairs = ∅ ∧
      (S.gateChildren 0).card = 2 ∧ (S.eqnChildren 0).card = 0 ∧
      (S.gateChildren 1).card = 2 ∧ (S.eqnChildren 1).card = 0 := by decide
  have hevalS : stratifiedPotential ce w bp S = 3 + 2 * w 2 0 := by
    rcases hS_cards with ⟨hg, he, hu, hp, hg0, he0, hg1, he1⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.card_empty, Finset.sum_empty,
      Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), hg0, he0, hg1, he1]
    ring
  rw [hevalS, hS_cards.1] at hinit
  have hpc := h.pairCreation_le hS (G := 2) (t₁ := 0) (t₂ := 1) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (α := false) (β := false) (γ := false)
    (fun val => by change (val 0 && val 1) = _; simp)
    (K := 4) (by decide) (by decide)
  let S' : State 2 := ((S.addPair ⟨0, false, 1, false⟩).deleteGate 2
    (Lit.const false)).deleteConstraint (.inl 4)
  have hS'_cards : S'.gates.card = 1 ∧ S'.eqns = ∅ ∧ S'.unpaired = ∅ ∧
      S'.pairs = {⟨0, false, 1, false⟩} ∧ S.a - S'.a = 1 ∧
      (S'.gateChildren 0).card = 1 ∧ (S'.eqnChildren 0).card = 0 ∧
      (S'.gateChildren 1).card = 1 ∧ (S'.eqnChildren 1).card = 0 := by decide
  have hevalS' : stratifiedPotential ce w bp S' = 1 + bp 1 0 1 0 := by
    rcases hS'_cards with ⟨hg, he, hu, hp, -, hg0, he0, hg1, he1⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.card_empty, Finset.sum_empty,
      Finset.sum_singleton, hg0, he0, hg1, he1]
    ring
  change stratifiedPotential ce w bp S' + c * ((S.a - S'.a : ℕ) : ℚ) ≤ _ at hpc
  rw [hevalS', hevalS, hS'_cards.2.2.2.2.1] at hpc
  exact ⟨by norm_num at hinit; linarith, by norm_num at hpc; linarith⟩

/-- `2`-input, `3`-gate XOR state witnessing `ce ≤ 1` when moving an affine gate reading two
auxiliary variables. -/
private def auxAuxState : State 2 :=
  mkBaseState 2 {2, 3, 4}
    (fun j =>
      if j = 2 then ⟨(· ^^ ·), .node 0, .node 1⟩
      else if j = 3 then ⟨fun a b => !a ^^ b, .node 0, .node 1⟩
      else ⟨(· ^^ ·), .node 2, .node 3⟩)
    ⟨.node 4, false⟩

private theorem auxAux_ce_le_one {ce : ℚ} {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {c w_init : ℚ}
    (h : StratifiedStepSound ce w bp c w_init) : ce ≤ 1 := by
  let S₀ := auxAuxState
  obtain ⟨_, hS₀⟩ := exists_valid_of_baseStateOK S₀ rfl rfl rfl rfl rfl (by decide)
  let S₁ : State 2 := S₀.moveAffine 2 S₀.freshEqn
  let S₂ : State 2 := S₁.moveAffine 3 S₁.freshEqn
  have hS₂ : S₂.Valid _ := valid_moveAffine_of
    (valid_moveAffine_of hS₀ (by decide) (by decide) (by decide))
    (by decide) (by decide) (by decide)
  have hmov := h.moveAffine_of hS₂ (J := 4) (by decide) (by decide) (by decide)
  let S₃ : State 2 := S₂.moveAffine 4 S₂.freshEqn
  have h2 : S₂.gates.card = 1 ∧ S₂.eqns.card = 2 ∧ S₂.unpaired = {0, 1} ∧ S₂.pairs = ∅ ∧
      (S₂.gateChildren 0).card = 0 ∧ (S₂.eqnChildren 0).card = 2 ∧
      (S₂.gateChildren 1).card = 0 ∧ (S₂.eqnChildren 1).card = 2 := by decide
  have h3 : S₃.gates.card = 0 ∧ S₃.eqns.card = 3 ∧ S₃.unpaired = {0, 1} ∧ S₃.pairs = ∅ ∧
      (S₃.gateChildren 0).card = 0 ∧ (S₃.eqnChildren 0).card = 2 ∧
      (S₃.gateChildren 1).card = 0 ∧ (S₃.eqnChildren 1).card = 2 := by decide
  have he2 : stratifiedPotential ce w bp S₂ = 1 + 2 * ce + 2 * w 0 2 := by
    rcases h2 with ⟨hg, he, hu, hp, hg0, he0, hg1, he1⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_empty,
      Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), hg0, he0, hg1, he1]; ring
  have he3 : stratifiedPotential ce w bp S₃ = 3 * ce + 2 * w 0 2 := by
    rcases h3 with ⟨hg, he, hu, hp, hg0, he0, hg1, he1⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_empty,
      Finset.sum_pair (by decide : (0 : ℕ) ≠ 1), hg0, he0, hg1, he1]; ring
  change stratifiedPotential ce w bp S₃ ≤ _ at hmov
  linarith

/-- `4`-input, `3`-gate state (`x₀ ⊕ x₂`, `x₁ ∧ x₃`, `g₄ ∧ g₅`) with two pairs witnessing
`ce + 2 * bp 0 1 1 0 ≤ 2 * bp 1 0 1 0 + 1` under `moveAffine`. -/
private def pairedPairedState : State 4 :=
  mkBaseState 4 {4, 5, 6}
    (fun j =>
      if j = 4 then ⟨(· ^^ ·), .node 0, .node 2⟩
      else if j = 5 then ⟨(· && ·), .node 1, .node 3⟩
      else ⟨(· && ·), .node 4, .node 5⟩)
    ⟨.node 6, false⟩

private theorem pairedPaired_bound {ce : ℚ} {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ}
    {c w_init : ℚ} (h : StratifiedStepSound ce w bp c w_init) :
    ce + 2 * bp 0 1 1 0 ≤ 2 * bp 1 0 1 0 + 1 := by
  let S₀ := pairedPairedState
  obtain ⟨_, hS₀⟩ := exists_valid_of_baseStateOK S₀ rfl rfl rfl rfl rfl (by decide)
  let S₁ : State 4 := S₀.addPair ⟨0, false, 1, false⟩
  let S₂ : State 4 := S₁.addPair ⟨2, false, 3, false⟩
  have hS₂ : S₂.Valid _ := State.Valid.addPair
    (State.Valid.addPair hS₀ ⟨by decide, by decide, by decide⟩)
    ⟨by decide, by decide, by decide⟩
  have hmov := h.moveAffine_of hS₂ (J := 4) (by decide) (by decide) (by decide)
  let S₃ : State 4 := S₂.moveAffine 4 S₂.freshEqn
  have hpne : (⟨0, false, 1, false⟩ : ZeroPair) ≠ ⟨2, false, 3, false⟩ := by decide
  have h2 : S₂.gates.card = 3 ∧ S₂.eqns.card = 0 ∧ S₂.unpaired = ∅ ∧
      S₂.pairs = {⟨0, false, 1, false⟩, ⟨2, false, 3, false⟩} ∧
      (S₂.gateChildren 0).card = 1 ∧ (S₂.eqnChildren 0).card = 0 ∧
      (S₂.gateChildren 1).card = 1 ∧ (S₂.eqnChildren 1).card = 0 ∧
      (S₂.gateChildren 2).card = 1 ∧ (S₂.eqnChildren 2).card = 0 ∧
      (S₂.gateChildren 3).card = 1 ∧ (S₂.eqnChildren 3).card = 0 := by decide
  have h3 : S₃.gates.card = 2 ∧ S₃.eqns.card = 1 ∧ S₃.unpaired = ∅ ∧
      S₃.pairs = {⟨0, false, 1, false⟩, ⟨2, false, 3, false⟩} ∧
      (S₃.gateChildren 0).card = 0 ∧ (S₃.eqnChildren 0).card = 1 ∧
      (S₃.gateChildren 1).card = 1 ∧ (S₃.eqnChildren 1).card = 0 ∧
      (S₃.gateChildren 2).card = 0 ∧ (S₃.eqnChildren 2).card = 1 ∧
      (S₃.gateChildren 3).card = 1 ∧ (S₃.eqnChildren 3).card = 0 := by decide
  have he2 : stratifiedPotential ce w bp S₂ = 3 + 2 * bp 1 0 1 0 := by
    rcases h2 with ⟨hg, he, hu, hp, c0, e0, c1, e1, c2, e2, c3, e3⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_empty, Finset.sum_pair hpne,
      c0, e0, c1, e1, c2, e2, c3, e3]; ring
  have he3 : stratifiedPotential ce w bp S₃ = 2 + ce + 2 * bp 0 1 1 0 := by
    rcases h3 with ⟨hg, he, hu, hp, c0, e0, c1, e1, c2, e2, c3, e3⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_empty, Finset.sum_pair hpne,
      c0, e0, c1, e1, c2, e2, c3, e3]; ring
  change stratifiedPotential ce w bp S₃ ≤ _ at hmov
  linarith

/-- `4`-input, `6`-gate state walking sequentially through `moveAffine` on `(paired, aux)`
(`ce + bp 0 1 1 0 ≤ bp 1 0 1 0 + 1`) and `PairInSystem` + `unitDelete`
(`w 2 0 ≤ bp 0 1 1 0 + 1 + ce`). -/
private def farkasCycleState : State 4 :=
  mkBaseState 4 {4, 5, 6, 7, 8, 9}
    (fun j =>
      if j = 4 then ⟨(· ^^ ·), .node 2, .node 3⟩
      else if j = 5 then ⟨(· ^^ ·), .node 0, .node 4⟩
      else if j = 6 then ⟨fun a b => !a && b, .node 1, .node 2⟩
      else if j = 7 then ⟨(· && ·), .node 5, .node 3⟩
      else if j = 8 then ⟨(· && ·), .node 5, .node 6⟩
      else ⟨(· && ·), .node 7, .node 8⟩)
    ⟨.node 9, false⟩

private theorem farkasCycle_bounds {ce : ℚ} {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ}
    {c w_init : ℚ} (h : StratifiedStepSound ce w bp c w_init) :
    ce + bp 0 1 1 0 ≤ bp 1 0 1 0 + 1 ∧ w 2 0 ≤ bp 0 1 1 0 + 1 + ce := by
  let S₀ := farkasCycleState
  obtain ⟨_, hS₀⟩ := exists_valid_of_baseStateOK S₀ rfl rfl rfl rfl rfl (by decide)
  let S₁ : State 4 := S₀.moveAffine 4 S₀.freshEqn
  let S₂ : State 4 := S₁.addPair ⟨0, false, 1, false⟩
  have hS₂ : S₂.Valid _ := State.Valid.addPair
    (valid_moveAffine_of hS₀ (by decide) (by decide) (by decide))
    ⟨by decide, by decide, by decide⟩
  have hmov := h.moveAffine_of hS₂ (J := 5) (by decide) (by decide) (by decide)
  let S₃ : State 4 := S₂.moveAffine 5 S₂.freshEqn
  have hS₃ : S₃.Valid _ := valid_moveAffine_of hS₂ (by decide) (by decide) (by decide)
  let pr₀ : ZeroPair := ⟨0, false, 1, false⟩
  let S₃' : State 4 := (S₃.fixConst (pr₀.partner 0) (pr₀.partnerBias 0)).deleteConstraint (.inl 6)
  have haff : S₃'.AffineIn 5 false {0, 2, 3} := by
    refine ⟨by decide, fun val heq => ?_⟩
    have he0 : (S₃'.eqn 0).Holds val := heq 0 (by decide)
    have he1 : (S₃'.eqn 1).Holds val := heq 1 (by decide)
    have ht0 : (S₃'.eqn 0).terms = {2, 3, 4} ∧ (S₃'.eqn 0).rhs = false := by decide
    have ht1 : (S₃'.eqn 1).terms = {0, 4, 5} ∧ (S₃'.eqn 1).rhs = false := by decide
    unfold Equation.Holds at he0 he1
    rw [ht0.1, ht0.2, Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at he0
    rw [ht1.1, ht1.2, Finset.sum_insert (by decide), Finset.sum_pair (by decide)] at he1
    rw [Finset.sum_insert (by decide), Finset.sum_pair (by decide)]
    revert he0 he1
    generalize val 0 = v0; generalize val 2 = v2; generalize val 3 = v3
    generalize val 4 = v4; generalize val 5 = v5
    revert v0 v2 v3 v4 v5; decide
  have hpis := h.pairInSystem_le hS₃
    (not_degPair_of_pairs (F := {0, 1}) (by decide) (by decide))
    (not_partnersShareChild_of (by decide))
    (pr := pr₀) (p := 0) (e := 1) (by decide) (by decide) (by decide) (by decide)
    (show S₃.out.arg ≠ .node 0 by decide)
    (Hr := .inl 6) (by decide) (by decide) (Q := 5) (c₀ := false) (T := {0, 2, 3})
    (by decide) haff (by decide)
  let S₄ : State 4 := (S₃'.swap 0 5 false {0, 2, 3}).dropEqn 1 0
  have h2 : S₂.gates.card = 5 ∧ S₂.eqns.card = 1 ∧ S₂.unpaired = {2, 3} ∧ S₂.pairs = {pr₀} ∧
      (S₂.gateChildren 2).card = 1 ∧ (S₂.eqnChildren 2).card = 1 ∧
      (S₂.gateChildren 3).card = 1 ∧ (S₂.eqnChildren 3).card = 1 ∧
      (S₂.gateChildren 0).card = 1 ∧ (S₂.eqnChildren 0).card = 0 ∧
      (S₂.gateChildren 1).card = 1 ∧ (S₂.eqnChildren 1).card = 0 := by decide
  have h3 : S₃.gates.card = 4 ∧ S₃.eqns.card = 2 ∧ S₃.unpaired = {2, 3} ∧ S₃.pairs = {pr₀} ∧
      (S₃.gateChildren 2).card = 1 ∧ (S₃.eqnChildren 2).card = 1 ∧
      (S₃.gateChildren 3).card = 1 ∧ (S₃.eqnChildren 3).card = 1 ∧
      (S₃.gateChildren 0).card = 0 ∧ (S₃.eqnChildren 0).card = 1 ∧
      (S₃.gateChildren 1).card = 1 ∧ (S₃.eqnChildren 1).card = 0 := by decide
  have h4 : S₄.gates.card = 3 ∧ S₄.eqns.card = 1 ∧ S₄.unpaired = {2, 3, 5} ∧ S₄.pairs = ∅ ∧
      S₃.a - S₄.a = 0 ∧
      (S₄.gateChildren 2).card = 1 ∧ (S₄.eqnChildren 2).card = 1 ∧
      (S₄.gateChildren 3).card = 1 ∧ (S₄.eqnChildren 3).card = 1 ∧
      (S₄.gateChildren 5).card = 2 ∧ (S₄.eqnChildren 5).card = 0 := by decide
  have he2 : stratifiedPotential ce w bp S₂ = 5 + ce + 2 * w 1 1 + bp 1 0 1 0 := by
    rcases h2 with ⟨hg, he, hu, hp, c2, e2, c3, e3, c0, e0, c1, e1⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_singleton,
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), pr₀, c2, e2, c3, e3, c0, e0, c1, e1]; ring
  have he3 : stratifiedPotential ce w bp S₃ = 4 + 2 * ce + 2 * w 1 1 + bp 0 1 1 0 := by
    rcases h3 with ⟨hg, he, hu, hp, c2, e2, c3, e3, c0, e0, c1, e1⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_singleton,
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3), pr₀, c2, e2, c3, e3, c0, e0, c1, e1]; ring
  have he4 : stratifiedPotential ce w bp S₄ = 3 + ce + 2 * w 1 1 + w 2 0 := by
    rcases h4 with ⟨hg, he, hu, hp, -, c2, e2, c3, e3, c5, e5⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_empty,
      Finset.sum_insert (by decide : (2 : ℕ) ∉ ({3, 5} : Finset ℕ)),
      Finset.sum_pair (by decide : (3 : ℕ) ≠ 5), c2, e2, c3, e3, c5, e5]; ring
  change stratifiedPotential ce w bp S₃ ≤ _ at hmov
  change stratifiedPotential ce w bp S₄ + c * ((S₃.a - S₄.a : ℕ) : ℚ) ≤ _ at hpis
  rw [he4, he3, h4.2.2.2.2.1] at hpis
  exact ⟨by linarith, by norm_num at hpis; linarith⟩

/-- `4`-input, `3`-gate opposite-bias paired Case 5a witness (`c ≤ 2 * bp 1 0 1 0 + 3`). -/
private def aopWitnessState : State 4 :=
  mkBaseState 4 {4, 5, 6}
    (fun j =>
      if j = 4 then ⟨(· && ·), .node 0, .node 2⟩
      else if j = 5 then ⟨(· && ·), .node 1, .node 3⟩
      else ⟨(· && ·), .node 4, .node 5⟩)
    ⟨.node 6, false⟩

private theorem aopWitness_bound {ce : ℚ} {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ}
    {c w_init : ℚ} (h : StratifiedStepSound ce w bp c w_init) :
    c ≤ 2 * bp 1 0 1 0 + 3 := by
  let S₀ := aopWitnessState
  obtain ⟨_, hS₀⟩ := exists_valid_of_baseStateOK S₀ rfl rfl rfl rfl rfl (by decide)
  let pr₁ : ZeroPair := ⟨0, false, 1, false⟩
  let pr₂ : ZeroPair := ⟨2, true, 3, false⟩
  let S₁ : State 4 := S₀.addPair pr₁
  let S₂ : State 4 := S₁.addPair pr₂
  have hS₂ : S₂.Valid _ := State.Valid.addPair
    (State.Valid.addPair hS₀ ⟨by decide, by decide, by decide⟩)
    ⟨by decide, by decide, by decide⟩
  have haop := h.andOnPair_le hS₂
    (not_degPair_of_pairs (F := {0, 1, 2, 3}) (by decide) (by decide))
    (not_partnersShareChild_of (by decide))
    (G := 4) (p := 0) (w₀ := 2) (pr := pr₁) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (prw := some pr₂) (fun h' => nomatch h')
    (fun _ hq => Option.some_injective _ hq ▸ ⟨by decide, by decide⟩) (b := false) (c₀ := false)
    (fun val hw => by change (val 0 && val 2) = false; rw [hw, Bool.and_false])
    (Hr := .inl 5) (Hw' := .inl 5) (K := 6) (by decide)
    (fun _ _ _ => ⟨by decide, by decide⟩) (fun _ hq _ => Option.some_injective _ hq ▸ by decide)
  let S₃ : State 4 := S₂.andOnPairStep 4 pr₁ 0 2 (some pr₂) false false (.inl 5) 6 (.inl 5)
  have hpne : pr₁ ≠ pr₂ := by decide
  have h2 : S₂.gates.card = 3 ∧ S₂.eqns.card = 0 ∧ S₂.unpaired = ∅ ∧ S₂.pairs = {pr₁, pr₂} ∧
      (S₂.gateChildren 0).card = 1 ∧ (S₂.eqnChildren 0).card = 0 ∧
      (S₂.gateChildren 1).card = 1 ∧ (S₂.eqnChildren 1).card = 0 ∧
      (S₂.gateChildren 2).card = 1 ∧ (S₂.eqnChildren 2).card = 0 ∧
      (S₂.gateChildren 3).card = 1 ∧ (S₂.eqnChildren 3).card = 0 := by decide
  have h3 : S₃.gates.card = 0 ∧ S₃.eqns.card = 0 ∧ S₃.unpaired = {0} ∧ S₃.pairs = ∅ ∧
      S₂.a - S₃.a = 1 ∧ (S₃.gateChildren 0).card = 0 ∧ (S₃.eqnChildren 0).card = 0 := by decide
  have he2 : stratifiedPotential ce w bp S₂ = 3 + 2 * bp 1 0 1 0 := by
    rcases h2 with ⟨hg, he, hu, hp, c0, e0, c1, e1, c2, e2, c3, e3⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_empty, Finset.sum_pair hpne,
      pr₁, pr₂, c0, e0, c1, e1, c2, e2, c3, e3]; ring
  have he3 : stratifiedPotential ce w bp S₃ = 0 := by
    rcases h3 with ⟨hg, he, hu, hp, -, c0, e0⟩
    simp only [stratifiedPotential, hg, he, hu, hp, Finset.sum_empty, Finset.sum_singleton,
      c0, e0, h.w_zero]; ring
  change stratifiedPotential ce w bp S₃ + c * ((S₂.a - S₃.a : ℕ) : ℚ) ≤ _ at haop
  rw [he3, he2, h3.2.2.2.2.1] at haop
  norm_num at haop
  linarith

/-- **Original `State`-grounded bigraded Farkas `4n` barrier**: for any bigraded potential
`(ce, w, bp)` sound across the `AffineDisperser4n` state transitions (`StratifiedStepSound`),
the leading coefficient `c - w_init` is at most `4`. -/
theorem stratified_weight_sub_le_four {ce : ℚ} {w : ℕ → ℕ → ℚ} {bp : ℕ → ℕ → ℕ → ℕ → ℚ}
    {c w_init : ℚ} (h : StratifiedStepSound ce w bp c w_init) :
    c - w_init ≤ 4 := by
  obtain ⟨h_init, h_pc⟩ := fanout2_bounds h
  obtain ⟨h_move_pa, h_pis⟩ := farkasCycle_bounds h
  linarith

/-- **Original `State`-grounded Pareto-optimality of `(ce, β, w_init, c) = (1, 3, 5, 9)`**: in any
bigraded potential satisfying `StratifiedStepSound` and attaining `c - w_init = 4`, concrete valid
`State` transitions force `ce = 1`, `3 ≤ bp 1 0 1 0`, `bp 0 1 1 0 = bp 1 0 1 0`, `5 ≤ w 2 0`,
`5 ≤ w_init`, `9 ≤ c`, and `w 2 0 = bp 1 0 1 0 + 2`. -/
theorem stratified_weight_lower_bounds_of_sub_eq_four {ce : ℚ} {w : ℕ → ℕ → ℚ}
    {bp : ℕ → ℕ → ℕ → ℕ → ℚ} {c w_init : ℚ}
    (h : StratifiedStepSound ce w bp c w_init) (h_opt : c - w_init = 4) :
    ce = 1 ∧ 3 ≤ bp 1 0 1 0 ∧ bp 0 1 1 0 = bp 1 0 1 0 ∧ 5 ≤ w 2 0 ∧ 5 ≤ w_init ∧ 9 ≤ c ∧
      w 2 0 = bp 1 0 1 0 + 2 := by
  obtain ⟨h_init, h_pc⟩ := fanout2_bounds h
  have h_ce := auxAux_ce_le_one h
  have h_pp := pairedPaired_bound h
  obtain ⟨h_pa, h_pis⟩ := farkasCycle_bounds h
  have h_aop := aopWitness_bound h
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
    by linarith⟩

/-! ### Explicit `4N - O(N / log N)` lower bounds for `explicitDisperser` -/

private theorem four_mul_le_cost_add_explicitThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (explicitDisperser N))) :
    4 * N ≤ C.program.cost binaryB2Cost + 9 * (explicitThreshold N + 1) :=
  four_mul_le_cost_add (isAffineDisperser_explicitDisperser N) C hC

/-- Asymptotic natural-number binary-gate lower bound for `explicitDisperser N`:
eventually `4 * N ≤ C.program.cost binaryB2Cost + 54 * N / (Nat.log 2 N + 1) + 9`. -/
theorem eventually_four_mul_le_cost_add_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * N ≤ C.program.cost binaryB2Cost + 54 * N / (Nat.log 2 N + 1) + 9 := by
  filter_upwards [eventually_explicitThreshold_le] with N hth C hC
  have hlb := four_mul_le_cost_add_explicitThreshold C hC
  have hdiv : explicitThreshold N ≤ 6 * N / (Nat.log 2 N + 1) :=
    Nat.le_div_iff_mul_le (Nat.succ_pos _) |>.2 (by linarith)
  have hmul : 9 * (6 * N / (Nat.log 2 N + 1)) ≤ 54 * N / (Nat.log 2 N + 1) := by
    rw [Nat.le_div_iff_mul_le (Nat.succ_pos _)]
    have := Nat.div_mul_le_self (6 * N) (Nat.log 2 N + 1)
    calc
      9 * (6 * N / (Nat.log 2 N + 1)) * (Nat.log 2 N + 1)
        = 9 * ((6 * N / (Nat.log 2 N + 1)) * (Nat.log 2 N + 1)) := by ring
      _ ≤ 9 * (6 * N) := Nat.mul_le_mul_left 9 this
      _ = 54 * N := by ring
  omega

/-- Asymptotic natural-number size lower bound for `explicitDisperser N`:
eventually `4 * N ≤ C.size + 54 * N / (Nat.log 2 N + 1) + 9`. -/
theorem eventually_four_mul_le_size_add_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * N ≤ C.size + 54 * N / (Nat.log 2 N + 1) + 9 := by
  filter_upwards [eventually_four_mul_le_cost_add_explicitDisperser] with N hN C hC
  have := hN C hC
  have := cost_binaryB2Cost_le_size C
  omega

private theorem eventually_four_mul_sub_le_cost_of_computes_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤
        (C.program.cost binaryB2Cost : ℝ) := by
  filter_upwards [eventually_four_mul_le_cost_add_explicitDisperser] with N hN C hC
  have hdiv : ((54 * N / (Nat.log 2 N + 1) : ℕ) : ℝ) ≤
      54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) := by
    simpa [Nat.cast_add, Nat.cast_mul] using
      (Nat.cast_div_le (α := ℝ) (m := 54 * N) (n := Nat.log 2 N + 1))
  cast_linarith [hN C hC]

private theorem eventually_four_mul_sub_le_size_of_computes_explicitDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (explicitDisperser N)) →
      4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤ (C.size : ℝ) := by
  filter_upwards [eventually_four_mul_sub_le_cost_of_computes_explicitDisperser] with N hN C hC
  cast_linarith [cost_binaryB2Cost_le_size C, hN C hC]

/-- There exists an explicit language in `P` (`explicitDisperserLanguage`) whose `N`-bit slices
require at least `4 * N - 54 * N / (Nat.log 2 N + 1) - 9` genuinely binary `B₂` gates. -/
theorem exists_mem_P_eventually_four_mul_sub_le_cost :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤
          (C.program.cost binaryB2Cost : ℝ) := by
  refine ⟨explicitDisperserLanguage, explicitDisperserLanguage_mem_P, ?_⟩
  filter_upwards [eventually_four_mul_sub_le_cost_of_computes_explicitDisperser] with N hN C hC
  rw [slice_explicitDisperserLanguage] at hC
  exact hN C hC

/-- There exists an explicit language in `P` (`explicitDisperserLanguage`) whose `N`-bit slices
require Boolean circuits of size at least `4 * N - 54 * N / (Nat.log 2 N + 1) - 9`. -/
theorem exists_mem_P_eventually_four_mul_sub_le_size :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 54 * (N : ℝ) / ((Nat.log 2 N : ℝ) + 1) - 9 ≤ (C.size : ℝ) := by
  refine ⟨explicitDisperserLanguage, explicitDisperserLanguage_mem_P, ?_⟩
  filter_upwards [eventually_four_mul_sub_le_size_of_computes_explicitDisperser] with N hN C hC
  rw [slice_explicitDisperserLanguage] at hC
  exact hN C hC

/-! ### Unconditional `4N - O(N ^ (4 / 5))` lower bounds in `P` via `Li.primeDisperser` -/

private theorem four_mul_le_cost_add_primeThreshold {N : ℕ}
    (C : Circuit (fullSignature 2 Bool) N 1)
    (hC : C.Computes fullInterpretation (single (Li.primeDisperser N))) :
    4 * N ≤ C.program.cost binaryB2Cost + 9 * (Li.primeThreshold N + 1) :=
  four_mul_le_cost_add (Li.isAffineDisperser_primeDisperser N) C hC

private theorem eventually_four_mul_sub_le_cost_of_computes_primeDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (Li.primeDisperser N)) →
      4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.program.cost binaryB2Cost : ℝ) := by
  filter_upwards [Li.eventually_primeThreshold_real_le] with N hleR C hC
  have hnatR : (4 : ℝ) * (N : ℝ) ≤
      (C.program.cost binaryB2Cost : ℝ) + 9 * ((Li.primeThreshold N + 1 : ℕ) : ℝ) := by
    exact_mod_cast four_mul_le_cost_add_primeThreshold C hC
  linarith

private theorem eventually_four_mul_sub_le_size_of_computes_primeDisperser :
    ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
      C.Computes fullInterpretation (single (Li.primeDisperser N)) →
      4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ) := by
  filter_upwards [eventually_four_mul_sub_le_cost_of_computes_primeDisperser] with N hN C hC
  cast_linarith [cost_binaryB2Cost_le_size C, hN C hC]

/-- Unconditional explicit language in `P` (`Li.primeDisperserLanguage`) whose `N`-bit slices
eventually require at least `4 * N - 19332 * N ^ (4 / 5)` genuinely binary `B₂` gates
(`binaryB2Cost`, with constants and unary negations free). -/
theorem exists_mem_P_eventually_le_cost_primeDisperser :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.program.cost binaryB2Cost : ℝ) :=
  ⟨Li.primeDisperserLanguage, Li.primeDisperserLanguage_mem_P, by
    simpa only [Li.slice_primeDisperserLanguage] using
      eventually_four_mul_sub_le_cost_of_computes_primeDisperser⟩

/-- Unconditional explicit language in `P` (`Li.primeDisperserLanguage`) whose `N`-bit slices
eventually require Boolean circuits of total size at least `4 * N - 19332 * N ^ (4 / 5)`. -/
theorem exists_mem_P_eventually_le_size_primeDisperser :
    ∃ L : Language Bool, L ∈ P Turing.MultiTapeTM.encBits ∧
      ∀ᶠ N in atTop, ∀ (C : Circuit (fullSignature 2 Bool) N 1),
        C.Computes fullInterpretation (single (L.slice N)) →
        4 * (N : ℝ) - 19332 * (N : ℝ) ^ ((4 : ℝ) / 5) ≤ (C.size : ℝ) :=
  ⟨Li.primeDisperserLanguage, Li.primeDisperserLanguage_mem_P, by
    simpa only [Li.slice_primeDisperserLanguage] using
      eventually_four_mul_sub_le_size_of_computes_primeDisperser⟩

end Cslib.Circuits.Boolean.AffineDisperser4n
