# Cooperative games, cost sharing and Nash bargaining

The modules under `CslibFrontier/GameTheory/Cooperative/` formalize transferable-utility (TU)
cost-sharing and cooperative value games, linear-programming characterizations of the core,
group-strategyproof Moulin cost-sharing mechanisms, primal-dual water-filling on submodular games,
the Shapley value, and two-player Nash bargaining, following
[Jain and Mahdian](../sources.md#jainmahdian07), Chapter 15 (Sections 15.1–15.4.1, 15.6, and
Exercises 15.1–15.2), and [Tardos and Vazirani](../sources.md#tardosvazirani07), Section 1.7.2.
They are mathematical models of coalitional stability, incentives, and axiomatic fairness: cost
functions, sharing schemes, and bargaining operators are real-valued functions, and no machine
running time or oracle query count is charged.

## Transferable-utility games, approximate cores, and facility location

Import `CslibFrontier.GameTheory.Cooperative.Basic`. In `Cslib.GameTheory`, a finite-coalition
`CostSharingGame A` specifies `cost : Finset A → ℝ` normalized by `cost ∅ = 0`, carrying
`AddCommGroup` and `Module ℝ` structure (`0`, `+`, `-`, `•`, `∑`), while the dual
surplus model `CooperativeGame A` specifies `val : Finset A → ℝ` with `val ∅ = 0`. They convert
losslessly via `CostSharingGame.toCooperativeGame` and `CooperativeGame.toCostSharingGame`
(`val = -cost`), transferring core allocations under negation (`inCore_toCooperativeGame_iff`,
`inCore_toCostSharingGame_iff`).

- `G.IsCoreFeasible α` states coalitional stand-alone rationality `∀ S, ∑ j ∈ S, α j ≤ G.cost S`,
  and `G.IsCoreFeasibleOn T α` restricts this condition to subsets `S ⊆ T`.
- `G.InCore α` pairs exact budget balance `∑ j : A, α j = G.cost Finset.univ` with
  `G.IsCoreFeasible α` (Definition 15.3).
- `G.InApproxCore γ α` relaxes budget balance to
  `γ * G.cost Finset.univ ≤ ∑ j : A, α j ∧ ∑ j : A, α j ≤ G.cost Finset.univ` alongside exact
  coalitional rationality `G.IsCoreFeasible α` (Definition 15.7), matching `InCore` at `γ = 1`
  (`inApproxCore_one_iff`).
- `IsBalancedWeights w` asks for `0 ≤ w` and `∀ j : A, ∑ S with j ∈ S, w S = 1` (Definition 15.5).
  Weak duality (`InApproxCore.mul_le_sum_balanced`, `InCore.le_sum_balanced`) sums `w S` times
  coalitional rationality over all `S`.

`FacilityLocationInstance A F` models cooperative facility location (Definition 15.1), either via an
arbitrary nonnegative connection matrix (`openCost`, `connCost`) or induced from shortest-path or
metric distances on `A ⊕ F` via `FacilityLocationInstance.ofMetric`. For any nonempty coalition `S`,
`toCostSharingGame` takes the minimum over nonempty open facility subsets `F' ⊆ F` of
`planCost S F'` (opening costs plus per-agent nearest-open-facility connection costs).

- `FacilityLocationInstance.IsDualFeasible.isCoreFeasible` proves Proposition 15.10: any feasible
  solution `(α, β)` of the dual facility-location LP `(15.4)` makes `α` satisfy coalitional
  rationality, and therefore lies in the core whenever `∑ j, α j = c(univ)`.
- `example15_2` formalizes the 2-facility, 3-agent metric instance of Example 15.2, proving all
  seven coalition costs (`example15_2_cost`) and core membership of `![4, 2, 2]` and `![4, 1, 3]`.
- For Example 15.4's empty-core construction, the library separates a textbook subtlety: adding a
  third facility `f₃` with `f₃ = 3` and `d(f₃, a) = d(f₃, c) = 1` to Example 15.2 and re-closing
  shortest paths under the triangle inequality yields `d(f₂, a) ≤ 1 + 1 + 1 = 3`, dropping
  `c({a, b, c})` from `8` to `7`. `emptyCoreBipartiteFL` formalizes the literal bipartite table
  of Example 15.4, while `emptyCoreMetricFL` formalizes the genuine 6-vertex shortest-path metric on
  `K_{3,3} \ M` with opening costs `3`. Both have an empty `1`-core (proved via `[1/2, 1/2, 1/2]`
  balanced pair weights) and a tight `(15 / 16)`-core (`emptyCoreMetricFL_inApproxCore`,
  `emptyCoreMetricFL_not_nonemptyApproxCore_of_gt`).

## Bondareva–Shapley LP duality and linear exchange economies

Import `CslibFrontier.GameTheory.Cooperative.Core`. Using strong LP duality over linearly ordered
fields (`Matrix.exists_isGreatest_isLeast_dotProduct` in
`CslibFrontier/Foundations/LinearAlgebra/Matrix/LinearProgramming.lean`),
`CostSharingGame.exists_isGreatest_isLeast_coreLP` proves that the cost-recovery maximization LP
`(15.1)` (`max {∑ j, α j | G.IsCoreFeasible α}`) and the fractional balanced-weights minimization LP
`(15.2)` (`min {∑ S, w S * G.cost S | IsBalancedWeights w}`) both attain a common optimum `G.lpOpt`:

- `CostSharingGame.nonemptyCore_iff_balanced` and `CooperativeGame.nonemptyCore_iff_balanced` prove
  the Bondareva–Shapley theorem (Theorem 15.6): a cost-sharing game has a nonempty core iff
  `G.cost Finset.univ ≤ ∑ S, w S * G.cost S` for every balanced `w` (and dual inequality
  `∑ S, w S * G.val S ≤ G.val Finset.univ` for surplus games).
- `CostSharingGame.nonemptyApproxCore_iff_balanced` proves the `γ`-Bondareva–Shapley theorem
  (Theorem 15.8): `G.NonemptyApproxCore γ` holds iff `γ * G.cost Finset.univ ≤ ∑ S, w S * G.cost S`
  for every balanced `w`. Strong duality establishes this equivalence for every `γ : ℝ`, without
  requiring `γ ≤ 1`.
- For subadditive games (`G.IsSubadditive`), `IsSubadditive.isLeast_integralBalanced` shows that the
  minimum over `ℕ`-valued balanced weights (`IsIntegralBalancedWeights`, exact coalition partitions)
  equals `G.cost Finset.univ`, and `isGreatest_nonemptyApproxCore_integralityGapLP` proves
  Corollary 15.9: when `0 < G.cost Finset.univ`, `G.integralityGapLP = G.lpOpt / G.cost Finset.univ`
  is the greatest `γ` with a nonempty `γ`-core.

`LinearExchangeEconomy A G` formalizes Exercise 15.1: each agent `i : A` holds nonnegative initial
endowments `endowment i : G → ℝ` and nonnegative linear marginal utilities `utility i : G → ℝ`.
`coalitionValue` assigns each good's total coalitional supply to a coalition member with maximum
marginal utility for that good (`isGreatest_exactRedistribution`,
`isGreatest_feasibleRedistribution`). Pricing each good at its grand-coalition maximum marginal
utility and crediting each agent's initial endowment (`marketPriceAllocation`) produces an explicit
core allocation (`marketPriceAllocation_inCore`, `toCooperativeGame_nonemptyCore`).

## Cross-monotonic cost sharing, Moulin's mechanism, and submodular games

Import `CslibFrontier.GameTheory.Cooperative.MoulinCostSharing`. A `CostSharingScheme A` assigns a
vector `share S : A → ℝ` to every finite serviced coalition `S`, with `share S i = 0` for `i ∉ S`
(Definition 15.12).

- `ξ.IsBudgetBalanced G γ` requires `γ * G.cost S ≤ ∑ i ∈ S, ξ.share S i ≤ G.cost S` for every `S`
  (`isBudgetBalanced_one_iff` reduces `γ = 1` to exact equality).
- `ξ.IsCrossMonotone` requires `S ⊆ T → i ∈ S → ξ.share T i ≤ ξ.share S i` (Definition 15.13;
  `isCrossMonotone_iff_union` gives the `S ∪ T` form).
- `CostSharingScheme.inApproxCore_univ` and `inCore_univ` prove Proposition 15.14: if `ξ` is
  `γ`-budget-balanced and cross-monotone, `ξ.share Finset.univ` lies in the `γ`-core.

A binary-service sealed-bid `CostSharingMechanism A` chooses `serviced : (A → ℝ) → Finset A` and
`payment : (A → ℝ) → A → ℝ`, with quasilinear utility `(if i ∈ serviced b then u i else 0) -
payment b i` (`toSingleParameterMechanism` embeds it into `SingleParameter.Mechanism A`). Moulin's
iterative-pruning mechanism `ξ.moulinMechanism` (Figure 15.2) iterates
`ξ.moulinStep b S = S.filter (fun i => ξ.share S i ≤ b i)` for `Fintype.card A` rounds from
`Finset.univ` (`ξ.moulinServiced b`):

- `isGreatest_isWilling_moulinServiced` and `moulinServiced_eq_of_validPruning` prove
  Proposition 15.15: for cross-monotone `ξ`, `ξ.moulinServiced b` is the unique largest willing
  coalition `{S | ∀ i ∈ S, ξ.share S i ≤ b i}`, and any asynchronous valid pruning sequence
  (`ValidPruningStep`) terminating at a willing coalition reaches the same set.
- `moulinMechanism_isGroupStrategyproof`, `moulinMechanism_isBudgetBalanced`,
  `moulinMechanism_voluntaryParticipation`, `moulinMechanism_consumerSovereignty`, and
  `moulinMechanism_noPositiveTransfers` prove Theorem 15.16 (Moulin 1999): if `ξ` is cross-monotone
  and `γ`-budget-balanced (with nonnegative shares for NPT), `ξ.moulinMechanism` satisfies VP, CS,
  NPT, `γ`-budget balance, and group-strategyproofness (`IsGroupStrategyproof`, equivalent to ruling
  out weakly-better-for-all, strictly-better-for-one coalitional misreports `C.piecewise z u` via
  `isGroupStrategyproof_iff_not_beneficial`, and implying `SingleParameter.Mechanism.IsDSIC` via
  `IsGroupStrategyproof.isDSIC`).

`CostSharingGame.IsSubmodular` reuses `Cslib.Algorithms.Lean.Submodular.IsSubmodular G.cost`
(Definition 15.17). Under core feasibility on `T`, tight coalitions (`G.IsTight α S`, meaning
`∑ j ∈ S, α j = G.cost S`) are closed under union (`IsTight.union`, Lemma 15.18), giving a unique
greatest tight subset `G.maximalTightSet T α` (`isGreatest_maximalTightSet`, Corollary 15.19).
`G.submodularCostShare T` and `G.submodularCostShareScheme` implement the Dutta–Ray / Jain–Vazirani
primal-dual water-filling algorithm `SubmodularCostShare` (Figure 15.3) over `T.card` freeze steps,
and `submodularCostShareScheme_isCrossMonotone`, `submodularCostShareScheme_isBudgetBalanced`, and
`submodularCostShareScheme_isNonneg` prove Theorem 15.20. Submodular minimization runtime for each
freeze threshold is not modeled.

## The Shapley value and Nash bargaining

Import `CslibFrontier.GameTheory.Cooperative.ShapleyValue`.

- `shapleyValue G i` sums `shapleyWeight (Fintype.card A) S.card * (G.cost (insert i S) - G.cost S)`
  over `S ∈ (Finset.univ.erase i).powerset`, with `shapleyValue_eq_sum_card` grouping by subset
  size and `shapleyValue_eq_permShapleyValue` equating it to the uniform average `permShapleyValue`
  over all `Fin (Fintype.card A) ≃ A` agent orderings ([Tardos and Vazirani](../sources.md#tardosvazirani07),
  Example 1.14).
- `example15_24_shapleyValue` and `example15_24_not_inCore` evaluate Example 15.24 to
  `(23 / 6, 11 / 6, 7 / 3)` on `example15_2`, which violates `{b, c}`'s stand-alone bound
  `25 / 6 > 4` despite the core being nonempty.
- `eq_shapleyValue_of_axioms` and `existsUnique_shapleyValue` prove Shapley's uniqueness theorem
  (Theorem 15.26) over the `2^|A| - 1` scaled unanimity-game basis (`unanimityGame`,
  `eq_sum_unanimityGame`): `shapleyValue` is the unique operator satisfying `IsEfficientValue`,
  `IsSymmetricValue` (or `IsAnonymousValue`, Definition 15.25), `SatisfiesDummy`, and
  `IsAdditiveValue`, without assuming homogeneity or nonnegativity. Two source conventions from
  Definition 15.25 (p. 404) are made explicit: Efficiency (`∑ i, φ G i = G.cost univ`) is stated as
  an explicit hypothesis rather than left implicit in the prose definition of a cost allocation, and
  `IsDummyAgent` quantifies over all `S ⊆ A \ {i}` (`i ∉ S`) rather than the typographical strict
  subset `S ⊂ A \ {i}`.
- `CostSharingGame.shapleyScheme` restricts `shapleyValue` to each coalition `T` (`G.restrict T`),
  and `IsSubmodular.shapleyScheme_isCrossMonotone`, `IsSubmodular.shapleyValue_inCore`, and
  `IsSubmodular.moulinMechanism_shapleyScheme_isGroupStrategyproof` prove Exercise 15.2.

`BargainingProblem` models Nash's two-player bargaining problem (Section 15.6.3, pp. 404–405) as a
compact, convex set `feasible : Set (ℝ × ℝ)` containing `disagreement ∈ feasible` and at least one
strictly individually rational outcome `x` with `disagreement.1 < x.1 ∧ disagreement.2 < x.2`
(comprehensiveness is not needed). `nashBargainingSolution B` maximizes
`B.nashProduct x = (x.1 - d.1) * (x.2 - d.2)` over `B.individuallyRational`
(`isGreatest_nashBargainingSolution`), and strict midpoint concavity makes the maximizer unique
(`nashBargainingSolution_unique_maximizer`). `eq_nashBargainingSolution_of_axioms`,
`existsUnique_nashBargainingSolution`, and `existsUnique_nashBargainingSolution_paretoOptimal` prove
Theorem 15.28: `nashBargainingSolution` is the unique `IsBargainingSolution` satisfying
`IsWeaklyParetoOptimal` (Definition 15.27's coordinate-wise `p > φ(X)`, or strong
`IsParetoOptimal`), `IsSymmetricBargaining`, `IsScaleInvariant` (positive affine rescaling
`u_i ↦ a_i u_i + b_i` for `a_i > 0`, combining Section 15.6.3's translation normalization to
`d = (0, 0)` with Definition 15.27's scale independence), and `SatisfiesIIA`.
