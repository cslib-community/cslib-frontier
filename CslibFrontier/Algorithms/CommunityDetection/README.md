# Exact recovery in the two-community stochastic block model

This development proves dense-regime exact recovery by a native polynomial-time program.
For every fixed pair of probabilities $0\le q<p\le1$, one program recovers all hidden community
labels, up to a global swap, with probability tending to one. The communities need not have
equal sizes. The same program works under every sequence of priors on the hidden labels.

The executable algorithm constructs an integer centered adjacency matrix, searches its power
columns, rounds their signs, and performs one weighted vote cleanup. Its native certificate
accounts for the bit lengths of all intermediate integers. Two fixed integer constants
approximate the needed real centering; arbitrary real $p,q$ are allowed in the theorem.

A companion mathematical algorithm uses Mathlib's exact leading eigenvector and the same
rounding and cleanup analysis. Both algorithms have complete probability guarantees. The
integer-power algorithm carries the native computational certificate.

## 1. Model and formalized theorems

Write a labeling as $g\in\{-1,1\}^n$. Conditional on $g$, each unordered pair of distinct
vertices is an independent edge, with probability $p$ if its labels agree and $q$ otherwise.
There are no self-loops. The parameters $p,q$ are known to the solver; the labels are hidden.

In Lean, labels have type `Fin n → Bool`. The existing `BitString.signVal` reads `false` as
$+1$ and `true` as $-1$. The product PMF `coinLaw` draws independent Bernoulli bits indexed by
ordered pairs, and `sample` reads only the strict upper triangle. Unused bits do not affect
the observed graph.

[Model.lean](../../Probability/StochasticBlockModel/Model.lean) defines the experiment through
the existing `DistributionalSearchProblem` interface:

- `Instance` stores the latent `labels` and observed `graph` in named fields.
- `instanceDistribution` first draws the labels from a supplied prior, then draws their graph.
- `searchProblem.observe` gives the solver only the graph.
- Acceptance is `answer = state.labels ∨ answer = fun i => !state.labels i`.

The theorem `graphLaw_not` proves that swapping every hidden label leaves the graph law
unchanged. Thus the global-swap equivalence in the success relation matches the statistical
symmetry of the problem. There is no requirement that either label class be nonempty; the
two named labels describe a partition into at most two parts.

### Main computational theorem

For each fixed $p>q$, there are fixed natural parameters $D,c$ such that the actual function
`recoverInput ⟨D,c⟩` is polynomial-time on every encoded dense graph and succeeds with failure
tending to zero under every family of label priors. The parameters and the machine are chosen
before the graph size and label prior vary.

The exported statement in [PolyTime.lean](PolyTime.lean) is:

```lean
open scoped Classical in
theorem exists_recoverInput_ppt_tendsto_failure (p q : I) (hpq : (q : ℝ) < p) :
    ∃ params : PowerParameters,
      IsPPTOn encDenseGraphInput (encList encBool)
        (fun x => pure (recoverInput params x)) ∧
      ∀ prior : ∀ n, PMF (Fin n → Bool),
        Tendsto (fun n => (searchProblem p q (prior n)).experiment
          (fun G => PMF.pure (fun i : Fin n =>
            (recoverInput params (DenseGraphInput.ofGraph G)).getD i.val false)) false)
          atTop (𝓝 0)
```

`IsPPTOn` is the existing strict, native multitape machine predicate. This solver is
deterministic; its realization in that predicate ignores the available random bits. The input
contains the graph and its dimension. The hidden labels and an arbitrary prior remain solely
in the statistical experiment.

The word representation is explicit: `encDenseGraphInput` frames the unary vertex count and
appends raw adjacency bits. A canonical graph uses exactly $n^2+2n+1$ input bits. The output
encoding `encList encBool` frames a list of exactly $n$ Boolean labels. `ofGraph` and the indexed
output reads specify the meanings of these representations.

### Companion exact-eigenvector theorem

Let $\mathcal A_{p,q}$ be `recoverSpectral p q`. For every fixed $p>q$ and every family of
label priors $(\pi_n)$,

$$
\Pr_{g\sim\pi_n,\;G\sim\mathrm{SBM}(g,p,q)}
\left[\mathcal A_{p,q}(G)\notin\{g,-g\}\right]\longrightarrow0.
$$

The exported theorem in [Asymptotics.lean](Asymptotics.lean) has the following signature.
The excerpt uses the namespaces opened in that module and omits the proof body.

```lean
open scoped Classical in
theorem tendsto_searchProblem_recoverSpectral_failure (p q : I)
    (prior : ∀ n, PMF (Fin n → Bool)) (hpq : (q : ℝ) < p) :
    Tendsto (fun n => (searchProblem p q (prior n)).experiment
      (fun G => PMF.pure (recoverSpectral p q G)) false) atTop (𝓝 0)
```

The expression tending to zero is the actual `ℝ≥0∞` failure mass of the search experiment.
The proof first bounds its real-valued form and then uses the finiteness of PMF masses to
transfer the limit back. The prior may vary with $n$ and is not restricted to uniform or
balanced labelings.

### Explicit finite guarantee

Set

$$
d=\frac{p-q}{2}>0.
$$

If $d^3n>41472$, the same solver satisfies

$$
\Pr\left[\mathcal A_{p,q}(G)\notin\{g,-g\}\right]
\le 2e^{-n}+2n\exp\!\left(-\frac{d^2n}{8}\right).
$$

The bound holds for each fixed labeling and, by averaging, under every prior. The exported
arbitrary-prior statement in [Final.lean](Final.lean) is:

```lean
open scoped Classical in
theorem searchProblem_recoverSpectral_failure_le (p q : I)
    (prior : PMF (Fin n → Bool)) (hpq : (q : ℝ) < p)
    (hsize : 41472 < (gap p q) ^ 3 * (n : ℝ)) :
    ((searchProblem p q prior).experiment
      (fun G => PMF.pure (recoverSpectral p q G)) false).toReal ≤
        2 * exp (-(n : ℝ)) +
          2 * n * exp (-(gap p q) ^ 2 * n / 8)
```

These are conservative sufficient conditions, not optimized constants. The checked client
[CommunityDetection.lean](../../../CslibFrontierTests/CommunityDetection.lean) applies this
theorem at $p=3/4$, $q=1/4$, $n=3{,}000{,}000$, where $d^3n=46{,}875>41{,}472$.
That client checks a theorem application; it does not execute an eigensolver on that graph.

## 2. Relation to the paper literature

The reference is Frank McSherry,
[**Spectral Partitioning of Random Graphs**](https://static.aminer.org/pdf/PDF/000/211/400/spectral_partitioning_of_random_graphs.pdf),
FOCS 2001, pp. 529–537, DOI [10.1109/SFCS.2001.959929](https://doi.org/10.1109/SFCS.2001.959929),
bibliography key `McSherry2001`. Locators refer to sections in the linked paper.

| Paper location | Relationship to this development |
|---|---|
| §1.1, graph partition model and planted partition problem | Independent edges depend on latent classes; success recovers the induced partition. Here there are two classes, equal within-class probabilities, and known parameters. |
| §1.2, spectral approach and `Partition` | Shared principle: recover low-rank structure despite random adjacency noise. The paper splits columns and clusters projected columns; this development centers to rank one, rounds a leading eigenvector, and cleans up by votes. |
| §2.4, Theorem 10 | Both analyses control the noise operator norm. The formal proof here uses an elementary finite-net bound $36\sqrt n$, without the paper's variance-sensitive estimate. |

This is an original conservative dense-regime analysis of the specified algorithm, not a
formalization of McSherry's full theorem or its parameter range. His notation uses $q$ for
within-community probability and $p$ for between-community probability, opposite to ours.

## 3. Algorithm and its Lean representation

Let $A$ be the adjacency matrix, $J$ the all-ones matrix, and $I$ the identity. Put
$m=(p+q)/2$ and $d=(p-q)/2$.

### Step 1: center and shift

Construct

$$
M=A-m(J-I)+dI.
$$

For $i\ne j$, the expected adjacency entry is $m+d g_i g_j$. The diagonal of $A$ is zero,
so the scalar diagonal correction gives the exact identity

$$
M=dgg^\top+N,\qquad \mathbb E[N\mid g]=0.
$$

`centeredAdjacency` and `shiftedCenteredAdjacency` define these matrices. The theorem
`shiftedCenteredAdjacency_sample` proves the decomposition entry by entry, and
`sum_sample_adjMatrix` proves the expected adjacency entries using the product PMF.
`noise` is represented by independent upper-triangular centered entries plus their transpose.

Centering removes the all-ones component without assuming $g$ is orthogonal to it. This is
why the proof works for unequal community sizes. The diagonal correction also makes every
true-label vote have mean exactly $dn$, including its diagonal contribution.

### Step 2: take a leading eigenvector

Choose a unit eigenvector $v$ for the largest algebraic eigenvalue of $M$.
`leadingEigenvector` uses Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis` with index zero
and its decreasingly ordered spectrum. It does not use an arbitrary enumeration of matrix
eigenvalues. The empty graph has a specified zero-vector fallback.

The hidden unit direction is

$$
u=\frac{g}{\sqrt n}.
$$

The existing `BitString.signWord` embeds the labels into Euclidean space, and Mathlib's
`NormedSpace.normalize` supplies the normalization. There is no separate community-specific
normalization definition.

### Step 3: round coordinates

Set $h_i=-1$ when $v_i<0$, and $h_i=+1$ otherwise. Ties go to $+1$.
`spectralLabels` applies the existing `BitString.signRound`, generalized from Boolean-cube
domains to arbitrary finite coordinate types.

If $v_i$ has the wrong sign relative to $s g_i/\sqrt n$, for $s\in\{-1,1\}$, that coordinate
contributes at least $1/n$ to the squared Euclidean error. Thus

$$
\operatorname{Ham}(h,sg)\le n\|v-su\|^2.
$$

The shared scaled rounding lemma proves this coordinate argument, and
`hammingDist_signRound_le_card_mul_norm_sub_sq` supplies its Euclidean form. The theorem
`spectralLabels_errors` accounts for the eigenvector's arbitrary global sign by choosing
between the original labeling and its global complement.

### Step 4: clean up by a weighted vote

For every vertex, compute

$$
z_i=\sum_j M_{ij}h_j,
\qquad \widehat g_i=\operatorname{sign}(z_i),
$$

with the same zero-tie convention. This is `cleanup M h` in
[Cleanup.lean](Cleanup.lean). `recoverSpectral` composes the three mathematical operations:
matrix construction, spectral sign rounding, and cleanup.

Every entry of $M$ has absolute value at most one. If $h$ makes $b$ errors relative to a chosen
orientation of the true labels, changing those labels changes any row vote by at most $2b$.
Consequently,

$$
g_i\sum_j M_{ij}g_j>2b\quad\text{for every }i
\quad\Longrightarrow\quad
\operatorname{cleanup}(M,h)=g.
$$

`cleanup_eq_of_margin` proves this deterministic implication. It permits $h$ to depend on
$M$. The probability argument therefore needs concentration only for votes against the
fixed true labeling, not an independence assumption about the estimated labels. The margin
is unchanged when both occurrences of $g$ are globally negated, so the cleanup respects the
success relation on every event used by the proof.

## 4. Completing the probability proof

Two bad events account for the displayed failure probability.

**Noise event.** The shared independent-entry theorem proves

$$
\Pr[\|N\|>36\sqrt n]\le 2e^{-n}.
$$

For fixed unit-ball vectors, the bilinear form is a weighted sum of independent centered
edge scores. Existing bounded-differences concentration bounds that sum. Two half-nets,
each with at most $5^n$ elements, turn the bilinear estimates into an operator-norm bound.
[RandomMatrix.lean](../../Probability/StochasticBlockModel/RandomMatrix.lean) applies that
generic result to the actual biased Bernoulli coins of the SBM.

**Margin event.** For every fixed true labeling,

$$
\Pr\!\left[\exists i:\;
g_i\sum_j M_{ij}g_j\le\frac{dn}{2}\right]
\le 2n\exp\!\left(-\frac{d^2n}{8}\right).
$$

[Concentration.lean](../../Probability/StochasticBlockModel/Concentration.lean) expresses a
centered row margin as a weighted sum of independent edge scores, bounds the sum of squared
weights by $n$, and applies a union bound over vertices. Shared edges make different rows
dependent, but the union bound needs no independence between rows.

On the complement of the noise event, the new rank-one perturbation lemma gives

$$
\min_{s\in\{-1,1\}}\|v-su\|^2
\le 8\left(\frac{36\sqrt n}{dn}\right)^2.
$$

Its proof uses the Rayleigh quotient to show that the leading eigenvalue is at least
$dn-\|N\|\ge dn/2$, then applies the eigen-equation to bound distance from the signal line.
The existing geometric sign lemma turns distance from that line into distance from one of
its two unit directions. No caller-supplied spectral-gap hypothesis is left in the result.

Rounding therefore makes at most $10368/d^2$ errors. Cleanup succeeds whenever

$$
\frac{20736}{d^2}<\frac{dn}{2},
\quad\text{equivalently}\quad d^3n>41472.
$$

Because $0<d\le1/2$, the same size condition implies the required spectral separation
$72\sqrt n\le dn$. The private arithmetic lemma `dense_parameters` checks both implications.
`coinLaw_recoverSpectral_failure_le` puts the failure event inside the union of the two bad
events. `searchProblem_failure_le_of_fixedLabels` then averages the conditional result over
any supplied prior.

For fixed $d>0$, the size condition eventually holds and both exponential terms tend to zero.
[Recovery.lean](../../Probability/StochasticBlockModel/Recovery.lean) shares the noise/margin
union bound and the final exponential-decay argument between the exact-eigenvector and integer
program proofs. [Asymptotics.lean](Asymptotics.lean) supplies the eigenvector algorithm's
eventual deterministic size condition.

## 5. Integer-power implementation and its computational certificate

### Fixed finite parameters

For $d=(p-q)/2>0$, choose a positive natural $D$ with $Dd\ge32$, and put

$$
c=\left\lfloor D^2m\right\rfloor,\qquad m=\frac{p+q}{2}.
$$

Lean uses the Archimedean property to choose $D$ and Mathlib's natural-floor lemmas to prove
$0\le c\le D^2$ and $|D^2m-c|\le1$. Only these two finite naturals are stored in the program's
`PowerParameters`. Their existence is proved for each fixed real pair $p>q$; no rationality or
computable-real representation is required of that pair.

### Exact integer computation

[Algorithm.lean](Algorithm.lean) specifies the symmetric integer matrix

$$
B_{ii}=0,\qquad B_{ij}=D^2A_{ij}-c\quad(i\ne j).
$$

For every standard-basis seed $e_i$ and each $0\le t\le n$, the algorithm considers
$y=B^te_i$ and $z=B^{t+1}e_i$. It takes the first pair satisfying

$$
0<\|z\|^2,\qquad (Dn)^2\|y\|^2\le4\|z\|^2.
$$

Both tests use integer sums and products. The returned vector is rounded by comparing each
coordinate with zero; zero has sign $+1$. One multiplication by $B$ computes the cleanup
votes, whose signs give the output. If the search finds no pair, its specified vector is zero.

The common [integer-power modules](../IntegerPower/Basic.lean) supply the enumeration,
[search-existence proof](../IntegerPower/Search.lean),
[quantitative alignment theorem](../IntegerPower/Approximation.lean), and
[stored native program](../IntegerPower/Program.lean). Planted-clique recovery now consumes the
same implementation and proof. [Program.lean](Program.lean) constructs the community matrix
and performs the two sign decisions and cleanup with binary integer arithmetic.

The exact bridge `recoverInput_eq_ofFn` proves equality of the complete output list with
`List.ofFn (recoverPower params x.graph)` on every dense input. It covers short or asymmetric
adjacency words, empty graphs, ties at zero, and the search fallback. `recoverInput_ofGraph`
specializes this to the canonical presentation used in the statistical theorem.

### Why the approximation still recovers every label

The centering calculation in [IntegerCentering.lean](IntegerCentering.lean) gives

$$
B=D^2M+(D^2m-c)J+(c-D^2p)I.
$$

The two extra terms contribute at most $n+D^2$ to the operator bound and to the change in
each true-label row margin. On the old noise event, the total residual from the rank-one signal
is therefore at most

$$
R=36D^2\sqrt n+n+D^2.
$$

[PowerAnalysis.lean](PowerAnalysis.lean) proves correctness whenever
$R\le(d/16)Dn$ and the true-label margins exceed $dn/2$. The shared power-growth theorem
finds a candidate, its normalized vector is close to one of the two signal directions, and
rounding makes at most $d^2n/32$ errors. Normalization occurs in the proof only. Since
$|B_{ij}|\le D^2$, changing $b$ estimated labels changes each cleanup vote by at most $2D^2b$.
The transferred true-label margins dominate that error, so cleanup recovers all labels.

The sufficient conditions

$$
Dd\ge32,\qquad n\ge2D^2+(72D^2)^2
$$

imply the residual bound. `recoverInput_failure_le` consequently gives the actual program
the same failure estimate $2e^{-n}+2n e^{-d^2n/8}$. For fixed $D$, the size condition eventually
holds. This establishes the computational theorem without assuming an eigensolver, a spectral
gap for a supplied instance, or an efficient sampler for the prior.

### Native resource accounting

The unconditional theorem in [Program.lean](Program.lean) is:

```lean
@[fun_prop] theorem computableInPolyTime_recoverInput (params : PowerParameters) :
    ComputableInPolyTime (recoverInput params)
      encDenseGraphInput (encList encBool)
```

It charges construction of the integer table, all $n(n+1)$ candidate tests, sign rounding,
matrix-vector cleanup, and writing the output. The existing
[integer matrix-power kernel](../../Computability/PolyTime/Int/MatrixPower.lean) proves that,
if the entries have at most $b$ magnitude bits, coordinates after $t$ multiplications have
at most $1+t(b+\operatorname{size}(n))$ magnitude bits. The stored integers may have large
values, while their binary encodings remain polynomially bounded. Native bounded iteration,
list search, and arithmetic certificates turn that bound into `ComputableInPolyTime`.

The polynomial may depend on the fixed constants $D,c$. The theorem covers one machine for
all dimensions and priors at the chosen fixed $p,q$. Parameter estimation and a machine taking
varying encoded probability parameters would be additional results.

## 6. Existing library usage and shared changes

| Component | Reuse and additions |
|---|---|
| Probability spaces | Existing cslib-frontier `PMF.coin`, finite `PMF.pi`, expectation identities, event bounds, and bind bounds. Mathlib's homogeneous random-graph measure does not directly supply the heterogeneous block product PMF. |
| Hidden-state problem | The `DistributionalSearchProblem` interface introduced in the planted-clique development. No new average-case problem framework or model of computation is introduced. |
| Linear algebra | Mathlib's Euclidean spaces, matrix/operator conversion, rank-one operators, ordered symmetric spectrum, and normalization. A new generic leading-eigenvector perturbation estimate extends the existing spectral module. |
| Concentration | Existing bounded differences plus the finite nets from the planted-clique work. Weighted centered-score and symmetric-matrix results are extracted into general probability modules. The old planted-clique random-matrix proof now calls them too. |
| Boolean rounding | Existing `signVal`, `signWord`, `hammingDist`, and `signRound`. Rounding is moved to `Foundations/Data/BitString/Sign/Rounding.lean`, generalized to arbitrary finite domains, and extended to scaled signs. Existing Fourier-learning and junta callers use the shared implementation. |
| Cleanup | A deterministic weighted-vote lemma for any uniform entry bound, independent of the graph distribution or the method producing the approximate labels. Both algorithms use it. |
| Native computation | Existing `ComputableInPolyTime`, `IsPPTOn`, and the deterministic-to-PPT bridge; native binary integer arithmetic, row tables, bounded iteration, and list search. The planted-clique power search and its alignment proof are extracted into shared modules. |
| Graph representation | Shared `DenseGraphInput` with native lookup and a canonical graph-presentation inverse. Planted clique delegates to it while retaining its original three-field encoding: encoded words unchanged. |

The ordinary-import clients check the exact-signal cleanup, the full native theorem, and
equality of graph laws when $p=q$. The latter confirms that the model does not reveal labels
merely through their representation. The
[program client](../../../CslibFrontierTests/CommunityDetectionProgram.lean) executes the
complete algorithm on two disjoint edges and obtains the correct two communities, checks the
empty-input path, and applies the native certificate and exact representation bridge.

## 7. Scope and remaining directions

The completed computational result is exact recovery for known, fixed $p>q$, with a native
polynomial-time integer program, an actual finite error bound, and an asymptotic theorem for
every label prior. The exact leading-eigenvector specification retains its separate, sharper
finite sufficient condition. Computing that exact eigenvector is not a claim of the native
program; a certified finite-precision implementation would be another realization.

Sparse detection and sparse exact recovery need different quantitative estimates and, in
the bounded-degree regime, different spectral machinery. The present $O(\sqrt n)$ noise
bound and uniform $2b$ cleanup sensitivity do not establish those thresholds. Parameter
estimation when $p,q$ are unknown and models with more than two communities are also outside
this theorem.
