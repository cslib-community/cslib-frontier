# Planted-clique recovery

This development proves that, for every fixed real $c>0$, one deterministic native
polynomial-time program recovers a planted clique with probability tending to one whenever
$k(n)\ge c\sqrt n$ eventually. It also gives a separate correctness proof for the ordinary
adjacency matrix's second-eigenvector algorithm using Mathlib.

The every-$c$ program uses an exact integer matrix-power algorithm inside a common-neighbor
search. A second certified program computes a rational approximation to the ordinary adjacency
matrix's actual second eigenvector, then selects coordinates and performs degree cleanup. Its
strongest finite recovery theorem applies at $k\ge(51/7)\sqrt n$, for $n\ge2^{64}$ and
$4096k\le n$. A certified hybrid removes the upper-size restriction by using the existing
integer solver for large cliques. These explicit guarantees concern the actual native programs
and their recovery experiments, for every prior on hidden sets of the prescribed size.

## 1. Paper and formalized theorems

### Source and correspondence

The source is Noga Alon, Michael Krivelevich and Benny Sudakov,
[**Finding a large hidden clique in a random graph**](https://www.tau.ac.il/~nogaa/PDFS/clique3.pdf),
*Random Structures & Algorithms* 13(3–4), 457–466 (1998).
The bibliography key is `AlonKrivelevichSudakov1998`. The locators below use the linked
author manuscript's printed pages, not the journal pagination.

| Source location | Corresponding part of this development |
|---|---|
| Main result, introduction and Section 2, pp. 2–3 | Recovery with high probability for every fixed positive coefficient of $\sqrt n$. |
| Algorithm A, Section 2.1, p. 3 | The exact specification in [Eigenvector.lean](Eigenvector.lean), and its rational approximation and native recovery program in [EigenvectorPolyTime.lean](EigenvectorPolyTime.lean). |
| Section 2.2, pp. 4–7; Proposition 2.1, Proposition 2.3 and Lemma 2.4 | Ordered spectral separation, a centered-indicator residual, eigenvector alignment, coordinate selection and degree cleanup. |
| Lemma 2.4's outside-to-clique row sums, p. 6 | [Directional.lean](Directional.lean) obtains a finite exponential estimate by applying the library's Johnson–Lindenstrauss row-concentration theorem to the actual edge coins. |
| Algorithm B, Section 2.3, pp. 7–8 | The executable common-neighbor wrapper in [CommonNeighborProgram.lean](CommonNeighborProgram.lean), with the integer-power algorithm as its certified base solver. |

The formalization uses conservative explicit constants and finite error bounds. The integer
base algorithm is a variant developed for this formalization. The literal Algorithm A
specification is analyzed separately. The polynomial filter, iteration count and rational
normalization below are implementation choices of this formalization. The threshold $51/7$,
the explicit cutoff and the exponential error budget are an original quantitative variant
of the paper's proof; they are not asserted as the paper's constants or as optimal constants.
In particular, the full-range hybrid uses the existing certified integer solver where the
source uses a preliminary degree argument. The raw second-eigenvector theorem retains its
explicit sparsity premise. This distinction is recorded in
[#6238](https://github.com/cslib-community/cslib-frontier/issues/6238).

### The random problem and what counts as success

Let $S\subseteq\{0,\ldots,n-1\}$ have cardinality $k$. Sample $S$ from a supplied prior, then
independently sample fair edge coins. Every pair in $S$ is joined; every other unordered pair
is an independent edge with probability $1/2$. The algorithm receives the graph and the public
target size $k$.

[Probability/PlantedClique/Problem.lean](../../Probability/PlantedClique/Problem.lean)
makes this separation explicit:

- `PlantedInstance` stores the hidden set and the graph.
- `instanceDistribution` draws the hidden set before the independent edge coins.
- `searchProblem` reveals only `PlantedInstance.graph`.
- Its success relation is `answer = state.planted`.

Thus success means exact recovery of the latent set. The prior can be arbitrary; specializing
it to `uniformPlantedSet n k hkn` gives the usual uniform planting law. The prior is part of
the mathematical experiment, not a sampler supplied to the machine. A prior on the stated
subtype can exist only when $k\le n$.

### Main asymptotic theorem: one native program for every fixed $c>0$

For every $c>0$, there is a fixed seed size $s$ such that the explicit program
$A_s=\mathtt{commonNeighborRecover}\ \mathtt{recoverInput}\ s$ is polynomial-time, and for
every sequence of target sizes and every family of planted-set priors,

$$
\bigl(k(n)\ge c\sqrt n\text{ eventually}\bigr)
\quad\Longrightarrow\quad
\Pr_{S,G}\!\left[A_s(G,k(n))\ne S\right]\longrightarrow0.
$$

The exported signature in
[CommonNeighborAsymptotics.lean](CommonNeighborAsymptotics.lean) is below. Lean excerpts in
this guide omit proof bodies and use the namespaces opened in their linked source modules.

```lean
theorem exists_commonNeighborRecover_ppt_tendsto_failure {c : ℝ} (hc : 0 < c) :
    ∃ s : ℕ,
      IsPPTOn encRecoveryInput (encList encUnary)
        (fun input => pure (commonNeighborRecover recoverInput s input)) ∧
      ∀ (k : ℕ → ℕ) (prior : ∀ n, PMF {S : Finset (Fin n) // S.card = k n}),
        (∀ᶠ n : ℕ in atTop, c * sqrt n ≤ (k n : ℝ)) →
        Tendsto (fun n => (searchProblem (prior n)).experiment
          (fun G => PMF.pure (vertexSet n
            (commonNeighborRecover recoverInput s (RecoveryInput.ofGraph G (k n))))) false)
          atTop (𝓝 0)
```

The quantifier order matters. The seed size and program are fixed before the size schedule
and priors. The program receives the value $k(n)$ in its input, so the theorem does not
require an algorithm for computing the schedule itself. The polynomial can depend on the
fixed $s$; the statement does not treat $s$ as a further runtime input.

`IsPPTOn` is the existing uniform native model. Here the certified program is deterministic,
embedded using `pure`. The limit concerns the actual `ENNReal` failure probability, obtained
by evaluating the Boolean success experiment at `false`.

### Original finite base and exact eigenvector interfaces

The certified integer solver has the following probability theorem in [Final.lean](Final.lean).
Here and in the next signature, `n : ℕ` is an implicit parameter of the enclosing section.

```lean
theorem searchProblem_recover_failure_le {k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hn : 1 ≤ n) (hk : 6 ≤ k) (hsize : 1024 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment (fun G => PMF.pure (recover G k)) false).toReal ≤
      2 * exp (-(n : ℝ)) + n * exp (-(k : ℝ) / 32)
```

[Program.lean](Program.lean) proves `computableInPolyTime_recoverInput` and the semantic
agreement `toFinset_recoverInput`. [PolyTime.lean](PolyTime.lean) combines them with this bound
in `searchProblem_hasPPTSolver`.

For the exact raw-adjacency second-eigenvector specification,
[EigenvectorFinal.lean](EigenvectorFinal.lean) proves:

```lean
theorem searchProblem_recoverEigenvector_failure_le {k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hn : 1 ≤ n) (hk : 6 ≤ k) (hsparse : 4096 * k ≤ n)
    (hsize : 8192 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment (fun G => PMF.pure (recoverEigenvector G k)) false).toReal ≤
      2 * exp (-(n : ℝ)) + n * exp (-(k : ℝ) / 32)
```

All spectral, independence and alignment estimates are proved inside this result. Its remaining
premises are numerical size conditions. The exact eigenvector definition is noncomputable and
serves as the mathematical specification.

[EigenvectorPolyTime.lean](EigenvectorPolyTime.lean) proves the corresponding bound for the
actual finite-integer-arithmetic recovery program:

```lean
theorem searchProblem_recoverApproximateEigenvectorInput_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hn : 1 ≤ n) (hk : 6 ≤ k) (hsparse : 4096 * k ≤ n)
    (hsize : 8192 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment
      (fun G => PMF.pure (vertexSet n
        (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G k)))) false).toReal ≤
      2 * Real.exp (-(n : ℝ)) + n * Real.exp (-(k : ℝ) / 32)
```

`computableInPolyTime_recoverApproximateEigenvectorInput` certifies this same function on all
encoded inputs, without a size or spectral promise. The model-parametric endpoint
`searchProblem_eigenvector_hasPPTSolver` combines that certificate with the recovery experiment.
Its all-parameter budget is the displayed exponential expression in the proved regime and $1$
elsewhere. The machine receives the graph and public $k$; no eigenvector, successful starting
column or approximation witness is supplied to it.

Checked clients use $n=2^{50}$ and $k=2^{38}$, so the finite hypotheses are jointly satisfiable.
These clients apply the theorem symbolically; they do not execute the very large iteration count.

### Sharper native theorem: coefficient $51/7$

Define the explicit failure bound

$$
R(n,k)=2e^{-n/64}+e^{-n/2^{24}}+ne^{-k/2^{15}}.
$$

[EigenvectorSharp.lean](EigenvectorSharp.lean) proves the following statement for the same
finite-precision second-eigenvector program. No global-noise, directional-noise, spectral,
alignment or approximation condition remains as a hypothesis.

```lean
theorem searchProblem_recoverApproximateEigenvectorInput_failure_le_sharp {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hnlarge : 2 ^ 64 ≤ n) (hsparse : 4096 * k ≤ n)
    (hsize : 51 / 7 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment
      (fun G => PMF.pure (vertexSet n
        (recoverApproximateEigenvectorInput (RecoveryInput.ofGraph G k)))) false).toReal ≤
      eigenvectorSharpError n k
```

[EigenvectorHybrid.lean](EigenvectorHybrid.lean) defines one further native program:

```lean
def recoverHybridEigenvectorInput (x : RecoveryInput) : List ℕ :=
  if 1048576 * x.vertexCount ≤ x.cliqueSize ^ 2 then recoverInput x
  else recoverApproximateEigenvectorInput x
```

The integer test is equivalent to $1024\sqrt n\le k$. On that branch the existing integer
solver applies. When the test fails and $n\ge2^{64}$, arithmetic gives $4096k\le n$, so the
sharper eigenvector theorem applies. Consequently the full-range endpoint is:

```lean
theorem searchProblem_recoverHybridEigenvectorInput_failure_le {n k : ℕ}
    (prior : PMF {S : Finset (Fin n) // S.card = k})
    (hnlarge : 2 ^ 64 ≤ n) (hsize : 51 / 7 * Real.sqrt n ≤ (k : ℝ)) :
    ((searchProblem prior).experiment
      (fun G => PMF.pure (vertexSet n
        (recoverHybridEigenvectorInput (RecoveryInput.ofGraph G k)))) false).toReal ≤
      eigenvectorSharpError n k
```

`computableInPolyTime_recoverHybridEigenvectorInput` charges the branch test and both possible
computations. `searchProblem_hybridEigenvector_hasPPTSolver` packages one fixed strict PPT
program for every dimension and every target schedule. Its error budget is $R(n,k)$ in the
proved regime and $1$ elsewhere; the runtime certificate itself has no size promise.

The cutoff $2^{64}$ is deliberately conservative: it absorbs the diagonal and centering terms
using simple finite inequalities. It is not a practical input-size or running-time claim.
The three displayed error terms tend to zero along $k\ge(51/7)\sqrt n$. The exported sharp
endpoints above are finite probability inequalities; the every-$c$ limit theorem earlier in
this guide is a separate formalized asymptotic endpoint.

The checked sharp client uses $n=49\cdot2^{64}$ and $k=51\cdot2^{32}$, exactly attaining
$k=(51/7)\sqrt n$, with the usual uniform planting law. A second client uses $k=n=2^{64}$
to exercise the large-clique branch. These are symbolic theorem applications, not executions
of the huge matrices or power counts.

## 2. Algorithm and proof, with the Lean correspondence

### A. The literal second-eigenvector algorithm

Given the ordinary $0/1$ adjacency matrix $A$, take a unit eigenvector $v_2$ for its second
largest algebraic eigenvalue, select the $k$ largest absolute coordinates, and retain vertices
with at least $3k/4$ neighbors among those selected.

**Choose the second eigenvector.** `secondEigenvector` converts the adjacency matrix to a
symmetric real linear map and uses Mathlib's `LinearMap.IsSymmetric.eigenvectorBasis`.
This basis is indexed by decreasing eigenvalue; zero-based index `1` selects the second.
`adjMatrix_apply_secondEigenvector` proves its ordered eigen-equation, and
`norm_secondEigenvector` proves unit norm. The definition returns zero when $n<2$, keeping
the specification total.

**Select coordinates.** `eigenvectorApproximateSet` calls `List.selectLargest` with score
`fun i => |secondEigenvector G i|`. The generic selection API supplies cardinality and the
comparison between selected and unselected scores. Ties are handled by the same stable
selection operation throughout the proof.

**Clean up by degrees.** `recoverEigenvector` applies `SimpleGraph.recoverCliqueByDegree`.
The threshold is represented as the exact integer inequality
$3k\le4|N(v)\cap W|$, avoiding truncated natural-number division.

The deterministic cleanup lemma is shared by all constructions. Write $m=|S\setminus W|$
and $d_S(v)=|N(v)\cap S|$. For $|W|=|S|=k$, a planted clique is recovered whenever
$4(m+1)\le k$ and $4(d_S(v)+m)<3k$ for every outside vertex. The first inequality includes
the absent self-loop. The original bounds $m\le k/16$, $d_S(v)\le5k/8$ and $k\ge6$ imply
these conditions; the sharper proof below supplies a different pair of margins. This is
`recoverCliqueByDegree_eq_of_overlap` in
[CliqueRecovery.lean](../../Foundations/Combinatorics/SimpleGraph/CliqueRecovery.lean).

### B. Why the selected eigenvector reveals the clique

Write

$$
w=\frac{\mathbf1}{\sqrt n},\qquad
u=\frac{\mathbf1_S}{\sqrt k},\qquad
A=\frac n2ww^{\mathsf T}+\frac k2uu^{\mathsf T}+E.
$$

The rank-two term is the signal, not the exact expectation: the expectation also subtracts
$(I+\operatorname{diag}(\mathbf1_S))/2$. The proof includes this diagonal correction in $E$.

The sharper argument uses separate estimates for the global operator norm and the particular
direction $u$. A global norm bound is enough to separate eigenvalues, but using it again on
$u$ would lose much of the improvement in the recovery threshold.

**Global noise.** [RandomMatrix.lean](../../Probability/PlantedClique/RandomMatrix.lean)
proves, for every $a\ge0$, the single-net estimate

$$
\Pr[\|N\|_{\mathrm{op}}>a\sqrt n]
\le2\exp\!\left[\left(\frac72-\frac{49a^2}{256}\right)n\right].
$$

For a unit vector, the independent-edge coefficients of $x^{\mathsf T}Nx$ have squared sum
at most $2$. A $1/16$-net has at most $33^n$ points, and symmetry lets its quadratic forms
control the operator norm with factor $8/7$. The finite-net lemma is generic; the coefficients
and their independence come from the planted-graph sampler. Taking $a=30/7$ gives failure
at most $2e^{-n/64}$, and [RandomGraph.lean](RandomGraph.lean) transports this to

$$
\|E\|_{\mathrm{op}}\le\frac{15}{7}\sqrt n+1.
$$

The same theorem strengthens the previous coarse noise estimate to $5\sqrt n$ with failure
at most $2e^{-n}$; the older recovery interfaces continue to consume the weaker $36\sqrt n$
event. There is one shared random-matrix proof.

**Noise in the planted direction.** Inside $S$, the signed noise is zero. Outside $S$, the
coordinates of $Nu$ are normalized sums of independent signs. Different outside vertices
use disjoint edge coordinates. [Probability/PlantedClique/Directional.lean](../../Probability/PlantedClique/Directional.lean)
reuses the injective edge-row map and the existing Johnson–Lindenstrauss concentration theorem
for sums of squared Rademacher row sums. For $\epsilon\ge0$, it proves

$$
\Pr\!\left[\|Nu\|^2>(1+\epsilon)n\right]
\le\exp\!\left[-\frac{n-k}{2}
 \left(\frac{\epsilon^2}{2}-\frac{\epsilon^3}{3}\right)\right].
$$

The normalized-vector bridge is [Directional.lean](Directional.lean). Setting
$\epsilon=1/1024$ and using sparsity bounds this failure by $e^{-n/2^{24}}$. Including the
diagonal correction gives the convenient finite bound

$$
\|Eu\|\le\frac{1025}{2048}\sqrt n+1.
$$

This replaces the source's asymptotic moment calculation with an already formalized finite
row-concentration inequality. It does not assume independence of entire symmetric-matrix rows.

**Residual and eigenline.** The generic lemmas in
[EigenvectorPerturbation.lean](../../Foundations/Analysis/InnerProductSpace/EigenvectorPerturbation.lean)
use Mathlib's ordered orthonormal eigenbasis. A Rayleigh estimate places the first eigenvalue
above the all-ones signal. A vector in the span of the first three eigenvectors orthogonal to
both $w$ and $u$ bounds the third eigenvalue by the perturbation norm; ordering handles the
rest. For $t=\langle w,u\rangle=\sqrt{k/n}$ and $x=u-tw$, the exact residual identity gives

$$
\left\|(A-\tfrac{k}{2}I)x\right\|
\le \|Eu\|+|t|\,\|E\|_{\mathrm{op}}+\frac{k}{2}|t|.
$$

Here $x=(n\mathbf1_S-k\mathbf1)/(n\sqrt k)$ is the source's centered indicator after
rescaling. The eigenbasis expansion bounds the component of $x$ perpendicular to $v_2$
by residual divided by spectral separation. The proof keeps its actual projection coefficient
$c=\langle x,v_2\rangle$: coordinate selection is invariant under a common nonzero scale,
and its ordering inequality also remains valid for zero scale. There is no need to normalize
this projection to unit length and incur an extra alignment loss.

[EigenvectorBounds.lean](EigenvectorBounds.lean) combines these estimates and verifies the
finite arithmetic at $k\ge(51/7)\sqrt n$, $n\ge2^{64}$, $4096k\le n$:

$$
|\lambda_2-k/2|\le k/8,\qquad
|\lambda_i-k/2|\ge k/6\quad(i\ne2),\qquad
\exists c,\ |c|\le1\ \land\ \|cv_2-u\|\le107/320.
$$

At the threshold, the leading spectral gap is
$(51/14-15/7)\sqrt n=(3/2)\sqrt n$, while the fixed directional bound has leading size
$(1025/2048)\sqrt n$. Their ratio is $1025/3072\approx0.333659$. The checked $107/320$
bound also accounts for centering and both diagonal corrections. The large finite cutoff
makes those additional terms small.

**Approximation, selection and cleanup.** The actual rational vector $\widehat v$ is within
$1/64$ of one sign of $v_2$. Multiplying by the same $c$ and sign gives

$$
\|c\sigma\widehat v-u\|\le\frac{107}{320}+\frac1{64}=\frac7{20}.
$$

The generic coordinate-selection bound in [Indicator.lean](Indicator.lean) now yields

$$
|S\setminus W|\le2k(7/20)^2=\frac{49}{200}k.
$$

[Degree.lean](../../Probability/PlantedClique/Degree.lean) proves that every outside vertex
has at most $(129/256)k$ neighbors in $S$, except with probability at most $ne^{-k/32768}$.
The sum $129/256+49/200=3/4-7/6400$ leaves a strict outside-vertex cleanup margin. The
inside-vertex inequality accounts for the absent self-loop using $k\ge200$, which follows
from the size hypotheses. `recoverApproximateEigenvectorInput_eq_of_spectral_bounds`
connects these inequalities to the actual program and its tie handling. Finally,
[EigenvectorSharp.lean](EigenvectorSharp.lean) unions the three bad events and averages the
fixed-set guarantee over any supplied prior to obtain $R(n,k)$.

The older exact-eigenvector and integer-solver theorems still use the shared two-event
composition in [Probability/PlantedClique/Recovery.lean](../../Probability/PlantedClique/Recovery.lean).
Their public finite bounds are preserved, while their deterministic and probabilistic proofs
consume the generalized helpers above.

### C. Computing the second eigenvector with finite arithmetic

The implementation approximates the ordered second eigenvector of the same raw adjacency
matrix $A$. It has four steps.

**1. Isolate the eigenvalue with a polynomial filter.** The implementation analysis accepts
the separated-spectrum interface

$$
|\lambda_2-k/2|\le k/8,\qquad
i\ne2\ \Longrightarrow\ |\lambda_i-k/2|\ge k/6.
$$

Both the older `adjMatrix_eigenvalues_bounds` theorem and the sharper
`secondEigenvector_bounds_of_residual_le` theorem supply this interface. The additional radius bound
`SimpleGraph.abs_adjMatrix_eigenvalues_le` in the general
[adjacency-spectrum module](../../Foundations/Combinatorics/SimpleGraph/AdjMatrix.lean)
gives $|\lambda_i|\le n$ for any graph. Define

$$
K=16(n+k+1)^2,\qquad F=KI-(2A-kI)^2.
$$

[EigenvectorProgram.lean](EigenvectorProgram.lean) defines this integer matrix as
`secondEigenvectorFilter` and implements its row table as `RecoveryInput.eigenvectorFilterRows`.
Because $F$ is a polynomial in $A$, the same ordered eigenbasis diagonalizes both. For the
second eigenvector its eigenvalue is $\alpha=K-(2\lambda_2-k)^2>0$; every other filtered
eigenvalue is nonnegative and at most $\beta=K-k^2/9$. The proved bounds imply

$$
0\le\frac\beta\alpha\le1-\frac{1}{3072n^2}.
$$

This turns the required second eigenline into the dominant eigenline of an exactly
represented integer matrix, without changing the eigenvectors.

**2. Find a useful column without a guessed starting vector.** Set

$$
t(n)=1048576\,n^3=2^{20}n^3.
$$

`eigenvectorPowerColumn` computes every $F^{t(n)}e_j$, compares exact integer squared norms,
and selects a maximum with stable tie breaking. `eigenvectorPowerColumn_spec` proves both
that the returned list is an actual power column and that its squared norm is maximal.

The reusable theorem
`OrthonormalBasis.exists_sign_normalize_pow_column_sub_sq_le` in
[PowerIteration.lean](../../Foundations/Analysis/InnerProductSpace/PowerIteration.lean)
shows that the selected column $z$ is nonzero and that, for one sign $\sigma$,

$$
\left\|\frac z{\|z\|}-\sigma v_2\right\|^2
\le2n\left(\frac\beta\alpha\right)^{2t(n)}.
$$

It works with an arbitrary orthonormal eigenbasis and an arbitrary orthonormal seed basis.
Summing the second-eigenvector projections over the seed basis supplies a lower bound for
the maximum column norm; an eigenbasis expansion bounds the perpendicular error. Thus the
proof establishes a suitable starting column for the actual exhaustive selection procedure.
[EigenvectorApproximation.lean](EigenvectorApproximation.lean) combines this theorem with
the filter bounds and an elementary inverse-Bernoulli estimate to obtain distance at most
$1/128$ from $z/\|z\|$ to the second eigenvector, up to sign.

**3. Return a rational vector with a proved normalization error.** Exact real normalization
is only a proof device. For an integer vector $z$ and positive integer precision scale $p$,
[IntegerVector/Normalize.lean](../IntegerVector/Normalize.lean) stores

$$
Q=\sum_i z_i^2,\qquad
d=\left\lfloor\sqrt{p^2Q}\right\rfloor+1,\qquad
\widehat v_i=\frac{p z_i}{d}.
$$

`RationalVector` contains a signed-binary numerator list and one binary natural denominator;
the fractions need not be reduced. `normalize` computes these finite data, and
`normalize_close` proves, for nonzero integer $z$,

$$
\left\|\widehat v-\frac z{\|z\|}\right\|\le\frac1p.
$$

The proof uses the defining inequalities for integer square root and the fact that a nonzero
integer vector has norm at least one. `approximateSecondEigenvectorInput` uses $p=128$.
The triangle inequality therefore gives the required total error $1/64$;
`approximateSecondEigenvectorInput_close` proves it for the computed rational output.

**4. Select coordinates and clean up.** The rational output has a common positive scale
factor multiplying $z$. Comparing its absolute coordinates is therefore exactly equivalent
to comparing the integer magnitudes of $z$, including all ties. The recovery program can
reuse `largestIndices` on $z$ and then `RecoveryInput.cleanup`. Its proof connects those
comparisons to the scaled-alignment cleanup theorem described above. The original
`recoverFromApproximateSecondEigenvector_eq` tolerance interface also remains a client of
the same approximation guarantee. The corresponding concentration estimates give the
probability theorems for this same program.

Both the rational-output program and the complete recovery program have native
`ComputableInPolyTime` certificates. They reuse the integer matrix-power certificate, which
charges growing coordinate bit lengths, and the binary integer-square-root certificate.
The polynomial iteration count is computed from unary $n$. Construction of the filter,
enumeration of all columns, exact norm comparisons, sorting, normalization and output writing
are charged. The large fixed iteration bound is chosen for a simple verified polynomial
bound; no claim of practical numerical performance is made.

Every input record is handled. Missing adjacency bits decode as absent edges, the decoded
graph is symmetric and loop-free, and zero-dimensional input produces an empty column and
rational output with denominator $1$. Outside the spectral regime the program still runs
with its unconditional runtime certificate; the failure budget is $1$.

### D. The exact integer algorithm with a native runtime certificate

The executable base algorithm uses

$$
M=2A-J+I,
$$

with zero diagonal and off-diagonal entries $1$ or $-1$. For each $0\le t\le n$ and each
standard basis vector $e_i$, it computes $y=M^te_i$ and $z=M^{t+1}e_i$, looking for

$$
\|z\|^2>0,\qquad k^2\|y\|^2\le4\|z\|^2.
$$

These are exact comparisons of integer sums of squares. `growingColumn?` chooses the first
successful pair; `recoveredVector` returns its $z$, or zero if none exists. `approximateSet`
takes its $k$ largest absolute coordinates, and `recover` performs the same degree cleanup.

[IntegerPower/Search.lean](../IntegerPower/Search.lean) proves that the search succeeds in the required signal
regime. The general argument uses traces of positive operator powers to show that some
basis orbit must grow. [Correctness.lean](Correctness.lean) then uses the rank-one perturbation

$$
M=\mathbf1_S\mathbf1_S^{\mathsf T}+R,\qquad
\|R\|_{\mathrm{op}}\le k/16
$$

and the growth test to prove alignment of $z/\|z\|$ with the planted indicator.
Normalization is used only in the proof. Coordinate selection and degree cleanup reuse
the same lemmas as the raw eigenvector argument. The random noise and degree estimates
discharge the deterministic premises when $k\ge1024\sqrt n$.

The computational statement is uniform in the dimensions. `RecoveryInput` contains unary
$n$, unary $k$, and raw row-major adjacency bits; a canonical input has encoded length

$$
n^2+2n+2k+2.
$$

Matrix entries, vector entries and squared norms are stored as signed binary integers.
The new [matrix-power kernel](../../Computability/PolyTime/Int/MatrixPower.lean) proves that
after $t$ iterations, each coordinate has at most
$1+t(b+\operatorname{size}(n))$ magnitude bits when matrix entries have at most $b$.
This supports the existing native bounded-iteration rule and charges the actual arithmetic.

`computableInPolyTime_recoverInput` certifies constructing the signed matrix, enumerating
and testing columns, sorting coordinates, performing degree cleanup, and writing the output.
`toFinset_recoverInput` identifies the list implementation with the mathematical `recover`.
The decoder gives every input record a total graph interpretation, so the runtime certificate
requires no planted-graph, spectral, or input-well-formedness hypothesis.

### E. Common neighbors give every fixed positive threshold

Fix a seed size $s$. The wrapper enumerates lists of $s$ distinct vertices. For each seed
set $T$, form

$$
U=N^*(T)=\{v\notin T:\ \forall t\in T,\ vt\in E(G)\}.
$$

Compute the induced graph on $U$, run the integer solver with target $k-s$, lift the returned
local identifiers, and add the seed. Form all such candidates and return the first candidate
verified to be a $k$-clique; return the empty list if none passes.

[CommonNeighborProgram.lean](CommonNeighborProgram.lean) implements these steps as
`RecoveryInput.commonVertices`, `inducedInput`, `commonNeighborCandidate`,
`validatesClique` and `commonNeighborRecover`. Increasing enumeration of $U$ provides the
relabeling; `graph_inducedInput` proves that the represented graph is the mathematical induced
graph. The verifier checks size, distinctness, identifier bounds and pairwise adjacency.

The implementation enumerates distinct lists rather than subsets, so a seed set may occur
in several orders. Its fallback is empty, rather than an arbitrary $k$-set. Neither choice
changes the high-probability recovery result. The native certificate includes candidate
construction and verification for the fixed-size enumeration.

**Expose the right randomness.** In the proof, fix one $T\subseteq S$ of size $s$ before
sampling any edge coins. The algorithm will enumerate it. All $k-s$ vertices of $S\setminus T$
survive in $U$, while each outside vertex survives independently with probability
$q=2^{-s}$.

[CommonNeighbors.lean](../../Probability/PlantedClique/CommonNeighbors.lean) proves the
induced distribution using an exact coupling: retain the seed-touching coordinates from one
uniform coin table and resample the other coordinates from an independent table. A
product-space involution proves that the resulting full table has the original law. The
exposed coordinates determine $U$, while the fresh coordinates determine the induced graph.
For each fixed exposure, the increasing relabeling therefore gives an exact planted-graph
law with $|U|$ vertices and planted size $k-s$. No conditional-probability division is needed.

**Control the reduced size.** [CommonNeighborSize.lean](../../Probability/PlantedClique/CommonNeighborSize.lean)
proves independence by an injective map from outside-vertex/seed-vertex pairs to upper-triangle
edge coordinates. Applying the existing finite-PMF Hoeffding inequality to the corresponding
indicators gives

$$
\Pr[|U|\ge k+2nq]\le e^{-2nq^2}.
$$

On the remaining event, the base solver applies if
$6\le k-s$ and $1024\sqrt{k+2nq}\le k-s$.
[CommonNeighborRecovery.lean](CommonNeighborRecovery.lean) combines the exact induced law
with the already-proved base recovery bound.

**Justify accepting the first clique.** A successful planted seed guarantees that a correct
candidate exists; the verifier alone does not guarantee that an earlier accepted clique is
the hidden set. [Uniqueness.lean](../../Probability/PlantedClique/Uniqueness.lean) closes this
point. If every outside vertex has at most $5k/8$ neighbors in $S$, any other $k$-clique must
contain at least $3k/8$ outside vertices. For a fixed outside $r$-set, the exact clique
probability is $2^{-\binom r2}$. With $r=\lfloor k/4\rfloor$, a union bound excludes all such
sets except with probability at most

$$
ne^{-k/32}+\binom nr2^{-\binom r2}.
$$

Thus the wrapper recovers the latent planted set. This is a random-input exact-recovery
theorem; it is not a maximum-clique algorithm for arbitrary input graphs.

Combining the events,
`searchProblem_commonNeighborRecover_failure_le` in
[CommonNeighborFinal.lean](CommonNeighborFinal.lean) proves the finite bound

$$
\begin{aligned}
\Pr[A_s(G,k)\ne S]\le{}&
 e^{-2nq^2}
 +2e^{-(k-s)}+ne^{-(k-s)/32}\\
&+ne^{-k/32}
 +\binom nr2^{-\binom r2}.
\end{aligned}
$$

It assumes $n\ge1$, $k-s\ge6$ and $1024\sqrt{k+2nq}\le k-s$.
The proof analyzes one fixed planted seed, so there is no factor of $n^s$ in the error
bound. Enumeration contributes to running time, not to this probability estimate.

Finally, choose a constant $s$ such that

$$
16\cdot1024^2\cdot2^{-s}\le c^2.
$$

`exists_commonNeighbor_seedSize` proves that eventual $k(n)\ge c\sqrt n$ implies the
finite numerical promise for this fixed choice. Every error term tends to zero. In particular,
the proof bounds the binomial term eventually by $e^{-r}$, using
$\binom nr\le n^r$ and $\log n=o(\sqrt n)$. Squeezing the actual failure probability by this
budget proves the main asymptotic theorem.

## 3. Use of cslib-frontier and Mathlib

### Infrastructure already present before this development

The following are pre-existing APIs used directly by the proof or runtime certificate.

| Existing component | Use in this formalization |
|---|---|
| [Boolean games](../../Crypto/Game.lean) and [concrete game bounds](../../Crypto/Game/Concrete.lean): `Game.Indistinguishable`, `IndistinguishableWithError`, `IndistinguishableWithin` | The new distribution-law adapter supplies experiments to the established notions, with explicit evaluators and admissibility or resource predicates. |
| [Native PPT](../../Computability/Probabilistic/PPT.lean): `IsPPTOn` and `ComputableInPolyTime.isPPTOn` | Turn the deterministic machine certificate into one strict PPT program for the entire input family. |
| [Structure encodings](../../Computability/Machines/Turing/MultiTape/Encodings/Structure.lean): `enc_structure` | Generate the concrete record encoding and constructor/projection certificates for `RecoveryInput`. |
| [Integer tables](../../Computability/PolyTime/Int/Table.lean), [dot products](../../Computability/PolyTime/Int/DotProduct.lean), binary arithmetic and native list/iteration rules | Certify the matrix construction, exact arithmetic, list traversal and bounded iteration. Existing `ComputableInPolyTime.listsUpTo` supplies the fixed-seed enumeration certificate. |
| [Binary square root](../../Computability/Machines/Turing/MultiTape/Complexity/PolyTime/Nat/Sqrt.lean): `ComputableInPolyTime.binary_sqrt` | Compute the common rational denominator while charging the bit cost of the squared norm and precision. |
| [Inverse Bernoulli inequality](../../Foundations/Analysis/BernoulliInequality.lean): `Real.one_sub_pow_le_one_div_one_add_mul` | Convert the filter's contraction ratio into an explicit finite iteration bound. |
| [TracePower.lean](../../Foundations/LinearAlgebra/TracePower.lean): `LinearMap.IsPositive.pow_le_re_trace_pow` and `LinearMap.IsSymmetric.re_inner_apply_eq_sum` | Prove the existence of a growing power column and expand spectral quadratic forms in the eigenbasis. |
| [Rademacher.lean](../../Probability/BitString/Rademacher.lean): `expect_exp_mul_sum_mul_signVal_le` | Supply the moment-generating-function estimate from which the new scalar tail bounds, degree bounds and random-matrix estimate are derived. |
| [JohnsonLindenstrauss.lean](../../Probability/JohnsonLindenstrauss.lean): `dens_mul_lt_sum_sq_sum_mul_signVal_le` | Bound the squared noise norm in the planted direction from independent outside-to-clique rows, without a new moment or concentration development. |
| [Uniform PMFs](../../Probability/PMF/Uniform.lean): `uniformOfFintype_pi_map_comp_embedding` and `uniformOfFintype_bind_bind_fst_equiv` | Transport uniform coin laws through injective coordinate maps and justify exposure/resampling. |
| [Concentration.lean](../../Probability/Concentration.lean): `PMF.pi_sum_ge_mean_add` | Bound the number of surviving outside vertices after row independence has been established. |
| [EventBind.lean](../../Probability/PMF/EventBind.lean): `toOuterMeasure_bind_failure_toReal_le` | Combine sequential failure probabilities and average fixed-planted-set bounds over arbitrary priors. |

Mathlib supplies `SimpleGraph`, finite sets, matrices, Euclidean spaces, continuous linear
maps and their operator norms, orthonormal bases and ordered self-adjoint spectral theory.
In particular, the literal second eigenvector uses the ordering of
`LinearMap.IsSymmetric.eigenvectorBasis` and `eigenvalues_antitone`. The matrix-level
eigenbasis has an arbitrary reindexing and is not used to identify the second eigenvalue.
Mathlib's filters, exponential/logarithmic asymptotics and `ENNReal` continuity support the
final limit argument. The sharper proof also uses Mathlib's orthogonal projections and
their norm contraction, the self-adjoint Rayleigh characterization of the operator norm,
and Haar-volume scaling for finite-net packing.

### Shared interfaces and lemmas added by this development

The new
[DistributionalSearchProblem](../../Probability/Distributional/Search.lean) separates the
state law, observation and acceptance relation. Its model-parametric `HasSolver` takes an
evaluator and an admissibility predicate:

$$
\exists a,\quad \operatorname{Admissible}(a)\ \land\
\forall n,\ \Pr[\text{the search experiment with }\operatorname{eval}(a,n)
\text{ fails}]\le\epsilon(n).
$$

A whole program is quantified before the dimension. A client can choose a uniform machine
or a circuit family and impose the corresponding resource condition explicitly. The
definition does not equate these computational models.

The new [DistinguishingProblem](../../Probability/Distributional/Distinguishing.lean) stores
the two observation laws. [Crypto.Distributional.game](../../Crypto/Game/Distributional.lean)
connects them to the pre-existing Boolean-game predicates. Existing inversion and hidden-bit
prediction experiments are connected to search in
[DistributionalSearch.lean](../../Crypto/Game/DistributionalSearch.lean). These bridges make
the statistical and cryptographic uses share the same underlying experiments.

[CommonNeighborPolyTime.lean](CommonNeighborPolyTime.lean) supplies the concrete native
instance as `searchProblem_commonNeighbor_hasPPTSolver`. Its evaluator presents the graph
as `RecoveryInput.ofGraph`, runs the encoded program, and interprets output identifiers with
`vertexSet`. The all-parameter budget `commonNeighborFailureBound` uses the proved finite
bound in its numerical regime and the trivial budget $1$ elsewhere.

The additional shared mathematics includes coordinate selection and its error bound,
deterministic clique cleanup and uniqueness, finite-seed common neighborhoods, uniform
fixed-pattern probabilities, spectral perturbation lemmas, finite nets, Rademacher tails,
and the native integer-power and sorting certificates. The finite-precision implementation
adds a general maximum-column power-iteration estimate and certified rational normalization
of integer vectors. The sharper analysis generalizes the net radius, quadratic-form net
bound, rank-two residual and spectral-separation interfaces, and the degree margin; existing
clients are migrated to those shared statements. These are contributions of this
development, rather than pre-existing planted-clique machinery.

One reuse improvement is an extraction: the stable merge-sort/insertion-sort bridge formerly
private to the matroid greedy algorithm now lives in
[Foundations/Data/List/MergeSort.lean](../../Foundations/Data/List/MergeSort.lean).
The existing matroid client and the new selection/runtime proof use that shared lemma.
The circuit-testing layer also gains `isCircuitTest_iff_exists_circuit`, relating its existing
semantic test class to explicit De Morgan circuits.

The coefficient $51/7$ is the best constant checked in this development, not a claimed
optimum. Further work could reduce the finite cutoff, improve the residual and rounding
losses, or implement the paper's preliminary degree branch. The full-range guarantee already
uses the explicit native hybrid above. The every-$c$ native recovery theorem uses the integer
solver and common-neighbor wrapper; these are distinct, fully specified programs.
