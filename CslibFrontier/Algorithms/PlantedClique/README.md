# Planted-clique recovery

This development proves that, for every fixed real $c>0$, one deterministic native
polynomial-time program recovers a planted clique with probability tending to one whenever
$k(n)\ge c\sqrt n$ eventually. It also gives a separate correctness proof for the ordinary
adjacency matrix's second-eigenvector algorithm using Mathlib.

The every-$c$ program uses an exact integer matrix-power algorithm inside a common-neighbor
search. A second certified program computes a rational approximation to the ordinary adjacency
matrix's actual second eigenvector, then selects coordinates and performs degree cleanup. Its
finite recovery theorem has the same size assumptions and error bound as the exact eigenvector
specification. Sharpening those constants toward the paper's threshold remains open in
[#6238](https://github.com/cslib-community/cslib-frontier/issues/6238).

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
| Algorithm B, Section 2.3, pp. 7–8 | The executable common-neighbor wrapper in [CommonNeighborProgram.lean](CommonNeighborProgram.lean), with the integer-power algorithm as its certified base solver. |

The formalization uses conservative explicit constants and finite error bounds. The integer
base algorithm is a variant developed for this formalization. The literal Algorithm A
specification is analyzed separately. The polynomial filter, iteration count and rational
normalization below are implementation choices of this formalization, not numerical routines
specified by the paper. The paper's constant $10$ is not established here. That remaining
analysis, including the source's preceding reduction to $k=O(\sqrt{n\log n})$, is tracked in
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

### Finite base theorem and literal eigenvector theorem

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

The deterministic cleanup lemma is shared by both spectral constructions. If $|W|=|S|=k$,
at most $k/16$ planted vertices are missing from $W$, and every outside vertex has at most
$5k/8$ neighbors in $S$, then the cleanup returns $S$. An outside vertex has at most
$5k/8+k/16<3k/4$ neighbors in $W$. A planted vertex has at least $15k/16-1$; the hypothesis
$k\ge6$ accounts for the absent self-loop. This is
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

[RandomMatrix.lean](../../Probability/PlantedClique/RandomMatrix.lean) bounds the signed
noise matrix $N$ by $36\sqrt n$, except with probability at most $2e^{-n}$. Consequently,

$$
\|E\|_{\mathrm{op}}\le18\sqrt n+1\le k/256
$$

in the eigenvector theorem's regime. This is
`opNorm_raw_residual_le_card_div_256`.

The new general lemmas in
[EigenvectorPerturbation.lean](../../Foundations/Analysis/InnerProductSpace/EigenvectorPerturbation.lean)
carry out the spectral argument using Mathlib's orthonormal eigenbasis:

1. A Rayleigh estimate bounds the first eigenvalue from below.
2. The span of the first three eigenvectors contains a nonzero vector orthogonal to both
   $w$ and $u$. On that vector only the perturbation contributes to the quadratic form.
   This bounds the third eigenvalue, and ordering bounds every subsequent eigenvalue.
3. Set $t=\langle w,u\rangle=\sqrt{k/n}$ and $x=u-tw$. The sparsity hypothesis gives
   $|t|\le1/64$. The proof bounds the residual
   $\|(A-\tfrac{k}{2}I)x\|$ by $3k/128$ and separates all eigenvalues except the second
   from $k/2$ by at least $k/4$.
4. Expand $x$ in the ordered eigenbasis. The residual identity bounds the sum of squared
   coefficients away from the second eigenspace. After accounting for $tw$ and the possible
   sign of the eigenvector, `secondEigenvector_alignment` gives

$$
\exists \sigma\in\{-1,1\},\qquad
\|v_2-\sigma u\|^2\le49/2048<1/32.
$$

Here $x=(n\mathbf1_S-k\mathbf1)/(n\sqrt k)$, relating the formalized residual argument to
the centered indicator used in the source. The finite bounds above are the bounds proved
by this development.

The generic coordinate-error lemma then yields
$16|S\setminus W|\le k$; `eigenvectorApproximateSet_overlap` is its application to $v_2$.
The shared cleanup lemma finishes deterministic correctness. The outside-degree failure
bound is at most $ne^{-k/32}$, and a union bound gives the finite probability theorem.

[Probability/PlantedClique/Recovery.lean](../../Probability/PlantedClique/Recovery.lean)
shares this probability step between both algorithms. Its
`dens_recover_ne_le_of_noise_degree` takes a proof that recovery succeeds whenever both
good conditions hold and returns the common failure bound. Both final modules instantiate
it with their deterministic correctness proofs.

The same proof also establishes a useful numerical interface:
`recoverFromApproximateSecondEigenvector_eq` allows an arbitrary vector $v$ satisfying

$$
\min_{\varepsilon\in\{-1,1\}}\|v-\varepsilon v_2\|\le1/64.
$$

Under the deterministic noise and degree conditions, selecting coordinates of $v$ and
performing the same cleanup still returns $S$. Exact normalization of $v$ is unnecessary.
The finite-precision implementation proves this tolerance for its actual output.

### C. Computing the second eigenvector with finite arithmetic

The implementation approximates the ordered second eigenvector of the same raw adjacency
matrix $A$. It has four steps.

**1. Isolate the eigenvalue with a polynomial filter.** Under the deterministic rank-two
noise and sparsity conditions, `adjMatrix_eigenvalues_bounds` proves

$$
|\lambda_2-k/2|\le k/8,\qquad
i\ne2\ \Longrightarrow\ |\lambda_i-k/2|\ge k/4.
$$

The general proof, `second_eigenvalue_bounds_of_rank_two`, reuses the ordered-spectrum,
residual and projection estimates from the alignment argument. The additional radius bound
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
eigenvalue is nonnegative and at most $\beta=K-k^2/4$. The proved bounds imply

$$
0\le\frac\beta\alpha\le1-\frac{1}{768n^2}.
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
comparisons to the existing `recoverFromApproximateSecondEigenvector_eq` tolerance theorem.
The common noise/degree failure lemma then gives the probability theorem for this same program.

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

[PowerSearch.lean](PowerSearch.lean) proves that the search succeeds in the required signal
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
| [Uniform PMFs](../../Probability/PMF/Uniform.lean): `uniformOfFintype_pi_map_comp_embedding` and `uniformOfFintype_bind_bind_fst_equiv` | Transport uniform coin laws through injective coordinate maps and justify exposure/resampling. |
| [Concentration.lean](../../Probability/Concentration.lean): `PMF.pi_sum_ge_mean_add` | Bound the number of surviving outside vertices after row independence has been established. |
| [EventBind.lean](../../Probability/PMF/EventBind.lean): `toOuterMeasure_bind_failure_toReal_le` | Combine sequential failure probabilities and average fixed-planted-set bounds over arbitrary priors. |

Mathlib supplies `SimpleGraph`, finite sets, matrices, Euclidean spaces, continuous linear
maps and their operator norms, orthonormal bases and ordered self-adjoint spectral theory.
In particular, the literal second eigenvector uses the ordering of
`LinearMap.IsSymmetric.eigenvectorBasis` and `eigenvalues_antitone`. The matrix-level
eigenbasis has an arbitrary reindexing and is not used to identify the second eigenvalue.
Mathlib's filters, exponential/logarithmic asymptotics and `ENNReal` continuity support the
final limit argument.

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
of integer vectors. These are contributions of this
development, rather than pre-existing planted-clique machinery.

One reuse improvement is an extraction: the stable merge-sort/insertion-sort bridge formerly
private to the matroid greedy algorithm now lives in
[Foundations/Data/List/MergeSort.lean](../../Foundations/Data/List/MergeSort.lean).
The existing matroid client and the new selection/runtime proof use that shared lemma.
The circuit-testing layer also gains `isCircuitTest_iff_exists_circuit`, relating its existing
semantic test class to explicit De Morgan circuits.

The remaining analysis in
[#6238](https://github.com/cslib-community/cslib-frontier/issues/6238) is to sharpen the
second-eigenvector constants toward Algorithm A's $10\sqrt n$ threshold, including the
paper's preliminary size reduction. The every-$c$ native recovery theorem above uses the
integer solver and common-neighbor wrapper; the separate finite-precision second-eigenvector
program is certified in the explicit finite regime stated above.
