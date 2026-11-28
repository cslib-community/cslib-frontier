# Roadmap: Algorithms and optimization

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

### Optimization and duality

- **Linear programming:** a polynomial-time LP algorithm (ellipsoid or interior point) accounting for bit complexity and intermediate precision, and LP optimization as a search problem with rational outputs.
- **Simplex method** ([#3572](https://github.com/cslib-community/cslib-frontier/issues/3572)): Phase I (an initial feasible dictionary or an infeasibility certificate), and exponential lower bounds for pivot rules other than Dantzig's, such as Bland's (Avis–Chvátal 1978).
  Also smoothed analysis (Spielman–Teng), strongly polynomial special cases, and a costed implementation.
- **Ellipsoid method:** for a polynomial-time LP algorithm, a finite-precision central-cut update with its rounding error, a volume lower bound for full-dimensional rational polytopes, the reduction of feasibility to that case, and a machine-level running-time bound.
- **Extension complexity** ([#3611](https://github.com/cslib-community/cslib-frontier/issues/3611)): the facet form of Yannakakis's theorem (an extension with `r` facets, Fiorini–Massar–Pokutta–Tiwary–de Wolf Theorem 3 (ii)), semidefinite and conic extensions, and Rothvoß's lower bound for the perfect matching polytope.
- **Lattice basis reduction** ([#3235](https://github.com/cslib-community/cslib-frontier/issues/3235)): costs for the LLL algorithm, namely `O(n⁴ log B)` arithmetic operations and the `O(n log B)` bit-size bound of (1.26), giving polynomial-time statements for LLL and Babai's nearest-plane algorithm.
  Also Babai's algorithm with `δ` near `1` and rational targets.
  Applications include simultaneous Diophantine approximation and polynomial factorization over `ℚ`.
- **Separation and optimization:** a precise oracle interface and a separation–optimization equivalence with its representation, accuracy and well-boundedness hypotheses.
  Extend to convex optimization through explicit oracle and numerical-error contracts.
- **Lovász theta and perfect graphs** ([#2998](https://github.com/cslib-community/cslib-frontier/issues/2998)): the SDP and eigenvalue formulations of the theta function `ϑ` and their equivalence with the orthonormal-representation definition.
  Then its polynomial-time approximation by the ellipsoid method (Grötschel–Lovász–Schrijver), which makes clique number and chromatic number of perfect graphs polynomial-time computable, building on the separation–optimization interface.
- **Primal–dual approximation and multiplicative weights:** reusable primal–dual analyses with vertex cover and set cover as first clients, and multiplicative weights building on the experts regret bounds.
  Targets include randomized weighted majority and sampled Hedge as probabilistic computations, charged finite-precision implementations, and applications to packing and covering LPs and learning.
- **Online convex optimization:** online Newton step for exp-concave losses; follow-the-regularized-leader with time-varying regularizers and local-norm bounds; and entropic follow-the-regularized-leader recovering Hedge with `√(2T ln n)` regret.
  Also finite-precision implementations.

### Combinatorial optimization

Coordinate native graph-algorithm work with [CSLib's graph-algorithm directions](https://github.com/leanprover/cslib/blob/main/CONTRIBUTING.md#graph-algorithms-and-graph-foundations), reusing graph and matroid foundations and the shared data-structure interfaces.

- **Flows and matching:** weighted bipartite matching on rectangular and sparse instances and minimum-cost flow through common residual-network and duality machinery.
  Matching also covers the decomposition of `M ⊕ M*` into vertex-disjoint augmenting paths and a sparse Hopcroft–Karp entry point whose cost includes building the adjacency lists.
- **General matching** ([#3337](https://github.com/cslib-community/cslib-frontier/issues/3337)): unweighted and weighted matching in non-bipartite graphs with blossoms, through Edmonds' blossom-contraction lemma, with an executable blossom algorithm and its `O(|V|²|E|)` bound.
  Also the Gallai–Edmonds decomposition.
- **Chain decompositions:** the Greene–Kleitman theorem on `k`-chain and `k`-antichain families, Dilworth's theorem for infinite posets of finite width by compactness, the perfection of comparability graphs and their complements, weighted versions, and a sparse minimum chain cover entry point that charges building the comparability lists.
- **Global minimum cut:** the per-cut bound for the Karger–Stein recursive contraction algorithm, Stoer–Wagner in `O(n m + n² log n)` time, Nagamochi–Ibaraki sparse certificates for `k`-edge-connectivity and Karger's near-linear algorithm.
  Also the `O((2n)^(2α))` bound on `α`-minimal cuts and the enumeration and cactus representation of all minimum cuts.
- **Gomory–Hu trees:** an executable flow/cut oracle over `ℚ` for Gusfield's construction, and Word-RAM running times for its push–relabel and Dinitz instances.
- **Push–relabel maximum flow** ([#3373](https://github.com/cslib-community/cslib-frontier/issues/3373)): Word-RAM running times for current-arc scanning (`O(|V|² |E|)`), FIFO (`O(|V|³)`), highest-label (`O(|V|² √|E|)`), gap and global-relabelling heuristics, and dynamic trees (`O(|V| |E| log(|V|² / |E|))`).
- **Menger's theorem** ([#3409](https://github.com/cslib-community/cslib-frontier/issues/3409)): Menger for infinite graphs (the Erdős–Menger theorem, proved by Aharoni and Berger) and a native local or global `k`-connectivity test with a charged running-time bound.
- **Algebraic matching** ([#3052](https://github.com/cslib-community/cslib-frontier/issues/3052)): the Mulmuley–Vazirani–Vazirani algorithm for general graphs in its Pfaffian form, a machine-level running-time certificate for the Edmonds and Tutte determinant tests, and an RNC implementation.
- **Blocking-flow maximum flow:** a Word-RAM running time for Dinitz's algorithm with current-arc depth-first blocking-flow search (`O(|V| |E|)` per phase, `O(|V|^2 |E|)` overall).
  Also Sleator–Tarjan dynamic trees (`O(|V| |E| log |V|)`), the Even–Tarjan unit-capacity bounds `O(|E| · min(|V|^{2/3}, |E|^{1/2}))`, and Karzanov's `O(|V|^3)` preflows.
- **Auction algorithms** ([#3317](https://github.com/cslib-community/cslib-frontier/issues/3317)): `ε`-scaling for Bertsekas's auction with its `O(n A log (n C))` bound as a Word-RAM running time.
  Also the Jacobi, reverse and asymmetric auctions, sparse and rectangular instances, a bridge to the Hungarian method's potentials, and `ε`-relaxation for minimum-cost flow.
- **Graph search and shortest paths** ([#3053](https://github.com/cslib-community/cslib-frontier/issues/3053)): the Bellman–Ford predecessor tree, bridges and biconnectivity, linear-time acyclicity, and bridges to Dijkstra and matrix shortest paths.
- **Minimum-cost arborescences** ([#3526](https://github.com/cslib-community/cslib-frontier/issues/3526)): sparse `O(n m)` implementations of the Chu–Liu/Edmonds algorithm, Tarjan's `O(m log n)` and the Gabow–Galil–Spencer–Tarjan `O(m + n log n)` implementations, and Edmonds' branching polytope (Theorem 2).
- **Matroids** ([#2018](https://github.com/cslib-community/cslib-frontier/issues/2018)): a Word-RAM running time for the host computation of the exchange-graph matroid intersection solver, kept separate from its independence-oracle query counts.
  Extend to weighted matroid intersection.
- **Submodular optimization:** the `α/(p+α)` bound for greedy over `p`-systems with an `α`-approximate marginal-gain oracle, the continuous greedy with pipage rounding for `1 - 1/e` over a matroid, knapsack constraints and non-monotone objectives.
  Value-oracle and independence-oracle calls are charged separately from each other and from their concrete realizations.
- **Stable matching** ([#2990](https://github.com/cslib-community/cslib-frontier/issues/2990)): ties, rotations and the stable-matching poset, and stable roommates.
  A charged native implementation of deferred acceptance should run in `O(n^2)` time.
- **Housing markets and top trading cycles** ([#3286](https://github.com/cslib-community/cslib-frontier/issues/3286)): house allocation with existing tenants (Abdulkadiroğlu–Sönmez), indifferences (top trading absorbing sets), and a charged `O(n^2)` top trading cycles.
- **Interval dynamic programming:** the Hu–Tucker and Garsia–Wachs `O(n log n)` algorithms for alphabetic trees.
  Also matrix-chain multiplication and optimal polygon triangulation as instances of the generic interval recurrence, which in general fail the quadrangle-inequality hypotheses, Knuth's sharper candidate count, and SMAWK and Monge-matrix speedups.
- **Classical approximation algorithms** ([#2869](https://github.com/cslib-community/cslib-frontier/issues/2869)): machine-level polynomial-time certificates for greedy set cover and for Kruskal-based TSP tours on encoded matrices, and a polynomial-time minimum-weight perfect matching (Edmonds' blossom) for Christofides' `3/2` for metric TSP, with a tightness family approaching `3/2`.
  Also Karlin–Klein–Oveis Gharan's `3/2 - 10^{-36}`.
  LP-based and primal–dual analyses belong to the primal–dual direction.
- **Steiner tree:** Kou–Markowsky–Berman's leaf bound `2 (1 - 1/ℓ)` and their pruning steps; Zelikovsky's `11/6` and Robins–Zelikovsky's `1.55` greedy algorithms; and the Byrka–Grandoni–Rothvoß–Sanità LP-rounding bounds (`1.694` and `ln 4 + ε`).
  Also NP-hardness of the decision version (Karp, within [#2904](https://github.com/cslib-community/cslib-frontier/issues/2904)), even with unit weights by reduction from vertex cover, and a polynomial-time certificate for the heuristic with an executable shortest-path oracle.
- **Metric k-center:** a machine-level running time for Gonzalez's farthest-first 2-approximation, the Hochbaum–Shmoys threshold algorithm, k-supplier and k-median.
- **State-space search** ([#3669](https://github.com/cslib-community/cslib-frontier/issues/3669)): search problems and two-player games given implicitly by actions, results and goal or terminal tests, as in Russell and Norvig's *Artificial Intelligence: A Modern Approach*.
  Generic best-first search over an abstract frontier with its uninformed instances, A* with admissible and consistent heuristics, and minimax with alpha-beta pruning.
  Costs are node expansions and generations counted in CSLib's query model, including the bound that A* with a consistent heuristic expands each state at most once.

### Sorting and selection

- **Comparison selection** ([#3279](https://github.com/cslib-community/cslib-frontier/issues/3279)): sharper constants for median-of-medians selection in CSLib's comparison-query model (a six-comparison median of five, reusing the group comparisons in the partition) and group sizes such as three or seven.
  Also the `5.4305 n` bound for the refined `PICK` of Blum, Floyd, Pratt, Rivest and Tarjan, Dor and Zwick's `2.95 n` median bound, and a word-RAM implementation with charged instruction counts.
- **Comparison lower bounds for selection** ([#3279](https://github.com/cslib-community/cslib-frontier/issues/3279)): Kislitsyn's `n + ⌈log₂ n⌉ − 2` comparisons for the second smallest in CSLib's comparison-query model.
  Also lower bounds for the median and for general ranks, such as Bent and John's `2n − o(n)`.

### Online algorithms and competitive analysis

- **Competitive-analysis framework:** randomized online strategies against adaptive adversaries, distinguished from oblivious adversaries, in the same action and cost model.
- **Adaptive search trees:** for splay trees, Sleator–Tarjan's Unified Theorem and Cole's Dynamic Finger theorem; and a BST access-and-rotation model with Wilber-style lower bounds.
  State dynamic optimality as a conjectural research target with explicit strategy and sequence quantifiers.
- **Beyond deterministic ski rental and list update:** continuous-time randomized ski rental and the asymptotic `e/(e-1)` lower bound with an additive constant; randomized (BIT, COMB) and dynamic list update.
  Also McGeoch–Sleator's `H_k`-competitive partitioning algorithm for randomized paging.
- **Optimal stopping:** the tight i.i.d. prophet constant `≈0.745`, prophet secretary and random-order models, and matroid and multiple-choice prophet inequalities.
  Also the full-information secretary problem and a general mixtures theorem for randomized rules.
- **`k`-server** ([#3287](https://github.com/cslib-community/cslib-frontier/issues/3287)): the `k / (k - h + 1)` lower bound against `h < k` offline servers (Manasse–McGeoch–Sleator), `k`-competitiveness of Double Coverage on trees (Chrobak–Larmore), and the work-function algorithm's `2k - 1` bound (Koutsoupias–Papadimitriou).
  Also the `k`-server conjecture as a research target with explicit quantifiers, the `k = 2` case on every metric, randomized `k`-server, and the offline optimum by min-cost flow.
- **Online bin packing:** the stronger deterministic lower bounds of Brown–Liang (`1.536`), van Vliet (`1.5401`) and Balogh–Békési–Galambos (`248/161`) and the fully adaptive constructions; Harmonic-type upper bounds; and randomized lower bounds.
  Online bin packing should also be an instance of the competitive-analysis framework, charging `1` per opened bin, with online packers as deterministic strategies and a non-competitiveness corollary.

### Algorithmic game theory

- **Computing equilibria:** PLS-completeness of finding a pure Nash equilibrium of a congestion game (Fabrikant–Papadimitriou–Talwar), including the symmetric case, by reduction from local Max-Cut (PLS-complete by Schäffer–Yannakakis or by reductions from `LocalOpt`), through succinct game encodings; polynomial-time algorithms for symmetric network congestion games; exponentially long better-response paths.
  PPAD-completeness of computing mixed Nash equilibria of finite games.
- **Bimatrix games and Lemke–Howson** ([#3391](https://github.com/cslib-community/cslib-frontier/issues/3391)): extending the Lemke–Howson parity argument to degenerate bimatrix games by lexicographic perturbation; the Lemke–Howson path as a standalone algorithm; the Savani–von Stengel exponential lower bound.
- **Equilibrium concepts and dynamics:** last-iterate convergence of no-regret dynamics; bandit feedback and sampled play; convergence time of better-response dynamics in potential games.
- **Price of anarchy:** Wardrop equilibrium existence and essential uniqueness for continuous nondecreasing latencies (Beckmann's convex potential); worst-case networks for latency classes without the constant functions (parallel links and unions of paths); the M/M/1 and M/G/1 delay bounds (Roughgarden 2003); Braess's paradox.
- **Price of stability and potential games:** the tight price of stability of affine congestion games below `2`, and sharper general-`k` undirected and weighted network-design price-of-stability bounds.
  Strong Nash equilibria of fair cost-sharing games: their existence in special network classes (Epstein–Feldman–Mansour 2009) and a network without one; the Monderer–Shapley characterization of potential games as congestion games.

### Mechanism design ([#2947](https://github.com/cslib-community/cslib-frontier/issues/2947))

The directions below extend the single-parameter, Groves/VCG, optimal-auction and Bayes–Nash foundations in `GameTheory/Mechanism`, including revenue equivalence and the first-price equilibrium for i.i.d. uniform values.

- **Single-parameter corollaries:** the sponsored-search payment formula (rank-by-bid allocation with slot click-through rates) and the greedy knapsack rule with its monotonicity and ½-approximation.
  State allocation algorithms with charged running time, so that approximation and truthfulness are both proved for an actual algorithm.
- **Revenue maximization beyond the regular DSIC case:** ironing for irregular distributions, constructing the ironed virtual valuations instead of assuming them.
  Optimality over Bayesian incentive-compatible mechanisms, measurable virtual-welfare maximizers for finite feasible sets, and distributions without a bounded density (atoms, unbounded support).
- **Bayes–Nash equilibria of auctions:** the symmetric first-price equilibrium `b(v) = E[max of the other values | it is below v]` for general i.i.d. priors with densities and its uniqueness (Hartline, *Mechanism Design and Approximation*, §2.8–2.9); the all-pay auction; truthful bidding as a Bayes–Nash equilibrium of every DSIC mechanism.
  The exact optimal revenue `(n - 1 + 2^(-n)) / (n + 1)` for i.i.d. uniform values (`5/12` for two bidders).
- **Limits of VCG:** the limits of VCG on multi-parameter domains, such as the failure of revenue monotonicity and vulnerability to collusion.

### Social choice ([#3282](https://github.com/cslib-community/cslib-frontier/issues/3282))

Social welfare and social choice functions on strict rankings, from Arrow's impossibility theorem (Geanakoplos's pivotal-voter proof) onward.

- **Strategy-proofness beyond the full domain:** the Gibbard–Satterthwaite theorem allowing individual indifference, and Gibbard's 1977 theorem that strategy-proof random social choice functions are mixtures of unilateral and duple rules.
- **Quantitative Arrow** ([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)): Kalai's Fourier-analytic bound on the probability of a Condorcet paradox and its robust version via FKN.
- **Computational social choice:** polynomial-time manipulation of greedy-manipulable rules, NP-hardness of manipulating second-order Copeland (Bartholdi–Tovey–Trick 1989), and the complexity of winner determination for Dodgson and Kemeny rules, with explicit profile encodings and charged running time.

### Structural graph algorithms

- **Dynamic programming over tree decompositions** ([#2927](https://github.com/cslib-community/cslib-frontier/issues/2927)): a reusable evaluator over a supplied rooted decomposition with state-space, transition, join and runtime bounds.
  Clients: coloring and SAT decision and counting, each naming the graph whose width is measured; runtimes are stated in the number of vertices.
- **Treewidth structure** ([#2927](https://github.com/cslib-community/cslib-frontier/issues/2927)): an encoded treewidth parameter connected to `FPT`, treewidth under minors, and the grid and separator characterizations of treewidth.
- **Algorithmic metatheorems:** MSO-to-automata/evaluator compilation and a Courcelle-style theorem with computable parameter dependence on width and formula size.
  Keep the supplied decomposition and its encoding explicit; certify decomposition finding separately.
  Connect the evaluator to descriptive complexity, parameterized reductions and constraint networks.

### Sampling and approximate counting

- **Fixed-field sampling endpoints:** circuit output and output-count validation, native circuit-bound VOLE execution ([#2765](https://github.com/cslib-community/cslib-frontier/issues/2765), [#643](https://github.com/cslib-community/cslib-frontier/issues/643)), growing extension-field arithmetic, raw-bit adversarial transport ([#2744](https://github.com/cslib-community/cslib-frontier/issues/2744)) and fresh-session amplification.
- **Entropy-optimal sampling from fair coins:** the Knuth–Yao bounds `H(p) ≤ E[T]` for every DDG tree generating `p` and `E[T] < H(p) + 2` with optimality for the Knuth–Yao tree, and the dyadic equality characterization, for distributions with countable support and infinite entropy.
  For rational `p`, the Knuth–Yao sampler as a native fair-coin program with certified output law and expected time (an `IsPPTOn`-style certificate in expected time), as in the finite-precision entropy-optimal samplers of Saad, Freer, Rinard and Mansinghka.
- **Markov-chain sampling** ([#2857](https://github.com/cslib-community/cslib-frontier/issues/2857)): total-variation mixing bounds by conductance and canonical paths, and an FPRAS for colorings in the sense of `Classes/FPRAS`, charging the estimator's Glauber updates.
  Implement Metropolis sampling for encoded rational target weights, charging initialization, arithmetic and every transition, with support and mixing hypotheses explicit.
- **FPRAS and almost-uniform sampling:** the Jerrum–Valiant–Vazirani equivalence of FPRAS and FPAUS for self-reductions fixing several symbols per step.
  Also Sinclair and Jerrum's reduction from polynomial-error counting.
  Instantiate both directions for concrete relations such as DNF assignments.
- **Approximate counting of matchings and permanents:** randomized approximate counting for matchings and permanents of nonnegative rational matrices through explicit mixing and reduction theorems.
  Reuse the coupling and expander APIs and connect to the separate Stockmeyer oracle-counting track where their hypotheses agree.
- **Permanent bounds:** extensions of Brégman's upper bound to nonnegative real matrices (for example Soules 2000).
  The van der Waerden lower bound for doubly stochastic matrices (Egorychev–Falikman, or Gurvits's capacity proof), the Kahn–Lovász bound for perfect matchings of general graphs, and their use in approximate-counting analyses.

### Constructive probabilistic methods

- **Talagrand thinning consequences** ([#4330](https://github.com/cslib-community/cslib-frontier/issues/4330)): use the thinning corollary in [#2525](https://github.com/cslib-community/cslib-frontier/pull/2525) to establish Conjecture 7.8, then apply the finite spread and smallness reductions to Conjectures 7.3 and 7.11.
- **Planted-clique recovery** ([#6238](https://github.com/cslib-community/cslib-frontier/issues/6238)): certify a finite-precision realization of the raw-adjacency second-eigenvector algorithm in the native computation model, and sharpen its constants to match Alon–Krivelevich–Sudakov.
  See the [proof and module guide](../CslibFrontier/Algorithms/PlantedClique/README.md).
- **Moser–Tardos resampling** ([#3096](https://github.com/cslib-community/cslib-frontier/issues/3096)): the derandomized algorithm of Theorem 1.4, and native sampling and event-detection costs for the resampling algorithms.
  Build the Kolmogorov form's decoder as a multi-tape machine taking the formula, transferring it to `condPlain`.
- **Conditional expectations and pessimistic estimators:** algorithmic alteration, and coloring or combinatorial-construction clients of the certified greedy choice rule for pessimistic estimators.
  Preserve the quantitative guarantee when converting an existence argument into a deterministic or randomized algorithm.
- **Small sample spaces** ([#2935](https://github.com/cslib-community/cslib-frontier/issues/2935)): a polynomial-time certificate for searching the trinomial-field `k`-wise independent space for fixed `k > 3` for an assignment as good as a uniformly random one on clauses of at least `k` distinct literals.
  Extend to small-bias and almost `k`-wise independent spaces and their clients.

### Randomized verification and fingerprinting

- **Fingerprinting** ([#2980](https://github.com/cslib-community/cslib-frontier/issues/2980)): Karp–Rabin fingerprints (a random evaluation point over a finite field, or a random prime modulus with explicit prime-counting bounds), a rolling-hash pattern matcher with charged updates and a union bound over all windows, and the private-coin `O(log n)` equality protocol.
  Native machine or RAM realizations with bit-level arithmetic costs are a separate endpoint.

### String algorithms

- **Burrows–Wheeler transform:** a Word-RAM running time for the forward transform.
  Move-to-front and entropy coding of the last column, compression bounds in the empirical entropy `H_k` (Manzini), FM-index backward search and rank/select structures, and the link to suffix arrays for sentinel-terminated words.
- **Suffix arrays:** charged linear-time construction for integer alphabets (SA-IS or Kärkkäinen–Sanders DC3), Manber–Myers `O(|p| + log n)` search using precomputed LCP values, suffix trees (Ukkonen or McCreight) and their equivalence to suffix arrays with LCP arrays, and applications such as longest repeated substring and the Burrows–Wheeler transform.
- **Z-algorithm:** linear conversions between Z-values and the KMP prefix function and applications such as Main–Lorentz repetition finding.
- **Multi-pattern matching:** compressed or comparison-based Aho–Corasick transitions for sparse or unbounded alphabets, dynamic dictionary matching and Turing-machine realizations.
- **Edit distance and longest common subsequence:** for unit costs, the metric axioms and equality with the least number of single-letter edits; Wagner–Fischer's trace equivalence for general costs; Hirschberg's linear-space alignment; a machine-level polynomial-time computation; Ukkonen's and Myers' `O((|x| + |y|) d)` algorithms; the Masek–Paterson speedup; and `OV` hardness ([#3037](https://github.com/cslib-community/cslib-frontier/issues/3037)).
- **Palindromes:** Manacher's on-line formulation, reporting palindromic prefixes as letters arrive with a per-letter amortized bound; palindromic trees (eertrees) and counting distinct palindromic factors, of which there are at most `|w| + 1`; and the parallel algorithms of Apostolico, Breslauer and Galil.
