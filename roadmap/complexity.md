# Roadmap: Complexity classes and reductions

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

### Coverage catalogue

Build an auditable coverage index of the [Complexity Zoo](https://complexityzoo.net/Complexity_Zoo) and canonical problems and theorems ECCC papers need, verified against primary sources and linked to canonical definitions ([#6741](https://github.com/cslib-community/cslib-frontier/issues/6741), [#6641](https://github.com/cslib-community/cslib-frontier/issues/6641)).
Each entry records source, aliases, model, conventions (uniformity, advice, oracle access, error gaps, resources, reduction type), Lean declarations, missing prerequisites and level, from definition to verified theorem.
Containments, separations, closure properties, complete problems and reductions are tracked separately across decision, function, search, counting, promise, distributional and parameterized problems.

### Structure, time and space

- **Real-algebraic counting bounds** ([#6560](https://github.com/cslib-community/cslib-frontier/issues/6560)): port lean-canny's ETR/∃ℝ containment in C₂₆P and existential–universal real truth in C₆₀P, with PSPACE corollaries.
  Extract reusable implicit-polynomial, coefficient and trace algorithms while preserving uniformity, encodings and full evaluator costs.
- **Planar Boolean CSP dichotomy** ([#3091](https://github.com/cslib-community/cslib-frontier/issues/3091)): extend the native Boolean classification to ordered planar instances of arbitrary fixed relation arity, preserving individual incidence occurrences and cyclic argument order.
  The endpoint must prove the embedding and recognition interface, the cyclic-difference reduction, the even delta-matroid edge-CSP algorithm and planar hardness transfer internally, including the additional self-complementary tractable family.
  Supplied-embedding or matching-realizable-only milestones leave it open.
- **Context-free languages**: conversion of an arbitrary grammar to Chomsky normal form with its size blow-up, giving decidability of every context-free language, and a machine-level polynomial-time decider for each fixed grammar (CFL ⊆ P, Sipser Theorem 7.16).
  Also Valiant's subcubic parsing by Boolean matrix multiplication, the pumping lemma with non-context-freeness of `{aⁿbⁿcⁿ}`, and CFG emptiness in P versus undecidable universality.
- **Abstract (Blum) complexity** ([#2866](https://github.com/cslib-community/cslib-frontier/issues/2866)): the compression theorem in running-time form, one computable `h` with `C_{Φ_i} ⊂ C_{n ↦ h n (Φ_i n)}` for every total `φ_i`; the value form is false by the gap theorem.
  Also `g`-honesty for partial functions (Odifreddi II, Exercises VII.2.14b–d), effective speedup (Blum's pseudo-speedup), and native multitape time and space as Blum measures.
- **Busy beaver** ([#3314](https://github.com/cslib-community/cslib-frontier/issues/3314)): Radó's `Σ(n)` and `S(n)` for Turing machines counted by states, with a simulation bridge to the `Nat.Partrec.Code` version and the known small values (`S(5) = 47,176,870`, from the bbchallenge Coq proof) as a cross-check.
  Also independence of busy beaver values from ZFC (Aaronson–Yedidia) and the connection to Chaitin's `Ω`.
- **Post's correspondence problem**: Sipser's computation-history reduction from the acceptance problem of an arbitrary machine, decidability of unary PCP and of PCP with two dominoes (Ehrenfeucht–Karhumäki–Rozenberg, 1982), and undecidability with five dominoes (Neary, 2015).
  Also the consequences for ambiguity, universality and intersection emptiness of context-free grammars and for mortality of 3×3 integer matrices (Paterson, 1970).
- **Degrees of unsolvability** ([#3379](https://github.com/cslib-community/cslib-frontier/issues/3379)): a general relativized jump operator (reconciled with [mathlib4#38973](https://github.com/leanprover-community/mathlib4/pull/38973)), the Friedberg–Muchnik theorem by finite injury, Sacks splitting and density of the c.e. degrees, and Spector's minimal degree.
- **Time hierarchies** ([#1572](https://github.com/cslib-community/cslib-frontier/issues/1572)): separations of noninteger polynomial degrees and the textbook `f log f = o(g)` hierarchy ([#4211](https://github.com/cslib-community/cslib-frontier/issues/4211)) from the `O(t log t)` universal simulation.
  Also a word-RAM hierarchy by direct diagonalization with a gap smaller than `T` versus `T⁵`, sharp nondeterministic ([#4213](https://github.com/cslib-community/cslib-frontier/issues/4213)) and alternating time hierarchies with certified simulators, `(log t)^ε` gaps for general time-constructible `t`, and W. J. Paul's fixed-tape hierarchy (1979).
- **Probabilistic time hierarchies** ([#2084](https://github.com/cslib-community/cslib-frontier/issues/2084)): the `PromiseBPTIME` hierarchy for promise problems by delayed diagonalization, following He (ECCC TR25-004), and the one-bit-advice hierarchy for languages of van Melkebeek and Pervyshev.
  The advice-free hierarchy for `BPTIME` itself is open and is not a target.
- **Randomized primality tests** ([#2958](https://github.com/cslib-community/cslib-frontier/issues/2958)): an explicit Solovay–Strassen verifier putting the primes in `coRP` via the polynomial-time Jacobi symbol and a gcd step, since non-units can satisfy Euler's congruence.
- **Catalytic space and KMPS collapses** ([#2521](https://github.com/cslib-community/cslib-frontier/issues/2521)): native `CSPACE(s,c)` with nondeterministic and randomized variants, restoring the catalyst on every branch.
  Koucký–Mertz–Pyne–Sami's [*Collapsing Catalytic Classes*](https://arxiv.org/abs/2504.08444) with its parameter ranges and oracle promises: `CL = CNL = CPrL = CBPL`, compress-or-compute simulation, catalytic Savitch and complementation, randomized space–catalyst tradeoffs, hierarchy collapses and lossy-space consequences.
- **Robust catalytic extensions** ([#2521](https://github.com/cslib-community/cslib-frontier/issues/2521)): the Koucký–Mertz–Sami [robust catalytic extensions](https://arxiv.org/abs/2605.09648) beyond KMPS.
  Their broader collapse is conditional on an explicit circuit-hardness assumption, and their resetting-error and time regimes are kept distinct from the unconditional KMPS results.
- **Classical randomized-space proof reuse** ([#7602](https://github.com/cslib-community/cslib-frontier/issues/7602)): derive `NSPACE_subset_DSPACE_sq` and `RL ⊆ NL ⊆ DSPACE(log² n)` through the space calculus's midpoint recursion rule, replacing the hand-built Savitch stack machines while preserving encodings and workspace bounds.
- **Further classical randomized logspace** ([#459](https://github.com/cslib-community/cslib-frontier/issues/459)): two-sided `BPL` amplification, the random-walk proof of `USTCON ∈ RL`, and Saks–Zhou's `BPL ⊆ DSPACE(log^{3/2} n)`.
- **Reingold:** a symmetric-machine model of SL, and the edge-list encoding of USTCON by a logspace reduction.
- **Cook–Mertz Tree Evaluation refinements** ([#2855](https://github.com/cslib-community/cslib-frontier/issues/2855)): Cook–Mertz malformed-input handling for Tree Evaluation and the refined `O(ℓ + H log(ℓ + 2))` space bound.
- **Time–space lower bounds for nondeterministic linear time** ([#2896](https://github.com/cslib-community/cslib-frontier/issues/2896)): the Arora–Barak bound `NTIME(n) ⊄ TISP(n^1.2, n^0.2)` by virtual padding and the Lipton–Viglas `n^(√2 − ε)` form, from the speedup and slowdown lemmas for `TISP` and `Σ₂TIME`.
  Also the textbook `√(t·s)` speedup, the golden-ratio deterministic bound of Fortnow, Lipton, van Melkebeek and Viglas, and the transfer to SAT through a quasi-linear-size Cook–Levin reduction ([#4225](https://github.com/cslib-community/cslib-frontier/issues/4225)).
- **Alternating classes** ([#4086](https://github.com/cslib-community/cslib-frontier/issues/4086)): the Chandra–Kozen–Stockmeyer bridges `NSPACE s ⊆ ATIME (s ^ 2)` without a time-constructibility hypothesis on `s` and `DTIME (2 ^ O(s)) ⊆ ASPACE s` without a space-constructibility hypothesis, bounded-alternation characterizations of PH, and sharp bounds for sublinear space, distinct from polynomial-space simulation.
- **Unambiguous space** ([#7185](https://github.com/cslib-community/cslib-frontier/issues/7185)): `NSPACE(s) = USPACE(s)` for every bound `s ≥ log₂ n`, without space-constructibility, for native machines and arbitrary injective input encodings.
  Run the Justesen seed scheduler on configuration graphs of growing radix, for a decider and for its Immerman–Szelepcsényi complement, until one of the two accepts.
  This needs the scheduler's size bounds uniformly in the radix exponent.
- **Fast alternating counting simulation** ([#4728](https://github.com/cslib-community/cslib-frontier/issues/4728)): clocked bitwise accepting-path counting through tensor contraction in alternating time `O(n + t / sqrt(log(t+2)))`.
  Locally accessible contraction expressions, certified index and arithmetic costs, and the count-preserving machine reduction.
  Input access and clock computation must be charged explicitly.
- **Pebble games and space lower bounds** ([#2995](https://github.com/cslib-community/cslib-frontier/issues/2995)): black-white pebbling on digraphs with exact prices, erasure and time–space trade-offs for reversible pebbling of the path including whether `3 ^ k` is optimal for `k + 1` pebbles ([#3199](https://github.com/cslib-community/cslib-frontier/issues/3199)), the Hopcroft–Paul–Valiant `O(n / log n)` bound ([#3573](https://github.com/cslib-community/cslib-frontier/issues/3573)) with the matching Paul–Tarjan–Celoni family, and Gilbert–Tarjan and Lengauer–Tarjan trade-offs.
- **Deeper consequences of a Boolean-hierarchy collapse:** Kadin's sparse `S` with `coNP ⊆ NP^S`, and the collapse of `PH` into `P^{NP^{NP}[O(log n)]} ⊆ Δ₃ᴾ`, which follows from results of Wagner and of Chang and Kadin, not from Kadin's 1988 argument (see his erratum).
- **Explicit universal SAT solver** ([#7906](https://github.com/cslib-community/cslib-frontier/issues/7906)): investigate whether one fixed native total SAT decision procedure, halting on unsatisfiable inputs as well, runs in worst-case polynomial time if and only if `P = NP`, or formalize total variants under explicit stronger hypotheses (a known exponent bound or polynomially bounded Frege proofs) accounting for dovetailing, certificate checking and universal simulation overhead.

### Reducibilities and the structure of complete sets

- **Reducibilities** ([#1351](https://github.com/cslib-community/cslib-frontier/issues/1351)): logspace Turing reductions, in an oracle model whose query tape is not charged to the space bound, and their transitivity; the rest of the inclusion hierarchy of Ladner, Lynch and Selman, and its separations.
- **Sparse and tally sets**: Kadin's stronger form with a sparse `S ∈ NP` and `coNP ⊆ NP^S`, and `P^{NP[O(log n)]} = P^NP_tt` (Hemachandra).
- **Berman–Hartmanis:** paddability of the standard NP-complete graph, number and set problems, hence their p-isomorphism to SAT; every many-one complete set for EXP is complete under one-one, length-increasing reductions (Berman); and the isomorphism theorem for sets complete under AC⁰ reductions (Agrawal, Allender and Rudich).
- **Autoreducibility and mitoticity** ([#1351](https://github.com/cslib-community/cslib-frontier/issues/1351)): for nontrivial sets, `m`-autoreducible equals `m`-mitotic, so every NP-complete set splits into two NP-complete sets (Glaßer, Pavan, Selman and Zhang); separations of complexity classes by autoreducibility (Buhrman, Fortnow, van Melkebeek and Torenvliet).
- **Logspace autoreducibility of complete sets** ([#2468](https://github.com/cslib-community/cslib-frontier/issues/2468)): the full expanded 2013 paper of Glaßer, Nguyen, Reitwießner, Selman and Witek: Lemma 3.3's transfer from local self-reducibility with answer regeneration and adaptive-to-tt conversion, its bounded and many-one cases, Theorem 3.5, and Sections 4 and 5 (query bounds, separations, mitoticity, diagonalization).
  The parity-logspace application needs native path counting and complement closure.
- **Selectivity and downward self-reducibility:** downward self-reducible sets lie in PSPACE, self-reducible P-selective sets lie in P, and P-selective sets are not `≤ₜₜᵖ`-hard for NP unless P = NP.
- **Low and high hierarchies in NP** (Schöning): sparse NP sets lie in `Low₂` (Ko and Schöning), and so does graph isomorphism, via graph non-isomorphism in AM.
- **Immunity**: complexity cores for `PSPACE`, core density (Orponen–Schöning) and core sizes (Juedes–Lutz).
  Also `DTIME(t)`-bi-immunity for constructible `t`, further Balcázar–Schöning results, almost-everywhere hardness, and Mayordomo's measure results.
- **Exponential-time complete problems**: succinct circuit value for `EXP` and succinct SAT for `NEXP`, generalized games complete for `EXP`, and the isomorphism and density structure of `E`-complete sets.

### Average-case complexity

- **Distributional framework** ([#2865](https://github.com/cslib-community/cslib-frontier/issues/2865)): samplability of polynomial-time computable ensembles, Levin's runtime-moment average polynomial time and its relation to errorless schemes, and randomized average-case classes.
  Probability-zero instances obstruct a literal equivalence with errorless schemes.
- **Heuristic hierarchy and universal distributions** ([#2865](https://github.com/cslib-community/cslib-frontier/issues/2865)): `(BH, U^BH) ∈ Heur_{1/n} P` gives `DistNP ⊆ HeurP`, with the `Avg` analogue (Bogdanov–Trevisan Prop. 21), via a fixed clocked universal program on inputs `(c, z, 1^t)`, since the source's padding can change `BH` membership.
  Also Levin, Li and Vitányi (Bogdanov–Trevisan Thm 16): under `K_n(x) ∝ 2^{-C(x)}` on each length, a decidable `L` with `(L, K) ∈ Heur_{1/n³} P` is in `P`.
- **Completeness beyond computable ensembles** ([#2865](https://github.com/cslib-community/cslib-frontier/issues/2865)): extend bounded-halting completeness for `DistNP` to samplable distributions (Impagliazzo–Levin, `SampNP`), and bridge the verifier-form bounded halting problem to a nondeterministic machine model.
  Connect the framework to one-way functions, learning and the metacomplexity track ([#798](https://github.com/cslib-community/cslib-frontier/issues/798)), preserving the distribution and reduction conventions.

### Counting and modular classes

- **Another Solution Problem (ASP) framework:** ASP reductions with certified polynomial-time forward and inverse witness maps, starting from the parsimonious reductions to positive exact-one SAT and its planar three-occurrence variants.
  Exact count preservation alone does not supply the ASP runtime certificates.
- **Exact counting by determinants** ([#3081](https://github.com/cslib-community/cslib-frontier/issues/3081)): Kasteleyn's Pfaffian method for counting perfect matchings of planar graphs in polynomial time, in contrast with permanent #P-completeness.
- **Target-relativized counting classes:** `LWPP^A`, `WPP^A` and `SBP^A` with `FP^A` targets; adaptive WPP closure and UP-oracle containment.
- **Native oracle counting machines:** efficient encoded oracle checking, response-access costs and oracle-machine characterizations, with resource bounds uniform over admissible oracles.

### Interactive proofs

- **GKR verifier under log-space uniformity** ([#892](https://github.com/cslib-community/cslib-frontier/issues/892)): certify the running time of the uniform verifier.
- **Arthur–Merlin classes:** the Babai–Moran speedup `AM[2 t(n)] = AM[t(n)]` for polynomially many rounds (patterns that depend on the input length), interactive-machine characterizations of Arthur–Merlin classes, and perfect zero knowledge.
- **Debate protocols** ([#7579](https://github.com/cslib-community/cslib-frontier/issues/7579)): competing provers with bounded honest strategies, starting from doubly-efficient debate with a stochastic oracle (Brown-Cohen, Irving and Piliouras, arXiv:2311.14125, Section 6).
  The endpoint is the cross-examination protocol for encoded machines, with prover time, verifier time and verifier query bounds, under a Lipschitz hypothesis whose exact form is settled in the issue.
  Correctness for a prefix-indexed step law alone leaves it open.
  Then prover-estimator debate (arXiv:2506.13609).
- **Statistical zero knowledge** ([#3205](https://github.com/cslib-community/cslib-frontier/issues/3205)): interactive honest-verifier and general SZK with simulators and equivalence with `PromiseSZK`, giving `SD` membership and completeness in the interactive sense, Entropy Difference (Goldreich–Vadhan), closure under complement (Okamoto), and `SZK ⊆ coAM` (Fortnow). The `SZK ⊆ AM` inclusion uses the Statistical Difference definition.
  Instances are pairs of De Morgan circuits, with general pairs padded to common input and output counts.

### Descriptive complexity and first-order reductions

Ordered first-order complexity follows Immerman: structures on {0, …, n-1} with n ≥ 2, FO means FO(≤, BIT), and `≤_fo`, `≤_fop` and `≤_qfp` keep their standard meanings; the order-free `FO.Reduces` and `FO.QFReduces` stay as a general layer.
Numeric predicates are computed from the universe size, not supplied as unverified input tables.

- **Projection refinements** ([#4394](https://github.com/cslib-community/cslib-frontier/issues/4394)): first-order and quantifier-free projection refinements (`≤_fop`, `≤_qfp`) of ordered `REACH` `NL`-completeness, and order-free projection reducibility on arbitrary finite structure classes.
- **Circuit Value P-completeness** ([#1245](https://github.com/cslib-community/cslib-frontier/issues/1245)): Circuit Value is P-complete under first-order reductions, via `REACHa → MCVP → CVP` (Immerman, Theorem 3.26 and Exercise 3.28), the first-order alternating-logspace simulation of polynomial-time machines, and the translation to `encCircuitValue`.
- **Native NL closure facts:** NL^NL = NL.
- **Further logical characterizations:** on ordered structures, DLOGTIME-uniform AC⁰ = FO(≤, BIT) (Barrington–Immerman–Straubing); then order-invariant and fixed-point queries and uniform translations between syntax, structures and algorithms.
- **Logical lower-bound methods**: Ehrenfeucht–Fraïssé games with constants, Gaifman's normal form, and fixed-point expressiveness with Cai–Fürer–Immerman separations, linked to the ordered capture theorems, where FO(≤, BIT) defines EVEN.
- **Nondefinability applications**: Libkin's balanced binary trees and same generation, planarity, Hamiltonicity and `k`-colorability for `k ≥ 3`.
- **Undecidability in the finite:** Trakhtenbrot's theorem and the finite-satisfiability dichotomy for Mathlib's `L.Sentence` over infinite vocabularies (with a primitive recursive arity map) and languages with function symbols.
- **Logic and automata on words**: FO[<] = star-free = aperiodic via Schützenberger's theorem, with decidability of first-order definability for regular languages.
  Also homomorphic-image closure of regular languages (upstream to CSLib), the non-elementary formula-to-automaton lower bound, Büchi's theorem for ω-words (S1S), and MSO on finite trees (Thatcher–Wright, Doner) and infinite trees (Rabin, S2S).
- **Asymptotic probabilities** ([#4080](https://github.com/cslib-community/cslib-frontier/issues/4080)): 0-1 laws for unlabelled structures and for classes defined by parametric axioms such as the simple-graph axioms.
  Also embeddings from fixed-point and transitive-closure logics into `L^ω_∞ω` for the fixed-point Kolaitis–Vardi 0-1 laws, and the Shelah–Spencer laws for sparse random graphs.
- **Dynamic descriptive complexity:** dynamic programs and update semantics with explicit initialization, auxiliary relations and domain conventions; invariant-preservation rules and reachability in DynFO as a target.
  Relate logical update restrictions to the stateful-algorithm interfaces through explicit translations.
- **Color refinement and Weisfeiler–Leman**: equitable partitions as fractional automorphisms and isomorphisms (Tinhofer; Ramana–Scheinerman–Ullman; Grohe–Kersting–Mladenov–Selman, Theorems 4.1 and 5.2), and certified polynomial-time algorithms for 1-WL and `k`-WL.
  Also `k`-WL with arbitrary initial tuple colorings, linear-size expander Cai–Fürer–Immerman graphs, and embeddings of fixed-point logics into `L^k_∞ω`.
- **Vollmer's generalized quantifier framework** ([#399](https://github.com/cslib-community/cslib-frontier/issues/399)): Vollmer's survey [*A Generalized Quantifier Concept in Computational Complexity Theory*](https://arxiv.org/abs/cs/9809115), covering ordered leaf words, explicit uniformity and input-access models, finite-monoid classification and generalized logical quantifiers.
  The formalization must keep the paper's resource models and quantifier bounds.

### Uniform circuit families

Define logspace and DLOGTIME uniformity with explicit gate-address, direct-connection and input encodings; certify circuit generation, evaluation and the machine-to-circuit simulations ([#4224](https://github.com/cslib-community/cslib-frontier/issues/4224)), preserving size, depth and construction resources; and prove FO with order and BIT equals DLOGTIME-uniform AC⁰ under explicit conventions.

### Search, parameterized and fine-grained complexity

- **TFNP:** CLS, further local search, fixed-point and equilibrium problems.
- **Unique end of potential line**: `UEOPL` and its inclusions into `EOPL` (Fearnley et al. 2020; Göös et al. 2022).
- **`PPAD`-completeness of Sperner and Brouwer** ([#3087](https://github.com/cslib-community/cslib-frontier/issues/3087)): `PPAD` membership of circuit `d`-dimensional Sperner and `Brouwer^f` through an oriented door graph, `PPAD`-hardness of two-dimensional discrete Brouwer (Chen–Deng), and `PPAD`-completeness of three-dimensional Sperner and Brouwer (Papadimitriou 1994; Daskalakis–Goldberg–Papadimitriou).
- **Brouwer's fixed-point theorem**: arbitrary compact convex subsets of `Fin n → ℝ` by retraction onto the cube or a simplex.
- **Parameterized:** strongly uniform variants (computable `f`) and further explicit polynomial kernels; connect these to [structural graph algorithms](algorithms.md#structural-graph-algorithms) and their decomposition costs.
- **Crown decompositions**: a polynomial-time crown finder (maximum matching or Kőnig cover in the machine model) giving a kernelization of the encoded `VertexCover` with `O(k)` vertices, the LP-based `2k` kernel by Nemhauser–Trotter, and the expansion lemma (`q`-expansions) with its kernels.
- **Iterative compression**: Hüffner's `O(3^k · k m n)` and `O(3^k · m n)` odd cycle transversal bounds (at most `k + 1` augmenting paths on adjacency lists, then incremental flow updates), and encoded `OddCycleTransversal ∈ FPT` on multi-tape machines.
  Also the `O*(2.3146^k)` LP-based algorithm (Lokshtanov–Narayanaswamy–Raman–Ramanujan–Saurabh), feedback vertex set and directed variants.
- **Kernelization lower bounds** ([#3266](https://github.com/cslib-community/cslib-frontier/issues/3266)): concrete bounds such as Clique parameterized by vertex cover, cross-compositions of bounded cost and the complementary witness lemma, and AND-composition (Drucker).
- **Color coding** ([#2870](https://github.com/cslib-community/cslib-frontier/issues/2870)): the one-sided-error randomized fpt algorithm for `LongPath` by random colorings (a fixed `k`-set is colorful with probability `K.descFactorial k / K ^ k ≥ e ^ (-k)`), and its derandomization by perfect hash families.
- **W-hierarchy** ([#3256](https://github.com/cslib-community/cslib-frontier/issues/3256)): `W[2]`-completeness of Dominating Set, `W[1]`-completeness of short Turing machine acceptance, `W[P]` under effective fpt-reductions, and the A-hierarchy.
- **Exact exponential algorithms** ([#3013](https://github.com/cslib-community/cslib-frontier/issues/3013), [#3672](https://github.com/cslib-community/cslib-frontier/issues/3672)): a polynomial space bound for inclusion–exclusion Hamiltonian path counting in a model that measures space, and further exact exponential algorithms such as fast subset convolution and inclusion–exclusion colouring.
- **Fine-grained hypotheses after ETH** ([#8457](https://github.com/cslib-community/cslib-frontier/issues/8457)): develop the Satisfiability Hypothesis framework to recover conditional lower bounds whose `ETH` and `SETH` premises are refuted, and prove further fine-grained reductions from open hypotheses (`OVH`, `APSP`, `3SUM`).
- **3SUM via selected-entries subset convolution** ([#4667](https://github.com/cslib-community/cslib-frontier/issues/4667)): STOC submission 1421 (Chan–Itakura–Ma–Yu): the hashing reduction of integer 3SUM to selected entries of ranked subset convolution (Theorem 2.3) and the randomized `n^1.965` algorithm (Corollary 2.4), selected-entries convolution in `[r]^d` and the `O(n^(⌈k/2⌉ - ε_k))` algorithm for odd k-SUM (Section 3), and the deterministic reductions of real 3SUM and real APSP to #AE sparse triangle (Sections 4–5).
- **APSP class** ([#3076](https://github.com/cslib-community/cslib-frontier/issues/3076)): equivalences of APSP with minimum-weight cycle, replacement paths, metricity and (min,+) product verification (Vassilevska Williams–Williams), and with radius and median (Abboud–Grandoni–Vassilevska Williams, SODA 2015).
  Also `-∞` weights, general (min,⊙) structures and output-sensitive listing (Vassilevska Williams–Williams Theorem 4.3) for negative triangle, word-RAM realizations with bit-length costs and Kerr's `Ω(n³)` bound for (min,+) straight-line programs; Bellman–Ford with negative-cycle reporting is [#3053](https://github.com/cslib-community/cslib-frontier/issues/3053).
- **Reductions from orthogonal vectors** ([#3037](https://github.com/cslib-community/cslib-frontier/issues/3037)): the `(3/2 - ε)`-approximation corollary for diameter (Roditty–Vassilevska Williams Theorem 9), the sparse `m ^ (2 - ε)` bound from low-dimension `OVH` (dimension `c log N`), and `OV` hardness of LCS and edit distance by alignment gadgets (Backurs–Indyk; Abboud–Backurs–Vassilevska Williams; Bringmann–Künnemann).

### Approximation and PCP

- **Håstad's optimal MAX-E3SAT hardness** ([#8364](https://github.com/cslib-community/cslib-frontier/issues/8364)): for `0 < ε < 1/8`, NP-hardness of distinguishing satisfiable E3-CNF formulas from those where every assignment satisfies at most `7/8 + ε` of the clauses (Theorem 6.5), via the perfect-completeness test of Section 6.
- **MAX 2-SAT**: APX-hardness with explicit inapproximability constants, and a gap-preserving reduction from MAX 2-SAT to unweighted MAX CUT.
- **Approximation classes and gap reductions:** `APX` and `APX`-completeness, CSP approximation classifications and relaxation gaps, and the 2-to-2 games theorem, with assumptions such as the Unique Games Conjecture stated explicitly.
- **Approximation algorithms** ([#3230](https://github.com/cslib-community/cslib-frontier/issues/3230)): a general interface for approximation ratios of optimization problems connecting polynomial-time algorithms and matching hardness results, and further LP and SDP rounding algorithms.
  Goemans–Williamson needs polynomial-time SDP solving with precision accounting, a `ProbComp` realization of the Gaussian sample, the Feige–Schechtman tightness gap, the Section 7.2.2 MAX-SAT LP/SDP hybrid, and derandomization.
- **Packing approximation** ([#2964](https://github.com/cslib-community/cslib-frontier/issues/2964)): the asymptotic approximation scheme for bin packing of Fernandez de la Vega and Lueker, Dósa and Sgall's absolute bound `FF ≤ ⌊17/10 * OPT⌋` for First Fit with their matching lower-bound instances, First Fit Decreasing's `11/9` bound and Lawler's faster knapsack FPTAS.
- **Scheduling** ([#2909](https://github.com/cslib-community/cslib-frontier/issues/2909)): real-valued processing times under precedence constraints, Graham's anomaly instances as checked examples, a general tight family for LPT, the Hochbaum–Shmoys PTAS for `P || C_max`, and runtime bounds for `listSchedule` and `lptSchedule`.
- **A practical PCP construction:** cost of the encoded PCP construction on complete reductions, rotation certificates polynomial in the bit length of a vertex name, and machine-level error reduction and extractors from expander walks with certified seed and evaluation costs.

### Proof complexity

- **Proof space**: total and variable space for resolution, clause-space lower bounds for random `k`-CNFs, time–space trade-offs for pebbling formulas, and degree versus space in polynomial calculus.
- **Sum-of-squares**: converse pseudo-expectation duality, and the Lasserre and Sherali–Adams hierarchies with a bridge to the proof system.
  Also Grigoriev's `Ω(n)` degree lower bound for random `3`-XOR (Barak–Steurer Theorem 2) with Schoenebeck's gaps for CSPs implied by XOR, size–degree relations and size lower bounds.
- **Positivstellensatz refutations**: the `0/1` encoding and Grigoriev's knapsack bound through pseudo-expectations, and the dynamic Positivstellensatz calculus and the Lovász–Schrijver systems of Grigoriev–Hirsch–Pasechnik, compared with the static form.
- **Tree-like resolution**: the asymptotic `2 ^ Θ(n log n)` tree-like size of `PHP^m_n`, `m > n`, with the matching `2 ^ O(n log n)` upper bound (Dantchev–Riis), the functional pigeonhole principle, and a tree-like versus general resolution separation (Ben-Sasson–Impagliazzo–Wigderson).
- **Polynomial calculus** ([#3542](https://github.com/cslib-community/cslib-frontier/issues/3542), [#3569](https://github.com/cslib-community/cslib-frontier/issues/3569)): Nullstellensatz and polynomial-calculus bounds: the completeness degree `max(D, n + 1)` and the matching `⌈n/2⌉ + 1` subset-sum upper bound (Impagliazzo–Pudlák–Sgall), size and degree bounds for converting polynomial calculus to Nullstellensatz, and Cook–Reckhow packaging with encodings.
  Also a uniform bound in resolution line count alone for the squarefree PCR translation, degree-controlled translation to the original-variable PC encoding, pigeonhole degree lower bounds, and size lower bounds.
- **Frege**: implicational completeness of the Hilbert-style system (Kalmár); formula-size measures; the simulation of resolution as a p-simulation of Cook–Reckhow proof systems, with encodings and translation time; the mutual p-simulation of Frege systems; and Extended Frege.
- **Cutting planes:** the bounded-coefficient clique–colouring bound via Krajíček's feasible interpolation (Corollary 7.3, [#2019](https://github.com/cslib-community/cslib-frontier/issues/2019)), and monotone interpolation for shared variables with only nonpositive coefficients in `Γ_B`.
  Pudlák's unrestricted-coefficient lower bound via monotone real circuits, coefficient-size measures, Buss–Clote cutting planes with division by 2 only, and the p-simulation of resolution, with encodings and translation time.
- **Feasible interpolation** ([#2019](https://github.com/cslib-community/cslib-frontier/issues/2019)): further clients of Krajíček's interpolation theorem for semantic derivations, namely resolution through Theorem 6.1, the linear equational calculus, and the monotone case for the `ℬ` side.
  The cutting-planes work is under **Cutting planes**.
- **Proof search:** automatizability and weak automatizability with explicit encodings and runtime dependence on the shortest proof; proof-search reductions built on the Cook–Reckhow and p-simulation APIs; then reflection principles and bounded-arithmetic witnessing theorems.
