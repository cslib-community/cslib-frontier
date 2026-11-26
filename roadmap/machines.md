# Roadmap: Machines, RAM and data structures

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

- **Pointer machines and disjoint sets** ([#5441](https://github.com/cslib-community/cslib-frontier/issues/5441)): Build on the injective heap simulation with allocation to prove separation/locality and source-program correspondence with undefined-value traps and invocation conventions.
  Extend WordRAM compilation with input/output setup, further scalar implementations and workspace bounds.
  Extend the deterministic WordRAM-to-pointer compiler to charged input preparation and randomized semantics.
  Establish native union-find algorithms and lower bounds with explicit symbol-opacity and set-separation assumptions.

- **Local-address WordRAM simulation** ([#8800](https://github.com/cslib-community/cslib-frontier/issues/8800)): Prove constant overhead for a fragment with bounded pointer moves, reference loads and stores, and matched scalar operations and bounded random draws.
  Apply the simulation to three-way quicksort with countdown pivot walks and a locally accessed work stack, transferring the sorted-permutation result and expected instruction bound.

- **Efficient universal simulation** ([#800](https://github.com/cslib-community/cslib-frontier/issues/800)): A storage bound for the universal function running in time `O(N + poly(D, M) · (t + 1) log(t + 2))`, for encoded input length `N`, description length `D` and largest input symbol `M`, in terms of the simulated machine's space rather than its time.
  An unclocked form within the same time bound that runs until the simulated machine halts.
- **Plain computability** ([#862](https://github.com/cslib-community/cslib-frontier/issues/862)): Complete the plain calculus and delete the tidy calculus, keeping only a machine-level kernel inside the Machines layer.
- **Certificate APIs and automation** ([#1155](https://github.com/cslib-community/cslib-frontier/issues/1155)): Predictable certificate search, with `polytime` and `ppt` failures that check the goal's shape and say what is missing even when search records no hint ([#5976](https://github.com/cslib-community/cslib-frontier/issues/5976)), using Cook–Levin and GGM as regression clients.
  Improve configuration views, tape partitions and handoff identities only where several clients benefit, keeping machine transitions out of global simp.
- **Certificate coverage** ([#1155](https://github.com/cslib-community/cslib-frontier/issues/1155)): Infer encodings for ordinary functional expressions through constructor, projection, lookup and composition rules, and generalize list, bounded-table, cache and nested-loop invariants where clients need them.
  Keep time, workspace and output-size bounds separate through composition, apply cumulative streaming contracts to captured iteration and nested loops, and develop general open-program composition.
- **Mathlib TM2:** Sublinear work-space comparisons and a linear-space forward simulation.
- **Single-tape lower bounds** ([#2884](https://github.com/cslib-community/cslib-frontier/issues/2884)): A single-tape palindrome decider in time `O(n²)`, matching the quadratic lower bound for CSLib `SingleTapeTM` deciders.
  A linear-time multi-tape palindrome decider gives the one-tape/two-tape time separation.
  The nondeterministic analogue, under the accept measure, of the theorem that single-tape deciders in time `o(n log n)` accept only regular languages.
- **Generic RAM:** Uniform arbitrary-program dispatch with general width-selection and input-fit theorems, and simulation of operations by programs over smaller bases.
  Structured programs and time classes over arbitrary value domains with weighted or bit costs, and simulations between instances.
- **Word RAM:** An AC⁰ basis, wider-fragment simulations, and transfer of Anthropic's modular machine and APSP algorithms.
  Transfer of bounded-error (Monte Carlo) and adaptive-adversary cell-probe lower bounds, and the Horn-SAT and domino-tiling clients.
- **Randomized Word RAM** ([#1124](https://github.com/cslib-community/cslib-frontier/issues/1124)): Expected-time rules for unbounded almost-surely terminating structured loops, random-tape equivalence, and BPP/RP/ZPP simulation bridges for the randomized word RAM.
- **Sharper native Exact Triangle exponent** ([#2423](https://github.com/cslib-community/cslib-frontier/issues/2423)): Prove an `Oκ(n^2.9983)` bound, the source's stated exponent, for the automatic box-backed Exact Triangle host under the library's native conventions.
- **Memory-oracle realization** ([#2205](https://github.com/cslib-community/cslib-frontier/issues/2205)): Verify Word-RAM algorithms as memory-oracle programs refined to native programs by game-hop proofs, replacing hand-stepped code proofs.
- **Memory-oracle clients** ([#2205](https://github.com/cslib-community/cslib-frontier/issues/2205), [#5427](https://github.com/cslib-community/cslib-frontier/issues/5427)): Realize the framed queue with faithful allocation and Karger–Stein, keeping each client's original word envelope and bounds.
  Karger–Stein also needs its contraction implementation and a recursive frame stack.
  The direction also covers generic stateful and whole-client composition.
- **Stateful Word-RAM algorithms:** Word-RAM controllers for larger adaptive and iterative clients, including the two-stack queue and timeline-editing controllers, with reusable allocation and deallocation, shrinking, and live and peak space accounting.
  Ownership and recursive procedures, and model realizations for cell probes, caches and randomness.
- **Data-structure extensions:** Present and historical queries for the retroactive interface, balancing and heap or RAM representations of search trees, uniform preprocessing and dynamic updates for fusion trees, Word-RAM deletion and predecessor for van Emde Boas sets, and deallocation, shrinking and compiled client controllers for the doubling array.
- **Resizable Word RAM and dynamic succinct dictionary** ([#3167](https://github.com/cslib-community/cslib-frontier/issues/3167)): Deamortized worst-case operations with high-probability space bounds for the dynamic dictionary on the Resizable Word RAM.
- **With-high-probability succinct dictionary** ([#5356](https://github.com/cslib-community/cslib-frontier/issues/5356)): The Section 6 resizing and the Theorem 1.1 endpoint of the SOSA 2024 succinct dynamic dictionary with worst-case operational bounds with high probability (Bender, Farach-Colton, J. Kuszmaul, W. Kuszmaul).
- **Typed-call evaluator:** An evaluator for fixed-program Word-RAM clients that returns the typed observation, final state and halt-inclusive instruction cost, so that the prefix-sum clients no longer assemble preparation, evaluation and halt accounting by hand.
- **Priority-queue and shortest-path consolidation** ([#949](https://github.com/cslib-community/cslib-frontier/issues/949)): Lift the operation-count helpers to `IndexedMinPQ`, and parameterize flat-program operation-sequence execution (`RunsOps`) over `PQCode` so that `BinaryHeap` and `FibonacciHeap` share one generic `run_ops_exact` theorem.
  Factor a common `ShortestPathSpec p bound` predicate across `LogLinearSpec`, `FibonacciSpec` and `FibonacciLinearSpec`.
- **Perfect hashing:** A word-RAM realization of the static FKS two-level table with `w`-bit seeds and headers, charged bucketing and layout, an unbounded Las Vegas construction and a bridge to `w`-bit cell probes.
  FKS's `k x mod p mod s` family with its `n + o(n)` refinement and deterministic construction, dynamic perfect hashing (Dietzfelbinger et al.), and the Fredman–Komlós lower bound on the description size of perfect hash families.
- **Ropes** ([#3670](https://github.com/cslib-community/cslib-frontier/issues/3670)): a persistent sequence over an arbitrary element type, stored as an AVL-balanced binary tree with bounded non-empty chunks at its leaves and verified against `List`.
  Indexing, concatenation by join and positional splitting, with insertion, range erasure, extraction and replacement derived from split and join.
  Word-RAM running times for the same operations: join linear in the height difference and split logarithmic in the length.
- **B-trees** ([#3674](https://github.com/cslib-community/cslib-frontier/issues/3674)): The `⌈log₂(n + 1)⌉` comparison lower bound for lookup, and cost bounds for B+-trees, which keep only separator keys in interior nodes and every entry in a leaf.
- **Subconstant-redundancy dynamic dictionary** ([#5349](https://github.com/cslib-community/cslib-frontier/issues/5349)): dynamic succinct dictionaries with subconstant redundancy `R` following Li, Liang, Yu, and Zhou (SODA 2024, arXiv:2310.20536).
  Word-RAM bit-packed realization with `O(1)` expected query time, `infoBits + O(R)` bits for `R ≤ n` (including Section 4 small-`R` adapter trees), Las Vegas sentinel/resizing wrappers, and localized subtree rehashing with `O((n + M) log* n)` expected work.

### Parallel, external-memory and distributed models

- **Parallel algorithms:** Work–span semantics for a parallel language or PRAM model whose computation DAGs feed the unit-time DAG scheduling bounds of `Algorithms/Lean/Scheduling/Brent.lean`, followed by prefix scan, sorting and graph primitives with both work and span bounds.
  State processor access, synchronization and scheduling overhead explicitly, including work stealing (Blumofe–Leiserson).
- **Memory hierarchies:** External-memory and ideal-cache models with explicit capacity and block-size parameters, with scanning, B-tree operations, blocked matrix multiplication and cache-oblivious sorting as clients.
  Connect arithmetic-step, memory-access and cache-miss bounds through concrete realizations, including replacement and initialization conventions.
- **Distributed complexity** ([#7505](https://github.com/cslib-community/cslib-frontier/issues/7505)): The CONGEST model with explicit message-size conventions, and locality lower bounds, communication-to-round reductions and corresponding algorithmic examples for LOCAL and CONGEST.
  Targets include Linial's `O(Δ²)` colouring, deterministic MIS on bounded-degree graphs and CONGEST message bounds.
- **Luby's MIS** ([#7505](https://github.com/cslib-community/cslib-frontier/issues/7505)): The expected phase count of the random-priority variant, the pairwise-independent analysis of Luby's original marking algorithm and its NC derandomization, Ghaffari's `O(log Δ) + poly(log log n)` bound, and the Kuhn–Moscibroda–Wattenhofer lower bounds.
- **Locality on cycles and paths:** The tight `½ log* n + O_|L|(1)` bound for flexible problems in the Chang–Studený–Suomela classification of LCL problems on directed cycles, and the classification extended to LCLs with inputs, paths and undirected cycles.
- **Fault-tolerant agreement:** Byzantine agreement with polynomially many messages for all `n > 3t` ([#7210](https://github.com/cslib-community/cslib-frontier/issues/7210)), weak agreement and the Byzantine firing squad.
  Approximate agreement with unbounded inputs and dynamic halting ([#7116](https://github.com/cslib-community/cslib-frontier/issues/7116)), and clock-synchronization bounds for asynchronous event-driven systems, bounded drift and incomplete networks ([#7202](https://github.com/cslib-community/cslib-frontier/issues/7202)).
  Termination of Ben-Or's randomized agreement under history-dependent scheduling ([#7120](https://github.com/cslib-community/cslib-frontier/issues/7120)).
