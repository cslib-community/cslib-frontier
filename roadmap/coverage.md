# Roadmap: Coverage and reuse

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

The long-term bar is to support formalizing every paper in the [Electronic Colloquium on Computational Complexity](https://eccc.weizmann.ac.il/colloquium/call_for_papers/), with the additional work per paper increasingly its new mathematics: standard models, representation changes, reductions, resource certificates and proof techniques come from the library.
Use a growing, source-pinned sample of papers, including some chosen after an API was designed, as demanding clients, and promote recurring obligations into shared APIs only after reuse is demonstrated.

- **Arora–Barak coverage** ([#4711](https://github.com/cslib-community/cslib-frontier/issues/4711)): audit remaining draft endpoints, including formal-measure density amplification with Razborov–Rudich's additive loss (22.3).
  Settle the draft's statements on its time-bounded classes, TISP (5.13, 5.14.1) and BPL (Exercise 7 §7), under its ever-nonblank space measure, where a configuration needs $O(S\log T)$ bits.
- **One sensitivity API:** Define the sensitivity measures over any `Fintype` in CSLib and drop the separate measures of the sensitivity-separation development.
- **Divide-and-conquer recurrences:** Matching `Θ` bounds for equality recurrences and case 3 under the general regularity condition, for the master theorem over `ℕ`.
  Move hand-solved recurrences onto it where the generic constant suffices, keeping CSLib's sharper merge-sort bound and the halving lemma, the sharp tool for `b = 2`.

### OpenAI math results ([#1002](https://github.com/cslib-community/cslib-frontier/issues/1002))

Review Lance Fortnow's [expository rewrites](https://github.com/fortnow/AI-Papers) of the OpenAI math papers and his [TCS catalogue](https://lance.fortnow.com/openai-math-tcs.htm) of the openai/math release, and extract the in-scope results, both headline theorems and minor lemmas useful in their own right.
Prove each against cslib-frontier's definitions from the cited manuscript's exact statement with its version pinned, labelling unrefereed results; a source formalization is a reference, not evidence.
The openai/math formalizations are Apache 2.0, as is cslib-frontier, so adaptation with attribution is permitted; the rewrites state no license and are only read and credited.

- **The sharper Theorem 1.1 bound** ([#1538](https://github.com/cslib-community/cslib-frontier/issues/1538)): A `#k`-SAT model counter running in time `2^{O_k(n log log n / √log n)}` at arbitrary density, by recursive tensor contraction.
  The intended route combines the fixed-density bound `2^{O_{k,D}(n / √log n)}` (Theorem D.1 with `ℓ = 1`) with the Lemma D.2 construction, applied natively to the model-counter interface.
- **Exact optimization:** Native extraction of an optimizing MAX-SAT assignment in contraction time measured by literal occurrences plus clauses.
- **Large weights:** Signed or rational weight interfaces for exact contraction of tensor tables whose bit lengths are polynomial in the structural size, applied natively to weighted-CSP partition functions.
