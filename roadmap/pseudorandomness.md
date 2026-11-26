# Roadmap: Pseudorandomness, coding and Boolean analysis

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

- **Improved sparse expanders** ([#3348](https://github.com/cslib-community/cslib-frontier/issues/3348)): simple degree-two and degree-three cores with their matching-path extensions, the link from their generalized eigenvector equations to normalized spectral expansion, explicit core families, and the density-sequence asymptotic coefficient approaching `π² / 8`.
  For lossless expansion, the equivariant regular subgraph and its full row rank through the orbit-matrix and prime-power-group argument.
  Finite spectral certificates, conditional cut-rank bounds and transfer for a supplied subgraph do not complete these construction endpoints.
- **Derandomization from hardness**: the infinitely-often variant, and the EXP ⊄ P/poly endpoint of Babai, Fortnow, Nisan and Wigderson.
- **Derandomization from generic generators** ([#5452](https://github.com/cslib-community/cslib-frontier/issues/5452)): Arora–Barak Lemma 16.4 and Goldreich Proposition 8.15 for `BPTIME(t)` with general `t`, as stated.
  Under the library's constant-factor `BPTIME` the printed proofs leave a gap; whether the sources' own conventions avoid it is open.
- **Hard-core lemma**: Holenstein's optimal density, a set of density `δ` from hardness `δ / 2` (his Lemma 2.1); the uniform hard-core lemma; and sharper size losses from smooth boosting.
- **Extractors** ([#895](https://github.com/cslib-community/cslib-frontier/issues/895)): beyond Chor–Goldreich, two-source extractors for lower min-entropy through Chattopadhyay–Zuckerman's Theorem 4.1, resilient functions (Theorems 3 and 4) and extractor (Theorem 1).
  Finite guarantees stay separate from uniform construction and decoding costs.
- **Random graph connectivity** ([#3485](https://github.com/cslib-community/cslib-frontier/issues/3485)): the hitting-time theorem, and the translation of the connectivity threshold for Mathlib's binomial random graph `G(n, p)` to `G(n, m)`.
- **Random graph thresholds** ([#3275](https://github.com/cslib-community/cslib-frontier/issues/3275)): for Mathlib's binomial random graph `G(n, p)`, the second-moment `1`-statement for balanced graphs at `n ^ (-v / e)`, and Bollobás's general threshold `n ^ (-1 / m(H))`.
  Also Janson's inequality and the Poisson limit at the threshold; the connectivity threshold `log n / n` belongs to random graph connectivity ([#3485](https://github.com/cslib-community/cslib-frontier/issues/3485)).
- **Explicit Ramsey graphs** ([#3041](https://github.com/cslib-community/cslib-frontier/issues/3041)): strongly explicit graphs with no `k`-clique or `k`-independent set on more than Frankl–Wilson's `k ^ Θ(log k / log log k)` vertices, toward Erdős's existential `2 ^ (k / 2)`: the two-source disperser and extractor constructions of Barak–Rao–Shaltiel–Wigderson, Cohen, Chattopadhyay–Zuckerman and Li, with the disperser connection of [#895](https://github.com/cslib-community/cslib-frontier/issues/895).
  Keep these bounds separate from polynomial-time recognition and adjacency certificates.
  An explicit graph on `2 ^ Ω(k)` vertices is open.
- **The Frankl–Wilson modular intersection theorem** ([#3041](https://github.com/cslib-community/cslib-frontier/issues/3041)): the theorem in its inclusion-matrix form (reportedly `|L| ≤ d`), beyond the restricted form `|L| ≤ d mod p` of the triangular polynomial argument.
- **Codes**: the decoding running time of Guruswami–Sudan list decoding, and concrete list-decodable codes for Nisan–Wigderson.
- **Upper bounds on code size** ([#3280](https://github.com/cslib-community/cslib-frontier/issues/3280)): the McEliece–Rodemich–Rumsey–Welch linear-programming bound (Delsarte's linear program and Krawtchouk polynomials).
- **Expander codes** ([#3278](https://github.com/cslib-community/cslib-frontier/issues/3278)): lossless expanders, probabilistic or explicit (Capalbo–Reingold–Vadhan–Wigderson), making expander codes asymptotically good; a machine-model linear-time decoder; Spielman's linear-time encodable codes; and Zémor's decoding of Tanner codes on spectral expanders.
- **Channel coding** ([#3304](https://github.com/cslib-community/cslib-frontier/issues/3304)): dispersion terms at capacity, discrete memoryless channels with mutual-information capacity, feedback channels, explicit efficiently decodable capacity-achieving codes (Forney concatenation, polar codes), and the link to list decoding.
- **Locally decodable codes** ([#2929](https://github.com/cslib-community/cslib-frontier/issues/2929)): the binary XOR normal form for locally decodable codes, and the Goldreich–Karloff–Schulman–Trevisan and Kerenidis–de Wolf exponential lower bounds for two-query locally decodable codes.
- **Lempel–Ziv compression**: LZ77 bit-level codes with bounded lookahead.
  Also asymptotic optimality for stationary ergodic sources through Ziv's inequality, and links to Kolmogorov complexity and finite-state compressibility.
  Word-RAM parser running times are a separate endpoint.
- **Boolean analysis** ([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)): coverage of O'Donnell's *Analysis of Boolean Functions*, including the book-form statements of its Chapter 9 (Friedgut's junta theorem with its spectral concentration, and the sharper asymptotic constant of Exercise 9.30).
  Also hypercontractivity beyond `p ≤ 2 ≤ q`, further applications of hypercontractivity, such as the two-set Generalized Small-Set Expansion Theorem and the sharp Level-1 Inequality for `[−1, 1]`-valued `f`, and reverse hypercontractivity at the exponents `0` and `−∞` and for nonnegative functions with negative exponents (Exercise 10.6(a)).
- **Invariance principles** ([#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)): from Chapter 11 of O'Donnell's book, the Invariance Principle for `(2, 3, ρ)`-hypercontractive ensembles (Remark 11.66) with its Lévy-distance bound (the second statement of Corollary 11.70), the classical and Variant Berry–Esseen Theorems, and cdf-closeness to Gaussians through the Carbery–Wright theorem (Theorem 11.71).
  Also Majority Is Stablest through Borell's isoperimetric theorem.
- **Resource-bounded measure and dimension**: Lutz's p-measure in `E` with the quantitative Measure Conservation bound and countable p-unions (Lutz's Lemma 3.10(c)), measure in `EXP` (`p₂`), p-randomness, gales and resource-bounded dimension.
  State the budgets and uniformity of betting strategies separately from measure-theoretic facts, and connect quantitative randomness to Kolmogorov complexity.
