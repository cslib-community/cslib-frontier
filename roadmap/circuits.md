# Roadmap: Circuits and algebraic complexity

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

- **Williams's NEXP ⊄ ACC⁰ and Murray–Williams's NQP ⊄ ACC⁰** ([#889](https://github.com/cslib-community/cslib-frontier/issues/889)): some language in NEXP, then NQP, has no polynomial-size `ACC⁰` circuits (AND, OR, NOT and `MOD_m` gates).
  This needs the quasilinear succinct 3-CNF reduction for `NTIME(2 ^ n)` (Williams, Fact 3.1), nondeterministic `ACC⁰` compression of De Morgan circuits (Williams, Lemma 3.1), and the `E^NP` and NEXP lower bounds.
- **Circuit lower bounds from refuting ETH** ([#1539](https://github.com/cslib-community/cslib-frontier/issues/1539)): `E^NP ⊄ SIZE(O(n))`, and a language in `E^NP` whose fan-in-two circuits need more than `c n √log n` gates infinitely often, by Williams's witness-circuit argument with #CircuitSAT counters.
  It requires connecting the exponential nondeterministic time hierarchy to framed witness preparation and building the linear-size decoder and checker uniformly.
- **Circuit classes, bridges and barriers**: uniform NC, AC and TC, circuit-to-machine bridges, algorithm-to-lower-bound arguments, and the algebrization barrier.
  NC simulation of unrestricted `TCⁱ` needs Muroga's threshold weight-bounding theorem.
- **Formula and monotone depth lower bounds**: formula lower bounds beyond Andreev's, following Jukna, and Raz–Wigderson's monotone depth bound for matching on general graphs.
- **Monotone circuits versus P**: a monotone language in P whose monotone circuit complexity is exponential, the gap of É. Tardos (1988).
- **Explicit affine dispersers for logarithmic dimension** ([#4323](https://github.com/cslib-community/cslib-frontier/issues/4323)): an explicit polynomial-time affine disperser for dimension `O(log n)` (Li 2023), strengthening the unconditional `4 N - o(N)` Boolean circuit lower bounds in `P` (`O(N / log N)` and `O(N ^ (4 / 5))` thresholds) to `4 N - O(log N)`.
- **An explicit frontier extractor** ([#7793](https://github.com/cslib-community/cslib-frontier/issues/7793)): port v1's sumset-extractor construction with an explicit family in `Complexity.P encBits` that discharges the frontier lower bounds' hypotheses.
  Because it would exceed the library's unconditional `4 N - o(N)` bound in P, it needs an independent correctness review of the frontier core.
- **Depth-two threshold circuits for Andreev's function**: closing the worst-case gate gap between `Ω̃(n ^ (3 / 2))` and `O(n ^ 2)` for depth-two weighted threshold circuits computing Andreev's function, following Kane–Williams (arXiv:1511.07860v1).
- **Construction runtimes**: certified separately from gate counts, for the mass-production constructors with constructive choices of information sets and line menus, the iterated-function preprocessing, and the bit complexity of formula evaluation on the rational hitting-list matrices.
- **Algebraic complexity** ([#891](https://github.com/cslib-community/cslib-frontier/issues/891)): Limaye–Srinivasan–Tavenas superpolynomial lower bounds for constant-depth circuits computing iterated matrix multiplication over any field, including their semantic set-multilinear model, growing product-depth `Δ` with exponent `d ^ exp(-O(Δ))`, the `√d` bound at `Δ = 1` (LST Lemma 13 and Corollary 4), the full range of `d`, and the `0/1`-substitution remark.
- **Identity testing and hitting sets** ([#891](https://github.com/cslib-community/cslib-frontier/issues/891)): polynomial identity testing and hitting sets for arithmetic circuits, beyond the hitting sets for small partial-derivative spaces, sums of powers of linear forms, ROABPs and non-commutative ABPs.
  Also the Kabanets–Impagliazzo theorem: a deterministic PIT algorithm implies NEXP ⊄ P/poly or the permanent has no polynomial-size arithmetic circuits.
- **VNP-completeness of the permanent** ([#321](https://github.com/cslib-community/cslib-frontier/issues/321)): Valiant's theorem that the permanent is VNP-complete over fields of characteristic other than two.
  Hardness still needs formulas for VP witnesses, the two-entry selector gadget, and elimination of Boolean sums with repeated selectors.
- **Non-commutative formulas and branching programs**: the reduction from general to homogeneous layered non-commutative ABPs, so that Nisan's lower bounds apply to general ABPs, and non-commutative formula lower bounds for the determinant and permanent.
- **Tensor, rank and partial-derivative methods**: arithmetic lower bounds by tensor and rank methods and partial-derivative measures: Nisan–Wigderson's all-orders measure with their elementary symmetric polynomial and iterated matrix multiplication bounds, and shifted partial derivatives.
- **Depth-reduction chasms**: depth four (Agrawal–Vinay) and depth three (Gupta–Kamath–Kayal–Saptharishi), with uniform construction costs certified separately from gate counts.
- **Strassen's degree bound**: Bézout's inequality and the `n log d` multiplication lower bound for the power map.
  With the Baur–Strassen transfer this gives the `Ω(n log d)` bound for the single power sum `∑ xᵢ^(d+1)`.
- **Matrix inversion from the determinant**: inversion through the adjugate circuits of [`Arithmetic/Adjugate`](../CslibFrontier/Computability/Circuit/Arithmetic/Adjugate.lean), in a circuit model with division.
- **Determinantal complexity**: Cai–Chen–Li's extension of the Mignon–Ressayre bound `n² ≤ 2 · dc(perm_n)` to every characteristic other than two, and Yabe's real bound `dc(perm_n) ≥ (n - 1)² + 1` through Sylvester's law of inertia.
  Also border determinantal complexity in geometric complexity theory (Landsberg–Manivel–Ressayre).
- **The matrix multiplication exponent**: the bound `ω ≤ 9/4` over fields of positive characteristic, extending Pass's constructive proof (arXiv:2610.28627v2) of OpenAI's bound beyond characteristic zero.
  Also the rectangular and dual exponents, and explicit sizes and constants.
- **Fast integer and polynomial multiplication** ([#2923](https://github.com/cslib-community/cslib-frontier/issues/2923)): Karatsuba multiplication with smaller constants, logarithmic or polylogarithmic depth, uniform generation, and a native or word-RAM realization.
  Also Toom–Cook (`O(n ^ log₃ 5)` for Toom-3) and lower bounds such as rank `3` for the two-term product tensor.
- **Fast Fourier transform and FFT multiplication**: mixed-radix and Bluestein FFTs for every length, and FFTs and FFT multiplication as arithmetic circuits of size `O(n log n)` and depth `O(log n)`, over commutative rings with suitable principal roots of unity.
  Without such roots, Schönhage–Strassen over `R[x] / (x ^ m + 1)` with the `O(n log n log log n)` integer bound; and lower bounds such as Morgenstern's `Ω(n log n)` for bounded-coefficient linear circuits.
- **Matrix rigidity and linear circuits** ([#3209](https://github.com/cslib-community/cslib-frontier/issues/3209)): Valiant's criterion for linear circuits with nonlinear gates over finite fields, Shparlinsky's Vandermonde bound, and the asymptotic Alman–Williams non-rigidity of Walsh–Hadamard matrices (their Theorem 1.1).
  An explicit `(εn, n ^ (1 + δ))`-rigid matrix is Valiant's open problem.
- **Real-algebraic decision procedures**: port the Sturm–Tarski query evaluator, recursive evaluator, implicit arithmetic, native space certificates and the ETR upper bound from [lean-canny](https://github.com/SamuelSchlesinger/lean-canny).

### Jukna coverage

Formalize the established results, constructions and worthwhile exercises of [Jukna's *Boolean Function Complexity* (2012)](https://web.vu.lt/mif/s.jukna/boolean/index.html), with the author's [errata](https://web.vu.lt/mif/s.jukna/boolean/misprints-BFC.html), auditing each statement against the numbered result.
Organize modules by subject, not chapter.

| Chapters | Next coverage work |
| --- | --- |
| 1–2: foundations and Boolean analysis | Counting, graph complexity, degree and approximation results; the partial-function circuit upper bounds that use Lemma 1.17. |
| 3–5: communication | Matrix, randomized and multiparty results. |
| 6–10: formulas and circuits | Formula and monotone bounds; span programs and negation complexity. |
| 11–13: depth restrictions and general gates | Depth-three, threshold, entropy, wire and linear-operator bounds. |
| 14–17: trees and branching programs | Bounded-read and bounded-time lower bounds and tree results. |
| 18–19: proof complexity | Proof-space and cutting-plane lower bounds. |
| 20: barriers and further methods | The book's generator, natural-proof, fusion and indirect lower-bound results. |
