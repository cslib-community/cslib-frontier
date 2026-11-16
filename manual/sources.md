# Primary sources and provenance

Repository citations are pinned to the reviewed source or dependency revision. Direct declaration links in the chapter text identify the supporting statement. The [library bibliography](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/references.bib) is linked at the survey revision; inclusion there is not a claim that this review checked every cited paper. Mathematical attributions reported only from source annotations are identified as such in the chapters.

The private-transcript sources are described in [the extraction methods](history/methods.md); selected excerpts are included in the manual, while their bulk exports remain untracked. Public GitHub issues, PRs and CI runs are linked from [development history](history/development.md). Refetching mutable records is not an archive of their historical contents. Inaccessible sources and unavailable archives are identified below or in the relevant chapter.

<a id="aaronson20"></a>
## aaronson20

Scott Aaronson. *The Busy Beaver Frontier*. ACM SIGACT News 51(3), 32–54, 2020. https://doi.org/10.1145/3427361.3427369 ; author's version https://www.scottaaronson.com/papers/bb.pdf . Read in the author's version on 2026-11-08: Proposition 1 (oracle access to any upper bound on the shift function solves the halting problem, hence no such bound is computable; the library proves the unrelativized corollary) and Proposition 2 (the shift function eventually exceeds every computable function). Both are stated for Turing machines; Section 2 notes that they hold in any universal model of computation. Section 1 defines `BB_L` for a programming language `L` with bit-string programs (and a variant through Kolmogorov complexity), the closest analogue of the library's code-size version. Journal pagination was taken from the bibliographic record.

<a id="abukhzam2007"></a>
## abukhzam2007

Faisal N. Abu-Khzam, Michael R. Fellows, Michael A. Langston and W. Henry Suters. "Crown Structures for Vertex Cover Kernelization." *Theory of Computing Systems* 41(3), 411–430, 2007. https://doi.org/10.1007/s00224-007-1328-0 . Bibliographic data and the abstract (crown structures; a crown-based kernelization compared with the LP-based one) were checked against secondary search summaries on 2026-11-08 UTC. The full text was not inspected, and the crown definition used in [Crown](../CslibFrontier/Foundations/Combinatorics/SimpleGraph/Crown.lean) is not attributed to a numbered statement there. Chor, Fellows and Juedes, "Linear Kernels in Linear Time, or How to Save k Colors in O(n²) Steps", WG 2004, LNCS 3353, 257–269, https://doi.org/10.1007/978-3-540-30559-0_22, is cited in the module docstring on the same basis.

<a id="acek17"></a>
## acek17

Daniel Apon, Chongwon Cho, Karim Eldefrawy and Jonathan Katz. "Efficient, Reusable Fuzzy Extractors from LWE." *Cyber Security Cryptography and Machine Learning (CSCML 2017)*, LNCS 10332, 1–18, Springer, 2017. https://doi.org/10.1007/978-3-319-60080-2_1 ; IACR Cryptology ePrint Archive Report 2017/755, https://eprint.iacr.org/2017/755 . Checked against the ePrint 2017/755 PDF on 2026-11-14: Definitions 2 and 3 (weak and strong reusability, Section 2.2, p. 6; the public-parameters model is described in Section 2.1, p. 4), the common-matrix FMR construction, Theorem 1 and the 1-query strong-reusability attack (Section 3.3, pp. 9–10), and the encryption-based strongly reusable fuzzy extractor from LWE without random oracles (Section 5, pp. 11–12). Checked again on 2026-11-15 (SHA-256 `18ebc576b367e3896c77293ca11909a12477b84c770d1490ae3df8db5b8b9d02`): Definition 4 (decisional LWE `LWE_{n,m,q,χ}` for an integer `q ≥ 2`, Section 2.3, p. 7) and the Section 5 security sketch (assumptions (1) and (2), the `LWE_{n,(t+2)m,q,χ}` claim for adversaries making at most `t` oracle calls, and the simulation, p. 12).

<a id="achlioptas03"></a>
## achlioptas03

Dimitris Achlioptas. “Database-Friendly Random Projections: Johnson–Lindenstrauss with Binary Coins.” *Journal of Computer and System Sciences* 66(4), 671–687, 2003. https://doi.org/10.1016/S0022-0000(03)00025-4 . Author-hosted copy of the typeset journal version: https://cgi.di.uoa.gr/~optas/papers/jl.pdf . Checked against that copy on 2026-11-07 UTC: Theorem 1.1 on p. 673 (squared distances within `1 ± ε` with probability at least `1 - n^(-β)` for `k ≥ k₀ = (4 + 2β) log n / (ε²/2 - ε³/3)`, stated for all `ε, β > 0`; the `±1` distribution is (1)). Also checked: Lemma 4.1 on p. 679 (Gaussian entries), Lemma 5.1 on p. 679 (the per-vector tails), and Lemma 5.2 on p. 680, eqs. (6)–(7) (the bounds on `𝔼 exp (h Q²)` and `𝔼 Q⁴`).

<a id="acor22"></a>
## acor22

Divesh Aggarwal, Eldon Chung, Maciej Obremski, João Ribeiro. "On Secret Sharing, Randomness, and Random-less Reductions for Secret Sharing." *Theory of Cryptography (TCC 2022), Part I*, LNCS 13747, 327–354, Springer, 2022. https://doi.org/10.1007/978-3-031-22318-1_12 ; ePrint https://eprint.iacr.org/2021/802 . Bibliographic metadata taken from `references.bib`. The direct ePrint copy was not inspected (gated behind an automated challenge), so ACOR22 attributions are unverified directly; the formalized threshold design results (`ThresholdDesign`, `(t', n') → (2, 2)` composition, `(2, 3, 2, 2)` and `(r, r, 2, 2)` impossibility for `r ≥ 3`) were checked against [aggarwal26](#aggarwal26), Section 5.

<a id="aggarwal26"></a>
## aggarwal26

Divesh Aggarwal. *Secret Sharing Despite Non-Extractable Randomness*. arXiv:2610.20173v2, 2026. https://arxiv.org/abs/2610.20173v2 . LaTeX source (`secret_sharing.tex`, version v2) checked on 2026-11-10 UTC: Definition 2.1 (threshold finite-key correctness and `δ`-statistical privacy relative to a source class `sources`; generalized in the library to general `AccessStructure` and arbitrary `Key`) and Section 5 ("Relation to the reductions of ACOR22", covering threshold distribution designs, the `(t', n') → (2, 2)` composition, and non-existence of `(2, 3, 2, 2)` and `(r, r, 2, 2)` designs with `r ≥ 3`, generalized in the library to `DistributionDesign`, `ThresholdDesignOn`, and `no_thresholdDesign_two_two` for `2 ≤ t ≤ n`, `3 ≤ n`).

<a id="ahocorasick75"></a>
## ahocorasick75

Alfred V. Aho, Margaret J. Corasick. "Efficient String Matching: An Aid to Bibliographic Search." *Communications of the ACM* 18(6), 333–340, 1975. https://doi.org/10.1145/360825.360855 . Scanned copy in D. J. Bernstein's bibliography archive, https://cr.yp.to/bib/1975/aho.pdf , checked 2026-11-08 for Algorithms 1 and 3, Lemmas 1–3, Theorems 1, 2 and 4, and Figures 1 and 2.

<a id="ahlswedecsiszar93"></a>
## ahlswedecsiszar93

Rudolf Ahlswede and Imre Csiszár. "Common Randomness in Information Theory and Cryptography. Part I: Secret Sharing." *IEEE Transactions on Information Theory* 39(4), 1121–1132, 1993. https://doi.org/10.1109/18.243431 . Bibliographic metadata checked via secondary search summaries on 2026-11-11.

<a id="ahlswedecsiszar07"></a>
## ahlswedecsiszar07

Rudolf Ahlswede and Imre Csiszár. "On Oblivious Transfer Capacity." ISIT 2007, Nice, France, pp. 2061–2064, https://doi.org/10.1109/ISIT.2007.4557524, https://www.math.uni-bielefeld.de/ahlswede/homepage/public/242.pdf. Checked on 2026-11-11 against the open-access technical report `242.pdf`: §3 Theorem 1 (PDF p. 6) and §4 Eq. (14) (PDF p. 8). Used for the asymptotic single-choice-bit string-OT bound (which the Lean formalization adapts to finite exact batch-bit OT with independent choices).

<a id="aik11"></a>
## aik11

Benny Applebaum, Yuval Ishai, Eyal Kushilevitz. "How to Garble Arithmetic Circuits." *52nd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2011)*, 120–129, 2011. https://doi.org/10.1109/FOCS.2011.40 . Checked on 2026-11-10 against the author-hosted copy of the FOCS version, https://bennyapplebaum.sites.tau.ac.il/_files/ugd/f706bf_ccb157901f504e32a79d89a666f56de3.pdf , which has no printed page numbers: Definition 4.2 (affinization gadget), Definition 4.5 (perfect privacy of a gadget) and Section 5, Fact 5.1. Cited for the framework of affine key encodings over a ring (with per-wire keys) and for the notion of an affinization gadget; the four-value multiplication gadget formalized here is an explicit instance derived in the Lean source, not the general compiler of the paper.

<a id="alonbabaisuzuki1991"></a>
## alonbabaisuzuki1991

Noga Alon, László Babai and Hiroshi Suzuki. “Multilinear Polynomials and Frankl–Ray-Chaudhuri–Wilson Type Intersection Theorems.” *Journal of Combinatorial Theory, Series A* 58(2), 165–180, 1991. https://doi.org/10.1016/0097-3165(91)90058-O . Bibliographic metadata from search summaries on 2026-11-08; the full text was not inspected in this pass. The manual attributes only the multilinear polynomial method for uniform and nonuniform restricted-intersection bounds to this paper; theorem numbers are not cited.

<a id="alonfeldmanprocacciatennenholtz10"></a>
## alonfeldmanprocacciatennenholtz10

Noga Alon, Michal Feldman, Ariel D. Procaccia and Moshe Tennenholtz. "Strategyproof Approximation of the Minimax on Networks." *Mathematics of Operations Research* 35(3), 513–526, 2010. https://doi.org/10.1287/moor.1100.0457 (journal metadata verified via web search on 2026-11-11; journal PDF not inspected). Preprint inspected on 2026-11-11: "Strategyproof Approximation Mechanisms for Location on Networks," arXiv:0907.2049v1 (12 July 2009), https://arxiv.org/pdf/0907.2049v1 . Checked Section 2 (pp. 4–5: strategyproofness, group strategyproofness in the weak sense, social cost, approximation ratio) and Section 3.2 (pp. 6–7: Mechanism 1 random dictatorship, Theorem 3.1 proving strategyproofness and `2 - 2/n` approximation on graphs, first remark extending to arbitrary metric spaces, third remark on the 3-leaf star counterexample to weak group strategyproofness, and fourth remark on weak group strategyproofness on the line).

<a id="alongibbonsmatiasszegedy99"></a>
## alongibbonsmatiasszegedy99

Noga Alon, Phillip B. Gibbons, Yossi Matias, Mario Szegedy. “Tracking Join and Self-Join Sizes in Limited Storage.” *Proceedings of the 18th ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS)*, 10–20, 1999. https://doi.org/10.1145/303976.303978 . Author-hosted PostScript of the conference version: https://www.math.tau.ac.il/~matias/papers/pods99.ps . Checked against that copy on 2026-11-08: Section 4.3 (the tug-of-war join signature `S(F) = ∑ ε_i f_i` with four-wise independent `±1` signs and estimator `S(F)·S(G)`), Lemma 4.4 (mean `|F ⋈ G|`, variance at most `2·SJ(F)·SJ(G)`, through the exact variance in equation (3) of its proof), Theorem 4.5 (the `k`-fold mean with `k = c·B₂²/B₁²` and Chebyshev), the deletion rule following it, and the statement of Theorem 4.3 (signature lower bound, not formalized). The journal version, *Journal of Computer and System Sciences* 64(3), 719–747, 2002, https://doi.org/10.1006/jcss.2001.1813 , was taken from bibliographic metadata and not inspected.

<a id="alonmatiasszegedy99"></a>
## alonmatiasszegedy99

Noga Alon, Yossi Matias, Mario Szegedy. “The Space Complexity of Approximating the Frequency Moments.” *Journal of Computer and System Sciences* 58(1), 137–147, 1999; preliminary version in STOC 1996. https://doi.org/10.1006/jcss.1997.1545 . Author-hosted copy of the journal version: https://www.tau.ac.il/~nogaa/PDFS/amsz4.pdf . An independent agent review checked the theorem locators and statements (Theorem 2.2 for the `F₂` sketch, Proposition 3.1 for the `F∞` lower bound) against that copy on 2026-11-07 UTC. The JCSS page numbers were taken from secondary search summaries and were not checked against the typeset journal PDF.

<a id="alonspencer2016"></a>
## alonspencer2016

Noga Alon and Joel H. Spencer. *The Probabilistic Method*, 4th edition. Wiley, 2016. ISBN 978-1-119-06195-3. Bibliographic data from the library bibliography. The section locators used for the second moment method and random graphs (Chapter 4: §4.3 for the bound `Pr[X = 0] ≤ Var X / (E X) ^ 2`, §4.4 for random graphs and threshold functions) were taken from secondary tables of contents and from an agent review, which placed the bound at Theorem 4.3.1. The book was not inspected in this pass, and the library cites section numbers only. The 0-1 law for `G(n, p)` with constant `0 < p < 1` is cited at §10.4 ("Zero–One Laws", Chapter 10 "Random Graphs") from secondary tables of contents, consulted on 2026-11-10; one secondary summary placed it at §10.7 instead, so this locator is unverified and no theorem number is cited.

<a id="alonyusterzwick1995"></a>
## alonyusterzwick1995

Noga Alon, Raphael Yuster, Uri Zwick. "Color-Coding." *Journal of the ACM* 42(4), 844–856, 1995. https://doi.org/10.1145/210332.210337 . Bibliographic data from the DOI record. The locator Lemma 3.1 (colorful paths by dynamic programming over color sets) was taken from secondary descriptions; the full text was not inspected in this pass.

<a id="ambainis02"></a>
## ambainis02

Andris Ambainis. "Quantum lower bounds by quantum arguments." *Journal of Computer and System Sciences* 64(4), 750–767, 2002 (preliminary version in STOC 2000). https://doi.org/10.1006/jcss.2002.1826 ; open preprint arXiv:quant-ph/0002066v1 (24 February 2000), https://arxiv.org/abs/quant-ph/0002066 . Checked in arXiv:quant-ph/0002066v1 (`density4.tex`) on 2026-11-11: Section 2 (query model and extension to larger input/output alphabets), Section 3 Lemma 1 (multi-outcome distinguishing state-overlap bound `2√(ε(1-ε))`, proved in `Overlap.lean` and `ReadoutOverlap.lean`), Section 6.1 Theorem 6 (relational adversary bound `(1 - 2√(ε(1-ε))) √(m m') = O(T √l_max)` for non-Boolean input alphabets and pairwise conflict product `l_{x,i} l_{y,i} ≤ l_max`, proved in `ValueAdversary.lean` with constant `2` for arbitrary unitary value oracles), and Section 6.2 Theorem 7 (`Ω(√N)` query lower bound for inverting a permutation via single-transposition pairs across a balanced bipartition, proved in `PermutationInversion.lean`). Journal pagination comes from `references.bib` and was not directly inspected.

<a id="ambainis06"></a>
## ambainis06

Andris Ambainis. "Polynomial degree vs. quantum query complexity." *Journal of Computer and System Sciences* 72(2), 220–238, 2006; preliminary version FOCS 2003; arXiv:quant-ph/0305028v4 (23 November 2004). https://arxiv.org/abs/quant-ph/0305028 . Read in arXiv:quant-ph/0305028v4 on 2026-11-11: Section 3.3 Definitions 1–3 (relation weights, `w'(x, y, i)`, and adversary bound), Section 4.1 Lemma 1 (the weighted adversary lower bound), Lemma 4 (`w'` formulation), and Section 4.3 Lemma 3 (`4`-bit base function with weight `w = 1` at Hamming distance `1` and `2/3` at Hamming distance `2`, `w' ∈ {1, 1/3, 4/3}`, and maximum load `wt/v = 2.5`). Journal pagination was checked through DBLP/search metadata and was not inspected directly.

<a id="ambainismoscatappdewolf00"></a>
## ambainismoscatappdewolf00

Andris Ambainis, Michele Mosca, Alain Tapp and Ronald de Wolf. *Private Quantum Channels*. 41st Annual Symposium on Foundations of Computer Science (FOCS 2000), 547–553. https://doi.org/10.1109/SFCS.2000.892142 ; author-hosted copy https://homepages.cwi.nl/~rdewolf/publ/qc/AMTW00.pdf . Read in the author-hosted copy on 2026-11-08: Definition 3.1 (private quantum channel: the key-averaged image of every plaintext state is one fixed state), Theorem 4.1 (the uniformly random `n`-qubit Pauli product is a private quantum channel for all of `H_{2^n}` with output `I / 2^n`; its proof remarks that this holds for a qubit "no matter if it is entangled with other qubits") and Corollary 5.4 (key entropy at least `2n`, the lower bound, which is not formalized). Definition 3.1 quantifies over pure plaintext states; the library states secrecy for every density matrix, which follows by linearity. The arXiv preprint quant-ph/0003101, *Private Quantum Channels and the Cost of Randomizing Quantum Information*, lists only Mosca, Tapp and de Wolf; locators follow the FOCS version.

<a id="andoniindyk08"></a>
## andoniindyk08

Alexandr Andoni, Piotr Indyk. “Near-Optimal Hashing Algorithms for Approximate Nearest Neighbor in High Dimensions.” *Communications of the ACM* 51(1), 117–122, 2008. https://doi.org/10.1145/1327452.1327494 . Inspected in the author-hosted copy (https://people.csail.mit.edu/indyk/p117-andoni.pdf). Section 2.4, "Strategy 1", p. 119, states: "It is shown in [25, 19] that the first strategy, with L′ = 3L, yields a solution to the randomized c-approximate R-near neighbor problem". Here [25] is Indyk–Motwani, STOC 1998 ([indykmotwani98](#indykmotwani98)), and [19] is Gionis–Indyk–Motwani, "Similarity search in high dimensions via hashing", VLDB 1999. The same page takes `L = Θ(n^ρ)` with `ρ = ln(1/P₁)/ln(1/P₂)`. Cited as an exposition of the rule that stops the LSH query after `3L` candidates; the rule itself is credited to [25, 19].

<a id="anshelevichdktwr08"></a>
## anshelevichdktwr08

Elliot Anshelevich, Anirban Dasgupta, Jon Kleinberg, Éva Tardos, Tom Wexler and Tim Roughgarden. *The Price of Stability for Network Design with Fair Cost Allocation*. SIAM Journal on Computing 38(4), 1602–1623, 2008; preliminary version in FOCS 2004. https://doi.org/10.1137/070680096 . Bibliographic metadata only, as given in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, reference [1]; the DOI was taken from a search summary. The paper's text was not inspected (the author-hosted copies tried returned 404), so no locator in it is cited. The `H_k` price-of-stability theorem is attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, Theorem 2.1, and proved following [tardoswexler07](#tardoswexler07), §19.3.

<a id="apostolicobreslauergalil95"></a>
## apostolicobreslauergalil95

Alberto Apostolico, Dany Breslauer and Zvi Galil. "Parallel Detection of All Palindromes in a String." *Theoretical Computer Science* 141(1–2), 163–173, 1995. https://doi.org/10.1016/0304-3975(94)00083-U . Locators refer to the preliminary version, INRIA Research Report RR-2136, 1993, open copy https://inria.hal.science/inria-00074536 , checked on 2026-11-08 UTC. Section 1 defines even and odd palindromes of radius `R` centered at a position and the maximal radii at all positions; the manual's center convention is translated from these definitions. Section 1 also states that Manacher's algorithm computes the maximal radii at all positions in linear time. The journal text was not inspected.

<a id="aspvallplasstarjan79"></a>
## aspvallplasstarjan79

Bengt Aspvall, Michael F. Plass and Robert Endre Tarjan. "A Linear-Time Algorithm for Testing the Truth of Certain Quantified Boolean Formulas." *Information Processing Letters* 8(3), 121–123, 1979. https://doi.org/10.1016/0020-0190(79)90002-4 . Bibliographic metadata as in the library bibliography; the primary text has not been inspected, so no theorem or section numbers are cited. Credited for the implication-graph characterization of 2-SAT and its linear-time strongly-connected-components decision and witness-construction algorithm.

<a id="babai86"></a>
## babai86

László Babai. "On Lovász' Lattice Reduction and the Nearest Lattice Point Problem." *Combinatorica* 6(1), 1–13, 1986. https://doi.org/10.1007/BF02579403 . Not inspected (no open version was used); cited bibliographically as the origin of the nearest-plane algorithm. The formalization follows [regev04](#regev04).

<a id="babaioffchuangfeldman07"></a>
## babaioffchuangfeldman07

Moshe Babaioff, John Chuang and Michal Feldman. "Incentives in Peer-to-Peer Systems." Chapter 23 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 593–612. https://doi.org/10.1017/CBO9780511800481.025 (chapter metadata checked against the Crossref record). A university-hosted PDF of the book was consulted on 2026-11-08 for Exercise 23.6 (p. 611). Its definition of a strong equilibrium (SE) excludes coalitions in which every member strictly gains, and is stated for utilities. The library's `IsStrongEquilibrium` is that notion for costs, with the coalition required to be nonempty, which the exercise leaves implicit. By contrast, the strong Nash equilibrium of [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, Definition 3.1 (`IsStrongNash`) also excludes deviations in which no member loses and some member gains. The same weak-deviation definition appears in Chapter 1, §1.7.1 of the book (Tardos and Vazirani), which attributes the notion to Aumann (1974); Aumann's text was not consulted.

<a id="baloghbekesidosaepsteinlevin18"></a>
## baloghbekesidosaepsteinlevin18

János Balogh, József Békési, György Dósa, Leah Epstein and Asaf Levin. *A new lower bound for classic online bin packing*. arXiv:1807.05554v1, 2018. https://arxiv.org/abs/1807.05554 ; published in *Algorithmica* 83(7), 2047–2062, 2021, https://doi.org/10.1007/s00453-021-00818-7 (bibliographic data from the Crossref record; the locators follow arXiv v1). Worker w156-ff read the arXiv version on 2026-11-08 UTC. Section 1 reports that Yao's first lower bound on the asymptotic competitive ratio uses at most three types of items, `1/7 + ε`, `1/3 + ε` and `1/2 + ε`; it does not state the value of that bound. It also reports the later bounds of Brown and Liang (`1.53635`), van Vliet (`1.5401474`) and Balogh, Békési and Galambos (`248/161`). The library's [OnlineLowerBound](../CslibFrontier/Algorithms/Lean/BinPacking/OnlineLowerBound.lean) module takes its item types from this report.

<a id="barak-steurer16"></a>
## barak-steurer16

Boaz Barak and David Steurer. *Proofs, beliefs, and algorithms through the lens of sum-of-squares*. Lecture notes, 2016, https://www.sumofsquares.org/ . On 2026-11-08 UTC worker w96-sos consulted these author-hosted lectures: "Mathematical definitions" (https://www.sumofsquares.org/public/lec01-2_definitions.pdf), for Theorem 19, the duality of sum-of-squares certificates and pseudo-distributions; "The sos algorithm over general domains" (https://www.sumofsquares.org/public/lec-definitions-general.pdf), for Definition 1 (sos proofs), the remark after Theorem 2 (degree-`d` sos refutations), Definitions 5 and 7 (pseudo-distributions and the constraints they satisfy) and Theorem 8; and "Higher-degree integrality gaps" (https://www.sumofsquares.org/public/lec03-2_lowerbounds_csp.pdf), for Theorem 2, Lemmas 7 and 9, and Lemma 24 (Grigoriev's bound for Tseitin tautologies on vertex expanders). The sum-of-squares modules cite these locators. The notes are a living document, and the numbering may change.

<a id="barnumsaksszegedy03"></a>
## barnumsaksszegedy03

Howard Barnum, Michael E. Saks and Márió Szegedy. "Quantum query complexity and semi-definite programming." *Proceedings of the 18th IEEE Annual Conference on Computational Complexity (CCC 2003)*, 179–193, 2003. https://doi.org/10.1109/CCC.2003.1214419 . Bibliographic metadata checked through search records on 2026-11-11; the full CCC 2003 text was not inspected directly. Cited via [Høyer, Lee and Špalek 2007](#hoyerleespalek07) (Section 1.1, Definition 1 and Theorem 1) for the nonnegative spectral adversary `ADV(f) = max_{Γ ≥ 0} ‖Γ‖ / max_i ‖Γ ∘ D_i‖`.

<a id="barrett26"></a>
## barrett26

Clark Barrett, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet Kohli, Leonardo de Moura, Alexandre Rademaker and Sorrachai Yingchareonthawornchai. *CSLib: The Lean Computer Science Library*. arXiv:2602.04846v1, 2026. https://doi.org/10.48550/arXiv.2602.04846 . Author/title/version metadata checked against https://arxiv.org/abs/2602.04846 on 2026-11-02 UTC.

<a id="basupollackroy06"></a>
## basupollackroy06

Saugata Basu, Richard Pollack and Marie-Françoise Roy. *Algorithms in Real Algebraic Geometry*, 2nd edition. Algorithms and Computation in Mathematics 10, Springer, 2006. https://doi.org/10.1007/3-540-33099-2 . Bibliographic metadata from `references.bib`; the primary textbook was not directly inspected (the retired author-hosted URL `perso.univ-rennes1.fr` returned HTTP 404), so internal chapter, section, and theorem numbers reported in secondary summaries (such as Chapter 2, Theorem 2.50 for Sturm's theorem over real closed fields and Chapter 10, §§10.1–10.2 for root bounds, root-separation bounds, and Sturm bisection) remain unverified against the printed text and are not claimed as verified locators. Local adaptations in `CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/`: [`Sturm.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/Sturm.lean) proves Sturm's theorem on `(a, b]` over `ℝ` via local constancy of `sturmVariations p x + #{r ≤ x}`; [`RootBound.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/RootBound.lean) packages the cleared-denominator rational `ℓ²` root-separation form (`Polynomial.mignotte_sep_sqNorm_rat`); and [`TotalRatPoly.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/TotalRatPoly.lean) with [`TotalIsolation.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/TotalIsolation.lean) implements an end-to-end `TimeM ℕ`-charged `List ℚ` Sturm-bisection isolator (`isolateRootsTotalM`, `isolateRootsTotal`) with left-endpoint root refinement and boundary separation into strictly disjoint closed rational intervals (`J₁.upper < J₂.lower`).

<a id="bax93"></a>
## bax93

Eric T. Bax. “Inclusion and Exclusion Algorithm for the Hamiltonian Path Problem.” *Information Processing Letters* 47(4), 203–207, 1993. https://doi.org/10.1016/0020-0190(93)90033-6 . Bibliographic metadata checked via DOI/DBLP on 2026-11-11; the article body (paywalled) was not inspected, so the manual cites it for the inclusion–exclusion walk-counting algorithm without a theorem or page locator.

<a id="bcgl92"></a>
## bcgl92

Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby. *On the Theory of Average Case Complexity*. Journal of Computer and System Sciences 44(2), 193–219, 1992; preliminary version in STOC 1989. https://doi.org/10.1016/0022-0000(92)90019-F . Bibliographic metadata checked against the Crossref record on 2026-11-08. The primary text was not inspected, and no theorem number is claimed. The manual attributes to this paper only the implication `DistNP ⊆ AvgP ⇒ NE = E`, as reported by [bm15](#bm15), §5.

<a id="bcs16"></a>
## bcs16

Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner. *Interactive Oracle Proofs*. TCC 2016-B II, 31–60. https://doi.org/10.1007/978-3-662-53644-5_2 .

<a id="bdfkk18"></a>
## bdfkk18

Chris Brzuska, Antoine Delignat-Lavaud, Cédric Fournet, Konrad Kohbrok and Markulf Kohlweiss. *State Separation for Code-Based Game-Playing Proofs*. ASIACRYPT 2018, Lecture Notes in Computer Science 11274, 222–249. https://doi.org/10.1007/978-3-030-03332-3_9 . Bibliographic metadata as in the library bibliography. The primary text was not inspected, and no theorem number is claimed. The manual attributes to this paper only the package calculus: packages composed sequentially and side by side, and the reduction and hybrid steps built from them.

<a id="beigelgill92"></a>
## beigelgill92

Richard Beigel and John Gill. "Counting Classes: Thresholds, Parity, Mods, and Fewness." *Theoretical Computer Science* 103(1), 3–23, 1992. https://doi.org/10.1016/0304-3975(92)90084-S ; the author's full version (dated June 10, 1996) is linked from https://cis.temple.edu/~beigel/papers/bg-mods-tcs.html . Checked against that author's version on 2026-11-08 UTC by worker w167-modpe. (Re-inspected during #3554): Property 8(ii), p. 4 (binomial coefficients `C(f, g)` of #P functions with polynomially bounded UPF `g` are in #P, specialized locally to FP `g`), Corollary 20 (`C(n, p^k) ≢ 0 mod p` iff the base-`p` digit of `n` at `p^k` is nonzero), Proposition 29 (`j ∣ k` gives `MOD_jP ⊆ MOD_kP`) and Theorem 30 (`MOD_{k^i}P = MOD_kP` for prime `k` and `i ≥ 1`), Theorem 32 (Hertrampf characterization of `MOD_{jk}P`), Corollaries 33–35, p. 16 (Corollary 33 is prime-factor union decomposition, Corollary 34 is squarefree collapse, Corollary 35 is ordinary union closure), and Hertrampf remark (intersection closure yields complement closure). `CslibFrontier/Computability/Complexity/Classes/ModP/Composite.lean` contains a locally reconstructed proof of the Hertrampf characterization (the 1990 original was not inspected). Numbering follows the author's version; the journal pagination is from the DOI record and the typeset journal numbering was not checked.

<a id="bellman58"></a>
## bellman58

Richard Bellman. "On a Routing Problem." *Quarterly of Applied Mathematics* 16(1), 87–90, 1958. https://doi.org/10.1090/qam/102435 . Bibliographic data from the DOI record and secondary summaries; the paper was not inspected in this pass.

<a id="bellman62"></a>
## bellman62

Richard Bellman. “Dynamic Programming Treatment of the Travelling Salesman Problem.” *Journal of the ACM* 9(1), 61–63, 1962. https://doi.org/10.1145/321105.321111 . Bibliographic metadata checked on 2026-11-07; the article body was not inspected in this pass, so the manual cites it for the subset dynamic program and not for a numbered statement.

<a id="bennett89"></a>
## bennett89

Charles H. Bennett. *Time/Space Trade-Offs for Reversible Computation*. SIAM Journal on Computing 18(4), 766–776, 1989. https://doi.org/10.1137/0218053 . Bibliographic metadata only; the paper was not inspected in this pass. The manual credits it with the recursive checkpointing strategy as described in [ltv98](#ltv98), Sections 6 and 7.

<a id="bensassonkopparty12"></a>
## bensassonkopparty12

Eli Ben-Sasson and Swastik Kopparty. *Affine Dispersers from Subspace Polynomials*. SIAM Journal on Computing 41(4), 880–914, 2012. https://doi.org/10.1137/110826254 . Bibliographic metadata as in the library bibliography; the primary PDF was not directly inspected, so ECCC report theorem locators recorded in the source remain unverified against the primary text.

<a id="berge57"></a>
## berge57

Claude Berge. *Two Theorems in Graph Theory*. Proceedings of the National Academy of Sciences of the United States of America 43(9), 842–844, 1957. https://doi.org/10.1073/pnas.43.9.842 . Bibliographic metadata only; the primary text was not inspected. The manual attributes to this paper the augmenting-path characterization of maximum matchings; the "Theorem 1" locator comes from secondary descriptions and is unverified. Schrijver's lecture notes ([schrijver17](#schrijver17), Theorem 3.2) state the result without attribution.

<a id="berge58"></a>
## berge58

Claude Berge. *Sur le couplage maximum d'un graphe*. Comptes Rendus Hebdomadaires des Séances de l'Académie des Sciences 247, 258–259, 1958. Bibliographic data from secondary bibliographies; the note was not inspected, and no theorem number is claimed. The manual attributes to it the Tutte–Berge formula, following [schrijver17](#schrijver17), Section 5.1.

<a id="berger1966"></a>
## berger1966

Robert Berger. *The Undecidability of the Domino Problem*. Memoirs of the American
Mathematical Society 66, 1966. [Publisher record](https://doi.org/10.1090/memo/0066).
Bibliographic metadata checked on 2026-11-16 against the publisher record and its Crossref
deposit. The book's full text was inaccessible in this pass: internal locator not verified.
The formalization uses the later Robinson–Ollinger route described under
[Jeandel–Vanier](#jeandelvanier2020), ported from the pinned lean-wang revision there.

<a id="bermanhartmanis75"></a>
## bermanhartmanis75

Leonard Berman and Juris Hartmanis. *On Isomorphisms and Density of NP and Other Complete Sets*. Technical Report TR75-260, Department of Computer Science, Cornell University, October 1975. https://hdl.handle.net/1813/7101 . The open eCommons PDF is an image scan without a text layer. An independent agent review checked these locators against it on 2026-11-08 UTC: §I, printed p. 2 (the isomorphism conjecture and its `P ≠ NP` consequence); §III, Theorem 1, printed pp. 7–10 (PDF pp. 10–13; isomorphism from invertible, length-increasing one-one reductions); Lemmas 3 and 5, printed pp. 10–12 (length growth and the two-argument padding and read-back condition); and Theorem 7 with its CNF construction, printed pp. 13–14. The journal version (*SIAM Journal on Computing* 6(2), 305–322, 1977, https://doi.org/10.1137/0206023) was not checked, and its numbering is not claimed to match.

<a id="bertsekas88"></a>
## bertsekas88

Dimitri P. Bertsekas. "The auction algorithm: A distributed relaxation method for the assignment problem." *Annals of Operations Research* 14, 105–123, 1988. https://doi.org/10.1007/BF02186476 . Author-hosted scan: https://web.mit.edu/dimitrib/www/TheAuctionAP.pdf . The original algorithm is the MIT LIDS working paper "A Distributed Algorithm for the Assignment Problem" (March 1979), retyped at https://web.mit.edu/dimitrib/www/Bertsekas_Auction_Distributed_1979.pdf . The manual uses the 1988 paper for the `O(N A C / ε)` complexity of the pure (unscaled) auction (§1) and for scaling integer costs by `N + 1` and running down to `ε = 1` (§3). Both locators were checked against the author-hosted scan on 2026-11-08 UTC.

<a id="bertsekas98"></a>
## bertsekas98

Dimitri P. Bertsekas. *Network Optimization: Continuous and Discrete Models*. Athena Scientific, Belmont, MA, 1998. ISBN 1-886529-02-7. Author-hosted copy: https://web.mit.edu/dimitrib/www/netbook_Full_Book_NEW.pdf . Checked against that copy on 2026-11-08 UTC: §1.3.3 and Prop. 1.4 (an assignment satisfying `ε`-complementary slackness is within `n ε` of optimal); §7.1.1, ε-CS (7.1), the bidding rule (7.2)–(7.5) with the Gauss–Seidel version, Prop. 7.1 (ε-CS is preserved) and Prop. 7.2 (termination, `n ε`-optimality, optimality for integer data and `ε < 1/n`); Figs. 1.12–1.14 (the price-war example); §7.1.4 and Prop. 7.3 (`ε`-scaling, not formalized).

<a id="beullenscamposcelihesskannwischer26"></a>
## beullenscamposcelihesskannwischer26

Ward Beullens, Fabio Campos, Sofía Celi, Basil Hess and Matthias J. Kannwischer. *MAYO: Round 3 Version*, August 31, 2026 (bibliography key `BeullensCamposCeliHessKannwischer2026`). https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/mayo_specification.pdf . Checked against that PDF on 2026-11-14 (SHA-256 `1fc7561dc8ffdbe36c101b985266e4d3c8aa88fa580e18ead215a80ac7bb371f`): Section 2.1.2, Algorithm 2, printed pp. 8–9 specifies `SampleSolution` by shifting with explicit randomness, rejecting a matrix without full row rank even when the shifted system is consistent, and shifting the solution back. Section 2.1.5, Algorithm 7, printed p. 14 tries at most 256 separately derived randomness records and keeps the first successful call; the remark on printed p. 3 says a failed signing attempt retains the salt and derives fresh randomness for another preimage-sampling attempt. The formalization records only the deterministic abstract solver contract, shift correctness and ordered bounded-retry behavior. It does not formalize the source's uniform-sampling statement, rank probability, signing algorithm, correctness or security reductions.

<a id="beyersdorffgalesilauria10"></a>
## beyersdorffgalesilauria10

Olaf Beyersdorff, Nicola Galesi and Massimo Lauria. *A lower bound for the pigeonhole principle in tree-like Resolution by asymmetric Prover–Delayer games*. Information Processing Letters 110(23), 1074–1077, 2010. https://doi.org/10.1016/j.ipl.2010.09.007 ; author's copy https://massimolauria.net/documents/tree-like-php.pdf (6 pages). Read in the author's copy on 2026-11-08. Locators checked there: Theorem 1 on p. 3 (if `F` has a tree-like refutation of size at most `S`, Delayer gets at most `log S` points in every `(c₀, c₁)`-game with `1/c₀ + 1/c₁ = 1`); Theorem 2 on p. 4 (every tree-like refutation of `PHP^m_n` has size `2^Ω(n log n)`); the explicit `2^((n/2) log(n/2 + 1)) = (n/2 + 1)^(n/2)` for even `n` at the end of that proof on p. 5; and the closing remark on p. 5 that the bound also holds for the functional pigeonhole principle. The abstract and introduction present the result as a simpler proof of Dantchev and Riis's bound (CCC 2001). Journal pagination was taken from the Crossref record. The ECCC version (TR10-081) was not reachable from this environment and was not read.

<a id="bfckk24"></a>
## bfckk24

Michael A. Bender, Martin Farach-Colton, John Kuszmaul and William Kuszmaul. "Modern Hashing Made Simple." *Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA 2024)*, 363–373, 2024. https://doi.org/10.1137/1.9781611977936.33 ; open author-hosted copy https://par.nsf.gov/servlets/purl/10488765 (11 pages; `BenderFarachColtonKuszmaulKuszmaul2024`). Checked against the open copy on 2026-11-14 UTC: Section 2.1, PDF pp. 2–3 (word-RAM model with `w = (1 + Θ(1)) log n`, high-probability `1 - O(1 / n^c)` convention, and zero-space random-hash-oracle assumption); Section 2.2, PDF p. 3 (B-trees and `k`-tries, Lemma 2.2); Section 3, PDF p. 4 (slow partition hash tables, Lemma 3.1); Section 4, PDF pp. 4–6 (indexed partition hash tables and `B = √(log n)` Four-Russians B-tree query mapper, Lemmas 4.1–4.3); and Section 5, PDF pp. 6–7 (deamortizing insertions and deletions to `O(1)` time w.h.p. via growing and shrinking `√n`-tries, Lemma 5.1; historical trie-buffer discussion in Section 7, PDF p. 8). SOSA proceedings pagination (`363–373`) comes from `references.bib` and the DOI record and was not separately inspected; Milestones 1–3a of [#5356](https://github.com/cslib-community/cslib-frontier/issues/5356) formalize foundational and pure-model adaptations rather than the end-to-end Theorem 1.1 / Theorem 6.1 resizable hash table.

<a id="bfckkl22"></a>
## bfckkl22

Michael A. Bender, Martin Farach-Colton, John Kuszmaul, William Kuszmaul and Mingmou Liu. "On the Optimal Time/Space Tradeoff for Hash Tables." *Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 1284–1297, 2022. https://doi.org/10.1145/3519935.3519969 ; open preprint `arXiv:2111.00602v2` (4 November 2021), https://arxiv.org/abs/2111.00602v2 (`BenderFarachColtonKuszmaulKuszmaulLiu2022`). Checked against `arXiv:2111.00602v2` on 2026-11-11 and 2026-11-13 UTC (unnumbered title page is PDF p. 1, so printed p. `p` is PDF p. `p + 1`): Section 2.1, printed p. 3 / PDF p. 4 (balls-to-slots probe complexity `1 + log i` and switching cost); Section 2.4, printed p. 7 / PDF p. 8 (iterated logarithm `log^(k) n`); Sections 3 and 3.1, printed pp. 8–12 / PDF pp. 9–13 (`k`-kick tree hierarchy, depth-cap distribution, greedy unsaturated-ancestor selection, priority kicks with switching cost `≤ k + 1`, Lemma 1 on printed pp. 10–11 / PDF pp. 11–12, and Theorems 2–3 on printed p. 12 / PDF p. 13); and Section 5.1, printed p. 27 / PDF p. 28 (removal-only deletion in cubbies). STOC proceedings pagination comes from `references.bib` and was not separately inspected.

<a id="bfprt73"></a>
## bfprt73

Manuel Blum, Robert W. Floyd, Vaughan Pratt, Ronald L. Rivest and Robert E. Tarjan. *Time Bounds for Selection*. Journal of Computer and System Sciences 7(4), 448–461, 1973. https://doi.org/10.1016/S0022-0000(73)80033-9 . Bibliographic metadata and the abstract's `5.4305 n` comparison bound for `PICK` were checked through secondary search results on 2026-11-08; the paper's text was not read. The manual attributes to this paper only the median-of-medians selection algorithm and that constant. The groups-of-five accounting in the Lean files follows the presentation in [clrs09](#clrs09), Section 9.3, which was not checked against the printed book.

<a id="bhr12"></a>
## bhr12

Mihir Bellare, Viet Tung Hoang, Phillip Rogaway. "Foundations of Garbled Circuits." *Proceedings of the 2012 ACM Conference on Computer and Communications Security (CCS '12)*, 784–796, 2012. https://doi.org/10.1145/2382196.2382279 . Full version: Cryptology ePrint Archive, Report 2012/265. Bibliographic data from the DOI record and secondary listings (`BellareHoangRogaway2012`). The abstract garbling-scheme framework in `Garbling/{Scheme,Games,Foundations,CircuitInverters}.lean` follows Sections 2.3 and 3–4 of ePrint 2012/265 (conventional Boolean circuits in §2.3, syntax in §3.1, side information in §3.3, the five security games in §§3.4–3.6, the explicit topology and size inverters of Proposition 1 in §4.1, and the indistinguishability/simulation reductions and circuit corollaries of Propositions 2 and 3 and Corollaries 1 and 2 in §§4.2–4.3), while the concrete point-and-permute circuit garbling in `Garbling/{Basic,Privacy}.lean` cites the garbling-scheme syntax and simulation-based privacy with topology side information at paper level only, because the ePrint copy returned HTTP 403 and the ACM page sat behind a bot challenge in the pass that added those modules. Checked on 2026-11-15 against the ePrint full version dated October 1, 2012 (45 pages, SHA-256 `33c00b94752c8ecd852c8cf84ef70967a4290ea5409ed615e6293ff3137dc8ed`; printed page `p` is PDF page `p + 2`): §3.1, p. 7, the length condition (`|F|`, `|e|` and `|d|` depend only on `k`, `f.n`, `f.m` and `|f|`), the nondegeneracy condition (`e` and `d` depend only on those and the coins) and the correctness condition, which `Garbling/HalfGates/Scheme.lean` cites for the clauses that half-gates garbling fails.

<a id="bhr12b"></a>
## bhr12b

Mihir Bellare, Viet Tung Hoang, Phillip Rogaway. "Adaptively Secure Garbling with Applications to One-Time Programs and Secure Outsourcing." *Advances in Cryptology – ASIACRYPT 2012*, LNCS 7658, 134–153, Springer, 2012. https://doi.org/10.1007/978-3-642-34961-4_10 . Full version: Cryptology ePrint Archive, Report 2012/564 (`BellareHoangRogaway2012b`). `Garbling/Adaptive.lean` formalizes the coarse-grained adaptive privacy game `Prv1` of Section 3.1, Figure 2, in which a two-stage adversary first receives `(F, d)` from `Garble(f)` and then adaptively queries `Input(x)` to receive `X` from a stateful two-stage simulator.

<a id="birge83"></a>
## birge83

Lucien Birgé. "Approximation dans les espaces métriques et théorie de l'estimation." *Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete* 65(2), 181–237, 1983. https://doi.org/10.1007/BF00532480 . Bibliographic metadata checked via search summaries on 2026-11-11; the article text was not inspected, and no theorem number is claimed. Cited as background origin for bounded likelihood-ratio Hellinger tests (`leCamBirgeTest`) and Hellinger tournament localization (`birgeTournamentSelect`); the explicit `1/3`–`2/3` clipped `birgeWeight` formulation and constants (`1 - h² / 25`, `10 * r`, `11 * r`, `2 * (M - 1) * exp (-4 n r²)`) are proved from first principles in `CslibFrontier/Probability/HypothesisSelection/{LeCamBirge,Tournament}.lean`.

<a id="bjkst02"></a>
## bjkst02

Ziv Bar-Yossef, T. S. Jayram, Ravi Kumar, D. Sivakumar, Luca Trevisan. “Counting Distinct Elements in a Data Stream.” *Randomization and Approximation Techniques in Computer Science (RANDOM 2002)*, LNCS 2483, 1–10, Springer, 2002. https://doi.org/10.1007/3-540-45726-7_1 . Author-hosted copy: https://webee.technion.ac.il/people/zivby/papers/f0/f0.ps . Locators checked against that copy on 2026-11-08 UTC: Section 2 (the first algorithm) and Theorem 1. The algorithm picks a pairwise independent hash `h : [m] → [M]` with `M = m³` and keeps the `t = ⌈96/ε²⌉` smallest distinct hash values. It outputs `tM/v`, where `v` is the `t`-th smallest value. Each tail is bounded by `1/6` via Chebyshev, plus `1/m` for collisions, and the median of `O(log(1/δ))` copies gives `O(1/ε² · log m · log(1/δ))` bits. The LNCS page numbers come from the DOI record and were not checked against the typeset volume.

<a id="bland77"></a>
## bland77

Robert G. Bland. "New Finite Pivoting Rules for the Simplex Method." *Mathematics of Operations Research* 2(2), 103–107, 1977. https://doi.org/10.1287/moor.2.2.103 . Bibliographic data from the DOI record and search summaries; the paper was not inspected in this pass, and no theorem number is claimed. The manual credits it with the smallest-subscript pivoting rule and its finiteness; the formalized no-cycling proof is the standard largest-fickle-variable argument as presented in textbooks such as [chvatal83](#chvatal83), Chapter 3.

<a id="blum67"></a>
## blum67

Manuel Blum. *A Machine-Independent Theory of the Complexity of Recursive Functions*. Journal of the ACM 14(2), 322–336, 1967. https://doi.org/10.1145/321386.321395 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the two axioms, recursive relatedness and the speed-up theorem to this paper. The manual also mentions the customary attribution of the measure-independent theorem on arbitrarily complex functions to this paper (and to Rabin, 1960); that attribution and any theorem locator are unverified.

<a id="blumfurstkearnslipton93"></a>
## blumfurstkearnslipton93

Avrim Blum, Merrick Furst, Michael Kearns and Richard J. Lipton. "Cryptographic Primitives Based on Hard Learning Problems." *Advances in Cryptology — CRYPTO '93*, LNCS 773, 278–291, 1993. https://doi.org/10.1007/3-540-48329-2_24 . Bibliographic metadata only (`references.bib`); the paper was not inspected and no numbered result is claimed. [CryptoHardness/Inversion.lean](../CslibFrontier/MachineLearning/UniformLearning/CryptoHardness/Inversion.lean) cites it, with [Impagliazzo and Levin](#impagliazzolevin90), for the easy direction of the correspondence between average-case learning and one-way functions: an inverter for the map from a key and examples to the labelled sample is a consistent learner.

<a id="blummansour07"></a>
## blummansour07

Avrim Blum and Yishay Mansour. "From External to Internal Regret." *Journal of Machine Learning Research* 8, 1307–1324, 2007. https://www.jmlr.org/papers/v8/blum07a.html . Read in the JMLR PDF on 2026-11-10. Locators checked there: the definition of swap regret as regret against all `N^N` modification rules (§2, p. 1311), Definition 2 (`ε`-correlated equilibrium) and Theorem 3 (`R/T`-correlated equilibria from swap regret `R`, p. 1311), the reduction with stationary `p = pQ` and Definition 4 (§3, p. 1312), and Theorem 5 (swap regret at most `∑ i, R_i`) with Corollaries 6 and 7 (`O(N √(T log N))` and `O(√(T N log N))`, p. 1313). The paper scales losses to `[0, 1]`; the library's Hedge-based bound uses losses in `[-1, 1]` and the second-order Hedge bound, which gives `2 √(T N ln N)` with explicit constants.

<a id="bm15"></a>
## bm15

Markus Bläser and Bodo Manthey. *Smoothed Complexity Theory*. ACM Transactions on Computation Theory 7(2), Article 6, 2015; preliminary version in MFCS 2012. https://doi.org/10.1145/2656210 ; arXiv:1202.1936. Read in arXiv v2 (29 June 2012) on 2026-11-08. §5, in the paragraph before Theorem 5.2, attributes `DistNP ⊆ Avg-P ⇒ NE = E` to Ben-David, Chor, Goldreich and Luby. Journal metadata checked against the Crossref record.

<a id="bmr16"></a>
## bmr16

Marshall Ball, Tal Malkin, Mike Rosulek. "Garbling Gadgets for Boolean and Arithmetic Circuits." *Proceedings of the 2016 ACM SIGSAC Conference on Computer and Communications Security (CCS '16)*, 565–577, 2016. https://doi.org/10.1145/2976749.2978410 . Full version: Cryptology ePrint Archive, Report 2016/969. Bibliographic data from the DOI record. Checked on 2026-11-14 against the ePrint full version dated October 6, 2016 (22 pages, SHA-256 `e9a7cfec82e60b3c71970f8d617015ab0b731bb53d76710fcbf07bbb11a74755`); locators use its printed page numbers, which are also its PDF page numbers. §4.1, p. 5: labels `W^x = W^0 + xΔ_m`, multiplication by a constant `c` coprime to `m`, and key length `λ_m = ⌈λ / log m⌉` (logarithms base 2, §2, p. 3). §4.2, p. 6: each wire has its own modulus, and a projection gate costs `m - 1` ciphertexts after choosing `W_j^0 = -H(g, W_i^{-τ}) - φ(-τ)Δ_n`. Figure 1, p. 7: the garbling scheme for mixed-moduli simple circuits, in which all ciphertexts of a projection gate use that gate's tweak. §4.3, p. 7: the oracle `O(g, i, j, X, a, c) = H(g, X + aΔ_{m_i}) + cΔ_{m_j}`, Definition 1 (mixed-modulus circular correlation robustness against polynomial-time adversaries that query their oracle on distinct `g` values and `a ≠ 0`) and Theorem 1. Proof sketch of Theorem 1, pp. 7–8: it replaces every ciphertext with `a ≠ 0` using only the oracle of Definition 1, hence with `m - 1` queries under one tweak, and states the authenticity bound `1 / 2^λ` (p. 8). Moduli are not restricted to primes: the gadgets use mod-`(b + 1)` wires (§5, p. 8), output modulus `k + 1` (§6.2, p. 11) and `Z_{p+q-1}` (§6.3, pp. 12–13). §4.3 does not analyse zero divisors of composite moduli. An earlier pass read the ePrint text on 2026-11-09.

<a id="bmr90"></a>
## bmr90

Donald Beaver, Silvio Micali, Phillip Rogaway. "The Round Complexity of Secure Protocols." *Proceedings of the 22nd Annual ACM Symposium on Theory of Computing (STOC '90)*, 503–513, 1990. https://doi.org/10.1145/100216.100287 . Bibliographic data from the DOI record and secondary listings, cited as the usual source of the point-and-permute technique. The full text was not inspected in this pass.

<a id="bodlaenderdowneyfellowshermelin2009"></a>
## bodlaenderdowneyfellowshermelin2009

Hans L. Bodlaender, Rodney G. Downey, Michael R. Fellows and Danny Hermelin. "On Problems without Polynomial Kernels." *Journal of Computer and System Sciences* 75(8), 423–434, 2009. https://doi.org/10.1016/j.jcss.2009.04.001 . Bibliographic data from the reference list of [Bodlaender, Jansen and Kratsch](#bodlaenderjansenkratsch2014), item [4]. The paper was not inspected; the manual cites it only through that paper's attribution of the k-Path kernel lower bound (Section 1, p. 2 of arXiv v1), and no theorem number is used.

<a id="bodlaenderjansenkratsch2014"></a>
## bodlaenderjansenkratsch2014

Hans L. Bodlaender, Bart M. P. Jansen and Stefan Kratsch. "Kernelization Lower Bounds by Cross-Composition." *SIAM Journal on Discrete Mathematics* 28(1), 277–305, 2014. https://doi.org/10.1137/120880240 . Inspected the arXiv version [1206.5941v1](https://arxiv.org/abs/1206.5941v1) on 2026-11-08: Definition 1 (kernelization, generalized kernelization, p. 4), Definition 2 (compression, p. 5), Proposition 1 (p. 5), Definition 4 (weak OR-distillation, p. 5), Theorem 2 (Fortnow–Santhanam, p. 6), Lemma 1 (complementary witness lemma, attributed to Dell and van Melkebeek, p. 7), Definition 8 (polynomial equivalence relation, p. 8), Definition 9 (and/or-cross-composition, p. 8), Theorem 5 and Corollary 2 (p. 9), Theorem 6 with its proof (pp. 10–11), the attribution of the k-Path kernel lower bound in Section 1 (p. 2) and the equivalence relation in the proof of Theorem 7 (p. 13). Locators follow that arXiv numbering; the journal numbering was not checked.

<a id="borodin72"></a>
## borodin72

Allan Borodin. *Computational Complexity and the Existence of Complexity Gaps*. Journal of the ACM 19(1), 158–174, 1972. https://doi.org/10.1145/321679.321691 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the gap theorem and the almost-everywhere class convention to this paper.

<a id="borodinelyaniv98"></a>
## borodinelyaniv98

Allan Borodin, Ran El-Yaniv. *Online Computation and Competitive Analysis*. Cambridge University Press, 1998. The chapter outline, in particular Chapter 1 on list accessing, comes from the publisher's table of contents; the book text was not inspected in this pass. The manual cites it only as a textbook pointer for ski rental and for the deterministic list-accessing lower bound, with no theorem numbers.

<a id="bregman73"></a>
## bregman73

L. M. Brégman. "Some properties of nonnegative matrices and their permanents." *Soviet Mathematics Doklady* 14, 945–949, 1973; translated from *Doklady Akademii Nauk SSSR* 211, 27–30, 1973. Bibliographic data from secondary sources; the paper was not inspected. The manual credits it only with the statement of the bound `per A ≤ ∏ i, (r i)! ^ (1 / r i)` for 0/1 matrices.

<a id="broder97"></a>
## broder97

Andrei Z. Broder. “On the Resemblance and Containment of Documents.” *Proceedings of Compression and Complexity of Sequences 1997* (SEQUENCES 1997), IEEE, 21–29. https://doi.org/10.1109/SEQUEN.1997.666900 . DOI and metadata as reported by search indexes; neither the DOI nor the full text was resolved in this pass (no connection to the publisher). The manual credits it with the MinHash identity `Pr[min σ(A) = min σ(B)] = |A ∩ B|/|A ∪ B|` for a uniform permutation, which secondary sources attribute to it.

<a id="bs23"></a>
## bs23

Dan Boneh and Victor Shoup. *A Graduate Course in Applied Cryptography*, version 0.6, January 2023. https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf . Title, authors and edition verified from the primary PDF during independent source review on 2026-11-02. Detailed textbook locator claims remain attributed to the Lean source docstrings; no complete textbook correspondence audit was performed.

<a id="bt06"></a>
## bt06

Andrej Bogdanov and Luca Trevisan. *Average-Case Complexity*. Foundations and Trends in Theoretical Computer Science 2(1), 1–106, 2006. https://doi.org/10.1561/0400000004 ; arXiv:cs/0606037. Definition, lemma and theorem numbers (Definitions 1, 2, 6, 8–11 and 17, Proposition 7, Lemma 18, Theorem 19, Claim 20) were checked against the arXiv text on 2026-11-07.

<a id="burrowswheeler94"></a>
## burrowswheeler94

Michael Burrows and David J. Wheeler. *A Block-sorting Lossless Data Compression Algorithm*. SRC Research Report 124, Digital Systems Research Center, Palo Alto, 10 May 1994. Openly hosted copy: https://www.cs.jhu.edu/~langmea/resources/burrows_wheeler.pdf . On 2026-11-08 UTC the worker checked the following against that copy: Section 2, Algorithm C (steps C1–C2, with `I` the first row equal to `S`, numbered from zero) and Algorithm D (steps D1–D3), the running example `S = abraca`, `L = caraab`, `I = 1`, `T = (4 0 5 1 2 3)`, the remark after D3 on periodic `S`, and Section 4.2 (the arrays `C` and `P`, with `T[i] = P[i] + C[L[i]]`). The HP Labs copy of the report could not be reached (connection failure), so it was not compared.

<a id="canetti20"></a>
## canetti20

Ran Canetti. *Universally Composable Security*. Journal of the ACM 67(5), Article 28, 2020; full version Cryptology ePrint Archive 2000/067. https://doi.org/10.1145/3402457 .

<a id="canonne22"></a>
## canonne22

Clément L. Canonne. *Topics and Techniques in Distribution Testing: A Biased but Representative Sample*. Foundations and Trends in Communications and Information Theory 19(6), 1032–1198, 2022. https://doi.org/10.1561/0100000114 . Checked on 2026-11-10 against the author-hosted draft dated March 10, 2024 at https://ccanonne.github.io/files/misc/main-survey-fnt.pdf (journal pagination not inspected; locators follow that March 10, 2024 draft): Appendix B (pp. 149–152: Definition B.1, `(B.1)`–`(B.3)`, `(B.5)`–`(B.6)`, Lemmas B.1, B.2, and B.5) for Hellinger/`χ²`/KL definitions, tensorization, and comparison inequalities, and Section 3.1 (pp. 99–103: `(3.3)`, Lemma 3.1, and `(3.10)`) for the `√(2n)` Hellinger i.i.d. bound and Ingster's mixture second-moment identity (`CslibFrontier/Probability/{Hellinger,ChiSquare}.lean`).

<a id="carmosinoimpagliazzokabanetskolokolova2016"></a>
## carmosinoimpagliazzokabanetskolokolova2016

Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova. *Learning Algorithms from Natural Proofs*. 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 10:1–10:24, 2016. https://doi.org/10.4230/LIPIcs.CCC.2016.10 . Checked on 2026-11-11 against the LIPIcs PDF: Section 2.4, Definitions 2.8–2.10, Theorem 2.11 and the sketch of the reconstruction algorithm that follows it (p. 10:9), which `CslibFrontier/MachineLearning/UniformLearning/NisanWigderson.lean` follows for one run. For the AC⁰[2] efficiency of their generator ([#4451](https://github.com/cslib-community/cslib-frontier/issues/4451)), also checked on 2026-11-11 against the LIPIcs PDF: Definition 3.1, Theorems 3.2 and 3.3 (p. 10:10) and the proof of Theorem 3.2 (p. 10:11); Definition 3.4 (black-box amplification, pp. 10:10–10:11) and Lemma 3.5 (p. 10:11); Section 3.1, which opens on p. 10:11 with the design requirements; Theorem 3.6 and its proof (pp. 10:12–10:13), which define the polynomials `A_i` and the sets `S_i`, bound their overlap on p. 10:12 and end with the hard-coded matrix `M_{j,k} = r_j^k`; Theorem 3.7 and its proof (p. 10:13); and Theorem 4.3 (p. 10:15) with its proof (pp. 10:15–10:16). `CslibFrontier/Crypto/Primitives/PRG/NisanWigderson/{BitPolynomial,MXCircuit,AmpGeneratorCircuit}.lean` and `CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/{GLAmp,GLAmpCircuit}.lean` follow them for `p = 2`. For the reconstruction for `p = 2`, also checked on 2026-11-11 against the LIPIcs PDF: Theorem 4.1 (p. 10:14); Theorem 4.2 and the sketch of its algorithm (p. 10:15); and Claim 4.4 (p. 10:15), whose proof and the combination with Theorem 4.1 that ends the proof of Theorem 4.3 follow on pp. 10:15–10:16. `CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/GLAmpDecode.lean` and `CslibFrontier/MachineLearning/UniformLearning/CIKK/Amplification.lean` follow them. For the `p = 2` natural property and the learner built from it, also checked on 2026-11-11 against the LIPIcs PDF, by an agent in the [M6.7 gate note](https://github.com/cslib-community/cslib-frontier/issues/4451#issuecomment-6791276714): Theorems 5.1 and 5.3 (p. 10:19) and the sketch of the `p = 2` rank property (p. 10:20). `CslibFrontier/Computability/Circuit/Boolean/Razborov/RankProperty.lean` follows that sketch in a variant, and `CslibFrontier/MachineLearning/UniformLearning/CIKK/Learner.lean` follows Theorem 5.1 in a per-function black-box form.

<a id="ccpv11"></a>
## ccpv11

Gruia Călinescu, Chandra Chekuri, Martin Pál, Jan Vondrák. “Maximizing a Monotone Submodular Function subject to a Matroid Constraint.” *SIAM Journal on Computing* 40(6), 1740–1766, 2011. https://doi.org/10.1137/080733991 . The `p`-system definition and the greedy ratios `1/p` (modular) and `1/(p+1)` (monotone submodular) in Section 1, and the proof of the `1/(p+1)` bound in Appendix B (“Analysis of Greedy for p-systems”), were checked on 2026-11-08 against the authors' manuscript dated September 21, 2009, at https://theory.stanford.edu/~jvondrak/data/submod-matroid.pdf ; the journal pagination was not checked. The manual reports the original Fisher–Nemhauser–Wolsey and Jenkyns attributions as stated in this paper.

<a id="cdpw07"></a>
## cdpw07

Ran Canetti, Yevgeniy Dodis, Rafael Pass and Shabsi Walfish. *Universally Composable Security with Global Setup*. TCC 2007, Lecture Notes in Computer Science 4392, 61–85; full version Cryptology ePrint Archive 2006/432. https://doi.org/10.1007/978-3-540-70936-7_4 . The primary text was not inspected, and no theorem number is claimed. The manual attributes to this paper only the setting of sessions that share a global functionality which the environment also queries directly.

<a id="cf01"></a>
## cf01

Ran Canetti and Marc Fischlin. *Universally Composable Commitments*. CRYPTO 2001, Lecture Notes in Computer Science 2139, 19–40, 2001; full version Cryptology ePrint Archive 2001/055. https://doi.org/10.1007/3-540-44647-8_2 . Section 2.2, Figure 2 (`F_com`, p. 10) and Section 3, Theorem 6 (p. 12) were checked against the full version, Cryptology ePrint Archive 2001/055. The library proves an adaptation and special case of Theorem 6: one commitment message and one opening message, a constant completeness gap, a single simulator fixed before the environment, and call-counted (not machine-efficiency) bounds. Theorem 6 for general bilateral protocols and the computational setting is not formalized.

<a id="cgks98"></a>
## cgks98

Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan. *Private Information Retrieval*. Journal of the ACM 45(6), 965–981, 1998; preliminary version FOCS 1995. https://doi.org/10.1145/293347.293350 . Definition 1 (§2.1, p. 4), the coalition `t`-privacy extension of §2.2 (pp. 4–5, and the polynomial family noted without construction in §1.1, pp. 1–2), the polynomial-time requirement of §2.4 (p. 6), the schemes of §§3.1, 3.2 and 3.4 (Proposition 4, Corollary 3; pp. 6–8, 11), the covering-code schemes of §3.3 (Theorem 1, Footnote 1 on exact covers, the `d = 5, k = 7` row of Figure 1, the radius-`2` covering remark `k · d · n ^ (1 / d) + k · C(d, 2) · n ^ (2 / d)`, and Corollary 2; pp. 8–10), the block-retrieval transformations and constant-overhead schemes of §4 (Propositions 4 and 5, the group-homomorphism note on p. 12, Corollaries 6, 7 and 8; pp. 11–13), the single-server bound of §5.1 in its one-round and interactive forms, and §5.2 (the Claim, its two observations and the closing note on the even-set scheme) were checked on 2026-11-08, 2026-11-11 and 2026-11-12 against the authors' journal version of April 21, 1998, at http://people.csail.mit.edu/madhu/papers/1995/pir-journ.pdf (§5 is on pp. 13–15). In [PIR/GeneralCover.lean](../CslibFrontier/Crypto/Protocols/PIR/GeneralCover.lean), Theorem 1 (`hasIndexedScheme_of_hammingDist`) states explicit `0 < |D|` and `Function.Injective code` hypotheses (`d - 1` truncates at `d = 0` in `ℕ`, and duplicate codewords would violate `k ≤ 2 ^ d`), while for radius-`2` covers `hasScheme_of_hammingDist_two` proves the full-ball count `k · (2 · d · ℓ + C(d, 2) · ℓ² + 1) = k · d · ℓ + k · C(d, 2) · ℓ² + k · (d · ℓ + 1)` (CGKS p. 10's displayed leading expression `k · d · ℓ + k · C(d, 2) · ℓ²` plus the `k · (d · ℓ + 1)` distance-`0`/`1` answer bits; the literal `k · d · ℓ + k · C(d, 2) · ℓ²` bound without lower-order answer terms is not proved) alongside the exact radius-`r` count `k · (d · ℓ + ∑_{j ≤ r} C(d, j) · ℓ ^ j)` and the coarser `d²` upper bound `k · d · ℓ + k · d² · ℓ²` (`hasScheme_of_hammingDist_two_sq`, for `2 ≤ |D|` and `1 ≤ ℓ`). Because §1.1 omits the polynomial-interpolation construction while stating `O(t(n) · n ^ (1 / c))` for `c · t(n)` servers, [PIR/Shamir.lean](../CslibFrontier/Crypto/Protocols/PIR/Shamir.lean) formalizes an explicit finite-field adaptation over `Shamir.Params F S` that matches `k = c · t` servers and fixed-`t` exponent `n ^ (1 / c)` while retaining the field bit-width factor `⌈log₂ |F|⌉` (`|F| > c · t`, a weaker finite-field communication variant). Neither polynomial-time computation (§2.4, p. 6; §3.3 Remark, p. 10) nor fair-coin simulation of finite-uniform `ProbComp` primitives is modeled. In the interactive form, the user's output may depend on its coins, so the source's step that the same communication forces the same output is replaced by the rectangle property of protocols. The typeset JACM PDF was not consulted; locators follow the authors' version.

<a id="chaitin74"></a>
## chaitin74

Gregory J. Chaitin. *Information-Theoretic Limitations of Formal Systems*. Journal of the ACM 21(3), 403–424, 1974. https://doi.org/10.1145/321832.321839 . Bibliographic metadata checked on 2026-11-08; the paper is behind the ACM paywall and was not inspected. The manual attributes the incompleteness theorem for program-size complexity to it, following the customary attribution; its theorem numbers and the exact form of its bound are unverified. The Lean docstrings also cite the textbook treatment in Li and Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 4th edition (Springer, 2019), Chapter 2; the section and theorem locator within that chapter was not checked.

<a id="chakrabarti25"></a>
## chakrabarti25

Amit Chakrabarti. *Data Stream Algorithms: Lecture Notes*. Dartmouth College, latest update July 1, 2025. https://www.cs.dartmouth.edu/~ac/Teach/data-streams-lecnotes.pdf . Locators checked against that PDF on 2026-11-07 UTC: Unit 1 (Section 1.1 for the MAJORITY and FREQUENT problems, Algorithm 1 and Theorem 1.3.1 for Misra–Gries, Exercise 1-1 for the `(m − m̂)/k` sharpening), Section 2.4 (the median trick) and Section 5.3 (Algorithms 7–8 and equations (5.1)–(5.7) for the Count-Sketch).

<a id="charikar02"></a>
## charikar02

Moses S. Charikar. “Similarity Estimation Techniques from Rounding Algorithms.” *Proceedings of the 34th Annual ACM Symposium on Theory of Computing* (STOC 2002), 380–388. https://doi.org/10.1145/509907.509965 . DOI and metadata as reported by search indexes; the DOI was not resolved in this pass. The locator Lemma 1 (for a similarity admitting a locality-sensitive hashing scheme, `1 − sim` satisfies the triangle inequality) was not checked against the full text in this pass.

<a id="charikar04"></a>
## charikar04

Moses Charikar, Kevin Chen, Martin Farach-Colton. “Finding Frequent Items in Data Streams.” *Theoretical Computer Science* 312(1), 3–15, 2004; preliminary version in ICALP 2002. https://doi.org/10.1016/S0304-3975(03)00400-6 . Bibliographic data from search summaries of the DOI record; the Count-Sketch statements formalized here follow the presentation of [chakrabarti25](#chakrabarti25), Section 5.3. The journal text was not inspected in this pass.

<a id="chattopadhyayliao20"></a>
## chattopadhyayliao20

Eshan Chattopadhyay and Jyun-Jie Liao. *Optimal Error Pseudodistributions for Read-Once Branching Programs*. 35th Computational Complexity Conference (CCC 2020), LIPIcs 169, 25:1–25:27, 2020. https://doi.org/10.4230/LIPIcs.CCC.2020.25 ; cited from arXiv:2002.07208v4. Appendix A.1 (Definition A.2, Lemmas A.3 and A.4) was checked against the arXiv v4 text on 2026-11-08. Hoza (2021) cites the CCC version's Lemma 43 for the same material.

<a id="chendeng06"></a>
## chendeng06

Xi Chen and Xiaotie Deng. "On the Complexity of 2D Discrete Fixed Point Problem." *Automata, Languages and Programming (ICALP 2006)*, LNCS 4051, 489–500, Springer, 2006. https://doi.org/10.1007/11786986_43 ; journal version in *Theoretical Computer Science* 410(44), 4448–4456, 2009, https://doi.org/10.1016/j.tcs.2009.07.052 . Bibliographic metadata as recorded in `references.bib`; the paper's full text was not inspected directly, so no internal theorem number or page locator is cited. The library cites it for the `PPAD`-completeness of two-dimensional discrete Sperner (`Sperner2D`) proved in [SpernerHardness.lean](../CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/SpernerHardness.lean) via an explicit polynomial-time circuit reduction from `EndOfLine` on a `2 ^ (n + 5) × 2 ^ (n + 5)` grid tiled by `16 × 16` crossing and turning cells.

<a id="chenhiraharaoliveirapichrajgopalsanthanam2020"></a>
## chenhiraharaoliveirapichrajgopalsanthanam2020

Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Ján Pich, Ninad Rajgopal and Rahul Santhanam. *Beyond Natural Proofs: Hardness Magnification and Locality*. ITCS 2020, LIPIcs 151. https://doi.org/10.4230/LIPIcs.ITCS.2020.70 ; full version ECCC TR19-168. Checked against the ECCC full version on 2026-11-11: Definition 3 (learning by circuits with non-adaptive membership queries, Section 2.2, p. 12), Lemma 34 (its use of a non-adaptive learner with the seed fixed by Adleman's trick, pp. 25–27), Definition 11 (local circuit classes `[q, ℓ, a]–C[s]`, Section 2.5, p. 13) and the MCSP `[OS18]` and `[MMW19]` bullets of Proposition 63 (Appendix A.2, p. 52). Theorem numbers follow the ECCC numbering.

<a id="christofides76"></a>
## christofides76

Nicos Christofides. *Worst-Case Analysis of a New Heuristic for the Travelling Salesman Problem*. Report 388, Graduate School of Industrial Administration, Carnegie-Mellon University, 1976; reprinted in *Operations Research Forum* 3, article 20, 2022, https://doi.org/10.1007/s43069-021-00101-z . The report details are those of reference [73] in [Williamson and Shmoys](#williamsonshmoys11), whose Chapter 2 Notes attribute the algorithm to Christofides; the reprint details come from search summaries. Neither the report nor the reprint was checked; the formalization follows the proof of Theorem 2.13 of Williamson and Shmoys.

<a id="chrobakkarloffpaynevishwanathan91"></a>
## chrobakkarloffpaynevishwanathan91

Marek Chrobak, Howard J. Karloff, Thomas H. Payne, Sundar Vishwanathan. "New Results on Server Problems." *SIAM Journal on Discrete Mathematics* 4(2), 172–181, 1991. https://doi.org/10.1137/0404017 . Bibliographic metadata only; the full text was not inspected in this pass, so no theorem number is cited. The manual credits this paper with the `k`-competitiveness of Double Coverage on the line, which secondary sources attribute to it; the local proof uses the standard potential `k·M_min + Σ_{i<j}|s_i - s_j|`.

<a id="chuliu65"></a>
## chuliu65

Yoeng-Jin Chu and Tseng-Hong Liu. "On the Shortest Arborescence of a Directed Graph." *Scientia Sinica* 14, 1396–1400, 1965. The bibliographic details come from search summaries; the paper was not inspected, and no theorem locator is claimed. The manual cites it as the earlier, independent source of the cycle-contraction algorithm for minimum-cost arborescences; the formalization follows [Edmonds 1967](#edmonds67b).

<a id="chvatal83"></a>
## chvatal83

Vašek Chvátal. *Linear Programming*. W. H. Freeman, New York, 1983. Bibliographic data from library and search summaries; the book was not inspected in this pass. The chapter locators used in the manual and docstrings (Chapter 2 for dictionaries, pivoting and the optimality test; Chapters 2–3 for the unboundedness test, which search summaries of the table of contents place in Chapter 3; Chapter 3 for cycling, the cycling example and the smallest-subscript rule; Chapter 4 for the Klee–Minty programs and the `2^n - 1` pivots of the largest-coefficient rule on them; Chapter 5 for duality and the dual solution read off the final dictionary) come from secondary summaries and memory of the book, not from a copy, and are unverified. The coefficients of the cycling example in `CslibFrontierTests/Algorithms/Lean/Simplex.lean` were taken from those summaries and checked by running Dantzig's rule on them, which returns to the initial basis after six degenerate pivots.

<a id="ckkz12"></a>
## ckkz12

Seung Geol Choi, Jonathan Katz, Ranjit Kumaresan and Hong-Sheng Zhou. "On the Security of the 'Free-XOR' Technique." *Theory of Cryptography (TCC 2012)*, 39–53, 2012. https://doi.org/10.1007/978-3-642-28914-9_3 ; full version: Cryptology ePrint Archive, Report 2011/510, https://eprint.iacr.org/2011/510 . Checked on 2026-11-15 against the ePrint PDF of October 5, 2011 (14 pages, SHA-256 `3a8fe73ee05f8abb9d1079da877d1d6a0f42346d05f3a41e7ed630f616ab3897`); locators use its printed page numbers, which are also its PDF page numbers; this is the author's check, which no reviewer has yet repeated at the source, so the library cites these locators as not verified. §4, p. 9: the oracle `Circ_R(w, w′, g, b₁, b₂, b₃) = H(w ⊕ b₁R ‖ w′ ⊕ b₂R ‖ g) ⊕ b₃R`, the random oracle `Rand` and the legal queries. P. 10: Definition 4, circular 2-correlation robustness against non-uniform polynomial-time distinguishers, and Theorem 3, security of the free-XOR protocol against a semi-honest adversary in the OT-hybrid model. Cited for the origin of circular correlation robustness; the library formalizes no dual-key notion.

<a id="cks20"></a>
## cks20

Clément L. Canonne, Gautam Kamath and Thomas Steinke. *The Discrete Gaussian for Differential Privacy*. NeurIPS 2020; cited from arXiv:2004.00010v5, 2021. https://arxiv.org/abs/2004.00010 . Definition 28 and Lemmas 29–30 were checked against the arXiv v5 PDF on 2026-11-07.

<a id="clrs09"></a>
## clrs09

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest and Clifford Stein. *Introduction to Algorithms*, third edition. MIT Press, 2009. ISBN 978-0-262-03384-8. Section 35.1, procedure `APPROX-VERTEX-COVER` and Theorem 35.1 (it is a polynomial-time 2-approximation algorithm). The locator 35.1 was checked against secondary course material, not the printed book. Sections 22.3–22.4 (depth-first search; Lemma 22.11, acyclic if and only if no back edges; Theorem 22.12, correctness of `TOPOLOGICAL-SORT`) and Section 24.1 (Bellman–Ford; Lemma 24.2, estimates equal shortest-path weights after `|V| - 1` passes when no negative cycle is reachable; Theorem 24.4, correctness of `BELLMAN-FORD`) were likewise checked against secondary course material. Sections 25.1 ("Shortest paths and matrix multiplication": repeated (min,+) squaring) and 25.2 ("The Floyd–Warshall algorithm") are the all-pairs shortest-path locators. They were checked against the edition's published table of contents only. Section 26.4 ("Push-relabel algorithms") is the push–relabel locator. Its statement numbers were checked against secondary course material, not the printed book: Lemma 26.14 (an overflowing vertex admits a push or a relabel), Lemma 26.15 (heights never decrease, and a relabel raises them), Lemma 26.16 (push and relabel keep a height function), Lemma 26.17 (no residual `s`–`t` path), Theorem 26.18 (correctness at termination), Lemma 26.19 (an overflowing vertex reaches `s` in the residual network), Lemma 26.20 (heights stay below `2|V|`), Corollary 26.21 (fewer than `2|V|²` relabels), Lemmas 26.22 and 26.23 (fewer than `2|V||E|` saturating and fewer than `4|V|²(|V| + |E|)` nonsaturating pushes) and Theorem 26.24 (`O(|V|² |E|)` basic operations). Section 9.3 ("Selection in worst-case linear time") is the locator for the groups-of-five median-of-medians algorithm and its counting step; it was not checked against the printed book. Section 9.1 ("Minimum and maximum") is the locator for the linear scan for the minimum and for finding the minimum and maximum together with `3⌊n/2⌋` comparisons by comparing pairs; secondary course material places the lower bound `⌈3n/2⌉ - 2` for the minimum and maximum in Exercise 9.1-2. Neither locator was checked against the printed book. Section 15.4 ("Longest common subsequence": Theorem 15.1, optimal substructure of an LCS, and the running example `ABCBDAB`, `BDCABA` with an LCS of length `4`) and Problem 15-5 ("Edit distance") are the edit-distance and LCS locators. They were checked against secondary course material, not the printed book. Section 15.5 ("Optimal binary search trees": the recurrence for `e[i, j]` and the five-key example with expected cost 2.75) was checked against secondary course material, not the printed book. Kosaraju's two-pass strongly connected components algorithm in [DFS/SCC.lean](../CslibFrontier/Algorithms/Lean/DFS/SCC.lean) cites the book without attributing a section or theorem number, as the corresponding section has not been checked against the printed book.

<a id="complexitylib"></a>
## complexitylib

cslib-frontier contributors. *cslib-frontier* (named Complexitylib at this snapshot), source snapshot `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`. [Pinned repository](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8). Individual declarations are linked in the text. The repository bibliography records mathematical sources; attribution here reports those source annotations unless independent verification is explicitly stated.

<a id="cook74"></a>
## cook74

Stephen A. Cook. *An Observation on Time-Storage Trade Off*. Journal of Computer and System Sciences 9(3):308-316, 1974. The pyramid lower bound was checked through its statement as Theorem 4.8 of [nordstrom15](#nordstrom15).

<a id="cookmertz24"></a>
## cookmertz24

James Cook and Ian Mertz. *Tree Evaluation is in Space O(log n · log log n)*. STOC 2024; full report ECCC TR23-174 (15 November 2023). https://eccc.weizmann.ac.il/report/2023/174/ .

<a id="cookreckhow73"></a>
## cookreckhow73

Stephen A. Cook, Robert A. Reckhow. “Time Bounded Random Access Machines.” *Journal of Computer and System Sciences* 7(4), 354–375, 1973. https://doi.org/10.1016/S0022-0000(73)80029-7 . Local source explicitly labels its adaptation; publisher fetch unavailable in this pass.

<a id="cookreckhow79"></a>
## cookreckhow79

Stephen A. Cook, Robert A. Reckhow. “The Relative Efficiency of Propositional Proof Systems.” *The Journal of Symbolic Logic* 44(1), 36–50, 1979. https://doi.org/10.2307/2273702 . The manual cites this paper for the notion of a Frege system. The simulation of resolution by the Frege system in the [proof-systems chapter](circuits-logic-and-other-models/proof-systems.md) is presented as a standard fact in this framework, with no theorem locator; the paper itself was not re-inspected in this pass.

<a id="cormode05"></a>
## cormode05

Graham Cormode, S. Muthukrishnan. “An Improved Data Stream Summary: The Count-Min Sketch and its Applications.” *Journal of Algorithms* 55(1), 58–75, 2005. https://doi.org/10.1016/j.jalgor.2003.12.001 ; author PDF https://www.cs.ox.ac.uk/people/graham.cormode/pubs/papers/cm-full.pdf . Sections 3–4.1 and fixed point-query guarantee consulted.

<a id="correaschulzstiermoses04"></a>
## correaschulzstiermoses04

José R. Correa, Andreas S. Schulz and Nicolás E. Stier-Moses. *Selfish Routing in Capacitated Networks*. Mathematics of Operations Research 29(4), 961–976, 2004. https://doi.org/10.1287/moor.1040.0098 . Bibliographic metadata only; the publisher's text is paywalled and no open author's version was found, so it was not inspected and no locator in it is cited. Following [roughgarden13cs364a](#roughgarden13cs364a), Lecture #11, Theorem 3.3, which credits it, `CslibFrontier/GameTheory/Congestion/PigouBound.lean` cites it for the Pigou-bound theorem in the generality formalized there.

<a id="coverthomas06"></a>
## coverthomas06

Thomas M. Cover and Joy A. Thomas. *Elements of Information Theory*, second edition. Wiley-Interscience, 2006. https://doi.org/10.1002/047174882X . Section 5.11, "Generation of discrete distributions from fair coins": Theorem 5.11.1 (`H(X) ≤ E[T]` for every generating tree), Theorem 5.11.2 (equality for dyadic distributions) and Theorem 5.11.3 (`H(X) ≤ E[T] < H(X) + 2` for the optimal tree). The theorem numbers and statements were taken from secondary summaries and course notes on 2026-11-08; the printed book was not inspected. Also cited for Section 2.10 (Fano's inequality: Theorem 2.10.1, the corollary after it with the sharper `log(|𝒳| − 1)` form for estimators valued in `𝒳`, and the remark on guessing without side information), Section 7.1 (capacity of the binary symmetric channel), Lemma 7.9.2 and Theorem 7.9.1 (the converse to the channel coding theorem); these locators were likewise checked against secondary course material, not the printed book.

Chapter 13 (universal source coding): the Lempel–Ziv tree-structured (incremental) parsing, its example `ABBABBABBBAABABAA`, and the distinct-parsing lemma `c(n) ≤ n / ((1 - ε_n) log n)` with `ε_n = min(1, (log log n + 4) / log n)` in §13.5. The library cites only the section; secondary sources disagree on the lemma's number. The section, the lemma's statement and the example were taken from secondary course material and search summaries and were not checked against the printed book.

<a id="cs03"></a>
## cs03

Ronald Cramer and Victor Shoup. “Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack.” *SIAM Journal on Computing* 33(1), 167–226, 2003. https://doi.org/10.1137/S0097539702403773 . Authors' revised manuscript (August 14, 2003): https://www.shoup.net/papers/cca2.pdf (Section 5.1, target collision resistance; Section 6.1, Figure 1, the hash key `hk` drawn at key generation and published in the public key; Section 6.2, Theorem 1). Checked against that manuscript on 2026-11-14.

<a id="cslib"></a>
## cslib

CSLib contributors. *CSLib*, pinned dependency snapshot `254e30e6d4299c51323aaeaf5f51a4763b375d4a`. [Pinned repository](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a).

<a id="cygan2015"></a>
## cygan2015

Marek Cygan, Fedor V. Fomin, Łukasz Kowalik, Daniel Lokshtanov, Dániel Marx, Marcin Pilipczuk, Michał Pilipczuk, and Saket Saurabh. *Parameterized Algorithms*. Springer, 2015. [DOI](https://doi.org/10.1007/978-3-319-21275-3). Inspected the authors' companion PDF dated 2016-05-30: Definitions 1.2–1.3 (p. 13), Definition 2.1 (pp. 18–19), Lemma 2.2 (p. 20), and Section 2.2.1 (pp. 21–22); accessed 2026-11-02. On 2026-11-08 the same PDF returned HTTP 403, so the crown material of Section 2.3 cited by [Crown](../CslibFrontier/Foundations/Combinatorics/SimpleGraph/Crown.lean) was not inspected. Secondary sources number the crown lemma Lemma 2.14 and the `3k` kernel Theorem 2.16; these numbers are unverified and are not used in the Lean docstrings. The color-coding locators Section 5.2 and Lemma 5.5, the fpt-reduction locator Section 13.1, and the tree-decomposition locator Section 7.3.1 (weighted independent set, stated for `n`-vertex graphs), used in [parameterized complexity](machines-and-classes/parameterized-complexity.md), were not re-inspected. Section 4.4 (iterative compression for odd cycle transversal), cited by [OddCycleTransversal](../CslibFrontier/Foundations/Combinatorics/SimpleGraph/OddCycleTransversal.lean) and its algorithm, was not inspected either; its locator comes from secondary sources. Likewise, nice tree-decomposition normalization (Lemma 7.4, p. 161), bounded-treewidth CSP dynamic programming, and the clause-grouping `3-SAT`-to-`Clique` ETH lower bound (Theorem 14.21, p. 485) were inspected in the companion PDF and verified, matching the locators in the [results registry](../CslibFrontierResults/Entries.lean).

The same author PDF supports the weighted-circuit enumeration in Section 13.3, p. 436, and the definition of `W[t]` in Definition 13.16, p. 437, used in [parameterized complexity](machines-and-classes/parameterized-complexity.md). This section does not define `W[P]`; the library's `WP` reduction closure is documented separately and its equivalence with an effective literature class is not claimed.

<a id="dasguptagupta03"></a>
## dasguptagupta03

Sanjoy Dasgupta, Anupam Gupta. “An Elementary Proof of a Theorem of Johnson and Lindenstrauss.” *Random Structures & Algorithms* 22(1), 60–65, 2003. https://doi.org/10.1002/rsa.10073 . Author-hosted copy: https://cseweb.ucsd.edu/~dasgupta/papers/jl.pdf . Checked against that copy on 2026-11-07 UTC: Theorem 2.1 on p. 61 (`0 < ε < 1` and `k ≥ 4 (ε²/2 - ε³/3)⁻¹ ln n`), and Lemma 2.2 on p. 62 (tails for the projection of a random unit vector onto `k` coordinates, proved with `𝔼 exp (sX²) = (1 - 2s)^(-1/2)` for a standard Gaussian `X`).

<a id="desimone90"></a>
## desimone90

Caterina De Simone. "The cut polytope and the boolean quadric polytope." *Discrete Mathematics* 79(1), 71–75, 1990. https://doi.org/10.1016/0012-365X(90)90056-N . Bibliographic metadata checked via search summaries on 2026-11-11 UTC; the primary paper was not inspected and no locator in it is cited. Cited alongside [fmptw15](#fmptw15), Theorem 5, for the linear isomorphism between `CUT(n + 1)` and `CORR(n)`.
<a id="datar04"></a>
## datar04

Mayur Datar, Nicole Immorlica, Piotr Indyk and Vahab S. Mirrokni. “Locality-sensitive hashing scheme based on p-stable distributions.” *Proceedings of the Twentieth Annual Symposium on Computational Geometry (SoCG 2004)*, ACM, 253–262, 2004. https://doi.org/10.1145/997817.997857 . Bibliographic metadata checked against DBLP search results; the full text was not inspected (attempted archive links returned HTTP 404), so section and theorem locators remain unverified.

<a id="devroyelugosi01"></a>
## devroyelugosi01

Luc Devroye and Gábor Lugosi. *Combinatorial Methods in Density Estimation*. Springer Series in Statistics, Springer, New York, 2001. ISBN 978-0-387-95117-1. https://doi.org/10.1007/978-1-4613-0125-7 . Bibliographic metadata checked via search summaries on 2026-11-11; the book text was not inspected, so Chapter 6 attribution is unverified against the printed book. Cited as background for Scheffé sets (`scheffeSet`), pairwise Scheffé tests (`scheffeTest`), and `3 * OPT + 2 * γ` minimum-distance TV selection (`scheffeSelect`); the one-sided `scheffeScore` formulation and Hoeffding union-bound proofs in `CslibFrontier/Probability/HypothesisSelection/{LeCamBirge,Tournament}.lean` are this library's formulation.

<a id="dewolf19"></a>
## dewolf19

Ronald de Wolf. *Quantum Computing: Lecture Notes*. arXiv:1907.09415, read in v6. https://arxiv.org/abs/1907.09415 . For the density-matrix modules the following were checked on 2026-11-08: §15.1 (density matrices are the positive semidefinite matrices of trace one; a pure state is `|φ⟩⟨φ|`; unitaries act by `ρ ↦ UρU*`), §18.3 (the partial trace, defined by `Tr_B (C ⊗ D) = C · Tr D` and extended linearly; the reduced state of an EPR pair is `I / 2`), and Chapter 18, Exercises 5 (the random Pauli on one qubit, "a quantum one-time pad") and 7 (Alice cannot signal to Bob by a unitary on her half of an entangled pure state). The Kraus-family form of no-signalling in the library is a standard generalization of Exercise 7, not a statement from the notes.

<a id="diestel25"></a>
## diestel25

Reinhard Diestel. *Graph Theory*, sixth edition. Graduate Texts in Mathematics 173, Springer, 2025. The author's free preview chapters (https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch3.pdf and Ch1.pdf) were consulted on 2026-11-08 and 2026-11-11 UTC for Section 1.4 (`k`-connectedness `|G| > k`, separating sets, Proposition 1.4.2 `κ(G) ≤ λ(G)`), Section 3.3, Theorem 3.3.1 (`A`–`B` Menger), Corollary 3.3.5 (i) (vertex form, `ab ∉ E`) and (ii) (edge form), and Theorem 3.3.6 (i)–(ii) (global `k`-connectivity Menger).

<a id="dilworth1950"></a>
## dilworth1950

Robert P. Dilworth. "A Decomposition Theorem for Partially Ordered Sets." *Annals of Mathematics* 51(1), 161–166, 1950. https://doi.org/10.2307/1969503 . Bibliographic metadata from search summaries, checked on 2026-11-08; the paper is paywalled and was not inspected. The library attributes to it only the finite case of the decomposition theorem, whose formal statement follows [Schrijver's lecture notes](#schrijver17), Theorem 7.6.

<a id="dinic70"></a>
## dinic70

E. A. Dinic. “Algorithm for Solution of a Problem of Maximum Flow in Networks with Power Estimation.” *Soviet Mathematics Doklady* 11, 1277–1280 (1970). This original paper was not consulted. The bibliographic data come from secondary citations, and the manual attributes to it only the level-network and blocking-flow method and its phase bound, as these are standardly described. Yefim Dinitz's historical account, “Dinitz' Algorithm: The Original Version and Even's Version” (in *Theoretical Computer Science: Essays in Memory of Shimon Even*, LNCS 3895, 218–240, Springer, 2006, https://doi.org/10.1007/11685654_10 ; bibliographic data checked against the Crossref record on 2026-11-08), is cited in the module docstrings for the history. Its text was not inspected: the author-hosted PDF's text layer could not be extracted.

<a id="dinur2007"></a>
## dinur2007

Irit Dinur. “The PCP Theorem by Gap Amplification.” *Journal of the ACM* 54(3), Article 12 (2007). DOI: https://doi.org/10.1145/1236457.1236459. Author copy dated 2007-02-13 inspected: https://www.wisdom.weizmann.ac.il/~dinuri/mypapers/combpcp.pdf (opening definition and Theorem 1.1).

<a id="dinur2016"></a>
## dinur2016

Irit Dinur. “Mildly Exponential Reduction from Gap 3SAT to Polynomial-Gap Label-Cover.” *Electronic Colloquium on Computational Complexity*, Report TR16-128, 2016. https://eccc.weizmann.ac.il/report/2016/128/ . Bibliographic metadata checked against the ECCC report record; the report's full text was inspected for Hypothesis 2.5 (p. 5), which has at most $D n$ clauses and fixed soundness $< 0.9$. Used alongside [manurangsiraghavendra2017](#manurangsiraghavendra2017) to document the Gap Exponential Time Hypothesis adaptation (`GapETH`, `rGapETH`) in [FineGrained/GapETH.lean](../CslibFrontier/Computability/Complexity/FineGrained/GapETH.lean).

<a id="dosasgall2013"></a>
## dosasgall2013

György Dósa and Jiří Sgall. "First Fit bin packing: A tight analysis." *30th International Symposium on Theoretical Aspects of Computer Science (STACS 2013)*, LIPIcs 20, 538–549, 2013. https://doi.org/10.4230/LIPIcs.STACS.2013.538 . Worker w156-ff read the open-access LIPIcs PDF on 2026-11-08 UTC and checked these parts: the weight function of Section 1.2 (scaled size `6/5 · a` plus a bonus); the observation there that every bin weighs at most `1.7`; Lemma 1.1, the amortization step; and the Section 1.1 history of the additive constants. [FirstFitWeight](../CslibFrontier/Algorithms/Lean/BinPacking/FirstFitWeight.lean) cites these locators. The constant `+0.9` is credited there to Garey, Graham, Johnson and Yao (ref. [4]), and `+0.7` to Xia and Tan (ref. [15]); both attributions are reported only via this paper. The absolute bound `FF ≤ 1.7 · Opt` (Theorem 3.13) and the lower bounds of Section 4 (Lemma 4.1, Theorem 4.2) were read but are not formalized. The small instances for `Opt ≤ 9` at the end of the proof of Theorem 4.2 (`i` items each of sizes `1/6 - 2δ`, `1/3 + δ` and `1/2 + δ`) are checked for `i = 3` and `i = 9` in [BinPackingFirstFitWeight](../CslibFrontierTests/BinPackingFirstFitWeight.lean).

<a id="dworkroth14"></a>
## dworkroth14

Cynthia Dwork and Aaron Roth. *The Algorithmic Foundations of Differential Privacy*. Foundations and Trends in Theoretical Computer Science 9(3–4), 211–407, 2014. https://doi.org/10.1561/0400000042 . Definition 2.4, Proposition 2.1, Theorem 2.2 and its footnote, §2.3, Claim 3.5, Theorem 3.16, Definition 3.7, Theorem 3.20, Corollary 3.21, Theorem B.1 and Corollary B.2 were checked against the published PDF on 2026-11-07. Theorem 8.2 (pp. 161–162), Lemma 8.3 and the proof of Theorem 8.2 (pp. 162–163), Lemma 8.4 and Corollary 8.5 (p. 165), Theorem 8.7 (p. 166), Theorem 8.8 with its proof and Claim 8.9 (pp. 167–169), and the bibliographic notes of §8.3, which credit Theorem 8.2 to Dwork, McSherry and Talwar (p. 170) and Theorem 8.8 to De (p. 171), were checked on 2026-11-08 against the authors' open version (https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf), whose page numbers these are.

<a id="edmonds65"></a>
## edmonds65

Jack Edmonds. "Maximum Matching and a Polyhedron with 0,1-Vertices." *Journal of Research of the National Bureau of Standards, Section B* 69B(1–2), 125–130, 1965. https://doi.org/10.6028/jres.069B.013 . Cited only as the origin of polynomial-time minimum-weight perfect matching, which the library does not formalize; the bibliographic details come from search summaries and the paper was not checked.

<a id="edmonds67b"></a>
## edmonds67b

Jack Edmonds. "Optimum Branchings." *Journal of Research of the National Bureau of Standards, Section B* 71B(4), 233–240, 1967. https://doi.org/10.6028/jres.071B.032 . Bibliographic metadata checked against the Crossref record on 2026-11-08. Section 2 (the reduction of optimum spanning arborescences with a prescribed root to optimum branchings; arcs are directed away from the root), Theorem 1 (stated in Section 3: a *good*, that is polynomially bounded, algorithm for optimum branchings exists) and Section 4 (the algorithm, which selects the best arc into each node and contracts cycles, and its proof) were checked against the open NIST PDF on 2026-11-08. The library formalizes the Section 1 branching characterization, the Section 2 weight-shift reductions, the Section 4 contraction algorithm (including materialized `O(n³)` `TimeM` table solvers), and the polynomial-time content of Theorem 1 on binary-weighted adjacency tables (`minArborescenceDec_mem_P`, `minOutArborescenceDec_mem_P`, `maxBranchingDec_mem_P`). Theorem 2 (Section 5, the branching polytope) and sparse `O(m log n)` / `O(m + n log n)` implementations are not formalized.

<a id="epsteinfeldmanmansour09"></a>
## epsteinfeldmanmansour09

Amir Epstein, Michal Feldman and Yishay Mansour. *Strong Equilibrium in Cost Sharing Connection Games*. Games and Economic Behavior 67(1), 51–68, 2009. https://doi.org/10.1016/j.geb.2008.07.002 . Bibliographic metadata only, as given in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, reference [4], and checked against the Crossref record of the DOI. The paper's text was not inspected, so no locator in it is cited, and which notion of strong equilibrium it uses was not checked. The `H_k` bound on the cost of strong Nash equilibria of fair cost-sharing games is attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, Theorem 3.2, and proved following that lecture. The lecture states it for its weak-deviation notion (Definition 3.1, `IsStrongNash`), but its proof only uses that no coalition can make every member strictly better off (footnote 2 notes that the stronger inequality is not needed). So the library proves the bound for the all-strict notion `IsStrongEquilibrium` of [babaioffchuangfeldman07](#babaioffchuangfeldman07), Exercise 23.6, which contains every strong Nash equilibrium.

<a id="erdos1947"></a>
## erdos1947

Paul Erdős. “Some Remarks on the Theory of Graphs.” *Bulletin of the American Mathematical Society* 53(4), 292–294, 1947. https://doi.org/10.1090/S0002-9904-1947-08785-1 . Bibliographic metadata checked on 2026-11-07; the full text was not inspected in this pass. The manual attributes only the counting lower bound `2 ^ (k / 2) < R(k, k)` to this paper; the formal statement follows Alon–Spencer, *The Probabilistic Method*, Proposition 1.1.1, as cited in the Lean documentation.

<a id="erdosszekeres1935"></a>
## erdosszekeres1935

Paul Erdős and George Szekeres. “A Combinatorial Problem in Geometry.” *Compositio Mathematica* 2, 463–470, 1935. http://www.numdam.org/item/CM_1935__2__463_0/ . The graph-theoretic Ramsey theorem and its induction, pp. 465–467, give the upper bound `R(k, l) ≤ C(k + l − 2, k − 1)`; the agent review of the introducing PR checked pp. 466–467 against the Numdam PDF. The monotone subsequence theorem (the Theorem on p. 467 for `n` points and its `f(i, k) = (i − 1)(k − 1) + 1` form with the matching construction on p. 468, where equal values may count as increasing or decreasing) was checked against the same PDF on 2026-11-08 for `CslibFrontier.Foundations.Combinatorics.ErdosSzekeres`.

<a id="erickson24"></a>
## erickson24

Jeff Erickson, Ivor van der Hoog, Tillmann Miltzow. “Smoothing the Gap Between NP and ∃R.” *SIAM Journal on Computing* 53(6), FOCS20-102–FOCS20-138, 2024. https://doi.org/10.1137/20M1385287 . Author preprint consulted: https://arxiv.org/abs/1912.02278v3 , §6.1. Published metadata comes from the pinned bibliography; the consulted preprint is dated 2021.

<a id="fabrikantpapadimitrioutalwar04"></a>
## fabrikantpapadimitrioutalwar04

Alex Fabrikant, Christos H. Papadimitriou, and Kunal Talwar. *The Complexity of Pure Nash Equilibria*. Proceedings of the 36th Annual ACM Symposium on Theory of Computing (STOC 2004), 604–612. https://doi.org/10.1145/1007352.1007445 . Bibliographic metadata checked against Crossref on 2026-11-08; the PLS-completeness theorem is attributed as cited in Roughgarden's CS364A Lecture #19, Theorem 3.1. The paper itself was not consulted.

<a id="falcon2020"></a>
## falcon2020

Falcon team. *Falcon: Fast-Fourier Lattice-Based Compact Signatures over NTRU*, NIST Post-Quantum Cryptography Standardization Round 3 submission, version 1.2, 2020. [Official archive](https://csrc.nist.gov/CSRC/media/Projects/post-quantum-cryptography/documents/round-3/submissions/Falcon-Round3.zip). Checked on 2026-11-13 against archive SHA-256 `fd58f0454f6bfb4713734e60b2d2d75d96fbae62d5180fceeef1039df5362f44`; the enclosed specification has SHA-256 `fec58c4c7e2f1712413c1e77994886c6f1f40f1cc7ec5fa650f132927ca07cd6`, and `KAT/falcon512-KAT.rsp` has SHA-256 `dd75c946fdedef4ec46a2bee7e10c65c9126f1a839b9ced6921fd45f7354b5cd`. `CslibFrontier.Crypto.Falcon` maps Algorithm 3, Algorithm 14's 64-bit threshold distribution and lazy byte comparison, Algorithms 16 and 18 and Section 3.11.6 to its current verification and sampler interfaces. Algorithm 14, lines 4–10 on printed p. 43, computes a uint64 threshold `z`; lines 5–10 compare its bytes most-significant first and return one with exact probability `2^-64 * z`. The archive's `Reference_Implementation/falcon512/falcon512int/sign.c::BerExp` assigns the threshold at line 1074 and implements the lazy comparison at lines 1082–1087; `inner.h::prng_get_u8`, lines 565–577, supplies each visited byte and refills its buffer when necessary. The formal fixed-threshold interface proves the exact conditional law. Its lazy companion uses the shared `Byte` and `natToFixedBytesBE` boundary, makes one eight-fair-bit draw per visited byte, records the one-to-eight-byte trace and exact source ledger of one draw, subtraction, loop equality test and eight fair bits per byte with zero external resources, proves the same complete decision distribution, and proves that reading past the first byte has probability `2^-8`. The comparison coordinate excludes the one final sign extraction and loop-index tests. These are source operations, not Lean or native steps. It does not formalize the floating-point approximation that produced `z`, PRNG-buffer refills, `BaseSampler`, `SamplerZ`, the Gaussian or retry law, or native resource use. In `Reference_Implementation/falcon512/falcon512int/shake.c`, `i_shake256_inject`, `i_shake256_flip` and `i_shake256_extract` confirm the 136-byte rate chunks, least-significant-byte lane convention, `0x1F` domain/padding byte and final `0x80` bit; `common.c`'s `hash_to_point_vartime` consumes successive output bytes as big-endian 16-bit words. The SHAKE256 client checks `count = 0`'s exact 40-byte salt followed by its 33-byte message against the first 20 output bytes; these finite fixtures are not a full key/signature KAT verification, a complete Gaussian sampler, a native resource certificate or a claim about the still-developing FIPS 206 standard.

<a id="feige1998"></a>
## feige1998

Uriel Feige. "A Threshold of ln n for Approximating Set Cover." *Journal of the ACM* 45(4), 634–652, 1998. https://doi.org/10.1145/285055.285059 . Bibliographic metadata checked via search records only; primary text uninspected and internal theorem locators unverified (no numbered paper theorems claimed). Cited for the Set Cover hardness threshold framework using separating partition gadgets.

<a id="fgms20"></a>
## fgms20

John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani. "Unique End of Potential Line." *Journal of Computer and System Sciences* 114, 1–35, 2020. https://doi.org/10.1016/j.jcss.2020.05.007 . Checked on 2026-11-11 against the arXiv TeX source of `arXiv:1811.03841v1` (https://arxiv.org/abs/1811.03841 , dated 9 November 2018): Section 2 ("Unique End of Potential Line"), Definition 9 (`EndOfPotentialLine`, `\label{def:EOPL}`, solution types `(R1)` and `(R2)` under `P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0` with `V : {0, 1}^n → {0, …, 2^m - 1}`) and the complexity class `EOPL` with `EOPL ⊆ PLS ∩ PPAD`. `CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/PotentialLine.lean` formalizes uniform polynomial-time `EOPL` and `SOPL` families, totalized `(R1)/(R2)` violation relations (`mem_EOPL_iff_violation`, `mem_SOPL_iff_violation`), and `EOPL ⊆ PLS ∩ PPAD`. `CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/PotentialLineNormalization.lean` formalizes the uniform polynomial-time `(n + 1)`-bit normalization to the exact syntactic source conditions `PromisedPotentialLine` (`P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0`), pure `(R1)/(R2)` relations (`endOfPotentialLinePromisedRel`, `sinkOfPotentialLinePromisedRel`), and unary potential bit-bounds (`mem_EOPL_iff_promised_bounded`, `mem_SOPL_iff_promised_bounded`). Both modules use uniform polynomial-time families rather than canonical Boolean circuit codes; `UEOPL`, `CLS`, and the journal version's numbering were not formalized or separately checked.

<a id="fiatkarplubymcgeochsleatoryoung91"></a>
## fiatkarplubymcgeochsleatoryoung91

Amos Fiat, Richard M. Karp, Michael Luby, Lyle A. McGeoch, Daniel D. Sleator and Neal E. Young. "Competitive Paging Algorithms." *Journal of Algorithms* 12(4), 685–699, 1991. https://doi.org/10.1016/0196-6774(91)90040-6 . Checked on 2026-11-11 against the arXiv TeX source of `arXiv:cs/0205038v1` (https://arxiv.org/abs/cs/0205038 , submitted 24 May 2002): Section 3 ("The marking algorithm") and Theorem 1 (`\label{markingthm1}`, stating that the marking algorithm is a `2 H_k`-competitive algorithm for the uniform `k`-server problem on `n` vertices). `CslibFrontier/DataStructure/Paging/Marking.lean` formalizes the marking algorithm over `Paging.problem α k` via `Online.BehavioralStrategy` with three local adaptations: (1) pages range over any `[DecidableEq α]` type rather than a finite `n`-vertex uniform metric; (2) initialization covers any admissible cache `|s₀| ≤ k` (inserting without eviction while `|cache| < k`) with additive constant `0`, rather than only a full initial cache `{1, …, k}`; and (3) `cleanCount_le_two_mul_scheduleCost` proves `#clean ≤ 2 · OPT` directly against arbitrary (not necessarily lazy) valid offline schedules without invoking the Manasse–McGeoch–Sleator lazy-schedule reduction. The `H_k` randomized lower bound against an oblivious adversary (Theorem 4 and Corollary 5, Section 5), unequal-capacity bounds, and the published journal's pagination were not formalized or separately checked.

<a id="fips1804"></a>
## fips1804

National Institute of Standards and Technology. *Secure Hash Standard*, Federal Information Processing Standards Publication 180-4, 2015. https://doi.org/10.6028/NIST.FIPS.180-4 . Checked on 2026-11-14 against the official August 2015 PDF (SHA-256 `5b88d70308c95106e713221c7085cbb8e89dc2eb6214d75c885af2f07ffc6b8a`): Sections 4.1.2 and 4.1.3 define the SHA-256 and SHA-512 logical functions, Sections 4.2.2 and 4.2.3 give the round constants, Sections 5.1.1 and 5.1.2 give padding and length encoding, Sections 5.2 and 5.3 give parsing and initial states, and Sections 6.2 and 6.4 give the hash computations. `CslibFrontier.Crypto.Primitives.ByteString` supplies typed byte strings and big-endian conversion, and `CslibFrontier.Crypto.Primitives.Hash.SHA2` supplies byte-aligned SHA-256 and SHA-512 with the source input-length domains. The official [SHA-256 example PDF](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf) (SHA-256 `7006b6549dad2fc8c6f29417a921f2e48208157ef496a7e1e1d7d17c5cc1e7db`) supplies `abc` at input p. 1 and digest p. 3, and the two-block example at input p. 3 and digest p. 6. The official [SHA-512 example PDF](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf) (SHA-256 `84ce867c99bad5a7b05abc74bb1dfc9de8486f49a160653cc8b15272cc532115`) supplies `abc` at input p. 1 and digest p. 4, and the two-block example at input p. 4 and digest p. 11. These executable specifications are not constant-time or machine-costed implementations, security proofs, or NIST validations.

<a id="fips202"></a>
## fips202

National Institute of Standards and Technology. *SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*, Federal Information Processing Standards Publication 202, 2015. https://doi.org/10.6028/NIST.FIPS.202 . Checked on 2026-11-13 against the published August 2015 PDF (SHA-256 `1592607831ff0908cc590632ce371c6c95e94025bb1a0c8ae90a4d0ec1ed025e`): Sections 3.1.2--3.1.3 give the bit-string/state correspondence, Sections 3.2--3.3 and Algorithms 1--7 give the five round maps and round function, Section 4 and Algorithm 8 give the permutation-backed sponge construction, Section 5.1 and Algorithm 9 give `pad10*1`, Section 6.1 defines SHA3-512 as `KECCAK[1024](M || 01, 512)`, and Section 6.2 defines SHAKE128 as `KECCAK[256](M || 1111, d)` and SHAKE256 as `KECCAK[512](M || 1111, d)`. The official NIST [SHA3-512 0-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA3-512_Msg0.pdf) and [SHA3-512 1600-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA3-512_1600.pdf) examples were checked on 2026-11-16 with SHA-256 hashes `6d0a6fecea7babaffe9f3b09058fdb1590576e52b9dbfe0a637705db6f7de248` and `2f5f6ca71c3bd7bf3e99d142f7c4035b1e3fea95d7fc7e7a79a38ce995388211`. The official NIST [SHAKE128 0-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE128_Msg0.pdf), [SHAKE128 1600-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE128_Msg1600.pdf), [SHAKE256 0-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE256_Msg0.pdf) and [SHAKE256 1600-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE256_Msg1600.pdf) examples were checked with SHA-256 hashes `3013d904e0f6cebc8dad6393cbf3eed4d1a537b3b3dc5e7b48552ff597942974`, `437f905d9790ce7a18625b396ba57c6118bb46d1542ec3cf1d46faac23c261ef`, `d736c1a93eb6440e1e6b640402e31ea5258281b2b9237f84ea0ba4186518fc59` and `f4226f5c72914e5d2b331812c5973d8d685c8af1ccb97c2a3a2fd1c02fd173d1`. `CslibFrontier.Crypto.Primitives.Hash.Keccak`, `.Keccak.Circuit`, `.Keccak.Efficient`, and `.Keccak.SHAKE128` implement the byte-aligned executable functions and their stated exact-permutation or asymptotic machine certificates; they do not claim cryptographic security, constant-time execution, a concrete whole-sponge cost, FIPS validation or a future FIPS 206 definition.

<a id="fips203"></a>
## fips203

National Institute of Standards and Technology. *Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Federal Information Processing Standards Publication 203, 2024. https://doi.org/10.6028/NIST.FIPS.203 . Checked on 2026-11-14 against the official published PDF (1,252,341 bytes; SHA-256 `fe1f12f32a7e44ec9fdebbf400cda843a40b506dee676725234dc6f7923b6cac`). Section 4.1, Equations (4.3) and (4.6) define the SHAKE256 noise PRF and the one-shot/incremental SHAKE128 correspondence; Section 4.2.1, Algorithms 3–6 define least-significant-bit-first byte packing and `ByteEncode_d`/`ByteDecode_d`; Section 4.2.2, Algorithms 7–8 define SampleNTT's three-byte rejection parser and `SamplePolyCBD`; Section 5, Algorithms 13–15 define K-PKE, including `rho || j || i`; Section 6, Algorithms 16–18 defines the internal ML-KEM algorithms; Section 7, Algorithms 19–21 defines the ML-KEM interface, and Section 7.2, Equation (7.1) gives the public-key decode/re-encode check; Section 8, Table 2 gives the parameter sets. The publication page currently links an errata/potential-updates workbook; these locators and claims map the published PDF. The coefficient-level K-PKE modules record their model differences (uniform matrix, sampled coins, coefficient form), while the encoding/seed-expansion modules cover only the source-ready byte and finite-prefix boundaries described in their documentation.

<a id="fips205"></a>
## fips205

National Institute of Standards and Technology. *Stateless Hash-Based Digital Signature Standard*, Federal Information Processing Standards Publication 205, 2024. https://doi.org/10.6028/NIST.FIPS.205 . Checked on 2026-11-13 against the official PDF (SHA-256 `8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d`): Section 4.2 and Figures 2–9 define the canonical 32-byte address and its seven type-specific layouts; Section 4.3 and Table 1 define the address setters, including clearing the final 12 bytes on every type change; Section 4.4 defines the unsigned big-endian integer encoding and Algorithm 4 defines `base_2b`; Section 5, Equations (5.1)–(5.4) fixes `lg_w = 4`, `w = 16`, `len1 = 2n`, `len2 = 3` and `len = 2n + 3` for `n = 16, 24, 32`; Algorithms 7 and 8, lines 1–7 define the shared message conversion and complement checksum, including the four-bit left shift and two-byte big-endian encoding; and Section 11.2, Figure 18 and Table 3 define the 22-byte compressed address used by the SHA2 parameter sets. `CslibFrontier.Crypto.Primitives.SLHDSA.Address` formalizes the address-domain layer with typed 32-byte and 22-byte encodings, and `CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.Digits` formalizes exactly the digit-preprocessing layer. They do not formalize the concrete hash instantiations, the Algorithm 5 chain, complete WOTS+, XMSS, FORS, the hypertree, signing, verification or security analysis.

<a id="fks84"></a>
## fks84

Michael L. Fredman, János Komlós, Endre Szemerédi. "Storing a Sparse Table with O(1) Worst Case Access Time." *Journal of the ACM* 31(3), 538–544, 1984. https://doi.org/10.1145/828.1884 . Bibliographic metadata was checked against the DOI record on 2026-11-08. The full text was not inspected. The formalization follows the textbook account in [clrs09](#clrs09), Section 11.5 ("Perfect hashing"), and that locator was checked against the edition's published table of contents only. No theorem numbers are attributed to either source.

<a id="floyd62"></a>
## floyd62

Robert W. Floyd. "Algorithm 97: Shortest Path." *Communications of the ACM* 5(6), 345, 1962. https://doi.org/10.1145/367766.368168 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the Floyd–Warshall recurrence to this note.

<a id="flumgrohe2006"></a>
## flumgrohe2006

Jörg Flum and Martin Grohe. *Parameterized Complexity Theory*. Springer, 2006. [DOI](https://doi.org/10.1007/3-540-29953-X). The [publisher's Chapter 3 preview](https://page-one.springer.com/pdf/preview/10.1007/3-540-29953-X_3) was inspected: Definition 3.1 on printed p. 45 defines `W[P]` by restricted nondeterministic multitape machines with computable time and nondeterminism bounds, and Proposition 3.2 on printed p. 46 states `FPT ⊆ W[P] ⊆ XP ∩ paraNP`. The preview does not give a weighted-circuit characterization. It is used in [parameterized complexity](machines-and-classes/parameterized-complexity.md) to contrast conventions; equivalence with the library's potentially ineffective reduction closure `WP` is not established.

<a id="fly22"></a>
## fly22

Zhiyuan Fan, Jiatu Li, and Tianqi Yang. *The Exact Complexity of Pseudorandom Functions and the Black-Box Natural Proof Barrier for Bootstrapping Results in Computational Complexity*. Electronic Colloquium on Computational Complexity (ECCC), Report TR21-125, Revision 1 (12 June 2022), https://eccc.weizmann.ac.il/report/2021/125/ ; conference version in *Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 962–975, https://doi.org/10.1145/3519935.3520010 . Inspected ECCC TR21-125 Revision 1 PDF directly: Section 4.1 (pp. 24–26), Section 4.2, Definitions 4.3–4.5 (pp. 26–27), Section 4.4, Definition 4.9 (p. 28), Section 7.1, Definition 7.1, Lemmas 7.2–7.4, and Theorem 7.5 (pp. 39–41), and Section 7.2 (pp. 41–42).

<a id="fmptw15"></a>
## fmptw15

Samuel Fiorini, Serge Massar, Sebastian Pokutta, Hans Raj Tiwary and Ronald de Wolf. *Exponential Lower Bounds for Polytopes in Combinatorial Optimization*. Journal of the ACM 62(2), 1–23, 2015. https://doi.org/10.1145/2716307 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC. Locators checked against arXiv:1111.0837v4 (23 Dec 2013), https://arxiv.org/abs/1111.0837 , on 2026-11-08 UTC: definition (1) of an extended formulation (EF) and its size (Section 1), the slack matrix and extension complexity (Section 3), Lemma 2, Theorem 3 (the factorization theorem, `dim P ≥ 1`) and Theorem 4 (the rectangle covering bound, attributed to [yannakakis91](#yannakakis91)) in Section 3.1. Checked against the same arXiv v4 text on 2026-11-11 UTC: Section 3.2 (Theorems 5 and 7, Lemma 6 on `COR(n)` and `CUT(n + 1)`), Section 3.3 (Lemmas 8 and 9, Theorem 10 on `STAB(G_n)`), and Section 3.4 (Lemma 11, Theorem 12 on `TSP(n)`). The journal version's numbering was not checked.

<a id="fmr20"></a>
## fmr20

Benjamin Fuller, Xianrui Meng and Leonid Reyzin. "Computational Fuzzy Extractors." *Information and Computation* 275, article 104602, 2020. https://doi.org/10.1016/j.ic.2020.104602 ; full version IACR Cryptology ePrint Archive Report 2013/416 (revision of June 23, 2020), https://eprint.iacr.org/2013/416 ; conference version ASIACRYPT 2013, LNCS 8269, 174-193. Locators in the library follow the ePrint revision: Definitions 2.1-2.4 and Lemma 2.5 (Section 2), Construction 4.1, Definition 4.5, Lemma 4.7 and Theorem 4.11 (Section 4). Checked on 2026-11-14 against that revision (31 pages, SHA-256 `7ebe9884a2963304ae98329742652916a281d3eb1eb860fc411392bbb99d310d`; printed page numbers, which are also its PDF page numbers): Construction 4.1 (p. 11, prime `q`, the source reading as the LWE error); Definition 4.5 (p. 13, `dist-LWE_{n,m,q,χ}` with `χ` an arbitrary distribution on `Z_q^m`, prime `q = poly(n)`, concrete `(ε, s_sec)` security); Theorem 4.6 (p. 13, from Döttling and Müller-Quade) and Theorem 4.8 (p. 14, from Bai et al.), which derive it for uniform-interval errors from Gaussian LWE; Lemma 4.7 (p. 14, dimension `n - k`, any `χ`); Theorem 4.11 (p. 17, with `χ` the uniform source over `[-2^(b-1), 2^(b-1)]^m`); and Theorem 5.2 (p. 18, symbol-fixing sources). Checked on 2026-11-15 against the same revision: Definition 2.2 (p. 6, computational fuzzy extractor, whose item 4 is security against the distinguishers `D_{s_sec}` of p. 5). The page numbers of the Information and Computation version were not checked.

<a id="fnw78"></a>
## fnw78

Marshall L. Fisher, George L. Nemhauser, Laurence A. Wolsey. “An Analysis of Approximations for Maximizing Submodular Set Functions—II.” *Mathematical Programming Study* 8, 73–87, 1978. https://doi.org/10.1007/BFb0121195 . Bibliographic data from the DOI record; the paper is paywalled and its full text was not inspected. The manual attributes to it only the greedy `1/2` (matroid) and `1/(p+1)` (intersection of `p` matroids) bounds, following [Călinescu et al.](#ccpv11), Section 1 and Appendix B.

<a id="fominkratsch10"></a>
## fominkratsch10

Fedor V. Fomin and Dieter Kratsch. *Exact Exponential Algorithms*. Texts in Theoretical Computer Science, An EATCS Series. Springer, 2010. https://doi.org/10.1007/978-3-642-16533-7 . Bibliographic metadata checked on 2026-11-07. Inspected the author-hosted manuscript dated October 12, 2010 (https://fedorvf.github.io/BookEA/BookEA.pdf): Section 4.1, Theorem 4.2 for the general inclusion–exclusion principle, and Section 4.2.2, Theorem 4.5 and Eq. (4.4), printed pp. 56–57 (PDF pp. 68–69), for the inclusion–exclusion Hamiltonian path algorithm (where the book fixes start and end vertices `s, t` and counts `(s, t)`-walks on `n + 2` vertices, adapted in [`HamiltonianCount.lean`](../CslibFrontier/Algorithms/Lean/TSP/HamiltonianCount.lean) to count all endpoint choices on `n` vertices and charged in `TimeM` integer-addition ticks rather than the book's unit-cost versus log-cost discussion). The Section 1.2 locator for the Held–Karp TSP dynamic program was taken from secondary descriptions and issue #3013 without inspecting that section. It is also cited at book level for search-tree branching vectors and disjoint clause-prefix branching on fixed-width SAT; no internal chapter, theorem, or page locators are claimed.

<a id="forbesshpilka2013"></a>
## forbesshpilka2013

Michael A. Forbes and Amir Shpilka. "Quasipolynomial-time Identity Testing of Non-commutative and Read-once Oblivious Algebraic Branching Programs." FOCS 2013, 243–252; arXiv:1209.2408v2, https://arxiv.org/abs/1209.2408v2 . Read in the arXiv version: §1.1 (pp. 2–3) for the set-multilinear and univariate encodings, and §4 for the reduction from non-commutative programs: Construction 4.1 and Lemma 4.2 (p. 22), Lemma 4.3 (p. 23), Lemma 4.5 and Theorem 4.6 (p. 24). The library formalizes this reduction for homogeneous layered programs only and feeds it the hitting set of its own adaptation of Agrawal–Gurjar–Korwar–Saxena; Corollary 4.7 (p. 25), with the paper's generator and bound, is not formalized.

<a id="fortnowsanthanam2011"></a>
## fortnowsanthanam2011

Lance Fortnow and Rahul Santhanam. "Infeasibility of Instance Compression and Succinct PCPs for NP." *Journal of Computer and System Sciences* 77(1), 91–106, 2011. https://doi.org/10.1016/j.jcss.2010.06.007 . Bibliographic data from the DOI record. The paper was not inspected in this pass; the manual cites the statement of its distillation theorem through [Bodlaender, Jansen and Kratsch](#bodlaenderjansenkratsch2014), Theorem 2.

<a id="franklwilson1981"></a>
## franklwilson1981

Peter Frankl and Richard M. Wilson. “Intersection Theorems with Geometric Consequences.” *Combinatorica* 1(4), 357–368, 1981. https://doi.org/10.1007/BF02579457 . Bibliographic metadata as already recorded in the library bibliography; it was not re-checked against the publisher record, and the full text was not inspected in this pass. The manual attributes to this paper the modular intersection theorem and the explicit Ramsey graph on the `(p² - 1)`-subsets of a `p³`-set. The formal modular statement is the restricted form given by the triangular polynomial argument (`|L| ≤ d mod p`); the paper's own hypotheses (reportedly `|L| ≤ d` in the uniform case) were not checked.

<a id="freivalds79"></a>
## freivalds79

Rūsiņš Freivalds. "Fast Probabilistic Algorithms." *Mathematical Foundations of Computer Science 1979*, Lecture Notes in Computer Science 74, 57–69. https://doi.org/10.1007/3-540-09526-8_5 . Bibliographic data from the DOI record, checked 2026-11-07; the full text was not inspected. The manual attributes only the random-vector matrix-product check to this paper.

<a id="friezekaronski2016"></a>
## friezekaronski2016

Alan Frieze and Michał Karoński. *Introduction to Random Graphs*. Cambridge University Press, 2016. https://doi.org/10.1017/CBO9781316339831 . Inspected the author-hosted version dated August 7, 2026 (https://www.math.cmu.edu/~af1p/BOOK.pdf), §4.1, Theorem 4.1 and its proof; §1.2, Lemma 1.11 (sharp threshold for isolated vertices, stated and proved in `G(n, m)` with `m = n (log n + ω) / 2` by the first and second moment methods); and §3.1, `E X_0 = n (1 - p) ^ (n - 1)` in `G(n, p)` with its limits (3.1). The theorem is stated for `G_m` with `m = n (log n + c_n) / 2`; the proof works in `G(n, p)` with `p = (log n + c) / n`, and the text later cites it for "`G(n, p)` is connected w.h.p. for `np − log n → ∞`". The book attributes the theorem to Erdős and Rényi, "On random graphs I", *Publ. Math. Debrecen* 6 (1959), 290–297; that paper was not inspected. Also inspected Lemma 33.10 (pp. 696–697, truncated inclusion-exclusion/Bonferroni bounds) and Theorem 33.11 (pp. 697–698, Brun's sieve). The source's `B_r` (written `B_k = E[choose(S_n, k)]`) is formalized as the sum of `r`-fold intersection measures with limit `lam^r / r!` (binomial-moment normalization). The formalization deliberately extends the result to finite measures by using the `r = 0` hypothesis to require that the total mass converges to 1. The publisher's ISBN and DOI are from catalogue records.

<a id="fulkerson1956"></a>
## fulkerson1956

D. R. Fulkerson. "Note on Dilworth's Decomposition Theorem for Partially Ordered Sets." *Proceedings of the American Mathematical Society* 7(4), 701–702, 1956. https://doi.org/10.1090/S0002-9939-1956-0078334-6 . Bibliographic metadata from search summaries, checked on 2026-11-08. The publisher PDF returned HTTP 403 and was not inspected. The Dilworth module credits this note with the reduction of Dilworth's theorem to König's theorem through the bipartite graph of the strict order, following the customary attribution; the paper's own formulation is unverified.

<a id="gentry09"></a>
## gentry09

Craig Gentry. “Fully Homomorphic Encryption Using Ideal Lattices.” *STOC 2009*, 169–178. https://doi.org/10.1145/1536414.1536440 . Bibliographic data and theorem locator taken from the pinned repository; full text not independently re-audited here.

<a id="gglrs00"></a>
## gglrs00

Oded Goldreich, Shafi Goldwasser, Eric Lehman, Dana Ron and Alex Samorodnitsky. *Testing Monotonicity*. Combinatorica 20(3), 301–337, 2000. https://doi.org/10.1007/s004930070011 . Bibliographic metadata checked against the Crossref record on 2026-11-08. The journal version is paywalled, and the author-hosted pages could not be reached (connection reset), so the text was not inspected and no theorem locator is claimed. The manual attributes the edge tester for Boolean functions on the hypercube to this paper, as [roughgarden15cc](#roughgarden15cc) does.

<a id="ggm86"></a>
## ggm86

Oded Goldreich, Shafi Goldwasser, Silvio Micali. “How to Construct Random Functions.” *Journal of the ACM* 33(4), 792–807, 1986. Author-hosted version of record: https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf . Adaptive function-test definition consulted.

<a id="gibbard73"></a>
## gibbard73

Allan Gibbard. "Manipulation of Voting Schemes: A General Result." *Econometrica* 41(4), 587–601, 1973. https://doi.org/10.2307/1914083 . Bibliographic data from secondary search summaries on 2026-11-08 UTC; the paper was not inspected. [Nisan, *Introduction to Mechanism Design*](#nisan07), p. 239, credits the theorem to Gibbard (1973) and Satterthwaite (1975); Nisan's own statement (Theorem 9.8) is the form for rules onto at least three alternatives. The range form (at least three possible outcomes), formalized as the main theorem, is the standard statement in secondary accounts and was not checked against the original; no theorem number is claimed.

<a id="gilbertpollak68"></a>
## gilbertpollak68

E. N. Gilbert and H. O. Pollak. *Steiner Minimal Trees*. SIAM Journal on Applied Mathematics 16(1), 1–29, 1968. https://doi.org/10.1137/0116001 . Cited only because the Chapter 12 Notes of [Williamson and Shmoys](#williamsonshmoys11) attribute the MST factor-2 heuristic for Steiner tree to Moore, as described in this paper. The paper itself was not checked.

<a id="gkr15"></a>
## gkr15

Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum. *Delegating Computation: Interactive Proofs for Muggles*. JACM 62(4), article 27, 2015. https://doi.org/10.1145/2699436 .

<a id="gkst06"></a>
## gkst06

Oded Goldreich, Howard Karloff, Leonard J. Schulman and Luca Trevisan. "Lower Bounds for Linear Locally Decodable Codes and Private Information Retrieval." *Computational Complexity* 15(3), 263–296, 2006. https://doi.org/10.1007/s00037-006-0216-3 ; full preliminary version: Electronic Colloquium on Computational Complexity (ECCC), Report TR01-080, 2001, https://eccc.weizmann.ac.il/report/2001/080/ . Checked on 2026-11-12 against the ECCC TR01-080 report PDF (Section 1.2 Definition 1.7 on p. 4, Section 2.1 Definition 2.1 on p. 6, Section 5.1 Lemma 5.1 on pp. 14–15, and Section 7.1 Lemma 7.1 on pp. 19–20); journal volume, issue, pages and DOI verified against bibliographic metadata.

<a id="gkwy20"></a>
## gkwy20

Chun Guo, Jonathan Katz, Xiao Wang and Yu Yu. "Efficient and Secure Multiparty Computation from Fixed-Key Block Ciphers." *2020 IEEE Symposium on Security and Privacy (SP 2020)*, 825–841, 2020. https://doi.org/10.1109/SP40000.2020.00016 ; full version: Cryptology ePrint Archive, Report 2019/074, https://eprint.iacr.org/2019/074 . Checked on 2026-11-15 against the ePrint PDF dated January 21, 2019 (30 pages, SHA-256 `dc4ff4859fa884d529c176c13a583433c21d95036e7a563067596d5f05e96292`); locators use its printed page numbers, which are also its PDF page numbers; this is the author's check, which no reviewer has yet repeated at the source, so the library cites these locators as not verified. §3, p. 7: the definitions are concrete, asymptotic versions follow "by suitable modifications", and the key law may be non-uniform, as in half gates, where the least significant bit of `R` is `1`. Pp. 7–8: Definitions 1 and 2, correlation robustness and circular correlation robustness. P. 8: the remark that the definitions let tweaks repeat and that weaker notions, such as non-repeating tweaks, may suffice; Definition 3, tweakable (circular) correlation robustness, with `O(x, i, b) = H(x ⊕ R, i) ⊕ b·R`, distinguishers that never ask both `(x, i, 0)` and `(x, i, 1)`, and `(t, q, ρ, ε)` bounds for every key law of min-entropy at least `ρ`; and the relations between the definitions.

<a id="gm94"></a>
## gm94

Torbjörn Granlund, Peter L. Montgomery. "Division by Invariant Integers using Multiplication." *Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI 1994)*, 61–72, 1994. https://doi.org/10.1145/178243.178249 . Checked on 2026-11-10 against the copy at https://gmplib.org/~tege/divcnst-pldi94.pdf : Section 4, Theorem 4.2 (multiply-and-shift division by an invariant integer, base 2, word size `N`, with a non-strict bound on the multiplier). The formalized identity is a radix-`p` variant with a strict bound, in the form of [ll24](#ll24) Lemma 5; the bound `m ≤ p ^ (k + 1)` on the chosen multiplier is proved in the Lean source.

<a id="goemanswilliamson95"></a>
## goemanswilliamson95

Michel X. Goemans and David P. Williamson. "Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming." *Journal of the ACM* 42(6), 1115–1145, 1995. https://doi.org/10.1145/227683.227684 . Section 2 (the relaxation (P) and random-hyperplane rounding) and Section 3 (Theorem 3.1, Lemma 3.2, Theorem 3.3, Lemma 3.4, and Lemma 3.5 with its tangent-line proof at `θ = 2.331122`) were checked against the author-hosted copy at https://math.mit.edu/~goemans/PAPERS/maxcut-jacm.pdf on 2026-11-08. Section 7.2.1 (relaxations `(Q')`, `(P')`, and Theorem 7.2.1.1 for MAX 2-SAT) and Section 7.3 (relaxations `(Q'')`, `(P'')`, Lemmas 7.3.1–7.3.2, the `β > 0.79607` MAX DICUT bound, the balanced-digraph `α` bound on p. 1138, and the sign typo in display `(Q'')`) were checked against the same copy on 2026-11-11.

<a id="goldbergtarjan88"></a>
## goldbergtarjan88

Andrew V. Goldberg and Robert E. Tarjan. "A New Approach to the Maximum-Flow Problem." *Journal of the ACM* 35(4), 921–940, 1988. https://doi.org/10.1145/48014.61051 . The bibliographic data come from search summaries of the publisher record (2026-11-08). The paper was not inspected, so no theorem number is cited. The manual credits it with the preflow push–relabel method and its `O(|V|² |E|)` generic bound, as these are standardly described. The formalization follows [clrs09](#clrs09), Section 26.4.

<a id="goldreich-tree24"></a>
## goldreich-tree24

Oded Goldreich. *On the Cook–Mertz Tree Evaluation procedure*. ECCC TR24-109, revision 2 (27 December 2024). https://eccc.weizmann.ac.il/report/2024/109/ .

<a id="goldreich04"></a>
## goldreich04

Oded Goldreich. *Foundations of Cryptography, Volume 2: Basic Applications*. Cambridge University Press, 2004. https://doi.org/10.1017/CBO9780511721656 . Author's chapter listing and draft availability: https://www.wisdom.weizmann.ac.il/~oded/foc-vol2.html . Author page checked; the full published chapter was not independently audited here.

<a id="goldreich98frag"></a>
## goldreich98frag

Oded Goldreich. *Foundations of Cryptography (Fragments of a Book – Version 2.03)*. Working draft dated February 27, 1998 (bibliography key `Goldreich1998Fragments`). The author's page https://www.wisdom.weizmann.ac.il/~oded/foc-drafts.html posts it as early drafts of Chapters 1–4 of *Foundations of Cryptography, Volume 1* (Cambridge University Press, 2001), in the files https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part1N.pdf (title page, preface and Chapter 1; SHA-256 `8bb9b1749e92a76af10ded00ef440de04bfcd5de128e68022205c8e84037b3d7`), `part2N.pdf` (Chapter 2; `e0c0a64cc14321effaccbcb26e845254f08d8dc14b2358529687430a869aa45d`), `part3N.pdf` (Chapter 3; `773f69ff14873f66bbe241179dcf5c90c2389c81cd8a3b1b8f8f6aad365e46c3`) and `part4N.pdf` (Chapter 4; `97e67c3cae68701705839386a31f462803c6c9e6d1984638442010df99b6f977`). Printed page numbers run continuously across the four files. Read on 2026-11-15: Definitions 2.2.1 (strong one-way functions, p. 29), 2.2.6 (non-uniformly one-way functions, with the remark that follows it, p. 36) and 2.5.1 (hard-core predicates, p. 54); Definitions 3.2.2 (polynomial-time indistinguishability, p. 78) and 3.3.2 (pseudorandom generators, p. 85), the description of one-way permutations as length-preserving one-to-one one-way functions in Section 3.4.1 (p. 91), and the definition of indistinguishability by polynomial-size circuits in Exercise 8 of Chapter 3 (p. 121); Definition 4.2.6 (generalized interactive proofs with a soundness bound, p. 136), the remark that probabilistic polynomial time means a strict bound on the running time (p. 145), and Definition 4.3.8 (auxiliary-input zero knowledge, with the discussion of its clocks that follows it, pp. 151–152). The published volume was not inspected, so its numbering is not claimed to match the draft's.

<a id="gomoryhu61"></a>
## gomoryhu61

Ralph E. Gomory and T. C. Hu. “Multi-Terminal Network Flows.” *Journal of the Society for Industrial and Applied Mathematics* 9(4), 551–570, 1961. https://doi.org/10.1137/0109047 . Bibliographic metadata checked through the publisher record; the article body was not inspected in this pass. The manual cites it for cut-equivalent (Gomory–Hu) trees and the triangle inequality for minimum cut values, as described in [Schrijver 2003](#schrijver03), Section 15.4. The review of PR #4586 reports the triangle inequality on pp. 551–552, the observation that there are at most `n - 1` distinct minimum cut values on p. 553 and the tree-path lemma (Lemma 2) on p. 556; these locators were not rechecked here.

<a id="goosetal22"></a>
## goosetal22

Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao. "Further Collapses in TFNP." *37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 33:1–33:15, 2022. https://doi.org/10.4230/LIPIcs.CCC.2022.33 . Checked on 2026-11-10 against the arXiv TeX source of `arXiv:2202.07761v2` (https://arxiv.org/abs/2202.07761 , dated 20 May 2022): Section 1, Theorem 1 (`EOPL = PLS ∩ PPAD`) and Theorem 2 (`SOPL = PLS ∩ PPADS`); Section 2, Lemma 1 (`inj-PHP` and `bij-PHP` as `PPADS`- and `PPAD`-complete formulations); Section 3, Lemma 2 (the path-pigeonhole reduction `inj-PHP ≤ Path-inj-PHP_f`); Section 4, Lemma 3 (`SoD ∧ inj-PHP ≤ SoPL`); and Section 5, Lemma 4 (`SoPL ∧ bij-PHP ≤ EoPL`). `CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/PotentialLineCollapse.lean` implements Lemma 4 directly from `SOPL` and `PPAD` (`SOPL_inter_PPAD_subset_EOPL`, `EOPL_eq_SOPL_inter_PPAD`). `CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/SOPLCollapse.lean` implements Lemmas 1–3 directly on `PLS` and `PPADS` families over width `n₁(a) + 2(n₁(a) + n₂(a))` (`plsPpads_sink`, `mem_SOPL_of_localOpt_sinkOfLine`, `PLS_inter_PPADS_subset_SOPL`) and deduces Theorem 2 (`SOPL_eq_PLS_inter_PPADS`) and Theorem 1 (`EOPL_eq_PLS_inter_PPAD`). `UEOPL` and the query-model results of the paper are not formalized.

<a id="grenet11"></a>
## grenet11

Bruno Grenet. *An upper bound for the permanent versus determinant problem*. Manuscript, 2011 (the PDF is dated May 25, 2012). https://www-verimag.imag.fr/~grenetb/publis/Gre11.pdf . Checked against the author's PDF on 2026-11-08. Its unnumbered Lemma (an algebraic branching program of size `2ⁿ` on the subsets of `{1, …, n}` computes the permanent) is the private path-sum development in `CslibFrontier/Foundations/LinearAlgebra/Matrix/GrenetPermanent.lean`. Its unnumbered Theorem (a `(2ⁿ - 1) × (2ⁿ - 1)` matrix with entries in `{x_ij} ∪ {-1, 0, 1}` has the permanent as determinant) is `Matrix.permanent_eq_det_grenetMatrix` together with `Matrix.grenetMatrix_apply_eq`. `Cslib.Circuits.Arithmetic.isProjection_permanent_det_two_pow_sub_one` is the strict projection form, Grenet's `dc_s(n) ≤ 2ⁿ - 1`. Grenet works over fields of characteristic other than two; the library proves the identity over every commutative ring. The library uses Grenet's construction with a different sign normalization: `-1` on the diagonal at every vertex other than the merged source and sink, rather than loops of weight `1` with weight `-1` on the first layer for even `n`. It proves the determinant identity through the adjugate rather than through cycle covers.

<a id="grigoriev01"></a>
## grigoriev01

Dima Grigoriev. *Linear lower bound on degrees of Positivstellensatz calculus proofs for the parity*. Theoretical Computer Science 259(1–2), 613–622, 2001. https://doi.org/10.1016/S0304-3975(00)00157-2 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC. The article is behind a publisher paywall, so its text was not consulted, and no theorem or page locator in it is claimed. The library attributes the linear degree lower bound for Tseitin parity systems on expanders to this paper. The precise statement used is that of [barak-steurer16](#barak-steurer16), lecture "Higher-degree integrality gaps", Lemma 24.

<a id="grigorievhirschpasechnik02"></a>
## grigorievhirschpasechnik02

Dima Grigoriev, Edward A. Hirsch and Dmitrii V. Pasechnik. *Complexity of Semialgebraic Proofs*. Moscow Mathematical Journal 2(4), 647–679, 2002; extended abstracts in STACS 2002 and ICALP 2002. https://doi.org/10.17323/1609-4514-2002-2-4-647-679 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC. On the same date worker w96-sos consulted the author-hosted copy https://edwardahirsch.github.io/edwardahirsch/papers/02mmj.pdf for Section 2.3 (the translation of a CNF into the inequalities (2.4)–(2.6)), Section 2.5 (static `LS₊`) and Example 2.1 (p. 10 of that copy: the degree-`2` static `LS₊` refutation of `PHP^m_{m-1}`). The ECCC version (TR01-103) could not be retrieved, and the typeset journal pagination of Example 2.1 was not checked.

<a id="grs12"></a>
## grs12

Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan. *Universally Utility-Maximizing Privacy Mechanisms*. SIAM Journal on Computing 41(6), 1673–1693, 2012; conference version STOC 2009. https://doi.org/10.1137/09076828X . §2.1 and Example 2.1 were checked against arXiv:0811.2841v3 on 2026-11-07.

<a id="gsw13"></a>
## gsw13

Craig Gentry, Amit Sahai, Brent Waters. “Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based.” *CRYPTO 2013*, LNCS 8042, 75–92. https://doi.org/10.1007/978-3-642-40041-4_5 ; authors' full-version record https://eprint.iacr.org/2013/340 . Metadata/abstract checked; PDF fetch was blocked in this source pass.

<a id="gupta23"></a>
## gupta23

Anupam Gupta. “Dimension Reduction and the JL Lemma.” Chapter 11 of the lecture notes for CMU 15-850 *Advanced Algorithms*; PDF dated 2023-02-17. https://www.cs.cmu.edu/~15850/notes/lec12.pdf . Checked on 2026-11-07 UTC: §11.6.2, Lemma 11.9 bounds `𝔼 exp (tV²)` for a symmetric σ-sub-Gaussian `V` by the corresponding Gaussian moment generating function. The proof linearizes the square with an independent Gaussian, exchanges the averages and applies the sub-Gaussian bound. The notes apply the lemma to Rademacher projection matrices.

<a id="guruswamirudrasudan25"></a>
## guruswamirudrasudan25

Venkatesan Guruswami, Atri Rudra and Madhu Sudan. *Essential Coding Theory*. Draft book, version of 26 August 2025. https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/ ; open PDF https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf . The library's key is `GuruswamiRudraSudan2019`. Read in the open PDF on 2026-11-08 for Chapter 6:

- §6.2 (the binary symmetric channel) and §6.2.2 (capacity: reliable communication is possible below it and impossible above it);
- Theorem 6.3.1 (p. 119): part (1), achievability with error `2^(−δn)`, and part (2), for `0 ≤ p < 1/2` and `k ≥ ⌈(1 − H(p) + ε) n⌉` with `0 ≤ ε ≤ 1/2 − p`, some message misdecoded with probability more than `1/2`;
- §6.3.1, the packing proof of part (2) (pp. 120–122), and Remark 6.3.2, the error bound `1 − 2^(−βn)`;
- §6.3.2 and Claim 6.3.3, the random-coding proof of part (1).

The draft does not name Wolfowitz. The manual's attribution of the strong converse for discrete memoryless channels to him is standard background and was not checked against his paper.

<a id="gusfield90"></a>
## gusfield90

Dan Gusfield. “Very Simple Methods for All Pairs Network Flow Analysis.” *SIAM Journal on Computing* 19(1), 143–155, 1990. https://doi.org/10.1137/0219009 . Bibliographic metadata checked through the publisher record; the article body (paywalled) was not inspected, so no theorem or page locator is given. Cited for the variant of the Gomory–Hu construction without contraction: a parent array, one minimum cut computation per non-root vertex in the original graph, the re-hanging of vertices on the source side, and the swap of `s` and `t` when the parent of `t` is on the source side. That description was taken from secondary accounts of the algorithm. The Lean proof of correctness (`isGomoryHuTree_gusfieldParent`) is self-contained and does not follow the article's argument.

<a id="gusfield97"></a>
## gusfield97

Dan Gusfield. *Algorithms on Strings, Trees, and Sequences: Computer Science and Computational Biology.* Cambridge University Press, 1997. https://doi.org/10.1017/CBO9780511574931 . Bibliographic metadata checked through the publisher record, and section titles through a table of contents; the book body was not inspected in this pass. Cited for the Z-values and Z-boxes of §1.3, the linear-time Z algorithm of §1.4, and exact matching through the Z-values of `P$T` in §1.5; these locators come from the section titles. Theorem numbers and the precise statements in the body were not checked.

<a id="harpeledindykmotwani12"></a>
## harpeledindykmotwani12

Sariel Har-Peled, Piotr Indyk, Rajeev Motwani. “Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality.” *Theory of Computing* 8(14), 321–350, 2012. https://doi.org/10.4086/toc.2012.v008a014 . DOI and metadata as reported by search indexes; the open-access PDF could not be fetched in this pass (no connection). Cited for the `(r, cr, p₁, p₂)` form of locality-sensitive families, for the LSH `(c, r)`-near-neighbour structure with exponent `ρ = log (1/p₁) / log (1/p₂)` (locator Theorem 3.4, from secondary summaries; not checked against the text). According to those summaries, Theorem 3.4 is stated for a fully dynamic structure with `p₁, p₂ ∈ (0, 1)`, and the library formalizes only the static structure. Also cited for `ρ ≤ 1/c` for bit sampling in Hamming space (locator Section 3.2.1, from secondary summaries; not checked against the text).

<a id="hartline21"></a>
## hartline21

Jason D. Hartline. *Mechanism Design and Approximation*, book manuscript; chapters 1–7 revised 20 September 2021. http://jasonhartline.com/MDnA/ . The author-hosted Chapter 2, "Equilibrium", was consulted on 2026-11-08 for Definitions 2.3.2 and 2.4.1, §2.3, §2.4, Proposition 2.4.1, Theorem 2.5.1, §2.7 (Corollaries 2.7.1 and 2.7.2, Example 2.7.1), §2.8 (Example 2.8.1) and §2.9; locators follow that version.

<a id="hartmanis1968"></a>
## hartmanis1968

Juris Hartmanis. "Computational Complexity of One-Tape Turing Machine Computations." *Journal of the ACM* 15(2), 325–339, 1968. https://doi.org/10.1145/321450.321464 . Bibliographic metadata checked through Crossref; the article body was not inspected in this pass. The manual cites it for the `n log n` lower bound on one-tape recognition of nonregular languages, as attributed in [Pighizzini 2009](#pighizzini2009), §1 and §4.

<a id="heath24"></a>
## heath24

David Heath. "Efficient Arithmetic in Garbled Circuits." *Advances in Cryptology – EUROCRYPT 2024*, Lecture Notes in Computer Science 14655, 3–31, 2024. https://doi.org/10.1007/978-3-031-58740-5_1 . Full version: Cryptology ePrint Archive, Paper 2024/139, https://eprint.iacr.org/2024/139 . Locators follow the ePrint full version: §2.1 Definition 1 (circular correlation robustness), §3.2 Definitions 4 and 6 (switch systems and legality), §3.3 Construction 1 and Figure 2 (switch-system garbling and evaluation), §4 (pp. 13–14) and §4.1 `bin-to-hot` (p. 14, single-ciphertext binary-to-one-hot conversion, halving the material of Heath–Kolesnikov CCS 2021), and Appendix A, Theorem 4 and Figure 4 (obliviousness and its hybrids).

<a id="heldkarp62"></a>
## heldkarp62

Michael Held and Richard M. Karp. “A Dynamic Programming Approach to Sequencing Problems.” *Journal of the Society for Industrial and Applied Mathematics* 10(1), 196–210, 1962. https://doi.org/10.1137/0110015 . Bibliographic metadata checked on 2026-11-07; the article body was not inspected in this pass, so the manual cites it for the subset dynamic program and not for a numbered statement.

<a id="hennie1965"></a>
## hennie1965

F. C. Hennie. “One-tape, off-line Turing machine computations.” *Information and Control* 8(6), 553–578, 1965. https://doi.org/10.1016/S0019-9958(65)90399-2 . Bibliographic metadata checked; the article body was not inspected in this pass, so the manual cites it for the crossing-sequence method and not for a numbered statement.

<a id="henson26"></a>
## henson26

Christopher Henson and Fabrizio Montesi. *Computer Science as Infrastructure: the Spine of the Lean Computer Science Library (CSLib)*. EPTCS 449 (LSFA 2026), pp. 141–148, 2026. https://doi.org/10.4204/EPTCS.449.9 . Version-of-record metadata verified through https://arxiv.org/abs/2602.15078v2 on 2026-11-02 UTC; DOI resolver was unavailable in this research environment.

<a id="hhk17"></a>
## hhk17

Dennis Hofheinz, Kathrin Hövelmanns, Eike Kiltz. “A Modular Analysis of the Fujisaki–Okamoto Transformation.” *Theory of Cryptography (TCC 2017)*, LNCS 10677, 341–371, 2017. https://doi.org/10.1007/978-3-319-70500-2_12 ; full version https://eprint.iacr.org/2017/604 (dated 2 November 2021). Checked against the 2 November 2021 ePrint PDF (§2.1 correctness/spreadness and Def. 2.2 / Fig. 4 IND-CPA; §3.1 Fig. 5 transform `T`; §3.2.1 Fig. 9 `FO^⊥`; §3.2.2 Fig. 12 `FO-notbot`), with model adaptations (`ExplicitCoinPKE`/`Scheme` fixed types and arbitrary `sampleCoins`/`sampleMsg`/`sampleKey` samplers, two-stage IND-CPA `cpaAdvantage` via `PKE.cpaExperiment` on `ExplicitCoinPKE.toPKE`, with the single-stage fixed-message `indCpaGame`/`indCpaAdvantage` kept only for the spread-necessity example, and domain-separated `H : Bool × M × CT → K`) documented in the Lean modules and chapter text.

<a id="hhrvw20"></a>
## hhrvw20

Iftach Haitner, Thomas Holenstein, Omer Reingold, Salil Vadhan, Hoeteck Wee. “Inaccessible Entropy II: IE Functions and Universal One-Way Hashing.” *Theory of Computing* 16(8), 1–55, 2020. https://doi.org/10.4086/toc.2020.v016a008 . Open-access article PDF inspected (Section 3, Definitions 3.1, 3.3, 3.9, pp. 11–15, including canonical collision-finder sanitization and adversary-dependent accessible preimage sets; Section 4.2, Theorem 4.5 and Claims 4.6–4.8, pp. 21–25, with polynomial light-image threshold and `d * Real.logb 2 n / n` entropy gap against uniform strict-PPT adversaries; and Section 5.1, Theorem 5.1, Lemmas 5.3–5.7, and Section 5.1.5 STEPS 1–5, pp. 25–32, proved from Definition 3.9's adversary-dependent hypothesis).

<a id="hierholzer73"></a>
## hierholzer73

Carl Hierholzer. “Ueber die Möglichkeit, einen Linienzug ohne Wiederholung und ohne Unterbrechung zu umfahren.” *Mathematische Annalen* 6, 30–32, 1873. https://doi.org/10.1007/BF01442866 . Cited for the sufficiency of even degrees and the splicing construction; the attribution follows secondary sources, and the German original was not checked.

<a id="hill99"></a>
## hill99

Johan Håstad, Russell Impagliazzo, Leonid A. Levin, Michael Luby. “A Pseudorandom Generator from Any One-Way Function.” *SIAM Journal on Computing* 28(4), 1364–1396, 1999. https://doi.org/10.1137/S0097539793244708 . Publisher abstract checked; full article not independently audited.

<a id="hirahara2018"></a>
## hirahara2018

Shuichi Hirahara. *Non-Black-Box Worst-Case to Average-Case Reductions within NP*. FOCS 2018, 247–258. https://doi.org/10.1109/FOCS.2018.00032 . Full version ECCC TR18-138. Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter. The Lean module documentation follows its Definition 9 (`MINKT`) and Definition 11 (`GapMINKT`) with ECCC numbering.

<a id="hirahara2022"></a>
## hirahara2022

Shuichi Hirahara. *NP-Hardness of Learning Programs and Partial MCSP*. FOCS 2022, 968–979. https://doi.org/10.1109/FOCS54457.2022.00095 . Full version ECCC TR22-119. Checked against the FOCS proceedings text on 2026-11-11: the partial-string problems `MKTP*` and `MINKT*` (Section I, p. 971), consistency with a partial string (footnote 5, p. 971), the KT-style time measure of Theorem I.2 (footnote 6, p. 971), Theorem I.2 (p. 971; its "In particular" clause, NP-hardness of Partial MCSP and of `MINKT*` under randomized reductions, is `PartialMCSP.rpHard` and `MINKTStar.rpHard`), and the account of Ko's `MINKT` and relativization barrier (abstract, p. 968; Section I, p. 970). The ECCC numbering was not checked.

<a id="hk21"></a>
## hk21

David Heath, Vladimir Kolesnikov. “One Hot Garbling.” *ACM CCS 2021*, 574–593. https://doi.org/10.1145/3460120.3484764 . Full version: Cryptology ePrint Archive, Paper 2022/798, https://eprint.iacr.org/2022/798 . The ePrint full text was read in this pass for §4.1 (p. 10): the binary-to-one-hot conversion expands a GGM tree, sending two encrypted values per level and a final correction, `2(n − 1) + 1` ciphertexts in all. Cited as the origin of one-hot garbling. The library's single-ciphertext construction is the one of [heath24](#heath24), not this one, and its obliviousness reduction is original rather than a transcription of this paper's proof.

<a id="hkn24"></a>
## hkn24

David Heath, Vladimir Kolesnikov, Lucien K. L. Ng. “Garbled Circuit Lookup Tables with Logarithmic Number of Ciphertexts.” *EUROCRYPT 2024*. Full version: Cryptology ePrint Archive, Paper 2024/369, https://eprint.iacr.org/2024/369 . The ePrint full text was read in this pass for Definition 1 (circular correlation robustness, following Zahur–Rosulek–Evans, with `Δ ∈ 1{0,1}^{κ−1}`), Figure 1 (p. 10, the interface of one-hot garbling, credited to [hk21](#hk21); it states `(2n − 1)κ` bits, the count of [hk21](#hk21), whereas Theorem 1 uses the `(n − 1)κ` of [heath24](#heath24)), Lemma 1 and the display after it (`T(f)ᵀ · H(x) = f(x)` and its garbled form), Theorem 1 (p. 19, cost `2ⁿm + (n − 1)κ + nmκ` per gate, matching the cost breakdown on p. 20) and the proof of Theorem 3 (obliviousness; the `n − 1` one-hot rows are simulated by uniform strings, as shown in [hk21](#hk21)).

<a id="hmu06"></a>
## hmu06

John E. Hopcroft, Rajeev Motwani and Jeffrey D. Ullman. *Introduction to Automata Theory, Languages, and Computation*, third edition. Addison-Wesley, 2006. ISBN 0-321-45536-3. Cited for Section 7.4.4 ("Testing Membership in a CFL"), the CYK algorithm for grammars in Chomsky normal form. The section number and title were checked against secondary course material, not the printed book.

<a id="holenstein05"></a>
## holenstein05

Thomas Holenstein. “Key Agreement from Weak Bit Agreement.” *Proceedings of the 37th Annual ACM Symposium on Theory of Computing (STOC 2005)*. Author PDF inspected: https://crypto.ethz.ch/publications/files/Holens05.pdf (Section 2 on Impagliazzo's hard-core lemma; Section 2.1, Lemma 2.1; Section 2.1.1, Lemma 2.2 on choosing a set according to a measure).

<a id="holenstein06"></a>
## holenstein06

Thomas Holenstein. “Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness.” *TCC 2006*. Author PDF: https://crypto.ethz.ch/publications/files/Holens06.pdf . Definitions and construction overview consulted.

<a id="holenstein09"></a>
## holenstein09

Thomas Holenstein. “Parallel Repetition: Simplifications and the No-Signaling Case.” *Theory of Computing* 5(8), 141–172, 2009. https://doi.org/10.4086/toc.2009.v005a008 . Journal PDF inspected (Definition 2.4 and Theorem 2.5, p. 146; Definition 5.1, p. 151; Lemma 5.4 and (5.5), p. 153; Claims 6.2 and 6.3, p. 154; Lemma 6.4 and (6.3)–(6.7) of its proof, p. 155; (6.8)–(6.16), p. 156; the first stage of the embedding, from (6.15) and (6.16) by Corollary 5.3, (6.17)–(6.19) and the second stage, and Lemma 6.5, (6.20) and its proof, p. 157; Lemma 7.1, p. 158; the proof of Theorem 2.5, (7.6) and (7.7), p. 159).

<a id="hooverpersianoyeo26"></a>
## hooverpersianoyeo26

Alexander Hoover, Giuseppe Persiano and Kevin Yeo. "Lower Bounds for PIR with Preprocessing from Blackbox Cryptography." FOCS 2026 (the arXiv listing says "To appear in FOCS 2026"). Full version: arXiv:2607.06451v3, 10 September 2026, https://arxiv.org/abs/2607.06451v3 ; also Cryptology ePrint Archive, Paper 2026/1384, https://eprint.iacr.org/2026/1384 . Locators are the printed page numbers of arXiv:2607.06451v3, checked against its PDF on 2026-11-15. Definition 6.1, pp. 50–51: `Query` is a two-party protocol with client messages `τu` and server messages `τd`; `ε`-correctness is a success probability ("Pr[Query(st, Q; D, R) = (D[Q]; ⊥) : R ←$ {0,1}^r; (st; ⊥ | τoff) ←$ Setup(1^λ; 1^λ, D, R)] ≥ ε", p. 50, where the sampling of `R` and the `Setup` run is written under `Pr`); `δ`-privacy and `γ`-data privacy are defined against efficient adversaries, and "perfectly correct, private, and data private" means `ε = 1`, `δ = 0` and `γ = 0` (p. 51). Theorem 6.2 and its proof, p. 52: "Let s < k ≤ n and ε > 2^{s−k}. In the random oracle model, there does not exist a k-batch SPIR scheme with s-bit client storage that is ε-correct, perfectly private, and perfectly data private." The first version, arXiv:2607.06451v1, states the threshold as "ε > 1 − 2^{s−k}" (p. 46). Section 6.3, pp. 54–55 (the first toy, under the heading "n-bit client storage, O(k log n)-bit communication", p. 54). The library does not formalize Theorem 6.2. It proves an original information-theoretic bound in a restricted model (plain model, one online round, deterministic online client, perfect notions as identical view laws) by the counting argument in the proof of Theorem 6.2 (`Scheme.correct_le_card_div_two_pow`; `Scheme.correct_le_two_pow_sub` gives `ε ≤ 2 ^ (s - k)`, matching the v3 threshold; `Scheme.batchSPIR_limitation` uses the v1 threshold; all with a `2 ≤ n` guard that the zero-storage scheme at `n = k = 1, s = 0` shows is needed), using the transcript-independence step of that proof (`Scheme.eval_onlineTranscript_eq`). It also has an online-randomized variant with an explicit `Fintype.card Ω` factor (`RandomizedScheme.correct_le_card_mul_card_div_two_pow`, not in the source), the first Section 6.3 toy with an ideal setup (`toyScheme`: `2 ^ n * n!` client states, perfect correctness and data privacy, privacy on injective batches only, and the repeated-query counterexample for `2 ≤ k` and `2 ≤ n`), and a coordinate-wise variant `parallelToyScheme`, not in the source, which shows the hypotheses are jointly satisfiable for every `n` and `k`. Not formalized: Theorem 6.2 itself, Lemma 6.3, Theorem 6.4, the PRF inner-product toy and Sections 6.4–6.5 (Theorem 6.5).

<a id="hoyerleespalek07"></a>
## hoyerleespalek07

Peter Høyer, Troy Lee and Robert Špalek. "Negative weights make adversaries stronger." *Proceedings of the 39th Annual ACM Symposium on Theory of Computing (STOC 2007)*, 526–535, 2007. https://doi.org/10.1145/1250790.1250867 ; open version arXiv:quant-ph/0611054v2 (24 April 2007), https://arxiv.org/abs/quant-ph/0611054 . Checked in arXiv:quant-ph/0611054v2 on 2026-11-11: Section 1.1 Definitions 1–2 and Theorems 1–2 (`ADV` and `ADV±`, with the Boolean bound `(1 - 2√(ε(1-ε))) ADV±(f) ≤ 2T` matching Theorem 2, and the arbitrary-output bound strengthened to `1 - 2√(ε(1-ε)) - ε` vs. the weaker `- 2ε` form stated there), Section 7.1 Theorem 20 (Ambainis's 4-bit function), and Section 7.2 Theorem 21 (the 6-bit Hamming-weight-3 partial function separating `ADV ≤ 3` from `ADV± ≥ 2 + 3√5/5`, and its `(3/5, -1/5, 1/5)` specialization giving `16/5`).

<a id="hoza21"></a>
## hoza21

William M. Hoza. *Better Pseudodistributions and Derandomization for Space-Bounded Computation*. APPROX/RANDOM 2021, LIPIcs 207, 28:1–28:23, 2021. https://doi.org/10.4230/LIPIcs.APPROX/RANDOM.2021.28 . Appendix A (Lemma A.2 and the proof of Theorem A.3) was checked against the LIPIcs text on 2026-11-08.

<a id="hppy25"></a>
## hppy25

Alexander Hoover, Sarvar Patel, Giuseppe Persiano and Kevin Yeo. "Plinko: Single-Server PIR with Efficient Updates via Invertible PRFs." *Advances in Cryptology – EUROCRYPT 2025, Part VI*, Lecture Notes in Computer Science, 3–33, Springer, 2025. https://doi.org/10.1007/978-3-031-91095-1_1 ; full version: Cryptology ePrint Archive, Paper 2024/318, https://eprint.iacr.org/2024/318 . Checked against the full ePrint version on 2026-11-14 and rechecked on 2026-11-15: Section 3 Definition 3.1 (pp. 9–10, PRF), Section 4 Definition 4.1 (p. 10, invertible PRF), Section 4.2 Theorem 4.4 and Corollary 4.5 (pp. 12–13, permutation-and-sampler composition), Section 5.1 Definitions 5.1–5.2 and Figure 5 (pp. 19–20, offline-online and updateable PIR), Section 5.2 Theorem 5.3 and the Plinko construction, promotion, caching, update, correctness and privacy paragraphs (pp. 20–23), and Appendix A (p. 30) with Figure 7 (p. 31, normative pseudocode `HintInit`, `Query`, `Answer`, `Recon`, `GetHint`, `UpdateDB`, `UpdateHint`). `CslibFrontier.Crypto.Primitives.PRF.Invertible` formalizes `InvertiblePRF`, exact inversion correctness (`IsCorrectKey`, `IsCorrect`, `IsCorrectOnGen`), `idealInvertiblePRF`, and the inversion correctness of `compose` / `composePerm` (Theorem 4.4 / Corollary 4.5). `CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Plinko` formalizes `plinkoScheme` on `Fin c × Fin w` with `nReg + nBackup` hint slots (`ActiveHint`, `BackupHint`, `PlinkoState`), algorithmic equivalence of `getHint` via `iF.inv` and `getHintScan` (both return a `MatchedHint` record), single-pass entry streaming (`initPlinkoState`, `streamEntry`, `streamPreprocess`, `foldr_streamEntry_univ`), conditional multi-query correctness (`PlinkoState.Valid`, `CanAnswer`, `CanAnswerSeq`, `isCorrectFrom_plinkoScheme_of_canAnswerSeq`, `valid_of_mem_support_preprocess`), the fact that the query map sends a uniform hint conditioned on containing `x` to `plinkoSim` (`eval_buildQuery_conditioned_eq_plinkoSim`), adaptive multi-query perfect privacy of the idealized stand-in `plinkoHybridScheme`, which has no iPRF, keys or hint table, keeps `db` in its state and draws a fresh conditioned hint per query (`isPerfectlyPrivateWith_plinkoHybridScheme`, `privacyAdvantage_plinkoHybridScheme_eq_zero`), and single/batch database and hint updates driven by `UpdateSummary` records (`updateDB`, `updateHint`, `updateState`, `valid_updateHint`, `valid_updateState`). The bidirectional iPRF security proof of Theorem 4.4, PMNS (Section 4.1 Definitions 4.2–4.3, Figure 4, Lemma 4.6, Theorem 4.7), the Chernoff hint-load bound and Theorem 5.3 asymptotic bounds, `CanAnswerSeq` failure probability, amortized re-streaming, Appendix B Plinko-Piano, `B`-bit entries, FHE offline preprocessing, and exact multi-query privacy of the full `plinkoScheme` are not formalized. Modelling choices: `getHint` takes the smallest matching candidate slot where Figure 7 scans them in random order, and a cached query sends a dummy simulator message where Figure 7 queries a fresh random index. The bibliographic record (authors, title, Part VI, pages, DOI) was checked against the Crossref records for the chapter and the volume on 2026-11-15; Crossref does not list the LNCS volume number, so it is omitted.

<a id="hueffner2009"></a>
## hueffner2009

Falk Hüffner. "Algorithm Engineering for Optimal Graph Bipartization." *Journal of Graph Algorithms and Applications* 13(2), 77–98, 2009. https://doi.org/10.7155/jgaa.00177 . Journal PDF inspected on 2026-11-08 (https://jgaa.info/index.php/jgaa/article/download/paper177/2776): Section 3, Lemma 2 (p. 84; the disjoint-compression characterization by valid colourings and vertex cuts, after subdividing the edges at the old solution), the Compress-OCC routine (p. 85), and the running-time paragraph with Theorem 1 (p. 86). There Hüffner records that Reed, Smith and Vetta state `O(4^k · kmn)`, and shows that assigning each vertex of the old solution one of three roles (deleted, or one of two colourings of its neighbours) gives `3^k` minimum vertex cut problems and `O(3^k · kmn)` (Theorem 1). [OddCycleTransversal](../CslibFrontier/Algorithms/Lean/IterativeCompression/OddCycleTransversal.lean) credits the `3^k` count to this theorem; the improvement to `O(3^k · mn)` (Theorem 2, p. 88) is not formalized.

<a id="iknp03"></a>
## iknp03

Yuval Ishai, Joe Kilian, Kobbi Nissim and Erez Petrank. "Extending Oblivious Transfers Efficiently." *Advances in Cryptology – CRYPTO 2003*, Lecture Notes in Computer Science 2729, 145–161, Springer, 2003. https://doi.org/10.1007/978-3-540-45146-4_9 . Inspected on 2026-11-15 in the IACR archive copy of the CRYPTO 2003 version (https://www.iacr.org/archive/crypto2003/27290145/27290145.pdf, read through the Wayback Machine snapshot of 2026-08-21; 17 pages with the LNCS page numbers 145–161; SHA-256 `b1336e811da8a24c4c0fc66904dda4c61aa0283e7d146638c66c8917856ff9ae`): Theorem 2 (p. 147); §2.1 on the random oracle, hybrid-model reductions and black-box reductions (pp. 149–150); §2.2, the functionality `ot^m_ℓ` (p. 151); Fig. 1, the protocol with a semi-honest receiver (p. 152); §3.1, the perfect simulator for a malicious sender and the statistical simulator for a semi-honest receiver in the random-oracle model, with Lemma 1 (pp. 152–154); §5, Definition 1 (correlation robustness of an efficiently computable `h : {0,1}* → {0,1}`) and the discussion that replaces the random oracle of Fig. 1 by a correlation robust `h` for bit transfers, hashing `u` in place of `(j, u)`, with footnote 10 and Theorem 3 (p. 157); and Appendix A, the stand-alone definition of secure two-party computation against a non-adaptive adversary (p. 160).

<a id="ilango2020focs"></a>
## ilango2020focs

Rahul Ilango. *Constant Depth Formula and Partial Function Versions of MCSP are Hard*. FOCS 2020, 424–433. https://doi.org/10.1109/FOCS46700.2020.00047 . Full version ECCC TR20-183. Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.

<a id="ilo2020"></a>
## ilo2020

Rahul Ilango, Bruno Loff and Igor C. Oliveira. *NP-Hardness of Circuit Minimization for Multi-Output Functions*. 35th Computational Complexity Conference (CCC 2020), LIPIcs 169, 22:1–22:36. https://doi.org/10.4230/LIPIcs.CCC.2020.22 . Inspected the LIPIcs PDF directly: Theorem 4 (p. 22:5), the canonical DNF (pp. 22:19–22:20), Section 4.2 (pp. 22:20–22:21), Proposition 14 and the consequence `∆ = CC(T • g) − CC(g)` (pp. 22:21–22:22), Lemma 15 (p. 22:22) and Lemma 16 (pp. 22:22–22:23).

<a id="ilps22"></a>
## ilps22

Russell Impagliazzo, Rex Lei, Toniann Pitassi, Jessica Sorrell. *Reproducibility in Learning*. *Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 818–831, 2022. https://doi.org/10.1145/3519935.3519973 ; arXiv:2201.08430. Bibliographic metadata only (`references.bib`); primary text uninspected; no numbered paper theorems are claimed. Cited for the definitions of shared-seed `ρ`-replicable sample algorithms, randomized threshold/grid rounding, confidence amplification, finite-domain amplification (`amplifyFinite`), general-domain collision-threshold amplification (`amplifyReplicability`), and replicable bounded-mean and coin-bias estimation formalized (alongside `Cslib.ProbComp` program wrappers and `MeasureTheory.volume` variants) in `CslibFrontier/MachineLearning/Replicable/`.

<a id="immerman1988"></a>
## immerman1988

Neil Immerman. “Nondeterministic Space Is Closed under Complementation.” *SIAM Journal on Computing* 17(5), 935–938 (1988). DOI: https://doi.org/10.1137/0217058. Author copy inspected: https://people.cs.umass.edu/~immerman/pub/space.pdf (Theorem 1; inspected 2026-11-01).

<a id="impagliazzo01"></a>
## impagliazzo01

Russell Impagliazzo and Ramamohan Paturi. *On the Complexity of k-SAT*. Journal of Computer and System Sciences 62(2), 367–375, 2001. DOI: [10.1006/jcss.2000.1727](https://doi.org/10.1006/jcss.2000.1727). [Author-hosted copy](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturi_2001_jcss.pdf). Publisher metadata and abstract checked 2026-11-02; cited for the historical exponent-based hypothesis, not for the 2026 result.

<a id="impagliazzo95"></a>
## impagliazzo95

Russell Impagliazzo. “Hard-Core Distributions for Somewhat Hard Problems.” *Proceedings of the 36th Annual Symposium on Foundations of Computer Science (FOCS 1995)*, 538–545. DOI: [10.1109/SFCS.1995.492584](https://doi.org/10.1109/SFCS.1995.492584). Bibliographic metadata only; the paper itself was not inspected, and its statement is cited as recalled in [Holenstein 2005](#holenstein05), Section 2.

<a id="impagliazzojaiswalkabanetswigderson10"></a>
## impagliazzojaiswalkabanetswigderson10

Russell Impagliazzo, Ragesh Jaiswal, Valentine Kabanets and Avi Wigderson. *Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized*. SIAM Journal on Computing 39(4), 1637–1665, 2010. DOI: [10.1137/080734030](https://doi.org/10.1137/080734030) (as reported by search; not resolved). The authors' preprint dated 2009-10-19 (https://www.math.ias.edu/~avi/PUBLICATIONS/ImpagliazzoJaKaWi2010.pdf) was inspected on 2026-11-11: Theorem 1.2 (the decoder that CIKK cite as their Theorem 4.1), Algorithms 1–2, Theorem 3.2 and Lemmas 2.11–2.14 and 3.8–3.12. Locators follow the preprint; the journal numbering is unchecked.

<a id="impagliazzolevin90"></a>
## impagliazzolevin90

Russell Impagliazzo and Leonid A. Levin. "No Better Ways to Generate Hard NP Instances than Picking Uniformly at Random." *Proceedings of the 31st Annual Symposium on Foundations of Computer Science (FOCS 1990)*, 812–821. https://doi.org/10.1109/FSCS.1990.89604 . Bibliographic metadata only (`references.bib`); the paper was not inspected and no numbered result is claimed. Cited with [Blum, Furst, Kearns and Lipton](#blumfurstkearnslipton93) by [CryptoHardness/Inversion.lean](../CslibFrontier/MachineLearning/UniformLearning/CryptoHardness/Inversion.lean).

<a id="impagliazzopudlaksgall99"></a>
## impagliazzopudlaksgall99

Russell Impagliazzo, Pavel Pudlák and Jiří Sgall. “Lower Bounds for the Polynomial Calculus and the Gröbner Basis Algorithm.” *Computational Complexity* 8(2), 127–144, 1999. DOI: [10.1007/s000370050024](https://doi.org/10.1007/s000370050024). Bibliographic record from `references.bib` (`ImpagliazzoPudlakSgall1999`); the paper text was not inspected (the `algFPHP` axiom presentation follows [#3569](https://github.com/cslib-community/cslib-frontier/issues/3569)).

<a id="impagliazzowigderson97"></a>
## impagliazzowigderson97

Russell Impagliazzo and Avi Wigderson. *P = BPP if E Requires Exponential Circuits: Derandomizing the XOR Lemma*. Proceedings of the 29th Annual ACM Symposium on Theory of Computing, 220–229, 1997. DOI: [10.1145/258533.258590](https://doi.org/10.1145/258533.258590). ACM metadata checked by the coordinated source pass on 2026-11-02; no complete literature proof audit is asserted.

<a id="indykmotwani98"></a>
## indykmotwani98

Piotr Indyk, Rajeev Motwani. “Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality.” *Proceedings of the 30th Annual ACM Symposium on Theory of Computing* (STOC 1998), 604–613. https://doi.org/10.1145/276698.276876 . DOI and metadata as reported by search indexes; neither the DOI nor the full text was resolved in this pass. Cited for the definition of locality-sensitive families, for bit sampling under the Hamming distance, and for the LSH near-neighbour structure with `n^ρ` query cost. [andoniindyk08](#andoniindyk08), Section 2.4, p. 119, credits this paper, together with Gionis–Indyk–Motwani (VLDB 1999), with the rule that stops the query after `3L` candidates; this locator was not checked against the STOC text.

<a id="irani91"></a>
## irani91

Sandy Irani. "Two Results on the List Update Problem." *Information Processing Letters* 38(6), 301–306, 1991. https://doi.org/10.1016/0020-0190(91)90086-W . Crossref metadata checked on 2026-11-07; the full text was not inspected in this pass. The manual uses it only as the place where secondary sources say the deterministic `2n/(n+1)` list-update lower bound of Karp and Raghavan is reported.

<a id="jansonluczakrucinski2000"></a>
## jansonluczakrucinski2000

Svante Janson, Tomasz Łuczak and Andrzej Ruciński. *Random Graphs*. Wiley-Interscience Series in Discrete Mathematics and Optimization, Wiley, 2000. https://doi.org/10.1002/9781118032718 . Bibliographic data from secondary records of the DOI. The chapter locator (Chapter 3, small subgraphs and the threshold `n ^ (-1 / m(H))`) was taken from secondary descriptions; the book was not inspected in this pass, and no theorem number is claimed.

<a id="jeandelvanier2020"></a>
## jeandelvanier2020

Emmanuel Jeandel and Pascal Vanier. *The Undecidability of the Domino Problem*. In Shigeki
Akiyama and Pierre Arnoux (eds.), *Substitution and Tiling Dynamics*, Lecture Notes in Mathematics
2273, 293–357, Springer, 2020. [Publisher record](https://doi.org/10.1007/978-3-030-57666-0_6);
[authors' manuscript](https://www.lacl.fr/pvanier/rech/cirm.pdf). Read on 2026-11-16 by the
authoring Codex workers: §3.2 (beginning on manuscript p. 22), Definition 10 and Theorem 9
(p. 23), Proposition 8 (p. 24), and Figures 13–16 (pp. 25–26). The tile set is attributed to
[Ollinger](#ollinger2008) on p. 24. The Robinson modules use
[lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3aaaef3eac65559352ef94f62ab9c00482)
at that revision, retaining its authors and Apache-2.0 credit. “Corrected” identifies its
Figure 13 component transcription and the second thick-layer summand at `L2b` in Figure 16(c),
whose southeast extension uses `R1` rather than `R3`
([plan, lines 94–98](https://github.com/edemaine/lean-wang/blob/64268a3/plan.md#L94-L98)).
Both thick-layer boundary lanes are retained. This records lean-wang's correction, not a
verified erratum to the printed figures; historical correction: locator not verified.
