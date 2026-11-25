# Primary sources and provenance

<!--
Each entry is its anchor line, its `## key` heading, a blank line and its text.
Write each sentence of the text on a line of its own, so that changes to different sentences touch different lines.
`python3 scripts/sources_format.py --write` puts the file in this format, and `python3 scripts/check_operator_manual.py`, which CI runs, reports lines that are not in it.
The opt-in merge driver `scripts/resolve_sources_conflict.py` merges entries and lines; see CONTRIBUTING.md.
-->

Repository citations are pinned to the reviewed source or dependency revision.
Direct declaration links in the chapter text identify the supporting statement.
The [library bibliography](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8/references.bib) is linked at the survey revision; inclusion there is not a claim that this review checked every cited paper.
Mathematical attributions reported only from source annotations are identified as such in the chapters.

The private-transcript sources are described in [the extraction methods](history/methods.md); selected excerpts are included in the manual, while their bulk exports remain untracked.
Public GitHub issues, PRs and CI runs are linked from [development history](history/development.md).
Refetching mutable records is not an archive of their historical contents.
Inaccessible sources and unavailable archives are identified below or in the relevant chapter.

<a id="aaronson20"></a>
## aaronson20

Scott Aaronson.
*The Busy Beaver Frontier*.
ACM SIGACT News 51(3), 32–54, 2020. https://doi.org/10.1145/3427361.3427369 ; author's version https://www.scottaaronson.com/papers/bb.pdf . Read in the author's version on 2026-11-08: Proposition 1 (oracle access to any upper bound on the shift function solves the halting problem, hence no such bound is computable; the library proves the unrelativized corollary) and Proposition 2 (the shift function eventually exceeds every computable function).
Both are stated for Turing machines; Section 2 notes that they hold in any universal model of computation.
Section 1 defines `BB_L` for a programming language `L` with bit-string programs (and a variant through Kolmogorov complexity), the closest analogue of the library's code-size version.
Journal pagination was taken from the bibliographic record.

<a id="abboudcensorhillelkhourypaz21"></a>
## abboudcensorhillelkhourypaz21

Amir Abboud, Keren Censor-Hillel, Seri Khoury and Ami Paz.
"Smaller Cuts, Higher Lower Bounds."
*ACM Transactions on Algorithms* 17(4), article 30, 30:1–30:40, 2021. https://doi.org/10.1145/3469834 ; preprint arXiv:1901.01630.
Checked against the publisher's PDF on 2026-11-13: Definition 4 (families of streaming lower bound graphs, p. 30:32) and Theorem 14 (p. 30:33: an `R`-pass streaming algorithm with `M` bits of memory for such a family gives `RM = Ω(CC(f))`, deterministic and randomized).
The protocol in the proof of Theorem 14 sends at most `(2R − 1)M` bits (`M` from Alice in each pass and from Bob in every pass but the last); the proof incorrectly writes this total as `R(2M − 1)`, which does not affect the asymptotic statement.
The library counts the same protocol exactly, `(2p − 1)b` bits of memory states, plus one bit so that the output is determined by the transcript (in the source, only Bob learns the answer). arXiv:1901.01630v2 numbers these Definition 3 and Theorem 15.

<a id="abrahamdolevgonenhalpern2006"></a>
## abrahamdolevgonenhalpern2006

Ittai Abraham, Danny Dolev, Rica Gonen and Joseph Y. Halpern.
"Distributed Computing Meets Game Theory: Robust Mechanisms for Rational Secret Sharing and Multiparty Computation."
*Proceedings of the Twenty-Fifth Annual ACM Symposium on Principles of Distributed Computing (PODC 2006)*, 53–62, 2006. https://doi.org/10.1145/1146381.1146393 . Bibliographic metadata only (`references.bib`); the full text was not inspected locally in this pass and no theorem locators are attributed here.
Cited in [SecretSharing.lean](../CslibFrontier/GameTheory/RationalCrypto/SecretSharing.lean) and [Payoff.lean](../CslibFrontier/GameTheory/Strategic/Payoff.lean) alongside [dodisrabin2007](#dodisrabin2007) for `k`-resilient equilibria (`(t - 1)`-resilience) in rational secret sharing via randomized geometric termination.

<a id="abukhzam2007"></a>
## abukhzam2007

Faisal N. Abu-Khzam, Michael R. Fellows, Michael A. Langston and W. Henry Suters.
"Crown Structures for Vertex Cover Kernelization."
*Theory of Computing Systems* 41(3), 411–430, 2007. https://doi.org/10.1007/s00224-007-1328-0 . Bibliographic data and the abstract (crown structures; a crown-based kernelization compared with the LP-based one) were checked against secondary search summaries on 2026-11-08 UTC.
The full text was not inspected, and the crown definition used in [Crown](../CslibFrontier/Foundations/Combinatorics/SimpleGraph/Crown.lean) is not attributed to a numbered statement there.
Chor, Fellows and Juedes, "Linear Kernels in Linear Time, or How to Save k Colors in O(n²) Steps", WG 2004, LNCS 3353, 257–269, https://doi.org/10.1007/978-3-540-30559-0_22, is cited in the module docstring on the same basis.

<a id="acek17"></a>
## acek17

Daniel Apon, Chongwon Cho, Karim Eldefrawy and Jonathan Katz.
"Efficient, Reusable Fuzzy Extractors from LWE."
*Cyber Security Cryptography and Machine Learning (CSCML 2017)*, LNCS 10332, 1–18, Springer, 2017. https://doi.org/10.1007/978-3-319-60080-2_1 ; IACR Cryptology ePrint Archive Report 2017/755, https://eprint.iacr.org/2017/755 . Checked against the ePrint 2017/755 PDF on 2026-11-14: Definitions 2 and 3 (weak and strong reusability, Section 2.2, p. 6; the public-parameters model is described in Section 2.1, p. 4), the common-matrix FMR construction, Theorem 1 and the 1-query strong-reusability attack (Section 3.3, pp. 9–10), and the encryption-based strongly reusable fuzzy extractor from LWE without random oracles (Section 5, pp. 11–12).
Checked again on 2026-11-15 (SHA-256 `18ebc576b367e3896c77293ca11909a12477b84c770d1490ae3df8db5b8b9d02`): Definition 4 (decisional LWE `LWE_{n,m,q,χ}` for an integer `q ≥ 2`, Section 2.3, p. 7) and the Section 5 security sketch (assumptions (1) and (2), the `LWE_{n,(t+2)m,q,χ}` claim for adversaries making at most `t` oracle calls, and the simulation, p. 12).

<a id="acemogluozdaglar2007jsac"></a>
## acemogluozdaglar2007jsac

Daron Acemoglu and Asuman Ozdaglar.
"Competition in Parallel-Serial Networks."
*IEEE Journal on Selected Areas in Communications* 25(6), 1180–1192, 2007 (bibliography key `AcemogluOzdaglar2007JSAC`). https://doi.org/10.1109/JSAC.2007.070812 . Checked firsthand on 2026-11-24 UTC against the typeset IEEE JSAC PDF (13 pages, printed pp. 1180–1192, SHA-256 `40f977832ef5523fd110fa19f7a26066b29d2e7943deacdda3d6cbc61ee8addd`): Section II (pp. 1181–1182: Assumption 1 smooth convex latencies with `l_j(0) = 0`, Eq. (1) priced Wardrop equilibrium on parallel-serial topologies, Proposition 1 Beckmann potential existence, and Definition 2 social optimum), Section III (p. 1183: Definition 3 pure-strategy oligopoly equilibrium), Section IV-A (pp. 1183–1184: Eq. (8) social surplus efficiency metric and Example 2 showing pure-strategy OE coordination failure can yield arbitrarily low efficiency), Section IV-B (pp. 1184–1185: Definition 5 Harsanyi strict OE, Lemma 1 interior positivity of strict OE prices and flows when some path has positive revenue, and Proposition 6(a) serial markup lower bound `p_j^{OE} ≥ x_i^{OE} ∑_{k ∈ N_i} l_k'(x_i^{OE})`), Section IV-C–D (p. 1185: Example 3 showing partial-demand strict OE can have efficiency `4 n / (n + 1)^2 → 0`, Definition 6 full-demand strict / strong OE, and Example 4 two-path tightness family approaching `1 / 2`), and Section IV-E (p. 1189: Theorem 2 tight `1 / 2` efficiency lower bound for full-demand strict OE).
Cited by [ParallelSerial.lean](../CslibFrontier/GameTheory/Congestion/Pricing/ParallelSerial.lean).

<a id="acemogluozdaglar2007mor"></a>
## acemogluozdaglar2007mor

Daron Acemoglu and Asuman Ozdaglar.
"Competition and Efficiency in Congested Markets."
*Mathematics of Operations Research* 32(1), 1–31, 2007 (bibliography key `AcemogluOzdaglar2007MOR`). https://doi.org/10.1287/moor.1060.0231 . Checked firsthand on 2026-11-24 UTC against the typeset INFORMS journal PDF (31 pages, printed pp. 1–31, SHA-256 `f3bf52dea8bd05f55cb39571c9dc71163ccbf52a7ccd2dbb4cfc644537ccd425`): Section 2 (pp. 4–7: Eq. (2) priced Wardrop equilibrium, Assumption 2.1 smooth convex latencies on `[0, ∞)` with `l_i(0) = 0`, Proposition 2.2 Beckmann potential existence, Definition 2.2 social optimum, and Eq. (7) KKT social-optimality conditions), Section 3 (pp. 7–8: Definition 3.1 monopoly equilibrium, Proposition 3.2 equivalence between monopoly equilibrium flows and social optima with `p_i = R - l_i(x_i)` on active links and zero consumer surplus), Section 4 (pp. 8–12: Definition 4.1 multi-link-provider pure-strategy oligopoly equilibrium, Assumption 4.1 singleton ownership of active zero-latency links, Lemma 4.2 interior positivity of provider profits and link revenues/flows, Example 4.2 three-link two-provider counterexample when Assumption 4.1 is omitted, Proposition 4.4 and Corollary 4.1 provider markup inequalities `x_i l_i'(x_i) ≤ p_i` and `p_i ≤ x_i l_i'(x_i) + x_i / ∑_{q: owner(q) ≠ s} (l_q'(x_q))⁻¹`), and Section 5 (pp. 13–20: Lemmas 5.1–5.2 marginal-cost equalization for same-owner links, Example 5.2 exact `5 / 6` witness on `I ≥ 2` links, and Theorem 5.2 tight `5 / 6` oligopoly efficiency bound).
Note that in the real-valued uncapacitated `[0, ∞)` specialization formalized here (`b_{C_i} = ∞`), every link flow is interior above `x_i`, so capacity-boundary multipliers vanish.
Cited by [PricedWardrop.lean](../CslibFrontier/GameTheory/Congestion/Pricing/PricedWardrop.lean) and [Oligopoly.lean](../CslibFrontier/GameTheory/Congestion/Pricing/Oligopoly.lean).

<a id="achlioptas03"></a>
## achlioptas03

Dimitris Achlioptas.
“Database-Friendly Random Projections: Johnson–Lindenstrauss with Binary Coins.”
*Journal of Computer and System Sciences* 66(4), 671–687, 2003. https://doi.org/10.1016/S0022-0000(03)00025-4 . Author-hosted copy of the typeset journal version: https://cgi.di.uoa.gr/~optas/papers/jl.pdf . Checked against that copy on 2026-11-07 UTC: Theorem 1.1 on p. 673 (squared distances within `1 ± ε` with probability at least `1 - n^(-β)` for `k ≥ k₀ = (4 + 2β) log n / (ε²/2 - ε³/3)`, stated for all `ε, β > 0`; the `±1` distribution is (1)).
Also checked: Lemma 4.1 on p. 679 (Gaussian entries), Lemma 5.1 on p. 679 (the per-vector tails), and Lemma 5.2 on p. 680, eqs. (6)–(7) (the bounds on `𝔼 exp (h Q²)` and `𝔼 Q⁴`).

<a id="acor22"></a>
## acor22

Divesh Aggarwal, Eldon Chung, Maciej Obremski, João Ribeiro.
"On Secret Sharing, Randomness, and Random-less Reductions for Secret Sharing."
*Theory of Cryptography (TCC 2022), Part I*, LNCS 13747, 327–354, Springer, 2022. https://doi.org/10.1007/978-3-031-22318-1_12 ; ePrint https://eprint.iacr.org/2021/802 . Bibliographic metadata taken from `references.bib`.
The direct ePrint copy was not inspected (gated behind an automated challenge), so ACOR22 attributions are unverified directly; the formalized threshold design results (`ThresholdDesign`, `(t', n') → (2, 2)` composition, `(2, 3, 2, 2)` and `(r, r, 2, 2)` impossibility for `r ≥ 3`) were checked against [aggarwal26](#aggarwal26), Section 5.

<a id="afekattiyadolevgafnimerrittshavit1993"></a>
## afekattiyadolevgafnimerrittshavit1993

Yehuda Afek, Hagit Attiya, Danny Dolev, Eli Gafni, Michael Merritt and Nir Shavit.
"Atomic Snapshots of Shared Memory."
*Journal of the ACM* 40(4), 873–890, 1993. https://doi.org/10.1145/153724.153741 ; author-hosted copy https://people.csail.mit.edu/shanir/publications/AADGMS.pdf . Inspected the 21-page author-hosted PDF (SHA-256 `bdeef5d024d12b97bc148efcb999234e04785b9e57de90e1df04ded6c1078459`; journal pagination taken from the bibliographic record) on 2026-11-22 UTC: Section 2.1 (pp. 4–5, Figure 1 on p. 4 and Definition 1 on p. 5 for the canonical single-writer atomic snapshot specification) and Section 3 with Section 3.1 (pp. 7–10, Figure 3 on p. 8 for the unbounded sequence-numbered single-writer `scan`/`update` algorithm with embedded scan and twice-moved view borrowing, Lemmas 3.1 and 3.2 on p. 9, and Lemmas 3.3 and 3.4 and Theorem 1 on p. 10).
Cited by [SetAgreement/AtomicSnapshot.lean](../CslibFrontier/Computability/Distributed/SetAgreement/AtomicSnapshot.lean), which models each single-register read of `collect` as an individual atomic transition along `ScanOrder P`, fuses `scan_i`'s final local decision (`finishScan`) with `.doneScan` and `update_i`'s atomic register write (`readyToWrite`) with `.doneUpdate` (whereas Figure 1 separates internal `Scan_i`/`Update_i(d)` from external `ScanReturn_i`/`UpdateReturn_i`), and proves Herlihy–Wing linearizability (`unbounded_snapshotLinearizable_of_reachable`) and `O(n²)` wait-free step and shared-register operation bounds as an unbounded-register step toward [#7504](https://github.com/cslib-community/cslib-frontier/issues/7504); Section 4 (bounded single-writer registers, pp. 10–13) and Section 5 (bounded multi-writer registers, pp. 13–16) remain open in [#7504](https://github.com/cslib-community/cslib-frontier/issues/7504).

<a id="aggarwal26"></a>
## aggarwal26

Divesh Aggarwal.
*Secret Sharing Despite Non-Extractable Randomness*. arXiv:2610.20173v2, 2026. https://arxiv.org/abs/2610.20173v2 . LaTeX source (`secret_sharing.tex`, version v2) checked on 2026-11-10 UTC: Definition 2.1 (threshold finite-key correctness and `δ`-statistical privacy relative to a source class `sources`; generalized in the library to general `AccessStructure` and arbitrary `Key`) and Section 5 ("Relation to the reductions of ACOR22", covering threshold distribution designs, the `(t', n') → (2, 2)` composition, and non-existence of `(2, 3, 2, 2)` and `(r, r, 2, 2)` designs with `r ≥ 3`, generalized in the library to `DistributionDesign`, `ThresholdDesignOn`, and `no_thresholdDesign_two_two` for `2 ≤ t ≤ n`, `3 ≤ n`).

<a id="ahocorasick75"></a>
## ahocorasick75

Alfred V. Aho, Margaret J. Corasick.
"Efficient String Matching: An Aid to Bibliographic Search."
*Communications of the ACM* 18(6), 333–340, 1975. https://doi.org/10.1145/360825.360855 . Scanned copy in D. J. Bernstein's bibliography archive, https://cr.yp.to/bib/1975/aho.pdf , checked 2026-11-08 for Algorithms 1 and 3, Lemmas 1–3, Theorems 1, 2 and 4, and Figures 1 and 2.

<a id="ahlswedecsiszar93"></a>
## ahlswedecsiszar93

Rudolf Ahlswede and Imre Csiszár.
"Common Randomness in Information Theory and Cryptography.
Part I: Secret Sharing."
*IEEE Transactions on Information Theory* 39(4), 1121–1132, 1993. https://doi.org/10.1109/18.243431 . Bibliographic metadata checked via secondary search summaries on 2026-11-11.

<a id="ahlswedecsiszar07"></a>
## ahlswedecsiszar07

Rudolf Ahlswede and Imre Csiszár.
"On Oblivious Transfer Capacity."
ISIT 2007, Nice, France, pp. 2061–2064, https://doi.org/10.1109/ISIT.2007.4557524, https://www.math.uni-bielefeld.de/ahlswede/homepage/public/242.pdf.
Checked on 2026-11-11 against the open-access technical report `242.pdf`: §3 Theorem 1 (PDF p. 6) and §4 Eq. (14) (PDF p. 8).
Used for the asymptotic single-choice-bit string-OT bound (which the Lean formalization adapts to finite exact batch-bit OT with independent choices).

<a id="aik11"></a>
## aik11

Benny Applebaum, Yuval Ishai, Eyal Kushilevitz.
"How to Garble Arithmetic Circuits."
*52nd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2011)*, 120–129, 2011. https://doi.org/10.1109/FOCS.2011.40 . Checked on 2026-11-10 against the author-hosted copy of the FOCS version, https://bennyapplebaum.sites.tau.ac.il/_files/ugd/f706bf_ccb157901f504e32a79d89a666f56de3.pdf , which has no printed page numbers: Definition 4.2 (affinization gadget), Definition 4.5 (perfect privacy of a gadget) and Section 5, Fact 5.1.
Cited for the framework of affine key encodings over a ring (with per-wire keys) and for the notion of an affinization gadget; the four-value multiplication gadget formalized here is an explicit instance derived in the Lean source, not the general compiler of the paper.

<a id="alberseiltsevendarmansourroditty06"></a>
## alberseiltsevendarmansourroditty06

Susanne Albers, Stefan Eilts, Eyal Even-Dar, Yishay Mansour and Liam Roditty.
"On Nash Equilibria for a Network Creation Game."
*Proceedings of the Seventeenth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2006)*, 89–98, SIAM, 2006. https://doi.org/10.1145/1109557.1109568 (bibliography key `AlbersEiltsEvenDarMansourRoditty2006`).
Bibliographic provenance from [tardoswexler07](#tardoswexler07), §19.2.3, §19.5.1 and p. 511 bibliography (replacing the chapter's initial `A. Albers` with `Susanne Albers` as in `references.bib`); the paper's full text was not inspected firsthand, so internal theorem and page locators are recorded as `unverified` in [Entries/LocalConnection.lean](../CslibFrontierResults/Entries/LocalConnection.lean).
The `4α / √n + 9` equilibrium-diameter bound and `O(1 + α / √n)` price-of-anarchy bound in [NetworkFormation/LocalConnection.lean](../CslibFrontier/GameTheory/NetworkFormation/LocalConnection.lean) are attributed to it following [tardoswexler07](#tardoswexler07), Theorem 19.6 (pp. 493–494).

<a id="almanwilliams2017"></a>
## almanwilliams2017

Josh Alman and Ryan Williams.
"Probabilistic Rank and Matrix Rigidity."
[arXiv:1611.05558v2](https://arxiv.org/pdf/1611.05558v2), 7 January 2017 (bibliography key `AlmanWilliams2017`, PDF SHA-256 `8ca83b72bdc02cf3b637def97745bd2af57a6d8c4b598ca622e27e03b5ec31d0`).
Section 3, Lemma 3.2 (printed p. 6, PDF p. 7) gives integer multilinear interpolation on consecutive Hamming layers, formalized as `Cslib.exists_multilinear_of_consecutive_weights`.
The finite Sylvester–Hadamard rank and off-band edit bounds are steps toward [#3209](https://github.com/cslib-community/cslib-frontier/issues/3209).
The asymptotic estimates in Lemmas 3.1 and 3.3 and the non-rigidity bound in Theorem 1.1 remain open in this development.
[Independent agent source check of §§1–3](https://github.com/cslib-community/cslib-frontier/pull/7803#pullrequestreview-6016309173).

<a id="alonbabaiitai1986"></a>
## alonbabaiitai1986

Noga Alon, László Babai and Alon Itai.
"A Fast and Simple Randomized Parallel Algorithm for the Maximal Independent Set Problem."
*Journal of Algorithms* 7(4), 567–583, 1986. https://doi.org/10.1016/0196-6774(86)90019-2 ; author-hosted copy of the typeset article: https://www.cs.tau.ac.il/~nogaa/PDFS/Publications2/A%20fast%20and%20simple%20randomized%20parallel%20algorithm%20for%20the%20maximal%20independent%20set%20problem.pdf . Checked on 2026-11-22 UTC against that PDF (17 pages, printed pp. 567–583, SHA-256 `165d32a264e8f2e66bfaf85fec05358b21c90896a34824f49d885cd05680fc51`): §2–§3 (pp. 568–570, Procedure `IN` and single-phase Procedure `IN(H)` on p. 570, which marks each active vertex `v` of degree `d_H(v) > 0` independently with probability `1 / d_H(v)`, isolated vertices into `S`, and for each edge `u v` with both endpoints marked randomly erases `u`'s mark with probability `d_H(u) / (d_H(u) + d_H(v))` and `v`'s otherwise before deleting `S` and `N(S)`) and §4 (pp. 570–572, defining `v` as bad when at least `2 / 3` of its neighbors have degree strictly exceeding `d_H(v)` and good otherwise, proving `Pr[good v deleted] >= (1 - e^(-1/3)) / e` in Lemmas 4.1–4.2 and Corollary 4.3 on pp. 570–571, `>= |E(H)| / 2` good edges via the directed `d^+(u) >= 2 d^-(u)` counting argument in Lemma 4.4 on p. 572, and `E[deleted edges] >= (1 / (2 e))(1 - e^(-1/3)) |E(H)|` in Corollary 4.5 on p. 572).
Cited for the parallel phase-based MIS paradigm and the Lemma 4.4 good-edge orientation argument; [LocalGraph/LubyMIS.lean](../CslibFrontier/Computability/Distributed/LocalGraph/LubyMIS.lean) (`localCoinPhase`, `localCoinLubyMIS`, `seventyTwo_mul_expect_liveEdges_coinPhase_le`) formalizes instead Algorithm 7.6 of [Wattenhofer](#wattenhofer16), §7.2, pp. 73–76 (presenting [Luby](#luby1986)'s `1 / (2 d_H(v))` marking with deterministic `(d_H, uid)` tie-breaking, `1 / 36` good-vertex deletion, and `71 / 72` edge survival, steps toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505) and [#3270](https://github.com/cslib-community/cslib-frontier/issues/3270); Procedure `IN(H)`'s `1 / d_H(v)` + randomized edge-mark erasure is not formalized).

<a id="alonbabaisuzuki1991"></a>
## alonbabaisuzuki1991

Noga Alon, László Babai and Hiroshi Suzuki.
“Multilinear Polynomials and Frankl–Ray-Chaudhuri–Wilson Type Intersection Theorems.”
*Journal of Combinatorial Theory, Series A* 58(2), 165–180, 1991. https://doi.org/10.1016/0097-3165(91)90058-O . Bibliographic metadata from search summaries on 2026-11-08; the full text was not inspected in this pass.
The manual attributes only the multilinear polynomial method for uniform and nonuniform restricted-intersection bounds to this paper; theorem numbers are not cited.

<a id="alonfeldmanprocacciatennenholtz10"></a>
## alonfeldmanprocacciatennenholtz10

Noga Alon, Michal Feldman, Ariel D. Procaccia and Moshe Tennenholtz.
"Strategyproof Approximation of the Minimax on Networks."
*Mathematics of Operations Research* 35(3), 513–526, 2010. https://doi.org/10.1287/moor.1100.0457 (journal metadata verified via web search on 2026-11-11; journal PDF not inspected).
Preprint inspected on 2026-11-11: "Strategyproof Approximation Mechanisms for Location on Networks," arXiv:0907.2049v1 (12 July 2009), https://arxiv.org/pdf/0907.2049v1 . Checked Section 2 (pp. 4–5: strategyproofness, group strategyproofness in the weak sense, social cost, approximation ratio) and Section 3.2 (pp. 6–7: Mechanism 1 random dictatorship, Theorem 3.1 proving strategyproofness and `2 - 2/n` approximation on graphs, first remark extending to arbitrary metric spaces, third remark on the 3-leaf star counterexample to weak group strategyproofness, and fourth remark on weak group strategyproofness on the line).

<a id="alongibbonsmatiasszegedy99"></a>
## alongibbonsmatiasszegedy99

Noga Alon, Phillip B. Gibbons, Yossi Matias, Mario Szegedy.
“Tracking Join and Self-Join Sizes in Limited Storage.”
*Proceedings of the 18th ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS)*, 10–20, 1999. https://doi.org/10.1145/303976.303978 . Author-hosted PostScript of the conference version: https://www.math.tau.ac.il/~matias/papers/pods99.ps . Checked against that copy on 2026-11-08: Section 4.3 (the tug-of-war join signature `S(F) = ∑ ε_i f_i` with four-wise independent `±1` signs and estimator `S(F)·S(G)`), Lemma 4.4 (mean `|F ⋈ G|`, variance at most `2·SJ(F)·SJ(G)`, through the exact variance in equation (3) of its proof), Theorem 4.5 (the `k`-fold mean with `k = c·B₂²/B₁²` and Chebyshev), the deletion rule following it, and the statement of Theorem 4.3 (signature lower bound, not formalized).
The journal version, *Journal of Computer and System Sciences* 64(3), 719–747, 2002, https://doi.org/10.1006/jcss.2001.1813 , was taken from bibliographic metadata and not inspected.

<a id="alonmatiasszegedy99"></a>
## alonmatiasszegedy99

Noga Alon, Yossi Matias, Mario Szegedy.
“The Space Complexity of Approximating the Frequency Moments.”
*Journal of Computer and System Sciences* 58(1), 137–147, 1999; preliminary version in STOC 1996. https://doi.org/10.1006/jcss.1997.1545 . Author-hosted copy of the journal version: https://www.tau.ac.il/~nogaa/PDFS/amsz4.pdf . An independent agent review checked the theorem locators and statements (Theorem 2.2 for the `F₂` sketch, Proposition 3.1 for the `F∞` lower bound) against that copy on 2026-11-07 UTC.
The JCSS page numbers were taken from secondary search summaries and were not checked against the typeset journal PDF.

<a id="alonmilman1985"></a>
## alonmilman1985

Noga Alon and Vitali D. Milman.
"λ₁, Isoperimetric Inequalities for Graphs, and Superconcentrators."
*Journal of Combinatorial Theory, Series B* 38(1), 73–88, 1985. https://doi.org/10.1016/0095-8956(85)90092-9 . Bibliographic metadata checked on 2026-11-24; the article PDF was not directly inspected, so no internal theorem number from this paper is claimed.
Cited as the origin of the discrete combinatorial-Laplacian Cheeger inequality, whose statement and proof (`(h'_G)² / (2 max_v d_v) ≤ λ'_1 ≤ 2 h'_G`) were verified firsthand against [chung1997](#chung1997), §2.5, pp. 34–35.

<a id="alonspencer2016"></a>
## alonspencer2016

Noga Alon and Joel H. Spencer.
*The Probabilistic Method*, 4th edition.
Wiley, 2016.
ISBN 978-1-119-06195-3.
Bibliographic data from the library bibliography.
The section locators used for the second moment method and random graphs (Chapter 4: §4.3 for the bound `Pr[X = 0] ≤ Var X / (E X) ^ 2`, §4.4 for random graphs and threshold functions) were taken from secondary tables of contents and from an agent review, which placed the bound at Theorem 4.3.1.
The book was not inspected in this pass, and the library cites section numbers only.
The 0-1 law for `G(n, p)` with constant `0 < p < 1` is cited at §10.4 ("Zero–One Laws", Chapter 10 "Random Graphs") from secondary tables of contents, consulted on 2026-11-10; one secondary summary placed it at §10.7 instead, so this locator is unverified and no theorem number is cited.

<a id="alonyusterzwick1995"></a>
## alonyusterzwick1995

Noga Alon, Raphael Yuster, Uri Zwick.
"Color-Coding."
*Journal of the ACM* 42(4), 844–856, 1995. https://doi.org/10.1145/210332.210337 . Bibliographic data from the DOI record.
The locator Lemma 3.1 (colorful paths by dynamic programming over color sets) was taken from secondary descriptions; the full text was not inspected in this pass.

<a id="alrabiahgoodmanmosheiffribeiro2025"></a>
## alrabiahgoodmanmosheiffribeiro2025

Omar Alrabiah, Jesse Goodman, Jonathan Mosheiff and João Ribeiro.
*Low-Degree Polynomials Are Good Extractors*.
APPROX/RANDOM 2025. https://doi.org/10.4230/LIPIcs.APPROX/RANDOM.2025.38 . Locators follow ECCC TR24-093, revision 1, https://eccc.weizmann.ac.il/report/2024/093/revision/1/download/ . Checked directly on 2026-11-22: Theorem 2 (printed p. 8) gives random degree-`d` sumset extractors for `k ≥ C d (n / ε²)^(1/⌊d/2⌋)`; for `d = 4` and `ε = n^(-β)`, `β < 1/2`, its threshold is sublinear.
Cited in `PolynomialWitness.lean` for prior existence; that module proves coordinate-rectangle estimates and frontier applications, not the full sumset theorem or a uniform construction.

<a id="ambainis02"></a>
## ambainis02

Andris Ambainis.
"Quantum lower bounds by quantum arguments."
*Journal of Computer and System Sciences* 64(4), 750–767, 2002 (preliminary version in STOC 2000). https://doi.org/10.1006/jcss.2002.1826 ; open preprint arXiv:quant-ph/0002066v1 (24 February 2000), https://arxiv.org/abs/quant-ph/0002066 . Checked in arXiv:quant-ph/0002066v1 (`density4.tex`) on 2026-11-11: Section 2 (query model and extension to larger input/output alphabets), Section 3 Lemma 1 (multi-outcome distinguishing state-overlap bound `2√(ε(1-ε))`, proved in `Overlap.lean` and `ReadoutOverlap.lean`), Section 6.1 Theorem 6 (relational adversary bound `(1 - 2√(ε(1-ε))) √(m m') = O(T √l_max)` for non-Boolean input alphabets and pairwise conflict product `l_{x,i} l_{y,i} ≤ l_max`, proved in `ValueAdversary.lean` with constant `2` for arbitrary unitary value oracles), and Section 6.2 Theorem 7 (`Ω(√N)` query lower bound for inverting a permutation via single-transposition pairs across a balanced bipartition, proved in `PermutationInversion.lean`).
Journal pagination comes from `references.bib` and was not directly inspected.

<a id="ambainis06"></a>
## ambainis06

Andris Ambainis.
"Polynomial degree vs. quantum query complexity."
*Journal of Computer and System Sciences* 72(2), 220–238, 2006; preliminary version FOCS 2003; arXiv:quant-ph/0305028v4 (23 November 2004). https://arxiv.org/abs/quant-ph/0305028 . Read in arXiv:quant-ph/0305028v4 on 2026-11-11: Section 3.3 Definitions 1–3 (relation weights, `w'(x, y, i)`, and adversary bound), Section 4.1 Lemma 1 (the weighted adversary lower bound), Lemma 4 (`w'` formulation), and Section 4.3 Lemma 3 (`4`-bit base function with weight `w = 1` at Hamming distance `1` and `2/3` at Hamming distance `2`, `w' ∈ {1, 1/3, 4/3}`, and maximum load `wt/v = 2.5`).
Journal pagination was checked through DBLP/search metadata and was not inspected directly.

<a id="ambainismoscatappdewolf00"></a>
## ambainismoscatappdewolf00

Andris Ambainis, Michele Mosca, Alain Tapp and Ronald de Wolf.
*Private Quantum Channels*. 41st Annual Symposium on Foundations of Computer Science (FOCS 2000), 547–553. https://doi.org/10.1109/SFCS.2000.892142 ; author-hosted copy https://homepages.cwi.nl/~rdewolf/publ/qc/AMTW00.pdf (7 PDF pages, printed pp. 547–553, SHA-256 `d9b9626de1c7f3d9396d9696ce15b5a47b9b1ee95c17ce613591d9ceb00412c9`).
Read in the author-hosted copy on 2026-11-08 and re-checked on 2026-11-24: Definition 3.1 (p. 548, private quantum channel: the key-averaged image of every plaintext state in `S` with ancilla `ρ_a` is one fixed state `ρ_0`), Theorem 4.1 (p. 549, the uniformly random `n`-qubit Pauli product is a private quantum channel for all of `H_{2^n}` with output `I / 2^n`; its proof remarks that this holds for a qubit "no matter if it is entangled with other qubits"), Lemma 4.4 (p. 550, proved in Appendix A, pp. 552–553: hiding all unentangled `n`-qubit states forces off-diagonal basis units `|x⟩⟨y|` with `x ≠ y` to map to `0`), Theorem 5.1 (p. 550, `2n ≤ H(p)` without ancilla), Theorem 5.2 (p. 551, Bell-basis reduction from unentangled `n`-qubit states to `4^n` orthogonal basis states), Theorem 5.3 (p. 551, `log |S| ≤ H(p)` for orthogonal basis states with arbitrary ancilla `ρ_a`), and Corollaries 5.4 and 5.5 (p. 551, `2n ≤ H(p)` and `4^n ≤ N` for unentangled and general `n`-qubit pure states with arbitrary ancilla, formalized in [KeyLowerBound.lean](../CslibFrontier/Crypto/Protocols/Quantum/KeyLowerBound.lean)).
Definition 3.1 quantifies over pure plaintext states; [OneTimePad.lean](../CslibFrontier/Crypto/Protocols/Quantum/OneTimePad.lean) states secrecy for every density matrix, which follows by linearity, while [KeyLowerBound.lean](../CslibFrontier/Crypto/Protocols/Quantum/KeyLowerBound.lean) proves the lower bounds on pure states (and unentangled pure states) directly as in Definition 3.1.
The arXiv preprint quant-ph/0003101v1 (SHA-256 `af0b3211689e8f4a9d828fad63fcd6b7bbd388b7f21c34bc7e2a9fdfc5f14cbd`), *Private Quantum Channels and the Cost of Randomizing Quantum Information*, lists only Mosca, Tapp and de Wolf; locators follow the FOCS version.

<a id="amelootnevenvandenbussche2011"></a>
## amelootnevenvandenbussche2011

Tom J. Ameloot, Frank Neven, and Jan Van den Bussche.
"Relational Transducers for Declarative Networking."
*Proceedings of the 30th ACM SIGMOD-SIGACT-SIGART Symposium on Principles of Database Systems (PODS 2011)*, 283–292, 2011 (extended journal version in *Journal of the ACM* 60(2), Article 15, 2013, https://doi.org/10.1145/2450142.2450151). https://doi.org/10.1145/1989284.1989321 ; open preprint arXiv:1012.2858v1 (13 December 2010), https://arxiv.org/pdf/1012.2858 . Checked in arXiv:1012.2858v1 (12 PDF pp., SHA-256 `f6b994171ee9524c703c44ba70d6de9d65b64cf4f3787a1964f28c94925fd564`) on 2026-11-22 UTC: Section 2.1 (p. 3: cumulative inflationary `out` relations of relational transducers), Section 3 (pp. 3–4: transducer networks `(N, P)`, asynchronous configuration runs, `out(rho)` union over transitions, eventual delivery, and `N` implementing `Q`), Section 4 (pp. 4–6: delivery-preserving runs, horizontal partitions `H`, coordination-free executions `CF(N, H)`, and Example 2 on p. 5 showing single-node networks `|V| = 1` are trivially coordination-free for every query), Section 5 (pp. 6–8: oblivious transducers ignoring `All` and `Id`, Example 9 on p. 7 for disjunctive nonemptiness of `A` or `B`, Example 10 on p. 7 showing emptiness requires `Id` and `All`, and Proposition 11 on pp. 7–8), and Section 6 (p. 8: Theorem 12 proving `Q` is definable by a coordination-free transducer network on all networks iff `Q` is monotone via a two-node `{u, v}` isolated-prefix horizontal-partition argument, and Corollary 13).
Proceedings and journal pagination come from DOI metadata; internal page locators follow arXiv:1012.2858v1.
[CRDT/Monotonicity.lean](../CslibFrontier/Computability/Distributed/CRDT/Monotonicity.lean) formalizes a **semilattice irrevocable-emission and preorder-observation step** toward [#7502](https://github.com/cslib-community/cslib-frontier/issues/7502) (`semilatticeCoordinationFreeConsistent_iff_monotone`, `semilatticeObservableConsistent_iff_monotone`, `semilatticeCoordinationFreeConsistent_of_subsingleton`, and positive/negative CRDT query instantiations), adapting the two-replica split-brain argument of Theorem 12 to `SemilatticeSup S` states while leaving full relational transducer networks, network-awareness (`All`, `Id`), and `FO`+`while` / Dedalus characterizations (Sections 7–8, Theorems 6, 16, and 18) open in [#7502](https://github.com/cslib-community/cslib-frontier/issues/7502).

<a id="andersonmoorenagarajaozment07"></a>
## andersonmoorenagarajaozment07

Ross Anderson, Tyler Moore, Shishir Nagaraja and Andy Ozment.
"Incentives and Information Security."
Chapter 25 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 633–650. https://doi.org/10.1017/CBO9780511800481.027 ; author-hosted CUP page proofs (23 May 2007, 18 PDF pp., proof pp. 631–647 plus blank p. 18): https://www.cl.cam.ac.uk/archive/rja14/Papers/book-chapter-agt-1.pdf . In the published 2007 Cambridge University Press book, §25.2 ("Misaligned Incentives") and §25.2.1 ("Applications of Game Theory", printed p. 635; proof p. 633 / PDF p. 3 in the 23 May 2007 author-hosted page proofs, where proof p. 634 begins §25.2.2 "Network Effects and Deployment") provide a three-paragraph qualitative prose survey motivating the three Hirshleifer/Varian effort-aggregation models ([varian04](#varian04): total effort, weakest link, and best shot, together with opposite group-size comparative statics) and the Kunreuther–Heal interdependent security model ([kunreutherheal03](#kunreutherheal03), [healkunreuther07](#healkunreuther07): binary protection investment under peer contagion and tipping/cascading adoption).
Cited as chapter survey motivation by [Security/SystemReliability.lean](../CslibFrontier/GameTheory/Security/SystemReliability.lean) and [Security/Interdependent.lean](../CslibFrontier/GameTheory/Security/Interdependent.lean) (part of [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789)), whose formal definitions and theorems follow [varian04](#varian04), [kunreutherheal03](#kunreutherheal03), and [healkunreuther07](#healkunreuther07); §§25.2.2–25.5 (network effects, information asymmetries, vulnerability markets, and network topology models) remain open.

<a id="andoniindyk08"></a>
## andoniindyk08

Alexandr Andoni, Piotr Indyk.
“Near-Optimal Hashing Algorithms for Approximate Nearest Neighbor in High Dimensions.”
*Communications of the ACM* 51(1), 117–122, 2008. https://doi.org/10.1145/1327452.1327494 . Inspected in the author-hosted copy (https://people.csail.mit.edu/indyk/p117-andoni.pdf).
Section 2.4, "Strategy 1", p. 119, states: "It is shown in [25, 19] that the first strategy, with L′ = 3L, yields a solution to the randomized c-approximate R-near neighbor problem".
Here [25] is Indyk–Motwani, STOC 1998 ([indykmotwani98](#indykmotwani98)), and [19] is Gionis–Indyk–Motwani, "Similarity search in high dimensions via hashing", VLDB 1999.
The same page takes `L = Θ(n^ρ)` with `ρ = ln(1/P₁)/ln(1/P₂)`.
Cited as an exposition of the rule that stops the LSH query after `3L` candidates; the rule itself is credited to [25, 19].

<a id="angluin1980b"></a>
## angluin1980b

Dana Angluin.
"Local and Global Properties in Networks of Processors."
*Proceedings of the Twelfth Annual ACM Symposium on Theory of Computing (STOC 1980)*, 82–93, 1980. https://doi.org/10.1145/800141.804655 . The library's key is `Angluin1980b` (distinguished from `Angluin1980`).
Bibliographic metadata checked via DOI and search summaries on 2026-11-22 UTC; the conference proceedings PDF was not directly inspected, so internal theorem and page locators are not claimed.
[RingElection/Anonymous.lean](../CslibFrontier/Computability/Distributed/RingElection/Anonymous.lean) proves concrete oriented-ring rotational symmetry steps toward [#7200](https://github.com/cslib-community/cslib-frontier/issues/7200) (not the paper's general processor-network covering impossibility endpoints): synchronous-round rotational invariance (`AnonProtocol.not_electsUniqueLeader_sync_of_two_le`) and sequential FIFO wave uniformity (`AnonAsyncProtocol.exists_rotWave_trace_leaders_card_ne_one`) on `Fin n` for `2 ≤ n`, even when nodes know `n`.
[LocalGraph/Basic.lean](../CslibFrontier/Computability/Distributed/LocalGraph/Basic.lean) proves synchronous simple-graph `LOCAL` covering-map lift state invariance for both broadcast/multiset and port-numbered protocols (`BroadcastProtocol.state_eq_of_graphCovering`, `PortProtocol.state_eq_of_portCovering`, following the covering-map formulation verified against [Hirvonen and Suomela](#hirvonensuomela2020), §7.1–§7.3, Theorem 7.1, printed pp. 115–121) together with anonymous leader-election impossibility (`PortProtocol.not_electsUniqueLeader_of_portCovering`, `BroadcastProtocol.not_electsUniqueLeader_of_graphCovering`, instantiated on `C_6 -> C_3` via `BroadcastProtocol.not_electsUniqueLeader_cycleGraph_six` and `PortProtocol.not_electsUniqueLeader_cycleGraphPortNumbering_six`, bipartite double covers via `PortProtocol.not_electsUniqueLeader_bipartiteDoubleCover`, and symmetric `K_{3,3}` via `PortProtocol.not_electsUniqueLeader_k33PortNumbering`) and anonymous coloring impossibility (`PortProtocol.not_isProperColoring_of_portCovering`, `BroadcastProtocol.not_twoColoring_cycleGraph_six`, `PortProtocol.not_twoColoring_cycleGraphPortNumbering_six`, `PortProtocol.not_isProperColoring_bipartiteDoubleCover`, `PortProtocol.not_isProperColoring_k33PortNumbering`, steps toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505); Angluin's asynchronous port-automaton / edge-coloring processor-network model is not formalized).

<a id="anshelevichdktwr08"></a>
## anshelevichdktwr08

Elliot Anshelevich, Anirban Dasgupta, Jon Kleinberg, Éva Tardos, Tom Wexler and Tim Roughgarden.
*The Price of Stability for Network Design with Fair Cost Allocation*.
SIAM Journal on Computing 38(4), 1602–1623, 2008; preliminary version in FOCS 2004. https://doi.org/10.1137/070680096 . Bibliographic metadata only, as given in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, reference [1]; the DOI was taken from a search summary.
The paper's text was not inspected (the author-hosted copies tried returned 404), so no locator in it is cited.
The `H_k` price-of-stability theorem is attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, Theorem 2.1, and proved following [tardoswexler07](#tardoswexler07), §19.3.

<a id="apostolicobreslauergalil95"></a>
## apostolicobreslauergalil95

Alberto Apostolico, Dany Breslauer and Zvi Galil.
"Parallel Detection of All Palindromes in a String."
*Theoretical Computer Science* 141(1–2), 163–173, 1995. https://doi.org/10.1016/0304-3975(94)00083-U . Locators refer to the preliminary version, INRIA Research Report RR-2136, 1993, open copy https://inria.hal.science/inria-00074536 , checked on 2026-11-08 UTC.
Section 1 defines even and odd palindromes of radius `R` centered at a position and the maximal radii at all positions; the manual's center convention is translated from these definitions.
Section 1 also states that Manacher's algorithm computes the maximal radii at all positions in linear time.
The journal text was not inspected.

<a id="arrow1951welfare"></a>
## arrow1951welfare

Kenneth J. Arrow.
"An Extension of the Basic Theorems of Classical Welfare Economics."
*Proceedings of the Second Berkeley Symposium on Mathematical Statistics and Probability*, 507–532, University of California Press, Berkeley, 1951 (library key `Arrow1951Welfare`).
Bibliographic metadata only; the proceedings PDF was not directly inspected, so no internal theorem, lemma or page locators are claimed.
Cited alongside [arrowdebreu1954](#arrowdebreu1954) for price quasi-equilibria (`ExchangeMarket.IsPriceQuasiEquilibrium`), the Second Fundamental Theorem of Welfare Economics via hyperplane separation and lump-sum endowment redistribution (`ExchangeMarket.exists_priceQuasiEquilibrium_reendow_of_isParetoOptimal`, `ExchangeMarket.exists_isCompetitiveEquilibrium_reendow_of_isParetoOptimal`), and Arrow's zero-income corner counterexample (`arrowCorner` in [CoreWelfare.lean](../CslibFrontierTests/GameTheory/CoreWelfare.lean)) in [Welfare.lean](../CslibFrontier/GameTheory/Market/Welfare.lean), steps toward [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).

<a id="arrowdebreu1954"></a>
## arrowdebreu1954

Kenneth J. Arrow and Gerard Debreu.
"Existence of an Equilibrium for a Competitive Economy."
*Econometrica* 22(3), 265–290, 1954. https://doi.org/10.2307/1907353 . Bibliographic metadata only (library key `ArrowDebreu1954`); the journal PDF was not directly inspected, so internal theorem and page locators remain `unverified` in the results registry.
Cited for the Arrow–Debreu competitive equilibrium and Pareto optimality (First Welfare Theorem) foundations in [Basic.lean](../CslibFrontier/GameTheory/Market/Basic.lean).

<a id="aspvallplasstarjan79"></a>
## aspvallplasstarjan79

Bengt Aspvall, Michael F. Plass and Robert Endre Tarjan.
"A Linear-Time Algorithm for Testing the Truth of Certain Quantified Boolean Formulas."
*Information Processing Letters* 8(3), 121–123, 1979. https://doi.org/10.1016/0020-0190(79)90002-4 ; 1979 journal scan https://mathweb.ucsd.edu/~sbuss/CourseWeb/Math268_2007WS/2SAT.pdf . Checked against the 1979 journal scan during outside-fleet source review on 2026-11-23: printed p. 121 steps 1(i)–(ii) (two vertices per variable and contrapositive implication arcs) and printed p. 122 Theorem 1 and "Two-satisfiability algorithm" (SCC obstruction and reverse-topological assignment for existential 2-CNF).
In [TwoSAT.lean](../CslibFrontier/Algorithms/Lean/TwoSAT.lean) and [WordRAM/TwoSAT.lean](../CslibFrontier/Algorithms/WordRAM/TwoSAT.lean), Lean's Kosaraju SCC pass (`sccs`) and the certified standard-basis Word-RAM implementation and `512 * (n + φ.length + 1)` instruction bound are this formalization's own refinement; the paper uses Tarjan's SCC algorithm and also studies quantified 2-CNF.

<a id="attiyabarnoydolev1995"></a>
## attiyabarnoydolev1995

Hagit Attiya, Amotz Bar-Noy and Danny Dolev.
"Sharing Memory Robustly in Message-Passing Systems."
*Journal of the ACM* 42(1), 124–142, 1995. https://doi.org/10.1145/200836.200869 ; author PDF https://groups.csail.mit.edu/tds/papers/Attiya/JACM95.pdf . Inspected on 2026-11-22 UTC for §1 (p. 127, split-partition / message-suspension motivation for majority resilience), §2.1–2.2 (pp. 128–129, complete-network asynchronous crash-fault message passing and single-writer multi-reader atomic register specification), §3 (pp. 130–131, Lemma 3.1 majority-acknowledgment `communicate` primitive), §4 (pp. 131–134, Figure 2, Lemmas 4.3–4.6, Propositions 4.7–4.8 and Theorem 4.9 on p. 134: unbounded SWMR atomic register emulator tolerating `⌊(n - 1)/2⌋` processor failures using one `communicate` phase for writes, two `communicate` phases with read write-back for reads, `O(n)` messages and `O(1)` time per operation), and §7 (pp. 140–141, obtaining multi-writer multi-reader atomic registers by composition over the SWMR emulator; §§5–6 bounded-timestamp and dynamic-link emulators are not formalized).
In [ABD/Basic.lean](../CslibFrontier/Computability/Distributed/ABD/Basic.lean), [ABD/Protocol.lean](../CslibFrontier/Computability/Distributed/ABD/Protocol.lean) and [ABD/Impossibility.lean](../CslibFrontier/Computability/Distributed/ABD/Impossibility.lean), the asynchronous envelope model (`Fair F` delivering eventually to recipients outside `F`, without §3's ping-pong channel discipline or message/time cost bounds) and linearizability specification support the independent `(n - t)`-cardinality quorum envelope MWMR `(seq, writer)` specialization `abdProtocol` (after [lynchshvartsman1997](#lynchshvartsman1997), §4.1–4.2) together with Lean's quantified `2 ≤ n ≤ 2t` partition impossibility (`not_implementsAtomicRegister_of_partition`, `not_implementsAtomicRegister`, motivated by §1, p. 127) and `n ≤ 1 ∨ 2t < n` resilience characterization (`exists_linearizableRegister_iff`).

<a id="azuma67"></a>
## azuma67

Kazuoki Azuma.
"Weighted Sums of Certain Dependent Random Variables."
*Tôhoku Mathematical Journal* 19(3), 357–367, 1967. https://doi.org/10.2748/tmj/1178243286 ; J-STAGE publisher scan https://www.jstage.jst.go.jp/article/tmj1949/19/3/19_3_357/_pdf/-char/en . Checked against the publisher scan during outside-fleet source review on 2026-11-22: §1 property `[G]` on printed p. 357 and Remark 1 on printed p. 358 (bounded increments), and §2 proof of Lemma 2, display (2.4) on printed pp. 358–359 (iterated conditional exponential-moment bound for weighted martingale differences).
In [Azuma.lean](../CslibFrontier/Probability/Azuma.lean), `seqProcess_mul_exp_le` adapts display (2.4) to finite-horizon sequential `PMF` processes by deriving the conditional `[G]` factor with parameter `c k / 2` from the one-step centered Hoeffding bound ([hoeffding63](#hoeffding63), Theorem 2 eq. (2.6), eq. (2.18), and §4 eq. (4.16)) and nonpositive supermartingale drift, with the fixed-time tails as corollaries.

<a id="babai86"></a>
## babai86

László Babai.
"On Lovász' Lattice Reduction and the Nearest Lattice Point Problem."
*Combinatorica* 6(1), 1–13, 1986. https://doi.org/10.1007/BF02579403 . Not inspected (no open version was used); cited bibliographically as the origin of the nearest-plane algorithm.
The formalization follows [regev04](#regev04).

<a id="babaioffchuangfeldman07"></a>
## babaioffchuangfeldman07

Moshe Babaioff, John Chuang and Michal Feldman.
"Incentives in Peer-to-Peer Systems."
Chapter 23 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 593–612. https://doi.org/10.1017/CBO9780511800481.025 (chapter metadata checked against the Crossref record).
A university-hosted PDF of the book was consulted on 2026-11-08 for Exercise 23.6 (p. 611).
Its definition of a strong equilibrium (SE) excludes coalitions in which every member strictly gains, and is stated for utilities.
The library's `IsStrongEquilibrium` is that notion for costs, with the coalition required to be nonempty, which the exercise leaves implicit.
By contrast, the strong Nash equilibrium of [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, Definition 3.1 (`IsStrongNash`) also excludes deviations in which no member loses and some member gains.
The same weak-deviation definition appears in Chapter 1, §1.7.1 of the book (Tardos and Vazirani), which attributes the notion to Aumann (1974); Aumann's text was not consulted.

<a id="babaioffimmorlicakleinberg07"></a>
## babaioffimmorlicakleinberg07

Moshe Babaioff, Nicole Immorlica and Robert Kleinberg.
"Matroids, Secretary Problems, and Online Mechanisms."
*Proceedings of the Eighteenth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2007)*, SIAM, 2007, 434–443; author-hosted PDF https://www.cs.cornell.edu/~rdk/papers/matsec.pdf (SHA-256 `773528230854616a6b0c7cd720f16fe081f889cfcae595df8d93decc44ab6e2d`, 12 pp.).
Inspected in full on 2026-11-24 UTC against the author-hosted PDF: §2 (pp. 2–3, matroid secretary problem, Unknown Single-Value unit-demand domain, and the convention assuming distinct nonzero values / zero-value elements), §3.2 (p. 5, Threshold Price Algorithm and Theorem 3.2), §4 (p. 6, Price Sampling Algorithm, Claim 1, Claim 2, Theorem 4.1 `4d`-approximation on left-degree-`d` transversal matroids, and Theorem 4.2 truthful USV online mechanism), §5 (pp. 6–7, graphic matroids), and §6 (pp. 7–9, Remark on filtering `0`-weight elements and independent secretary copies on partition matroids, p. 9).
In [MatroidSecretary.lean](../CslibFrontier/Probability/OptimalStopping/MatroidSecretary.lean), `partitionSelect` and `exp_neg_one_mul_sum_le_expectedPartitionSecretary` formalize §6's partition-matroid `e`-competitive algorithm; `thresholdPriceRun` and `sum_le_mul_expectedThresholdPrice` formalize §3.2 Theorem 3.2 using the exact `Nat.clog 2 k + 1` exponent count (giving factor `32 * (⌈log₂ k⌉ + 1)` covering rank `k = 1`, with corollary `sum_le_sixtyFour_clog_mul_expectedThresholdPrice` giving `64 * ⌈log₂ k⌉` for `k ≥ 2`, where the paper writes `32 ⌈log₂ k⌉` by abbreviating the probability `1 / (⌈log₂ k⌉ + 1)` as `1 / log k`), filter out `0`-weight elements per §6 so zero-weight ties cannot block the global maximum when `sampleMax = 0`, and require a loopless finite matroid with `2 ≤ |α|` (since `s = ⌈1/2⌉ = 1` leaves an empty suffix at `n = 1`).
In [TransversalSecretary.lean](../CslibFrontier/Probability/OptimalStopping/TransversalSecretary.lean), `priceSamplingMatch` and `sum_le_four_mul_degree_mul_expectedPriceSampling` formalize §4 Theorem 4.1 (`4d`-approximation) using strict `<` pricing, well-behaved weights, `2 ≤ |L|`, and `Finset.exists_min_image` without requiring a linear order on `R`; `priceSamplingUSV_ir` and `priceSamplingUSV_truthful` formalize §4 Theorem 4.2 ex-post IR and DSIC truthfulness without any degree restriction.
§§5–6 (graphic matroids and Karger truncation reduction) are left open.

<a id="baloghbekesidosaepsteinlevin18"></a>
## baloghbekesidosaepsteinlevin18

János Balogh, József Békési, György Dósa, Leah Epstein and Asaf Levin.
*A new lower bound for classic online bin packing*. arXiv:1807.05554v1, 2018. https://arxiv.org/abs/1807.05554 ; published in *Algorithmica* 83(7), 2047–2062, 2021, https://doi.org/10.1007/s00453-021-00818-7 (bibliographic data from the Crossref record; the locators follow arXiv v1).
Worker w156-ff read the arXiv version on 2026-11-08 UTC.
Section 1 reports that Yao's first lower bound on the asymptotic competitive ratio uses at most three types of items, `1/7 + ε`, `1/3 + ε` and `1/2 + ε`; it does not state the value of that bound.
It also reports the later bounds of Brown and Liang (`1.53635`), van Vliet (`1.5401474`) and Balogh, Békési and Galambos (`248/161`).
The library's [OnlineLowerBound](../CslibFrontier/Algorithms/Lean/BinPacking/OnlineLowerBound.lean) module takes its item types from this report.

<a id="banaszczyk1993"></a>
## banaszczyk1993

Wojciech Banaszczyk.
"New Bounds in Some Transference Theorems in the Geometry of Numbers."
*Mathematische Annalen* 296(4), 625–635, 1993. https://doi.org/10.1007/BF01445125 . Verified locator for the shifted Gaussian tail bound: Lemma 1.5(ii), printed p. 630 (with the centered case in Lemma 1.5(i) and mass-scaling in Lemma 1.4).
The formalized statements in `Gaussian.OffCenterTail` also cross-reference [micciancioregev2007](#micciancioregev2007) Lemma 2.10 and Regev (JACM 2009, `Regev2009` in `references.bib`) Lemmas 2.4–2.5.

<a id="barak-steurer16"></a>
## barak-steurer16

Boaz Barak and David Steurer.
*Proofs, beliefs, and algorithms through the lens of sum-of-squares*.
Lecture notes, 2016, https://www.sumofsquares.org/ . On 2026-11-08 UTC worker w96-sos consulted these author-hosted lectures: "Mathematical definitions" (https://www.sumofsquares.org/public/lec01-2_definitions.pdf), for Theorem 19, the duality of sum-of-squares certificates and pseudo-distributions; "The sos algorithm over general domains" (https://www.sumofsquares.org/public/lec-definitions-general.pdf), for Definition 1 (sos proofs), the remark after Theorem 2 (degree-`d` sos refutations), Definitions 5 and 7 (pseudo-distributions and the constraints they satisfy) and Theorem 8; and "Higher-degree integrality gaps" (https://www.sumofsquares.org/public/lec03-2_lowerbounds_csp.pdf), for Theorem 2, Lemmas 7 and 9, and Lemma 24 (Grigoriev's bound for Tseitin tautologies on vertex expanders).
The sum-of-squares modules cite these locators.
The notes are a living document, and the numbering may change.

<a id="barnumsaksszegedy03"></a>
## barnumsaksszegedy03

Howard Barnum, Michael E. Saks and Márió Szegedy.
"Quantum query complexity and semi-definite programming."
*Proceedings of the 18th IEEE Annual Conference on Computational Complexity (CCC 2003)*, 179–193, 2003. https://doi.org/10.1109/CCC.2003.1214419 . Bibliographic metadata checked through search records on 2026-11-11; the full CCC 2003 text was not inspected directly.
Cited via [Høyer, Lee and Špalek 2007](#hoyerleespalek07) (Section 1.1, Definition 1 and Theorem 1) for the nonnegative spectral adversary `ADV(f) = max_{Γ ≥ 0} ‖Γ‖ / max_i ‖Γ ∘ D_i‖`.

<a id="barrett26"></a>
## barrett26

Clark Barrett, Swarat Chaudhuri, Fabrizio Montesi, Jim Grundy, Pushmeet Kohli, Leonardo de Moura, Alexandre Rademaker and Sorrachai Yingchareonthawornchai.
*CSLib: The Lean Computer Science Library*. arXiv:2602.04846v1, 2026. https://doi.org/10.48550/arXiv.2602.04846 . Author/title/version metadata checked against https://arxiv.org/abs/2602.04846 on 2026-11-02 UTC.

<a id="basupollackroy06"></a>
## basupollackroy06

Saugata Basu, Richard Pollack and Marie-Françoise Roy.
*Algorithms in Real Algebraic Geometry*, 2nd edition.
Algorithms and Computation in Mathematics 10, Springer, 2006. https://doi.org/10.1007/3-540-33099-2 ; copy inspected in outside-fleet review ([#7735](https://github.com/cslib-community/cslib-frontier/pull/7735#pullrequestreview-6016516231)): https://www.academia.edu/2789226/Algorithms_in_real_algebraic_geometry . Mapped specifically to the Sturm root-counting ingredient: Chapter 2, Theorem 2.50 (printed p. 52) counts distinct roots in an open interval over a real closed field, whereas [`Sturm.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/Sturm.lean) works over `ℝ` with finite real endpoints and counts distinct roots in `(a, b]` via local constancy of `sturmReducedVariations p x + #{r ≤ x}` (`Polynomial.sturmReducedVariations_sub_eq_card_roots_Ioc`, `Polynomial.sturmVariations_sub_eq_card_roots_Ioc_of_gcd_eval_ne_zero`, `Polynomial.sturmVariations_sub_eq_card_roots_Ioc`).
Section 10.2, Algorithm 10.4 (printed pp. 373–374)—which works over integer coefficients, uses Bernstein coefficient variation, and returns open rational intervals together with singleton rational roots—is related work, not the formalized algorithm.
The executable `List ℚ` Sturm-bisection isolators (`isolateRoots`, which may return touching intervals, and `isolateRootsTotal` in [`Isolation.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/Isolation.lean) and [`TotalIsolation.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/TotalIsolation.lean), which refines boundaries on squarefree input to strictly separated pairwise-disjoint closed intervals `J₁.upper < J₂.lower` in strictly monotone bijection with `{x : ℝ // aeval x p = 0}` and satisfies dyadic endpoint bit bounds under `HasCoeffBitBound B cs` via [`BitBounds.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/BitBounds.lean)), the Sylvester/Hadamard rational Sturm bit-bound ([`SturmBitBounds.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/SturmBitBounds.lean)), and the unconditional multi-tape Turing-machine polynomial-time certification ([`RootIsolation.lean`](../CslibFrontier/Computability/Complexity/RealAlgebraic/RootIsolation.lean), `isolateRoots_computableInPolyTime`, `isolateRootsTotal_computableInPolyTime`) are the library's own construction.

<a id="baumbmrs23eprint"></a>
## baumbmrs23eprint

Carsten Baum, Lennart Braun, Cyprien Delpech de Saint Guilhem, Michael Klooß, Emmanuela Orsini, Lawrence Roy and Peter Scholl.
*Publicly Verifiable Zero-Knowledge and Post-Quantum Signatures From VOLE-in-the-Head*, Cryptology ePrint Archive, Paper 2023/996 (full version of CRYPTO 2023, `BaumBMRS2023Eprint`). https://eprint.iacr.org/2023/996 . Checked on 2026-11-24 against the IACR ePrint 2023/996 full version: Appendix B.1 ("ZK from Generalized sVOLE for Arbitrary Degree-d Relations", printed p. 46) sketches how to generalize sVOLE polynomial checks over a vector of degree-`d` constraints using `(d - 1)` random VOLE masks and independent challenges `χ_i ∈ F_p` (both independent weights in `toOuterMeasure_qsHomogLinearBatch_le` / `toOuterMeasure_qsMaskedCheckValue_le` and single-scalar powers `χ^i` in `toOuterMeasure_qsHomogScalarBatch_le` are proved in [HigherDegreeCheck.lean](../CslibFrontier/Crypto/Protocols/VOLE/HigherDegreeCheck.lean)), and Section 4, Lemma 4 ("FS ◦ O2C", printed pp. 19–20) proves straight-line NIZK knowledge extraction across `Q_Verify` calls with per-call VC extraction loss and `µ · (Q_FS + Q_Verify) · κ`.
[ROExtractor.lean](../CslibFrontier/Crypto/Protocols/VOLE/ROExtractor.lean) specializes that straight-line RO construction to a single repetition (`µ = 1`) over flat `2 ^ d`-leaf RO commitments, and [ROBridge.lean](../CslibFrontier/Crypto/Protocols/AnonymousToken/ROBridge.lean) composes it with `AnonymousToken.Basic` and `AnonymousToken.Conservation`.
Cited in [HigherDegreeCheck.lean](../CslibFrontier/Crypto/Protocols/VOLE/HigherDegreeCheck.lean), [ROExtractor.lean](../CslibFrontier/Crypto/Protocols/VOLE/ROExtractor.lean), and [ROBridge.lean](../CslibFrontier/Crypto/Protocols/AnonymousToken/ROBridge.lean); the CRYPTO 2023 LNCS proceedings entry (`BaumBMRS2023`) lists pp. 581–615 without Appendix B.1 (the LNCS volume PDF was not separately opened).

<a id="baumetal26faest"></a>
## baumetal26faest

Carsten Baum, Ward Beullens, Lennart Braun, Cyprien Delpech de Saint Guilhem, Michael Klooß, Christian Majenz, Shibam Mukherjee, Emmanuela Orsini, Sebastian Ramacher, Christian Rechberger, Lawrence Roy and Peter Scholl.
*FAEST v3: Algorithm Specifications*, Version 3.0, September 1, 2026 (bibliography key `BaumEtAl2026FAEST`). https://faest.info/faest-spec-v3.0.pdf . Checked against that PDF on 2026-11-22 (SHA-256 `a880ae59c1f35e0a54a83316de85e2b70bf3ca80f1b4b593340008bc4ef9107b`): Section 10.6, Lemma 10.26 (printed pp. 97–98) specifies the affine-line extractor `E_{KOS,S}(H, ũ, ṽ)` over a finite opening set `S` and states the relaxed cubic bound `(|S|^3 / 6 + |S|^2 / 2) ε` after deriving the sharper binomial sum `(choose |S| 2 + choose |S| 3) ε` from the two bad events (same-challenge distinct-response hash collisions and three distinct-challenge non-collinear openings with collinear hashed images), and Corollary 10.27 (printed pp. 98–99) specializes to a partial-function response graph `S_t` where Bad event 1 is impossible (stating `|S_t|^3 / 6 · ε_v` from the proof's `choose |S_t| 3 · ε_v`).
`CslibFrontier.Crypto.Protocols.VOLE.KOSExtractor` formalizes these abstract `IsUniversalHash` steps: the executable total extractor `kosExtract`, the affine collinearity defect `kosAffineDefect`, the explicit computable failure witness `kosFailureWitness`, and the exact list-position binomial bounds `ε * (responses.length.choose 3)` on response graphs and `ε * (responses.length.choose 2 + responses.length.choose 3)` on arbitrary opening lists (matching `|S|` on duplicate-free enumerations `responses.Nodup`).
Concrete `VOLEHash` universality (Lemma 4.6), BAVC reconstruction ([#5302](https://github.com/cslib-community/cslib-frontier/issues/5302)), Lemma 10.19's response-graph construction, QuickSilver v3, and ROM/QROM signature reductions remain open under [#4987](https://github.com/cslib-community/cslib-frontier/issues/4987).
Re-checked on 2026-11-25 against that same specification for `CslibFrontier.Crypto.Protocols.AnonymousToken.CRTHazard` and `CslibFrontier.Crypto.Protocols.AnonymousToken.CRTDecoupling`: Section 3.1 (Tables 3.1–3.2, printed pp. 13–15, e.g. `nmult = 312` for `FAEST-128s`/`FAEST-128f` and `nmask = dzk + 3`), Section 3.3 (p. 18, `H5 : {0, 1}^128 × {0, 1}^32 × {0, 1}^λ → {0, 1}^nmask`), Section 6 (pp. 35–43, Figures 6.1–6.3, `FAEST.VOLECommit` / `FAEST.VOLEReconstruct` CRT-based masks, `H5(iv, e, L0e)` / `H5(iv, e, L1e)` queries, and `cmult` gate correction bits), and Section 10.10 (Theorem 10.42, Games `G6`–`G11`, pp. 115–121, switching `VOLECommit` to uniform `u`, `ci`, `cmult` with programmed/checked `H5` queries).
Those two modules provide background-motivated finite query-bounded `ZMod 2` parity/`H5` and CRT-decoupling formalizations over abstract matrix and commitment interfaces rather than the concrete AES/Rijndael QuickSilver circuits or asymptotic PPT proofs of FAEST v3 ([#7068](https://github.com/cslib-community/cslib-frontier/issues/7068)).

<a id="baumetal26faester"></a>
## baumetal26faester

Carsten Baum, Ward Beullens, Lennart Braun, Cyprien Delpech de Saint Guilhem, Michael Klooß, Christian Majenz, Shibam Mukherjee, Emmanuela Orsini, Sebastian Ramacher, Christian Rechberger, Lawrence Roy and Peter Scholl.
*Shorter, Tighter, FAESTer: Optimizations and Improved (QROM) Analysis for VOLE-in-the-Head Signatures*, Cryptology ePrint Archive, Paper 2026/164 (`BaumEtAl2026FAESTer`). https://eprint.iacr.org/2026/164 . Checked on 2026-11-24 against the IACR ePrint 2026/164 preprint (https://eprint.iacr.org/2026/164): Section 3, Definition 27 (printed pp. 17–18, "Almost-Injective PRG" assumption for the `Simple` AES-PRG leaf commitment variant `(r, PRG_{2λ}(r))`, noting that multiple seeds may otherwise map to the same commitment and defeat preimage extraction), and Section 3.3, Lemma 32 (printed pp. 25–26, "Extractable Binding of VOLE Commitment", together with Lemma 33 "Random oracle graph game" on p. 26).
Cited in [PRGLeafSeparation.lean](../CslibFrontier/Crypto/Protocols/VOLE/PRGLeafSeparation.lean) for the PRG leaf separation showing that `leaf_hash::aes_ctr` allows zero-query valid proofs (defeating statement- and proof-less leaf-query-log extractors `extLog : LeafTrace → Option Wit` against disjoint-witness statements with probability `1`, excluding the `(tr, prf)` extractor shape of `extractWitnessFromTrace`), that colliding PRG commitments (`hComEq`, `hdCorrEq` across disjoint-witness statements with injective `encWit`) defeat every deterministic preimage-table seed extractor `extPre` with probability `1`, and that colliding proofs break unbounded proof-only extractors omitting `stmt` with probability at least `1 / |Chal|` for arbitrary `d : ℕ` (`d ≥ 1` opening `2 ^ d - 1 ≥ 1` leaves; while full Definition 27 / Lemma 32 post-challenge equivocation for unbounded extractors that also receive `stmt` remains open).

<a id="bax93"></a>
## bax93

Eric T. Bax.
“Inclusion and Exclusion Algorithm for the Hamiltonian Path Problem.”
*Information Processing Letters* 47(4), 203–207, 1993. https://doi.org/10.1016/0020-0190(93)90033-6 . Bibliographic metadata checked via DOI/DBLP on 2026-11-11; the article body (paywalled) was not inspected, so the manual cites it for the inclusion–exclusion walk-counting algorithm without a theorem or page locator.

<a id="bbhr18"></a>
## bbhr18

Eli Ben-Sasson, Iddo Bentov, Yinon Horesh and Michael Riabzev.
"Fast Reed–Solomon Interactive Oracle Proofs of Proximity."
*45th International Colloquium on Automata, Languages, and Programming (ICALP 2018)*, LIPIcs 107, 14:1–14:17, Schloss Dagstuhl, 2018. https://doi.org/10.4230/LIPIcs.ICALP.2018.14 ; full/long version ECCC TR17-134.
The library's key is `BenSassonBentovHoreshRiabzev2018`.
Bibliographic metadata checked against `references.bib`.
Multi-round smooth `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2` and 2-to-1 coset folding over arbitrary fields of characteristic `≠ 2` (generalizing the fixed localization parameter `η` / `2 ^ η`-to-1 folding of the long version ECCC TR17-134, Remark 3.1, p. 13, to round-dependent arities `l⁽ⁱ⁾` as in [bciks20](#bciks20), Section 8.2, printed pp. 36–38 (fibers in Eq. (8.1), the interpolation map defined right after it and evaluated in Eq. (8.2), and the affine batching combination in Eq. (8.3), all on printed p. 37), and using the final-round anchor convention of printed p. 38 that interpolates the degree-`< kFinal` final codeword from the first `kFinal` entries of `π_m`), the `PublicCoinIOP`s `friSmoothIOP` and `friIOP` (`friIOP_eq_friSmoothIOP` via `FRIParams.toSmooth`), perfect completeness, and query accounting—exact committed-proof-oracle opening list length `kFinal + q * (aritySum + m + 2)` (`FRISmoothParams.proofOracleQueries`, specializing to `kFinal + q * (3 * m + 2)` in `FRIParams.proofOracleQueries`, via `PublicCoinIOP.queries`) plus a direct input-word read budget of `q` scheduled input positions, with multiplicity (`inputWordReads`, listed by `friSmoothInputQueries` / `friInputQueries` and certified sufficient by `friSmoothDecide_congr_inputQueries` / `friDecide_congr_inputQueries`; a schedule / upper-bound budget because `decide` can reject on answer length before input access, repetitions short-circuit on earlier failures, and query challenges may repeat indices), for a combined word-query budget of `kFinal + q * (aritySum + m + 3)` (`kFinal + q * (3 * m + 3)` for 2-to-1, `totalWordQueries`, aligned with counting both input-word and prover-table queries on pp. 14:3–14:4)—are formalized in [FRI/Folding.lean](../CslibFrontier/Crypto/Protocols/FRI/Folding.lean) and [FRI/Protocol.lean](../CslibFrontier/Crypto/Protocols/FRI/Protocol.lean).
[FRI/Soundness.lean](../CslibFrontier/Crypto/Protocols/FRI/Soundness.lean) establishes the unconditional round-by-round invariant (`friIOP_rbrSound`) and query-round escape bound (`friQueryRound_escape_le`), together with conditional commit-round escape and two-channel BCS random-oracle compilation steps ([bcs16](#bcs16)) parameterized by `WeightedLineGapBound` / `UniqueLineGapHypothesis`; [FRI/JohnsonSoundness.lean](../CslibFrontier/Crypto/Protocols/FRI/JohnsonSoundness.lean) discharges those per-round line-gap hypotheses in the unique-decoding regime and up to the Johnson and `η`-gap bounds (`friJohnsonCommitBound`, `friJohnsonEtaCommitBound`) for this single-word FRI model (paired with [bciks20](#bciks20)).

<a id="bcgl92"></a>
## bcgl92

Shai Ben-David, Benny Chor, Oded Goldreich and Michael Luby.
*On the Theory of Average Case Complexity*.
Journal of Computer and System Sciences 44(2), 193–219, 1992; preliminary version in STOC 1989. https://doi.org/10.1016/0022-0000(92)90019-F . Bibliographic metadata checked against the Crossref record on 2026-11-08.
The primary text was not inspected, and no theorem number is claimed.
The manual attributes to this paper only the implication `DistNP ⊆ AvgP ⇒ NE = E`, as reported by [bm15](#bm15), §5.

<a id="bciks20"></a>
## bciks20

Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty and Shubhangi Saraf.
"Proximity Gaps for Reed–Solomon Codes."
*Journal of the ACM* 70(5), 31:1–31:57, 2023; accepted author/NSF manuscript https://par.nsf.gov/servlets/purl/10467091 ; preliminary version FOCS 2020; IACR Cryptology ePrint Archive 2020/654, https://eprint.iacr.org/2020/654 . https://doi.org/10.1145/3614423 . The library's key is `BenSassonCarmonIshaiKoppartySaraf2020`.
Bibliographic metadata checked against `references.bib`; section and theorem locators follow the accepted *Journal of the ACM* (2023) manuscript (where Theorem 1.2 treats affine-space proximity gaps across both the unique-decoding and Johnson-bound regimes, Theorem 1.4 treats line correlated agreement across both regimes, Theorem 1.5 treats parameterized curves, Theorem 1.6 on printed p. 6 treats affine-space correlated agreement, Theorem 4.1 treats unique-decoding lines, Theorem 5.1 on p. 17 treats unweighted Johnson-bound lines, Lemma 6.3 and Section 6.3 on printed pp. 29–31 prove the line-to-affine reduction, Theorems 6.1–6.2 treat unique-decoding and Johnson-bound degree-`r` curves, Theorem 7.1 treats weighted correlated agreement on curves, Version I, in the `α > √ρ` range, Theorem 7.2 treats weighted correlated agreement on lines/curves, and Theorems 7.3–7.4 on printed p. 32 with proof in Section 7.3 on printed p. 34 treat weighted correlated agreement over affine spaces; by contrast, Theorem 7.2 of the July 2020 ePrint 2020/654 author version concerns FRI soundness).
Formalized across:

- [Unique.lean](../CslibFrontier/Foundations/Data/Code/ProximityGap/Unique.lean): unique-decoding correlated agreement and proximity gaps for affine lines and degree-`d` parameterized curves (unique-decoding cases of Theorems 1.2, 1.4, and 1.5, together with Theorems 4.1 and 6.1), including the unique maximal shared agreement set and unique codewords clauses on printed pp. 5–6 and Remark 4.1 on p. 13 (`exists_uniqueMaximal_correlatedAgreement_unique`, `exists_uniqueMaximal_correlatedAgreement_curve_unique`, derived via the generic uniqueness step `exists_uniqueMaximal_correlatedAgreement_of_exists` whose premise supplies a correlated-agreement witness);
- [Johnson.lean](../CslibFrontier/Foundations/Data/Code/ProximityGap/Johnson.lean): explicit-parameter Guruswami–Sudan correlated-agreement steps for lines and integer-weighted degree-`r` curves over arbitrary fields of arbitrary characteristic (steps toward Theorems 5.1, 6.2 and 7.2) together with original explicit-constant line proximity-gap variants (`1800 * (m + 1)^6 * n^2 / (ρ * |F|)` and `115200 * n^2 / (ρ * η^6 * |F|)`) in the setting of Theorem 1.4 (not uniformly smaller at small `m` than the displayed `(m + 1/2)^7 / (3 * ρ^(3/2))` finite constant of Theorem 5.1, p. 17 in the accepted NSF/JACM manuscript);
- [Curve.lean](../CslibFrontier/Foundations/Data/Code/ProximityGap/Curve.lean): sharp unique-decoding `ℕ`/`ℚ`-weighted correlated agreement (a unique-decoding specialization and signed-weight extension of Section 7 / Theorem 7.1, where source Theorem 7.1 treats weighted curves, Version I, in the `α > √ρ` range), original explicit-constant Johnson-bound curve proximity-gap variants and `ℚ`-weighted curve/line steps (toward Theorems 1.5, 6.2, 7.1 and 7.2), pointwise close-or-sparse affine-space dichotomy lifts (`proximityGap_affine_of_line` and weighted unique-decoding `*_affine_unique_sharp` instantiations), the generic Lemma 6.3 + Section 6.3 / Section 7.3 line-to-affine correlated-agreement reduction (`exists_weighted_correlatedAgreement_affine_of_divergence` and `exists_weighted_correlatedAgreement_affine_of_line` on printed pp. 29–31 and p. 34, repairing printed p. 34's zero-weight `D' = D'_i` claim by intersecting candidate agreement sets with `supp W`; the generic linear-code lemma also avoids the unique extension used on printed p. 31, which for Reed–Solomon codes under Theorem 7.4 is available because `α > ρ`), exact eq. (1.2) (`|ι| * |F| ^ ℓ < |F| * #T`) unique-decoding affine-space correlated agreement with Theorem 1.6's uniqueness and maximality clause (`exists_uniqueMaximal_correlatedAgreement_affine_unique`, printed p. 6 and pp. 28–31) and its exact-`|F|` dichotomy (`proximityGap_affine_unique`, Theorem 1.2 eq. (1.2)), and list-premise-free unweighted, `ℕ`-weighted, and `ℚ`-weighted Johnson-bound affine correlated agreement and exact-`|F|` dichotomies in both explicit-parameter `(m, D)` form and explicit-constant closed form (`1800 * [M *] (m + 1)^6 * n^2 / (ρ * |F|)` and `115200 * [M *] n^2 / (ρ * η^6 * |F|)`) in the setting of Theorem 1.2, Theorem 1.6 on printed p. 6, and Theorems 7.3–7.4 on printed p. 32.
  These Johnson-bound formulas are original finite bounds: eq. (1.3) uses `min(η, √ρ / 20)` in its denominator while the Lean formulas use the gap `η` directly, so a density sufficient for eq. (1.3) / Theorem 1.6 (or Theorem 7.4) can fall below the Lean cutoff; the exact cited endpoints, the paper's displayed finite constants `(m + 1/2)^7 / (3 * ρ^(3/2))`, `(2 * m + 1) * (M * n + 1) / √ρ`, and `ρ^2 / (2 * η)^7`, and the exact displayed finite constants of Lemma 8.2 and Theorem 8.3 in Section 8 remain tracked in #5968;
- [FRI/Folding.lean](../CslibFrontier/Crypto/Protocols/FRI/Folding.lean), [FRI/Protocol.lean](../CslibFrontier/Crypto/Protocols/FRI/Protocol.lean), [FRI/Soundness.lean](../CslibFrontier/Crypto/Protocols/FRI/Soundness.lean) and [FRI/JohnsonSoundness.lean](../CslibFrontier/Crypto/Protocols/FRI/JohnsonSoundness.lean): single-word smooth `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2` (`FRISmoothParams`, `foldFiberComp`, `foldFiber`, `friSmoothIOP`, `sum_arity_sub_one_mul_domainSize`, crediting Section 8.2 on printed pp. 36–38 for round-dependent arities, Eq. (8.1) on printed p. 37 for the fibers, the interpolation map defined immediately after it for the coefficient vector `foldFiberComp`, and Eq. (8.2) for its evaluation `foldFiber`, generalizing the fixed localization parameter of [bbhr18](#bbhr18) ECCC TR17-134 Remark 3.1 p. 13, and using the final-round Lagrange anchor convention of printed p. 38 on the first `kFinal` entries of `π_m`) and 2-to-1 (`FRIParams.toSmooth`, `friIOP_eq_friSmoothIOP`) FRI coset folding and protocol completeness (with exact committed-opening length `proofOracleQueries` and `q` scheduled input positions, with multiplicity, as the `inputWordReads` / `totalWordQueries` budget), together with the smooth FRI IOP round-by-round invariant and query-round escape bound (`friSmoothIOP_rbrSound`, with the binary statements as corollaries via `friDoomed_iff_friSmoothDoomed` and `friCommitGame_eq_friSmoothCommitGame`), degree-`(l⁽ⁱ⁾ - 1)` curve proximity-gap contracts for each folding round (`WeightedCurveGapPerRound`, `WeightedCurveGapBound`, `UniqueCurveGapHypothesis`, specializing to the line contracts at `l⁽ⁱ⁾ = 2` via `weightedLineGapPerRound_iff_weightedCurveGapPerRound`), conditional commit-phase escape / summed interactive IOP / BCS random-oracle compilation steps, and unconditional derivation of the per-round curve budgets in the unique-decoding regime (`friSmoothUniqueCommitError`) and up to the Johnson and `η`-gap bounds (`friSmoothJohnsonRoundBound`, `friSmoothJohnsonCommitBound`, `friSmoothJohnsonEtaCommitBound`, `weightedCurveGapBound_of_johnson_eta`, `friSmoothJohnsonCommitError`, whose per-round budgets telescope to a `(1 - 1 / 2 ^ totalLog)` factor independent of the arities; binary specializations `friJohnsonRoundBound`, `friJohnsonCommitBound`, `friJohnsonEtaCommitBound`, `weightedLineGapBound_of_johnson_eta`, `friJohnsonCommitError`) in [FRI/JohnsonSoundness.lean](../CslibFrontier/Crypto/Protocols/FRI/JohnsonSoundness.lean).
  Theorem 8.3 of the accepted JACM manuscript treats batched FRI with correlated agreement of the initial functions and its stated quantitative error (and is an IOP theorem, not a BCS random-oracle theorem): batched initial-function correlated agreement is formalized in [FRI/BatchProtocol.lean](../CslibFrontier/Crypto/Protocols/FRI/BatchProtocol.lean), [FRI/BatchSoundness.lean](../CslibFrontier/Crypto/Protocols/FRI/BatchSoundness.lean) and [FRI/BatchJohnsonSoundness.lean](../CslibFrontier/Crypto/Protocols/FRI/BatchJohnsonSoundness.lean) (with exact quantitative Lemma 8.2 / Theorem 8.3 displayed constants still tracked in #5968), while the non-interactive random-oracle bounds follow by composing the FRI IOP escape bounds with the two-channel BCS compiler ([bcs16](#bcs16));
- [FRI/BatchProtocol.lean](../CslibFrontier/Crypto/Protocols/FRI/BatchProtocol.lean): the `(m + 2)`-round `PublicCoinIOP` formulation of Section 8.2's affine/linear batched smooth `l⁽ⁱ⁾ = 2 ^ stepLog i ≥ 2` (`friSmoothBatchIOP`) and 2-to-1 (`friBatchIOP`, with `friBatchIOP_eq_friSmoothBatchIOP`) FRI protocols (printed pp. 36–40, Eq. (8.1) for the fibers, the interpolation map defined right after it, Eq. (8.2) for its evaluation and Eq. (8.3) for the affine batching combination, all on p. 37, batched QUERY steps (1)–(4) on p. 38, and the final-round Lagrange anchor convention of p. 38 on the first `kFinal` entries of `π_m`) delegating rounds `1 .. m + 1` to `FRI/Protocol.lean`, together with perfect IOP / deterministic BCS / two-channel BCS random-oracle completeness, the exact committed-oracle opening list length (`kFinal + q * (aritySum + m + 2)`, specializing to `kFinal + q * (3 * m + 2)`) and `q` scheduled input positions, with multiplicity, as the `(t + 1) * q` direct-read and `kFinal + q * (aritySum + m + t + 3)` (`kFinal + q * (3 * m + t + 3)` for 2-to-1) combined word-query budgets (`friSmoothBatchDecide_congr_inputQueries`, `friBatchDecide_congr_inputQueries`; budgets because `decide` can reject on answer length before input access, repetitions short-circuit, and query challenges may repeat), and the shared code-parameterized completeness relation and integer / real-density tuple correlated-agreement languages (`friBatchCompletenessRel`, `friBatchProximityLang`, `friBatchCorrAgreeLang`) with unified ceiling and floor real-to-integer threshold bridges (`friBatchCeilThreshold_bounds`, `friBatchFloorThreshold_bounds`, specializing to `batchCeilThreshold_bounds`, `batchFloorThreshold_bounds`) for Lemma 8.2 and Theorem 8.3;
- [FRI/BatchSoundness.lean](../CslibFrontier/Crypto/Protocols/FRI/BatchSoundness.lean): unconditional round-by-round soundness (`friSmoothBatchIOP_rbrSound` and its binary corollary `friBatchIOP_rbrSound`, proving initialization on false tuples, preservation on good transitions, and terminal rejection) and marginal challenge / tail-escape reductions for `friSmoothBatchIOP` and `friBatchIOP` delegating rounds `1 .. m + 1` to `FRI/Soundness.lean`, together with polymorphic round-`0` unweighted affine-word escape contracts (`SmoothBatchRound0GapBound`, `SmoothBatchRound0Escape`, and the binary `BatchRound0GapBound`, `BatchRound0Escape`, testing unweighted agreement of `stmt.eval x` strictly above `B / n` for `n = 2 ^ d` and `B = n - e - 1`, whereas Section 8.2.1, printed pp. 41–42, defines `E⁽⁰⁾` immediately before eq. (8.8)—and eq. (8.8) bounds its probability—via `μ⁽⁰⁾`-weighted agreement of the reported oracle `f⁽⁰⁾` above `max(α, √ρ · (1 + 1 / (2m)))`; because `μ⁽⁰⁾ = 1` only where `f⁽⁰⁾` matches `stmt.eval x`, high weighted agreement implies high unweighted agreement of `stmt.eval x` while the converse can fail, and for a tuple with common agreement at most `B / n` the Lean event contains the paper's event `E⁽⁰⁾` whenever `max(α, √ρ · (1 + 1 / (2m))) ≥ B / n`, though the cutoffs can differ, e.g. at `n = 16, k = 4, e = 7, α = 1 / 2, m = 3`), list-premise-free round-`0` probability upper bounds with exact denominator `|F|` across the unique-decoding (`batchRound0Escape_of_unique`; at batch size `t = 0` the false word is independent of the challenge and its round-`0` escape probability is `0`), explicit-parameter `(m₀, D₀)` Johnson (`batchRound0Escape_of_johnson_discrete`), and original explicit-constant Johnson / `η`-gap regimes (`friBatchJohnsonRound0Bound`, `batchRound0Escape_of_johnson`, `batchRound0Escape_of_johnson_eta`, inheriting `Curve.lean`'s explicit Siegel constants and direct-`η` scope rather than eq. (1.3)'s `min(η, √ρ / 20)`), and conditional whole-protocol uniform per-round escape / two-channel BCS random-oracle composition steps ([bcs16](#bcs16));
- [FRI/BatchJohnsonSoundness.lean](../CslibFrontier/Crypto/Protocols/FRI/BatchJohnsonSoundness.lean): whole-protocol summed commit-phase (`friSmoothBatchCommitGame`, with binary `friBatchCommitGame` via `friBatchCommitGame_eq_friSmoothBatchCommitGame`) and interactive IOP (`iopInteractiveGame (friSmoothBatchIOP params t)` and `iopInteractiveGame (friBatchIOP params t)`) soundness probability upper bounds combining `BatchSoundness.lean`'s round-`0` escape bounds with `Soundness.lean` / `JohnsonSoundness.lean`'s per-round smooth folding budgets (geometric for `l⁽ⁱ⁾ = 2`) via [BCS/Interactive.lean](../CslibFrontier/Crypto/Protocols/BCS/Interactive.lean) (`iopCommitPhase_map_true_le_sum`, `iopInteractiveGame_le_sum`), in the setting of Lemma 8.2 (printed pp. 38–39, eq. (8.5); proved via the commit-phase bad-event sum in Section 8.2.1 on printed p. 42 and geometric telescoping on printed p. 43) and Theorem 8.3 (printed p. 39, proved on printed p. 40 by applying Lemma 8.2), across the unique-decoding (`friSmoothBatchUniqueCommitError`, `friBatchUniqueCommitError`), discrete `(m₀, D₀)` + `(mRound, DRound)` Guruswami–Sudan, closed-form Johnson (`friSmoothBatchJohnsonCommitError`, `friBatchJohnsonCommitError`), and `η`-gap (`friSmoothBatchJohnsonEtaCommitError`, `friBatchJohnsonEtaCommitError`) regimes in both integer-`e` (`batchProximityLang`) and real-`α` (`⌊α₀ * 2 ^ d⌋₊` via `batchFloorThreshold_bounds` for commit-phase bounds and `batchCorrAgreeLang t α` via `batchCeilThreshold_bounds` / `batchCorrAgreeLang_eq_batchProximityLang` for forward interactive upper bounds and direct contrapositives `friBatchIOP_sound_of_*`) forms, together with separate adaptive two-channel BCS random-oracle compiler compositions ([bcs16](#bcs16)).
  Relative to the `μ⁽⁰⁾`-weighted oracle event `E⁽⁰⁾` defined immediately before eq. (8.8) (whose probability eq. (8.8) bounds, with cutoff `max(α, √ρ · (1 + 1 / (2m)))`), the unweighted `stmt.eval x` round-`0` event unconditionally contains `E⁽⁰⁾` at matching Johnson multiplicity `mJ = m` (`m ≤ mJ`), contains `E⁽⁰⁾` in the real-`α` unique-decoding case under the explicit condition `(1 + ρ) / 2 ≤ max(α, √ρ · (1 + 1 / (2m)))` (failing on `𝔽₁₇ˣ` at `n = 16, k = 4, α = 1 / 2, m = 3`, where `10` agreeing positions clear `7 / 12` and miss strict `> 5 / 8`), and contains `E⁽⁰⁾` in the real-`α` `η`-gap case under `√ρ + η ≤ max(α, √ρ · (1 + 1 / (2m)))` (with `t = 0` round-`0` escape `0`).
  Inherits direct-read / combined word-query budget accounting (`batchInputWordReads`, `batchTotalWordQueries` vs. exact `proofOracleQueries`) and original explicit Siegel constants (`(2 - 1 / 2 ^ totalLog)` for smooth schedules, with `totalLog = m` in the binary case: `(2 - 1 / 2 ^ m) * 1800 * (mJ + 1)^6 * (2 ^ d)^2 / (ρ * |F|)` for `mJ ≥ 1` and `(2 - 1 / 2 ^ m) * 115200 * (2 ^ d)^2 / (ρ * η^6 * |F|)` using `η` directly rather than eq. (1.3)'s `min(η, √ρ / 20)`); exact correspondence with the displayed constants of Lemma 8.2 and Theorem 8.3 remains tracked in #5968.

<a id="bcs16"></a>
## bcs16

Eli Ben-Sasson, Alessandro Chiesa and Nicholas Spooner.
*Interactive Oracle Proofs*.
TCC 2016-B II, 31–60. https://doi.org/10.1007/978-3-662-53644-5_2 .

<a id="bdfkk18"></a>
## bdfkk18

Chris Brzuska, Antoine Delignat-Lavaud, Cédric Fournet, Konrad Kohbrok and Markulf Kohlweiss.
*State Separation for Code-Based Game-Playing Proofs*.
ASIACRYPT 2018, Lecture Notes in Computer Science 11274, 222–249. https://doi.org/10.1007/978-3-030-03332-3_9 . Bibliographic metadata as in the library bibliography.
The primary text was not inspected, and no theorem number is claimed.
The manual attributes to this paper only the package calculus: packages composed sequentially and side by side, and the reduction and hybrid steps built from them.

<a id="beigelgill92"></a>
## beigelgill92

Richard Beigel and John Gill.
"Counting Classes: Thresholds, Parity, Mods, and Fewness."
*Theoretical Computer Science* 103(1), 3–23, 1992. https://doi.org/10.1016/0304-3975(92)90084-S ; the author's full version (dated June 10, 1996) is linked from https://cis.temple.edu/~beigel/papers/bg-mods-tcs.html . Checked against that author's version on 2026-11-08 UTC by worker w167-modpe.
(Re-inspected during #3554): Property 8(ii), p. 4 (binomial coefficients `C(f, g)` of #P functions with polynomially bounded UPF `g` are in #P, specialized locally to FP `g`), Corollary 20 (`C(n, p^k) ≢ 0 mod p` iff the base-`p` digit of `n` at `p^k` is nonzero), Proposition 29 (`j ∣ k` gives `MOD_jP ⊆ MOD_kP`) and Theorem 30 (`MOD_{k^i}P = MOD_kP` for prime `k` and `i ≥ 1`), Theorem 32 (Hertrampf characterization of `MOD_{jk}P`), Corollaries 33–35, p. 16 (Corollary 33 is prime-factor union decomposition, Corollary 34 is squarefree collapse, Corollary 35 is ordinary union closure), and Hertrampf remark (intersection closure yields complement closure).
`CslibFrontier/Computability/Complexity/Classes/ModP/Composite.lean` contains a locally reconstructed proof of the Hertrampf characterization (the 1990 original was not inspected).
Numbering follows the author's version; the journal pagination is from the DOI record and the typeset journal numbering was not checked.

<a id="bellman58"></a>
## bellman58

Richard Bellman.
"On a Routing Problem."
*Quarterly of Applied Mathematics* 16(1), 87–90, 1958. https://doi.org/10.1090/qam/102435 . Bibliographic data from the DOI record and secondary summaries; the paper was not inspected in this pass.

<a id="bellman62"></a>
## bellman62

Richard Bellman.
“Dynamic Programming Treatment of the Travelling Salesman Problem.”
*Journal of the ACM* 9(1), 61–63, 1962. https://doi.org/10.1145/321105.321111 . Bibliographic metadata checked on 2026-11-07; the article body was not inspected in this pass, so the manual cites it for the subset dynamic program and not for a numbered statement.

<a id="bennett89"></a>
## bennett89

Charles H. Bennett.
*Time/Space Trade-Offs for Reversible Computation*.
SIAM Journal on Computing 18(4), 766–776, 1989. https://doi.org/10.1137/0218053 . Bibliographic metadata only; the paper was not inspected in this pass.
The manual credits it with the recursive checkpointing strategy as described in [ltv98](#ltv98), Sections 6 and 7.

<a id="benor1983"></a>
## benor1983

Michael Ben-Or.
"Another Advantage of Free Choice (Extended Abstract): Completely Asynchronous Agreement Protocols."
*Proceedings of the Second Annual ACM Symposium on Principles of Distributed Computing (PODC '83)*, 27–30, 1983. https://doi.org/10.1145/800221.806707 ; open copy https://cs.nyu.edu/~apanda/classes/sp26/papers/benor83.pdf . Checked against that PDF (SHA-256 `d094451eea8ce287ab4b4625eb50604e32e247dbf724a88d35b57e6fa2a778c4`) on 2026-11-22 UTC: Section 2 ("The Consensus Problem", printed pp. 27–28: binary inputs `x_P`, write-once `0`/`1` output register, unanimous validity `(C1)`, asynchronous message buffer `M`, history- and configuration-dependent adversary step/delivery schedule, and `t`-correctness) and Section 3 ("A Consensus Protocol", printed pp. 28–29: Protocol A on p. 28 with `N - t` Stage-1/Stage-2 waits, `> N / 2` majority for `(2, r, v, D)` vs `(2, r, ?)`, Stage-2 adoption on at least one `D`-message, decision on `> t` `D`-messages, and independent `1 / 2` local coin flip fallback; Theorem 1 and the `N ≤ 2t` partition remark on p. 29).
[BenOr/Basic.lean](../CslibFrontier/Computability/Distributed/BenOr/Basic.lean) formalizes quorum-phase execution (`PhaseSchedule.Valid`) and phased mid-stage crash safety (`CrashSchedule.Valid`, `crashRun_agreement`) for Protocol A's thresholds under arbitrary coin sequences; [BenOr/Liveness.lean](../CslibFrontier/Computability/Distributed/BenOr/Liveness.lean) proves a **pre-coin phase-scheduler termination step** (`probRun`, selecting each phase's complete `PhaseSchedule` from the phase boundary state before sampling `localCoinLaw`), alongside a separate common-coin variant (`commonCoinLaw`, not in `[BenOr1983]`), while termination in Section 2's arbitrary step/delivery-interleaving scheduler model remains open in `#7120`.

<a id="bensassonkopparty12"></a>
## bensassonkopparty12

Eli Ben-Sasson and Swastik Kopparty.
*Affine Dispersers from Subspace Polynomials*.
SIAM Journal on Computing 41(4), 880–914, 2012. https://doi.org/10.1137/110826254 . Bibliographic metadata as in the library bibliography; the primary PDF was not directly inspected, so ECCC report theorem locators recorded in the source remain unverified against the primary text.

<a id="berge57"></a>
## berge57

Claude Berge.
*Two Theorems in Graph Theory*.
Proceedings of the National Academy of Sciences of the United States of America 43(9), 842–844, 1957. https://doi.org/10.1073/pnas.43.9.842 . Bibliographic metadata only; the primary text was not inspected.
The manual attributes to this paper the augmenting-path characterization of maximum matchings; the "Theorem 1" locator comes from secondary descriptions and is unverified.
Schrijver's lecture notes ([schrijver17](#schrijver17), Theorem 3.2) state the result without attribution.

<a id="berge58"></a>
## berge58

Claude Berge.
*Sur le couplage maximum d'un graphe*.
Comptes Rendus Hebdomadaires des Séances de l'Académie des Sciences 247, 258–259, 1958.
Bibliographic data from secondary bibliographies; the note was not inspected, and no theorem number is claimed.
The manual attributes to it the Tutte–Berge formula, following [schrijver17](#schrijver17), Section 5.1.

<a id="berger1966"></a>
## berger1966

Robert Berger.
*The Undecidability of the Domino Problem*.
Memoirs of the American Mathematical Society 66, 1966.
[Publisher record](https://doi.org/10.1090/memo/0066).
Bibliographic metadata checked on 2026-11-16 against the publisher record and its Crossref deposit.
The book's full text was inaccessible in this pass: internal locator not verified.
The formalization uses the later Robinson–Ollinger route described under [Jeandel–Vanier](#jeandelvanier2020), ported from the pinned lean-wang revision there.

<a id="bermangaray1989"></a>
## bermangaray1989

Piotr Berman and Juan A. Garay.
"Asymptotically Optimal Distributed Consensus (Extended Abstract)."
*Automata, Languages and Programming (ICALP 1989)*, Lecture Notes in Computer Science 372, 80–94, Springer, 1989. https://doi.org/10.1007/BFb0035753 . Bibliographic metadata checked via Crossref and secondary indexes on 2026-11-22 UTC; the paywalled LNCS proceedings PDF was not accessible in this pass, so internal section and theorem locators are not verified (tracked under [#7210](https://github.com/cslib-community/cslib-frontier/issues/7210)).
[Byzantine/PhaseKing.lean](../CslibFrontier/Computability/Distributed/Byzantine/PhaseKing.lean) therefore lands `phaseKing`, `phaseKing_solvesByzantineAgreement`, and `exists_polyMsg_solvesByzantineAgreement` as 2-round-per-phase rotating-king protocol steps toward [#7210](https://github.com/cslib-community/cslib-frontier/issues/7210) (`4 * t < Fintype.card P`, `2 * (t + 1)` rounds, `Msg = V`): in round `2 * k` each process sets `kingProposal` to the unique value with multiplicity at least `n - 2 * t` (defaulting to `est`), and in round `2 * k + 1` each process locks onto any value with round-`2 * k` multiplicity at least `n - t` and adopts the phase king's broadcast otherwise.

<a id="bermangarayperry1989"></a>
## bermangarayperry1989

Piotr Berman, Juan A. Garay and Kenneth J. Perry.
"Towards Optimal Distributed Consensus."
*30th Annual Symposium on Foundations of Computer Science (FOCS 1989)*, 410–415, 1989. https://doi.org/10.1109/SFCS.1989.63511 . Bibliographic metadata checked via Crossref and secondary indexes on 2026-11-22 UTC; the paywalled IEEE proceedings PDF was not accessible in this pass, so internal section and theorem locators are not verified.
Mentioned in [Byzantine/PhaseKing.lean](../CslibFrontier/Computability/Distributed/Byzantine/PhaseKing.lean) only as background for the 3-round-per-phase extension of [Berman and Garay](#bermangaray1989) from `4 * t < n` to `3 * t < n` resilience (not formalized here; tracked under [#7210](https://github.com/cslib-community/cslib-frontier/issues/7210)), alongside the 2-round `4 * t < n` rotating-king step (`phaseKing`, with `Fin 4, t = 1` sharpness counterexample `phaseKing_fails_four_one`) and the [Turpin–Coan](#turpincoan1984) multivalued-to-binary reduction step (`turpinCoan`).

<a id="bermanhartmanis75"></a>
## bermanhartmanis75

Leonard Berman and Juris Hartmanis.
*On Isomorphisms and Density of NP and Other Complete Sets*.
Technical Report TR75-260, Department of Computer Science, Cornell University, October 1975. https://hdl.handle.net/1813/7101 . The open eCommons PDF is an image scan without a text layer.
An independent agent review checked these locators against it on 2026-11-08 UTC: §I, printed p. 2 (the isomorphism conjecture and its `P ≠ NP` consequence); §III, Theorem 1, printed pp. 7–10 (PDF pp. 10–13; isomorphism from invertible, length-increasing one-one reductions); Lemmas 3 and 5, printed pp. 10–12 (length growth and the two-argument padding and read-back condition); and Theorem 7 with its CNF construction, printed pp. 13–14.
The journal version (*SIAM Journal on Computing* 6(2), 305–322, 1977, https://doi.org/10.1137/0206023) was not checked, and its numbering is not claimed to match.

<a id="bertsekas88"></a>
## bertsekas88

Dimitri P. Bertsekas.
"The auction algorithm: A distributed relaxation method for the assignment problem."
*Annals of Operations Research* 14, 105–123, 1988. https://doi.org/10.1007/BF02186476 . Author-hosted scan: https://web.mit.edu/dimitrib/www/TheAuctionAP.pdf . The original algorithm is the MIT LIDS working paper "A Distributed Algorithm for the Assignment Problem" (March 1979), retyped at https://web.mit.edu/dimitrib/www/Bertsekas_Auction_Distributed_1979.pdf . The manual uses the 1988 paper for the `O(N A C / ε)` complexity of the pure (unscaled) auction (§1) and for scaling integer costs by `N + 1` and running down to `ε = 1` (§3).
Both locators were checked against the author-hosted scan on 2026-11-08 UTC.

<a id="bertsekas98"></a>
## bertsekas98

Dimitri P. Bertsekas.
*Network Optimization: Continuous and Discrete Models*.
Athena Scientific, Belmont, MA, 1998.
ISBN 1-886529-02-7.
Author-hosted copy: https://web.mit.edu/dimitrib/www/netbook_Full_Book_NEW.pdf . Checked against that copy on 2026-11-08 UTC: §1.3.3 and Prop. 1.4 (an assignment satisfying `ε`-complementary slackness is within `n ε` of optimal); §7.1.1, ε-CS (7.1), the bidding rule (7.2)–(7.5) with the Gauss–Seidel version, Prop. 7.1 (ε-CS is preserved) and Prop. 7.2 (termination, `n ε`-optimality, optimality for integer data and `ε < 1/n`); Figs. 1.12–1.14 (the price-war example); §7.1.4 and Prop. 7.3 (`ε`-scaling, not formalized).

<a id="beullenscamposcelihesskannwischer26"></a>
## beullenscamposcelihesskannwischer26

Ward Beullens, Fabio Campos, Sofía Celi, Basil Hess and Matthias J. Kannwischer.
*MAYO: Round 3 Version*, August 31, 2026 (bibliography key `BeullensCamposCeliHessKannwischer2026`). https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/mayo_specification.pdf . Checked against that PDF on 2026-11-14 (SHA-256 `1fc7561dc8ffdbe36c101b985266e4d3c8aa88fa580e18ead215a80ac7bb371f`): Section 2.1.2, Algorithm 2, printed pp. 8–9 specifies `SampleSolution` by shifting with explicit randomness, rejecting a matrix without full row rank even when the shifted system is consistent, and shifting the solution back.
Section 2.1.5, Algorithm 7, printed p. 14 tries at most 256 separately derived randomness records and keeps the first successful call; the remark on printed p. 3 says a failed signing attempt retains the salt and derives fresh randomness for another preimage-sampling attempt.
The formalization records only the deterministic abstract solver contract, shift correctness and ordered bounded-retry behavior.
It does not formalize the source's uniform-sampling statement, rank probability, signing algorithm, correctness or security reductions.

<a id="beyersdorffgalesilauria10"></a>
## beyersdorffgalesilauria10

Olaf Beyersdorff, Nicola Galesi and Massimo Lauria.
*A lower bound for the pigeonhole principle in tree-like Resolution by asymmetric Prover–Delayer games*.
Information Processing Letters 110(23), 1074–1077, 2010. https://doi.org/10.1016/j.ipl.2010.09.007 ; author's copy https://massimolauria.net/documents/tree-like-php.pdf (6 pages).
Read in the author's copy on 2026-11-08.
Locators checked there: Theorem 1 on p. 3 (if `F` has a tree-like refutation of size at most `S`, Delayer gets at most `log S` points in every `(c₀, c₁)`-game with `1/c₀ + 1/c₁ = 1`); Theorem 2 on p. 4 (every tree-like refutation of `PHP^m_n` has size `2^Ω(n log n)`); the explicit `2^((n/2) log(n/2 + 1)) = (n/2 + 1)^(n/2)` for even `n` at the end of that proof on p. 5; and the closing remark on p. 5 that the bound also holds for the functional pigeonhole principle.
The abstract and introduction present the result as a simpler proof of Dantchev and Riis's bound (CCC 2001).
Journal pagination was taken from the Crossref record.
The ECCC version (TR10-081) was not reachable from this environment and was not read.

<a id="bfckk24"></a>
## bfckk24

Michael A. Bender, Martin Farach-Colton, John Kuszmaul and William Kuszmaul.
"Modern Hashing Made Simple."
*Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA 2024)*, 363–373, 2024. https://doi.org/10.1137/1.9781611977936.33 ; open author-hosted copy https://par.nsf.gov/servlets/purl/10488765 (11 pages; `BenderFarachColtonKuszmaulKuszmaul2024`).
Checked against the open copy on 2026-11-14 UTC: Section 2.1, PDF pp. 2–3 (word-RAM model with `w = (1 + Θ(1)) log n`, high-probability `1 - O(1 / n^c)` convention, and zero-space random-hash-oracle assumption); Section 2.2, PDF p. 3 (B-trees and `k`-tries, Lemma 2.2); Section 3, PDF p. 4 (slow partition hash tables, Lemma 3.1); Section 4, PDF pp. 4–6 (indexed partition hash tables and `B = √(log n)` Four-Russians B-tree query mapper, Lemmas 4.1–4.3); and Section 5, PDF pp. 6–7 (deamortizing insertions and deletions to `O(1)` time w.h.p. via growing and shrinking `√n`-tries, Lemma 5.1; historical trie-buffer discussion in Section 7, PDF p. 8).
SOSA proceedings pagination (`363–373`) comes from `references.bib` and the DOI record and was not separately inspected; [#5356](https://github.com/cslib-community/cslib-frontier/issues/5356) (`CslibFrontier/DataStructure/Dictionary/WordRAM/SuccinctWhp.lean`) formalizes the fixed-capacity Word-RAM key-value adaptation (Sections 2.2 and 3–5, with explicit `BitPackedDoubleTabulation` seeds sampled once at initialization, `CsrState` fallback on bad seeds, and SWAR B+-trees, giving `O_c(1)` query as well as update time w.h.p. rather than SOSA 2024's deterministic worst-case `O(1)` queries under runtime random-oracle resampling) rather than the Section 6 / Theorem 1.1 resizable hash table.
Also cited in `CslibFrontier/DataStructure/Dictionary/WordRAM/ResizableSuccinct` (`#3167`) for the fingerprint-indexed bucket partition and dynamic resizing design (Sections 3–4 and 6); that endpoint formalizes a synthesis original to this formalization—`O(1)` expected amortized oblivious instructions with explicit stored 3-wise independent quotient hashing and strict `1 · OPT` single-tape resting and migration-peak space on the Resizable Word RAM—whereas the paper proves deamortized with-high-probability bounds under idealized hash functions (remaining open under `#3167`).

<a id="bfckkl22"></a>
## bfckkl22

Michael A. Bender, Martin Farach-Colton, John Kuszmaul, William Kuszmaul and Mingmou Liu.
"On the Optimal Time/Space Tradeoff for Hash Tables."
*Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 1284–1297, 2022. https://doi.org/10.1145/3519935.3519969 ; open preprint `arXiv:2111.00602v2` (4 November 2021), https://arxiv.org/abs/2111.00602v2 (`BenderFarachColtonKuszmaulKuszmaulLiu2022`).
Checked against `arXiv:2111.00602v2` on 2026-11-11 and 2026-11-13 UTC (unnumbered title page is PDF p. 1, so printed p. `p` is PDF p. `p + 1`): Section 2.1, printed p. 3 / PDF p. 4 (balls-to-slots probe complexity `1 + log i` and switching cost); Section 2.4, printed p. 7 / PDF p. 8 (iterated logarithm `log^(k) n`); Sections 3 and 3.1, printed pp. 8–12 / PDF pp. 9–13 (`k`-kick tree hierarchy, depth-cap distribution, greedy unsaturated-ancestor selection, priority kicks with switching cost `≤ k + 1`, Lemma 1 on printed pp. 10–11 / PDF pp. 11–12, and Theorems 2–3 on printed p. 12 / PDF p. 13); and Section 5.1, printed p. 27 / PDF p. 28 (removal-only deletion in cubbies).
STOC proceedings pagination comes from `references.bib` and was not separately inspected.

<a id="bfprt73"></a>
## bfprt73

Manuel Blum, Robert W. Floyd, Vaughan Pratt, Ronald L. Rivest and Robert E. Tarjan.
*Time Bounds for Selection*.
Journal of Computer and System Sciences 7(4), 448–461, 1973. https://doi.org/10.1016/S0022-0000(73)80033-9 . Bibliographic metadata and the abstract's `5.4305 n` comparison bound for `PICK` were checked through secondary search results on 2026-11-08; the paper's text was not read.
The manual attributes to this paper only the median-of-medians selection algorithm and that constant.
The groups-of-five accounting in the Lean files follows the presentation in [clrs09](#clrs09), Section 9.3, which was not checked against the printed book.

<a id="bgks20"></a>
## bgks20

Eli Ben-Sasson, Lior Goldberg, Swastik Kopparty and Shubhangi Saraf.
"DEEP-FRI: Sampling Outside the Box Improves Soundness."
*11th Innovations in Theoretical Computer Science Conference (ITCS 2020)*, LIPIcs 151, 5:1–5:32, Schloss Dagstuhl, 2020. https://doi.org/10.4230/LIPIcs.ITCS.2020.5 ; preliminary versions `arXiv:1903.12243` and IACR Cryptology ePrint Archive 2019/336.
The library's key is `BenSassonGoldbergKoppartySaraf2020`.
Bibliographic metadata checked via DOI and DBLP records on 2026-11-24 UTC; the primary PDF was not directly inspected in this pass, so internal theorem and page locators are not claimed.
Cited in [FRI/DeepALI.lean](../CslibFrontier/Crypto/Protocols/FRI/DeepALI.lean) for out-of-domain DEEP quotienting (`deepQuotientPoly`, `deepQuotientWord`) and the DEEP-ALI algebraic linking protocol (`DeepALISystem`, `deepALIGame`), whose correlated-agreement soundness bounds compose integer Johnson list-size bounds with smooth and binary batched FRI ([bciks20](#bciks20)).

<a id="bhr12"></a>
## bhr12

Mihir Bellare, Viet Tung Hoang, Phillip Rogaway.
"Foundations of Garbled Circuits."
*Proceedings of the 2012 ACM Conference on Computer and Communications Security (CCS '12)*, 784–796, 2012. https://doi.org/10.1145/2382196.2382279 . Full version: Cryptology ePrint Archive, Report 2012/265.
Bibliographic data from the DOI record and secondary listings (`BellareHoangRogaway2012`).
The abstract garbling-scheme framework in `Garbling/{Scheme,Games,Foundations,CircuitInverters}.lean` follows Sections 2.3 and 3–4 of ePrint 2012/265 (conventional Boolean circuits in §2.3, syntax in §3.1, side information in §3.3, the five security games in §§3.4–3.6, the explicit topology and size inverters of Proposition 1 in §4.1, and the indistinguishability/simulation reductions and circuit corollaries of Propositions 2 and 3 and Corollaries 1 and 2 in §§4.2–4.3), while the concrete point-and-permute circuit garbling in `Garbling/{Basic,Privacy}.lean` cites the garbling-scheme syntax and simulation-based privacy with topology side information at paper level only, because the ePrint copy returned HTTP 403 and the ACM page sat behind a bot challenge in the pass that added those modules.
Checked on 2026-11-15 against the ePrint full version dated October 1, 2012 (45 pages, SHA-256 `33c00b94752c8ecd852c8cf84ef70967a4290ea5409ed615e6293ff3137dc8ed`; printed page `p` is PDF page `p + 2`): §3.1, p. 7, the length condition (`|F|`, `|e|` and `|d|` depend only on `k`, `f.n`, `f.m` and `|f|`), the nondegeneracy condition (`e` and `d` depend only on those and the coins) and the correctness condition, which `Garbling/HalfGates/Scheme.lean` cites for the clauses that half-gates garbling fails.

<a id="bhr12b"></a>
## bhr12b

Mihir Bellare, Viet Tung Hoang, Phillip Rogaway.
"Adaptively Secure Garbling with Applications to One-Time Programs and Secure Outsourcing."
*Advances in Cryptology – ASIACRYPT 2012*, LNCS 7658, 134–153, Springer, 2012. https://doi.org/10.1007/978-3-642-34961-4_10 . Full version: Cryptology ePrint Archive, Report 2012/564 (`BellareHoangRogaway2012b`).
`Garbling/Adaptive.lean` formalizes the coarse-grained adaptive privacy game `Prv1` of Section 3.1, Figure 2, in which a two-stage adversary first receives `(F, d)` from `Garble(f)` and then adaptively queries `Input(x)` to receive `X` from a stateful two-stage simulator.

<a id="bird84"></a>
## bird84

Charles G. Bird.
*Group Incentive Compatibility in a Market with Indivisible Goods*.
Economics Letters 14(4), 309–313, 1984. https://doi.org/10.1016/0165-1765(84)90003-X . Bibliographic metadata checked via search records on 2026-11-24 UTC; the publisher's text is paywalled and was not inspected, so no internal theorem or page locator is claimed.
Cited as the standard primary reference originating group strategy-proofness of top trading cycles (`Bird1984`); strong group strategy-proofness and coalitional invariance are proved from first principles in `CslibFrontier/Algorithms/Lean/HousingMarket/GroupIncentives.lean`.

<a id="birge83"></a>
## birge83

Lucien Birgé.
"Approximation dans les espaces métriques et théorie de l'estimation."
*Zeitschrift für Wahrscheinlichkeitstheorie und Verwandte Gebiete* 65(2), 181–237, 1983. https://doi.org/10.1007/BF00532480 . Bibliographic metadata checked via search summaries on 2026-11-11; the article text was not inspected, and no theorem number is claimed.
Cited as background origin for bounded likelihood-ratio Hellinger tests (`leCamBirgeTest`) and Hellinger tournament localization (`birgeTournamentSelect`); the explicit `1/3`–`2/3` clipped `birgeWeight` formulation and constants (`1 - h² / 25`, `10 * r`, `11 * r`, `2 * (M - 1) * exp (-4 n r²)`) are proved from first principles in `CslibFrontier/Probability/HypothesisSelection/{LeCamBirge,Tournament}.lean`.

<a id="birmanschiperstephenson1991"></a>
## birmanschiperstephenson1991

Kenneth Birman, André Schiper and Pat Stephenson.
"Lightweight Causal and Atomic Group Multicast."
*ACM Transactions on Computer Systems* 9(3), 272–314, August 1991. https://doi.org/10.1145/128738.128742 . Checked firsthand on 2026-11-22 against the typeset ACM TOCS PDF hosted at Cornell (`https://www.cs.cornell.edu/courses/cs614/2003sp/papers/BSS91.pdf`, SHA-256 `aaac290d3ba2261a22dedf85ec8ba7e393bf972c3e6141eaf92aa526b0008749`; printed page `p` is PDF page `p - 271`): §4.1 (pp. 277–278, execution and asynchronous transport model), §4.2 (pp. 278–280, causal `CBCAST` vs. total `ABCAST` delivery ordering), §4.3 (p. 280, vector time `VT(p_i)` update rules (1)–(4) and the characterization `m → m' ↔ VT(m) < VT(m')`), and §5.1 (pp. 281–283, single-group `CBCAST` protocol steps (1)–(3) on p. 281 with delivery condition `VT(m)[i] = VT(p_j)[i] + 1` and `VT(m)[k] ≤ VT(p_j)[k]` for `k ≠ i`, Safety proof on p. 282, and Liveness proof on p. 283).
[CausalBroadcast/Causal.lean](../CslibFrontier/Computability/Distributed/CausalBroadcast/Causal.lean) formalizes a static single-group (`dests(m) = P`), single-hop `CBCAST` step toward [#7297](https://github.com/cslib-community/cslib-frontier/issues/7297) over `Cslib.LTS` for arbitrary crash-fault sets `F : Set P` (without diffusion/view-flush forwarding, dynamic membership views §5.5, token-holder view-synchronous `ABCAST` §5.2, vector-clock stability compression §§5.3–5.4, or overlapping process groups §6); because raw point-to-point multicast can be interrupted mid-send if a faulty sender crashes (`BSSAction.crashBroadcast`), liveness at `q ∉ F` (`bss_live_of_packetSentTo`) takes the causal-ancestor transmission hypothesis `PacketSentTo q`, specializing in `bss_live_of_atomic_multicast` and `BSSSolvesAtomicMulticastCausalBroadcast` to liveness when crashes occur between atomic multicast steps.

<a id="bjks04"></a>
## bjks04

Ziv Bar-Yossef, T. S. Jayram, Ravi Kumar and D. Sivakumar.
"An Information Statistics Approach to Data Stream and Communication Complexity."
*Journal of Computer and System Sciences* 68(4), 702–732, 2004 (preliminary version in FOCS 2002). https://doi.org/10.1016/j.jcss.2003.11.006 . Checked on 2026-11-16 against an "Article in press" copy of the journal version with the journal's pagination: Section 3.1, the end of the proof of Theorem 3.1 (pp. 708–709), where a `c`-pass `s`-space algorithm gives a `t`-player multi-round protocol in which "the last player sends the content of the memory back to the first player", with total communication at most `cst`.
Whether this paragraph is already in the FOCS 2002 version was not checked.

<a id="bjkst02"></a>
## bjkst02

Ziv Bar-Yossef, T. S. Jayram, Ravi Kumar, D. Sivakumar, Luca Trevisan.
“Counting Distinct Elements in a Data Stream.”
*Randomization and Approximation Techniques in Computer Science (RANDOM 2002)*, LNCS 2483, 1–10, Springer, 2002. https://doi.org/10.1007/3-540-45726-7_1 . Author-hosted copy: https://webee.technion.ac.il/people/zivby/papers/f0/f0.ps . Locators checked against that copy on 2026-11-08 UTC: Section 2 (the first algorithm) and Theorem 1.
The algorithm picks a pairwise independent hash `h : [m] → [M]` with `M = m³` and keeps the `t = ⌈96/ε²⌉` smallest distinct hash values.
It outputs `tM/v`, where `v` is the `t`-th smallest value.
Each tail is bounded by `1/6` via Chebyshev, plus `1/m` for collisions, and the median of `O(log(1/δ))` copies gives `O(1/ε² · log m · log(1/δ))` bits.
The LNCS page numbers come from the DOI record and were not checked against the typeset volume.

<a id="bland77"></a>
## bland77

Robert G. Bland.
"New Finite Pivoting Rules for the Simplex Method."
*Mathematics of Operations Research* 2(2), 103–107, 1977. https://doi.org/10.1287/moor.2.2.103 . Bibliographic data from the DOI record and search summaries; the paper was not inspected in this pass, and no theorem number is claimed.
The manual credits it with the smallest-subscript pivoting rule and its finiteness; the formalized no-cycling proof is the standard largest-fickle-variable argument as presented in textbooks such as [chvatal83](#chvatal83), Chapter 3.

<a id="blum67"></a>
## blum67

Manuel Blum.
*A Machine-Independent Theory of the Complexity of Recursive Functions*.
Journal of the ACM 14(2), 322–336, 1967. https://doi.org/10.1145/321386.321395 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the two axioms, recursive relatedness and the speed-up theorem to this paper.
The manual also mentions the customary attribution of the measure-independent theorem on arbitrarily complex functions to this paper (and to Rabin, 1960); that attribution and any theorem locator are unverified.

<a id="blumfurstkearnslipton93"></a>
## blumfurstkearnslipton93

Avrim Blum, Merrick Furst, Michael Kearns and Richard J. Lipton.
"Cryptographic Primitives Based on Hard Learning Problems."
*Advances in Cryptology — CRYPTO '93*, LNCS 773, 278–291, 1993. https://doi.org/10.1007/3-540-48329-2_24 . Bibliographic metadata only (`references.bib`); the paper was not inspected and no numbered result is claimed.
[CryptoHardness/Inversion.lean](../CslibFrontier/MachineLearning/UniformLearning/CryptoHardness/Inversion.lean) cites it, with [Impagliazzo and Levin](#impagliazzolevin90), for the easy direction of the correspondence between average-case learning and one-way functions: an inverter for the map from a key and examples to the labelled sample is a consistent learner.
[CryptoHardness/OneWayInversion.lean](../CslibFrontier/MachineLearning/UniformLearning/CryptoHardness/OneWayInversion.lean) cites both papers the same way for a step towards that direction, not for a statement of either paper.

<a id="blummansour07"></a>
## blummansour07

Avrim Blum and Yishay Mansour.
"From External to Internal Regret."
*Journal of Machine Learning Research* 8, 1307–1324, 2007. https://www.jmlr.org/papers/v8/blum07a.html . Read in the JMLR PDF on 2026-11-10.
Locators checked there: the definition of swap regret as regret against all `N^N` modification rules (§2, p. 1311), Definition 2 (`ε`-correlated equilibrium) and Theorem 3 (`R/T`-correlated equilibria from swap regret `R`, p. 1311), the reduction with stationary `p = pQ` and Definition 4 (§3, p. 1312), and Theorem 5 (swap regret at most `∑ i, R_i`) with Corollaries 6 and 7 (`O(N √(T log N))` and `O(√(T N log N))`, p. 1313).
The paper scales losses to `[0, 1]`; the library's Hedge-based bound uses losses in `[-1, 1]` and the second-order Hedge bound, which gives `2 √(T N ln N)` with explicit constants.

<a id="blummansour07agt"></a>
## blummansour07agt

Avrim Blum and Yishay Mansour.
"Learning, Regret Minimization, and Equilibria."
Chapter 4 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 79–102. https://doi.org/10.1017/CBO9780511800481.006 . Bibliography key `BlumMansour2007AGT`.
Checked against the 2007 book PDF (printed pp. 79–102) on 2026-11-24 UTC (and cross-checked against the author-hosted chapter PDF `regret-chapter.pdf`, preprint pp. 4–30, whose section, definition, theorem, and exercise numbers match the published chapter): §4.2 (pp. 81–82, preprint pp. 7–8: adversarial full-information online model over `N` actions with round-`t` distributions `p^t`, loss vectors `ℓ^t ∈ [0, 1]^N`, cumulative losses `L_i^T` and `L_min^T = min_i L_i^T`, external regret `R = L_H^T - L_min^T`, and memoryless modification-rule families `F` specializing to external, pairwise internal `F_{i,j}` / `F^in`, and swap `F^{sw}` regret, formalized via `IsOnlineAlgorithm` in [LowerBounds.lean](../CslibFrontier/MachineLearning/OnlineLearning/LowerBounds.lean), `minCumLoss` in [Greedy.lean](../CslibFrontier/MachineLearning/OnlineLearning/Greedy.lean), and `modRegret` and `internalRules` in [InternalRegret.lean](../CslibFrontier/MachineLearning/OnlineLearning/InternalRegret.lean)); §4.3, Theorem 4.1 (pp. 82–83: dynamic regret `R_{G_all} ≥ T (1 - 1 / N)` against all action sequences `G_all` on `{0, 1}` losses, `exists_dynamic_regret_ge`); §4.3.1, Theorem 4.2 (p. 83: Greedy / Follow-the-Leader bound `L_Greedy^T ≤ N L_min^T + (N - 1)`, generalized from `{0, 1}` to all `[0, 1]` losses in `greedy_loss_le` and `greedyPlay_loss_le`), Theorem 4.3 (pp. 83–84: deterministic online lower bound `L_D^T = T` and `L_min^T = ⌊T / N⌋`, proved with exact equality `minCumLoss ℓ T = ⌊T / N⌋` in `exists_deterministic_loss_eq_and_minCumLoss_eq`), and Theorem 4.4 (p. 84: Randomized Greedy uniform-leader bound `L_RG^T ≤ ln N + (1 + ln N) L_min^T` on `{0, 1}` losses in `randGreedy_loss_le_harmonic` and `randGreedy_loss_le_log`; contrary to p. 83's opening remark that everything in §4.3.1 extends easily to `[0, 1]` losses, exact-tie `randGreedyProb` fails Theorem 4.4 on `[0, 1]` losses, refuted at `T = 7` on `Fin 2` by `perturbedAltLoss` in [ExternalRegret.lean](../CslibFrontierTests/ExternalRegret.lean)); §§4.3.2–4.3.3, Theorem 4.5 (pp. 85–86: Randomized Weighted Majority `(1 + η) L_min^T + (ln N) / η` on `{0, 1}` losses for `0 < η ≤ 1 / 2`) and Theorem 4.6 (pp. 86–87: Polynomial Weights `L_PW^T ≤ L_k^T + η Q_k^T + (ln N) / η` with `Q_k^T = ∑_{t=1}^T (ℓ_k^t)^2` on `[0, 1]` losses, `mw_regret_le_sq` and `mw_regret_le` in [MultiplicativeWeights.lean](../CslibFrontier/MachineLearning/OnlineLearning/MultiplicativeWeights.lean), together with the capped tuning `η = min {√((ln N) / T), 1 / 2}` giving `2 √(T ln N)` external regret for all horizons `T` in both Theorems 4.5 and 4.6, `mw_regret_le_sqrt_of_mem_Icc`); §4.3.4, Theorem 4.7 (pp. 87–88: short-horizon stochastic lower bound `E[L_{R1}^T] = T / 2` with `L_min^T = 0` for `T < log₂ N`, proved for `2 ^ T ≤ N` in `exists_stochastic_loss_eq_half_minCumLoss_zero`) and Theorem 4.8 (p. 88: two-expert `Ω(√T)` stochastic external-regret lower bound, proved with explicit Khintchine constant `1 / (2 e)` for `N ≥ 2` in `exists_two_experts_stochastic_regret_ge`); §4.4.2, Theorem 4.9 (pp. 89–90: constant-sum value duality `isMinimaxValue_swap_of_add_eq`, average expected loss `v + R / T` against arbitrary mixed opponent play in `average_loss_le_of_isMinimaxValue`, `constantSum_col_average_loss_le`, and `constantSum_average_loss_mem_Icc`, and the coupled no-regret proof of von Neumann's minimax theorem `ciSup_ciInf_eq_ciInf_ciSup` and `isMinimaxValue_ciInf_ciSup` in [ConstantSum.lean](../CslibFrontier/MachineLearning/OnlineLearning/ConstantSum.lean), noting the printed `min`/`max` transposition typo in the displayed formulas for `v_min^1, v_max^1` on p. 89); §§4.4.3–4.4.4 and §4.5 (pp. 90–94, preprint pp. 17–21: `switch_i`, Definitions 4.10 and 4.11 for exact and `ε`-correlated equilibrium, Theorem 4.12 for `(R / T)`-correlated equilibria from swap regret `R`, Theorem 4.13 bounding average weight on `ε`-dominated actions by `R / (ε T)` with §4.4.4 dominated-action discussion on pp. 91–92, and §4.5 Definition 4.14, Theorem 4.15, and Corollary 4.16, with Hart–Mas-Colell regret-matching and correlated-equilibrium bridges formalized in [OnlineLearning/RegretMatching.lean](../CslibFrontier/MachineLearning/OnlineLearning/RegretMatching.lean) and [Strategic/RegretMatching.lean](../CslibFrontier/GameTheory/Strategic/RegretMatching.lean)); §4.6, Theorem 4.17 (pp. 94–96: partial-information / multi-armed bandit block-exploration reduction partitioning `T` steps into `K` blocks, unbiased single-arm feedback eq. (4.2) on p. 95, and block count `K = ⌊(T / N)^{2/3}⌋` for `T ≥ N` on p. 96 giving `L_MAB^T ≤ L_min^T + O(T^{2/3} N^{1/3} log N)`, formalized without requiring `K ∣ T` via `mabPlay`, `mabPlay_bandit_congr`, `mabPlay_expected_loss_le`, `mabPlay_expected_loss_le_two_thirds`, and the capped Polynomial Weights instantiation `mabMW_expected_loss_le` in [Bandit.lean](../CslibFrontier/MachineLearning/OnlineLearning/Bandit.lean)); §4.7.1 (p. 98: prose discussion of Kalai and Vempala's online linear optimization algorithm over subsets of `ℝ^n` without a numbered theorem; `KalaiVempala2005` was not directly inspected, so [FPL.lean](../CslibFrontier/MachineLearning/OnlineLearning/FPL.lean) states its uniform-cube Follow-the-Perturbed-Leader bounds without claiming a verified theorem locator or registering an inventory entry); and Exercises 4.1, 4.2, 4.5, and 4.8 (p. 101, preprint p. 28: Exercise 4.1 bounding swap regret by `N` times internal regret in `modRegret_univ_le_card_mul_internalRules` and [OnlineLearning/RegretMatching.lean](../CslibFrontier/MachineLearning/OnlineLearning/RegretMatching.lean), with `N - 1` tightness witness `exists_modRegret_univ_eq_sub_one`; Exercise 4.2 separating swap from external regret on `Fin 3` in `exists_modRegret_const_zero_and_univ_eq` and `exists_unbounded_modRegret_univ_div_const`; Exercise 4.5 `Ω(√(T log N))` external-regret lower bound stated for `T ≥ N`, proved with constant `1 / (4 e)` for `N ≥ 2` and `⌊log₂ N⌋ ≤ T` in `exists_stochastic_regret_ge_sqrt_mul_log`; and Exercise 4.8 with §4.4.4, pp. 91–92 bounding cumulative weight on `ε`-dominated actions under `hedgeFactor` and `mwFactor` in `sum_prob_hedgeFactor_le_of_dominated` and `sum_prob_mwFactor_le_of_dominated`, contrasted with the nonpositive-external-regret counterexample `exists_nonpos_external_regret_dominated_weight` in [InternalRegret.lean](../CslibFrontier/MachineLearning/OnlineLearning/InternalRegret.lean)).

<a id="blumrosennisan07"></a>
## blumrosennisan07

Liad Blumrosen and Noam Nisan.
"Combinatorial Auctions."
Chapter 11 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 267–299 (ISBN 978-0-521-87282-9; bibliography key `BlumrosenNisan2007`).
A university-hosted PDF of the book (SHA-256 `83084d9996024ca92f313c5ae55fec7b3b379f06172a4c24b62229da9c558543`) was consulted via uncropped rendered page images on 2026-11-24 for the chapter heading and table of contents (p. viii, pp. 267 and 299–301 confirming page range 267–299), §11.1 (pp. 267–268: Definition 11.1 of normalized monotone valuations, Definition 11.2 of allocations and social welfare), §11.2 (*The Single-Minded Case*, pp. 270–275: Definition 11.3 of single-minded bids on p. 270; Definition 11.4 of winner determination and Proposition 11.5 on p. 271; Proposition 11.6 on p. 272; Definition 11.7 of single-minded mechanisms and incentive compatibility, and Theorem 11.8 on p. 273; Figure 11.1 greedy LOS mechanism and Lemma 11.9 on pp. 274–275; and Lemma 11.10 with displays (11.1)–(11.2) on p. 275), §11.3 (pp. 275–279: linear programming relaxation LPR displays (11.3)–(11.6) and dual DLPR displays (11.7)–(11.9) on p. 276; Definition 11.11 of demand, Definition 11.12 of Walrasian equilibrium with the printed index typo `S*_m` for `S*_n`, Theorem 11.13 First Welfare Theorem on pp. 277–278 with display (11.10); Example 11.14 on p. 278; Theorem 11.15 Second Welfare Theorem on pp. 278–279 with the printed typo `p*_i` for `p*_j`; and Corollary 11.16 on p. 279), §§11.4.1–11.4.2 (pp. 280–281: Definition 11.17 of additive and unit-demand valuations, Definition 11.19 of symmetric and downward-sloping valuations), §11.7.1 (pp. 289–292: Figure 11.3 item-price ascending auction on p. 290, Definition 11.28 of substitutes/gross-substitutes valuations on p. 290, Definition 11.29 of `ε`-Walrasian equilibrium on p. 291, Theorem 11.30, Claim 11.31 and Footnote 5 on p. 291, and Example 11.32 with Footnote 6 on p. 292), §11.8 and bibliography (pp. 295–297, attributing gross substitutes and ascending substitutes auctions to [Kelso and Crawford](#kelsocrawford1982) and [Gul and Stacchetti](#gulstacchetti1999)), and Exercise 11.6 (p. 299: every gross-substitutes valuation is submodular).
Printed-statement boundaries in §11.2 noted in `CslibFrontier/GameTheory/Mechanism/CombinatorialAuction/SingleMinded.lean` and witnessed in `CslibFrontierTests/GameTheory/SingleMinded.lean`: (a) the payment box in Figure 11.1 (p. 274) omits `k ∈ W` from the index condition `k < j, k ≠ i, S_k* ∩ S_j* = ∅`; (b) the exact `iff` in Lemma 11.9 (p. 274) under losers-pay-zero uses strict-value monotonicity (`v' > v` and `S' ⊆ S`), individual rationality, and nonnegative payments; and (c) Lemma 11.10 (p. 275) assumes `Nonempty M` (`m ≥ 1`) when empty desired bundles (`S* = ∅`) are admitted (the original Lehmann–O'Callaghan–Shoham article was not inspected directly).
Monotonicity (Definition 11.1) is not needed in §11.3; the fractional form of Theorem 11.13, the 0–1 form of Theorem 11.15, and Corollary 11.16 require the weaker condition `∀ i, 0 ≤ v i ∅` (tested tight by negative-empty-bundle counterexamples in `CslibFrontierTests/GameTheory/CombinatorialAuction.lean`).
In Theorem 11.30 (p. 291), the printed statement claims welfare within `n ε` (`|N| * ε`) for item-price `ε`-Walrasian equilibria (conflating item-price surcharges with the bundle-price `n ε` bound of Theorem 11.36 on p. 294); for Definition 11.29 item prices, the tight general bound proved in [GrossSubstitutes.lean](../CslibFrontier/GameTheory/Mechanism/CombinatorialAuction/GrossSubstitutes.lean) is `|M| * ε` (`m ε`), with `|N| * ε` proved under the single-item hypothesis `∀ i, (b.bundle i).card ≤ 1` and a 1-bidder, 2-item counterexample to `n ε` checked in `CslibFrontierTests/GameTheory/KelsoCrawford.lean`.
No polynomial-time running-time or oracle-query claim is formalized (the computational clause of Theorem 11.8 and Propositions 11.5–11.6 stay open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789)).

<a id="bm15"></a>
## bm15

Markus Bläser and Bodo Manthey.
*Smoothed Complexity Theory*.
ACM Transactions on Computation Theory 7(2), Article 6, 2015; preliminary version in MFCS 2012. https://doi.org/10.1145/2656210 ; arXiv:1202.1936.
Read in arXiv v2 (29 June 2012) on 2026-11-08.
§5, in the paragraph before Theorem 5.2, attributes `DistNP ⊆ Avg-P ⇒ NE = E` to Ben-David, Chor, Goldreich and Luby.
Journal metadata checked against the Crossref record.

<a id="bmr16"></a>
## bmr16

Marshall Ball, Tal Malkin, Mike Rosulek.
"Garbling Gadgets for Boolean and Arithmetic Circuits."
*Proceedings of the 2016 ACM SIGSAC Conference on Computer and Communications Security (CCS '16)*, 565–577, 2016. https://doi.org/10.1145/2976749.2978410 . Full version: Cryptology ePrint Archive, Report 2016/969.
Bibliographic data from the DOI record.
Checked on 2026-11-14 against the ePrint full version dated October 6, 2016 (22 pages, SHA-256 `e9a7cfec82e60b3c71970f8d617015ab0b731bb53d76710fcbf07bbb11a74755`); locators use its printed page numbers, which are also its PDF page numbers.
§4.1, p. 5: labels `W^x = W^0 + xΔ_m`, multiplication by a constant `c` coprime to `m`, and key length `λ_m = ⌈λ / log m⌉` (logarithms base 2, §2, p. 3).
§4.2, p. 6: each wire has its own modulus, and a projection gate costs `m - 1` ciphertexts after choosing `W_j^0 = -H(g, W_i^{-τ}) - φ(-τ)Δ_n`.
Figure 1, p. 7: the garbling scheme for mixed-moduli simple circuits, in which all ciphertexts of a projection gate use that gate's tweak.
§4.3, p. 7: the oracle `O(g, i, j, X, a, c) = H(g, X + aΔ_{m_i}) + cΔ_{m_j}`, Definition 1 (mixed-modulus circular correlation robustness against polynomial-time adversaries that query their oracle on distinct `g` values and `a ≠ 0`) and Theorem 1.
Proof sketch of Theorem 1, pp. 7–8: it replaces every ciphertext with `a ≠ 0` using only the oracle of Definition 1, hence with `m - 1` queries under one tweak, and states the authenticity bound `1 / 2^λ` (p. 8).
Moduli are not restricted to primes: the gadgets use mod-`(b + 1)` wires (§5, p. 8), output modulus `k + 1` (§6.2, p. 11) and `Z_{p+q-1}` (§6.3, pp. 12–13).
§4.3 does not analyse zero divisors of composite moduli.
An earlier pass read the ePrint text on 2026-11-09.

<a id="bmr90"></a>
## bmr90

Donald Beaver, Silvio Micali, Phillip Rogaway.
"The Round Complexity of Secure Protocols."
*Proceedings of the 22nd Annual ACM Symposium on Theory of Computing (STOC '90)*, 503–513, 1990. https://doi.org/10.1145/100216.100287 . Bibliographic data from the DOI record and secondary listings, cited as the usual source of the point-and-permute technique.
The full text was not inspected in this pass.

<a id="bodlaenderdowneyfellowshermelin2009"></a>
## bodlaenderdowneyfellowshermelin2009

Hans L. Bodlaender, Rodney G. Downey, Michael R. Fellows and Danny Hermelin.
"On Problems without Polynomial Kernels."
*Journal of Computer and System Sciences* 75(8), 423–434, 2009. https://doi.org/10.1016/j.jcss.2009.04.001 . Bibliographic data from the reference list of [Bodlaender, Jansen and Kratsch](#bodlaenderjansenkratsch2014), item [4].
The paper was not inspected; the manual cites it only through that paper's attribution of the k-Path kernel lower bound (Section 1, p. 2 of arXiv v1), and no theorem number is used.

<a id="bodlaenderjansenkratsch2014"></a>
## bodlaenderjansenkratsch2014

Hans L. Bodlaender, Bart M. P. Jansen and Stefan Kratsch.
"Kernelization Lower Bounds by Cross-Composition."
*SIAM Journal on Discrete Mathematics* 28(1), 277–305, 2014. https://doi.org/10.1137/120880240 . Inspected the arXiv version [1206.5941v1](https://arxiv.org/abs/1206.5941v1) on 2026-11-08: Definition 1 (kernelization, generalized kernelization, p. 4), Definition 2 (compression, p. 5), Proposition 1 (p. 5), Definition 4 (weak OR-distillation, p. 5), Theorem 2 (Fortnow–Santhanam, p. 6), Lemma 1 (complementary witness lemma, attributed to Dell and van Melkebeek, p. 7), Definition 8 (polynomial equivalence relation, p. 8), Definition 9 (and/or-cross-composition, p. 8), Theorem 5 and Corollary 2 (p. 9), Theorem 6 with its proof (pp. 10–11), the attribution of the k-Path kernel lower bound in Section 1 (p. 2) and the equivalence relation in the proof of Theorem 7 (p. 13).
Locators follow that arXiv numbering; the journal numbering was not checked.

<a id="borodin72"></a>
## borodin72

Allan Borodin.
*Computational Complexity and the Existence of Complexity Gaps*.
Journal of the ACM 19(1), 158–174, 1972. https://doi.org/10.1145/321679.321691 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the gap theorem and the almost-everywhere class convention to this paper.

<a id="borodinelyaniv98"></a>
## borodinelyaniv98

Allan Borodin, Ran El-Yaniv.
*Online Computation and Competitive Analysis*.
Cambridge University Press, 1998.
The chapter outline, in particular Chapter 1 on list accessing, comes from the publisher's table of contents; the book text was not inspected in this pass.
The manual cites it only as a textbook pointer for ski rental and for the deterministic list-accessing lower bound, with no theorem numbers.

<a id="borowskygafni1993"></a>
## borowskygafni1993

Elizabeth Borowsky and Eli Gafni.
"Generalized FLP Impossibility Result for t-Resilient Asynchronous Computations."
*Proceedings of the 25th Annual ACM Symposium on Theory of Computing (STOC 1993)*, 91–100, 1993. https://doi.org/10.1145/167088.167119 . Bibliographic metadata verified via DOI/DBLP and cross-checked in [borowskygafni1997](#borowskygafni1997) and [herlihyshavit1999](#herlihyshavit1999) on 2026-11-22 UTC; the paywalled conference PDF was not directly inspected, so no internal section, theorem or page locator is asserted.
Cited by [SetAgreement/ImmediateSnapshot.lean](../CslibFrontier/Computability/Distributed/SetAgreement/ImmediateSnapshot.lean) and [SetAgreement/Impossibility.lean](../CslibFrontier/Computability/Distributed/SetAgreement/Impossibility.lean).

<a id="borowskygafni1997"></a>
## borowskygafni1997

Elizabeth Borowsky and Eli Gafni.
"A Simple Algorithmically Reasoned Characterization of Wait-Free Computations (Extended Abstract)."
*Proceedings of the Sixteenth Annual ACM Symposium on Principles of Distributed Computing (PODC 1997)*, 189–198, 1997. https://doi.org/10.1145/259380.259439 ; author-hosted PostScript https://web.cs.ucla.edu/~eli/eli/podc2col.ps . Inspected the 10-page author-hosted PostScript (SHA-256 `405f4c23f7912550cd304009f69262ddede4b333e323165880abc3fe9aafc325`; proceedings pagination 189–198 taken from the bibliographic record) on 2026-11-22 UTC: Section 3.4 ("Immediate Snapshot Model", PS p. 5, ordered-partition `WriteRead` schedules), Section 3.5 ("Iterated Immediate Snapshot Model", PS pp. 5–6, one-shot immediate snapshot conditions 1–3 of self-inclusion, containment, and immediacy, and the iterated full-information view recurrence), and Section 3.6 ("Characterization of the b-shot Iterated Immediate Full-Information Protocol", PS p. 6, Lemmas 3.2–3.3 and Proposition 3.1).
Cited by [SetAgreement/ImmediateSnapshot.lean](../CslibFrontier/Computability/Distributed/SetAgreement/ImmediateSnapshot.lean) and [SetAgreement/Impossibility.lean](../CslibFrontier/Computability/Distributed/SetAgreement/Impossibility.lean); Section 4's emulation of atomic snapshot memory by iterated immediate snapshot memory remains open in [#7504](https://github.com/cslib-community/cslib-frontier/issues/7504).

<a id="bouillaguetetal25"></a>
## bouillaguetetal25

Charles Bouillaguet, Thibauld Feneuil, Jules Maire, Matthieu Rivain, Julia Sauvage and Damien Vergnaud.
*Multivariate Commitments and Signatures with Efficient Protocols*.
Cryptology ePrint Archive, Paper 2025/2035 (`BouillaguetEtAl2025`), https://eprint.iacr.org/2025/2035 . Checked directly on 2026-11-25 UTC against the 51-page ePrint PDF (ModDate 2025-11-03, SHA-256 `6fe3531109ca6c9363da53f65f53253f5a619ecbfabb0a7284c829f2beae2eea`; printed page numbers match PDF page numbers): Section 6.1 ("Parameters selection", printed pp. 21–22, Table 3 "Parameter sets for the MQ-commitment with q = 256" on printed p. 22, containing `k = 32, n = 83, m = 131`); Section 7 (starting on printed p. 23) and Section 7.2 (printed pp. 27–28, informal blind-signature security reduction and Theorem 5); Appendix A, Definition 12 ("One-More Claw-Freeness", printed p. 38, sampling uniform `J ← MQ(q, n, m)` and granting an arbitrary-target inversion oracle `O_Invert(H^{-1}, ·)` while requiring `q(κ) + 1` claws with distinct `H(x_i) = J(z_i)`); and Appendix D.1, proof of Theorem 5 (printed p. 50, informally applying `ℓ+1`-claw-freeness to `(x, y) ↦ (x + F(y), H(y))`).
Cited by [ACTMQ.lean](../CslibFrontier/Crypto/Protocols/AnonymousToken/ACTMQ.lean) (`#7068`), which formalizes the structured-target one-more claw-freeness game for `(F r + μ, G r)` with a distinct-target dedup budget and an explicit `gCollisionExperiment` binding term.

<a id="bracha1987"></a>
## bracha1987

Gabriel Bracha.
"Asynchronous Byzantine Agreement Protocols."
*Information and Computation* 75(2), 130–143, 1987. https://doi.org/10.1016/0890-5401(87)90054-X . Bibliographic metadata checked via secondary indexes on 2026-11-21 UTC; the full journal text was not inspected, so no numbered section or theorem locator is asserted.
Cited by [AsyncByzantine/Basic.lean](../CslibFrontier/Computability/Distributed/AsyncByzantine/Basic.lean), [AsyncByzantine/Impossibility.lean](../CslibFrontier/Computability/Distributed/AsyncByzantine/Impossibility.lean) and [AsyncByzantine/Bracha.lean](../CslibFrontier/Computability/Distributed/AsyncByzantine/Bracha.lean) (which formalizes the streamlined three-phase `initial`/`echo`/`ready` rule where `echo` is emitted only upon receiving `initial` from `dealer`).

<a id="brachatoueg1985"></a>
## brachatoueg1985

Gabriel Bracha and Sam Toueg.
"Asynchronous Consensus and Broadcast Protocols."
*Journal of the ACM* 32(4), 824–840, 1985. https://doi.org/10.1145/4221.214134 . Bibliographic metadata checked via secondary indexes on 2026-11-21 UTC; the full journal text was not inspected, so no numbered section or theorem locator is asserted.
Cited by [AsyncByzantine/Basic.lean](../CslibFrontier/Computability/Distributed/AsyncByzantine/Basic.lean), [AsyncByzantine/Impossibility.lean](../CslibFrontier/Computability/Distributed/AsyncByzantine/Impossibility.lean) and [AsyncByzantine/Bracha.lean](../CslibFrontier/Computability/Distributed/AsyncByzantine/Bracha.lean) for the asynchronous authenticated Byzantine message-passing model and the `n > 3t` resilience threshold.

<a id="bregman73"></a>
## bregman73

L. M. Brégman.
"Some properties of nonnegative matrices and their permanents."
*Soviet Mathematics Doklady* 14, 945–949, 1973; translated from *Doklady Akademii Nauk SSSR* 211, 27–30, 1973.
Bibliographic data from secondary sources; the paper was not inspected.
The manual credits it only with the statement of the bound `per A ≤ ∏ i, (r i)! ^ (1 / r i)` for 0/1 matrices.

<a id="brier50"></a>
## brier50

Glenn W. Brier.
"Verification of Forecasts Expressed in Terms of Probability."
*Monthly Weather Review* 78(1), 1–3, 1950 (bibliography key `Brier1950`). https://doi.org/10.1175/1520-0493(1950)078<0001:VOFEIT>2.0.CO;2 . Bibliographic metadata checked via DOI and catalogue records; the 1950 article PDF was not directly inspected, so internal equation, section and page locators are marked `unverified` in the results registry.
Cited at paper level in [ScoringRules.lean](../CslibFrontier/GameTheory/PredictionMarket/ScoringRules.lean) as the primary origin of the quadratic (Brier) probability score alongside [friedmanresnicksami07](#friedmanresnicksami07).

<a id="broder97"></a>
## broder97

Andrei Z. Broder.
“On the Resemblance and Containment of Documents.”
*Proceedings of Compression and Complexity of Sequences 1997* (SEQUENCES 1997), IEEE, 21–29. https://doi.org/10.1109/SEQUEN.1997.666900 . DOI and metadata as reported by search indexes; neither the DOI nor the full text was resolved in this pass (no connection to the publisher).
The manual credits it with the MinHash identity `Pr[min σ(A) = min σ(B)] = |A ∩ B|/|A ∪ B|` for a uniform permutation, which secondary sources attribute to it.

<a id="brown1966"></a>
## brown1966

William G. Brown.
"On Graphs That Do Not Contain a Thomsen Graph."
*Canadian Mathematical Bulletin* 9(3), 281–285, 1966. https://doi.org/10.4153/CMB-1966-036-2 ; PDF https://web.vu.lt/mif/s.jukna/Knizka/Brown.pdf . Inspected the 5-page article PDF (pp. 281–285, SHA-256 `ff5a85c14c64cebc4d71a5054eee9a63449dc365299cd36fad8026a8b4d81e94`) on 2026-11-23 UTC for §2 (pp. 282–283): equation `(2.1)` defines the graph `G` on the `p^3` points of `EG(3, p)` with `y ∈ S(x)` iff `∑_{i=1}^3 (x_i - y_i)^2 = α`, where `α ∈ GF(p)` is chosen to be a nonzero quadratic residue when `p ≡ 3 (mod 4)` (so `α = 1` is an allowed radius parameter), giving `|S(x)| = p^2 - p` and `(p^5 - p^4)/2` undirected edges, and the radical-plane reduction `(2.2)` together with `(2.3) LEMMA` ("No three points of `S(x)` are collinear", p. 283) prove that `G` contains no `K_{3,3}`.
[BrownMatrix.lean](../CslibFrontier/Foundations/Combinatorics/BrownMatrix.lean) specializes equation `(2.1)` at `α = 1` (`Cslib.brownMatrix` over `Fin 3 → ZMod p` for primes `p ≡ 3 (mod 4)`), so each row of the `p^3 × p^3` adjacency matrix has `p^2 - p = p(p - 1)` ones and the matrix weight `p^5 - p^4 = p^4(p - 1)` is twice Brown's undirected edge count `(p^5 - p^4)/2`.

<a id="bs23"></a>
## bs23

Dan Boneh and Victor Shoup.
*A Graduate Course in Applied Cryptography*, version 0.6, January 2023. https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf . Title, authors and edition verified from the primary PDF during independent source review on 2026-11-02.
On 2026-11-22 UTC `BonehShoup_0_6.pdf` (SHA-256 `67bc4507f7558c99f0ecc331651da224f0a73b2453fdd8ff5e67c8d4e56cc7dd`) was also checked directly for Section 6.2 (Attack Game 6.2 and Theorem 6.1, printed pp. 220–223 / PDF pp. 236–239: Attack Game 6.2 on PDF p. 237, Theorem 6.1 and proof on PDF pp. 237–239) and Section 6.14 (Exercise 6.2, printed p. 246 / PDF p. 262), and on 2026-11-23 UTC for Sections 9.2.2–9.2.3 (Attack Game 9.2 on printed p. 362 / PDF p. 378 and the remark after Theorem 9.1 on printed p. 363 / PDF p. 379) and Section 9.13 (Exercise 9.12(a) on printed p. 394 / PDF p. 410 and Exercise 9.15 on printed p. 395 / PDF p. 411).
On 2026-11-24 UTC `BonehShoup_0_6.pdf` (same SHA-256) was also checked directly for Section 15.4 (equation (15.8), printed p. 625), Section 15.5.1 (Attack Game 15.1 and Definition 15.3 on printed p. 628; Theorem 15.1 and equation (15.9) on printed pp. 628–629), and Section 15.6.3.2 (Attack Game 15.8 and Definition 15.12 on printed pp. 649–650).
For `CslibFrontier.Crypto.Computational.CBCMAC`, checked on 2026-11-22 against `BonehShoup_0_6.pdf` (SHA-256 `67bc4507f7558c99f0ecc331651da224f0a73b2453fdd8ff5e67c8d4e56cc7dd`): Section 4.4.1 (Attack Game 4.2 and Definition 4.2, printed pp. 132–133), Section 4.6.1 (Definition 4.5, printed p. 152), Section 6.1 (Attack Game 6.1 and Definition 6.2, printed pp. 218–219), Section 6.3 (Theorem 6.2, printed p. 224), Section 6.4.1 (Figure 6.3a, Theorem 6.3, and equation (6.7), printed pp. 226–229), Section 6.4.3 (CBC extension attack, printed pp. 230–231), and Sections 6.6–6.6.1 (Theorem 6.8 and Method 1, printed pp. 235–236).
Other detailed textbook locator claims remain attributed to the Lean source docstrings; no complete textbook correspondence audit was performed.

<a id="bt06"></a>
## bt06

Andrej Bogdanov and Luca Trevisan.
*Average-Case Complexity*.
Foundations and Trends in Theoretical Computer Science 2(1), 1–106, 2006. https://doi.org/10.1561/0400000004 ; arXiv:cs/0606037.
Definition, lemma and theorem numbers (Definitions 1, 2, 6, 8–11 and 17, Proposition 7, Lemma 18, Theorem 19, Claim 20) were checked against the arXiv text on 2026-11-07.

<a id="budish11"></a>
## budish11

Eric Budish.
"The Combinatorial Assignment Problem: Approximate Competitive Equilibrium from Equal Incomes."
*Journal of Political Economy* 119(6), 1061–1103, 2011. https://doi.org/10.1086/664613 . Bibliographic metadata checked via DOI/search records on 2026-11-24 UTC; the journal text was not inspected on disk, so no internal page or theorem locator is claimed.
Cited (`Budish2011`) for the `EF1` (envy-free up to one good) fairness notion (`MonotoneValuation.IsEF1`).

<a id="bulowklemperer96"></a>
## bulowklemperer96

Jeremy Bulow and Paul Klemperer.
"Auctions Versus Negotiations."
*The American Economic Review* 86(1), 180–194, 1996.
Bibliographic metadata only, as given in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #6, reference [1] (p. 7).
The paper's text was not inspected, so no locator in it is cited; the prior-independent `(n + 1)`-bidder Vickrey revenue theorem is proved following [roughgarden13cs364a](#roughgarden13cs364a), Lecture #6, Theorem 4.1 (p. 6).

<a id="bunsteinke16"></a>
## bunsteinke16

Mark Bun and Thomas Steinke.
"Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds."
*Theory of Cryptography (TCC 2016-B, Part I)*, Lecture Notes in Computer Science 9985, 635–658, Springer, 2016. https://doi.org/10.1007/978-3-662-53641-4_24 ; preprint arXiv:1605.02065v1, https://arxiv.org/abs/1605.02065v1 . Checked against the arXiv:1605.02065v1 LaTeX source (`main.tex`, SHA-256 `5bf5affdf21fa0b5fe2bdd6c1056220c58ceed1cf8ea18b3234eb271c9728dcc`) on 2026-11-22: §1.2.1 Proposition 1.4 (`prop:PDPtoCDP-intro`), §2 Definition of Rényi divergence `D_α(P ‖ Q)` and Lemma `lem:Renyi`, and §3.1 Proposition 3.3 (`prop:EpsSquared`: if `D_∞(P ‖ Q) ≤ ε` and `D_∞(Q ‖ P) ≤ ε`, then `D_α(P ‖ Q) ≤ α ε² / 2` for all `α > 1`).
LNCS volume, page numbers, and DOI were taken from the bibliographic record.

<a id="burnslynch1993"></a>
## burnslynch1993

James E. Burns and Nancy A. Lynch.
"Bounds on Shared Memory for Mutual Exclusion."
*Information and Computation* 107(2), 171–184, December 1993. https://doi.org/10.1006/inco.1993.1065 ; author-hosted copy: https://groups.csail.mit.edu/tds/papers/Lynch/ic93.pdf . Checked against that copy on 2026-11-22 UTC (SHA-256 `fdcaaa7c282e9c3c35b6dc3b581df152fab321c46448d872a9721f46285bbe11`, 14 pages, printed pp. 171–184): §2 "Read/Write Systems" (pp. 172–174: `S = (P, V, q₀, φ)` with remainder, trying, critical, and exit regions `Rᵢ, Tᵢ, Cᵢ, Eᵢ`, single-variable reads and blind writes, and fair histories stepping every process outside `Rᵢ` infinitely often), §3 "Mutual Exclusion with Global Progress" (pp. 174–175: mutual exclusion and global progress as a region change in every nonnull fair history), and §5 "The Lower Bound" (pp. 177–183: Theorem 5.1 on p. 177 stating `|V| ≥ |P|` for `|P| ≥ 2`, "looks like" Definition 5.1 and indistinguishability Lemma 5.2 on p. 177, obliterated/hidden Definitions 5.2–5.3 and Lemma 5.3 on pp. 178–179, "covered" Definition 5.4 on p. 179, covering-write Lemma 5.4 on p. 180, and nullification Definition 5.5 and Lemma 5.5 on pp. 180–183).
Cited for `not_deadlockFreeMutex_of_single_register` in `CslibFrontier/Computability/Distributed/MutualExclusion/FilterLock.lean`, an intermediate 1-register base step (`2 ≤ Fintype.card P`, `Fintype.card Reg ≤ 1`) toward Theorem 5.1 (#7296) that uses one poised blind write to erase another process's writes (specializing Lemmas 5.2 and 5.4) under `MutexProtocol.DeadlockFree` (which asks for some process to reach `.cs` from an initially trying state under `WeakFair` — scheduling `.trying` and `.exit` — and `CSEventuallyExits`, whereas Burns–Lynch asks for a region change in each nonnull fair history).

<a id="burrowswheeler94"></a>
## burrowswheeler94

Michael Burrows and David J. Wheeler.
*A Block-sorting Lossless Data Compression Algorithm*.
SRC Research Report 124, Digital Systems Research Center, Palo Alto, 10 May 1994.
Openly hosted copy: https://www.cs.jhu.edu/~langmea/resources/burrows_wheeler.pdf . On 2026-11-08 UTC the worker checked the following against that copy: Section 2, Algorithm C (steps C1–C2, with `I` the first row equal to `S`, numbered from zero) and Algorithm D (steps D1–D3), the running example `S = abraca`, `L = caraab`, `I = 1`, `T = (4 0 5 1 2 3)`, the remark after D3 on periodic `S`, and Section 4.2 (the arrays `C` and `P`, with `T[i] = P[i] + C[L[i]]`).
The HP Labs copy of the report could not be reached (connection failure), so it was not compared.

<a id="canetti20"></a>
## canetti20

Ran Canetti.
*Universally Composable Security*.
Journal of the ACM 67(5), Article 28, 2020; full version Cryptology ePrint Archive 2000/067. https://doi.org/10.1145/3402457 . Locators for the static-UC definitions refer to the ePrint revision of February 11, 2020 (106 pages; printed page = PDF page − 3), read through the Internet Archive copy https://web.archive.org/web/20260904164957id_/https://eprint.iacr.org/2000/067.pdf (SHA-256 `0466f041f546ce6db5e86c7ec81ea12604c4bea6c944b73b4eeac8457564703a`, first recorded in [#5680](https://github.com/cslib-community/cslib-frontier/pull/5680); its SHA-1 matches the archive's digest for that capture); the JACM version was not inspected for those static-UC locators, and its numbering may differ.
For adaptive corruptions in `Protocols/UC/Adaptive.lean`, `Protocols/UC/AdaptiveToStatic.lean`, and `Protocols/UC/AdaptiveDummyAdversary.lean`, the JACM version (pagination `28:1`–`28:94`) Section 7.1 (JACM pp. 28:69–70; ePrint p. 74), Section 7.1.1 (JACM p. 28:71), Section 7.2 (JACM pp. 28:73–74), JACM p. 28:15, and Claim 11 (JACM p. 28:43) were checked for adaptive corruptions, static-corruption restriction, the corruption-status query, standard PID-wise ideal-functionality corruption, and dummy-adversary completeness; the formalization provides a call-bounded statistical snapshot corruption model (`P.view` snapshots of every party after each inner activation, where `P.view` is arbitrary and may hide stored coins, and global inner-activation counts are exposed; Canetti §7.1.1's write-once storage restriction, mandatory coin exposure, per-party activation granularity, PPT time bounds, and adaptive composition stay open).
For fixed-arity multi-session composition in [Protocols/UC/MultiSession.lean](../CslibFrontier/Crypto/Protocols/UC/MultiSession.lean), Section 6.1 Theorem 22 (JACM p. `28:58`; ePrint p. `61`), Corollaries 23 and 24 (JACM p. `28:59`; ePrint p. `62`), and Section 6.3 (JACM p. `28:67`; ePrint p. `70`) were checked; this adapts them to a fixed finite `Fin m` session family in the static-corruption, call-bounded model, and dynamic `SID` creation and full Theorem 22 stay open.

<a id="canettirabin03"></a>
## canettirabin03

Ran Canetti and Tal Rabin.
*Universal Composition with Joint State*.
Advances in Cryptology -- CRYPTO 2003, Lecture Notes in Computer Science, vol. 2729, Springer, pp. 265--281, 2003. https://doi.org/10.1007/978-3-540-45146-4_16 . Checked against the CRYPTO 2003 proceedings version by named section and theorem: §3, "The Composition Operation" (`π^[ρ̂]`), §3, "The Multi-session Extension of an Ideal Functionality" (`F̂`), Theorem 1 (Universal Composition with Joint State), and the proof of Theorem 1 (definition of `π̃` and item 3 of the proof); Cryptology ePrint Archive 2002/047 was not inspected.
In [Protocols/UC/JointState.lean](../CslibFrontier/Crypto/Protocols/UC/JointState.lean), the lazy multi-session functionality `IdealFunctionality.multiSession` quantifies over an arbitrary `SSID` with `DecidableEq` and initializes each selected copy on first touch, while `MultiHybridProtocol.toJoint`, `jointDemux`, `jointMux`, and the fixed-session `EmulatesWithin` proof steps target a fixed finite `Fin m` sub-session family over a single joint-state sub-protocol in the static-corruption, pull-only, call-bounded model; separately, the generic lazy-vs-eager parallel-package equivalence `SSP.run_parFinLazy_eq_parFin` in [Protocols/SSP/ParFinLazy.lean](../CslibFrontier/Crypto/Protocols/SSP/ParFinLazy.lean) is restricted to a fixed finite `Fin m` session family.
Unlike the source's `F̂` (which sends `(sid, ssid, v)` to `Pi` and sends `ssid` to the adversary whenever a copy sends `(ssid, v)`), `IdealFunctionality.multiSession` returns an untagged `Option SubOut` on the selected pull and provides an explicitly queried backdoor interface (`SubSessionBackdoor`) returning BackR, exposing no raw copy state; no implication between `Realizes` for this pull API and the source premise is claimed.
Full `Realizes` composition, environment-budgeted dynamic-session composition, adaptive corruptions, and push-semantics `F̂` stay open.

<a id="canonne22"></a>
## canonne22

Clément L. Canonne.
*Topics and Techniques in Distribution Testing: A Biased but Representative Sample*.
Foundations and Trends in Communications and Information Theory 19(6), 1032–1198, 2022. https://doi.org/10.1561/0100000114 . Checked on 2026-11-10 against the author-hosted draft dated March 10, 2024 at https://ccanonne.github.io/files/misc/main-survey-fnt.pdf (journal pagination not inspected; locators follow that March 10, 2024 draft): Appendix B (pp. 149–152: Definition B.1, `(B.1)`–`(B.3)`, `(B.5)`–`(B.6)`, Lemmas B.1, B.2, and B.5) for Hellinger/`χ²`/KL definitions, tensorization, and comparison inequalities, and Section 3.1 (pp. 99–103: `(3.3)`, Lemma 3.1, and `(3.10)`) for the `√(2n)` Hellinger i.i.d. bound and Ingster's mixture second-moment identity (`CslibFrontier/Probability/{Hellinger,ChiSquare}.lean`).

<a id="carmosinoimpagliazzokabanetskolokolova2016"></a>
## carmosinoimpagliazzokabanetskolokolova2016

Marco L. Carmosino, Russell Impagliazzo, Valentine Kabanets and Antonina Kolokolova.
*Learning Algorithms from Natural Proofs*. 31st Conference on Computational Complexity (CCC 2016), LIPIcs 50, 10:1–10:24, 2016. https://doi.org/10.4230/LIPIcs.CCC.2016.10 . Checked on 2026-11-11 against the LIPIcs PDF: Section 2.4, Definitions 2.8–2.10, Theorem 2.11 and the sketch of the reconstruction algorithm that follows it (p. 10:9), which `CslibFrontier/MachineLearning/UniformLearning/NisanWigderson.lean` follows for one run.
For the AC⁰[2] efficiency of their generator ([#4451](https://github.com/cslib-community/cslib-frontier/issues/4451)), also checked on 2026-11-11 against the LIPIcs PDF: Definition 3.1, Theorems 3.2 and 3.3 (p. 10:10) and the proof of Theorem 3.2 (p. 10:11); Definition 3.4 (black-box amplification, pp. 10:10–10:11) and Lemma 3.5 (p. 10:11); Section 3.1, which opens on p. 10:11 with the design requirements; Theorem 3.6 and its proof (pp. 10:12–10:13), which define the polynomials `A_i` and the sets `S_i`, bound their overlap on p. 10:12 and end with the hard-coded matrix `M_{j,k} = r_j^k`; Theorem 3.7 and its proof (p. 10:13); and Theorem 4.3 (p. 10:15) with its proof (pp. 10:15–10:16).
`CslibFrontier/Crypto/Primitives/PRG/NisanWigderson/{BitPolynomial,MXCircuit,AmpGeneratorCircuit}.lean` and `CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/{GLAmp,GLAmpCircuit}.lean` follow them for `p = 2`.
For the reconstruction for `p = 2`, also checked on 2026-11-11 against the LIPIcs PDF: Theorem 4.1 (p. 10:14); Theorem 4.2 and the sketch of its algorithm (p. 10:15); and Claim 4.4 (p. 10:15), whose proof and the combination with Theorem 4.1 that ends the proof of Theorem 4.3 follow on pp. 10:15–10:16.
`CslibFrontier/Computability/Circuit/Boolean/HardnessAmplification/GLAmpDecode.lean` and `CslibFrontier/MachineLearning/UniformLearning/CIKK/Amplification.lean` follow them.
For the `p = 2` natural property and the learner built from it, also checked on 2026-11-11 against the LIPIcs PDF, by an agent in the [M6.7 gate note](https://github.com/cslib-community/cslib-frontier/issues/4451#issuecomment-6791276714): Theorems 5.1 and 5.3 (p. 10:19) and the sketch of the `p = 2` rank property (p. 10:20).
`CslibFrontier/Computability/Circuit/Boolean/Razborov/RankProperty.lean` follows that sketch in a variant, and `CslibFrontier/MachineLearning/UniformLearning/CIKK/Learner.lean` follows Theorem 5.1 in a per-function black-box form.

<a id="castroliskov1999"></a>
## castroliskov1999

Miguel Castro and Barbara Liskov.
"Practical Byzantine Fault Tolerance."
In *Proceedings of the Third Symposium on Operating Systems Design and Implementation (OSDI '99)*, 173–186, USENIX Association, February 1999.
USENIX proceedings PostScript: https://www.usenix.org/legacy/publications/library/proceedings/osdi99/full_papers/castro/castro.ps . Checked on 2026-11-22 UTC against `castro.ps` (SHA-256 `4920113c97e7e95ee3468f88178e6a1d6480f4b052ea13ceaa3e16b590bf9453`, 14 pages numbered internally 1–14): Section 2 (p. 2, asynchronous Byzantine message-passing model with cryptographic authentication and resilience bound $n \ge 3f + 1$, $f = \lfloor(n - 1)/3\rfloor$), Section 3 (pp. 2–3, deterministic state-machine replication safety and conditional liveness under bounded eventual delay), Sections 4.1–4.2 (pp. 3–5, normal-case three-phase `PRE-PREPARE`, `PREPARE` and `COMMIT` protocol, `prepared(m, v, n, i)` requiring `PRE-PREPARE` plus $2f$ matching backup `PREPARE`s, and `committed-local(m, v, n, i)` requiring `prepared` plus $2f + 1$ matching `COMMIT`s), Section 4.3 (pp. 5–6, `CHECKPOINT` garbage collection and low/high watermarks $h$, $H$), Section 4.4 (p. 6, `VIEW-CHANGE(v + 1, n, C, P, i)` carrying prepared certificates $P$ and `NEW-VIEW(v + 1, V, O)` carrying $2f + 1$ valid `VIEW-CHANGE` messages $V$ and re-proposed `PRE-PREPARE`s $O$ across `min-s`..`max-s` selecting the highest-view prepared request or `null` no-op for gaps), Sections 4.5.1–4.5.2 (pp. 6–7, within-view non-equivocation, cross-view commit preservation via intersection of $2f + 1$ `VIEW-CHANGE` messages with $f + 1$ non-faulty prepared replicas, and synchronized-view liveness), and Section 5 (pp. 7–9, message digests $D(m)$ and MAC authenticators).
Cited as the primary target for the ideal-authentication checkpoint-free multi-slot step in [PBFT.lean](../CslibFrontier/Computability/Distributed/ByzantineQuorum/PBFT.lean) (`preparedCert_unique_idealAuth`, `committedLocal_preserves_higher_prepared_idealAuth`, `pbft_commit_agreement_idealAuth`, `pbft_smr_state_agreement_idealAuth`, `pbft_honest_primary_three_phase_liveness_idealAuth`, paired with an original `Fin 3`, $f = 1$ split-brain counterexample `exists_pbft_splitBrain_fin3` under `#7506`), which generalizes the quorum threshold from $2f + 1$ at $n = 3f + 1$ to `pbftQuorumSize P f = |P| - f` for arbitrary $3f < |P|$, enforces sender non-forgery structurally via `PBFTMsg.signer` rather than Section 5 cryptographic MACs/digests, sets `min-s = 0` without Section 4.3 `CHECKPOINT` watermarks, and proves conditional 3-phase liveness for an already-synchronized honest view rather than Section 4.5.2's exponential-backoff view-change timer synchronization.

<a id="castroliskov2002"></a>
## castroliskov2002

Miguel Castro and Barbara Liskov.
"Practical Byzantine Fault Tolerance and Proactive Recovery."
*ACM Transactions on Computer Systems* 20(4), 398–461, November 2002. https://doi.org/10.1145/571637.571640 . Bibliographic metadata checked on 2026-11-22 UTC; the ACM journal text was not inspected, so no internal section, theorem or page locator from the 2002 article is asserted (all PBFT protocol and proof locators in [PBFT.lean](../CslibFrontier/Computability/Distributed/ByzantineQuorum/PBFT.lean) refer to [castroliskov1999](#castroliskov1999)).

<a id="ccpv11"></a>
## ccpv11

Gruia Călinescu, Chandra Chekuri, Martin Pál, Jan Vondrák.
“Maximizing a Monotone Submodular Function subject to a Matroid Constraint.”
*SIAM Journal on Computing* 40(6), 1740–1766, 2011. https://doi.org/10.1137/080733991 . The `p`-system definition and the greedy ratios `1/p` (modular) and `1/(p+1)` (monotone submodular) in Section 1, and the proof of the `1/(p+1)` bound in Appendix B (“Analysis of Greedy for p-systems”), were checked on 2026-11-08 against the authors' manuscript dated September 21, 2009, at https://theory.stanford.edu/~jvondrak/data/submod-matroid.pdf ; the journal pagination was not checked.
The manual reports the original Fisher–Nemhauser–Wolsey and Jenkyns attributions as stated in this paper.

<a id="cdpw07"></a>
## cdpw07

Ran Canetti, Yevgeniy Dodis, Rafael Pass and Shabsi Walfish.
*Universally Composable Security with Global Setup*.
TCC 2007, Lecture Notes in Computer Science 4392, 61–85; full version Cryptology ePrint Archive 2006/432. https://doi.org/10.1007/978-3-540-70936-7_4 . The primary text was not inspected, and no theorem number is claimed.
The manual attributes to this paper only the setting of sessions that share a global functionality which the environment also queries directly.

<a id="cf01"></a>
## cf01

Ran Canetti and Marc Fischlin.
*Universally Composable Commitments*.
CRYPTO 2001, Lecture Notes in Computer Science 2139, 19–40, 2001; full version Cryptology ePrint Archive 2001/055. https://doi.org/10.1007/3-540-44647-8_2 . Section 2.2, Figure 2 (`F_com`, p. 10) and Section 3, Theorem 6 (p. 12) were checked against the full version, Cryptology ePrint Archive 2001/055.
The library proves an adaptation and special case of Theorem 6: one commitment message and one opening message, a constant completeness gap, a single simulator fixed before the environment, and call-counted (not machine-efficiency) bounds.
Theorem 6 for general bilateral protocols and the computational setting is not formalized.
Theorem 8 (p. 20, erasing parties) and Theorem 11 (p. 26, `UCCReUse`/`NotErase`, non-erasing parties) motivate the erasing vs. non-erasing distinction in `Protocols/UC/Adaptive.lean` (modeled via per-activation `P.view` snapshots rather than write-once memory); neither computational theorem is formalized (`CslibFrontierTests/Crypto/UCAdaptiveSeparation.lean` gives concrete separation witnesses for both `AdaptiveEmulatesWithin` and `AdaptiveEmulates`).

<a id="cgks98"></a>
## cgks98

Benny Chor, Oded Goldreich, Eyal Kushilevitz and Madhu Sudan.
*Private Information Retrieval*.
Journal of the ACM 45(6), 965–981, 1998; preliminary version FOCS 1995. https://doi.org/10.1145/293347.293350 . Definition 1 (§2.1, p. 4), the coalition `t`-privacy extension of §2.2 (pp. 4–5, and the polynomial family noted without construction in §1.1, pp. 1–2), the polynomial-time requirement of §2.4 (p. 6), the schemes of §§3.1, 3.2 and 3.4 (Proposition 4, Corollary 3; pp. 6–8, 11), the covering-code schemes of §3.3 (Theorem 1, Footnote 1 on exact covers, the `d = 5, k = 7` row of Figure 1, the radius-`2` covering remark `k · d · n ^ (1 / d) + k · C(d, 2) · n ^ (2 / d)`, and Corollary 2; pp. 8–10), the block-retrieval transformations and constant-overhead schemes of §4 (Propositions 4 and 5, the group-homomorphism note on p. 12, Corollaries 6, 7 and 8; pp. 11–13), the single-server bound of §5.1 in its one-round and interactive forms, and §5.2 (the Claim, its two observations and the closing note on the even-set scheme) were checked on 2026-11-08, 2026-11-11 and 2026-11-12 against the authors' journal version of April 21, 1998, at http://people.csail.mit.edu/madhu/papers/1995/pir-journ.pdf (§5 is on pp. 13–15).
In [PIR/GeneralCover.lean](../CslibFrontier/Crypto/Protocols/PIR/GeneralCover.lean), Theorem 1 (`hasIndexedScheme_of_hammingDist`) states explicit `0 < |D|` and `Function.Injective code` hypotheses (`d - 1` truncates at `d = 0` in `ℕ`, and duplicate codewords would violate `k ≤ 2 ^ d`), while for radius-`2` covers `hasScheme_of_hammingDist_two` proves the full-ball count `k · (2 · d · ℓ + C(d, 2) · ℓ² + 1) = k · d · ℓ + k · C(d, 2) · ℓ² + k · (d · ℓ + 1)` (CGKS p. 10's displayed leading expression `k · d · ℓ + k · C(d, 2) · ℓ²` plus the `k · (d · ℓ + 1)` distance-`0`/`1` answer bits; the literal `k · d · ℓ + k · C(d, 2) · ℓ²` bound without lower-order answer terms is not proved) alongside the exact radius-`r` count `k · (d · ℓ + ∑_{j ≤ r} C(d, j) · ℓ ^ j)` and the coarser `d²` upper bound `k · d · ℓ + k · d² · ℓ²` (`hasScheme_of_hammingDist_two_sq`, for `2 ≤ |D|` and `1 ≤ ℓ`).
Because §1.1 omits the polynomial-interpolation construction while stating `O(t(n) · n ^ (1 / c))` for `c · t(n)` servers, [PIR/Shamir.lean](../CslibFrontier/Crypto/Protocols/PIR/Shamir.lean) formalizes an explicit finite-field adaptation over `Shamir.Params F S` that matches `k = c · t` servers and fixed-`t` exponent `n ^ (1 / c)` while retaining the field bit-width factor `⌈log₂ |F|⌉` (`|F| > c · t`, a weaker finite-field communication variant).
Neither polynomial-time computation (§2.4, p. 6; §3.3 Remark, p. 10) nor fair-coin simulation of finite-uniform `ProbComp` primitives is modeled.
In the interactive form, the user's output may depend on its coins, so the source's step that the same communication forces the same output is replaced by the rectangle property of protocols.
The typeset JACM PDF was not consulted; locators follow the authors' version.

<a id="chaitin74"></a>
## chaitin74

Gregory J. Chaitin.
*Information-Theoretic Limitations of Formal Systems*.
Journal of the ACM 21(3), 403–424, 1974. https://doi.org/10.1145/321832.321839 . Bibliographic metadata checked on 2026-11-08; the paper is behind the ACM paywall and was not inspected.
The manual attributes the incompleteness theorem for program-size complexity to it, following the customary attribution; its theorem numbers and the exact form of its bound are unverified.
The Lean docstrings also cite the textbook treatment in Li and Vitányi, *An Introduction to Kolmogorov Complexity and Its Applications*, 4th edition (Springer, 2019), Chapter 2; the section and theorem locator within that chapter was not checked.

<a id="chakrabarti25"></a>
## chakrabarti25

Amit Chakrabarti.
*Data Stream Algorithms: Lecture Notes*.
Dartmouth College, latest update July 1, 2025. https://www.cs.dartmouth.edu/~ac/Teach/data-streams-lecnotes.pdf . Locators checked against that PDF on 2026-11-07 UTC: Unit 1 (Section 1.1 for the MAJORITY and FREQUENT problems, Algorithm 1 and Theorem 1.3.1 for Misra–Gries, Exercise 1-1 for the `(m − m̂)/k` sharpening), Section 2.4 (the median trick) and Section 5.3 (Algorithms 7–8 and equations (5.1)–(5.7) for the Count-Sketch).

<a id="chandrahadzilacostoueg1996"></a>
## chandrahadzilacostoueg1996

Tushar Deepak Chandra, Vassos Hadzilacos and Sam Toueg.
"The Weakest Failure Detector for Solving Consensus."
*Journal of the ACM* 43(4), 685–722, July 1996 (preliminary version PODC 1992, pp. 147–158). https://doi.org/10.1145/234533.234549 . Checked firsthand on 2026-11-22 against the typeset JACM PDF (`https://www.cs.utexas.edu/~lorenzo/corsi/cs380d/papers/p685-chandra.pdf`, SHA-256 `d1068a5e16924fce1745cf96f85212035dad763907416776ea815626a7a685eb`; printed page `p` is PDF page `p - 684`): §§2.1–2.4 (pp. 689–692, failure patterns `F`, failure detector histories `H_D`, algorithms `A`, configurations, steps, runs `(F, H_D, I, S, T)`, and environments `E`), §§3–4 (pp. 692–693, the Consensus specification and distributed reducibility `D >=_E D'` via transformation algorithm `T_{D -> D'}`), §5 (p. 694, the eventual-leader failure detector `Omega` outputting a single trusted process `H_Omega(p, t) in Pi`, Theorem 5.1 reducing `Omega` to `<>W` via `output_p <- Pi - {q}`, Theorem 5.2 reducing any consensus-solving detector `D` to `Omega` for `n > 2f`, Corollary 5.3, and Theorem 5.4 establishing `<>W` as the weakest failure detector for Consensus when `n > 2f`), and §6 (pp. 694–712, the valence-DAG and simulation-forest extraction `T_{D -> Omega}`).
[FailureDetectors/Hierarchy.lean](../CslibFrontier/Computability/Distributed/FailureDetectors/Hierarchy.lean) formalizes `LeaderHistory`, `IsEventuallyLeader`, `LeaderHistory.toDetectorHistory`, and the pure history-map step `IsEventuallyLeader.toDetectorHistory_isEventuallyStrong` (`Omega -> <>S`, and hence `<>W`, after Theorem 5.1, p. 694); the asynchronous message-buffer automaton `(F, H_D, I, S, T)`, transformation automaton `T_{Omega -> <>W}`, and §6 necessity extraction `D -> Omega` remain open in [#7503](https://github.com/cslib-community/cslib-frontier/issues/7503).

<a id="chandrakozenstockmeyer1981"></a>
## chandrakozenstockmeyer1981

Ashok K. Chandra, Dexter C. Kozen and Larry J. Stockmeyer.
"Alternation."
*Journal of the ACM* 28(1), 114–133, January 1981 (preliminary versions in FOCS 1976, pp. 89–97 and 98–108). https://doi.org/10.1145/322234.322243 . Checked firsthand on 2026-11-23 against the 20-page typeset JACM PDF (`https://people.cs.umass.edu/~immerman/cs601/alternation.pdf`, SHA-256 `c3d33bbd4a6ba75cf681e4abc07ad9ad50036b39b14fc734e80da413671856f9`; printed page `p` is PDF page `p - 113`): Section 2 (pp. 116–122, Definitions 2.1–2.5 for alternating Turing machines with `{∧, ∨, ¬, accept, reject}` state labels, three-valued `{0, ⊥, 1}` least-fixed-point acceptance `l*`, finite-tree restriction Lemmas 2.1–2.3, negation elimination in Theorem 2.5 on pp. 120–121, and constructible halting-path clocking in Theorem 2.6 on pp. 121–122) and Section 3 (pp. 122–125, Theorem 3.1 `NSPACE(S(n)) ⊆ ⋃_{c > 0} ATIME(c · S(n)²)` for `S(n) ≥ n`, Theorem 3.2 `ATIME(T(n)) ⊆ DSPACE(T(n))` for `T(n) ≥ n` proved on p. 123 by postorder evaluation of `C(σ_M(x), T(n))` with the remark on pp. 123–124 noting that equipping alternating machines with random-access input indexing suffices in that proof to avoid writing the entire input in each reconstructed configuration and relax `T(n) ≥ n` to `T(n) ≥ log n`, Theorem 3.3 `ASPACE(S(n)) ⊆ ⋃_{c > 0} DTIME(c^{S(n)})` for `S(n) ≥ log n`, Theorem 3.4 `DTIME(T(n)) ⊆ ASPACE(c · log T(n))` for `T(n) ≥ n`, and Corollaries 3.5–3.6).
In [Alternating/DeterministicSpace.lean](../CslibFrontier/Computability/Machines/Turing/MultiTape/Alternating/DeterministicSpace.lean) and [Alternation/DeterministicSpace.lean](../CslibFrontier/Computability/Complexity/Classes/Alternation/DeterministicSpace.lean), `ATIME enc t` (`MultiTapeATM.DecidesInTime`) and `DSPACE enc s` (`MultiTapeTM.DecidableInTimeAndSpace`) use binary-alphabet halting deciders up to linear factors `c₁ * t n + c₂` and `c₁ * s n + c₂` rather than Definition 2.5's arbitrary-alphabet recognizers (whose proof on p. 123 removes constructibility by trying depths `T = 1, 2, …`, which can keep trying larger depths on rejected inputs); because every computation path of an `ATIME` decider halts within `c₁ * t n + c₂` moves, the evaluator halts on all inputs without computing `t`.
`ATIME_subset_DSPACE_of_le` (`ATIME t ⊆ DSPACE t` for `n ≤ t n`) maps to Theorem 3.2 in this binary halting-decider model, derived from `ATIME_subset_DSPACE` (`ATIME t ⊆ DSPACE (n + t n)`), the library's formulation for arbitrary `t` where `n` pays for copying the encoded input during sequential coin replay; Theorems 3.1 and 3.4 remain open in [#4086](https://github.com/cslib-community/cslib-frontier/issues/4086).

<a id="chandratoueg1996"></a>
## chandratoueg1996

Tushar Deepak Chandra and Sam Toueg.
"Unreliable Failure Detectors for Reliable Distributed Systems."
*Journal of the ACM* 43(2), 225–267, March 1996. https://doi.org/10.1145/226643.226647 . Checked firsthand on 2026-11-22 against the typeset JACM PDF (`https://www.cs.utexas.edu/~lorenzo/corsi/cs380d/papers/p225-chandra.pdf`, SHA-256 `f2c4b22a63e43c462286ce740e38528bac275d87e769d794bb830a434e1362cf`; printed page `p` is PDF page `p - 224`): §§2.1–2.4 and Figure 1 (pp. 231–234, monotone failure patterns `F(t) subseteq F(t+1)`, `crashed(F)`, `correct(F)`, failure detector histories `H : Pi x T -> 2^Pi`, Strong/Weak Completeness on p. 232, Strong/Weak Accuracy on pp. 232–233, Eventual Strong/Weak Accuracy and equivalence of the `Pi - F(t')` and `correct(F)` formulations on finite `Pi` on p. 233, and the eight classes `P, S, <>P, <>S, Q, W, <>Q, <>W` in Figure 1 on p. 234, where `Q` and `<>Q` are denoted solely by calligraphic symbols without English adjectives), §3 and Figure 3 (pp. 235–238, periodic suspect-forwarding reduction `output_p <- (output_p union suspects_q) - {q}` on p. 236, Lemmas 3.1–3.3 and Theorem 3.4 on p. 237, and Corollary 3.5 on p. 238), §4 and Figure 4 (pp. 238–239, Reliable Broadcast specification and diffusion protocol on p. 238), §5 (p. 239, Consensus specification: Termination, Uniform integrity, Agreement, Uniform validity), §§6.2–6.3 and Figure 6 (pp. 242–248, `f`-oblivious 4-phase rotating-coordinator `<>S` consensus algorithm waiting for `ceiling((n + 1)/2)` majorities for `f < ceiling(n/2)` in Figure 6 on p. 243 and remark on p. 244, Uniform Agreement Lemma 6.2.1 on pp. 244–245, Termination Lemma 6.2.2 on pp. 245–246, Theorem 6.2.3 on p. 246, Corollary 6.2.4 for `<>W` on pp. 246–247, and Theorem 6.3.1 on pp. 247–248 proving impossibility of Consensus using `<>P` when `f >= ceiling(n/2)`), §7 and §7.1 (pp. 248–252, Atomic Broadcast as Reliable Broadcast plus Total Order on p. 248, reduction of Consensus to Atomic Broadcast on p. 249, observation (1) on p. 249, Figure 7 on p. 249 transforming Reliable Broadcast and repeated Consensus instances `propose(k, -)` / `decide(k, -)` into Atomic Broadcast via deterministic batch ordering of `msgSet^k - A_delivered_p`, Lemmas 7.1.1–7.1.5 on pp. 250–252, and Theorem 7.1.6 and Corollary 7.1.7 on p. 252), and §8 (pp. 253–254, Theorem 8.1 and Figure 8).
[FailureDetectors/Hierarchy.lean](../CslibFrontier/Computability/Distributed/FailureDetectors/Hierarchy.lean) formalizes `FailurePattern`, `DetectorHistory`, the six completeness/accuracy properties (`eventualStrongAccuracy_iff_alive`, `eventualWeakAccuracy_iff_alive`), the eight classes, and the raw-history 3-cube lattice (`DetectorClass.forall_sat_imp_iff_le`, `weakCompleteness_iff_strongCompleteness_of_card_le_two`).
As steps toward [#7503](https://github.com/cslib-community/cslib-frontier/issues/7503), [FailureDetectors/Reduction.lean](../CslibFrontier/Computability/Distributed/FailureDetectors/Reduction.lean) formalizes Figure 3's suspect-forwarding transducer (`gossipHistory`, `AdmissibleGossipSchedule`, and zero-delay witness `syncGossipSchedule`, boosting `Q -> P`, `W -> S`, `<>Q -> <>P`, `<>W -> <>S`), and [FailureDetectors/Consensus.lean](../CslibFrontier/Computability/Distributed/FailureDetectors/Consensus.lean) formalizes an explicit asynchronous-round step model (`FDAsyncRoundProtocol`, `AdmissibleFDNetwork`) proving unconditional safety (without any `t` bound, via strict-majority quorums `Fintype.card P / 2 + 1`) and `<>S` / gossip-boosted `<>W` termination for `2 * t < Fintype.card P` of the `t`-oblivious 4-stage rotating-coordinator protocol `ctRoundProtocol` (adapting Figure 6 to `0`-indexed rounds `r = k / 4` storing updated timestamps `ts := r + 1` so `0` remains the initial timestamp, and lockstep global subrounds `k` with Subround-3 `.phase4 s.decided` broadcasts by all decided processes in place of skewed-round execution and Figure 4's diffusion `R-broadcast`), alongside the `2 <= Fintype.card P <= 2 * t` `<>P` impossibility step (`not_solvesFDAsyncRoundConsensus_eventuallyPerfect`) and sharp threshold characterizations; event-driven skewed-round executions remain open in [#7503](https://github.com/cslib-community/cslib-frontier/issues/7503).
One-shot initial-broadcast and abstract discrete-time (`t : ℕ`) slot-trace steps toward [#7297](https://github.com/cslib-community/cslib-frontier/issues/7297) are formalized in [CausalBroadcast/TotalOrder.lean](../CslibFrontier/Computability/Distributed/CausalBroadcast/TotalOrder.lean) (`consensusOfTotalOrderBroadcast`, `not_exists_oneShotTotalOrderBroadcast_ge_one`, `ConsensusSlotExec`, and `totalOrderBroadcast_of_consensusSlotExec`), where `TotalOrderBroadcastAlg` supplies one initial broadcast per process at `start` and `ConsensusSlotExec` axiomatizes subprotocol execution traces of the underlying Reliable Broadcast and per-slot Consensus instances.

<a id="chandylamport1985"></a>
## chandylamport1985

K. Mani Chandy and Leslie Lamport.
"Distributed Snapshots: Determining Global States of Distributed Systems."
*ACM Transactions on Computer Systems* 3(1), 63–75, 1985. https://doi.org/10.1145/214451.214456 . Checked on 2026-11-22 against the typeset journal PDF at https://lamport.azurewebsites.net/pubs/chandy.pdf (SHA-256 `285e71bf56470620ff6080be39a416ea5de0ec855750983f50471712226b1d6a`): Section 1 (pp. 63–65, defining a stable property `y` on p. 64 as closure under reachability, with termination, deadlock and token loss as examples on pp. 63–64), Section 2 (pp. 65–68, the asynchronous error-free FIFO channel model, 5-tuple events `⟨p, s, s', M, c⟩` on p. 66, and Examples 2.1–2.2 on pp. 66–68), Section 3.2 (p. 70, the Marker-Sending Rule and Marker-Receiving Rule), Section 3.3 (pp. 70–71, conditions `(L1)` and `(L2)` and the unnumbered strong-connectivity termination proof on p. 71), Section 4 (pp. 71–74, Figure 8 on p. 72 motivating non-physical snapshots and Theorem 1 on p. 72 with its causal-swap proof on pp. 72–73, the sole numbered theorem in the paper), and Section 5 (pp. 74–75, stability detection `(y(S_ι) → definite) ∧ (definite → y(S_φ))` for `definite := y(S*)` on p. 74, proved on p. 75).
In [ChandyLamport/Basic.lean](../CslibFrontier/Computability/Distributed/ChandyLamport/Basic.lean), `System P S M` over `Digraph P` models at most one channel per ordered pair `(src, dest)` (including self-loops, whereas §2, Figure 1 allows parallel labeled channels), generalizes `P S M : Type*` without finiteness assumptions (`[Finite P]` is assumed only for liveness), generalizes §2's single-channel events to transitions emitting a finite list `sent : List (P × M)` of outgoing messages atomically, and keeps `sys.lts` free of stuttering so `sys.lts.IsTerminal` expresses genuine global deadlock (`isStablePred_isTerminal`).
In [ChandyLamport/Snapshot.lean](../CslibFrontier/Computability/Distributed/ChandyLamport/Snapshot.lean), `SnapEvent.initiateSnapshot` and the first `SnapEvent.recvMarker` record the local state and append `.marker` to all outgoing edges atomically, while `extractSnapshot` assembles `S*` directly (matching §3.3, p. 71, which separates state recording from disseminating recorded states to a collector).
In [ChandyLamport/Correctness.lean](../CslibFrontier/Computability/Distributed/ChandyLamport/Correctness.lean), `chandyLamport_perm_mTr` and `chandyLamport_consistent_cut` formalize Theorem 1 (§4, pp. 72–73) on the `[ι, φ)` execution segment from any pre-snapshot state `S_init` (`sys.IsPreSnapshot S_init`) to any complete state `S_final` (`IsSnapshotComplete S_final`), permuting `eraseTrace xl` into `tracePreEvents S_init xl ++ tracePostEvents S_init xl` through `extractSnapshot S_final` (any prefix before `S_init` and suffix after `S_final` compose unchanged via `LTS.MTr.comp`); `stablePred_transfer` formalizes §5 (pp. 74–75, stating `y(S_ι) → y(S*)` in its contrapositive form `¬ Φ S* → ¬ Φ (project S_init)`); and `snapshot_liveness` formalizes §3.3 (p. 71) on finite strongly connected graphs under weak FIFO head-delivery fairness `FairChannels` (realizing `(L1)` while atomic marker handling discharges `(L2)`, with `SnapEvent.stutter` extending finite quiescent runs to `OmegaExecution`s and `System.InputEnabled.exists_fair_snapOmegaExecution` proving non-vacuity of `FairChannels`).

<a id="changkannan06"></a>
## changkannan06

Kevin L. Chang and Ravi Kannan.
"The Space Complexity of Pass-Efficient Algorithms for Clustering."
*Proceedings of the Seventeenth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2006)*, 1157–1166. https://doi.org/10.1145/1109557.1109685 . Checked against the SODA text on 2026-11-13: Section 5.1, the proof of Theorem 5.1 (stated on p. 1164), on p. 1165, which simulates an `ℓ`-pass algorithm with memory `M(A)` by "a total of 2ℓ − 1 messages of size at most M(A)", Alice and Bob alternately continuing each pass on their halves of the stream.
The journal version (SIAM J. Comput., 2009, retitled) was not inspected.

<a id="changroberts1979"></a>
## changroberts1979

Ernest Chang and Rosemary Roberts.
"An Improved Algorithm for Decentralized Extrema-Finding in Circular Configurations of Processes."
*Communications of the ACM* 22(5), 281–283, 1979. https://doi.org/10.1145/359104.359108 . The library's key is `ChangRoberts1979`.
Bibliographic metadata checked via DOI and search summaries on 2026-11-22 UTC; the article PDF was not directly inspected, so internal theorem and page locators are not claimed.
[RingElection/ChangRoberts.lean](../CslibFrontier/Computability/Distributed/RingElection/ChangRoberts.lean) formalizes simultaneous-all-initiator election-pass steps toward [#7200](https://github.com/cslib-community/cslib-frontier/issues/7200) (not the arbitrary-initiator or elected-announcement-pass endpoints) over an asynchronous FIFO unidirectional ring `Fin n` (`crAllInit`): unique-maximum termination (`crAllInit_terminates`), the `n * (n + 1) / 2` message bound (`crAllInit_messages_le`, `crAllInit_totalMsgs_rev_eq`), and the `n H_n` permutation-average formula (`crAllInit_avg_totalMsgs_eq`).

<a id="chanitakuramayu2026"></a>
## chanitakuramayu2026

Timothy M. Chan, Reina Itakura, Zhiyuan Ma and Yuancheng Yu.
"3SUM Made Simpler (Without Matrix Multiplication), `k`-SUM Hypothesis Refuted for Odd `k`, and Real 3SUM/APSP Derandomized."
STOC submission 1421, manuscript dated November 3, 2026, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1421.pdf . Checked against that manuscript (PDF SHA-256 `a21997be2b5840f7287e0995cef3c44b02ebdb3f81a5e53067c8b35b1a3d3996`): §2.1 Problem 2.1 and Theorem 2.2 on p. 5 (ranked supports of size `t`, query rank `2t`, deterministic `(n + binom(d, ≤s) + |C| · binom(2t, ≥s)) · d^{O(1)}` bound for `0 ≤ s ≤ 2t`), together with the preprocessing/query recurrences and word-RAM footnote 7 on pp. 5–6.
In [TrimmedYates.lean](../CslibFrontier/Algorithms/Lean/TrimmedYates.lean) and [WordRAM/TrimmedYates.lean](../CslibFrontier/Algorithms/WordRAM/TrimmedYates.lean), Lean generalizes the input ranks to `t₁, t₂` with query size `t₁ + t₂` (`s ≤ t₁ + t₂`) and formalizes the standard-basis Word-RAM program (`computesListInTime_program` for general `coveringProduct` with `highPeak` bound; `executesList_program` and `exec_solveFromTries_subsetConvolution` for ranked signed-integer `subsetConvolution` at explicit word width `w`); the §2.2 hashing reduction (Theorem 2.3) and Sections 3–5 remain open in [#4667](https://github.com/cslib-community/cslib-frontier/issues/4667).

<a id="charikar02"></a>
## charikar02

Moses S. Charikar.
“Similarity Estimation Techniques from Rounding Algorithms.”
*Proceedings of the 34th Annual ACM Symposium on Theory of Computing* (STOC 2002), 380–388. https://doi.org/10.1145/509907.509965 . DOI and metadata as reported by search indexes; the DOI was not resolved in this pass.
The locator Lemma 1 (for a similarity admitting a locality-sensitive hashing scheme, `1 − sim` satisfies the triangle inequality) was not checked against the full text in this pass.

<a id="charikar04"></a>
## charikar04

Moses Charikar, Kevin Chen, Martin Farach-Colton.
“Finding Frequent Items in Data Streams.”
*Theoretical Computer Science* 312(1), 3–15, 2004; preliminary version in ICALP 2002. https://doi.org/10.1016/S0304-3975(03)00400-6 . Bibliographic data from search summaries of the DOI record; the Count-Sketch statements formalized here follow the presentation of [chakrabarti25](#chakrabarti25), Section 5.3.
The journal text was not inspected in this pass.

<a id="charronbost1991"></a>
## charronbost1991

Bernadette Charron-Bost.
"Concerning the Size of Logical Clocks in Distributed Systems."
*Information Processing Letters* 39(1), 11–16, 1991. https://doi.org/10.1016/0020-0190(91)90055-M . Bibliographic metadata checked via secondary indexes on 2026-11-22 UTC; the full journal text was not inspected, so no numbered section or theorem locator is asserted.
[VectorClock/LowerBound.lean](../CslibFrontier/Computability/Distributed/VectorClock/LowerBound.lean) proves a self-contained crown-execution dimension lower-bound step over finite unicast `Execution P` traces (`crownFin`, `unicast_clock_dim_lower_bound`, `exists_unicast_orderEmbedding_clock_iff`) toward `#7203` after this work, without claiming its uninspected primary-source endpoint.

<a id="chashkin2006"></a>
## chashkin2006

A. V. Chashkin.
"On the Complexity of a Cyclic Shift of a Set of Real Numbers."
*Diskretnyi Analiz i Issledovanie Operatsii*, Ser. 1, 13(4), 89–92, 2006 (in Russian; English translation in *Journal of Applied and Industrial Mathematics* 1(2), 175–177, 2007; bibliography key `Chashkin2006`).
Bibliographic data taken from reference `[3]` of [Sergeev](#sergeev2020monotoneshift); the journal article was not inspected directly, so no direct theorem or page locator in `Chashkin2006` is claimed.
Cited through [Sergeev](#sergeev2020monotoneshift), pp. 1 and 4, for the real-valued 2-multiplexor shift lower-bound argument adapted to Boolean monotone circuits in [Shift.lean](../CslibFrontier/Computability/Circuit/Monotone/Shift.lean).

<a id="chattopadhyayliao20"></a>
## chattopadhyayliao20

Eshan Chattopadhyay and Jyun-Jie Liao.
*Optimal Error Pseudodistributions for Read-Once Branching Programs*. 35th Computational Complexity Conference (CCC 2020), LIPIcs 169, 25:1–25:27, 2020. https://doi.org/10.4230/LIPIcs.CCC.2020.25 ; cited from arXiv:2002.07208v4.
Appendix A.1 (Definition A.2, Lemmas A.3 and A.4) was checked against the arXiv v4 text on 2026-11-08.
Hoza (2021) cites the CCC version's Lemma 43 for the same material.

<a id="chawlahartlinemalecsivan10"></a>
## chawlahartlinemalecsivan10

Shuchi Chawla, Jason D. Hartline, David L. Malec and Balasubramanian Sivan.
"Multi-Parameter Mechanism Design and Sequential Posted Pricing."
*Proceedings of the 42nd ACM Symposium on Theory of Computing (STOC 2010)*, 311–320, 2010. https://doi.org/10.1145/1806689.1806733 ; cited from https://arxiv.org/pdf/0907.2435v2 (26 pp., SHA-256 `220807f3da1b4dc409fe627719ac167130108db0ae60d4bc495e3a76e9e0838b`), inspected on 2026-11-24 for §1–§2.2 (sequential and order-oblivious posted-price mechanisms and group strategy-proofness, pp. 1–4), §5.2 Theorem 10 (p. 9), and Appendix D.2 (Theorem 24, Proof of Theorem 10 for `k = 1` single-item non-i.i.d. regular revenue `2`-approximation via `(φᵢ)⁺`, and "An example with a gap of 2", pp. 18–19).

<a id="chendeng06"></a>
## chendeng06

Xi Chen and Xiaotie Deng.
"On the Complexity of 2D Discrete Fixed Point Problem."
*Automata, Languages and Programming (ICALP 2006)*, LNCS 4051, 489–500, Springer, 2006. https://doi.org/10.1007/11786986_43 ; journal version in *Theoretical Computer Science* 410(44), 4448–4456, 2009, https://doi.org/10.1016/j.tcs.2009.07.052 . Bibliographic metadata as recorded in `references.bib`; the paper's full text was not inspected directly, so no internal theorem number or page locator is cited.
The library cites it for the `PPAD`-completeness of two-dimensional discrete Sperner (`Sperner2D`) proved in [SpernerHardness.lean](../CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/SpernerHardness.lean) via an explicit polynomial-time circuit reduction from `EndOfLine` on a `2 ^ (n + 5) × 2 ^ (n + 5)` grid tiled by `16 × 16` crossing and turning cells.

<a id="chengfriedman05"></a>
## chengfriedman05

Alice Cheng and Eric Friedman.
"Sybilproof Reputation Mechanisms."
*Proceedings of the 2005 ACM SIGCOMM Workshop on Economics of Peer-to-Peer Systems (P2PECON '05)*, 128–132, ACM, 2005 (bibliography key `ChengFriedman2005`). https://doi.org/10.1145/1080192.1080202 . Checked against the 5-page ACM workshop PDF (printed pp. 128–132) on 2026-11-24: §3 Definitions 1–5 (pp. 129–130: reputation functions, contraction-based Sybil strategies, rank-sybilproofness, `K`-sybilproofness, and value-sybilproofness), §4.1 Definition 6 and Theorems 1–2 (p. 130: symmetric reputation functions and impossibility of nontrivial symmetric rank-sybilproof or `k`-sybilproof mechanisms), and §4.2 Theorems 4–5 (pp. 130–131: value-sybilproofness of capacity/flow-based propagation and rank-sybilproofness of single-path `max`-aggregation / Pathrank).
Note that Definition 4 of `ChengFriedman2005` indexes `k`-sybilproofness by total Sybil cluster size `|U'| ≤ k` (`k ≥ 2` in Theorem 2), whereas [friedmanresnicksami07](#friedmanresnicksami07) Definition 27.6 indexes `K`-rank-sybilproofness by additional fake identities `|U'| ≤ K + 1` (`K > 0` in Theorem 27.7); [Sybilproof.lean](../CslibFrontier/GameTheory/Reputation/Sybilproof.lean) follows the NRTV `|U'| ≤ K + 1` convention.

<a id="chenhiraharaoliveirapichrajgopalsanthanam2020"></a>
## chenhiraharaoliveirapichrajgopalsanthanam2020

Lijie Chen, Shuichi Hirahara, Igor C. Oliveira, Ján Pich, Ninad Rajgopal and Rahul Santhanam.
*Beyond Natural Proofs: Hardness Magnification and Locality*.
ITCS 2020, LIPIcs 151. https://doi.org/10.4230/LIPIcs.ITCS.2020.70 ; full version ECCC TR19-168.
Checked against the ECCC full version on 2026-11-11: Definition 3 (learning by circuits with non-adaptive membership queries, Section 2.2, p. 12), Lemma 34 (its use of a non-adaptive learner with the seed fixed by Adleman's trick, pp. 25–27), Definition 11 (local circuit classes `[q, ℓ, a]–C[s]`, Section 2.5, p. 13) and the MCSP `[OS18]` and `[MMW19]` bullets of Proposition 63 (Appendix A.2, p. 52).
Theorem numbers follow the ECCC numbering.

<a id="ching97"></a>
## ching97

Stephen Ching.
"Strategy-proofness and 'median voters'."
*International Journal of Game Theory* 26(4), 473–490, 1997 (bibliography key `Ching1997`). https://doi.org/10.1007/BF01813886 . Bibliographic metadata checked via DOI and secondary references on 2026-11-24; the published journal text is paywalled and was not directly inspected, so no internal theorem numbers are claimed.
Cited via [schummervohra07](#schummervohra07) (§10.6, p. 263) for showing that the peaks-only requirement in [moulin80](#moulin80) is redundant for strategy-proof onto rules on ordinal single-peaked preferences.

<a id="chistopolskayapodolskii2018"></a>
## chistopolskayapodolskii2018

Anastasiya Chistopolskaya and Vladimir V. Podolskii.
*Parity Decision Tree Complexity is Greater Than Granularity*.
ECCC TR18-174, revision 2, 26 October 2018; arXiv:1810.08668v2.
[Pinned report](https://eccc.weizmann.ac.il/report/2018/174/revision/2/download/).
Read on 2026-11-23: §2.3, Lemma 5, printed pp. 7–8 (parity decision-tree depth at most the AND count plus one); §3, Theorem 6, pp. 8–9 (depth at least granularity plus one for a nonconstant function); §4, Lemma 9, p. 11 (majority granularity `n − B(n)`) and Corollary 11, p. 12 (multiplicative complexity at least `n − B(n)`).
Here `B(n)` is the binary digit sum and majority returns true on a tie, matching the report's threshold `⌊(n + 1)/2⌋`.
The circuit formalization proves a direct joint-workspace denominator invariant, permitting arbitrary binary Boolean operations while charging exactly the nonaffine ones; the Zhegalkin specialization uses the existing `{XOR, AND, 1}` minimum-cost definition.
The source's decision-tree simulation and exact decision-tree complexity are not asserted by this circuit result.

<a id="christofides76"></a>
## christofides76

Nicos Christofides.
*Worst-Case Analysis of a New Heuristic for the Travelling Salesman Problem*.
Report 388, Graduate School of Industrial Administration, Carnegie-Mellon University, 1976; reprinted in *Operations Research Forum* 3, article 20, 2022, https://doi.org/10.1007/s43069-021-00101-z . The report details are those of reference [73] in [Williamson and Shmoys](#williamsonshmoys11), whose Chapter 2 Notes attribute the algorithm to Christofides; the reprint details come from search summaries.
Neither the report nor the reprint was checked; the formalization follows the proof of Theorem 2.13 of Williamson and Shmoys.

<a id="chrobakkarloffpaynevishwanathan91"></a>
## chrobakkarloffpaynevishwanathan91

Marek Chrobak, Howard J. Karloff, Thomas H. Payne, Sundar Vishwanathan.
"New Results on Server Problems."
*SIAM Journal on Discrete Mathematics* 4(2), 172–181, 1991. https://doi.org/10.1137/0404017 . Bibliographic metadata only; the full text was not inspected in this pass, so no theorem number is cited.
The manual credits this paper with the `k`-competitiveness of Double Coverage on the line, which secondary sources attribute to it; the local proof uses the standard potential `k·M_min + Σ_{i<j}|s_i - s_j|`.

<a id="chuliu65"></a>
## chuliu65

Yoeng-Jin Chu and Tseng-Hong Liu.
"On the Shortest Arborescence of a Directed Graph."
*Scientia Sinica* 14, 1396–1400, 1965.
The bibliographic details come from search summaries; the paper was not inspected, and no theorem locator is claimed.
The manual cites it as the earlier, independent source of the cycle-contraction algorithm for minimum-cost arborescences; the formalization follows [Edmonds 1967](#edmonds67b).

<a id="chung1997"></a>
## chung1997

Fan R. K. Chung.
*Spectral Graph Theory*.
CBMS Regional Conference Series in Mathematics 92, American Mathematical Society, 1997 (revised chapters hosted by the author at https://mathweb.ucsd.edu/~fan/research/revised.html ).
Checked firsthand on 2026-11-24 against the author-hosted revised Chapter 1 (`https://mathweb.ucsd.edu/~fan/research/cb/ch1.pdf`, SHA-256 `c37f9caff11d5ea03197ddfe6276e11f959d56bc2783eea5a241f648c85357f9`, printed pp. 1–21) and Chapter 2 (`https://mathweb.ucsd.edu/~fan/research/cb/ch2.pdf`, SHA-256 `dff6acad98635c9efcac9ea1a5338ab45a6fb9093ca50ab433df5a9552883a17`, printed pp. 23–40): §1.2 (pp. 2–6, combinatorial Laplacian `L`, normalized Laplacian $\mathcal{L} = T^{-1/2} L T^{-1/2}$ with convention `T^{-1}(v, v) = 0` at isolated vertices `d_v = 0`, Rayleigh quotient (1.1), spectral gap `λ_G = λ_1` in (1.2), volume `vol G = ∑_v d_v`, and Examples 1.1 and 1.5 for `K_n` and `C_n`), §1.3 (pp. 6–7, Lemma 1.7 basic bounds `λ_1 ≤ n / (n - 1)`, `λ_1 ≤ 1` for incomplete graphs, and `λ_i ≤ 2`), §2.2 (pp. 24–25, volume `vol S`, edge boundary $\partial S = E(S, \overline{S})$, set conductance `h_G(S)` in (2.1), and Cheeger constant `h_G` in (2.2)), §2.3 (pp. 25–28, Lemma 2.1 `2 h_G ≥ λ_1`, Theorem 2.2 `λ_1 > h_G² / 2` for connected graphs, Theorem 2.3 `λ_G ≥ 1 - √(1 - h_G²)`, and `h_G ≥ 2 / vol G` for connected graphs on p. 28), and §2.5 (pp. 34–35, modified Cheeger constant / isoperimetric number `h'_G`, combinatorial Laplacian algebraic connectivity `λ'_1`, `2 h'_G ≥ λ'_1`, and `λ'_1 ≥ (h'_G)² / (2 max_v d_v)`).
Formalized in [`SimpleGraph/Cheeger.lean`](../CslibFrontier/Foundations/Combinatorics/SimpleGraph/Cheeger.lean).
Pagination of the printed 1997 AMS monograph was not separately checked against the revised author chapters.

<a id="chvatal83"></a>
## chvatal83

Vašek Chvátal.
*Linear Programming*.
W. H. Freeman, New York, 1983.
Bibliographic data from library and search summaries; the book was not inspected in this pass.
The chapter locators used in the manual and docstrings (Chapter 2 for dictionaries, pivoting and the optimality test; Chapters 2–3 for the unboundedness test, which search summaries of the table of contents place in Chapter 3; Chapter 3 for cycling, the cycling example and the smallest-subscript rule; Chapter 4 for the Klee–Minty programs and the `2^n - 1` pivots of the largest-coefficient rule on them; Chapter 5 for duality and the dual solution read off the final dictionary) come from secondary summaries and memory of the book, not from a copy, and are unverified.
The coefficients of the cycling example in `CslibFrontierTests/Algorithms/Lean/Simplex.lean` were taken from those summaries and checked by running Dantzig's rule on them, which returns to the initial basis after six degenerate pivots.

<a id="ckkz12"></a>
## ckkz12

Seung Geol Choi, Jonathan Katz, Ranjit Kumaresan and Hong-Sheng Zhou.
"On the Security of the 'Free-XOR' Technique."
*Theory of Cryptography (TCC 2012)*, 39–53, 2012. https://doi.org/10.1007/978-3-642-28914-9_3 ; full version: Cryptology ePrint Archive, Report 2011/510, https://eprint.iacr.org/2011/510 . Checked on 2026-11-15 against the ePrint PDF of October 5, 2011 (14 pages, SHA-256 `3a8fe73ee05f8abb9d1079da877d1d6a0f42346d05f3a41e7ed630f616ab3897`); locators use its printed page numbers, which are also its PDF page numbers; this is the author's check, which no reviewer has yet repeated at the source, so the library cites these locators as not verified.
§4, p. 9: the oracle `Circ_R(w, w′, g, b₁, b₂, b₃) = H(w ⊕ b₁R ‖ w′ ⊕ b₂R ‖ g) ⊕ b₃R`, the random oracle `Rand` and the legal queries.
P. 10: Definition 4, circular 2-correlation robustness against non-uniform polynomial-time distinguishers, and Theorem 3, security of the free-XOR protocol against a semi-honest adversary in the OT-hybrid model.
Cited for the origin of circular correlation robustness; the library formalizes no dual-key notion.

<a id="ckmpsw19"></a>
## ckmpsw19

Ioannis Caragiannis, David Kurokawa, Hervé Moulin, Ariel D. Procaccia, Nisarg Shah and Junxing Wang.
"The Unreasonable Fairness of Maximum Nash Welfare."
*ACM Transactions on Economics and Computation* 7(3), Article 12, 12:1–12:32, 2019. https://doi.org/10.1145/3355902 . Bibliographic metadata checked via DOI/search records on 2026-11-24 UTC; the journal PDF was not inspected on disk, so no internal theorem or page locator is claimed.
Cited (`CaragiannisKurokawaMoulinProcacciaShahWang2019`) for Round-Robin `EF1` (`AdditiveValuation.isEF1_roundRobin`) and the simultaneous `EF1` and Pareto optimality of two-stage Maximum Nash Welfare allocations (`AdditiveValuation.IsMaxNashWelfare`, `AdditiveValuation.IsMaxNashWelfare.isEF1`, `AdditiveValuation.IsMaxNashWelfare.isParetoOptimal`).

<a id="cks20"></a>
## cks20

Clément L. Canonne, Gautam Kamath and Thomas Steinke.
*The Discrete Gaussian for Differential Privacy*.
NeurIPS 2020; cited from arXiv:2004.00010v5, 2021. https://arxiv.org/abs/2004.00010 . Definition 28 and Lemmas 29–30 were checked against the arXiv v5 PDF on 2026-11-07.

<a id="clrs09"></a>
## clrs09

Thomas H. Cormen, Charles E. Leiserson, Ronald L. Rivest and Clifford Stein.
*Introduction to Algorithms*, third edition.
MIT Press, 2009.
ISBN 978-0-262-03384-8.
Section 35.1, procedure `APPROX-VERTEX-COVER` and Theorem 35.1 (it is a polynomial-time 2-approximation algorithm).
The locator 35.1 was checked against secondary course material, not the printed book.
Sections 22.3–22.4 (depth-first search; Lemma 22.11, acyclic if and only if no back edges; Theorem 22.12, correctness of `TOPOLOGICAL-SORT`) and Section 24.1 (Bellman–Ford; Lemma 24.2, estimates equal shortest-path weights after `|V| - 1` passes when no negative cycle is reachable; Theorem 24.4, correctness of `BELLMAN-FORD`) were likewise checked against secondary course material.
Sections 25.1 ("Shortest paths and matrix multiplication": repeated (min,+) squaring) and 25.2 ("The Floyd–Warshall algorithm") are the all-pairs shortest-path locators.
They were checked against the edition's published table of contents only.
Section 26.4 ("Push-relabel algorithms") is the push–relabel locator.
Its statement numbers were checked against secondary course material, not the printed book: Lemma 26.14 (an overflowing vertex admits a push or a relabel), Lemma 26.15 (heights never decrease, and a relabel raises them), Lemma 26.16 (push and relabel keep a height function), Lemma 26.17 (no residual `s`–`t` path), Theorem 26.18 (correctness at termination), Lemma 26.19 (an overflowing vertex reaches `s` in the residual network), Lemma 26.20 (heights stay below `2|V|`), Corollary 26.21 (fewer than `2|V|²` relabels), Lemmas 26.22 and 26.23 (fewer than `2|V||E|` saturating and fewer than `4|V|²(|V| + |E|)` nonsaturating pushes) and Theorem 26.24 (`O(|V|² |E|)` basic operations).
Section 9.3 ("Selection in worst-case linear time") is the locator for the groups-of-five median-of-medians algorithm and its counting step; it was not checked against the printed book.
Section 9.1 ("Minimum and maximum") is the locator for the linear scan for the minimum and for finding the minimum and maximum together with `3⌊n/2⌋` comparisons by comparing pairs; secondary course material places the lower bound `⌈3n/2⌉ - 2` for the minimum and maximum in Exercise 9.1-2.
Neither locator was checked against the printed book.
Section 15.4 ("Longest common subsequence": Theorem 15.1, optimal substructure of an LCS, and the running example `ABCBDAB`, `BDCABA` with an LCS of length `4`) and Problem 15-5 ("Edit distance") are the edit-distance and LCS locators.
They were checked against secondary course material, not the printed book.
Section 15.5 ("Optimal binary search trees": the recurrence for `e[i, j]` and the five-key example with expected cost 2.75) was checked against secondary course material, not the printed book.
Kosaraju's two-pass strongly connected components algorithm in [DFS/SCC.lean](../CslibFrontier/Algorithms/Lean/DFS/SCC.lean) cites the book without attributing a section or theorem number, as the corresponding section has not been checked against the printed book.

<a id="codenottivaradarajan2007"></a>
## codenottivaradarajan2007

Bruno Codenotti and Kasturi Varadarajan.
"Computation of Market Equilibria by Convex Programming."
Chapter 6 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, pp. 135–158. https://doi.org/10.1017/CBO9780511800481.008 . Key `CodenottiVaradarajan2007`.
Checked in same-fleet review on 2026-11-24 against the 2007 CUP book text (`ch06.txt`): Section 6.1.1 (pp. 136–137; `demandSet_smul`, excess demand, and Walras's law on p. 137; note §6.1.1 p. 136 assumes concavity, global nonsatiation, and monotonicity, whereas [Basic.lean](../CslibFrontier/GameTheory/Market/Basic.lean) assumes local nonsatiation directly), Section 6.1.5 (p. 139, linear utility), Section 6.1.7 (p. 140, proportional-endowment Fisher-to-exchange embedding `w_i = δ_i w`), Section 6.2 (p. 141, Fisher market), and Section 6.4.1 (p. 147).
Note Chapter 6 does not define Pareto optimality or prove the First Welfare Theorem.
Held for outside-authoring-fleet primary-source review.

<a id="colevishkin1986"></a>
## colevishkin1986

Richard Cole and Uzi Vishkin.
"Deterministic Coin Tossing with Applications to Optimal Parallel List Ranking."
*Information and Control* 70(1), 32–53, 1986. https://doi.org/10.1016/S0019-9958(86)80023-7 . Bibliographic metadata checked via DOI record on 2026-11-22 UTC; the journal PDF was not directly inspected, so internal section and theorem numbers are not claimed.
Credited for the `(pos, bit)` lowest-differing-bit color-reduction step (`cvColor`, `cvBound`) formalized on oriented cycles in [OrientedCycle/ColeVishkin.lean](../CslibFrontier/Computability/Distributed/OrientedCycle/ColeVishkin.lean) and lifted across `Δ` functional out-edge orientations on general bounded-degree graphs in [LocalGraph/Coloring.lean](../CslibFrontier/Computability/Distributed/LocalGraph/Coloring.lean) (`deltaPlusOneColoring`, step toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505)).

<a id="complexitylib"></a>
## complexitylib

cslib-frontier contributors.
*cslib-frontier* (named Complexitylib at this snapshot), source snapshot `13e6a31951bf1c89a1a6258c44f9444aecbbefd8`.
[Pinned repository](https://github.com/cslib-community/cslib-frontier/blob/13e6a31951bf1c89a1a6258c44f9444aecbbefd8).
Individual declarations are linked in the text.
The repository bibliography records mathematical sources; attribution here reports those source annotations unless independent verification is explicitly stated.

<a id="cook74"></a>
## cook74

Stephen A. Cook.
*An Observation on Time-Storage Trade Off*.
Journal of Computer and System Sciences 9(3):308-316, 1974.
The pyramid lower bound was checked through its statement as Theorem 4.8 of [nordstrom15](#nordstrom15).

<a id="cookmertz24"></a>
## cookmertz24

James Cook and Ian Mertz.
*Tree Evaluation is in Space O(log n · log log n)*.
STOC 2024; full report ECCC TR23-174 (15 November 2023). https://eccc.weizmann.ac.il/report/2023/174/ .

<a id="cookreckhow73"></a>
## cookreckhow73

Stephen A. Cook, Robert A. Reckhow.
“Time Bounded Random Access Machines.”
*Journal of Computer and System Sciences* 7(4), 354–375, 1973. https://doi.org/10.1016/S0022-0000(73)80029-7 . Local source explicitly labels its adaptation; publisher fetch unavailable in this pass.

<a id="cookreckhow79"></a>
## cookreckhow79

Stephen A. Cook, Robert A. Reckhow.
“The Relative Efficiency of Propositional Proof Systems.”
*The Journal of Symbolic Logic* 44(1), 36–50, 1979. https://doi.org/10.2307/2273702 . The manual cites this paper for the notion of a Frege system.
The simulation of resolution by the Frege system in the [proof-systems chapter](circuits-logic-and-other-models/proof-systems.md) is presented as a standard fact in this framework, with no theorem locator; the paper itself was not re-inspected in this pass.

<a id="cormode05"></a>
## cormode05

Graham Cormode, S. Muthukrishnan.
“An Improved Data Stream Summary: The Count-Min Sketch and its Applications.”
*Journal of Algorithms* 55(1), 58–75, 2005. https://doi.org/10.1016/j.jalgor.2003.12.001 ; author PDF https://www.cs.ox.ac.uk/people/graham.cormode/pubs/papers/cm-full.pdf . Sections 3–4.1 and fixed point-query guarantee consulted.

<a id="correaschulzstiermoses04"></a>
## correaschulzstiermoses04

José R. Correa, Andreas S. Schulz and Nicolás E. Stier-Moses.
*Selfish Routing in Capacitated Networks*.
Mathematics of Operations Research 29(4), 961–976, 2004. https://doi.org/10.1287/moor.1040.0098 . Bibliographic metadata only; the publisher's text is paywalled and no open author's version was found, so it was not inspected and no locator in it is cited.
Following [roughgarden13cs364a](#roughgarden13cs364a), Lecture #11, Theorem 3.3, which credits it, `CslibFrontier/GameTheory/Congestion/PigouBound.lean` cites it for the Pigou-bound theorem in the generality formalized there.

<a id="coverthomas06"></a>
## coverthomas06

Thomas M. Cover and Joy A. Thomas.
*Elements of Information Theory*, second edition.
Wiley-Interscience, 2006. https://doi.org/10.1002/047174882X . Section 5.11, "Generation of discrete distributions from fair coins": Theorem 5.11.1 (`H(X) ≤ E[T]` for every generating tree), Theorem 5.11.2 (equality for dyadic distributions) and Theorem 5.11.3 (`H(X) ≤ E[T] < H(X) + 2` for the optimal tree).
The theorem numbers and statements were taken from secondary summaries and course notes on 2026-11-08; the printed book was not inspected.
Also cited for Section 2.10 (Fano's inequality: Theorem 2.10.1, the corollary after it with the sharper `log(|𝒳| − 1)` form for estimators valued in `𝒳`, and the remark on guessing without side information), Section 7.1 (capacity of the binary symmetric channel), Lemma 7.9.2 and Theorem 7.9.1 (the converse to the channel coding theorem); these locators were likewise checked against secondary course material, not the printed book.

Chapter 13 (universal source coding): the Lempel–Ziv tree-structured (incremental) parsing, its example `ABBABBABBBAABABAA`, and the distinct-parsing lemma `c(n) ≤ n / ((1 - ε_n) log n)` with `ε_n = min(1, (log log n + 4) / log n)` in §13.5.
The library cites only the section; secondary sources disagree on the lemma's number.
The section, the lemma's statement and the example were taken from secondary course material and search summaries and were not checked against the printed book.

<a id="cremermclean88"></a>
## cremermclean88

Jacques Crémer and Richard P. McLean.
"Full Extraction of the Surplus in Bayesian and Dominant Strategy Auctions."
*Econometrica* 56(6), 1247–1257, 1988. https://doi.org/10.2307/1913096 . Bibliographic metadata and DOI only; the paywalled 1988 *Econometrica* PDF was not directly inspected firsthand, so internal page, equation, and numbered theorem locators are not claimed, and no `CslibFrontierResults/` entries are registered.
Cited in [CremerMcLean.lean](../CslibFrontier/GameTheory/Mechanism/CremerMcLean.lean) for full surplus extraction in correlated finite-type quasilinear environments under row linear independence (`IsExPostDSIC`) and convex independence (`IsBIC`) of conditional belief matrices.

<a id="cs03"></a>
## cs03

Ronald Cramer and Victor Shoup.
“Design and Analysis of Practical Public-Key Encryption Schemes Secure against Adaptive Chosen Ciphertext Attack.”
*SIAM Journal on Computing* 33(1), 167–226, 2003. https://doi.org/10.1137/S0097539702403773 . Authors' revised manuscript (August 14, 2003): https://www.shoup.net/papers/cca2.pdf (Section 5.1, target collision resistance; Section 6.1, Figure 1, the hash key `hk` drawn at key generation and published in the public key; Section 6.2, Theorem 1).
Checked against that manuscript on 2026-11-14.
A copy of the same manuscript (69 pages, dated August 14, 2003; SHA-256 `ac2250e7e5d5c156979de1629edbdb0c8248ef25455f66b55640c98a1bad1191`) was fetched from that URL on 2026-11-18 UTC, because the IACR ePrint refused automated download.
Its printed page is the PDF page minus 3.
Read there on 2026-11-18: Section 7.1 (key encapsulation mechanisms, with keys of `KEM.KeyLen(λ)` bits), Section 7.1.1 (soundness) and Section 7.1.2, printed pp. 38–39 (the adaptive chosen-ciphertext attack game for a KEM: Stage 1 gives the adversary the public key, Stages 2 and 4 are decryption queries, Stage 3 returns `(K†, ψ*)` with `K⁺` uniform on `ℓ`-bit strings, and `AdvCCA'` = 2 · `AdvCCA`).

<a id="cslib"></a>
## cslib

CSLib contributors.
*CSLib*, pinned dependency snapshot `254e30e6d4299c51323aaeaf5f51a4763b375d4a`.
[Pinned repository](https://github.com/leanprover/cslib/blob/254e30e6d4299c51323aaeaf5f51a4763b375d4a).

<a id="cygan2015"></a>
## cygan2015

Marek Cygan, Fedor V. Fomin, Łukasz Kowalik, Daniel Lokshtanov, Dániel Marx, Marcin Pilipczuk, Michał Pilipczuk, and Saket Saurabh.
*Parameterized Algorithms*.
Springer, 2015.
[DOI](https://doi.org/10.1007/978-3-319-21275-3).
Inspected the authors' companion PDF dated 2016-05-30: Definitions 1.2–1.3 (p. 13), Definition 2.1 (pp. 18–19), Lemma 2.2 (p. 20), and Section 2.2.1 (pp. 21–22); accessed 2026-11-02.
On 2026-11-08 the same PDF returned HTTP 403, so the crown material of Section 2.3 cited by [Crown](../CslibFrontier/Foundations/Combinatorics/SimpleGraph/Crown.lean) was not inspected.
Secondary sources number the crown lemma Lemma 2.14 and the `3k` kernel Theorem 2.16; these numbers are unverified and are not used in the Lean docstrings.
The color-coding locators Section 5.2 and Lemma 5.5, the fpt-reduction locator Section 13.1, and the tree-decomposition locator Section 7.3.1 (weighted independent set, stated for `n`-vertex graphs), used in [parameterized complexity](machines-and-classes/parameterized-complexity.md), were not re-inspected.
Section 4.4 (iterative compression for odd cycle transversal), cited by [OddCycleTransversal](../CslibFrontier/Foundations/Combinatorics/SimpleGraph/OddCycleTransversal.lean) and its algorithm, was not inspected either; its locator comes from secondary sources.
Likewise, nice tree-decomposition normalization (Lemma 7.4, p. 161), bounded-treewidth CSP dynamic programming, and the clause-grouping `3-SAT`-to-`Clique` ETH lower bound (Theorem 14.21, p. 485) were inspected in the companion PDF and verified, matching the locators in the [results registry](../CslibFrontierResults/Entries.lean).

The same author PDF supports the weighted-circuit enumeration in Section 13.3, p. 436, and the definition of `W[t]` in Definition 13.16, p. 437, used in [parameterized complexity](machines-and-classes/parameterized-complexity.md).
This section does not define `W[P]`; the library's `WP` reduction closure is documented separately and its equivalence with an effective literature class is not claimed.

<a id="dasfraigniaudpazrosen25"></a>
## dasfraigniaudpazrosen25

Avinandan Das, Pierre Fraigniaud, Ami Paz and Adi Rosén.
"Semi-Streaming Algorithms for Graph Property Certification." arXiv:2503.12996v1, 2025. https://arxiv.org/abs/2503.12996 . Checked against arXiv:2503.12996v1 on 2026-11-16: Section 1 (a certification scheme's verifier receives a certificate from the prover before the stream starts; its cost is the certificate size plus the memory) and Lemma 7 (a family of streaming lower bound graphs gives `c + m = Ω(CC^N(f))` for one-pass certification schemes with `c`-bit certificates and `m` bits of memory; the proof simulates one pass, with one message from Alice to Bob).

<a id="dasguptagupta03"></a>
## dasguptagupta03

Sanjoy Dasgupta, Anupam Gupta.
“An Elementary Proof of a Theorem of Johnson and Lindenstrauss.”
*Random Structures & Algorithms* 22(1), 60–65, 2003. https://doi.org/10.1002/rsa.10073 . Author-hosted copy: https://cseweb.ucsd.edu/~dasgupta/papers/jl.pdf . Checked against that copy on 2026-11-07 UTC: Theorem 2.1 on p. 61 (`0 < ε < 1` and `k ≥ 4 (ε²/2 - ε³/3)⁻¹ ln n`), and Lemma 2.2 on p. 62 (tails for the projection of a random unit vector onto `k` coordinates, proved with `𝔼 exp (sX²) = (1 - 2s)^(-1/2)` for a standard Gaussian `X`).

<a id="demainehearn2008"></a>
## demainehearn2008

Erik D. Demaine and Robert A. Hearn.
*Constraint Logic: A Uniform Framework for Modeling Computation as Games*.
Proceedings of the 23rd IEEE Conference on Computational Complexity, 149–162, 2008.
Section 3.1 introduces the red–blue connector with minimum inflow one.
[Authors’ version](https://erikdemaine.org/papers/CL_Complexity2008/paper.pdf)

<a id="desimone90"></a>
## desimone90

Caterina De Simone.
"The cut polytope and the boolean quadric polytope."
*Discrete Mathematics* 79(1), 71–75, 1990. https://doi.org/10.1016/0012-365X(90)90056-N . Bibliographic metadata checked via search summaries on 2026-11-11 UTC; the primary paper was not inspected and no locator in it is cited.
Cited alongside [fmptw15](#fmptw15), Theorem 5, for the linear isomorphism between `CUT(n + 1)` and `CORR(n)`.

<a id="datar04"></a>
## datar04

Mayur Datar, Nicole Immorlica, Piotr Indyk and Vahab S. Mirrokni.
“Locality-sensitive hashing scheme based on p-stable distributions.”
*Proceedings of the Twentieth Annual Symposium on Computational Geometry (SoCG 2004)*, ACM, 253–262, 2004. https://doi.org/10.1145/997817.997857 . Bibliographic metadata checked against DBLP search results; the full text was not inspected (attempted archive links returned HTTP 404), so section and theorem locators remain unverified.

<a id="debreuscarf1963"></a>
## debreuscarf1963

Gerard Debreu and Herbert Scarf.
"A Limit Theorem on the Core of an Economy."
*International Economic Review* 4(3), 235–246, 1963 (library key `DebreuScarf1963`). https://doi.org/10.2307/2525306 . Bibliographic metadata only; the journal PDF was not directly inspected, so no internal theorem, lemma or page locators are claimed.
Cited in [Core.lean](../CslibFrontier/GameTheory/Market/Core.lean) for coalition blocking (`ExchangeMarket.IsBlockedBy`), the exchange-economy core (`ExchangeMarket.IsInCore`), core inclusion of competitive equilibria (`ExchangeMarket.IsCompetitiveEquilibrium.isInCore`), `r`-fold replica economies (`ExchangeMarket.replica`), the equal-treatment theorem under strictly concave utilities (`ExchangeMarket.eq_of_isInCore_replica`), and the Debreu–Scarf core shrinking and core equivalence theorems (`ExchangeMarket.exists_priceQuasiEquilibrium_of_forall_replica_isInCore`, `ExchangeMarket.exists_isCompetitiveEquilibrium_of_forall_replica_isInCore`, `ExchangeMarket.exists_isCompetitiveEquilibrium_iff_forall_replica_isInCore`), steps toward [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).

<a id="devroyelugosi01"></a>
## devroyelugosi01

Luc Devroye and Gábor Lugosi.
*Combinatorial Methods in Density Estimation*.
Springer Series in Statistics, Springer, New York, 2001.
ISBN 978-0-387-95117-1. https://doi.org/10.1007/978-1-4613-0125-7 . Bibliographic metadata checked via search summaries on 2026-11-11; the book text was not inspected, so Chapter 6 attribution is unverified against the printed book.
Cited as background for Scheffé sets (`scheffeSet`), pairwise Scheffé tests (`scheffeTest`), and `3 * OPT + 2 * γ` minimum-distance TV selection (`scheffeSelect`); the one-sided `scheffeScore` formulation and Hoeffding union-bound proofs in `CslibFrontier/Probability/HypothesisSelection/{LeCamBirge,Tournament}.lean` are this library's formulation.

<a id="dewolf06"></a>
## dewolf06

Ronald de Wolf.
"Lower Bounds on Matrix Rigidity via a Quantum Argument."
*Automata, Languages and Programming (ICALP 2006), Part I*, LNCS 4051, 62–71, Springer, 2006 (bibliography key `deWolf2006`). https://doi.org/10.1007/11786986_7 ; preprint arXiv:quant-ph/0505188v2 (25 April 2006), https://arxiv.org/abs/quant-ph/0505188 . Checked against the arXiv:quant-ph/0505188v2 LaTeX source (`qr-icalp06.tex`, SHA-256 `2e1653ce6ad5963a32539e831d1c12dac3c402f7ee6e450ff6da0698eb9c38d7`) and S. V. Lokam's *Complexity Lower Bounds using Linear Algebra* (`Lokam2009`, https://www.cs.toronto.edu/~toni/Courses/CommComplexity/Papers/lokam-book.pdf , SHA-256 `8d414a15f21b2e58b6a62f8bbda7abe3e1afca5da3cdca831c1711231618edf2`) on 2026-11-22: §1.2 (`qr-icalp06.tex`, lines 133 and 148–151, noting `R_H(r) ≥ n² / (4r)` for `r ≤ n / 2` and extending to generalized Hadamard matrices) and §3, Theorem 1 (`rank A ≥ ab / n` for every `a × b` submatrix `A` of `H`, attributing Lokam 2001 Corollary 2.7; corresponding to `Lokam2009`, §3.2, Lemma 3.6 on printed p. 44 / PDF p. 47) and Theorem 2 (`if r ≤ n / 2, then R_H(r) ≥ n² / (4r)`, lines 314–335, corresponding to `Lokam2009`, §3.2.1, Definition 3.3 and Theorem 3.8 on printed pp. 45–46 / PDF pp. 48–49, where Lokam's printed statement omits `r ≤ n / 2` while selecting `2r` rows in the first sentence of its proof).
Formalized in [`Rigidity/Hadamard.lean`](../CslibFrontier/Foundations/LinearAlgebra/Matrix/Rigidity/Hadamard.lean) for Mathlib's `Matrix.IsHadamard` over `ℝ` and `ℂ` (`[RCLike K]`) and over arbitrary characteristic-zero fields with trivial `star` (`Matrix.IsHadamard.card_mul_le_rank_submatrix`, `Matrix.IsHadamard.card_mul_le_rank_submatrix_of_trivialStar`, `Matrix.IsHadamard.card_sq_le_four_mul_rigidity`, `Matrix.IsHadamard.card_sq_le_four_mul_rigidity_of_trivialStar`).

<a id="dewolf19"></a>
## dewolf19

Ronald de Wolf.
*Quantum Computing: Lecture Notes*. arXiv:1907.09415, read in v6 (SHA-256 `b797f4165555d28180438586412e7629fecadb94a7ea81c761de8bdfd37a1fc1`). https://arxiv.org/abs/1907.09415 . For the density-matrix modules the following were checked on 2026-11-08: §15.1 (density matrices are the positive semidefinite matrices of trace one; a pure state is `|φ⟩⟨φ|`; unitaries act by `ρ ↦ UρU*`), §18.3 (the partial trace, defined by `Tr_B (C ⊗ D) = C · Tr D` and extended linearly; the reduced state of an EPR pair is `I / 2`), and Chapter 18, Exercises 5 (the random Pauli on one qubit, "a quantum one-time pad") and 7 (Alice cannot signal to Bob by a unitary on her half of an entangled pure state).
The Kraus-family form of no-signalling in the library is a standard generalization of Exercise 7, not a statement from the notes.
Checked again on 2026-11-24 for Chapter 15, §15.2–§15.3 (printed pp. 129–132): von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` in base `2` and Theorem 3 on printed p. 131 (part 1: `I(X : Y) ≤ n` without prior entanglement; part 2: `I(X : Y) ≤ 2n` with arbitrary prior entanglement, establishing optimality of superdense coding, formalized in [Holevo.lean](../CslibFrontier/Foundations/Quantum/DensityMatrix/Holevo.lean)).

<a id="diestel25"></a>
## diestel25

Reinhard Diestel.
*Graph Theory*, sixth edition.
Graduate Texts in Mathematics 173, Springer, 2025.
The author's free preview chapters (https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch3.pdf and Ch1.pdf) were consulted on 2026-11-08 and 2026-11-11 UTC for Section 1.4 (`k`-connectedness `|G| > k`, separating sets, Proposition 1.4.2 `κ(G) ≤ λ(G)`), Section 3.3, Theorem 3.3.1 (`A`–`B` Menger), Corollary 3.3.5 (i) (vertex form, `ab ∉ E`) and (ii) (edge form), and Theorem 3.3.6 (i)–(ii) (global `k`-connectivity Menger).

<a id="dijkstra1973"></a>
## dijkstra1973

Edsger W. Dijkstra.
*Self-stabilization in Spite of Distributed Control*.
Burroughs Corporation technical manuscript EWD391, 1 October 1973.
Transcription in the E. W. Dijkstra Archive at the University of Texas at Austin, https://www.cs.utexas.edu/users/EWD/transcriptions/EWD03xx/EWD391.html , inspected on 2026-11-22 (SHA-256 `5de1ab12c133be80d9865eff729cd10e7d6095f96e420063f9b690fd6c3543ce`).
Checked: the ring of `N + 1` finite-state machines `0 .. N` under a daemon issuing adjustment commands infinitely often to every machine (permitting no-effect commands on unprivileged machines) and legitimate states with a single rotating privilege (opening section before the first `* * *` break); the composite-ring symmetry impossibility argument in the first paragraph after the first `* * *` break (in [DijkstraRing.lean](../CslibFrontier/Computability/Distributed/SelfStabilization/DijkstraRing.lean), `UniformRingProtocol`, `UniformRingProtocol.card_privilegedSet_dvd_of_isRingPeriodic`, `not_uniform_enabledMove_selfStabilizing_composite_ring`, and `not_uniform_distEnabledMove_selfStabilizing_composite_ring` formalize scheduler-scoped enabled-move steps where `centralLTS` / `distLTS` permit only privileged moves without fairness across residue classes, leaving EWD391's fair-command composite-ring endpoint open in #7291); the `K`-state ring rules (`x[i] ≠ x[i - 1] → x[i] := x[i - 1]` for `1 ≤ i ≤ N` and `x[0] = x[N] → x[0] := (x[0] + 1) mod K`), deadlock-freedom by transitivity of equality, legitimate-state rotation, and central-daemon convergence for `K ≥ N` (before the second `* * *` break); and the distributed-daemon discussion after the second `* * *` break (which considers separate local reads and adjustments rather than `dijkstraDistRing`'s original simultaneous atomic-subset updates from a single pre-step state).

<a id="dijkstra1974"></a>
## dijkstra1974

Edsger W. Dijkstra.
"Self-stabilizing Systems in Spite of Distributed Control."
*Communications of the ACM* 17(11), 643–644, November 1974. https://doi.org/10.1145/361179.361202 (open copy https://raw.githubusercontent.com/papers-we-love/papers-we-love/main/distributed_systems/self-stabilizing-systems-in-spite-of-distributed-control.pdf , SHA-256 `283a8360655dcafc10cbef8e58fc60f6332e8a660516635b9db37ac00e38cbac`; manuscript version EWD426, https://www.cs.utexas.edu/users/EWD/ewd04xx/EWD426.PDF , SHA-256 `bac4d6c8f79db228d139d23197e945fa1816989a111e25e6893ad66b9c59eb52`).
Checked against the typeset CACM 2-page PDF on 2026-11-22:

- Page 643, right column: connected network of finite-state machines with Boolean privilege functions of a machine's own state and its neighbours' states, central daemon selecting one present privilege per move (explicitly excluding a distributed daemon on p. 643), legitimate-state requirements (1)–(4), and the definition of *self-stabilizing* ("regardless of the initial state and regardless of the privilege selected each time for the next move, at least one privilege will always be present and the system is guaranteed to find itself in a legitimate state after a finite number of moves") ↔ `CorruptedStep`, `SelfStabilizing` in [Basic.lean](../CslibFrontier/Computability/Distributed/SelfStabilization/Basic.lean).
  Generic `SelfStabilizing` captures closure (requirement (2)), deadlock-freedom (at least one privilege present in every state, implying requirement (1)), and well-founded finite convergence without fairness assumptions; source requirements (3) (each privilege occurs in some legitimate state) and (4) (mutual reachability of all legitimate states) of Dijkstra's legitimate-state specification lie outside the generic `SelfStabilizing` predicate's scope.
- Page 643 bottom to page 644 top: remark that for the cyclic arrangement "the discovery that not all machines could be identical was the crucial one" (discussed in [dijkstra1973](#dijkstra1973), with scheduler-scoped enabled-move steps in [DijkstraRing.lean](../CslibFrontier/Computability/Distributed/SelfStabilization/DijkstraRing.lean)).
- Page 644, left column ("Solution with K-state Machines (`K > N`)") and right column (Note 1): ring of `N + 1` machines numbered `0` through `N` (formalized over `Fin n` with total ring size `n = N + 1`, so `K > N` corresponds to `n ≤ K` and `K ≥ N` corresponds to `n - 1 ≤ K`), legitimate states defined as those in which *exactly one* privilege is present (`DijkstraLegitimate n K`), bottom rule `if L = S then S := (S + 1) mod K fi` and normal rule `if L ≠ S then S := L fi` (`dijkstraPrivileged`, `dijkstraNextVal`, `dijkstraRing`), and Note 1 ("With a central daemon the relation `K ≥ N` is sufficient") ↔ `dijkstraRing_selfStabilizing_of_pred_le` in [DijkstraRing.lean](../CslibFrontier/Computability/Distributed/SelfStabilization/DijkstraRing.lean).
  The simultaneous atomic-subset transition model `dijkstraDistRing` and its closure/convergence/iff theorems (`dijkstraDistRing_legitimate_closed`, `dijkstraDistRing_mTr_legitimate_of_le`, `dijkstraDistRing_selfStabilizing_of_le`, `dijkstraDistRing_not_selfStabilizing_of_lt`, `dijkstraDistRing_selfStabilizing_iff`), together with the explicit `K * (n * (n - 1) / 2) + K` bound `dijkstraRing_mTr_legitimate_of_le` and periodic converse `dijkstraRing_not_selfStabilizing_of_lt_pred` (`dijkstraRing_selfStabilizing_iff`), are original to this formalization.
  The four-state and three-state bidirectional ring solutions on p. 644 remain open under #7291.

<a id="dijkstrascholten1980"></a>
## dijkstrascholten1980

Edsger W. Dijkstra and Carel S. Scholten.
"Termination Detection for Diffusing Computations."
*Information Processing Letters* 11(1), 1–4, August 1980. https://doi.org/10.1016/0020-0190(80)90021-6 . Author manuscript EWD687a (26 January 1979), E. W. Dijkstra Archive, University of Texas at Austin: typescript PDF https://www.cs.utexas.edu/~EWD/ewd06xx/EWD687a.PDF (SHA-256 `f4930afa16451a4e692e1e37b1dca50235450f9c5da72eb15ee888314f9b0bb9`, 9 PDF pages; cover notice on PDF p. 1 records publication as *Information Processing Letters* 11, 1: 1–4, 1980) and HTML transcription https://www.cs.utexas.edu/~EWD/transcriptions/EWD06xx/EWD687a.html (SHA-256 `af6e11072721321943ed132b74374da40477bf95db8102c55bef29c83da93e10`), both inspected in full on 2026-11-22 UTC.
Journal metadata was verified against the Crossref DOI record; the typeset Elsevier journal PDF was not directly inspected, so all verified locators refer to `EWD687a`: `EWD687a - 0`–`2` (PDF pp. 3–5: diffusing computations from a single environment node, incoming deficit sum `C`, outgoing deficit sum `D`, invariants P0–P3 with `C > 0 ∨ D = 0` on internal nodes), `EWD687a - 3` (PDF p. 6: signalling guard `G : C > 1 ∨ (C = 1 ∧ D = 0)` and Theorem 1, bounded-step return of the environment to the neutral state once the computation proper terminates), `EWD687a - 4`–`5` (PDF pp. 7–8: invariant P4, pointed-bag "cornets" with oldest incoming "engagement edge", observations a)–c) establishing a rooted tree of engaged nodes, Theorem 2 proving that a neutral environment implies global termination, and the concluding remark that the single counter `D` suffices on the outgoing side).
The formalization in `Cslib.Distributed.DijkstraScholten` models the concrete asynchronous in-flight message-passing, single-parent (`Option P`) eager-acknowledgement overlay step toward #7286 rather than `EWD687a`'s atomic edge-deficit updates and general deferred-cornet obligation bags.

<a id="dilworth1950"></a>
## dilworth1950

Robert P. Dilworth.
"A Decomposition Theorem for Partially Ordered Sets."
*Annals of Mathematics* 51(1), 161–166, 1950. https://doi.org/10.2307/1969503 . Bibliographic metadata from search summaries, checked on 2026-11-08; the paper is paywalled and was not inspected.
The library attributes to it only the finite case of the decomposition theorem, whose formal statement follows [Schrijver's lecture notes](#schrijver17), Theorem 7.6.

<a id="dinic70"></a>
## dinic70

E. A. Dinic.
“Algorithm for Solution of a Problem of Maximum Flow in Networks with Power Estimation.”
*Soviet Mathematics Doklady* 11, 1277–1280 (1970).
This original paper was not consulted.
The bibliographic data come from secondary citations, and the manual attributes to it only the level-network and blocking-flow method and its phase bound, as these are standardly described.
Yefim Dinitz's historical account, “Dinitz' Algorithm: The Original Version and Even's Version” (in *Theoretical Computer Science: Essays in Memory of Shimon Even*, LNCS 3895, 218–240, Springer, 2006, https://doi.org/10.1007/11685654_10 ; bibliographic data checked against the Crossref record on 2026-11-08), is cited in the module docstrings for the history.
Its text was not inspected: the author-hosted PDF's text layer could not be extracted.

<a id="dinur2007"></a>
## dinur2007

Irit Dinur.
“The PCP Theorem by Gap Amplification.”
*Journal of the ACM* 54(3), Article 12 (2007).
DOI: https://doi.org/10.1145/1236457.1236459.
Author copy dated 2007-02-13 inspected: https://www.wisdom.weizmann.ac.il/~dinuri/mypapers/combpcp.pdf (opening definition and Theorem 1.1).

<a id="dinur2016"></a>
## dinur2016

Irit Dinur.
“Mildly Exponential Reduction from Gap 3SAT to Polynomial-Gap Label-Cover.”
*Electronic Colloquium on Computational Complexity*, Report TR16-128, 2016. https://eccc.weizmann.ac.il/report/2016/128/ . Bibliographic metadata checked against the ECCC report record; the report's full text was inspected for Hypothesis 2.5 (p. 5), which has at most $D n$ clauses and fixed soundness $< 0.9$.
Used alongside [manurangsiraghavendra2017](#manurangsiraghavendra2017) to document the Gap Exponential Time Hypothesis adaptation (`GapETH`, `rGapETH`) in [FineGrained/GapETH.lean](../CslibFrontier/Computability/Complexity/FineGrained/GapETH.lean).

<a id="dodisrabin2007"></a>
## dodisrabin2007

Yevgeniy Dodis and Tal Rabin.
"Cryptography and Game Theory."
Chapter 8 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 181–206, 2007. https://doi.org/10.1017/CBO9780511800481.010 . Bibliographic metadata checked in `references.bib`; the primary chapter PDF was not inspected locally in this pass, so locators (`Section 8.1.2`, `Section 8.4.1`, `Section 8.5.2`, `Definition 8.8`, `Footnote 9`, `p. 200`, `Theorem 8.9`) follow the pinned audit record and have not yet been verified against the primary source.
Cited by [Dominance.lean](../CslibFrontier/GameTheory/Strategic/Dominance.lean) (`IDoWDS`), [Payoff.lean](../CslibFrontier/GameTheory/Strategic/Payoff.lean) (`PayoffGame.WeaklyDominatesOn`, `PayoffGame.idowdsIter`), and [SecretSharing.lean](../CslibFrontier/GameTheory/RationalCrypto/SecretSharing.lean) (Halpern–Teague bounded-round `IDoWDS` collapse and the utility-dependent `k < n` geometric-termination protocol, with 1-shot stage `IDoWDS` survival proved on `geometricStageGame` for `(n, n)` sharing; the `k < n/2` and `k < n/3` regimes of Theorem 8.9 are not formalized).

<a id="dolev1982"></a>
## dolev1982

Danny Dolev.
"The Byzantine Generals Strike Again."
*Journal of Algorithms* 3(1), 14–30, 1982. https://doi.org/10.1016/0196-6774(82)90004-9 . Author-hosted scan: https://www.cs.huji.ac.il/~dolev/pubs/byz-strike-again.pdf (SHA-256 `e4fc84d5ef7b6d79c933cdcf682719a10bd99c80e00b74e67a0d5202e24a28cc`).
Checked against that scan on 2026-11-22 UTC by worker `connectivity`: §1, pp. 15–16 (`Agreement A` / Crusader Agreement and `Agreement B` / Byzantine Agreement for a single designated transmitter `z`, with the `t < k / 2` and `t < n / 3` threshold statement on p. 16); §2, pp. 17–21 (route-carrying messages, sets of up to `t` suspicious processors, the Purifying Algorithm on p. 19, and Theorem 1 on p. 19: reliable-transmitter delivery over `2t + 1` disjoint paths); §3, pp. 22–25 (`(Byz1)`–`(Byz2)` on p. 22 and the Crusader necessity bounds in Lemmas 3–5, pp. 23–25); §4, pp. 25–27 (`Algorithm CR`, Lemma 6 and Theorem 7); and §5, pp. 27–29 (`Algorithm BG`, Lemma 8, Theorem 9 and Corollary 10 on p. 29 for designated-transmitter broadcast when `n > 3t` and connectivity `> 2t`).
[ByzantineGraph/Connectivity.lean](../CslibFrontier/Computability/Distributed/ByzantineGraph/Connectivity.lean) adapts disjoint-path purification (`purifiedOM`, after §2 Theorem 1, p. 19, using strict majority over fixed simple paths rather than arbitrary-set suspicious-processor search) together with `Byzantine.om` ([lamportshostakpease1982](#lamportshostakpease1982)) to prove the synchronous fixed-round Boolean consensus upper bound (`solvesByzantineAgreement_purifiedOM`, `exists_solvesByzantineAgreement_of_le_iff`, `exists_solvesByzantineAgreement_iff`); Dolev's designated-transmitter broadcast (`Agreement B`, Corollary 10) and Crusader Agreement (`Agreement A`, Theorem 7) are not formalized there and remain open under [#7121](https://github.com/cslib-community/cslib-frontier/issues/7121).

<a id="dolevlynchpinterstarkweihl1986"></a>
## dolevlynchpinterstarkweihl1986

Danny Dolev, Nancy A. Lynch, Shlomit S. Pinter, Eugene W. Stark, and William E. Weihl.
"Reaching Approximate Agreement in the Presence of Faults."
*Journal of the ACM* 33(3), 499–516, 1986. https://doi.org/10.1145/5925.5931 ; author-hosted copy of the typeset journal PDF: https://groups.csail.mit.edu/tds/papers/Lynch/jacm86.pdf . Checked against `jacm86.pdf` (SHA-256 `56f1a805786c2145e78041ac9c5f17b1b05f495d08d1f037508ee4e9aac56a69`) on 2026-11-22 UTC: Section 2.1 (pp. 501–503, Lemmas 1–3 on `reduce^j` intersection loss and range containment), Section 2.2 (pp. 503–504, `f_{k, t}(V) = mean(select_k(reduce^t(V)))`, Lemma 4 validity, and Lemma 5 contraction by `c(m - 2t, k)`), Section 3 (pp. 505–508, synchronous nonterminating Algorithm $S_0$, Lemma 6, and dynamically halting Algorithm $S$ / Theorem 1 for `n ≥ 3t + 1`), Section 4 (pp. 508–511, single-hop asynchronous nonterminating Algorithm $A_0$ waiting for `n - t` round-`h` responses, Lemma 8, and dynamically halting Algorithm $A$ / Theorem 2 for `n ≥ 5t + 1`), and Section 7 (pp. 515–516, citing Fischer, Lynch and Merritt, ref.
[8], for the `3t + 1` synchronous lower bound, noting the `3t + 1` vs `5t + 1` asynchronous gap via Bracha's witness ideas, ref.
[2], and stating the fixed-round `r` diameter-contraction variant on p. 516).
Cited by [ApproxAgreement/TrimmedMidpoint.lean](../CslibFrontier/Computability/Distributed/ApproxAgreement/TrimmedMidpoint.lean) and [ApproxAgreement/Protocol.lean](../CslibFrontier/Computability/Distributed/ApproxAgreement/Protocol.lean), which formalize the two-endpoint midpoint specialization `midTrim` (`(min + max) / 2` of `trimmed t xs`, matching `f_{t, t}` at `n = 3t + 1` and `f_{2t, t}` at `n = 5t + 1`), fixed-horizon `R`-round counterparts of Algorithms $S_0$ and $A_0$ (`syncApproxProtocol`, `asyncApproxProtocol`), and unit-interval `[0, 1]`, fixed-horizon milestone predicates (`SolvesUnitSyncApproxAgreement`, `SolvesUnitAsyncApproxAgreement`) toward `#7116` and `#3261`; unbounded-input dynamic halting (Algorithms $S$ and $A$, Theorems 1 and 2) remains open under `#7116`.

<a id="dolevstrong1983"></a>
## dolevstrong1983

Danny Dolev and H. Raymond Strong.
"Authenticated Algorithms for Byzantine Agreement."
*SIAM Journal on Computing* 12(4), 656–666, 1983. https://doi.org/10.1137/0212045 . Inspected on 2026-11-22 UTC against the published journal PDF (11 pages, printed pp. 656–666, SHA-256 `6067a27c37468c41c4b43fe3e6bab95b1829b74883625d944d6ce77756e165bb`, https://www2.imm.dtu.dk/courses/02220/2015/L12/DolevStrong83.pdf): §1 (pp. 656–657) and §2 (pp. 657–659) for synchronous single-sender agreement and correctness/decision rules (`n ≥ 3`, `t ≤ n` in the paper); §4 (pp. 661–662) for the nested authentication label syntax `(label a)p` and semantics; and §4, Theorem 3 (pp. 662–663) for the `(t + 1)`-phase two-value-capped broadcast algorithm using at most two messages per directed edge (`O(e) = O(n²)`).
Cited by [Byzantine/DolevStrong.lean](../CslibFrontier/Computability/Distributed/Byzantine/DolevStrong.lean), which enforces Theorem 3's dealer-rooted exact-phase-length chains (`c.signers.getLast? = some dealer`, `c.signers.length = r + 1 ≤ t + 1`, `Nodup`, `i ∉ c.signers`) and forwarding only to recipients `dst ∉ c.signers` (`≤ 2 * (n - F.card) * (n - 1)` point-to-point `SignedChain` transmissions in `AuthProtocol.correctMessagesSent`), generalizes `P` and `t` to arbitrary `[Fintype P]` and `[DecidableEq V]` using `[LinearOrder P]` (`Finset.min'`) in place of Theorem 3's lexicographic message order, and abstracts signatures via value-level execution-trace provenance (`AuthProtocol.WellSigned` and `AuthProtocol.Unforgeable`) rather than nested syntactic labels.

<a id="dosasgall2013"></a>
## dosasgall2013

György Dósa and Jiří Sgall.
"First Fit bin packing: A tight analysis."
*30th International Symposium on Theoretical Aspects of Computer Science (STACS 2013)*, LIPIcs 20, 538–549, 2013. https://doi.org/10.4230/LIPIcs.STACS.2013.538 . Worker w156-ff read the open-access LIPIcs PDF on 2026-11-08 UTC and checked these parts: the weight function of Section 1.2 (scaled size `6/5 · a` plus a bonus); the observation there that every bin weighs at most `1.7`; Lemma 1.1, the amortization step; and the Section 1.1 history of the additive constants.
[FirstFitWeight](../CslibFrontier/Algorithms/Lean/BinPacking/FirstFitWeight.lean) cites these locators.
The constant `+0.9` is credited there to Garey, Graham, Johnson and Yao (ref.
[4]), and `+0.7` to Xia and Tan (ref.
[15]); both attributions are reported only via this paper.
The absolute bound `FF ≤ 1.7 · Opt` (Theorem 3.13) and the lower bounds of Section 4 (Lemma 4.1, Theorem 4.2) were read but are not formalized.
The small instances for `Opt ≤ 9` at the end of the proof of Theorem 4.2 (`i` items each of sizes `1/6 - 2δ`, `1/3 + δ` and `1/2 + δ`) are checked for `i = 3` and `i = 9` in [BinPackingFirstFitWeight](../CslibFrontierTests/BinPackingFirstFitWeight.lean).

<a id="dworklynchstockmeyer1988"></a>
## dworklynchstockmeyer1988

Cynthia Dwork, Nancy Lynch, and Larry Stockmeyer.
"Consensus in the Presence of Partial Synchrony."
*Journal of the ACM* 35(2), 288–323, 1988. https://doi.org/10.1145/42282.42283 . All 36 pages (pp. 288–323) of the MIT CSAIL TDS PDF (https://groups.csail.mit.edu/tds/papers/Lynch/jacm88.pdf ; 3,187,769 bytes, SHA-256 `d307503b15594d2cbd6c1ca6be1bd13666e03e90c097096d9cd35aedc19777cb`) were inspected firsthand on 2026-11-22 UTC: Section 1.2 (pp. 289–292) and Table I (p. 291), separating unconditional pre-stabilization safety from post-stabilization termination across fault models and noting on p. 291 that in the unauthenticated Byzantine case the `N ≥ 3t + 1` "only if" direction follows immediately from the completely synchronous result of Pease, Shostak and Lamport (ref.
[15]); Sections 2.1–2.4 (pp. 293–295), defining fail-stop, omission, and Byzantine faults with and without authentication alongside consistency, eventual termination, strong unanimity (`∀ i, x i = v` when any process in `C` decides), and weak unanimity (`∀ i, x i = v` when `C` contains all processes); Section 3.1 (p. 295), defining the basic round model with reliable correct-to-correct delivery from `GST` onward; Section 3.2.1 (pp. 296–298, Algorithm 1, Lemmas 3.1–3.3, Theorem 3.1) for omission/fail-stop faults (`N ≥ 2t + 1`); Sections 3.2.2–3.2.3 (pp. 298–302, Algorithms 2–3, Figure 1 on p. 301, Lemmas 3.4–3.9, Theorems 3.2–3.3, and Remark 1 on p. 302 noting `O(t)` post-GST round complexity) for Byzantine faults (`N ≥ 3t + 1`); Section 4.1 (pp. 303–304, Theorem 4.1), reducing synchronous processors with eventual message-delay bound `Δ` to the basic round model; and Section 4.3 (pp. 305–306), establishing the weak-unanimity lower bounds for `2 ≤ N ≤ 2t` omission/fail-stop faults (Theorem 4.3, pp. 305–306) and `2 ≤ N ≤ 3t` authenticated Byzantine faults (Theorem 4.4, p. 306).
[PartialSynchrony/Basic.lean](../CslibFrontier/Computability/Distributed/PartialSynchrony/Basic.lean) and [PartialSynchrony/Liveness.lean](../CslibFrontier/Computability/Distributed/PartialSynchrony/Liveness.lean) formalize the Section 3.1 basic round model (`PartialSyncProtocol`, `IsGST`) directly; instead of Algorithms 1 and 3's alternating trying/lock-release phases, monotone `PROPER`-set piggybacking on every message, and continuous Srikanth–Toueg echo simulation across all subsequent rounds, they give original three- and six-subround rotating-coordinator view-based quorum-locking protocols (`omissionQuorumProtocol` with three subrounds per view for `2 * t < Fintype.card P`, and `byzQuorumProtocol` with six subrounds per view—using a two-round `t + 1` / `n - t` unauthenticated status and input-properness relay followed by echo, vote/lock, and commit quorums—for `3 * t < Fintype.card P`, achieving strong correct-input validity `∀ i ∉ F, x i = v` and bounded decision by `gst + 6 * (t + 2)`).
`not_omissionPartialSync_weakUnanimity` (with immediate corollary `not_solvesOmissionPartialSync`) proves Theorem 4.3's pre-GST two-group healed-partition lower bound (`2 ≤ |P| ≤ 2t`) under weak unanimity (`F = ∅`, `∃ gst, IsGST deliver ∅ gst`) in the basic round model, while `not_solvesByzantinePartialSync` proves the unauthenticated Byzantine `2 ≤ |P| ≤ 3t` lower bound (with correct-input validity) by specializing at `GST = 0` to synchronous covering (`Cslib.Distributed.Byzantine.Protocol.state_eq_coverState`), as noted on p. 291.
The real-time step-group simulations for synchronous processors with eventual or unknown `Δ` (Theorems 4.1–4.2, pp. 303–305), the authenticated Byzantine protocols and weak-unanimity partition lower bound (Algorithm 2, §3.2.2, and Theorem 4.4, p. 306), and partially synchronous processors (Sections 5–6, pp. 306–322) are not formalized.

<a id="dworkroth14"></a>
## dworkroth14

Cynthia Dwork and Aaron Roth.
*The Algorithmic Foundations of Differential Privacy*.
Foundations and Trends in Theoretical Computer Science 9(3–4), 211–407, 2014. https://doi.org/10.1561/0400000042 . Definition 2.4, Proposition 2.1, Theorem 2.2 and its footnote, §2.3, Claim 3.5, Theorem 3.16, Definition 3.7, Theorem 3.20, Corollary 3.21, Theorem B.1 and Corollary B.2 were checked against the published PDF on 2026-11-07.
Theorem 8.2 (pp. 161–162), Lemma 8.3 and the proof of Theorem 8.2 (pp. 162–163), Lemma 8.4 and Corollary 8.5 (p. 165), Theorem 8.7 (p. 166), Theorem 8.8 with its proof and Claim 8.9 (pp. 167–169), and the bibliographic notes of §8.3, which credit Theorem 8.2 to Dwork, McSherry and Talwar (p. 170) and Theorem 8.8 to De (p. 171), were checked on 2026-11-08 against the authors' open version (https://www.cis.upenn.edu/~aaroth/Papers/privacybook.pdf), whose page numbers these are.

<a id="edmonds65"></a>
## edmonds65

Jack Edmonds.
"Maximum Matching and a Polyhedron with 0,1-Vertices."
*Journal of Research of the National Bureau of Standards, Section B* 69B(1–2), 125–130, 1965. https://doi.org/10.6028/jres.069B.013 . Cited only as the origin of polynomial-time minimum-weight perfect matching, which the library does not formalize; the bibliographic details come from search summaries and the paper was not checked.

<a id="edmonds67b"></a>
## edmonds67b

Jack Edmonds.
"Optimum Branchings."
*Journal of Research of the National Bureau of Standards, Section B* 71B(4), 233–240, 1967. https://doi.org/10.6028/jres.071B.032 . Bibliographic metadata checked against the Crossref record on 2026-11-08.
Section 2 (the reduction of optimum spanning arborescences with a prescribed root to optimum branchings; arcs are directed away from the root), Theorem 1 (stated in Section 3: a *good*, that is polynomially bounded, algorithm for optimum branchings exists) and Section 4 (the algorithm, which selects the best arc into each node and contracts cycles, and its proof) were checked against the open NIST PDF on 2026-11-08.
The library formalizes the Section 1 branching characterization, the Section 2 weight-shift reductions, the Section 4 contraction algorithm (including materialized `Vector`-table solvers and standard-basis Word-RAM programs running in `C * (n + 1) ^ 3` instructions at every word width `w` satisfying `Fits w I.wordBound`, i.e., `I.wordBound < 2 ^ w`, where the polynomial `wordBound` bounds word values and addresses so a width `w` of order `log(n + 2) + log(M₀ + 2)` bits suffices), and the polynomial-time content of Theorem 1 on binary-weighted adjacency tables (`minArborescenceDec_mem_P`, `minOutArborescenceDec_mem_P`, `maxBranchingDec_mem_P`).
Theorem 2 (Section 5, the branching polytope) and sparse `O(m log n)` / `O(m + n log n)` implementations are not formalized.

<a id="eisenberggale1959"></a>
## eisenberggale1959

Edmund Eisenberg and David Gale.
"Consensus of Subjective Probabilities: The Pari-Mutuel Method."
*The Annals of Mathematical Statistics* 30(1), 165–168, 1959. https://doi.org/10.1214/aoms/1177706369 . Bibliographic metadata only (library key `EisenbergGale1959`); the journal PDF was not directly inspected, so internal theorem and page locators remain `unverified` in the results registry.
Cited as the origin of the Eisenberg–Gale convex program formalized in [EisenbergGale.lean](../CslibFrontier/GameTheory/Market/EisenbergGale.lean).

<a id="epsteinfeldmanmansour09"></a>
## epsteinfeldmanmansour09

Amir Epstein, Michal Feldman and Yishay Mansour.
*Strong Equilibrium in Cost Sharing Connection Games*.
Games and Economic Behavior 67(1), 51–68, 2009. https://doi.org/10.1016/j.geb.2008.07.002 . Bibliographic metadata only, as given in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, reference [4], and checked against the Crossref record of the DOI.
The paper's text was not inspected, so no locator in it is cited, and which notion of strong equilibrium it uses was not checked.
The `H_k` bound on the cost of strong Nash equilibria of fair cost-sharing games is attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #15, Theorem 3.2, and proved following that lecture.
The lecture states it for its weak-deviation notion (Definition 3.1, `IsStrongNash`), but its proof only uses that no coalition can make every member strictly better off (footnote 2 notes that the stronger inequality is not needed).
So the library proves the bound for the all-strict notion `IsStrongEquilibrium` of [babaioffchuangfeldman07](#babaioffchuangfeldman07), Exercise 23.6, which contains every strong Nash equilibrium.

<a id="erdos1947"></a>
## erdos1947

Paul Erdős.
“Some Remarks on the Theory of Graphs.”
*Bulletin of the American Mathematical Society* 53(4), 292–294, 1947. https://doi.org/10.1090/S0002-9904-1947-08785-1 . Bibliographic metadata checked on 2026-11-07; the full text was not inspected in this pass.
The manual attributes only the counting lower bound `2 ^ (k / 2) < R(k, k)` to this paper; the formal statement follows Alon–Spencer, *The Probabilistic Method*, Proposition 1.1.1, as cited in the Lean documentation.

<a id="erdosszekeres1935"></a>
## erdosszekeres1935

Paul Erdős and George Szekeres.
“A Combinatorial Problem in Geometry.”
*Compositio Mathematica* 2, 463–470, 1935. http://www.numdam.org/item/CM_1935__2__463_0/ . The graph-theoretic Ramsey theorem and its induction, pp. 465–467, give the upper bound `R(k, l) ≤ C(k + l − 2, k − 1)`; the agent review of the introducing PR checked pp. 466–467 against the Numdam PDF.
The monotone subsequence theorem (the Theorem on p. 467 for `n` points and its `f(i, k) = (i − 1)(k − 1) + 1` form with the matching construction on p. 468, where equal values may count as increasing or decreasing) was checked against the same PDF on 2026-11-08 for `CslibFrontier.Foundations.Combinatorics.ErdosSzekeres`.

<a id="erickson24"></a>
## erickson24

Jeff Erickson, Ivor van der Hoog, Tillmann Miltzow.
“Smoothing the Gap Between NP and ∃R.”
*SIAM Journal on Computing* 53(6), FOCS20-102–FOCS20-138, 2024. https://doi.org/10.1137/20M1385287 . Author preprint consulted: https://arxiv.org/abs/1912.02278v3 , §6.1.
Published metadata comes from the pinned bibliography; the consulted preprint is dated 2021.

<a id="fabrikantluthramanevapapadimitrioushenker03"></a>
## fabrikantluthramanevapapadimitrioushenker03

Alex Fabrikant, Ankur Luthra, Elitza Maneva, Christos H. Papadimitriou and Scott Shenker.
"On a Network Creation Game."
*Proceedings of the Twenty-Second Annual Symposium on Principles of Distributed Computing (PODC 2003)*, 347–351, ACM, 2003. https://doi.org/10.1145/872035.872088 (bibliography key `FabrikantLuthraManevaPapadimitriouShenker2003`).
Bibliographic provenance from [tardoswexler07](#tardoswexler07), §19.2, §19.5.1 and p. 512 bibliography (correcting the chapter bibliography's `C. Shenker` and `pp. 247–351` to `Scott Shenker` and `347–351` as in `references.bib`); the paper's full text was not inspected firsthand, so internal theorem and page locators are recorded as `unverified` in [Entries/LocalConnection.lean](../CslibFrontierResults/Entries/LocalConnection.lean).
The local connection game model, social-optimum and star/clique stability characterizations, `3d` diameter-to-PoA reduction, and `O(√α)` equilibrium-diameter and price-of-anarchy bounds in [NetworkFormation/LocalConnection.lean](../CslibFrontier/GameTheory/NetworkFormation/LocalConnection.lean) follow [tardoswexler07](#tardoswexler07), §19.2.1–§19.2.3 (pp. 490–493).

<a id="fabrikantpapadimitrioutalwar04"></a>
## fabrikantpapadimitrioutalwar04

Alex Fabrikant, Christos H. Papadimitriou, and Kunal Talwar.
*The Complexity of Pure Nash Equilibria*.
Proceedings of the 36th Annual ACM Symposium on Theory of Computing (STOC 2004), 604–612. https://doi.org/10.1145/1007352.1007445 . Bibliographic metadata checked against Crossref on 2026-11-08; the PLS-completeness theorem is attributed as cited in Roughgarden's CS364A Lecture #19, Theorem 3.1.
The paper itself was not consulted.

<a id="falcon2020"></a>
## falcon2020

Falcon team.
*Falcon: Fast-Fourier Lattice-Based Compact Signatures over NTRU*, NIST Post-Quantum Cryptography Standardization Round 3 submission, version 1.2, 2020.
[Official archive](https://csrc.nist.gov/CSRC/media/Projects/post-quantum-cryptography/documents/round-3/submissions/Falcon-Round3.zip).
Checked on 2026-11-13 against archive SHA-256 `fd58f0454f6bfb4713734e60b2d2d75d96fbae62d5180fceeef1039df5362f44`; the enclosed specification has SHA-256 `fec58c4c7e2f1712413c1e77994886c6f1f40f1cc7ec5fa650f132927ca07cd6`, and `KAT/falcon512-KAT.rsp` has SHA-256 `dd75c946fdedef4ec46a2bee7e10c65c9126f1a839b9ced6921fd45f7354b5cd`.
`CslibFrontier.Crypto.Falcon` maps Algorithm 3, Algorithm 14's 64-bit threshold distribution and lazy byte comparison, Algorithms 16 and 18 and Section 3.11.6 to its current verification and sampler interfaces.
Algorithm 14, lines 4–10 on printed p. 43, computes a uint64 threshold `z`; lines 5–10 compare its bytes most-significant first and return one with exact probability `2^-64 * z`.
The archive's `Reference_Implementation/falcon512/falcon512int/sign.c::BerExp` assigns the threshold at line 1074 and implements the lazy comparison at lines 1082–1087; `inner.h::prng_get_u8`, lines 565–577, supplies each visited byte and refills its buffer when necessary.
The formal fixed-threshold interface proves the exact conditional law.
Its lazy companion uses the shared `Byte` and `natToFixedBytesBE` boundary, makes one eight-fair-bit draw per visited byte, records the one-to-eight-byte trace and exact source ledger of one draw, subtraction, loop equality test and eight fair bits per byte with zero external resources, proves the same complete decision distribution, and proves that reading past the first byte has probability `2^-8`.
The comparison coordinate excludes the one final sign extraction and loop-index tests.
These are source operations, not Lean or native steps.
It does not formalize the floating-point approximation that produced `z`, PRNG-buffer refills, `BaseSampler`, `SamplerZ`, the Gaussian or retry law, or native resource use.
In `Reference_Implementation/falcon512/falcon512int/shake.c`, `i_shake256_inject`, `i_shake256_flip` and `i_shake256_extract` confirm the 136-byte rate chunks, least-significant-byte lane convention, `0x1F` domain/padding byte and final `0x80` bit; `common.c`'s `hash_to_point_vartime` consumes successive output bytes as big-endian 16-bit words.
The SHAKE256 client checks `count = 0`'s exact 40-byte salt followed by its 33-byte message against the first 20 output bytes; these finite fixtures are not a full key/signature KAT verification, a complete Gaussian sampler, a native resource certificate or a claim about the still-developing FIPS 206 standard.

<a id="feige1998"></a>
## feige1998

Uriel Feige.
"A Threshold of ln n for Approximating Set Cover."
*Journal of the ACM* 45(4), 634–652, 1998. https://doi.org/10.1145/285055.285059 . Bibliographic metadata checked via search records only; primary text uninspected and internal theorem locators unverified (no numbered paper theorems claimed).
Cited for the Set Cover hardness threshold framework using separating partition gadgets.

<a id="feigenbaumpapadimitrioushenker2001"></a>
## feigenbaumpapadimitrioushenker2001

Joan Feigenbaum, Christos H. Papadimitriou and Scott Shenker.
"Sharing the Cost of Multicast Transmissions."
*Journal of Computer and System Sciences* 63(1), 21–41, 2001 (preliminary version in STOC 2000). https://doi.org/10.1006/jcss.2001.1754 . Bibliographic metadata checked via DOI and secondary search summaries on 2026-11-24; the published PDF was not inspected directly, so internal page numbers are not claimed.
Cited by [MulticastCostSharing.lean](../CslibFrontier/GameTheory/Cooperative/MulticastCostSharing.lean) for the comparison of Shapley (`SH`) and Marginal Cost (`MC` / Clarke VCG) multicast cost sharing on rooted trees, the exact two-pass (`2` messages per link) distributed tree algorithm for `MC` receiver selection and VCG payments, failure of group-strategyproofness for `MC`, and the deterministic `(k + 1)`-bit cut communication lower bound for `SH` on path instances (leaving the paper's randomized lower bound open).

<a id="feigenbaumschapirashenker2007"></a>
## feigenbaumschapirashenker2007

Joan Feigenbaum, Michael Schapira and Scott Shenker.
"Distributed Algorithmic Mechanism Design."
Chapter 14 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 363–384. https://doi.org/10.1017/CBO9780511800481.016 . Bibliographic metadata checked via DOI and secondary search summaries on 2026-11-24; the chapter PDF was not inspected directly, so internal section, theorem, and exercise numbers are not claimed in [MulticastCostSharing.lean](../CslibFrontier/GameTheory/Cooperative/MulticastCostSharing.lean).
Cited by [MulticastCostSharing.lean](../CslibFrontier/GameTheory/Cooperative/MulticastCostSharing.lean) alongside [FeigenbaumPapadimitriouShenker2001](#feigenbaumpapadimitrioushenker2001) and [MoulinShenker2001](#moulinshenker2001) for distributed multicast cost sharing (`SH` vs. `MC`, the two-pass VCG tree algorithm, and cut communication lower bounds), and by `CslibFrontier/GameTheory/InterdomainRouting/{GaoRexford,StablePaths}.lean`.

<a id="fey04"></a>
## fey04

Mark Fey.
*May's Theorem with an Infinite Population*.
Working paper, Department of Political Science, University of Rochester, May 2002, revised April 2003, corrected May 2004 (published in *Social Choice and Welfare* 23(2), 275–293, 2004, https://doi.org/10.1007/s00355-003-0256-3 ).
Library bibliography key `Fey2004`.
Inspected the 30-page author-hosted May 2004 manuscript PDF (SHA-256 `ba260bbe2276cf6f53b53ebe7440b6e01d1a316a6f90644b6a6f1198d0590de1`) on 2026-11-24 UTC: §1, p. 1 (statement of May's theorem characterizing finite-electorate majority rule over two alternatives by anonymity, neutrality and positive responsiveness); §2, Definition 1, p. 5 (neutrality, monotonicity and positive responsiveness on strict two-alternative ballots with social ties) and Definition 2, p. 7 (strong permutation anonymity); and §3, Definition 3 and Lemma 1, pp. 7–8, with §4.2, Theorem 2 and footnote 13, pp. 13–15 (free ultrafilters as purely finitely additive `{0, 1}`-measures and their connection to [fishburn70](#fishburn70)).
Cited by [SocialChoice/May.lean](../CslibFrontier/GameTheory/SocialChoice/May.lean).

<a id="fgms20"></a>
## fgms20

John Fearnley, Spencer Gordon, Ruta Mehta and Rahul Savani.
"Unique End of Potential Line."
*Journal of Computer and System Sciences* 114, 1–35, 2020. https://doi.org/10.1016/j.jcss.2020.05.007 . Checked on 2026-11-11 against the arXiv TeX source of `arXiv:1811.03841v1` (https://arxiv.org/abs/1811.03841 , dated 9 November 2018): Section 2 ("Unique End of Potential Line"), Definition 9 (`EndOfPotentialLine`, `\label{def:EOPL}`, solution types `(R1)` and `(R2)` under `P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0` with `V : {0, 1}^n → {0, …, 2^m - 1}`) and the complexity class `EOPL` with `EOPL ⊆ PLS ∩ PPAD`.
`CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/PotentialLine.lean` formalizes uniform polynomial-time `EOPL` and `SOPL` families, totalized `(R1)/(R2)` violation relations (`mem_EOPL_iff_violation`, `mem_SOPL_iff_violation`), and `EOPL ⊆ PLS ∩ PPAD`.
`CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/PotentialLineNormalization.lean` formalizes the uniform polynomial-time `(n + 1)`-bit normalization to the exact syntactic source conditions `PromisedPotentialLine` (`P(0^n) = 0^n ≠ S(0^n)` and `V(0^n) = 0`), pure `(R1)/(R2)` relations (`endOfPotentialLinePromisedRel`, `sinkOfPotentialLinePromisedRel`), and unary potential bit-bounds (`mem_EOPL_iff_promised_bounded`, `mem_SOPL_iff_promised_bounded`).
Both modules use uniform polynomial-time families rather than canonical Boolean circuit codes; `UEOPL`, `CLS`, and the journal version's numbering were not formalized or separately checked.

<a id="fiatkarplubymcgeochsleatoryoung91"></a>
## fiatkarplubymcgeochsleatoryoung91

Amos Fiat, Richard M. Karp, Michael Luby, Lyle A. McGeoch, Daniel D. Sleator and Neal E. Young.
"Competitive Paging Algorithms."
*Journal of Algorithms* 12(4), 685–699, 1991. https://doi.org/10.1016/0196-6774(91)90040-6 . Checked on 2026-11-11 and 2026-11-24 against the arXiv TeX source of `arXiv:cs/0205038v1` (https://arxiv.org/abs/cs/0205038 , submitted 24 May 2002; tarball SHA-256 `d07934f721cafd79cbe10d70ca1f19ad9efb78ab239b3edc41a446c24ed80c6d`, `marking.tex`): Section 3 ("The marking algorithm", Theorem 1 `\label{markingthm1}` for `2 H_k`-competitiveness on `n` vertices, Theorem 2 `\label{markingthm2}` for `H_{n-1}`-competitiveness of `(n - 1)`-server uniform paging on `n` vertices, and the `k = 2, n = 4` non-`H_2`-competitiveness example) and Section 5 ("A lower bound", Theorem 4 and Corollary 5 stating that no randomized algorithm for the uniform `k`-server problem on `n` vertices is `c`-competitive with `c < H_k` when `1 ≤ k ≤ n - 1`).
`CslibFrontier/DataStructure/Paging/Marking.lean` formalizes Theorem 1 over `Paging.problem α k` via `Online.BehavioralStrategy` with three local adaptations: (1) pages range over any `[DecidableEq α]` type rather than a finite `n`-vertex uniform metric; (2) initialization covers any admissible cache `|s₀| ≤ k` (inserting without eviction while `|cache| < k`) with additive constant `0`, rather than only a full initial cache `{1, …, k}`; and (3) `cleanCount_le_two_mul_scheduleCost` proves `#clean ≤ 2 · OPT` directly against arbitrary (not necessarily lazy) valid offline schedules without invoking the Manasse–McGeoch–Sleator lazy-schedule reduction.
`CslibFrontier/DataStructure/Paging/RandomizedLowerBound.lean` formalizes Section 5 (Theorem 4 and Corollary 5) via the oblivious subphase/phase nemesis construction for both `Online.BehavioralStrategy` and `Online.RandStrategy` from any admissible initial cache (`not_isCompetitiveFrom_behavioral_of_lt`, `not_isCompetitiveFrom_rand_of_lt`), Section 3 Theorem 2 (`markingStrategy_isCompetitive_of_card_le`, `(H_k, 0)`-competitiveness when `Fintype.card α ≤ k + 1`), and the `k = 2, n = 4` separation (`markingStrategy_not_isCompetitive_harmonic_two_fin_four`).
Algorithm EATR (Section 4, Theorem 3), combining online algorithms (Section 6), unequal-capacity bounds, and the published journal's pagination were not formalized or separately checked.

<a id="fidge1988"></a>
## fidge1988

Colin J. Fidge.
"Timestamps in Message-Passing Systems That Preserve the Partial Ordering."
*Proceedings of the 11th Australian Computer Science Conference* (*Australian Computer Science Communications* 10(1)), 56–66, 1988; open proceedings scan at https://classpages.cselabs.umn.edu/Spring-2018/csci8980/Papers/Foundations/fidge.pdf . Checked against that 11-page proceedings scan (SHA-256 `dabbb981c6af43431443a8b18ad8e360012d865abeaa597d6b22bbe22bdcc612`, complete printed pp. 56–66) on 2026-11-22 UTC by worker `vector-clocks`: "Asynchronous Communication", pp. 58–59, and Appendix A, pp. 64–65 (timestamp arrays `[c_1, …, c_n]` maintained by Rules RA1–RA5, p. 58, and compared by Equation EA1 `e_p → f_q ↔ T_{e_p}[p] < T_{f_q}[p]`, p. 59); and "Synchronous Communication", pp. 60–62, and Appendix B, pp. 65–66 (CSP bidirectional exchange Rules RS1–RS4 and Equation ES1, not formalized here).
Note that Fidge's asynchronous Rule RA4 (p. 58) additionally sets `local_array[q] := 1 + other_array[q]` for the sender `q` when `local_array[q] ≤ other_array[q]` so that EA1 uses strict `<`, whereas `Execution.vc` (`vcNext`) in [VectorClock/Clocks.lean](../CslibFrontier/Computability/Distributed/VectorClock/Clocks.lean) implements [mattern1989](#mattern1989)'s pure componentwise-`sup` and owner-only-increment rule, where `e₁ < e₂ ↔ vc e₁ e₁.actor ≤ vc e₂ e₁.actor` for `e₁ ≠ e₂`.

<a id="fips1804"></a>
## fips1804

National Institute of Standards and Technology.
*Secure Hash Standard*, Federal Information Processing Standards Publication 180-4, 2015. https://doi.org/10.6028/NIST.FIPS.180-4 . Checked on 2026-11-14 against the official August 2015 PDF (SHA-256 `5b88d70308c95106e713221c7085cbb8e89dc2eb6214d75c885af2f07ffc6b8a`): Sections 4.1.2 and 4.1.3 define the SHA-256 and SHA-512 logical functions, Sections 4.2.2 and 4.2.3 give the round constants, Sections 5.1.1 and 5.1.2 give padding and length encoding, Sections 5.2 and 5.3 give parsing and initial states, and Sections 6.2 and 6.4 give the hash computations.
`CslibFrontier.Crypto.Primitives.ByteString` supplies typed byte strings and big-endian conversion, and `CslibFrontier.Crypto.Primitives.Hash.SHA2` supplies byte-aligned SHA-256 and SHA-512 with the source input-length domains.
The official [SHA-256 example PDF](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA256.pdf) (SHA-256 `7006b6549dad2fc8c6f29417a921f2e48208157ef496a7e1e1d7d17c5cc1e7db`) supplies `abc` at input p. 1 and digest p. 3, and the two-block example at input p. 3 and digest p. 6.
The official [SHA-512 example PDF](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA512.pdf) (SHA-256 `84ce867c99bad5a7b05abc74bb1dfc9de8486f49a160653cc8b15272cc532115`) supplies `abc` at input p. 1 and digest p. 4, and the two-block example at input p. 4 and digest p. 11.
These executable specifications are not constant-time or machine-costed implementations, security proofs, or NIST validations.

<a id="fips1981"></a>
## fips1981

National Institute of Standards and Technology.
*The Keyed-Hash Message Authentication Code (HMAC)*, Federal Information Processing Standards Publication 198-1, 2008. https://doi.org/10.6028/NIST.FIPS.198-1 . Checked on 2026-11-24 against the official PDF (SHA-256 `67661ba1407b391c799ff407471de18f36697af51d78a777e817c067ac30da23`): Section 2.3 defines the block size and `ipad`/`opad` and bounds the text at fewer than `2^B - 8B` bits, Section 3 states the preliminary hashing rule for keys longer than the block, and Section 4 with Table 1 defines all three block-sized `K0` branches and the nested equation `H((K0 xor opad) || H((K0 xor ipad) || text))`.
`CslibFrontier.Crypto.Primitives.Hash.HMAC` instantiates the complete construction with total SHA-256 and SHA-512 functions, which are the source's HMAC while a hashed key and the inner hash input are inside the SHA-2 message-length domain and apply the same steps to the total SHA-2 functions elsewhere, and proves that zero bytes appended to a key that still fits in one block do not change the result.
It returns full digests and does not claim truncation rules, pseudorandomness, MAC security, constant-time execution or NIST validation.

<a id="fips202"></a>
## fips202

National Institute of Standards and Technology.
*SHA-3 Standard: Permutation-Based Hash and Extendable-Output Functions*, Federal Information Processing Standards Publication 202, 2015. https://doi.org/10.6028/NIST.FIPS.202 . Checked on 2026-11-13 against the published August 2015 PDF (SHA-256 `1592607831ff0908cc590632ce371c6c95e94025bb1a0c8ae90a4d0ec1ed025e`): Sections 3.1.2--3.1.3 give the bit-string/state correspondence, Sections 3.2--3.3 and Algorithms 1--7 give the five round maps and round function, Section 4 and Algorithm 8 give the permutation-backed sponge construction, Section 5.1 and Algorithm 9 give `pad10*1`, Section 6.1 defines SHA3-512 as `KECCAK[1024](M || 01, 512)`, and Section 6.2 defines SHAKE128 as `KECCAK[256](M || 1111, d)` and SHAKE256 as `KECCAK[512](M || 1111, d)`.
The official NIST [SHA3-512 0-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA3-512_Msg0.pdf) and [SHA3-512 1600-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHA3-512_1600.pdf) examples were checked on 2026-11-16 with SHA-256 hashes `6d0a6fecea7babaffe9f3b09058fdb1590576e52b9dbfe0a637705db6f7de248` and `2f5f6ca71c3bd7bf3e99d142f7c4035b1e3fea95d7fc7e7a79a38ce995388211`.
The official NIST [SHAKE128 0-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE128_Msg0.pdf), [SHAKE128 1600-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE128_Msg1600.pdf), [SHAKE256 0-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE256_Msg0.pdf) and [SHAKE256 1600-bit](https://csrc.nist.gov/CSRC/media/Projects/Cryptographic-Standards-and-Guidelines/documents/examples/SHAKE256_Msg1600.pdf) examples were checked with SHA-256 hashes `3013d904e0f6cebc8dad6393cbf3eed4d1a537b3b3dc5e7b48552ff597942974`, `437f905d9790ce7a18625b396ba57c6118bb46d1542ec3cf1d46faac23c261ef`, `d736c1a93eb6440e1e6b640402e31ea5258281b2b9237f84ea0ba4186518fc59` and `f4226f5c72914e5d2b331812c5973d8d685c8af1ccb97c2a3a2fd1c02fd173d1`.
`CslibFrontier.Crypto.Primitives.Hash.Keccak`, `.Keccak.Circuit`, `.Keccak.Efficient`, and `.Keccak.SHAKE128` implement the byte-aligned executable functions and their stated exact-permutation or asymptotic machine certificates; they do not claim cryptographic security, constant-time execution, a concrete whole-sponge cost, FIPS validation or a future FIPS 206 definition.

<a id="fips203"></a>
## fips203

National Institute of Standards and Technology.
*Module-Lattice-Based Key-Encapsulation Mechanism Standard*, Federal Information Processing Standards Publication 203, 2024. https://doi.org/10.6028/NIST.FIPS.203 . Checked on 2026-11-14 against the official published PDF (1,252,341 bytes; SHA-256 `fe1f12f32a7e44ec9fdebbf400cda843a40b506dee676725234dc6f7923b6cac`).
Section 4.1, Equations (4.3) and (4.6) define the SHAKE256 noise PRF and the one-shot/incremental SHAKE128 correspondence; Section 4.2.1, Algorithms 3–6 define least-significant-bit-first byte packing and `ByteEncode_d`/`ByteDecode_d`; Section 4.2.2, Algorithms 7–8 define SampleNTT's three-byte rejection parser and `SamplePolyCBD`; Section 5, Algorithms 13–15 define K-PKE, including `rho || j || i`; Section 6, Algorithms 16–18 defines the internal ML-KEM algorithms; Section 7, Algorithms 19–21 defines the ML-KEM interface, and Section 7.2, Equation (7.1) gives the public-key decode/re-encode check; Section 8, Table 2 gives the parameter sets.
The publication page currently links an errata/potential-updates workbook; these locators and claims map the published PDF.
The coefficient-level K-PKE modules record their model differences (uniform matrix, sampled coins, coefficient form), while the encoding/seed-expansion modules cover only the source-ready byte and finite-prefix boundaries described in their documentation.

<a id="fips205"></a>
## fips205

National Institute of Standards and Technology.
*Stateless Hash-Based Digital Signature Standard*, Federal Information Processing Standards Publication 205, 2024. https://doi.org/10.6028/NIST.FIPS.205 . Checked on 2026-11-13 against the official PDF (SHA-256 `8ef34228276f3386d23cb0da8c14592b8cfb0db3358016bba64df7a004f8d13d`): Section 4.2 and Figures 2–9 define the canonical 32-byte address and its seven type-specific layouts; Section 4.3 and Table 1 define the address setters, including clearing the final 12 bytes on every type change; Section 4.4 defines the unsigned big-endian integer encoding and Algorithm 4 defines `base_2b`; Section 5, Equations (5.1)–(5.4) fixes `lg_w = 4`, `w = 16`, `len1 = 2n`, `len2 = 3` and `len = 2n + 3` for `n = 16, 24, 32`; Algorithms 7 and 8, lines 1–7 define the shared message conversion and complement checksum, including the four-bit left shift and two-byte big-endian encoding; and Section 11.2, Figure 18 and Table 3 define the 22-byte compressed address used by the SHA2 parameter sets.
Checked on 2026-11-24 by agent `worker-6605-slhdsa` against the same PDF: Section 4.1 gives the argument and result lengths of the six hash calls, `PRF_msg : B^n × B^n × B* → B^n` and `H_msg : B^n × B^n × B^n × B* → B^m` among them; Algorithm 5 (printed p. 18) defines the chain iteration and its hash-address writes; Algorithm 8 (printed p. 21), lines 8–16, finishes the signature-selected chains and compresses their ordered endpoints with `T_len`; Section 6 and Figure 11 (printed p. 22) give the XMSS signature as `(h' + len) * n` bytes, a WOTS+ signature followed by `h'` authentication nodes; Algorithm 11 (printed p. 25) computes the WOTS+ public key of leaf `idx` and then makes `h'` ordered `H` calls with the specified tree-height and tree-index writes; Section 7.2 and Algorithm 13 (printed p. 28) give its next consumer, the hypertree verifier, which makes `d` Algorithm 11 calls and compares the last result with `PK.root`; Section 9 defines `m = ceil((h - h') / 8) + ceil(h' / 8) + ceil(k * a / 8)` and Table 2 (printed p. 43) lists `n`, `h`, `d`, `h'`, `a`, `k` and `m` for the parameter sets; Algorithm 19 (printed p. 35), lines 2–5, passes an `n`-byte `opt_rand` to `PRF_msg` and then calls `H_msg`; and Sections 11.1, 11.2.1 and 11.2.2 define the SHAKE and SHA2 instantiations of all six calls.
`CslibFrontier.Crypto.Primitives.SLHDSA.Address` formalizes the address-domain layer with typed 32-byte and 22-byte encodings, `SLHDSA.HashCalls` the four addressed calls `PRF`, `F`, `H` and `T_l`, `SLHDSA.MessageCalls` the two message calls `PRF_msg` and `H_msg`, `SLHDSA.WOTS.Digits` exactly the digit-preprocessing layer, `SLHDSA.WOTS.Chain` Algorithm 5, `SLHDSA.WOTS.PublicKeyFromSignature` Algorithm 8 and `SLHDSA.XMSS.PublicKeyFromSignature` Algorithm 11, with an equation for its address after each loop iteration.
They do not formalize digest slicing, WOTS+ key generation or signing, XMSS tree generation or signing, FORS, the hypertree, signing, verification or security analysis; in particular, nothing here proves that Algorithm 11 recovers the root of a generated tree.

FIPS 205 Section 11.2 additionally incorporates FIPS 198-1 HMAC and RFC 8017 MGF1 into the SHA-2 definitions of `PRF_msg` and `H_msg`.
`CslibFrontier.Crypto.Primitives.Hash.HMAC` and `CslibFrontier.Crypto.Primitives.Hash.MGF1` supply those shared primitives, including the full HMAC key preprocessing and MGF1's four-byte counters.
`CslibFrontier.Crypto.Primitives.SLHDSA.MessageCalls` builds the FIPS 205 `PRF_msg` and `H_msg` calls on them, with the parameter-set truncation and message packaging of Sections 11.1--11.2.2; it proves nothing about those calls beyond the lengths of their byte packages.

<a id="fischerlynch1982"></a>
## fischerlynch1982

Michael J. Fischer and Nancy A. Lynch.
"A Lower Bound for the Time to Assure Interactive Consistency."
*Information Processing Letters* 14(4), 183–186, 1982. https://doi.org/10.1016/0020-0190(82)90033-3 . Inspected on 2026-11-22 UTC against the published journal PDF (4 pages, printed pp. 183–186, SHA-256 `eaec1656212aa48d02f59032c81d9d0454a0776f7680a58f9c224e4abca1044d`, https://groups.csail.mit.edu/tds/papers/Lynch/ipl82.pdf): §§1–3 (pp. 183–184) for the synchronous `k`-round interactive consistency problem over `{0, 1} ⊆ V` (vector output agreeing across nonfaulty processors and recording each nonfaulty processor's private value at its own coordinate), §5 Theorems 3–4 (p. 185, restating the `n ≥ 3m + 1` bound of Pease, Shostak and Lamport), and §6 Theorem 5 (pp. 185–186, ruling out `k ≤ m` rounds).
Cited by [Byzantine/RoundBound.lean](../CslibFrontier/Computability/Distributed/Byzantine/RoundBound.lean) both for Theorem 5 on interactive consistency (`InteractiveProtocol.not_solvesInteractiveConsistency_of_rounds_le` under `[Nontrivial V]`, `t + 2 ≤ Fintype.card P`, `R ≤ t`, making explicit the `n ≥ t + 2` bound implicit in Theorem 5's `m = 0` base case and PSL invocation, with the `n = 2, t = 1` one-round boundary witnessed on `Fin 2`) and for its Boolean consensus adaptation (`Protocol.not_solvesByzantineAgreement_of_rounds_le` for `2 ≤ Fintype.card P`, `R ≤ t`, alongside the same-round majority adapter `InteractiveProtocol.toByzantineAgreement` / `InteractiveProtocol.solvesByzantineAgreement_toByzantineAgreement` from Boolean interactive consistency to Boolean consensus).

<a id="fischerlynchmerritt1985"></a>
## fischerlynchmerritt1985

Michael J. Fischer, Nancy A. Lynch and Michael Merritt.
"Easy Impossibility Proofs for Distributed Consensus Problems."
In *Proceedings of the Fourth Annual ACM Symposium on Principles of Distributed Computing (PODC '85)*, 59–70, 1985. https://doi.org/10.1145/323596.323602 . Checked against the PODC '85 scan at https://www.cs.cornell.edu/courses/cs614/2005fa/papers/FLM85.pdf (SHA-256 `373077db53f16f57a16bc1778385cdbf2b68b6701766f34ee4c385610f32ca86`) on 2026-11-22 UTC by worker `connectivity` (and independently checked by `reviewer-codex-edemaine` on PR #7157): §1, p. 59 (definition of *inadequate graphs* for `m` faults as `< 3m + 1` nodes or `< 2m + 1` vertex connectivity); §2, pp. 60–61 (directed communication graphs, Locality Axiom, Fault Axiom, and graph coverings); §3, p. 61 (Boolean inputs `{0, 1}`, Agreement on all correct nodes, Validity when all correct nodes share the same input, and Theorem 1: Byzantine agreement is impossible in inadequate graphs); §3.1, pp. 61–62 (six-group hexagon covering for `n ≤ 3m`); and §3.2, pp. 62–63 (split-cut two-copy eight-group covering `S` across `B ∪ D` with `|B|, |D| ≤ m` separating nonempty `A` and `C` via scenarios `S₁, S₂, S₃`).
Cited by [Byzantine/NodeBound.lean](../CslibFrontier/Computability/Distributed/Byzantine/NodeBound.lean), [ByzantineGraph/Basic.lean](../CslibFrontier/Computability/Distributed/ByzantineGraph/Basic.lean) and [ByzantineGraph/Connectivity.lean](../CslibFrontier/Computability/Distributed/ByzantineGraph/Connectivity.lean), which restrict to deterministic synchronous protocols on undirected `SimpleGraph P` deciding at a uniform fixed round `R` (`GraphProtocol.not_solvesByzantineAgreement_of_isVertexSeparator`).
Sections 4–7 (weak agreement, Byzantine firing squad, approximate agreement and clock synchronization) are not formalized in `ByzantineGraph/`.

<a id="fishburn70"></a>
## fishburn70

Peter C. Fishburn.
"Arrow's Impossibility Theorem: Concise Proof and Infinite Voters."
*Journal of Economic Theory* 2(1), 103–106, 1970. https://doi.org/10.1016/0022-0531(70)90015-3 . Library bibliography key `Fishburn1970`.
Bibliographic metadata checked in [fey04](#fey04) (References, p. 25, and footnote 13, p. 15) and against the DOI record on 2026-11-24 UTC; the published journal text was not inspected, so no internal theorem numbers are claimed.
Cited by [SocialChoice/WeakOrder.lean](../CslibFrontier/GameTheory/SocialChoice/WeakOrder.lean) for the existence of non-dictatorial weakly Pareto, IIA social welfare functions on infinite electorates via nonprincipal ultrafilters (`Filter.hyperfilter`).

<a id="fks84"></a>
## fks84

Michael L. Fredman, János Komlós, Endre Szemerédi.
"Storing a Sparse Table with O(1) Worst Case Access Time."
*Journal of the ACM* 31(3), 538–544, 1984. https://doi.org/10.1145/828.1884 . Bibliographic metadata was checked against the DOI record on 2026-11-08.
The full text was not inspected.
The formalization follows the textbook account in [clrs09](#clrs09), Section 11.5 ("Perfect hashing"), and that locator was checked against the edition's published table of contents only.
No theorem numbers are attributed to either source.

<a id="floyd62"></a>
## floyd62

Robert W. Floyd.
"Algorithm 97: Shortest Path."
*Communications of the ACM* 5(6), 345, 1962. https://doi.org/10.1145/367766.368168 . Bibliographic metadata checked on 2026-11-07; the manual attributes only the Floyd–Warshall recurrence to this note.

<a id="flumgrohe2006"></a>
## flumgrohe2006

Jörg Flum and Martin Grohe.
*Parameterized Complexity Theory*.
Springer, 2006.
[DOI](https://doi.org/10.1007/3-540-29953-X).
The [publisher's Chapter 3 preview](https://page-one.springer.com/pdf/preview/10.1007/3-540-29953-X_3) was inspected: Definition 3.1 on printed p. 45 defines `W[P]` by restricted nondeterministic multitape machines with computable time and nondeterminism bounds, and Proposition 3.2 on printed p. 46 states `FPT ⊆ W[P] ⊆ XP ∩ paraNP`.
The preview does not give a weighted-circuit characterization.
It is used in [parameterized complexity](machines-and-classes/parameterized-complexity.md) to contrast conventions; equivalence with the library's potentially ineffective reduction closure `WP` is not established.

<a id="fly22"></a>
## fly22

Zhiyuan Fan, Jiatu Li, and Tianqi Yang.
*The Exact Complexity of Pseudorandom Functions and the Black-Box Natural Proof Barrier for Bootstrapping Results in Computational Complexity*.
Electronic Colloquium on Computational Complexity (ECCC), Report TR21-125, Revision 1 (12 June 2022), https://eccc.weizmann.ac.il/report/2021/125/ ; conference version in *Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 962–975, https://doi.org/10.1145/3519935.3520010 . Inspected ECCC TR21-125 Revision 1 PDF directly: Section 4.1 (pp. 24–26), Section 4.2, Definitions 4.3–4.5 (pp. 26–27), Section 4.4, Definition 4.9 (p. 28), Section 7.1, Definition 7.1, Lemmas 7.2–7.4, and Theorem 7.5 (pp. 39–41), and Section 7.2 (pp. 41–42).

<a id="fmptw15"></a>
## fmptw15

Samuel Fiorini, Serge Massar, Sebastian Pokutta, Hans Raj Tiwary and Ronald de Wolf.
*Exponential Lower Bounds for Polytopes in Combinatorial Optimization*.
Journal of the ACM 62(2), 1–23, 2015. https://doi.org/10.1145/2716307 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC.
Locators checked against arXiv:1111.0837v4 (23 Dec 2013), https://arxiv.org/abs/1111.0837 , on 2026-11-08 UTC: definition (1) of an extended formulation (EF) and its size (Section 1), the slack matrix and extension complexity (Section 3), Lemma 2, Theorem 3 (the factorization theorem, `dim P ≥ 1`) and Theorem 4 (the rectangle covering bound, attributed to [yannakakis91](#yannakakis91)) in Section 3.1.
Checked against the same arXiv v4 text on 2026-11-11 UTC: Section 3.2 (Theorems 5 and 7, Lemma 6 on `COR(n)` and `CUT(n + 1)`), Section 3.3 (Lemmas 8 and 9, Theorem 10 on `STAB(G_n)`), and Section 3.4 (Lemma 11, Theorem 12 on `TSP(n)`).
The journal version's numbering was not checked.

<a id="fmr20"></a>
## fmr20

Benjamin Fuller, Xianrui Meng and Leonid Reyzin.
"Computational Fuzzy Extractors."
*Information and Computation* 275, article 104602, 2020. https://doi.org/10.1016/j.ic.2020.104602 ; full version IACR Cryptology ePrint Archive Report 2013/416 (revision of June 23, 2020), https://eprint.iacr.org/2013/416 ; conference version ASIACRYPT 2013, LNCS 8269, 174-193.
Locators in the library follow the ePrint revision: Definitions 2.1-2.4 and Lemma 2.5 (Section 2), Construction 4.1, Definition 4.5, Lemma 4.7 and Theorem 4.11 (Section 4).
Checked on 2026-11-14 against that revision (31 pages, SHA-256 `7ebe9884a2963304ae98329742652916a281d3eb1eb860fc411392bbb99d310d`; printed page numbers, which are also its PDF page numbers): Construction 4.1 (p. 11, prime `q`, the source reading as the LWE error); Definition 4.5 (p. 13, `dist-LWE_{n,m,q,χ}` with `χ` an arbitrary distribution on `Z_q^m`, prime `q = poly(n)`, concrete `(ε, s_sec)` security); Theorem 4.6 (p. 13, from Döttling and Müller-Quade) and Theorem 4.8 (p. 14, from Bai et al.), which derive it for uniform-interval errors from Gaussian LWE; Lemma 4.7 (p. 14, dimension `n - k`, any `χ`); Theorem 4.11 (p. 17, with `χ` the uniform source over `[-2^(b-1), 2^(b-1)]^m`); and Theorem 5.2 (p. 18, symbol-fixing sources).
Checked on 2026-11-15 against the same revision: Definition 2.2 (p. 6, computational fuzzy extractor, whose item 4 is security against the distinguishers `D_{s_sec}` of p. 5).
The page numbers of the Information and Computation version were not checked.

<a id="fnw78"></a>
## fnw78

Marshall L. Fisher, George L. Nemhauser, Laurence A. Wolsey.
“An Analysis of Approximations for Maximizing Submodular Set Functions—II.”
*Mathematical Programming Study* 8, 73–87, 1978. https://doi.org/10.1007/BFb0121195 . Bibliographic data from the DOI record; the paper is paywalled and its full text was not inspected.
The manual attributes to it only the greedy `1/2` (matroid) and `1/(p+1)` (intersection of `p` matroids) bounds, following [Călinescu et al.](#ccpv11), Section 1 and Appendix B.

<a id="fominkratsch10"></a>
## fominkratsch10

Fedor V. Fomin and Dieter Kratsch.
*Exact Exponential Algorithms*.
Texts in Theoretical Computer Science, An EATCS Series.
Springer, 2010. https://doi.org/10.1007/978-3-642-16533-7 . Bibliographic metadata checked on 2026-11-07.
Inspected the author-hosted manuscript dated October 12, 2010 (https://fedorvf.github.io/BookEA/BookEA.pdf): Section 4.1, Theorem 4.2 for the general inclusion–exclusion principle, and Section 4.2.2, Theorem 4.5 and Eq. (4.4), printed pp. 56–57 (PDF pp. 68–69), for the inclusion–exclusion Hamiltonian path algorithm (where the book fixes start and end vertices `s, t` and counts `(s, t)`-walks on `n + 2` vertices, adapted in [`HamiltonianCount.lean`](../CslibFrontier/Algorithms/Lean/TSP/HamiltonianCount.lean) as a pure specification counting all endpoint choices on `n` vertices and realized on a standard-basis word-RAM in `O((n³ + 1) · 2ⁿ)` instructions in [`WordRAM/HamiltonianCount.lean`](../CslibFrontier/Algorithms/WordRAM/HamiltonianCount.lean), rather than the book's unit-cost versus log-cost discussion).
The Section 1.2 locator for the Held–Karp TSP dynamic program was taken from secondary descriptions and issue #3013 without inspecting that section.
It is also cited at book level for search-tree branching vectors and disjoint clause-prefix branching on fixed-width SAT; no internal chapter, theorem, or page locators are claimed.

<a id="forbesshpilka2013"></a>
## forbesshpilka2013

Michael A. Forbes and Amir Shpilka.
"Quasipolynomial-time Identity Testing of Non-commutative and Read-once Oblivious Algebraic Branching Programs."
FOCS 2013, 243–252; arXiv:1209.2408v2, https://arxiv.org/abs/1209.2408v2 . Read in the arXiv version: §1.1 (pp. 2–3) for the set-multilinear and univariate encodings, and §4 for the reduction from non-commutative programs: Construction 4.1 and Lemma 4.2 (p. 22), Lemma 4.3 (p. 23), Lemma 4.5 and Theorem 4.6 (p. 24).
The library formalizes this reduction for homogeneous layered programs only and feeds it the hitting set of its own adaptation of Agrawal–Gurjar–Korwar–Saxena; Corollary 4.7 (p. 25), with the paper's generator and bound, is not formalized.

<a id="fortnowsanthanam2011"></a>
## fortnowsanthanam2011

Lance Fortnow and Rahul Santhanam.
"Infeasibility of Instance Compression and Succinct PCPs for NP."
*Journal of Computer and System Sciences* 77(1), 91–106, 2011. https://doi.org/10.1016/j.jcss.2010.06.007 . Bibliographic data from the DOI record.
The paper was not inspected in this pass; the manual cites the statement of its distillation theorem through [Bodlaender, Jansen and Kratsch](#bodlaenderjansenkratsch2014), Theorem 2.

<a id="franklwilson1981"></a>
## franklwilson1981

Peter Frankl and Richard M. Wilson.
“Intersection Theorems with Geometric Consequences.”
*Combinatorica* 1(4), 357–368, 1981. https://doi.org/10.1007/BF02579457 . Bibliographic metadata as already recorded in the library bibliography; it was not re-checked against the publisher record, and the full text was not inspected in this pass.
The manual attributes to this paper the modular intersection theorem and the explicit Ramsey graph on the `(p² - 1)`-subsets of a `p³`-set.
The formal modular statement is the restricted form given by the triangular polynomial argument (`|L| ≤ d mod p`); the paper's own hypotheses (reportedly `|L| ≤ d` in the uniform case) were not checked.

<a id="freivalds79"></a>
## freivalds79

Rūsiņš Freivalds.
"Fast Probabilistic Algorithms."
*Mathematical Foundations of Computer Science 1979*, Lecture Notes in Computer Science 74, 57–69. https://doi.org/10.1007/3-540-09526-8_5 . Bibliographic data from the DOI record, checked 2026-11-07; the full text was not inspected.
The manual attributes only the random-vector matrix-product check to this paper.

<a id="friedmanresnick01"></a>
## friedmanresnick01

Eric J. Friedman and Paul Resnick.
"The Social Cost of Cheap Pseudonyms."
*Journal of Economics & Management Strategy* 10(2), 173–199, 2001 (bibliography key `FriedmanResnick2001`). https://doi.org/10.1111/j.1430-9134.2001.00173.x . Bibliographic metadata from the DOI record and [friedmanresnicksami07](#friedmanresnicksami07); the 2001 journal PDF was not directly inspected, so [RepeatedPD.lean](../CslibFrontier/GameTheory/Reputation/RepeatedPD.lean) cites it at paper level as the origin of the cheap-pseudonym whitewashing and Pay-Your-Dues (`PYD`) model presented in [friedmanresnicksami07](#friedmanresnicksami07), §27.3 (pp. 682–683) and Exercise 27.4 (p. 697).

<a id="friedmanresnicksami07"></a>
## friedmanresnicksami07

Eric Friedman, Paul Resnick and Rahul Sami.
"Manipulation-Resistant Reputation Systems."
Chapter 27 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 677–698 (bibliography key `FriedmanResnickSami2007`). https://doi.org/10.1017/CBO9780511800481.029 . Checked against the 2007 Cambridge University Press book text (printed pp. 677–697) on 2026-11-24: §27.2 (pp. 680–682: infinitely repeated Prisoner's Dilemma with stage payoffs `(1, 2, 0, -1)`, normalized discounted payoff, Grim trigger `δ ≥ 1/2`, Reputational-Grim, and Personalized-Grim, noting on p. 681 that uniform random pairing among `N` potential opponents yields threshold `δ ≥ N / (N + 1)` rather than `1 - 1 / (2N)`), §27.3 (pp. 682–683: whitewashing entry-fee deterrence `f ≥ 1 / δ`, Pay-Your-Dues `PYD`, and newcomer welfare loss), §27.4 (pp. 684–688: simultaneous peer-rating game Eq. `(27.1)`, logarithmic peer-prediction transfer Eq. `(27.2)`, Proposition 1 on p. 687, and uninformative constant equilibria in Footnote 2 on p. 688), §27.5 (pp. 689–693: transitive trust graphs, monotonicity, symmetry, rank-strategyproofness in §27.5.1, Definitions 27.2–27.4 and 27.6, Theorems 27.5 and 27.7–27.9, and Figure 27.2 on p. 692), and Exercises 27.1–27.6 and 27.8 (pp. 696–697, noting in Exercise 27.2 that under `(1, 2, 0, -1)` stage payoffs `(TFT, TFT)` is an SPNE at the unique knife-edge discount factor `δ = 1 / 2` and fails for every `δ ≠ 1 / 2`).
Also checked against the 2007 Cambridge University Press book text (printed pp. 677–698) for §27.4.2 (pp. 686–687: Definition 27.1 of strictly proper scoring rules on p. 686, and the quadratic and logarithmic scoring rules) and Exercise 27.7 (p. 697: strict propriety and range bounds of `a + b * quadraticScore`; the book states the 2-event affine form without writing `b > 0`, which [ScoringRules.lean](../CslibFrontier/GameTheory/PredictionMarket/ScoringRules.lean) formalizes over arbitrary finite `Ω` with `[-1, 1]` bounds on `quadraticScore` and positive rescaling `0 < b` in `ScoringRule.IsStrictlyProperOn.affine`, while restricting real-valued `logScore` to `openProbSimplex Ω` or `supp(q) ⊆ supp(p)` because `Real.log 0 = 0`).

<a id="friezekaronski2016"></a>
## friezekaronski2016

Alan Frieze and Michał Karoński.
*Introduction to Random Graphs*.
Cambridge University Press, 2016. https://doi.org/10.1017/CBO9781316339831 . Inspected the author-hosted version dated August 7, 2026 (https://www.math.cmu.edu/~af1p/BOOK.pdf), §4.1, Theorem 4.1 and its proof; §1.2, Lemma 1.11 (sharp threshold for isolated vertices, stated and proved in `G(n, m)` with `m = n (log n + ω) / 2` by the first and second moment methods); and §3.1, `E X_0 = n (1 - p) ^ (n - 1)` in `G(n, p)` with its limits (3.1).
The theorem is stated for `G_m` with `m = n (log n + c_n) / 2`; the proof works in `G(n, p)` with `p = (log n + c) / n`, and the text later cites it for "`G(n, p)` is connected w.h.p. for `np − log n → ∞`".
The book attributes the theorem to Erdős and Rényi, "On random graphs I", *Publ.
Math.
Debrecen* 6 (1959), 290–297; that paper was not inspected.
Also inspected Lemma 33.10 (pp. 696–697, truncated inclusion-exclusion/Bonferroni bounds) and Theorem 33.11 (pp. 697–698, Brun's sieve).
The source's `B_r` (written `B_k = E[choose(S_n, k)]`) is formalized as the sum of `r`-fold intersection measures with limit `lam^r / r!` (binomial-moment normalization).
The formalization deliberately extends the result to finite measures by using the `r = 0` hypothesis to require that the total mass converges to 1.
The publisher's ISBN and DOI are from catalogue records.

<a id="fulkerson1956"></a>
## fulkerson1956

D. R. Fulkerson.
"Note on Dilworth's Decomposition Theorem for Partially Ordered Sets."
*Proceedings of the American Mathematical Society* 7(4), 701–702, 1956. https://doi.org/10.1090/S0002-9939-1956-0078334-6 . Bibliographic metadata from search summaries, checked on 2026-11-08.
The publisher PDF returned HTTP 403 and was not inspected.
The Dilworth module credits this note with the reduction of Dilworth's theorem to König's theorem through the bipartite graph of the strict order, following the customary attribution; the paper's own formulation is unverified.

<a id="gallagerhumbletspira1983"></a>
## gallagerhumbletspira1983

R. G. Gallager, P. A. Humblet, and P. M. Spira.
"A Distributed Algorithm for Minimum-Weight Spanning Trees."
*ACM Transactions on Programming Languages and Systems* 5(1), 66–77, January 1983. https://doi.org/10.1145/357195.357200 . Inspected the typeset ACM TOPLAS PDF (`https://users.ece.utexas.edu/~garg/resources/p66-gallager.pdf`, SHA-256 `fe9ff9f38e79e3e52c7022f6a77b9aaee3d76801ebbc010bc77d7f147c739a6b`) on 2026-11-22: Section 1 (pp. 66–68, connected undirected network of `N` nodes and `E` edges with distinct finite edge weights, asynchronous error-free FIFO links, spontaneous awakening of any nonempty subset of nodes, and worst-case `5 N log_2 N + 2 E` message bound); Section 2 (pp. 68–69, Property 1 cut extension for minimum-weight outgoing edges of MST fragments on p. 68, Property 2 uniqueness of the minimum-weight spanning tree under distinct edge weights on p. 68, and fragment levels with absorption `L < L'` and mutual-MOE merge `L = L' -> L + 1`); Section 3 (pp. 69–73, `Sleeping`/`Find`/`Found` node states, `Branch`/`Rejected`/`Basic` edge states, `Test`/`Accept`/`Reject` with simultaneous dual-`Test` rejection and level-delay `L > LN`, `Report(W)`, `Change-core` / `Change-root`, `Connect(L)`, `Initiate(L, F, S)`, fragment size `>= 2^L` and level bound `<= log_2 N` on p. 72, and deadlock-freedom via the minimum-level fragment with smallest MOE on pp. 72–73); Section 4 (p. 73, communication cost analysis yielding at most `2 E` rejection messages and `5 N log_2 N + 2 E` total messages); Section 5 (pp. 73–74, `5 N log_2 N` timing analysis under synchronous general awakening on p. 74); and the Appendix (pp. 74–77, local node/edge variables and per-node asynchronous event rules (1)–(12) on pp. 75–77).
Scope note: `Foundations.Combinatorics.SimpleGraph.MinimumSpanningTree` formalizes Section 2 Properties 1 and 2 unconditionally on Mathlib's `SimpleGraph V` (`SimpleGraph.IsMST.exists_sup_edge_of_isMOE`, `SimpleGraph.IsMOE.mem_edgeSet_of_isMST_of_injOn`, `SimpleGraph.IsMST.eq_of_injOn`, `SimpleGraph.existsUnique_isMST_of_injOn`, bridged to sequential Kruskal in `Algorithms.Lean.Kruskal.SimpleGraph.kruskalGraph_isMST`).
`Computability.Distributed.MinimumSpanningTree.GHS` formalizes an event-driven fragment-phase execution and seven-type message-accounting model (`fragLTS`, `FragReachable`) as a milestone step toward `#7508`, proving MST-subtree and per-fragment tree invariants, internal-chord rejection, fragment size `2^L` and `Nat.log 2 (Fintype.card V)` level bounds, minimum-level smallest-MOE deadlock-freedom, termination at the exact unique MST in `Fintype.card V - 1` combine steps, and `s.msgs.total <= 5 * Fintype.card V * Nat.log 2 (Fintype.card V) + 2 * G.edgeFinset.card`; refining the Appendix per-node FIFO message-queue automaton onto `fragLTS`, the nondistinct-weight tie-breaking modification (§3, p. 73), and the `5 N log_2 N` synchronous-awakening time bound (§5, pp. 73–74) remains open in `#7508`.

<a id="gaspers26"></a>
## gaspers26

Serge Gaspers.
*Path Decompositions of Sparse Graphs via Gaussian Sweeps and Faster Exponential Algorithms*. arXiv:2611.05146v1 (November 2026), https://arxiv.org/abs/2611.05146 ; MIT-licensed Lean 4 companion archived at Zenodo release v1, https://doi.org/10.5281/zenodo.23883489 . Checked directly against the arXiv LaTeX source (`main.tex`), compiled PDF, and Zenodo release archive on 2026-11-22.
Relevant numbered statements in arXiv:2611.05146v1: Theorem 1.1(a) (bounded degree, §1.1, p. 1 / PDF p. 3: `pw(G) ≤ c₃ n + o(n)` for `Δ(G) ≤ 3`, proved as Theorem 8.1 in §8, p. 45 / PDF p. 47) and Corollary 1.2 (bisection width and cutwidth, §1.1, p. 1 / PDF p. 3: `bw(G) ≤ cw(G) ≤ c₃ n + o(n)`), where `c₃ = (3 / (4π)) arccos(5 / 6) ≈ 0.139822`.
Scope note: this library adapts the certificate-free `CubicPathwidth.C3` geometry, bipartite connector lemma, and switched interval-bag decomposition into `CslibFrontier/Computability/Circuit/Frontier/Layouts/Switched/` and formalizes existential (non-constructive) edge-cut and bisection bounds on finite loopless 3-regular multigraphs (`exists_width_le_switchedCoefficient`, `exists_ncard_edgeCut_le`, parallel edges allowed) plus the cycle-rank bound `LayoutBound 3 (2 * c₃)` for subcubic multigraphs (`layoutBound_switched`); the paper's `n^{2+o(1)}` deterministic algorithms (Theorem 1.5, p. 4 / PDF p. 6; Corollary 10.2, §10, p. 71 / PDF p. 73) and mixed-degree / `Δ ≤ 4, 5` / exact exponential algorithm results are not formalized here.
The numerical coefficient bounds in `Coefficient.lean`, the direct cubic-multigraph interval-to-cutwidth bridge `exists_width_le_of_intervals`, the concentration proof via `unitKernelRow`, and all downstream frontier lower-bound instantiations (`FanInTwo`, `Nondeterministic`, `Ledger/Unconditional`, `Correlation`, `Linear/Unconditional`) are original to this library.

<a id="gentry09"></a>
## gentry09

Craig Gentry.
“Fully Homomorphic Encryption Using Ideal Lattices.”
*STOC 2009*, 169–178. https://doi.org/10.1145/1536414.1536440 . Bibliographic data and theorem locator taken from the pinned repository; full text not independently re-audited here.

<a id="gentrypeikertvaikuntanathan2008"></a>
## gentrypeikertvaikuntanathan2008

Craig Gentry, Chris Peikert, and Vinod Vaikuntanathan.
"Trapdoors for Hard Lattices and New Cryptographic Constructions."
*Proceedings of the 40th Annual ACM Symposium on Theory of Computing (STOC 2008)*, 197–206, 2008. https://doi.org/10.1145/1374376.1374407 . Full version (*How to Use a Short Basis: Trapdoors for Hard Lattices and New Cryptographic Constructions*, dated August 25, 2008, `https://eprint.iacr.org/2007/432`, SHA-256 `7e747881cddd16b7dcf82893682cb9b4c788d7cec5712f80aa4193f2bd30a5b3`) inspected on 2026-11-21: Section 4.1, Lemma 4.2 (1-D discrete Gaussian tail bound, printed p. 14) and Lemma 4.3 (`SampleZ` rejection sampler over `ℤ ∩ [c − s · t(n), c + s · t(n)]`, printed p. 15, including the capped-iteration remark at the end of its proof).
In `Computability.Probabilistic.DiscreteGaussian1D`, `Cslib.Probability.sampleZ` implements the capped-trial strict-PPT variant over the padded integer proposal interval `[⌊c⌋ - R, ⌊c⌋ + R]` about `⌊c⌋` (`R = ⌊√⌊t² · s²⌋⌋ + 2`, containing the paper's window `ℤ ∩ [c − s · t, c + s · t]`) with explicit unary trial cap `maxTrials` and finite dyadic acceptance precision `prec`, proved in both dual-mass (`ρ_{1/s}(ℤ* \ {0}) ≤ ε ≤ 1/2`) and smoothing-parameter (`η_ε(ℤ) ≤ s`) forms.

<a id="gglrs00"></a>
## gglrs00

Oded Goldreich, Shafi Goldwasser, Eric Lehman, Dana Ron and Alex Samorodnitsky.
*Testing Monotonicity*.
Combinatorica 20(3), 301–337, 2000. https://doi.org/10.1007/s004930070011 . Bibliographic metadata checked against the Crossref record on 2026-11-08.
The journal version is paywalled, and the author-hosted pages could not be reached (connection reset), so the text was not inspected and no theorem locator is claimed.
The manual attributes the edge tester for Boolean functions on the hypercube to this paper, as [roughgarden15cc](#roughgarden15cc) does.

<a id="ggm86"></a>
## ggm86

Oded Goldreich, Shafi Goldwasser, Silvio Micali.
“How to Construct Random Functions.”
*Journal of the ACM* 33(4), 792–807, 1986.
Author-hosted version of record: https://www.wisdom.weizmann.ac.il/~oded/X/ggm-jacm.pdf . Adaptive function-test definition consulted.

<a id="gibbard73"></a>
## gibbard73

Allan Gibbard.
"Manipulation of Voting Schemes: A General Result."
*Econometrica* 41(4), 587–601, 1973. https://doi.org/10.2307/1914083 . Bibliographic data from secondary search summaries on 2026-11-08 UTC; the paper was not inspected.
[Nisan, *Introduction to Mechanism Design*](#nisan07), p. 239, credits the theorem to Gibbard (1973) and Satterthwaite (1975); Nisan's own statement (Theorem 9.8) is the form for rules onto at least three alternatives.
The range form (at least three possible outcomes), formalized as the main theorem, is the standard statement in secondary accounts and was not checked against the original; no theorem number is claimed.

<a id="gilbertpollak68"></a>
## gilbertpollak68

E. N. Gilbert and H. O. Pollak.
*Steiner Minimal Trees*.
SIAM Journal on Applied Mathematics 16(1), 1–29, 1968. https://doi.org/10.1137/0116001 . Cited only because the Chapter 12 Notes of [Williamson and Shmoys](#williamsonshmoys11) attribute the MST factor-2 heuristic for Steiner tree to Moore, as described in this paper.
The paper itself was not checked.

<a id="gkr15"></a>
## gkr15

Shafi Goldwasser, Yael Tauman Kalai and Guy N. Rothblum.
*Delegating Computation: Interactive Proofs for Muggles*.
JACM 62(4), article 27, 2015. https://doi.org/10.1145/2699436 .

<a id="gkst06"></a>
## gkst06

Oded Goldreich, Howard Karloff, Leonard J. Schulman and Luca Trevisan.
"Lower Bounds for Linear Locally Decodable Codes and Private Information Retrieval."
*Computational Complexity* 15(3), 263–296, 2006. https://doi.org/10.1007/s00037-006-0216-3 ; full preliminary version: Electronic Colloquium on Computational Complexity (ECCC), Report TR01-080, 2001, https://eccc.weizmann.ac.il/report/2001/080/ . Checked on 2026-11-12 against the ECCC TR01-080 report PDF (Section 1.2 Definition 1.7 on p. 4, Section 2.1 Definition 2.1 on p. 6, Section 5.1 Lemma 5.1 on pp. 14–15, and Section 7.1 Lemma 7.1 on pp. 19–20); journal volume, issue, pages and DOI verified against bibliographic metadata.

<a id="gkwy20"></a>
## gkwy20

Chun Guo, Jonathan Katz, Xiao Wang and Yu Yu.
"Efficient and Secure Multiparty Computation from Fixed-Key Block Ciphers."
*2020 IEEE Symposium on Security and Privacy (SP 2020)*, 825–841, 2020. https://doi.org/10.1109/SP40000.2020.00016 ; full version: Cryptology ePrint Archive, Report 2019/074, https://eprint.iacr.org/2019/074 . Checked on 2026-11-15 against the ePrint PDF dated January 21, 2019 (30 pages, SHA-256 `dc4ff4859fa884d529c176c13a583433c21d95036e7a563067596d5f05e96292`); locators use its printed page numbers, which are also its PDF page numbers; this is the author's check, which no reviewer has yet repeated at the source, so the library cites these locators as not verified.
§3, p. 7: the definitions are concrete, asymptotic versions follow "by suitable modifications", and the key law may be non-uniform, as in half gates, where the least significant bit of `R` is `1`.
Pp. 7–8: Definitions 1 and 2, correlation robustness and circular correlation robustness.
P. 8: the remark that the definitions let tweaks repeat and that weaker notions, such as non-repeating tweaks, may suffice; Definition 3, tweakable (circular) correlation robustness, with `O(x, i, b) = H(x ⊕ R, i) ⊕ b·R`, distinguishers that never ask both `(x, i, 0)` and `(x, i, 1)`, and `(t, q, ρ, ε)` bounds for every key law of min-entropy at least `ρ`; and the relations between the definitions.

<a id="gm94"></a>
## gm94

Torbjörn Granlund, Peter L. Montgomery.
"Division by Invariant Integers using Multiplication."
*Proceedings of the ACM SIGPLAN 1994 Conference on Programming Language Design and Implementation (PLDI 1994)*, 61–72, 1994. https://doi.org/10.1145/178243.178249 . Checked on 2026-11-10 against the copy at https://gmplib.org/~tege/divcnst-pldi94.pdf : Section 4, Theorem 4.2 (multiply-and-shift division by an invariant integer, base 2, word size `N`, with a non-strict bound on the multiplier).
The formalized identity is a radix-`p` variant with a strict bound, in the form of [ll24](#ll24) Lemma 5; the bound `m ≤ p ^ (k + 1)` on the chosen multiplier is proved in the Lean source.

<a id="gneitingraftery07"></a>
## gneitingraftery07

Tilmann Gneiting and Adrian E. Raftery.
"Strictly Proper Scoring Rules, Prediction, and Estimation."
*Journal of the American Statistical Association* 102(477), 359–378, 2007 (bibliography key `GneitingRaftery2007`). https://doi.org/10.1198/016214506000001437 . Bibliographic metadata checked via DOI and catalogue records; the journal full text was not directly inspected, so internal theorem, section and page locators are marked `unverified` in the results registry.
Cited at paper level in [ScoringRules.lean](../CslibFrontier/GameTheory/PredictionMarket/ScoringRules.lean) for the convex-potential / Bregman-divergence characterization of proper and strictly proper scoring rules on convex subsets of the simplex (where real-valued finiteness on `P` discharges regularity) and for the spherical scoring rule (`sphericalScore`).

<a id="gochtmccreeshmyreennordstromoerteltan2024"></a>
## gochtmccreeshmyreennordstromoerteltan2024

Stephan Gocht, Ciaran McCreesh, Magnus O. Myreen, Jakob Nordström, Andy Oertel and Yong Kiam Tan.
"End-to-End Verification for Subgraph Solving."
*Proceedings of the 38th AAAI Conference on Artificial Intelligence (AAAI 2024)*, 8038–8047, 2024. https://doi.org/10.1609/aaai.v38i8.28642 ; author-hosted copy https://cakeml.org/aaai24-verified-subgraphs.pdf . Checked against that copy (SHA-256 `3d8ca0a1c0cfd004ba08752e433bca33da5d8a1def9fd6d416492b93667169da`) on 2026-11-23 UTC: Figure 2 (HOL definitions of cliques, maximum clique size and subgraph isomorphism, p. 8039), §3.2 (verified graph problem encoders, with footnote 1 on the `good_graph` check, p. 8041), §3.3 and Figure 5 (end-to-end correctness of the maximum clique checker, pp. 8042–8043).
The paper states its encoders' theorems in prose; the statements formalized are those of the CakeML sources at commit [`14856fcf`](https://github.com/CakeML/cakeml/tree/14856fcfddeb3fdafdf8a1080e567a55d3102698): `encode_correct`, `conv_concl_def`, `full_encode_sem_concl` and `full_encode_sem_concl_check` in `examples/pseudo_bool/graph_encoding/cliqueScript.sml`, `has_subgraph_iso_def`, `encode_def`, `encode_correct`, `full_encode_correct` and `full_encode_sem_concl` in `examples/pseudo_bool/graph_encoding/subgraph_isoScript.sml`, `parse_dimacs`, `parse_lad` and `check_good_graph` in `graph_basicScript.sml`, `clique_sem_def` in `examples/pseudo_bool/array/cliqueProgScript.sml`, and `check_unsat_3_sem_def` in `examples/pseudo_bool/array/subgraph_isoProgScript.sml`.
[Graph/Clique.lean](../CslibFrontier/Logics/Propositional/PseudoBoolean/Graph/Clique.lean) proves the pure functional statement `clique_sem`, not Figure 5 itself: Figure 5 (`main_semantics`) is a theorem about CakeML's compiled x64 code, its file and command-line I/O and its output, none of which the library models.
[Graph/Dimacs.lean](../CslibFrontier/Logics/Propositional/PseudoBoolean/Graph/Dimacs.lean) reads DIMACS graphs as `parse_dimacs` does, except that it also accepts blank lines, comment lines whose first word starts with `c`, and digit separators.
The maximal clique encoding (`mencode_correct`) is not formalized.
[Graph/SubgraphIso.lean](../CslibFrontier/Logics/Propositional/PseudoBoolean/Graph/SubgraphIso.lean) proves `encode_correct` for subgraph isomorphism, with `has_subgraph_iso` as Mathlib's `SimpleGraph.IsContained` (a non-induced copy, not the induced embedding `↪g`), and the pure functional statement `check_unsat_3_sem` of `cake_pb_iso`, not its `main_semantics`, which is again about compiled code and I/O; §3.3 of the paper discusses only the clique checker's theorem.
Its graphs `SimpleGraph (Fin n)` are the loop-free part of CakePB's `good_graph` model.
CakePB writes the per-pattern at-most-one constraints (`has_mapping_am1`) with `≤`, and they are written here in the `≥` form CakePB normalizes them to; the per-target constraints (`one_one`) are already `≥` constraints over negated literals in CakePB.
An at-most-one constraint (`has_mapping_am1` or `one_one`) with no literal (for an empty target or pattern) has degree `0` here and `-1` in CakePB, both trivial; the at-least-one constraint `has_mapping_al1` of a pattern vertex is `0 ≥ 1` for an empty target, of degree `1` in both ([CakePB definitions](https://github.com/CakeML/cakeml/blob/14856fcfddeb3fdafdf8a1080e567a55d3102698/examples/pseudo_bool/graph_encoding/subgraph_isoScript.sml#L18-L35)).
The encoding is printed with CakePB's variable names `xa_u` (`enc_string_def`) and in CakePB's constraint order, so kernel proofs for `cake_pb_iso`'s encoding, such as the Glasgow Subgraph Solver's elaborated by VeriPB, are read unchanged, with no renaming.
No theorem relates the Lean checker to CakePB's; acceptance of the same proofs by `cake_pb_iso` was checked only on the test fixtures: the five written by hand, two of which have such empty at-most-one rows, the empty-target fixture's `UNSAT` proof using the empty at-least-one row; and two proofs of the Glasgow Subgraph Solver.
[Graph/Lad.lean](../CslibFrontier/Logics/Propositional/PseudoBoolean/Graph/Lad.lean) accepts the LAD texts `parse_lad` and `check_good_graph` accept, except that it rejects loops, which CakePB accepts and a simple graph cannot have; on an accepted text it gives the same adjacency relation as CakePB, but it keeps the neighbour lists as written, a repeated neighbour included, where CakePB stores sets (`list_to_num_set`).
Registered in [VeriPBClique](../CslibFrontierResults/Entries/VeriPBClique.lean), with the outside-fleet source check of [PR #7675](https://github.com/cslib-community/cslib-frontier/pull/7675#pullrequestreview-6015059703), and in [VeriPBSubgraphIso](../CslibFrontierResults/Entries/VeriPBSubgraphIso.lean), with the outside-fleet source check of [PR #7944](https://github.com/cslib-community/cslib-frontier/pull/7944#pullrequestreview-6024571013) and the outside-fleet delta source check of [PR #8361](https://github.com/cslib-community/cslib-frontier/pull/8361#issuecomment-7141434117) for the names `xa_u` and the reading of `ia`.

<a id="goemansmirroknivetta05"></a>
## goemansmirroknivetta05

Michel X. Goemans, Vahab S. Mirrokni and Adrian Vetta.
"Sink Equilibria and Convergence."
*46th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2005)*, 142–154, IEEE, 2005 (bibliography key `GoemansMirrokniVetta2005`). https://doi.org/10.1109/SFCS.2005.68 . Bibliographic metadata from `references.bib` and the Chapter 19 bibliography of [Tardos and Wexler](#tardoswexler07) (p. 512); the full text was not inspected firsthand, so no internal section or theorem locator in this paper is claimed (`unverified` in [Entries/UtilityGame.lean](../CslibFrontierResults/Entries/UtilityGame.lean)).
Cited via [Tardos and Wexler](#tardoswexler07), §19.4.5 and §19.5.3 (pp. 506, 511), for transient social-welfare bounds under random best-response moves in monotone basic utility games ([UtilityGame/Basic.lean](../CslibFrontier/GameTheory/UtilityGame/Basic.lean)).

<a id="goemanswilliamson95"></a>
## goemanswilliamson95

Michel X. Goemans and David P. Williamson.
"Improved Approximation Algorithms for Maximum Cut and Satisfiability Problems Using Semidefinite Programming."
*Journal of the ACM* 42(6), 1115–1145, 1995. https://doi.org/10.1145/227683.227684 . Section 2 (the relaxation (P) and random-hyperplane rounding) and Section 3 (Theorem 3.1, Lemma 3.2, Theorem 3.3, Lemma 3.4, and Lemma 3.5 with its tangent-line proof at `θ = 2.331122`) were checked against the author-hosted copy at https://math.mit.edu/~goemans/PAPERS/maxcut-jacm.pdf on 2026-11-08.
Section 7.2.1 (relaxations `(Q')`, `(P')`, and Theorem 7.2.1.1 for MAX 2-SAT) and Section 7.3 (relaxations `(Q'')`, `(P'')`, Lemmas 7.3.1–7.3.2, the `β > 0.79607` MAX DICUT bound, the balanced-digraph `α` bound on p. 1138, and the sign typo in display `(Q'')`) were checked against the same copy on 2026-11-11.

<a id="goldbergplotkinshannon1988"></a>
## goldbergplotkinshannon1988

Andrew V. Goldberg, Serge A. Plotkin and Gregory E. Shannon.
"Parallel Symmetry-Breaking in Sparse Graphs."
*SIAM Journal on Discrete Mathematics* 1(4), 434–446, 1988. https://doi.org/10.1137/0401044 . Bibliographic metadata checked via DOI record on 2026-11-22 UTC; the paywalled journal PDF was not directly inspected, so internal theorem and page locators are not claimed.
Credited as background for decomposing bounded-degree graph coloring into `Δ` out-degree-`1` orientations followed by iterative greedy color merging in [LocalGraph/Coloring.lean](../CslibFrontier/Computability/Distributed/LocalGraph/Coloring.lean) (`deltaPlusOneColoring`, `1 + log* C + 5 Δ (Δ + 1)` rounds, step toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505)).

<a id="goldbergtarjan88"></a>
## goldbergtarjan88

Andrew V. Goldberg and Robert E. Tarjan.
"A New Approach to the Maximum-Flow Problem."
*Journal of the ACM* 35(4), 921–940, 1988. https://doi.org/10.1145/48014.61051 . The bibliographic data come from search summaries of the publisher record (2026-11-08).
The paper was not inspected, so no theorem number is cited.
The manual credits it with the preflow push–relabel method and its `O(|V|² |E|)` generic bound, as these are standardly described.
The formalization follows [clrs09](#clrs09), Section 26.4.

<a id="goldreich-tree24"></a>
## goldreich-tree24

Oded Goldreich.
*On the Cook–Mertz Tree Evaluation procedure*.
ECCC TR24-109, revision 2 (27 December 2024). https://eccc.weizmann.ac.il/report/2024/109/ .

<a id="goldreich04"></a>
## goldreich04

Oded Goldreich.
*Foundations of Cryptography, Volume 2: Basic Applications*.
Cambridge University Press, 2004. https://doi.org/10.1017/CBO9780511721656 . Author's chapter listing and draft availability: https://www.wisdom.weizmann.ac.il/~oded/foc-vol2.html . Author page checked; the full published chapter was not independently audited here.

<a id="goldreich98frag"></a>
## goldreich98frag

Oded Goldreich.
*Foundations of Cryptography (Fragments of a Book – Version 2.03)*.
Working draft dated February 27, 1998 (bibliography key `Goldreich1998Fragments`).
The author's page https://www.wisdom.weizmann.ac.il/~oded/foc-drafts.html posts it as early drafts of Chapters 1–4 of *Foundations of Cryptography, Volume 1* (Cambridge University Press, 2001), in the files https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part1N.pdf (title page, preface and Chapter 1; SHA-256 `8bb9b1749e92a76af10ded00ef440de04bfcd5de128e68022205c8e84037b3d7`), `part2N.pdf` (Chapter 2; `e0c0a64cc14321effaccbcb26e845254f08d8dc14b2358529687430a869aa45d`), `part3N.pdf` (Chapter 3; `773f69ff14873f66bbe241179dcf5c90c2389c81cd8a3b1b8f8f6aad365e46c3`) and `part4N.pdf` (Chapter 4; `97e67c3cae68701705839386a31f462803c6c9e6d1984638442010df99b6f977`).
Printed page numbers run continuously across the four files.
Read on 2026-11-15: Definitions 2.2.1 (strong one-way functions, p. 29), 2.2.6 (non-uniformly one-way functions, with the remark that follows it, p. 36) and 2.5.1 (hard-core predicates, p. 54); Definitions 3.2.2 (polynomial-time indistinguishability, p. 78) and 3.3.2 (pseudorandom generators, p. 85), the description of one-way permutations as length-preserving one-to-one one-way functions in Section 3.4.1 (p. 91), and the definition of indistinguishability by polynomial-size circuits in Exercise 8 of Chapter 3 (p. 121); Definition 4.2.6 (generalized interactive proofs with a soundness bound, p. 136), the remark that probabilistic polynomial time means a strict bound on the running time (p. 145), and Definition 4.3.8 (auxiliary-input zero knowledge, with the discussion of its clocks that follows it, pp. 151–152).
The published volume was not inspected, so its numbering is not claimed to match the draft's.

<a id="gomoryhu61"></a>
## gomoryhu61

Ralph E. Gomory and T. C. Hu.
“Multi-Terminal Network Flows.”
*Journal of the Society for Industrial and Applied Mathematics* 9(4), 551–570, 1961. https://doi.org/10.1137/0109047 . Bibliographic metadata checked through the publisher record; the article body was not inspected in this pass.
The manual cites it for cut-equivalent (Gomory–Hu) trees and the triangle inequality for minimum cut values, as described in [Schrijver 2003](#schrijver03), Section 15.4.
The review of PR #4586 reports the triangle inequality on pp. 551–552, the observation that there are at most `n - 1` distinct minimum cut values on p. 553 and the tree-path lemma (Lemma 2) on p. 556; these locators were not rechecked here.

<a id="goosetal22"></a>
## goosetal22

Mika Göös, Alexandros Hollender, Siddhartha Jain, Gilbert Maystre, William Pires, Robert Robere and Ran Tao.
"Further Collapses in TFNP."
*37th Computational Complexity Conference (CCC 2022)*, LIPIcs 234, 33:1–33:15, 2022. https://doi.org/10.4230/LIPIcs.CCC.2022.33 . Checked on 2026-11-10 against the arXiv TeX source of `arXiv:2202.07761v2` (https://arxiv.org/abs/2202.07761 , dated 20 May 2022): Section 1, Theorem 1 (`EOPL = PLS ∩ PPAD`) and Theorem 2 (`SOPL = PLS ∩ PPADS`); Section 2, Lemma 1 (`inj-PHP` and `bij-PHP` as `PPADS`- and `PPAD`-complete formulations); Section 3, Lemma 2 (the path-pigeonhole reduction `inj-PHP ≤ Path-inj-PHP_f`); Section 4, Lemma 3 (`SoD ∧ inj-PHP ≤ SoPL`); and Section 5, Lemma 4 (`SoPL ∧ bij-PHP ≤ EoPL`).
`CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/PotentialLineCollapse.lean` implements Lemma 4 directly from `SOPL` and `PPAD` (`SOPL_inter_PPAD_subset_EOPL`, `EOPL_eq_SOPL_inter_PPAD`).
`CslibFrontier/Computability/Complexity/Classes/TFNP/Subclasses/SOPLCollapse.lean` implements Lemmas 1–3 directly on `PLS` and `PPADS` families over width `n₁(a) + 2(n₁(a) + n₂(a))` (`plsPpads_sink`, `mem_SOPL_of_localOpt_sinkOfLine`, `PLS_inter_PPADS_subset_SOPL`) and deduces Theorem 2 (`SOPL_eq_PLS_inter_PPADS`) and Theorem 1 (`EOPL_eq_PLS_inter_PPAD`).
`UEOPL` and the query-model results of the paper are not formalized.

<a id="gray1978"></a>
## gray1978

Jim Gray.
"Notes on Data Base Operating Systems."
In *Operating Systems: An Advanced Course*, edited by R. Bayer, R. M. Graham and G. Seegmüller, Lecture Notes in Computer Science 60, 393–481, Springer, 1978. https://doi.org/10.1007/3-540-08755-9_9 . Checked on 2026-11-22 against the author-hosted scan of the published LNCS 60 chapter, https://jimgray.azurewebsites.net/papers/dbos.pdf (SHA-256 `3aec1194772e5f5de19bf8fb4fe9c6aa431c0fd6523057b65f827e2aee776b0d`, printed pp. 393–481): Section 5.8.3.3 ("Two Phase Commit Protocol", pp. 465–470), including Section 5.8.3.3.1 ("Generals Paradox", pp. 465–466) and Section 5.8.3.3.2 ("Two Phase Commit Protocol", pp. 466–469; message scenarios 1–3 on p. 467; coordinator and cohort pseudocode on p. 468; restart and coordinator-crash blocking discussion on p. 469).
`CslibFrontier/Computability/Distributed/AtomicCommit/TwoPhaseCommit.lean` formalizes an intermediate fail-stop register-state step toward Section 5.8.3.3.2 (`twoPCStep?`, `twoPCLts`, abstracting stable undo/redo log forces into persistent per-site `TwoPCLocalState` registers across permanent fail-stop crashes rather than crash-recovery log-replay restarts; #7289), proving fail-stop decision stability, agreement, and abort validity (`twoPC_decision_stable_failStop`, `twoPC_agreement_failStop`, `twoPC_abort_of_vote_no_failStop`), fault-free commit and abort completion (`twoPC_failureFree_commit_failStop`, `twoPC_failureFree_abort_failStop`), and coordinator-crash uncertainty / survivor blocking (`twoPC_uncertain_bivalent_failStop`, `twoPC_no_safe_survivor_termination_failStop`).

<a id="grenet11"></a>
## grenet11

Bruno Grenet.
*An upper bound for the permanent versus determinant problem*.
Manuscript, 2011 (the PDF is dated May 25, 2012). https://www-verimag.imag.fr/~grenetb/publis/Gre11.pdf . Checked against the author's PDF on 2026-11-08.
Its unnumbered Lemma (an algebraic branching program of size `2ⁿ` on the subsets of `{1, …, n}` computes the permanent) is the private path-sum development in `CslibFrontier/Foundations/LinearAlgebra/Matrix/GrenetPermanent.lean`.
Its unnumbered Theorem (a `(2ⁿ - 1) × (2ⁿ - 1)` matrix with entries in `{x_ij} ∪ {-1, 0, 1}` has the permanent as determinant) is `Matrix.permanent_eq_det_grenetMatrix` together with `Matrix.grenetMatrix_apply_eq`.
`Cslib.Circuits.Arithmetic.isProjection_permanent_det_two_pow_sub_one` is the strict projection form, Grenet's `dc_s(n) ≤ 2ⁿ - 1`.
Grenet works over fields of characteristic other than two; the library proves the identity over every commutative ring.
The library uses Grenet's construction with a different sign normalization: `-1` on the diagonal at every vertex other than the merged source and sink, rather than loops of weight `1` with weight `-1` on the first layer for even `n`.
It proves the determinant identity through the adjugate rather than through cycle covers.

<a id="grigoriev01"></a>
## grigoriev01

Dima Grigoriev.
*Linear lower bound on degrees of Positivstellensatz calculus proofs for the parity*.
Theoretical Computer Science 259(1–2), 613–622, 2001. https://doi.org/10.1016/S0304-3975(00)00157-2 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC.
The article is behind a publisher paywall, so its text was not consulted, and no theorem or page locator in it is claimed.
The library attributes the linear degree lower bound for Tseitin parity systems on expanders to this paper.
The precise statement used is that of [barak-steurer16](#barak-steurer16), lecture "Higher-degree integrality gaps", Lemma 24.

<a id="grigorievhirschpasechnik02"></a>
## grigorievhirschpasechnik02

Dima Grigoriev, Edward A. Hirsch and Dmitrii V. Pasechnik.
*Complexity of Semialgebraic Proofs*.
Moscow Mathematical Journal 2(4), 647–679, 2002; extended abstracts in STACS 2002 and ICALP 2002. https://doi.org/10.17323/1609-4514-2002-2-4-647-679 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC.
On the same date worker w96-sos consulted the author-hosted copy https://edwardahirsch.github.io/edwardahirsch/papers/02mmj.pdf for Section 2.3 (the translation of a CNF into the inequalities (2.4)–(2.6)), Section 2.5 (static `LS₊`) and Example 2.1 (p. 10 of that copy: the degree-`2` static `LS₊` refutation of `PHP^m_{m-1}`).
The ECCC version (TR01-103) could not be retrieved, and the typeset journal pagination of Example 2.1 was not checked.

<a id="grs12"></a>
## grs12

Arpita Ghosh, Tim Roughgarden and Mukund Sundararajan.
*Universally Utility-Maximizing Privacy Mechanisms*.
SIAM Journal on Computing 41(6), 1673–1693, 2012; conference version STOC 2009. https://doi.org/10.1137/09076828X . §2.1 and Example 2.1 were checked against arXiv:0811.2841v3 on 2026-11-07.

<a id="gsw13"></a>
## gsw13

Craig Gentry, Amit Sahai, Brent Waters.
“Homomorphic Encryption from Learning with Errors: Conceptually-Simpler, Asymptotically-Faster, Attribute-Based.”
*CRYPTO 2013*, LNCS 8042, 75–92. https://doi.org/10.1007/978-3-642-40041-4_5 ; authors' full-version record https://eprint.iacr.org/2013/340 . Metadata/abstract checked; PDF fetch was blocked in this source pass.

<a id="gulstacchetti1999"></a>
## gulstacchetti1999

Faruk Gul and Ennio Stacchetti.
"Walrasian Equilibrium with Gross Substitutes."
*Journal of Economic Theory* 87(1), 95–124, 1999 (bibliography key `GulStacchetti1999`).
Bibliographic metadata checked against [blumrosennisan07](#blumrosennisan07), p. 297; the primary journal PDF was not consulted in this pass (`primary PDF unverified`), and no internal theorem or page locator is claimed.
[GrossSubstitutes.lean](../CslibFrontier/GameTheory/Mechanism/CombinatorialAuction/GrossSubstitutes.lean) cites it alongside [blumrosennisan07](#blumrosennisan07) (§§11.7.1, 11.8, and Exercise 11.6, pp. 290–299) for submodularity of gross-substitutes valuations and existence of exact Walrasian equilibria.

<a id="gupta23"></a>
## gupta23

Anupam Gupta.
“Dimension Reduction and the JL Lemma.”
Chapter 11 of the lecture notes for CMU 15-850 *Advanced Algorithms*; PDF dated 2023-02-17. https://www.cs.cmu.edu/~15850/notes/lec12.pdf . Checked on 2026-11-07 UTC: §11.6.2, Lemma 11.9 bounds `𝔼 exp (tV²)` for a symmetric σ-sub-Gaussian `V` by the corresponding Gaussian moment generating function.
The proof linearizes the square with an independent Gaussian, exchanges the averages and applies the sub-Gaussian bound.
The notes apply the lemma to Rademacher projection matrices.

<a id="guruswamirudrasudan25"></a>
## guruswamirudrasudan25

Venkatesan Guruswami, Atri Rudra and Madhu Sudan.
*Essential Coding Theory*.
Draft book, version of 26 August 2025. https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/ ; open PDF https://cse.buffalo.edu/faculty/atri/courses/coding-theory/book/web-coding-book.pdf . The library's key is `GuruswamiRudraSudan2019`.
Read in the open PDF on 2026-11-08 for Chapter 6:

- §6.2 (the binary symmetric channel) and §6.2.2 (capacity: reliable communication is possible below it and impossible above it);
- Theorem 6.3.1 (p. 119): part (1), achievability with error `2^(−δn)`, and part (2), for `0 ≤ p < 1/2` and `k ≥ ⌈(1 − H(p) + ε) n⌉` with `0 ≤ ε ≤ 1/2 − p`, some message misdecoded with probability more than `1/2`;
- §6.3.1, the packing proof of part (2) (pp. 120–122), and Remark 6.3.2, the error bound `1 − 2^(−βn)`;
- §6.3.2 and Claim 6.3.3, the random-coding proof of part (1).

The draft does not name Wolfowitz.
The manual's attribution of the strong converse for discrete memoryless channels to him is standard background and was not checked against his paper.

Multiplicity list decoding of Reed–Solomon codes (the Guruswami–Sudan algorithm) appears in Chapter 12 of this 26 August 2025 draft (checked correspondence, printed pp. 253–259):

- §§12.2.3–12.2.4: adding multiplicities to Sudan's algorithm, with Definitions 12.2.8–9 (multiplicity vanishing via shifted polynomials and Hasse derivatives, formalized in [Bivariate.lean](../CslibFrontier/Foundations/Algebra/Polynomial/Bivariate.lean) as `Polynomial.Bivariate.shift`, `Polynomial.Bivariate.hasseDerivBiv`, and `Polynomial.Bivariate.VanishesToOrder`);
- Algorithm 12.2.3 and Lemmas 12.2.10–11: multiplicity interpolation and root-divisibility (formalized in [GuruswamiSudan.lean](../CslibFrontier/Foundations/Data/Code/GuruswamiSudan.lean) as `Cslib.Code.GuruswamiSudan.IsWeightedInterpolant`, `Cslib.Code.GuruswamiSudan.IsInterpolant`, `Cslib.Code.GuruswamiSudan.weightedInterpolant`, `Cslib.Code.GuruswamiSudan.interpolant`, `Cslib.Code.GuruswamiSudan.IsInterpolant.X_sub_C_dvd`, and `Cslib.Code.guruswamiSudan`);
- Theorem 12.2.12: list decoding of Reed–Solomon codes up to the Johnson radius `1 - √ρ` (formalized as `Cslib.Code.mem_guruswamiSudan_johnson_iff` and `Cslib.Code.exists_guruswamiSudan_of_eps`).

<a id="guruswamisudan99"></a>
## guruswamisudan99

Venkatesan Guruswami and Madhu Sudan.
"Improved Decoding of Reed–Solomon and Algebraic-Geometry Codes."
*IEEE Transactions on Information Theory* 45(6), 1757–1767, 1999; preliminary version FOCS 1998. https://doi.org/10.1109/18.782097 . The library's key is `GuruswamiSudan1999`.
Bibliographic metadata checked against `references.bib`; the paywalled IEEE article body was not inspected directly, so no journal theorem or page locator is claimed.
The formalized exposition follows [Essential Coding Theory](#guruswamirudrasudan25), §§12.2.3–12.2.4, Definitions 12.2.8–9, Algorithm 12.2.3, Lemmas 12.2.10–11, and Theorem 12.2.12 (pp. 253–259), with characteristic-independent bivariate polynomial algebra (`Polynomial.Bivariate.VanishesToOrder`, `Polynomial.Bivariate.weightedDegree`) in [Bivariate.lean](../CslibFrontier/Foundations/Algebra/Polynomial/Bivariate.lean) and Reed–Solomon multiplicity interpolation and Johnson-radius decoding (`Cslib.Code.GuruswamiSudan.IsWeightedInterpolant`, `Cslib.Code.GuruswamiSudan.IsInterpolant`, `Cslib.Code.guruswamiSudan`, `Cslib.Code.mem_guruswamiSudan_johnson_iff`, `Cslib.Code.exists_guruswamiSudan_of_eps`) in [GuruswamiSudan.lean](../CslibFrontier/Foundations/Data/Code/GuruswamiSudan.lean).

<a id="gusfield90"></a>
## gusfield90

Dan Gusfield.
“Very Simple Methods for All Pairs Network Flow Analysis.”
*SIAM Journal on Computing* 19(1), 143–155, 1990. https://doi.org/10.1137/0219009 . Bibliographic metadata checked through the publisher record; the article body (paywalled) was not inspected, so no theorem or page locator is given.
Cited for the variant of the Gomory–Hu construction without contraction: a parent array, one minimum cut computation per non-root vertex in the original graph, the re-hanging of vertices on the source side, and the swap of `s` and `t` when the parent of `t` is on the source side.
That description was taken from secondary accounts of the algorithm.
The Lean proof of correctness (`isGomoryHuTree_gusfieldParent`) is self-contained and does not follow the article's argument.

<a id="gusfield97"></a>
## gusfield97

Dan Gusfield.
*Algorithms on Strings, Trees, and Sequences: Computer Science and Computational Biology.*
Cambridge University Press, 1997. https://doi.org/10.1017/CBO9780511574931 . Bibliographic metadata checked through the publisher record, and section titles through a table of contents; the book body was not inspected in this pass.
Cited for the Z-values and Z-boxes of §1.3, the linear-time Z algorithm of §1.4, and exact matching through the Z-values of `P$T` in §1.5; these locators come from the section titles.
Theorem numbers and the precise statements in the body were not checked.

<a id="hadzilacostoueg1994"></a>
## hadzilacostoueg1994

Vassos Hadzilacos and Sam Toueg.
*A Modular Approach to Fault-Tolerant Broadcasts and Related Problems*.
Technical Report TR94-1425, Department of Computer Science, Cornell University, May 1994. https://hdl.handle.net/1813/6207 . Checked firsthand on 2026-11-22 against the Cornell eCommons scan (`https://ecommons.cornell.edu/server/api/core/bitstreams/5c4f64e7-53d3-4098-a28b-341974cb86b2/content`, SHA-256 `cb3ba50162af16ed480ccdabf38661653577002f19ccce6790b072ae412002c5`; cited by printed report page numbers, where printed page `p` is PDF page `p + 2`): §3.1 (pp. 9–10, Reliable Broadcast = Validity + Agreement + Integrity on p. 10), §3.3 (pp. 11–12, Causal Broadcast and prefix-closed Causal Order, Theorem 1), §3.4 (pp. 12–13, Atomic Broadcast = Reliable Broadcast + Total Order on p. 13), §3.8 (pp. 14–15, Uniform Integrity on p. 14 and Uniform Causal/Total Order and Uniform counterparts on p. 15), §3.9 (pp. 15–16, modular broadcast hierarchy on p. 16), §7.1 (pp. 56–57, Consensus specification), §7.2.1 (p. 58, Figure 13 transformation of Atomic Broadcast into Consensus, Theorem 13, and Corollary 2 establishing 1-crash asynchronous impossibility via FLP), and §7.2.2 (pp. 59–63, Figure 14 on p. 60 transforming Consensus and Reliable Broadcast into Atomic Broadcast, Lemmas 1–5 and Corollary 3 on pp. 61–63, and Theorem 14 and Corollary 4 on p. 63).
As steps toward [#7297](https://github.com/cslib-community/cslib-frontier/issues/7297) in [CausalBroadcast/TotalOrder.lean](../CslibFrontier/Computability/Distributed/CausalBroadcast/TotalOrder.lean), `TotalOrderBroadcastAlg` follows `Cslib.FLP.Algorithm` in supplying one initial broadcast value `inp p : V` per process `p` (`start`) for the Figure 13 / Theorem 13 / Corollary 2 reduction (`consensusOfTotalOrderBroadcast`, `not_exists_oneShotTotalOrderBroadcast_ge_one`) and the `0`-fault sequencer `zeroFaultTotalOrderAlg` (`exists_oneShotTotalOrderBroadcast_iff_eq_zero`), while `ConsensusSlotExec` and `totalOrderBroadcast_of_consensusSlotExec` model the multi-shot Figure 14 / Chandra–Toueg Figure 7 batch reduction over arbitrary `[LinearOrder Msg]` at the abstract discrete-time (`t : ℕ`) subprotocol-trace level.

<a id="halpernteague2004"></a>
## halpernteague2004

Joseph Y. Halpern and Vanessa Teague.
"Rational Secret Sharing and Multiparty Computation: Extended Abstract."
*Proceedings of the Thirty-Sixth Annual ACM Symposium on Theory of Computing (STOC 2004)*, 623–632, 2004. https://doi.org/10.1145/1007352.1007447 . Bibliographic metadata only (`references.bib`); the full text was not inspected locally in this pass and no section or theorem locators are attributed here.
Cited in [SecretSharing.lean](../CslibFrontier/GameTheory/RationalCrypto/SecretSharing.lean) and [Payoff.lean](../CslibFrontier/GameTheory/Strategic/Payoff.lean) for bounded-round `IDoWDS` impossibility in rational secret sharing and randomized geometric-termination share reconstruction.

<a id="hanson03"></a>
## hanson03

Robin Hanson.
"Combinatorial Information Market Design."
*Information Systems Frontiers* 5(1), 107–119, 2003 (bibliography key `Hanson2003`). https://doi.org/10.1023/A:1022058209073 . Bibliographic metadata checked via DOI/catalogue records and cross-referenced in [pennocksami07](#pennocksami07), §26.4.1; the journal full text was not directly inspected, so internal theorem and page locators are marked `unverified` in the results registry.
Cited at paper level in [LMSR.lean](../CslibFrontier/GameTheory/PredictionMarket/LMSR.lean) for sequential market scoring rules (`msrStepPayoff`, `msrTotalPayoff`, `msrStepPayoff_expected_lt`).

<a id="hanson07"></a>
## hanson07

Robin Hanson.
"Logarithmic Market Scoring Rules for Modular Combinatorial Information Aggregation."
*The Journal of Prediction Markets* 1(1), 3–15, 2007 (bibliography key `Hanson2007`). https://doi.org/10.5750/jpm.v1i1.417 . Bibliographic metadata checked via DOI/catalogue records and cross-referenced in [pennocksami07](#pennocksami07), §26.4.1; the journal full text was not directly inspected, so internal theorem and page locators are marked `unverified` in the results registry.
Cited at paper level in [LMSR.lean](../CslibFrontier/GameTheory/PredictionMarket/LMSR.lean) for Hanson's logarithmic market scoring rule cost-function formulation (`lmsrCost`, `lmsrPrice`) and `b * log |Ω|` worst-case loss bound.

<a id="harpeledindykmotwani12"></a>
## harpeledindykmotwani12

Sariel Har-Peled, Piotr Indyk, Rajeev Motwani.
“Approximate Nearest Neighbor: Towards Removing the Curse of Dimensionality.”
*Theory of Computing* 8(14), 321–350, 2012. https://doi.org/10.4086/toc.2012.v008a014 . DOI and metadata as reported by search indexes; the open-access PDF could not be fetched in this pass (no connection).
Cited for the `(r, cr, p₁, p₂)` form of locality-sensitive families, for the LSH `(c, r)`-near-neighbour structure with exponent `ρ = log (1/p₁) / log (1/p₂)` (locator Theorem 3.4, from secondary summaries; not checked against the text).
According to those summaries, Theorem 3.4 is stated for a fully dynamic structure with `p₁, p₂ ∈ (0, 1)`, and the library formalizes only the static structure.
Also cited for `ρ ≤ 1/c` for bit sampling in Hamming space (locator Section 3.2.1, from secondary summaries; not checked against the text).

<a id="hartline21"></a>
## hartline21

Jason D. Hartline.
*Mechanism Design and Approximation*, book manuscript; chapters 1–7 revised 20 September 2021. http://jasonhartline.com/MDnA/ . The author-hosted Chapter 2, "Equilibrium", was consulted on 2026-11-08 for Definitions 2.3.2 and 2.4.1, §2.3, §2.4, Proposition 2.4.1, Theorem 2.5.1, §2.7 (Corollaries 2.7.1 and 2.7.2, Example 2.7.1), §2.8 (Example 2.8.1) and §2.9; locators follow that version.

<a id="hartlinekarlin07"></a>
## hartlinekarlin07

Jason D. Hartline and Anna R. Karlin.
"Profit Maximization in Mechanism Design."
Chapter 13 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 331–361 (bibliography key `HartlineKarlin2007`, ISBN `978-0-521-87282-9`; page 362 is a blank verso before Chapter 14 on page 363).
A university-hosted PDF of the book (non-printable online edition, SHA-256 `83084d9996024ca92f313c5ae55fec7b3b379f06172a4c24b62229da9c558543`) was consulted via rendered page images on 2026-11-24 for the table of contents (pp. viii–ix), §13.1 (pp. 331–334: seller production cost `c(x)`, Example 13.1 single-item auction, Example 13.2 digital goods auctions, §13.1.2 preliminaries, Definition 13.5 truthful in expectation, Theorem 13.6, Observation 13.1.1), §13.2 (pp. 335–338: Definition 13.7 `VA_r`, Definition 13.8 virtual valuation, Definition 13.9 virtual surplus, Theorem 13.10 expected profit equals expected virtual surplus, Lemma 13.11, §13.2.2 Lemma 13.12 truthfulness of virtual-surplus maximization and remark on the technical ironing extension for nonmonotone virtual valuations, Definition 13.13, Example 13.14, Theorem 13.15, Example 13.16, Definition 13.17 optimal sale price `opt(F)`, Theorem 13.18 optimal Bayesian digital goods auction), §13.3.1 (pp. 339–340: Definition 13.19 empirical distribution `F_b`, Definition 13.20 empirical Myerson `EM`, Definition 13.21 deterministic optimal price `DOP`, Example 13.23 `10` bids at `$10` and `90` bids at `$1`), §13.4 (pp. 344–349: §13.4.1 Definition 13.33 competitive ratio, §13.4.2 Definition 13.34 `ℱ⁽²⁾` and two-bid `($1, $2)` tightness example, §13.4.4 Definition 13.39 decision problem and `ℱ`, Definition 13.40 `ProfitExtract_R`, §13.4.5 Definition 13.41 `RSPE` and Theorem 13.42), and Exercises (pp. 360–361: Exercise 13.1 seller reservation value `v_0 > 0`, Exercise 13.3 discrete virtual valuations, Exercise 13.4 single-item `EM` equals Vickrey, and Exercise 13.10).
Cited by [Mechanism/Ironing.lean](../CslibFrontier/GameTheory/Mechanism/Ironing.lean) and `ProfitExtraction.lean`.
Two printed slips on p. 348 are noted and repaired in `ProfitExtraction.lean`: the informal intuition paragraph after Definition 13.41 writes `ℱ⁽²⁾` instead of `ℱ` for `R'` and `R''` (Definition 13.41(ii) uses `ℱ`), and the prose and proof of Theorem 13.42 claim that the realized profit of `RSPE` equals `min(R', R'')`, whereas when `R' = R'' > 0` both profit extractions succeed and yield `2 * R'` (counterexample `b = (1, 1)` checked in `CslibFrontierTests/GameTheory/DigitalGoods.lean`).
The original papers cited in Chapter 13 were not inspected directly.

<a id="hartmanis1968"></a>
## hartmanis1968

Juris Hartmanis.
"Computational Complexity of One-Tape Turing Machine Computations."
*Journal of the ACM* 15(2), 325–339, 1968. https://doi.org/10.1145/321450.321464 . Bibliographic metadata checked through Crossref; the article body was not inspected in this pass.
The manual cites it for the `n log n` lower bound on one-tape recognition of nonregular languages, as attributed in [Pighizzini 2009](#pighizzini2009), §1 and §4.

<a id="hartmascolell00"></a>
## hartmascolell00

Sergiu Hart and Andreu Mas-Colell.
"A Simple Adaptive Procedure Leading to Correlated Equilibrium."
*Econometrica* 68(5), 1127–1150, September 2000. https://doi.org/10.1111/1468-0262.00153 . Inspected on 2026-11-24 against the published *Econometrica* PDF: checked §2 (pp. 1129–1131: correlated equilibrium and correlated `ε`-equilibrium definitions, Chicken non-convex-hull-of-Nash remark on p. 1129, pairwise regret `(2.1a)–(2.1c)`, inertial transition probabilities `(2.2)` with footnote 5 normalization, empirical distribution `(2.3)`, and Main Theorem), §3 (pp. 1133–1138: stationary regret-matching balance equation `(3.1)`, Theorem A, the Proposition on pp. 1133–1134 characterizing empirical convergence to correlated `ε`-equilibria via pairwise regrets, the Corollary on p. 1134, Blackwell's Approachability Theorem `(3.2)` with Euclidean projection `F(x) = [x]_-` onto `ℝ_-^L` in Figure 2 on p. 1137, proof `(3.3)–(3.5)` of Theorem A, and the `1/√t` rate remark on p. 1138), §4(c) (p. 1139: unconditional/external regret-matching `(4.2a)–(4.2b)` and Theorem B, attributing Blackwell's approachability construction to [Blackwell 1956]), and Appendix Step M1 (p. 1146: quadratic nonpositive-orthant potential recursion), formalized in [OnlineLearning/RegretMatching.lean](../CslibFrontier/MachineLearning/OnlineLearning/RegretMatching.lean) and [Strategic/RegretMatching.lean](../CslibFrontier/GameTheory/Strategic/RegretMatching.lean).

<a id="healkunreuther07"></a>
## healkunreuther07

Geoffrey Heal and Howard Kunreuther.
"Modeling Interdependent Risks."
*Risk Analysis* 27(3), 621–634, 2007. https://doi.org/10.1111/j.1539-6924.2007.00904.x ; Wharton Risk Management and Decision Processes Center working copy (November 2006, 22 PDF pp.): https://repository.upenn.edu/server/api/core/bitstreams/deed4e9e-2751-441c-82fb-1b7c426dd954/content . Checked against that 22-page Wharton PDF (journal pagination 621–634 taken from Crossref) on 2026-11-24 UTC: §2.1–§2.2 (pp. 4–5: Class 1 partial protection vs. Class 2 complete protection), §3 ("3.
The Model", pp. 6–11, with §3.1 "Tipping" on p. 9: eqs. (1)–(3) for critical protection cost `c_i(s_{-i}) = p_i L_i ∏_{j ≠ i, s_j = N} (1 - r_{j, i})`, Definition 1 on p. 8 for pure Nash equilibrium, Theorem 1 on p. 9 for constructive pure-Nash existence via monotone best-response iteration, Theorem 2 on p. 9 and Appendix p. 20 for coexistence and Pareto dominance of full investment over zero investment, Definition 2 on p. 9 for critical coalitions, Definition 3 on p. 9 for minimum critical coalitions `MCC`, and Theorem 3 and Definition 4 `SCC` on p. 10 with Appendix eq. (17) on p. 20 for smallest critical coalitions under agent-uniform contagion externalities), and §5.1–§5.2 (§5.1 "Tipping" on p. 14 and §5.2 "Cascading" on pp. 15–16: multi-airline Class 1 baggage-security games and the 3-airline 2-round tipping cascade seeded by `{A_3}`).
Inspection uncovered an omitted boundary case in Appendix eq. (17) (p. 20) of Theorem 3: the paper checks only agents `i > k` outside both coalitions and omits replaced agents `k' ∈ M' \ M` whose high `c_{k'}` was bypassed while inside `M'`; [Security/Interdependent.lean](../CslibFrontier/GameTheory/Security/Interdependent.lean) (`InterdependentSecuritySpec.isCriticalCoalition_of_higher_contagion`) adds the necessary normalized-reluctance alignment `c_k / (p_k L_k) ≤ c_j / (p_j L_j)` on `M' \ M` vs. `M \ M'` (automatic for homogeneous `(p, L, c)`), and [SecurityEconomics.lean](../CslibFrontierTests/GameTheory/SecurityEconomics.lean) supplies checked `Fin 3` (`IsCriticalCoalition`) and `Fin 4` (`TipsAll`) counterexamples without that hypothesis.
Endogenous direct-loss risks (§4, pp. 11–12) and Class 2 complete-protection problems (§6, pp. 17–19) are not formalized here.

<a id="hearndemaine2005"></a>
## hearndemaine2005

Robert A. Hearn and Erik D. Demaine.
*PSPACE-completeness of sliding-block puzzles and other problems through the nondeterministic constraint logic model of computation*.
Theoretical Computer Science 343 (2005), 72–96.
Sections 2.1–2.2 of the authors’ version define the three reachability questions and the AND/OR vertex types.
Theorem 5 and Corollary 6 (§3.1, pp. 7–8 of that version) prove PSPACE-completeness of the three questions.
The formalization covers finite AND/OR multigraphs, allowing loops and parallel edges as in footnote 2 on p. 4.
It uses one bit per edge and deterministic Savitch search for the upper bounds.
The polynomial-time reductions from alternating prenex CNF produce loop-free graphs.
Theorem 9 (§3.2, p. 9, Figure 8 and Lemmas 7–8) extends the three results to planar AND/OR graphs.
The planar problems use the same explicit graph encodings and require existence of a continuous polygonal embedding, allowing loops and parallel edges.
Polynomially bounded rotation certificates give the planarity upper bound.
The reductions compile closed, well-typed plane words into loop-free graphs with continuous planar orthogonal grid drawings.
[Authors’ version](https://erikdemaine.org/papers/NCL_TCS/paper.pdf)

<a id="heath24"></a>
## heath24

David Heath.
"Efficient Arithmetic in Garbled Circuits."
*Advances in Cryptology – EUROCRYPT 2024*, Lecture Notes in Computer Science 14655, 3–31, 2024. https://doi.org/10.1007/978-3-031-58740-5_1 . Full version: Cryptology ePrint Archive, Paper 2024/139, https://eprint.iacr.org/2024/139 . Locators follow the ePrint full version: §2.1 Definition 1 (circular correlation robustness), §3.2 Definitions 4 and 6 (switch systems and legality), §3.3 Construction 1 and Figure 2 (switch-system garbling and evaluation), §4 (pp. 13–14) and §4.1 `bin-to-hot` (p. 14, single-ciphertext binary-to-one-hot conversion, halving the material of Heath–Kolesnikov CCS 2021), and Appendix A, Theorem 4 and Figure 4 (obliviousness and its hybrids).

<a id="heldkarp62"></a>
## heldkarp62

Michael Held and Richard M. Karp.
“A Dynamic Programming Approach to Sequencing Problems.”
*Journal of the Society for Industrial and Applied Mathematics* 10(1), 196–210, 1962. https://doi.org/10.1137/0110015 . Bibliographic metadata checked on 2026-11-07; the article body was not inspected in this pass, so the manual cites it for the subset dynamic program and not for a numbered statement.

<a id="hellerstein2010"></a>
## hellerstein2010

Joseph M. Hellerstein.
"The Declarative Imperative: Experiences and Conjectures in Distributed Logic."
*ACM SIGMOD Record* 39(1), 5–19, 2010 (PODS 2010 invited keynote paper; also UC Berkeley Technical Report UCB/EECS-2010-90, June 1, 2010). https://doi.org/10.1145/1860702.1860704 ; open copy http://www2.eecs.berkeley.edu/Pubs/TechRpts/2010/Archive/EECS-2010-90.pdf . Checked against UCB/EECS-2010-90 (16 PDF pp.: 2 cover/copyright pp. + 14 article pp., SHA-256 `77f1f27394170d96281fe81a616b63112d1f36749cdc6364ce2d50f63d0895c2`) on 2026-11-22 UTC: Section 3.4.3 (PDF p. 9 / article p. 7: voting/threshold monotonicity vs counting-to-0 non-monotonicity) and Section 4.1 ("Parallelism, Distribution and Monotonicity", PDF pp. 10–11 / article pp. 8–9, Conjecture 1 "Consistency And Logical Monotonicity (CALM)" on PDF p. 11 stating that a program has an eventually consistent, coordination-free execution strategy iff it is expressible in monotonic logic).
Journal pagination comes from DOI metadata; internal page locators follow UCB/EECS-2010-90.
Cited in [CRDT/Monotonicity.lean](../CslibFrontier/Computability/Distributed/CRDT/Monotonicity.lean) as motivation for the semilattice irrevocable-emission monotonicity step toward [#7502](https://github.com/cslib-community/cslib-frontier/issues/7502).

<a id="hendlershavityerushalmi2004"></a>
## hendlershavityerushalmi2004

Danny Hendler, Nir Shavit, and Lena Yerushalmi.
"A Scalable Lock-Free Stack Algorithm."
*Proceedings of the Sixteenth Annual ACM Symposium on Parallelism in Algorithms and Architectures (SPAA)*, 206-215, 2004 (bibliography key `HendlerShavitYerushalmi2004`). https://doi.org/10.1145/1007912.1007944 . Inspected the author-hosted SPAA proceedings PDF https://people.csail.mit.edu/shanir/publications/Lock_Free.pdf (10 pages, printed pp. 206-215; SHA-256 `7d0203f55e992df1ef487c6418ac472aaf606d238b51148f0465c42118de44f1`) on 2026-11-22 UTC: Section 2.1 (p. 208, Figure 2 `Simple_Stack` and `Cell` types following Treiber's singly-linked list stack); Section 2.2 (p. 208, Figure 3 `TryPerformStackOp` lines `T1-T19` implementing central-stack `PUSH` and `POP` via `CAS(&S.ptop, ...)`); Sections 2.2-2.3 (p. 209, ABA prevention via version tags at the end of Section 2.2, and cell-pool memory management with SMR or ROP in Section 2.3); Section 5 (p. 212, Definition 5.1 sequential LIFO stack specification, explicitly abstracting away ABA issues in the proof); Section 5.2 (p. 214, Lemma 5.13 central-stack linearization points at successful `CAS` and empty `phead == NULL` read, and Theorem 5.16); and Section 5.3 (p. 215, Theorem 5.17 lock-freedom via failed `CAS` witnessing an intervening successful `CAS` on `phead`).
Cited by [ConcurrentObjects/TreiberStack.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/TreiberStack.lean), which formalizes a fresh-node (ABA-free) central-stack step toward [#7501](https://github.com/cslib-community/cslib-frontier/issues/7501) (`treiberFreshNode_isLinearizable`, `treiberFreshNode_isLockFree`, and `treiberFreshNode_cas_fail_witnesses_intervening_cas`), leaving the elimination-backoff collision array and ABA version-tagged free-list recycling open in [#7501](https://github.com/cslib-community/cslib-frontier/issues/7501).

<a id="hennie1965"></a>
## hennie1965

F. C. Hennie.
“One-tape, off-line Turing machine computations.”
*Information and Control* 8(6), 553–578, 1965. https://doi.org/10.1016/S0019-9958(65)90399-2 . Bibliographic metadata checked; the article body was not inspected in this pass, so the manual cites it for the crossing-sequence method and not for a numbered statement.

<a id="henson26"></a>
## henson26

Christopher Henson and Fabrizio Montesi.
*Computer Science as Infrastructure: the Spine of the Lean Computer Science Library (CSLib)*.
EPTCS 449 (LSFA 2026), pp. 141–148, 2026. https://doi.org/10.4204/EPTCS.449.9 . Version-of-record metadata verified through https://arxiv.org/abs/2602.15078v2 on 2026-11-02 UTC; DOI resolver was unavailable in this research environment.

<a id="herlihy1991"></a>
## herlihy1991

Maurice Herlihy.
"Wait-Free Synchronization."
*ACM Transactions on Programming Languages and Systems* 13(1), 124–149, 1991. https://doi.org/10.1145/114005.102808 . Inspected the author-hosted print PDF https://cs.brown.edu/~mph/Herlihy91/p124-herlihy.pdf (SHA-256 `f2758020dc0c0dd6502d5eb43ccdce313d568095b8eb3eabb9d02959394a221f`; note the PDF running footer misprints `Vol. 11, No. 1`, whereas the journal volume is `13`, `0164-0925/91/0100-0124`) on 2026-11-22 UTC: Figure 1 (p. 126, impossibility and universality hierarchy); §2.2–2.3 (pp. 128–130, concurrent systems, sequential histories, linearizability `<_H ⊆ <_S`, wait-free vs bounded wait-free implementations); §3 (pp. 130–131, consensus consistency/wait-freedom/validity and Definition 1 on p. 130 for consensus number); §3.1 (pp. 131–133, bivalence/univalence/decision steps on p. 131, Theorem 2 on pp. 131–132 & Figures 3–5 on pp. 132–133 proving read/write registers have consensus number `1`); §3.2 (pp. 133–135, Figure 6 on p. 133, Theorem 3 on pp. 133–134 & Figure 7 on p. 134 for 2-process RMW consensus, p. 134 defining "interfering" commuting-or-overwriting RMW families, Theorem 4 on p. 134 proving 3-process impossibility for interfering RMW operations, and Theorem 5 on p. 135 & Figures 8–9 on p. 135 proving `compare&swap` has infinite consensus number); and §4.1 (pp. 143–146, remark on p. 144 noting that omitting the `announce` helping step makes the log-append protocol nonblocking rather than wait-free across unbounded streams, Figure 14 on p. 145, Lemmas 1–5 on pp. 144–146, and Theorem 14 on p. 146).
Cited by [SharedMemory/Basic.lean](../CslibFrontier/Computability/Distributed/SharedMemory/Basic.lean) (`Protocol.WaitFree` modeled as accessibility of active transitions from every `initConfig`), [SharedMemory/Hierarchy.lean](../CslibFrontier/Computability/Distributed/SharedMemory/Hierarchy.lean) (`1 < 2 < ∞` hierarchy, formalizing the concrete `test&set` instance of Figure 7 while leaving Theorem 3's general arbitrary-nontrivial-RMW lower bound open), and [SharedMemory/Universal.lean](../CslibFrontier/Computability/Distributed/SharedMemory/Universal.lean) (formalizing the finite-invocation-batch `P`, unhelped idealized `ConsensusCell` log-append step under `ValidSlotSchedule`, without §4.1's `announce`/helping array or §4.2's bounded-memory cell reclamation); also cited by [ConcurrentObjects/Progress.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/Progress.lean) (`ProgressSystem.IsWaitFree` over infinite multi-operation schedules).

<a id="herlihyluchangcomoir2003"></a>
## herlihyluchangcomoir2003

Maurice Herlihy, Victor Luchangco, and Mark Moir.
"Obstruction-Free Synchronization: Double-Ended Queues as an Example."
*23rd International Conference on Distributed Computing Systems (ICDCS)*, 522-529, 2003 (bibliography key `HerlihyLuchangcoMoir2003`). https://doi.org/10.1109/ICDCS.2003.1203503 . Inspected the 8-page author-hosted reprint https://cs.brown.edu/people/mph/HerlihyLM03/main.pdf (8 pages, numbered pp. 1-8; SHA-256 `5624664dd52ccbec23411377441d157f811f97e4d801e7471787ad97c6bf2d68`) on 2026-11-22 UTC: Section 1 (pp. 1-2, defining obstruction-free synchronization as guaranteed finite-step completion when a thread executes in isolation from any reachable state, contrasting it with wait-free and lock-free synchronization, and discussing livelock when two or more conflicting threads contend concurrently; Sections 3-4 on pp. 2-7 present the array-based obstruction-free double-ended queue example).
Cited by [ConcurrentObjects/Progress.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/Progress.lean) for `ProgressSystem.IsLockFree`, `ProgressSystem.IsObstructionFree`, `ProgressSystem.IsLockFree.isObstructionFree`, and the original minimal two-step shared-register claim-and-verify witness `racingClaimSystem` separating `IsObstructionFree` from `IsLockFree` (Section 3's double-ended queue is not formalized).

<a id="herlihyshavit1999"></a>
## herlihyshavit1999

Maurice Herlihy and Nir Shavit.
"The Topological Structure of Asynchronous Computability."
*Journal of the ACM* 46(6), 858–923, 1999. https://doi.org/10.1145/331524.331529 ; author-hosted journal PDF https://cs.brown.edu/~mph/HerlihyS99/p858-herlihy.pdf . Inspected the typeset journal PDF (SHA-256 `88d855c2dd21bc7066d652dd84524c492d245fe3e210c3702bed19e652d452c0`, pp. 858–923) on 2026-11-22 UTC: Section 3.3 ("Set Agreement", pp. 879–882, including the `k`-set agreement task specification on p. 879, Figure 22 and Lemma 3.2 Sperner's Lemma on p. 880, Figure 23 and Theorem 3.3 on p. 881, and Figure 24 on p. 882) and Section 5.2 ("The Chromatic Subdivision", pp. 897–899, including Definition 5.3 on p. 897 for the combinatorial standard chromatic subdivision conditions (1)–(3) and Figure 33 and Definition 5.4 on p. 898 for the iterated standard chromatic subdivision).
Cited by [SetAgreement/ImmediateSnapshot.lean](../CslibFrontier/Computability/Distributed/SetAgreement/ImmediateSnapshot.lean) (formalizing the input-simplex extension argument of the proof of Theorem 3.3 on p. 881 in `IISProtocol.isCarrierValid_of_isValid`) and [SetAgreement/Impossibility.lean](../CslibFrontier/Computability/Distributed/SetAgreement/Impossibility.lean) (proving the odd panchromatic parity step `odd_card_panchromatic_iis` and `R`-round `IIS` `k`-set agreement impossibility step `not_solvesSetAgreement_iis` combinatorially via a backwards-from-`R` split/merge involution paired with `Cslib.Sperner.odd_card_doors_iff_surjective`, while leaving Theorem 3.1 and Theorem 3.3's general asynchronous read/write shared-memory to `IIS` reduction open in [#7504](https://github.com/cslib-community/cslib-frontier/issues/7504)).

<a id="herlihywing1990"></a>
## herlihywing1990

Maurice P. Herlihy and Jeannette M. Wing.
"Linearizability: A Correctness Condition for Concurrent Objects."
*ACM Transactions on Programming Languages and Systems* 12(3), 463-492, July 1990 (bibliography key `HerlihyWing1990`). https://doi.org/10.1145/78969.78972 . Inspected the author-hosted scan of the published journal article https://www.cs.cmu.edu/~wing/publications/HerlihyWing90.pdf (30 pages, printed pp. 463-492; SHA-256 `79e2ff81a15c55de870492231e81e36c50366389c118a7317b5877f603cfa2a0`) on 2026-11-22 UTC: Section 2.1 (pp. 467-468, invocation and response events, process and object subhistories `H | P` and `H | x`, sequential and well-formed histories, equivalence, `complete(H)`, prefix-closed sequential specifications, and total operations); Section 2.2 (pp. 468-469, irreflexive real-time precedence `<_H` and conditions L1-L2 defining linearizability via response-append extensions `H'`; note that the literal printed L2 restricts `<_H` to operations completed in `H`, which fails locality and nonblocking until amended to operations completed in `H'` as shown in [selaherlihypetrank2021](#selaherlihypetrank2021)); Section 3.1 (pp. 470-471, Theorem 1 proving locality: `H` is linearizable iff `H | x` is linearizable for every object `x`); Section 3.2 (pp. 471-472, Theorem 2 proving the nonblocking property for pending invocations of total operations); and Section 3.3 (p. 472, sequential consistency, proof that linearizability implies sequential consistency, single-queue history `H_7` separating sequential consistency from linearizability, and two-queue history `H_8` showing sequential consistency is not local).
Cited by [ConcurrentObjects/Linearizability.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/Linearizability.lean) (`IsLinearizable`, where `History.prec H e_0 e_1` sees invocations pending in `H` and `IsLinearizable` applies it to operations completed in the extension `H'` as justified by `History.prec_append_resp_iff`, matching Definition 4.1 and Theorems 5.1-5.2 of [selaherlihypetrank2021](#selaherlihypetrank2021); `IsSequentiallyConsistent`, extending Section 3.3's p. 472 complete-history formulation to incomplete histories via `History.IsExtension` and `History.complete` in parallel with `IsLinearizable` and coinciding on complete histories such as `H_7` and `H_8`; `IsLinearizable.isSequentiallyConsistent`; `isLinearizable_iff_forall_obj`; `exists_linearizable_append_resp_of_total`; and original atomic-register counterparts of `H_7` and `H_8` in `exists_sequentiallyConsistent_not_linearizable` and `exists_obj_sequentiallyConsistent_not_global`).

<a id="hhk17"></a>
## hhk17

Dennis Hofheinz, Kathrin Hövelmanns, Eike Kiltz.
“A Modular Analysis of the Fujisaki–Okamoto Transformation.”
*Theory of Cryptography (TCC 2017)*, LNCS 10677, 341–371, 2017. https://doi.org/10.1007/978-3-319-70500-2_12 ; full version https://eprint.iacr.org/2017/604 (dated 2 November 2021).
The pinned copy is the Internet Archive's https://web.archive.org/web/20250427001626id_/https://eprint.iacr.org/2017/604.pdf (38 pages; printed page = PDF page; SHA-256 `056ef846e047ec1e7f69629c839e9160312338d330d27f292e40d595a9c73fff`, first recorded in [#5675](https://github.com/cslib-community/cslib-frontier/pull/5675); its SHA-1 matches the archive's digest for that capture).
Checked against the 2 November 2021 ePrint PDF (§2.1 correctness/spreadness and Def. 2.2 / Fig. 4 IND-CPA; §3.1 Fig. 5 transform `T`; §3.2.1 Fig. 9 `FO^⊥`; §3.2.2 Fig. 12 `FO-notbot`), with model adaptations (`ExplicitCoinPKE`/`Scheme` fixed types and arbitrary `sampleCoins`/`sampleMsg`/`sampleKey` samplers, two-stage IND-CPA `cpaAdvantage` via `PKE.cpaExperiment` on `ExplicitCoinPKE.toPKE`, with the single-stage fixed-message `indCpaGame`/`indCpaAdvantage` kept only for the spread-necessity example) documented in the Lean modules.
The implicit-rejection key and ordinary key both use `H : M × CT → K` as in Figure 12.

<a id="hhrvw20"></a>
## hhrvw20

Iftach Haitner, Thomas Holenstein, Omer Reingold, Salil Vadhan, Hoeteck Wee.
“Inaccessible Entropy II: IE Functions and Universal One-Way Hashing.”
*Theory of Computing* 16(8), 1–55, 2020. https://doi.org/10.4086/toc.2020.v016a008 . Open-access article PDF inspected (Section 3, Definitions 3.1, 3.3, 3.9, pp. 11–15, including canonical collision-finder sanitization and adversary-dependent accessible preimage sets; Section 4.2, Theorem 4.5 and Claims 4.6–4.8, pp. 21–25, with polynomial light-image threshold and `d * Real.logb 2 n / n` entropy gap against uniform strict-PPT adversaries; and Section 5.1, Theorem 5.1, Lemmas 5.3–5.7, and Section 5.1.5 STEPS 1–5, pp. 25–32, proved from Definition 3.9's adversary-dependent hypothesis).

<a id="hierholzer73"></a>
## hierholzer73

Carl Hierholzer.
“Ueber die Möglichkeit, einen Linienzug ohne Wiederholung und ohne Unterbrechung zu umfahren.”
*Mathematische Annalen* 6, 30–32, 1873. https://doi.org/10.1007/BF01442866 . Cited for the sufficiency of even degrees and the splicing construction; the attribution follows secondary sources, and the German original was not checked.

<a id="hill99"></a>
## hill99

Johan Håstad, Russell Impagliazzo, Leonid A. Levin, Michael Luby.
“A Pseudorandom Generator from Any One-Way Function.”
*SIAM Journal on Computing* 28(4), 1364–1396, 1999. https://doi.org/10.1137/S0097539793244708 . Publisher abstract checked; full article not independently audited.

<a id="hirahara2018"></a>
## hirahara2018

Shuichi Hirahara.
*Non-Black-Box Worst-Case to Average-Case Reductions within NP*.
FOCS 2018, 247–258. https://doi.org/10.1109/FOCS.2018.00032 . Full version ECCC TR18-138.
Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.
The Lean module documentation follows its Definition 9 (`MINKT`) and Definition 11 (`GapMINKT`) with ECCC numbering.

<a id="hirahara2022"></a>
## hirahara2022

Shuichi Hirahara.
*NP-Hardness of Learning Programs and Partial MCSP*.
FOCS 2022, 968–979. https://doi.org/10.1109/FOCS54457.2022.00095 . Full version ECCC TR22-119.
Checked against the FOCS proceedings text on 2026-11-11: the partial-string problems `MKTP*` and `MINKT*` (Section I, p. 971), consistency with a partial string (footnote 5, p. 971), the KT-style time measure of Theorem I.2 (footnote 6, p. 971), Theorem I.2 (p. 971; its "In particular" clause, NP-hardness of Partial MCSP and of `MINKT*` under randomized reductions, is `PartialMCSP.rpHard` and `MINKTStar.rpHard`), and the account of Ko's `MINKT` and relativization barrier (abstract, p. 968; Section I, p. 970).
The ECCC numbering was not checked.

<a id="hirvonensuomela2020"></a>
## hirvonensuomela2020

Juho Hirvonen and Jukka Suomela.
*Distributed Algorithms 2020*, online textbook, Aalto University, https://jukkasuomela.fi/da2020/da2020.pdf . Checked on 2026-11-22 UTC against the PDF edition dated 9 November 2025 (141 pages, SHA-256 `8ce6b0498c5586d51381fb1c99479e5fc3e695757853278156c1e63b5a016fdf`): Chapter 3 (§3.2–§3.3, printed pp. 39–45, port-numbering `PN` model), Chapter 4 (§4.5, Lemma 4.1, printed p. 69 / PDF p. 79: one-round greedy local-maximum color reduction reducing `c > Δ + 1` colors to `c - 1` colors on graphs of maximum degree `Δ`), and Chapter 7 (§7.1–§7.3, printed pp. 115–121 / PDF pp. 125–131, Definition of covering maps on port-numbered networks with `C_6 -> C_3` and `K_{3,3} -> K_3` examples on printed pp. 115–117, Theorem 7.1 on printed pp. 118–119 proving deterministic `PN` state invariance along covering maps, and cycle/coloring impossibility examples in §7.3 on printed pp. 119–121).
Cited for [LocalGraph/Basic.lean](../CslibFrontier/Computability/Distributed/LocalGraph/Basic.lean) (`PortNumbering`, `GraphCovering`, `PortCovering`, `PortProtocol.state_eq_of_portCovering`) and [LocalGraph/Coloring.lean](../CslibFrontier/Computability/Distributed/LocalGraph/Coloring.lean) (`greedyStep`, `greedyColorReduction_run`, steps toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505)).

<a id="hk21"></a>
## hk21

David Heath, Vladimir Kolesnikov.
“One Hot Garbling.”
*ACM CCS 2021*, 574–593. https://doi.org/10.1145/3460120.3484764 . Full version: Cryptology ePrint Archive, Paper 2022/798, https://eprint.iacr.org/2022/798 . The ePrint full text was read in this pass for §4.1 (p. 10): the binary-to-one-hot conversion expands a GGM tree, sending two encrypted values per level and a final correction, `2(n − 1) + 1` ciphertexts in all.
Cited as the origin of one-hot garbling.
The library's single-ciphertext construction is the one of [heath24](#heath24), not this one, and its obliviousness reduction is original rather than a transcription of this paper's proof.

<a id="hkn24"></a>
## hkn24

David Heath, Vladimir Kolesnikov, Lucien K. L. Ng.
“Garbled Circuit Lookup Tables with Logarithmic Number of Ciphertexts.”
*EUROCRYPT 2024*.
Full version: Cryptology ePrint Archive, Paper 2024/369, https://eprint.iacr.org/2024/369 . The ePrint full text was read in this pass for Definition 1 (circular correlation robustness, following Zahur–Rosulek–Evans, with `Δ ∈ 1{0,1}^{κ−1}`), Figure 1 (p. 10, the interface of one-hot garbling, credited to [hk21](#hk21); it states `(2n − 1)κ` bits, the count of [hk21](#hk21), whereas Theorem 1 uses the `(n − 1)κ` of [heath24](#heath24)), Lemma 1 and the display after it (`T(f)ᵀ · H(x) = f(x)` and its garbled form), Theorem 1 (p. 19, cost `2ⁿm + (n − 1)κ + nmκ` per gate, matching the cost breakdown on p. 20) and the proof of Theorem 3 (obliviousness; the `n − 1` one-hot rows are simulated by uniform strings, as shown in [hk21](#hk21)).

<a id="hmu06"></a>
## hmu06

John E. Hopcroft, Rajeev Motwani and Jeffrey D. Ullman.
*Introduction to Automata Theory, Languages, and Computation*, third edition.
Addison-Wesley, 2006.
ISBN 0-321-45536-3.
Cited for Section 7.4.4 ("Testing Membership in a CFL"), the CYK algorithm for grammars in Chomsky normal form.
The section number and title were checked against secondary course material, not the printed book.

<a id="hoeffding63"></a>
## hoeffding63

Wassily Hoeffding.
"Probability Inequalities for Sums of Bounded Random Variables."
*Journal of the American Statistical Association* 58(301), 13–30, March 1963. https://doi.org/10.1080/01621459.1963.10500830 . Checked against the JSTOR PDF (`hoefding.pdf`, SHA-256 `3021bcc097ef23a99a84d0eef8dcce2fd835c71df79a105727d3e03f8f0b8930`, 19 pages, printed pp. 13–30) on 2026-11-22: §2 Theorem 2, eq. (2.6) on printed p. 16 (PDF p. 5, `Pr{X̄ - μ ≥ t} ≤ exp (-2 n² t² / ∑_{i=1}^n (b_i - a_i)²)` for `a_i ≤ X_i ≤ b_i` and `t > 0`), the martingale extension on printed p. 18, eq. (2.18) (PDF p. 7, noting Theorems 1 and 2 remain true when `S'_m = S_m - E S_m` is a martingale), and §4 Lemma 1 and eqs. (4.11)–(4.17) on printed pp. 21–23 (PDF pp. 10–12, centered MGF bound `E e^{h(X_i - μ_i)} ≤ e^{h² (b_i - a_i)² / 8}` and optimization at `h = 4 n t / ∑ (b_i - a_i)²`).

<a id="holevo1973"></a>
## holevo1973

Alexander S. Holevo.
"Bounds for the Quantity of Information Transmitted by a Quantum Communication Channel."
*Problemy Peredachi Informatsii* 9(3), 3–11, 1973 (English translation in *Problems of Information Transmission* 9(3), 177–183, 1973, bibliography key `Holevo1973`).
Bibliographic metadata checked via secondary records on 2026-11-24; neither the Russian original nor the 1973 translation scan was directly inspected, so no internal page or equation numbers in `Holevo1973` are claimed.
Cited in [Holevo.lean](../CslibFrontier/Foundations/Quantum/DensityMatrix/Holevo.lean) as the origin of Holevo information and Holevo's bound, whose mathematical statement and proof were checked directly against [watrous2018](#watrous2018), Chapter 5, Theorem 5.49.

<a id="holenstein05"></a>
## holenstein05

Thomas Holenstein.
“Key Agreement from Weak Bit Agreement.”
*Proceedings of the 37th Annual ACM Symposium on Theory of Computing (STOC 2005)*.
Author PDF inspected: https://crypto.ethz.ch/publications/files/Holens05.pdf (Section 2 on Impagliazzo's hard-core lemma; Section 2.1, Lemma 2.1; Section 2.1.1, Lemma 2.2 on choosing a set according to a measure).

<a id="holenstein06"></a>
## holenstein06

Thomas Holenstein.
“Pseudorandom Generators from One-Way Functions: A Simple Construction for Any Hardness.”
*TCC 2006*.
Author PDF: https://crypto.ethz.ch/publications/files/Holens06.pdf . Definitions and construction overview consulted.

<a id="holenstein09"></a>
## holenstein09

Thomas Holenstein.
“Parallel Repetition: Simplifications and the No-Signaling Case.”
*Theory of Computing* 5(8), 141–172, 2009. https://doi.org/10.4086/toc.2009.v005a008 . Journal PDF inspected (Definition 2.4 and Theorem 2.5, p. 146; Definition 5.1 and Lemma 5.2, p. 151; Figure 1, the correlated-sampling protocol and the proof of Lemma 5.2, pp. 152–153; Lemma 5.4 and (5.5), p. 153; Claims 6.2 and 6.3, p. 154; Lemma 6.4 and (6.3)–(6.7) of its proof, p. 155; (6.8)–(6.16), p. 156; the first stage of the embedding, from (6.15) and (6.16) by Corollary 5.3, (6.17)–(6.19) and the second stage, and Lemma 6.5, (6.20) and its proof, p. 157; Lemma 7.1, p. 158; the proof of Theorem 2.5, (7.6) and (7.7), p. 159).

<a id="hooverpersianoyeo26"></a>
## hooverpersianoyeo26

Alexander Hoover, Giuseppe Persiano and Kevin Yeo.
"Lower Bounds for PIR with Preprocessing from Blackbox Cryptography."
FOCS 2026 (the arXiv listing says "To appear in FOCS 2026").
Full version: arXiv:2607.06451v3, 10 September 2026, https://arxiv.org/abs/2607.06451v3 ; also Cryptology ePrint Archive, Paper 2026/1384, https://eprint.iacr.org/2026/1384 . Locators are the printed page numbers of arXiv:2607.06451v3, checked against its PDF on 2026-11-15.
Definition 6.1, pp. 50–51: `Query` is a two-party protocol with client messages `τu` and server messages `τd`; `ε`-correctness is a success probability ("Pr[Query(st, Q; D, R) = (D[Q]; ⊥) : R ←$ {0,1}^r; (st; ⊥ | τoff) ←$ Setup(1^λ; 1^λ, D, R)] ≥ ε", p. 50, where the sampling of `R` and the `Setup` run is written under `Pr`); `δ`-privacy and `γ`-data privacy are defined against efficient adversaries, and "perfectly correct, private, and data private" means `ε = 1`, `δ = 0` and `γ = 0` (p. 51).
Theorem 6.2 and its proof, p. 52: "Let s < k ≤ n and ε > 2^{s−k}.
In the random oracle model, there does not exist a k-batch SPIR scheme with s-bit client storage that is ε-correct, perfectly private, and perfectly data private."
The first version, arXiv:2607.06451v1, states the threshold as "ε > 1 − 2^{s−k}" (p. 46).
Section 6.3, pp. 54–55 (the first toy, under the heading "n-bit client storage, O(k log n)-bit communication", p. 54).
The library does not formalize Theorem 6.2.
It proves an original information-theoretic bound in a restricted model (plain model, one online round, deterministic online client, perfect notions as identical view laws) by the counting argument in the proof of Theorem 6.2 (`Scheme.correct_le_card_div_two_pow`; `Scheme.correct_le_two_pow_sub` gives `ε ≤ 2 ^ (s - k)`, matching the v3 threshold; `Scheme.batchSPIR_limitation` uses the v1 threshold; all with a `2 ≤ n` guard that the zero-storage scheme at `n = k = 1, s = 0` shows is needed), using the transcript-independence step of that proof (`Scheme.eval_onlineTranscript_eq`).
It also has an online-randomized variant with an explicit `Fintype.card Ω` factor (`RandomizedScheme.correct_le_card_mul_card_div_two_pow`, not in the source), the first Section 6.3 toy with an ideal setup (`toyScheme`: `2 ^ n * n!` client states, perfect correctness and data privacy, privacy on injective batches only, and the repeated-query counterexample for `2 ≤ k` and `2 ≤ n`), and a coordinate-wise variant `parallelToyScheme`, not in the source, which shows the hypotheses are jointly satisfiable for every `n` and `k`.
Not formalized: Theorem 6.2 itself, Lemma 6.3, Theorem 6.4, the PRF inner-product toy and Sections 6.4–6.5 (Theorem 6.5).

<a id="howardmalkhispiegelman17"></a>
## howardmalkhispiegelman17

Heidi Howard, Dahlia Malkhi and Alexander Spiegelman.
"Flexible Paxos: Quorum Intersection Revisited."
OPODIS 2016, LIPIcs 70, 25:1–25:14, published 2017. https://doi.org/10.4230/LIPIcs.OPODIS.2016.25 . Published PDF inspected on 2026-11-23: §3, pp. 25:4–25:5 (cross-phase quorum intersection and phase-specific availability); §4.2, p. 25:6 (cardinality threshold `q₁ + q₂ > N`); §4.3, p. 25:7 (row/column grid quorums); and §5, pp. 25:8–25:9 (Theorems 1–2 and Eq. (3), agreement via preservation of earlier decisions).
`Paxos/Quorums.lean` gives the two-family interface and original finite-set formulations of the exact threshold and asymmetric failure-family availability conditions.
`Paxos/Basic.lean` and `Paxos/Liveness.lean` use this interface in the existing crash-stop operational kernel: agreement, phase-2 progress after a proposal, and full progress in a cohort containing both kinds of quorum.
These are crash-stop steps, not the persistent-storage crash-recovery or Multi-Paxos endpoints; those remain tracked in [#7207](https://github.com/cslib-community/cslib-frontier/issues/7207).
The static families do not implement §7's dynamic quorum announcements.

<a id="howson1972"></a>
## howson1972

Joseph T. Howson, Jr. "Equilibria of Polymatrix Games."
*Management Science* 18(5), 312–318, 1972. https://doi.org/10.1287/mnsc.18.5.312 . Bibliographic metadata checked from `references.bib` (`Howson1972`) and DOI records; the *Management Science* journal full text was not inspected firsthand, and no internal theorem, equation, or page locators are cited.
Cited alongside [Janovskaja 1968](#janovskaja1968) by [Polymatrix/Basic.lean](../CslibFrontier/GameTheory/Polymatrix/Basic.lean) for the multiplayer polymatrix game model and its pairwise bilinear mixed-strategy equilibrium characterization.

<a id="hoyerleespalek07"></a>
## hoyerleespalek07

Peter Høyer, Troy Lee and Robert Špalek.
"Negative weights make adversaries stronger."
*Proceedings of the 39th Annual ACM Symposium on Theory of Computing (STOC 2007)*, 526–535, 2007. https://doi.org/10.1145/1250790.1250867 ; open version arXiv:quant-ph/0611054v2 (24 April 2007), https://arxiv.org/abs/quant-ph/0611054 . Checked in arXiv:quant-ph/0611054v2 on 2026-11-11: Section 1.1 Definitions 1–2 and Theorems 1–2 (`ADV` and `ADV±`, with the Boolean bound `(1 - 2√(ε(1-ε))) ADV±(f) ≤ 2T` matching Theorem 2, and the arbitrary-output bound strengthened to `1 - 2√(ε(1-ε)) - ε` vs. the weaker `- 2ε` form stated there), Section 7.1 Theorem 20 (Ambainis's 4-bit function), and Section 7.2 Theorem 21 (the 6-bit Hamming-weight-3 partial function separating `ADV ≤ 3` from `ADV± ≥ 2 + 3√5/5`, and its `(3/5, -1/5, 1/5)` specialization giving `16/5`).

<a id="hoza21"></a>
## hoza21

William M. Hoza.
*Better Pseudodistributions and Derandomization for Space-Bounded Computation*.
APPROX/RANDOM 2021, LIPIcs 207, 28:1–28:23, 2021. https://doi.org/10.4230/LIPIcs.APPROX/RANDOM.2021.28 . Appendix A (Lemma A.2 and the proof of Theorem A.3) was checked against the LIPIcs text on 2026-11-08.

<a id="hppy25"></a>
## hppy25

Alexander Hoover, Sarvar Patel, Giuseppe Persiano and Kevin Yeo.
"Plinko: Single-Server PIR with Efficient Updates via Invertible PRFs."
*Advances in Cryptology – EUROCRYPT 2025, Part VI*, Lecture Notes in Computer Science, 3–33, Springer, 2025. https://doi.org/10.1007/978-3-031-91095-1_1 ; full version: Cryptology ePrint Archive, Paper 2024/318, https://eprint.iacr.org/2024/318 . Checked against the full ePrint version on 2026-11-14 and rechecked on 2026-11-15: Section 3 Definition 3.1 (pp. 9–10, PRF), Section 4 Definition 4.1 (p. 10, invertible PRF), Section 4.2 Theorem 4.4 and Corollary 4.5 (pp. 12–13, permutation-and-sampler composition), Section 5.1 Definitions 5.1–5.2 and Figure 5 (pp. 19–20, offline-online and updateable PIR), Section 5.2 Theorem 5.3 and the Plinko construction, promotion, caching, update, correctness and privacy paragraphs (pp. 20–23), and Appendix A (p. 30) with Figure 7 (p. 31, normative pseudocode `HintInit`, `Query`, `Answer`, `Recon`, `GetHint`, `UpdateDB`, `UpdateHint`).
`CslibFrontier.Crypto.Primitives.PRF.Invertible` formalizes `InvertiblePRF`, exact inversion correctness (`IsCorrectKey`, `IsCorrect`, `IsCorrectOnGen`), `idealInvertiblePRF`, and the inversion correctness of `compose` / `composePerm` (Theorem 4.4 / Corollary 4.5).
`CslibFrontier.Crypto.Protocols.PIR.Preprocessing.Plinko` formalizes `plinkoScheme` on `Fin c × Fin w` with `nReg + nBackup` hint slots (`ActiveHint`, `BackupHint`, `PlinkoState`), algorithmic equivalence of `getHint` via `iF.inv` and `getHintScan` (both return a `MatchedHint` record), single-pass entry streaming (`initPlinkoState`, `streamEntry`, `streamPreprocess`, `foldr_streamEntry_univ`), conditional multi-query correctness (`PlinkoState.Valid`, `CanAnswer`, `CanAnswerSeq`, `isCorrectFrom_plinkoScheme_of_canAnswerSeq`, `valid_of_mem_support_preprocess`), the fact that the query map sends a uniform hint conditioned on containing `x` to `plinkoSim` (`eval_buildQuery_conditioned_eq_plinkoSim`), adaptive multi-query perfect privacy of the idealized stand-in `plinkoHybridScheme`, which has no iPRF, keys or hint table, keeps `db` in its state and draws a fresh conditioned hint per query (`isPerfectlyPrivateWith_plinkoHybridScheme`, `privacyAdvantage_plinkoHybridScheme_eq_zero`), and single/batch database and hint updates driven by `UpdateSummary` records (`updateDB`, `updateHint`, `updateState`, `valid_updateHint`, `valid_updateState`).
The bidirectional iPRF security proof of Theorem 4.4, PMNS (Section 4.1 Definitions 4.2–4.3, Figure 4, Lemma 4.6, Theorem 4.7), the Chernoff hint-load bound and Theorem 5.3 asymptotic bounds, `CanAnswerSeq` failure probability, amortized re-streaming, Appendix B Plinko-Piano, `B`-bit entries, FHE offline preprocessing, and exact multi-query privacy of the full `plinkoScheme` are not formalized.
Modelling choices: `getHint` takes the smallest matching candidate slot where Figure 7 scans them in random order, and a cached query sends a dummy simulator message where Figure 7 queries a fresh random index.
The bibliographic record (authors, title, Part VI, pages, DOI) was checked against the Crossref records for the chapter and the volume on 2026-11-15; Crossref does not list the LNCS volume number, so it is omitted.

<a id="hueffner2009"></a>
## hueffner2009

Falk Hüffner.
"Algorithm Engineering for Optimal Graph Bipartization."
*Journal of Graph Algorithms and Applications* 13(2), 77–98, 2009. https://doi.org/10.7155/jgaa.00177 . Journal PDF inspected on 2026-11-08 (https://jgaa.info/index.php/jgaa/article/download/paper177/2776): Section 3, Lemma 2 (p. 84; the disjoint-compression characterization by valid colourings and vertex cuts, after subdividing the edges at the old solution), the Compress-OCC routine (p. 85), and the running-time paragraph with Theorem 1 (p. 86).
There Hüffner records that Reed, Smith and Vetta state `O(4^k · kmn)`, and shows that assigning each vertex of the old solution one of three roles (deleted, or one of two colourings of its neighbours) gives `3^k` minimum vertex cut problems and `O(3^k · kmn)` (Theorem 1).
[OddCycleTransversal](../CslibFrontier/Algorithms/Lean/IterativeCompression/OddCycleTransversal.lean) credits the `3^k` count to this theorem; the improvement to `O(3^k · mn)` (Theorem 2, p. 88) is not formalized.

<a id="hulsingkudinov22"></a>
## hulsingkudinov22

Andreas Hülsing and Mikhail Kudinov.
*Recovering the Tight Security Proof of SPHINCS+*.
Cryptology ePrint Archive, Paper 2022/346, 2022. https://eprint.iacr.org/2022/346 . Bibliographic metadata taken from `references.bib`.
Locator: Theorem 3 and Equations (5)--(6), printed pp. 20--21.
The original author recorded this locator as checked on 2026-11-14 against the ePrint paper, version dated 19 August 2022, with the note that these statements separate a `PRF_msg` term and an `H_msg` (ITSR) term in the EU-CMA bound, and an agent source review on #5573 of the same day ([comment](https://github.com/cslib-community/cslib-frontier/issues/5573#issuecomment-6881580912)) reports that the citation matches that theorem, including the separate PRF and ITSR terms.
The locator was not re-read on 2026-11-24, when the ePrint server refused automated requests from the agents then working on the citing module, and it has not been confirmed by a reviewer outside the authoring fleet.
[SLHDSA/MessageCalls.lean](../CslibFrontier/Crypto/Primitives/SLHDSA/MessageCalls.lean) cites the paper only as the source of the security properties that the SPHINCS+ proof requires of `PRF_msg` and `H_msg`.
The module implements the FIPS 205 executable calls and states or proves none of those properties.

<a id="iknp03"></a>
## iknp03

Yuval Ishai, Joe Kilian, Kobbi Nissim and Erez Petrank.
"Extending Oblivious Transfers Efficiently."
*Advances in Cryptology – CRYPTO 2003*, Lecture Notes in Computer Science 2729, 145–161, Springer, 2003. https://doi.org/10.1007/978-3-540-45146-4_9 . Inspected on 2026-11-15 in the IACR archive copy of the CRYPTO 2003 version (https://www.iacr.org/archive/crypto2003/27290145/27290145.pdf, read through the Wayback Machine snapshot of 2026-08-21; 17 pages with the LNCS page numbers 145–161; SHA-256 `b1336e811da8a24c4c0fc66904dda4c61aa0283e7d146638c66c8917856ff9ae`): Theorem 2 (p. 147); §2.1 on the random oracle, hybrid-model reductions and black-box reductions (pp. 149–150); §2.2, the functionality `ot^m_ℓ` (p. 151); Fig. 1, the protocol with a semi-honest receiver (p. 152); §3.1, the perfect simulator for a malicious sender and the statistical simulator for a semi-honest receiver in the random-oracle model, with Lemma 1 (pp. 152–154); §5, Definition 1 (correlation robustness of an efficiently computable `h : {0,1}* → {0,1}`) and the discussion that replaces the random oracle of Fig. 1 by a correlation robust `h` for bit transfers, hashing `u` in place of `(j, u)`, with footnote 10 and Theorem 3 (p. 157); and Appendix A, the stand-alone definition of secure two-party computation against a non-adaptive adversary (p. 160).

<a id="ilango2020focs"></a>
## ilango2020focs

Rahul Ilango.
*Constant Depth Formula and Partial Function Versions of MCSP are Hard*.
FOCS 2020, 424–433. https://doi.org/10.1109/FOCS46700.2020.00047 . Full version ECCC TR20-183.
Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.

<a id="ilo2020"></a>
## ilo2020

Rahul Ilango, Bruno Loff and Igor C. Oliveira.
*NP-Hardness of Circuit Minimization for Multi-Output Functions*. 35th Computational Complexity Conference (CCC 2020), LIPIcs 169, 22:1–22:36. https://doi.org/10.4230/LIPIcs.CCC.2020.22 . Inspected the LIPIcs PDF directly: Theorem 4 (p. 22:5), the canonical DNF (pp. 22:19–22:20), Section 4.2 (pp. 22:20–22:21), Proposition 14 and the consequence `∆ = CC(T • g) − CC(g)` (pp. 22:21–22:22), Lemma 15 (p. 22:22) and Lemma 16 (pp. 22:22–22:23).

<a id="ilps22"></a>
## ilps22

Russell Impagliazzo, Rex Lei, Toniann Pitassi, Jessica Sorrell.
*Reproducibility in Learning*.
*Proceedings of the 54th Annual ACM SIGACT Symposium on Theory of Computing (STOC 2022)*, 818–831, 2022. https://doi.org/10.1145/3519935.3519973 ; arXiv:2201.08430.
Bibliographic metadata only (`references.bib`); primary text uninspected; no numbered paper theorems are claimed.
Cited for the definitions of shared-seed `ρ`-replicable sample algorithms, randomized threshold/grid rounding, confidence amplification, finite-domain amplification (`amplifyFinite`), general-domain collision-threshold amplification (`amplifyReplicability`), and replicable bounded-mean and coin-bias estimation formalized (alongside `Cslib.ProbComp` program wrappers and `MeasureTheory.volume` variants) in `CslibFrontier/MachineLearning/Replicable/`.

<a id="immerman1988"></a>
## immerman1988

Neil Immerman.
“Nondeterministic Space Is Closed under Complementation.”
*SIAM Journal on Computing* 17(5), 935–938 (1988).
DOI: https://doi.org/10.1137/0217058.
Author copy inspected: https://people.cs.umass.edu/~immerman/pub/space.pdf (Theorem 1; inspected 2026-11-01).

<a id="impagliazzo01"></a>
## impagliazzo01

Russell Impagliazzo and Ramamohan Paturi.
*On the Complexity of k-SAT*.
Journal of Computer and System Sciences 62(2), 367–375, 2001.
DOI: [10.1006/jcss.2000.1727](https://doi.org/10.1006/jcss.2000.1727).
[Author-hosted copy](https://cseweb.ucsd.edu/~paturi/myPapers/pubs/ImpagliazzoPaturi_2001_jcss.pdf).
Publisher metadata and abstract checked 2026-11-02; cited for the historical exponent-based hypothesis, not for the 2026 result.

<a id="impagliazzo95"></a>
## impagliazzo95

Russell Impagliazzo.
“Hard-Core Distributions for Somewhat Hard Problems.”
*Proceedings of the 36th Annual Symposium on Foundations of Computer Science (FOCS 1995)*, 538–545.
DOI: [10.1109/SFCS.1995.492584](https://doi.org/10.1109/SFCS.1995.492584).
Bibliographic metadata only; the paper itself was not inspected, and its statement is cited as recalled in [Holenstein 2005](#holenstein05), Section 2.

<a id="impagliazzojaiswalkabanetswigderson10"></a>
## impagliazzojaiswalkabanetswigderson10

Russell Impagliazzo, Ragesh Jaiswal, Valentine Kabanets and Avi Wigderson.
*Uniform Direct Product Theorems: Simplified, Optimized, and Derandomized*.
SIAM Journal on Computing 39(4), 1637–1665, 2010.
DOI: [10.1137/080734030](https://doi.org/10.1137/080734030) (as reported by search; not resolved).
The authors' preprint dated 2009-10-19 (https://www.math.ias.edu/~avi/PUBLICATIONS/ImpagliazzoJaKaWi2010.pdf) was inspected on 2026-11-11: Theorem 1.2 (the decoder that CIKK cite as their Theorem 4.1), Algorithms 1–2, Theorem 3.2 and Lemmas 2.11–2.14 and 3.8–3.12.
Locators follow the preprint; the journal numbering is unchecked.

<a id="impagliazzolevin90"></a>
## impagliazzolevin90

Russell Impagliazzo and Leonid A. Levin.
"No Better Ways to Generate Hard NP Instances than Picking Uniformly at Random."
*Proceedings of the 31st Annual Symposium on Foundations of Computer Science (FOCS 1990)*, 812–821. https://doi.org/10.1109/FSCS.1990.89604 . Bibliographic metadata only (`references.bib`); the paper was not inspected and no numbered result is claimed.
Cited with [Blum, Furst, Kearns and Lipton](#blumfurstkearnslipton93) by [CryptoHardness/Inversion.lean](../CslibFrontier/MachineLearning/UniformLearning/CryptoHardness/Inversion.lean) and [CryptoHardness/OneWayInversion.lean](../CslibFrontier/MachineLearning/UniformLearning/CryptoHardness/OneWayInversion.lean).

<a id="impagliazzopudlaksgall99"></a>
## impagliazzopudlaksgall99

Russell Impagliazzo, Pavel Pudlák and Jiří Sgall.
“Lower Bounds for the Polynomial Calculus and the Gröbner Basis Algorithm.”
*Computational Complexity* 8(2), 127–144, 1999.
DOI: [10.1007/s000370050024](https://doi.org/10.1007/s000370050024).
Bibliographic record from `references.bib` (`ImpagliazzoPudlakSgall1999`); the paper text was not inspected (the `algFPHP` axiom presentation follows [#3569](https://github.com/cslib-community/cslib-frontier/issues/3569)).

<a id="impagliazzowigderson97"></a>
## impagliazzowigderson97

Russell Impagliazzo and Avi Wigderson.
*P = BPP if E Requires Exponential Circuits: Derandomizing the XOR Lemma*.
Proceedings of the 29th Annual ACM Symposium on Theory of Computing, 220–229, 1997.
DOI: [10.1145/258533.258590](https://doi.org/10.1145/258533.258590).
ACM metadata checked by the coordinated source pass on 2026-11-02; no complete literature proof audit is asserted.

<a id="indykmotwani98"></a>
## indykmotwani98

Piotr Indyk, Rajeev Motwani.
“Approximate Nearest Neighbors: Towards Removing the Curse of Dimensionality.”
*Proceedings of the 30th Annual ACM Symposium on Theory of Computing* (STOC 1998), 604–613. https://doi.org/10.1145/276698.276876 . DOI and metadata as reported by search indexes; neither the DOI nor the full text was resolved in this pass.
Cited for the definition of locality-sensitive families, for bit sampling under the Hamming distance, and for the LSH near-neighbour structure with `n^ρ` query cost.
[andoniindyk08](#andoniindyk08), Section 2.4, p. 119, credits this paper, together with Gionis–Indyk–Motwani (VLDB 1999), with the rule that stops the query after `3L` candidates; this locator was not checked against the STOC text.

<a id="irani91"></a>
## irani91

Sandy Irani.
"Two Results on the List Update Problem."
*Information Processing Letters* 38(6), 301–306, 1991. https://doi.org/10.1016/0020-0190(91)90086-W . Crossref metadata checked on 2026-11-07; the full text was not inspected in this pass.
The manual uses it only as the place where secondary sources say the deterministic `2n/(n+1)` list-update lower bound of Karp and Raghavan is reported.

<a id="jainmahdian07"></a>
## jainmahdian07

Kamal Jain and Mohammad Mahdian.
"Cost Sharing."
Chapter 15 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 385–410. https://doi.org/10.1017/CBO9780511800481.017 . Checked firsthand on 2026-11-23 against the chapter text (pp. 385–410): Section 15.1 (pp. 385–386: TU cost-sharing games with `c(∅) = 0`, Definition 15.1 cooperative facility location game, and Example 15.2), Section 15.2 (pp. 386–391: Definition 15.3 core, Example 15.4, LPs `(15.1)`–`(15.2)`, Definition 15.5 balanced weights, Theorem 15.6 Bondareva–Shapley theorem, Definition 15.7 `γ`-core with `γ · c(A) ≤ ∑ α_j ≤ c(A)`, Theorem 15.8 `γ`-Bondareva–Shapley theorem, Corollary 15.9 LP integrality gap, and Proposition 15.10 dual facility-location LP `(15.4)`), Section 15.3 (pp. 391–394: NPT, VP, CS, `γ`-budget balance, group-strategyproofness, Definition 15.12 cost-sharing scheme, Definition 15.13 cross-monotonicity, Proposition 15.14, Figure 15.2 Moulin's mechanism `M_ξ`, Proposition 15.15 largest willing coalition and pruning-order independence, and Theorem 15.16 Moulin 1999), Section 15.4.1 (pp. 396–397: Definition 15.17 submodular cost-sharing game, Lemma 15.18 tight-set uncrossing, Corollary 15.19 maximal tight set, Figure 15.3 `SubmodularCostShare`, and Theorem 15.20), Section 15.6 (pp. 402–405: Section 15.6.1 Shapley value formula, Example 15.24 `(23/6, 11/6, 7/3)` outside the core of Example 15.2, Definition 15.25 Anonymity/Dummy/Additivity where Efficiency is implicit and Dummy prints `S ⊂ A \ {i}` for `S ⊆ A \ {i}`, Theorem 15.26 Shapley's uniqueness theorem, Section 15.6.3 2-player bargaining, Definition 15.27 weak Pareto optimality / symmetry / scale independence / IIA combined with translation normalization to `d = (0, 0)`, and Theorem 15.28 Nash's bargaining theorem), and Section 15.8 (p. 410: Exercises 15.1 and 15.2).
Cited by `CslibFrontier/GameTheory/Cooperative/{Basic,Core,MoulinCostSharing,ShapleyValue}.lean`.

<a id="janovskaja1968"></a>
## janovskaja1968

Elena B. Janovskaja.
"Equilibrium Points in Polymatrix Games."
*Litovskii Matematicheskii Sbornik* 8(2), 381–384, 1968. https://doi.org/10.15388/LMJ.1968.20224 . Bibliographic metadata checked from `references.bib` (`Janovskaja1968`) and DOI records; the published journal full text was not inspected firsthand, and no internal theorem, equation, or page locators are cited.
Cited alongside [Howson 1972](#howson1972) by [Polymatrix/Basic.lean](../CslibFrontier/GameTheory/Polymatrix/Basic.lean) for the multiplayer polymatrix game model and its pairwise bilinear mixed-strategy equilibrium characterization.

<a id="jansonluczakrucinski2000"></a>
## jansonluczakrucinski2000

Svante Janson, Tomasz Łuczak and Andrzej Ruciński.
*Random Graphs*.
Wiley-Interscience Series in Discrete Mathematics and Optimization, Wiley, 2000. https://doi.org/10.1002/9781118032718 . Bibliographic data from secondary records of the DOI.
The chapter locator (Chapter 3, small subgraphs and the threshold `n ^ (-1 / m(H))`) was taken from secondary descriptions; the book was not inspected in this pass, and no theorem number is claimed.

<a id="jeandelvanier2020"></a>
## jeandelvanier2020

Emmanuel Jeandel and Pascal Vanier.
*The Undecidability of the Domino Problem*.
In Shigeki Akiyama and Pierre Arnoux (eds.), *Substitution and Tiling Dynamics*, Lecture Notes in Mathematics 2273, 293–357, Springer, 2020.
[Publisher record](https://doi.org/10.1007/978-3-030-57666-0_6); [authors' manuscript](https://www.lacl.fr/pvanier/rech/cirm.pdf).
Read on 2026-11-16 by the authoring Codex workers: §3.2 (beginning on manuscript p. 22), Definition 10 and Theorem 9 (p. 23), Proposition 8 (p. 24), and Figures 13–16 (pp. 25–26).
The tile set is attributed to [Ollinger](#ollinger2008) on p. 24.
The Robinson modules use [lean-wang](https://github.com/edemaine/lean-wang/tree/64268a3aaaef3eac65559352ef94f62ab9c00482) at that revision, retaining its authors and Apache-2.0 credit.
“Corrected” identifies its Figure 13 component transcription and the second thick-layer summand at `L2b` in Figure 16(c), whose southeast extension uses `R1` rather than `R3` ([plan, lines 94–98](https://github.com/edemaine/lean-wang/blob/64268a3/plan.md#L94-L98)).
Both thick-layer boundary lanes are retained.
This records lean-wang's correction, not a verified erratum to the printed figures; historical correction: locator not verified.
Full agreement with those figures is not checked in Lean.
The hierarchy modules formalize matching substitution, local recognition, parent towers, recurrence and nonempty plane tilings; they do not include Proposition 8's aperiodicity conclusion or domino undecidability.
The routing worker additionally read §3.3, pp. 26–29, on 2026-11-16: light/dark separation, obstruction signals, free-grid transmission and the two directions of seed removal.
Routing formalizes the generic conditional step, including its finite-grid/addressed-patch consumers.
Signals constructs the finite decorated scaffold, decodes arbitrary scaffold planes, and characterizes roles by clear signal edges.
Canonical certificates retain 312 selected decorated nodes from that same lean-wang revision's [ShadedSubstitutionStateWitnesses](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/ShadedSubstitutionStateWitnesses.lean).
Nodes are reindexed in source-list order; semantic seam certificates replace repeated decoding of the source tables.
Canonical patches assign nearest-border obstruction signals to matching decorated substitutions and establish that the resulting finite scaffold tiles the plane.
Carrier/BorderCertificates retains the 376-state invariant from [ShadedCarrierBorderHierarchyData](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/ShadedCarrierBorderHierarchyData.lean).
Each state records a decorated node, coordinate parities and a three-by-three border halo.
Indexed witnesses certify all sixteen child refinements, visible border observations and index-zero child configurations.
Carrier/Borders gives these certificates their recursive frame interpretation.
Carrier/Borders, Carrier/Addresses, Carrier/Corners and Realization port the pinned revision's ShadedCarrierHierarchy, ShadedCarrierBorderHierarchy, ShadedCarrierBorderGeometry, ShadedCarrierBorderIntervals, ShadedCarrierSquareGeometry, ShadedCarrierHierarchyAddressing, ShadedCarrierConcreteRoles and ShadedCarrierCornerAddressing.
Recursive owner frames identify the canonical carriers, their integer addresses satisfy wire equations, and every corner has address zero.
Thus the concrete scaffold realizes every pointed payload plane, as in ShadedCarrierCornerAddressing.lean:435–440.
The named border halo and `AddressedSquare` replace the source's raw halo lists and `SquareAddressing`; the carrier arithmetic and centered-marker induction closely follow the source.
The backward authoring worker also read Theorem 10 on manuscript p. 29 and the proof-route attribution in §3.4, pp. 29–30, plus [Robinson's primary paper](https://lipn.univ-paris13.fr/~fernique/qc/robinson.pdf), §7, printed pp. 201–205, on 2026-11-16.
The red-path and shading modules are after §3.3, Figures 17–18, manuscript pp. 24, 26–28, read directly on 2026-11-16: light red wires cross dark ones, and squares emit signals on their exterior borders.
The exact opposite-shade crossing rule (also forbidding dark–dark crossings), quarter-port connectivity, and nearest outward-facing light-boundary invariant come from lean-wang's red-graph and oriented-light modules at the same pinned revision; the discrete-height argument is not attributed to the manuscript.
These are scaffold ingredients, not Theorem 10's endpoint.
This source check is authoring evidence, not independent review.

FreeGrid proves that every decoded scaffold plane contains a light consecutive marked grid for each requested number of rows and columns.
Its canonical free-line inductions follow `coordinate_free_lines` in [CanonicalEvenFreeLines, line 417](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/CanonicalEvenFreeLines.lean#L417) and [CanonicalOddFreeLines, line 449](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/CanonicalOddFreeLines.lean#L449).
Transfer to arbitrary shades follows `freeCoordinates` in [CanonicalShadeComparison, line 284](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/CanonicalShadeComparison.lean#L284) and [CanonicalOddShadeComparison, line 361](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/CanonicalOddShadeComparison.lean#L361), sharing one comparison proof and using closed coordinate formulas instead of branch lists.
Marker transport follows [ShadedMarkedFreeGrid, line 64](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/ShadedMarkedFreeGrid.lean#L64); the arbitrary-plane assembly and gap filling follow [SparseFreeLineDecodedMarkedGrid, line 43](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/SparseFreeLineDecodedMarkedGrid.lean#L43) and [ShadedConsecutiveFreeGrid, line 220](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/ShadedConsecutiveFreeGrid.lean#L220).
The `RedPaths/Certificates` module supplies the odd-phase finite base after [CanonicalOddShadeBase.exists_boundedPath, line 22](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/CanonicalOddShadeBase.lean#L22), using the [oddNodes witnesses, line 5412](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/RedShadeGraphPathWitnesses.lean#L5412) with shared path prefixes and semantic-side certificates.

FreeGrid/Obstruction turns these grids into routed grids: the outward-facing light boundary rules out extra crossings.
It retains the signal-corridor argument and [ShadedObstructionGeometry.Geometry.crossingObstruction, line 252](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/ShadedObstructionGeometry.lean#L252), while separating the payload propagation of [ShadedPayloadCorridors.tileableFixedCornerSquare_of_consecutive, line 229](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/ShadedPayloadCorridors.lean#L229) into generic Routing.
Forcing then proves `scaffold_forces : Forces scaffold`, after [OrientedLightForward.closed104_forcesRoutedFixedCornerSquares, line 32](https://github.com/edemaine/lean-wang/blob/64268a3/LeanWang/Robinson/Closed104/OrientedLightForward.lean#L32): for every seeded payload and every combined plane tiling, there is a seeded payload square of each positive side length.
There is no extra premise about the scaffold.
The lean-wang declarations and locators above were checked against the pinned source by an authoring Codex worker on 2026-11-16; this is authoring evidence, not independent review.

Robinson/Reduction discharges both concrete obligations and proves `TilesPlane (removeSeed I) ↔ TilesQuadrant I`, with a primitive-recursive map.
Undecidable then proves Berger's theorem `¬ ComputablePred TilesPlane`, using the existing `List WangTile` instance encoding through `(top, bottom, left, right)`.
This is after Robinson's proof in the Ollinger form presented here, ported and restructured from lean-wang's Robinson/Reduction.lean at the same revision.
Its `(n, s, e, w)` record and `Fin 4 → ℕ` tiles encode the same fixed-orientation matching problem: our top/bottom/left/right correspond to n/s/w/e, reordering the last two coded components.
The assembly authoring helper checked this manuscript's §1.1, Theorem 1, p. 2 and §3.3, Theorem 10, p. 29 directly on 2026-11-16.
Berger's memoir internal locator remains unverified, as recorded under [Berger1966](#berger1966).
No aperiodicity theorem or co-RE completeness is claimed.

<a id="jnvwy2020lowindividualdegree"></a>
## jnvwy2020lowindividualdegree

Zhengfeng Ji, Anand Natarajan, Thomas Vidick, John Wright and Henry Yuen.
*Quantum soundness of the classical low individual degree test*. arXiv:2009.12982v1, 2020.
Definition 3.2 and Figure 2 give the three verifier branches, their sampling, and their degree requirements.
The formalization uses positive ambient dimension so a uniform coordinate can be sampled.
The displayed diagonal affine image is a singleton for the sampled zero direction.
The current result establishes the verifier and honest completeness.
Theorem 3.10 is tracked under [#6149](https://github.com/cslib-community/cslib-frontier/issues/6149).
[Source, pp. 12–13](https://arxiv.org/pdf/2009.12982v1#page=12)

<a id="johari2007"></a>
## johari2007

Ramesh Johari.
"The Price of Anarchy and the Design of Scalable Resource Allocation Mechanisms."
Chapter 21 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 543–568. https://doi.org/10.1017/CBO9780511800481.023 (bibliography key `Johari2007`).
Inspected the book PDF (SHA-256 `83084d9996024ca92f313c5ae55fec7b3b379f06172a4c24b62229da9c558543`) on 2026-11-24 UTC: §21.2 (pp. 545–551, Assumption 1 and Theorems 21.1, 21.2, Corollary 21.3, and Theorem 21.4 on Kelly's proportional allocation mechanism, formalized in `CslibFrontier/GameTheory/ResourceAllocation/KellyMechanism.lean`), §21.3 ("A Characterization Theorem", pp. 551–559: Definitions 21.5 and 21.6 on p. 552, Definitions 21.7 and 21.8 on p. 553, Example 21.9 on pp. 553–554, the worst-case efficiency ratio `ρ(D)` over nonnegative admissible utilities and Theorem 21.10 on p. 554, the Steps 1–8 proof on pp. 555–558 including Footnote 4 on p. 556 avoiding a `C²` hypothesis, and Eq. (21.38) with Figure 21.1 on p. 558, formalized in `CslibFrontier/GameTheory/ResourceAllocation/MarketClearing.lean`), §21.4 (pp. 559–564, Theorem 21.11, Corollary 21.12, Example 21.13, and Proposition 21.14 on scalar strategy VCG mechanisms, formalized in `CslibFrontier/GameTheory/ResourceAllocation/SSVCG.lean`), and Exercises 21.1–21.2 (pp. 567–568, first-order optimality and exact worst-case efficiency `ρ(D_c) = G(c)` for `D_c(p, θ) = θ p^(-1/c)`, `c ≥ 1`, formalized in `MarketClearing.lean`).
Two printed typos in §21.3 are corrected in `MarketClearing.lean`: Definition 21.8(iii) on p. 553 prints `∃ θ > 0, D(p, θ) = d` for `d ≥ 0`, which at `d = 0` combined with `D(p, θ) = a(p) θ + b(p) ≥ 0` would force `D ≡ 0` and leave `𝒟` empty (contradicting Example 21.9 and Theorem 21.10(ii)), so `IsRegularMarketClearing.surjective_demand` uses `∃ θ ≥ 0, D p θ = d` matching the strategy space `[0, ∞)`; and Example 21.9 on p. 553 prints exponent `1/c` in `p_D(θ) = (∑_r θ_r / C)^(1/c)` for `D(p, θ) = θ p^(-1/c)`, whereas solving `∑_r θ_r p^(-1/c) = C` gives exponent `c`, `((∑_r θ_r) / C)^c` (`clearingPrice_powerElasticity`, consistent with `B(p) = p^(1/c)`, `Λ(μ) = μ^c`, and Exercises 21.1–21.2).
Multi-link network resource allocation (§21.5) remains open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).

<a id="joharitsitsiklis2009"></a>
## joharitsitsiklis2009

Ramesh Johari and John N. Tsitsiklis.
"Efficiency of Scalar-Parameterized Mechanisms."
*Operations Research* 57(4), 823–839, 2009. https://doi.org/10.1287/opre.1080.0638 (bibliography key `JohariTsitsiklis2009`).
Bibliographic metadata from `references.bib` (journal publication of the 2007 working paper cited in [Johari](#johari2007), §21.6.2, pp. 565–566).
The *Operations Research* journal full text was not inspected firsthand, so theorem numbering and pagination in this article are marked `unverified` in the results registry; the formalized statements and proofs in `CslibFrontier/GameTheory/ResourceAllocation/MarketClearing.lean` were checked directly against [Johari](#johari2007), §21.3 and Exercises 21.1–21.2.

<a id="johnsonlindenstrauss84"></a>
## johnsonlindenstrauss84

William B. Johnson, Joram Lindenstrauss.
“Extensions of Lipschitz Mappings into a Hilbert Space.”
In *Conference in Modern Analysis and Probability (New Haven, Conn., 1982)*, Contemporary Mathematics 26, 189–206.
American Mathematical Society, 1984. https://doi.org/10.1090/conm/026/737400 . Bibliographic data from the DOI record; the manual attributes only the existence of low-distortion linear embeddings of `n` points into `O(log n / ε²)` dimensions to this paper.

<a id="jrr25"></a>
## jrr25

Jake Januzelli, Mike Rosulek, Lawrence Roy.
"Lower Bounds for Garbled Circuits from Shannon-Type Information Inequalities."
*Advances in Cryptology – CRYPTO 2025*, 2025.
Full version: Cryptology ePrint Archive, Paper 2025/876, https://eprint.iacr.org/2025/876 . Bibliographic metadata from the ePrint record; the paper's numbered lemmas were not checked against the full text.
Cited at topic level as motivation for the generic one-world conditional-entropy transfer and Fano size bound; the paper's multi-world gate-specific Shannon-type inequalities and single-gate random-oracle model are not formalized.

<a id="juknasergeev2013"></a>
## juknasergeev2013

Stasys Jukna and Igor Sergeev.
"Complexity of Linear Boolean Operators."
*Foundations and Trends in Theoretical Computer Science* 9(1), 1–123, 2013. https://doi.org/10.1561/0400000063 ; authors' PDF https://igorssergeev.github.io/papers/linear.pdf . Inspected the authors' monograph PDF (SHA-256 `57d43bce79dc0a5a28d2f6b3890c6b522cde3d8020610f7703d105226929896a`) on 2026-11-23 UTC for §3.3 ("Nechiporuk's bounds", pp. 31–33): Theorem 3.9 (pp. 32–33) proves via Pippenger's threshold-edge cut argument that every `(k + 1, l + 1)`-free Boolean matrix `A` satisfies `OR(A) ≥ |A| / (k · l)` (and `OR_2(A) ≥ |A| / max {k, l}`), and in particular `2`-free matrices satisfy `OR(A) = |A| = OR_1(A)` (p. 33).
[Rectifier/Basic.lean](../CslibFrontier/Computability/Circuit/Rectifier/Basic.lean) formalizes the symmetric `k = l = K - 1` case (`IsRectangleFreeMatrix A K → boolMatrixWeight A ≤ (K - 1)^2 * orComplexity A`) and its `2`-free consequence `OR(A) = OR_d(A) = |A|` (`1 ≤ d`).

<a id="kabanetscai2000"></a>
## kabanetscai2000

Valentine Kabanets and Jin-Yi Cai.
*Circuit Minimization Problem*.
STOC 2000, 73–79. https://doi.org/10.1145/335305.335314 . Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.
The theorem number of the one-way-function consequence is unverified.

<a id="kaibelweltge15"></a>
## kaibelweltge15

Volker Kaibel and Stefan Weltge.
"A Short Proof that the Extension Complexity of the Correlation Polytope Grows Exponentially."
*Discrete & Computational Geometry* 53(2), 397–401, 2015. https://doi.org/10.1007/s00454-014-9655-9 ; arXiv:1307.3543, https://arxiv.org/abs/1307.3543 . Checked against arXiv:1307.3543v6 (25 Feb 2016) on 2026-11-11 UTC: Section 2 (valid subsets of `D(n)`, Lemma 1 for the valid face `F_a`, Lemma 2 for the covering of `D(n)` of size `f`, Theorem 1 proving `xc(CORR(n)) ≥ 1.5^n` via `̺(n) ≤ 2^n`) and Section 3 (the rectangle covering number of `UDISJ(n)` and nondeterministic communication lower bound `log₂(1.5^n)`).
Journal pagination was taken from bibliographic search records.

<a id="kargerstein96"></a>
## kargerstein96

David R. Karger and Clifford Stein.
"A New Approach to the Minimum Cut Problem."
*Journal of the ACM* 43(4), 601–640, 1996. https://doi.org/10.1145/234533.234534 . Bibliography key `KargerStein1996`.
Inspected on 2026-11-08 in the author-hosted copy (people.csail.mit.edu/karger/Papers/contract.pdf, dated 6 August 1996); locators refer to that copy.
Section 2 defines the blocks `s(a)` and the output cut.
Lemma 2.1 says a cut is output iff no crossing edge is contracted.
Theorem 2.2 is the per-cut bound `C(n, 2)⁻¹`, and the text after its proof notes that the `n`-cycle makes the bound tight.
The proof of Theorem 4.4 attributes the bound of `C(n, 2)` minimum cuts to Dinitz, Karzanov and Lomonosov (1976).
The proof of Theorem 8.4, stated for `α`-minimal cuts, bounds their number by the disjointness of the output events; applied to Theorem 2.2, this argument gives the count.
That 1976 paper was not consulted and is cited only through this attribution.

<a id="karlin88"></a>
## karlin88

Anna R. Karlin, Mark S. Manasse, Larry Rudolph, Daniel D. Sleator.
"Competitive Snoopy Caching."
*Algorithmica* 3, 79–119, 1988. https://doi.org/10.1007/BF01762111 . Bibliographic data from secondary indexes and the DOI record; the full text was not inspected in this pass.
The manual credits this paper only with the rent-or-buy framing behind ski rental, which secondary sources attribute to it.

<a id="karlin94"></a>
## karlin94

Anna R. Karlin, Mark S. Manasse, Lyle A. McGeoch, Susan Owicki.
"Competitive Randomized Algorithms for Nonuniform Problems."
*Algorithmica* 11(6), 542–571, 1994 (preliminary version in SODA 1990). https://doi.org/10.1007/BF01189993 . Bibliographic data from secondary indexes and the DOI record; the full text was not inspected, so no theorem number is cited.
The manual credits this paper with the equalizing randomized rent-or-buy strategy and its ratio `1/(1 - (1 - 1/B)^B) → e/(e-1)` against an oblivious adversary, which secondary sources attribute to it.

<a id="karp82"></a>
## karp82

Richard M. Karp.
“Dynamic Programming Meets the Principle of Inclusion and Exclusion.”
*Operations Research Letters* 1(2), 49–51, 1982. https://doi.org/10.1016/0167-6377(82)90044-X . Bibliographic metadata checked via DOI on 2026-11-11; the article body (paywalled) was not inspected, so the manual cites it for the inclusion–exclusion formulation of sequencing/Hamiltonian-path counting without a theorem or page locator.

<a id="kasai01"></a>
## kasai01

Toru Kasai, Gunho Lee, Hiroki Arimura, Setsuo Arikawa and Kunsoo Park.
"Linear-Time Longest-Common-Prefix Computation in Suffix Arrays and Its Applications."
*Combinatorial Pattern Matching (CPM 2001)*, Lecture Notes in Computer Science 2089, 181–192, Springer, 2001. https://doi.org/10.1007/3-540-48194-X_17 . Bibliographic data from secondary indexes and the DOI record; the publisher's full text was not accessible in this pass.
The manual credits it with the text-order LCP algorithm and the height lemma `lcp[rank[i + 1]] ≥ lcp[rank[i]] - 1`, following the customary attribution; its internal lemma and theorem numbers are not cited.

<a id="kasami65"></a>
## kasami65

Tadao Kasami.
*An Efficient Recognition and Syntax-Analysis Algorithm for Context-Free Languages*.
Scientific Report AFCRL-65-758, Air Force Cambridge Research Laboratory, Bedford, MA, 1965.
Bibliographic metadata was checked against secondary sources on 2026-11-08; the report was not inspected.
It is cited, with [Younger 1967](#younger67), as an original source of the CYK algorithm.

<a id="katzlindell20"></a>
## katzlindell20

Jonathan Katz and Yehuda Lindell.
*Introduction to Modern Cryptography*, 3rd edition.
CRC Press, 2020.
Bibliographic metadata and section titles checked against the authors' 3rd-edition table of contents and preface: https://www.cs.umd.edu/~jkatz/imc/toc-preface-3rd.pdf (Sections 9.2.3–9.2.4 on the factoring and RSA assumptions; Section 15.1.1 on trapdoor permutations; Section 15.2 on Paillier encryption; Sections 15.4.1–15.4.3 on quadratic residues and the quadratic residuosity assumption; and Sections 15.5.1–15.5.2 on modular square roots and the Rabin trapdoor permutation).
Checked against a PDF of the 3rd edition (CRC Press, 2020), Chapter 12, pp. 423–437, directly inspected on 2026-11-16 for §12.3.2 Definition 12.13 (p. 425, `KEM^cca` with `n`-bit keys and decapsulation oracle rejecting the challenge ciphertext), §12.4.2 Construction 12.19 (p. 431, Diffie–Hellman KEM with `H : G → {0, 1}^{ℓ(n)}`), §12.4.4 gap-CDH prose definition with fixed-base DDH oracle `O_y(U, V) = 1 ↔ V = U^y` (p. 434), Theorem 12.22 (p. 435, ROM CCA security of Construction 12.19 under gap-CDH), and Construction 12.23's `c ∈ G` decryption validation remark (pp. 435–436).
The [third-edition text](https://studylib.net/doc/28600889/introduction-to-modern-cryptography--third-edition) was also checked for the fixed-length syntax in Definition 3.7 (p. 52), the single-challenge CCA experiment in Definition 5.1 (pp. 149–150), and §5.2.1, Definitions 5.2–5.4 and Theorem 5.5 (pp. 151–153), which relate fresh-plaintext unforgeability and CCA security to the real/ideal experiment.
Other numbered locators outside these passages and the additional check below remain attributed to the Lean source docstrings, as those chapters were not independently audited; the Lean modules adapt the parameter generators, RSA challenge domain, Rabin sampling distribution, and the Paillier encryption-randomness sampler (dyadic sampling with `unitOrOne` in place of uniform `ℤ_N^*`) as documented in their module docstrings and implementation notes.

Additional source check on 2026-11-23 against an online copy of the third-edition text (not the publisher's): §15.2.3, Definition 15.14 (printed pp. 537–538), requires exact agreement between the product of two independent encryptions and fresh encryption of their sum, as well as correctness under decryption.
The `10 / 2 ^ n` bound in [Paillier.Statistical](../CslibFrontier/Crypto/Computational/Paillier/Statistical.lean) is an original statistical approximation for the implemented dyadic sampler; its fixed-ciphertext comparison is stronger than the independent-product bound at the same error, and is not the source definition.

<a id="kdw04"></a>
## kdw04

Iordanis Kerenidis and Ronald de Wolf.
"Exponential Lower Bound for 2-Query Locally Decodable Codes via a Quantum Argument."
*Journal of Computer and System Sciences* 69(3), 395–420, 2004. https://doi.org/10.1016/j.jcss.2004.04.007 ; arXiv text https://arxiv.org/abs/quant-ph/0208062v2 . Checked on 2026-11-12 against `arXiv:quant-ph/0208062v2` (Appendix B Definition 3 and Theorem 9 on printed p. 14, and Appendix B Lemma 3 on printed p. 16); journal metadata from DOI record.

<a id="kearns07"></a>
## kearns07

Michael Kearns.
"Graphical Games."
Chapter 7 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 159–180 (bibliography key `Kearns2007`). https://doi.org/10.1017/CBO9780511800481.009 . Checked directly against the Chapter 7 book text (pp. 159–180) on 2026-11-24: Section 7.2 (pp. 161–162: standing binary-action `{0, 1}` and `[0, 1]`-payoff conventions on p. 161 with the multi-action generalization remark, mixed strategies, Nash equilibrium and additive `ε`-Nash equilibrium on p. 162, closed neighborhoods `N(i)` containing `i`, Definition 7.1 for graphical games `(G, M)` on p. 162, and the Section 7.2 Remarks on p. 162 on neighborhood-exponential parameter counts and representing any normal-form game on the complete graph), Section 7.3 (pp. 164–166: upside-down rooted tree orientation and upstream subtrees `UP_G(U)` on p. 164, Figure 7.1 Algorithm `TreeNash` on p. 165, root table `T(z)` on p. 166, and Theorem 7.3 on p. 166 proving exact equilibrium soundness and completeness of the abstract continuous-table two-pass dynamic program), Section 7.3.1 (pp. 166–168: discretized `τ`-grid `{0, τ, 2τ, …, 1}^n`, Lemma 7.4 on p. 167 proving that the `L_1`-nearest `τ`-grid strategy to a Nash equilibrium on a graph of maximum degree `d` is a `dτ`-Nash equilibrium, and `ApproximateTreeNash` with Theorem 7.5 on pp. 167–168), Section 7.3.3 (pp. 168–169: `NashProp` unoriented neighbor-table refutation on general graphs, beginning on p. 168), and Section 7.4.1 (pp. 170–171: Definition 7.7 expected payoff equivalence `P ≡_EP Q` on p. 170, Definition 7.8 local neighborhood equivalence `P ≡_LN Q` on p. 171, Lemma 7.9 on p. 171 showing `P ≡_LN Q` strictly refines `P ≡_EP Q`, and Lemma 7.10 on p. 171 showing `P ≡_LN Q` preserves correlated equilibria).
Cited by [Graphical/Basic.lean](../CslibFrontier/GameTheory/Graphical/Basic.lean) and [Graphical/TreeNash.lean](../CslibFrontier/GameTheory/Graphical/TreeNash.lean) (with `C_4` counterexamples in [Tests/GameTheory/Graphical.lean](../CslibFrontierTests/GameTheory/Graphical.lean)), which generalize Definition 7.1, Theorem 7.3, and Definitions 7.7–7.8 / Lemmas 7.9–7.10 to arbitrary action families `S : ι → Type*` and formalize the mathematical equilibrium correctness and `L_1`-closeness completeness step of Theorem 7.5 (`approxTreeNash_isApproxNash`, `exists_approxTreeNashOutput_of_isMixedNash`) without its polynomial machine running-time claim; machine running-time bounds for Theorem 7.5 and rectangular `ExactTreeNash` (Section 7.3.2, Theorem 7.6, p. 168), local Markov networks for correlated equilibria (Section 7.4.2, pp. 172–176), and graphical economics (Section 7.5, pp. 176–179) remain open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).

<a id="kelsocrawford1982"></a>
## kelsocrawford1982

Alexander S. Kelso, Jr. and Vincent P. Crawford.
"Job Matching, Coalition Formation, and Gross Substitutes."
*Econometrica* 50(6), 1483–1504, 1982 (bibliography key `KelsoCrawford1982`).
Bibliographic metadata checked against [blumrosennisan07](#blumrosennisan07), p. 297; the primary journal PDF was not consulted in this pass (`primary PDF unverified`), and no internal theorem or page locator is claimed.
[GrossSubstitutes.lean](../CslibFrontier/GameTheory/Mechanism/CombinatorialAuction/GrossSubstitutes.lean) cites it alongside [blumrosennisan07](#blumrosennisan07) (§11.7.1, Figure 11.3, Definition 11.28, Theorem 11.30, and Claim 11.31, pp. 290–291) as the originating reference for gross substitutes, ascending substitutes auctions, and Walrasian equilibrium existence.

<a id="kempekleinbergtardos03"></a>
## kempekleinbergtardos03

David Kempe, Jon Kleinberg and Éva Tardos.
"Maximizing the Spread of Influence through a Social Network."
*Proceedings of the Ninth ACM SIGKDD International Conference on Knowledge Discovery and Data Mining*, 137–146, 2003. https://doi.org/10.1145/956750.956769 . Bibliographic metadata taken from [kleinberg07](#kleinberg07) (Bibliography, pp. 631–632) and the DOI record; the conference text was not inspected firsthand, so internal theorem and page locators are left unverified.
Cited through [kleinberg07](#kleinberg07), Sections 24.3–24.4, for the Linear Threshold and Independent Cascade models, the time-layered DAG reduction for nonprogressive processes (pp. 621–622), the live-edge reachability proof of Independent Cascade influence submodularity (Theorem 24.5, pp. 625–626), and greedy `(1 - 1/e)` influence maximization.

<a id="kempekleinbergtardos05"></a>
## kempekleinbergtardos05

David Kempe, Jon Kleinberg and Éva Tardos.
"Influential Nodes in a Diffusion Model for Social Networks."
*Automata, Languages and Programming (ICALP 2005)*, 1127–1138, 2005. https://doi.org/10.1007/11523468_91 . Bibliographic metadata taken from [kleinberg07](#kleinberg07) (Bibliography, p. 632) and the DOI record; the conference text was not inspected firsthand, so internal theorem and page locators are left unverified.
Cited through [kleinberg07](#kleinberg07), Sections 24.3–24.4, for the equivalence of the General Threshold Model and the order-independent Cascade Model over final active-set distributions (pp. 620–621) and submodularity of influence for diminishing-returns cascade models (Theorem 24.4, pp. 624, 626).

<a id="khot10"></a>
## khot10

Subhash Khot.
"On the Unique Games Conjecture (Invited Survey)."
*2010 IEEE 25th Annual Conference on Computational Complexity (CCC)*, 99–121, 2010. https://doi.org/10.1109/CCC.2010.19 . Author-hosted copy inspected: https://cs.nyu.edu/~khot/papers/UGCSurvey.pdf (Section 2.4, p. 6 of the author copy: the second paragraph after Definition 2.4, beginning "Let us return", on finding a satisfying labelling of a value-1 instance by trying every label for one vertex and propagating along each connected component, and the remark after Conjecture 2.5 that the conjecture would be false with `ε = 0`).
The page range and DOI are from the bibliographic record and were not checked against the typeset proceedings.

<a id="kirshnersamorodnitsky21"></a>
## kirshnersamorodnitsky21

Naomi Kirshner and Alex Samorodnitsky.
"A Moment Ratio Bound for Polynomials and Some Extremal Properties of Krawtchouk Polynomials and Hamming Spheres."
*IEEE Transactions on Information Theory* 67(6), 3509–3541, 2021. https://doi.org/10.1109/TIT.2021.3071597 ; arXiv:1909.11929v1.
The statements of Theorem 1.3, Corollary 1.4 and Theorem 1.5 in arXiv v1 were read on 2026-11-12.
They hold for every `n`, with no `o(1)` terms, for polynomials of degree `s ≤ n / 2`.
The independent review of [#4735](https://github.com/cslib-community/cslib-frontier/pull/4735) checked Saglam's specializations against the same version.
Saglam's explicit `γ` is `H(ρ)/2 - ψ(3, ρ)`, by Proposition 2.6 at `p = 3` with `t = 1 - 2δ` (so `t² = ρ/(2 - 3ρ)`).
His integral form is their `τ(x, y) = H(x) + I(y, x) - I(0, x)` for `y ≤ 1/2 - √(x(1 - x))` (§2.1.1–2.1.2).
As printed, Theorem 1.5 fails at degree `0`: for `f ≡ 1` and `i = 0` the `≥` event has probability `1 > 2^{-n}`.
The library's hypotheses therefore use a strict event and require `0 < w`.
[Code/PuncturedBallFourier](../CslibFrontier/Foundations/Data/Code/PuncturedBallFourier.lean) states Corollary 1.4 (third moment) and Theorem 1.5 (tail) as hypotheses (`KSThirdMomentBound`, `KSTailBound`), in the specialization quoted in [Saglam](#saglam27), Appendix A. They are not proved.

<a id="kleeminty72"></a>
## kleeminty72

Victor Klee and George J. Minty.
"How Good Is the Simplex Algorithm?"
In O. Shisha (ed.), *Inequalities III*, Academic Press, New York, 1972, pp. 159–175.
Bibliographic data from search summaries; the paper was not inspected in this pass, and no theorem number is claimed.
The manual credits it with the deformed cubes on which Dantzig's largest-coefficient rule visits all `2^n` vertices.
The formalized program, `max ∑ 10^(n-j) x_j` subject to `2 ∑_{j<i} 10^(i-j) x_j + x_i ≤ 100^(i-1)` and `x ≥ 0`, is the textbook form attributed to [chvatal83](#chvatal83), Chapter 4, which was not inspected either; the coefficients were taken from secondary summaries and checked by running Dantzig's rule on them for `n ≤ 7`, which takes `2^n - 1` pivots in each case.

<a id="kleenepost54"></a>
## kleenepost54

Stephen C. Kleene and Emil L. Post.
*The Upper Semi-Lattice of Degrees of Recursive Unsolvability*.
Annals of Mathematics (2) 59(3), 379–407, 1954. https://doi.org/10.2307/1969708 . Bibliographic metadata checked on 2026-11-08; the article is paywalled and was not inspected.
The manual attributes to it, following the customary attribution, the existence of two Turing-incomparable sets below `0′` by the finite extension method.
No section or theorem locator is claimed.

<a id="kleinberg07"></a>
## kleinberg07

Jon Kleinberg.
"Cascading Behavior in Networks: Algorithmic and Economic Issues."
Chapter 24 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 613–632.
Read in the book PDF on 2026-11-24 for Sections 24.3–24.4 (printed pp. 618–627, PDF pp. 639–648): the incoming-neighbor convention (p. 619, Footnote 1), Linear Threshold and General Threshold models (`g_v(∅) = 0`, `θ_v ∼ Uniform[0, 1]`, pp. 619–620, 623), the order-independent Cascade and Independent Cascade models and bidirectional equivalence with General Threshold over final active-set distributions (pp. 620–621, citing [kempekleinbergtardos05](#kempekleinbergtardos05)), the `T`-step time-layered DAG reduction for nonprogressive processes (pp. 621–622), Theorem 24.3 (`1 - 1/e` greedy monotone submodular maximization, p. 624), Theorem 24.4 (diminishing-returns Cascade influence submodularity, p. 624, reduction to submodular local thresholds on p. 626), Theorem 24.5 (Independent Cascade influence submodularity and its live-edge reachability proof, pp. 625–626), and Theorem 24.6 (General Threshold influence submodularity for submodular local thresholds `g_v`, p. 626, citing [mosselroch07](#mosselroch07)).
Cited by [InfluenceModels.lean](../CslibFrontier/GameTheory/Network/InfluenceModels.lean) and [InfluenceMaximization.lean](../CslibFrontier/GameTheory/Network/InfluenceMaximization.lean); the approximate-oracle `(1 - 1/e - ε)` discussion (p. 624) and Exercise 24.3 hardness/inapproximability (p. 632) remain open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).

<a id="kleinbergtardos06"></a>
## kleinbergtardos06

Jon Kleinberg and Éva Tardos.
*Algorithm Design*.
Addison-Wesley, 2006.
Cited for Section 6.6 ("Sequence Alignment"), the alignment dynamic program with gap and mismatch costs.
Section 6.7 ("Sequence Alignment in Linear Space via Divide and Conquer") is the locator for the Hirschberg follow-up.
The section titles were checked against search summaries of the published table of contents on 2026-11-08, not the printed book.

<a id="kmb81"></a>
## kmb81

L. Kou, G. Markowsky and L. Berman.
*A Fast Algorithm for Steiner Trees*.
Acta Informatica 15(2), 141–145, 1981. https://doi.org/10.1007/BF00288961 . The heuristic's steps (shortest-path distance graph on the terminals, its minimum spanning tree, replacement by shortest paths, a spanning tree of the result, then pruning non-terminal leaves) and the `2 (1 - 1/ℓ)` bound, with `ℓ` the number of leaves of an optimal tree, are taken from the abstract and secondary sources.
The body of the paper was not consulted.

<a id="knasterkuratowskimazurkiewicz29"></a>
## knasterkuratowskimazurkiewicz29

Bronisław Knaster, Kazimierz Kuratowski and Stefan Mazurkiewicz.
"Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe."
*Fundamenta Mathematicae* 14, 132–137, 1929.
Bibliographic metadata checked via search summaries; the full text was not inspected, so internal section or theorem locators are not claimed.
Cited by [KKMS.lean](../CslibFrontier/Foundations/Analysis/Brouwer/KKMS.lean) for the classical KKM covering lemma.

<a id="knuth1994"></a>
## knuth1994

Donald E. Knuth.
*The Sandwich Theorem*.
Electronic Journal of Combinatorics 1, A1, 1994. https://doi.org/10.37236/1193 ; arXiv text https://arxiv.org/abs/math/9312214 . The arXiv text was consulted on 2026-11-07 for §1 (orthogonal labelings and the lemma `α ≤ ϑ`), §4 (4.9), §5 (5.2), the product lemma of §20 and the pentagon umbrella of §22.
The formal umbrella matches §22 up to the vertex relabelling `i ↦ 3i`.

<a id="knuth71"></a>
## knuth71

Donald E. Knuth.
"Optimum Binary Search Trees."
*Acta Informatica* 1(1), 14–25, 1971. https://doi.org/10.1007/BF00264289 . The bibliographic data come from secondary indexes and search summaries; the article was not inspected in this pass.
The manual credits it, as secondary sources do, with the cubic dynamic program, the monotonicity of optimal roots and the resulting quadratic algorithm.
No theorem numbers are cited.

<a id="knuth98"></a>
## knuth98

Donald E. Knuth.
*The Art of Computer Programming, Volume 3: Sorting and Searching*, second edition.
Addison-Wesley, 1998.
Section 5.3.3 ("Minimum-comparison selection") is the locator for the `n - 1` bound for the minimum and for the bound `⌈3n/2⌉ - 2` for the minimum and maximum, which secondary sources place in Exercise 5.3.3-16 with an attribution to Pohl.
These locators come from secondary sources; the printed book was not inspected.

<a id="knuthyao76"></a>
## knuthyao76

Donald E. Knuth and Andrew C. Yao.
"The Complexity of Nonuniform Random Number Generation."
In J. F. Traub (ed.), *Algorithms and Complexity: New Directions and Recent Results*, Academic Press, 1976, pp. 357–428.
Cited for DDG trees, the optimal tree built from binary expansions, and the entropy bounds `H ≤ E[T] < H + 2`.
These attributions follow Cover–Thomas §5.11 and secondary literature (Saad, Freer, Rinard and Mansinghka, POPL 2020).
The 1976 text was not inspected, so no theorem number is cited.

<a id="ko1991"></a>
## ko1991

Ker-I Ko.
*On the Complexity of Learning Minimum Time-Bounded Turing Machines*.
SIAM Journal on Computing 20(5), 962–986, 1991. https://doi.org/10.1137/0220059 . Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.

<a id="kobayashi1985"></a>
## kobayashi1985

Kojiro Kobayashi.
"On proving time constructibility of functions."
*Theoretical Computer Science* 35, 215–225, 1985. https://doi.org/10.1016/0304-3975(85)90015-5 . Bibliographic metadata checked through Crossref; the article body was not inspected in this pass.
The manual cites it, as [Pighizzini 2009](#pighizzini2009) §4 does, as an independent proof of the `n log n` bound.

<a id="kollarronyaiszabo1996"></a>
## kollarronyaiszabo1996

János Kollár, Lajos Rónyai and Tibor Szabó.
"Norm-Graphs and Bipartite Turán Numbers."
*Combinatorica* 16(3), 399–406, 1996. https://doi.org/10.1007/BF01261323 . Bibliographic metadata as cited in [sergeev2014orcomplement](#sergeev2014orcomplement) (Reference [4], p. 3); the article was not inspected directly.
Cited in [Rectifier/ComplementSeparation.lean](../CslibFrontier/Computability/Circuit/Rectifier/ComplementSeparation.lean) only to note that Sergeev's Theorem 1(i) projective norm-graph instantiation remains open under [#7622](https://github.com/cslib-community/cslib-frontier/issues/7622).

<a id="kortevygen18"></a>
## kortevygen18

Bernhard Korte and Jens Vygen.
*Combinatorial Optimization: Theory and Algorithms*, sixth edition.
Springer, Algorithms and Combinatorics 21, 2018. https://doi.org/10.1007/978-3-662-56039-6 . Cited for Section 2.4 (Eulerian and bipartite graphs), which characterizes connected graphs with a closed Eulerian walk by even degrees (Euler, Hierholzer).
The section was located from secondary sources and not checked against the printed book; its theorem number is not cited.

<a id="kosugexagawa2022"></a>
## kosugexagawa2022

Haruhisa Kosuge and Keita Xagawa.
*Probabilistic Hash-and-Sign with Retry in the Quantum Random Oracle Model*.
IACR Cryptology ePrint Archive Report 2022/1359 (bibliography key `KosugeXagawa2022`). https://eprint.iacr.org/2022/1359 . Checked on 2026-11-24 UTC against the archived 53-page PDF (ModDate 2024-02-08, SHA-256 `60cb3368f368beeaec030cc9446e6fe1d4151106299b3f2984245a9ac6d5e031`): Section 2.3 (p. 10, Figure 4 and Definition 7) defines the preimage-sampling (`PS`) game comparing `x ← I(y)` on uniform `y` (with retry until `x ≠ ⊥` in `Sample_0`) against `x ← SampDom(F)`; Section 4, Theorem 1 (pp. 17–18) proves `INV ⇒ EUF-CMA` for `HaS[T_wpsf, H]`, including the classical-ROM specialization on p. 18 with `(q_ro + 1) Adv^{INV} + Adv^{PS} + q'_sign (q'_sign + q_ro + 1) / |R| + (q_ro + 1)(q'_sign - q_sign) / |R|`; and Appendix B.2, Proposition 3 (p. 36) applies Theorem 1 to original UOV.
[UOV/HashAndSign.lean](../CslibFrontier/Crypto/Protocols/UOV/HashAndSign.lean) proves finite classical-ROM reductions without retry (`Option Preimage` failure retained so `q'_sign = q_sign`, exact `Salt` collision slack `(q_S * q_H + q_S.choose 2) / |Salt|`, and an unsalted deterministic counterpart with explicit `PS_1` and target-birthday slack); QROM bounds remain unformalized.

<a id="kov17"></a>
## kov17

Peter Kairouz, Sewoong Oh and Pramod Viswanath.
*The Composition Theorem for Differential Privacy*.
IEEE Transactions on Information Theory 63(6), 4037–4049, 2017. https://doi.org/10.1109/TIT.2017.2685505 ; theorem numbering cited from arXiv:1311.0776v4, 2015.
Theorem 3.4 (equation (7)) was checked against the arXiv v4 PDF on 2026-11-07; the journal metadata was checked against Crossref.

<a id="ks08"></a>
## ks08

Vladimir Kolesnikov, Thomas Schneider.
"Improved Garbled Circuit: Free XOR Gates and Applications."
*Automata, Languages and Programming, 35th International Colloquium (ICALP 2008)*, Lecture Notes in Computer Science 5126, 486–498, 2008. https://doi.org/10.1007/978-3-540-70583-3_40 ; author's copy: https://www.cs.toronto.edu/~vlad/papers/XOR_ICALP08.pdf . Cited at paper level for the free-XOR technique, which it proves secure in the random oracle model; no theorem numbers are claimed.

<a id="kuhnwattenhofer2006"></a>
## kuhnwattenhofer2006

Fabian Kuhn and Roger Wattenhofer.
"On the Complexity of Distributed Graph Coloring."
*Proceedings of the Twenty-Fifth Annual ACM Symposium on Principles of Distributed Computing (PODC 2006)*, 7–15, 2006. https://doi.org/10.1145/1146381.1146387 ; author-hosted copy: https://ac.informatik.uni-freiburg.de/publications/publications/podc06.pdf . Checked on 2026-11-22 UTC against that PDF (9 pages, printed pp. 7–15, SHA-256 `a27d59bb9609708e3fb433effc6f951254da40a27841c4aa9a8b85ffe68e27a9`): §1 (pp. 7–8, overview), §3 ("The Neighborhood Graph", p. 9: Definition 3.1 defining the one-round neighborhood graph `N_1(m, Δ)` and Lemma 3.1 showing deterministic `1`-round color reduction achieves palette size `q = χ(N_1(m, Δ))`), §4 (pp. 9–12: Theorem 4.3 `χ(N_1(m, Δ)) ∈ O(Δ² log m)` `1`-round upper bound and Theorem 4.8 `1`-round lower bound), §5 (pp. 12–13: Theorem 5.1 proving that one communication round reduces `m` colors to `⌈m (Δ + 1) / (Δ + 2)⌉` colors by mapping high colors into disjoint blocks of size `Δ + 1`, Corollary 5.2 giving `O(Δ log Δ + log* m)` iterative `1`-round `(Δ + 1)`-coloring by combining Linial's cover-free set systems with Theorem 5.1, and Theorem 5.3 / Corollary 5.4 iterative lower bounds), and §6 ("Randomized Distributed Coloring", pp. 13–14: Theorem 6.1 and Corollary 6.2 giving `O(Δ log log n)` randomized w.h.p.
`(Δ + 1)`-coloring).
[LocalGraph/Coloring.lean](../CslibFrontier/Computability/Distributed/LocalGraph/Coloring.lean) formalizes the one-round disjoint-block compression step `kwCompressProtocol_run` and strict palette shrinkage `kwBound_lt` (steps toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505); §4's `N_1(m, Δ)` bounds, §5's Corollary 5.2 `O(Δ log Δ + log* m)` algorithm and Theorem 5.3 / Corollary 5.4 lower bounds, and §6's randomized `O(Δ log log n)` algorithm are not formalized).

<a id="kunreutherheal03"></a>
## kunreutherheal03

Howard Kunreuther and Geoffrey Heal.
"Interdependent Security."
*Journal of Risk and Uncertainty* 26(2–3), 231–249, 2003. https://doi.org/10.1023/A:1024119208153 ; NBER Insurance Workshop version (February 2002, 20 PDF pp.): https://users.nber.org/~confer/2002/insw02/kunreuther.pdf . Checked against that 20-page NBER PDF (journal pagination 231–249 taken from Crossref) on 2026-11-24 UTC: §2 ("2.
A Model of Interdependent Security", pp. 3–11: two-agent expected costs, Table 1, and Table 2 `p = 0.1, q = 0.8, L = 1000, c = 95` coordination example on pp. 3–5, `n`-agent geometric-series unprotected loss `p L + p q L (1 - p) ∑_{t=0}^{n-2} (1 - p q)^t = L (1 - (1 - p)(1 - p q)^{n-1})` on p. 7, Proposition 1 and Corollary 1 on p. 8 proving expected loss approaches `L` as `n → ∞` and eventual failure of dominant-strategy investment for any `c > 0`, and critical threshold `c*(n - 1) = p L (1 - p q)^{n - 1}`, symmetry of pure Nash equilibria, and Table 3 "Types of Nash Equilibria for Different c Values" on p. 9) and §3 ("Internalizing Externalities", pp. 11–13: Pigouvian non-investment tax `t* = max {0, c - p(L - M)}` (`t* > c - c*(n - 1)`) on p. 13).
Formalized in [Security/Interdependent.lean](../CslibFrontier/GameTheory/Security/Interdependent.lean) (`symmetricIDSSpec_cost_allFalse_eq_geom_sum`, `symmetricIDSSpec_criticalCost_eq_geom_sum`, `tendsto_symmetricIDSSpec_cost_allFalse_atTop`, `eventually_not_dominant_invest_symmetricIDSSpec`, `eq_const_of_isPureNash_symmetricIDSSpec`, and `isCoarseCorrelatedEquilibrium_symmetricIDSSpec_taxed_unique`; the companion 2-agent mixed-vs-correlated strict gap `symmetricIDSSpec_isMixedNash_and_correlated_strict_improvement`, `(1, μ)`-smoothness Price-of-Anarchy bounds `isSmooth_toCostGame` / `expected_socialCost_le_of_isCCE` / `symmetricIDSSpec_poa_eq_inv_one_sub`, and `(n + 1)`-agent Prisoner's Dilemma `1 + n q` social-cost ratio `symmetricIDSSpec_prisonersDilemma_socialCost_le` are original extensions); §§3.2–5 (insurance, bankruptcy/limited liability, and multi-period discounting) are not formalized here.

<a id="kyber302"></a>
## kyber302

Roberto Avanzi, Joppe Bos, Léo Ducas, Eike Kiltz, Tancrède Lepoint, Vadim Lyubashevsky, John M. Schanck, Peter Schwabe, Gregor Seiler, Damien Stehlé.
*CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation (version 3.02)*, NIST Post-Quantum Cryptography Standardization third-round submission, 4 August 2021. https://pq-crystals.org/kyber/data/kyber-specification-round3-20210804.pdf . Checked on 2026-11-14 against that PDF (SHA-256 `1c54ad57022e00b77ff7acd40e9b38a962e7fbbd02bea73b183349c53a8f8aee`): the Module-LWE advantage `Adv^mlwe_{m,k,η}` with `(s, e) ← β_η^k × β_η^m` (§4.3, p. 19); Theorem 1, the IND-CPA bound for Kyber.CPAPKE (§4.3.1, p. 20); and the Module-LWER problem with the two-term replacement eq. (6) (§4.4 and footnote 3, pp. 21–22).
Checked again on 2026-11-15 against the same PDF: the pseudorandom function `PRF : B^32 × B → B^*` (p. 5); `CBD_η : B^{64η} → R_q` (Algorithm 2, p. 7); the noise `CBD_η(PRF(σ, N))` of key generation and `CBD_η(PRF(r, N))` of encryption (Algorithms 4 and 5, pp. 8–9); in Algorithm 4 (p. 8), `(ρ, σ) := G(d)`, `Â[i][j] := Parse(XOF(ρ, j, i))` and `pk := (Encode_12(t̂ mod q) ‖ ρ)`; in Algorithm 5 (p. 9), `ρ` read from `pk` and `Â^T[i][j] := Parse(XOF(ρ, i, j))`; the instantiation of `PRF(s, b)` by SHAKE-256(s‖b) (p. 11); and Theorem 1's opening "Suppose XOF and G are random oracles" (p. 20).
Cited for `MLKEM.cpaAdvantage_le`, whose model differences (a uniform matrix in the public key in place of `ρ`, no `XOF` or `G` oracles, sampled coins, uncompressed ciphertext hop, no running time) are recorded in the Lean module; for its asymptotic form with ideal coin expansion and the matrix in the public key, `MLKEM.indCPA_kpkeIdealCoins_of_decisionModuleLWEWith`, a step towards Theorem 1 without its `Adv^prf` term or its random oracles `XOF` and `G`, whose module records the same differences and its parameter family; and for `MLKEM.indCPA_kpkePRF_of_decisionModuleLWEWith`, IND-CPA of K-PKE with seed expansion (`MLKEM.kpkePRF`) and the matrix in the public key, a step towards Theorem 1 with its `Adv^prf` term but without its random oracles `XOF` and `G`, whose module records its deviations.

<a id="lahaiepennocksaberivohra07"></a>
## lahaiepennocksaberivohra07

Sébastien Lahaie, David M. Pennock, Amin Saberi and Rakesh V. Vohra.
"Sponsored Search Auctions."
Chapter 28 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 699–716 (ISBN 978-0-521-87282-9; bibliography key `LahaiePennockSaberiVohra2007`).
A university-hosted PDF of the book (SHA-256 `83084d9996024ca92f313c5ae55fec7b3b379f06172a4c24b62229da9c558543`) was consulted via rendered page images (including full uncropped page bottom slices) on 2026-11-24 for the table of contents (p. xii), Chapter 28 opening (pp. 699–700), §28.2 (pp. 701–702, GSP weighted bid ranking and GFP), §28.3 (pp. 702–707, assignment LP (28.1)–(28.4) and dual (28.5)–(28.7), Northwest corner rule and three-bidder two-slot example on p. 704, local envy-freeness (28.9)–(28.10) on p. 705, Theorem 28.1 on p. 706, Theorem 28.2 on pp. 706–707), §28.4.1 "The Online Allocation Problem" (pp. 707–711: offline LP (28.11) and its dual on p. 708, complementary slackness discussion on p. 708, greedy 1/2-competitive ratio and two-bidder example on p. 709, Algorithm 1 (`φ(x) = 1 - e^{x-1}`) and Theorem 28.3 on p. 709, discrete function `Φ(s) = 1 - (1 - 1/k)^{k-s}` (28.12) and Lemma 28.4 (28.13)–(28.14) on p. 710, Theorem 28.3 proof summary on pp. 710–711), §28.6 bibliographic notes (pp. 712–713), and Exercises 28.1–28.6 (pp. 715–716, including Exercise 28.6 removing the assumption that the optimal solution exhausts all budgets).
Discrepancies verified on the page images for §28.3: (1) on p. 704, the three-bidder two-slot example states that the generalized Vickrey auction charges bidder 1 `(1 - μ₂/μ₁) v₂` per click, omitting the `+ (μ₂/μ₁) v₃` term when `v₃ > 0` (the Clarke-pivot total payment is `(μ₁ - μ₂) v₂ + μ₂ v₃`); (2) on p. 705, (28.9)–(28.10) are stated only for matched pairs without an explicit dummy-slot condition for unassigned bidders, so the literal reading admits non-optimal locally envy-free assignments when `k < n`; (3) in the proof of Theorem 28.2 on p. 706, the displayed inequality `p*_{j-1}/μ_{j-1} ≥ p*_{j-1}/μ_j` has the wrong direction because `μ_{j-1} > μ_j > 0` (the required monotonicity `p*_{j-1}/μ_{j-1} ≥ p*_j/μ_j` holds instead from (28.9) and individual rationality), and the deviation check is omitted on p. 707.
Discrepancies verified on the page images for §28.4.1: (1) on p. 709, the two-bidder greedy example (`B₁ = B₂ = 2`, `b₁₁ = 2`, `b₁₂ = 2 - ε`, `b₂₁ = 2`, `b₂₂ = ε`) reports the optimal objective value as `4`, whereas assigning query 2 to bidder 1 and query 1 to bidder 2 yields `4 - ε` (and for `1 < ε < 2` greedy's `2 + ε` exceeds `4 - ε`); (2) on p. 709, comparing greedy against the fractional LP (28.11) requires bounding bids (`b_{ij} ≤ B_j`), because otherwise a single query with bid `n` across `n` unit-budget bidders has LP value `n` vs. online revenue `1`; (3) on p. 710, in the second line of the aligned display proving Theorem 28.3, changing summation order gives `∑_{j=0}^i Φ(i)` instead of `∑_{j=0}^i Φ(j)`.
The earlier independent primary articles mentioned in §28.6 (Edelman–Ostrovsky–Schwarz, Varian, Mehta–Saberi–Vazirani–Vazirani 2005, Karp–Vazirani–Vazirani 1990, Kalyanasundaram–Pruhs 2000, Buchbinder–Jain–Naor 2006) were not inspected directly; no theorem numbers from them are claimed.

<a id="lamagnasavage1974"></a>
## lamagnasavage1974

Edmund A. Lamagna and John E. Savage.
"Combinational Complexity of Some Monotone Functions."
*Proceedings of the 15th Annual Symposium on Switching and Automata Theory* (SWAT 1974), 140–144, IEEE, 1974 (bibliography key `LamagnaSavage1974`). https://doi.org/10.1109/SWAT.1974.8 . Bibliographic data taken from reference `[6]` of [Sergeev](#sergeev2020monotoneshift); the proceedings article was not inspected directly, so no direct theorem or page locator in `LamagnaSavage1974` is claimed.
Cited through [Sergeev](#sergeev2020monotoneshift), p. 5 (footnote 2), for the fan-in-2 subcircuit path-peeling `log₂ n!` lower-bound argument formalized in [Shift.lean](../CslibFrontier/Computability/Circuit/Monotone/Shift.lean).

<a id="lamport1974"></a>
## lamport1974

Leslie Lamport.
"A New Solution of Dijkstra's Concurrent Programming Problem."
*Communications of the ACM* 17(8), 453–455, August 1974. https://doi.org/10.1145/361082.361093 ; author-hosted copy of the typeset article: https://lamport.azurewebsites.net/pubs/bakery.pdf . Checked against that copy on 2026-11-22 UTC (SHA-256 `afdae206fc85f872846f3eafedf4e76fbc14cbfb25ff65fefea59bb244a2b6a5`, 3 pages, printed pp. 453–455): "The Algorithm" (p. 454: Algol-like `choosing[1:N]` and `number[1:N]` protocol, `maximum` scan in arbitrary order, safe overlapping reads returning arbitrary values while a write is in progress, and processor failure from any unbounded non-critical state halting and resetting `choosing[i]` and `number[i]` to zero) and "Proof of Correctness" (pp. 454–455: definitions of "in the doorway" and "in the bakery", Assertion 1 on p. 454 concluding numeric `number[i] < number[k]` from doorway entry whereas `bakery_doorway_lt` starts before the ticket scan and concludes lexicographic `ticket` order, Assertion 2 on pp. 454–455, mutual exclusion and first-come-first-served on p. 455, and Assertion 3 on p. 455 giving bounded-failure progress for some processor followed by per-process lockout freedom, formalized in `bakery_starvationFree` under explicit `BakeryState.WeakFair`, `BakeryAction.NoFailAfter`, and the target's no-failure premise).

<a id="lamport1978"></a>
## lamport1978

Leslie Lamport.
"Time, Clocks, and the Ordering of Events in a Distributed System."
*Communications of the ACM* 21(7), 558–565, July 1978. https://doi.org/10.1145/359545.359563 ; author-hosted copy of the typeset article: https://lamport.azurewebsites.net/pubs/time-clocks.pdf . Checked against that PDF (SHA-256 `c55e7cab4230aa3d7126748a149b2db6f0d7a67296d5eccfdd50a210299a96b2`) on 2026-11-22 UTC by worker `vector-clocks`: "The Partial Ordering", pp. 558–559 (Definition of `→` via conditions (1)–(3), concurrent distinct events `¬(a → b)` and `¬(b → a)`, and Footnote 2 on point-to-point vs multi-recipient send events; `Execution P` models finite unicast traces with at-most-once delivery); "Logical Clocks", pp. 559–560 (Clock Condition `a → b` implies `C(a) < C(b)`, C1 and C2, p. 560 remark that the converse cannot hold across concurrent events, and implementation rules IR1 and IR2(a),(b), instantiated here with unit increments `L p + 1` and `max (L p) L_msg + 1`); and "Ordering the Events Totally", pp. 560–561 (tie-breaking total order `⇒` defined by `C_i(a) < C_j(b)` or `(C_i(a) = C_j(b) ∧ P_i < P_j)`).
The distributed mutual exclusion / state-machine protocol (pp. 561–562) and physical clock synchronization bound (pp. 562–565) are not formalized here.
Cited by [VectorClock/Basic.lean](../CslibFrontier/Computability/Distributed/VectorClock/Basic.lean) and [VectorClock/Clocks.lean](../CslibFrontier/Computability/Distributed/VectorClock/Clocks.lean) for `Execution.HappensBefore`, `Execution.Concurrent`, `Execution.lamportClock`, `Execution.lamportClock_strictMono`, `not_exists_1d_characterization`, and `Execution.lamportTotalOrder`.

<a id="lamport1998"></a>
## lamport1998

Leslie Lamport.
"The Part-Time Parliament."
*ACM Transactions on Computer Systems* 16(2), 133–169, May 1998. https://doi.org/10.1145/279227.279229 ; author-hosted PDF with minor corrections of 29 August 2000: https://lamport.azurewebsites.net/pubs/lamport-paxos.pdf . Checked on 2026-11-22 against that PDF (SHA-256 `cd9544e9615bcd417a2c10063671cecca0b28ad4bc5db3f64467a83ecc7028d3`, author-PDF pp. 1–32): §1.2 (author-PDF pp. 2–3 / journal pp. 134–135, ledger consistency, nontriviality, and the two-group Chamber split-brain scenario motivating quorum intersection); §1.3 (author-PDF pp. 3–4, indelible ledger notes vs volatile slip-of-paper state, hourglass timers, and non-corrupting messengers with arbitrary delay, duplication, and loss); §2.1 (author-PDF pp. 5–8, ballot conditions `B1(ℬ)`–`B3(ℬ)` on pp. 5 and 7, the consistency `Lemma` and `Theorem 1` on pp. 7–8, and single-ballot extension `Theorem 2` on p. 8); §2.2–§2.3 and Appendix A1–A2 (author-PDF pp. 9–12 and 25–31, lexicographic `(integer, priest)` ballot ownership on p. 9, intersecting majority/weighted-quorum sets on p. 9, the Preliminary and Basic Synod protocols with `lastTried[p]`, `prevVote[p]`, `nextBal[p]` on pp. 11–12, and inductive consistency invariants `I1`–`I7` on pp. 28–31); and §2.4 (author-PDF pp. 12–14, competing-ballot preemption when higher-numbered `NextBallot` messages arrive continuously, single-president progress discussion, NACK `nextBal[q]` replies, and hourglass timeout bounds).
Cited as a target for the **crash-stop intermediate step** in `CslibFrontier/Computability/Distributed/Paxos/Basic.lean` (`phase2a_unique_of_ballot_crashStop`, `chosenAt_implies_higher_phase2a_eq_crashStop`, `paxos_agreement_crashStop`, `paxos_validity_crashStop`) and `CslibFrontier/Computability/Distributed/Paxos/Liveness.lean` (`exists_duelling_proposers_livelock`, `paxos_liveness_of_sole_leader_crashStop`, `exists_sole_leader_execution_crashStop`, `synodQuorumProtocol_safeCohort_crashStop`), which do **not** establish the crash-recovery cited endpoints: (a) Single-Decree Synod (§2) only is modeled—§3 Multi-Paxos parliamentary ledger replication (author-PDF pp. 15–22) remains open; (b) permanent crash-stop node failures (`crashed : Bool`) are modeled rather than crash-recovery with persistent ledger notes and volatile slip-of-paper restarts (§1.3, §2.3, Appendix A2 `Forget`), while `.prepare p r` resets per-round proposer fields (`proposed`, `promised`, `maxVote`); (c) `allowsVote` uses `Lamport2001` §2.2's `mb ≤ b` Phase 2b voting guard (updating `maxBal := some b`) rather than §2.3 step (4)'s `b = nextBal[q]`; (d) `paxos_liveness_of_sole_leader_crashStop` formalizes only a conditional 4-phase progress step assuming an already-selected sole proposer preparing a ballot above `BallotsBelow` with no higher ballot prepared, without modeling §2.4's real-time hourglass timeouts, NACK `nextBal[q]` ballot-bumping, or president election; and (e) `not_synod_safe_of_disjoint_quorums` (`AsyncQuorumProtocol`) is an original asynchronous partition / split-brain impossibility motivating quorum intersection (§1.2, §2.1 `B2`) rather than a numbered theorem statement of `Lamport1998`.

<a id="lamport2001"></a>
## lamport2001

Leslie Lamport.
"Paxos Made Simple."
*ACM SIGACT News* 32(4), 51–58, December 2001; author-hosted PDF dated 1 November 2001: https://lamport.azurewebsites.net/pubs/paxos-simple.pdf . Checked on 2026-11-22 against that PDF (SHA-256 `c83b5141257730d6fd20097ef17ebd02a02dfcb1809bad5873b7739659bb3f2b`, internal pp. 1–11 on PDF pp. 4–14): §2.1 (internal pp. 1–2 / PDF pp. 4–5, consensus safety requirements of validity/nontriviality, single chosen value, and no spurious learning, `proposer`/`acceptor`/`learner` roles, and the asynchronous non-Byzantine message-passing model with arbitrary delay, duplication, and loss); §2.2 (internal pp. 2–6 / PDF pp. 5–9, intersecting majorities and generalized quorum systems on p. 2, invariants `P1`, `P2`, `P2^a`, `P2^b`, `P2^c`, and `P1^a` on pp. 2–5, and the two-phase `Phase 1a`/`1b` and `Phase 2a`/`2b` algorithm on pp. 5–6); §2.3 (internal pp. 6–7 / PDF pp. 9–10, learner quorum acceptance from acceptors' Phase 2b responses); §2.4 (internal p. 7 / PDF p. 10, the alternating two-proposer livelock scenario `n_1 < n_2 < n_3 < ...` and conditional progress of a single distinguished proposer issuing a proposal number greater than any already used across a working majority, citing FLP for why reliable leader election requires randomness or real time/timeouts); and §2.5 (internal pp. 7–8 / PDF pp. 10–11, co-located roles, stable storage across restarts, and disjoint per-proposer ballot sets).
Cited as a target for the **crash-stop intermediate step** in `CslibFrontier/Computability/Distributed/Paxos/Basic.lean` (`phase2a_unique_of_ballot_crashStop`, `chosenAt_implies_higher_phase2a_eq_crashStop`, `paxos_agreement_crashStop`, `paxos_validity_crashStop`) and `CslibFrontier/Computability/Distributed/Paxos/Liveness.lean` (`exists_duelling_proposers_livelock`, `paxos_liveness_of_sole_leader_crashStop`, `exists_sole_leader_execution_crashStop`, `synodQuorumProtocol_safeCohort_crashStop`), which model permanent crash-stop node failures rather than crash-recovery with stable storage (§2.1, §2.5), formalize only conditional sole-proposer 4-phase progress (`paxos_liveness_of_sole_leader_crashStop`) without leader election or NACKs (§2.4), pair with an original asynchronous partition / split-brain impossibility via `AsyncQuorumProtocol` (`not_synod_safe_of_disjoint_quorums`, motivating §2.2), and leave both persistent-storage crash recovery and §3 state-machine replication (internal pp. 8–11, Multi-Paxos) open.

<a id="lamportshostakpease1982"></a>
## lamportshostakpease1982

Leslie Lamport, Robert Shostak and Marshall Pease.
"The Byzantine Generals Problem."
*ACM Transactions on Programming Languages and Systems* 4(3), 382–401, July 1982. https://doi.org/10.1145/357172.357176 ; author-hosted copy of the typeset article: https://lamport.azurewebsites.net/pubs/byz.pdf . Checked against that copy on 2026-11-08 UTC by worker w169-omt: §1, pp. 383–384 (conditions 1′ and 2 on the values `v(i)`, the interactive consistency conditions IC1 and IC2, and the reduction in which each general sends its value by a solution to the commander problem); §3, pp. 387–388 (the oral-message assumptions A1–A3, the default order RETREAT, the definition of `OM(m)` and of `majority`, and the remark that values are prefixed by the sequence of relaying lieutenants); p. 390 (Lemma 1: `OM(m)` satisfies IC2 with more than `2k + m` generals and at most `k` traitors; Theorem 1: `OM(m)` satisfies IC1 and IC2 with more than `3m` generals and at most `m` traitors); §7, pp. 400–401 (message paths of length up to `m + 1`, and up to `(n − 1)(n − 2)⋯(n − m − 1)` messages).

<a id="lavi07"></a>
## lavi07

Ron Lavi.
"Computationally Efficient Approximation Mechanisms."
Chapter 12 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 301–329 (blank verso p. 330; ISBN `978-0-521-87282-9`).
The library's key is `Lavi2007`.
A university-hosted PDF of the book (non-printable publisher edition, viewed as rendered page images) was consulted on 2026-11-24 for TOC p. viii, chapter opener p. 301, §12.4 (pp. 317–320), the bibliography on p. 328, and the exercises on p. 329: Definition 12.23 (affine maximizer, p. 317; note that the printed text omits the constraints `kᵢ ≥ 0` and `∃ i, kᵢ > 0` needed for Theorem 12.24), Theorem 12.24 (Roberts' theorem, p. 318), Definition 12.25 (neutrality, p. 318), Theorem 12.26 (neutral Roberts' theorem, p. 318), Definition 12.27 and Claim 12.28 (positive association of differences / PAD, p. 318), Definition 12.29 and Claim 12.30 (Generalized-WMON, pp. 318–319), equation (12.13) (`P(x, y)`, p. 319), Claims 12.31–12.32 (p. 319), Claims 12.33–12.34 (p. 320), Exercise 12.6 (implementable rule failing Generalized-WMON on a restricted domain, p. 329), and Exercise 12.8 (`γ(x, y)` shift proof completing Roberts' theorem without neutrality, p. 329).
Original article citations in this chapter (including Roberts 1979) were not inspected.

<a id="lean-validation"></a>
## lean-validation

Lean development team.
*Validating a Lean Proof*, The Lean Language Reference, accessed 2026-11-02 UTC. https://lean-lang.org/doc/reference/latest/ValidatingProofs/ . The page was inspected live; the requested version-specific URL was unavailable, and no verified archival snapshot was obtained.
Version-specific library assertions in this dossier instead rely on pinned repository sources.

<a id="lecam73"></a>
## lecam73

Lucien Le Cam.
"Convergence of Estimates Under Dimensionality Restrictions."
*The Annals of Statistics* 1(1), 38–53, 1973. https://doi.org/10.1214/aos/1193342380 . Bibliographic metadata checked via search summaries on 2026-11-11; the article text was not inspected, and no theorem number is claimed.
Cited as background origin for bounded pairwise Hellinger tests and tournament localization (`leCamBirgeTest`, `birgeTournamentSelect`).

<a id="ledouxtalagrand91"></a>
## ledouxtalagrand91

Michel Ledoux and Michel Talagrand.
*Probability in Banach Spaces: Isoperimetry and Processes*.
Ergebnisse der Mathematik und ihrer Grenzgebiete (3), vol. 23, Springer-Verlag, Berlin, 1991.
ISBN 978-3-540-52013-9.
Bibliographic metadata and the locator Theorem 4.12 (pp. 112–114, Rademacher contraction principle for convex nondecreasing functions and centered contractions `φ_i(0) = 0`) were checked against secondary search summaries on 2026-11-11 UTC; the book text was not directly inspected.
[Rademacher/Contraction](../CslibFrontier/MachineLearning/Rademacher/Contraction.lean) follows the uncentered expected-supremum proof of [mohrirostamizadehtalwalkar18](#mohrirostamizadehtalwalkar18), Section 5.4, Lemma 5.7.

<a id="lemkehowson64"></a>
## lemkehowson64

Carlton E. Lemke and Joseph T. Howson, Jr. "Equilibrium Points of Bimatrix Games."
*Journal of the Society for Industrial and Applied Mathematics* 12(2), 413–423, 1964. https://doi.org/10.1137/0112033 . Bibliographic data from the DOI record and secondary summaries; the paper's text was not consulted.
It is cited only as the origin of the algorithm.
Locators for the formalized statements follow [vonstengel07](#vonstengel07).

<a id="lempelziv76"></a>
## lempelziv76

Abraham Lempel and Jacob Ziv.
"On the Complexity of Finite Sequences."
*IEEE Transactions on Information Theory* 22(1), 75–81, 1976. https://doi.org/10.1109/TIT.1976.1055501 . Bibliographic data from the DOI record.
The paper's text was not inspected (it is paywalled).
The definitions of reproduction, production, history and exhaustive history, and the statements that the exhaustive history is unique and has the fewest components (so that the complexity `c(S)` is its number of components), were taken from secondary summaries.
No theorem numbers are cited.

<a id="leskovecrajaramanullman20"></a>
## leskovecrajaramanullman20

Jure Leskovec, Anand Rajaraman, Jeffrey D. Ullman.
*Mining of Massive Datasets*, 3rd edition.
Cambridge University Press, 2020. https://doi.org/10.1017/9781108684163 . DOI and metadata as reported by search indexes.
The section locators used here (3.3.3 minhashing and Jaccard similarity, 3.4.2 analysis of the banding technique, 3.6.1 locality-sensitive functions, 3.6.2 families for the Jaccard distance, 3.6.3 amplification, 3.7.1 families for the Hamming distance) were matched against section titles reported by secondary sources; the book text was not inspected in this pass (no connection to the authors' site).

<a id="lev86"></a>
## lev86

Leonid A. Levin.
*Average Case Complete Problems*.
SIAM Journal on Computing 15(1), 285–286, 1986. https://doi.org/10.1137/0215020 . Bibliographic metadata checked on 2026-11-07.
The manual attributes only the existence of a complete distributional problem for `(NP, PComp)` to this paper, and follows the proof of [bt06](#bt06), Theorem 19.

<a id="levinperes2017"></a>
## levinperes2017

David A. Levin and Yuval Peres (with contributions by Elizabeth L. Wilmer, and a chapter on coupling from the past by James G. Propp and David B. Wilson).
*Markov Chains and Mixing Times*, 2nd edition.
American Mathematical Society, Providence, RI, 2017. https://doi.org/10.1090/mbk/107 ; author-hosted PDF https://pages.uoregon.edu/dlevin/MARKOV/markovmixing.pdf (416 PDF pages, dated March 21, 2017, SHA-256 `9ef39f9467d9647ff3f5e8747b9ce24b7a90d13be2f8156fbd827b95b661a772`, where printed page `p` in the main text is PDF page `p + 16`).
Checked directly against that PDF on 2026-11-24 for Section 1.3 (lazy version `(I + P) / 2`, printed p. 8 / PDF p. 24), Section 12.1 (Lemma 12.1(i), `(12.1)`, Lemma 12.2 symmetric conjugation `D_π^{1/2} P D_π^{-1/2}`, and Lemma 12.3 mean-zero eigenfunctions, printed pp. 161–163 / PDF pp. 177–179), Section 12.2 (`λ_*` `(12.6)`, `γ_* = 1 - λ_*`, `γ = 1 - λ_2` `(12.7)`, variance contraction `(12.8)`, Theorem 12.4 `(12.10)` and `(12.13)`, and Theorem 12.5 `(12.14)`–`(12.15)`, printed pp. 163–164 / PDF pp. 179–180), Section 12.6 (Lemma 12.18 `ℓ²` / `χ²` bound, printed p. 172 / PDF p. 188), Chapter 12 Exercises 12.1(a), 12.3, and 12.4 (printed p. 177 / PDF p. 193), and Section 13.2.1 (`(13.2)` Dirichlet form, Lemma 13.6, Lemma 13.7 `(13.3)`, and Remark 13.8, printed pp. 181–182 / PDF pp. 197–198).
Earlier citations in `MarkovChain/` to Chapters 1, 2, 3, 4, 5, 10, and 14 use the same edition's section and theorem numbering.

<a id="lfkn92"></a>
## lfkn92

Carsten Lund, Lance Fortnow, Howard Karloff and Noam Nisan.
*Algebraic Methods for Interactive Proof Systems*.
JACM 39(4), 859–868, 1992. https://doi.org/10.1145/146585.146605 .

<a id="li2023"></a>
## li2023

Xin Li.
*Two Source Extractors for Asymptotically Optimal Entropy, and (Many) More*.
FOCS 2023, 1271–1281. https://doi.org/10.1109/FOCS57990.2023.00075 . `SumsetBridge.lean` uses ECCC TR23-023, revision 1, https://eccc.weizmann.ac.il/report/2023/023/revision/1/download/ , checked directly on 2026-11-22: Definition 1.1 (printed p. 1, explicit means polynomial-time computable) and Theorem 7.13 (printed p. 36, a one-bit sumset extractor at entropy `c(ε) log n` for every fixed error `ε > 0`).
Formalizing that construction remains the [explicit frontier extractor objective](../roadmap/circuits.md).
The fixed-error statement alone does not provide one family with vanishing error.
Other numbered locators in `AffineSource.lean`, previously taken from secondary descriptions, remain unverified against the typeset FOCS version.

<a id="liliangyuzhou2023"></a>
## liliangyuzhou2023

Tianxiao Li, Jingxun Liang, Huacheng Yu, and Renfei Zhou.
*Tight Cell-Probe Lower Bounds for Dynamic Succinct Dictionaries*.
FOCS 2023, 1842–1862. https://doi.org/10.1109/FOCS57990.2023.00112 . Section, theorem, lemma, claim, equation, and page locators follow https://arxiv.org/abs/2306.02253v3 (where printed page `p` is PDF page `p + 1`).

<a id="lindell17"></a>
## lindell17

Yehuda Lindell.
*How To Simulate It – A Tutorial on the Simulation Proof Technique*.
Electronic Colloquium on Computational Complexity, Report TR17-112, 2017. https://eccc.weizmann.ac.il/report/2017/112/ . The ECCC PDF dated June 27, 2017 was read for Section 2 (computational indistinguishability against non-uniform polynomial-time distinguishers with one negligible function for all inputs, p. 3), Section 4.2 (Definition 4.1, security against static semi-honest adversaries for two parties, p. 7) and the remark on auxiliary information (p. 9); page numbers are those printed in the report.

<a id="liptonyoung1994"></a>
## liptonyoung1994

Richard J. Lipton and Neal E. Young.
*Simple Strategies for Large Zero-Sum Games with Applications to Complexity Theory*.
STOC 1994, 734–740. https://doi.org/10.1145/195058.195447 . Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.
It is cited for the anti-checker idea; no theorem locator is claimed.

<a id="liupass20"></a>
## liupass20

Yanyi Liu and Rafael Pass.
*On One-way Functions and Kolmogorov Complexity*.
FOCS 2020, 1243–1254. https://doi.org/10.1109/FOCS46700.2020.00118 . Definition/theorem locators refer to the full version https://arxiv.org/abs/2009.11514v1 (24 PDF pages; unnumbered title page is PDF p. 1, so printed pp. 1–23 are PDF pp. 2–24; PDF SHA-256 `22fd253c7f5720739d07771b4c9a6c9639a29350abdab7192a57ee0fd3039919`).
Inspected on 2026-11-21 for Section 2.1 Definition 2.2 (`α`-weak and weak one-way function, p. 7), Section 2.4 Definition 2.6 (`μ(·)`-indistinguishability, p. 9), Section 2.5 (Shannon entropy `H(X)`, p. 9), Section 5.1 Definition 5.1 (`μ-condEP-PRG`, p. 11), Section 5.3 (pp. 14–16), and Appendix A (pp. 21–23).
Theorem 3.1 and other §§2.3 and 3 locators remain attributed to `arXiv:2009.11514v1` (pp. 8–9).

<a id="liupass2021crypto"></a>
## liupass2021crypto

Yanyi Liu and Rafael Pass.
*On the Possibility of Basing Cryptography on EXP ≠ BPP*.
CRYPTO 2021, LNCS 12825, 11–40. https://doi.org/10.1007/978-3-030-84242-0_2 . Full version ECCC TR21-056.
Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.
The Lean module documentation cites its Section 2.2 for `MKtP` and Fact 3.1 with ECCC numbering.

<a id="liupass2022ccc"></a>
## liupass2022ccc

Yanyi Liu and Rafael Pass.
*On One-Way Functions from NP-Complete Problems*.
CCC 2022, LIPIcs 234, 36:1–36:24. https://doi.org/10.4230/LIPIcs.CCC.2022.36 . Full version ECCC TR21-059.
Checked against the LIPIcs text on 2026-11-11: Theorem 1.2 (p. 36:5), the NP-completeness of the conditional problem `McK^tP[ζ]` under randomized polynomial-time reductions, where a program is a RAM machine with random access to the condition (p. 36:4); footnote 4 (p. 36:4) notes that the problem had not been considered for RAM programs before, as opposed to Turing machines.

<a id="lizhong2024"></a>
## lizhong2024

Xin Li and Yan Zhong.
*Explicit Directional Affine Extractors and Improved Hardness for Linear Branching Programs*.
CCC 2024, LIPIcs 300, 10:1–10:14. https://doi.org/10.4230/LIPIcs.CCC.2024.10 ; preprint arXiv:2304.11495.
Bibliographic metadata checked on 2026-11-11 UTC; secondary search summaries confirm Definition 21 (affine somewhere condenser), Theorem 18, and Lemma 20 in Section 3, while the full primary PDF was not read line by line, so the remaining numbered locators cited in `AffineSource.lean` and `SomewhereCondenser.lean` remain unverified against the typeset CCC version.

<a id="ll24"></a>
## ll24

Hanjun Li, Tianren Liu.
"How to Garble Mixed Circuits that Combine Boolean and Arithmetic Computations."
*Advances in Cryptology – EUROCRYPT 2024, Part VI*, LNCS 14656, Springer, 2024. https://doi.org/10.1007/978-3-031-58751-1_12 . Full version: Cryptology ePrint Archive, Report 2023/1584, https://eprint.iacr.org/2023/1584 . Checked on 2026-11-10 against the ePrint version dated 2023-10-13 (page numbers below are those printed in that version): Section 2, pp. 4–5 (digit and bit representations) and equation (1), p. 6; Section 3.1, pp. 8–9 (global offset `Δ`, labels `(Δx + A, x + α)`, and the affinization gadget simulated from the label of `xy`, p. 9); Section 4.1, Figure 5, p. 20, and Lemma 4, pp. 20–21 (bit composition); Section 4.2, pp. 21–22 (division and remainder by a constant `N`, Lemma 5, p. 22); Section 5, pp. 23–24 (CRT reconstruction, Theorem 2, p. 24).
The formalization uses additive pads over the ring where the paper uses XOR pads, and generalizes Section 5 to arbitrary pairwise coprime moduli.

<a id="lll82"></a>
## lll82

Arjen K. Lenstra, Hendrik W. Lenstra Jr. and László Lovász.
"Factoring Polynomials with Rational Coefficients."
*Mathematische Annalen* 261, 515–534, 1982. https://doi.org/10.1007/BF01457454 . Inspected the author-hosted scan https://www.math.leidenuniv.nl/~hwl/PUBLICATIONS/1982f/art.pdf on 2026-11-08: §1, conditions (1.4)–(1.5) and the remark after (1.5), Proposition (1.6) and the remark after it, Proposition (1.11), the algorithm (1.15)–(1.21), the swap formulas (1.22) and the termination argument (1.23)–(1.26).

<a id="lmms04"></a>
## lmms04

Richard J. Lipton, Evangelos Markakis, Elchanan Mossel and Amin Saberi.
"On Approximately Fair Allocations of Indivisible Goods."
*Proceedings of the 5th ACM Conference on Electronic Commerce (EC 2004)*, 125–131, ACM, 2004. https://doi.org/10.1145/988772.988792 . Bibliographic metadata checked via DOI/search records on 2026-11-24 UTC; the conference PDF was not inspected on disk, so no internal theorem or page locator is claimed.
Cited (`LiptonMarkakisMosselSaberi2004`) for envy-graph cycle elimination and the maximum-marginal-utility envy bound (`MonotoneValuation.lmmsAllocate`, `MonotoneValuation.isEF1_lmmsAllocate`, `MonotoneValuation.lmmsAllocate_val_le_add_maxMarginal`).

<a id="lokam09"></a>
## lokam09

Satyanarayana V. Lokam.
"Complexity Lower Bounds using Linear Algebra."
*Foundations and Trends in Theoretical Computer Science* 4(1–2), 1–155, 2009 (issue dated 2008; bibliography key `Lokam2009`). https://doi.org/10.1561/0400000011 ; author/course PDF https://www.cs.toronto.edu/~toni/Courses/CommComplexity/Papers/lokam-book.pdf . Checked against that PDF on 2026-11-22 (SHA-256 `8d414a15f21b2e58b6a62f8bbda7abe3e1afca5da3cdca831c1711231618edf2`): §2.1, Definition 2.1 (printed p. 11 / PDF p. 14) and the unnumbered prose immediately after Definition 2.1 (printed pp. 11–12 / PDF pp. 14–15), stating the universal upper bound `R_A^F(r) ≤ (n - r)^2` over any field (some PDF text extractors drop the underline on p. 11 and read `<`, whereas `≤ (n - r)^2` is the true bound and is attained by the `2 × 2` rational Hadamard matrix at `r = 0, 1`) and attributing to [Valiant](#valiant77) (reference `[98]`) the finite-field counting bound `R_A^F(r) = Ω((n - r)^2 / log n)` for almost all `n × n` matrices (fraction tending to `1` as `n → ∞`; formalized in `Matrix.one_sub_inv_pow_lt_card_sq_div_log_le_rigidity` with exact floor threshold `(|n| - r)^2 / (4 ⌊log_|K| |n|⌋ + 6)` and probability `> 1 - |K|^(-⌊(|n| - r)^2 / 2⌋)`, which is positive once `4 ⌊log_|K| |n|⌋ + 6 ≤ (|n| - r)^2` and gives Lokam's positive `Ω((n - r)^2 / log n)` order for fixed `K` and `r ≤ (1 - ε) |n|`, `ε > 0`); §2.2, eq. (2.3) and Theorem 2.11 (printed pp. 20–21 / PDF pp. 23–24, attributing [Midrijānis](#midrijanis05)'s block-tiling lower bound `R_{H_k}(r) ≥ n^2 / (4r)` for `n = 2^k` and power-of-two `r ≤ n / 2` over fields of characteristic `≠ 2` — with Lokam's `r = 2^{t-1}`, the `2r ≤ 2^k` restriction `t ≤ k` comes from choosing blocks of side `2^t`, which are `±S_t` by eq. (2.3) rather than that proof sentence's printed index slip `±S_{k-t}`, while Midrijānis states `r ≤ n / 2` explicitly; formalized for `r = 2^t`, `t < k` in `Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow`); and §3.2–3.2.1, Lemma 3.6, Definition 3.3, and Theorem 3.8 (printed pp. 44–46 / PDF pp. 47–49, attributing [de Wolf](#dewolf06)'s submatrix-rank and row-averaging lower bound `R_H(r) ≥ n^2 / (4r)` for generalized complex Hadamard matrices, where Lokam's printed statement of Theorem 3.8 omits `r ≤ n / 2` while selecting `2r` rows in the first sentence of its proof; formalized with `2r ≤ |n|` in `Matrix.IsHadamard.card_mul_le_rank_submatrix`, `Matrix.IsHadamard.card_sq_le_four_mul_rigidity`, `Matrix.IsHadamard.card_sq_le_four_mul_rigidity_of_trivialStar`, and `Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard`).
Also inspected in the same PDF: §2.1, Definition 2.2 (printed p. 13), Theorem 2.1 and Lemma 2.2 (printed pp. 14–15), and §2.2, Lemmas 2.3–2.4 and Theorem 2.5 (printed pp. 16–17).

<a id="louiabuamara1987"></a>
## louiabuamara1987

Michael C. Loui and Hosame H. Abu-Amara.
"Memory Requirements for Agreement Among Unreliable Asynchronous Processes."
*Advances in Computing Research* 4, 163–183, JAI Press, 1987.
Bibliographic metadata checked via secondary indexes on 2026-11-22 UTC; the full chapter text was not inspected in this pass, so no definition, theorem, or passage from this chapter is claimed.
Listed in [SharedMemory/Basic.lean](../CslibFrontier/Computability/Distributed/SharedMemory/Basic.lean) and [SharedMemory/Hierarchy.lean](../CslibFrontier/Computability/Distributed/SharedMemory/Hierarchy.lean) solely as prior shared-register impossibility work noted by Herlihy ([herlihy1991](#herlihy1991), §3.1, p. 132, ref.
`[21]`, and §3.7, p. 142); all formalized shared-memory definitions and theorems are verified against [herlihy1991](#herlihy1991).

<a id="lovasz1979"></a>
## lovasz1979

László Lovász.
*On the Shannon Capacity of a Graph*.
IEEE Transactions on Information Theory 25(1), 1–7, 1979. https://doi.org/10.1109/TIT.1979.1055985 . Bibliographic data from the DOI record.
The full text was not inspected in this pass, so no theorem numbers are quoted.
The attributed content (orthonormal representations with orthogonality on nonadjacent pairs, `ϑ`, `Θ ≤ ϑ`, submultiplicativity under strong products and `Θ(C₅) = √5`) follows [knuth1994](#knuth1994) and standard accounts.

<a id="lp09"></a>
## lp09

Yehuda Lindell, Benny Pinkas.
"A Proof of Security of Yao's Protocol for Two-Party Computation."
*Journal of Cryptology* 22(2), 161–188, 2009. https://doi.org/10.1007/s00145-008-9036-8 . Metadata checked at the publisher.
Locators refer to the ePrint version 2004/175 of June 26, 2006 (25 pages; printed and PDF page numbers agree), read on 2026-11-15 through the Internet Archive copy https://web.archive.org/web/20260925153108/https://eprint.iacr.org/2004/175.pdf (sha256 `31b6d91daed7b182793d30b47b0b21736dd477f963a732434a21b97f0f07dfe9`): Definition 1 (§2.1, p. 5), the garbled-circuit construction (§4.1, p. 12), Protocol 2 and Theorem 7 (§4.2, p. 15), and the two cases of the proof of Theorem 7, Case 1 (p. 16) and Case 2 with the simulator `S₂` (pp. 18–19).
The journal version was not inspected, and its numbering may differ.

<a id="ltv98"></a>
## ltv98

Ming Li, John Tromp and Paul Vitányi.
*Reversible Simulation of Irreversible Computation by Pebble Games*.
Physica D 120, 168–176, 1998. https://doi.org/10.1016/S0167-2789(98)00052-9 . Locators refer to arXiv:quant-ph/9703009v3 (11 April 1997), https://arxiv.org/abs/quant-ph/9703009v3 . The reversible pebble rule (Section 6), the procedures `pebble(s, n)` and `unpebble(s, n)` (Section 7), Theorem 1, Corollaries 1 and 2, Lemma 1 and Theorem 2 were checked.
The definitions of available pebbles and of weak and strong solvability, the statement and proof of Theorem 1 (including the distance estimate `2^j + 2^f + 2^(f+1) + ⋯ + 2^(j−1) ≤ 2^(j+1)`), and Corollary 1 were rechecked against the same arXiv version on 2026-11-08 for `ReversiblePathReachable.lean`.

<a id="luby1986"></a>
## luby1986

Michael Luby.
"A Simple Parallel Algorithm for the Maximal Independent Set Problem."
*SIAM Journal on Computing* 15(4), 1036–1053, 1986 (preliminary version in *STOC 1985*, 1–10). https://doi.org/10.1137/0215074 . Bibliographic metadata checked via DOI record on 2026-11-22 UTC; the paywalled SIAM journal PDF was not directly inspected, so internal theorem and page locators are not claimed.
Credited for the randomized phase-based maximal independent set paradigm formalized in centralized random-priority form in [Algorithms/Lean/LubyMIS.lean](../CslibFrontier/Algorithms/Lean/LubyMIS.lean) and in synchronous `LOCAL` message-passing form (both the 2-round-per-phase random-priority variant and the 3-round-per-phase `1 / (2 d_H(v))` degree-weighted coin-flip variant following [Wattenhofer](#wattenhofer16), §7.2–§7.3, with the good-edge orientation argument also in [Alon, Babai and Itai](#alonbabaiitai1986), Lemma 4.4) in [LocalGraph/LubyMIS.lean](../CslibFrontier/Computability/Distributed/LocalGraph/LubyMIS.lean) (steps toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505) and [#3270](https://github.com/cslib-community/cslib-frontier/issues/3270); Luby's pairwise-independent PRAM derandomization is not formalized).

<a id="lundeliuslynch1984"></a>
## lundeliuslynch1984

Jennifer Lundelius and Nancy Lynch.
"An Upper and Lower Bound for Clock Synchronization."
*Information and Control* 62(2–3), 190–204, 1984. https://doi.org/10.1016/S0019-9958(84)80033-9 . Bibliographic metadata checked via DOI/bibliography records only; the journal full text was not inspected, so no internal section, lemma or theorem numbers are cited.
Cited as background for the synchronous lockstep, drift-free `R`-round clock-synchronization steps in [`ClockSync/Basic.lean`](../CslibFrontier/Computability/Distributed/ClockSync/Basic.lean) (`LockstepProtocol`, `localView_shift_eq`, `adj_shift_eq`) and [`ClockSync/LundeliusLynch.lean`](../CslibFrontier/Computability/Distributed/ClockSync/LundeliusLynch.lean) (`lockstepClockSync_lower_bound`, `lockstepClockAvg`, `lockstepClockAvg_achievesSkew`, `exists_achievesLockstepSkew_iff`), which do not formalize the paper's general asynchronous event-driven message-passing lower bound (tracked in [#7202](https://github.com/cslib-community/cslib-frontier/issues/7202)).

<a id="lundyannakakis1994"></a>
## lundyannakakis1994

Carsten Lund and Mihalis Yannakakis.
"On the Hardness of Approximating Minimization Problems."
*Journal of the ACM* 41(5), 960–981, 1994. https://doi.org/10.1145/185675.306789 . Bibliographic metadata checked via search records only; primary text uninspected and internal theorem locators unverified (no numbered paper theorems claimed).
Cited for the constant-factor and logarithmic Set Cover inapproximability reductions from Label Cover using set-system partition gadgets.

<a id="lupanov1956"></a>
## lupanov1956

O. B. Lupanov.
"On Rectifier and Switching-and-Rectifier Schemes" (in Russian).
*Doklady Akademii Nauk SSSR* 111(6), 1171–1174, 1956.
Bibliographic metadata as cited in [sergeev2014orcomplement](#sergeev2014orcomplement) (Reference [5], pp. 1, 3); the Russian original was not inspected, so no printed page within 1171–1174 is cited (locator not verified).
English translation, "On rectifier and switching-and-rectifier circuits", hosted by Stasys Jukna: https://web.vu.lt/mif/s.jukna/boolean/lupanov56.pdf (6 pages; its footnote gives the same journal data, and Jukna's note [Lupanov's decomposition lemma](https://web.vu.lt/mif/s.jukna/boolean/Lupanov-decomposition.html) credits the translation to Igor Sergeev).
Read in that translation on 2026-11-24 UTC (SHA-256 `9ff0b51d926de7f1fb8e86c451a401a390679a68eca84c2b7f6b75f31731068b`): section 2°, the Definition of a rectifier `(p, q)`-circuit with its conditions 1)–3) (no chain between two inputs, between two outputs, or from an output to an input), the rank, and the measures `B_r(A)` and `B_r(p, q)` (PDF pp. 1–2); the unnumbered Lemma `B₂(p, q) ≤ p + q · 2^(q−1)` with its proof (PDF p. 2); Theorem 1, `B₂(pₙ, qₙ) ∼ pₙqₙ / lg₂ pₙ`, with part 1 of its proof, the upper bound (PDF p. 3).
Theorem 1 as displayed in the translation assumes `pₙ → ∞`, `pₙ ≥ qₙ` and `lg₂ pₙ / qₙ → ∞`; the upper-bound proof needs `qₙ / lg₂ pₙ → ∞`, which is the regime `log n ≪ m ≤ n` of Jukna's note (the note presents the statement as Lemma 1.2 of Jukna's book, bibliography key `Jukna2012`; the book was not inspected), and the library states the bound under that corrected condition.
[Boolean/Rectifier.lean](../CslibFrontier/Computability/Circuit/Boolean/Rectifier.lean) proves the Lemma (`exists_depth_two`) and the count of the blocked construction (`exists_depth_two_blocked_exact`), and [Boolean/Rectifier/Asymptotic.lean](../CslibFrontier/Computability/Circuit/Boolean/Rectifier/Asymptotic.lean) proves the upper bound of Theorem 1 without `pₙ ≥ qₙ` (`exists_depth_two_asymptotic_upper`, `exists_depth_two_eventually`).
The witnesses are two-layer circuits over a disjunction signature, which are `(p, q)`-circuits of rank at most two; `B₂` is not defined in the library, and the lower bound and asymptotic equivalence of Theorem 1 are not formalized.
[Rectifier/Basic.lean](../CslibFrontier/Computability/Circuit/Rectifier/Basic.lean) cites the paper as historical attribution for its rectifier-graph model, which does not impose conditions 1)–3): its `orDepthComplexity 2` is at most `B₂` and can be smaller, so `orDepthComplexity_two_le_add_mul_two_pow` and `orDepthComplexity_two_asymptotic_upper` are weaker than the Lemma and Theorem 1.

<a id="lynchshvartsman1997"></a>
## lynchshvartsman1997

Nancy A. Lynch and Alexander A. Shvartsman.
"Robust Emulation of Shared Memory Using Dynamic Quorum-Acknowledged Broadcasts."
In *Proceedings of the 27th Annual International Symposium on Fault-Tolerant Computing (FTCS '97)*, 272–281, IEEE, 1997. https://doi.org/10.1109/FTCS.1997.614100 . Locators refer to the authors' December 2, 1996 MIT Laboratory for Computer Science manuscript, https://groups.csail.mit.edu/tds/papers/Lynch/FTCS97.pdf , inspected on 2026-11-22 UTC for §4.1 (pp. 8–9, uniform two-phase fixed-quorum multi-writer multi-reader atomic register emulation using lexicographic `(seq, pid)` tags) and §4.2 with Appendix B (pp. 10–11, 22–23: Lemma 4.2 tag monotonicity, Lemmas 4.3–4.4 relating operation tags across real-time precedence, the `(tag, write-before-read)` partial order, and Theorem 4.5 atomicity; the IEEE conference text was not separately inspected).
Cited by [ABD/Basic.lean](../CslibFrontier/Computability/Distributed/ABD/Basic.lean), [ABD/Protocol.lean](../CslibFrontier/Computability/Distributed/ABD/Protocol.lean) and [ABD/Impossibility.lean](../CslibFrontier/Computability/Distributed/ABD/Impossibility.lean) as an independent cardinality-quorum envelope specialization **after** §4.1–4.2 (rather than a direct formalization of Theorem 4.5): whereas §4.1–4.2 use separate fixed read and write quorum families, a quorum-acknowledged broadcast abstraction, and a per-processor client request queue (with Theorem 4.5 proving atomicity only), `abdProtocol` runs concrete point-to-point envelope transitions with `(n - t)`-cardinality quorums and idle-only client invocations, proving `Reachable s → Linearizable v₀ s.history` (`abd_linearizable`) alongside a separate fair-crash termination theorem (`abd_terminates`) and omitting §4.3 Theorem 4.6's conditional `4d` time / `8n` message bounds and §5's dynamic quorum reconfiguration.

<a id="ma94"></a>
## ma94

Jinpeng Ma.
*Strategy-Proofness and the Strict Core in a Market with Indivisibilities*.
International Journal of Game Theory 23(1), 75–83, 1994. https://doi.org/10.1007/BF01242849 . Bibliographic metadata checked via search records on 2026-11-24 UTC; the publisher's text is paywalled and was not inspected, so no internal theorem or page locator is claimed.
Cited as the standard primary reference characterizing Gale's top trading cycles mechanism as the unique individually rational, Pareto-efficient, and strategy-proof housing mechanism (`Ma1994`), proved from first principles in `CslibFrontier/Algorithms/Lean/HousingMarket/Characterization.lean`.

<a id="mahler64"></a>
## mahler64

Kurt Mahler.
"An inequality for the discriminant of a polynomial."
*Michigan Mathematical Journal* 11(3), 257–262, 1964. https://doi.org/10.1307/mmj/1028999140 . Bibliographic metadata from `references.bib`; the Project Euclid full text was gated behind an automated challenge and was not directly inspected, so internal lemma and theorem numbers reported in secondary mathematical records (Lemma 1 for Hadamard's determinant inequality and Theorem 2 for the root-separation lower bound `|α - β| > √3 · m^{-(m+2)/2} · |D(f)|^{1/2} · M(f)^{-(m-1)}` for degree `m ≥ 2` in terms of discriminant `D(f)` and Mahler measure `M(f)`) remain unverified against the primary article.
In [`RootBound.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/RootBound.lean), `Polynomial.mignotte_sep_mahler_complex` proves the squared non-strict complex form `3 · ‖D(f)‖ ≤ ‖α - β‖² · d^{d+2} · M(f)^{2(d-1)}`, and `Polynomial.mignotte_sep_sqNorm_real` / `Polynomial.mignotte_sep_sqNorm_rat` combine it with `|D(f)| ≥ 1` for separable integer polynomials and Landau's coefficient `ℓ²` bound `M(f) ≤ ‖f‖₂`.

<a id="malkhireiter1998"></a>
## malkhireiter1998

Dahlia Malkhi and Michael Reiter.
"Byzantine Quorum Systems."
*Distributed Computing* 11(4), 203–213, 1998. https://doi.org/10.1007/s004460050050 ; author-hosted journal PDF: https://users.ece.cmu.edu/~reiter/papers/1998/DC.pdf (preliminary conference version in *Proceedings of the 29th Annual ACM Symposium on Theory of Computing (STOC '97)*, 569–578, 1997, author PDF https://users.ece.cmu.edu/~reiter/papers/1997/STOC.pdf ).
Checked on 2026-11-22 UTC against `DC.pdf` (SHA-256 `357c1f89795f0910eb3e749b92ca13b51ff4efd6fb5319e2566cf7f53a26bf45`, pp. 203–213) and `STOC.pdf` (SHA-256 `926974b6fe799a954026f1c16b725628c889fcd94f2ab34468ba8dc969299170`): Section 3.1 (p. 204, server universe $U$, non-empty pairwise-intersecting quorum system $\mathcal{Q} \subseteq 2^U$, and non-empty subset-incomparable fail-prone system $\mathcal{B} \subseteq 2^U$), Section 3.2 (p. 205, timestamped register access protocol), Section 3.3 (p. 205, Definition 3.1 load), Section 4 (pp. 205–207: Definition 4.1 `M-Consistency` $|(Q_1 \cap Q_2) \setminus B_1| > |B_2 \cap Q_2|$ and `M-Availability` $\forall B \in \mathcal{B},\, \exists Q \in \mathcal{Q},\, Q \cap B = \emptyset$, Lemma 4.2 safe-variable read-after-write correctness on p. 206, Theorem 4.3 general existence characterization $\mathcal{Q} = \{U \setminus B : B \in \mathcal{B}\}$ on p. 206, Corollary 4.4 $U \not\subseteq B_1 \cup B_2 \cup B_3 \cup B_4$ and $n > 4f$ threshold bound on p. 206, Theorem 4.5 $1/\sqrt{n}$ load lower bound on p. 207, and Example 4.6 threshold construction of size $\lceil(n + 2f + 1)/2\rceil$ on p. 207), Section 5.1 (pp. 207–208: Definition 5.1 `D-Consistency` $(Q_1 \cap Q_2) \setminus B \ne \emptyset$ and `D-Availability`, Lemmas 5.2–5.3, Theorem 5.4, Corollary 5.5 $U \not\subseteq B_1 \cup B_2 \cup B_3$ and $n > 3f$ threshold bound, and Example 5.6 threshold construction of size $\lceil(n + f + 1)/2\rceil$ on p. 208), Section 5.2 (pp. 208–210: Definition 5.9 weak-inequality `O-Consistency1` $|(Q_1 \cap Q_2) \setminus B_1| \ge |(Q_2 \cap B_2) \cup (Q_2 \setminus Q_1)|$ with `O-Consistency2` and `O-Availability`, the remark immediately below Definition 5.9 on p. 209 replacing $\ge$ by strict $>$ in `O-Consistency1` so timestamp-free majority voting suffices, Lemma 5.10 on pp. 209–210, Example 5.11 $f$-opaque threshold construction and p. 210 note that characterizing opaque-quorum existence over general $\mathcal{B}$ is an open problem, Theorem 5.12 $n \ge 5f$ for $f > 0$ under Definition 5.9's weak inequality on p. 210, and Theorem 5.14 load lower bound on p. 210), and Section 6 (pp. 210–212: faulty-client Echo/Ready update protocol, Figure 5 and Lemmas 6.2–6.7).
Cited by [QuorumSystems.lean](../CslibFrontier/Computability/Distributed/ByzantineQuorum/QuorumSystems.lean) as a uniform $b$-threshold (`thresholdAdversary P b`) step under `#7506` (`QuorumSystem` leaves nonemptiness and pairwise intersection unbundled on candidate families, deriving both from `IsThresholdDisseminationQuorumSystem`, while `thresholdAdversary P b = {F | F.card <= b}` downward-closes `{F | F.card = b}` rather than requiring Section 3.1's subset-incomparability on $\mathcal{B}$): `exists_thresholdDisseminationQuorumSystem_iff` ($3b < |P|$, threshold specialization of Corollary 5.5 and Example 5.6), `exists_thresholdMaskingQuorumSystem_iff` ($4b < |P|$, threshold specialization of Corollary 4.4 and Example 4.6), `exists_thresholdStrongOpaqueQuorumSystem_iff` ($5b < |P|$, formalizing the p. 209 strong-inequality $>$ variant `IsThresholdStrongOpaqueQuorumSystem` via `strongOpaqueThresholdQuorums` of size $\lceil(2|P| + 2b + 1)/3\rceil$ rather than Definition 5.9 / Example 5.11 / Theorem 5.12's weak-inequality $5b \le |P|$ bound), and `threshold_masking_register_max_ts_eq` / `threshold_maskingRead_eq_some_latest_write` (formalizing a $b$-threshold single-latest-write step after Lemma 4.2, leaving general non-uniform fail-prone systems $\mathcal{B}$ in Theorems 4.3 and 5.4 and Corollaries 4.4 and 5.5, weak-inequality opaque quorum systems in Definition 5.9 / Example 5.11 / Theorem 5.12, load lower bounds in Section 3.3 / Theorem 4.5 / Theorem 5.14, and Section 6 faulty-client Echo/Ready updates open in `#7506`).

<a id="manacher75"></a>
## manacher75

Glenn Manacher.
“A New Linear-Time ‘On-Line’ Algorithm for Finding the Smallest Initial Palindrome of a String.”
*Journal of the ACM* 22(3), 346–351, 1975. https://doi.org/10.1145/321892.321896 . Bibliographic data from the DOI record; the paper is behind the ACM paywall and was not inspected.
The manual credits it with the linear-time algorithm for all maximal palindromic radii as described in [apostolicobreslauergalil95](#apostolicobreslauergalil95), Section 1; its formulation is on-line, as its title and that description say, and its internal locators are not cited.

<a id="manassemcgeochsleator90"></a>
## manassemcgeochsleator90

Mark S. Manasse, Lyle A. McGeoch, Daniel D. Sleator.
"Competitive Algorithms for Server Problems."
*Journal of Algorithms* 11(2), 208–230, 1990. https://doi.org/10.1016/0196-6774(90)90003-W ; author PDF https://www.cs.cmu.edu/~sleator/papers/server-problems.pdf . Theorem 6 (lower bound `k/(k-h+1)` against `h`-server offline algorithms on a graph with at least `k + 1` nodes, proved with a lazy online algorithm, its nemesis sequence and an ensemble of offline algorithms) and Corollary 7 (no `c`-competitive algorithm for `c < k`) were checked against the author PDF on 2026-11-08.
The local lower bound is the case `h = k`.

<a id="manbermyers93"></a>
## manbermyers93

Udi Manber and Gene Myers.
"Suffix Arrays: A New Method for On-Line String Searches."
*SIAM Journal on Computing* 22(5), 935–948, 1993; preliminary version in SODA 1990. https://doi.org/10.1137/0222058 . Bibliographic data from secondary indexes and the DOI record; the journal text is behind the SIAM paywall and was not inspected.
The manual credits it with the suffix array and with the contrast between the plain `O(P log N)` binary search and the `O(P + log N)` search that reuses longest-common-prefix information, following the customary attribution; section and theorem numbers are not cited.

<a id="manin56"></a>
## manin56

Ju.
I. Manin.
"On cubic congruences to a prime modulus."
*Izvestiya Akademii Nauk SSSR.
Seriya Matematicheskaya* 20(5), 673–678, 1956 (in Russian). https://www.mathnet.ru/eng/im3844 . Bibliographic metadata was checked against secondary sources; the Math-Net.ru page itself could not be opened and the paper was not inspected.
The locators §2 (pp. 675–676: the recurrence for the heights of a sequence of points and its closed form) and Lemma 2 (p. 676: the cancellation count) were supplied by an independent reviewer who read the paper, and were not rechecked for this entry.
The Lean modules under `CslibFrontier/Foundations/AlgebraicGeometry/EllipticCurve/` adapt Manin's proof of Hasse's bound rather than transcribe it; the implementation notes of [`ManinHeight.lean`](../CslibFrontier/Foundations/AlgebraicGeometry/EllipticCurve/ManinHeight.lean) list the differences (projective rather than affine point count, reversed sequence index, a cubic that keeps its quadratic term so that characteristic three is included, and a recurrence derived from Mathlib's add-sub map).

<a id="manurangsiraghavendra2017"></a>
## manurangsiraghavendra2017

Pasin Manurangsi and Prasad Raghavendra.
“A Birthday Repetition Theorem and Complexity of Approximating Dense CSPs.”
*44th International Colloquium on Automata, Languages, and Programming (ICALP 2017)*, LIPIcs 80, 78:1–78:15, 2017. https://doi.org/10.4230/LIPIcs.ICALP.2017.78 . Bibliographic metadata checked against the LIPIcs DOI record; the paper's full text was inspected for the approximation ETHA formulation (§1.1, p. 78:5).
Used alongside [dinur2016](#dinur2016) to document the Gap Exponential Time Hypothesis adaptation (`GapETH`, `rGapETH`) in [FineGrained/GapETH.lean](../CslibFrontier/Computability/Complexity/FineGrained/GapETH.lean).

<a id="mathlib"></a>
## mathlib

Mathlib contributors.
*Mathlib*, pinned source `69552756cd8a2d2d48763cf7279fd814d6a1224d`, inspected 2026-11-01. https://github.com/leanprover-community/mathlib4/tree/69552756cd8a2d2d48763cf7279fd814d6a1224d

<a id="mattern1987"></a>
## mattern1987

Friedemann Mattern.
"Algorithms for Distributed Termination Detection."
*Distributed Computing* 2(3), 161–175, 1987. https://doi.org/10.1007/BF01782776 . Bibliographic metadata checked against the Crossref DOI record on 2026-11-22 UTC; the full text was not inspected (gated behind an automated challenge on the publisher host), so no section or theorem locators are cited.
Referenced only as bibliographic context for general non-diffusing message-counting termination detection tracked in #7286; the sequential-polling false-termination trace `exists_phantom_termination_naive_poll` in `Cslib.Distributed.DijkstraScholten` is an original 3-process counterexample constructed directly in Lean.

<a id="mattern1989"></a>
## mattern1989

Friedemann Mattern.
"Virtual Time and Global States of Distributed Systems."
In *Parallel and Distributed Algorithms*, North-Holland, 215–226, 1989; author-edited reprint PDF (paginated pp. 120–131, noting on p. 120 minor alterations from the October 1988 Chateau de Bonas / 1989 North-Holland proceedings version): http://theory.lcs.mit.edu/classes/6.852/05/papers/VirtTimeGlobStatesFull.pdf (also hosted at https://vs.inf.ethz.ch/publ/papers/VirtTimeGlobStates.pdf ).
Checked against the first copy (SHA-256 `64830b6a039f0e1840e06d1e745b8abe00d2e224b17721e2fff37731116d3bae`) on 2026-11-22 UTC by worker `vector-clocks` (the North-Holland book pagination pp. 215–226 was not separately inspected): §2 "Event structures", p. 121 (internal, send, and receive events and conditions (1)–(3) for `<`); §3 "Consistent cuts", p. 123 (Definition 3 left-closed cuts, absence of unsent received messages, and Theorem 2 `∪`/`∩` sublattice closure); §7 "Vector time", pp. 126–127 (local increment `C_i[i] := C_i[i] + 1` and componentwise `sup(C_i, t)` merge — note `vcNext` merges `sup(cur, msg)` before incrementing `p`'s entry, which yields the identical vector on every valid execution because `msg[p] ≤ cur[p]` by Theorem 5, p. 127; Definition 4 vector relations `≤`, `<`, and reflexive vector concurrency `¬(u < v) ∧ ¬(v < u)`, whereas `Execution.Concurrent` follows Lamport's irreflexive event concurrency `¬(e₁ ≤ e₂) ∧ ¬(e₂ ≤ e₁)` and agrees with `¬(vc e₁ < vc e₂) ∧ ¬(vc e₂ < vc e₁)` on distinct events by `vc_injective`; Definition 5 and Theorem 6, p. 127, consistent-cut frontier criterion `t_X = (C(c_1)[1], …, C(c_n)[n])` assuming an event `frontier p` on each process); and §8 "The structure of vector time", pp. 127–128 (Theorem 10 `e < e' ↔ C(e) < C(e')` and Theorem 11 single-coordinate comparison of given timestamps `e < e' ↔ C(e)[i] ≤ C(e')[i]` for `e' ≠ e` with `e` at `P_i`).
The non-FIFO snapshot algorithm (§11, pp. 129–131) is not formalized here.
Cited by [VectorClock/Basic.lean](../CslibFrontier/Computability/Distributed/VectorClock/Basic.lean), [VectorClock/Clocks.lean](../CslibFrontier/Computability/Distributed/VectorClock/Clocks.lean) and [VectorClock/LowerBound.lean](../CslibFrontier/Computability/Distributed/VectorClock/LowerBound.lean) for `Execution.IsConsistentCut`, `Execution.vc`, `happensBeforeLe_iff_coord_le`, `happensBefore_iff_coord_le`, `happensBefore_iff_vc_lt`, and `isConsistentCut_cutOfFrontier_iff`.

<a id="may52"></a>
## may52

Kenneth O. May.
"A Set of Independent Necessary and Sufficient Conditions for Simple Majority Decisions."
*Econometrica* 20(4), 680–684, 1952. https://doi.org/10.2307/1907651 . Library bibliography key `May1952`.
Bibliographic metadata checked in [fey04](#fey04) (References, p. 27) and against the DOI record on 2026-11-24 UTC; the published *Econometrica* text is paywalled and was not inspected directly, so no internal theorem numbers are claimed.
The axioms (anonymity, neutrality, and positive responsiveness) were checked against [fey04](#fey04) (§1, p. 1; §2, Definition 1, p. 5; Definition 2, p. 7), and [SocialChoice/May.lean](../CslibFrontier/GameTheory/SocialChoice/May.lean) proves the characterization on both strict profiles (`SocialWelfareFunction`) and weak individual rankings (`WeakSocialWelfareFunction`, allowing individual indifference as in May's three-valued ballots) for arbitrary finite electorates.

<a id="mccreightmeyer69"></a>
## mccreightmeyer69

Edward M. McCreight and Albert R. Meyer.
*Classes of Computable Functions Defined by Bounds on Computation: Preliminary Report*.
Proceedings of the First Annual ACM Symposium on Theory of Computing (STOC '69), 79–88, 1969. https://doi.org/10.1145/800169.805423 . Bibliographic metadata checked on 2026-11-08; the paper is behind the ACM paywall and was not inspected.
The manual attributes the union, naming and honesty theorems to it, following the customary attribution; Odifreddi's textbook [odifreddi99](#odifreddi99) attributes the Naming Theorem VII.3.6 and the Union Theorem VII.3.7 to it.
The paper's own theorem numbers and exact hypotheses are unverified.
Odifreddi states the union theorem for a uniformly recursive sequence `t_n` with `t_n(x) ≤ t_{n+1}(x)` for all `n` and `x`, which is the hypothesis of `union_theorem`.
Secondary accounts state the union theorem for a recursively enumerable "self-bounded" set of bounds, in which every finite subset is dominated almost everywhere by a member; this would match `union_theorem_of_directed`, but it has not been checked against the paper, so the library derives the directed and almost-everywhere variants from the pointwise `union_theorem`.
The open survey by Hartmanis and Hopcroft (Cornell TR70-59, https://hdl.handle.net/1813/5918) is an image scan that was not read in this pass.

<a id="mckaymurraywilliams2019"></a>
## mckaymurraywilliams2019

Dylan McKay, Cody D. Murray and R. Ryan Williams.
*Weak Lower Bounds on Resource-Bounded Compression Imply Strong Separations of Complexity Classes*.
STOC 2019, 1215–1225. https://doi.org/10.1145/3313276.3316396 . Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.

<a id="menger27"></a>
## menger27

Karl Menger.
"Zur allgemeinen Kurventheorie."
*Fundamenta Mathematicae* 10, 96–115, 1927.
Cited for attribution only: the paper was not consulted, and the formal statements follow [schrijver17](#schrijver17) and [diestel25](#diestel25).

<a id="micciancioregev2007"></a>
## micciancioregev2007

Daniele Micciancio and Oded Regev.
"Worst-Case to Average-Case Reductions Based on Gaussian Measures."
*SIAM Journal on Computing* 37(1), 267–302, 2007. https://doi.org/10.1137/S0097539705447360 . Author's copy dated December 27, 2005 (`https://cseweb.ucsd.edu/~daniele/papers/Gaussian.pdf`) inspected on 2026-11-20 (cross-checked against the December 14, 2005 copy at `https://cims.nyu.edu/~regev/papers/average.pdf`): Definition 2.1 (half-`L¹` statistical distance, pp. 5–6), Lemma 2.9 (shifted-vs-centered mass monotonicity, p. 9), Lemma 2.10 (Banaszczyk's centered and shifted Gaussian tails, p. 9), Definition 3.1 (the smoothing parameter `η_ε(Λ)`, p. 10), Lemma 3.2 (`η_{2^{-n}}(Λ) ≤ √n / λ₁(Λ*)`, pp. 10–11), Lemma 4.1 (uniformity modulo a lattice for arbitrary centers, p. 12), and Lemma 4.4 (off-center discrete Gaussian sample-norm tail bound, p. 15).
In `Gaussian.OffCenterTail`, the shifted tail sharpens eq. (6) of Lemma 2.10 by removing the factor of `2`, and `ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_smoothingParameter_le` (together with its dual-mass form `ZLattice.discreteGaussian_norm_sub_gt_sqrt_lt_of_dual_mass_le`) proves Lemma 4.4 under `η_ε(L) ≤ s`, strengthening `(1 / 2) ^ n` to strict `(1 / 4) ^ n`.
In `Gaussian.Quotient`, `ZLattice.tvDist_gaussian_shift_quotient_le` and `ZLattice.tvDist_gaussian_shift_quotient_le_of_smoothingParameter_le` use Mathlib's full-`L¹` `tvDist` convention (twice the source's half-`L¹` statistical distance `Δ`).
In `Gaussian.SmoothingParameter`, `ZLattice.smoothingParameter` uses the same reciprocal-width dual sum `ρ_{1/s}(L* \ {0})` and handles dimension zero explicitly (`η_ε(L) = 0`).
Lemma 2.11 (expected squared norm of linear combinations of independent random vectors, p. 10, in `Foundations.Probability.IndependentSumNorm`), Lemma 4.2 (first and second directional moments of discrete Gaussians, pp. 13–14), and Lemma 4.3 (norm of mean and expected squared norm of discrete Gaussians, p. 14) are also used: in `Gaussian.MomentsDiscrete`, the Lemma 4.2 and 4.3 theorems are provided in both smoothing-parameter form (`2 * η_ε(L) ≤ s`, `0 < ε < 1`) and dual-mass form (`ρ_{2/s}(L* \ {0}) ≤ ε < 1`).
Also used (inspected on 2026-11-21): Lemma 2.9 (`ρ_{s,c}(Λ) ≤ ρ_s(Λ)`, p. 9) and Lemma 3.3 (`η_ε(Λ) ≤ √(ln(2n(1 + 1/ε)) / π) · λ_n(Λ)`, pp. 11–12; p. 11 in the December 14, 2005 copy).
In `Gaussian.ShiftBounds`, `ZLattice.gaussianMass_le_gaussianMass_zero` generalizes Lemma 2.9 to arbitrary discrete `ℤ`-submodules; in `Gaussian.SuccessiveMinimum`, `ZLattice.smoothingParameter_le_sqrt_log_mul_successiveMinimum` (together with its dual-mass core `ZLattice.gaussianMass_dual_sub_one_le_of_successiveMinimum`) proves Lemma 3.3 (handling dimension zero explicitly and excluding the asymptotic `ω(log n)` remark).
The worst-case-to-SIS modules also use (inspected on 2026-11-21): Definition 2.6 (`GIVP^φ_γ`, §2, p. 7), Definition 2.7 (`GDD^φ_γ`, §2, p. 7), §2 (prose remark on fine-grid discretization, p. 8), Definition 5.1 (`ℓ₂`-SIS, §5.1, p. 17), Lemma 5.2 (existence of `ℓ₂`-SIS solutions for `β ≥ √m · q^{n/m}`, §5.1, p. 17), Definition 5.3 (`SIS_{q, m, β}` ensemble, §5.1, p. 17), Definition 5.6 (`IncGDD^φ_{γ, g}`, §5.2, p. 19), Lemma 5.7 (sampling lemma, §5.2, p. 20), Lemma 5.8 (combining procedure, §5.2, pp. 20–21), Theorem 5.9 (`IncGDD` to `ℓ₂`-SIS reduction, §5.2, pp. 22–24), and Lemma 5.10 (finite deterministic and guarded lattice basis shortening step from `IncGDD^φ_{γ, 8}` to `GIVP^φ_{8γ}`, §5.3, p. 24).
In `Lattice.GIVP`, `IncGDD.IsSolution` uses Mathlib's canonical `Pi` supremum norm `‖S‖` (`max_i ‖S i‖` in positive rank, `0` in rank `0`).
In `SIS.Ell2`, `SISEll2` reuses `SISParams` (integer `P.β`) and `SISParams.Solver.IsPPT`, while `SIS.IsEll2Solution`, `sisEll2Experiment`, and `sisEll2Advantage` accept arbitrary real bounds `β : ℝ`.
In `SIS.MR07Core`, Lemmas 5.7 and 5.8 and the single-call core of Theorem 5.9 are formalized on the fine discrete grid `G_q = (1 / q) ℤⁿ` (choosing the discretization parameter equal to the SIS modulus `q` is this module's representation choice, following the prose remark in §2, p. 8) with ideal samplers, an HNF-free `(ℤ / D ℤ)ⁿ` quotient surjection (`D = |det(B⁻¹ S)|`), and the dual-mass premise `ρ_{2/s}(L(B)* \ {0}) ≤ ε`; strict-PPT realization and amplification are not formalized there.
In `Lattice.MR07Shorten`, the orthogonal shortening target `ratOrthoTarget` avoids real square roots via exact rational kernel elimination (`ratKernelBasis`) and integer square roots (`Nat.sqrt`), and only the finite deterministic/guarded shortening step is formalized here (probabilistic amplification and strict-PPT accounting are separate work).
In `Crypto.Computational.SIS.MR07Samplers`, `sampleGridGaussian` and `sampleQuotientModS` provide the finite-precision grid Gaussian and HNF-free quotient sampling primitives supporting Lemmas 5.7–5.8, together with typed-law bridges to `idealGridSample` on `GridRep B q × intLattice B` (via `decodeGridPair`) and to `PMF.uniformOfFintype (SublatticeQuot B S)` (via `decodeSublatticeQuot`).

<a id="midrijanis05"></a>
## midrijanis05

Gatis Midrijānis.
*Three lines proof of the lower bound for the matrix rigidity*. arXiv:cs/0506081v1 (20 June 2005), https://arxiv.org/abs/cs/0506081v1 (bibliography key `Midrijanis2005`).
Checked against the arXiv:cs/0506081v1 LaTeX source (`rigidity.tex`, SHA-256 `4e211e164ef44b2093ef8a2e58c3f5b7a22d675d57f5a7e8fb0da68ab5a12b95`) and S. V. Lokam's *Complexity Lower Bounds using Linear Algebra* (`Lokam2009`, https://www.cs.toronto.edu/~toni/Courses/CommComplexity/Papers/lokam-book.pdf , SHA-256 `8d414a15f21b2e58b6a62f8bbda7abe3e1afca5da3cdca831c1711231618edf2`) on 2026-11-22: §1.3 (`rigidity.tex`, lines 159–182, Kronecker definition of the `n = 2^k` Sylvester matrix `S(n)`, matching `Lokam2009`, §2.2, eq. (2.3) on printed p. 20 / PDF p. 23) and §2, Theorem 1 (`rigidity.tex`, lines 190–205: if `S(n)` is a Sylvester matrix and `r ≤ n / 2` is a power of `2`, then `R_{S(n)}(r) ≥ n² / (4r)` by partitioning into `(n / (2r))²` blocks of `± S(2r)`; reproduced in `Lokam2009`, §2.2, Theorem 2.11 on printed pp. 20–21 / PDF pp. 23–24, where with Lokam's `r = 2^{t-1}` the `2r ≤ 2^k` restriction `t ≤ k` comes from choosing blocks of side `2^t`, which are `± S_t` by eq. (2.3) rather than that proof sentence's printed index slip `± S_{k-t}`).
Formalized in [`Rigidity/Hadamard.lean`](../CslibFrontier/Foundations/LinearAlgebra/Matrix/Rigidity/Hadamard.lean) over every field `K` with `(2 : K) ≠ 0` (`Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard_two_pow`), and extended to arbitrary integers `1 ≤ r` with `2r ≤ 2^k` in characteristic zero (`Matrix.two_pow_le_four_mul_rigidity_sylvesterHadamard`) via [`dewolf06`](#dewolf06).

<a id="mignonressayre04"></a>
## mignonressayre04

Thierry Mignon and Nicolas Ressayre.
*A quadratic bound for the determinant and permanent problem*.
International Mathematics Research Notices 2004(79), 4241–4253, 2004. https://doi.org/10.1155/S1073792804142566 . Bibliographic metadata checked on 2026-11-08; the publisher copy was not inspected, so no theorem number is claimed.
The statement (`dc(perm_n) ≥ n²/2` in characteristic zero), the point `X₀` (all ones with `1 - n` in one corner), and the two Hessian lemmas were checked against R. Saptharishi, *A survey of lower bounds in arithmetic circuit complexity*, chapter "Determinantal Complexity Lower Bounds" (Theorem `thm:Mignon-Ressayre-mainthm`, Lemmas `lem:MR-det-ub` and `lem:MR-perm-lb`), at GitHub revision `af95c539`.
The full rank of the Hessian at `X₀` is proved in the library by its own sandwich-identity argument, not by the survey's eigenvalue or block-matrix computation.

<a id="mignotte82"></a>
## mignotte82

Maurice Mignotte.
"Some Useful Bounds."
In Bruno Buchberger, George E. Collins and Rüdiger Loos (eds.), *Computer Algebra: Symbolic and Algebraic Computation*, Computing Supplementum 4, 259–263, Springer, 1982. https://doi.org/10.1007/978-3-7091-7551-4_16 ; copy inspected in outside-fleet review ([#7735](https://github.com/cslib-community/cslib-frontier/pull/7735#pullrequestreview-6016516231)): https://web.dm.unipi.it/gianni/TC%26C/Mignotte.pdf . Theorem 3 (printed pp. 260–261) and Theorem 5 together with its integral corollary (printed p. 262) supply the Landau norm comparison and root-separation ingredients (`Polynomial.mignotte_sep_sqNorm_real`, `Polynomial.mignotte_sep_sqNorm_rat` in [`RootBound.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/RootBound.lean)), paired with [`mahler64`](#mahler64) (pp. 257–262, internal equation locator unverified).
These root-separation ingredients govern `mignotteBisectionDepth` and are distinct from the library's own end-to-end `List ℚ` Sturm-bisection implementation and polynomial-time Turing-machine certification ([`TotalIsolation.lean`](../CslibFrontier/Foundations/Algebra/Polynomial/RealRoot/TotalIsolation.lean), [`RootIsolation.lean`](../CslibFrontier/Computability/Complexity/RealAlgebraic/RootIsolation.lean)).

<a id="millerresnickzeckhauser05"></a>
## millerresnickzeckhauser05

Nolan Miller, Paul Resnick and Richard Zeckhauser.
"Eliciting Informative Feedback: The Peer-Prediction Method."
*Management Science* 51(9), 1359–1373, 2005 (bibliography key `MillerResnickZeckhauser2005`). https://doi.org/10.1287/mnsc.1050.0379 . Checked against the June 15, 2004 working-paper PDF (pp. 4–11) together with [friedmanresnicksami07](#friedmanresnicksami07), §27.4 (pp. 685–688) on 2026-11-24: §2 Eq. `(1)` (Bayes–Nash reporting condition), §2.1 stochastic relevance definition and Proposition 1 (truthful reporting as a strict Bayes–Nash equilibrium under peer-prediction scoring), §2.2 Proposition 2 (positive affine scaling `α > 0` to overcome fixed signal-acquisition effort cost `c > 0`), and §2.3 Eq. `(4)` (ex-post budget-balanced net transfers `τ_i(a) = τ_i^*(a_i, a_{r(i)}) - τ_{b(i)}^*(a_{b(i)}, a_{r(b(i))})` for `b(i) ≠ i` and `r(b(i)) ≠ i` when `|I| ≥ 3`); journal pagination from the DOI record.
Cited in [PeerPrediction.lean](../CslibFrontier/GameTheory/Reputation/PeerPrediction.lean).

<a id="mironov17"></a>
## mironov17

Ilya Mironov.
"Rényi Differential Privacy."
*2017 IEEE 30th Computer Security Foundations Symposium (CSF)*, 263–275, IEEE, 2017. https://doi.org/10.1109/CSF.2017.11 ; preprint arXiv:1702.07476v3, https://arxiv.org/abs/1702.07476v3 . Checked against the arXiv:1702.07476v3 LaTeX source (`renyi.tex`, SHA-256 `3b43d215025874ad33c3ad5ff9b75360a3f815909f016bdf93508dafb5a44fef`) on 2026-11-22: Definitions 1–2 (pure and approximate differential privacy), Definition 3 (Section III, Rényi divergence `D_α(P ‖ Q)` of order `α > 1` in natural logarithms, with `α = 1` defined by the KL limit), Definition 4 (Section III, `(α, ε)`-Rényi differential privacy), Section III "Post-processing" (`D_α(g(P) ‖ g(Q)) ≤ D_α(P ‖ Q)`), Proposition 1 (Section III, adaptive sequential composition), Proposition 3 (Section IV, conversion from `(α, ε)`-RDP to `(ε + log(1/δ)/(α - 1), δ)`-DP), Section V Lemma 1 (`2 α ε²`, citing [bunsteinke16](#bunsteinke16), Proposition 3.3 for the sharp `α ε² / 2` bound), Proposition 5 (Section VI-A, randomized response), and Appendix A (nonnegativity `0 ≤ D_α(P ‖ Q)`).
IEEE CSF page numbers and DOI were taken from the bibliographic record.

<a id="mirroknivetta04"></a>
## mirroknivetta04

Vahab S. Mirrokni and Adrian Vetta.
"Convergence Issues in Competitive Games."
*Approximation, Randomization, and Combinatorial Optimization: Algorithms and Techniques (APPROX/RANDOM 2004)*, Lecture Notes in Computer Science 3122, 183–194, Springer, 2004 (bibliography key `MirrokniVetta2004`). https://doi.org/10.1007/978-3-540-27821-4_17 . Bibliographic metadata from `references.bib` and the Chapter 19 bibliography of [Tardos and Wexler](#tardoswexler07) (p. 513); the full text was not inspected firsthand, so no internal section or theorem locator in this paper is claimed (`unverified` in [Entries/UtilityGame.lean](../CslibFrontierResults/Entries/UtilityGame.lean)).
Cited via [Tardos and Wexler](#tardoswexler07), §19.4.5 and §19.5.3 (pp. 506, 511), for random best-response welfare guarantees in monotone basic utility games ([UtilityGame/Basic.lean](../CslibFrontier/GameTheory/UtilityGame/Basic.lean)).

<a id="mirsky1971"></a>
## mirsky1971

L. Mirsky.
"A Dual of Dilworth's Decomposition Theorem."
*The American Mathematical Monthly* 78(8), 876–877, 1971. https://doi.org/10.1080/00029890.1971.11992886 . Bibliographic metadata from search summaries, checked on 2026-11-08; the paper is paywalled and was not inspected.
The library attributes to it only the finite chain–antichain duality, whose formal statement and height-function proof follow [Schrijver's lecture notes](#schrijver17), Theorem 7.5.

<a id="mishrasanthanam2026revision1"></a>
## mishrasanthanam2026revision1

Om Swostik Mishra and Rahul Santhanam.
*An Explicit `4n - O(log n)` Size Lower Bound against General Boolean Circuits*.
ECCC TR26-260, revision 1, 2026. https://eccc.weizmann.ac.il/report/2026/260/revision/1/download/ . Checked directly on 2026-11-22: Theorem 1.1 (printed p. 2, an explicit `P` lower bound), Theorem 4.1 (printed p. 21, the `4n - 10d` affine-disperser bound and a `poly(n, 2^d)` refuter for polynomial-time dispersers), and Remark 4.3 (printed p. 26, coefficient-`4` optimality for the paper's `s + βq + αI` potential estimates).
The `4n - 9d`, binary-cost and bigraded-potential results in `AffineDisperser4n.lean` and `AffineDisperser4n/Corollary.lean` are local refinements, not the cited endpoints.
This check does not identify the inaccessible STOC submission with this revision or verify every intermediate lemma attribution.

<a id="mishrasanthanam2027"></a>
## mishrasanthanam2027

Om Swostik Mishra and Rahul Santhanam.
*An Explicit `4n - O(log n)` Size Lower Bound against General Boolean Circuits*.
STOC 2027 submission 1241, 2027. https://stoc2027.sigact-ec.workers.dev/submissions/1241.pdf . The submission PDF was inaccessible in this pass (HTTP error 1042) and was not inspected directly; bibliographic details and cited labels (`Lemma 2.2`, `Theorem 4.1`, `Lemma 4.2`, `Remark 4.3`, and the `Theorem 1.1` target) come from repository issue `#4322` and remain unverified against that submission.
The separately checked public revision is recorded in [mishrasanthanam2026revision1](#mishrasanthanam2026revision1).

<a id="mishrasanthanam26"></a>
## mishrasanthanam26

Om Swostik Mishra and Rahul Santhanam.
*An Explicit `3.5n - o(n)` Size Lower Bound against General Boolean Circuits*.
Electronic Colloquium on Computational Complexity (ECCC) TR26-260, 2026, https://eccc.weizmann.ac.il/report/2026/260/ . Bibliographic metadata as in the library bibliography; the primary text was not directly inspected.

<a id="misragries82"></a>
## misragries82

Jayadev Misra, David Gries.
“Finding Repeated Elements.”
*Science of Computer Programming* 2(2), 143–152, 1982. https://doi.org/10.1016/0167-6423(82)90012-0 . Bibliographic data from search summaries of the DOI record; the Misra–Gries statements formalized here follow the presentation of [chakrabarti25](#chakrabarti25), Unit 1.
The journal text was not inspected in this pass.

<a id="mithardnessgroup2026sh"></a>
## mithardnessgroup2026sh

MIT Hardness Group, Josh Brunner, Erik D. Demaine, Fabian Frei, Timothy Gomez, Markus Hecher, Jeffery Li and Jayson Lynch.
*ETH is Dead, Long Live SH*. arXiv:2611.02650v2, 16 November 2026.
[Versioned PDF](https://arxiv.org/pdf/2611.02650v2).
The independent source review checked §1 and footnotes 1–2 (pp. 1–2) for the decision SH input-size conventions, §2.1, Lemma 2.1 (p. 5) for the decision fixed-width size formulation, and §3, Theorem 3.1 (p. 8) for exponent transfer.
The library uses occurring variables in `CNF ℕ` and allows polynomial overhead in the native binary encoding length.
The counting half of Lemma 2.1 is tracked in [#8457](https://github.com/cslib-community/cslib-frontier/issues/8457).
[Independent review](https://github.com/cslib-community/cslib-frontier/pull/8539#pullrequestreview-6055020260).

<a id="mitzenmacherupfal17"></a>
## mitzenmacherupfal17

Michael Mitzenmacher and Eli Upfal.
*Probability and Computing: Randomization and Probabilistic Techniques in Algorithms and Data Analysis*, 2nd edition.
Cambridge University Press, 2017.
The locator Section 1.3, Theorem 1.4 (an incorrect product survives a uniform `0`/`1` vector with probability at most `1/2`) was checked against secondary descriptions on 2026-11-07; the full text was not inspected in this pass.

<a id="mohrirostamizadehtalwalkar18"></a>
## mohrirostamizadehtalwalkar18

Mehryar Mohri, Afshin Rostamizadeh and Ameet Talwalkar.
*Foundations of Machine Learning*, 2nd edition.
MIT Press, 2018.
ISBN 978-0-262-03940-6; https://cs.nyu.edu/~mohri/mlbook/ . Bibliographic metadata from `references.bib`; Chapter 3 locators (Definitions 3.1–3.2, Theorem 3.3, Lemma 3.4, Theorem 3.5, Theorem 3.7, Corollaries 3.8, 3.9, 3.18 and 3.19) and Section 5.4 locators (Definitions 5.5–5.6 for the `ρ`-margin loss and empirical margin loss, Lemma 5.7 for uncentered Talagrand contraction, and Theorem 5.8, (5.39)–(5.40) for fixed-`ρ` Rademacher margin generalization bounds) were checked against secondary search summaries on 2026-11-11 UTC; the printed book PDF was not directly inspected in this pass.
Theorem 7.2 (AdaBoost's empirical error, p. 149) and Corollary 7.5 were read in a PDF of the book on 2026-11-13.
The library formalizes these results on finite `PMF` sample spaces and assumes uniform boundedness on real-valued hypothesis classes so that real conditional suprema `⨆` are bounded above.

<a id="moirshavit2007"></a>
## moirshavit2007

Mark Moir and Nir Shavit.
"Concurrent Data Structures."
Chapter 47 of Dinesh P. Mehta and Sartaj Sahni (eds.), *Handbook of Data Structures and Applications*, Chapman and Hall/CRC, 2004; revised author preprint (2007), https://people.csail.mit.edu/shanir/publications/concurrent-data-structures.pdf (32 pages, chapter-numbered pp. 1-1 to 1-32; SHA-256 `38c6fe1fdda2f2ad981127432e765733991bce415c19ba87b1cd9e7847a7a56b`; bibliography key `MoirShavit2007`).
Inspected the 2007 preprint PDF on 2026-11-22 UTC: Section 1.1.3 (pp. 1-5 to 1-6, wait-free, lock-free, and obstruction-free progress conditions, their containment hierarchy, and `CAS` retry-loop starvation separating lock-freedom from wait-freedom) and Section 1.3 (pp. 1-15 to 1-16, Treiber's lock-free `CAS` stack and the ABA problem with version-numbered head pointers).
Cited by [ConcurrentObjects/Progress.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/Progress.lean) and [ConcurrentObjects/TreiberStack.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/TreiberStack.lean).

<a id="monderershapley96"></a>
## monderershapley96

Dov Monderer and Lloyd S. Shapley.
*Potential Games*.
Games and Economic Behavior 14(1), 124–143, 1996. https://doi.org/10.1006/game.1996.0044 . The published text was consulted on 2026-11-07 for the definitions (2.1)–(2.3), Lemmas 2.1, 2.3, 2.5 and 2.7, Corollary 2.2, Theorem 3.1 and footnote 12, and checked again against the *Games and Economic Behavior* PDF on 2026-11-24 ([PR #8098](https://github.com/cslib-community/cslib-frontier/pull/8098#issuecomment-7139462024)) for Section 2 (Prisoner's Dilemma on p. 128, counterexample `G₁` on p. 129, Corollary 2.6 on p. 130, Theorem 2.8 and Corollary 2.9 on pp. 130–131, and Lemma 2.10 with equation (2.4) on pp. 131–132) and Appendix A (pp. 138–139, proof of Theorem 2.8).
In [Strategic/PotentialCharacterization.lean](../CslibFrontier/GameTheory/Strategic/PotentialCharacterization.lean), all game definitions are stated in cost-minimization form (with reversed inequalities relative to payoffs), `CostGame.IsWeightedPotential` omits positivity `0 < w i` relative to equation (2.2) (supplying `0 < w i` explicitly where needed and generalizing Lemma 2.10 to arbitrary `w : ι → ℝ`), and the coordination–dummy decomposition (`CostGame.IsCoordination`, `CostGame.IsDummy`, `CostGame.exists_isExactPotential_iff_coordination_add_dummy`) is proved algebraically without citing Appendix B.

<a id="mosertardos10"></a>
## mosertardos10

Robin A. Moser and Gábor Tardos.
“A Constructive Proof of the General Lovász Local Lemma.”
*Journal of the ACM* 57(2), Article 11, 2010. https://doi.org/10.1145/1667053.1667060 . Open version: arXiv:0903.0544v3, https://arxiv.org/abs/0903.0544 . Theorems 1.1–1.4, the Section 2 definitions of the log and witness trees, Lemma 2.1 and the Section 3 counting argument (Lemma 3.1) were checked against the arXiv v3 PDF (dated 20 May 2009) on 2026-11-08; Section 6 (lopsidependency, Lemma 6.2, Theorem 6.1, and the conflict-graph CNF application) was checked against the same arXiv v3 PDF on 2026-11-11.
The JACM article numbering was not checked against the typeset journal version.

<a id="mosselroch07"></a>
## mosselroch07

Elchanan Mossel and Sébastien Roch.
"On the Submodularity of Influence in Social Networks."
*Proceedings of the Thirty-Ninth Annual ACM Symposium on Theory of Computing (STOC 2007)*, 128–134, 2007. https://doi.org/10.1145/1250790.1250811 . Bibliographic metadata taken from [kleinberg07](#kleinberg07) (Bibliography, p. 632, cited as "to appear in STOC 2007") and the DOI record; the full text was not inspected firsthand, so internal theorem and page locators are left unverified.
Cited through [kleinberg07](#kleinberg07), Section 24.4, Theorem 24.6 (p. 626), for global submodularity of expected influence in the General Threshold Model whenever all local threshold functions `g_v` are monotone, normalized (`g_v(∅) = 0`), and submodular; [InfluenceMaximization.lean](../CslibFrontier/GameTheory/Network/InfluenceMaximization.lean) (`GeneralThresholdModel.isSubmodular_integral_thresholdFinal`, `GeneralThresholdModel.isSubmodular_influence`) proves this via a measure-preserving conditional reflection coupling on `[0, 1]^V`.

<a id="motzkinstraus1965"></a>
## motzkinstraus1965

T. S. Motzkin and E. G. Straus.
"Maxima for Graphs and a New Proof of a Theorem of Turán."
*Canadian Journal of Mathematics* 17, 533–540, 1965. https://doi.org/10.4153/CJM-1965-053-6 . Bibliographic metadata checked via DOI and secondary search summaries on 2026-11-10; the published text is uninspected.
The manual attributes to this paper the characterization `max_{x ∈ Δ} xᵀ A_G x = 1 - 1 / ω(G)` over the standard simplex (noting the factor-of-2 convention `∑_{ij ∈ E} x_i x_j = (1 / 2) xᵀ A_G x`); no internal theorem or section numbers are cited.

<a id="moulin80"></a>
## moulin80

Hervé Moulin.
"On Strategy-Proofness and Single Peakedness."
*Public Choice* 35(4), 437–455, 1980. https://doi.org/10.1007/BF00128122 . Bibliographic metadata checked against `references.bib` (`Moulin1980`) and secondary search summaries on 2026-11-10; the full text was not inspected, so no internal theorem numbers are claimed.
Cited in [the mechanism-design chapter](algorithms-and-memory/mechanism-design.md) via [procacciatennenholtz13](#procacciatennenholtz13) (§3.1, p. 18:8) for group strategyproofness of fixed order-statistic (generalized median) rules on the real line (PT note the weak notion; the library proves the strong variant directly).

<a id="moulinshenker2001"></a>
## moulinshenker2001

Hervé Moulin and Scott Shenker.
"Strategyproof Sharing of Submodular Costs: Budget Balance versus Efficiency."
*Economic Theory* 18(3), 511–533, 2001. https://doi.org/10.1007/PL00004200 . Bibliographic metadata checked via DOI and secondary search summaries on 2026-11-24; the published PDF was not inspected directly, so internal page and theorem numbers are not claimed.
Cited by [MulticastCostSharing.lean](../CslibFrontier/GameTheory/Cooperative/MulticastCostSharing.lean) for the per-link Shapley cost-sharing mechanism on submodular multicast games, impossibility of combining strategyproofness, voluntary participation, no positive transfers, exact budget balance, and social-welfare maximization on excludable public goods, and the tight `(H_n - 1) C` minimax worst-case additive welfare-loss bound for `1`-budget-balanced cross-monotonic Moulin mechanisms.

<a id="mullersatterthwaite77"></a>
## mullersatterthwaite77

Eitan Muller and Mark A. Satterthwaite.
"The Equivalence of Strong Positive Association and Strategy-Proofness."
*Journal of Economic Theory* 14(2), 412–418, 1977. https://doi.org/10.1016/0022-0531(77)90140-5 . Bibliographic data from secondary search summaries on 2026-11-08 UTC; the paper was not inspected.
It is cited, from secondary accounts, for the equivalence of strategy-proofness and Maskin monotonicity (strong positive association) and for the theorem that a Maskin monotone rule with at least three outcomes is dictatorial.
The library proves both through [Nisan](#nisan07)'s argument; no theorem number is claimed.

<a id="murraywilliams2017"></a>
## murraywilliams2017

Cody D. Murray and R. Ryan Williams.
*On the (Non) NP-Hardness of Computing Circuit Complexity*.
Theory of Computing 13(4), 1–22, 2017. https://doi.org/10.4086/toc.2017.v013a004 . Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.
The Lean module documentation quotes its Theorem 1.6 (Section 1, p. 5) and Theorem 4.1 (Section 4.1, p. 13).

<a id="murtykabadi1987"></a>
## murtykabadi1987

Katta G. Murty and Santosh N. Kabadi.
"Some NP-Complete Problems in Quadratic and Nonlinear Programming."
*Mathematical Programming* 39(2), 117–129, 1987. https://doi.org/10.1007/BF02592948 . Bibliographic metadata checked via DOI and secondary search summaries on 2026-11-10; the published text is uninspected.
The manual cites it for the `coNP`-completeness of testing matrix copositivity (and `NP`-completeness of non-copositivity), noting that secondary summaries describe [Murty–Kabadi] as reducing from subset sum whereas this library proves completeness via `Clique` and Motzkin–Straus; no internal theorem or section numbers are cited.

<a id="myerson81"></a>
## myerson81

Roger B. Myerson.
"Optimal Auction Design."
*Mathematics of Operations Research* 6(1), 58–73, 1981. https://doi.org/10.1287/moor.6.1.58 (bibliography key `Myerson1981`).
Bibliographic metadata from `references.bib`; the journal text was not directly inspected in this pass, so no internal section or theorem numbers are claimed.
Cited bibliographically via [Hartline and Karlin](#hartlinekarlin07), §13.2, and [Roughgarden](#roughgarden13cs364a) for Myerson's Lemma, virtual valuations, optimal single-parameter auctions, and convex-hull ironing of irregular distributions.

<a id="nagamochiibaraki92"></a>
## nagamochiibaraki92

Hiroshi Nagamochi and Toshihide Ibaraki.
"Computing Edge-Connectivity in Multigraphs and Capacitated Graphs."
*SIAM Journal on Discrete Mathematics* 5(1), 54–66, 1992. https://doi.org/10.1137/0405004 . Bibliographic metadata checked against the Crossref record on 2026-11-08; the paper was not inspected.
The manual credits it with the basic property of maximum adjacency orderings (the cut of the last vertex is a minimum cut between the last two), as attributed by [stoerwagner97](#stoerwagner97) in secondary descriptions.
No locator is claimed.

<a id="nagy1972"></a>
## nagy1972

Zsigmond Nagy.
“A Constructive Estimation of the Ramsey Numbers” (in Hungarian).
*Matematikai Lapok* 23, 301–302, 1972 (the volume is dated 1972 but reportedly appeared in 1975).
The original was not inspected; the construction and its bound follow Jukna, *Extremal Combinatorics*, 2nd ed., §13.7 and the Chapter 13 exercises, as cited in the Lean documentation.

<a id="naor91"></a>
## naor91

Moni Naor.
“Bit Commitment Using Pseudorandomness.”
*Journal of Cryptology* 4(2), 151–158, 1991. https://doi.org/10.1007/BF00196774 . The journal version was not inspected.
Read on 2026-11-15 in the author's copy, https://www.wisdom.weizmann.ac.il/~naor/PAPERS/bit.pdf (“Bit Commitment Using Pseudo-Randomness”, 10 pages, dated February 25, 2001; SHA-256 `938b32039291411c682ca457c8c040dba7f0dc264de91182e6cb8cdaaba633b6`), whose section and page numbers the library cites: Section 2 (pp. 3–4), the secrecy and binding conditions of a bit commitment, the remark on auxiliary input, and the conditions for commitments to many bits, in which the receiver selects the two sequences.
Section 2, p. 4 allows any polynomial output length and treats the generator as a stream with efficient prefixes.
Section 3 (pp. 5–6) uses its first `3n` bits.
Theorem 3.1(1), p. 6 bounds the probability that a probabilistic polynomial-time receiver guesses the bit by one half plus any inverse polynomial for sufficiently large `n`.
Claim 3.1 counts seed pairs to bound binding failure by `2⁻ⁿ`.
Theorem 3.1(2) states the strict inequality.

<a id="naoryung89"></a>
## naoryung89

Moni Naor and Moti Yung.
“Universal One-Way Hash Functions and their Cryptographic Applications.”
*Proceedings of the Twenty-First Annual ACM Symposium on Theory of Computing (STOC 1989)*, 33–43, 1989. https://doi.org/10.1145/73007.73011 . Authors' revised manuscript (March 13, 1995): https://www.wisdom.weizmann.ac.il/~naor/PAPERS/uowhf.ps (§2, §2.3, §3 and §4).

<a id="nascimentowinter08"></a>
## nascimentowinter08

Anderson C. A. Nascimento and Andreas Winter.
"On the Oblivious-Transfer Capacity of Noisy Resources."
*IEEE Transactions on Information Theory* 54(6), 2572–2581, 2008. https://doi.org/10.1109/TIT.2008.921856 . Bibliographic metadata checked via secondary search summaries on 2026-11-11; the full paper was not audited, so no internal theorem numbers are claimed.

<a id="nash51"></a>
## nash51

John Nash.
"Non-Cooperative Games."
*Annals of Mathematics* 54(2), 286–295, 1951. https://doi.org/10.2307/1969529 . Bibliographic data from the DOI record.
Theorem 1 ("every finite game has an equilibrium point") and its proof by Brouwer's theorem were checked on printed p. 288 of the scan at https://www.cs.upc.edu/~ia/nash51.pdf during the agent review of [#4105](https://github.com/cslib-community/cslib-frontier/pull/4105) on 2026-11-10.

<a id="nayakwu99"></a>
## nayakwu99

Ashwin Nayak and Felix Wu.
*The Quantum Query Complexity of Approximating the Median and Related Statistics*.
STOC '99, 384–393, 1999. https://doi.org/10.1145/301250.301349 ; open version arXiv:quant-ph/9804066v2, https://arxiv.org/abs/quant-ph/9804066v2 . Bibliographic metadata taken from `references.bib` (`NayakWu1999`).
The arXiv v2 LaTeX source (`main.tex`) was inspected on 2026-11-11 UTC for the Section 1 problem definitions (`ε`-approximate median, `Δ`-approximate `k`-th smallest element with its relaxed input-membership remark, and `Δ`-approximate count), Theorem 1.5 (`Ω(√(n/Δ) + √(k(n-k))/Δ)` for `k`-th smallest), Corollary 1.6 (`Ω(1/ε)` and `Ω(min {1/ε, n})` for approximate median), Theorem 1.11 (`Ω(√(n/Δ) + √(t(n-t))/Δ)` for approximate counting), and the Section 2 partial-function reductions (`Proof of Theorem 1.5`).
Nayak and Wu prove the underlying threshold bound by the polynomial method (Corollary 1.2); the library derives the reductions from `one_sub_mul_add_le_four_mul_mul_abs_sub_of_weight` ([AmbainisAdversary/WeightLayers](../CslibFrontier/Computability/QueryComplexity/Quantum/AmbainisAdversary/WeightLayers.lean)).

<a id="nechiporuk1970"></a>
## nechiporuk1970

E. I. Nechiporuk.
"On the Topological Principles of Self-Correction" (in Russian).
*Problemy Kibernetiki* 21, 5–102, 1970 (English translation in *Systems Theory Research* 21, 1–99, 1970).
Bibliographic metadata as cited in [sergeev2014orcomplement](#sergeev2014orcomplement) (Reference [6], pp. 1, 3) and [juknasergeev2013](#juknasergeev2013) (§3.3, p. 32); neither the Russian original nor the translation was inspected directly (locator not verified).
[Rectifier/Basic.lean](../CslibFrontier/Computability/Circuit/Rectifier/Basic.lean) proves `|A| ≤ (K - 1)^2 · OR(A)` and its `2`-free consequence `OR(A) = OR_d(A) = |A|` (`1 ≤ d`), checked against [juknasergeev2013](#juknasergeev2013) (§3.3, Theorem 3.9, pp. 32–33, taking `k = l = K - 1`); [sergeev2014orcomplement](#sergeev2014orcomplement) quotes the weaker denominator `K^2` on p. 3 and records the `2`-free consequence on p. 1.

<a id="nielsenchuang2010"></a>
## nielsenchuang2010

Michael A. Nielsen and Isaac L. Chuang.
*Quantum Computation and Quantum Information: 10th Anniversary Edition*.
Cambridge University Press, 2010 (bibliography key `NielsenChuang2010`). https://doi.org/10.1017/CBO9780511976667 . Bibliographic data and the Section 12.1.1, Theorem 12.1 locator for Holevo's bound were taken from secondary textbook metadata (locator not verified directly against the printed book in this pass); the formalized statements in [Holevo.lean](../CslibFrontier/Foundations/Quantum/DensityMatrix/Holevo.lean) were checked directly against [watrous2018](#watrous2018), Chapter 5, Theorem 5.49 and Corollary 5.50.

<a id="nisan07"></a>
## nisan07

Noam Nisan.
"Introduction to Mechanism Design (for Computer Scientists)."
Chapter 9 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 209–242. https://doi.org/10.1017/CBO9780511800481.011 . A university-hosted PDF of the book was consulted on 2026-11-08 for §9.2 (pp. 211–215: Definitions 9.1, 9.4, 9.5, 9.7 and 9.9, Proposition 9.6, Theorem 9.8, and Lemmas 9.10–9.11), and consulted on 2026-11-23 for §9.3.2–9.3.5 (pp. 217–221: Definitions 9.14, 9.15 and 9.18, Theorem 9.17, Lemma 9.20, §9.3.5.1 single-item VCG and §9.3.5.4 multi-unit auctions), §9.4 (pp. 222–225: Definitions 9.21, 9.22 and 9.24, Propositions 9.23 and 9.25, and Corollary 9.26), §9.5.6 (pp. 231–232: Definition 9.38 on universal vs expected truthfulness of randomized mechanisms), and §9.6.1 (pp. 233–234: Definitions 9.40–9.43 and Proposition 9.44 on Bayesian mechanisms and the Bayesian revelation principle).
In §9.2, Nisan writes `x ≺ y` for "`y` is preferred to `x`" (`Prefers y x`), and leaves `n ≥ 1` voters implicit in Lemma 9.11 (`nisanSWF_isPareto` takes `[Nonempty V]` or `[Nontrivial A]`).
The main Gibbard–Satterthwaite theorem in `GibbardSatterthwaite.lean` strengthens Theorem 9.8 to three alternatives in the range rather than onto, while `GibbardSatterthwaiteReduction.lean` exposes Nisan's standalone `IsSingleMonotone` and `nisanSWF` reduction.
The same PDF was also consulted (as rendered page images) on 2026-11-24 for §9.5 (pp. 225–228) and §9.8 Notes (pp. 239–240): Proposition 9.27 (taxation principle / direct characterization, p. 226), Definition 9.28 (weak monotonicity / WMON, p. 227), Theorem 9.29 (necessity of WMON, proved p. 227; sufficiency on convex domains, stated without proof p. 227), Definition 9.30 (affine maximizer, p. 228; note the printed condition `wᵢ ∈ ℝ⁺` excludes dictatorships required by Theorem 9.32), Proposition 9.31 (weighted Groves / weighted VCG payments, p. 228), and Theorem 9.32 (Roberts' theorem, p. 228).
Checked again on 2026-11-24 UTC in the Cambridge University Press typeset edition for §9.2.1 ("Condorcet's Paradox", p. 211: three-voter cyclic pairwise majority `a ≻ b ≻ c ≻ a`) and §9.2.2 ("Voting Methods", pp. 211–212: plurality, Borda count, and strategic voting under plurality when a voter with `a ≻_i b ≻_i c` votes for `b` to defeat `c`), cited by [SocialChoice/Condorcet.lean](../CslibFrontier/GameTheory/SocialChoice/Condorcet.lean).

<a id="nisan92"></a>
## nisan92

Noam Nisan.
*Pseudorandom Generators for Space-Bounded Computation*.
Combinatorica 12(4), 449–461, 1992.
DOI: [10.1007/BF01305237](https://doi.org/10.1007/BF01305237).
The publisher copy is paywalled and was not consulted, so its theorem numbering is unverified.
The statement was checked against S. Vadhan, *Pseudorandomness* (2012), §8.2.1, and P. Hatami and W. Hoza, *Paradigms for Unconditional Pseudorandom Generators* (2024), Definition 1.5 and §3.2.
The Lean proof is the library's own derivation of the hashing argument in expectation form.

<a id="nisanwigderson94"></a>
## nisanwigderson94

Noam Nisan and Avi Wigderson.
*Hardness vs Randomness*.
Journal of Computer and System Sciences 49(2), 149–167, 1994.
DOI: [10.1016/S0022-0000(05)80043-1](https://doi.org/10.1016/S0022-0000(05)80043-1).
Publisher metadata and abstract checked by the coordinated source pass on 2026-11-02; this section's source-to-proof description follows the pinned Lean documentation.

<a id="nordstrom15"></a>
## nordstrom15

Jakob Nordström.
*New Wine into Old Wineskins: A Survey of Some Pebbling Classics with Supplemental Results*, manuscript version of 25 March 2015. https://www.jakobnordstrom.se/docs/publications/PebblingSurveyTMP.pdf . Definition 1.1 (black pebble game), Proposition 2.5 (sliding), Theorem 4.1 (complete binary trees), Definition 4.5 and Theorem 4.8 (pyramids) were checked.

<a id="np01"></a>
## np01

Moni Naor and Benny Pinkas.
"Efficient Oblivious Transfer Protocols."
*Proceedings of the Twelfth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 2001)*, 448–457, SIAM, 2001.
Bibliographic metadata checked against `references.bib` (`NaorPinkas2001`); cited only as general background for DDH-based oblivious transfer without internal SODA 2001 locators (the SODA text was not inspected).
The formalized protocol is a variant of [bs23](#bs23), Section 23.5.7, Figure 23.17 with the Remark 23.6 check, known sender exponent, and per-branch `(rᵢ, sᵢ)` randomization, proved directly.

<a id="odifreddi99"></a>
## odifreddi99

Piergiorgio Odifreddi.
*Classical Recursion Theory, Volume II*.
Studies in Logic and the Foundations of Mathematics 143, North-Holland, 1999.
ISBN 978-0-444-50205-6.
Read in the author's open PDF, https://www.piergiorgioodifreddi.it/wp-content/uploads/2010/10/CRT2.pdf , on 2026-11-08.
Locators checked there, with the book's printed page numbers: Definition VII.2.9 (measured sets, pp. 33–34); Definition VII.2.13 (`g`-honest functions, p. 35); Exercise VII.2.14a (members of a measured set are honest for one recursive `g`, attributed to Blum 1967, p. 36); Definition VII.3.1 (the almost-everywhere class `C_t`, p. 47); Theorem VII.3.6 (Naming Theorem, attributed to Meyer and McCreight 1969, statement and proof pp. 51–54); and Theorem VII.3.7 (Union Theorem, attributed to Meyer and McCreight 1969, p. 55).
The manual uses this book for the statements of these results, not for their proofs: the library's union proof was written independently, and its naming proof follows the book's priority construction with the differences recorded in the Lean module docstring.

<a id="odonnell14"></a>
## odonnell14

Ryan O'Donnell.
*Analysis of Boolean Functions*.
Cambridge University Press, 2014; arXiv edition, arXiv:2105.10386v1, May 2021, https://arxiv.org/abs/2105.10386 . Library bibliography key `ODonnell2014`.
Read in the arXiv edition on 2026-11-08: §1.7, p. 38, Exercise 1.28 (a) `|f̂(S)| ≤ 2δ` for `S ≠ S*` when `dist(f, χ_{S*}) = δ`, (b) the BLR test rejects with probability at least `3δ − 10δ² + 8δ³`, (c) this cannot be improved to `cδ − O(δ²)` for any `c > 3`; and Exercise 1.29 (a) the characterization of affine functions by `f(x) + f(y) + f(z) = f(x + y + z)`, (b) `E[f(x) f(y) f(z) f(x + y + z)] = Σ_S f̂(S)⁴`, (c) a four-query affinity test with uniform queries whose acceptance probability `1 − ε` gives `ε`-closeness to affine, (d) an alternate test with three uniform queries and one fixed query.
Theorem 1.30 (BLR soundness) is in §1.6 of the same edition.
In [LinearityRejection](../CslibFrontier/Foundations/BooleanAnalysis/LinearityRejection.lean), part (b) is proved for every parity, not only the nearest, and part (c) is stated as the failure of every bound `cδ − Cδ²` for `c > 3` over functions at distance `δ ≤ δ₀` from their nearest parity.
The anchored test in [Affinity](../CslibFrontier/Foundations/BooleanAnalysis/Affinity.lean) is one answer to part (d); the exercise asks for some such test and does not specify it.
Read on 2026-11-12: §2.1, p. 43, Definition 2.1 (`Majₙ(x) = sgn(x₁ + ⋯ + xₙ)` for odd `n`; for even `n`, a majority function is any `f` equal to that sign wherever the sum is nonzero); §2.3, p. 50, Proposition 2.31 (`I[f] = Σᵢ f̂(i)` for monotone `f`), Proposition 2.32 (`E[w] = n/2 + ½ Σᵢ f̂(i)` for the number `w` of votes agreeing with the outcome) and equation (2.3) in its proof (`Σᵢ f̂(i) = E[f(x)(x₁ + ⋯ + xₙ)]`); p. 51, Theorem 2.33 (the majority functions are the unique maximizers of `Σᵢ f̂(i)`, and `I[f] ≤ I[Majₙ] = √(2/π)√n + O(n^{−1/2})` for monotone `f`).
[Majority](../CslibFrontier/Foundations/BooleanAnalysis/Majority.lean) proves the characterization for every `n`, reading the book's restriction to odd `n` through `Cslib.majority n`, which breaks ties towards `true` (the book's −1) and is a majority function in the book's even-`n` sense, and proves the inequality of Theorem 2.33 but not its asymptotic value.
Read on 2026-11-13, in the same edition: §11.5, the Invariance Principle for Sums of Random Variables, Proposition 11.58 and Corollaries 11.59, 11.61 and 11.62 (pp. 354–357), Corollary 11.70 (p. 363) and Exercises 11.40, 11.41, 11.42 and 11.44 (pp. 380–381), for [InvarianceSums](../CslibFrontier/Foundations/Probability/InvarianceSums.lean), [SmoothTests](../CslibFrontier/Foundations/Probability/SmoothTests.lean), [LevyDistance](../CslibFrontier/Foundations/Probability/LevyDistance.lean) and the two `InvarianceLevy` modules.
Corollary 11.62 hides a universal constant in `O(γ^(1/4))`; the formalization proves it with the constant `6`, comparing `X` with `Yᵢ ∼ N(0, Var[Xᵢ])` as in the proof of the Variant Berry–Esseen Theorem (p. 356) and bounding `E|Yᵢ|³ ≤ 2 E|Xᵢ|³` in place of the book's `2 √(2/π) E|Xᵢ|³` in (11.28).
Only the first statement of Corollary 11.70 is formalized; its second statement depends on Remark 11.66.
Read on 2026-11-14: §2.3, p. 49, Proposition 2.28 (`I[f] = E[sens_f(x)]`, where `sens_f(x)` is the number of pivotal coordinates for `f` on input `x`); p. 51, equation (2.4) (`I[f] = E[Σᵢ Dᵢf(x)²]`), Definition 2.34 (the discrete gradient of `f` at `x` is `(D₁f(x), D₂f(x), …, Dₙf(x))`), the note after it (for `f : {−1, 1}ⁿ → {−1, 1}` the squared Euclidean norm of the gradient at `x` is `sens_f(x)`) and Proposition 2.35 (`I[f]` is the mean over `x` of the squared Euclidean norm of the gradient).
[Influence](../CslibFrontier/Foundations/BooleanAnalysis/Influence.lean) proves Proposition 2.35 and the note for an arbitrary finite coordinate type, writing that squared norm as `∑ i, gradient f x i ^ 2` because the norm on `ι → ℝ` is the sup norm; p. 52, Theorem 2.39 `2α log(1/α) ≤ I[f]` for `f : {−1, 1}^n → {−1, 1}` with `α = min{Pr[f = 1], Pr[f = −1]}`, stated without proof and called optimal for `α` a power of `1/2`; `log` is `log₂` (List of Notation, p. xvi).
The notes of §2.6 (p. 68) credit the edge-isoperimetric inequality to Harper (1964), and Exercises 10.25 (p. 320, `2α ln(1/α) ≤ I[f]` from the Log-Sobolev Inequality) and 11.21 (p. 374, up to a constant factor from Bobkov's Inequality) derive weaker forms.
[EdgeIsoperimetry](../CslibFrontier/Foundations/BooleanAnalysis/EdgeIsoperimetry.lean) proves Theorem 2.39 from the classical bound `|A| log₂ |A|` on the directed edges that a set `A` of the cube spans, by induction on the dimension; as for Proposition 1.15, `α` is written as the relative Hamming distance to the nearer constant, so `Pr[f = 1]` is the distance to the constant `true` (`signVal false = 1`).
§10.1, p. 285, Remark 10.3 and the Reverse Small-Set Expansion Theorem (for `0 ≤ ρ ≤ 1` and volumes `exp(−a²/2)`, `exp(−b²/2)`, `Pr[x ∈ A, y ∈ B] ≥ exp(−(a² + 2ρab + b²)/(2(1 − ρ²)))`); §10.6, p. 314, Exercise 10.6, which states the Reverse Hypercontractivity Theorem (`‖T_ρ f‖_q ≥ ‖f‖_p` for `−∞ ≤ q < p ≤ 1` and `0 ≤ ρ ≤ √((1 − p)/(1 − q))`), the Reverse Two-Function Hypercontractivity Theorem (for `r, s ≤ 0` and `0 ≤ ρ ≤ √(rs) ≤ 1`) and the reverse Hölder inequality, with parts (a)–(c) and the Reverse Two-Point Inequality on p. 315; and p. 315, Exercise 10.7 (a)–(f), Exercise 10.8 and Exercise 10.9.
[ReverseHypercontractivity](../CslibFrontier/Foundations/BooleanAnalysis/ReverseHypercontractivity.lean) proves both theorems for every exponent except `0` and `−∞`, with functions of negative exponent assumed positive (the reduction of Exercise 10.6(a) is not formalized), and the Reverse Small-Set Expansion Theorem for `ρ < 1`, since at `ρ = 1` Lean's `x / 0 = 0` would make the stated bound `1`.
Exercise 10.6(b) is proved for positive functions.
Exercise 10.6(c): the reduction to `n = 1` as stated; the further reduction to the two-point inequality for `r < −1` only, since for `−1 < r, s ≤ 0` the one-bit case goes through the `q = 0` two-point inequality and the AM–GM inequality.
Exercise 10.7(a) is proved for every `ρ ≤ √((1 − p)/(1 − q))` directly by comparing binomial series, without part (b), whose hint (the monotonicity of `‖f‖_p` in `p` for negative `p`) is not formalized; part (d) by duality as hinted; part (e) through Exercise 10.6(b) rather than the semigroup property; and part (f) only for the one-bit inequality at `q = 0`, in [ReverseTwoPoint](../CslibFrontier/Foundations/BooleanAnalysis/Hypercontractivity/ReverseTwoPoint.lean).
Part (c), the case `q = −∞`, is not formalized.
Exercise 10.8 is derived on every cube from the general theorem rather than proved directly for `n = 1`, and the reverse Hölder inequality is in [ReverseHolder](../CslibFrontier/Foundations/Analysis/ReverseHolder.lean).
Read on 2026-11-16: §1.7, p. 39, Exercise 1.30 (a permutation `π` acts on inputs by `(x^π)_i = x_{π(i)}` and on functions by `f^π(x) = f(x^π)`; `Aut(f) = {π : f^π = f}` is the automorphism group of `f`; part (a), `(f^π)^(S) = f̂(π⁻¹(S))`); §2.1, p. 45, Definition 2.10 (`f` is transitive-symmetric if for all `i, i'` some permutation taking `i` to `i'` has `f(x^π) = f(x)` for all `x`); §2.2, p. 48, Proposition 2.22 (a transitive-symmetric monotone `f : {−1, 1}ⁿ → {−1, 1}` has `Inf_i[f] ≤ 1/√n` for all `i`, proved from `f̂(i) = f̂(i')` and Parseval); §2.6, p. 64, Exercise 2.47 (transitive symmetry means that `Aut(f)` acts transitively on `[n]`); its claim `Pr_{π∼Aut(f)}[π(i) = j] = 1/n` is not formalized.
[TransitiveSymmetric](../CslibFrontier/Foundations/BooleanAnalysis/TransitiveSymmetric.lean) states Definition 2.10 as Mathlib's `MulAction.IsPretransitive (aut f) ι`, the form of Exercise 2.47, and derives Proposition 2.22 from the `√n` bound on the total influence of monotone functions instead of Parseval.
Read on 2026-11-20: §9.2, p. 255, Corollary 9.12 (`Inf_i^{(1/3)}[f] ≤ Inf_i[f]^{3/2}` for `f : {−1, 1}ⁿ → {−1, 1}`); §9.6, p. 265, the Kahn–Kalai–Linial (KKL) Theorem (`MaxInf[f] ≥ Var[f] · Ω(log n / n)`, unnumbered); p. 267, the KKL Edge-Isoperimetric Theorem (unnumbered: for nonconstant `f` with `Ĩ[f] = I[f]/Var[f] ≥ 1`, `MaxInf[f] ≥ (9/Ĩ[f]²) · 9^{−Ĩ[f]}`), sharp at `Ĩ[f] = 1`, and the derivation of the KKL Theorem from it by distinguishing whether `Ĩ[f] ≥ .1 log n`; pp. 267–268, the proof in the unbiased case by the chain `3 · 3^{−I[f]} ≤ 3 Stab_{1/3}[f] ≤ I^{(1/3)}[f] ≤ Σᵢ Infᵢ[f]^{3/2} ≤ MaxInf[f]^{1/2} · I[f]`, with (9.15) the convexity step; §9.7, p. 276, Exercise 9.29 (the general-variance case, replacing (9.15) by `3 Σ_{|S|≥1} (1/3)^{|S|} f̂(S)² ≥ 3 Var[f] · 3^{−I[f]/Var[f]}`) and Exercise 9.30 (best known constants, with the asymptotic constant `1/2` of part (c)).
[KahnKalaiLinial](../CslibFrontier/Foundations/BooleanAnalysis/KahnKalaiLinial.lean) proves the general-variance theorem with the book's constants, without the hypothesis `Ĩ[f] ≥ 1` (it follows from the Poincaré Inequality), and the KKL Theorem with the constant `1/4` for every `n ≥ 1`, by splitting at `Ĩ[f] = log n / 4` instead of `.1 log n`; these replace the module's earlier weaker forms, the bound `Var[f] · log(1/δ) ≤ 6 I[f]` when every influence is at most `δ` and the KKL Theorem with constant `1/12`.
It does not attempt Exercise 9.30.
§1.4, p. 28, the notation `f^{≤k} = Σ_{|S| ≤ k} f̂(S) χ_S` introduced after Definition 1.19; §1.7, p. 37, Exercise 1.13 (`‖f‖_p ≤ ‖f‖_q` for `0 < p ≤ q < ∞`, and its extension to `q = ∞`); §9.5, p. 262, Theorem 9.21 (`‖f‖_q ≤ √(q − 1)^k ‖f‖_2` for `f` of degree at most `k` and `q ≥ 2`); §9.7, p. 271, Exercise 9.8 ((a) `‖f^{≤k}‖_q ≤ √(q − 1)^k ‖f‖_q` for `q ≥ 2`, with the hint to prove the stronger `‖f^{≤k}‖_q ≤ √(q − 1)^k ‖f‖_2`; (b) `‖f^{≤k}‖_q ≤ (1/√(q − 1))^k ‖f‖_q` for `1 < q ≤ 2`); §10.4, p. 299, Proposition 10.37 (both ranges of Exercise 9.8) and p. 300, Lemma 10.38 (`‖g^{≤k}‖_4 ≤ (√3/ρ)^k ‖T_ρ g‖_4` for `0 < ρ ≤ 1`).
[LpNorm](../CslibFrontier/Foundations/Analysis/LpNorm.lean) proves Exercise 1.13 for real exponents on any finite type, not the case `q = ∞`.
[LowDegreePart](../CslibFrontier/Foundations/BooleanAnalysis/LowDegreePart.lean) proves the case `q ≥ 2` of Proposition 10.37 and the stronger `L²` form of the hint from Theorem 9.21, and Lemma 10.38 for every `q ≥ 2` (the book's `q = 4` is an instance) by the book's proof with Theorem 9.21 in place of the Bonami Lemma; it proves the case `1 < q ≤ 2` by the direct route of the hint to Exercise 9.8(b), the `(p, 2)`-Hypercontractivity Theorem with `p = q` at `ρ = √(q − 1)`, through the stronger `‖f^{≤k}‖_2 ≤ (1/√(q − 1))^k ‖f‖_q`.
Read on 2026-11-19: §1.7, p. 37, Exercise 1.19(a) (if `f : {−1, 1}ⁿ → {−1, 1}` has `W¹[f] = 1`, then `f = ±χ_S` for some `|S| = 1`); §2.4, p. 54, Example 2.44 (`Stab_ρ[χᵢ] = ρ` for all `ρ`); p. 56, Theorem 2.49 (`Stab_ρ[f] = Σ_S ρ^{|S|} f̂(S)² = Σ_k ρ^k W^k[f]`) and Proposition 2.50 (for `ρ ∈ (0, 1)`, an unbiased `f : {−1, 1}ⁿ → {−1, 1}` has `Stab_ρ[f] ≤ ρ`, with equality if and only if `f = ±χᵢ`); §2.5, p. 59, Theorem 2.56 (the probability of a Condorcet winner is `3/4 − 3/4 Stab_{−1/3}[f]`) and the proof of Arrow's Theorem after it (`(−1/3)^k ≥ −1/3` for all `k`, so equality forces `W¹[f] = 1`).
[DegreeOneWeight](../CslibFrontier/Foundations/BooleanAnalysis/DegreeOneWeight.lean) proves Exercise 1.19(a) with its converse, writing `±χᵢ` as the literals `x ↦ b ⊕ xᵢ` and taking the forward direction from the Friedgut–Kalai–Naor module; proves Proposition 2.50, with the inequality on the closed interval `0 ≤ ρ ≤ 1`; and proves, for every `ρ` in `[−1, 0]`, the inequality `Stab_ρ[f] ≥ ρ` and, for `ρ` in `(−1, 0)`, equality exactly for `±χᵢ`, the two steps the book takes at `ρ = −1/3`.
Theorem 2.56 and Arrow's Theorem itself are not proved there.
Read on 2026-11-17: §5.4, p. 126, the Level-1 Inequality (`f : {−1, 1}ⁿ → {0, 1}` with `E[f] = α ≤ 1/2` has `W¹[f] ≤ O(α² log(1/α))`) and Remark 5.28 (the sharp form `W¹[f] ≤ 2α² ln(1/α)`, and the extension to `f : {−1, 1}ⁿ → [−1, 1]` with `α = E[|f|]`); p. 128, Lemma 5.31 (`E[1{|ℓ(x)|>s} · |ℓ(x)|] ≤ (2s + 2) exp(−s²/2)` for `Σᵢ aᵢ² = 1` and `s ≥ 1`, from Hoeffding's bound) and the proof of the Level-1 Inequality, which takes `f` with values in `[−1, 1]` and `α = E[|f|]` and reaches `σ ≤ αs + 4s exp(−s²/2)`.
[LevelOneInequality](../CslibFrontier/Foundations/BooleanAnalysis/LevelOneInequality.lean) proves the `[−1, 1]` form with the explicit constant `16` in place of `O(1)`, bounding the tail by Cauchy–Schwarz and Hoeffding's bound instead of Lemma 5.31; the sharp constant of Remark 5.28 is proved for `{0, 1}`-valued `f` in [LevelK](../CslibFrontier/Foundations/BooleanAnalysis/LevelK.lean); see below.
§2.4, p. 56, Theorem 2.49 (`Stab_ρ[f] = ∑_S ρ^{|S|} f̂(S)² = ∑_k ρ^k W^k[f]`); §5.2, p. 121, Theorem 5.18 (for `ρ ∈ [0, 1)`, `Stab_ρ[Maj_n]` is a decreasing function of `n`, at least `(2/π) arcsin ρ` and at most `(2/π) arcsin ρ + O(1/(√(1−ρ²)·√n))`); §5.3, pp. 121–123: the opening remarks of the section (`Maj_n` is symmetric, so its coefficient on `S` depends only on `|S|` by Exercise 1.30, and odd, so it vanishes when `|S|` is even) and Theorem 5.19 (p. 122: for odd `|S| = k` the coefficient is `(−1)^{(k−1)/2} C((n−1)/2, (k−1)/2)/C(n−1, k−1) · 2/2^n · C(n−1, (n−1)/2)`; the proof, pp. 122–123, uses `D_n Maj_n = Half_{n−1}` and compares two expansions of `T_ρ Half_{2m}(1, …, 1)`), Corollary 5.20 (p. 123: the coefficients on `S` and `T` with `|S| + |T| = n + 1` agree up to the sign `(−1)^{(n−1)/2}`, hence `W^{n−k+1}[Maj_n] = k/(n−k+1) · W^k[Maj_n]`) and Corollary 5.21 (p. 123: for odd `k`, `W^k[Maj_n]` strictly decreases in `n ≥ k` odd); §5.6, p. 136, Exercise 5.21 (for odd `n`, the size of the coefficient on `S` decreases in `|S|` for odd `1 ≤ |S| ≤ (n−1)/2`, and the largest coefficient is the one on `{1}`, asymptotically `√(2/(nπ))`).
[MajorityFourier](../CslibFrontier/Foundations/BooleanAnalysis/MajorityFourier.lean) states Theorem 5.19 for `n = 2m + 1` and `k = 2j + 1` as `(−1)^j C(m, j)/C(2m, 2j) · C(2m, m)/4^m`, and sums the coefficients of `Half_{2m}` over all `2j`-sets instead of comparing the two expansions.
It proves Corollary 5.21 in the one-step form `n → n + 2`.
It proves the monotonicity claim of Theorem 5.18 in the same one-step form, as a strict decrease for `0 < ρ < 1`, since at `ρ = 0` every `Stab_0[Maj_n]` is `0`; the `arcsin` bounds are not formalized.
It proves the decrease of Exercise 5.21 up to `|S| ≤ (n + 3)/2` and the maximum at singletons, but not the asymptotic.
[LevelWeight](../CslibFrontier/Foundations/BooleanAnalysis/LevelWeight.lean) states the level form of Theorem 2.49.
Read on 2026-11-19: §9.2, p. 254, Corollary 9.8 (for `A` of volume `α`, `Stab_{1/3}[1_A] = Pr[x ∈ A, y ∈ A] ≤ α^{3/2}`, equivalently `Pr[y ∈ A] ≤ α^{1/2}` for `x` uniform on `A` and `α > 0`); §9.5, p. 264, the Small-Set Expansion Theorem (`Stab_ρ[1_A] ≤ α^{2/(1+ρ)}` for `0 ≤ ρ ≤ 1`, equivalently `Pr[y ∈ A] ≤ α^{(1−ρ)/(1+ρ)}`).
[SmallSetExpansion](../CslibFrontier/Foundations/BooleanAnalysis/SmallSetExpansion.lean) proves both inequalities, writing `Stab_ρ[1_A]` as `noiseStability ρ (A.indicator 1)`; the equivalent conditional forms are not stated.
Read on 2026-11-21: §5.4, p. 125, Proposition 5.24 (the indicator `f` of a subcube of codimension `k ≥ 1`, for example `AND_k`, has `E[f] = 2 ^ (-k)` and `W¹[f] = k 2 ^ (-2k)`), and §5.6, p. 137, Exercise 5.29 (prove Proposition 5.24).
[Subcube](../CslibFrontier/Foundations/BooleanAnalysis/Subcube.lean) proves the Fourier coefficients of a subcube indicator (`fourierCoeff_ite_forall_mem_eq`) and the degree-one weight (`levelWeight_one_ite_forall_mem_eq`); the density is `expect_ite_forall_mem_eq` in [AgreeExpect](../CslibFrontier/Foundations/Data/BitString/AgreeExpect.lean).
Both hold for every codimension, `k = 0` included, and `W¹` is `levelWeight 1` of [LevelWeight](../CslibFrontier/Foundations/BooleanAnalysis/LevelWeight.lean), the book's sum of the squared coefficients on singletons.
§3.6, p. 86, Exercise 3.9, which bounds the largest absolute Fourier coefficient by the mean absolute value of the function and the largest absolute value of the function by the sum of the absolute Fourier coefficients; [Fourier](../CslibFrontier/Foundations/BooleanAnalysis/Fourier.lean) proves them as `abs_fourierCoeff_le_expect_abs` and `abs_le_sum_abs_fourierCoeff`, the second from `abs_sum_mul_chi_le` for any combination of characters.
Exercise 3.15, pp. 86–87, the uncertainty principle: for nonzero `f`, the fractional sparsity `Pr_x[f(x) ≠ 0]` times the Fourier sparsity, which is the number of nonzero coefficients (Definition 3.9, p. 72; List of Notation, p. xviii), is at least `1`.
[UncertaintyPrinciple](../CslibFrontier/Foundations/BooleanAnalysis/UncertaintyPrinciple.lean) states it in this form, with `sparsity(f)` as the density `dens {x | f x ≠ 0}`, derives the form multiplied by `2 ^ n` with both factors counts, and proves it from the two bounds of Exercise 3.9 instead of through parts (a)–(c); part (d), the equality cases, is not formalized.
The §3.6 notes, p. 91, credit the uncertainty principle to Matolcsi and Szűcs (1973) (the book's reference [MS73]), and the module docstring credits them.
Read on 2026-11-22: §2.4, p. 56, Proposition 2.51 (`d/dρ Stab_ρ[f]` is `W¹[f]` at `ρ = 0` and `I[f]` at `ρ = 1`, with the restatement `d/dδ NS_δ[f] = I[f]` at `δ = 0` for Boolean `f`); p. 57, Definition 2.52 (stable influences, for `ρ ∈ [0, 1]`) and Fact 2.53 (`I^{(ρ)}[f] = d/dρ Stab_ρ[f] = Σ_k k ρ^{k−1} W^k[f]`).
In [StableInfluence](../CslibFrontier/Foundations/BooleanAnalysis/StableInfluence.lean), `hasDerivAt_noiseStability` proves the derivative half of Fact 2.53 at every real `ρ`, the Fourier half being `totalStableInfluence_eq_sum` summed over sets rather than degrees; `hasDerivAt_noiseStability_zero` and `hasDerivAt_noiseStability_one` are the two identities of Proposition 2.51.
The noise-sensitivity restatement is not stated separately.
Its claim that `NS_δ[f]` increases on `[0, 1/2]` for Boolean `f` is `Cslib.BitString.noiseSensitivity_mono` (`Noise.lean`).
§2.6, p. 64, Exercise 2.40 asks the reader to verify Fact 2.53; `hasDerivAt_noiseStability` and `totalStableInfluence_eq_sum` together do so.
§8.4, p. 220, Definition 8.39 (`φ(x_i) = (x_i − μ)/σ` with `μ = 1 − 2p` and `σ = 2√(p(1 − p))`); p. 221, Definition 8.40 (`f̂(S) = E[f(x) φ_S(x)]` under `π_p^{⊗n}`); p. 222, Notation 8.43 (for `p ∈ (0, 1)`, `f^{(p)}` is `f` viewed under `π_p^{⊗n}`); p. 223, Proposition 8.45 (`I[f] = σ² E[sens_f(x)]`) and its proof (`Inf_i[f] = σ² E[(D_{x_i} f)²]`); p. 224, the Margulis–Russo Formula (8.8) (for `f : {−1, 1}ⁿ → ℝ`, `d/dμ E[f^{(p)}] = (1/σ) Σᵢ f̂^{(p)}(i)`); p. 225, its proof, equation (8.9) (for monotone `f : {−1, 1}ⁿ → {−1, 1}`, `d/dp Pr_p[f(x) = −1] = d/dμ E[f^{(p)}] = I[f^{(p)}]/σ²`, where each bit is `−1` with probability `p`) and Remark 8.48 (for nonconstant monotone `f`, `Pr_p[f(x) = True]` is strictly increasing in `p`).
[MargulisRusso](../CslibFrontier/Foundations/BooleanAnalysis/MargulisRusso.lean) takes `true` as the bit of probability `p`, which is `−1` under `signVal`.
It states (8.8) for `0 < p < 1` as the derivative of `m ↦ E_{(1−m)/2}[f]` at `μ`, writing `f̂^{(p)}(i)` out as `E_p[f(x) (x_i − μ)/σ]` (`hasDerivAt_bernoulliAverage_one_sub_div_two`), and proves it as the book does, from the slope in `p`, `−2 Σᵢ E_p[D_{x_i} f]`, and `E_p[f(x) (x_i − μ)] = σ² E_p[D_{x_i} f]`.
It also states the classical form `d/dp E_p[f] = Σᵢ E_p[f(x^{i↦true}) − f(x^{i↦false})]` as an identity of polynomials in `p`, at every real `p`.
It states (8.9) in the same way, with right side `Σᵢ E_p[(D_{x_i} f)²]`, and also as the expected number of pivotal coordinates, `E_p[sens_f]`; the `p`-biased influence itself is not defined.
The left side reads as `Pr_p[f(x) = −1]` only for `p ∈ [0, 1]`, and the right side as `I[f^{(p)}]/σ²`, by the proof of Proposition 8.45, only for `0 < p < 1`, where Notation 8.43 defines `f^{(p)}` and `σ² > 0`: at `p = 0` or `1` a dictator still has slope `1` while `σ² = 0`.
§1.7, pp. 35–36, Exercise 1.9 (the multilinear representation of a Boolean function over `{0, 1}`; (c) its coefficients are integers) and p. 36, Exercise 1.11 ((b) a Boolean function with `deg(f) = k ≥ 1` has Fourier coefficients that are integer multiples of `2^{1−k}`).
[LowDegreeGranularity](../CslibFrontier/Foundations/BooleanAnalysis/LowDegreeGranularity.lean) assumes `deg(f) ≤ k` and also covers `k = 0`, where the coefficients are integers; its integer-valued lemma, coefficients in multiples of `2^{−k}` for degree at most `k`, uses part (c) of Exercise 1.9 through the Möbius coefficients, and the passage to signs is part (d).
§3.2, p. 74, Proposition 3.16, fourth item (a function to the integers computed by a decision tree of depth `k` has coefficients in multiples of `2^{−k}`), derived from that lemma in [DecisionTree/Granularity](../CslibFrontier/Computability/DecisionTree/Granularity.lean).
§3.4, p. 82, Theorem 3.36 (for `k ≥ 1`, the functions of degree at most `k` are learnable from random examples with error `0` in time `n^k · poly(n, 2^k)`) and §3.6, p. 89, Exercise 3.36 (prove it by rounding estimates, in light of Exercise 1.11): [ExactLowDegree](../CslibFrontier/MachineLearning/UniformLearning/ExactLowDegree.lean) proves the sample-complexity step toward Theorem 3.36, following Exercise 3.36.
It rounds each estimate to the nearest multiple of `2^{1−k}`, takes the failure probability `δ` as a parameter where the book fixes it at `1/10` (§3.4, p. 79, after Definition 3.27), and certifies the number of examples, `2 · 4^k · log(2N/δ)` for the `N` sets of at most `k` coordinates.
Its learner is noncomputable, and the running time `n^k · poly(n, 2^k)` with a circuit as output remains open on [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).
§3.1, p. 69, Definition 3.1 (the spectrum of `f` is `ε`-concentrated on degree up to `k` when its Fourier weight above degree `k` is at most `ε`); §3.2, p. 72, Definition 3.8 (the spectral `p`-norm; the spectral 1-norm is the sum of the absolute values of the Fourier coefficients); §3.4, p. 79, Definition 3.28 (`ε`-concentration on a collection `F`: the Fourier weight outside `F` is at most `ε`), and pp. 80–81, the proof of Theorem 3.29 (by Parseval, `𝔼[(f − g)²]` is the squared error of `g` on `F` plus the weight of `f` outside `F` when `g` is a combination of the characters of `F`); §3.6, p. 87, Exercise 3.16 (`f` is `ε`-concentrated on a collection of at most `L²/ε` sets, where `L` is its spectral 1-norm) and Exercise 3.17 (if `f` is `ε₁`-concentrated on `F` and `𝔼[(f − g)²] ≤ ε₂`, then `g` is `2(ε₁ + ε₂)`-concentrated on `F`).
[SpectralConcentration](../CslibFrontier/Foundations/BooleanAnalysis/SpectralConcentration.lean) bounds the weight on an arbitrary collection of sets, so the same statements cover the complement of `F` and the degree tails; it states Exercise 3.17 unconditionally as `W_T[g] ≤ 2(W_T[f] + 𝔼[(f − g)²])`, from which the book's form follows, and proves Exercise 3.16 with the sets `S` whose coefficient has absolute value at least `ε/L`.
§1.7, p. 34, Exercise 1.1(g), the Fourier expansion of the inner product mod 2 function `IP_{2n}(x, y) = (−1)^{x·y}`; [InnerProduct](../CslibFrontier/Foundations/BooleanAnalysis/InnerProduct.lean) computes all of its coefficients, with `x` the first and `y` the last `n` bits.
§5.1, pp. 116–117, Definition 5.7 (the sparsity of a PTF representation `f = sgn(p)` is the number of terms of `p`), Theorem 5.10 and Corollary 5.11 (any PTF representation of `IP_{2n}` has sparsity at least `2^n`, since by Exercise 1.1 every Fourier coefficient of `IP_{2n}` has absolute value `2^{−n}`); [InnerProductPTF](../CslibFrontier/Foundations/BooleanAnalysis/InnerProductPTF.lean) states it in `Cslib.BitString.two_pow_le_card_dotProduct_fstBits_sndBits_of_nonneg_mul` for every family `T` outside which the coefficients of `p` vanish, under the weaker sign condition `IP_{2n} · p ≥ 0`, which also allows `IP_{2n} = −1` where `p = 0`.
There the hypothesis `p ≠ 0` is needed for every `n` (`p = 0` and `T` empty meet the others); the book leaves `p ≢ 0` implicit, and for its representations with `sgn(0) = 1` it matters only for `n = 0`, where `IP_0 = 1`.
§2.6, p. 64, Exercise 2.39 (`NS_δ[f] ≤ 2α` for all `δ ∈ [0, 1]`, for `f : {−1, 1}ⁿ → {−1, 1}` with `α = min(Pr[f = 1], Pr[f = −1])`).
[Noise](../CslibFrontier/Foundations/BooleanAnalysis/Noise.lean) proves it for every `δ ≤ 1`, with `α` written as the relative Hamming distance to the nearer constant, as for Theorem 2.39 in [EdgeIsoperimetry](../CslibFrontier/Foundations/BooleanAnalysis/EdgeIsoperimetry.lean), and also bounds `NS_δ[f]` by twice the distance to either constant.
§9.6, p. 270, Corollary 9.32: if `Var[f] ≥ 1/2`, some `S` with `0 < |S| ≤ O(I[f])` has squared Fourier coefficient at least exp(−O(I[f]²)), proved by taking `ε = 1/8` in Friedgut's Junta Theorem (p. 269), whose spectral half comes from the proof of Theorem 9.28 (pp. 268–269); and Remark 9.33: if `Var[f] < 1/2`, the squared empty coefficient is at least `1/2`.
[LargeCoefficient](../CslibFrontier/Foundations/BooleanAnalysis/LargeCoefficient.lean) states Corollary 9.32 for any bound `K ≥ I[f]`, with `|S| ≤ 8 K` and the explicit bound `1 / (4 (M + 1) ^ m)`, `M = (256/9) K³ 81^(8 K)` and `m` equal to `8 K` rounded down; it takes the set `J` from the spectral step in [FriedgutJunta](../CslibFrontier/Foundations/BooleanAnalysis/FriedgutJunta.lean) (`exists_sum_filter_not_subset_fourierCoeff_sq_le_of_totalInfluence_le`), and counts the subsets of `J` of size at most `m` by `(|J| + 1)^m` (`sum_range_choose_le_add_one_pow`) in place of the book's `|J|^(8 I[f])`; both are exp(O(I[f]²)).
Remark 9.33 is not a separate lemma: it is Fact 1.14 (`expect_sub_expect_sq_signVal`) with `fourierCoeff_empty`, and gives strict inequality.
§4.2, p. 97, Proposition 4.14: indexing coefficients by the intersections of `T` with the tribes, `Tribes_{w,s}` (with `−1` as True) has coefficient `2(1 − 2^(−w))^s − 1` on the empty set and `2(−1)^(k+|T|) 2^(−kw) (1 − 2^(−w))^(s−k)` when `T` meets `k > 0` tribes; its proof is Exercise 4.6 (§4.6, p. 108).
[Tribes](../CslibFrontier/Foundations/BooleanAnalysis/Tribes.lean) proves both cases (`fourierCoeff_signVal_tribes_empty`, `fourierCoeff_signVal_tribes_of_ne_empty`) for `tribes` read as signs, whose `true` is the book's True.
§2.6, p. 61, Exercise 2.2 (majority, AND, OR, `±χᵢ` and `±1` are linear threshold functions), Exercise 2.5 (`f` is unate in the `i`th direction if it is monotone or antimonotone in that direction, and unate if unate in all directions; (a) `|f̂(i)| ≤ Infᵢ[f]` with equality if and only if `f` is unate in the `i`th direction) and Exercise 2.6 (linear threshold functions are unate); p. 63, Exercise 2.23 (`I[f] ≤ √n` for monotone `f` by Cauchy–Schwarz and Parseval, extended to unate `f`); §5.5, p. 130, Peres's Theorem (`NS_δ[f] ≤ O(√δ)` for every linear threshold function) and Definition 5.34 (a class is uniformly noise-stable if some `ε : [0, 1/2] → [0, 1]` with `ε(δ) → 0` as `δ → 0⁺` bounds `NS_δ[f]` for every member); p. 131, Theorem 5.35 (for `δ ∈ (0, 1/2]`, a class closed under negation and identification of input variables whose members on `n` bits have `I[f] ≤ A(n)` has `NS_δ[f] ≤ A(m)/m` with `m = ⌊1/δ⌋`) and its proof through `g_{z,π}(w) = f(z ∘ w_π)`; p. 132, the proof of Peres's Theorem and Remark 5.36 (its first sentence: the proof gives `1/√⌊1/δ⌋`; its second: this is at most `√(3/2) √δ` on `(0, 1/2]` and `√δ + O(δ^{3/2})` for small `δ`).
[PolynomialThreshold](../CslibFrontier/Foundations/BooleanAnalysis/PolynomialThreshold.lean) proves Exercise 2.2: threshold functions, which cover majority, AND (`threshold n n`), OR (`threshold n 1`) and the constants, and the literals `±χᵢ` are linear threshold functions.
[Peres](../CslibFrontier/Foundations/BooleanAnalysis/Peres.lean) proves Peres's Theorem with the `1/√⌊1/δ⌋` and `√(3/2) √δ` bounds of Remark 5.36 for an arbitrary finite coordinate type, not the remark's `√δ + O(δ^{3/2})` (tracked on [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131)), and states Definition 5.34 with a real-valued `ε` that bounds the noise sensitivities for `δ ∈ (0, 1/2]` rather than `ε : [0, 1/2] → [0, 1]`; clamping `ε` to `[0, 1]` (`max 0 (min ε 1)`) keeps the bound since noise sensitivities lie in `[0, 1]`, and at `δ = 0` they vanish; [NoiseSensitivityInfluence](../CslibFrontier/Foundations/BooleanAnalysis/NoiseSensitivityInfluence.lean) proves the exact identity `NS_{1/m}[f] = 𝔼_{z,π} I[g_{z,π}] / m` of its proof and Theorem 5.35 for classes also closed under adding dummy variables, which the book's proof uses implicitly (it takes `π` not onto).
Source issue: as printed, Theorem 5.35 is false: `{χ₁, −χ₁}` on one bit is closed under negation and identification, and `A(1) = 1`, `A(m) = 0` for `m ≥ 2` at `δ = 1/4` would give `NS_{1/4}[χ₁] ≤ 0`, while `NS_{1/4}[χ₁] = 1/4`.
[Monotone](../CslibFrontier/Foundations/BooleanAnalysis/Monotone.lean) proves Exercises 2.5(a) and 2.23 (monotone and unate cases), and [Unate](../CslibFrontier/Foundations/BooleanAnalysis/Unate.lean) proves Exercise 2.6.
Read on 2026-11-23: §3.6, p. 86, Exercise 3.6, that the spectral 1-norm is submultiplicative, as `sum_abs_fourierCoeff_mul_le` in [SpectralNorm](../CslibFrontier/Foundations/BooleanAnalysis/SpectralNorm.lean), through the product formula `fourierCoeff_mul`; Exercise 3.7(a), p. 86, that restriction reduces the spectral 1-norm, as `sum_abs_fourierCoeff_piecewise_le`; and the consequence of §3.3, p. 76, Proposition 3.21 that `F_{S|J} f` has spectral 1-norm at most `‖f̂‖₁` (used in the proof of Proposition 6.41), as `sum_abs_fourierCoeff_fourierCoeff_piecewise_le`.
§6.1, p. 144, Definition 6.2 (`ε`-regular functions), Remark 6.3 and the constant and parity cases of Example 6.4, and p. 145, Proposition 6.7, which detects regularity by the fourth spectral moment: [Regularity](../CslibFrontier/Foundations/BooleanAnalysis/Regularity.lean) writes `Var[f]` as `𝔼 (f − 𝔼 f)²` and assumes `0 ≤ ε` in part (2), which fails for negative `ε` when there is at least one coordinate.
§6.4, p. 157, Lemma 6.38, that an `ε`-biased density fools `f` up to `‖f̂‖₁ ε`: [Fooling](../CslibFrontier/Probability/Fooling.lean) proves it as `IsSmallBias.fools` for a distribution whose biases are the density's Fourier coefficients, with `0 ≤ ε`; Corollary 6.39, p. 157, the same for `f²` with `‖f̂‖₁² ε`, as `IsSmallBias.fools_sq`.
Propositions 6.40, p. 157, and 6.41, p. 158: [DeterministicEstimation](../CslibFrontier/Foundations/BooleanAnalysis/DeterministicEstimation.lean) certifies the queried points of the estimators and their number, for a sample space from the powering construction, not the running time; Proposition 6.41 is stated for any `f` with `|f| ≤ 1`, not only `±1`-valued `f`.
Theorems 6.42 and 6.43 are not formalized.
The Derandomized BLR Test, p. 159, and Theorem 6.44, p. 159 (proof to p. 160), with Remark 6.45, p. 159: [DerandomizedBLR](../CslibFrontier/Foundations/BooleanAnalysis/DerandomizedBLR.lean) defines the acceptance probability `derandomizedBLRAcceptance` for `y` drawn from a distribution, states the theorem for every `θ` with `|θ| ≤ |2 acc − 1|`, which covers the book's exact acceptance `1/2 + θ/2` of either sign and acceptance at least `1/2 + θ/2` for `θ ≥ 0`, and also in a spectral form for `θ = 2 acc − 1`; the bound `δ + ε / (2 (1 − 2δ))` for Remark 6.45's "nearly `δ`-close provided `ε ≪ δ`" is not in the book.
§4.1, p. 93, Definition 4.1 (a DNF is an OR of terms, each an AND of literals, no term contains a variable and its negation, and the width of a term is its number of literals); p. 94, Definitions 4.3 (the size of a DNF is its number of terms and its width the maximum width of a term) and 4.4 (the same for CNFs); pp. 95–96, Proposition 4.9 (a function computed by a DNF or CNF of size `s` is `ε`-close, for `ε ∈ (0, 1]`, to one computed by a DNF of width `log(s/ε)`), proved by deleting the terms with more than `log(s/ε)` literals and a union bound, with "a similar proof" for CNFs.
In [DNFWidth](../CslibFrontier/Foundations/BooleanAnalysis/DNFWidth.lean) the CNF case is read as giving a CNF, `0 < ε` suffices, and the narrow formula also has at most `s` terms.
The library's terms may repeat a literal or contain both signs of a variable, so the theorems also state that the narrow formula has no repeated literal in any term or clause, that each term of the narrow DNF is consistent (`Term.consistent`) and that no clause of the narrow CNF is a tautology (`CNF.isTautClause`): Definition 4.1's restriction, carried to clauses by Definition 4.4.
Its width, the length of its terms, is then the book's number of literals.
The base 2 of `log` comes from the book's List of Notation (p. xvi), not from Proposition 4.9 itself.
§9.5, p. 264, Corollary 9.25 (`Inf_i^{(ρ)}[f] ≤ Inf_i[f]^{2/(1+ρ)}` for `f : {−1, 1}ⁿ → {−1, 1}`, `0 ≤ ρ ≤ 1` and all `i`), introduced as the generalization of Corollary 9.12 obtained from the `(p, 2)`-Hypercontractivity Theorem; Corollary 9.12 (recorded on 2026-11-20) is its case `ρ = 1/3`.
[StableInfluenceBound](../CslibFrontier/Foundations/BooleanAnalysis/StableInfluenceBound.lean) proves Corollary 9.25 as `stableInfluence_signVal_le_influence_rpow`; [KahnKalaiLinial](../CslibFrontier/Foundations/BooleanAnalysis/KahnKalaiLinial.lean) uses the case `ρ = 1/3`, which is not stated separately.
§9.7, p. 276, Exercise 9.33 (a nonconstant monotone `f` has some `S ≠ ∅` with `f̂(S)² ≥ exp(−O(I[f]/Var[f]))`, with the hint that `|S| ≤ 1` is possible by the KKL Edge-Isoperimetric Theorem of §9.6, p. 267, and Proposition 2.21 of §2.2, p. 48, `Infᵢ[f] = f̂(i)` for monotone `f`).
[KahnKalaiLinial](../CslibFrontier/Foundations/BooleanAnalysis/KahnKalaiLinial.lean) proves it with `S` a singleton and the constant `10` (`exists_exp_neg_le_fourierCoeff_singleton_sq_of_monotone`), from the book-form edge-isoperimetric bound `MaxInf[f] ≥ (9 / Ĩ²) 9^{−Ĩ}` and `(9 / Ĩ²) 9^{−Ĩ} ≥ exp(−5 Ĩ)` for `Ĩ = I[f]/Var[f] > 0`.
Read on 2026-11-23: §3.5, p. 83, Theorem 3.37 (a concept class whose members have spectra `ε/4`-concentrated on collections of at most `M` sets is learnable using queries with error `ε` in time `poly(M, n, 1/ε)`), and p. 84, Definition 3.39 (the Fourier weight of `f` on the sets whose intersection with `J` is `S`, for `S ⊆ J`) and Proposition 3.40 with its proof (query access to `f` estimates that weight within `ε` except with probability `δ` in time `poly(n, 1/ε) log(1/δ)`, by a Chernoff bound on `O(log(1/δ)/ε²)` samples); §3.6, p. 89, Exercise 3.39 (deduce Theorem 3.37 from the Goldreich–Levin Algorithm).
[KushilevitzMansour](../CslibFrontier/MachineLearning/UniformLearning/KushilevitzMansour.lean) proves the query and sample step toward Theorem 3.37 for the largest such class, `concentratedClass ι M (ε/4)`: it certifies samples and queries, not running time, which remains open on [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131) since the bucket search has no cap on the number of buckets.
It goes through the combined error bound on accurate samples rather than through the Goldreich–Levin list guarantee followed by Theorem 3.29, the route of Exercise 3.39.
For Proposition 3.40 only the sample bound of the proof is proved, with the explicit count `(2/ε²) log(2/δ)`; queries and time are not certified.
§9.2, p. 256, inequality (9.7) (`W^{≤k}[f] ≤ 3^k α^{3/2}` for `f : {−1, 1}ⁿ → {0, 1}` of mean `α` and every `k`); §9.5, p. 264, the Level-k Inequalities (`W^{≤k}[f] ≤ (2e/k · ln(1/α))^k α²` for a positive integer `k ≤ 2 ln(1/α)`); §9.7, p. 273, Exercise 9.18 ((a) `W¹[f] ≤ (α^{2/(1+ρ)} − α²)/ρ` for `0 < ρ ≤ 1`; (b) the sharp Level-1 Inequality `W¹[f] ≤ 2α² ln(1/α)` of Remark 5.28, §5.4, p. 126, by letting `ρ` tend to `0` from above).
[LevelK](../CslibFrontier/Foundations/BooleanAnalysis/LevelK.lean) proves (9.7), the Level-k Inequalities and both parts of Exercise 9.18 for `f = 1_A`, written `A.indicator 1`; Remark 5.28's extension of the sharp bound to `f : {−1, 1}ⁿ → [−1, 1]` with `α = E[|f|]` is not formalized.
Also §3.5, p. 83, the Goldreich–Levin Theorem (unnumbered: given query access to `f : {−1, 1}ⁿ → {−1, 1}` and `0 < τ ≤ 1`, a `poly(n, 1/τ)`-time algorithm outputs with high probability a list containing every set whose Fourier coefficient has absolute value at least `τ`, and only sets whose coefficient has absolute value at least `τ/2`, hence by Parseval at most `4/τ²` sets), and pp. 84–85, its proof (buckets split one coordinate at a time and are discarded at estimated weight at most `τ²/2`; estimates within `τ²/4` keep every heavy set, leave no singleton bucket of a set whose coefficient has absolute value at most `τ/2`, and keep at most `4/τ²` buckets).
The same module proves the query and sample step toward the Goldreich–Levin Theorem for a query tree running the bucket search: from `m ≥ (32/τ⁴) log(2(n+2)2^n/δ)` samples and at most `m(2n+3)` non-adaptive queries, its list has the two guarantees and at most `4/τ²` sets except with probability `δ`, with the strict second guarantee `> τ/2` and without the assumption `τ ≤ 1`; it keeps the buckets with estimate at least `τ²/2` rather than discarding those at most `τ²/2`.
The running time `poly(n, 1/τ)` is not certified and remains open on [#2131](https://github.com/cslib-community/cslib-frontier/issues/2131).

<a id="oliveirapichsanthanam2019"></a>
## oliveirapichsanthanam2019

Igor Carboni Oliveira, Ján Pich and Rahul Santhanam.
*Hardness Magnification near State-Of-The-Art Lower Bounds*.
CCC 2019, LIPIcs 137, 27:1–27:29. https://doi.org/10.4230/LIPIcs.CCC.2019.27 . Lemma numbers follow the journal version, Theory of Computing 17(11), 2021.
Bibliographic data comes from the repository bibliography.
The Lean modules cite its Lemmas 4.1 and 4.7 and Theorem 1.4.
For Theorem 1.4, worker meta-proj read the authors' copy of ECCC TR18-158 revision 1 (https://www.dcs.warwick.ac.uk/~igorcarb/documents/papers/OPS19.pdf) on 2026-11-11 UTC: Theorem 4 there is the same statement with an unspecified universal constant `c ≥ 1`, its proof in Section 4.1 uses `c = 10`, Definition 9 has no-instances of size `> s₂`, and Section 2 says gate types do not matter.
The journal numbering `1.4` was not checked against the journal text.

<a id="oliveirasanthanam2017"></a>
## oliveirasanthanam2017

Igor Carboni Oliveira and Rahul Santhanam.
*Conspiracies Between Learning Algorithms, Circuit Lower Bounds, and Pseudorandomness*.
CCC 2017, LIPIcs 79, 18:1–18:49. https://doi.org/10.4230/LIPIcs.CCC.2017.18 . Full version arXiv:1611.01190.
Bibliographic data comes from the repository bibliography and the LIPIcs record.
The Lean module [CryptoHardness/NaturalProperty.lean](../CslibFrontier/MachineLearning/UniformLearning/CryptoHardness/NaturalProperty.lean) cites Theorem 8, (1) ⇒ (5) (a learner yields a distinguisher, hence a natural property) and Lemma 4 from the arXiv full version; the page locators are not recorded in the results registry.

<a id="oliveirasanthanam2018"></a>
## oliveirasanthanam2018

Igor Carboni Oliveira and Rahul Santhanam.
*Hardness Magnification for Natural Problems*.
FOCS 2018, 65–76. https://doi.org/10.1109/FOCS.2018.00016 . Full version ECCC TR18-139.
Bibliographic data comes from the repository bibliography; the paper was not inspected for this chapter.
The Lean module documentation quotes Theorems 1, 5, 17 and 27 and Lemma 16 from the ECCC full version with page locators.

<a id="ollinger2008"></a>
## ollinger2008

Nicolas Ollinger.
*Two-by-Two Substitution Systems and the Undecidability of the Domino Problem*.
In Arnold Beckmann, Costas Dimitracopoulos and Benedikt Löwe (eds.), *Logic and Theory of Algorithms*, Lecture Notes in Computer Science 5028, 476–485, Springer, 2008.
[Publisher record](https://doi.org/10.1007/978-3-540-69407-6_51).
Bibliographic metadata checked at the publisher on 2026-11-16 by an authoring Codex agent.
Cited as the origin of the tile set attributed to Ollinger in [Jeandel–Vanier](#jeandelvanier2020), manuscript p. 24 and Figure 13 on p. 25.
The paper's full text was not available in this pass: internal theorem/figure locator not verified.
The concrete formalization follows the pinned lean-wang transcription described in that registry entry.

<a id="openaich26"></a>
## openaich26

OpenAI.
*Existential–universal real sentences in the counting hierarchy*.
Preprint, 4 October 2026, not peer reviewed.
Bibliography key `OpenAI2026CountingHierarchy`; source revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`.
[Section 2 TeX](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Existential-universal-real-sentences-in-the-counting-hierarchy-October-4-2026/build/sections/02-counting.tex) and Appendix A (`08-existential-bound.tex`) were read on 2026-11-14 for the CRT circle identity, dyadic error, first-flag sign argument, and its use in the appendix.
The mathematical layer allows arbitrary pairwise coprime positive moduli and explicit numerical bounds.
The numerical prime-window corollary uses the existing elementary prime-count estimate, and the product algorithm averages over generators instead of selecting one.
`CountingHierarchy.ResidueSign` formalizes Proposition 2.6's computational sign conclusion for one uniform residue evaluator, binary magnitude/exclusion bounds and the disclosed strict oracle/majority-verifier levels.
Its checked clients illustrate 8 → 13 → 21 arithmetic bookkeeping and the 21 → 24 → 25 → 26 sign/choice/language compatibility chain; characteristic coefficients, real geometry and the ETR theorem remain outside this development.

<a id="openai-logspace26"></a>
## openai-logspace26

OpenAI.
*Exact Derandomization of Logarithmic Space: L = RL = BPL*.
Preprint, 23 September 2026, not peer reviewed; cited here only for construction provenance.
Accompanying Lean file at revision `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/CatalyticComparison.lean .

<a id="openai-metric-ports26"></a>
## openai-metric-ports26

OpenAI.
*Circuit Lower Bounds for Hamiltonian Cycle and the Permanent*, Lemma 4.1 and Theorem 4.2, and *Euclidean Geometry in the Asymptotic Spectrum of Tensors*, Definition 11.1.
AI-authored, unrefereed preprints dated 24 November 2026.
Bibliography keys `OpenAI2026HamiltonianPermanent` and `OpenAI2026EuclideanSpectrum`.
The [graph obstruction](../CslibFrontier/Probability/MarkovChain/PortObstruction.lean) smooths a walk by barycentric averaging, realizes it with a finite set of labels and replaces each vertex by a copy of the candidate graph.
This gives the explicit integer bound `n < (8d)^(2 ⌈7000(1+b)⌉)` on the order of a degree-`d` graph with uniform squared Poincaré constant `b` in a family of complete CAT(0) spaces without ports.
[Graph amplification](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Circuit-lower-bounds-for-Hamiltonian-cycle-and-the-permanent-November-24-2026/build/entropy.tex#L54-L117).
[Ports](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Euclidean-geometry-in-the-asymptotic-spectrum-of-tensors-November-24-2026/build/port-graphs.tex#L10-L36).

<a id="openaieth26"></a>
## openaieth26

OpenAI.
*The Exponential Time Hypothesis is False*.
Manuscript dated 17 October 2026, revised 25 October 2026.
Source revision `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`.
[PDF](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/paper.pdf); [primary TeX](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/The-Exponential-Time-Hypothesis-is-False-October-25-2026/build/main_full_version.tex).
The interpolation-route statement, metadata and label were checked in freshly retrieved TeX on 2026-11-02; full proof and PDF pagination were not independently audited.

<a id="orzelsrinivasantavenasyehudayoff25"></a>
## orzelsrinivasantavenasyehudayoff25

Ian Orzel, Srikanth Srinivasan, Sébastien Tavenas and Amir Yehudayoff.
"The Algebraic Cost of a Boolean Sum."
*45th IARCS Annual Conference on Foundations of Software Technology and Theoretical Computer Science (FSTTCS 2025)*, LIPIcs 360, 47:1–47:13, Schloss Dagstuhl, 2025 (bibliography key `OrzelSrinivasanTavenasYehudayoff2025`). https://doi.org/10.4230/LIPIcs.FSTTCS.2025.47 ; open HTML https://drops.dagstuhl.de/storage/00lipics/lipics-vol360-fsttcs2025/html/LIPIcs.FSTTCS.2025.47/LIPIcs.FSTTCS.2025.47.html . Checked against the open Dagstuhl edition on 2026-11-22: §1.2 Definition 1 (p. 47:3, when a polynomial sequence simulates formulas via polynomial-size projections), Lemma 4 (p. 47:4, attributing to [Valiant 1979](#valiant79algebra) that both `perm` and `det` simulate formulas), Lemma 5 (p. 47:4, two variable instances suffice for Boolean sums), and §2 (pp. 47:5–47:6, field of characteristic not two, scalar-permitting projection conventions, projection-based determinantal complexity `dc(f)` as the minimum `k` such that `f` is a projection of `det_k`, and the statement that `dc(f) < ∞` for all `f`).
[Permanent/Formula.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Permanent/Formula.lean), [Determinant/Projection.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Determinant/Projection.lean), and [Determinant/Formula.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Determinant/Formula.lean) prove the explicit `(F.size + 1) × (F.size + 1)` plain-projection (`IsProjection`, without outer scalar multiplier) formula-simulation bounds and projection universality over arbitrary commutative semirings (for `permanent`) and commutative rings (for `det`, using `-1` along the subdiagonal of `N - 1` via `IsSubstABP`), which in turn upper-bounds the affine-linear `determinantalComplexity` of [DeterminantalComplexity.lean](../CslibFrontier/Computability/Circuit/Arithmetic/DeterminantalComplexity.lean).

<a id="ozdaglar2008"></a>
## ozdaglar2008

Asuman Ozdaglar.
"Price Competition with Elastic Traffic."
*Networks* 52(3), 141–155, 2008 (bibliography key `Ozdaglar2008`). https://doi.org/10.1002/net.20239 . Bibliographic metadata checked via Crossref/DOI records on 2026-11-24 UTC; the Wiley journal PDF was not directly inspected, so no internal theorem or page locator from `Ozdaglar2008` is claimed.
The elastic-traffic oligopoly `2 / 3` efficiency theorem (`elastic_oligopoly_surplus_two_thirds`, `elastic_oligopoly_efficiency_ge_two_thirds`, and `elasticTightness_surplus_lt_two_thirds_add`) in [Oligopoly.lean](../CslibFrontier/GameTheory/Congestion/Pricing/Oligopoly.lean) is verified directly against the textbook statement in [ozdaglarsrikant2007](#ozdaglarsrikant2007), Section 22.2.6, Theorem 22.4, p. 585 (which cites an earlier working-paper version of this article).

<a id="ozdaglarsrikant2007"></a>
## ozdaglarsrikant2007

Asuman Ozdaglar and R. Srikant.
"Incentives and Pricing in Communications Networks."
Chapter 22 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 571–591 (bibliography key `OzdaglarSrikant2007`). https://doi.org/10.1017/CBO9780511800481.024 . Checked firsthand on 2026-11-24 UTC against the published book PDF (SHA-256 `e1591ad20619742a6b2d71a0380033aa086e4faef1391a16992836b545ab773f`, Chapter 22 on printed pp. 571–591): Section 22.2.1 (pp. 579–580: Example 22.1 two-link quadratic/linear latency comparison of social optimum, Wardrop equilibrium, monopoly pricing, and duopoly pricing), Section 22.2.2 (pp. 581–582: Eq. (22.22) priced Wardrop equilibrium, Eq. (22.23) social optimum, Eq. (22.24) Pigovian marginal-congestion tolls, and Eq. (22.25) consumer surplus and monopoly profit decomposition), Section 22.2.3 (p. 582: monopoly equilibrium efficiency `= 1`), Section 22.2.4 (p. 583: Eq. (22.26) oligopoly equilibrium, Eq. (22.27) interior oligopoly price characterization, and Eq. (22.28) worst-case oligopoly efficiency ratio), Section 22.2.5 (p. 584: Example 22.2 exact `5 / 6` witness and Theorem 22.3 tight `5 / 6` oligopoly efficiency bound), and Section 22.2.6 (pp. 585–586: Theorem 22.4 tight `2 / 3` oligopoly efficiency bound for elastic traffic with concave `u(x)` and concave marginal utility `u'(x)`, Figure 22.2 parallel-serial topology, and Theorem 22.5 tight `1 / 2` efficiency bound for full-demand strict oligopoly equilibria on parallel-serial networks).
Sections 22.1 and 22.4 (Kelly primal-dual congestion control and time-scale stability) remain open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).
Cited by [PricedWardrop.lean](../CslibFrontier/GameTheory/Congestion/Pricing/PricedWardrop.lean), [Oligopoly.lean](../CslibFrontier/GameTheory/Congestion/Pricing/Oligopoly.lean), and [ParallelSerial.lean](../CslibFrontier/GameTheory/Congestion/Pricing/ParallelSerial.lean).

<a id="papadimitriou07"></a>
## papadimitriou07

Christos H. Papadimitriou.
"The Complexity of Finding Nash Equilibria."
Chapter 2 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 29–52. https://doi.org/10.1017/CBO9780511800481.004 . Checked firsthand on 2026-11-24 against the chapter text (pp. 29–52): Section 2.1.1, Example 2.2 (pp. 30–31: symmetric bimatrix game `B = Aᵀ`, the `3 × 3` symmetric example `[[0, 3, 0], [0, 0, 3], [2, 2, 2]]`, and existence of symmetric Nash equilibria), Section 2.3.1, Theorem 2.4 (p. 34: polynomial reduction from two-player `Nash` to `Symmetric Nash` via `C = [[0, A], [Bᵀ, 0]]` after shifting `A, B > 0`), Section 2.6.6 (p. 45: `ε`-approximate Nash equilibrium definition, the citation to Daskalakis, Mehta and Papadimitriou for `(1/2)`-approximate Nash equilibria in two-player games — without printing the two-step construction formula — and the citation to Lipton, Markakis and Mehta 2003), and Sections 2.7–2.7.1 (pp. 45–48: Chicken / drivers game `[[4, 1], [5, 0]]`, the correlated-equilibrium inequalities `(CE)`, product-distribution equivalence to mixed Nash equilibria, the 50–50 traffic signal `C₁ = [[0, 1/2], [1/2, 0]]` and social-welfare-optimal correlated equilibrium `C₂ = [[1/3, 1/3], [1/3, 0]]`, Figure 2.4, Theorem 2.5 on p. 47 that in any nondegenerate two-player game the Nash equilibria are vertices of the `(CE)` polytope, and the remarks on pp. 47–48 on linear-objective optimality and non-vertex Nash equilibria in games with three or more players).
Cited by `CslibFrontier/GameTheory/Strategic/{ApproxNash,Correlated,Symmetric}.lean` and `CslibFrontier/GameTheory/Bimatrix/{CorrelatedPolytope,Symmetric}.lean`.

<a id="papadimitriou94ppad"></a>
## papadimitriou94ppad

Christos H. Papadimitriou.
"On the Complexity of the Parity Argument and Other Inefficient Proofs of Existence."
*Journal of Computer and System Sciences* 48(3), 498–532, 1994. https://doi.org/10.1016/S0022-0000(05)80063-7 . Bibliographic metadata checked against `references.bib` (`Papadimitriou1994PPAD`); the journal text was not inspected, so internal theorem numbers are not claimed.
Cited for the complexity class `PPAD`, canonical `EndOfLine` completeness, and containment of two-player Nash equilibrium.

<a id="papai00"></a>
## papai00

Szilvia Pápai.
*Strategyproof Assignment by Hierarchical Exchange*.
Econometrica 68(6), 1403–1433, 2000. https://doi.org/10.1111/1468-0262.00166 . Bibliographic metadata checked via search records on 2026-11-24 UTC; the publisher's text is paywalled and was not inspected, so no internal lemma or theorem locator is claimed.
Cited as standard background (`Papai2000`) for the equivalence between strong group strategy-proofness and strategy-proofness plus non-bossiness on strict private-good preference domains (`HousingMechanism.isGroupStrategyProof_iff`).

<a id="pedersen1991"></a>
## pedersen1991

Torben Pryds Pedersen.
"Non-Interactive and Information-Theoretic Secure Verifiable Secret Sharing."
*Advances in Cryptology — CRYPTO '91*, LNCS 576, 129–140, Springer, 1992. https://doi.org/10.1007/3-540-46766-1_9 . Publisher's PDF, https://link.springer.com/content/pdf/10.1007/3-540-46766-1_9.pdf , fetched on 2026-11-18 UTC (SHA-256 `79c0634a04b7bc869715770519eca9dcfcb3011012dbff054b9487b187558b18`): a 12-page scan of the complete printed pp. 129–140 (PDF page = printed page − 128).
Read on 2026-11-18: Section 2 (p. 130: primes `q | p − 1`, `G_q` the order-`q` subgroup of `Z_p^*`, `g` a generator) and all of Section 3 (p. 131): `g` and `h` are chosen so that nobody knows `log_g h`, by a trusted center or a coin-flipping protocol; the commitment is `E(s, t) = g^s h^t` for `s ∈ Z_q` and random `t ∈ Z_q`; Theorem 3.1 states that for uniform `t` the commitment is uniform on `G_q` (first sentence) and that `s ≠ s'` with `E(s, t) = E(s', t')` gives `t ≠ t' mod q` and `log_g h = (s − s')/(t' − t) mod q` (second sentence).
The theorem states no game or computational assumption, and the first sentence needs `h ≠ 1`, which the condition on `log_g h` implies.
Sections 4–6 were not checked.

<a id="peikert2016"></a>
## peikert2016

Chris Peikert.
*A Decade of Lattice Cryptography*.
Foundations and Trends in Theoretical Computer Science 10(4), 283–424, 2016. https://doi.org/10.1561/0400000074 ; author PDF dated February 17, 2016 at https://web.eecs.umich.edu/~cpeikert/pubs/lattice-survey.pdf . Consulted in the February 17, 2016 author PDF: Section 4.2.1, unnumbered "Normal form" paragraph, printed p. 23, for the sample transformation from `(n + m)`-sample uniform-secret LWE to `m`-sample error-secret (normal-form) LWE by inverting the top `n × n` block, losing the singular-block probability (`NormalForm.lean` formalizes these finite probability steps on framed-integer `ProbComp` callers toward the hardness reductions in #3673, without certifying polynomial-time inversion).

<a id="pennocksami07"></a>
## pennocksami07

David M. Pennock and Rahul Sami.
"Computational Aspects of Prediction Markets."
Chapter 26 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 651–676 (bibliography key `PennockSami2007`). https://doi.org/10.1017/CBO9780511800481.028 . Checked against the 2007 Cambridge University Press book text (printed pp. 651–676) for §26.4.1 (pp. 663–664: Hanson's sequential market scoring rules, the LMSR cost function `C(q) = b ln(∑ e^{q_i / b})`, instantaneous softmax prices `∂C/∂q_i`, equivalence between cost-function trading and logarithmic MSR updates, and the `b ln |Ω|` worst-case market-maker loss bound).
In [LMSR.lean](../CslibFrontier/GameTheory/PredictionMarket/LMSR.lean), the KL-divergence Bregman identity (`lmsrCost_bregmanDivergence_eq`) and global convexity (`convexOn_lmsrCost`) are proved as mathematical companions (not stated in Chapter 26), and Exercise 26.3 (pp. 674–675, conditional securities `S_{φ|ψ}` and conditional cost function `C_ψ`) remains open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).

<a id="peterson1981"></a>
## peterson1981

Gary L. Peterson.
"Myths About the Mutual Exclusion Problem."
*Information Processing Letters* 12(3), 115–116, June 1981. https://doi.org/10.1016/0020-0190(81)90106-X ; Yale course copy of the typeset article: https://zoo.cs.yale.edu/classes/cs323/doc/Peterson.pdf . Checked against that copy on 2026-11-22 UTC (SHA-256 `850d4d35ce7474de2e8e0271372878282afc231a86c221e7b77b08cda049e85e`, 2 pages, printed pp. 115–116): the 2-process protocol and non-atomic busy-wait convention in Fig. 1 (p. 115), the two primitive solutions in Fig. 2 (p. 116), and the `(n - 1)`-level `n`-process filter protocol in Fig. 3 ("Simple n process solution", p. 116: `Q[1..n]` initially `0`, `TURN[1..n - 1]` initially `1`, setting `Q[i] := j; TURN[j] := i; wait until (∀ k ≠ i, Q[k] < j) or TURN[j] ≠ i`, then `Critical Section; Q[i] := 0`, with the generalized correctness proof left to the reader).
Cited in `CslibFrontier/Computability/Distributed/MutualExclusion/FilterLock.lean` for `filterLock` and `filterLock_mutualExclusion`, where Lean uses `0`-indexed `Fin n` / `Fin (n - 1)` arrays (`level` and `victim` initialized to `0`) and evaluates each waiting room's test via individual atomic reads (`checkVictim` reading `victim[r]` and `checkLevel` accumulating processes read below room `r`), with `card_at_level_le` and `filterLock_step_progress` as proof infrastructure and `filterLock_exists_cs_execution` giving an enabled finite trying-only execution witness (fair-execution progress across infinite runs remains open under #7296).

<a id="peterson1982"></a>
## peterson1982

Gary L. Peterson.
"An $O(n \log n)$ Unidirectional Algorithm for the Circular Extrema Problem."
*ACM Transactions on Programming Languages and Systems* 4(4), 758–762, 1982. https://doi.org/10.1145/69622.357194 . The library's key is `Peterson1982`.
Bibliographic metadata checked via DOI and search summaries on 2026-11-22 UTC; the journal PDF was not directly inspected, so internal theorem and page locators are not claimed.
[RingElection/Peterson.lean](../CslibFrontier/Computability/Distributed/RingElection/Peterson.lean) formalizes all-initially-active basic two-hop unidirectional FIFO ring election steps toward [#7200](https://github.com/cslib-community/cslib-frontier/issues/7200) (with all `n` nodes starting active in `twoHopAllActiveInit`, rather than spontaneous wakeup or the `1.44 n log n` Fibonacci-threshold refinement): strict-local-peak active-subring halving `2 * active_{k + 1} ≤ active_k` (`twoHopAllActive_phase_halving`), one-step FIFO confluence (`twoHopStep_comm`), unique-maximum termination (`twoHopAllActive_elects_leader`), and the `2 * n * Nat.log 2 n + n` asynchronous message bound (`twoHopAllActive_messages_le`).

<a id="pighizzini2009"></a>
## pighizzini2009

Giovanni Pighizzini.
"Nondeterministic One-Tape Off-Line Turing Machines and Their Time CslibFrontier." arXiv:0905.1271v1 [cs.FL], 2009. https://arxiv.org/abs/0905.1271v1 . The v1 text was read for §1, Theorem 1 (§3: crossing sequences of bounded length imply regularity, stated for nondeterministic machines under the weak measure), and the opening of §4 with Theorem 3 (attribution of the deterministic `n log n` bound to Trakhtenbrot, Hartmanis and Kobayashi).
The arXiv record says the paper was to appear in the *Journal of Automata, Languages and Combinatorics*; secondary indexes place it in volume 14 (2009), pp. 107–124.
The journal version was not inspected.

<a id="plautroughgarden20"></a>
## plautroughgarden20

Benjamin Plaut and Tim Roughgarden.
"Almost Envy-Freeness with General Valuations."
*SIAM Journal on Discrete Mathematics* 34(2), 1039–1068, 2020. https://doi.org/10.1137/19M124397X . Bibliographic metadata checked via DOI/search records on 2026-11-24 UTC; the journal PDF was not inspected on disk, so no internal theorem or page locator is claimed.
Cited (`PlautRoughgarden2020`) for strong envy-freeness up to any good (`MonotoneValuation.IsEFX`).

<a id="pohl72"></a>
## pohl72

Ira Pohl.
"A Sorting Problem and Its CslibFrontier."
*Communications of the ACM* 15(6), 462–464, 1972. https://doi.org/10.1145/361405.361423 . Bibliographic data from the DOI record.
Cited, following the customary attribution in Knuth §5.3.3 and CLRS §9.1, for the adversary argument showing that `⌈3n/2⌉ - 2` comparisons are necessary and sufficient to find the minimum and maximum of `n` elements.
The paper is paywalled and was not inspected, so no theorem number is cited.

<a id="pomfrit26"></a>
## pomfrit26

Carsten Baum, Marvin Beckmann, Ward Beullens, Shibam Mukherjee and Christian Rechberger.
*Concretely Efficient Blind Signatures Based on VOLE-in-the-Head Proofs and the MAYO Trapdoor*, USENIX Security 2026 prepublication (`PoMFRIT2026`). https://www.usenix.org/system/files/conference/usenixsecurity26/sec26_prepub_baum.pdf . Read on 2026-11-21: Definition 3.1, printed p. 7, samples independent uniform target slots, allows arbitrary preimage queries, counts all calls against a fixed budget, and requires one more valid answer at distinct indices.
`Signature.oneMoreExperiment` implements that finite classical experiment when given its uniform target sampler and the relevant key and preimage algorithms.
It does not implement the paper's blind-signature proof or quantum adversaries.
The original collision-strategy theorem retains the signer's validation probability, including failed preimage calls.

<a id="post46"></a>
## post46

Emil L. Post.
"A Variant of a Recursively Unsolvable Problem."
*Bulletin of the American Mathematical Society* 52(4), 264–268, 1946. https://doi.org/10.1090/S0002-9904-1946-08555-9 . Bibliographic metadata only.
The publisher's PDF returned an access error and was not inspected.
It is cited as the origin of the correspondence problem and its unsolvability, as in [sipser13](#sipser13), §5.2.

<a id="procacciatennenholtz13"></a>
## procacciatennenholtz13

Ariel D. Procaccia and Moshe Tennenholtz.
"Approximate Mechanism Design without Money."
*ACM Transactions on Economics and Computation* 1(4), Article 18 (18:1–18:26), 2013 (preliminary version in EC 2009). https://doi.org/10.1145/2542174.2542175 . Author-hosted TEAC copy inspected on 2026-11-11 at https://procaccia.info/wp-content/uploads/2020/03/facility.pdf : checked Section 3 (p. 18:7: randomized facility-location model, strategyproofness, group strategyproofness in the weak sense with strong group strategyproofness noted in passing, social cost, approximation ratio) and Section 3.1 (pp. 18:7–18:8: median optimality on `ℝ` with `med(x)` choosing `x_{(n-1)/2}` for even `n`, and weak group strategyproofness of fixed `k`-th order statistics attributed to [moulin80](#moulin80)).
Re-inspected on 2026-11-24 for Section 3.2 (pp. 18:8–18:11, Table I: maximum cost `mc`, midpoint `cen(x) = (lt(x) + rt(x)) / 2` optimality and non-strategyproofness, Theorem 3.1 leftmost `2`-approximation, Theorem 3.2 deterministic `2` lower bound for `n ≥ 2`, Mechanism 1 Left–Right–Midpoint returning `lt(x)`, `rt(x)`, `cen(x)` with probabilities `1/4, 1/4, 1/2`, Theorem 3.3 weak group strategyproofness and `3/2`-approximation together with the `n ≥ 3` failure of strong group strategyproofness noted in §3 on p. 18:7, and Lemmas 3.5–3.6 and Theorem 3.4 giving the `3/2` randomized lower bound for `n ≥ 2`), formalized in [FacilityLocation/MaxCost.lean](../CslibFrontier/GameTheory/Mechanism/FacilityLocation/MaxCost.lean).
Cited in [the mechanism-design chapter](algorithms-and-memory/mechanism-design.md).

<a id="radhakrishnan97"></a>
## radhakrishnan97

Jaikumar Radhakrishnan.
"An Entropy Proof of Bregman's Theorem."
*Journal of Combinatorial Theory, Series A* 77(1), 161–164, 1997. https://doi.org/10.1006/jcta.1996.2727 . Bibliographic data from the DOI record.
Cited only as an alternative proof; the library does not formalize it.

<a id="rado62"></a>
## rado62

Tibor Radó.
*On Non-Computable Functions*.
The Bell System Technical Journal 41(3), 877–884, 1962. https://doi.org/10.1002/j.1538-7305.1962.tb00480.x ; scan at https://archive.org/details/bstj41-3-877 . Read in the archive.org text on 2026-11-08: Section V, Theorem (`Σ(n)` eventually exceeds every computable `f`, so `Σ` is not computable), proved with an auxiliary computable majorant of `f`; Section VI defines the shift function `S(n)` and derives the same domination from `S(n) ≥ Σ(n)`.

<a id="raychaudhuriwilson1975"></a>
## raychaudhuriwilson1975

Dijen K. Ray-Chaudhuri and Richard M. Wilson.
“On `t`-Designs.”
*Osaka Journal of Mathematics* 12(3), 737–744, 1975.
Bibliographic metadata from search summaries on 2026-11-08; the full text was not inspected in this pass.
The manual attributes only the uniform bound `C(n, s)` for `s` allowed intersection sizes to this paper.

<a id="razborovrudich1997"></a>
## razborovrudich1997

Alexander A. Razborov and Steven Rudich.
*Natural Proofs*.
Journal of Computer and System Sciences 55(1), 24–35, 1997. https://doi.org/10.1006/jcss.1997.1494 . Bibliographic data comes from the repository bibliography.
The [journal text](https://www.cs.toronto.edu/tss/files/papers/1-s2.0-S002200009791494X-main.pdf) gives the generator conjecture on p. 26, defines hardness before Theorem 4.1 on p. 30, and uses a truth-table test on the constructed function family in equation (3) on p. 31.
Section 3.2 (p. 27), which states Razborov's GF(2) rank property against AC⁰[2] abstractly and leaves its largeness as an exercise, was inspected for [#4451](https://github.com/cslib-community/cslib-frontier/issues/4451).

<a id="reedsmithvetta2004"></a>
## reedsmithvetta2004

Bruce Reed, Kaleigh Smith and Adrian Vetta.
"Finding Odd Cycle Transversals."
*Operations Research Letters* 32(4), 299–301, 2004. https://doi.org/10.1016/j.orl.2003.10.009 . Bibliographic data from the DOI record; the full text was not inspected.
It introduces iterative compression and the odd cycle transversal algorithm used in [OddCycleTransversal](../CslibFrontier/Algorithms/Lean/IterativeCompression/OddCycleTransversal.lean), cited without a theorem locator.
Its stated running time is `O(4^k · kmn)`, as recorded by [hueffner2009](#hueffner2009), p. 86; the `3^k` analysis formalized here is credited to [hueffner2009](#hueffner2009), Theorem 1.
The textbook presentation cited alongside it is [cygan2015](#cygan2015), Section 4.4; its statement number (Theorem 4.17, `O(3^k · k n (n + m))`) comes from secondary sources and is not used in the Lean docstrings.

<a id="regev04"></a>
## regev04

Oded Regev.
*Lattices in Computer Science*, Lecture 3: "CVP Algorithm" (scribe: E. Kaplan).
Lecture notes, Tel Aviv University, Fall 2004. https://cims.nyu.edu/~regev/teaching/lattices_fall_2004/ln/cvp.pdf . Inspected on 2026-11-08: §1 (the nearest-plane algorithm with `δ = 3/4` LLL, input `B ∈ ℤ^{m×n}`, `t ∈ ℤᵐ`), Claims 4–5, and Lemma 6 (`‖x − t‖ ≤ 2^{n/2} ‖y − t‖` for the output `x` and a closest lattice point `y`).
The notes attribute the factor `2 (2/√3)ⁿ` to Babai's algorithm and present `2^{n/2}` for simplicity.

<a id="regev2009"></a>
## regev2009

Oded Regev.
"On lattices, learning with errors, random linear codes, and cryptography."
*Journal of the ACM* 56(6), Article 34 (1–40), 2009. https://doi.org/10.1145/1568318.1568324 ; author PDF dated May 2, 2009 at https://cims.nyu.edu/~regev/papers/qcrypto.pdf . Consulted in the May 2, 2009 author PDF: Lemma 4.1 (pp. 30–31, non-negligible fraction of good secrets from uniform-secret advantage) and Lemma 4.2 (p. 31, efficient search from an all-secret distinguisher for prime `2 ≤ p ≤ poly(n)`).
`SearchToDecision.lean` formalizes a finite probability step toward Regev's reduction (#3673) over arbitrary prime `q`, using a fixed-batch distinguisher's absolute averaged acceptance gap, fresh per-trial secret re-randomization over `(n * q + 1) * N * m` samples, noncomputable argmax selection, and an explicit Hoeffding bound, without an `IsPPTOn` certificate.

<a id="reingold2008"></a>
## reingold2008

Omer Reingold.
“Undirected Connectivity in Log-Space.”
*Journal of the ACM* 55(4), Article 17 (2008).
DOI: https://doi.org/10.1145/1391289.1391291.
Author copy dated 2008-05-03 inspected: https://omereingold.wordpress.com/wp-content/uploads/2014/10/sl.pdf.

<a id="renyi61"></a>
## renyi61

Alfréd Rényi.
"On Measures of Entropy and Information."
*Proceedings of the Fourth Berkeley Symposium on Mathematical Statistics and Probability, Volume 1: Contributions to the Theory of Statistics*, 547–561, University of California Press, Berkeley, CA, 1961.
Open scan: https://static.renyi.hu/renyi_cikkek/1961_on_measures_of_entropy_and_information.pdf . Checked against that scan during outside-fleet source review on 2026-11-22: §3, eq. (3.3) on printed p. 554 defines order-`α` information for finite distributions with positive reference masses in base-`2` logarithms (`log₂`); swapping the paper's distribution letters to `(p, q)` and multiplying by `ln 2` yields the finite natural-logarithm formula, while countable support, `⊤` on off-support atoms, and the modern data-processing, composition, and hockey-stick properties in [Renyi.lean](../CslibFrontier/Probability/Renyi.lean) follow [mironov17](#mironov17).

<a id="reynolds02"></a>
## reynolds02

John C. Reynolds.
“Separation Logic: A Logic for Shared Mutable Data Structures.”
*LICS 2002*, 55–74. https://doi.org/10.1109/LICS.2002.1029817 ; author PDF https://www.cs.cmu.edu/~jcr/seplogic.pdf . The standard locality/separating-conjunction principle was consulted; the local finite-support model is an adaptation.

<a id="rfc4231"></a>
## rfc4231

Magnus Nystrom.
*Identifiers and Test Vectors for HMAC-SHA-224, HMAC-SHA-256, HMAC-SHA-384, and HMAC-SHA-512*, RFC 4231, 2005. https://doi.org/10.17487/RFC4231 . Checked on 2026-11-24 against the RFC Editor text: Section 4.2's test case 1 supplies the 20-byte `0x0b` key, `Hi There` data and full SHA-256/SHA-512 outputs; Section 4.7's test case 6 supplies the 131-byte `0xaa` key, long-key message and full outputs.
`CslibFrontierTests/Crypto/HMACMGF1.lean` checks those four values against the executable HMAC functions.
They cover short-key padding and long-key hashing, while values computed outside Lean cover exact-block keys; these are primitive regression vectors, not FIPS 205 message-call or validation vectors.

<a id="rfc8017"></a>
## rfc8017

Kathleen Moriarty, Burt Kaliski, Jakob Jonsson and Andreas Rusch.
*PKCS #1: RSA Cryptography Specifications Version 2.2*, RFC 8017, 2016. https://doi.org/10.17487/RFC8017 . Checked on 2026-11-24 against the RFC Editor text: Section 4.1 defines generic big-endian `I2OSP`, and Appendix B.2.1 defines MGF1 by encoding each consecutive counter with `I2OSP(counter, 4)`, hashing `mgfSeed || C`, concatenating the digests and taking the leading `maskLen` octets, with the inclusive `maskLen <= 2^32 hLen` bound.
`CslibFrontier.Crypto.Primitives.Hash.MGF1` instantiates this algorithm with SHA-256 and SHA-512 as total functions of the seed and the requested length, which agree with the source up to its output-length bound and reduce the counter modulo `2^32` beyond it, and proves that a shorter mask is a prefix of every longer mask from the same seed.
`CslibFrontierTests/Crypto/HMACMGF1.lean` evaluates both functions on both sides of the digest-length boundary against values computed outside Lean; the RFC has no MGF1 test vectors.
The module does not claim pseudorandomness, constant-time execution, RSA functionality or validation.

<a id="rompel90"></a>
## rompel90

John Rompel.
“One-Way Functions are Necessary and Sufficient for Secure Signatures.”
*Proceedings of the Twenty-Second Annual ACM Symposium on Theory of Computing (STOC 1990)*, 387–394, 1990. https://doi.org/10.1145/100216.100269 . Bibliographic metadata checked against the repository bibliography; the formalization establishes universal one-way hashing via the inaccessible-entropy construction of [hhrvw20](#hhrvw20) rather than Rompel's original construction, and the ACM full text was not directly inspected in this pass.

<a id="rosenthal73"></a>
## rosenthal73

Robert W. Rosenthal.
*A Class of Games Possessing Pure-Strategy Nash Equilibria*.
International Journal of Game Theory 2(1), 65–67, 1973. https://doi.org/10.1007/BF01737559 . Bibliographic metadata checked on 2026-11-07; the potential-function theorem is attributed as cited in Monderer–Shapley, Theorem 3.1.

<a id="roth82"></a>
## roth82

Alvin E. Roth.
*Incentive Compatibility in a Market with Indivisible Goods*.
Economics Letters 9(2), 127–132, 1982. https://doi.org/10.1016/0165-1765(82)90003-9 . Bibliographic metadata only; the publisher's text is paywalled and was not inspected.
It is cited as the standard primary reference for the strategy-proofness of top trading cycles; no locator in it was verified, and neither [schummervohra07](#schummervohra07) nor [roughgarden13cs364a](#roughgarden13cs364a), Lecture #9, cites it.

<a id="rothpostlewaite77"></a>
## rothpostlewaite77

Alvin E. Roth and Andrew Postlewaite.
*Weak versus Strong Domination in a Market with Indivisible Goods*.
Journal of Mathematical Economics 4(2), 131–137, 1977. https://doi.org/10.1016/0304-4068(77)90004-0 . Bibliographic metadata only; the publisher's text is paywalled and was not inspected, so no theorem number is cited.
The housing-market modules attribute to it, as the standard primary reference and without a verified locator, the uniqueness of the strict-core (weak-domination) allocation and its agreement with the competitive allocation; neither [schummervohra07](#schummervohra07) nor [roughgarden13cs364a](#roughgarden13cs364a), Lecture #9, cites it.

<a id="rothsotomayor90"></a>
## rothsotomayor90

Alvin E. Roth and Marilda A. Oliveira Sotomayor.
*Two-Sided Matching: A Study in Game-Theoretic Modeling and Analysis*.
Econometric Society Monographs, Cambridge University Press, 1990. https://doi.org/10.1017/CCOL052139015X . Bibliographic metadata checked against Crossref on 2026-11-08.
The book itself was not inspected.
Its Chapter 2 theorem numbers and statements were checked against Muriel Niederle's lecture notes *Matching: The Theory* (Stanford, 26 September 2011, https://web.stanford.edu/~niederle/MarketDesignClassIntro2.pdf), which follow the book's numbering.
They are Theorem 2.8 (a stable matching exists for every marriage market), Theorem 2.12 (with strict preferences there are M-optimal and W-optimal stable matchings), Theorem 2.13 (opposing interests, credited to Knuth) and Theorem 2.22 (with strict preferences, the set of people who are single is the same for all stable matchings).
The incomplete-list stable-matching modules cite these theorems.

<a id="roughgarden03"></a>
## roughgarden03

Tim Roughgarden.
*The Price of Anarchy is Independent of the Network Topology*.
Journal of Computer and System Sciences 67(2), 341–364, 2003. https://doi.org/10.1016/S0022-0000(03)00044-8 . The author's version of 23 December 2002 (https://theory.stanford.edu/~tim/papers/indep.pdf) was consulted on 2026-11-08 for Section 2.4, Definitions 2.5 and 3.1–3.3, Theorem 3.8, Lemma 4.1, Theorem 4.2, Proposition 5.1 and Remark 5.2; locators follow that version.
Its anarchy value is defined through marginal costs for latencies with `x c(x)` convex, and Proposition 5.1 takes the degree `p ≥ 1`.
The library uses the Pigou-ratio definition of [roughgarden13cs364a](#roughgarden13cs364a), Lecture #11, (2), which agrees with it on standard classes (Definition 3.1; up to the degenerate convention when `c(r) = 0`), needs no convexity, and includes `d = 0`.

<a id="roughgarden13cs364a"></a>
## roughgarden13cs364a

Tim Roughgarden.
*CS364A: Algorithmic Game Theory*, lecture notes, Stanford University, Fall 2013. https://theory.stanford.edu/~tim/f13/f13.html . Lecture #17, "No-Regret Dynamics" (18 November 2013), was consulted on 2026-11-07 for Definition 1.2, §3, Proposition 3.1, Remark 3.2, Corollary 3.3 and footnote 1.
Lecture #9, "Beyond Quasi-Linearity" (21 October 2013), was consulted on 2026-11-08 for §3 (the top trading cycle algorithm, Theorems 3.1 and 3.2).
Its core is defined by strict blocking, for which only the existence half of Theorem 3.2 holds; a checked three-agent market in `CslibFrontierTests/HousingMarket.lean` has a second core allocation.
Lecture #11, "Selfish Routing and the Price of Anarchy" (28 October 2013), was consulted on 2026-11-08 for Definition 3.2, the Pigou bound (2), Theorem 3.3, Table 1 and the proof in §5.
Lecture #15, "Best-Case and Strong Nash Equilibria" (11 November 2013), was consulted on 2026-11-08 for §1.2 (network cost-sharing games, displays (1) and (2)), §1.3 (VHS or Betamax, Figure 1), §1.4 (the opt-out example, Figure 2), Theorem 2.1, the remark after it that the opt-out example rules out a smaller factor, and displays (3) and (4).
Exercise Set #7, Exercise 55 (`C(f)/2 ≤ Φ(f) ≤ C(f)` for affine atomic selfish routing), was consulted on the same day.
Lecture #15 §3 (Definition 3.1, Theorem 3.2 and its proof, displays (5)–(8), and the remark that the opt-out equilibrium is strong), §4 and Figure 4, and Exercise Set #8, Exercise 67 (strong Nash equilibria for a common source and sink), were consulted on the same day for the strong Nash equilibrium modules.
Exercise 67 asks for a one-to-one correspondence between strong Nash equilibria and minimum-cost outcomes.
The library proves it for fair cost-sharing games in which all players share the strategy set and the resource map (a profile is a strong Nash equilibrium if and only if it has minimum social cost), together with its stated consequences, existence and a price of anarchy of `1`.
Lecture #19, "Pure Nash Equilibria and PLS-Completeness" (2 December 2013), was consulted on 2026-11-08 for §2.2 (abstract local search problems), the PLS-membership argument of §3 with formula (1), and Theorem 3.1.
Lecture #18, "From External Regret to Swap Regret and the Minimax Theorem" (20 November 2013), was consulted on 2026-11-10 for Definition 1.2 (swap regret, p. 2), Theorem 2.1 and its proof (the black-box reduction, pp. 3–5) and the stationarity equation (7) (p. 5).
Lecture #6, "Simple Near-Optimal Auctions" (9 October 2013, https://theory.stanford.edu/~tim/f13/l/l6.pdf, 8 pp., SHA-256 `1a6ba00d7771d624ded8000f1ca60810f64c79b093def8ad0b768bf550c6e358`), was consulted on 2026-11-24 for §2 (Theorem 2.1 and displays (2)–(5), pp. 2–4), §3 (posted-price single-item auctions for non-identical regular bidders via `φᵢ(vᵢ)⁺`, pp. 4–5), and §4 (Theorem 4.1, the Bulow–Klemperer theorem, pp. 5–6).

<a id="roughgarden15"></a>
## roughgarden15

Tim Roughgarden.
*Intrinsic Robustness of the Price of Anarchy*.
Journal of the ACM 62(5), Article 32, 2015. https://doi.org/10.1145/2806883 . The author's version of 14 July 2015 was consulted on 2026-11-07 for Definition 2.1, derivation (3)–(5), Example 2.5, (15) and Theorems 3.2–3.3; locators follow that version.

<a id="roughgarden15cc"></a>
## roughgarden15cc

Tim Roughgarden.
*Communication Complexity (for Algorithm Designers)*.
Lecture notes, arXiv:1509.06257v1, 2015; published in Foundations and Trends in Theoretical Computer Science 11(3–4), 217–404, 2016. https://arxiv.org/abs/1509.06257v1 . arXiv version 1 was consulted on 2026-11-08 for §8.3.1 (pp. 125–129): the edge tester, display (8.2), the Key Claim and Theorem 8.2, which the notes attribute to [gglrs00](#gglrs00).
The monotonicity-testing modules follow this proof, and their locators follow version 1.
Theorem 8.2 takes `t = Θ(n / ε)` trials.
The library proves the upper bound with explicit constants and claims nothing about fewer trials.

<a id="roughgardentardos02"></a>
## roughgardentardos02

Tim Roughgarden and Éva Tardos.
*How Bad Is Selfish Routing?*
Journal of the ACM 49(2), 236–259, 2002. https://doi.org/10.1145/506147.506153 . The author's version of 5 December 2001 was consulted on 2026-11-07 for Section 2.1, Definition 2.1, Lemma 2.2, Theorem 4.5 and Figure 3; locators follow that version.

<a id="roughgardentardos07"></a>
## roughgardentardos07

Tim Roughgarden and Éva Tardos.
"Introduction to the Inefficiency of Equilibria."
Chapter 17 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 443–459.
A university-hosted PDF of the book was consulted on 2026-11-08 for §17.1.3 (the definitions of the price of anarchy and the price of stability) and Example 17.3 with Figure 17.3 (the `H_k` lower bound for Shapley network design games).

<a id="rubinsteinwangweinberg20"></a>
## rubinsteinwangweinberg20

Aviad Rubinstein, Jack Z. Wang and S. Matthew Weinberg.
"Optimal Single-Choice Prophet Inequalities from Samples."
*11th Innovations in Theoretical Computer Science Conference (ITCS 2020)*, LIPIcs 151, 60:1–60:10, 2020. https://doi.org/10.4230/LIPIcs.ITCS.2020.60 ; cited from https://arxiv.org/pdf/1911.07945v2 (11 pp., SHA-256 `abd52c22bd65f4748fbc1f45430a689008892b1cb172eab1ee59ceeef7c5baaf`), inspected on 2026-11-24 for §1 (Definition 1 and Theorem 1, p. 1), §2 ("Continuous vs. Discrete Distributions" uniform tie-breaking reduction, p. 2), and §3 (Observation 3, Propositions 4 and 5, and Proof of Theorem 1, pp. 3–4).

<a id="saglam27"></a>
## saglam27

Mert Saglam.
*Linear Codes Exceeding the Gilbert–Varshamov Bound*.
STOC 2027 submission 1516. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1516.pdf (PDF SHA-256 `ac6f2bba913aa15cfec8dda07a8e9e37b7186e145fef4719cb623dd04d15baa3`).
The submission PDF was read on 2026-11-12: the abstract (main theorem), Section 1, Section 2 (odd circuits, the extension row and the bound on the expected number of odd circuits), Section 3.1, Lemma 3.1 (statement only), Section 3.3 (the three-range estimate on `sinh z - z` and the moment/tail split) and Appendix A. [Code/OddCircuit](../CslibFrontier/Foundations/Data/Code/OddCircuit.lean) and [Code/OddCircuitFourier](../CslibFrontier/Foundations/Data/Code/OddCircuitFourier.lean) formalize Section 2 and the reduction of Section 3.3 to the moment and tail estimates.
[Code/PuncturedBallFourier](../CslibFrontier/Foundations/Data/Code/PuncturedBallFourier.lean) derives Lemma 3.1, with explicit constants, from the Kirshner–Samorodnitsky bounds quoted in Appendix A ([kirshnersamorodnitsky21](#kirshnersamorodnitsky21)), which are hypotheses.
[Code/OddCircuitAsymptotic](../CslibFrontier/Foundations/Data/Code/OddCircuitAsymptotic.lean) proves the main theorem from Lemma 3.1 with `ζ = 1 / 2`, so the leading constant `(1 - ζ) / 4` with `ζ → 0` is not formalized.
These are submissions, not confirmed acceptances.

<a id="sakszaharoglou2000"></a>
## sakszaharoglou2000

Michael Saks and Fotios Zaharoglou.
"Wait-Free k-Set Agreement Is Impossible: The Topology of Public Knowledge."
*SIAM Journal on Computing* 29(5), 1449–1483, 2000. https://doi.org/10.1137/S0097539796307698 (preliminary version in *STOC 1993*, pp. 101–110).
Bibliographic metadata verified via DOI/DBLP and cross-checked in [herlihyshavit1999](#herlihyshavit1999) on 2026-11-22 UTC; the paywalled journal and conference texts were not directly inspected, so no internal section, theorem or page locator is asserted.
Cited by [SetAgreement/Impossibility.lean](../CslibFrontier/Computability/Distributed/SetAgreement/Impossibility.lean).

<a id="sakszhou99"></a>
## sakszhou99

Michael Saks and Shiyu Zhou.
*BP_H SPACE(S) ⊆ DSPACE(S^{3/2})*.
Journal of Computer and System Sciences 58(2), 376–403, 1999. https://doi.org/10.1006/jcss.1998.1616 . The publisher copy is paywalled and was not consulted, so its internal numbering (including the Lemma 5.4 cited by Chattopadhyay–Liao) is unverified.
The iteration is formalized from the presentation of Chattopadhyay and Liao (2020), Appendix A.1.

<a id="saptharishi26survey"></a>
## saptharishi26survey

Ramprasad Saptharishi.
*A survey of lower bounds in arithmetic circuit complexity*.
Living GitHub repository, pinned at revision `af95c539791b6ec0c3f86a135a98a3e0aca34613` (bibliography key `Saptharishi2026Survey`). https://github.com/dasarpmar/lowerbounds-survey/tree/af95c539791b6ec0c3f86a135a98a3e0aca34613 . Checked against the TeX source at revision `af95c539` on 2026-11-08 and 2026-11-22: `chap_dc.tex` (Chapter "Determinantal Complexity Lower Bounds" `chap:dc`, defining determinantal complexity `dc(f)` as the least `m` for which `f` is the determinant of an `m × m` affine-linear matrix, recalling determinant projection universality via Theorem `thm:vp`, and presenting Theorem `thm:Mignon-Ressayre-mainthm` and Lemmas `lem:MR-det-ub` and `lem:MR-perm-lb` for [Mignon–Ressayre](#mignonressayre04)) and `chap_vpvnp.tex` (Chapter "Algebraic complexity classes" `chap-vpvnp`: Theorem `thm:vp`, Section `sec:formula-to-dets` "Warm-up: Formulas to permanents", Subsection "ABPs reduce to Det_n", and the accompanying exercise adapting formula simulation to determinants).
[Determinant/Projection.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Determinant/Projection.lean), [Determinant/Formula.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Determinant/Formula.lean) and [DeterminantalComplexity.lean](../CslibFrontier/Computability/Circuit/Arithmetic/DeterminantalComplexity.lean) formalize specialization branching-program closure (`IsSubstABP`), the `(F.size + 1) × (F.size + 1)` determinant projection bound for arithmetic formulas, and finite determinantal complexity (`determinantalComplexity_lt_top`) over arbitrary commutative rings and variable index types through `Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul` rather than equal-length cycle-cover padding.

<a id="satterthwaite75"></a>
## satterthwaite75

Mark A. Satterthwaite.
"Strategy-Proofness and Arrow's Conditions: Existence and Correspondence Theorems for Voting Procedures and Social Welfare Functions."
*Journal of Economic Theory* 10(2), 187–217, 1975. https://doi.org/10.1016/0022-0531(75)90050-2 . Bibliographic data from secondary search summaries on 2026-11-08 UTC; the paper was not inspected.
Cited, with [Gibbard](#gibbard73), for the Gibbard–Satterthwaite theorem; no theorem number is claimed.

<a id="savage71"></a>
## savage71

Leonard J. Savage.
"Elicitation of Personal Probabilities and Expectations."
*Journal of the American Statistical Association* 66(336), 783–801, 1971 (bibliography key `Savage1971`). https://doi.org/10.1080/01621459.1971.10482346 . Bibliographic metadata checked via DOI and catalogue records; the 1971 journal PDF was not directly inspected, so internal theorem, section and page locators are marked `unverified` in the results registry.
Cited at paper level in [ScoringRules.lean](../CslibFrontier/GameTheory/PredictionMarket/ScoringRules.lean) for the convex-potential / subgradient characterization of proper and strictly proper scoring rules (`savageScoringRule`, `isProperOn_iff_exists_savage`, `isStrictlyProperOn_iff_exists_savage`).

<a id="scarf67"></a>
## scarf67

Herbert E. Scarf.
"The Core of an $N$ Person Game."
*Econometrica* 35(1), 50–69, 1967. https://doi.org/10.2307/1909383 . Bibliographic metadata checked via search summaries; the full text was not inspected, so internal section or theorem locators are not claimed.
Cited by [Scarf.lean](../CslibFrontier/GameTheory/Cooperative/Scarf.lean) for NTU cooperative games and Scarf's theorem.

<a id="schoenebeck08"></a>
## schoenebeck08

Grant Schoenebeck.
*Linear Level Lasserre Lower Bounds for Certain k-CSPs*. 49th Annual IEEE Symposium on Foundations of Computer Science (FOCS 2008), 593–602. https://doi.org/10.1109/FOCS.2008.74 . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC.
On the same date worker w96-sos consulted the author-hosted copy https://schoeneb.people.si.umich.edu/papers/LasserreNew.pdf (19 pages, TeX output dated 6 December 2008) for Definition 5 (rounds of Lasserre), Definition 10 (width-`w` resolution on XOR formulas), Lemma 13 (the main lemma, p. 8) and Claim 14.
In that copy Lemma 13 grants a feasible solution at the `w/2`-th round of Lasserre.
An independent review reported `w/4` from a different version, so the constant is version-dependent.
The library proves the sum-of-squares form of the lemma and does not construct Lasserre vectors.
The typeset FOCS version was not consulted.

<a id="schoening99"></a>
## schoening99

Uwe Schöning.
*A Probabilistic Algorithm for k-SAT and Constraint Satisfaction Problems*. 40th Annual Symposium on Foundations of Computer Science (FOCS 1999), 410–414. https://doi.org/10.1109/SFFCS.1999.814612 . Bibliographic metadata taken from `references.bib` (`Schoening1999`); the paywalled conference proceedings were not directly inspected, and no internal theorem or page locators are claimed.
Cited at paper level for the `3n`-step randomized local-search trial on width-`k` CNFs and its `(2 (k - 1) / k) ^ n` amplified decision algorithm (`(4 / 3) ^ n` for `3`-SAT).

<a id="schrijver03"></a>
## schrijver03

Alexander Schrijver.
*Combinatorial Optimization: Polyhedra and Efficiency*.
Algorithms and Combinatorics 24, Springer, 2003.
Cited for Gomory–Hu trees.
The locator (Chapter 15, “Connectivity and Gomory–Hu trees”, Section 15.4) is taken from secondary descriptions of the table of contents only: the book itself was not inspected, and no theorem or page locator is claimed.
It is also cited for Dinitz's algorithm: the locator Section 10.6 (on Dinitz's `O(n²m)` maximum-flow algorithm) was likewise taken from secondary descriptions of the table of contents.
It is also cited for minimum-cost arborescences: the locator Section 52.1 (“Finding a shortest r-arborescence”) was likewise taken from secondary descriptions of the table of contents.
A [hosted copy of Part I](https://www.lamsade.dauphine.fr/~cornaz/Enseignement/M2_MODO/DATA/A1.PDF) (Volume A, “Paths and Flows”, with the book's pagination) was inspected on 2026-11-11 for the real-capacity flow and Gomory–Hu results: Section 10.1 (pp. 148–149) defines flows with capacities `c : A → ℝ₊`, conservation and the value; Theorem 10.3 (Section 10.2, p. 150) is the max-flow min-cut theorem; in Section 15.4, Theorem 15.13 (p. 249) is the path-minimum property of a Gomory–Hu tree and Theorem 15.14 (p. 250) its existence.
`isMaxRealFlow_minRealCutBetween` extends Theorem 10.3 from `ℝ` to any linearly ordered field, encodes arcs as ordered pairs and obtains the maximum by linear-programming duality.

<a id="schrijver17"></a>
## schrijver17

Alexander Schrijver.
*A Course in Combinatorial Optimization*.
Lecture notes, version of March 23, 2017. https://homepages.cwi.nl/~lex/files/dict.pdf . The author-hosted PDF was consulted on 2026-11-08 UTC for Section 10.4 (Lemma 10.2), Section 10.5 (Example 10.5a, displays (23)–(25) and (27), Theorems 10.6, 10.7 and 10.9) and Exercise 10.22; the matroid intersection modules cite these locators.
It was also consulted on 2026-11-08 UTC for Section 3.2 (display (6) and Theorem 3.2), Section 5.1 (Theorem 5.1 and Corollary 5.1a) and Theorem 5.2; the general-matching modules `Berge` and `TutteBerge` cite these locators.
Section 4.1 (Theorem 4.1, Corollaries 4.1a and 4.1b including directed multigraphs, the vertex-splitting and undirected remarks after them, and Theorem 4.2's remark on integer-capacity path packing) was consulted on 2026-11-08 and 2026-11-11 UTC for the Menger modules.
Section 7.3 (display (17), Theorems 7.5 and 7.6) was consulted on 2026-11-08 for the Mirsky and Dilworth modules.
The corresponding chapter of Schrijver's 2003 monograph (Chapter 41) is cited in the library from secondary descriptions only; its theorem and page locators are unverified.

<a id="schrijver78"></a>
## schrijver78

Alexander Schrijver.
"A Short Proof of Minc's Conjecture."
*Journal of Combinatorial Theory, Series A* 25(1), 80–83, 1978. https://doi.org/10.1016/0097-3165(78)90036-5 . Bibliographic data from the DOI record; the paper was not inspected.
The induction in the library's Brégman module follows the published descriptions of this proof (induction on `n`, a convexity inequality at one row, then averaging over the rows).

<a id="schrijver86"></a>
## schrijver86

Alexander Schrijver.
*Theory of Linear and Integer Programming*.
Wiley-Interscience Series in Discrete Mathematics, John Wiley & Sons, Chichester, 1986.
An independent agent review checked the primary book on 2026-11-11 UTC for Section 3.2, Theorem 3.2 (pp. 29–30, determinant encoding-size bound) and Section 3.3, "The Gaussian elimination method": Theorem 3.3 (pp. 32–33, polynomial-time rational Gaussian elimination), Corollary 3.3a (pp. 33–34, polynomial-time determinant, rank, inverse, linear-independence testing, and linear system solving), and the Gauss–Jordan discussion with Equations (28)–(30) (p. 35).
Local adaptations in [`BareissElimination.lean`](../CslibFrontier/Algorithms/LinearAlgebra/BareissElimination.lean) and [`RationalElimination.lean`](../CslibFrontier/Computability/PolyTime/LinearAlgebra/RationalElimination.lean): (1) rather than Schrijver's normalized rational elimination, row denominators are cleared upfront and fraction-free Sylvester–Bareiss minor-scaled Gauss–Jordan updates are executed over `ℤ` with an explicit Hadamard/factorial bound (`stageEntryBound`); and (2) native multi-tape Turing `ComputableInPolyTime` time and workspace bounds are certified using `enc_structure` codecs with explicit unary dimension headers (`numRows`, `numCols`, `rank`, `pivotRows`, `pivotCols`, `nonPivotCols`) and framed signed-binary/rational entries.

<a id="schummervohra02"></a>
## schummervohra02

James Schummer and Rakesh V. Vohra.
"Strategy-proof Location on a Network."
*Journal of Economic Theory* 104(2), 405–428, 2002. https://doi.org/10.1006/jeth.2001.2807 . The published version is paywalled and was not inspected.
The [authors' January 23, 2001 preprint](https://www.kellogg.northwestern.edu/faculty/schummer/ftp/research/circle.pdf) was read on 2026-11-11, and the locators below refer to its pages.
Section 2 (pp. 5–6) sets up finite connected length graphs and preferences given by negative path distance.
Section 3 (pp. 9–16) defines generalized median voter schemes on paths, their consistency (p. 12) and extended median voter schemes, and Theorem 1 (p. 15) characterizes strategy-proof onto rules on trees.
Section 4 proves Theorem 2 (p. 21): every strategy-proof onto rule has a dictator on each cycle.
`TreeEMVS` represents extended median voter schemes by branch-winning coalitions rather than by consistent path schemes; see its docstring for the correspondence.
Strong group strategyproofness of these rules is proved in the library and is not stated in the paper.
The cycle results cover shortest cycles only.

<a id="schummervohra07"></a>
## schummervohra07

James Schummer and Rakesh V. Vohra.
"Mechanism Design without Money."
Chapter 10 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 243–265.
A university-hosted PDF of the book was consulted on 2026-11-08 for §10.3 (the definition of blocking coalitions and the core, Definition 10.5, Theorems 10.6 and 10.7, pp. 253–255).
Its core uses weak blocking, the strict core of the housing-market modules.
Its claim on p. 255 that the core and the strict core coincide under strict preferences is refuted by a checked three-agent market in `CslibFrontierTests/HousingMarket.lean`.
The same university-hosted PDF was consulted on 2026-11-24 for §10.2 (single-peaked preferences over `[0, 1]`, Lemma 10.1, pp. 245–246; Theorem 10.2 and Eq. (10.1), footnote 6, pp. 247–250; Definition 10.3 and Theorem 10.4, pp. 250–251; §10.2.2 minimum-peak individual-rationality uniqueness, p. 252) and Exercises 10.1–10.4 (pp. 264–265), formalized in [SinglePeaked/Basic.lean](../CslibFrontier/GameTheory/SocialChoice/SinglePeaked/Basic.lean), [SinglePeaked/Ching.lean](../CslibFrontier/GameTheory/SocialChoice/SinglePeaked/Ching.lean), and [FacilityLocation/PhantomMedian.lean](../CslibFrontier/GameTheory/Mechanism/FacilityLocation/PhantomMedian.lean) (generalizing `[0, 1]` to arbitrary closed intervals `Set.Icc a b` with `a ≤ b`, and adding strong group strategy-proofness and the symmetric right-endpoint individual-rationality counterpart); [FacilityLocation/ThreeLeafTree.lean](../CslibFrontier/GameTheory/Mechanism/FacilityLocation/ThreeLeafTree.lean) formalizes the symmetric path-distance facility-location specialization after Exercise 10.5 (p. 265) and [schummervohra02](#schummervohra02) Theorem 1, while the ordinal tree-single-peaked preference domain of Exercise 10.5 remains open ([#7789](https://github.com/cslib-community/cslib-frontier/issues/7789)).

<a id="selaherlihypetrank2021"></a>
## selaherlihypetrank2021

Gal Sela, Maurice Herlihy, and Erez Petrank.
"Brief Announcement: Linearizability: A Typo."
*Proceedings of the 2021 ACM Symposium on Principles of Distributed Computing (PODC)*, 2021 (bibliography key `SelaHerlihyPetrank2021`). https://doi.org/10.1145/3465084.3467944 ; full version "Linearizability: A Typo", https://arxiv.org/abs/2105.06737v2 . Inspected the arXiv v2 PDF https://arxiv.org/pdf/2105.06737v2 (13 pages, numbered pp. 1-13, dated 29 July 2021; SHA-256 `1a8b2fadcf89f16b89d0b544864ad10082d1330a56a08d816f5bd37e26b83893`) on 2026-11-22 UTC: Sections 2.1-2.2 (p. 3, Definitions 2.1-2.2 recalling the original printed linearizability definition of [herlihywing1990](#herlihywing1990), where `<_H` applies only to operations completed in `H`); Sections 3.1-3.3 (pp. 4-6, Figures 1-3 showing that original printed L2 allows pending invocations to linearize before earlier completed operations and fails both locality and the nonblocking property); Section 4 (p. 6, Definition 4.1 "Amended Linearizability", strengthening L2 to `<_{complete(H')} <= <_S`, equivalently `<_{H'} <= <_S` on operations completed in `H'`); Section 5.2 (pp. 7-9, Theorem 5.1 proving locality for Definition 4.1); Section 5.3 (p. 9, Theorem 5.2 proving the nonblocking property for pending invocations of total operations under Definition 4.1); and Section 6 (pp. 9-10, Definition 6.1 and Figure 5 showing why extending `<_H` to unlinearized pending invocations would be too strong).
Cited by [ConcurrentObjects/Linearizability.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/Linearizability.lean): `History.prec H e_0 e_1` sees invocations pending in `H`, and `IsLinearizable` enforces it on all operations completed in the extension `H'` (`History.IsCompletedOp H'`), which is equivalent to `<_{H'} <= <_S` by `History.prec_append_resp_iff` and matches Definition 4.1, with `isLinearizable_iff_forall_obj` and `exists_linearizable_append_resp_of_total` corresponding to Theorems 5.1 and 5.2.

<a id="sergeev2013additivemultiplicative"></a>
## sergeev2013additivemultiplicative

Igor S. Sergeev.
"A relation between additive and multiplicative complexity of Boolean functions."
Preprint `arXiv:1303.4177v1` (18 March 2013), 4 pp.; author-hosted English PDF `https://igorssergeev.github.io/papers/1303.4177e.pdf` (SHA-256 `58b0aa108d9da736f77d706ecfd9657abecdee341fb7fe97e9ab3cbf6f8357b3`), inspected in full (pp. 1–4) on 2026-11-22 UTC under strict clean-room conditions solely from the PDF.
Formalized in [`Zhegalkin.lean`](../CslibFrontier/Computability/Circuit/Boolean/Zhegalkin.lean):

- **Lemma 1 (pp. 2–3, active-square additive matrix synthesis):** `Matrix.activeSquare` (`S(A)`) counts entries `(i, j)` within horizontal distance `Nat.log 2 m` of a `true` entry in row `i` (equivalent to `≤ Real.logb 2 m` for integer column distances when `1 ≤ m`).
  `Additive.exists_circuit_matrix_le_bound` proves the explicit `(s, p)` bound `(n * 2 ^ s) / s + A.activeSquare / (2 * s) + m * p + (m ⌈/⌉ p) * 2 ^ s * (n ⌈/⌉ s)` over any `AddCommMonoid` for `0 < s ≤ Nat.log 2 m + 1` and `0 < p` (applying horizontal section column-pairing to the `⌊n / s⌋` full width-`s` blocks while routing the single partial remainder block directly from the precomputed block subset sums; `[AddCommMonoid G]` over `{0, +}` supplies `0` for all-zero rows on total output wires, whereas p. 2 footnote 4 states a commutative semigroup `(G, +)` and `exists_circuit_matrix_le_bound` emits zero `Op.zero` gates whenever every row of `A` has a `true` entry), and `Additive.exists_circuit_matrix_le` deduces `A.activeSquare / (2 * Real.logb 2 m) + ε * ((m + n) ^ 2 / Real.logb 2 m)` for `2 ≤ m` and sufficiently large `m + n`.
- **Theorem 1 (upper bound, pp. 1, 3, multiplicative-to-total complexity over `{⊕, ∧, 1}`):** `Zhegalkin.exists_circuit_of_andCost_le_bound` topologically decomposes any `{⊕, ∧, 1}`-circuit with `k ≤ M` conjunction gates into `2 M` affine forms and synthesizes an acyclic staged `{⊕, ∧, 1}`-circuit using at most `k` conjunction gates and `Zhegalkin.totalBound n M s p` total gates (synthesizing width-`s` conjunction-block subset sums stage-by-stage and routing the `< s` intra-stage conjunction dependencies directly so every shared paired column sum precedes both participating rows).
  Bounding `Zhegalkin.totalBound n M s p` directly, `Zhegalkin.exists_circuit_of_andCost_le` and `Zhegalkin.complexity_le_of_multiplicativeComplexity_le` prove the `(1 / 2 + ε) * M * (M + 2 * n) / Real.logb 2 M` upper bound with a uniform threshold in `M` for all `n : ℕ`, recovering Sergeev's published upper bound when `M = Ω(n)`.
- **Citation boundary:** Theorem 1 on p. 1 also asserts asymptotic optimality via a counting argument on p. 2 citing Nechiporuk (1962) and Lupanov (1958); only the constructive upper bounds of Lemma 1 and Theorem 1 are formalized and registered here.

<a id="sergeev2014orcomplement"></a>
## sergeev2014orcomplement

Igor S. Sergeev.
"On Relative OR-Complexity of Boolean Matrices and Their Complements." arXiv:1407.4626v1 [cs.CC], July 17, 2014. https://arxiv.org/abs/1407.4626v1 ; PDF https://arxiv.org/pdf/1407.4626v1 (mirror https://igorssergeev.github.io/papers/1407.4626v1.pdf ).
Inspected the 3-page arXiv v1 PDF (SHA-256 `7e489989a639a6959543c812843d8b3a1c53c39e66ee8fa20d57063d931b44a6`, pp. 1–3) on 2026-11-22 UTC: rectifier `(m, n)`-circuit model, `OR(A)`, `OR_d(A)`, `k`-rectangle-freeness, Nechiporuk's `2`-free consequence `OR(Ā) = OR_2(Ā) = |Ā|`, and Theorem 1(i) on p. 1; Theorem 1(ii), Lemma 1 (`|A| ≥ 2 n^{3/2} → Ω((|A|/n)^4)` `2`-rectangles), the `n = C(m, 2)` `2`-rectangle lift `B` (noting the p. 2 line-above-Lemma-2 misprint "in `B`" for "in `A`"), Lemma 2 (`k`-free `A` implies `(C(k - 1, 2) + 1)`-free `B`), and Lemma 3 statement on p. 2; and the proof of Lemma 3 (depth-`3` circuit for `B̄` and quoted Nechiporuk bound `OR(B) ≥ |B| / K^2`, noting that Lemma 3 writes `Ω((|A| / (k n))^4)` by reusing Lemma 1's dimension letter `n` after setting `n = C(m, 2)` for an `m × m` matrix `A`, whereas Lemma 1 on `A` gives `|B| = Ω((|A| / m)^4)` and `OR(B) = Ω((|A| / (k m))^4)`, which is the bound yielding both Theorem 1(i) and Theorem 1(ii)) and the Theorem 1(ii) instantiation via Brown's `3`-free `m × m` matrix (`m = p^3`, `p ≡ 3 (mod 4)` prime, `n = C(p^3, 2)`) on p. 3.
Formalized in [RectangleFreeMatrix.lean](../CslibFrontier/Foundations/Combinatorics/RectangleFreeMatrix.lean) (Lemmas 1–2), [BrownMatrix.lean](../CslibFrontier/Foundations/Combinatorics/BrownMatrix.lean) (Brown's `3`-free unit-sphere matrix of exact weight `p^4(p - 1)`, checked directly against [brown1966](#brown1966), §2, pp. 282–283), [Rectifier/Basic.lean](../CslibFrontier/Computability/Circuit/Rectifier/Basic.lean) (`RectifierCircuit`, `orComplexity`, `orDepthComplexity`, and the sharp `(K - 1)^2` Nechiporuk bound `|A| ≤ (K - 1)^2 · OR(A)` checked against [juknasergeev2013](#juknasergeev2013), §3.3, Theorem 3.9, pp. 32–33), and [Rectifier/ComplementSeparation.lean](../CslibFrontier/Computability/Circuit/Rectifier/ComplementSeparation.lean) (Lemma 3 and Theorem 1(ii)).
Theorem 1(i)'s projective norm-graph instantiation ([kollarronyaiszabo1996](#kollarronyaiszabo1996)) remains open under [#7622](https://github.com/cslib-community/cslib-frontier/issues/7622).

<a id="sergeev2020monotoneshift"></a>
## sergeev2020monotoneshift

Igor S. Sergeev.
*On the Monotone Complexity of the Shift Operator*. arXiv:1905.10747v2 [cs.CC], 30 June 2020 (7 pages; bibliography key `Sergeev2020MonotoneShift`). https://arxiv.org/abs/1905.10747 ; author-hosted English PDF `1905.10747v2e.pdf` inspected on 2026-11-22 UTC (pp. 1–7, SHA-256 `958164165be62070e6905ac3beadc5151ab96e3ff85d1444f54d9f897b31c973`): "Preliminaries" (pp. 2–3: monotone cyclic shift operator $S_{q, A}(X, Y) = X \gg k$ for `Y = α_k` over an `n`-element antichain `A ⊂ B^m`, dual-rail binary antichain `A_0` of width `2(⌊log₂ n⌋ + 1)`, weight-`1` one-hot antichain `A_1 ⊂ B^n`, and monotone permutation operator `P_{q, Π}(X, Y) = π(X)` over an `n!`-element antichain `Π`), "Upper complexity bounds" (pp. 3–4: Theorem 1 proving `L(S_{q, A}) ≤ L(A) + O(q n log n)` via `⌈log₂ n⌉` layers of monotone multiplexers `Y^{i,1} a ∨ Y^{i,0} b` and `O(n log n)` corollaries on `A_0` and `A_1`; Theorem 2 on `P_{q, Π}` sorting-network upper bounds via AKS [2] is not formalized here), and "Lower complexity bounds" (pp. 4–6: Theorem 3 proving `L(S_{q, A}) ≥ q n log₂ n - O(q n)` for every `n`-element antichain `A`, adapting [Chashkin](#chashkin2006) and [Lamagna and Savage](#lamagnasavage1974), and the unnumbered Corollary on p. 6 deducing `L(P_{q, Π}) ≥ q n log₂ n - O(q n)` for every `Π`).
Formalized in [Shift.lean](../CslibFrontier/Computability/Circuit/Monotone/Shift.lean) over `Cslib.Circuits.Monotone.signature` weighted by `Monotone.binaryCost`, with explicit constants `4 * q * n * Nat.clog 2 n` in Theorem 1, `3 * q * n * Nat.clog 2 n` on `dualRailShiftCode n b` (`Nat.clog 2 n ≤ b`), and `q * ∑_{t=1}^n Nat.clog 2 t ≥ q * n * Nat.log 2 n - q * n` in Theorem 3 and its permutation corollary.

<a id="sergeev2023bksequence"></a>
## sergeev2023bksequence

Igor S. Sergeev.
*An Explicit Finite $B_k$-Sequence*. arXiv:2304.03988v1, 8 April 2023. https://arxiv.org/abs/2304.03988 ; PDF https://arxiv.org/pdf/2304.03988v1 . Inspected arXiv:2304.03988v1 (4 PDF pages, printed pp. 1–4, SHA-256 `d2cfa6dd1ba989da2178b1cf3a73bcba0b047ed97d54f1807b2e591aed570e35`) on 2026-11-22 UTC: the Abstract and Introduction on p. 1 (definition of `B_k`-sequences via multiset equality of `k`-fold sums, the `C(n + k - 1, k) ≤ N` counting lower bound in `ℤ_N`, and footnote 1 specifying binary output representation), the `H[n, k]` construction and `B_k` correctness/density proof on p. 2 (`r = 1 + ⌈k log₂ p_n⌉`, unique `(-1)^j · 5^h (mod 2^r)` representation of odd residues for `r ≥ 3`, `H[n, k] = {h_i | p_i ≡ ±5^{h_i} (mod 2^r), 0 ≤ h_i < 2^{r-2}}` forming a size-`n` `B_k`-sequence in `ℤ_{2^{r-2}}` with `2^{r-2} < p_n^k`), and the `(n + k)^{O(1)}` explicitness argument using `O(r^2)` arithmetic operations for the bit-by-bit base-`5` discrete logarithm in `⟨5^{2^{r-3}}⟩ = {1, 2^{r-1} + 1}` on pp. 2–3.
Formalized in [Combinatorics/Additive/BkSequence.lean](../CslibFrontier/Foundations/Combinatorics/Additive/BkSequence.lean) (`IsBkSet`, `IsBkSequence`, `IsBkSet.choose_le_card`, `dlogFiveModTwoPow`, `sergeevBkSequence`, `length_sergeevBkSequence`, `isBkSequence_map_zmod_sergeevBkSequence`, `isBkSequence_sergeevBkSequence`, `mem_sergeevBkSequence_lt`, bounding `p_n ≤ (n + 2)(2⌊log₂(n + 2)⌋ + 4)` via elementary Chebyshev counting rather than Rosser–Schoenfeld's `2n log(n + 2)`) and [Complexity/BkSequencePolyTime.lean](../CslibFrontier/Computability/Complexity/BkSequencePolyTime.lean) (`computableInPolyTime_dlogFiveModTwoPow` and `computableInPolyTime_sergeevBkSequence`, certifying polynomial bit time on a multi-tape Turing machine from unary `(n, k)` to binary sequence entries via trial division and sequential bit extraction, whereas the paper's `O(r^2)` figure counts arithmetic operations for the discrete logarithm, left open as a separate arithmetic-operation bound in [#7625](https://github.com/cslib-community/cslib-frontier/issues/7625)).

<a id="sergeev2025prefixdepth"></a>
## sergeev2025prefixdepth

Igor S. Sergeev.
*A Note on the Depth of Optimal Fanout-Bounded Prefix Circuits*. arXiv preprint `arXiv:2512.23657v1` (`cs.DS`), 29 December 2025. https://arxiv.org/abs/2512.23657 ; PDF https://arxiv.org/pdf/2512.23657v1 . Checked on 2026-11-22 UTC against the versioned arXiv PDF `https://arxiv.org/pdf/2512.23657v1` (10 PDF pages: 5-page English version on PDF pp. 1–5 followed by the 5-page Russian version on PDF pp. 6–10, SHA-256 `c9734f8d643f2a0c16ccefe1108ef07d0d7fa4f7ae1ef5c99aba0fd6461a1422`; also matching the standalone 5-page English-only PDF `2512.23657v1eng.pdf` from the author's homepage, printed pp. 1–5, SHA-256 `3166460d578d23047e40cc650106ddb7b606ae42d436412df4a2591a7670f1a4`): Introduction (English pp. 1–2, Equation (1) universal semigroup prefix products over `{x ◦ y, x}`, binary gate complexity `C`, depth `D` counting both gate types, the framework-tree/output-set decomposition yielding `C + D ≥ 2N - 2` and zero-deficiency optimality `C + D = 2N - 2`, characteristic polynomial `P_k(x) = 2 + x + x^2 + ⋯ + x^{k-2} - x^k` with unique positive root `α_k` increasing toward `φ = (1 + √5)/2`, and the main Theorem `D(N, k) = log_{α_k} N ± O(1)` on p. 2) and Proof of the theorem (English pp. 2–5, principal-chain segment decomposition into consistent tree pairs `(I_d, Q_d)`, `w_k*(D) = ∑_{d=0}^D w_k(d, D - d)`, Equation (3) and the remark immediately following it on p. 3 giving `w_2(D) = w_2*(D - 1)`, Claim (4) and Equations (5)–(7) on pp. 3–4, the order-`k` recurrence `w_k*(D) = ∑_{i=2}^{k-1} w_k*(D - i) + 2 w_k*(D - k) + k` on p. 4, and root dominance `|x| ≤ α_k` on p. 5).
Historical attributions mentioned in passing in our docstrings — Fich (1983) and Snir (1986) for `C + D ≥ 2N - 2` and `D(N, 2) = ⌊log₂ N⌋ + ⌊log₂(2N/3)⌋`, and Sheeran–Parberry (2006) and Lin–Hung (2009) for prior fanout-bounded constructions — are secondary citations via `[Sergeev2025PrefixDepth]` pp. 1–2 and were not inspected directly.
Formalized in [`Prefix/Basic.lean`](../CslibFrontier/Computability/Circuit/Prefix/Basic.lean), [`Prefix/ConsistentTree.lean`](../CslibFrontier/Computability/Circuit/Prefix/ConsistentTree.lean), and [`Prefix/OptimalDepth.lean`](../CslibFrontier/Computability/Circuit/Prefix/OptimalDepth.lean): inputs and outputs are `0`-indexed (`Fin N`), external output poles are counted alongside internal gate input slots in `wireFanout` (matching the pp. 1–2 framework-tree/output decomposition and the p. 3 discussion after Equation (3) of principal-chain fanout budgets), and because the principal chain starts at input `x_0` (`width = 1`) and traverses `D` segments `d = 0, …, D - 1`, total circuit width is `N = 1 + ∑_{d=0}^{D-1} w_d` (`N ≤ w_k*(D)` at `k = 2` via `w_k(D, 0) = 1`, constructive existence holds for `1 ≤ N ≤ 1 + w_k*(D - 1)`, and general `k ≥ 3` exponential upper bounds use the original auxiliary bound `P_k(3/2) > 0` in `three_halves_lt_alphaRoot`).

<a id="sergeev2025symmetric"></a>
## sergeev2025symmetric

Igor S. Sergeev.
*Economical formulae for symmetric boolean functions*.
English preprint dated 1 May 2025, https://igorssergeev.github.io/papers/symm2025eng.pdf . Source SHA-256: `5467458454fdaa803462a95da789d3a042b5c3c08bef65070eb8c30709f0d899`.
The inspected locators are §2, the partial-comparison definitions on printed p. 9 and the majority reconstruction identity (2) in the proof of Claim 2 on p. 10; and §3, rule (4) on p. 12 and the three overlap-correction cases in the proof of Lemma 1 on p. 13.
The finite reconstruction identities are distinct from the surrounding asymptotic formula-depth claims.
The continued formalization of those claims is tracked in [#7708](https://github.com/cslib-community/cslib-frontier/issues/7708).

<a id="sergeev2026uniquedisjointness"></a>
## sergeev2026uniquedisjointness

Igor S. Sergeev.
*Upper Bounds for the Monotone Rank of the Unique Disjointness Matrix*. arXiv:2607.27014v1 [cs.CC], 29 July 2026 (7 pp., SHA-256 `04f383aa5bc1a63eaadede288122adad745b88ae7aea0fbcd6e628218b718e65`). https://arxiv.org/abs/2607.27014 . Checked against the arXiv v1 PDF on 2026-11-22 UTC: §1 (pp. 1–3, defining the partially defined `2^n × 2^n` unique disjointness matrix `U_n[a, b] = 1` for `a ∩ b = ∅`, `0` for `|a ∩ b| = 1`, `*` for `|a ∩ b| > 1`, its OR-rank / covering rank `rk_∨`, nonnegative real rank `rk_{ℝ_+}`, and SUM-rank / partition rank `rk_+` over `(ℕ_{≥ 0}, +, ·)`), §2 (pp. 3–4, Lemma 1 on p. 3 partitioning `{0, 1}^n` into `2 n` distance-`3` codes via coordinate-flipped cosets of the binary Hamming code of length `N = 2^m - 1`, and Theorem 1 on pp. 3–4 proving `rk_+ U_n ≤ O(n^3 (3 / ∛4)^n) ≺ 1.89^n`), and §3 (pp. 4–6, Lemma 2 on p. 4 stating the Sapozhenko–Lovász–Stein `(1 + ln |X|) |X| / s` uniform covering bound, and Theorem 2 on pp. 4–6 proving `rk_∨ U_n ≤ n^{O(1)} (3 / 2)^n`).
Formalized in [Code/HammingCode.lean](../CslibFrontier/Foundations/Data/Code/HammingCode.lean) (`exists_partition_minDist_three`), [Combinatorics/LovaszSteinCover.lean](../CslibFrontier/Foundations/Combinatorics/LovaszSteinCover.lean) (`exists_subset_cover_card_le_of_uniform`), [Nondeterministic/PartitionCover.lean](../CslibFrontier/Computability/Communication/Nondeterministic/PartitionCover.lean) (`IsPartitionCover`, `partitionCoverNumber`, `partitionCoverNumber_eq_iInf_nonnegRank_nat`), and [Nondeterministic/UniqueDisjointnessUpper.lean](../CslibFrontier/Computability/Communication/Nondeterministic/UniqueDisjointnessUpper.lean) (`partitionCoverNumber_uniqueDisjointnessRel_le`, `exists_partitionCoverNumber_uniqueDisjointnessRel_le_rpow`, `eventually_partitionCoverNumber_uniqueDisjointnessRel_lt`, `exists_coverNumber_uniqueDisjointnessRel_le`, `two_pow_mul_coverNumber_uniqueDisjointnessRel_le`, and `exists_poly_coverNumber_uniqueDisjointnessRel`).
Footnote 5 on p. 5 elides parity and integer rounding in §3; the Lean proof replaces asymptotic entropy / Stirling estimates with exact integer division parameters (`x_0 = p + q - ⌊n / 2⌋`, `m_1 = ⌊n p / (p + q)⌋`, `z_0 = ⌊p q / (n - p)⌋`) and Vandermonde hypergeometric mode bounds, eliminating Case I (`β ≤ 0.1` or `α ≥ 0.9`) and establishing `rk_∨ U_n ≤ 8 (n + 1)^7 (3 / 2)^n` unconditionally for all `n`.

<a id="shalevshwartzbendavid14"></a>
## shalevshwartzbendavid14

Shai Shalev-Shwartz and Shai Ben-David.
*Understanding Machine Learning: From Theory to Algorithms*.
Cambridge University Press, 2014.
ISBN 978-1-107-05713-5.
A PDF of the book was read on 2026-11-13 for Section 10.2 (AdaBoost, Theorem 10.2 and its proof, pp. 135–137, including the product form `Z_{t+1}/Z_t = 2 √(ε_{t+1} (1 - ε_{t+1}))`) and Lemma 10.3 (Section 10.3).
[Boosting/AdaBoost](../CslibFrontier/MachineLearning/Boosting/AdaBoost.lean) records its differences from Theorem 10.2: early stopping at `ε_t = 0` and ties predicting `false`.

<a id="shamir1979"></a>
## shamir1979

Adi Shamir.
"How to Share a Secret."
*Communications of the ACM* 22(11), 612–613, 1979. https://doi.org/10.1145/359168.359176 . Bibliographic metadata taken from `references.bib`; cited at paper level for Shamir threshold secret sharing over finite fields, wrapped from pinned cslib's `Shamir` module, [Shamir/Linear.lean](../CslibFrontier/Crypto/Protocols/SecretSharing/Shamir/Linear.lean), and [Shamir/Product.lean](../CslibFrontier/Crypto/Protocols/SecretSharing/Shamir/Product.lean).

<a id="shamir1992"></a>
## shamir1992

Adi Shamir.
“IP = PSPACE.”
*Journal of the ACM* 39(4), 869–877 (1992).
DOI: https://doi.org/10.1145/146585.146609.
Original-paper scan inspected: https://crypto.cs.mcgill.ca/~crepeau/COMP647/2007/TOPIC01/Shamir-IP=PSPACE.pdf.

<a id="shannon1956"></a>
## shannon1956

Claude E. Shannon.
*The Zero Error Capacity of a Noisy Channel*.
IRE Transactions on Information Theory 2(3), 8–19, 1956. https://doi.org/10.1109/TIT.1956.1056798 . Bibliographic data from the DOI record.
The zero-error capacity as a limit over strong powers, and the five-word code in the square of the pentagon, are attributed from secondary accounts; the full text was not inspected in this pass.

<a id="shapiropreguicabaquerozawirski2011"></a>
## shapiropreguicabaquerozawirski2011

Marc Shapiro, Nuno Preguiça, Carlos Baquero, and Marek Zawirski.
"Conflict-free Replicated Data Types."
*Stabilization, Safety, and Security of Distributed Systems (SSS 2011)*, Lecture Notes in Computer Science 6976, 386–400, Springer, 2011 (author version: INRIA Research Report RR-7687, August 2011, pp. 1–18, `inria-00609399v2`). https://doi.org/10.1007/978-3-642-24550-3_29 ; open copy https://inria.hal.science/inria-00609399/document . Checked against INRIA RR-7687v2 (22 PDF pp. / 18 report pp., SHA-256 `c70f6223813f6be92a6d80b5c078c69375160f996bc7656b4be2eb937eb95bbf`) on 2026-11-22 UTC: Section 2.1 (report pp. 4–5, Definition 2.1 causal history), Section 2.2 (p. 5, Definitions 2.2–2.3 Strong Eventual Consistency), Section 2.3 (pp. 6–7, Definition 2.4 monotonic semilattice object / `CvRDT` and Theorem 2.1 proving state-based SEC), Section 2.4 (pp. 7–8, Definition 2.5 op-based causal history and causal-delivery assumption on p. 7, Definition 2.6 concurrent downstream commutativity, and Theorem 2.2 proving op-based `CmRDT` SEC), Section 3.2.1 (p. 9, Theorem 3.1 `CvRDT`-to-`CmRDT` emulation), Section 3.2.2 (pp. 9–10, Theorem 3.2 `CmRDT`-to-`CvRDT` emulation), and Sections 4.1–4.2 (pp. 11–12, replicated counters and sets).
LNCS pagination comes from Springer DOI metadata; internal page locators follow INRIA RR-7687v2.
[CRDT/Basic.lean](../CslibFrontier/Computability/Distributed/CRDT/Basic.lean) and [CRDT/DataTypes.lean](../CslibFrontier/Computability/Distributed/CRDT/DataTypes.lean) formalize these `CvRDT`, `CmRDT`, emulation, `CausalBroadcast` bridge, and replicated counter/set steps toward [#7502](https://github.com/cslib-community/cslib-frontier/issues/7502), keeping graph and sequence CRDTs (Section 5) open in [#7502](https://github.com/cslib-community/cslib-frontier/issues/7502).

<a id="shapiropreguicabaquerozawirski2011r"></a>
## shapiropreguicabaquerozawirski2011r

Marc Shapiro, Nuno Preguiça, Carlos Baquero, and Marek Zawirski.
*A comprehensive study of Convergent and Commutative Replicated Data Types*.
INRIA Research Report RR-7506 (`inria-00555588v1`), 50 pp., January 2011. https://inria.hal.science/inria-00555588/document . Checked against that report PDF (51 PDF pp. / 50 report pp., SHA-256 `483279817b1413599a1ce6ef7b721b1a1999b537b4899d4f37af3820b0314716`) on 2026-11-22 UTC: Sections 2.2–2.4 (report pp. 5–13, Propositions 2.1–2.2 and Specifications 3–4 for `CvRDT`/`CmRDT` convergence and mutual emulation), Section 3.1 (pp. 14–16, naive `max`-merge counter anomaly, Specification 6 `G-Counter`, and Specification 7 `PN-Counter`), and Section 3.3 (pp. 21–27, Figure 11 non-commuting untagged `add`/`remove`, Specification 11 `G-Set`, Specification 12 `2P-Set` tombstone permanence, and Specification 15 & Figure 14 Observed-Remove Set `OR-Set` with unique tags and concurrent add-wins semantics).
Formalized as steps toward [#7502](https://github.com/cslib-community/cslib-frontier/issues/7502) in [CRDT/Basic.lean](../CslibFrontier/Computability/Distributed/CRDT/Basic.lean) and [CRDT/DataTypes.lean](../CslibFrontier/Computability/Distributed/CRDT/DataTypes.lean), while `LWW-Element-Set`, graph CRDTs, and `RGA` / Treedoc continuous sequences (Sections 3.3.3–3.3.4, 3.4, and 3.5) remain open in [#7502](https://github.com/cslib-community/cslib-frontier/issues/7502).

<a id="shapley73"></a>
## shapley73

Lloyd S. Shapley.
"On Balanced Games Without Side Payments."
In T. C. Hu and S. M. Robinson (eds.), *Mathematical Programming*, Academic Press, New York, 261–290, 1973.
Bibliographic metadata checked via search summaries; the full text was not inspected, so internal section or theorem locators are not claimed.
Cited by [KKMS.lean](../CslibFrontier/Foundations/Analysis/Brouwer/KKMS.lean) for the KKMS theorem and by [Scarf.lean](../CslibFrontier/GameTheory/Cooperative/Scarf.lean) for balancedness and the KKMS proof of Scarf's theorem.

<a id="shapley74"></a>
## shapley74

Lloyd S. Shapley.
"A Note on the Lemke–Howson Algorithm."
*Mathematical Programming Studies* 1 (*Pivoting and Extensions*, ed. M. L. Balinski), 175–189, Springer, 1974 (also RAND Report R-1538-PR, July 1974). https://doi.org/10.1007/BFb0121248 . Bibliographic metadata checked against the Springer DOI record and secondary summaries on 2026-11-11; the full text was not inspected, so internal theorem numbers are not claimed.
Credited, via [vonstengel07](#vonstengel07) (§3.12), with the determinant-based orientation (index) of the Lemke–Howson graph.

<a id="shapleyscarf74"></a>
## shapleyscarf74

Lloyd Shapley and Herbert Scarf.
*On Cores and Indivisibility*.
Journal of Mathematical Economics 1(1), 23–37, 1974. https://doi.org/10.1016/0304-4068(74)90033-0 . Bibliographic metadata only; the publisher's text is paywalled and was not inspected.
The housing market model and the top trading cycles algorithm (credited there to David Gale) are attributed to it as in [roughgarden13cs364a](#roughgarden13cs364a), Lecture #9, §3, and [schummervohra07](#schummervohra07), §10.6 (which lists the pages as 23–28; the Crossref record was not rechecked).
The housing-market modules also attribute to it the competitive allocation at round-size prices (`isCompetitive_ttc`), from memory of the literature; this attribution is unverified.

<a id="shenuspenskyvereshchagin17"></a>
## shenuspenskyvereshchagin17

Alexander Shen, Vladimir A. Uspensky and Nikolay Vereshchagin.
*Kolmogorov Complexity and Algorithmic Randomness*.
Mathematical Surveys and Monographs 220, American Mathematical Society, 2017. https://doi.org/10.1090/surv/220 . The printed edition was not inspected.
The authors' open draft dated 6 October 2016 (https://www.lirmm.fr/~ashen/kolmbook-eng.pdf) was read on 2026-11-08 UTC: Section 2.2, Theorem 17 (optimal conditional decompressors), Theorem 18 (`C(x | y) ≤ C(x) + O(1)`, `C(x | x) = O(1)`), Theorem 20 (`C(x, y) ≤ C(x) + 2 log C(x) + C(y | x) + O(1)`), Theorem 21 (Kolmogorov–Levin, `O(log n)` form, proof by sections and large sections) and Theorem 22 (`C(x, y) = C(x) + C(y | x) + O(log C(x, y))`); Section 2.3, the definition `I(x : y) = C(y) − C(y | x)` and Theorem 23 (information symmetry).
The draft's theorem numbers are not claimed to match the printed edition, so the library cites sections.

<a id="shi03"></a>
## shi03

Yaoyun Shi.
"Both Toffoli and Controlled-NOT Need Little Help to Do Universal Quantum Computing."
*Quantum Information and Computation* 3(1), 84–92, 2003. https://doi.org/10.26421/QIC3.1-7 ; arXiv version (v2, titled "Both Toffoli and Controlled-NOT need little help to do universal quantum computation") https://arxiv.org/abs/quant-ph/0205115 . The arXiv v2 PDF was read on 2026-11-08 UTC for §2 (the notation `U[A]` for a gate on chosen qubits), §4 (Propositions 4.1 and 4.2, Definition 4.3, Lemmas 4.4 and 4.5, Algorithm 2, Theorem 4.6) and Figure 1.
The library's controlled circuits, phase oracles, reflection about zero and plane rotation follow the proof of Lemma 4.5 in §4.2.
With the Hadamard gate, `σ_z = H σ_x H` holds exactly, so §4.1 is not used.
Journal pagination is taken from the bibliographic record.

<a id="shoup00"></a>
## shoup00

Victor Shoup.
"A Composition Theorem for Universal One-Way Hash Functions."
*Advances in Cryptology – EUROCRYPT 2000*, LNCS 1807, 445–452, Springer, 2000. https://doi.org/10.1007/3-540-45539-6_31 ; preliminary version Cryptology ePrint Archive 1999/017 ( https://eprint.iacr.org/1999/017 ).
Bibliographic metadata checked on 2026-11-14 UTC; the full primary 2000 text was not directly inspected, so the formalization implements the `O(|y| log t)` XOR-masking composition stated in [hhrvw20](#hhrvw20) Section 5.1.4 (Lemma 5.7, p. 30) and verifies the `2`-adic last-occurrence combinatorics, key-construction bijection, and reduction directly in Lean without claiming section, figure, or page locators inside Shoup's 2000 paper.

<a id="shoup1990"></a>
## shoup1990

Victor Shoup.
"New Algorithms for Finding Irreducible Polynomials over Finite Fields."
*Mathematics of Computation* 54(189), 435–447, 1990. https://doi.org/10.1090/s0025-5718-1990-0993933-0 . Bibliographic metadata checked on 2026-11-11 UTC; the full primary PDF was not read directly, so the library relies on the standard deterministic Frobenius/trace construction and deterministic Berlekamp splitting verified directly in Lean without claiming section/theorem locators from the paper.

<a id="simpson05"></a>
## simpson05

Stephen G. Simpson.
*Topics in Logic and Foundations: Spring 2004*.
Draft dated November 1, 2005.
[Author-hosted PDF](https://sgslogic.net/t20/notes/topics-s04.pdf), inspected on 2026-11-12: §2.6, Theorem 2.6.4 and its finite-extension proof, pp. 30–31; register-machine conventions in §1.1.1 and halting-on-input-0 in §2.5.
This is the checked exposition for `KleenePostJump`; the original Kleene–Post article and Soare locators remain unverified.

<a id="sipser13"></a>
## sipser13

Michael Sipser.
*Introduction to the Theory of Computation*, third edition.
Cengage Learning, 2013.
Cited for Definition 2.8 (Chomsky normal form: rules `A → BC` and `A → a`, with `S → ε` permitted for the start variable `S`, and `S` forbidden on every right-hand side; the library's `ChomskyNormalFormGrammar` imposes the latter restriction only when `S → ε` is present) and Theorem 7.16 ("Every context-free language is a member of P", proved by the CYK dynamic program).
Both locators were checked against secondary course material, not the printed book.
Also cited for §5.2 and Theorem 5.15 (Post's correspondence problem is undecidable, proved through the modified problem MPCP by a reduction from `A_TM`).
That locator was checked against secondary summaries, not the printed book.

<a id="skeen1981"></a>
## skeen1981

Dale Skeen.
"Nonblocking Commit Protocols."
*Proceedings of the 1981 ACM SIGMOD International Conference on Management of Data (SIGMOD '81)*, 133–142, 1981. https://doi.org/10.1145/582318.582339 . Checked on 2026-11-22 against an open copy of the published proceedings article, https://www.cs.cornell.edu/courses/cs614/2004sp/papers/Ske81.pdf (SHA-256 `62e2c997193d2ae6b762640d3c2ef8964f824afe68eee14137d1d11cda4b44d4`, printed pp. 133–142): Section 1 (3-site `2PC` blocking scenario, p. 134; fail-stop / no-partition network assumptions, p. 135), Section 2 (finite-state automaton model, centralized `2PC` in Figure 2 on p. 135, committable states on pp. 136–137), Section 4 (Theorem 1, the Fundamental Nonblocking Theorem, p. 138; buffer state `p` in Figure 6, p. 139), Section 5 ("A Nonblocking Central Site Protocol", Figure 7, p. 140), and the second section printed with number `5` ("Termination Protocols", pp. 140–141: Central Site Termination Protocol and backup coordinator failover; the proceedings text numbers both sections `5`).
`CslibFrontier/Computability/Distributed/AtomicCommit/ThreePhaseCommit.lean` formalizes an intermediate global-phase FSA and survivor-polling step toward centralized `3PC` (`ThreePCState`, `threePCStep?`, `threePCLts`, `backupPhase`, `threePCTerminate`; omitting in-flight message buffers and polling all operational survivors in `alive` rather than branching on the elected backup's own local state over messages as on p. 141, and leaving decentralized quorum `3PC`, crash-recovery restarts, and a `CommitProtocol` instantiation to #7289).
Within that global-phase step it proves the non-blocking state invariant (`threePC_no_uncertain_and_committed_globalPhase`), decision stability, safety, and crash-free commit (`threePC_decision_stable_globalPhase`, `threePC_agreement_globalPhase`, `threePC_abort_of_vote_no_globalPhase`, `threePC_failureFree_commit_globalPhase`), and survivor termination across recursive coordinator crashes (`threePCTerminate_mTr_globalPhase`, `threePC_nonblocking_termination_globalPhase`).

<a id="skeenstonebraker1983"></a>
## skeenstonebraker1983

Dale Skeen and Michael Stonebraker.
"A Formal Model of Crash Recovery in a Distributed System."
*IEEE Transactions on Software Engineering* SE-9(3), 219–228, May 1983. https://doi.org/10.1109/TSE.1983.236608 . Checked on 2026-11-22 against an open copy of the published IEEE TSE article, https://www.inf.fu-berlin.de/lehre/SS10/DBS-TA/Reader/3PCSkeenStonebr.pdf (SHA-256 `123a16b7403799151b5097b44ae8db99c7c631862ac214e69d141ddb073dbf0f`, printed pp. 219–228; preliminary technical report *A Formal Model of Crash Recovery in a Distributed System*, Electronics Research Laboratory Memorandum UCB/ERL M80/48, University of California, Berkeley, October 1980, https://www2.eecs.berkeley.edu/Pubs/TechRpts/1980/Archive/ERL-m-80-48.pdf , SHA-256 `21890be6c98704fb7aacc1cc58fe9e2a08c06a47c80297a96968344a0e9770a9`): Sections II–III (FSA transaction model and centralized `2PC`, Figures 1 and 3, pp. 219–222), Section IV-C (Lemma 1 on `2PC` blocking, p. 223), Section V-A ("Partitioning With Loss of Messages", Theorem 4: nonexistence of protocols resilient to a network partition when cross-partition messages are lost, p. 225), and the Appendix Proof of Theorem 4 (p. 227, referring to the boundary-state crossing structure of Proof of Theorem 3 on pp. 226–227).
`CslibFrontier/Computability/Distributed/AtomicCommit/ThreePhaseCommit.lean` formalizes an intermediate partition-cut step after Theorem 4 over asynchronous point-to-point protocols without crash-recovery states (`CommitProtocol`, `CommitProtocol.IsPartitionCutResilient`, `cutCfg`), proving `not_nonblocking_atomicCommit_of_partitionCut` for any nonempty disjoint `(G₁, G₂)` and `not_exists_partitionCutResilient_atomicCommit` for `2 ≤ Fintype.card P` via discrete continuity along the partition-free all-`yes` execution; crash-recovery states, Theorem 5 (undeliverable-message notification), multi-site recovery classes of Section IV-D, and instantiating `3PC` as a `CommitProtocol` remain open under #7289.

<a id="sleatortarjan85"></a>
## sleatortarjan85

Daniel D. Sleator, Robert E. Tarjan.
“Amortized Efficiency of List Update and Paging Rules.”
*Communications of the ACM* 28(2), 202–208, 1985. https://doi.org/10.1145/2786.2793 ; author PDF https://www.cs.cmu.edu/~sleator/papers/amortized-efficiency.pdf (SHA-256 `c5669e50994bf823e0d6c1b001707feb105dd9bc5c3909f8f693d93df872096a`).
Paging scope and equal-capacity specialization checked against source and local mapping; Section 4 ("Paging", pp. 206–208) rechecked against the author PDF on 2026-11-24 UTC for the FIFO rule definition (p. 207), equal-capacity FIFO `k`-competitiveness (p. 208, formalized in `CslibFrontier/DataStructure/Paging/FIFO.lean` via `lruPotential`), and the LIFO alternating counterexample for `n_MIN ≥ 2` (p. 208, formalized in `CslibFrontier/DataStructure/Paging/FIFO.lean`).
Unequal-capacity resource augmentation (`n_MIN < n_A`) and the LFU counterexample (p. 208) remain open.
The list-update cost model of Section 2, Theorem 1 (`C_MF(s) ≤ 2C_A(s) + X_A(s) − F_A(s) − m`) and the remark after its proof (different initial lists, plus the initial inversion count) were checked against the author PDF on 2026-11-07 UTC.

<a id="sleatortarjan85b"></a>
## sleatortarjan85b

Daniel Dominic Sleator, Robert Endre Tarjan.
“Self-Adjusting Binary Search Trees.”
*Journal of the ACM* 32(3), 652–686, 1985. https://doi.org/10.1145/3828.3835 ; author PDF https://www.cs.cmu.edu/~sleator/papers/self-adjusting.pdf . The author PDF was consulted on 2026-11-08 for Section 2 (Lemma 1, Theorems 1–4, pp. 658–660) and Section 3, Lemma 2 (pp. 663–664).

<a id="smithtutte41"></a>
## smithtutte41

C. A. B. Smith and W. T. Tutte.
"On Unicursal Paths in a Network of Degree 4."
*The American Mathematical Monthly* 48(4), 233–237, 1941. https://doi.org/10.2307/2302716 . Bibliographic data from [Stanley's notes](#stanley13) (reference [101]) and the DOI record, checked 2026-11-08 UTC.
The paper was not inspected.
It is cited because the BEST theorem is named partly after its authors.
Stanley (Chapter 10 notes, pp. 198–199) says that they give a determinantal formula for the number of Eulerian tours in a special class of balanced digraphs and were not involved in the original discovery.

<a id="soare87"></a>
## soare87

Robert I. Soare.
*Recursively Enumerable Sets and Degrees*.
Perspectives in Mathematical Logic, Springer, 1987. https://doi.org/10.1007/978-3-662-02460-7 . Bibliographic metadata checked on 2026-11-08; the book was not inspected, and no open copy was used.
It is cited as a standard reference for oracle computations, the use principle and finite extension constructions.
No chapter or theorem locator is claimed.

<a id="stanley13"></a>
## stanley13

Richard P. Stanley.
*Topics in Algebraic Combinatorics*.
Course notes, version of 1 February 2013, author-hosted at https://math.mit.edu/~rstan/algcomb/algcomb.pdf ; published as *Algebraic Combinatorics: Walks, Trees, Tableaux, and More*, Springer, 2013.
Checked in the author-hosted version on 2026-11-08 UTC (Corollary 10.3 re-checked 2026-11-11 UTC), Chapter 10 ("Eulerian digraphs and oriented trees"): the definitions of tours, Eulerian tours, balanced digraphs and oriented trees (pp. 189–190); Theorem 10.2, the BEST theorem `ε(D, e) = τ(D, v) ∏_u (outdeg(u) − 1)!` for a connected balanced digraph, with the last-exit proof (pp. 191–192); Corollary 10.3, root independence `τ(D, v) = τ(D, v')` via cyclic rotation of Eulerian tours in display `(10.1)` (p. 193); Theorem 10.4, the directed matrix-tree theorem `det L₀ = τ(D, v_p)` for a connected digraph with parallel edges and loops (p. 193); Corollary 10.5, the determinant form of the BEST theorem (p. 194); and the chapter notes (pp. 198–199), which attribute Theorem 10.2 to van Aardenne-Ehrenfest and de Bruijn, Theorem 5a, and Theorem 10.4 to Tutte, Theorem 3.6.
The page numbers are those of the notes; the printed book was not checked.

<a id="stoerwagner97"></a>
## stoerwagner97

Mechthild Stoer and Frank Wagner.
"A Simple Min-Cut Algorithm."
*Journal of the ACM* 44(4), 585–591, 1997. https://doi.org/10.1145/263867.263872 . Bibliographic metadata checked against the Crossref record on 2026-11-08.
The publisher's PDF returned HTTP 403 and was not retried, so the paper was not inspected.
Its numbering (the phase recursion as Theorem 2.1, the cut-of-the-phase lemma as Lemma 3.1) comes from secondary descriptions and is unverified, which is why the Lean docstrings name the results rather than the numbers.
The 8-vertex example graph in `CslibFrontierTests/StoerWagner.lean` and the trace of the worked example's first phase come from the English Wikipedia article "Stoer–Wagner algorithm", consulted on 2026-11-08, not from the paper's figure.
A. Frank's note on MA orderings was unreachable (connection failure), and the corresponding section of Schrijver's 2003 monograph was not consulted; neither is cited.

<a id="sudantrevisanvadhan01"></a>
## sudantrevisanvadhan01

Madhu Sudan, Luca Trevisan and Salil Vadhan.
*Pseudorandom Generators without the XOR Lemma*.
Journal of Computer and System Sciences 62(2), 236–266, 2001.
DOI: [10.1006/jcss.2000.1730](https://doi.org/10.1006/jcss.2000.1730).
Publisher metadata and abstract checked by the coordinated source pass on 2026-11-02; the proof-route attribution comes from the pinned Lean module.

<a id="svensson99"></a>
## svensson99

Lars-Gunnar Svensson.
*Strategy-Proof Allocation of Indivisible Goods*.
Social Choice and Welfare 16(4), 557–567, 1999. https://doi.org/10.1007/s003550050160 . Bibliographic metadata checked via search records on 2026-11-24 UTC; the publisher's text is paywalled and was not inspected, so no internal theorem or page locator is claimed.
Cited alongside [ma94](#ma94) and [papai00](#papai00) (`Svensson1999`) for non-bossiness, group strategy-proofness, and the axiomatic characterization of top trading cycles.

<a id="tardosvazirani07"></a>
## tardosvazirani07

Éva Tardos and Vijay V. Vazirani.
"Basic Solution Concepts and Computational Issues."
Chapter 1 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 3–28. https://doi.org/10.1017/CBO9780511800481.003 . Checked firsthand on 2026-11-23 and 2026-11-24 against Section 1.3.6 and Example 1.10 (pp. 14–15: Traffic light `(-100, 1, 0)` game and correlated equilibrium definition), Section 1.4.2 and Theorem 1.11 (pp. 16–18: two-person zero-sum games, the row player's maximin and column player's minimax linear programs on p. 17, and Theorem 1.11 that optimal solutions to the pair of linear programs form a Nash equilibrium), and Section 1.7.2 (pp. 21–22: transferable-utility cooperative games, core allocations, and Example 1.14 defining the Shapley value as the expected marginal contribution under a uniformly random agent ordering).
Cited by `CslibFrontier/GameTheory/Bimatrix/{CorrelatedPolytope,ZeroSum}.lean` and `CslibFrontier/GameTheory/Cooperative/{Basic,ShapleyValue}.lean`.

<a id="tardoswexler07"></a>
## tardoswexler07

Éva Tardos and Tom Wexler.
"Network Formation Games and the Potential Function Method."
Chapter 19 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, 487–516.
A university-hosted PDF of the book was consulted on 2026-11-08 for §19.3.1 (the global connection game, the potential `Σ c_e H_{k_e}`, Lemmas 19.7 and 19.8, Theorem 19.10), §19.3.2 (fair cost sharing as a congestion game with `c_e(x) = c_e / x`) and §19.3.3 (Theorem 19.13: `cost(S) / A ≤ Φ(S) ≤ B · cost(S)` with `A, B > 0` gives price of stability at most `AB`).
Checked on 2026-11-24 against the Chapter 19 text (printed pp. 489–494 and 507–508) for §19.2 ("The Local Connection Game", formalized in [NetworkFormation/LocalConnection.lean](../CslibFrontier/GameTheory/NetworkFormation/LocalConnection.lean)): §19.2.1 (p. 490: unilateral incident-link strategies, infinite disconnection cost, and the ordered-pair social-cost convention `SC(G) = ∑_{u ≠ v} dist_G(u, v) + α |E|`), §19.2.2 (pp. 490–491: Lemma 19.1 on star and complete-graph social optima around `α = 2`, Lemma 19.2 on star and complete-graph pure Nash stability around `α = 1`, and Theorem 19.3 on price of stability `1` outside `(1, 2)` and at most `4 / 3` on `[1, 2]`), §19.2.3 (pp. 491–494: Lemma 19.4 bounding a diameter-`d` pure Nash equilibrium's social cost by `3d` times optimal, Theorem 19.5 on `O(√α)` equilibrium diameter and price of anarchy, and Theorem 19.6 on equilibrium diameter `4α / √n + 9` and `O(1 + α / √n)` price of anarchy), and §19.5.1 (pp. 507–508: attributions to [fabrikantluthramanevapapadimitrioushenker03](#fabrikantluthramanevapapadimitrioushenker03) and [alberseiltsevendarmansourroditty06](#alberseiltsevendarmansourroditty06)).
In Theorem 19.5 (p. 492), the chapter states the equilibrium-diameter bound as `2√α` by setting `dist(u, v) ≥ 2k` and deducing `k ≤ √α`; for odd diameter `d = 2k + 1`, shortcutting `(u, v)` saves `0 + 2 + ... + 2k = k(k + 1) = (d² - 1) / 4`, yielding the sharp bound `√(4α + 1) ≤ 2√α + 1` proved in [NetworkFormation/LocalConnection.lean](../CslibFrontier/GameTheory/NetworkFormation/LocalConnection.lean) and attained on `P_4` at `α = 2` (`diam = 3 > 2√2`, checked in [GameTheory/LocalConnection.lean](../CslibFrontierTests/GameTheory/LocalConnection.lean)).
Checked firsthand on 2026-11-24 against the Chapter 19 text for §19.4.1 (pp. 502–503: Vetta's competitive facility location model with client reservation values, connection costs capped at client value, and second-cheapest pricing; the three-stage trembling-hand equilibrium motivation on p. 503 is not formalized), §19.4.2 (pp. 503–504: Theorem 19.16 exact potential `V(s)` and Corollary 19.17 pure-equilibrium existence, price of stability `1`, best-response convergence, and suboptimality), §19.4.3 (pp. 504–505: utility game properties (i)–(iii), basic and monotone utility games, and Theorem 19.18 showing competitive facility location is a monotone basic utility game), §19.4.4 (p. 505: Theorem 19.19 pure-equilibrium price-of-anarchy bound of `2` for monotone utility games; the coarse-correlated equilibrium bound in [UtilityGame/Basic.lean](../CslibFrontier/GameTheory/UtilityGame/Basic.lean) is an original extension), §19.4.5 (p. 506, with footnote 1: Theorem 19.20 reaching expected social welfare at least `(1/2 - ε)` times optimal after `O(n log(1/ε))` uniformly random best-response moves in monotone basic utility games, formalized under nonnegative empty-set value in [UtilityGame/Basic.lean](../CslibFrontier/GameTheory/UtilityGame/Basic.lean)), §19.5.3 (p. 511: facility installation costs `f(s_i)` and the extension of Theorem 19.19 to mixed Nash equilibria, citing [Vetta](#vetta02)), and Exercises 19.16–19.17 (pp. 515–516: Exercise 19.16(a)–(b) on p. 515 for the closed-neighborhood wealth-sharing location game as a valid utility game with price of anarchy approaching `2`, and Exercise 19.17(a)–(b) on p. 515 for unbounded price of anarchy and the `V(O) ≤ 2 V(S) + F` bound under facility opening costs in [UtilityGame/CompetitiveFacilityLocation.lean](../CslibFrontier/GameTheory/UtilityGame/CompetitiveFacilityLocation.lean); Exercise 19.18 on pp. 515–516 remains open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789)).

<a id="tarjan72"></a>
## tarjan72

Robert Endre Tarjan.
"Depth-First Search and Linear Graph Algorithms."
*SIAM Journal on Computing* 1(2), 146–160, 1972. https://doi.org/10.1137/0201010 . Bibliographic data from the DOI record; the paper was not inspected in this pass.

<a id="tarjan77"></a>
## tarjan77

Robert Endre Tarjan.
*Reference Machines Require Non-Linear Time to Maintain Disjoint Sets*.
Stanford CS-TR-77-603, March 1977.
[Report PDF](https://ftpmirror.your.org/pub/misc/bitsavers/pdf/stanford/Stanford_CS_TR_Collection_2025-12-12/PDF/1977/CS-TR-77-603.pdf).
Section 2, pp. 4–7, checked on 2026-11-14: explicit-reference memory, instruction/record costs, undefined-value traps (p. 6), and equality-only symbols.
This check corrects the earlier manual claim that behavior on undefined data was unspecified.
The local model uses total semantics and does not prove source equivalence or the lower bound.

<a id="tarjan79"></a>
## tarjan79

Robert Endre Tarjan.
“A Class of Algorithms Which Require Nonlinear Time to Maintain Disjoint Sets.”
*Journal of Computer and System Sciences* 18(2), 110–127, 1979. https://doi.org/10.1016/0022-0000(79)90042-4 . The pointer-machine development cites §2, pp. 111–112, and the disjoint-set application in §3, pp. 113–115.
The original implementation records inspection of the journal PDF; the 2026-11-14 correction independently checked the accessible 1977 report above, not the journal PDF.
The chapter distinguishes the formal model from source-faithful algorithms and lower bounds.

<a id="thaler22"></a>
## thaler22

Justin Thaler.
*Proofs, Arguments, and Zero-Knowledge*.
Foundations and Trends in Privacy and Security 4(2–4), 117–660, 2022. https://doi.org/10.1561/3300000030 . Later author manuscript consulted: https://people.cs.georgetown.edu/jthaler/ProofsArgsAndZK.pdf , dated 18 July 2023, §§4.1, 4.6.

<a id="thorup13"></a>
## thorup13

Mikkel Thorup.
“Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence.”
*FOCS 2013*, 90–99. https://doi.org/10.1109/FOCS.2013.18 ; author preprint https://arxiv.org/abs/1311.3121v2 . Bibliographic record checked; the formalization's quantitative adaptation is grounded in the formal abstract at the pinned revision (since retired) and the library source.

<a id="toda1991"></a>
## toda1991

Seinosuke Toda.
“PP Is as Hard as the Polynomial-Time Hierarchy.”
*SIAM Journal on Computing* 20(5), 865–877 (1991).
Publisher abstract inspected 2026-11-01: https://doi.org/10.1137/0220053.

<a id="toran04"></a>
## toran04

Jacobo Torán.
“Space and Width in Propositional Resolution.”
The Computational Complexity Column, *Bulletin of the EATCS* 83, 86–104, 2004 (bibliography key `Toran2004`).
Author-hosted copy: https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/toran/beatcs/column83.pdf . Checked against that copy on 2026-11-08 UTC: Definition 2 (resolution space, as sequences of clause sets obtained by deleting clauses, adding a resolvent or adding an initial clause, the model of `CNF.configLTS`), Definition 7 (the pebble game in which an inference may shift a pebble from a parent to the resolvent) and Lemma 8 (space equals that game's pebble number), Theorem 9 (`tree-size(F) ≥ 2 ^ space(F) - 1`, after Esteban and Torán), and the Section 4 statement that the pigeonhole formulas with `m > n` have resolution space exactly `n + 1` independently of the number of pigeons (the text says "holes", evidently a slip).
The survey's numerical values are those of the shifting game, one less than clause space in the library's convention.
The survey credits the pigeonhole result to its reference [29], J. Torán, “Lower bounds for the space used in resolution”, CSL 1999, LNCS 1683, 362–373; that paper was not inspected.
Journal pagination was taken from the bibliographic record.

<a id="treiber1986"></a>
## treiber1986

R. Kent Treiber.
*Systems Programming: Coping with Parallelism*.
Research Report RJ 5118, IBM Almaden Research Center, April 1986 (bibliography key `Treiber1986`).
Offline corporate technical report; bibliographic metadata verified via [hendlershavityerushalmi2004](#hendlershavityerushalmi2004) (reference [22], p. 215) on 2026-11-22 UTC.
The report text was not directly inspected, so no internal page or figure numbers from `RJ 5118` are claimed; [ConcurrentObjects/TreiberStack.lean](../CslibFrontier/Computability/Distributed/ConcurrentObjects/TreiberStack.lean) cites it for historical attribution of the lock-free `CAS` stack while grounding verified pseudocode and proof locators in [hendlershavityerushalmi2004](#hendlershavityerushalmi2004) and [moirshavit2007](#moirshavit2007).

<a id="tsybakov09"></a>
## tsybakov09

Alexandre B. Tsybakov.
*Introduction to Nonparametric Estimation*.
Springer Series in Statistics, Springer, 2009 (ISBN 978-0-387-79051-0). https://doi.org/10.1007/b13794 . Bibliographic metadata checked on 2026-11-10 (full text not inspected); Section 2.4 (`Divergence Measures and Lower Bounds`) is cited for `f`-divergence properties, Hellinger/TV comparisons (with Tsybakov scaling squared Hellinger by `2`, whereas the library normalizes `h ∈ [0, 1]`), `χ²` tensorization, `2 h² ≤ KL ≤ χ²`, and the Ingster/Le Cam mixture second-moment reduction.

<a id="turpincoan1984"></a>
## turpincoan1984

Russell Turpin and Brian A. Coan.
"Extending Binary Byzantine Agreement to Multivalued Byzantine Agreement."
*Information Processing Letters* 18(2), 73–76, 1984. https://doi.org/10.1016/0020-0190(84)90027-9 . Read on 2026-11-22 UTC in the MIT CSAIL scan of the published journal article, https://groups.csail.mit.edu/tds/papers/Coan/TurpinCoan-ipl84.pdf (4 pages, printed pp. 73–76, dated 28 February 1984; SHA-256 `d2dfb0e2dfe3d367f93df30b6dd9c32b5c35c6b4be42d3f337d57918b86a4836`), and cross-checked against MIT LCS Technical Report MIT/LCS/TR-315, https://groups.csail.mit.edu/tds/papers/Coan/MIT-LCS-TR-315.pdf (April 1984, 7 pages; SHA-256 `21766180f09ac93e1e0078ec9d3d8ba02d848c86dfa52aa2e18f320902455785`).
Checked in the published IPL copy: §1 (pp. 73–74, synchronous completely connected unauthenticated network of `P` processes with at most `T` Byzantine faults, `P > 3T`, prepending two rounds to any symmetric binary Byzantine agreement algorithm with `V`-sized messages sent in round 1 only and 1 bit in round 2); §2 (p. 74, local arrays `v`, `p` and boolean `alert`: a process is `perplexed` iff at least `(P - T) / 2` received round-1 values differ from its initial value and `content` otherwise, `alert` is `true` iff at least `P - 2T` entries of `p` are `true`, and binary agreement on `alert` outputs `default` on `true` and the shared content value via majority vote over `{v(j) | p(j) = false}` on `false`); §3 (pp. 74–75, unnumbered prose proofs of validity and agreement using `(P + T) / 2 + (P - T) / 2 = P`, at least `T + 1` correct content processes when `alert = false`, and at most `T` faulty processes); and §4 (p. 75, `O(P^2)` bound on `O(log |V|)`-bit messages in round 1; the optional 1-round `2T + 5` optimization for biased binary algorithms is not formalized).
In [Byzantine/PhaseKing.lean](../CslibFrontier/Computability/Distributed/Byzantine/PhaseKing.lean), `turpinCoan` writes §2's exact rational threshold `count(heard ≠ input) ≥ (P - T) / 2` in integer-multiplied form `2 * count(heard = input) ≤ n + t`, includes self-messages in `MultivaluedProtocol` (for `i ∉ F`, `heard i = x i` and `perp i = s.perplexed` match `v(j)` and `p(j)` of §2, so `turpinCoan_valueMessagesSent_eq` counts all `(n - |F|) * n` round-1 transmissions), and computes `candidate` uniformly via `uniqueAboveOn {j | perp j = false} (t + 1) heard` on both content and perplexed processes.
`turpinCoan_solvesByzantineAgreement` lands as a step toward [#7210](https://github.com/cslib-community/cslib-frontier/issues/7210) pending an outside-author-fleet source check and `CslibFrontierResults/Entries.lean` registration.

<a id="tutte48"></a>
## tutte48

W. T. Tutte.
"The dissection of equilateral triangles into equilateral triangles."
*Mathematical Proceedings of the Cambridge Philosophical Society* 44(4), 463–482, 1948. https://doi.org/10.1017/S030500410002449X . Not inspected.
[Stanley's notes](#stanley13) (Chapter 10 notes, p. 199, and reference [118]) attribute the directed matrix-tree theorem to Theorem 3.6 of this paper.

<a id="uov26"></a>
## uov26

Ward Beullens, Ming-Shing Chen, Jintai Ding, Boru Gong, Matthias J. Kannwischer, Jacques Patarin, Bo-Yuan Peng, Dieter Schmidt, Cheng-Jhih Shih, Chengdong Tao, Bo-Yin Yang.
*UOV: Unbalanced Oil and Vinegar, Algorithm Specifications and Supporting Documentation*, Version 3.0, August 30, 2026 (bibliography key `UOV2026`). https://csrc.nist.gov/csrc/media/Projects/pqc-dig-sig/documents/UOV_Specification_R3.pdf . Checked against that PDF on 2026-11-14, 2026-11-21, and 2026-11-22 (SHA-256 `ce9044adf1b4e407467968438fa66794882bcaa6411d3509bed72ff54380181a`): Section 3.1 (printed pp. 11–13, specifically p. 12) defines `Upper(M)` as the unique upper-triangular matrix `M'` such that `M' - M` is alternating.
`CslibFrontier.Foundations.LinearAlgebra.Matrix.UpperTriangularQuadratic` formalizes this generic matrix construction (`Matrix.upperQuadratic`), its `Matrix.IsUpperTriangular` and `LinearMap.IsAlt` properties, `Matrix.toQuadraticForm'` equality, and uniqueness.
Section 3.3 (printed p. 19) defines `GF16 = F2[x]/(x^4+x+1)` and `GF256 = F2[x]/(x^8+x^4+x^3+x+1)`, stores elements as polynomial-basis coefficient arrays with the high bit representing the `x^3` or `x^7` coefficient, and packs the first of two `GF16` elements into the low nibble.
`CslibFrontier.Crypto.Protocols.UOV.Field` identifies these fields with `Cslib.BinaryField 4` and `Cslib.BinaryField 8`, proves their modulus codes are `19` and `283`, and formalizes only the individual-element and two-element packing conventions.
Appendix A, Definition 2 (printed p. 49) specifies the independent uniform OV coefficients, uniform invertible input transformation, independently uniform target, and acceptance of any preimage.
`Crypto.Protocols.UOV.Games` gives that ideal coefficient/transformation sampler and its oil-subspace vanishing property; `idealRawScheme` preserves an explicitly supplied finite preimage algorithm, including `none` failures.
Appendix A's ordinary-UOV reduction concerns **salt-UOV**, whose fixed-vinegar/resampled-salt signing differs from the recommended UOV signer.
Section 3.1 (printed pp. 11–13) and Section 3.2.1–3.2.3 / Figure 2 (printed pp. 13–17) specify the `[O; I_m]` oil-space embedding, block public matrices `[[P_i^(1), P_i^(2)], [0, P_i^(3)]]` with upper-triangular `P_i^(1)` and `P_i^(3) = Upper(-O^T P_i^(1) O - O^T P_i^(2))`, precomputed `S_i = (P_i^(1) + P_i^(1)^T) O + P_i^(2)`, and signing linear system `L x = t - y` for `s = [v; 0] + [O; I_m] x` over `q ∈ {16, 256}`; `CslibFrontier.Crypto.Protocols.UOV.BlockKey` formalizes this expanded-matrix key-construction (`BlockKeyMaterial`), oil-block uniqueness, oil-subspace vanishing, and signing-linearization core over arbitrary commutative rings (instantiated at `UOV.F16` and `UOV.F256`).
Full seed-expanded algorithms, byte encodings, retry/failure analysis, and security reductions remain open under [#4987](https://github.com/cslib-community/cslib-frontier/issues/4987).

<a id="valiant77"></a>
## valiant77

Leslie G. Valiant.
"Graph-Theoretic Arguments in Low-Level Complexity."
*Mathematical Foundations of Computer Science 1977* (MFCS '77), Lecture Notes in Computer Science 53, 162–176, Springer, 1977 (bibliography key `Valiant1977`). https://doi.org/10.1007/3-540-08353-7_135 . Bibliographic data from `references.bib`; the proceedings paper was not inspected directly.
The matrix-rigidity definition, `(n - r)^2` upper bound, finite-field random-matrix counting bound, and linear-circuit criterion attributed to it are cited through [Lokam](#lokam09) (§2.1, reference `[98]`), with no direct section or theorem locator claimed in `Valiant1977`.

<a id="valiant79algebra"></a>
## valiant79algebra

Leslie G. Valiant.
"Completeness Classes in Algebra."
*Proceedings of the Eleventh Annual ACM Symposium on Theory of Computing (STOC '79)*, 249–261, 1979 (bibliography key `Valiant1979Algebra`). https://doi.org/10.1145/800135.804419 ; proceedings scan https://sites.math.washington.edu/~billey/colombia/references/valiant.completeness.1979.pdf (13 pages, printed pp. 249–261; SHA-256 `95ba81c4721bf31722bc052177d6260807f3ffb8281572bb0d031f6b0efd080d`).
Checked against that scan on 2026-11-22: §1 ("Algebraic Definitions", printed pp. 249–250, defining formulas over a field `F`, binary-operation formula size `|f|` counting `+` and `×` gates with constant and variable leaves of size `0`, minimal formula size `|P_i|`, simple substitutions `σ : X → Y ∪ F`, projections, and `p`-projections) and §2 ("Universality of the Determinant", printed pp. 250–251, cycle-cover expansion of `Det(Y)` on p. 250 and Theorem 1 with proof on p. 251: every `P_i ∈ F[x_1, …, x_i]` is a projection of `Det_{s × s}` where `s = |P_i| + 2`).
As later noted in §1.2 (printed pp. 63–64; manuscript pp. 3–4) and corrected in §2.1 (printed pp. 67–69; manuscript pp. 7–9; see also §6 Conclusion, printed p. 93 / manuscript p. 33) of Bruno Grenet, Erich L. Kaltofen, Pascal Koiran and Natacha Portier, "Symmetric Determinantal Representation of Formulas and Weakly Skew Circuits", *Contemporary Mathematics* 556 (*Randomization, Relaxation, and Complexity in Polynomial Equation Solving*), 61–96, AMS, 2012 (checked on 2026-11-22 against the publisher's offprint https://membres-ljk.imag.fr/Bruno.Grenet/publis/GKKP11j.pdf , 36 pages, printed pp. 61–96, offprint header dated 2011, SHA-256 `74cf4c896975776c9d356c6e6d4d1c5a540b5c1b36bae4437199bd9f53e87cc3`, and the authors' manuscript https://users.cs.duke.edu/~elk27/bibliography/10/GKKP10.pdf , 36 pages, manuscript pp. 1–36, SHA-256 `7d4578105061e66f930a795699d9c576ae4dab134a30c3fe2921e310c50c84ad`), Valiant's equal-parity addition step (b)(i) on p. 251 can introduce parallel `(s, t)` edges when adding two length-`1` formulas, producing a sum of two variables in a single matrix entry rather than a simple substitution entry; their §2.1 Theorem 1 (`[19]`) and Lemma 2 give a digraph proof of the `e + 1` bound already credited to Liu and Regan (2006), over a field of characteristic different from `2`, for formulas of green size `e` (where scalar multiplications are free, Definition 6) with at least one addition, while the remark immediately below Theorem 1 (printed p. 68 / manuscript p. 8) records the separate addition-free monomial case `c x_1 … x_n` of green size `e = n - 1` (`e + 2` in general, `e + 1` when `c = 1`).
[Determinant/Projection.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Determinant/Projection.lean), [Determinant/Formula.lean](../CslibFrontier/Computability/Circuit/Arithmetic/Determinant/Formula.lean), and [DeterminantalComplexity.lean](../CslibFrontier/Computability/Circuit/Arithmetic/DeterminantalComplexity.lean) use their own strictly upper-triangular specialization branching-program construction (`IsSubstABP`), merging only sources and adding a unit bridge edge between sinks on addition (avoiding parallel edges without parity tracking or division) and taking the `(N - 1).submatrix Fin.castSucc Fin.succ` minor via `Matrix.eq_det_submatrix_sub_one_of_eq_single_add_vecMul`, to prove the `(F.size + 1) × (F.size + 1)` plain-projection bound (`Formula.size` counting `.add`, `.mul`, and `.const` nodes, with input leaves free), projection universality (`exists_isProjection_det`), and universal finiteness of `determinantalComplexity` (`determinantalComplexity_lt_top`) over every commutative ring `K` and arbitrary variable index type `σ` (see also [Orzel, Srinivasan, Tavenas and Yehudayoff](#orzelsrinivasantavenasyehudayoff25) and [Saptharishi](#saptharishi26survey)).

<a id="valiant79"></a>
## valiant79

Leslie G. Valiant.
"The Complexity of Computing the Permanent."
*Theoretical Computer Science* 8(2), 189–201, 1979. https://doi.org/10.1016/0304-3975(79)90044-6 . Bibliographic metadata from `references.bib`; the journal text was not inspected directly, so no internal theorem number or page locator is cited.
Credited at paper level for introducing `#P` and `#P`-completeness under polynomial-time counting Turing reductions.

<a id="valiant79enumeration"></a>
## valiant79enumeration

Leslie G. Valiant.
"The Complexity of Enumeration and Reliability Problems."
*SIAM Journal on Computing* 8(3), 410–421, 1979 (bibliography key `Valiant1979Enumeration`). https://doi.org/10.1137/0208032 . Checked on 2026-11-24 against a scan of journal pages 410–419, https://www.math.cmu.edu/~af1p/Teaching/MCC17/Papers/enumerate.pdf : §2 (p. 411) defines reductions by oracle machines whose oracles return polynomially bounded function values; §4 (p. 413) calls a conjunctive-normal-form formula monotone if no variable is negated and in `k`-form if each conjunct has at most `k` disjuncts; problem 7, MONOTONE 2-SAT, and Theorem 1 (p. 414) state that counting the satisfying assignments of a monotone formula in 2-form is `#P`-complete, proved through reductions 6–7 (p. 415) from perfect matchings by way of imperfect matchings.
The library does not formalize this theorem.
[`SharpTwoSAT.lean`](../CslibFrontier/Computability/Complexity/Problems/SharpTwoSAT.lean) proves the weaker statement that counting is `#P`-complete for general `2-CNF` formulas, on occurring variables and under the bit-oracle convention `AnswersBits`, by an original clause-weight gadget and division-free finite-difference interpolation whose oracle queries contain negated literals.
The monotone theorem remains open in [#3672](https://github.com/cslib-community/cslib-frontier/issues/3672).

<a id="valiant84"></a>
## valiant84

L. G. Valiant.
"A Theory of the Learnable."
*Proceedings of the Sixteenth Annual ACM Symposium on Theory of Computing* (STOC '84), 436–445, 1984. https://doi.org/10.1145/800057.808710 . Bibliographic data from the library's `references.bib` entry `Valiant1984`; the paper was not inspected for this citation.
The manual attributes to it, following the standard account, the observation that pseudorandom functions make polynomial-size circuits unlearnable; no section or theorem locator is claimed.

<a id="vanaardenneehrenfestdebruijn51"></a>
## vanaardenneehrenfestdebruijn51

T. van Aardenne-Ehrenfest and N. G. de Bruijn.
"Circuits and trees in oriented linear graphs."
*Simon Stevin* 28, 203–217, 1951.
Bibliographic data from [Stanley's notes](#stanley13) (reference [1]), checked 2026-11-08 UTC.
The paper was not inspected.
Stanley (Chapter 10 notes, p. 198) attributes the BEST theorem to its Theorem 5a.

<a id="vanderzanden2015"></a>
## vanderzanden2015

Tom C. van der Zanden.
*Parameterized Complexity of Graph Constraint Logic*.
IPEC 2015, LIPIcs 43, 282–293. https://doi.org/10.4230/LIPIcs.IPEC.2015.282 . [Conference PDF](https://drops.dagstuhl.de/storage/00lipics/lipics-vol043-ipec2015/LIPIcs.IPEC.2015.282/LIPIcs.IPEC.2015.282.pdf).
Outside-fleet [agent source check](https://github.com/cslib-community/cslib-frontier/pull/7948#pullrequestreview-6028755848), 2026-11-23: §2.1 and Definition 4; §3, Theorem 6 and its proof, printed pp. 286–289 (PDF pp. 5–8).
The registered result is configuration-to-configuration PSPACE-completeness for planar AND/OR graphs with one fixed bandwidth bound, under the general graph encoding.

<a id="varian04"></a>
## varian04

Hal R. Varian.
"System Reliability and Free Riding."
In L. Jean Camp and Stephen Lewis (eds.), *Economics of Information Security*, Advances in Information Security 12, Springer, 2004, 1–15. https://doi.org/10.1007/1-4020-8090-5_1 ; author-hosted manuscript (revised 30 November 2004, 16 PDF pp.): https://people.ischool.berkeley.edu/~hal/Papers/2004/reliability . Checked against that 16-page author-hosted PDF (chapter pagination 1–15 matches Springer metadata) on 2026-11-24 UTC: §2 (pp. 2–3: valuations `v_i`, unit effort costs `c_i`, reliability curve `P(F)`, and total-effort `∑ x_i`, weakest-link `min_i x_i`, and best-shot `max_i x_i` aggregators), §3.1 (p. 3: Fact 1 characterizing total-effort Nash equilibria via `sup_i x̂_i` with sub-champion free-riding), §3.2 (p. 4: Fact 2 characterizing the weakest-link constant-effort continuum `[0, min_i x̂_i]` for `|ι| ≥ 2` and Pareto dominance of `min_i x̂_i`), §3.3 (pp. 4–5: best-shot single-contributor champion and asymmetric "slacker" Nash equilibria), §4.1–§4.3 (pp. 5–7: eqs. (5)–(6), Fact 3 total-effort underprovision and wrong-agent theorem, and Fact 4 comparing weakest-link and total-effort social optima), §5 (p. 7: Fact 5 opposite group-size comparative statics), §6 (p. 8: Fact 7 identical-agent weakest-link efficiency), and §7.1–§7.2 (pp. 8–11: Fact 8 on p. 9 for Pigouvian failure fine in total effort and Fact 9 on p. 11 for negligence due-care rule in weakest link).
Formalized in `CostGame` minimization form (`val i * (1 - prob (agg x)) + unitCost i * x i`) over `x : ι → ℝ≥0` in [Security/SystemReliability.lean](../CslibFrontier/GameTheory/Security/SystemReliability.lean), including boundary corner `x̂_i = 0` (together with original `((∑ i, c_i) / c_min)` / `|ι|` robust Price-of-Anarchy bounds); §8 ("Sequential moves", pp. 11–13: §8.1 total effort, §8.2 best-effort and weakest-link, Fact 10 on p. 12, and Facts 11–12 on p. 13), §9 ("Adversaries", pp. 13–14), §10 ("Sum of efforts and weakest link", pp. 14–15), and §11 ("Future work", p. 15, noting imperfect information) remain open.

<a id="varian1974"></a>
## varian1974

Hal R. Varian.
"Equity, Envy, and Efficiency."
*Journal of Economic Theory* 9(1), 63–91, 1974 (library key `Varian1974`). https://doi.org/10.1016/0022-0531(74)90075-1 . Bibliographic metadata only; the journal PDF was not directly inspected, so no internal theorem, lemma or page locators are claimed.
Cited in [Welfare.lean](../CslibFrontier/GameTheory/Market/Welfare.lean) for Fisher-market equal-budget envy-freeness (`FisherMarket.IsEquilibrium.utility_le_of_budget_le`, `LinearFisherMarket.IsEquilibrium.envyFree_of_budget_eq`), budget-weighted envy-freeness (`LinearFisherMarket.IsEquilibrium.budget_mul_utility_le`), and proportional-share guarantees (`FisherMarket.IsEquilibrium.utility_budgetShare_supply_le`, `LinearFisherMarket.IsEquilibrium.proportional_share`), steps toward [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789).

<a id="vazirani2007"></a>
## vazirani2007

Vijay V. Vazirani.
"Combinatorial Algorithms for Market Equilibria."
Chapter 5 of Noam Nisan, Tim Roughgarden, Éva Tardos and Vijay V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, pp. 103–134. https://doi.org/10.1017/CBO9780511800481.007 . Key `Vazirani2007`.
Checked in same-fleet review on 2026-11-24 against the 2007 CUP book text (`ch05.txt`): Section 5.1 (pp. 103–104, Fisher market model), Section 5.2 (pp. 105–107: Eisenberg–Gale convex program `(5.1)`, KKT conditions `(i)`–`(iv)` on p. 106, bang-per-buck characterization, and Theorem 5.1 parts 1–3 on p. 107 — note `"If each good has a potential buyer"` is stated explicitly while positive budgets/supplies and buyer nonsatiation are left implicit in `IsNonDegenerate`; part 4 polynomial-bit rationality remains open under [#7789](https://github.com/cslib-community/cslib-frontier/issues/7789)), and Section 5.11 (p. 122, linear Arrow–Debreu exchange market background; note §5.11's `(m + 1)`-agent, `(n + 1)`-good money reduction is distinct from the same-`(I, G)` proportional-endowment embedding in `toExchangeMarket`).
Held for outside-authoring-fleet primary-source review.

<a id="vetta02"></a>
## vetta02

Adrian Vetta.
"Nash Equilibria in Competitive Societies, with Applications to Facility Location, Traffic Routing and Auctions."
*43rd Annual IEEE Symposium on Foundations of Computer Science (FOCS 2002)*, 416–425, IEEE, 2002 (bibliography key `Vetta2002`). https://doi.org/10.1109/SFCS.2002.1181966 . Bibliographic metadata from `references.bib` and the Chapter 19 bibliography of [Tardos and Wexler](#tardoswexler07) (p. 513); the full text was not inspected firsthand, so no internal section or theorem locator in this paper is claimed (`unverified` in [Entries/UtilityGame.lean](../CslibFrontierResults/Entries/UtilityGame.lean)).
Cited via [Tardos and Wexler](#tardoswexler07), §19.4 and §19.5.3 (pp. 502–505, 511), for competitive facility location, valid and basic utility games, and the price-of-anarchy bound of `2` for pure and mixed Nash equilibria in monotone utility games ([UtilityGame/Basic.lean](../CslibFrontier/GameTheory/UtilityGame/Basic.lean), [UtilityGame/CompetitiveFacilityLocation.lean](../CslibFrontier/GameTheory/UtilityGame/CompetitiveFacilityLocation.lean)).

<a id="voleact26"></a>
## voleact26

Tianyu Zhang, Christopher Patton and Samuel Schlesinger.
*VOLE-ACT* (`VOLEACT2026`), design draft at [revision 8869b7255d8f595da79ab4e2edddb364c830978d](https://github.com/Moderation-of-unLinkable-Endorsements/internet-drafts/blob/8869b7255d8f595da79ab4e2edddb364c830978d/draft-authors-mole-vole-act.md).
Read on 2026-11-21: Overview, Tag, Spending, MQ zero-opening scaling forgery, and Proof status.
The formalization factors the target as `Tag(Com(nf, ctx, t, r), x)`, proves extracted-state credit accounting, and implements an original semantic-freshness-to-target-forgery-or-binding-witness reduction.
The source explicitly leaves the structured-target hardness argument and full protocol reductions open.
The scaling lemmas cover the abstract vector equations and the fixed-zero-opening obstruction from a nonzero tail, not byte-encoded balance totals or security of the corrected MQ construction.
Re-read on 2026-11-24: Overview, Parameters / Tag, Initial Issuance (Issue Request and Issue Response), Spending (Spend Request and Spend Response, including checks V1–V4 and the per-key, per-context nullifier records) and Proof status, for `AnonymousToken.Conservation`.
That module proves an original extracted-model credit-conservation reduction step for single-issuer VOLE-ACT: an order-independent accounting bound over request transcripts, an adaptive game bounded by the target EUF-CMA success of `targetForger` plus a target-collision term, and, for `tag = Prod.mk`, a bound on that term by the binding of a keyless commitment scheme.
The draft states no security game or theorem for this property, and the module claims none for the unextracted protocol.
Re-read on 2026-11-25 for `AnonymousToken.ACTMQ`: Instantiations / VOLE-ACT-MQ (`#mq-commitment`, `#mq-com`, `#mq-tag`), Spending `(V4)` `< 2^(8*L)` range checks (`#spending`), Security Considerations (`#mq-zero-opening-forgery`), and Proof status (`#proof-status`).
That module defines the concrete `clawExperiment` and `gCollisionExperiment` games, enforces `(V4)` note range bounds (`NoteInRange`, `actMQConservationExperiment`) so `Set.InjOn actEmbed` instantiates over finite fields, proves structural `G`-collision and zero-opening scaling bounds/obstructions, and keeps all results concrete-game-only.
Re-read on 2026-11-25: Protocol Specification / Initial Issuance (`IssueRequest`, `IssueResponse`, witness `(nf, r)`, `T_init > 0`), Spending (`SpendRequest`, `SpendResponse`, witness `(t, r, x, s, nf', t', r')`, checks V1–V4 and `2^(8L)` range checks), and Proof status (explicitly leaving the unlinkability reduction to VOLEitH zero-knowledge and commitment hiding open), for `AnonymousToken.Unlinkability`, `AnonymousToken.CRTDecoupling`, and `AnonymousToken.CRTHazard` (with generic `[Field K]` left-kernel lemmas in `CslibFrontier.Foundations.LinearAlgebra.Matrix.LeftKernel`).
Those modules formalize original finite query-bounded adaptive malicious-issuer unlinkability bounds, concrete unguarded-vs-guarded balance-partitioning counterexamples, non-black-box CRT decoupling, finite-field/`ZMod 2` left-kernel parity leakage, Issue-to-Spend / Spend balance-prefix distinguishers, and witness-order repair.
Full adaptive extraction, random-oracle realization, privacy, and machine resource certificates remain [#7068](https://github.com/cslib-community/cslib-frontier/issues/7068).

<a id="voleihat26"></a>
## voleihat26

Tianyu Zhang and Christopher Patton.
*VOLE-IHAT* (`VOLEIHAT2026`), design draft at [revision 8869b7255d8f595da79ab4e2edddb364c830978d](https://github.com/Moderation-of-unLinkable-Endorsements/internet-drafts/blob/8869b7255d8f595da79ab4e2edddb364c830978d/draft-authors-mole-vole-ihat.md).
Read on 2026-11-21: RedeemRelation and Security Considerations.
The shared certification interface represents the selected issuer and any valid UOV preimage; fixed-budget one-more hardness refers to the independent random-target game of PoMFRIT.
The extracted single-issuer prefix reduction preserves the signing-call budget; it does not prove the source's issuer-hiding, adaptive extraction, or multi-issuer random-oracle security claim, tracked in [#7068](https://github.com/cslib-community/cslib-frontier/issues/7068).

<a id="volemole26"></a>
## volemole26

Christopher Patton and Tianyu Zhang.
*vole-mole: Post-quantum anonymous credentials based on UOV and VOLE-in-the-Head* (`VoleMole2026`), GitHub repository https://github.com/cloudflareresearch/vole-mole at [commit 87af6871f49d29f9613ee893485c50566ca7d620](https://github.com/cloudflareresearch/vole-mole/tree/87af6871f49d29f9613ee893485c50566ca7d620) (2026-11-18).
Checked firsthand on 2026-11-24: `src/keccak/segmented.hpp` (lines 1–35) instantiates the segmented Keccak-p[800, 12] constraint gadget at `d_zk = 9` (`max(2^3, 3^2) = 9`), `src/act/spend.hpp` specifies `SPEND_WITNESS_BYTES` offsets across lines 92–108 (`ℓ' = 6784`, `C' = 12283`) and invokes `ACT_SPEND_COMBINE_DST` (line 383), `src/dst.hpp` (line 44) defines `ACT_SPEND_COMBINE_DST = make_dst("rata", act::VERSION, 'l', '0')` (trailing ASCII byte `'0'` / `0x30`, also hashed inside the `Combination` constructor for batching `m_uov` constraints in `src/uov/circuit.hpp:63–64`; note `vole-mole`'s other 7-byte tags mostly share trailing `0x30` via distinct penultimate purpose bytes outside the single-trailing-byte model), `src/voleith.hpp` (line 126) extends the FAEST v3 domain-separator convention up to `domain_separator = 4` (`8 + 4 = 12`), and `src/act/issue.hpp:121`, `src/act/spend.hpp:289`, `src/ihat/circuit.hpp:33`, and `src/pomfrit/redeem.hpp:75` instantiate leaf hashing with `faest::leaf_hash::aes_ctr` (`EM128F::leaf_hash_v`).
[HigherDegreeCheck.lean](../CslibFrontier/Crypto/Protocols/VOLE/HigherDegreeCheck.lean) cites the algebraic parameters and models only single-shot conditional Round-2+3 algebraic checks (it does not formalize full `vole-mole` `ZKHash`/`VOLEHash` or Fiat–Shamir soundness); [PRGLeafSeparation.lean](../CslibFrontier/Crypto/Protocols/VOLE/PRGLeafSeparation.lean) cites the `leaf_hash::aes_ctr` instantiation for why PRG-based leaf commitments do not yield a plain-ROM query-log extractor.

<a id="vonstengel07"></a>
## vonstengel07

Bernhard von Stengel.
"Equilibrium Computation for Two-Player Games in Strategic and Extensive Form."
Chapter 3 of N. Nisan, T. Roughgarden, É. Tardos and V. V. Vazirani (eds.), *Algorithmic Game Theory*, Cambridge University Press, 2007, pp. 53–78. https://doi.org/10.1017/CBO9780511800481.005 . The author's preprint https://www.maths.lse.ac.uk/Personal/stengel/TEXTE/agt-stengel.pdf was consulted on 2026-11-08 for Proposition 3.1, the example (3.3), Definition 3.2, Proposition 3.3, (3.5)–(3.6), the polytope form of nondegeneracy in §3.3, §3.4 and Corollary 3.7.
Statement and equation numbers follow that preprint; its page numbers differ from the book's.
In the printed 2007 book chapter (`ch03.txt`, pp. 53–78), Sections 3.7–3.11 (pp. 66–74) were also checked (same-fleet review on 2026-11-24; outside-authoring-fleet source check remains open for `CslibFrontierResults/Entries/ExtensiveGames.lean` and `CslibFrontierResults/Entries/ExtensiveSequenceLP.lean`): extensive-form game trees and singleton information sets in perfect-information games (§3.7, pp. 66–68), subgame-perfect equilibrium and Algorithm 3.9 for perfect-information games via Figure 3.3 (§3.8, pp. 68–69; distinct-payoff uniqueness and entry deterrence are not in §3.8), reduced strategic form (§3.9, pp. 69–70), perfect recall (p. 70), realized-sequence count `|S_i| = 1 + ∑_{h ∈ H_i} |C_h|` (p. 70), realization plans and Proposition 3.10 (pp. 70–71), Proposition 3.11 on realization equivalence under node-reach probabilities (p. 71), Corollary 3.12 / Kuhn's theorem (p. 71), unnumbered realization-plan polytope vertex prose (p. 72), constraint and payoff matrices `(3.25)`–`(3.26)` (p. 72), best-response primal-dual LPs `(3.27)`–`(3.28)` and zero-sum minmax/maxmin LPs `(3.29)`–`(3.30)` with Theorem 3.13 (§3.11, p. 73), and general two-player complementary slackness `(3.31)`–`(3.33)` with Theorem 3.14 (§3.11, p. 74); Exercise 3.12 (p. 78) concerns a depth-`L` binary alternating game with forgotten opponent last move, not a 1-player counterexample to Kuhn's theorem.
The published chapter text (pp. 53–78) was also checked firsthand on 2026-11-24 for Algorithm 3.4 and the uniqueness claim following it (pp. 56–57), Section 3.6 and Proposition 3.8 (pp. 65–66), and Exercises 3.1 and 3.2 (p. 77: uniqueness of support-equation solutions in nondegenerate games and positive probability on all pure best responses in a nondegenerate equilibrium), cited by `CslibFrontier/GameTheory/Bimatrix/CorrelatedPolytope.lean`.

<a id="vww18"></a>
## vww18

Virginia Vassilevska Williams and R. Ryan Williams.
"Subcubic Equivalences Between Path, Matrix, and Triangle Problems."
*Journal of the ACM* 65(5), 27:1–27:38, 2018; preliminary version in FOCS 2010. https://doi.org/10.1145/3186893 . Bibliographic metadata checked on 2026-11-07.
The authors' journal manuscript https://people.csail.mit.edu/virgi/tria-mmult-jv.pdf was consulted on 2026-11-08 for the negative triangle problem over a structure (Section 2), Theorem 4.1, Theorem 4.2, Lemma 4.1 and Lemma 4.2 (and its proof with parts of size `n^{1−a}`).
Theorem and lemma numbers follow that manuscript.

<a id="vzg13"></a>
## vzg13

Joachim von zur Gathen and Jürgen Gerhard.
*Modern Computer Algebra*, 3rd edition, Cambridge University Press, 2013. https://doi.org/10.1017/CBO9781139856065 . Bibliographic metadata checked from the publisher record and Chapter 5 section listing (§5.7 "Rational function reconstruction", p. 115; §5.8 "Cauchy interpolation", p. 118; and §5.10 "Rational number reconstruction"); the full book text was not inspected, and no theorem or algorithm numbers are claimed.

<a id="wagnerfischer74"></a>
## wagnerfischer74

Robert A. Wagner and Michael J. Fischer.
"The String-to-String Correction Problem."
*Journal of the ACM* 21(1), 168–173, 1974. https://doi.org/10.1145/321796.321811 . The bibliographic data come from search summaries of the publisher record (2026-11-08).
The full text is paywalled and was not inspected, so the paper's internal theorem and algorithm numbering is unverified and is not cited.
The manual credits it with the edit-distance dynamic program under general letter costs, with traces (alignments) as the objects of minimum cost and with the `O(|x| |y|)` table, as these are standardly described.

<a id="wang81"></a>
## wang81

Paul S. Wang.
"A p-adic Algorithm for Univariate Partial Fractions."
*Proceedings of the 1981 ACM Symposium on Symbolic and Algebraic Computation (SYMSAC '81)*, 212–217, ACM, 1981. https://doi.org/10.1145/800206.806398 . Bibliographic metadata checked from the ACM Digital Library record; the article text was not inspected, and no theorem or algorithm numbers are claimed.

<a id="wangren25"></a>
## wangren25

Zhikun Wang and Ling Ren.
"Single-Server Client Preprocessing PIR with Tight Space-Time Trade-off."
*Advances in Cryptology – EUROCRYPT 2025*, Lecture Notes in Computer Science, 94–122, Springer, 2025. https://doi.org/10.1007/978-3-031-91095-1_4 ; full version: Cryptology ePrint Archive, Paper 2024/1845 (version of 2024-11-10, 29 pp.), https://eprint.iacr.org/2024/1845 . Checked against the ePrint 2024/1845 version of 2024-11-10 on 2026-11-15 (locators follow the ePrint pagination; the typeset LNCS pages were not consulted directly): Definition 2.1 (p. 10), Section 3.1 (pp. 12–13, operations `Init`/`Access`/`Locate`/`Relocate`, correctness and perfect security, Experiments 3.1 and 3.2 on p. 13), Theorem 3.3 (p. 13), Constructions 3.4 and 3.5 (p. 14), Definition 3.6, Facts 3.7–3.8, Lemma 3.9, Corollary 3.10, Facts 3.11–3.12, and Lemmas 3.13–3.15 (pp. 15–16), and Lemma 3.16 (pp. 16–17).
In [PIR/Preprocessing/Relocation.lean](../CslibFrontier/Crypto/Protocols/PIR/Preprocessing/Relocation.lean), Experiment 3.1's initial output is `(locate s₀ 0, …, locate s₀ (m - 1))` (correcting the p. 13 pseudocode typo "Output (DS.Access(0), DS.Access(1), . . . , DS.Access(m − 1))." to match Experiment 3.2, "Output the position of each element in [m] in A.", and the proof of Lemma 3.16 on p. 16), Experiment 3.2's output is read from the queried cell before the update (correcting the p. 13 pseudocode "Update A[c′] ← A[ci] and A[ci] ← ∅." followed by "If A[c′] ≠ ⊥, output c′.", which outputs `c′` when an empty queried cell selects itself, to match the proof of Lemma 3.16 on p. 16, "For the t-th position ct , no element resides in position ct , then the output of both Experiments 3.1 and 3.2 will be ⊥."), the relocation sequence `c : Fin Q → Fin m'` is fixed and injective with `Q ≤ m' - m` as required in Section 3.1 (p. 12), and the history is 0-indexed as in Definition 3.6 (`C[t] → P(m + t)`).
The permutation is ideal (uniformly random), security is perfect (exact equality of output laws), and adaptively chosen positions are not modelled.
The expected/amortized running-time bounds of Theorem 3.3 and Appendix A, the small-domain PRP instantiation (Section 2.2), the PIR scheme (Section 4, Theorem 4.1 and Construction 4.2), and the `ST = Ω(nw)` lower-bound sketches (Appendix B, Theorems B.1–B.2) are not formalized.

<a id="watrous2018"></a>
## watrous2018

John Watrous.
*The Theory of Quantum Information*.
Cambridge University Press, 2018 (bibliography key `Watrous2018`). https://doi.org/10.1017/9781316848142 ; author-hosted pre-publication draft chapters at https://cs.uwaterloo.ca/~watrous/TQI/ . Checked on 2026-11-24 against the author-hosted Chapter 5 PDF (`TQI.5.pdf`, printed pp. 255–316, SHA-256 `cb6145939a5b337a4f03c09892a19ed3dfb28ec77472c5f7b06ccba46857288a`): Proposition 5.19 (printed p. 265, isometric invariance of quantum relative entropy), Theorem 5.23 (printed p. 268, concavity of von Neumann entropy / nonnegativity of Holevo information), Theorem 5.24 (printed p. 270, subadditivity of von Neumann entropy), Theorem 5.25 (printed p. 271, Araki–Lieb inequality), Theorem 5.35 (printed p. 282, monotonicity of quantum relative entropy under channels), Section 5.3 eqs. (5.271)–(5.277) and Theorem 5.49 (printed pp. 299–300, Holevo's theorem `I_acc(η) ≤ χ(η)` proved via monotonicity of quantum relative entropy under the measurement channel), and Corollary 5.50 (printed p. 300, `I_acc(η) ≤ log(dim(Y))`), all formalized in [Holevo.lean](../CslibFrontier/Foundations/Quantum/DensityMatrix/Holevo.lean).
Theorem 5.53 and Corollary 5.55 (printed pp. 302–304, Nayak's bound for quantum random access codes) remain open under [#3329](https://github.com/cslib-community/cslib-frontier/issues/3329).

<a id="wattenhofer16"></a>
## wattenhofer16

Roger Wattenhofer.
*Principles of Distributed Computing*, lecture notes, ETH Zürich, Chapter 1 "Introduction & Vertex Coloring" (https://disco.ethz.ch/courses/podc_allstars/lecture/chapter1.pdf , 10 pages, SHA-256 `515de9a619af65f46ee1aac7cefcac66036616d65aa6015435c9a2f9fa074385`) and Chapter 7 "Maximal Independent Set" (https://disco.ethz.ch/courses/podc_allstars/lecture/chapter7.pdf , PDF dated 2016-08-23, 13 pages, printed pp. 71–83, SHA-256 `4e79c0d458460e472cad5d9fa752686492880498e90e2d201343b5319f5447ef`).
Inspected 2026-11-08 for §7.3: Algorithm 7.12 ("Fast MIS 2"), Lemma 7.14 (edge removal), Theorem 7.15, Corollary 7.18 and the chapter notes, which attribute the algorithm to Métivier, Robson, Saheb-Djahromi and Zemmari (Distributed Computing 23(5–6), 2011) as a simplification of Luby (SIAM J. Comput. 15(4), 1986).
Re-inspected 2026-11-22 UTC for Chapter 1 (synchronous `LOCAL` vertex coloring) and §7.2, printed pp. 73–76: Algorithm 7.6 ("Fast MIS", `1 / (2 d(v))` marking with degree-then-identifier tie-breaking), Lemma 7.7 (`Pr[v joins] ≥ 1 / (4 d(v))`, pp. 73–74), Lemma 7.8 (good nodes removed with probability `≥ 1 / 36`, pp. 74–75), Lemmas 7.9–7.10 (at least half the edges are good, p. 75), and Theorem 7.11 (`E[removed edges] ≥ m / 72`, pp. 75–76), formalized as synchronous `LOCAL` steps toward [#7505](https://github.com/cslib-community/cslib-frontier/issues/7505) and [#3270](https://github.com/cslib-community/cslib-frontier/issues/3270) in [LocalGraph/LubyMIS.lean](../CslibFrontier/Computability/Distributed/LocalGraph/LubyMIS.lean).

<a id="welchlynch1988"></a>
## welchlynch1988

Jennifer Lundelius Welch and Nancy Lynch.
"A New Fault-Tolerant Algorithm for Clock Synchronization."
*Information and Computation* 77(1), 1–36, 1988. https://doi.org/10.1016/0890-5401(88)90043-0 . Bibliographic metadata checked via DOI/bibliography records only; the journal full text was not inspected, so no internal section, lemma or theorem numbers are cited.
Cited as background for the separated lockstep-round, drift-free Byzantine trimmed-midpoint steps in [`ClockSync/ByzantineSync.lean`](../CslibFrontier/Computability/Distributed/ClockSync/ByzantineSync.lean) (`lockstepByzantineClockStep`, `lockstepDriftFreeByzantineOffset_mem_Icc`, `lockstepDriftFreeByzantineOffset_abs_sub_le`, `lockstepDriftFreeByzantineOffsetIter_abs_sub_le`), which reuse `ApproxAgreement.multisetMidTrim` on zero-drift clocks and do not formalize the paper's local-timer-triggered asynchronous periodic resynchronization under nonzero bounded hardware clock drift (tracked in [#7202](https://github.com/cslib-community/cslib-frontier/issues/7202)).

<a id="williams2010"></a>
## williams2010

R. Ryan Williams.
*Improving Exhaustive Search Implies Superpolynomial Lower Bounds*.
STOC 2010.
The author's full version dated May 4, 2010, https://people.csail.mit.edu/rrw/improved-algs-lbs2.pdf , was checked on 2026-11-11 for Theorem 1.1, the violated-clause circuit in the proof of Theorem 3.2 (printed p. 10), and Lemma 3.2.
The succinct-verifier modules formalize the violated-clause test and its native guess-and-verify simulation, with a quadratic unary certificate format; they do not claim the full NEXP circuit lower bound or the source's `O(s log s)` description length.

<a id="williams25"></a>
## williams25

R. Ryan Williams.
*Simulating Time With Square-Root Space*. arXiv:2502.17779v1 (25 February 2025), Appendix A, equation (6); version states to appear in STOC 2025. https://arxiv.org/abs/2502.17779v1 .

<a id="williamsonshmoys11"></a>
## williamsonshmoys11

David P. Williamson and David B. Shmoys.
*The Design of Approximation Algorithms*.
Cambridge University Press, 2011. https://doi.org/10.1017/CBO9780511921735 . Section 1.6 (Algorithm 1.2, Theorems 1.11 and 1.12) and the Chapter 1 Chapter Notes attribution of the greedy set-cover analysis to Chvátal (Mathematics of Operations Research 4(3), 233–235, 1979, https://doi.org/10.1287/moor.4.3.233) were checked against the authors' electronic edition at https://www.designofapproxalgs.com on 2026-11-07, as were Section 2.4 (Lemma 2.10, Theorems 2.11 and 2.12) and the Chapter 2 Chapter Notes, which attribute nearest addition and its analysis to Rosenkrantz, Stearns and Lewis (1977) and call the double-tree algorithm folklore.
The handshake argument, Theorem 2.13 (Christofides' algorithm is a 3/2-approximation) and its proof, and the Chapter 2 Notes attribution to Christofides (reference [73]) were checked against the same edition on 2026-11-08, as were Exercise 2.5 (the MST 2-approximation for Steiner tree, metric part (a) and metric completion part (b)), Section 12.3 and the Chapter 12 Notes attribution of the factor-2 Steiner heuristic to Moore via Gilbert and Pollak (reference [130]).
Section 2.2 (Algorithm 2.1, Theorems 2.3 and 2.4) and the Chapter 2 Chapter Notes, which attribute the k-center algorithm and analysis to Gonzalez (Theoretical Computer Science 38, 293–306, 1985, https://doi.org/10.1016/0304-3975(85)90224-5), an alternative 2-approximation to Hochbaum and Shmoys (Mathematics of Operations Research 10(2), 180–184, 1985, https://doi.org/10.1287/moor.10.2.180) and Theorem 2.4 to Hsu and Nemhauser (Discrete Applied Mathematics 1(3), 209–215, 1979, https://doi.org/10.1016/0166-218X(79)90044-1), were checked against the same electronic edition on 2026-11-08; the three original papers were not checked.

<a id="winter16"></a>
## winter16

Andreas Winter.
"Tight Uniform Continuity Bounds for Quantum Entropies: Conditional Entropy, Relative Entropy Distance and Energy Constraints."
*Communications in Mathematical Physics* 347(1), 291–313, 2016. https://doi.org/10.1007/s00220-016-2609-8 . Cited at topic level for the classical special case of the conditional-entropy continuity bound with observation-independent modulus `(1 + ε) h₂(ε / (1 + ε))`; no specific theorem or lemma number from the journal text is claimed.

<a id="wrochna2014"></a>
## wrochna2014

Marcin Wrochna.
*Reconfiguration in bounded bandwidth and treedepth*. arXiv:1405.0847v1, 5 May 2014. https://arxiv.org/pdf/1405.0847v1 . Outside-fleet [agent source check](https://github.com/cslib-community/cslib-frontier/pull/7948#pullrequestreview-6028755848), 2026-11-23: §2 through Lemma 2 and §3, Theorem 3 (p. 5).
The registered result is the PSPACE-hardness direction for one fixed finite digraph H, with equal-length words and single-position changes preserving consecutive-pair legality.

<a id="yannakakis91"></a>
## yannakakis91

Mihalis Yannakakis.
*Expressing Combinatorial Optimization Problems by Linear Programs*.
Journal of Computer and System Sciences 43(3), 441–466, 1991. https://doi.org/10.1016/0022-0000(91)90024-Y . Bibliographic metadata checked against the Crossref record on 2026-11-08 UTC.
The publisher page returned HTTP 403 and the primary text was not inspected.
No theorem number is claimed; the factorization theorem and the rectangle covering bound are attributed to this paper as reported by [fmptw15](#fmptw15), Section 1 and Theorems 3 and 4.

<a id="yao77"></a>
## yao77

Andrew Chi-Chih Yao.
"Probabilistic Computations: Toward a Unified Measure of CslibFrontier."
*Proceedings of the 18th Annual Symposium on Foundations of Computer Science* (FOCS 1977), 222–227. https://doi.org/10.1109/SFCS.1977.24 . Bibliographic data from the DOI record; the full text was not inspected in this pass.
The manual credits this paper with Yao's minimax principle, whose easy (averaging) direction gives randomized lower bounds from distributions over inputs.

<a id="yao80"></a>
## yao80

Andrew Chi-Chih Yao.
"New Algorithms for Bin Packing."
*Journal of the ACM* 27(2), 207–227, 1980. https://doi.org/10.1145/322186.322187 . Bibliographic data and the abstract are from the Crossref record of the DOI, checked on 2026-11-08 UTC.
The abstract defines `r(S)` as the maximum ratio `S(L)/L*` for large `L*`, where `S(L)` is the number of bins used by algorithm `S` and `L*` the minimum number needed.
It states that every on-line algorithm `S` has `r(S) ≥ 3/2`.
The item types `1/7 + ε`, `1/3 + ε` and `1/2 + ε` of the construction are as reported in [baloghbekesidosaepsteinlevin18](#baloghbekesidosaepsteinlevin18), Section 1.
The full text was not inspected, since no open copy was found, so the theorem number and Yao's own proof are not recorded.
[OnlineLowerBound](../CslibFrontier/Algorithms/Lean/BinPacking/OnlineLowerBound.lean) cites the paper on that basis.

<a id="yao80b"></a>
## yao80b

F. Frances Yao.
"Efficient Dynamic Programming Using Quadrangle Inequalities."
*Proceedings of the 12th Annual ACM Symposium on Theory of Computing* (STOC 1980), 429–435. https://doi.org/10.1145/800141.804691 . The bibliographic data come from secondary indexes and search summaries; the paper was not inspected in this pass.
The manual credits it, as secondary sources do, with the lemma that the optimal cost inherits the quadrangle inequality from a monotone weight satisfying it, and with the resulting monotonicity of optimal roots.
Its lemma and theorem numbers are not cited.

<a id="yao86"></a>
## yao86

Andrew Chi-Chih Yao.
"How to Generate and Exchange Secrets (Extended Abstract)."
*27th Annual Symposium on Foundations of Computer Science (FOCS 1986)*, 162–167, 1986. https://doi.org/10.1109/SFCS.1986.25 . Bibliographic data from the DOI record and secondary listings, cited as the customary origin of garbled circuits.
The full text was not inspected in this pass.

<a id="yap1983"></a>
## yap1983

Chee K. Yap.
"Some Consequences of Non-Uniform Conditions on Uniform Classes."
*Theoretical Computer Science* 26(3), 287–300, 1983. https://doi.org/10.1016/0304-3975(83)90020-8 . Bibliographic data from the library bibliography (`Yap1983`); the full text is paywalled and was not inspected, so no theorem number in Yap's paper is cited.
The manual attributes to it the collapse `coNP ⊆ NP/poly → PH = Σ₃` (`NP ⊆ coNP/poly → PH = Σ₃`), as cited in [Bodlaender, Jansen and Kratsch](#bodlaenderjansenkratsch2014), Theorem 2 (p. 6 of arXiv v1).

<a id="yekhanin12"></a>
## yekhanin12

Sergey Yekhanin.
*Locally Decodable Codes*.
Foundations and Trends in Theoretical Computer Science 6(3), 139–255, 2012. https://doi.org/10.1561/0400000030 . Definition 6.1 and Lemma 6.2 (§6.1.1, private information retrieval from perfectly smooth codes) were checked on 2026-11-08 against the author's draft at https://www.microsoft.com/en-us/research/wp-content/uploads/2016/02/LDC_now.pdf ; the numbering of the published monograph was not checked.

<a id="younger67"></a>
## younger67

Daniel H. Younger.
"Recognition and Parsing of Context-Free Languages in Time n³."
*Information and Control* 10(2), 189–208, 1967. https://doi.org/10.1016/S0019-9958(67)80007-X . Bibliographic metadata was checked on 2026-11-08; the article body was not inspected.
It is cited, with [Kasami 1965](#kasami65), as an original source of the CYK algorithm.

<a id="zhang05"></a>
## zhang05

Shengyu Zhang.
"On the power of Ambainis's lower bounds."
*Theoretical Computer Science* 339(2–3), 241–256, 2005. https://doi.org/10.1016/j.tcs.2005.01.019 ; open version arXiv:quant-ph/0311060v2, https://arxiv.org/abs/quant-ph/0311060 . Checked in arXiv:quant-ph/0311060v2 on 2026-11-11: Section 1 Definition 1 and Theorem 3 (the general weighted adversary `Alb₃`, proved in `WeightedAdversary.lean`), Section 2 Theorem 5 (`Alb₂ ≤ Alb₃`, realized via `WeightScheme.ofUnweighted` and used to prove `one_sub_mul_sqrt_le_two_mul_mul_sqrt` in `AmbainisAdversary.lean`), The `Alb₃ ≤ ADV` mapping (`WeightScheme.le_spectralAdversary`) is an original proof; the cited Theorem 6 maps `Alb₃` to `√(N C_-(f))` instead.
Journal pagination was not inspected directly.

<a id="zivlempel77"></a>
## zivlempel77

Jacob Ziv and Abraham Lempel.
"A Universal Algorithm for Sequential Data Compression."
*IEEE Transactions on Information Theory* 23(3), 337–343, 1977. https://doi.org/10.1109/TIT.1977.1055714 . Bibliographic data from the DOI record and secondary summaries.
It is cited as the origin of the sliding-window code that writes each phrase as (pointer, length, next symbol).
The paper's text was not inspected, and its bounded lookahead and fixed-width codewords are not formalized.

<a id="zivlempel78"></a>
## zivlempel78

Jacob Ziv and Abraham Lempel.
"Compression of Individual Sequences via Variable-Rate Coding."
*IEEE Transactions on Information Theory* 24(5), 530–536, 1978. https://doi.org/10.1109/TIT.1978.1055934 . Bibliographic data from the DOI record and secondary summaries.
The incremental parsing rule (each phrase is the shortest new prefix) is attributed through [Cover and Thomas](#coverthomas06); the paper's text was not inspected in this pass.

<a id="zpzs24"></a>
## zpzs24

Mingxun Zhou, Andrew Park, Wenting Zheng and Elaine Shi.
"Piano: Extremely Simple, Single-Server PIR with Sublinear Server Computation."
*2024 IEEE Symposium on Security and Privacy (SP)*, 4296–4314, 2024. https://doi.org/10.1109/SP54263.2024.00055 ; full version (author order Mingxun Zhou, Andrew Park, Elaine Shi and Wenting Zheng): Cryptology ePrint Archive, Paper 2023/452, https://eprint.iacr.org/2023/452.pdf . Checked against the full ePrint version on 2026-11-12: Section 2 and Section 3.1–3.2 (Figure 1 on p. 6, Definition 3.1 on pp. 7–8, Theorems 3.2–3.4 on pp. 8–9), Appendix A (pp. 20–21, Figure 3 compacted query offsets and `√n`-parity server replies), and Appendix C.1–C.2 (pp. 24–26, Theorem C.1 and Lemma C.2).
The library formalizes deterministic conditional correctness for the Figure 1 `HintTable` client (`CanAnswerSeq`, with replacement and backup entries sharing one per-chunk counter `used`), exact perfect privacy in the ideal-random-set model for the separate unbounded-backup server-view hybrid `pianoHybridScheme` (which sets replacement and backup parity bits to `false` and is not a correct PIR scheme), and the exact bit-alphabet online communication counts; the PRF reduction, full-client privacy, the Theorem 3.3 failure-probability bound, pipelining, the Appendix A server algorithm, and storage/runtime bounds are not formalized.

<a id="zre15"></a>
## zre15

Samee Zahur, Mike Rosulek, David Evans.
"Two Halves Make a Whole: Reducing Data Transfer in Garbled Circuits Using Half Gates."
*Advances in Cryptology – EUROCRYPT 2015*, Lecture Notes in Computer Science 9057, 220–250, 2015. https://doi.org/10.1007/978-3-662-46803-6_8 . Full version: Cryptology ePrint Archive, Report 2014/756, https://eprint.iacr.org/2014/756 . Checked on 2026-11-15 against the ePrint PDF of March 16, 2015, headed "In 34th Eurocrypt, Sofia, Bulgaria, April 2015" (28 pages, SHA-256 `789ecaf8651b6dc8341d6033f951d76c0e6f4b04427cdde26cf91ecfb0af3083`); locators use its printed page numbers, which are also its PDF page numbers.
P. 8: the hash `H : {0,1}^k × ℤ → {0,1}^k` used with a unique public index for each group of calls.
§4, p. 10: the opening remark that for circuits of AND and XOR gates everything about `f` is public, so no separate `Φ(f)` is defined, and §4.1, Definition 1: circular correlation robustness, with the oracle `Circ_R(x, i, b) = H(x ⊕ R, i) ⊕ bR` for `R ∈ {0,1}^(k−1)1`, a random function `Rand` with `k`-bit output, legal query sequences that never ask one `(x, i)` with different `b`, polynomial-time adversaries and negligible advantage; the adversary has unrestricted access to `H`.
P. 11: Definition 3, circular correlation robustness for naturally derived keys.
P. 12: Definition 3 is a restricted version of Definition 1, and Theorem 1 states that the scheme satisfies `obv.simS` and `prv.simS` (the notions of [bhr12](#bhr12)) for any `H` with correlation robustness for naturally derived keys.
`Computational/CircularCorrelationRobust.lean` formalizes Definition 1 with the differences listed in the [assumptions inventory](programs-crypto-and-probability/assumptions.md).
P. 9: Figure 2, the garbling scheme, whose hash calls at AND gates are numbered by `NextIndex`.
Pp. 12–14: the proof of Theorem 1, a chain of hybrids from the simulator to the real garbling; Fig. 3 (p. 13) gives the simulator `S` and the hybrid `G₁^O`, which knows the input, samples the labels the evaluator holds and, at each AND gate, asks its oracle `(W_a, j, v_b ⊕ lsb W_b)` and `(W_b, j', v_a)` on the labels `W_a`, `W_b` it holds.
`Garbling/HalfGates/Reduction.lean` follows `G₁^O` (checked on 2026-11-15 against the same PDF, by the author of that module).
The single-instance simulation privacy of `Garbling/HalfGates/Privacy.lean` is still cited at paper level.

<a id="hoorylinialwigderson06"></a>
## hoorylinialwigderson06

Shlomo Hoory, Nathan Linial and Avi Wigderson.
"Expander graphs and their applications."
*Bulletin of the American Mathematical Society* 43(4):439-561, 2006.
The library formalization pins the May 3, 2006 draft (`expanderbookr1.pdf`).
Section 2.4 (Lemma 2.5) covers the singular-value adaptation (separated from the GV coding background in §12.3.1), mapping the adjacency-eigenvalue normalization to the normalized biadjacency singular value (including bipartite trivial modes) with `d = |D|`, `N = |L| = |R|`, and edge count `d*N`.

<a id="sipserspielman96"></a>
## sipserspielman96

Michael Sipser and Daniel A. Spielman.
"Expander codes."
*IEEE Transactions on Information Theory* 42(6):1710-1722, 1996.
Section VI (Lemma 15, pp. 1715-1716) provides the local-to-global distance formula.
The formalization marks two-code, asymmetric, arbitrary-alphabet, and finite-ring extensions as original adaptations.
