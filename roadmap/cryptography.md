# Roadmap: Cryptography

Part of the [roadmap](../ROADMAP.md), which explains what an entry is and when one is added or removed.

### Cryptographic landmarks

- **Completeness of oblivious transfer** ([#1212](https://github.com/cslib-community/cslib-frontier/issues/1212)): In the ideal OT-hybrid model, every polynomial-time multiparty functionality admits a protocol secure against static malicious corruptions, with real/ideal simulation and abort, under the standard communication assumptions.
  The route needs ideal commitment realization from OT with efficient two-sided simulation, composition, a malicious compiler and MPC simulation.
- **Regev's worst-case to average-case reduction** ([#1213](https://github.com/cslib-community/cslib-frontier/issues/1213)): For suitable `q` and Gaussian noise rate `α` with `αq > 2√n`, an efficient search-LWE algorithm yields a quantum polynomial-time algorithm for worst-case GapSVP and SIVP within `Õ(n/α)`.
  The noise law, modulus restrictions and quantum reduction are part of the theorem.
  Open steps toward it are Lemma 3.11's single-sample experiment ([#2767](https://github.com/cslib-community/cslib-frontier/issues/2767)) and the Micciancio–Regev worst-case to average-case reduction for SIS ([#6861](https://github.com/cslib-community/cslib-frontier/issues/6861)).

### Modern fully homomorphic encryption

Develop these in reviewable milestones, reusing the finite sampling, gadget algebra, native certificates and game reductions where their hypotheses match.
The [pre-rewrite FHE section](https://github.com/cslib-community/cslib-frontier/blob/c89dd48c/ROADMAP.md#modern-fhe-methods-and-deployment-priorities) maps the schemes to current libraries and workloads.

- **Gentry's exact loss and running time** ([#2585](https://github.com/cslib-community/cslib-frontier/issues/2585), [#2722](https://github.com/cslib-community/cslib-frontier/issues/2722)): For Gentry's bootstrapping instantiated with GSW, prove his exact concrete-security loss and the `poly(ℓ, d)` running-time clause of his Theorem 4.
  This includes the literal source loss mapping, a multiplicative comparison of primitive costs with adversary runtime, and the complete modular-game time and space assembly with prepared-metadata accounting.

1. **Ring arithmetic and RLWE**: Natively certify RNS/CRT conversions, parity-preserving modulus switching and negacyclic NTT multiplication over `(Z/qZ)[X]/(X^d + 1)`.
   Define the RLWE secret and error laws and experiment separately, since an ordinary-LWE reduction does not give them.
   For Module-LWE encryption, add native encryption, seed codecs and small-secret security.
2. **FHEW/TFHE programmable bootstrapping** ([Ducas–Micciancio](https://eprint.iacr.org/2014/816); [Chillotti–Gama–Georgieva–Izabachène](https://eprint.iacr.org/2016/870)): Prove the bootstrap decrypts to `f(m)` with its noise, failure, width and runtime bounds, under negacyclic lookup restrictions and torus representations.
   Floating-point FFTs need rounding-error proofs.
   Then add [Lee et al.'s smaller-key methods](https://eprint.iacr.org/2022/198) and batched variants with exact secret distributions and joint error bounds.
3. **Exact packed BFV/BGV** ([Brakerski–Gentry–Vaikuntanathan](https://eprint.iacr.org/2011/277); [Fan–Vercauteren](https://eprint.iacr.org/2012/144)): Slot encoding, multiplication, relinearization, rotations and level management, with leveled evaluation before a separately proved refresh.
   Equality modulo the plaintext modulus differs from ordinary integer equality, which needs a range bound.
4. **Approximate packed CKKS and its bootstrap** ([Cheon–Kim–Kim–Song](https://eprint.iacr.org/2016/421)): An explicit approximate-correctness interface and a norm bound on decoded error covering rescaling, rounding, key switching and rotations.

For each scheme, prove chosen-plaintext security for the actual algorithms and public evaluation keys; keep LWE/RLWE, circular/KDM assumptions and attack-cost estimates distinct; introduce a decryption-failure game when correctness is not perfect; and require nonvacuous parameter families and full-input native runtime.

### Public-key, lattice and symmetric constructions ([#640](https://github.com/cslib-community/cslib-frontier/issues/640))

- **Sigma protocols and Fiat–Shamir** ([#5770](https://github.com/cslib-community/cslib-frontier/issues/5770)): Prove random-oracle EUF-CMA security of Schnorr signatures under discrete log for random group setups, beyond fixed group families of polynomial description length given to the reduction, and certify the generic Fiat–Shamir forking reduction for other Sigma protocols.
  Identification and eavesdropping security do not suffice.
- **Lattice signatures from SIS**: Prove random-oracle EUF-CMA security of Lyubashevsky's signatures (2009, 2012) from SIS by a native reduction that receives only `A`, with an efficient secret-free simulator and a security parameter family.
  This includes bounding the all-attempt signing simulation through visible oracle reads ([#2798](https://github.com/cslib-community/cslib-frontier/issues/2798)).
- **Lattice identification and Dilithium-style signatures**: Prove identification security under SIS, and the security of Dilithium-style signature schemes over module SIS and module LWE, as theory.
- **Prime-modulus LWE asymptotic reductions** ([#3673](https://github.com/cslib-community/cslib-frontier/issues/3673)): Certify polynomial-time matrix inversion over `ZMod q` for the normal-form reductions and approximate uniform `ZMod q` sampling with computable argmax selection for `SearchLWE` to `DecisionLWE`.
- **Hybrid encryption** ([#2749](https://github.com/cslib-community/cslib-frontier/issues/2749)): Extend adaptive CCA security of KEM–DEM hybrid encryption beyond the `n`-bit-message bound of Boneh–Shoup Exercise 12.5(a) to arbitrary message spaces (unrestricted `WordINDCCA2`), prechallenge KEM queries and multiple encapsulation challenges.
- **Paillier encryption and composite residuosity**: Construct native balanced-modulus generation for Paillier encryption and instantiate its IND-CPA security under Decisional Composite Residuosity (Katz–Lindell Theorem 15.13) with that generator.
- **Garbled circuits and Yao's protocol** ([#6045](https://github.com/cslib-community/cslib-frontier/issues/6045)): Prove semi-honest security of Yao's two-party protocol with oblivious transfer realized by a protocol, through a computational composition theorem that replaces the ideal batched OT oracle of the protocol family `Yao.family`.
  An extension is half-gates privacy under circular correlation robustness for naturally derived keys, the weaker assumption of Zahur, Rosulek and Evans's Theorem 1 ([#5293](https://github.com/cslib-community/cslib-frontier/issues/5293)).

### Zero-knowledge proof systems toward libzk ([#643](https://github.com/cslib-community/cslib-frontier/issues/643))

The libzk components are listed in build order, ending with libzk's compositional structure.

- **Composition and round-by-round knowledge soundness**: Parallel and OR composition of protocols, with round-by-round knowledge soundness preserved under parallel and OR composition.
- **Oracle statements**: Let a later phase query an earlier phase's oracle message (virtual output oracles, as in ArkLib), with knowledge soundness and zero knowledge in oracle worlds.
- **Efficient simulators and auxiliary-input zero knowledge**: Malicious-verifier auxiliary-input zero knowledge on the interactive core with efficiency-certified simulators, in statistical and computational forms.
- **Polynomial commitments and Ligero**: Polynomial commitment and evaluation-query reductions, and, for the Ligero IOP, prover-committed column oracles with straight-line witness extraction, quadratic constraint checks, zero-knowledge row masking and BCS compilation.
- **BCS transform**: Extend the random-oracle BCS compiler with state-restoration knowledge soundness ([#6042](https://github.com/cslib-community/cslib-frontier/issues/6042)), machine-level verifier runtime and zero knowledge.
  A polynomial-time encoding of NP witnesses into IOPs then gives the BCS version of Kilian's succinct arguments for NP.
- **VOLE constraint reductions and VOLE-in-the-head**: Prove full zero-knowledge security of VOLE-based proofs for the arithmetic-circuit relation `∃ w, C.eval (x ++ w) = y`, with fresh-session amplification, scalar-challenge batching, growing fields, adversarial setup and scheduling, then VOLE-in-the-head.
  This includes a native circuit prover/verifier certificate with honest-sender realization ([#2765](https://github.com/cslib-community/cslib-frontier/issues/2765)) and raw-bit adversarial transport ([#2744](https://github.com/cslib-community/cslib-frontier/issues/2744)).
- **libzk composition**: Express libzk's compositional structure as a composition of these components, without ciphersuites.

### Private information retrieval ([#3251](https://github.com/cslib-community/cslib-frontier/issues/3251))

Information-theoretic private information retrieval, following Chor–Goldreich–Kushilevitz–Sudan (CGKS).

- **Information-theoretic PIR**: Complete CGKS Section 3.3 with covering-code schemes for the other rows of Figure 1 and the asymptotic lower estimate, and model the machine running time of the user and servers (CGKS Section 2.4).
- **PIR lower bounds**: Lower bounds for general two-server schemes, beyond the linear-summation schemes of CGKS Section 5.2, which the source leaves open.
- **Batch SPIR with client preprocessing (Hoover–Persiano–Yeo, FOCS 2026, arXiv:2607.06451v3, Theorem 6.2, p. 52)**: the storage lower bound as stated (`ε > 2^(s−k)`), in the random oracle model, with an interactive online phase and online client randomness.
- **Plinko privacy and bounds** ([#5736](https://github.com/cslib-community/cslib-frontier/issues/5736)): Prove privacy of the full `plinkoScheme` (the hint-refresh argument and a reduction to forward iPRF security), the security half of Theorem 4.4 with pseudorandom multinomial samplers, and the Theorem 5.3 bounds, including the hint-load and failure-probability estimates.
- **Client-preprocessing single-server PIR**: Prove Wang–Ren Theorem 4.1 (Construction 4.2 instantiated with small-domain PRPs and expected-time bounds) and the generalized `ST = Ω(nw)` space-time trade-off lower bounds (Theorems B.1 and B.2 following Yeo 2023 and Corrigan-Gibbs–Henzinger–Kogan 2022).

### Concurrent and quantum security

- **NIST post-quantum portfolio** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987); machine witnesses [#5285](https://github.com/cslib-community/cslib-frontier/issues/5285)): Faithful protocols and exact concrete/asymptotic quantum reductions for ML-KEM/DSA, SLH/FN-DSA, HQC and active signatures.
  Concrete endpoints charge constructed-program size and online time, space, randomness, queries and circuits; asymptotic reductions certify uniform polynomial composition.
  Preserve sampling, abort, transform, failure, controller-layout/relocation and evolving-claim obligations; operational QPPT/QROM security remains open.
- **FAEST security** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987)): Formalize FAEST's BAVC ([#5302](https://github.com/cslib-community/cslib-frontier/issues/5302)) and QuickSilver components and prove its correctness and ROM/QROM security.
- **HQC security** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987)): Connect the finite Theorem 6.3 game hops to classical ([#5290](https://github.com/cslib-community/cslib-frontier/issues/5290)) and native ([#5281](https://github.com/cslib-community/cslib-frontier/issues/5281)) DQCSD assumptions with machine and circuit resource certificates.
  Then complete the sampler/seed model, numerical DFR, the published Theorem 6.4 salted Fujisaki–Okamoto/ROM and KEM endpoint ([#5279](https://github.com/cslib-community/cslib-frontier/issues/5279)), and the separate QROM upgrade ([#5280](https://github.com/cslib-community/cslib-frontier/issues/5280)).
- **SQIsign foundations** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987)): Extend its `B_{p,∞}` presentation with maximal orders and ideals, finite-field and elliptic-curve arithmetic, isogenies and Deuring, protocol algorithms, failure analysis, distribution switches, assumptions and security reductions.

- **SDitH foundations** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987)): Formalize Algorithm 6's byte PRG ([#5580](https://github.com/cslib-community/cslib-frontier/issues/5580)), the full GGM/BAVC tree, the PIOP, commitments, grinding and signing/verification.
  Then prove hardness, including the SD-to-RSD reduction ([#5332](https://github.com/cslib-community/cslib-frontier/issues/5332)), with machine costs, asymptotic family security and finite instantiated exact-constant bounds.

- **Concurrent composition**: Extend fixed-arity multi-session UC (`UC.Emulates.composeMulti`) to session ids created on first use and bounded by the environment's polynomial budget, joint-state UC (Canetti–Rabin Theorem 1, adaptive JUC, push-semantics `F̂`), global setup (GUC/EUC), and efficient-simulator/communication-model composition ([#6043](https://github.com/cslib-community/cslib-frontier/issues/6043)).
  Adaptive objectives: Canetti §7.1.1 write-once storage, coin exposure and per-party activation granularity (beyond the snapshot model), adaptive `Emulates.compose`, Canetti–Fischlin Theorems 8 and 11, non-malleability and static-malicious OT.
- **Quantum-secure cryptography** ([#4987](https://github.com/cslib-community/cslib-frontier/issues/4987)): Define uniform quantum-efficient distinguishers and computational indistinguishability with quantum side information, and justify security reductions for concrete constructions in that model.
  Connect the quantum-computation and lattice tracks through these adversary models.
  This includes quantum oracle access, the quantum random-oracle model, and extraction or rewinding under their precise hypotheses.
