/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CramerShoup.Scheme
public import CslibFrontier.Crypto.Computational.CramerShoup.Reductions
public import CslibFrontier.Crypto.Computational.DiffieHellman.EncodingBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.Encryption.CCA.Multi
import CslibFrontier.Crypto.Game.Statistical
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.StatisticalDistance
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.Negligible

/-!
# The Cramer–Shoup public-key encryption scheme and 1CCA security under DDH

This module completes the single-challenge adaptive chosen-ciphertext (**1CCA / IND-CCA2** and
**1CCA with associated data**, Definition 12.2, printed p. 468, and Section 12.7, Definition 12.7,
printed pp. 501–502) security proof for the **Multiplicative Cramer–Shoup public-key encryption
scheme** ($\mathcal{E}_{\mathrm{MCS}}$, [Boneh and Shoup, Exercise 12.27, printed
pp. 521–522][BonehShoup2023], over an arbitrary associated-data type `AD : Type` as well as the
associated-data-free specialization) defined in
`CslibFrontier.Crypto.Computational.CramerShoup.Scheme`
over a `PrimeOrderGroupFamily`, in the standard model under:
1. the Decisional Diffie–Hellman (`DDH`) assumption,
2. collision resistance (`CollisionResistantForOn`) of the $\mathbb{Z}_q$-valued hash family $H'$
   (`cramerShoupHashMod`) on its well-formed inputs, the encodings of
   $\mathbb{G}^3 \times \mathcal{D}$ (`isCramerShoupHashInput`), keyed by a hash key drawn at key
   generation in the native theorems, and
3. a positive group-order lower bound $m(n) > 0$ with $m(n) \le q$ and negligible inverse order
   $1 / m(n)$,

following the Games 0–6 proof template of [Boneh and Shoup, Section 12.5.3, Theorem 12.9 and
Remark 12.3, printed pp. 488–493][BonehShoup2023].

We first prove the concrete and asymptotic 1CCA bounds for the **ideal exact-uniform PMF** games
(`cramerShoupMsgCCA2Game`, `cramerShoupADGroupCCA2Game`, `cramerShoupADGroupIdealINDCCA2`,
`cramerShoupGroupCCA2Game`, `cramerShoupGroupIdealINDCCA2`, `cramerShoupADCCA2Game`,
`cramerShoupCCA2Game`), in which key and challenge exponents are drawn from
`PMF.uniformOfFintype (ZMod (F.order d))` and the `42 / 2 ^ n` dyadic loss arises solely from the
`sampleModNat` exponent draws inside the strict-PPT DDH and CRHF reductions. These
ideal-sampling results, the concrete bounds
(`advantage_cramerShoupMsgCCA2Game_le_ideal_of_honest_bounds`,
`advantage_cramerShoupMsgCCA2Game_le_ideal` and its four specializations) and the asymptotic
`DDH.cramerShoupMsgIdealINDCCA2` with its two group-element specializations, are steps, not the
cited result. We then bridge these ideal games to the
library's **native strict-PPT PKE 1CCA notions** (`Encryption.cca2ADGameOn`,
`Encryption.INDCCA2ADOn`, `Encryption.cca2GameOn`, and
`Encryption.INDCCA2On`) via `advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le` and
`advantage_cca2GameOn_cramerShoupGroupCCA2Game_le` (which account for the additional `8 / 2 ^ n`
per-bit `sampleModNat` approximation loss of `cramerShoupKeyGenProb`, `cramerShoupADEncryptProb`,
and `cramerShoupEncryptProb`), yielding `DDH.indcca2ADOn_cramerShoup_bitStringAD` (associated
data in $\{0,1\}^*$), `DDH.indcca2On_cramerShoup`, and (via `INDCCA2On.indcca2MultiOn`, the
batch-challenge step toward Theorem 12.1) batch-challenge multi-challenge CCA security
`DDH.indcca2MultiOn_cramerShoup`.

## Source Statements ([BonehShoup2023], Section 12.5.3 & Exercise 12.27)

Verbatim from [BonehShoup2023], Section 12.5.3 (printed pp. 489–492):

> **Theorem 12.9.** If the DDH assumption holds in $\mathbb{G}$, $\mathcal{E}_s$ is 1CCA secure,
> $H$ is a secure KDF, and $H'$ is collision resistant, then $\mathcal{E}_{\mathrm{CS}}$ is CCA
> secure.
>
> In particular, for every 1CCA adversary $\mathcal{A}$ that attacks $\mathcal{E}_{\mathrm{CS}}$ as
> in Definition 12.2, and makes at most $Q_d$ decryption queries, there exist a DDH adversary
> $\mathcal{B}_{\mathrm{ddh}}$ for $\mathbb{G}$ as in Attack Game 10.6, a 1CCA adversary
> $\mathcal{B}_s$ that attacks $\mathcal{E}_s$ as in Definition 9.6, a KDF adversary
> $\mathcal{B}_{\mathrm{kdf}}$ that attacks $H$ as in Attack Game 11.3, and a collision-finding
> adversary $\mathcal{B}_{\mathrm{cr}}$ that attacks $H'$ as in Attack Game 8.1, where
> $\mathcal{B}_{\mathrm{ddh}}, \mathcal{B}_s, \mathcal{B}_{\mathrm{kdf}}, \mathcal{B}_{\mathrm{cr}}$
> are elementary wrappers around $\mathcal{A}$, such that
> $$\text{1CCAadv}[\mathcal{A}, \mathcal{E}_{\mathrm{CS}}] \le
> 2\left(\text{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] +
> \text{KDFadv}[\mathcal{B}_{\mathrm{kdf}}, H] +
> \text{CRadv}[\mathcal{B}_{\mathrm{cr}}, H'] + \frac{Q_d + 1}{q}\right) +
> \text{1CCAadv}[\mathcal{B}_s, \mathcal{E}_s]. \quad (12.19)$$
> …
> **Game 1.** We replace the lines marked (2) and (3) in Fig. 12.3 as follows:
> $$(2) \qquad z \leftarrow f(v, w)$$
> $$(3) \qquad z' \leftarrow f'(v, w, \rho)$$
> Here, instead of using the auxiliary information that allows us to compute $f$ on $L_u$ and $f'$
> on $L_u \times \mathbb{Z}_q$, we compute them directly, using the secret key $\mathit{sk}$. This
> does not change the result of the computation in any way. Therefore,
> $$\Pr[W_1] = \Pr[W_0]. \quad (12.21)$$
> …
> **Game 2.** We replace the line marked (1) in Fig. 12.3 with
> $$(1) \qquad \gamma \xleftarrow{R} \mathbb{Z}_q$$
> …
> It is easy to see that
> $$|\Pr[W_1] - \Pr[W_2]| \le \text{DDHadv}[\mathcal{B}_{\mathrm{ddh}}, \mathbb{G}] \quad (12.22)$$
> for an efficient DDH adversary $\mathcal{B}_{\mathrm{ddh}}$ …
>
> **Game 3.** We replace the line marked (1) in Fig. 12.3 with
> $$(1) \qquad \gamma \xleftarrow{R} \mathbb{Z}_q \setminus \{\alpha\beta\}$$
> Since the statistical distance between the uniform distribution on all triples and the uniform
> distribution on all non-DH-triples is $1/q$ (see Exercise 10.7), it follows that:
> $$|\Pr[W_2] - \Pr[W_3]| \le \frac{1}{q}. \quad (12.23)$$
>
> **Game 4.** We now play our “CR card”. Let us define $\mathit{Coll}_{u,v}(\hat{v}, \hat{w})$ to
> be true if $(\hat{v}, \hat{w}) \ne (v, w)$ and $H'(\hat{v}, \hat{w}) = H'(v, w)$, and to be
> false, otherwise. In this game, we “widen” the rejection rule at line (5), replacing it with
> $$(5) \qquad \text{if } \mathit{Coll}_{u,v}(\hat{u}, \hat{v}) \text{ or }
>   z' \ne f'(\hat{v}, \hat{w}, \hat{\rho})$$
> Let $Z_4$ be the event that in Game 4, some decryption query, which would not have triggered the
> rejection rule of Game 3, does trigger the wider rejection rule in Game 4. Clearly, Games 3 and 4
> proceed identically unless event $Z_4$ occurs. By the Difference Lemma, we have
> $$|\Pr[W_3] - \Pr[W_4]| \le \Pr[Z_4]. \quad (12.24)$$
> It should be clear that
> $$\Pr[Z_4] \le \text{CRadv}[\mathcal{B}_{\mathrm{cr}}, H']. \quad (12.25)$$
> for an efficient collision-finding adversary $\mathcal{B}_{\mathrm{cr}}$. Indeed, adversary
> $\mathcal{B}_{\mathrm{cr}}$ just plays Game 4 and waits for the event $Z_4$ to happen.

Verbatim from [BonehShoup2023], Exercise 12.27 (printed pp. 521–522):
> … Show that $\mathcal{E}_{\mathrm{MCS}}$ is CCA secure, provided $H'$ is collision resistant and
> the DDH assumption holds for $\mathbb{G}$.

## Scope and Quantitative Adaptation

* **Associated data $\mathcal{D}$** ([BonehShoup2023], Section 12.7, Definition 12.7, printed
  pp. 501–502, and Exercise 12.27, printed pp. 521–522) and **single-challenge 1CCA
  (`Definition 12.2` / `Definition 12.7`)**.
* **Adaptation of Game 4 from $\mathcal{E}_{\mathrm{CS}}$ to $\mathcal{E}_{\mathrm{MCS}}$**: in
  Theorem 12.9 ($\mathcal{E}_{\mathrm{CS}}$), $H'$ hashes the pair $(v, w)$ and
  $\mathit{Coll}_{u,v}(\hat{v}, \hat{w})$ tests $(\hat{v}, \hat{w}) \ne (v, w) \land
  H'(\hat{v}, \hat{w}) = H'(v, w)$. In Multiplicative Cramer–Shoup $\mathcal{E}_{\mathrm{MCS}}$
  with associated data (Exercise 12.27, printed pp. 521–522), $H'$ hashes the 4-tuple
  $(v, w, e, d) \in \mathbb{G}^3 \times \mathcal{D}$ (`encBits4`), so the Game 4 collision
  predicate tests $(\hat{v}, \hat{w}, \hat{e}, \hat{d}) \ne (v, w, e, d) \land
  H'(\hat{v}, \hat{w}, \hat{e}, \hat{d}) = H'(v, w, e, d)$ (while Phase 2 decryption rejects the
  full challenge pair $((\hat{v}, \hat{w}, \hat{e}, \hat{z}'), \hat{d}) = ((v, w, e, z'), d)$).
* **Ideal exact-uniform PMF games vs. native `Encryption.INDCCA2ADOn` / `Encryption.INDCCA2On`**:
  `cramerShoupMsgCCA2Game`, `cramerShoupADGroupCCA2Game`, `cramerShoupADGroupIdealINDCCA2`,
  `cramerShoupGroupCCA2Game`, `cramerShoupGroupIdealINDCCA2`, `cramerShoupADCCA2Game` and
  `cramerShoupCCA2Game` are **ideal exact-uniform PMF** 1CCA experiments and security definitions,
  in which the challenger samples exponents from `PMF.uniformOfFintype (ZMod (F.order d))`. In
  `advantage_cramerShoupADGroupCCA2Game_le_ideal` and
  `advantage_cramerShoupGroupCCA2Game_le_ideal` (original quantitative adaptations of `(12.19)` to
  $\mathcal{E}_{\mathrm{MCS}}$ in the ideal games, with uniform strict-PPT reductions; steps, not
  the cited result), the two fixed-bit DDH
  distinguishers and two fixed-bit collision finders contribute `42 / 2 ^ n` from their internal
  `sampleModNat` exponent draws, and `(2 * Q₁ n + 2 * Q₂ n + 2) / m` combines the non-DH triple
  exclusion (`1 / m`) and the adaptive Lemma 12.8 bound (`(Q₁ n + Q₂ n) / m`) across `bit = false`
  and `bit = true`. The **native strict-PPT** security theorems
  `DDH.indcca2ADOn_cramerShoup_bitStringAD` and `DDH.indcca2On_cramerShoup` instantiate
  `Encryption.INDCCA2ADOn` and `Encryption.INDCCA2On`, bridging from `cramerShoupKeyGenProb`,
  `cramerShoupADEncryptProb`, and `cramerShoupEncryptProb` to the ideal games with an additional
  `8 / 2 ^ n` statistical loss per challenge bit (`16 / 2 ^ n` across both bits).
* **Keyed hash and fixed group family in the native theorems**: the ideal-game theorems
  (`DDH.cramerShoupADGroupIdealINDCCA2`, `DDH.cramerShoupGroupIdealINDCCA2`) hold for an arbitrary
  setup law `setup : ℕ → PMF F.Desc`, and their collision-resistance premise is stated for that
  law. For a point-mass law, that premise concerns a single fixed function at each security
  parameter.
  [BonehShoup2023], Section 8.1, printed p. 290, observe that for a fixed hash function an
  adversary that just outputs a collision exists, and avoid this by indexing the hash with a
  randomly chosen system parameter. The native scheme therefore draws a hash key at key
  generation and publishes it in
  the public key, as [CramerShoup2003], Section 6.1, Figure 1 does (and [CramerShoup1998],
  Section 3, which chooses the hash function from a universal one-way family at key generation).
  It is the scheme of `CramerShoup.Reductions` over `F.withKey`, whose parameters `(d, hk)` attach
  the hash key `hk` to the group `d`. The native theorems `DDH.indcca2ADOn_cramerShoup_bitStringAD`,
  `DDH.indcca2On_cramerShoup`, and `DDH.indcca2MultiOn_cramerShoup` fix a polynomial-time
  computable group family `d : ℕ → F.Desc` and a polynomial-time key length `keyLen`: the group at
  parameter `n` is `d n` and is not sampled, and the hash key is a uniform `keyLen n`-bit word.
  DDH is assumed for the point-mass setup `fun n => PMF.pure (d n)`; `DDH.withKey` transfers it to
  `F.withKey`. Collision resistance is assumed for the keyed family
  `F.withKey.cramerShoupHashMod H` under `withKeySetup (fun n => PMF.pure (d n)) keyLen` on its
  well-formed inputs, and its collision finders receive the group and the key. The hypotheses make
  `n ↦ F.order (d n)` a sequence of primes that is computable in polynomial time from the unary
  parameter and has negligible inverse.
* **Hash assumption on well-formed inputs**: Exercise 12.27 (printed p. 521) declares
  $H' : \mathbb{G}^3 \times \mathcal{D} \to \mathbb{Z}_q$, and the theorems assume collision
  resistance of the keyed hash only there: `CollisionResistantForOn` with the domain
  `isCramerShoupHashInput hasAD isElem`, which accepts exactly the encoded tuples
  `encodeCramerShoupTuple d v w e ad` (`isCramerShoupHashInput_iff`). With associated data the
  native theorem takes $\mathcal{D} = \{0,1\}^*$ (`encAD = encBits`), because decryption hashes
  whatever associated-data word it is given; a general $\mathcal{D}$, with collision resistance
  only on $\mathbb{G}^3 \times \mathcal{D}$, needs decryption to reject associated data outside
  $\mathcal{D}$ and is open (#5293). Without associated data, $\mathcal{D} = \{[]\}$. Collision
  resistance on all words (`CollisionResistantFor`) implies this premise
  (`CollisionResistantForOn.mono`) and is strictly stronger: a hash that is collision resistant on
  $\mathbb{G}^3 \times \mathcal{D}$ can be made to collide on malformed words. The
  collision finder outputs only collisions between the challenge's tuple and the tuple of a
  Phase 2 query that is well-formed; a colliding query whose tuple is malformed fails the
  group-membership checks that decryption performs (compare [BonehShoup2023], Remark 12.3,
  printed p. 493), so Games 2 and 3 answer it alike
  (`decodeCramerShoup_eq_none_of_isCramerShoupHashInput_eq_false`).
* **Hash assumption compared with the original papers**: [CramerShoup2003], Theorem 1
  (Section 6.2), needs only target collision resistance in the sense of its Section 5.1, where the
  target is a uniformly random tuple of group elements, and [CramerShoup1998], Theorem 1
  (Section 4), assumes a universal one-way family. Both are weaker than collision resistance, so
  these theorems use a stronger hash assumption than the original papers.
* **Group-order growth premise**: the asymptotic theorems assume a positive lower bound `m : ℕ → ℕ`
  on the group order `F.order` with `Negligible (fun n => (1 / m n : ℝ≥0))` so that the
  information-theoretic projective-hash and non-DH-triple terms `(2 * Q₁ n + 2 * Q₂ n + 2) / m n`
  are negligible for polynomial query bounds `Q₁, Q₂`.
-/

@[expose] public section

namespace Cslib.Crypto.PrimeOrderGroupFamily

open Probability Turing.MultiTapeTM ProjectiveHash Encryption Game
open scoped ENNReal NNReal

variable (F : PrimeOrderGroupFamily)


/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment for Multiplicative Cramer–Shoup
parameterized by `hasAD : Bool`, a message-to-group-word encoding `encodeMsg : F.Desc × Msg →
List Bool`, and an associated-data encoding `encodeAD : F.Desc × AD → List Bool`
([BonehShoup2023], Section 12.1, Attack Game 12.1 and Definition 12.2, printed pp. 467–468; Section
12.7, Definition 12.7, printed pp. 501–502; and Exercise 12.27, printed pp. 521–522; Game 0 of
Section 12.5.3, printed pp. 490–491). Key and challenge exponents are sampled from the exact uniform
distribution `PMF.uniformOfFintype (ZMod (F.order d))`. -/
noncomputable def cramerShoupMsgCCA2Game
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
  let pk := F.encodeCramerShoupPublicKeyValues d pkVal
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, csChoiceMsg₀ choice)
  let m₁ := encodeMsg (d, csChoiceMsg₁ choice)
  let ad := encodeAD (d, csChoiceAD choice)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let β ← PMF.uniformOfFintype (ZMod (F.order d))
    let ct := F.encodeCramerShoupEncrypt H d
      (F.encode d (csPkU pkVal), F.encode d (csPkH pkVal),
        F.encode d (csPkH₁ pkVal), F.encode d (csPkH₂ pkVal))
      m ad β.val
    let guessOut ← ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
      (adversary.guess n choice.2 ct)).run ())
    return guessOut.1
  else
    return false

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment with associated data for
Multiplicative Cramer–Shoup over encoded group-element messages (`Msg = List Bool`, `encodeMsg =
Prod.snd`) and associated-data type `AD` encoded via `encAD : AD ↪ List Bool`. -/
noncomputable abbrev cramerShoupADGroupCCA2Game
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : WordADCCA2Adversary AD)
    (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game true Prod.snd (fun p => encAD p.2) setup H isElem adversary bit n

/-- Ideal exact-uniform PMF single-challenge 1CCA security with associated data of Multiplicative
Cramer–Shoup over encoded group-element messages (`WordADCCA2Adversary AD`). -/
def cramerShoupADGroupIdealINDCCA2
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary false n)
    (fun adversary n => F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary true n)
    (WordADCCA2Adversary.IsPPT encAD)

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment for Multiplicative Cramer–Shoup
over encoded group-element messages (`Msg = List Bool`, `encodeMsg = Prod.snd`, associated-data-free
specialization `ad = []`), enforcing the group-membership challenge admissibility check
`isElem (d, m₀) && isElem (d, m₁)`. -/
noncomputable abbrev cramerShoupGroupCCA2Game
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : WordCCA2Adversary)
    (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game false Prod.snd (fun _ => []) setup H isElem adversary.toADUnit bit n

/-- Ideal exact-uniform PMF single-challenge 1CCA security of Multiplicative Cramer–Shoup over
encoded group-element messages (`WordCCA2Adversary`). -/
def cramerShoupGroupIdealINDCCA2
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) : Prop :=
  Game.Indistinguishable
    (fun adversary n => F.cramerShoupGroupCCA2Game setup H isElem adversary false n)
    (fun adversary n => F.cramerShoupGroupCCA2Game setup H isElem adversary true n)
    WordCCA2Adversary.IsPPT

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment with associated data for
Multiplicative Cramer–Shoup over single-bit messages (`Msg = Bool`, embedded into `F.Carrier d` via
`F.encodeBit`) and associated-data type `AD` encoded via `encAD : AD ↪ List Bool`. -/
noncomputable abbrev cramerShoupADCCA2Game
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : ADCCA2Adversary AD)
    (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game true (fun p => F.encodeBit p.1 p.2) (fun p => encAD p.2)
    setup H isElem adversary bit n

/-- The **ideal exact-uniform PMF** single-challenge 1CCA experiment for Multiplicative Cramer–Shoup
over single-bit messages (`Msg = Bool`, embedded into `F.Carrier d` via `F.encodeBit`,
associated-data-free specialization `ad = []`). -/
noncomputable abbrev cramerShoupCCA2Game
    (setup : ℕ → PMF F.Desc) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : CCA2Adversary) (bit : Bool) (n : ℕ) : Game :=
  F.cramerShoupMsgCCA2Game false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
    setup H isElem adversary.toADUnit bit n

/-- Shared challenge experiment for **Games 1 and 2** ([BonehShoup2023], Section 12.5.3, printed
p. 490) at fixed group `d` and triple exponents `(α, β, γ)`: sample the six secret-key exponents
uniformly from `ZMod (F.order d)` and compute the challenge ciphertext from
`(u, v, w) = (α • g, β • g, γ • g)` using the secret key via `encodeCramerShoupChallenge`. -/
noncomputable def cramerShoupChallengeGame
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ)
    (d : F.Desc) (α β γ : ZMod (F.order d)) : Game := do
  let U := PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← U; let τ ← U; let σ₁ ← U; let τ₁ ← U; let σ₂ ← U; let τ₂ ← U
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d)
  let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  let m₀ := encodeMsg (d, csChoiceMsg₀ choice)
  let m₁ := encodeMsg (d, csChoiceMsg₁ choice)
  let ad := encodeAD (d, csChoiceAD choice)
  if isElem (d, m₀) && isElem (d, m₁) then
    let m := if bit then m₁ else m₀
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    let guessOut ← ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct ad))
      (adversary.guess n choice.2 ct)).run ())
    return guessOut.1
  else
    return false

/-- **Game 1** ([BonehShoup2023], Section 12.5.3, printed p. 490, adapted to
$\mathcal{E}_{\mathrm{MCS}}$ with associated data): draw `(α, β)` and `sk` uniformly from `ZMod q`,
and compute the challenge ciphertext from `(v, w) = (β • g, (α * β) • g)` using the secret key via
`encodeCramerShoupChallenge`. -/
noncomputable def cramerShoupGame1
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  F.cramerShoupChallengeGame hasAD encodeMsg encodeAD H isElem adversary bit n d α β (α * β)

/-- **Game 0 = Game 1** ([BonehShoup2023], Section 12.5.3, equation (12.21), printed p. 490):
computing the challenge ciphertext from `(v, w) = (β • g, (α * β) • g)` using the secret key
produces the exact same distribution as public-key encryption. -/
theorem cramerShoupMsgCCA2Game_eq_game1
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary bit n =
      F.cramerShoupGame1 hasAD encodeMsg encodeAD setup H isElem adversary bit n := by
  simp only [cramerShoupMsgCCA2Game, cramerShoupGame1, cramerShoupChallengeGame,
    PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure, encodeCramerShoupPublicKey_encode, skNatOfZMod,
    csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂, csChoiceMsg₀, csChoiceMsg₁, csChoiceAD,
    ZMod.natCast_zmod_val, encodeCramerShoupEncrypt_publicKey_eq_challenge]
  refine congrArg _ (funext fun d => congrArg _ (funext fun α => ?_))
  iterate 7
    conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype (ZMod (F.order d)))]
    refine congrArg _ (funext fun _ => ?_)
  split_ifs <;> first | rfl | exact (PMF.bind_const _ _).symm

/-- **Game 2** ([BonehShoup2023], Section 12.5.3, printed p. 490, adapted to
$\mathcal{E}_{\mathrm{MCS}}$ with associated data): replace the Diffie–Hellman challenge pair
`(v, w) = (β • g, (α * β) • g)` by an independent random pair `(v, w) = (β • g, γ • g)` with
uniform `γ : ZMod (F.order d)`. -/
noncomputable def cramerShoupGame2
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  F.cramerShoupChallengeGame hasAD encodeMsg encodeAD H isElem adversary bit n d α β γ

private theorem advantage_eval_cramerShoupMsgToDDHDistinguisher_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ)
    (d : F.Desc) (α β γ : ZMod (F.order d)) :
    Game.advantage
      (ProbComp.eval
        (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit n d
          (α • F.generator d) (β • F.generator d) (γ • F.generator d)))
      (F.cramerShoupChallengeGame hasAD encodeMsg encodeAD H isElem adversary bit n d α β γ) ≤
      6 / 2 ^ n := by
  simp only [cramerShoupChallengeGame, cramerShoupMsgToDDHDistinguisher, pmf_norm]
  refine F.advantage_bind_sampleCramerShoupSK_le n d _ _ fun s t s₁ t₁ s₂ t₂ => ?_
  rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d α ((s, t), ((s₁, t₁), (s₂, t₂))),
    F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d ((s, t), ((s₁, t₁), (s₂, t₂)))]
  refine congrArg _ (funext fun choiceOut => ?_)
  by_cases h : (isElem (d, encodeMsg (d, csChoiceMsg₀ choiceOut.1)) &&
      isElem (d, encodeMsg (d, csChoiceMsg₁ choiceOut.1))) = true
  · simp only [h, ↓reduceIte, ProbComp.eval_bind, ProbComp.eval_pure]
    rw [F.encodeCramerShoupChallenge_eq_skNatOfZMod H d ((s, t), ((s₁, t₁), (s₂, t₂))),
      F.cramerShoupPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d ((s, t), ((s₁, t₁), (s₂, t₂)))]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

private theorem advantage_four_le (g₁ g₂ g₃ g₄ : Game) {n : ℕ}
    (h₁ : Game.advantage g₂ g₁ ≤ 6 / 2 ^ n) (h₂ : Game.advantage g₃ g₄ ≤ 6 / 2 ^ n) :
    Game.advantage g₁ g₄ ≤ Game.advantage g₂ g₃ + 12 / 2 ^ n := by
  game_trans [g₂, g₃] using [h₁, le_rfl, h₂]

/-- **Game 1 $\to$ Game 2 bound** ([BonehShoup2023], Section 12.5.3, equation (12.22), printed
p. 492): the distinguishing advantage between `cramerShoupGame1` and `cramerShoupGame2` is at
most the DDH advantage of `cramerShoupMsgToDDHDistinguisher` plus `12 / 2 ^ n` (six approximate
`sampleModNat` secret-key exponent draws in `ddhRealGame` and six in `ddhRandomGame`). -/
theorem advantage_cramerShoupGame1_game2_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.cramerShoupGame1 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n)
        (F.ddhRandomGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      12 / 2 ^ n := by
  refine advantage_four_le _ _ _ _ ?_ ?_
  · unfold ddhRealGame Game.withSetup cramerShoupGame1
    simp only [eval_ddhRealExperiment, PMF.monad_bind_eq_bind]
    peel_binds d α β
    exact F.advantage_eval_cramerShoupMsgToDDHDistinguisher_le hasAD encodeMsg encodeAD H isElem
      hmem adversary bit n d α β (α * β)
  · unfold ddhRandomGame Game.withSetup cramerShoupGame2
    simp only [eval_ddhRandomExperiment, PMF.monad_bind_eq_bind]
    peel_binds d α β γ
    exact F.advantage_eval_cramerShoupMsgToDDHDistinguisher_le hasAD encodeMsg encodeAD H isElem
      hmem adversary bit n d α β γ

private noncomputable def cramerShoupExactCollisionInner
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool) (adversary : ADCCA2AdversaryOf Msg AD)
    (bit : Bool) (n : ℕ) (d : F.Desc)
    (α β γ σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) : Game := do
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let u := F.encode d (α • F.generator d)
  let v := F.encode d (β • F.generator d)
  let w := F.encode d (γ • F.generator d)
  let pk := F.encodeCramerShoupPublicKey d u sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  let choice := choiceOut.1
  if isElem (d, encodeMsg (d, csChoiceMsg₀ choice)) &&
      isElem (d, encodeMsg (d, csChoiceMsg₁ choice)) then
    let m := if bit then encodeMsg (d, csChoiceMsg₁ choice) else encodeMsg (d, csChoiceMsg₀ choice)
    let ad := encodeAD (d, csChoiceAD choice)
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    runFinderOracle (F.cramerShoupCollisionPhase2Reply hasAD H isElem d sk ct ad)
      (fun req =>
        let q := splitCramerShoupQuery hasAD req
        F.isCramerShoupCollision H d q.1 q.2 ct ad &&
          F.isCramerShoupHashInput hasAD isElem d (extractCramerShoupTuple q.1 q.2))
      (fun req =>
        let q := splitCramerShoupQuery hasAD req
        extractCramerShoupTuple q.1 q.2)
      (adversary.guess n choice.2 ct) none
      (fun cand => isCollisionFor (F.cramerShoupHashMod H)
        (fun _ => F.isCramerShoupHashInput hasAD isElem) n d cand (extractCramerShoupTuple ct ad))
  else pure false

/-- Exact-exponent collision game matching the collision event between `cramerShoupGame2` and
`cramerShoupGame3`. -/
private noncomputable def cramerShoupExactCollisionGame
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) : Game := do
  let d ← setup n
  let α ← PMF.uniformOfFintype (ZMod (F.order d))
  let β ← PMF.uniformOfFintype (ZMod (F.order d))
  let γ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₁ ← PMF.uniformOfFintype (ZMod (F.order d))
  let σ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  let τ₂ ← PMF.uniformOfFintype (ZMod (F.order d))
  F.cramerShoupExactCollisionInner hasAD encodeMsg encodeAD H isElem adversary bit n d
    α β γ σ τ σ₁ τ₁ σ₂ τ₂

/-- The hashed tuple of a challenge ciphertext built from group elements is a well-formed hash
input. -/
private theorem isCramerShoupHashInput_extractCramerShoupTuple_challenge (hasAD : Bool)
    {isElem : F.Desc × List Bool → Bool}
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (H : F.Desc × List Bool → List Bool) (d : F.Desc) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ)))
    (v w : F.Carrier d) {m : List Bool} (hm : isElem (d, m) = true) {ad : List Bool}
    (had : hasAD = true ∨ ad = []) :
    F.isCramerShoupHashInput hasAD isElem d
      (extractCramerShoupTuple
        (F.encodeCramerShoupChallenge H d sk (F.encode d v) (F.encode d w) m ad) ad) = true := by
  obtain ⟨m, rfl⟩ := (hmem d m).mp hm
  simp only [F.encodeCramerShoupChallenge_encode, encodeCramerShoupCiphertext,
    extractCramerShoupTuple_encBits4]
  exact (F.isCramerShoupHashInput_iff hasAD hmem d _).mpr ⟨v, w, _, ad, had, rfl⟩

/-- The Game 2 $\to$ Game 3 difference is bounded by a collision between the challenge's hashed
tuple and the hashed tuple of a Phase 2 query that is a well-formed hash input. A colliding query
whose tuple is not well-formed gets the same reply in both games, since decryption rejects it
(`decodeCramerShoup_eq_none_of_isCramerShoupHashInput_eq_false`). -/
private theorem advantage_cramerShoupGame2_game3_le_exactCollision
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hAD : ∀ p, hasAD = true ∨ encodeAD p = [])
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.succProbability
        (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary
          bit n) := by
  unfold cramerShoupGame2 cramerShoupChallengeGame cramerShoupGame3 cramerShoupExactCollisionGame
    cramerShoupExactCollisionInner
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  refine advantage_bind_le_succProbability_bind (setup n) _ _ _ fun d => ?_
  iterate 10 refine bind_apply_le_add_bind_apply _ _ _ _ true fun _ => ?_
  rename_i _ β γ σ τ σ₁ τ₁ σ₂ τ₂ choiceOut
  by_cases h : (isElem (d, encodeMsg (d, csChoiceMsg₀ choiceOut.1)) &&
      isElem (d, encodeMsg (d, csChoiceMsg₁ choiceOut.1))) = true
  · simp only [h, ↓reduceIte]
    let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
    let v := F.encode d (β • F.generator d)
    let w := F.encode d (γ • F.generator d)
    let m := if bit then encodeMsg (d, csChoiceMsg₁ choiceOut.1)
      else encodeMsg (d, csChoiceMsg₀ choiceOut.1)
    let ad := encodeAD (d, csChoiceAD choiceOut.1)
    let ct := F.encodeCramerShoupChallenge H d sk v w m ad
    have hm : isElem (d, m) = true := by
      simp only [Bool.and_eq_true] at h
      cases bit <;> simp [m, h]
    have htarget : F.isCramerShoupHashInput hasAD isElem d (extractCramerShoupTuple ct ad) = true :=
      F.isCramerShoupHashInput_extractCramerShoupTuple_challenge hasAD hmem H d sk _ _ hm (hAD _)
    refine runStatelessOracle_le_runFinderOracle _ _ _ _ _
      (fun req hbad => ?_) (fun req hbad => ?_) _ _ _
    · have hq : hasAD = true ∨ (splitCramerShoupQuery hasAD req).2 = [] := by
        cases hasAD <;> simp [splitCramerShoupQuery]
      dsimp only [cramerShoupPhase2Reply, cramerShoupCollisionPhase2Reply] at hbad ⊢
      cases hcoll : F.isCramerShoupCollision H d (splitCramerShoupQuery hasAD req).1
          (splitCramerShoupQuery hasAD req).2 ct ad
      · simp only [Bool.or_false]
      · rw [hcoll, Bool.true_and] at hbad
        rw [F.decodeCramerShoup_eq_none_of_isCramerShoupHashInput_eq_false hasAD H isElem d sk _ _
          hq hbad]
        simp only [Bool.or_true, ↓reduceIte, encOption_none, ite_self]
    · rw [Bool.and_eq_true, F.isCramerShoupCollision_eq_isCollisionFor H n d,
        isCollisionFor_eq_true_iff] at hbad
      exact (isCollisionFor_eq_true_iff ..).mpr ⟨hbad.2, htarget, hbad.1.2.2⟩
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
    exact ⟨le_self_add, le_self_add⟩

private theorem succProbability_cramerShoupExactCollisionGame_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.succProbability
      (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H)
          (fun _ => F.isCramerShoupHashInput hasAD isElem)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      9 / 2 ^ n := by
  let C := F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit
  have hadv :
      Game.advantage
        (collisionGameFor setup (F.cramerShoupHashMod H)
          (fun _ => F.isCramerShoupHashInput hasAD isElem) C n)
        (F.cramerShoupExactCollisionGame hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      9 / 2 ^ n := by
    unfold collisionGameFor Game.withSetup collisionExperiment cramerShoupExactCollisionGame C
      cramerShoupMsgToCollisionFinder
    simp only [pmf_norm, F.smul_encode]
    peel_binds d
    let kSK (α β γ : ZMod (F.order d)) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) : Game :=
      let u := F.encode d (α • F.generator d)
      let v := F.encode d (β • F.generator d)
      let w := F.encode d (γ • F.generator d)
      let pk := F.encodeCramerShoupPublicKey d u sk
      (ProbComp.eval ((OracleComp.interpret
        (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
          (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
        (adversary.choose n pk)).run ())).bind fun choiceOut =>
        let choice := choiceOut.1
        (ProbComp.eval
          (if isElem (d, encodeMsg (d, csChoiceMsg₀ choice)) &&
              isElem (d, encodeMsg (d, csChoiceMsg₁ choice)) then
            let m := if bit then encodeMsg (d, csChoiceMsg₁ choice)
              else encodeMsg (d, csChoiceMsg₀ choice)
            let ad := encodeAD (d, csChoiceAD choice)
            let ct := F.encodeCramerShoupChallenge H d sk v w m ad
            ((OracleComp.interpret
              (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
                (F.cramerShoupCollisionPhase2Oracle hasAD H isElem d sk ct ad))
              (adversary.guess n choice.2 ct)).run none) >>= fun out =>
              let target := extractCramerShoupTuple ct ad
              pure (out.2.getD target, target)
          else pure ([], []))).bind fun pair =>
          PMF.pure
            (isCollisionFor (F.cramerShoupHashMod H)
              (fun _ => F.isCramerShoupHashInput hasAD isElem) n d pair.1 pair.2)
    have hstep1 := F.advantage_bind_sampleCramerShoupTripleExponents_le n d
      (fun α β γ => (ProbComp.eval (F.sampleCramerShoupSK n d)).bind (kSK α β γ))
    refine ((Game.advantage_triangle _ _ _).trans
      (add_le_add hstep1 (d := 6 / 2 ^ n) ?_)).trans_eq (by ring)
    peel_binds α β γ
    refine F.advantage_bind_sampleCramerShoupSK_le n d (kSK α β γ)
      (F.cramerShoupExactCollisionInner hasAD encodeMsg encodeAD H isElem adversary
        bit n d α β γ)
      fun s t s₁ t₁ s₂ t₂ => ?_
    dsimp only [kSK, cramerShoupExactCollisionInner]
    rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d α ((s, t), ((s₁, t₁), (s₂, t₂))),
      F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d
        ((s, t), ((s₁, t₁), (s₂, t₂)))]
    refine congrArg _ (funext fun choiceOut => ?_)
    by_cases h : (isElem (d, encodeMsg (d, csChoiceMsg₀ choiceOut.1)) &&
        isElem (d, encodeMsg (d, csChoiceMsg₁ choiceOut.1))) = true
    · simp only [pmf_norm, h, ↓reduceIte]
      rw [F.encodeCramerShoupChallenge_eq_skNatOfZMod H d
          ((s, t), ((s₁, t₁), (s₂, t₂))),
        F.cramerShoupCollisionPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d
          ((s, t), ((s₁, t₁), (s₂, t₂)))]
      unfold runFinderOracle cramerShoupCollisionPhase2Oracle
      refine congrArg _ (funext fun out => ?_)
      cases out.2 <;> simp
    · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure, PMF.pure_bind]
      rfl
  game_trans using [hadv]

/-- **Game 2 $\to$ Game 3 bound** (the collision-rejection hop into Game 4 of [BonehShoup2023],
Section 12.5.3, equations (12.24)–(12.25), printed p. 492, adapted to $\mathcal{E}_{\mathrm{MCS}}$
with associated data): if `isElem` accepts exactly the encodings of group elements and the
challenge's associated data is `[]` when `hasAD = false`, the distinguishing advantage between
`cramerShoupGame2` and `cramerShoupGame3` is bounded by the success probability of
`cramerShoupMsgToCollisionFinder` in finding a collision between well-formed hash inputs
(`isCramerShoupHashInput hasAD isElem`) plus `9 / 2 ^ n` (from the nine approximate
`sampleModNat` exponent draws in `cramerShoupMsgToCollisionFinder`). -/
theorem advantage_cramerShoupGame2_game3_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hAD : ∀ p, hasAD = true ∨ encodeAD p = [])
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      (F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H)
          (fun _ => F.isCramerShoupHashInput hasAD isElem)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      9 / 2 ^ n :=
  (F.advantage_cramerShoupGame2_game3_le_exactCollision
    hasAD encodeMsg encodeAD setup H isElem hmem hAD adversary bit n).trans
    (F.succProbability_cramerShoupExactCollisionGame_le
      hasAD encodeMsg encodeAD setup H isElem hmem adversary bit n)

/-! ### Concrete ideal-game 1CCA bounds (steps toward [BonehShoup2023], Theorem 12.9 & Ex. 12.27) -/

/-- **Combined Game 0 $\to$ Game 5 bound for a single challenge bit**: under honest query bounds
`(Q₁, Q₂)`, the distinguishing advantage between `cramerShoupMsgCCA2Game` and `cramerShoupGame5` is
at most the DDH advantage of `cramerShoupMsgToDDHDistinguisher` plus the collision-finding success
probability of `cramerShoupMsgToCollisionFinder` plus `(Q₁ + Q₂ + 1) / m + 21 / 2 ^ n`. -/
theorem advantage_cramerShoupMsgCCA2Game_game5_le
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hAD : ∀ p, hasAD = true ∨ encodeAD p = [])
    (adversary : ADCCA2AdversaryOf Msg AD) (bit : Bool) (n Q₁ Q₂ m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d)
    (hQ₁ : F.HonestPhase1QueryBound setup adversary n Q₁)
    (hQ₂ : F.HonestPhase2QueryBound hasAD encodeAD setup H isElem adversary n Q₂) :
    Game.advantage
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary bit n)
      (F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary bit n) ≤
      Game.advantage
        (F.ddhRealGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n)
        (F.ddhRandomGame setup
          (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      Game.succProbability
        (collisionGameFor setup (F.cramerShoupHashMod H)
          (fun _ => F.isCramerShoupHashInput hasAD isElem)
          (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary bit) n) +
      ((Q₁ + Q₂ + 1 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
      21 / 2 ^ n := by
  game_trans [
    F.cramerShoupGame1 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
    F.cramerShoupGame2 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
    F.cramerShoupGame3 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
    F.cramerShoupGame4 hasAD encodeMsg encodeAD setup H isElem adversary bit n]
    using [
      F.cramerShoupMsgCCA2Game_eq_game1 hasAD encodeMsg encodeAD setup H isElem adversary bit n,
      F.advantage_cramerShoupGame1_game2_le hasAD encodeMsg encodeAD setup H isElem hmem
        adversary bit n,
      F.advantage_cramerShoupGame2_game3_le hasAD encodeMsg encodeAD setup H isElem hmem hAD
        adversary bit n,
      F.advantage_cramerShoupGame3_game4_le hasAD encodeMsg encodeAD setup H isElem hmem
        adversary bit n Q₁ Q₂ m hm0 hm hQ₁ hQ₂,
      F.advantage_cramerShoupGame4_game5_le hasAD encodeMsg encodeAD setup H isElem hmem
        adversary bit n m hm0 hm]
  exact le_of_eq (by push_cast; ring)

/-- Concrete upper-bound expression for the two-run single-bit Theorem 12.9 / Exercise 12.27 1CCA
reduction ([BonehShoup2023], equation (12.19), printed p. 490): the DDH advantages of
`cramerShoupMsgToDDHDistinguisher` at `false` and `true`, the success probabilities of
`cramerShoupMsgToCollisionFinder` at `false` and `true` in finding collisions between well-formed
hash inputs (`isCramerShoupHashInput hasAD isElem`), and
`(2 * Q₁ + 2 * Q₂ + 2) / m + 42 / 2 ^ n`. -/
noncomputable abbrev cramerShoupCCA2Bound
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (adversary : ADCCA2AdversaryOf Msg AD) (n Q₁ Q₂ m : ℕ) : ℝ≥0 :=
  Game.advantage
    (F.ddhRealGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false) n)
    (F.ddhRandomGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary false) n) +
  Game.advantage
    (F.ddhRealGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true) n)
    (F.ddhRandomGame setup
      (F.cramerShoupMsgToDDHDistinguisher hasAD encodeMsg encodeAD H isElem adversary true) n) +
  Game.succProbability
    (collisionGameFor setup (F.cramerShoupHashMod H)
      (fun _ => F.isCramerShoupHashInput hasAD isElem)
      (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary false) n) +
  Game.succProbability
    (collisionGameFor setup (F.cramerShoupHashMod H)
      (fun _ => F.isCramerShoupHashInput hasAD isElem)
      (F.cramerShoupMsgToCollisionFinder hasAD encodeMsg encodeAD H isElem adversary true) n) +
  ((2 * Q₁ + 2 * Q₂ + 2 : ℕ) : ℝ≥0) / (m : ℝ≥0) +
  42 / 2 ^ n

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 12.9 and Exercise 12.27, not the cited
result: under honest query bounds `(Q₁, Q₂)`, the 1CCA advantage in `cramerShoupMsgCCA2Game`,
whose key and challenge exponents are drawn exactly uniformly at the `PMF` level, is at most
`cramerShoupCCA2Bound`, combining the Game 0 $\to$ Game 5 bounds for `bit = false` and
`bit = true` via `cramerShoupGame5_false_eq_true` (where `42 / 2 ^ n` is the reduction loss from
the `sampleModNat` exponent draws inside the reductions). -/
theorem advantage_cramerShoupMsgCCA2Game_le_ideal_of_honest_bounds
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool) (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hAD : ∀ p, hasAD = true ∨ encodeAD p = [])
    (adversary : ADCCA2AdversaryOf Msg AD) (n Q₁ Q₂ m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d)
    (hQ₁ : F.HonestPhase1QueryBound setup adversary n Q₁)
    (hQ₂ : F.HonestPhase2QueryBound hasAD encodeAD setup H isElem adversary n Q₂) :
    Game.advantage
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary false n)
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary true n) ≤
      F.cramerShoupCCA2Bound hasAD encodeMsg encodeAD setup H isElem adversary n Q₁ Q₂ m := by
  have hfalse := F.advantage_cramerShoupMsgCCA2Game_game5_le hasAD encodeMsg encodeAD setup H
    isElem hmem hAD adversary false n Q₁ Q₂ m hm0 hm hQ₁ hQ₂
  have htrue := F.advantage_cramerShoupMsgCCA2Game_game5_le hasAD encodeMsg encodeAD setup H
    isElem hmem hAD adversary true n Q₁ Q₂ m hm0 hm hQ₁ hQ₂
  game_trans [
    F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary false n,
    F.cramerShoupGame5 hasAD encodeMsg encodeAD setup H isElem adversary true n]
    using [hfalse,
      F.cramerShoupGame5_false_eq_true hasAD encodeMsg encodeAD setup H isElem adversary n,
      htrue]
  dsimp only [cramerShoupCCA2Bound]
  exact le_of_eq (by push_cast; ring)

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 12.9 and Exercise 12.27, not the cited
result: for any adversary with decryption-query bounds `(Q₁ n, Q₂ n)`, the 1CCA advantage at
parameter `n` in `cramerShoupMsgCCA2Game`, whose key and challenge exponents are drawn exactly
uniformly at the `PMF` level, is bounded by the DDH advantages of
`cramerShoupMsgToDDHDistinguisher` (`false` and `true`), the collision-finding success
probabilities of `cramerShoupMsgToCollisionFinder` (`false` and `true`), plus
`(2 * Q₁ n + 2 * Q₂ n + 2) / m + 42 / 2 ^ n`. The cited result for the strict-PPT scheme with
group-element messages is `DDH.indcca2ADOn_cramerShoup_bitStringAD` (with associated data in
$\{0,1\}^*$) and `DDH.indcca2On_cramerShoup`. -/
theorem advantage_cramerShoupMsgCCA2Game_le_ideal
    (hasAD : Bool) {Msg AD : Type} (encodeMsg : F.Desc × Msg → List Bool)
    (encodeAD : F.Desc × AD → List Bool)
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hAD : ∀ p, hasAD = true ∨ encodeAD p = [])
    (adversary : ADCCA2AdversaryOf Msg AD) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary false n)
      (F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary true n) ≤
      F.cramerShoupCCA2Bound hasAD encodeMsg encodeAD setup H isElem adversary
        n (Q₁ n) (Q₂ n) m :=
  F.advantage_cramerShoupMsgCCA2Game_le_ideal_of_honest_bounds hasAD encodeMsg encodeAD setup H
    isElem hmem hAD adversary n (Q₁ n) (Q₂ n) m hm0 hm
    (fun _ _ _ _ _ _ => hQ.1 n _)
    (fun _ _ _ _ _ _ _ _ _ _ _ _ _ => hQ.2 n _ _)

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 12.9 and Exercise 12.27, not the cited
result (after Section 12.5.3, Theorem 12.9 and Remark 12.3, printed pp. 488–493, Section 12.7,
printed pp. 501–502, and Exercise 12.27, printed pp. 521–522): an adaptation of the concrete
bound (12.19) to the ideal exact-uniform PMF 1CCA game `cramerShoupADGroupCCA2Game` for
Multiplicative Cramer–Shoup $\mathcal{E}_{\mathrm{MCS}}$ with associated data and group-element
messages, in the two-run single-bit reduction style (with `42 / 2 ^ n` from the approximate
`sampleModNat` exponent draws in the reductions). The cited result for the strict-PPT scheme, with
associated data in $\{0,1\}^*$ (`encAD = encBits`), is `DDH.indcca2ADOn_cramerShoup_bitStringAD`,
which reaches this game through `advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le`. -/
theorem advantage_cramerShoupADGroupCCA2Game_le_ideal
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : WordADCCA2Adversary AD) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary false n)
      (F.cramerShoupADGroupCCA2Game encAD setup H isElem adversary true n) ≤
      F.cramerShoupCCA2Bound true Prod.snd (fun p => encAD p.2) setup H isElem adversary
        n (Q₁ n) (Q₂ n) m :=
  F.advantage_cramerShoupMsgCCA2Game_le_ideal true Prod.snd (fun p => encAD p.2) setup H isElem
    hmem (fun _ => .inl rfl) adversary Q₁ Q₂ hQ n m hm0 hm

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 12.9 and Exercise 12.27, not the cited
result (after Section 12.5.3, Theorem 12.9 and Remark 12.3, printed pp. 488–493, and
Exercise 12.27, printed pp. 521–522): an original adaptation of the concrete bound (12.19) to the
ideal exact-uniform PMF 1CCA game `cramerShoupGroupCCA2Game` for Multiplicative Cramer–Shoup
$\mathcal{E}_{\mathrm{MCS}}$ with group-element messages, in the two-run single-bit reduction style
(with `42 / 2 ^ n` from the approximate `sampleModNat` exponent draws in the reductions). The cited
result for the strict-PPT scheme is `DDH.indcca2On_cramerShoup`, which reaches this game through
`advantage_cca2GameOn_cramerShoupGroupCCA2Game_le`. -/
theorem advantage_cramerShoupGroupCCA2Game_le_ideal
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : WordCCA2Adversary) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupGroupCCA2Game setup H isElem adversary false n)
      (F.cramerShoupGroupCCA2Game setup H isElem adversary true n) ≤
      F.cramerShoupCCA2Bound false Prod.snd (fun _ => []) setup H isElem adversary.toADUnit
        n (Q₁ n) (Q₂ n) m :=
  F.advantage_cramerShoupMsgCCA2Game_le_ideal false Prod.snd (fun _ => []) setup H isElem hmem
    (fun _ => .inr rfl) adversary.toADUnit Q₁ Q₂ hQ.toADUnit n m hm0 hm

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 12.9 and Exercise 12.27, not the cited
result: the bound of `advantage_cramerShoupMsgCCA2Game_le_ideal` for single-bit messages with
associated data, in the ideal exact-uniform PMF game `cramerShoupADCCA2Game`. -/
theorem advantage_cramerShoupADCCA2Game_le_ideal
    {AD : Type} (encAD : AD ↪ List Bool)
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : ADCCA2Adversary AD) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupADCCA2Game encAD setup H isElem adversary false n)
      (F.cramerShoupADCCA2Game encAD setup H isElem adversary true n) ≤
      F.cramerShoupCCA2Bound true (fun p => F.encodeBit p.1 p.2) (fun p => encAD p.2) setup H
        isElem adversary n (Q₁ n) (Q₂ n) m :=
  F.advantage_cramerShoupMsgCCA2Game_le_ideal true (fun p => F.encodeBit p.1 p.2)
    (fun p => encAD p.2) setup H isElem hmem (fun _ => .inl rfl) adversary Q₁ Q₂ hQ n m hm0 hm

/-- Ideal-sampling step toward [BonehShoup2023], Theorem 12.9 and Exercise 12.27, not the cited
result: the bound of `advantage_cramerShoupMsgCCA2Game_le_ideal` for single-bit messages, in the
ideal exact-uniform PMF game `cramerShoupCCA2Game`. -/
theorem advantage_cramerShoupCCA2Game_le_ideal
    (setup : ℕ → PMF F.Desc)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (adversary : CCA2Adversary) (Q₁ Q₂ : ℕ → ℕ)
    (hQ : adversary.IsQueryBounded Q₁ Q₂) (n m : ℕ)
    (hm0 : 0 < m) (hm : ∀ d ∈ (setup n).support, m ≤ F.order d) :
    Game.advantage
      (F.cramerShoupCCA2Game setup H isElem adversary false n)
      (F.cramerShoupCCA2Game setup H isElem adversary true n) ≤
      F.cramerShoupCCA2Bound false (fun p => F.encodeBit p.1 p.2) (fun _ => []) setup H
        isElem adversary.toADUnit n (Q₁ n) (Q₂ n) m :=
  F.advantage_cramerShoupMsgCCA2Game_le_ideal false (fun p => F.encodeBit p.1 p.2) (fun _ => [])
    setup H isElem hmem (fun _ => .inr rfl) adversary.toADUnit Q₁ Q₂ hQ.toADUnit n m hm0 hm

/-! ### Polynomial length bounds and asymptotic 1CCA security -/

private theorem length_encBits4_encode_le {d : F.Desc} {B : ℕ}
    (hB : ∀ x : F.Carrier d, (F.encode d x).length ≤ B)
    (x₁ x₂ x₃ x₄ : F.Carrier d) :
    (encBits4 (F.encode d x₁, F.encode d x₂, F.encode d x₃, F.encode d x₄)).length ≤
      22 * B + 14 := by
  have h1 := hB x₁; have h2 := hB x₂; have h3 := hB x₃; have h4 := hB x₄
  enc_len [encBits4]

private theorem length_encodeCramerShoupPublicKey_le {d : F.Desc} {B : ℕ}
    (hB : ∀ x : F.Carrier d, (F.encode d x).length ≤ B)
    (α : ZMod (F.order d)) (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk).length ≤
      2 * (F.encDesc d).length + 44 * B + 30 := by
  rw [F.encodeCramerShoupPublicKey_encode]
  generalize F.cramerShoupPublicKey d α _ _ _ _ _ _ = pk
  unfold encodeCramerShoupPublicKeyValues
  have h4 := F.length_encBits4_encode_le hB (csPkU pk) (csPkH pk) (csPkH₁ pk) (csPkH₂ pk)
  enc_len

/-- Ideal-sampling step toward `DDH.indcca2ADOn_cramerShoup_bitStringAD` and
`DDH.indcca2On_cramerShoup`, not
the cited result: asymptotic 1CCA security of Multiplicative Cramer–Shoup for general message and
associated-data encodings in the ideal exact-uniform PMF game (after [BonehShoup2023],
Theorem 12.9, Section 12.7 & Exercise 12.27, printed pp. 488–493, 501–502, 521–522). If DDH holds
for an arbitrary setup law `setup`, `cramerShoupHashMod H` is collision-resistant for `setup` on
its well-formed inputs `isCramerShoupHashInput hasAD isElem`, every supported group at parameter
`n` has order at least `m n > 0` with `1 / m n` negligible, and supported group descriptions have
polynomially bounded bit-length, then `cramerShoupMsgCCA2Game`, whose exponents are drawn exactly
uniformly, is indistinguishable between `bit = false` and `bit = true` against all strict oracle
PPT adversaries. The premise `hAD` says that without associated data (`hasAD = false`) the
challenge's associated-data word is `[]`, as in every specialization, so that the challenge's
hashed tuple is well-formed. -/
theorem DDH.cramerShoupMsgIdealINDCCA2
    {F : PrimeOrderGroupFamily}
    (hasAD : Bool)
    {Msg AD : Type} {encMsg : Msg ↪ List Bool} {encAD : AD ↪ List Bool}
    {encodeMsg : F.Desc × Msg → List Bool}
    {encodeAD : F.Desc × AD → List Bool}
    (hencMsg : ComputableInPolyTime encodeMsg (encPair F.encDesc encMsg) encBits)
    (hencAD : ComputableInPolyTime encodeAD (encPair F.encDesc encAD) encBits)
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hAD : ∀ p, hasAD = true ∨ encodeAD p = [])
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantForOn F.encDesc setup (F.cramerShoupHashMod H)
      (fun _ => F.isCramerShoupHashInput hasAD isElem))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    Game.Indistinguishable
      (fun adversary n =>
        F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary false n)
      (fun adversary n =>
        F.cramerShoupMsgCCA2Game hasAD encodeMsg encodeAD setup H isElem adversary true n)
      (ADCCA2AdversaryOf.IsPPT encMsg encAD) := by
  intro adversary hA
  obtain ⟨cd, kd, hdesc_le⟩ := hdesc
  obtain ⟨ce, ke, henc_le⟩ := F.exists_length_encode_le
  obtain ⟨c₁, d₁, c₂, d₂, cs, ds, hQ₁_raw, hQ₂_raw, hstate⟩ := hA.query_bounds
  let Ld (n : ℕ) : ℕ := cd * (n + 1) ^ kd
  let B (n : ℕ) : ℕ := ce * (Ld n + 1) ^ ke
  let Lpk (n : ℕ) : ℕ := 2 * Ld n + 44 * B n + 30
  let Lct (n : ℕ) : ℕ := 22 * B n + 14
  let Lst (n : ℕ) : ℕ := cs * (n + Lpk n + 2) ^ ds
  let Q₁ (n : ℕ) : ℕ := c₁ * (n + Lpk n + 2) ^ d₁
  let Q₂ (n : ℕ) : ℕ := c₂ * (n + Lst n + Lct n + 2) ^ d₂
  have hddh (bit : Bool) :=
    hDDH _ (F.isPPT_cramerShoupMsgToDDHDistinguisher hasAD hencMsg hencAD hH hisElem hA bit)
  have hcr (bit : Bool) :=
    hCR.negligible _
      (F.isPPTOn_cramerShoupMsgToCollisionFinder hasAD hencMsg hencAD hH hisElem hA bit)
  negligible [cramerShoupCCA2Bound] using fun n => by
    have hB_le : ∀ {d}, d ∈ (setup n).support → ∀ x : F.Carrier d, (F.encode d x).length ≤ B n :=
      fun hd x => (henc_le _ x).trans (by have := hdesc_le n _ hd; dsimp only [B]; gcongr)
    have hpk_le : ∀ {d}, d ∈ (setup n).support → ∀ α δ δ₁ δ₂,
        (F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d))
          (F.skNatOfZMod d δ 0 δ₁ 0 δ₂ 0)).length ≤ Lpk n :=
      fun hd α _ _ _ => (F.length_encodeCramerShoupPublicKey_le (hB_le hd) α _).trans
        (by have := hdesc_le n _ hd; dsimp only [Lpk]; gcongr)
    refine F.advantage_cramerShoupMsgCCA2Game_le_ideal_of_honest_bounds hasAD encodeMsg encodeAD
      setup H isElem hmem hAD adversary n (Q₁ n) (Q₂ n) (m n) (hm0 n) (hm n)
      (fun d hd α δ δ₁ δ₂ => by
        refine (hQ₁_raw n _).mono ?_
        have := hpk_le hd α δ δ₁ δ₂; dsimp only [Q₁]; gcongr)
      ?_
    intro d hd α β γ δ τ δ₁ δ₂ ξ choiceOut hchoice mElem
    rw [ProbOracleComp.eval_run_interpret_eq_runWith] at hchoice
    have hpk := hpk_le hd α δ δ₁ δ₂
    have hst : (csChoiceState choiceOut.1).length ≤ Lst n :=
      (hstate n _ Unit _ () choiceOut.2 choiceOut.1 hchoice).trans (by dsimp only [Lst]; gcongr)
    refine (hQ₂_raw n (csChoiceState choiceOut.1) _).mono ?_
    dsimp only [Q₂, Lct]
    gcongr
    exact F.length_encBits4_encode_le (hB_le hd) _ _ _ _

/-- Ideal-sampling step toward `DDH.indcca2ADOn_cramerShoup_bitStringAD`, not the cited result
(after [BonehShoup2023], Theorem 12.9 & Exercise 12.27): for group-element messages with associated
data `AD`, Multiplicative Cramer–Shoup satisfies the ideal exact-uniform PMF 1CCA notion
`cramerShoupADGroupIdealINDCCA2` under DDH, collision resistance of `cramerShoupHashMod H` on
`isCramerShoupHashInput true isElem`, a positive group-order lower bound `m n > 0` with `1 / m n`
negligible, and polynomially bounded group description bit-length, for an arbitrary setup law.
The hash premise covers every associated-data word, not only those in the range of `encAD`,
because decryption hashes any associated-data word; it is the exercise's premise only when
`encAD` is onto, as `encBits` is. -/
theorem DDH.cramerShoupADGroupIdealINDCCA2
    {F : PrimeOrderGroupFamily}
    {AD : Type} (encAD : AD ↪ List Bool)
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantForOn F.encDesc setup (F.cramerShoupHashMod H)
      (fun _ => F.isCramerShoupHashInput true isElem))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    F.cramerShoupADGroupIdealINDCCA2 encAD setup H isElem :=
  hDDH.cramerShoupMsgIdealINDCCA2 true (encodeAD := fun p => encAD p.2)
    (ComputableInPolyTime.snd F.encDesc encBits)
    ((ComputableInPolyTime.of_eq (encIn := encAD) (encOut := encBits)
      (fun _ => rfl)).comp (ComputableInPolyTime.snd F.encDesc encAD))
    hH hisElem hmem (fun _ => .inl rfl) hCR hm0 hm hinv hdesc

/-- Ideal-sampling step toward `DDH.indcca2On_cramerShoup`, not the cited result (after
[BonehShoup2023], Theorem 12.9 & Exercise 12.27): for group-element messages, Multiplicative
Cramer–Shoup satisfies the ideal exact-uniform PMF 1CCA notion `cramerShoupGroupIdealINDCCA2` under
DDH, collision resistance of `cramerShoupHashMod H` on its well-formed inputs
`isCramerShoupHashInput false isElem`, a positive group-order lower bound `m n > 0` with
`1 / m n` negligible, and polynomially bounded group description bit-length, for an arbitrary
setup law. -/
theorem DDH.cramerShoupGroupIdealINDCCA2
    {F : PrimeOrderGroupFamily}
    {setup : ℕ → PMF F.Desc}
    {H : F.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    (hH : ComputableInPolyTime H (encPair F.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH setup)
    (hCR : CollisionResistantForOn F.encDesc setup (F.cramerShoupHashMod H)
      (fun _ => F.isCramerShoupHashInput false isElem))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, ∀ d ∈ (setup n).support, m n ≤ F.order d)
    (hinv : Negligible fun n => (1 / m n : ℝ≥0))
    (hdesc : ∃ c k : ℕ, ∀ n, ∀ d ∈ (setup n).support,
      (F.encDesc d).length ≤ c * (n + 1) ^ k) :
    F.cramerShoupGroupIdealINDCCA2 setup H isElem :=
  fun adversary hA =>
    hDDH.cramerShoupMsgIdealINDCCA2 false (encodeAD := fun _ : F.Desc × Unit => [])
      (ComputableInPolyTime.snd F.encDesc encBits)
      (.const (encIn := encPair F.encDesc encUnit) [])
      hH hisElem hmem (fun _ => .inr rfl) hCR hm0 hm hinv hdesc adversary.toADUnit hA.toADUnit

/-! ### `Encryption.cca2ADGameOn`, `Encryption.INDCCA2ADOn`, `Encryption.cca2GameOn`, and
`Encryption.INDCCA2On` instantiations -/

private theorem advantage_four_le_eight (g₁ g₂ g₃ g₄ : Game) {n : ℕ}
    (h₁ : Game.advantage g₁ g₂ ≤ 1 / 2 ^ n)
    (h₂ : Game.advantage g₂ g₃ ≤ 6 / 2 ^ n)
    (h₃ : Game.advantage g₃ g₄ ≤ 1 / 2 ^ n) :
    Game.advantage g₁ g₄ ≤ 8 / 2 ^ n := by
  game_trans [g₂, g₃] using [h₁, h₂, h₃]

private theorem eval_run_interpret_map_bind
    {α β γ State : Type}
    (oracle : Unit × List Bool → StateT State ProbComp (List Bool))
    (f : α → β) (oa : WordOracleComp Unit α) (s : State)
    (k : β × State → PMF γ) :
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      (f <$> oa)).run s)).bind k =
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m)) oracle)
      oa).run s)).bind (fun p => k (f p.1, p.2)) := by
  rw [OracleComp.interpret_map, StateT.run_map]
  simp only [pmf_norm, ← bind_pure_comp]

private noncomputable def cramerShoupCCA2InnerB
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d))
    (choiceOut : (((List Bool × List Bool) × AD) × List Bool) × Unit)
    (β : ZMod (F.order d)) : Game :=
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let pkVal := F.cramerShoupPublicKey d α σ τ σ₁ τ₁ σ₂ τ₂
  let m := if bit then csChoiceMsg₁ choiceOut.1 else csChoiceMsg₀ choiceOut.1
  let adBits := encodeAD (d, csChoiceAD choiceOut.1)
  let ct := F.encodeCramerShoupEncrypt H d
    (F.encode d (csPkU pkVal), F.encode d (csPkH pkVal),
      F.encode d (csPkH₁ pkVal), F.encode d (csPkH₂ pkVal)) m adBits β.val
  (ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct adBits))
    (adversary.guess n (csChoiceState choiceOut.1) ct)).run ())).bind
    (fun guessOut => PMF.pure guessOut.1)

private noncomputable def cramerShoupCCA2InnerSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (α σ τ σ₁ τ₁ σ₂ τ₂ : ZMod (F.order d)) (useExactB : Bool) : Game := do
  let sk := F.skNatOfZMod d σ τ σ₁ τ₁ σ₂ τ₂
  let pk := F.encodeCramerShoupPublicKey d (F.encode d (α • F.generator d)) sk
  let choiceOut ← ProbComp.eval ((OracleComp.interpret
    (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
      (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
    (adversary.choose n pk)).run ())
  if isElem (d, csChoiceMsg₀ choiceOut.1) && isElem (d, csChoiceMsg₁ choiceOut.1) then
    if useExactB then
      let β ← PMF.uniformOfFintype (ZMod (F.order d))
      F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
        α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut β
    else
      let b ← ProbComp.eval (F.sampleExp n d)
      F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
        α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut (b : ZMod (F.order d))
  else
    pure false

private noncomputable def cramerShoupCCA2SampledSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (α : ZMod (F.order d)) : Game :=
  (ProbComp.eval (F.sampleCramerShoupSK n d)).bind fun sk =>
    F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n α
      ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
      ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
      ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d)) false

private noncomputable def cramerShoupCCA2UniformSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ)
    (useExactB : Bool) : Game := do
  let U := PMF.uniformOfFintype (ZMod (F.order d))
  let α ← U; let σ ← U; let τ ← U; let σ₁ ← U; let τ₁ ← U; let σ₂ ← U; let τ₂ ← U
  F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
    α σ τ σ₁ τ₁ σ₂ τ₂ useExactB

private theorem advantage_cramerShoupCCA2InnerSK_le
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ) :
    Game.advantage
      ((ProbComp.eval (F.sampleExp n d)).bind fun a =>
        F.cramerShoupCCA2SampledSK hasAD encodeAD H isElem d adversary bit n
          (a : ZMod (F.order d)))
      (F.cramerShoupCCA2UniformSK hasAD encodeAD H isElem d adversary bit n true) ≤
      8 / 2 ^ n := by
  refine advantage_four_le_eight _
    ((PMF.uniformOfFintype (ZMod (F.order d))).bind
      (F.cramerShoupCCA2SampledSK hasAD encodeAD H isElem d adversary bit n))
    (F.cramerShoupCCA2UniformSK hasAD encodeAD H isElem d adversary bit n false) _
    (F.advantage_bind_sampleExp_le n d
      (F.cramerShoupCCA2SampledSK hasAD encodeAD H isElem d adversary bit n))
    (by
      simp only [cramerShoupCCA2UniformSK, PMF.monad_bind_eq_bind]
      exact advantage_bind_le_nnreal _ _ _ fun α =>
        F.advantage_bind_sampleCramerShoupSK_le n d _ (fun σ τ σ₁ τ₁ σ₂ τ₂ =>
          F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
            α σ τ σ₁ τ₁ σ₂ τ₂ false) (fun _ _ _ _ _ _ => rfl)) ?_
  simp only [cramerShoupCCA2UniformSK, PMF.monad_bind_eq_bind]
  peel_binds α σ τ σ₁ τ₁ σ₂ τ₂
  dsimp only [cramerShoupCCA2InnerSK]
  peel_binds choiceOut
  by_cases h : (isElem (d, csChoiceMsg₀ choiceOut.1) && isElem (d, csChoiceMsg₁ choiceOut.1)) = true
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    exact F.advantage_bind_sampleExp_le n d
      (F.cramerShoupCCA2InnerB hasAD encodeAD H isElem d adversary bit n
        α σ τ σ₁ τ₁ σ₂ τ₂ choiceOut)
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Game.advantage_self, zero_le]

private theorem cramerShoupMsgCCA2Game_eq_bind_innerSK
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool) (isElem : F.Desc × List Bool → Bool)
    (setup : ℕ → PMF F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n : ℕ) :
    F.cramerShoupMsgCCA2Game hasAD (fun p => p.2) encodeAD setup H isElem adversary bit n =
    (setup n).bind fun d =>
      F.cramerShoupCCA2UniformSK hasAD encodeAD H isElem d adversary bit n true := by
  simp only [pmf_norm, cramerShoupMsgCCA2Game, cramerShoupCCA2UniformSK]
  iterate 8 refine congrArg _ (funext fun _ => ?_)
  simp only [cramerShoupCCA2InnerSK, cramerShoupCCA2InnerB, PMF.monad_bind_eq_bind,
    PMF.monad_pure_eq_pure, ↓reduceIte,
    encodeCramerShoupPublicKey_encode, skNatOfZMod,
    csPkU, csPkH, csPkH₁, csPkH₂, csSkS, csSkT, csSkS₁, csSkT₁, csSkS₂, csSkT₂,
    csChoiceMsg₀, csChoiceMsg₁, csChoiceAD, ZMod.natCast_zmod_val]

private theorem cramerShoupCCA2InnerSK_false_eq
    (hasAD : Bool) {AD : Type} (encodeAD : F.Desc × AD → List Bool)
    (H : F.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : F.Desc) (adversary : WordADCCA2Adversary AD) (bit : Bool) (n a : ℕ)
    (sk : (ℕ × ℕ) × ((ℕ × ℕ) × (ℕ × ℕ))) :
    let pk := F.encodeCramerShoupPublicKey d
      (F.encode d ((a : ZMod (F.order d)) • F.generator d)) sk
    (ProbComp.eval ((OracleComp.interpret
      (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
        (F.cramerShoupPhase1Oracle hasAD H isElem d sk))
      (adversary.choose n pk)).run ())).bind (fun choiceOut =>
        ProbComp.eval
          (if (isElem (d, csChoiceMsg₀ choiceOut.1) &&
              isElem (d, csChoiceMsg₁ choiceOut.1)) = true then do
            let b ← F.sampleExp n d
            let ct := F.encodeCramerShoupEncrypt H d (decodeBits4 (dropFrame pk))
              (if bit then csChoiceMsg₁ choiceOut.1 else csChoiceMsg₀ choiceOut.1)
              (encodeAD (d, csChoiceAD choiceOut.1)) b
            let guessOut ← (OracleComp.interpret
              (OracleComp.sumHandler (fun m => StateT.lift (ProbComp.unifFin m))
                (F.cramerShoupPhase2Oracle hasAD H isElem d sk ct
                  (encodeAD (d, csChoiceAD choiceOut.1))))
              (adversary.guess n (csChoiceState choiceOut.1) ct)).run ()
            return guessOut.1
          else
            return false)) =
    F.cramerShoupCCA2InnerSK hasAD encodeAD H isElem d adversary bit n
      (a : ZMod (F.order d))
      ((csSkS sk : ℕ) : ZMod (F.order d)) ((csSkT sk : ℕ) : ZMod (F.order d))
      ((csSkS₁ sk : ℕ) : ZMod (F.order d)) ((csSkT₁ sk : ℕ) : ZMod (F.order d))
      ((csSkS₂ sk : ℕ) : ZMod (F.order d)) ((csSkT₂ sk : ℕ) : ZMod (F.order d)) false := by
  dsimp only [cramerShoupCCA2InnerSK]
  simp only [PMF.monad_bind_eq_bind, PMF.monad_pure_eq_pure]
  rw [F.encodeCramerShoupPublicKey_eq_skNatOfZMod d (a : ZMod (F.order d)) sk,
    F.cramerShoupPhase1Oracle_eq_skNatOfZMod hasAD H isElem hmem d sk]
  refine congrArg _ (funext fun choiceOut => ?_)
  by_cases h : (isElem (d, csChoiceMsg₀ choiceOut.1) && isElem (d, csChoiceMsg₁ choiceOut.1)) = true
  · simp only [pmf_norm, h, ↓reduceIte, Bool.false_eq_true,
      F.decodeBits4_dropFrame_encodeCramerShoupPublicKey, cramerShoupCCA2InnerB]
    refine congrArg _ (funext fun b => ?_)
    rw [F.encodeCramerShoupEncrypt_skNatOfZMod,
      F.cramerShoupPhase2Oracle_eq_skNatOfZMod hasAD H isElem hmem d sk]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, ProbComp.eval_pure]

private theorem exists_length_encDesc_withKeySetup_le {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary) :
    ∃ c k : ℕ, ∀ n, ∀ p ∈ (F.withKeySetup (fun n => PMF.pure (d n)) keyLen n).support,
      (F.withKey.encDesc p).length ≤ c * (n + 1) ^ k := by
  obtain ⟨c₁, k₁, h₁⟩ := hd.polyBounded_length.exists_le
  obtain ⟨c₂, k₂, h₂⟩ := hkeyLen.polyBounded_length.exists_le
  refine ⟨2 * c₁ + 1 + c₂, k₁ + k₂, fun n p hp => ?_⟩
  obtain ⟨hd', hk⟩ := F.mem_support_withKeySetup (d := p.1) (k := p.2) hp
  rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
  have p₁ : (F.encDesc (d n)).length ≤ c₁ * (n + 1) ^ (k₁ + k₂) :=
    Nat.le_trans (by simpa only [encUnary_apply, List.length_replicate] using h₁ n)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_add_right _ _)))
  have p₂ : keyLen n ≤ c₂ * (n + 1) ^ (k₁ + k₂) :=
    Nat.le_trans (by simpa only [encUnary_apply, List.length_replicate] using h₂ n)
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_add_left _ _)))
  change (encPair F.encDesc encBits p).length ≤ _
  rw [length_encPair, encBits_apply, hd', hk]
  nlinarith [Nat.one_le_pow (k₁ + k₂) (n + 1) (Nat.succ_pos n)]

private theorem order_withKeySetup_ge {d : ℕ → F.Desc} {keyLen : ℕ → ℕ} {m : ℕ → ℕ}
    (hm : ∀ n, m n ≤ F.order (d n)) :
    ∀ n, ∀ p ∈ (F.withKeySetup (fun n => PMF.pure (d n)) keyLen n).support,
      m n ≤ F.withKey.order p := by
  intro n p hp
  obtain ⟨hd', -⟩ := F.mem_support_withKeySetup (d := p.1) (k := p.2) hp
  rw [PMF.support_pure, Set.mem_singleton_iff] at hd'
  simpa only [PrimeOrderGroupFamily.withKey, hd'] using hm n

private theorem negligible_advantage_of_eight_le {g₀ g₁ h₀ h₁ : ℕ → Game}
    (hmid : Negligible fun n => Game.advantage (h₀ n) (h₁ n))
    (hle₀ : ∀ n, Game.advantage (g₀ n) (h₀ n) ≤ 8 / 2 ^ n)
    (hle₁ : ∀ n, Game.advantage (g₁ n) (h₁ n) ≤ 8 / 2 ^ n) :
    Negligible fun n => Game.advantage (g₀ n) (g₁ n) := by
  negligible using fun n => by
    have h1 := (Game.advantage_comm (g₁ n) (h₁ n)).symm.le.trans (hle₁ n)
    exact ((Game.advantage_triangle (g₀ n) (h₀ n) (g₁ n)).trans
      (add_le_add le_rfl (Game.advantage_triangle (h₀ n) (h₁ n) (g₁ n)))).trans
      (add_le_add (hle₀ n) (add_le_add le_rfl h1))

/-- Binding the ideal game over `withKeySetup` for a fixed group family draws the key first. -/
private theorem withKeySetup_pure_bind {α : Type} (d : ℕ → F.Desc) (keyLen : ℕ → ℕ) (n : ℕ)
    (f : F.withKey.Desc → PMF α) :
    (F.withKeySetup (fun n => PMF.pure (d n)) keyLen n).bind f =
      (ProbComp.eval (BitString.sampleList (keyLen n))).bind fun hk => f (d n, hk) := by
  rw [withKeySetup, PMF.pure_bind, PMF.bind_map]
  rfl

/-- The native `Encryption.cca2ADGameOn` experiment for `(cramerShoupValid, cramerShoupKeyGenProb,
cramerShoupADEncryptProb, cramerShoupADDecryptOpt)` with a keyed hash is within statistical
distance `8 / 2 ^ n` of the ideal exact-uniform PMF game `cramerShoupADGroupCCA2Game` over
`F.withKey` and the setup `withKeySetup (fun n => PMF.pure (d n)) keyLen` (accounting for the eight
`sampleModNat` exponent draws in `cramerShoupKeyGenProb` and `cramerShoupADEncryptProb`; both
games draw the same uniform hash key). -/
theorem advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le
    {AD : Type} (encAD : AD ↪ List Bool)
    (H : F.withKey.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : ℕ → F.Desc) (keyLen : ℕ → ℕ) (adversary : WordADCCA2Adversary AD) (bit : Bool)
    (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (cca2ADGameOn (F.cramerShoupValid isElem d) encAD encBits
          (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupADEncryptProb encAD H d)
          (F.cramerShoupADDecryptOpt H isElem d) adversary bit n))
      (F.withKey.cramerShoupADGroupCCA2Game encAD (F.withKeySetup (fun n => PMF.pure (d n)) keyLen)
        H (F.isElemWithKey isElem) adversary bit n) ≤
      8 / 2 ^ n := by
  have hgame0 :
      ProbComp.eval
        (cca2ADGameOn (F.cramerShoupValid isElem d) encAD encBits
          (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupADEncryptProb encAD H d)
          (F.cramerShoupADDecryptOpt H isElem d) adversary bit n) =
      (ProbComp.eval (BitString.sampleList (keyLen n))).bind fun hk =>
        (ProbComp.eval (F.withKey.sampleExp n (d n, hk))).bind fun a =>
          F.withKey.cramerShoupCCA2SampledSK true (fun p => encAD p.2) H (F.isElemWithKey isElem)
            (d n, hk) adversary bit n (a : ZMod (F.withKey.order (d n, hk))) := by
    simp only [pmf_norm, cca2ADGameOn, cramerShoupKeyGenProb, cramerShoupADEncryptProb,
      cramerShoupValid, F.smul_encode, F.cca2ADPhase1Oracle_cramerShoupADDecryptOpt,
      F.cca2ADPhase2Oracle_cramerShoupADDecryptOpt, cramerShoupCCA2SampledSK,
      cramerShoupPkHashKey_encodeCramerShoupPublicKey, bind_assoc, pure_bind]
    exact congrArg _ (funext fun hk => congrArg _ (funext fun a => congrArg _ (funext fun sk =>
      F.withKey.cramerShoupCCA2InnerSK_false_eq true (fun p => encAD p.2) H
        (F.isElemWithKey isElem) (F.isElemWithKey_iff hmem) (d n, hk) adversary bit n a sk)))
  rw [hgame0, cramerShoupADGroupCCA2Game, F.withKey.cramerShoupMsgCCA2Game_eq_bind_innerSK,
    F.withKeySetup_pure_bind]
  exact Game.advantage_bind_le_nnreal _ _ _ fun hk =>
    F.withKey.advantage_cramerShoupCCA2InnerSK_le true (fun p => encAD p.2) H
      (F.isElemWithKey isElem) (d n, hk) adversary bit n

/-- **Multiplicative Cramer–Shoup with associated data in $\mathcal{D} = \{0,1\}^*$ is 1CCA
secure** ([BonehShoup2023], Exercise 12.27, printed pp. 521–522, by the method of Theorem 12.9,
printed pp. 489–493) under DDH and collision resistance of $H'$ on
$\mathbb{G}^3 \times \{0,1\}^*$. The associated-data space is all words because decryption
hashes whatever associated-data word it is given: `cca2ADPhase1Oracle` and `cca2ADPhase2Oracle`
pass any word to `cramerShoupADDecryptOpt`. A general space $\mathcal{D}$, with collision
resistance assumed only on $\mathbb{G}^3 \times \mathcal{D}$, is open (#5293); it needs
decryption to reject associated data outside $\mathcal{D}$.

In detail: for any polynomial-time group description family `d : ℕ → F.Desc`, polynomial-time
key length `keyLen`, and polynomial-time `H` and `isElem` such that `isElem` accepts exactly the
encodings of group elements, the probabilistic polynomial-time scheme
`(cramerShoupKeyGenProb d keyLen, cramerShoupADEncryptProb encBits H d,
cramerShoupADDecryptOpt H isElem d)`, with associated data the bit strings themselves
(`encBits` is the identity embedding), satisfies the native single-challenge
`Encryption.INDCCA2ADOn` notion with respect to `cramerShoupValid isElem d`. The premises are DDH
for the point-mass setup `fun n => PMF.pure (d n)`; collision resistance of the keyed hash family
`F.withKey.cramerShoupHashMod H`, whose system parameter is the group `d n` together with a
uniform `keyLen n`-bit key, on the words that `isCramerShoupHashInput true` accepts (encoded
group-element triples with any associated-data word); and a positive lower bound
`m n ≤ F.order (d n)` with `1 / m n` negligible. Key generation draws the hash key and publishes
it in the public key, as in [CramerShoup2003], Section 6.1, Figure 1. The group at parameter `n`
is the fixed description `d n`; it is not sampled. [CramerShoup2003], Theorem 1, assumes only
target collision resistance of the keyed hash. -/
theorem DDH.indcca2ADOn_cramerShoup_bitStringAD
    {F : PrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput true (F.isElemWithKey isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2ADOn (F.cramerShoupValid isElem d) encBits encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupADEncryptProb encBits H d)
      (F.cramerShoupADDecryptOpt H isElem d) := fun adversary hA =>
  negligible_advantage_of_eight_le
    ((hDDH.withKey hkeyLen).cramerShoupADGroupIdealINDCCA2 encBits hH
      (F.computableInPolyTime_isElemWithKey hisElem) (F.isElemWithKey_iff hmem) hCR hm0
      (F.order_withKeySetup_ge hm) hinv (F.exists_length_encDesc_withKeySetup_le hd hkeyLen)
      adversary hA)
    (F.advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le encBits H isElem hmem d keyLen
      adversary false)
    (F.advantage_cca2ADGameOn_cramerShoupADGroupCCA2Game_le encBits H isElem hmem d keyLen
      adversary true)

/-- The native `Encryption.cca2GameOn` experiment for `(cramerShoupValid, cramerShoupKeyGenProb,
cramerShoupEncryptProb, cramerShoupDecryptOpt)` with a keyed hash is within statistical distance
`8 / 2 ^ n` of the ideal exact-uniform PMF game `cramerShoupGroupCCA2Game` over `F.withKey` and
the setup `withKeySetup (fun n => PMF.pure (d n)) keyLen` (accounting for the eight `sampleModNat`
exponent draws in `cramerShoupKeyGenProb` and `cramerShoupEncryptProb`; both games draw the same
uniform hash key). -/
theorem advantage_cca2GameOn_cramerShoupGroupCCA2Game_le
    (H : F.withKey.Desc × List Bool → List Bool)
    (isElem : F.Desc × List Bool → Bool)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (d : ℕ → F.Desc) (keyLen : ℕ → ℕ) (adversary : WordCCA2Adversary) (bit : Bool) (n : ℕ) :
    Game.advantage
      (ProbComp.eval
        (cca2GameOn (F.cramerShoupValid isElem d) encBits (F.cramerShoupKeyGenProb d keyLen)
          (F.cramerShoupEncryptProb H d) (F.cramerShoupDecryptOpt H isElem d) adversary bit n))
      (F.withKey.cramerShoupGroupCCA2Game (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) H
        (F.isElemWithKey isElem) adversary bit n) ≤
      8 / 2 ^ n := by
  have hgame0 :
      ProbComp.eval
        (cca2GameOn (F.cramerShoupValid isElem d) encBits (F.cramerShoupKeyGenProb d keyLen)
          (F.cramerShoupEncryptProb H d) (F.cramerShoupDecryptOpt H isElem d) adversary bit n) =
      (ProbComp.eval (BitString.sampleList (keyLen n))).bind fun hk =>
        (ProbComp.eval (F.withKey.sampleExp n (d n, hk))).bind fun a =>
          F.withKey.cramerShoupCCA2SampledSK false (fun _ => []) H (F.isElemWithKey isElem)
            (d n, hk) adversary.toADUnit bit n (a : ZMod (F.withKey.order (d n, hk))) := by
    simp only [pmf_norm, cca2GameOn, cramerShoupKeyGenProb, cramerShoupEncryptProb,
      cramerShoupValid, F.smul_encode, F.cca2Phase1Oracle_cramerShoupDecryptOpt,
      F.cca2Phase2Oracle_cramerShoupDecryptOpt, cramerShoupCCA2SampledSK,
      cramerShoupPkHashKey_encodeCramerShoupPublicKey, bind_assoc, pure_bind]
    refine congrArg _ (funext fun hk => congrArg _ (funext fun a => congrArg _ (funext fun sk =>
      ?_)))
    rw [← F.withKey.cramerShoupCCA2InnerSK_false_eq false (fun _ => []) H
      (F.isElemWithKey isElem) (F.isElemWithKey_iff hmem) (d n, hk) adversary.toADUnit bit n a sk]
    dsimp only [CCA2AdversaryOf.toADUnit]
    rw [eval_run_interpret_map_bind]
    rfl
  rw [hgame0, cramerShoupGroupCCA2Game, F.withKey.cramerShoupMsgCCA2Game_eq_bind_innerSK,
    F.withKeySetup_pure_bind]
  exact Game.advantage_bind_le_nnreal _ _ _ fun hk =>
    F.withKey.advantage_cramerShoupCCA2InnerSK_le false (fun _ => []) H
      (F.isElemWithKey isElem) (d n, hk) adversary.toADUnit bit n

/-- **Multiplicative Cramer–Shoup is 1CCA secure** ([BonehShoup2023], Exercise 12.27, printed
pp. 521–522, without associated data, proved by the method of Theorem 12.9, printed pp. 489–493)
under DDH and collision resistance of $H'$ on its well-formed inputs
$\mathbb{G}^3 \times \mathcal{D}$, here with $\mathcal{D} = \{[]\}$. For any polynomial-time
group description family `d : ℕ → F.Desc`, polynomial-time key length `keyLen`, and
polynomial-time `H` and `isElem` such that `isElem` accepts exactly the encodings of group
elements, the probabilistic polynomial-time scheme `(cramerShoupKeyGenProb d keyLen,
cramerShoupEncryptProb H d, cramerShoupDecryptOpt H isElem d)` satisfies the native
single-challenge `Encryption.INDCCA2On` notion with respect to `cramerShoupValid isElem d`. The
premises are DDH for the point-mass setup `fun n => PMF.pure (d n)`; collision resistance of the
keyed hash family `F.withKey.cramerShoupHashMod H`, whose system parameter is the group `d n`
together with a uniform `keyLen n`-bit key, on the words that `isCramerShoupHashInput false`
accepts (encoded group-element triples with empty associated data); and a positive lower bound
`m n ≤ F.order (d n)` with `1 / m n` negligible. Key generation draws the hash key and publishes
it in the public key, as in [CramerShoup2003], Section 6.1, Figure 1. The group at parameter `n`
is the fixed description `d n`; it is not sampled. [CramerShoup2003], Theorem 1, assumes only
target collision resistance of the keyed hash. -/
theorem DDH.indcca2On_cramerShoup
    {F : PrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput false (F.isElemWithKey isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2On (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) := fun adversary hA =>
  negligible_advantage_of_eight_le
    ((hDDH.withKey hkeyLen).cramerShoupGroupIdealINDCCA2 hH
      (F.computableInPolyTime_isElemWithKey hisElem) (F.isElemWithKey_iff hmem) hCR hm0
      (F.order_withKeySetup_ge hm) hinv (F.exists_length_encDesc_withKeySetup_le hd hkeyLen)
      adversary hA)
    (F.advantage_cca2GameOn_cramerShoupGroupCCA2Game_le H isElem hmem d keyLen adversary false)
    (F.advantage_cca2GameOn_cramerShoupGroupCCA2Game_le H isElem hmem d keyLen adversary true)

/-- **Multiplicative Cramer–Shoup is CCA secure in the batch-challenge game** ([BonehShoup2023],
Exercise 12.27, printed pp. 521–522, proved by the method of Theorem 12.9, printed pp. 489–493,
and the batch-challenge specialization of Theorem 12.1, printed p. 468) under DDH and collision
resistance of $H'$ on its well-formed inputs $\mathbb{G}^3 \times \mathcal{D}$, here with
$\mathcal{D} = \{[]\}$. Under the hypotheses of `DDH.indcca2On_cramerShoup`, the scheme
`(cramerShoupKeyGenProb d keyLen, cramerShoupEncryptProb H d, cramerShoupDecryptOpt H isElem d)`
satisfies the two-phase batch-challenge multi-challenge `Encryption.INDCCA2MultiOn` notion with
respect to `cramerShoupValid isElem d`. The hash key is drawn at key generation and published in
the public key. -/
theorem DDH.indcca2MultiOn_cramerShoup
    {F : PrimeOrderGroupFamily}
    {H : F.withKey.Desc × List Bool → List Bool}
    {isElem : F.Desc × List Bool → Bool}
    {d : ℕ → F.Desc} {keyLen : ℕ → ℕ}
    (hH : ComputableInPolyTime H (encPair F.withKey.encDesc encBits) encBits)
    (hisElem : ComputableInPolyTime isElem (encPair F.encDesc encBits) encBool)
    (hd : ComputableInPolyTime d encUnary F.encDesc)
    (hkeyLen : ComputableInPolyTime keyLen encUnary encUnary)
    (hmem : ∀ d x, isElem (d, x) = true ↔ x ∈ Set.range (F.encode d))
    (hDDH : F.DDH (fun n => PMF.pure (d n)))
    (hCR : CollisionResistantForOn F.withKey.encDesc
      (F.withKeySetup (fun n => PMF.pure (d n)) keyLen) (F.withKey.cramerShoupHashMod H)
      (fun _ => F.withKey.isCramerShoupHashInput false (F.isElemWithKey isElem)))
    {m : ℕ → ℕ} (hm0 : ∀ n, 0 < m n)
    (hm : ∀ n, m n ≤ F.order (d n))
    (hinv : Negligible fun n => (1 / m n : ℝ≥0)) :
    INDCCA2MultiOn (F.cramerShoupValid isElem d) encBits encBits
      (F.cramerShoupKeyGenProb d keyLen) (F.cramerShoupEncryptProb H d)
      (F.cramerShoupDecryptOpt H isElem d) :=
  (hDDH.indcca2On_cramerShoup hH hisElem hd hkeyLen hmem hCR hm0 hm hinv).indcca2MultiOn
    (F.computableInPolyTime_cramerShoupValid hisElem hd)
    (F.isPPTOn_cramerShoupKeyGenProb hd hkeyLen)
    (F.isPPTOn_cramerShoupEncryptProb hH hd)
    (F.computableInPolyTime_cramerShoupDecryptOpt hH hisElem hd)

end Cslib.Crypto.PrimeOrderGroupFamily
