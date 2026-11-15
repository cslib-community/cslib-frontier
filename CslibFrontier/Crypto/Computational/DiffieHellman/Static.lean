/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman.Finite
public import CslibFrontier.Crypto.Computational.ElGamal.ProbComp
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
public import CslibFrontier.Languages.Probabilistic.Oracle.Run
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.ZMod.NatCast
import CslibFrontier.Languages.Probabilistic.Oracle.Substitution.QueryCount
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PolyTime

/-!
# Static Diffie–Hellman and chosen-ciphertext key recovery against multiplicative ElGamal

Fix an additive commutative group `G` that is a `ZMod q`-module, as in
`CslibFrontier/Crypto/Computational/DiffieHellman/Finite.lean`; the textbook element `v ^ α` is
`α • v` and the identity `1` is `0`.

In the static Diffie–Hellman (SDH) experiment ([BonehShoup2023], Section 16.1.4, Attack Game 16.1,
p. 688), the challenger draws a uniform secret `α : ZMod q` and answers each query `v : G` with
`α • v` (`sdhOracle`); the adversary wins when it outputs `α` (`sdhExperiment`, `sdhAdvantage`).
With one query at `g`, a discrete-logarithm adversary `A` plays `dlExperiment q g A` inside
`sdhExperiment` (`dlToSDH`, `sdhExperiment_dlToSDH`).

Multiplicative ElGamal ([BonehShoup2023], Exercise 11.5, p. 459) decrypts a ciphertext
`(v, e) : G × G` under secret key `α : ZMod q` to `e - α • v` (`elGamalDecryptValue`). As
observed in [BonehShoup2023], Section 16.1.4 (p. 688), decrypting `(-v, 0)` (the additive form of
`(1 / v, 1)`) returns `0 - α • (-v) = α • v` (`elGamalDecryptValue_neg_zero`). Consequently,
answering each SDH query `v` by asking the ElGamal decryption oracle for `(-v, 0)` turns any
static-DH adversary `A` into a chosen-ciphertext key-recovery adversary `sdhToElGamalKeyRecovery A`
with the exact same experiment distribution and success probability
(`elGamalKeyRecoveryExperiment_sdhToElGamalKeyRecovery`,
`elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery`), preserving any query budget `Q`
(`isQueryBounded_sdhToElGamalKeyRecovery`) and submitting only ciphertexts with second component `0`
(`queriesSatisfy_sdhToElGamalKeyRecovery`). Conversely, an ElGamal key-recovery adversary `B` making
at most `Q` decryption queries gives a static-DH adversary `elGamalKeyRecoveryToSDH g B` making at
most `Q + 1` SDH queries (one query at `g` for the public key `α • g`, plus one per decryption
query) with the same experiment distribution (`sdhExperiment_elGamalKeyRecoveryToSDH`,
`isQueryBounded_elGamalKeyRecoveryToSDH`).

Over a `PrimeOrderGroupFamily`, `sdhGame` and `elGamalKeyRecoveryGame` average these experiments
over a setup distribution, and `elGamalSDHCiphertext` maps `(d, encode v)` to the encoded
ciphertext `(-v, 0)` in polynomial time (`computableInPolyTime_elGamalSDHCiphertext`), with
`elGamalDecryptDet` recovering `encode ((ofBits sk : ZMod q) • v)` on every encoded group element
(`elGamalDecryptDet_elGamalSDHCiphertext`). The efficiency evidence in this module consists of the
per-reduction query bounds and `computableInPolyTime_elGamalSDHCiphertext`; no family-level PPT
adversary predicate (`IsOraclePPT` / `IsOraclePPTOf`) or asymptotic `SDH` assumption (`Prop`) is
stated here, as word-level oracle rejection of non-subgroup queries requires a decodable group
family.

## Differences from the book

* Groups are written additively as `ZMod q`-modules: `1` is `0`, `v ^ α` is `α • v`, `1 / v` is
  `-v`, and the decryption query `(1 / v, 1)` is `(-v, 0)`.
* The fixed-group definitions and theorems assume only `[AddCommGroup G]`, `[NeZero q]` and
  `[Module (ZMod q) G]`; neither primality of `q` nor that `g` generates `G` is required.
* In Attack Game 16.1 the challenger sends no initial group element to the SDH adversary, whereas in
  `elGamalKeyRecoveryExperiment` the adversary receives the public key `α • g`. Thus
  `sdhToElGamalKeyRecovery` ignores the public key and preserves the query bound `Q`, while
  `elGamalKeyRecoveryToSDH` queries `g` once to form `α • g` and has query bound `Q + 1`.
* On a `PrimeOrderGroupFamily`, `elGamalSDHCiphertext` inverts `v` by multiplying its encoding by
  `F.order d - 1`. This equals `-v` on encoded elements of `F.Carrier d`
  (`elGamalSDHCiphertext_encode`), whereas on bit strings outside `Set.range (F.encode d)` (such as
  quadratic non-residues in a Schnorr modulus) `elGamalDecryptDet` and `F.smul` can disagree.

## Main definitions

* `Cslib.Crypto.SDHSpec`, `Cslib.Crypto.SDHAdversary`, `Cslib.Crypto.sdhOracle`,
  `Cslib.Crypto.sdhExperiment`, `Cslib.Crypto.sdhAdvantage`: Attack Game 16.1 in a fixed group;
  `sdhOracle` is shared with the one-more Diffie–Hellman game of Section 11.6.3.
* `Cslib.Crypto.dlToSDH`: the 1-query discrete-logarithm to static-DH reduction.
* `Cslib.Crypto.ElGamalDecryptionSpec`, `Cslib.Crypto.ElGamalKeyRecoveryAdversary`,
  `Cslib.Crypto.elGamalDecryptValue`, `Cslib.Crypto.elGamalDecryptOracle`,
  `Cslib.Crypto.elGamalKeyRecoveryExperiment`, `Cslib.Crypto.elGamalKeyRecoveryAdvantage`:
  the multiplicative ElGamal chosen-ciphertext key-recovery experiment.
* `Cslib.Crypto.dlToElGamalKeyRecovery`, `Cslib.Crypto.sdhToElGamalKeyRecovery`,
  `Cslib.Crypto.elGamalKeyRecoveryToSDH`: the reductions between discrete logarithm, static DH and
  ElGamal key recovery.
* `Cslib.Crypto.PrimeOrderGroupFamily.SDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ElGamalKeyRecoveryAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.sdhGame`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalKeyRecoveryGame`: the games over a prime-order group
  family.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalSDHCiphertext`: the word-level query-to-ciphertext map
  `(d, encode v) ↦ encode (-v, 0)`.

## Main results

* `Cslib.Crypto.sdhExperiment_dlToSDH`, `Cslib.Crypto.sdhAdvantage_dlToSDH`,
  `Cslib.Crypto.isQueryBounded_dlToSDH`, `Cslib.Crypto.queriesSatisfy_dlToSDH`: discrete logarithm
  reduces to 1-query static DH.
* `Cslib.Crypto.elGamalDecryptValue_neg_zero`: decrypting `(-v, 0)` returns `α • v`.
* `Cslib.Crypto.elGamalKeyRecoveryExperiment_dlToElGamalKeyRecovery`,
  `Cslib.Crypto.elGamalKeyRecoveryAdvantage_dlToElGamalKeyRecovery`,
  `Cslib.Crypto.isQueryBounded_dlToElGamalKeyRecovery`: 0-query ElGamal key recovery is the
  discrete-logarithm experiment.
* `Cslib.Crypto.elGamalKeyRecoveryExperiment_sdhToElGamalKeyRecovery`,
  `Cslib.Crypto.elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery`,
  `Cslib.Crypto.isQueryBounded_sdhToElGamalKeyRecovery`,
  `Cslib.Crypto.queriesSatisfy_sdhToElGamalKeyRecovery`: static DH reduces to ElGamal CCA key
  recovery with the same advantage and query budget `Q`.
* `Cslib.Crypto.sdhExperiment_elGamalKeyRecoveryToSDH`,
  `Cslib.Crypto.sdhAdvantage_elGamalKeyRecoveryToSDH`,
  `Cslib.Crypto.isQueryBounded_elGamalKeyRecoveryToSDH`: ElGamal CCA key recovery with budget `Q`
  reduces to static DH with budget `Q + 1`.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalKeyRecoveryGame_sdhToElGamalKeyRecovery`,
  `Cslib.Crypto.PrimeOrderGroupFamily.sdhGame_elGamalKeyRecoveryToSDH`: the family-level game
  identities.
* `Cslib.Crypto.PrimeOrderGroupFamily.elGamalSDHCiphertext_encode`,
  `Cslib.Crypto.PrimeOrderGroupFamily.decodeElGamal_elGamalSDHCiphertext`,
  `Cslib.Crypto.PrimeOrderGroupFamily.elGamalDecryptDet_elGamalSDHCiphertext`,
  `Cslib.Crypto.PrimeOrderGroupFamily.computableInPolyTime_elGamalSDHCiphertext`: correctness and
  polynomial-time certificate for `elGamalSDHCiphertext`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Exercise 11.5 (p. 459) and Section 16.1.4 (Attack Game 16.1,
  p. 688).
-/

public section

namespace Cslib.Crypto

open Probability
open scoped NNReal ENNReal

section FixedGroup

variable {G : Type} [AddCommGroup G] (q : ℕ) [NeZero q] [Module (ZMod q) G] (g : G)

/-! ### Static Diffie–Hellman (Attack Game 16.1) -/

/-- The oracle interface of the static Diffie–Hellman game ([BonehShoup2023], Section 16.1.4,
Attack Game 16.1, p. 688): each query is a group element `v : G` and is answered by a group
element. -/
abbrev SDHSpec (G : Type) : OracleSpec G := fun _ => G

/-- An adversary for the static Diffie–Hellman game in a group `G` of exponent modulus `q`: a
randomized oracle program over `SDHSpec G` that outputs a guess in `ZMod q`. -/
abbrev SDHAdversary (G : Type) (q : ℕ) : Type :=
  ProbOracleComp (SDHSpec G) (ZMod q)

/-- The static Diffie–Hellman solve oracle ([BonehShoup2023], Section 16.1.4, Attack Game 16.1,
p. 688, and Section 11.6.3, p. 455): on query `v : G`, return `α • v` (the textbook `v ^ α`).
This is also the CDH-solve oracle of the one-more Diffie–Hellman game of Section 11.6.3. -/
@[expose] def sdhOracle (α : ZMod q) (v : G) : ProbComp G :=
  pure (α • v)

/-- The static Diffie–Hellman experiment ([BonehShoup2023], Section 16.1.4, Attack Game 16.1,
p. 688): draw a uniform secret `α : ZMod q`, run `A` against `sdhOracle q α`, and accept when the
adversary outputs `α`. -/
@[expose] noncomputable def sdhExperiment (A : SDHAdversary G q) : Experiment := do
  let α ← $ᵗ ZMod q
  let guess ← A.run (sdhOracle q α)
  return guess = α

/-- The static Diffie–Hellman advantage of `A`: its success probability in `sdhExperiment`. -/
@[expose] noncomputable def sdhAdvantage (A : SDHAdversary G q) : ℝ≥0 :=
  Experiment.succProbability (sdhExperiment q A)

/-- Turn a discrete-logarithm adversary `A` into a 1-query static Diffie–Hellman adversary
([BonehShoup2023], Section 16.1.4, p. 688): query the SDH oracle at `g` to obtain `α • g` and run
`A` on the reply. -/
def dlToSDH {q : ℕ} (g : G) (A : G → ProbComp (ZMod q)) : SDHAdversary G q := do
  let u ← ProbOracleComp.query (spec := SDHSpec G) g
  ProbOracleComp.sample (A u)

omit [NeZero q] in
/-- Running `dlToSDH g A` against `sdhOracle q α` runs `A (α • g)`. -/
@[simp] theorem run_sdhOracle_dlToSDH (A : G → ProbComp (ZMod q)) (α : ZMod q) :
    (dlToSDH g A).run (sdhOracle q α) = A (α • g) := by
  simp [dlToSDH, sdhOracle]

/-- In `sdhExperiment`, `dlToSDH g A` is the discrete-logarithm experiment `dlExperiment q g A`. -/
@[simp] theorem sdhExperiment_dlToSDH (A : G → ProbComp (ZMod q)) :
    sdhExperiment q (dlToSDH g A) = dlExperiment q g A := by
  simp [sdhExperiment, dlExperiment]

/-- `dlToSDH g A` wins the static Diffie–Hellman game with the exact discrete-logarithm advantage
of `A`. -/
@[simp] theorem sdhAdvantage_dlToSDH (A : G → ProbComp (ZMod q)) :
    sdhAdvantage q (dlToSDH g A) = dlAdvantage q g A := by
  simp [sdhAdvantage, dlAdvantage]

omit [AddCommGroup G] in
/-- `dlToSDH g A` makes at most `1` SDH query on every path. -/
theorem isQueryBounded_dlToSDH {q : ℕ} (g : G) (A : G → ProbComp (ZMod q)) :
    (dlToSDH g A).IsQueryBounded 1 := by
  simpa [dlToSDH] using
    (ProbOracleComp.IsQueryBounded.query (spec := SDHSpec G) g).bind fun u =>
      ProbOracleComp.IsQueryBounded.sample (spec := SDHSpec G) (A u)

omit [AddCommGroup G] in
/-- Every SDH query made by `dlToSDH g A` is `g`. -/
theorem queriesSatisfy_dlToSDH {q : ℕ} (g : G) (A : G → ProbComp (ZMod q)) :
    (dlToSDH g A).QueriesSatisfy (· = g) := by
  simpa [dlToSDH, ProbOracleComp.QueriesSatisfy] using
    (ProbOracleComp.QueriesSatisfy.query (spec := SDHSpec G) (p := (· = g)) rfl).bind fun u =>
      ProbOracleComp.QueriesSatisfy.sample (spec := SDHSpec G) (A u)

/-! ### Chosen-ciphertext key recovery on multiplicative ElGamal -/

/-- The decryption oracle interface of multiplicative ElGamal ([BonehShoup2023], Exercise 11.5,
p. 459, and Section 16.1.4, p. 688): a query is a ciphertext pair `(v, e) : G × G` and is answered
by the decrypted group element in `G`. -/
abbrev ElGamalDecryptionSpec (G : Type) : OracleSpec (G × G) := fun _ => G

/-- A chosen-ciphertext key-recovery adversary against multiplicative ElGamal: given the public
key `u = α • g`, it queries the decryption oracle on ciphertexts in `G × G` and outputs a guess
for the secret key `α : ZMod q`. -/
abbrev ElGamalKeyRecoveryAdversary (G : Type) (q : ℕ) : Type :=
  G → ProbOracleComp (ElGamalDecryptionSpec G) (ZMod q)

/-- Algebraic multiplicative ElGamal decryption of a ciphertext `(v, e)` under secret key
`α : ZMod q` ([BonehShoup2023], Exercise 11.5, p. 459), written additively as `e - α • v`. -/
@[expose] def elGamalDecryptValue (α : ZMod q) (ct : G × G) : G :=
  ct.2 - α • ct.1

omit [NeZero q] in
/-- **Key observation of [BonehShoup2023], Section 16.1.4 (p. 688)**: decrypting the ciphertext
`(-v, 0)` (the additive form of `c := (1 / v, 1)`) under secret key `α` returns `α • v` (the
additive form of `v ^ α`). -/
@[simp] theorem elGamalDecryptValue_neg_zero (α : ZMod q) (v : G) :
    elGamalDecryptValue q α (-v, (0 : G)) = α • v := by
  simp [elGamalDecryptValue]

/-- The multiplicative ElGamal decryption oracle under secret key `α : ZMod q`. -/
@[expose] def elGamalDecryptOracle (α : ZMod q) (ct : G × G) : ProbComp G :=
  pure (elGamalDecryptValue q α ct)

/-- The chosen-ciphertext key-recovery experiment for multiplicative ElGamal ([BonehShoup2023],
Section 16.1.4, p. 688): draw a uniform secret key `α : ZMod q`, pass the public key `α • g` to `B`
with access to `elGamalDecryptOracle q α`, and accept when `B` outputs `α`. -/
@[expose] noncomputable def elGamalKeyRecoveryExperiment
    (B : ElGamalKeyRecoveryAdversary G q) : Experiment := do
  let α ← $ᵗ ZMod q
  let guess ← (B (α • g)).run (elGamalDecryptOracle q α)
  return guess = α

/-- The key-recovery advantage of `B` against multiplicative ElGamal: its success probability in
`elGamalKeyRecoveryExperiment`. -/
@[expose] noncomputable def elGamalKeyRecoveryAdvantage
    (B : ElGamalKeyRecoveryAdversary G q) : ℝ≥0 :=
  Experiment.succProbability (elGamalKeyRecoveryExperiment q g B)

/-- Embed a discrete-logarithm adversary `A` as a 0-query ElGamal key-recovery adversary. -/
def dlToElGamalKeyRecovery {q : ℕ} (A : G → ProbComp (ZMod q)) :
    ElGamalKeyRecoveryAdversary G q :=
  fun u => ProbOracleComp.sample (A u)

/-- Without decryption queries, `elGamalKeyRecoveryExperiment` is `dlExperiment`. -/
@[simp] theorem elGamalKeyRecoveryExperiment_dlToElGamalKeyRecovery
    (A : G → ProbComp (ZMod q)) :
    elGamalKeyRecoveryExperiment q g (dlToElGamalKeyRecovery A) = dlExperiment q g A := by
  simp [elGamalKeyRecoveryExperiment, dlToElGamalKeyRecovery, dlExperiment]

/-- `dlToElGamalKeyRecovery A` has the exact discrete-logarithm advantage of `A`. -/
@[simp] theorem elGamalKeyRecoveryAdvantage_dlToElGamalKeyRecovery
    (A : G → ProbComp (ZMod q)) :
    elGamalKeyRecoveryAdvantage q g (dlToElGamalKeyRecovery A) = dlAdvantage q g A := by
  simp [elGamalKeyRecoveryAdvantage, dlAdvantage]

omit [AddCommGroup G] in
/-- `dlToElGamalKeyRecovery A` makes `0` decryption queries. -/
theorem isQueryBounded_dlToElGamalKeyRecovery {q : ℕ} (A : G → ProbComp (ZMod q)) (u : G) :
    (dlToElGamalKeyRecovery A u).IsQueryBounded 0 :=
  ProbOracleComp.IsQueryBounded.sample (spec := ElGamalDecryptionSpec G) (A u)

/-- **The static-DH to ElGamal CCA key-recovery reduction** ([BonehShoup2023], Section 16.1.4,
p. 688): given a static-DH adversary `A`, build the key-recovery CCA adversary `B` that runs `A`
and answers each SDH query `v : G` by querying the ElGamal decryption oracle on `(-v, 0)` (the
additive form of `(1 / v, 1)`). -/
def sdhToElGamalKeyRecovery {q : ℕ} (A : SDHAdversary G q) :
    ElGamalKeyRecoveryAdversary G q :=
  fun _ => ProbOracleComp.simulate (fun v => ProbOracleComp.query (-v, 0)) A

omit [NeZero q] in
/-- Running `sdhToElGamalKeyRecovery A` against the ElGamal decryption oracle runs `A` against the
SDH oracle. -/
@[simp] theorem run_elGamalDecryptOracle_sdhToElGamalKeyRecovery (α : ZMod q)
    (A : SDHAdversary G q) (u : G) :
    (sdhToElGamalKeyRecovery A u).run (elGamalDecryptOracle q α) = A.run (sdhOracle q α) := by
  simp only [sdhToElGamalKeyRecovery, ProbOracleComp.run_simulate, ProbOracleComp.run_query,
    elGamalDecryptOracle, elGamalDecryptValue_neg_zero]
  rfl

/-- **The key-recovery experiment of `sdhToElGamalKeyRecovery A` is `sdhExperiment q A`**
([BonehShoup2023], Section 16.1.4, p. 688). -/
@[simp] theorem elGamalKeyRecoveryExperiment_sdhToElGamalKeyRecovery (A : SDHAdversary G q) :
    elGamalKeyRecoveryExperiment q g (sdhToElGamalKeyRecovery A) = sdhExperiment q A := by
  simp [elGamalKeyRecoveryExperiment, sdhExperiment]

/-- **`sdhToElGamalKeyRecovery A` recovers the ElGamal secret key with the exact SDH advantage of
`A`** ([BonehShoup2023], Section 16.1.4, p. 688). -/
@[simp] theorem elGamalKeyRecoveryAdvantage_sdhToElGamalKeyRecovery (A : SDHAdversary G q) :
    elGamalKeyRecoveryAdvantage q g (sdhToElGamalKeyRecovery A) = sdhAdvantage q A := by
  simp [elGamalKeyRecoveryAdvantage, sdhAdvantage]

/-- **Query-bound certificate for `sdhToElGamalKeyRecovery`**: if `A` makes at most `Q` SDH
queries, then `sdhToElGamalKeyRecovery A` makes at most `Q` decryption queries. -/
theorem isQueryBounded_sdhToElGamalKeyRecovery {q : ℕ} {A : SDHAdversary G q} {Q : ℕ}
    (hQ : A.IsQueryBounded Q) (u : G) :
    (sdhToElGamalKeyRecovery A u).IsQueryBounded Q :=
  hQ.simulate fun v => ProbOracleComp.IsQueryBounded.query (spec := ElGamalDecryptionSpec G) (-v, 0)

/-- Every decryption query submitted by `sdhToElGamalKeyRecovery A` has second component `0`
(the textbook `(1 / v, 1)`). -/
theorem queriesSatisfy_sdhToElGamalKeyRecovery {q : ℕ} (A : SDHAdversary G q) (u : G) :
    (sdhToElGamalKeyRecovery A u).QueriesSatisfy fun ct => ct.2 = 0 := by
  classical
  have h0 : OracleComp.IsCostBounded (Sum.elim (fun _ => 0) (fun _ => 0)) A 0 :=
    OracleComp.IsCostBounded.of_forall_cost_eq_zero (fun q => by cases q <;> rfl) A
  have hsim := ProbOracleComp.isCostBounded_simulate
    (cost := fun _ => 0) (cost' := fun ct : G × G => if ct.2 = 0 then 0 else 1)
    (fun v => by
      simpa using ProbOracleComp.isCostBounded_query (spec := ElGamalDecryptionSpec G)
        (fun ct : G × G => if ct.2 = 0 then 0 else 1) (-v, 0))
    h0
  exact hsim.of_le fun q => by
    cases q <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> split_ifs <;> simp_all

/-- The converse reduction: turn an ElGamal key-recovery adversary `B` into a static-DH adversary
by querying `g` to obtain the public key `α • g` and answering each decryption query `(v, e)` with
`e - α • v` via one SDH query at `v`. -/
def elGamalKeyRecoveryToSDH {q : ℕ} (g : G) (B : ElGamalKeyRecoveryAdversary G q) :
    SDHAdversary G q := do
  let u ← ProbOracleComp.query (spec := SDHSpec G) g
  ProbOracleComp.simulate
    (fun ct : G × G => do
      let w ← ProbOracleComp.query (spec := SDHSpec G) ct.1
      return ct.2 - w)
    (B u)

omit [NeZero q] in
/-- Running `elGamalKeyRecoveryToSDH g B` against `sdhOracle q α` runs `B (α • g)` against
`elGamalDecryptOracle q α`. -/
@[simp] theorem run_sdhOracle_elGamalKeyRecoveryToSDH (B : ElGamalKeyRecoveryAdversary G q)
    (α : ZMod q) :
    (elGamalKeyRecoveryToSDH g B).run (sdhOracle q α) =
      (B (α • g)).run (elGamalDecryptOracle q α) := by
  simp only [elGamalKeyRecoveryToSDH, ProbOracleComp.run_bind, ProbOracleComp.run_query,
    ProbOracleComp.run_simulate, ProbOracleComp.run_pure, sdhOracle, pure_bind]
  rfl

/-- In `sdhExperiment`, `elGamalKeyRecoveryToSDH g B` is `elGamalKeyRecoveryExperiment q g B`. -/
@[simp] theorem sdhExperiment_elGamalKeyRecoveryToSDH (B : ElGamalKeyRecoveryAdversary G q) :
    sdhExperiment q (elGamalKeyRecoveryToSDH g B) = elGamalKeyRecoveryExperiment q g B := by
  simp [sdhExperiment, elGamalKeyRecoveryExperiment]

/-- `elGamalKeyRecoveryToSDH g B` wins the static-DH game with the exact key-recovery advantage of
`B`. -/
@[simp] theorem sdhAdvantage_elGamalKeyRecoveryToSDH (B : ElGamalKeyRecoveryAdversary G q) :
    sdhAdvantage q (elGamalKeyRecoveryToSDH g B) = elGamalKeyRecoveryAdvantage q g B := by
  simp [sdhAdvantage, elGamalKeyRecoveryAdvantage]

/-- **Query-bound certificate for `elGamalKeyRecoveryToSDH`**: if `B` makes at most `Q` decryption
queries on every public key, then `elGamalKeyRecoveryToSDH g B` makes at most `Q + 1` SDH
queries. -/
theorem isQueryBounded_elGamalKeyRecoveryToSDH {q : ℕ} (g : G)
    {B : ElGamalKeyRecoveryAdversary G q} {Q : ℕ} (hQ : ∀ u, (B u).IsQueryBounded Q) :
    (elGamalKeyRecoveryToSDH g B).IsQueryBounded (Q + 1) := by
  rw [Nat.add_comm]
  refine (ProbOracleComp.IsQueryBounded.query (spec := SDHSpec G) g).bind fun u => ?_
  refine (hQ u).simulate fun ct => ?_
  simpa using (ProbOracleComp.IsQueryBounded.query (spec := SDHSpec G) ct.1).bind fun w =>
    OracleComp.IsCostBounded.pure (ct.2 - w) 0

end FixedGroup

namespace PrimeOrderGroupFamily

open Turing.MultiTapeTM

variable (F : PrimeOrderGroupFamily)

/-- A family of static Diffie–Hellman adversaries over `F`: at security parameter `n` and public
group parameters `d : F.Desc`, an `SDHAdversary` in `F.Carrier d`. -/
abbrev SDHAdversary : Type :=
  ℕ → (d : F.Desc) → Crypto.SDHAdversary (F.Carrier d) (F.order d)

/-- A family of multiplicative ElGamal key-recovery adversaries over `F`: at security parameter `n`
and public group parameters `d : F.Desc`, an `ElGamalKeyRecoveryAdversary` in `F.Carrier d`. -/
abbrev ElGamalKeyRecoveryAdversary : Type :=
  ℕ → (d : F.Desc) → Crypto.ElGamalKeyRecoveryAdversary (F.Carrier d) (F.order d)

/-- The static Diffie–Hellman game over `F`: draw public group parameters `d` from `setup n` and
run `sdhExperiment` in `F.Carrier d`. -/
noncomputable def sdhGame (setup : ℕ → PMF F.Desc) (adversary : F.SDHAdversary)
    (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d => sdhExperiment (F.order d) (adversary n d)

/-- The multiplicative ElGamal key-recovery game over `F`: draw public group parameters `d` from
`setup n` and run `elGamalKeyRecoveryExperiment` in `F.Carrier d`. -/
noncomputable def elGamalKeyRecoveryGame (setup : ℕ → PMF F.Desc)
    (adversary : F.ElGamalKeyRecoveryAdversary) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    elGamalKeyRecoveryExperiment (F.order d) (F.generator d) (adversary n d)

/-- `F.elGamalDecrypt d` is `elGamalDecryptValue` in `F.Carrier d`. -/
theorem elGamalDecrypt_eq_elGamalDecryptValue (d : F.Desc) (α : ZMod (F.order d))
    (ct : F.Carrier d × F.Carrier d) :
    F.elGamalDecrypt d α ct = elGamalDecryptValue (F.order d) α ct := rfl

/-- Decrypting `(-v, 0)` with `F.elGamalDecrypt d α` returns `α • v`. -/
@[simp] theorem elGamalDecrypt_neg_zero (d : F.Desc) (α : ZMod (F.order d)) (v : F.Carrier d) :
    F.elGamalDecrypt d α (-v, 0) = α • v :=
  elGamalDecryptValue_neg_zero (F.order d) α v

/-- Over any setup law, `sdhToElGamalKeyRecovery` turns an SDH adversary family into an ElGamal
key-recovery adversary family with the exact same game distribution. -/
@[simp] theorem elGamalKeyRecoveryGame_sdhToElGamalKeyRecovery (setup : ℕ → PMF F.Desc)
    (adversary : F.SDHAdversary) (n : ℕ) :
    F.elGamalKeyRecoveryGame setup (fun m d => sdhToElGamalKeyRecovery (adversary m d)) n =
      F.sdhGame setup adversary n := by
  simp [elGamalKeyRecoveryGame, sdhGame]

/-- Over any setup law, `elGamalKeyRecoveryToSDH` turns an ElGamal key-recovery adversary family
into an SDH adversary family with the exact same game distribution. -/
@[simp] theorem sdhGame_elGamalKeyRecoveryToSDH (setup : ℕ → PMF F.Desc)
    (adversary : F.ElGamalKeyRecoveryAdversary) (n : ℕ) :
    F.sdhGame setup (fun m d => elGamalKeyRecoveryToSDH (F.generator d) (adversary m d)) n =
      F.elGamalKeyRecoveryGame setup adversary n := by
  simp [sdhGame, elGamalKeyRecoveryGame]

/-- The word-level ciphertext map of the static-DH key-recovery attack on multiplicative ElGamal
([BonehShoup2023], Section 16.1.4, p. 688): given group parameters `d` and an encoded group element
`w`, construct the encoded ciphertext `encPair encBits encBits (encode (-v), encode 0)` by
multiplying `w` by `F.order d - 1` (which is `-1` in `ZMod (F.order d)`) and pairing with
`0 • g`. -/
@[expose] def elGamalSDHCiphertext (d : F.Desc) (w : List Bool) : List Bool :=
  encPair encBits encBits
    (F.smul (d, F.order d - 1, w), F.smul (d, 0, F.encode d (F.generator d)))

/-- On an encoded group element `F.encode d v`, `elGamalSDHCiphertext` produces the encoded
ciphertext `(-v, 0)` (the textbook `(1 / v, 1)`). -/
@[simp] theorem elGamalSDHCiphertext_encode (d : F.Desc) (v : F.Carrier d) :
    F.elGamalSDHCiphertext d (F.encode d v) =
      encPair encBits encBits (F.encode d (-v), F.encode d 0) := by
  simp [elGamalSDHCiphertext, F.smul_encode, ZMod.natCast_self_sub_one]

/-- Word-level ElGamal decryption `decodeElGamal` on the components of
`elGamalSDHCiphertext d (F.encode d v)` under secret-key exponent `a` returns
`F.encode d ((a : ZMod (F.order d)) • v)`. -/
theorem decodeElGamal_elGamalSDHCiphertext (d : F.Desc) (a : ℕ) (v : F.Carrier d) :
    F.decodeElGamal (d, a, unframe (F.elGamalSDHCiphertext d (F.encode d v)),
      dropFrame (F.elGamalSDHCiphertext d (F.encode d v))) =
      F.encode d ((a : ZMod (F.order d)) • v) := by
  simp [elGamalSDHCiphertext_encode, decodeElGamal_encode]

/-- Deterministic word-level ElGamal decryption `elGamalDecryptDet` on
`elGamalSDHCiphertext (d n) (F.encode (d n) v)` under secret key `sk` returns the encoded SDH
reply `F.encode (d n) ((ofBits sk : ZMod (F.order (d n))) • v)`. -/
theorem elGamalDecryptDet_elGamalSDHCiphertext (d : ℕ → F.Desc) (n : ℕ) (sk : List Bool)
    (v : F.Carrier (d n)) :
    F.elGamalDecryptDet d n sk (F.elGamalSDHCiphertext (d n) (F.encode (d n) v)) =
      F.encode (d n) ((ofBits sk : ZMod (F.order (d n))) • v) := by
  simp [elGamalDecryptDet, elGamalSDHCiphertext_encode, decodeElGamal_encode]

/-- **Polynomial-time certificate for `elGamalSDHCiphertext`**: constructing the encoded decryption
query `(-v, 0)` from `(d, encode v)` is computable in polynomial time. -/
theorem computableInPolyTime_elGamalSDHCiphertext :
    ComputableInPolyTime (fun p : F.Desc × List Bool => F.elGamalSDHCiphertext p.1 p.2)
      (encPair F.encDesc encBits) encBits := by
  have hd := ComputableInPolyTime.fst F.encDesc encBits
  have hw := ComputableInPolyTime.snd F.encDesc encBits
  have hord := F.computableInPolyTime_order.comp hd
  have hpred := ComputableInPolyTime.binary_sub.comp (hord.prod (ComputableInPolyTime.const 1))
  have hneg := F.computableInPolyTime_smul.comp (hd.prod (hpred.prod hw))
  have hzero := F.computableInPolyTime_smul.comp
    (hd.prod ((ComputableInPolyTime.const 0).prod (F.computableInPolyTime_generator.comp hd)))
  unfold elGamalSDHCiphertext
  fun_prop

end PrimeOrderGroupFamily

end Cslib.Crypto
