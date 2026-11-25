/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Computational.TreeSignature.ForgerEfficiency
public import CslibFrontier.Crypto.Computational.TreeSignature.IdealToLazy
public import CslibFrontier.Crypto.Computational.TreeSignature.LazyToIndexed
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Crypto.Computational.MerkleSignature.Security
import CslibFrontier.Crypto.Computational.OneWayToPRF
import CslibFrontier.Crypto.Negligible.Dyadic
import CslibFrontier.Tactic.Negligible

/-!
# Security of stateless tree signatures

Steps toward stateless EUF-CMA security of `TreeSignature.scheme`, [BonehShoup2023],
Section 14.6.3, Theorem 14.6, p. 600, in the binary case `q = 2`. An indexed EUF-CMA secure
signature scheme `S` of capacity at least `2`, used at indices `0` and `1` only, and a
length-preserving pseudorandom function yield a stateless many-time signature scheme
(`eufCMA_scheme_of_prf`). That is not Theorem 14.6, because its PRF premise is stronger than the
source's, as explained below; the theorem itself is open (#5293).

Theorem 14.6 covers a `q`-ary tree of depth `d` for poly-bounded `d` and `q` with `q ^ d`
super-poly. The tree here is binary, so `2 ^ depth n` must be super-poly: the asymptotic theorems
assume that `1 / 2 ^ depth n` is negligible, with `depth` computable in polynomial time. The
source's term `Q ^ 2 / (2 q ^ d)` becomes `Q ^ 2 / 2 ^ (depth n + 1)`, and its factor `Q d`
becomes `dyadicSize (Q * depth n)`, a power of two in `(Q d, 2 Q d]` when `Q d ≥ 1`. The tree
for general `q` is not formalized (#5293). Besides the construction's deviations, listed in
`CslibFrontier.Crypto.Computational.TreeSignature`, the theorems differ from the source in two ways.

* The outer messages are `n`-bit, `SignatureScheme`'s message space.
* The coins of node keys and signatures are `prfCoins family`: a length-preserving
  `PseudorandomFunction` `family`, keyed at `coinParam budget n` bits, evaluated at the padded
  request and truncated. The source assumes a PRF `F` defined over
  `(K, {1, …, q} ^ {≤ d}, {0, 1} ^ w)` whose outputs are the coins (Sections 14.6.2 and 14.6.3,
  p. 600).

Using `family` at the rescaled parameter `coinParam budget n ≥ n` adds no assumption: the proof
turns its security there into a bound negligible in `n` (`exists_negligible_treeGame_le`). The
premise that `family` is a length-preserving PRF, on every key length and every query, is however
stronger than the source's. It implies that the coins `prfCoins family` are pseudorandom
(`PseudorandomFunction.coinIndistinguishable`), but the converse is not proved. The proof passes
through the coin games `coinRealGame` and `coinIdealGame`, but these accept every request word,
and a request of at least `N` bits reaches `family` at its first `N` bits, so they expose `family`
on every `N`-bit input as its own PRF games do. A faithful Theorem 14.6 needs the coin games
restricted to the tree's requests at the parameters `coinParam budget n`, and a proof that
`treeCoinAdversary` stays in that domain.

Starting from `treeGame` (`TreeSignature.scheme`'s `eufCmaGame`), the reduction is split into four
focused companion modules after the PRF-to-random-function coin hybrid
(`CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid`):

* `CslibFrontier.Crypto.Computational.TreeSignature.Reduction`: coin-request width/injectivity
  lemmas, `lazyTreeGame`, and the planted-node reduction `indexedForger`.
* `CslibFrontier.Crypto.Computational.TreeSignature.ForgerEfficiency`: strict oracle-PPT
  certificate `isOraclePPT_indexedForger`.
* `CslibFrontier.Crypto.Computational.TreeSignature.IdealToLazy`: birthday bound replacing the
  uniform random function in `treeIdealGame` with lazy node keys, lazy edge signatures, and
  leaf-collision aborts (`succProbability_treeIdealGame_le_lazy`, losing at most
  `(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)`).
* `CslibFrontier.Crypto.Computational.TreeSignature.LazyToIndexed`: plug-and-pray reduction from
  `lazyTreeGame` to `S.indexedEufCmaGame` (`succProbability_lazyTreeGame_le`, losing a factor
  `dyadicSize (slotBound n)` when `Q * depth n ≤ slotBound n`).

Both game hops share the leaf-guarded signing handler combinators in
`CslibFrontier.Crypto.Computational.TreeSignature.Handlers`. This module assembles the concrete
and asymptotic security theorems and existential upgrades.

Combining this upgrade with `OneWay.exists_pseudorandomFunction` and `OneWay.exists_indexedEUFCMA`
constructs a stateless EUF-CMA secure signature scheme from a one-way function and a
collision-resistant hash family (`OneWay.exists_eufCMA_of_hashFamily`). With target
collision-resistant hashing from inaccessible entropy in place of the collision-resistant hash
family, `CslibFrontier.Crypto.Computational.Rompel` removes that assumption: every uniform `OneWay`
function yields a stateless many-time `SignatureScheme` satisfying `EUFCMA`
(`OneWay.exists_eufCMA`, [Rompel1990]).

## Main results

* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay`,
  `Cslib.Crypto.OneWay.exists_eufCMA_of_hashFamily`: existential upgrades from indexed signatures
  and a one-way function, and from a one-way function plus a collision-resistant hash family.

## Steps toward Theorem 14.6 with `q = 2`

* `Cslib.Crypto.TreeSignature.succProbability_treeIdealGame_le`,
  `Cslib.Crypto.TreeSignature.succProbability_eufCmaGame_scheme_le`: concrete bounds for
  `treeIdealGame` and `TreeSignature.scheme`.
* `Cslib.Crypto.TreeSignature.eufCMA_scheme_of_prf_of_inv`,
  `Cslib.Crypto.TreeSignature.eufCMA_scheme_of_prf`: stateless EUF-CMA security of
  `TreeSignature.scheme` from `IndexedEUFCMA` and a length-preserving `PseudorandomFunction`, a
  premise stronger than the source's.
* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf`: the existential form.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 14.6.3, Theorem 14.6, p. 600.
* [J. Rompel, *One-Way Functions are Necessary and Sufficient for Secure Signatures*][Rompel1990].
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped NNReal

namespace TreeSignature

/-- **Concrete security of `treeIdealGame`** (a step of the proof of [BonehShoup2023],
Theorem 14.6): combining the lazy-coin leaf-collision hybrid and the planted-node indexed-forgery
reduction. -/
theorem succProbability_treeIdealGame_le (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N slotBound sigCap : ℕ → ℕ) {n Q : ℕ}
    (hcap : 2 ≤ S.capacity n) (hdepth_pos : 1 ≤ depth n)
    (hwidth : 2 * depth n + 4 ≤ N n) (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ N n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) ≤
      dyadicSize (slotBound n) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) +
        (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) :=
  (succProbability_treeIdealGame_le_lazy S T depth N hdepth_pos hwidth hkgBudget hsgBudget
    adversary hq).trans
    (add_le_add
      (succProbability_lazyTreeGame_le S depth slotBound sigCap hcap hdepth_pos hslot hsigCap
        adversary hq) le_rfl)

/-- Concrete bound for `TreeSignature.scheme` at one parameter `n`, a step toward
[BonehShoup2023], Section 14.6.3, Theorem 14.6, p. 600, in the binary case `q = 2`, not the cited
result: the forging probability of any `Q`-query forger against `TreeSignature.scheme` with
`prfCoins family` is bounded by the PRF distinguishing advantage of
`coinDistinguisher (treeCoinAdversary …)` at `N n`, plus `dyadicSize (slotBound n)` times
`indexedForger`'s indexed forging probability against `S`, plus
`(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)`. The source's terms are `Q d · iSIGadv` and
`Q ^ 2 / (2 q ^ d)`; general `q` is not formalized (#5293). -/
theorem succProbability_eufCmaGame_scheme_le (S : IndexedSignatureScheme) (T : S.Seeded)
    (family : List Bool → List Bool → List Bool)
    (depth N inv slotBound sigCap : ℕ → ℕ)
    (hcoins : ComputableInPolyTime
      (fun ((k, input, length) : List Bool × List Bool × ℕ) => prfCoins family k input length)
      (encPair encBits (encPair encBits encUnary)) encBits)
    (hN : ComputableInPolyTime N encUnary encUnary)
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n)
    (hinv : ∀ n, inv (N n) = n)
    {n Q : ℕ} (hwidth : 2 * depth n + 4 ≤ N n) (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ N n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval
        ((scheme S T (prfCoins family) N depth hcoins hN hdepth hcap hdepth_pos).eufCmaGame
          adversary n)) ≤
      Game.advantage
        (ProbComp.eval (prfRealGame id family
          (coinDistinguisher (treeCoinAdversary S T depth N inv adversary)) (N n)))
        (ProbComp.eval (prfIdealGame id id
          (coinDistinguisher (treeCoinAdversary S T depth N inv adversary)) (N n))) +
      dyadicSize (slotBound n) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) +
      (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) := by
  rw [eufCmaGame_scheme]
  refine (succProbability_treeGame_le_prf (S := S) (T := T) (depth := depth) (N := N)
    family hinv adversary n).trans ((add_le_add (succProbability_treeIdealGame_le S T depth N
      slotBound sigCap (hcap n) (hdepth_pos n) hwidth hkgBudget hsgBudget hslot hsigCap
      adversary hq) le_rfl).trans_eq (by ring))

/-- Step toward [BonehShoup2023], Section 14.6.3, Theorem 14.6, p. 600, in the binary case
`q = 2`, not the cited result: its PRF premise is stronger than the source's (#5293). This is
`eufCMA_scheme_of_prf` with a general PRF parameter `N` and an explicit left inverse: if `S` is
indexed EUF-CMA secure with capacity at least `2`, `family` is a length-preserving pseudorandom
function, `N` covers all tree coin requests and has a polynomial-time left inverse `inv`, and
`(1 : ℝ≥0) / 2 ^ depth n` is negligible, then `TreeSignature.scheme` is stateless EUF-CMA secure.
The premise and the other deviations are those of `eufCMA_scheme_of_prf`, with `N` in place of
`coinParam budget`. -/
theorem eufCMA_scheme_of_prf_of_inv (S : IndexedSignatureScheme) (hS : S.IndexedEUFCMA)
    (T : S.Seeded) {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {depth N inv : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hN : ComputableInPolyTime N encUnary encUnary)
    (hinvPoly : ComputableInPolyTime inv encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n)
    (hNge : ∀ n, n ≤ N n) (hinv : ∀ n, inv (N n) = n)
    (hwidth : ∀ n, 2 * depth n + 4 ≤ N n) (hkgBudget : ∀ n, T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ N n)
    (hdepthNeg : Negligible (fun n => (1 : ℝ≥0) / 2 ^ depth n)) :
    (scheme S T (prfCoins family) N depth
      (computableInPolyTime_prfCoins hF.polyTime) hN hdepth hcap hdepth_pos).EUFCMA := by
  obtain ⟨sigCap, hsigCapPoly, hsigCap⟩ := exists_sigCap_polyTime S
  obtain ⟨ck, dk, hkgLen⟩ := S.keyGen_ppt.length_le
  simp only [encUnary_apply, List.length_replicate] at hkgLen
  apply SignatureScheme.EUFCMA.of_negligible
  intro adversary hA
  simp only [eufCmaGame_scheme]
  obtain ⟨εPrf, hεPrfNeg, hprfLe⟩ :=
    exists_negligible_treeGame_le S T depth N hF hdepth hN hNge hinvPoly hinv hA
  obtain ⟨cq, dq, hqb⟩ := hA.query_bounds
  let Q (n : ℕ) : ℕ := cq * (3 * n + ck * (n + 1) ^ dk + 3) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by dsimp only [Q]; fun_prop
  let slotBound (n : ℕ) : ℕ := Q n * depth n
  have hIdxNeg := hS.negligible (indexedForger S depth slotBound sigCap adversary)
    (isOraclePPT_indexedForger S hdepth (hQPoly.unary_mul' hdepth) hsigCapPoly hA)
  have hbound (n : ℕ) : Game.succProbability
        (ProbComp.eval (treeGame S T depth N (prfCoins family) adversary n)) ≤
      (dyadicSize (slotBound n) : ℝ≥0) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) +
      (Q n ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) + εPrf n := by
    have hqBound : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
        (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded (Q n) :=
      fun root hroot => by
        have hrk : root.1.length ≤ ck * (n + 1) ^ dk := by
          simpa only [encBits_apply] using
            (length_le_encPair_left encBits encBits root).trans (hkgLen n root hroot)
        have hpkLen : (encPair encUnary encBits (n, root.1)).length =
            2 * n + 1 + root.1.length := by
          simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
        exact (hqb n _).1.mono (Nat.mul_le_mul_left cq (Nat.pow_le_pow_left (by omega) dq))
    exact (hprfLe n).trans (add_le_add (succProbability_treeIdealGame_le S T depth N slotBound
      sigCap (hcap n) (hdepth_pos n) (hwidth n) (hkgBudget n) (hsgBudget n) le_rfl (hsigCap n)
      adversary hqBound) le_rfl)
  negligible using hbound

/-- Step toward [BonehShoup2023], Section 14.6.3, Theorem 14.6, p. 600, in the binary case
`q = 2`, not the cited result: its PRF premise `hF` is stronger than the source's (#5293). If `S`
is indexed EUF-CMA secure with capacity at least `2`, used at indices `0` and `1` only, `family`
is a length-preserving pseudorandom function, `budget` covers all tree coin requests, and
`(1 : ℝ≥0) / 2 ^ depth n` is negligible, then `TreeSignature.scheme` with coins `prfCoins family`
at the PRF parameter `coinParam budget n` is stateless EUF-CMA secure.

Theorem 14.6 assumes only that its coin function `F`, defined over
`(K, {1, …, q} ^ {≤ d}, {0, 1} ^ w)`, is a PRF. Here the coins are `prfCoins family`: `family` at
the padded request, truncated. The premise `hF` asks that `family` be a PRF on every key length
and every query. It implies that the coins are pseudorandom
(`PseudorandomFunction.coinIndistinguishable`), but the converse is not proved. The proof passes
through that coin indistinguishability, but over every request word and every PRF parameter, and a
request of at least `N` bits reaches `family` at its first `N` bits, so those games expose `family`
on every `N`-bit input as its own PRF games do. Theorem 14.6 itself needs the coin games
restricted to the tree's requests at the parameters `coinParam budget n`. The rescaled parameter
adds no assumption, since the proof turns the PRF's security at `coinParam budget n ≥ n` into a
bound negligible in `n`.

The other deviations: the tree is binary, so the source's condition that `q ^ d` is super-poly is
`hdepthNeg`, and general `q` is not formalized (#5293); and the outer messages are `n`-bit. -/
theorem eufCMA_scheme_of_prf (S : IndexedSignatureScheme) (hS : S.IndexedEUFCMA) (T : S.Seeded)
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family)
    {depth budget : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hbudget : ComputableInPolyTime budget encUnary encUnary)
    (hcap : ∀ n, 2 ≤ S.capacity n) (hdepth_pos : ∀ n, 1 ≤ depth n)
    (hwidth : ∀ n, 2 * depth n + 4 ≤ budget n) (hkgBudget : ∀ n, T.keyGenBudget n ≤ budget n)
    (hsgBudget : ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ budget n)
    (hdepthNeg : Negligible (fun n => (1 : ℝ≥0) / 2 ^ depth n)) :
    (scheme S T (prfCoins family) (coinParam budget) depth
      (computableInPolyTime_prfCoins hF.polyTime)
      (computableInPolyTime_coinParam hbudget) hdepth hcap hdepth_pos).EUFCMA :=
  eufCMA_scheme_of_prf_of_inv S hS T hF hdepth
    (computableInPolyTime_coinParam hbudget)
    (computableInPolyTime_coinParamInv hbudget)
    hcap hdepth_pos (le_coinParam budget) (coinParamInv_coinParam budget)
    (fun n => (hwidth n).trans (lt_coinParam budget n).le)
    (fun n => (hkgBudget n).trans (lt_coinParam budget n).le)
    (fun n keys hk u hu msg hm =>
      (hsgBudget n keys hk u hu msg hm).trans (lt_coinParam budget n).le)
    hdepthNeg

/-- Corollary of the step `eufCMA_scheme_of_prf` toward [BonehShoup2023], Section 14.6.3,
Theorem 14.6, p. 600, with `q = 2`, not the cited result: any indexed EUF-CMA secure signature
scheme of capacity at least `2` and any length-preserving pseudorandom function yield a stateless
EUF-CMA secure signature scheme on `n`-bit messages. The scheme is `TreeSignature.scheme` with
depth `n + 1`, so that `2 ^ (n + 1)` is super-poly, and coins `prfCoins family`. The premise `hF`
is stronger than the source's PRF premise on the coins, as `eufCMA_scheme_of_prf` explains
(#5293). -/
theorem _root_.Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_prf
    {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA) (hcap : ∀ n, 2 ≤ S.capacity n)
    {family : List Bool → List Bool → List Bool} (hF : PseudorandomFunction family) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  let T := S.seeded
  let depth : ℕ → ℕ := fun n => n + 1
  have hdepth : ComputableInPolyTime depth encUnary encUnary :=
    (ComputableInPolyTime.id' (encIn := encUnary)).unary_add' (.const 1)
  have hdepth_pos : ∀ n, 1 ≤ depth n := fun _ => Nat.le_add_left 1 _
  have hdepthNeg : Negligible (fun n => (1 : ℝ≥0) / 2 ^ depth n) :=
    negligible_inv_two_pow_of_le fun n => Nat.le_succ n
  obtain ⟨budget, hbudget, hwidth, hkgB, hsgB⟩ := exists_treeCoinBudget S T hdepth
  exact ⟨scheme S T (prfCoins family) (coinParam budget) depth
      (computableInPolyTime_prfCoins hF.polyTime)
      (computableInPolyTime_coinParam hbudget) hdepth hcap hdepth_pos,
    eufCMA_scheme_of_prf S hS T hF hdepth hbudget hcap hdepth_pos hwidth hkgB hsgB hdepthNeg⟩

/-- **Stateless many-time signatures from indexed signatures and one-way functions**: any indexed
EUF-CMA secure signature scheme of capacity at least `2` and any one-way function yield a stateless
EUF-CMA secure signature scheme. -/
theorem _root_.Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay
    {S : IndexedSignatureScheme} (hS : S.IndexedEUFCMA) (hcap : ∀ n, 2 ≤ S.capacity n)
    {f : List Bool → List Bool} (hf : OneWay f) :
    ∃ M : SignatureScheme, M.EUFCMA :=
  let ⟨_, hF⟩ := hf.exists_pseudorandomFunction; hS.exists_eufCMA_of_prf hcap hF

/-- **Stateless many-time signatures from one-way functions and collision-resistant hash families**:
combining Lamport one-time signatures, depth-`1` Merkle trees (capacity `2`), PRFs from one-way
functions, and stateless tree signatures yields a stateless EUF-CMA secure signature scheme. -/
theorem _root_.Cslib.Crypto.OneWay.exists_eufCMA_of_hashFamily
    {f : List Bool → List Bool} (hf : OneWay f)
    {H : List Bool → List Bool → List Bool} (hH : HashFamily H) :
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨S, hcapS, hS⟩ :=
    hf.exists_indexedEUFCMA hH (depth := fun _ => 1) (ComputableInPolyTime.const 2)
  exact hS.exists_eufCMA_of_oneWay (fun n => by rw [hcapS n]; decide) hf

end TreeSignature

end Cslib.Crypto
