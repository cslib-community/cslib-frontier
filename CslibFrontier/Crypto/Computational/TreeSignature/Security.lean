/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Mathlib.Data.List.GetD
public import CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid
public import CslibFrontier.Crypto.Computational.CollisionResistant
public import CslibFrontier.Crypto.Computational.OneWay
public import CslibFrontier.Crypto.Negligible.Dyadic
public import CslibFrontier.Languages.Probabilistic.Repeat
public import CslibFrontier.Languages.Probabilistic.UniformNat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Eq
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.BitString
import CslibFrontier.Computability.Probabilistic.Oracle.Composition
import CslibFrontier.Computability.Probabilistic.Oracle.Memoize
import CslibFrontier.Computability.Probabilistic.Oracle.Substitution
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.QueryBounds
import CslibFrontier.Computability.Probabilistic.Repeat
import CslibFrontier.Computability.Probabilistic.Sampling
import CslibFrontier.Computability.Probabilistic.UniformNat
import CslibFrontier.Crypto.Computational.MerkleSignature.Security
import CslibFrontier.Crypto.Computational.OneWayToPRF
import CslibFrontier.Foundations.Data.List.GetD
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
import CslibFrontier.Languages.Probabilistic.Iteration.Chain
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm
import CslibFrontier.Languages.Probabilistic.Oracle.QueryBoundedSimulation
import CslibFrontier.Languages.Probabilistic.Oracle.Simulation
import CslibFrontier.Languages.Probabilistic.Oracle.Support
import CslibFrontier.Languages.Probabilistic.RandomOracle.Probabilistic
import CslibFrontier.Languages.Probabilistic.UntilBad.Flag
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.Coupling
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.EncLen
import CslibFrontier.Tactic.SuppCases

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

Starting from `treeGame` (`TreeSignature.scheme`'s `eufCmaGame`), the reduction proceeds in two
steps after replacing `prfCoins F` with a uniform random function (`treeIdealGame`, proved in
`CslibFrontier.Crypto.Computational.TreeSignature.CoinHybrid`):

1. **Lazy node keys and edge signatures without leaf collisions** (`lazyTreeGame`): when `N n`
   exceeds all coin-request lengths (`2 * depth n + 4 ≤ N n`) and all seeded key/signature coin
   budgets on supported keys and messages, distinct tree nodes and `(node, bit)` edges pad to
   distinct random-function inputs. Guarding against repeated leaves across `Q` signing queries adds
   at most `(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)` by `OracleComp.IdenticalUntilBad`, and on good runs
   every node key is distributed as `S.keyGen n` and every edge signature as `S.sign`.
2. **Reduction to indexed forgery** (`indexedForger`): pre-sampling `dyadicSize (slotBound n)` node
   keys and planting the indexed challenge verification key at a uniform dyadic slot `target`
   simulates `lazyTreeGame` exactly whenever `Q * depth n ≤ slotBound n`. Any valid tree forgery on
   a fresh `n`-bit message diverges from the visited tree or forges at a leaf parent, yielding a
   valid indexed forgery at the deepest matching visited node along the forged path.

Combining this upgrade with `OneWay.exists_pseudorandomFunction` and `OneWay.exists_indexedEUFCMA`
constructs a stateless EUF-CMA secure signature scheme from a one-way function and a
collision-resistant hash family (`OneWay.exists_eufCMA_of_hashFamily`). With target
collision-resistant hashing from inaccessible entropy in place of the collision-resistant hash
family, `CslibFrontier.Crypto.Computational.Rompel` removes that assumption: every uniform `OneWay`
function yields a stateless many-time `SignatureScheme` satisfying `EUFCMA`
(`OneWay.exists_eufCMA`, [Rompel1990]).

## Main definitions

* `Cslib.Crypto.TreeSignature.lazyTreeGame`: intermediate tree forging game with lazy node keys,
  lazy edge signatures, and leaf-collision abort.
* `Cslib.Crypto.TreeSignature.plantNodeKeys`, `Cslib.Crypto.TreeSignature.plantedTreeHandler`,
  `Cslib.Crypto.TreeSignature.extractForgery`, `Cslib.Crypto.TreeSignature.indexedForgerAt`,
  `Cslib.Crypto.TreeSignature.indexedForger`: the reduction from stateless tree forgery to indexed
  forgery.

## Main results

* `Cslib.Crypto.TreeSignature.exists_treeCoinBudget`: polynomial-time unary coin budget covering
  all tree request widths and seeded key/signature budgets.
* `Cslib.Crypto.TreeSignature.isOraclePPT_indexedForger`: `indexedForger` is uniformly strict
  oracle PPT for every oracle-PPT tree forger.
* `Cslib.Crypto.IndexedSignatureScheme.IndexedEUFCMA.exists_eufCMA_of_oneWay`,
  `Cslib.Crypto.OneWay.exists_eufCMA_of_hashFamily`: existential upgrades from indexed signatures
  and a one-way function, and from a one-way function plus a collision-resistant hash family.

## Steps toward Theorem 14.6 with `q = 2`

* `Cslib.Crypto.TreeSignature.succProbability_treeIdealGame_le_lazy`,
  `Cslib.Crypto.TreeSignature.succProbability_lazyTreeGame_le`,
  `Cslib.Crypto.TreeSignature.succProbability_treeIdealGame_le`,
  `Cslib.Crypto.TreeSignature.succProbability_eufCmaGame_scheme_le`: concrete bounds for
  `treeIdealGame`, `lazyTreeGame`, and `TreeSignature.scheme`.
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
open scoped NNReal ENNReal

namespace TreeSignature

attribute [local fun_prop]
  ComputableInPolyTime.bool_and'
  ComputableInPolyTime.unary_dyadicSize
  IsPPTOn.replicate

@[local fun_prop]
private theorem headD_list_fp {α β : Type} {encA : α ↪ List Bool} {encB : β ↪ List Bool}
    {l : α → List β} (hl : ComputableInPolyTime l encA (encList encB)) (d : β) :
    ComputableInPolyTime (fun a => (l a).headD d) encA encB :=
  (ComputableInPolyTime.headD (encA := encB) (encL := encList encB) d).comp hl

@[local fun_prop]
private theorem getLastD_fp {α : Type} {encA : α ↪ List Bool} {l : α → List Bool} (d : Bool)
    (hl : ComputableInPolyTime l encA encBits) :
    ComputableInPolyTime (fun a => (l a).getLastD d) encA encBool := by
  have heq : (fun a => (l a).getLastD d) = fun a => (l a).getD ((l a).length - 1) d := by
    funext a
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD]
  rw [heq]; fun_prop

@[local fun_prop]
private theorem contains_fp {α β : Type} [BEq β] [LawfulBEq β] {encA : α ↪ List Bool}
    {encB : β ↪ List Bool} {l : α → List β} {x : α → β}
    (hl : ComputableInPolyTime l encA (encList encB))
    (hx : ComputableInPolyTime x encA encB) :
    ComputableInPolyTime (fun a => (l a).contains (x a)) encA encBool := by
  have heq : (fun a => (l a).contains (x a)) = fun a => (l a).any (fun b => b == x a) := by
    funext a
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.any_eq_true]
    simp only [beq_iff_eq, exists_eq_right]
  rw [heq]
  exact ComputableInPolyTime.anyWithInput hl
    ((ComputableInPolyTime.snd encA encB).beq (hx.comp (ComputableInPolyTime.fst encA encB)))

@[local fun_prop]
private theorem encodeSignature_funProp {α : Type} {encA : α ↪ List Bool}
    {leaf : α → List Bool} {certs : α → List (List Bool × List Bool)} {last : α → List Bool}
    (hl : ComputableInPolyTime leaf encA encBits)
    (hc : ComputableInPolyTime certs encA (encList (encPair encBits encBits)))
    (hs : ComputableInPolyTime last encA encBits) :
    ComputableInPolyTime (fun a => encodeSignature (leaf a) (certs a) (last a)) encA encBits := by
  unfold encodeSignature; fun_prop

@[local fun_prop]
private theorem signatureDecoder_funProp {α : Type} {encA : α ↪ List Bool} {s : α → List Bool}
    (hs : ComputableInPolyTime s encA encBits) :
    ComputableInPolyTime (fun a => signatureDecoder.decode (s a)) encA
      (encPair encBits (encPair (encList (encPair encBits encBits)) encBits)) :=
  signatureDecoder.computableInPolyTime.comp hs

private theorem exists_signInput_length_bound (S : IndexedSignatureScheme) :
    ∃ pkB : ℕ → ℕ,
      ComputableInPolyTime pkB encUnary encUnary ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
        (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
        (encPair encBits (encPair encUnary encBits) (keys.2, u, msg)).length + 1 ≤
          3 * pkB n + n + 5 := by
  obtain ⟨ck, dk, hkgLen⟩ := S.keyGen_ppt.length_le
  simp only [encUnary_apply, List.length_replicate] at hkgLen
  refine ⟨fun n => ck * (n + 1) ^ dk, by fun_prop, fun n keys hkeys u hu msg hmsg => ?_⟩
  have hskLen : keys.2.length ≤ ck * (n + 1) ^ dk :=
    (length_le_encPair_right encBits encBits keys).trans (hkgLen n keys hkeys)
  have hmsgLen : msg.length ≤ ck * (n + 1) ^ dk + n := by
    rcases hmsg with rfl | ⟨keys', hkeys', rfl⟩
    · omega
    · have hk' := (length_le_encPair_left encBits encBits keys').trans (hkgLen n keys' hkeys')
      simp only [encBits_apply] at hk'
      omega
  enc_len

/-! ### Request lengths, injectivity, and coin budgets -/

section Requests

theorem length_keyInput (path : List Bool) : (keyInput path).length = path.length + 3 := by
  enc_len [keyInput, List.length_singleton]

theorem length_signInput (path : List Bool) (u : ℕ) :
    (signInput path u).length = 2 * path.length + u + 4 := by
  enc_len [signInput, List.length_singleton]

theorem keyInput_injective : Function.Injective keyInput := by
  intro p q h
  exact (Prod.mk.inj ((encPair encBool encBits).injective h)).2

theorem signInput_injective {p q : List Bool} {u v : ℕ} (h : signInput p u = signInput q v) :
    p = q ∧ u = v :=
  Prod.mk.inj (Prod.mk.inj ((encPair encBool (encPair encBits encUnary)).injective h)).2

theorem keyInput_ne_signInput (p q : List Bool) (u : ℕ) : keyInput p ≠ signInput q u := by
  intro h
  have hu := congrArg unframe h
  simp only [keyInput, signInput, encPair_apply, unframe_frame_append] at hu
  exact Bool.false_ne_true (encBool.injective hu)

theorem padRequest_keyInput_injective {M d : ℕ} (hM : 2 * d + 4 ≤ M) {p q : List Bool}
    (hp : p.length < d) (hq : q.length < d)
    (h : padRequest M (keyInput p) = padRequest M (keyInput q)) : p = q := by
  apply keyInput_injective
  apply padRequest_injective _ _ h
  · rw [length_keyInput]; omega
  · rw [length_keyInput]; omega

theorem padRequest_signInput_injective {M d : ℕ} (hM : 2 * d + 4 ≤ M) {p q : List Bool}
    {u v : ℕ} (hp : p.length < d) (hq : q.length < d) (hu : u ≤ 1) (hv : v ≤ 1)
    (h : padRequest M (signInput p u) = padRequest M (signInput q v)) : p = q ∧ u = v := by
  apply signInput_injective
  apply padRequest_injective _ _ h
  · rw [length_signInput]; omega
  · rw [length_signInput]; omega

theorem padRequest_keyInput_ne_signInput {M d : ℕ} (hM : 2 * d + 4 ≤ M) {p q : List Bool}
    {u : ℕ} (hp : p.length < d) (hq : q.length < d) (hu : u ≤ 1) :
    padRequest M (keyInput p) ≠ padRequest M (signInput q u) := by
  intro h
  apply keyInput_ne_signInput p q u
  apply padRequest_injective _ _ h
  · rw [length_keyInput]; omega
  · rw [length_signInput]; omega

/-- Every seeded indexed signature scheme admits a polynomial-time unary coin budget covering all
tree request widths (`2 * depth n + 4`), key-generation budgets, and signing budgets on supported
keys and messages (`n`-bit messages or supported public keys). -/
theorem exists_treeCoinBudget (S : IndexedSignatureScheme) (T : S.Seeded) {depth : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    ∃ budget : ℕ → ℕ,
      ComputableInPolyTime budget encUnary encUnary ∧
      (∀ n, 2 * depth n + 4 ≤ budget n) ∧
      (∀ n, T.keyGenBudget n ≤ budget n) ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
        (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
        T.signBudget keys.2 u msg ≤ budget n := by
  obtain ⟨pkB, hpkB, hlenB⟩ := exists_signInput_length_bound S
  obtain ⟨cb, db, hkb⟩ := T.keyGenBudget_polyTime.polyBounded_length.exists_le
  obtain ⟨cB, dB, hsb⟩ := T.signBudget_polyTime.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hkb hsb
  let budget (n : ℕ) : ℕ :=
    2 * depth n + 4 + cb * (n + 1) ^ db + cB * (3 * pkB n + n + 5) ^ dB
  refine ⟨budget, by dsimp only [budget]; fun_prop, fun n => by dsimp only [budget]; omega,
    fun n => by have := hkb n; dsimp only [budget]; omega,
    fun n keys hkeys u hu msg hmsg => ?_⟩
  have hle := (hsb (keys.2, u, msg)).trans
    (Nat.mul_le_mul_left cB (Nat.pow_le_pow_left (hlenB n keys hkeys u hu msg hmsg) dB))
  dsimp only [budget] at hle ⊢
  omega

end Requests

/-! ### Lazy tree game and reduction to indexed forgery -/

/-- Association-list cache assigning node paths to pre-sampled slot indices. -/
abbrev NodeSlotCache := List (List Bool × ℕ)

/-- Association-list cache memoizing node keys `(pk, sk)` by path. -/
abbrev NodeKeyCache := List (List Bool × (List Bool × List Bool))

/-- Association-list cache memoizing signatures by `(path, u)`. -/
abbrev EdgeSigCache := List ((List Bool × ℕ) × List Bool)

/-- State of the lazy tree signing handler: node keys, edge signatures, queried messages,
sampled leaves, and the leaf-collision abort flag. -/
abbrev LazyTreeState :=
  (NodeKeyCache × EdgeSigCache) × (List (List Bool) × List (List Bool) × Bool)

/-- Chain state during `certifyLazy`. -/
abbrev LazyCertState := CertState × (NodeKeyCache × EdgeSigCache)

/-- One step of lazy certification along `leaf`: memoize the child's key from `S.keyGen n` and
memoize the parent's signature on the child's public key from `S.sign`. -/
@[expose] noncomputable def certifyStepLazy (S : IndexedSignatureScheme) (n : ℕ)
    (leaf : List Bool) (state : LazyCertState) : ProbComp LazyCertState := do
  let ((node, (_, sk), certs), (nodes, edges)) := state
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (child, nodes') ← memoize (fun _ => S.keyGen n) childPath nodes
  let (σ, edges') ← memoize (fun _ => S.sign sk bit.toNat child.1) (node, bit.toNat) edges
  return ((childPath, child, certs ++ [(child.1, σ)]), (nodes', edges'))

/-- Lazily certify the path along `leaf` from `root` for `depth n - 1` steps. -/
@[expose] noncomputable def certifyLazy (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) (leaf : List Bool) (caches : NodeKeyCache × EdgeSigCache) :
    ProbComp LazyCertState :=
  OracleComp.iterate (depth n - 1) (certifyStepLazy S n leaf) (([], root, []), caches)

/-- Signing handler of `lazyTreeGame`: check `msg.length = n`, sample a uniform leaf, abort with
`[]` if a leaf collision occurs (or has already occurred), and otherwise lazily certify the path
and sign `msg`. -/
@[expose] noncomputable def lazySignHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) (request : Unit × List Bool) :
    StateT LazyTreeState ProbComp (List Bool) := fun state =>
  let msg := request.2
  let ((nodes, edges), (queried, seenLeaves, bad)) := state
  if msg.length = n then
    if bad then
      pure ([], ((nodes, edges), (msg :: queried, seenLeaves, true)))
    else do
      let leaf ← BitString.sampleList (depth n)
      if seenLeaves.contains leaf then
        pure ([], ((nodes, edges), (msg :: queried, seenLeaves, true)))
      else do
        let ((node, (_, sk), certs), (nodes', edges')) ←
          certifyLazy S depth n root leaf (nodes, edges)
        let (σ, edges'') ←
          memoize (fun _ => S.sign sk (leaf.getLastD false).toNat msg)
            (node, (leaf.getLastD false).toNat) edges'
        return (encodeSignature leaf certs σ,
          ((nodes', edges''), (msg :: queried, leaf :: seenLeaves, false)))
  else
    pure ([], ((nodes, edges), (msg :: queried, seenLeaves, bad)))

/-- Intermediate tree forging game ([BonehShoup2023], proof of Theorem 14.6): node keys and
internal/leaf signatures are sampled lazily from `S.keyGen` and `S.sign`, and signing returns `[]`
once any leaf is sampled twice. -/
@[expose] noncomputable def lazyTreeGame (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (adversary : Forger) (n : ℕ) : ProbComp Bool := do
  let root ← S.keyGen n
  let pk := encPair encUnary encBits (n, root.1)
  let init : LazyTreeState := (([([], root)], []), ([], [], false))
  let (msig, state) ← (OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifFin k))
      (lazySignHandler S depth n root)) (adversary n pk)).run init
  let (_, (queried, _, _)) := state
  let (msg, sig) := msig
  return (msg.length == n) && !queried.contains msg && verify S depth pk msg sig

/-! ### The planted-node reduction (`indexedForger`) -/

/-- State of `plantedTreeHandler`: visited node-to-slot cache, edge-signature cache, queried
messages, sampled leaves, and the leaf-collision abort flag. -/
abbrev PlantedState :=
  (NodeSlotCache × EdgeSigCache) × (List (List Bool) × List (List Bool) × Bool)

/-- Initial state of `plantedTreeHandler`: the root `[]` occupies slot `0`. -/
@[expose] def initPlantedState : PlantedState :=
  (([([], 0)], []), ([], [], false))

/-- Pre-sample `dyadicSize (slotBound n)` node key pairs, planting `(vk, [])` at `min target
(dyadicSize (slotBound n) - 1)`. -/
@[expose] noncomputable def plantNodeKeys (S : IndexedSignatureScheme) (slotBound : ℕ → ℕ)
    (n target : ℕ) (vk : List Bool) : ProbComp (List (List Bool × List Bool)) := do
  let total := dyadicSize (slotBound n)
  let idx := min target (total - 1)
  let front ← OracleComp.replicate idx (S.keyGen n)
  let back ← OracleComp.replicate (total - idx - 1) (S.keyGen n)
  return front ++ (vk, []) :: back

/-- Assign `path` its cached slot or the next available slot `min visited.length cap`. -/
@[expose] def visitNodeM (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) :
    WordOracleComp Unit (ℕ × NodeSlotCache) :=
  memoize (fun _ => pure (min visited.length cap)) path visited

/-- Produce an edge signature at slot `idx` and index `u` on `msg`, querying the external indexed
signing oracle when `idx = target` and running `S.sign` locally otherwise, capped at `sigCap`
bits. -/
@[expose] noncomputable def signEdgeRaw (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap idx u : ℕ) (msg : List Bool) :
    WordOracleComp Unit (List Bool) :=
  if idx = target then
    List.take sigCap <$> ProbOracleComp.query ((), encPair encUnary encBits (u, msg))
  else
    List.take sigCap <$> ProbOracleComp.sample (S.sign (keys.getD idx ([], [])).2 u msg)

/-- Memoize `signEdgeRaw` on `(path, u)` in `edges`. -/
@[expose] noncomputable def signEdgeM (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap : ℕ) (path : List Bool) (idx u : ℕ)
    (msg : List Bool) (edges : EdgeSigCache) :
    WordOracleComp Unit (List Bool × EdgeSigCache) :=
  memoize (fun _ => signEdgeRaw S keys target sigCap idx u msg) (path, u) edges

/-- Chain state during `certifyPlanted`: `(path, slotIdx, certs)` paired with `(visited, edges)`. -/
abbrev PlantedCertState :=
  (List Bool × ℕ × List (List Bool × List Bool)) × (NodeSlotCache × EdgeSigCache)

/-- One step of planted certification along `leaf`. -/
@[expose] noncomputable def certifyStepPlanted (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap : ℕ) (leaf : List Bool)
    (state : PlantedCertState) : WordOracleComp Unit PlantedCertState := do
  let ((node, idx, certs), (visited, edges)) := state
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, visited') ← visitNodeM keys.length childPath visited
  let childPk := (keys.getD childIdx ([], [])).1
  let (σ, edges') ← signEdgeM S keys target sigCap node idx bit.toNat childPk edges
  return ((childPath, childIdx, certs ++ [(childPk, σ)]), (visited', edges'))

/-- Certify `depth n - 1` steps from the root `[]` at slot `0` using planted keys. -/
@[expose] noncomputable def certifyPlanted (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (target sigCap n : ℕ) (leaf : List Bool)
    (caches : NodeSlotCache × EdgeSigCache) : WordOracleComp Unit PlantedCertState :=
  OracleComp.iterate (depth n - 1) (certifyStepPlanted S keys target sigCap leaf)
    (([], 0, []), caches)

/-- Signing handler of `indexedForgerAt`: answer `n`-bit signing queries along uniform leaves,
aborting with `[]` on leaf collisions, and delegating signatures at slot `target` to the external
indexed signing oracle. -/
@[expose] noncomputable def plantedTreeHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (target sigCap n : ℕ) (request : Unit × List Bool) :
    StateT PlantedState (WordOracleComp Unit) (List Bool) := fun state =>
  let msg := request.2
  let ((visited, edges), (queried, seenLeaves, bad)) := state
  if msg.length = n then
    if bad then
      pure ([], ((visited, edges), (msg :: queried, seenLeaves, true)))
    else do
      let leaf ← ProbOracleComp.sample (BitString.sampleList (depth n))
      if seenLeaves.contains leaf then
        pure ([], ((visited, edges), (msg :: queried, seenLeaves, true)))
      else do
        let ((node, idx, certs), (visited', edges')) ←
          certifyPlanted S depth keys target sigCap n leaf (visited, edges)
        let (σ, edges'') ←
          signEdgeM S keys target sigCap node idx (leaf.getLastD false).toNat msg edges'
        return (encodeSignature leaf certs σ,
          ((visited', edges''), (msg :: queried, leaf :: seenLeaves, false)))
  else
    pure ([], ((visited, edges), (msg :: queried, seenLeaves, bad)))

/-- Extract a candidate indexed forgery `(u, m, σ)` for the key planted at `target` from a tree
forgery `(msg, sig)` and the visited-node cache `visited`: look up the unique path assigned to
`target`, and output either the child-key certificate at depth `path.length` (when internal) or the
final message signature `(u, msg, last)` (when at depth `d - 1`). -/
@[expose] def extractForgery (d target : ℕ) (visited : NodeSlotCache) (msg sig : List Bool) :
    ℕ × List Bool × List Bool :=
  let (leaf, certs, last) := signatureDecoder.decode sig
  let path := ((visited.filter fun e => e.2 == target).headD ([], 0)).1
  let j := path.length
  let u := (leaf.getD j false).toNat
  if j + 1 < d then
    let (childPk, childSig) := certs.getD j ([], [])
    (u, childPk, childSig)
  else
    (u, msg, last)

/-- The indexed forger with its challenge verification key planted at slot `target`. -/
@[expose] noncomputable def indexedForgerAt (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (target : ℕ) : IndexedForger :=
  fun n vk => do
    let keys ← ProbOracleComp.sample (plantNodeKeys S slotBound n target vk)
    let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
    let (msig, state) ← (OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbOracleComp.sample (ProbComp.unifFin j)))
        (plantedTreeHandler S depth keys target (sigCap n) n))
      (adversary n pk)).run initPlantedState
    let ((visited, _), _) := state
    let (msg, sig) := msig
    return extractForgery (depth n) target visited msg sig

/-- The indexed forger: sample a uniform dyadic slot `target < dyadicSize (slotBound n)` and run
`indexedForgerAt`. -/
@[expose] noncomputable def indexedForger (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) : IndexedForger :=
  fun n vk => do
    let target ← ProbOracleComp.sample (ProbComp.sampleDyadicIndex (slotBound n))
    indexedForgerAt S depth slotBound sigCap adversary target n vk

/-! ### Strict oracle-PPT certificate for `indexedForger` -/

section ForgerEfficiency

/-- The visited node-to-slot cache, encoded as a list of entries; each entry is a node path in
binary followed by its slot in unary, the path framed. -/
private abbrev encNodeCache : NodeSlotCache ↪ List Bool :=
  encList (encPair encBits encUnary)

/-- The edge-signature cache, encoded as a list of entries; each entry is an edge (a node path in
binary followed by the edge bit in unary, the path framed), framed, followed by its signature in
binary. -/
private abbrev encEdgeCache : EdgeSigCache ↪ List Bool :=
  encList (encPair (encPair encBits encUnary) encBits)

/-- A list of pairs of words, such as the pre-sampled node key pairs or a certificate chain;
each pair is its first word in binary, framed, followed by its second word in binary. -/
private abbrev encKeys : List (List Bool × List Bool) ↪ List Bool :=
  encList (encPair encBits encBits)

/-- The state of `plantedTreeHandler`, encoded as a nested pair: the visited node cache (framed)
and the edge-signature cache, framed together, followed by the queried messages (framed), the
sampled leaves (framed) and the abort flag. Each list holds its words in binary. -/
private abbrev encPlantedState : PlantedState ↪ List Bool :=
  encPair (encPair encNodeCache encEdgeCache)
    (encPair (encList encBits) (encPair (encList encBits) encBool))

/-- The chain state of `certifyPlanted`, encoded as a nested pair: the node path in binary
(framed), the slot in unary (framed) and the certificates (key/signature word pairs, `encKeys`),
framed together, followed by the visited node cache (framed) and the edge-signature cache. -/
private abbrev encPlantedCert : PlantedCertState ↪ List Bool :=
  encPair (encPair encBits (encPair encUnary encKeys)) (encPair encNodeCache encEdgeCache)

private theorem length_fst_getD_keys_le (keys : List (List Bool × List Bool)) (idx : ℕ) :
    (keys.getD idx ([], [])).1.length ≤ (encKeys keys).length := by
  by_cases h : idx < keys.length
  · exact (length_le_encPair_left encBits encBits _).trans
      (length_le_encList_of_mem (encPair encBits encBits) (List.getD_mem _ h))
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h)]
    exact Nat.zero_le _

@[local fun_prop]
private theorem isPPTOn_plantNodeKeys (S : IndexedSignatureScheme) {slotBound : ℕ → ℕ}
    (hslot : ComputableInPolyTime slotBound encUnary encUnary) :
    IsPPTOn (encPair (encPair encUnary encBits) encUnary) encKeys
      (fun c : (ℕ × List Bool) × ℕ => plantNodeKeys S slotBound c.1.1 c.2 c.1.2) := by
  have _ := S.keyGen_ppt
  dsimp only [plantNodeKeys]
  fun_prop

@[local fun_prop]
private theorem isOraclePPTOn_visitNodeM {γ : Type} {enc : γ ↪ List Bool}
    {cap : γ → ℕ} {path : γ → List Bool} {visited : γ → NodeSlotCache}
    (hcap : ComputableInPolyTime cap enc encUnary)
    (hpath : ComputableInPolyTime path enc encBits)
    (hvisited : ComputableInPolyTime visited enc encNodeCache) :
    IsOraclePPTOn enc (encPair encUnary encNodeCache)
      (fun a => visitNodeM (cap a) (path a) (visited a)) :=
  IsOraclePPTOn.memoize (compute := fun a _ => pure (min (visited a).length (cap a)))
    (ComputableInPolyTime.isOraclePPTOn (by fun_prop)) hpath hvisited

@[local fun_prop]
private theorem isOraclePPTOn_signEdgeM (S : IndexedSignatureScheme) {γ : Type}
    {enc : γ ↪ List Bool} {keys : γ → List (List Bool × List Bool)}
    {target sigCap idx u : γ → ℕ} {path msg : γ → List Bool} {edges : γ → EdgeSigCache}
    (hkeys : ComputableInPolyTime keys enc encKeys)
    (htarget : ComputableInPolyTime target enc encUnary)
    (hsigCap : ComputableInPolyTime sigCap enc encUnary)
    (hpath : ComputableInPolyTime path enc encBits)
    (hidx : ComputableInPolyTime idx enc encUnary)
    (hu : ComputableInPolyTime u enc encUnary)
    (hmsg : ComputableInPolyTime msg enc encBits)
    (hedges : ComputableInPolyTime edges enc encEdgeCache) :
    IsOraclePPTOn enc (encPair encBits encEdgeCache)
      (fun a => signEdgeM S (keys a) (target a) (sigCap a) (path a) (idx a) (u a) (msg a)
        (edges a)) := by
  have _ := S.sign_ppt
  unfold signEdgeM signEdgeRaw
  exact IsOraclePPTOn.memoize
    (compute := fun a _ =>
      if idx a = target a then
        List.take (sigCap a) <$> ProbOracleComp.query ((), encPair encUnary encBits (u a, msg a))
      else
        List.take (sigCap a) <$>
          ProbOracleComp.sample (S.sign ((keys a).getD (idx a) ([], [])).2 (u a) (msg a)))
    (IsOraclePPTOn.ite (by fun_prop)
      (IsOraclePPTOn.query_take () (by fun_prop) hsigCap)
      (((S.sign_ppt.preprocess
        (prepare := fun a => (((keys a).getD (idx a) ([], [])).2, u a, msg a))
        (by fun_prop)).isOraclePPTOn (Operation := Unit)).map_with (by fun_prop)))
    (hpath.prod hu) hedges

private theorem length_le_of_mem_support_signEdgeRaw (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (target sigCap idx u : ℕ) (msg : List Bool)
    {σ : List Bool} (hσ : σ ∈ OracleComp.support (signEdgeRaw S keys target sigCap idx u msg)) :
    σ.length ≤ sigCap := by
  unfold signEdgeRaw at hσ
  split_ifs at hσ <;>
    (obtain ⟨_, -, rfl⟩ := OracleComp.mem_supportWith_map_iff.mp hσ; exact List.length_take_le _ _)

/-- Input to `certifyPlanted`: `((keys, (target, sigCap), (n, leaf)), (visited₀, edges₀))`. -/
private abbrev CertLoopIn :=
  (List (List Bool × List Bool) × (ℕ × ℕ) × (ℕ × List Bool)) × (NodeSlotCache × EdgeSigCache)

private abbrev CertLoopIn.keys (a : CertLoopIn) := a.1.1
private abbrev CertLoopIn.target (a : CertLoopIn) := a.1.2.1.1
private abbrev CertLoopIn.sigCap (a : CertLoopIn) := a.1.2.1.2
private abbrev CertLoopIn.parameter (a : CertLoopIn) := a.1.2.2.1
private abbrev CertLoopIn.leaf (a : CertLoopIn) := a.1.2.2.2
private abbrev CertLoopIn.visited (a : CertLoopIn) := a.2.1
private abbrev CertLoopIn.edges (a : CertLoopIn) := a.2.2

private theorem isOraclePPTOn_certifyStepPlanted (S : IndexedSignatureScheme) :
    IsOraclePPTOn
      (encPair (encPair encKeys (encPair (encPair encUnary encUnary) encBits)) encPlantedCert)
      encPlantedCert
      (fun q : (List (List Bool × List Bool) × (ℕ × ℕ) × List Bool) × PlantedCertState =>
        certifyStepPlanted S q.1.1 q.1.2.1.1 q.1.2.1.2 q.1.2.2 q.2) := by
  let encIn :=
    encPair (encPair encKeys (encPair (encPair encUnary encUnary) encBits)) encPlantedCert
  let encMid := encPair encIn (encPair encUnary encNodeCache)
  let encEnd := encPair encMid (encPair encBits encEdgeCache)
  have hbit : ComputableInPolyTime
      (fun q : (List (List Bool × List Bool) × (ℕ × ℕ) × List Bool) × PlantedCertState =>
        q.1.2.2.getD q.2.1.1.length false) encIn encBool :=
    ComputableInPolyTime.bitsGetDWithInput (by fun_prop) (by fun_prop) false
  have hpath : ComputableInPolyTime
      (fun q : (List (List Bool × List Bool) × (ℕ × ℕ) × List Bool) × PlantedCertState =>
        q.2.1.1 ++ [q.1.2.2.getD q.2.1.1.length false]) encIn encBits :=
    ComputableInPolyTime.bitsAppend (by fun_prop)
      (ComputableInPolyTime.bitsCons hbit (.const []))
  have hchildPk : ComputableInPolyTime
      (fun r : ((List (List Bool × List Bool) × (ℕ × ℕ) × List Bool) × PlantedCertState) ×
          (ℕ × NodeSlotCache) => (r.1.1.1.getD r.2.1 ([], [])).1) encMid encBits :=
    (ComputableInPolyTime.listGetDWithInput (by fun_prop) (by fun_prop) ([], [])).fst'
  have hvisit := isOraclePPTOn_visitNodeM (enc := encIn)
    (cap := fun q => q.1.1.length)
    (path := fun q => q.2.1.1 ++ [q.1.2.2.getD q.2.1.1.length false])
    (visited := fun q => q.2.2.1) (by fun_prop) hpath (by fun_prop)
  have hsign := isOraclePPTOn_signEdgeM S (enc := encMid)
    (keys := fun r => r.1.1.1) (target := fun r => r.1.1.2.1.1)
    (sigCap := fun r => r.1.1.2.1.2) (path := fun r => r.1.2.1.1)
    (idx := fun r => r.1.2.1.2.1)
    (u := fun r => (r.1.1.2.2.getD r.1.2.1.1.length false).toNat)
    (msg := fun r => (r.1.1.1.getD r.2.1 ([], [])).1) (edges := fun r => r.1.2.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    ((by fun_prop : ComputableInPolyTime Bool.toNat encBool encUnary).comp
      (hbit.comp (ComputableInPolyTime.fst encIn _)))
    hchildPk (by fun_prop)
  have hpost : ComputableInPolyTime
      (fun s : (((List (List Bool × List Bool) × (ℕ × ℕ) × List Bool) × PlantedCertState) ×
          (ℕ × NodeSlotCache)) × (List Bool × EdgeSigCache) =>
        ((s.1.1.2.1.1 ++ [s.1.1.1.2.2.getD s.1.1.2.1.1.length false], s.1.2.1,
          s.1.1.2.1.2.2 ++ [((s.1.1.1.1.getD s.1.2.1 ([], [])).1, s.2.1)]),
          (s.1.2.2, s.2.2))) encEnd encPlantedCert :=
    ((hpath.comp (by fun_prop)).prod
      ((by fun_prop : ComputableInPolyTime _ encEnd encUnary).prod
        (ComputableInPolyTime.listAppend' (by fun_prop)
          (ComputableInPolyTime.cons'
            ((hchildPk.comp (ComputableInPolyTime.fst encMid _)).prod (by fun_prop))
            (.const []))))).prod (by fun_prop)
  exact hvisit.bind_with (hsign.bind_with hpost.isOraclePPTOn)

private def plantedLoopInv (Mv Me : ℕ) (a : CertLoopIn) (i : ℕ)
    (state : PlantedCertState) : Prop :=
  let ((keys, _, _), (visited₀, edges₀)) := a
  let ((node, idx, certs), (visited, edges)) := state
  node.length = i ∧ idx ≤ Mv ∧ certs.length = i ∧
  (∀ c ∈ certs, c.1.length ≤ (encKeys keys).length ∧ c.2.length ≤ Me) ∧
  (∀ e ∈ visited, e.2 ≤ Mv) ∧ (∀ e ∈ edges, e.2.length ≤ Me) ∧
  (encNodeCache visited).length ≤
    (encNodeCache visited₀).length + i * (4 * (i + 1) + 2 * Mv + 3) ∧
  (encEdgeCache edges).length ≤
    (encEdgeCache edges₀).length + i * (8 * i + 2 * Me + 11)

private theorem plantedLoopInv_step (S : IndexedSignatureScheme) {Mv Me : ℕ} (a : CertLoopIn)
    (hMv : a.keys.length ≤ Mv) (hMe : a.sigCap ≤ Me) (i : ℕ) (state : PlantedCertState)
    (hinv : plantedLoopInv Mv Me a i state) (next : PlantedCertState)
    (hnext : next ∈ OracleComp.support
      (certifyStepPlanted S a.keys a.target a.sigCap a.leaf state)) :
    plantedLoopInv Mv Me a (i + 1) next := by
  rcases a with ⟨⟨keys, ⟨target, sigCap⟩, ⟨n, leaf⟩⟩, ⟨visited₀, edges₀⟩⟩
  rcases state with ⟨⟨node, idx, certs⟩, ⟨visited, edges⟩⟩
  obtain ⟨hnode, hidx, hcertsLen, hcerts, hvis, hedg, hvisLen, hedgLen⟩ := hinv
  supp_cases hnext [certifyStepPlanted, OracleComp.support] with
    ⟨⟨childIdx, visited'⟩, hvisStep, ⟨σ, edges'⟩, hedgStep, rfl⟩
  have hvBound := ProbOracleComp.memoize_call_size_le encBits encUnary
    (fun _ => pure (min visited.length keys.length))
    (node ++ [leaf.getD node.length false]) visited Mv
    (fun e he => by simpa only [encUnary_apply, List.length_replicate] using hvis e he)
    (fun val hval => by
      rw [OracleComp.eq_of_mem_supportWith_pure hval]
      simpa only [encUnary_apply, List.length_replicate] using (Nat.min_le_right _ _).trans hMv)
    hvisStep
  have heBound := ProbOracleComp.memoize_call_size_le (encPair encBits encUnary) encBits
    (fun _ => signEdgeRaw S keys target sigCap idx
      (leaf.getD node.length false).toNat (keys.getD childIdx ([], [])).1)
    (node, (leaf.getD node.length false).toNat) edges Me
    (fun e he => by simpa only [encBits_apply] using hedg e he)
    (fun val hval => by
      simpa only [encBits_apply] using
        (length_le_of_mem_support_signEdgeRaw S keys target sigCap idx _ _ hval).trans hMe)
    hedgStep
  simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate,
    List.length_append, List.length_singleton, hnode] at hvBound heBound
  have hu : (leaf.getD i false).toNat ≤ 1 := Bool.toNat_le _
  refine ⟨by simp [hnode], hvBound.1, by simp [hcertsLen], ?_, hvBound.2.1, heBound.2.1, ?_, ?_⟩
  · rintro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hcerts c hc
    · rw [List.mem_singleton.mp hc]
      exact ⟨length_fst_getD_keys_le keys childIdx, heBound.1⟩
  · dsimp only [encNodeCache] at hvisLen ⊢
    exact hvBound.2.2.trans (by
      have := Nat.mul_le_mul_left i
        (show 4 * (i + 1) + 2 * Mv + 3 ≤ 4 * (i + 1 + 1) + 2 * Mv + 3 by omega)
      have : (i + 1) * (4 * (i + 1 + 1) + 2 * Mv + 3) =
          i * (4 * (i + 1 + 1) + 2 * Mv + 3) + (4 * (i + 1 + 1) + 2 * Mv + 3) := Nat.succ_mul _ _
      omega)
  · dsimp only [encEdgeCache] at hedgLen ⊢
    exact heBound.2.2.trans (by
      have := Nat.mul_le_mul_left i
        (show 8 * i + 2 * Me + 11 ≤ 8 * (i + 1) + 2 * Me + 11 by omega)
      have : (i + 1) * (8 * (i + 1) + 2 * Me + 11) =
          i * (8 * (i + 1) + 2 * Me + 11) + (8 * (i + 1) + 2 * Me + 11) := Nat.succ_mul _ _
      omega)

private theorem certifyPlanted_support_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {Mv Me : ℕ} (a : CertLoopIn)
    (hMv : a.keys.length ≤ Mv) (hMe : a.sigCap ≤ Me)
    (hv₀ : ∀ e ∈ a.visited, e.2 ≤ Mv) (he₀ : ∀ e ∈ a.edges, e.2.length ≤ Me) :
    ∀ state ∈ OracleComp.support
      (certifyPlanted S depth a.keys a.target a.sigCap a.parameter a.leaf a.2),
      plantedLoopInv Mv Me a (depth a.parameter - 1) state := by
  suffices ∀ k, ∀ state ∈ OracleComp.support
      (OracleComp.iterate k (certifyStepPlanted S a.keys a.target a.sigCap a.leaf)
        (([], 0, []), a.2)),
      plantedLoopInv Mv Me a k state from this _
  intro k
  induction k with
  | zero =>
    intro state hstate
    rw [OracleComp.eq_of_mem_supportWith_pure hstate]
    exact ⟨rfl, Nat.zero_le _, rfl, by simp, hv₀, he₀, by simp, by simp⟩
  | succ k ih =>
    intro state hstate
    rw [OracleComp.iterate_succ] at hstate
    obtain ⟨prev, hprev, hstep⟩ := OracleComp.mem_supportWith_bind_iff.mp hstate
    exact plantedLoopInv_step S a hMv hMe k prev (ih prev hprev) state hstep

private theorem plantedLoopInv_enc_bounds {Mv Me d i : ℕ} {a : CertLoopIn}
    {state : PlantedCertState} (hi : i ≤ d)
    (hinv : plantedLoopInv Mv Me a i state) :
    (encKeys state.1.2.2).length ≤ d * (2 * (2 * (encKeys a.keys).length + 1 + Me) + 1) ∧
    (encNodeCache state.2.1).length ≤
      (encNodeCache a.visited).length + d * (4 * (d + 1) + 2 * Mv + 3) ∧
    (encEdgeCache state.2.2).length ≤
      (encEdgeCache a.edges).length + d * (8 * d + 2 * Me + 11) := by
  rcases a with ⟨⟨keys, _, _⟩, _⟩
  obtain ⟨-, -, hcertsLen, hcerts, -, -, hvisLen, hedgLen⟩ := hinv
  have hcertsList : (encKeys state.1.2.2).length ≤
      state.1.2.2.length * (2 * (2 * (encKeys keys).length + 1 + Me) + 1) :=
    length_encList_le (encPair encBits encBits) _ fun c hc => by
      obtain ⟨h1, h2⟩ := hcerts c hc
      enc_len
  refine ⟨hcertsList.trans (by rw [hcertsLen]; gcongr),
    hvisLen.trans (by gcongr), hedgLen.trans (by gcongr)⟩

private theorem isOraclePPTOn_certifyPlanted (S : IndexedSignatureScheme) {depth : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary) :
    IsOraclePPTOn
      (encPair (encPair encKeys (encPair (encPair encUnary encUnary) (encPair encUnary encBits)))
        (encPair encNodeCache encEdgeCache))
      encPlantedCert
      (fun a : CertLoopIn =>
        certifyPlanted S depth a.keys a.target a.sigCap a.parameter a.leaf a.2) := by
  let encLoopIn :=
    encPair (encPair encKeys (encPair (encPair encUnary encUnary) (encPair encUnary encBits)))
      (encPair encNodeCache encEdgeCache)
  obtain ⟨cd, dd, hdd⟩ := hdepth.polyBounded_length.exists_le
  simp only [encUnary_apply, List.length_replicate] at hdd
  have hleIn (a : CertLoopIn) :
      a.keys.length ≤ (encLoopIn a).length ∧ (encKeys a.keys).length ≤ (encLoopIn a).length ∧
      a.sigCap ≤ (encLoopIn a).length ∧ a.parameter ≤ (encLoopIn a).length ∧
      (encNodeCache a.visited).length ≤ (encLoopIn a).length ∧
      (encEdgeCache a.edges).length ≤ (encLoopIn a).length := by
    rcases a with ⟨⟨keys, _, ⟨n, leaf⟩⟩, ⟨visited, edges⟩⟩
    have hk := length_le_length_encList (encPair encBits encBits) keys
    enc_len [CertLoopIn.keys, CertLoopIn.sigCap, CertLoopIn.parameter, CertLoopIn.visited,
      CertLoopIn.edges, encLoopIn, encKeys]
  let bound (L : ℕ) : ℕ :=
    let d := cd * (L + 1) ^ dd
    let certB := d * (2 * (3 * L + 1) + 1)
    2 * (2 * d + 1 + (2 * L + 1 + certB)) + 1 +
      (2 * (L + d * (4 * (d + 1) + 2 * L + 3)) + 1 + (L + d * (8 * d + 2 * L + 11)))
  refine (IsOraclePPTOn.iterateWith_spec (input := encLoopIn) (stateEncoding := encPlantedCert)
    (count := fun a : CertLoopIn => depth a.parameter - 1)
    (initial := fun a => ((([], 0, []), a.2) : PlantedCertState))
    (step := fun (a : CertLoopIn) state =>
      certifyStepPlanted S a.keys a.target a.sigCap a.leaf state)
    (by fun_prop) (by fun_prop)
    ((isOraclePPTOn_certifyStepPlanted S).preprocess
      (prepare := fun pair : CertLoopIn × PlantedCertState =>
        ((pair.1.keys, (pair.1.target, pair.1.sigCap), pair.1.leaf), pair.2))
      (by fun_prop))
    (fun a i state => plantedLoopInv (encLoopIn a).length (encLoopIn a).length a i state)
    (fun a => ⟨rfl, Nat.zero_le _, rfl, by simp,
      fun e he => by
        have h := ((length_le_encPair_right encBits encUnary e).trans
          (length_le_encList_of_mem (encPair encBits encUnary) he)).trans (hleIn a).2.2.2.2.1
        simpa only [encUnary_apply, List.length_replicate] using h,
      fun e he => by
        have h := ((length_le_encPair_right (encPair encBits encUnary) encBits e).trans
          (length_le_encList_of_mem (encPair (encPair encBits encUnary) encBits) he)).trans
          (hleIn a).2.2.2.2.2
        simpa only [encBits_apply] using h,
      by simp, by simp⟩)
    (fun a i state _ hinv next hnext =>
      plantedLoopInv_step S a (hleIn a).1 (hleIn a).2.2.1 i state hinv next hnext)
    (size := fun a => bound (encLoopIn a).length)
    (PolyBounded.of_polynomiallyBounded _ <| by
      have hd : PolynomiallyBounded (fun L => cd * (L + 1) ^ dd) := by
        exact .mul (.const cd) (.pow (.add .id (.const 1)) dd)
      have hc : PolynomiallyBounded (fun L =>
          cd * (L + 1) ^ dd * (2 * (3 * L + 1) + 1)) :=
        hd.mul (.add (.mul (.const 2) (.add (.mul (.const 3) .id) (.const 1))) (.const 1))
      have hv : PolynomiallyBounded (fun L =>
          L + cd * (L + 1) ^ dd * (4 * (cd * (L + 1) ^ dd + 1) + 2 * L + 3)) :=
        .add .id (hd.mul (.add (.add (.mul (.const 4) (.add hd (.const 1))) (.mul (.const 2) .id))
          (.const 3)))
      have he : PolynomiallyBounded (fun L =>
          L + cd * (L + 1) ^ dd * (8 * (cd * (L + 1) ^ dd) + 2 * L + 11)) :=
        .add .id (hd.mul (.add (.add (.mul (.const 8) hd) (.mul (.const 2) .id)) (.const 11)))
      exact .add (.add (.mul (.const 2) (.add (.add (.mul (.const 2) hd) (.const 1))
        (.add (.add (.mul (.const 2) .id) (.const 1)) hc))) (.const 1))
        (.add (.add (.mul (.const 2) hv) (.const 1)) he))
    (fun (a : CertLoopIn) i ⟨⟨node, idx, certs⟩, ⟨visited, edges⟩⟩ hi hinv => by
      obtain ⟨-, hKE, -, hpar, hVE, hEE⟩ := hleIn a
      have hd : depth a.parameter ≤ cd * ((encLoopIn a).length + 1) ^ dd :=
        (hdd a.parameter).trans (by gcongr)
      obtain ⟨hcB, hvB, heB⟩ := plantedLoopInv_enc_bounds (hi.trans (Nat.sub_le _ _)) hinv
      have hnode : node.length ≤ cd * ((encLoopIn a).length + 1) ^ dd :=
        hinv.1 ▸ (hi.trans (Nat.sub_le _ _)).trans hd
      have hidx : idx ≤ (encLoopIn a).length := hinv.2.1
      have hcB' : (encKeys certs).length ≤
          (cd * ((encLoopIn a).length + 1) ^ dd) * (2 * (3 * (encLoopIn a).length + 1) + 1) :=
        hcB.trans (Nat.mul_le_mul hd (by omega))
      have hvB' : (encNodeCache visited).length ≤ (encLoopIn a).length +
          cd * ((encLoopIn a).length + 1) ^ dd *
            (4 * (cd * ((encLoopIn a).length + 1) ^ dd + 1) + 2 * (encLoopIn a).length + 3) :=
        hvB.trans (by gcongr)
      have heB' : (encEdgeCache edges).length ≤ (encLoopIn a).length +
          cd * ((encLoopIn a).length + 1) ^ dd *
            (8 * (cd * ((encLoopIn a).length + 1) ^ dd) + 2 * (encLoopIn a).length + 11) :=
        heB.trans (by gcongr)
      dsimp only [bound]
      enc_len)).1

/-- Caller tuple for `plantedTreeHandler`: `(((n, vk), target), keys)`. -/
private abbrev ForgerCaller := ((ℕ × List Bool) × ℕ) × List (List Bool × List Bool)

private theorem isOraclePPTOn_plantedTreeHandler (S : IndexedSignatureScheme)
    {depth sigCap : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hsigCap : ComputableInPolyTime sigCap encUnary encUnary) :
    let encCaller := encPair (encPair (encPair encUnary encBits) encUnary) encKeys
    IsOraclePPTOn
      (encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) encPlantedState))
      (encPair encBits encPlantedState)
      (fun pair : ForgerCaller × ((Unit × List Bool) × PlantedState) =>
        plantedTreeHandler S depth pair.1.2 pair.1.1.2 (sigCap pair.1.1.1.1) pair.1.1.1.1
          pair.2.1 pair.2.2) := by
  intro encCaller
  have _ := isOraclePPTOn_certifyPlanted S hdepth
  let encH := encPair encCaller (encPair (encPair (encFinEnum Unit) encBits) encPlantedState)
  let encHL := encPair encH encBits
  let encHLC := encPair encHL encPlantedCert
  have hcert : IsOraclePPTOn encHL encPlantedCert
      (fun q : (ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool =>
        certifyPlanted S depth q.1.1.2 q.1.1.1.2 (sigCap q.1.1.1.1.1) q.1.1.1.1.1 q.2
          (q.1.2.2.1.1, q.1.2.2.1.2)) :=
    (isOraclePPTOn_certifyPlanted S hdepth).preprocess (input := encHL)
      (prepare := fun q : (ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool =>
        (((q.1.1.2, (q.1.1.1.2, sigCap q.1.1.1.1.1), (q.1.1.1.1.1, q.2)),
          (q.1.2.2.1.1, q.1.2.2.1.2)) : CertLoopIn))
      (by fun_prop)
  have hsignLast := isOraclePPTOn_signEdgeM S (enc := encHLC)
    (keys := fun r => r.1.1.1.2) (target := fun r => r.1.1.1.1.2)
    (sigCap := fun r => sigCap r.1.1.1.1.1.1) (path := fun r => r.2.1.1)
    (idx := fun r => r.2.1.2.1) (u := fun r => (r.1.2.getLastD false).toNat)
    (msg := fun r => r.1.1.2.1.2) (edges := fun r => r.2.2.2)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
    (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
  have hleaf : IsOraclePPTOn (Operation := Unit) encH encBits
      (fun p : ForgerCaller × ((Unit × List Bool) × PlantedState) =>
        ProbOracleComp.sample (BitString.sampleList (depth p.1.1.1.1))) :=
    ((by fun_prop : ComputableInPolyTime
      (fun p : ForgerCaller × ((Unit × List Bool) × PlantedState) => depth p.1.1.1.1)
      encH encUnary).sampleList).isOraclePPTOn
  have hpost : ComputableInPolyTime
      (fun s : (((ForgerCaller × ((Unit × List Bool) × PlantedState)) × List Bool) ×
          PlantedCertState) × (List Bool × EdgeSigCache) =>
        (encodeSignature s.1.1.2 s.1.2.1.2.2 s.2.1,
          ((s.1.2.2.1, s.2.2),
            (s.1.1.1.2.1.2 :: s.1.1.1.2.2.2.1, s.1.1.2 :: s.1.1.1.2.2.2.2.1, false))))
      (encPair encHLC (encPair encBits encEdgeCache)) (encPair encBits encPlantedState) := by
    fun_prop
  have hgood : IsOraclePPTOn encHL (encPair encBits encPlantedState)
      (fun q => certifyPlanted S depth q.1.1.2 q.1.1.1.2 (sigCap q.1.1.1.1.1) q.1.1.1.1.1 q.2
          (q.1.2.2.1.1, q.1.2.2.1.2) >>= fun c =>
        signEdgeM S q.1.1.2 q.1.1.1.2 (sigCap q.1.1.1.1.1) c.1.1 c.1.2.1
          (q.2.getLastD false).toNat q.1.2.1.2 c.2.2 >>= fun e =>
          pure (encodeSignature q.2 c.1.2.2 e.1,
            ((c.2.1, e.2), (q.1.2.1.2 :: q.1.2.2.2.1, q.2 :: q.1.2.2.2.2.1, false)))) :=
    hcert.bind_with
      (hsignLast.bind_with hpost.isOraclePPTOn)
  unfold plantedTreeHandler
  exact IsOraclePPTOn.ite (by fun_prop)
    (IsOraclePPTOn.cond (by fun_prop)
      (ComputableInPolyTime.isOraclePPTOn (by fun_prop))
      (hleaf.bind_with (IsOraclePPTOn.cond (by fun_prop)
        (ComputableInPolyTime.isOraclePPTOn (by fun_prop)) hgood)))
    (ComputableInPolyTime.isOraclePPTOn (by fun_prop))

private def plantedResourceAllowance (depth sigCap : ℕ → ℕ) (c : ForgerCaller)
    (w : List Bool) : ℕ :=
  let n := c.1.1.1
  let d := depth n
  let sc := sigCap n
  let kLen := c.2.length
  let kEncLen := (encKeys c.2).length
  let replyB := 2 * d + 1 + (2 * (d * (2 * (2 * kEncLen + 1 + sc) + 1)) + 1 + sc)
  let vGrow := d * (4 * (d + 1) + 2 * kLen + 3)
  let eGrow := (d + 1) * (8 * d + 2 * sc + 11)
  let qGrow := 2 * w.length + 2
  let slGrow := 2 * d + 2
  replyB + 4 * vGrow + 2 * eGrow + 2 * qGrow + 2 * slGrow

private theorem plantedState_length_eq (state : PlantedState) :
    (encPlantedState state).length =
      4 * (encNodeCache state.1.1).length +
      2 * (encEdgeCache state.1.2).length +
      2 * (encList encBits state.2.1).length +
      2 * (encList encBits state.2.2.1).length + 6 := by
  rcases state with ⟨⟨v, e⟩, ⟨q, sl, b⟩⟩
  enc_len [List.length_singleton]

private theorem plantedTreeHandler_preserve (S : IndexedSignatureScheme) (depth sigCap : ℕ → ℕ)
    (c : ForgerCaller) (request : Unit × List Bool) (state : PlantedState)
    (hinv : (∀ e ∈ state.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ state.1.2, e.2.length ≤ sigCap c.1.1.1))
    (result : List Bool × PlantedState)
    (hresult : result ∈ OracleComp.support
      (plantedTreeHandler S depth c.2 c.1.2 (sigCap c.1.1.1) c.1.1.1 request state)) :
    ((∀ e ∈ result.2.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ result.2.1.2, e.2.length ≤ sigCap c.1.1.1)) ∧
    result.1.length ≤ plantedResourceAllowance depth sigCap c request.2 ∧
    (encPlantedState result.2).length ≤
      (encPlantedState state).length + plantedResourceAllowance depth sigCap c request.2 := by
  rcases state with ⟨⟨visited, edges⟩, ⟨queried, seenLeaves, bad⟩⟩
  obtain ⟨hvis, hedg⟩ := hinv
  have hqCons : (encList encBits (request.2 :: queried)).length ≤
      (encList encBits queried).length + (2 * request.2.length + 2) := by
    simp only [encList_cons, List.length_append, length_frame, encBits_apply]; omega
  have hpure (b' : Bool) :
      ((∀ e ∈ visited, e.2 ≤ c.2.length) ∧ (∀ e ∈ edges, e.2.length ≤ sigCap c.1.1.1)) ∧
      ([] : List Bool).length ≤ plantedResourceAllowance depth sigCap c request.2 ∧
      (encPlantedState ((visited, edges), (request.2 :: queried, seenLeaves, b'))).length ≤
        (encPlantedState ((visited, edges), (queried, seenLeaves, bad))).length +
          plantedResourceAllowance depth sigCap c request.2 := by
    refine ⟨⟨hvis, hedg⟩, Nat.zero_le _, ?_⟩
    rw [plantedState_length_eq, plantedState_length_eq]
    dsimp only [plantedResourceAllowance]; omega
  unfold plantedTreeHandler at hresult
  dsimp only at hresult
  split_ifs at hresult with hmsg hbad
  · rw [OracleComp.eq_of_mem_supportWith_pure hresult]; exact hpure true
  · obtain ⟨leaf, hleaf, hrest⟩ := OracleComp.mem_supportWith_bind_iff.mp hresult
    have hleafLen := BitString.length_of_mem_support_uniformList <| by
      rwa [← BitString.eval_sampleList, ← ProbOracleComp.support_sample]
    split_ifs at hrest with hcoll
    · rw [OracleComp.eq_of_mem_supportWith_pure hrest]; exact hpure true
    · simp only [OracleComp.mem_supportWith_bind_iff] at hrest
      obtain ⟨⟨⟨node, idx, certs⟩, ⟨visited', edges'⟩⟩, hcert, ⟨σ, edges''⟩, hsig, hres⟩ := hrest
      rw [OracleComp.eq_of_mem_supportWith_pure hres]
      have hloop := certifyPlanted_support_inv S depth
        ((c.2, (c.1.2, sigCap c.1.1.1), (c.1.1.1, leaf)), (visited, edges))
        le_rfl le_rfl hvis hedg _ hcert
      obtain ⟨hcB, hvB, heB⟩ := plantedLoopInv_enc_bounds (Nat.sub_le (depth c.1.1.1) 1) hloop
      obtain ⟨hnode, -, -, -, hvis', hedg', -, -⟩ := hloop
      have heLast := ProbOracleComp.memoize_call_size_le (encPair encBits encUnary) encBits
        (fun _ => signEdgeRaw S c.2 c.1.2 (sigCap c.1.1.1) idx
          (leaf.getLastD false).toNat request.2)
        (node, (leaf.getLastD false).toNat) edges' (sigCap c.1.1.1)
        (fun e he => by simpa only [encBits_apply] using hedg' e he)
        (fun val hval => by
          simpa only [encBits_apply] using
            length_le_of_mem_support_signEdgeRaw S c.2 c.1.2 (sigCap c.1.1.1) idx _ _ hval)
        hsig
      simp only [length_encPair, encBits_apply, encUnary_apply, List.length_replicate, hnode]
        at heLast
      have hu : (leaf.getLastD false).toNat ≤ 1 := Bool.toNat_le _
      have hslCons : (encList encBits (leaf :: seenLeaves)).length ≤
          (encList encBits seenLeaves).length + (2 * depth c.1.1.1 + 2) := by
        simp only [encList_cons, List.length_append, length_frame, encBits_apply, hleafLen]; omega
      refine ⟨⟨hvis', heLast.2.1⟩, ?_, ?_⟩
      · have hσLen : σ.length ≤ sigCap c.1.1.1 := heLast.1
        dsimp only [plantedResourceAllowance, CertLoopIn.keys, CertLoopIn.sigCap, encKeys]
          at hcB ⊢
        simp only [encodeSignature, length_encPair, encBits_apply, hleafLen]
        omega
      · rw [plantedState_length_eq, plantedState_length_eq]
        dsimp only [plantedResourceAllowance, CertLoopIn.keys, CertLoopIn.sigCap,
          CertLoopIn.visited, CertLoopIn.edges, CertLoopIn.parameter, encNodeCache, encEdgeCache]
          at hvB heB hnode heLast ⊢
        have hsucc : (depth c.1.1.1 + 1) * (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) =
            depth c.1.1.1 * (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) +
              (8 * depth c.1.1.1 + 2 * sigCap c.1.1.1 + 11) := Nat.succ_mul _ _
        have hsub := Nat.sub_le (depth c.1.1.1) 1
        omega
  · rw [OracleComp.eq_of_mem_supportWith_pure hresult]; exact hpure bad

private theorem computableInPolyTime_extractForgery :
    ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × NodeSlotCache) × (List Bool × List Bool) =>
        extractForgery q.1.1.1 q.1.1.2 q.1.2 q.2.1 q.2.2)
      (encPair (encPair (encPair encUnary encUnary) encNodeCache) (encPair encBits encBits))
      (encPair encUnary (encPair encBits encBits)) := by
  let encIn := encPair (encPair (encPair encUnary encUnary) encNodeCache) (encPair encBits encBits)
  let encMid := encPair encIn (encPair (encPair encBits (encPair encKeys encBits)) encUnary)
  have hmid : ComputableInPolyTime
      (fun q : ((ℕ × ℕ) × NodeSlotCache) × (List Bool × List Bool) =>
        (q, signatureDecoder.decode q.2.2,
          ((q.1.2.filter fun e => e.2 == q.1.1.2).headD ([], 0)).1.length)) encIn encMid := by
    fun_prop
  let T := (((ℕ × ℕ) × NodeSlotCache) × (List Bool × List Bool)) ×
    (List Bool × List (List Bool × List Bool) × List Bool) × ℕ
  have hbit := (by fun_prop : ComputableInPolyTime Bool.toNat encBool encUnary).comp
    (ComputableInPolyTime.bitsGetDWithInput (encIn := encMid)
      (by fun_prop : ComputableInPolyTime (fun t : T => t.2.1.1) encMid encBits)
      (by fun_prop : ComputableInPolyTime (fun t : T => t.2.2) encMid encUnary) false)
  have hentry := ComputableInPolyTime.listGetDWithInput (encIn := encMid)
    (by fun_prop : ComputableInPolyTime (fun t : T => t.2.1.2.1) encMid encKeys)
    (by fun_prop : ComputableInPolyTime (fun t : T => t.2.2) encMid encUnary) ([], [])
  have hstep : ComputableInPolyTime
      (fun t : T =>
        if t.2.2 + 1 < t.1.1.1.1 then
          ((t.2.1.1.getD t.2.2 false).toNat, t.2.1.2.1.getD t.2.2 ([], []))
        else ((t.2.1.1.getD t.2.2 false).toNat, t.1.2.1, t.2.1.2.2))
      encMid (encPair encUnary (encPair encBits encBits)) :=
    ComputableInPolyTime.ite_decide (by fun_prop) (hbit.prod hentry) (hbit.prod (by fun_prop))
  exact (hstep.comp hmid).of_enc_eq fun q => by
    simp only [Function.comp_apply, extractForgery]

/-- The planted-node reduction `indexedForger` is uniformly strict oracle PPT whenever `depth`,
`slotBound`, and `sigCap` are polynomial-time in unary and `adversary` is strict oracle PPT. -/
theorem isOraclePPT_indexedForger (S : IndexedSignatureScheme) {depth slotBound sigCap : ℕ → ℕ}
    (hdepth : ComputableInPolyTime depth encUnary encUnary)
    (hslot : ComputableInPolyTime slotBound encUnary encUnary)
    (hsigCap : ComputableInPolyTime sigCap encUnary encUnary)
    {adversary : Forger} (hA : IsOraclePPT (encPair encBits encBits) adversary) :
    IsOraclePPT (encPair encUnary (encPair encBits encBits))
      (indexedForger S depth slotBound sigCap adversary) := by
  let encStage := encPair (encPair encUnary encBits) encUnary
  let encCaller := encPair encStage encKeys
  have hres : ComputableInPolyTime
      (fun pair : ForgerCaller × List Bool =>
        plantedResourceAllowance depth sigCap pair.1 pair.2)
      (encPair encCaller encBits) encUnary := by
    have hformula : ComputableInPolyTime
        (fun q : (ℕ × ℕ) × (ℕ × ℕ × ℕ) =>
          2 * q.1.1 + 1 + (2 * (q.1.1 * (2 * (2 * q.2.2.1 + 1 + q.1.2) + 1)) + 1 + q.1.2) +
            4 * (q.1.1 * (4 * (q.1.1 + 1) + 2 * q.2.1 + 3)) +
            2 * ((q.1.1 + 1) * (8 * q.1.1 + 2 * q.1.2 + 11)) +
            2 * (2 * q.2.2.2 + 2) + 2 * (2 * q.1.1 + 2))
        (encPair (encPair encUnary encUnary)
          (encPair encUnary (encPair encUnary encUnary))) encUnary := by fun_prop
    have hargs : ComputableInPolyTime
        (fun p : ForgerCaller × List Bool =>
          ((depth p.1.1.1.1, sigCap p.1.1.1.1),
            (p.1.2.length, (encKeys p.1.2).length, p.2.length)))
        (encPair encCaller encBits)
        (encPair (encPair encUnary encUnary)
          (encPair encUnary (encPair encUnary encUnary))) := by fun_prop
    exact (hformula.comp hargs).of_enc_eq fun p => by
      simp only [Function.comp_apply, plantedResourceAllowance]
  have hrun := hA.run_interpret_preprocess_open (External := Unit)
    (handler := fun c : ForgerCaller =>
      plantedTreeHandler S depth c.2 c.1.2 (sigCap c.1.1.1) c.1.1.1)
    (prepare := fun c : ForgerCaller =>
      (c.1.1.1, encPair encUnary encBits (c.1.1.1, (c.2.getD 0 ([], [])).1)))
    (initial := fun _ => initPlantedState)
    (resources := plantedResourceAllowance depth sigCap)
    (by fun_prop) (isOraclePPTOn_plantedTreeHandler S hdepth hsigCap)
    (ComputableInPolyTime.const initPlantedState)
    (fun c state => (∀ e ∈ state.1.1, e.2 ≤ c.2.length) ∧
      (∀ e ∈ state.1.2, e.2.length ≤ sigCap c.1.1.1))
    (fun c => by
      simp only [initPlantedState, List.mem_singleton, List.not_mem_nil, IsEmpty.forall_iff,
        implies_true, and_true]
      rintro _ rfl; exact Nat.zero_le _)
    hres (plantedTreeHandler_preserve S depth sigCap)
  have hextract := computableInPolyTime_extractForgery.comp
    (by fun_prop : ComputableInPolyTime
      (fun pair : ForgerCaller × ((List Bool × List Bool) × PlantedState) =>
        (((depth pair.1.1.1.1, pair.1.1.2), pair.2.2.1.1), (pair.2.1.1, pair.2.1.2)))
      (encPair encCaller (encPair (encPair encBits encBits) encPlantedState))
      (encPair (encPair (encPair encUnary encUnary) encNodeCache) (encPair encBits encBits)))
  refine IsOraclePPTOn.isOraclePPT ?_
  unfold indexedForger indexedForgerAt
  exact ((isPPTOn_sampleDyadicIndex (by fun_prop)).isOraclePPTOn).bind_with
    ((isPPTOn_plantNodeKeys S hslot).isOraclePPTOn.bind_with
      (hrun.bind_with hextract.isOraclePPTOn))

end ForgerEfficiency

/-! ### Shared leaf-guarded signing handler combinators -/

section TreeHandlers

private abbrev TreeLog := List (List Bool) × List (List Bool) × Bool

private abbrev TreeState (σ : Type) := σ × TreeLog

private abbrev TreeBody (σ : Type) := List Bool → List Bool → σ → PMF (List Bool × σ)

private abbrev TreeMsg (S : IndexedSignatureScheme) (n : ℕ) (msg : List Bool) : Prop :=
  msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1

private def treeBad {σ : Type} (s : TreeState σ) : Prop := s.2.2.2 = true

private theorem bool_eq_of_toNat_eq {a b : Bool} (h : a.toNat = b.toNat) : a = b := by
  cases a <;> cases b <;> first | rfl | simp at h

private theorem lookup_mem {K V : Type} [BEq K] [LawfulBEq K] {l : List (K × V)} {k : K} {v : V}
    (h : l.lookup k = some v) : (k, v) ∈ l := by
  obtain ⟨_, _, rfl, -⟩ := List.lookup_eq_some_iff.mp h
  exact List.mem_append_right _ List.mem_cons_self

private theorem lookup_cons_ne {K V : Type} [BEq K] [LawfulBEq K]
    {k₁ k₂ : K} {v : V} {l : List (K × V)} (hne : k₂ ≠ k₁) :
    ((k₁, v) :: l).lookup k₂ = l.lookup k₂ := by
  rw [List.lookup_cons, beq_false_of_ne hne]

private noncomputable def guardedTreeHandler {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) (req : Unit × List Bool) : StateT (TreeState σ) PMF (List Bool) :=
  fun (inner, queried, seenLeaves, bad) =>
    if req.2.length = n then
      if bad then PMF.pure ([], (inner, req.2 :: queried, seenLeaves, true))
      else (BitString.uniformList (depth n)).bind fun leaf =>
        if seenLeaves.contains leaf then
          PMF.pure ([], (inner, req.2 :: queried, seenLeaves, true))
        else (body leaf req.2 inner).map fun (sig, inner') =>
          (sig, (inner', req.2 :: queried, leaf :: seenLeaves, false))
    else PMF.pure ([], (inner, req.2 :: queried, seenLeaves, bad))

private noncomputable def unguardedTreeHandler {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) (req : Unit × List Bool) : StateT (TreeState σ) PMF (List Bool) :=
  fun (inner, queried, seenLeaves, bad) =>
    if req.2.length = n then
      (BitString.uniformList (depth n)).bind fun leaf =>
        let bad' := bad || seenLeaves.contains leaf
        let seen' := if bad' then seenLeaves else leaf :: seenLeaves
        (body leaf req.2 inner).map fun (sig, inner') =>
          (sig, (inner', req.2 :: queried, seen', bad'))
    else PMF.pure ([], (inner, req.2 :: queried, seenLeaves, bad))

private theorem guardedTreeHandler_bind_comm {σ₁ σ₂ γ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body₁ : TreeBody σ₁) (body₂ : γ → TreeBody σ₂)
    (exp : σ₁ → PMF γ) (rep : σ₁ → σ₂) (inv : TreeState σ₁ → Prop)
    (req : Unit × List Bool) (s : TreeState σ₁)
    (hinv_pure : ∀ b', inv (s.1, req.2 :: s.2.1, s.2.2.1, b'))
    (hgood : req.2.length = n → s.2.2.2 = false →
      ∀ leaf ∈ (BitString.uniformList (depth n)).support, s.2.2.1.contains leaf = false →
        ((body₁ leaf req.2 s.1).bind fun (sig, inner') =>
          (exp inner').map fun k => (k, sig, rep inner')) =
          ((exp s.1).bind fun k =>
            (body₂ k leaf req.2 (rep s.1)).map fun (sig, inner') => (k, sig, inner')) ∧
        ∀ sig inner', (sig, inner') ∈ (body₁ leaf req.2 s.1).support →
          inv (inner', req.2 :: s.2.1, leaf :: s.2.2.1, false)) :
    ((guardedTreeHandler depth n body₁ req s).bind fun (ans, s') =>
      (exp s'.1).map fun k => (k, ans, (rep s'.1, s'.2))) =
      ((exp s.1).bind fun k =>
        (guardedTreeHandler depth n (body₂ k) req (rep s.1, s.2)).map (k, ·)) ∧
    ∀ ans s', (ans, s') ∈ (guardedTreeHandler depth n body₁ req s).support → inv s' := by
  obtain ⟨inner, queried, seen, bad⟩ := s
  dsimp only [guardedTreeHandler]
  split_ifs with hmsg hbad
  · refine ⟨by simp only [PMF.pure_bind, PMF.map, Function.comp_def], fun ans s' hm => ?_⟩
    supp_cases hm; exact hinv_pure true
  · have hbf : bad = false := Bool.eq_false_iff.mpr hbad
    refine ⟨?_, fun ans s' hm => ?_⟩
    · rw [PMF.bind_bind]
      simp_rw [PMF.map_bind]
      rw [PMF.bind_comm (exp inner) (BitString.uniformList (depth n))]
      refine PMF.bind_congr_on_support _ _ _ fun leaf hl => ?_
      cases hs : seen.contains leaf
      · simp only [Bool.false_eq_true, ↓reduceIte, PMF.bind_map, Function.comp_def]
        have hg := congrArg (PMF.map fun (k, sig, inner') =>
          (k, sig, (inner', req.2 :: queried, leaf :: seen, false)))
          (hgood hmsg hbf leaf hl hs).1
        simpa only [pmf_norm] using hg
      · simp only [↓reduceIte, PMF.pure_bind, PMF.map, Function.comp_def]
    · obtain ⟨leaf, hl, hm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hm
      cases hs : seen.contains leaf
      · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm
        supp_cases hm with ⟨⟨sig, inner'⟩, hmem, rfl, rfl⟩
        exact (hgood hmsg hbf leaf hl hs).2 sig inner' hmem
      · simp only [hs, ↓reduceIte] at hm
        supp_cases hm; exact hinv_pure true
  · refine ⟨by simp only [PMF.pure_bind, PMF.map, Function.comp_def], fun ans s' hm => ?_⟩
    supp_cases hm; exact hinv_pure bad

private theorem guardedTreeHandler_map {σ₁ σ₂ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body₁ : TreeBody σ₁) (body₂ : TreeBody σ₂)
    (rep : σ₁ → σ₂) (inv : TreeState σ₁ → Prop)
    (req : Unit × List Bool) (s : TreeState σ₁)
    (hinv_pure : ∀ b', inv (s.1, req.2 :: s.2.1, s.2.2.1, b'))
    (hgood : req.2.length = n → s.2.2.2 = false →
      ∀ leaf ∈ (BitString.uniformList (depth n)).support, s.2.2.1.contains leaf = false →
        (body₁ leaf req.2 s.1).map (fun (sig, inner') => (sig, rep inner')) =
          body₂ leaf req.2 (rep s.1) ∧
        ∀ sig inner', (sig, inner') ∈ (body₁ leaf req.2 s.1).support →
          inv (inner', req.2 :: s.2.1, leaf :: s.2.2.1, false)) :
    (guardedTreeHandler depth n body₁ req s).map (fun (ans, s') => (ans, rep s'.1, s'.2)) =
      guardedTreeHandler depth n body₂ req (rep s.1, s.2) ∧
    ∀ ans s', (ans, s') ∈ (guardedTreeHandler depth n body₁ req s).support → inv s' := by
  have h := guardedTreeHandler_bind_comm depth n body₁ (fun _ : Unit => body₂)
    (fun _ => PMF.pure ()) rep inv req s hinv_pure fun hm hb leaf hl hs => by
      obtain ⟨heq, hi⟩ := hgood hm hb leaf hl hs
      refine ⟨?_, hi⟩
      rw [PMF.pure_bind, ← heq]
      simp only [PMF.map, pmf_norm]
  exact ⟨by simpa only [PMF.map, pmf_norm] using congrArg (PMF.map Prod.snd) h.1, h.2⟩

private theorem guardedTreeHandler_support_inv {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) (inv : TreeState σ → Prop)
    (req : Unit × List Bool) (s : TreeState σ)
    (hinv_pure : ∀ b', inv (s.1, req.2 :: s.2.1, s.2.2.1, b'))
    (hgood : req.2.length = n → s.2.2.2 = false →
      ∀ leaf ∈ (BitString.uniformList (depth n)).support, s.2.2.1.contains leaf = false →
        ∀ sig inner', (sig, inner') ∈ (body leaf req.2 s.1).support →
          inv (inner', req.2 :: s.2.1, leaf :: s.2.2.1, false)) :
    ∀ ans s', (ans, s') ∈ (guardedTreeHandler depth n body req s).support → inv s' := by
  obtain ⟨inner, queried, seen, bad⟩ := s
  intro ans s' hm
  dsimp only [guardedTreeHandler] at hm
  split_ifs at hm with hmsg hbad
  · supp_cases hm; exact hinv_pure true
  · have hbf : bad = false := Bool.eq_false_iff.mpr hbad
    obtain ⟨leaf, hl, hm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hm
    cases hs : seen.contains leaf
    · simp only [hs, Bool.false_eq_true, ↓reduceIte] at hm
      supp_cases hm with ⟨⟨sig, inner'⟩, hmem, rfl, rfl⟩
      exact hgood hmsg hbf leaf hl hs sig inner' hmem
    · simp only [hs, ↓reduceIte] at hm
      supp_cases hm; exact hinv_pure true
  · supp_cases hm; exact hinv_pure bad

private theorem identicalUntilBad_treeHandler {σ : Type} (depth : ℕ → ℕ) (n : ℕ)
    (body : TreeBody σ) :
    ProbOracleComp.IdenticalUntilBad
      (unguardedTreeHandler depth n body) (guardedTreeHandler depth n body) treeBad := by
  refine OracleComp.IdenticalUntilBad.probOracleComp ⟨?_, ?_, ?_⟩
  · rintro req ⟨inner, queried, seen, bad⟩ hs a ⟨inner', queried', seen', bad'⟩ hs'
    obtain rfl : bad = false := Bool.eq_false_iff.mpr hs
    obtain rfl : bad' = false := Bool.eq_false_iff.mpr hs'
    simp only [unguardedTreeHandler, guardedTreeHandler, Bool.false_or, Bool.false_eq_true,
      ↓reduceIte]
    split_ifs with hmsg
    · simp only [PMF.bind_apply]
      refine tsum_congr fun leaf => ?_
      cases hcl : seen.contains leaf
      · simp only [Bool.false_eq_true, ↓reduceIte]
      · simp only [↓reduceIte]
        have h1 : ((body leaf req.2 inner).map fun (sig, inner'') =>
            (sig, inner'', req.2 :: queried, seen, true))
            (a, (inner', queried', seen', false)) = 0 :=
          (PMF.apply_eq_zero_iff _ _).mpr fun hm => by supp_cases hm
        have h2 : (PMF.pure ([], (inner, req.2 :: queried, seen, true)) :
            PMF (List Bool × TreeState σ)) (a, (inner', queried', seen', false)) = 0 :=
          (PMF.apply_eq_zero_iff _ _).mpr fun hm => by supp_cases hm
        rw [h1, h2]
    · rfl
  · rintro req ⟨inner, queried, seen, bad⟩ hbad x hx
    obtain rfl : bad = true := hbad
    simp only [unguardedTreeHandler, Bool.true_or, ↓reduceIte] at hx
    split_ifs at hx <;> (supp_cases hx; rfl)
  · rintro req ⟨inner, queried, seen, bad⟩ hbad x hx
    obtain rfl : bad = true := hbad
    simp only [guardedTreeHandler, ↓reduceIte] at hx
    split_ifs at hx <;> (supp_cases hx; rfl)

private theorem toOuterMeasure_bad_guardedTreeHandler_le {α σ : Type} (depth : ℕ → ℕ) (n Q : ℕ)
    (body : TreeBody σ) {prog : WordOracleComp Unit α} (hq : prog.IsQueryBounded Q) (inner : σ)
    (queried : List (List Bool)) :
    ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (guardedTreeHandler depth n body)) prog).run (inner, queried, [], false)).toOuterMeasure
        {x | treeBad x.2} ≤
      (((Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) : ℝ≥0) : ℝ≥0∞) := by
  have hstep : ∀ req (s : TreeState σ), ¬treeBad s →
      (guardedTreeHandler depth n body req s).toOuterMeasure {x | treeBad x.2} ≤
        (s.2.2.1.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ depth n) := by
    rintro req ⟨inner₀, q₀, seen, bad⟩ hs
    obtain rfl : bad = false := Bool.eq_false_iff.mpr hs
    simp only [guardedTreeHandler, Bool.false_eq_true, ↓reduceIte]
    split_ifs with hmsg
    · classical
      refine (Probability.PMF.toOuterMeasure_bind_le_add (BitString.uniformList (depth n)) _
        (seen.toFinset : Set (List Bool)) {x : List Bool × TreeState σ | treeBad x.2} 0
        fun leaf _ hnot => ?_).trans ?_
      · have hmem : seen.contains leaf = false := Bool.eq_false_iff.mpr fun hc =>
          hnot (Finset.mem_coe.mpr (List.mem_toFinset.mpr (List.contains_iff_mem.mp hc)))
        simp only [hmem, Bool.false_eq_true, ↓reduceIte, le_zero_iff,
          PMF.toOuterMeasure_apply_eq_zero_iff]
        exact Set.disjoint_left.mpr fun x hx hbad => by supp_cases hx; cases hbad
      · rw [add_zero]
        exact (BitString.toOuterMeasure_uniformList_finset_le (depth n) seen.toFinset).trans
          (by gcongr; exact_mod_cast List.toFinset_card_le seen)
    · simp [PMF.toOuterMeasure_pure_apply, treeBad]
  have hgrow : ∀ req (s : TreeState σ), ¬treeBad s → ∀ x ∈
      (guardedTreeHandler depth n body req s).support, ¬treeBad x.2 →
      x.2.2.2.1.length ≤ s.2.2.1.length + 1 := by
    rintro req ⟨inner₀, q₀, seen, bad⟩ hs x hx hxbad
    obtain rfl : bad = false := Bool.eq_false_iff.mpr hs
    simp only [guardedTreeHandler, Bool.false_eq_true, ↓reduceIte] at hx
    split_ifs at hx
    · obtain ⟨leaf, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).mp hx
      split_ifs at hx <;> (supp_cases hx; first | exact absurd rfl hxbad | exact le_rfl)
    · supp_cases hx; exact Nat.le_succ _
  have hbad := ProbOracleComp.toOuterMeasure_bad_choose_two_le
    (handler := guardedTreeHandler depth n body) (bad := treeBad)
    (fun s => s.2.2.1.length) ((1 : ℝ≥0∞) / 2 ^ depth n) hstep hgrow hq
    (s := (inner, queried, [], false)) Bool.false_ne_true
  rw [ProbOracleComp.runWith_eq_run_interpret] at hbad
  have htwo : (1 : ℝ≥0∞) / 2 ^ depth n = 2 * ((1 : ℝ≥0∞) / 2 ^ (depth n + 1)) := by
    simp only [one_div, pow_succ']
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have hchoose : 2 * Q.choose 2 ≤ Q ^ 2 := by
    rw [Nat.choose_two_right, pow_two]
    exact (Nat.mul_div_le _ 2).trans (Nat.mul_le_mul_left Q (Nat.sub_le Q 1))
  refine hbad.trans ?_
  have herr : ((((Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) : ℝ≥0)) : ℝ≥0∞) =
      ((Q ^ 2 : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ (depth n + 1)) := by
    rw [ENNReal.coe_div (pow_ne_zero _ two_ne_zero), div_eq_mul_inv, one_div]; push_cast; ring
  simp only [List.length_nil, mul_zero, zero_add, htwo, ← mul_assoc]
  rw [herr, mul_comm (Q.choose 2 : ℝ≥0∞) 2, ← Nat.cast_ofNat, ← Nat.cast_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hchoose) zero_le

private noncomputable def lazySignBody (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) : TreeBody (NodeKeyCache × EdgeSigCache) :=
  fun leaf msg caches =>
    (ProbComp.eval (certifyLazy S depth n root leaf caches)).bind fun
      ((node, (_, sk), certs), (nodes', edges')) =>
        (ProbComp.eval (memoize (fun _ => S.sign sk (leaf.getLastD false).toNat msg)
          (node, (leaf.getLastD false).toNat) edges')).map fun (σ, edges'') =>
            (encodeSignature leaf certs σ, (nodes', edges''))

private theorem eval_lazySignHandler_eq (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (root : List Bool × List Bool) (req : Unit × List Bool) (s : LazyTreeState) :
    ProbComp.eval (lazySignHandler S depth n root req s) =
      guardedTreeHandler depth n (lazySignBody S depth n root) req s := by
  obtain ⟨⟨nodes, edges⟩, queried, seen, bad⟩ := s
  simp only [lazySignHandler, guardedTreeHandler, lazySignBody, apply_ite ProbComp.eval,
    BitString.eval_sampleList, pmf_norm]
  split_ifs with hmsg hbad <;> rfl

end TreeHandlers

/-! ### From ideal coins to the lazy tree game -/

section IdealToLazy

private abbrev CoinCache := List (List Bool × List Bool)

private noncomputable def lazyCoinRequest (M : ℕ) (x : List Bool) (L : ℕ) :
    StateT CoinCache PMF (List Bool) := fun cc =>
  (memoize (fun _ => BitString.uniformList M) (padRequest M x) cc).map
    fun out => (out.1.take L, out.2)

private noncomputable def lazyCoinHandler (M : ℕ) (r : Unit × List Bool) :
    StateT CoinCache PMF (List Bool) :=
  let req := coinRequestDecoder.decode r.2
  lazyCoinRequest M req.1 req.2

private theorem run_interpret_coinRequest (M : ℕ) (x : List Bool) (L : ℕ) (cc : CoinCache) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
      (coinRequest x L)).run cc = lazyCoinRequest M x L cc := by
  simp only [coinRequest, OracleComp.interpret_map, ProbOracleComp.interpret_query,
    StateT.run_map, PMF.monad_map_eq_map]
  change (lazyCoinHandler M ((), encPair encBits encUnary (x, L)) cc).map
    (fun (v, s) => (v.take L, s)) = _
  simp only [lazyCoinHandler, coinRequestDecoder.decode_enc, lazyCoinRequest, PMF.map_comp,
    Function.comp_def, List.take_take, Nat.min_self]

private theorem eval_treeIdealGame_eq_lazyCoin (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (treeIdealGame S T depth N adversary n) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler (N n)))
        (simulateTreeGame S T depth adversary n)).run []).map Prod.fst := by
  set M := N n
  set prog := simulateTreeGame S T depth adversary n
  have hideal : ProbComp.eval (treeIdealGame S T depth N adversary n) =
      (PMF.uniformOfFintype (BitString M → BitString M)).bind fun table =>
        OracleComp.interpret
          (OracleComp.sumHandler ProbComp.unifOracle
            (fun r : Unit × List Bool => PMF.pure (randomCoinOracle M table r.2)))
          prog := by
    simp only [treeIdealGame, ProbComp.eval_bind, ProbComp.eval_uniform]
    refine PMF.bind_congr_on_support _ _ _ fun table _ => ?_
    have hc : ∀ x L, (randomCoinOracle M table (encPair encBits encUnary (x, L))).length ≤ L := by
      intro x L; simp only [randomCoinOracle, coinRequestDecoder.decode_enc]
      exact List.length_take_le _ _
    have hcoins : coinsOf (randomCoinOracle M table) = tableCoins M table := by
      funext _ x L; simp only [coinsOf, randomCoinOracle, coinRequestDecoder.decode_enc, tableCoins]
    rw [← hcoins, ← evalDet_simulateTreeGame hc adversary n [], ← eval_interpret_eq_evalDet,
      ProbOracleComp.eval_interpret]
    simp only [ProbComp.eval_pure]; rfl
  let adapt (r : Unit × List Bool) :
      ProbOracleComp (fun _ : BitString M => List Bool) (List Bool) :=
    let req := coinRequestDecoder.decode r.2
    List.take req.2 <$> ProbOracleComp.query (BitString.ofList M (padRequest M req.1))
  let adapted := OracleComp.interpret
    (OracleComp.sumHandler (fun k => ProbOracleComp.sample (ProbComp.unifFin k)) adapt) prog
  have hmem := RandomOracle.interpret_prob_eq_memoize_map (encBitString M) List.ofFn
    (fun _ => PMF.uniformOfFintype (BitString M)) (fun _ => BitString.uniformList M)
    (fun _ => rfl) adapted
  rw [PMF.pi_uniformOfFintype, Probability.PMF.monad_bind_eq_bind] at hmem
  simp only [encBitString_apply] at hmem
  have hlhs : ∀ table : BitString M → BitString M,
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle (fun key => PMF.pure (List.ofFn (table key))))
        adapted =
      OracleComp.interpret
        (OracleComp.sumHandler ProbComp.unifOracle
          (fun r : Unit × List Bool => PMF.pure (randomCoinOracle M table r.2))) prog := by
    intro table
    simp only [adapted, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
      ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
    congr 1; funext q; cases q with
    | inl _ => rfl
    | inr r =>
      simp only [adapt, OracleComp.interpret_map, ProbOracleComp.interpret_query,
        pmf_norm, randomCoinOracle, randomFunctionOracle, length_padRequest, ↓reduceIte]
  have hrhs : (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (fun key => memoize (fun _ => BitString.uniformList M) (List.ofFn key)))
        adapted).run [] =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M)) prog).run [] := by
    simp only [adapted, OracleComp.interpret_interpret, OracleComp.interpret_sumHandler,
      ProbOracleComp.interpret_sample, ProbComp.unifFin, OracleComp.interpret_query]
    refine congrArg (fun h => (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h) prog).run [])
      (funext fun r => funext fun cc => ?_)
    simp only [adapt, interp_norm, pmf_norm,
      BitString.ofFn_ofList (length_padRequest M _), lazyCoinHandler, lazyCoinRequest]
    rfl
  rw [hideal, ← PMF.bind_congr_on_support _ _ _ (fun t _ => hlhs t), hmem, hrhs]

private noncomputable def coinSignBody (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) : TreeBody CoinCache :=
  fun leaf msg cc =>
    (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
      (do
        let (node, (_, sk), certs) ← certifyO S T depth n leaf
        let σ ← signAtO S T node sk (leaf.getLastD false).toNat msg
        return encodeSignature leaf certs σ)).run cc

private abbrev JointInner := CoinCache × (NodeKeyCache × EdgeSigCache)

private noncomputable def jointNodeKey (S : IndexedSignatureScheme) (T : S.Seeded) (M n : ℕ)
    (path : List Bool) (st : CoinCache × NodeKeyCache) :
    PMF ((List Bool × List Bool) × (CoinCache × NodeKeyCache)) :=
  (lazyCoinRequest M (keyInput path) (T.keyGenBudget n) st.1).map fun out =>
    let key := T.keyGenWith n out.1
    let nodes' := match st.2.lookup path with | some _ => st.2 | none => (path, key) :: st.2
    (key, (out.2, nodes'))

private noncomputable def jointSignAt (S : IndexedSignatureScheme) (T : S.Seeded) (M : ℕ)
    (path sk : List Bool) (u : ℕ) (msg : List Bool) (st : CoinCache × EdgeSigCache) :
    PMF (List Bool × (CoinCache × EdgeSigCache)) :=
  (lazyCoinRequest M (signInput path u) (T.signBudget sk u msg) st.1).map fun out =>
    let σ := T.signWith sk u msg out.1
    let edges' := match st.2.lookup (path, u) with
      | some _ => st.2 | none => ((path, u), σ) :: st.2
    (σ, (out.2, edges'))

private noncomputable def jointCertifyStep (S : IndexedSignatureScheme) (T : S.Seeded) (M n : ℕ)
    (leaf : List Bool) (st : CoinCache × LazyCertState) : PMF (CoinCache × LazyCertState) := do
  let (cc, ((node, (_, sk), certs), (nodes, edges))) := st
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (child, (cc', nodes')) ← jointNodeKey S T M n childPath (cc, nodes)
  (jointSignAt S T M node sk bit.toNat child.1 (cc', edges)).map fun (σ, (cc'', edges')) =>
    (cc'', ((childPath, child, certs ++ [(child.1, σ)]), (nodes', edges')))

private noncomputable def jointCertify (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf : List Bool) (st : JointInner) :
    PMF (CoinCache × LazyCertState) := do
  let (root, (cc₀, nodes₀)) ← jointNodeKey S T M n [] (st.1, st.2.1)
  Nat.iterate (fun m => m.bind (jointCertifyStep S T M n leaf)) (depth n - 1)
    (PMF.pure (cc₀, (([], root, []), (nodes₀, st.2.2))))

private noncomputable def jointCoinBody (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) : TreeBody JointInner :=
  fun leaf msg st =>
    (jointCertify S T depth M n leaf st).bind fun
      (cc', ((node, (_, sk), certs), (nodes', edges'))) =>
        (jointSignAt S T M node sk (leaf.getLastD false).toNat msg (cc', edges')).map
          fun (σ, (cc'', edges'')) => (encodeSignature leaf certs σ, (cc'', (nodes', edges'')))

private theorem map_dropCaches_jointNodeKey (S : IndexedSignatureScheme) (T : S.Seeded)
    (M n : ℕ) (path : List Bool) (cc : CoinCache) (ns : NodeKeyCache) :
    (jointNodeKey S T M n path (cc, ns)).map (fun out => (out.1, out.2.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (nodeKeyO S T n path)).run cc := by
  simp only [jointNodeKey, nodeKeyO, OracleComp.interpret_map, StateT.run_map,
    run_interpret_coinRequest, pmf_norm]

private theorem map_dropCaches_jointSignAt (S : IndexedSignatureScheme) (T : S.Seeded)
    (M : ℕ) (path sk : List Bool) (u : ℕ) (msg : List Bool) (cc : CoinCache)
    (es : EdgeSigCache) :
    (jointSignAt S T M path sk u msg (cc, es)).map (fun out => (out.1, out.2.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (signAtO S T path sk u msg)).run cc := by
  simp only [jointSignAt, signAtO, OracleComp.interpret_map, StateT.run_map,
    run_interpret_coinRequest, pmf_norm]

private theorem map_dropCaches_jointCertify (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf : List Bool) (st : JointInner) :
    (jointCertify S T depth M n leaf st).map (fun out => (out.2.1, out.1)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (certifyO S T depth n leaf)).run st.1 := by
  simp only [jointCertify, certifyO, OracleComp.run_interpret_bind, pmf_norm,
    ← map_dropCaches_jointNodeKey S T M n [] st.1 st.2.1]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨root, cc₀, nodes₀⟩ _ => ?_
  rw [OracleComp.run_interpret_iterate_pmf]
  refine (PMF.map_iterate_bind_of_invariant (jointCertifyStep S T M n leaf) _
    (fun out => (out.2.1, out.1)) (fun _ _ => True) (depth n - 1)
    (cc₀, (([], root, []), (nodes₀, st.2.2))) trivial fun _ _ out _ => ?_).1
  obtain ⟨c, ⟨node, ⟨_, sk⟩, certs⟩, ns, es⟩ := out
  refine ⟨?_, fun _ _ => trivial⟩
  simp only [jointCertifyStep, certifyStepO, OracleComp.run_interpret_bind,
    OracleComp.run_interpret_pure, pmf_norm,
    ← map_dropCaches_jointNodeKey S T M n (node ++ [leaf.getD node.length false]) c ns]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨child, c', _⟩ _ => ?_
  rw [← map_dropCaches_jointSignAt S T M node sk (leaf.getD node.length false).toNat child.1 c' es,
    PMF.bind_map]
  simp only [PMF.map, Function.comp_def]

private theorem map_dropCaches_jointCoinBody (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (leaf msg : List Bool) (st : JointInner) :
    (jointCoinBody S T depth M n leaf msg st).map (fun (sig, st') => (sig, st'.1)) =
      coinSignBody S T depth M n leaf msg st.1 := by
  simp only [jointCoinBody, coinSignBody, OracleComp.run_interpret_bind,
    OracleComp.run_interpret_pure, pmf_norm, ← map_dropCaches_jointCertify S T depth M n leaf st]
  refine PMF.bind_congr_on_support _ _ _ fun ⟨cc', ⟨node, ⟨_, sk⟩, certs⟩, _, es'⟩ _ => ?_
  rw [← map_dropCaches_jointSignAt S T M node sk (leaf.getLastD false).toNat msg cc' es',
    PMF.bind_map]
  simp only [PMF.map, Function.comp_def]

private theorem take_sub_one_append_getLastD {l : List Bool} {d : ℕ} (hd : 1 ≤ d)
    (hl : l.length = d) : l.take (d - 1) ++ [l.getLastD false] = l := by
  have hlt : d - 1 < l.length := by omega
  have hlast : l.getLastD false = l[d - 1] := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    simp only [hl, Option.getD_eq_iff, List.getElem?_eq_getElem hlt, true_or]
  rw [hlast, ← List.take_succ_eq_append_getElem hlt, show d - 1 + 1 = l.length by omega,
    List.take_length]

private def jointLazyInv (S : IndexedSignatureScheme) (T : S.Seeded) (M d n : ℕ)
    (root : List Bool × List Bool) (s : TreeState JointInner) : Prop :=
  let ((cc, (nodes, edges)), (_, seenLeaves, _)) := s
  nodes.lookup [] = some root ∧
  (∀ p k, (p, k) ∈ nodes → p.length < d ∧ k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
  (∀ p, p.length < d →
    nodes.lookup p =
      (cc.lookup (padRequest M (keyInput p))).map
        (fun w => T.keyGenWith n (w.take (T.keyGenBudget n)))) ∧
  (∀ q v σ, ((q, v), σ) ∈ edges →
    q.length < d ∧ v ≤ 1 ∧
      (q.length = d - 1 → ∃ l ∈ seenLeaves, l.length = d ∧ q = l.take (d - 1) ∧
        v = (l.getLastD false).toNat)) ∧
  (∀ p u, p.length < d → u ≤ 1 → edges.lookup (p, u) = none →
    cc.lookup (padRequest M (signInput p u)) = none) ∧
  ∀ p (b : Bool) σ, p.length + 1 < d → edges.lookup (p, b.toNat) = some σ →
    ∃ kp kc w, nodes.lookup p = some kp ∧ nodes.lookup (p ++ [b]) = some kc ∧
      cc.lookup (padRequest M (signInput p b.toNat)) = some w ∧
      σ = T.signWith kp.2 b.toNat kc.1 (w.take (T.signBudget kp.2 b.toNat kc.1))

private theorem jointLazyInv_insert_sign (S : IndexedSignatureScheme) (T : S.Seeded)
    {M d n : ℕ} (hwidth : 2 * d + 4 ≤ M) {root : List Bool × List Bool}
    {cc : CoinCache} {ns : NodeKeyCache} {es : EdgeSigCache}
    {q₀ q₁ sl₀ sl₁ : List (List Bool)} {b₀ b₁ : Bool}
    (hinv : jointLazyInv S T M d n root ((cc, ns, es), (q₀, sl₀, b₀)))
    (hsub : ∀ l ∈ sl₀, l ∈ sl₁) {node : List Bool} {u : ℕ} (hnode_lt : node.length < d)
    (hu : u ≤ 1) (w σ : List Bool)
    (hleaf : node.length = d - 1 →
      ∃ l ∈ sl₁, l.length = d ∧ node = l.take (d - 1) ∧ u = (l.getLastD false).toNat)
    (hinternal : ∀ b : Bool, b.toNat = u → node.length + 1 < d →
      ∃ kp kc, ns.lookup node = some kp ∧ ns.lookup (node ++ [b]) = some kc ∧
        σ = T.signWith kp.2 b.toNat kc.1 (w.take (T.signBudget kp.2 b.toNat kc.1))) :
    jointLazyInv S T M d n root
      (((padRequest M (signInput node u), w) :: cc, ns, ((node, u), σ) :: es), (q₁, sl₁, b₁)) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hinv
  refine ⟨h1, h2, fun p hp => ?_, fun q v σ' hmem => ?_, fun p u' hp hu' he => ?_,
    fun p b σ' hp he => ?_⟩
  · rw [lookup_cons_ne (padRequest_keyInput_ne_signInput hwidth hp hnode_lt hu)]
    exact h3 p hp
  · rcases List.mem_cons.mp hmem with hhead | htail
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Prod.mk.inj hhead).1; exact ⟨hnode_lt, hu, hleaf⟩
    · obtain ⟨hq, hv, hex⟩ := h4 q v σ' htail
      exact ⟨hq, hv, fun h => let ⟨l, hl, h'⟩ := hex h; ⟨l, hsub l hl, h'⟩⟩
  · have hne : (p, u') ≠ (node, u) := fun h => by simp [h] at he
    rw [lookup_cons_ne hne] at he
    rw [lookup_cons_ne fun h => hne (Prod.ext_iff.mpr
      (padRequest_signInput_injective hwidth hp hnode_lt hu' hu h))]
    exact h5 p u' hp hu' he
  · by_cases hpb : (p, b.toNat) = (node, u)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hpb
      rw [List.lookup_cons, beq_self_eq_true] at he
      obtain rfl := Option.some.inj he.symm
      obtain ⟨kp, kc, hkp, hkc, hσ⟩ := hinternal b rfl hp
      exact ⟨kp, kc, w, hkp, hkc, by simp, hσ⟩
    · rw [lookup_cons_ne hpb] at he
      obtain ⟨kp, kc, w', hkp, hkc, hw', hσ'⟩ := h6 p b σ' hp he
      refine ⟨kp, kc, w', hkp, hkc, ?_, hσ'⟩
      rw [lookup_cons_ne fun h => hpb (Prod.ext_iff.mpr
        (padRequest_signInput_injective hwidth (Nat.lt_of_succ_lt hp) hnode_lt
          (Bool.toNat_le b) hu h))]
      exact hw'

private theorem jointNodeKey_spec (S : IndexedSignatureScheme) (T : S.Seeded) {M d n : ℕ}
    (hwidth : 2 * d + 4 ≤ M) (hkgBudget : T.keyGenBudget n ≤ M)
    {root : List Bool × List Bool} {s : TreeState JointInner}
    (hinv : jointLazyInv S T M d n root s) {path : List Bool} (hpath : path.length < d) :
    ((jointNodeKey S T M n path (s.1.1, s.1.2.1)).map fun (k, (_, ns')) => (k, ns')) =
      ProbComp.eval (memoize (fun _ => S.keyGen n) path s.1.2.1) ∧
    ∀ k cc' ns', (k, (cc', ns')) ∈ (jointNodeKey S T M n path (s.1.1, s.1.2.1)).support →
      jointLazyInv S T M d n root ((cc', ns', s.1.2.2), s.2) ∧
      ns'.lookup path = some k ∧ k ∈ (ProbComp.eval (S.keyGen n)).support ∧
      ∀ q v, s.1.2.1.lookup q = some v → q ≠ path → ns'.lookup q = some v := by
  obtain ⟨⟨cc, nodes, edges⟩, log⟩ := s
  obtain ⟨hroot, hnodesMem, hnodesLk, hedgesMem, hedgesNone, hedgesSome⟩ := hinv
  have hrel := hnodesLk path hpath
  simp only [jointNodeKey, lazyCoinRequest, memoize]
  cases hcc : cc.lookup (padRequest M (keyInput path)) with
  | some w =>
    rw [hcc, Option.map_some] at hrel
    refine ⟨by simp only [hrel, pmf_norm], fun k cc' ns' hm => ?_⟩
    simp only [hrel] at hm; supp_cases hm
    exact ⟨⟨hroot, hnodesMem, hnodesLk, hedgesMem, hedgesNone, hedgesSome⟩, hrel,
      T.keyGenWith_mem_support n _, fun _ _ h _ => h⟩
  | none =>
    rw [hcc, Option.map_none] at hrel
    refine ⟨?_, fun k cc' ns' hm => ?_⟩
    · simp only [hrel, bind_pure_comp, pmf_norm]
      rw [T.eval_keyGen n _ le_rfl, ← BitString.uniformList_take hkgBudget]
      simp only [pmf_norm, PMF.map]
    · simp only [hrel, pmf_norm] at hm
      obtain ⟨w, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
      obtain ⟨rfl, h2⟩ := Prod.mk.inj heq.symm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      have hstay {q v} (hq : nodes.lookup q = some v) :
          ((path, T.keyGenWith n (w.take (T.keyGenBudget n))) :: nodes).lookup q = some v := by
        rw [lookup_cons_ne fun h => by subst h; rw [hq] at hrel; cases hrel]; exact hq
      refine ⟨⟨hstay hroot, fun p kp hp => ?_, fun p hp => ?_, hedgesMem,
          fun p u hp hu he => ?_, fun p b σ hp he => ?_⟩,
        by simp, T.keyGenWith_mem_support n _,
        fun q v hqv hne => by rw [lookup_cons_ne hne]; exact hqv⟩
      · rcases List.mem_cons.mp hp with hhead | htail
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hhead; exact ⟨hpath, T.keyGenWith_mem_support n _⟩
        · exact hnodesMem p kp htail
      · by_cases hpeq : p = path
        · subst hpeq; simp
        · rw [lookup_cons_ne hpeq, lookup_cons_ne fun h =>
            hpeq (padRequest_keyInput_injective hwidth hp hpath h)]
          exact hnodesLk p hp
      · rw [lookup_cons_ne (padRequest_keyInput_ne_signInput hwidth hpath hp hu).symm]
        exact hedgesNone p u hp hu he
      · obtain ⟨kp, kc, w', hkp, hkc, hw', hσ⟩ := hedgesSome p b σ hp he
        refine ⟨kp, kc, w', hstay hkp, hstay hkc, ?_, hσ⟩
        rw [lookup_cons_ne
          (padRequest_keyInput_ne_signInput hwidth hpath (Nat.lt_of_succ_lt hp)
            (Bool.toNat_le b)).symm]
        exact hw'

private theorem jointSignAt_internal_spec (S : IndexedSignatureScheme) (T : S.Seeded)
    {M d n : ℕ} (hwidth : 2 * d + 4 ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    {root kp kc : List Bool × List Bool} {cc : CoinCache} {ns : NodeKeyCache} {es : EdgeSigCache}
    {log : TreeLog} (hinv : jointLazyInv S T M d n root ((cc, ns, es), log))
    {node : List Bool} {bit : Bool} (hnode_lt : node.length + 1 < d)
    (hkp : ns.lookup node = some kp) (hkp_supp : kp ∈ (ProbComp.eval (S.keyGen n)).support)
    (hkc : ns.lookup (node ++ [bit]) = some kc)
    (hkc_supp : kc ∈ (ProbComp.eval (S.keyGen n)).support) :
    ((jointSignAt S T M node kp.2 bit.toNat kc.1 (cc, es)).map fun (σ, (_, es')) => (σ, es')) =
      ProbComp.eval (memoize (fun _ => S.sign kp.2 bit.toNat kc.1) (node, bit.toNat) es) ∧
    ∀ σ cc' es', (σ, (cc', es')) ∈ (jointSignAt S T M node kp.2 bit.toNat kc.1 (cc, es)).support →
      jointLazyInv S T M d n root ((cc', ns, es'), log) := by
  simp only [jointSignAt, lazyCoinRequest, memoize]
  cases hes : es.lookup (node, bit.toNat) with
  | some σ₀ =>
    obtain ⟨kp', kc', w, hkp', hkc', hw, hσ₀⟩ := hinv.2.2.2.2.2 node bit σ₀ hnode_lt hes
    cases Option.some.inj (hkp.symm.trans hkp')
    cases Option.some.inj (hkc.symm.trans hkc')
    refine ⟨by simp only [hw, pmf_norm, ← hσ₀], fun σ cc' es' hm => ?_⟩
    simp only [hw] at hm; supp_cases hm; exact hinv
  | none =>
    have hbu := Bool.toNat_le bit
    have hlt := Nat.lt_of_succ_lt hnode_lt
    have hcc := hinv.2.2.2.2.1 node bit.toNat hlt hbu hes
    have hbud := hsgBudget kp hkp_supp bit.toNat hbu kc.1 (Or.inr ⟨kc, hkc_supp, rfl⟩)
    simp only [hcc, bind_pure_comp, pmf_norm]
    refine ⟨?_, fun σ cc' es' hm => ?_⟩
    · rw [T.eval_sign kp.2 bit.toNat kc.1 _ le_rfl, ← BitString.uniformList_take hbud]
      simp only [pmf_norm, PMF.map]
    · obtain ⟨w, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
      obtain ⟨rfl, h2⟩ := Prod.mk.inj heq.symm
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h2
      refine jointLazyInv_insert_sign S T hwidth hinv (fun _ h => h) hlt hbu w _
        (fun _ => by omega) fun b hb _ => ?_
      obtain rfl := bool_eq_of_toNat_eq hb
      exact ⟨kp, kc, hkp, hkc, rfl⟩

private theorem jointCertify_spec (S : IndexedSignatureScheme) (T : S.Seeded) (depth : ℕ → ℕ)
    {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    {root : List Bool × List Bool} {s : TreeState JointInner}
    (hinv : jointLazyInv S T M (depth n) n root s) {leaf : List Bool}
    (hleaf : leaf.length = depth n) :
    ((jointCertify S T depth M n leaf s.1).map Prod.snd) =
      ProbComp.eval (certifyLazy S depth n root leaf s.1.2) ∧
    ∀ cc' cert ns' es',
      (cc', (cert, (ns', es'))) ∈ (jointCertify S T depth M n leaf s.1).support →
      jointLazyInv S T M (depth n) n root ((cc', ns', es'), s.2) ∧
      cert.1 = leaf.take (depth n - 1) ∧ ns'.lookup cert.1 = some cert.2.1 ∧
      cert.2.1 ∈ (ProbComp.eval (S.keyGen n)).support := by
  obtain ⟨⟨cc, nodes, edges⟩, log⟩ := s
  have hrootLen : ([] : List Bool).length < depth n := by simp; omega
  have hrootSome : nodes.lookup [] = some root := hinv.1
  have hnk0 : jointNodeKey S T M n [] (cc, nodes) = PMF.pure (root, (cc, nodes)) := by
    have hrel := hinv.2.2.1 [] hrootLen
    rw [hrootSome] at hrel
    cases hcc : cc.lookup (padRequest M (keyInput [])) with
    | none => simp [hcc] at hrel
    | some w =>
      rw [hcc, Option.map_some] at hrel
      simp only [jointNodeKey, lazyCoinRequest, memoize, hcc, hrootSome, pmf_norm,
        Option.some.inj hrel.symm]
  simp only [jointCertify, hnk0, certifyLazy, ProbComp.eval_iterate, pmf_norm]
  let stepInv (m : ℕ) (out : CoinCache × LazyCertState) : Prop :=
    jointLazyInv S T M (depth n) n root ((out.1, out.2.2), log) ∧
    out.2.1.1 = leaf.take m ∧ out.2.2.1.lookup out.2.1.1 = some out.2.1.2.1 ∧
    out.2.1.2.1 ∈ (ProbComp.eval (S.keyGen n)).support
  have hmain := PMF.map_iterate_bind_of_invariant (jointCertifyStep S T M n leaf)
    (fun s => ProbComp.eval (certifyStepLazy S n leaf s)) Prod.snd stepInv (depth n - 1)
    (cc, (([], root, []), (nodes, edges)))
    ⟨hinv, rfl, hrootSome, (hinv.2.1 [] root (lookup_mem hrootSome)).2⟩
    fun m hm ⟨c, ⟨node, ⟨pk, sk⟩, certs⟩, ns, es⟩ ⟨hinv_c, hnode_eq, hns_node, hkey_supp⟩ => by
      dsimp only at hinv_c hnode_eq hns_node hkey_supp
      have hnode_len : node.length = m := by
        rw [hnode_eq, List.length_take, hleaf, Nat.min_eq_left (by omega)]
      set bit := leaf.getD node.length false
      set cPath := node ++ [bit]
      have hchild_lt : cPath.length < depth n := by simp [cPath]; omega
      have hne : node ≠ cPath := fun h => by
        have := congrArg List.length h; simp [cPath] at this
      obtain ⟨hnk_eq, hnk_inv⟩ := jointNodeKey_spec S T hwidth hkgBudget hinv_c hchild_lt
      dsimp only [jointCertifyStep, certifyStepLazy]
      have hstep := PMF.map_bind_of_invariant (jointNodeKey S T M n cPath (c, ns))
        (ProbComp.eval (memoize (fun _ => S.keyGen n) cPath ns)) (fun x => (x.1, x.2.2))
        (fun x => jointLazyInv S T M (depth n) n root ((x.2.1, x.2.2, es), log) ∧
          x.2.2.lookup cPath = some x.1 ∧ x.1 ∈ (ProbComp.eval (S.keyGen n)).support ∧
          x.2.2.lookup node = some (pk, sk))
        (fun (child, c', ns') => (jointSignAt S T M node sk bit.toNat child.1 (c', es)).map
          fun (σ, c'', es') => (c'', ((cPath, child, certs ++ [(child.1, σ)]), (ns', es'))))
        (fun (child, ns') => (ProbComp.eval (memoize (fun _ => S.sign sk bit.toNat child.1)
          (node, bit.toNat) es)).map fun (σ, es') =>
            ((cPath, child, certs ++ [(child.1, σ)]), (ns', es')))
        Prod.snd (stepInv (m + 1))
        ⟨hnk_eq, fun ⟨child, c', ns'⟩ hm_nk => by
          obtain ⟨h1, h2, h3, h4⟩ := hnk_inv child c' ns' hm_nk
          exact ⟨h1, h2, h3, h4 node (pk, sk) hns_node hne⟩⟩
        fun ⟨child, c', ns'⟩ _ ⟨hinv_c', hns'_child, hchild_supp, hns'_node⟩ => by
          obtain ⟨hse_eq, hse_inv⟩ := jointSignAt_internal_spec S T hwidth hsgBudget hinv_c'
            (by omega) hns'_node hkey_supp hns'_child hchild_supp
          refine ⟨?_, fun out' hout' => ?_⟩
          · simpa only [pmf_norm, PMF.map] using congrArg (PMF.map fun (σ, es') =>
              ((cPath, child, certs ++ [(child.1, σ)]), (ns', es'))) hse_eq
          · obtain ⟨⟨σ, c'', es'⟩, hm_sa, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hout'
            refine ⟨hse_inv σ c'' es' hm_sa, ?_, hns'_child, hchild_supp⟩
            have hlt : m < leaf.length := by omega
            dsimp only [stepInv, cPath, bit]
            rw [hnode_len, hnode_eq, List.getD_eq_getElem _ _ hlt,
              List.take_succ_eq_append_getElem hlt]
      exact ⟨by simpa only [pmf_norm, PMF.map] using hstep.1, hstep.2⟩
  exact ⟨hmain.1, fun cc' cert ns' es' hm => hmain.2 (cc', (cert, (ns', es'))) hm⟩

private theorem jointCoinBody_step_lazy (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    (root : List Bool × List Bool) (req : Unit × List Bool) (s : TreeState JointInner)
    (hinv : jointLazyInv S T M (depth n) n root s) :
    (guardedTreeHandler depth n (jointCoinBody S T depth M n) req s).map
        (fun (a, s') => (a, s'.1.2, s'.2)) =
      ProbComp.eval (lazySignHandler S depth n root req (s.1.2, s.2)) ∧
    ∀ a s', (a, s') ∈ (guardedTreeHandler depth n (jointCoinBody S T depth M n) req s).support →
      jointLazyInv S T M (depth n) n root s' := by
  rw [eval_lazySignHandler_eq]
  have hinv_init : ∀ b', jointLazyInv S T M (depth n) n root
      (s.1, req.2 :: s.2.1, s.2.2.1, b') := fun _ => hinv
  refine guardedTreeHandler_map depth n (jointCoinBody S T depth M n)
    (lazySignBody S depth n root) Prod.snd (jointLazyInv S T M (depth n) n root) req s
    hinv_init fun hmsg _ leaf hleaf_supp hseen => ?_
  have hleaf_len := BitString.length_of_mem_support_uniformList hleaf_supp
  have hnotMem : leaf ∉ s.2.2.1 := fun h => by simp [h] at hseen
  obtain ⟨hcert_eq, hcert_inv⟩ :=
    jointCertify_spec S T depth hdepth_pos hwidth hkgBudget hsgBudget hinv hleaf_len
  dsimp only [jointCoinBody, lazySignBody]
  refine (fun h => ⟨h.1, fun sig inner' hm => h.2 (sig, inner') hm⟩)
    (PMF.map_bind_of_invariant (jointCertify S T depth M n leaf s.1)
      (ProbComp.eval (certifyLazy S depth n root leaf s.1.2)) Prod.snd
      (fun (cc', cert, ns', es') => jointLazyInv S T M (depth n) n root ((cc', ns', es'), s.2) ∧
        cert.1 = leaf.take (depth n - 1) ∧ ns'.lookup cert.1 = some cert.2.1 ∧
        cert.2.1 ∈ (ProbComp.eval (S.keyGen n)).support)
      _ _ (fun (sig, st') => (sig, st'.2))
      (fun (x : List Bool × JointInner) =>
        jointLazyInv S T M (depth n) n root (x.2, req.2 :: s.2.1, leaf :: s.2.2.1, false))
      ⟨hcert_eq, fun ⟨cc', cert, ns', es'⟩ hm => hcert_inv cc' cert ns' es' hm⟩
      fun ⟨cc', ⟨node, ⟨pk, sk⟩, certs⟩, ns', es'⟩ _ ⟨hinv_c', hnode_eq, _, hkey_supp⟩ => by
        dsimp only at hnode_eq hkey_supp ⊢
        have hnode_len : node.length = depth n - 1 := by
          rw [hnode_eq, List.length_take, hleaf_len, Nat.min_eq_left (by omega)]
        have hnode_lt : node.length < depth n := by omega
        set uLast := (leaf.getLastD false).toNat
        have hes'_none : es'.lookup (node, uLast) = none := by
          cases hlk : es'.lookup (node, uLast) with
          | none => rfl
          | some σ₀ =>
            exfalso
            obtain ⟨l, hl_mem, hl_len, hq_eq, hv_eq⟩ :=
              (hinv_c'.2.2.2.1 node uLast σ₀ (lookup_mem hlk)).2.2 hnode_len
            have hleaf_eq : leaf = l := by
              rw [← take_sub_one_append_getLastD hdepth_pos hleaf_len,
                ← take_sub_one_append_getLastD hdepth_pos hl_len, ← hnode_eq, hq_eq,
                bool_eq_of_toNat_eq hv_eq]
            exact hnotMem (hleaf_eq ▸ hl_mem)
        have hcc'_none := hinv_c'.2.2.2.2.1 node uLast hnode_lt (Bool.toNat_le _) hes'_none
        have hbud := hsgBudget (pk, sk) hkey_supp uLast (Bool.toNat_le _) req.2 (Or.inl hmsg)
        simp only [jointSignAt, lazyCoinRequest, memoize, hes'_none, hcc'_none,
          bind_pure_comp, pmf_norm]
        refine ⟨?_, fun x hm => ?_⟩
        · rw [T.eval_sign sk uLast req.2 _ le_rfl, ← BitString.uniformList_take hbud]
          simp only [pmf_norm, PMF.map]
        · obtain ⟨w, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
          exact jointLazyInv_insert_sign S T hwidth hinv_c' (fun _ h => List.mem_cons_of_mem _ h)
            hnode_lt (Bool.toNat_le _) w _
            (fun _ => ⟨leaf, List.mem_cons_self, hleaf_len, hnode_eq, rfl⟩)
            fun _ _ hp => by omega)

private noncomputable def coinGameWith (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) (M n : ℕ) (adversary : Forger)
    (h : Unit × List Bool → StateT (TreeState CoinCache) PMF (List Bool)) (w₀ : List Bool) :
    PMF Bool :=
  let root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
  let pk := encPair encUnary encBits (n, root.1)
  let init : TreeState CoinCache := ([(padRequest M (keyInput []), w₀)], ([], [], false))
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) h)
    (adversary n pk)).run init).map fun (msig, (_, queried, _, _)) =>
      (msig.1.length == n) && !queried.contains msig.1 && verify S depth pk msig.1 msig.2

private theorem eval_treeIdealGame_eq_unguarded (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (treeIdealGame S T depth N adversary n) =
      (BitString.uniformList (N n)).bind
        (coinGameWith S T depth (N n) n adversary
          (unguardedTreeHandler depth n (coinSignBody S T depth (N n) n))) := by
  set M := N n
  rw [eval_treeIdealGame_eq_lazyCoin]
  have hroot : (OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
      (nodeKeyO S T n [])).run [] =
      (BitString.uniformList M).map fun w₀ =>
        (T.keyGenWith n (w₀.take (T.keyGenBudget n)), [(padRequest M (keyInput []), w₀)]) := by
    simp only [nodeKeyO, OracleComp.interpret_map, StateT.run_map, run_interpret_coinRequest,
      lazyCoinRequest, memoize, List.lookup_nil, pmf_norm, PMF.map]
  simp only [simulateTreeGame, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
    pmf_norm]
  rw [hroot, PMF.bind_map]
  refine PMF.bind_congr_on_support _ _ _ fun w₀ _ => ?_
  set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
  set pk := encPair encUnary encBits (n, root.1)
  set cc₀ : CoinCache := [(padRequest M (keyInput []), w₀)]
  have hstep : ∀ req (s : TreeState CoinCache),
      ((unguardedTreeHandler depth n (coinSignBody S T depth M n) req s).map
        fun (a, s') => (a, (s'.2.1, s'.1))) =
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (lazyCoinHandler M))
        (signHandler S T depth n req s.2.1)).run s.1).map fun ((a, b), c) => (a, b, c)) := by
    rintro req ⟨cc, queried, seen, bad⟩
    simp only [unguardedTreeHandler, signHandler, signO]
    split_ifs with hmsg
    · rw [bind_assoc, OracleComp.run_interpret_bind, ProbOracleComp.run_interpret_sample,
        BitString.eval_sampleList]
      simp only [pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun leaf _ => ?_
      simp only [coinSignBody, OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
        pmf_norm]
    · simp only [pure_bind, OracleComp.run_interpret_pure, pmf_norm]
  have hflat := ProbOracleComp.run_interpret_run_interpret (signHandler S T depth n)
    (lazyCoinHandler M) (adversary n pk) [] cc₀
  have hunguard := ProbOracleComp.run_interpret_map_state
    (unguardedTreeHandler depth n (coinSignBody S T depth M n))
    (fun q (st : List (List Bool) × CoinCache) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k)) (lazyCoinHandler M))
        (signHandler S T depth n q st.1)).run st.2).map fun ((a, b), c) => (a, b, c))
    (fun s => (s.2.1, s.1)) hstep (adversary n pk) (cc₀, [], [], false)
  have hcomb := congrArg (PMF.map fun ((msig, queried), _) =>
      (msig.1.length == n) && !queried.contains msig.1 && verify S depth pk msig.1 msig.2)
    (hflat.trans (congrArg (PMF.map fun (a, b, c) => ((a, b), c)) hunguard.symm))
  simpa only [coinGameWith, pmf_norm, PMF.map] using hcomb

private theorem eval_lazyTreeGame_eq_guarded (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth : ℕ → ℕ) {M n : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ M)
    (hkgBudget : T.keyGenBudget n ≤ M)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → T.signBudget keys.2 u msg ≤ M)
    (adversary : Forger) :
    ProbComp.eval (lazyTreeGame S depth adversary n) =
      (BitString.uniformList M).bind
        (coinGameWith S T depth M n adversary
          (guardedTreeHandler depth n (coinSignBody S T depth M n))) := by
  have hrootLaw : ProbComp.eval (S.keyGen n) =
      (BitString.uniformList M).map fun w₀ => T.keyGenWith n (w₀.take (T.keyGenBudget n)) := by
    rw [T.eval_keyGen n _ le_rfl, ← BitString.uniformList_take hkgBudget, PMF.map_comp]; rfl
  simp only [lazyTreeGame, hrootLaw, ProbOracleComp.eval_run_interpret, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun w₀ _ => ?_
  set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
  set pk := encPair encUnary encBits (n, root.1)
  set jInit : TreeState JointInner :=
    (([(padRequest M (keyInput []), w₀)], [([], root)], []), ([], [], false))
  have hrootLen : ([] : List Bool).length < depth n := by simp; omega
  have hjInv : jointLazyInv S T M (depth n) n root jInit := by
    refine ⟨by simp, ?_, ?_, ?_, ?_, ?_⟩
    · intro p k hp; obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp hp)
      exact ⟨hrootLen, T.keyGenWith_mem_support n _⟩
    · intro p hp; by_cases hp0 : p = []
      · subst hp0; simp [root]
      · simp only [lookup_cons_ne hp0,
          lookup_cons_ne fun h => hp0 (padRequest_keyInput_injective hwidth hp hrootLen h),
          List.lookup_nil, Option.map_none]
    · intro _ _ _ h; cases h
    · intro p u hp hu _
      simp only [lookup_cons_ne (padRequest_keyInput_ne_signInput hwidth hrootLen hp hu).symm,
        List.lookup_nil]
    · intro _ _ _ _ h; cases h
  have hprojLazy := ProbOracleComp.run_interpret_map_state_of_invariant
    (guardedTreeHandler depth n (jointCoinBody S T depth M n))
    (fun q s => ProbComp.eval (lazySignHandler S depth n root q s))
    (fun s => (s.1.2, s.2)) (jointLazyInv S T M (depth n) n root)
    (fun q s hs a s' hm =>
      (jointCoinBody_step_lazy S T depth hdepth_pos hwidth hkgBudget hsgBudget root q s hs).2
        a s' hm)
    (fun q s hs =>
      (jointCoinBody_step_lazy S T depth hdepth_pos hwidth hkgBudget hsgBudget root q s hs).1)
    (adversary n pk) jInit hjInv
  have hprojGuard := ProbOracleComp.run_interpret_map_state
    (guardedTreeHandler depth n (jointCoinBody S T depth M n))
    (guardedTreeHandler depth n (coinSignBody S T depth M n))
    (fun s => (s.1.1, s.2))
    (fun q s => (guardedTreeHandler_map depth n (jointCoinBody S T depth M n)
      (coinSignBody S T depth M n) Prod.fst (fun _ => True) q s (fun _ => trivial)
      fun _ _ leaf _ _ => ⟨map_dropCaches_jointCoinBody S T depth M n leaf q.2 s.1,
        fun _ _ _ => trivial⟩).1)
    (adversary n pk) jInit
  have hwinL := congrArg (PMF.map fun (msig, (_, (queried, _, _))) =>
    (msig.1.length == n) && !queried.contains msig.1 && verify S depth pk msig.1 msig.2)
    hprojLazy.symm
  have hwinG := congrArg (PMF.map fun (msig, (_, queried, _, _)) =>
    (msig.1.length == n) && !queried.contains msig.1 && verify S depth pk msig.1 msig.2)
    hprojGuard
  dsimp only [coinGameWith]
  simp only [pmf_norm] at hwinL hwinG ⊢
  simpa only [PMF.map, Function.comp_def] using hwinL.trans hwinG

/-- **From ideal coins to lazy tree signing**: when `N n` covers all padded tree request widths and
seeded key/signature coin budgets, replacing the uniform random function in `treeIdealGame` with
lazy node keys, lazy edge signatures, and leaf-collision aborts (`lazyTreeGame`) loses at most
`(Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)` across any `Q`-query adversary. -/
theorem succProbability_treeIdealGame_le_lazy (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N : ℕ → ℕ) {n Q : ℕ} (hdepth_pos : 1 ≤ depth n) (hwidth : 2 * depth n + 4 ≤ N n)
    (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) ≤
      Game.succProbability (ProbComp.eval (lazyTreeGame S depth adversary n)) +
        (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) := by
  set err : ℝ≥0 := (Q ^ 2 : ℝ≥0) / 2 ^ (depth n + 1)
  have hle_enn : ProbComp.eval (treeIdealGame S T depth N adversary n) true ≤
      ProbComp.eval (lazyTreeGame S depth adversary n) true + (err : ℝ≥0∞) := by
    rw [eval_treeIdealGame_eq_unguarded,
      eval_lazyTreeGame_eq_guarded S T depth hdepth_pos hwidth hkgBudget hsgBudget adversary]
    refine Probability.PMF.bind_apply_le_add_const_on_support _ true fun w₀ _ => ?_
    set root := T.keyGenWith n (w₀.take (T.keyGenBudget n))
    set pk := encPair encUnary encBits (n, root.1)
    have hiub := identicalUntilBad_treeHandler depth n (coinSignBody S T depth (N n) n)
    have hdiff := OracleComp.IdenticalUntilBad.bind_apply_le hiub (adversary n pk)
      ([(padRequest (N n) (keyInput []), w₀)], [], [], false)
      (fun (msig, (_, queried, _, _)) => PMF.pure
        ((msig.1.length == n) && !queried.contains msig.1 && verify S depth pk msig.1 msig.2)) true
    rw [OracleComp.IdenticalUntilBad.bad_eq hiub] at hdiff
    exact hdiff.trans (add_le_add le_rfl (toOuterMeasure_bad_guardedTreeHandler_le depth n Q _
      (hq root (T.keyGenWith_mem_support n _)) _ []))
  have h := ENNReal.toNNReal_mono
    (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, ENNReal.coe_ne_top⟩) hle_enn
  rwa [ENNReal.toNNReal_add (PMF.apply_ne_top _ _) ENNReal.coe_ne_top, ENNReal.toNNReal_coe] at h

end IdealToLazy

/-! ### From lazy tree signing to indexed forgery -/

section LazyToIndexed

/-- Full log entry `(path, slotIdx, u, msg)` recorded on every fresh edge signature in the
pre-sampled tree experiment. -/
private abbrev AllSignedLog := List (List Bool × ℕ × ℕ × List Bool)

/-- Inner state of the pre-sampled tree handler: `(visited, edges, allSigned)`. -/
private abbrev PresampledInner := NodeSlotCache × EdgeSigCache × AllSignedLog

/-- State of the pre-sampled tree signing handler. -/
private abbrev PresampledState := TreeState PresampledInner

private def initPresampledState : PresampledState := (([([], 0)], [], []), ([], [], false))

/-- Extract the indexed signing oracle log `(u, msg)` at slot `target` from `allSigned`. -/
private def signedLogOf (target : ℕ) (allSigned : AllSignedLog) : List (ℕ × List Bool) :=
  (allSigned.filter fun e => e.2.1 == target).map fun e => (e.2.2.1, e.2.2.2)

/-- Pure counterpart of `visitNodeM`. -/
private def visitNodePure (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) :
    ℕ × NodeSlotCache :=
  match visited.lookup path with
  | some idx => (idx, visited)
  | none => let idx := min visited.length cap; (idx, (path, idx) :: visited)

private theorem run_interpret_visitNodeM {External : Type}
    (oracle : Unit × List Bool → StateT External PMF (List Bool))
    (cap : ℕ) (path : List Bool) (visited : NodeSlotCache) (ext : External) :
    (OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j)) oracle)
      (visitNodeM cap path visited)).run ext =
      PMF.pure (visitNodePure cap path visited, ext) := by
  simp only [visitNodeM, visitNodePure, memoize]
  cases visited.lookup path <;>
    simp only [pure_bind, OracleComp.run_interpret_pure, Probability.PMF.monad_pure_eq_pure]

private theorem filter_headD_of_mem_unique (visited : NodeSlotCache) {p : List Bool}
    {idx : ℕ} (hmem : (p, idx) ∈ visited)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂) :
    ((visited.filter fun e => e.2 == idx).headD ([], 0)).1 = p := by
  have hin : (p, idx) ∈ visited.filter fun e => e.2 == idx :=
    List.mem_filter.mpr ⟨hmem, beq_self_eq_true idx⟩
  cases hflt : visited.filter fun e => e.2 == idx with
  | nil => simp [hflt] at hin
  | cons hd tl =>
    obtain ⟨hhd_vis, hhd_eq⟩ := List.mem_filter.mp (hflt ▸ List.mem_cons_self)
    rw [List.headD_cons, huniq hd hhd_vis (p, idx) hmem (beq_iff_eq.mp hhd_eq)]

private theorem slot_bound_lt_dyadicSize {Q d B : ℕ} (hd : 1 ≤ d) (hB : Q * d ≤ B) :
    1 + Q * (d - 1) < dyadicSize B := by
  rcases Nat.eq_zero_or_pos Q with rfl | hQ
  · have := two_le_dyadicSize B; omega
  · have := Nat.mul_sub_left_distrib Q d 1
    have : Q ≤ Q * d := Nat.le_mul_of_pos_right Q hd
    have := lt_dyadicSize B
    omega

private theorem fst_getD_splice (front back : List (List Bool × List Bool))
    (x : List Bool × List Bool) (idx : ℕ) :
    ((front ++ (x.1, []) :: back).getD idx ([], [])).1 =
      ((front ++ x :: back).getD idx ([], [])).1 := by
  by_cases h : idx = front.length
  · subst h; simp only [List.getD_append_cons_length]
  · rw [List.getD_append_cons_of_ne front back (x.1, []) x ([], []) h]

/-- Local edge-signing step on pre-sampled `keys`, truncating fresh signatures to `sigCap` bits and
recording `(path, idx, u, msg)` in `allSigned`. -/
private noncomputable def localSignEdge (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (sigCap : ℕ) (path : List Bool) (idx u : ℕ)
    (msg : List Bool) (ea : EdgeSigCache × AllSignedLog) :
    PMF (List Bool × (EdgeSigCache × AllSignedLog)) :=
  match ea.1.lookup (path, u) with
  | some σ => PMF.pure (σ, ea)
  | none =>
    (ProbComp.eval (S.sign (keys.getD idx ([], [])).2 u msg)).map fun raw =>
      let σ := raw.take sigCap
      (σ, (((path, u), σ) :: ea.1, (path, idx, u, msg) :: ea.2))

private theorem mem_support_localSignEdge {S : IndexedSignatureScheme}
    {keys : List (List Bool × List Bool)} {sigCap : ℕ} {path : List Bool} {idx u : ℕ}
    {msg : List Bool} {edges : EdgeSigCache} {allSigned : AllSignedLog}
    {σ : List Bool} {edges' : EdgeSigCache} {allSigned' : AllSignedLog}
    (hm : (σ, edges', allSigned') ∈
      (localSignEdge S keys sigCap path idx u msg (edges, allSigned)).support) :
    (edges' = edges ∧ allSigned' = allSigned) ∨
      (edges' = ((path, u), σ) :: edges ∧ allSigned' = (path, idx, u, msg) :: allSigned) := by
  simp only [localSignEdge] at hm
  cases hlk : edges.lookup (path, u) with
  | some σ₀ => rw [hlk] at hm; supp_cases hm; exact Or.inl ⟨rfl, rfl⟩
  | none => rw [hlk] at hm; supp_cases hm with ⟨raw, -, rfl, rfl, rfl⟩; exact Or.inr ⟨rfl, rfl⟩

private abbrev LocalCertState :=
  (List Bool × ℕ × List (List Bool × List Bool)) × PresampledInner

private noncomputable def localCertifyStep (S : IndexedSignatureScheme)
    (keys : List (List Bool × List Bool)) (sigCap : ℕ) (leaf : List Bool)
    (state : LocalCertState) : PMF LocalCertState :=
  let ((node, idx, certs), (visited, edges, allSigned)) := state
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, visited') := visitNodePure keys.length childPath visited
  let childPk := (keys.getD childIdx ([], [])).1
  (localSignEdge S keys sigCap node idx bit.toNat childPk (edges, allSigned)).map
    fun (σ, (edges', allSigned')) =>
      ((childPath, childIdx, certs ++ [(childPk, σ)]), (visited', edges', allSigned'))

private noncomputable def localCertify (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (leaf : List Bool)
    (caches : PresampledInner) : PMF LocalCertState :=
  Nat.iterate (fun d => d.bind (localCertifyStep S keys sigCap leaf)) (depth n - 1)
    (PMF.pure (([], 0, []), caches))

private noncomputable def localSignBody (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) : TreeBody PresampledInner :=
  fun leaf msg caches =>
    (localCertify S depth keys sigCap n leaf caches).bind fun
      ((node, idx, certs), (visited', edges', allSigned')) =>
        (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat msg
          (edges', allSigned')).map fun (σ, (edges'', allSigned'')) =>
            (encodeSignature leaf certs σ, (visited', edges'', allSigned''))

private noncomputable def localTreeHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) :
    Unit × List Bool → StateT PresampledState PMF (List Bool) :=
  guardedTreeHandler depth n (localSignBody S depth keys sigCap n)

/-- Pre-sampled tree experiment: sample `dyadicSize (slotBound n)` key pairs of `S`, then run
`adversary` against `localTreeHandler`. -/
private noncomputable def presampledExp (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    PMF (List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) := do
  let keys ← ProbComp.eval (OracleComp.replicate (dyadicSize (slotBound n)) (S.keyGen n))
  let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  ((OracleComp.interpret
    (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
      (localTreeHandler S depth keys (sigCap n) n))
    (adversary n pk)).run initPresampledState).map fun (msig, st) => (keys, msig, st)

/-- Whether `indexedForgerAt` at `target` wins on a pre-sampled outcome. -/
private def plantedWin (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n target : ℕ)
    (out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) : Bool :=
  let (keys, msig, ((visited, _, allSigned), _)) := out
  let cand := extractForgery (depth n) target visited msig.1 msig.2
  !(signedLogOf target allSigned).contains (cand.1, cand.2.1) &&
    S.verify (keys.getD target ([], [])).1 cand.1 cand.2.1 cand.2.2

/-- Whether `adversary` wins `lazyTreeGame` on a pre-sampled outcome. -/
private def treeWinOfPresampled (S : IndexedSignatureScheme) (depth : ℕ → ℕ) (n : ℕ)
    (out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState) : Bool :=
  let (keys, msig, (_, (queried, _, _))) := out
  let pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  (msig.1.length == n) && !queried.contains msig.1 && verify S depth pk msig.1 msig.2

/-! #### Simulation of `plantedTreeHandler` + `indexedSigningOracle` by `localTreeHandler` -/

private def slotEdgeInv (K : ℕ) (st : PresampledInner) : Prop :=
  let (visited, edges, allSigned) := st
  ([], 0) ∈ visited ∧
  (∀ e ∈ visited, e.2 < K → e.2 < visited.length) ∧
  (∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) ∧
  ∀ p idx u m, (p, idx, u, m) ∈ allSigned → (p, idx) ∈ visited ∧ edges.lookup (p, u) ≠ none

private theorem visitNodePure_inv {P : List Bool → Prop} {K : ℕ} {visited : NodeSlotCache}
    (path : List Bool) (hp : P path)
    (hlt : ∀ e ∈ visited, P e.1 ∧ (e.2 < K → e.2 < visited.length))
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) :
    let (idx, visited') := visitNodePure K path visited
    (path, idx) ∈ visited' ∧
    (∀ e ∈ visited, e ∈ visited') ∧
    visited'.length ≤ visited.length + 1 ∧
    (∀ e ∈ visited', P e.1 ∧ (e.2 < K → e.2 < visited'.length)) ∧
    (∀ e₁ ∈ visited', ∀ e₂ ∈ visited', e₁.2 < K → e₁.2 = e₂.2 → e₁ = e₂) ∧
    (∀ e ∈ visited', e ∈ visited ∨ e = (path, min visited.length K)) := by
  simp only [visitNodePure]
  cases hlk : visited.lookup path with
  | some idx =>
    exact ⟨lookup_mem hlk, fun _ h => h, Nat.le_succ _, hlt, huniq, fun _ h => Or.inl h⟩
  | none =>
    refine ⟨List.mem_cons_self, fun _ h => List.mem_cons_of_mem _ h, le_rfl, fun e he => ?_,
      fun e₁ he₁ e₂ he₂ he₁K heq => ?_, fun _ h => (List.mem_cons.mp h).symm⟩
    · rcases List.mem_cons.mp he with rfl | ht
      · exact ⟨hp, fun _ => Nat.lt_succ_of_le (Nat.min_le_left _ _)⟩
      · exact ⟨(hlt e ht).1, fun hK => Nat.lt_succ_of_lt ((hlt e ht).2 hK)⟩
    · rcases List.mem_cons.mp he₁ with rfl | ht₁ <;> rcases List.mem_cons.mp he₂ with rfl | ht₂
      · rfl
      · have := (hlt e₂ ht₂).2 (heq ▸ he₁K); dsimp only at he₁K heq; omega
      · have := (hlt e₁ ht₁).2 he₁K; dsimp only at heq; omega
      · exact huniq e₁ ht₁ e₂ ht₂ he₁K heq

private theorem localSignEdge_planted_spec (S : IndexedSignatureScheme)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    {visited : NodeSlotCache} {edges : EdgeSigCache} {allSigned : AllSignedLog}
    (hslotLt : front.length < (front ++ x :: back).length)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited,
      e₁.2 < (front ++ x :: back).length → e₁.2 = e₂.2 → e₁ = e₂)
    (hall : ∀ p₀ idx₀ u₀ m₀, (p₀, idx₀, u₀, m₀) ∈ allSigned →
      (p₀, idx₀) ∈ visited ∧ edges.lookup (p₀, u₀) ≠ none)
    {path : List Bool} {idx u : ℕ} (hvis : (path, idx) ∈ visited) (hu : u ≤ 1)
    (msg : List Bool) :
    ((localSignEdge S (front ++ x :: back) sigCap path idx u msg (edges, allSigned)).map
      fun (σ, (edges', allSigned')) => (σ, (edges', signedLogOf front.length allSigned'))) =
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (signEdgeM S (front ++ (x.1, []) :: back) front.length sigCap path idx u msg edges)).run
        (signedLogOf front.length allSigned)).map
          (fun ((σ, edges'), signed') => (σ, (edges', signed'))) ∧
    ∀ σ edges' allSigned',
      (σ, (edges', allSigned')) ∈
        (localSignEdge S (front ++ x :: back) sigCap path idx u msg (edges, allSigned)).support →
      ∀ p₀ idx₀ u₀ m₀, (p₀, idx₀, u₀, m₀) ∈ allSigned' →
        (p₀, idx₀) ∈ visited ∧ edges'.lookup (p₀, u₀) ≠ none := by
  refine ⟨?_, fun σ edges' allSigned' hm p₀ idx₀ u₀ m₀ hm_all => ?_⟩
  · simp only [localSignEdge, signEdgeM, memoize]
    cases hes : edges.lookup (path, u) with
    | some σ₀ => simp only [OracleComp.run_interpret_pure, pmf_norm]
    | none =>
      simp only [signEdgeRaw]
      by_cases hidx : idx = front.length
      · subst hidx
        have hnotMem : u ∉ (signedLogOf front.length allSigned).map Prod.fst := by
          simp only [signedLogOf, List.mem_map, List.mem_filter, beq_iff_eq]
          rintro ⟨_, ⟨⟨p₀, idx₀, u₀, m₀⟩, ⟨hm_all, rfl⟩, rfl⟩, rfl⟩
          obtain ⟨hp₀_vis, hp₀_lk⟩ := hall p₀ front.length u₀ m₀ hm_all
          exact hp₀_lk (congrArg (fun p => edges.lookup (p, u₀))
            (Prod.mk.inj (huniq _ hp₀_vis _ hvis hslotLt rfl)).1 |>.trans hes)
        have huLt : u < S.capacity n := by omega
        have hlog : signedLogOf front.length ((path, front.length, u, msg) :: allSigned) =
            (u, msg) :: signedLogOf front.length allSigned := by
          simp only [signedLogOf, List.filter_cons, beq_self_eq_true, ↓reduceIte, List.map_cons]
        simp only [↓reduceIte, List.getD_append_cons_length,
          OracleComp.run_interpret_bind, OracleComp.interpret_map,
          ProbOracleComp.interpret_query, OracleComp.run_interpret_pure,
          StateT.run_map, IndexedSignatureScheme.indexedSigningOracle,
          IndexedSignatureScheme.requestDecoder.decode_enc, hlog, pmf_norm]
        dsimp only [StateT.run]
        simp only [huLt, hnotMem, not_false_eq_true, and_self, ↓reduceIte, pmf_norm, PMF.map]
      · have hlog : signedLogOf front.length ((path, idx, u, msg) :: allSigned) =
            signedLogOf front.length allSigned := by
          simp only [signedLogOf, List.filter_cons, beq_false_of_ne hidx, Bool.false_eq_true,
            ↓reduceIte]
        rw [List.getD_append_cons_of_ne front back (x.1, []) x ([], []) hidx]
        simp only [hidx, ↓reduceIte, interp_norm, hlog, pmf_norm, PMF.map]
  · rcases mem_support_localSignEdge hm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hall p₀ idx₀ u₀ m₀ hm_all
    · rcases List.mem_cons.mp hm_all with hhead | ht
      · obtain ⟨rfl, h2⟩ := Prod.mk.inj hhead
        obtain ⟨rfl, h3⟩ := Prod.mk.inj h2
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
        exact ⟨hvis, by simp⟩
      · obtain ⟨hpv, hpl⟩ := hall p₀ idx₀ u₀ m₀ ht
        refine ⟨hpv, ?_⟩
        rw [List.lookup_cons]; cases (p₀, u₀) == (path, u) <;> [exact hpl; rintro ⟨⟩]

private theorem localCertify_planted_spec (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    (leaf : List Bool) {caches : PresampledInner}
    (hinv : slotEdgeInv (front ++ x :: back).length caches) :
    let keys := front ++ x :: back
    let keys' := front ++ (x.1, []) :: back
    ((localCertify S depth keys sigCap n leaf caches).map
      fun (c, (v, e, a)) => ((c, (v, e)), signedLogOf front.length a)) =
      (OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (certifyPlanted S depth keys' front.length sigCap n leaf (caches.1, caches.2.1))).run
        (signedLogOf front.length caches.2.2) ∧
    ∀ c v e a, (c, (v, e, a)) ∈ (localCertify S depth keys sigCap n leaf caches).support →
      (c.1, c.2.1) ∈ v ∧ slotEdgeInv keys.length (v, e, a) := by
  obtain ⟨visited, edges, allSigned⟩ := caches
  set keys := front ++ x :: back
  set keys' := front ++ (x.1, []) :: back
  have hslotLt : front.length < keys.length := by simp [keys]
  have hlenEq : keys'.length = keys.length := by simp [keys, keys']
  dsimp only [localCertify, certifyPlanted]
  rw [OracleComp.run_interpret_iterate_pmf]
  have hmain := PMF.map_iterate_bind_of_invariant
    (localCertifyStep S keys sigCap leaf)
    (fun (cs, sg) => (OracleComp.interpret
      (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
        (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
      (certifyStepPlanted S keys' front.length sigCap leaf cs)).run sg)
    (fun (c, (v, e, a)) => ((c, (v, e)), signedLogOf front.length a))
    (fun _ ((node, idx, _), st) => (node, idx) ∈ st.1 ∧ slotEdgeInv keys.length st)
    (depth n - 1) (([], 0, []), (visited, edges, allSigned)) ⟨hinv.1, hinv⟩
    fun _ _ ⟨⟨node, idx, certs⟩, v, e, a⟩ ⟨hnode_v, hroot_v, hlt_v, huniq_v, hall_v⟩ => by
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      have hvp := visitNodePure_inv (P := fun _ => True) childPath trivial
        (fun ent he => ⟨trivial, hlt_v ent he⟩) huniq_v
      set vp := visitNodePure keys.length childPath v
      have hedg := localSignEdge_planted_spec S (sigCap := sigCap) hcap hslotLt
        hvp.2.2.2.2.1 (fun p₀ i₀ u₀ m₀ hm => ⟨hvp.2.1 _ (hall_v _ _ _ _ hm).1,
          (hall_v _ _ _ _ hm).2⟩) (hvp.2.1 _ hnode_v) (Bool.toNat_le bit)
        (keys.getD vp.1 ([], [])).1
      refine ⟨?_, fun st' hst' => ?_⟩
      · simp only [localCertifyStep, certifyStepPlanted, hlenEq, OracleComp.run_interpret_bind,
          OracleComp.run_interpret_pure, run_interpret_visitNodeM, pmf_norm]
        have h1 := congrArg (PMF.map fun (σ, (e', s')) =>
          (((childPath, vp.1, certs ++ [((keys.getD vp.1 ([], [])).1, σ)]), (vp.2, e')), s'))
          hedg.1
        rw [fst_getD_splice front back x vp.1]
        simpa only [pmf_norm, PMF.map] using h1
      · supp_cases hst' [localCertifyStep] with ⟨⟨σ, e', a'⟩, hm, rfl⟩
        exact ⟨hvp.1, hvp.2.1 _ hroot_v, fun ent he => (hvp.2.2.2.1 ent he).2,
          hvp.2.2.2.2.1, hedg.2 σ e' a' hm⟩
  exact ⟨hmain.1, fun c v e a hm => hmain.2 (c, (v, e, a)) hm⟩

private theorem localTreeHandler_planted_step (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n sigCap : ℕ} (hcap : 2 ≤ S.capacity n)
    {front back : List (List Bool × List Bool)} {x : List Bool × List Bool}
    (req : Unit × List Bool) (st : PresampledState)
    (hinv : slotEdgeInv (front ++ x :: back).length st.1) :
    let keys := front ++ x :: back
    let keys' := front ++ (x.1, []) :: back
    let rep : PresampledState → PlantedState × List (ℕ × List Bool) :=
      fun ((v, e, a), log) => (((v, e), log), signedLogOf front.length a)
    ((localTreeHandler S depth keys sigCap n req st).map fun (ans, st') => (ans, rep st')) =
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (plantedTreeHandler S depth keys' front.length sigCap n req
          ((st.1.1, st.1.2.1), st.2))).run (signedLogOf front.length st.1.2.2)).map
        fun ((ans, ps'), sg') => (ans, ps', sg')) ∧
    ∀ ans st', (ans, st') ∈ (localTreeHandler S depth keys sigCap n req st).support →
      slotEdgeInv keys.length st'.1 := by
  obtain ⟨⟨visited, edges, allSigned⟩, queried, seen, bad⟩ := st
  set keys := front ++ x :: back
  set keys' := front ++ (x.1, []) :: back
  have hslotLt : front.length < keys.length := by simp [keys]
  let hOra := OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
    (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s))
  let plantedBody : TreeBody ((NodeSlotCache × EdgeSigCache) × List (ℕ × List Bool)) :=
    fun leaf msg ((v, e), sg) =>
      ((OracleComp.interpret hOra do
        let ((node, idx, certs), (v', e')) ←
          certifyPlanted S depth keys' front.length sigCap n leaf (v, e)
        let (σ, e'') ←
          signEdgeM S keys' front.length sigCap node idx (leaf.getLastD false).toNat msg e'
        return (encodeSignature leaf certs σ, (v', e''))).run sg).map
        fun ((sig, ve'), sg') => (sig, (ve', sg'))
  have hstep := guardedTreeHandler_map depth n (localSignBody S depth keys sigCap n) plantedBody
    (fun (v, e, a) => ((v, e), signedLogOf front.length a)) (fun s => slotEdgeInv keys.length s.1)
    req ((visited, edges, allSigned), queried, seen, bad) (fun _ => hinv)
    fun _ _ leaf _ _ => by
      obtain ⟨hcert_eq, hcert_inv⟩ := localCertify_planted_spec S depth hcap leaf hinv
      dsimp only [localSignBody, plantedBody]
      have hpair := PMF.map_bind_of_invariant
        (localCertify S depth keys sigCap n leaf (visited, edges, allSigned))
        ((OracleComp.interpret hOra
          (certifyPlanted S depth keys' front.length sigCap n leaf (visited, edges))).run
          (signedLogOf front.length allSigned))
        (fun (c, (v, e, a)) => ((c, (v, e)), signedLogOf front.length a))
        (fun ((node, idx, _), (v', e', a')) =>
          (node, idx) ∈ v' ∧ slotEdgeInv keys.length (v', e', a'))
        (fun ((node, idx, certs), (v', e', a')) =>
          (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat req.2 (e', a')).map
            fun (σ, (e'', a'')) => (encodeSignature leaf certs σ, (v', e'', a'')))
        (fun (((node, idx, certs), (v', e')), sg') =>
          ((OracleComp.interpret hOra (signEdgeM S keys' front.length sigCap node idx
            (leaf.getLastD false).toNat req.2 e')).run sg').map fun ((σ, e''), sg'') =>
              (encodeSignature leaf certs σ, ((v', e''), sg'')))
        (fun (sig, v, e, a) => (sig, ((v, e), signedLogOf front.length a)))
        (fun p => slotEdgeInv keys.length p.2)
        ⟨hcert_eq, fun ⟨c, v', e', a'⟩ hm => hcert_inv c v' e' a' hm⟩
        fun ⟨⟨node, idx, certs⟩, v', e', a'⟩ _ ⟨hnode_v', hroot_v', hlt_v', huniq_v', hall_v'⟩ => by
          obtain ⟨hedg_eq, hedg_inv⟩ := localSignEdge_planted_spec S (sigCap := sigCap) hcap
            hslotLt huniq_v' hall_v' hnode_v' (Bool.toNat_le _) req.2
          refine ⟨?_, fun _ hm => ?_⟩
          · simpa only [pmf_norm, PMF.map] using congrArg
              (PMF.map fun (σ, (e'', s'')) => (encodeSignature leaf certs σ, (v', e''), s''))
              hedg_eq
          · obtain ⟨⟨σ, e'', a''⟩, hmem, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
            exact ⟨hroot_v', hlt_v', huniq_v', hedg_inv σ e'' a'' hmem⟩
      refine ⟨by simpa only [OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
        pmf_norm, PMF.map] using hpair.1, fun sig inner' hm => hpair.2 (sig, inner') hm⟩
  have hre : (guardedTreeHandler depth n plantedBody req
      (((visited, edges), signedLogOf front.length allSigned), queried, seen, bad)).map
      (fun (ans, (ve', sg'), log) => (ans, (ve', log), sg')) =
      ((OracleComp.interpret hOra (plantedTreeHandler S depth keys' front.length sigCap n req
          ((visited, edges), queried, seen, bad))).run (signedLogOf front.length allSigned)).map
        fun ((ans, ps'), sg') => (ans, ps', sg') := by
    simp only [guardedTreeHandler, plantedTreeHandler, plantedBody]
    split_ifs with hmsg hbad
    · simp only [OracleComp.run_interpret_pure, pmf_norm]
    · simp only [hOra, OracleComp.run_interpret_bind, ProbOracleComp.run_interpret_sample,
        BitString.eval_sampleList, pmf_norm]
      refine PMF.bind_congr_on_support _ _ _ fun leaf _ => ?_
      split_ifs <;> simp only [OracleComp.run_interpret_bind, OracleComp.run_interpret_pure,
        pmf_norm, PMF.map]
    · simp only [OracleComp.run_interpret_pure, pmf_norm]
  exact ⟨by simpa only [localTreeHandler, pmf_norm] using
    (congrArg (PMF.map fun (ans, (ve', sg'), log) => (ans, (ve', log), sg')) hstep.1).trans hre,
    hstep.2⟩

/-- The index of an extracted forgery is a bit, so it lies below every capacity of at least `2`. -/
private theorem extractForgery_fst_lt (d target : ℕ) (visited : NodeSlotCache)
    (msg sig : List Bool) {cap : ℕ} (hcap : 2 ≤ cap) :
    (extractForgery d target visited msg sig).1 < cap := by
  unfold extractForgery
  generalize signatureDecoder.decode sig = t
  obtain ⟨leaf, certs, last⟩ := t
  dsimp only
  split_ifs <;> exact (Bool.toNat_le _).trans_lt (by omega)

private theorem map_plantedWin_presampledExp (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n : ℕ} (hcap : 2 ≤ S.capacity n)
    (adversary : Forger) {target : ℕ} (htarget : target < dyadicSize (slotBound n)) :
    (presampledExp S depth slotBound sigCap adversary n).map (plantedWin S depth n target) =
      ProbComp.eval
        (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary target) n) := by
  set K := dyadicSize (slotBound n) with hK_def
  have hmin : min target (K - 1) = target := Nat.min_eq_left (by omega)
  have hsplit : K = target + ((K - target - 1) + 1) := by omega
  simp only [presampledExp, IndexedSignatureScheme.indexedEufCmaGame, indexedForgerAt,
    plantNodeKeys, ← hK_def, hmin]
  conv_lhs => rw [hsplit, ← ProbComp.eval_replicate_splice]
  simp only [ProbOracleComp.eval_run_interpret, interp_norm, pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun x _ =>
    PMF.bind_congr_on_support _ _ _ fun front hfront =>
    PMF.bind_congr_on_support _ _ _ fun back _ => ?_
  have hfrontLen : front.length = target := ((ProbComp.mem_support_replicate_iff _ _ _).mp hfront).1
  subst hfrontLen
  set keys := front ++ x :: back
  set keys' := front ++ (x.1, []) :: back
  set pk := encPair encUnary encBits (n, (keys.getD 0 ([], [])).1)
  have hinitInv : slotEdgeInv keys.length initPresampledState.1 :=
    ⟨List.mem_singleton.mpr rfl,
      fun e he _ => by rw [List.mem_singleton.mp he]; simp [initPresampledState],
      fun e₁ he₁ e₂ he₂ _ _ => by rw [List.mem_singleton.mp he₁, List.mem_singleton.mp he₂],
      fun _ _ _ _ h => by cases h⟩
  have hflat := ProbOracleComp.run_interpret_run_interpret
    (plantedTreeHandler S depth keys' front.length (sigCap n) n)
    (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s))
    (adversary n pk) initPlantedState []
  have hsim := ProbOracleComp.run_interpret_map_state_of_invariant
    (localTreeHandler S depth keys (sigCap n) n)
    (fun q (st : PlantedState × List (ℕ × List Bool)) =>
      ((OracleComp.interpret
        (OracleComp.sumHandler (fun j => StateT.lift (ProbComp.unifOracle j))
          (fun q s => ProbComp.eval (S.indexedSigningOracle n x.2 q s)))
        (plantedTreeHandler S depth keys' front.length (sigCap n) n q st.1)).run st.2).map
        fun ((a, b), c) => (a, b, c))
    (fun ((v, e, a), log) => (((v, e), log), signedLogOf front.length a))
    (fun st => slotEdgeInv keys.length st.1)
    (fun q st hst ans st' hm => (localTreeHandler_planted_step S depth hcap q st hst).2 ans st' hm)
    (fun q st hst => (localTreeHandler_planted_step S depth hcap q st hst).1)
    (adversary n pk) initPresampledState hinitInv
  have hpk0 : (keys'.getD 0 ([], [])).1 = (keys.getD 0 ([], [])).1 := fst_getD_splice front back x 0
  rw [hpk0]
  have hcomb := (congrArg (PMF.map fun (a, b, c) => ((a, b), c)) hsim).trans hflat.symm
  have hwin := congrArg (PMF.map fun ((msig, ps), sg) =>
    let cand := extractForgery (depth n) front.length ps.1.1 msig.1 msig.2
    decide (cand.1 < S.capacity n) && !sg.contains (cand.1, cand.2.1) &&
      S.verify x.1 cand.1 cand.2.1 cand.2.2) hcomb
  simpa only [pmf_norm, PMF.map, plantedWin, keys, List.getD_append_cons_length,
    extractForgery_fst_lt _ _ _ _ _ hcap, decide_true, Bool.true_and] using hwin

/-! #### Equivalence between `lazyTreeGame` and `presampledExp` -/

private abbrev JointKeysInner := List (List Bool × List Bool) × PresampledInner
private abbrev JointKeysState := TreeState JointKeysInner
private abbrev JointKeysCertState := List (List Bool × List Bool) × LocalCertState

private def nodesOf (usedKeys : List (List Bool × List Bool)) (visited : NodeSlotCache) :
    NodeKeyCache :=
  visited.map fun e => (e.1, usedKeys.getD e.2 ([], []))

private noncomputable def jointVisitKey (S : IndexedSignatureScheme) (n : ℕ) (path : List Bool)
    (uv : List (List Bool × List Bool) × NodeSlotCache) :
    PMF (ℕ × (List (List Bool × List Bool) × NodeSlotCache)) :=
  match uv.2.lookup path with
  | some idx => PMF.pure (idx, uv)
  | none =>
    (ProbComp.eval (S.keyGen n)).map fun child =>
      (uv.2.length, (uv.1 ++ [child], (path, uv.2.length) :: uv.2))

private noncomputable def jointKeysCertifyStep (S : IndexedSignatureScheme) (sigCap n : ℕ)
    (leaf : List Bool) (st : JointKeysCertState) : PMF JointKeysCertState := do
  let (usedKeys, ((node, idx, certs), (visited, edges, allSigned))) := st
  let bit := leaf.getD node.length false
  let childPath := node ++ [bit]
  let (childIdx, (usedKeys', visited')) ← jointVisitKey S n childPath (usedKeys, visited)
  let childPk := (usedKeys'.getD childIdx ([], [])).1
  (localSignEdge S usedKeys' sigCap node idx bit.toNat childPk (edges, allSigned)).map
    fun (σ, (edges', allSigned')) =>
      (usedKeys', ((childPath, childIdx, certs ++ [(childPk, σ)]), (visited', edges', allSigned')))

private noncomputable def jointKeysCertify (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) (leaf : List Bool) (init : JointKeysInner) : PMF JointKeysCertState :=
  Nat.iterate (fun d => d.bind (jointKeysCertifyStep S sigCap n leaf)) (depth n - 1)
    (PMF.pure (init.1, (([], 0, []), init.2)))

private noncomputable def jointKeysBody (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) : TreeBody JointKeysInner :=
  fun leaf msg st =>
    (jointKeysCertify S depth sigCap n leaf st).bind fun
      (uk', ((node, idx, certs), (vis', edg', all'))) =>
        (localSignEdge S uk' sigCap node idx (leaf.getLastD false).toNat msg (edg', all')).map
          fun (σ, (edg'', all'')) => (encodeSignature leaf certs σ, (uk', (vis', edg'', all'')))

private noncomputable def jointKeysHandler (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n : ℕ) : Unit × List Bool → StateT JointKeysState PMF (List Bool) :=
  guardedTreeHandler depth n (jointKeysBody S depth sigCap n)

private def jointKeysInv (S : IndexedSignatureScheme) (n : ℕ) (root : List Bool × List Bool)
    (st : JointKeysInner) : Prop :=
  let (usedKeys, visited, _, _) := st
  usedKeys.length = visited.length ∧
  visited.lookup [] = some 0 ∧
  usedKeys.getD 0 ([], []) = root ∧
  (∀ k ∈ usedKeys, k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
  ∀ e ∈ visited, e.2 < visited.length

private theorem nodesOf_append_singleton (usedKeys : List (List Bool × List Bool))
    (visited : NodeSlotCache) (hvis : ∀ e ∈ visited, e.2 < usedKeys.length)
    (path : List Bool) (child : List Bool × List Bool) :
    nodesOf (usedKeys ++ [child]) ((path, usedKeys.length) :: visited) =
      (path, child) :: nodesOf usedKeys visited := by
  simp only [nodesOf, List.map_cons, List.getD_append_cons_length usedKeys [] child ([], [])]
  exact congrArg _ (List.map_congr_left fun e he => by rw [List.getD_append _ _ _ _ (hvis e he)])

private theorem jointVisitKey_support_inv (S : IndexedSignatureScheme) (n : ℕ)
    {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen : uk.length = vis.length) (hpos : 0 < uk.length)
    (hvis : ∀ e ∈ vis, e.2 < vis.length) (path : List Bool)
    {idx : ℕ} {uk' : List (List Bool × List Bool)} {vis' : NodeSlotCache}
    (hm : (idx, (uk', vis')) ∈ (jointVisitKey S n path (uk, vis)).support) :
    uk'.length = vis'.length ∧ 0 < uk'.length ∧ (∀ e ∈ vis', e.2 < vis'.length) ∧
    idx < uk'.length ∧ uk.length ≤ uk'.length ∧ vis'.length ≤ vis.length + 1 ∧
    uk'.getD 0 ([], []) = uk.getD 0 ([], []) ∧
    (∀ k ∈ uk', k ∈ uk ∨ k ∈ (ProbComp.eval (S.keyGen n)).support) ∧
    (∀ j < uk.length, uk'.getD j ([], []) = uk.getD j ([], [])) ∧
    (∀ p₀ i₀, vis.lookup p₀ = some i₀ → vis'.lookup p₀ = some i₀) := by
  simp only [jointVisitKey] at hm
  cases hlk : vis.lookup path with
  | some i₀ =>
    rw [hlk] at hm; supp_cases hm
    exact ⟨hlen, hpos, hvis, hlen ▸ hvis _ (lookup_mem hlk), le_rfl, Nat.le_succ _,
      rfl, fun _ h => Or.inl h, fun _ _ => rfl, fun _ _ h => h⟩
  | none =>
    rw [hlk] at hm; supp_cases hm with ⟨child, hchild, rfl, rfl, rfl⟩
    refine ⟨by simp [hlen], by simp, fun e he => ?_, by simp [hlen], by simp, by simp,
      List.getD_append _ _ _ _ hpos, fun k hk => ?_, fun j hj => List.getD_append _ _ _ _ hj,
      fun p₀ i₀ hp₀ => by
        rw [lookup_cons_ne fun h => by subst h; rw [hp₀] at hlk; cases hlk]; exact hp₀⟩
    · rcases List.mem_cons.mp he with rfl | ht
      · simp
      · exact Nat.lt_succ_of_lt (hvis e ht)
    · rcases List.mem_append.mp hk with hk | hk
      · exact Or.inl hk
      · exact Or.inr (List.mem_singleton.mp hk ▸ hchild)

private theorem localSignEdge_notrunc (S : IndexedSignatureScheme) {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {usedKeys : List (List Bool × List Bool)}
    (hsupp : ∀ k ∈ usedKeys, k ∈ (ProbComp.eval (S.keyGen n)).support)
    {idx u : ℕ} (hidx : idx < usedKeys.length) (hu : u ≤ 1)
    {path msg : List Bool} (hmsg : TreeMsg S n msg)
    (edges : EdgeSigCache) (allSigned : AllSignedLog) :
    ((localSignEdge S usedKeys sigCap path idx u msg (edges, allSigned)).map
      fun (σ, (edges', _)) => (σ, edges')) =
      ProbComp.eval
        (memoize (fun _ => S.sign (usedKeys.getD idx ([], [])).2 u msg) (path, u) edges) := by
  simp only [localSignEdge, memoize]
  cases edges.lookup (path, u) with
  | some σ₀ => simp only [pmf_norm]
  | none =>
    simp only [bind_pure_comp, pmf_norm]
    refine PMF.map_congr_on_support _ _ _ fun raw hraw => ?_
    simp only [List.take_of_length_le
      (hsigCap _ (hsupp _ (List.getD_mem ([], []) hidx)) u hu msg hmsg raw hraw)]

private theorem jointKeysCertify_lazy_spec (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {root : List Bool × List Bool} {st : JointKeysInner}
    (hinv : jointKeysInv S n root st) (leaf : List Bool) :
    ((jointKeysCertify S depth sigCap n leaf st).map
      fun (uk', ((node, idx, certs), (vis', edg', _))) =>
        ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg'))) =
      ProbComp.eval (certifyLazy S depth n root leaf (nodesOf st.1 st.2.1, st.2.2.1)) ∧
    ∀ uk' node idx certs vis' edg' all',
      (uk', ((node, idx, certs), (vis', edg', all'))) ∈
        (jointKeysCertify S depth sigCap n leaf st).support →
      jointKeysInv S n root (uk', vis', edg', all') ∧ idx < uk'.length := by
  obtain ⟨usedKeys, visited, edges, allSigned⟩ := st
  have hpos0 : 0 < usedKeys.length := by
    have h1 := hinv.1; have := hinv.2.2.2.2 _ (lookup_mem hinv.2.1); omega
  dsimp only [jointKeysCertify, certifyLazy]
  rw [ProbComp.eval_iterate]
  have hmain := PMF.map_iterate_bind_of_invariant
    (jointKeysCertifyStep S sigCap n leaf) (fun s => ProbComp.eval (certifyStepLazy S n leaf s))
    (fun (uk', ((node, idx, certs), (vis', edg', _))) =>
      ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg')))
    (fun _ (uk, ((_, idx, _), p)) => jointKeysInv S n root (uk, p) ∧ idx < uk.length)
    (depth n - 1) (usedKeys, (([], 0, []), (visited, edges, allSigned))) ⟨hinv, hpos0⟩
    fun _ _ ⟨uk, ⟨node, idx, certs⟩, vis, edg, all⟩
        ⟨⟨hlen, hrv, hrk, hsupp, hvis⟩, hidx⟩ => by
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      have hpos : 0 < uk.length := Nat.lt_of_le_of_lt (Nat.zero_le _) hidx
      have hvis_eq : ((jointVisitKey S n childPath (uk, vis)).map
          fun (i, (uk', vis')) => (uk'.getD i ([], []), nodesOf uk' vis')) =
          ProbComp.eval (memoize (fun _ => S.keyGen n) childPath (nodesOf uk vis)) := by
        simp only [jointVisitKey, memoize]
        have hlkM : (nodesOf uk vis).lookup childPath =
            (vis.lookup childPath).map (fun i => uk.getD i ([], [])) :=
          List.lookup_map_snd vis (fun i => uk.getD i ([], [])) childPath
        cases hlk : vis.lookup childPath with
        | some i => rw [hlk, Option.map_some] at hlkM; simp only [hlkM, pmf_norm]
        | none =>
          rw [hlk, Option.map_none] at hlkM
          simp only [hlkM, bind_pure_comp, pmf_norm]
          refine PMF.map_congr_on_support _ _ _ fun child _ => by
            simp only [← hlen, List.getD_append_cons_length uk [] child ([], []),
              nodesOf_append_singleton uk vis (fun e he => hlen ▸ hvis e he) childPath child]
      dsimp only [jointKeysCertifyStep, certifyStepLazy]
      have hstep := PMF.map_bind_of_invariant (jointVisitKey S n childPath (uk, vis))
        (ProbComp.eval (memoize (fun _ => S.keyGen n) childPath (nodesOf uk vis)))
        (fun (i, (uk', vis')) => (uk'.getD i ([], []), nodesOf uk' vis'))
        (fun (cIdx, (uk', vis')) =>
          jointKeysInv S n root (uk', vis', edg, all) ∧ cIdx < uk'.length ∧
          uk'.getD idx ([], []) = uk.getD idx ([], []) ∧ idx < uk'.length)
        (fun (cIdx, (uk', vis')) =>
          let childPk := (uk'.getD cIdx ([], [])).1
          (localSignEdge S uk' sigCap node idx bit.toNat childPk (edg, all)).map
            fun (σ, (edg', all')) => (uk', ((childPath, cIdx, certs ++ [(childPk, σ)]),
              (vis', edg', all'))))
        (fun (child, ns') =>
          (ProbComp.eval (memoize (fun _ => S.sign (uk.getD idx ([], [])).2 bit.toNat child.1)
            (node, bit.toNat) edg)).bind fun (σ, edg') =>
              PMF.pure ((childPath, child, certs ++ [(child.1, σ)]), (ns', edg')))
        (fun (uk', ((node, idx, certs), (vis', edg', _))) =>
          ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg')))
        (fun (uk', ((_, idx', _), p)) => jointKeysInv S n root (uk', p) ∧ idx' < uk'.length)
        ⟨hvis_eq, fun ⟨cIdx, uk', vis'⟩ hm => by
          obtain ⟨hlen', _, hvis', hcLt, hle, _, h0, h4, hkeep, hlk0⟩ :=
            jointVisitKey_support_inv S n hlen hpos hvis childPath hm
          exact ⟨⟨hlen', hlk0 [] 0 hrv, h0.trans hrk,
            fun k hk => (h4 k hk).elim (hsupp k) id, hvis'⟩,
            hcLt, hkeep idx hidx, hidx.trans_le hle⟩⟩
        fun ⟨cIdx, uk', vis'⟩ _ ⟨hinv', hcLt, hidx_eq, hidx'⟩ => by
          have hse := localSignEdge_notrunc S hsigCap hinv'.2.2.2.1 hidx'
            (Bool.toNat_le bit) (path := node)
            (Or.inr ⟨_, hinv'.2.2.2.1 _ (List.getD_mem ([], []) hcLt), rfl⟩) edg all
          rw [hidx_eq] at hse
          refine ⟨?_, fun out hm => ?_⟩
          · simpa only [pmf_norm, PMF.map] using congrArg
              (PMF.map fun (σ, edg') => ((childPath, uk'.getD cIdx ([], []),
                certs ++ [((uk'.getD cIdx ([], [])).1, σ)]), nodesOf uk' vis', edg')) hse
          · obtain ⟨⟨_, _, _⟩, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
            exact ⟨hinv', hcLt⟩
      exact ⟨by simpa only [pmf_norm, PMF.map] using hstep.1, hstep.2⟩
  refine ⟨by simpa only [hinv.2.2.1] using hmain.1, fun uk' node idx certs vis' edg' all' hm =>
    hmain.2 (uk', ((node, idx, certs), (vis', edg', all'))) hm⟩

private theorem jointKeysHandler_lazy_step (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {sigCap n : ℕ}
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap)
    {root : List Bool × List Bool} (req : Unit × List Bool) (st : JointKeysState)
    (hinv : jointKeysInv S n root st.1) :
    ((jointKeysHandler S depth sigCap n req st).map fun (ans, st') =>
      (ans, (nodesOf st'.1.1 st'.1.2.1, st'.1.2.2.1), st'.2)) =
      ProbComp.eval (lazySignHandler S depth n root req
        ((nodesOf st.1.1 st.1.2.1, st.1.2.2.1), st.2)) ∧
    ∀ ans st', (ans, st') ∈ (jointKeysHandler S depth sigCap n req st).support →
      jointKeysInv S n root st'.1 := by
  rw [eval_lazySignHandler_eq]
  refine guardedTreeHandler_map depth n (jointKeysBody S depth sigCap n)
    (lazySignBody S depth n root) (fun (uk, vis, edg, _) => (nodesOf uk vis, edg))
    (fun s => jointKeysInv S n root s.1) req st (fun _ => hinv) fun hmsg _ leaf _ _ => ?_
  obtain ⟨hcert_eq, hcert_inv⟩ := jointKeysCertify_lazy_spec S depth hsigCap hinv leaf
  dsimp only [jointKeysBody, lazySignBody]
  refine (fun h => ⟨h.1, fun sig inner' hm => h.2 (sig, inner') hm⟩)
    (PMF.map_bind_of_invariant (jointKeysCertify S depth sigCap n leaf st.1)
      (ProbComp.eval (certifyLazy S depth n root leaf (nodesOf st.1.1 st.1.2.1, st.1.2.2.1)))
      (fun (uk', ((node, idx, certs), (vis', edg', _))) =>
        ((node, uk'.getD idx ([], []), certs), (nodesOf uk' vis', edg')))
      (fun (uk', (_, idx, _), p) => jointKeysInv S n root (uk', p) ∧ idx < uk'.length)
      (fun (uk', ((node, idx, certs), (vis', edg', all'))) =>
        (localSignEdge S uk' sigCap node idx (leaf.getLastD false).toNat req.2 (edg', all')).map
          fun (σ, (edg'', all'')) => (encodeSignature leaf certs σ, (uk', (vis', edg'', all''))))
      (fun ((node, (_, sk), certs), (ns', edg')) =>
        (ProbComp.eval (memoize (fun _ => S.sign sk (leaf.getLastD false).toNat req.2)
          (node, (leaf.getLastD false).toNat) edg')).map fun (σ, edg'') =>
            (encodeSignature leaf certs σ, (ns', edg'')))
      (fun (sig, uk', vis', edg', _) => (sig, nodesOf uk' vis', edg'))
      (fun (x : List Bool × JointKeysInner) => jointKeysInv S n root x.2)
      ⟨hcert_eq, fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ hm =>
        hcert_inv uk' node idx certs vis' edg' all' hm⟩
      fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ _ ⟨hi', hidx'⟩ => by
        have hse := localSignEdge_notrunc S hsigCap hi'.2.2.2.1 hidx'
          (Bool.toNat_le (leaf.getLastD false)) (path := node) (Or.inl hmsg) edg' all'
        refine ⟨?_, fun _ hm => ?_⟩
        · simpa only [pmf_norm, PMF.map] using congrArg
            (PMF.map fun (σ, edg'') => (encodeSignature leaf certs σ, nodesOf uk' vis', edg'')) hse
        · obtain ⟨⟨_, _, _⟩, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm; exact hi')

private noncomputable def expandKeys (S : IndexedSignatureScheme) (n K : ℕ)
    (uk : List (List Bool × List Bool)) : PMF (List (List Bool × List Bool)) :=
  (ProbComp.eval (OracleComp.replicate (K - uk.length) (S.keyGen n))).map (uk ++ ·)

private theorem jointVisitKey_expandKeys (S : IndexedSignatureScheme) (n K : ℕ)
    {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen : uk.length = vis.length) (hlt : vis.length < K) (path : List Bool) :
    ((jointVisitKey S n path (uk, vis)).bind fun (idx, (uk', vis')) =>
      (expandKeys S n K uk').map fun keys => (keys, idx, vis')) =
      (expandKeys S n K uk).map fun keys =>
        let (idx, vis') := visitNodePure keys.length path vis
        (keys, idx, vis') := by
  simp only [jointVisitKey, visitNodePure]
  cases vis.lookup path with
  | some idx => simp only [pmf_norm]
  | none =>
    set m := K - uk.length - 1
    have hsub : K - uk.length = m + 1 := by omega
    simp only [expandKeys, hsub, OracleComp.replicate_succ, pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun child _ => ?_
    rw [show K - (uk ++ [child]).length = m by simp; omega]
    refine PMF.map_congr_on_support _ _ _ fun rem hrem => ?_
    have hremLen := ((ProbComp.mem_support_replicate_iff _ _ _).mp hrem).1
    have hmin : min vis.length (uk ++ child :: rem).length = vis.length :=
      Nat.min_eq_left (by simp [hremLen]; omega)
    simp only [List.append_assoc, List.singleton_append, hmin]

private theorem localSignEdge_expandKeys (S : IndexedSignatureScheme) (n K sigCap : ℕ)
    {uk : List (List Bool × List Bool)} {idx : ℕ} (hidx : idx < uk.length)
    (path : List Bool) (u : ℕ) (msg : List Bool) (ea : EdgeSigCache × AllSignedLog) :
    ((localSignEdge S uk sigCap path idx u msg ea).bind fun out =>
      (expandKeys S n K uk).map fun keys => (keys, out)) =
      (expandKeys S n K uk).bind fun keys =>
        (localSignEdge S keys sigCap path idx u msg ea).map fun out => (keys, out) := by
  have hcomm : ((localSignEdge S uk sigCap path idx u msg ea).bind fun out =>
      (expandKeys S n K uk).map fun keys => (keys, out)) =
      (expandKeys S n K uk).bind fun keys =>
        (localSignEdge S uk sigCap path idx u msg ea).map fun out => (keys, out) := by
    simp only [PMF.map]; exact PMF.bind_comm _ _ _
  rw [hcomm]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  supp_cases hkeys [expandKeys] with ⟨rem, -, rfl⟩
  simp only [localSignEdge, List.getD_append _ _ _ _ hidx]

private theorem jointKeysCertify_expandKeys (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n K : ℕ) {uk : List (List Bool × List Bool)} {vis : NodeSlotCache}
    (hlen0 : uk.length = vis.length) (hpos0 : 0 < uk.length)
    (hvis0 : ∀ e ∈ vis, e.2 < vis.length) (hbound : vis.length + (depth n - 1) ≤ K)
    (leaf : List Bool) (edg : EdgeSigCache) (all : AllSignedLog) :
    ((jointKeysCertify S depth sigCap n leaf (uk, vis, edg, all)).bind
      fun (uk', cs) => (expandKeys S n K uk').map fun keys => (keys, cs)) =
      (expandKeys S n K uk).bind (fun keys =>
        (localCertify S depth keys sigCap n leaf (vis, edg, all)).map fun cs => (keys, cs)) ∧
    ∀ uk' cs, (uk', cs) ∈ (jointKeysCertify S depth sigCap n leaf (uk, vis, edg, all)).support →
      uk'.length = cs.2.1.length ∧ 0 < uk'.length ∧
      (∀ e ∈ cs.2.1, e.2 < cs.2.1.length) ∧
      cs.1.2.1 < uk'.length ∧ cs.2.1.length ≤ vis.length + (depth n - 1) := by
  dsimp only [jointKeysCertify, localCertify]
  let inv (m : ℕ) (st : JointKeysCertState) : Prop :=
    st.1.length = st.2.2.1.length ∧ 0 < st.1.length ∧
    (∀ e ∈ st.2.2.1, e.2 < st.2.2.1.length) ∧
    st.2.1.2.1 < st.1.length ∧ st.2.2.1.length ≤ vis.length + m
  have hmain := PMF.iterate_bind_comm_of_invariant (jointKeysCertifyStep S sigCap n leaf)
    (fun keys => localCertifyStep S keys sigCap leaf) (fun st => expandKeys S n K st.1) Prod.snd
    inv (depth n - 1) (uk, (([], 0, []), (vis, edg, all)))
    ⟨hlen0, hpos0, hvis0, hpos0, Nat.le_add_right _ _⟩
    fun m hm ⟨uk_m, ⟨node, idx, certs⟩, vis_m, edg_m, all_m⟩
        ⟨hlen_m, hpos_m, hvis_m, hidx_m, hgrow_m⟩ => by
      dsimp only at hlen_m hpos_m hvis_m hidx_m hgrow_m
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      simp only [jointKeysCertifyStep, localCertifyStep, pmf_norm]
      have hstep := PMF.bind_bind_comm_of_invariant (jointVisitKey S n childPath (uk_m, vis_m))
        (fun x => expandKeys S n K x.2.1) (fun x => (x.1, x.2.2))
        (fun keys => PMF.pure (visitNodePure keys.length childPath vis_m))
        (fun x => x.2.1.length = x.2.2.length ∧ 0 < x.2.1.length ∧
          (∀ e ∈ x.2.2, e.2 < x.2.2.length) ∧ x.1 < x.2.1.length ∧
          uk_m.length ≤ x.2.1.length ∧ x.2.2.length ≤ vis_m.length + 1)
        (expandKeys S n K uk_m)
        (fun (cIdx, (uk', vis')) =>
          let childPk := (uk'.getD cIdx ([], [])).1
          (localSignEdge S uk' sigCap node idx bit.toNat childPk (edg_m, all_m)).map
            fun (σ, (edg', all')) =>
              (uk', ((childPath, cIdx, certs ++ [(childPk, σ)]), (vis', edg', all'))))
        (fun x => expandKeys S n K x.1) Prod.snd
        (fun keys (cIdx, vis') =>
          let childPk := (keys.getD cIdx ([], [])).1
          (localSignEdge S keys sigCap node idx bit.toNat childPk (edg_m, all_m)).map
            fun (σ, edg', all') => ((childPath, cIdx, certs ++ [(childPk, σ)]), vis', edg', all'))
        (inv (m + 1))
        ⟨by simpa only [PMF.map, pmf_norm] using
          jointVisitKey_expandKeys S n K hlen_m (by omega) childPath,
          fun ⟨cIdx, uk', vis'⟩ hm_vk => by
            obtain ⟨hl, hp, hv, hc, hle, hg, -⟩ :=
              jointVisitKey_support_inv S n hlen_m hpos_m hvis_m childPath hm_vk
            exact ⟨hl, hp, hv, hc, hle, hg⟩⟩
        fun ⟨cIdx, uk', vis'⟩ _ ⟨hl1, hp1, hv1, hcLt, hleU, hg1⟩ => by
          refine ⟨?_, fun ⟨_, _⟩ hm_se => ?_⟩
          · have hse' := congrArg (PMF.map fun (keys, σ, edg', all') =>
              (keys, ((childPath, cIdx, certs ++ [((uk'.getD cIdx ([], [])).1, σ)]),
                vis', edg', all')))
              (localSignEdge_expandKeys S n K sigCap (hidx_m.trans_le hleU) node bit.toNat
                (uk'.getD cIdx ([], [])).1 (edg_m, all_m))
            simp only [pmf_norm] at hse' ⊢
            rw [hse']
            refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
            supp_cases hkeys [expandKeys] with ⟨rem, -, rfl⟩
            rw [List.getD_append _ _ _ _ hcLt]
          · obtain ⟨⟨_, _, _⟩, -, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp hm_se
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq.symm
            exact ⟨hl1, hp1, hv1, hcLt, hg1.trans (Nat.add_le_add_right hgrow_m 1)⟩
      exact ⟨by simpa only [pmf_norm] using hstep.1, hstep.2⟩
  exact ⟨hmain.1, fun uk' cs hm => hmain.2 (uk', cs) hm⟩

private def jointExpandInv (K budget : ℕ) (st : JointKeysInner) : Prop :=
  st.1.length = st.2.1.length ∧ 0 < st.1.length ∧
  (∀ e ∈ st.2.1, e.2 < st.2.1.length) ∧ st.2.1.length + budget ≤ K

private theorem jointKeysHandler_expandKeys (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (sigCap n K : ℕ) (req : Unit × List Bool) (st : JointKeysState)
    (hinv : jointExpandInv K (depth n - 1) st.1) :
    ((jointKeysHandler S depth sigCap n req st).bind fun (ans, st') =>
      (expandKeys S n K st'.1.1).map fun keys => (keys, ans, (st'.1.2, st'.2))) =
      (expandKeys S n K st.1.1).bind (fun keys =>
        (localTreeHandler S depth keys sigCap n req (st.1.2, st.2)).map fun (ans, ps') =>
          (keys, ans, ps')) ∧
    ∀ ans st', (ans, st') ∈ (jointKeysHandler S depth sigCap n req st).support →
      st'.1.1.length = st'.1.2.1.length ∧ 0 < st'.1.1.length ∧
      (∀ e ∈ st'.1.2.1, e.2 < st'.1.2.1.length) ∧
      st'.1.2.1.length ≤ st.1.2.1.length + (depth n - 1) := by
  obtain ⟨⟨uk, vis, edg, allSigned⟩, log⟩ := st
  obtain ⟨hlen, hpos, hvis, hbound⟩ := hinv
  refine guardedTreeHandler_bind_comm depth n (jointKeysBody S depth sigCap n)
    (fun keys => localSignBody S depth keys sigCap n) (fun x => expandKeys S n K x.1) Prod.snd
    (fun s => s.1.1.length = s.1.2.1.length ∧ 0 < s.1.1.length ∧
      (∀ e ∈ s.1.2.1, e.2 < s.1.2.1.length) ∧ s.1.2.1.length ≤ vis.length + (depth n - 1))
    req ((uk, vis, edg, allSigned), log)
    (fun _ => ⟨hlen, hpos, hvis, Nat.le_add_right _ _⟩)
    fun _ _ leaf _ _ => by
      have hcert := jointKeysCertify_expandKeys S depth sigCap n K hlen hpos hvis hbound leaf edg
        allSigned
      dsimp only [jointKeysBody, localSignBody]
      have hpair := PMF.bind_bind_comm_of_invariant
        (jointKeysCertify S depth sigCap n leaf (uk, vis, edg, allSigned))
        (fun x => expandKeys S n K x.1) Prod.snd
        (fun keys => localCertify S depth keys sigCap n leaf (vis, edg, allSigned))
        (fun (uk', cs') => uk'.length = cs'.2.1.length ∧ 0 < uk'.length ∧
          (∀ e ∈ cs'.2.1, e.2 < cs'.2.1.length) ∧ cs'.1.2.1 < uk'.length ∧
          cs'.2.1.length ≤ vis.length + (depth n - 1))
        (expandKeys S n K uk)
        (fun (uk', ((node, idx, certs), (vis', edg', all'))) =>
          (localSignEdge S uk' sigCap node idx (leaf.getLastD false).toNat req.2
            (edg', all')).map fun (σ, (edg'', all'')) =>
              (encodeSignature leaf certs σ, (uk', (vis', edg'', all''))))
        (fun x => expandKeys S n K x.2.1) (fun x => (x.1, x.2.2))
        (fun keys ((node, idx, certs), (vis', edg', all')) =>
          (localSignEdge S keys sigCap node idx (leaf.getLastD false).toNat req.2
            (edg', all')).map fun (σ, (edg'', all'')) =>
              (encodeSignature leaf certs σ, (vis', edg'', all'')))
        (fun (_, uk', vis', _, _) => uk'.length = vis'.length ∧ 0 < uk'.length ∧
          (∀ e ∈ vis', e.2 < vis'.length) ∧ vis'.length ≤ vis.length + (depth n - 1))
        ⟨hcert.1, fun ⟨uk', cs'⟩ hm => hcert.2 uk' cs' hm⟩
        fun ⟨uk', ⟨node, idx, certs⟩, vis', edg', all'⟩ _ ⟨hl1, hp1, hv1, hidx', hg1⟩ => by
          refine ⟨?_, fun x hm => ?_⟩
          · simpa only [pmf_norm] using congrArg (PMF.map fun (keys, σ, edg'', all'') =>
              (keys, encodeSignature leaf certs σ, vis', edg'', all''))
              (localSignEdge_expandKeys S n K sigCap hidx' node (leaf.getLastD false).toNat req.2
                (edg', all'))
          · obtain ⟨⟨_, _, _⟩, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
            exact ⟨hl1, hp1, hv1, hg1⟩
      exact ⟨by simpa only [pmf_norm] using hpair.1, fun sig inner' hm => hpair.2 (sig, inner') hm⟩

private theorem eval_lazyTreeGame_eq_presampled (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n Q : ℕ} (hdepth_pos : 1 ≤ depth n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      TreeMsg S n msg → ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    ProbComp.eval (lazyTreeGame S depth adversary n) =
      (presampledExp S depth slotBound sigCap adversary n).map
        (treeWinOfPresampled S depth n) := by
  set K := dyadicSize (slotBound n) with hK_def
  have hK2 : 2 ≤ K := two_le_dyadicSize (slotBound n)
  have hslotLt : 1 + Q * (depth n - 1) < K := slot_bound_lt_dyadicSize hdepth_pos hslot
  have hrep : ProbComp.eval (OracleComp.replicate K (S.keyGen n)) =
      (ProbComp.eval (S.keyGen n)).bind fun root => expandKeys S n K [root] := by
    have hKeq : K = (K - 1) + 1 := by omega
    conv_lhs => rw [hKeq, OracleComp.replicate_succ]
    simp only [expandKeys, List.length_singleton, List.singleton_append, pmf_norm]
  simp only [lazyTreeGame, presampledExp, ← hK_def, ProbOracleComp.eval_run_interpret, hrep,
    pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun root hroot => ?_
  set pk := encPair encUnary encBits (n, root.1)
  set initJ : JointKeysState := (([root], initPresampledState.1), initPresampledState.2)
  have hjInv : jointKeysInv S n root initJ.1 :=
    ⟨rfl, rfl, rfl, fun k hk => List.mem_singleton.mp hk ▸ hroot,
      fun e he => by rw [List.mem_singleton.mp he]; simp [initPresampledState]⟩
  have hproj := ProbOracleComp.run_interpret_map_state_of_invariant
    (jointKeysHandler S depth (sigCap n) n)
    (fun q s => ProbComp.eval (lazySignHandler S depth n root q s))
    (fun s => ((nodesOf s.1.1 s.1.2.1, s.1.2.2.1), s.2))
    (fun s => jointKeysInv S n root s.1)
    (fun q s hs a s' hm => (jointKeysHandler_lazy_step S depth hsigCap q s hs).2 a s' hm)
    (fun q s hs => (jointKeysHandler_lazy_step S depth hsigCap q s hs).1)
    (adversary n pk) initJ hjInv
  have hexpRun := (ProbOracleComp.IsQueryBounded.run_interpret_bind_comm_of_invariant
    (jointKeysHandler S depth (sigCap n) n)
    (fun keys => localTreeHandler S depth keys (sigCap n) n)
    (fun st => expandKeys S n K st.1.1) (fun st => (st.1.2, st.2))
    (fun rem st => jointExpandInv K (rem * (depth n - 1)) st.1)
    (fun r s ⟨h1, h2, h3, h4⟩ =>
      ⟨h1, h2, h3, le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ r)) _) h4⟩)
    (fun r req s ⟨h1, h2, h3, h4⟩ => by
      have hmul : (r + 1) * (depth n - 1) = r * (depth n - 1) + (depth n - 1) :=
        Nat.succ_mul r (depth n - 1)
      obtain ⟨heq, hsupp⟩ :=
        jointKeysHandler_expandKeys S depth (sigCap n) n K req s ⟨h1, h2, h3, by omega⟩
      exact ⟨heq, fun ans s' hm => by
        obtain ⟨hl, hp, hv, hg⟩ := hsupp ans s' hm; exact ⟨hl, hp, hv, by omega⟩⟩)
    (hq root hroot) (s := initJ)
    ⟨rfl, Nat.zero_lt_one,
      fun e he => by rw [List.mem_singleton.mp he]; simp [initJ, initPresampledState],
      by simpa [initJ, initPresampledState] using hslotLt.le⟩).1
  have hlhs : ((OracleComp.interpret
      (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
        (fun q s => ProbComp.eval (lazySignHandler S depth n root q s)))
      (adversary n pk)).run (([([], root)], []), ([], [], false))).bind
        (fun (msig, (_, queried, _, _)) => PMF.pure
          ((msig.1.length == n) && !queried.contains msig.1 &&
            verify S depth pk msig.1 msig.2)) =
      (((OracleComp.interpret
        (OracleComp.sumHandler (fun k => StateT.lift (ProbComp.unifOracle k))
          (jointKeysHandler S depth (sigCap n) n))
        (adversary n pk)).run initJ).bind fun (msig, s') =>
          (expandKeys S n K s'.1.1).map fun keys => (keys, msig, (s'.1.2, s'.2))).map
        (treeWinOfPresampled S depth n) := by
    rw [show (([([], root)], []), ([], [], false)) =
      ((nodesOf initJ.1.1 initJ.1.2.1, initJ.1.2.2.1), initJ.2) from rfl, ← hproj]
    simp only [pmf_norm]
    refine PMF.bind_congr_on_support _ _ _ fun ⟨msig, st'⟩ hm_run => ?_
    have hjInv' := ProbOracleComp.run_interpret_invariant
      (jointKeysHandler S depth (sigCap n) n) (fun s => jointKeysInv S n root s.1)
      (fun q s hs a s' hm => (jointKeysHandler_lazy_step S depth hsigCap q s hs).2 a s' hm)
      (adversary n pk) initJ hjInv msig st' hm_run
    have hpos' : 0 < st'.1.1.length := hjInv'.1 ▸ hjInv'.2.2.2.2 ([], 0) (lookup_mem hjInv'.2.1)
    symm
    rw [← PMF.map_const (expandKeys S n K st'.1.1)]
    refine PMF.map_congr_on_support _ _ _ fun keys hkeys => ?_
    supp_cases hkeys [expandKeys] with ⟨rem, -, rfl⟩
    simp only [treeWinOfPresampled, List.getD_append _ _ _ _ hpos', hjInv'.2.2.1, pk]; rfl
  have hexpWin := congrArg (PMF.map (treeWinOfPresampled S depth n)) hexpRun
  rw [hlhs, hexpWin]
  simp only [pmf_norm]
  refine PMF.bind_congr_on_support _ _ _ fun keys hkeys => ?_
  supp_cases hkeys [expandKeys] with ⟨rem, -, rfl⟩; rfl

/-! #### Query-bounded invariant on `presampledExp` and forgery extraction -/

private def allSignedInv (d : ℕ) (keys : List (List Bool × List Bool))
    (visited : NodeSlotCache) (queried : List (List Bool)) (allSigned : AllSignedLog) : Prop :=
  ∀ p idx u m, (p, idx, u, m) ∈ allSigned →
    (p, idx) ∈ visited ∧
    ((p.length + 1 < d ∧ ∃ (b : Bool) (childIdx : ℕ),
        b.toNat = u ∧ (p ++ [b], childIdx) ∈ visited ∧ m = (keys.getD childIdx ([], [])).1) ∨
      (p.length + 1 = d ∧ m ∈ queried))

private theorem allSignedInv_mono {d : ℕ} {keys : List (List Bool × List Bool)}
    {v₁ v₂ : NodeSlotCache} {q₁ q₂ : List (List Bool)} {a : AllSignedLog}
    (hv : ∀ e ∈ v₁, e ∈ v₂) (hq : ∀ m ∈ q₁, m ∈ q₂) (h : allSignedInv d keys v₁ q₁ a) :
    allSignedInv d keys v₂ q₂ a := fun p idx u m hm =>
  let ⟨hp, hd⟩ := h p idx u m hm
  ⟨hv _ hp, hd.imp (fun ⟨hl, b, c, hb, hc, hm⟩ => ⟨hl, b, c, hb, hv _ hc, hm⟩)
    (fun ⟨hl, hm⟩ => ⟨hl, hq _ hm⟩)⟩

private theorem allSignedInv_localSignEdge {S : IndexedSignatureScheme}
    {d : ℕ} {keys : List (List Bool × List Bool)} {sigCap : ℕ}
    {node msg : List Bool} {idx u : ℕ} {e : EdgeSigCache} {a : AllSignedLog}
    {v : NodeSlotCache} {q : List (List Bool)} {σ : List Bool} {e' : EdgeSigCache}
    {a' : AllSignedLog}
    (hm : (σ, (e', a')) ∈ (localSignEdge S keys sigCap node idx u msg (e, a)).support)
    (hinv : allSignedInv d keys v q a)
    (hnew : (node, idx) ∈ v ∧
      ((node.length + 1 < d ∧ ∃ (b : Bool) (childIdx : ℕ), b.toNat = u ∧
          (node ++ [b], childIdx) ∈ v ∧ msg = (keys.getD childIdx ([], [])).1) ∨
        (node.length + 1 = d ∧ msg ∈ q))) :
    allSignedInv d keys v q a' := by
  rcases mem_support_localSignEdge hm with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact hinv
  · intro p i₀ u' m hm'
    rcases List.mem_cons.mp hm' with hhead | ht
    · obtain ⟨rfl, h2⟩ := Prod.mk.inj hhead
      obtain ⟨rfl, h3⟩ := Prod.mk.inj h2
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj h3
      exact hnew
    · exact hinv p i₀ u' m ht

private def presampledBoundedInv (d : ℕ) (keys : List (List Bool × List Bool)) (rem : ℕ)
    (st : PresampledState) : Prop :=
  let ((visited, _, allSigned), (queried, _, _)) := st
  ([], 0) ∈ visited ∧
  visited.length + rem * (d - 1) ≤ keys.length ∧
  (∀ e ∈ visited, e.1.length < d ∧ e.2 < visited.length) ∧
  (∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂) ∧
  allSignedInv d keys visited queried allSigned

private theorem localCertify_bounded_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (hd : 1 ≤ depth n)
    (leaf : List Bool) {visited : NodeSlotCache} {edges : EdgeSigCache}
    {queried : List (List Bool)} {allSigned : AllSignedLog}
    (hroot : ([], 0) ∈ visited) (hbound : visited.length + (depth n - 1) ≤ keys.length)
    (hvis : ∀ e ∈ visited, e.1.length < depth n ∧ e.2 < visited.length)
    (huniq : ∀ e₁ ∈ visited, ∀ e₂ ∈ visited, e₁.2 = e₂.2 → e₁ = e₂)
    (hall : allSignedInv (depth n) keys visited queried allSigned) :
    ∀ node idx certs v' e' a',
      ((node, idx, certs), (v', e', a')) ∈
        (localCertify S depth keys sigCap n leaf (visited, edges, allSigned)).support →
      node.length + 1 = depth n ∧ (node, idx) ∈ v' ∧ ([], 0) ∈ v' ∧
      v'.length ≤ visited.length + (depth n - 1) ∧
      (∀ e ∈ v', e.1.length < depth n ∧ e.2 < v'.length) ∧
      (∀ e₁ ∈ v', ∀ e₂ ∈ v', e₁.2 = e₂.2 → e₁ = e₂) ∧
      allSignedInv (depth n) keys v' queried a' := by
  let inv (k : ℕ) (cs : LocalCertState) : Prop :=
    cs.1.1.length = k ∧ (cs.1.1, cs.1.2.1) ∈ cs.2.1 ∧ ([], 0) ∈ cs.2.1 ∧
    cs.2.1.length ≤ visited.length + k ∧
    (∀ e ∈ cs.2.1, e.1.length < depth n ∧ e.2 < cs.2.1.length) ∧
    (∀ e₁ ∈ cs.2.1, ∀ e₂ ∈ cs.2.1, e₁.2 = e₂.2 → e₁ = e₂) ∧
    allSignedInv (depth n) keys cs.2.1 queried cs.2.2.2
  have hmain := PMF.iterate_bind_invariant (localCertifyStep S keys sigCap leaf) inv (depth n - 1)
    (([], 0, []), (visited, edges, allSigned))
    ⟨rfl, hroot, hroot, Nat.le_add_right _ _, hvis, huniq, hall⟩
    fun k hk ⟨⟨node, idx, certs⟩, v, e, a⟩
        ⟨hnLen, hnode_v, hroot_v, hgrow_v, hvis_v, huniq_v, hall_v⟩ cs' hm_step => by
      dsimp only at hnLen hnode_v hroot_v hgrow_v hvis_v huniq_v hall_v
      have hvLt : v.length < keys.length := by omega
      have hkLt : k + 1 < depth n := by omega
      set bit := leaf.getD node.length false
      set childPath := node ++ [bit]
      have hcLen : childPath.length = k + 1 := by simp [childPath, hnLen]
      supp_cases hm_step [localCertifyStep] with ⟨⟨σ, e', a'⟩, hm_se, rfl⟩
      have hvp := visitNodePure_inv (P := fun p => p.length < depth n) (K := keys.length)
        childPath (hcLen ▸ hkLt) (fun ent he => ⟨(hvis_v ent he).1, fun _ => (hvis_v ent he).2⟩)
        (fun e₁ he₁ e₂ he₂ _ heq => huniq_v e₁ he₁ e₂ he₂ heq)
      set vp := visitNodePure keys.length childPath v
      have hltK : ∀ ent ∈ vp.2, ent.2 < keys.length := fun ent he =>
        (hvp.2.2.2.2.2 ent he).elim (fun h => (hvis_v ent h).2.trans hvLt)
          (fun h => h ▸ (Nat.min_le_left _ _).trans_lt hvLt)
      have hlift : allSignedInv (depth n) keys vp.2 queried a :=
        allSignedInv_mono hvp.2.1 (fun _ h => h) hall_v
      refine ⟨hcLen, hvp.1, hvp.2.1 _ hroot_v, hvp.2.2.1.trans (Nat.add_le_add_right hgrow_v 1),
        fun ent he => ⟨(hvp.2.2.2.1 ent he).1, (hvp.2.2.2.1 ent he).2 (hltK ent he)⟩,
        fun e₁ he₁ e₂ he₂ heq => hvp.2.2.2.2.1 e₁ he₁ e₂ he₂ (hltK e₁ he₁) heq,
        allSignedInv_localSignEdge hm_se hlift ⟨hvp.2.1 _ hnode_v,
          Or.inl ⟨hnLen ▸ hkLt, bit, vp.1, rfl, hvp.1, rfl⟩⟩⟩
  intro node idx certs v' e' a' hm
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hmain _ hm
  exact ⟨by dsimp only at h1; omega, h2, h3, h4, h5, h6, h7⟩

private theorem localTreeHandler_bounded_inv (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    (keys : List (List Bool × List Bool)) (sigCap n : ℕ) (hd : 1 ≤ depth n)
    (req : Unit × List Bool) {rem : ℕ} {st : PresampledState}
    (hinv : presampledBoundedInv (depth n) keys (rem + 1) st) :
    ∀ ans st', (ans, st') ∈ (localTreeHandler S depth keys sigCap n req st).support →
      presampledBoundedInv (depth n) keys rem st' := by
  obtain ⟨⟨visited, edges, allSigned⟩, queried, seen, bad⟩ := st
  obtain ⟨hroot, hbound, hvis, huniq, hall⟩ := hinv
  have hmul : (rem + 1) * (depth n - 1) = rem * (depth n - 1) + (depth n - 1) :=
    Nat.succ_mul rem (depth n - 1)
  refine guardedTreeHandler_support_inv depth n (localSignBody S depth keys sigCap n)
    (presampledBoundedInv (depth n) keys rem) req _
    (fun _ => ⟨hroot, by omega, hvis, huniq,
      allSignedInv_mono (fun _ h => h) (fun _ => List.mem_cons_of_mem _) hall⟩)
    fun _ _ leaf _ _ sig ⟨v', e'', a''⟩ hm => ?_
  supp_cases hm [localSignBody] with ⟨⟨⟨node, idx, certs⟩, v₁, e₁, a₁⟩, hm_cert, ⟨σ, e₃, a₃⟩,
    hm_edge, rfl, rfl, rfl, rfl⟩
  obtain ⟨hnLen, hnode_v', hroot_v', hgrow_v', hvis_v', huniq_v', hall_v'⟩ :=
    localCertify_bounded_inv S depth keys sigCap n hd leaf hroot (by omega) hvis huniq hall
      node idx certs v₁ e₁ a₁ hm_cert
  exact ⟨hroot_v', by dsimp only; omega, hvis_v', huniq_v',
    allSignedInv_localSignEdge hm_edge
      (allSignedInv_mono (fun _ h => h) (fun _ => List.mem_cons_of_mem req.2) hall_v')
      ⟨hnode_v', Or.inr ⟨hnLen, List.mem_cons_self⟩⟩⟩

private def chainPk (pk₀ : List Bool) (certs : List (List Bool × List Bool)) (j : ℕ) :
    List Bool :=
  if j = 0 then pk₀ else (certs.getD (j - 1) ([], [])).1

private theorem foldl_verifyStep_spec (S : IndexedSignatureScheme) (pk₀ : List Bool)
    (bits : List Bool) (certs : List (List Bool × List Bool)) (hlen : bits.length = certs.length) :
    ((bits.zip certs).foldl (verifyStep S) (true, pk₀)).2 = chainPk pk₀ certs bits.length ∧
    (((bits.zip certs).foldl (verifyStep S) (true, pk₀)).1 = true ↔
      ∀ j < bits.length,
        S.verify (chainPk pk₀ certs j) (bits.getD j false).toNat
          (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true) := by
  suffices ∀ m ≤ bits.length,
      (((bits.take m).zip (certs.take m)).foldl (verifyStep S) (true, pk₀)).2 =
        chainPk pk₀ certs m ∧
      ((((bits.take m).zip (certs.take m)).foldl (verifyStep S) (true, pk₀)).1 = true ↔
        ∀ j < m, S.verify (chainPk pk₀ certs j) (bits.getD j false).toNat
          (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true) by
    have h := this bits.length le_rfl
    rwa [List.take_length, hlen, List.take_length, ← hlen] at h
  intro m
  induction m with
  | zero => intro _; simp [chainPk]
  | succ m ih =>
    intro hm
    obtain ⟨ih_pk, ih_ok⟩ := ih (by omega)
    rw [List.take_succ_eq_append_getElem hm, List.take_succ_eq_append_getElem (hlen ▸ hm),
      List.zip_append (by simp [hlen]), List.zip_cons_cons, List.zip_nil_right, List.foldl_append,
      List.foldl_cons, List.foldl_nil]
    simp only [verifyStep, ih_pk, Bool.and_eq_true, ih_ok,
      ← List.getD_eq_getElem bits false hm, ← List.getD_eq_getElem certs ([], []) (hlen ▸ hm)]
    exact ⟨by simp [chainPk],
      ⟨fun ⟨ha, hl⟩ j hj => (Nat.lt_succ_iff_lt_or_eq.mp hj).elim (ha j) (· ▸ hl),
        fun h => ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h m (Nat.lt_succ_self m)⟩⟩⟩

private theorem win_implies_any_plantedWin (S : IndexedSignatureScheme) (depth : ℕ → ℕ)
    {n K : ℕ} (hd : 1 ≤ depth n)
    {out : List (List Bool × List Bool) × (List Bool × List Bool) × PresampledState}
    (hkeysLen : out.1.length = K)
    (hinv : presampledBoundedInv (depth n) out.1 0 out.2.2)
    (hwin : treeWinOfPresampled S depth n out = true) :
    ((List.range K).any fun j => plantedWin S depth n j out) = true := by
  classical
  obtain ⟨keys, ⟨msgStar, sigStar⟩, ⟨visited, edges, allSigned⟩, queried, seen, bad⟩ := out
  obtain ⟨hroot, hbound, hvis, huniq, hall⟩ := hinv
  simp only [Nat.zero_mul, Nat.add_zero] at hbound
  simp only [treeWinOfPresampled, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, List.contains_iff_mem, beq_iff_eq] at hwin
  obtain ⟨⟨_, hfresh⟩, hver⟩ := hwin
  set pk₀ := (keys.getD 0 ([], [])).1
  set leaf := (signatureDecoder.decode sigStar).1
  set certs := (signatureDecoder.decode sigStar).2.1
  set last := (signatureDecoder.decode sigStar).2.2
  simp only [verify, keyDecoder.decode_enc] at hver
  change ((leaf.length == depth n) && (certs.length + 1 == depth n) &&
    ((leaf.dropLast.zip certs).foldl (verifyStep S) (true, pk₀)).1 &&
    S.verify ((leaf.dropLast.zip certs).foldl (verifyStep S) (true, pk₀)).2
      (leaf.getLastD false).toNat msgStar last) = true at hver
  simp only [Bool.and_eq_true, beq_iff_eq] at hver
  obtain ⟨⟨⟨hleafLen, hcertsLen⟩, hchainOk⟩, hlastOk⟩ := hver
  have hdropLen : leaf.dropLast.length = certs.length := by
    rw [List.length_dropLast, hleafLen]; omega
  obtain ⟨hchainPk, hchainAll⟩ := foldl_verifyStep_spec S pk₀ leaf.dropLast certs hdropLen
  have hcertsVer : ∀ j < depth n - 1,
      S.verify (chainPk pk₀ certs j) (leaf.getD j false).toNat
        (certs.getD j ([], [])).1 (certs.getD j ([], [])).2 = true := fun j hj => by
    have hjDrop : j < leaf.dropLast.length := by rw [List.length_dropLast, hleafLen]; exact hj
    have hvj := hchainAll.mp hchainOk j hjDrop
    have hbit : leaf.dropLast.getD j false = leaf.getD j false := by
      rw [List.dropLast_eq_take, hleafLen, List.getD_eq_getElem _ _ (by simp; omega),
        List.getElem_take, List.getD_eq_getElem _ _ (by omega)]
    rwa [hbit] at hvj
  rw [hchainPk, List.length_dropLast, hleafLen, show leaf.getLastD false =
    leaf.getD (depth n - 1) false by
      rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, hleafLen,
        List.getD_eq_getElem?_getD]] at hlastOk
  let P (j : ℕ) : Prop :=
    ∃ idx, (leaf.take j, idx) ∈ visited ∧ (keys.getD idx ([], [])).1 = chainPk pk₀ certs j
  set jStar := Nat.findGreatest P (depth n - 1)
  have hjLe : jStar ≤ depth n - 1 := Nat.findGreatest_le (depth n - 1)
  obtain ⟨target, hmemT, hpkT⟩ : P jStar := Nat.findGreatest_spec (Nat.zero_le _) ⟨0, hroot, rfl⟩
  have hpathEq := filter_headD_of_mem_unique visited hmemT huniq
  have hpathLen : (leaf.take jStar).length = jStar := by
    rw [List.length_take, hleafLen]; exact Nat.min_eq_left (by omega)
  have hlogMem : ∀ {u₀ m₀}, (u₀, m₀) ∈ signedLogOf target allSigned →
      ((leaf.take jStar).length + 1 < depth n ∧ ∃ (b : Bool) (childIdx : ℕ), b.toNat = u₀ ∧
        (leaf.take jStar ++ [b], childIdx) ∈ visited ∧ m₀ = (keys.getD childIdx ([], [])).1) ∨
      ((leaf.take jStar).length + 1 = depth n ∧ m₀ ∈ queried) := by
    intro u₀ m₀ hmemLog
    simp only [signedLogOf, List.mem_map, List.mem_filter, beq_iff_eq] at hmemLog
    obtain ⟨⟨p, idx, u', m'⟩, ⟨hm_all, hidxEq⟩, heq⟩ := hmemLog
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    dsimp only at hidxEq
    subst hidxEq
    obtain ⟨hp_vis, hdisj⟩ := hall p idx u' m' hm_all
    obtain ⟨rfl, -⟩ := Prod.mk.inj (huniq _ hp_vis _ hmemT rfl)
    exact hdisj
  rw [List.any_eq_true]
  refine ⟨target, List.mem_range.mpr ?_, ?_⟩
  · have := (hvis _ hmemT).2; dsimp only at hkeysLen; omega
  simp only [plantedWin, extractForgery, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff,
    ne_eq, List.contains_iff_mem, hpathEq, hpathLen]
  by_cases hjLt : jStar + 1 < depth n
  · simp only [hjLt, ↓reduceIte]
    refine ⟨fun hm => ?_, hpkT ▸ hcertsVer jStar (by omega)⟩
    rcases hlogMem hm with ⟨_, b, childIdx, hbu, hcVis, hcmEq⟩ | ⟨hbadLen, _⟩
    · have hbeq := bool_eq_of_toNat_eq hbu
      subst hbeq
      have hjLeaf : jStar < leaf.length := by omega
      rw [List.getD_eq_getElem _ _ hjLeaf, ← List.take_succ_eq_append_getElem hjLeaf]
        at hcVis
      exact Nat.findGreatest_is_greatest (lt_add_one jStar) (by omega)
        ⟨childIdx, hcVis, by simpa [chainPk] using hcmEq.symm⟩
    · rw [hpathLen] at hbadLen; omega
  · simp only [hjLt, ↓reduceIte]
    have hjEq : jStar = depth n - 1 := by omega
    refine ⟨fun hm => ?_, by rw [hpkT, hjEq]; exact hlastOk⟩
    rcases hlogMem hm with ⟨hbadLt, _⟩ | ⟨_, hmq⟩
    · rw [hpathLen, hjEq] at hbadLt; omega
    · exact hfresh hmq

private theorem eval_indexedEufCmaGame_indexedForger (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) (adversary : Forger) (n : ℕ) :
    ProbComp.eval (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) =
      (PMF.uniformOfFintype (Fin (dyadicSize (slotBound n)))).bind fun target =>
        ProbComp.eval
          (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary target.val)
            n) := by
  simp only [IndexedSignatureScheme.indexedEufCmaGame, indexedForger,
    ProbOracleComp.eval_run_interpret, interp_norm,
    ProbComp.eval_sampleDyadicIndex, pmf_norm]
  rw [PMF.bind_comm]

/-- **From lazy tree signing to indexed forgery**: when `Q * depth n ≤ slotBound n` and `sigCap n`
bounds all supported edge signature lengths, the forging probability in `lazyTreeGame` is at most
`dyadicSize (slotBound n)` times `indexedForger`'s forging probability against `S`. -/
theorem succProbability_lazyTreeGame_le (S : IndexedSignatureScheme)
    (depth slotBound sigCap : ℕ → ℕ) {n Q : ℕ}
    (hcap : 2 ≤ S.capacity n) (hdepth_pos : 1 ≤ depth n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n)
    (adversary : Forger)
    (hq : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
      (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded Q) :
    Game.succProbability (ProbComp.eval (lazyTreeGame S depth adversary n)) ≤
      dyadicSize (slotBound n) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) := by
  set K := dyadicSize (slotBound n)
  set X := presampledExp S depth slotBound sigCap adversary n
  have hslotLt : 1 + Q * (depth n - 1) < K := slot_bound_lt_dyadicSize hdepth_pos hslot
  have hsupp : ∀ out ∈ X.support,
      out.1.length = K ∧ presampledBoundedInv (depth n) out.1 0 out.2.2 := by
    intro out hout
    supp_cases hout [X, presampledExp] with ⟨keys, hkeys, ⟨msig, st⟩, hrun, rfl⟩
    obtain ⟨hkLen, hkSupp⟩ := (ProbComp.mem_support_replicate_iff _ _ _).mp hkeys
    have hpos : 0 < keys.length := by have := two_le_dyadicSize (slotBound n); omega
    have hinit : presampledBoundedInv (depth n) keys Q initPresampledState :=
      ⟨List.mem_singleton.mpr rfl, by simpa [hkLen] using hslotLt.le,
        fun e he => by rw [List.mem_singleton.mp he]; exact ⟨by simp; omega, by simp⟩,
        fun e₁ he₁ e₂ he₂ _ => by rw [List.mem_singleton.mp he₁, List.mem_singleton.mp he₂],
        fun _ _ _ _ h => by cases h⟩
    exact ⟨hkLen, ProbOracleComp.IsQueryBounded.run_interpret_invariant
      (localTreeHandler S depth keys (sigCap n) n) (presampledBoundedInv (depth n) keys)
      (fun r _ ⟨h1, h2, h3, h4, h5⟩ =>
        ⟨h1, le_trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_succ r)) _) h2,
          h3, h4, h5⟩)
      (fun _ req _ hs ans st' hm => localTreeHandler_bounded_inv S depth keys (sigCap n) n
        hdepth_pos req hs ans st' hm)
      (hq _ (hkSupp _ (List.getD_mem ([], []) hpos))) hinit msig st hrun⟩
  have hsum : ProbComp.eval (lazyTreeGame S depth adversary n) true ≤
      ∑ i ∈ Finset.range K, ProbComp.eval
        (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary i) n) true := by
    rw [eval_lazyTreeGame_eq_presampled S depth slotBound sigCap hdepth_pos hslot hsigCap
      adversary hq]
    refine (PMF.map_true_mono X
      (F := fun out => (List.range K).any fun j => plantedWin S depth n j out) fun out ho hw =>
        let ⟨hk, hi⟩ := hsupp out ho; win_implies_any_plantedWin S depth hdepth_pos hk hi hw).trans
      ((PMF.map_any_range_true_le_sum X K (plantedWin S depth n)).trans
        (Finset.sum_le_sum fun i hi => by
          rw [map_plantedWin_presampledExp S depth slotBound sigCap hcap adversary
            (Finset.mem_range.mp hi)]))
  have havg : ((K : ℕ) : ℝ≥0∞) * ProbComp.eval
        (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n) true =
      ∑ i ∈ Finset.range K, ProbComp.eval
        (S.indexedEufCmaGame (indexedForgerAt S depth slotBound sigCap adversary i) n) true := by
    rw [eval_indexedEufCmaGame_indexedForger, PMF.bind_apply, tsum_fintype]
    simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
    rw [← Finset.mul_sum, ← mul_assoc,
      ENNReal.mul_inv_cancel (Nat.cast_ne_zero.mpr (dyadicSize_pos (slotBound n)).ne') (by simp),
      one_mul, ← Fin.sum_univ_eq_sum_range]
  rw [← havg] at hsum
  have h := ENNReal.toNNReal_mono (ENNReal.mul_ne_top (by simp) (PMF.apply_ne_top _ _)) hsum
  rw [ENNReal.toNNReal_mul, ENNReal.toNNReal_natCast] at h
  exact h

end LazyToIndexed

/-! ### Concrete and asymptotic EUF-CMA security of `TreeSignature.scheme` -/

section AsymptoticSecurity

/-- **Concrete security of `treeIdealGame`** (a step of the proof of [BonehShoup2023],
Theorem 14.6): combining the lazy-coin leaf-collision hybrid and the planted-node indexed-forgery
reduction. -/
theorem succProbability_treeIdealGame_le (S : IndexedSignatureScheme) (T : S.Seeded)
    (depth N slotBound sigCap : ℕ → ℕ) {n Q : ℕ}
    (hcap : 2 ≤ S.capacity n) (hdepth_pos : 1 ≤ depth n)
    (hwidth : 2 * depth n + 4 ≤ N n) (hkgBudget : T.keyGenBudget n ≤ N n)
    (hsgBudget : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
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
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (hslot : Q * depth n ≤ slotBound n)
    (hsigCap : ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
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
  have hprf := succProbability_treeGame_le_prf (S := S) (T := T) (depth := depth) (N := N)
    family hinv adversary n
  have hideal := succProbability_treeIdealGame_le S T depth N slotBound sigCap (hcap n)
    (hdepth_pos n) hwidth hkgBudget hsgBudget hslot hsigCap adversary hq
  calc Game.succProbability (ProbComp.eval (treeGame S T depth N (prfCoins family) adversary n))
      ≤ Game.succProbability (ProbComp.eval (treeIdealGame S T depth N adversary n)) + _ := hprf
    _ ≤ (_ + _) + _ := add_le_add hideal le_rfl
    _ = _ := by ring

private theorem exists_sigCap_polyTime (S : IndexedSignatureScheme) :
    ∃ sigCap : ℕ → ℕ,
      ComputableInPolyTime sigCap encUnary encUnary ∧
      ∀ n, ∀ keys ∈ (ProbComp.eval (S.keyGen n)).support, ∀ u ≤ 1, ∀ msg,
        (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
        ∀ σ ∈ (ProbComp.eval (S.sign keys.2 u msg)).support, σ.length ≤ sigCap n := by
  obtain ⟨pkB, hpkB, hlenB⟩ := exists_signInput_length_bound S
  obtain ⟨cs, ds, hsgLen⟩ := S.sign_ppt.length_le
  exact ⟨fun n => cs * (3 * pkB n + n + 5) ^ ds, by fun_prop,
    fun n keys hkeys u hu msg hmsg σ hσ =>
      (hsgLen (keys.2, u, msg) σ hσ).trans
        (Nat.mul_le_mul_left cs (Nat.pow_le_pow_left (hlenB n keys hkeys u hu msg hmsg) ds))⟩

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
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ N n)
    (hdepthNeg : Negligible (fun n => (1 : ℝ≥0) / 2 ^ depth n)) :
    (scheme S T (prfCoins family) N depth
      (computableInPolyTime_prfCoins hF.polyTime) hN hdepth hcap hdepth_pos).EUFCMA := by
  obtain ⟨sigCap, hsigCapPoly, hsigCap⟩ := exists_sigCap_polyTime S
  obtain ⟨ck, dk, hkgLen⟩ := S.keyGen_ppt.length_le
  simp only [encUnary_apply, List.length_replicate] at hkgLen
  apply SignatureScheme.EUFCMA.of_negligible
  intro adversary hA
  obtain ⟨εPrf, hεPrfNeg, hprfLe⟩ :=
    exists_negligible_treeGame_le S T depth N hF hdepth hN hNge hinvPoly hinv hA
  obtain ⟨cq, dq, hqb⟩ := hA.query_bounds
  let Q (n : ℕ) : ℕ := cq * (3 * n + ck * (n + 1) ^ dk + 3) ^ dq
  have hQPoly : ComputableInPolyTime Q encUnary encUnary := by
    dsimp only [Q]
    fun_prop
  let slotBound (n : ℕ) : ℕ := Q n * depth n
  have hslotPoly : ComputableInPolyTime slotBound encUnary encUnary :=
    hQPoly.unary_mul' hdepth
  have hForgerPPT := isOraclePPT_indexedForger S hdepth hslotPoly hsigCapPoly hA
  have hIdxNeg := hS.negligible (indexedForger S depth slotBound sigCap adversary) hForgerPPT
  have hbound : ∀ n,
      Game.succProbability
        (ProbComp.eval
          ((scheme S T (prfCoins family) N depth (computableInPolyTime_prfCoins hF.polyTime)
            hN hdepth hcap hdepth_pos).eufCmaGame adversary n)) ≤
      (dyadicSize (slotBound n) : ℝ≥0) * Game.succProbability
        (ProbComp.eval
          (S.indexedEufCmaGame (indexedForger S depth slotBound sigCap adversary) n)) +
      (Q n ^ 2 : ℝ≥0) / 2 ^ (depth n + 1) + εPrf n := fun n => by
    rw [eufCmaGame_scheme]
    have hqBound : ∀ root ∈ (ProbComp.eval (S.keyGen n)).support,
        (adversary n (encPair encUnary encBits (n, root.1))).IsQueryBounded (Q n) := by
      intro root hroot
      have hrk : root.1.length ≤ ck * (n + 1) ^ dk := by
        have := (length_le_encPair_left encBits encBits root).trans (hkgLen n root hroot)
        simpa only [encBits_apply] using this
      have hpkLen : (encPair encUnary encBits (n, root.1)).length = 2 * n + 1 + root.1.length := by
        simp only [length_encPair, encUnary_apply, List.length_replicate, encBits_apply]
      have hleQ : cq * (n + (encPair encUnary encBits (n, root.1)).length + 2) ^ dq ≤ Q n :=
        Nat.mul_le_mul_left cq (Nat.pow_le_pow_left (by omega) dq)
      exact (hqb n _).1.mono hleQ
    have hideal := succProbability_treeIdealGame_le S T depth N slotBound sigCap (hcap n)
      (hdepth_pos n) (hwidth n) (hkgBudget n) (hsgBudget n) le_rfl (hsigCap n) adversary hqBound
    exact (hprfLe n).trans (add_le_add hideal le_rfl)
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
      (msg.length = n ∨ ∃ keys' ∈ (ProbComp.eval (S.keyGen n)).support, msg = keys'.1) →
      T.signBudget keys.2 u msg ≤ budget n)
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
    ∃ M : SignatureScheme, M.EUFCMA := by
  obtain ⟨family, hF⟩ := hf.exists_pseudorandomFunction
  exact hS.exists_eufCMA_of_prf hcap hF

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

end AsymptoticSecurity

end TreeSignature

end Cslib.Crypto
