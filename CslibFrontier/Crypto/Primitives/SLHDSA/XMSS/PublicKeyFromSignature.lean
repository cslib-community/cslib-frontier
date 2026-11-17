/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Primitives.SLHDSA.WOTS.PublicKeyFromSignature
import Mathlib.Tactic

/-!
# Definitions-only FIPS 205 XMSS public-key reconstruction

This module implements FIPS 205, Section 6.3, Algorithm 11. It first reconstructs the WOTS+
public key with Algorithm 8, then combines that leaf with the ordered XMSS authentication path.
At level `k`, the quotient `floor(idx / 2^k)` selects whether the current node precedes or follows
`AUTH[k]`; the concrete addressed function `H` is then called at tree height `k + 1` and tree
index `floor(idx / 2^(k + 1))`.

The executable evaluator carries source operation, external-query and static-shape ledgers. The
operation ledger is assembled from the instrumented WOTS+ call and the instrumented authentication
fold, rather than attached independently to the output. The external-query count is zero because
this layer invokes the concrete hash functions, not oracle handlers. The static ledger records the
source input/output shapes and deliberately records no compiled-program description size.

This is a definitions-only milestone. Its first semantic correctness property would say that a
signature produced by FIPS 205 Algorithms 9--10 reconstructs the corresponding XMSS root; those
algorithms are not yet formalized, so that property is not proved here. FIPS 205 Algorithm 13 is
the next library consumer: it threads `d` calls to this evaluator through the hypertree layers.
This module also does not define a generic Merkle tree, perform full SLH-DSA verification, or
establish classical or quantum security. It gives no machine, program-size, gate, qubit, timing
or constant-time bound.

## Main definitions

* `Cslib.Crypto.SLHDSA.XMSS.Signature`: the exact WOTS+ signature and `h'`-node authentication
  path.
* `Cslib.Crypto.SLHDSA.XMSS.xmssPkFromSigWithLedger`: Algorithm 11 with source ledgers.
* `Cslib.Crypto.SLHDSA.XMSS.xmssPkFromSig`: FIPS 205 Algorithm 11.

## Main results

* `Cslib.Crypto.SLHDSA.XMSS.authenticationCalls_fixed`: each authentication level contributes one
  node read, pair construction, `H` call, height write and index write.
* `Cslib.Crypto.SLHDSA.XMSS.authenticationCalls_branch_partition`: the two input orders partition
  the authentication levels.
* `Cslib.Crypto.SLHDSA.XMSS.xmssPkFromSigWithLedger_ledger`: the complete run agrees with the
  closed source ledger.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Table 2 and Section 6.3,
  Algorithm 11, printed p. 25][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA.XMSS

open Cslib.Crypto Cslib.Crypto.SLHDSA

/-- An XMSS signature is a WOTS+ signature followed by exactly `h'` authentication nodes. -/
structure Signature (p : SecurityBytes) (shape : ParameterShape) where
  /-- The first `len` `n`-byte blocks, interpreted as a WOTS+ signature. -/
  wots : WOTS.Signature p
  /-- The following `h'` `n`-byte blocks, from leaf level upward. -/
  authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p

/-- The number `len + h'` of `n`-byte blocks in an XMSS signature. -/
@[expose] def signatureBlocks (p : SecurityBytes) (shape : ParameterShape) : ℕ :=
  WOTS.len p + ParameterShape.xmssHeight p shape

/-- The exact byte length `(len + h') * n` of an XMSS signature. -/
@[expose] def signatureBytes (p : SecurityBytes) (shape : ParameterShape) : ℕ :=
  signatureBlocks p shape * p.count

/-- A WOTS+ leaf index is bounded by the `2^h'` leaves of its standardized XMSS tree. -/
abbrev LeafIndex (p : SecurityBytes) (shape : ParameterShape) :=
  Fin (2 ^ ParameterShape.xmssHeight p shape)

private theorem leafCount_le_addressWord (p : SecurityBytes) (shape : ParameterShape) :
    2 ^ ParameterShape.xmssHeight p shape ≤ 2 ^ 32 := by
  cases p <;> cases shape <;> decide

private theorem xmssHeight_le_nine (p : SecurityBytes) (shape : ParameterShape) :
    ParameterShape.xmssHeight p shape ≤ 9 := by
  cases p <;> cases shape <;> decide

private def leafAddressWord {p : SecurityBytes} {shape : ParameterShape}
    (idx : LeafIndex p shape) : AddressWord :=
  ⟨idx, idx.isLt.trans_le (leafCount_le_addressWord p shape)⟩

private def heightAddressWord {p : SecurityBytes} {shape : ParameterShape}
    (level : Fin (ParameterShape.xmssHeight p shape)) : AddressWord :=
  ⟨level.val + 1, by
    have hlevel := level.isLt
    have hheight := xmssHeight_le_nine p shape
    omega⟩

private def wotsHashAddress {p : SecurityBytes} {shape : ParameterShape}
    (address : Address) (idx : LeafIndex p shape) : Address :=
  (address.setTypeAndClear .wotsHash).setKeyPairAddress (leafAddressWord idx)

private theorem wotsHashAddress_valid {p : SecurityBytes} {shape : ParameterShape}
    (address : Address) (idx : LeafIndex p shape) :
    WOTS.ValidHashAddress (wotsHashAddress address idx) :=
  rfl

private def initialTreeAddress {p : SecurityBytes} {shape : ParameterShape}
    (address : Address) (idx : LeafIndex p shape) : Address :=
  (address.setTypeAndClear .tree).setTreeIndex (leafAddressWord idx)

private def nodeIsLeft (index level : ℕ) : Bool :=
  (index / 2 ^ level) % 2 == 0

private theorem nodeIsLeft_eq_true_iff (index level : ℕ) :
    nodeIsLeft index level = true ↔ (index / 2 ^ level) % 2 = 0 := by
  simp [nodeIsLeft]

private def nextTreeIndexAddressWord (current : AddressWord) (left : Bool) : AddressWord :=
  if left = true then
    ⟨current.val / 2, (Nat.div_le_self current.val 2).trans_lt current.isLt⟩
  else
    ⟨(current.val - 1) / 2,
      ((Nat.div_le_self (current.val - 1) 2).trans (Nat.sub_le current.val 1)).trans_lt
        current.isLt⟩

private theorem nextTreeIndexAddressWord_eq_half (current : AddressWord) (left : Bool)
    (hleft : left = true ↔ current.val % 2 = 0) :
    (nextTreeIndexAddressWord current left).val = current.val / 2 := by
  by_cases h : left = true
  · simp only [nextTreeIndexAddressWord, h, ite_true]
  · have hodd : current.val % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one current.val with heven | hodd
      · exact (h (hleft.mpr heven)).elim
      · exact hodd
    simp only [nextTreeIndexAddressWord, h, Bool.false_eq_true, ite_false]
    omega

private def authenticationStepAddress {p : SecurityBytes} {shape : ParameterShape}
    (current : Address) (level : Fin (ParameterShape.xmssHeight p shape))
    (left : Bool) : Address :=
  (current.setTreeHeight (heightAddressWord level)).setTreeIndex
    (nextTreeIndexAddressWord current.word7 left)

/-- When the current index is `floor(idx / 2^levels)`, the source's even/odd update produces
`floor(idx / 2^(levels + 1))`. -/
private theorem authenticationStepAddress_index {p : SecurityBytes} {shape : ParameterShape}
    (current : Address) (idx : LeafIndex p shape) (levels : ℕ)
    (level : Fin (ParameterShape.xmssHeight p shape)) (_hlevel : level.val = levels)
    (hindex : current.word7.val = idx.val / 2 ^ levels) :
    (authenticationStepAddress current level (nodeIsLeft idx.val levels)).word7.val =
      idx.val / 2 ^ (levels + 1) := by
  have hleft : nodeIsLeft idx.val levels = true ↔ current.word7.val % 2 = 0 := by
    rw [hindex]
    exact nodeIsLeft_eq_true_iff idx.val levels
  change (nextTreeIndexAddressWord current.word7 (nodeIsLeft idx.val levels)).val = _
  rw [nextTreeIndexAddressWord_eq_half current.word7 (nodeIsLeft idx.val levels) hleft, hindex,
    Nat.div_div_eq_div_mul, ← pow_succ]

private def AddressAtLevel {p : SecurityBytes} {shape : ParameterShape}
    (initial : Address) (idx : LeafIndex p shape) (levels : ℕ) (current : Address) : Prop :=
  current.addressType = .tree ∧
    current.word5 = 0 ∧
    current.word6.val = levels ∧
    current.word7.val = idx.val / 2 ^ levels ∧
    current.layerAddress = initial.layerAddress ∧
    current.treeAddress = initial.treeAddress

/-- Lines 6--7 establish the level-zero tree-address invariant. -/
private theorem addressAtLevel_initial {p : SecurityBytes} {shape : ParameterShape}
    (initial : Address) (idx : LeafIndex p shape) :
    AddressAtLevel initial idx 0 (initialTreeAddress initial idx) := by
  simp [AddressAtLevel, initialTreeAddress, Address.setTreeIndex, leafAddressWord]

/-- Lines 9 and 11/14 advance the exact mutable-address invariant by one level. -/
private theorem addressAtLevel_step {p : SecurityBytes} {shape : ParameterShape}
    {initial current : Address} {idx : LeafIndex p shape} {levels : ℕ}
    (hcurrent : AddressAtLevel initial idx levels current)
    (level : Fin (ParameterShape.xmssHeight p shape)) (hlevel : level.val = levels) :
    AddressAtLevel initial idx (levels + 1)
      (authenticationStepAddress current level (nodeIsLeft idx.val levels)) := by
  rcases hcurrent with ⟨htype, hword5, _hheight, hindex, hlayer, htree⟩
  refine ⟨htype, hword5, ?_, ?_, hlayer, htree⟩
  · exact hlevel ▸ rfl
  · exact authenticationStepAddress_index current idx levels level hlevel hindex

/-- The exact ordered two-block input to `H` at one authentication level. -/
private def authenticationInput {p : SecurityBytes} {shape : ParameterShape}
    (idx : LeafIndex p shape) (level : Fin (ParameterShape.xmssHeight p shape))
    (node authenticationNode : NBytes p) : TwoNBytes p :=
  if nodeIsLeft idx.val level.val = true then
    FixedBytes.pairBlocks node authenticationNode
  else
    FixedBytes.pairBlocks authenticationNode node

/-- Exact operations performed by an authentication-path prefix. -/
structure AuthenticationCalls where
  /-- Authentication nodes read. -/
  authenticationNodesRead : ℕ
  /-- Ordered two-block inputs constructed. -/
  pairConstructions : ℕ
  /-- Calls to the concrete addressed function `H`. -/
  hCalls : ℕ
  /-- Writes of the tree-height word. -/
  treeHeightWrites : ℕ
  /-- Writes of the tree-index word after the initial line 7 write. -/
  treeIndexWrites : ℕ
  /-- Levels where the current node is the first input block. -/
  nodeFirstBranches : ℕ
  /-- Levels where the authentication node is the first input block. -/
  authenticationFirstBranches : ℕ
  deriving DecidableEq, Repr

private def AuthenticationCalls.addStep (calls : AuthenticationCalls) (left : Bool) :
    AuthenticationCalls :=
  { authenticationNodesRead := calls.authenticationNodesRead + 1
    pairConstructions := calls.pairConstructions + 1
    hCalls := calls.hCalls + 1
    treeHeightWrites := calls.treeHeightWrites + 1
    treeIndexWrites := calls.treeIndexWrites + 1
    nodeFirstBranches := calls.nodeFirstBranches + if left = true then 1 else 0
    authenticationFirstBranches :=
      calls.authenticationFirstBranches + if left = true then 0 else 1 }

/-- Closed source-operation ledger for the first `levels` authentication nodes. -/
def authenticationCalls (index : ℕ) : ℕ → AuthenticationCalls
  | 0 => ⟨0, 0, 0, 0, 0, 0, 0⟩
  | levels + 1 => (authenticationCalls index levels).addStep (nodeIsLeft index levels)

/-- Each processed authentication node produces exactly one pair, `H` call, height write and
post-initialization index write. -/
theorem authenticationCalls_fixed (index levels : ℕ) :
    (authenticationCalls index levels).authenticationNodesRead = levels ∧
      (authenticationCalls index levels).pairConstructions = levels ∧
      (authenticationCalls index levels).hCalls = levels ∧
      (authenticationCalls index levels).treeHeightWrites = levels ∧
      (authenticationCalls index levels).treeIndexWrites = levels := by
  induction levels with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ levels ih =>
      simp [authenticationCalls, AuthenticationCalls.addStep, ih]

/-- The left-first and authentication-first branches partition the processed levels. -/
theorem authenticationCalls_branch_partition (index levels : ℕ) :
    (authenticationCalls index levels).nodeFirstBranches +
      (authenticationCalls index levels).authenticationFirstBranches = levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      cases hleft : nodeIsLeft index levels <;>
        simp only [authenticationCalls, AuthenticationCalls.addStep, hleft,
          Bool.false_eq_true, ite_false, ite_true] <;>
        omega

private structure AuthenticationRun (p : SecurityBytes) where
  /-- The current `n`-byte tree node. -/
  output : NBytes p
  /-- The mutable address after the processed prefix. -/
  address : Address
  /-- Operations actually accumulated while constructing the node. -/
  calls : AuthenticationCalls

/-- Instrumented Algorithm 11 lines 8--18 for an authentication-path prefix. Calls occur in
increasing level order, and each recursive step derives its output from the preceding output. -/
private def authenticationRootWithCalls (family : HashFamily) {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape)
    (authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p)
    (publicSeed : NBytes p) (address : Address) (leaf : NBytes p) :
    (levels : ℕ) → levels ≤ ParameterShape.xmssHeight p shape → AuthenticationRun p
  | 0, _ => ⟨leaf, initialTreeAddress address idx, authenticationCalls idx.val 0⟩
  | levels + 1, hlevels =>
      let previous := authenticationRootWithCalls family idx authentication publicSeed address leaf
        levels (by omega)
      let level : Fin (ParameterShape.xmssHeight p shape) := ⟨levels, by omega⟩
      let left := nodeIsLeft idx.val levels
      let nextAddress := authenticationStepAddress previous.address level left
      { output := h family publicSeed nextAddress
          (authenticationInput idx level previous.output (authentication level))
        address := nextAddress
        calls := previous.calls.addStep left }

private theorem authenticationRootWithCalls_calls (family : HashFamily) {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape)
    (authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p)
    (publicSeed : NBytes p) (address : Address) (leaf : NBytes p) (levels : ℕ)
    (hlevels : levels ≤ ParameterShape.xmssHeight p shape) :
    (authenticationRootWithCalls family idx authentication publicSeed address leaf levels
      hlevels).calls = authenticationCalls idx.val levels := by
  induction levels with
  | zero => rfl
  | succ levels ih =>
      simp only [authenticationRootWithCalls, ih, authenticationCalls]

/-- The address carried by the actual recursive run has the exact Algorithm 11 state after every
processed prefix. -/
private theorem authenticationRootWithCalls_addressAtLevel (family : HashFamily)
    {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape)
    (authentication : Fin (ParameterShape.xmssHeight p shape) → NBytes p)
    (publicSeed : NBytes p) (address : Address) (leaf : NBytes p) (levels : ℕ)
    (hlevels : levels ≤ ParameterShape.xmssHeight p shape) :
    AddressAtLevel address idx levels
      (authenticationRootWithCalls family idx authentication publicSeed address leaf levels
        hlevels).address := by
  induction levels with
  | zero => exact addressAtLevel_initial address idx
  | succ levels ih =>
      change AddressAtLevel address idx (levels + 1)
        (authenticationStepAddress
          (authenticationRootWithCalls family idx authentication publicSeed address leaf levels
            (by omega)).address
          ⟨levels, by omega⟩ (nodeIsLeft idx.val levels))
      exact addressAtLevel_step (ih (by omega)) ⟨levels, by omega⟩ rfl

/-- Exact source operations of Algorithm 11, including the nested Algorithm 8 ledger. -/
structure OperationLedger where
  /-- The exact nested WOTS+ Algorithm 8 ledger. -/
  wots : WOTS.PublicKeyFromSigCalls
  /-- Invocations of WOTS+ public-key reconstruction. -/
  wotsPkFromSigInvocations : ℕ
  /-- Algorithm 11 calls to `setTypeAndClear`, excluding the nested WOTS+ ledger. -/
  typeAndClearCalls : ℕ
  /-- Algorithm 11 key-pair address writes, excluding the nested WOTS+ ledger. -/
  keyPairAddressWrites : ℕ
  /-- Algorithm 11 initial and per-level tree-index writes. -/
  treeIndexWrites : ℕ
  /-- Operations accumulated by the authentication-path fold. -/
  authentication : AuthenticationCalls
  deriving DecidableEq, Repr

/-- External oracle operations at this concrete executable layer. -/
structure QueryLedger where
  /-- Calls through an external oracle interface. Concrete `F`, `T_len`, and `H` are not counted. -/
  externalOracleQueries : ℕ
  /-- External oracle handlers installed by this evaluator. -/
  externalOracleHandlers : ℕ
  deriving DecidableEq, Repr

/-- Static source shapes and the deliberately absent compiled-description measurement. -/
structure StaticDescriptionLedger where
  /-- WOTS+ signature blocks. -/
  wotsSignatureBlocks : ℕ
  /-- Authentication-path blocks. -/
  authenticationBlocks : ℕ
  /-- Total XMSS signature blocks. -/
  signatureBlocks : ℕ
  /-- Total XMSS signature bytes. -/
  signatureBytes : ℕ
  /-- Blocks in each `H` input. -/
  hInputBlocks : ℕ
  /-- Bytes in each `H` input. -/
  hInputBytes : ℕ
  /-- Bytes in the reconstructed root. -/
  outputBytes : ℕ
  /-- `none`: this source specification has no compiled-program description-size measurement. -/
  compiledDescriptionBytes : Option ℕ
  deriving DecidableEq, Repr

/-- The three source-ledger views kept distinct from compiled resource claims. -/
structure SourceLedger where
  /-- Exact source operations. -/
  operations : OperationLedger
  /-- External-query boundary, separated from concrete hash calls. -/
  queries : QueryLedger
  /-- Static source shapes and the absence of a compiled-description measurement. -/
  staticDescription : StaticDescriptionLedger
  deriving DecidableEq, Repr

/-- Closed operation ledger for Algorithm 11. -/
@[expose] def operationLedger {p : SecurityBytes} {shape : ParameterShape}
    (M : WOTS.Message p) (idx : LeafIndex p shape) : OperationLedger :=
  { wots := WOTS.publicKeyFromSigCalls M
    wotsPkFromSigInvocations := 1
    typeAndClearCalls := 2
    keyPairAddressWrites := 1
    treeIndexWrites := 1 + ParameterShape.xmssHeight p shape
    authentication := authenticationCalls idx.val (ParameterShape.xmssHeight p shape) }

/-- Closed static-shape ledger for one standardized Algorithm 11 invocation. -/
@[expose] def staticDescriptionLedger (p : SecurityBytes) (shape : ParameterShape) :
    StaticDescriptionLedger :=
  { wotsSignatureBlocks := WOTS.len p
    authenticationBlocks := ParameterShape.xmssHeight p shape
    signatureBlocks := signatureBlocks p shape
    signatureBytes := signatureBytes p shape
    hInputBlocks := 2
    hInputBytes := 2 * p.count
    outputBytes := p.count
    compiledDescriptionBytes := none }

/-- Closed operation/query/static source ledger for Algorithm 11. -/
@[expose] def sourceLedger {p : SecurityBytes} {shape : ParameterShape}
    (M : WOTS.Message p) (idx : LeafIndex p shape) : SourceLedger :=
  { operations := operationLedger M idx
    queries := ⟨0, 0⟩
    staticDescription := staticDescriptionLedger p shape }

/-- Reconstructed root and ledgers actually accumulated by Algorithm 11. -/
structure PublicKeyFromSigRun (p : SecurityBytes) where
  /-- The reconstructed `n`-byte XMSS root. -/
  output : NBytes p
  /-- Source operations, query boundary and static shapes accumulated by the run. -/
  ledger : SourceLedger

/-- Instrumented FIPS 205 Algorithm 11. -/
def xmssPkFromSigWithLedger (family : HashFamily) {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape) (sig : Signature p shape)
    (M : WOTS.Message p) (publicSeed : NBytes p) (address : Address) : PublicKeyFromSigRun p :=
  let hashAddress := wotsHashAddress address idx
  let wotsRun := WOTS.wotsPkFromSigWithCalls family sig.wots M publicSeed hashAddress
    (wotsHashAddress_valid address idx)
  let authenticationRun := authenticationRootWithCalls family idx sig.authentication publicSeed
    address wotsRun.output (ParameterShape.xmssHeight p shape) le_rfl
  { output := authenticationRun.output
    ledger :=
      { operations :=
          { wots := wotsRun.calls
            wotsPkFromSigInvocations := 1
            typeAndClearCalls := 2
            keyPairAddressWrites := 1
            treeIndexWrites := 1 + ParameterShape.xmssHeight p shape
            authentication := authenticationRun.calls }
        queries := ⟨0, 0⟩
        staticDescription := staticDescriptionLedger p shape } }

/-- FIPS 205 Algorithm 11 as the output projection of its instrumented evaluator. -/
def xmssPkFromSig (family : HashFamily) {p : SecurityBytes} {shape : ParameterShape}
    (idx : LeafIndex p shape) (sig : Signature p shape) (M : WOTS.Message p)
    (publicSeed : NBytes p) (address : Address) : NBytes p :=
  (xmssPkFromSigWithLedger family idx sig M publicSeed address).output

/-- The complete instrumented run agrees with the closed operation/query/static source ledger. -/
@[simp] theorem xmssPkFromSigWithLedger_ledger (family : HashFamily) {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape) (sig : Signature p shape)
    (M : WOTS.Message p) (publicSeed : NBytes p) (address : Address) :
    (xmssPkFromSigWithLedger family idx sig M publicSeed address).ledger = sourceLedger M idx := by
  simp only [xmssPkFromSigWithLedger, sourceLedger, operationLedger,
    WOTS.wotsPkFromSigWithCalls_calls, authenticationRootWithCalls_calls]

/-- `xmssPkFromSig` is the output projection of the instrumented Algorithm 11 evaluator. -/
theorem xmssPkFromSigWithLedger_output (family : HashFamily) {p : SecurityBytes}
    {shape : ParameterShape} (idx : LeafIndex p shape) (sig : Signature p shape)
    (M : WOTS.Message p) (publicSeed : NBytes p) (address : Address) :
    (xmssPkFromSigWithLedger family idx sig M publicSeed address).output =
      xmssPkFromSig family idx sig M publicSeed address :=
  (rfl)

end Cslib.Crypto.SLHDSA.XMSS
