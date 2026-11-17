/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test)

public import CslibFrontier.Crypto.Primitives.SLHDSA.XMSS.PublicKeyFromSignature

set_option linter.privateModule false

/-!
# Checked clients for FIPS 205 XMSS public-key reconstruction

These checks cover all six standardized XMSS heights, executable composition with WOTS+
Algorithm 8, and the source ledgers exposed for composition. The internal branch and mutable
address invariants are proved privately in the implementation module. These tests are not a
library caller and do not claim generated-signature correctness, verification, security or
compiled resource bounds.
-/

public section

namespace SLHDSAXMSSPublicKeyTests

open Cslib.Crypto Cslib.Crypto.SLHDSA Cslib.Crypto.SLHDSA.XMSS

private def zeroBytes (p : SecurityBytes) : NBytes p := fun _ => 0
private def zeroMessage (p : SecurityBytes) : WOTS.Message p := fun _ => 0
private def zeroWOTSSignature (p : SecurityBytes) : WOTS.Signature p := fun _ _ => 0

private def zeroSignature (p : SecurityBytes) (shape : ParameterShape) : Signature p shape :=
  { wots := zeroWOTSSignature p
    authentication := fun _ _ => 0 }

private def zeroIndex (p : SecurityBytes) (shape : ParameterShape) : LeafIndex p shape :=
  ⟨0, by cases p <;> cases shape <;> decide⟩

private def baseAddress : Address :=
  Address.tree 3 0x0102030405060708 0 0

/-! ### Exact signature and parameter shapes -/

example : ParameterShape.xmssHeight .bytes16 .small = 9 := rfl
example : ParameterShape.xmssHeight .bytes16 .fast = 3 := rfl
example : ParameterShape.xmssHeight .bytes24 .small = 9 := rfl
example : ParameterShape.xmssHeight .bytes24 .fast = 3 := rfl
example : ParameterShape.xmssHeight .bytes32 .small = 8 := rfl
example : ParameterShape.xmssHeight .bytes32 .fast = 4 := rfl

example : signatureBlocks .bytes16 .small = 44 := rfl
example : signatureBytes .bytes16 .small = 704 := rfl
example : signatureBlocks .bytes32 .fast = 71 := rfl
example : signatureBytes .bytes32 .fast = 2272 := rfl

private def indexFive : LeafIndex .bytes16 .fast := ⟨5, by decide⟩

/-! ### Complete executable clients -/

example : NBytes .bytes16 :=
  xmssPkFromSig .shake (zeroIndex .bytes16 .small) (zeroSignature .bytes16 .small)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress
example : NBytes .bytes16 :=
  xmssPkFromSig .sha2 (zeroIndex .bytes16 .fast) (zeroSignature .bytes16 .fast)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress
example : NBytes .bytes24 :=
  xmssPkFromSig .shake (zeroIndex .bytes24 .small) (zeroSignature .bytes24 .small)
    (zeroMessage .bytes24) (zeroBytes .bytes24) baseAddress
example : NBytes .bytes24 :=
  xmssPkFromSig .sha2 (zeroIndex .bytes24 .fast) (zeroSignature .bytes24 .fast)
    (zeroMessage .bytes24) (zeroBytes .bytes24) baseAddress
example : NBytes .bytes32 :=
  xmssPkFromSig .shake (zeroIndex .bytes32 .small) (zeroSignature .bytes32 .small)
    (zeroMessage .bytes32) (zeroBytes .bytes32) baseAddress
example : NBytes .bytes32 :=
  xmssPkFromSig .sha2 (zeroIndex .bytes32 .fast) (zeroSignature .bytes32 .fast)
    (zeroMessage .bytes32) (zeroBytes .bytes32) baseAddress

example (family : HashFamily) :
    (xmssPkFromSigWithLedger family indexFive (zeroSignature .bytes16 .fast)
      (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress).output =
      xmssPkFromSig family indexFive (zeroSignature .bytes16 .fast) (zeroMessage .bytes16)
        (zeroBytes .bytes16) baseAddress :=
  xmssPkFromSigWithLedger_output family indexFive (zeroSignature .bytes16 .fast)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress

example (family : HashFamily) :
    (xmssPkFromSigWithLedger family indexFive (zeroSignature .bytes16 .fast)
      (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress).ledger =
      sourceLedger (zeroMessage .bytes16) indexFive :=
  xmssPkFromSigWithLedger_ledger family indexFive (zeroSignature .bytes16 .fast)
    (zeroMessage .bytes16) (zeroBytes .bytes16) baseAddress

/-! ### Exact source ledgers -/

example : (operationLedger (zeroMessage .bytes16) indexFive).treeIndexWrites = 4 := rfl
example : (authenticationCalls 5 3).hCalls = 3 :=
  (authenticationCalls_fixed 5 3).2.2.1
example :
    (authenticationCalls 5 3).nodeFirstBranches +
      (authenticationCalls 5 3).authenticationFirstBranches = 3 :=
  authenticationCalls_branch_partition 5 3
example :
    (staticDescriptionLedger .bytes16 .fast).compiledDescriptionBytes = none := rfl
example : (staticDescriptionLedger .bytes16 .fast).hInputBytes = 32 := rfl
example : (staticDescriptionLedger .bytes16 .fast).outputBytes = 16 := rfl

end SLHDSAXMSSPublicKeyTests
