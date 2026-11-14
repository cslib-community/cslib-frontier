/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.CeilDiv
public import CslibFrontier.Init

/-!
# Shared SLH-DSA parameters

This module records the three security-element byte lengths used by every parameter set in
FIPS 205, Table 2. It is shared by the concrete hash calls and the WOTS+, XMSS, FORS, hypertree,
and top-level layers built on them.

The finite type describes only the standardized concrete byte lengths. It is deliberately distinct
from any later asymptotic security family indexed by a growing parameter.

## Main definitions

* `Cslib.Crypto.SLHDSA.SecurityBytes`: the three standard values of `n`.
* `Cslib.Crypto.SLHDSA.SecurityBytes.count`: the byte length selected by a value.
* `Cslib.Crypto.SLHDSA.ParameterShape`: the small-signature and fast-signing shapes.
* `Cslib.Crypto.SLHDSA.ParameterShape.digestBytes`: the six standard values of `m`.

## Main results

* `Cslib.Crypto.SLHDSA.SecurityBytes.count_pos`: every standardized length is positive.
* `Cslib.Crypto.SLHDSA.SecurityBytes.count_le_32`: every standardized length is at most 32.
* `Cslib.Crypto.SLHDSA.ParameterShape.digestBytes_eq`: the Section 9 digest-length formula.

## References

* [NIST, *Stateless Hash-Based Digital Signature Standard*, Table 2][NISTFIPS205]
-/

public section

namespace Cslib.Crypto.SLHDSA

/-- The three byte lengths `n` used by the FIPS 205 parameter sets. -/
inductive SecurityBytes where
  | bytes16
  | bytes24
  | bytes32
  deriving DecidableEq, Repr

namespace SecurityBytes

/-- The security-element and message length `n`, in bytes. -/
def count : SecurityBytes → ℕ
  | .bytes16 => 16
  | .bytes24 => 24
  | .bytes32 => 32

/-- Every standardized value of `n` is positive. -/
theorem count_pos (p : SecurityBytes) : 0 < p.count := by
  cases p <;> decide

/-- Every standardized value of `n` is at most 32 bytes. -/
theorem count_le_32 (p : SecurityBytes) : p.count ≤ 32 := by
  cases p <;> decide

end SecurityBytes

/-- The two parameter shapes paired with every standardized security-byte length. -/
inductive ParameterShape where
  | small
  | fast
  deriving DecidableEq, Repr

namespace ParameterShape

/-- The total hypertree height `h` from FIPS 205, Table 2. -/
def totalHeight : SecurityBytes → ParameterShape → ℕ
  | .bytes16, .small => 63
  | .bytes16, .fast => 66
  | .bytes24, .small => 63
  | .bytes24, .fast => 66
  | .bytes32, .small => 64
  | .bytes32, .fast => 68

/-- The number `d` of hypertree layers from FIPS 205, Table 2. -/
def layers : SecurityBytes → ParameterShape → ℕ
  | .bytes16, .small => 7
  | .bytes16, .fast => 22
  | .bytes24, .small => 7
  | .bytes24, .fast => 22
  | .bytes32, .small => 8
  | .bytes32, .fast => 17

/-- The height `h'` of one XMSS tree from FIPS 205, Table 2. -/
def xmssHeight : SecurityBytes → ParameterShape → ℕ
  | .bytes16, .small => 9
  | .bytes16, .fast => 3
  | .bytes24, .small => 9
  | .bytes24, .fast => 3
  | .bytes32, .small => 8
  | .bytes32, .fast => 4

/-- The FORS tree height `a` from FIPS 205, Table 2. -/
def forsHeight : SecurityBytes → ParameterShape → ℕ
  | .bytes16, .small => 12
  | .bytes16, .fast => 6
  | .bytes24, .small => 14
  | .bytes24, .fast => 8
  | .bytes32, .small => 14
  | .bytes32, .fast => 9

/-- The number `k` of FORS trees from FIPS 205, Table 2. -/
def forsTrees : SecurityBytes → ParameterShape → ℕ
  | .bytes16, .small => 14
  | .bytes16, .fast => 33
  | .bytes24, .small => 17
  | .bytes24, .fast => 33
  | .bytes32, .small => 22
  | .bytes32, .fast => 35

/-- The Section 9 message-digest length `m`, in bytes. -/
def digestBytes (p : SecurityBytes) (shape : ParameterShape) : ℕ :=
  (totalHeight p shape - xmssHeight p shape) ⌈/⌉ 8 +
    (forsTrees p shape * forsHeight p shape) ⌈/⌉ 8 +
    xmssHeight p shape ⌈/⌉ 8

/-- The digest-length definition is exactly the three-slice formula from FIPS 205, Section 9. -/
theorem digestBytes_eq (p : SecurityBytes) (shape : ParameterShape) :
    digestBytes p shape =
      (totalHeight p shape - xmssHeight p shape) ⌈/⌉ 8 +
        (forsTrees p shape * forsHeight p shape) ⌈/⌉ 8 +
        xmssHeight p shape ⌈/⌉ 8 :=
  rfl

/-- Table 2's `h'` values partition the total hypertree height into `d` equal layers. -/
theorem totalHeight_eq_layers_mul_xmssHeight (p : SecurityBytes) (shape : ParameterShape) :
    totalHeight p shape = layers p shape * xmssHeight p shape := by
  cases p <;> cases shape <;> decide

/-- Every standardized message digest has positive byte length. -/
theorem digestBytes_pos (p : SecurityBytes) (shape : ParameterShape) :
    0 < digestBytes p shape := by
  cases p <;> cases shape <;> decide

end ParameterShape

end Cslib.Crypto.SLHDSA
