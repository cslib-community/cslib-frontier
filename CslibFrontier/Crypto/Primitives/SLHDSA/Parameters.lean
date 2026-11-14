/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

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

## Main results

* `Cslib.Crypto.SLHDSA.SecurityBytes.count_pos`: every standardized length is positive.
* `Cslib.Crypto.SLHDSA.SecurityBytes.count_le_32`: every standardized length is at most 32.

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

end Cslib.Crypto.SLHDSA
