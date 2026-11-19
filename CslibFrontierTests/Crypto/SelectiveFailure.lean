/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module

public import CslibFrontier.Crypto.Protocols.PIR.SelectiveFailure
public import CslibFrontier.Crypto.Protocols.SelectiveFailure

/-!
# Tests: selective failure attacks across protocols and PIR

* Protocol-agnostic selective failure (`SelectiveFailure.Model`):
  - Input-indexed payload transfer (`SelectiveFailure.indexedPayloadModel`, modeling 1-out-of-`4`
    and batch oblivious transfer on `Fin 2 → Fin 4 → Bool`): perturbing slot `(0, 0)` to
    `!(m 0 0)` causes a selective failure iff the receiver selected slot `0` in instance `0`
    (`isDeterministicAttack_indexedPayload`), achieving distinguishing advantage `1`
    (`advantage_indexedPayload_eq_one`) and refuting `IsSelectiveFailureFree`
    (`not_isSelectiveFailureFree_indexedPayload`).
* Immunity of unbalanced 1-bit XOR-sum PIR (`Scheme.IsSelectiveFailureFree`):
  - `PIR.twoServer (Fin 4)`, `PIR.evenTwoServer (0 : Fin 4)`, `PIR.cube (Fin 3) (Fin 2)`, and the
    Proposition 5 XOR-compressed block scheme `((twoServer (Option (Fin 3))).sumChunks 2)`
    are selective-failure free (`selectiveFailureAdvantage = 0` against every single-server
    malicious answer strategy on every database).
* Vulnerability of matrix-balanced `Scheme.rows` and block-lifted `Scheme.toBlock`
  (CGKS Section 3.4 Corollary 3 & Section 4.1 Proposition 4):
  - `((twoServer (Fin 3)).rows (Fin 3))` and `((cube (Fin 2) (Fin 3)).rows (Fin 3))` are not
    selective-failure free (`not_isSelectiveFailureFree_twoServer_rows`,
    `not_isSelectiveFailureFree_cube_rows`), and `rowsFlipAttack` achieves
    `selectiveFailureAdvantage = 1` between `(0, 0)` and `(1, 0)` on **every** database `x`.
  - Block-lifted bit retrieval `((twoServer (Fin 3)).toBlock (Fin 4)).toBitScheme` is not
    selective-failure free (`Scheme.not_isSelectiveFailureFree_toBlock_toBitScheme`).
* Vulnerability of covering-code subcube emulation PIR (`RadiusOneCover.scheme`, CGKS Section 3.3
  Theorem 1 & Corollary 2):
  - `RadiusOneCover.cubeThree.scheme (Fin 4)` (`2` servers, `O(n ^ (1 / 3))`) and
    `RadiusOneCover.cubeFour.scheme (Fin 4)` (`4` servers, `O(n ^ (1 / 4))`) are not
    selective-failure free (`not_isSelectiveFailureFree_cubeThree`,
    `not_isSelectiveFailureFree_cubeFour`), and `coverFlipAttack` achieves
    `selectiveFailureAdvantage = 1` on **every** database `x`.
* Vulnerability of polynomial Shamir `t`-private PIR (`PIR.shamir` and `PIR.shamirCube`):
  - Over `ZMod 5`, `shamir (Fin 4) params2_3` (`t = 2, k = 3`) is `2`-private against passive
    coalitions (`isTPrivate_shamir`) yet vulnerable to a **single** server's additive shift attack
    `lagrangeShiftAttack` with `Δ = 2` (`not_isSelectiveFailureFree_shamir`,
    `selectiveFailureAdvantage_shamir_eq_one = 1`).
  - Over `ZMod 5`, `shamirCube (Fin 2) (Fin 3) params1_3` (`d = 2, t = 1, k = 3`) is `1`-private
    against passive servers (`isTPrivate_shamirCube`) yet vulnerable to a single server's additive
    shift attack (`not_isSelectiveFailureFree_shamirCube`,
    `selectiveFailureAdvantage_shamirCube_eq_one = 1`).
-/

public section

namespace CslibFrontierTests.Crypto.SelectiveFailure

open Cslib Cslib.Crypto.Protocols Cslib.Crypto.Protocols.SelectiveFailure
  Cslib.Crypto.Protocols.PIR Cslib.Crypto.Protocols.SecretSharing

/-! ### 1. Protocol-agnostic selective failure: 1-out-of-4 OT / indexed payload transfer -/

/-- Perturbing slot `(0, 0)` in batch 1-out-of-`4` payload transfer causes a deterministic
selective failure iff the receiver selected slot `0` in instance `0`. -/
example (m : Fin 2 → Fin 4 → Bool) :
    (indexedPayloadModel m).IsDeterministicAttack
      (indexedPayloadPerturb m 0 0 (!(m 0 0))) (fun b => decide (b 0 = 0)) :=
  isDeterministicAttack_indexedPayload m 0 0 (Bool.not_ne_self (m 0 0))

/-- Distinguishing advantage `1` between receiver choices `fun _ => 0` and `fun _ => 1` in batch
1-out-of-`4` payload transfer. -/
example (m : Fin 2 → Fin 4 → Bool) :
    (indexedPayloadModel m).advantage
      (indexedPayloadPerturb m 0 0 (!(m 0 0))) (fun _ => 0) (fun _ => 1) = 1 :=
  advantage_indexedPayload_eq_one m 0 0 (Bool.not_ne_self (m 0 0)) rfl (by decide)

/-- Batch 1-out-of-`4` payload transfer is not selective-failure free. -/
example (m : Fin 2 → Fin 4 → Bool) :
    ¬ (indexedPayloadModel m).IsSelectiveFailureFree :=
  not_isSelectiveFailureFree_indexedPayload m

/-! ### 2. Unbalanced 1-bit XOR-sum PIR schemes are selective-failure free -/

example : (twoServer (Fin 4)).IsSelectiveFailureFree :=
  isSelectiveFailureFree_twoServer

/-- Against `twoServer (Fin 4)`, every single-server malicious answer strategy `malAns` has zero
selective-failure distinguishing advantage on every database `x`. -/
example (x : Fin 4 → Bool) (s₀ : Bool) (malAns : (Fin 4 → Bool) → Bool) (i₀ i₁ : Fin 4) :
    (twoServer (Fin 4)).selectiveFailureAdvantage x s₀ malAns i₀ i₁ = 0 :=
  isSelectiveFailureFree_twoServer x (s₀, malAns) i₀ i₁

example : (evenTwoServer (0 : Fin 4)).IsSelectiveFailureFree :=
  isSelectiveFailureFree_evenTwoServer 0

example : (cube (Fin 3) (Fin 2)).IsSelectiveFailureFree :=
  isSelectiveFailureFree_cube

/-- Proposition 5's `sumChunks` XOR-compression preserves selective-failure immunity. -/
example : ((twoServer (Option (Fin 3))).sumChunks 2).IsSelectiveFailureFree :=
  Scheme.IsSelectiveFailureFree.sumChunks 2 isCorrect_twoServer isPrivate_twoServer
    (Scheme.hasXorReconstruct_twoServer (Option (Fin 3)))

/-! ### 3. Matrix-balanced `Scheme.rows` and block-lifted `Scheme.toBlock` are vulnerable -/

example : ¬ ((twoServer (Fin 3)).rows (Fin 3)).IsSelectiveFailureFree :=
  not_isSelectiveFailureFree_twoServer_rows

example : ¬ ((cube (Fin 2) (Fin 3)).rows (Fin 3)).IsSelectiveFailureFree :=
  not_isSelectiveFailureFree_cube_rows

/-- Flipping row `0` of server `false`'s answer in `(twoServer (Fin 3)).rows (Fin 3)` distinguishes
query `(0, 0)` from query `(1, 0)` with advantage `1` on **every** database `x` (including the
all-`false` database). -/
example (x : Fin 3 × Fin 3 → Bool) :
    ((twoServer (Fin 3)).rows (Fin 3)).selectiveFailureAdvantage x false
      ((twoServer (Fin 3)).rowsFlipAttack x false 0) (0, 0) (1, 0) = 1 :=
  Scheme.selectiveFailureAdvantage_rows_eq_one isCorrect_twoServer
    (Scheme.hasXorReconstruct_twoServer (Fin 3)) x false (by decide) 0 0

/-- Lifting `twoServer (Fin 3)` to `4`-bit blocks via `Scheme.toBlock (Fin 4)` is vulnerable to
single-bit selective failure attacks. -/
example : ¬ ((twoServer (Fin 3)).toBlock (Fin 4)).toBitScheme.IsSelectiveFailureFree :=
  Scheme.not_isSelectiveFailureFree_toBlock_toBitScheme isCorrect_twoServer
    (Scheme.hasXorReconstruct_twoServer (Fin 3))

/-! ### 4. Covering-code subcube emulation PIR (`RadiusOneCover.scheme`) is vulnerable -/

example : ¬ (RadiusOneCover.cubeThree.scheme (Fin 4)).IsSelectiveFailureFree :=
  not_isSelectiveFailureFree_cubeThree

example : ¬ (RadiusOneCover.cubeFour.scheme (Fin 4)).IsSelectiveFailureFree :=
  not_isSelectiveFailureFree_cubeFour

/-- In CGKS Corollary 2's 2-server `O(n ^ (1 / 3))` scheme
`RadiusOneCover.cubeThree.scheme (Fin 4)`, server `false` emulates cube vertex
`![true, false, false]` along direction `r₀ = 0`, so flipping entry `(0, 0)` distinguishes query
`fun _ => 0` from `fun _ => 1` with advantage `1` on every database `x`. -/
example (x : (Fin 3 → Fin 4) → Bool) :
    (RadiusOneCover.cubeThree.scheme (Fin 4)).selectiveFailureAdvantage x false
      (RadiusOneCover.cubeThree.coverFlipAttack x false 0 0)
      (fun _ => 0) (fun _ => 1) = 1 :=
  RadiusOneCover.cubeThree.selectiveFailureAdvantage_scheme_eq_one x
    (w₀ := ![true, false, false]) rfl 0 rfl (by decide)

/-! ### 5. Polynomial Shamir `t`-private PIR (`shamir` and `shamirCube`) is vulnerable -/

local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- `2`-private `3`-server Shamir parameters over `ZMod 5`. -/
def params2_3 : Shamir.Params (ZMod 5) (Fin 3) :=
  zmodShamirParams (t := 2) (k := 3) (p := 5) (by decide) (by decide)

/-- `1`-private `3`-server Shamir parameters over `ZMod 5`. -/
def params1_3 : Shamir.Params (ZMod 5) (Fin 3) :=
  zmodShamirParams (t := 1) (k := 3) (p := 5) (by decide) (by decide)

private theorem threshold_params2_3 : params2_3.threshold = 2 :=
  threshold_zmodShamirParams (t := 2) (k := 3) (p := 5) (by decide) (by decide)

private theorem threshold_params1_3 : params1_3.threshold = 1 :=
  threshold_zmodShamirParams (t := 1) (k := 3) (p := 5) (by decide) (by decide)

/-- Separation between passive `t`-privacy and active selective-failure security:
`shamir (Fin 4) params2_3` is `2`-private against passive coalitions of size `2`, yet is NOT
selective-failure free against a single server. -/
example :
    (shamir (Fin 4) params2_3).IsTPrivate 2 ∧
      ¬ (shamir (Fin 4) params2_3).IsSelectiveFailureFree :=
  ⟨threshold_params2_3 ▸ isTPrivate_shamir params2_3,
    not_isSelectiveFailureFree_shamir params2_3 (by rw [threshold_params2_3]; decide)⟩

/-- On the point database `x i = decide (i = 0)`, a single server `0` in `2`-private `shamir`
distinguishes `i₀ = 0` from `i₁ = 1` with selective-failure advantage `1` using shift `Δ = 2`. -/
example :
    let x : Fin 4 → Bool := fun i => decide (i = 0)
    (shamir (Fin 4) params2_3).selectiveFailureAdvantage x 0
      ((shamir (Fin 4) params2_3).lagrangeShiftAttack params2_3 x 0 (2 : ZMod 5)) 0 1 = 1 :=
  selectiveFailureAdvantage_shamir_eq_one params2_3 (fun i => decide (i = 0)) 0
    (by decide) (by decide) (by decide)

/-- Degree-`2` polynomial PIR `shamirCube (Fin 2) (Fin 3) params1_3` is `1`-private against passive
servers yet is NOT selective-failure free. -/
example :
    (shamirCube (Fin 2) (Fin 3) params1_3).IsTPrivate 1 ∧
      ¬ (shamirCube (Fin 2) (Fin 3) params1_3).IsSelectiveFailureFree :=
  ⟨threshold_params1_3 ▸ isTPrivate_shamirCube params1_3,
    not_isSelectiveFailureFree_shamirCube params1_3
      (by rw [threshold_params1_3]; decide) (by rw [threshold_params1_3]; decide)⟩

/-- Single-server selective-failure advantage `1` on `shamirCube (Fin 2) (Fin 3) params1_3` between
`fun _ => 0` and `fun _ => 1` on the point database `x i = decide (i = fun _ => 0)`. -/
example :
    let x : (Fin 2 → Fin 3) → Bool := fun i => decide (i = fun _ => 0)
    (shamirCube (Fin 2) (Fin 3) params1_3).selectiveFailureAdvantage x 0
      ((shamirCube (Fin 2) (Fin 3) params1_3).lagrangeShiftAttack params1_3 x 0 (2 : ZMod 5))
      (fun _ => 0) (fun _ => 1) = 1 :=
  selectiveFailureAdvantage_shamirCube_eq_one params1_3
    (by rw [threshold_params1_3]; decide)
    (fun i => decide (i = fun _ => 0)) 0 (by decide) (by decide) (by decide)

end CslibFrontierTests.Crypto.SelectiveFailure
