/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.MPC.ProductRelation
public import CslibFrontier.Crypto.Protocols.MPC.ProductRelation.Privacy
public import CslibFrontier.Crypto.Protocols.MPC.SPDZ
public import CslibFrontier.Crypto.Protocols.VOLE.Basic
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform

/-!
# Two-Party Authenticated Sharing, Authenticated Beaver Triples, and 7-Relation Reduction

This module formalizes two-party pairwise-key authenticated secret sharing over `ZMod q` (for prime
`q`), its bridges to `Cslib.Crypto.Protocols.MPC.SPDZ.AuthShare` and
`Cslib.Crypto.Protocols.VOLE.VOLECorrelation`, single-element opening verification soundness
(`1 / q`), authenticated Beaver online multiplication closure, and the reduction of authenticated
Beaver-triple checking to `m = 7` product relations via
`CslibFrontier.Crypto.Protocols.MPC.ProductRelation` and
`CslibFrontier.Crypto.Protocols.MPC.ProductRelation.Privacy`.

## Protocol model and source correspondence

* **Two-party pairwise-key authenticated sharing** (following [BonehShoup2023], Section 23.2.4.1;
  exact page and equation numbers for §23.2.4.1 not verified from a rendered PDF): `P₁` holds a
  secret MAC key `α : ZMod q` and `P₂` holds a secret MAC key `β : ZMod q`. A shared secret
  `x = x₁ + x₂` is represented by per-party shares `s₁, s₂ : PartyAuthShare (ZMod q)` where `P₁`
  holds `(x₁, t₁, u₁)` and `P₂` holds `(x₂, t₂, u₂)` satisfying `t₁ + t₂ = α * (x₁ + x₂)` and
  `u₁ + u₂ = β * (x₁ + x₂)`. Each key's tag pair matches a `δ = 0` two-party
  `SPDZ.AuthShare q 2` ([DamgardPastroSmartZakarias2012]) and rearranges into a length-1
  `VOLECorrelation` for opening verification.
* **7-relation authenticated Beaver-triple check** (following [BonehShoup2023], Section 23.2.4.8,
  reducing to Protocol 23.5 of Sections 23.2.4.5–23.2.4.6, printed pp. 1014–1016, and Fact 23.2
  of Section 23.2.4.7, printed pp. 1016–1017; exact page and equation numbers for §23.2.4.8 not
  verified from a rendered PDF): an authenticated Beaver triple `(a, b, c)` is packed into
  `Fin 7 → TripleShare (ZMod q)` encoding `a * b = c` together with the 6 MAC relations
  `α * a = t_a`, `α * b = t_b`, `α * c = t_c`, `β * a = u_a`, `β * b = u_b`, `β * c = u_c`, with
  `P₁` placing `α` and `P₂` placing `0` on indices `1, 2, 3`, and `P₁` placing `0` and `P₂` placing
  `β` on indices `4, 5, 6`. Because `2 * 7 = 14`, the standing distinct-node bound `2 * m < q`
  becomes `hq : 14 < q`, yielding corrupt-dealer soundness `14 / (q - 8)`.
* **Authenticated online multiplication closure**: combining a valid authenticated triple with
  public masked openings `(d, e)` yields a valid authenticated product share agreeing coordinatewise
  with `Beaver.beaverMulShare` and `SPDZ.AuthShare.mulOnline`.

## Main definitions

* `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.Valid`: two-party pairwise-key
  authenticated secret sharing and MAC invariant.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.toSPDZ₁`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.toSPDZ₂`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.toVOLEForP1`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.toVOLEForP2`: explicit bridges to
  `SPDZ.AuthShare` and `VOLE.VOLECorrelation`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.verifyOpening`: single-element share opening check.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.addConstP1`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.addConstP2`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.mulOnlineP1`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.mulOnlineP2`: local constant addition
  and authenticated Beaver online multiplication.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthTriple`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthTriple.Valid`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.toTripleShares₁`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.toTripleShares₂`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.extractTriple`: authenticated triple shares and
  `m = 7` product-relation packing.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.honestAuthPartiesRun`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.checkAuthTriple`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.AuthTripleInstance`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.AuthCorruptP1Adversary`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.AuthCorruptP2Adversary`: authenticated triple
  checking protocol and corrupt-party privacy experiments.

## Main results

* `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.valid_iff_spdz`: exact equivalence
  with `SPDZ.AuthShare.Valid` under keys `(α, β)` with `delta = 0`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.toOuterMeasure_verifyOpening_le`: `1 / q`
  single-share MAC forgery bound over uniform `key : ZMod q`, proved via
  `VOLE.toOuterMeasure_voleVerifyOpening_le`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.Valid.mulOnline`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.PartyAuthShare.val_add_mulOnline_eq_mul`: MAC
  preservation and product correctness of authenticated online Beaver multiplication.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.productRelations_toTripleShares_iff`: exact `iff`
  between `ProductRelations (toTripleShares₁ α tr₁) (toTripleShares₂ β tr₂)` and
  `PartyAuthTriple.Valid α β tr₁ tr₂`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_checkAuthTriple_eq_pure`: completeness `= 1`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_honestAuthPartiesRun_accept_le`: corrupt-dealer
  soundness bound `14 / (q - 8)` for prime `q > 14`.
* `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_authExperiment0P1_eq_experiment1P1`,
  `Cslib.Crypto.Protocols.MPC.ProductRelation.eval_authExperiment0P2_eq_experiment1P2`: exact
  corrupt-party simulation privacy from `ProductRelation.Privacy`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 23.2.4.1, 23.2.4.5–23.2.4.8 (pp. 1014–1017 verified for
  §§23.2.4.5–23.2.4.7; exact locators for §§23.2.4.1 and 23.2.4.8 not verified from rendered
  PDF).
* [I. Damgård, V. Pastro, N. P. Smart, S. Zakarias, *Multiparty Computation from Somewhat
  Homomorphic Encryption*][DamgardPastroSmartZakarias2012].
* [D. Beaver, *Efficient Multiparty Protocols Using Circuit Randomization*][Beaver1991].
-/

public section

namespace Cslib.Crypto.Protocols.MPC.ProductRelation

open Cslib.Probability Cslib.ProbComp
open Cslib.Crypto.Protocols.MPC Cslib.Crypto.Protocols.MPC.Beaver
open Cslib.Crypto.Protocols.MPC.SPDZ Cslib.Crypto.Protocols.VOLE
open scoped ENNReal

/-! ### Two-party pairwise-key authenticated secret sharing and bridges -/

/-- One party's additive share of a two-party pairwise-key authenticated value `x = x₁ + x₂`
over `R` ([BonehShoup2023], §23.2.4.1): holds additive share `val` of `x`, additive share `mac1`
of `P₁`'s MAC `α * x`, and additive share `mac2` of `P₂`'s MAC `β * x`. -/
@[ext] structure PartyAuthShare (R : Type) where
  /-- Party's additive share `x_i` of `x = x₁ + x₂`. -/
  val : R
  /-- Party's additive share `t_i` of `P₁`'s MAC `α * x = t₁ + t₂`. -/
  mac1 : R
  /-- Party's additive share `u_i` of `P₂`'s MAC `β * x = u₁ + u₂`. -/
  mac2 : R
  deriving DecidableEq, Fintype, Inhabited, Repr

namespace PartyAuthShare

/-- Pairwise-key MAC invariant for two-party authenticated shares `(s₁, s₂)` under `P₁`'s key `α`
and `P₂`'s key `β`: `s₁.mac1 + s₂.mac1 = α * (s₁.val + s₂.val)` and
`s₁.mac2 + s₂.mac2 = β * (s₁.val + s₂.val)`. -/
@[expose] def Valid {R : Type} [Mul R] [Add R] (α β : R) (s₁ s₂ : PartyAuthShare R) : Prop :=
  s₁.mac1 + s₂.mac1 = α * (s₁.val + s₂.val) ∧ s₁.mac2 + s₂.mac2 = β * (s₁.val + s₂.val)

instance {R : Type} [Mul R] [Add R] [DecidableEq R] (α β : R) (s₁ s₂ : PartyAuthShare R) :
    Decidable (Valid α β s₁ s₂) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- View `(s₁, s₂)` under `P₁`'s MAC key `α` as a 2-party `SPDZ.AuthShare q 2` with `delta = 0`. -/
@[expose] def toSPDZ₁ {q : ℕ} (s₁ s₂ : PartyAuthShare (ZMod q)) : SPDZ.AuthShare q 2 where
  delta := 0
  valShares := ![s₁.val, s₂.val]
  macShares := ![s₁.mac1, s₂.mac1]

/-- View `(s₁, s₂)` under `P₂`'s MAC key `β` as a 2-party `SPDZ.AuthShare q 2` with `delta = 0`. -/
@[expose] def toSPDZ₂ {q : ℕ} (s₁ s₂ : PartyAuthShare (ZMod q)) : SPDZ.AuthShare q 2 where
  delta := 0
  valShares := ![s₁.val, s₂.val]
  macShares := ![s₁.mac2, s₂.mac2]

/-- Bridge theorem: two-party pairwise-key validity under `(α, β)` holds if and only if both
projected `SPDZ.AuthShare` views satisfy `SPDZ.AuthShare.Valid`. -/
theorem valid_iff_spdz {q : ℕ} (α β : ZMod q) (s₁ s₂ : PartyAuthShare (ZMod q)) :
    Valid α β s₁ s₂ ↔ (toSPDZ₁ s₁ s₂).Valid α ∧ (toSPDZ₂ s₁ s₂).Valid β := by
  simp only [Valid, SPDZ.AuthShare.Valid, SPDZ.AuthShare.macSum, SPDZ.AuthShare.secret,
    toSPDZ₁, toSPDZ₂, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, add_zero]

/-- View `(s₁, s₂)` with `P₂` as the IT-MAC prover and `P₁` (holding `α`) as the verifier as a
length-1 `VOLECorrelation` with receiver key `-α`. -/
@[expose] def toVOLEForP1 {R : Type} [CommRing R] (α : R) (s₁ s₂ : PartyAuthShare R) :
    VOLECorrelation R 1 where
  u := fun _ => s₂.val
  v := fun _ => s₂.mac1
  delta := -α
  w := fun _ => α * s₁.val - s₁.mac1

/-- View `(s₁, s₂)` with `P₁` as the IT-MAC prover and `P₂` (holding `β`) as the verifier as a
length-1 `VOLECorrelation` with receiver key `-β`. -/
@[expose] def toVOLEForP2 {R : Type} [CommRing R] (β : R) (s₁ s₂ : PartyAuthShare R) :
    VOLECorrelation R 1 where
  u := fun _ => s₁.val
  v := fun _ => s₁.mac2
  delta := -β
  w := fun _ => β * s₂.val - s₂.mac2

/-- Bridge theorem: `toVOLEForP1 α s₁ s₂` is valid iff `P₁`'s MAC equation
`s₁.mac1 + s₂.mac1 = α * (s₁.val + s₂.val)` holds. -/
theorem voleValid_toVOLEForP1_iff {R : Type} [CommRing R] (α : R) (s₁ s₂ : PartyAuthShare R) :
    (toVOLEForP1 α s₁ s₂).Valid ↔ s₁.mac1 + s₂.mac1 = α * (s₁.val + s₂.val) := by
  simp only [VOLECorrelation.Valid, toVOLEForP1]
  constructor
  · intro h
    have h0 := h 0
    linear_combination -h0
  · intro h _
    linear_combination -h

/-- Bridge theorem: `toVOLEForP2 β s₁ s₂` is valid iff `P₂`'s MAC equation
`s₁.mac2 + s₂.mac2 = β * (s₁.val + s₂.val)` holds. -/
theorem voleValid_toVOLEForP2_iff {R : Type} [CommRing R] (β : R) (s₁ s₂ : PartyAuthShare R) :
    (toVOLEForP2 β s₁ s₂).Valid ↔ s₁.mac2 + s₂.mac2 = β * (s₁.val + s₂.val) := by
  simp only [VOLECorrelation.Valid, toVOLEForP2]
  constructor
  · intro h
    have h0 := h 0
    linear_combination -h0
  · intro h _
    linear_combination -h

/-- Coordinatewise addition of `PartyAuthShare` values. -/
@[expose] def add {R : Type} [Add R] (s₁ s₂ : PartyAuthShare R) : PartyAuthShare R where
  val := s₁.val + s₂.val
  mac1 := s₁.mac1 + s₂.mac1
  mac2 := s₁.mac2 + s₂.mac2

instance {R : Type} [Add R] : Add (PartyAuthShare R) := ⟨add⟩

/-- Coordinatewise negation of a `PartyAuthShare`. -/
@[expose] def neg {R : Type} [Neg R] (s : PartyAuthShare R) : PartyAuthShare R where
  val := -s.val
  mac1 := -s.mac1
  mac2 := -s.mac2

instance {R : Type} [Neg R] : Neg (PartyAuthShare R) := ⟨neg⟩

/-- Coordinatewise subtraction of `PartyAuthShare` values. -/
@[expose] def sub {R : Type} [Sub R] (s₁ s₂ : PartyAuthShare R) : PartyAuthShare R where
  val := s₁.val - s₂.val
  mac1 := s₁.mac1 - s₂.mac1
  mac2 := s₁.mac2 - s₂.mac2

instance {R : Type} [Sub R] : Sub (PartyAuthShare R) := ⟨sub⟩

/-- Public scalar multiplication of a `PartyAuthShare` by `c : R`. -/
@[expose] def smul {R : Type} [Mul R] (c : R) (s : PartyAuthShare R) : PartyAuthShare R where
  val := c * s.val
  mac1 := c * s.mac1
  mac2 := c * s.mac2

instance {R : Type} [Mul R] : SMul R (PartyAuthShare R) := ⟨smul⟩

/-- Local update of `P₁`'s share when adding a public constant `c : R` (using `P₁`'s key `α`):
`P₁` shifts `val` by `c` and `mac1` by `α * c`, leaving `mac2` unchanged. -/
@[expose] def addConstP1 {R : Type} [Add R] [Mul R] (c α : R) (s₁ : PartyAuthShare R) :
    PartyAuthShare R where
  val := s₁.val + c
  mac1 := s₁.mac1 + α * c
  mac2 := s₁.mac2

/-- Local update of `P₂`'s share when adding a public constant `c : R` (using `P₂`'s key `β`):
`P₂` keeps `val` and `mac1` unchanged and shifts `mac2` by `β * c`. -/
@[expose] def addConstP2 {R : Type} [Add R] [Mul R] (c β : R) (s₂ : PartyAuthShare R) :
    PartyAuthShare R where
  val := s₂.val
  mac1 := s₂.mac1
  mac2 := s₂.mac2 + β * c

/-- Local online Beaver multiplication step for `P₁` given `P₁`'s key `α`, public masked openings
`d, e`, and `P₁`'s authenticated triple shares `(a₁, b₁, c₁)`: computes
`addConstP1 (d * e) α ((e • a₁ + d • b₁) + c₁)`. -/
@[expose] def mulOnlineP1 {R : Type} [Add R] [Mul R]
    (α d e : R) (a₁ b₁ c₁ : PartyAuthShare R) : PartyAuthShare R :=
  addConstP1 (d * e) α ((e • a₁ + d • b₁) + c₁)

/-- Local online Beaver multiplication step for `P₂` given `P₂`'s key `β`, public masked openings
`d, e`, and `P₂`'s authenticated triple shares `(a₂, b₂, c₂)`: computes
`addConstP2 (d * e) β ((e • a₂ + d • b₂) + c₂)`. -/
@[expose] def mulOnlineP2 {R : Type} [Add R] [Mul R]
    (β d e : R) (a₂ b₂ c₂ : PartyAuthShare R) : PartyAuthShare R :=
  addConstP2 (d * e) β ((e • a₂ + d • b₂) + c₂)

private theorem toSPDZ₁_add {q : ℕ} (s₁ s₁' s₂ s₂' : PartyAuthShare (ZMod q)) :
    toSPDZ₁ (s₁ + s₁') (s₂ + s₂') = toSPDZ₁ s₁ s₂ + toSPDZ₁ s₁' s₂' := by
  ext i <;> [simp [toSPDZ₁]; fin_cases i <;> rfl; fin_cases i <;> rfl]

private theorem toSPDZ₂_add {q : ℕ} (s₁ s₁' s₂ s₂' : PartyAuthShare (ZMod q)) :
    toSPDZ₂ (s₁ + s₁') (s₂ + s₂') = toSPDZ₂ s₁ s₂ + toSPDZ₂ s₁' s₂' := by
  ext i <;> [simp [toSPDZ₂]; fin_cases i <;> rfl; fin_cases i <;> rfl]

private theorem toSPDZ₁_neg {q : ℕ} (s₁ s₂ : PartyAuthShare (ZMod q)) :
    toSPDZ₁ (-s₁) (-s₂) = -(toSPDZ₁ s₁ s₂) := by
  ext i <;> [simp [toSPDZ₁]; fin_cases i <;> rfl; fin_cases i <;> rfl]

private theorem toSPDZ₂_neg {q : ℕ} (s₁ s₂ : PartyAuthShare (ZMod q)) :
    toSPDZ₂ (-s₁) (-s₂) = -(toSPDZ₂ s₁ s₂) := by
  ext i <;> [simp [toSPDZ₂]; fin_cases i <;> rfl; fin_cases i <;> rfl]

private theorem toSPDZ₁_sub {q : ℕ} (s₁ s₁' s₂ s₂' : PartyAuthShare (ZMod q)) :
    toSPDZ₁ (s₁ - s₁') (s₂ - s₂') = toSPDZ₁ s₁ s₂ - toSPDZ₁ s₁' s₂' := by
  ext i <;> [simp [toSPDZ₁]; fin_cases i <;> rfl; fin_cases i <;> rfl]

private theorem toSPDZ₂_sub {q : ℕ} (s₁ s₁' s₂ s₂' : PartyAuthShare (ZMod q)) :
    toSPDZ₂ (s₁ - s₁') (s₂ - s₂') = toSPDZ₂ s₁ s₂ - toSPDZ₂ s₁' s₂' := by
  ext i <;> [simp [toSPDZ₂]; fin_cases i <;> rfl; fin_cases i <;> rfl]

private theorem toSPDZ₁_smul {q : ℕ} (c : ZMod q) (s₁ s₂ : PartyAuthShare (ZMod q)) :
    toSPDZ₁ (c • s₁) (c • s₂) = c • toSPDZ₁ s₁ s₂ := by
  ext i <;> [simp [toSPDZ₁]; fin_cases i <;> rfl; fin_cases i <;> rfl]

private theorem toSPDZ₂_smul {q : ℕ} (c : ZMod q) (s₁ s₂ : PartyAuthShare (ZMod q)) :
    toSPDZ₂ (c • s₁) (c • s₂) = c • toSPDZ₂ s₁ s₂ := by
  ext i <;> [simp [toSPDZ₂]; fin_cases i <;> rfl; fin_cases i <;> rfl]

/-- `Valid α β` is preserved under share addition, via `SPDZ.AuthShare.Valid.add`. -/
theorem Valid.add {q : ℕ} {α β : ZMod q} {s₁ s₁' s₂ s₂' : PartyAuthShare (ZMod q)}
    (h : Valid α β s₁ s₂) (h' : Valid α β s₁' s₂') :
    Valid α β (s₁ + s₁') (s₂ + s₂') := by
  rw [valid_iff_spdz] at h h' ⊢
  rw [toSPDZ₁_add, toSPDZ₂_add]
  exact ⟨h.1.add h'.1, h.2.add h'.2⟩

/-- `Valid α β` is preserved under share negation, via `SPDZ.AuthShare.Valid.neg`. -/
theorem Valid.neg {q : ℕ} {α β : ZMod q} {s₁ s₂ : PartyAuthShare (ZMod q)}
    (h : Valid α β s₁ s₂) :
    Valid α β (-s₁) (-s₂) := by
  rw [valid_iff_spdz] at h ⊢
  rw [toSPDZ₁_neg, toSPDZ₂_neg]
  exact ⟨h.1.neg, h.2.neg⟩

/-- `Valid α β` is preserved under share subtraction, via `SPDZ.AuthShare.Valid.sub`. -/
theorem Valid.sub {q : ℕ} {α β : ZMod q} {s₁ s₁' s₂ s₂' : PartyAuthShare (ZMod q)}
    (h : Valid α β s₁ s₂) (h' : Valid α β s₁' s₂') :
    Valid α β (s₁ - s₁') (s₂ - s₂') := by
  rw [valid_iff_spdz] at h h' ⊢
  rw [toSPDZ₁_sub, toSPDZ₂_sub]
  exact ⟨h.1.sub h'.1, h.2.sub h'.2⟩

/-- `Valid α β` is preserved under public scalar multiplication, via `SPDZ.AuthShare.Valid.smul`.
-/
theorem Valid.smul {q : ℕ} {α β : ZMod q} (c : ZMod q) {s₁ s₂ : PartyAuthShare (ZMod q)}
    (h : Valid α β s₁ s₂) :
    Valid α β (c • s₁) (c • s₂) := by
  rw [valid_iff_spdz] at h ⊢
  rw [toSPDZ₁_smul, toSPDZ₂_smul]
  exact ⟨h.1.smul c, h.2.smul c⟩

/-- `Valid α β` is preserved under local public constant addition `(addConstP1, addConstP2)`. -/
theorem Valid.addConst {R : Type} [CommRing R] {α β : R} (c : R) {s₁ s₂ : PartyAuthShare R}
    (h : Valid α β s₁ s₂) :
    Valid α β (addConstP1 c α s₁) (addConstP2 c β s₂) := by
  refine ⟨?_, ?_⟩ <;> simp only [addConstP1, addConstP2]
  · linear_combination h.1
  · linear_combination h.2

/-- `Valid α β` is preserved by authenticated online Beaver multiplication
`(mulOnlineP1, mulOnlineP2)` for arbitrary candidate public openings `d, e`. -/
theorem Valid.mulOnline {q : ℕ} {α β : ZMod q}
    {a₁ a₂ b₁ b₂ c₁ c₂ : PartyAuthShare (ZMod q)} (d e : ZMod q)
    (ha : Valid α β a₁ a₂) (hb : Valid α β b₁ b₂) (hc : Valid α β c₁ c₂) :
    Valid α β (mulOnlineP1 α d e a₁ b₁ c₁) (mulOnlineP2 β d e a₂ b₂ c₂) :=
  Valid.addConst (d * e) (((Valid.smul e ha).add (Valid.smul d hb)).add hc)

/-- `P₁`'s value share from `mulOnlineP1` agrees with `Beaver.beaverMulShare 0`. -/
theorem val_mulOnlineP1_eq_beaverMulShare {R : Type} [CommRing R]
    (α d e : R) (a₁ b₁ c₁ : PartyAuthShare R) :
    (mulOnlineP1 α d e a₁ b₁ c₁).val =
      beaverMulShare (m := 2) 0 (d, e) ⟨a₁.val, b₁.val, c₁.val⟩ := by
  change (e * a₁.val + d * b₁.val) + c₁.val + d * e =
    (if (0 : Fin 2).val = 0 then d * e else 0) + d * b₁.val + e * a₁.val + c₁.val
  simp only [Fin.val_zero, ↓reduceIte]
  ring

/-- `P₂`'s value share from `mulOnlineP2` agrees with `Beaver.beaverMulShare 1`. -/
theorem val_mulOnlineP2_eq_beaverMulShare {R : Type} [CommRing R]
    (β d e : R) (a₂ b₂ c₂ : PartyAuthShare R) :
    (mulOnlineP2 β d e a₂ b₂ c₂).val =
      beaverMulShare (m := 2) 1 (d, e) ⟨a₂.val, b₂.val, c₂.val⟩ := by
  change (e * a₂.val + d * b₂.val) + c₂.val =
    (if (1 : Fin 2).val = 0 then d * e else 0) + d * b₂.val + e * a₂.val + c₂.val
  simp only [Fin.val_one, one_ne_zero, ↓reduceIte, zero_add]
  ring

/-- Reconstructed product of `mulOnlineP1` and `mulOnlineP2` equals `(x₁ + x₂) * (y₁ + y₂)` when
`d = (x₁ + x₂) - (a₁ + a₂)`, `e = (y₁ + y₂) - (b₁ + b₂)`, and
`c₁ + c₂ = (a₁ + a₂) * (b₁ + b₂)`. -/
theorem val_add_mulOnline_eq_mul {R : Type} [CommRing R]
    {α β d e : R} (x₁ x₂ y₁ y₂ a₁ a₂ b₁ b₂ c₁ c₂ : PartyAuthShare R)
    (hd : d = (x₁.val + x₂.val) - (a₁.val + a₂.val))
    (he : e = (y₁.val + y₂.val) - (b₁.val + b₂.val))
    (hc : c₁.val + c₂.val = (a₁.val + a₂.val) * (b₁.val + b₂.val)) :
    (mulOnlineP1 α d e a₁ b₁ c₁).val + (mulOnlineP2 β d e a₂ b₂ c₂).val =
      (x₁.val + x₂.val) * (y₁.val + y₂.val) := by
  let xy : Fin 2 → R × R := ![(x₁.val, y₁.val), (x₂.val, y₂.val)]
  let tr : Fin 2 → TripleShare R := ![⟨a₁.val, b₁.val, c₁.val⟩, ⟨a₂.val, b₂.val, c₂.val⟩]
  have hop : (∑ j : Fin 2, localMaskedOpening (xy j) (tr j)) = (d, e) := by
    ext
    · simp only [Fin.sum_univ_two, localMaskedOpening, xy, tr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Prod.fst_add]
      rw [hd]
      ring
    · simp only [Fin.sum_univ_two, localMaskedOpening, xy, tr,
        Matrix.cons_val_zero, Matrix.cons_val_one, Prod.snd_add]
      rw [he]
      ring
  have hsum :
      (∑ i : Fin 2, beaverMulShare i (d, e) (tr i)) =
        (x₁.val + x₂.val) * (y₁.val + y₂.val) := by
    rw [← hop]
    have hmul := sum_beaverMulShare_eq_mul xy tr (by
      simpa [Fin.sum_univ_two, tr, Matrix.cons_val_zero, Matrix.cons_val_one] using hc)
    simpa [Fin.sum_univ_two, xy, Matrix.cons_val_zero, Matrix.cons_val_one] using hmul
  rw [val_mulOnlineP1_eq_beaverMulShare, val_mulOnlineP2_eq_beaverMulShare]
  simpa [Fin.sum_univ_two, tr, Matrix.cons_val_zero, Matrix.cons_val_one] using hsum

end PartyAuthShare

/-! ### Single-element opening verification and `1 / q` MAC forgery bound -/

/-- Verification check for opening a two-party authenticated share: given verifier's MAC key `key`,
verifier's share `(honestVal, honestMac)`, and prover's claimed opening `(claimedVal, claimedMac)`,
accepts iff `claimedMac + honestMac = key * (claimedVal + honestVal)`
([BonehShoup2023], §23.2.4.1). -/
@[expose] def verifyOpening {R : Type} [Mul R] [Add R]
    (key honestVal honestMac claimedVal claimedMac : R) : Prop :=
  claimedMac + honestMac = key * (claimedVal + honestVal)

instance {R : Type} [Mul R] [Add R] [DecidableEq R]
    (key honestVal honestMac claimedVal claimedMac : R) :
    Decidable (verifyOpening key honestVal honestMac claimedVal claimedMac) :=
  inferInstanceAs (Decidable (_ = _))

/-- Bridge theorem: `verifyOpening` is equivalent to `VOLE.voleVerifyOpening` at receiver key
`-key` and adjusted verifier tag `key * honestVal - honestMac`. -/
theorem verifyOpening_iff_voleVerifyOpening {R : Type} [CommRing R]
    (key honestVal honestMac claimedVal claimedMac : R) :
    verifyOpening key honestVal honestMac claimedVal claimedMac ↔
      voleVerifyOpening (fun _ : Fin 1 => key * honestVal - honestMac) (-key)
        (fun _ => claimedVal) (fun _ => claimedMac) := by
  simp only [verifyOpening, voleVerifyOpening, Fin.forall_fin_one]
  constructor <;> intro h <;> linear_combination -h

/-- **Single-element MAC forgery bound (`1 / q`)**: fixing the true share `(trueVal, trueMac)`,
the verifier's value share `honestVal`, and any forged opening `claimedVal ≠ trueVal` with
`claimedMac`, over a uniformly random verifier key `key : ZMod q` (for prime `q`) with consistent
verifier tag `honestMac = key * (trueVal + honestVal) - trueMac`, `verifyOpening` accepts with
probability at most `1 / q` (proved directly via `VOLE.toOuterMeasure_voleVerifyOpening_le`). -/
theorem toOuterMeasure_verifyOpening_le {q : ℕ} [Fact (Nat.Prime q)]
    {trueVal trueMac honestVal claimedVal claimedMac : ZMod q}
    (hne : claimedVal ≠ trueVal) :
    (PMF.uniformOfFintype (ZMod q)).toOuterMeasure
      { key : ZMod q |
        verifyOpening key honestVal (key * (trueVal + honestVal) - trueMac)
          claimedVal claimedMac } ≤
      (q : ℝ≥0∞)⁻¹ := by
  have hset :
      { key : ZMod q |
        verifyOpening key honestVal (key * (trueVal + honestVal) - trueMac)
          claimedVal claimedMac } =
      (Equiv.neg (ZMod q)) ⁻¹'
        { d : ZMod q | ∀ _ : Fin 1, trueVal * d + trueMac = claimedVal * d + claimedMac } := by
    ext key
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Equiv.neg_apply, verifyOpening,
      Fin.forall_fin_one]
    constructor <;> intro h <;> linear_combination -h
  rw [hset, ← PMF.toOuterMeasure_map_apply,
    PMF.uniformOfFintype_map_equiv (Equiv.neg (ZMod q))]
  have hneFun : (fun _ : Fin 1 => claimedVal) ≠ (fun _ : Fin 1 => trueVal) :=
    fun h => hne (congrFun h 0)
  simpa [ZMod.card] using
    (toOuterMeasure_voleVerifyOpening_le (F := ZMod q)
      (x := fun _ : Fin 1 => trueVal) (v := fun _ : Fin 1 => trueMac)
      (x' := fun _ : Fin 1 => claimedVal) (v' := fun _ : Fin 1 => claimedMac) hneFun)

/-! ### Authenticated Beaver triples and 7-relation reduction (`m = 7`) -/

/-- One party's shares `(a, b, c)` of a two-party authenticated Beaver triple over `R`. -/
@[ext] structure PartyAuthTriple (R : Type) where
  /-- Authenticated share of `a`. -/
  a : PartyAuthShare R
  /-- Authenticated share of `b`. -/
  b : PartyAuthShare R
  /-- Authenticated share of `c` (intended to satisfy `a * b = c`). -/
  c : PartyAuthShare R
  deriving DecidableEq, Fintype, Inhabited, Repr

namespace PartyAuthTriple

/-- Validity of a two-party authenticated Beaver triple `(tr₁, tr₂)` under `P₁`'s MAC key `α` and
`P₂`'s MAC key `β`: `(a₁ + a₂) * (b₁ + b₂) = c₁ + c₂` and all three shares `a, b, c` satisfy
`PartyAuthShare.Valid α β`. -/
@[expose] def Valid {R : Type} [CommRing R] (α β : R) (tr₁ tr₂ : PartyAuthTriple R) : Prop :=
  (tr₁.a.val + tr₂.a.val) * (tr₁.b.val + tr₂.b.val) = tr₁.c.val + tr₂.c.val ∧
    PartyAuthShare.Valid α β tr₁.a tr₂.a ∧
    PartyAuthShare.Valid α β tr₁.b tr₂.b ∧
    PartyAuthShare.Valid α β tr₁.c tr₂.c

instance {R : Type} [CommRing R] [DecidableEq R] (α β : R) (tr₁ tr₂ : PartyAuthTriple R) :
    Decidable (Valid α β tr₁ tr₂) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- Authenticated Beaver online multiplication closure on a valid `PartyAuthTriple`: given
`(tr₁, tr₂)` valid under `(α, β)` and openings `d = (x₁ + x₂) - (a₁ + a₂)`,
`e = (y₁ + y₂) - (b₁ + b₂)`, the local outputs `(z₁, z₂)` form a valid `PartyAuthShare` of
`(x₁ + x₂) * (y₁ + y₂)`. -/
theorem mulOnline_valid_and_eq_mul {q : ℕ} {α β d e : ZMod q}
    {tr₁ tr₂ : PartyAuthTriple (ZMod q)} (htr : Valid α β tr₁ tr₂)
    (x₁ x₂ y₁ y₂ : PartyAuthShare (ZMod q))
    (hd : d = (x₁.val + x₂.val) - (tr₁.a.val + tr₂.a.val))
    (he : e = (y₁.val + y₂.val) - (tr₁.b.val + tr₂.b.val)) :
    let z₁ := PartyAuthShare.mulOnlineP1 α d e tr₁.a tr₁.b tr₁.c
    let z₂ := PartyAuthShare.mulOnlineP2 β d e tr₂.a tr₂.b tr₂.c
    PartyAuthShare.Valid α β z₁ z₂ ∧
      z₁.val + z₂.val = (x₁.val + x₂.val) * (y₁.val + y₂.val) :=
  ⟨PartyAuthShare.Valid.mulOnline d e htr.2.1 htr.2.2.1 htr.2.2.2,
   PartyAuthShare.val_add_mulOnline_eq_mul x₁ x₂ y₁ y₂ tr₁.a tr₂.a tr₁.b tr₂.b tr₁.c tr₂.c
     hd he htr.1.symm⟩

end PartyAuthTriple

/-- Pack `P₁`'s MAC key `α` and authenticated triple share `tr₁` into `Fin 7 → TripleShare R`
([BonehShoup2023], §23.2.4.8):
* index `0`: `(a₁, b₁, c₁)` for `a * b = c`
* indices `1, 2, 3`: `(α, a₁, t_{a1})`, `(α, b₁, t_{b1})`, `(α, c₁, t_{c1})`
* indices `4, 5, 6`: `(0, a₁, u_{a1})`, `(0, b₁, u_{b1})`, `(0, c₁, u_{c1})` -/
@[expose] def toTripleShares₁ {R : Type} [Zero R] (α : R) (tr₁ : PartyAuthTriple R) :
    Fin 7 → TripleShare R
  | ⟨0, _⟩ => ⟨tr₁.a.val, tr₁.b.val, tr₁.c.val⟩
  | ⟨1, _⟩ => ⟨α, tr₁.a.val, tr₁.a.mac1⟩
  | ⟨2, _⟩ => ⟨α, tr₁.b.val, tr₁.b.mac1⟩
  | ⟨3, _⟩ => ⟨α, tr₁.c.val, tr₁.c.mac1⟩
  | ⟨4, _⟩ => ⟨0, tr₁.a.val, tr₁.a.mac2⟩
  | ⟨5, _⟩ => ⟨0, tr₁.b.val, tr₁.b.mac2⟩
  | ⟨6, _⟩ => ⟨0, tr₁.c.val, tr₁.c.mac2⟩

/-- Pack `P₂`'s MAC key `β` and authenticated triple share `tr₂` into `Fin 7 → TripleShare R`
([BonehShoup2023], §23.2.4.8):
* index `0`: `(a₂, b₂, c₂)` for `a * b = c`
* indices `1, 2, 3`: `(0, a₂, t_{a2})`, `(0, b₂, t_{b2})`, `(0, c₂, t_{c2})`
* indices `4, 5, 6`: `(β, a₂, u_{a2})`, `(β, b₂, u_{b2})`, `(β, c₂, u_{c2})` -/
@[expose] def toTripleShares₂ {R : Type} [Zero R] (β : R) (tr₂ : PartyAuthTriple R) :
    Fin 7 → TripleShare R
  | ⟨0, _⟩ => ⟨tr₂.a.val, tr₂.b.val, tr₂.c.val⟩
  | ⟨1, _⟩ => ⟨0, tr₂.a.val, tr₂.a.mac1⟩
  | ⟨2, _⟩ => ⟨0, tr₂.b.val, tr₂.b.mac1⟩
  | ⟨3, _⟩ => ⟨0, tr₂.c.val, tr₂.c.mac1⟩
  | ⟨4, _⟩ => ⟨β, tr₂.a.val, tr₂.a.mac2⟩
  | ⟨5, _⟩ => ⟨β, tr₂.b.val, tr₂.b.mac2⟩
  | ⟨6, _⟩ => ⟨β, tr₂.c.val, tr₂.c.mac2⟩

/-- Extract a party's `PartyAuthTriple` from a `Fin 7 → TripleShare R` tuple by reading `(a, b, c)`
from index `0`, `mac1` tags from `(1..3).c`, and `mac2` tags from `(4..6).c`. -/
@[expose] def extractTriple {R : Type} (t : Fin 7 → TripleShare R) : PartyAuthTriple R where
  a := ⟨(t 0).a, (t 1).c, (t 4).c⟩
  b := ⟨(t 0).b, (t 2).c, (t 5).c⟩
  c := ⟨(t 0).c, (t 3).c, (t 6).c⟩

@[simp] theorem extractTriple_toTripleShares₁ {R : Type} [Zero R]
    (α : R) (tr₁ : PartyAuthTriple R) :
    extractTriple (toTripleShares₁ α tr₁) = tr₁ := by
  ext <;> rfl

@[simp] theorem extractTriple_toTripleShares₂ {R : Type} [Zero R]
    (β : R) (tr₂ : PartyAuthTriple R) :
    extractTriple (toTripleShares₂ β tr₂) = tr₂ := by
  ext <;> rfl

/-- **Exact 7-relation reduction equivalence** ([BonehShoup2023], §23.2.4.8):
`ProductRelations (toTripleShares₁ α tr₁) (toTripleShares₂ β tr₂)` holds over `ZMod q` if and
only if `(tr₁, tr₂)` is a valid authenticated Beaver triple under `(α, β)`. -/
theorem productRelations_toTripleShares_iff {q : ℕ} (α β : ZMod q)
    (tr₁ tr₂ : PartyAuthTriple (ZMod q)) :
    ProductRelations (toTripleShares₁ α tr₁) (toTripleShares₂ β tr₂) ↔
      PartyAuthTriple.Valid α β tr₁ tr₂ := by
  constructor
  · intro h
    refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · simpa [toTripleShares₁, toTripleShares₂] using h 0
    · simpa [toTripleShares₁, toTripleShares₂] using (h 1).symm
    · simpa [toTripleShares₁, toTripleShares₂] using (h 4).symm
    · simpa [toTripleShares₁, toTripleShares₂] using (h 2).symm
    · simpa [toTripleShares₁, toTripleShares₂] using (h 5).symm
    · simpa [toTripleShares₁, toTripleShares₂] using (h 3).symm
    · simpa [toTripleShares₁, toTripleShares₂] using (h 6).symm
  · rintro ⟨h0, ⟨h1, h4⟩, ⟨h2, h5⟩, ⟨h3, h6⟩⟩ k
    fin_cases k <;> simp only [toTripleShares₁, toTripleShares₂, add_zero, zero_add]
    · exact h0
    · exact h1.symm
    · exact h2.symm
    · exact h3.symm
    · exact h4.symm
    · exact h5.symm
    · exact h6.symm

/-! ### Completeness, corrupt-dealer soundness (`14 / (q - 8)`), and corrupt-party privacy -/

/-- Honest party verification for authenticated Beaver-triple checking in Protocol 23.5 (`m = 7`)
with MAC keys `(α, β)`: each party extracts its candidate triple from `d_i.triples`, checks that
`d_i.triples` matches `toTripleShares₁ α` / `toTripleShares₂ β`, and otherwise aborts immediately;
when both local consistency checks pass, the parties run `honestPartiesRun q 7 hq d₁ d₂`. -/
@[expose] noncomputable def honestAuthPartiesRun (q : ℕ) [Fact (Nat.Prime q)] (hq : 14 < q)
    (α β : ZMod q) (d₁ d₂ : PartyDeal q 7) : ProbComp (Bool × Bool) :=
  if d₁.triples = toTripleShares₁ α (extractTriple d₁.triples) ∧
     d₂.triples = toTripleShares₂ β (extractTriple d₂.triples) then
    honestPartiesRun q 7 hq d₁ d₂
  else
    return (false, false)

/-- Full honest execution of the authenticated Beaver-triple check on `(α, β, tr₁, tr₂)`:
honest dealer `deal` on `(toTripleShares₁ α tr₁, toTripleShares₂ β tr₂)` followed by
`honestAuthPartiesRun`. -/
@[expose] noncomputable def checkAuthTriple (q : ℕ) [Fact (Nat.Prime q)] (hq : 14 < q)
    (α β : ZMod q) (tr₁ tr₂ : PartyAuthTriple (ZMod q)) : ProbComp (Bool × Bool) := do
  let dd ← deal (toTripleShares₁ α tr₁) (toTripleShares₂ β tr₂)
  honestAuthPartiesRun q hq α β dd.1 dd.2

/-- **Completeness (`= 1`)**: when `q > 14` is prime and `(tr₁, tr₂)` is a valid authenticated
Beaver triple under `(α, β)`, `checkAuthTriple` accepts for both parties with probability `1`. -/
theorem eval_checkAuthTriple_eq_pure {q : ℕ} [Fact (Nat.Prime q)] (hq : 14 < q)
    {α β : ZMod q} {tr₁ tr₂ : PartyAuthTriple (ZMod q)}
    (hvalid : PartyAuthTriple.Valid α β tr₁ tr₂) :
    ProbComp.eval (checkAuthTriple q hq α β tr₁ tr₂) = PMF.pure (true, true) := by
  let t₁ := toTripleShares₁ α tr₁
  let t₂ := toTripleShares₂ β tr₂
  have hrel : ProductRelations t₁ t₂ :=
    (productRelations_toTripleShares_iff α β tr₁ tr₂).mpr hvalid
  have hred :
      ProbComp.eval (checkAuthTriple q hq α β tr₁ tr₂) =
        ProbComp.eval (do
          let dd ← deal t₁ t₂
          honestPartiesRun q 7 hq dd.1 dd.2) := by
    simp only [checkAuthTriple, ProbComp.eval_bind]
    refine PMF.bind_congr_on_support _ _ _ fun dd hdd => ?_
    simp only [deal, ProbComp.eval_bind, ProbComp.eval_pure, PMF.mem_support_bind_iff,
      PMF.mem_support_pure_iff] at hdd
    rcases hdd with ⟨e₁, _, a02, _, b02, _, hdd'⟩
    rcases hdd'.symm with rfl
    have hcons :
        (e₁.toDeal t₁).triples = toTripleShares₁ α (extractTriple (e₁.toDeal t₁).triples) ∧
        ((honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂).triples =
          toTripleShares₂ β (extractTriple ((honestC2 t₁ t₂ e₁ a02 b02).toDeal t₂).triples) := by
      simp [t₁, t₂]
    dsimp only [t₁, t₂] at hcons
    dsimp only [honestAuthPartiesRun]
    split_ifs
    rfl
  rw [hred]
  exact eval_honestProtocol_eq_pure hq hrel

/-- **Corrupt-dealer soundness (`14 / (q - 8)`)**: for prime `q > 14` and arbitrary corrupt dealer
messages `(d₁, d₂) : PartyDeal q 7 × PartyDeal q 7`, if the extracted triple fails
`PartyAuthTriple.Valid α β`, then either `P₁` or `P₂` finishes without aborting with probability
at most `14 / (q - 8)` (from `ProductRelation.eval_honestPartiesRun_accept_le` at `m = 7`). -/
theorem eval_honestAuthPartiesRun_accept_le {q : ℕ} [Fact (Nat.Prime q)] (hq : 14 < q)
    {α β : ZMod q} {d₁ d₂ : PartyDeal q 7}
    (hnot : ¬ PartyAuthTriple.Valid α β (extractTriple d₁.triples) (extractTriple d₂.triples)) :
    (ProbComp.eval (honestAuthPartiesRun q hq α β d₁ d₂)).toOuterMeasure
        { res : Bool × Bool | res.1 = true ∨ res.2 = true } ≤
      (14 : ℝ≥0∞) / ((q - 8 : ℕ) : ℝ≥0∞) := by
  dsimp only [honestAuthPartiesRun]
  split_ifs with hcons
  · have hnotRel : ¬ ProductRelations d₁.triples d₂.triples := by
      rw [hcons.1, hcons.2, productRelations_toTripleShares_iff]
      exact hnot
    have hbound := eval_honestPartiesRun_accept_le (m := 7) hq hnotRel
    rw [show (2 * ((7 : ℕ) : ℝ≥0∞)) = 14 by norm_num, show q - 7 - 1 = q - 8 by omega] at hbound
    exact hbound
  · rw [ProbComp.eval_pure, PMF.toOuterMeasure_pure_apply]
    split_ifs with hmem
    · exfalso; simp at hmem
    · exact zero_le

/-- A two-party authenticated Beaver-triple instance `(α, β, tr₁, tr₂)`. -/
@[ext] structure AuthTripleInstance (R : Type) where
  /-- `P₁`'s secret MAC key `α`. -/
  key1 : R
  /-- `P₂`'s secret MAC key `β`. -/
  key2 : R
  /-- `P₁`'s shares of the authenticated Beaver triple `(a, b, c)`. -/
  triple1 : PartyAuthTriple R
  /-- `P₂`'s shares of the authenticated Beaver triple `(a, b, c)`. -/
  triple2 : PartyAuthTriple R
  deriving DecidableEq, Inhabited, Repr

/-- Validity of `inst : AuthTripleInstance R`. -/
@[expose] def AuthTripleInstance.Valid {R : Type} [CommRing R] (inst : AuthTripleInstance R) :
    Prop :=
  PartyAuthTriple.Valid inst.key1 inst.key2 inst.triple1 inst.triple2

instance {R : Type} [CommRing R] [DecidableEq R] (inst : AuthTripleInstance R) :
    Decidable inst.Valid :=
  inferInstanceAs (Decidable (PartyAuthTriple.Valid inst.key1 inst.key2 inst.triple1 inst.triple2))

/-- Interactive adversary corrupting `P₁` in the 7-relation authenticated-triple check. -/
structure AuthCorruptP1Adversary (q : ℕ) (σ : Type) where
  /-- Samples `(inst, st)`. Privacy requires `inst.Valid` on the support. -/
  chooseInputs : ProbComp (AuthTripleInstance (ZMod q) × σ)
  /-- Chooses challenge `r` after observing `P₁`'s Step 1 deal `d₁`. -/
  chooseChallenge : σ → PartyDeal q 7 → ProbComp (ZMod q × σ)
  /-- Chooses `P₁`'s evaluation opening after receiving honest `P₂`'s evaluation `(α₂, β₂, γ₂)`. -/
  sendOpening : σ → ZMod q × ZMod q × ZMod q → ProbComp ((ZMod q × ZMod q × ZMod q) × σ)
  /-- Outputs final Boolean bit after observing `P₂`'s abort/accept status. -/
  finish : σ → Option Bool → ProbComp Bool

/-- Embed `AuthCorruptP1Adversary q σ` into `CorruptP1Adversary q 7 σ` via `toTripleShares₁` and
`toTripleShares₂`. In the resulting simulated experiment `experiment1P1`, `S_D^(1)` sees only
`toTripleShares₁ inst.key1 inst.triple1` and ignores `inst.key2` and `inst.triple2`. -/
@[expose] def AuthCorruptP1Adversary.toProductAdversary {q : ℕ} {σ : Type}
    (A : AuthCorruptP1Adversary q σ) : CorruptP1Adversary q 7 σ where
  chooseInputs := do
    let (inst, st) ← A.chooseInputs
    return (toTripleShares₁ inst.key1 inst.triple1, toTripleShares₂ inst.key2 inst.triple2, st)
  chooseChallenge := A.chooseChallenge
  sendOpening := A.sendOpening
  finish := A.finish

/-- **Corrupt-`P₁` exact simulation privacy** (from Fact 23.2 in
`ProductRelation.eval_experiment0P1_eq_experiment1P1`): when `q > 14` is prime and every instance in
the support of `A.chooseInputs` satisfies `AuthTripleInstance.Valid`, the real and simulated
experiments induce identical output distributions on `Bool`. -/
theorem eval_authExperiment0P1_eq_experiment1P1 {q : ℕ} [Fact (Nat.Prime q)] (hq : 14 < q)
    {σ : Type} (A : AuthCorruptP1Adversary q σ)
    (hvalid : ∀ inst st, (inst, st) ∈ (ProbComp.eval A.chooseInputs).support → inst.Valid) :
    ProbComp.eval (experiment0P1 q 7 A.toProductAdversary) =
      ProbComp.eval (experiment1P1 q 7 A.toProductAdversary) := by
  refine eval_experiment0P1_eq_experiment1P1 (m := 7) hq A.toProductAdversary ?_
  intro t₁ t₂ st hx
  simp only [AuthCorruptP1Adversary.toProductAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx
  rcases hx with ⟨⟨inst, st'⟩, hinst, rfl, rfl, rfl⟩
  exact (productRelations_toTripleShares_iff inst.key1 inst.key2 inst.triple1 inst.triple2).mpr
    (hvalid inst st hinst)

/-- Interactive adversary corrupting `P₂` in the 7-relation authenticated-triple check. -/
structure AuthCorruptP2Adversary (q : ℕ) (σ : Type) where
  /-- Samples `(inst, st)`. Privacy requires `inst.Valid` on the support. -/
  chooseInputs : ProbComp (AuthTripleInstance (ZMod q) × σ)
  /-- Chooses `P₂`'s evaluation opening after receiving `d₂`, `r`, and `P₁`'s evaluation
  `(α₁, β₁, γ₁)`. -/
  sendOpening :
    σ → PartyDeal q 7 → ZMod q → ZMod q × ZMod q × ZMod q →
      ProbComp ((ZMod q × ZMod q × ZMod q) × σ)
  /-- Outputs final Boolean bit after observing `P₁`'s acceptance decision. -/
  finish : σ → Bool → ProbComp Bool

/-- Embed `AuthCorruptP2Adversary q σ` into `CorruptP2Adversary q 7 σ` via `toTripleShares₁` and
`toTripleShares₂`. In the resulting simulated experiment `experiment1P2`, `S_D^(2)` sees only
`toTripleShares₂ inst.key2 inst.triple2` and ignores `inst.key1` and `inst.triple1`. -/
@[expose] def AuthCorruptP2Adversary.toProductAdversary {q : ℕ} {σ : Type}
    (A : AuthCorruptP2Adversary q σ) : CorruptP2Adversary q 7 σ where
  chooseInputs := do
    let (inst, st) ← A.chooseInputs
    return (toTripleShares₁ inst.key1 inst.triple1, toTripleShares₂ inst.key2 inst.triple2, st)
  sendOpening := A.sendOpening
  finish := A.finish

/-- **Corrupt-`P₂` exact simulation privacy** (from Fact 23.2 in
`ProductRelation.eval_experiment0P2_eq_experiment1P2`): when `q > 14` is prime and every instance in
the support of `A.chooseInputs` satisfies `AuthTripleInstance.Valid`, the real and simulated
experiments induce identical output distributions on `Bool`. -/
theorem eval_authExperiment0P2_eq_experiment1P2 {q : ℕ} [Fact (Nat.Prime q)] (hq : 14 < q)
    {σ : Type} (A : AuthCorruptP2Adversary q σ)
    (hvalid : ∀ inst st, (inst, st) ∈ (ProbComp.eval A.chooseInputs).support → inst.Valid) :
    ProbComp.eval (experiment0P2 q 7 hq A.toProductAdversary) =
      ProbComp.eval (experiment1P2 q 7 hq A.toProductAdversary) := by
  refine eval_experiment0P2_eq_experiment1P2 (m := 7) hq A.toProductAdversary ?_
  intro t₁ t₂ st hx
  simp only [AuthCorruptP2Adversary.toProductAdversary, ProbComp.eval_bind, ProbComp.eval_pure,
    PMF.mem_support_bind_iff, PMF.mem_support_pure_iff, Prod.mk.injEq] at hx
  rcases hx with ⟨⟨inst, st'⟩, hinst, rfl, rfl, rfl⟩
  exact (productRelations_toTripleShares_iff inst.key1 inst.key2 inst.triple1 inst.triple2).mpr
    (hvalid inst st hinst)

end Cslib.Crypto.Protocols.MPC.ProductRelation
