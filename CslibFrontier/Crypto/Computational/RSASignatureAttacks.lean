/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Gcd
public import CslibFrontier.Crypto.Computational.RSASignature
public import CslibFrontier.Crypto.Computational.RSAUnitInversion
public import CslibFrontier.Languages.Probabilistic.Oracle.QueryCount
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Crypto.Computational.RSAAttacks
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.UniformPoint

/-!
# Attacks on RSA signatures without a full-domain hash

Without a full-domain hash, RSA signatures are forgeable ([BonehShoup2023], Sections 13.3 and
13.6). Three forgers win Attack Game 13.1 (`Signature.Scheme.eufCmaExperiment`), each with an
exact success law and a bound on its signing queries:

* p. 536: against unhashed RSA signatures, `unhashedRSAExistentialForger` picks `σ` and outputs
  the message `σ ^ e % N` with the signature `σ`. It makes no query and wins with probability `1`.
* p. 537, equation (13.4): `unhashedRSAUniversalForger` signs any chosen message `m` with one
  query, by blinding: it asks for the signature on `m * r ^ e % N` and divides it by `r`. With the
  factor `N - 1` it wins with probability `1` on every message, for every key. For a unit `m` and
  any sampler of units it wins exactly when `r ≢ 1` modulo `N`; with the book's uniform unit it
  loses with probability exactly `1 / φ(N)`.
* p. 547, equation (13.9): `rsaMultiplicativeForger` asks for the signatures on `m₁` and `m₂` and
  outputs their product as a signature on `m₃`, when `H m₃ ≡ H m₁ * H m₂` modulo `N`.

The forgers carry query bounds, and the blinding and unblinding maps are certified polynomial
time (`computableInPolyTime_rsaBlind`, for a positive modulus, and
`computableInPolyTime_rsaUnblind`). No forger is certified as a polynomial-time program: the game
here is typed, the library has no polynomial-time predicate for typed oracle adversaries yet
(#4894), and the word-coded form of the forgers is not in this module.

Where the book is silent:

* Equation (13.4) holds for every unit `r`. For `r ≡ 1` the signing query is `m` itself, so the
  output is a valid signature that Attack Game 13.1 does not count; the book does not mention this
  case. With the book's uniform unit the forger loses on a message that is a unit with probability
  exactly `1 / φ(N)`.
* The book assumes that `m` is a unit and leaves the other case to the reader. Here the forger
  signs a non-unit itself with `rsaNonUnitRoot`, with no query; blinding does not work there.
* The book says "three messages" for (13.9) and does not state `m₃ ≠ m₁` and `m₃ ≠ m₂`. The game
  needs both; they follow from (13.9) when both digests are at least `2`. The product in (13.9)
  is over the integers; only the congruence modulo `N` is used.

The attack of p. 536 is stated there for any trapdoor permutation scheme; here it is stated for
RSA, as p. 537 restates it.

## Main definitions

* `Cslib.Crypto.rsaBlind`, `Cslib.Crypto.rsaUnblind`: blinding a message and unblinding its
  signature.
* `Cslib.Crypto.unhashedRSAExistentialForger`, `Cslib.Crypto.unhashedRSAUniversalForger`,
  `Cslib.Crypto.rsaMultiplicativeForger`: the forgers of pp. 536, 537 and 547.

## Main results

* `Cslib.Crypto.rsaEval_rsaUnblind`: equation (13.4).
* `Cslib.Crypto.eval_eufCmaExperiment_unhashedRSAExistentialForger`: forgery without a query.
* `Cslib.Crypto.eval_eufCmaExperiment_unhashedRSAUniversalForger_sub_one`: unhashed RSA
  signatures are universally forgeable with one query.
* `Cslib.Crypto.eval_eufCmaExperiment_unhashedRSAUniversalForger`,
  `Cslib.Crypto.eval_eufCmaExperiment_unhashedRSAUniversalForger_uniform`,
  `Cslib.Crypto.eval_eufCmaExperiment_unhashedRSAUniversalForger_of_not_coprime`: the law of the
  universal forger for a sampler of units, for the uniform unit, and on a non-unit.
* `Cslib.Crypto.eval_eufCmaExperiment_rsaMultiplicativeForger`: forgery from (13.9).

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023], Section 13.3,
  pp. 536–537, and Section 13.6, p. 547.
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

variable {M : Type}

/-! ### Blinding -/

/-- The blinded message `m * r ^ e % N` of the attack on unhashed RSA signatures. -/
@[expose]
def rsaBlind (N e m r : ℕ) : ℕ := m * rsaEval N e r % N

/-- Unblinding: `σ * r⁻¹ % N`, with the inverse of `r` modulo `N` computed by `BinaryGcd.modInv`. -/
@[expose]
def rsaUnblind (N r σ : ℕ) : ℕ := σ * BinaryGcd.modInv r N % N

/-- Equation (13.4): if `σ ^ e = m * r ^ e` modulo `N` and `r` is a unit, then
`(σ / r) ^ e = m` modulo `N`. -/
theorem rsaEval_rsaUnblind {N e m r σ : ℕ} (hN : 0 < N) (hr : Nat.Coprime r N)
    (hσ : rsaEval N e σ = rsaBlind N e m r) :
    rsaEval N e (rsaUnblind N r σ) = m % N := by
  have hinv : r * BinaryGcd.modInv r N ≡ 1 [MOD N] := BinaryGcd.mul_modInv_modEq_one hN hr
  have h1 : σ ^ e ≡ m * r ^ e [MOD N] := by
    have : σ ^ e % N = m * (r ^ e % N) % N := hσ
    calc σ ^ e ≡ m * (r ^ e % N) [MOD N] := this
      _ ≡ m * r ^ e [MOD N] := Nat.ModEq.mul_left _ (Nat.mod_modEq _ _)
  have h2 : (σ * BinaryGcd.modInv r N) ^ e ≡ m [MOD N] := by
    calc (σ * BinaryGcd.modInv r N) ^ e = σ ^ e * BinaryGcd.modInv r N ^ e := mul_pow _ _ _
      _ ≡ m * r ^ e * BinaryGcd.modInv r N ^ e [MOD N] := Nat.ModEq.mul_right _ h1
      _ = m * (r * BinaryGcd.modInv r N) ^ e := by rw [mul_pow, mul_assoc]
      _ ≡ m * 1 ^ e [MOD N] := Nat.ModEq.mul_left _ (hinv.pow e)
      _ = m := by rw [one_pow, mul_one]
  unfold rsaEval rsaUnblind
  rw [← Nat.pow_mod]
  exact h2

/-- The signature on the blinded message is `m ^ d * r` modulo `N`, the signature on `m` times
the blinding factor. -/
private theorem rsaInvert_rsaBlind (desc : RSADesc) (m r : ℕ) :
    rsaInvert desc.modulus desc.d (rsaBlind desc.modulus desc.e m r) =
      rsaInvert desc.modulus desc.d m * r % desc.modulus := by
  have h := rsaInvert_rsaEval_mul desc (rsaInvert desc.modulus desc.d m) r
  rwa [rsaEval_rsaInvert_mod, Nat.mod_mul_mod] at h

/-- A blinded message differs from the message exactly when the blinding factor moves its
signature: `m * r ^ e = m` modulo `N` iff `m ^ d * r = m ^ d` modulo `N`. -/
private theorem rsaBlind_eq_iff (desc : RSADesc) {m : ℕ} (hm : m < desc.modulus) (r : ℕ) :
    rsaBlind desc.modulus desc.e m r = m ↔
      rsaInvert desc.modulus desc.d m * r ≡ rsaInvert desc.modulus desc.d m [MOD desc.modulus] := by
  have hσ : rsaInvert desc.modulus desc.d m < desc.modulus := Nat.mod_lt _ desc.modulus_pos
  constructor
  · intro h
    have := congrArg (rsaInvert desc.modulus desc.d) h
    rw [rsaInvert_rsaBlind] at this
    exact this.trans (Nat.mod_eq_of_lt hσ).symm
  · intro h
    have h1 : rsaInvert desc.modulus desc.d (rsaBlind desc.modulus desc.e m r) =
        rsaInvert desc.modulus desc.d m := by
      rw [rsaInvert_rsaBlind]
      exact h.trans (Nat.mod_eq_of_lt hσ)
    have h2 := congrArg (rsaEval desc.modulus desc.e) h1
    have hlt : rsaBlind desc.modulus desc.e m r < desc.modulus := Nat.mod_lt _ desc.modulus_pos
    rwa [rsaEval_rsaInvert desc hlt, rsaEval_rsaInvert desc hm] at h2

/-- Blinding fixes a unit `m` exactly when `r = 1` modulo `N`. -/
private theorem rsaBlind_eq_iff_of_coprime (desc : RSADesc) {m : ℕ} (hm : m < desc.modulus)
    (hcop : Nat.Coprime m desc.modulus) (r : ℕ) :
    rsaBlind desc.modulus desc.e m r = m ↔ r ≡ 1 [MOD desc.modulus] := by
  have hσ : Nat.Coprime (rsaInvert desc.modulus desc.d m) desc.modulus :=
    (ZMod.coprime_mod_iff_coprime _ _).mpr (Nat.Coprime.pow_left _ hcop)
  rw [rsaBlind_eq_iff desc hm]
  refine ⟨fun h => Nat.ModEq.cancel_left_of_coprime hσ.symm (by simpa using h), fun h => ?_⟩
  simpa using h.mul_left (rsaInvert desc.modulus desc.d m)

/-! ### Existential forgery without a query (p. 536) -/

/-- The forger of [BonehShoup2023], p. 536, against unhashed RSA signatures: pick `σ` and output
the message `σ ^ e % N` with the signature `σ`. It makes no signing query. -/
def unhashedRSAExistentialForger (pk : RSAPublicKey) (pick : ProbComp (Fin pk.N)) :
    ProbOracleComp (fun _ : Fin pk.N => ℕ) (Fin pk.N × ℕ) := do
  let σ ← ProbOracleComp.sample pick
  return (pk.eval σ, (σ : ℕ))

theorem isQueryBounded_unhashedRSAExistentialForger (pk : RSAPublicKey)
    (pick : ProbComp (Fin pk.N)) :
    (unhashedRSAExistentialForger pk pick).IsQueryBounded 0 := by
  unfold unhashedRSAExistentialForger
  simpa using (ProbOracleComp.IsQueryBounded.sample (spec := fun _ : Fin pk.N => ℕ) pick).bind
    fun σ => OracleComp.IsCostBounded.pure (pk.eval σ, (σ : ℕ)) 0

/-- The forger of p. 536 wins Attack Game 13.1 against unhashed RSA signatures with
probability `1`, for every key and every way of picking `σ`. -/
theorem eval_eufCmaExperiment_unhashedRSAExistentialForger (desc : RSADesc)
    (pick : ProbComp (Fin desc.modulus)) :
    ProbComp.eval ((unhashedRSASignature desc).eufCmaExperiment
      fun _ => unhashedRSAExistentialForger desc.publicKey pick) = PMF.pure true := by
  have h (σ : Fin desc.modulus) : rsaEval desc.modulus desc.e σ =
      rsaEval desc.modulus desc.e σ % desc.modulus := (Nat.mod_mod _ _).symm
  have hmap : (ProbComp.eval pick).map (fun _ => true) = PMF.pure true := PMF.map_const _ _
  simp [forgeExperiment, ProbOracleComp.runLogWith, unhashedRSAExistentialForger, rsaSignature,
    freshMessage, ← h, hmap]

/-! ### Universal forgery with one query (p. 537, equation (13.4)) -/

/-- The forger of [BonehShoup2023], p. 537, against unhashed RSA signatures. To sign a unit `m`,
it picks `r`, asks for the signature `σ'` on the blinded message `m * r ^ e % N` and outputs
`σ' / r`: one signing query. A message that is not a unit it signs itself, with
`rsaNonUnitRoot`; this is the case the book leaves to the reader. -/
def unhashedRSAUniversalForger (pk : RSAPublicKey) (m : Fin pk.N) (pick : ProbComp ℕ) :
    ProbOracleComp (fun _ : Fin pk.N => ℕ) (Fin pk.N × ℕ) :=
  if Nat.Coprime m pk.N then do
    let r ← ProbOracleComp.sample pick
    let σ ← ProbOracleComp.query (spec := fun _ : Fin pk.N => ℕ)
      ⟨rsaBlind pk.N pk.e m r, Nat.mod_lt _ m.pos⟩
    return (m, rsaUnblind pk.N r σ)
  else return (m, rsaNonUnitRoot pk.N pk.e m)

theorem isQueryBounded_unhashedRSAUniversalForger (pk : RSAPublicKey) (m : Fin pk.N)
    (pick : ProbComp ℕ) : (unhashedRSAUniversalForger pk m pick).IsQueryBounded 1 := by
  unfold unhashedRSAUniversalForger
  split
  · simpa using (ProbOracleComp.IsQueryBounded.sample (spec := fun _ : Fin pk.N => ℕ) pick).bind
      fun r => (ProbOracleComp.IsQueryBounded.query (spec := fun _ : Fin pk.N => ℕ)
        (⟨rsaBlind pk.N pk.e m r, Nat.mod_lt _ m.pos⟩ : Fin pk.N)).bind
          fun σ => OracleComp.IsCostBounded.pure (m, rsaUnblind pk.N r σ) 0
  · exact OracleComp.IsCostBounded.pure _ 1

/-- **Universal forgery of unhashed RSA signatures** ([BonehShoup2023], p. 537, equation (13.4)):
on a unit `m`, when every `r` that `pick` returns is a unit modulo `N`, the forger's output always
verifies, and the blinded message differs from `m` unless `r = 1` modulo `N`: the forger wins
Attack Game 13.1 exactly when `pick` returns some `r ≠ 1` modulo `N`. -/
theorem eval_eufCmaExperiment_unhashedRSAUniversalForger (desc : RSADesc)
    {m : Fin desc.modulus} (hm : Nat.Coprime m desc.modulus) (pick : ProbComp ℕ)
    (hpick : ∀ r ∈ (ProbComp.eval pick).support, Nat.Coprime r desc.modulus) :
    ProbComp.eval ((unhashedRSASignature desc).eufCmaExperiment
      fun _ => unhashedRSAUniversalForger desc.publicKey m pick) =
      (ProbComp.eval pick).map fun r => decide (¬ r ≡ 1 [MOD desc.modulus]) := by
  simp only [forgeExperiment, ProbOracleComp.runLogWith, unhashedRSAUniversalForger,
    ite_eq_left hm, rsaSignature, freshMessage, bind_pure_comp, ProbOracleComp.runState_bind,
    ProbOracleComp.runState_sample, ProbOracleComp.runState_map, ProbOracleComp.runState_query,
    StateT.run_bind, StateT.run_lift, StateT.run_map, ProbOracleComp.logOracle_run,
    Signer.ofSign_apply, map_pure, Functor.map_map, List.nil_append, Bool.decide_and, List.mem_map,
    Prod.exists, exists_and_right, exists_eq_right, not_exists, decide_not, List.map_cons,
    List.map_nil, List.mem_cons, List.not_mem_nil, or_false, pure_bind, ProbComp.eval_map]
  refine PMF.map_congr_on_support _ _ _ fun r hr => ?_
  have hlt : rsaBlind desc.modulus desc.e m r < desc.modulus := Nat.mod_lt _ desc.modulus_pos
  have hv := rsaEval_rsaUnblind (m := m) desc.modulus_pos (hpick r hr) (rsaEval_rsaInvert desc hlt)
  have hfresh : m = (⟨rsaBlind desc.modulus desc.e m r, hlt⟩ : Fin desc.modulus) ↔
      rsaBlind desc.modulus desc.e m r = m := by rw [Fin.ext_iff, eq_comm]
  have hσ : rsaUnblind desc.modulus r
      (rsaInvert desc.modulus desc.d (rsaBlind desc.modulus desc.e m r)) < desc.modulus :=
    Nat.mod_lt _ desc.modulus_pos
  simp [hσ, hv, hfresh, rsaBlind_eq_iff_of_coprime desc m.isLt hm r]

/-- On a message that is not a unit modulo `N`, the forger of p. 537 makes no query and wins
Attack Game 13.1 with probability `1`. -/
theorem eval_eufCmaExperiment_unhashedRSAUniversalForger_of_not_coprime (desc : RSADesc)
    {m : Fin desc.modulus} (hm : ¬ Nat.Coprime m desc.modulus) (pick : ProbComp ℕ) :
    ProbComp.eval ((unhashedRSASignature desc).eufCmaExperiment
      fun _ => unhashedRSAUniversalForger desc.publicKey m pick) = PMF.pure true := by
  have hσ : rsaInvert desc.modulus desc.d m < desc.modulus := Nat.mod_lt _ desc.modulus_pos
  simp [forgeExperiment, ProbOracleComp.runLogWith, unhashedRSAUniversalForger, hm, rsaSignature,
    freshMessage, rsaNonUnitRoot_eq_rsaInvert desc m.isLt hm, rsaEval_rsaInvert desc m.isLt, hσ,
    Nat.mod_eq_of_lt m.isLt]

/-- **Universal forgery with a uniform blinding factor** ([BonehShoup2023], p. 537): on a message
that is a unit modulo `N`, the forger that draws `r` uniformly from the units loses Attack
Game 13.1 exactly when `r = 1`, so with probability `1 / φ(N)`. -/
theorem eval_eufCmaExperiment_unhashedRSAUniversalForger_uniform (desc : RSADesc)
    {m : Fin desc.modulus} (hm : Nat.Coprime m desc.modulus) :
    ProbComp.eval ((unhashedRSASignature desc).eufCmaExperiment fun _ =>
      unhashedRSAUniversalForger desc.publicKey m
        ((fun u => (desc.unitResidue u : ℕ)) <$> ProbComp.uniform (ZMod desc.modulus)ˣ)) false =
      (Nat.totient desc.modulus : ENNReal)⁻¹ := by
  have hpick : ∀ r ∈ (ProbComp.eval ((fun u => (desc.unitResidue u : ℕ)) <$>
      ProbComp.uniform (ZMod desc.modulus)ˣ)).support, Nat.Coprime r desc.modulus := by
    intro r hr
    simp only [ProbComp.eval_map, PMF.support_map, Set.mem_image] at hr
    obtain ⟨u, -, rfl⟩ := hr
    exact ZMod.val_coe_unit_coprime u
  have hfun : ((fun r : ℕ => decide (¬ r ≡ 1 [MOD desc.modulus])) ∘
      fun u : (ZMod desc.modulus)ˣ => (desc.unitResidue u : ℕ)) =
      (! ·) ∘ fun u => decide (u = 1) := by
    funext u
    have h : (desc.unitResidue u : ℕ) ≡ 1 [MOD desc.modulus] ↔ u = 1 := by
      rw [← ZMod.natCast_eq_natCast_iff]
      simp [RSADesc.unitResidue]
    simp [h]
  have hone : ((PMF.uniformOfFintype (ZMod desc.modulus)ˣ).map fun u => decide (u = 1)) true =
      (Nat.totient desc.modulus : ENNReal)⁻¹ := by
    rw [PMF.map_decide_eq_apply_true, PMF.uniformOfFintype_apply, ZMod.card_units_eq_totient]
  rw [eval_eufCmaExperiment_unhashedRSAUniversalForger desc hm _ hpick, ProbComp.eval_map,
    ProbComp.eval_uniform, PMF.map_comp, hfun, ← PMF.map_comp, ← hone]
  simp [PMF.map_apply]

/-- **Unhashed RSA signatures are universally forgeable** ([BonehShoup2023], p. 537): with the
blinding factor `N - 1`, the forger wins Attack Game 13.1 with probability `1`, for every key and
every message. It makes at most one signing query (`isQueryBounded_unhashedRSAUniversalForger`),
and it is not certified as a polynomial-time program. -/
theorem eval_eufCmaExperiment_unhashedRSAUniversalForger_sub_one (desc : RSADesc)
    (m : Fin desc.modulus) :
    ProbComp.eval ((unhashedRSASignature desc).eufCmaExperiment
      fun _ => unhashedRSAUniversalForger desc.publicKey m (pure (desc.modulus - 1))) =
      PMF.pure true := by
  by_cases hm : Nat.Coprime m desc.modulus
  · have hN : 2 * 2 ≤ desc.modulus := Nat.mul_le_mul desc.hp.two_le desc.hq.two_le
    have hcop : Nat.Coprime (desc.modulus - 1) desc.modulus :=
      (Nat.coprime_self_sub_left (by omega)).mpr (Nat.coprime_one_left _)
    rw [eval_eufCmaExperiment_unhashedRSAUniversalForger desc hm (pure (desc.modulus - 1))
      (by simpa using hcop)]
    have hne : ¬ desc.modulus - 1 ≡ 1 [MOD desc.modulus] := by
      intro h
      have := Nat.ModEq.eq_of_lt_of_lt h (by omega) (by omega)
      omega
    simp [hne]
  · exact eval_eufCmaExperiment_unhashedRSAUniversalForger_of_not_coprime desc hm _

/-! ### Multiplicative forgery with two queries (p. 547, equation (13.9)) -/

/-- The forger of [BonehShoup2023], p. 547: ask for the signatures on `m₁` and `m₂` and output
their product modulo `N` as a signature on `m₃`. It makes two signing queries. -/
@[expose]
def rsaMultiplicativeForger (pk : RSAPublicKey) (m₁ m₂ m₃ : M) :
    ProbOracleComp (fun _ : M => ℕ) (M × ℕ) := do
  let σ₁ ← ProbOracleComp.query (spec := fun _ : M => ℕ) m₁
  let σ₂ ← ProbOracleComp.query (spec := fun _ : M => ℕ) m₂
  return (m₃, σ₁ * σ₂ % pk.N)

theorem isQueryBounded_rsaMultiplicativeForger (pk : RSAPublicKey) (m₁ m₂ m₃ : M) :
    (rsaMultiplicativeForger pk m₁ m₂ m₃).IsQueryBounded 2 := by
  unfold rsaMultiplicativeForger
  simpa using (ProbOracleComp.IsQueryBounded.query (spec := fun _ : M => ℕ) m₁).bind
    fun σ₁ => (ProbOracleComp.IsQueryBounded.query (spec := fun _ : M => ℕ) m₂).bind
      fun σ₂ => OracleComp.IsCostBounded.pure (m₃, σ₁ * σ₂ % pk.N) 0

/-- **Multiplicative forgery** ([BonehShoup2023], equation (13.9)): if the digest of `m₃` is the
product of the digests of `m₁` and `m₂` modulo `N` and `m₃` is neither of them, the forger wins
Attack Game 13.1 against `rsaSignature desc H` with probability `1`. -/
theorem eval_eufCmaExperiment_rsaMultiplicativeForger [DecidableEq M] (desc : RSADesc)
    (H : M → ℕ) {m₁ m₂ m₃ : M} (hH : H m₃ ≡ H m₁ * H m₂ [MOD desc.modulus])
    (h₁ : m₃ ≠ m₁) (h₂ : m₃ ≠ m₂) :
    ProbComp.eval ((rsaSignature desc H).eufCmaExperiment
      fun pk => rsaMultiplicativeForger pk m₁ m₂ m₃) = PMF.pure true := by
  have hσ : rsaInvert desc.modulus desc.d (H m₁) * rsaInvert desc.modulus desc.d (H m₂) %
      desc.modulus = rsaInvert desc.modulus desc.d (H m₁ * H m₂) :=
    (rsaEval_mul desc.modulus desc.d (H m₁) (H m₂)).symm
  have hv : rsaEval desc.modulus desc.e (rsaInvert desc.modulus desc.d (H m₁ * H m₂)) =
      H m₃ % desc.modulus := (rsaEval_rsaInvert_mod desc _).trans hH.symm
  have hlt : rsaInvert desc.modulus desc.d (H m₁ * H m₂) < desc.modulus :=
    Nat.mod_lt _ desc.modulus_pos
  simp [forgeExperiment, ProbOracleComp.runLogWith, rsaMultiplicativeForger, rsaSignature,
    freshMessage, hσ, hv, hlt, h₁, h₂]

/-! ### Efficiency of the forgers' arithmetic -/

/-- Blinding is computable in polynomial time whenever `N`, `e`, `m` and `r` are, and
`0 < N a`. This certifies the map, not a forger. -/
theorem computableInPolyTime_rsaBlind {α : Type} {enc : α ↪ List Bool} {N e m r : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (he : ComputableInPolyTime e enc encNat)
    (hm : ComputableInPolyTime m enc encNat) (hr : ComputableInPolyTime r enc encNat)
    (hpos : ∀ a, 0 < N a) :
    ComputableInPolyTime (fun a => rsaBlind (N a) (e a) (m a) (r a)) enc encNat :=
  ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_mul' hm (computableInPolyTime_rsaEval hN he hr hpos)) hN

/-- Unblinding is computable in polynomial time whenever `N`, `r` and `σ` are. This certifies
the map, not a forger. -/
theorem computableInPolyTime_rsaUnblind {α : Type} {enc : α ↪ List Bool} {N r σ : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hr : ComputableInPolyTime r enc encNat)
    (hσ : ComputableInPolyTime σ enc encNat) :
    ComputableInPolyTime (fun a => rsaUnblind (N a) (r a) (σ a)) enc encNat :=
  ComputableInPolyTime.binary_mod'
    (ComputableInPolyTime.binary_mul' hσ (ComputableInPolyTime.binary_modInv' hr hN)) hN

end Cslib.Crypto
