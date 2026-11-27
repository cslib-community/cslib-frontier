/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Computational.DiffieHellman.EvenOrder
public import CslibFrontier.Crypto.Computational.DiscreteLog.CyclicGroupFamily
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Captured
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Prime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Search
import CslibFrontier.Crypto.Negligible.InversePolynomial
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Tactic.PPT

/-!
# Decisional Diffie–Hellman over cyclic group families, and small prime factors of the order

This module states the Decisional Diffie–Hellman assumption over a `CyclicGroupFamily`: Attack
Game 10.6 of [BonehShoup2023] (p. 410) without the restriction that the order is prime, as in
Exercise 10.24 (p. 431). Its declarations have the shapes of the prime-order ones in
`CslibFrontier/Crypto/Computational/DiffieHellman.lean`, and on a prime-order family the two
assumptions agree (`PrimeOrderGroupFamily.ddh_toCyclicGroupFamily_iff`).

The small-prime-factor test of [BonehShoup2023], Exercise 16.2(a) (p. 707)
(`Cslib.Crypto.ddhSmallFactorDistinguisher` in
`CslibFrontier/Crypto/Computational/DiffieHellman/SmallFactor.lean`), generalizes the parity test
of Section 16.1.3 (`Cslib.Crypto.ddhParityDistinguisher` in
`CslibFrontier/Crypto/Computational/DiffieHellman/EvenOrder.lean`) from `l = 2` to any prime
factor `l ∣ F.order d`. Parameterized by a factor selector
`factor : ℕ → F.Desc → ℕ`, `CyclicGroupFamily.ddhSmallFactorDistinguisher F factor` is computed by
one uniform strict PPT machine on `encDDHInput` whenever `factor` is polynomial time
(`CyclicGroupFamily.isPPT_ddhSmallFactorDistinguisher`). Whenever `factor n d` is a prime divisor
of `F.order d` at most `bound n`, its distinguishing advantage is at least `(bound n)⁻¹`
(`CyclicGroupFamily.inv_le_advantage_ddhSmallFactorDistinguisher`), so DDH fails whenever a
polynomial-time selector finds a polynomially bounded prime factor infinitely often
(`CyclicGroupFamily.not_ddh_of_prime_factor`). In particular:

* Exercise 16.2(a) (`CyclicGroupFamily.not_ddh_of_polynomiallyBounded_minFac`): DDH fails whenever
  `1 < F.order d` and `(F.order d).minFac` is polynomially bounded across `(setup n).support`
  infinitely often. The internal distinguisher uses `Nat.findGreatest` to test the greatest prime
  factor up to the polynomial bound `C * (n + 1) ^ D` where the exercise names the smallest factor,
  yielding the same conclusion without extra machinery.
* Section 16.1.3 and Exercise 10.24 (`CyclicGroupFamily.ddhParityDistinguisher`, `l = 2`):
  `CyclicGroupFamily.isPPT_ddhParityDistinguisher` and `CyclicGroupFamily.not_ddh_of_even_order`
  specialize the small-factor results to `factor _ _ := 2`.

## Main definitions

* `Cslib.Crypto.CyclicGroupFamily.DDHInput`, `Cslib.Crypto.CyclicGroupFamily.encDDHInput`: the
  input of a DDH distinguisher and its encoding.
* `Cslib.Crypto.CyclicGroupFamily.DDHDistinguisher`,
  `Cslib.Crypto.CyclicGroupFamily.DDHDistinguisher.IsPPT`: DDH distinguishers and their
  efficiency on encodings.
* `Cslib.Crypto.CyclicGroupFamily.ddhRealGame`, `Cslib.Crypto.CyclicGroupFamily.ddhRandomGame`,
  `Cslib.Crypto.CyclicGroupFamily.DDH`: the two DDH games and the DDH assumption.
* `Cslib.Crypto.CyclicGroupFamily.ddhSmallFactorDistinguisher`: the small-prime-factor test
  parameterized by a factor selector `factor : ℕ → F.Desc → ℕ`.
* `Cslib.Crypto.CyclicGroupFamily.ddhParityDistinguisher`: the parity test (`l = 2`) as a
  distinguisher over the family.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.isPPT_toCyclicGroupFamily_iff`,
  `Cslib.Crypto.PrimeOrderGroupFamily.ddh_toCyclicGroupFamily_iff`: on a prime-order family, PPT
  distinguishers and the DDH assumption are those of `PrimeOrderGroupFamily`.
* `Cslib.Crypto.CyclicGroupFamily.isPPT_ddhSmallFactorDistinguisher`: the small-factor test is PPT
  when `factor` is polynomial time.
* `Cslib.Crypto.CyclicGroupFamily.inv_le_advantage_ddhSmallFactorDistinguisher`: per-parameter
  advantage lower bound `(B : ℝ≥0)⁻¹`.
* `Cslib.Crypto.CyclicGroupFamily.not_ddh_of_prime_factor`: general DDH failure criterion for any
  polynomially bounded polynomial-time prime factor selector.
* `Cslib.Crypto.CyclicGroupFamily.not_ddh_of_polynomiallyBounded_minFac`: DDH fails when the
  smallest prime factor of `F.order d` is polynomially bounded infinitely often (Exercise 16.2(a)).
* `Cslib.Crypto.CyclicGroupFamily.isPPT_ddhParityDistinguisher`: the parity test is PPT.
* `Cslib.Crypto.CyclicGroupFamily.not_ddh_of_even_order`: DDH does not hold when every group the
  setup law can produce has even order.

## Implementation notes

`DDHInput`, `encDDHInput`, `DDHDistinguisher`, `DDHDistinguisher.IsPPT`, `ddhRealGame`,
`ddhRandomGame` and `DDH` repeat the prime-order declarations over `CyclicGroupFamily`, with the
same games `Cslib.Crypto.ddhRealExperiment` and `Cslib.Crypto.ddhRandomExperiment`.
`ddh_toCyclicGroupFamily_iff` ties the two assumptions together. Removing this repeated boilerplate
after `PrimeOrderGroupFamily` settles is tracked separately in #5673.

Not covered: the `O(log q)` operation count of Exercise 16.2(a) as a count of group operations (only
polynomial time on `encDDHInput` is proved), Exercise 16.2(b), and a family of the groups
`(ZMod p)ˣ`. For such a family with odd primes `p`, `not_ddh_of_even_order` applies, since the order
`p - 1` is even; without it, the book's conclusion that DDH does not hold in `Z_p^*` (p. 687, and
the remark after Exercise 10.24) is proved here only in the fixed-group form
`ddhAdvantage_units_ddhParityDistinguisher`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Attack Game 10.6 (p. 410), Exercise 10.24 (p. 431), Section
  16.1.3 (p. 687) and Exercise 16.2(a) (p. 707).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM

namespace CyclicGroupFamily

variable (F : CyclicGroupFamily)

/-! ### Distinguisher inputs and the DDH assumption -/

/-- The input of a DDH distinguisher: the security parameter, public group parameters `d` and
three elements of `F.Carrier d`, which are `a • g`, `b • g` and the candidate shared element. -/
structure DDHInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the group, its order and generator within the family. -/
  groupParameters : F.Desc
  /-- The first public element, `a • g` in the experiment. -/
  leftPublic : F.Carrier groupParameters
  /-- The second public element, `b • g` in the experiment. -/
  rightPublic : F.Carrier groupParameters
  /-- The candidate shared element: `(a * b) • g` in the real experiment, an independent `c • g`
  in the random one. -/
  candidateShared : F.Carrier groupParameters

/-- The encoding of a DDH input: the unary security parameter, the group parameters and the words
of the three elements, each framed except the last (`encDDHInput_apply`). It has the layout of
`PrimeOrderGroupFamily.encDDHInput`. -/
enc_structure encDDHInput (F : CyclicGroupFamily) : DDHInput F where
  secParam : encUnary, groupParameters : F.encDesc,
  leftPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  rightPublic : (F.encode groupParameters) using (F.encode_injective groupParameters),
  candidateShared : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- A DDH distinguisher over the family: given the security parameter, public group parameters
`d` and three elements of `F.Carrier d`, it outputs a bit. -/
abbrev DDHDistinguisher : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → F.Carrier d → F.Carrier d → ProbComp Bool

variable {F} in
/-- A DDH distinguisher is PPT when one uniform strict PPT machine reads `encDDHInput` and writes
the distinguisher's output bit. -/
@[expose] def DDHDistinguisher.IsPPT (distinguisher : F.DDHDistinguisher) : Prop :=
  IsPPTOn F.encDDHInput encBool fun x =>
    distinguisher x.secParam x.groupParameters x.leftPublic x.rightPublic x.candidateShared

/-- The real DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 0, with the order not
required to be prime as in Exercise 10.24): choose group parameters `d` using the arbitrary setup
law, then run `Cslib.Crypto.ddhRealExperiment` in `F.Carrier d`. -/
@[expose] noncomputable def ddhRealGame (setup : ℕ → PMF F.Desc)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    ddhRealExperiment (F.order d) (F.generator d) (distinguisher n d)

/-- The random DDH game ([BonehShoup2023], Attack Game 10.6, Experiment 1, with the order not
required to be prime as in Exercise 10.24): choose group parameters `d` using the arbitrary setup
law, then run `Cslib.Crypto.ddhRandomExperiment` in `F.Carrier d`. -/
@[expose] noncomputable def ddhRandomGame (setup : ℕ → PMF F.Desc)
    (distinguisher : F.DDHDistinguisher) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    ddhRandomExperiment (F.order d) (F.generator d) (distinguisher n d)

/-- The Decisional Diffie–Hellman assumption for a cyclic group family and a setup law
([BonehShoup2023], Attack Game 10.6, printed p. 410, with the order not required to be prime, as
in Exercise 10.24, printed p. 431): every PPT DDH distinguisher has negligible advantage between
`ddhRealGame` and `ddhRandomGame`. This is a hypothesis, not a theorem; on a prime-order family it
is `PrimeOrderGroupFamily.DDH` (`PrimeOrderGroupFamily.ddh_toCyclicGroupFamily_iff`). -/
@[expose] def DDH (setup : ℕ → PMF F.Desc) : Prop :=
  Game.Indistinguishable (F.ddhRealGame setup) (F.ddhRandomGame setup)
    DDHDistinguisher.IsPPT

end CyclicGroupFamily

/-! ### Agreement with the prime-order assumption -/

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-- The DDH inputs of `F` and of `F.toCyclicGroupFamily` correspond field by field. -/
private def ddhInputEquiv : F.DDHInput ≃ F.toCyclicGroupFamily.DDHInput where
  toFun x := ⟨x.secParam, x.groupParameters, x.leftPublic, x.rightPublic, x.candidateShared⟩
  invFun x := ⟨⟨x.secParam, x.groupParameters, x.leftPublic, x.rightPublic⟩, x.candidateShared⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Corresponding DDH inputs have the same encoding. -/
private theorem encDDHInput_ddhInputEquiv (x : F.DDHInput) :
    F.toCyclicGroupFamily.encDDHInput (F.ddhInputEquiv x) = F.encDDHInput x := by
  rw [CyclicGroupFamily.encDDHInput_apply, encDDHInput_apply]
  rfl

/-- A distinguisher over `F` is PPT for `F.toCyclicGroupFamily` exactly when it is PPT for `F`:
the two input encodings agree. -/
theorem isPPT_toCyclicGroupFamily_iff (distinguisher : F.DDHDistinguisher) :
    CyclicGroupFamily.DDHDistinguisher.IsPPT (F := F.toCyclicGroupFamily) distinguisher ↔
      distinguisher.IsPPT := by
  constructor
  · rintro ⟨k, State, hfin, machine, c, e, h⟩
    refine ⟨k, State, hfin, machine, c, e, fun a => ?_⟩
    rw [← F.encDDHInput_ddhInputEquiv a]
    exact h (F.ddhInputEquiv a)
  · rintro ⟨k, State, hfin, machine, c, e, h⟩
    refine ⟨k, State, hfin, machine, c, e, fun a => ?_⟩
    obtain ⟨a, rfl⟩ := F.ddhInputEquiv.surjective a
    rw [F.encDDHInput_ddhInputEquiv a]
    exact h a

/-- On a prime-order family the DDH assumption over cyclic group families is the prime-order
one. -/
theorem ddh_toCyclicGroupFamily_iff (setup : ℕ → PMF F.Desc) :
    F.toCyclicGroupFamily.DDH setup ↔ F.DDH setup :=
  forall_congr' fun distinguisher =>
    imp_congr (F.isPPT_toCyclicGroupFamily_iff distinguisher) Iff.rfl

end PrimeOrderGroupFamily

/-! ### Small prime factors and the parity test in families -/

namespace CyclicGroupFamily

section SmallFactor

open Filter
open scoped NNReal ENNReal

variable (F : CyclicGroupFamily)

/-- The small-prime-factor DDH distinguisher of [BonehShoup2023], Exercise 16.2(a) (p. 707),
parameterized by a factor selector `factor : ℕ → F.Desc → ℕ`: in the group selected by `d` it runs
`Cslib.Crypto.ddhSmallFactorDistinguisher (F.order d) (factor n d)`. When used inside
`not_ddh_of_polynomiallyBounded_minFac`, `factor` selects the greatest prime factor of `F.order d`
up to the polynomial bound `C * (n + 1) ^ D` where the exercise names the smallest prime factor;
both yield the same failure theorem. -/
@[expose] def ddhSmallFactorDistinguisher (factor : ℕ → F.Desc → ℕ) : F.DDHDistinguisher :=
  fun n d => Crypto.ddhSmallFactorDistinguisher (F.order d) (factor n d)

/-- **The small-factor test is efficient**: whenever `factor` is computable in polynomial time on
`encPair encUnary F.encDesc → encNat`, one uniform strict PPT machine computes
`ddhSmallFactorDistinguisher F factor` on `encDDHInput`. It divides `F.order d` by `factor n d`
and multiplies each encoded element by the quotient using `F.smul`. -/
theorem isPPT_ddhSmallFactorDistinguisher (factor : ℕ → F.Desc → ℕ)
    (hfactor : ComputableInPolyTime (fun p : ℕ × F.Desc => factor p.1 p.2)
      (encPair encUnary F.encDesc) encNat) :
    (ddhSmallFactorDistinguisher F factor).IsPPT := by
  refine (ComputableInPolyTime.isPPTOn (f := fun x : F.DDHInput =>
    decide (F.encode x.groupParameters
        (((F.order x.groupParameters / factor x.secParam x.groupParameters : ℕ) :
          ZMod (F.order x.groupParameters)) • x.candidateShared) = F.encode x.groupParameters 0) ==
      decide (F.encode x.groupParameters
          (((F.order x.groupParameters / factor x.secParam x.groupParameters : ℕ) :
            ZMod (F.order x.groupParameters)) • x.leftPublic) = F.encode x.groupParameters 0 ∨
        F.encode x.groupParameters
          (((F.order x.groupParameters / factor x.secParam x.groupParameters : ℕ) :
            ZMod (F.order x.groupParameters)) • x.rightPublic) = F.encode x.groupParameters 0))
    (by fun_prop)).congr fun x => ?_
  simp [ddhSmallFactorDistinguisher, Crypto.ddhSmallFactorDistinguisher,
    (F.encode_injective _).eq_iff, Nat.cast_smul_eq_nsmul]

/-- If every `d ∈ (setup n).support` has order divisible by a prime `factor n d ≤ B`, then
`ddhSmallFactorDistinguisher F factor` achieves distinguishing advantage at least `(B : ℝ≥0)⁻¹` at
security parameter `n`. -/
theorem inv_le_advantage_ddhSmallFactorDistinguisher (setup : ℕ → PMF F.Desc)
    (factor : ℕ → F.Desc → ℕ) (n B : ℕ)
    (hsupport : ∀ d ∈ (setup n).support,
      (factor n d).Prime ∧ factor n d ∣ F.order d ∧ factor n d ≤ B) :
    (B : ℝ≥0)⁻¹ ≤
      (F.ddhRealGame setup (ddhSmallFactorDistinguisher F factor) n).advantage
        (F.ddhRandomGame setup (ddhSmallFactorDistinguisher F factor) n) := by
  have hreal : F.ddhRealGame setup (ddhSmallFactorDistinguisher F factor) n = PMF.pure true :=
    (PMF.bind_congr_on_support _ _ (fun _ => PMF.pure true) fun d hd =>
      eval_ddhRealExperiment_ddhSmallFactorDistinguisher _ _ _ (hsupport d hd).1
        (hsupport d hd).2.1 (F.smul_generator_injective d)).trans (PMF.bind_const _ _)
  rw [hreal, Game.advantage_pure_true_left]
  suffices (((B : ℝ≥0)⁻¹ : ℝ≥0) : ℝ≥0∞) ≤
      F.ddhRandomGame setup (ddhSmallFactorDistinguisher F factor) n false by
    simpa using ENNReal.toNNReal_mono (PMF.apply_ne_top _ _) this
  refine PMF.le_bind_apply_on_support _ fun d hd => ?_
  obtain ⟨hp, hdvd, hle⟩ := hsupport d hd
  have hadv := inv_le_ddhAdvantage_ddhSmallFactorDistinguisher (F.order d) (factor n d)
    (F.generator d) hp hdvd (F.smul_generator_injective d)
  rw [ddhAdvantage, Experiment.advantage,
    eval_ddhRealExperiment_ddhSmallFactorDistinguisher _ _ _ hp hdvd
      (F.smul_generator_injective d), Game.advantage_pure_true_left] at hadv
  have hB : (B : ℝ≥0)⁻¹ ≤ ((factor n d : ℕ) : ℝ≥0)⁻¹ :=
    inv_anti₀ (by exact_mod_cast hp.pos) (by exact_mod_cast hle)
  have h := ENNReal.coe_le_coe.mpr (hB.trans hadv)
  rw [ENNReal.coe_toNNReal (PMF.apply_ne_top _ _)] at h
  exact h

/-- General prime-factor DDH failure criterion (underlying [BonehShoup2023], Exercise 10.24 and
Exercise 16.2(a)): whenever a polynomial-time factor selector `factor` outputs, for infinitely
many security parameters `n`, a prime divisor of `F.order d` at most `bound n` across
`(setup n).support` for a polynomially bounded `bound`, `F.DDH setup` fails. -/
theorem not_ddh_of_prime_factor {setup : ℕ → PMF F.Desc}
    (factor : ℕ → F.Desc → ℕ)
    (hfactor : ComputableInPolyTime (fun p : ℕ × F.Desc => factor p.1 p.2)
      (encPair encUnary F.encDesc) encNat)
    (bound : ℕ → ℕ) (hbound : PolynomiallyBounded bound)
    (hle : ∃ᶠ n in atTop, ∀ d ∈ (setup n).support,
      (factor n d).Prime ∧ factor n d ∣ F.order d ∧ factor n d ≤ bound n) :
    ¬ F.DDH setup := by
  intro hddh
  refine not_negligible_of_frequently_inv_le (PolynomiallyBoundedNNReal.natCast hbound)
    (hle.mono fun n hn => ⟨?_,
      inv_le_advantage_ddhSmallFactorDistinguisher F setup factor n (bound n) hn⟩)
    (hddh _ (isPPT_ddhSmallFactorDistinguisher F factor hfactor))
  obtain ⟨d, hd⟩ := (setup n).support_nonempty
  exact_mod_cast (hn d hd).1.pos.trans_le (hn d hd).2.2

/-- The greatest prime factor of `q` up to `B` is a prime divisor of `q` up to `B` when
`q.minFac ≤ B`. -/
private theorem findGreatest_primeFactor {q B : ℕ} (hq : 1 < q) (hle : q.minFac ≤ B) :
    (Nat.findGreatest (fun i => i.Prime ∧ q % i = 0) B).Prime ∧
      Nat.findGreatest (fun i => i.Prime ∧ q % i = 0) B ∣ q ∧
      Nat.findGreatest (fun i => i.Prime ∧ q % i = 0) B ≤ B := by
  have h := Nat.findGreatest_spec (P := fun i => i.Prime ∧ q % i = 0) hle
    ⟨Nat.minFac_prime (by omega), Nat.mod_eq_zero_of_dvd (Nat.minFac_dvd q)⟩
  exact ⟨h.1, Nat.dvd_of_mod_eq_zero h.2, Nat.findGreatest_le B⟩

/-- Searching up to `C * (n + 1) ^ D` for the greatest prime divisor of `F.order d` is computable in
polynomial time (`encUnary × F.encDesc → encNat`). -/
private theorem findGreatest_polyTime (C D : ℕ) :
    ComputableInPolyTime
      (fun p : ℕ × F.Desc =>
        Nat.findGreatest (fun i => i.Prime ∧ F.order p.2 % i = 0) (C * (p.1 + 1) ^ D))
      (encPair encUnary F.encDesc) encNat := by
  have hmod : ComputableInPolyTime (fun p : (ℕ × F.Desc) × ℕ => F.order p.1.2 % p.2)
      (encPair (encPair encUnary F.encDesc) encUnary) encNat :=
    .binary_mod' (F.computableInPolyTime_order_comp
      ((ComputableInPolyTime.snd _ _).comp (.fst _ _)))
      (ComputableInPolyTime.unary_to_binary.comp (.snd _ _))
  exact ComputableInPolyTime.unary_to_binary.comp <| ComputableInPolyTime.findGreatest
    ((show ComputableInPolyTime (fun n => C * (n + 1) ^ D) encUnary encUnary by fun_prop).comp
      (.fst _ _))
    ((ComputableInPolyTime.unary_decide_prime.comp (.snd _ _)).decide_and
      (.decide_eq' hmod (.const 0)))

/-- **DDH fails when a small prime factor is polynomially bounded** ([BonehShoup2023], Exercise
16.2(a), p. 707): if for infinitely many security parameters `n`, every group `d` in the support
of `setup n` has `1 < F.order d` and smallest prime factor `(F.order d).minFac ≤ bound n` for a
polynomially bounded `bound`, then DDH does not hold.

The distinguisher instantiated in the proof (`ddhSmallFactorDistinguisher F fun n d =>
Nat.findGreatest (fun i => i.Prime ∧ F.order d % i = 0) (C * (n + 1) ^ D)`) tests the greatest
prime factor up to `C * (n + 1) ^ D` where the exercise names the smallest prime factor; the theorem
is the same, since any prime divisor up to `bound n` gives advantage at least `(bound n)⁻¹`. The
proof establishes polynomial time on `encDDHInput`, not the `O(log q)` operation count. -/
theorem not_ddh_of_polynomiallyBounded_minFac {setup : ℕ → PMF F.Desc}
    (bound : ℕ → ℕ) (hbound : PolynomiallyBounded bound)
    (hmin : ∃ᶠ n in atTop, ∀ d ∈ (setup n).support,
      1 < F.order d ∧ (F.order d).minFac ≤ bound n) :
    ¬ F.DDH setup := by
  obtain ⟨C, D, hCD⟩ := polynomiallyBounded_iff_le.mp hbound
  exact not_ddh_of_prime_factor F
    (fun n d => Nat.findGreatest (fun i => i.Prime ∧ F.order d % i = 0) (C * (n + 1) ^ D))
    (findGreatest_polyTime F C D) (fun n => C * (n + 1) ^ D)
    (polynomiallyBounded_iff_le.mpr ⟨C, D, fun _ => le_rfl⟩)
    (hmin.mono fun n hn d hd =>
      findGreatest_primeFactor (hn d hd).1 ((hn d hd).2.trans (hCD n)))

/-- The parity test of [BonehShoup2023], Section 16.1.3 (p. 687), as a distinguisher over the
family: in the group selected by `d` it runs `Cslib.Crypto.ddhParityDistinguisher (F.order d)`. -/
@[expose] def ddhParityDistinguisher : F.DDHDistinguisher :=
  ddhSmallFactorDistinguisher F (fun _ _ => 2)

/-- **The parity test is efficient**: one uniform strict PPT machine computes
`ddhParityDistinguisher` on `encDDHInput`. It computes `F.order d / 2`, multiplies each encoded
element by it with `F.smul` and compares the results with the encoded identity. -/
theorem isPPT_ddhParityDistinguisher : (ddhParityDistinguisher F).IsPPT :=
  isPPT_ddhSmallFactorDistinguisher F (fun _ _ => 2) (ComputableInPolyTime.const 2)

variable {F} in
/-- **DDH fails in families of even order** ([BonehShoup2023], Exercise 10.24, p. 431): when every
group the setup law can produce has even order, the parity test, which is PPT
(`isPPT_ddhParityDistinguisher`), has advantage `1 / 2` for every security parameter, so the
DDH assumption does not hold. -/
theorem not_ddh_of_even_order {setup : ℕ → PMF F.Desc}
    (heven : ∀ n, ∀ d ∈ (setup n).support, Even (F.order d)) : ¬ F.DDH setup :=
  not_ddh_of_prime_factor F (fun _ _ => 2) (ComputableInPolyTime.const 2) (fun _ => 2)
    (polynomiallyBounded_iff_le.2 ⟨2, 0, fun _ => by simp⟩)
    (Eventually.of_forall fun n d hd =>
      ⟨Nat.prime_two, (heven n d hd).two_dvd, le_rfl⟩).frequently

end SmallFactor

end CyclicGroupFamily

end Cslib.Crypto
