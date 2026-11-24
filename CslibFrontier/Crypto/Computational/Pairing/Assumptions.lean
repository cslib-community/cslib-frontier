/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Computational.Pairing
public import CslibFrontier.Crypto.Computational.DiffieHellman
public import CslibFrontier.Crypto.Game
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
import CslibFrontier.Computability.Probabilistic.PPT.Capture
import CslibFrontier.Computability.Probabilistic.PPT.Extension
import CslibFrontier.Crypto.Game.Order
import CslibFrontier.Crypto.Negligible.Basic
import CslibFrontier.Probability.PMF
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformPoint
import CslibFrontier.Tactic.GameHop
import CslibFrontier.Tactic.Negligible
import CslibFrontier.Tactic.PolyTime.Init
import CslibFrontier.Tactic.PPT

/-!
# Pairing-based hardness assumptions and direct consequences

This module formalizes the co-Computational Diffie–Hellman (co-CDH) and Decision Bilinear
Diffie–Hellman (Decision BDH) assumptions over pairing groups, together with the direct algebraic
consequences of a pairing from [BonehShoup2023], Sections 15.4–15.6.

* **Co-CDH (`Attack Game 15.1` and `Definition 15.3`, p. 628):** stated for a prime-order group
  family `F` and a companion `C : F.Companion` (`PrimeOrderGroupFamily.CoCDH`), giving the
  adversary `(α • g₀, α • g₁, β • g₀) ∈ G₀ × G₁ × G₀` and asking for `(α * β) • g₀ ∈ G₀`.
  For any companion `C`, `F.CoCDH C setup` implies `F.CDH setup` (and hence `F.DiscreteLog setup`),
  and when `C = F.self` (`G₁ = G₀`) it is equivalent to `F.CDH setup` (`coCdh_self_iff_cdh`).
* **Decision BDH (`Attack Game 15.8` and `Definition 15.12`, pp. 649–650):** stated over a
  `PairingGroupFamily` (`PairingGroupFamily.DecisionBDH`), asking a uniform strict PPT
  distinguisher to distinguish `(α • g₀, α • g₁, β • g₀, γ • g₁, (α * β * γ) • g_T)` from
  `(α • g₀, α • g₁, β • g₀, γ • g₁, δ • g_T)`. Since distinguishers output a single bit, this is
  equivalent to its word-level form (`decisionBDH_iff_encoded`).
* **Direct §15.4 consequences (p. 625):** when a pairing is symmetric (`P.G₁ = P.G₀.self`), checking
  `e(u, v) = e(g₀, w)` (equation (15.8)) decides DDH with advantage at least `1 / 2` for every setup
  law (`PairingGroupFamily.not_ddh_of_symmetric`). Moreover, discrete logarithm hardness in `GT`
  follows from discrete logarithm hardness in either source group
  (`DiscreteLog.target_of_sourceZero` and `DiscreteLog.target_of_sourceOne`).

All family assumptions allow an arbitrary `setup : ℕ → PMF F.Desc` rather than an efficient group
generator; they coincide with the textbook assumptions when `setup` is efficiently samplable.
They are hypotheses, not theorems.

## Main definitions

* `Cslib.Crypto.coCdhExperiment`, `Cslib.Crypto.coCdhAdvantage`: fixed-group co-CDH experiment and
  advantage.
* `Cslib.Crypto.dbdhRealExperiment`, `Cslib.Crypto.dbdhRandomExperiment`,
  `Cslib.Crypto.dbdhAdvantage`: fixed-group Decision BDH experiments and advantage.
* `Cslib.Crypto.PrimeOrderGroupFamily.CoCDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.encCoCDHInput`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CoCDHAdversary`,
  `Cslib.Crypto.PrimeOrderGroupFamily.coCdhGame`, `Cslib.Crypto.PrimeOrderGroupFamily.CoCDH`:
  asymptotic co-CDH game and assumption.
* `Cslib.Crypto.PairingGroupFamily.DBDHInput`, `Cslib.Crypto.PairingGroupFamily.encDBDHInput`,
  `Cslib.Crypto.PairingGroupFamily.DBDHDistinguisher`,
  `Cslib.Crypto.PairingGroupFamily.dbdhRealGame`,
  `Cslib.Crypto.PairingGroupFamily.dbdhRandomGame`,
  `Cslib.Crypto.PairingGroupFamily.DecisionBDH`: asymptotic Decision BDH games and assumption.

## Main results

* `Cslib.Crypto.PrimeOrderGroupFamily.CoCDH.cdh`,
  `Cslib.Crypto.PrimeOrderGroupFamily.CoCDH.discreteLog`,
  `Cslib.Crypto.PrimeOrderGroupFamily.coCdh_self_iff_cdh`: relations between co-CDH, CDH, and
  discrete logarithms.
* `Cslib.Crypto.PairingGroupFamily.decisionBDH_iff_encoded`: word-level equivalence for Decision
  BDH.
* `Cslib.Crypto.PairingGroupFamily.not_ddh_of_symmetric`: symmetric pairings break DDH.
* `Cslib.Crypto.PairingGroupFamily.DiscreteLog.target_of_sourceZero`,
  `Cslib.Crypto.PairingGroupFamily.DiscreteLog.target_of_sourceOne`: source-group discrete-log
  hardness implies target-group discrete-log hardness.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Sections 15.4–15.6 (pp. 625, 628–629, 649–650).
-/

public section

namespace Cslib.Crypto

open Probability Turing.MultiTapeTM
open scoped ENNReal NNReal Cslib.Probability.PMF

section FixedExperiments

/-! ### Fixed-group co-CDH and Decision BDH experiments -/

section CoCDHExperiment

variable {G₀ G₁ : Type} [AddCommGroup G₀] [DecidableEq G₀] [AddCommGroup G₁] (q : ℕ) [NeZero q]
  [Module (ZMod q) G₀] [Module (ZMod q) G₁] (g₀ : G₀) (g₁ : G₁)

/-- The co-Computational Diffie–Hellman experiment ([BonehShoup2023], Attack Game 15.1, p. 628) in
fixed groups `G₀` and `G₁` of order `q`: draw uniform `α, β : ZMod q`, give `(α • g₀, α • g₁,
β • g₀)` to `A`, and accept when `A` outputs `(α * β) • g₀`. -/
@[expose] noncomputable def coCdhExperiment (A : G₀ → G₁ → G₀ → ProbComp G₀) : Experiment := do
  let a ← $ᵗ ZMod q
  let b ← $ᵗ ZMod q
  let z ← A (a • g₀) (a • g₁) (b • g₀)
  return z = (a * b) • g₀

/-- The co-CDH advantage of `A`: its success probability in `coCdhExperiment`. -/
@[expose] noncomputable def coCdhAdvantage (A : G₀ → G₁ → G₀ → ProbComp G₀) : ℝ≥0 :=
  Experiment.succProbability (coCdhExperiment q g₀ g₁ A)

/-- Ignoring the `G₁` element in `coCdhExperiment` yields `cdhExperiment` in `G₀`. -/
theorem coCdhExperiment_ignoreSecond (A : G₀ → G₀ → ProbComp G₀) :
    coCdhExperiment q g₀ g₁ (fun u₀ _ v₀ => A u₀ v₀) = cdhExperiment q g₀ A := rfl

/-- When `G₁ = G₀` and `g₁ = g₀`, feeding `u` as both `u₀` and `u₁` reduces `coCdhExperiment` to
`cdhExperiment`. -/
theorem coCdhExperiment_self {g : G₀} (A : G₀ → G₀ → G₀ → ProbComp G₀) :
    coCdhExperiment q g g A = cdhExperiment q g (fun u v => A u u v) := rfl

end CoCDHExperiment

section DBDHExperiment

variable {G₀ G₁ GT : Type} [AddCommGroup G₀] [AddCommGroup G₁] [AddCommGroup GT] (q : ℕ) [NeZero q]
  [Module (ZMod q) G₀] [Module (ZMod q) G₁] [Module (ZMod q) GT] (g₀ : G₀) (g₁ : G₁) (gT : GT)

/-- The real world of the Decision Bilinear Diffie–Hellman experiment ([BonehShoup2023], Attack
Game 15.8, Experiment 0, p. 649): draw uniform `α, β, γ : ZMod q` and give `(α • g₀, α • g₁,
β • g₀, γ • g₁, (α * β * γ) • gT)` to `D`. The book's unused `δ` does not affect the law. -/
@[expose] noncomputable def dbdhRealExperiment (D : G₀ → G₁ → G₀ → G₁ → GT → ProbComp Bool) :
    Experiment := do
  let a ← $ᵗ ZMod q
  let b ← $ᵗ ZMod q
  let c ← $ᵗ ZMod q
  D (a • g₀) (a • g₁) (b • g₀) (c • g₁) ((a * b * c) • gT)

/-- The random world of the Decision Bilinear Diffie–Hellman experiment ([BonehShoup2023], Attack
Game 15.8, Experiment 1, p. 649): draw uniform `α, β, γ, δ : ZMod q` and give `(α • g₀, α • g₁,
β • g₀, γ • g₁, δ • gT)` to `D`. -/
@[expose] noncomputable def dbdhRandomExperiment (D : G₀ → G₁ → G₀ → G₁ → GT → ProbComp Bool) :
    Experiment := do
  let a ← $ᵗ ZMod q
  let b ← $ᵗ ZMod q
  let c ← $ᵗ ZMod q
  let d ← $ᵗ ZMod q
  D (a • g₀) (a • g₁) (b • g₀) (c • g₁) (d • gT)

/-- The Decision BDH advantage of `D`: its distinguishing advantage between `dbdhRealExperiment`
and `dbdhRandomExperiment`. -/
@[expose] noncomputable def dbdhAdvantage (D : G₀ → G₁ → G₀ → G₁ → GT → ProbComp Bool) : ℝ≥0 :=
  Experiment.advantage (dbdhRealExperiment q g₀ g₁ gT D) (dbdhRandomExperiment q g₀ g₁ gT D)

/-- The law of `dbdhRealExperiment`: uniform `a, b, c : ZMod q` at the `PMF` level. -/
theorem eval_dbdhRealExperiment (D : G₀ → G₁ → G₀ → G₁ → GT → ProbComp Bool) :
    ProbComp.eval (dbdhRealExperiment q g₀ g₁ gT D) =
      (PMF.uniformOfFintype (ZMod q)).bind fun a =>
        (PMF.uniformOfFintype (ZMod q)).bind fun b =>
          (PMF.uniformOfFintype (ZMod q)).bind fun c =>
            ProbComp.eval (D (a • g₀) (a • g₁) (b • g₀) (c • g₁) ((a * b * c) • gT)) := by
  simp only [dbdhRealExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]

/-- The law of `dbdhRandomExperiment`: uniform `a, b, c, d : ZMod q` at the `PMF` level. -/
theorem eval_dbdhRandomExperiment (D : G₀ → G₁ → G₀ → G₁ → GT → ProbComp Bool) :
    ProbComp.eval (dbdhRandomExperiment q g₀ g₁ gT D) =
      (PMF.uniformOfFintype (ZMod q)).bind fun a =>
        (PMF.uniformOfFintype (ZMod q)).bind fun b =>
          (PMF.uniformOfFintype (ZMod q)).bind fun c =>
            (PMF.uniformOfFintype (ZMod q)).bind fun d =>
              ProbComp.eval (D (a • g₀) (a • g₁) (b • g₀) (c • g₁) (d • gT)) := by
  simp only [dbdhRandomExperiment, ProbComp.eval_bind, ProbComp.eval_uniform]

end DBDHExperiment

end FixedExperiments

namespace PrimeOrderGroupFamily

variable (F : PrimeOrderGroupFamily)

/-! ### Asymptotic co-CDH assumption over a family and companion -/

/-- The input of a co-CDH adversary: the security parameter, public group parameters `d`,
elements `u₀ = α • g₀`, `u₁ = α • g₁`, and `v₀ = β • g₀`. -/
structure CoCDHInput (C : F.Companion) where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the groups `F.Carrier d` and `C.Carrier d`. -/
  groupParameters : F.Desc
  /-- First base challenge `α • g₀ ∈ G₀`. -/
  leftZero : F.Carrier groupParameters
  /-- Companion challenge `α • g₁ ∈ G₁`. -/
  leftOne : C.Carrier groupParameters
  /-- Second base challenge `β • g₀ ∈ G₀`. -/
  rightZero : F.Carrier groupParameters

/-- Encoding of a co-CDH input: unary security parameter, `F.encDesc`, and encoded elements
`F.encode d u₀`, `C.encode d u₁`, `F.encode d v₀`, each framed except the last. -/
enc_structure encCoCDHInput (F : PrimeOrderGroupFamily) (C : F.Companion) : CoCDHInput F C where
  secParam : encUnary,
  groupParameters : F.encDesc,
  leftZero : (F.encode groupParameters) using (F.encode_injective groupParameters),
  leftOne : (C.encode groupParameters) using (C.encode_injective groupParameters),
  rightZero : (F.encode groupParameters) using (F.encode_injective groupParameters)

/-- A co-CDH adversary over `F` and companion `C`: given the security parameter, group parameters
`d`, and `(u₀, u₁, v₀)`, it outputs an element of `F.Carrier d`. -/
abbrev CoCDHAdversary (C : F.Companion) : Type :=
  ℕ → (d : F.Desc) → F.Carrier d → C.Carrier d → F.Carrier d → ProbComp (F.Carrier d)

variable {F} in
/-- A co-CDH adversary is PPT when one uniform strict PPT machine reads `F.encCoCDHInput C` and
writes the encoding of the adversary's output element in `F.Carrier d`. -/
@[expose] def CoCDHAdversary.IsPPT {C : F.Companion} (adversary : F.CoCDHAdversary C) : Prop :=
  IsPPTOn (F.encCoCDHInput C) encBits fun x =>
    F.encode x.groupParameters <$>
      adversary x.secParam x.groupParameters x.leftZero x.leftOne x.rightZero

/-- The co-CDH game ([BonehShoup2023], Attack Game 15.1, p. 628): draw group parameters `d` from
the arbitrary setup law, then run `coCdhExperiment` in `(F.Carrier d, C.Carrier d)`. -/
@[expose] noncomputable def coCdhGame (C : F.Companion) (setup : ℕ → PMF F.Desc)
    (adversary : F.CoCDHAdversary C) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    coCdhExperiment (F.order d) (F.generator d) (C.generator d) (adversary n d)

/-- The co-Computational Diffie–Hellman assumption ([BonehShoup2023], Attack Game 15.1 and
Definition 15.3, p. 628) for a family `F`, companion `C`, and setup law `setup`: every uniform
strict PPT co-CDH adversary wins `coCdhGame` with negligible probability. As for `CDH` and
`DiscreteLog`, `setup` is an arbitrary `ℕ → PMF F.Desc` rather than an efficient group generator;
this matches the source when `setup` is efficiently samplable. -/
@[expose] def CoCDH (C : F.Companion) (setup : ℕ → PMF F.Desc) : Prop :=
  ∀ adversary : F.CoCDHAdversary C, adversary.IsPPT →
    Negligible fun n => Game.succProbability (F.coCdhGame C setup adversary n)

/-- Embed a CDH adversary into a co-CDH adversary by ignoring the `G₁` challenge `u₁`. -/
@[expose] def cdhToCoCDHAdversary (C : F.Companion) (adversary : F.CDHAdversary) :
    F.CoCDHAdversary C :=
  fun n d u₀ _ v₀ => adversary n d u₀ v₀

private def coCDHInputToCDH (C : F.Companion) (x : F.CoCDHInput C) : F.CDHInput :=
  ⟨x.secParam, x.groupParameters, x.leftZero, x.rightZero⟩

/-- The projection from `CoCDHInput` to `CDHInput` is computable in polynomial time. -/
private theorem computableInPolyTime_coCDHInputToCDH (C : F.Companion) :
    ComputableInPolyTime (F.coCDHInputToCDH C) (F.encCoCDHInput C) F.encCDHInput := by
  have hsec : ComputableInPolyTime (fun x : F.CoCDHInput C => x.secParam)
      (F.encCoCDHInput C) encUnary := by fun_prop
  have hgrp : ComputableInPolyTime (fun x : F.CoCDHInput C => x.groupParameters)
      (F.encCoCDHInput C) F.encDesc := by fun_prop
  have hlz : ComputableInPolyTime
      (fun x : F.CoCDHInput C => F.encode x.groupParameters x.leftZero)
      (F.encCoCDHInput C) encBits := by fun_prop
  have hrz : ComputableInPolyTime
      (fun x : F.CoCDHInput C => F.encode x.groupParameters x.rightZero)
      (F.encCoCDHInput C) encBits := by fun_prop
  exact (F.encCDHInput_mk_polyTime hsec hgrp hlz hrz).of_enc_eq fun _ => rfl

/-- Wrapping a PPT CDH adversary to ignore `u₁` preserves uniform strict PPT. -/
theorem isPPT_cdhToCoCDHAdversary (C : F.Companion) {adversary : F.CDHAdversary}
    (hA : adversary.IsPPT) : (F.cdhToCoCDHAdversary C adversary).IsPPT :=
  hA.preprocess (F.computableInPolyTime_coCDHInputToCDH C)

/-- `coCdhGame` of `cdhToCoCDHAdversary` equals `cdhGame` of `adversary`. -/
@[simp] theorem coCdhGame_cdhToCoCDHAdversary (C : F.Companion) (setup : ℕ → PMF F.Desc)
    (adversary : F.CDHAdversary) (n : ℕ) :
    F.coCdhGame C setup (F.cdhToCoCDHAdversary C adversary) n = F.cdhGame setup adversary n :=
  rfl

variable {F} in
/-- **Co-CDH implies CDH** in `F` for every companion `C`: ignoring `u₁ = α • g₁` turns any
CDH adversary into a co-CDH adversary with the same success probability. -/
theorem CoCDH.cdh {C : F.Companion} {setup : ℕ → PMF F.Desc} (h : F.CoCDH C setup) :
    F.CDH setup := by
  intro adversary hA
  simpa only [coCdhGame_cdhToCoCDHAdversary] using h _ (F.isPPT_cdhToCoCDHAdversary C hA)

variable {F} in
/-- **Co-CDH implies DiscreteLog** in `F` for every companion `C`. -/
theorem CoCDH.discreteLog {C : F.Companion} {setup : ℕ → PMF F.Desc} (h : F.CoCDH C setup) :
    F.DiscreteLog setup :=
  h.cdh.discreteLog

/-- Embed a symmetric co-CDH adversary (where `C = F.self`) into a CDH adversary by duplicating
`u = α • g₀` into both `G₀` and `G₁` slots. -/
@[expose] def coCdhSelfToCDHAdversary (adversary : F.CoCDHAdversary F.self) : F.CDHAdversary :=
  fun n d u v => adversary n d u u v

private def cdhInputToCoCDHSelf (x : F.CDHInput) : F.CoCDHInput F.self :=
  ⟨x.secParam, x.groupParameters, x.leftPublic, x.leftPublic, x.rightPublic⟩

/-- Duplicating `leftPublic` from `CDHInput` to `CoCDHInput F.self` is computable in polynomial
time. -/
private theorem computableInPolyTime_cdhInputToCoCDHSelf :
    ComputableInPolyTime F.cdhInputToCoCDHSelf F.encCDHInput (F.encCoCDHInput F.self) := by
  have hsec : ComputableInPolyTime (fun x : F.CDHInput => x.secParam)
      F.encCDHInput encUnary := by fun_prop
  have hgrp : ComputableInPolyTime (fun x : F.CDHInput => x.groupParameters)
      F.encCDHInput F.encDesc := by fun_prop
  have hleft : ComputableInPolyTime
      (fun x : F.CDHInput => F.encode x.groupParameters x.leftPublic)
      F.encCDHInput encBits := by fun_prop
  have hright : ComputableInPolyTime
      (fun x : F.CDHInput => F.encode x.groupParameters x.rightPublic)
      F.encCDHInput encBits := by fun_prop
  exact (F.encCoCDHInput_mk_polyTime F.self hsec hgrp hleft hleft hright).of_enc_eq fun _ => rfl

/-- Duplicating `u` preserves uniform strict PPT. -/
theorem isPPT_coCdhSelfToCDHAdversary {adversary : F.CoCDHAdversary F.self}
    (hA : adversary.IsPPT) : (F.coCdhSelfToCDHAdversary adversary).IsPPT :=
  hA.preprocess F.computableInPolyTime_cdhInputToCoCDHSelf

/-- In the symmetric case `C = F.self`, `coCdhGame` coincides with `cdhGame` of
`coCdhSelfToCDHAdversary`. -/
@[simp] theorem coCdhGame_self_eq (setup : ℕ → PMF F.Desc)
    (adversary : F.CoCDHAdversary F.self) (n : ℕ) :
    F.coCdhGame F.self setup adversary n =
      F.cdhGame setup (F.coCdhSelfToCDHAdversary adversary) n :=
  rfl

/-- **Symmetric co-CDH is equivalent to CDH** ([BonehShoup2023], Section 15.5.1, p. 629): when
`C = F.self` (`G₁ = G₀` and `g₁ = g₀`), `F.CoCDH F.self setup ↔ F.CDH setup`. -/
theorem coCdh_self_iff_cdh (setup : ℕ → PMF F.Desc) :
    F.CoCDH F.self setup ↔ F.CDH setup := by
  refine ⟨CoCDH.cdh, fun hCDH adversary hA => ?_⟩
  rw [funext fun n => F.coCdhGame_self_eq setup adversary n]
  exact hCDH _ (F.isPPT_coCdhSelfToCDHAdversary hA)

end PrimeOrderGroupFamily

namespace PairingGroupFamily

variable (P : PairingGroupFamily)

/-! ### Asymptotic Decision BDH assumption over a pairing group family -/

/-- The input of a Decision BDH distinguisher: security parameter, group parameters `d`, and the
five elements `(u₀, u₁, v₀, w₁, z)` of [BonehShoup2023], Attack Game 15.8 (p. 649). -/
structure DBDHInput where
  /-- The security parameter, given to machines in unary. -/
  secParam : ℕ
  /-- Public parameters selecting the pairing groups. -/
  groupParameters : P.G₀.Desc
  /-- First source challenge `α • g₀ ∈ G₀`. -/
  leftZero : P.G₀.Carrier groupParameters
  /-- Second source challenge `α • g₁ ∈ G₁`. -/
  leftOne : P.G₁.Carrier groupParameters
  /-- Second exponent in first group `β • g₀ ∈ G₀`. -/
  rightZero : P.G₀.Carrier groupParameters
  /-- Third exponent in second group `γ • g₁ ∈ G₁`. -/
  thirdOne : P.G₁.Carrier groupParameters
  /-- Target challenge element, either `(α * β * γ) • g_T` or independent `δ • g_T`. -/
  candidateTarget : P.GT.Carrier groupParameters

/-- Encoding of a Decision BDH input: unary security parameter, `P.G₀.encDesc`, and the five
encoded group elements, each framed except the last. -/
enc_structure encDBDHInput (P : PairingGroupFamily) : DBDHInput P where
  secParam : encUnary,
  groupParameters : P.G₀.encDesc,
  leftZero : (P.G₀.encode groupParameters) using (P.G₀.encode_injective groupParameters),
  leftOne : (P.G₁.encode groupParameters) using (P.G₁.encode_injective groupParameters),
  rightZero : (P.G₀.encode groupParameters) using (P.G₀.encode_injective groupParameters),
  thirdOne : (P.G₁.encode groupParameters) using (P.G₁.encode_injective groupParameters),
  candidateTarget : (P.GT.encode groupParameters) using (P.GT.encode_injective groupParameters)

/-- A Decision BDH distinguisher over `P`: given `(n, d, u₀, u₁, v₀, w₁, z)`, it outputs a bit.
-/
abbrev DBDHDistinguisher : Type :=
  ℕ → (d : P.G₀.Desc) → P.G₀.Carrier d → P.G₁.Carrier d → P.G₀.Carrier d → P.G₁.Carrier d →
    P.GT.Carrier d → ProbComp Bool

variable {P} in
/-- A Decision BDH distinguisher is PPT when one uniform strict PPT machine reads
`P.encDBDHInput` and writes its output bit. -/
@[expose] def DBDHDistinguisher.IsPPT (distinguisher : P.DBDHDistinguisher) : Prop :=
  IsPPTOn P.encDBDHInput encBool fun x =>
    distinguisher x.secParam x.groupParameters x.leftZero x.leftOne x.rightZero x.thirdOne
      x.candidateTarget

/-- The real Decision BDH game ([BonehShoup2023], Attack Game 15.8, Experiment 0, p. 649): draw
group parameters `d` from `setup n` and run `dbdhRealExperiment` with `gT = P.GT.generator d`
(matching `e(g₀, g₁)` by `P.pair_generator d`). -/
@[expose] noncomputable def dbdhRealGame (setup : ℕ → PMF P.G₀.Desc)
    (distinguisher : P.DBDHDistinguisher) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    dbdhRealExperiment (P.G₀.order d) (P.G₀.generator d) (P.G₁.generator d) (P.GT.generator d)
      (distinguisher n d)

/-- The random Decision BDH game ([BonehShoup2023], Attack Game 15.8, Experiment 1, p. 649): draw
group parameters `d` from `setup n` and run `dbdhRandomExperiment` with `gT = P.GT.generator d`. -/
@[expose] noncomputable def dbdhRandomGame (setup : ℕ → PMF P.G₀.Desc)
    (distinguisher : P.DBDHDistinguisher) (n : ℕ) : Game :=
  Game.withSetup (setup n) fun d =>
    dbdhRandomExperiment (P.G₀.order d) (P.G₀.generator d) (P.G₁.generator d) (P.GT.generator d)
      (distinguisher n d)

/-- The Decision Bilinear Diffie–Hellman assumption ([BonehShoup2023], Attack Game 15.8 and
Definition 15.12, pp. 649–650) for a pairing group family `P` and setup law `setup`: every uniform
strict PPT distinguisher has negligible distinguishing advantage between `dbdhRealGame` and
`dbdhRandomGame`. As for `DiscreteLog`, `setup` is an arbitrary `ℕ → PMF P.G₀.Desc` rather than
an efficient parameter generator; this matches the source when `setup` is efficiently samplable. -/
@[expose] def DecisionBDH (setup : ℕ → PMF P.G₀.Desc) : Prop :=
  Game.Indistinguishable (P.dbdhRealGame setup) (P.dbdhRandomGame setup)
    DBDHDistinguisher.IsPPT

/-- Flat word layout `(1ⁿ, d, u₀, u₁, v₀, w₁, z)` of `encDBDHInput`. -/
abbrev encWordDBDHInput :
    (ℕ × P.G₀.Desc × List Bool × List Bool × List Bool × List Bool × List Bool) ↪ List Bool :=
  encPair encUnary (encPair P.G₀.encDesc
    (encPair encBits (encPair encBits (encPair encBits (encPair encBits encBits)))))

/-- **`DecisionBDH` is the word-level Decision BDH assumption**: since distinguishers output a
single bit, quantifying over distinguishers reading the flat word layout gives the exact same
assumption as `DecisionBDH`. -/
theorem decisionBDH_iff_encoded (setup : ℕ → PMF P.G₀.Desc) :
    P.DecisionBDH setup ↔
      ∀ distinguisher :
          ℕ → P.G₀.Desc × List Bool × List Bool × List Bool × List Bool × List Bool →
            ProbComp Bool,
        IsPPTOn P.encWordDBDHInput encBool (fun x => distinguisher x.1 x.2) →
          Negligible fun n =>
            Game.advantage
              (P.dbdhRealGame setup (fun n d u₀ u₁ v₀ w₁ z =>
                distinguisher n (d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀,
                  P.G₁.encode d w₁, P.GT.encode d z)) n)
              (P.dbdhRandomGame setup (fun n d u₀ u₁ v₀ w₁ z =>
                distinguisher n (d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀,
                  P.G₁.encode d w₁, P.GT.encode d z)) n) := by
  constructor
  · intro h distinguisher hD
    refine h _ (IsPPTOn.preprocess hD (prepare := fun x : P.DBDHInput =>
      (x.secParam, x.groupParameters, P.G₀.encode _ x.leftZero, P.G₁.encode _ x.leftOne,
        P.G₀.encode _ x.rightZero, P.G₁.encode _ x.thirdOne, P.GT.encode _ x.candidateTarget))
      ?_)
    exact (ComputableInPolyTime.id' (encIn := P.encDBDHInput)).of_enc_eq fun x =>
      (P.encDBDHInput_apply x).symm
  · intro h distinguisher hD
    obtain ⟨w, hwPPT, hwEq⟩ := hD.exists_bool_factor P.encDBDHInput_apply
    obtain rfl : distinguisher = fun n d u₀ u₁ v₀ w₁ z =>
        w (n, d, P.G₀.encode d u₀, P.G₁.encode d u₁, P.G₀.encode d v₀,
          P.G₁.encode d w₁, P.GT.encode d z) :=
      funext₂ fun n d => funext fun u₀ => funext fun u₁ => funext fun v₀ => funext fun w₁ =>
        funext fun z => hwEq ⟨n, d, u₀, u₁, v₀, w₁, z⟩
    exact h (fun n tup => w (n, tup)) hwPPT

/-! ### Direct §15.4 consequences (p. 625) -/

/-- The pairing DDH check `e(u, v) = e(g₀, w)` on encoded group elements
([BonehShoup2023], equation (15.8), p. 625). -/
@[expose] def symmetricDDHCheck (d : P.G₀.Desc) (u v w : List Bool) : Bool :=
  decide (P.pairEncoded (d, u, v) =
    P.pairEncoded (d, P.G₀.encode d (P.G₀.generator d), w))

private theorem computableInPolyTime_symmetricDDHCheck :
    ComputableInPolyTime
      (fun x : P.G₀.DDHInput =>
        P.symmetricDDHCheck x.groupParameters
          (P.G₀.encode x.groupParameters x.leftPublic)
          (P.G₀.encode x.groupParameters x.rightPublic)
          (P.G₀.encode x.groupParameters x.candidateShared))
      P.G₀.encDDHInput encBool := by
  have hflat : ComputableInPolyTime
      (fun x : P.G₀.DDHInput =>
        (x.secParam, x.groupParameters, P.G₀.encode x.groupParameters x.leftPublic,
          P.G₀.encode x.groupParameters x.rightPublic,
          P.G₀.encode x.groupParameters x.candidateShared))
      P.G₀.encDDHInput
      (encPair encUnary (encPair P.G₀.encDesc (encPair encBits (encPair encBits encBits)))) :=
    (ComputableInPolyTime.id' (encIn := P.G₀.encDDHInput)).of_enc_eq fun x =>
      (P.G₀.encDDHInput_apply x).symm
  have hd : ComputableInPolyTime (fun x : P.G₀.DDHInput => x.groupParameters)
      P.G₀.encDDHInput P.G₀.encDesc :=
    ((ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp hflat)).of_enc_eq
      fun _ => rfl
  have hu : ComputableInPolyTime
      (fun x : P.G₀.DDHInput => P.G₀.encode x.groupParameters x.leftPublic)
      P.G₀.encDDHInput encBits :=
    ((ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp hflat))).of_enc_eq fun _ => rfl
  have hv : ComputableInPolyTime
      (fun x : P.G₀.DDHInput => P.G₀.encode x.groupParameters x.rightPublic)
      P.G₀.encDDHInput encBits :=
    ((ComputableInPolyTime.fst _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hflat)))).of_enc_eq
      fun _ => rfl
  have hw : ComputableInPolyTime
      (fun x : P.G₀.DDHInput => P.G₀.encode x.groupParameters x.candidateShared)
      P.G₀.encDDHInput encBits :=
    ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp
      ((ComputableInPolyTime.snd _ _).comp ((ComputableInPolyTime.snd _ _).comp hflat)))).of_enc_eq
      fun _ => rfl
  have hg₀ := P.G₀.computableInPolyTime_encode_generator hd
  have h1 : ComputableInPolyTime
      (fun x : P.G₀.DDHInput =>
        P.pairEncoded (x.groupParameters,
          P.G₀.encode x.groupParameters x.leftPublic,
          P.G₀.encode x.groupParameters x.rightPublic))
      P.G₀.encDDHInput encBits :=
    P.computableInPolyTime_pairEncoded.comp (hd.prod (hu.prod hv))
  have h2 : ComputableInPolyTime
      (fun x : P.G₀.DDHInput =>
        P.pairEncoded (x.groupParameters,
          P.G₀.encode x.groupParameters (P.G₀.generator x.groupParameters),
          P.G₀.encode x.groupParameters x.candidateShared))
      P.G₀.encDDHInput encBits :=
    P.computableInPolyTime_pairEncoded.comp (hd.prod (hg₀.prod hw))
  exact (h1.beq h2).of_enc_eq fun x => by
    simp [symmetricDDHCheck, beq_eq_decide]

/-- Distinguisher checking equation (15.8) when `P` is a symmetric pairing (`P.G₁ = P.G₀.self`).
-/
@[expose] def symmetricDDHDistinguisher : P.G₀.DDHDistinguisher :=
  fun _ d u v w =>
    pure (P.symmetricDDHCheck d (P.G₀.encode d u) (P.G₀.encode d v) (P.G₀.encode d w))

/-- `symmetricDDHDistinguisher` is uniform strict PPT. -/
theorem isPPT_symmetricDDHDistinguisher : P.symmetricDDHDistinguisher.IsPPT :=
  P.computableInPolyTime_symmetricDDHCheck.isPPTOn

private theorem symmetricDDHCheck_eq_of_symmetric (h : P.G₁ = P.G₀.self) (d : P.G₀.Desc)
    (α β γ : ZMod (P.G₀.order d)) :
    P.symmetricDDHCheck d (P.G₀.encode d (α • P.G₀.generator d))
        (P.G₀.encode d (β • P.G₀.generator d))
        (P.G₀.encode d (γ • P.G₀.generator d)) =
      decide (α * β = γ) := by
  obtain ⟨G₀, G₁, GT, pair, hgen, pe, hpe, hppt⟩ := P
  dsimp only at h
  subst h
  simp only [symmetricDDHCheck]
  change decide (pe (d, G₀.encode d (α • G₀.generator d),
      G₀.self.encode d (β • G₀.self.generator d)) =
    pe (d, G₀.encode d (G₀.generator d),
      G₀.self.encode d (γ • G₀.self.generator d))) = decide (α * β = γ)
  rw [hpe, hpe, decide_eq_decide, (GT.encode_injective d).eq_iff]
  have hp1 : pair d (α • G₀.generator d) (β • G₀.self.generator d) = (α * β) • GT.generator d := by
    rw [LinearMap.map_smul₂, map_smul, smul_smul, hgen]
  have hp2 : pair d (G₀.generator d) (γ • G₀.self.generator d) = γ • GT.generator d := by
    rw [map_smul, hgen]
  rw [hp1, hp2]
  exact (GT.toFamily.smul_generator_injective d).eq_iff

/-- **DDH is easy in a symmetric pairing group** ([BonehShoup2023], Section 15.4, equation (15.8),
p. 625): if `P.G₁ = P.G₀.self`, then checking `e(α • g₀, β • g₀) = e(g₀, γ • g₀)` distinguishes
real DDH triples from random triples with advantage at least `1 / 2` for every setup law. -/
theorem not_ddh_of_symmetric (h : P.G₁ = P.G₀.self) (setup : ℕ → PMF P.G₀.Desc) :
    ¬ P.G₀.DDH setup := by
  intro hDDH
  have hneg := hDDH P.symmetricDDHDistinguisher P.isPPT_symmetricDDHDistinguisher
  have hreal (n : ℕ) :
      P.G₀.ddhRealGame setup P.symmetricDDHDistinguisher n = PMF.pure true := by
    simp only [PrimeOrderGroupFamily.ddhRealGame, Game.withSetup, eval_ddhRealExperiment,
      symmetricDDHDistinguisher, ProbComp.eval_pure, P.symmetricDDHCheck_eq_of_symmetric h,
      decide_true, PMF.bind_const]
  have hrand (n : ℕ) :
      Game.succProbability (P.G₀.ddhRandomGame setup P.symmetricDDHDistinguisher n) ≤
        (1 / 2 : ℝ≥0) := by
    dsimp only [PrimeOrderGroupFamily.ddhRandomGame]
    refine Game.succProbability_withSetup_le _ _ fun d _ => ?_
    dsimp only [Experiment.succProbability, Game.succProbability]
    rw [eval_ddhRandomExperiment]
    simp only [symmetricDDHDistinguisher, ProbComp.eval_pure,
      P.symmetricDDHCheck_eq_of_symmetric h]
    have hinner (a b : ZMod (P.G₀.order d)) :
        ((PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun c =>
          PMF.pure (decide (a * b = c))) true = (P.G₀.order d : ℝ≥0∞)⁻¹ := by
      have heq := Cslib.Probability.PMF.uniformOfFintype_bind_decide_eq_apply_true (a * b)
      simpa only [ZMod.card, eq_comm] using heq
    have hmid (a : ZMod (P.G₀.order d)) :
        ((PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun b =>
          (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun c =>
            PMF.pure (decide (a * b = c))) true = (P.G₀.order d : ℝ≥0∞)⁻¹ := by
      rw [PMF.bind_apply]
      simp_rw [hinner, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    have htot :
        ((PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun a =>
          (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun b =>
            (PMF.uniformOfFintype (ZMod (P.G₀.order d))).bind fun c =>
              PMF.pure (decide (a * b = c))) true = (P.G₀.order d : ℝ≥0∞)⁻¹ := by
      rw [PMF.bind_apply]
      simp_rw [hmid, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [htot, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast]
    have h2 : (2 : ℝ≥0) ≤ P.G₀.order d := by exact_mod_cast (P.G₀.prime_order d).two_le
    simpa only [one_div] using inv_anti₀ (by norm_num) h2
  have hadv (n : ℕ) :
      (1 / 2 : ℝ≥0) ≤
        Game.advantage (P.G₀.ddhRealGame setup P.symmetricDDHDistinguisher n)
          (P.G₀.ddhRandomGame setup P.symmetricDDHDistinguisher n) := by
    rw [hreal n]
    have hra := hrand n
    rw [← NNReal.coe_le_coe] at hra ⊢
    rw [Game.coe_advantage_pure_true_left]
    push_cast at hra ⊢
    linarith
  exact not_negligible_const (by norm_num) (negligible_of_le hneg hadv)

/-- Lift a target-group discrete-log adversary to `P.G₀` via `u₀ ↦ P.pair d u₀ g₁`
([BonehShoup2023], Section 15.4, p. 625). -/
@[expose] noncomputable def dlTargetToZeroAdversary
    (adversary : ℕ → P.G₀.Desc × List Bool → ProbComp (List Bool)) :
    ℕ → P.G₀.Desc × List Bool → ProbComp (List Bool) :=
  fun n input => adversary n (input.1, P.pairEncoded (input.1, input.2,
    P.G₁.encode input.1 (P.G₁.generator input.1)))

/-- `dlTargetToZeroAdversary` preserves uniform strict PPT. -/
theorem isPPT_dlTargetToZeroAdversary
    {adversary : ℕ → P.G₀.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair P.G₀.encDesc encBits)) encBits
      fun x => adversary x.1 x.2) :
    IsPPTOn (encPair encUnary (encPair P.G₀.encDesc encBits)) encBits
      fun x => P.dlTargetToZeroAdversary adversary x.1 x.2 := by
  have hd : ComputableInPolyTime (fun x : ℕ × P.G₀.Desc × List Bool => x.2.1)
      (encPair encUnary (encPair P.G₀.encDesc encBits)) P.G₀.encDesc := by fun_prop
  have hu : ComputableInPolyTime (fun x : ℕ × P.G₀.Desc × List Bool => x.2.2)
      (encPair encUnary (encPair P.G₀.encDesc encBits)) encBits := by fun_prop
  have hg₁ := P.G₁.computableInPolyTime_encode_generator hd
  have hp := P.computableInPolyTime_pairEncoded.comp (hd.prod (hu.prod hg₁))
  exact hA.preprocess ((by fun_prop : ComputableInPolyTime
    (fun x : ℕ × P.G₀.Desc × List Bool => x.1) _ encUnary).prod (hd.prod hp))

/-- **Discrete-log hardness in `G₀` implies discrete-log hardness in `GT`** ([BonehShoup2023],
Section 15.4, p. 625: computing discrete logarithms in `G₀` is no harder than in `GT`). -/
theorem DiscreteLog.target_of_sourceZero {setup : ℕ → PMF P.G₀.Desc}
    (hG₀ : P.G₀.DiscreteLog setup) : P.GT.toFamily.DiscreteLog setup := by
  intro adversary hA
  have hred := hG₀ (P.dlTargetToZeroAdversary adversary) (P.isPPT_dlTargetToZeroAdversary hA)
  refine negligible_of_le hred fun n => ?_
  simp only [PrimeOrderGroupFamily.discreteLogGame, dlTargetToZeroAdversary,
    PrimeOrderGroupFamily.Companion.toFamily]
  refine Game.succProbability_mono (PMF.bind_apply_mono_on_support _ _ fun d _ => ?_)
  refine PMF.bind_apply_mono_on_support _ _ fun a _ => ?_
  have h1 : P.G₁.generator d = (1 : ZMod (P.G₀.order d)) • P.G₁.generator d := (one_smul _ _).symm
  rw [P.pairEncoded_encode, h1, P.pair_smul_generator_smul_generator, mul_one]

/-- Lift a target-group discrete-log adversary to `P.G₁` via `u₁ ↦ P.pair d g₀ u₁`
([BonehShoup2023], Section 15.4, p. 625). -/
@[expose] noncomputable def dlTargetToOneAdversary
    (adversary : ℕ → P.G₀.Desc × List Bool → ProbComp (List Bool)) :
    ℕ → P.G₀.Desc × List Bool → ProbComp (List Bool) :=
  fun n input => adversary n (input.1, P.pairEncoded (input.1,
    P.G₀.encode input.1 (P.G₀.generator input.1), input.2))

/-- `dlTargetToOneAdversary` preserves uniform strict PPT. -/
theorem isPPT_dlTargetToOneAdversary
    {adversary : ℕ → P.G₀.Desc × List Bool → ProbComp (List Bool)}
    (hA : IsPPTOn (encPair encUnary (encPair P.G₁.toFamily.encDesc encBits)) encBits
      fun x => adversary x.1 x.2) :
    IsPPTOn (encPair encUnary (encPair P.G₁.toFamily.encDesc encBits)) encBits
      fun x => P.dlTargetToOneAdversary adversary x.1 x.2 := by
  have hd : ComputableInPolyTime (fun x : ℕ × P.G₀.Desc × List Bool => x.2.1)
      (encPair encUnary (encPair P.G₀.encDesc encBits)) P.G₀.encDesc := by fun_prop
  have hv : ComputableInPolyTime (fun x : ℕ × P.G₀.Desc × List Bool => x.2.2)
      (encPair encUnary (encPair P.G₀.encDesc encBits)) encBits := by fun_prop
  have hg₀ := P.G₀.computableInPolyTime_encode_generator hd
  have hp := P.computableInPolyTime_pairEncoded.comp (hd.prod (hg₀.prod hv))
  exact hA.preprocess ((by fun_prop : ComputableInPolyTime
    (fun x : ℕ × P.G₀.Desc × List Bool => x.1) _ encUnary).prod (hd.prod hp))

/-- **Discrete-log hardness in `G₁` implies discrete-log hardness in `GT`** ([BonehShoup2023],
Section 15.4, p. 625: computing discrete logarithms in `G₁` is no harder than in `GT`). -/
theorem DiscreteLog.target_of_sourceOne {setup : ℕ → PMF P.G₀.Desc}
    (hG₁ : P.G₁.toFamily.DiscreteLog setup) : P.GT.toFamily.DiscreteLog setup := by
  intro adversary hA
  have hred := hG₁ (P.dlTargetToOneAdversary adversary) (P.isPPT_dlTargetToOneAdversary hA)
  refine negligible_of_le hred fun n => ?_
  simp only [PrimeOrderGroupFamily.discreteLogGame, dlTargetToOneAdversary,
    PrimeOrderGroupFamily.Companion.toFamily]
  refine Game.succProbability_mono (PMF.bind_apply_mono_on_support _ _ fun d _ => ?_)
  refine PMF.bind_apply_mono_on_support _ _ fun a _ => ?_
  have h1 : P.G₀.generator d = (1 : ZMod (P.G₀.order d)) • P.G₀.generator d := (one_smul _ _).symm
  rw [P.pairEncoded_encode, h1, P.pair_smul_generator_smul_generator, one_mul]

end PairingGroupFamily

end Cslib.Crypto
