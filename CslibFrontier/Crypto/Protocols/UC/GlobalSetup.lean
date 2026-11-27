/-
Copyright (c) 2026 Phillipp Schoppmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Phillipp Schoppmann
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Composition
public import CslibFrontier.Crypto.Protocols.UC.HybridFunctionality
import CslibFrontier.Languages.Probabilistic.Oracle.InterpNorm

/-!
# Universally Composable Security with Global Setup (EUC / GUC)

This module formalizes Universally Composable (UC) execution, emulation, dummy-adversary
completeness, and single-session composition in the presence of a shared **global setup**
functionality `G : UC.GlobalSetup GSpec` (the externalized / global-setup UC paradigm introduced by
[CanettiDPW2007], adapted here to this library's call-bounded, fixed-`n`-party, static-corruption
port model; theorem and page locators in the TCC 2007 proceedings were not inspected directly).

## Model and scope

* **Shared global setup:** A global setup `G : UC.GlobalSetup GSpec` maps each security parameter
  `κ : ℕ` to a closed interactive machine `G κ : Machine OracleSpec.empty GSpec`. The environment
  `Z`, the adversary/simulator `A`/`S`, and the protocol `π` (as well as any outer hybrid protocol
  `ρ` and its subroutine `σ`) share oracle access to the **same** live stateful instance `G κ`.
* **Non-programmability by the simulator:** In `GlobalExec G π A C Z κ z`, `Z` calls `GSpec`
  directly alongside the party port and `A`; neither `A` nor `S` sits between `Z` and `G`, so `S`
  may query `G κ` but cannot intercept, reset, or equivocate `G`'s answers to `Z` or honest
  parties.
* **Call-bounded budgets:** As throughout `CslibFrontier/Crypto/Protocols/UC`, budgets
  (`Machine.IsBounded`, `PolyBounded`) count oracle calls and private samples per activation only,
  leaving local computation unbounded (`#6043`). Single-session shared-setup EUC composition
  (`gCompose`) replaces one subroutine `π` with `φ` inside a hybrid protocol `ρ` that may also
  query `GSpec`, while dynamic-SID composition and computational PPT machines remain open
  (`#6043`).

## Main definitions

* `Cslib.Crypto.Protocols.UC.GlobalSetup`, `Cslib.Crypto.Protocols.UC.GlobalProtocol`,
  `Cslib.Crypto.Protocols.UC.GlobalAdversary`, `Cslib.Crypto.Protocols.UC.GlobalExecAdversary`,
  `Cslib.Crypto.Protocols.UC.GlobalEnvironment`,
  `Cslib.Crypto.Protocols.UC.GlobalHybridProtocol`: participants sharing a global setup `GSpec`.
* `Cslib.Crypto.Protocols.UC.GlobalExec`, `Cslib.Crypto.Protocols.UC.gAdvantage`: UC execution and
  distinguishing advantage with a shared global setup `G`.
* `Cslib.Crypto.Protocols.UC.GEmulatesWithin`, `Cslib.Crypto.Protocols.UC.GRealizesWithin`,
  `Cslib.Crypto.Protocols.UC.GEmulatesDummyWithin`,
  `Cslib.Crypto.Protocols.UC.GEmulatesBlackBoxWithin`, `Cslib.Crypto.Protocols.UC.GEmulates`,
  `Cslib.Crypto.Protocols.UC.GRealizes`, `Cslib.Crypto.Protocols.UC.GEmulatesDummy`: concrete and
  asymptotic global-setup emulation notions.
* `Cslib.Crypto.Protocols.UC.gDummyAdversary`, `Cslib.Crypto.Protocols.UC.gCompSim`,
  `Cslib.Crypto.Protocols.UC.gAbsorbAdversary`: dummy adversary, black-box simulator, and absorbed
  environment sharing `GSpec`.
* `Cslib.Crypto.Protocols.UC.gCompose`, `Cslib.Crypto.Protocols.UC.gAbsorbHybrid`,
  `Cslib.Crypto.Protocols.UC.gHybridSim`: single-session shared-setup subroutine replacement and
  composed simulator.
* `Cslib.Crypto.Protocols.UC.coinSetup`, `Cslib.Crypto.Protocols.UC.coinReaderProto`,
  `Cslib.Crypto.Protocols.UC.localCoinProto`, `Cslib.Crypto.Protocols.UC.indepCoinFunc`:
  local-vs-global non-programmable setup separation objects.

## Main results

* `Cslib.Crypto.Protocols.UC.GEmulatesWithin.refl`,
  `Cslib.Crypto.Protocols.UC.GEmulatesWithin.trans`,
  `Cslib.Crypto.Protocols.UC.GEmulates.refl`, `Cslib.Crypto.Protocols.UC.GEmulates.trans`:
  preorder properties of global-setup emulation.
* `Cslib.Crypto.Protocols.UC.GEmulatesDummyWithin.gEmulatesWithin`,
  `Cslib.Crypto.Protocols.UC.GEmulatesWithin.gEmulatesDummyWithin`,
  `Cslib.Crypto.Protocols.UC.gEmulates_iff_gEmulatesDummy`: completeness of the dummy adversary
  with respect to a shared global setup `G`.
* `Cslib.Crypto.Protocols.UC.GEmulatesDummyWithin.compose`,
  `Cslib.Crypto.Protocols.UC.GEmulatesWithin.compose`,
  `Cslib.Crypto.Protocols.UC.GEmulates.compose`, `Cslib.Crypto.Protocols.UC.GRealizes.compose`,
  `Cslib.Crypto.Protocols.UC.GRealizes.compose_trans`: single-session shared-setup EUC
  composition.
* `Cslib.Crypto.Protocols.UC.localCoinProto_realizesWithin_indepCoinFunc`,
  `Cslib.Crypto.Protocols.UC.localCoinProto_realizes_indepCoinFunc`,
  `Cslib.Crypto.Protocols.UC.not_gRealizesWithin_coinSetup`,
  `Cslib.Crypto.Protocols.UC.not_gRealizes_coinSetup`: separation between plain UC realization with
  a local setup (`0` advantage) and GUC impossibility against a shared non-programmable `G` (`≥ 1/2`
  advantage against every simulator).

## References

* [R. Canetti, Y. Dodis, R. Pass, S. Walfish, *Universally Composable Security with Global
  Setup*][CanettiDPW2007], TCC 2007 (LNCS 4392, pp. 61–85; motivation only; exact section and
  theorem locators not verified from the TCC proceedings): externalized/global-setup UC execution,
  dummy-adversary completeness, shared-setup composition, and non-programmable-setup separation.
* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 4: the underlying
  call-bounded UC execution model adapted by `CslibFrontier.Crypto.Protocols.UC.Execution`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open OracleComp (sumHandler)
open scoped NNReal ENNReal

variable {n : ℕ} {In Out NetQ NetR NetQ₁ NetR₁ NetQ₂ NetR₂ NetQ₃ NetR₃ AdvQ AdvR : Type}
  {BackQ BackR SubIn SubOut NQ NR NQ₁ NR₁ NQ₂ NR₂ α : Type}
  {ιG : Type} {GSpec : ιG → Type}

/-! ### Global setup, participants, and shared-port wiring -/

/-- A global setup machine indexed by security parameter `κ`, exporting interface `GSpec`. Unlike a
local protocol, `G` does not depend on any single session's corrupted-party set `C`. -/
abbrev GlobalSetup {ιG : Type} (GSpec : ιG → Type) : Type 1 :=
  ℕ → Machine OracleSpec.empty GSpec

/-- An `n`-party protocol in the `GSpec`-global-setup model: its activations may call `GSpec`. -/
abbrev GlobalProtocol (n : ℕ) (In Out NetQ NetR : Type) {ιG : Type} (GSpec : ιG → Type) : Type 1 :=
  ℕ → Finset (Fin n) → Machine GSpec (protocolSpec n In Out NetQ NetR)

/-- An adversary (or simulator) with direct oracle access to `GSpec` alongside the network port. -/
abbrev GlobalAdversary (n : ℕ) (AdvQ AdvR NetQ NetR : Type) {ιG : Type} (GSpec : ιG → Type) :
    Type 1 :=
  ℕ → Finset (Fin n) → Machine (netSpec NetQ NetR ⊕ₒ GSpec) (netSpec AdvQ AdvR)

/-- An adversary in the global-setup UC execution of an `n`-party protocol behind static-corruption
routing. -/
abbrev GlobalExecAdversary (n : ℕ) (In Out NetQ NetR AdvQ AdvR : Type) {ιG : Type}
    (GSpec : ιG → Type) : Type 1 :=
  GlobalAdversary n AdvQ AdvR (RoutedNetQ n In NetQ) (RoutedNetR Out NetR) GSpec

/-- An environment in the global-setup UC execution: besides the party and adversary ports, it has
direct oracle access to `GSpec` that no adversary or simulator intercepts. -/
abbrev GlobalEnvironment (n : ℕ) (In Out AdvQ AdvR : Type) {ιG : Type} (GSpec : ιG → Type) :
    Type :=
  ℕ → List Bool → ProbOracleComp (execSpec n In Out AdvQ AdvR ⊕ₒ GSpec) Bool

/-- Viewing a closed `IdealFunctionality` as a `GlobalProtocol` that makes no calls to `GSpec`. -/
@[expose] def IdealFunctionality.toGlobalProtocol (F : IdealFunctionality n In Out BackQ BackR) :
    GlobalProtocol n In Out BackQ BackR GSpec :=
  fun κ C => {
    State := F.State
    init := F.init κ C
    handle
      | .inl (i, x) => fun s => ProbOracleComp.sample ((F.onInput i x).run s)
      | .inr q => fun s => ProbOracleComp.sample ((F.onBackdoor q).run s) }

/-- Exposes a machine's imported interface `I` directly alongside its exported interface `E` so
external callers and the machine share the same live `I` instance. -/
@[expose] def shareRight {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type} (M : Machine I E) :
    Machine I (E ⊕ₒ I) where
  State := M.State
  init := M.init
  handle
    | .inl e => M.handle e
    | .inr i => StateT.lift (ProbOracleComp.query i)

/-- Exposes the shared right-hand port `I` on `M : Machine (L ⊕ₒ I) E` without intercepting it. -/
@[expose] def passRight {ιL ιE ιI : Type} {L : ιL → Type} {E : ιE → Type} {I : ιI → Type}
    (M : Machine (L ⊕ₒ I) E) : Machine (L ⊕ₒ I) (E ⊕ₒ I) where
  State := M.State
  init := M.init
  handle
    | .inl e => M.handle e
    | .inr i => StateT.lift (ProbOracleComp.query (spec := L ⊕ₒ I) (Sum.inr i))

/-- Lift a program over `(netSpec NetQ NetR ⊕ₒ GSpec)` to `(protocolSpec n In Out NetQ NetR ⊕ₒ
GSpec)` by sending network queries to `protocolSpec`'s right branch and keeping `GSpec` direct. -/
@[expose] def liftNetWithG (program : ProbOracleComp (netSpec NetQ NetR ⊕ₒ GSpec) α) :
    ProbOracleComp (protocolSpec n In Out NetQ NetR ⊕ₒ GSpec) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec
        (protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)) (Sum.inl k))
      fun
        | .inl q => ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)
            (Sum.inl (Sum.inr q))
        | .inr g => ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)
            (Sum.inr g))
    program

/-- Lift an adversary `A` talking to `(netSpec NetQ NetR ⊕ₒ GSpec)` into a machine on
`(execSpec n In Out AdvQ AdvR ⊕ₒ GSpec)` that forwards party queries and direct `GSpec` queries
unchanged. -/
@[expose] def gLiftAdversary
    (A : Machine (netSpec NetQ NetR ⊕ₒ GSpec) (netSpec AdvQ AdvR)) :
    Machine (protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)
      (execSpec n In Out AdvQ AdvR ⊕ₒ GSpec) where
  State := A.State
  init := A.init
  handle
    | .inl (.inl p) => StateT.lift (ProbOracleComp.query
        (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec) (Sum.inl (Sum.inl p)))
    | .inl (.inr q) => fun s => liftNetWithG ((A.handle q).run s)
    | .inr g => StateT.lift (ProbOracleComp.query
        (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec) (Sum.inr g))

/-- Sharing the global port commutes with composition. -/
private theorem shareRight_comp_shareRight {ιI ιE₁ ιE₂ : Type} {I : ιI → Type}
    {E₁ : ιE₁ → Type} {E₂ : ιE₂ → Type} (A : Machine (E₁ ⊕ₒ I) E₂) (P : Machine I E₁) :
    shareRight (A.comp (shareRight P)) = (passRight A).comp (shareRight P) := by
  simp only [shareRight, passRight, Machine.comp]
  congr 1 with q s : 2
  cases q with
  | inl e => rfl
  | inr i =>
    change (StateT.lift (ProbOracleComp.query (spec := I) i)).run s =
      Equiv.prodAssoc _ _ _ <$> (shareRight P).runFrom
        ((StateT.lift (ProbOracleComp.query (spec := E₁ ⊕ₒ I) (Sum.inr i))).run s.1) s.2
    simp only [StateT.run_lift, bind_pure_comp]
    dsimp only [shareRight]
    rfl

/-! ### Global-setup UC execution and advantage -/

/-- The closed execution machine for protocol `π`, adversary `A`, and shared global setup `G`. -/
@[expose] def gExecMachine (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec)
    (A : GlobalExecAdversary n In Out NetQ NetR AdvQ AdvR GSpec)
    (κ : ℕ) (C : Finset (Fin n)) :
    Machine OracleSpec.empty (execSpec n In Out AdvQ AdvR ⊕ₒ GSpec) :=
  ((gLiftAdversary (A κ C)).comp (shareRight (routeCorrupt C (π κ C)))).comp (G κ)

/-- The global-setup UC execution experiment: the environment's output bit when interacting with
protocol `π`, adversary `A`, and shared global setup `G`, with corrupted parties `C`, security
parameter `κ`, and auxiliary input `z`. -/
@[expose] def GlobalExec (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec)
    (A : GlobalExecAdversary n In Out NetQ NetR AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) : ProbComp Bool :=
  (gExecMachine G π A κ C).run (Z κ z)

/-- The distinguishing advantage of environment `Z` between `(π, A, G)` and `(φ, S, G)`. -/
@[expose] noncomputable def gAdvantage (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (A : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
    (S : GlobalExecAdversary n In Out NetQ₂ NetR₂ AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) : NNReal :=
  Game.advantage (GlobalExec G π A C Z κ z).eval (GlobalExec G φ S C Z κ z).eval

/-- Every execution with a shared global setup has zero advantage against itself. -/
@[simp] theorem gAdvantage_self (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec)
    (A : GlobalExecAdversary n In Out NetQ NetR AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) :
    gAdvantage G π π A A C Z κ z = 0 :=
  Game.advantage_self _

/-- The global-setup distinguishing advantage is symmetric. -/
theorem gAdvantage_comm (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (A : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
    (S : GlobalExecAdversary n In Out NetQ₂ NetR₂ AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) :
    gAdvantage G π φ A S C Z κ z = gAdvantage G φ π S A C Z κ z :=
  Game.advantage_comm _ _

/-- Triangle inequality for the global-setup distinguishing advantage. -/
theorem gAdvantage_triangle (G : GlobalSetup GSpec)
    (π₁ : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (π₂ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (π₃ : GlobalProtocol n In Out NetQ₃ NetR₃ GSpec)
    (A₁ : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
    (A₂ : GlobalExecAdversary n In Out NetQ₂ NetR₂ AdvQ AdvR GSpec)
    (A₃ : GlobalExecAdversary n In Out NetQ₃ NetR₃ AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) :
    gAdvantage G π₁ π₃ A₁ A₃ C Z κ z ≤
      gAdvantage G π₁ π₂ A₁ A₂ C Z κ z + gAdvantage G π₂ π₃ A₂ A₃ C Z κ z :=
  Game.advantage_triangle _ _ _

/-! ### Budgets and global-setup emulation notions -/

/-- Polynomial oracle-call-count bound on a global-setup protocol. -/
@[expose] def GlobalProtocol.PolyBounded
    (π : GlobalProtocol n In Out NetQ NetR GSpec) (p : Polynomial ℕ) : Prop :=
  ∀ κ C, (π κ C).IsBounded (p.eval κ)

/-- Polynomial oracle-call-count bound on a global-setup adversary. -/
@[expose] def GlobalAdversary.PolyBounded
    (A : GlobalAdversary n AdvQ AdvR NetQ NetR GSpec) (p : Polynomial ℕ) : Prop :=
  ∀ κ C, (A κ C).IsBounded (p.eval κ)

/-- Polynomial oracle-call-count bound on a global-setup environment. -/
@[expose] def GlobalEnvironment.PolyBounded
    (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec) (p : Polynomial ℕ) : Prop :=
  ∀ κ z, (Z κ z).IsQueryBounded (p.eval κ)

/-- Concrete UC emulation with shared global setup `G`: every adversary `A` with budget `pA` has a
simulator `S` with budget `pS` bounded by `g (κ + pA κ)` (accessing `GSpec` directly, without
intercepting `Z`'s or honest parties' calls to `G`) such that every environment with budget `pZ`
has advantage at most `ε pA pZ κ`. -/
@[expose] def GEmulatesWithin (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  ∀ (AdvQ AdvR : Type) (A : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
    (pA : Polynomial ℕ), A.PolyBounded pA →
    ∃ (S : GlobalExecAdversary n In Out NetQ₂ NetR₂ AdvQ AdvR GSpec) (pS : Polynomial ℕ),
      S.PolyBounded pS ∧ SimPolyBound g pA pS ∧
        ∀ (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
          (pZ : Polynomial ℕ), Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
            gAdvantage G π φ A S C Z κ z ≤ ε pA pZ κ

/-- Concrete UC realization of an ideal functionality `F` in the `G`-global-setup model. -/
abbrev GRealizesWithin (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec)
    (F : IdealFunctionality n In Out BackQ BackR)
    (g : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  GEmulatesWithin G π F.toGlobalProtocol g ε

namespace GEmulatesWithin

/-- Concrete global-setup emulation is preserved by weakening the error bound. -/
theorem mono {G : GlobalSetup GSpec}
    {π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec}
    {φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec}
    {g : Polynomial ℕ} {ε ε' : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : GEmulatesWithin G π φ g ε) (hε : ∀ pA pZ κ, ε pA pZ κ ≤ ε' pA pZ κ) :
    GEmulatesWithin G π φ g ε' := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hSg, hadv⟩ := h AdvQ AdvR A pA hA
  exact ⟨S, pS, hS, hSg, fun C Z pZ hZ κ z => (hadv C Z pZ hZ κ z).trans (hε pA pZ κ)⟩

/-- Every global-setup protocol emulates itself with zero error: the adversary is its own simulator.
-/
theorem refl (G : GlobalSetup GSpec) (π : GlobalProtocol n In Out NetQ NetR GSpec) :
    GEmulatesWithin G π π Polynomial.X (fun _ _ _ => 0) :=
  fun _ _ A pA hA => ⟨A, pA, hA, SimPolyBound.refl pA, fun C Z _ _ κ z => by simp⟩

/-- Transitivity of concrete global-setup emulation. If `π₁` emulates `π₂` with overhead `g₁₂` and
error `ε₁₂`, and `π₂` emulates `π₃` with overhead `g₂₃` and error `ε₂₃` monotone in the adversary's
budget, then `π₁` emulates `π₃` with the composed overhead and the summed error. -/
theorem trans {G : GlobalSetup GSpec}
    {π₁ : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec}
    {π₂ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec}
    {π₃ : GlobalProtocol n In Out NetQ₃ NetR₃ GSpec}
    {g₁₂ g₂₃ : Polynomial ℕ} {ε₁₂ ε₂₃ : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h₁₂ : GEmulatesWithin G π₁ π₂ g₁₂ ε₁₂) (h₂₃ : GEmulatesWithin G π₂ π₃ g₂₃ ε₂₃)
    (hmono : ∀ p p' pZ κ, (∀ κ', p.eval κ' ≤ p'.eval κ') → ε₂₃ p pZ κ ≤ ε₂₃ p' pZ κ) :
    GEmulatesWithin G π₁ π₃ (g₂₃.comp (Polynomial.X + g₁₂))
      (fun pA pZ κ => ε₁₂ pA pZ κ + ε₂₃ (g₁₂.comp (Polynomial.X + pA)) pZ κ) := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S₂, pS₂, hS₂, hS₂g, hadv₁₂⟩ := h₁₂ AdvQ AdvR A pA hA
  obtain ⟨S₃, pS₃, hS₃, hS₃g, hadv₂₃⟩ := h₂₃ AdvQ AdvR S₂ pS₂ hS₂
  refine ⟨S₃, pS₃, hS₃, hS₂g.trans hS₃g, fun C Z pZ hZ κ z => ?_⟩
  calc gAdvantage G π₁ π₃ A S₃ C Z κ z
      ≤ gAdvantage G π₁ π₂ A S₂ C Z κ z + gAdvantage G π₂ π₃ S₂ S₃ C Z κ z :=
        gAdvantage_triangle G π₁ π₂ π₃ A S₂ S₃ C Z κ z
    _ ≤ ε₁₂ pA pZ κ + ε₂₃ (g₁₂.comp (Polynomial.X + pA)) pZ κ :=
        add_le_add (hadv₁₂ C Z pZ hZ κ z)
          ((hadv₂₃ C Z pZ hZ κ z).trans (hmono _ _ pZ κ hS₂g.le_eval_comp))

end GEmulatesWithin

/-- Asymptotic UC emulation with shared global setup `G` and negligible error. -/
@[expose] def GEmulates (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec) : Prop :=
  ∀ (AdvQ AdvR : Type) (A : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
    (pA : Polynomial ℕ), A.PolyBounded pA →
    ∃ (S : GlobalExecAdversary n In Out NetQ₂ NetR₂ AdvQ AdvR GSpec) (pS : Polynomial ℕ),
      S.PolyBounded pS ∧
        ∀ pZ : Polynomial ℕ, ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
          ∀ (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec),
            Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool), gAdvantage G π φ A S C Z κ z ≤ ν κ

/-- Asymptotic UC realization of an ideal functionality `F` with shared global setup `G`. -/
abbrev GRealizes (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec)
    (F : IdealFunctionality n In Out BackQ BackR) : Prop :=
  GEmulates G π F.toGlobalProtocol

/-- Concrete global-setup emulation with negligible error implies asymptotic global-setup emulation.
-/
theorem GEmulatesWithin.gEmulates {G : GlobalSetup GSpec}
    {π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec}
    {φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec}
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : GEmulatesWithin G π φ g ε) (hε : ∀ pA pZ, Negligible (ε pA pZ)) :
    GEmulates G π φ := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, _, hadv⟩ := h AdvQ AdvR A pA hA
  exact ⟨S, pS, hS, fun pZ => ⟨ε pA pZ, hε pA pZ, fun C Z hZ κ z => hadv C Z pZ hZ κ z⟩⟩

namespace GEmulates

/-- Every global-setup protocol emulates itself. -/
theorem refl (G : GlobalSetup GSpec) (π : GlobalProtocol n In Out NetQ NetR GSpec) :
    GEmulates G π π :=
  (GEmulatesWithin.refl G π).gEmulates fun _ _ => negligible_zero

/-- Asymptotic global-setup emulation is transitive. -/
theorem trans {G : GlobalSetup GSpec}
    {π₁ : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec}
    {π₂ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec}
    {π₃ : GlobalProtocol n In Out NetQ₃ NetR₃ GSpec}
    (h₁₂ : GEmulates G π₁ π₂) (h₂₃ : GEmulates G π₂ π₃) : GEmulates G π₁ π₃ := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S₂, pS₂, hS₂, hadv₁₂⟩ := h₁₂ AdvQ AdvR A pA hA
  obtain ⟨S₃, pS₃, hS₃, hadv₂₃⟩ := h₂₃ AdvQ AdvR S₂ pS₂ hS₂
  refine ⟨S₃, pS₃, hS₃, fun pZ => ?_⟩
  obtain ⟨ν₁₂, hν₁₂, h₁⟩ := hadv₁₂ pZ
  obtain ⟨ν₂₃, hν₂₃, h₂⟩ := hadv₂₃ pZ
  refine ⟨ν₁₂ + ν₂₃, hν₁₂.add hν₂₃, fun C Z hZ κ z => ?_⟩
  exact (gAdvantage_triangle G π₁ π₂ π₃ A S₂ S₃ C Z κ z).trans
    (add_le_add (h₁ C Z hZ κ z) (h₂ C Z hZ κ z))

end GEmulates

/-! ### Dummy adversary and black-box completeness with global setup -/

/-- The dummy adversary in the global-setup model forwards network queries directly to the
protocol's network port while leaving the environment's direct `GSpec` access untouched. -/
@[expose] def gDummyAdversary (n : ℕ) (NetQ NetR : Type) {ιG : Type} (GSpec : ιG → Type) :
    GlobalAdversary n NetQ NetR NetQ NetR GSpec :=
  fun _ _ => {
    State := PUnit
    init := pure PUnit.unit
    handle := fun q => StateT.lift (ProbOracleComp.query (spec := netSpec NetQ NetR ⊕ₒ GSpec)
      (Sum.inl q)) }

/-- The black-box simulator running `A` on top of a dummy-adversary simulator `S_D`, with `A`'s
direct calls to `GSpec` passing around `S_D` directly to the global setup. -/
@[expose] def gCompSim
    (S_D : GlobalAdversary n NetQ₁ NetR₁ NetQ₂ NetR₂ GSpec)
    (A : GlobalAdversary n AdvQ AdvR NetQ₁ NetR₁ GSpec) :
    GlobalAdversary n AdvQ AdvR NetQ₂ NetR₂ GSpec :=
  fun κ C => (A κ C).comp (passRight (S_D κ C))

/-- The environment absorbing `A` internally: `Z`'s adversary queries go to `A`, `A`'s network
queries go to the dummy adversary, and both `Z`'s and `A`'s `GSpec` queries go directly to `G`. -/
@[expose] def gAbsorbAdversary (C : Finset (Fin n))
    (A : GlobalAdversary n AdvQ AdvR NetQ NetR GSpec)
    (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec) :
    GlobalEnvironment n In Out NetQ NetR GSpec :=
  fun κ z => (gLiftAdversary (A κ C)).link (Z κ z)

private theorem gLiftAdversary_dummy (n : ℕ) (NetQ NetR : Type) {ιG : Type} (GSpec : ιG → Type)
    (κ : ℕ) (C : Finset (Fin n)) :
    gLiftAdversary (n := n) (In := In) (Out := Out)
      (gDummyAdversary n NetQ NetR GSpec κ C) =
      Machine.id (protocolSpec n In Out NetQ NetR ⊕ₒ GSpec) := by
  have hhandle :
      (gLiftAdversary (n := n) (In := In) (Out := Out)
        (gDummyAdversary n NetQ NetR GSpec κ C)).handle =
        (Machine.id (protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)).handle := by
    funext q s
    rcases q with ⟨p | q⟩ | g
    · rfl
    · change liftNetWithG ((StateT.lift (ProbOracleComp.query
          (spec := netSpec NetQ NetR ⊕ₒ GSpec) (Sum.inl q))).run s) = _
      simp only [StateT.run_lift, liftNetWithG, bind_pure_comp]
      rfl
    · rfl
  exact congrArg (Machine.mk PUnit (pure PUnit.unit)) hhandle

private theorem gExec_eq_run_shareRight_link (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec)
    (A : GlobalExecAdversary n In Out NetQ NetR AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) :
    GlobalExec G π A C Z κ z =
      (G κ).run ((shareRight (routeCorrupt C (π κ C))).link
        ((gLiftAdversary (A κ C)).link (Z κ z))) := by
  simp only [GlobalExec, gExecMachine, Machine.run_comp, Machine.link_comp]

/-- Running the dummy adversary runs `shareRight (routeCorrupt C (π κ C))` directly inside `G`. -/
@[simp] theorem gExec_dummyAdversary (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec) (C : Finset (Fin n))
    (Z : GlobalEnvironment n In Out (RoutedNetQ n In NetQ) (RoutedNetR Out NetR) GSpec)
    (κ : ℕ) (z : List Bool) :
    GlobalExec G π (gDummyAdversary n _ _ GSpec) C Z κ z =
      (G κ).run ((shareRight (routeCorrupt C (π κ C))).link (Z κ z)) := by
  rw [gExec_eq_run_shareRight_link, gLiftAdversary_dummy, Machine.link_id]

/-- Absorbing `A` into `Z` equals running `A` against the dummy adversary, as an equation of
programs. -/
theorem gExec_eq_gExec_dummy (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ NetR GSpec)
    (A : GlobalExecAdversary n In Out NetQ NetR AdvQ AdvR GSpec) (C : Finset (Fin n))
    (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec) (κ : ℕ) (z : List Bool) :
    GlobalExec G π A C Z κ z =
      GlobalExec G π (gDummyAdversary n _ _ GSpec) C (gAbsorbAdversary C A Z) κ z := by
  rw [gExec_eq_run_shareRight_link, gExec_dummyAdversary, gAbsorbAdversary]

private theorem liftNetWithG_pure (a : α) :
    liftNetWithG (n := n) (In := In) (Out := Out) (pure a :
      ProbOracleComp (netSpec NetQ NetR ⊕ₒ GSpec) α) = pure a := rfl

private theorem liftNetWithG_bind {β : Type}
    (program : ProbOracleComp (netSpec NetQ NetR ⊕ₒ GSpec) α)
    (next : α → ProbOracleComp (netSpec NetQ NetR ⊕ₒ GSpec) β) :
    liftNetWithG (n := n) (In := In) (Out := Out) (program >>= next) =
      liftNetWithG program >>= fun a => liftNetWithG (next a) :=
  OracleComp.interpret_bind _ _ _

private theorem liftNetWithG_map {β : Type} (f : α → β)
    (program : ProbOracleComp (netSpec NetQ NetR ⊕ₒ GSpec) α) :
    liftNetWithG (n := n) (In := In) (Out := Out) (f <$> program) = f <$> liftNetWithG program :=
  OracleComp.interpret_map _ _ _

private theorem liftNetWithG_sample (program : ProbComp α) :
    liftNetWithG (n := n) (In := In) (Out := Out)
      (ProbOracleComp.sample (spec := netSpec NetQ NetR ⊕ₒ GSpec) program) =
      ProbOracleComp.sample program := by
  simp only [liftNetWithG, ProbOracleComp.interpret_sample]
  exact (OracleComp.substitute_eq_interpret _ _).symm

private theorem runFrom_gLiftAdversary_liftNetWithG
    (S : Machine (netSpec NetQ₂ NetR₂ ⊕ₒ GSpec) (netSpec NetQ₁ NetR₁))
    (program : ProbOracleComp (netSpec NetQ₁ NetR₁ ⊕ₒ GSpec) α) (s : S.State) :
    (gLiftAdversary (n := n) (In := In) (Out := Out) S).runFrom (liftNetWithG program) s =
      liftNetWithG ((passRight S).runFrom program s) := by
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    simp only [PFunctor.FreeM.bind_eq_bind]
    cases q with
    | inl k =>
      have hs : liftNetWithG (n := n) (In := In) (Out := Out)
          (OracleComp.query (spec := probOracleSpec (netSpec NetQ₁ NetR₁ ⊕ₒ GSpec)) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← liftNetWithG_sample]
        rfl
      have hrunS : (passRight S).runFrom
          (OracleComp.query (spec := probOracleSpec (netSpec NetQ₁ NetR₁ ⊕ₒ GSpec)) (Sum.inl k))
            s =
          (fun a => (a, s)) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
        (passRight S).runFrom_sample (ProbComp.unifFin k) s
      rw [liftNetWithG_bind, hs]
      erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]
      erw [Machine.runFrom_bind, hrunS, bind_map_left, liftNetWithG_bind, liftNetWithG_sample]
      exact bind_congr fun a => ih a s
    | inr e =>
      cases e with
      | inl nq =>
        have hq : liftNetWithG (n := n) (In := In) (Out := Out)
            (OracleComp.query (spec := probOracleSpec (netSpec NetQ₁ NetR₁ ⊕ₒ GSpec))
              (Sum.inr (Sum.inl nq))) =
            ProbOracleComp.query (spec := protocolSpec n In Out NetQ₁ NetR₁ ⊕ₒ GSpec)
              (Sum.inl (Sum.inr nq)) := rfl
        rw [liftNetWithG_bind, hq]
        erw [Machine.runFrom_bind, Machine.runFrom_query]
        erw [Machine.runFrom_bind, Machine.runFrom_query, liftNetWithG_bind]
        exact bind_congr fun x => ih x.1 x.2
      | inr g =>
        have hg : liftNetWithG (n := n) (In := In) (Out := Out)
            (OracleComp.query (spec := probOracleSpec (netSpec NetQ₁ NetR₁ ⊕ₒ GSpec))
              (Sum.inr (Sum.inr g))) =
            ProbOracleComp.query (spec := protocolSpec n In Out NetQ₁ NetR₁ ⊕ₒ GSpec)
              (Sum.inr g) := rfl
        rw [liftNetWithG_bind, hg]
        erw [Machine.runFrom_bind, Machine.runFrom_query]
        erw [Machine.runFrom_bind, Machine.runFrom_query, liftNetWithG_bind]
        have hstep₁ : ((gLiftAdversary (n := n) (In := In) (Out := Out) S).handle (Sum.inr g)).run
              (s : (gLiftAdversary (n := n) (In := In) (Out := Out) S).State) =
            (fun a => (a, (s : (gLiftAdversary (n := n) (In := In) (Out := Out) S).State))) <$>
              ProbOracleComp.query
                (spec := protocolSpec n In Out NetQ₂ NetR₂ ⊕ₒ GSpec) (Sum.inr g) := by
          dsimp only [gLiftAdversary]
          rw [StateT.run_lift, bind_pure_comp]
        have hstep₂ : ((passRight S).handle (Sum.inr g)).run (s : (passRight S).State) =
            (fun a => (a, (s : (passRight S).State))) <$> ProbOracleComp.query
              (spec := netSpec NetQ₂ NetR₂ ⊕ₒ GSpec) (Sum.inr g) := by
          dsimp only [passRight]
          rw [StateT.run_lift, bind_pure_comp]
        erw [hstep₁, hstep₂, bind_map_left, liftNetWithG_map, bind_map_left]
        exact bind_congr fun a => ih a s

private theorem gLiftAdversary_comp
    (A : Machine (netSpec NetQ₁ NetR₁ ⊕ₒ GSpec) (netSpec AdvQ AdvR))
    (S : Machine (netSpec NetQ₂ NetR₂ ⊕ₒ GSpec) (netSpec NetQ₁ NetR₁)) :
    gLiftAdversary (n := n) (In := In) (Out := Out) (A.comp (passRight S)) =
      (gLiftAdversary A).comp (gLiftAdversary S) := by
  have hhandle :
      (gLiftAdversary (n := n) (In := In) (Out := Out) (A.comp (passRight S))).handle =
        ((gLiftAdversary A).comp (gLiftAdversary S)).handle := by
    funext q s
    rcases q with ⟨p | q⟩ | g
    · change (StateT.lift (ProbOracleComp.query
          (spec := protocolSpec n In Out NetQ₂ NetR₂ ⊕ₒ GSpec) (Sum.inl (Sum.inl p)))).run s =
        Equiv.prodAssoc _ _ _ <$> (gLiftAdversary S).runFrom
          ((StateT.lift (ProbOracleComp.query
            (spec := protocolSpec n In Out NetQ₁ NetR₁ ⊕ₒ GSpec) (Sum.inl (Sum.inl p)))).run s.1)
          s.2
      simp only [StateT.run_lift, bind_pure_comp]
      dsimp only [gLiftAdversary]
      rfl
    · change liftNetWithG (Equiv.prodAssoc _ _ _ <$>
          (passRight S).runFrom ((A.handle q).run s.1) s.2) =
        Equiv.prodAssoc _ _ _ <$> (gLiftAdversary S).runFrom
          (liftNetWithG ((A.handle q).run s.1)) s.2
      rw [liftNetWithG_map]
      erw [runFrom_gLiftAdversary_liftNetWithG]
      rfl
    · change (StateT.lift (ProbOracleComp.query
          (spec := protocolSpec n In Out NetQ₂ NetR₂ ⊕ₒ GSpec) (Sum.inr g))).run s =
        Equiv.prodAssoc _ _ _ <$> (gLiftAdversary S).runFrom
          ((StateT.lift (ProbOracleComp.query
            (spec := protocolSpec n In Out NetQ₁ NetR₁ ⊕ₒ GSpec) (Sum.inr g))).run s.1) s.2
      simp only [StateT.run_lift, bind_pure_comp]
      dsimp only [gLiftAdversary]
      rfl
  exact congrArg (Machine.mk (A.State × S.State)
    ((A.comp (passRight S)).init)) hhandle

/-- Running the black-box simulator `gCompSim S_D A` equals running `S_D` against the absorbed
environment `gAbsorbAdversary C A Z`. -/
theorem gExec_gCompSim (G : GlobalSetup GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (S_D : GlobalAdversary n (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁)
      (RoutedNetQ n In NetQ₂) (RoutedNetR Out NetR₂) GSpec)
    (A : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) :
    GlobalExec G φ (gCompSim S_D A) C Z κ z =
      GlobalExec G φ S_D C (gAbsorbAdversary C A Z) κ z := by
  simp only [gExec_eq_run_shareRight_link, gCompSim, gLiftAdversary_comp, gAbsorbAdversary,
    Machine.link_comp]

/-- The advantage against the black-box simulator `gCompSim S_D A` equals the advantage between the
dummy adversary and `S_D` for the absorbed environment `gAbsorbAdversary C A Z`. -/
theorem gAdvantage_gCompSim (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (S_D : GlobalAdversary n (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁)
      (RoutedNetQ n In NetQ₂) (RoutedNetR Out NetR₂) GSpec)
    (A : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
    (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
    (κ : ℕ) (z : List Bool) :
    gAdvantage G π φ A (gCompSim S_D A) C Z κ z =
      gAdvantage G π φ (gDummyAdversary n _ _ GSpec) S_D C (gAbsorbAdversary C A Z) κ z := by
  rw [gAdvantage, gAdvantage, gExec_eq_gExec_dummy, gExec_gCompSim]

/-- Absorbing the dummy adversary into an environment leaves the environment unchanged. -/
@[simp] theorem gAbsorbAdversary_dummy (C : Finset (Fin n))
    (Z : GlobalEnvironment n In Out NetQ NetR GSpec) :
    gAbsorbAdversary C (gDummyAdversary n NetQ NetR GSpec) Z = Z := by
  funext κ z
  simp only [gAbsorbAdversary, gLiftAdversary_dummy, Machine.link_id]

/-- Running `S_D` behind the dummy adversary in `gCompSim` does not change its advantage against the
dummy adversary. -/
theorem gAdvantage_gCompSim_dummy (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (S_D : GlobalAdversary n (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁)
      (RoutedNetQ n In NetQ₂) (RoutedNetR Out NetR₂) GSpec)
    (C : Finset (Fin n))
    (Z : GlobalEnvironment n In Out (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁) GSpec)
    (κ : ℕ) (z : List Bool) :
    gAdvantage G π φ (gDummyAdversary n _ _ GSpec)
        (gCompSim S_D (gDummyAdversary n _ _ GSpec)) C Z κ z =
      gAdvantage G π φ (gDummyAdversary n _ _ GSpec) S_D C Z κ z := by
  rw [gAdvantage_gCompSim, gAbsorbAdversary_dummy]

/-! #### Budgets for dummy adversary, black-box simulator, and absorbed environment -/

private theorem isQueryBounded_liftNetWithG
    {program : ProbOracleComp (netSpec NetQ NetR ⊕ₒ GSpec) α} {m : ℕ}
    (h : program.IsQueryBounded m) :
    (liftNetWithG (n := n) (In := In) (Out := Out) program).IsQueryBounded m := by
  dsimp only [liftNetWithG]
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr e =>
    cases e with
    | inl q => exact OracleComp.IsCostBounded.query _
    | inr g => exact OracleComp.IsCostBounded.query _

private theorem isBounded_gLiftAdversary
    {A : Machine (netSpec NetQ NetR ⊕ₒ GSpec) (netSpec AdvQ AdvR)} {t : ℕ} (h : A.IsBounded t) :
    (gLiftAdversary (n := n) (In := In) (Out := Out) A).IsBounded (t + 1) := by
  refine ⟨h.1.mono (by omega), fun q s => ?_⟩
  rcases q with ⟨p | q⟩ | g
  · dsimp only [gLiftAdversary] at s ⊢
    rw [StateT.run_lift, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  · exact (isQueryBounded_liftNetWithG (h.2 q s)).mono (by omega)
  · dsimp only [gLiftAdversary] at s ⊢
    rw [StateT.run_lift, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))

private theorem isBounded_passRight {ιL ιE ιI : Type} {L : ιL → Type} {E : ιE → Type}
    {I : ιI → Type} {M : Machine (L ⊕ₒ I) E} {t : ℕ} (h : M.IsBounded (t + 1)) :
    (passRight M).IsBounded (t + 1) := by
  refine ⟨h.1, fun q s => ?_⟩
  cases q with
  | inl e => exact h.2 e s
  | inr i =>
    dsimp only [passRight] at s ⊢
    rw [StateT.run_lift, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))

private theorem isBounded_shareRight {ιI ιE : Type} {I : ιI → Type} {E : ιE → Type}
    {M : Machine I E} {t : ℕ} (h : M.IsBounded (t + 1)) : (shareRight M).IsBounded (t + 1) := by
  refine ⟨h.1, fun q s => ?_⟩
  cases q with
  | inl e => exact h.2 e s
  | inr i =>
    dsimp only [shareRight] at s ⊢
    rw [StateT.run_lift, bind_pure_comp]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))

/-- The global-setup dummy adversary makes one oracle call per activation. -/
theorem gDummyAdversary_polyBounded (n : ℕ) (NetQ NetR : Type) {ιG : Type} (GSpec : ιG → Type) :
    (gDummyAdversary n NetQ NetR GSpec).PolyBounded 1 := fun _ _ => by
  rw [Polynomial.eval_one]
  refine ⟨OracleComp.IsCostBounded.pure _ 1, fun q s => ?_⟩
  dsimp only [gDummyAdversary] at s ⊢
  rw [StateT.run_lift, bind_pure_comp]
  exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)

/-- The black-box simulator `gCompSim S_D A` has budget `pA * (pD + 2) + (pD + 1)` when `S_D` and
`A` have budgets `pD` and `pA`. -/
theorem gCompSim_polyBounded
    {S_D : GlobalAdversary n NetQ₁ NetR₁ NetQ₂ NetR₂ GSpec}
    {A : GlobalAdversary n AdvQ AdvR NetQ₁ NetR₁ GSpec}
    {pD pA : Polynomial ℕ} (hS : S_D.PolyBounded pD) (hA : A.PolyBounded pA) :
    (gCompSim S_D A).PolyBounded (pA * (pD + 2) + (pD + 1)) := fun κ C => by
  have h := (hA κ C).comp (isBounded_passRight ((hS κ C).mono (Nat.le_succ _)))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat]
  exact h.mono (by ring_nf; omega)

/-- The budget of `gCompSim` is bounded by the simulator overhead `X * (pD + 2) + (pD + 1)` applied
to the adversary's budget. -/
theorem simPolyBound_gCompSim (pD pA : Polynomial ℕ) :
    SimPolyBound (Polynomial.X * (pD + 2) + (pD + 1)) pA (pA * (pD + 2) + (pD + 1)) := fun κ => by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat]
  have hD : pD.eval κ ≤ pD.eval (κ + pA.eval κ) := pD.eval_mono (Nat.le_add_right _ _)
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.add_le_add_right hD 2))
    (Nat.add_le_add_right hD 1)

/-- The absorbed environment `gAbsorbAdversary C A Z` has budget `absorbPoly pZ pA`. -/
theorem gAbsorbAdversary_polyBounded (C : Finset (Fin n))
    {A : GlobalAdversary n AdvQ AdvR NetQ NetR GSpec}
    {Z : GlobalEnvironment n In Out AdvQ AdvR GSpec}
    {pA pZ : Polynomial ℕ} (hA : A.PolyBounded pA) (hZ : Z.PolyBounded pZ) :
    (gAbsorbAdversary C A Z).PolyBounded (absorbPoly pZ pA) := fun κ z => by
  have h := Machine.isQueryBounded_link (isBounded_gLiftAdversary (n := n) (In := In) (Out := Out)
    (hA κ C)) (hZ κ z)
  refine h.mono (le_of_eq ?_)
  rw [eval_absorbPoly]

/-! #### Dummy-adversary and black-box emulation equivalences -/

/-- Concrete global-setup emulation of the dummy adversary. -/
@[expose] def GEmulatesDummyWithin (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  ∃ S_D : GlobalAdversary n (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁)
      (RoutedNetQ n In NetQ₂) (RoutedNetR Out NetR₂) GSpec,
    S_D.PolyBounded pD ∧
      ∀ (C : Finset (Fin n))
        (Z : GlobalEnvironment n In Out (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁) GSpec)
        (pZ : Polynomial ℕ), Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
          gAdvantage G π φ (gDummyAdversary n _ _ GSpec) S_D C Z κ z ≤ ε pZ κ

/-- Concrete global-setup black-box emulation. -/
@[expose] def GEmulatesBlackBoxWithin (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec)
    (pD : Polynomial ℕ) (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  ∃ S_D : GlobalAdversary n (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁)
      (RoutedNetQ n In NetQ₂) (RoutedNetR Out NetR₂) GSpec,
    S_D.PolyBounded pD ∧
      ∀ (AdvQ AdvR : Type)
        (A : GlobalExecAdversary n In Out NetQ₁ NetR₁ AdvQ AdvR GSpec)
        (pA : Polynomial ℕ), A.PolyBounded pA →
        ∀ (C : Finset (Fin n)) (Z : GlobalEnvironment n In Out AdvQ AdvR GSpec)
          (pZ : Polynomial ℕ), Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
            gAdvantage G π φ A (gCompSim S_D A) C Z κ z ≤ ε pA pZ κ

/-- Asymptotic global-setup emulation of the dummy adversary. -/
@[expose] def GEmulatesDummy (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec) : Prop :=
  ∃ (S_D : GlobalAdversary n (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁)
      (RoutedNetQ n In NetQ₂) (RoutedNetR Out NetR₂) GSpec) (pD : Polynomial ℕ),
    S_D.PolyBounded pD ∧
      ∀ pZ : Polynomial ℕ, ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
        ∀ (C : Finset (Fin n))
          (Z : GlobalEnvironment n In Out (RoutedNetQ n In NetQ₁) (RoutedNetR Out NetR₁) GSpec),
          Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
            gAdvantage G π φ (gDummyAdversary n _ _ GSpec) S_D C Z κ z ≤ ν κ

section Completeness

variable {G : GlobalSetup GSpec}
  {π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec}
  {φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec}

/-- A simulator for the global-setup dummy adversary gives black-box emulation through `gCompSim`,
with the error evaluated at the absorbed environment's budget. -/
theorem GEmulatesDummyWithin.gEmulatesBlackBoxWithin {pD : Polynomial ℕ}
    {ε : Polynomial ℕ → ℕ → ℝ≥0} (h : GEmulatesDummyWithin G π φ pD ε) :
    GEmulatesBlackBoxWithin G π φ pD (fun pA pZ => ε (absorbPoly pZ pA)) := by
  obtain ⟨S_D, hS, hadv⟩ := h
  refine ⟨S_D, hS, fun AdvQ AdvR A pA hA C Z pZ hZ κ z => ?_⟩
  rw [gAdvantage_gCompSim]
  exact hadv C _ _ (gAbsorbAdversary_polyBounded C hA hZ) κ z

/-- Black-box global-setup emulation implies concrete global-setup emulation with simulator overhead
`X * (pD + 2) + (pD + 1)`. -/
theorem GEmulatesBlackBoxWithin.gEmulatesWithin {pD : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (h : GEmulatesBlackBoxWithin G π φ pD ε) :
    GEmulatesWithin G π φ (Polynomial.X * (pD + 2) + (pD + 1)) ε := by
  obtain ⟨S_D, hS, hadv⟩ := h
  exact fun AdvQ AdvR A pA hA => ⟨gCompSim S_D A, pA * (pD + 2) + (pD + 1),
    gCompSim_polyBounded hS hA, simPolyBound_gCompSim pD pA, hadv AdvQ AdvR A pA hA⟩

/-- Dummy-adversary completeness (sufficiency) for `GEmulatesDummyWithin`, in this library's
call-bounded (computationally unbounded), fixed-`n`-party, static-corruption shared-setup port model
(#6043), not the polynomial-time ITM GUC dummy-adversary completeness of [CanettiDPW2007]: a
simulator for the dummy adversary with budget `pD` and error `ε` gives concrete global-setup
emulation of every adversary with overhead `X * (pD + 2) + (pD + 1)` and error `ε` at the absorbed
environment's budget. -/
theorem GEmulatesDummyWithin.gEmulatesWithin {pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (h : GEmulatesDummyWithin G π φ pD ε) :
    GEmulatesWithin G π φ (Polynomial.X * (pD + 2) + (pD + 1))
      (fun pA pZ => ε (absorbPoly pZ pA)) :=
  h.gEmulatesBlackBoxWithin.gEmulatesWithin

/-- Dummy-adversary completeness (necessity) for `GEmulatesWithin`, in this library's call-bounded
(computationally unbounded), fixed-`n`-party, static-corruption shared-setup port model (#6043), not
the polynomial-time ITM GUC dummy-adversary completeness of [CanettiDPW2007]: concrete global-setup
emulation specializes to the dummy adversary, giving a dummy simulator whose budget `pD` is bounded
by `g` at adversary budget `1`. -/
theorem GEmulatesWithin.gEmulatesDummyWithin {g : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (h : GEmulatesWithin G π φ g ε) :
    ∃ pD, SimPolyBound g 1 pD ∧ GEmulatesDummyWithin G π φ pD (fun pZ => ε 1 pZ) := by
  obtain ⟨S_D, pD, hS, hg, hadv⟩ := h _ _ (gDummyAdversary n _ _ GSpec) 1
    (gDummyAdversary_polyBounded n _ _ GSpec)
  exact ⟨pD, hg, S_D, hS, hadv⟩

/-- Black-box global-setup emulation specializes to emulation of the dummy adversary. -/
theorem GEmulatesBlackBoxWithin.gEmulatesDummyWithin {pD : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (h : GEmulatesBlackBoxWithin G π φ pD ε) :
    GEmulatesDummyWithin G π φ pD (fun pZ => ε 1 pZ) := by
  obtain ⟨S_D, hS, hadv⟩ := h
  refine ⟨S_D, hS, fun C Z pZ hZ κ z => ?_⟩
  rw [← gAdvantage_gCompSim_dummy]
  exact hadv _ _ (gDummyAdversary n _ _ GSpec) 1
    (gDummyAdversary_polyBounded n _ _ GSpec) C Z pZ hZ κ z

/-- **Global-setup dummy-adversary completeness** for `GEmulates`, in this library's call-bounded
(computationally unbounded), fixed-`n`-party, static-corruption shared-setup port model (#6043), not
the polynomial-time ITM GUC dummy-adversary completeness of [CanettiDPW2007]: asymptotic
global-setup emulation is equivalent to simulating the dummy adversary while sharing `GSpec`. -/
theorem gEmulates_iff_gEmulatesDummy (G : GlobalSetup GSpec)
    (π : GlobalProtocol n In Out NetQ₁ NetR₁ GSpec)
    (φ : GlobalProtocol n In Out NetQ₂ NetR₂ GSpec) :
    GEmulates G π φ ↔ GEmulatesDummy G π φ := by
  constructor
  · intro h
    exact h _ _ (gDummyAdversary n _ _ GSpec) 1 (gDummyAdversary_polyBounded n _ _ GSpec)
  · rintro ⟨S_D, pD, hS, hadv⟩ AdvQ AdvR A pA hA
    refine ⟨gCompSim S_D A, pA * (pD + 2) + (pD + 1), gCompSim_polyBounded hS hA, fun pZ => ?_⟩
    obtain ⟨ν, hν, hbound⟩ := hadv (absorbPoly pZ pA)
    refine ⟨ν, hν, fun C Z hZ κ z => ?_⟩
    rw [gAdvantage_gCompSim]
    exact hbound C _ (gAbsorbAdversary_polyBounded C hA hZ) κ z

end Completeness

/-! ### Single-session shared-setup EUC composition -/

/-- A hybrid protocol in the global-setup model: its activations may call both the party port of
one subroutine `SubIn`/`SubOut` and the shared global setup `GSpec`. -/
abbrev GlobalHybridProtocol (n : ℕ) (In Out NetQ NetR SubIn SubOut : Type) {ιG : Type}
    (GSpec : ιG → Type) : Type 1 :=
  ℕ → Finset (Fin n) → Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR)

/-- Polynomial call budget for a global-setup hybrid protocol. -/
@[expose] def GlobalHybridProtocol.PolyBounded
    (ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec) (p : Polynomial ℕ) : Prop :=
  ∀ κ C, (ρ κ C).IsBounded (p.eval κ)

/-- Lift a program over `(partySpec n In Out ⊕ₒ GSpec)` into `(protocolSpec n In Out NetQ NetR ⊕ₒ
GSpec)`. -/
@[expose] def liftPartyWithG (program : ProbOracleComp (partySpec n In Out ⊕ₒ GSpec) α) :
    ProbOracleComp (protocolSpec n In Out NetQ NetR ⊕ₒ GSpec) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec
        (protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)) (Sum.inl k))
      fun
        | .inl p => ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)
            (Sum.inl (Sum.inl p))
        | .inr g => ProbOracleComp.query (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec)
            (Sum.inr g))
    program

/-- Wrap a global-setup hybrid protocol `M` so its subroutine calls enter the imported subroutine's
party port, its direct `GSpec` calls pass through, and the subroutine's network port is exposed
beside `M`'s own. -/
@[expose] def gHybridWrap
    (M : Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR)) :
    Machine (protocolSpec n SubIn SubOut NQ NR ⊕ₒ GSpec)
      (protocolSpec n In Out (NetQ ⊕ NQ) (NetR ⊕ NR)) where
  State := M.State
  init := M.init
  handle
    | .inl p => fun s => liftPartyWithG ((M.handle (.inl p)).run s)
    | .inr (.inl q) => fun s => liftPartyWithG ((Sum.inl <$> M.handle (.inr q)).run s)
    | .inr (.inr q) => StateT.lift (Sum.inr <$>
        ProbOracleComp.query (spec := protocolSpec n SubIn SubOut NQ NR ⊕ₒ GSpec)
          (Sum.inl (Sum.inr q)))

/-- Shared-setup subroutine replacement `gCompose ρ σ`: `ρ` calls subroutine `σ` on its party
port while **both** `ρ` and `σ` share the same live `GSpec` port. -/
@[expose] def gCompose (ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec)
    (σ : GlobalProtocol n SubIn SubOut NQ NR GSpec) :
    GlobalProtocol n In Out (NetQ ⊕ RoutedNetQ n SubIn NQ) (NetR ⊕ RoutedNetR SubOut NR) GSpec :=
  fun κ C => (gHybridWrap (ρ κ C)).comp (shareRight (routeCorrupt C (σ κ C)))

/-- Absorbing the hybrid protocol `ρ` (along with its direct `GSpec` calls) into the environment of
the subroutine. -/
@[expose] def gAbsorbHybrid (C : Finset (Fin n))
    (ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec)
    (Z : GlobalEnvironment n In Out
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)) GSpec) :
    GlobalEnvironment n SubIn SubOut (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR) GSpec :=
  fun κ z =>
    (passRight (routeCorrupt C (gHybridWrap (NQ := RoutedNetQ n SubIn NQ)
      (NR := RoutedNetR SubOut NR) (ρ κ C)))).link (Z κ z)

/-- Lift a program calling the subroutine's routed network port and `GSpec` into a program calling
the composed network port and `GSpec`. -/
private def gLiftSubNet
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR) ⊕ₒ GSpec) α) :
    ProbOracleComp (netSpec (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)) ⊕ₒ GSpec) α :=
  OracleComp.interpret
    (sumHandler
      (fun k => OracleComp.query (spec := probOracleSpec
        (netSpec (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
          (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)) ⊕ₒ GSpec)) (Sum.inl k))
      fun
        | .inl q => subReply <$> ProbOracleComp.query (spec := netSpec
            (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
            (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)) ⊕ₒ GSpec)
            (Sum.inl (Sum.inr (Sum.inr q)))
        | .inr g => ProbOracleComp.query (spec := netSpec
            (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
            (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)) ⊕ₒ GSpec) (Sum.inr g))
    program

/-- The composed simulator's machine: queries for `ρ` are forwarded, queries for the subroutine are
answered by the subroutine simulator `S`, and `S`'s direct `GSpec` calls pass through to the shared
global setup. -/
def gHybridSimMachine
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) ⊕ₒ GSpec)
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁))) :
    Machine
      (netSpec (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) ⊕ₒ GSpec)
      (netSpec (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))) where
  State := S.State
  init := S.init
  handle
    | .inl p => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) ⊕ₒ GSpec) (Sum.inl (Sum.inl p)))
    | .inr (.inl q) => StateT.lift (outerReply <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) ⊕ₒ GSpec)
        (Sum.inl (Sum.inr (Sum.inl q))))
    | .inr (.inr q) => fun s =>
        gLiftSubNet (((fun r => Sum.inr (Sum.inr r)) <$> S.handle q).run s)

/-- The composed simulator for `gCompose ρ π` against `gCompose ρ φ`, built from a simulator `S`
for the dummy adversary of `π` against `φ`. -/
@[expose] def gHybridSim
    (S : GlobalAdversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) GSpec) :
    GlobalAdversary n
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁))
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) GSpec :=
  fun κ C => gHybridSimMachine (S κ C)

/-- Running the dummy adversary against `gCompose ρ π` equals running the dummy adversary against
`π` with the hybrid protocol `ρ` absorbed into the environment `gAbsorbHybrid C ρ Z`. -/
theorem gExec_gCompose_dummy (G : GlobalSetup GSpec)
    (ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec)
    (π : GlobalProtocol n SubIn SubOut NQ NR GSpec) (C : Finset (Fin n))
    (Z : GlobalEnvironment n In Out
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)) GSpec)
    (κ : ℕ) (z : List Bool) :
    GlobalExec G (gCompose ρ π) (gDummyAdversary n _ _ GSpec) C Z κ z =
      GlobalExec G π (gDummyAdversary n _ _ GSpec) C (gAbsorbHybrid C ρ Z) κ z := by
  simp only [gExec_dummyAdversary, gCompose, routeCorrupt_comp, shareRight_comp_shareRight,
    Machine.link_comp, gAbsorbHybrid]

section ComposeSwap

private theorem liftPartyWithG_map {β : Type} (f : α → β)
    (program : ProbOracleComp (partySpec n In Out ⊕ₒ GSpec) α) :
    liftPartyWithG (NetQ := NetQ) (NetR := NetR) (f <$> program) =
      f <$> liftPartyWithG program := by
  dsimp only [liftPartyWithG]
  exact OracleComp.interpret_map _ _ _

private theorem gLiftSubNet_map {β : Type} (f : α → β)
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR) ⊕ₒ GSpec) α) :
    gLiftSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) (f <$> program) =
      f <$> gLiftSubNet program := by
  dsimp only [gLiftSubNet]
  exact OracleComp.interpret_map _ _ _

private theorem runFrom_gLiftAdversary_liftPartyWithG
    (S : Machine (netSpec NQ₂ NR₂ ⊕ₒ GSpec) (netSpec NQ₁ NR₁))
    (program : ProbOracleComp (partySpec n SubIn SubOut ⊕ₒ GSpec) α) (s : S.State) :
    (gLiftAdversary (n := n) (In := SubIn) (Out := SubOut) S).runFrom
        (liftPartyWithG (NetQ := NQ₁) (NetR := NR₁) program) s =
      (fun a => (a, s)) <$> liftPartyWithG (NetQ := NQ₂) (NetR := NR₂) program := by
  dsimp only [liftPartyWithG]
  refine Machine.runFrom_interpret_of_forward (gLiftAdversary S) _ _ (fun q s => ?_) program s
  cases q with
  | inl k => exact runFrom_query_sample _ k s
  | inr e =>
    cases e with
    | inl p =>
      change (gLiftAdversary S).runFrom (ProbOracleComp.query
          (spec := protocolSpec n SubIn SubOut NQ₁ NR₁ ⊕ₒ GSpec) (Sum.inl (Sum.inl p))) s = _
      rw [Machine.runFrom_query]
      dsimp only [gLiftAdversary]
      erw [StateT.run_lift, bind_pure_comp]
    | inr g =>
      change (gLiftAdversary S).runFrom (ProbOracleComp.query
          (spec := protocolSpec n SubIn SubOut NQ₁ NR₁ ⊕ₒ GSpec) (Sum.inr g)) s = _
      rw [Machine.runFrom_query]
      dsimp only [gLiftAdversary]
      erw [StateT.run_lift, bind_pure_comp]

private theorem runFrom_passRight_routeCorrupt_liftNet_gLiftSubNet
    (C : Finset (Fin n))
    (M : Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR))
    (program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR) ⊕ₒ GSpec) α)
    (s : M.State) :
    (passRight (routeCorrupt C
        (gHybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR) M))).runFrom
        (liftNetWithG (gLiftSubNet program)) s =
      (fun a => (a, s)) <$> liftNetWithG program := by
  dsimp only [liftNetWithG, gLiftSubNet]
  rw [OracleComp.interpret_interpret]
  refine Machine.runFrom_interpret_of_forward
    (passRight (routeCorrupt C (gHybridWrap M))) _ _ (fun q s => ?_) program s
  cases q with
  | inl k =>
    simp only [OracleComp.interpret_query]
    exact runFrom_query_sample _ k s
  | inr e =>
    cases e with
    | inl q =>
      simp only [OracleComp.interpret_map, ProbOracleComp.interpret_query, Machine.runFrom_map,
        Machine.runFrom_query]
      change Prod.map subReply _root_.id <$> ((Sum.inr <$> StateT.lift (Sum.inr <$>
        ProbOracleComp.query (spec := protocolSpec n SubIn SubOut (RoutedNetQ n SubIn NQ)
          (RoutedNetR SubOut NR) ⊕ₒ GSpec) (Sum.inl (Sum.inr q)))).run s) = _
      rw [StateT.run_map, StateT.run_lift, bind_pure_comp, Functor.map_map, Functor.map_map,
        Functor.map_map]
      rfl
    | inr g =>
      dsimp only [passRight]
      erw [ProbOracleComp.interpret_query, Machine.runFrom_query, StateT.run_lift, bind_pure_comp]

private theorem gLiftAdversary_handle_inl_inl {AdvQ AdvR : Type}
    (A : Machine (netSpec NetQ NetR ⊕ₒ GSpec) (netSpec AdvQ AdvR)) (p : Fin n × In) (s : A.State) :
    ((gLiftAdversary (n := n) (In := In) (Out := Out) A).handle (Sum.inl (Sum.inl p))).run s =
      (fun a => (a, s)) <$> ProbOracleComp.query
        (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec) (Sum.inl (Sum.inl p)) := by
  dsimp only [gLiftAdversary]
  rw [StateT.run_lift, bind_pure_comp]

private theorem gLiftAdversary_handle_inl_inr {AdvQ AdvR : Type}
    (A : Machine (netSpec NetQ NetR ⊕ₒ GSpec) (netSpec AdvQ AdvR)) (q : AdvQ) (s : A.State) :
    ((gLiftAdversary (n := n) (In := In) (Out := Out) A).handle (Sum.inl (Sum.inr q))).run s =
      liftNetWithG ((A.handle q).run s) := rfl

private theorem gLiftAdversary_handle_inr {AdvQ AdvR : Type}
    (A : Machine (netSpec NetQ NetR ⊕ₒ GSpec) (netSpec AdvQ AdvR)) (g : ιG) (s : A.State) :
    ((gLiftAdversary (n := n) (In := In) (Out := Out) A).handle (Sum.inr g)).run s =
      (fun a => (a, s)) <$> ProbOracleComp.query
        (spec := protocolSpec n In Out NetQ NetR ⊕ₒ GSpec) (Sum.inr g) := by
  dsimp only [gLiftAdversary]
  rw [StateT.run_lift, bind_pure_comp]

private theorem gHybridWrap_handle_inl
    (M : Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR))
    (p : Fin n × In) (s : M.State) :
    ((gHybridWrap (NQ := NQ) (NR := NR) M).handle (.inl p)).run s =
      liftPartyWithG ((M.handle (.inl p)).run s) := rfl

private theorem gHybridWrap_handle_inr_inl
    (M : Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR))
    (q : NetQ) (s : M.State) :
    ((gHybridWrap (NQ := NQ) (NR := NR) M).handle (.inr (.inl q))).run s =
      (fun p => (Sum.inl p.1, p.2)) <$> liftPartyWithG ((M.handle (.inr q)).run s) := by
  change liftPartyWithG ((Sum.inl <$> M.handle (.inr q)).run s) = _
  rw [StateT.run_map, liftPartyWithG_map]

private theorem gHybridWrap_handle_inr_inr
    (M : Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR))
    (q : NQ) (s : M.State) :
    ((gHybridWrap (NR := NR) M).handle (.inr (.inr q))).run s =
      (fun a => (Sum.inr a, s)) <$>
        ProbOracleComp.query
          (spec := protocolSpec n SubIn SubOut NQ NR ⊕ₒ GSpec) (Sum.inl (Sum.inr q)) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem gHybridSimMachine_handle_inl
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) ⊕ₒ GSpec)
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (p : Fin n × In) (s : S.State) :
    ((gHybridSimMachine (NetQ := NetQ) (NetR := NetR) (Out := Out) S).handle (.inl p)).run s =
      (fun a => (outerReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) ⊕ₒ GSpec) (.inl (.inl p)) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem gHybridSimMachine_handle_inr_inl
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) ⊕ₒ GSpec)
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (q : NetQ) (s : S.State) :
    ((gHybridSimMachine (In := In) (NetR := NetR) (Out := Out) S).handle
        (.inr (.inl q))).run s =
      (fun a => (outerReply a, s)) <$> ProbOracleComp.query (spec := netSpec
        (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₂))
        (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₂)) ⊕ₒ GSpec) (.inl (.inr (.inl q))) := by
  change (StateT.lift _).run s = _
  rw [StateT.run_lift, bind_pure_comp, Functor.map_map]

private theorem gHybridSimMachine_handle_inr_inr
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) ⊕ₒ GSpec)
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (q : RoutedNetQ n SubIn NQ₁) (s : S.State) :
    ((gHybridSimMachine (In := In) (NetQ := NetQ) (NetR := NetR) (Out := Out) S).handle
        (.inr (.inr q))).run s =
      (fun p => (Sum.inr (Sum.inr p.1), p.2)) <$> gLiftSubNet ((S.handle q).run s) := by
  change gLiftSubNet ((_ <$> S.handle q).run s) = _
  rw [StateT.run_map, gLiftSubNet_map]

private theorem handle_swap_g
    (C : Finset (Fin n))
    (M : Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR))
    (S : Machine (netSpec (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) ⊕ₒ GSpec)
      (netSpec (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)))
    (q : ((Fin n × In) ⊕ RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁)) ⊕ ιG)
    (sρ : M.State) (sS : S.State) :
    Equiv.prodAssoc _ _ _ <$> (passRight (routeCorrupt C (gHybridWrap
        (NQ := RoutedNetQ n SubIn NQ₂) (NR := RoutedNetR SubOut NR₂) M))).runFrom
          (((gLiftAdversary (n := n) (In := In) (Out := Out)
            (gHybridSimMachine S)).handle q).run sS) sρ =
      Prod.map _root_.id Prod.swap <$> (Equiv.prodAssoc _ _ _ <$>
        (gLiftAdversary (n := n) (In := SubIn) (Out := SubOut) S).runFrom
          (((passRight (routeCorrupt C (gHybridWrap
            (NQ := RoutedNetQ n SubIn NQ₁) (NR := RoutedNetR SubOut NR₁) M))).handle q).run sρ)
          sS) := by
  -- The outer wrapper types differ syntactically between LHS and RHS, so `erw` unfolds them.
  rcases q with (⟨i, x⟩ | ⟨i, x⟩ | q | q) | g
  · erw [gLiftAdversary_handle_inl_inl, Machine.runFrom_map, Machine.runFrom_query]
    erw [routeCorrupt_handle_inl, routeCorrupt_handle_inl]
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      rfl
    · simp only [hi, ↓reduceIte]
      erw [gHybridWrap_handle_inl, gHybridWrap_handle_inl]
      erw [runFrom_gLiftAdversary_liftPartyWithG (NQ₁ := RoutedNetQ n SubIn NQ₁)
          (NR₁ := RoutedNetR SubOut NR₁) (NQ₂ := RoutedNetQ n SubIn NQ₂)
          (NR₂ := RoutedNetR SubOut NR₂)]
      repeat erw [Functor.map_map]
      rfl
  · erw [gLiftAdversary_handle_inl_inr, gHybridSimMachine_handle_inl, liftNetWithG_map,
      Machine.runFrom_map, Machine.runFrom_query]
    erw [routeCorrupt_handle_inr_inl, routeCorrupt_handle_inr_inl]
    by_cases hi : i ∈ C
    · simp only [hi, ↓reduceIte]
      erw [gHybridWrap_handle_inl, gHybridWrap_handle_inl, Machine.runFrom_map,
        runFrom_gLiftAdversary_liftPartyWithG (NQ₁ := RoutedNetQ n SubIn NQ₁)
          (NR₁ := RoutedNetR SubOut NR₁) (NQ₂ := RoutedNetQ n SubIn NQ₂)
          (NR₂ := RoutedNetR SubOut NR₂)]
      repeat erw [Functor.map_map]
      rfl
    · simp only [hi, ↓reduceIte]
      rfl
  · erw [gLiftAdversary_handle_inl_inr, gHybridSimMachine_handle_inr_inl, liftNetWithG_map,
      Machine.runFrom_map, Machine.runFrom_query]
    erw [routeCorrupt_handle_inr_inr C, routeCorrupt_handle_inr_inr C,
      gHybridWrap_handle_inr_inl, gHybridWrap_handle_inr_inl]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map,
      runFrom_gLiftAdversary_liftPartyWithG (NQ₁ := RoutedNetQ n SubIn NQ₁)
        (NR₁ := RoutedNetR SubOut NR₁) (NQ₂ := RoutedNetQ n SubIn NQ₂)
        (NR₂ := RoutedNetR SubOut NR₂)]
    repeat erw [Functor.map_map]
    rfl
  · erw [gLiftAdversary_handle_inl_inr, gHybridSimMachine_handle_inr_inr, liftNetWithG_map,
      Machine.runFrom_map, runFrom_passRight_routeCorrupt_liftNet_gLiftSubNet C]
    erw [Functor.map_map]
    erw [routeCorrupt_handle_inr_inr C, gHybridWrap_handle_inr_inr]
    repeat erw [Functor.map_map]
    erw [Machine.runFrom_map, Machine.runFrom_query, gLiftAdversary_handle_inl_inr]
    repeat erw [Functor.map_map]
    rfl
  · erw [gLiftAdversary_handle_inr, Machine.runFrom_map, Machine.runFrom_query]
    dsimp only [passRight]
    simp only [Functor.map_map]
    rfl

end ComposeSwap

/-- Running `gCompose ρ φ` with `gHybridSim S` has the exact same output distribution as running `φ`
with `S` and `gAbsorbHybrid C ρ Z`, while sharing the same live global setup `G κ`. -/
theorem eval_gExec_gCompose_gHybridSim (G : GlobalSetup GSpec)
    (ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec)
    (φ : GlobalProtocol n SubIn SubOut NQ₂ NR₂ GSpec)
    (S : GlobalAdversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) GSpec)
    (C : Finset (Fin n))
    (Z : GlobalEnvironment n In Out
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)) GSpec)
    (κ : ℕ) (z : List Bool) :
    (GlobalExec G (gCompose ρ φ) (gHybridSim S) C Z κ z).eval =
      (GlobalExec G φ S C (gAbsorbHybrid C ρ Z) κ z).eval := by
  simp only [GlobalExec, gExecMachine, gCompose, routeCorrupt_comp, shareRight_comp_shareRight,
    gHybridSim, gAbsorbHybrid, Machine.run_comp, Machine.link_comp]
  rw [← Machine.run_comp (shareRight (routeCorrupt C (φ κ C))) (G κ)]
  conv_rhs => rw [← Machine.run_comp (shareRight (routeCorrupt C (φ κ C))) (G κ)]
  rw [← Machine.link_comp
      (gLiftAdversary (n := n) (In := In) (Out := Out) (gHybridSimMachine (S κ C)))
      (passRight (routeCorrupt C (gHybridWrap (NQ := RoutedNetQ n SubIn NQ₂)
        (NR := RoutedNetR SubOut NR₂) (ρ κ C)))) (Z κ z),
    ← Machine.link_comp
      (passRight (routeCorrupt C (gHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
        (NR := RoutedNetR SubOut NR₁) (ρ κ C))))
      (gLiftAdversary (n := n) (In := SubIn) (Out := SubOut) (S κ C)) (Z κ z)]
  refine eval_run_link_swap
    (gLiftAdversary (n := n) (In := In) (Out := Out) (gHybridSimMachine (S κ C)))
    (passRight (routeCorrupt C (gHybridWrap (NQ := RoutedNetQ n SubIn NQ₂)
      (NR := RoutedNetR SubOut NR₂) (ρ κ C))))
    (passRight (routeCorrupt C (gHybridWrap (NQ := RoutedNetQ n SubIn NQ₁)
      (NR := RoutedNetR SubOut NR₁) (ρ κ C))))
    (gLiftAdversary (n := n) (In := SubIn) (Out := SubOut) (S κ C))
    _root_.id _root_.id (id_map _) (id_map _) ?_
    ((shareRight (routeCorrupt C (φ κ C))).comp (G κ)) (Z κ z)
  exact fun q s => handle_swap_g C (ρ κ C) (S κ C) q s.1 s.2

/-- The advantage between `gCompose ρ π` against the dummy adversary and `gCompose ρ φ` against
`gHybridSim S` equals the advantage between `π` against the dummy adversary and `φ` against `S` for
the absorbed environment `gAbsorbHybrid C ρ Z`. -/
theorem gAdvantage_gCompose (G : GlobalSetup GSpec)
    (ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec)
    (π : GlobalProtocol n SubIn SubOut NQ₁ NR₁ GSpec)
    (φ : GlobalProtocol n SubIn SubOut NQ₂ NR₂ GSpec)
    (S : GlobalAdversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) GSpec)
    (C : Finset (Fin n))
    (Z : GlobalEnvironment n In Out
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ₁))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR₁)) GSpec)
    (κ : ℕ) (z : List Bool) :
    gAdvantage G (gCompose ρ π) (gCompose ρ φ)
        (gDummyAdversary n _ _ GSpec) (gHybridSim S) C Z κ z =
      gAdvantage G π φ (gDummyAdversary n _ _ GSpec) S C (gAbsorbHybrid C ρ Z) κ z := by
  rw [gAdvantage, gAdvantage, gExec_gCompose_dummy, eval_gExec_gCompose_gHybridSim]

/-! #### Budgets for shared-setup composition -/

private theorem isQueryBounded_liftPartyWithG
    {program : ProbOracleComp (partySpec n In Out ⊕ₒ GSpec) α} {m : ℕ}
    (h : program.IsQueryBounded m) :
    (liftPartyWithG (NetQ := NetQ) (NetR := NetR) program).IsQueryBounded m := by
  dsimp only [liftPartyWithG]
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr e =>
    cases e with
    | inl p => exact OracleComp.IsCostBounded.query _
    | inr g => exact OracleComp.IsCostBounded.query _

private theorem isQueryBounded_gLiftSubNet
    {program : ProbOracleComp (netSpec (RoutedNetQ n SubIn NQ) (RoutedNetR SubOut NR) ⊕ₒ GSpec) α}
    {m : ℕ} (h : program.IsQueryBounded m) :
    (gLiftSubNet (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) program).IsQueryBounded
      m := by
  dsimp only [gLiftSubNet]
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl k => exact OracleComp.IsCostBounded.query _
  | inr e =>
    cases e with
    | inl q => exact (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)
    | inr g => exact OracleComp.IsCostBounded.query _

private theorem isBounded_gHybridWrap
    {M : Machine (partySpec n SubIn SubOut ⊕ₒ GSpec) (protocolSpec n In Out NetQ NetR)} {t : ℕ}
    (h : M.IsBounded t) : (gHybridWrap (NQ := NQ) (NR := NR) M).IsBounded (t + 1) := by
  refine ⟨h.1.mono (by omega), fun q s => ?_⟩
  rcases q with p | q | q
  · dsimp only [gHybridWrap]
    exact (isQueryBounded_liftPartyWithG (h.2 _ s)).mono (by omega)
  · erw [gHybridWrap_handle_inr_inl]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((isQueryBounded_liftPartyWithG (h.2 _ s)).mono (by omega))
  · erw [gHybridWrap_handle_inr_inr]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))

/-- The absorbed environment `gAbsorbHybrid C ρ Z` has budget `absorbPoly pZ pρ`. -/
theorem gAbsorbHybrid_polyBounded (C : Finset (Fin n))
    {ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec}
    {Z : GlobalEnvironment n In Out
      (RoutedNetQ n In (NetQ ⊕ RoutedNetQ n SubIn NQ))
      (RoutedNetR Out (NetR ⊕ RoutedNetR SubOut NR)) GSpec}
    {pρ pZ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hZ : Z.PolyBounded pZ) :
    (gAbsorbHybrid C ρ Z).PolyBounded (absorbPoly pZ pρ) := fun κ z => by
  have hrc : (routeCorrupt C (gHybridWrap
      (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR) (ρ κ C))).IsBounded
      (pρ.eval κ + 1) :=
    isBounded_routeCorrupt C (isBounded_gHybridWrap (hρ κ C))
  refine (Machine.isQueryBounded_link (isBounded_passRight hrc) (hZ κ z)).mono (le_of_eq ?_)
  rw [eval_absorbPoly]

/-- The composed simulator `gHybridSim S` has budget `pS + 1` when `S` has budget `pS`. -/
theorem gHybridSim_polyBounded
    {S : GlobalAdversary n (RoutedNetQ n SubIn NQ₁) (RoutedNetR SubOut NR₁)
      (RoutedNetQ n SubIn NQ₂) (RoutedNetR SubOut NR₂) GSpec}
    {pS : Polynomial ℕ} (hS : S.PolyBounded pS) :
    (gHybridSim (In := In) (Out := Out) (NetQ := NetQ) (NetR := NetR) S).PolyBounded
      (pS + 1) := fun κ C => by
  rw [Polynomial.eval_add, Polynomial.eval_one]
  refine ⟨(hS κ C).1.mono (by omega), fun q s => ?_⟩
  dsimp only [gHybridSim] at s ⊢
  rcases q with p | q | q
  · erw [gHybridSimMachine_handle_inl]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  · erw [gHybridSimMachine_handle_inr_inl]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  · erw [gHybridSimMachine_handle_inr_inr]
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((isQueryBounded_gLiftSubNet ((hS κ C).2 q s)).mono (by omega))

/-- The shared-setup composition `gCompose ρ σ` has budget `(pρ + 1) * (pσ + 2) + (pσ + 1)` when `ρ`
and `σ` have budgets `pρ` and `pσ`. -/
theorem gCompose_polyBounded
    {ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec}
    {σ : GlobalProtocol n SubIn SubOut NQ NR GSpec}
    {pρ pσ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hσ : σ.PolyBounded pσ) :
    (gCompose ρ σ).PolyBounded ((pρ + 1) * (pσ + 2) + (pσ + 1)) := fun κ C => by
  have h := (isBounded_gHybridWrap (NQ := RoutedNetQ n SubIn NQ) (NR := RoutedNetR SubOut NR)
    (hρ κ C)).comp (isBounded_shareRight (t := pσ.eval κ)
      (isBounded_routeCorrupt C ((hσ κ C).mono (by omega))))
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat]
  exact h.mono (le_of_eq (by ring))

/-! #### Shared-setup EUC composition theorems -/

section ComposeTheorems

variable {G : GlobalSetup GSpec}
  {ρ : GlobalHybridProtocol n In Out NetQ NetR SubIn SubOut GSpec}
  {π : GlobalProtocol n SubIn SubOut NQ₁ NR₁ GSpec}
  {φ : GlobalProtocol n SubIn SubOut NQ₂ NR₂ GSpec}

/-- Shared-setup composition for `GEmulatesDummyWithin`, in this library's call-bounded
(computationally unbounded), fixed-`n`-party, static-corruption shared-setup port model (#6043), a
step toward the polynomial-time ITM EUC composition theorem of [CanettiDPW2007] but not that
theorem: if `S` simulates the dummy adversary of `π` in `φ` with budget `pD` and error `ε`, then
`gHybridSim S` simulates the dummy adversary of `gCompose ρ π` in `gCompose ρ φ` with budget
`pD + 1` and error `ε` evaluated at the absorbed environment's budget `absorbPoly pZ pρ`, all
parties sharing the same global setup `G`. -/
theorem GEmulatesDummyWithin.compose {pρ pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (hρ : ρ.PolyBounded pρ) (h : GEmulatesDummyWithin G π φ pD ε) :
    GEmulatesDummyWithin G (gCompose ρ π) (gCompose ρ φ) (pD + 1)
      (fun pZ => ε (absorbPoly pZ pρ)) := by
  obtain ⟨S, hS, hadv⟩ := h
  refine ⟨gHybridSim S, gHybridSim_polyBounded hS, fun C Z pZ hZ κ z => ?_⟩
  rw [gAdvantage_gCompose]
  exact hadv C _ _ (gAbsorbHybrid_polyBounded C hρ hZ) κ z

/-- Concrete shared-setup composition for `GEmulatesWithin`, in this library's call-bounded
(computationally unbounded), fixed-`n`-party, static-corruption shared-setup port model (#6043), a
step toward the polynomial-time ITM EUC composition theorem of [CanettiDPW2007] but not that
theorem: if `π` emulates `φ` with simulator overhead `g` and error `ε`, then `gCompose ρ π` emulates
`gCompose ρ φ` with the overhead below and error `ε 1` evaluated at the environment budget that
absorbs both the adversary and the hybrid protocol. -/
theorem GEmulatesWithin.compose {pρ g : Polynomial ℕ}
    {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0} (hρ : ρ.PolyBounded pρ)
    (h : GEmulatesWithin G π φ g ε) :
    GEmulatesWithin G (gCompose ρ π) (gCompose ρ φ)
      (Polynomial.X * (g.comp (Polynomial.X + 1) + 1 + 2) + (g.comp (Polynomial.X + 1) + 1 + 1))
      (fun pA pZ => ε 1 (absorbPoly (absorbPoly pZ pA) pρ)) := by
  obtain ⟨pD, hg, hD⟩ := h.gEmulatesDummyWithin
  intro AdvQ AdvR A pA hA
  obtain ⟨S, pS, hS, hSg, hadv⟩ := (hD.compose hρ).gEmulatesWithin AdvQ AdvR A pA hA
  refine ⟨S, pS, hS, fun κ => (hSg κ).trans ?_, hadv⟩
  have hD' : pD.eval (κ + pA.eval κ) ≤ g.eval (κ + pA.eval κ + 1) := by
    simpa only [Polynomial.eval_one] using hg (κ + pA.eval κ)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat, Polynomial.eval_comp]
  gcongr

/-- **Single-session shared-setup composition** for `GEmulates`, in this library's call-bounded
(computationally unbounded), fixed-`n`-party, static-corruption shared-setup port model (#6043), a
step toward the polynomial-time ITM EUC composition theorem of [CanettiDPW2007] but not that
theorem: replacing subroutine `π` with `φ` inside a hybrid protocol `ρ` with a polynomial budget
preserves `GEmulates` while `ρ`, `π`, `φ`, the adversary/simulator, and the environment all share
the same live global setup `G`. -/
theorem GEmulates.compose {pρ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (h : GEmulates G π φ) :
    GEmulates G (gCompose ρ π) (gCompose ρ φ) := by
  rw [gEmulates_iff_gEmulatesDummy] at h ⊢
  obtain ⟨S, pD, hS, hadv⟩ := h
  refine ⟨gHybridSim S, pD + 1, gHybridSim_polyBounded hS, fun pZ => ?_⟩
  obtain ⟨ν, hν, hbound⟩ := hadv (absorbPoly pZ pρ)
  refine ⟨ν, hν, fun C Z hZ κ z => ?_⟩
  rw [gAdvantage_gCompose]
  exact hbound C _ (gAbsorbHybrid_polyBounded C hρ hZ) κ z

/-- Replacing an ideal functionality by a protocol that realizes it with shared setup `G`, in this
library's call-bounded (computationally unbounded), fixed-`n`-party, static-corruption shared-setup
port model (#6043), not the polynomial-time ITM GUC result of [CanettiDPW2007]: if `π` realizes `F`,
then `gCompose ρ π` emulates the `F`-hybrid protocol `gCompose ρ F.toGlobalProtocol` in the sense of
`GEmulates`. -/
theorem GRealizes.compose {F : IdealFunctionality n SubIn SubOut BackQ BackR}
    {pρ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (h : GRealizes G π F) :
    GEmulates G (gCompose ρ π) (gCompose ρ F.toGlobalProtocol) :=
  GEmulates.compose hρ h

/-- Modular protocol design with shared setup `G`, in this library's call-bounded (computationally
unbounded), fixed-`n`-party, static-corruption shared-setup port model (#6043), not the
polynomial-time ITM GUC result of [CanettiDPW2007]: if `gCompose ρ F.toGlobalProtocol` realizes `I`
and `π` realizes `F`, then `gCompose ρ π` realizes `I`. -/
theorem GRealizes.compose_trans {GQ GR : Type}
    {F : IdealFunctionality n SubIn SubOut BackQ BackR}
    {I : IdealFunctionality n In Out GQ GR}
    {pρ : Polynomial ℕ} (hρ : ρ.PolyBounded pρ) (hπ : GRealizes G π F)
    (hρI : GRealizes G (gCompose ρ F.toGlobalProtocol) I) :
    GRealizes G (gCompose ρ π) I :=
  (hπ.compose hρ).trans hρI

end ComposeTheorems

/-! ### Non-programmability separation: local setup vs. global setup -/

/-- A one-bit random setup machine `coinSetup` sampling a uniform coin `c : Bool` at
initialization and returning `c` on every query `()`. -/
@[expose] def coinSetup : GlobalSetup (netSpec Unit Bool) := fun _ => {
  State := Bool
  init := (fun r => decide (r.val = 1)) <$> ProbComp.unifFin 1
  handle := fun _ s => pure (s, s) }

/-- A 1-party global-setup protocol reading the shared `coinSetup` bit upon party `0`'s query. -/
@[expose] def coinReaderProto : GlobalProtocol 1 Unit Bool Unit Unit (netSpec Unit Bool) :=
  fun _ _ => {
    State := Unit
    init := pure ()
    handle
      | .inl (_, _) => StateT.lift (some <$> ProbOracleComp.query (spec := netSpec Unit Bool) ())
      | .inr _ => pure () }

/-- The same coin-reading protocol closed against a **local** private `coinSetup` instance (not
exposed directly to the environment). -/
@[expose] def localCoinProto : Protocol 1 Unit Bool Unit Unit :=
  HybridFunctionality.close
    { State := Unit
      init := fun _ _ => pure ()
      onInput := fun _ _ => StateT.lift (some <$> ProbOracleComp.query
        (spec := netSpec Unit Bool) ())
      onBackdoor := fun _ => pure () }
    (fun κ _ => coinSetup κ)

/-- The ideal 1-party random-coin functionality `indepCoinFunc`: samples its own fresh uniform bit
`r : Bool` independently of any global setup, returns `some r` on party query, and ignores
backdoor queries. -/
@[expose] def indepCoinFunc : IdealFunctionality 1 Unit Bool Unit Unit where
  State := Bool
  init _ _ := (fun r => decide (r.val = 1)) <$> ProbComp.unifFin 1
  onInput _ _ s := pure (some s, s)
  onBackdoor _ s := pure ((), s)

private theorem eval_run_map_state {ιE : Type} {E : ιE → Type}
    (M₁ M₂ : Machine OracleSpec.empty E) (f : M₂.State → M₁.State)
    (hinit : f <$> M₂.init = M₁.init)
    (hstep : ∀ q s, (M₁.handle q).run (f s) = Prod.map _root_.id f <$> (M₂.handle q).run s)
    (program : ProbOracleComp E α) :
    (M₁.run program).eval = (M₂.run program).eval := by
  simp only [Machine.run, Machine.link, ← hinit, ProbOracleComp.sample_map, bind_map_left,
    Machine.closeProgram_bind, Machine.closeProgram_sample, ProbComp.eval_bind]
  congr 1 with s : 1
  rw [Machine.runFrom_map_state M₁ M₂ f hstep program s, Functor.map_map]
  rfl

private theorem localCoinProto_handle_eq_indepCoin (κ : ℕ) (C : Finset (Fin 1))
    (q : (Fin 1 × Unit) ⊕ RoutedNetQ 1 Unit Unit) (s : Bool) :
    ((corruptRouter C (localCoinProto κ C)).handle q).run (PUnit.unit, s) =
      Prod.map _root_.id (fun b : Bool => (PUnit.unit, b)) <$>
        ((corruptRouter C (indepCoinFunc.toProtocol κ C)).handle q).run s := by
  refine handle_corruptRouter_map_state C (localCoinProto κ C) (indepCoinFunc.toProtocol κ C)
    (fun b => (PUnit.unit, b)) (fun q₀ s₀ => ?_) q s
  dsimp only [IdealFunctionality.toProtocol, indepCoinFunc] at s₀ ⊢
  rcases q₀ with ⟨i, _⟩ | _
  · simp only [localCoinProto, HybridFunctionality.close, HybridFunctionality.toMachine,
      Machine.comp, StateT.run, StateT.lift, bind_pure_comp, Functor.map_map]
    simp only [coinSetup]
    rfl
  · simp only [localCoinProto, HybridFunctionality.close, HybridFunctionality.toMachine,
      Machine.comp, StateT.run]
    erw [Machine.runFrom_pure]
    rfl

/-- With a **local** private `coinSetup`, `localCoinProto` UC-realizes `indepCoinFunc` with zero
error (`advantage = 0`). -/
theorem localCoinProto_realizesWithin_indepCoinFunc :
    RealizesWithin localCoinProto indepCoinFunc Polynomial.X (fun _ _ _ => 0) := by
  intro AdvQ AdvR A pA hA
  refine ⟨A, pA, hA, SimPolyBound.refl pA, fun C Z pZ hZ κ z => ?_⟩
  have hexec : (exec localCoinProto A C Z κ z).eval =
      (exec indepCoinFunc.toProtocol A C Z κ z).eval := by
    refine eval_run_map_state (execMachine localCoinProto A κ C)
      (execMachine indepCoinFunc.toProtocol A κ C) (Prod.map _root_.id fun b => (PUnit.unit, b))
      ?_ ?_ (Z κ z)
    · dsimp only [execMachine, Machine.comp, corruptRouter, localCoinProto,
        HybridFunctionality.close, HybridFunctionality.toMachine, coinSetup,
        indepCoinFunc, IdealFunctionality.toProtocol]
      simp only [map_bind, bind_map_left, bind_assoc, pure_bind]
      rfl
    · intro q s
      exact Machine.comp_handle_map_state (liftAdversary (A κ C))
        (corruptRouter C (localCoinProto κ C)) (corruptRouter C (indepCoinFunc.toProtocol κ C))
        (fun b => (PUnit.unit, b)) (localCoinProto_handle_eq_indepCoin κ C) q s
  rw [advantage, hexec, Game.advantage_self]

/-- With a **local** private `coinSetup`, `localCoinProto` UC-realizes `indepCoinFunc`. -/
theorem localCoinProto_realizes_indepCoinFunc : Realizes localCoinProto indepCoinFunc :=
  localCoinProto_realizesWithin_indepCoinFunc.emulates fun _ _ => negligible_zero

/-- Environment testing whether party `0`'s output matches a direct query to `coinSetup`. -/
@[expose] def coinDistinguisherEnv {AdvQ AdvR : Type} :
    GlobalEnvironment 1 Unit Bool AdvQ AdvR (netSpec Unit Bool) := fun _ _ => do
  let pOut ← ProbOracleComp.query
    (spec := execSpec 1 Unit Bool AdvQ AdvR ⊕ₒ netSpec Unit Bool)
    (Sum.inl (Sum.inl ((0 : Fin 1), ())))
  let gBit ← ProbOracleComp.query
    (spec := execSpec 1 Unit Bool AdvQ AdvR ⊕ₒ netSpec Unit Bool) (Sum.inr ())
  return decide (pOut = some gBit)

private theorem coinDistinguisherEnv_polyBounded {AdvQ AdvR : Type} :
    (coinDistinguisherEnv : GlobalEnvironment 1 Unit Bool AdvQ AdvR (netSpec Unit Bool)).PolyBounded
      2 := fun _ _ => by
  rw [Polynomial.eval_ofNat]
  refine ((OracleComp.IsCostBounded.query _).bind fun _ =>
    (OracleComp.isCostBounded_map_iff _ _ _).mpr (OracleComp.IsCostBounded.query _)).mono (by omega)

private noncomputable def uniformCoinBool : PMF Bool :=
  (ProbComp.unifFin 1).eval.map (fun r => decide (r.val = 1))

private theorem uniformCoinBool_apply (b : Bool) : uniformCoinBool b = (1 / 2 : ℝ≥0∞) := by
  simp only [uniformCoinBool, ProbComp.eval_unifFin, PMF.map_apply,
    Probability.PMF.uniformOfFintype_apply, Fintype.card_fin]
  rw [tsum_fintype, Fin.sum_univ_two]
  cases b <;> norm_num

private theorem eval_gExec_coinReader_dummy (κ : ℕ) (z : List Bool) :
    (GlobalExec coinSetup coinReaderProto
      (gDummyAdversary 1 (RoutedNetQ 1 Unit Unit) (RoutedNetR Bool Unit) (netSpec Unit Bool))
      ∅ coinDistinguisherEnv κ z).eval = PMF.pure true := by
  rw [gExec_dummyAdversary, Machine.run, Machine.link, Machine.link]
  dsimp only [coinDistinguisherEnv]
  simp only [coinSetup, shareRight, routeCorrupt, coinReaderProto, StateT.run, StateT.lift,
    Finset.notMem_empty, ↓reduceIte, Machine.runFrom_bind, ProbOracleComp.sample_pure,
    bind_map_left, pure_bind, Machine.runFrom_map, Machine.runFrom_query, bind_pure_comp,
    map_bind, Functor.map_map, Machine.closeProgram_bind, Machine.closeProgram_sample,
    Machine.closeProgram_map, Machine.closeProgram_pure, ProbComp.eval_bind, ProbComp.eval_map,
    ProbComp.eval_pure, PMF.map, Function.comp_def, PMF.pure_bind, Prod.map_apply, id_eq,
    decide_true, PMF.bind_const]

private theorem eval_gExec_indepCoin_any
    (S : GlobalExecAdversary 1 Unit Bool Unit Unit (RoutedNetQ 1 Unit Unit) (RoutedNetR Bool Unit)
      (netSpec Unit Bool)) (κ : ℕ) (z : List Bool) :
    (GlobalExec coinSetup (indepCoinFunc.toGlobalProtocol) S ∅ coinDistinguisherEnv κ z).eval =
      uniformCoinBool.bind (fun c => uniformCoinBool.map (fun r => decide (r = c))) := by
  have hrunFrom : ∀ (sS : (S κ ∅).State) (r c : Bool),
      (gExecMachine coinSetup (indepCoinFunc.toGlobalProtocol) S κ ∅).runFrom
        (coinDistinguisherEnv κ z) ((sS, r), c) =
      pure (decide (r = c), ((sS, r), c)) := fun sS r c => by
    dsimp only [coinDistinguisherEnv]
    erw [Machine.runFrom_bind, Machine.runFrom_query]
    have hq1 :
        ((gExecMachine coinSetup (indepCoinFunc.toGlobalProtocol) S κ ∅).handle
          (Sum.inl (Sum.inl ((0 : Fin 1), ())))).run ((sS, r), c) =
        pure (some r, ((sS, r), c)) := by
      simp only [gExecMachine, Machine.comp, gLiftAdversary, shareRight, routeCorrupt,
        IdealFunctionality.toGlobalProtocol, indepCoinFunc, coinSetup, StateT.run, StateT.lift,
        Machine.runFrom_map, Machine.runFrom_query, ProbOracleComp.sample_pure, bind_pure_comp,
        Finset.notMem_empty, ↓reduceIte, Functor.map_map]
      rfl
    erw [hq1, pure_bind, Machine.runFrom_bind, Machine.runFrom_query]
    have hq2 :
        ((gExecMachine coinSetup (indepCoinFunc.toGlobalProtocol) S κ ∅).handle
          (Sum.inr ())).run ((sS, r), c) =
        pure (c, ((sS, r), c)) := by
      simp only [gExecMachine, Machine.comp, gLiftAdversary, shareRight, routeCorrupt,
        IdealFunctionality.toGlobalProtocol, indepCoinFunc, coinSetup, StateT.run, StateT.lift,
        Machine.runFrom_map, Machine.runFrom_query, bind_pure_comp, Functor.map_map]
      rfl
    erw [hq2, pure_bind, Machine.runFrom_pure]
    simp only [Option.some.injEq]
    rfl
  rw [GlobalExec, Machine.run, Machine.link, Machine.closeProgram_bind, Machine.closeProgram_sample,
    ProbComp.eval_bind]
  dsimp only [gExecMachine, Machine.comp, shareRight, routeCorrupt, gLiftAdversary,
    IdealFunctionality.toGlobalProtocol, indepCoinFunc, coinSetup]
  simp only [ProbComp.eval_bind, ProbComp.eval_map, ProbComp.eval_pure, PMF.bind_bind,
    PMF.pure_bind, uniformCoinBool, PMF.map, Function.comp_def]
  congr 1; funext rG
  congr 1; funext rP
  have hstep : ∀ (sS : (S κ ∅).State),
      (Machine.closeProgram (Prod.fst <$> (gExecMachine coinSetup
        (indepCoinFunc.toGlobalProtocol) S κ ∅).runFrom (coinDistinguisherEnv κ z)
        ((sS, decide (rP.val = 1)), decide (rG.val = 1)))).eval =
      PMF.pure (decide (decide (rP.val = 1) = decide (rG.val = 1))) := fun sS => by
    erw [hrunFrom sS (decide (rP.val = 1)) (decide (rG.val = 1)), map_pure,
      Machine.closeProgram_pure, ProbComp.eval_pure]
  have hcongr : ((S κ ∅).init.eval.bind fun sS =>
      (Machine.closeProgram (Prod.fst <$> (gExecMachine coinSetup
        (indepCoinFunc.toGlobalProtocol) S κ ∅).runFrom (coinDistinguisherEnv κ z)
        ((sS, decide (rP.val = 1)), decide (rG.val = 1)))).eval) =
      ((S κ ∅).init.eval.bind fun _ =>
        PMF.pure (decide (decide (rP.val = 1) = decide (rG.val = 1)))) := by
    congr 1; funext sS
    exact hstep sS
  dsimp only [gExecMachine, Machine.comp, shareRight, routeCorrupt, gLiftAdversary,
    IdealFunctionality.toGlobalProtocol, indepCoinFunc, coinSetup] at hcongr
  rw [hcongr, PMF.bind_const]

/-- In the global-setup model with shared `coinSetup`, every simulator `S` fails to make
`indepCoinFunc` indistinguishable from `coinReaderProto`: `coinDistinguisherEnv` achieves
exact distinguishing advantage `1 / 2`. -/
theorem gAdvantage_coinSetup_eq_half
    (S : GlobalExecAdversary 1 Unit Bool Unit Unit (RoutedNetQ 1 Unit Unit) (RoutedNetR Bool Unit)
      (netSpec Unit Bool)) (κ : ℕ) (z : List Bool) :
    gAdvantage coinSetup coinReaderProto indepCoinFunc.toGlobalProtocol
      (gDummyAdversary 1 _ _ _) S ∅ coinDistinguisherEnv κ z = (1 / 2 : ℝ≥0) := by
  rw [gAdvantage, eval_gExec_coinReader_dummy, eval_gExec_indepCoin_any,
    Game.advantage_pure_true_left]
  have hfalse : (uniformCoinBool.bind (fun c =>
      uniformCoinBool.map (fun r => decide (r = c)))) false = (1 / 2 : ℝ≥0∞) := by
    rw [PMF.bind_apply, tsum_bool]
    simp only [PMF.map_apply, tsum_bool, uniformCoinBool_apply]
    simp only [decide_false, Bool.false_eq, decide_true, Bool.true_eq_false, ↓reduceIte,
      zero_add, add_zero]
    rw [show (1 / 2 : ℝ≥0∞) * (1 / 2) + (1 / 2) * (1 / 2) = (1 / 2 + 1 / 2) * (1 / 2) by ring,
      ENNReal.add_halves, one_mul]
  rw [Game.failProbability, hfalse]
  rw [← ENNReal.coe_inj, ENNReal.coe_toNNReal (by norm_num)]
  norm_num

/-- **Local-vs-global separation (concrete):** when `coinSetup` is global (`Z` queries it directly),
`coinReaderProto` does not GUC-realize `indepCoinFunc` for any concrete error `< 1 / 2` at `pA = 1`,
`pZ = 2`. -/
theorem not_gRealizesWithin_coinSetup (g : Polynomial ℕ)
    (ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0) (κ : ℕ) (hε : ε 1 2 κ < 1 / 2) :
    ¬ GRealizesWithin coinSetup coinReaderProto indepCoinFunc g ε := by
  intro h
  obtain ⟨S, _, _, _, hadv⟩ := h _ _ (gDummyAdversary 1 _ _ _) 1
    (gDummyAdversary_polyBounded 1 _ _ _)
  have hle := hadv ∅ coinDistinguisherEnv 2 coinDistinguisherEnv_polyBounded κ []
  rw [gAdvantage_coinSetup_eq_half] at hle
  exact not_lt_of_ge hle hε

/-- **Local-vs-global separation (asymptotic):** `coinReaderProto` does not GUC-realize
`indepCoinFunc` with global setup `coinSetup`, even though `localCoinProto` UC-realizes
`indepCoinFunc` with zero error. -/
theorem not_gRealizes_coinSetup :
    ¬ GRealizes coinSetup coinReaderProto indepCoinFunc := by
  intro h
  obtain ⟨S, _, _, hadv⟩ := h _ _ (gDummyAdversary 1 _ _ _) 1
    (gDummyAdversary_polyBounded 1 _ _ _)
  obtain ⟨ν, hν, hbound⟩ := hadv 2
  obtain ⟨m, hm⟩ := (negligible_iff ν).mp hν 0 (1 / 2 : ℝ≥0) (by norm_num)
  have hlt := hm m le_rfl
  simp only [pow_zero, one_mul] at hlt
  have hle := hbound ∅ coinDistinguisherEnv coinDistinguisherEnv_polyBounded m []
  rw [gAdvantage_coinSetup_eq_half] at hle
  exact not_lt_of_ge hle hlt

end Cslib.Crypto.Protocols.UC
