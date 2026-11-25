/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SSP.Basic
public import CslibFrontier.Crypto.Protocols.UC.Composition

/-!
# Ideal functionalities with a private outgoing call port

This module defines `UC.HybridFunctionality`, an `n`-party ideal functionality equipped with a
private outgoing call port `G`, in this library's call-and-return, call-bounded port model.
Each activation (`onInput` for party inputs and `onBackdoor` for adversary backdoor queries) is a
stateful `ProbOracleComp G` program that may call `G` and wait for the answer before continuing.
Closing `F` with a closed resource machine `R κ C : Machine OracleSpec.empty G` via
`HybridFunctionality.close F R` yields an ordinary `UC.Protocol` by sequential machine composition
`(F.toMachine κ C).comp (R κ C)`, reusing `Machine.comp` from
`CslibFrontier.Crypto.Protocols.UC.Machine`.

## Model and scope

* **Library construction (no cited definition).** In the interactive Turing machine model of
  [Canetti2020], Section 3.1.2 (JACM p. 28:23), the external-write instruction lets an ITI
  write to a tape of another ITI, subject to the control function, which determines which
  external-write instructions are allowed; `HybridFunctionality` restricts outgoing calls to
  call-and-return oracle invocations (`ProbOracleComp G`).
* **Private resource.** In `HybridFunctionality.close F R`, neither the environment nor the
  adversary can reach `G` directly; any adversary access to the resource must be forwarded by `F`
  through `onBackdoor`. By contrast, the library's routed `UC.HybridProtocol` construction
  (`CslibFrontier.Crypto.Protocols.UC.Composition`) routes subroutine calls behind `corruptRouter`
  and exposes the subroutine's routed network port to the adversary.
* **Initialization order and indexing.** Like a `UC.Protocol`, the resource `R` is indexed by
  `(κ, C)`. Because `close` is `Machine.comp`, `R κ C` is initialized before `F.init κ C`.
* **Call-bounded budgets.** As throughout `CslibFrontier.Crypto.Protocols.UC`, budgets
  (`Machine.IsBounded`, `Protocol.PolyBounded`) count oracle calls and private samples only, leaving
  local computation unbounded; computational polynomial-time machine execution is open in #6043.

## Main definitions

* `Cslib.Crypto.Protocols.UC.HybridFunctionality`: an `n`-party ideal functionality with a private
  outgoing call port `G`.
* `Cslib.Crypto.Protocols.UC.HybridFunctionality.toMachine`: the interactive machine of a hybrid
  functionality, exporting the party and backdoor ports and importing `G`.
* `Cslib.Crypto.Protocols.UC.HybridFunctionality.close`: closing a hybrid functionality with a
  private resource `R` to obtain a `UC.Protocol`.
* `Cslib.Crypto.Protocols.UC.IdealFunctionality.toHybrid`: viewing a closed `IdealFunctionality` as
  a hybrid functionality over `OracleSpec.empty`.

## Main results

* `Cslib.Crypto.Protocols.UC.IdealFunctionality.toHybrid_toMachine`: `toHybrid` followed by
  `toMachine` recovers `IdealFunctionality.toProtocol`.
* `Cslib.Crypto.Protocols.UC.HybridFunctionality.close_polyBounded`: closing a bounded hybrid
  functionality with a bounded resource yields a bounded protocol.
* `Cslib.Crypto.Protocols.UC.HybridFunctionality.exec_close`: the UC execution of `F.close R` is the
  exact program obtained by running the resource `R κ C` against the reduction program linking
  `absorbAdversary C A Z κ z` with `routeCorrupt C (F.toMachine κ C)`.
* `Cslib.Crypto.Protocols.UC.HybridFunctionality.advantage_close`: swapping the private resource of
  a hybrid functionality reduces to the `SSP.advantage` between the two resources for that explicit
  reduction program.
* `Cslib.Crypto.Protocols.UC.HybridFunctionality.isQueryBounded_closeReduction`: polynomial call
  budget for the resource-swap reduction program.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], J. ACM 67(5), Article 28, 2020,
  Section 3.1.2 (JACM p. 28:23): the general external-write mechanism that motivates
  functionalities invoking subroutines (restricted here to call-and-return with a private resource).
* [C. Brzuska, A. Delignat-Lavaud, C. Fournet, K. Kohbrok, M. Kohlweiss, *State Separation for
  Code-Based Game-Playing Proofs*][BrzuskaDFKK2018]: the package-algebra reduction behind
  `SSP.advantage_comp`.
-/

public section

namespace Cslib.Crypto.Protocols.UC

open scoped NNReal

/-- Library construction (no cited definition): an `n`-party ideal functionality with a private
outgoing call port `G` in this library's call-and-return reading, where `onInput` and `onBackdoor`
may call `G` and wait for the answer. The general mechanism in [Canetti2020], Section 3.1.2
(JACM p. 28:23), is the external-write instruction, restricted here to call-and-return. -/
structure HybridFunctionality (n : ℕ) (In Out BackQ BackR : Type) {ιG : Type} (G : ιG → Type) :
    Type 1 where
  /-- The private state. -/
  State : Type
  /-- The initial state, given the security parameter and the corrupted parties. -/
  init : ℕ → Finset (Fin n) → ProbComp State
  /-- Party `i` gives input `x` (or polls) and receives its pending output, if any; the activation
  may call the resource port `G`. -/
  onInput : Fin n → In → StateT State (ProbOracleComp G) (Option Out)
  /-- A backdoor query of the adversary; the activation may call the resource port `G`. -/
  onBackdoor : BackQ → StateT State (ProbOracleComp G) BackR

variable {n : ℕ} {In Out BackQ BackR AdvQ AdvR : Type} {ιG : Type} {G : ιG → Type}

/-- Library construction (no cited result): the interactive machine of `F` for security parameter
`κ` and corrupted parties `C`: party inputs go to `onInput`, the network port is the backdoor, and
resource calls go out on `G`. -/
@[expose] def HybridFunctionality.toMachine (F : HybridFunctionality n In Out BackQ BackR G)
    (κ : ℕ) (C : Finset (Fin n)) : Machine G (protocolSpec n In Out BackQ BackR) where
  State := F.State
  init := F.init κ C
  handle
    | .inl (i, x) => F.onInput i x
    | .inr q => F.onBackdoor q

/-- Library construction (no cited result): `F` with its resource calls answered by `R`, a private
resource indexed by `(κ, C)` that neither the environment nor the adversary can reach directly
(any adversary access must be forwarded by `F` through `onBackdoor`). Because `close` uses
`Machine.comp`, `R κ C` is initialized before `F.init κ C`. -/
@[expose] def HybridFunctionality.close (F : HybridFunctionality n In Out BackQ BackR G)
    (R : ℕ → Finset (Fin n) → Machine OracleSpec.empty G) : Protocol n In Out BackQ BackR :=
  fun κ C => (F.toMachine κ C).comp (R κ C)

/-- Library construction (no cited result): an ideal functionality viewed as a hybrid functionality
over the empty resource interface `OracleSpec.empty`. -/
@[expose] def IdealFunctionality.toHybrid (F : IdealFunctionality n In Out BackQ BackR) :
    HybridFunctionality n In Out BackQ BackR OracleSpec.empty where
  State := F.State
  init := F.init
  onInput i x s := ProbOracleComp.sample ((F.onInput i x).run s)
  onBackdoor q s := ProbOracleComp.sample ((F.onBackdoor q).run s)

/-- Library infrastructure (no cited result): converting an ideal functionality to a hybrid
functionality and then to a machine recovers `IdealFunctionality.toProtocol`. -/
@[simp] theorem IdealFunctionality.toHybrid_toMachine (F : IdealFunctionality n In Out BackQ BackR)
    (κ : ℕ) (C : Finset (Fin n)) : F.toHybrid.toMachine κ C = F.toProtocol κ C :=
  rfl

/-- Library infrastructure (no cited result), in this library's call-bounded port model (budgets
bound oracle call counts only; computational polynomial time is open in #6043): closing a bounded
hybrid functionality with a bounded resource gives a bounded protocol. -/
theorem HybridFunctionality.close_polyBounded {F : HybridFunctionality n In Out BackQ BackR G}
    {R : ℕ → Finset (Fin n) → Machine OracleSpec.empty G} {p q : Polynomial ℕ}
    (hF : ∀ κ C, (F.toMachine κ C).IsBounded (p.eval κ))
    (hR : ∀ κ C, (R κ C).IsBounded (q.eval κ)) :
    (F.close R).PolyBounded (p * (q + 1) + q) := fun κ C => by
  simpa only [close, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] using
    (hF κ C).comp (hR κ C)

/-- Library infrastructure (no cited result): running the UC execution of `F.close R` is, as an
exact equation of programs, running the private resource `R κ C` against the program that links
`absorbAdversary C A Z κ z` with the corruption-routed machine `routeCorrupt C (F.toMachine κ C)`.
-/
theorem HybridFunctionality.exec_close (F : HybridFunctionality n In Out BackQ BackR G)
    (R : ℕ → Finset (Fin n) → Machine OracleSpec.empty G)
    (A : ExecAdversary n In Out BackQ BackR AdvQ AdvR) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    exec (F.close R) A C Z κ z =
      (R κ C).run
        ((routeCorrupt C (F.toMachine κ C)).link (absorbAdversary C A Z κ z)) := by
  simp only [exec, execMachine, close, corruptRouter_comp, Machine.run_comp, absorbAdversary]

/-- Library infrastructure (no cited result): swapping the private resource of a hybrid
functionality is a state-separating reduction. The environment's advantage between `F.close R` and
`F.close R'` (with the same adversary) equals the `SSP.advantage` between the two resources for the
program that links `absorbAdversary C A Z κ z` with `routeCorrupt C (F.toMachine κ C)`. -/
theorem HybridFunctionality.advantage_close (F : HybridFunctionality n In Out BackQ BackR G)
    (R R' : ℕ → Finset (Fin n) → Machine OracleSpec.empty G)
    (A : ExecAdversary n In Out BackQ BackR AdvQ AdvR) (C : Finset (Fin n))
    (Z : Environment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    UC.advantage (F.close R) (F.close R') A A C Z κ z =
      SSP.advantage
        ((routeCorrupt C (F.toMachine κ C)).link (absorbAdversary C A Z κ z))
        (R κ C) (R' κ C) := by
  simp only [advantage, exec, execMachine, close, corruptRouter_comp, absorbAdversary]
  exact (SSP.advantage_comp (Z κ z) (liftAdversary (A κ C)) _ _).trans
    (SSP.advantage_comp _ (routeCorrupt C (F.toMachine κ C)) _ _)

/-- Library infrastructure (no cited result), in this library's call-bounded port model (budgets
bound oracle call counts only; computational polynomial time is open in #6043): call budget for
the resource-swap reduction program in `HybridFunctionality.advantage_close`. -/
theorem HybridFunctionality.isQueryBounded_closeReduction
    {F : HybridFunctionality n In Out BackQ BackR G}
    {A : ExecAdversary n In Out BackQ BackR AdvQ AdvR}
    {Z : Environment n In Out AdvQ AdvR} {pF pA pZ : Polynomial ℕ}
    (hF : ∀ κ C, (F.toMachine κ C).IsBounded (pF.eval κ))
    (hA : A.PolyBounded pA) (hZ : Z.PolyBounded pZ)
    (C : Finset (Fin n)) (κ : ℕ) (z : List Bool) :
    OracleComp.IsQueryBounded
      ((routeCorrupt C (F.toMachine κ C)).link (absorbAdversary C A Z κ z))
      (pF.eval κ + (absorbPoly pZ pA).eval κ * (pF.eval κ + 1)) :=
  Machine.isQueryBounded_link (isBounded_routeCorrupt C (hF κ C))
    (absorbAdversary_polyBounded C hA hZ κ z)

end Cslib.Crypto.Protocols.UC
