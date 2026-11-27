/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.UC.Adaptive
public import CslibFrontier.Crypto.Protocols.UC.DummyAdversary

/-!
# The adaptive dummy adversary

The adaptive dummy adversary `UC.adaptiveDummyAdversary` forwards every query of the environment
to the routed adaptive network port `AdaptiveNetQ`/`AdaptiveNetR`—including party inputs, `.net`
network messages, and `.corrupt i` queries—and returns every reply and `CorruptionReport` verbatim.

As in the static setting (`CslibFrontier.Crypto.Protocols.UC.DummyAdversary`), simulating the
adaptive dummy adversary suffices for general adaptive UC emulation
(`UC.adaptiveEmulates_iff_adaptiveEmulatesDummy`). The key subtlety relative to static UC is that an
`AdaptiveAdversary` carries its initial corruption set `initial : ℕ → Finset (Fin n)`: since the
environment can inspect `corrupted` via `AdaptivePartyQ.status` (passed straight through by
`UC.liftAdaptiveAdversary`), `UC.AdaptiveEmulatesDummy` and `UC.AdaptiveEmulatesDummyWithin`
quantify `S_D` per `C₀ : ℕ → Finset (Fin n)` (`∀ C₀, ∃ S_D, ...`). Given `A`, composing `A` on top
dummy simulator `S_D` obtained for `C₀ := A.initial` yields `UC.compAdaptiveSim S_D A` with
`initial := S_D.initial`.

Budgets count oracle calls per activation (`Cslib.Crypto.Protocols.UC.Machine.IsBounded`), not
running time; these theorems are call-bounded statistical adaptations of Claim 11 (p. 28:43) of
[Canetti2020] to the snapshot adaptive-corruption model of `UC.Adaptive` (inspired by Section
7.1.1, p. 28:71; §7.1.1's write-once storage restriction remains open).

## Main definitions

* `Cslib.Crypto.Protocols.UC.adaptiveDummyAdversary`: the adaptive forwarding adversary.
* `Cslib.Crypto.Protocols.UC.compAdaptiveSim`: an adversary composed on top of a dummy simulator.
* `Cslib.Crypto.Protocols.UC.absorbAdaptiveAdversary`: an environment running an adversary
  internally while passing party and `.status` queries through unchanged.
* `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesDummyWithin`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesDummy`: concrete and negligible-error emulation of
  the adaptive dummy adversary.

## Main results

* `Cslib.Crypto.Protocols.UC.adaptiveExec_dummyAdversary`,
  `Cslib.Crypto.Protocols.UC.adaptiveExec_eq_adaptiveExec_dummy`,
  `Cslib.Crypto.Protocols.UC.adaptiveExec_compAdaptiveSim`,
  `Cslib.Crypto.Protocols.UC.adaptiveAdvantage_compAdaptiveSim`: execution regrouping laws.
* `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesDummyWithin.emulatesWithin`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesWithin.emulatesDummyWithin`,
  `Cslib.Crypto.Protocols.UC.adaptiveEmulates_iff_adaptiveEmulatesDummy`: adaptive dummy-adversary
  completeness.

## References

* [R. Canetti, *Universally Composable Security*][Canetti2020], Section 4.3 (Claim 11, p. 28:43,
  dummy-adversary completeness) and Section 7.1.1 (p. 28:71, inspiration for the snapshot
  adaptive-corruption model).
-/

public section

namespace Cslib.Crypto.Protocols.UC

open scoped NNReal

variable {n : ℕ} {In Out Q R NetQ NetR View AdvQ AdvR : Type}
  {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ : Type}

/-! ### Adaptive dummy adversary, black-box simulators, and absorbed environments -/

/-- The adaptive dummy adversary with initial corruption set `C₀`, forwarding all network, party,
and `.corrupt` queries and returning all replies and `CorruptionReport`s verbatim. -/
@[expose] def adaptiveDummyAdversary (C₀ : ℕ → Finset (Fin n)) (NetQ NetR : Type) :
    AdaptiveAdversary n In Out NetQ NetR View (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)
    where
  initial := C₀
  machine _ := Machine.id (netSpec (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))

/-- Compose an adversary `A` on top of a dummy-adversary simulator `S_D`, inheriting `S_D`'s
initial corruption set. -/
@[expose] def compAdaptiveSim
    (S_D : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂
      (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁))
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR) :
    AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂ AdvQ AdvR where
  initial := S_D.initial
  machine κ := (A.machine κ).comp (S_D.machine κ)

/-- Absorb an adaptive adversary `A` into the environment `Z`. Party and `.status` queries from `Z`
pass through unchanged to `adaptiveRouter`. -/
@[expose] def absorbAdaptiveAdversary
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) :
    AdaptiveEnvironment n In Out (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View) :=
  fun κ z => (liftAdaptiveAdversary (A.machine κ)).link (Z κ z)

/-- Running the adaptive execution with `adaptiveDummyAdversary` runs `Z` directly against
`adaptiveRouter`. -/
@[simp] theorem adaptiveExec_dummyAdversary (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View) (C₀ : ℕ → Finset (Fin n))
    (Z : AdaptiveEnvironment n In Out (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View))
    (κ : ℕ) (z : List Bool) :
    adaptiveExec mode P (adaptiveDummyAdversary C₀ NetQ NetR) Z κ z =
      (adaptiveRouter mode P κ (C₀ κ)).run (Z κ z) := by
  simp only [adaptiveExec, adaptiveExecMachine, adaptiveDummyAdversary, Machine.run_comp,
    Machine.liftRight_id, Machine.link_id]

/-- Running any adaptive adversary `A` with `Z` equals running `adaptiveDummyAdversary` with
initial set `A.initial` against the absorbed environment `absorbAdaptiveAdversary A Z`. -/
theorem adaptiveExec_eq_adaptiveExec_dummy (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ NetR View)
    (A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec mode P A Z κ z =
      adaptiveExec mode P (adaptiveDummyAdversary A.initial NetQ NetR)
        (absorbAdaptiveAdversary A Z) κ z := by
  simp only [adaptiveExec, adaptiveExecMachine, adaptiveDummyAdversary, absorbAdaptiveAdversary,
    Machine.run_comp, Machine.liftRight_id, Machine.link_id]

/-- Running `compAdaptiveSim S_D A` with `Z` equals running `S_D` with the absorbed environment
`absorbAdaptiveAdversary A Z`. -/
theorem adaptiveExec_compAdaptiveSim (mode : CorruptionMode)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (S_D : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂
      (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁))
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveExec mode Q (compAdaptiveSim S_D A) Z κ z =
      adaptiveExec mode Q S_D (absorbAdaptiveAdversary A Z) κ z := by
  simp only [adaptiveExec, adaptiveExecMachine, compAdaptiveSim, absorbAdaptiveAdversary,
    Machine.run_comp, Machine.liftRight_comp, Machine.link_comp]

/-- Advantage of `Z` against `(P, A)` and `(Q, compAdaptiveSim S_D A)` equals the advantage of
`absorbAdaptiveAdversary A Z` against `(P, adaptiveDummyAdversary A.initial)` and `(Q, S_D)`. -/
theorem adaptiveAdvantage_compAdaptiveSim (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (S_D : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂
      (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁))
    (A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR)
    (Z : AdaptiveEnvironment n In Out AdvQ AdvR) (κ : ℕ) (z : List Bool) :
    adaptiveAdvantage mode P Q A (compAdaptiveSim S_D A) Z κ z =
      adaptiveAdvantage mode P Q (adaptiveDummyAdversary A.initial NetQ₁ NetR₁) S_D
        (absorbAdaptiveAdversary A Z) κ z := by
  rw [adaptiveAdvantage, adaptiveExec_eq_adaptiveExec_dummy, adaptiveExec_compAdaptiveSim]
  rfl

/-- Absorbing the dummy adversary leaves an environment unchanged. -/
@[simp] theorem absorbAdaptiveAdversary_dummy (C₀ : ℕ → Finset (Fin n)) (NetQ NetR : Type)
    (Z : AdaptiveEnvironment n In Out (AdaptiveNetQ n In NetQ) (AdaptiveNetR Out NetR View)) :
    absorbAdaptiveAdversary (adaptiveDummyAdversary (View := View) C₀ NetQ NetR) Z = Z := by
  funext κ z
  simp only [absorbAdaptiveAdversary, adaptiveDummyAdversary, Machine.liftRight_id,
    Machine.link_id]

/-! ### Budgets -/

/-- The adaptive dummy adversary makes at most one call per activation. -/
theorem adaptiveDummyAdversary_polyBounded (C₀ : ℕ → Finset (Fin n)) (NetQ NetR : Type) :
    (adaptiveDummyAdversary (In := In) (Out := Out) (View := View) C₀ NetQ NetR).PolyBounded 1 :=
  fun _ => (Machine.isBounded_id _).mono (by simp)

/-- Composing `A` (budget `pA`) on top of `S_D` (budget `pD`) gives budget `pA * (pD + 1) + pD`. -/
theorem compAdaptiveSim_polyBounded
    {S_D : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂
      (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁)}
    {A : AdaptiveAdversary n In Out NetQ₁ NetR₁ View₁ AdvQ AdvR}
    {pD pA : Polynomial ℕ} (hS : S_D.PolyBounded pD) (hA : A.PolyBounded pA) :
    (compAdaptiveSim S_D A).PolyBounded (pA * (pD + 1) + pD) := fun κ => by
  have h := (hA κ).comp (hS κ)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one]
  exact h

/-- Absorbing an adaptive adversary with budget `pA` into an environment with budget `pZ` gives
budget `absorbPoly pZ pA`. -/
theorem absorbAdaptiveAdversary_polyBounded
    {A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR}
    {Z : AdaptiveEnvironment n In Out AdvQ AdvR} {pA pZ : Polynomial ℕ}
    (hA : A.PolyBounded pA) (hZ : Z.PolyBounded pZ) :
    (absorbAdaptiveAdversary A Z).PolyBounded (absorbPoly pZ pA) := fun κ z => by
  have h := Machine.isQueryBounded_link
    (Machine.isBounded_liftRight (adaptivePartySpec n In Out) (hA κ)) (hZ κ z)
  refine h.mono (le_of_eq ?_)
  rw [eval_absorbPoly]

/-! ### Completeness of the adaptive dummy adversary -/

/-- Concrete emulation of the adaptive dummy adversary under `mode` in the snapshot
adaptive-corruption model of `UC.Adaptive` (statistical, call-bounded adaptation of [Canetti2020],
Definition 10 and Claim 11, p. 28:43; §7.1.1 write-once storage remains open): for every initial
corruption schedule `C₀`, there exists a simulator `S_D` with call budget `pD` such that every
environment `Z` with budget `pZ` has advantage at most `ε pZ κ`. Quantifying `C₀` outside `S_D`
lets `S_D.initial` match `C₀`, which `.status` makes observable. -/
@[expose] def AdaptiveEmulatesDummyWithin (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂)
    (pD : Polynomial ℕ) (ε : Polynomial ℕ → ℕ → ℝ≥0) : Prop :=
  ∀ C₀ : ℕ → Finset (Fin n),
    ∃ S_D : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂
        (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁),
      S_D.PolyBounded pD ∧
        ∀ (Z : AdaptiveEnvironment n In Out
            (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁))
          (pZ : Polynomial ℕ), Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
            adaptiveAdvantage mode P Q (adaptiveDummyAdversary C₀ NetQ₁ NetR₁) S_D Z κ z ≤ ε pZ κ

/-- Completeness of the adaptive dummy adversary (concrete): simulating the dummy adversary implies
general adaptive emulation with simulator overhead `X * (pD + 1) + pD` and error evaluated at the
absorbed environment budget `absorbPoly pZ pA`. -/
theorem AdaptiveEmulatesDummyWithin.emulatesWithin {mode : CorruptionMode}
    {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {pD : Polynomial ℕ} {ε : Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesDummyWithin mode P Q pD ε) :
    AdaptiveEmulatesWithin mode P Q (Polynomial.X * (pD + 1) + pD)
      (fun pA pZ => ε (absorbPoly pZ pA)) := by
  intro AdvQ AdvR A pA hA
  obtain ⟨S_D, hS, hadv⟩ := h A.initial
  refine ⟨compAdaptiveSim S_D A, pA * (pD + 1) + pD,
    compAdaptiveSim_polyBounded hS hA, simPolyBound_compSim pD pA, fun Z pZ hZ κ z => ?_⟩
  rw [adaptiveAdvantage_compAdaptiveSim]
  exact hadv _ _ (absorbAdaptiveAdversary_polyBounded hA hZ) κ z

/-- Concrete adaptive emulation implies concrete dummy-adversary emulation with budget
`g.comp (X + 1)`. -/
theorem AdaptiveEmulatesWithin.emulatesDummyWithin {mode : CorruptionMode}
    {P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁}
    {Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂}
    {g : Polynomial ℕ} {ε : Polynomial ℕ → Polynomial ℕ → ℕ → ℝ≥0}
    (h : AdaptiveEmulatesWithin mode P Q g ε) :
    AdaptiveEmulatesDummyWithin mode P Q (g.comp (Polynomial.X + 1)) (fun pZ => ε 1 pZ) := by
  intro C₀
  obtain ⟨S_D, pD, hS, hSg, hadv⟩ := h _ _ (adaptiveDummyAdversary C₀ NetQ₁ NetR₁) 1
    (adaptiveDummyAdversary_polyBounded C₀ NetQ₁ NetR₁)
  refine ⟨S_D, hS.mono fun κ => ?_, hadv⟩
  simpa only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    using hSg κ

/-- Negligible-error emulation of the adaptive dummy adversary under `mode` in the snapshot
adaptive-corruption model of `UC.Adaptive` (statistical, call-bounded adaptation of [Canetti2020],
Claim 11, p. 28:43; §7.1.1 write-once storage remains open). -/
@[expose] def AdaptiveEmulatesDummy (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂) : Prop :=
  ∀ C₀ : ℕ → Finset (Fin n),
    ∃ (S_D : AdaptiveAdversary n In Out NetQ₂ NetR₂ View₂
        (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁)) (pD : Polynomial ℕ),
      S_D.PolyBounded pD ∧
        ∀ pZ : Polynomial ℕ, ∃ ν : ℕ → ℝ≥0, Negligible ν ∧
          ∀ (Z : AdaptiveEnvironment n In Out
              (AdaptiveNetQ n In NetQ₁) (AdaptiveNetR Out NetR₁ View₁)),
            Z.PolyBounded pZ → ∀ (κ : ℕ) (z : List Bool),
              adaptiveAdvantage mode P Q
                (adaptiveDummyAdversary C₀ NetQ₁ NetR₁) S_D Z κ z ≤ ν κ

/-- Completeness of the adaptive dummy adversary (negligible error) in the snapshot
adaptive-corruption model of `UC.Adaptive`: adaptive UC emulation is equivalent to simulating the
adaptive dummy adversary (call-bounded adaptation of [Canetti2020], Claim 11, p. 28:43). -/
theorem adaptiveEmulates_iff_adaptiveEmulatesDummy (mode : CorruptionMode)
    (P : AdaptiveProtocol n In Out NetQ₁ NetR₁ View₁)
    (Q : AdaptiveProtocol n In Out NetQ₂ NetR₂ View₂) :
    AdaptiveEmulates mode P Q ↔ AdaptiveEmulatesDummy mode P Q := by
  constructor
  · intro h C₀
    exact h _ _ (adaptiveDummyAdversary C₀ NetQ₁ NetR₁) 1
      (adaptiveDummyAdversary_polyBounded C₀ NetQ₁ NetR₁)
  · intro h AdvQ AdvR A pA hA
    obtain ⟨S_D, pD, hS, hadv⟩ := h A.initial
    refine ⟨compAdaptiveSim S_D A, pA * (pD + 1) + pD,
      compAdaptiveSim_polyBounded hS hA, fun pZ => ?_⟩
    obtain ⟨ν, hν, hbound⟩ := hadv (absorbPoly pZ pA)
    refine ⟨ν, hν, fun Z hZ κ z => ?_⟩
    rw [adaptiveAdvantage_compAdaptiveSim]
    exact hbound _ (absorbAdaptiveAdversary_polyBounded hA hZ) κ z

end Cslib.Crypto.Protocols.UC
