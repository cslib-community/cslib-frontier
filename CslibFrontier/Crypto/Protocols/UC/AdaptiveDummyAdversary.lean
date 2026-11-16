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
[Canetti2020] to the adaptive execution model of Section 7.1.1 (p. 28:71).

## Main definitions

* `Cslib.Crypto.Protocols.UC.adaptiveDummyAdversary`: the adaptive forwarding adversary.
* `Cslib.Crypto.Protocols.UC.compAdaptiveSim`: an adversary composed on top of a dummy simulator.
* `Cslib.Crypto.Protocols.UC.absorbAdaptiveAdversary`: an environment running an adversary
  internally while passing party and `.status` queries through unchanged.
* `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesDummyWithin`,
  `Cslib.Crypto.Protocols.UC.AdaptiveEmulatesDummy`: concrete and negligible-error emulation of
  the adaptive dummy adversary.

## Main results

* `Cslib.Crypto.Protocols.UC.liftAdaptiveAdversary_id`,
  `Cslib.Crypto.Protocols.UC.liftAdaptiveAdversary_comp`: forwarding and composition laws for
  `UC.liftAdaptiveAdversary`.
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
  dummy-adversary completeness) and Section 7.1.1 (p. 28:71, adaptive corruptions).
-/

public section

namespace Cslib.Crypto.Protocols.UC

open scoped NNReal

variable {n : ℕ} {In Out Q R NetQ NetR View AdvQ AdvR : Type}
  {NetQ₁ NetR₁ View₁ NetQ₂ NetR₂ View₂ : Type} {α : Type}

/-! ### Programs on the adaptive network port -/

section LiftAdaptiveNet

/-- Running a lifted network program against a lifted adversary equals lifting the run against
the adversary. -/
theorem runFrom_liftAdaptiveAdversary_liftAdaptiveNet
    (S : Machine (netSpec Q R) (netSpec AdvQ AdvR))
    (program : ProbOracleComp (netSpec AdvQ AdvR) α) (s : S.State) :
    (liftAdaptiveAdversary (n := n) (In := In) (Out := Out) S).runFrom
        (liftAdaptiveNet program) s =
      liftAdaptiveNet (S.runFrom program s) := by
  induction program using OracleComp.induction generalizing s with
  | pure a => rfl
  | query_bind q cont ih =>
    cases q with
    | inl k =>
      have h₁ : liftAdaptiveNet (n := n) (In := In) (Out := Out)
          (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR)) (Sum.inl k)) =
          ProbOracleComp.sample (ProbComp.unifFin k) := by
        rw [← liftAdaptiveNet_sample (Q := AdvQ) (R := AdvR)]
        rfl
      have h₂ : S.runFrom (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR))
          (Sum.inl k)) s = (fun a => (a, s)) <$> ProbOracleComp.sample (ProbComp.unifFin k) :=
        S.runFrom_sample (ProbComp.unifFin k) s
      rw [liftAdaptiveNet_bind, h₁, Machine.runFrom_bind, h₂, liftAdaptiveNet_bind,
        liftAdaptiveNet_map, liftAdaptiveNet_sample, bind_map_left]
      erw [Machine.runFrom_bind, Machine.runFrom_sample, bind_map_left]
      exact bind_congr fun a => ih a s
    | inr e =>
      rw [liftAdaptiveNet_bind, Machine.runFrom_bind, liftAdaptiveNet_bind]
      erw [Machine.runFrom_bind]
      have h₁ : (liftAdaptiveAdversary (n := n) (In := In) (Out := Out) S).runFrom
          (liftAdaptiveNet (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR))
            (Sum.inr e))) s =
          liftAdaptiveNet (S.runFrom
            (OracleComp.query (spec := probOracleSpec (netSpec AdvQ AdvR)) (Sum.inr e)) s) := by
        erw [liftAdaptiveNet_query, Machine.runFrom_query, Machine.runFrom_query]
        rfl
      exact (congrArg (fun m => m >>= _) h₁).trans
        (bind_congr fun (x : AdvR × S.State) => ih x.1 x.2)

end LiftAdaptiveNet

/-! ### The lifted adaptive adversary -/

/-- Placing the forwarding machine in front of the adaptive network gives the forwarding machine. -/
@[simp] theorem liftAdaptiveAdversary_id :
    liftAdaptiveAdversary (n := n) (In := In) (Out := Out) (Machine.id (netSpec Q R)) =
      Machine.id (adaptivePartySpec n In Out ⊕ₒ netSpec Q R) := by
  simp only [liftAdaptiveAdversary, Machine.id]
  congr 1 with q s : 2
  cases q with
  | inl p => rfl
  | inr q =>
    change liftAdaptiveNet ((fun a => (a, s)) <$> ProbOracleComp.query q) = _
    rw [liftAdaptiveNet_map, liftAdaptiveNet_query]
    rfl

/-- Placing a composition in front of the adaptive network composes the lifted machines. -/
theorem liftAdaptiveAdversary_comp
    (A : Machine (netSpec Q R) (netSpec AdvQ AdvR))
    (S : Machine (netSpec NetQ NetR) (netSpec Q R)) :
    liftAdaptiveAdversary (n := n) (In := In) (Out := Out) (A.comp S) =
      (liftAdaptiveAdversary A).comp (liftAdaptiveAdversary S) := by
  simp only [liftAdaptiveAdversary, Machine.comp]
  congr 1 with q s : 2
  cases q with
  | inl p =>
    change (StateT.lift (ProbOracleComp.query
        (spec := adaptivePartySpec n In Out ⊕ₒ netSpec NetQ NetR) (Sum.inl p))) s =
      Equiv.prodAssoc _ _ _ <$>
        (liftAdaptiveAdversary (n := n) (In := In) (Out := Out) S).runFrom
          ((StateT.lift (ProbOracleComp.query
            (spec := adaptivePartySpec n In Out ⊕ₒ netSpec Q R) (Sum.inl p))).run s.1) s.2
    simp only [StateT.lift, StateT.run, bind_pure_comp]
    erw [Machine.runFrom_map, Machine.runFrom_query]
    simp only [liftAdaptiveAdversary, StateT.lift, StateT.run, bind_pure_comp, Functor.map_map]
    rfl
  | inr e =>
    change liftAdaptiveNet (Equiv.prodAssoc _ _ _ <$> S.runFrom ((A.handle e).run s.1) s.2) =
      Equiv.prodAssoc _ _ _ <$>
        (liftAdaptiveAdversary S).runFrom (liftAdaptiveNet ((A.handle e).run s.1)) s.2
    rw [runFrom_liftAdaptiveAdversary_liftAdaptiveNet, liftAdaptiveNet_map]
    rfl

/-- Lifting to the adaptive network port preserves call count. -/
theorem isQueryBounded_liftAdaptiveNet {α : Type}
    {program : ProbOracleComp (netSpec Q R) α} {m : ℕ} (h : program.IsQueryBounded m) :
    (liftAdaptiveNet (n := n) (In := In) (Out := Out) program).IsQueryBounded m := by
  refine OracleComp.IsCostBounded.interpret (fun q => ?_) h
  cases q with
  | inl _ => exact OracleComp.IsCostBounded.query _
  | inr _ => exact OracleComp.IsCostBounded.query _

/-- Lifting a machine with at most `t` calls per activation gives at most `t + 1` calls per
activation: party and `.status` queries pass through with one call. -/
theorem isBounded_liftAdaptiveAdversary {M : Machine (netSpec Q R) (netSpec AdvQ AdvR)} {t : ℕ}
    (h : M.IsBounded t) :
    (liftAdaptiveAdversary (n := n) (In := In) (Out := Out) M).IsBounded (t + 1) := by
  refine ⟨h.1.mono (Nat.le_succ t), fun q s => ?_⟩
  cases q with
  | inl p =>
    change ((fun a => (a, s)) <$> ProbOracleComp.query _).IsQueryBounded _
    exact (OracleComp.isCostBounded_map_iff _ _ _).mpr
      ((OracleComp.IsCostBounded.query _).mono (by omega))
  | inr q => exact (isQueryBounded_liftAdaptiveNet (h.2 q s)).mono (Nat.le_succ t)

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
    liftAdaptiveAdversary_id, Machine.link_id]

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
    Machine.run_comp, liftAdaptiveAdversary_id, Machine.link_id]

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
    Machine.run_comp, liftAdaptiveAdversary_comp, Machine.link_comp]

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
  simp only [absorbAdaptiveAdversary, adaptiveDummyAdversary, liftAdaptiveAdversary_id,
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

/-- `compAdaptiveSim`'s budget is bounded by `X * (pD + 1) + pD` at `κ + pA.eval κ`. -/
theorem simPolyBound_compAdaptiveSim (pD pA : Polynomial ℕ) :
    SimPolyBound (Polynomial.X * (pD + 1) + pD) pA (pA * (pD + 1) + pD) := fun κ => by
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one]
  have hD : pD.eval κ ≤ pD.eval (κ + pA.eval κ) := pD.eval_mono (Nat.le_add_right _ _)
  exact Nat.add_le_add (Nat.mul_le_mul (Nat.le_add_left _ _) (Nat.add_le_add_right hD 1)) hD

/-- Absorbing an adaptive adversary with budget `pA` into an environment with budget `pZ` gives
budget `absorbPoly pZ pA`. -/
theorem absorbAdaptiveAdversary_polyBounded
    {A : AdaptiveAdversary n In Out NetQ NetR View AdvQ AdvR}
    {Z : AdaptiveEnvironment n In Out AdvQ AdvR} {pA pZ : Polynomial ℕ}
    (hA : A.PolyBounded pA) (hZ : Z.PolyBounded pZ) :
    (absorbAdaptiveAdversary A Z).PolyBounded (absorbPoly pZ pA) := fun κ z => by
  have h := Machine.isQueryBounded_link (isBounded_liftAdaptiveAdversary (hA κ)) (hZ κ z)
  refine h.mono (le_of_eq ?_)
  rw [eval_absorbPoly]

/-! ### Completeness of the adaptive dummy adversary -/

/-- Concrete emulation of the adaptive dummy adversary under `mode` (statistical, call-bounded
adaptation of [Canetti2020], Definition 10 and Claim 11, p. 28:43): for every initial corruption
schedule `C₀`, there exists a simulator `S_D` with call budget `pD` such that every environment `Z`
with budget `pZ` has advantage at most `ε pZ κ`. Quantifying `C₀` outside `S_D` lets `S_D.initial`
match `C₀`, which `.status` makes observable. -/
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
    compAdaptiveSim_polyBounded hS hA, simPolyBound_compAdaptiveSim pD pA, fun Z pZ hZ κ z => ?_⟩
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

/-- Negligible-error emulation of the adaptive dummy adversary under `mode` (statistical,
call-bounded adaptation of [Canetti2020], Claim 11, p. 28:43). -/
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

/-- Completeness of the adaptive dummy adversary (negligible error): adaptive UC emulation is
equivalent to simulating the adaptive dummy adversary (call-bounded adaptation of [Canetti2020],
Claim 11, p. 28:43). -/
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
