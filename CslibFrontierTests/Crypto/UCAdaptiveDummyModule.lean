/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: local-only (test)

import CslibFrontier.Crypto.Protocols.UC.AdaptiveToStatic
import CslibFrontier.Crypto.Protocols.UC.AdaptiveDummyAdversary

/-!
# Module-mode client of `AdaptiveToStatic` and `AdaptiveDummyAdversary`

Ordinary `module` client exercising `AdaptiveAdversary.clampStatic`, the static-from-adaptive
emulation bridges (`AdaptiveEmulatesWithin.static_of_adaptive`,
`AdaptiveEmulates.static_of_adaptive`), and adaptive dummy-adversary completeness
(`adaptiveDummyAdversary`, `compAdaptiveSim`, `absorbAdaptiveAdversary`,
`adaptiveEmulates_iff_adaptiveEmulatesDummy`) through public exports alone.
-/

namespace CslibFrontierTests.Crypto.UCAdaptiveDummyModule

open Cslib Cslib.Crypto Cslib.Crypto.Protocols.UC
open scoped NNReal

-- Clamping any adversary enforces `NoNewCorrupt` and preserves `PolyBounded`, and `.static`
-- execution matches `.adaptive` execution with `clampStatic`.
example (P : AdaptiveProtocol 1 Unit Unit Unit Unit Unit)
    (Z : AdaptiveEnvironment 1 Unit Unit Unit (AdaptiveNetR Unit Unit Unit))
    (κ : ℕ) (z : List Bool) :
    let eagerCorruptAdv : AdaptiveAdversary 1 Unit Unit Unit Unit Unit
        Unit (AdaptiveNetR Unit Unit Unit) :=
      { initial := fun _ => ∅
        machine := fun _ =>
          { State := Unit
            init := pure ()
            handle := fun _ _ => do
              let r ← ProbOracleComp.query
                (spec := netSpec (AdaptiveNetQ 1 Unit Unit) (AdaptiveNetR Unit Unit Unit))
                (.corrupt 0)
              pure (r, ()) } }
    eagerCorruptAdv.clampStatic.NoNewCorrupt ∧
      (eagerCorruptAdv.PolyBounded 1 → eagerCorruptAdv.clampStatic.PolyBounded 1) ∧
      adaptiveExec .static P eagerCorruptAdv Z κ z =
        adaptiveExec .adaptive P eagerCorruptAdv.clampStatic Z κ z := by
  intro eagerCorruptAdv
  exact ⟨eagerCorruptAdv.noNewCorrupt_clampStatic,
    fun hA => hA.clampStatic,
    adaptiveExec_static_eq_adaptive_clampStatic P eagerCorruptAdv Z κ z⟩

-- An ordinary client can compose `AdaptiveEmulatesWithin.refl`, `static_of_adaptive`, and
-- `emulatesDummyWithin` / `adaptiveEmulates_iff_adaptiveEmulatesDummy`.
example :
    let trivialIdeal : IdealFunctionality 1 Unit Unit Unit Unit :=
      { State := Unit
        init := fun _ _ => pure ()
        onInput := fun _ _ => pure none
        onBackdoor := fun _ => pure () }
    let trivialProtocol : AdaptiveProtocol 1 Unit Unit Unit Unit Unit :=
      trivialIdeal.toAdaptive fun _ _ _ => ()
    AdaptiveEmulatesWithin .static trivialProtocol trivialProtocol Polynomial.X (fun _ _ _ => 0) ∧
      AdaptiveEmulates .static trivialProtocol trivialProtocol ∧
      AdaptiveEmulatesDummyWithin .adaptive trivialProtocol trivialProtocol
        (Polynomial.X.comp (Polynomial.X + 1)) (fun _ _ => 0) ∧
      AdaptiveEmulatesDummy .adaptive trivialProtocol trivialProtocol := by
  intro trivialIdeal trivialProtocol
  have hwithin := AdaptiveEmulatesWithin.refl .adaptive trivialProtocol
  have hemul : AdaptiveEmulates .adaptive trivialProtocol trivialProtocol :=
    hwithin.emulates fun _ _ _ => by simp
  exact ⟨hwithin.static_of_adaptive, hemul.static_of_adaptive,
    hwithin.emulatesDummyWithin,
    (adaptiveEmulates_iff_adaptiveEmulatesDummy .adaptive trivialProtocol trivialProtocol).mp hemul⟩

-- Dummy-adversary execution and simulator composition work through ordinary imports.
example (P : AdaptiveProtocol 1 Unit Unit Unit Unit Unit)
    (A : AdaptiveAdversary 1 Unit Unit Unit Unit Unit Unit (AdaptiveNetR Unit Unit Unit))
    (Zdummy : AdaptiveEnvironment 1 Unit Unit
      (AdaptiveNetQ 1 Unit Unit) (AdaptiveNetR Unit Unit Unit))
    (Z : AdaptiveEnvironment 1 Unit Unit Unit (AdaptiveNetR Unit Unit Unit))
    (κ : ℕ) (z : List Bool) :
    adaptiveExec .adaptive P (adaptiveDummyAdversary (fun _ => ∅) Unit Unit)
        Zdummy κ z =
      (adaptiveRouter .adaptive P κ ∅).run (Zdummy κ z) ∧
      adaptiveAdvantage .adaptive P P A
        (compAdaptiveSim (adaptiveDummyAdversary (fun _ => ∅) Unit Unit) A)
        Z κ z =
      adaptiveAdvantage .adaptive P P
        (adaptiveDummyAdversary A.initial Unit Unit)
        (adaptiveDummyAdversary (fun _ => ∅) Unit Unit)
        (absorbAdaptiveAdversary A Z) κ z :=
  ⟨adaptiveExec_dummyAdversary .adaptive P (fun _ => ∅) Zdummy κ z,
    adaptiveAdvantage_compAdaptiveSim .adaptive P P
      (adaptiveDummyAdversary (fun _ => ∅) Unit Unit) A Z κ z⟩

end CslibFrontierTests.Crypto.UCAdaptiveDummyModule
