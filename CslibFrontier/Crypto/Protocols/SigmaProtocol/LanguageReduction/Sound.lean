/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Interactive
import CslibFrontier.Computability.Interactive.StatementMap
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction

/-!
# Soundness of derived Sigma protocols

Soundness transfer for `SigmaProtocol.comap` under condition (ii) of a language reduction
([BonehShoup2023], Section 20.2, p. 829, combined with Theorem 20.1, p. 824). Soundness is
`Cslib.Interactive.Verifier.Sound World.plain` against all provers, not bounded provers as in
Attack Game 20.1.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.sound_comap`: soundness transfers with the same error
  whenever true `R'`-statements come only from true `R`-statements.
* `Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction.sound`: a language reduction yields
  soundness with error `1 / |C|` from special soundness of `P'`.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Interactive
open scoped ENNReal

section Sound

variable {X Y X' Y' T C Z : Type} [Fintype C] [Nonempty C]
  {P' : SigmaProtocol X' Y' T C Z} {f : X → Y → X'} {g : Y → Y'}

/-- Soundness is inherited under condition (ii), with the same error: no condition on the witness
map, and none on `R'` beyond soundness of the verifier of `P'` for its language. -/
theorem sound_comap {W' : Type} {R' : Y' → W' → Prop} {W : Type} {R : Y → W → Prop}
    {langOut : Set Unit} {ε : ℝ≥0∞}
    (h : P'.toInteractiveVerifier.Sound World.plain (language R') langOut ε)
    (f : X → Y → X') (hg : ∀ y, (∃ w', R' (g y) w') → ∃ w, R y w) :
    (P'.comap f g).toInteractiveVerifier.Sound World.plain (language R) langOut ε :=
  Verifier.Sound.comap (g := g) h hg

/-- A language reduction gives a sound protocol from a special sound one, with error
`1 / |C|` ([BonehShoup2023], Section 20.2 with Theorem 20.1). -/
theorem LanguageReduction.sound {R : X → Y → Prop} {R' : X' → Y' → Prop}
    (h : LanguageReduction R R' f g) {extract : Y' → T → C → Z → C → Z → X'}
    (hP : P'.SpecialSoundness R' extract) (langOut : Set Unit := Set.univ) :
    (P'.comap f g).toInteractiveVerifier.Sound World.plain (language (Function.swap R)) langOut
      (1 / (Fintype.card C : ℝ≥0∞)) :=
  sound_comap (hP.sound langOut) f h.exists_of_exists_map

end Sound

end Cslib.Crypto.Protocols.SigmaProtocol
