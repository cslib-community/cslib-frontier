/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Basic

/-!
# Language reductions and derived Sigma protocols

Pullback of a Sigma protocol `P'` for `R'` along a witness map `f : X → Y → X'` and a statement
map `g : Y → Y'` ([BonehShoup2023], Section 20.2, p. 829). The derived protocol `P'.comap f g`
runs `P'` on `(f x y, g y)` for the prover and on `g y` for the verifier, keeping commitments,
challenges and responses unchanged.

A `LanguageReduction R R' f g` requires:
(i) `(f x y, g y)` is in `R'` whenever `(x, y)` is in `R` (`map_rel`);
(ii) `y` has some witness in `R` whenever `g y` has one in `R'` (`exists_of_exists_map`).

`Complete.comap` and `SpecialHVZK.comap` depend only on condition (i). `SpecialSoundness.comap`
transfers special soundness to the relation "`w` is a witness of `g y`" without hypotheses on the
maps; `SpecialSoundness.mapWitness` maps the extracted witness back to `R` when a witness map
`k : W → Y → W'` is given.

Unlike `Cslib.Complexity.LevinReduction`
(`CslibFrontier/Computability/Complexity/Reduction/Levin.lean`) and `ZKProof.withRelationWitness`
(`CslibFrontier/Crypto/Computational/ZeroKnowledge/Levin.lean`), which act on encoded NP relations
and include a polynomial-time backward witness map, `LanguageReduction` works on typed relations
without encodings or decision procedures and does not require recovering witnesses of `y` from
witnesses of `g y`.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction`: predicate bundling conditions (i) and
  (ii) of a language reduction.
* `Cslib.Crypto.Protocols.SigmaProtocol.comap`: derived Sigma protocol along `f` and `g`.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.Complete.comap`: completeness under condition (i).
* `Cslib.Crypto.Protocols.SigmaProtocol.SpecialHVZK.comap`: special HVZK under condition (i).
* `Cslib.Crypto.Protocols.SigmaProtocol.SpecialSoundness.comap`: special soundness for the mapped
  statement `g y`.
* `Cslib.Crypto.Protocols.SigmaProtocol.SpecialSoundness.mapWitness`: post-processing an extractor
  with a witness map back.
* `Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction.complete`: completeness from a language
  reduction.
* `Cslib.Crypto.Protocols.SigmaProtocol.LanguageReduction.specialHVZK`: special HVZK from a
  language reduction.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

universe u

section LanguageReduction

variable {X : Type*} {Y : Type*} {X' : Type*} {Y' : Type*}

/-- A **language reduction** from `R` to `R'` ([BonehShoup2023], Section 20.2): a curried
witness map `f : X → Y → X'` (taking `x` and `y` separately rather than as a pair `(x, y)`) and a
statement map `g : Y → Y'` such that (i) `f` sends a witness of `y` to a witness of `g y`, and
(ii) `g y` is a true statement of `R'` only if `y` is a true statement of `R`. Unlike the book's
maps, the predicate does not ask for `f` or `g` to be efficiently computable; word representations
appear as hypotheses on the transfers in
`CslibFrontier/Crypto/Protocols/SigmaProtocol/LanguageReduction/Efficient.lean`. -/
structure LanguageReduction (R : X → Y → Prop) (R' : X' → Y' → Prop) (f : X → Y → X')
    (g : Y → Y') : Prop where
  /-- Condition (i). -/
  map_rel : ∀ x y, R x y → R' (f x y) (g y)
  /-- Condition (ii). -/
  exists_of_exists_map : ∀ y, (∃ x', R' x' (g y)) → ∃ x, R x y

namespace LanguageReduction

variable {R : X → Y → Prop} {R' : X' → Y' → Prop} {f : X → Y → X'} {g : Y → Y'}

/-- A witness map back gives condition (ii). -/
theorem of_witnessMap (hf : ∀ x y, R x y → R' (f x y) (g y)) (k : X' → Y → X)
    (hk : ∀ x' y, R' x' (g y) → R (k x' y) y) : LanguageReduction R R' f g :=
  ⟨hf, fun y ⟨x', hx'⟩ => ⟨k x' y, hk x' y hx'⟩⟩

end LanguageReduction

end LanguageReduction

section Comap

variable {X Y X' Y' T C Z : Type u}

/-- The protocol for statements `Y` and witnesses `X` obtained from a protocol `P'` for statements
`Y'` and witnesses `X'` along a witness map `f` and a statement map `g`
([BonehShoup2023], Section 20.2): the prover on `(x, y)` is the prover of `P'` on
`(f x y, g y)`, and the verifier on `y` is the verifier of `P'` on `g y`. Commitments, challenges
and responses are unchanged. -/
@[expose] def comap (P' : SigmaProtocol X' Y' T C Z) (f : X → Y → X') (g : Y → Y') :
    SigmaProtocol X Y T C Z where
  State := P'.State
  commit x y := P'.commit (f x y) (g y)
  respond x y := P'.respond (f x y) (g y)
  verify y := P'.verify (g y)

@[simp] theorem comap_transcript (P' : SigmaProtocol X' Y' T C Z) (f : X → Y → X') (g : Y → Y')
    (x : X) (y : Y) (c : C) :
    (P'.comap f g).transcript x y c = P'.transcript (f x y) (g y) c := rfl

variable {P' : SigmaProtocol X' Y' T C Z} {f : X → Y → X'} {g : Y → Y'}
  {R : X → Y → Prop} {R' : X' → Y' → Prop}

/-- Completeness is inherited under condition (i). -/
theorem Complete.comap (h : P'.Complete R') (hf : ∀ x y, R x y → R' (f x y) (g y)) :
    (P'.comap f g).Complete R :=
  fun x y hxy c tz htz => h (f x y) (g y) (hf x y hxy) c tz htz

/-- Special HVZK is inherited under condition (i), with the simulator of `P'` run on `g y`. -/
theorem SpecialHVZK.comap {simulate : Y' → C → PMF (T × Z)} (h : P'.SpecialHVZK R' simulate)
    (hf : ∀ x y, R x y → R' (f x y) (g y)) :
    (P'.comap f g).SpecialHVZK R fun y => simulate (g y) where
  accepts y c tz htz := h.accepts (g y) c tz htz
  transcript_eq x y hxy c := h.transcript_eq (f x y) (g y) (hf x y hxy) c

/-- Special soundness is inherited for the relation "`w` is a witness of `g y`", with the
extractor of `P'` run on `g y`. No condition on the maps is needed, and the extracted witness is
one of `R'`, not of `R`. -/
theorem SpecialSoundness.comap {W : Type*} {R' : W → Y' → Prop}
    {extract : Y' → T → C → Z → C → Z → W} (h : P'.SpecialSoundness R' extract)
    (f : X → Y → X') (g : Y → Y') :
    (P'.comap f g).SpecialSoundness (fun w y => R' w (g y)) fun y => extract (g y) :=
  fun y t c z c' z' hc hz hz' => h (g y) t c z c' z' hc hz hz'

/-- Post-process the extracted witness by a map that preserves the relation at every statement. -/
theorem SpecialSoundness.mapWitness {P : SigmaProtocol X Y T C Z} {W : Type*} {W' : Type*}
    {R : W → Y → Prop} {R' : W' → Y → Prop} {extract : Y → T → C → Z → C → Z → W}
    (h : P.SpecialSoundness R extract) (k : W → Y → W') (hk : ∀ w y, R w y → R' (k w y) y) :
    P.SpecialSoundness R' fun y t c z c' z' => k (extract y t c z c' z') y :=
  fun y t c z c' z' hc hz hz' => hk _ y (h y t c z c' z' hc hz hz')

/-- A language reduction gives a complete protocol (this is `Complete.comap` at `h.map_rel`, which
needs condition (i) only). -/
theorem LanguageReduction.complete (h : LanguageReduction R R' f g) (hP : P'.Complete R') :
    (P'.comap f g).Complete R :=
  hP.comap h.map_rel

/-- A language reduction gives a special HVZK protocol (this is `SpecialHVZK.comap` at `h.map_rel`,
which needs condition (i) only). -/
theorem LanguageReduction.specialHVZK (h : LanguageReduction R R' f g)
    {simulate : Y' → C → PMF (T × Z)} (hP : P'.SpecialHVZK R' simulate) :
    (P'.comap f g).SpecialHVZK R fun y => simulate (g y) :=
  hP.comap h.map_rel

end Comap

end Cslib.Crypto.Protocols.SigmaProtocol
