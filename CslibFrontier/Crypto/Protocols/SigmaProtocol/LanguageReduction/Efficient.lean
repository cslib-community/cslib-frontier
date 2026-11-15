/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.Efficient.Verifier
public import CslibFrontier.Crypto.Protocols.SigmaProtocol.LanguageReduction
import CslibFrontier.Computability.Probabilistic.PPT.Composition

/-!
# Efficient simulation, extraction and verification under statement maps

Transfers `EfficientSpecialHVZK`, `EfficientSpecialSoundness` and `EfficientVerifier` along a
statement map `g` whose word representation `gw : I × List Bool → List Bool` is deterministic
polynomial time ([BonehShoup2023], Section 20.2, p. 829). Also provides
`EfficientSpecialSoundness.mapWitness` to post-process an efficient extractor by a polynomial-time
witness map back.

Efficiency of the derived honest prover (which applies `f`) is not formalized here, because the
library has no efficiency predicate for Sigma-protocol honest provers.

## Main definitions

* `Cslib.Crypto.Protocols.SigmaProtocol.Encoding.withStatement`: replace the statement encoding of
  an `Encoding` for a derived Sigma protocol family.

## Main results

* `Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialHVZK.comap`: transfer strict-PPT special
  HVZK simulation under condition (i) and a polynomial-time word map `gw` realizing `g`.
* `Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialSoundness.comap`: transfer polynomial-time
  special-soundness extraction for "`w` is a witness of `g y`".
* `Cslib.Crypto.Protocols.SigmaProtocol.EfficientSpecialSoundness.mapWitness`: post-process an
  efficient extractor with a polynomial-time witness map back.
* `Cslib.Crypto.Protocols.SigmaProtocol.EfficientVerifier.comap`: transfer polynomial-time
  verification along a polynomial-time word map `gw` realizing `g`.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Turing.MultiTapeTM
open scoped ENNReal

section Efficient

variable {I : Type} {X Y X' Y' T C Z W W' : I → Type}

/-- The encoding of a derived family: that of the original family, with a statement encoding for
the new statements. -/
@[expose] def Encoding.withStatement (enc' : Encoding I Y' T C Z) (encY : ∀ i, Y i ↪ List Bool) :
    Encoding I Y T C Z where
  index := enc'.index
  statement := encY
  commitment := enc'.commitment
  challenge := enc'.challenge
  response := enc'.response

variable {P' : ∀ i, SigmaProtocol (X' i) (Y' i) (T i) (C i) (Z i)}
  {enc' : Encoding I Y' T C Z} {f : ∀ i, X i → Y i → X' i} {g : ∀ i, Y i → Y' i}
  {encY : ∀ i, Y i ↪ List Bool} {gw : I × List Bool → List Bool}

/-- Efficient special HVZK is inherited under condition (i) when the statement map is polynomial
time on encodings: the derived simulator computes `g` and runs the simulator of `P'`. -/
theorem EfficientSpecialHVZK.comap {R' : ∀ i, X' i → Y' i → Prop}
    {simulate : ∀ i, Y' i → C i → PMF (T i × Z i)} {δ : I → ℝ≥0∞}
    (h : EfficientSpecialHVZK P' R' enc' simulate δ) {R : ∀ i, X i → Y i → Prop}
    (hf : ∀ i x y, R i x y → R' i (f i x y) (g i y))
    (hgw : ComputableInPolyTime gw (encPair enc'.index encBits) encBits)
    (hg : ∀ i y, gw (i, encY i y) = enc'.statement i (g i y)) :
    EfficientSpecialHVZK (fun i => (P' i).comap (f i) (g i)) R (enc'.withStatement encY)
      (fun i y c => simulate i (g i y) c) δ where
  specialHVZK i := (h.specialHVZK i).comap (hf i)
  realized := by
    obtain ⟨sim, hppt, hreal⟩ := h.realized
    obtain ⟨program, hprogram, hword⟩ := hppt.exists_word
    refine ⟨fun i y c => sim i (g i y) c, ?_, fun i y c => hreal i (g i y) c⟩
    have hprep : ComputableInPolyTime
        (fun p : I × List Bool × List Bool => (p.1, gw (p.1, p.2.1), p.2.2))
        (encSimulatorWordInput enc'.index) (encSimulatorWordInput enc'.index) := by
      fun_prop
    refine Simulator.IsPPT.of_word (enc := enc'.withStatement encY)
      (program := fun p => program (p.1, gw (p.1, p.2.1), p.2.2))
      (hprogram.preprocess hprep) fun i y c => ?_
    change _ = ProbComp.eval (program (i, gw (i, encY i y), enc'.challenge i c))
    rw [hg i y]
    exact hword i (g i y) c

/-- Efficient special soundness is inherited for the relation "`w` is a witness of `g y`" when
the statement map is polynomial time on encodings: the derived extractor computes `g` and runs the
extractor of `P'`. -/
theorem EfficientSpecialSoundness.comap {R' : ∀ i, W i → Y' i → Prop}
    {encW : ∀ i, W i ↪ List Bool} {extract : ∀ i, Y' i → T i → C i → Z i → C i → Z i → W i}
    (h : EfficientSpecialSoundness P' R' enc' encW extract) (f : ∀ i, X i → Y i → X' i)
    (hgw : ComputableInPolyTime gw (encPair enc'.index encBits) encBits)
    (hg : ∀ i y, gw (i, encY i y) = enc'.statement i (g i y)) :
    EfficientSpecialSoundness (fun i => (P' i).comap (f i) (g i)) (fun i w y => R' i w (g i y))
      (enc'.withStatement encY) encW (fun i y => extract i (g i y)) where
  specialSoundness i := (h.specialSoundness i).comap (f i) (g i)
  polyTime := by
    obtain ⟨e, he, hreal⟩ := h.polyTime
    refine ⟨fun p => e (p.1, gw (p.1, p.2.1), p.2.2), by fun_prop, fun i y t c z c' z' => ?_⟩
    change e (i, gw (i, encY i y), _) = _
    rw [hg i y]
    exact hreal i (g i y) t c z c' z'

/-- Post-process an efficient extractor by a witness map that is polynomial time on encodings. -/
theorem EfficientSpecialSoundness.mapWitness
    {P : ∀ i, SigmaProtocol (X i) (Y i) (T i) (C i) (Z i)} {enc : Encoding I Y T C Z}
    {R : ∀ i, W i → Y i → Prop} {R' : ∀ i, W' i → Y i → Prop} {encW : ∀ i, W i ↪ List Bool}
    {extract : ∀ i, Y i → T i → C i → Z i → C i → Z i → W i}
    (h : EfficientSpecialSoundness P R enc encW extract) (k : ∀ i, W i → Y i → W' i)
    (hk : ∀ i w y, R i w y → R' i (k i w y) y) (encW' : ∀ i, W' i ↪ List Bool)
    {kw : I × List Bool × List Bool → List Bool}
    (hkw : ComputableInPolyTime kw (encPair enc.index (encPair encBits encBits)) encBits)
    (hkreal : ∀ i w y, kw (i, encW i w, enc.statement i y) = encW' i (k i w y)) :
    EfficientSpecialSoundness P R' enc encW'
      (fun i y t c z c' z' => k i (extract i y t c z c' z') y) where
  specialSoundness i := (h.specialSoundness i).mapWitness (k i) (hk i)
  polyTime := by
    obtain ⟨e, he, hreal⟩ := h.polyTime
    refine ⟨fun p => kw (p.1, e p, p.2.1), by fun_prop, fun i y t c z c' z' => ?_⟩
    change kw (i, e _, enc.statement i y) = _
    rw [hreal i y t c z c' z']
    exact hkreal i _ y

/-- Efficient verification is inherited when the statement map is polynomial time on encodings:
the derived verifier computes `g` and runs the verifier of `P'`. -/
theorem EfficientVerifier.comap (h : EfficientVerifier P' enc') (f : ∀ i, X i → Y i → X' i)
    (hgw : ComputableInPolyTime gw (encPair enc'.index encBits) encBits)
    (hg : ∀ i y, gw (i, encY i y) = enc'.statement i (g i y)) :
    EfficientVerifier (fun i => (P' i).comap (f i) (g i)) (enc'.withStatement encY) := by
  obtain ⟨v, hv, hreal⟩ := h
  refine ⟨fun p => v (p.1, gw (p.1, p.2.1), p.2.2), by fun_prop, fun i y t c z => ?_⟩
  change v (i, gw (i, encY i y), _) = _
  rw [hg i y]
  exact hreal i (g i y) t c z

end Efficient

end Cslib.Crypto.Protocols.SigmaProtocol
