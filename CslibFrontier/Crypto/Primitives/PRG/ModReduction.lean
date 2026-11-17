/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Cslib.Crypto.Primitives.PRG.Defs
public import Mathlib.Data.ZMod.Defs
import CslibFrontier.Probability.StatisticalDistance.Event
import CslibFrontier.Probability.StatisticalDistance.UniformMod

/-!
# Modular reduction of finite pseudorandom generators

Reduction of a finite-type `PRG.Generator Seed (Fin N)` modulo `m`, giving `Generator.modNat`, and
the concrete advantage inequality of Boneh–Shoup Example 3.3 (`Generator.advantage_modNat_le`) for
every adversary. Example 3.3 itself, that the residues are computationally indistinguishable from
uniform when the generator is secure and `m / N` is negligible, is
`Cslib.Crypto.ComputationallyIndistinguishable.map_modWord` and
`Cslib.Crypto.PseudorandomGenerator.indistinguishable_map_modWord`, whose reduction is certified
PPT (`Cslib.Crypto.isPPT_modDistinguisher`).

## Main definitions

* `Cslib.Crypto.PRG.Generator.modNat`: compose a `Fin N`-valued generator with reduction modulo `m`.

## Main results

* `Cslib.Crypto.PRG.Generator.advantage_modNat_le`:
  `Distadv[A, P₀, P₁] ≤ PRGadv[B, G] + m / N`.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*,
  Version 0.6][BonehShoup2023], Section 3.11 (Example 3.3, pp. 86–87).
-/

public section

namespace Cslib.Crypto.PRG.Generator

open Cslib.Probability

variable {Seed : Type*}

/-- The generator `G`, whose outputs are numbers below `N`, followed by reduction modulo `m`
([BonehShoup2023], Example 3.3, p. 86). -/
@[expose] def modNat {N : ℕ} (G : Generator Seed (Fin N)) (m : ℕ) : Generator Seed (ZMod m) :=
  ⟨fun seed => ((G seed).val : ZMod m)⟩

@[simp] theorem modNat_apply {N : ℕ} (G : Generator Seed (Fin N)) (m : ℕ) (seed : Seed) :
    G.modNat m seed = ((G seed).val : ZMod m) := rfl

variable [Fintype Seed] [Nonempty Seed]

/-- **Example 3.3 for a generator on finite types** ([BonehShoup2023], p. 87):
`Distadv[A, P₀, P₁] ≤ PRGadv[B, G] + m / N`, where `P₀` is the output of `G` reduced modulo `m`,
`P₁` is uniform on `ZMod m`, and `B` reduces its challenge modulo `m` and runs `A`. Nothing is
assumed about `G` or `A`, and `N` need not be a power of two. -/
theorem advantage_modNat_le {N : ℕ} [NeZero N] (G : Generator Seed (Fin N)) (m : ℕ) [NeZero m]
    (adversary : Adversary (ZMod m)) :
    (G.modNat m).advantage adversary ≤
      G.advantage (fun y => adversary (y.val : ZMod m)) + m / N := by
  have hreal : (G.modNat m).realExperiment adversary =
      G.realExperiment fun y => adversary (y.val : ZMod m) := by
    simp only [realExperiment, outputDist]
    rw [show (PMF.uniformOfFintype Seed).map (G.modNat m) =
      ((PMF.uniformOfFintype Seed).map G).map fun y : Fin N => (y.val : ZMod m) from by
        rw [PMF.map_comp]; rfl, PMF.bind_map]
    rfl
  have hmid := PMF.abs_bind_apply_toReal_sub_le_dist
    ((PMF.uniformOfFintype (Fin N)).map fun x => (x.val : ZMod m))
    (PMF.uniformOfFintype (ZMod m)) adversary true
  rw [PMF.bind_map] at hmid
  unfold advantage
  rw [hreal]
  refine (abs_sub_le _ ((idealExperiment fun y : Fin N => adversary (y.val : ZMod m)) true).toReal
    _).trans (add_le_add le_rfl ?_)
  exact hmid.trans (PMF.dist_map_natCast_uniformOfFintype_le_div N m)

end Cslib.Crypto.PRG.Generator
