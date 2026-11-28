/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
public import CslibFrontier.Probability.MarkovChain.PortObstruction
import CslibFrontier.Computability.Circuit.Arithmetic.Separation.Curvature.Curvature

/-!
# Testing field ports on binary wires

A multiplicative upper functional assigns a real exponent to each binary wire between two parties.
The ports inequality bounds the mean squared exponent between two uniform vertices by a
constant times its mean on the edges, for every placement of vertices at parties.

Here `SpectralPoint` means a multiplicative upper functional. The normalized additive points
in [OpenAI2026EuclideanSpectrum, §§2.1 and 11.1] satisfy its covering inequality: a sum of
local restrictions is a restriction of their direct sum. Thus graphs passing the local test
also pass the paper's test. For the local class, the finite tests are equivalent to tests in
complete CAT(0) price spaces. Squared-distance inequalities are closed under limits and
positive rescaling, and every finite price is the pullback of the metric of such a space by
[AnthropicVPVNP2026, Proposition C.3].
-/

public section

namespace Cslib

open Finset
open scoped BigOperators

universe u

namespace PartyTensor

/-- A complete CAT(0) metric space whose distances form a tensor price over `K`. -/
structure HadamardPriceSpace (K : Type) [Field K] where
  /-- The underlying points of the space. -/
  Carrier : Type u
  /-- The metric of the price space. -/
  [metric : MetricSpace Carrier]
  /-- The space is complete and its midpoints satisfy the CAT(0) inequality. -/
  [cat0 : CompleteCAT0Space Carrier]
  /-- Every finite distance table of the metric is a price over the field. -/
  isPrice : IsPrice K (dist : Carrier → Carrier → ℝ)

attribute [instance] HadamardPriceSpace.metric HadamardPriceSpace.cat0

end PartyTensor

namespace RotationMap

variable {V D : Type} [Fintype V] [Fintype D] (G : RotationMap V D) (K : Type) [Field K]

/-- At every finite spectral point, the mean squared binary-wire exponent of a pair of
independent vertices is at most `b` times that of a random edge. Vertex placements may
identify parties. -/
@[expose] def HasWirePoincareBound (b : ℝ) : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (F : PartyTensor.SpectralPoint K I) (f : V → I),
    (𝔼 i, 𝔼 j, F.wireExponent (f i) (f j) ^ 2) ≤
      b * 𝔼 p : V × D, F.wireExponent (f p.1) (f (G.rot p).1) ^ 2

/-- Passing from wire exponents to finite price tables preserves a squared Poincaré bound.
This applies to placements in price metrics of any cardinality and universe. -/
theorem HasWirePoincareBound.hasPoincareBound {b : ℝ} (h : G.HasWirePoincareBound K b)
    {X : Type*} [PseudoMetricSpace X] (hX : PartyTensor.IsPrice K (dist : X → X → ℝ)) :
    G.HasPoincareBound X b := by
  classical
  intro f
  let S : Set (V → V → ℝ) := {d |
    (𝔼 i, 𝔼 j, d i j ^ 2) ≤ b * 𝔼 p : V × D, d p.1 (G.rot p).1 ^ 2}
  have closed : IsClosed S := by
    apply isClosed_le
    all_goals simp only [Fintype.expect_eq_sum_div_card]; fun_prop
  apply PartyTensor.prices_induction (hX.mem f) (S := S) closed
  intro F c _
  change (𝔼 i, 𝔼 j, (c * F.wireExponent i j) ^ 2) ≤
    b * 𝔼 p : V × D, (c * F.wireExponent p.1 (G.rot p).1) ^ 2
  simp only [mul_pow, ← Finset.mul_expect]
  rw [mul_left_comm b]
  exact mul_le_mul_of_nonneg_left (h V F id) (sq_nonneg _)

private def liftPriceSpace {X : Type} [MetricSpace X] [CompleteCAT0Space X]
    (hX : PartyTensor.IsPrice K (dist : X → X → ℝ)) :
    PartyTensor.HadamardPriceSpace.{u} K where
  Carrier := ULift.{u} X
  metric := inferInstance
  cat0 :=
    { exists_mid := fun x y => by
        obtain ⟨m, hm⟩ := CompleteCAT0Space.exists_mid x.down y.down
        exact ⟨ULift.up m, fun z => hm z.down⟩ }
  isPrice := hX.comp ULift.down

/-- A regular graph passes the finite spectral-point test exactly when it has the same
squared-distance bound in every complete CAT(0) price space over the field. -/
theorem hasWirePoincareBound_iff {b : ℝ} :
    G.HasWirePoincareBound K b ↔
      ∀ X : PartyTensor.HadamardPriceSpace.{u} K, G.HasPoincareBound X.Carrier b := by
  constructor
  · exact fun h X => h.hasPoincareBound _ _ X.isPrice
  · intro h I _ _ F f
    obtain ⟨X, mX, cX, g, hX, hg⟩ :=
      Circuits.Arithmetic.Separation.Curvature.exists_completeCAT0Space_of_isPrice
        (PartyTensor.isPrice_wireExponent F)
    have hw := h (liftPriceSpace.{u} K hX) (fun v => ULift.up (g (f v)))
    change (𝔼 i, 𝔼 j, dist (g (f i)) (g (f j)) ^ 2) ≤
      b * 𝔼 p : V × D, dist (g (f p.1)) (g (f (G.rot p).1)) ^ 2 at hw
    simpa only [hg] using hw

end RotationMap

namespace PartyTensor

/-- Field ports tested on the library's multiplicative upper functionals. Regular undirected
multigraphs of unbounded order have a common degree and a common squared Poincaré bound
on all finite binary-wire exponents over `K`. This implies the port condition of
[OpenAI2026EuclideanSpectrum, Definition 11.1], whose finite tests use additive points. -/
@[expose] def HasPorts (K : Type) [Field K] : Prop :=
  ∃ (D : Type) (_ : Fintype D) (_ : Nonempty D) (b : ℝ), 0 ≤ b ∧
    ∀ n : ℕ, ∃ (V : Type) (_ : Fintype V) (_ : Nonempty V) (G : RotationMap V D),
      n ≤ Fintype.card V ∧ G.HasWirePoincareBound K b

/-- The same port graphs and constants work for finite spectral points and the family of
complete CAT(0) price spaces over the field. -/
theorem hasPorts_iff_metricPorts (K : Type) [Field K] :
    HasPorts K ↔ RotationMap.HasPorts (fun X : HadamardPriceSpace.{u} K => X.Carrier) := by
  constructor <;> rintro ⟨D, dD, nD, b, hb, h⟩ <;> refine ⟨D, dD, nD, b, hb, fun n => ?_⟩
  · obtain ⟨V, fV, nV, G, hv, hG⟩ := h n
    exact ⟨V, fV, nV, G, hv, (G.hasWirePoincareBound_iff K).1 hG⟩
  · obtain ⟨V, fV, nV, G, hv, hG⟩ := h n
    exact ⟨V, fV, nV, G, hv, (G.hasWirePoincareBound_iff K).2 hG⟩

end PartyTensor
end Cslib
