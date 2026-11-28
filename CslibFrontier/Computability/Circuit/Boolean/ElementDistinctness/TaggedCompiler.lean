/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.ElementDistinctness.RoutingNetwork
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Normalize
public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.BatchSubstitution
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# An exact compiler whose only large gates test a tagged permutation

For a fixed field and address width `h`, a compiled network consists of ordinary trivalent
vertices and calls to one table. All `3 * 2 ^ h * h` incidences belong to the call even when a
wire connects two calls or has both ends at one call. [OpenAI2026EuclideanSpectrum,
Proposition 14.1] constructs these networks for powers of normalized inputs over a finite
field with ports. The budget here specializes its parameter `J` to four and its size budget
to the actual normalized volume. The construction of the compiler is an open part of #8448.
-/

public section

namespace Cslib.Circuits.Boolean.ElementDistinctness

open Frontier Filter

open scoped Classical in
/-- Every ordinary site has at most three incidences. At a call site the named incidences
are exactly the tag bits and the two payloads, and the local table checks that delivery. -/
@[expose] def UsesTaggedCalls {K I O C E : Type} [Zero K] [One K] [Finite I] [Finite O] [Finite C]
    [Finite E] (N : OpenBitNetwork K I (O ⊕ C) E) (h : ℕ) : Prop :=
  ∃ ports : ∀ c, N.Port (.inr c) ≃ RoutingBit h,
    (∀ o, Nat.card (N.Port (.inl o)) ≤ 3) ∧
    ∀ c (α : E → Bool) (x : I → Bool),
      (if TaggedPermutation
        (fun j => Sum.elim (Sum.elim α α) x ((ports c).symm j).val) then 1 else 0) =
          N.tensor (.inr c) α x

/-- The tagged-permutation compiler specification of [OpenAI2026EuclideanSpectrum,
Proposition 14.1], restricted to input volumes between `n` and `n ^ 4`, where `n = 2 ^ h`.
It must produce actual networks, including their call tables and the cost of their wires.
Its replication and size bounds are uniform over the input network. -/
@[expose] def HasExactTaggedCompiler (K : Type) [CommRing K] (a κ : ℝ) (C : ℕ) : Prop :=
  ∀ᶠ h : ℕ in atTop, let n := 2 ^ h
    let L := Nat.log 2 h + 1
    ∀ (I V E : Type) [Fintype I] [DecidableEq I] [Fintype V] [Fintype E] [DecidableEq E]
      (P : OpenBitNetwork K I V E), P.IsNormalized → n ≤ P.volume → P.volume ≤ n ^ 4 →
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ 2 ^ (C * L ^ 2) ∧
        ∃ (O B F : Type) (_ : Fintype O) (_ : Fintype B) (_ : Fintype F) (_ : DecidableEq F)
          (H : OpenBitNetwork K (Fin d × I) (O ⊕ B) F), UsesTaggedCalls H h ∧
          (∀ z, H.contraction z = ∏ j : Fin d, P.contraction (fun i => z (j, i))) ∧
            (H.volume : ℝ) ≤ κ * d * ((P.volume : ℝ) / (h : ℝ) ^ a + Fintype.card I * (L ^ C : ℕ))

open scoped Classical in
/-- The exact charged descent after a joint batch of tagged verifiers has been substituted.
The normalized input is any finite network with named exterior bits. The output computes
the product of `d` copies of its contraction. The unamortized charge pays for the final
group of tests, of total width `t * 3 * 2 ^ h * h`. -/
@[expose] def HasChargedTaggedCompiler (R : Type) [CommRing R] (a K : ℝ) (C : ℕ) : Prop :=
  ∀ᶠ h : ℕ in atTop, let n := 2 ^ h; let L := Nat.log 2 h + 1
    ∀ t : ℕ, 0 < t → t ≤ 2 * n →
      ∀ (I V E : Type) [Fintype I] [DecidableEq I] [Fintype V] [Fintype E] [DecidableEq E]
        (P : OpenBitNetwork R I V E), P.IsNormalized →
        n ≤ P.volume → P.volume ≤ n ^ 4 →
      ∀ (W F : Type) [Fintype W] [Fintype F] [DecidableEq F]
        (M : OpenBitNetwork R (Fin t × RoutingBit h) W F), M.Trivalent →
        (∀ z, M.contraction z = ∏ i : Fin t,
          if TaggedPermutation (fun q => z (i, q)) then 1 else 0) →
      ∃ d : ℕ, 1 ≤ d ∧ d ≤ 2 ^ (C * L ^ 2) ∧
        ∃ (V' E' : Type) (_ : Fintype V') (_ : Fintype E') (_ : DecidableEq E')
          (Q : OpenBitNetwork R (Fin d × I) V' E'), Q.Trivalent ∧
          (∀ z, Q.contraction z = ∏ r : Fin d, P.contraction (fun i => z (r, i))) ∧
          (Q.volume : ℝ) ≤ K * M.volume / (t * (3 * n * h) : ℕ) *
            (d * (P.volume / (h : ℝ) ^ a + (Fintype.card I : ℝ) * (L ^ C : ℕ)) +
              (t * (3 * n * h) : ℕ))

private def identityDelivery (h : ℕ) : RoutingBit h → Bool
  | .tag i b => (BitString.equivFin h).symm i b
  | .input _ _ | .output _ _ => false

private theorem taggedPermutation_identityDelivery (h : ℕ) :
    TaggedPermutation (identityDelivery h) := by
  constructor
  · simp only [identityDelivery, Equiv.apply_symm_apply]
    exact ⟨fun _ _ h => h, fun i => ⟨i, rfl⟩⟩
  · exact fun _ _ => rfl

/-- Compiling with tagged calls and then filling them in batches gives a trivalent compiler.
Its last group can be incomplete. Wires joining calls, including calls in that group, count
once in the resulting network. -/
theorem HasExactTaggedCompiler.charged {K : Type} [CommRing K] {a κ : ℝ} {C : ℕ}
    (hc : HasExactTaggedCompiler K a κ C) (hκ : 0 ≤ κ) :
    HasChargedTaggedCompiler K a (3 * κ + 1) C := by
  classical
  filter_upwards [hc, eventually_ge_atTop 1] with h compile hh
  dsimp only at compile ⊢
  intro t ht _ I V E _ _ _ _ _ P hP hlo hhi W F _ _ _ M hM htag
  obtain ⟨d, hd, hd', O, B, A, iO, iB, iA, dA, H, ⟨ports, ho, hcalls⟩, hcomp, hsize⟩ :=
    compile I V E P hP hlo hhi
  let : NeZero h := ⟨by lia⟩
  let : NeZero t := ⟨ht.ne'⟩
  let : Nonempty (RoutingBit h) := ⟨.tag 0 0⟩
  let table (y : RoutingBit h → Bool) : K := if TaggedPermutation y then 1 else 0
  have hone : table (identityDelivery h) = 1 := by
    simp [table, taggedPermutation_identityDelivery]
  obtain ⟨W', F', iW', iF', dF', Q, hQ, _, hv, heq⟩ :=
    OpenBitNetwork.exists_replace_call_batches_le H M ports table (identityDelivery h) hone ho hM
      htag fun c α x => (hcalls c α x).symm
  refine ⟨d, hd, hd', W', F', iW', iF', dF', Q, hQ, fun z => (heq z).trans (hcomp z), ?_⟩
  rw [Nat.card_eq_fintype_card (α := Fin t), Fintype.card_fin,
    Nat.card_eq_fintype_card (α := RoutingBit h), card_routingBit] at hv
  let k := t * (3 * 2 ^ h * h)
  let p := (M.volume : ℝ) / k
  let z := (d : ℝ) * (P.volume / (h : ℝ) ^ a + Fintype.card I * ((Nat.log 2 h + 1) ^ C : ℕ))
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hs : (H.volume : ℝ) ≤ κ * z := by simpa only [z, ← mul_assoc] using hsize
  change (Q.volume : ℝ) ≤ p * (3 * H.volume + k) at hv
  change (Q.volume : ℝ) ≤ (3 * κ + 1) * M.volume / k * (z + k)
  rw [mul_div_assoc, show (3 * κ + 1) * p * (z + k) = p * ((3 * κ + 1) * (z + k)) by ring]
  refine hv.trans (mul_le_mul_of_nonneg_left ?_ hp)
  nlinarith only [hs, hz, mul_nonneg hκ (Nat.cast_nonneg k : 0 ≤ (k : ℝ))]

end Cslib.Circuits.Boolean.ElementDistinctness
