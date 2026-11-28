/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.Open
public import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Price.Basic
import CslibFrontier.Foundations.LinearAlgebra.Tensor.Party.Network
import CslibFrontier.Foundations.Data.Nat.Card
import Mathlib.Algebra.BigOperators.Pi
import Mathlib.Tactic.FinCases

/-!
# Wire prices of an open bit network

An open network that realizes a matching of its exterior bits restricts the product of its
internal bit wires to the product of the matching wires. Consequently, in every placement of
the vertices, the total price of the matching is at most the total price of the internal edges.
This gives the deterministic wire inequality in the proof of the lemma “Uniform destinations”
in [OpenAI2026MatrixExponentNineFourths, §4.2]. Exterior sites can be placed separately by
paying the lengths of the spokes from them to their incident vertices.
-/

public section

namespace Cslib.Circuits.Frontier.OpenBitNetwork

open Finset PartyTensor

variable {K P V E : Type} {I : Type*} [Finite I] [Fintype P] [Fintype V] [Fintype E]
  [DecidableEq E]

open scoped Classical in
/-- A network realizing independent equality wires on the exterior pairs `legs` is a tensor
restriction from its internal wires to those pairs, with the vertices as parties. -/
theorem wires_le_of_contraction_eq [CommSemiring K] (N : OpenBitNetwork K I V E)
    (legs : (Σ _ : P, Fin 2) ≃ I)
    (hN : ∀ x, N.contraction x = ∏ p, if x (legs ⟨p, 0⟩) = x (legs ⟨p, 1⟩) then 1 else 0) :
    wires K (fun p => N.site (legs ⟨p, 0⟩)) (fun p => N.site (legs ⟨p, 1⟩)) (fun _ => 2) ≤
      wires K N.src N.tgt (fun _ => 2) := by
  classical
  let atEnd : (Σ _ : P, Fin 2) → V := N.site ∘ legs
  let bits (x : (Σ _ : P, Fin 2) → Fin 2) (i : I) := finTwoEquiv (x (legs.symm i))
  let unitWire (_ : P) := unit K (Fin 2) 2
  have hpush := push_le_of_edges atEnd id (outer unitWire) (fun _ : E => Bool)
    N.src N.tgt (fun v x l => N.tensor v l (bits x)) (by
      intro v x x' l l' hx hl
      rw [N.tensor_congr v l l' hl]
      apply N.exterior_congr
      intro i hi
      exact congrArg finTwoEquiv (hx _ (by simpa [atEnd] using hi))) (by
      intro x
      change (Σ _ : P, Fin 2) → Fin 2 at x
      calc
        _ = ∏ p, if bits x (legs ⟨p, 0⟩) = bits x (legs ⟨p, 1⟩) then 1 else 0 := by
          change (∏ p, (unit K (Fin 2) 2).entry (fun m => x ⟨p, m⟩)) = _
          refine Finset.prod_congr rfl fun p _ => ?_
          refine (unit_two_entry (K := K) (fun m => x ⟨p, m⟩)).trans ?_
          simp only [bits, legs.symm_apply_apply, finTwoEquiv.injective.eq_iff]
        _ = N.contraction (bits x) := (hN _).symm
        _ = _ := by simp only [TensorNetwork.contraction, Finset.sum_apply, Finset.prod_apply])
  have hEnd (p : P) : push (fun i => atEnd ⟨p, i⟩) (unitWire p) =
      wire K 2 (atEnd ⟨p, 0⟩) (atEnd ⟨p, 1⟩) := by
    rw [show (fun i : Fin 2 => atEnd ⟨p, i⟩) = ![atEnd ⟨p, 0⟩, atEnd ⟨p, 1⟩] from
      funext fun i => by fin_cases i <;> rfl]
    rfl
  change wires K (fun p => atEnd ⟨p, 0⟩) (fun p => atEnd ⟨p, 1⟩) (fun _ => 2) ≤ _
  simpa only [wires, hEnd, Fintype.card_bool, id_eq]
    using (antisymmRel_push_outer atEnd unitWire).2.trans hpush

/-- For any placement in a space with price `w`, the sum of the exterior pair prices is at most
the sum of the internal edge prices. -/
theorem sum_price_le_of_contraction_eq [Field K] (N : OpenBitNetwork K I V E)
    (legs : (Σ _ : P, Fin 2) ≃ I)
    (hN : ∀ x, N.contraction x = ∏ p, if x (legs ⟨p, 0⟩) = x (legs ⟨p, 1⟩) then 1 else 0)
    {X : Type*} {w : X → X → ℝ} (hw : IsPrice K w) (f : V → X) :
    (∑ p, w (f (N.site (legs ⟨p, 0⟩))) (f (N.site (legs ⟨p, 1⟩)))) ≤
      ∑ e, w (f (N.src e)) (f (N.tgt e)) := by
  classical
  let a (p : P) := N.site (legs ⟨p, 0⟩)
  let b (p : P) := N.site (legs ⟨p, 1⟩)
  refine prices_induction (hw.mem f)
    (S := {d | (∑ p, d (a p) (b p)) ≤ ∑ e, d (N.src e) (N.tgt e)})
    (isClosed_le (by fun_prop) (by fun_prop)) fun F c hc => ?_
  change (∑ p, c * F.wireExponent (a p) (b p)) ≤ ∑ e, c * F.wireExponent (N.src e) (N.tgt e)
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ hc
  have h := F.monotone (N.wires_le_of_contraction_eq legs hN)
  rw [F.apply_wires _ _ (fun _ => by decide), F.apply_wires _ _ (fun _ => by decide)] at h
  simp only [Nat.cast_ofNat, ← Real.rpow_sum_of_pos (by norm_num : (0 : ℝ) < 2)] at h
  exact (Real.rpow_le_rpow_left_iff (by norm_num)).1 h

/-- A matching can be measured at arbitrary exterior sites by paying once for each spoke
from an exterior bit to its incident vertex. The right-hand side is independent of the
permutation. Any subfamily of input bits can be used. -/
theorem sum_price_le_edges_add_spokes {K L V E I : Type} [Field K]
    [Fintype L] [Fintype V] [Fintype E] [DecidableEq E] [Fintype I]
    (N : OpenBitNetwork K (L ⊕ L) V E) (π : Equiv.Perm L)
    (hN : ∀ x, N.contraction x = ∏ l, if x (.inl l) = x (.inr (π l)) then 1 else 0)
    (active : I ↪ L) {X : Type*} {w : X → X → ℝ} (hw : PartyTensor.IsPrice K w)
    (inside : V → X) (terminal : L ⊕ L → X) :
    (∑ i, w (terminal (.inl (active i))) (terminal (.inr (π (active i))))) ≤
      (∑ e, w (inside (N.src e)) (inside (N.tgt e))) +
        ∑ l, w (terminal l) (inside (N.site l)) := by
  classical
  let legs : (Σ _ : L, Fin 2) ≃ L ⊕ L :=
    (Equiv.sigmaEquivProd L (Fin 2)).trans <| (Equiv.prodComm _ _).trans <|
      (Equiv.prodCongr finTwoEquiv (Equiv.refl L)).trans <|
        (Equiv.boolProdEquivSum L).trans (Equiv.sumCongr (Equiv.refl L) π)
  let demand (l : L) := w (terminal (.inl l)) (terminal (.inr (π l)))
  let across (l : L) := w (inside (N.site (.inl l))) (inside (N.site (.inr (π l))))
  let spoke (l : L ⊕ L) := w (terminal l) (inside (N.site l))
  have hwires : (∑ l, across l) ≤ ∑ e, w (inside (N.src e)) (inside (N.tgt e)) :=
    N.sum_price_le_of_contraction_eq legs hN hw inside
  have hpath (l : L) : demand l ≤ across l + (spoke (.inl l) + spoke (.inr (π l))) := by
    have h1 := hw.triangle (terminal (.inl l)) (inside (N.site (.inl l))) (terminal (.inr (π l)))
    have h2 := hw.triangle (inside (N.site (.inl l))) (inside (N.site (.inr (π l))))
      (terminal (.inr (π l)))
    rw [hw.symm (inside (N.site (.inr (π l))))] at h2
    dsimp only [demand, across, spoke]
    linarith only [h1, h2]
  calc
    _ = ∑ l ∈ univ.map active, demand l := (sum_map _ _ _).symm
    _ ≤ ∑ l, demand l := sum_le_univ_sum_of_nonneg fun _ => hw.nonneg _ _
    _ ≤ _ := sum_le_sum fun l _ => hpath l
    _ = (∑ l, across l) + ∑ l, spoke l := by
      simp only [sum_add_distrib, Fintype.sum_sum_type]
      rw [Equiv.sum_comp π (fun l => spoke (.inr l))]
    _ ≤ _ := add_le_add hwires le_rfl

end Cslib.Circuits.Frontier.OpenBitNetwork

namespace Cslib.Circuits.Frontier

/-- Attach a new leaf and one graph edge for every named terminal. -/
@[expose] def Multigraph.withTerminalSpokes {V E I : Type*} (G : Multigraph V E) (site : I → V) :
    Multigraph (V ⊕ I) (E ⊕ I) where
  src := Sum.elim (.inl ∘ G.src) .inr
  tgt := Sum.elim (.inl ∘ G.tgt) (.inl ∘ site)

/-- Adding the terminal spokes of a trivalent network gives at most three incidence darts
at each original vertex and one at each new leaf. -/
theorem OpenBitNetwork.Trivalent.withTerminalSpokes {K I V E : Type*}
    [Finite I] [Finite V] [Finite E] {N : OpenBitNetwork K I V E} (h : N.Trivalent) :
    ∀ s, Nat.card {d : (E ⊕ I) ⊕ (E ⊕ I) //
      Sum.elim (N.toMultigraph.withTerminalSpokes N.site).src
        (N.toMultigraph.withTerminalSpokes N.site).tgt d = s} ≤ 3 := by
  rintro (v | i)
  · have hv : Nat.card {e // N.src e = v} + Nat.card {e // N.tgt e = v} +
        Nat.card {i // N.site i = v} ≤ 3 := h v
    simpa only [Nat.card_subtype_sum, Sum.elim_inl, Sum.elim_inr, Multigraph.withTerminalSpokes,
      Function.comp_apply, Sum.inl.injEq, Sum.inr_ne_inl, Nat.card_of_isEmpty, add_zero, add_assoc]
      using hv
  · simp [Nat.card_subtype_sum, Multigraph.withTerminalSpokes, Nat.card_eq_fintype_card]

end Cslib.Circuits.Frontier
