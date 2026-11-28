/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.TensorNetwork.WirePrice
public import CslibFrontier.Foundations.Combinatorics.Expander.MetricPoincare
import CslibFrontier.Foundations.Combinatorics.Expander.RegularQuotient
import CslibFrontier.Foundations.Data.Finset.Expect

/-!
# Routing shifts on a rectangle

Different choices of local tables on one trivalent bit network route row and column shifts on
selected input lanes. Add the terminals to the graph as leaves and distribute its interior
vertices among the sites. Averaging the wire inequality over each family of shifts bounds the
mean squared distance of two uniform sites by the mean squared edge length of a regular graph
on the rectangle, in every space whose metric is a price. This supplies the geometric input
to the logarithmic graph obstruction in the approach to element distinctness in issue #8448.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Circuits.Frontier.OpenBitNetwork

universe u

variable {K V E L S T : Type} [Fintype V] [Fintype E] [DecidableEq E] [Fintype L] [Fintype S]

/-- Different choices of local tables on one graph route matchings on a common set of
terminals. On a named selection of lanes the matchings realize the prescribed shifts. -/
structure ShiftRoutings [CommSemiring K] (N : OpenBitNetwork K (L ⊕ L) V E)
    (terminal : L ⊕ L → S) (h : ℕ) (shift : T → S → S) where
  /-- Input labels of the selected lanes. -/
  active : (S × Fin h) ↪ L
  /-- Permutation realized on all input labels for each shift. -/
  perm : T → Equiv.Perm L
  /-- Local tables for the chosen permutation. -/
  tables : T → OpenBitNetwork K (L ⊕ L) V E
  /-- All choices use the same internal wires. -/
  graph_eq : ∀ t, (tables t).toMultigraph = N.toMultigraph
  /-- All choices use the same physical attachment for each input and output. -/
  sites_eq : ∀ t, (tables t).site = N.site
  /-- The exterior tensor checks equality along the whole matching. -/
  contraction_eq : ∀ t x, (tables t).contraction x =
    ∏ l, if x (.inl l) = x (.inr (perm t l)) then 1 else 0
  /-- Every selected input starts at its own site. -/
  input_site : ∀ p, terminal (.inl (active p)) = p.1
  /-- The selected outputs end at the sites prescribed by the shift. -/
  output_site : ∀ t p, terminal (.inr (perm t (active p))) = shift t p.1

private theorem ShiftRoutings.expect_le [Field K] [Nonempty S]
    {N : OpenBitNetwork K (L ⊕ L) V E} (place : V ⊕ (L ⊕ L) → S)
    {h : ℕ} [NeZero h] {shift : T → S → S}
    (cert : N.ShiftRoutings (fun l => place (.inr l)) h shift) (t : T)
    {D : Type*} [Fintype D] (R : RotationMap S D)
    (hR : ∀ w : S → S → ℝ, (∀ s s', 0 ≤ w s s') →
      (∑ e, w (place ((N.toMultigraph.withTerminalSpokes N.site).src e))
        (place ((N.toMultigraph.withTerminalSpokes N.site).tgt e))) ≤
        ∑ p : S × D, w p.1 (R.rot p).1)
    {X : Type*} [PseudoMetricSpace X] (hX : PartyTensor.IsPrice K (dist : X → X → ℝ))
    (f : S → X) :
    (𝔼 s, dist (f s) (f (shift t s))) ≤
      (Fintype.card D : ℝ) / h * 𝔼 p : S × D, dist (f p.1) (f (R.rot p).1) := by
  let G := N.toMultigraph.withTerminalSpokes N.site
  have hp := (cert.tables t).sum_price_le_edges_add_spokes (cert.perm t) (cert.contraction_eq t)
    cert.active hX (fun v => f (place (.inl v))) (fun l => f (place (.inr l)))
  have hs : (h : ℝ) * (∑ s, dist (f s) (f (shift t s))) ≤
      ∑ e, dist (f (place (G.src e))) (f (place (G.tgt e))) := by
    simpa only [cert.input_site, cert.output_site, cert.sites_eq,
      congrArg Multigraph.src (cert.graph_eq t), congrArg Multigraph.tgt (cert.graph_eq t),
      Fintype.sum_prod_type, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_sum,
      G, Multigraph.withTerminalSpokes, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Function.comp_apply] using hp
  have bound := hs.trans (hR (fun s s' => dist (f s) (f s')) fun _ _ => dist_nonneg)
  rw [← Fintype.card_mul_expect, ← Fintype.card_mul_expect, Fintype.card_prod, Nat.cast_mul]
    at bound
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast NeZero.pos h)]
  apply (mul_le_mul_iff_right₀ (by exact_mod_cast Fintype.card_pos : 0 < (Fintype.card S : ℝ))).mp
  nlinarith only [bound]

private theorem expect_translate_le {S T : Type*} [Fintype S] [Fintype T] [AddGroup T]
    (origin : S → T) (g : S → T → ℝ) {C : ℝ}
    (h : ∀ δ : T, (𝔼 s, g s (origin s + δ)) ≤ C) : (𝔼 s, 𝔼 t, g s t) ≤ C := by
  calc
    _ = 𝔼 s, 𝔼 δ, g s (origin s + δ) :=
      expect_congr rfl fun s _ => (Fintype.expect_add_left _ _).symm
    _ = 𝔼 δ, 𝔼 s, g s (origin s + δ) := expect_comm _ _ _
    _ ≤ 𝔼 _ : T, C := expect_le_expect fun δ _ => h δ
    _ = C := Fintype.expect_const _

/-- A trivalent network that routes all row and column shifts on selected lanes gives a
regular graph on the rectangle. Its squared-distance inequality holds in every spectral
target. Only exterior terminals have prescribed sites. The interior vertices fit in at
most `|V| / |A × B| + 1` additional slots per site. -/
theorem exists_regular_of_terminal_shifts [Field K] {A B : Type} [Fintype A] [Fintype B]
    [AddGroup A] [AddGroup B] (N : OpenBitNetwork K (L ⊕ L) V E) (hN : N.Trivalent)
    (terminal : L ⊕ L → A × B) (h k : ℕ) [NeZero h]
    (hload : ∀ s, Nat.card {l // terminal l = s} ≤ k)
    (rows : N.ShiftRoutings terminal h fun δ : B => fun s => (s.1, s.2 + δ))
    (cols : N.ShiftRoutings terminal h fun δ : A => fun s => (s.1 + δ, s.2)) :
    let q := Fintype.card V / Fintype.card (A × B) + 1 + k
    ∃ R : RotationMap (A × B) (Fin q × Fin 3), ∀ (X : Type u) [PseudoMetricSpace X],
      PartyTensor.IsPrice K (dist : X → X → ℝ) → ∀ f : A × B → X,
      (𝔼 s, 𝔼 t, dist (f s) (f t) ^ 2) ≤
        12 * (2 * ((q : ℝ) * 3 / h)) ^ 2 *
          𝔼 p : (A × B) × (Fin q × Fin 3), dist (f p.1) (f (R.rot p).1) ^ 2 := by
  let q := Fintype.card V / Fintype.card (A × B) + 1 + k
  let : NeZero q := ⟨by dsimp [q]; lia⟩
  obtain ⟨place, hfixed, hsite⟩ := exists_balanced_sum_placement (V := V) terminal hload
  have hsites : (fun l => place (.inr l)) = terminal := funext hfixed
  rw [← hsites] at rows cols
  let G := N.toMultigraph.withTerminalSpokes N.site
  obtain ⟨R, hR⟩ := RotationMap.exists_regular_of_fiber_bounds G.src G.tgt place
    hN.withTerminalSpokes hsite
  refine ⟨R, fun X inst hX f => ?_⟩
  apply R.expect_dist_sq_le_of_forall_expect_dist_le (by positivity) _ f
  intro g
  let C := (Fintype.card (Fin q × Fin 3) : ℝ) / h *
    𝔼 p : (A × B) × (Fin q × Fin 3), dist (g p.1) (g (R.rot p).1)
  have hr : (𝔼 s : A × B, 𝔼 v : B, dist (g s) (g (s.1, v))) ≤ C :=
    expect_translate_le Prod.snd _ fun δ => rows.expect_le place δ R hR hX g
  have hc : (𝔼 s : A × B, 𝔼 u : A, dist (g s) (g (u, s.2))) ≤ C :=
    expect_translate_le Prod.fst _ fun δ => cols.expect_le place δ R hR hX g
  rw [Fintype.expect_prod_type] at hr hc
  rw [expect_comm (ι := A) (κ := B) univ univ] at hc
  have both := (expect_dist_le_row_add_column fun a b => g (a, b)).trans (add_le_add hr hc)
  simpa only [C, q, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat,
    ← two_mul, mul_assoc] using both

end Cslib.Circuits.Frontier.OpenBitNetwork
