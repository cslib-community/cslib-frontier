/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Anchoring

/-!
# Noisy dependency breaking for anchored questions

This is the single-coordinate sampler of
[Bavarian, Vidick and Yuen, §4.1][BavarianVidickYuen2022], arXiv:1509.07466v2.
The message sent by the designated player is a question with a lower anchor probability.
Given that message, an additional erase step completes its anchoring, independently of the
other player's question.

The joint law of the two resulting questions, with the message forgotten, is the anchored
question law for either designated player.
-/

public section

open scoped unitInterval ENNReal

namespace Cslib.PCP.AnchoredDependency

open Cslib.Probability.PMF

variable {X Y : Type*}

/-- The additional erasure rate is half the final anchor probability. -/
noncomputable def noise (α : I) : I :=
  ⟨(α : ℝ) / 2, by constructor <;> linarith [α.2.1, α.2.2]⟩

/-- The reveal's anchor probability is `(α - η) / (1 - η)` for `η = α / 2`. -/
noncomputable def messageRate (α : I) : I :=
  ⟨(α : ℝ) / (2 - α), by
    have hd : 0 < 2 - (α : ℝ) := by linarith [α.2.2]
    exact ⟨div_nonneg α.2.1 hd.le, (div_le_one hd).mpr (by linarith [α.2.2])⟩⟩

private theorem coin_messageRate_or_noise (α : I) :
    (coin (messageRate α)).bind (fun i => (coin (noise α)).map fun k => i || k) = coin α := by
  have h := α.2.2
  have hd : (2 : ℝ) - α ≠ 0 := by linarith
  ext b
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  have hfalse : (coin (noise α)).map (fun k => false || k) = coin (noise α) := by
    exact PMF.map_id _
  have htrue : (coin (noise α)).map (fun k => true || k) = PMF.pure true :=
    PMF.map_const _ _
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_bool, hfalse, htrue,
    ENNReal.toReal_add (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
      (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))]
  cases b <;>
    simp [ENNReal.toReal_mul, coin_apply_toReal, PMF.pure_apply, messageRate, noise] <;>
    field_simp <;> ring

/-- The joint law of the first player's revealed message and the other player's question. -/
noncomputable def messagePair (μ : PMF (X × Y)) (α : I) :
    PMF (Option X × Option Y) :=
  anchorPair μ (messageRate α) α

/-- For every supported message, Bob uses exactly the conditional distribution from the
original anchored law, as in the source's left reveal. -/
theorem conditionalSnd_messagePair (μ : PMF (X × Y)) (α : I)
    (h₀ : 0 < (α : ℝ)) (h₁ : (α : ℝ) < 1) (m : Option X)
    (hm : m ∈ ((messagePair μ α).map Prod.fst).support) :
    conditionalSnd (messagePair μ α) m = conditionalSnd (anchorPair μ α α) m := by
  apply conditionalSnd_anchorPair_left_rate μ (messageRate α) α α m hm
  cases m
  · simpa [coin_apply, Option.isNone] using
      (ENNReal.ofReal_ne_zero_iff.mpr h₀ : ENNReal.ofReal (α : ℝ) ≠ 0)
  · simpa [coin_apply, Option.isNone] using
      (ENNReal.ofReal_ne_zero_iff.mpr (sub_pos.mpr h₁) : ENNReal.ofReal (1 - (α : ℝ)) ≠ 0)

/-- Erase the revealed question with the additional noise probability. -/
noncomputable def noisyQuestion (α : I) (m : Option X) : PMF (Option X) :=
  (coin (noise α)).map fun k => if k then none else m

/-- Draw the message, then draw each player's question by its own conditional kernel. -/
noncomputable def leftLaw (μ : PMF (X × Y)) (α : I) :
    PMF (Option X × (Option X × Option Y)) :=
  ((messagePair μ α).map Prod.fst).bind fun m =>
    ((noisyQuestion α m).bind fun x =>
      (conditionalSnd (messagePair μ α) m).map (x, ·)).map (m, ·)

/-- The point-mass factorization in Claim 4.1 for the left reveal. At positive message mass,
the two kernels therefore give independent questions conditional on the message. -/
theorem leftLaw_apply (μ : PMF (X × Y)) (α : I) (m x : Option X) (y : Option Y) :
    leftLaw μ α (m, x, y) = ((messagePair μ α).map Prod.fst) m * noisyQuestion α m x *
      conditionalSnd (messagePair μ α) m y := by
  rw [leftLaw, bind_map_prodMk_apply, bind_map_prodMk_apply, mul_assoc]

/-- Given a supported message, the joint chance of two anchors is at least `η α`.
The mass form also records the probability of the message. -/
theorem leftLaw_bothAnchors_le (μ : PMF (X × Y)) (α : I) (m : Option X)
    (hm : m ∈ ((messagePair μ α).map Prod.fst).support) :
    ((messagePair μ α).map Prod.fst) m * ENNReal.ofReal (noise α : ℝ) *
      ENNReal.ofReal (α : ℝ) ≤ leftLaw μ α (m, none, none) := by
  have hnoise : ENNReal.ofReal (noise α : ℝ) ≤ noisyQuestion α m none := by
    simpa only [noisyQuestion, coin_apply, ite_true] using
      le_map_apply (coin (noise α)) (fun k => if k then none else m) true
  have hright := conditionalSnd_anchorPair_none μ (messageRate α) α m hm
  change conditionalSnd (messagePair μ α) m none = _ at hright
  rw [leftLaw_apply, hright]
  gcongr

private theorem map_dropMessage_leftLaw (μ : PMF (X × Y)) (α : I) :
    (leftLaw μ α).map Prod.snd = (messagePair μ α).bind fun q =>
      (noisyQuestion α q.1).map (·, q.2) := by
  conv_rhs => rw [← bind_conditionalSnd (messagePair μ α)]
  simp only [leftLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_bind, PMF.bind_map]
  congr 1 with m : 1
  exact PMF.bind_comm _ _ _

/-- The left reveal has the original anchored question marginal (Claim 4.2). -/
theorem map_snd_leftLaw (μ : PMF (X × Y)) (α : I) :
    (leftLaw μ α).map Prod.snd = anchorPair μ α α := by
  rw [map_dropMessage_leftLaw]
  let p := coin (messageRate α)
  let q := coin α
  let r := coin (noise α)
  let f (i j k : Bool) (xy : X × Y) : Option X × Option Y :=
    (if k then none else if i then none else some xy.1, if j then none else some xy.2)
  calc
    _ = p.bind (fun i => q.bind fun j => μ.bind fun xy => r.map fun k => f i j k xy) := by
      simp only [messagePair, anchorPair, noisyQuestion, PMF.bind_bind, PMF.bind_map,
        PMF.map_comp, Function.comp_def, p, q, r, f]
    _ = p.bind (fun i => r.bind fun k => q.bind fun j => μ.map (f i j k)) := by
      refine congrArg (PMF.bind p) (funext fun i => ?_)
      calc
        _ = q.bind (fun j => r.bind fun k => μ.map (f i j k)) := by
          refine congrArg (PMF.bind q) (funext fun j => ?_)
          exact PMF.bind_comm _ _ _
        _ = _ := PMF.bind_comm _ _ _
    _ = (p.bind fun i => r.map fun k => i || k).bind (fun z =>
          q.bind fun j => μ.map fun xy => (if z then none else some xy.1,
            if j then none else some xy.2)) := by
      simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def]
      refine congrArg (PMF.bind p) (funext fun i =>
        congrArg (PMF.bind r) (funext fun k => ?_))
      cases i <;> cases k <;> rfl
    _ = _ := by
      rw [show (p.bind fun i => r.map fun k => i || k) = coin α from
        coin_messageRate_or_noise α]
      rfl

private theorem map_swap_anchorPair (μ : PMF (X × Y)) (α β : I) :
    (anchorPair μ α β).map Prod.swap = anchorPair (μ.map Prod.swap) β α := by
  simp only [anchorPair, PMF.map_bind, PMF.map_comp, Function.comp_def]
  exact PMF.bind_comm _ _ _

/-- Draw the right reveal by exchanging the players, then restore the question order. -/
noncomputable def rightLaw (μ : PMF (X × Y)) (α : I) :
    PMF (Option Y × (Option X × Option Y)) :=
  (leftLaw (μ.map Prod.swap) α).map ((Equiv.refl _).prodCongr (Equiv.prodComm _ _))

/-- The point-mass factorization for the right reveal. -/
theorem rightLaw_apply (μ : PMF (X × Y)) (α : I) (m y : Option Y) (x : Option X) :
    rightLaw μ α (m, x, y) = ((messagePair (μ.map Prod.swap) α).map Prod.fst) m *
      noisyQuestion α m y * conditionalSnd (messagePair (μ.map Prod.swap) α) m x := by
  rw [rightLaw, map_equiv_apply]
  exact leftLaw_apply (μ.map Prod.swap) α m y x

/-- The right reveal also has the original anchored question marginal (Claim 4.2). -/
theorem map_snd_rightLaw (μ : PMF (X × Y)) (α : I) :
    (rightLaw μ α).map Prod.snd = anchorPair μ α α := by
  rw [rightLaw, PMF.map_comp]
  change (leftLaw (μ.map Prod.swap) α).map (Prod.swap ∘ Prod.snd) = _
  rw [← PMF.map_comp, map_snd_leftLaw, map_swap_anchorPair, PMF.map_comp]
  have h : Prod.swap ∘ (Prod.swap : X × Y → Y × X) = id := funext Prod.swap_swap
  rw [h, PMF.map_id]

/-- Select the designated player fairly, then reveal that player's message and draw the pair. -/
noncomputable def law (μ : PMF (X × Y)) (α : I) :
    PMF (Sum (Option X) (Option Y) × (Option X × Option Y)) :=
  (uniformOfFintype Bool).bind fun left =>
    if left then (leftLaw μ α).map (Prod.map Sum.inl id)
    else (rightLaw μ α).map (Prod.map Sum.inr id)

/-- Forgetting both the designated player and the message gives the original anchored law. -/
theorem map_snd_law (μ : PMF (X × Y)) (α : I) :
    (law μ α).map Prod.snd = anchorPair μ α α := by
  rw [law, PMF.map_bind]
  have h (left : Bool) :
      ((if left then (leftLaw μ α).map (Prod.map Sum.inl id)
        else (rightLaw μ α).map (Prod.map Sum.inr id)).map
        (Prod.snd : Sum (Option X) (Option Y) × (Option X × Option Y) → _)) =
        anchorPair μ α α := by
    cases left <;> simp only [Bool.false_eq_true, ite_false, ite_true, PMF.map_comp]
    · exact map_snd_rightLaw μ α
    · exact map_snd_leftLaw μ α
  simp only [h, PMF.bind_const]

/-- Independent copies of the revealed experiment have precisely the repeated game's question law.
This is the question marginal in BVY Claim 4.3. -/
theorem map_questions_pi_law {A B : Type*} [Finite X] [Finite Y]
    (G : TwoProverGame X Y A B) (α : I) (n : ℕ) :
    (pi fun _ : Fin n => law G.questions α).map
      (fun samples => (Prod.fst ∘ Prod.snd ∘ samples, Prod.snd ∘ Prod.snd ∘ samples)) =
        ((G.anchored α).pow n).questions := by
  rw [show (fun samples : Fin n → Sum (Option X) (Option Y) × (Option X × Option Y) =>
      (Prod.fst ∘ Prod.snd ∘ samples, Prod.snd ∘ Prod.snd ∘ samples)) =
      (fun qs : Fin n → Option X × Option Y => (Prod.fst ∘ qs, Prod.snd ∘ qs)) ∘
        (fun samples => Prod.snd ∘ samples) from rfl]
  rw [← PMF.map_comp]
  have hproject : (pi fun _ : Fin n => law G.questions α).map
      (fun samples => Prod.snd ∘ samples) =
        pi (fun _ : Fin n => (law G.questions α).map Prod.snd) :=
    (pi_map (fun _ : Fin n => law G.questions α) (fun _ => Prod.snd)).symm
  rw [hproject]
  simp only [map_snd_law, TwoProverGame.pow, TwoProverGame.anchored_questions, Function.comp_def]

end Cslib.PCP.AnchoredDependency
