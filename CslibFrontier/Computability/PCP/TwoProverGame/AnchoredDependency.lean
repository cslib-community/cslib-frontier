/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.TwoProverGame.Anchoring
import CslibFrontier.Probability.PMF.Expect
import CslibFrontier.Probability.PMF.Bind

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

/-- The extra erase probability as a real number. -/
@[simp] theorem coe_noise (α : I) : (noise α : ℝ) = (α : ℝ) / 2 := by
  unfold noise
  rfl

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

/-- The original anchored pair is dominated by the message-and-other-question law
with factor `2 / α` for positive `α`. The product form holds also at zero rate. -/
theorem noise_mul_anchorPair_le_messagePair (μ : PMF (X × Y)) (α : I)
    (q : Option X × Option Y) :
    ((α : ℝ) / 2) * (anchorPair μ α α q).toReal ≤ (messagePair μ α q).toReal := by
  have hα₀ := α.2.1
  have hα₁ := α.2.2
  have hden : 0 < 2 - (α : ℝ) := by linarith
  have hβ₀ : (α : ℝ) / 2 ≤ (messageRate α : ℝ) := by
    change _ ≤ (α : ℝ) / (2 - α)
    rw [le_div_iff₀ hden]
    nlinarith [sq_nonneg (α : ℝ)]
  have hβ₁ : (messageRate α : ℝ) ≤ α := by
    change (α : ℝ) / (2 - α) ≤ _
    rw [div_le_iff₀ hden]
    nlinarith [mul_nonneg hα₀ (sub_nonneg.mpr hα₁)]
  have ha : (α : ℝ) / 2 * α ≤ messageRate α :=
    (mul_le_of_le_one_right (by positivity) hα₁).trans hβ₀
  have hb : (α : ℝ) / 2 * (1 - α) ≤ 1 - (messageRate α : ℝ) :=
    (mul_le_of_le_one_left (sub_nonneg.mpr hα₁) (by linarith)).trans (sub_le_sub_left hβ₁ 1)
  rcases q with ⟨x, y⟩
  cases x <;> cases y <;>
    simp only [messagePair, anchorPair_apply, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal α.2.1, ENNReal.toReal_ofReal (messageRate α).2.1,
      ENNReal.toReal_ofReal (sub_nonneg.mpr α.2.2),
      ENNReal.toReal_ofReal (sub_nonneg.mpr (messageRate α).2.2)]
  all_goals
    simp only [← mul_assoc]
    first
    | exact mul_le_mul_of_nonneg_right ha (by positivity)
    | exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha (by positivity))
        ENNReal.toReal_nonneg
    | exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hb (by positivity))
        ENNReal.toReal_nonneg

/-- Erase the revealed question with the additional noise probability. -/
@[expose] noncomputable def noisyQuestion (α : I) (m : Option X) : PMF (Option X) :=
  (coin (noise α)).map fun k => if k then none else m

/-- Draw the message, then draw each player's question by its own conditional kernel. -/
noncomputable def leftLaw (μ : PMF (X × Y)) (α : I) :
    PMF (Option X × (Option X × Option Y)) :=
  ((messagePair μ α).map Prod.fst).bind fun m =>
    ((noisyQuestion α m).bind fun x =>
      (conditionalSnd (messagePair μ α) m).map (x, ·)).map (m, ·)

/-- Forgetting the further noisy question leaves the original message and the other question. -/
theorem map_messageAndBob_leftLaw (μ : PMF (X × Y)) (α : I) :
    (leftLaw μ α).map (fun (m, _, y) => (m, y)) = messagePair μ α := by
  conv_rhs => rw [← bind_conditionalSnd (messagePair μ α)]
  simp only [leftLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, PMF.bind_const]

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

private theorem law_inl_apply (μ : PMF (X × Y)) (α : I) (m : Option X)
    (q : Option X × Option Y) :
    law μ α (Sum.inl m, q) = (uniformOfFintype Bool) true * leftLaw μ α (m, q) := by
  have hzero : ((rightLaw μ α).map (Prod.map Sum.inr id)) (Sum.inl m, q) = 0 := by
    rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
    rintro ⟨z, -, hz⟩
    have h := congrArg (fun z : (Option X ⊕ Option Y) × (Option X × Option Y) => z.1) hz
    cases h
  rw [law, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  have hinj : Function.Injective (Prod.map (Sum.inl : Option X → Option X ⊕ Option Y)
      (id : Option X × Option Y → Option X × Option Y)) :=
    Sum.inl_injective.prodMap Function.injective_id
  have hmap := map_apply_of_injective (leftLaw μ α) hinj (m, q)
  simpa only [Bool.false_eq_true, ite_false, ite_true, hzero, mul_zero, add_zero,
    Prod.map_apply, id_eq] using congrArg ((uniformOfFintype Bool) true * ·) hmap

private theorem law_inr_apply (μ : PMF (X × Y)) (α : I) (m : Option Y)
    (q : Option X × Option Y) :
    law μ α (Sum.inr m, q) = (uniformOfFintype Bool) false * rightLaw μ α (m, q) := by
  have hzero : ((leftLaw μ α).map (Prod.map Sum.inl id)) (Sum.inr m, q) = 0 := by
    rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
    rintro ⟨z, -, hz⟩
    have h := congrArg (fun z : (Option X ⊕ Option Y) × (Option X × Option Y) => z.1) hz
    cases h
  rw [law, PMF.bind_apply, tsum_fintype, Fintype.sum_bool]
  have hinj : Function.Injective (Prod.map (Sum.inr : Option Y → Option X ⊕ Option Y)
      (id : Option X × Option Y → Option X × Option Y)) :=
    Sum.inr_injective.prodMap Function.injective_id
  have hmap := map_apply_of_injective (rightLaw μ α) hinj (m, q)
  simpa only [Bool.false_eq_true, ite_false, ite_true, hzero, mul_zero, zero_add,
    Prod.map_apply, id_eq] using congrArg ((uniformOfFintype Bool) false * ·) hmap

/-- Choosing Alice's message tag and reading Bob's question dominates the anchored
pair for every nonnegative score. The factor `α / 4` includes the fair tag choice. -/
theorem sum_anchoredPair_le_sum_leftReveal [Fintype X] [Fintype Y]
    (μ : PMF (X × Y)) (α : I) (score : Option X × Option Y → ℝ)
    (hscore : ∀ q, 0 ≤ score q) :
    ((α : ℝ) / 4) * (∑ q, (anchorPair μ α α q).toReal * score q) ≤
      ∑ z, (law μ α z).toReal *
        (match z with
        | (.inl m, _, y) => score (m, y)
        | (.inr _, _, _) => 0) := by
  have h : (α : ℝ) / 2 * (∑ q, (anchorPair μ α α q).toReal * score q) ≤
      ∑ q, (messagePair μ α q).toReal * score q := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun q _ => by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (noise_mul_anchorPair_le_messagePair μ α q) (hscore q)
  have hleft : ((uniformOfFintype Bool) true).toReal = 1 / 2 := by
    norm_num [Probability.PMF.uniformOfFintype_apply]
  have hsum : (∑ z, (law μ α z).toReal *
        (match z with
        | (.inl m, _, y) => score (m, y)
        | (.inr _, _, _) => 0)) =
      (1 / 2) * ∑ q, (messagePair μ α q).toReal * score q := by
    rw [← map_messageAndBob_leftLaw, sum_map_mul]
    simp only [Fintype.sum_prod_type, Fintype.sum_sum_type, law_inl_apply, ENNReal.toReal_mul,
      hleft, mul_zero, Finset.sum_const_zero, add_zero, Finset.mul_sum, mul_assoc]
  rw [hsum]
  linarith

/-- Exchanging both the message tag and the questions gives the reveal law of the exchanged
question distribution. -/
theorem map_swap_law (μ : PMF (X × Y)) (α : I) :
    (law μ α).map (Prod.map Sum.swap Prod.swap) = law (μ.map Prod.swap) α := by
  have hμ : (μ.map Prod.swap).map Prod.swap = μ := by
    rw [PMF.map_comp, show Prod.swap ∘ (Prod.swap : X × Y → Y × X) = id from
      funext Prod.swap_swap, PMF.map_id]
  have hcoin : (uniformOfFintype Bool) true = (uniformOfFintype Bool) false := by
    simp only [Probability.PMF.uniformOfFintype_apply]
  ext ⟨m, y, x⟩
  change ((law μ α).map ((Equiv.sumComm _ _).prodCongr (Equiv.prodComm _ _))) (m, y, x) = _
  rw [map_equiv_apply]
  cases m with
  | inl m =>
    change law μ α (Sum.inr m, x, y) = law (μ.map Prod.swap) α (Sum.inl m, y, x)
    rw [law_inr_apply, law_inl_apply, hcoin, rightLaw, map_equiv_apply]
    rfl
  | inr m =>
    change law μ α (Sum.inl m, x, y) = law (μ.map Prod.swap) α (Sum.inr m, y, x)
    rw [law_inl_apply, law_inr_apply, hcoin, rightLaw, map_equiv_apply, hμ]
    rfl

/-- Choosing Bob's message tag and reading Alice's question has the corresponding
domination bound with the players exchanged. -/
theorem sum_anchoredPair_le_sum_rightReveal [Fintype X] [Fintype Y]
    (μ : PMF (X × Y)) (α : I) (score : Option X × Option Y → ℝ)
    (hscore : ∀ q, 0 ≤ score q) :
    ((α : ℝ) / 4) * (∑ q, (anchorPair μ α α q).toReal * score q) ≤
      ∑ z, (law μ α z).toReal *
        (match z with
        | (.inr m, x, _) => score (x, m)
        | (.inl _, _, _) => 0) := by
  have h := sum_anchoredPair_le_sum_leftReveal (μ.map Prod.swap) α (score ∘ Prod.swap)
    (fun q => hscore q.swap)
  rw [← map_swap_anchorPair, sum_map_mul, ← map_swap_law, sum_map_mul] at h
  simp only [Function.comp_apply, Prod.swap_swap] at h
  convert h using 1
  refine Finset.sum_congr rfl ?_
  rintro ⟨m, x, y⟩ _
  cases m <;> rfl

/-- Given a supported left message, the questions are sampled independently. -/
theorem conditionalSnd_law_inl (μ : PMF (X × Y)) (α : I) (m : Option X)
    (hm : Sum.inl m ∈ ((law μ α).map Prod.fst).support) :
    conditionalSnd (law μ α) (Sum.inl m) =
      (noisyQuestion α m).bind fun x =>
        (conditionalSnd (messagePair μ α) m).map (x, ·) := by
  have hcond : conditionalSnd (law μ α) (Sum.inl m) = conditionalSnd (leftLaw μ α) m := by
    apply conditionalSnd_eq_of_scaled_slices _ _ _ _ 1 ((uniformOfFintype Bool) true) hm
      one_ne_zero ENNReal.one_ne_top
    intro q
    rw [one_mul, law_inl_apply]
  have hm' : m ∈ ((messagePair μ α).map Prod.fst).support := by
    have hmass : ((law μ α).map Prod.fst) (Sum.inl m) =
        (uniformOfFintype Bool) true * ((messagePair μ α).map Prod.fst) m := by
      rw [map_fst_apply]
      simp_rw [law_inl_apply]
      rw [ENNReal.tsum_mul_left, ← map_fst_apply, leftLaw, map_fst_bind_pair]
    rw [PMF.mem_support_iff, hmass, mul_ne_zero_iff] at hm
    exact hm.2
  rw [hcond, leftLaw]
  exact conditionalSnd_bind_pair _ _ _ hm'

/-- Given a supported right message, the questions are sampled independently. -/
theorem conditionalSnd_law_inr (μ : PMF (X × Y)) (α : I) (m : Option Y)
    (hm : Sum.inr m ∈ ((law μ α).map Prod.fst).support) :
    conditionalSnd (law μ α) (Sum.inr m) =
      (conditionalSnd (messagePair (μ.map Prod.swap) α) m).bind fun x =>
        (noisyQuestion α m).map (x, ·) := by
  have hr : rightLaw μ α =
      ((messagePair (μ.map Prod.swap) α).map Prod.fst).bind fun r =>
        ((conditionalSnd (messagePair (μ.map Prod.swap) α) r).bind fun x =>
          (noisyQuestion α r).map (x, ·)).map (r, ·) := by
    simp only [rightLaw, leftLaw, PMF.map_bind, PMF.map_comp, Function.comp_def]
    congr 1 with r : 1
    simp only [← PMF.bind_pure_comp, Function.comp_def]
    exact PMF.bind_comm _ _ (fun y x => PMF.pure (r, x, y))
  have hcond : conditionalSnd (law μ α) (Sum.inr m) = conditionalSnd (rightLaw μ α) m := by
    apply conditionalSnd_eq_of_scaled_slices _ _ _ _ 1 ((uniformOfFintype Bool) false) hm
      one_ne_zero ENNReal.one_ne_top
    intro q
    rw [one_mul, law_inr_apply]
  have hm' : m ∈ ((messagePair (μ.map Prod.swap) α).map Prod.fst).support := by
    have hmass : ((law μ α).map Prod.fst) (Sum.inr m) =
        (uniformOfFintype Bool) false * ((messagePair (μ.map Prod.swap) α).map Prod.fst) m := by
      rw [map_fst_apply]
      simp_rw [law_inr_apply]
      rw [ENNReal.tsum_mul_left, ← map_fst_apply, hr, map_fst_bind_pair]
    rw [PMF.mem_support_iff, hmass, mul_ne_zero_iff] at hm
    exact hm.2
  rw [hcond, hr]
  exact conditionalSnd_bind_pair _ _ _ hm'

/-- Alice's question law given the tagged noisy message. -/
@[expose] noncomputable def aliceGivenMessage (μ : PMF (X × Y)) (α : I) :
    Option X ⊕ Option Y → PMF (Option X)
  | .inl x => noisyQuestion α x
  | .inr y => conditionalSnd (messagePair (μ.map Prod.swap) α) y

/-- Bob's question law given the tagged noisy message. -/
@[expose] noncomputable def bobGivenMessage (μ : PMF (X × Y)) (α : I) :
    Option X ⊕ Option Y → PMF (Option Y)
  | .inl x => conditionalSnd (messagePair μ α) x
  | .inr y => noisyQuestion α y

/-- The single-trial law is obtained by sampling the message, then the two independent
local questions. -/
theorem law_eq_bind_messages (μ : PMF (X × Y)) (α : I) :
    law μ α = ((law μ α).map Prod.fst).bind fun m =>
      ((aliceGivenMessage μ α m).bind fun x => (bobGivenMessage μ α m).map (x, ·)).map (m, ·) := by
  conv_lhs => rw [← bind_conditionalSnd (law μ α)]
  apply bind_congr_on_support
  intro m hm
  cases m with
  | inl x => rw [conditionalSnd_law_inl μ α x hm]; rfl
  | inr y => rw [conditionalSnd_law_inr μ α y hm]; rfl

/-- Conditional on each supported tagged message, the probability of two anchors is at
least `α² / 2`. The mass form also holds for unsupported messages. -/
theorem law_bothAnchors_le (μ : PMF (X × Y)) (α : I) (m : Option X ⊕ Option Y) :
    ((law μ α).map Prod.fst) m * ENNReal.ofReal (noise α : ℝ) * ENNReal.ofReal (α : ℝ) ≤
      law μ α (m, none, none) := by
  have hleft (m : Option X) : ((leftLaw μ α).map Prod.fst) m =
      ((messagePair μ α).map Prod.fst) m := by
    simp only [leftLaw, map_fst_bind_pair]
  have hright (m : Option Y) : ((rightLaw μ α).map Prod.fst) m =
      ((messagePair (μ.map Prod.swap) α).map Prod.fst) m := by
    rw [rightLaw, PMF.map_comp]
    change ((leftLaw (μ.map Prod.swap) α).map Prod.fst) m = _
    simp only [leftLaw, map_fst_bind_pair]
  cases m with
  | inl m =>
    rw [map_fst_apply, law_inl_apply]
    simp_rw [law_inl_apply]
    rw [ENNReal.tsum_mul_left, ← map_fst_apply, hleft, mul_assoc, mul_assoc]
    gcongr
    by_cases hm : m ∈ ((messagePair μ α).map Prod.fst).support
    · simpa only [mul_assoc] using leftLaw_bothAnchors_le μ α m hm
    · rw [PMF.mem_support_iff, not_not] at hm
      simp [hm]
  | inr m =>
    rw [map_fst_apply, law_inr_apply]
    simp_rw [law_inr_apply]
    rw [ENNReal.tsum_mul_left, ← map_fst_apply, hright, mul_assoc, mul_assoc]
    gcongr
    by_cases hm : m ∈ ((messagePair (μ.map Prod.swap) α).map Prod.fst).support
    · rw [rightLaw, map_equiv_apply]
      change _ ≤ leftLaw (μ.map Prod.swap) α (m, none, none)
      simpa only [mul_assoc] using leftLaw_bothAnchors_le (μ.map Prod.swap) α m hm
    · rw [PMF.mem_support_iff, not_not] at hm
      simp [hm]

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
