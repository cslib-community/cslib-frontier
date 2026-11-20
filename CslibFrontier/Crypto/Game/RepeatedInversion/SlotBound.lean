/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Crypto.Game.RepeatedInversion
public import CslibFrontier.Crypto.Game.Inversion
import CslibFrontier.Languages.Probabilistic.Oracle.RunLogAgree
import CslibFrontier.Probability.PMF.Bool
import CslibFrontier.Probability.PMF.Bind

/-!
# Repeated one-way inversion: the guessing step

A win of the repeated chain game `repeatedIterateExperiment` names a chain and, on it, a slot below
every revealed one. Planting an inversion challenge above slot `g` (`slotInverter`) therefore
inverts `f` on the law of that slot, and summing over the `n * d` slots bounds the repeated game
(`succProbability_repeatedIterateExperiment_le_sum`). At `d = 1`, with the slot drawn exactly
uniformly below `t` as by the adversary `B` in the proof of [BonehShoup2023], Lemma 13.5,
pp. 539–540 (`plantInverter`), this gives that lemma's inequality (13.6) for the typed game,
`rOWadv[A, f, t] ≤ t · OWadv[B, f]` (`succProbability_repeatedInversionExperiment_le`).

The statements are about typed games and say nothing about running time. `slotInverter` is
certified inside the word-level reduction `repeatedInverter`
(`CslibFrontier/Crypto/Computational/OneWay/Repeated.lean`), which draws a dyadic index and,
when it is below `t n`, runs `slotInverter` at it. `plantInverter` has no efficiency certificate:
a strict PPT sampler draws an exactly uniform index below `t` only when `t` is a power of two. So
(13.6) here is not Lemma 13.5 itself, whose `B` is efficient. The efficient form is
`OneWayOn.repeatedInversion_negligible`, through `succProbability_repeatedInversionGameOn_le`,
which loses the dyadic range `dyadicSize (t n)` in place of `t`.

## Main definitions

* `Cslib.Crypto.slotInverter`: the inverter that plants its challenge above one slot.
* `Cslib.Crypto.plantInverter`: the book's inverter for (13.6), planting at an exactly uniform
  index; it has no efficiency certificate.

## Main results

* `Cslib.Crypto.succProbability_repeatedIterateExperiment_le_sum`: the chain game is bounded by
  the sum over slots of the inversion games of `slotInverter`.
* `Cslib.Crypto.succProbability_repeatedInversionExperiment_le_sum`: the `d = 1` case.
* `Cslib.Crypto.succProbability_repeatedInversionExperiment_le`: the inequality (13.6) for the
  typed game.

## References

* [D. Boneh, V. Shoup, *A Graduate Course in Applied Cryptography*][BonehShoup2023],
  Section 13.4.1, Lemma 13.5, (13.6), pp. 539–540; Exercise 14.15, p. 612.
-/

public section

namespace Cslib.Crypto

open Cslib Probability
open scoped ENNReal NNReal

variable {Q X : Type} [Inhabited X] [DecidableEq X]

/-! ### The reduction: plant the challenge above one slot -/

/-- Invert `f` at `c` by planting `c` above slot `g`: chain `g / d` is simulated from `c` at the
positions above `g % d`, the other chains are sampled, and the slots at or below `g` on that
chain, which the reduction does not know, are answered with `default`. A claim for a slot at or
below `g` on that chain is pushed up to position `g % d`. -/
@[expose] def slotInverter (idx : Q → ℕ) (sample : ProbComp X) (f : X → X) (n d g : ℕ)
    (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) (c : X) : ProbComp X := do
  let front ← OracleComp.replicate (g / d) sample
  let back ← OracleComp.replicate (n - g / d - 1) sample
  let out ← (A (front.map f^[d] ++ f^[d - 1 - g % d] c :: back.map f^[d])).run fun q =>
    pure (if idx q / d = g / d then
        if g % d < idx q % d then f^[idx q % d - g % d - 1] c else default
      else chainSlot f d (front ++ default :: back) (idx q))
  return if idx out.1 / d = g / d ∧ idx out.1 % d ≤ g % d then f^[g % d - idx out.1 % d] out.2
    else default

/-! ### Proof of the plug-and-pray step -/

/-- Slot `g` is at or above the claimed slot on its chain and below every revealed slot of that
chain, and the claim pushed up to `g` inverts `f` at the value above slot `g`. -/
private def slotHit (idx : Q → ℕ) (f : X → X) (d g : ℕ) (xs : List X)
    (z : (Q × X) × List (Q × X)) : Bool :=
  decide (idx z.1.1 / d = g / d ∧ idx z.1.1 % d ≤ g % d ∧
    (∀ r ∈ z.2, ¬ (idx r.1 / d = g / d ∧ idx r.1 % d ≤ g % d)) ∧
    f (f^[g % d - idx z.1.1 % d] z.1.2) = f (f^[g % d] (xs.getD (g / d) default)))

/-- A win of the chain game points to a slot: the one just below the lowest revealed slot of the
claimed chain. -/
private theorem exists_slotHit {idx : Q → ℕ} {f : X → X} {n d : ℕ} (hd : 0 < d) {xs : List X}
    (hxs : xs.length = n) {q : Q} {x : X} {log : List (Q × X)}
    (hlog : ∀ r ∈ log, r.2 = chainSlot f d xs (idx r.1))
    (hwin : (chainVerify f d (xs.map f^[d]) (idx q) x && chainConsistent idx f d q x log) = true) :
    ∃ g ∈ Finset.range (n * d), slotHit idx f d g xs ((q, x), log) = true := by
  classical
  rw [Bool.and_eq_true] at hwin
  obtain ⟨hver, hcons⟩ := hwin
  have hbd : idx q % d < d := Nat.mod_lt _ hd
  have hver' : idx q / d < n ∧ f^[d - idx q % d] x = f^[d] (xs.getD (idx q / d) default) := by
    simp only [chainVerify, beq_iff_eq, List.getElem?_map, Option.map_eq_some_iff] at hver
    obtain ⟨y, hy, hfy⟩ := hver
    have hget : xs.getD (idx q / d) default = y := by
      rw [List.getD_eq_getElem?_getD, hy]
      rfl
    exact ⟨hxs ▸ (List.getElem?_eq_some_iff.mp hy).1, hget ▸ hfy.symm⟩
  have hcons' : ∀ r ∈ log, idx r.1 / d = idx q / d →
      idx q % d < idx r.1 % d ∧ f^[idx r.1 % d - idx q % d] x = r.2 := by
    simp only [chainConsistent, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hcons
    intro r hr hra
    exact (hcons r hr).resolve_left (not_not.mpr hra)
  have hP : ∃ m, m + 1 = d ∨ ∃ r ∈ log, idx r.1 / d = idx q / d ∧ idx r.1 % d = m + 1 :=
    ⟨d - 1, Or.inl (by omega)⟩
  have hp := Nat.find_spec hP
  have hmin : ∀ m, m < Nat.find hP →
      ¬ (m + 1 = d ∨ ∃ r ∈ log, idx r.1 / d = idx q / d ∧ idx r.1 % d = m + 1) :=
    fun m hm => Nat.find_min hP hm
  generalize Nat.find hP = p at hp hmin
  have hpd : p < d := by
    rcases hp with hp | ⟨r, -, -, hr⟩
    · omega
    · have := Nat.mod_lt (idx r.1) hd
      omega
  have hbp : idx q % d ≤ p := by
    rcases hp with hp | ⟨r, hr, hra, hrp⟩
    · omega
    · have := (hcons' r hr hra).1
      omega
  have hgd : (idx q / d * d + p) / d = idx q / d := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hd, Nat.div_eq_of_lt hpd, zero_add]
  have hgm : (idx q / d * d + p) % d = p := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hpd]
  refine ⟨idx q / d * d + p, Finset.mem_range.mpr ?_, ?_⟩
  · calc idx q / d * d + p < idx q / d * d + d := by omega
      _ = (idx q / d + 1) * d := by ring
      _ ≤ n * d := Nat.mul_le_mul_right d hver'.1
  · simp only [slotHit, decide_eq_true_eq, hgd, hgm]
    refine ⟨trivial, hbp, ?_, ?_⟩
    · rintro r hr ⟨hra, hrp⟩
      have hbr := (hcons' r hr hra).1
      exact hmin (idx r.1 % d - 1) (by omega) (Or.inr ⟨r, hr, hra, by omega⟩)
    · have e1 : f (f^[p - idx q % d] x) = f^[p - idx q % d + 1] x :=
        (Function.iterate_succ_apply' f _ x).symm
      have e2 : f (f^[p] (xs.getD (idx q / d) default)) = f^[p + 1] (xs.getD (idx q / d) default) :=
        (Function.iterate_succ_apply' f _ _).symm
      rw [e1, e2]
      rcases hp with hp | ⟨r, hr, hra, hrp⟩
      · rw [show p - idx q % d + 1 = d - idx q % d by omega, hp]
        exact hver'.2
      · have h2 := (hcons' r hr hra).2
        rw [hlog r hr, chainSlot, hra, hrp] at h2
        rw [show p - idx q % d + 1 = p + 1 - idx q % d by omega]
        exact h2

omit [DecidableEq X] in
/-- Away from the slots at or below `g` on its chain, the reveal oracle of the seeds
`front ++ x₀ :: back` is the oracle that `slotInverter` simulates from `f (f^[g % d] x₀)`. -/
private theorem chainSlot_eq_of_not_below {idx : Q → ℕ} {f : X → X} {d g : ℕ} {front : List X}
    (hfront : front.length = g / d) (back : List X) (x₀ : X) {q : Q}
    (hq : ¬ (idx q / d = g / d ∧ idx q % d ≤ g % d)) :
    chainSlot f d (front ++ x₀ :: back) (idx q) =
      if idx q / d = g / d then
        if g % d < idx q % d then f^[idx q % d - g % d - 1] (f (f^[g % d] x₀)) else default
      else chainSlot f d (front ++ default :: back) (idx q) := by
  by_cases h : idx q / d = g / d
  · have hlt : g % d < idx q % d := by
      by_contra hcon
      exact hq ⟨h, Nat.le_of_not_lt hcon⟩
    have e : f^[idx q % d - g % d - 1] (f (f^[g % d] x₀)) = f^[idx q % d] x₀ := by
      rw [← Function.iterate_succ_apply' f, ← Function.iterate_add_apply]
      exact congrArg (fun k => f^[k] x₀) (by omega)
    have hget : (front ++ x₀ :: back).getD front.length default = x₀ := by simp
    rw [ite_eq_left h, ite_eq_left hlt, e, chainSlot, h, ← hfront, hget]
  · rw [ite_eq_right h, chainSlot, chainSlot]
    congr 1
    rw [← hfront] at h
    rcases Nat.lt_or_gt_of_ne h with h | h
    · simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
    · obtain ⟨k, hk⟩ : ∃ k, idx q / d = front.length + (k + 1) :=
        ⟨idx q / d - front.length - 1, by omega⟩
      simp [List.getD_eq_getElem?_getD, hk, List.getElem?_append_right]

omit [Inhabited X] [DecidableEq X] in
/-- The public key that `slotInverter` builds from the challenge above slot `g` is the public key
of the seeds `front ++ x₀ :: back`. -/
private theorem slotKey_eq {f : X → X} {d p : ℕ} (hp : p < d) (front back : List X) (x₀ : X) :
    front.map f^[d] ++ f^[d - 1 - p] (f (f^[p] x₀)) :: back.map f^[d] =
      (front ++ x₀ :: back).map f^[d] := by
  have e : f^[d - 1 - p] (f (f^[p] x₀)) = f^[d] x₀ := by
    rw [← Function.iterate_succ_apply' f, ← Function.iterate_add_apply]
    exact congrArg (fun k => f^[k] x₀) (by omega)
  rw [e, List.map_append, List.map_cons]

/-- An event of one law whose outcomes are at least as likely under a second law, and satisfy a
second event, is at most as likely as the second event under the second law. -/
private theorem map_true_le_map_true_of_le {α : Type} (μ ν : PMF α) {E F : α → Bool}
    (h : ∀ a, E a = true → μ a ≤ ν a ∧ F a = true) : μ.map E true ≤ ν.map F true := by
  rw [PMF.map_apply_true, PMF.map_apply_true]
  refine tsum_le_tsum fun a => ?_
  cases hE : E a
  · simp
  · obtain ⟨hle, hF⟩ := h a hE
    simp [hF, hle]

/-- **The plug-and-pray step.** A win of the repeated game names a chain and, on it, the highest
slot below everything revealed; planting the challenge above that slot inverts `f` on the law of
that slot. -/
theorem succProbability_repeatedIterateExperiment_le_sum (idx : Q → ℕ) (sample : ProbComp X)
    (f : X → X) (n : ℕ) {d : ℕ} (hd : 0 < d)
    (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) :
    Experiment.succProbability (repeatedIterateExperiment idx sample f n d A) ≤
      ∑ g ∈ Finset.range (n * d), Experiment.succProbability
        (inversionExperiment (f^[g % d] <$> sample) f (slotInverter idx sample f n d g A)) := by
  -- The joint law of the seeds and the logged run of the game.
  set D : PMF (List X × ((Q × X) × List (Q × X))) :=
    (ProbComp.eval (OracleComp.replicate n sample)).bind fun xs =>
      (ProbComp.eval ((A (xs.map f^[d])).runLog fun q => pure (chainSlot f d xs (idx q)))).map
        (Prod.mk xs) with hD
  have hsupp : ∀ w ∈ D.support,
      w.1.length = n ∧ ∀ r ∈ w.2.2, r.2 = chainSlot f d w.1 (idx r.1) := by
    rintro ⟨xs, z⟩ hw
    simp only [hD, PMF.mem_support_bind_iff, PMF.mem_support_map_iff, Prod.mk.injEq] at hw
    obtain ⟨xs', hxs', z', hz', rfl, rfl⟩ := hw
    refine ⟨((ProbComp.mem_support_replicate_iff _ _ _).mp hxs').1, ?_⟩
    rw [← ProbOracleComp.runLogWith_some] at hz'
    exact ProbOracleComp.forall_mem_runLogWith
      (P := fun p => p.2 = chainSlot f d xs' (idx p.1)) (fun log q program hprog r hr => by
        cases hprog
        simpa using hr) _ hz'
  have hreal : ProbComp.eval (repeatedIterateExperiment idx sample f n d A) =
      D.map fun w => chainVerify f d (w.1.map f^[d]) (idx w.2.1.1) w.2.1.2 &&
        chainConsistent idx f d w.2.1.1 w.2.1.2 w.2.2 := by
    rw [repeatedIterateExperiment, eval_forgeExperiment_eq, hD, PMF.map_bind]
    simp only [chainKeyGen, ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
      PMF.map_comp]
    rfl
  have hstep : ∀ g ∈ Finset.range (n * d),
      (D.map fun w => slotHit idx f d g w.1 w.2) true ≤ ProbComp.eval (inversionExperiment
        (f^[g % d] <$> sample) f (slotInverter idx sample f n d g A)) true := by
    intro g hg
    have hgn : g / d < n :=
      Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact Finset.mem_range.mp hg)
    have hpd : g % d < d := Nat.mod_lt _ hd
    have hrep := ProbComp.eval_replicate_splice sample (g / d) (n - g / d - 1)
    rw [show g / d + (n - g / d - 1 + 1) = n by omega] at hrep
    have hL : (D.map fun w => slotHit idx f d g w.1 w.2) =
        (ProbComp.eval sample).bind fun x₀ =>
        (ProbComp.eval (OracleComp.replicate (g / d) sample)).bind fun front =>
        (ProbComp.eval (OracleComp.replicate (n - g / d - 1) sample)).bind fun back =>
        (ProbComp.eval ((A ((front ++ x₀ :: back).map f^[d])).runLog fun q =>
          pure (chainSlot f d (front ++ x₀ :: back) (idx q)))).map
            (slotHit idx f d g (front ++ x₀ :: back)) := by
      rw [hD, ← hrep]
      simp only [ProbComp.eval_bind, ProbComp.eval_pure, PMF.bind_bind, PMF.pure_bind,
        PMF.map_bind, PMF.map_comp]
      rfl
    have hR : ProbComp.eval (inversionExperiment (f^[g % d] <$> sample) f
          (slotInverter idx sample f n d g A)) =
        (ProbComp.eval sample).bind fun x₀ =>
        (ProbComp.eval (OracleComp.replicate (g / d) sample)).bind fun front =>
        (ProbComp.eval (OracleComp.replicate (n - g / d - 1) sample)).bind fun back =>
        (ProbComp.eval ((A (front.map f^[d] ++ f^[d - 1 - g % d] (f (f^[g % d] x₀)) ::
            back.map f^[d])).runLog fun q =>
          pure (if idx q / d = g / d then
              if g % d < idx q % d then f^[idx q % d - g % d - 1] (f (f^[g % d] x₀)) else default
            else chainSlot f d (front ++ default :: back) (idx q)))).map fun z =>
          f (if idx z.1.1 / d = g / d ∧ idx z.1.1 % d ≤ g % d then
            f^[g % d - idx z.1.1 % d] z.1.2 else default) == f (f^[g % d] x₀) := by
      simp only [inversionExperiment, slotInverter, ProbComp.eval_bind, ProbComp.eval_pure,
        ProbComp.eval_map, PMF.bind_bind, PMF.pure_bind, PMF.bind_map,
        ← ProbOracleComp.map_fst_eval_runLog, Function.comp_def]
      rfl
    rw [hL, hR]
    refine PMF.bind_apply_mono_on_support _ _ fun x₀ _ => ?_
    refine PMF.bind_apply_mono_on_support _ _ fun front hfront => ?_
    refine PMF.bind_apply_mono_on_support _ _ fun back _ => ?_
    have hlen : front.length = g / d := ((ProbComp.mem_support_replicate_iff _ _ _).mp hfront).1
    rw [slotKey_eq hpd]
    refine map_true_le_map_true_of_le _ _ fun z hz => ?_
    simp only [slotHit, decide_eq_true_eq] at hz
    obtain ⟨hza, hzb, hzlog, hzf⟩ := hz
    refine ⟨le_of_eq (ProbOracleComp.eval_runLog_apply_eq_of_agree
      (bad := fun q => idx q / d = g / d ∧ idx q % d ≤ g % d) (fun q hq => ?_) _ hzlog), ?_⟩
    · rw [chainSlot_eq_of_not_below hlen back x₀ hq]
    · have hget : (front ++ x₀ :: back).getD (g / d) default = x₀ := by
        rw [← hlen]
        simp
      rw [hget] at hzf
      simpa [hza, hzb] using hzf
  have hsum : ProbComp.eval (repeatedIterateExperiment idx sample f n d A) true ≤
      ∑ g ∈ Finset.range (n * d), ProbComp.eval (inversionExperiment (f^[g % d] <$> sample) f
        (slotInverter idx sample f n d g A)) true := by
    rw [hreal]
    refine (PMF.map_true_le_sum D (Finset.range (n * d))
      (F := fun g w => slotHit idx f d g w.1 w.2) fun w hw hE => ?_).trans
      (Finset.sum_le_sum hstep)
    obtain ⟨hlen, hlog⟩ := hsupp w hw
    obtain ⟨xs, ⟨q, x⟩, log⟩ := w
    exact exists_slotHit hd hlen hlog hE
  have htop : ∀ g ∈ Finset.range (n * d), ProbComp.eval (inversionExperiment (f^[g % d] <$> sample)
      f (slotInverter idx sample f n d g A)) true ≠ ⊤ := fun g _ => PMF.apply_ne_top _ _
  calc Experiment.succProbability (repeatedIterateExperiment idx sample f n d A)
      ≤ (∑ g ∈ Finset.range (n * d), ProbComp.eval (inversionExperiment (f^[g % d] <$> sample) f
          (slotInverter idx sample f n d g A)) true).toNNReal :=
        ENNReal.toNNReal_mono (ENNReal.sum_ne_top.mpr htop) hsum
    _ = _ := ENNReal.toNNReal_sum htop

/-- The slot sum behind (13.6): the `d = 1` case. -/
theorem succProbability_repeatedInversionExperiment_le_sum (idx : Q → ℕ) (sample : ProbComp X)
    (f : X → X) (t : ℕ) (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) :
    Experiment.succProbability (repeatedInversionExperiment idx sample f t A) ≤
      ∑ g ∈ Finset.range t, Experiment.succProbability
        (inversionExperiment sample f (slotInverter idx sample f t 1 g A)) := by
  have h := succProbability_repeatedIterateExperiment_le_sum idx sample f t Nat.one_pos A
  simpa only [repeatedIterateExperiment_one, mul_one, Nat.mod_one, Function.iterate_zero,
    id_map] using h

/-- The adversary `B` in the proof of [BonehShoup2023], Lemma 13.5, on the typed game: plant the
challenge at an exactly uniform index below `t`. It has no efficiency certificate, since a strict
PPT sampler draws an exactly uniform index below `t` only when `t` is a power of two; the certified
word-level reduction `repeatedInverter` draws a dyadic index instead. -/
@[expose] def plantInverter (idx : Q → ℕ) (sample : ProbComp X) (f : X → X) (t : ℕ)
    (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) (c : X) : ProbComp X := do
  let ω ← ProbComp.unifFin (t - 1)
  slotInverter idx sample f t 1 ω A c

/-! ### The factor-`t` inequality (13.6) -/

/-- The inequality (13.6) of [BonehShoup2023], Lemma 13.5, p. 539, for the typed game and every
typed adversary `A`: `rOWadv[A, f, t] ≤ t · OWadv[B, f]` with `B = plantInverter`. This is not
Lemma 13.5 itself, whose `B` is efficient: `plantInverter` has no efficiency certificate. The
efficient form is `OneWayOn.repeatedInversion_negligible`, with the factor `dyadicSize (t n)` in
place of `t`. -/
theorem succProbability_repeatedInversionExperiment_le (idx : Q → ℕ) (sample : ProbComp X)
    (f : X → X) (t : ℕ) (A : List X → ProbOracleComp (fun _ : Q => X) (Q × X)) :
    Experiment.succProbability (repeatedInversionExperiment idx sample f t A) ≤
      t * Experiment.succProbability
        (inversionExperiment sample f (plantInverter idx sample f t A)) := by
  refine (succProbability_repeatedInversionExperiment_le_sum idx sample f t A).trans ?_
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · have ht' : t - 1 + 1 = t := Nat.sub_add_cancel ht
    have h : ProbComp.eval (inversionExperiment sample f (plantInverter idx sample f t A)) =
        (PMF.uniformOfFintype (Fin (t - 1 + 1))).bind fun ω =>
          ProbComp.eval (inversionExperiment sample f (slotInverter idx sample f t 1 ω A)) := by
      simp only [ProbComp.eval_inversionExperiment, plantInverter, ProbComp.eval_bind,
        ProbComp.eval_unifFin]
      exact inversionExperiment_bind _ _ _ _
    have key : ProbComp.eval (inversionExperiment sample f (plantInverter idx sample f t A)) true =
        (t : ℝ≥0∞)⁻¹ * ∑ g ∈ Finset.range t, ProbComp.eval (inversionExperiment sample f
          (slotInverter idx sample f t 1 g A)) true := by
      rw [h, PMF.bind_apply, tsum_fintype]
      simp only [PMF.uniformOfFintype_apply, Fintype.card_fin]
      rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun g => ProbComp.eval
        (inversionExperiment sample f (slotInverter idx sample f t 1 g A)) true), ht']
    have htop : ∀ g ∈ Finset.range t, ProbComp.eval (inversionExperiment sample f
        (slotInverter idx sample f t 1 g A)) true ≠ ⊤ := fun g _ => PMF.apply_ne_top _ _
    have hsucc : Experiment.succProbability
          (inversionExperiment sample f (plantInverter idx sample f t A)) =
        (t : ℝ≥0)⁻¹ * ∑ g ∈ Finset.range t, Experiment.succProbability
          (inversionExperiment sample f (slotInverter idx sample f t 1 g A)) := by
      change (ProbComp.eval _ true).toNNReal = _
      rw [key, ENNReal.toNNReal_mul, ENNReal.toNNReal_inv, ENNReal.toNNReal_natCast,
        ENNReal.toNNReal_sum htop]
    rw [hsucc, mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr ht.ne')]

end Cslib.Crypto
