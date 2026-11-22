/-
Copyright (c) 2026 Charlie Cruz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Cruz
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.Space
public import CslibFrontier.Computability.Complexity.Classes.Hierarchy.TinyDesc
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.Constructible
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Exponential

/-!
# The almost-everywhere space hierarchy theorem (Lemma 2.5)

Complexitylib's diagonal argument for space (`Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE`)
needs an *eventual* gap: every `c * f n + c` eventually below `G n`. Its proof uses the gap at a
single, arbitrarily large length only, the length of a padded description of the decider. So a
*frequent* gap suffices (`setOf_spaceDiagonal_notMem_DSPACE_of_frequently`): for every `c`, there
are arbitrarily large `n` with `c * f n + c ≤ G n`. The proof below is Complexitylib's
(`CslibFrontier/Computability/Complexity/Classes/Hierarchy/Space.lean`, by Samuel Schlesinger), with
the padding chosen at such a length.

The frequent form is the almost-everywhere hierarchy theorem of the paper (Lemma 2.5, Appendix B)
for the diagonal language `{x | spaceDiagonal G x = true}`:

* `spaceDiagonal_ae_lower_bound`: every deterministic machine deciding this language, within any
  time bound and within a pointwise space bound `space x`, has a constant `C ≥ 1` such that for
  all large `n` some input `x` of length `n` has `G n < C * space x`.

The bound `space x` may be taken to be the number of work cells the machine visits on `x`, so the
machine visits more than `G n / C` cells on some input of each large length, as in Lemma 2.5.

Differences from the paper's Lemma 2.5: its hypothesis `S(n) ≥ n` appears as `n ≤ G n`
(Complexitylib's diagonal holds its input, see `Cslib.Complexity.DSPACE_ssubset_DSPACE`), and the
machine model is Complexitylib's deterministic multitape machine computing the indicator, with the
work-space measure of `Turing.MultiTapeTM.RunsInSpace`.

## Main results

* `setOf_spaceDiagonal_notMem_DSPACE_of_frequently`: the diagonal argument with a frequent gap.
* `spaceDiagonal_ae_lower_bound`: Lemma 2.5 for a single machine.
-/

@[expose] public section

namespace Cslib.Complexity.NtimeDspace.Cross

open Cslib Cslib.Complexity _root_.Turing _root_.Turing.MultiTapeTM
    _root_.Turing.MultiTapeTM.Universal Filter

/-- Eventually, `n + 1` has at most `n / 4` binary digits (as in Complexitylib's proof). -/
theorem eventually_four_mul_length_encNat_le :
    ∀ᶠ n in atTop, 4 * (encNat (n + 1)).length ≤ n := by
  obtain ⟨C, hC⟩ := exists_pow_length_encNat_le 2
  filter_upwards [eventually_ge_atTop (100 * (C + 1))] with n hn
  have h₁ := hC (n + 1)
  by_contra hlt
  have h₂ : (n + 1) ^ 2 ≤ 16 * ((encNat (n + 1)).length + 1) ^ 2 := by
    rw [show 16 * ((encNat (n + 1)).length + 1) ^ 2 = (4 * ((encNat (n + 1)).length + 1)) ^ 2 by
      ring]
    exact Nat.pow_le_pow_left (by omega) 2
  have h₃ : 100 * (C + 1) * (n + 1) ≤ (n + 1) ^ 2 := by
    rw [sq]; exact Nat.mul_le_mul_right _ (by omega)
  nlinarith

open Diagonal in
/-- **The diagonal argument for space, with a frequent gap.** If for every `c` there are
arbitrarily large `n` with `c * f n + c ≤ G n`, and `n ≤ G n`, the problem of the diagonal within
space `G` is not in `DSPACE f`. This is `Cslib.Complexity.setOf_spaceDiagonal_notMem_DSPACE` with
the eventual gap weakened to a frequent one; the proof is the same, padding the description of the
decider to a length at which the gap holds. -/
theorem setOf_spaceDiagonal_notMem_DSPACE_of_frequently {f G : ℕ → ℕ} (hn : ∀ n, n ≤ G n)
    (hfG : ∀ c, ∃ᶠ n in atTop, c * f n + c ≤ G n) :
    {x | spaceDiagonal G x = true} ∉ DSPACE encBits f := by
  rintro ⟨c₁, c₂, t, hA⟩
  obtain ⟨g, ⟨k, State, hfinite, tm, htm⟩, hg⟩ := decidableInTimeAndSpace_iff.mp hA
  have := Fintype.ofFinite State
  let eS : State ↪ ℕ := (Fintype.equivFin State).toEmbedding.trans Fin.valEmbedding
  set D := descLen (desc eS eBit tm) with hD
  set P := 6 * (2 * D + 5) * (c₁ + c₂) + 3 * D + 4 with hP
  set e := storageBoundExp Bool k
  set base := storageBoundBase Bool State k
  have hpoly : ∀ᶠ n in atTop, ((n + 2) * base) ^ 2 < 2 ^ n :=
    PolynomiallyBounded.eventually_lt_two_pow (f := fun n => ((n + 2) * base) ^ 2) (by fun_prop)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hpoly.and eventually_four_mul_length_encNat_le)
  -- a length beyond `N`, beyond the description, at which the gap holds
  obtain ⟨n, hnN, hgap⟩ := (hfG (2 * e * (c₁ + c₂) + 2 * P)).forall_exists_of_atTop
    (N + 2 ^ 2 ^ (eDesc (desc eS eBit tm)).length + 2 * (eDesc (desc eS eBit tm)).length + 1)
  have h₁ : 2 * e * (c₁ + c₂) * f n + 2 * e * (c₁ + c₂) ≤ G n := by
    refine le_trans ?_ hgap
    have := Nat.mul_le_mul_right (f n) (Nat.le_add_right (2 * e * (c₁ + c₂)) (2 * P))
    omega
  have h₂ : 2 * P * f n + 2 * P ≤ G n := by
    refine le_trans ?_ hgap
    have := Nat.mul_le_mul_right (f n) (Nat.le_add_left (2 * P) (2 * e * (c₁ + c₂)))
    omega
  set pad := List.replicate (n - (2 * (eDesc (desc eS eBit tm)).length + 1)) false
  have hpow := Nat.one_le_two_pow (n := (eDesc (desc eS eBit tm)).length)
  have hpow₂ := Nat.one_le_two_pow (n := 2 ^ (eDesc (desc eS eBit tm)).length)
  have hlen : (frame (eDesc (desc eS eBit tm)) ++ pad).length =
      2 * (eDesc (desc eS eBit tm)).length + 1 + pad.length := by
    rw [List.length_append, length_frame]
  have hpadlen : pad.length = n - (2 * (eDesc (desc eS eBit tm)).length + 1) :=
    List.length_replicate ..
  have htiny : tinyDesc (frame (eDesc (desc eS eBit tm)) ++ pad) = true := by
    rw [tinyDesc, unframe_frame_append, hlen]
    refine decide_eq_true (Nat.lt_size.mpr ?_).le
    omega
  generalize hx : frame (eDesc (desc eS eBit tm)) ++ pad = x at hlen htiny
  have hxn : x.length = n := by omega
  rw [← hxn] at h₁ h₂
  obtain ⟨h₃, h₄⟩ := hN x.length (by omega)
  have hrun := htm x
  simp only [encBits_apply] at hrun
  set s := c₁ * f x.length + c₂ with hs
  have hsf : s ≤ (c₁ + c₂) * (f x.length + 1) := by rw [hs]; nlinarith
  -- the decider halts within the clock
  have hclock : (x.length + 2) * storageBound Bool State k s ≤ 2 ^ G x.length := by
    have he : 2 * (e * s) ≤ G x.length := by
      have := Nat.mul_le_mul_left (2 * e) hsf
      have e₁ : 2 * e * ((c₁ + c₂) * (f x.length + 1)) =
          2 * e * (c₁ + c₂) * f x.length + 2 * e * (c₁ + c₂) := by ring
      have e₂ : 2 * (e * s) = 2 * e * s := by ring
      omega
    have hsq : ((x.length + 2) * base * 2 ^ (e * s)) ^ 2 ≤ (2 ^ G x.length) ^ 2 := by
      calc ((x.length + 2) * base * 2 ^ (e * s)) ^ 2
          = ((x.length + 2) * base) ^ 2 * 2 ^ (2 * (e * s)) := by ring
        _ ≤ 2 ^ x.length * 2 ^ G x.length :=
          Nat.mul_le_mul h₃.le (Nat.pow_le_pow_right (by norm_num) he)
        _ ≤ 2 ^ G x.length * 2 ^ G x.length :=
          Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (hn _))
        _ = (2 ^ G x.length) ^ 2 := (sq _).symm
    refine le_trans ?_ ((Nat.pow_le_pow_iff_left two_ne_zero).mp hsq)
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul_left _ (storageBound_le_base_mul_pow s)
  obtain ⟨hhalt, hout⟩ := hrun.of_card.runFrom_of_le hclock
  -- the configurations of the simulation fit within the budget
  have hbudget : cfgSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤ G x.length := by
    have hsp : simSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤ s := by
      rw [simSpace_desc]
      exact space_le_of_runsInSpace hrun.2.2 _
    have hk : (desc eS eBit tm).tapes ≤ D := by
      simp only [hD, descLen, eDesc_apply, length_encPair, encUnary_apply, List.length_replicate]
      omega
    have hP' : 6 * (2 * D + 5) * s + 3 * D + 4 ≤ P * (f x.length + 1) := by
      have := Nat.mul_le_mul_left (6 * (2 * D + 5)) hsf
      have e₁ : P * (f x.length + 1) = 6 * (2 * D + 5) * ((c₁ + c₂) * (f x.length + 1)) +
          (3 * D + 4) * (f x.length + 1) := by rw [hP]; ring
      have : 3 * D + 4 ≤ (3 * D + 4) * (f x.length + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega
    have e₂ : 2 * P * f x.length + 2 * P = 2 * (P * (f x.length + 1)) := by ring
    simp only [cfgSpace, List.length_map, ← hD]
    have e₃ : 3 * (2 * D + 5) * 2 * simSpace (desc eS eBit tm) (x.map eBit) (2 ^ G x.length) ≤
        6 * (2 * D + 5) * s := by
      rw [show 3 * (2 * D + 5) * 2 = 6 * (2 * D + 5) by ring]
      exact Nat.mul_le_mul_left _ hsp
    have := hn x.length
    omega
  -- so the diagonal negates the answer of the decider
  have hd : spaceDiagonal G x = !g x := by
    subst hx
    exact spaceDiagonal_desc eS tm pad G htiny hbudget hhalt hout
  have hgx := hg x
  simp only [Set.mem_ofPred_eq, hd] at hgx
  revert hgx
  cases g x <;> decide

/-- The largest value of `space` on the words of length `n`. -/
noncomputable def maxOnLength (space : List Bool → ℕ) (n : ℕ) : ℕ :=
  Finset.univ.sup fun v : List.Vector Bool n => space v.toList

theorem le_maxOnLength (space : List Bool → ℕ) (x : List Bool) :
    space x ≤ maxOnLength space x.length :=
  Finset.le_sup (f := fun v : List.Vector Bool x.length => space v.toList) (b := ⟨x, rfl⟩)
    (Finset.mem_univ _)

theorem exists_eq_maxOnLength (space : List Bool → ℕ) (n : ℕ) :
    ∃ x : List Bool, x.length = n ∧ space x = maxOnLength space n := by
  obtain ⟨v, -, hv⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (List.Vector Bool n))
    Finset.univ_nonempty (fun v : List.Vector Bool n => space v.toList)
  exact ⟨v.toList, v.toList_length, hv.symm⟩

theorem maxOnLength_le {space : List Bool → ℕ} {n B : ℕ}
    (h : ∀ x : List Bool, x.length = n → space x ≤ B) : maxOnLength space n ≤ B :=
  Finset.sup_le fun v _ => h v.toList v.toList_length

/-- **Lemma 2.5 for a single machine** (the almost-everywhere space hierarchy theorem). Let
`n ≤ G n`. Every deterministic machine deciding the diagonal language within space `G`, with any
time bound and any pointwise space bound `space`, has a constant `C ≥ 1` such that, for all large
`n`, some input `x` of length `n` has `G n < C * space x`. -/
theorem spaceDiagonal_ae_lower_bound {G : ℕ → ℕ} (hn : ∀ n, n ≤ G n) {k : ℕ} {State : Type}
    [Finite State] (tm : MultiTapeTM k Bool State) {g : List Bool → Bool}
    {time space : List Bool → ℕ}
    (htm : tm.ComputesFunInTimeAndSpace encBits encBool g time space)
    (hg : ∀ x, spaceDiagonal G x = true ↔ g x = true) :
    ∃ C, 1 ≤ C ∧ ∀ᶠ n in atTop, ∃ x : List Bool, x.length = n ∧ G n < C * space x := by
  have hmem : {x | spaceDiagonal G x = true} ∈ DSPACE encBits (maxOnLength space) := by
    refine mem_DSPACE_iff.mpr ⟨1, 0, time, decidableInTimeAndSpace_iff.mpr ⟨g, ?_, hg⟩⟩
    refine ⟨k, State, inferInstance, tm, htm.mono (fun _ => le_rfl) fun x => ?_⟩
    simp only [encBits_apply, one_mul, add_zero]
    exact le_maxOnLength space x
  have hnot : ¬ ∀ c, ∃ᶠ n in atTop, c * maxOnLength space n + c ≤ G n := fun h =>
    setOf_spaceDiagonal_notMem_DSPACE_of_frequently hn h hmem
  push Not at hnot
  obtain ⟨c, hc⟩ := hnot
  refine ⟨2 * c + 1, by omega, ?_⟩
  filter_upwards [hc, eventually_ge_atTop c] with n hcn hnc
  obtain ⟨x, hx, hxf⟩ := exists_eq_maxOnLength space n
  refine ⟨x, hx, ?_⟩
  have hGn := hn n
  rw [← hxf] at hcn
  rcases Nat.eq_zero_or_pos (space x) with h0 | h0
  · rw [h0] at hcn; omega
  · nlinarith

end Cslib.Complexity.NtimeDspace.Cross
