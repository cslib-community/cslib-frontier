/-
Copyright (c) 2026 Sam McGuire. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam McGuire
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.OriginalCountQuery
public import CslibFrontier.Computability.Complexity.Classes.CountingSimulation.SourceScheduleVerifier

/-!
# Original counting-machine bits from ordinary inputs

The external challenge contains the counting machine's clock. A finite verifier scales it
on its own tapes by the fixed number of binary choices used to encode each transition.
The occurrence-labelled count at the unscaled clock is recovered at the original bit index.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open _root_.Turing _root_.Turing.MultiTapeTM _root_.Turing.MultiTapePTM _root_.Turing.MultiTapeATM
open CarryLookaheadCountingInitialLayout OuterRootLeaf ComputableInPolyTime

namespace ScheduleChallenge

/-- Replace each source transition by its fixed number of binary choice steps. -/
@[expose] def widen (width : ℕ) (p : ScheduleChallenge) : ScheduleChallenge :=
  ⟨p.time * width, p.bit, p.claim⟩

/-- Scaling both short schedule projections is polynomial in the original binary metadata. -/
theorem exists_widen_setup_degree (k states width : ℕ) :
    ∃ d, let T := fun p : ScheduleChallenge => ((enc p).length + 1) ^ d
      ComputableInO (fun p : ScheduleChallenge => outerRootTemplate k states (p.time * width))
        enc RootBalanceRequest.encPublic T T ∧
      ComputableInO (fun p : ScheduleChallenge => scheduleRequest k (p.time * width) p.bit p.claim)
        enc Circuits.Boolean.CarryLookahead.Query.CountingInput.encInput T T := by
  have ht : ComputableInPolyTime ScheduleChallenge.time enc encNat := by fun_prop
  have hm := binary_mul' ht (const width)
  have hw : ComputableInPolyTime (widen width) enc enc := by
    apply enc_mk_polyTime
    · exact hm
    · fun_prop
    · fun_prop
  obtain ⟨a, _, hf⟩ := ((computableInPolyTime_outerRootTemplate k states).comp hm).exists_degree
  obtain ⟨b, _, hg⟩ := ((request_polyTime k).comp hw).exists_degree
  refine ⟨a + b, hf.inO.mono_le ?_ ?_, hg.inO.mono_le ?_ ?_⟩
  all_goals intro p; apply Nat.pow_le_pow_right (by omega); omega

/-- Metadata for the unscaled clock fits the square-root-logarithmic budget even when the
requested bit is above the unscaled time, up to the full binary transition count bound. -/
theorem exists_widen_clock (c d width : ℕ) (hw : 0 < width) :
    ∃ K, ∀ p : ScheduleChallenge, 2 ≤ p.time → p.bit < p.time * width + 1 →
      c * (((enc p).length + 1) ^ d + 1) + 8 ≤
        K * (p.time / (Nat.log 2 (p.time + 2)).sqrt + 2) := by
  obtain ⟨A, hA⟩ := exists_clock c d
  refine ⟨A * width, ?_⟩
  intro p ht hb
  have hmul := Nat.le_mul_of_pos_right p.time hw
  have hlen : (enc p).length ≤ (enc (widen width p)).length := by
    simp only [length_enc, widen]
    have hs := Nat.size_le_size hmul
    omega
  have ha := hA (widen width p) (ht.trans hmul)
    (hb.trans_le (Nat.succ_le_succ (le_paddedTime _)))
  calc
    _ ≤ c * (((enc (widen width p)).length + 1) ^ d + 1) + 8 := by gcongr
    _ ≤ A * (numBlocks (p.time * width) + 1) := ha
    _ ≤ A * (p.time * width / (Nat.log 2 (p.time * width + 2)).sqrt + 2) :=
      Nat.mul_le_mul_left A (Nat.succ_le_succ (numBlocks_le_div_sqrt_log_add_one _))
    _ ≤ _ := by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left A (width_clock_le _ _ hw)

end ScheduleChallenge

/-- A fixed finite table verifier physically constructs the widened clock from the original
challenge. The source word stays available on the read-only tape throughout preparation. -/
private theorem exists_widened_verifier (k states width : ℕ) (hw : 0 < width)
    {K : ℕ} {R : Type} [Finite R] (i j : Fin K) (hij : i ≠ j) (right : MultiTapeATM K Bool R) :
    ∃ (u : ℕ) (src : Fin u) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C t₀ : ℕ),
      ∀ {State : Type} [Finite State] (M : MultiTapePTM k Bool State) (st : State ≃ Fin states)
        (input : List Bool) {t : ℕ}, t₀ ≤ t → ∀ budget,
        ChecksSeededContractions i j right M st input (t * width) budget →
        ∀ (bit : Fin (t * width + 1)) (claim : Bool),
        let p : ScheduleChallenge := ⟨t, bit.val, claim⟩
        let start := SharedWordFork.start src atm input (ScheduleChallenge.enc p) 0
        let time := C * (t / (Nat.log 2 (t + 2)).sqrt + 2) + budget
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (M.acceptCount input (paddedTime (t * width))).testBit bit.val = claim) := by
  obtain ⟨scratch, a, r, q, S, hS, eval, C, t₀, he⟩ :=
    exists_short_count_verifier k states i j hij right
  let := hS
  obtain ⟨d, hf, hg⟩ := ScheduleChallenge.exists_widen_setup_degree k states width
  obtain ⟨u, src, Q, hQ, atm, c, h⟩ :=
    RootPackingBalance.TerminalLayout.exists_load_from hf hg _ _
      (ScheduleCountPrepare.context_ne_request scratch a r q) eval
  obtain ⟨B, hB⟩ := ScheduleChallenge.exists_widen_clock c d width hw
  refine ⟨u, src, Q, hQ, atm, B + C * width, max 2 t₀, ?_⟩
  intro State _ M st input t ht budget hseed bit claim p start time
  have ht' := (Nat.le_max_right 2 t₀).trans (ht.trans (Nat.le_mul_of_pos_right t hw))
  let index : Fin (paddedTime (t * width) + 1) :=
    ⟨bit.val, bit.isLt.trans_le (Nat.succ_le_succ (le_paddedTime _))⟩
  let eTime := C * (t * width / (Nat.log 2 (t * width + 2)).sqrt + 2) + budget
  obtain ⟨hh, ha⟩ := he M st input ht' budget hseed index claim
  have hs := h input p 0 (Nat.zero_le _) eTime
  dsimp only at hs
  rw [ScheduleCountPrepare.ready_eq_initial] at hs
  obtain ⟨hh₁, ha₁⟩ := hs hh
  have hb := hB p ((Nat.le_max_left _ _).trans ht) bit.isLt
  have hc := Nat.mul_le_mul_left C (width_clock_le t width hw)
  rw [← Nat.mul_assoc] at hc
  have hclock : 0 + c * (((ScheduleChallenge.enc p).length + 1) ^ d + 1) + 8 + eTime ≤ time := by
    dsimp only [time, eTime]
    rw [Nat.add_mul]
    change _ ≤ B * (t / (Nat.log 2 (t + 2)).sqrt + 2) at hb
    omega
  exact ⟨hh₁.mono hclock, ⟨fun h' => ha.mp (ha₁.mp (h'.of_halted_stepCoins hh₁)),
    fun h' => (ha₁.mpr (ha.mpr h')).mono hclock⟩⟩

/-- For every finite occurrence-labelled counting machine choose its binary table once.
Given a seeded contraction continuation, a finite ATM on the ordinary input consisting of
the original clock, bit, sign and source word recovers the original terminal count bit. -/
theorem exists_original_machine_verifier {k : ℕ} {S : Type} [Finite S] (M : MultiTapeCTM k Bool S) :
    ∃ (width states : ℕ) (P : Type) (_ : Finite P) (table : MultiTapePTM k Bool P)
      (st : P ≃ Fin states), 0 < width ∧
      ∀ {K : ℕ} {R : Type} [Finite R] (i j : Fin K), i ≠ j → ∀ right : MultiTapeATM K Bool R,
      ∃ (u : ℕ) (Q : Type) (_ : Finite Q) (atm : MultiTapeATM u Bool Q) (C t₀ : ℕ),
      ∀ (input : List Bool) {t : ℕ}, t₀ ≤ t → M.HaltsWithin t (Cfg.init M.initial input) →
        ∀ budget, ChecksSeededContractions i j right table st input (t * width) budget →
        ∀ (bit : Fin (t * width + 1)) (claim : Bool),
        let p : ScheduleChallenge := ⟨t, bit.val, claim⟩
        let start := atm.toPTM.toNTM.initCfg (encPair ScheduleChallenge.enc encBits (p, input))
        let time := C * (input.length + (t / (Nat.log 2 (t + 2)).sqrt + 2)) + budget
        atm.HaltsWithin time start ∧ (atm.AcceptsWithin time start ↔
          (M.acceptCount t (Cfg.init M.initial input)).testBit bit.val = claim) := by
  obtain ⟨width, states, P, hP, table, st, hw, hcount⟩ := exists_original_count_table M
  let := hP
  refine ⟨width, states, P, hP, table, st, hw, ?_⟩
  intro K R _ i j hij right
  obtain ⟨v, src, S, hS, child, A, t₀, hv⟩ :=
    exists_widened_verifier k states width hw i j hij right
  let := hS
  obtain ⟨u, Q, hQ, atm, c, h⟩ := SourceWordInput.exists_prepend ScheduleChallenge.enc src child
  obtain ⟨G, hG⟩ := ScheduleChallenge.exists_widen_clock 1 1 width hw
  refine ⟨u, Q, hQ, atm, c + c * G + A, max 2 t₀, ?_⟩
  intro input t ht halted budget hseed bit claim p start time
  let m := t / (Nat.log 2 (t + 2)).sqrt + 2
  let ct := A * m + budget
  obtain ⟨hh, ha⟩ := hv table st input ((Nat.le_max_right _ _).trans ht) budget hseed bit claim
  obtain ⟨hh₁, ha₁⟩ := h p input ct hh
  have hx := hG p ((Nat.le_max_left _ _).trans ht) bit.isLt
  change 1 * (((ScheduleChallenge.enc p).length + 1) ^ 1 + 1) + 8 ≤ G * m at hx
  simp only [one_mul, pow_one] at hx
  have hlen : (ScheduleChallenge.enc p).length + 1 ≤ G * m := by omega
  have hc : c * (input.length + (ScheduleChallenge.enc p).length + 1) + ct ≤ time := by
    let N := c + c * G + A
    have h₁ : c * input.length ≤ N * input.length :=
      Nat.mul_le_mul_right _ (by dsimp [N]; omega)
    have h₂ : (c * G + A) * m ≤ N * m := Nat.mul_le_mul_right _ (by dsimp [N]; omega)
    calc
      _ ≤ c * (input.length + G * m) + ct := by rw [Nat.add_assoc]; gcongr
      _ = c * input.length + (c * G + A) * m + budget := by dsimp only [ct]; ring
      _ ≤ N * (input.length + m) + budget := by
        rw [Nat.mul_add N input.length m]
        exact Nat.add_le_add_right (Nat.add_le_add h₁ h₂) _
  rw [hcount input t bit.val halted] at ha
  exact ⟨hh₁.mono hc, ⟨fun h' => ha.mp (ha₁.mp (h'.of_halted_stepCoins hh₁)),
    fun h' => (ha₁.mpr (ha.mpr h')).mono hc⟩⟩

end Cslib.Complexity.CountingSimulation
