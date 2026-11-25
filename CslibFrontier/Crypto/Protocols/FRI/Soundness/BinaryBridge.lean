/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.BinaryDefs
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.SmoothEscape
import CslibFrontier.Foundations.Data.Hamming

/-!
# Binary-to-Smooth FRI Bridges and Transcript/Counting/Unique-Decoding Corollaries

Establishes exact equivalences between binary `FRIParams` state, doomed/good-step predicates,
commit games, and line proximity-gap contracts and their smooth `FRISmoothParams` counterparts at
`params.toSmooth`, together with binary transcript-update, weight-bound, starting-point counting,
and unique-decoding line-gap upgrade corollaries.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

section BinaryTranscriptAndBridges

variable {F : Type} [Field F]

private theorem sum_filter_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (P : α → Prop) [DecidablePred P] (Q : β → Prop) [DecidablePred Q]
    (w₁ : α → ℕ) (w₂ : β → ℕ)
    (hP : ∀ a, P a ↔ Q (e a)) (hw : ∀ a, w₁ a = w₂ (e a)) :
    (∑ a ∈ Finset.univ.filter P, w₁ a) = ∑ b ∈ Finset.univ.filter Q, w₂ b := by
  simp only [Finset.sum_filter]
  exact (Finset.sum_congr rfl fun a _ => by simp only [hP a, hw a]).trans
    (Equiv.sum_comp e fun b => if Q b then w₂ b else 0)

/-- Equivalence between `Fin (params.arity i * params.domainSize (i.val + 1))` and
`Fin (params.domainSize i.val)` for a smooth folding round `i : Fin params.m`. -/
private abbrev FRISmoothParams.fiberDomainEquiv (params : FRISmoothParams F) (i : Fin params.m) :
    Fin (params.arity i * params.domainSize (i.val + 1)) ≃ Fin (params.domainSize i.val) :=
  finCongr (params.domainSize_eq_arity_mul_succ i).symm

/-! #### Binary-to-Smooth State and Game Bridges -/

private def toSmoothDomEquiv (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m) :
    Fin (2 ^ (params.d - i)) ≃ Fin (params.toSmooth.domainSize i) :=
  finCongr (by rw [params.toSmooth_domainSize hi])

private theorem toSmoothDomEquiv_val (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m)
    (j : Fin (2 ^ (params.d - i))) :
    (toSmoothDomEquiv params hi j).val = j.val :=
  rfl

private theorem mem_rsCode_iff_toSmooth (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m)
    (v : Fin (2 ^ (params.d - i)) → F) :
    v ∈ params.rsCode i ↔ (v ∘ (toSmoothDomEquiv params hi).symm) ∈ params.toSmooth.rsCode i := by
  have heval (p : Polynomial F) :
      (fun j => p.eval (params.eval i j)) = v ↔
        (fun y => p.eval (params.toSmooth.eval i y)) = v ∘ (toSmoothDomEquiv params hi).symm := by
    have hpt (j) : params.toSmooth.eval i (toSmoothDomEquiv params hi j) = params.eval i j := by
      simp [FRISmoothParams.eval, FRIParams.eval, cosetEval, cosetPoint,
        params.toSmooth_cumLog hi, toSmoothDomEquiv_val]
    exact ⟨fun h => funext fun y => by
        rw [Function.comp_apply, ← congrFun h ((toSmoothDomEquiv params hi).symm y), ← hpt,
          Equiv.apply_symm_apply],
      fun h => funext fun j => by
        have := congrFun h (toSmoothDomEquiv params hi j)
        simpa only [Function.comp_apply, Equiv.symm_apply_apply, hpt] using this⟩
  simp only [FRIParams.rsCode, FRISmoothParams.rsCode, mem_reedSolomon, params.toSmooth_dim hi,
    heval]

private theorem mem_rsCode_comp_toSmooth (params : FRIParams F) {i : ℕ} (hi : i ≤ params.m)
    (v : Fin (params.toSmooth.domainSize i) → F) :
    (v ∘ toSmoothDomEquiv params hi) ∈ params.rsCode i ↔ v ∈ params.toSmooth.rsCode i := by
  rw [mem_rsCode_iff_toSmooth params hi]
  simp [Function.comp_assoc]

private theorem friTargetWord_apply_eq_smooth (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))) :
    friTargetWord params stmt pref i hi j =
      friSmoothTargetWord params.toSmooth stmt pref i hi (toSmoothDomEquiv params hi j) := by
  cases i with
  | zero => rfl
  | succ k =>
    have hkm : k < params.m := Nat.lt_of_succ_le hi
    let s : Fin (2 ^ params.d) := ⟨j.val, lt_of_lt_of_le j.isLt
      (Nat.pow_le_pow_right (by omega) (Nat.sub_le _ _))⟩
    have hdom := params.toSmooth_domainSize hi
    have hfin : toSmoothDomEquiv params hi j = friSmoothFoldedFin params.toSmooth ⟨k, hkm⟩ s :=
      Fin.ext (Nat.mod_eq_of_lt
        (show s.val < params.toSmooth.domainSize (k + 1) by simpa only [hdom] using j.isLt)).symm
    simp only [friTargetWord, friSmoothTargetWord, foldWord_apply_eq_foldFiber]
    rw [hfin, foldFiber_toSmooth_eq_fold2Fiber params ⟨k, hkm⟩ _ s (prefFoldScalar pref k)]
    change fold2Fiber _ _ _ _ = fold2Fiber _ _ _ _
    have h0 : j.val = s.val % 2 ^ (params.d - (k + 1)) := (Nat.mod_eq_of_lt j.isLt).symm
    congr 1
    · exact congrArg (prefOracle pref k) (Fin.ext (by
        simp [reindexDouble, fiberIdx, friSmoothFoldedFin, hdom, h0]))
    · exact congrArg (prefOracle pref k) (Fin.ext (by
        simp [reindexDouble, fiberIdx, friSmoothFoldedFin, hdom, h0]))
    · simp [FRIParams.eval, cosetEval, cosetPoint, friRoundPosFin, h0]

private theorem pushWeight_toSmooth_eq_add (params : FRIParams F) {k : ℕ} (hkm : k < params.m)
    (f : Fin (2 ^ (params.d - k)) → ℕ)
    (g : Fin (params.toSmooth.domainSize k) → ℕ)
    (hfg : ∀ y, f y = g (toSmoothDomEquiv params hkm.le y))
    (j : Fin (2 ^ (params.d - (k + 1)))) :
    let hkd : k < params.d := lt_of_lt_of_le hkm params.hm
    f (reindexDouble hkd ⟨j.val, by omega⟩) +
        f (reindexDouble hkd ⟨j.val + 2 ^ (params.d - (k + 1)), by omega⟩) =
      pushWeight (a := params.toSmooth.arity ⟨k, hkm⟩)
        (fun idx => g (params.toSmooth.fiberDomainEquiv ⟨k, hkm⟩ idx))
        (toSmoothDomEquiv params hkm j) := by
  have hdom1 : params.toSmooth.domainSize (k + 1) = 2 ^ (params.d - (k + 1)) :=
    params.toSmooth_domainSize hkm
  simp only [pushWeight, hfg]
  change _ = ∑ t : Fin 2, _
  rw [Fin.sum_univ_two]
  congr 1 <;> exact congrArg g (Fin.ext (by
    simp [toSmoothDomEquiv, FRISmoothParams.fiberDomainEquiv, reindexDouble, fiberIdx, hdom1]))

private theorem friPreWeight_apply_eq_smooth [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))),
      friPreWeight params stmt pref i hi j =
        friSmoothPreWeight params.toSmooth stmt pref i hi (toSmoothDomEquiv params hi j)
  | 0, _, _ => rfl
  | k + 1, hi, j => by
    have hkm : k < params.m := Nat.lt_of_succ_le hi
    simp only [friPreWeight, friSmoothPreWeight]
    refine pushWeight_toSmooth_eq_add params hkm
      (fun y => if restrictOracle (i := k) (prefOracle pref k) y =
          friTargetWord params stmt pref k hkm.le y then
        friPreWeight params stmt pref k hkm.le y else 0)
      (fun y => if restrictOracle (i := params.toSmooth.cumLog k) (prefOracle pref k) y =
          friSmoothTargetWord params.toSmooth stmt pref k hkm.le y then
        friSmoothPreWeight params.toSmooth stmt pref k hkm.le y else 0)
      (fun y => ?_) j
    simp only [friPreWeight_apply_eq_smooth params stmt pref k hkm.le y,
      friTargetWord_apply_eq_smooth params stmt pref k hkm.le y]
    rfl

private theorem friOracleFilterWeight_apply_eq_smooth [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F) (j : Fin (2 ^ (params.d - i))) :
    friOracleFilterWeight params stmt pref i hi π j =
      friSmoothOracleFilterWeight params.toSmooth stmt pref i hi π
        (toSmoothDomEquiv params hi j) := by
  simp only [friOracleFilterWeight, friSmoothOracleFilterWeight,
    friTargetWord_apply_eq_smooth params stmt pref i hi j,
    friPreWeight_apply_eq_smooth params stmt pref i hi j]
  rfl

private theorem friNextWeight_apply_eq_smooth [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) :
    friNextWeight params stmt pref i hi π j =
      friSmoothNextWeight params.toSmooth stmt pref i hi π (toSmoothDomEquiv params hi j) :=
  pushWeight_toSmooth_eq_add params hi _ _
    (friOracleFilterWeight_apply_eq_smooth params stmt pref i hi.le π) j

private theorem friSmoothFinal_toSmooth_eq (params : FRIParams F)
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friSmoothFinalIdx params.toSmooth s = friFinalIdx params s ∧
    friSmoothFinalCodeword params.toSmooth πFinal (friSmoothFinalFin params.toSmooth s) =
      friFinalCodeword params πFinal (friFinalFin params s) :=
  ⟨friSmoothFinalIdx_toSmooth params s, by
    simp only [friSmoothFinalCodeword, friFinalCodeword, params.toSmooth_finalAnchorPoints,
      eval_toSmooth_final]⟩

private theorem friPrefixPasses_iff_smooth (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (s : Fin (2 ^ params.d)) :
    friPrefixPasses params stmt pref i s ↔
      friSmoothPrefixPasses params.toSmooth stmt pref i s := by
  simp only [friPrefixPasses, friSmoothPrefixPasses]
  refine and_congr_right fun _ => forall_congr' fun k => imp_congr_right fun _ => ?_
  rw [foldFiber_toSmooth_eq_fold2Fiber, friSmoothFiberIdx_toSmooth_zero,
    friSmoothFiberIdx_toSmooth_one, friSmoothFoldedIdx_toSmooth]

private theorem friTranscriptSingleAccepts_iff_smooth (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt pref s ↔
      friSmoothTranscriptSingleAccepts params.toSmooth stmt pref s := by
  obtain ⟨hidx, hcw⟩ := friSmoothFinal_toSmooth_eq params (prefOracle pref params.m) s
  simp only [friTranscriptSingleAccepts, friSmoothTranscriptSingleAccepts,
    friPrefixPasses_iff_smooth, hidx, hcw]

/-- Exact equivalence between binary `friFinalPasses` and smooth `friSmoothFinalPasses` at
`params.toSmooth`. -/
theorem friFinalPasses_iff_friSmoothFinalPasses (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F) (s : Fin (2 ^ params.d)) :
    friFinalPasses params stmt pref πFinal s ↔
      friSmoothFinalPasses params.toSmooth stmt pref πFinal s := by
  obtain ⟨hidx, hcw⟩ := friSmoothFinal_toSmooth_eq params πFinal s
  simp only [friFinalPasses, friSmoothFinalPasses, hidx, hcw]
  refine and_congr_right fun _ => and_congr_left fun _ => forall_congr' fun k => ?_
  rw [foldFiber_toSmooth_eq_fold2Fiber, friSmoothFiberIdx_toSmooth_zero,
    friSmoothFiberIdx_toSmooth_one, friSmoothFoldedIdx_toSmooth]

private theorem filter_friFinalPasses_eq (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (πFinal : OracleTable params.d F)
    [DecidablePred (friFinalPasses params stmt pref πFinal)]
    [DecidablePred (friSmoothFinalPasses params.toSmooth stmt pref πFinal)] :
    (Finset.univ.filter fun s => friFinalPasses params stmt pref πFinal s) =
      Finset.univ.filter fun s => friSmoothFinalPasses params.toSmooth stmt pref πFinal s := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, friFinalPasses_iff_friSmoothFinalPasses]

private theorem friCommitDoomed_iff_smooth [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) :
    friCommitDoomed params B stmt pref i hi ↔
      friSmoothCommitDoomed params.toSmooth B stmt pref i hi := by
  let e := toSmoothDomEquiv params hi
  have hsum (c' : Fin (params.toSmooth.domainSize i) → F) :
      (∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = (c' ∘ e) j),
        friPreWeight params stmt pref i hi j) =
      ∑ y ∈ Finset.univ.filter (fun y =>
          friSmoothTargetWord params.toSmooth stmt pref i hi y = c' y),
        friSmoothPreWeight params.toSmooth stmt pref i hi y :=
    sum_filter_equiv e _ _ _ _
      (fun j => by rw [friTargetWord_apply_eq_smooth, Function.comp_apply])
      (friPreWeight_apply_eq_smooth params stmt pref i hi)
  exact ⟨fun h c' hc' => hsum c' ▸ h (c' ∘ e) ((mem_rsCode_comp_toSmooth params hi c').mpr hc'),
    fun h c hc => by
      have heq := hsum (c ∘ e.symm)
      simp only [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id] at heq
      exact heq.trans_le (h (c ∘ e.symm) ((mem_rsCode_iff_toSmooth params hi c).mp hc))⟩

/-- Exact equivalence between binary `friDoomed` and smooth `friSmoothDoomed` at `params.toSmooth`.
-/
theorem friDoomed_iff_friSmoothDoomed [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    friDoomed params B stmt pref ↔ friSmoothDoomed params.toSmooth B stmt pref := by
  unfold friDoomed friSmoothDoomed
  split_ifs with h1 h2
  · exact friCommitDoomed_iff_smooth params B stmt pref pref.length h1
  · exact exists_congr fun a =>
      not_congr (friTranscriptSingleAccepts_iff_smooth params stmt pref
        (prefQueryIdxs pref params.m a))
  · exact Iff.rfl

/-- Exact equivalence between binary `friGoodStep` and smooth `friSmoothGoodStep` at
`params.toSmooth`. -/
theorem friGoodStep_iff_friSmoothGoodStep [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (π : OracleTable params.d F) (c : FRIChal F params.d params.q) :
    friGoodStep params B stmt pref π c ↔ friSmoothGoodStep params.toSmooth B stmt pref π c := by
  unfold friGoodStep friSmoothGoodStep
  split_ifs
  · exact friDoomed_iff_friSmoothDoomed params B stmt (pref ++ [(π, c)])
  · exact Iff.rfl


/-- Exact equality between binary `friCommitGame` and smooth `friSmoothCommitGame` at
`params.toSmooth`. -/
theorem friCommitGame_eq_friSmoothCommitGame [Fintype F] (params : FRIParams F) (B : ℕ)
    (stmt : OracleTable params.d F)
    (P : InteractiveIOPProver params.d F (FRIChal F params.d params.q)) :
    friCommitGame params B stmt P = friSmoothCommitGame params.toSmooth B stmt P := by
  simp only [friCommitGame, friSmoothCommitGame]
  congr 1; funext pref; congr 1; funext πFinal
  rw [@filter_friFinalPasses_eq F _ params stmt pref πFinal
    (Classical.decPred _) (Classical.decPred _)]

/-! #### Binary-to-Smooth Line/Curve Proximity-Gap Bridges -/

private theorem forall_fin_toSmooth_arity_iff (params : FRIParams F) (i : Fin params.m)
    (P : Fin (params.toSmooth.arity i) → Prop) :
    (∀ r : Fin (params.toSmooth.arity i), P r) ↔ P ⟨0, by simp⟩ ∧ P ⟨1, by simp⟩ :=
  ⟨fun h => ⟨h _, h _⟩, fun ⟨h0, h1⟩ r => by
    have : r.val < 2 := by simpa only [params.toSmooth_arity i] using r.isLt
    rcases (by omega : r.val = 0 ∨ r.val = 1) with hr | hr
    · exact (Fin.ext hr : r = ⟨0, by simp⟩) ▸ h0
    · exact (Fin.ext hr : r = ⟨1, by simp⟩) ▸ h1⟩

private theorem curveSum_toSmooth_eq_line {α : Type*} (params : FRIParams F) (i : Fin params.m)
    (u : Fin (params.toSmooth.arity i) → α → F) (z : F) :
    (∑ r : Fin (params.toSmooth.arity i), z ^ r.val • u r) =
      u ⟨0, by simp⟩ + z • u ⟨1, by simp⟩ := by
  change (∑ r : Fin 2, z ^ r.val • u ⟨r.val, by simp [r.isLt]⟩) = _
  simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul]

private def toSmoothPair (params : FRIParams F) (i : Fin params.m)
    (v₀ v₁ : Fin (2 ^ (params.d - (i.val + 1))) → F) :
    Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F :=
  fun r => if r.val = 0 then v₀ ∘ (toSmoothDomEquiv params i.isLt).symm
    else v₁ ∘ (toSmoothDomEquiv params i.isLt).symm

private theorem toSmoothPair_mem_rsCode (params : FRIParams F) (i : Fin params.m)
    {v₀ v₁ : Fin (2 ^ (params.d - (i.val + 1))) → F}
    (hv₀ : v₀ ∈ params.rsCode (i.val + 1)) (hv₁ : v₁ ∈ params.rsCode (i.val + 1))
    (r : Fin (params.toSmooth.arity i)) :
    toSmoothPair params i v₀ v₁ r ∈ params.toSmooth.rsCode (i.val + 1) := by
  dsimp only [toSmoothPair]; split_ifs
  · exact (mem_rsCode_iff_toSmooth params i.isLt v₀).mp hv₀
  · exact (mem_rsCode_iff_toSmooth params i.isLt v₁).mp hv₁

/-- Symmetric round-`i` equivalence between binary line weights/words `(W, u₀, u₁)` and
smooth degree-1 curve weights/words `(W', u)` matched along `e := toSmoothDomEquiv params i.isLt`.
Used in both directions of `weightedLineGapPerRound_iff_weightedCurveGapPerRound` and
`weightedLineEscapePerRound_iff_weightedCurveEscapePerRound`. -/
private theorem lineCurveRound_iff [DecidableEq F] (params : FRIParams F)
    (i : Fin params.m) (B : ℕ)
    (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ)
    (W' : Fin (params.toSmooth.domainSize (i.val + 1)) → ℕ)
    (hW : ∀ j, W j = W' (toSmoothDomEquiv params i.isLt j))
    (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F)
    (u : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F)
    (hu₀ : ∀ j, u₀ j = u ⟨0, by simp⟩ (toSmoothDomEquiv params i.isLt j))
    (hu₁ : ∀ j, u₁ j = u ⟨1, by simp⟩ (toSmoothDomEquiv params i.isLt j)) :
    ((∀ j, W j ≤ 2 ^ (i.val + 1)) ↔
        ∀ y, W' y ≤ 2 ^ params.toSmooth.cumLog (i.val + 1)) ∧
    ((∑ j, W j) = ∑ y, W' y) ∧
    ((∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
        (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) ↔
      (∀ v : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F,
        (∀ r, v r ∈ params.toSmooth.rsCode (i.val + 1)) →
        (∑ y ∈ Finset.univ.filter (fun y => ∀ r, u r y = v r y), W' y) ≤ B)) ∧
    ({z : F | ∃ v ∈ params.rsCode (i.val + 1),
        B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j} =
      {z : F | ∃ v ∈ params.toSmooth.rsCode (i.val + 1),
        B < ∑ y ∈ Finset.univ.filter
          (fun y => (∑ r : Fin (params.toSmooth.arity i), z ^ r.val • u r) y = v y), W' y}) := by
  let e := toSmoothDomEquiv params i.isLt
  have hsum_pair (v : Fin (params.toSmooth.arity i) →
      Fin (params.toSmooth.domainSize (i.val + 1)) → F) :
      (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v ⟨0, by simp⟩ (e j) ∧
          u₁ j = v ⟨1, by simp⟩ (e j)), W j) =
        ∑ y ∈ Finset.univ.filter (fun y => ∀ r, u r y = v r y), W' y :=
    sum_filter_equiv e _ _ _ _ (fun j => by
      rw [forall_fin_toSmooth_arity_iff params i, hu₀ j, hu₁ j]) hW
  have hsum_comb (z : F) (v : Fin (params.toSmooth.domainSize (i.val + 1)) → F) :
      (∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = (v ∘ e) j), W j) =
        ∑ y ∈ Finset.univ.filter
          (fun y => (∑ r : Fin (params.toSmooth.arity i), z ^ r.val • u r) y = v y), W' y :=
    sum_filter_equiv e _ _ _ _ (fun j => by
      rw [curveSum_toSmooth_eq_line, Function.comp_apply]
      simp [e, hu₀ j, hu₁ j]) hW
  refine ⟨by rw [params.toSmooth_cumLog i.isLt]; exact
      ⟨fun h y => by rw [← e.apply_symm_apply y, ← hW]; exact h (e.symm y),
        fun h j => by rw [hW]; exact h (e j)⟩,
    (Finset.sum_congr rfl fun j _ => hW j).trans (Equiv.sum_comp e W'), ⟨?_, ?_⟩, ?_⟩
  · intro hline v hv
    exact (hsum_pair v) ▸ hline (v ⟨0, by simp⟩ ∘ e)
      ((mem_rsCode_comp_toSmooth params i.isLt _).mpr (hv _))
      (v ⟨1, by simp⟩ ∘ e) ((mem_rsCode_comp_toSmooth params i.isLt _).mpr (hv _))
  · intro hcurve v₀ hv₀ v₁ hv₁
    have hpair := hsum_pair (toSmoothPair params i v₀ v₁)
    simp only [toSmoothPair, ↓reduceIte, Nat.one_ne_zero, Function.comp_apply, e,
      Equiv.symm_apply_apply] at hpair
    exact hpair.trans_le (hcurve _ (toSmoothPair_mem_rsCode params i hv₀ hv₁))
  · ext z
    refine ⟨fun ⟨v, hv, hlt⟩ => ⟨v ∘ e.symm, (mem_rsCode_iff_toSmooth params i.isLt v).mp hv,
        (by simpa [Function.comp_assoc] using hsum_comb z (v ∘ e.symm)) ▸ hlt⟩,
      fun ⟨v, hv, hlt⟩ => ⟨v ∘ e, (mem_rsCode_comp_toSmooth params i.isLt v).mpr hv,
        hsum_comb z v ▸ hlt⟩⟩

private theorem weightedLine_iff_weightedCurve [DecidableEq F] (params : FRIParams F) (B : ℕ)
    (P : Fin params.m → Set F → Prop) :
    (∀ (i : Fin params.m) (W : Fin (2 ^ (params.d - (i.val + 1))) → ℕ),
      (∀ j, W j ≤ 2 ^ (i.val + 1)) → (∑ j, W j ≤ 2 ^ params.d) →
      ∀ (u₀ u₁ : Fin (2 ^ (params.d - (i.val + 1))) → F),
        (∀ v₀ ∈ params.rsCode (i.val + 1), ∀ v₁ ∈ params.rsCode (i.val + 1),
          (∑ j ∈ Finset.univ.filter (fun j => u₀ j = v₀ j ∧ u₁ j = v₁ j), W j) ≤ B) →
        P i {z : F | ∃ v ∈ params.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter (fun j => (u₀ + z • u₁) j = v j), W j}) ↔
    (∀ (i : Fin params.m) (W : Fin (params.toSmooth.domainSize (i.val + 1)) → ℕ),
      (∀ j, W j ≤ 2 ^ params.toSmooth.cumLog (i.val + 1)) → (∑ j, W j ≤ 2 ^ params.d) →
      ∀ (u : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F),
        (∀ v : Fin (params.toSmooth.arity i) → Fin (params.toSmooth.domainSize (i.val + 1)) → F,
          (∀ r, v r ∈ params.toSmooth.rsCode (i.val + 1)) →
          (∑ j ∈ Finset.univ.filter (fun j => ∀ r, u r j = v r j), W j) ≤ B) →
        P i {z : F | ∃ v ∈ params.toSmooth.rsCode (i.val + 1),
          B < ∑ j ∈ Finset.univ.filter
            (fun j => (∑ r : Fin (params.toSmooth.arity i), z ^ r.val • u r) j = v j), W j}) := by
  refine ⟨fun h i W hW_le hW_sum u hno => ?_, fun h i W hW_le hW_sum u₀ u₁ hno => ?_⟩
  · have ⟨h1, h2, h3, h4⟩ := lineCurveRound_iff params i B
      (W ∘ toSmoothDomEquiv params i.isLt) W (fun _ => rfl)
      (u ⟨0, by simp⟩ ∘ toSmoothDomEquiv params i.isLt)
      (u ⟨1, by simp⟩ ∘ toSmoothDomEquiv params i.isLt) u (fun _ => rfl) (fun _ => rfl)
    exact h4 ▸ h i _ (h1.mpr hW_le) (h2.symm ▸ hW_sum) _ _ (h3.mpr hno)
  · have ⟨h1, h2, h3, h4⟩ := lineCurveRound_iff params i B W
      (W ∘ (toSmoothDomEquiv params i.isLt).symm) (fun j => by simp)
      u₀ u₁ (toSmoothPair params i u₀ u₁) (fun j => by simp [toSmoothPair])
      (fun j => by simp [toSmoothPair])
    exact h4.symm ▸ h i _ (h1.mp hW_le) (h2 ▸ hW_sum) _ (h3.mp hno)

/-- Exact equivalence between binary `WeightedLineGapPerRound` and smooth
`WeightedCurveGapPerRound` at `params.toSmooth`. -/
theorem weightedLineGapPerRound_iff_weightedCurveGapPerRound [DecidableEq F]
    (params : FRIParams F) (B : ℕ) (B_commit : Fin params.m → ℕ) :
    WeightedLineGapPerRound params B B_commit ↔
      WeightedCurveGapPerRound params.toSmooth B B_commit :=
  weightedLine_iff_weightedCurve params B fun i S => ∀ Z : Finset F, (∀ z ∈ Z, z ∈ S) →
    Z.card ≤ B_commit i

/-- Exact equivalence between binary `WeightedLineEscapePerRound` and smooth
`WeightedCurveEscapePerRound` at `params.toSmooth`. -/
theorem weightedLineEscapePerRound_iff_weightedCurveEscapePerRound [Fintype F] [DecidableEq F]
    (params : FRIParams F) (B : ℕ) (ε_commit : Fin params.m → ℝ≥0∞) :
    WeightedLineEscapePerRound params B ε_commit ↔
      WeightedCurveEscapePerRound params.toSmooth B ε_commit :=
  weightedLine_iff_weightedCurve params B fun i S =>
    (PMF.uniformOfFintype F).toOuterMeasure S ≤ ε_commit i

private theorem uniqueLineGapHypothesis_to_smooth [DecidableEq F] (params : FRIParams F) {e : ℕ}
    (hgap : UniqueLineGapHypothesis params e) :
    UniqueCurveGapHypothesis params.toSmooth e := by
  intro i u Z hZ hclose
  let eqv := toSmoothDomEquiv params i.isLt
  have hdom := params.toSmooth_domainSize i.isLt
  have hcum := params.toSmooth_cumLog i.isLt
  have hZ' : 2 ^ (params.d - (i.val + 1)) < Z.card := by
    simpa only [params.toSmooth_arity i, Nat.reduceSub, one_mul, hdom] using hZ
  let u₀ := u ⟨0, by simp⟩ ∘ eqv
  let u₁ := u ⟨1, by simp⟩ ∘ eqv
  have hclose' (z) (hz : z ∈ Z) : ∃ v ∈ params.rsCode (i.val + 1),
      hammingDist (u₀ + z • u₁) v ≤ e / 2 ^ (i.val + 1) := by
    obtain ⟨v, hv, hd⟩ := hclose z hz
    rw [curveSum_toSmooth_eq_line, hcum] at hd
    refine ⟨v ∘ eqv, (mem_rsCode_comp_toSmooth params i.isLt v).mpr hv, Eq.trans_le ?_ hd⟩
    simpa only [hammingDist, Finset.card_eq_sum_ones] using
      sum_filter_equiv eqv _ _ (fun _ => 1) (fun _ => 1)
        (fun j => by simp [u₀, u₁]) (fun _ => rfl)
  obtain ⟨D', v₀, hv₀, v₁, hv₁, hD'_card, hD'_agree⟩ := hgap i u₀ u₁ Z hZ' hclose'
  refine ⟨D'.image eqv, toSmoothPair params i v₀ v₁, toSmoothPair_mem_rsCode params i hv₀ hv₁,
    by rwa [Finset.card_image_of_injective D' eqv.injective, hdom, hcum], fun y hy => ?_⟩
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
  exact (forall_fin_toSmooth_arity_iff params i _).mpr (by
    simpa only [toSmoothPair, eqv, u₀, u₁, Function.comp_apply, Equiv.symm_apply_apply,
      Nat.one_ne_zero, ↓reduceIte] using hD'_agree j hj)

end BinaryTranscriptAndBridges

/-! ### Binary Transcript-State, Weight, Counting, and Unique-Upgrade Corollaries -/

section BinaryBridgeCorollaries

variable {F : Type} [Field F]

/-- Appending suffix rounds `extra` preserves `friTargetWord` at round `i ≤ pref.length`. -/
theorem friTargetWord_append (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friTargetWord params stmt (pref ++ extra) i hi = friTargetWord params stmt pref i hi := by
  cases i with
  | zero => rfl
  | succ k =>
    have hk : k < pref.length := Nat.lt_of_succ_le hlen
    simp only [friTargetWord, prefOracle_append_left pref extra hk,
      prefFoldScalar_append_left pref extra hk]

/-- Appending suffix rounds `extra` does not change `friPreWeight` at round `i ≤ pref.length`. -/
theorem friPreWeight_append [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref extra : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i ≤ params.m) (hlen : i ≤ pref.length) :
    friPreWeight params stmt (pref ++ extra) i hi = friPreWeight params stmt pref i hi := by
  induction i with
  | zero => rfl
  | succ k ih =>
    have hk : k < pref.length := Nat.lt_of_succ_le hlen
    ext j
    simp only [friPreWeight,
      friTargetWord_append params stmt pref extra (Nat.le_of_succ_le hi) hk.le,
      ih (Nat.le_of_succ_le hi) hk.le, prefOracle_append_left pref extra hk]

/-- One-step folding update for `friTargetWord` after appending round `(π, c)`. -/
theorem friTargetWord_append_step (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friTargetWord params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      fold2 (params.g ^ (2 ^ pref.length)) (params.ω ^ (2 ^ pref.length))
        (fun idx : Fin (2 * 2 ^ (params.d - (pref.length + 1))) =>
          restrictOracle (i := pref.length) π
            (reindexDouble (lt_of_lt_of_le hpm params.hm) idx))
        c.foldScalar := by
  simp only [friTargetWord, prefOracle_append_self, prefFoldScalar_append_self]


/-- One-step update for `friPreWeight` after appending round `(π, c)` equals `friNextWeight`. -/
theorem friPreWeight_append_step [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hpm : pref.length < params.m) (π : OracleTable params.d F)
    (c : FRIChal F params.d params.q) :
    friPreWeight params stmt (pref ++ [(π, c)]) (pref.length + 1) hpm =
      friNextWeight params stmt pref pref.length hpm π := by
  ext j
  simp only [friPreWeight, friNextWeight, friOracleFilterWeight,
    friTargetWord_append params stmt pref [(π, c)] hpm.le le_rfl,
    friPreWeight_append params stmt pref [(π, c)] hpm.le le_rfl, prefOracle_append_self]

/-- Oracle-filtered weight is bounded pointwise by `friPreWeight`. -/
theorem friOracleFilterWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - i))) :
    friOracleFilterWeight params stmt pref i hi π j ≤
      friPreWeight params stmt pref i hi j := by
  unfold friOracleFilterWeight
  split_ifs
  · exact le_rfl
  · exact Nat.zero_le _

/-- Pointwise bound on pre-filter weights: `friPreWeight ... i j ≤ 2 ^ i`. -/
theorem friPreWeight_le [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))) :
    friPreWeight params stmt pref i hi j ≤ 2 ^ i := by
  rw [friPreWeight_apply_eq_smooth]
  simpa only [params.toSmooth_cumLog hi] using
    friSmoothPreWeight_le params.toSmooth stmt pref i hi (toSmoothDomEquiv params hi j)

/-- Pointwise bound on pushed weights `friNextWeight ... i π j ≤ 2 ^ (i + 1)`. -/
theorem friNextWeight_le [DecidableEq F] (params : FRIParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (2 ^ (params.d - (i + 1)))) :
    friNextWeight params stmt pref i hi π j ≤ 2 ^ (i + 1) := by
  rw [friNextWeight_apply_eq_smooth]
  simpa only [params.toSmooth_cumLog hi] using
    friSmoothNextWeight_le params.toSmooth stmt pref i hi π (toSmoothDomEquiv params hi j)


private theorem sum_eq_of_toSmoothDomEquiv (params : FRIParams F) {r : ℕ} (hr : r ≤ params.m)
    (f : Fin (2 ^ (params.d - r)) → ℕ) (g : Fin (params.toSmooth.domainSize r) → ℕ)
    (hfg : ∀ j, f j = g (toSmoothDomEquiv params hr j)) :
    (∑ j : Fin (2 ^ (params.d - r)), f j) = ∑ y : Fin (params.toSmooth.domainSize r), g y :=
  (Finset.sum_congr rfl fun j _ => hfg j).trans (Equiv.sum_comp (toSmoothDomEquiv params hr) g)

/-- Total-weight bound: `∑ j, friPreWeight ... i j ≤ 2 ^ d`. -/
theorem sum_friPreWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) :
    (∑ j : Fin (2 ^ (params.d - i)), friPreWeight params stmt pref i hi j) ≤ 2 ^ params.d := by
  rw [sum_eq_of_toSmoothDomEquiv params hi _ _ (friPreWeight_apply_eq_smooth params stmt pref i hi)]
  exact sum_friSmoothPreWeight_le params.toSmooth stmt pref i hi

/-- Total-weight bound on pushed weights: `∑ j, friNextWeight ... i π j ≤ 2 ^ d`. -/
theorem sum_friNextWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F) :
    (∑ j : Fin (2 ^ (params.d - (i + 1))), friNextWeight params stmt pref i hi π j) ≤
      2 ^ params.d := by
  rw [sum_eq_of_toSmoothDomEquiv params hi _ _
    (friNextWeight_apply_eq_smooth params stmt pref i hi π)]
  exact sum_friSmoothNextWeight_le params.toSmooth stmt pref i hi π

/-- Monotonicity of filtered weighted agreement in binary FRI. -/
theorem sum_agree_friOracleFilterWeight_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (c : Fin (2 ^ (params.d - i)) → F) :
    (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := i) π j = c j),
      friOracleFilterWeight params stmt pref i hi π j) ≤
    ∑ j ∈ Finset.univ.filter (fun j => friTargetWord params stmt pref i hi j = c j),
      friPreWeight params stmt pref i hi j := by
  let e := toSmoothDomEquiv params hi
  rw [sum_filter_equiv e _ (fun y => restrictOracle (i := params.toSmooth.cumLog i) π y =
        (c ∘ e.symm) y) _ _
      (fun j => by simp only [Function.comp_apply, Equiv.symm_apply_apply]; rfl)
      (friOracleFilterWeight_apply_eq_smooth params stmt pref i hi π),
    sum_filter_equiv e _ (fun y =>
        friSmoothTargetWord params.toSmooth stmt pref i hi y = (c ∘ e.symm) y) _ _
      (fun j => by simp [e, friTargetWord_apply_eq_smooth params stmt pref i hi j])
      (friPreWeight_apply_eq_smooth params stmt pref i hi)]
  exact sum_agree_friSmoothOracleFilterWeight_le params.toSmooth stmt pref i hi π (c ∘ e.symm)


/-- On a complete transcript `pref ++ [(πFinal, c)]`, `friTranscriptSingleAccepts` coincides with
`friFinalPasses`. -/
theorem friTranscriptSingleAccepts_append_iff (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F)
    (c : FRIChal F params.d params.q) (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt (pref ++ [(πFinal, c)]) s ↔
      friFinalPasses params stmt pref πFinal s := by
  have hm_eq : prefOracle (pref ++ [(πFinal, c)]) params.m = πFinal :=
    hlen ▸ prefOracle_append_self pref πFinal c
  have h0 : prefOracle (pref ++ [(πFinal, c)]) 0 =
      if params.m = 0 then πFinal else prefOracle pref 0 := by
    split_ifs with hm
    · exact hm ▸ hm_eq
    · exact prefOracle_append_left pref [(πFinal, c)] (by omega)
  have hnext (k : Fin params.m) :
      prefOracle (pref ++ [(πFinal, c)]) (k.val + 1) =
        if k.val + 1 = params.m then πFinal else prefOracle pref (k.val + 1) := by
    split_ifs with hlast
    · rwa [hlast]
    · exact prefOracle_append_left pref [(πFinal, c)] (by omega)
  simp only [friTranscriptSingleAccepts, friPrefixPasses, friFinalPasses,
    hm_eq, h0, apply_ite (fun f : OracleTable params.d F => f s), and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => forall_congr' fun k => ?_
  have hk_lt : k.val < pref.length := by omega
  simp only [k.isLt, true_implies, prefOracle_append_left pref [(πFinal, c)] hk_lt,
    prefFoldScalar_append_left pref [(πFinal, c)] hk_lt, hnext k]

/-- On a `List.ofFn` transcript, `friTranscriptSingleAccepts` coincides with `friSingleAccepts`. -/
theorem friTranscriptSingleAccepts_ofFn_iff (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (oracles : Fin (params.m + 1) → OracleTable params.d F)
    (chals : Fin (params.m + 1) → FRIChal F params.d params.q)
    (s : Fin (2 ^ params.d)) :
    friTranscriptSingleAccepts params stmt
        (List.ofFn fun j : Fin (params.m + 1) => (oracles j, chals j)) s ↔
      friSingleAccepts params stmt chals oracles s := by
  simp only [friTranscriptSingleAccepts, friPrefixPasses, friSingleAccepts,
    prefOracle_ofFn oracles chals (Nat.zero_lt_succ params.m),
    prefOracle_ofFn oracles chals (Nat.lt_succ_self params.m), and_assoc]
  refine and_congr_right fun _ => and_congr_left fun _ => forall_congr' fun k => ?_
  simp only [k.isLt, true_implies,
    prefOracle_ofFn oracles chals (Nat.lt_succ_of_lt k.isLt),
    prefFoldScalar_ofFn oracles chals (Nat.lt_succ_of_lt k.isLt),
    prefOracle_ofFn oracles chals (Nat.succ_lt_succ k.isLt)]
  rfl

/-- **Exact binary starting-point counting identity** (corollary of
`card_filter_friSmoothPrefixPasses_eq`). -/
theorem card_filter_friPrefixPasses_eq [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (j : Fin (2 ^ (params.d - i))) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      s.val % 2 ^ (params.d - i) = j.val ∧ friPrefixPasses params stmt pref i s).card =
    friOracleFilterWeight params stmt pref i hi (prefOracle pref i) j := by
  rw [friOracleFilterWeight_apply_eq_smooth]
  have hfilt :
      (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % 2 ^ (params.d - i) = j.val ∧ friPrefixPasses params stmt pref i s) =
      Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % params.toSmooth.domainSize i = (toSmoothDomEquiv params hi j).val ∧
          friSmoothPrefixPasses params.toSmooth stmt pref i s := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, params.toSmooth_domainSize hi,
      toSmoothDomEquiv_val, friPrefixPasses_iff_smooth]
  rw [hfilt]
  exact card_filter_friSmoothPrefixPasses_eq params.toSmooth stmt pref i hi _

/-- **Binary final query-acceptance counting bound** (corollary of
`card_filter_friSmoothFinalPasses_le`). -/
theorem card_filter_friFinalPasses_le [DecidableEq F] (params : FRIParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (hlen : pref.length = params.m) (πFinal : OracleTable params.d F) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      friFinalPasses params stmt pref πFinal s).card ≤
    ∑ j ∈ Finset.univ.filter (fun j =>
      friTargetWord params stmt pref params.m le_rfl j =
        friFinalCodeword params πFinal j),
      friPreWeight params stmt pref params.m le_rfl j := by
  have hcw (j : Fin (2 ^ (params.d - params.m))) : friFinalCodeword params πFinal j =
      friSmoothFinalCodeword params.toSmooth πFinal (toSmoothDomEquiv params le_rfl j) := by
    simp only [friFinalCodeword, friSmoothFinalCodeword, params.toSmooth_finalAnchorPoints,
      FRIParams.eval, FRISmoothParams.eval, cosetEval, cosetPoint, params.toSmooth_cumLog le_rfl,
      toSmoothDomEquiv_val]
  rw [filter_friFinalPasses_eq, sum_filter_equiv (toSmoothDomEquiv params le_rfl) _
    (fun y => friSmoothTargetWord params.toSmooth stmt pref params.m le_rfl y =
      friSmoothFinalCodeword params.toSmooth πFinal y) _ _
    (fun j => by rw [friTargetWord_apply_eq_smooth, hcw])
    (friPreWeight_apply_eq_smooth params stmt pref params.m le_rfl)]
  exact card_filter_friSmoothFinalPasses_le params.toSmooth stmt pref hlen πFinal

/-- **Conditional step (shrinking per-round binary unique-decoding weighted upgrade)** (corollary of
`weightedCurveGapPerRound_of_uniqueCurveGap`). -/
theorem weightedLineGapPerRound_of_uniqueLineGap [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueLineGapHypothesis params e) :
    WeightedLineGapPerRound params (2 ^ params.d - e - 1)
      (fun i => 2 ^ (params.d - (i.val + 1))) := by
  have huniq' : 2 * e + params.toSmooth.dim 0 ≤ 2 ^ params.toSmooth.d := by
    simpa only [params.toSmooth_dim (Nat.zero_le params.m)] using huniq
  have hsm := weightedCurveGapPerRound_of_uniqueCurveGap params.toSmooth huniq'
    (uniqueLineGapHypothesis_to_smooth params hgap)
  rw [weightedLineGapPerRound_iff_weightedCurveGapPerRound]
  refine hsm.mono fun i => ?_
  simp only [FRISmoothParams.arity, pow_one, Nat.reduceSub, one_mul,
    params.toSmooth_domainSize i.isLt, le_rfl]

/-- **Conditional step (uniform binary unique-decoding weighted upgrade)**. -/
theorem weightedLineGapBound_of_uniqueLineGap [DecidableEq F]
    (params : FRIParams F) {e : ℕ} (huniq : 2 * e + params.dim 0 ≤ 2 ^ params.d)
    (hgap : UniqueLineGapHypothesis params e) :
    WeightedLineGapBound params (2 ^ params.d - e - 1) (2 ^ (params.d - 1)) :=
  (weightedLineGapPerRound_of_uniqueLineGap params huniq hgap).mono fun _ =>
    Nat.pow_le_pow_right (by omega)
      (Nat.sub_le_sub_left (Nat.succ_le_succ (Nat.zero_le _)) _)


end BinaryBridgeCorollaries

end Cslib.Crypto.Protocols.FRI
