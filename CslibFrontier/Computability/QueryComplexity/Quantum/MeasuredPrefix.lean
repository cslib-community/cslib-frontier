/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.Quantum.ValueQueryUpdate
public import CslibFrontier.Languages.Probabilistic.QueriesWith
public import CslibFrontier.Languages.Probabilistic.Oracle.EvalPure
import CslibFrontier.Probability.PMF.Expect

/-!
# Quantum query prefixes with measured classical oracle services

An interaction prefix alternates coherent queries, measurements and classical subroutines.
Classical labels remember the measured outcomes and returned replies. The quantum register is
retained on every branch. A classical subroutine can adapt its internal queries to the actual
table. Each is counted even when the subroutine eventually returns an error.
-/

public section

namespace Cslib.Quantum

open Finset OracleComp
open scoped BigOperators

variable {ι D V W : Type} [Fintype ι] [Fintype V] [Fintype W] [DecidableEq ι]

/-- A finite interaction before a fresh address is sampled. The label type contains all
outward classical information. Control depends on these labels; coherent queries act on the
entire private quantum register and produce no classical query transcript. -/
inductive MeasuredPrefix (ι D V W : Type) [Fintype ι] [Fintype V] [Fintype W] :
    (B : Type) → [Fintype B] → Type 1
  /-- The empty prefix acting on the supplied quantum register. -/
  | start : MeasuredPrefix ι D V W Unit
  /-- A table-independent isometry selected by the observed classical history. -/
  | localGate {B} [history : Fintype B] (prior : MeasuredPrefix ι D V W B)
      (applyGate : B → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) : MeasuredPrefix ι D V W B
  /-- Conditional coherent query followed by a branch-dependent isometry. -/
  | coherent {B} [history : Fintype B] (prior : MeasuredPrefix ι D V W B) (enabled : B → Bool)
      (gate : B → ValueState ι V W →ₗᵢ[ℂ] ValueState ι V W) : MeasuredPrefix ι D V W B
  /-- Measure a classical label and retain the associated projected state. -/
  | measure {B M} [history : Fintype B] [labels : Fintype M] [eqLabel : DecidableEq M]
      (prior : MeasuredPrefix ι D V W B)
      (read : B → ι × V × W → M) : MeasuredPrefix ι D V W (B × M)
  /-- Run an adaptive classical service on the same fixed table and record the outward reply.
  Internal reads occur in the service only. -/
  | service {B R} [history : Fintype B] [labels : Fintype R] [eqLabel : DecidableEq R]
      (prior : MeasuredPrefix ι D V W B)
      (run : B → OracleComp (fun _ : ι => D) R) (K : ℕ) (budget : ∀ b, (run b).IsQueryBounded K) :
      MeasuredPrefix ι D V W (B × R)

namespace MeasuredPrefix

variable (step : D → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))

/-- Unnormalized residual vector at an actual outward history. Its squared norm is the
probability of that history. The classical service returns the answer computed from the table. -/
noncomputable def state (step : D → (EuclideanSpace ℂ V ≃ₗᵢ[ℂ] EuclideanSpace ℂ V))
    (ψ : ValueState ι V W) {B} [Fintype B] :
    MeasuredPrefix ι D V W B → (ι → D) → B → ValueState ι V W
  | .start, _, _ => ψ
  | .localGate (history := _) p g, H, b => g b (p.state step ψ H b)
  | .coherent (history := _) p enabled gate, H, b =>
    gate b (if enabled b then valueOracle step H (p.state step ψ H b) else p.state step ψ H b)
  | .measure (history := _) (labels := _) (eqLabel := _) p read, H, (b, m) =>
    projOutcomes (fun x => read b x = m) (p.state step ψ H b)
  | .service (history := _) (labels := _) (eqLabel := _) p run _ _, H, (b, r) =>
    if evalPure H (run b) = r then p.state step ψ H b else 0

/-- The sum of the per-call disturbance factors. A coherent call contributes two and a
classical service inspecting at most K table entries contributes `√(2K)`. Local gates and
measurements have zero cost. -/
@[expose] noncomputable def updateCost {B} [Fintype B] : MeasuredPrefix ι D V W B → ℝ
  | .start => 0
  | .localGate (history := _) p _ => p.updateCost
  | .coherent (history := _) p _ _ => p.updateCost + 2
  | .measure (history := _) (labels := _) (eqLabel := _) p _ => p.updateCost
  | .service (history := _) (labels := _) (eqLabel := _) p _ K _ => p.updateCost + Real.sqrt (2 * K)

private theorem sum_sq_record {R E : Type} [Fintype R] [DecidableEq R] [NormedAddCommGroup E]
    (r : R) (a b : E) :
    ∑ v, ‖(if r = v then a else 0) - (if r = v then b else 0)‖ ^ 2 = ‖a - b‖ ^ 2 := by
  rw [sum_eq_single r]
  · simp
  · intro x _ hx; simp [Ne.symm hx]
  · simp

omit [DecidableEq ι] in
/-- The branches carry exactly the squared norm of the input register, even for adaptively
chosen services and intermediate measurements. -/
theorem sum_sq_state {B} [Fintype B] (p : MeasuredPrefix ι D V W B)
    (ψ : ValueState ι V W) (H : ι → D) :
    ∑ b, ‖p.state step ψ H b‖ ^ 2 = ‖ψ‖ ^ 2 := by
  induction p with
  | start => simp [state]
  | localGate p g ih => simpa [state] using ih
  | coherent p enabled gate ih =>
    simpa [state, apply_ite] using ih
  | measure p read ih =>
    simpa only [state, Fintype.sum_prod_type, sum_sq_norm_projOutcomes_fibers] using ih
  | service p run K _ ih =>
    simp only [state, Fintype.sum_prod_type]
    convert ih using 1
    apply sum_congr rfl
    intro b _
    rw [sum_eq_single (evalPure H (run b))]
    · simp
    · intro r _ hr; simp [Ne.symm hr]
    · simp

omit [DecidableEq ι] in
private theorem state_add {B} [Fintype B] (p : MeasuredPrefix ι D V W B) (H : ι → D)
    (x y : ValueState ι V W) (b : B) :
    p.state step (x + y) H b = p.state step x H b + p.state step y H b := by
  induction p with
  | start => rfl
  | localGate p g ih => simp [state, ih, map_add]
  | coherent p enabled gate ih => cases hv : enabled b <;> simp [state, hv, ih, map_add]
  | measure p read ih => obtain ⟨b, m⟩ := b; simp [state, ih, map_add]
  | service p run K budget ih =>
    obtain ⟨b, r⟩ := b
    by_cases hr : evalPure H (run b) = r <;> simp [state, hr, ih]

omit [DecidableEq ι] in
private theorem state_smul {B} [Fintype B] (p : MeasuredPrefix ι D V W B) (H : ι → D)
    (z : ℂ) (x : ValueState ι V W) (b : B) :
    p.state step (z • x) H b = z • p.state step x H b := by
  induction p with
  | start => rfl
  | localGate p g ih => simp [state, ih, map_smul]
  | coherent p enabled gate ih => cases hv : enabled b <;> simp [state, hv, ih, map_smul]
  | measure p read ih => obtain ⟨b, m⟩ := b; simp [state, ih, map_smul]
  | service p run K budget ih =>
    obtain ⟨b, r⟩ := b
    by_cases hr : evalPure H (run b) = r <;> simp [state, hr, ih]

omit [DecidableEq ι] in
/-- Collect all outward records and retained amplitudes of the actual measured computation.
Its squared amplitude at each label is the probability of that record and final basis outcome. -/
noncomputable def outcomeIsometry {B} [Fintype B] (p : MeasuredPrefix ι D V W B) (H : ι → D) :
    ValueState ι V W →ₗᵢ[ℂ] EuclideanSpace ℂ (B × (ι × V × W)) where
  toFun ψ := WithLp.toLp 2 fun (b, x) => (p.state step ψ H b).ofLp x
  map_add' x y := by ext ⟨b, j⟩; simp [state_add]
  map_smul' z x := by ext ⟨b, j⟩; simp [state_smul]
  norm_map' ψ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    change ‖(WithLp.toLp 2 fun (b, x) => (p.state step ψ H b).ofLp x :
      EuclideanSpace ℂ (B × (ι × V × W)))‖ ^ 2 = ‖ψ‖ ^ 2
    simpa only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type] using p.sum_sq_state step ψ H

omit [DecidableEq ι] in
/-- Disturbance costs are nonnegative. -/
theorem updateCost_nonneg {B} [Fintype B] (p : MeasuredPrefix ι D V W B) :
    0 ≤ p.updateCost := by
  induction p with
  | start => exact (le_rfl : (0 : ℝ) ≤ 0)
  | localGate p g ih => exact ih
  | coherent p enabled gate ih => exact add_nonneg ih (by norm_num)
  | measure p read ih => exact ih
  | service p run K hb ih => exact add_nonneg ih (Real.sqrt_nonneg _)

private theorem sum_sq_triangle {J E : Type} [Fintype J] [NormedAddCommGroup E]
    (a b c : J → E) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (hab : ∑ j, ‖a j - b j‖ ^ 2 ≤ d ^ 2) (hbc : ∑ j, ‖b j - c j‖ ^ 2 ≤ e ^ 2) :
    ∑ j, ‖a j - c j‖ ^ 2 ≤ (d + e) ^ 2 := by
  let pack (x : J → E) : PiLp 2 (fun _ : J => E) := WithLp.toLp 2 x
  have sq (x y : J → E) : ‖pack x - pack y‖ ^ 2 = ∑ j, ‖x j - y j‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    rfl
  rw [← sq] at hab hbc ⊢
  exact pow_le_pow_left₀ (norm_nonneg _)
    ((norm_sub_le_norm_sub_add_norm_sub _ _ _).trans
      (add_le_add ((sq_le_sq₀ (norm_nonneg _) hd).mp hab)
        ((sq_le_sq₀ (norm_nonneg _) he).mp hbc))) 2

private theorem extend_bound {B C E : Type} [Fintype B] [Fintype C] [NormedAddCommGroup E]
    (u : (ι → D) → B → E) (move : (ι → D) → (B → E) → C → E)
    (H : ι → D) (v : D) {d e : ℝ} (hd : 0 ≤ d) (he : 0 ≤ e)
    (prev : ∑ i, ∑ b, ‖u (Function.update H i v) b - u H b‖ ^ 2 ≤ d ^ 2)
    (isom : ∀ G x y, (∑ c, ‖move G x c - move G y c‖ ^ 2) = ∑ b, ‖x b - y b‖ ^ 2)
    (localCost : ∑ i, ∑ c, ‖move (Function.update H i v) (u H) c - move H (u H) c‖ ^ 2 ≤
      e ^ 2) :
    ∑ i, ∑ c, ‖move (Function.update H i v) (u (Function.update H i v)) c -
      move H (u H) c‖ ^ 2 ≤ (d + e) ^ 2 := by
  let G (i : ι) := Function.update H i v
  have h := sum_sq_triangle (J := ι × C) (fun (i, c) => move (G i) (u (G i)) c)
    (fun (i, c) => move (G i) (u H) c) (fun (_, c) => move H (u H) c) hd he
  simp only [Fintype.sum_prod_type, isom] at h
  exact h prev localCost

private theorem sum_sq_service_change {R E : Type} [Fintype R] [DecidableEq R]
    [NormedAddCommGroup E]
    (H : ι → D) (v : D) (run : OracleComp (fun _ : ι => D) R) {K : ℕ}
    (budget : run.IsQueryBounded K) (u : E) :
    ∑ i, ∑ r, ‖(if evalPure (Function.update H i v) run = r then u else 0) -
      (if evalPure H run = r then u else 0)‖ ^ 2 ≤ (2 * K : ℝ) * ‖u‖ ^ 2 := by
  classical
  let reads := (queriesWith H run).toFinset
  have stab (i : ι) (hi : i ∉ reads) :
      evalPure (Function.update H i v) run = evalPure H run := by
    apply (interpret_id_congr H (Function.update H i v) run ?_).1
    intro j hj
    exact Function.update_of_ne (fun he => hi (by simpa [he, reads] using hj)) ..
  have row (i : ι) :
      (∑ r, ‖(if evalPure (Function.update H i v) run = r then u else 0) -
        (if evalPure H run = r then u else 0)‖ ^ 2) ≤
        if i ∈ reads then 2 * ‖u‖ ^ 2 else 0 := by
    by_cases hi : i ∈ reads
    · rw [ite_eq_left hi]
      let a := evalPure (Function.update H i v) run
      let b := evalPure H run
      change (∑ r, ‖(if a = r then u else 0) - (if b = r then u else 0)‖ ^ 2) ≤ _
      by_cases hab : a = b
      · simp [hab]
      · have per (r : R) : ‖(if a = r then u else 0) - (if b = r then u else 0)‖ ^ 2 =
            (if a = r then ‖u‖ ^ 2 else 0) + (if b = r then ‖u‖ ^ 2 else 0) := by
          by_cases ha : a = r <;> by_cases hb : b = r <;> simp_all
        simp [per, sum_add_distrib, two_mul]
    · simp [hi, stab i hi]
  calc
    _ ≤ ∑ i, if i ∈ reads then 2 * ‖u‖ ^ 2 else 0 := sum_le_sum fun i _ => row i
    _ = reads.card * (2 * ‖u‖ ^ 2) := by simp
    _ ≤ _ := by
      have hn := List.toFinset_card_le (queriesWith H run) |>.trans (budget.length_queriesWith_le H)
      calc
        _ ≤ (K : ℝ) * (2 * ‖u‖ ^ 2) := by gcongr
        _ = _ := by ring

/-- Sum, over changed table addresses and all outward histories, of the squared difference
between the two retained states. The estimate includes all earlier adaptive classical services
and coherent calls on this same table. -/
theorem sum_sq_state_update_sub_le {B} [Fintype B] (p : MeasuredPrefix ι D V W B)
    (ψ : ValueState ι V W) (hψ : ‖ψ‖ = 1) (H : ι → D) (v : D) :
    ∑ i, ∑ b, ‖p.state step ψ (Function.update H i v) b - p.state step ψ H b‖ ^ 2 ≤
      p.updateCost ^ 2 := by
  induction p with
  | start => simp [state, updateCost]
  | localGate p g ih => simpa only [state, updateCost, ← map_sub, LinearIsometry.norm_map] using ih
  | @coherent B _ p enabled gate ih =>
    let move (G : ι → D) (x : B → ValueState ι V W) (b : B) :=
      gate b (if enabled b then valueOracle step G (x b) else x b)
    apply extend_bound (p.state step ψ) move H v p.updateCost_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      ih
    · intro G x y
      apply sum_congr rfl
      intro b _
      cases hv : enabled b <;> simp [move, hv, ← map_sub]
    · rw [sum_comm]
      calc
        _ ≤ ∑ b, 4 * ‖p.state step ψ H b‖ ^ 2 := by
          refine sum_le_sum fun b _ => ?_
          cases hv : enabled b with
          | false => simp [move, hv]
          | true =>
            simp only [move, hv, ↓reduceIte, ← map_sub (gate b), LinearIsometry.norm_map]
            calc
              _ ≤ ∑ i, (2 * ‖querySlice i (p.state step ψ H b)‖) ^ 2 := by
                exact sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
                  (norm_valueOracle_update_sub_le ..) 2
              _ = _ := by norm_num [mul_pow, ← mul_sum, sum_sq_norm_querySlice]
        _ = _ := by rw [← mul_sum, sum_sq_state, hψ]; norm_num
  | @measure B M _ _ _ p read ih =>
    simpa only [state, updateCost, Fintype.sum_prod_type, ← map_sub,
      sum_sq_norm_projOutcomes_fibers] using ih
  | @service B R _ _ _ p run K budget ih =>
    let move (G : ι → D) (x : B → ValueState ι V W) (br : B × R) :=
      if evalPure G (run br.1) = br.2 then x br.1 else 0
    apply extend_bound (p.state step ψ) move H v p.updateCost_nonneg
      (Real.sqrt_nonneg (2 * (K : ℝ))) ih
    · intro G x y
      simp only [move, Fintype.sum_prod_type, sum_sq_record]
    · simp only [move, Fintype.sum_prod_type]
      rw [sum_comm]
      calc
        _ ≤ ∑ b, (2 * K : ℝ) * ‖p.state step ψ H b‖ ^ 2 := sum_le_sum fun b _ =>
          sum_sq_service_change H v (run b) (budget b) _
        _ = _ := by rw [← mul_sum, sum_sq_state, Real.sq_sqrt (by positivity)]
                    rw [hψ]; ring

/-- Acceptance when a bounded classical service returns a reply and the adversary resumes its
measured quantum computation on the same table, starting in the supplied residual state. -/
@[expose] noncomputable def serviceAcceptance {R O : Type} [Fintype O]
    (run : OracleComp (fun _ : ι => D) R) (next : R → MeasuredPrefix ι D V W O)
    (accept : R → Finset (O × (ι × V × W))) (H : ι → D) (u : ValueState ι V W) : ℝ :=
  let r := evalPure H run
  measureProb ((next r).outcomeIsometry step H u) (accept r)

private theorem mean_change_unit {R O : Type} [Fintype O] (run : OracleComp (fun _ : ι => D) R)
    (next : R → MeasuredPrefix ι D V W O) (accept : R → Finset (O × (ι × V × W)))
    (H : ι → D) (v : D) (u : ValueState ι V W) (hu : ‖u‖ = 1) {K : ℕ}
    (bound : run.IsQueryBounded K) (μ : PMF ι) {δ : ℝ} (hp : ∀ i, (μ i).toReal ≤ δ) :
    (∑ i, (μ i).toReal * |serviceAcceptance step run next accept (Function.update H i v) u -
      serviceAcceptance step run next accept H u|) ≤
      Real.sqrt (δ * (K + (next (evalPure H run)).updateCost ^ 2)) := by
  classical
  let r := evalPure H run
  let G (i : ι) := Function.update H i v
  let score (T : ι → D) := serviceAcceptance step run next accept T u
  let gap (i : ι) := |score (G i) - score H|
  let reads := (queriesWith H run).toFinset
  let U (T : ι → D) := (next r).outcomeIsometry step T u
  have score_range (T) : 0 ≤ score T ∧ score T ≤ 1 :=
    ⟨measureProb_nonneg _ _, (measureProb_le_measureProb_univ _ _).trans_eq
      (by rw [measureProb_univ, LinearIsometry.norm_map, hu, one_pow])⟩
  have one (i) : gap i ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith [(score_range (G i)).2,
    (score_range H).1], by linarith [(score_range H).2, (score_range (G i)).1]⟩
  have each (i) : gap i ^ 2 ≤ (if i ∈ reads then 1 else 0) + ‖U (G i) - U H‖ ^ 2 := by
    by_cases hi : i ∈ reads
    · simp only [hi, ↓reduceIte]
      exact (pow_le_one₀ (abs_nonneg _) (one i)).trans (le_add_of_nonneg_right (sq_nonneg _))
    · have same : evalPure (G i) run = r := by
        apply (interpret_id_congr H (G i) run ?_).1
        intro j hj
        exact Function.update_of_ne (fun he => hi (by simpa [he, reads] using hj)) ..
      have near := abs_measureProb_sub_le_norm_sub (ψ := U (G i)) (φ := U H)
        (by simp [U, hu]) (by simp [U, hu]) (accept r)
      simp only [hi, ↓reduceIte, zero_add]
      apply pow_le_pow_left₀ (abs_nonneg _) _ 2
      simpa only [gap, score, serviceAcceptance, same, r, U] using near
  have all : ∑ i, ‖U (G i) - U H‖ ^ 2 ≤ (next r).updateCost ^ 2 := by
    have h := (next r).sum_sq_state_update_sub_le step u hu H v
    simpa only [U, outcomeIsometry, EuclideanSpace.norm_sq_eq, PiLp.sub_apply,
      Fintype.sum_prod_type, LinearIsometry.coe_mk, LinearMap.coe_mk, AddHom.coe_mk] using h
  have card : reads.card ≤ K :=
    (List.toFinset_card_le (queriesWith H run)).trans (bound.length_queriesWith_le H)
  have squares : ∑ i, gap i ^ 2 ≤ K + (next r).updateCost ^ 2 := by
    refine (sum_le_sum fun i _ => each i).trans ?_
    simpa [sum_add_distrib] using add_le_add (show (reads.card : ℝ) ≤ K by exact_mod_cast card) all
  have jensen := Probability.PMF.sq_tsum_le_tsum_sq μ (g := gap) (fun _ => abs_nonneg _) one
  rw [tsum_fintype, tsum_fintype] at jensen
  apply Real.le_sqrt_of_sq_le
  refine jensen.trans ((sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hp i) (sq_nonneg _)).trans ?_)
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left squares
    (ENNReal.toReal_nonneg.trans (hp μ.support_nonempty.choose))

/-- Expected change caused by one hidden table update before a bounded classical
service and an arbitrary adaptive quantum continuation. Only the actual classical accesses at H
can alter its reply. On every other address, the single unchanged reply selects the same circuit. -/
theorem mean_abs_serviceAcceptance_update_sub_le {R O : Type} [Fintype O]
    (run : OracleComp (fun _ : ι => D) R) (next : R → MeasuredPrefix ι D V W O)
    (accept : R → Finset (O × (ι × V × W))) (H : ι → D) (v : D) (u : ValueState ι V W)
    {K : ℕ} (bound : run.IsQueryBounded K) (μ : PMF ι) {δ : ℝ} (hp : ∀ i, (μ i).toReal ≤ δ) :
    (∑ i, (μ i).toReal * |serviceAcceptance step run next accept (Function.update H i v) u -
      serviceAcceptance step run next accept H u|) ≤
      ‖u‖ ^ 2 * Real.sqrt (δ * (K + (next (evalPure H run)).updateCost ^ 2)) := by
  by_cases hu : u = 0
  · simp [hu, serviceAcceptance, measureProb]
  let z : ℂ := (‖u‖ : ℂ)
  let φ := z⁻¹ • u
  have hz : z ≠ 0 := by simpa [z] using hu
  have normφ : ‖φ‖ = 1 := by simp [φ, z, norm_smul, hu]
  have eq : z • φ = u := by simp [φ, smul_smul, hz]
  have scale (T) : serviceAcceptance step run next accept T u =
      ‖u‖ ^ 2 * serviceAcceptance step run next accept T φ := by
    conv_lhs => rw [← eq]
    simp only [serviceAcceptance, map_smul, measureProb_smul]
    simp [z]
  simp_rw [scale, ← mul_sub, abs_mul, abs_of_nonneg (sq_nonneg ‖u‖),
    ← mul_assoc, mul_comm _ (‖u‖ ^ 2), mul_assoc]
  rw [← mul_sum]
  exact mul_le_mul_of_nonneg_left (mean_change_unit step run next accept H v φ normφ bound μ hp)
    (sq_nonneg _)

end MeasuredPrefix

end Cslib.Quantum
