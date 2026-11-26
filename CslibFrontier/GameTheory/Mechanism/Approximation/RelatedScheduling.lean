/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import CslibFrontier.GameTheory.Mechanism.Myerson
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Archer–Tardos Characterization and Truthful Scheduling on Related Machines

This module formalizes the single-parameter cost-minimization (reverse auction) characterization of
Archer and Tardos ([ArcherTardos2001]; [NisanRoughgardenTardosVazirani2007], Chapter 12,
Definition 12.1, Theorem 12.2, and Exercise 12.1, locators not verified against primary PDF),
together with its application to truthful makespan minimization on uniformly related machines.

Each agent `i : ι` has a private unit cost `cᵢ > 0` (for related machines of speed `sᵢ > 0`,
`cᵢ = 1 / sᵢ`), is assigned work `work c i ≥ 0`, and receives a payment `payment c i`, yielding
quasilinear utility `payment c i - cᵢ * work c i`. A work rule is *antitone* (`IsAntitoneWork`) if
increasing an agent's own cost `cᵢ` never increases its assigned work `work (update c i cᵢ') i`.
Whenever the tail `x ↦ work (update c i x) i` is integrable on `(cᵢ, ∞)`, the **Archer–Tardos
payment formula** `pᵢ(c) = cᵢ * work c i + ∫ x in Ioi (cᵢ), work (update c i x) i` makes every
antitone work rule DSIC and individually rational, and is the unique DSIC payment rule satisfying
the normalization `lim_{x → ∞} pᵢ(update c i x) = 0`.

On uniformly related machines with public nonnegative job weights `w : J → ℝ` and `m ≥ 2`
machines, exact makespan minimization with any fixed cost-independent tie-breaking linear order on
schedules (`lexOptAlloc`) is antitone in machine unit costs (equivalently, monotone in machine
speeds) and assigns zero work to any machine whose unit cost is sufficiently large. Consequently
its work tail is compactly supported, integrable, and yields a DSIC, individually rational exact
makespan-minimization mechanism (`lexOptMechanism_isDSIC`, `lexOptMechanism_isIR`).

## Main definitions

* `Cslib.GameTheory.Mechanism.RelatedScheduling.CostMechanism`: single-parameter cost-minimization
  mechanism (`work` and `payment`).
* `Cslib.GameTheory.Mechanism.RelatedScheduling.CostMechanism.IsDSIC`, `IsIR`, `IsAntitoneWork`,
  `HasIntegrableTail`, `archerTardosPayment`, `archerTardosMechanism`.
* `Cslib.GameTheory.Mechanism.RelatedScheduling.work`, `relatedMakespan`, `optRelatedMakespan`,
  `lexOptAlloc`, `lexOptMechanism`: related-machine scheduling model and lexicographically
  tie-broken optimal mechanism.

## Main results

* `Cslib.GameTheory.Mechanism.RelatedScheduling.CostMechanism.IsDSIC.isAntitoneWork`: DSIC
  cost mechanisms have antitone work rules ([ArcherTardos2001];
  [NisanRoughgardenTardosVazirani2007], Chapter 12, Theorem 12.2, locator not verified against
  primary PDF).
* `Cslib.GameTheory.Mechanism.RelatedScheduling.archerTardosMechanism_isDSIC`,
  `archerTardosMechanism_isIR`, `archerTardosPayment_nonneg`: antitone work rules with integrable
  tails are DSIC and individually rational under Archer–Tardos payments.
* `CostMechanism.IsDSIC.payment_eq_archerTardosPayment`:
  uniqueness of Archer–Tardos payments under `lim_{x → ∞} pᵢ(x, c₋ᵢ) = 0`.
* `Cslib.GameTheory.Mechanism.RelatedScheduling.lexOptWork_isAntitoneWork`,
  `lexOptMechanism_isDSIC`, `lexOptMechanism_isIR`, `lexOptAlloc_isOptimal`: exact makespan
  minimization on related machines with fixed tie-breaking is antitone in unit costs and
  implementable as a DSIC, individually rational mechanism ([ArcherTardos2001];
  [NisanRoughgardenTardosVazirani2007], Chapter 12, Exercise 12.1, locator not verified against
  primary PDF).

## References

* [A. Archer and É. Tardos, *Truthful Mechanisms for One-Parameter Agents*][ArcherTardos2001]
* [N. Nisan, T. Roughgarden, É. Tardos, and V. V. Vazirani (eds.),
  *Algorithmic Game Theory*, Chapter 12, §12.1 and Exercise 12.1]
  [NisanRoughgardenTardosVazirani2007]
-/

open MeasureTheory Filter Topology

public section

namespace Cslib.GameTheory.Mechanism.RelatedScheduling

/-! ### Archer–Tardos Characterization for Single-Parameter Cost Mechanisms -/

/-- A direct-revelation single-parameter cost-minimization mechanism: on reported positive unit
costs `c : ι → ℝ`, agent `i` is assigned work `work c i` and receives payment `payment c i`. -/
structure CostMechanism (ι : Type*) where
  /-- The work (load) rule `work c i`. -/
  work : (ι → ℝ) → ι → ℝ
  /-- The payment rule `payment c i` paid to agent `i`. -/
  payment : (ι → ℝ) → ι → ℝ

section ArcherTardos

variable {ι : Type*}

/-- Positive unit-cost profiles `c i > 0` for every agent `i`. -/
@[expose] def posCosts : Set (ι → ℝ) :=
  {c | ∀ i, 0 < c i}

theorem update_mem_posCosts [DecidableEq ι] {c : ι → ℝ} (hc : c ∈ posCosts) (i : ι) {x : ℝ}
    (hx : 0 < x) : Function.update c i x ∈ posCosts := fun j => by
  rcases eq_or_ne j i with rfl | hji
  · simpa only [Function.update_self] using hx
  · simpa only [Function.update_of_ne hji] using hc j

/-- Quasilinear utility `payment c i - v * work c i` of agent `i` with true unit cost `v` on
reported profile `c`. -/
@[expose] def CostMechanism.utility (M : CostMechanism ι) (i : ι) (v : ℝ) (c : ι → ℝ) : ℝ :=
  M.payment c i - v * M.work c i

/-- Dominant-strategy incentive compatibility on positive unit-cost profiles: reporting true cost
`v > 0` maximizes agent `i`'s utility. -/
@[expose] def CostMechanism.IsDSIC [DecidableEq ι] (M : CostMechanism ι) : Prop :=
  ∀ (c : ι → ℝ), c ∈ posCosts → ∀ (i : ι) (v : ℝ), 0 < v →
    M.utility i v c ≤ M.utility i v (Function.update c i v)

/-- Individual rationality on positive unit-cost profiles: a truthful agent receives nonnegative
utility. -/
@[expose] def CostMechanism.IsIR (M : CostMechanism ι) : Prop :=
  ∀ (c : ι → ℝ), c ∈ posCosts → ∀ i : ι, 0 ≤ M.utility i (c i) c

/-- A work rule is *antitone* (monotone nonincreasing in own cost) on positive cost profiles:
increasing agent `i`'s reported cost never increases the work assigned to `i`. -/
@[expose] def IsAntitoneWork [DecidableEq ι] (q : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ (c : ι → ℝ), c ∈ posCosts → ∀ i : ι,
    AntitoneOn (fun x => q (Function.update c i x) i) (Set.Ioi 0)

/-- The tail integrability hypothesis of Archer–Tardos: along every agent's own cost coordinate,
the work function is integrable on `(a, ∞)` for every `a > 0`. -/
@[expose] def HasIntegrableTail [DecidableEq ι] (q : (ι → ℝ) → ι → ℝ) : Prop :=
  ∀ (c : ι → ℝ), c ∈ posCosts → ∀ (i : ι) (a : ℝ), 0 < a →
    IntegrableOn (fun x => q (Function.update c i x) i) (Set.Ioi a) volume

/-- **Archer–Tardos payment formula** ([ArcherTardos2001];
[NisanRoughgardenTardosVazirani2007], Chapter 12, Theorem 12.2, locator not verified against
primary PDF): `pᵢ(c) = cᵢ * qᵢ(c) + ∫ x in Ioi (cᵢ), qᵢ(update c i x)`. -/
@[expose] noncomputable def archerTardosPayment [DecidableEq ι] (q : (ι → ℝ) → ι → ℝ)
    (c : ι → ℝ) (i : ι) : ℝ :=
  c i * q c i + ∫ x in Set.Ioi (c i), q (Function.update c i x) i

/-- The cost mechanism pairing work rule `q` with Archer–Tardos payments. -/
@[expose] noncomputable def archerTardosMechanism [DecidableEq ι] (q : (ι → ℝ) → ι → ℝ) :
    CostMechanism ι :=
  ⟨q, archerTardosPayment q⟩

/-- **Archer–Tardos necessity**: every DSIC cost mechanism has an antitone work rule. -/
theorem CostMechanism.IsDSIC.isAntitoneWork [DecidableEq ι] {M : CostMechanism ι}
    (hM : M.IsDSIC) : IsAntitoneWork M.work := by
  intro c hc i a ha b hb hab
  rcases hab.lt_or_eq with hlt | rfl
  · have h1 := hM (Function.update c i b) (update_mem_posCosts hc i hb) i a ha
    have h2 := hM (Function.update c i a) (update_mem_posCosts hc i ha) i b hb
    simp only [CostMechanism.utility, Function.update_idem] at h1 h2
    change M.work (Function.update c i b) i ≤ M.work (Function.update c i a) i
    nlinarith
  · exact le_rfl

private theorem setIntegral_Ioc_bounds_of_antitoneOn {f : ℝ → ℝ}
    (hf : AntitoneOn f (Set.Ioi 0)) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hint : IntegrableOn f (Set.Ioc a b) volume) :
    (b - a) * f b ≤ ∫ x in Set.Ioc a b, f x ∧ ∫ x in Set.Ioc a b, f x ≤ (b - a) * f a := by
  have hmeas : volume (Set.Ioc a b) ≠ ⊤ := by simp [Real.volume_Ioc]
  have hval (k : ℝ) : ∫ _x in Set.Ioc a b, k = (b - a) * k := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (sub_nonneg.2 hab),
      smul_eq_mul]
  exact ⟨(hval (f b)).symm.trans_le
      (setIntegral_mono_on (integrableOn_const (hs := hmeas)) hint measurableSet_Ioc
        fun x hx => hf (ha.trans hx.1) (ha.trans_le hab) hx.2),
    (setIntegral_mono_on hint (integrableOn_const (hs := hmeas)) measurableSet_Ioc
      fun x hx => hf ha (ha.trans hx.1) hx.1.le).trans_eq (hval (f a))⟩

private theorem setIntegral_Ioi_split {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hint : IntegrableOn f (Set.Ioi a) volume) :
    ∫ x in Set.Ioi a, f x = (∫ x in Set.Ioc a b, f x) + ∫ x in Set.Ioi b, f x := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi hab,
    setIntegral_union Set.Ioc_disjoint_Ioi_same measurableSet_Ioi
      (hint.mono_set Set.Ioc_subset_Ioi_self) (hint.mono_set (Set.Ioi_subset_Ioi hab))]

/-- **Archer–Tardos sufficiency** ([ArcherTardos2001]; [NisanRoughgardenTardosVazirani2007],
Chapter 12, Theorem 12.2, locator not verified against primary PDF): an antitone work rule with
integrable tails is DSIC under `archerTardosPayment`. -/
theorem archerTardosMechanism_isDSIC [DecidableEq ι] {q : (ι → ℝ) → ι → ℝ}
    (hq : IsAntitoneWork q) (hint : HasIntegrableTail q) :
    (archerTardosMechanism q).IsDSIC := by
  intro c hc i v hv
  set f : ℝ → ℝ := fun x => q (Function.update c i x) i
  have hu_c : (archerTardosMechanism q).utility i v c =
      (c i - v) * f (c i) + ∫ x in Set.Ioi (c i), f x := by
    simp only [CostMechanism.utility, archerTardosMechanism, archerTardosPayment, f,
      Function.update_eq_self]
    ring
  have hu_v : (archerTardosMechanism q).utility i v (Function.update c i v) =
      ∫ x in Set.Ioi v, f x := by
    simp only [CostMechanism.utility, archerTardosMechanism, archerTardosPayment, f,
      Function.update_self, Function.update_idem]
    ring
  rw [hu_c, hu_v]
  rcases le_total v (c i) with hvc | hcv
  · rw [setIntegral_Ioi_split hvc (hint c hc i v hv)]
    linarith [(setIntegral_Ioc_bounds_of_antitoneOn (hq c hc i) hv hvc
      ((hint c hc i v hv).mono_set Set.Ioc_subset_Ioi_self)).1]
  · rw [setIntegral_Ioi_split hcv (hint c hc i (c i) (hc i))]
    linarith [(setIntegral_Ioc_bounds_of_antitoneOn (hq c hc i) (hc i) hcv
      ((hint c hc i (c i) (hc i)).mono_set Set.Ioc_subset_Ioi_self)).2]

/-- Truthful utility under Archer–Tardos payments equals the tail integral
`∫ x in Ioi (c i), q (update c i x) i`. -/
theorem utility_archerTardosMechanism [DecidableEq ι] (q : (ι → ℝ) → ι → ℝ) (i : ι)
    (c : ι → ℝ) :
    (archerTardosMechanism q).utility i (c i) c =
      ∫ x in Set.Ioi (c i), q (Function.update c i x) i := by
  simp only [CostMechanism.utility, archerTardosMechanism, archerTardosPayment]
  ring

/-- With nonnegative work, Archer–Tardos payments are individually rational. -/
theorem archerTardosMechanism_isIR [DecidableEq ι] {q : (ι → ℝ) → ι → ℝ}
    (hq0 : ∀ c ∈ posCosts, ∀ i, 0 ≤ q c i) :
    (archerTardosMechanism q).IsIR := by
  intro c hc i
  rw [utility_archerTardosMechanism]
  exact setIntegral_nonneg measurableSet_Ioi fun x hx =>
    hq0 _ (update_mem_posCosts hc i ((hc i).trans hx)) i

/-- With nonnegative work, Archer–Tardos payments are nonnegative on positive cost profiles. -/
theorem archerTardosPayment_nonneg [DecidableEq ι] {q : (ι → ℝ) → ι → ℝ}
    (hq0 : ∀ c ∈ posCosts, ∀ i, 0 ≤ q c i) {c : ι → ℝ} (hc : c ∈ posCosts) (i : ι) :
    0 ≤ archerTardosPayment q c i :=
  add_nonneg (mul_nonneg (hc i).le (hq0 c hc i))
    (utility_archerTardosMechanism q i c ▸ archerTardosMechanism_isIR hq0 c hc i)

/-- Finite-interval payment identity for any DSIC cost mechanism: on `0 < a ≤ b`,
`(p(a) - a q(a)) - (p(b) - b q(b)) = ∫ x in Ioc a b, q(x)`. -/
theorem CostMechanism.IsDSIC.utility_sub_utility_eq_integral [DecidableEq ι] {M : CostMechanism ι}
    (hM : M.IsDSIC) {c : ι → ℝ} (hc : c ∈ posCosts) (i : ι) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    M.utility i a (Function.update c i a) - M.utility i b (Function.update c i b) =
      ∫ x in Set.Ioc a b, M.work (Function.update c i x) i := by
  set f : ℝ → ℝ := fun x => M.work (Function.update c i x) i
  set u : ℝ → ℝ := fun x => M.utility i x (Function.update c i x)
  have hf_anti : AntitoneOn f (Set.Ioi 0) := hM.isAntitoneWork c hc i
  have hf_int (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) : IntegrableOn f (Set.Ioc x y) volume :=
    (hf_anti.mono fun _ ht =>
      ha.trans_le (hax.trans (Set.uIcc_of_le hxy ▸ ht).1)).intervalIntegrable.1
  set φ : ℝ → ℝ := fun v => u v + ∫ x in Set.Ioc a v, f x
  have hconst : φ b = φ a := by
    refine Cslib.GameTheory.SingleParameter.eq_of_abs_sub_le_mul_sub (f := fun x => -f x) hab
      fun z y haz hzy _ => ?_
    have hz : 0 < z := ha.trans_le haz
    have hy : 0 < y := hz.trans_le hzy
    have h1 := hM (Function.update c i y) (update_mem_posCosts hc i hy) i z hz
    have h2 := hM (Function.update c i z) (update_mem_posCosts hc i hz) i y hy
    simp only [CostMechanism.utility, Function.update_idem] at h1 h2
    have hsplit : ∫ x in Set.Ioc a y, f x =
        (∫ x in Set.Ioc a z, f x) + ∫ x in Set.Ioc z y, f x := by
      rw [← Set.Ioc_union_Ioc_eq_Ioc haz hzy,
        setIntegral_union (Set.Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc
          (hf_int a z le_rfl haz) (hf_int z y haz hzy)]
    obtain ⟨hI1, hI2⟩ := setIntegral_Ioc_bounds_of_antitoneOn hf_anti hz hzy (hf_int z y haz hzy)
    simp only [φ, u, CostMechanism.utility]
    rw [hsplit, abs_le]
    exact ⟨by nlinarith, by nlinarith⟩
  simp only [φ, Set.Ioc_self, Measure.restrict_empty, integral_zero_measure, add_zero] at hconst
  linarith

private theorem tendsto_mul_zero_of_antitoneOn_integrableOn {f : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hnonneg : ∀ x > 0, 0 ≤ f x) (hf : AntitoneOn f (Set.Ioi 0))
    (hint : IntegrableOn f (Set.Ioi a) volume) :
    Tendsto (fun b => b * f b) atTop (𝓝 0) := by
  have htail : Tendsto (fun b => ∫ x in Set.Ioi (b / 2), f x) atTop (𝓝 0) := by
    refine (sub_self (∫ x in Set.Ioi a, f x) ▸ tendsto_const_nhds.sub
      ((intervalIntegral_tendsto_integral_Ioi a hint tendsto_id).comp
        (tendsto_id.atTop_div_const zero_lt_two))).congr' ?_
    filter_upwards [eventually_ge_atTop (2 * a)] with b hb
    have hab2 : a ≤ b / 2 := by linarith
    simp only [Function.comp_apply, id_eq, intervalIntegral.integral_of_le hab2,
      setIntegral_Ioi_split hab2 hint]
    ring
  refine squeeze_zero' ?_ ?_ (by simpa only [mul_zero] using htail.const_mul 2)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
    exact mul_nonneg hb.le (hnonneg b hb)
  · filter_upwards [eventually_ge_atTop (2 * a)] with b hb
    have hb2 : 0 < b / 2 := by linarith
    have hab2 : a ≤ b / 2 := by linarith
    have hIoc := (setIntegral_Ioc_bounds_of_antitoneOn hf hb2 (by linarith : b / 2 ≤ b)
      (hint.mono_set (Set.Ioc_subset_Ioi_self.trans (Set.Ioi_subset_Ioi hab2)))).1
    have hsub : ∫ x in Set.Ioc (b / 2) b, f x ≤ ∫ x in Set.Ioi (b / 2), f x :=
      setIntegral_mono_set (hint.mono_set (Set.Ioi_subset_Ioi hab2))
        (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => hnonneg x (hb2.trans hx))
        (Eventually.of_forall Set.Ioc_subset_Ioi_self)
    linarith

/-- **Archer–Tardos payment uniqueness** ([ArcherTardos2001];
[NisanRoughgardenTardosVazirani2007], Chapter 12, Theorem 12.2, locator not verified against
primary PDF): for any DSIC cost mechanism with nonnegative work, integrable tail, and vanishing
asymptotic payment `lim_{x → ∞} pᵢ(update c i x) = 0`, the payment equals `archerTardosPayment`. -/
theorem CostMechanism.IsDSIC.payment_eq_archerTardosPayment [DecidableEq ι] {M : CostMechanism ι}
    (hM : M.IsDSIC) (hq0 : ∀ c ∈ posCosts, ∀ i, 0 ≤ M.work c i)
    (hint : HasIntegrableTail M.work) {c : ι → ℝ} (hc : c ∈ posCosts) (i : ι)
    (hlim : Tendsto (fun x => M.payment (Function.update c i x) i) atTop (𝓝 0)) :
    M.payment c i = archerTardosPayment M.work c i := by
  set f : ℝ → ℝ := fun x => M.work (Function.update c i x) i
  have hf_int : IntegrableOn f (Set.Ioi (c i)) volume := hint c hc i (c i) (hc i)
  have hmul : Tendsto (fun b => b * f b) atTop (𝓝 0) :=
    tendsto_mul_zero_of_antitoneOn_integrableOn (hc i)
      (fun x hx => hq0 _ (update_mem_posCosts hc i hx) i) (hM.isAntitoneWork c hc i) hf_int
  have hconst_lim : Tendsto (fun _ : ℝ => M.utility i (c i) c) atTop
      (𝓝 (∫ x in Set.Ioi (c i), f x)) := by
    refine (add_zero (∫ x in Set.Ioi (c i), f x) ▸
      (intervalIntegral_tendsto_integral_Ioi (c i) hf_int tendsto_id).add
        (by simpa only [CostMechanism.utility, sub_zero] using hlim.sub hmul)).congr' ?_
    filter_upwards [eventually_ge_atTop (c i)] with b hb
    have hid := hM.utility_sub_utility_eq_integral hc i (hc i) hb
    rw [Function.update_eq_self] at hid
    simp only [id_eq, intervalIntegral.integral_of_le hb, CostMechanism.utility, f] at hid ⊢
    linarith
  have heq := tendsto_nhds_unique tendsto_const_nhds hconst_lim
  simp only [CostMechanism.utility, archerTardosPayment] at heq ⊢
  linarith

end ArcherTardos

/-! ### Truthful Exact Makespan Minimization on Uniformly Related Machines -/

section RelatedMachines

variable {M J : Type*} [DecidableEq M] [Fintype J]

/-- Total job weight (work) assigned to machine `i` under schedule `a : J → M`. -/
@[expose] def work (w : J → ℝ) (a : J → M) (i : M) : ℝ :=
  ∑ j with a j = i, w j

theorem work_nonneg {w : J → ℝ} (hw : ∀ j, 0 ≤ w j) (a : J → M) (i : M) :
    0 ≤ work w a i :=
  Finset.sum_nonneg fun j _ => hw j

variable [Fintype M] [Nonempty M]

/-- Makespan `max_i cᵢ * work w a i` of schedule `a` on related machines with unit costs `c`
(where machine `i` has speed `sᵢ = 1 / cᵢ`). -/
@[expose] def relatedMakespan (w : J → ℝ) (c : M → ℝ) (a : J → M) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => c i * work w a i

theorem cost_mul_work_le_relatedMakespan (w : J → ℝ) (c : M → ℝ) (a : J → M) (i : M) :
    c i * work w a i ≤ relatedMakespan w c a :=
  Finset.le_sup' (fun k => c k * work w a k) (Finset.mem_univ i)

theorem relatedMakespan_le_iff (w : J → ℝ) (c : M → ℝ) (a : J → M) {B : ℝ} :
    relatedMakespan w c a ≤ B ↔ ∀ i : M, c i * work w a i ≤ B := by
  simp only [relatedMakespan, Finset.sup'_le_iff, Finset.mem_univ, forall_const]

variable [DecidableEq J]

/-- Optimal makespan over all `J → M` schedules on related machines with unit costs `c`. -/
@[expose] noncomputable def optRelatedMakespan (w : J → ℝ) (c : M → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty fun a : J → M => relatedMakespan w c a

theorem optRelatedMakespan_le (w : J → ℝ) (c : M → ℝ) (a : J → M) :
    optRelatedMakespan w c ≤ relatedMakespan w c a :=
  Finset.inf'_le (fun a : J → M => relatedMakespan w c a) (Finset.mem_univ a)

/-- Volume lower bound on related-machine optimal makespan:
`∑ⱼ wⱼ ≤ optRelatedMakespan w c * ∑ᵢ (1 / cᵢ)`. -/
theorem sum_weight_le_optRelatedMakespan_mul_sum_inv {w : J → ℝ} {c : M → ℝ}
    (hc : c ∈ posCosts) :
    ∑ j : J, w j ≤ optRelatedMakespan w c * ∑ i : M, (c i)⁻¹ := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty (α := J → M)) (fun a => relatedMakespan w c a)
  rw [optRelatedMakespan, ha,
    ← Finset.sum_fiberwise_of_maps_to (g := a) (fun j _ => Finset.mem_univ (a j)) w,
    Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    ((le_div_iff₀' (hc i)).2 (cost_mul_work_le_relatedMakespan w c a i)).trans_eq
      (div_eq_mul_inv _ _)

private noncomputable def optSchedules (w : J → ℝ) (c : M → ℝ) : Finset (J → M) :=
  Finset.univ.filter fun a => relatedMakespan w c a = optRelatedMakespan w c

private theorem optSchedules_nonempty (w : J → ℝ) (c : M → ℝ) :
    (optSchedules w c).Nonempty := by
  obtain ⟨a, -, ha⟩ := Finset.exists_mem_eq_inf'
    (Finset.univ_nonempty (α := J → M)) (fun a => relatedMakespan w c a)
  exact ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ a, ha.symm⟩⟩

/-- Exact makespan minimization with fixed cost-independent tie-breaking given by a `LinearOrder`
on `J → M` ([ArcherTardos2001]; [NisanRoughgardenTardosVazirani2007], Chapter 12, Exercise 12.1,
locator not verified against primary PDF). -/
noncomputable def lexOptAlloc [LinearOrder (J → M)] (w : J → ℝ) (c : M → ℝ) : J → M :=
  (optSchedules w c).min' (optSchedules_nonempty w c)

theorem lexOptAlloc_isOptimal [LinearOrder (J → M)] (w : J → ℝ) (c : M → ℝ) :
    relatedMakespan w c (lexOptAlloc w c) = optRelatedMakespan w c := by
  exact (Finset.mem_filter.1 (Finset.min'_mem (optSchedules w c) (optSchedules_nonempty w c))).2

theorem lexOptAlloc_le_of_optimal [LinearOrder (J → M)] (w : J → ℝ) (c : M → ℝ) {a : J → M}
    (ha : relatedMakespan w c a = optRelatedMakespan w c) :
    lexOptAlloc w c ≤ a :=
  Finset.min'_le _ _ (Finset.mem_filter.2 ⟨Finset.mem_univ a, ha⟩)

/-- **Monotonicity of lexicographically tie-broken exact makespan minimization**
([ArcherTardos2001]; [NisanRoughgardenTardosVazirani2007], Chapter 12, Exercise 12.1, locator not
verified against primary PDF): for any fixed cost-independent linear order on schedules, the work
assigned to each machine is antitone in its unit cost (equivalently, monotone in its speed). -/
theorem lexOptWork_isAntitoneWork [LinearOrder (J → M)] {w : J → ℝ} (hw : ∀ j, 0 ≤ w j) :
    IsAntitoneWork (fun c : M → ℝ => work w (lexOptAlloc w c)) := by
  intro c hc i x hx y hy hxy
  rcases hxy.eq_or_lt with rfl | hlt
  · exact le_rfl
  let cx := Function.update c i x
  let cy := Function.update c i y
  let ax := lexOptAlloc w cx
  let ay := lexOptAlloc w cy
  change work w ay i ≤ work w ax i
  by_contra hnot
  have hwork_lt : work w ax i < work w ay i := lt_of_not_ge hnot
  -- Every schedule's makespan at `cx` is at most its makespan at `cy`.
  have hmono (a : J → M) : relatedMakespan w cx a ≤ relatedMakespan w cy a :=
    (relatedMakespan_le_iff w cx a).2 fun k => by
      rcases eq_or_ne k i with rfl | hki
      · calc cx k * work w a k
          _ = x * work w a k := by simp only [cx, Function.update_self]
          _ ≤ y * work w a k := mul_le_mul_of_nonneg_right hlt.le (work_nonneg hw a k)
          _ = cy k * work w a k := by simp only [cy, Function.update_self]
          _ ≤ relatedMakespan w cy a := cost_mul_work_le_relatedMakespan w cy a k
      · calc cx k * work w a k
          _ = cy k * work w a k := by simp only [cx, cy, Function.update_of_ne hki]
          _ ≤ relatedMakespan w cy a := cost_mul_work_le_relatedMakespan w cy a k
  have hopt_x : relatedMakespan w cx ax = optRelatedMakespan w cx := lexOptAlloc_isOptimal w cx
  have hopt_y : relatedMakespan w cy ay = optRelatedMakespan w cy := lexOptAlloc_isOptimal w cy
  have hax_le_ay : relatedMakespan w cx ax ≤ relatedMakespan w cx ay :=
    hopt_x.trans_le (optRelatedMakespan_le w cx ay)
  have hay_le_ax_cy : relatedMakespan w cy ay ≤ relatedMakespan w cy ax :=
    hopt_y.trans_le (optRelatedMakespan_le w cy ax)
  -- Show `relatedMakespan w cy ax ≤ relatedMakespan w cy ay`:
  -- machine `i` has strictly less completion time under `ax` than under `ay` at cost `y`,
  -- and every other machine `k ≠ i` has the same cost under `cx` and `cy`.
  have hax_cy_i : cy i * work w ax i < relatedMakespan w cy ay :=
    (mul_lt_mul_of_pos_left hwork_lt
      (by simpa only [cy, Function.update_self] using Set.mem_Ioi.1 hy)).trans_le
      (cost_mul_work_le_relatedMakespan w cy ay i)
  have hax_cy_le : relatedMakespan w cy ax ≤ relatedMakespan w cy ay :=
    (relatedMakespan_le_iff w cy ax).2 fun k => by
      rcases eq_or_ne k i with rfl | hki
      · exact hax_cy_i.le
      · calc cy k * work w ax k
          _ = cx k * work w ax k := by simp only [cx, cy, Function.update_of_ne hki]
          _ ≤ relatedMakespan w cx ax := cost_mul_work_le_relatedMakespan w cx ax k
          _ ≤ relatedMakespan w cx ay := hax_le_ay
          _ ≤ relatedMakespan w cy ay := hmono ay
  have hax_opt_cy : relatedMakespan w cy ax = optRelatedMakespan w cy :=
    (le_antisymm hax_cy_le hay_le_ax_cy).trans hopt_y
  -- Now `ax` attains `relatedMakespan w cy ax = relatedMakespan w cy ay` on some machine `k₀`.
  -- That `k₀` cannot be `i` (strict inequality above), so `k₀ ≠ i`, forcing
  -- `relatedMakespan w cx ay = optRelatedMakespan w cx` as well!
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := M))
    (fun k => cy k * work w ax k)
  change relatedMakespan w cy ax = cy k₀ * work w ax k₀ at hk₀
  have hk₀_ne : k₀ ≠ i := fun h =>
    hax_cy_i.ne ((h ▸ hk₀).symm.trans (hax_opt_cy.trans hopt_y.symm))
  have hay_cx_le : relatedMakespan w cx ay ≤ relatedMakespan w cx ax := by
    calc
      relatedMakespan w cx ay ≤ relatedMakespan w cy ay := hmono ay
      _ = cx k₀ * work w ax k₀ := by
        rw [hopt_y, ← hax_opt_cy, hk₀]
        simp only [cx, cy, Function.update_of_ne hk₀_ne]
      _ ≤ relatedMakespan w cx ax := cost_mul_work_le_relatedMakespan w cx ax k₀
  have hay_opt_cx : relatedMakespan w cx ay = optRelatedMakespan w cx :=
    (le_antisymm hay_cx_le hax_le_ay).trans hopt_x
  exact lt_irrefl _ (le_antisymm (lexOptAlloc_le_of_optimal w cx hay_opt_cx)
    (lexOptAlloc_le_of_optimal w cy hax_opt_cy) ▸ hwork_lt)

/-- When there are at least two machines (`[Nontrivial M]`), any machine whose unit cost exceeds a
finite threshold receives zero total work under `lexOptAlloc`. -/
theorem lexOptWork_eq_zero_of_large_cost [LinearOrder (J → M)] [Nontrivial M] {w : J → ℝ}
    (hw : ∀ j, 0 ≤ w j) {c : M → ℝ} (hc : c ∈ posCosts) (i : M) :
    ∃ C : ℝ, ∀ x : ℝ, C < x → work w (lexOptAlloc w (Function.update c i x)) i = 0 := by
  obtain ⟨k, hki⟩ := exists_ne i
  let posJobs : Finset J := Finset.univ.filter fun j => 0 < w j
  by_cases hne : posJobs.Nonempty
  · let wMin : ℝ := posJobs.inf' hne w
    have hwMin_pos : 0 < wMin := (Finset.lt_inf'_iff hne).2 fun _ hj => (Finset.mem_filter.1 hj).2
    let W : ℝ := ∑ j : J, w j
    refine ⟨(c k * W) / wMin, fun x hx => ?_⟩
    set cx := Function.update c i x
    let aAllK : J → M := fun _ => k
    have hopt_le : optRelatedMakespan w cx ≤ c k * W := by
      refine (optRelatedMakespan_le w cx aAllK).trans ((relatedMakespan_le_iff w cx aAllK).2
        fun m => ?_)
      rcases eq_or_ne m k with rfl | hmk
      · simp only [cx, Function.update_of_ne hki, work, aAllK, Finset.filter_true, W, le_refl]
      · rw [work, Finset.filter_false_of_mem fun _ _ => Ne.symm hmk, Finset.sum_empty, mul_zero]
        exact mul_nonneg (hc k).le (Finset.sum_nonneg fun j _ => hw j)
    have hle_opt : x * work w (lexOptAlloc w cx) i ≤ c k * W :=
      calc x * work w (lexOptAlloc w cx) i
        _ = cx i * work w (lexOptAlloc w cx) i := by simp only [cx, Function.update_self]
        _ ≤ relatedMakespan w cx (lexOptAlloc w cx) :=
              cost_mul_work_le_relatedMakespan w cx (lexOptAlloc w cx) i
        _ = optRelatedMakespan w cx := lexOptAlloc_isOptimal w cx
        _ ≤ c k * W := hopt_le
    refine Finset.sum_eq_zero fun j hj => ?_
    by_contra hne0
    have hwj_pos : 0 < w j := lt_of_le_of_ne (hw j) (Ne.symm hne0)
    have hwMin_le : wMin ≤ work w (lexOptAlloc w cx) i :=
      (Finset.inf'_le w (Finset.mem_filter.2 ⟨Finset.mem_univ j, hwj_pos⟩)).trans
        (Finset.single_le_sum (fun j' _ => hw j') hj)
    have hgt : c k * W < x * wMin := (div_lt_iff₀ hwMin_pos).1 hx
    have hx_pos : 0 < x := pos_of_mul_pos_left
      ((mul_nonneg (hc k).le (Finset.sum_nonneg fun _ _ => hw _)).trans_lt hgt) hwMin_pos.le
    linarith [mul_le_mul_of_nonneg_left hwMin_le hx_pos.le]
  · refine ⟨0, fun x _ => Finset.sum_eq_zero fun j _ => le_antisymm ?_ (hw j)⟩
    exact not_lt.1 fun hpos => hne ⟨j, Finset.mem_filter.2 ⟨Finset.mem_univ j, hpos⟩⟩

/-- With at least two machines, the work tail of `lexOptAlloc` is integrable on every `(a, ∞)`. -/
theorem lexOptWork_hasIntegrableTail [LinearOrder (J → M)] [Nontrivial M] {w : J → ℝ}
    (hw : ∀ j, 0 ≤ w j) :
    HasIntegrableTail (fun c : M → ℝ => work w (lexOptAlloc w c)) := by
  intro c hc i a ha
  obtain ⟨C, hC⟩ := lexOptWork_eq_zero_of_large_cost hw hc i
  set B := max a C
  have haB : a ≤ B := le_max_left a C
  have hanti : AntitoneOn (fun x => work w (lexOptAlloc w (Function.update c i x)) i)
      (Set.Ioi 0) := lexOptWork_isAntitoneWork hw c hc i
  have hIoc : IntegrableOn (fun x => work w (lexOptAlloc w (Function.update c i x)) i)
      (Set.Ioc a B) volume :=
    (hanti.mono fun t ht => ha.trans_le (Set.uIcc_of_le haB ▸ ht).1).intervalIntegrable.1
  have hIoi : IntegrableOn (fun x => work w (lexOptAlloc w (Function.update c i x)) i)
      (Set.Ioi B) volume :=
    (integrableOn_zero (μ := volume) (s := Set.Ioi B)).congr_fun
      (fun x hx => (hC x ((le_max_right a C).trans_lt hx)).symm) measurableSet_Ioi
  exact Set.Ioc_union_Ioi_eq_Ioi haB ▸ hIoc.union hIoi

/-- The **Archer–Tardos exact related-machine scheduling mechanism** combining `lexOptAlloc`
with `archerTardosPayment` ([ArcherTardos2001]; [NisanRoughgardenTardosVazirani2007], Chapter 12,
Exercise 12.1, locator not verified against primary PDF). -/
@[expose] noncomputable def lexOptMechanism [LinearOrder (J → M)] (w : J → ℝ) :
    CostMechanism M :=
  archerTardosMechanism fun c => work w (lexOptAlloc w c)

/-- **Truthfulness of `lexOptMechanism`**: for `m ≥ 2` related machines and nonnegative job
weights, exact makespan minimization with fixed tie-breaking and Archer–Tardos payments is DSIC. -/
theorem lexOptMechanism_isDSIC [LinearOrder (J → M)] [Nontrivial M] {w : J → ℝ}
    (hw : ∀ j, 0 ≤ w j) :
    (lexOptMechanism (M := M) (J := J) w).IsDSIC :=
  archerTardosMechanism_isDSIC (lexOptWork_isAntitoneWork hw) (lexOptWork_hasIntegrableTail hw)

/-- **Individual rationality of `lexOptMechanism`**. -/
theorem lexOptMechanism_isIR [LinearOrder (J → M)] {w : J → ℝ} (hw : ∀ j, 0 ≤ w j) :
    (lexOptMechanism (M := M) (J := J) w).IsIR :=
  archerTardosMechanism_isIR fun c _ i => work_nonneg hw (lexOptAlloc w c) i

end RelatedMachines

end Cslib.GameTheory.Mechanism.RelatedScheduling
