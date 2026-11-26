/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Online mechanism design: model, monotonicity, and critical values

In an *online mechanism design* environment ([Parkes2007], §16.2–§16.3.1, locators not verified
against primary PDF), each agent `i : ι` has a single-valued online type
`θᵢ = ⟨arrival, departure, value⟩` over a linearly ordered time domain `τ`, representing arrival
period `aᵢ`, departure period `dᵢ` (`aᵢ ≤ dᵢ`), and nonnegative value `vᵢ ≥ 0` for receiving an
allocation at some period `t ∈ [aᵢ, dᵢ]`. A deterministic direct-revelation online policy `π`
assigns each agent either `none` (unallocated) or `some t` with `t ∈ [aᵢ, dᵢ]` (window feasibility).
A policy is *causal* (`Policy.IsCausal`) when allocation at period `t` depends only on agents
whose reported arrival is at most `t`.

Unlike static single-parameter auctions (`Cslib.GameTheory.SingleParameter`), agents can misreport
arrival and departure times as well as values, subject to physical misreport constraints
([Parkes2007], Def. 16.4, locator not verified against primary PDF):

* **No early arrival and no late departure** (`AgentType.IsValidMisreport`): `aᵢ ≤ a'ᵢ` and
  `d'ᵢ ≤ dᵢ`, i.e., `[a'ᵢ, d'ᵢ] ⊆ [aᵢ, dᵢ]`.
* **No early arrival with arbitrary departure** (`AgentType.NoEarlyArrival`): `aᵢ ≤ a'ᵢ`, with
  `d'ᵢ` unrestricted (an allocation at `t > dᵢ` yields zero value to the agent).

The online *critical value* `π.criticalValue θ i a d had : ℝ≥0∞` ([Parkes2007], Def. 16.10,
locator not verified against primary PDF) is the infimum of values `r ≥ 0` at which agent `i` wins
on interval `[a, d]` given others' reports `θ₋ᵢ` (with `⊤` when `i` never wins). A deterministic
policy is *online-monotone* (`Policy.IsMonotone`, Def. 16.11) if winning is preserved under
earlier arrival, later departure, and strictly higher value (`a₂ ≤ a₁`, `d₁ ≤ d₂`, `v₁ < v₂`).

## Main definitions

* `AgentType`: online agent type `(arrival, departure, value)` with `arrival ≤ departure` and
  `0 ≤ value`.
* `AgentType.InWindow`, `AgentType.IsValidMisreport`, `AgentType.NoEarlyArrival`,
  `AgentType.realizedValue`.
* `Policy`, `Policy.IsCausal`, `Policy.IsMonotone`, `Policy.IsLateAllocating`.
* `Policy.criticalValue`, `Policy.criticalPayment`, `Policy.criticalMechanism`,
  `Policy.IsImplementable`.
* `Mechanism`, `Mechanism.utility`, `Mechanism.IsDSIC`, `Mechanism.IsDSICNoEarlyArrival`,
  `Mechanism.IsIR`, `Mechanism.IsNPT`, `Mechanism.IsLoserZero`.
* `welfare`, `revenue`: realized social welfare of an allocation map and total seller revenue of
  an online mechanism.

## Main results

* `welfare_nonneg`, `welfare_eq_sum_filter`, `revenue_nonneg`: nonnegativity of realized social
  welfare and NPT revenue, and sum characterization of feasible allocation welfare.

* `Policy.criticalValue_update`, `Policy.criticalValue_antitone`: for a monotone policy, the
  critical value is independent of agent `i`'s report and nonincreasing as the interval `[a, d]`
  widens ([Parkes2007], Lemma 16.12, locator not verified against primary PDF).
* `Policy.criticalMechanism_isDSIC`, `Policy.criticalMechanism_isIR`,
  `Policy.criticalMechanism_isNPT`, `Policy.criticalMechanism_isLoserZero`: pairing any monotone
  deterministic online policy with critical-value payments yields a DSIC, individually rational,
  no-positive-transfer mechanism with zero loser payments under no-early-arrival and
  no-late-departure misreports ([Parkes2007], Theorem 16.13, locator not verified against primary
  PDF).
* `Policy.criticalMechanism_isDSICNoEarlyArrival`: if a monotone policy also allocates winners at
  their reported departure (`IsLateAllocating`, "monotonic-late"), its critical mechanism is DSIC
  even under arbitrary departure misreports ([Parkes2007], §16.3.1, p. 420, locator not verified
  against primary PDF).
* `Mechanism.IsDSIC.payment_eq_criticalPayment`: critical payments are the unique DSIC, IR, NPT,
  loser-zero payment rule ([Parkes2007], Lemma 16.14, locator not verified against primary PDF).
* `Mechanism.IsDSIC.isMonotone`: every deterministic online policy implemented by a DSIC, IR,
  loser-zero mechanism is monotone ([Parkes2007], Theorem 16.15, locator not verified against
  primary PDF).
* `Policy.isImplementable_iff_isMonotone`: exact equivalence between online implementability and
  monotonicity.

## References

* [D. C. Parkes, *Online Mechanisms*][Parkes2007]
* [R. Lavi and N. Nisan, *Competitive Analysis of Incentive Compatible On-Line
  Auctions*][LaviNisan2000]
* [M. T. Hajiaghayi, R. Kleinberg, and D. C. Parkes, *Adaptive Limited-Supply Online
  Auctions*][HajiaghayiKleinbergParkes2004]
-/

open scoped BigOperators ENNReal

public section

namespace Cslib.GameTheory.OnlineMechanism

/-- A single-valued online agent type `(aᵢ, dᵢ, vᵢ)` over a preordered time domain `τ`:
arrival time `arrival`, departure time `departure` with `arrival ≤ departure`, and nonnegative
valuation `value` for receiving an allocation during `[arrival, departure]`
([Parkes2007], §16.2, Def. 16.8, locator not verified against primary PDF). -/
structure AgentType (τ : Type*) [Preorder τ] where
  /-- The agent's arrival period `aᵢ`. -/
  arrival : τ
  /-- The agent's departure period `dᵢ`. -/
  departure : τ
  /-- The agent's nonnegative value `vᵢ` for being allocated within `[aᵢ, dᵢ]`. -/
  value : ℝ
  /-- Arrival occurs no later than departure (`aᵢ ≤ dᵢ`). -/
  arrival_le_departure : arrival ≤ departure
  /-- Valuation is nonnegative (`0 ≤ vᵢ`). -/
  value_nonneg : 0 ≤ value

namespace AgentType

variable {τ : Type*} [Preorder τ]

/-- Period `t` lies inside agent `θ`'s active window `[θ.arrival, θ.departure]`. -/
@[expose] def InWindow (θ : AgentType τ) (t : τ) : Prop :=
  θ.arrival ≤ t ∧ t ≤ θ.departure

/-- Limited misreport under *no early arrival* and *no late departure*: a reported type `θ_rep`
is a valid misreport for true type `θ_true` when `[a', d'] ⊆ [a, d]`
([Parkes2007], Def. 16.4, locator not verified against primary PDF). -/
@[expose] def IsValidMisreport (θ_true θ_rep : AgentType τ) : Prop :=
  θ_true.arrival ≤ θ_rep.arrival ∧ θ_rep.departure ≤ θ_true.departure

/-- Limited misreport under *no early arrival* with *arbitrary departure*: `a ≤ a'`
([Parkes2007], Def. 16.4, locator not verified against primary PDF). -/
@[expose] def NoEarlyArrival (θ_true θ_rep : AgentType τ) : Prop :=
  θ_true.arrival ≤ θ_rep.arrival

theorem isValidMisreport_refl (θ : AgentType τ) : θ.IsValidMisreport θ :=
  ⟨le_rfl, le_rfl⟩

theorem IsValidMisreport.noEarlyArrival {θ₁ θ₂ : AgentType τ} (h : θ₁.IsValidMisreport θ₂) :
    θ₁.NoEarlyArrival θ₂ :=
  h.1

theorem InWindow.of_isValidMisreport {θ_true θ_rep : AgentType τ} {t : τ}
    (h : θ_true.IsValidMisreport θ_rep) (ht : θ_rep.InWindow t) : θ_true.InWindow t :=
  ⟨h.1.trans ht.1, ht.2.trans h.2⟩

open Classical in
/-- The value realized by an agent with true type `θ` from an allocation outcome `o : Option τ`:
`θ.value` if allocated at a period `t ∈ [θ.arrival, θ.departure]`, and `0` otherwise. -/
@[expose] noncomputable def realizedValue (θ : AgentType τ) (o : Option τ) : ℝ :=
  match o with
  | none => 0
  | some t => if θ.InWindow t then θ.value else 0

@[simp]
theorem realizedValue_none (θ : AgentType τ) : θ.realizedValue none = 0 := rfl

theorem realizedValue_some_of_inWindow {θ : AgentType τ} {t : τ} (ht : θ.InWindow t) :
    θ.realizedValue (some t) = θ.value := ite_eq_left ht

theorem realizedValue_some_of_not_inWindow {θ : AgentType τ} {t : τ} (ht : ¬ θ.InWindow t) :
    θ.realizedValue (some t) = 0 := ite_eq_right ht

theorem realizedValue_nonneg (θ : AgentType τ) (o : Option τ) : 0 ≤ θ.realizedValue o := by
  cases o <;> simp only [realizedValue, le_refl]
  split_ifs <;> simp [θ.value_nonneg]

theorem realizedValue_le_value (θ : AgentType τ) (o : Option τ) :
    θ.realizedValue o ≤ θ.value := by
  cases o <;> simp only [realizedValue, θ.value_nonneg]
  split_ifs <;> simp [θ.value_nonneg]

end AgentType

/-- A deterministic direct-revelation online allocation policy for agents `ι` over time domain `τ`.
On reported profile `θ`, agent `i` is either unallocated (`none`) or allocated at a period
`some t` inside its reported window `[aᵢ, dᵢ]` ([Parkes2007], Def. 16.2, locator not verified
against primary PDF). -/
structure Policy (ι τ : Type*) [Preorder τ] where
  /-- Allocation outcome for each agent: `some t` if allocated at period `t`, `none` otherwise. -/
  alloc : (ι → AgentType τ) → ι → Option τ
  /-- Window feasibility: an agent is only allocated within its reported active window. -/
  alloc_in_window : ∀ θ i t, alloc θ i = some t → (θ i).InWindow t

/-- A deterministic direct-revelation online mechanism pairs an online allocation policy with a
real-valued payment rule ([Parkes2007], Def. 16.2, locator not verified against primary PDF). -/
structure Mechanism (ι τ : Type*) [Preorder τ] where
  /-- The underlying deterministic online allocation policy. -/
  policy : Policy ι τ
  /-- Payment `pᵢ(θ)` charged to agent `i` on reported profile `θ`. -/
  payment : (ι → AgentType τ) → ι → ℝ

namespace Policy

variable {ι τ : Type*} [Preorder τ]

/-- Online causality: whether agent `i` is allocated at period `t` depends only on the reports of
agents who have arrived by period `t` ([Parkes2007], §16.2, Def. 16.2, locator not verified
against primary PDF). -/
@[expose] def IsCausal (π : Policy ι τ) : Prop :=
  ∀ (t : τ) (θ θ' : ι → AgentType τ),
    (∀ j, (θ j).arrival ≤ t ∨ (θ' j).arrival ≤ t → θ j = θ' j) →
    ∀ i, (π.alloc θ i = some t ↔ π.alloc θ' i = some t)

/-- Online monotonicity of a deterministic policy: winning is preserved by reporting an earlier
(or equal) arrival, a later (or equal) departure, and a strictly higher value
([Parkes2007], Def. 16.11, locator not verified against primary PDF). -/
@[expose] def IsMonotone [DecidableEq ι] (π : Policy ι τ) : Prop :=
  ∀ (i : ι) (θ : ι → AgentType τ) (θ₁ θ₂ : AgentType τ),
    θ₂.arrival ≤ θ₁.arrival → θ₁.departure ≤ θ₂.departure → θ₁.value < θ₂.value →
    (π.alloc (Function.update θ i θ₁) i).isSome →
    (π.alloc (Function.update θ i θ₂) i).isSome

/-- A deterministic policy is *late-allocating* if every allocated agent receives its allocation
at its reported departure period (`t = dᵢ`). Together with `IsMonotone`, this yields the
*monotonic-late* condition of [Parkes2007], §16.3.1, p. 420 (locator not verified against primary
PDF). -/
@[expose] def IsLateAllocating (π : Policy ι τ) : Prop :=
  ∀ θ i t, π.alloc θ i = some t → t = (θ i).departure

/-- The online critical value `vᶜ_{(a, d)}(θ₋ᵢ) ∈ ℝ≥0∞` of policy `π` for agent `i` on reported
window `[a, d]` given others' reports `θ₋ᵢ`: the infimum of nonnegative values `r` at which `i`
wins, or `⊤` if `i` never wins on `[a, d]` ([Parkes2007], Def. 16.10, locator not verified against
primary PDF). -/
@[expose] noncomputable def criticalValue [DecidableEq ι] (π : Policy ι τ)
    (θ : ι → AgentType τ) (i : ι) (a d : τ) (had : a ≤ d) : ℝ≥0∞ :=
  sInf {v : ℝ≥0∞ | ∃ (r : ℝ) (hr : 0 ≤ r), ENNReal.ofReal r = v ∧
    (π.alloc (Function.update θ i ⟨a, d, r, had, hr⟩) i).isSome}

/-- The critical-value payment rule associated with `π`: winners pay the real value of their
critical value on their reported window, and unallocated agents pay `0`. -/
@[expose] noncomputable def criticalPayment [DecidableEq ι] (π : Policy ι τ)
    (θ : ι → AgentType τ) (i : ι) : ℝ :=
  if (π.alloc θ i).isSome then
    (π.criticalValue θ i (θ i).arrival (θ i).departure (θ i).arrival_le_departure).toReal
  else 0

/-- The critical-value mechanism pairing policy `π` with `π.criticalPayment`. -/
@[expose] noncomputable def criticalMechanism [DecidableEq ι] (π : Policy ι τ) :
    Mechanism ι τ :=
  ⟨π, π.criticalPayment⟩

section CriticalValue

variable [DecidableEq ι]

/-- The critical value of agent `i` on `[a, d]` is independent of agent `i`'s reported type
([Parkes2007], Lemma 16.12, part 1, locator not verified against primary PDF). -/
theorem criticalValue_update (π : Policy ι τ) (θ : ι → AgentType τ) (i : ι)
    (θ' : AgentType τ) (a d : τ) (had : a ≤ d) :
    π.criticalValue (Function.update θ i θ') i a d had = π.criticalValue θ i a d had := by
  simp only [criticalValue, Function.update_idem]

/-- If agent `i` wins under report `⟨a, d, r, had, hr⟩`, then its critical value on `[a, d]` is at
most `ENNReal.ofReal r`. -/
theorem criticalValue_le_of_isSome {π : Policy ι τ} {θ : ι → AgentType τ} {i : ι}
    {a d : τ} {had : a ≤ d} {r : ℝ} (hr : 0 ≤ r)
    (hwin : (π.alloc (Function.update θ i ⟨a, d, r, had, hr⟩) i).isSome) :
    π.criticalValue θ i a d had ≤ ENNReal.ofReal r :=
  sInf_le ⟨r, hr, rfl, hwin⟩

/-- If agent `i` wins under `θ`, its critical value on its reported window is at most
`ENNReal.ofReal (θ i).value` (and hence finite). -/
theorem criticalValue_le_self {π : Policy ι τ} {θ : ι → AgentType τ} {i : ι}
    (hwin : (π.alloc θ i).isSome) :
    π.criticalValue θ i (θ i).arrival (θ i).departure (θ i).arrival_le_departure ≤
      ENNReal.ofReal (θ i).value :=
  criticalValue_le_of_isSome (θ i).value_nonneg (by rwa [Function.update_eq_self])

/-- For a monotone policy, any nonnegative value strictly above the critical value wins. -/
theorem isSome_of_criticalValue_lt {π : Policy ι τ} (hmono : π.IsMonotone)
    {θ : ι → AgentType τ} {i : ι} {a d : τ} {had : a ≤ d} {r : ℝ} (hr : 0 ≤ r)
    (hlt : π.criticalValue θ i a d had < ENNReal.ofReal r) :
    (π.alloc (Function.update θ i ⟨a, d, r, had, hr⟩) i).isSome := by
  obtain ⟨w, ⟨z, hz, rfl, hwin⟩, hw⟩ := sInf_lt_iff.mp hlt
  exact hmono i θ ⟨a, d, z, had, hz⟩ ⟨a, d, r, had, hr⟩ le_rfl le_rfl
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hz).mp hw) hwin

/-- For a monotone policy, widening the reported window `[a₁, d₁] ⊆ [a₂, d₂]` cannot increase the
critical value ([Parkes2007], Lemma 16.12, part 2, locator not verified against primary PDF). -/
theorem criticalValue_antitone {π : Policy ι τ} (hmono : π.IsMonotone)
    {θ : ι → AgentType τ} {i : ι} {a₁ d₁ a₂ d₂ : τ}
    (had₁ : a₁ ≤ d₁) (had₂ : a₂ ≤ d₂) (ha : a₂ ≤ a₁) (hd : d₁ ≤ d₂) :
    π.criticalValue θ i a₂ d₂ had₂ ≤ π.criticalValue θ i a₁ d₁ had₁ := by
  refine le_sInf fun _ ⟨r, hr, heq, hwin⟩ => heq ▸
    ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hrε : 0 ≤ r + (ε : ℝ) := add_nonneg hr ε.coe_nonneg
  simpa only [ENNReal.ofReal_add hr ε.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
    criticalValue_le_of_isSome hrε (hmono i θ ⟨a₁, d₁, r, had₁, hr⟩
      ⟨a₂, d₂, r + (ε : ℝ), had₂, hrε⟩ ha hd (lt_add_of_pos_right r (NNReal.coe_pos.mpr hε)) hwin)

/-- If `i` wins under `π` on `[a, d]` for every value strictly above `t ≥ 0` and only for values
at least `t`, then `π.criticalValue θ i a d had = ENNReal.ofReal t`. -/
theorem criticalValue_eq_of_threshold {π : Policy ι τ} {θ : ι → AgentType τ} {i : ι}
    {a d : τ} {had : a ≤ d} {t : ℝ} (ht : 0 ≤ t)
    (hwin : ∀ (r : ℝ) (hr : 0 ≤ r), t < r →
      (π.alloc (Function.update θ i ⟨a, d, r, had, hr⟩) i).isSome)
    (hlose : ∀ (r : ℝ) (hr : 0 ≤ r),
      (π.alloc (Function.update θ i ⟨a, d, r, had, hr⟩) i).isSome → t ≤ r) :
    π.criticalValue θ i a d had = ENNReal.ofReal t := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
    have htε : 0 ≤ t + (ε : ℝ) := add_nonneg ht ε.coe_nonneg
    simpa only [ENNReal.ofReal_add ht ε.coe_nonneg, ENNReal.ofReal_coe_nnreal] using
      criticalValue_le_of_isSome htε
        (hwin (t + ε) htε (lt_add_of_pos_right t (NNReal.coe_pos.mpr hε)))
  · exact le_sInf fun _ ⟨r, hr, heq, h⟩ => heq ▸ ENNReal.ofReal_le_ofReal (hlose r hr h)

end CriticalValue

end Policy

namespace Mechanism

variable {ι τ : Type*} [Preorder τ]

/-- The quasilinear utility of agent `i` with true type `θ_true` when the reported profile is
`θ_rep`: `realizedValue θ_true (alloc θ_rep i) - payment θ_rep i`. -/
@[expose] noncomputable def utility (M : Mechanism ι τ) (i : ι) (θ_true : AgentType τ)
    (θ_rep : ι → AgentType τ) : ℝ :=
  θ_true.realizedValue (M.policy.alloc θ_rep i) - M.payment θ_rep i

/-- Online dominant-strategy incentive compatibility (strong truthfulness) under *no early arrival*
and *no late departure* misreports: for every agent `i`, report profile `θ`, and true type
`θ_true` with `[a', d'] ⊆ [a, d]`, truthful reporting maximizes utility
([Parkes2007], Def. 16.5, locator not verified against primary PDF). -/
@[expose] def IsDSIC [DecidableEq ι] (M : Mechanism ι τ) : Prop :=
  ∀ (i : ι) (θ : ι → AgentType τ) (θ_true : AgentType τ),
    θ_true.IsValidMisreport (θ i) →
    M.utility i θ_true θ ≤ M.utility i θ_true (Function.update θ i θ_true)

/-- Online dominant-strategy incentive compatibility under *no early arrival* and *arbitrary
departure* misreports: `a ≤ a'`, with `d'` unrestricted
([Parkes2007], Def. 16.5 & §16.3.1, locator not verified against primary PDF). -/
@[expose] def IsDSICNoEarlyArrival [DecidableEq ι] (M : Mechanism ι τ) : Prop :=
  ∀ (i : ι) (θ : ι → AgentType τ) (θ_true : AgentType τ),
    θ_true.NoEarlyArrival (θ i) →
    M.utility i θ_true θ ≤ M.utility i θ_true (Function.update θ i θ_true)

/-- Ex-post individual rationality: every truthful agent receives nonnegative utility. -/
@[expose] def IsIR (M : Mechanism ι τ) : Prop :=
  ∀ (i : ι) (θ : ι → AgentType τ), 0 ≤ M.utility i (θ i) θ

/-- No positive transfers: payments are always nonnegative. -/
@[expose] def IsNPT (M : Mechanism ι τ) : Prop :=
  ∀ (i : ι) (θ : ι → AgentType τ), 0 ≤ M.payment θ i

/-- Losers pay zero: an unallocated agent is charged `0`. -/
@[expose] def IsLoserZero (M : Mechanism ι τ) : Prop :=
  ∀ (i : ι) (θ : ι → AgentType τ), M.policy.alloc θ i = none → M.payment θ i = 0

theorem IsDSICNoEarlyArrival.isDSIC [DecidableEq ι] {M : Mechanism ι τ}
    (h : M.IsDSICNoEarlyArrival) : M.IsDSIC :=
  fun i θ θ_true hmis => h i θ θ_true hmis.noEarlyArrival

/-- A truthful allocated agent realizes its reported value `vᵢ`, since `alloc` is window-feasible.
-/
theorem utility_of_alloc_some (M : Mechanism ι τ) {i : ι} {θ : ι → AgentType τ} {t : τ}
    (h : M.policy.alloc θ i = some t) :
    M.utility i (θ i) θ = (θ i).value - M.payment θ i := by
  simp only [utility, h,
    AgentType.realizedValue_some_of_inWindow (M.policy.alloc_in_window θ i t h)]

/-- An unallocated agent has utility `-M.payment θ i`. -/
theorem utility_of_alloc_none (M : Mechanism ι τ) {i : ι} {θ_true : AgentType τ}
    {θ : ι → AgentType τ} (h : M.policy.alloc θ i = none) :
    M.utility i θ_true θ = -M.payment θ i := by
  simp only [utility, h, AgentType.realizedValue_none, zero_sub]

end Mechanism

namespace Policy

variable {ι τ : Type*} [Preorder τ] [DecidableEq ι]

/-- An online policy is *implementable* if there exists a payment rule making `(π, p)` DSIC
(under no-early-arrival and no-late-departure misreports), individually rational, with no positive
transfers and zero loser payments. -/
@[expose] def IsImplementable (π : Policy ι τ) : Prop :=
  ∃ p : (ι → AgentType τ) → ι → ℝ,
    let M : Mechanism ι τ := ⟨π, p⟩
    M.IsDSIC ∧ M.IsIR ∧ M.IsNPT ∧ M.IsLoserZero

theorem criticalMechanism_isNPT (π : Policy ι τ) : π.criticalMechanism.IsNPT := by
  intro i θ
  simp only [criticalMechanism, criticalPayment]
  split_ifs <;> positivity

theorem criticalMechanism_isLoserZero (π : Policy ι τ) : π.criticalMechanism.IsLoserZero := by
  intro i θ hnone
  simp_all [criticalMechanism, criticalPayment]

/-- The critical-value mechanism of any deterministic online policy is individually rational
([Parkes2007], Theorem 16.13, IR part, locator not verified against primary PDF). -/
theorem criticalMechanism_isIR (π : Policy ι τ) : π.criticalMechanism.IsIR := by
  intro i θ
  cases h : π.alloc θ i with
  | none => simp [Mechanism.utility, criticalMechanism, criticalPayment, h]
  | some t =>
    have hle := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      (criticalValue_le_self (h.symm ▸ Option.isSome_some))
    simp only [Mechanism.utility, criticalMechanism, criticalPayment, h, Option.isSome_some,
      ↓reduceIte, AgentType.realizedValue_some_of_inWindow (π.alloc_in_window θ i t h)]
    linarith [ENNReal.toReal_ofReal (θ i).value_nonneg]

/-- Any monotone deterministic online policy paired with critical-value payments is DSIC under
no-early-arrival and no-late-departure misreports ([Parkes2007], Theorem 16.13, locator not
verified against primary PDF). -/
theorem criticalMechanism_isDSIC {π : Policy ι τ} (hmono : π.IsMonotone) :
    π.criticalMechanism.IsDSIC := by
  intro i θ θ_true hmis
  set θ_t := Function.update θ i θ_true
  cases hrep : π.alloc θ i with
  | none =>
    rw [Mechanism.utility_of_alloc_none _ hrep, π.criticalMechanism_isLoserZero i θ hrep,
      neg_zero]
    simpa only [θ_t, Function.update_self] using π.criticalMechanism_isIR i θ_t
  | some t_rep =>
    have hin_rep : θ_true.InWindow t_rep :=
      .of_isValidMisreport hmis (π.alloc_in_window θ i t_rep hrep)
    set cv_rep := π.criticalValue θ i (θ i).arrival (θ i).departure (θ i).arrival_le_departure
    set cv_true := π.criticalValue θ i θ_true.arrival θ_true.departure θ_true.arrival_le_departure
    have hcv_rep_ne_top : cv_rep ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (criticalValue_le_self (by simp [hrep]))
    have hcv_anti : cv_true ≤ cv_rep :=
      criticalValue_antitone hmono (θ i).arrival_le_departure θ_true.arrival_le_departure
        hmis.1 hmis.2
    conv_lhs => simp only [Mechanism.utility, criticalMechanism, criticalPayment, hrep,
      AgentType.realizedValue_some_of_inWindow hin_rep, Option.isSome_some, ↓reduceIte]
    cases ht : π.alloc θ_t i with
    | some t_true =>
      have hin_true : θ_true.InWindow t_true := by
        simpa only [θ_t, Function.update_self] using π.alloc_in_window θ_t i t_true ht
      simp only [Mechanism.utility, criticalMechanism, criticalPayment, ht,
        AgentType.realizedValue_some_of_inWindow hin_true, Option.isSome_some, ↓reduceIte,
        θ_t, Function.update_self, criticalValue_update]
      linarith [ENNReal.toReal_mono hcv_rep_ne_top hcv_anti]
    | none =>
      rw [Mechanism.utility_of_alloc_none _ ht, π.criticalMechanism_isLoserZero i θ_t ht, neg_zero]
      have hle_cv : ENNReal.ofReal θ_true.value ≤ cv_true := le_of_not_gt fun hlt =>
        Option.isSome_iff_ne_none.mp
          (isSome_of_criticalValue_lt hmono θ_true.value_nonneg hlt : (π.alloc θ_t i).isSome) ht
      linarith [ENNReal.toReal_mono hcv_rep_ne_top (hle_cv.trans hcv_anti),
        ENNReal.toReal_ofReal θ_true.value_nonneg]

/-- A *monotonic-late* deterministic online policy (`IsMonotone` and `IsLateAllocating`,
allocating winners at their reported departure) paired with critical-value payments is DSIC even
under *arbitrary departure* misreports (`IsDSICNoEarlyArrival`)
([Parkes2007], §16.3.1, p. 420, locator not verified against primary PDF). -/
theorem criticalMechanism_isDSICNoEarlyArrival {τ : Type*} [LinearOrder τ]
    {π : Policy ι τ} (hmono : π.IsMonotone) (hlate : π.IsLateAllocating) :
    π.criticalMechanism.IsDSICNoEarlyArrival := by
  intro i θ θ_true ha
  by_cases hd : (θ i).departure ≤ θ_true.departure
  · exact criticalMechanism_isDSIC hmono i θ θ_true ⟨ha, hd⟩
  · push Not at hd
    have hir : 0 ≤ π.criticalMechanism.utility i θ_true (Function.update θ i θ_true) := by
      simpa only [Function.update_self] using
        π.criticalMechanism_isIR i (Function.update θ i θ_true)
    cases hrep : π.criticalMechanism.policy.alloc θ i with
    | none =>
      rwa [Mechanism.utility_of_alloc_none _ hrep,
        π.criticalMechanism_isLoserZero i θ hrep, neg_zero]
    | some t_rep =>
      have hnotwin : ¬ θ_true.InWindow t_rep :=
        fun hin => not_le_of_gt hd (hlate θ i t_rep hrep ▸ hin.2)
      rw [Mechanism.utility, hrep, AgentType.realizedValue_some_of_not_inWindow hnotwin, zero_sub]
      linarith [π.criticalMechanism_isNPT i θ]

end Policy

namespace Mechanism

variable {ι τ : Type*} [Preorder τ] [DecidableEq ι]

/-- Necessity of online monotonicity: any deterministic online mechanism that is DSIC (under
no-early-arrival and no-late-departure misreports), individually rational, and charges unallocated
agents `0` must have an online-monotone allocation policy
([Parkes2007], Theorem 16.15, locator not verified against primary PDF). -/
theorem IsDSIC.isMonotone {M : Mechanism ι τ} (hdsic : M.IsDSIC) (hir : M.IsIR)
    (hlz : M.IsLoserZero) : M.policy.IsMonotone := by
  intro i θ θ₁ θ₂ ha hd hv hwin₁
  obtain ⟨t₁, ht₁⟩ := Option.isSome_iff_exists.mp hwin₁
  have hmis : θ₂.IsValidMisreport θ₁ := ⟨ha, hd⟩
  have hir₁ := hir i (Function.update θ i θ₁)
  rw [M.utility_of_alloc_some ht₁, Function.update_self] at hir₁
  have hin₂ : θ₂.InWindow t₁ := .of_isValidMisreport hmis (by
    simpa only [Function.update_self] using
      M.policy.alloc_in_window (Function.update θ i θ₁) i t₁ ht₁)
  have hdsic₂ :=
    hdsic i (Function.update θ i θ₁) θ₂ (by simpa only [Function.update_self] using hmis)
  rw [Function.update_idem] at hdsic₂
  by_contra hnotwin₂
  have hnone₂ := Option.not_isSome_iff_eq_none.mp hnotwin₂
  rw [M.utility_of_alloc_none hnone₂, hlz i (Function.update θ i θ₂) hnone₂, neg_zero] at hdsic₂
  simp only [utility, ht₁, AgentType.realizedValue_some_of_inWindow hin₂] at hdsic₂
  linarith

/-- On a fixed window `[a, d]`, a DSIC mechanism charges the same payment to all winning values. -/
private theorem IsDSIC.payment_eq_of_same_window {M : Mechanism ι τ} (hdsic : M.IsDSIC)
    {i : ι} {θ : ι → AgentType τ} {θ₁ θ₂ : AgentType τ}
    (ha : θ₁.arrival = θ₂.arrival) (hd : θ₁.departure = θ₂.departure)
    (hwin₁ : (M.policy.alloc (Function.update θ i θ₁) i).isSome)
    (hwin₂ : (M.policy.alloc (Function.update θ i θ₂) i).isSome) :
    M.payment (Function.update θ i θ₁) i = M.payment (Function.update θ i θ₂) i := by
  obtain ⟨t₁, ht₁⟩ := Option.isSome_iff_exists.mp hwin₁
  obtain ⟨t₂, ht₂⟩ := Option.isSome_iff_exists.mp hwin₂
  have hmis₁₂ : θ₁.IsValidMisreport θ₂ := ⟨le_of_eq ha, le_of_eq hd.symm⟩
  have hmis₂₁ : θ₂.IsValidMisreport θ₁ := ⟨le_of_eq ha.symm, le_of_eq hd⟩
  have hin₁ : θ₁.InWindow t₁ := by
    simpa only [Function.update_self] using M.policy.alloc_in_window _ i t₁ ht₁
  have hin₂ : θ₂.InWindow t₂ := by
    simpa only [Function.update_self] using M.policy.alloc_in_window _ i t₂ ht₂
  have h1 := hdsic i (Function.update θ i θ₂) θ₁ (by simpa only [Function.update_self] using hmis₁₂)
  have h2 := hdsic i (Function.update θ i θ₁) θ₂ (by simpa only [Function.update_self] using hmis₂₁)
  rw [Function.update_idem] at h1 h2
  simp only [utility, ht₁, ht₂, AgentType.realizedValue_some_of_inWindow hin₁,
    AgentType.realizedValue_some_of_inWindow hin₂,
    AgentType.realizedValue_some_of_inWindow (hin₂.of_isValidMisreport hmis₁₂),
    AgentType.realizedValue_some_of_inWindow (hin₁.of_isValidMisreport hmis₂₁)] at h1 h2
  linarith

/-- Uniqueness of critical-value payments: every DSIC, IR, NPT, loser-zero deterministic online
mechanism must charge each agent `M.policy.criticalPayment`
([Parkes2007], Lemma 16.14, locator not verified against primary PDF). -/
theorem IsDSIC.payment_eq_criticalPayment {M : Mechanism ι τ} (hdsic : M.IsDSIC)
    (hir : M.IsIR) (hnpt : M.IsNPT) (hlz : M.IsLoserZero) (θ : ι → AgentType τ) (i : ι) :
    M.payment θ i = M.policy.criticalPayment θ i := by
  cases h : M.policy.alloc θ i with
  | none => simp [hlz i θ h, Policy.criticalPayment, h]
  | some t =>
    set a := (θ i).arrival
    set d := (θ i).departure
    set had := (θ i).arrival_le_departure
    set cv := M.policy.criticalValue θ i a d had
    have hcv_ne_top : cv ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (M.policy.criticalValue_le_self (by simp [h]))
    simp only [Policy.criticalPayment, h, Option.isSome_some, ↓reduceIte]
    apply le_antisymm
    · have hp_le_cv : ENNReal.ofReal (M.payment θ i) ≤ cv := by
        refine le_sInf fun w ⟨r, hr, hw, hwin_r⟩ => ?_
        have hpeq := hdsic.payment_eq_of_same_window (θ := θ) (θ₁ := θ i)
          (θ₂ := ⟨a, d, r, had, hr⟩) rfl rfl (by simp [Function.update_eq_self, h]) hwin_r
        rw [Function.update_eq_self] at hpeq
        obtain ⟨t_r, ht_r⟩ := Option.isSome_iff_exists.mp hwin_r
        have hir_r := hir i (Function.update θ i ⟨a, d, r, had, hr⟩)
        rw [M.utility_of_alloc_some ht_r, Function.update_self] at hir_r
        exact hw ▸ ENNReal.ofReal_le_ofReal (by linarith)
      exact ENNReal.toReal_ofReal (hnpt i θ) ▸ ENNReal.toReal_mono hcv_ne_top hp_le_cv
    · refine le_of_not_gt fun hlt => ?_
      set z : ℝ := (M.payment θ i + cv.toReal) / 2 with hz_def
      have hz_nonneg : 0 ≤ z := by linarith [hnpt i θ]
      have hz_lt_cv : ENNReal.ofReal z < cv :=
        (ENNReal.ofReal_lt_iff_lt_toReal hz_nonneg hcv_ne_top).2 (by linarith)
      set θ_z : AgentType τ := ⟨a, d, z, had, hz_nonneg⟩
      have hlose_z : M.policy.alloc (Function.update θ i θ_z) i = none :=
        Option.not_isSome_iff_eq_none.1 fun hsome =>
          not_le_of_gt hz_lt_cv (M.policy.criticalValue_le_of_isSome hz_nonneg hsome)
      have hdsic_z := hdsic i θ θ_z ⟨le_rfl, le_rfl⟩
      rw [M.utility_of_alloc_none hlose_z, hlz i (Function.update θ i θ_z) hlose_z, neg_zero]
        at hdsic_z
      simp only [utility, h,
        AgentType.realizedValue_some_of_inWindow (θ := θ_z) (M.policy.alloc_in_window θ i t h),
        θ_z] at hdsic_z
      linarith

end Mechanism

namespace Policy

variable {ι τ : Type*} [Preorder τ] [DecidableEq ι]

/-- Exact characterization of deterministic online implementability under no-early-arrival and
no-late-departure misreports: a deterministic online policy admits a DSIC, IR, NPT, loser-zero
payment rule if and only if it is online-monotone
([Parkes2007], Theorems 16.13 and 16.15, locators not verified against primary PDF). -/
theorem isImplementable_iff_isMonotone {π : Policy ι τ} :
    π.IsImplementable ↔ π.IsMonotone :=
  ⟨fun ⟨_, hdsic, hir, _, hlz⟩ => hdsic.isMonotone hir hlz, fun hmono =>
    ⟨π.criticalPayment, criticalMechanism_isDSIC hmono, criticalMechanism_isIR π,
      criticalMechanism_isNPT π, criticalMechanism_isLoserZero π⟩⟩

end Policy

section AggregateObjectives

variable {ι τ : Type*} [Fintype ι] [Preorder τ]

/-- Realized social welfare of an allocation map `f : ι → Option τ` on online profile `θ`. -/
@[expose] noncomputable def welfare (θ : ι → AgentType τ) (f : ι → Option τ) : ℝ :=
  ∑ i : ι, (θ i).realizedValue (f i)

theorem welfare_nonneg (θ : ι → AgentType τ) (f : ι → Option τ) :
    0 ≤ welfare θ f :=
  Finset.sum_nonneg fun i _ => (θ i).realizedValue_nonneg (f i)

theorem welfare_eq_sum_filter {θ : ι → AgentType τ} {f : ι → Option τ}
    (hwin : ∀ i t, f i = some t → (θ i).InWindow t) :
    welfare θ f = ∑ i ∈ Finset.univ.filter (fun i => (f i).isSome), (θ i).value := by
  classical
  rw [welfare, Finset.sum_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases h : f i with
  | none => simp
  | some t => simp [AgentType.realizedValue_some_of_inWindow (hwin i t h)]

/-- Total seller revenue of an online mechanism `M` on online profile `θ`. -/
@[expose] noncomputable def revenue (M : Mechanism ι τ) (θ : ι → AgentType τ) : ℝ :=
  ∑ i : ι, M.payment θ i

theorem revenue_nonneg {M : Mechanism ι τ} (hnpt : M.IsNPT) (θ : ι → AgentType τ) :
    0 ≤ revenue M θ :=
  Finset.sum_nonneg fun i _ => hnpt i θ

end AggregateObjectives

end Cslib.GameTheory.OnlineMechanism
