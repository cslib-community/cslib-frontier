/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Lattice
import Mathlib.Tactic.Linarith

/-!
# The Vickrey–Clarke–Groves mechanism

A general (multi-parameter) mechanism design environment has agents `ι`, a set `Ω` of outcomes,
and a private valuation `vᵢ : Ω → ℝ` for each agent ([Roughgarden2013CS364A], Lecture 7, §1;
[Nisan2007], §9.3.2–9.3.4). A direct-revelation mechanism collects reported valuations
`b : ι → Ω → ℝ`, chooses an outcome and charges payments; agent `i` with valuation `v` has
quasilinear utility `v(ω) − pᵢ(b)`.

*Groves mechanisms* [Groves1973] choose an outcome maximizing reported welfare `∑ᵢ bᵢ(ω)` and
charge `pᵢ(b) = hᵢ(b₋ᵢ) − ∑ⱼ≠ᵢ bⱼ(ω*)`; every such mechanism is DSIC, both on any restricted
valuation domain `V : ι → Set (Ω → ℝ)` (`groves_isDSICOn`, [Nisan2007], Theorem 9.17) and on all
real valuations (`groves_isDSIC`). The *Clarke pivot* [Clarke1971]
`hᵢ(b₋ᵢ) = max_ω ∑ⱼ≠ᵢ bⱼ(ω)` gives the VCG mechanism, which charges each agent its externality
([Roughgarden2013CS364A], Lecture 7, (2); [Nisan2007], Definition 9.19). Its payments are
nonnegative (`vcg_payment_nonneg`, `vcg_noPositiveTransfersOn`) and a truthful agent with
nonnegative valuation gets nonnegative utility (`vcg_isIR`, `vcg_isIROn`;
[Roughgarden2013CS364A], Lecture 7, (4) and the exercise following it; [Nisan2007], Lemma 9.20).

DSIC holds for arbitrary real valuations; nonnegativity is only assumed for individual
rationality. Note that `Mechanism.IsIR` restricts the evaluated agent's valuation to `0 ≤ b i`
while leaving the other agents' reports unrestricted, whereas [Nisan2007]'s Definition 9.18
(`Mechanism.IsIROn`) quantifies over profiles in `V` with no built-in sign restriction—matching
procurement/cost domains and explaining why Lemma 9.20 assumes `0 ≤ v` on `V i`. The finite
outcome set is needed for the Clarke pivot and for the existence of a welfare-maximizing outcome
rule; DSIC of Groves mechanisms holds for any outcome type.

This `Mechanism ι Ω` is separate from `SingleParameter.Mechanism ι`. A single-parameter
environment is the special case in which agent `i`'s valuation of an outcome `ω` is `vᵢ · xᵢ(ω)`
for an allocation map `x` and a private scalar `vᵢ ≥ 0`, and its incentive predicates quantify
only over such valuations and nonnegative bids. `IsDSICOn` and `IsIROn` restrict DSIC and IR to
valuation domains; `CslibFrontier.GameTheory.Mechanism.LinearValuation` and
`CslibFrontier.GameTheory.Mechanism.Domains` identify single-parameter DSIC and IR with `IsDSICOn`
and `IsIROn` on linear valuations, and `CslibFrontier.GameTheory.Mechanism.VickreyVCG` shows
that VCG on single-item outcomes is the Vickrey auction.

## Main definitions

* `Mechanism`: an outcome rule and a payment rule on reported valuation profiles.
* `Mechanism.utility`, `Mechanism.IsDSIC`, `Mechanism.IsDSICOn`, `Mechanism.IsIR`,
  `Mechanism.IsIROn`, `Mechanism.NoPositiveTransfersOn`.
* `Mechanism.welfare`, `Mechanism.IsWelfareMaximizing`, `Mechanism.IsWelfareMaximizingOn`.
* `Mechanism.groves`, `Mechanism.clarkePivot`, `Mechanism.vcg`.

## Main results

* `Mechanism.groves_isDSICOn`, `Mechanism.groves_isDSIC`: Groves mechanisms with a
  welfare-maximizing outcome rule are DSIC on restricted and unrestricted domains
  ([Nisan2007], Theorem 9.17).
* `Mechanism.vcg_isDSICOn`, `Mechanism.vcg_isDSIC`, `Mechanism.vcg_payment_nonneg`,
  `Mechanism.vcg_noPositiveTransfersOn`, `Mechanism.vcg_isIROn`, `Mechanism.vcg_isIR`:
  DSIC, no positive transfers, and individual rationality of VCG with Clarke pivot payments
  ([Nisan2007], Theorem 9.17 and Lemma 9.20).
* `Mechanism.exists_isDSIC_isWelfareMaximizing`: in every general mechanism design environment
  with finitely many outcomes there is a DSIC welfare-maximizing mechanism
  ([Roughgarden2013CS364A], Lecture 7, Theorem 2.1), which can moreover be taken individually
  rational with nonnegative payments.
* `Mechanism.clarkePivot_comp_equiv`, `Mechanism.vcg_payment_comp_equiv`: transporting VCG along
  an equivalence of outcome types preserves Clarke pivots and payments.

## References

* [N. Nisan, *Introduction to mechanism design (for computer scientists)*][Nisan2007]
* [T. Roughgarden, *CS364A: Algorithmic Game Theory*, lecture notes][Roughgarden2013CS364A]
* [T. Roughgarden, *Twenty Lectures on Algorithmic Game Theory*][Roughgarden2016]
* [E. H. Clarke, *Multipart pricing of public goods*][Clarke1971]
* [T. Groves, *Incentives in teams*][Groves1973]
* [W. Vickrey, *Counterspeculation, auctions, and competitive sealed tenders*][Vickrey1961]
-/

public section

namespace Cslib.GameTheory

/-- A direct-revelation mechanism with agents `ι` and outcomes `Ω`: on the reported valuations
`b : ι → Ω → ℝ` it chooses `outcome b` and charges agent `i` the amount `payment b i`. -/
structure Mechanism (ι Ω : Type*) where
  /-- The outcome rule. -/
  outcome : (ι → Ω → ℝ) → Ω
  /-- The payment rule. -/
  payment : (ι → Ω → ℝ) → ι → ℝ

namespace Mechanism

variable {ι Ω : Type*}

/-- The quasilinear utility `v(ω) − pᵢ(b)` of agent `i` with valuation `v` on the reports `b`,
where `ω` is the chosen outcome. -/
@[expose] def utility (M : Mechanism ι Ω) (i : ι) (v : Ω → ℝ) (b : ι → Ω → ℝ) : ℝ :=
  v (M.outcome b) - M.payment b i

/-- Dominant-strategy incentive compatibility: for every agent `i`, valuation `v` and reports `b`,
reporting `v` instead of `bᵢ` does not lower `i`'s utility ([Roughgarden2013CS364A], Lecture 7,
§2). Valuations are arbitrary real functions. -/
@[expose] def IsDSIC [DecidableEq ι] (M : Mechanism ι Ω) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ) (v : Ω → ℝ),
    M.utility i v b ≤ M.utility i v (Function.update b i v)

/-- Individual rationality: an agent whose valuation `bᵢ` is nonnegative and who reports it
truthfully gets nonnegative utility, whatever the others report. -/
@[expose] def IsIR (M : Mechanism ι Ω) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ), 0 ≤ b i → 0 ≤ M.utility i (b i) b

/-- Dominant-strategy incentive compatibility on the valuation domains `V`: for every agent `i`,
valuation `v ∈ V i` and reports `b` with every `b j ∈ V j`, reporting `v` instead of `bᵢ` does not
lower `i`'s utility. On the full domains this is `IsDSIC` (`isDSICOn_univ_iff`). Single-parameter
environments are the domains of linear valuations; see
`CslibFrontier.GameTheory.Mechanism.LinearValuation`. -/
@[expose] def IsDSICOn [DecidableEq ι] (M : Mechanism ι Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ) (v : Ω → ℝ), (∀ j, b j ∈ V j) → v ∈ V i →
    M.utility i v b ≤ M.utility i v (Function.update b i v)

/-- A DSIC mechanism is DSIC on every valuation domain. -/
theorem IsDSIC.isDSICOn [DecidableEq ι] {M : Mechanism ι Ω} (hM : M.IsDSIC)
    (V : ι → Set (Ω → ℝ)) : M.IsDSICOn V :=
  fun i b v _ _ => hM i b v

theorem isDSICOn_univ_iff [DecidableEq ι] {M : Mechanism ι Ω} :
    M.IsDSICOn (fun _ => Set.univ) ↔ M.IsDSIC :=
  ⟨fun h i b v => h i b v (fun _ => Set.mem_univ _) (Set.mem_univ _), fun h => h.isDSICOn _⟩

/-- **Ex-post individual rationality on a restricted domain** ([Nisan2007], Definition 9.18): on
every truthful valuation profile in `V`, every agent gets nonnegative utility. -/
@[expose] def IsIROn (M : Mechanism ι Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, b j ∈ V j) → 0 ≤ M.utility i (b i) b

/-- **No positive transfers on a restricted domain** ([Nisan2007], Definition 9.18): on every
valuation profile in `V`, no agent receives a negative payment (subsidy) from the mechanism. -/
@[expose] def NoPositiveTransfersOn (M : Mechanism ι Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ (i : ι) (b : ι → Ω → ℝ), (∀ j, b j ∈ V j) → 0 ≤ M.payment b i

/-- On the unrestricted domain `Set.univ`, `IsIROn` says every agent gets nonnegative utility on
every profile. -/
@[simp] theorem isIROn_univ_iff (M : Mechanism ι Ω) :
    M.IsIROn (fun _ => Set.univ) ↔ ∀ i b, 0 ≤ M.utility i (b i) b :=
  ⟨fun h i b => h i b fun _ => trivial, fun h i b _ => h i b⟩

/-- On the unrestricted domain `Set.univ`, `NoPositiveTransfersOn` says payments are nonnegative
everywhere. -/
@[simp] theorem noPositiveTransfersOn_univ_iff (M : Mechanism ι Ω) :
    M.NoPositiveTransfersOn (fun _ => Set.univ) ↔ ∀ i b, 0 ≤ M.payment b i :=
  ⟨fun h i b => h i b fun _ => trivial, fun h i b _ => h i b⟩

theorem IsDSICOn.mono [DecidableEq ι] {M : Mechanism ι Ω} {V W : ι → Set (Ω → ℝ)}
    (hM : M.IsDSICOn W) (hVW : ∀ i, V i ⊆ W i) : M.IsDSICOn V :=
  fun i b v hb hv => hM i b v (fun j => hVW j (hb j)) (hVW i hv)

theorem IsIROn.mono {M : Mechanism ι Ω} {V W : ι → Set (Ω → ℝ)}
    (hM : M.IsIROn W) (hVW : ∀ i, V i ⊆ W i) : M.IsIROn V :=
  fun i b hb => hM i b fun j => hVW j (hb j)

theorem NoPositiveTransfersOn.mono {M : Mechanism ι Ω} {V W : ι → Set (Ω → ℝ)}
    (hM : M.NoPositiveTransfersOn W) (hVW : ∀ i, V i ⊆ W i) : M.NoPositiveTransfersOn V :=
  fun i b hb => hM i b fun j => hVW j (hb j)

/-- `Mechanism.IsIR` implies `Mechanism.IsIROn` on any domain of nonnegative valuations, in
particular on `fun _ => {v | 0 ≤ v}`. -/
theorem IsIR.isIROn {M : Mechanism ι Ω} (hM : M.IsIR) {V : ι → Set (Ω → ℝ)}
    (hV : ∀ i, ∀ v ∈ V i, 0 ≤ v) : M.IsIROn V :=
  fun i b hb => hM i b (hV i (b i) (hb i))

variable [Fintype ι]

/-- The reported welfare `∑ᵢ bᵢ(ω)` of the outcome `ω`. -/
@[expose] def welfare (b : ι → Ω → ℝ) (ω : Ω) : ℝ := ∑ i, b i ω

/-- An outcome rule is welfare-maximizing if it always chooses an outcome maximizing the reported
welfare ([Roughgarden2013CS364A], Lecture 7, (1)). -/
@[expose] def IsWelfareMaximizing (f : (ι → Ω → ℝ) → Ω) : Prop :=
  ∀ b ω, welfare b ω ≤ welfare b (f b)

/-- An outcome rule maximizes reported welfare on every profile in `V`. -/
@[expose] def IsWelfareMaximizingOn (f : (ι → Ω → ℝ) → Ω) (V : ι → Set (Ω → ℝ)) : Prop :=
  ∀ b, (∀ j, b j ∈ V j) → ∀ ω, welfare b ω ≤ welfare b (f b)

/-- Transporting a welfare-maximizing outcome rule along an equivalence `e : Ω₁ ≃ Ω₂` of outcome
types preserves welfare maximization. -/
theorem isWelfareMaximizing_comp_equiv {Ω₁ Ω₂ : Type*} (e : Ω₁ ≃ Ω₂) {f : (ι → Ω₁ → ℝ) → Ω₁}
    (hf : IsWelfareMaximizing f) :
    IsWelfareMaximizing (fun u : ι → Ω₂ → ℝ => e (f fun j ω₁ => u j (e ω₁))) := by
  intro u ω₂
  simpa only [welfare, Equiv.apply_symm_apply] using hf (fun j ω₁ => u j (e ω₁)) (e.symm ω₂)

private theorem welfare_eq_add [DecidableEq ι] (b : ι → Ω → ℝ) (i : ι) (ω : Ω) :
    welfare b ω = b i ω + ∑ j ∈ Finset.univ.erase i, b j ω :=
  (Finset.add_sum_erase _ _ (Finset.mem_univ i)).symm

variable [DecidableEq ι]

/-- The Groves mechanism [Groves1973] with outcome rule `f` and pivot `h`: agent `i` pays
`hᵢ(b) − ∑ⱼ≠ᵢ bⱼ(f(b))`. -/
@[expose] def groves (f : (ι → Ω → ℝ) → Ω) (h : ι → (ι → Ω → ℝ) → ℝ) : Mechanism ι Ω where
  outcome := f
  payment b i := h i b - ∑ j ∈ Finset.univ.erase i, b j (f b)

private theorem sum_erase_update (b : ι → Ω → ℝ) (i : ι) (v : Ω → ℝ) (ω : Ω) :
    ∑ j ∈ Finset.univ.erase i, Function.update b i v j ω = ∑ j ∈ Finset.univ.erase i, b j ω :=
  Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

/-- **Groves mechanisms are DSIC on restricted domains** ([Nisan2007], Theorem 9.17; [Groves1973]):
if `f` maximizes reported welfare on `V` and each pivot `h i` is independent of `i`'s report on `V`,
then `groves f h` is incentive compatible on `V`. -/
theorem groves_isDSICOn {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)}
    (hf : IsWelfareMaximizingOn f V) {h : ι → (ι → Ω → ℝ) → ℝ}
    (hh : ∀ i b v, (∀ j, b j ∈ V j) → v ∈ V i → h i (Function.update b i v) = h i b) :
    (groves f h).IsDSICOn V := by
  intro i b v hb hv
  simp only [utility, groves, hh i b v hb hv, sum_erase_update]
  have key := hf (Function.update b i v)
    ((Function.forall_update_iff b fun j u => u ∈ V j).2 ⟨hv, fun j _ => hb j⟩) (f b)
  rw [welfare_eq_add _ i, welfare_eq_add _ i, Function.update_self, sum_erase_update,
    sum_erase_update] at key
  linarith

/-- **Groves mechanisms are DSIC** [Groves1973]: if the outcome rule maximizes reported welfare
and the pivot `hᵢ` does not depend on `i`'s report, then `i`'s utility under truthful reporting is
`∑ⱼ bⱼ(ω*) − hᵢ(b₋ᵢ)` with `bᵢ = vᵢ`, which the mechanism maximizes. -/
theorem groves_isDSIC {f : (ι → Ω → ℝ) → Ω} (hf : IsWelfareMaximizing f)
    {h : ι → (ι → Ω → ℝ) → ℝ} (hh : ∀ i b v, h i (Function.update b i v) = h i b) :
    (groves f h).IsDSIC :=
  isDSICOn_univ_iff.1 <| groves_isDSICOn (fun b _ ω => hf b ω) fun i b v _ _ => hh i b v

variable [Fintype Ω] [Nonempty Ω]

/-- The Clarke pivot [Clarke1971]: the maximum welfare `max_ω ∑ⱼ≠ᵢ bⱼ(ω)` of the other agents. -/
@[expose] noncomputable def clarkePivot (i : ι) (b : ι → Ω → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun ω => ∑ j ∈ Finset.univ.erase i, b j ω

/-- The VCG mechanism with welfare-maximizing outcome rule `f`: agent `i` pays its externality
`max_ω ∑ⱼ≠ᵢ bⱼ(ω) − ∑ⱼ≠ᵢ bⱼ(f(b))` ([Roughgarden2013CS364A], Lecture 7, (2)). -/
@[expose] noncomputable def vcg (f : (ι → Ω → ℝ) → Ω) : Mechanism ι Ω := groves f clarkePivot

/-- The Clarke pivot of agent `i` does not depend on `i`'s report. -/
@[simp]
theorem clarkePivot_update (i : ι) (b : ι → Ω → ℝ) (v : Ω → ℝ) :
    clarkePivot i (Function.update b i v) = clarkePivot i b := by
  simp only [clarkePivot, sum_erase_update]

omit [Fintype Ω] [Nonempty Ω] in
/-- Pulling back valuations along an equivalence `e : Ω₁ ≃ Ω₂` of outcome types preserves the
Clarke pivot. -/
theorem clarkePivot_comp_equiv {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Nonempty Ω₁]
    [Fintype Ω₂] [Nonempty Ω₂] (e : Ω₁ ≃ Ω₂) (i : ι) (u : ι → Ω₂ → ℝ) :
    clarkePivot i (fun j ω₁ => u j (e ω₁)) = clarkePivot i u :=
  le_antisymm
    (Finset.sup'_le _ _ fun ω₁ _ =>
      Finset.le_sup' (fun ω₂ => ∑ j ∈ Finset.univ.erase i, u j ω₂) (Finset.mem_univ (e ω₁)))
    (Finset.sup'_le _ _ fun ω₂ _ =>
      Finset.le_sup'_of_le _ (Finset.mem_univ (e.symm ω₂)) (by simp))

omit [Fintype Ω] [Nonempty Ω] in
/-- Transporting a VCG mechanism along an equivalence `e : Ω₁ ≃ Ω₂` of outcome types preserves
payments on pulled-back valuation profiles. -/
theorem vcg_payment_comp_equiv {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Nonempty Ω₁]
    [Fintype Ω₂] [Nonempty Ω₂] (e : Ω₁ ≃ Ω₂) (f : (ι → Ω₁ → ℝ) → Ω₁) (u : ι → Ω₂ → ℝ) (i : ι) :
    (vcg fun v => e (f fun j ω₁ => v j (e ω₁))).payment u i =
      (vcg f).payment (fun j ω₁ => u j (e ω₁)) i := by
  simp only [vcg, groves, clarkePivot_comp_equiv]

/-- **VCG is DSIC on restricted domains** ([Nisan2007], Theorem 9.17): if `f` maximizes welfare on
`V`, then `vcg f` is incentive compatible on `V`. -/
theorem vcg_isDSICOn {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)}
    (hf : IsWelfareMaximizingOn f V) : (vcg f).IsDSICOn V :=
  groves_isDSICOn hf fun i b v _ _ => clarkePivot_update i b v

/-- **The VCG mechanism is DSIC** ([Roughgarden2013CS364A], Lecture 7, Theorem 2.1). -/
theorem vcg_isDSIC {f : (ι → Ω → ℝ) → Ω} (hf : IsWelfareMaximizing f) : (vcg f).IsDSIC :=
  groves_isDSIC hf clarkePivot_update

/-- VCG payments are nonnegative ([Roughgarden2013CS364A], Lecture 7, after (2)), for any
outcome rule. -/
theorem vcg_payment_nonneg (f : (ι → Ω → ℝ) → Ω) (b : ι → Ω → ℝ) (i : ι) :
    0 ≤ (vcg f).payment b i := by
  simp only [vcg, groves, clarkePivot, sub_nonneg]
  exact Finset.le_sup' (fun ω => ∑ j ∈ Finset.univ.erase i, b j ω) (Finset.mem_univ (f b))

/-- **VCG makes no positive transfers** ([Nisan2007], Lemma 9.20, first statement). -/
theorem vcg_noPositiveTransfersOn (f : (ι → Ω → ℝ) → Ω) (V : ι → Set (Ω → ℝ)) :
    (vcg f).NoPositiveTransfersOn V :=
  fun i b _ => vcg_payment_nonneg f b i

/-- At any profile `b` where `f` maximizes reported welfare, a truthful agent with nonnegative
valuation receives nonnegative VCG utility. -/
private theorem vcg_utility_nonneg {f : (ι → Ω → ℝ) → Ω} {b : ι → Ω → ℝ}
    (hf : ∀ ω, welfare b ω ≤ welfare b (f b)) {i : ι} (hb : 0 ≤ b i) :
    0 ≤ (vcg f).utility i (b i) b := by
  simp only [utility, vcg, groves, sub_sub_eq_add_sub, ← welfare_eq_add, sub_nonneg]
  refine Finset.sup'_le _ _ fun ω _ => ?_
  have : 0 ≤ b i ω := hb ω
  linarith [hf ω, welfare_eq_add b i ω]

/-- **VCG is individually rational on nonnegative domains** ([Nisan2007], Lemma 9.20, second
statement): if `f` maximizes welfare on `V` and every valuation in `V i` is nonnegative, then
`vcg f` is individually rational on `V`. -/
theorem vcg_isIROn {f : (ι → Ω → ℝ) → Ω} {V : ι → Set (Ω → ℝ)}
    (hf : IsWelfareMaximizingOn f V) (hV : ∀ i, ∀ v ∈ V i, 0 ≤ v) : (vcg f).IsIROn V :=
  fun i b hb => vcg_utility_nonneg (hf b hb) (hV i (b i) (hb i))

/-- **VCG is individually rational** ([Roughgarden2013CS364A], Lecture 7, after (4)): the rebate
`∑ⱼ bⱼ(ω*) − max_ω ∑ⱼ≠ᵢ bⱼ(ω)` is nonnegative when `bᵢ ≥ 0`, so a truthful agent with
nonnegative valuation pays at most its value of the chosen outcome. -/
theorem vcg_isIR {f : (ι → Ω → ℝ) → Ω} (hf : IsWelfareMaximizing f) : (vcg f).IsIR :=
  fun _ b hb => vcg_utility_nonneg (hf b) hb

omit [DecidableEq ι] [Fintype Ω] in
/-- A welfare-maximizing outcome rule exists when there are finitely many outcomes. -/
theorem exists_isWelfareMaximizing [Finite Ω] :
    ∃ f : (ι → Ω → ℝ) → Ω, IsWelfareMaximizing f := by
  choose f hf using fun b : ι → Ω → ℝ => Finite.exists_max (welfare b)
  exact ⟨f, hf⟩

omit [Fintype Ω] in
/-- **Vickrey–Clarke–Groves** ([Roughgarden2013CS364A], Lecture 7, Theorem 2.1): in every general
mechanism design environment with finitely many outcomes there is a DSIC welfare-maximizing
mechanism. The VCG mechanism is moreover individually rational with nonnegative payments. -/
theorem exists_isDSIC_isWelfareMaximizing [Finite Ω] :
    ∃ M : Mechanism ι Ω, M.IsDSIC ∧ IsWelfareMaximizing M.outcome ∧ M.IsIR ∧
      ∀ b i, 0 ≤ M.payment b i := by
  have := Fintype.ofFinite Ω
  obtain ⟨f, hf⟩ := exists_isWelfareMaximizing (ι := ι) (Ω := Ω)
  exact ⟨vcg f, vcg_isDSIC hf, hf, vcg_isIR hf, vcg_payment_nonneg f⟩

end Mechanism

end Cslib.GameTheory
