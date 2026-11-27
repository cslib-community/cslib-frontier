/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

import CslibFrontier.Computability.Circuit.Frontier.Layouts.Components
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Aggregate
public import CslibFrontier.Computability.Circuit.Frontier.Ledger.Sweep
public import CslibFrontier.Computability.Circuit.Frontier.LowerBound
import Mathlib.Tactic.Ring

/-!
# The frontier lower bound with gates of unbounded fan-in

**Main theorems** (`eventually_lt_mul_card_of_ledger_readout`, `eventually_lt_mul_card_of_ledger`).
Fix `r ≥ 2` and assume the layout hypothesis `LayoutBound (r + 1) A`. Let `S_n ⊆ U^n` be dense
`K_n`-rectangle-free sets with `log K_n = o(n)`, as in
`Cslib.Circuits.Frontier.eventually_lt_mul_innerSize`, and let `β(n) = o(n)`. For every `ε > 0`
and all large `n`, every circuit deciding `S_n` whose gates have fan-in at most `r`, except for
`k` *special* gates of any fan-in that have a ledger in a monoid `M` satisfying either
`k log |U| + log |M| ≤ β(n)` (`eventually_lt_mul_card_of_ledger_readout`) or `log |M| ≤ β(n)`
(`eventually_lt_mul_card_of_ledger`), has `s` ordinary inner gates (inner gates that are not
special) with

`(r - 1) s > (1 + 1/A - ε) n`.

Constants and special gates are free; the ledger contributes only to the sublinear error. Because
`Cslib.Circuits.Frontier.Ledger.exists_ncard_le` bounds extra transitions by
`min (|U| ^ k) |M| * |M|`, `k` aggregate gates in `T` pay only `k (log |U| + log |T|)` rather than
`3 k log |T|`: for example, `k = o(n / log t)` threshold gates `Th_t`, `k = o(n / log n)` majority
or symmetric gates, and `k = o(n / log W)` integer `LTF` gates of weight `L₁`-norm `W` cost nothing
in the leading term (`eventually_lt_mul_card_of_threshold`, `eventually_lt_mul_card_of_ltf`).

## Main results

* `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger_min`: the unified frontier lower bound
  under `log (min (|U| ^ k) |M| * |M|) ≤ β(n)`.
* `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger_readout`: the frontier lower bound under
  the `k log |U| + log |M| ≤ β(n)` budget.
* `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ledger`: the frontier lower bound under
  `log |M| ≤ β(n)`.
* `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_aggregates`: the frontier lower bound with
  aggregate gates.
* `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_threshold`,
  `Cslib.Circuits.Frontier.eventually_lt_mul_card_of_ltf`: corollaries for threshold (`Th_t`,
  `MAJ`, symmetric) and bounded-weight `LTF` special gates.
-/

public section

namespace Cslib.Circuits.Frontier

open Set Filter Asymptotics

universe u v w

variable {U : Type u} [Finite U] [Nontrivial U] {S : ∀ n, Set (Fin n → U)} {K : ℕ → ℕ}

/-- **The unified frontier lower bound with a ledger (`min (|U| ^ k) |M| · |M|`).** Let `r ≥ 2` and
assume `LayoutBound (r + 1) A` with `A > 0`. Let `S_n ⊆ U^n` be dense `K_n`-rectangle-free sets,
and let `β(n) = o(n)`. Then for every `ε > 0` and all large `n`, every circuit deciding `S_n` whose
ordinary gates have fan-in at most `r` and whose `k` special gates have a ledger in a finite
commutative monoid `M` with `log (min (|U| ^ k) |M| * |M|) ≤ β(n)` has `s` ordinary inner gates
with `(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_card_of_ledger_min {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        Ledger special c.program I M →
        Real.log
          ((min (Nat.card U ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M : ℕ) : ℝ) ≤
            β n →
        c.Decides I Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  set q := Nat.card U
  have hq : (1 : ℝ) < q := by exact_mod_cast Finite.one_lt_card
  have h2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hL2 : Real.log 2 ≤ Real.log q :=
    Real.log_le_log two_pos (by exact_mod_cast Finite.one_lt_card)
  have hβ' : (fun n => β n / Real.log 2) =o[atTop] fun n => (n : ℝ) :=
    (hβ.const_mul_left (1 / Real.log 2)).congr_left fun n => by ring
  obtain ⟨η, hη, H⟩ := eventually_lt_of_frontier hA (r + 2) hSK.isLittleO_log
    hSK.isLittleO_deficit hβ' hε
  obtain ⟨C, hC⟩ := hlayout.exists_layout_componentwise hη
  filter_upwards [H C, hSK.eventually_rectangleFree, eventually_card_mul_sq_le_ncard hSK,
    eventually_ge_atTop 1] with n hn hfreen hbign hn1
  intro σ I Acc c special _ M _ _ hfan L hE hS
  set o := c.outputs 0
  have hSeq : S n = {x | c.program.trace I x o ∈ Acc} := Set.ext hS
  rw [hSeq] at hfreen hbign
  have hK1 := hfreen.pos
  have hKS : K n ≤ {x | c.program.trace I x o ∈ Acc}.ncard :=
    (Nat.le_mul_of_pos_left _ Nat.card_pos).trans
      ((Nat.mul_le_mul_left _ (Nat.le_self_pow two_ne_zero _)).trans hbign)
  set lc := liveCircuit c.program special
  set V := Nat.card (Compiler.Vertex lc)
  set N := liveNetwork c.program special U
  have hfan' : lc.FanInAtMost r := (Program.fanInAtMost_eraseGates_iff (special := special)).2 hfan
  obtain ⟨π, hπ⟩ := hC _ _ (Compiler.graph lc) Compiler.loopless (Compiler.maxDegreeLE hr hfan')
  obtain ⟨t, ht, hcount⟩ := L.exists_ncard_le π hfreen hKS (card_vertex_liveCircuit_pos hn1)
    fun t ht => union_subset (hπ t ht t le_rfl (by omega)).1 (hπ t ht (t + 1) (by omega) le_rfl).1
  set W := N.component (π.symm ⟨t, ht⟩)
  set se := (c.program.innerGates.filter fun g => ¬special g).card
  have hse : lc.innerSize = se := innerSize_liveCircuit
  set a := (N.frontier π t ∪ N.frontier π (t + 1)).ncard + (N.readAt (π.symm ⟨t, ht⟩)).ncard
  set nW := (N.readIn W).ncard
  set s : ℝ := (((r - 1) * se : ℕ) : ℝ)
  have hs : s = (r - 1) * se := by simp [s, Nat.cast_sub (by omega : 1 ≤ r)]
  have ha : (a : ℝ) ≤ (N.frontier π t).ncard + (r + 2) := by
    have hU : (N.frontier π t ∪ N.frontier π (t + 1)).ncard ≤ (N.frontier π t).ncard + (r + 1) :=
      (ncard_le_ncard (union_subset subset_union_left (N.frontier_succ_subset π ht))
        (toFinite _)).trans ((ncard_union_le _ _).trans
          (Nat.add_le_add_left (Compiler.maxDegreeLE hr hfan' _) _))
    have hR : (N.readAt (π.symm ⟨t, ht⟩)).ncard ≤ 1 :=
      Compiler.ncard_readAt_le (I.withConstants (L.readout 1)) (fun _ => univ) _
    exact_mod_cast (show a ≤ (N.frontier π t).ncard + (r + 2) by simp only [a]; omega)
  have hρ : (N.cycleRankOn W : ℝ) + nW ≤ s + 1 := by
    have h := hse ▸ Compiler.cycleRankOn_add_ncard_readIn_le (I.withConstants (L.readout 1))
      (fun _ => univ) hfan' (N.edgeCut_component (π.symm ⟨t, ht⟩))
      (N.ncard_component_le_ncard_touching_add_one (π.symm ⟨t, ht⟩))
    simp only [s]
    exact_mod_cast h
  have hV : (V : ℝ) ≤ 7 * s + 3 * n + 3 := by
    have h := hse ▸ Compiler.card_vertex_le hfan'
    have hlive := hse ▸ card_live_le (p := c.program) (special := special)
    have hV_nat : V ≤ 7 * ((r - 1) * se) + 3 * n + 3 := by
      have h7 : 2 * r + 3 ≤ 7 * (r - 1) := by omega
      simp only [V]
      nlinarith [Nat.mul_le_mul_right se h7]
    dsimp only [s]
    exact_mod_cast hV_nat
  set E : ℕ := min (q ^ Nat.card {g // special g}) (Nat.card M) * Nat.card M
  have hEpos : 0 < E :=
    Nat.mul_pos (lt_min (Nat.pow_pos Nat.card_pos) Nat.card_pos) Nat.card_pos
  have hcount' : ({x | c.program.trace I x o ∈ Acc}.ncard : ℝ) ≤
      (K n : ℝ) ^ 2 * (V + 1) * E * (q : ℝ) ^ (min a nW) := by
    exact_mod_cast hcount.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.sub_le _ _) 2))))
  have hSpos : (0 : ℝ) < {x | c.program.trace I x o ∈ Acc}.ncard :=
    Nat.cast_pos.mpr (hK1.trans_le hKS)
  have hlogS : Real.logb q {x | c.program.trace I x o ∈ Acc}.ncard ≤
      2 * Real.logb q (K n) + Real.logb q (V + 1) + Real.logb q E + min a nW := by
    have hK0 : (0 : ℝ) < K n := by exact_mod_cast hK1
    have hE0 : (0 : ℝ) < E := by exact_mod_cast hEpos
    calc _ ≤ Real.logb q ((K n : ℝ) ^ 2 * (V + 1) * E * (q : ℝ) ^ (min a nW)) :=
          Real.logb_le_logb_of_le hq hSpos hcount'
      _ = _ := by
          rw [Real.logb_mul (by positivity) (by positivity), Real.logb_mul (by positivity)
            (by positivity), Real.logb_mul (by positivity) (by positivity), Real.logb_pow,
            Real.logb_pow, Real.logb_self_eq_one hq]
          push_cast
          ring
  rw [← hSeq] at hlogS
  have hlogE : Real.logb q E ≤ β n / Real.log 2 := by
    have h0 : 0 ≤ Real.log (E : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hEpos.ne')
    exact (div_le_div_of_nonneg_left h0 h2 hL2).trans (div_le_div_of_nonneg_right hE h2.le)
  have hlogK : 0 ≤ Real.logb q (K n) := Real.logb_nonneg hq (by exact_mod_cast hK1)
  have hmin1 : ((min a nW : ℕ) : ℝ) ≤ a := by exact_mod_cast min_le_left a nW
  have hmin2 : ((min a nW : ℕ) : ℝ) ≤ nW := by exact_mod_cast min_le_right a nW
  rw [← hs]
  exact hn s V (N.cycleRankOn W) (N.frontier π t).ncard (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hV (by linarith) (by linarith) (hπ t ht t le_rfl (by omega)).2

private theorem log_ledger_factor {q M : ℕ} (hq : 0 < q) (hM : 0 < M) (k : ℕ) :
    Real.log ((min (q ^ k) M * M : ℕ) : ℝ) =
      min (k * Real.log q) (Real.log M) + Real.log M := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hM' : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hpow : (0 : ℝ) < (q : ℝ) ^ k := pow_pos hq' _
  rw [Nat.cast_mul, Nat.cast_min, Nat.cast_pow, Real.log_mul (lt_min hpow hM').ne' hM'.ne',
    Real.strictMonoOn_log.monotoneOn.map_min hpow hM', Real.log_pow]

/-- **The tightened frontier lower bound with a ledger (`|U| ^ k · |M|`).** Under the hypotheses of
`eventually_lt_mul_card_of_ledger_min`, if `k log |U| + log |M| ≤ β(n)`, then `(r - 1) s >
(1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_card_of_ledger_readout {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        Ledger special c.program I M →
        Nat.card {g // special g} * Real.log (Nat.card U) + Real.log (Nat.card M) ≤ β n →
        c.Decides I Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  filter_upwards [eventually_lt_mul_card_of_ledger_min.{u, v, w} hr hA hlayout hSK hβ hε] with n hn
  intro σ I Acc c special _ M _ _ hfan L hM hS
  exact hn σ I Acc c special M hfan L ((log_ledger_factor Nat.card_pos Nat.card_pos _).trans_le
    ((add_le_add (min_le_left _ _) le_rfl).trans hM)) hS

/-- **The frontier lower bound with a ledger.** Let `r ≥ 2` and assume the layout hypothesis for
maximum degree `r + 1` with coefficient `A > 0`. Let `S_n ⊆ U^n` be `K_n`-rectangle-free sets over
a finite alphabet `U` with at least two symbols, with `log K_n = o(n)` and
`n log |U| - log |S_n| = o(n)`, and let `β(n) = o(n)`. Then for every `ε > 0` and all large `n`,
every circuit deciding `S_n`, over any basis and interpretation on `U`, whose gates have fan-in at
most `r` except for special gates of any fan-in with a ledger in a finite commutative monoid `M`
with `log |M| ≤ β(n)`, has `s` ordinary inner gates, the inner gates that are not special, with
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_card_of_ledger {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (M : Type w)
      [CommMonoid M] [Finite M],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        Ledger special c.program I M → Real.log (Nat.card M) ≤ β n → c.Decides I Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  have hβ2 : (fun n => 2 * β n) =o[atTop] fun n => (n : ℝ) := hβ.const_mul_left 2
  filter_upwards [eventually_lt_mul_card_of_ledger_min.{u, v, w} hr hA hlayout hSK hβ2 hε] with n hn
  intro σ I Acc c special _ M _ _ hfan L hM hS
  exact hn σ I Acc c special M hfan L ((log_ledger_factor Nat.card_pos Nat.card_pos _).trans_le
    ((add_le_add (min_le_right _ _) le_rfl).trans (by linarith))) hS

/-- **The frontier lower bound with aggregate gates.** Under the hypotheses of
`eventually_lt_mul_card_of_ledger`, for every `ε > 0` and all large `n`, every circuit deciding
`S_n`, over any basis and interpretation on `U`, whose gates have fan-in at most `r` except for
`k` special gates of any fan-in that aggregate in a finite commutative monoid `T`, with
`k log |T| ≤ β(n)`, has `s` ordinary inner gates with `(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_card_of_aggregates {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ U) (Acc : Set U)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (T : Type w)
      [CommMonoid T] [Finite T],
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        (∀ g, special g → Aggregates (I (c.program.lines g).op) T) →
        Nat.card {g // special g} * Real.log (Nat.card T) ≤ β n →
        c.Decides I Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  filter_upwards [eventually_lt_mul_card_of_ledger.{u, v, w} hr hA hlayout hSK hβ hε] with n hn
  intro σ I Acc c special _ T _ _ hfan hagg hk hS
  exact hn σ I Acc c special _ hfan (Ledger.ofAggregates hagg)
    (by simpa [Nat.card_fun] using hk) hS

/-- **The frontier lower bound with unbounded threshold gates (`Th_t`, `MAJ`, symmetric).** Fix
`r ≥ 2`, `LayoutBound (r + 1) A`, a dense rectangle-free Boolean family `S_n`, and `β(n) = o(n)`.
Every circuit deciding `S_n` whose ordinary gates have fan-in at most `r` and whose `k` special
gates compute `Boolean.Threshold.Op` with cutoff at most `t` (with `k (log 2 + log (t + 1)) ≤ β n`)
has `s` ordinary inner gates satisfying `(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_card_of_threshold {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {S : ∀ n, Set (Fin n → Bool)}
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (Acc : Set Bool) (c : Circuit Boolean.Threshold.signature n 1)
      (special : Fin c.size → Prop) [DecidablePred special] (t : ℕ),
        1 ≤ t →
        (∀ g, ¬special g → (c.program.lines g).op.arity ≤ r) →
        (∀ g, special g → match (c.program.lines g).op with
          | .not => True
          | .threshold _ j => j ≤ t) →
        Nat.card {g // special g} * (Real.log 2 + Real.log (t + 1)) ≤ β n →
        c.Decides Boolean.Threshold.interpretation Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  filter_upwards [eventually_lt_mul_card_of_ledger_readout.{0, 0, 0} hr hA hlayout hSK hβ hε]
    with n hn Acc c special _ t ht1 hfan hcut hk hS
  have hagg : ∀ g, special g →
      Aggregates (Boolean.Threshold.interpretation (c.program.lines g).op) (TruncAdd t) :=
    fun g hg => aggregates_thresholdOp _ (by
      have := hcut g hg
      cases h : (c.program.lines g).op with
      | not => exact ht1
      | threshold _ j => simpa [h] using this)
  refine hn Boolean.Threshold.signature Boolean.Threshold.interpretation Acc c special _ hfan
    (Ledger.ofAggregates hagg) ?_ hS
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, Nat.cast_ofNat,
    Nat.card_fun, TruncAdd.card, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  linarith

/-- **The frontier lower bound with bounded-weight integer `LTF` gates.** Fix `r ≥ 2`,
`LayoutBound (r + 1) A`, a dense rectangle-free Boolean family `S_n`, and `β(n) = o(n)`. Every
circuit deciding `S_n` whose ordinary gates have fan-in at most `r` and whose `k` special gates
each compute a function of an integer linear form of `L₁`-weight at most `W` (with
`k (log 2 + log (W + 1)) ≤ β n`) has `s` ordinary inner gates satisfying
`(r - 1) s > (1 + 1/A - ε) n`. -/
theorem eventually_lt_mul_card_of_ltf {r : ℕ} (hr : 2 ≤ r) {A : ℝ} (hA : 0 < A)
    (hlayout : LayoutBound (r + 1) A) {S : ∀ n, Set (Fin n → Bool)}
    (hSK : DenseRectangleFree S K)
    {β : ℕ → ℝ} (hβ : β =o[atTop] fun n => (n : ℝ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ (σ : Signature.{v}) (I : Interpretation σ Bool) (Acc : Set Bool)
      (c : Circuit σ n 1) (special : Fin c.size → Prop) [DecidablePred special] (W : ℕ),
        (∀ g, ¬special g → σ.Arity (c.program.lines g).op ≤ r) →
        (∀ g, special g → ∃ (w : Fin (σ.Arity (c.program.lines g).op) → ℤ) (P : ℤ → Bool),
          (∑ i, (w i).natAbs) ≤ W ∧
          I (c.program.lines g).op = fun x => P (∑ i, if x i then w i else 0)) →
        Nat.card {g // special g} * (Real.log 2 + Real.log (W + 1)) ≤ β n →
        c.Decides I Acc (S n) →
          (1 + 1 / A - ε) * n <
            (r - 1) * (c.program.innerGates.filter fun g => ¬special g).card := by
  filter_upwards [eventually_lt_mul_card_of_ledger_readout.{0, v, 0} hr hA hlayout hSK hβ hε]
    with n hn σ I Acc c special _ W hfan hltf hk hS
  have hagg : ∀ g, special g → Aggregates (I (c.program.lines g).op) (TruncAdd W) := fun g hg =>
    let ⟨w, P, hw, hI⟩ := hltf g hg
    hI ▸ aggregates_weightedSum w hw P
  refine hn σ I Acc c special _ hfan (Ledger.ofAggregates hagg) ?_ hS
  rw [Nat.card_eq_fintype_card (α := Bool), Fintype.card_bool, Nat.cast_ofNat,
    Nat.card_fun, TruncAdd.card, Nat.cast_pow, Real.log_pow, Nat.cast_add, Nat.cast_one]
  linarith

end Cslib.Circuits.Frontier
