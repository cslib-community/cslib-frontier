/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.Dictionary.SuccinctWhpProb
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Small-Regime Array, In-Place Slot Permutation, and CSR Fallback Model

This module develops three pure building blocks for the with-high-probability fixed-capacity
succinct dynamic dictionary (`Cslib.DataStructure.Dictionary.SuccinctWhp`):

1. **Small-regime deterministic array (`SmallDictState`)**: when `n_max < whpThreshold c`, the
   dictionary stores up to `n_max` `(present, key, value)` triples scanned in
   `n_max < whpThreshold c` deterministic steps (`failureProb = 0`).
2. **In-place cycle-following slot rearrangement (`permuteByTarget`)**: rearranges `qArr` and `vArr`
   in place across `n_max` physical slots along any injective partial map `{s < n_max | active s} →
   Fin n_max`, using a single 1-bit `active` marker array and fixed `n_max`-iteration loops. Both
   `fastMode → fallbackMode` compaction and `fallbackMode → fastMode` self-healing instantiate this
   single primitive.
3. **Compressed-sparse-row (`CsrState`) fallback dictionary and overflow-free `GoodSeedOnState`
   checker**: stores arbitrary bucket loads `(X_0, …, X_{M - 1})` (`∑ X_b ≤ n_max`) in `1 · OPT +
   o(n_max)` bits via bucket prefix sums `fbStart[0 .. M]` plus Feistel quotients and values, with
   exact `Dynamic.step` refinement for **every** seed `θ` and an overflow-free decision procedure
   for `GoodSeedOnState`.

## Main definitions

* `Cslib.DataStructure.Dictionary.SuccinctWhp.SmallDictState`, `smallScan`, `smallQuery`,
  `smallInsert`, `smallDelete`, `ValidSmallState`: deterministic small-regime dictionary model.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.permuteByTarget`: in-place cycle-following slot
  rearrangement.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.CsrState`, `csrQuery`, `csrInsert`, `csrDelete`,
  `ValidCsrState`, `checkBalancedBucketNat`, `checkGoodSeedOnState`: CSR fallback dictionary and
  self-healing eligibility checker.

## Main results

* `Cslib.DataStructure.Dictionary.SuccinctWhp.smallQuery_spec`, `smallInsert_spec`,
  `smallDelete_spec`: exact `Dynamic.step` refinement in the small regime.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.permuteByTarget_spec`: exact in-place bijection
  specification of `permuteByTarget`.
* `Cslib.DataStructure.Dictionary.SuccinctWhp.csrQuery_spec`, `csrInsert_spec`, `csrDelete_spec`,
  `checkGoodSeedOnState_spec`: exact `Dynamic.step` refinement in CSR fallback mode and exact
  equivalence with `GoodSeedOnState`.
-/

public section

namespace Cslib.DataStructure.Dictionary.SuccinctWhp

open Cslib.DataStructure.Dictionary
open Cslib.DataStructure.Dictionary.FeistelQuotient
open Finset
open scoped BigOperators

/-! ## Section 1: Small-regime deterministic dictionary (`n_max < whpThreshold c`) -/

/-- Pure state of the small-regime bit-packed array dictionary (`0 .. n_max - 1`). -/
structure SmallDictState where
  /-- Occupancy bit (`0` = empty, non-zero = active) at slot `i < n_max`. -/
  present : ℕ → ℕ
  /-- Stored key `< U` at slot `i < n_max`. -/
  keys : ℕ → ℕ
  /-- Stored value `< V` at slot `i < n_max`. -/
  vals : ℕ → ℕ

/-- Initial empty `SmallDictState`. -/
@[expose] def emptySmallState : SmallDictState where
  present := fun _ => 0
  keys := fun _ => 0
  vals := fun _ => 0

/-- Single step of the `n_max`-slot scan at index `i`, maintaining `(foundIdx1, freeIdx1)` where `0`
encodes `none` and `idx + 1` encodes `some idx`. -/
@[expose] def smallScanStep (st : SmallDictState) (u_val i : ℕ) (acc : ℕ × ℕ) : ℕ × ℕ :=
  if st.present i != 0 then
    if st.keys i == u_val && acc.1 == 0 then (i + 1, acc.2) else acc
  else
    if acc.2 == 0 then (acc.1, i + 1) else acc

/-- Prefix scan over `0 .. k - 1` returning `(foundIdx1, freeIdx1)`. -/
@[expose] def smallScan (st : SmallDictState) (u_val : ℕ) : ℕ → ℕ × ℕ
  | 0 => (0, 0)
  | k + 1 => smallScanStep st u_val k (smallScan st u_val k)

/-- Small-regime lookup of `u_val`. -/
@[expose] def smallQuery (n_max : ℕ) (st : SmallDictState) (u_val : ℕ) : Option ℕ :=
  let (f1, _) := smallScan st u_val n_max
  if f1 = 0 then none else some (st.vals (f1 - 1))

/-- Small-regime insertion / overwrite of `(u_val, v_val)`. -/
@[expose] def smallInsert (n_max : ℕ) (st : SmallDictState) (u_val v_val : ℕ) : SmallDictState :=
  let (f1, free1) := smallScan st u_val n_max
  if f1 != 0 then
    { st with vals := Function.update st.vals (f1 - 1) v_val }
  else if free1 != 0 then
    let idx := free1 - 1
    { present := Function.update st.present idx 1
      keys := Function.update st.keys idx u_val
      vals := Function.update st.vals idx v_val }
  else st

/-- Small-regime deletion of `u_val`. -/
@[expose] def smallDelete (n_max : ℕ) (st : SmallDictState) (u_val : ℕ) : SmallDictState :=
  let (f1, _) := smallScan st u_val n_max
  if f1 != 0 then
    { st with present := Function.update st.present (f1 - 1) 0 }
  else st

/-- Representation invariant relating `SmallDictState` to `dict : Dictionary.State U`. -/
@[expose] def ValidSmallState (U V n_max : ℕ) (st : SmallDictState) (dict : State U) : Prop :=
  (∀ i < n_max, st.present i ≤ 1) ∧
  (∀ i < n_max, st.present i ≠ 0 → st.keys i < U ∧ st.vals i < V) ∧
  (∀ i < n_max, ∀ j < n_max, st.present i ≠ 0 → st.present j ≠ 0 →
    st.keys i = st.keys j → i = j) ∧
  ∀ u : Fin U,
    (dict u = none ↔ ∀ i < n_max, st.present i ≠ 0 → st.keys i ≠ u.val) ∧
    ∀ v, dict u = some v ↔ ∃ i < n_max, st.present i ≠ 0 ∧ st.keys i = u.val ∧ st.vals i = v

theorem validSmallState_empty (U V n_max : ℕ) :
    ValidSmallState U V n_max emptySmallState (Dictionary.empty U) := by
  refine ⟨fun _ _ => Nat.zero_le 1, fun _ _ h => absurd rfl h,
    fun _ _ _ _ h => absurd rfl h, fun u => ⟨?_, fun v => ?_⟩⟩
  · simp [Dictionary.empty, emptySmallState]
  · simp [Dictionary.empty, emptySmallState]

private theorem smallScan_props (st : SmallDictState) (u_val : ℕ) (k : ℕ) :
    let (f1, free1) := smallScan st u_val k
    (f1 = 0 ↔ ∀ i < k, st.present i ≠ 0 → st.keys i ≠ u_val) ∧
    (f1 ≠ 0 → f1 - 1 < k ∧ st.present (f1 - 1) ≠ 0 ∧ st.keys (f1 - 1) = u_val) ∧
    (free1 = 0 ↔ ∀ i < k, st.present i ≠ 0) ∧
    (free1 ≠ 0 → free1 - 1 < k ∧ st.present (free1 - 1) = 0) := by
  induction k with
  | zero => simp [smallScan]
  | succ k ih =>
    simp only [smallScan, smallScanStep, Nat.forall_lt_succ_right] at ih ⊢
    split_ifs <;> grind

/-- Small-regime lookup matches `dict u`. -/
theorem smallQuery_spec {U V n_max : ℕ} {st : SmallDictState} {dict : State U}
    (hv : ValidSmallState U V n_max st dict) (u : Fin U) :
    smallQuery n_max st u.val = dict u := by
  obtain ⟨_, _, hinj, hmap⟩ := hv
  have hsc := smallScan_props st u.val n_max
  unfold smallQuery
  set p := smallScan st u.val n_max
  by_cases hf0 : p.1 = 0
  · simp only [hf0, ↓reduceIte]
    exact ((hmap u).1.mpr (hsc.1.mp hf0)).symm
  · simp only [hf0, ↓reduceIte]
    obtain ⟨hlt, hp, hk⟩ := hsc.2.1 hf0
    symm
    exact ((hmap u).2 (st.vals (p.1 - 1))).mpr ⟨p.1 - 1, hlt, hp, hk, rfl⟩

/-- The `none` clause of a small-regime slot map follows from its `some` clause. -/
private theorem smallMap_of_some_iff {o : Option ℕ} {n q : ℕ} {P K W : ℕ → ℕ}
    (h : ∀ v, o = some v ↔ ∃ i < n, P i ≠ 0 ∧ K i = q ∧ W i = v) :
    (o = none ↔ ∀ i < n, P i ≠ 0 → K i ≠ q) ∧
      ∀ v, o = some v ↔ ∃ i < n, P i ≠ 0 ∧ K i = q ∧ W i = v := by
  refine ⟨⟨fun ho i hi hp hq => ?_, fun hall => ?_⟩, h⟩
  · simpa [ho] using (h (W i)).mpr ⟨i, hi, hp, hq, rfl⟩
  · rcases ho : o with _ | v
    · rfl
    · obtain ⟨i, hi, hp, hq, -⟩ := (h v).mp ho
      exact absurd hq (hall i hi hp)

/-- Small-regime deletion preserves `ValidSmallState` and refines `Function.update dict u none`. -/
theorem smallDelete_spec {U V n_max : ℕ} {st : SmallDictState} {dict : State U}
    (hv : ValidSmallState U V n_max st dict) (u : Fin U) :
    ValidSmallState U V n_max (smallDelete n_max st u.val) (Function.update dict u none) := by
  obtain ⟨hp_le, hkv, hinj, hmap⟩ := hv
  have hsc := smallScan_props st u.val n_max
  unfold smallDelete
  set p := smallScan st u.val n_max
  by_cases hf0 : p.1 = 0
  · simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
    rw [show Function.update dict u none = dict from
      Function.update_eq_self_iff.mpr ((hmap u).1.mpr (hsc.1.mp hf0)).symm]
    exact ⟨hp_le, hkv, hinj, hmap⟩
  · obtain ⟨hidx_lt, hp_idx, hk_idx⟩ := hsc.2.1 hf0
    simp only [bne_iff_ne, ne_eq, hf0, not_false_eq_true, ↓reduceIte]
    clear hsc
    refine ⟨?_, ?_, ?_, fun x => smallMap_of_some_iff fun v => ?_⟩ <;>
      simp only [Function.update_apply]
    · grind
    · grind
    · grind
    · grind [Fin.ext_iff]

/-- Small-regime insertion preserves `ValidSmallState` and refines
`Function.update dict u (some v)` whenever `Dynamic.valid V n_max dict (.insert u v)`. -/
theorem smallInsert_spec {U V n_max : ℕ} {st : SmallDictState} {dict : State U}
    (hv : ValidSmallState U V n_max st dict) {u : Fin U} {v : ℕ}
    (hvalid : Dynamic.valid V n_max dict (.insert u v)) :
    ValidSmallState U V n_max (smallInsert n_max st u.val v)
      (Function.update dict u (some v)) := by
  obtain ⟨hcap, hv_lt⟩ := hvalid
  obtain ⟨hp_le, hkv, hinj, hmap⟩ := hv
  have hsc := smallScan_props st u.val n_max
  unfold smallInsert
  set p := smallScan st u.val n_max
  by_cases hf0 : p.1 = 0
  · have hnone_u : dict u = none := (hmap u).1.mpr (hsc.1.mp hf0)
    have hfr_ne : p.2 ≠ 0 := by
      intro hfr0
      have hall_act : ∀ i < n_max, st.present i ≠ 0 := hsc.2.2.1.mp hfr0
      let toKey : Fin n_max → Fin U := fun i =>
        ⟨st.keys i.val, (hkv i.val i.isLt (hall_act i.val i.isLt)).1⟩
      have hto_inj : Function.Injective toKey := fun i j heq =>
        Fin.ext (hinj i.val i.isLt j.val j.isLt (hall_act i.val i.isLt)
          (hall_act j.val j.isLt) (congrArg Fin.val heq))
      have hto_mem : ∀ i : Fin n_max, toKey i ∈ Dictionary.dom dict := fun i => by
        by_contra hnot
        rw [Dictionary.notMem_dom_iff] at hnot
        exact (hmap (toKey i)).1.mp hnot i.val i.isLt (hall_act i.val i.isLt) rfl
      have hle : n_max ≤ #(Dictionary.dom dict) := by
        simpa using card_le_card_of_injOn (s := univ) toKey (fun i _ => hto_mem i) hto_inj.injOn
      rcases hcap with hlt | hsome
      · omega
      · simp [hnone_u] at hsome
    obtain ⟨hidx_lt, hp0_idx⟩ := hsc.2.2.2 hfr_ne
    have hfree := hsc.1.mp hf0
    clear hsc hcap hnone_u
    simp only [hf0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte, bne_iff_ne, ne_eq,
      hfr_ne, not_false_eq_true]
    refine ⟨?_, ?_, ?_, fun x => smallMap_of_some_iff fun w => ?_⟩ <;>
      simp only [Function.update_apply]
    · grind
    · grind
    · grind
    · grind [Fin.ext_iff]
  · obtain ⟨hidx_lt, hp_idx, hk_idx⟩ := hsc.2.1 hf0
    simp only [bne_iff_ne, ne_eq, hf0, not_false_eq_true, ↓reduceIte]
    clear hsc hcap
    refine ⟨hp_le, ?_, hinj, fun x => smallMap_of_some_iff fun w => ?_⟩ <;>
      simp only [Function.update_apply]
    · grind
    · grind [Fin.ext_iff]

/-! ## Section 2: In-place cycle-following slot rearrangement (`permuteByTarget`) -/

/-- State tuple `(running, curDest, curQ, curV, act, qArr, vArr)` for `permuteInnerStep`. -/
abbrev PermChainState := Bool × ℕ × ℕ × ℕ × (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ)

/-- Single step of a cycle-following chain along `dest`. -/
@[expose] def permuteInnerStep (dest : ℕ → ℕ) (st : PermChainState) : PermChainState :=
  let (running, curDest, curQ, curV, act, qArr, vArr) := st
  if !running then st
  else if act curDest then
    let nxtDest := dest curDest
    let nxtQ := qArr curDest
    let nxtV := vArr curDest
    (true, nxtDest, nxtQ, nxtV,
      Function.update act curDest false,
      Function.update qArr curDest curQ,
      Function.update vArr curDest curV)
  else
    (false, curDest, curQ, curV, act,
      Function.update qArr curDest curQ,
      Function.update vArr curDest curV)

/-- Run `k` steps of `permuteInnerStep`. -/
@[expose] def permuteInnerLoop (dest : ℕ → ℕ) : ℕ → PermChainState → PermChainState
  | 0, st => st
  | k + 1, st => permuteInnerLoop dest k (permuteInnerStep dest st)

/-- Outer step at source slot `s`: if `act s` is still `true`, extracts `(qArr s, vArr s)` and runs
`n_max` inner chain steps. -/
@[expose] def permuteOuterStep (n_max : ℕ) (dest : ℕ → ℕ) (s : ℕ)
    (triple : (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ)) :
    (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ) :=
  let (act, qArr, vArr) := triple
  if act s then
    let st₀ : PermChainState :=
      (true, dest s, qArr s, vArr s, Function.update act s false, qArr, vArr)
    let (_, _, _, _, act', qArr', vArr') := permuteInnerLoop dest n_max st₀
    (act', qArr', vArr')
  else triple

/-- Run `permuteOuterStep` across `s = 0 .. k - 1`. -/
@[expose] def permuteOuterLoop (n_max : ℕ) (dest : ℕ → ℕ) :
    ℕ → (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → Bool) × (ℕ → ℕ) × (ℕ → ℕ)
  | 0, triple => triple
  | k + 1, triple => permuteOuterStep n_max dest k (permuteOuterLoop n_max dest k triple)

/-- Rearrange `(qArr, vArr)` in place across `0 .. n_max - 1` so every `s < n_max` with
`act₀ s = true` lands at `dest s`. -/
@[expose] def permuteByTarget (n_max : ℕ) (dest : ℕ → ℕ) (act₀ : ℕ → Bool)
    (qArr vArr : ℕ → ℕ) : (ℕ → ℕ) × (ℕ → ℕ) :=
  let actInit : ℕ → Bool := fun i => decide (i < n_max) && act₀ i
  let (_, qArr', vArr') := permuteOuterLoop n_max dest n_max (actInit, qArr, vArr)
  (qArr', vArr')

private def PermOuterInv (_n_max : ℕ) (dest : ℕ → ℕ) (A₀ placed : Finset ℕ)
    (q₀ v₀ : ℕ → ℕ) (Q_bnd V_bnd : ℕ)
    (act : ℕ → Bool) (qArr vArr : ℕ → ℕ) : Prop :=
  placed ⊆ A₀ ∧
  (∀ i, act i = true ↔ i ∈ A₀ \ placed) ∧
  (∀ s ∈ A₀ \ placed, qArr s = q₀ s ∧ vArr s = v₀ s) ∧
  (∀ p ∈ placed, qArr (dest p) = q₀ p ∧ vArr (dest p) = v₀ p) ∧
  (∀ i, qArr i < Q_bnd ∧ vArr i < V_bnd)

private theorem permuteInnerLoop_spec {n_max : ℕ} {dest : ℕ → ℕ} {A₀ : Finset ℕ}
    (_hA₀ : ∀ s ∈ A₀, s < n_max)
    (hinj : ∀ s₁ ∈ A₀, ∀ s₂ ∈ A₀, dest s₁ = dest s₂ → s₁ = s₂)
    {q₀ v₀ : ℕ → ℕ} {Q_bnd V_bnd : ℕ}
    (hqv₀ : ∀ i, q₀ i < Q_bnd ∧ v₀ i < V_bnd) :
    ∀ (k : ℕ) (st : PermChainState) (placed : Finset ℕ),
      (if st.1 = false then
        PermOuterInv n_max dest A₀ placed q₀ v₀ Q_bnd V_bnd st.2.2.2.2.1 st.2.2.2.2.2.1
          st.2.2.2.2.2.2
      else
        ∃ p_cur ∈ A₀,
          p_cur ∉ placed ∧
          placed ⊆ A₀ ∧
          #(A₀ \ insert p_cur placed) + 1 ≤ k ∧
          st.2.1 = dest p_cur ∧
          st.2.2.1 = q₀ p_cur ∧
          st.2.2.2.1 = v₀ p_cur ∧
          (∀ i, st.2.2.2.2.1 i = true ↔ i ∈ A₀ \ insert p_cur placed) ∧
          (∀ s ∈ A₀ \ insert p_cur placed,
            st.2.2.2.2.2.1 s = q₀ s ∧ st.2.2.2.2.2.2 s = v₀ s) ∧
          (∀ p ∈ placed,
            st.2.2.2.2.2.1 (dest p) = q₀ p ∧ st.2.2.2.2.2.2 (dest p) = v₀ p) ∧
          (∀ i, st.2.2.2.2.2.1 i < Q_bnd ∧ st.2.2.2.2.2.2 i < V_bnd)) →
      let st' := permuteInnerLoop dest k st
      st'.1 = false ∧
      ∃ placed', placed ⊆ placed' ∧
        (∀ i, st.2.2.2.2.1 i = false → i ∈ A₀ → i ∈ placed') ∧
        PermOuterInv n_max dest A₀ placed' q₀ v₀ Q_bnd V_bnd st'.2.2.2.2.1 st'.2.2.2.2.2.1
          st'.2.2.2.2.2.2 := by
  intro k
  induction k with
  | zero =>
    intro st placed hinv
    rcases hrun : st.1 with _ | _
    · simp only [hrun, ↓reduceIte] at hinv
      refine ⟨hrun, placed, Subset.rfl, fun i hfalse hiA => ?_, hinv⟩
      by_contra hnp
      have ht := (hinv.2.1 i).mpr (mem_sdiff.mpr ⟨hiA, hnp⟩)
      rw [hfalse] at ht; cases ht
    · simp only [hrun, Bool.true_eq_false, ↓reduceIte] at hinv
      obtain ⟨_, _, _, _, hle0, _⟩ := hinv
      omega
  | succ k ih =>
    intro st placed hinv
    rcases st with ⟨running, curDest, curQ, curV, act, qArr, vArr⟩
    dsimp only [permuteInnerLoop]
    cases running
    · simp only [↓reduceIte] at hinv
      have hstep : permuteInnerStep dest (false, curDest, curQ, curV, act, qArr, vArr) =
          (false, curDest, curQ, curV, act, qArr, vArr) := rfl
      rw [hstep]
      exact ih (false, curDest, curQ, curV, act, qArr, vArr) placed (by simpa using hinv)
    · simp only [Bool.true_eq_false, ↓reduceIte] at hinv
      obtain ⟨p_cur, hp_in, hp_not, hpl_sub, hk_le, hd_eq, hq_eq, hv_eq, hact, hunext, hpl,
        hbnd⟩ := hinv
      subst hd_eq hq_eq hv_eq
      set extSet := insert p_cur placed
      have hext_sub : extSet ⊆ A₀ := insert_subset_iff.mpr ⟨hp_in, hpl_sub⟩
      have hbnd' : ∀ i,
          Function.update qArr (dest p_cur) (q₀ p_cur) i < Q_bnd ∧
          Function.update vArr (dest p_cur) (v₀ p_cur) i < V_bnd := by
        intro i
        by_cases h : i = dest p_cur
        · subst h; simp [(hqv₀ p_cur).1, (hqv₀ p_cur).2]
        · simp [h, (hbnd i).1, (hbnd i).2]
      have hpl' : ∀ p ∈ extSet,
          Function.update qArr (dest p_cur) (q₀ p_cur) (dest p) = q₀ p ∧
          Function.update vArr (dest p_cur) (v₀ p_cur) (dest p) = v₀ p := by
        intro p hp
        rcases mem_insert.mp hp with rfl | hp_old
        · simp
        · have hne_p : p ≠ p_cur := fun heq => hp_not (heq ▸ hp_old)
          have hne_d : dest p ≠ dest p_cur := fun hd =>
            hne_p (hinj p (hpl_sub hp_old) p_cur hp_in hd)
          simp [hne_d, (hpl p hp_old).1, (hpl p hp_old).2]
      dsimp only [permuteInnerStep]
      simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      cases hact_d : act (dest p_cur)
      · simp only [Bool.false_eq_true, ↓reduceIte]
        have hd_not_sdiff : dest p_cur ∉ A₀ \ extSet := fun hm =>
          Bool.false_ne_true (hact_d.symm.trans ((hact _).mpr hm))
        have hout_step : PermOuterInv n_max dest A₀ extSet q₀ v₀ Q_bnd V_bnd
            act (Function.update qArr (dest p_cur) (q₀ p_cur))
            (Function.update vArr (dest p_cur) (v₀ p_cur)) := by
          refine ⟨hext_sub, hact, ?_, hpl', hbnd'⟩
          intro s hs
          have hne_s : s ≠ dest p_cur := fun heq => hd_not_sdiff (heq ▸ hs)
          simp [hne_s, (hunext s hs).1, (hunext s hs).2]
        obtain ⟨hrun', placed', hsub', hfalse', hout'⟩ := ih
          (false, dest p_cur, q₀ p_cur, v₀ p_cur, act,
            Function.update qArr (dest p_cur) (q₀ p_cur),
            Function.update vArr (dest p_cur) (v₀ p_cur))
          extSet (by simpa using hout_step)
        refine ⟨hrun', placed', (subset_insert _ _).trans hsub', fun i hfi hiA => ?_, hout'⟩
        exact hfalse' i hfi hiA
      · simp only [↓reduceIte]
        have hd_mem : dest p_cur ∈ A₀ \ extSet := (hact (dest p_cur)).mp hact_d
        have hd_in_A : dest p_cur ∈ A₀ := (mem_sdiff.mp hd_mem).1
        have hd_not_ext : dest p_cur ∉ extSet := (mem_sdiff.mp hd_mem).2
        have hqv_d := hunext (dest p_cur) hd_mem
        rw [hqv_d.1, hqv_d.2]
        have hcard_lt : #(A₀ \ insert (dest p_cur) extSet) < #(A₀ \ extSet) := by
          have hsdiff_eq : A₀ \ insert (dest p_cur) extSet = (A₀ \ extSet).erase (dest p_cur) := by
            ext x; simp [mem_sdiff, mem_insert, and_left_comm]
          rw [hsdiff_eq]
          exact card_erase_lt_of_mem hd_mem
        have hinv_nxt : ∃ p_nxt ∈ A₀,
            p_nxt ∉ extSet ∧
            extSet ⊆ A₀ ∧
            #(A₀ \ insert p_nxt extSet) + 1 ≤ k ∧
            dest (dest p_cur) = dest p_nxt ∧
            q₀ (dest p_cur) = q₀ p_nxt ∧
            v₀ (dest p_cur) = v₀ p_nxt ∧
            (∀ i, Function.update act (dest p_cur) false i = true ↔
              i ∈ A₀ \ insert p_nxt extSet) ∧
            (∀ s ∈ A₀ \ insert p_nxt extSet,
              Function.update qArr (dest p_cur) (q₀ p_cur) s = q₀ s ∧
              Function.update vArr (dest p_cur) (v₀ p_cur) s = v₀ s) ∧
            (∀ p ∈ extSet,
              Function.update qArr (dest p_cur) (q₀ p_cur) (dest p) = q₀ p ∧
              Function.update vArr (dest p_cur) (v₀ p_cur) (dest p) = v₀ p) ∧
            (∀ i,
              Function.update qArr (dest p_cur) (q₀ p_cur) i < Q_bnd ∧
              Function.update vArr (dest p_cur) (v₀ p_cur) i < V_bnd) := by
          refine ⟨dest p_cur, hd_in_A, hd_not_ext, hext_sub, by omega, rfl, rfl, rfl,
            ?_, ?_, hpl', hbnd'⟩
          · intro i
            by_cases hi : i = dest p_cur
            · subst hi; simp
            · simp only [Function.update_of_ne hi, hact i, mem_sdiff, mem_insert, hi, false_or]
          · intro s hs
            have hne_s : s ≠ dest p_cur := fun h => by subst h; simp at hs
            have hs_old : s ∈ A₀ \ extSet := by
              rw [mem_sdiff, mem_insert] at hs
              exact mem_sdiff.mpr ⟨hs.1, fun h => hs.2 (Or.inr h)⟩
            simp [hne_s, (hunext s hs_old).1, (hunext s hs_old).2]
        obtain ⟨hrun', placed', hsub', hfalse', hout'⟩ := ih
          (true, dest (dest p_cur), q₀ (dest p_cur), v₀ (dest p_cur),
            Function.update act (dest p_cur) false,
            Function.update qArr (dest p_cur) (q₀ p_cur),
            Function.update vArr (dest p_cur) (v₀ p_cur))
          extSet (by simpa using hinv_nxt)
        refine ⟨hrun', placed', (subset_insert _ _).trans hsub', fun i hfi hiA => ?_, hout'⟩
        by_cases hi_d : i = dest p_cur
        · subst hi_d; rw [hact_d] at hfi; cases hfi
        · exact hfalse' i (by simpa [hi_d] using hfi) hiA

/-- **Exact in-place permutation theorem (`permuteByTarget_spec`)**:
if `dest` is injective on `A₀ = {s < n_max | act₀ s = true}` and maps `A₀` into `< n_max`, then
`permuteByTarget` places `(q₀ s, v₀ s)` at `dest s` for every `s ∈ A₀` while preserving global
value bounds `(Q_bnd, V_bnd)`. -/
theorem permuteByTarget_spec {n_max : ℕ} {dest : ℕ → ℕ} {act₀ : ℕ → Bool}
    {q₀ v₀ : ℕ → ℕ} {Q_bnd V_bnd : ℕ}
    (hinj : ∀ s₁ < n_max, ∀ s₂ < n_max, act₀ s₁ = true → act₀ s₂ = true →
      dest s₁ = dest s₂ → s₁ = s₂)
    (hqv₀ : ∀ i, q₀ i < Q_bnd ∧ v₀ i < V_bnd) :
    let (q', v') := permuteByTarget n_max dest act₀ q₀ v₀
    (∀ s < n_max, act₀ s = true → q' (dest s) = q₀ s ∧ v' (dest s) = v₀ s) ∧
    (∀ i, q' i < Q_bnd ∧ v' i < V_bnd) := by
  let A₀ : Finset ℕ := (range n_max).filter fun s => act₀ s = true
  have hA₀_lt : ∀ s ∈ A₀, s < n_max := fun s hs => mem_range.mp (mem_filter.mp hs).1
  have hinj_A : ∀ s₁ ∈ A₀, ∀ s₂ ∈ A₀, dest s₁ = dest s₂ → s₁ = s₂ := fun s₁ h₁ s₂ h₂ hd =>
    hinj s₁ (hA₀_lt s₁ h₁) s₂ (hA₀_lt s₂ h₂) (mem_filter.mp h₁).2 (mem_filter.mp h₂).2 hd
  let actInit : ℕ → Bool := fun i => decide (i < n_max) && act₀ i
  have houter : ∀ k ≤ n_max,
      let (act_k, q_k, v_k) := permuteOuterLoop n_max dest k (actInit, q₀, v₀)
      ∃ placed, (∀ s ∈ A₀, s < k → s ∈ placed) ∧
        PermOuterInv n_max dest A₀ placed q₀ v₀ Q_bnd V_bnd act_k q_k v_k := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨∅, fun _ _ hs => absurd hs (Nat.not_lt_zero _), empty_subset _, ?_,
        fun _ _ => ⟨rfl, rfl⟩, fun _ hp => absurd hp (notMem_empty _), hqv₀⟩
      intro i
      simp [actInit, A₀]
    | succ k ih =>
      obtain ⟨placed, hcov, hout⟩ := ih (Nat.le_of_succ_le hk)
      dsimp only [permuteOuterLoop]
      set tr := permuteOuterLoop n_max dest k (actInit, q₀, v₀)
      dsimp only [permuteOuterStep]
      cases hact_k : tr.1 k
      · simp only [Bool.false_eq_true, ↓reduceIte]
        refine ⟨placed, fun s hsA hslt => ?_, hout⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hslt with hlt | rfl
        · exact hcov s hsA hlt
        · by_contra hnp
          have ht := (hout.2.1 s).mpr (mem_sdiff.mpr ⟨hsA, hnp⟩)
          rw [hact_k] at ht; cases ht
      · simp only [↓reduceIte]
        have hk_mem : k ∈ A₀ \ placed := (hout.2.1 k).mp hact_k
        have hk_A : k ∈ A₀ := (mem_sdiff.mp hk_mem).1
        have hk_np : k ∉ placed := (mem_sdiff.mp hk_mem).2
        have hqv_k := hout.2.2.1 k hk_mem
        have hcard_le : #(A₀ \ insert k placed) + 1 ≤ n_max := by
          have hsub : A₀ \ insert k placed ⊆ (range n_max).erase k := by
            intro x hx
            rw [mem_sdiff, mem_insert] at hx
            exact mem_erase.mpr ⟨fun heq => hx.2 (Or.inl heq), mem_range.mpr (hA₀_lt x hx.1)⟩
          have hc1 := card_le_card hsub
          have hc2 : #((range n_max).erase k) = n_max - 1 := by
            rw [card_erase_of_mem (mem_range.mpr (by omega)), card_range]
          omega
        have hloop := permuteInnerLoop_spec hA₀_lt hinj_A hqv₀ n_max
          (true, dest k, tr.2.1 k, tr.2.2 k, Function.update tr.1 k false, tr.2.1, tr.2.2)
          placed <| by
            simp only [Bool.true_eq_false, ↓reduceIte]
            refine ⟨k, hk_A, hk_np, hout.1, hcard_le, rfl, hqv_k.1, hqv_k.2, ?_, ?_, hout.2.2.2.1,
              hout.2.2.2.2⟩
            · intro i
              by_cases hik : i = k
              · subst hik; simp
              · simp only [Function.update_of_ne hik, hout.2.1 i, mem_sdiff, mem_insert, hik,
                  false_or]
            · intro s hs
              have hs_old : s ∈ A₀ \ placed := by
                rw [mem_sdiff, mem_insert] at hs
                exact mem_sdiff.mpr ⟨hs.1, fun hp => hs.2 (Or.inr hp)⟩
              exact hout.2.2.1 s hs_old
        obtain ⟨_, placed', hpl_sub, hfalse_in, hout'⟩ := hloop
        refine ⟨placed', fun s hsA hslt => ?_, hout'⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hslt with hlt | rfl
        · exact hpl_sub (hcov s hsA hlt)
        · exact hfalse_in s (by simp) hsA
  obtain ⟨placed, hcov, hout⟩ := houter n_max le_rfl
  dsimp only [permuteByTarget]
  refine ⟨fun s hs_lt hact_s => ?_, hout.2.2.2.2⟩
  have hsA : s ∈ A₀ := mem_filter.mpr ⟨mem_range.mpr hs_lt, hact_s⟩
  exact hout.2.2.2.1 s (hcov s hsA hs_lt)

/-! ## Section 3: Compressed-sparse-row (`CsrState`) fallback dictionary and `GoodSeedOnState` -/

/-- Compressed-sparse-row bucket fallback state over `M = numBucketsWhp n_max` Feistel buckets. -/
structure CsrState where
  /-- Bucket boundary prefix sums `fbStart 0 = 0 ≤ fbStart 1 ≤ … ≤ fbStart M ≤ n_max`. -/
  fbStart : ℕ → ℕ
  /-- Stored Feistel quotients `< 2 ^ quotBitsWhp U n_max`. -/
  qArr : ℕ → ℕ
  /-- Stored values `< V`. -/
  vArr : ℕ → ℕ

/-- Scan `len` slots starting at `lo` for `qArr (lo + k) == q_val`, returning `0` if absent or
`(lo + k) + 1` for the matching index. -/
@[expose] def csrScanRange (qArr : ℕ → ℕ) (lo q_val : ℕ) : ℕ → ℕ
  | 0 => 0
  | len + 1 =>
    let prev := csrScanRange qArr lo q_val len
    if prev != 0 then prev
    else if qArr (lo + len) == q_val then (lo + len) + 1
    else 0

/-- Shift `(qArr, vArr)` down by 1 across `i₀ .. i₀ + cnt - 1`
(`arr'[i₀ + k] = arr[i₀ + k + 1]`). -/
@[expose] def csrShiftDown (i₀ : ℕ) : ℕ → (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | 0, p => p
  | cnt + 1, p =>
    let (q1, v1) := csrShiftDown i₀ cnt p
    let pos := i₀ + cnt
    (Function.update q1 pos (q1 (pos + 1)), Function.update v1 pos (v1 (pos + 1)))

/-- Shift `(qArr, vArr)` up by 1 from `N` down across `cnt` elements (`idx = N - k`). -/
@[expose] def csrShiftUp (N : ℕ) : ℕ → (ℕ → ℕ) × (ℕ → ℕ) → (ℕ → ℕ) × (ℕ → ℕ)
  | 0, p => p
  | cnt + 1, p =>
    let (q1, v1) := csrShiftUp N cnt p
    let idx := N - cnt
    (Function.update q1 idx (q1 (idx - 1)), Function.update v1 idx (v1 (idx - 1)))

/-- Adjust `fbStart (b + 1 + k)` by `-1` (if `dec = true`) or `+1` (if `dec = false`) for
`k = 0 .. cnt - 1`. -/
@[expose] def csrAdjustStarts (b : ℕ) (dec : Bool) : ℕ → (ℕ → ℕ) → (ℕ → ℕ)
  | 0, f => f
  | cnt + 1, f =>
    let f1 := csrAdjustStarts b dec cnt f
    let idx := b + 1 + cnt
    Function.update f1 idx (if dec then f1 idx - 1 else f1 idx + 1)

/-- CSR fallback lookup of `(b, q_val)`. -/
@[expose] def csrQuery (csr : CsrState) (b q_val : ℕ) : Option ℕ :=
  let lo := csr.fbStart b
  let len := csr.fbStart (b + 1) - lo
  let f1 := csrScanRange csr.qArr lo q_val len
  if f1 = 0 then none else some (csr.vArr (f1 - 1))

/-- CSR fallback deletion of `(b, q_val)` across `M` buckets. -/
@[expose] def csrDelete (M : ℕ) (csr : CsrState) (b q_val : ℕ) : CsrState :=
  let lo := csr.fbStart b
  let len := csr.fbStart (b + 1) - lo
  let f1 := csrScanRange csr.qArr lo q_val len
  if f1 != 0 then
    let i₀ := f1 - 1
    let N := csr.fbStart M
    let (q', v') := csrShiftDown i₀ (N - 1 - i₀) (csr.qArr, csr.vArr)
    let fb' := csrAdjustStarts b true (M - b) csr.fbStart
    ⟨fb', q', v'⟩
  else csr

/-- CSR fallback insertion / overwrite of `(b, q_val, v_val)` across `M` buckets. -/
@[expose] def csrInsert (M : ℕ) (csr : CsrState) (b q_val v_val : ℕ) : CsrState :=
  let lo := csr.fbStart b
  let hi := csr.fbStart (b + 1)
  let f1 := csrScanRange csr.qArr lo q_val (hi - lo)
  if f1 != 0 then
    { csr with vArr := Function.update csr.vArr (f1 - 1) v_val }
  else
    let N := csr.fbStart M
    let (q1, v1) := csrShiftUp N (N - hi) (csr.qArr, csr.vArr)
    let q' := Function.update q1 hi q_val
    let v' := Function.update v1 hi v_val
    let fb' := csrAdjustStarts b false (M - b) csr.fbStart
    ⟨fb', q', v'⟩

/-- Exact invariant relating `CsrState` to `dict : Dictionary.State U` under bucket hash `h1`. -/
@[expose] def ValidCsrState (U V n_max : ℕ) (h1 : ℕ → ℕ) (csr : CsrState)
    (dict : State U) : Prop :=
  let M := numBucketsWhp n_max
  csr.fbStart 0 = 0 ∧
  (∀ b < M, csr.fbStart b ≤ csr.fbStart (b + 1)) ∧
  csr.fbStart M ≤ n_max ∧
  (∀ b < M, ∀ i, csr.fbStart b ≤ i → i < csr.fbStart (b + 1) →
    let u_val := feistelReconstruct (bWhp n_max) h1 b (csr.qArr i)
    u_val < U ∧
    feistelBucket (bWhp n_max) h1 u_val = b ∧
    keyQuotient (bWhp n_max) u_val = csr.qArr i ∧
    csr.qArr i < 2 ^ quotBitsWhp U n_max ∧
    csr.vArr i < V) ∧
  (∀ b < M, ∀ i j, csr.fbStart b ≤ i → i < csr.fbStart (b + 1) →
    csr.fbStart b ≤ j → j < csr.fbStart (b + 1) → csr.qArr i = csr.qArr j → i = j) ∧
  ∀ u : Fin U,
    let b := feistelBucket (bWhp n_max) h1 u.val
    let q := keyQuotient (bWhp n_max) u.val
    (dict u = none ↔ ∀ i, csr.fbStart b ≤ i → i < csr.fbStart (b + 1) → csr.qArr i ≠ q) ∧
    ∀ v, dict u = some v ↔
      ∃ i, csr.fbStart b ≤ i ∧ i < csr.fbStart (b + 1) ∧ csr.qArr i = q ∧ csr.vArr i = v

theorem fbStart_mono_of_adj {M : ℕ} {f : ℕ → ℕ} (hadj : ∀ b < M, f b ≤ f (b + 1)) :
    ∀ a b, a ≤ b → b ≤ M → f a ≤ f b := by
  intro a b hab hbM
  induction b with
  | zero =>
    have ha0 : a = 0 := by omega
    subst ha0; exact le_rfl
  | succ b ih =>
    rcases Nat.eq_or_lt_of_le hab with rfl | hlt
    · exact le_rfl
    · exact (ih (by omega) (by omega)).trans (hadj b (by omega))

private theorem csrScanRange_props (qArr : ℕ → ℕ) (lo q_val len : ℕ) :
    let f1 := csrScanRange qArr lo q_val len
    (f1 = 0 ↔ ∀ i, lo ≤ i → i < lo + len → qArr i ≠ q_val) ∧
    (f1 ≠ 0 → lo ≤ f1 - 1 ∧ f1 - 1 < lo + len ∧ qArr (f1 - 1) = q_val) := by
  induction len with
  | zero => simp only [csrScanRange]; grind
  | succ len ih =>
    simp only [csrScanRange] at ih ⊢
    split_ifs <;> grind

private theorem csrScanRange_to_props (qArr : ℕ → ℕ) (q : ℕ) {lo hi : ℕ} (hle : lo ≤ hi) :
    let hit := csrScanRange qArr lo q (hi - lo)
    (hit = 0 ↔ ∀ i, lo ≤ i → i < hi → qArr i ≠ q) ∧
    (hit ≠ 0 → lo ≤ hit - 1 ∧ hit - 1 < hi ∧ qArr (hit - 1) = q) := by
  have h := csrScanRange_props qArr lo q (hi - lo)
  dsimp only at h ⊢
  rw [Nat.add_sub_of_le hle] at h
  exact h

theorem csrShiftDown_apply (i₀ cnt : ℕ) (qArr vArr : ℕ → ℕ) (x : ℕ) :
    (csrShiftDown i₀ cnt (qArr, vArr)).1 x =
      (if i₀ ≤ x ∧ x < i₀ + cnt then qArr (x + 1) else qArr x) ∧
    (csrShiftDown i₀ cnt (qArr, vArr)).2 x =
      (if i₀ ≤ x ∧ x < i₀ + cnt then vArr (x + 1) else vArr x) := by
  induction cnt generalizing x with
  | zero => simp [csrShiftDown]
  | succ cnt ih =>
    dsimp only [csrShiftDown]
    simp only [Function.update_apply, ih]
    split_ifs <;> subst_vars <;> first | exact ⟨rfl, rfl⟩ | omega

theorem csrShiftUp_apply (N cnt : ℕ) (hcnt : cnt ≤ N) (qArr vArr : ℕ → ℕ) (x : ℕ) :
    (csrShiftUp N cnt (qArr, vArr)).1 x =
      (if N - cnt < x ∧ x ≤ N then qArr (x - 1) else qArr x) ∧
    (csrShiftUp N cnt (qArr, vArr)).2 x =
      (if N - cnt < x ∧ x ≤ N then vArr (x - 1) else vArr x) := by
  induction cnt generalizing x with
  | zero => simp [csrShiftUp]
  | succ cnt ih =>
    dsimp only [csrShiftUp]
    simp only [Function.update_apply, ih (by omega)]
    split_ifs <;> subst_vars <;> first | exact ⟨rfl, rfl⟩ | omega

private theorem csrAdjustStarts_apply (b : ℕ) (dec : Bool) (cnt : ℕ) (f : ℕ → ℕ) (x : ℕ) :
    csrAdjustStarts b dec cnt f x =
      if b + 1 ≤ x ∧ x < b + 1 + cnt then
        (if dec then f x - 1 else f x + 1)
      else f x := by
  induction cnt generalizing x with
  | zero => simp [csrAdjustStarts]
  | succ cnt ih =>
    simp only [csrAdjustStarts, Function.update_apply, ih]
    split_ifs <;> subst_vars <;> omega

/-- Exact bucket-slice bijection for `ValidCsrState`: for every `b : Fin (numBucketsWhp n_max)`,
`(Dictionary.dom dict).filter (feistelBucket = b)` has cardinality
`csr.fbStart (b + 1) - csr.fbStart b`, and `#(Dictionary.dom dict) = csr.fbStart M`. -/
theorem ValidCsrState.bucket_and_dom_card {U V n_max : ℕ} {h1 : ℕ → ℕ} {csr : CsrState}
    {dict : State U} (hv : ValidCsrState U V n_max h1 csr dict) :
    (∀ b : Fin (numBucketsWhp n_max),
      #((Dictionary.dom dict).filter fun u =>
        feistelBucket (bWhp n_max) h1 u.val = b.val) =
        csr.fbStart (b.val + 1) - csr.fbStart b.val) ∧
    #(Dictionary.dom dict) = csr.fbStart (numBucketsWhp n_max) := by
  obtain ⟨hfb0, hadj, _, hvalid_i, hinj, hmap⟩ := hv
  have hper_b : ∀ b : Fin (numBucketsWhp n_max),
      #((Dictionary.dom dict).filter fun u =>
        feistelBucket (bWhp n_max) h1 u.val = b.val) =
        csr.fbStart (b.val + 1) - csr.fbStart b.val := by
    intro b
    -- The slice `[fbStart b, fbStart (b + 1))` maps bijectively onto the keys of bucket `b`.
    let g : ℕ → ℕ := fun i => feistelReconstruct (bWhp n_max) h1 b.val (csr.qArr i)
    have himg : (Ico (csr.fbStart b.val) (csr.fbStart (b.val + 1))).image g =
        ((Dictionary.dom dict).filter fun u =>
          feistelBucket (bWhp n_max) h1 u.val = b.val).map Fin.valEmbedding := by
      ext x
      simp only [mem_image, mem_map, mem_filter, mem_Ico, Dictionary.mem_dom_iff,
        Fin.valEmbedding_apply]
      constructor
      · rintro ⟨i, ⟨hlo, hhi⟩, rfl⟩
        obtain ⟨hU, hb, hq, -, -⟩ := hvalid_i b.val b.isLt i hlo hhi
        refine ⟨⟨g i, hU⟩, ⟨⟨csr.vArr i, ((hmap _).2 _).mpr ?_⟩, hb⟩, rfl⟩
        exact ⟨i, by rwa [hb], by rwa [hb], hq.symm, rfl⟩
      · rintro ⟨u, ⟨⟨v, hv⟩, hb⟩, rfl⟩
        obtain ⟨i, hlo, hhi, hqi, -⟩ := ((hmap u).2 v).mp hv
        rw [hb] at hlo hhi
        refine ⟨i, ⟨hlo, hhi⟩, ?_⟩
        simp only [g, hqi, ← hb, feistelReconstruct_feistelBucket]
    have hinj_g : Set.InjOn g (Ico (csr.fbStart b.val) (csr.fbStart (b.val + 1))) := by
      intro i hi j hj heq
      simp only [coe_Ico, Set.mem_Ico] at hi hj
      have hqi := (hvalid_i b.val b.isLt i hi.1 hi.2).2.2.1
      have hqj := (hvalid_i b.val b.isLt j hj.1 hj.2).2.2.1
      exact hinj b.val b.isLt i j hi.1 hi.2 hj.1 hj.2 (by rw [← hqi, ← hqj]; exact congrArg _ heq)
    rw [← card_map, ← himg, card_image_of_injOn hinj_g, Nat.card_Ico]
  refine ⟨hper_b, ?_⟩
  have htel : ∀ k ≤ numBucketsWhp n_max,
      ∑ b ∈ range k, (csr.fbStart (b + 1) - csr.fbStart b) = csr.fbStart k := by
    intro k hk
    induction k with
    | zero => simp [hfb0]
    | succ k ih =>
      rw [sum_range_succ, ih (by omega)]
      have hle := hadj k (by omega)
      omega
  rw [card_eq_sum_card_fiberwise (t := univ) (fun u _ => mem_univ
    (⟨feistelBucket (bWhp n_max) h1 u.val, feistelBucket_lt _ _ _⟩ : Fin (numBucketsWhp n_max)))]
  simp only [Fin.ext_iff, hper_b]
  rw [Fin.sum_univ_eq_sum_range (fun k => csr.fbStart (k + 1) - csr.fbStart k), htel _ le_rfl]

/-- The `none` clause of a `ValidCsrState` slot map follows from its `some` clause. -/
private theorem slotMap_of_some_iff {o : Option ℕ} {lo hi q : ℕ} {qa va : ℕ → ℕ}
    (h : ∀ v, o = some v ↔ ∃ i, lo ≤ i ∧ i < hi ∧ qa i = q ∧ va i = v) :
    (o = none ↔ ∀ i, lo ≤ i → i < hi → qa i ≠ q) ∧
      ∀ v, o = some v ↔ ∃ i, lo ≤ i ∧ i < hi ∧ qa i = q ∧ va i = v := by
  refine ⟨⟨fun ho i hlo hhi hq => ?_, fun hall => ?_⟩, h⟩
  · simpa [ho] using (h (va i)).mpr ⟨i, hlo, hhi, hq, rfl⟩
  · rcases ho : o with _ | v
    · rfl
    · obtain ⟨i, hlo, hhi, hq, -⟩ := (h v).mp ho
      exact absurd hq (hall i hlo hhi)

/-- CSR fallback lookup matches `dict u` for every seed `h1`. -/
theorem csrQuery_spec {U V n_max : ℕ} {h1 : ℕ → ℕ} {csr : CsrState} {dict : State U}
    (hv : ValidCsrState U V n_max h1 csr dict) (u : Fin U) :
    csrQuery csr (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val) =
      dict u := by
  obtain ⟨_, hadj, _, _, _, hmap⟩ := hv
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q := keyQuotient (bWhp n_max) u.val
  have hb_lt : b < numBucketsWhp n_max := feistelBucket_lt (bWhp n_max) h1 u.val
  have hle_fb : csr.fbStart b ≤ csr.fbStart (b + 1) := hadj b hb_lt
  have hsc := csrScanRange_to_props csr.qArr q hle_fb
  dsimp only [csrQuery]
  set f1 := csrScanRange csr.qArr (csr.fbStart b) q (csr.fbStart (b + 1) - csr.fbStart b)
  by_cases hf0 : f1 = 0
  · simp only [hf0, ↓reduceIte]
    have hall := hsc.1.mp hf0
    exact ((hmap u).1.mpr hall).symm
  · simp only [hf0, ↓reduceIte]
    obtain ⟨hlo, hhi, hqi⟩ := hsc.2 hf0
    symm
    exact ((hmap u).2 (csr.vArr (f1 - 1))).mpr ⟨f1 - 1, hlo, hhi, hqi, rfl⟩

/-- CSR fallback deletion preserves `ValidCsrState` and refines `Function.update dict u none` for
every seed `h1`. -/
theorem csrDelete_spec {U V n_max : ℕ} {h1 : ℕ → ℕ} {csr : CsrState} {dict : State U}
    (hv : ValidCsrState U V n_max h1 csr dict) (u : Fin U) :
    ValidCsrState U V n_max h1
      (csrDelete (numBucketsWhp n_max) csr
        (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val))
      (Function.update dict u none) := by
  obtain ⟨hfb0, hadj, hfbM_le, hvalid_i, hinj, hmap⟩ := hv
  set M := numBucketsWhp n_max
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q := keyQuotient (bWhp n_max) u.val
  have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
  have hmono := fbStart_mono_of_adj hadj
  have hle_fb : csr.fbStart b ≤ csr.fbStart (b + 1) := hadj b hb_lt
  have hsc := csrScanRange_to_props csr.qArr q hle_fb
  dsimp only [csrDelete]
  set f1 := csrScanRange csr.qArr (csr.fbStart b) q (csr.fbStart (b + 1) - csr.fbStart b)
  by_cases hfnz : f1 != 0
  · have hf_ne : f1 ≠ 0 := by simpa using hfnz
    simp only [hfnz, ↓reduceIte]
    obtain ⟨hlo_0, hhi_0, hq_0⟩ := hsc.2 hf_ne
    set i₀ := f1 - 1
    set N := csr.fbStart M
    have hi₀_lt_N : i₀ < N := hhi_0.trans_le (hmono (b + 1) M (by omega) le_rfl)
    set sh := csrShiftDown i₀ (N - 1 - i₀) (csr.qArr, csr.vArr)
    set fb' := csrAdjustStarts b true (M - b) csr.fbStart
    have hMb : b + 1 + (M - b) = M + 1 := by
      dsimp only [M, b] at hb_lt ⊢
      omega
    have hfb'_eq :
        ∀ x, fb' x = if b + 1 ≤ x ∧ x ≤ M then csr.fbStart x - 1 else csr.fbStart x := by
      intro x
      change csrAdjustStarts b true (M - b) csr.fbStart x = _
      rw [csrAdjustStarts_apply, hMb]
      simp only [↓reduceIte]
      split_ifs <;> omega
    have hsh_eq : ∀ x < N - 1,
        sh.1 x = csr.qArr (if x < i₀ then x else x + 1) ∧
        sh.2 x = csr.vArr (if x < i₀ then x else x + 1) := by
      intro x hx
      dsimp only [sh]
      obtain ⟨hqx, hvx⟩ := csrShiftDown_apply i₀ (N - 1 - i₀) csr.qArr csr.vArr x
      rw [hqx, hvx]
      split_ifs <;> omega
    have hge1_pos : ∀ x, b + 1 ≤ x → x ≤ M → 1 ≤ csr.fbStart x := by
      intro x hbx hxM
      have h1 : i₀ + 1 ≤ csr.fbStart (b + 1) := hhi_0
      have h2 : csr.fbStart (b + 1) ≤ csr.fbStart x := hmono (b + 1) x hbx hxM
      omega
    have horig_in : ∀ b' < M, ∀ i', fb' b' ≤ i' → i' < fb' (b' + 1) →
        let orig := if i' < i₀ then i' else i' + 1
        i' < N - 1 ∧ csr.fbStart b' ≤ orig ∧ orig < csr.fbStart (b' + 1) ∧ orig ≠ i₀ := by
      intro b' hb' i' hlo' hhi'
      dsimp only
      rw [hfb'_eq b'] at hlo'
      rw [hfb'_eq (b' + 1)] at hhi'
      have hb1_M : csr.fbStart (b' + 1) ≤ N := hmono (b' + 1) M (by omega) le_rfl
      rcases lt_trichotomy b' b with hlt_b | rfl | hgt_b
      · have hn1 : ¬(b + 1 ≤ b' ∧ b' ≤ M) := by omega
        have hn2 : ¬(b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M) := by omega
        simp only [hn1, hn2, ↓reduceIte] at hlo' hhi'
        have hle_b : csr.fbStart (b' + 1) ≤ csr.fbStart b := hmono (b' + 1) b (by omega) (by omega)
        have hi'_lt : i' < i₀ := by omega
        simp only [hi'_lt, ↓reduceIte]
        exact ⟨by omega, hlo', hhi', by omega⟩
      · have hn1 : ¬(b + 1 ≤ b ∧ b ≤ M) := by omega
        have hy2 : b + 1 ≤ b + 1 ∧ b + 1 ≤ M := by omega
        rw [ite_eq_right hn1] at hlo'
        rw [ite_eq_left hy2] at hhi'
        have := hge1_pos (b + 1) le_rfl (by omega)
        by_cases hi'_lt : i' < i₀
        · simp only [hi'_lt, ↓reduceIte]
          exact ⟨by omega, hlo', by omega, by omega⟩
        · simp only [hi'_lt, ↓reduceIte]
          exact ⟨by omega, by omega, by omega, by omega⟩
      · have hy1 : b + 1 ≤ b' ∧ b' ≤ M := by omega
        have hy2 : b + 1 ≤ b' + 1 ∧ b' + 1 ≤ M := by omega
        rw [ite_eq_left hy1] at hlo'
        rw [ite_eq_left hy2] at hhi'
        have := hge1_pos b' (by omega) (by omega)
        have := hge1_pos (b' + 1) (by omega) (by omega)
        have hge_fb : csr.fbStart (b + 1) ≤ csr.fbStart b' :=
          hmono (b + 1) b' (by omega) (by omega)
        have hn_lt : ¬(i' < i₀) := by omega
        simp only [hn_lt, ↓reduceIte]
        exact ⟨by omega, by omega, by omega, by omega⟩
    dsimp only [ValidCsrState]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun x => slotMap_of_some_iff fun v => ?_⟩
    · rw [hfb'_eq 0]; split_ifs <;> omega
    · intro b' hb'
      change b' < M at hb'
      rw [hfb'_eq b', hfb'_eq (b' + 1)]
      have hle' := hadj b' hb'
      rcases lt_trichotomy b' b with hlt_b | rfl | hgt_b
      · split_ifs <;> omega
      · have := hge1_pos (b + 1) le_rfl (by omega)
        split_ifs <;> omega
      · have := hge1_pos b' (by omega) (by omega)
        have := hge1_pos (b' + 1) (by omega) (by omega)
        split_ifs <;> omega
    · change fb' M ≤ n_max
      rw [hfb'_eq M]
      have := hge1_pos M (by omega) le_rfl
      split_ifs <;> omega
    · intro b' hb' i' hlo' hhi'
      change b' < M at hb'
      obtain ⟨hi'_N, hor_lo, hor_hi, _⟩ := horig_in b' hb' i' hlo' hhi'
      obtain ⟨hq_eq, hv_eq⟩ := hsh_eq i' hi'_N
      rw [hq_eq, hv_eq]
      exact hvalid_i b' hb' _ hor_lo hor_hi
    · intro b' hb' i' j' hloi hhii hloj hhij hq_eq
      change b' < M at hb'
      obtain ⟨hi'_N, hlo1, hhi1, _⟩ := horig_in b' hb' i' hloi hhii
      obtain ⟨hj'_N, hlo2, hhi2, _⟩ := horig_in b' hb' j' hloj hhij
      rw [(hsh_eq i' hi'_N).1, (hsh_eq j' hj'_N).1] at hq_eq
      have horig_eq := hinj b' hb' _ _ hlo1 hhi1 hlo2 hhi2 hq_eq
      by_cases h1 : i' < i₀ <;> by_cases h2 : j' < i₀ <;>
        simp only [h1, h2, ↓reduceIte] at horig_eq <;> omega
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, reduceCtorEq, false_iff, not_exists, not_and]
        intro i' hlo' hhi' hq_eq _
        obtain ⟨hi'_N, hor_lo, hor_hi, hor_ne⟩ := horig_in b hb_lt i' hlo' hhi'
        rw [(hsh_eq i' hi'_N).1] at hq_eq
        exact hor_ne (hinj b hb_lt _ i₀ hor_lo hor_hi hlo_0 hhi_0 (hq_eq.trans hq_0.symm))
      · rw [Function.update_of_ne hxu, (hmap x).2 v]
        set bx := feistelBucket (bWhp n_max) h1 x.val
        have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
        constructor
        · rintro ⟨i, hi_lo, hi_hi, hq_i, hv_i⟩
          have hi_ne_i₀ : i ≠ i₀ := by
            intro h; rw [h] at hi_lo hi_hi hq_i
            by_cases hbx_eq : bx = b
            · exact hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq hbx_eq
                (hq_i.symm.trans hq_0)))
            · rcases lt_or_gt_of_ne hbx_eq with hlt | hgt
              · have := hmono (bx + 1) b (by omega) (by omega); omega
              · have := hmono (b + 1) bx (by omega) (by omega); omega
          let i' := if i < i₀ then i else i - 1
          have hi'_in : fb' bx ≤ i' ∧ i' < fb' (bx + 1) ∧
              (if i' < i₀ then i' else i' + 1) = i := by
            dsimp only [i']
            rw [hfb'_eq bx, hfb'_eq (bx + 1)]
            rcases lt_trichotomy bx b with hlt | heq | hgt
            · have hle_b := hmono (bx + 1) b (by omega) (by omega)
              split_ifs <;> omega
            · rw [heq] at hi_lo hi_hi ⊢
              have := hge1_pos (b + 1) le_rfl (by omega)
              split_ifs <;> omega
            · have := hge1_pos bx (by omega) (by omega)
              have := hge1_pos (bx + 1) (by omega) (by omega)
              have hge_b := hmono (b + 1) bx (by omega) (by omega)
              split_ifs <;> omega
          obtain ⟨hi'_N, _, _, _⟩ := horig_in bx hbx_lt i' hi'_in.1 hi'_in.2.1
          refine ⟨i', hi'_in.1, hi'_in.2.1, ?_, ?_⟩
          · rw [(hsh_eq i' hi'_N).1, hi'_in.2.2]; exact hq_i
          · rw [(hsh_eq i' hi'_N).2, hi'_in.2.2]; exact hv_i
        · rintro ⟨i', hlo', hhi', hq', hv'⟩
          obtain ⟨hi'_N, hor_lo, hor_hi, _⟩ := horig_in bx hbx_lt i' hlo' hhi'
          rw [(hsh_eq i' hi'_N).1] at hq'
          rw [(hsh_eq i' hi'_N).2] at hv'
          exact ⟨_, hor_lo, hor_hi, hq', hv'⟩
  · have hf0 : f1 = 0 := by simpa using hfnz
    simp only [hfnz, Bool.false_eq_true, ↓reduceIte]
    have hall := hsc.1.mp hf0
    have hnone_u : dict u = none := (hmap u).1.mpr hall
    rw [show Function.update dict u none = dict from Function.update_eq_self_iff.mpr hnone_u.symm]
    exact ⟨hfb0, hadj, hfbM_le, hvalid_i, hinj, hmap⟩

theorem keyQuotient_lt_two_pow_quotBitsWhp {U n_max : ℕ} (hnU : n_max ≤ U) (u : Fin U) :
    keyQuotient (bWhp n_max) u.val < 2 ^ quotBitsWhp U n_max := by
  unfold keyQuotient
  refine Nat.div_lt_of_lt_mul ?_
  rw [mul_comm, ← Nat.pow_add, quotBitsWhp_add_bWhp hnU]
  rcases le_or_gt U 1 with hU1 | hU1
  · have hu0 : u.val = 0 := by omega
    rw [hu0]
    exact Nat.two_pow_pos _
  · exact u.isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two U)

private theorem csr_insert_slot_iff {M b b' : ℕ} {f : ℕ → ℕ}
    (hadj : ∀ j < M, f j ≤ f (j + 1)) (hb : b < M) (hb' : b' < M) (i' : ℕ) :
    let hi := f (b + 1)
    let orig := if i' < hi then i' else i' - 1
    let shifted := fun j => if b + 1 ≤ j ∧ j ≤ M then f j + 1 else f j
    (shifted b' ≤ i' ∧ i' < shifted (b' + 1)) ↔
      (b' = b ∧ i' = hi) ∨ (i' ≠ hi ∧ f b' ≤ orig ∧ orig < f (b' + 1)) := by
  dsimp only
  have hmono := fbStart_mono_of_adj hadj
  rcases lt_trichotomy b' b with hlt | rfl | hgt
  · have hle := hmono (b' + 1) (b + 1) (Nat.succ_le_succ hlt.le) (Nat.succ_le_of_lt hb)
    rw [ite_eq_right (fun h => hlt.not_ge (Nat.le_of_succ_le h.1)),
      ite_eq_right (fun h => hlt.not_ge (Nat.le_of_succ_le_succ h.1))]
    simp only [hlt.ne, false_and, false_or]
    clear hadj hmono
    split_ifs <;> lia
  · have hle := hadj b' hb'
    rw [ite_eq_right (fun h => (Nat.not_succ_le_self b') h.1),
      ite_eq_left ⟨le_rfl, Nat.succ_le_of_lt hb'⟩]
    simp only [true_and]
    clear hadj hmono
    split_ifs <;> lia
  · have hle := hmono (b + 1) b' hgt hb'.le
    rw [ite_eq_left ⟨hgt, hb'.le⟩,
      ite_eq_left ⟨Nat.succ_le_succ hgt.le, Nat.succ_le_of_lt hb'⟩]
    simp only [hgt.ne', false_and, false_or]
    clear hadj hmono
    split_ifs <;> lia

/-- CSR fallback insertion preserves `ValidCsrState` and refines
`Function.update dict u (some v)` whenever `n_max ≤ U` and
`Dynamic.valid V n_max dict (.insert u v)`. -/
theorem csrInsert_spec {U V n_max : ℕ} (hnU : n_max ≤ U) {h1 : ℕ → ℕ} {csr : CsrState}
    {dict : State U} (hv : ValidCsrState U V n_max h1 csr dict) {u : Fin U} {v : ℕ}
    (hvalid : Dynamic.valid V n_max dict (.insert u v)) :
    ValidCsrState U V n_max h1
      (csrInsert (numBucketsWhp n_max) csr
        (feistelBucket (bWhp n_max) h1 u.val) (keyQuotient (bWhp n_max) u.val) v)
      (Function.update dict u (some v)) := by
  have hdom_card := hv.bucket_and_dom_card.2
  obtain ⟨hcap, hv_lt⟩ := hvalid
  obtain ⟨hfb0, hadj, hfbM_le, hvalid_i, hinj, hmap⟩ := hv
  set M := numBucketsWhp n_max
  set b := feistelBucket (bWhp n_max) h1 u.val
  set q := keyQuotient (bWhp n_max) u.val
  have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
  have hq_lt : q < 2 ^ quotBitsWhp U n_max := keyQuotient_lt_two_pow_quotBitsWhp hnU u
  have hmono := fbStart_mono_of_adj hadj
  have hle_fb : csr.fbStart b ≤ csr.fbStart (b + 1) := hadj b hb_lt
  have hsc := csrScanRange_to_props csr.qArr q hle_fb
  dsimp only [csrInsert]
  set f1 := csrScanRange csr.qArr (csr.fbStart b) q (csr.fbStart (b + 1) - csr.fbStart b)
  by_cases hfnz : f1 != 0
  · have hf_ne : f1 ≠ 0 := by simpa using hfnz
    simp only [hfnz, ↓reduceIte]
    obtain ⟨hlo_0, hhi_0, hq_0⟩ := hsc.2 hf_ne
    set i₀ := f1 - 1
    dsimp only [ValidCsrState]
    refine ⟨hfb0, hadj, hfbM_le, ?_, hinj, fun x => slotMap_of_some_iff fun w => ?_⟩
    · intro b' hb' i hlo hhi
      obtain ⟨hp1, hp2, hp3, hp4, hp5⟩ := hvalid_i b' hb' i hlo hhi
      exact ⟨hp1, hp2, hp3, hp4, by rw [Function.update_apply]; split_ifs <;> assumption⟩
    · set bx := feistelBucket (bWhp n_max) h1 x.val
      have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
      by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨i₀, hlo_0, hhi_0, hq_0, by simp⟩
        · rintro ⟨i, hlo, hhi, hqi, hwi⟩
          have hi_eq : i = i₀ := hinj b hb_lt i i₀ hlo hhi hlo_0 hhi_0 (hqi.trans hq_0.symm)
          subst hi_eq
          simpa using hwi
      · rw [Function.update_of_ne hxu, (hmap x).2 w]
        -- A slot of `x ≠ u` never holds the overwritten index `i₀`, which belongs to `u`.
        have hni : ∀ i, csr.fbStart bx ≤ i → i < csr.fbStart (bx + 1) →
            csr.qArr i = keyQuotient (bWhp n_max) x.val → i ≠ i₀ := by
          rintro i hlo hhi hqi rfl
          by_cases hbx : bx = b
          · exact hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq hbx
              (hqi.symm.trans hq_0)))
          · rcases lt_or_gt_of_ne hbx with hlt | hgt
            · have := hmono (bx + 1) b (by omega) (by omega); omega
            · have := hmono (b + 1) bx (by omega) (by omega); omega
        exact exists_congr fun i => and_congr_right fun hlo => and_congr_right fun hhi =>
          and_congr_right fun hqi => by simp only [Function.update_of_ne (hni i hlo hhi hqi)]
  · have hf0 : f1 = 0 := by simpa using hfnz
    simp only [hfnz, Bool.false_eq_true, ↓reduceIte]
    have hall := hsc.1.mp hf0
    have hnone_u : dict u = none := (hmap u).1.mpr hall
    set hi := csr.fbStart (b + 1)
    set N := csr.fbStart M
    have hhi_le_N : hi ≤ N := hmono (b + 1) M (by omega) le_rfl
    have hN_lt : N < n_max := by
      rcases hcap with hlt | hsome
      · rwa [hdom_card] at hlt
      · rw [hnone_u] at hsome; simp at hsome
    set sh := csrShiftUp N (N - hi) (csr.qArr, csr.vArr)
    set q' := Function.update sh.1 hi q
    set v' := Function.update sh.2 hi v
    set fb' := csrAdjustStarts b false (M - b) csr.fbStart
    have hMb : b + 1 + (M - b) = M + 1 := by
      dsimp only [M, b] at hb_lt ⊢
      omega
    have hfb'_eq :
        ∀ x, fb' x = if b + 1 ≤ x ∧ x ≤ M then csr.fbStart x + 1 else csr.fbStart x := by
      intro x
      change csrAdjustStarts b false (M - b) csr.fbStart x = _
      rw [csrAdjustStarts_apply, hMb]
      simp only [Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> omega
    have hqv'_eq : ∀ x ≤ N,
        (x < hi → q' x = csr.qArr x ∧ v' x = csr.vArr x) ∧
        (x = hi → q' x = q ∧ v' x = v) ∧
        (hi < x → q' x = csr.qArr (x - 1) ∧ v' x = csr.vArr (x - 1)) := by
      intro x hxN
      dsimp only [q', v', sh]
      obtain ⟨hqx, hvx⟩ := csrShiftUp_apply N (N - hi) (by omega) csr.qArr csr.vArr x
      refine ⟨fun hlt => ?_, fun heq => ?_, fun hgt => ?_⟩
      · have hne : x ≠ hi := by omega
        have hn : ¬(N - (N - hi) < x ∧ x ≤ N) := by omega
        simp [hne, hqx, hvx, hn]
      · subst heq; simp
      · have hne : x ≠ hi := by omega
        have hy : N - (N - hi) < x ∧ x ≤ N := by omega
        simp [hne, hqx, hvx, hy]
    -- Every occupied slot except the new one comes from this index in the old arrays.
    let orig (i' : ℕ) := if i' < hi then i' else i' - 1
    have horig_inj {i' j' : ℕ} (hi' : i' ≠ hi) (hj' : j' ≠ hi)
        (heq : orig i' = orig j') : i' = j' := by
      dsimp only [orig] at heq
      clear * - hi' hj' heq
      split_ifs at heq <;> lia
    have hslot (b' : ℕ) (hb' : b' < M) (i' : ℕ) :
        (fb' b' ≤ i' ∧ i' < fb' (b' + 1)) ↔
        (b' = b ∧ i' = hi) ∨
          (i' ≠ hi ∧ csr.fbStart b' ≤ orig i' ∧ orig i' < csr.fbStart (b' + 1)) := by
      rw [hfb'_eq b', hfb'_eq (b' + 1)]
      exact csr_insert_slot_iff hadj hb_lt hb' i'
    have hslot_le {b' i' : ℕ} (hb' : b' < M) (hhi' : i' < fb' (b' + 1)) : i' ≤ N := by
      have hle := hmono (b' + 1) M (Nat.succ_le_of_lt hb') le_rfl
      rw [hfb'_eq] at hhi'
      split at hhi'
      · exact (Nat.le_of_lt_succ hhi').trans hle
      · exact (hhi'.trans_le hle).le
    have hqv_orig {i' : ℕ} (hle : i' ≤ N) (hne : i' ≠ hi) :
        q' i' = csr.qArr (orig i') ∧ v' i' = csr.vArr (orig i') := by
      dsimp only [orig]
      split
      · exact (hqv'_eq i' hle).1 ‹i' < hi›
      · exact (hqv'_eq i' hle).2.2 (lt_of_le_of_ne (Nat.le_of_not_gt ‹¬i' < hi›) hne.symm)
    have hnew_slot := (hslot b hb_lt hi).mpr (Or.inl ⟨rfl, rfl⟩)
    have hqv_new := (hqv'_eq hi hhi_le_N).2.1 rfl
    have hrec_u : feistelReconstruct (bWhp n_max) h1 b q = u.val :=
      feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
    dsimp only [ValidCsrState]
    refine ⟨?_, ?_, ?_, ?_, ?_, fun x => slotMap_of_some_iff fun w => ?_⟩
    · rw [hfb'_eq 0, ite_eq_right (fun h => Nat.not_succ_le_zero b h.1)]
      exact hfb0
    · intro b' hb'
      change b' < M at hb'
      rw [hfb'_eq b', hfb'_eq (b' + 1)]
      by_cases hle : b + 1 ≤ b'
      · rw [ite_eq_left ⟨hle, hb'.le⟩,
          ite_eq_left ⟨hle.trans (Nat.le_succ _), Nat.succ_le_of_lt hb'⟩]
        exact Nat.succ_le_succ (hadj b' hb')
      · rw [ite_eq_right (fun h => hle h.1)]
        split
        · exact Nat.le_succ_of_le (hadj b' hb')
        · exact hadj b' hb'
    · change fb' M ≤ n_max
      rw [hfb'_eq M, ite_eq_left ⟨Nat.succ_le_of_lt hb_lt, le_rfl⟩]
      exact hN_lt
    · intro b' hb' i' hlo' hhi'
      rcases (hslot b' hb' i').mp ⟨hlo', hhi'⟩ with ⟨rfl, rfl⟩ | ⟨hne, hlo, hhi⟩
      · rw [hqv_new.1, hqv_new.2, hrec_u]
        exact ⟨u.isLt, rfl, rfl, hq_lt, hv_lt⟩
      · obtain ⟨hqe, hve⟩ := hqv_orig (hslot_le hb' hhi') hne
        rw [hqe, hve]
        exact hvalid_i b' hb' _ hlo hhi
    · intro b' hb' i' j' hloi hhii hloj hhij heq
      rcases (hslot b' hb' i').mp ⟨hloi, hhii⟩ with ⟨rfl, rfl⟩ | ⟨hni, hloi', hhii'⟩
      · rcases (hslot b hb' j').mp ⟨hloj, hhij⟩ with ⟨_, rfl⟩ | ⟨hnj, hloj', hhij'⟩
        · rfl
        · rw [hqv_new.1, (hqv_orig (hslot_le hb' hhij) hnj).1] at heq
          exact False.elim (hall _ hloj' hhij' heq.symm)
      · have hqi := (hqv_orig (hslot_le hb' hhii) hni).1
        rcases (hslot b' hb' j').mp ⟨hloj, hhij⟩ with ⟨rfl, rfl⟩ | ⟨hnj, hloj', hhij'⟩
        · rw [hqi, hqv_new.1] at heq
          exact False.elim (hall _ hloi' hhii' heq)
        · rw [hqi, (hqv_orig (hslot_le hb' hhij) hnj).1] at heq
          exact horig_inj hni hnj (hinj b' hb' _ _ hloi' hhii' hloj' hhij' heq)
    · by_cases hxu : x = u
      · subst hxu
        simp only [Function.update_self, Option.some.injEq]
        constructor
        · rintro rfl
          exact ⟨hi, hnew_slot.1, hnew_slot.2, hqv_new.1, hqv_new.2⟩
        · rintro ⟨i', hlo', hhi', hq', hv'⟩
          rcases (hslot b hb_lt i').mp ⟨hlo', hhi'⟩ with ⟨_, rfl⟩ | ⟨hne, hlo, hhi⟩
          · exact hqv_new.2.symm.trans hv'
          · rw [(hqv_orig (hslot_le hb_lt hhi') hne).1] at hq'
            exact False.elim (hall _ hlo hhi hq')
      · rw [Function.update_of_ne hxu, (hmap x).2 w]
        let bx := feistelBucket (bWhp n_max) h1 x.val
        have hbx_lt : bx < M := feistelBucket_lt (bWhp n_max) h1 x.val
        constructor
        · rintro ⟨i, hlo, hhi, hqi, hwi⟩
          obtain ⟨i', hne, hi'_orig⟩ : ∃ i', i' ≠ hi ∧ orig i' = i := by
            by_cases hlt : i < hi
            · exact ⟨i, Nat.ne_of_lt hlt, ite_eq_left hlt⟩
            · have hs : hi < i + 1 := Nat.lt_succ_of_le (Nat.le_of_not_gt hlt)
              exact ⟨i + 1, hs.ne', ite_eq_right (Nat.not_lt_of_ge hs.le)⟩
          have hslot' := (hslot bx hbx_lt i').mpr (Or.inr ⟨hne, hi'_orig ▸ hlo, hi'_orig ▸ hhi⟩)
          obtain ⟨hqe, hve⟩ := hqv_orig (hslot_le hbx_lt hslot'.2) hne
          rw [hi'_orig] at hqe hve
          exact ⟨i', hslot'.1, hslot'.2, hqe.trans hqi, hve.trans hwi⟩
        · rintro ⟨i', hlo', hhi', hqi', hwi'⟩
          rcases (hslot bx hbx_lt i').mp ⟨hlo', hhi'⟩ with ⟨hbx, rfl⟩ | ⟨hne, hlo, hhi⟩
          · exact False.elim (hxu (Fin.ext (eq_of_feistelBucket_eq_of_keyQuotient_eq hbx
              (hqi'.symm.trans hqv_new.1))))
          · obtain ⟨hqe, hve⟩ := hqv_orig (hslot_le hbx_lt hhi') hne
            exact ⟨_, hlo, hhi, hqe.symm.trans hqi', hve.symm.trans hwi'⟩

/-! ### Overflow-free `GoodSeedOnState` decision & salt-discovery procedure on `CsrState` -/

/-- Overflow-free single-bucket load-balance test (`M * X_b ≤ N + M * δ ∧ N ≤ M * X_b + M * δ`)
using only division and remainder `< max (N + 1) M`. -/
@[expose] def checkBalancedBucketNat (M δ N X_b : ℕ) : Bool :=
  let qN := N / M
  let rN := N % M
  let lb := if rN == 0 then qN - δ else (qN + 1) - δ
  decide (X_b ≤ qN + δ) && decide (lb ≤ X_b)

private theorem checkBalancedBucketNat_eq_true_iff {M δ N X_b : ℕ} (hM : 0 < M) :
    checkBalancedBucketNat M δ N X_b = true ↔
      (M * X_b ≤ N + M * δ ∧ N ≤ M * X_b + M * δ) := by
  unfold checkBalancedBucketNat
  have hdiv := Nat.div_add_mod N M
  have hmod_lt : N % M < M := Nat.mod_lt N hM
  -- Scaling the quotient comparisons by `M` reduces everything to `omega`.
  have hsc : ∀ a b, a ≤ b ↔ M * a ≤ M * b := fun _ _ => (Nat.mul_le_mul_left_iff hM).symm
  have := hsc X_b (N / M + δ); have := hsc (N / M + δ + 1) X_b
  have := hsc (N / M + 1) (X_b + δ); have := hsc (X_b + δ) (N / M); have := hsc (N / M) (X_b + δ)
  simp only [Nat.mul_add, Nat.mul_one] at *
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  split_ifs <;> omega

/-- Scan `b = 0 .. k - 1` to find the bucket `b` satisfying
`fbStart b ≤ i ∧ i < fbStart (b + 1)`. -/
@[expose] def csrBucketOfIdx (fbStart : ℕ → ℕ) (i : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 =>
    if fbStart k ≤ i && i < fbStart (k + 1) then k
    else csrBucketOfIdx fbStart i k

theorem csrBucketOfIdx_spec {M : ℕ} {fbStart : ℕ → ℕ} (h0 : fbStart 0 = 0)
    (_hadj : ∀ b < M, fbStart b ≤ fbStart (b + 1)) :
    ∀ k ≤ M, ∀ i < fbStart k,
      let b := csrBucketOfIdx fbStart i k
      b < k ∧ fbStart b ≤ i ∧ i < fbStart (b + 1) := by
  intro k hk
  induction k with
  | zero => simp [h0]
  | succ k ih =>
    intro i hi
    simp only [csrBucketOfIdx, Bool.and_eq_true, decide_eq_true_eq]
    split_ifs with hcond
    · exact ⟨by omega, hcond⟩
    · obtain ⟨h1, h2, h3⟩ := ih (by omega) i (by omega)
      exact ⟨by omega, h2, h3⟩

/-- `csrBucketOfIdx` depends only on `fbStart 0 .. fbStart k`. -/
theorem csrBucketOfIdx_congr {f₁ f₂ : ℕ → ℕ} {i k : ℕ}
    (h : ∀ b ≤ k, f₁ b = f₂ b) :
    csrBucketOfIdx f₁ i k = csrBucketOfIdx f₂ i k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    dsimp only [csrBucketOfIdx]
    rw [h k (Nat.le_succ k), h (k + 1) le_rfl, ih (fun b hb => h b (Nat.le_succ_of_le hb))]

/-- Check all buckets `0 .. k - 1` for
`checkBalancedBucketNat M δ N (fbStart (b + 1) - fbStart b)`. -/
@[expose] def checkAllBalancedCsr (M δ N : ℕ) (fbStart : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 =>
    checkAllBalancedCsr M δ N fbStart k &&
      checkBalancedBucketNat M δ N (fbStart (k + 1) - fbStart k)

/-- Check `rKeyOf j != rKeyOf i` across `j = 0 .. k - 1`. -/
@[expose] def checkNoEqBefore (f : ℕ → ℕ) (target : ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkNoEqBefore f target k && (f k != target)

/-- Check pairwise distinctness of `f` on `0 .. k - 1`. -/
@[expose] def checkPairwiseDistinctOn (f : ℕ → ℕ) : ℕ → Bool
  | 0 => true
  | k + 1 => checkPairwiseDistinctOn f k && checkNoEqBefore f (f k) k

private theorem checkNoEqBefore_iff (f : ℕ → ℕ) (target k : ℕ) :
    checkNoEqBefore f target k = true ↔ ∀ j < k, f j ≠ target := by
  induction k with
  | zero => simp [checkNoEqBefore]
  | succ k ih =>
    simp only [checkNoEqBefore, Bool.and_eq_true, ih, bne_iff_ne, Nat.forall_lt_succ_right]

private theorem checkPairwiseDistinctOn_iff (f : ℕ → ℕ) (k : ℕ) :
    checkPairwiseDistinctOn f k = true ↔ ∀ i < k, ∀ j < k, f i = f j → i = j := by
  induction k with
  | zero => simp [checkPairwiseDistinctOn]
  | succ k ih =>
    simp only [checkPairwiseDistinctOn, Bool.and_eq_true, ih, checkNoEqBefore_iff,
      Nat.forall_lt_succ_right]
    grind

/-- Search `s = 0 .. k - 1` for the first salt `s` making `fpAt s` pairwise distinct on
`lo .. lo + len - 1`, returning `0` if none exists or `s + 1` if found. -/
@[expose] def findSaltInRange (fpAt : ℕ → ℕ → ℕ) (lo len : ℕ) : ℕ → ℕ
  | 0 => 0
  | s + 1 =>
    let prev := findSaltInRange fpAt lo len s
    if prev != 0 then prev
    else if checkPairwiseDistinctOn (fun t => fpAt s (lo + t)) len then s + 1
    else 0

private theorem findSaltInRange_props (fpAt : ℕ → ℕ → ℕ) (lo len sMax : ℕ) :
    let res := findSaltInRange fpAt lo len sMax
    (res = 0 ↔ ∀ s < sMax, ¬(∀ i < len, ∀ j < len, fpAt s (lo + i) = fpAt s (lo + j) → i = j)) ∧
    (res ≠ 0 → res - 1 < sMax ∧
      ∀ i < len, ∀ j < len, fpAt (res - 1) (lo + i) = fpAt (res - 1) (lo + j) → i = j) := by
  induction sMax with
  | zero => simp [findSaltInRange]
  | succ s ih =>
    simp only [findSaltInRange, Nat.forall_lt_succ_right, bne_iff_ne, ne_eq,
      checkPairwiseDistinctOn_iff] at ih ⊢
    split_ifs with hp hc
    · exact ⟨iff_of_false (by simp) fun h => h.2 hc, fun _ => ⟨by omega, by simpa using hc⟩⟩
    · exact ⟨iff_of_true rfl ⟨ih.1.mp hp, hc⟩, fun h => absurd rfl h⟩
    · obtain ⟨hlt, hinj⟩ := ih.2 hp
      exact ⟨iff_of_false hp fun h => h.1 _ hlt hinj, fun _ => ⟨by omega, hinj⟩⟩

/-- Pure overflow-free `GoodSeedOnState` check and per-bucket collision-free salt finder on
`CsrState`. Returns `(ok, saltOfBucket)`. -/
@[expose] def checkGoodSeedOnState (c U n_max : ℕ) (θ : SeedWhp c U n_max) (csr : CsrState) :
    Bool × (ℕ → ℕ) :=
  let M := numBucketsWhp n_max
  let N := csr.fbStart M
  let h1 := bktHash c U n_max θ.1
  let keyValAt : ℕ → ℕ := fun i =>
    let b := csrBucketOfIdx csr.fbStart i M
    feistelReconstruct (bWhp n_max) h1 b (csr.qArr i)
  let rKeyAt : ℕ → ℕ := fun i =>
    if h : keyValAt i < U then fpReducedKey c U n_max θ.2 ⟨keyValAt i, h⟩ else 0
  let fpAt : ℕ → ℕ → ℕ := fun s i =>
    if hs : s < sMaxWhp c n_max then
      if hu : keyValAt i < U then fpHash c U n_max θ.2 ⟨s, hs⟩ ⟨keyValAt i, hu⟩ else 0
    else 0
  let okBal := checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M
  let okInj := checkPairwiseDistinctOn rKeyAt N
  let salt1Of : ℕ → ℕ := fun b =>
    findSaltInRange fpAt (csr.fbStart b) (csr.fbStart (b + 1) - csr.fbStart b) (sMaxWhp c n_max)
  let allSaltsFound : ℕ → Bool := Nat.rec true fun b prev => prev && (salt1Of b != 0)
  (okBal && okInj && allSaltsFound M, fun b => salt1Of b - 1)

private theorem checkAllBalancedCsr_iff (M δ N : ℕ) (fbStart : ℕ → ℕ) (k : ℕ) :
    checkAllBalancedCsr M δ N fbStart k = true ↔
      ∀ b < k, checkBalancedBucketNat M δ N (fbStart (b + 1) - fbStart b) = true := by
  induction k with
  | zero => simp [checkAllBalancedCsr]
  | succ k ih => simp only [checkAllBalancedCsr, Bool.and_eq_true, ih, Nat.forall_lt_succ_right]

theorem csrBucketOfIdx_eq_of_in_range {M : ℕ} {fbStart : ℕ → ℕ}
    (h0 : fbStart 0 = 0) (hadj : ∀ b < M, fbStart b ≤ fbStart (b + 1))
    {b i : ℕ} (hb : b < M) (hlo : fbStart b ≤ i) (hhi : i < fbStart (b + 1)) :
    csrBucketOfIdx fbStart i M = b := by
  have hmono := fbStart_mono_of_adj hadj
  have hi_M : i < fbStart M := hhi.trans_le (hmono (b + 1) M (by omega) le_rfl)
  obtain ⟨hb'_lt, hlo', hhi'⟩ := csrBucketOfIdx_spec h0 hadj M le_rfl i hi_M
  set b' := csrBucketOfIdx fbStart i M
  rcases lt_trichotomy b' b with hlt | heq | hgt
  · have := hmono (b' + 1) b (by omega) (by omega); omega
  · exact heq
  · have := hmono (b + 1) b' (by omega) (by omega); omega

/-- **Exact soundness and completeness of `checkGoodSeedOnState`**:
for any `ValidCsrState`, `(checkGoodSeedOnState c U n_max θ csr).1 = true ↔
GoodSeedOnState c U n_max θ dict`, and when `true`, `(checkGoodSeedOnState ...).2 b` is a valid
collision-free salt `< sMaxWhp c n_max` for every bucket `b`. -/
theorem checkGoodSeedOnState_spec {c U V n_max : ℕ} {θ : SeedWhp c U n_max}
    {csr : CsrState} {dict : State U}
    (hv : ValidCsrState U V n_max (bktHash c U n_max θ.1) csr dict) :
    let (ok, salts) := checkGoodSeedOnState c U n_max θ csr
    (ok = true ↔ GoodSeedOnState c U n_max θ dict) ∧
    (ok = true → ∀ b : Fin (numBucketsWhp n_max),
      ∃ hs : salts b.val < sMaxWhp c n_max,
        Set.InjOn (fpHash c U n_max θ.2 ⟨salts b.val, hs⟩)
          ((Dictionary.dom dict).filter (fun u =>
            feistelBucket (bWhp n_max) (bktHash c U n_max θ.1) u.val = b.val) : Set (Fin U))) := by
  obtain ⟨hcard_b, hcard_dom⟩ := hv.bucket_and_dom_card
  obtain ⟨hfb0, hadj, _, hvalid_i, hinj_q, hmap⟩ := hv
  set M := numBucketsWhp n_max
  set N := csr.fbStart M
  set h1 := bktHash c U n_max θ.1
  have hM_pos : 0 < M := by dsimp only [M, numBucketsWhp]; positivity
  have hmono := fbStart_mono_of_adj hadj
  let keyValAt : ℕ → ℕ := fun i =>
    feistelReconstruct (bWhp n_max) h1 (csrBucketOfIdx csr.fbStart i M) (csr.qArr i)
  let rKeyAt : ℕ → ℕ := fun i =>
    if h : keyValAt i < U then fpReducedKey c U n_max θ.2 ⟨keyValAt i, h⟩ else 0
  let fpAt : ℕ → ℕ → ℕ := fun s i =>
    if hs : s < sMaxWhp c n_max then
      if hu : keyValAt i < U then fpHash c U n_max θ.2 ⟨s, hs⟩ ⟨keyValAt i, hu⟩ else 0
    else 0
  let salt1Of : ℕ → ℕ := fun b =>
    findSaltInRange fpAt (csr.fbStart b) (csr.fbStart (b + 1) - csr.fbStart b) (sMaxWhp c n_max)
  let allSaltsFound : ℕ → Bool := Nat.rec true fun b prev => prev && (salt1Of b != 0)
  have hallSalts_iff : ∀ k, allSaltsFound k = true ↔ ∀ b < k, salt1Of b ≠ 0 := by
    intro k
    induction k with
    | zero => simp [allSaltsFound]
    | succ k ih =>
      change (allSaltsFound k && (salt1Of k != 0)) = true ↔ _
      simp only [Bool.and_eq_true, ih, bne_iff_ne]
      exact ⟨fun ⟨h1', h2'⟩ b hb => by
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hlt | rfl
        · exact h1' b hlt
        · exact h2',
        fun hall => ⟨fun b hb => hall b (Nat.lt_succ_of_lt hb), hall k (Nat.lt_succ_self k)⟩⟩
  have hidx_props : ∀ i < N,
      let b := csrBucketOfIdx csr.fbStart i M
      b < M ∧ csr.fbStart b ≤ i ∧ i < csr.fbStart (b + 1) ∧
      ∃ hu : keyValAt i < U,
        feistelBucket (bWhp n_max) h1 (keyValAt i) = b ∧
        keyQuotient (bWhp n_max) (keyValAt i) = csr.qArr i ∧
        (⟨keyValAt i, hu⟩ : Fin U) ∈ Dictionary.dom dict := by
    intro i hi
    obtain ⟨hb_lt, hlo, hhi⟩ := csrBucketOfIdx_spec hfb0 hadj M le_rfl i hi
    set b := csrBucketOfIdx csr.fbStart i M
    have hp := hvalid_i b hb_lt i hlo hhi
    refine ⟨hb_lt, hlo, hhi, hp.1, hp.2.1, hp.2.2.1, ?_⟩
    rw [Dictionary.mem_dom_iff]
    have hsome : dict ⟨keyValAt i, hp.1⟩ = some (csr.vArr i) := by
      apply ((hmap ⟨keyValAt i, hp.1⟩).2 (csr.vArr i)).mpr
      dsimp only
      rw [hp.2.1, hp.2.2.1]
      exact ⟨i, hlo, hhi, rfl, rfl⟩
    exact ⟨csr.vArr i, hsome⟩
  have hdom_to_idx : ∀ u ∈ Dictionary.dom dict,
      ∃ i < N,
        let b := feistelBucket (bWhp n_max) h1 u.val
        csr.fbStart b ≤ i ∧ i < csr.fbStart (b + 1) ∧
        csrBucketOfIdx csr.fbStart i M = b ∧ keyValAt i = u.val := by
    intro u hu
    rw [Dictionary.mem_dom_iff] at hu
    obtain ⟨v, hv_u⟩ := hu
    obtain ⟨i, hlo, hhi, hqi, _⟩ := ((hmap u).2 v).mp hv_u
    set b := feistelBucket (bWhp n_max) h1 u.val
    have hb_lt : b < M := feistelBucket_lt (bWhp n_max) h1 u.val
    have hi_N : i < N := hhi.trans_le (hmono (b + 1) M (by omega) le_rfl)
    have hb_eq := csrBucketOfIdx_eq_of_in_range hfb0 hadj hb_lt hlo hhi
    refine ⟨i, hi_N, hlo, hhi, hb_eq, ?_⟩
    dsimp only [keyValAt]
    rw [hb_eq, hqi]
    exact feistelReconstruct_feistelBucket (bWhp n_max) h1 u.val
  have hbal_iff : checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M = true ↔
      BalancedBuckets U n_max h1 (Dictionary.dom dict) := by
    rw [checkAllBalancedCsr_iff]
    unfold BalancedBuckets BalancedBucketAt
    constructor
    · intro hall b
      have hb := (checkBalancedBucketNat_eq_true_iff hM_pos).mp (hall b.val b.isLt)
      dsimp only
      rwa [hcard_b b, hcard_dom]
    · intro hbal b hb_lt
      have hb := hbal ⟨b, hb_lt⟩
      dsimp only at hb
      rw [hcard_b ⟨b, hb_lt⟩, hcard_dom] at hb
      exact (checkBalancedBucketNat_eq_true_iff hM_pos).mpr hb
  have hinj_iff : checkPairwiseDistinctOn rKeyAt N = true ↔
      Set.InjOn (fpReducedKey c U n_max θ.2) (Dictionary.dom dict : Set (Fin U)) := by
    rw [checkPairwiseDistinctOn_iff]
    constructor
    · intro hp u₁ hu₁ u₂ hu₂ hr_eq
      rw [mem_coe] at hu₁ hu₂
      obtain ⟨i₁, hi₁, _, _, _, hk₁⟩ := hdom_to_idx u₁ hu₁
      obtain ⟨i₂, hi₂, _, _, _, hk₂⟩ := hdom_to_idx u₂ hu₂
      have hr₁ : rKeyAt i₁ = fpReducedKey c U n_max θ.2 u₁ := by
        dsimp only [rKeyAt]; simp [hk₁, u₁.isLt]
      have hr₂ : rKeyAt i₂ = fpReducedKey c U n_max θ.2 u₂ := by
        dsimp only [rKeyAt]; simp [hk₂, u₂.isLt]
      have hi_eq := hp i₁ hi₁ i₂ hi₂ (hr₁.trans (hr_eq.trans hr₂.symm))
      subst hi_eq
      exact Fin.ext (hk₁.symm.trans hk₂)
    · intro hinj_dom i₁ hi₁ i₂ hi₂ hr_eq
      obtain ⟨hb₁, hlo₁, hhi₁, hu₁_lt, hfb₁, hq₁, hmem₁⟩ := hidx_props i₁ hi₁
      obtain ⟨hb₂, hlo₂, hhi₂, hu₂_lt, hfb₂, hq₂, hmem₂⟩ := hidx_props i₂ hi₂
      have hr₁ : rKeyAt i₁ = fpReducedKey c U n_max θ.2 ⟨keyValAt i₁, hu₁_lt⟩ := by
        dsimp only [rKeyAt]; simp [hu₁_lt]
      have hr₂ : rKeyAt i₂ = fpReducedKey c U n_max θ.2 ⟨keyValAt i₂, hu₂_lt⟩ := by
        dsimp only [rKeyAt]; simp [hu₂_lt]
      have hu_eq : (⟨keyValAt i₁, hu₁_lt⟩ : Fin U) = ⟨keyValAt i₂, hu₂_lt⟩ :=
        hinj_dom hmem₁ hmem₂ (hr₁.symm.trans (hr_eq.trans hr₂))
      have hkv_eq : keyValAt i₁ = keyValAt i₂ := congrArg Fin.val hu_eq
      have hb_eq : csrBucketOfIdx csr.fbStart i₁ M = csrBucketOfIdx csr.fbStart i₂ M := by
        rw [← hfb₁, hkv_eq, hfb₂]
      have hqa_eq : csr.qArr i₁ = csr.qArr i₂ := by
        rw [← hq₁, hkv_eq, hq₂]
      rw [hb_eq] at hlo₁ hhi₁
      exact hinj_q _ hb₂ i₁ i₂ hlo₁ hhi₁ hlo₂ hhi₂ hqa_eq
  have hsalt_b_iff : ∀ b : Fin M,
      (∀ s : Fin (sMaxWhp c n_max),
        (∀ t₁ < csr.fbStart (b.val + 1) - csr.fbStart b.val,
         ∀ t₂ < csr.fbStart (b.val + 1) - csr.fbStart b.val,
          fpAt s.val (csr.fbStart b.val + t₁) = fpAt s.val (csr.fbStart b.val + t₂) → t₁ = t₂) ↔
        Set.InjOn (fpHash c U n_max θ.2 s)
          ((Dictionary.dom dict).filter (fun u =>
            feistelBucket (bWhp n_max) h1 u.val = b.val) : Set (Fin U))) := by
    intro b s
    set lo := csr.fbStart b.val
    set len := csr.fbStart (b.val + 1) - lo
    have hlo_hi : lo + len = csr.fbStart (b.val + 1) := by
      have := hadj b.val b.isLt; omega
    constructor
    · intro hpair u₁ hu₁ u₂ hu₂ hfp_eq
      rw [mem_coe, mem_filter] at hu₁ hu₂
      obtain ⟨i₁, hi₁, hlo₁, hhi₁, _, hk₁⟩ := hdom_to_idx u₁ hu₁.1
      obtain ⟨i₂, hi₂, hlo₂, hhi₂, _, hk₂⟩ := hdom_to_idx u₂ hu₂.1
      rw [hu₁.2] at hlo₁ hhi₁
      rw [hu₂.2] at hlo₂ hhi₂
      set t₁ := i₁ - lo
      set t₂ := i₂ - lo
      have ht₁_lt : t₁ < len := by omega
      have ht₂_lt : t₂ < len := by omega
      have hi₁_eq : lo + t₁ = i₁ := by omega
      have hi₂_eq : lo + t₂ = i₂ := by omega
      have hfp₁ : fpAt s.val (lo + t₁) = fpHash c U n_max θ.2 s u₁ := by
        rw [hi₁_eq]; dsimp only [fpAt]; simp [s.isLt, hk₁, u₁.isLt]
      have hfp₂ : fpAt s.val (lo + t₂) = fpHash c U n_max θ.2 s u₂ := by
        rw [hi₂_eq]; dsimp only [fpAt]; simp [s.isLt, hk₂, u₂.isLt]
      have ht_eq := hpair t₁ ht₁_lt t₂ ht₂_lt (hfp₁.trans (hfp_eq.trans hfp₂.symm))
      have hi_eq : i₁ = i₂ := by omega
      subst hi_eq
      exact Fin.ext (hk₁.symm.trans hk₂)
    · intro hinj_s t₁ ht₁ t₂ ht₂ hfp_eq
      set i₁ := lo + t₁
      set i₂ := lo + t₂
      have hi₁_hi : i₁ < csr.fbStart (b.val + 1) := by omega
      have hi₂_hi : i₂ < csr.fbStart (b.val + 1) := by omega
      have hi₁_N : i₁ < N := hi₁_hi.trans_le (hmono (b.val + 1) M (by omega) le_rfl)
      have hi₂_N : i₂ < N := hi₂_hi.trans_le (hmono (b.val + 1) M (by omega) le_rfl)
      have hb₁_eq := csrBucketOfIdx_eq_of_in_range hfb0 hadj b.isLt (by omega) hi₁_hi
      have hb₂_eq := csrBucketOfIdx_eq_of_in_range hfb0 hadj b.isLt (by omega) hi₂_hi
      obtain ⟨_, _, _, hu₁_lt, hfb₁, hq₁, hmem₁⟩ := hidx_props i₁ hi₁_N
      obtain ⟨_, _, _, hu₂_lt, hfb₂, hq₂, hmem₂⟩ := hidx_props i₂ hi₂_N
      rw [hb₁_eq] at hfb₁
      rw [hb₂_eq] at hfb₂
      have hfp₁ : fpAt s.val i₁ = fpHash c U n_max θ.2 s ⟨keyValAt i₁, hu₁_lt⟩ := by
        dsimp only [fpAt]; simp [s.isLt, hu₁_lt]
      have hfp₂ : fpAt s.val i₂ = fpHash c U n_max θ.2 s ⟨keyValAt i₂, hu₂_lt⟩ := by
        dsimp only [fpAt]; simp [s.isLt, hu₂_lt]
      have hm₁ : (⟨keyValAt i₁, hu₁_lt⟩ : Fin U) ∈
          ((Dictionary.dom dict).filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :=
        mem_filter.mpr ⟨hmem₁, hfb₁⟩
      have hm₂ : (⟨keyValAt i₂, hu₂_lt⟩ : Fin U) ∈
          ((Dictionary.dom dict).filter fun u => feistelBucket (bWhp n_max) h1 u.val = b.val) :=
        mem_filter.mpr ⟨hmem₂, hfb₂⟩
      have hu_eq := hinj_s hm₁ hm₂ (hfp₁.symm.trans (hfp_eq.trans hfp₂))
      have hkv_eq : keyValAt i₁ = keyValAt i₂ := congrArg Fin.val hu_eq
      have hqa_eq : csr.qArr i₁ = csr.qArr i₂ := by rw [← hq₁, hkv_eq, hq₂]
      have hi_eq := hinj_q b.val b.isLt i₁ i₂ (by omega) hi₁_hi (by omega) hi₂_hi hqa_eq
      omega
  dsimp only [checkGoodSeedOnState]
  change ((checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M &&
      checkPairwiseDistinctOn rKeyAt N && allSaltsFound M) = true ↔
      GoodSeedOnState c U n_max θ dict) ∧
    ((checkAllBalancedCsr M (deltaWhp n_max) N csr.fbStart M &&
      checkPairwiseDistinctOn rKeyAt N && allSaltsFound M) = true → _)
  refine ⟨?_, ?_⟩
  · simp only [Bool.and_eq_true, hbal_iff, hinj_iff, hallSalts_iff, GoodSeedOnState]
    constructor
    · rintro ⟨⟨hbal, hinj_r⟩, hsalts⟩
      refine ⟨hinj_r, hbal, fun b => ?_⟩
      have hnz := hsalts b.val b.isLt
      obtain ⟨hs_lt, hpair⟩ := (findSaltInRange_props fpAt (csr.fbStart b.val)
        (csr.fbStart (b.val + 1) - csr.fbStart b.val) (sMaxWhp c n_max)).2 hnz
      exact ⟨⟨salt1Of b.val - 1, hs_lt⟩, (hsalt_b_iff b ⟨salt1Of b.val - 1, hs_lt⟩).mp hpair⟩
    · rintro ⟨hinj_r, hbal, hsalts⟩
      refine ⟨⟨hbal, hinj_r⟩, fun b hb_lt => ?_⟩
      obtain ⟨s, hinj_s⟩ := hsalts ⟨b, hb_lt⟩
      intro h0
      have hall_not := (findSaltInRange_props fpAt (csr.fbStart b)
        (csr.fbStart (b + 1) - csr.fbStart b) (sMaxWhp c n_max)).1.mp h0
      exact hall_not s.val s.isLt ((hsalt_b_iff ⟨b, hb_lt⟩ s).mpr hinj_s)
  · intro hok b
    simp only [Bool.and_eq_true, hallSalts_iff] at hok
    have hnz := hok.2 b.val b.isLt
    obtain ⟨hs_lt, hpair⟩ := (findSaltInRange_props fpAt (csr.fbStart b.val)
      (csr.fbStart (b.val + 1) - csr.fbStart b.val) (sMaxWhp c n_max)).2 hnz
    exact ⟨hs_lt, (hsalt_b_iff b ⟨salt1Of b.val - 1, hs_lt⟩).mp hpair⟩

end Cslib.DataStructure.Dictionary.SuccinctWhp

end
