/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.FRI.Soundness.Transcript

/-!
# Smooth FRI Fiber-Weight Bounds and Prefix Starting-Point Counting

Proves pointwise and total bounds on `friSmoothPreWeight` and `friSmoothNextWeight`, filtered
agreement monotonicity (`sum_agree_friSmoothOracleFilterWeight_le`), and the exact per-round
starting-point counting identity `card_filter_friSmoothPrefixPasses_eq`.
-/

public section

namespace Cslib.Crypto.Protocols.FRI

open scoped BigOperators ENNReal
open Cslib.Code
open Cslib.OracleComp
open Cslib.Crypto.Protocols.BCS
open Cslib.Probability

/-! ### Smooth Fiber-Weight Bounds -/

section SmoothWeightBounds

variable {F : Type} [Field F]

/-- Equivalence between `Fin (params.arity i * params.domainSize (i.val + 1))` and
`Fin (params.domainSize i.val)` for a smooth folding round `i : Fin params.m`. -/
private abbrev FRISmoothParams.fiberDomainEquiv (params : FRISmoothParams F) (i : Fin params.m) :
    Fin (params.arity i * params.domainSize (i.val + 1)) ≃ Fin (params.domainSize i.val) :=
  finCongr (params.domainSize_eq_arity_mul_succ i).symm

private theorem friSmoothOracleFilterWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (j : Fin (params.domainSize i)) :
    friSmoothOracleFilterWeight params stmt pref i hi π j ≤
      friSmoothPreWeight params stmt pref i hi j := by
  unfold friSmoothOracleFilterWeight
  split_ifs <;> omega

private theorem friSmoothNextWeight_le_of [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i < params.m) (π : OracleTable params.d F)
    (hprev : ∀ y, friSmoothPreWeight params stmt pref i hi.le y ≤ 2 ^ params.cumLog i)
    (j : Fin (params.domainSize (i + 1))) :
    friSmoothNextWeight params stmt pref i hi π j ≤ 2 ^ params.cumLog (i + 1) := by
  refine (pushWeight_le (M := 2 ^ params.cumLog i) (fun idx =>
    (friSmoothOracleFilterWeight_le params stmt pref i hi.le π _).trans (hprev _)) j).trans_eq ?_
  rw [params.cumLog_succ ⟨i, hi⟩, FRISmoothParams.arity, ← pow_add, add_comm]

private theorem sum_friSmoothNextWeight_le_prev [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    {i : ℕ} (hi : i < params.m) (π : OracleTable params.d F) :
    (∑ j : Fin (params.domainSize (i + 1)), friSmoothNextWeight params stmt pref i hi π j) ≤
      ∑ y : Fin (params.domainSize i), friSmoothPreWeight params stmt pref i hi.le y := by
  rw [friSmoothNextWeight, sum_pushWeight, Equiv.sum_comp (params.fiberDomainEquiv ⟨i, hi⟩)]
  exact Finset.sum_le_sum fun y _ => friSmoothOracleFilterWeight_le params stmt pref i hi.le π y

/-- Pointwise bound on smooth pre-filter weights: `friSmoothPreWeight ... i j ≤ 2 ^ cumLog i`. -/
theorem friSmoothPreWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (params.domainSize i)),
      friSmoothPreWeight params stmt pref i hi j ≤ 2 ^ params.cumLog i
  | 0, _, _ => by simp [friSmoothPreWeight, FRISmoothParams.cumLog]
  | i + 1, hi, j =>
    friSmoothNextWeight_le_of params stmt pref hi (prefOracle pref i)
      (friSmoothPreWeight_le params stmt pref i (Nat.le_of_succ_le hi)) j

/-- Pointwise bound on smooth pushed weights: `friSmoothNextWeight ... i π j ≤ 2 ^ cumLog (i + 1)`.
-/
theorem friSmoothNextWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F)
    (j : Fin (params.domainSize (i + 1))) :
    friSmoothNextWeight params stmt pref i hi π j ≤ 2 ^ params.cumLog (i + 1) :=
  friSmoothNextWeight_le_of params stmt pref hi π
    (friSmoothPreWeight_le params stmt pref i hi.le) j

/-- Total-weight bound on smooth pre-filter weights: `∑ j, friSmoothPreWeight ... i j ≤ 2 ^ d`. -/
theorem sum_friSmoothPreWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m),
      (∑ j : Fin (params.domainSize i), friSmoothPreWeight params stmt pref i hi j) ≤
        2 ^ params.d
  | 0, _ => by
    simp only [friSmoothPreWeight, Finset.sum_const, smul_eq_mul, mul_one]
    rw [Finset.card_univ, Fintype.card_fin, FRISmoothParams.domainSize, FRISmoothParams.cumLog,
      friCumLog_zero, Nat.sub_zero]
  | i + 1, hi =>
    (sum_friSmoothNextWeight_le_prev params stmt pref hi (prefOracle pref i)).trans
      (sum_friSmoothPreWeight_le params stmt pref i (Nat.le_of_succ_le hi))

/-- Total-weight bound on smooth pushed weights: `∑ j, friSmoothNextWeight ... i π j ≤ 2 ^ d`. -/
theorem sum_friSmoothNextWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i < params.m) (π : OracleTable params.d F) :
    (∑ j : Fin (params.domainSize (i + 1)), friSmoothNextWeight params stmt pref i hi π j) ≤
      2 ^ params.d :=
  (sum_friSmoothNextWeight_le_prev params stmt pref hi π).trans
    (sum_friSmoothPreWeight_le params stmt pref i hi.le)

/-- Monotonicity of filtered weighted agreement for smooth FRI: replacing `friSmoothTargetWord` and
`friSmoothPreWeight` by an arbitrary prover oracle `π` and its filtered weight
`friSmoothOracleFilterWeight` cannot increase weighted agreement with any word `c`. -/
theorem sum_agree_friSmoothOracleFilterWeight_le [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    (i : ℕ) (hi : i ≤ params.m) (π : OracleTable params.d F)
    (c : Fin (params.domainSize i) → F) :
    (∑ j ∈ Finset.univ.filter (fun j => restrictOracle (i := params.cumLog i) π j = c j),
      friSmoothOracleFilterWeight params stmt pref i hi π j) ≤
    ∑ j ∈ Finset.univ.filter (fun j => friSmoothTargetWord params stmt pref i hi j = c j),
      friSmoothPreWeight params stmt pref i hi j := by
  simp only [Finset.sum_filter, friSmoothOracleFilterWeight]
  refine Finset.sum_le_sum fun j _ => ?_
  split_ifs with h1 h2 h3 <;> try exact Nat.zero_le _
  · exact le_rfl
  · exact absurd (h2.symm.trans h1) h3


/-! ### Smooth Prefix Starting-Point Counting -/

/-- Exact `a`-way mod-splitting helper: for `0 < a` and `j < N`, `s % N = j` splits disjointly into
`∃ t : Fin a, s % (a * N) = j + t.val * N`. -/
private theorem mod_eq_iff_exists_fiberIdx {a N s j : ℕ} (ha : 0 < a) (hj : j < N) :
    s % N = j ↔ ∃ t : Fin a, s % (a * N) = j + t.val * N := by
  have hN : 0 < N := by omega
  have hmod : (s % (a * N)) % N = s % N := Nat.mod_mul_left_mod s a N
  refine ⟨fun h => ⟨⟨(s % (a * N)) / N, (Nat.div_lt_iff_lt_mul hN).mpr
    (Nat.mod_lt s (Nat.mul_pos ha hN))⟩, ?_⟩, fun ⟨t, ht⟩ => ?_⟩
  · have := Nat.div_add_mod (s % (a * N)) N; rw [hmod, h] at this; linarith
  · rw [← hmod, ht, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hj]

private theorem friSmoothPrefixPasses_succ_iff (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    {k : ℕ} (hi : k + 1 ≤ params.m) (j : Fin (params.domainSize (k + 1)))
    {s : Fin (2 ^ params.d)} (hs : s.val % params.domainSize (k + 1) = j.val) :
    friSmoothPrefixPasses params stmt pref (k + 1) s ↔
      friSmoothPrefixPasses params stmt pref k s ∧
        restrictOracle (i := params.cumLog (k + 1)) (prefOracle pref (k + 1)) j =
          friSmoothTargetWord params stmt pref (k + 1) hi j := by
  let kr : Fin params.m := ⟨k, Nat.lt_of_succ_le hi⟩
  have hfold :
      foldFiber (params.g ^ (2 ^ params.cumLog k)) (params.ω ^ (2 ^ params.cumLog k))
        (fun t : Fin (params.arity kr) => prefOracle pref k (friSmoothFiberIdx params kr s t))
        (friSmoothFoldedFin params kr s) (prefFoldScalar pref k) =
      friSmoothTargetWord params stmt pref (k + 1) hi j := by
    rw [show friSmoothFoldedFin params kr s = j from Fin.ext hs, friSmoothTargetWord,
      foldWord_apply_eq_foldFiber]
    congr 1; funext t; exact congrArg (prefOracle pref k) (Fin.ext (by
      simpa only [friSmoothFiberIdx, fiberIdx, FRISmoothParams.domainSize, finCongr_apply,
        Fin.val_cast] using congrArg (· + t.val * params.domainSize (k + 1)) hs))
  have hrhs : prefOracle pref (k + 1) (friSmoothFoldedIdx params kr s) =
      restrictOracle (i := params.cumLog (k + 1)) (prefOracle pref (k + 1)) j :=
    congrArg (prefOracle pref (k + 1)) (Fin.ext hs)
  simp only [friSmoothPrefixPasses, Nat.lt_succ_iff_lt_or_eq]
  constructor
  · rintro ⟨hbind, hall⟩
    exact ⟨⟨hbind, fun r hr => hall r (.inl hr)⟩,
      by have h := hall kr (.inr rfl); rwa [hfold, hrhs, eq_comm] at h⟩
  · rintro ⟨⟨hbind, hall⟩, hcur⟩
    refine ⟨hbind, fun r hr => hr.elim (hall r) fun heq => ?_⟩
    obtain rfl : r = kr := Fin.ext heq
    rwa [hfold, hrhs, eq_comm]

private theorem card_filter_friSmoothPrefixPasses_step_split [DecidableEq F]
    (params : FRISmoothParams F) (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q))
    {k : ℕ} (hi : k + 1 ≤ params.m) (j : Fin (params.domainSize (k + 1))) :
    (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      s.val % params.domainSize (k + 1) = j.val ∧
        friSmoothPrefixPasses params stmt pref k s).card =
      ∑ t : Fin (params.arity ⟨k, Nat.lt_of_succ_le hi⟩),
        (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
          s.val % params.domainSize k =
            (params.fiberDomainEquiv ⟨k, Nat.lt_of_succ_le hi⟩ (fiberIdx j t)).val ∧
            friSmoothPrefixPasses params stmt pref k s).card := by
  let kr : Fin params.m := ⟨k, Nat.lt_of_succ_le hi⟩
  let S (t : Fin (params.arity kr)) := Finset.univ.filter fun s : Fin (2 ^ params.d) =>
    s.val % params.domainSize k = (params.fiberDomainEquiv kr (fiberIdx j t)).val ∧
      friSmoothPrefixPasses params stmt pref k s
  have hsplit : params.domainSize k = params.arity kr * params.domainSize (k + 1) :=
    params.domainSize_eq_arity_mul_succ kr
  have hunion : (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
      s.val % params.domainSize (k + 1) = j.val ∧ friSmoothPrefixPasses params stmt pref k s) =
      Finset.univ.biUnion S := by
    ext s
    simp only [S, Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, hsplit,
      FRISmoothParams.fiberDomainEquiv, finCongr_apply, Fin.val_cast, fiberIdx]
    rw [mod_eq_iff_exists_fiberIdx (lt_of_lt_of_le (by omega) (params.two_le_arity kr)) j.isLt,
      exists_and_right]
  rw [hunion]
  exact Finset.card_biUnion fun t₁ _ t₂ _ hne => Finset.disjoint_left.mpr fun s hs₁ hs₂ =>
    hne <| Fin.ext <| Nat.eq_of_mul_eq_mul_right (Nat.pow_pos (by omega)) <|
      Nat.add_left_cancel ((Finset.mem_filter.mp hs₁).2.1.symm.trans (Finset.mem_filter.mp hs₂).2.1)

/-- **Exact smooth starting-point counting identity**: for every round `i ≤ m` and active-domain
coordinate `j : Fin (params.domainSize i)`, the filtered weight
`friSmoothOracleFilterWeight ... i (prefOracle pref i) j` equals the exact number of initial
positions `s : Fin (2 ^ d)` with `s % params.domainSize i = j` that satisfy
`friSmoothPrefixPasses ... i s`. -/
theorem card_filter_friSmoothPrefixPasses_eq [DecidableEq F] (params : FRISmoothParams F)
    (stmt : OracleTable params.d F)
    (pref : List (OracleTable params.d F × FRIChal F params.d params.q)) :
    ∀ (i : ℕ) (hi : i ≤ params.m) (j : Fin (params.domainSize i)),
      (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % params.domainSize i = j.val ∧ friSmoothPrefixPasses params stmt pref i s).card =
      friSmoothOracleFilterWeight params stmt pref i hi (prefOracle pref i) j
  | 0, _, j => by
    have hdom0 : params.domainSize 0 = 2 ^ params.d := by
      simp [FRISmoothParams.domainSize, FRISmoothParams.cumLog]
    let j₀ : Fin (2 ^ params.d) := ⟨j.val, hdom0 ▸ j.isLt⟩
    have hset : (Finset.univ.filter fun s : Fin (2 ^ params.d) =>
        s.val % params.domainSize 0 = j.val ∧ friSmoothPrefixPasses params stmt pref 0 s) =
        if prefOracle pref 0 j₀ = stmt j₀ then {j₀} else ∅ := by
      ext s
      have hmod : s.val % params.domainSize 0 = j.val ↔ s = j₀ := by
        simp [hdom0, Nat.mod_eq_of_lt s.isLt, Fin.ext_iff, j₀]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hmod, friSmoothPrefixPasses,
        Nat.not_lt_zero, false_implies, implies_true, and_true]
      by_cases hok : prefOracle pref 0 j₀ = stmt j₀ <;> simp +contextual [hok]
    rw [hset]
    by_cases hok : prefOracle pref 0 j₀ = stmt j₀ <;>
      simp [friSmoothOracleFilterWeight, friSmoothTargetWord, friSmoothPreWeight, restrictOracle,
        hok, j₀]
  | k + 1, hi, j => by
    simp only [friSmoothOracleFilterWeight]
    split_ifs with hmatch
    · rw [Finset.filter_congr (q := fun s => s.val % params.domainSize (k + 1) = j.val ∧
          friSmoothPrefixPasses params stmt pref k s) fun s _ => and_congr_right fun hs =>
          (friSmoothPrefixPasses_succ_iff params stmt pref hi j hs).trans (by simp [hmatch]),
        card_filter_friSmoothPrefixPasses_step_split params stmt pref hi j]
      exact Finset.sum_congr rfl fun t _ =>
        card_filter_friSmoothPrefixPasses_eq params stmt pref k (Nat.le_of_succ_le hi) _
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun s _ ⟨hs, hp⟩ =>
        hmatch ((friSmoothPrefixPasses_succ_iff params stmt pref hi j hs).mp hp).2


end SmoothWeightBounds

end Cslib.Crypto.Protocols.FRI
