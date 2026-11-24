/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.StableMatching.Incentives

/-!
# Roth's impossibility theorem for all `n ≥ 3` and the sharp `n ≤ 2` threshold

`CslibFrontier.Algorithms.Lean.StableMatching.Incentives` proved **Roth's impossibility theorem**
([Roth1982], Theorem 3) at market size `n = 3`. This module lifts the impossibility to **every**
`n ≥ 3` by padding `MatchingMechanism.rothInstance` with `n - 3` mutually top-ranked dummy pairs
(`padInstance`), and complements it with the **sharp positive threshold for `n ≤ 2`**: with
strict complete preference lists, proposer-proposing deferred acceptance is strategy-proof for
**both** proposers and receivers whenever `n ≤ 2` (and symmetrically for receiver-proposing DA).

## Main definitions

* `Cslib.Algorithms.Lean.StableMatching.MatchingMechanism.extendPerm`: lift a permutation on
  `Fin 3` to `Fin n` (`3 ≤ n`), fixing coordinates `≥ 3`.
* `Cslib.Algorithms.Lean.StableMatching.MatchingMechanism.padInstance`: embed a `3 × 3` market
  into `Instance n` (`3 ≤ n`) by adding `n - 3` mutually top-ranked dummy pairs `(d, d)`.

## Main results

* `Cslib.Algorithms.Lean.StableMatching.MatchingMechanism.isStable_padInstance_fixed`: every
  stable matching of `padInstance hn I` matches every dummy `d ≥ 3` to itself.
* `Cslib.Algorithms.Lean.StableMatching.MatchingMechanism.isStable_padInstance_restrict`: the
  restriction of a stable matching of `padInstance hn I` to `{0, 1, 2}` is stable for `I`.
* `Cslib.Algorithms.Lean.StableMatching.MatchingMechanism.not_isStable_and_strategyProof_of_le`:
  **Roth's impossibility theorem** ([Roth1982], Theorem 3) for **every** `n ≥ 3`: no stable
  matching mechanism of size `n` is strategy-proof for both proposers and receivers.
* `MatchingMechanism.isReceiverStrategyProof_deferredAcceptance_of_le_two`,
  `MatchingMechanism.isProposerStrategyProof_receiverDeferredAcceptance_of_le_two`:
  sharp converse for complete lists at `n ≤ 2` (both deferred-acceptance mechanisms are mutually
  strategy-proof).

## References

* [Roth1982]
-/

public section

namespace Cslib.Algorithms.Lean.StableMatching.MatchingMechanism

/-! ### Lifting `3 × 3` instances to `n ≥ 3` via mutually top-ranked dummy pairs -/

/-- Lift a permutation on `Fin 3` to `Fin n` (`3 ≤ n`), fixing every coordinate `k ≥ 3`. -/
@[expose] def extendPerm {n : ℕ} (hn : 3 ≤ n) (π : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin n) where
  toFun k :=
    if hk : k.val < 3 then ⟨(π ⟨k.val, hk⟩).val, lt_of_lt_of_le (π ⟨k.val, hk⟩).isLt hn⟩ else k
  invFun k :=
    if hk : k.val < 3 then
      ⟨(π.symm ⟨k.val, hk⟩).val, lt_of_lt_of_le (π.symm ⟨k.val, hk⟩).isLt hn⟩
    else k
  left_inv k := by
    by_cases hk : k.val < 3
    · have hlt : (π ⟨k.val, hk⟩).val < 3 := (π ⟨k.val, hk⟩).isLt
      simp only [hk, ↓reduceDIte, hlt, Fin.eta, Equiv.symm_apply_apply]
    · simp only [hk, ↓reduceDIte]
  right_inv k := by
    by_cases hk : k.val < 3
    · have hlt : (π.symm ⟨k.val, hk⟩).val < 3 := (π.symm ⟨k.val, hk⟩).isLt
      simp only [hk, ↓reduceDIte, hlt, Fin.eta, Equiv.apply_symm_apply]
    · simp only [hk, ↓reduceDIte]

private theorem extendPerm_symm_lt {n : ℕ} (hn : 3 ≤ n) (π : Equiv.Perm (Fin 3)) (k : Fin n)
    (hk : k.val < 3) :
    ((extendPerm hn π).symm k).val = (π.symm ⟨k.val, hk⟩).val := by
  simp only [extendPerm, Equiv.symm, Equiv.coe_fn_mk, hk, ↓reduceDIte]

/-- Embed a `3 × 3` instance `I` into `Instance n` (`3 ≤ n`): core agents `{0, 1, 2}` rank
`{0, 1, 2}` strictly above dummies in the exact order of `I`, while each dummy `d ≥ 3` places its
partner `d` at rank `0` (top choice). -/
@[expose] def padInstance {n : ℕ} (hn : 3 ≤ n) (I : Instance 3) : Instance n where
  propPref p :=
    if hp : p.val < 3 then extendPerm hn (I.propPref ⟨p.val, hp⟩)
    else Equiv.swap ⟨0, lt_of_lt_of_le (by omega) hn⟩ p
  recvPref r :=
    if hr : r.val < 3 then extendPerm hn (I.recvPref ⟨r.val, hr⟩)
    else Equiv.swap ⟨0, lt_of_lt_of_le (by omega) hn⟩ r

private theorem padInstance_propRank_core {n : ℕ} (hn : 3 ≤ n) (I : Instance 3)
    (p r : Fin 3) :
    ((padInstance hn I).propRank ⟨p.val, lt_of_lt_of_le p.isLt hn⟩
      ⟨r.val, lt_of_lt_of_le r.isLt hn⟩).val = (I.propRank p r).val := by
  simp only [Instance.propRank, padInstance, p.isLt, ↓reduceDIte]
  exact extendPerm_symm_lt hn (I.propPref p) ⟨r.val, lt_of_lt_of_le r.isLt hn⟩ r.isLt

private theorem padInstance_recvRank_core {n : ℕ} (hn : 3 ≤ n) (I : Instance 3)
    (r p : Fin 3) :
    ((padInstance hn I).recvRank ⟨r.val, lt_of_lt_of_le r.isLt hn⟩
      ⟨p.val, lt_of_lt_of_le p.isLt hn⟩).val = (I.recvRank r p).val := by
  simp only [Instance.recvRank, padInstance, r.isLt, ↓reduceDIte]
  exact extendPerm_symm_lt hn (I.recvPref r) ⟨p.val, lt_of_lt_of_le p.isLt hn⟩ p.isLt

/-- In every stable matching of `padInstance hn I`, each dummy pair `d ≥ 3` is matched to itself
(because both sides rank each other first). -/
theorem isStable_padInstance_fixed {n : ℕ} (hn : 3 ≤ n) {I : Instance 3} {μ : Matching n}
    (hμ : (padInstance hn I).IsStable μ) {d : Fin n} (hd : 3 ≤ d.val) :
    μ d = d := by
  by_contra hne
  have hd_not : ¬ d.val < 3 := by omega
  have hzero_d : ∀ (a : Fin n), ((Equiv.swap ⟨0, lt_of_lt_of_le (by omega) hn⟩ a).symm a).val =
      0 := fun a => by
    rw [Equiv.symm_swap, Equiv.swap_apply_right]
  have hprop0 : ((padInstance hn I).propRank d d).val = 0 := by
    simp only [Instance.propRank, padInstance, hd_not, ↓reduceDIte]
    exact hzero_d d
  have hrecv0 : ((padInstance hn I).recvRank d d).val = 0 := by
    simp only [Instance.recvRank, padInstance, hd_not, ↓reduceDIte]
    exact hzero_d d
  have hp_lt : (padInstance hn I).propRank d d < (padInstance hn I).propRank d (μ d) := by
    refine lt_of_le_of_ne ?_ fun heq => hne ((padInstance hn I).propRank_injective d heq).symm
    change ((padInstance hn I).propRank d d).val ≤ ((padInstance hn I).propRank d (μ d)).val
    rw [hprop0]
    exact Nat.zero_le _
  have hne_s : μ.symm d ≠ d := fun h => hne ((Equiv.symm_apply_eq μ).1 h).symm
  have hr_lt : (padInstance hn I).recvRank d d < (padInstance hn I).recvRank d (μ.symm d) := by
    refine lt_of_le_of_ne ?_ fun heq => hne_s ((padInstance hn I).recvRank_injective d heq).symm
    change ((padInstance hn I).recvRank d d).val ≤ ((padInstance hn I).recvRank d (μ.symm d)).val
    rw [hrecv0]
    exact Nat.zero_le _
  exact hμ d d ⟨hp_lt, hr_lt⟩

/-- Restrict a matching `μ : Matching n` that fixes every coordinate `≥ 3` to a `Matching 3`. -/
private def restrictMatching {n : ℕ} (hn : 3 ≤ n) (μ : Matching n)
    (hfix : ∀ d : Fin n, 3 ≤ d.val → μ d = d) : Matching 3 where
  toFun p :=
    ⟨(μ ⟨p.val, lt_of_lt_of_le p.isLt hn⟩).val, by
      by_contra hge
      have hfixed := hfix (μ ⟨p.val, lt_of_lt_of_le p.isLt hn⟩) (by omega)
      have hval : p.val = (μ ⟨p.val, lt_of_lt_of_le p.isLt hn⟩).val :=
        congrArg Fin.val (μ.injective hfixed.symm)
      have := p.isLt
      omega⟩
  invFun r :=
    ⟨(μ.symm ⟨r.val, lt_of_lt_of_le r.isLt hn⟩).val, by
      by_contra hge
      have hfixed := hfix (μ.symm ⟨r.val, lt_of_lt_of_le r.isLt hn⟩) (by omega)
      rw [Equiv.apply_symm_apply] at hfixed
      have hval : r.val = (μ.symm ⟨r.val, lt_of_lt_of_le r.isLt hn⟩).val :=
        congrArg Fin.val hfixed
      have := r.isLt
      omega⟩
  left_inv p := by ext; simp
  right_inv r := by ext; simp

private theorem isStable_restrict {n : ℕ} (hn : 3 ≤ n) {I : Instance 3} {μ : Matching n}
    (hμ : (padInstance hn I).IsStable μ) :
    I.IsStable (restrictMatching hn μ (fun _ hd => isStable_padInstance_fixed hn hμ hd)) := by
  rintro p r ⟨hp, hr⟩
  let p' : Fin n := ⟨p.val, lt_of_lt_of_le p.isLt hn⟩
  let r' : Fin n := ⟨r.val, lt_of_lt_of_le r.isLt hn⟩
  let ρ := restrictMatching hn μ (fun _ hd => isStable_padInstance_fixed hn hμ hd)
  have hμp' : (⟨(ρ p).val, lt_of_lt_of_le (ρ p).isLt hn⟩ : Fin n) = μ p' := by ext; rfl
  have hμr' : (⟨(ρ.symm r).val, lt_of_lt_of_le (ρ.symm r).isLt hn⟩ : Fin n) = μ.symm r' := by
    ext; rfl
  refine hμ p' r' ⟨?_, ?_⟩
  · change (padInstance hn I).propRank p' r' < (padInstance hn I).propRank p' (μ p')
    rw [← hμp', Fin.lt_def, padInstance_propRank_core, padInstance_propRank_core]
    exact hp
  · change (padInstance hn I).recvRank r' p' < (padInstance hn I).recvRank r' (μ.symm r')
    rw [← hμr', Fin.lt_def, padInstance_recvRank_core, padInstance_recvRank_core]
    exact hr

/-- Any stable matching of `padInstance hn I` restricts on `{0, 1, 2}` to a stable matching of
`I`. -/
theorem isStable_padInstance_restrict {n : ℕ} (hn : 3 ≤ n) {I : Instance 3} {μ : Matching n}
    (hμ : (padInstance hn I).IsStable μ) :
    ∃ ρ : Matching 3, I.IsStable ρ ∧
      ∀ p : Fin 3, (ρ p).val = (μ ⟨p.val, lt_of_lt_of_le p.isLt hn⟩).val :=
  ⟨restrictMatching hn μ (fun _ hd => isStable_padInstance_fixed hn hμ hd),
   isStable_restrict hn hμ, fun _ => rfl⟩

private theorem instance_ext {n : ℕ} {I J : Instance n}
    (hp : I.propPref = J.propPref) (hr : I.recvPref = J.recvPref) : I = J := by
  cases I; cases J; simp_all

private theorem padPref_update {n : ℕ} (hn : 3 ≤ n) (f : Fin 3 → Equiv.Perm (Fin 3))
    (i : Fin 3) (π : Equiv.Perm (Fin 3)) :
    (fun x : Fin n =>
      if h : x.val < 3 then extendPerm hn (Function.update f i π ⟨x.val, h⟩)
      else Equiv.swap ⟨0, lt_of_lt_of_le (by omega) hn⟩ x) =
      Function.update
        (fun x : Fin n =>
          if h : x.val < 3 then extendPerm hn (f ⟨x.val, h⟩)
          else Equiv.swap ⟨0, lt_of_lt_of_le (by omega) hn⟩ x)
        ⟨i.val, lt_of_lt_of_le i.isLt hn⟩ (extendPerm hn π) := by
  funext x
  by_cases hx : x = ⟨i.val, lt_of_lt_of_le i.isLt hn⟩
  · subst hx; simp [i.isLt]
  · rw [Function.update_of_ne hx]
    split_ifs with hlt
    · have hne : (⟨x.val, hlt⟩ : Fin 3) ≠ i :=
        fun h => hx (Fin.ext (congrArg Fin.val h : x.val = i.val))
      rw [Function.update_of_ne hne]
    · rfl

private theorem padInstance_updatePropPref {n : ℕ} (hn : 3 ≤ n) (I : Instance 3) (p : Fin 3)
    (π : Equiv.Perm (Fin 3)) :
    padInstance hn (I.updatePropPref p π) =
      (padInstance hn I).updatePropPref ⟨p.val, lt_of_lt_of_le p.isLt hn⟩ (extendPerm hn π) :=
  instance_ext (padPref_update hn I.propPref p π) rfl

private theorem padInstance_updateRecvPref {n : ℕ} (hn : 3 ≤ n) (I : Instance 3) (r : Fin 3)
    (π : Equiv.Perm (Fin 3)) :
    padInstance hn (I.updateRecvPref r π) =
      (padInstance hn I).updateRecvPref ⟨r.val, lt_of_lt_of_le r.isLt hn⟩ (extendPerm hn π) :=
  instance_ext rfl (padPref_update hn I.recvPref r π)

/-- **Roth's impossibility theorem** ([Roth1982], Theorem 3) for **every** `n ≥ 3`: no stable
matching mechanism on `n` proposers and `n` receivers with strict complete lists is
strategy-proof for both proposers and receivers. -/
theorem not_isStable_and_strategyProof_of_le {n : ℕ} (hn : 3 ≤ n) (M : MatchingMechanism n) :
    ¬ (M.IsStable ∧ M.IsProposerStrategyProof ∧ M.IsReceiverStrategyProof) := by
  rintro ⟨hs, hp, hr⟩
  let base := padInstance hn rothInstance
  have hbase : base.IsStable (M base) := hs base
  let ρ := restrictMatching hn (M base) (fun _ hd => isStable_padInstance_fixed hn hbase hd)
  rcases (rothInstance_isStable_iff ρ).1 (isStable_restrict hn hbase) with h | h
  · let π : Equiv.Perm (Fin 3) := permOfInjective ![2, 0, 1]
    let r0 : Fin n := ⟨0, lt_of_lt_of_le (0 : Fin 3).isLt hn⟩
    let upd := base.updateRecvPref r0 (extendPerm hn π)
    have hupd_eq : upd = padInstance hn (rothInstance.updateRecvPref 0 π) :=
      (padInstance_updateRecvPref hn rothInstance 0 π).symm
    have hupd : (padInstance hn (rothInstance.updateRecvPref 0 π)).IsStable (M upd) :=
      hupd_eq ▸ hs upd
    let ρ' := restrictMatching hn (M upd) (fun _ hd => isStable_padInstance_fixed hn hupd hd)
    have hgain := rothInstance_receiver_gains (isStable_restrict hn hupd)
    have hsp := hr base r0 (extendPerm hn π)
    have hMbase : (M base).symm r0 = ⟨(ρ.symm 0).val, lt_of_lt_of_le (ρ.symm 0).isLt hn⟩ := by
      ext; rfl
    have hMupd : (M upd).symm r0 = ⟨(ρ'.symm 0).val, lt_of_lt_of_le (ρ'.symm 0).isLt hn⟩ := by
      ext; rfl
    have hsp_val : ((padInstance hn rothInstance).recvRank r0 ((M base).symm r0)).val ≤
        ((padInstance hn rothInstance).recvRank r0 ((M upd).symm r0)).val := hsp
    rw [hMbase, hMupd] at hsp_val
    have h1 := padInstance_recvRank_core hn rothInstance 0 (ρ.symm 0)
    have h2 := padInstance_recvRank_core hn rothInstance 0 (ρ'.symm 0)
    have hr0 : (⟨(0 : Fin 3).val, lt_of_lt_of_le (0 : Fin 3).isLt hn⟩ : Fin n) = r0 := rfl
    rw [← hr0, h1, h2, h] at hsp_val
    exact absurd hsp_val (not_le_of_gt hgain)
  · let π : Equiv.Perm (Fin 3) := permOfInjective ![0, 1, 2]
    let p1 : Fin n := ⟨1, lt_of_lt_of_le (1 : Fin 3).isLt hn⟩
    let upd := base.updatePropPref p1 (extendPerm hn π)
    have hupd_eq : upd = padInstance hn (rothInstance.updatePropPref 1 π) :=
      (padInstance_updatePropPref hn rothInstance 1 π).symm
    have hupd : (padInstance hn (rothInstance.updatePropPref 1 π)).IsStable (M upd) :=
      hupd_eq ▸ hs upd
    let ρ' := restrictMatching hn (M upd) (fun _ hd => isStable_padInstance_fixed hn hupd hd)
    have hgain := rothInstance_proposer_gains (isStable_restrict hn hupd)
    have hsp := hp base p1 (extendPerm hn π)
    have hMbase : M base p1 = ⟨(ρ 1).val, lt_of_lt_of_le (ρ 1).isLt hn⟩ := by ext; rfl
    have hMupd : M upd p1 = ⟨(ρ' 1).val, lt_of_lt_of_le (ρ' 1).isLt hn⟩ := by ext; rfl
    have hsp_val : ((padInstance hn rothInstance).propRank p1 (M base p1)).val ≤
        ((padInstance hn rothInstance).propRank p1 (M upd p1)).val := hsp
    rw [hMbase, hMupd] at hsp_val
    have h1 := padInstance_propRank_core hn rothInstance 1 (ρ 1)
    have h2 := padInstance_propRank_core hn rothInstance 1 (ρ' 1)
    have hp1 : (⟨(1 : Fin 3).val, lt_of_lt_of_le (1 : Fin 3).isLt hn⟩ : Fin n) = p1 := rfl
    rw [← hp1, h1, h2, h] at hsp_val
    exact absurd hsp_val (not_le_of_gt hgain)

/-! ### Sharp converse for complete lists: `n ≤ 2` -/

private theorem perm_fin2_top_of_ne {a b : Equiv.Perm (Fin 2)} (hne : a ≠ b) (p : Fin 2)
    (hp : a.symm p = 1) : b.symm p = 0 := by
  by_contra h
  have h1 : b.symm p = 1 := by omega
  apply hne
  ext k
  have ha1 : a 1 = p := by rw [← hp, Equiv.apply_symm_apply]
  have hb1 : b 1 = p := by rw [← h1, Equiv.apply_symm_apply]
  have hka := a.injective
  have hkb := b.injective
  rcases (show k = 0 ∨ k = 1 by omega) with rfl | rfl
  · have ha0 : a 0 ≠ p := fun e => absurd (hka (e.trans ha1.symm)) (by decide)
    have hb0 : b 0 ≠ p := fun e => absurd (hkb (e.trans hb1.symm)) (by decide)
    omega
  · rw [ha1, hb1]

/-- For strict complete lists of size **`n ≤ 2`**, proposer-proposing deferred acceptance is
**also strategy-proof for the receivers** (showing the size threshold `n ≥ 3` in
`not_isStable_and_strategyProof_of_le` is sharp). -/
theorem isReceiverStrategyProof_deferredAcceptance_of_le_two {n : ℕ} (hn : n ≤ 2) :
    (deferredAcceptance (n := n)).IsReceiverStrategyProof := by
  rcases (show n = 0 ∨ n = 1 ∨ n = 2 by omega) with rfl | rfl | rfl
  · intro I r; exact r.elim0
  · intro I r π; exact le_of_eq (Subsingleton.elim _ _)
  · intro I r π
    dsimp only [deferredAcceptance]
    set μ := I.deferredAcceptance
    set I' := I.updateRecvPref r π
    set μ' := I'.deferredAcceptance
    by_cases htop : I.recvRank r (μ.symm r) = 0
    · rw [htop]; exact Fin.zero_le _
    · have hrank1 : I.recvRank r (μ.symm r) = 1 := by omega
      by_cases hπ : π = I.recvPref r
      · have hI' : I' = I := instance_ext rfl (by
          funext x; by_cases hx : x = r
          · subst hx; simp [I', Instance.updateRecvPref, hπ]
          · exact Function.update_of_ne hx π I.recvPref)
        have hμ'eq : μ' = μ := by dsimp only [μ']; rw [hI']
        rw [hμ'eq]
      · have htop' : I'.recvRank r (μ.symm r) = 0 := by
          have hupd : I'.recvPref r = π := by
            change Function.update I.recvPref r π r = π
            exact Function.update_self r π I.recvPref
          change (I'.recvPref r).symm (μ.symm r) = 0
          rw [hupd]
          exact perm_fin2_top_of_ne (Ne.symm hπ) (μ.symm r) hrank1
        have hμ_stable' : I'.IsStable μ := by
          rintro p s ⟨hp, hr⟩
          by_cases hsr : s = r
          · subst hsr
            change I'.recvRank s p < I'.recvRank s (μ.symm s) at hr
            rw [htop'] at hr
            exact absurd hr (Fin.not_lt_zero _)
          · refine I.isStable_deferredAcceptance p s ⟨hp, ?_⟩
            have hs_eq : I'.recvPref s = I.recvPref s := by
              change Function.update I.recvPref r π s = I.recvPref s
              exact Function.update_of_ne hsr π I.recvPref
            change (I'.recvPref s).symm p < (I'.recvPref s).symm (μ.symm s) at hr
            rw [hs_eq] at hr
            exact hr
        let p₀ : Fin 2 := if μ.symm r = 0 then 1 else 0
        have hp₀_ne : p₀ ≠ μ.symm r := by
          dsimp only [p₀]
          split_ifs with h
          · rw [h]; decide
          · exact Ne.symm h
        have hp₀_rankR : I.recvRank r p₀ = 0 := by
          have hne : I.recvRank r p₀ ≠ I.recvRank r (μ.symm r) :=
            fun e => hp₀_ne (I.recvRank_injective r e)
          omega
        have hp₀_rankP : I.propRank p₀ (μ p₀) = 0 := by
          by_contra h0
          have h1 : I.propRank p₀ (μ p₀) = 1 := by omega
          have hμp₀_ne : μ p₀ ≠ r := fun e =>
            hp₀_ne (μ.injective (e.trans (μ.apply_symm_apply r).symm))
          have hr_rankP : I.propRank p₀ r = 0 := by
            have hne : I.propRank p₀ r ≠ I.propRank p₀ (μ p₀) :=
              fun e => hμp₀_ne (I.propRank_injective p₀ e).symm
            omega
          exact I.isStable_deferredAcceptance p₀ r
            ⟨by rw [Instance.PropPrefers, hr_rankP, h1]; decide,
             by rw [Instance.RecvPrefers, hp₀_rankR, hrank1]; decide⟩
        have hle := I'.isProposerOptimal_deferredAcceptance.2 μ hμ_stable' p₀
        have hμ'_p₀ : μ' p₀ = μ p₀ := by
          have h0 : I.propRank p₀ (μ' p₀) ≤ 0 := by
            change I'.propRank p₀ (μ' p₀) ≤ I'.propRank p₀ (μ p₀) at hle
            change I.propRank p₀ (μ' p₀) ≤ I.propRank p₀ (μ p₀) at hle
            rwa [hp₀_rankP] at hle
          exact I.propRank_injective p₀ (by rw [hp₀_rankP]; exact le_antisymm h0 (Fin.zero_le _))
        have hμ'_eq : μ' = μ := by
          ext p
          by_cases hp : p = p₀
          · rw [hp, hμ'_p₀]
          · have h1 : μ' p ≠ μ' p₀ := fun e => hp (μ'.injective e)
            have h2 : μ p ≠ μ p₀ := fun e => hp (μ.injective e)
            rw [hμ'_p₀] at h1
            omega
        rw [hμ'_eq]

/-- Dual of `isReceiverStrategyProof_deferredAcceptance_of_le_two`: for `n ≤ 2`, receiver-proposing
deferred acceptance is also strategy-proof for the proposers. -/
theorem isProposerStrategyProof_receiverDeferredAcceptance_of_le_two {n : ℕ} (hn : n ≤ 2) :
    (receiverDeferredAcceptance (n := n)).IsProposerStrategyProof := by
  intro I p π
  exact isReceiverStrategyProof_deferredAcceptance_of_le_two hn I.swap p π

end Cslib.Algorithms.Lean.StableMatching.MatchingMechanism
