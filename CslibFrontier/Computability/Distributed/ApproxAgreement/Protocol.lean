/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Distributed.ApproxAgreement.TrimmedMidpoint
public import CslibFrontier.Computability.Distributed.AsyncByzantine.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
import CslibFrontier.Computability.Distributed.AsyncByzantine.Impossibility
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Unit-interval fixed-horizon approximate Byzantine agreement

Unit-interval (`[0, 1]`), fixed-horizon (`R`-round) deterministic synchronous (`3t < n`) and
single-hop asynchronous (`5t < n`) approximate Byzantine agreement protocols
(`SolvesUnitSyncApproxAgreement`, `SolvesUnitAsyncApproxAgreement`), together with arbitrary-range
`(hi - lo) / 2 ^ R` multi-round contraction and `2 ≤ n ≤ 3t` unit-interval impossibility bounds.

These declarations formalize bounded-input, fixed-horizon milestone steps toward `#7116` and `#3261`
after the nonterminating approximation phases (Algorithm $S_0$ in Section 3, Lemma 6, p. 506;
Algorithm $A_0$ in Section 4, Lemma 8, p. 509; and the fixed-round problem variant in Section 7,
p. 516) of [Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986] — not the
unbounded-input, dynamically halting Theorems 1 and 2 of that paper. Theorems 1 and 2 of
[DolevLynchPinterStarkWeihl1986] accept arbitrary real inputs without a pre-agreed horizon `R`,
computing process-dependent halting horizons `H = ⌈log_c(δ(V) / ε)⌉` from round-1 / round-0
`reduce^{2t}` views and echoing `(v, halted)` tags (Algorithms $S$ and $A$, Figures 1–2), and use
`f_{t, t}` / `f_{2t, t}` representative means rather than the two-endpoint midpoint `midTrim`.

## Contrast with exact consensus and FLP

* **Unit-interval synchronous threshold (`exists_solvesUnitSyncApproxAgreement_iff`):** for any
  `0 < ε < 1` over an Archimedean linearly ordered field `K`, a deterministic synchronous protocol
  on `P` solves `SolvesUnitSyncApproxAgreement t R ε` for some fixed horizon `R` **if and only if**
  `Fintype.card P ≤ 1 ∨ 3 * t < Fintype.card P`. Relaxing exact agreement (`ε = 0`) to `ε < 1` on
  `[0, 1]` inputs leaves the `3t + 1` synchronous fault threshold unchanged
  (`not_solvesUnitSyncApproxAgreement`, adapting
  [Fischer, Lynch and Merritt][FischerLynchMerritt1985]), while `syncApproxProtocol` contracts any
  honest input interval `[lo, hi]` by `2 ^ R` over `R` rounds without relay trees
  (`syncApproxProtocol_abs_decision_sub_le`).
* **Unit-interval asynchronous solvability despite FLP (`exists_solvesUnitAsyncApproxAgreement`):**
  whereas exact deterministic asynchronous binary consensus (`{0, 1}` inputs, `ε = 0`) is
  impossible on `n ≥ 2` processes even against a single crash fault (`Cslib.FLP`), for **every**
  `0 < ε` and `5 * t < Fintype.card P` there is a fixed horizon `R` for which the deterministic
  single-hop round-tagged protocol `asyncApproxProtocol` terminates under fair message delivery
  (`asyncApproxProtocol_terminates`), preserves every honest input interval `[lo, hi]`
  (`asyncApproxProtocol_mem_Icc`), contracts the honest output spread to `(hi - lo) / 2 ^ R`
  (`asyncApproxProtocol_abs_sub_le`), and therefore satisfies
  `SolvesUnitAsyncApproxAgreement t ε`.
* **Asynchronous `2 ≤ n ≤ 3t` impossibility (`not_solvesUnitAsyncApproxAgreement`):** no
  deterministic asynchronous protocol achieves `SolvesUnitAsyncApproxAgreement t ε` with `ε < 1`
  when `2 ≤ Fintype.card P ≤ 3 * t`, proved via `AsyncByzantine.Protocol.replay_subset_mTr`. Note
  that Theorem 2 of [Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986]
  likewise requires `5t < n` (`n ≥ 5t + 1`); closing the asynchronous resilience gap `3t < n ≤ 5t`
  via multi-hop witness techniques beyond [DolevLynchPinterStarkWeihl1986] (see Section 7, p. 515)
  is tracked separately under `#3261`.

## Main definitions

* `Cslib.Distributed.ApproxAgreement.SyncProtocol`: deterministic synchronous protocol over a
  value domain `V`.
* `Cslib.Distributed.ApproxAgreement.SyncProtocol.SolvesUnitSyncApproxAgreement`: unit-interval
  (`x k ∈ [0, 1]`), fixed-horizon (`R`-round) synchronous `ε`-approximate Byzantine agreement.
* `Cslib.Distributed.ApproxAgreement.syncApproxProtocol`: fixed-horizon synchronous iterative
  `multisetMidTrim` protocol (`3 * t < Fintype.card P`), after Algorithm $S_0$ of
  [DolevLynchPinterStarkWeihl1986].
* `Cslib.Distributed.ApproxAgreement.AsyncProtocol`: deterministic multi-input asynchronous
  Byzantine protocol reusing `Cslib.Distributed.AsyncByzantine`'s authenticated LTS configurations.
* `Cslib.Distributed.ApproxAgreement.AsyncProtocol.SolvesUnitAsyncApproxAgreement`: unit-interval
  (`x k ∈ [0, 1]`) asynchronous `ε`-approximate Byzantine agreement under fair delivery.
* `Cslib.Distributed.ApproxAgreement.RoundMsg`,
  `Cslib.Distributed.ApproxAgreement.AsyncApproxState`,
  `Cslib.Distributed.ApproxAgreement.asyncApproxProtocol`: fixed-horizon (`R`-round) single-hop
  round-tagged asynchronous approximate agreement protocol (`5 * t < Fintype.card P`), after
  Algorithm $A_0$ of [DolevLynchPinterStarkWeihl1986].

## Main results

* `Cslib.Distributed.ApproxAgreement.syncApproxProtocol_decision_mem_Icc`,
  `Cslib.Distributed.ApproxAgreement.syncApproxProtocol_abs_decision_sub_le`: arbitrary-interval
  convex-hull validity and `(hi - lo) / 2 ^ R` contraction of `syncApproxProtocol` for
  `3 * t < Fintype.card P`.
* `Cslib.Distributed.ApproxAgreement.SyncProtocol.not_solvesUnitSyncApproxAgreement`: unit-interval
  synchronous impossibility for `2 ≤ Fintype.card P ≤ 3 * t` and `ε < 1`.
* `Cslib.Distributed.ApproxAgreement.exists_solvesUnitSyncApproxAgreement_iff`: sharp threshold
  `Fintype.card P ≤ 1 ∨ 3 * t < Fintype.card P` for `SolvesUnitSyncApproxAgreement` (`0 < ε < 1`).
* `Cslib.Distributed.ApproxAgreement.asyncApproxProtocol_terminates`,
  `Cslib.Distributed.ApproxAgreement.asyncApproxProtocol_mem_Icc`,
  `Cslib.Distributed.ApproxAgreement.asyncApproxProtocol_abs_sub_le`: fair-delivery termination,
  arbitrary-interval convex-hull validity, and `(hi - lo) / 2 ^ R` contraction of
  `asyncApproxProtocol` for `5 * t < Fintype.card P`.
* `Cslib.Distributed.ApproxAgreement.exists_solvesUnitAsyncApproxAgreement`: solvability of
  `SolvesUnitAsyncApproxAgreement t ε` for `0 < ε` and
  `Fintype.card P ≤ 1 ∨ 5 * t < Fintype.card P`.
* `Cslib.Distributed.ApproxAgreement.AsyncProtocol.not_solvesUnitAsyncApproxAgreement`:
  unit-interval asynchronous impossibility for `2 ≤ Fintype.card P ≤ 3 * t` and `ε < 1`.

## References

* [D. Dolev, N. A. Lynch, S. S. Pinter, E. W. Stark, W. E. Weihl, *Reaching approximate agreement
  in the presence of faults*][DolevLynchPinterStarkWeihl1986]
* [M. J. Fischer, N. A. Lynch, M. Merritt, *Easy impossibility proofs for distributed consensus
  problems*][FischerLynchMerritt1985]
-/

public section

namespace Cslib.Distributed.ApproxAgreement

open Cslib Cslib.ωSequence Cslib.Distributed.AsyncByzantine

/-! ### Shared multi-round contraction engine and 3-partition helper -/

section SharedEngine

/-- Inductive multi-round contraction engine shared by the synchronous (`m = |P|`, `3t < |P|`) and
asynchronous (`m = |P| - t`, `5t < |P|`) protocols: if round-`0` honest proposals lie in `[lo, hi]`
and each round-`(r + 1)` honest proposal is `multisetMidTrim t (S.val.map f)` over a sender set `S`
of size at least `m` (with `|P| + 3t < 2m`) agreeing with round-`r` honest proposals on `S \ F`,
then at every round `r` all honest proposals lie in a subinterval `[lo_r, hi_r] ⊆ [lo, hi]` of
width at most `(hi - lo) / 2 ^ r`. -/
private lemma exists_Icc_of_roundMidTrim {P K : Type*} [Fintype P]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {F : Finset P} {t m : ℕ} (hF : F.card ≤ t) (hm : Fintype.card P + 3 * t < 2 * m)
    {prop : ℕ → P → Option K} {lo hi : K} (hlh : lo ≤ hi)
    (hbase : ∀ p ∉ F, ∀ v, prop 0 p = some v → v ∈ Set.Icc lo hi)
    (hstep : ∀ r, ∀ p ∉ F, ∀ w, prop (r + 1) p = some w →
      ∃ (S : Finset P) (f : P → K), m ≤ S.card ∧ w = multisetMidTrim t (S.val.map f) ∧
        ∀ q ∈ S, q ∉ F → ∃ v, prop r q = some v ∧ f q = v) :
    ∀ r, ∃ lo_r hi_r : K,
      lo ≤ lo_r ∧ lo_r ≤ hi_r ∧ hi_r ≤ hi ∧
      hi_r - lo_r ≤ (hi - lo) / 2 ^ r ∧
      ∀ p ∉ F, ∀ v, prop r p = some v → v ∈ Set.Icc lo_r hi_r := by
  classical
  intro r
  induction r with
  | zero =>
    refine ⟨lo, hi, le_rfl, hlh, le_rfl, ?_, hbase⟩
    rw [pow_zero, div_one]
  | succ r ih =>
    obtain ⟨lo_r, hi_r, hlo_r, hlh_r, hhi_r, hwidth_r, hmem_r⟩ := ih
    let H : Finset P := Finset.univ.filter fun p => p ∉ F ∧ (prop (r + 1) p).isSome
    by_cases hH : H.Nonempty
    · let wOf : P → K := fun p => (prop (r + 1) p).getD lo_r
      let val : P → K := fun q => (prop r q).getD lo_r
      have hval_mem : ∀ q ∉ F, val q ∈ Set.Icc lo_r hi_r := by
        intro q hqF
        dsimp only [val]
        cases hq : prop r q with
        | none => exact ⟨le_rfl, hlh_r⟩
        | some v => exact hmem_r q hqF v hq
      have hw_spec : ∀ p ∈ H, ∃ (S : Finset P) (f : P → K),
          m ≤ S.card ∧ wOf p = multisetMidTrim t (S.val.map f) ∧
          ∀ q ∈ S, q ∉ F → f q = val q := by
        intro p hp
        have hp' : p ∉ F ∧ (prop (r + 1) p).isSome := (Finset.mem_filter.mp hp).2
        obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp hp'.2
        obtain ⟨S, f, hScard, hweq, hf⟩ := hstep r p hp'.1 w hw
        refine ⟨S, f, hScard, ?_, ?_⟩
        · simp only [wOf, hw, Option.getD_some, hweq]
        · intro q hqS hqF
          obtain ⟨v, hv, hfq⟩ := hf q hqS hqF
          simp only [val, hv, Option.getD_some, hfq]
      have hw_mem : ∀ p ∈ H, wOf p ∈ Set.Icc lo_r hi_r := by
        intro p hp
        obtain ⟨S, f, hScard, hweq, hf⟩ := hw_spec p hp
        have hSu : S.card ≤ Fintype.card P := Finset.card_le_univ S
        rw [hweq]
        exact multisetMidTrim_map_mem_Icc hF (by omega) fun q hqS hqF => by
          rw [hf q hqS hqF]
          exact hval_mem q hqF
      have hw_diff : ∀ p₁ ∈ H, ∀ p₂ ∈ H, |wOf p₁ - wOf p₂| ≤ (hi_r - lo_r) / 2 := by
        intro p₁ hp₁ p₂ hp₂
        obtain ⟨S₁, f₁, hS₁, hw₁, hf₁⟩ := hw_spec p₁ hp₁
        obtain ⟨S₂, f₂, hS₂, hw₂, hf₂⟩ := hw_spec p₂ hp₂
        rw [hw₁, hw₂]
        exact abs_multisetMidTrim_map_sub_le hF (by omega) hval_mem hf₁ hf₂
      let lo' := H.inf' hH wOf
      let hi' := H.sup' hH wOf
      have ⟨p₀, hp₀⟩ := hH
      have hlo'_ge : lo_r ≤ lo' := (Finset.le_inf'_iff hH wOf).mpr fun p hp => (hw_mem p hp).1
      have hhi'_le : hi' ≤ hi_r := (Finset.sup'_le_iff hH wOf).mpr fun p hp => (hw_mem p hp).2
      have hlh' : lo' ≤ hi' :=
        (Finset.inf'_le wOf hp₀).trans (Finset.le_sup' wOf hp₀)
      obtain ⟨p_min, hp_min, hmin_eq⟩ := Finset.exists_mem_eq_inf' hH wOf
      obtain ⟨p_max, hp_max, hmax_eq⟩ := Finset.exists_mem_eq_sup' hH wOf
      have hsub_le : hi' - lo' ≤ (hi_r - lo_r) / 2 := by
        have habs := hw_diff p_max hp_max p_min hp_min
        have hle_abs : wOf p_max - wOf p_min ≤ |wOf p_max - wOf p_min| := le_abs_self _
        change H.sup' hH wOf - H.inf' hH wOf ≤ _
        rw [hmax_eq, hmin_eq]
        exact hle_abs.trans habs
      have hwidth' : hi' - lo' ≤ (hi - lo) / 2 ^ (r + 1) := by
        have hdiv : (hi_r - lo_r) / 2 ≤ ((hi - lo) / 2 ^ r) / 2 :=
          div_le_div_of_nonneg_right hwidth_r (by positivity)
        rw [div_div, ← pow_succ] at hdiv
        exact hsub_le.trans hdiv
      refine ⟨lo', hi', hlo_r.trans hlo'_ge, hlh', hhi'_le.trans hhi_r, hwidth', ?_⟩
      intro p hpF w hw
      have hpH : p ∈ H := by
        simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hpF, by simp only [hw, Option.isSome_some]⟩
      have hw_eq : w = wOf p := by simp only [wOf, hw, Option.getD_some]
      rw [hw_eq]
      exact ⟨Finset.inf'_le wOf hpH, Finset.le_sup' wOf hpH⟩
    · refine ⟨lo_r, lo_r, hlo_r, le_rfl, hlh_r.trans hhi_r, ?_, ?_⟩
      · rw [sub_self]
        have h0 : 0 ≤ hi - lo := sub_nonneg.mpr hlh
        positivity
      · intro p hpF w hw
        exfalso
        apply hH
        refine ⟨p, ?_⟩
        simp only [H, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hpF, by simp only [hw, Option.isSome_some]⟩

/-- Given `[Archimedean K]` and `0 < ε`, some round count `R` satisfies `(1 : K) / 2 ^ R ≤ ε`. -/
private lemma exists_one_div_two_pow_le {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [Archimedean K] {ε : K} (hε : 0 < ε) :
    ∃ R : ℕ, (1 : K) / 2 ^ R ≤ ε := by
  obtain ⟨R, hR⟩ := exists_nat_gt (1 / ε)
  refine ⟨R, le_of_lt ?_⟩
  have hpow : (R : K) < (2 : K) ^ R := by exact_mod_cast R.lt_two_pow_self
  have hlt : 1 / ε < (2 : K) ^ R := hR.trans hpow
  have h2pos : (0 : K) < (2 : K) ^ R := by positivity
  rw [div_lt_iff₀ h2pos]
  rwa [div_lt_iff₀ hε, mul_comm] at hlt

/-- Split `P` (`2 ≤ |P| ≤ 3 * t`) into three residue-modulo-`3` groups of size at most `t` each,
with designated witnesses in groups `0` and `2` (group `1` may be empty when `|P| = 2`). -/
private lemma exists_three_group_fn {P : Type*} [Fintype P] {t : ℕ}
    (h2 : 2 ≤ Fintype.card P) (h3 : Fintype.card P ≤ 3 * t) :
    ∃ (g : P → Fin 3) (a c : P),
      (∀ k : Fin 3, (Finset.univ.filter fun i => g i = k).card ≤ t) ∧
      g a = 0 ∧ g c = 2 := by
  classical
  let e := Fintype.equivFin P
  let g : P → Fin 3 := fun i => ⟨2 * (e i : ℕ) % 3, Nat.mod_lt _ (by omega)⟩
  refine ⟨g, e.symm ⟨0, by omega⟩, e.symm ⟨1, by omega⟩, fun k => ?_, ?_, ?_⟩
  · calc (Finset.univ.filter fun i => g i = k).card
        ≤ (Finset.range t).card := Finset.card_le_card_of_injOn (fun i => (e i : ℕ) / 3) ?_ ?_
      _ = t := Finset.card_range t
    · intro i _
      have hi := (e i).isLt
      simp only [Finset.coe_range, Set.mem_Iio]
      omega
    · intro i hi j hj hij
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
      apply e.injective
      have hi' := congrArg Fin.val hi
      have hj' := congrArg Fin.val hj
      simp only [g] at hi' hj' hij
      ext
      omega
  · simp only [g, Equiv.apply_symm_apply]
    rfl
  · simp only [g, Equiv.apply_symm_apply]
    rfl

end SharedEngine

/-! ### Part 1: Synchronous approximate Byzantine agreement (`3 * t < |P|`) -/

/-- A deterministic synchronous message-passing protocol on the complete graph of processes `P`
with inputs and outputs in `V` (extending `Cslib.Distributed.Byzantine.Protocol` from `Bool` to an
arbitrary value domain `V`). -/
structure SyncProtocol (P V State Msg : Type*) where
  /-- Initial state of process `i` on input `v : V`. -/
  init : P → V → State
  /-- `send r i s j`: message sent by process `i` in state `s` to `j` in round `r + 1`. -/
  send : ℕ → P → State → P → Msg
  /-- `update r i s m`: state of `i` after round `r + 1` upon receiving `m j` from each `j`. -/
  update : ℕ → P → State → (P → Msg) → State
  /-- Output value read off from state `s` of process `i`. -/
  output : P → State → V

namespace SyncProtocol

variable {P V S M : Type*} [DecidableEq P] (π : SyncProtocol P V S M)

/-- State of process `i` after `r` synchronous rounds on input vector `x` when processes in `F` are
faulty and faulty `j` sends `adv r j i` to `i` in round `r + 1`. -/
@[expose] def state (F : Finset P) (adv : ℕ → P → P → M) (x : P → V) : ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (state F adv x r i)
      (fun j => if j ∈ F then adv r j i else π.send r j (state F adv x r j) i)

/-- Output decision of process `i` after `R` rounds. -/
@[expose] def decision (F : Finset P) (adv : ℕ → P → P → M) (x : P → V) (R : ℕ) (i : P) : V :=
  π.output i (π.state F adv x R i)

/-- State after `r` rounds against a *rushing* adversary `strat` that inspects the global state
after round `r` before choosing faulty round-`(r + 1)` messages. -/
@[expose] def adaptiveState (F : Finset P) (strat : ℕ → (P → S) → P → P → M) (x : P → V) :
    ℕ → P → S
  | 0, i => π.init i (x i)
  | r + 1, i => π.update r i (adaptiveState F strat x r i)
      (fun j => if j ∈ F then strat r (adaptiveState F strat x r) j i
        else π.send r j (adaptiveState F strat x r j) i)

/-- A rushing adversary in a deterministic synchronous run is equivalent to the fixed message table
of messages it sends along that run. -/
theorem adaptiveState_eq_state (F : Finset P) (strat : ℕ → (P → S) → P → P → M) (x : P → V) :
    ∀ r, π.adaptiveState F strat x r =
      π.state F (fun r j i => strat r (π.adaptiveState F strat x r) j i) x r
  | 0 => rfl
  | r + 1 => by
    funext i
    simp only [adaptiveState, state]
    rw [← adaptiveState_eq_state F strat x r]

omit [DecidableEq P] in
/-- Run of `π` on a covering network `(label, input, nbr)`. -/
@[expose] def coverState {N : Type*} (label : N → P) (input : N → V) (nbr : N → P → N) :
    ℕ → N → S
  | 0, a => π.init (label a) (input a)
  | r + 1, a => π.update r (label a) (coverState label input nbr r a)
      (fun j => π.send r j (coverState label input nbr r (nbr a j)) (label a))

/-- **Covering lemma** for value-domain synchronous protocols
([Fischer, Lynch and Merritt][FischerLynchMerritt1985]). -/
theorem state_eq_coverState {N : Type*} (label : N → P) (input : N → V) (nbr : N → P → N)
    (F : Finset P) (adv : ℕ → P → P → M) (x : P → V) (e : P → N)
    (hlabel : ∀ i ∉ F, label (e i) = i) (hinput : ∀ i ∉ F, input (e i) = x i)
    (hnbr : ∀ i ∉ F, ∀ j ∉ F, nbr (e i) j = e j)
    (hadv : ∀ r, ∀ i ∉ F, ∀ j ∈ F,
      adv r j i = π.send r j (π.coverState label input nbr r (nbr (e i) j)) i) :
    ∀ r, ∀ i ∉ F, π.state F adv x r i = π.coverState label input nbr r (e i)
  | 0, i, hi => by simp only [state, coverState, hlabel i hi, hinput i hi]
  | r + 1, i, hi => by
    simp only [state, coverState, hlabel i hi]
    congr 1
    · exact state_eq_coverState label input nbr F adv x e hlabel hinput hnbr hadv r i hi
    · funext j
      split_ifs with hj
      · exact hadv r i hi j hj
      · rw [state_eq_coverState label input nbr F adv x e hlabel hinput hnbr hadv r j hj,
          hnbr i hi j hj]

/-- Zero-communication protocol in which each process outputs its own input. -/
@[expose] def ownInput (P V : Type*) : SyncProtocol P V V PUnit where
  init _ v := v
  send _ _ _ _ := .unit
  update _ _ s _ := s
  output _ s := s

section Spec

variable {K : Type*} [Field K] [LinearOrder K] (πK : SyncProtocol P K S M)

/-- Unit-interval, fixed-horizon synchronous `ε`-approximate Byzantine agreement (a
`[0, 1]`-bounded, fixed-round milestone step toward `#7116`, after Section 3 and Section 7, p. 516
of [Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986], rather than that
paper's unbounded-input, dynamically halting Theorem 1): whenever `F.card ≤ t` and all correct
inputs lie in `[0, 1]`, after the fixed round horizon `R`:
* **validity** (convex hull): for every closed interval `[lo, hi]` containing all correct inputs,
  every correct process's decision lies in `[lo, hi]`;
* **agreement** (`ε`-closeness): any two correct processes' decisions differ by at most `ε`. -/
structure SolvesUnitSyncApproxAgreement (t R : ℕ) (ε : K) : Prop where
  /-- Convex-hull validity: decisions remain within every `[lo, hi]` containing correct inputs. -/
  validity : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (x : P → K) (lo hi : K),
    (∀ k ∉ F, x k ∈ Set.Icc 0 1) → (∀ k ∉ F, x k ∈ Set.Icc lo hi) →
    ∀ i ∉ F, πK.decision F adv x R i ∈ Set.Icc lo hi
  /-- Approximate agreement: correct decisions lie within `ε` of each other. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ (adv : ℕ → P → P → M) (x : P → K),
    (∀ k ∉ F, x k ∈ Set.Icc 0 1) →
    ∀ i ∉ F, ∀ j ∉ F, |πK.decision F adv x R i - πK.decision F adv x R j| ≤ ε

theorem SolvesUnitSyncApproxAgreement.mono {πK : SyncProtocol P K S M} {t t' R : ℕ} {ε ε' : K}
    (h : πK.SolvesUnitSyncApproxAgreement t R ε) (ht : t' ≤ t) (hε : ε ≤ ε') :
    πK.SolvesUnitSyncApproxAgreement t' R ε' where
  validity F hF := h.validity F (hF.trans ht)
  agreement F hF adv x hx i hi j hj := (h.agreement F (hF.trans ht) adv x hx i hi j hj).trans hε

/-- Unit-interval fixed-horizon synchronous approximate agreement guarantees also hold against
rushing adversaries. -/
theorem SolvesUnitSyncApproxAgreement.adaptive {πK : SyncProtocol P K S M} {t R : ℕ} {ε : K}
    (h : πK.SolvesUnitSyncApproxAgreement t R ε) {F : Finset P} (hF : F.card ≤ t)
    (strat : ℕ → (P → S) → P → P → M) (x : P → K) (hx : ∀ k ∉ F, x k ∈ Set.Icc 0 1) :
    (∀ lo hi, (∀ k ∉ F, x k ∈ Set.Icc lo hi) →
      ∀ i ∉ F, πK.output i (πK.adaptiveState F strat x R i) ∈ Set.Icc lo hi) ∧
    (∀ i ∉ F, ∀ j ∉ F,
      |πK.output i (πK.adaptiveState F strat x R i) -
        πK.output j (πK.adaptiveState F strat x R j)| ≤ ε) := by
  rw [πK.adaptiveState_eq_state F strat x R]
  exact ⟨fun lo hi hIcc => h.validity F hF _ x lo hi hx hIcc, h.agreement F hF _ x hx⟩

theorem solvesUnitSyncApproxAgreement_ownInput [IsStrictOrderedRing K] [Subsingleton P]
    (t R : ℕ) {ε : K} (hε : 0 ≤ ε) :
    (ownInput P K).SolvesUnitSyncApproxAgreement t R ε := by
  have hstate : ∀ F adv (x : P → K) r i, (ownInput P K).state F adv x r i = x i := by
    intro F adv x r i
    induction r with
    | zero => rfl
    | succ _ ih => exact ih
  refine ⟨fun F _ adv x lo hi _ hIcc i hi => ?_, fun F _ adv x _ i _ j _ => ?_⟩
  · rw [decision, hstate]
    exact hIcc i hi
  · rw [Subsingleton.elim i j, sub_self, abs_zero]
    exact hε

/-- **Covering impossibility for unit-interval synchronous `ε`-approximate Byzantine agreement**
(`ε < 1`): if `P` splits into three groups of size at most `t` with witnesses `a` in group `0` and
`c` in group `2`, no protocol achieves `SolvesUnitSyncApproxAgreement t R ε` for `ε < 1` (in
particular for `ε < 1 / 2`), adapting [Fischer, Lynch and Merritt][FischerLynchMerritt1985]. -/
theorem not_solvesUnitSyncApproxAgreement_of_partition [Fintype P] [IsStrictOrderedRing K]
    {t R : ℕ} {ε : K} (hε : ε < 1) (g : P → Fin 3)
    (hcard : ∀ k : Fin 3, (Finset.univ.filter fun i => g i = k).card ≤ t)
    {a c : P} (ha : g a = 0) (hc : g c = 2) :
    ¬ πK.SolvesUnitSyncApproxAgreement t R ε := by
  intro h
  let bitVal : Bool → K := fun b => if b then 1 else 0
  have hbit_Icc : ∀ b : Bool, bitVal b ∈ Set.Icc (0 : K) 1 := by
    intro b; cases b <;> simp only [bitVal, Bool.false_eq_true, ↓reduceIte, Set.mem_Icc,
      le_rfl, zero_le_one, and_self]
  let cross : P → P → Bool := fun i j => decide ((g i = 0 ∧ g j = 2) ∨ (g i = 2 ∧ g j = 0))
  let nbr : P × Bool → P → P × Bool := fun p j => (j, p.2 ^^ cross p.1 j)
  let cover := πK.coverState Prod.fst (bitVal ∘ Prod.snd) nbr
  let grp : Fin 3 → Finset P := fun k => Finset.univ.filter fun i => g i = k
  let adv : (P → Bool) → ℕ → P → P → M := fun σ r j i =>
    πK.send r j (cover r (nbr (i, σ i) j)) i
  have hmem : ∀ k j, j ∉ grp k ↔ g j ≠ k := by
    intro k j; simp only [grp, Finset.mem_filter, Finset.mem_univ, true_and]
  have key : ∀ (k : Fin 3) (σ : P → Bool),
      (∀ i j, g i ≠ k → g j ≠ k → (σ i ^^ cross i j) = σ j) →
      ∀ i, g i ≠ k →
        πK.decision (grp k) (adv σ) (bitVal ∘ σ) R i = πK.output i (cover R (i, σ i)) := by
    intro k σ hσ i hi
    unfold decision
    rw [state_eq_coverState πK Prod.fst (bitVal ∘ Prod.snd) nbr (grp k) (adv σ) (bitVal ∘ σ)
      (fun i => (i, σ i)) (fun _ _ => rfl) (fun _ _ => rfl) ?_ (fun _ _ _ _ _ => rfl) R i
      ((hmem k i).mpr hi)]
    intro i' hi' j' hj'
    simp only [nbr, Prod.mk.injEq, true_and]
    exact hσ i' j' ((hmem k i').mp hi') ((hmem k j').mp hj')
  have hc₀ : g c ≠ 0 := by rw [hc]; decide
  have ha₂ : g a ≠ 2 := by rw [ha]; decide
  -- Group `0` faulty, all inputs `0`: convex hull `[0, 0]` forces `C₀` to output `0`.
  have h₀_mem := h.validity (grp 0) (hcard 0) (adv fun _ => false) (fun _ => 0) 0 0
    (fun _ _ => ⟨le_rfl, zero_le_one⟩) (fun _ _ => ⟨le_rfl, le_rfl⟩) c ((hmem 0 c).mpr hc₀)
  have h₀ : πK.output c (cover R (c, false)) = 0 := by
    have hkey := key 0 (fun _ => false) (fun i j hi hj => by
      simp only [cross, hi, hj, false_and, and_false, or_self, decide_false, Bool.xor_false]) c hc₀
    have hEq : (bitVal ∘ fun _ : P => false) = fun _ => (0 : K) := rfl
    rw [hEq] at hkey
    rw [hkey] at h₀_mem
    exact le_antisymm h₀_mem.2 h₀_mem.1
  -- Group `2` faulty, all inputs `1`: convex hull `[1, 1]` forces `A₁` to output `1`.
  have h₂_mem := h.validity (grp 2) (hcard 2) (adv fun _ => true) (fun _ => 1) 1 1
    (fun _ _ => ⟨zero_le_one, le_rfl⟩) (fun _ _ => ⟨le_rfl, le_rfl⟩) a ((hmem 2 a).mpr ha₂)
  have h₂ : πK.output a (cover R (a, true)) = 1 := by
    have hkey := key 2 (fun _ => true) (fun i j hi hj => by
      simp only [cross, hi, hj, false_and, and_false, or_self, decide_false, Bool.xor_false]) a ha₂
    have hEq : (bitVal ∘ fun _ : P => true) = fun _ => (1 : K) := rfl
    rw [hEq] at hkey
    rw [hkey] at h₂_mem
    exact le_antisymm h₂_mem.2 h₂_mem.1
  -- Group `1` faulty, group `0` input `1`, group `2` input `0`: `A₁` and `C₀` disagree by `1`.
  have hfin : ∀ u v : Fin 3, u ≠ 1 → v ≠ 1 →
      (decide (u = 0) ^^ decide ((u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0))) = decide (v = 0) := by
    decide
  let σ₁ : P → Bool := fun i => decide (g i = 0)
  have h₁ := h.agreement (grp 1) (hcard 1) (adv σ₁) (bitVal ∘ σ₁)
    (fun k _ => hbit_Icc (σ₁ k))
    a ((hmem 1 a).mpr (by rw [ha]; decide)) c ((hmem 1 c).mpr (by rw [hc]; decide))
  rw [key 1 σ₁ (fun i j hi hj => hfin _ _ hi hj) a (by rw [ha]; decide),
    key 1 σ₁ (fun i j hi hj => hfin _ _ hi hj) c (by rw [hc]; decide)] at h₁
  have hσ_a : σ₁ a = true := by simp only [σ₁, ha, decide_true]
  have hσ_c : σ₁ c = false := by
    have h20 : ((2 : Fin 3) = 0) ↔ False := by decide
    simp only [σ₁, hc, h20, decide_false]
  rw [hσ_a, hσ_c, h₂, h₀, sub_zero, abs_one] at h₁
  linarith

/-- **No unit-interval synchronous `ε`-approximate Byzantine agreement for `2 ≤ |P| ≤ 3 * t` and
`ε < 1`:** adapts the `3t + 1` covering lower bound proved in
[Fischer, Lynch and Merritt][FischerLynchMerritt1985] (and cited in Section 7, p. 515 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986]) to
`SolvesUnitSyncApproxAgreement` (including `|P| = 2` via an empty middle group). -/
theorem not_solvesUnitSyncApproxAgreement [Fintype P] [IsStrictOrderedRing K]
    {t R : ℕ} {ε : K} (h2 : 2 ≤ Fintype.card P) (h3 : Fintype.card P ≤ 3 * t) (hε : ε < 1) :
    ¬ πK.SolvesUnitSyncApproxAgreement t R ε := by
  obtain ⟨g, a, c, hcard, ha, hc⟩ := exists_three_group_fn h2 h3
  exact πK.not_solvesUnitSyncApproxAgreement_of_partition hε g hcard ha hc

end Spec

end SyncProtocol

/-- **Fixed-horizon synchronous iterative trimmed-midpoint protocol** (step after the nonterminating
Algorithm $S_0$ in Section 3, p. 506 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986], using `multisetMidTrim t`
in place of `f_{t, t}` and evaluated at a caller-chosen horizon `R` rather than Algorithm $S$'s
input-dependent halting tag): in each round every process broadcasts its current estimate, collects
the `|P|` values received, and moves to `multisetMidTrim t`. -/
@[expose] def syncApproxProtocol (P K : Type*) [Fintype P] [Field K] [LinearOrder K] (t : ℕ) :
    SyncProtocol P K K K where
  init _ v := v
  send _ _ s _ := s
  update _ _ _ m := multisetMidTrim t (Finset.univ.val.map m)
  output _ s := s

section SyncTheorems

variable {P K : Type*} [Fintype P] [DecidableEq P]
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]

private lemma syncApprox_exists_Icc {t : ℕ} (h3t : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) (adv : ℕ → P → P → K) (x : P → K)
    {lo hi : K} (hlh : lo ≤ hi) (hx : ∀ k ∉ F, x k ∈ Set.Icc lo hi) (R : ℕ) :
    ∃ lo_R hi_R : K,
      lo ≤ lo_R ∧ lo_R ≤ hi_R ∧ hi_R ≤ hi ∧
      hi_R - lo_R ≤ (hi - lo) / 2 ^ R ∧
      ∀ i ∉ F, (syncApproxProtocol P K t).decision F adv x R i ∈ Set.Icc lo_R hi_R := by
  let prop : ℕ → P → Option K := fun r p =>
    some ((syncApproxProtocol P K t).state F adv x r p)
  obtain ⟨lo_R, hi_R, hlo, hlh_R, hhi, hw, hmem⟩ :=
    exists_Icc_of_roundMidTrim (P := P) (K := K) (F := F) (t := t) (m := Fintype.card P)
      hF (by omega) (prop := prop) hlh
      (fun p hpF v hv => by
        simp only [prop, SyncProtocol.state, syncApproxProtocol, Option.some.injEq] at hv
        exact hv ▸ hx p hpF)
      (fun r p _ w hw => by
        simp only [prop, SyncProtocol.state, syncApproxProtocol, Option.some.injEq] at hw
        refine ⟨Finset.univ,
          fun j => if j ∈ F then adv r j p else (syncApproxProtocol P K t).state F adv x r j,
          by simp only [Finset.card_univ, le_rfl], hw.symm, fun q _ hqF => ?_⟩
        exact ⟨_, rfl, by simp only [hqF, ↓reduceIte]⟩)
      R
  exact ⟨lo_R, hi_R, hlo, hlh_R, hhi, hw, fun i hiF => hmem i hiF _ rfl⟩

/-- **Synchronous convex-hull validity:** for `3 * t < Fintype.card P`, if all correct inputs lie
in `[lo, hi]`, then after every round `R` every correct process's output in `syncApproxProtocol`
lies in `[lo, hi]`. -/
theorem syncApproxProtocol_decision_mem_Icc {t : ℕ} (h3t : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) (adv : ℕ → P → P → K) (x : P → K)
    {lo hi : K} (hx : ∀ k ∉ F, x k ∈ Set.Icc lo hi) (R : ℕ)
    {i : P} (hiF : i ∉ F) :
    (syncApproxProtocol P K t).decision F adv x R i ∈ Set.Icc lo hi := by
  have hlh : lo ≤ hi := (hx i hiF).1.trans (hx i hiF).2
  obtain ⟨lo_R, hi_R, hlo, _, hhi, _, hmem⟩ := syncApprox_exists_Icc h3t hF adv x hlh hx R
  exact ⟨hlo.trans (hmem i hiF).1, (hmem i hiF).2.trans hhi⟩

/-- **Synchronous multi-round contraction:** for `3 * t < Fintype.card P`, if all correct inputs
lie in `[lo, hi]`, then after `R` rounds any two correct processes' outputs in
`syncApproxProtocol` differ by at most `(hi - lo) / 2 ^ R`. -/
theorem syncApproxProtocol_abs_decision_sub_le {t : ℕ} (h3t : 3 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) (adv : ℕ → P → P → K) (x : P → K)
    {lo hi : K} (hx : ∀ k ∉ F, x k ∈ Set.Icc lo hi) (R : ℕ)
    {i j : P} (hiF : i ∉ F) (hjF : j ∉ F) :
    |(syncApproxProtocol P K t).decision F adv x R i -
      (syncApproxProtocol P K t).decision F adv x R j| ≤ (hi - lo) / 2 ^ R := by
  have hlh : lo ≤ hi := (hx i hiF).1.trans (hx i hiF).2
  obtain ⟨lo_R, hi_R, _, _, _, hw, hmem⟩ := syncApprox_exists_Icc h3t hF adv x hlh hx R
  obtain ⟨hi_lo, hi_hi⟩ := hmem i hiF
  obtain ⟨hj_lo, hj_hi⟩ := hmem j hjF
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Unit-interval, fixed-horizon step toward `#7116` (after Section 3 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986]): when
`3 * t < Fintype.card P` and `(1 : K) / 2 ^ R ≤ ε`, `syncApproxProtocol` achieves
`SolvesUnitSyncApproxAgreement t R ε`. -/
theorem solvesUnitSyncApproxAgreement_syncApprox {t R : ℕ} {ε : K}
    (h3t : 3 * t < Fintype.card P) (hR : (1 : K) / 2 ^ R ≤ ε) :
    (syncApproxProtocol P K t).SolvesUnitSyncApproxAgreement t R ε where
  validity _ hF adv x _ _ _ hIcc _ hiF :=
    syncApproxProtocol_decision_mem_Icc h3t hF adv x hIcc R hiF
  agreement _ hF adv x hx _ hiF _ hjF := by
    have hsub := syncApproxProtocol_abs_decision_sub_le h3t hF adv x hx R hiF hjF
    rw [sub_zero] at hsub
    exact hsub.trans hR

/-- **Sharp threshold for unit-interval, fixed-horizon synchronous approximate Byzantine agreement**
(milestone step toward `#7116`, after Section 3 and Section 7, p. 515 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986], rather than that paper's
unbounded-input, dynamically halting Theorem 1): over any Archimedean linearly ordered field `K` and
accuracy `0 < ε < 1`, a deterministic synchronous protocol on `P` solving
`SolvesUnitSyncApproxAgreement t R ε` for some fixed horizon `R` exists **if and only if**
`Fintype.card P ≤ 1 ∨ 3 * t < Fintype.card P`. The degenerate `|P| ≤ 1` branch is witnessed by
`SyncProtocol.ownInput`; `3 * t < |P|` sufficiency is witnessed by `syncApproxProtocol`; and
necessity for `2 ≤ |P| ≤ 3 * t` follows from `SyncProtocol.not_solvesUnitSyncApproxAgreement`
adapting [Fischer, Lynch and Merritt][FischerLynchMerritt1985]. -/
theorem exists_solvesUnitSyncApproxAgreement_iff.{u} (P : Type*) (K : Type u)
    [Fintype P] [DecidableEq P]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
    (t : ℕ) {ε : K} (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∃ (S M : Type u) (π : SyncProtocol P K S M) (R : ℕ),
      π.SolvesUnitSyncApproxAgreement t R ε) ↔
      Fintype.card P ≤ 1 ∨ 3 * t < Fintype.card P := by
  constructor
  · rintro ⟨S, M, π, R, hsol⟩
    by_contra! h
    exact π.not_solvesUnitSyncApproxAgreement (by omega) h.2 hε1 hsol
  · rintro (h1 | h3t)
    · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp h1
      exact ⟨K, PUnit.{u + 1}, SyncProtocol.ownInput P K, 0,
        SyncProtocol.solvesUnitSyncApproxAgreement_ownInput t 0 hε0.le⟩
    · obtain ⟨R, hR⟩ := exists_one_div_two_pow_le hε0
      exact ⟨K, K, syncApproxProtocol P K t, R, solvesUnitSyncApproxAgreement_syncApprox h3t hR⟩

end SyncTheorems

/-! ### Part 2: Asynchronous approximate Byzantine agreement (`5 * t < |P|`) -/

/-- A deterministic multi-party asynchronous authenticated message-passing protocol on `P` with
inputs and write-once outputs in `V`, local states `S`, and message payloads `M`. Global states
(`AsyncByzantine.State`), authenticated envelopes (`AsyncByzantine.Envelope`), transition actions
(`AsyncByzantine.Action`), and fairness (`AsyncByzantine.Protocol.Fair`) are reused directly from
`Cslib.Distributed.AsyncByzantine`. -/
structure AsyncProtocol (P V S M : Type*) where
  /-- Initial internal state of process `p` with input `v : V`. -/
  init : P → V → S
  /-- Initial outgoing `(dest, body)` messages emitted by process `p` with input `v : V`. -/
  initMsgs : P → V → Multiset (P × M)
  /-- State transition when `dest` receives `body` from `src`. -/
  next : P → ProcState S V → P → M → S
  /-- Outgoing messages `(q, m)` emitted when `dest` receives `body` from `src`. -/
  send : P → ProcState S V → P → M → Multiset (P × M)
  /-- Write-once output value (`some v`) delivered when `dest` receives `body` from `src`. -/
  out : P → ProcState S V → P → M → Option V

namespace AsyncProtocol

variable {P V S M : Type*} [DecidableEq P] [DecidableEq M] (π : AsyncProtocol P V S M)

/-- Embed `π` with fixed input vector `x : P → V` and any witness process `d : P` as an
`AsyncByzantine.Protocol`, sharing the exact same LTS transitions and initial configuration. -/
@[expose] def toBroadcast (x : P → V) (d : P) :
    AsyncByzantine.Protocol P S M V d where
  init p := π.init p (x p)
  initDealer _ := π.init d (x d)
  initMsgs p := π.initMsgs p (x p)
  initDealerMsgs _ := π.initMsgs d (x d)
  next := π.next
  send := π.send
  out := π.out

/-- Initial global configuration for static faulty set `F` and input vector `x : P → V`. -/
@[expose] def start [Fintype P] (F : Finset P) (x : P → V) : State P S M V where
  msgs := Finset.univ.val.bind fun p =>
    if p ∈ F then 0 else (π.initMsgs p (x p)).map (tagSender p)
  proc p := ⟨π.init p (x p), none⟩

/-- Local write-once state update upon message delivery. -/
@[expose] def updateProc (dest src : P) (body : M) (st : ProcState S V) : ProcState S V :=
  ⟨π.next dest st src body, if st.out.isNone then π.out dest st src body else st.out⟩

/-- Core global transition shared by authentic delivery and Byzantine injection. -/
@[expose] def recvCore (src dest : P) (body : M) (msgsBase : Multiset (Envelope P M))
    (s : State P S M V) : State P S M V where
  msgs := msgsBase + (π.send dest (s.proc dest) src body).map (tagSender dest)
  proc q := if q = dest then π.updateProc dest src body (s.proc dest) else s.proc q

/-- State resulting from delivering authentic in-flight envelope `e` to `e.dest`. -/
@[expose] def recvHonest (e : Envelope P M) (s : State P S M V) : State P S M V :=
  π.recvCore e.src e.dest e.body (s.msgs.erase e) s

/-- State resulting from delivering adversary-injected `(src, body)` to `dest`. -/
@[expose] def recvByz (src dest : P) (body : M) (s : State P S M V) : State P S M V :=
  π.recvCore src dest body s.msgs s

/-- Labelled transition system of `π` for static Byzantine set `F`. -/
@[expose] def lts (F : Finset P) : LTS (State P S M V) (Action P M) where
  Tr s a s' := match a with
    | .deliver e => e ∈ s.msgs ∧ e.dest ∉ F ∧ s' = π.recvHonest e s
    | .byzRecv src dest body => src ∈ F ∧ dest ∉ F ∧ s' = π.recvByz src dest body s
    | .stutter => s' = s

/-- Reachability from `π.start F x` under `π.lts F`. -/
@[expose] def Reachable [Fintype P] (F : Finset P) (x : P → V) (s : State P S M V) : Prop :=
  (π.lts F).CanReach (π.start F x) s

/-- Admissible infinite execution of `π` for static faulty set `F` and inputs `x : P → V`. -/
@[expose] def AdmissibleRun [Fintype P] (F : Finset P) (x : P → V)
    (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)) : Prop :=
  ss 0 = π.start F x ∧ (π.lts F).OmegaExecution ss xs ∧ AsyncByzantine.Protocol.Fair F ss xs

@[simp]
theorem toBroadcast_lts (x : P → V) (d : P) (F : Finset P) :
    (π.toBroadcast x d).lts F = π.lts F := rfl

omit [DecidableEq M] in
theorem toBroadcast_start [Fintype P] (F : Finset P) (x : P → V) (d : P)
    (inp : Option V) :
    (π.toBroadcast x d).start F inp = π.start F x := by
  ext1
  · simp only [AsyncByzantine.Protocol.start, start, AsyncByzantine.Protocol.initSend, toBroadcast]
    refine congrArg (Multiset.bind Finset.univ.val) (funext fun p => ?_)
    by_cases hpd : p = d
    · subst hpd; simp only [↓reduceIte]
    · simp only [hpd, ↓reduceIte]
  · ext p
    · simp only [AsyncByzantine.Protocol.start, start, AsyncByzantine.Protocol.initState,
        toBroadcast]
      by_cases hpd : p = d
      · subst hpd; simp only [↓reduceIte]
      · simp only [hpd, ↓reduceIte]
    · simp only [AsyncByzantine.Protocol.start, start]

theorem admissibleRun_iff_toBroadcast [Fintype P] (F : Finset P) (x : P → V) (d : P)
    (ss : ωSequence (State P S M V)) (xs : ωSequence (Action P M)) :
    π.AdmissibleRun F x ss xs ↔ (π.toBroadcast x d).AdmissibleRun F none ss xs := by
  simp only [AdmissibleRun, AsyncByzantine.Protocol.AdmissibleRun,
    toBroadcast_start, toBroadcast_lts]

theorem admissibleRun_reachable [Fintype P] {F : Finset P} {x : P → V}
    {ss : ωSequence (State P S M V)} {xs : ωSequence (Action P M)}
    (ha : π.AdmissibleRun F x ss xs) (k : ℕ) : π.Reachable F x (ss k) :=
  ⟨xs.extract 0 k, ha.1 ▸ ha.2.1.extract_mTr (Nat.zero_le k)⟩

theorem procDecided_stable {F : Finset P} {s s' : State P S M V} {p : P} {v : V}
    (hd : s.ProcDecided p v) (hreach : (π.lts F).CanReach s s') : s'.ProcDecided p v :=
  (π.toBroadcast (fun _ => v) p).procDecided_stable hd hreach

theorem omega_procDecided_stable {F : Finset P} {ss : ωSequence (State P S M V)}
    {xs : ωSequence (Action P M)} (he : (π.lts F).OmegaExecution ss xs)
    {k j : ℕ} (hkj : k ≤ j) {p : P} {v : V} (hd : (ss k).ProcDecided p v) :
    (ss j).ProcDecided p v :=
  (π.toBroadcast (fun _ => v) p).omega_procDecided_stable he hkj hd

/-- Trivial single-process asynchronous protocol: each process sends a unit self-message at start
and outputs its own input upon receiving any message. Uses `ULift` on local state so `State` lives
in `Type (max u v)` for independent process and value universes. -/
@[expose] def ownInput.{u, v} (P : Type u) (V : Type v) :
    AsyncProtocol P V (ULift.{u} V) PUnit.{v + 1} where
  init _ v := ⟨v⟩
  initMsgs p _ := {(p, .unit)}
  next _ st _ _ := st.state
  send _ _ _ _ := 0
  out _ st _ _ := some st.state.down

section Spec

variable {K : Type*} [Field K] [LinearOrder K] (πK : AsyncProtocol P K S M)

/-- Unit-interval asynchronous `ε`-approximate Byzantine agreement (a `[0, 1]`-bounded milestone
step toward `#7116` and `#3261`, after Section 4 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986], rather than that paper's
unbounded-input Theorem 2): whenever `F.card ≤ t` and all correct inputs lie in `[0, 1]`,
* **termination**: in every fair execution, every correct process eventually outputs a value;
* **validity**: for every `[lo, hi]` containing all correct inputs, every value output by a correct
  process in any reachable state lies in `[lo, hi]`;
* **agreement**: in any reachable state, any two values output by correct processes differ by at
  most `ε`. -/
structure SolvesUnitAsyncApproxAgreement [Fintype P] (t : ℕ) (ε : K) : Prop where
  /-- Fair-delivery termination: every correct process eventually decides. -/
  termination : ∀ F : Finset P, F.card ≤ t → ∀ x : P → K,
    (∀ k ∉ F, x k ∈ Set.Icc 0 1) →
    ∀ ss xs, πK.AdmissibleRun F x ss xs → ∀ i ∉ F, ∃ n v, (ss n).ProcDecided i v
  /-- Convex-hull validity across all reachable states. -/
  validity : ∀ F : Finset P, F.card ≤ t → ∀ (x : P → K) (lo hi : K),
    (∀ k ∉ F, x k ∈ Set.Icc 0 1) → (∀ k ∉ F, x k ∈ Set.Icc lo hi) →
    ∀ s, πK.Reachable F x s → ∀ i ∉ F, ∀ v, s.ProcDecided i v → v ∈ Set.Icc lo hi
  /-- Approximate `ε`-agreement across all reachable states. -/
  agreement : ∀ F : Finset P, F.card ≤ t → ∀ x : P → K,
    (∀ k ∉ F, x k ∈ Set.Icc 0 1) →
    ∀ s, πK.Reachable F x s → ∀ i ∉ F, ∀ j ∉ F, ∀ v₁ v₂,
    s.ProcDecided i v₁ → s.ProcDecided j v₂ → |v₁ - v₂| ≤ ε

theorem SolvesUnitAsyncApproxAgreement.mono [Fintype P] {πK : AsyncProtocol P K S M}
    {t t' : ℕ} {ε ε' : K}
    (h : πK.SolvesUnitAsyncApproxAgreement t ε) (ht : t' ≤ t) (hε : ε ≤ ε') :
    πK.SolvesUnitAsyncApproxAgreement t' ε' where
  termination F hF := h.termination F (hF.trans ht)
  validity F hF := h.validity F (hF.trans ht)
  agreement F hF x hx s hr i hi j hj v₁ v₂ h₁ h₂ :=
    (h.agreement F (hF.trans ht) x hx s hr i hi j hj v₁ v₂ h₁ h₂).trans hε

/-- Unit-interval agreement along any admissible run at arbitrary decision steps `n₁, n₂`. -/
theorem SolvesUnitAsyncApproxAgreement.agreement_admissible [Fintype P]
    {πK : AsyncProtocol P K S M} {t : ℕ} {ε : K}
    (h : πK.SolvesUnitAsyncApproxAgreement t ε) {F : Finset P} (hF : F.card ≤ t)
    {x : P → K} (hx : ∀ k ∉ F, x k ∈ Set.Icc 0 1)
    {ss : ωSequence (State P S M K)} {xs : ωSequence (Action P M)}
    (ha : πK.AdmissibleRun F x ss xs) {i j : P} (hi : i ∉ F) (hj : j ∉ F)
    {n₁ n₂ : ℕ} {v₁ v₂ : K}
    (h₁ : (ss n₁).ProcDecided i v₁) (h₂ : (ss n₂).ProcDecided j v₂) :
    |v₁ - v₂| ≤ ε :=
  h.agreement F hF x hx (ss (max n₁ n₂)) (πK.admissibleRun_reachable ha (max n₁ n₂))
    i hi j hj v₁ v₂
    (πK.omega_procDecided_stable ha.2.1 (le_max_left _ _) h₁)
    (πK.omega_procDecided_stable ha.2.1 (le_max_right _ _) h₂)

theorem solvesUnitAsyncApproxAgreement_ownInput.{u, v} {P : Type u} {K : Type v}
    [DecidableEq P] [Fintype P] [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Subsingleton P]
    (t : ℕ) {ε : K} (hε : 0 ≤ ε) :
    (ownInput P K).SolvesUnitAsyncApproxAgreement t ε := by
  have hinv : ∀ (F : Finset P) (x : P → K) (s : State P (ULift.{u} K) PUnit.{v + 1} K),
      (ownInput P K).Reachable F x s →
      ∀ p ∉ F, (s.proc p).state.down = x p ∧ ∀ v, s.ProcDecided p v → v = x p := by
    intro F x s ⟨xl, hxl⟩
    have htrInv : ((ownInput P K).lts F).TrInv
        (fun st => ∀ p ∉ F, (st.proc p).state.down = x p ∧ ∀ v, st.ProcDecided p v → v = x p) := by
      intro s₁ a s₂ htr ih p hpF
      cases a with
      | deliver e =>
        obtain ⟨_, _, rfl⟩ := htr
        simp only [State.ProcDecided, recvHonest, recvCore, updateProc, ownInput]
        split_ifs with hp hnone
        · subst hp
          exact ⟨(ih e.dest hpF).1, fun v hv => by
            cases hv; exact (ih e.dest hpF).1⟩
        · subst hp
          exact ih e.dest hpF
        · exact ih p hpF
      | byzRecv src dest body =>
        obtain ⟨_, _, rfl⟩ := htr
        simp only [State.ProcDecided, recvByz, recvCore, updateProc, ownInput]
        split_ifs with hp hnone
        · rw [hp] at hpF ⊢
          exact ⟨(ih dest hpF).1, fun v hv => by
            cases hv; exact (ih dest hpF).1⟩
        · rw [hp] at hpF ⊢
          exact ih dest hpF
        · exact ih p hpF
      | stutter =>
        obtain rfl := htr
        exact ih p hpF
    refine LTS.mtrInv_of_trInv htrInv _ _ _ hxl (fun p _ => ⟨rfl, fun v hv => ?_⟩)
    simp only [State.ProcDecided, start] at hv
    cases hv
  refine ⟨?_, ?_, ?_⟩
  · intro F _ x _ ss xs ha i hiF
    let e : Envelope P PUnit.{v + 1} := ⟨i, i, .unit⟩
    have he0 : e ∈ (ss 0).msgs := by
      rw [ha.1]
      simp only [start, ownInput, Multiset.mem_bind, Finset.mem_val, Finset.mem_univ, true_and]
      refine ⟨i, ?_⟩
      simp only [hiF, ↓reduceIte, Multiset.map_singleton, Multiset.mem_singleton]
      rfl
    obtain ⟨j, _, hj⟩ := ha.2.2 e hiF 0 he0
    have htr : ((ownInput P K).lts F).Tr (ss j) (.deliver e) (ss (j + 1)) := hj ▸ ha.2.1 j
    obtain ⟨_, _, hnext⟩ := htr
    refine ⟨j + 1, x i, ?_⟩
    have hj_inv := hinv F x (ss j) ((ownInput P K).admissibleRun_reachable ha j) i hiF
    simp only [State.ProcDecided, hnext, recvHonest, recvCore, updateProc, ownInput, e, ↓reduceIte]
    cases hout : ((ss j).proc i).out with
    | none => simp only [Option.isNone_none, ↓reduceIte, hj_inv.1]
    | some v =>
      simp only [Option.isNone_some, Bool.false_eq_true, ↓reduceIte, Option.some.injEq]
      exact hj_inv.2 v hout
  · intro F _ x lo hi _ hIcc s hr i hiF v hv
    rw [(hinv F x s hr i hiF).2 v hv]
    exact hIcc i hiF
  · intro F _ x _ s hr i hiF j hjF v₁ v₂ h₁ h₂
    rw [(hinv F x s hr i hiF).2 v₁ h₁, (hinv F x s hr j hjF).2 v₂ h₂,
      Subsingleton.elim i j, sub_self, abs_zero]
    exact hε

/-! ### Asynchronous `2 ≤ |P| ≤ 3 * t` split-brain impossibility -/

omit [Field K] [LinearOrder K] in
private lemma start_msgs_count_of_notMem [Fintype P] (F : Finset P) (x : P → K)
    {e : Envelope P M} (hnot : e.src ∉ F) :
    (πK.start F x).msgs.count e =
      ((πK.initMsgs e.src (x e.src)).map (tagSender e.src)).count e := by
  simp only [start, Multiset.count_bind]
  have hterm : ∀ p : P,
      (if p ∈ F then (0 : Multiset (Envelope P M))
        else (πK.initMsgs p (x p)).map (tagSender p)).count e =
      if p = e.src then ((πK.initMsgs e.src (x e.src)).map (tagSender e.src)).count e else 0 := by
    intro p
    by_cases hpe : p = e.src
    · subst hpe; simp only [hnot, ↓reduceIte]
    · simp only [hpe, ↓reduceIte]
      by_cases hpF : p ∈ F
      · simp only [hpF, ↓reduceIte, Multiset.count_zero]
      · simp only [hpF, ↓reduceIte]
        exact Multiset.count_eq_zero_of_notMem fun hmem => by
          obtain ⟨qm, _, htag⟩ := Multiset.mem_map.mp hmem
          exact hpe (congrArg Envelope.src htag)
  rw [show (Finset.univ.val.map fun p => (if p ∈ F then (0 : Multiset (Envelope P M))
      else (πK.initMsgs p (x p)).map (tagSender p)).count e) =
      Finset.univ.val.map fun p =>
        if p = e.src then ((πK.initMsgs e.src (x e.src)).map (tagSender e.src)).count e else 0
    from congrArg (fun f => Finset.univ.val.map f) (funext hterm)]
  change (Finset.univ.sum fun p =>
      if p = e.src then ((πK.initMsgs e.src (x e.src)).map (tagSender e.src)).count e else 0) = _
  rw [Finset.sum_eq_single e.src
    (fun p _ hne => by simp only [hne, ↓reduceIte])
    (fun h => absurd (Finset.mem_univ e.src) h)]
  simp only [↓reduceIte]

private lemma extract_isHonest_of_forall {P' M' : Type*} (xs : ωSequence (Action P' M'))
    {n : ℕ} (hhon : ∀ k, (xs k).IsHonest) :
    ∀ a ∈ xs.extract 0 n, a.IsHonest := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < n - 0 := by simpa only [ωSequence.length_extract] using hi
  rw [xs.get_extract hi']
  exact hhon (0 + i)

/-- **Split-brain impossibility for unit-interval asynchronous `ε`-approximate Byzantine agreement**
(`ε < 1`): if `P` is partitioned into pairwise disjoint groups `A, B, C` each of size at most `t`
with `a₀ ∈ A` and `c₀ ∈ C` (`B` may be empty), no protocol solves
`SolvesUnitAsyncApproxAgreement t ε` for `ε < 1`. -/
theorem not_solvesUnitAsyncApproxAgreement_of_partition [Fintype P] [IsStrictOrderedRing K]
    {t : ℕ} {ε : K} (hε : ε < 1)
    (A B C : Finset P)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hcover : ∀ p : P, p ∈ A ∨ p ∈ B ∨ p ∈ C)
    (hA : A.card ≤ t) (hB : B.card ≤ t) (hC : C.card ≤ t)
    {a₀ c₀ : P} (ha₀ : a₀ ∈ A) (hc₀ : c₀ ∈ C) :
    ¬ πK.SolvesUnitAsyncApproxAgreement t ε := by
  intro hsol
  have hc₀_not_A : c₀ ∉ A := Finset.disjoint_right.mp hAC hc₀
  have ha₀_not_C : a₀ ∉ C := Finset.disjoint_left.mp hAC ha₀
  have ha₀_not_B : a₀ ∉ B := Finset.disjoint_left.mp hAB ha₀
  have hc₀_not_B : c₀ ∉ B := Finset.disjoint_right.mp hBC hc₀
  have hcoverA : ∀ p, p ∉ A → p ∈ B ∨ p ∈ C := fun p hp => by
    rcases hcover p with h | h | h
    · exact absurd h hp
    · exact Or.inl h
    · exact Or.inr h
  have hcoverC : ∀ p, p ∉ C → p ∈ B ∨ p ∈ A := fun p hp => by
    rcases hcover p with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · exact absurd h hp
  let x₀ : P → K := fun _ => 0
  let x₁ : P → K := fun _ => 1
  let x_split : P → K := fun p => if p ∈ A then 1 else 0
  -- Run 1 (`A` silent faulty, all inputs `0`): `c₀ ∈ C` decides `0`.
  obtain ⟨ss₀, xs₀, ha₀_bc, hhon₀⟩ := (πK.toBroadcast x₀ a₀).exists_honest_admissibleRun A none
  have ha_run₀ : πK.AdmissibleRun A x₀ ss₀ xs₀ :=
    (πK.admissibleRun_iff_toBroadcast A x₀ a₀ ss₀ xs₀).mpr ha₀_bc
  obtain ⟨n₀, v₀, hdec₀⟩ := hsol.termination A hA x₀ (fun _ _ => ⟨le_rfl, zero_le_one⟩)
    ss₀ xs₀ ha_run₀ c₀ hc₀_not_A
  have hv₀ : v₀ = 0 := by
    have hm := hsol.validity A hA x₀ 0 0 (fun _ _ => ⟨le_rfl, zero_le_one⟩)
      (fun _ _ => ⟨le_rfl, le_rfl⟩) (ss₀ n₀) (πK.admissibleRun_reachable ha_run₀ n₀)
      c₀ hc₀_not_A v₀ hdec₀
    exact le_antisymm hm.2 hm.1
  subst hv₀
  have hmtr₀ : ((πK.toBroadcast x₀ a₀).lts A).MTr ((πK.toBroadcast x₀ a₀).start A none)
      (xs₀.extract 0 n₀) (ss₀ n₀) :=
    ha₀_bc.1 ▸ ha₀_bc.2.1.extract_mTr (Nat.zero_le n₀)
  -- Run 2 (`C` silent faulty, all inputs `1`): `a₀ ∈ A` decides `1`.
  obtain ⟨ss₁, xs₁, ha₁_bc, hhon₁⟩ := (πK.toBroadcast x₁ a₀).exists_honest_admissibleRun C none
  have ha_run₁ : πK.AdmissibleRun C x₁ ss₁ xs₁ :=
    (πK.admissibleRun_iff_toBroadcast C x₁ a₀ ss₁ xs₁).mpr ha₁_bc
  obtain ⟨n₁, v₁, hdec₁⟩ := hsol.termination C hC x₁ (fun _ _ => ⟨zero_le_one, le_rfl⟩)
    ss₁ xs₁ ha_run₁ a₀ ha₀_not_C
  have hv₁ : v₁ = 1 := by
    have hm := hsol.validity C hC x₁ 1 1 (fun _ _ => ⟨zero_le_one, le_rfl⟩)
      (fun _ _ => ⟨le_rfl, le_rfl⟩) (ss₁ n₁) (πK.admissibleRun_reachable ha_run₁ n₁)
      a₀ ha₀_not_C v₁ hdec₁
    exact le_antisymm hm.2 hm.1
  subst hv₁
  have hmtr₁ : ((πK.toBroadcast x₁ a₀).lts C).MTr ((πK.toBroadcast x₁ a₀).start C none)
      (xs₁.extract 0 n₁) (ss₁ n₁) :=
    ha₁_bc.1 ▸ ha₁_bc.2.1.extract_mTr (Nat.zero_le n₁)
  -- Run 3 (`B` equivocating faulty, `x_split`): replay `C` from Run 1, then `A` from Run 2.
  let u₀ := πK.start B x_split
  have hreplay : ∀ (G F_other : Finset P) (c : K) (u : State P S M K)
      {n : ℕ} {ss : ωSequence (State P S M K)} {xs : ωSequence (Action P M)},
      Disjoint B G → Disjoint F_other G →
      (∀ p, p ∉ F_other → p ∈ B ∨ p ∈ G) →
      (∀ p ∈ G, x_split p = c) →
      (∀ p ∈ G, u.proc p = u₀.proc p) →
      (∀ e : Envelope P M, e.src ∈ G → u₀.msgs.count e ≤ u.msgs.count e) →
      ((πK.toBroadcast (fun _ => c) a₀).lts F_other).MTr
        ((πK.toBroadcast (fun _ => c) a₀).start F_other none) (xs.extract 0 n) (ss n) →
      (∀ k, (xs k).IsHonest) →
      ∃ yl u', (πK.lts B).MTr u yl u' ∧
        (∀ p ∈ G, u'.proc p = (ss n).proc p) ∧
        (∀ p ∉ G, u'.proc p = u.proc p) ∧
        (∀ e : Envelope P M, e.src ∉ G → u'.msgs.count e = u.msgs.count e) := by
    intro G F_other c u n ss xs hBG hFG hcovG hxG hprocG hmsgG hmtr hhon
    refine (πK.toBroadcast (fun _ => c) a₀).replay_subset_mTr hBG hmtr
      (extract_isHonest_of_forall xs hhon)
      (fun e he => hcovG e.src
        ((πK.toBroadcast (fun _ => c) a₀).start_msgs_src_notMem F_other none he))
      hcovG (fun p hpG => ?_) (fun e heG _ => ?_)
    · rw [hprocG p hpG, πK.toBroadcast_start F_other (fun _ => c) a₀ none]
      simp only [u₀, start, hxG p hpG]
    · have hnotF : e.src ∉ F_other := Finset.disjoint_right.mp hFG heG
      have hnotB : e.src ∉ B := Finset.disjoint_right.mp hBG heG
      refine le_trans ?_ (hmsgG e heG)
      rw [πK.toBroadcast_start F_other (fun _ => c) a₀ none]
      dsimp only [u₀]
      rw [πK.start_msgs_count_of_notMem F_other (fun _ => c) hnotF,
        πK.start_msgs_count_of_notMem B x_split hnotB, hxG e.src heG]
  obtain ⟨yl₀, u₁, hyl₀, hu₁_C, hu₁_out, hu₁_msg⟩ :=
    hreplay C A 0 u₀ hBC hAC hcoverA
      (fun p hpC => ite_eq_right (Finset.disjoint_right.mp hAC hpC))
      (fun _ _ => rfl) (fun _ _ => le_rfl) hmtr₀ hhon₀
  obtain ⟨yl₁, u₂, hyl₁, hu₂_A, hu₂_out, _⟩ :=
    hreplay A C 1 u₁ hAB.symm hAC.symm hcoverC
      (fun p hpA => ite_eq_left hpA)
      (fun p hpA => hu₁_out p (Finset.disjoint_left.mp hAC hpA))
      (fun e heA => le_of_eq (hu₁_msg e (Finset.disjoint_left.mp hAC heA)).symm) hmtr₁ hhon₁
  have hreach : πK.Reachable B x_split u₂ := ⟨yl₀ ++ yl₁, LTS.MTr.comp (πK.lts B) hyl₀ hyl₁⟩
  have ha_dec : u₂.ProcDecided a₀ 1 := by
    change (u₂.proc a₀).out = some 1
    rw [hu₂_A a₀ ha₀]
    exact hdec₁
  have hc_dec : u₂.ProcDecided c₀ 0 := by
    change (u₂.proc c₀).out = some 0
    rw [hu₂_out c₀ hc₀_not_A, hu₁_C c₀ hc₀]
    exact hdec₀
  have hx_split_Icc : ∀ k ∉ B, x_split k ∈ Set.Icc (0 : K) 1 := by
    intro k _
    by_cases hkA : k ∈ A <;> simp only [x_split, hkA, ↓reduceIte, Set.mem_Icc,
      le_rfl, zero_le_one, and_self]
  have habs := hsol.agreement B hB x_split hx_split_Icc u₂ hreach
    a₀ ha₀_not_B c₀ hc₀_not_B 1 0 ha_dec hc_dec
  rw [sub_zero, abs_one] at habs
  linarith

/-- **No unit-interval asynchronous `ε`-approximate Byzantine agreement for `2 ≤ |P| ≤ 3 * t` and
`ε < 1`:** asynchronous split-brain analogue of the `3t + 1` bound of
[Fischer, Lynch and Merritt][FischerLynchMerritt1985] (cited in Section 7, p. 515 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986]). Covers both `n = 2`
(empty middle group) and `3 ≤ n ≤ 3 * t`, and in particular every `ε < 1 / 2`. -/
theorem not_solvesUnitAsyncApproxAgreement [Fintype P] [IsStrictOrderedRing K]
    {t : ℕ} {ε : K} (h2 : 2 ≤ Fintype.card P) (h3 : Fintype.card P ≤ 3 * t) (hε : ε < 1) :
    ¬ πK.SolvesUnitAsyncApproxAgreement t ε := by
  obtain ⟨g, a₀, c₀, hcard, ha₀, hc₀⟩ := exists_three_group_fn h2 h3
  let grp : Fin 3 → Finset P := fun k => Finset.univ.filter fun i => g i = k
  have hdisj : ∀ k₁ k₂ : Fin 3, k₁ ≠ k₂ → Disjoint (grp k₁) (grp k₂) := by
    intro k₁ k₂ hne
    rw [Finset.disjoint_left]
    intro p h₁ h₂
    simp only [grp, Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact hne (h₁.symm.trans h₂)
  have hcov : ∀ p : P, p ∈ grp 0 ∨ p ∈ grp 1 ∨ p ∈ grp 2 := by
    intro p
    simp only [grp, Finset.mem_filter, Finset.mem_univ, true_and]
    have hlt := (g p).isLt
    rcases gp : g p with ⟨val, hval⟩
    have : val = 0 ∨ val = 1 ∨ val = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  exact πK.not_solvesUnitAsyncApproxAgreement_of_partition hε (grp 0) (grp 1) (grp 2)
    (hdisj 0 1 (by decide)) (hdisj 0 2 (by decide)) (hdisj 1 2 (by decide))
    hcov (hcard 0) (hcard 1) (hcard 2)
    (a₀ := a₀) (c₀ := c₀)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ a₀, ha₀⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ c₀, hc₀⟩)

end Spec

end AsyncProtocol

/-! ### Fixed-horizon single-hop round-tagged asynchronous protocol (`5 * t < |P|`) -/

/-- Round-tagged payload exchanged by `asyncApproxProtocol`. -/
@[ext]
structure RoundMsg (K : Type*) where
  /-- Asynchronous round tag `0 ≤ round < R`. -/
  round : ℕ
  /-- Proposed value for `round`. -/
  val : K
  deriving @[expose] DecidableEq

/-- Local state of a process running `asyncApproxProtocol`. Retaining only the first message per
`(round, src)` deduplicates Byzantine replays and equivocations, while buffering messages for all
current and future rounds `st.round ≤ r < R` handles out-of-order asynchronous arrival and ignores
stale messages from already-completed rounds. -/
structure AsyncApproxState (P K : Type*) where
  /-- Current active round (`0 ≤ round ≤ R`); reaches `R` when all `R` rounds finish. -/
  round : ℕ
  /-- Current estimate (`x p` at round `0`, updated by `multisetMidTrim` at each round). -/
  est : K
  /-- First round-`r` value received from each sender `src : P`: `heard r src`. -/
  heard : ℕ → P → Option K

/-- Distinct senders recorded so far by `st` for round `r`. -/
@[expose] def roundSenders {P K : Type*} [Fintype P]
    (st : AsyncApproxState P K) (r : ℕ) : Finset P :=
  Finset.univ.filter fun j => (st.heard r j).isSome

/-- Multiset of values recorded so far by `st` for round `r`. -/
@[expose] def roundValues {P K : Type*} [Fintype P] [Zero K]
    (st : AsyncApproxState P K) (r : ℕ) : Multiset K :=
  (roundSenders st r).val.map fun j => (st.heard r j).getD 0

/-- Record `val` as the round-`r` value heard from `src` in `st`. -/
@[expose] def recordHeard {P K : Type*} [DecidableEq P]
    (st : AsyncApproxState P K) (r : ℕ) (src : P) (val : K) : AsyncApproxState P K :=
  { st with
    heard := Function.update st.heard r (Function.update (st.heard r) src (some val)) }

/-- Output record of a local step of `asyncApproxProtocol`. -/
structure AsyncApproxStepResult (P K : Type*) where
  /-- Updated local internal state. -/
  nextState : AsyncApproxState P K
  /-- Outgoing `(dest, msg)` multiset emitted in this step. -/
  outgoing : Multiset (P × RoundMsg K)
  /-- Value delivered (`some v`) upon completing round `R`. -/
  delivered : Option K

/-- Initial local state of process `p` with input `v` in `asyncApproxProtocol`. -/
@[expose] def asyncApproxInit (P : Type*) {K : Type*} (v : K) : AsyncApproxState P K where
  round := 0
  est := v
  heard _ _ := none

/-- Bounded cascade advancing `st` through consecutive rounds while `st.round < R` and at least
`Fintype.card P - t` distinct senders are buffered for `st.round`. Accumulates outgoing broadcasts
for every intermediate round `< R` entered during the cascade. -/
@[expose] def asyncApproxAdvance {P K : Type*} [Fintype P] [Field K] [LinearOrder K]
    (t R : ℕ) : ℕ → AsyncApproxState P K → AsyncApproxStepResult P K
  | 0, st => ⟨st, 0, if st.round = R then some st.est else none⟩
  | fuel + 1, st =>
    if st.round < R ∧ Fintype.card P - t ≤ (roundSenders st st.round).card then
      let est' := multisetMidTrim t (roundValues st st.round)
      let r' := st.round + 1
      let st' : AsyncApproxState P K := { st with round := r', est := est' }
      let outThis : Multiset (P × RoundMsg K) :=
        if r' < R then broadcastAll P ⟨r', est'⟩ else 0
      let tail := asyncApproxAdvance t R fuel st'
      ⟨tail.nextState, outThis + tail.outgoing, tail.delivered⟩
    else
      ⟨st, 0, if st.round = R then some st.est else none⟩

/-- Local transition handler for `asyncApproxProtocol`. When `R = 0`, the first received message
delivers `st.est` immediately; when `R > 0`, a fresh `(msg.round, src)` with
`st.round ≤ msg.round < R` is buffered and triggers `asyncApproxAdvance` (stale messages with
`msg.round < st.round` or after `st.round = R` are ignored). -/
@[expose] def asyncApproxStep {P K : Type*} [Fintype P] [DecidableEq P]
    [Field K] [LinearOrder K]
    (t R : ℕ) (st : AsyncApproxState P K) (src : P) (msg : RoundMsg K) :
    AsyncApproxStepResult P K :=
  if R = 0 then
    ⟨st, 0, some st.est⟩
  else if st.round ≤ msg.round ∧ msg.round < R ∧ (st.heard msg.round src).isNone then
    let st₁ := recordHeard st msg.round src msg.val
    asyncApproxAdvance t R (R - st₁.round) st₁
  else
    ⟨st, 0, none⟩

/-- **Fixed-horizon single-hop asynchronous approximate agreement protocol** (step after the
nonterminating Algorithm $A_0$ in Section 4, p. 509 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986], using `multisetMidTrim t`
in place of `f_{2t, t}` and halting after a caller-chosen round horizon `R` rather than Algorithm
$A$'s round-0 `reduce^{2t}` spread estimation and `(v, halted)` tags): at start every process
broadcasts `⟨0, x p⟩`; in each round `r < R`, upon collecting `|P| - t` distinct round-`r` senders,
a process updates its estimate via `multisetMidTrim t`, broadcasts `⟨r + 1, est'⟩` if `r + 1 < R`,
and delivers `est'` once `round = R`. -/
@[expose] def asyncApproxProtocol (P K : Type*) [Fintype P] [DecidableEq P]
    [Field K] [LinearOrder K] (t R : ℕ) :
    AsyncProtocol P K (AsyncApproxState P K) (RoundMsg K) where
  init _ v := asyncApproxInit P v
  initMsgs _ v := broadcastAll P ⟨0, v⟩
  next _ st src m := (asyncApproxStep t R st.state src m).nextState
  send _ st src m := (asyncApproxStep t R st.state src m).outgoing
  out _ st src m := (asyncApproxStep t R st.state src m).delivered

/-! ### Private invariant & liveness proofs for `asyncApproxProtocol` -/

section AsyncProofs

variable {P K : Type*} [Fintype P] [DecidableEq P] [Field K] [LinearOrder K]

/-- Ghost proposal reconstructed from `x_p`, `st.round`, and the frozen past buffers `st.heard r`
(`r < st.round`). -/
private def localProposal (t : ℕ) (x_p : K) (st : AsyncApproxState P K) : ℕ → Option K
  | 0 => some x_p
  | r + 1 =>
    if r + 1 ≤ st.round then some (multisetMidTrim t (roundValues st r)) else none

omit [DecidableEq P] in
private lemma localProposal_isSome {t : ℕ} {x_p : K} {st : AsyncApproxState P K} (r : ℕ) :
    (localProposal t x_p st r).isSome ↔ r ≤ st.round := by
  cases r with
  | zero => simp only [localProposal, Option.isSome_some, Nat.zero_le]
  | succ u =>
    dsimp only [localProposal]
    by_cases hu : u + 1 ≤ st.round
    · rw [ite_eq_left hu]
      simp only [Option.isSome_some, hu]
    · rw [ite_eq_right hu]
      simp only [Option.isSome_none, Bool.false_eq_true, hu]

omit [DecidableEq P] in
private lemma localProposal_congr {t : ℕ} {x_p : K} {st₁ st₂ : AsyncApproxState P K} {r : ℕ}
    (hr : r ≤ st₁.round) (hle : st₁.round ≤ st₂.round)
    (hheard : ∀ u < st₁.round, st₂.heard u = st₁.heard u) :
    localProposal t x_p st₂ r = localProposal t x_p st₁ r := by
  cases r with
  | zero => rfl
  | succ u =>
    have hu2 : u + 1 ≤ st₂.round := hr.trans hle
    have hrv : roundValues st₂ u = roundValues st₁ u := by
      simp only [roundValues, roundSenders, hheard u hr]
    simp only [localProposal, ite_eq_left hr, ite_eq_left hu2, hrv]

/-- Well-formedness of a single process's local state in `asyncApproxProtocol`. -/
private structure WellFormedLocal (t R : ℕ) (x_p : K) (st : AsyncApproxState P K) : Prop where
  round_le : st.round ≤ R
  prop_round : localProposal t x_p st st.round = some st.est
  past_senders : ∀ r < st.round, Fintype.card P - t ≤ (roundSenders st r).card

omit [DecidableEq P] in
private lemma wellFormedLocal_init {t R : ℕ} (v : K) :
    WellFormedLocal (P := P) t R v (asyncApproxInit P v) where
  round_le := Nat.zero_le R
  prop_round := rfl
  past_senders _ hr := by simp only [asyncApproxInit] at hr; omega

private lemma wellFormedLocal_recordHeard {t R : ℕ} {x_p : K} {st : AsyncApproxState P K}
    (hwf : WellFormedLocal t R x_p st) {m_round : ℕ} (hm : st.round ≤ m_round)
    (src : P) (val : K) :
    WellFormedLocal t R x_p (recordHeard st m_round src val) := by
  have hheard_past : ∀ u < st.round,
      (recordHeard st m_round src val).heard u = st.heard u := by
    intro u hu
    dsimp only [recordHeard]
    have hne : u ≠ m_round := by omega
    exact Function.update_of_ne hne ..
  refine ⟨hwf.round_le, ?_, ?_⟩
  · change localProposal t x_p (recordHeard st m_round src val) st.round = some st.est
    rw [localProposal_congr (st₁ := st) (st₂ := recordHeard st m_round src val)
      le_rfl le_rfl hheard_past]
    exact hwf.prop_round
  · intro u hu
    change u < st.round at hu
    simp only [roundSenders, hheard_past u hu]
    exact hwf.past_senders u hu

omit [DecidableEq P] in
private lemma advance_spec {t R : ℕ} :
    ∀ (fuel : ℕ) (st : AsyncApproxState P K) {x_p : K},
      WellFormedLocal t R x_p st →
      R - st.round ≤ fuel →
      let res := asyncApproxAdvance t R fuel st
      WellFormedLocal t R x_p res.nextState ∧
      st.round ≤ res.nextState.round ∧
      res.nextState.heard = st.heard ∧
      (∀ r, st.round ≤ r → r + 1 ≤ res.nextState.round → r + 1 < R →
        ∀ q : P, (q, ⟨r + 1, multisetMidTrim t (roundValues st r)⟩) ∈ res.outgoing) ∧
      (∀ q m, (q, m) ∈ res.outgoing →
        m.round < R ∧ st.round < m.round ∧
          localProposal t x_p res.nextState m.round = some m.val) ∧
      (res.nextState.round = R ∨
        (roundSenders res.nextState res.nextState.round).card < Fintype.card P - t) ∧
      res.delivered =
        if res.nextState.round = R then some res.nextState.est else none
  | 0, st, _, hwf, hfuel => by
    have hR : st.round = R := by have := hwf.round_le; omega
    dsimp only [asyncApproxAdvance]
    refine ⟨hwf, le_rfl, rfl, fun r _ _ _ => by omega, ?_, Or.inl hR, rfl⟩
    intro _ _ hm; simp only [Multiset.notMem_zero] at hm
  | fuel + 1, st, x_p, hwf, hfuel => by
    dsimp only
    by_cases hcond : st.round < R ∧ Fintype.card P - t ≤ (roundSenders st st.round).card
    · set est' := multisetMidTrim t (roundValues st st.round)
      set r' := st.round + 1
      set st' : AsyncApproxState P K := { st with round := r', est := est' }
      have hst'_r : st'.round = st.round + 1 := rfl
      have hadv : asyncApproxAdvance t R (fuel + 1) st =
          let outThis : Multiset (P × RoundMsg K) :=
            if r' < R then broadcastAll P ⟨r', est'⟩ else 0
          let tail := asyncApproxAdvance t R fuel st'
          ⟨tail.nextState, outThis + tail.outgoing, tail.delivered⟩ := by
        simp only [asyncApproxAdvance, hcond, and_self, ↓reduceIte, est', r', st']
      rw [hadv]
      dsimp only
      have hwf' : WellFormedLocal t R x_p st' := by
        refine ⟨by omega, ?_, ?_⟩
        · dsimp only [localProposal, st', r', est']
          rw [ite_eq_left le_rfl]
          rfl
        · intro u hu
          change u < st.round + 1 at hu
          by_cases hur : u = st.round
          · subst hur
            exact hcond.2
          · exact hwf.past_senders u (by omega)
      have hfuel' : R - st'.round ≤ fuel := by omega
      obtain ⟨hwf_t, hle_t, hheard_t, hstep_t, hout_t, hstop_t, hdel_t⟩ :=
        advance_spec fuel st' hwf' hfuel'
      refine ⟨hwf_t, (Nat.le_succ _).trans hle_t, hheard_t, ?_, ?_, hstop_t, hdel_t⟩
      · intro r hr1 hr2 hrlt q
        by_cases hrr : r = st.round
        · subst hrr
          have hrlt' : r' < R := hrlt
          rw [ite_eq_left hrlt']
          exact Multiset.mem_add.mpr
            (Or.inl (Multiset.mem_map.mpr ⟨q, Finset.mem_val.mpr (Finset.mem_univ q), rfl⟩))
        · have hr' : st'.round ≤ r := by omega
          exact Multiset.mem_add.mpr (Or.inr (hstep_t r hr' hr2 hrlt q))
      · intro q m hm
        rw [Multiset.mem_add] at hm
        rcases hm with hm_head | hm_tail
        · by_cases hrlt : r' < R
          · rw [ite_eq_left hrlt] at hm_head
            obtain ⟨_, _, heq⟩ := Multiset.mem_map.mp hm_head
            have hm_eq : m = ⟨r', est'⟩ := (Prod.mk.inj heq).2.symm
            subst hm_eq
            refine ⟨hrlt, Nat.lt_succ_self _, ?_⟩
            dsimp only [localProposal, r']
            rw [ite_eq_left hle_t]
            have hrv : roundValues (asyncApproxAdvance t R fuel st').nextState st.round =
                roundValues st st.round := by
              simp only [roundValues, roundSenders, hheard_t]
              rfl
            rw [hrv]
          · rw [ite_eq_right hrlt] at hm_head
            simp only [Multiset.notMem_zero] at hm_head
        · obtain ⟨h1, h2, h3⟩ := hout_t q m hm_tail
          exact ⟨h1, (Nat.lt_succ_self _).trans h2, h3⟩
    · have hadv : asyncApproxAdvance t R (fuel + 1) st =
          ⟨st, 0, if st.round = R then some st.est else none⟩ := by
        simp only [asyncApproxAdvance, hcond, ↓reduceIte]
      rw [hadv]
      dsimp only
      refine ⟨hwf, le_rfl, rfl, fun r _ _ _ => by omega, ?_, ?_, rfl⟩
      · intro _ _ hm; simp only [Multiset.notMem_zero] at hm
      · by_cases hrR : st.round = R
        · exact Or.inl hrR
        · have hlt : st.round < R := lt_of_le_of_ne hwf.round_le hrR
          exact Or.inr (Nat.lt_of_not_le fun hge => hcond ⟨hlt, hge⟩)

private lemma step_mono {t R : ℕ} {st : AsyncApproxState P K} {x_p : K}
    (hwf : WellFormedLocal t R x_p st) (src : P) (msg : RoundMsg K) :
    let res := asyncApproxStep t R st src msg
    st.round ≤ res.nextState.round ∧
    (∀ r v, localProposal t x_p st r = some v →
      localProposal t x_p res.nextState r = some v) ∧
    (∀ r j v, st.heard r j = some v → res.nextState.heard r j = some v) := by
  dsimp only
  by_cases hR0 : R = 0
  · have hs : asyncApproxStep t R st src msg = ⟨st, 0, some st.est⟩ := by
      simp only [asyncApproxStep, hR0, ↓reduceIte]
    rw [hs]
    exact ⟨le_rfl, fun _ _ h => h, fun _ _ _ h => h⟩
  · by_cases hfresh : st.round ≤ msg.round ∧ msg.round < R ∧ (st.heard msg.round src).isNone
    · set st₁ := recordHeard st msg.round src msg.val
      have hs : asyncApproxStep t R st src msg =
          asyncApproxAdvance t R (R - st₁.round) st₁ := by
        dsimp only [st₁]
        simp only [asyncApproxStep, hR0, hfresh, and_self, ↓reduceIte]
      rw [hs]
      have hwf₁ := wellFormedLocal_recordHeard hwf hfresh.1 src msg.val
      obtain ⟨_, hle, hheard_eq, _, _, _, _⟩ :=
        advance_spec (t := t) (R := R) (R - st₁.round) st₁ hwf₁ le_rfl
      refine ⟨hle, ?_, ?_⟩
      · intro r v hv
        have hr : r ≤ st.round := (localProposal_isSome r).mp (by rw [hv]; rfl)
        have hheard_past : ∀ u < st.round,
            (asyncApproxAdvance t R (R - st₁.round) st₁).nextState.heard u = st.heard u := by
          intro u hu
          rw [hheard_eq]
          dsimp only [st₁, recordHeard]
          have hne : u ≠ msg.round := by have := hfresh.1; omega
          exact Function.update_of_ne hne ..
        rw [localProposal_congr hr hle hheard_past]
        exact hv
      · intro r j v hv
        rw [hheard_eq]
        dsimp only [st₁, recordHeard]
        by_cases hmr : r = msg.round
        · subst hmr
          rw [Function.update_self]
          by_cases hjs : j = src
          · subst hjs
            have hnone := hfresh.2.2
            simp only [hv, Option.isNone_some, Bool.false_eq_true] at hnone
          · rw [Function.update_of_ne hjs]
            exact hv
        · rw [Function.update_of_ne hmr]
          exact hv
    · have hs : asyncApproxStep t R st src msg = ⟨st, 0, none⟩ := by
        simp only [asyncApproxStep, hR0, hfresh, ↓reduceIte]
      rw [hs]
      exact ⟨le_rfl, fun _ _ h => h, fun _ _ _ h => h⟩

/-- Global reachable-state invariant of `asyncApproxProtocol`. -/
private structure AsyncInv (F : Finset P) (t R : ℕ) (x : P → K)
    (s : State P (AsyncApproxState P K) (RoundMsg K) K) : Prop where
  wf : ∀ p ∉ F, WellFormedLocal t R (x p) (s.proc p).state
  msgs_auth : ∀ e ∈ s.msgs, e.src ∉ F ∧
    localProposal t (x e.src) (s.proc e.src).state e.body.round = some e.body.val
  heard_auth : ∀ p ∉ F, ∀ j ∉ F, ∀ r v,
    (s.proc p).state.heard r j = some v →
      localProposal t (x j) (s.proc j).state r = some v
  stop_cond : 1 ≤ Fintype.card P - t → ∀ p ∉ F,
    (s.proc p).state.round = R ∨
      (roundSenders (s.proc p).state (s.proc p).state.round).card < Fintype.card P - t
  out_spec : ∀ p ∉ F,
    (∀ v, s.ProcDecided p v → localProposal t (x p) (s.proc p).state R = some v) ∧
    (0 < R → ((s.proc p).state.round = R ↔ (s.proc p).out.isSome))

private lemma asyncInv_start (F : Finset P) (t R : ℕ) (x : P → K) :
    AsyncInv F t R x ((asyncApproxProtocol P K t R).start F x) := by
  refine ⟨fun p _ => wellFormedLocal_init (x p), ?_, ?_, ?_, ?_⟩
  · intro e he
    simp only [AsyncProtocol.start, asyncApproxProtocol, Multiset.mem_bind, Finset.mem_val,
      Finset.mem_univ, true_and] at he
    obtain ⟨p, hp⟩ := he
    by_cases hpF : p ∈ F
    · simp only [hpF, ↓reduceIte, Multiset.notMem_zero] at hp
    · simp only [hpF, ↓reduceIte, broadcastAll, Multiset.mem_map, Finset.mem_val,
        Finset.mem_univ, true_and] at hp
      obtain ⟨qm, ⟨q, rfl⟩, rfl⟩ := hp
      exact ⟨hpF, rfl⟩
  · intro p _ _ _ r v hv
    simp only [AsyncProtocol.start, asyncApproxProtocol, asyncApproxInit] at hv
    cases hv
  · intro h1 p _
    refine Or.inr ?_
    have hemp : roundSenders (asyncApproxInit P (x p)) 0 = ∅ := by
      ext j
      simp only [roundSenders, asyncApproxInit, Option.isSome_none, Bool.false_eq_true,
        Finset.mem_filter, Finset.mem_univ, and_false, Finset.notMem_empty]
    change (roundSenders (asyncApproxInit P (x p)) 0).card < Fintype.card P - t
    rw [hemp, Finset.card_empty]
    omega
  · intro p _
    refine ⟨fun v hv => ?_, fun hR => ?_⟩
    · simp only [State.ProcDecided, AsyncProtocol.start] at hv
      cases hv
    · simp only [AsyncProtocol.start, asyncApproxProtocol, asyncApproxInit, Option.isSome_none,
        Bool.false_eq_true, iff_false]
      omega

/-- Single-message reception helper preserving `AsyncInv` across both `deliver` and `byzRecv`. -/
private lemma asyncInv_recvCore {F : Finset P} {t R : ℕ} {x : P → K}
    {s : State P (AsyncApproxState P K) (RoundMsg K) K} (hinv : AsyncInv F t R x s)
    {src dest : P} {body : RoundMsg K} {msgsBase : Multiset (Envelope P (RoundMsg K))}
    (hdest : dest ∉ F)
    (hbase : ∀ e ∈ msgsBase, e ∈ s.msgs)
    (hsrc_auth : src ∉ F →
      localProposal t (x src) (s.proc src).state body.round = some body.val) :
    AsyncInv F t R x
      ((asyncApproxProtocol P K t R).recvCore src dest body msgsBase s) := by
  set s' := (asyncApproxProtocol P K t R).recvCore src dest body msgsBase s
  set st := (s.proc dest).state
  set res := asyncApproxStep t R st src body
  have hproc_state : ∀ q,
      (s'.proc q).state = if q = dest then res.nextState else (s.proc q).state := by
    intro q
    dsimp only [s', res, st]
    by_cases hqd : q = dest <;>
      simp only [AsyncProtocol.recvCore, AsyncProtocol.updateProc, asyncApproxProtocol,
        hqd, ↓reduceIte]
  have hproc_out_eq : ∀ q, (s'.proc q).out =
      if q = dest then
        if (s.proc dest).out.isNone then res.delivered else (s.proc dest).out
      else (s.proc q).out := by
    intro q
    dsimp only [s', res, st]
    by_cases hqd : q = dest <;>
      simp only [AsyncProtocol.recvCore, AsyncProtocol.updateProc, asyncApproxProtocol,
        hqd, ↓reduceIte]
  have hwf_dest : WellFormedLocal t R (x dest) st := hinv.wf dest hdest
  obtain ⟨_, hprop_mono_dest, _⟩ := step_mono (t := t) (R := R) hwf_dest src body
  have hprop_mono_all : ∀ q ∉ F, ∀ r v,
      localProposal t (x q) (s.proc q).state r = some v →
        localProposal t (x q) (s'.proc q).state r = some v := by
    intro q _ r v hv
    rw [hproc_state q]
    by_cases hqd : q = dest
    · rw [ite_eq_left hqd]
      subst hqd
      exact hprop_mono_dest r v hv
    · rw [ite_eq_right hqd]
      exact hv
  -- Analyse `asyncApproxStep t R st src body` into its three branches.
  have hdest_facts :
      WellFormedLocal t R (x dest) res.nextState ∧
      (∀ q m, (q, m) ∈ res.outgoing →
        localProposal t (x dest) res.nextState m.round = some m.val) ∧
      (∀ j ∉ F, ∀ r v, res.nextState.heard r j = some v →
        localProposal t (x j) (s'.proc j).state r = some v) ∧
      (1 ≤ Fintype.card P - t →
        res.nextState.round = R ∨
          (roundSenders res.nextState res.nextState.round).card < Fintype.card P - t) ∧
      ((∀ v, (s'.proc dest).out = some v →
          localProposal t (x dest) res.nextState R = some v) ∧
        (0 < R → (res.nextState.round = R ↔ (s'.proc dest).out.isSome))) := by
    by_cases hR0 : R = 0
    · subst hR0
      have hres : res = ⟨st, 0, some st.est⟩ := by
        dsimp only [res]
        simp only [asyncApproxStep, ↓reduceIte]
      have hout_d : (s'.proc dest).out =
          if (s.proc dest).out.isNone then some st.est else (s.proc dest).out := by
        rw [hproc_out_eq dest, ite_eq_left rfl, hres]
      rw [hres]
      dsimp only
      have hst_R : st.round = 0 := by have := hwf_dest.round_le; omega
      refine ⟨hwf_dest, ?_, ?_, fun _ => Or.inl hst_R, ?_⟩
      · intro _ _ hm; simp only [Multiset.notMem_zero] at hm
      · intro j hjF r v hv
        exact hprop_mono_all j hjF r v (hinv.heard_auth dest hdest j hjF r v hv)
      · refine ⟨fun v hv => ?_, fun h0 => by omega⟩
        rw [hout_d] at hv
        cases hout : (s.proc dest).out with
        | none =>
          simp only [hout, Option.isNone_none, ↓reduceIte, Option.some.injEq] at hv
          subst hv
          simpa only [hst_R] using hwf_dest.prop_round
        | some v₀ =>
          simp only [hout, Option.isNone_some, Bool.false_eq_true, ↓reduceIte,
            Option.some.injEq] at hv
          subst hv
          exact (hinv.out_spec dest hdest).1 v₀ hout
    · have hR_pos : 0 < R := Nat.pos_of_ne_zero hR0
      by_cases hfresh : st.round ≤ body.round ∧ body.round < R ∧ (st.heard body.round src).isNone
      · set st₁ := recordHeard st body.round src body.val
        have hst₁_r : st₁.round = st.round := rfl
        have hres : res = asyncApproxAdvance t R (R - st₁.round) st₁ := by
          dsimp only [res, st₁]
          simp only [asyncApproxStep, hR0, hfresh, and_self, ↓reduceIte]
        have hout_prev_none : (s.proc dest).out = none := by
          by_contra hne_none
          have hisSome : (s.proc dest).out.isSome := Option.ne_none_iff_isSome.mp hne_none
          have hroundR := ((hinv.out_spec dest hdest).2 hR_pos).mpr hisSome
          exact absurd hroundR (ne_of_lt (lt_of_le_of_lt hfresh.1 hfresh.2.1))
        have hproc_out : (s'.proc dest).out =
            (asyncApproxAdvance t R (R - st₁.round) st₁).delivered := by
          rw [hproc_out_eq dest, ite_eq_left rfl, hout_prev_none, Option.isNone_none,
            ite_eq_left rfl, hres]
        rw [hres]
        have hwf₁ := wellFormedLocal_recordHeard hwf_dest hfresh.1 src body.val
        obtain ⟨hwf_n, _, hheard_n, _, hout_n, hstop_n, hdel_n⟩ :=
          advance_spec (t := t) (R := R) (R - st₁.round) st₁ hwf₁ le_rfl
        refine ⟨hwf_n, ?_, ?_, fun _ => hstop_n, ?_⟩
        · intro q m hm
          exact (hout_n q m hm).2.2
        · intro j hjF r v hv
          rw [hheard_n] at hv
          dsimp only [st₁, recordHeard] at hv
          by_cases hmr : r = body.round
          · subst hmr
            rw [Function.update_self] at hv
            by_cases hjs : j = src
            · subst hjs
              rw [Function.update_self, Option.some.injEq] at hv
              subst hv
              exact hprop_mono_all j hjF _ _ (hsrc_auth hjF)
            · rw [Function.update_of_ne hjs] at hv
              exact hprop_mono_all j hjF _ _ (hinv.heard_auth dest hdest j hjF _ v hv)
          · rw [Function.update_of_ne hmr] at hv
            exact hprop_mono_all j hjF _ _ (hinv.heard_auth dest hdest j hjF r v hv)
        · rw [hproc_out, hdel_n]
          refine ⟨fun v hv => ?_, fun _ => ?_⟩
          · by_cases hrR : (asyncApproxAdvance t R (R - st₁.round) st₁).nextState.round = R
            · rw [ite_eq_left hrR] at hv
              cases hv
              have hp := hwf_n.prop_round
              rwa [hrR] at hp
            · rw [ite_eq_right hrR] at hv
              cases hv
          · by_cases hrR : (asyncApproxAdvance t R (R - st₁.round) st₁).nextState.round = R
            · rw [ite_eq_left hrR]
              exact ⟨fun _ => rfl, fun _ => hrR⟩
            · rw [ite_eq_right hrR]
              exact ⟨fun h => absurd h hrR, fun h => Bool.noConfusion h⟩
      · have hres : res = ⟨st, 0, none⟩ := by
          dsimp only [res]
          simp only [asyncApproxStep, hR0, hfresh, ↓reduceIte]
        have hproc_out : (s'.proc dest).out = (s.proc dest).out := by
          rw [hproc_out_eq dest, ite_eq_left rfl, hres]
          cases (s.proc dest).out <;> rfl
        rw [hres]
        dsimp only
        refine ⟨hwf_dest, ?_, ?_, fun h1 => hinv.stop_cond h1 dest hdest, ?_⟩
        · intro _ _ hm; simp only [Multiset.notMem_zero] at hm
        · intro j hjF r v hv
          exact hprop_mono_all j hjF r v (hinv.heard_auth dest hdest j hjF r v hv)
        · rw [hproc_out]
          exact hinv.out_spec dest hdest
  obtain ⟨hwf_d, hout_d, hheard_d, hstop_d, hout_spec_d⟩ := hdest_facts
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro p hpF
    rw [hproc_state p]
    by_cases hpd : p = dest
    · rw [ite_eq_left hpd]
      exact hpd ▸ hwf_d
    · rw [ite_eq_right hpd]
      exact hinv.wf p hpF
  · intro e he
    have he' : e ∈ msgsBase + res.outgoing.map (tagSender dest) := he
    rw [Multiset.mem_add, Multiset.mem_map] at he'
    rcases he' with he_old | ⟨⟨q, m⟩, hqm, rfl⟩
    · obtain ⟨hsrcF, hprop_old⟩ := hinv.msgs_auth e (hbase e he_old)
      exact ⟨hsrcF, hprop_mono_all e.src hsrcF e.body.round e.body.val hprop_old⟩
    · refine ⟨hdest, ?_⟩
      simp only [tagSender_src, tagSender_body]
      rw [hproc_state dest, ite_eq_left rfl]
      exact hout_d q m hqm
  · intro p hpF j hjF r v hv
    rw [hproc_state p] at hv
    by_cases hpd : p = dest
    · rw [ite_eq_left hpd] at hv
      exact hheard_d j hjF r v hv
    · rw [ite_eq_right hpd] at hv
      exact hprop_mono_all j hjF r v (hinv.heard_auth p hpF j hjF r v hv)
  · intro h1 p hpF
    rw [hproc_state p]
    by_cases hpd : p = dest
    · rw [ite_eq_left hpd]
      exact hstop_d h1
    · rw [ite_eq_right hpd]
      exact hinv.stop_cond h1 p hpF
  · intro p hpF
    by_cases hpd : p = dest
    · subst hpd
      refine ⟨fun v hv => ?_, fun hR => ?_⟩
      · rw [hproc_state p, ite_eq_left rfl]
        exact hout_spec_d.1 v hv
      · rw [hproc_state p, ite_eq_left rfl]
        exact hout_spec_d.2 hR
    · have hout_p : (s'.proc p).out = (s.proc p).out := by
        rw [hproc_out_eq p, ite_eq_right hpd]
      refine ⟨fun v hv => ?_, fun hR => ?_⟩
      · change (s'.proc p).out = some v at hv
        rw [hout_p] at hv
        exact hprop_mono_all p hpF R v ((hinv.out_spec p hpF).1 v hv)
      · rw [hproc_state p, ite_eq_right hpd, hout_p]
        exact (hinv.out_spec p hpF).2 hR

private lemma asyncInv_reachable {F : Finset P} {t R : ℕ} {x : P → K}
    {s : State P (AsyncApproxState P K) (RoundMsg K) K}
    (hr : (asyncApproxProtocol P K t R).Reachable F x s) :
    AsyncInv F t R x s := by
  obtain ⟨xl, hxl⟩ := hr
  have htr : ((asyncApproxProtocol P K t R).lts F).TrInv (AsyncInv F t R x) := by
    intro s₁ a s₂ hstep hinv
    cases a with
    | deliver e =>
      obtain ⟨he_mem, he_dest, rfl⟩ := hstep
      exact asyncInv_recvCore hinv he_dest
        (fun _ hm => Multiset.mem_of_mem_erase hm)
        (fun _ => (hinv.msgs_auth e he_mem).2)
    | byzRecv src dest body =>
      obtain ⟨hsrcF, hdest, rfl⟩ := hstep
      exact asyncInv_recvCore hinv hdest (fun _ hm => hm)
        (fun hnot => absurd hsrcF hnot)
    | stutter =>
      obtain rfl := hstep
      exact hinv
  exact LTS.mtrInv_of_trInv htr _ _ _ hxl (asyncInv_start F t R x)

/-! ### Monotonicity and round-by-round liveness helpers along `AdmissibleRun` -/

private lemma tr_state_mono {F : Finset P} {t R : ℕ} {x : P → K}
    {s₁ s₂ : State P (AsyncApproxState P K) (RoundMsg K) K}
    {a : Action P (RoundMsg K)} (hwf : ∀ p ∉ F, WellFormedLocal t R (x p) (s₁.proc p).state)
    (htr : ((asyncApproxProtocol P K t R).lts F).Tr s₁ a s₂) {p : P} (hpF : p ∉ F) :
    (s₁.proc p).state.round ≤ (s₂.proc p).state.round ∧
    (∀ r j, ((s₁.proc p).state.heard r j).isSome → ((s₂.proc p).state.heard r j).isSome) := by
  cases a with
  | deliver e =>
    obtain ⟨_, _, rfl⟩ := htr
    simp only [AsyncProtocol.recvHonest, AsyncProtocol.recvCore, AsyncProtocol.updateProc,
      asyncApproxProtocol]
    by_cases hpe : p = e.dest
    · obtain ⟨h1, _, h3⟩ := step_mono (t := t) (R := R) (hwf p hpF) e.src e.body
      subst hpe
      simp only [↓reduceIte]
      refine ⟨h1, fun r j hs => ?_⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      rw [h3 r j v hv]
      rfl
    · simp only [hpe, ↓reduceIte]
      exact ⟨le_rfl, fun _ _ h => h⟩
  | byzRecv src dest body =>
    obtain ⟨_, _, rfl⟩ := htr
    simp only [AsyncProtocol.recvByz, AsyncProtocol.recvCore, AsyncProtocol.updateProc,
      asyncApproxProtocol]
    by_cases hpd : p = dest
    · obtain ⟨h1, _, h3⟩ := step_mono (t := t) (R := R) (hwf p hpF) src body
      subst hpd
      simp only [↓reduceIte]
      refine ⟨h1, fun r j hs => ?_⟩
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hs
      rw [h3 r j v hv]
      rfl
    · simp only [hpd, ↓reduceIte]
      exact ⟨le_rfl, fun _ _ h => h⟩
  | stutter =>
    obtain rfl := htr
    exact ⟨le_rfl, fun _ _ h => h⟩

private lemma omega_state_mono {F : Finset P} {t R : ℕ} {x : P → K}
    {ss : ωSequence (State P (AsyncApproxState P K) (RoundMsg K) K)}
    {xs : ωSequence (Action P (RoundMsg K))}
    (ha : (asyncApproxProtocol P K t R).AdmissibleRun F x ss xs)
    {k₁ k₂ : ℕ} (hle : k₁ ≤ k₂) {p : P} (hpF : p ∉ F) :
    ((ss k₁).proc p).state.round ≤ ((ss k₂).proc p).state.round ∧
    (∀ r j, (((ss k₁).proc p).state.heard r j).isSome →
      (((ss k₂).proc p).state.heard r j).isSome) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction d with
  | zero => simp only [Nat.add_zero]; exact ⟨le_rfl, fun _ _ h => h⟩
  | succ d ih =>
    have hwf := (asyncInv_reachable
      ((asyncApproxProtocol P K t R).admissibleRun_reachable ha (k₁ + d))).wf
    obtain ⟨hr1, hh1⟩ := ih (Nat.le_add_right k₁ d)
    obtain ⟨hr2, hh2⟩ := tr_state_mono hwf (ha.2.1 (k₁ + d)) hpF
    exact ⟨hr1.trans hr2, fun r j h => hh2 r j (hh1 r j h)⟩

/-- Whenever honest `q ∉ F` has reached round `r < R` by step `m`, `q` emitted a round-`r`
envelope to `p` into `(ss k₀).msgs` at some step `k₀ ≤ m`. -/
private lemma exists_round_msg_emitted {F : Finset P} {t R : ℕ} {x : P → K}
    {ss : ωSequence (State P (AsyncApproxState P K) (RoundMsg K) K)}
    {xs : ωSequence (Action P (RoundMsg K))}
    (ha : (asyncApproxProtocol P K t R).AdmissibleRun F x ss xs)
    {r : ℕ} (hrR : r < R) {q : P} (hqF : q ∉ F) (p : P) :
    ∀ m, r ≤ ((ss m).proc q).state.round →
      ∃ k₀ ≤ m, ∃ v : K, (⟨q, p, ⟨r, v⟩⟩ : Envelope P (RoundMsg K)) ∈ (ss k₀).msgs
  | 0, hr0 => by
    have h0 : ((ss 0).proc q).state.round = 0 := by
      rw [ha.1]; rfl
    have hr_eq : r = 0 := by omega
    subst hr_eq
    refine ⟨0, le_rfl, x q, ?_⟩
    rw [ha.1]
    simp only [AsyncProtocol.start, asyncApproxProtocol, Multiset.mem_bind, Finset.mem_val,
      Finset.mem_univ, true_and]
    refine ⟨q, ?_⟩
    simp only [hqF, ↓reduceIte]
    exact mem_broadcastAll_tag q p (RoundMsg.mk 0 (x q))
  | m + 1, hrm => by
    by_cases hprev : r ≤ ((ss m).proc q).state.round
    · obtain ⟨k₀, hk₀, v, hv⟩ := exists_round_msg_emitted ha hrR hqF p m hprev
      exact ⟨k₀, hk₀.trans (Nat.le_succ m), v, hv⟩
    · have hlt : ((ss m).proc q).state.round < r := Nat.lt_of_not_le hprev
      have hr_pos : 0 < r := Nat.zero_lt_of_lt hlt
      have htr := ha.2.1 m
      have hwfm := (asyncInv_reachable
        ((asyncApproxProtocol P K t R).admissibleRun_reachable ha m)).wf q hqF
      -- Extract the single step on `q` that increased `q`'s round across `r`.
      have hstep_emit : ∀ (src : P) (body : RoundMsg K)
          (msgsBase : Multiset (Envelope P (RoundMsg K))),
          ss (m + 1) = (asyncApproxProtocol P K t R).recvCore src q body msgsBase (ss m) →
          ∃ v : K, (⟨q, p, ⟨r, v⟩⟩ : Envelope P (RoundMsg K)) ∈ (ss (m + 1)).msgs := by
        intro src body msgsBase hs_eq
        set st₀ := ((ss m).proc q).state
        have hrm' : r ≤ (asyncApproxStep t R st₀ src body).nextState.round := by
          rw [hs_eq] at hrm
          simpa only [AsyncProtocol.recvCore, AsyncProtocol.updateProc,
            asyncApproxProtocol, ↓reduceIte, st₀] using hrm
        have hR0 : R ≠ 0 := by omega
        by_cases hfresh :
            st₀.round ≤ body.round ∧ body.round < R ∧ (st₀.heard body.round src).isNone
        · set st₁ := recordHeard st₀ body.round src body.val
          have hst₁_r : st₁.round = st₀.round := rfl
          have hstep_eq : asyncApproxStep t R st₀ src body =
              asyncApproxAdvance t R (R - st₁.round) st₁ := by
            dsimp only [st₁]
            simp only [asyncApproxStep, hR0, hfresh, and_self, ↓reduceIte]
          rw [hstep_eq] at hrm'
          have hwf₁ := wellFormedLocal_recordHeard hwfm hfresh.1 src body.val
          obtain ⟨_, _, _, hstep_n, _, _, _⟩ :=
            advance_spec (t := t) (R := R) (R - st₁.round) st₁ hwf₁ le_rfl
          have hr1_ge : st₁.round ≤ r - 1 := by omega
          have hr1_le : (r - 1) + 1 ≤
              (asyncApproxAdvance t R (R - st₁.round) st₁).nextState.round := by omega
          have hr1_lt : (r - 1) + 1 < R := by omega
          have hmem_out := hstep_n (r - 1) hr1_ge hr1_le hr1_lt p
          have hr_sub : (r - 1) + 1 = r := Nat.sub_add_cancel hr_pos
          rw [hr_sub] at hmem_out
          refine ⟨multisetMidTrim t (roundValues st₁ (r - 1)), ?_⟩
          rw [hs_eq]
          change _ ∈ msgsBase + (asyncApproxStep t R st₀ src body).outgoing.map (tagSender q)
          rw [hstep_eq, Multiset.mem_add]
          exact Or.inr (Multiset.mem_map.mpr
            ⟨(p, ⟨r, multisetMidTrim t (roundValues st₁ (r - 1))⟩), hmem_out, rfl⟩)
        · have hstep_eq : asyncApproxStep t R st₀ src body = ⟨st₀, 0, none⟩ := by
            simp only [asyncApproxStep, hR0, hfresh, ↓reduceIte]
          rw [hstep_eq] at hrm'
          dsimp only at hrm'
          omega
      cases hact : xs m with
      | deliver e =>
        rw [hact] at htr
        obtain ⟨_, _, hnext⟩ := htr
        by_cases hqe : q = e.dest
        · subst hqe
          obtain ⟨v, hv⟩ := hstep_emit e.src e.body ((ss m).msgs.erase e) hnext
          exact ⟨m + 1, le_rfl, v, hv⟩
        · rw [hnext] at hrm
          simp only [AsyncProtocol.recvHonest, AsyncProtocol.recvCore, hqe, ↓reduceIte] at hrm
          omega
      | byzRecv src dest body =>
        rw [hact] at htr
        obtain ⟨_, _, hnext⟩ := htr
        by_cases hqd : q = dest
        · subst hqd
          obtain ⟨v, hv⟩ := hstep_emit src body (ss m).msgs hnext
          exact ⟨m + 1, le_rfl, v, hv⟩
        · rw [hnext] at hrm
          simp only [AsyncProtocol.recvByz, AsyncProtocol.recvCore, hqd, ↓reduceIte] at hrm
          omega
      | stutter =>
        rw [hact] at htr
        rw [htr] at hrm
        omega

/-- Once `⟨q, p, ⟨r, v⟩⟩` (`r < R`, `p ∉ F`) enters `(ss k₀).msgs` in a fair run (`R > 0`), at
some step `J` process `p` either has already advanced past round `r` (`r < round`) or has recorded
`q` in `heard r`. -/
private lemma exists_round_gt_or_heard_isSome {F : Finset P} {t R : ℕ} {x : P → K}
    (hR : 0 < R)
    {ss : ωSequence (State P (AsyncApproxState P K) (RoundMsg K) K)}
    {xs : ωSequence (Action P (RoundMsg K))}
    (ha : (asyncApproxProtocol P K t R).AdmissibleRun F x ss xs)
    {k₀ r : ℕ} (hrR : r < R) {q p : P} (hpF : p ∉ F) {v : K}
    (he_mem : (⟨q, p, ⟨r, v⟩⟩ : Envelope P (RoundMsg K)) ∈ (ss k₀).msgs) :
    ∃ J, r < ((ss J).proc p).state.round ∨ (((ss J).proc p).state.heard r q).isSome := by
  let e : Envelope P (RoundMsg K) := ⟨q, p, ⟨r, v⟩⟩
  obtain ⟨j, _, hj⟩ := ha.2.2 e hpF k₀ he_mem
  have htr : ((asyncApproxProtocol P K t R).lts F).Tr (ss j) (.deliver e) (ss (j + 1)) :=
    hj ▸ ha.2.1 j
  obtain ⟨_, _, hnext⟩ := htr
  refine ⟨j + 1, ?_⟩
  have hwf_j := (asyncInv_reachable
    ((asyncApproxProtocol P K t R).admissibleRun_reachable ha j)).wf p hpF
  by_cases hr_past : r < ((ss j).proc p).state.round
  · exact Or.inl (lt_of_lt_of_le hr_past (omega_state_mono ha (Nat.le_add_right j 1) hpF).1)
  · have hr_ge : ((ss j).proc p).state.round ≤ r := Nat.le_of_not_lt hr_past
    by_cases hprev_some : (((ss j).proc p).state.heard r q).isSome
    · exact Or.inr ((omega_state_mono ha (Nat.le_add_right j 1) hpF).2 r q hprev_some)
    · have hnone : (((ss j).proc p).state.heard r q).isNone :=
        Option.not_isSome_iff_eq_none.mp hprev_some ▸ Option.isNone_none
      refine Or.inr ?_
      rw [hnext]
      have hR0 : R ≠ 0 := by omega
      set st₀ := ((ss j).proc p).state
      have hfresh : st₀.round ≤ r ∧ r < R ∧ (st₀.heard r q).isNone := ⟨hr_ge, hrR, hnone⟩
      set st₁ := recordHeard st₀ r q v
      have hproc_p : (((asyncApproxProtocol P K t R).recvHonest e (ss j)).proc p).state =
          (asyncApproxStep t R st₀ q ⟨r, v⟩).nextState := by
        dsimp only [e, st₀]
        simp only [AsyncProtocol.recvHonest, AsyncProtocol.recvCore, AsyncProtocol.updateProc,
          asyncApproxProtocol, ↓reduceIte]
      have hstep_eq : asyncApproxStep t R st₀ q ⟨r, v⟩ =
          asyncApproxAdvance t R (R - st₁.round) st₁ := by
        dsimp only [st₁]
        simp only [asyncApproxStep, hR0, hfresh, and_self, ↓reduceIte]
      rw [hproc_p, hstep_eq]
      have hwf₁ := wellFormedLocal_recordHeard hwf_j hr_ge q v
      obtain ⟨_, _, hheard_eq, _, _, _, _⟩ :=
        advance_spec (t := t) (R := R) (R - st₁.round) st₁ hwf₁ le_rfl
      rw [hheard_eq]
      simp only [st₁, recordHeard, Function.update_self, Option.isSome_some]

/-! ### Public correctness theorems for `asyncApproxProtocol` -/

/-- **Asynchronous fair-delivery termination:** when `F.card ≤ t` and `t < Fintype.card P` (so in
particular whenever `5 * t < Fintype.card P`), in every admissible (fair) execution of
`asyncApproxProtocol P K t R` every correct process `i ∉ F` eventually outputs a value. -/
theorem asyncApproxProtocol_terminates {t R : ℕ} (ht : t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) (x : P → K)
    {ss : ωSequence (State P (AsyncApproxState P K) (RoundMsg K) K)}
    {xs : ωSequence (Action P (RoundMsg K))}
    (ha : (asyncApproxProtocol P K t R).AdmissibleRun F x ss xs)
    {i : P} (hiF : i ∉ F) :
    ∃ n v, (ss n).ProcDecided i v := by
  by_cases hR0 : R = 0
  · subst hR0
    let e : Envelope P (RoundMsg K) := ⟨i, i, ⟨0, x i⟩⟩
    have he0 : e ∈ (ss 0).msgs := by
      rw [ha.1]
      simp only [AsyncProtocol.start, asyncApproxProtocol, Multiset.mem_bind, Finset.mem_val,
        Finset.mem_univ, true_and]
      refine ⟨i, ?_⟩
      simp only [hiF, ↓reduceIte]
      exact mem_broadcastAll_tag i i (RoundMsg.mk 0 (x i))
    obtain ⟨j, _, hj⟩ := ha.2.2 e hiF 0 he0
    have htr : ((asyncApproxProtocol P K t 0).lts F).Tr (ss j) (.deliver e) (ss (j + 1)) :=
      hj ▸ ha.2.1 j
    obtain ⟨_, _, hnext⟩ := htr
    cases hout : ((ss j).proc i).out with
    | some v =>
      exact ⟨j, v, hout⟩
    | none =>
      refine ⟨j + 1, ((ss j).proc i).state.est, ?_⟩
      simp only [State.ProcDecided, hnext, AsyncProtocol.recvHonest, AsyncProtocol.recvCore,
        AsyncProtocol.updateProc, asyncApproxProtocol, asyncApproxStep, e, ↓reduceIte,
        hout, Option.isNone_none]
  · have hR : 0 < R := Nat.pos_of_ne_zero hR0
    have h1 : 1 ≤ Fintype.card P - t := by omega
    -- Prove by induction on `r ≤ R` that all correct processes eventually reach round `r`.
    have hall_reach : ∀ r ≤ R, ∃ K_r, ∀ k, K_r ≤ k → ∀ p ∉ F,
        r ≤ ((ss k).proc p).state.round := by
      intro r hr_le
      induction r with
      | zero => exact ⟨0, fun _ _ _ _ => Nat.zero_le _⟩
      | succ r ih =>
        have hr_lt : r < R := Nat.lt_of_succ_le hr_le
        obtain ⟨K_r, hK_r⟩ := ih (Nat.le_of_lt hr_lt)
        let H : Finset P := Finset.univ \ F
        have hex_pair : ∀ qp : P × P,
            ∃ J : ℕ, qp.1 ∈ H → qp.2 ∈ H →
              r < ((ss J).proc qp.2).state.round ∨
                (((ss J).proc qp.2).state.heard r qp.1).isSome := by
          intro ⟨q, p⟩
          by_cases hqp : q ∈ H ∧ p ∈ H
          · have hqF : q ∉ F := (Finset.mem_sdiff.mp hqp.1).2
            have hpF : p ∉ F := (Finset.mem_sdiff.mp hqp.2).2
            obtain ⟨k₀, _, v, he_mem⟩ :=
              exists_round_msg_emitted ha hr_lt hqF p K_r (hK_r K_r le_rfl q hqF)
            obtain ⟨J, hJ⟩ := exists_round_gt_or_heard_isSome hR ha hr_lt hpF he_mem
            exact ⟨J, fun _ _ => hJ⟩
          · exact ⟨0, fun hq hp => absurd ⟨hq, hp⟩ hqp⟩
        choose Jfn hJfn using hex_pair
        let K_next := max K_r ((H ×ˢ H).sup Jfn)
        refine ⟨K_next, fun k hk p hpF => ?_⟩
        have hk_Kr : K_r ≤ k := (le_max_left _ _).trans hk
        have hp_ge_r : r ≤ ((ss k).proc p).state.round := hK_r k hk_Kr p hpF
        have hpH : p ∈ H := Finset.mem_sdiff.mpr ⟨Finset.mem_univ p, hpF⟩
        by_cases hp_gt : r + 1 ≤ ((ss k).proc p).state.round
        · exact hp_gt
        · have hall_heard : H ⊆ roundSenders ((ss k).proc p).state r := by
            intro q hqH
            have hq_pair : (q, p) ∈ H ×ˢ H := Finset.mem_product.mpr ⟨hqH, hpH⟩
            have hJ_le : Jfn (q, p) ≤ k :=
              (Finset.le_sup hq_pair).trans ((le_max_right _ _).trans hk)
            have hdisj := hJfn (q, p) hqH hpH
            dsimp only at hdisj
            obtain ⟨hrmono, hhmono⟩ := omega_state_mono ha hJ_le hpF
            rcases hdisj with hr_already | hsome
            · omega
            · simp only [roundSenders, Finset.mem_filter, Finset.mem_univ, true_and]
              exact hhmono r q hsome
          have hH_card : Fintype.card P - t ≤ H.card := by
            have hsdiff := Finset.le_card_sdiff F Finset.univ
            rw [Finset.card_univ] at hsdiff
            change Fintype.card P - t ≤ (Finset.univ \ F).card
            omega
          have hsenders_ge : Fintype.card P - t ≤ (roundSenders ((ss k).proc p).state r).card :=
            hH_card.trans (Finset.card_le_card hall_heard)
          have hstop := (asyncInv_reachable
            ((asyncApproxProtocol P K t R).admissibleRun_reachable ha k)).stop_cond h1 p hpF
          have heq_r : ((ss k).proc p).state.round = r := by omega
          rcases hstop with hR_eq | hlt_card
          · omega
          · rw [heq_r] at hlt_card
            omega
    obtain ⟨K_R, hK_R⟩ := hall_reach R le_rfl
    have hinv_KR := asyncInv_reachable
      ((asyncApproxProtocol P K t R).admissibleRun_reachable ha K_R)
    have hround_eq : ((ss K_R).proc i).state.round = R := by
      have hge := hK_R K_R le_rfl i hiF
      have hle := (hinv_KR.wf i hiF).round_le
      omega
    have hisSome : ((ss K_R).proc i).out.isSome :=
      ((hinv_KR.out_spec i hiF).2 hR).mp hround_eq
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hisSome
    exact ⟨K_R, v, hv⟩

section AsyncOrderedField

variable [IsStrictOrderedRing K]

private lemma asyncApprox_exists_Icc {t R : ℕ} (h5t : 5 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {x : P → K}
    {lo hi : K} (hlh : lo ≤ hi) (hx : ∀ k ∉ F, x k ∈ Set.Icc lo hi)
    {s : State P (AsyncApproxState P K) (RoundMsg K) K}
    (hr : (asyncApproxProtocol P K t R).Reachable F x s) :
    ∃ lo_R hi_R : K,
      lo ≤ lo_R ∧ lo_R ≤ hi_R ∧ hi_R ≤ hi ∧
      hi_R - lo_R ≤ (hi - lo) / 2 ^ R ∧
      ∀ i ∉ F, ∀ v, s.ProcDecided i v → v ∈ Set.Icc lo_R hi_R := by
  have hinv := asyncInv_reachable hr
  let prop : ℕ → P → Option K := fun r p => localProposal t (x p) (s.proc p).state r
  obtain ⟨lo_R, hi_R, hlo, hlh_R, hhi, hw, hmem⟩ :=
    exists_Icc_of_roundMidTrim (P := P) (K := K) (F := F) (t := t) (m := Fintype.card P - t)
      hF (by omega) (prop := prop) hlh
      (fun p hpF v hv => by
        dsimp only [prop, localProposal] at hv
        exact (Option.some.inj hv.symm) ▸ hx p hpF)
      (fun r p hpF w hw => by
        dsimp only [prop, localProposal] at hw
        by_cases hr_le : r + 1 ≤ (s.proc p).state.round
        · rw [ite_eq_left hr_le, Option.some.injEq] at hw
          refine ⟨roundSenders (s.proc p).state r,
            fun q => ((s.proc p).state.heard r q).getD 0,
            (hinv.wf p hpF).past_senders r hr_le, hw.symm, fun q hqS hqF => ?_⟩
          obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (Finset.mem_filter.mp hqS).2
          exact ⟨v, hinv.heard_auth p hpF q hqF r v hv, by simp only [hv, Option.getD_some]⟩
        · rw [ite_eq_right hr_le] at hw
          cases hw)
      R
  refine ⟨lo_R, hi_R, hlo, hlh_R, hhi, hw, fun i hiF v hdec => ?_⟩
  exact hmem i hiF v ((hinv.out_spec i hiF).1 v hdec)

/-- **Asynchronous convex-hull validity:** when `5 * t < Fintype.card P`, in every reachable state
`s` of `asyncApproxProtocol P K t R`, if all correct inputs lie in `[lo, hi]`, then any value `v`
decided by a correct process `i ∉ F` lies in `[lo, hi]`. -/
theorem asyncApproxProtocol_mem_Icc {t R : ℕ} (h5t : 5 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {x : P → K}
    {lo hi : K} (hx : ∀ k ∉ F, x k ∈ Set.Icc lo hi)
    {s : State P (AsyncApproxState P K) (RoundMsg K) K}
    (hr : (asyncApproxProtocol P K t R).Reachable F x s)
    {i : P} (hiF : i ∉ F) {v : K} (hdec : s.ProcDecided i v) :
    v ∈ Set.Icc lo hi := by
  have hlh : lo ≤ hi := (hx i hiF).1.trans (hx i hiF).2
  obtain ⟨lo_R, hi_R, hlo, _, hhi, _, hmem⟩ := asyncApprox_exists_Icc h5t hF hlh hx hr
  exact ⟨hlo.trans (hmem i hiF v hdec).1, (hmem i hiF v hdec).2.trans hhi⟩

/-- **Asynchronous multi-round contraction:** when `5 * t < Fintype.card P`, in every reachable
state `s` of `asyncApproxProtocol P K t R`, if all correct inputs lie in `[lo, hi]`, then any two
values `v₁, v₂` decided by correct processes `i, j ∉ F` satisfy `|v₁ - v₂| ≤ (hi - lo) / 2 ^ R`. -/
theorem asyncApproxProtocol_abs_sub_le {t R : ℕ} (h5t : 5 * t < Fintype.card P)
    {F : Finset P} (hF : F.card ≤ t) {x : P → K}
    {lo hi : K} (hx : ∀ k ∉ F, x k ∈ Set.Icc lo hi)
    {s : State P (AsyncApproxState P K) (RoundMsg K) K}
    (hr : (asyncApproxProtocol P K t R).Reachable F x s)
    {i j : P} (hiF : i ∉ F) (hjF : j ∉ F)
    {v₁ v₂ : K} (h₁ : s.ProcDecided i v₁) (h₂ : s.ProcDecided j v₂) :
    |v₁ - v₂| ≤ (hi - lo) / 2 ^ R := by
  have hlh : lo ≤ hi := (hx i hiF).1.trans (hx i hiF).2
  obtain ⟨lo_R, hi_R, _, _, _, hw, hmem⟩ := asyncApprox_exists_Icc h5t hF hlh hx hr
  obtain ⟨h1_lo, h1_hi⟩ := hmem i hiF v₁ h₁
  obtain ⟨h2_lo, h2_hi⟩ := hmem j hjF v₂ h₂
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- Unit-interval, fixed-horizon step toward `#7116` and `#3261` (after Algorithm $A_0$ in Section 4
of [Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986]): when
`5 * t < Fintype.card P` and `(1 : K) / 2 ^ R ≤ ε`, `asyncApproxProtocol P K t R` achieves
`SolvesUnitAsyncApproxAgreement t ε`. -/
theorem solvesUnitAsyncApproxAgreement_asyncApprox {t R : ℕ} {ε : K}
    (h5t : 5 * t < Fintype.card P) (hR : (1 : K) / 2 ^ R ≤ ε) :
    (asyncApproxProtocol P K t R).SolvesUnitAsyncApproxAgreement t ε where
  termination _ hF x _ _ _ ha _ hiF :=
    asyncApproxProtocol_terminates (by omega) hF x ha hiF
  validity _ hF _ _ _ _ hIcc _ hr _ hiF _ hv :=
    asyncApproxProtocol_mem_Icc h5t hF hIcc hr hiF hv
  agreement _ hF _ hx _ hr _ hiF _ hjF _ _ h₁ h₂ := by
    have hsub := asyncApproxProtocol_abs_sub_le h5t hF hx hr hiF hjF h₁ h₂
    rw [sub_zero] at hsub
    exact hsub.trans hR

end AsyncOrderedField

end AsyncProofs

/-- **Unit-interval fixed-horizon asynchronous approximate Byzantine agreement** (milestone step
toward `#7116` and `#3261` after Algorithm $A_0$ in Section 4, p. 509 of
[Dolev, Lynch, Pinter, Stark and Weihl][DolevLynchPinterStarkWeihl1986], rather than that paper's
unbounded-input, dynamically halting Algorithm $A$ / Theorem 2): over any Archimedean linearly
ordered field `K`, for every `0 < ε` and `Fintype.card P ≤ 1 ∨ 5 * t < Fintype.card P`, there
exists a deterministic asynchronous protocol solving `SolvesUnitAsyncApproxAgreement t ε`
(`AsyncProtocol.ownInput` for `|P| ≤ 1`, and fixed-horizon `asyncApproxProtocol P K t R` with
`(1 : K) / 2 ^ R ≤ ε` for `5 * t < |P|`), contrasting with exact consensus impossibility
(`Cslib.FLP`) even on `[0, 1]` inputs. -/
theorem exists_solvesUnitAsyncApproxAgreement.{u, v} (P : Type u) (K : Type v)
    [Fintype P] [DecidableEq P]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Archimedean K]
    (t : ℕ) {ε : K} (hε : 0 < ε) (hn : Fintype.card P ≤ 1 ∨ 5 * t < Fintype.card P) :
    ∃ (S : Type (max u v)) (M : Type v) (_ : DecidableEq M) (π : AsyncProtocol P K S M),
      π.SolvesUnitAsyncApproxAgreement t ε := by
  rcases hn with h1 | h5t
  · have : Subsingleton P := Fintype.card_le_one_iff_subsingleton.mp h1
    exact ⟨ULift.{u} K, PUnit.{v + 1}, inferInstance, AsyncProtocol.ownInput P K,
      AsyncProtocol.solvesUnitAsyncApproxAgreement_ownInput t hε.le⟩
  · obtain ⟨R, hR⟩ := exists_one_div_two_pow_le hε
    exact ⟨AsyncApproxState P K, RoundMsg K, inferInstance, asyncApproxProtocol P K t R,
      solvesUnitAsyncApproxAgreement_asyncApprox h5t hR⟩

end Cslib.Distributed.ApproxAgreement
