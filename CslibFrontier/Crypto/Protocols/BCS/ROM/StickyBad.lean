/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM.State
public import CslibFrontier.Languages.Probabilistic.UntilBad.TwoCost
import CslibFrontier.Foundations.Data.List.Counting
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Languages.Probabilistic.QueryCount.Sum
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.UniformBound
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.List.GetD

/-!
# Forbidden Merkle digests, out-of-order Fiat–Shamir targets, and bad-state bounds for `bcsMemoize`

Bounds the single-step and accumulated probability that an adaptive two-channel BCS random-oracle
execution violates `BCSGoodState`, using `bcsForbiddenDigests` (restricted to the first `r` roots of
each Fiat–Shamir query) on the Merkle channel, `fsOutOfOrderTargets` on the Fiat–Shamir channel, and
a private sticky-bad handler wrapper `bcsStickyMemoize` analyzed via
`OracleComp.toOuterMeasure_bad_le_two_budgets` ([BenSassonChiesaSpooner2016]; compare
[ChiesaYogev2024], Chapters 18, 25, 26, and 31).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.bcsForbiddenDigests`: digests that a fresh Merkle hash answer must
  avoid to preserve `BCSGoodState` and root-extraction stability.
* `Cslib.Crypto.Protocols.BCS.fsOutOfOrderTargets`: previously queried challenge components that
  bound out-of-order Fiat–Shamir chain guessing.

## Main results

* `Cslib.Crypto.Protocols.BCS.length_bcsForbiddenDigests_le`,
  `Cslib.Crypto.Protocols.BCS.mem_bcsForbiddenDigests_of_not_bcsGoodState_cons`,
  `Cslib.Crypto.Protocols.BCS.length_fsOutOfOrderTargets_le`: cardinality and bad-transition
  containment bounds for `bcsForbiddenDigests` and `fsOutOfOrderTargets`.
* `Cslib.Crypto.Protocols.BCS.toOuterMeasure_memoize_not_bcsChainDoomed_step`,
  `Cslib.Crypto.Protocols.BCS.toOuterMeasure_bcsMemoize_not_goodState_step`,
  `Cslib.Crypto.Protocols.BCS.toOuterMeasure_run_bcsMemoize_not_goodState_le`: single-step and
  two-budget accumulated outer-measure bounds on violating `BCSGoodState` under `bcsMemoize`.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapters 18, 25, 26, and 31.
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Turing.MultiTapeTM Cslib.Probability Cslib.OracleComp
open scoped ENNReal

/-- Digests that a fresh Merkle hash output must avoid to preserve `BCSGoodState`: existing Merkle
outputs, left/right child digests of existing Merkle queries, and the first `r` roots of every
existing Fiat–Shamir query. Restricting each Fiat–Shamir entry via `List.take r` makes the list
length independent of adversarial Fiat–Shamir root-list sizes. -/
@[expose] def bcsForbiddenDigests (r : ℕ) {Stmt Chal : Type}
    (st : BCSTraceState Stmt Chal) : List (List Bool) :=
  st.1.map Prod.snd ++ st.1.map (fun (q, _) => unframe q) ++
    st.1.map (fun (q, _) => dropFrame q) ++
    st.2.flatMap (fun ((_, rts, _), _) => rts.take r)

theorem length_bcsForbiddenDigests_le (r : ℕ) {Stmt Chal : Type}
    (st : BCSTraceState Stmt Chal) :
    (bcsForbiddenDigests r st).length ≤ 3 * st.1.length + r * st.2.length := by
  have hfs : (st.2.flatMap (fun ((_, rts, _), _) => rts.take r)).length ≤ r * st.2.length := by
    simpa only [Nat.mul_comm] using List.length_flatMap_le (l := st.2)
      (f := fun ((_, rts, _), _) => rts.take r) (k := r)
      fun ⟨⟨_, rts, _⟩, _⟩ _ => List.length_take_le r rts
  unfold bcsForbiddenDigests
  rw [List.length_append, List.length_append, List.length_append,
    List.length_map, List.length_map, List.length_map]
  omega

private theorem mem_bcsForbiddenDigests_not_elim {r : ℕ} {Stmt Chal : Type}
    {tr_MT : List (List Bool × List Bool)} {tr_FS : List (BCSFSQuery Stmt Chal × Chal)}
    {ans : List Bool} (hnot : ans ∉ bcsForbiddenDigests r (tr_MT, tr_FS)) :
    (∀ p ∈ tr_MT, p.2 ≠ ans) ∧
      (∀ p ∈ tr_MT, ans ≠ unframe p.1 ∧ ans ≠ dropFrame p.1) ∧
      (ans ∉ tr_FS.flatMap (fun ((_, rts, _), _) => rts.take r)) := by
  simp only [bcsForbiddenDigests, List.mem_append, List.mem_map, not_or, not_exists,
    not_and] at hnot
  rcases hnot with ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
  exact ⟨h1, fun ⟨q, d'⟩ hp => ⟨fun h => h2 (q, d') hp h.symm, fun h => h3 (q, d') hp h.symm⟩, h4⟩

/-- If `BCSGoodState` holds on `st` and prepending `(msg, ans)` to `st.1` violates `BCSGoodState`,
then `ans` belongs to `bcsForbiddenDigests r st`. -/
theorem mem_bcsForbiddenDigests_of_not_bcsGoodState_cons {r d : ℕ} {Stmt Sym Chal : Type}
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {decSym : List Bool → Sym} {defaultSym : Sym}
    {st : BCSTraceState Stmt Chal} {msg ans : List Bool}
    (hgood : BCSGoodState r d S doomed decSym defaultSym st)
    (hbad : ¬ BCSGoodState r d S doomed decSym defaultSym ((msg, ans) :: st.1, st.2)) :
    ans ∈ bcsForbiddenDigests r st := by
  rcases st with ⟨tr_MT, tr_FS⟩
  by_contra hnot_mem
  obtain ⟨hsnd, hchildren, hfs⟩ := mem_bcsForbiddenDigests_not_elim hnot_mem
  refine hbad ⟨traceCollisionFree_cons_iff.mpr ⟨hgood.1, fun p hp heq => (hsnd p hp heq).elim⟩,
    fun x hx rts chals hr hchain => ?_⟩
  rcases rts with _ | ⟨rt₀, rest⟩
  · exact hgood.2 x hx [] chals hr hchain
  · obtain ⟨hlen, hsteps⟩ := hchain
    have hlast_mem : ((x, rt₀ :: rest, chals.take rest.length),
        chals[rest.length]'(by simpa using hlen ▸ Nat.lt_succ_self rest.length)) ∈ tr_FS := by
      simpa [List.take_length] using hsteps rest.length (Nat.lt_succ_self rest.length)
    have hrts : ∀ rt ∈ rt₀ :: rest, ans ≠ rt := fun rt hrt heq =>
      hfs <| List.mem_flatMap.mpr
        ⟨_, hlast_mem, by dsimp only; rwa [List.take_of_length_le hr, heq]⟩
    rw [bcsExtractTranscript_cons_of_ne decSym defaultSym d tr_MT msg chals hrts hchildren]
    exact hgood.2 x hx (rt₀ :: rest) chals hr ⟨hlen, hsteps⟩

/-- Candidate challenges at challenge-list index `idx` already anticipated by existing Fiat–Shamir
trace entries (used to bound out-of-order Fiat–Shamir chain guessing). -/
@[expose] def fsOutOfOrderTargets {Stmt Chal : Type} (idx : ℕ)
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) : List Chal :=
  tr_FS.filterMap fun ((_, _, prev), _) => prev[idx]?

theorem length_fsOutOfOrderTargets_le {Stmt Chal : Type} (idx : ℕ)
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) :
    (fsOutOfOrderTargets idx tr_FS).length ≤ tr_FS.length :=
  List.length_filterMap_le _ _

/-- Structural analysis of a fresh Fiat–Shamir entry `((x₀, rts₀, prev₀), c)` violating
`BCSChainDoomed`: `x₀ ∈ S`, and either `c` hits `fsOutOfOrderTargets (rts₀.length - 1) tr_FS` (an
out-of-order longer chain was already queried) or the parent prefix is already `doomed` and `c`
violates `goodStep`. -/
private theorem bad_fs_step_cases {r d : ℕ} {Stmt Sym Chal : Type} {S : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    {decSym : List Bool → Sym} {defaultSym : Sym}
    {tr_MT : List (List Bool × List Bool)} {tr_FS : List (BCSFSQuery Stmt Chal × Chal)}
    (hdoomed : BCSChainDoomed r d S doomed decSym defaultSym tr_MT tr_FS)
    {x₀ : Stmt} {rts₀ : List (List Bool)} {prev₀ : List Chal} {c : Chal}
    (hbad : ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT
      (((x₀, rts₀, prev₀), c) :: tr_FS)) :
    x₀ ∈ S ∧
      ((let pref₀ := bcsExtractTranscript decSym defaultSym d tr_MT
          (rts₀.take (rts₀.length - 1)) prev₀
        let π₀ := bcsExtractTable decSym defaultSym tr_MT d ((rts₀[rts₀.length - 1]?).getD [])
        doomed x₀ pref₀ ∧ ¬ goodStep x₀ pref₀ π₀ c) ∨
        c ∈ fsOutOfOrderTargets (rts₀.length - 1) tr_FS) := by
  unfold BCSChainDoomed at hbad
  push Not at hbad
  obtain ⟨x, hx, rts, chals, hr, ⟨hlen, hsteps⟩, hnot_doomed⟩ := hbad
  have hex_new : ∃ (i₀ : ℕ) (hi₀ : i₀ < rts.length),
      ((x, rts.take (i₀ + 1), chals.take i₀), chals[i₀]'(hlen ▸ hi₀)) =
        ((x₀, rts₀, prev₀), c) := by
    by_contra! hall_old
    exact hnot_doomed <| hdoomed x hx rts chals hr ⟨hlen, fun i hi =>
      (List.mem_cons.mp (hsteps i hi)).resolve_left (hall_old i hi)⟩
  obtain ⟨i₀, hi₀, heq₀⟩ := hex_new
  simp only [Prod.mk.injEq] at heq₀
  obtain ⟨⟨rfl, hrts₀_eq, hprev₀_eq⟩, hc_eq⟩ := heq₀
  have hrts₀_len : rts₀.length = i₀ + 1 := by
    rw [← hrts₀_eq, List.length_take_of_le hi₀]
  have hi₀_eq : rts₀.length - 1 = i₀ := by omega
  have hmem_of_ne (j : ℕ) (hj : j < rts.length) (hne : j ≠ i₀) :
      ((x, rts.take (j + 1), chals.take j), chals[j]'(hlen ▸ hj)) ∈ tr_FS :=
    (List.mem_cons.mp (hsteps j hj)).resolve_left fun hsame => by
      have hlen_eq := congrArg (fun e : BCSFSQuery Stmt Chal × Chal => e.1.2.1.length) hsame
      rw [show _ = j + 1 from List.length_take_of_le (Nat.succ_le_of_lt hj), hrts₀_len] at hlen_eq
      exact hne (by omega)
  refine ⟨hx, ?_⟩
  by_cases hmore : i₀ + 1 < rts.length
  · right
    refine hi₀_eq ▸ List.mem_filterMap.mpr ⟨_, hmem_of_ne (i₀ + 1) hmore (by omega), ?_⟩
    simp [List.getElem?_eq_getElem (by rw [List.length_take_of_le (by omega)]; omega :
      i₀ < (chals.take (i₀ + 1)).length), hc_eq]
  · left
    have hlast : i₀ + 1 = rts.length := by omega
    have hrts_eq : rts = rts₀ := by rw [← hrts₀_eq, hlast, List.take_length]
    have hparent : ValidFSChain tr_FS x (rts₀.take i₀) prev₀ := by
      subst hrts_eq hprev₀_eq
      refine ⟨by simp [List.length_take_of_le hi₀.le,
        List.length_take_of_le (hlen ▸ hi₀.le)], fun j hj => ?_⟩
      rw [List.length_take_of_le hi₀.le] at hj
      simpa [List.take_take, Nat.min_eq_left (Nat.succ_le_of_lt hj),
        Nat.min_eq_left hj.le] using hmem_of_ne j (hj.trans hi₀) hj.ne
    have hparent_doomed := hi₀_eq ▸ hdoomed x hx (rts₀.take i₀) prev₀
      ((List.length_take_le i₀ rts₀).trans (by omega)) hparent
    refine ⟨hparent_doomed, fun hgood_c => hnot_doomed ?_⟩
    have hrts_split : rts =
        rts₀.take (rts₀.length - 1) ++ [(rts₀[rts₀.length - 1]?).getD []] := by
      subst hrts_eq
      have h1 := List.take_succ_eq_append_getElem hi₀
      rw [hlast, List.take_length] at h1
      simpa [hi₀_eq, List.getElem?_eq_getElem hi₀] using h1
    have hchals_split : chals = prev₀ ++ [c] := by
      have hi₀_ch : i₀ < chals.length := hlen ▸ hi₀
      have h1 := List.take_succ_eq_append_getElem hi₀_ch
      rw [show i₀ + 1 = chals.length from by omega, List.take_length] at h1
      simpa [← hprev₀_eq, ← hc_eq] using h1
    have hlen_p : (rts₀.take (rts₀.length - 1)).length = prev₀.length := by
      simp [hi₀_eq, ← hprev₀_eq, Nat.min_eq_left (by omega : i₀ ≤ rts₀.length),
        Nat.min_eq_left (by omega : i₀ ≤ chals.length)]
    rw [hrts_split, hchals_split,
      bcsExtractTranscript_append_singleton decSym defaultSym d tr_MT hlen_p]
    exact hstep x hx _ _ c hparent_doomed hgood_c

/-- **Single-step Fiat–Shamir bad-event bound**: from a state `(tr_MT, tr_FS)` satisfying
`BCSChainDoomed`, one call to `memoize (fun _ => PMF.uniformOfFintype Chal)` violates
`BCSChainDoomed` with probability at most `ε_rbr + tr_FS.length * (1 / Fintype.card Chal)`. -/
theorem toOuterMeasure_memoize_not_bcsChainDoomed_step {r d : ℕ} {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (tr_MT : List (List Bool × List Bool)) (fsq : BCSFSQuery Stmt Chal)
    {tr_FS : List (BCSFSQuery Stmt Chal × Chal)}
    (hdoomed : BCSChainDoomed r d S doomed decSym defaultSym tr_MT tr_FS) :
    (memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal) fsq tr_FS).toOuterMeasure
      {out | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT out.2} ≤
      ε_rbr + (tr_FS.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal) := by
  rcases fsq with ⟨x₀, rts₀, prev₀⟩
  cases hlookup : tr_FS.lookup (x₀, rts₀, prev₀) with
  | some c₀ =>
    rw [memoize_of_some _ _ _ _ hlookup, PMF.monad_pure_eq_pure, PMF.toOuterMeasure_pure_apply]
    simp [hdoomed]
  | none =>
    rw [memoize_of_none _ _ _ hlookup]
    change ((PMF.uniformOfFintype Chal).map
      (fun c => (c, ((x₀, rts₀, prev₀), c) :: tr_FS))).toOuterMeasure _ ≤ _
    rw [PMF.toOuterMeasure_map_apply]
    by_cases hx₀ : x₀ ∈ S
    · set pref₀ := bcsExtractTranscript decSym defaultSym d tr_MT
        (rts₀.take (rts₀.length - 1)) prev₀
      set π₀ := bcsExtractTable decSym defaultSym tr_MT d ((rts₀[rts₀.length - 1]?).getD [])
      set E₁ : Set Chal := {c | doomed x₀ pref₀ ∧ ¬ goodStep x₀ pref₀ π₀ c}
      set E₂ : Set Chal := {c | c ∈ fsOutOfOrderTargets (rts₀.length - 1) tr_FS}
      refine ((PMF.uniformOfFintype Chal).toOuterMeasure.mono (s₂ := E₁ ∪ E₂) fun _ hc =>
          (bad_fs_step_cases hstep hdoomed hc).2).trans
        (((MeasureTheory.measure_union_le (μ := (PMF.uniformOfFintype Chal).toOuterMeasure)
          E₁ E₂)).trans (add_le_add ?_ ?_))
      · by_cases hd₀ : doomed x₀ pref₀
        · exact ((PMF.uniformOfFintype Chal).toOuterMeasure.mono (s₁ := E₁)
            fun _ hc => hc.2).trans (hescape x₀ hx₀ pref₀ π₀ hd₀)
        · simp [show E₁ = ∅ from Set.eq_empty_iff_forall_notMem.mpr fun _ h => hd₀ h.1]
      · refine (PMF.toOuterMeasure_uniformOfFintype_mem_list_le _).trans ?_
        gcongr
        exact length_fsOutOfOrderTargets_le _ tr_FS
    · have hempty : {c : Chal | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT
          (((x₀, rts₀, prev₀), c) :: tr_FS)} = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun _ hbad =>
          hx₀ (bad_fs_step_cases hstep hdoomed hbad).1
      simp [hempty]


/-! The sticky-bad wrapper `bcsStickyMemoize` runs `bcsMemoize` and records in a flag whether
any step was bad. Forgetting the flag recovers `bcsMemoize`
(`run_interpret_bcsStickyMemoize_map`), so the bad-state bounds of `bcsMemoize` below follow from
those of the wrapper. -/

section StickyBad

variable {r d : ℕ} {Stmt Sym Chal : Type}

/-- Single-step bad transition predicate for the sticky-bad wrapper used in prover-trace knowledge
extraction: either the next state violates `BCSGoodState`, or a fresh Merkle entry hit
`bcsForbiddenDigests r st` (which includes the first `r` roots of every Fiat–Shamir query in `st.2`
and all child digests of `st.1`). -/
private def BCSStepBad (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (st st' : BCSTraceState Stmt Chal) : Prop :=
  ¬ BCSGoodState r d S doomed decSym defaultSym st' ∨
    ∃ msg ans, st'.1 = (msg, ans) :: st.1 ∧ ans ∈ bcsForbiddenDigests r st

open Classical in
private noncomputable def bcsStickyMemoize (r d : ℕ) {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) :
    StateT (BCSTraceState Stmt Chal × Bool) PMF (BCSROMSpec Stmt Chal q) :=
  fun (st, badFlag) =>
    (bcsMemoize σ q st).map fun (ans, st') =>
      (ans, (st', badFlag || decide (BCSStepBad r d S doomed decSym defaultSym st st')))

open Classical in
private theorem bcsStickyMemoize_inl (r d : ℕ) {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (msg : List Bool) (tr_MT : List (List Bool × List Bool))
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) (flag : Bool) :
    bcsStickyMemoize r d S doomed decSym defaultSym σ (.inl msg) ((tr_MT, tr_FS), flag) =
      (memoize (fun _ => BitString.uniformList σ) msg tr_MT).map fun (ans, tr_MT') =>
        (ans, ((tr_MT', tr_FS),
          flag || decide (BCSStepBad r d S doomed decSym defaultSym
            (tr_MT, tr_FS) (tr_MT', tr_FS)))) := by
  simp only [bcsStickyMemoize, bcsMemoize, RandomOracle.memoizeSum_inl, PMF.map_comp,
    Function.comp_def]

open Classical in
private theorem bcsStickyMemoize_inr (r d : ℕ) {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (fsq : BCSFSQuery Stmt Chal) (tr_MT : List (List Bool × List Bool))
    (tr_FS : List (BCSFSQuery Stmt Chal × Chal)) (flag : Bool) :
    bcsStickyMemoize r d S doomed decSym defaultSym σ (.inr fsq) ((tr_MT, tr_FS), flag) =
      (memoize (fun _ => PMF.uniformOfFintype Chal) fsq tr_FS).map fun (c, tr_FS') =>
        (c, ((tr_MT, tr_FS'),
          flag || decide (BCSStepBad r d S doomed decSym defaultSym
            (tr_MT, tr_FS) (tr_MT, tr_FS')))) := by
  simp only [bcsStickyMemoize, bcsMemoize, RandomOracle.memoizeSum_inr, PMF.map_comp,
    Function.comp_def]

private def BCSStickyBad (r d : ℕ) {Stmt Sym Chal : Type} (S : Set Stmt)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym)
    (p : BCSTraceState Stmt Chal × Bool) : Prop :=
  p.2 = true ∨ ¬ BCSGoodState r d S doomed decSym defaultSym p.1

private theorem run_interpret_bcsStickyMemoize_map {Stmt Sym Chal γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (prog : OracleComp (BCSROMSpec Stmt Chal) γ)
    (st : BCSTraceState Stmt Chal) (badFlag : Bool) :
    ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ) prog).run
        (st, badFlag)).map (fun (res, p') => (res, p'.1)) =
      (OracleComp.interpret (bcsMemoize σ) prog).run st := by
  refine OracleComp.run_interpret_map_state
    (bcsStickyMemoize r d S doomed decSym defaultSym σ) (bcsMemoize σ) Prod.fst ?_ prog
    (st, badFlag)
  rintro q ⟨st₀, flag₀⟩
  dsimp only [bcsStickyMemoize]
  simp [Function.comp_def, PMF.map, PMF.bind_pure]

private theorem toOuterMeasure_bcsStickyMemoize_step [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) {p : BCSTraceState Stmt Chal × Bool}
    (hp : ¬ BCSStickyBad r d S doomed decSym defaultSym p) :
    (bcsStickyMemoize r d S doomed decSym defaultSym σ q p).toOuterMeasure
        {out | BCSStickyBad r d S doomed decSym defaultSym out.2} ≤
      (bcsMTCost q : ℝ≥0∞) *
        (((3 * p.1.1.length + r * p.1.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) +
      (bcsFSCost q : ℝ≥0∞) *
        (ε_rbr + (p.1.2.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) := by
  classical
  rcases p with ⟨⟨tr_MT, tr_FS⟩, badFlag⟩
  have ⟨hflag, hst⟩ : badFlag ≠ true ∧ BCSGoodState r d S doomed decSym defaultSym (tr_MT, tr_FS) :=
    by simpa [BCSStickyBad] using hp
  obtain rfl : badFlag = false := Bool.eq_false_iff.mpr hflag
  cases q with
  | inl msg =>
    simp only [bcsMTCost, bcsFSCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero,
      bcsStickyMemoize_inl, PMF.toOuterMeasure_map_apply]
    cases hlookup : tr_MT.lookup msg with
    | some ans =>
      simp [memoize_of_some _ _ _ _ hlookup, BCSStickyBad, BCSStepBad, hst]
    | none =>
      rw [memoize_of_none _ _ _ hlookup]
      change ((BitString.uniformList σ).map (fun ans => (ans, (msg, ans) :: tr_MT))).toOuterMeasure
        _ ≤ _
      rw [PMF.toOuterMeasure_map_apply]
      refine ((BitString.uniformList σ).toOuterMeasure.mono
          (s₂ := {ans | ans ∈ bcsForbiddenDigests r (tr_MT, tr_FS)}) fun ans hbad => by
        rcases hbad with hflag | hng
        · dsimp only at hflag; rw [Bool.false_or] at hflag
          rcases of_decide_eq_true hflag with hng | ⟨_, _, hcons, hmem⟩
          · exact mem_bcsForbiddenDigests_of_not_bcsGoodState_cons hst hng
          · exact (Prod.mk.inj (List.cons.inj hcons).1).2 ▸ hmem
        · exact mem_bcsForbiddenDigests_of_not_bcsGoodState_cons hst hng).trans
        ((toOuterMeasure_uniformList_mem_list_le σ (bcsForbiddenDigests r (tr_MT, tr_FS))).trans
          (by gcongr; exact length_bcsForbiddenDigests_le r (tr_MT, tr_FS)))
  | inr fsq =>
    simp only [bcsMTCost, bcsFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, zero_add,
      bcsStickyMemoize_inr, PMF.toOuterMeasure_map_apply]
    refine ((memoize (fun _ : BCSFSQuery Stmt Chal => PMF.uniformOfFintype Chal)
        fsq tr_FS).toOuterMeasure.mono
          (s₂ := {x | ¬ BCSChainDoomed r d S doomed decSym defaultSym tr_MT x.2})
          fun x hbad hfs => by
        rcases hbad with hflag | hng
        · dsimp only at hflag; rw [Bool.false_or] at hflag
          rcases of_decide_eq_true hflag with hng | ⟨_, _, heq, -⟩
          · exact hng ⟨hst.1, hfs⟩
          · exact absurd (congrArg List.length heq) (by simp)
        · exact hng ⟨hst.1, hfs⟩).trans
      (toOuterMeasure_memoize_not_bcsChainDoomed_step hstep hescape decSym defaultSym tr_MT fsq
        hst.2)

private theorem toOuterMeasure_run_bcsStickyMemoize_bad_le {γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hinit : ∀ x ∈ S, doomed x [])
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    {prog : OracleComp (BCSROMSpec Stmt Chal) γ} {Q_MT Q_FS : ℕ}
    (hMT : IsCostBounded bcsMTCost prog Q_MT)
    (hFS : IsCostBounded bcsFSCost prog Q_FS) :
    ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ) prog).run
        (([], []), false)).toOuterMeasure
      {out | BCSStickyBad r d S doomed decSym defaultSym out.2} ≤
      (Q_FS : ℝ≥0∞) * (ε_rbr + (Q_FS : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) * (((3 * Q_MT + r * Q_FS : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  refine (OracleComp.toOuterMeasure_bad_le_two_budgets
    (handler := bcsStickyMemoize r d S doomed decSym defaultSym σ)
    (bad := BCSStickyBad r d S doomed decSym defaultSym)
    bcsMTCost bcsFSCost
    (fun p => ((3 * p.1.1.length + r * p.1.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ))
    (fun p => ε_rbr + (p.1.2.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal))
    (3 * ((1 : ℝ≥0∞) / 2 ^ σ)) ((r : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) 0
    ((1 : ℝ≥0∞) / Fintype.card Chal)
    (fun q p hp => toOuterMeasure_bcsStickyMemoize_step hstep hescape decSym defaultSym σ q hp)
    (fun q ⟨⟨tr_MT, tr_FS⟩, _⟩ _ x hx _ => by
      cases q with
      | inl msg =>
        supp_cases hx [bcsStickyMemoize_inl] with ⟨⟨_, tr_MT'⟩, hmem, rfl⟩
        have hlen := length_le_of_mem_support_memoize _ msg tr_MT hmem
        simp only [bcsMTCost, bcsFSCost, Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, add_zero]
        exact (by gcongr : ((3 * tr_MT'.length + r * tr_FS.length : ℕ) : ℝ≥0∞) * _ ≤
          ((3 * (tr_MT.length + 1) + r * tr_FS.length : ℕ) : ℝ≥0∞) * _).trans_eq
          (by push_cast; ring)
      | inr fsq =>
        supp_cases hx [bcsStickyMemoize_inr] with ⟨⟨_, tr_FS'⟩, hmem, rfl⟩
        have hlen := length_le_of_mem_support_memoize _ fsq tr_FS hmem
        simp only [bcsMTCost, bcsFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero]
        exact (by gcongr : ((3 * tr_MT.length + r * tr_FS'.length : ℕ) : ℝ≥0∞) * _ ≤
          ((3 * tr_MT.length + r * (tr_FS.length + 1) : ℕ) : ℝ≥0∞) * _).trans_eq
          (by push_cast; ring))
    (fun q ⟨⟨tr_MT, tr_FS⟩, _⟩ _ x hx _ => by
      cases q with
      | inl msg => supp_cases hx [bcsStickyMemoize_inl]; simp [bcsMTCost, bcsFSCost]
      | inr fsq =>
        supp_cases hx [bcsStickyMemoize_inr] with ⟨⟨_, tr_FS'⟩, hmem, rfl⟩
        have hlen := length_le_of_mem_support_memoize _ fsq tr_FS hmem
        simp only [bcsMTCost, bcsFSCost, Nat.cast_zero, Nat.cast_one, zero_mul, one_mul, add_zero]
        exact (by gcongr : ε_rbr + (tr_FS'.length : ℝ≥0∞) * _ ≤
          ε_rbr + ((tr_FS.length + 1 : ℕ) : ℝ≥0∞) * _).trans_eq (by push_cast; ring))
    hMT hFS (s := (([], []), false))
    (fun h => h.elim Bool.false_ne_true (· (bcsGoodState_nil r d hinit decSym defaultSym)))
    ).trans_eq (by simp only [List.length_nil, mul_zero, add_zero]; push_cast; ring)

end StickyBad

/-- **Single-step bad-state bound for `bcsMemoize`**: from a good state `st`, a call `q` violates
`BCSGoodState` with probability at most
`bcsMTCost q * ((3 * st.1.length + r * st.2.length) * (1 / 2 ^ σ)) +`
`bcsFSCost q * (ε_rbr + st.2.length * (1 / Fintype.card Chal))`. -/
theorem toOuterMeasure_bcsMemoize_not_goodState_step {r d : ℕ} {Stmt Sym Chal : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (q : List Bool ⊕ BCSFSQuery Stmt Chal) {st : BCSTraceState Stmt Chal}
    (hst : BCSGoodState r d S doomed decSym defaultSym st) :
    (bcsMemoize σ q st).toOuterMeasure
        {out | ¬ BCSGoodState r d S doomed decSym defaultSym out.2} ≤
      (bcsMTCost q : ℝ≥0∞) *
        (((3 * st.1.length + r * st.2.length : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) +
      (bcsFSCost q : ℝ≥0∞) *
        (ε_rbr + (st.2.length : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) := by
  rcases st with ⟨tr_MT, tr_FS⟩
  have h := toOuterMeasure_bcsStickyMemoize_step (r := r) hstep hescape decSym defaultSym σ q
    (p := ((tr_MT, tr_FS), false)) fun hbad => Or.elim hbad Bool.false_ne_true (· hst)
  dsimp only [bcsStickyMemoize] at h
  rw [PMF.toOuterMeasure_map_apply] at h
  exact le_trans ((bcsMemoize σ q (tr_MT, tr_FS)).toOuterMeasure.mono
    fun out hout => Or.inr hout) h

/-- **Accumulated bad-state bound for `bcsMemoize`**: any program with Merkle query budget `Q_MT`
and Fiat–Shamir query budget `Q_FS` starting from `([], [])` violates `BCSGoodState` with
probability at most
`Q_FS * (ε_rbr + Q_FS * (1 / Fintype.card Chal)) + Q_MT * ((3 * Q_MT + r * Q_FS) * (1 / 2 ^ σ))`.
-/
theorem toOuterMeasure_run_bcsMemoize_not_goodState_le {r d : ℕ} {Stmt Sym Chal β : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    {S : Set Stmt} {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {ε_rbr : ℝ≥0∞}
    (hinit : ∀ x ∈ S, doomed x [])
    (hstep : ∀ x ∈ S, ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (hescape : ∀ x ∈ S, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    {prog : OracleComp (BCSROMSpec Stmt Chal) β} {Q_MT Q_FS : ℕ}
    (hMT : IsCostBounded bcsMTCost prog Q_MT)
    (hFS : IsCostBounded bcsFSCost prog Q_FS) :
    ((OracleComp.interpret (bcsMemoize σ) prog).run ([], [])).toOuterMeasure
        {out | ¬ BCSGoodState r d S doomed decSym defaultSym out.2} ≤
      (Q_FS : ℝ≥0∞) * (ε_rbr + (Q_FS : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) * (((3 * Q_MT + r * Q_FS : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [← run_interpret_bcsStickyMemoize_map (r := r) S doomed decSym defaultSym σ prog ([], [])
    false, PMF.toOuterMeasure_map_apply]
  refine le_trans ?_
    (toOuterMeasure_run_bcsStickyMemoize_bad_le hinit hstep hescape decSym defaultSym σ hMT hFS)
  exact (PMF.toOuterMeasure _).mono fun out hout => Or.inr hout


end Cslib.Crypto.Protocols.BCS
