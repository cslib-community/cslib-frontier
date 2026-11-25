/-
Copyright (c) 2026 Mayank Rathee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mayank Rathee
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.Basic
public import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Probability.PMF.BindFailure
import CslibFrontier.Probability.PMF.EventBind
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Interactive Public-Coin IOP Execution and Round-by-Round Escape Union Bounds

This module defines sequential adaptive execution for a `PublicCoinIOP`
(`CslibFrontier.Crypto.Protocols.BCS.Basic`) against an arbitrary (possibly randomized,
prefix-dependent) prover `InteractiveIOPProver`, and proves generic union-bound soundness theorems
summing per-round escape probabilities across rounds ([BenSassonChiesaSpooner2016];
[ChiesaYogev2024]; compare the commit-phase bad-event sum in the proof of Lemma 8.2 in
[BenSassonCarmonIshaiKoppartySaraf2020, Section 8.2.1, p. 42] and its combination with query rounds
in the proof of Theorem 8.3 on p. 40).

Because this module depends only on `PublicCoinIOP` and finite uniform distributions, any
public-coin IOP can import these interactive soundness combinators without pulling in
protocol-specific layers such as FRI coset folding or random-oracle Merkle extraction.

## Main definitions

* `Cslib.Crypto.Protocols.BCS.InteractiveIOPProver`: adaptive (possibly randomized) cheating IOP
  prover mapping a transcript prefix `List (OracleTable d Sym × Chal)` to a `PMF` over the next
  committed oracle table.
* `Cslib.Crypto.Protocols.BCS.InteractiveIOPProver.ofCausal`: lifts a deterministic causal prover
  `(j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym` to an `InteractiveIOPProver`.
* `Cslib.Crypto.Protocols.BCS.iopRunRounds`: runs `k` sequential public-coin IOP rounds from a
  transcript prefix against independent uniform verifier challenges.
* `Cslib.Crypto.Protocols.BCS.iopInteractiveGame`: runs all `r` rounds of a `PublicCoinIOP` and
  evaluates `iopVerify`.

## Main results

* `Cslib.Crypto.Protocols.BCS.length_of_mem_support_iopRunRounds`: every transcript in the support
  of `iopRunRounds P k pref` has length `pref.length + k`.
* `Cslib.Crypto.Protocols.BCS.iopPrefixEscape_le_sum`: prefix union bound `≤ ∑ j : Fin k, ε_round j`
  for escaping `doomed` over `k` adaptive public-coin rounds.
* `Cslib.Crypto.Protocols.BCS.iopCommitPhase_map_true_le_sum`: commit-phase-plus-final-oracle union
  bound `≤ ∑ j : Fin k, ε_round j` when every doomed length-`k` prefix forces `badFinal = false`
  (abstract template for the commit-phase bad-event sum in the proof of
  [BenSassonCarmonIshaiKoppartySaraf2020, Lemma 8.2, Section 8.2.1, p. 42]).
* `Cslib.Crypto.Protocols.BCS.iopInteractiveGame_le_sum`: full `r`-round summed interactive IOP
  soundness `≤ ∑ j : Fin r, ε_round j` from `IOPRoundByRoundSoundness`.
* `Cslib.Crypto.Protocols.BCS.iopInteractiveGame_ofCausal_eq`: for a deterministic causal prover,
  `iopInteractiveGame` coincides with evaluating `iopVerify` on a single uniform draw of
  `Fin r → Chal`.
* `Cslib.Crypto.Protocols.BCS.iopEscape_le_sup_of_perRound`: converts indexed per-round escape
  bounds `ε_round : Fin r → ℝ≥0∞` into the uniform all-prefix bound `Finset.univ.sup ε_round`
  consumed by `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [E. Ben-Sasson, D. Carmon, Y. Ishai, S. Kopparty, S. Saraf, *Proximity Gaps for Reed–Solomon
  Codes*][BenSassonCarmonIshaiKoppartySaraf2020]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024]
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open scoped BigOperators ENNReal
open Cslib.Probability

/-- Adaptive (possibly randomized) cheating IOP prover mapping a transcript prefix of committed
oracles and verifier challenges to a distribution over the next committed oracle table. -/
abbrev InteractiveIOPProver (d : ℕ) (Sym Chal : Type) : Type :=
  List (OracleTable d Sym × Chal) → PMF (OracleTable d Sym)

/-- Lift a deterministic causal IOP prover `P` (whose `j`-th oracle depends only on the preceding
`j` verifier challenges) to an `InteractiveIOPProver`. -/
@[expose] noncomputable def InteractiveIOPProver.ofCausal {r d : ℕ} {Sym Chal : Type}
    [Nonempty Sym] (P : (j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym) :
    InteractiveIOPProver d Sym Chal :=
  fun pref =>
    if h : pref.length < r then
      PMF.pure (P ⟨pref.length, h⟩ fun i => (pref[i.val]'i.isLt).2)
    else
      PMF.pure (fun _ => Classical.arbitrary Sym)

/-- Execute `k` sequential public-coin IOP rounds starting from transcript prefix `pref`: in each
round the prover samples `π ← P pref'` and the verifier draws `c` uniformly from `Chal`. -/
@[expose] noncomputable def iopRunRounds {d : ℕ} {Sym Chal : Type} [Fintype Chal] [Nonempty Chal]
    (P : InteractiveIOPProver d Sym Chal) :
    ℕ → List (OracleTable d Sym × Chal) → PMF (List (OracleTable d Sym × Chal))
  | 0, pref => PMF.pure pref
  | k + 1, pref =>
    (P pref).bind fun π =>
      (PMF.uniformOfFintype Chal).bind fun c =>
        iopRunRounds P k (pref ++ [(π, c)])

/-- Every transcript in the support of `iopRunRounds P k pref` has length `pref.length + k`. -/
theorem length_of_mem_support_iopRunRounds {d : ℕ} {Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal] (P : InteractiveIOPProver d Sym Chal) :
    ∀ (k : ℕ) (pref tr : List (OracleTable d Sym × Chal)),
      tr ∈ (iopRunRounds P k pref).support → tr.length = pref.length + k
  | 0, pref, tr, hmem => by
    rw [iopRunRounds, PMF.support_pure, Set.mem_singleton_iff] at hmem
    simp only [hmem, Nat.add_zero]
  | k + 1, pref, tr, hmem => by
    rw [iopRunRounds, PMF.mem_support_bind_iff] at hmem
    obtain ⟨π, _, hmem⟩ := hmem
    rw [PMF.mem_support_bind_iff] at hmem
    obtain ⟨c, _, hmem⟩ := hmem
    have ih := length_of_mem_support_iopRunRounds P k (pref ++ [(π, c)]) tr hmem
    simp only [List.length_append, List.length_singleton] at ih
    omega

/-- Full `r`-round interactive public-coin IOP soundness game: runs `P` against `r` independent
uniform verifier challenges and returns `iopVerify iop x chals oracles`. -/
@[expose] noncomputable def iopInteractiveGame {r d : ℕ} {Stmt Wit Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (x : Stmt) (P : InteractiveIOPProver d Sym Chal) : PMF Bool :=
  let defaultEntry : OracleTable d Sym × Chal :=
    ((P []).support_nonempty.some, Classical.arbitrary Chal)
  (iopRunRounds P r []).map fun tr =>
    let oracles : Fin r → OracleTable d Sym := fun j => (tr[j.val]?.getD defaultEntry).1
    let chals : Fin r → Chal := fun j => (tr[j.val]?.getD defaultEntry).2
    iopVerify iop x chals oracles

private theorem iopRunRounds_escape_le_sum_aux {d : ℕ} {Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal]
    (P : InteractiveIOPProver d Sym Chal)
    {doomed : List (OracleTable d Sym × Chal) → Prop}
    {goodStep : List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hstep : ∀ pref π c, doomed pref → goodStep pref π c → doomed (pref ++ [(π, c)])) :
    ∀ (m j : ℕ) (pref : List (OracleTable d Sym × Chal)) (ε : ℕ → ℝ≥0∞),
      pref.length = j →
      doomed pref →
      (∀ (t : ℕ) (pref' : List (OracleTable d Sym × Chal)) (π : OracleTable d Sym),
        t < m → pref'.length = j + t → doomed pref' →
        (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep pref' π c} ≤ ε t) →
      (iopRunRounds P m pref).toOuterMeasure {tr | ¬ doomed tr} ≤ ∑ t ∈ Finset.range m, ε t
  | 0, _, pref, _, _, hdoomed, _ => by
    have hzero : (PMF.pure pref).toOuterMeasure {tr | ¬ doomed tr} = 0 := by
      rw [PMF.toOuterMeasure_pure_apply]
      simp [hdoomed]
    simp only [iopRunRounds, hzero, Finset.range_zero, Finset.sum_empty, le_refl]
  | m + 1, j, pref, ε, hlen, hdoomed, hesc => by
    rw [iopRunRounds]
    refine (Cslib.Probability.PMF.toOuterMeasure_bind_le (P pref) _ _
      (error := ε 0 + ∑ t ∈ Finset.range m, ε (t + 1)) fun π => ?_).trans ?_
    · refine (Cslib.Probability.PMF.toOuterMeasure_bind_le_add (PMF.uniformOfFintype Chal)
        (fun c => iopRunRounds P m (pref ++ [(π, c)]))
        {c | ¬ goodStep pref π c} {tr | ¬ doomed tr}
        (∑ t ∈ Finset.range m, ε (t + 1)) ?_).trans
        (add_le_add (hesc 0 pref π (Nat.zero_lt_succ m) (by omega) hdoomed) le_rfl)
      intro c _ hc_good
      have hc' : goodStep pref π c := by
        simpa only [Set.mem_ofPred_eq, not_not] using hc_good
      have hdoomed' : doomed (pref ++ [(π, c)]) := hstep pref π c hdoomed hc'
      have hlen' : (pref ++ [(π, c)]).length = j + 1 := by
        simp only [List.length_append, List.length_singleton, hlen]
      exact iopRunRounds_escape_le_sum_aux P hstep m (j + 1) (pref ++ [(π, c)])
        (fun t => ε (t + 1)) hlen' hdoomed' (fun t pref' π' ht hlen'' hd' =>
          hesc (t + 1) pref' π' (Nat.succ_lt_succ ht) (by omega) hd')
    · rw [Finset.sum_range_succ']
      exact le_of_eq (add_comm _ _)

/-- **Prefix union bound for interactive public-coin IOPs**: if the empty transcript is doomed,
`goodStep` preserves `doomed`, and round `j < k` escapes `goodStep` with probability at most
`ε_round j` from any doomed length-`j` prefix, then after `k` adaptive interactive rounds the
probability of escaping `doomed` is at most `∑ j : Fin k, ε_round j`
(abstract first-escape sum underlying the proof of Lemma 8.2 in
[BenSassonCarmonIshaiKoppartySaraf2020, Section 8.2.1, p. 42]). -/
theorem iopPrefixEscape_le_sum {d : ℕ} {Stmt Sym Chal : Type} [Fintype Chal] [Nonempty Chal]
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {x : Stmt} (hinit : doomed x [])
    (hstep : ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (k : ℕ) (ε_round : Fin k → ℝ≥0∞)
    (hescape : ∀ (j : Fin k) pref π, pref.length = j.val → doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_round j)
    (P : InteractiveIOPProver d Sym Chal) :
    (iopRunRounds P k []).toOuterMeasure {tr | ¬ doomed x tr} ≤ ∑ j : Fin k, ε_round j := by
  let εNat : ℕ → ℝ≥0∞ := fun t => if ht : t < k then ε_round ⟨t, ht⟩ else 0
  have hbound := iopRunRounds_escape_le_sum_aux P (doomed := doomed x)
    (goodStep := goodStep x) hstep k 0 [] εNat rfl hinit
    (fun t pref' π ht hlen hd => by
      rw [Nat.zero_add] at hlen
      simpa only [εNat, ht, ↓reduceDIte] using hescape ⟨t, ht⟩ pref' π hlen hd)
  refine hbound.trans_eq ?_
  rw [← Fin.sum_univ_eq_sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [εNat, j.isLt, ↓reduceDIte, Fin.eta]

/-- **Commit-phase-plus-final-oracle union bound** (abstract template for the commit-phase bound
of [BenSassonCarmonIshaiKoppartySaraf2020, Lemma 8.2, pp. 38–39], proved via the bad-event sum in
Section 8.2.1, p. 42): if every doomed length-`k` prefix forces `badFinal pref πFinal = false` for
all final oracle tables `πFinal`, then running `k` commit rounds and sampling `πFinal ← P pref`
produces `badFinal pref πFinal = true` with probability at most `∑ j : Fin k, ε_round j`. -/
theorem iopCommitPhase_map_true_le_sum {d : ℕ} {Stmt Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal]
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    {x : Stmt} (hinit : doomed x [])
    (hstep : ∀ pref π c, doomed x pref → goodStep x pref π c → doomed x (pref ++ [(π, c)]))
    (k : ℕ) (ε_round : Fin k → ℝ≥0∞)
    (hescape : ∀ (j : Fin k) pref π, pref.length = j.val → doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_round j)
    (P : InteractiveIOPProver d Sym Chal)
    (badFinal : List (OracleTable d Sym × Chal) → OracleTable d Sym → Bool)
    (hfinal : ∀ pref πFinal, pref.length = k → doomed x pref → badFinal pref πFinal = false) :
    (((iopRunRounds P k []).bind fun pref => (P pref).map (badFinal pref)) true) ≤
      ∑ j : Fin k, ε_round j := by
  rw [← PMF.toOuterMeasure_apply_singleton]
  refine (Cslib.Probability.PMF.toOuterMeasure_bind_le_add (iopRunRounds P k [])
    (fun pref => (P pref).map (badFinal pref)) {tr | ¬ doomed x tr} {true} 0 ?_).trans ?_
  · intro pref hsupp hgood
    have hlen : pref.length = k := by
      simpa only [List.length_nil, Nat.zero_add] using
        length_of_mem_support_iopRunRounds P k [] pref hsupp
    have hd : doomed x pref := by simpa only [Set.mem_ofPred_eq, not_not] using hgood
    rw [PMF.toOuterMeasure_map_apply]
    have hempty : badFinal pref ⁻¹' {true} = ∅ := by
      ext πFinal
      simp [hfinal pref πFinal hlen hd]
    rw [hempty]
    exact (MeasureTheory.OuterMeasure.empty _).le
  · rw [add_zero]
    exact iopPrefixEscape_le_sum hinit hstep k ε_round hescape P

/-- **Summed interactive soundness for `PublicCoinIOP`** from `IOPRoundByRoundSoundness` and
per-round escape budgets `ε_round : Fin r → ℝ≥0∞`: for every `x ∉ lang` and adaptive (possibly
randomized) prover `P`, the acceptance probability `iopInteractiveGame iop x P true` is at most
`∑ j : Fin r, ε_round j`. -/
theorem iopInteractiveGame_le_sum {r d : ℕ} {Stmt Wit Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep)
    (ε_round : Fin r → ℝ≥0∞)
    (hescape : ∀ x ∉ lang, ∀ (j : Fin r) pref π, pref.length = j.val → doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_round j)
    {x : Stmt} (hx : x ∉ lang) (P : InteractiveIOPProver d Sym Chal) :
    iopInteractiveGame iop x P true ≤ ∑ j : Fin r, ε_round j := by
  let defaultEntry : OracleTable d Sym × Chal :=
    ((P []).support_nonempty.some, Classical.arbitrary Chal)
  let acceptFn : List (OracleTable d Sym × Chal) → Bool := fun tr =>
    iopVerify iop x (fun j => (tr[j.val]?.getD defaultEntry).2)
      (fun j => (tr[j.val]?.getD defaultEntry).1)
  have hgame : iopInteractiveGame iop x P true =
      (iopRunRounds P r []).toOuterMeasure (acceptFn ⁻¹' {true}) := by
    rw [← PMF.toOuterMeasure_apply_singleton, iopInteractiveGame, PMF.toOuterMeasure_map_apply]
  rw [hgame]
  refine ((iopRunRounds P r []).toOuterMeasure_mono ?_).trans
    (iopPrefixEscape_le_sum (hrbr.init_doomed x hx) (hrbr.step_doomed x)
      r ε_round (hescape x hx) P)
  rintro tr ⟨hacc, hsupp⟩
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hacc
  simp only [Set.mem_ofPred_eq]
  intro hd
  have hlen : tr.length = r := by
    simpa only [List.length_nil, Nat.zero_add] using
      length_of_mem_support_iopRunRounds P r [] tr hsupp
  let oracles : Fin r → OracleTable d Sym := fun j => (tr[j.val]?.getD defaultEntry).1
  let chals : Fin r → Chal := fun j => (tr[j.val]?.getD defaultEntry).2
  have htr_eq : (List.ofFn fun j : Fin r => (oracles j, chals j)) = tr := by
    apply List.ext_getElem (by simp only [List.length_ofFn, hlen])
    intro i hi1 hi2
    simp only [List.getElem_ofFn, oracles, chals, List.getElem?_eq_getElem hi2,
      Option.getD_some, Prod.mk.eta]
  have hrej := hrbr.reject_of_doomed x oracles chals (htr_eq.symm ▸ hd)
  exact Bool.false_ne_true (hrej.symm.trans hacc)

private noncomputable def causalPref {r d : ℕ} {Sym Chal : Type}
    (P : (j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym) :
    (j : ℕ) → (hj : j ≤ r) → (Fin j → Chal) → List (OracleTable d Sym × Chal)
  | 0, _, _ => []
  | j + 1, hj, hist =>
    causalPref P j (Nat.le_of_succ_le hj) (fun i => hist i.castSucc) ++
      [(P ⟨j, hj⟩ (fun i => hist i.castSucc), hist (Fin.last j))]

private theorem length_causalPref {r d : ℕ} {Sym Chal : Type}
    (P : (j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym) :
    ∀ (j : ℕ) (hj : j ≤ r) (hist : Fin j → Chal), (causalPref P j hj hist).length = j
  | 0, _, _ => rfl
  | j + 1, hj, hist => by
    simp only [causalPref, List.length_append, List.length_singleton,
      length_causalPref P j (Nat.le_of_succ_le hj)]

private theorem getElem_causalPref {r d : ℕ} {Sym Chal : Type}
    (P : (j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym) :
    ∀ (j : ℕ) (hj : j ≤ r) (hist : Fin j → Chal) (k : ℕ) (hk : k < j),
      (causalPref P j hj hist)[k]'(by rw [length_causalPref]; exact hk) =
        (P ⟨k, lt_of_lt_of_le hk hj⟩ (fun i => hist ⟨i.val, lt_trans i.isLt hk⟩), hist ⟨k, hk⟩)
  | 0, _, _, _, hk => absurd hk (Nat.not_lt_zero _)
  | j + 1, hj, hist, k, hk => by
    simp only [causalPref]
    have hlen : (causalPref P j (Nat.le_of_succ_le hj) (fun i => hist i.castSucc)).length = j :=
      length_causalPref P j _ _
    by_cases hlt : k < j
    · rw [List.getElem_append_left (by rw [hlen]; exact hlt)]
      exact getElem_causalPref P j (Nat.le_of_succ_le hj) (fun i => hist i.castSucc) k hlt
    · have hkeq : k = j := by omega
      subst hkeq
      rw [List.getElem_append_right (by rw [hlen])]
      simp only [hlen, Nat.sub_self, List.getElem_singleton]
      rfl

private theorem ofCausal_eq_pure {r d : ℕ} {Sym Chal : Type} [Nonempty Sym]
    (P : (j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym)
    (pref : List (OracleTable d Sym × Chal)) {j : ℕ} (hlen : pref.length = j) (hj : j < r)
    (hist : Fin j → Chal) (hget : ∀ k : Fin j, (pref[k.val]'(hlen ▸ k.isLt)).2 = hist k) :
    InteractiveIOPProver.ofCausal P pref = PMF.pure (P ⟨j, hj⟩ hist) := by
  subst hlen
  simp only [InteractiveIOPProver.ofCausal, hj, ↓reduceDIte]
  congr 2
  funext k
  exact hget k

private theorem iopRunRounds_ofCausal_aux {r d : ℕ} {Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal] [Nonempty Sym]
    (P : (j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym) :
    ∀ (m j : ℕ) (hjm : j + m = r) (hist : Fin j → Chal),
      iopRunRounds (InteractiveIOPProver.ofCausal P) m
          (causalPref P j (by omega) hist) =
        (PMF.uniformOfFintype (Fin m → Chal)).map fun rest =>
          causalPref P r le_rfl (fun k =>
            if hk : k.val < j then hist ⟨k.val, hk⟩
            else rest ⟨k.val - j, by omega⟩)
  | 0, j, hjm, hist => by
    obtain rfl : j = r := by omega
    rw [iopRunRounds, ← PMF.map_const (PMF.uniformOfFintype (Fin 0 → Chal))]
    congr 1
    funext _
    dsimp only [Function.const]
    congr 1
    funext k
    simp [k.isLt]
  | m + 1, j, hjm, hist => by
    have hj_lt : j < r := by omega
    have hstep_P :
        InteractiveIOPProver.ofCausal P (causalPref P j (by omega) hist) =
          PMF.pure (P ⟨j, hj_lt⟩ hist) :=
      ofCausal_eq_pure P _ (length_causalPref P j _ hist) hj_lt hist fun k =>
        congrArg Prod.snd (getElem_causalPref P j (by omega) hist k.val k.isLt)
    have hcausal_succ (c : Chal) :
        causalPref P j (by omega) hist ++ [(P ⟨j, hj_lt⟩ hist, c)] =
          causalPref P (j + 1) (by omega) (@Fin.snoc j (fun _ => Chal) hist c) := by
      simp only [causalPref, Fin.snoc_castSucc, Fin.snoc_last]
    rw [iopRunRounds, hstep_P, PMF.pure_bind]
    simp_rw [hcausal_succ, iopRunRounds_ofCausal_aux P m (j + 1) (by omega)]
    rw [Cslib.Probability.PMF.uniformOfFintype_bind_map,
      ← Cslib.Probability.PMF.uniformOfFintype_map_equiv
        (Fin.consEquiv (fun _ : Fin (m + 1) => Chal)).symm,
      PMF.map_comp]
    congr 1
    funext rest
    simp only [Function.comp_apply, Fin.consEquiv_symm_apply]
    congr 1
    funext k
    rcases lt_trichotomy k.val j with hk | hkeq | hk
    · have hk1 : k.val < j + 1 := by omega
      simp only [hk, hk1, ↓reduceDIte]
      exact Fin.snoc_castSucc (α := fun _ => Chal) (rest 0) hist ⟨k.val, hk⟩
    · have hk1 : k.val < j + 1 := by omega
      have hnot : ¬ k.val < j := by omega
      simp only [hnot, hk1, ↓reduceDIte]
      have hlast : (⟨k.val, hk1⟩ : Fin (j + 1)) = Fin.last j := Fin.ext hkeq
      have hzero : (⟨k.val - j, by omega⟩ : Fin (m + 1)) = 0 := Fin.ext (by simp [hkeq])
      rw [hlast, Fin.snoc_last, hzero]
    · have hnot1 : ¬ k.val < j := by omega
      have hnot2 : ¬ k.val < j + 1 := by omega
      simp only [hnot1, hnot2, ↓reduceDIte, Fin.tail]
      congr 1
      ext
      simp only [Fin.val_succ]
      omega

/-- For a deterministic causal prover `P`, the sequential `iopInteractiveGame` coincides with
evaluating `iopVerify` under a single uniform draw of `chals : Fin r → Chal`. -/
theorem iopInteractiveGame_ofCausal_eq {r d : ℕ} {Stmt Wit Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal] [Nonempty Sym]
    (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (x : Stmt)
    (P : (j : Fin r) → (Fin j.val → Chal) → OracleTable d Sym) :
    iopInteractiveGame iop x (InteractiveIOPProver.ofCausal P) =
      (PMF.uniformOfFintype (Fin r → Chal)).map fun chals =>
        iopVerify iop x chals (fun j => P j fun i => chals ⟨i.val, lt_trans i.isLt j.isLt⟩) := by
  have hrun := iopRunRounds_ofCausal_aux P r 0 (Nat.zero_add r) Fin.elim0
  have hnil : causalPref P 0 (Nat.zero_le r) Fin.elim0 = [] := rfl
  rw [hnil] at hrun
  simp only [iopInteractiveGame]
  change (iopRunRounds (InteractiveIOPProver.ofCausal P) r []).map _ = _
  rw [hrun, PMF.map_comp]
  congr 1
  funext chals
  simp only [Function.comp_apply, Nat.not_lt_zero, ↓reduceDIte, Nat.sub_zero, Fin.eta]
  have hget (j : Fin r) (d0 : OracleTable d Sym × Chal) :
      (causalPref P r le_rfl chals)[j.val]?.getD d0 =
        (P j (fun i => chals ⟨i.val, lt_trans i.isLt j.isLt⟩), chals j) := by
    have hj : j.val < (causalPref P r le_rfl chals).length := by
      rw [length_causalPref]
      exact j.isLt
    rw [List.getElem?_eq_getElem hj, Option.getD_some,
      getElem_causalPref P r le_rfl chals j.val j.isLt]
  simp only [hget]

/-- Bridge from per-round escape budgets `ε_round : Fin r → ℝ≥0∞` to the uniform all-prefix escape
bound `≤ Finset.univ.sup ε_round` consumed by `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`
when prefixes of length `≥ r` trivially satisfy `goodStep`. -/
theorem iopEscape_le_sup_of_perRound {r d : ℕ} {Stmt Sym Chal : Type}
    [Fintype Chal] [Nonempty Chal]
    {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (ε_round : Fin r → ℝ≥0∞)
    (hescape : ∀ x ∉ lang, ∀ (j : Fin r) pref π, pref.length = j.val → doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_round j)
    (hlong : ∀ x ∉ lang, ∀ pref π c, r ≤ pref.length → goodStep x pref π c) :
    ∀ x ∉ lang, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤
        Finset.univ.sup ε_round := by
  intro x hx pref π hdoomed
  by_cases hlt : pref.length < r
  · exact (hescape x hx ⟨pref.length, hlt⟩ pref π rfl hdoomed).trans
      (Finset.le_sup (Finset.mem_univ (⟨pref.length, hlt⟩ : Fin r)))
  · have hge : r ≤ pref.length := Nat.le_of_not_lt hlt
    have hempty : {c : Chal | ¬ goodStep x pref π c} = ∅ := by
      ext c
      simp [hlong x hx pref π c hge]
    rw [hempty]
    exact (MeasureTheory.OuterMeasure.empty _).trans_le zero_le

end Cslib.Crypto.Protocols.BCS
