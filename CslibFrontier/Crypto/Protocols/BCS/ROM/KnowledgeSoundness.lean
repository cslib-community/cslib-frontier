/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM.State
-- `import all` only to read the private sticky-bad handler (`bcsStickyMemoize`) and verifier
-- support-invariance lemma in the straight-line prover-trace knowledge-soundness reduction.
import all CslibFrontier.Crypto.Protocols.BCS.ROM.StickyBad
import all CslibFrontier.Crypto.Protocols.BCS.ROM.VerifyBounds
import CslibFrontier.Languages.Probabilistic.Norm
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Probability.PMF.Bind
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.SuppCases
import Mathlib.Data.List.OfFn

/-!
# Adaptive straight-line random-oracle knowledge soundness of the BCS transform

Defines the combined BCS execution `bcsExecROM` and the zero-rewinding straight-line knowledge
soundness experiment `bcsKnowledgeSoundnessGame` (which extracts a candidate witness directly from
the prover's pre-verifier Merkle query trace `tr_P`), and proves explicit non-asymptotic bounds on
extraction failure (`bcsROMKnowledgeSoundness_trace_bound`, `bcsROMKnowledgeSoundness_bound`,
`bcsROMKnowledgeSoundness_bound_of_prover_verifier`) from `IOPRoundByRoundKnowledgeSoundness`
([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Theorem 26.1.1 and Construction 26.1.3,
printed pp. 288–291, and Chapter 31, Definition 31.1.6 and Theorem 31.3.1).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.bcsExecROM`: combined prover-and-verifier execution in the
  two-channel BCS random-oracle model.
* `Cslib.Crypto.Protocols.BCS.bcsKnowledgeSoundnessGame`: straight-line ROM knowledge-soundness
  experiment extracting `bcsExtractWitness` from the prover's Merkle trace `tr_P` before running
  `bcsVerifyROM`.
* `Cslib.Crypto.Protocols.BCS.BCSExtractionFails`: trace-level extraction-failure event on an
  output of `bcsExecROM`.

## Main results

* `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsFSCost_bcsExecROM`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsExecROM`: per-channel query-cost bounds
  for `bcsExecROM`.
* `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_trace_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMKnowledgeSoundness_bound_of_prover_verifier`: adaptive
  straight-line ROM knowledge-soundness bounds without rewinding.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 26 (Theorem 26.1.1 and Construction 26.1.3) and Chapter 31 (Definition 31.1.6 and
  Theorem 31.3.1).
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Turing.MultiTapeTM Cslib.Probability Cslib.OracleComp
open scoped ENNReal

section ROMKnowledgeSoundness

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

/-- Combined prover-and-verifier execution in the two-channel BCS random-oracle model: runs `P` to
obtain `(x, prf)` and then runs `bcsVerifyROM iop encSym x prf`, returning `((x, prf), ok)`. -/
@[expose] def bcsExecROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal) (encSym : Sym → List Bool)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) :
    OracleComp (BCSROMSpec Stmt Chal) ((Stmt × BCSProof r Sym) × Bool) := do
  let (x, prf) ← P
  let ok ← bcsVerifyROM iop encSym x prf
  return ((x, prf), ok)

theorem isCostBounded_bcsFSCost_bcsExecROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS) :
    IsCostBounded bcsFSCost (bcsExecROM iop encSym P) (t_FS + r) := by
  unfold bcsExecROM
  exact hFS.bind fun (x, prf) =>
    (isCostBounded_bcsFSCost_bcsVerifyROM iop encSym x prf).bind fun ok =>
      IsCostBounded.pure ((x, prf), ok) 0

theorem isCostBounded_bcsMTCost_bcsExecROM (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    IsCostBounded bcsMTCost (bcsExecROM iop encSym P) (t_MT + q_V) := by
  unfold bcsExecROM
  exact hMT.bind_on_support fun (x, prf) hmem =>
    (hV x prf hmem).bind fun ok =>
      IsCostBounded.pure ((x, prf), ok) 0

open Classical in
/-- **Straight-line BCS ROM knowledge soundness experiment** (`bcsKnowledgeSoundnessGame`), run
once in the memoized two-channel ROM `bcsMemoize σ` from the empty traces `([], [])`:
1. the cheating prover `P` outputs `(x, prf)`;
2. the Merkle trace `tr_P` recorded so far (the prover's own queries) gives the candidate witness
   `w := bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots`, straight-line from
   `tr_P` alone, before the verifier runs and with zero rewinding;
3. `bcsVerifyROM iop encSym x prf` continues in the same oracle to obtain `ok`;
4. the game outputs `true` iff `ok = true` and `¬ rel x w`. -/
@[expose] noncomputable def bcsKnowledgeSoundnessGame [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (rel : Stmt → Wit → Prop) (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (encSym : Sym → List Bool) (decSym : List Bool → Sym) (defaultSym : Sym)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) : PMF Bool :=
  StateT.run' (s := (([], []) : BCSTraceState Stmt Chal)) do
    let (x, prf) ← OracleComp.interpret (bcsMemoize σ) P
    let (tr_P, _) ← get
    let w := bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots
    let ok ← OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)
    return ok && decide (¬ rel x w)

open Classical in
/-- `bcsKnowledgeSoundnessGame` as a bind: run `P` from `([], [])`, then run `bcsVerifyROM` from
the prover's final traces `(tr_P, tr_FS)`. -/
private theorem bcsKnowledgeSoundnessGame_eq_bind [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (rel : Stmt → Wit → Prop) (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (encSym : Sym → List Bool) (decSym : List Bool → Sym) (defaultSym : Sym)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) :
    bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ =
      ((OracleComp.interpret (bcsMemoize σ) P).run ([], [])).bind fun ((x, prf), (tr_P, tr_FS)) =>
        let w := bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots
        ((OracleComp.interpret (bcsMemoize σ) (bcsVerifyROM iop encSym x prf)).run
          (tr_P, tr_FS)).map fun (ok, _) => ok && decide (¬ rel x w) := by
  simp only [bcsKnowledgeSoundnessGame, StateT.run'_eq, StateT.run_bind, StateT.run_get,
    StateT.run_pure, pmf_norm, PMF.monad_map_eq_map, PMF.map]

/-- **Straight-line extraction failure** on an output `(((x, prf), ok), (tr_MT, tr_FS))` of
`bcsExecROM` under `bcsMemoize σ`: the verifier accepts (`ok = true`), but the witness
`bcsExtractWitness iopExtract decSym defaultSym tr_MT x prf.roots` extracted from the Merkle trace
`tr_MT` fails `rel x`. -/
@[expose] def BCSExtractionFails (rel : Stmt → Wit → Prop)
    (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit) (decSym : List Bool → Sym)
    (defaultSym : Sym) : ((Stmt × BCSProof r Sym) × Bool) × BCSTraceState Stmt Chal → Prop
  | (((x, prf), ok), (tr_MT, _)) =>
    ok = true ∧ ¬ rel x (bcsExtractWitness iopExtract decSym defaultSym tr_MT x prf.roots)

/-- **Trace-level straight-line BCS ROM knowledge soundness bound**: on a combined execution of
`bcsExecROM iop encSym P` under `bcsMemoize σ`, the probability of `BCSExtractionFails` (the
verifier accepts `(x, prf)` while the witness extracted from the final Merkle trace `tr_MT` fails
`rel x`) is at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMKnowledgeSoundness_trace_bound [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost (bcsExecROM iop encSym P) Q_MT) :
    ((OracleComp.interpret (bcsMemoize σ) (bcsExecROM iop encSym P)).run ([], [])).toOuterMeasure
        {out | BCSExtractionFails rel iopExtract decSym defaultSym out} ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  set run := (OracleComp.interpret (bcsMemoize σ) (bcsExecROM iop encSym P)).run ([], [])
  rw [← PMF.toOuterMeasure_apply_inter_support]
  refine (run.toOuterMeasure.mono
    fun ⟨⟨⟨x, prf⟩, ok⟩, st₃⟩ ⟨⟨hok, hnot_rel⟩, hmem⟩ => ?_).trans
    (toOuterMeasure_run_bcsMemoize_not_goodState_le (S := Set.univ)
      (fun x _ => hks.init_doomed x) (fun x _ => hks.step_doomed x)
      (fun x _ => hescape x) decSym defaultSym σ hMT
      (isCostBounded_bcsFSCost_bcsExecROM iop encSym hFS))
  subst hok
  supp_cases hmem [run, bcsExecROM, run_interpret_bind, run_interpret_pure] with
    ⟨⟨⟨x, prf⟩, st₁⟩, hP, ⟨_, _⟩, hV, ⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩
  intro hgood
  obtain ⟨chals, -, hdoomed, hiop_acc⟩ :=
    exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ hP hV
      hgood (Set.mem_univ x)
  exact hnot_rel (hks.extract_of_doomed x _ chals hdoomed hiop_acc)

/-- Along a `liftRight` program run under `bcsStickyMemoize`, the Merkle trace `tr_MT` is unchanged.
-/
private theorem fst_eq_of_mem_support_bcsStickyMemoize_liftRight {γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (prog : OracleComp (BCSFSSpec Stmt Chal) γ)
    {p p' : BCSTraceState Stmt Chal × Bool} {res : γ}
    (hmem : (res, p') ∈
      ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ)
        (OracleComp.liftRight (spec₁ := MerkleHashSpec) prog)).run p).support) :
    p'.1.1 = p.1.1 := by
  induction prog using OracleComp.induction generalizing p with
  | pure a =>
    supp_cases hmem [liftRight_pure, run_interpret_pure]
    rfl
  | query_bind q cont ih =>
    rcases p with ⟨⟨tr_MT, tr_FS⟩, flag⟩
    rw [← OracleComp.runWith_eq_run_interpret] at hmem
    supp_cases hmem [liftRight_freeMBind, liftRight_query, OracleComp.runWith_freeMBind,
      OracleComp.runWith_query, bcsStickyMemoize_inr] with
      ⟨_, ⟨⟨c₂, tr_FS₁⟩, -, rfl⟩, hcont⟩
    rw [OracleComp.runWith_eq_run_interpret] at hcont
    exact (ih c₂ hcont :)

/-- Along a `liftLeft` program run under `bcsStickyMemoize`, if the final sticky flag `p'.2` is
`false`, then `p'.1.2 = p.1.2` and `bcsExtractTable` is unchanged on every root appearing in the
first `r` roots of any Fiat–Shamir entry in `p.1.2`. -/
private theorem extractTable_eq_of_mem_support_bcsStickyMemoize_liftLeft {γ : Type}
    [BEq Stmt] [BEq Chal] [Fintype Chal] [Nonempty Chal]
    (S : Set Stmt) (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (decSym : List Bool → Sym) (defaultSym : Sym) (σ : ℕ)
    (prog : OracleComp MerkleHashSpec γ)
    {p p' : BCSTraceState Stmt Chal × Bool} {res : γ}
    (hmem : (res, p') ∈
      ((OracleComp.interpret (bcsStickyMemoize r d S doomed decSym defaultSym σ)
        (OracleComp.liftLeft (spec₂ := BCSFSSpec Stmt Chal) prog)).run p).support)
    (hflag' : p'.2 = false) :
    p.2 = false ∧ p'.1.2 = p.1.2 ∧
      ∀ rt ∈ p.1.2.flatMap (fun ((_, rts, _), _) => rts.take r),
        bcsExtractTable decSym defaultSym p'.1.1 d rt =
          bcsExtractTable decSym defaultSym p.1.1 d rt := by
  induction prog using OracleComp.induction generalizing p with
  | pure a =>
    supp_cases hmem [liftLeft_pure, run_interpret_pure]
    exact ⟨hflag', rfl, fun _ _ => rfl⟩
  | query_bind msg cont ih =>
    rcases p with ⟨⟨tr_MT, tr_FS⟩, flag⟩
    rw [← OracleComp.runWith_eq_run_interpret] at hmem
    supp_cases hmem [liftLeft_freeMBind, liftLeft_query, OracleComp.runWith_freeMBind,
      OracleComp.runWith_query, bcsStickyMemoize_inl] with
      ⟨_, ⟨⟨ans₂, tr_MT₁⟩, hmt, rfl⟩, hcont⟩
    rw [OracleComp.runWith_eq_run_interpret] at hcont
    obtain ⟨hflag₁, hfs_eq, hextract_tail⟩ := ih ans₂ hcont
    dsimp only at hflag₁ hfs_eq hextract_tail
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hflag₁
    obtain ⟨rfl, hnot_step⟩ := hflag₁
    refine ⟨rfl, hfs_eq, fun rt hrt => ?_⟩
    rw [hextract_tail rt hrt]
    supp_cases hmt [RandomOracle.mem_support_memoize_iff]
    · rfl
    · obtain ⟨_, hchildren, hnot_fs⟩ := mem_bcsForbiddenDigests_not_elim
        fun hforb => hnot_step (Or.inr ⟨msg, ans₂, rfl, hforb⟩)
      exact bcsExtractTable_cons_of_ne decSym defaultSym tr_MT msg
        (fun heq => hnot_fs (heq ▸ hrt)) hchildren

/-- Rewriting `bcsKnowledgeSoundnessGame` as an event over the sticky-bad execution of
`bcsExecROM iop encSym P`: forgetting the sticky flag in both `P` and `bcsVerifyROM` reproduces
`bcsKnowledgeSoundnessGame`. -/
private theorem bcsKnowledgeSoundnessGame_eq_sticky [BEq Stmt] [BEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (rel : Stmt → Wit → Prop) (iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit)
    (doomed : Stmt → List (OracleTable d Sym × Chal) → Prop)
    (encSym : Sym → List Bool) (decSym : List Bool → Sym) (defaultSym : Sym)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) :
    open Classical in
    bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ =
      (((OracleComp.interpret (bcsStickyMemoize r d Set.univ doomed decSym defaultSym σ) P).run
          (([], []), false)).bind fun ((x, prf), p₁) =>
        let w := bcsExtractWitness iopExtract decSym defaultSym p₁.1.1 x prf.roots
        ((OracleComp.interpret (bcsStickyMemoize r d Set.univ doomed decSym defaultSym σ)
          (bcsVerifyROM iop encSym x prf)).run p₁).map
            fun (ok, _) => ok && decide (¬ rel x w)) := by
  classical
  rw [bcsKnowledgeSoundnessGame_eq_bind,
    ← run_interpret_bcsStickyMemoize_map Set.univ doomed decSym defaultSym σ P ([], []) false,
    PMF.bind_map]
  refine congrArg (PMF.bind _) (funext fun ⟨⟨x, prf⟩, ⟨⟨tr_P, tr_FS⟩, flag₁⟩⟩ => ?_)
  dsimp only [Function.comp_def]
  rw [← run_interpret_bcsStickyMemoize_map Set.univ doomed decSym defaultSym σ
    (bcsVerifyROM iop encSym x prf) (tr_P, tr_FS) flag₁, PMF.map_comp]
  rfl

/-- **Adaptive straight-line BCS ROM knowledge soundness theorem** (compare state-restoration
knowledge soundness and direct extraction in [BenSassonChiesaSpooner2016] and [ChiesaYogev2024],
Theorem 26.1.1 and Construction 26.1.3, printed pp. 288–291, and the round-by-round reduction in
[ChiesaYogev2024], Chapter 31, Definition 31.1.6 and Theorem 31.3.1): under
`IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep` with per-round challenge
escape probability `≤ ε_rbr`, for any adaptive cheating prover `P` making at most `t_FS`
Fiat–Shamir queries such that `bcsExecROM iop encSym P` makes at most `Q_MT` Merkle hash queries,
the probability that `bcsVerifyROM` accepts `(x, prf)` while the straight-line witness
`bcsExtractWitness iopExtract decSym defaultSym tr_P x prf.roots` (extracted from the prover's own
Merkle trace `tr_P` with zero rewinding, before running the verifier) fails `rel x` is at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMKnowledgeSoundness_bound [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost (bcsExecROM iop encSym P) Q_MT) :
    bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  classical
  set handler := bcsStickyMemoize r d (Set.univ : Set Stmt) doomed decSym defaultSym σ
  set combined : PMF (Bool × (BCSTraceState Stmt Chal × Bool)) :=
    ((OracleComp.interpret handler P).run (([], []), false)).bind fun ((x, prf), p₁) =>
      ((OracleComp.interpret handler (bcsVerifyROM iop encSym x prf)).run p₁).map
        fun (ok, p₃) =>
          (ok && decide (¬ rel x
            (bcsExtractWitness iopExtract decSym defaultSym p₁.1.1 x prf.roots)), p₃)
  have hgame_eq : bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ =
      combined.map Prod.fst := by
    simp only [bcsKnowledgeSoundnessGame_eq_sticky iop rel iopExtract doomed encSym decSym
      defaultSym P σ, combined, handler, pmf_norm, PMF.map]
  have hrun_snd : combined.map Prod.snd =
      ((OracleComp.interpret handler (bcsExecROM iop encSym P)).run (([], []), false)).map
        Prod.snd := by
    simp only [combined, bcsExecROM, run_interpret_bind, run_interpret_pure, pmf_norm, PMF.map]
  have hmem_proj {γ : Type} (prog : OracleComp (BCSROMSpec Stmt Chal) γ) {res : γ}
      {p p' : BCSTraceState Stmt Chal × Bool}
      (h : (res, p') ∈ ((OracleComp.interpret handler prog).run p).support) :
      (res, p'.1) ∈ ((OracleComp.interpret (bcsMemoize σ) prog).run p.1).support :=
    run_interpret_bcsStickyMemoize_map Set.univ doomed decSym defaultSym σ prog p.1 p.2 ▸
      (PMF.mem_support_map_iff _ _ _).mpr ⟨(res, p'), h, rfl⟩
  rw [hgame_eq, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply,
    ← PMF.toOuterMeasure_apply_inter_support]
  refine (combined.toOuterMeasure.mono
      (s₂ := {out | BCSStickyBad r d Set.univ doomed decSym defaultSym out.2})
      fun ⟨win, p₃⟩ ⟨hwin, hmem⟩ => ?_).trans <|
    le_trans (le_of_eq <| by
      change (combined.toOuterMeasure
        (Prod.snd ⁻¹' {p | BCSStickyBad r d Set.univ doomed decSym defaultSym p})) = _
      rw [← PMF.toOuterMeasure_map_apply Prod.snd combined, hrun_snd,
        PMF.toOuterMeasure_map_apply]
      rfl)
    (toOuterMeasure_run_bcsStickyMemoize_bad_le
      (fun x _ => hks.init_doomed x) (fun x _ => hks.step_doomed x)
      (fun x _ => hescape x) decSym defaultSym σ hMT
      (isCostBounded_bcsFSCost_bcsExecROM iop encSym hFS))
  obtain rfl : win = true := by simpa using hwin
  supp_cases hmem [combined, eq_comm (a := true), Bool.and_eq_true, decide_eq_true_eq] with
    ⟨⟨⟨x, prf⟩, p₁⟩, hP_sticky, ⟨_, p₃'⟩, hV_sticky, ⟨rfl, hnot_rel_P⟩, rfl⟩
  by_contra hnot_bad
  have ⟨hflag₃, hgood₃⟩ :
      p₃'.2 = false ∧ BCSGoodState r d Set.univ doomed decSym defaultSym p₃'.1 := by
    have h : p₃'.2 ≠ true ∧ BCSGoodState r d Set.univ doomed decSym defaultSym p₃'.1 := by
      simpa [BCSStickyBad] using hnot_bad
    exact ⟨Bool.eq_false_iff.mpr h.1, h.2⟩
  have hV_split := hV_sticky
  supp_cases hV_split [bcsVerifyROM, run_interpret_bind] with
    ⟨⟨chals_mid, p₂⟩, hchal_sticky, hopen_sticky⟩
  have htr_P_eq := fst_eq_of_mem_support_bcsStickyMemoize_liftRight Set.univ doomed decSym
    defaultSym σ (bcsChallengesProg x prf.roots) hchal_sticky
  obtain ⟨_, hfs₂_eq, hextract_eq⟩ := extractTable_eq_of_mem_support_bcsStickyMemoize_liftLeft
    Set.univ doomed decSym defaultSym σ (bcsVerifyOpeningsProg iop encSym x prf chals_mid)
    hopen_sticky hflag₃
  obtain ⟨chals, ⟨hlen_ch, hsteps_ch⟩, hdoomed, hiop_acc⟩ :=
    exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ
      (hmem_proj P hP_sticky) (hmem_proj (bcsVerifyROM iop encSym x prf) hV_sticky)
      hgood₃ (Set.mem_univ x)
  have horacles_eq :
      bcsExtractOracles decSym defaultSym p₁.1.1 d prf.roots =
        bcsExtractOracles decSym defaultSym p₃'.1.1 d prf.roots := funext fun j => by
    have hmem_forb : prf.roots j ∈ p₂.1.2.flatMap (fun ((_, rts, _), _) => rts.take r) := by
      rw [← hfs₂_eq, List.mem_flatMap]
      refine ⟨_, hsteps_ch j.val (by simp [j.isLt]), ?_⟩
      dsimp only
      rw [List.take_of_length_le (by simp [Nat.succ_le_of_lt j.isLt]), ← rootPrefix_eq_take_ofFn]
      exact List.mem_ofFn.mpr ⟨Fin.last j.val, by simp⟩
    exact (htr_P_eq ▸ hextract_eq (prf.roots j) hmem_forb).symm
  exact hnot_rel_P (by simpa only [bcsExtractWitness, horacles_eq] using
    hks.extract_of_doomed x _ chals hdoomed hiop_acc)

/-- **Adaptive straight-line BCS ROM knowledge soundness (separate prover/verifier Merkle budgets on
`P.support`)**: if `P` makes at most `t_MT` Merkle hash queries and `t_FS` Fiat–Shamir queries, and
`bcsVerifyROM iop encSym x prf` makes at most `q_V` Merkle hash queries for outputs `(x, prf) ∈
P.support`, then `bcsKnowledgeSoundnessGame` fails straight-line witness extraction on an accepted
proof with probability at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`(t_MT + q_V) * ((3 * (t_MT + q_V) + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMKnowledgeSoundness_bound_of_prover_verifier
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {rel : Stmt → Wit → Prop}
    {iopExtract : Stmt → (Fin r → OracleTable d Sym) → Wit}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hks : IOPRoundByRoundKnowledgeSoundness iop rel iopExtract doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    bcsKnowledgeSoundnessGame iop rel iopExtract encSym decSym defaultSym P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMKnowledgeSoundness_bound hks hescape hdec defaultSym σ hFS
    (isCostBounded_bcsMTCost_bcsExecROM iop encSym hMT hV)

end ROMKnowledgeSoundness

end Cslib.Crypto.Protocols.BCS
