/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Crypto.Protocols.BCS.ROM.State
import CslibFrontier.Crypto.Protocols.BCS.ROM.StickyBad
-- `import all` only to apply private `exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM`
-- when connecting an accepting `bcsSoundnessProg` run to `BCSGoodState` failure.
import all CslibFrontier.Crypto.Protocols.BCS.ROM.VerifyBounds
import CslibFrontier.Languages.Probabilistic.QueryCount.Support
import CslibFrontier.Probability.PMF.Event
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.Uniform
import CslibFrontier.Tactic.SuppCases

/-!
# Adaptive two-channel random-oracle soundness of the BCS transform

Defines the adaptive two-channel BCS random-oracle soundness game (`bcsSoundnessProg`,
`bcsSoundnessGame`) and proves explicit non-asymptotic soundness bounds (`bcsROMSoundness_bound`,
`bcsROMSoundness_bound_of_prover_verifier`) from `IOPRoundByRoundSoundness`
([BenSassonChiesaSpooner2016]; compare [ChiesaYogev2024], Theorem 25.2.1, printed pp. 276–278, and
Chapter 31, Definitions 31.1.1–31.1.2 and Theorem 31.2.1).

## Main definitions

* `Cslib.Crypto.Protocols.BCS.bcsSoundnessProg`, `Cslib.Crypto.Protocols.BCS.bcsSoundnessGame`:
  two-channel `OracleComp` soundness program and lazy random-oracle soundness experiment.

## Main results

* `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsFSCost_bcsSoundnessProg`,
  `Cslib.Crypto.Protocols.BCS.isCostBounded_bcsMTCost_bcsSoundnessProg`,
  `Cslib.Crypto.Protocols.BCS.bcsSoundnessGame_eq_run_bcsMemoize`: per-channel query-cost bounds
  for `bcsSoundnessProg` and equivalence between `bcsSoundnessGame` and `bcsMemoize`.
* `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound`,
  `Cslib.Crypto.Protocols.BCS.bcsROMSoundness_bound_of_prover_verifier`: adaptive two-channel ROM
  soundness bounds under combined or separate prover/verifier Merkle query budgets.

## References

* [E. Ben-Sasson, A. Chiesa, N. Spooner, *Interactive Oracle Proofs*][BenSassonChiesaSpooner2016]
* [A. Chiesa, E. Yogev, *Building Cryptographic Proofs from Hash Functions*][ChiesaYogev2024],
  Chapter 25 (Theorem 25.2.1) and Chapter 31 (Definitions 31.1.1–31.1.2 and Theorem 31.2.1).
-/

public section

namespace Cslib.Crypto.Protocols.BCS

open Cslib.Crypto Turing.MultiTapeTM Cslib.Probability Cslib.OracleComp
open scoped ENNReal

section ROMSoundness

variable {r d : ℕ} {Stmt Wit Sym Chal : Type}

open Classical in
/-- The BCS ROM soundness execution as an `OracleComp (BCSROMSpec Stmt Chal)` program: run the
cheating prover `P` to obtain `(x, prf)`, run `bcsVerifyROM iop encSym x prf`, and return `true`
when `x ∉ lang` and the verifier accepts. -/
@[expose] noncomputable def bcsSoundnessProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) :
    OracleComp (BCSROMSpec Stmt Chal) Bool := do
  let (x, prf) ← P
  let ok ← bcsVerifyROM iop encSym x prf
  return decide (x ∉ lang) && ok

/-- If the cheating prover `P` makes at most `t_FS` Fiat–Shamir queries, then
`bcsSoundnessProg iop encSym lang P` makes at most `t_FS + r` Fiat–Shamir queries. -/
theorem isCostBounded_bcsFSCost_bcsSoundnessProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS) :
    IsCostBounded bcsFSCost (bcsSoundnessProg iop encSym lang P) (t_FS + r) := by
  unfold bcsSoundnessProg
  open Classical in
  exact hFS.bind fun (x, prf) =>
    (isCostBounded_bcsFSCost_bcsVerifyROM iop encSym x prf).bind fun ok =>
      IsCostBounded.pure (decide (x ∉ lang) && ok) 0

/-- If `P` makes at most `t_MT` Merkle hash queries and `bcsVerifyROM iop encSym x prf` makes at
most `q_V` Merkle hash queries for every `(x, prf) ∈ P.support`, then `bcsSoundnessProg` makes at
most `t_MT + q_V` Merkle hash queries. -/
theorem isCostBounded_bcsMTCost_bcsSoundnessProg (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    IsCostBounded bcsMTCost (bcsSoundnessProg iop encSym lang P) (t_MT + q_V) := by
  unfold bcsSoundnessProg
  open Classical in
  exact hMT.bind_on_support fun (x, prf) hmem =>
    (hV x prf hmem).bind fun ok =>
      IsCostBounded.pure (decide (x ∉ lang) && ok) 0

/-- The BCS ROM soundness experiment with `σ`-bit Merkle digests: runs `bcsSoundnessProg` against
the shared lazy random oracle `RandomOracle.answer (bcsOracleDist Stmt Chal σ)` from an empty cache.
-/
@[expose] noncomputable def bcsSoundnessGame [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) : PMF Bool :=
  (OracleComp.runWith (RandomOracle.answer (bcsOracleDist Stmt Chal σ))
    (bcsSoundnessProg iop encSym lang P) (fun _ => none)).map Prod.fst

theorem bcsSoundnessGame_eq_run_bcsMemoize [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal] (iop : PublicCoinIOP r d Stmt Wit Sym Chal)
    (encSym : Sym → List Bool) (lang : Set Stmt)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)) (σ : ℕ) :
    bcsSoundnessGame iop encSym lang P σ =
      ((OracleComp.interpret (bcsMemoize σ) (bcsSoundnessProg iop encSym lang P)).run ([], [])).map
        Prod.fst := by
  rw [bcsSoundnessGame, show bcsOracleDist Stmt Chal σ =
      sumHandler (spec₁ := MerkleHashSpec) (spec₂ := BCSFSSpec Stmt Chal)
        (fun _ => BitString.uniformList σ) (fun _ => PMF.uniformOfFintype Chal) from
    funext fun | .inl _ => rfl | .inr _ => rfl]
  exact (RandomOracle.map_fst_run_interpret_memoizeSum_nil _ _ _).symm

/-- Any outcome `(true, st')` in the support of `bcsSoundnessProg` under `bcsMemoize` violates
`BCSGoodState` on `langᶜ`. -/
private theorem not_bcsGoodState_of_mem_support_bcsSoundnessProg
    [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    (P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym))
    {st' : BCSTraceState Stmt Chal}
    (hmem : (true, st') ∈
      ((OracleComp.interpret (bcsMemoize σ) (bcsSoundnessProg iop encSym lang P)).run
        ([], [])).support) :
    ¬ BCSGoodState r d langᶜ doomed decSym defaultSym st' := by
  supp_cases hmem [bcsSoundnessProg, run_interpret_bind, run_interpret_pure,
    eq_comm (a := true), Bool.and_eq_true, decide_eq_true_eq] with
    ⟨⟨⟨x, prf⟩, st₁⟩, hP, ⟨_, st₃⟩, hV, ⟨hx_not_lang, rfl⟩, rfl⟩
  intro hgood
  obtain ⟨chals, -, hdoomed, hiop_acc⟩ :=
    exists_doomed_and_iopVerify_of_mem_support_bcsVerifyROM iop hdec defaultSym σ hP hV hgood
      hx_not_lang
  exact Bool.false_ne_true ((hrbr.reject_of_doomed x _ chals hdoomed).symm.trans hiop_acc)

/-- **Adaptive two-channel BCS ROM soundness theorem** (compare state-restoration soundness in
[BenSassonChiesaSpooner2016] and [ChiesaYogev2024], Theorem 25.2.1, printed pp. 276–278, and the
round-by-round reduction in [ChiesaYogev2024], Chapter 31, Definitions 31.1.1–31.1.2 and Theorem
31.2.1): under `IOPRoundByRoundSoundness iop lang doomed goodStep` with per-round challenge escape
probability `≤ ε_rbr`, any adaptive cheating prover `P` making at most `t_FS` Fiat–Shamir queries
such that `bcsSoundnessProg iop encSym lang P` makes at most `Q_MT` Merkle hash queries convinces
`bcsVerifyROM` on a false statement `x ∉ lang` with probability at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`Q_MT * ((3 * Q_MT + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMSoundness_bound [DecidableEq Stmt] [DecidableEq Chal] [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x ∉ lang, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_FS Q_MT : ℕ}
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hMT : IsCostBounded bcsMTCost (bcsSoundnessProg iop encSym lang P) Q_MT) :
    bcsSoundnessGame iop encSym lang P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        (Q_MT : ℝ≥0∞) *
          (((3 * Q_MT + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) := by
  rw [bcsSoundnessGame_eq_run_bcsMemoize, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  set run := (OracleComp.interpret (bcsMemoize σ) (bcsSoundnessProg iop encSym lang P)).run ([], [])
  rw [← PMF.toOuterMeasure_apply_inter_support]
  refine (run.toOuterMeasure.mono fun ⟨res, st'⟩ ⟨hres, hmem⟩ => ?_).trans
    (toOuterMeasure_run_bcsMemoize_not_goodState_le (S := langᶜ)
      hrbr.init_doomed (fun x _ => hrbr.step_doomed x) hescape decSym defaultSym σ hMT
      (isCostBounded_bcsFSCost_bcsSoundnessProg iop encSym lang hFS))
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hres
  subst hres
  exact not_bcsGoodState_of_mem_support_bcsSoundnessProg hrbr hdec defaultSym σ P hmem

/-- **Adaptive two-channel BCS ROM soundness (separate prover/verifier Merkle budgets on
`P.support`)**: if `P` makes at most `t_MT` Merkle hash queries and `t_FS` Fiat–Shamir queries, and
`bcsVerifyROM iop encSym x prf` makes at most `q_V` Merkle hash queries for outputs `(x, prf) ∈
P.support`, then `bcsSoundnessGame` accepts a false statement with probability at most
`(t_FS + r) * (ε_rbr + (t_FS + r) * (1 / Fintype.card Chal)) +`
`(t_MT + q_V) * ((3 * (t_MT + q_V) + r * (t_FS + r)) * (1 / 2 ^ σ))`. -/
theorem bcsROMSoundness_bound_of_prover_verifier [DecidableEq Stmt] [DecidableEq Chal]
    [Fintype Chal] [Nonempty Chal]
    {iop : PublicCoinIOP r d Stmt Wit Sym Chal} {lang : Set Stmt}
    {doomed : Stmt → List (OracleTable d Sym × Chal) → Prop}
    {goodStep : Stmt → List (OracleTable d Sym × Chal) → OracleTable d Sym → Chal → Prop}
    (hrbr : IOPRoundByRoundSoundness iop lang doomed goodStep)
    {ε_rbr : ℝ≥0∞}
    (hescape : ∀ x ∉ lang, ∀ pref π, doomed x pref →
      (PMF.uniformOfFintype Chal).toOuterMeasure {c | ¬ goodStep x pref π c} ≤ ε_rbr)
    {encSym : Sym → List Bool} {decSym : List Bool → Sym}
    (hdec : Function.LeftInverse decSym encSym) (defaultSym : Sym) (σ : ℕ)
    {P : OracleComp (BCSROMSpec Stmt Chal) (Stmt × BCSProof r Sym)} {t_MT t_FS q_V : ℕ}
    (hMT : IsCostBounded bcsMTCost P t_MT)
    (hFS : IsCostBounded bcsFSCost P t_FS)
    (hV : ∀ x prf, (x, prf) ∈ P.support →
      IsCostBounded bcsMTCost (bcsVerifyROM iop encSym x prf) q_V) :
    bcsSoundnessGame iop encSym lang P σ true ≤
      ((t_FS + r : ℕ) : ℝ≥0∞) *
          (ε_rbr + ((t_FS + r : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / Fintype.card Chal)) +
        ((t_MT + q_V : ℕ) : ℝ≥0∞) *
          (((3 * (t_MT + q_V) + r * (t_FS + r) : ℕ) : ℝ≥0∞) * ((1 : ℝ≥0∞) / 2 ^ σ)) :=
  bcsROMSoundness_bound hrbr hescape hdec defaultSym σ hFS
    (isCostBounded_bcsMTCost_bcsSoundnessProg iop encSym lang hMT hV)

end ROMSoundness

end Cslib.Crypto.Protocols.BCS
